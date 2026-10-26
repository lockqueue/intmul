/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.SafePark
import SubNLogN.Machine.Calculus.FramePassSafe
import SubNLogN.Machine.Calculus.ParkAll
import SubNLogN.Machine.Calculus.HdrFacts

/-!
# Framed procedure calculus: regression examples (`Calculus/Regression.lean`)

Small unit-test proof examples that pin down what the framed procedure calculus
certifies and what it does not. All of them use one- or two-stack layouts.
* T1: an all-tail (extensional) `FramedRunsIn` fact for `spy` that is not a safe run.
* T2/T3: pop-and-restore is not safe on an empty framed stack, but is safe with an owned guard.
  Any protected suffix may then be appended.
* T4: actual running time may depend on the tail, so `FramedRunsIn` costs are upper bounds.
* T5: an empty *unframed* scratch stack is observable.
* T6/T7: sequential composition does not commute (shared registers; pushes that read the
  register).
* T8: an open program (`recur 0`) depends on its environment.
* T9: framed sets can only shrink along a call (the `hframe` direction).
* T10–T14: guarded passes: costs on empty and two-bit payloads, orientation, the missing guard
  (`notG g none = true`), and the alias exclusion.
* T15–T18: families: empty-family wrapper costs 3 and 5, a duplicated role pushes two marks, and
  the parking order.
* T19: a child may clobber the register, which is why wrapper postconditions are `True`.
* T22: there is no injection `Fin 76 → Fin 8`, so mulBig's scratch bank is not `W5_mulAt`'s.
* T23: pointwise witnesses do not give a uniform program.
* T24: `FramedRunsIn` for an empty tail class is vacuous.
* T20/T21: the header `[0, 1]` is `[mark, bit true, mark]`, and no `tag j` occurs in a header.
-/

namespace SubNLogN.Machine.Calculus.Regression

open TMFw TMFw.Contracts TMFw.Lib

/-! ### Case T1: extensional is not safe -/

/-- Read the top of the single stack into the register. -/
def spy : SProg Unit := .peek () (fun _ o => o)

/-- T1a: `spy` restores every tail, with budget 1 (all-tail judgment). -/
theorem t1_framed : FramedRunsIn (fun _ _ => True) [] spy (fun _ => []) (fun _ => [])
    (fun _ => True) 1 := by
  intro τ _ s hs
  obtain ⟨v, stk⟩ := s
  refine ⟨⟨(stk ()).head?, stk⟩, 1, ?_, ⟨hs, trivial⟩, le_rfl⟩
  have h := Eval.peek ([] : List (SProg Unit)) () (fun _ o => o) v stk
  exact h

/-- T1b: on an empty framed stack, `spy` has no safe run. -/
theorem t1_not_safe : ¬ SafeRunsIn (fun _ : Unit => True) [] spy (fun _ => []) (fun _ => [])
    (fun _ => True) 1 := by
  intro h
  obtain ⟨v', t, e, -, -⟩ := h none
  unfold spy at e
  cases e with
  | peek _ _ _ _ _ hS => exact hS trivial rfl

/-! ### Cases T2/T3: pop-and-restore -/

/-- Pop the top symbol into the register and push it back. -/
def popRestore : SProg Unit := .seq (popR ()) (restoreR ())

/-- T2a: `popRestore` restores every content exactly, in 3 steps. -/
theorem t2_eval (tl : List Sym) (v : Option Sym) :
    Eval [] popRestore ⟨v, fun _ => tl⟩ ⟨tl.head?, fun _ => tl⟩ 3 := by
  have h1 := Eval.pop ([] : List (SProg Unit)) () (fun _ o => o) v (fun _ => tl)
  have h2 := restoreR_eval [] () tl (Function.update (fun _ : Unit => tl) () tl.tail) (by simp)
  have hS : Function.update (Function.update (fun _ : Unit => tl) () tl.tail) () tl =
      fun _ => tl := by
    funext k
    cases k
    simp
  rw [hS] at h2
  exact Eval.seq h1 h2

/-- T2b: on an empty framed stack, `popRestore` has no safe run (it pops the empty visible
content). -/
theorem t2_not_safe : ¬ SafeRunsIn (fun _ : Unit => True) [] popRestore (fun _ => [])
    (fun _ => []) (fun _ => True) 3 := by
  intro h
  obtain ⟨v', t, e, -, -⟩ := h none
  unfold popRestore at e
  cases e with
  | seq e1 _ =>
    unfold popR at e1
    cases e1 with
    | pop _ _ _ _ _ hS => exact hS trivial rfl

/-- T3: with an owned guard (visible content `[mark]`), `popRestore` is safe for the framed
stack and restores it in 3 steps. -/
theorem t3_safe : SafeRunsIn (fun _ : Unit => True) [] popRestore (fun _ => [Sym.mark])
    (fun _ => [Sym.mark]) (fun _ => True) 3 := by
  intro v
  have hnn : (fun _ : Unit => True) () → (fun _ : Unit => [Sym.mark]) () ≠ [] := fun _ => by simp
  have h1 := SafeEval.pop (framed := fun _ : Unit => True) [] () (fun _ o => o) v
    (fun _ : Unit => [Sym.mark]) hnn
  have h2 := safeEval_restoreR_mark (fun _ : Unit => True) [] ()
    (Function.update (fun _ : Unit => [Sym.mark]) () [])
  have hS : Function.update (Function.update (fun _ : Unit => [Sym.mark]) () []) ()
      (Sym.mark :: Function.update (fun _ : Unit => [Sym.mark]) () [] ()) =
      fun _ => [Sym.mark] := by
    funext k
    cases k
    simp
  rw [hS] at h2
  exact ⟨some Sym.mark, 3, SafeEval.seq h1 h2, trivial, le_rfl⟩

/-- T3, continued: any suffix may be appended below the owned guard. -/
theorem t3_tail (τ : Unit → List Sym) : SafeRunsIn (fun _ : Unit => True) [] popRestore
    (appendTail (fun _ => [Sym.mark]) τ) (appendTail (fun _ => [Sym.mark]) τ) (fun _ => True) 3 :=
  t3_safe.frame_tail τ (fun _ h => absurd trivial h)

/-! ### Case T4: actual time depends on the tail -/

/-- Peek; on `none`, spend one extra step. -/
def timedPeek : SProg Unit := .seq (peekR ()) (.ite (fun r => r.isSome) skip (.seq skip skip))

/-- T4a: on the empty stack the run takes exactly 4 steps. -/
theorem t4_empty (v : Option Sym) :
    Eval [] timedPeek ⟨v, fun _ => []⟩ ⟨none, fun _ => []⟩ 4 := by
  have h1 := Eval.peek ([] : List (SProg Unit)) () (fun _ o => o) v (fun _ => [])
  have h2 : Eval ([] : List (SProg Unit)) (.seq skip skip) ⟨none, fun _ => []⟩
      ⟨none, fun _ => []⟩ 2 := Eval.seq (skip_eval _ _) (skip_eval _ _)
  exact Eval.seq h1 (Eval.ite_false (c := fun r : Option Sym => r.isSome) (p := skip) rfl h2)

/-- T4b: on the stack `[mark]` the run takes exactly 3 steps. -/
theorem t4_mark (v : Option Sym) :
    Eval [] timedPeek ⟨v, fun _ => [Sym.mark]⟩ ⟨some Sym.mark, fun _ => [Sym.mark]⟩ 3 := by
  have h1 := Eval.peek ([] : List (SProg Unit)) () (fun _ o => o) v (fun _ => [Sym.mark])
  exact Eval.seq h1 (Eval.ite_true (c := fun r : Option Sym => r.isSome) (q := .seq skip skip)
    rfl (skip_eval _ _))

/-- T4c: the common extensional budget over all tails is 4 (an upper bound, not the time). -/
theorem t4_framed : FramedRunsIn (fun _ _ => True) [] timedPeek (fun _ => []) (fun _ => [])
    (fun _ => True) 4 := by
  intro τ _ s hs
  obtain ⟨v, stk⟩ := s
  have h1 := Eval.peek ([] : List (SProg Unit)) () (fun _ o => o) v stk
  cases hh : (stk ()).head? with
  | none =>
    have h2 : Eval ([] : List (SProg Unit)) (.seq skip skip) ⟨(stk ()).head?, stk⟩
        ⟨(stk ()).head?, stk⟩ 2 := Eval.seq (skip_eval _ _) (skip_eval _ _)
    refine ⟨⟨(stk ()).head?, stk⟩, 4, Eval.seq h1 (Eval.ite_false
      (c := fun r : Option Sym => r.isSome) (p := skip) (by simp [hh]) h2), ⟨hs, trivial⟩, le_rfl⟩
  | some a =>
    refine ⟨⟨(stk ()).head?, stk⟩, 3, Eval.seq h1 (Eval.ite_true
      (c := fun r : Option Sym => r.isSome) (q := .seq skip skip) (by simp [hh])
      (skip_eval _ _)), ⟨hs, trivial⟩, by omega⟩

/-! ### Case T5: an empty unframed scratch stack is observable -/

/-- Record on stack `true` whether the scratch stack `false` is empty. -/
def observe : SProg Bool := .seq (.peek false (fun _ o => o)) (.push true (fun r => Sym.bit r.isNone))

/-- T5a: empty scratch: pushes `bit true`, in 2 steps. -/
theorem t5_empty (v : Option Sym) :
    Eval [] observe ⟨v, fun _ => []⟩
      ⟨none, Function.update (fun _ => []) true [Sym.bit true]⟩ 2 := by
  have h1 := Eval.peek ([] : List (SProg Bool)) false (fun _ o => o) v (fun _ => [])
  have h2 := Eval.push ([] : List (SProg Bool)) true (fun r => Sym.bit r.isNone) none
    (fun _ => [])
  exact Eval.seq h1 h2

/-- T5b: guarded scratch (`[mark]`): pushes `bit false`, in 2 steps. -/
theorem t5_guarded (v : Option Sym) :
    Eval [] observe ⟨v, Function.update (fun _ => []) false [Sym.mark]⟩
      ⟨some Sym.mark, Function.update (Function.update (fun _ => []) false [Sym.mark]) true
        (Sym.bit false :: Function.update (fun _ => []) false [Sym.mark] true)⟩ 2 := by
  have h1 := Eval.peek ([] : List (SProg Bool)) false (fun _ o => o) v
    (Function.update (fun _ => []) false [Sym.mark])
  have h2 := Eval.push ([] : List (SProg Bool)) true (fun r => Sym.bit r.isNone) (some Sym.mark)
    (Function.update (fun _ => []) false [Sym.mark])
  exact Eval.seq h1 h2

/-! ### T6/T7: no commutation without independence -/

/-- T6: two register loads in the two orders end with different registers (2 steps each). -/
theorem t6 (S : Unit → List Sym) (b : Bool) :
    Eval [] (Prog.seq (Prog.load (fun _ => false)) (Prog.load (fun _ => true)) :
      Prog Unit (fun _ => Sym) Bool) ⟨b, S⟩ ⟨true, S⟩ 2 ∧
    Eval [] (Prog.seq (Prog.load (fun _ => true)) (Prog.load (fun _ => false)) :
      Prog Unit (fun _ => Sym) Bool) ⟨b, S⟩ ⟨false, S⟩ 2 := by
  constructor
  · have h1 := Eval.load ([] : List (Prog Unit (fun _ => Sym) Bool)) (fun _ => false) b S
    have h2 := Eval.load ([] : List (Prog Unit (fun _ => Sym) Bool)) (fun _ => true) false S
    exact Eval.seq h1 h2
  · have h1 := Eval.load ([] : List (Prog Unit (fun _ => Sym) Bool)) (fun _ => true) b S
    have h2 := Eval.load ([] : List (Prog Unit (fun _ => Sym) Bool)) (fun _ => false) true S
    exact Eval.seq h1 h2

/-- T7: a load and a push that reads the register, in the two orders, push different bits. -/
theorem t7 (S : Unit → List Sym) :
    Eval [] (Prog.seq (Prog.load (fun _ => true)) (Prog.push () (fun r => Sym.bit r)) :
      Prog Unit (fun _ => Sym) Bool) ⟨false, S⟩
      ⟨true, Function.update S () (Sym.bit true :: S ())⟩ 2 ∧
    Eval [] (Prog.seq (Prog.push () (fun r => Sym.bit r)) (Prog.load (fun _ => true)) :
      Prog Unit (fun _ => Sym) Bool) ⟨false, S⟩
      ⟨true, Function.update S () (Sym.bit false :: S ())⟩ 2 := by
  constructor
  · have h1 := Eval.load ([] : List (Prog Unit (fun _ => Sym) Bool)) (fun _ => true) false S
    have h2 := Eval.push ([] : List (Prog Unit (fun _ => Sym) Bool)) () (fun r => Sym.bit r) true S
    exact Eval.seq h1 h2
  · have h1 := Eval.push ([] : List (Prog Unit (fun _ => Sym) Bool)) () (fun r => Sym.bit r) false S
    have h2 := Eval.load ([] : List (Prog Unit (fun _ => Sym) Bool)) (fun _ => true) false
      (Function.update S () (Sym.bit false :: S ()))
    exact Eval.seq h1 h2

/-! ### T8: open programs depend on the environment -/

/-- T8: `recur 0` in the two load environments ends with different registers (3 steps each). -/
theorem t8 (S : Unit → List Sym) (b : Bool) :
    Eval [Prog.load (fun _ => false)] (Prog.recur 0 : Prog Unit (fun _ => Sym) Bool) ⟨b, S⟩
      ⟨false, S⟩ 3 ∧
    Eval [Prog.load (fun _ => true)] (Prog.recur 0 : Prog Unit (fun _ => Sym) Bool) ⟨b, S⟩
      ⟨true, S⟩ 3 := by
  constructor
  · have h := Eval.load ([Prog.load (fun _ => false)] : List (Prog Unit (fun _ => Sym) Bool))
      (fun _ => false) b S
    exact Eval.recur (n := 0) rfl h
  · have h := Eval.load ([Prog.load (fun _ => true)] : List (Prog Unit (fun _ => Sym) Bool))
      (fun _ => true) b S
    exact Eval.recur (n := 0) rfl h

/-! ### T9: the framed set only shrinks along a call -/

/-- T9: `spy` on an empty stack is safe for the empty framed set but not for the full one. The
`hframe` condition needed to transport the first fact to the full framed set is false. -/
theorem t9 :
    SafeRunsIn (fun _ : Unit => False) [] spy (fun _ => []) (fun _ => []) (fun _ => True) 1 ∧
    ¬ SafeRunsIn (fun _ : Unit => True) [] spy (fun _ => []) (fun _ => []) (fun _ => True) 1 ∧
    ¬ (∀ x : Unit, (fun _ : Unit => True) (id x) → (fun _ : Unit => False) x) := by
  refine ⟨fun v => ⟨none, 1, ?_, trivial, le_rfl⟩, t1_not_safe, fun h => h () trivial⟩
  have h := SafeEval.peek (framed := fun _ : Unit => False) [] () (fun _ o => o) v
    (fun _ => []) (fun h => h.elim)
  exact h

/-! ### T19: a child may clobber the register -/

/-- Push a `mark`, clear the register, pop the `mark` back into the register. -/
def clobber : SProg Unit := .seq (pushC () Sym.mark) (.seq (.load (fun _ => none)) (popR ()))

/-- T19: the final register is `some mark`, whatever the initial register; 3 steps. -/
theorem t19 (S : Unit → List Sym) (v : Option Sym) :
    Eval [] clobber ⟨v, S⟩ ⟨some Sym.mark, S⟩ 3 := by
  have h1 := Eval.push ([] : List (SProg Unit)) () (fun _ => Sym.mark) v S
  have h2 := Eval.load ([] : List (SProg Unit)) (fun _ => none) v
    (Function.update S () (Sym.mark :: S ()))
  have h3 := Eval.pop ([] : List (SProg Unit)) () (fun _ o => o) none
    (Function.update S () (Sym.mark :: S ()))
  refine (Eval.seq h1 (Eval.seq h2 h3)).of_eq ?_ rfl
  have hS : Function.update (Function.update S () (Sym.mark :: S ())) ()
      (Function.update S () (Sym.mark :: S ()) ()).tail = S := by
    funext k
    cases k
    simp
  rw [hS]
  simp

/-! ### T22: the mulBig scratch bank does not fit `W5_mulAt`'s -/

/-- T22: there is no injection from 76 scratch stacks into 8. -/
theorem t22 : ¬ ∃ f : Fin 76 → Fin 8, Function.Injective f := by
  rintro ⟨f, hf⟩
  exact absurd (Fintype.card_le_of_injective f hf) (by simp)

/-! ### T23: pointwise witnesses are not uniform -/

/-- T23: for each bit there is a program pushing it, but no single program pushes both from the
same initial state. -/
theorem t23 :
    (∀ b : Bool, ∃ P : SProg Unit, Runs P (fun _ => []) (fun _ => [Sym.bit b]) (fun _ => True) 1) ∧
    ¬ ∃ P : SProg Unit, ∀ b : Bool,
      Runs P (fun _ => []) (fun _ => [Sym.bit b]) (fun _ => True) 1 := by
  constructor
  · intro b
    refine ⟨pushC () (Sym.bit b), ?_⟩
    intro s hs
    obtain ⟨v, stk⟩ := s
    change stk = (fun _ => []) at hs
    subst hs
    refine ⟨⟨v, fun _ => [Sym.bit b]⟩, 1, ?_, ⟨rfl, trivial⟩, le_rfl⟩
    have h := Eval.push ([] : List (SProg Unit)) () (fun _ => Sym.bit b) v (fun _ => [])
    refine h.of_eq ?_ rfl
    have hS : Function.update (fun _ : Unit => ([] : List Sym)) () ([Sym.bit b] ++ []) =
        fun _ => [Sym.bit b] := by
      funext k
      cases k
      simp
    simpa using hS
  · rintro ⟨P, hP⟩
    obtain ⟨s₁, t₁, e₁, ⟨h₁, -⟩, -⟩ := hP true ⟨none, fun _ => []⟩ rfl
    obtain ⟨s₂, t₂, e₂, ⟨h₂, -⟩, -⟩ := hP false ⟨none, fun _ => []⟩ rfl
    have key : (fun _ : Unit => [Sym.bit true]) = (fun _ => [Sym.bit false]) :=
      h₁.symm.trans ((congrArg St.stk (e₁.det e₂).1).trans h₂)
    have := congrFun key ()
    simp at this

/-! ### T24: an empty tail class makes `FramedRunsIn` vacuous -/

/-- T24: with no admissible tail, `FramedRunsIn` holds for any claimed final stacks. -/
theorem t24 (S S' : Unit → List Sym) (Q : Option Sym → Prop) (T : ℕ) :
    FramedRunsIn (fun _ _ => False) [] spy S S' Q T :=
  fun _ hτ => (hτ ()).elim

/-! ### T10–T14: guarded passes (`FramePass`; certificates in `FramePassSafe`) -/

section Passes

variable {K : Type} [DecidableEq K]

/-- T10: empty payload, source `[g]`: pass M costs 2 and the guard remains. -/
theorem t10_passM {g : Sym} {src dst : K} (hne : src ≠ dst) (S : K → List Sym)
    (hS : S src = [g]) :
    SafeRunsIn (fun _ => True) [] (passM g src dst) S
      (Function.update (Function.update S src [g]) dst (S dst)) (fun r => r = some g) 2 :=
  safe_passM hne [] [] (by simp) S hS []

/-- T10: pass F on an empty payload costs 2. -/
theorem t10_passF {g : Sym} {src d₁ d₂ : K} (h1 : src ≠ d₁) (h2 : src ≠ d₂) (h12 : d₁ ≠ d₂)
    (S : K → List Sym) (hS : S src = [g]) :
    SafeRunsIn (fun _ => True) [] (passF g src d₁ d₂) S
      (Function.update (Function.update (Function.update S src [g]) d₁ (S d₁)) d₂ (S d₂))
      (fun r => r = some g) 2 :=
  safe_passF h1 h2 h12 [] [] (by simp) S hS []

/-- T10: pass E on an empty payload costs 2. -/
theorem t10_passE {g : Sym} {src : K} (S : K → List Sym) (hS : S src = [g]) :
    SafeRunsIn (fun _ => True) [] (passE g src) S (Function.update S src [g])
      (fun r => r = some g) 2 :=
  safe_passE [] [] (by simp) S hS []

/-- T10: passes S and C on an empty payload, with a guarded temporary, cost 4 each. -/
theorem t10_passS_passC {g : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (S : K → List Sym) (hS : S src = [g]) (hT : S tmp = [g]) :
    SafeRunsIn (fun _ => True) [] (passS g src tmp dst) S
      (Function.update (Function.update S src [g]) dst (S dst)) (fun r => r = some g) 4 ∧
    SafeRunsIn (fun _ => True) [] (passC g src tmp dst) S (Function.update S dst (S dst))
      (fun r => r = some g) 4 :=
  ⟨safe_passS h1 h2 h3 [] [] [] (by simp) S hS hT [],
    safe_passC h1 h2 h3 [] [] [] (by simp) S hS hT []⟩

/-- T11: pass M reverses a two-bit payload (cost 10); pass F costs 12; pass E costs 8. -/
theorem t11 {g : Sym} {src d₁ d₂ : K} (h1 : src ≠ d₁) (h2 : src ≠ d₂) (h12 : d₁ ≠ d₂)
    (hg : g ∉ [Sym.bit false, Sym.bit true]) (S : K → List Sym)
    (hS : S src = [Sym.bit false, Sym.bit true, g]) :
    SafeRunsIn (fun _ => True) [] (passM g src d₁) S
      (Function.update (Function.update S src [g]) d₁ (Sym.bit true :: Sym.bit false :: S d₁))
      (fun r => r = some g) 10 ∧
    SafeRunsIn (fun _ => True) [] (passF g src d₁ d₂) S
      (Function.update (Function.update (Function.update S src [g]) d₁
        (Sym.bit true :: Sym.bit false :: S d₁)) d₂ (Sym.bit true :: Sym.bit false :: S d₂))
      (fun r => r = some g) 12 ∧
    SafeRunsIn (fun _ => True) [] (passE g src) S (Function.update S src [g])
      (fun r => r = some g) 8 :=
  ⟨safe_passM h1 _ [] hg S hS [], safe_passF h1 h2 h12 _ [] hg S hS [],
    safe_passE _ [] hg S hS []⟩

/-- T12: pass S keeps the orientation of a two-bit payload (cost 20). Pass C keeps the source and
copies with the same orientation (cost 22). -/
theorem t12 {g : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst) (h3 : src ≠ dst)
    (hg : g ∉ [Sym.bit false, Sym.bit true]) (S : K → List Sym)
    (hS : S src = [Sym.bit false, Sym.bit true, g]) (hT : S tmp = [g]) :
    SafeRunsIn (fun _ => True) [] (passS g src tmp dst) S
      (Function.update (Function.update S src [g]) dst (Sym.bit false :: Sym.bit true :: S dst))
      (fun r => r = some g) 20 ∧
    SafeRunsIn (fun _ => True) [] (passC g src tmp dst) S
      (Function.update S dst (Sym.bit false :: Sym.bit true :: S dst)) (fun r => r = some g) 22 :=
  ⟨safe_passS h1 h2 h3 _ [] [] hg S hS hT [], safe_passC h1 h2 h3 _ [] [] hg S hS hT []⟩

/-- T13: on a missing guard (`none`) the loop test `notG g` is `true`. An empty source is not a
stopping condition, so no guarded specification follows for it. -/
theorem t13 (g : Sym) : notG g none = true := by simp [notG]

omit [DecidableEq K] in
/-- T14: the alias `src = dst` violates the distinctness hypotheses of passes M/S/C. -/
theorem t14 (k : K) : ¬ (k ≠ k) := fun h => h rfl

end Passes

/-! ### T15–T18: families (`ParkAll`) -/

section Families

variable {K σ : Type} [DecidableEq K]

/-- T15: protecting the empty family around a 1-step child takes exactly 3 steps (the two
`skip`s of the empty traversals are charged). -/
theorem t15 (l : Lens σ (Option Sym)) (S : K → List Sym) (v : σ) :
    Eval [] (protectAllCall l [] (.load id)) ⟨v, S⟩ ⟨v, S⟩ 3 := by
  have h1 := skip_eval ([] : List (Prog K (fun _ => Sym) σ)) ⟨v, S⟩
  have h2 := Eval.load ([] : List (Prog K (fun _ => Sym) σ)) id v S
  exact Eval.seq h1 (Eval.seq h2 h1)

/-- T16: parking the empty family around a 1-step child takes exactly 5 steps. -/
theorem t16 (l : Lens σ (Option Sym)) (p : K) (S : K → List Sym) (v : σ) :
    ∃ s', Eval [] (parkAllCall l [] p (.load id)) ⟨v, S⟩ s' 5 := by
  have e0 := skip_eval ([] : List (Prog K (fun _ => Sym) σ)) ⟨v, S⟩
  have e1 := Eval.push ([] : List (Prog K (fun _ => Sym) σ)) p
    (fun w => (fun _ => Sym.mark) (l.get w)) v S
  have e2 := Eval.load ([] : List (Prog K (fun _ => Sym) σ)) id v
    (Function.update S p ((fun w => (fun _ => Sym.mark) (l.get w)) v :: S p))
  have e3 := Eval.pop ([] : List (Prog K (fun _ => Sym) σ)) p
    (fun w o => l.set w ((fun _ o => o) (l.get w) o)) (id v)
    (Function.update S p ((fun w => (fun _ => Sym.mark) (l.get w)) v :: S p))
  exact ⟨_, Eval.seq e0 (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (skip_eval _ _))))⟩

/-- T17: protecting the duplicated family `[k, k]` pushes two marks on `k` (3 steps), while
`protState [k, k]` has one. The one-mark theorem needs `Nodup`. -/
theorem t17 (l : Lens σ (Option Sym)) (k : K) (S : K → List Sym) (v : σ) :
    (∃ s', Eval [] (protectAll l [k, k]) ⟨v, S⟩ s' 3 ∧
      s'.stk k = Sym.mark :: Sym.mark :: S k) ∧
    protState [k, k] S k = Sym.mark :: S k := by
  refine ⟨?_, by simp [protState]⟩
  have e1 := Eval.push ([] : List (Prog K (fun _ => Sym) σ)) k
    (fun w => (fun _ => Sym.mark) (l.get w)) v S
  have e2 := Eval.push ([] : List (Prog K (fun _ => Sym) σ)) k
    (fun w => (fun _ => Sym.mark) (l.get w)) v
    (Function.update S k ((fun w => (fun _ => Sym.mark) (l.get w)) v :: S k))
  refine ⟨_, Eval.seq e1 (Eval.seq e2 (skip_eval _ _)), ?_⟩
  simp

omit [DecidableEq K] in
/-- T18: parking `[a, b]` puts the block of `b` on top, so unparking must traverse `[b, a]`. -/
theorem t18 (a b : K) (es : K → List Sym) :
    parked [a, b] es = (es b).reverse ++ [Sym.mark] ++ (es a).reverse ++ [Sym.mark] ∧
    ([a, b] : List K).reverse = [b, a] := by
  constructor
  · simp [parked]
  · rfl

end Families

/-! ### T20/T21: headers (`Hdr`, `HdrFacts`) -/

/-- T20: the header of the fields `[0, 1]` is `[mark, bit true, mark]`. It starts with a `mark`,
so a mark-delimited pass stops immediately. -/
theorem t20 : W9.hdrSyms [0, 1] = [Sym.mark, Sym.bit true, Sym.mark] := by
  have h0 : Computability.encodeNat 0 = [] := TMFw.encodeNat_zero
  have h1 : Computability.encodeNat 1 = [true] := by
    have := TMFw.encodeNat_add_add_one 0
    simpa [h0] using this
  simp [W9.hdrSyms, natSyms, h0, h1]

/-- T21: no `tag j` occurs in any header. A whole descriptor still needs `kind ≠ tag 13`
(`HdrFacts.tag13_not_mem_descPayload`). -/
theorem t21 (j : Fin 16) (fs : List ℕ) : Sym.tag j ∉ W9.hdrSyms fs :=
  HdrFacts.tag_not_mem_hdrSyms j fs

#assert_std_axioms t1_framed t1_not_safe t2_eval t2_not_safe t3_safe t3_tail t4_empty t4_mark
  t4_framed t5_empty t5_guarded t6 t7 t8 t9 t19 t22 t23 t24 t10_passM t10_passF t10_passE
  t10_passS_passC t11 t12 t13 t14 t15 t16 t17 t18 t20 t21

end SubNLogN.Machine.Calculus.Regression
