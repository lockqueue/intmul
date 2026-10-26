import WP.W3.Rip

/-!
# WP.W3.AddLoop — the ripple loop on the machine

Stacks `Loc 3 3`: operands `kX = .inl 0`, `kY = .inl 1`, destination `kZ = .inl 2`; scratch
`kTX`, `kTY` (receive the operand bits, to be moved back) and `kT` (out bits, carry on top).
Registers `AReg = Option Sym × Option Sym × Bool`: the peeked tops of `kX`, `kY`, and the carry.

One iteration (`ripBody f`): pop the carry from `kT`; move the next bit of `kX` (if any) onto
`kTX`, same for `kY`/`kTY`; push the out bit and then the new carry onto `kT`; peek `kX`, `kY`.
`ripLoop f` runs while a peeked symbol is a bit: `max |A| |B|` iterations, cost `≤ 12·max + 1`
(`ripLoop_eval`). On exit `kT` holds `(rip f n c A B).reverse` above the old content.
-/

namespace WP.W3

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Atoms with rewritten end states -/

section Atoms

variable {K σ : Type} [DecidableEq K]

theorem eval_stk {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ}
    {s : St K (fun _ => Sym) σ} {v : σ} {S₁ S₂ : K → List Sym} {t : ℕ}
    (h : Eval ρ p s ⟨v, S₁⟩ t) (hS : S₁ = S₂) : Eval ρ p s ⟨v, S₂⟩ t := by
  subst hS
  exact h

theorem eval_pop_eq (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ)
    (v : σ) (S : K → List Sym) (x : Sym) (L : List Sym) (hS : S k = x :: L) :
    Eval ρ (.pop k f) ⟨v, S⟩ ⟨f v (some x), Function.update S k L⟩ 1 :=
  (Eval.pop ρ k f v S).of_eq (by simp only [hS, List.head?_cons, List.tail_cons]) rfl

theorem eval_peek_eq (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ)
    (v : σ) (S : K → List Sym) (o : Option Sym) (ho : (S k).head? = o) :
    Eval ρ (.peek k f) ⟨v, S⟩ ⟨f v o, S⟩ 1 :=
  (Eval.peek ρ k f v S).of_eq (by rw [ho]) rfl

theorem eval_push_eq (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Sym) (v : σ)
    (S : K → List Sym) (x : Sym) (L : List Sym) (hx : f v = x) (hL : S k = L) :
    Eval ρ (.push k f) ⟨v, S⟩ ⟨v, Function.update S k (x :: L)⟩ 1 :=
  (Eval.push ρ k f v S).of_eq (by rw [hx, hL]) rfl

end Atoms

/-! ## Stacks, registers, programs -/

/-- Registers: peeked tops of the two operands, carry. -/
abbrev AReg : Type := Option Sym × Option Sym × Bool

/-- Programs of the add/sub kernel. -/
abbrev AProg : Type := Prog (Loc 3 3) (fun _ => Sym) AReg

/-- First operand. -/
abbrev kX : Loc 3 3 := .inl 0
/-- Second operand. -/
abbrev kY : Loc 3 3 := .inl 1
/-- Destination. -/
abbrev kZ : Loc 3 3 := .inl 2
/-- Scratch: bits taken from `kX`. -/
abbrev kTX : Loc 3 3 := .inr 0
/-- Scratch: bits taken from `kY`. -/
abbrev kTY : Loc 3 3 := .inr 1
/-- Scratch: out bits, carry on top. -/
abbrev kT : Loc 3 3 := .inr 2

theorem stk_ext33 {S S' : Loc 3 3 → List Sym} (h0 : S kX = S' kX) (h1 : S kY = S' kY)
    (h2 : S kZ = S' kZ) (h3 : S kTX = S' kTX) (h4 : S kTY = S' kTY) (h5 : S kT = S' kT) :
    S = S' := by
  funext k
  rcases k with ⟨_ | _ | _ | n, hn⟩ | ⟨_ | _ | _ | n, hn⟩
  · exact h0
  · exact h1
  · exact h2
  · omega
  · exact h3
  · exact h4
  · exact h5
  · omega

/-- Pop `k` (discarding) and push the peeked symbol `g v` onto `t`, if `g v` is a bit. -/
def condMove (k t : Loc 3 3) (g : AReg → Option Sym) : AProg :=
  .ite (fun v => optIsBit (g v)) (.seq (.pop k fun v _ => v) (.push t fun v => (g v).getD .sep))
    skip

/-- Pop the carry from `kT`. -/
def popCarry : AProg := .pop kT fun v o => (v.1, v.2.1, optBit o)

/-- Push the out bit onto `kT`. -/
def pushOut (f : Bool → Bool → Bool → Bool × Bool) : AProg :=
  .push kT fun v => .bit (f (optBit v.1) (optBit v.2.1) v.2.2).1

/-- Push the new carry onto `kT`. -/
def pushCarry (f : Bool → Bool → Bool → Bool × Bool) : AProg :=
  .push kT fun v => .bit (f (optBit v.1) (optBit v.2.1) v.2.2).2

/-- Peek the first operand. -/
def peekX : AProg := .peek kX fun v o => (o, v.2)

/-- Peek the second operand. -/
def peekY : AProg := .peek kY fun v o => (v.1, o, v.2.2)

/-- One ripple step. -/
def ripBody (f : Bool → Bool → Bool → Bool × Bool) : AProg :=
  .seq popCarry (.seq (condMove kX kTX (·.1)) (.seq (condMove kY kTY (·.2.1))
    (.seq (pushOut f) (.seq (pushCarry f) (.seq peekX peekY)))))

/-- The ripple loop. -/
def ripLoop (f : Bool → Bool → Bool → Bool × Bool) : AProg :=
  .loop (fun v => optIsBit v.1 || optIsBit v.2.1) (ripBody f)

/-! ## One step -/

theorem optIsBit_head?_map {r : List Sym} (hr : TermOK r) :
    ∀ A : List Bool, optIsBit (A.map Sym.bit ++ r).head? = decide (0 < A.length)
  | [] => by simp [optIsBit_head?_of_termOK hr]
  | _ :: _ => by simp

theorem condMove_eval {k t : Loc 3 3} (hkt : k ≠ t) (g : AReg → Option Sym) (v : AReg)
    (A : List Bool) (rk : List Sym) (hrk : TermOK rk) (S : Loc 3 3 → List Sym)
    (hS : S k = A.map Sym.bit ++ rk) (hg : g v = (A.map Sym.bit ++ rk).head?) :
    ∃ n, n ≤ 3 ∧ Eval [] (condMove k t g) ⟨v, S⟩
      ⟨v, Function.update (Function.update S k (A.tail.map Sym.bit ++ rk)) t
        ((A.take 1).map Sym.bit ++ S t)⟩ n := by
  cases A with
  | nil =>
    have hS' : S k = rk := hS
    refine ⟨2, by omega, eval_stk (Eval.ite_false ?_ (skip_eval [] _)) ?_⟩
    · show optIsBit (g v) = false
      rw [hg]
      exact optIsBit_head?_of_termOK hrk
    · simp only [List.tail_nil, List.take_nil, List.map_nil, List.nil_append]
      rw [← hS', Function.update_eq_self, Function.update_eq_self]
  | cons a A =>
    have hS' : S k = Sym.bit a :: (A.map Sym.bit ++ rk) := hS
    have hg' : g v = some (Sym.bit a) := hg
    have e1 := eval_pop_eq [] k (fun (v : AReg) _ => v) v S (.bit a) _ hS'
    have e2 := eval_push_eq [] t (fun v => (g v).getD .sep) v
      (Function.update S k (A.map Sym.bit ++ rk)) (.bit a) (S t) (by simp only [hg', Option.getD_some])
      (Function.update_of_ne (Ne.symm hkt) _ _)
    refine ⟨3, le_refl _, eval_stk (Eval.ite_true ?_ (Eval.seq e1 e2)) ?_⟩
    · show optIsBit (g v) = true
      rw [hg']
      rfl
    · rfl

#assert_std_axioms eval_stk eval_pop_eq eval_peek_eq eval_push_eq stk_ext33 optIsBit_head?_map
  condMove_eval

end WP.W3
