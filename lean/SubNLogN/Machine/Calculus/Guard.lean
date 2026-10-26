/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Park

/-!
# Framed procedure calculus (`Calculus/Guard.lean`): parking with arbitrary delimiter symbols

`Calculus/Park.lean` uses `mark` for everything. Multi-field descriptor procedures
can instead use distinct delimiter tags, e.g. a protected boundary
`Sym.tag 7` below each live stream, a parked-stream separator `Sym.tag 8` and a saved-descriptor
separator `Sym.tag 9` (descriptors themselves contain `mark`s). This file generalizes the parking
layer to arbitrary delimiter symbols; the `mark` versions are the instance `stop = psep = guard =
mark` (`park_eq_parkG`, `unpark_eq_unparkG`, `stopTail_mark_iff`, `freeOf_mark_iff`).

* `StopTail g tl`: `tl` is empty or starts with `g`; `FreeOf g l`: `g` does not occur in `l`.
* `moveUntil g src dst`: move the block above the first `g` of `src` onto `dst` (reversed); the `g`
  (or `none`) goes to the register; cost `3·|block| + 2`.
* `parkG stop psep r p`: push `psep` on `p`, move the `stop`-free block above `r`'s `stop`-tail onto
  `p`, restore `r`'s `stop`; cost `3·|block| + 5`. `unparkG psep p r`: move the block above `p`'s
  top `psep` back onto `r`, drop that `psep`; cost `3·|block| + 2`.
* `runsIn_parkCallG`: `parkG stop psep r p ; push guard on p ; child ; pop p ; unparkG psep p r`; the
  child sees `r` in its `stop`-tail state and `p` with `guard` on top; overhead `6·|block| + 9`.
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

/-! ## Delimiter vocabulary -/

/-- `tl` is empty or starts with the delimiter `g`. -/
def StopTail (g : Sym) (tl : List Sym) : Prop := tl = [] ∨ tl.head? = some g

/-- The delimiter `g` does not occur in `l`. -/
def FreeOf (g : Sym) (l : List Sym) : Prop := ∀ d ∈ l, d ≠ g

theorem stopTail_mark_iff (tl : List Sym) : StopTail Sym.mark tl ↔ FrameTail tl := Iff.rfl

theorem freeOf_mark_iff (l : List Sym) : FreeOf Sym.mark l ↔ MarkFree l := Iff.rfl

theorem StopTail.cons (g : Sym) (l : List Sym) : StopTail g (g :: l) := Or.inr rfl

theorem FreeOf.reverse {g : Sym} {l : List Sym} (h : FreeOf g l) : FreeOf g l.reverse :=
  fun d hd => h d (List.mem_reverse.mp hd)

/-- Bit blocks are free of every non-bit delimiter. -/
theorem FreeOf.bits {g : Sym} (hg : g.isBit = false) (es : List Bool) :
    FreeOf g (es.map Sym.bit) := by
  intro d hd h
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hd
  subst h
  exact absurd hg (by simp [Sym.isBit])

section Programs

variable {K : Type}

/-- Loop guard: the register holds a symbol other than `g`. -/
def notSymR (g : Sym) (r : Option Sym) : Bool :=
  match r with
  | some d => !decide (d = g)
  | none => false

/-- Move the block above the first `g` of `src` onto `dst` (reversed). -/
def moveUntil (g : Sym) (src dst : K) : SProg K :=
  .seq (popR src) (.loop (notSymR g) (moveBitsBody src dst))

/-- **Park** the `stop`-free block above `r`'s `stop`-tail on `p`, above a new `psep`. -/
def parkG (stop psep : Sym) (r p : K) : SProg K :=
  .seq (pushC p psep) (.seq (moveUntil stop r p) (restoreR r))

/-- **Unpark**: move the block above `p`'s top `psep` back onto `r`; drop that `psep`. -/
def unparkG (psep : Sym) (p r : K) : SProg K := moveUntil psep p r

theorem notSymR_mark : notSymR Sym.mark = notMarkR := by
  funext r
  cases r <;> rfl

theorem moveUntil_mark (src dst : K) : moveUntil Sym.mark src dst = moveToMark src dst := by
  simp [moveUntil, moveToMark, notSymR_mark]

theorem park_eq_parkG (r p : K) : park r p = parkG Sym.mark Sym.mark r p := by
  simp [park, parkG, moveUntil_mark]

theorem unpark_eq_unparkG (p r : K) : unpark p r = unparkG Sym.mark p r := by
  simp [unpark, unparkG, moveUntil_mark]

theorem closed_moveUntil (g : Sym) (src dst : K) : (moveUntil g src dst).Closed := by
  simp [Prog.Closed, moveUntil, Prog.FreeBelow, moveBitsBody, pushR, popR]

theorem closed_parkG (stop psep : Sym) (r p : K) : (parkG stop psep r p).Closed := by
  simp [Prog.Closed, parkG, moveUntil, Prog.FreeBelow, moveBitsBody, pushR, popR, pushC,
    restoreR, Lib.skip]

theorem closed_unparkG (psep : Sym) (p r : K) : (unparkG psep p r).Closed :=
  closed_moveUntil psep p r

end Programs

section Eval

variable {K : Type} [DecidableEq K]

theorem notSymR_head?_of_stopTail {g : Sym} {rest : List Sym} (h : StopTail g rest) :
    notSymR g rest.head? = false := by
  rcases h with rfl | h
  · rfl
  · rw [h]
    simp [notSymR]

theorem moveUntil_loop_eval {g : Sym} {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) :
    ∀ (es rest : List Sym) (S : K → List Sym), FreeOf g es → StopTail g rest →
      S src = (es ++ rest).tail →
      Eval ρ (.loop (notSymR g) (moveBitsBody src dst)) ⟨(es ++ rest).head?, S⟩
        ⟨rest.head?, Function.update (Function.update S src rest.tail) dst (es.reverse ++ S dst)⟩
        (3 * es.length + 1)
  | [], rest, S, _, hrest, hS => by
    refine (Eval.loop_false (notSymR_head?_of_stopTail hrest)).of_eq ?_ rfl
    have hS' : S src = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update (Function.update S src rest.tail)
      dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | e :: es, rest, S, hes, hrest, hS => by
    have he : e ≠ g := hes e List.mem_cons_self
    have hes' : FreeOf g es := fun d hd => hes d (List.mem_cons_of_mem e hd)
    have hS' : S src = es ++ rest := hS
    have hpush : Eval ρ (pushR dst) ⟨some e, S⟩ ⟨some e, Function.update S dst (e :: S dst)⟩ 1 :=
      (Eval.push ρ dst (fun r => r.getD .sep) (some e) S).of_eq rfl rfl
    have hsrc : Function.update S dst (e :: S dst) src = es ++ rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval ρ (popR src) ⟨some e, Function.update S dst (e :: S dst)⟩
        ⟨(es ++ rest).head?, Function.update (Function.update S dst (e :: S dst))
          src (es ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := moveUntil_loop_eval hne ρ es rest
      (Function.update (Function.update S dst (e :: S dst)) src (es ++ rest).tail) hes' hrest
      (Function.update_self _ _ _)
    have hc : notSymR g (some e) = true := by simp [notSymR, he]
    refine (Eval.loop_true hc (Eval.seq hpush hpop) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **moveUntil**, exact. -/
theorem moveUntil_eval {g : Sym} {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K))
    (v : Option Sym) (es rest : List Sym) (S : K → List Sym) (hes : FreeOf g es)
    (hrest : StopTail g rest) (hS : S src = es ++ rest) :
    Eval ρ (moveUntil g src dst) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S src rest.tail) dst (es.reverse ++ S dst)⟩
      (3 * es.length + 2) := by
  have h1 : Eval ρ (popR src) ⟨v, S⟩
      ⟨(es ++ rest).head?, Function.update S src (es ++ rest).tail⟩ 1 := by
    refine (Eval.pop ρ src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := moveUntil_loop_eval hne ρ es rest (Function.update S src (es ++ rest).tail) hes hrest
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- **parkG**, exact. -/
theorem parkG_eval {stop psep : Sym} {r p : K} (hrp : r ≠ p) (ρ : List (SProg K))
    (v : Option Sym) (es rest : List Sym) (S : K → List Sym) (hes : FreeOf stop es)
    (hrest : StopTail stop rest) (hS : S r = es ++ rest) :
    Eval ρ (parkG stop psep r p) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S r rest) p (es.reverse ++ psep :: S p)⟩
      (3 * es.length + 5) := by
  have e0 : Eval ρ (pushC p psep) ⟨v, S⟩ ⟨v, Function.update S p (psep :: S p)⟩ 1 :=
    Eval.push ρ p (fun _ => psep) v S
  have e1 := moveUntil_eval hrp ρ v es rest (Function.update S p (psep :: S p)) hes hrest
    (by rw [Function.update_of_ne hrp]; exact hS)
  have e2 := restoreR_eval ρ r rest
    (Function.update (Function.update (Function.update S p (psep :: S p)) r rest.tail) p
      (es.reverse ++ Function.update S p (psep :: S p) p))
    (by rw [Function.update_of_ne hrp, Function.update_self])
  refine (Eval.seq e0 (Eval.seq e1 e2)).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- **unparkG**, exact. -/
theorem unparkG_eval {psep : Sym} {p r : K} (hpr : p ≠ r) (ρ : List (SProg K)) (v : Option Sym)
    (es pt : List Sym) (S : K → List Sym) (hes : FreeOf psep es)
    (hS : S p = es.reverse ++ psep :: pt) :
    Eval ρ (unparkG psep p r) ⟨v, S⟩
      ⟨some psep, Function.update (Function.update S p pt) r (es ++ S r)⟩ (3 * es.length + 2) := by
  have h := moveUntil_eval hpr ρ v es.reverse (psep :: pt) S hes.reverse (StopTail.cons psep pt) hS
  refine h.of_eq ?_ (by rw [List.length_reverse])
  rw [List.reverse_reverse]
  rfl

theorem runs_parkG {stop psep : Sym} {r p : K} (hrp : r ≠ p) (es rest : List Sym)
    (S : K → List Sym) (hes : FreeOf stop es) (hrest : StopTail stop rest)
    (hS : S r = es ++ rest) :
    Runs (parkG stop psep r p) S
      (Function.update (Function.update S r rest) p (es.reverse ++ psep :: S p))
      (fun _ => True) (3 * es.length + 5) :=
  Runs.of_eval fun v => ⟨_, _, parkG_eval hrp [] v es rest S hes hrest hS, trivial, le_rfl⟩

theorem runs_unparkG {psep : Sym} {p r : K} (hpr : p ≠ r) (es pt : List Sym) (S : K → List Sym)
    (hes : FreeOf psep es) (hS : S p = es.reverse ++ psep :: pt) :
    Runs (unparkG psep p r) S (Function.update (Function.update S p pt) r (es ++ S r))
      (fun _ => True) (3 * es.length + 2) :=
  Runs.of_eval fun v => ⟨_, _, unparkG_eval hpr [] v es pt S hes hS, trivial, le_rfl⟩

/-- Pop the top symbol, whatever it is. -/
theorem runs_popR (k : K) (S : K → List Sym) (d : Sym) (tl : List Sym) (hS : S k = d :: tl) :
    Runs (unprotect k) S (Function.update S k tl) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨some d, 1, by
    have h := Eval.pop ([] : List (SProg K)) k (fun _ o => o) v S
    rw [hS] at h
    exact h, trivial, le_rfl⟩

/-- Push a constant guard symbol. -/
theorem runs_pushC (k : K) (g : Sym) (S : K → List Sym) :
    Runs (pushC k g) S (Function.update S k (g :: S k)) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, by
    have h := Eval.push ([] : List (SProg K)) k (fun _ => g) v S
    exact h, trivial, le_rfl⟩

end Eval

/-! ## Call with parking, general delimiters -/

section Calls

variable {K σ : Type} [DecidableEq K]

/-- **Call with parking (general delimiters)**: `parkG stop psep r p ; push guard on p ; child ;
pop p ; unparkG psep p r`. -/
def parkCallG (stop psep guard : Sym) (l : Lens σ (Option Sym)) (r p : K)
    (child : Prog K (fun _ => Sym) σ) : Prog K (fun _ => Sym) σ :=
  .seq ((parkG stop psep r p).liftRegs l) (.seq ((pushC p guard).liftRegs l) (.seq child
    (.seq ((unprotect p).liftRegs l) ((unparkG psep p r).liftRegs l))))

omit [DecidableEq K] in
theorem closed_parkCallG (stop psep guard : Sym) (l : Lens σ (Option Sym)) (r p : K)
    {child : Prog K (fun _ => Sym) σ} (hc : child.Closed) :
    (parkCallG stop psep guard l r p child).Closed :=
  ⟨WP.W9comp.closed_liftRegs l (closed_parkG stop psep r p),
    WP.W9comp.closed_liftRegs l (by simp [Prog.Closed, pushC, Prog.FreeBelow]), hc,
    WP.W9comp.closed_liftRegs l (closed_unprotect p),
    WP.W9comp.closed_liftRegs l (closed_unparkG psep p r)⟩

/-- **The parking rule, general delimiters.** The parent's `r` holds a block `es` (free of `stop`
and of `psep`) above its `stop`-tail `rest`. The child runs with `r = rest` and with
`p = guard :: es.reverse ++ psep :: (old p)`; it may rewrite `r` and must restore `p`. Then the
call puts `es` back on top of the child's `r` and restores the old `p`; overhead `6·|es| + 9`. -/
theorem runsIn_parkCallG {ρ : List (Prog K (fun _ => Sym) σ)} {stop psep guard : Sym}
    (l : Lens σ (Option Sym)) {r p : K} (hrp : r ≠ p) {child : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (es rest : List Sym) (hes : FreeOf stop es)
    (hes' : FreeOf psep es) (hrest : StopTail stop rest) (hSr : S r = es ++ rest)
    (hchild : RunsIn ρ child
      (Function.update (Function.update S r rest) p (guard :: (es.reverse ++ psep :: S p))) S' Q T)
    (hp' : S' p = guard :: (es.reverse ++ psep :: S p)) :
    RunsIn ρ (parkCallG stop psep guard l r p child) S
      (Function.update (Function.update S' p (S p)) r (es ++ S' r)) (fun _ => True)
      (T + 6 * es.length + 9) := by
  have e1 := RunsIn.of_runs_liftRegs l (runs_parkG (psep := psep) hrp es rest S hes hrest hSr)
    (closed_parkG stop psep r p) ρ
  set S1 := Function.update (Function.update S r rest) p (es.reverse ++ psep :: S p) with hS1
  have e2 := RunsIn.of_runs_liftRegs l (runs_pushC p guard S1)
    (by simp [Prog.Closed, pushC, Prog.FreeBelow]) ρ
  have hS2 : Function.update S1 p (guard :: S1 p) =
      Function.update (Function.update S r rest) p (guard :: (es.reverse ++ psep :: S p)) := by
    rw [hS1, Function.update_self, Function.update_idem]
  rw [hS2] at e2
  have e4 := RunsIn.of_runs_liftRegs l (runs_popR p S' guard _ hp') (closed_unprotect p) ρ
  have e5 := RunsIn.of_runs_liftRegs l
    (runs_unparkG (Ne.symm hrp) es (S p) (Function.update S' p (es.reverse ++ psep :: S p)) hes'
      (Function.update_self _ _ _))
    (closed_unparkG psep p r) ρ
  have hfin : Function.update (Function.update (Function.update S' p (es.reverse ++ psep :: S p))
      p (S p)) r (es ++ Function.update S' p (es.reverse ++ psep :: S p) r) =
      Function.update (Function.update S' p (S p)) r (es ++ S' r) := by
    rw [Function.update_idem, Function.update_of_ne hrp]
  rw [hfin] at e5
  refine RunsIn.mono (RunsIn.seq e1 (RunsIn.seq e2 (RunsIn.seq hchild (RunsIn.seq e4 e5))))
    (fun _ _ => trivial) ?_
  omega

end Calls

#assert_std_axioms stopTail_mark_iff freeOf_mark_iff FreeOf.bits notSymR_mark moveUntil_mark
  park_eq_parkG unpark_eq_unparkG closed_moveUntil closed_parkG closed_unparkG moveUntil_eval
  parkG_eval unparkG_eval runs_parkG runs_unparkG runs_popR runs_pushC closed_parkCallG
  runsIn_parkCallG

end SubNLogN.Machine.Calculus
