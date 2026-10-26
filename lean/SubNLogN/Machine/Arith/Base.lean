/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.Value

/-!
# AR machine base (`Arith/Base.lean`): registers, atoms, and generic mark/bit loops

**Scope (honest summary).** Shared program building blocks for the AR kernels
(`Contracts/Arith.lean`) and their exact evaluation lemmas. Everything is proved (no `sorry`).

## Design (shared by all AR kernels)
* **Registers.** One register type `AReg` for every AR program: `o`, `r`, `q` hold peeked or popped
  symbols (`o` for data sources, `r` for rulers, `q` for buffers), `c`, `st`, `hf`, `sg`, `x`
  are bit flags (carry, sticky, half, sign, scratch), and `ord` holds a comparison result.
  Library programs run through the lenses `lensO` and `lensC`.
* **Rulers.** A count `n` is held in unary as a *ruler*: `n` `mark` symbols on top of a
  delimiter that is not `mark`. Walking a ruler costs `O(1)` per mark.
* **Delimiters.** Every private scratch stack gets a delimiter pushed first and popped last, so its
  arbitrary initial content is never inspected and is restored exactly.
* **Lemmas.** Exact `Eval` lemmas with explicit costs, by induction over the number of marks or
  bits. Final stacks are `Function.update`s of the initial stacks.

## Contents
* `moveMarks X R` moves the marks of `X` onto `R` (`moveMarks_eval`, cost `4n + 2`).
* `clearMarks R` pops the marks of `R` (`clearMarks_eval`, cost `3n + 2`).
* `drainBits B` pops the bits of `B` (`drainBits_eval`, cost `3n + 2`).
* `walkStep_eval`: one step of a ruler walk `walk R X body`.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts

/-! ## Registers -/

/-- Registers of every AR program. -/
structure AReg where
  /-- last symbol read from a data source -/
  o : Option Sym
  /-- last symbol read from a ruler -/
  r : Option Sym
  /-- last symbol read from a buffer -/
  q : Option Sym
  /-- carry -/
  c : Bool
  /-- sticky bit -/
  st : Bool
  /-- half bit (last discarded bit) -/
  hf : Bool
  /-- sign bit (last bit read) -/
  sg : Bool
  /-- scratch bit -/
  x : Bool
  /-- result of a comparison -/
  ord : Ordering

instance : Nonempty AReg := ⟨⟨none, none, none, false, false, false, false, false, .eq⟩⟩

instance : Finite AReg := by
  refine Finite.of_injective
    (fun a : AReg => (a.o, a.r, a.q, a.c, a.st, a.hf, a.sg, a.x, a.ord)) ?_
  rintro ⟨⟩ ⟨⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- Lens on the data register `o` (for library programs with one `Option Sym` register). -/
def lensO : Lens AReg (Option Sym) where
  get v := v.o
  set v x := { v with o := x }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lens on `(o, q, ord)` (for the library comparison `Lib.cmpNum`). -/
def lensC : Lens AReg (Option Sym × Option Sym × Ordering) where
  get v := (v.o, v.q, v.ord)
  set v x := { v with o := x.1, q := x.2.1, ord := x.2.2 }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- AR programs over stacks `K`. -/
abbrev AProg (K : Type) := Prog K (fun _ => Sym) AReg

/-- AR states over stacks `K`. -/
abbrev ASt (K : Type) := St K (fun _ => Sym) AReg

/-- The symbol is `mark`. -/
def isMarkO : Option Sym → Bool
  | some .mark => true
  | _ => false

/-- The symbol is a bit. -/
def isBitO : Option Sym → Bool
  | some (.bit _) => true
  | _ => false

/-- The bit of a symbol, with default `d` for a non-bit. -/
def bitD : Option Sym → Bool → Bool
  | some (.bit b), _ => b
  | _, d => d

@[simp] theorem isMarkO_mark : isMarkO (some .mark) = true := rfl
@[simp] theorem isMarkO_bit (b : Bool) : isMarkO (some (.bit b)) = false := rfl
@[simp] theorem isBitO_bit (b : Bool) : isBitO (some (.bit b)) = true := rfl
@[simp] theorem bitD_bit (b d : Bool) : bitD (some (.bit b)) d = b := rfl

theorem isMarkO_false_of_ne {o : Option Sym} (h : o ≠ some .mark) : isMarkO o = false := by
  rcases o with _ | ⟨_ | _ | _ | _ | _ | _ | _⟩ <;> first | rfl | exact absurd rfl h

theorem isBitO_false_of_termOK {L : List Sym} (h : TermOK L) : isBitO L.head? = false := by
  rcases L with _ | ⟨y, L⟩
  · rfl
  · have hy := h y rfl
    rcases y with _ | _ | _ | _ | _ | _ | _ <;> first | rfl | simp_all [Sym.isBit]

theorem bitD_of_termOK {L : List Sym} (h : TermOK L) (d : Bool) : bitD L.head? d = d := by
  rcases L with _ | ⟨y, L⟩
  · rfl
  · have hy := h y rfl
    rcases y with _ | _ | _ | _ | _ | _ | _ <;> first | rfl | simp_all [Sym.isBit]

/-! ## Atoms -/

variable {K : Type}

/-- Peek `k` into `r`. -/
def peekR (k : K) : AProg K := .peek k fun v o => { v with r := o }

/-- Peek `k` into `q`. -/
def peekQ (k : K) : AProg K := .peek k fun v o => { v with q := o }

/-- Peek `k` into `o`. -/
def peekO (k : K) : AProg K := .peek k fun v o => { v with o := o }

/-- Pop `k` into `o`. -/
def popO (k : K) : AProg K := .pop k fun v o => { v with o := o }

/-- Pop `k`, discarding the symbol. -/
def drop1 (k : K) : AProg K := .pop k fun v _ => v

/-- Push the constant `y` onto `k`. -/
def pushS (k : K) (y : Sym) : AProg K := .push k fun _ => y

/-- Do nothing (1 step). -/
def skipA : AProg K := .load id

/-- Move the marks of `X` onto `R`: loop. -/
def mmLoop (X R : K) : AProg K :=
  .loop (fun v => isMarkO v.r) (.seq (drop1 X) (.seq (pushS R .mark) (peekR X)))

/-- Move the marks of `X` onto `R`. -/
def moveMarks (X R : K) : AProg K := .seq (peekR X) (mmLoop X R)

/-- Pop the marks of `R`: loop. -/
def cmLoop (R : K) : AProg K := .loop (fun v => isMarkO v.r) (.seq (drop1 R) (peekR R))

/-- Pop the marks of `R`. -/
def clearMarks (R : K) : AProg K := .seq (peekR R) (cmLoop R)

/-- Pop the bits of `B`: loop. -/
def dbLoop (B : K) : AProg K := .loop (fun v => isBitO v.q) (.seq (drop1 B) (peekQ B))

/-- Pop the bits of `B`. -/
def drainBits (B : K) : AProg K := .seq (peekQ B) (dbLoop B)

/-- One step of a ruler walk: take a mark from `R` to `X`, run `body`, peek `R`. -/
def walkStep (R X : K) (body : AProg K) : AProg K :=
  .seq (drop1 R) (.seq (pushS X .mark) (.seq body (peekR R)))

/-- Walk the ruler `R` (marks go to `X`), running `body` once per mark: loop. -/
def walkLoop (R X : K) (body : AProg K) : AProg K :=
  .loop (fun v => isMarkO v.r) (walkStep R X body)

/-- Walk the ruler `R` (marks go to `X`), running `body` once per mark. -/
def walk (R X : K) (body : AProg K) : AProg K := .seq (peekR R) (walkLoop R X body)

/-! ## Evaluation lemmas for atoms -/

variable [DecidableEq K]

theorem eval_drop1 (k : K) (v : AReg) (S : K → List Sym) (y : Sym) (L : List Sym)
    (h : S k = y :: L) : Eval [] (drop1 k) ⟨v, S⟩ ⟨v, Function.update S k L⟩ 1 := by
  refine (Eval.pop [] k _ v S).of_eq ?_ rfl
  rw [h]; rfl

theorem eval_popO (k : K) (v : AReg) (S : K → List Sym) (y : Sym) (L : List Sym)
    (h : S k = y :: L) :
    Eval [] (popO k) ⟨v, S⟩ ⟨{ v with o := some y }, Function.update S k L⟩ 1 := by
  refine (Eval.pop [] k _ v S).of_eq ?_ rfl
  rw [h]; rfl

theorem eval_peekR (k : K) (v : AReg) (S : K → List Sym) :
    Eval [] (peekR k) ⟨v, S⟩ ⟨{ v with r := (S k).head? }, S⟩ 1 :=
  Eval.peek [] k _ v S

theorem eval_peekQ (k : K) (v : AReg) (S : K → List Sym) :
    Eval [] (peekQ k) ⟨v, S⟩ ⟨{ v with q := (S k).head? }, S⟩ 1 :=
  Eval.peek [] k _ v S

theorem eval_peekO (k : K) (v : AReg) (S : K → List Sym) :
    Eval [] (peekO k) ⟨v, S⟩ ⟨{ v with o := (S k).head? }, S⟩ 1 :=
  Eval.peek [] k _ v S

theorem eval_pushS (k : K) (y : Sym) (v : AReg) (S : K → List Sym) :
    Eval [] (pushS k y) ⟨v, S⟩ ⟨v, Function.update S k (y :: S k)⟩ 1 :=
  Eval.push [] k _ v S

theorem eval_skipA (v : AReg) (S : K → List Sym) : Eval [] (skipA (K := K)) ⟨v, S⟩ ⟨v, S⟩ 1 :=
  Eval.load [] id v S

theorem replicate_mark_head (n : ℕ) (D : List Sym) :
    (List.replicate (n + 1) Sym.mark ++ D).head? = some .mark := by
  simp [List.replicate_succ]

theorem rep_cons {α : Type} (n : ℕ) (a : α) (L : List α) :
    List.replicate n a ++ a :: L = a :: (List.replicate n a ++ L) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-! ## Generic loops -/

theorem mmLoop_eval {X R : K} (hXR : X ≠ R) :
    ∀ (n : ℕ) (D : List Sym) (v : AReg) (S : K → List Sym), D.head? ≠ some .mark →
      S X = List.replicate n .mark ++ D → v.r = (List.replicate n Sym.mark ++ D).head? →
      Eval [] (mmLoop X R) ⟨v, S⟩
        ⟨{ v with r := D.head? }, Function.update (Function.update S X D) R
          (List.replicate n .mark ++ S R)⟩ (4 * n + 1)
  | 0, D, v, S, hD, hX, hv => by
    simp only [List.replicate_zero, List.nil_append] at hX hv ⊢
    refine (Eval.loop_false (by rw [hv]; exact isMarkO_false_of_ne hD)).of_eq ?_ rfl
    rw [← hv, ← hX, Function.update_eq_self, Function.update_eq_self]
  | n + 1, D, v, S, hD, hX, hv => by
    have hX' : S X = Sym.mark :: (List.replicate n .mark ++ D) := by
      rw [hX, List.replicate_succ, List.cons_append]
    set S1 := Function.update S X (List.replicate n .mark ++ D) with hS1
    set S2 := Function.update S1 R (Sym.mark :: S1 R) with hS2
    have hS2X : S2 X = List.replicate n .mark ++ D := by
      rw [hS2, Function.update_of_ne hXR, hS1, Function.update_self]
    have e1 := eval_drop1 X v S _ _ hX'
    have e2 := eval_pushS R .mark v S1
    have e3 : Eval [] (peekR X) ⟨v, S2⟩
        ⟨{ v with r := (List.replicate n Sym.mark ++ D).head? }, S2⟩ 1 := by
      refine (eval_peekR X v S2).of_eq ?_ rfl
      rw [hS2X]
    have ih := mmLoop_eval hXR n D { v with r := (List.replicate n Sym.mark ++ D).head? } S2 hD
      hS2X rfl
    have hc : isMarkO v.r = true := by rw [hv, replicate_mark_head]; rfl
    refine (Eval.loop_true hc (Eval.seq e1 (Eval.seq e2 e3)) ih).of_eq ?_ (by ring)
    congr 1
    funext k
    simp only [hS2, hS1, Function.update_apply, List.replicate_succ, List.cons_append, rep_cons]
    split_ifs <;> simp_all [rep_cons]

/-- **moveMarks**, exact: the `n` marks of `X` (above `D`, which does not start with `mark`) go
onto `R`. Cost `4n + 2`. -/
theorem moveMarks_eval {X R : K} (hXR : X ≠ R) (n : ℕ) (D : List Sym) (v : AReg)
    (S : K → List Sym) (hD : D.head? ≠ some .mark) (hX : S X = List.replicate n .mark ++ D) :
    Eval [] (moveMarks X R) ⟨v, S⟩
      ⟨{ v with r := D.head? }, Function.update (Function.update S X D) R
        (List.replicate n .mark ++ S R)⟩ (4 * n + 2) := by
  have e1 := eval_peekR X v S
  rw [hX] at e1
  exact (Eval.seq e1 (mmLoop_eval hXR n D _ S hD hX rfl)).of_eq rfl (by ring)

theorem cmLoop_eval {R : K} :
    ∀ (n : ℕ) (D : List Sym) (v : AReg) (S : K → List Sym), D.head? ≠ some .mark →
      S R = List.replicate n .mark ++ D → v.r = (List.replicate n Sym.mark ++ D).head? →
      Eval [] (cmLoop R) ⟨v, S⟩ ⟨{ v with r := D.head? }, Function.update S R D⟩ (3 * n + 1)
  | 0, D, v, S, hD, hR, hv => by
    simp only [List.replicate_zero, List.nil_append] at hR hv ⊢
    refine (Eval.loop_false (by rw [hv]; exact isMarkO_false_of_ne hD)).of_eq ?_ rfl
    rw [← hv, ← hR, Function.update_eq_self]
  | n + 1, D, v, S, hD, hR, hv => by
    have hR' : S R = Sym.mark :: (List.replicate n .mark ++ D) := by
      rw [hR, List.replicate_succ, List.cons_append]
    set S1 := Function.update S R (List.replicate n .mark ++ D) with hS1
    have e1 := eval_drop1 R v S _ _ hR'
    have e2 : Eval [] (peekR R) ⟨v, S1⟩
        ⟨{ v with r := (List.replicate n Sym.mark ++ D).head? }, S1⟩ 1 := by
      refine (eval_peekR R v S1).of_eq ?_ rfl
      rw [hS1, Function.update_self]
    have ih := cmLoop_eval n D { v with r := (List.replicate n Sym.mark ++ D).head? } S1 hD
      (by rw [hS1, Function.update_self]) rfl
    have hc : isMarkO v.r = true := by rw [hv, replicate_mark_head]; rfl
    refine (Eval.loop_true hc (Eval.seq e1 e2) ih).of_eq ?_ (by ring)
    rw [hS1, Function.update_idem]

/-- **clearMarks**, exact: pops the `n` marks of `R`. Cost `3n + 2`. -/
theorem clearMarks_eval {R : K} (n : ℕ) (D : List Sym) (v : AReg) (S : K → List Sym)
    (hD : D.head? ≠ some .mark) (hR : S R = List.replicate n .mark ++ D) :
    Eval [] (clearMarks R) ⟨v, S⟩ ⟨{ v with r := D.head? }, Function.update S R D⟩
      (3 * n + 2) := by
  have e1 := eval_peekR R v S
  rw [hR] at e1
  exact (Eval.seq e1 (cmLoop_eval n D _ S hD hR rfl)).of_eq rfl (by ring)

theorem dbLoop_eval {B : K} :
    ∀ (L : List Bool) (D : List Sym) (v : AReg) (S : K → List Sym), TermOK D →
      S B = L.map Sym.bit ++ D → v.q = (L.map Sym.bit ++ D).head? →
      Eval [] (dbLoop B) ⟨v, S⟩ ⟨{ v with q := D.head? }, Function.update S B D⟩
        (3 * L.length + 1)
  | [], D, v, S, hD, hB, hv => by
    simp only [List.map_nil, List.nil_append] at hB hv ⊢
    refine (Eval.loop_false (by rw [hv]; exact isBitO_false_of_termOK hD)).of_eq ?_ rfl
    rw [← hv, ← hB, Function.update_eq_self]
  | b :: L, D, v, S, hD, hB, hv => by
    have hB' : S B = Sym.bit b :: (L.map Sym.bit ++ D) := by rw [hB]; rfl
    set S1 := Function.update S B (L.map Sym.bit ++ D) with hS1
    have e1 := eval_drop1 B v S _ _ hB'
    have e2 : Eval [] (peekQ B) ⟨v, S1⟩ ⟨{ v with q := (L.map Sym.bit ++ D).head? }, S1⟩ 1 := by
      refine (eval_peekQ B v S1).of_eq ?_ rfl
      rw [hS1, Function.update_self]
    have ih := dbLoop_eval L D { v with q := (L.map Sym.bit ++ D).head? } S1 hD
      (by rw [hS1, Function.update_self]) rfl
    have hc : isBitO v.q = true := by rw [hv]; rfl
    refine (Eval.loop_true hc (Eval.seq e1 e2) ih).of_eq ?_ (by simp only [List.length_cons]; ring)
    rw [hS1, Function.update_idem]

/-- **drainBits**, exact: pops the bits of `B` down to the terminator `D`. Cost `3|L| + 2`. -/
theorem drainBits_eval {B : K} (L : List Bool) (D : List Sym) (v : AReg) (S : K → List Sym)
    (hD : TermOK D) (hB : S B = L.map Sym.bit ++ D) :
    Eval [] (drainBits B) ⟨v, S⟩ ⟨{ v with q := D.head? }, Function.update S B D⟩
      (3 * L.length + 2) := by
  have e1 := eval_peekQ B v S
  rw [hB] at e1
  exact (Eval.seq e1 (dbLoop_eval L D _ S hD hB rfl)).of_eq rfl (by ring)

/-- **One walk step**, given the body's evaluation on the stacks after the mark moved from `R` to
`X`. The body must leave `R` as it found it. -/
theorem walkStep_eval {R X : K} (hRX : R ≠ X) (body : AProg K) (n : ℕ) (D : List Sym) (v : AReg)
    (S : K → List Sym) (hR : S R = List.replicate (n + 1) .mark ++ D) {v2 : AReg}
    {S2 : K → List Sym} {tb : ℕ}
    (hb : Eval [] body ⟨v, Function.update (Function.update S R (List.replicate n .mark ++ D)) X
      (.mark :: S X)⟩ ⟨v2, S2⟩ tb) (hS2R : S2 R = List.replicate n .mark ++ D) :
    Eval [] (walkStep R X body) ⟨v, S⟩
      ⟨{ v2 with r := (List.replicate n Sym.mark ++ D).head? }, S2⟩ (tb + 3) := by
  have hR' : S R = Sym.mark :: (List.replicate n .mark ++ D) := by
    rw [hR, List.replicate_succ, List.cons_append]
  have e1 := eval_drop1 R v S _ _ hR'
  have e2 := eval_pushS X .mark v (Function.update S R (List.replicate n .mark ++ D))
  rw [Function.update_of_ne hRX.symm] at e2
  have e3 : Eval [] (peekR R) ⟨v2, S2⟩
      ⟨{ v2 with r := (List.replicate n Sym.mark ++ D).head? }, S2⟩ 1 := by
    refine (eval_peekR R v2 S2).of_eq ?_ rfl
    rw [hS2R]
  exact (Eval.seq e1 (Eval.seq e2 (Eval.seq hb e3))).of_eq rfl (by ring)

end SubNLogN.Machine.Arith
