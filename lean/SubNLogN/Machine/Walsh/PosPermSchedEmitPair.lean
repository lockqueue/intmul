/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedEmitSt

/-!
# Schedule compiler emitter, part 3 (`Machine/Walsh/PosPermSchedEmitPair.lean`): one position of a scan

`xBody IT stA` is one step of a slice scan at position `x`:
* look up `y = I x`;
* if `x < y`, form the stage pair `(c, t)`: `(y, x)` for stage A, `(x, y)` for stage B;
* test the slice of its target: `j₀ ≤ t < E` (`E` in `q4`) and `(t - j₀) % K = hi`;
* if the test passes, emit `t` then `c` onto the batch buffer and count the pair.

`runs_xBody` is its exact effect on the emitter states `st S₀ v acc bt`.

**Scope (honest summary).** Definitions and proved rules only; no contract is proved here.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh

/-! ## The program -/

/-- The slice test of the target `t`: `e0 = [t < j₀]`, `e1 = [t < E]` (`E` in `q4`),
`q7 = t - j₀`, `(q8, v) = (q7 / K, q7 % K)`, `fnd = [v = hi]`. -/
def sliceTest : SProg Stk :=
  .seq (ltR .t .j0 .e0) (.seq (ltR .t .q4 .e1) (.seq (subR .t .j0 .q7)
    (.seq (dmR .q7 .K .q8 .v) (eqR .v .hi .fnd))))

/-- Emit `t` then `c` onto the batch buffer and count the pair. -/
def emitPairB : SProg Stk :=
  .seq (copyR .t .b) (.seq (emitB .b) (.seq (copyR .c .b) (.seq (emitB .b) (inc .cnt))))

/-- Clear the pair registers. -/
def clrPair : SProg Stk :=
  .seq (clr .c) (.seq (clr .t) (.seq (clr .e0) (.seq (clr .e1) (.seq (clr .q7) (.seq (clr .q8)
    (.seq (clr .v) (clr .fnd)))))))

/-- The test branch: emit iff `¬ t < j₀`, `t < E`, `v = hi`. -/
def pairBranch : SProg Stk := ifR .e0 skip (ifR .e1 (ifR .fnd emitPairB skip) skip)

/-- A candidate pair (`x < y`). -/
def pairBody (stA : Bool) : SProg Stk :=
  .seq (ctSet stA .x) (.seq sliceTest (.seq pairBranch clrPair))

/-- **One position of a slice scan.** -/
def xBody (IT : RawN) (stA : Bool) : SProg Stk :=
  .seq (lookR IT .x .y) (.seq (ltR .x .y .f) (.seq (ifR .f (pairBody stA) skip)
    (.seq (clr .f) (clr .y))))

/-! ## Values and states -/

/-- The control of the stage pair at `(x, y = I x)`. -/
def cvOf (stA : Bool) (X Y : ℕ) : ℕ := if stA then Y else X
/-- The target of the stage pair at `(x, y = I x)`. -/
def tvOf (stA : Bool) (X Y : ℕ) : ℕ := if stA then X else Y
/-- The machine's slice test of a target. -/
def mqOf (j0 E K hi tv : ℕ) : Bool := decide (j0 ≤ tv ∧ tv < E ∧ (tv - j0) % K = hi)

/-- The per-position registers cleared. -/
def pz (v : RegN → ℕ) : RegN → ℕ := fun r =>
  match r with
  | .y | .f | .c | .t | .e0 | .e1 | .q7 | .q8 | .v | .fnd | .b => 0
  | r => v r

/-- A candidate: position `x := X`, `y := Y`, `f := 1`. -/
def pv1 (v : RegN → ℕ) (X Y : ℕ) : RegN → ℕ :=
  Function.update (Function.update (Function.update (pz v) .x X) .y Y) .f 1

/-- The candidate with its pair `c := cv`, `t := tv`. -/
def pv2 (v : RegN → ℕ) (X Y cv tv : ℕ) : RegN → ℕ :=
  Function.update (Function.update (pv1 v X Y) .c cv) .t tv

/-- The candidate after the slice test. -/
def pv3 (v : RegN → ℕ) (X Y cv tv : ℕ) : RegN → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (pv2 v X Y cv tv) .e0 (if tv < v .j0 then 1 else 0))
    .e1 (if tv < v .q4 then 1 else 0)) .q7 (tv - v .j0)) .q8 ((tv - v .j0) / v .K))
    .v ((tv - v .j0) % v .K)) .fnd (if (tv - v .j0) % v .K = v .hi then 1 else 0)

theorem finVals_length {m : ℕ} (I : Fin m → Fin m) : (finVals I).length = m := by
  simp [finVals]

theorem finVals_getElem {m : ℕ} (I : Fin m → Fin m) (X : Fin m)
    (h : (X : ℕ) < (finVals I).length) : (finVals I)[(X : ℕ)] = (I X : ℕ) := by
  simp [finVals]

/-! ## Rules of the blocks -/

section Blocks

variable (S₀ : Stk → List Sym) (acc bt : List Sym) {V : ℕ}

theorem runs_ctSet (stA : Bool) (v : RegN → ℕ) (X Y : ℕ) (hX : X ≤ V) (hY : Y ≤ V) :
    Runs (ctSet stA .x) (st S₀ (pv1 v X Y) acc bt)
      (st S₀ (pv2 v X Y (cvOf stA X Y) (tvOf stA X Y)) acc bt) (fun _ => True) (2 * opW V) := by
  cases stA with
  | true =>
    exact runs_weak (runs_seq' (runs_copyR0 S₀ _ acc bt .y .c hY rfl)
      (runs_copyR0 S₀ _ acc bt .x .t hX rfl) le_rfl) rfl (by omega)
  | false =>
    exact runs_weak (runs_seq' (runs_copyR0 S₀ _ acc bt .x .c hX rfl)
      (runs_copyR0 S₀ _ acc bt .y .t hY rfl) le_rfl) rfl (by omega)

theorem runs_sliceTest (v : RegN → ℕ) (X Y cv tv : ℕ) (htv : tv ≤ V) (hj0 : v .j0 ≤ V)
    (hE : v .q4 ≤ V) (hK : v .K ≤ V) (hK0 : 0 < v .K) (hhi : v .hi ≤ V) :
    Runs sliceTest (st S₀ (pv2 v X Y cv tv) acc bt) (st S₀ (pv3 v X Y cv tv) acc bt)
      (fun _ => True) (5 * opW V) := by
  have hu : tv - v .j0 ≤ V := by omega
  have hr : (tv - v .j0) % v .K ≤ V := le_trans (Nat.mod_le _ _) hu
  exact runs_weak (runs_seq' (runs_ltR0 S₀ _ acc bt .t .j0 .e0 htv hj0 rfl)
    (runs_seq' (runs_ltR0 S₀ _ acc bt .t .q4 .e1 htv hE rfl)
    (runs_seq' (runs_subR0 S₀ _ acc bt .t .j0 .q7 htv hj0 rfl)
    (runs_seq' (runs_dmR0 S₀ _ acc bt .q7 .K .q8 .v hu hK hK0 rfl rfl)
      (runs_eqR0 S₀ _ acc bt .v .hi .fnd hr hhi rfl) le_rfl) le_rfl) le_rfl) le_rfl) rfl
    (by omega)

theorem runs_emitPairB (hB1 : S₀ (rs .B1) = []) (v : RegN → ℕ) (X Y cv tv : ℕ) (hcv : cv ≤ V)
    (htv : tv ≤ V) :
    Runs emitPairB (st S₀ (pv3 v X Y cv tv) acc bt)
      (st S₀ (pv3 (Function.update v .cnt (v .cnt + 1)) X Y cv tv) acc
        (natSyms cv ++ Sym.mark :: (natSyms tv ++ Sym.mark :: bt)))
      (fun _ => True) (5 * opW V) := by
  refine runs_weak (runs_seq' (runs_copyR0 S₀ _ acc bt .t .b htv rfl)
    (runs_seq' (runs_emitB S₀ _ acc bt .b hB1 htv)
    (runs_seq' (runs_copyR0 S₀ _ acc _ .c .b hcv rfl)
    (runs_seq' (runs_emitB S₀ _ acc _ .b hB1 hcv)
      (runs_inc (V := V) S₀ _ acc _ .cnt) le_rfl) le_rfl) le_rfl) le_rfl)
    (st_congr (fun r => by cases r <;> rfl)) (by omega)

theorem runs_clrPair (v : RegN → ℕ) (X Y cv tv : ℕ) (hV1 : 1 ≤ V) (hcv : cv ≤ V)
    (htv : tv ≤ V) :
    Runs clrPair (st S₀ (pv3 v X Y cv tv) acc bt) (st S₀ (pv1 v X Y) acc bt) (fun _ => True)
      (8 * opW V) := by
  have h0 : (if tv < v .j0 then 1 else 0) ≤ V := by split <;> omega
  have h1 : (if tv < v .q4 then 1 else 0) ≤ V := by split <;> omega
  have h2 : tv - v .j0 ≤ V := by omega
  have h3 : (tv - v .j0) / v .K ≤ V := le_trans (Nat.div_le_self _ _) h2
  have h4 : (tv - v .j0) % v .K ≤ V := le_trans (Nat.mod_le _ _) h2
  have h5 : (if (tv - v .j0) % v .K = v .hi then 1 else 0) ≤ V := by split <;> omega
  refine runs_weak (runs_seq' (runs_clr S₀ _ acc bt .c hcv) (runs_seq' (runs_clr S₀ _ acc bt .t htv)
    (runs_seq' (runs_clr S₀ _ acc bt .e0 h0) (runs_seq' (runs_clr S₀ _ acc bt .e1 h1)
    (runs_seq' (runs_clr S₀ _ acc bt .q7 h2) (runs_seq' (runs_clr S₀ _ acc bt .q8 h3)
    (runs_seq' (runs_clr S₀ _ acc bt .v h4) (runs_clr S₀ _ acc bt .fnd h5) le_rfl) le_rfl) le_rfl)
    le_rfl) le_rfl) le_rfl) le_rfl) (st_congr (fun r => by cases r <;> rfl)) (by omega)

theorem runs_pairBranch (hB1 : S₀ (rs .B1) = []) (v : RegN → ℕ) (X Y cv tv : ℕ) (hcv : cv ≤ V)
    (htv : tv ≤ V) :
    Runs pairBranch (st S₀ (pv3 v X Y cv tv) acc bt)
      (if mqOf (v .j0) (v .q4) (v .K) (v .hi) tv = true then
        st S₀ (pv3 (Function.update v .cnt (v .cnt + 1)) X Y cv tv) acc
          (natSyms cv ++ Sym.mark :: (natSyms tv ++ Sym.mark :: bt))
      else st S₀ (pv3 v X Y cv tv) acc bt)
      (fun _ => True) (12 * opW V) := by
  by_cases h0 : tv < v .j0
  · have hq : mqOf (v .j0) (v .q4) (v .K) (v .hi) tv = false := by
      unfold mqOf
      simp only [decide_eq_false_iff_not]
      rintro ⟨ha, -, -⟩
      omega
    rw [hq, if_neg (by decide)]
    exact runs_weak (runs_ifR_pos S₀ _ acc bt
      (by show (if tv < v .j0 then 1 else 0) ≠ 0; simp [h0])
      (runs_skip_st (V := V) S₀ _ acc bt)) rfl (by have := one_le_opW V; omega)
  · by_cases h1 : tv < v .q4
    · by_cases h2 : (tv - v .j0) % v .K = v .hi
      · have hq : mqOf (v .j0) (v .q4) (v .K) (v .hi) tv = true := by
          unfold mqOf
          simp only [decide_eq_true_eq]
          exact ⟨by omega, h1, h2⟩
        rw [hq, if_pos rfl]
        exact runs_weak (runs_ifR_neg S₀ _ acc bt
          (by show (if tv < v .j0 then 1 else 0) = 0; simp [h0])
          (runs_ifR_pos S₀ _ acc bt (by show (if tv < v .q4 then 1 else 0) ≠ 0; simp [h1])
          (runs_ifR_pos S₀ _ acc bt
            (by show (if (tv - v .j0) % v .K = v .hi then 1 else 0) ≠ 0; simp [h2])
            (runs_emitPairB S₀ acc bt hB1 v X Y cv tv hcv htv)))) rfl (by have := one_le_opW V; omega)
      · have hq : mqOf (v .j0) (v .q4) (v .K) (v .hi) tv = false := by
          unfold mqOf
          simp only [decide_eq_false_iff_not]
          rintro ⟨-, -, hc⟩
          exact h2 hc
        rw [hq, if_neg (by decide)]
        exact runs_weak (runs_ifR_neg S₀ _ acc bt
          (by show (if tv < v .j0 then 1 else 0) = 0; simp [h0])
          (runs_ifR_pos S₀ _ acc bt (by show (if tv < v .q4 then 1 else 0) ≠ 0; simp [h1])
          (runs_ifR_neg S₀ _ acc bt
            (by show (if (tv - v .j0) % v .K = v .hi then 1 else 0) = 0; simp [h2])
            (runs_skip_st (V := V) S₀ _ acc bt)))) rfl (by have := one_le_opW V; omega)
    · have hq : mqOf (v .j0) (v .q4) (v .K) (v .hi) tv = false := by
        unfold mqOf
        simp only [decide_eq_false_iff_not]
        rintro ⟨-, hb, -⟩
        exact h1 hb
      rw [hq, if_neg (by decide)]
      exact runs_weak (runs_ifR_neg S₀ _ acc bt
        (by show (if tv < v .j0 then 1 else 0) = 0; simp [h0])
        (runs_ifR_neg S₀ _ acc bt (by show (if tv < v .q4 then 1 else 0) = 0; simp [h1])
          (runs_skip_st (V := V) S₀ _ acc bt))) rfl (by have := one_le_opW V; omega)

theorem runs_pairBody (hB1 : S₀ (rs .B1) = []) (stA : Bool) (v : RegN → ℕ) (X Y : ℕ)
    (hV1 : 1 ≤ V) (hX : X ≤ V) (hY : Y ≤ V) (hj0 : v .j0 ≤ V) (hE : v .q4 ≤ V) (hK : v .K ≤ V)
    (hK0 : 0 < v .K) (hhi : v .hi ≤ V) :
    Runs (pairBody stA) (st S₀ (pv1 v X Y) acc bt)
      (if mqOf (v .j0) (v .q4) (v .K) (v .hi) (tvOf stA X Y) = true then
        st S₀ (pv1 (Function.update v .cnt (v .cnt + 1)) X Y) acc
          (natSyms (cvOf stA X Y) ++ Sym.mark :: (natSyms (tvOf stA X Y) ++ Sym.mark :: bt))
      else st S₀ (pv1 v X Y) acc bt)
      (fun _ => True) (30 * opW V) := by
  have hcv : cvOf stA X Y ≤ V := by unfold cvOf; split <;> omega
  have htv : tvOf stA X Y ≤ V := by unfold tvOf; split <;> omega
  have h1 := runs_ctSet S₀ acc bt stA v X Y hX hY
  have h2 := runs_sliceTest S₀ acc bt v X Y (cvOf stA X Y) (tvOf stA X Y) htv hj0 hE hK hK0 hhi
  have h3 := runs_pairBranch S₀ acc bt hB1 v X Y (cvOf stA X Y) (tvOf stA X Y) hcv htv
  by_cases hq : mqOf (v .j0) (v .q4) (v .K) (v .hi) (tvOf stA X Y) = true
  · rw [if_pos hq] at h3 ⊢
    have h4 := runs_clrPair S₀ acc
      (natSyms (cvOf stA X Y) ++ Sym.mark :: (natSyms (tvOf stA X Y) ++ Sym.mark :: bt))
      (Function.update v .cnt (v .cnt + 1)) X Y (cvOf stA X Y) (tvOf stA X Y) hV1 hcv htv
    exact runs_weak (runs_seq' h1 (runs_seq' h2 (runs_seq' h3 h4 le_rfl) le_rfl) le_rfl) rfl
      (by omega)
  · rw [if_neg hq] at h3 ⊢
    have h4 := runs_clrPair S₀ acc bt v X Y (cvOf stA X Y) (tvOf stA X Y) hV1 hcv htv
    exact runs_weak (runs_seq' h1 (runs_seq' h2 (runs_seq' h3 h4 le_rfl) le_rfl) le_rfl) rfl
      (by omega)

end Blocks

/-! ## One position -/

/-- A position `x := X`, the per-position registers cleared. -/
def pv0 (v : RegN → ℕ) (X : ℕ) : RegN → ℕ := Function.update (pz v) .x X

/-- The pair of position `X` kept by the machine's slice test. -/
def xOpt {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (j0 E K hi : ℕ) (X : Fin m) :
    Option (Fin m × Fin m) :=
  (pairOf stA I X).filter (fun p => mqOf j0 E K hi (p.2 : ℕ))

theorem pairOf_lt {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (X : Fin m)
    (h : (X : ℕ) < (I X : ℕ)) : pairOf stA I X = some (if stA then (I X, X) else (X, I X)) := by
  unfold pairOf
  rw [if_pos (Fin.lt_def.mpr h)]

theorem pairOf_nlt {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (X : Fin m)
    (h : ¬ (X : ℕ) < (I X : ℕ)) : pairOf stA I X = none := by
  unfold pairOf
  rw [if_neg (fun h' => h (Fin.lt_def.mp h'))]

theorem pair_fst (stA : Bool) {m : ℕ} (I : Fin m → Fin m) (X : Fin m) :
    (((if stA then (I X, X) else (X, I X)).1 : Fin m) : ℕ) = cvOf stA X (I X) := by
  cases stA <;> rfl

theorem pair_snd (stA : Bool) {m : ℕ} (I : Fin m → Fin m) (X : Fin m) :
    (((if stA then (I X, X) else (X, I X)).2 : Fin m) : ℕ) = tvOf stA X (I X) := by
  cases stA <;> rfl

theorem xOpt_toList_pos {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (j0 E K hi : ℕ) (X : Fin m)
    (hlt : (X : ℕ) < (I X : ℕ)) (hq : mqOf j0 E K hi (tvOf stA X (I X)) = true) :
    (xOpt stA I j0 E K hi X).toList = [if stA then (I X, X) else (X, I X)] := by
  unfold xOpt
  rw [pairOf_lt stA I X hlt]
  cases stA <;> simp_all [tvOf]

theorem xOpt_toList_negq {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (j0 E K hi : ℕ) (X : Fin m)
    (hlt : (X : ℕ) < (I X : ℕ)) (hq : ¬ mqOf j0 E K hi (tvOf stA X (I X)) = true) :
    (xOpt stA I j0 E K hi X).toList = [] := by
  unfold xOpt
  rw [pairOf_lt stA I X hlt]
  cases stA <;> simp_all [tvOf]

theorem xOpt_toList_neglt {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (j0 E K hi : ℕ) (X : Fin m)
    (hlt : ¬ (X : ℕ) < (I X : ℕ)) : (xOpt stA I j0 E K hi X).toList = [] := by
  unfold xOpt
  rw [pairOf_nlt stA I X hlt]
  rfl

theorem hdrSyms_pair_append {m : ℕ} (p : Fin m × Fin m) (bt : List Sym) :
    hdrSyms (pairFields [p]) ++ bt =
      natSyms (p.1 : ℕ) ++ Sym.mark :: (natSyms (p.2 : ℕ) ++ Sym.mark :: bt) := by
  rw [hdrSyms_pairFields_cons, pairFields_nil, PSIO.hdrSyms_nil]
  simp

/-- **One position of a slice scan**: the batch buffer gains the header fields `[c, t]` of the pair
of position `X` if it passes the slice test, and the count grows accordingly. -/
theorem runs_xBody (S₀ : Stk → List Sym) (acc bt : List Sym) {V : ℕ} (IT : RawN)
    (hIT : IT = .I0T ∨ IT = .I1T) {m : ℕ} (I : Fin m → Fin m)
    (hT : S₀ (rs IT) = utab (finVals I)) (hU : S₀ (rs .U) = []) (hB1 : S₀ (rs .B1) = [])
    (stA : Bool) (v : RegN → ℕ) (X : Fin m) (hV1 : 1 ≤ V) (hm : m ≤ V)
    (hL : (utab (finVals I)).length ≤ V) (hj0 : v .j0 ≤ V) (hE : v .q4 ≤ V) (hK : v .K ≤ V)
    (hK0 : 0 < v .K) (hhi : v .hi ≤ V) :
    Runs (xBody IT stA) (st S₀ (pv0 v X) acc bt)
      (st S₀ (pv0 (Function.update v .cnt
          (v .cnt + (xOpt stA I (v .j0) (v .q4) (v .K) (v .hi) X).toList.length)) X) acc
        (hdrSyms (pairFields (xOpt stA I (v .j0) (v .q4) (v .K) (v .hi) X).toList) ++ bt))
      (fun _ => True) (40 * opW V) := by
  have hX : (X : ℕ) ≤ V := by have := X.isLt; omega
  have hIX : (I X : ℕ) ≤ V := by have := (I X).isLt; omega
  have hj : (X : ℕ) < (finVals I).length := by rw [finVals_length]; exact X.isLt
  have s1 : Runs (lookR IT .x .y) (st S₀ (pv0 v X) acc bt)
      (st S₀ (Function.update (pv0 v X) .y (I X : ℕ)) acc bt) (fun _ => True) (opW V) := by
    have h : Runs (lookR IT .x .y) (st S₀ (pv0 v X) acc bt)
        (st S₀ (Function.update (pv0 v X) .y ((finVals I)[(X : ℕ)]'hj)) acc bt)
        (fun _ => True) (opW V) :=
      runs_lookR0 S₀ (pv0 v X) acc bt IT hIT .x .y (finVals I) hT hU hj hX hL rfl
    rw [finVals_getElem I X hj] at h
    exact h
  have s2 : Runs (ltR .x .y .f) (st S₀ (Function.update (pv0 v X) .y (I X : ℕ)) acc bt)
      (st S₀ (Function.update (Function.update (pv0 v X) .y (I X : ℕ)) .f
        (if (X : ℕ) < (I X : ℕ) then 1 else 0)) acc bt) (fun _ => True) (opW V) :=
    runs_ltR0 S₀ _ acc bt .x .y .f hX hIX rfl
  by_cases hlt : (X : ℕ) < (I X : ℕ)
  · rw [if_pos hlt] at s2
    have s3 := runs_pairBody S₀ acc bt hB1 stA v (X : ℕ) (I X : ℕ) hV1 hX hIX hj0 hE hK hK0 hhi
    by_cases hq : mqOf (v .j0) (v .q4) (v .K) (v .hi) (tvOf stA (X : ℕ) (I X : ℕ)) = true
    · rw [if_pos hq] at s3
      refine runs_weak (runs_seq' s1 (runs_seq' s2 (runs_seq'
        (runs_ifR_pos S₀ _ acc bt (by show (1 : ℕ) ≠ 0; omega) s3)
        (runs_seq' (runs_clr S₀ _ acc _ .f hV1) (runs_clr S₀ _ acc _ .y hIX) le_rfl) le_rfl)
        le_rfl) le_rfl) ?_ (by have := one_le_opW V; omega)
      rw [xOpt_toList_pos stA I (v .j0) (v .q4) (v .K) (v .hi) X hlt hq, hdrSyms_pair_append,
        pair_fst, pair_snd]
      exact st_congr (fun r => by cases r <;> rfl)
    · rw [if_neg hq] at s3
      refine runs_weak (runs_seq' s1 (runs_seq' s2 (runs_seq'
        (runs_ifR_pos S₀ _ acc bt (by show (1 : ℕ) ≠ 0; omega) s3)
        (runs_seq' (runs_clr S₀ _ acc _ .f hV1) (runs_clr S₀ _ acc _ .y hIX) le_rfl) le_rfl)
        le_rfl) le_rfl) ?_ (by have := one_le_opW V; omega)
      rw [xOpt_toList_negq stA I (v .j0) (v .q4) (v .K) (v .hi) X hlt hq]
      exact st_congr (fun r => by cases r <;> rfl)
  · rw [if_neg hlt] at s2
    refine runs_weak (runs_seq' s1 (runs_seq' s2 (runs_seq'
      (runs_ifR_neg S₀ _ acc bt (by show (0 : ℕ) = 0; rfl)
        (runs_skip_st (V := V) S₀ _ acc bt))
      (runs_seq' (runs_clr S₀ _ acc _ .f (Nat.zero_le V)) (runs_clr S₀ _ acc _ .y hIX) le_rfl)
      le_rfl) le_rfl) le_rfl) ?_ (by have := one_le_opW V; omega)
    rw [xOpt_toList_neglt stA I (v .j0) (v .q4) (v .K) (v .hi) X hlt]
    exact st_congr (fun r => by cases r <;> rfl)

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit
