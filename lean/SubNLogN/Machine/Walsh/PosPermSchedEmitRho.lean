/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedEmitLoopDefs

/-!
# Schedule compiler emitter, part 4 (`Machine/Walsh/PosPermSchedEmitRho.lean`): one slice

`rhoBody_of : EmitBatchStmt → RhoBodyStmt` handles one slice `(g, ρ)` of the emitter:
* the positions are scanned in decreasing order (`runs_xLoop`, via `sufPairs`);
* the batch buffer then holds `hdrSyms (pairFields ps)` and `cnt = |ps|`, where
  `ps = batchPairs K d g ρ stagePairs` (`batch_eq_suf`, via `xOpt_eq_slice`);
* the batch command is emitted iff `ps ≠ []` (`sliceCmds_eq`, `batch_acc`).

**Scope (honest summary).** Proved; the batch emission enters as the hypothesis `EmitBatchStmt`,
which is proved separately as `emitBatch_holds` (`PosPermSchedEmitBlk.lean`).
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Math.Walsh.PosPermAux

/-! ## List facts -/

theorem pairFields_append {m : ℕ} (l₁ l₂ : List (Fin m × Fin m)) :
    pairFields (l₁ ++ l₂) = pairFields l₁ ++ pairFields l₂ := by
  simp [pairFields, List.flatMap_append]

theorem sufPairs_len_succ {m : ℕ} (Q : Fin m → Option (Fin m × Fin m)) {i : ℕ} (hi : i < m) :
    (sufPairs Q (i + 1)).length =
      (sufPairs Q i).length + (Q ⟨m - 1 - i, by omega⟩).toList.length := by
  rw [sufPairs_succ Q hi, List.length_append, Nat.add_comm]

theorem hdrSyms_suf_succ {m : ℕ} (Q : Fin m → Option (Fin m × Fin m)) {i : ℕ} (hi : i < m) :
    hdrSyms (pairFields (sufPairs Q (i + 1))) =
      hdrSyms (pairFields (Q ⟨m - 1 - i, by omega⟩).toList) ++
        hdrSyms (pairFields (sufPairs Q i)) := by
  rw [sufPairs_succ Q hi, pairFields_append, PSIO.hdrSyms_append]

theorem xOpt_eq_slice {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (K d g ρ : ℕ) (X : Fin m) :
    xOpt stA I (groupStart K d g) (groupStart K d g + groupSize m K d g * K) K (K - ρ - 1) X =
      (pairOf stA I X).filter (sliceQ K d g ρ) := by
  unfold xOpt
  congr 1
  funext p
  simp only [mqOf, sliceQ, mem_slicePos, decide_eq_decide]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by omega⟩

theorem batch_eq_suf {m : ℕ} (stA : Bool) (I : Fin m → Fin m) (K d g ρ : ℕ) (hρ : ρ < K) :
    batchPairs K d g ⟨ρ, hρ⟩ (stPairs stA I) =
      sufPairs (xOpt stA I (groupStart K d g) (groupStart K d g + groupSize m K d g * K) K
        (K - ρ - 1)) m := by
  rw [sufPairs_full]
  unfold stPairs
  rw [batchPairs_stage]
  congr 1
  funext X
  exact (xOpt_eq_slice stA I K d g ρ X).symm

theorem length_hdrSyms_pairFields_le {m : ℕ} (ps : List (Fin m × Fin m)) :
    (hdrSyms (pairFields ps)).length ≤ ps.length * (2 * m + 2) := by
  induction ps with
  | nil => simp [pairFields_nil, PSIO.hdrSyms_nil]
  | cons p ps ih =>
    rw [hdrSyms_pairFields_cons]
    have h1 := PSIO.natSyms_length_le (p.1 : ℕ)
    have h2 := PSIO.natSyms_length_le (p.2 : ℕ)
    have h3 := p.1.isLt
    have h4 := p.2.isLt
    simp only [List.length_append, List.length_cons]
    rw [Nat.succ_mul]
    omega

theorem sufPairs_length_le {m : ℕ} (Q : Fin m → Option (Fin m × Fin m)) (i : ℕ) :
    (sufPairs Q i).length ≤ m := by
  unfold sufPairs
  refine le_trans (List.length_filterMap_le _ _) ?_
  simp only [List.length_drop, List.length_finRange]
  omega

/-! ## The scan of one slice -/

/-- **The slice scan**: the decreasing loop over the positions collects the batch. -/
theorem runs_xLoop (S₀ : Stk → List Sym) (acc : List Sym) {V : ℕ} (IT : RawN)
    (hIT : IT = .I0T ∨ IT = .I1T) {m : ℕ} (I : Fin m → Fin m)
    (hT : S₀ (rs IT) = utab (finVals I)) (hU : S₀ (rs .U) = []) (hB1 : S₀ (rs .B1) = [])
    (stA : Bool) (u : RegN → ℕ) (hV1 : 1 ≤ V) (hm : m ≤ V)
    (hL : (utab (finVals I)).length ≤ V) (hj0 : u .j0 ≤ V) (hE : u .q4 ≤ V) (hK : u .K ≤ V)
    (hK0 : 0 < u .K) (hhi : u .hi ≤ V) :
    Runs (loopR .x (xBody IT stA))
      (st S₀ (Function.update (pz (Function.update u .cnt 0)) .x m) acc [])
      (st S₀ (Function.update (pz (Function.update u .cnt
          (sufPairs (xOpt stA I (u .j0) (u .q4) (u .K) (u .hi)) m).length)) .x 0) acc
        (hdrSyms (pairFields (sufPairs (xOpt stA I (u .j0) (u .q4) (u .K) (u .hi)) m))))
      (fun _ => True) (m * (40 * opW V + 3) + 2) := by
  have hL' := runs_loopR S₀ .x rfl
    (fun i => pz (Function.update u .cnt
      (sufPairs (xOpt stA I (u .j0) (u .q4) (u .K) (u .hi)) i).length))
    (fun _ => acc)
    (fun i => hdrSyms (pairFields (sufPairs (xOpt stA I (u .j0) (u .q4) (u .K) (u .hi)) i)))
    (40 * opW V) m
    (fun i hi => by
      have h := runs_xBody S₀ acc
        (hdrSyms (pairFields (sufPairs (xOpt stA I (u .j0) (u .q4) (u .K) (u .hi)) i))) IT hIT I
        hT hU hB1 stA
        (Function.update u .cnt (sufPairs (xOpt stA I (u .j0) (u .q4) (u .K) (u .hi)) i).length)
        ⟨m - 1 - i, by omega⟩ hV1 hm hL hj0 hE hK hK0 hhi
      refine runs_weak h ?_ le_rfl
      show _ = st S₀ (Function.update (pz (Function.update u .cnt
          (sufPairs (xOpt stA I (u .j0) (u .q4) (u .K) (u .hi)) (i + 1)).length)) .x (m - 1 - i))
        acc (hdrSyms (pairFields (sufPairs (xOpt stA I (u .j0) (u .q4) (u .K) (u .hi)) (i + 1))))
      rw [sufPairs_len_succ _ hi, hdrSyms_suf_succ _ hi]
      exact st_congr (fun r => by cases r <;> rfl))
  simp only [sufPairs_zero, List.length_nil, pairFields_nil, PSIO.hdrSyms_nil] at hL'
  exact hL'

/-! ## One slice -/

theorem rhoBody_of (hEB : EmitBatchStmt) : RhoBodyStmt := by
  intro S₀ IT hIT m d K g I stA w acc V ρ hρ hT hU hB1 hm hK hj0 hD hE hnS hV1 hmV hKV hL hj0V
    hEV hDV hnSV hBT
  subst hm
  subst hK
  have hK0 : 0 < w .K := by omega
  have hhiV : w .K - ρ - 1 ≤ V := by omega
  have hρV : ρ ≤ V := by omega
  have hρ1V : ρ + 1 ≤ V + 1 := by omega
  -- the batch of the slice
  have hb := batch_eq_suf stA I (w .K) d g ρ hρ
  rw [← hE, ← hj0] at hb
  have sx := runs_xLoop S₀ acc IT hIT I hT hU hB1 stA
    (Function.update (Function.update (rz w) .rho ρ) .hi (w .K - ρ - 1)) hV1 hmV hL hj0V hEV hKV
    hK0 hhiV
  have sx' : Runs (loopR .x (xBody IT stA))
      (st S₀ (Function.update (pz (Function.update (Function.update (Function.update (rz w) .rho ρ)
        .hi (w .K - ρ - 1)) .cnt 0)) .x (w .m)) acc [])
      (st S₀ (Function.update (pz (Function.update (Function.update (Function.update (rz w) .rho ρ)
        .hi (w .K - ρ - 1)) .cnt (batchPairs (w .K) d g ⟨ρ, hρ⟩ (stPairs stA I)).length)) .x 0) acc
        (hdrSyms (pairFields (batchPairs (w .K) d g ⟨ρ, hρ⟩ (stPairs stA I)))))
      (fun _ => True) (w .m * (40 * opW V + 3) + 2) := by
    rw [hb]
    exact sx
  have hpsm : (batchPairs (w .K) d g ⟨ρ, hρ⟩ (stPairs stA I)).length ≤ w .m := by
    rw [hb]
    exact sufPairs_length_le _ _
  have e1 : w .m * (40 * opW V + 3) = 40 * (w .m * opW V) + 3 * w .m := by ring
  have e2 : (w .m + 2) * (50 * opW V) = 50 * (w .m * opW V) + 100 * opW V := by ring
  have e3 : w .m ≤ w .m * opW V := Nat.le_mul_of_pos_right _ (one_le_opW V)
  have e4 := one_le_opW V
  by_cases hps : batchPairs (w .K) d g ⟨ρ, hρ⟩ (stPairs stA I) = []
  · -- empty batch: nothing is emitted
    have hC : (batchPairs (w .K) d g ⟨ρ, hρ⟩ (stPairs stA I)).length = 0 := by rw [hps]; rfl
    rw [hps] at sx'
    refine runs_weak (runs_seq' (runs_subR0 S₀ _ acc [] .K .rho .hi hKV hρV rfl)
      (runs_seq' (runs_dec (V := V) S₀ _ acc [] .hi)
      (runs_seq' (runs_weak (runs_copyR0 S₀ _ acc [] .m .x hmV rfl)
        (st_congr (fun r => by cases r <;> rfl)) le_rfl)
      (runs_seq' sx'
      (runs_seq' (runs_ifR_neg S₀ _ acc [] (by rfl) (runs_skip_st (V := V) S₀ _ acc []))
      (runs_seq' (runs_clr S₀ _ acc [] .hi hhiV) (runs_inc (V := V) S₀ _ acc [] .rho) le_rfl)
      le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) ?_ (by omega)
    rw [sliceCmds_eq, if_pos hps]
    exact st_congr (fun r => by cases r <;> rfl)
  · -- nonempty batch: emitted
    have hC : (batchPairs (w .K) d g ⟨ρ, hρ⟩ (stPairs stA I)).length ≠ 0 := by
      intro h
      exact hps (List.eq_nil_of_length_eq_zero h)
    have hBTV : (hdrSyms (pairFields (batchPairs (w .K) d g ⟨ρ, hρ⟩ (stPairs stA I)))).length ≤
        V := by
      refine le_trans (length_hdrSyms_pairFields_le _) (le_trans ?_ hBT)
      exact Nat.mul_le_mul_right _ (by omega)
    have se := hEB S₀ (Function.update (pz (Function.update (Function.update (Function.update
      (rz w) .rho ρ) .hi (w .K - ρ - 1)) .cnt (batchPairs (w .K) d g ⟨ρ, hρ⟩ (stPairs stA I)).length))
      .x 0) acc (hdrSyms (pairFields (batchPairs (w .K) d g ⟨ρ, hρ⟩ (stPairs stA I)))) V hU hB1 rfl
      hV1 hρV hnSV hDV hj0V
      (by show (batchPairs (w .K) d g ⟨ρ, hρ⟩ (stPairs stA I)).length ≤ V; omega) hBTV
    refine runs_weak (runs_seq' (runs_subR0 S₀ _ acc [] .K .rho .hi hKV hρV rfl)
      (runs_seq' (runs_dec (V := V) S₀ _ acc [] .hi)
      (runs_seq' (runs_weak (runs_copyR0 S₀ _ acc [] .m .x hmV rfl)
        (st_congr (fun r => by cases r <;> rfl)) le_rfl)
      (runs_seq' sx'
      (runs_seq' (runs_ifR_pos S₀ _ acc _ hC se)
      (runs_seq' (runs_clr S₀ _ _ [] .hi hhiV) (runs_inc (V := V) S₀ _ _ [] .rho) le_rfl)
      le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) ?_ (by omega)
    have hacc : (schedSyms (sliceCmds (w .m) d (w .K) g ⟨ρ, hρ⟩ (stPairs stA I))).reverse ++ acc =
        Sym.sep2 :: (natSyms (batchPairs (w .K) d g ⟨ρ, hρ⟩ (stPairs stA I)).length ++
          Sym.mark :: (hdrSyms (pairFields (batchPairs (w .K) d g ⟨ρ, hρ⟩ (stPairs stA I))) ++
            Sym.sep2 :: (natSyms (w .j0) ++ Sym.mark :: (natSyms (w .D) ++ Sym.mark ::
              (natSyms (w .nS) ++ Sym.mark :: (natSyms ρ ++ Sym.mark :: Sym.tag 0 :: acc)))))) := by
      rw [sliceCmds_eq, if_neg hps]
      simp only [schedSyms, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [batch_acc, ← hnS, ← hD, ← hj0]
    rw [hacc]
    exact st_congr (fun r => by cases r <;> rfl)

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit
