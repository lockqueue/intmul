/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7Repair

/-!
# Lemma A.9 repair: glue facts for the repair skeleton (`Machine/AppC/C7RepairGlue.lean`)

Small facts used by the composition of the repair phase from its kernels (extraction, radix sort,
reinsertion), all pure:
* (G1) `holeCount_holes`: the skeleton has as many holes as the bank has records;
* (G2) `holes_rec_len`, (G3) `bank_rec_len`: record lengths in the skeleton and the bank;
* (G4) `one_le_keyWidth`, `lt_two_pow_keyWidth`, `keyWidth_le_lgVol`: the key width
  `c7KeyWidth M = Nat.size M`;
* (G5) `repair_sort_reinsert_cost`: the radix sort plus reinsertion cost is at most
  `64 · (V + M (L+1)^3 + badMax · L (R + L + 2))` with `L = lgVol V`, for `V ≥ M (R + 1)`. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine.AppC.C7RepairAux.Math

open SubNLogN.Machine.AppC.C7RadixAux

/-- (G1) The skeleton has one hole per bank record. -/
theorem holeCount_holes (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (A : ℕ)
    (v : List (List Bool)) :
    holeCount (holes K ρ f N1 N2 N3 σ v) = (bank K ρ f N1 N2 N3 σ A v).length := by
  rw [bank_length]
  unfold holeCount holes
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro p _
  simp only [Function.comp_apply]
  cases badB K ρ f N1 N2 N3 σ p <;> rfl

/-- (G2) Kept records of the skeleton have the record length. -/
theorem holes_rec_len {R : ℕ} (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3))
    (v : List (List Bool)) (hv : ∀ p ∈ v, p.length = R) :
    ∀ p, some p ∈ holes K ρ f N1 N2 N3 σ v → p.length = R := by
  intro p hp
  unfold holes at hp
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hp
  rw [List.mem_range] at hq
  by_cases hb : badB K ρ f N1 N2 N3 σ q = true
  · rw [if_pos hb] at hqe
    exact absurd hqe (by simp)
  · rw [if_neg hb, Option.some.injEq] at hqe
    rw [← hqe, List.getD_eq_getElem _ _ hq]
    exact hv _ (List.getElem_mem hq)

/-- (G3) Bank records have `A` key bits and the record length. -/
theorem bank_rec_len {R : ℕ} (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (A : ℕ)
    (v : List (List Bool)) (hv : ∀ p ∈ v, p.length = R) :
    ∀ r ∈ bank K ρ f N1 N2 N3 σ A v, r.1.length = A ∧ r.2.length = R := by
  intro r hr
  unfold bank at hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  rw [List.mem_filter, List.mem_range] at hq
  refine ⟨bitsLE_length A _, ?_⟩
  show (v.getD q default).length = R
  rw [List.getD_eq_getElem _ _ hq.1]
  exact hv _ (List.getElem_mem hq.1)

/-- (G4) The key width is at least one for `M ≥ 1`. -/
theorem one_le_keyWidth {M : ℕ} (hM : 1 ≤ M) : 1 ≤ c7KeyWidth M :=
  Nat.size_pos.mpr hM

/-- (G4) Every record index fits in the key width. -/
theorem lt_two_pow_keyWidth (M : ℕ) : M < 2 ^ c7KeyWidth M :=
  Nat.lt_size_self M

/-- (G4) The key width is at most `lgVol V` when `M ≤ V`. -/
theorem keyWidth_le_lgVol {M V : ℕ} (h : M ≤ V) : c7KeyWidth M ≤ lgVol V := by
  unfold c7KeyWidth lgVol
  rw [Nat.size_le]
  rcases Nat.eq_zero_or_pos V with hV | hV
  · have hM0 : M = 0 := by omega
    rw [hM0]
    positivity
  · calc M < 2 * V := by omega
      _ ≤ 2 ^ Nat.clog 2 (2 * V) := Nat.le_pow_clog (by norm_num) _

/-- (G5, arithmetic) Sort plus reinsertion cost against the Lemma A.9 budget. -/
theorem sort_reinsert_arith {M V R nb bm A L : ℕ} (hM : 1 ≤ M) (hMV : M * (R + 1) ≤ V)
    (hnb : nb ≤ bm) (hA : A ≤ L) :
    A * (nb * (8 * A + 8 * R + 17) + 10) + 16 * A + 2 + (M * (3 * A + 8 * R + 16) + 7) ≤
      64 * (V + M * (L + 1) ^ 3 + bm * L * (R + L + 2)) := by
  have h1 : A * nb ≤ L * bm := Nat.mul_le_mul hA hnb
  have h2 : A * nb * (8 * A + 8 * R + 17) ≤ L * bm * (8 * L + 8 * R + 17) :=
    Nat.mul_le_mul h1 (by omega)
  have h4 : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h5 : (L + 1) ^ 3 ≤ M * (L + 1) ^ 3 := Nat.le_mul_of_pos_left _ hM
  have h6 : M * A ≤ M * (L + 1) ^ 3 := Nat.mul_le_mul_left M (by omega)
  have h7 : M * R + M ≤ V := by
    have : M * (R + 1) = M * R + M := by ring
    omega
  have z1 := Nat.zero_le (bm * L * L)
  have z2 := Nat.zero_le (bm * L * R)
  have z3 := Nat.zero_le (bm * L)
  nlinarith [h1, h2, h4, h5, h6, h7, z1, z2, z3]

/-- (G5) Sort plus reinsertion cost of the repair phase, for `A = c7KeyWidth M`, `L = lgVol V`,
`V ≥ M (R + 1)` and at most `badMax K f M` exceptional records. -/
theorem repair_sort_reinsert_cost {K f M V R nb : ℕ} (hM : 1 ≤ M) (hMV : M * (R + 1) ≤ V)
    (hnb : nb ≤ badMax K f M) :
    c7KeyWidth M * (nb * (8 * c7KeyWidth M + 8 * R + 17) + 10) + 16 * c7KeyWidth M + 2 +
      (M * (3 * c7KeyWidth M + 8 * R + 16) + 7) ≤
      64 * (V + M * (lgVol V + 1) ^ 3 + badMax K f M * lgVol V * (R + lgVol V + 2)) := by
  have hMV' : M ≤ V := by
    have : M ≤ M * (R + 1) := Nat.le_mul_of_pos_right M (by omega)
    omega
  exact sort_reinsert_arith hM hMV hnb (keyWidth_le_lgVol hMV')

/-- (G6, arithmetic) The sort, reinsertion and pops cost against `64 · c7Cost`, with `C0 ≥ V` the
first summand of `c7Cost`. -/
theorem glue_cost_arith {M V C0 R nb bm A L : ℕ} (hM : 1 ≤ M) (hMV : M * (R + 1) ≤ V)
    (hVC : V ≤ C0) (hnb : nb ≤ bm) (hA : A ≤ L) :
    A * (nb * (8 * A + 8 * R + 17) + 10) + 16 * A + 2 + (1 + (M * (3 * A + 8 * R + 16) + 7 + 1)) ≤
      64 * (C0 + M * (L + 1) ^ 3 + bm * L * (R + L + 2)) := by
  have h1 : A * nb ≤ L * bm := Nat.mul_le_mul hA hnb
  have h2 : A * nb * (8 * A + 8 * R + 17) ≤ L * bm * (8 * L + 8 * R + 17) :=
    Nat.mul_le_mul h1 (by omega)
  have h4 : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h5 : (L + 1) ^ 3 ≤ M * (L + 1) ^ 3 := Nat.le_mul_of_pos_left _ hM
  have h6 : M * A ≤ M * (L + 1) ^ 3 := Nat.mul_le_mul_left M (by omega)
  have h7 : M * R + M ≤ V := by
    have : M * (R + 1) = M * R + M := by ring
    omega
  have z1 := Nat.zero_le (bm * L * L)
  have z2 := Nat.zero_le (bm * L * R)
  have z3 := Nat.zero_le (bm * L)
  nlinarith [h1, h2, h4, h5, h6, h7, z1, z2, z3]

/-- (G7, arithmetic) The extraction budget against `2 · c7Cost`. -/
theorem glue_extract_arith {M V C0 R bm L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L) (hVC : V ≤ C0) :
    M * (L + 1) ^ 3 + V + bm * (L + 1) + 1 ≤ 2 * (C0 + M * (L + 1) ^ 3 + bm * L * (R + L + 2)) := by
  have h1 : 1 ≤ M * (L + 1) ^ 3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : bm * (L + 1) ≤ bm * (2 * L) := Nat.mul_le_mul_left bm (by omega)
  have h3 : bm * L ≤ bm * L * (R + L + 2) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith [h1, h2, h3]

end SubNLogN.Machine.AppC.C7RepairAux.Math

namespace SubNLogN.Machine

open AppC.C7Aux AppC.C7RadixAux AppC.C7RepairAux AppC.C7RepairAux.Math SubNLogN.Machine.Calculus

/-- **Glue facts of the repair composition** (`C7RepairGlueStmt`, `C7Repair.lean`). -/
theorem c7RepairGlue_holds (τ : ℝ) (σ : Equiv.Perm (Fin 3)) : C7RepairGlueStmt τ σ := by
  intro K ρ f N0 N1 N2 N3 R w hK hρ hf hN0 hN1 hN2 hN3 hR hlen hrec
  have hMpos : 0 < c7M K f N0 N1 N2 N3 := by unfold c7M; positivity
  have hM1 : 1 ≤ w.length := by omega
  have hV : vol w = w.length * (R + 1) := vol_of_len hrec
  have hMV : w.length ≤ vol w := by
    rw [hV]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hAL : c7KeyWidth w.length ≤ lgVol (vol w) := keyWidth_le_lgVol hMV
  have hL1 : 1 ≤ lgVol (vol w) := by
    unfold lgVol
    exact Nat.clog_pos (by norm_num) (by omega)
  have hnb : (bank K ρ f N1 N2 N3 σ (c7KeyWidth w.length) w).length ≤ badMax K f w.length := by
    rw [bank_length, hlen]
    exact bad_count_le σ hK hρ hN1 hN2 hN3
  have hholes : (holes K ρ f N1 N2 N3 σ w).length = w.length := by
    unfold holes
    rw [List.length_map, List.length_range]
  have hceil : vol w ≤ ⌈(vol w : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1)⌉₊ := by
    have h0 : (0 : ℝ) ≤ ((f * K : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (by positivity) τ
    have h1 : (vol w : ℝ) ≤ (vol w : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1) := by
      have hv0 : (0 : ℝ) ≤ (vol w : ℝ) := by positivity
      nlinarith
    exact_mod_cast h1.trans (Nat.le_ceil _)
  refine ⟨holeCount_holes K ρ f N1 N2 N3 σ _ w, holes_rec_len K ρ f N1 N2 N3 σ w hrec,
    bank_rec_len K ρ f N1 N2 N3 σ _ w hrec, one_le_keyWidth hM1,
    le_of_lt (lt_two_pow_keyWidth _), ?_, ?_⟩
  · have hcd := countdownCost_le (fun _ => (bank K ρ f N1 N2 N3 σ (c7KeyWidth w.length) w).length *
      (8 * c7KeyWidth w.length + 8 * R + 17) + 10) (c7KeyWidth w.length)
    rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul] at hcd
    rw [hholes]
    unfold c7Cost
    refine le_trans ?_ (glue_cost_arith hM1 (le_of_eq hV.symm) hceil hnb hAL)
    omega
  · unfold c7Cost
    exact glue_extract_arith hM1 hL1 hceil

end SubNLogN.Machine
