/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixKit2
import SubNLogN.Machine.FFT.DIFRun
import SubNLogN.Math.Walsh.Proofs.DirectFFT

/-!
# K4-PREFIX, arithmetic and value facts for the driver (`Machine/FFT/PrefixFacts.lean`)

* `pf_bound`: `pfS + pfN + D·pfY = m₀`, so the passes act on the index bits `L, …, L + n - 1`
  with `L = D·pfY` and `n = pfN`.
* `pfN_le`: `n ≤ D`; `cnt_eq`, `cnt_pos`: the parameter counter for `v + 1 ≠ ℓ`.
* Width and shape facts for the passes and the truncations.

All proved, no `sorry`.
-/

namespace SubNLogN.Machine.FFT.PrefixAux

open TMFw TMFw.Contracts SubNLogN.Machine.FFT.DIF SubNLogN.Math.Walsh SubNLogN.Math.Common

section Arith

variable {D : ℕ}

/-- A prefix round of round index `v < ℓ` with `K ≥ 1`: `v = ℓ - 1` or `v < b₀`. -/
theorem prefix_cases (ℓ K v : ℕ) (hK : 1 ≤ K) (hv : v < ℓ) (hnc : ¬ IsChunkRound ℓ K v) :
    v + 1 = ℓ ∨ (v + 1 ≠ ℓ ∧ v < layoutB0 ℓ K) := by
  by_cases h : v + 1 = ℓ
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    by_contra hc
    exact hnc ⟨by omega, by omega, by omega⟩

theorem layoutB0_le (ℓ K : ℕ) : layoutB0 ℓ K ≤ ℓ - 1 := Nat.mod_le _ _

theorem nLong_le (ℓ : ℕ) (a : Fin D → ℕ) : LayoutPermAux.nLong ℓ a ≤ D := by
  unfold LayoutPermAux.nLong
  calc ((List.finRange D).filter _).length ≤ (List.finRange D).length := List.length_filter_le _ _
    _ = D := List.length_finRange

theorem pf_bound (q ℓ K w v : ℕ) (a : Fin D → ℕ) (hshape : MidShapeOK q ℓ K w a) (hv : v < ℓ)
    (hnc : ¬ IsChunkRound ℓ K v) :
    pfS ℓ K a v + pfN ℓ K a v + D * pfY ℓ K v = addrBits a := by
  obtain ⟨-, -, hℓ2, -, hK1, -, ha, -⟩ := hshape
  rw [LayoutPermAux.addrBits_eq ℓ a (by omega) ha]
  rcases prefix_cases ℓ K v hK1 hv hnc with h | ⟨h, hb⟩
  · simp only [pfS, pfN, pfY, if_pos h]
    ring
  · simp only [pfS, pfN, pfY, if_neg h]
    have hb0 := layoutB0_le ℓ K
    obtain ⟨x, hx⟩ : ∃ x, x = layoutB0 ℓ K - 1 - v := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y, y = ℓ - 1 - layoutB0 ℓ K + v := ⟨_, rfl⟩
    have hxy : ℓ - 1 = x + 1 + y := by omega
    rw [← hx, ← hy, hxy]
    ring

theorem pfN_le (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) : pfN ℓ K a v ≤ D := by
  unfold pfN
  split_ifs
  · exact nLong_le ℓ a
  · exact le_rfl

theorem cnt_eq (q ℓ K w v : ℕ) (a : Fin D → ℕ) (hshape : MidShapeOK q ℓ K w a) (hv : v < ℓ)
    (hnc : ¬ IsChunkRound ℓ K v) (h : v + 1 ≠ ℓ) :
    (if v + 1 = ℓ then 0 else 2 ^ D - 1) = 2 ^ pfN ℓ K a v - 1 := by
  simp only [pfN, if_neg h]

theorem cnt_pos (D' : ℕ) (hD : 1 ≤ D') : 1 ≤ 2 ^ D' - 1 := by
  have : 2 ≤ 2 ^ D' := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ D' := Nat.pow_le_pow_right (by norm_num) hD
  omega

/-- Case `v = ℓ - 1`: the record count is `2^L` blocks of `2^n`, `L + n = m₀`. -/
theorem caseA_bits (q ℓ K w v : ℕ) (a : Fin D → ℕ) (hshape : MidShapeOK q ℓ K w a) (hv : v < ℓ)
    (hnc : ¬ IsChunkRound ℓ K v) (h : v + 1 = ℓ) :
    D * pfY ℓ K v + pfN ℓ K a v = addrBits a := by
  have := pf_bound q ℓ K w v a hshape hv hnc
  simp only [pfS, if_pos h] at this
  omega

theorem two_pow_sub_one_div_two (k : ℕ) : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [pow_succ]
  omega

end Arith

/-! ## Arrays: truncations, shapes, widths -/

theorem tdivPow_zero (x : ℤ) : tdivPow x 0 = x := by
  simp [tdivPow]

theorem mapC_truncShift_zero (B : List (List CInt)) : mapC (truncShiftC 0) B = B := by
  unfold mapC truncShiftC
  conv_rhs => rw [← List.map_id B]
  apply List.map_congr_left
  intro row _
  conv_rhs => rw [← List.map_id row]
  apply List.map_congr_left
  intro c _
  simp [tdivPow_zero]

theorem fitsTwos_tdivPow {W : ℕ} {x : ℤ} (h : FitsTwos W x) (s : ℕ) : FitsTwos W (tdivPow x s) := by
  unfold FitsTwos at *
  unfold tdivPow
  have hp : (0 : ℤ) < 2 ^ s := by positivity
  by_cases hx : 0 ≤ x
  · have h1 : 0 ≤ x.tdiv (2 ^ s) := Int.tdiv_nonneg hx hp.le
    have h2 : x.tdiv (2 ^ s) ≤ x := Int.tdiv_le_self _ hx
    constructor <;> omega
  · have hx' : 0 ≤ -x := by omega
    have e : x.tdiv (2 ^ s) = -((-x).tdiv (2 ^ s)) := by rw [Int.neg_tdiv, neg_neg]
    have h1 : 0 ≤ (-x).tdiv (2 ^ s) := Int.tdiv_nonneg hx' hp.le
    have h2 : (-x).tdiv (2 ^ s) ≤ -x := Int.tdiv_le_self _ hx'
    rw [e]
    constructor <;> omega

theorem fits_mapC_trunc {W : ℕ} {B : List (List CInt)} (h : CArrFits W B) (s : ℕ) :
    CArrFits W (mapC (truncShiftC s) B) := by
  intro cs hcs c hc
  simp only [mapC, List.mem_map] at hcs
  obtain ⟨row, hrow, rfl⟩ := hcs
  obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
  exact ⟨fitsTwos_tdivPow (h row hrow c0 hc0).1 s, fitsTwos_tdivPow (h row hrow c0 hc0).2 s⟩

theorem fits_iter_trunc {W : ℕ} {B : List (List CInt)} (h : CArrFits W B) :
    ∀ i, CArrFits W ((mapC (truncShiftC 1))^[i] B) := by
  intro i
  induction i with
  | zero => exact h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact fits_mapC_trunc ih 1

theorem shape_mapC (f : CInt → CInt) (B : List (List CInt)) (N r : ℕ) (hB : B.length = N)
    (hrow : ∀ row ∈ B, row.length = r) :
    (mapC f B).length = N ∧ ∀ row ∈ mapC f B, row.length = r := by
  refine ⟨by simp [mapC, hB], fun row hr => ?_⟩
  simp only [mapC, List.mem_map] at hr
  obtain ⟨row0, h0, rfl⟩ := hr
  simp [hrow row0 h0]

theorem shape_iter_trunc (B : List (List CInt)) (N r : ℕ) (hB : B.length = N)
    (hrow : ∀ row ∈ B, row.length = r) :
    ∀ i, ((mapC (truncShiftC 1))^[i] B).length = N ∧
      ∀ row ∈ (mapC (truncShiftC 1))^[i] B, row.length = r := by
  intro i
  induction i with
  | zero => exact ⟨hB, hrow⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact shape_mapC _ _ N r ih.1 ih.2

theorem cvol_shape (w : ℕ) (B : List (List CInt)) (N r : ℕ) (hB : B.length = N)
    (hrow : ∀ row ∈ B, row.length = r) : cvol w B = N + 2 * w * (N * r) := by
  rw [cvol_eq, ncoef_uniform B r hrow, hB]

theorem shape_encCube {m : ℕ} (q ℓ : ℕ) (z : RArr (Cube m) (2 ^ ℓ)) :
    (encCube q z).length = 2 ^ m ∧ ∀ row ∈ encCube q z, row.length = 2 ^ ℓ := by
  refine ⟨by simp [encCube, encArr, cubeAddrs], fun row hr => ?_⟩
  simp only [encCube, encArr, List.mem_map] at hr
  obtain ⟨x, -, rfl⟩ := hr
  simp

theorem fits_encCube {m r : ℕ} {q w : ℕ} (hw : q + 2 ≤ w) {z : RArr (Cube m) r}
    (hz : ArrOnDiskGrid q z) : CArrFits w (encCube q z) := by
  intro cs hcs c hc
  simp only [encCube, encArr, List.mem_map] at hcs
  obtain ⟨x, -, rfl⟩ := hcs
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc
  exact fits_gridInt hw (hz x k)

theorem diskGrid_truncArr_hT {m r q : ℕ} (T : Finset (Fin m)) {z : RArr (Cube m) r}
    (hz : ArrOnDiskGrid q z) : ArrOnDiskGrid q (truncArr q (hT T z)) := fun x k =>
  truncC_mem_diskGrid q _ (DirectFFTProof.hT_apply_norm_le T z (fun y k' => (hz y k').2) x k)

end SubNLogN.Machine.FFT.PrefixAux
