/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostScanMath
import SubNLogN.Machine.Bridge.PrePostKD
import SubNLogN.Machine.Bridge.Values
import SubNLogN.Math.Bridge.IntForms.Spread

/-!
# K5 pre-scaling: value lemmas (`Bridge/PreScaleVal.lean`)

Pure value lemmas for the `PreScaleStmt` machine (`Bridge/PrePostPreMain.lean`):
* `clog_preScaleMax`: `⌈log₂ M⌉` of `preScaleMax` is what the scan computes
  (`max pIn` of a `cmax` fold over the reversed numerator list);
* `dimD_eq`, `lg_dimD`: for a power-of-two shape `D = ∏_{i ≥ 1} t_i = 2^kD` with
  `kD = Σ_{i ≥ 1} zcount t_i`, so `lg D = max kD 1`;
* `preScaleExp_eq`: the pre-scaling exponent in terms of the scan result and `kD`;
* `encVec_preScaled_le` / `encVec_preScaled_gt`: the stored pre-scaled array is an exact left
  shift (`shlC`), resp. a truncating right shift (`truncShiftC`, exact under the grid hypothesis)
  of the stored input;
* `scanMax_le`: the scan result is `≤ w - 1` for inputs fitting `w`-bit two's complement;
* header-length bounds `zsum_le_hdr`, `bitLen_le_hdr`, `length_le_hdr`; `natSyms_tail`.

All proved, no `sorry`.
-/

namespace SubNLogN.Machine.BridgePSH

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.BridgePP
open SubNLogN.Math.Common SubNLogN.Math.Common.GridInt SubNLogN.Math.Bridge Computability

/-- The input numerators in index order. -/
noncomputable def nums (F : ℕ) {R : ℕ} (x : Fin R → ℂ) : List CInt :=
  (List.finRange R).map fun j => gridInt F (x j)

/-- `M`: what the pre-scaling scan computes (pass 2 runs over the reversed list). -/
noncomputable def scanMax (F : ℕ) {R : ℕ} (x : Fin R → ℂ) : ℕ := (nums F x).reverse.foldl cmax 0

/-- `kD = Σ_{i ≥ 1} zcount (t i)` (`= lg D` for a power-of-two shape). -/
def kD {d : ℕ} (t : Fin d → ℕ) : ℕ := zsum (List.ofFn t).tail

/-! ## The `cmax` fold -/

theorem foldl_cmax_le_iff_psv (n : ℕ) : ∀ (L : List CInt) (m : ℕ),
    L.foldl cmax m ≤ n ↔
      m ≤ n ∧ ∀ c ∈ L, Nat.clog 2 c.1.natAbs ≤ n ∧ Nat.clog 2 c.2.natAbs ≤ n
  | [], m => by simp
  | c :: L, m => by
    rw [List.foldl_cons, foldl_cmax_le_iff_psv n L (cmax m c)]
    simp only [cmax, max_le_iff, List.mem_cons, forall_eq_or_imp]
    tauto

theorem clog_preScaleMax (pIn : ℕ) {R : ℕ} (X : Fin R → ℤ × ℤ) :
    Nat.clog 2 (IntForms.preScaleMax pIn X) =
      max pIn (((List.finRange R).map X).reverse.foldl cmax 0) := by
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num)]
    have h1 : ((List.finRange R).map X).reverse.foldl cmax 0 ≤
        max pIn (((List.finRange R).map X).reverse.foldl cmax 0) := le_max_right _ _
    rw [foldl_cmax_le_iff_psv] at h1
    obtain ⟨-, h2⟩ := h1
    unfold IntForms.preScaleMax
    refine max_le (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)) (max_le ?_ ?_)
    · apply Finset.sup_le
      intro j _
      exact (Nat.clog_le_iff_le_pow (by norm_num)).1 (h2 (X j) (by simp)).1
    · apply Finset.sup_le
      intro j _
      exact (Nat.clog_le_iff_le_pow (by norm_num)).1 (h2 (X j) (by simp)).2
  · apply max_le
    · have hM : 2 ^ pIn ≤ IntForms.preScaleMax pIn X := le_max_left _ _
      calc pIn = Nat.clog 2 (2 ^ pIn) := (Nat.clog_pow 2 pIn (by norm_num)).symm
        _ ≤ Nat.clog 2 (IntForms.preScaleMax pIn X) := Nat.clog_mono_right 2 hM
    · rw [foldl_cmax_le_iff_psv]
      refine ⟨Nat.zero_le _, fun c hc => ?_⟩
      rw [List.mem_reverse, List.mem_map] at hc
      obtain ⟨j, -, rfl⟩ := hc
      constructor
      · apply Nat.clog_mono_right
        unfold IntForms.preScaleMax
        exact le_max_of_le_right (le_max_of_le_left
          (Finset.le_sup (f := fun j => (X j).1.natAbs) (Finset.mem_univ j)))
      · apply Nat.clog_mono_right
        unfold IntForms.preScaleMax
        exact le_max_of_le_right (le_max_of_le_right
          (Finset.le_sup (f := fun j => (X j).2.natAbs) (Finset.mem_univ j)))

/-! ## `D` and `kD` -/

theorem pow_zcount_eq_psv {t : ℕ} (h : ∃ a, t = 2 ^ a) : 2 ^ zcount t = t := by
  obtain ⟨a, rfl⟩ := h
  rw [zcount_two_pow]

theorem dimD_eq {d : ℕ} (t : Fin d → ℕ) (hd : 1 ≤ d) (ht : ShapeOK t) : dimD t = 2 ^ kD t := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  unfold dimD kD
  rw [Finset.prod_filter, Fin.prod_univ_succ, List.ofFn_succ, List.tail_cons]
  simp only [Fin.val_zero, ne_eq, not_true_eq_false, if_false, Fin.val_succ, Nat.add_one_ne_zero,
    not_false_eq_true, if_true, one_mul]
  unfold zsum
  rw [List.map_ofFn, List.sum_ofFn, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (pow_zcount_eq_psv (ht i.succ).2).symm

theorem lg_dimD {d : ℕ} (t : Fin d → ℕ) (hd : 1 ≤ d) (ht : ShapeOK t) :
    lg (dimD t) = max (kD t) 1 := by
  rw [BridgePSH.dimD_eq t hd ht, lg, Nat.clog_pow 2 _ (by norm_num)]

theorem preScaleExp_eq {d : ℕ} (t : Fin d → ℕ) (hd : 1 ≤ d) (ht : ShapeOK t) (pIn : ℕ)
    (x : Fin (totalLen t) → ℂ) (hx : ∀ j, OnGrid pIn (x j)) :
    preScaleExp t x = 1 + (max pIn (scanMax pIn x) - pIn) + (max (kD t) 1 + 1) / 2 + 4 := by
  rw [IntForms.preScaleExp_eq_nat t pIn x (fun j => gridInt pIn (x j))
    (fun j => (gridValC_gridIntC (hx j)).symm)]
  unfold IntForms.preScaleExpNat IntForms.preScaleHNat scanMax nums
  rw [BridgePSH.clog_preScaleMax, BridgePSH.lg_dimD t hd ht]

/-! ## The stored pre-scaled array -/

theorem gridInt_gridValC_psv (F : ℕ) (c : ℤ × ℤ) : gridInt F (gridValC F c) = c :=
  gridIntC_gridValC F c

theorem encVec_preScaled_le {d : ℕ} (t : Fin d → ℕ) (pIn q : ℕ) (x : Fin (totalLen t) → ℂ)
    (hx : ∀ j, OnGrid pIn (x j)) (hA : pIn + preScaleExp t x ≤ q) :
    encVec q (preScaled t x) = mapC (shlC (q - (pIn + preScaleExp t x))) (encVec pIn x) := by
  unfold encVec mapC
  rw [List.map_map]
  refine List.map_congr_left fun j _ => ?_
  have h := IntForms.preScaled_eq_gridValC_of_le t pIn q x (fun j => gridInt pIn (x j))
    (fun j => (gridValC_gridIntC (hx j)).symm) hA j
  simp only [Function.comp, List.map_cons, List.map_nil]
  rw [h, gridInt_gridValC_psv]
  unfold IntForms.preScaledInt
  rw [if_pos hA]
  simp [smulC, shlC, mul_comm]

theorem encVec_preScaled_gt {d : ℕ} (t : Fin d → ℕ) (pIn q : ℕ) (x : Fin (totalLen t) → ℂ)
    (hx : ∀ j, OnGrid pIn (x j)) (hg : ∀ j, OnGrid q (preScaled t x j))
    (hA : q < pIn + preScaleExp t x) :
    encVec q (preScaled t x) =
      mapC (truncShiftC (pIn + preScaleExp t x - q)) (encVec pIn x) := by
  unfold encVec mapC
  rw [List.map_map]
  refine List.map_congr_left fun j _ => ?_
  have hX : ∀ j, x j = gridValC pIn (gridInt pIn (x j)) := fun j =>
    (gridValC_gridIntC (hx j)).symm
  have h := IntForms.preScaled_eq_gridValC_of_onGrid t pIn q x (fun j => gridInt pIn (x j)) hX j
    (hg j)
  obtain ⟨s, hs⟩ : ∃ s, pIn + preScaleExp t x = q + s := ⟨pIn + preScaleExp t x - q, by omega⟩
  have hs' : pIn + preScaleExp t x - q = s := by omega
  have hgrid := hg j
  rw [IntForms.preScaled_eq_gridValC_add t pIn x (fun j => gridInt pIn (x j)) hX j, hs] at hgrid
  obtain ⟨c', hc'⟩ := onGrid_iff_exists_gridValC.mp hgrid
  rw [← gridValC_add_smulC_two_pow q s c', gridValC_inj] at hc'
  have hd1 : (2 : ℤ) ^ s ∣ (gridInt pIn (x j)).1 := ⟨c'.1, by rw [← hc']; rfl⟩
  have hd2 : (2 : ℤ) ^ s ∣ (gridInt pIn (x j)).2 := ⟨c'.2, by rw [← hc']; rfl⟩
  simp only [Function.comp, List.map_cons, List.map_nil]
  rw [h, gridInt_gridValC_psv]
  unfold IntForms.preScaledInt
  rw [if_neg (by omega), hs']
  simp only [truncShiftC, tdivPow, List.cons.injEq, and_true, Prod.mk.injEq]
  exact ⟨(Int.tdiv_eq_ediv_of_dvd hd1).symm, (Int.tdiv_eq_ediv_of_dvd hd2).symm⟩

/-! ## The scan bound -/

theorem natAbs_le_of_fitsTwos_psv {w : ℕ} {z : ℤ} (h : FitsTwos w z) :
    z.natAbs ≤ 2 ^ (w - 1) := by
  obtain ⟨h1, h2⟩ := h
  have h3 : |z| ≤ 2 ^ (w - 1) := abs_le.2 ⟨h1, h2.le⟩
  have h5 : ((z.natAbs : ℕ) : ℤ) ≤ ((2 ^ (w - 1) : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    push_cast
    exact h3
  exact_mod_cast h5

theorem clog_le_of_fitsTwos_psv {w : ℕ} {z : ℤ} (h : FitsTwos w z) :
    Nat.clog 2 z.natAbs ≤ w - 1 :=
  (Nat.clog_le_iff_le_pow (by norm_num)).2 (natAbs_le_of_fitsTwos_psv h)

theorem scanMax_le (w F : ℕ) {R : ℕ} (x : Fin R → ℂ) (h : ArrFits w F x) :
    scanMax F x ≤ w - 1 := by
  unfold scanMax nums
  rw [foldl_cmax_le_iff_psv]
  refine ⟨Nat.zero_le _, fun c hc => ?_⟩
  rw [List.mem_reverse, List.mem_map] at hc
  obtain ⟨j, -, rfl⟩ := hc
  exact ⟨clog_le_of_fitsTwos_psv (h j).1, clog_le_of_fitsTwos_psv (h j).2⟩

/-! ## Header lengths -/

theorem length_natSyms_psv (n : ℕ) : (natSyms n).length = bitLen n := by
  simp [natSyms, bitLen]

theorem length_hdrSyms_cons_psv (a : ℕ) (L : List ℕ) :
    (hdrSyms (a :: L)).length = bitLen a + 1 + (hdrSyms L).length := by
  rw [BridgePP.hdrSyms_cons]
  simp [length_natSyms_psv]
  omega

theorem zcount_le_bitLen_psv (x : ℕ) : zcount x ≤ bitLen x := by
  unfold zcount bitLen
  exact List.count_le_length ..

theorem zsum_le_hdr (fs : List ℕ) : zsum fs ≤ (hdrSyms fs).length := by
  induction fs with
  | nil => simp [zsum, hdrSyms]
  | cons a fs ih =>
    have h1 := zcount_le_bitLen_psv a
    have h2 : zsum (a :: fs) = zcount a + zsum fs := by simp [zsum]
    rw [h2, length_hdrSyms_cons_psv]
    omega

theorem bitLen_le_hdr (fs : List ℕ) : ∀ x ∈ fs, bitLen x ≤ (hdrSyms fs).length := by
  induction fs with
  | nil => intro x hx; simp at hx
  | cons a fs ih =>
    intro x hx
    rw [length_hdrSyms_cons_psv]
    rcases List.mem_cons.1 hx with rfl | h
    · omega
    · have := ih x h
      omega

theorem length_le_hdr (fs : List ℕ) : fs.length ≤ (hdrSyms fs).length := by
  induction fs with
  | nil => simp [hdrSyms]
  | cons a fs ih =>
    rw [length_hdrSyms_cons_psv, List.length_cons]
    omega

/-! ## Halving a counter -/

theorem encodeNat_tail_psv (m : ℕ) : (encodeNat m).tail = encodeNat (m / 2) := by
  obtain ⟨n, rfl | rfl⟩ : ∃ n, m = n + n ∨ m = n + n + 1 := ⟨m / 2, by omega⟩
  · rw [encodeNat_add, show (n + n) / 2 = n by omega]
    split_ifs with h
    · simp [h]
    · rfl
  · rw [encodeNat_add_add_one, show (n + n + 1) / 2 = n by omega]
    rfl

theorem natSyms_tail (m : ℕ) : (natSyms m).tail = natSyms (m / 2) := by
  unfold natSyms
  rw [← encodeNat_tail_psv]
  rcases encodeNat m with _ | ⟨a, l⟩ <;> rfl

end SubNLogN.Machine.BridgePSH
