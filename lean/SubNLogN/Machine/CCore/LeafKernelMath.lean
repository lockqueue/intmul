/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.CCore
import SubNLogN.Math.Networks.Proofs.CCoreCorrect
import SubNLogN.Machine.Layer.DrvPreDefs

/-!
# C-core leaf kernel: the value layer (`CCore/LeafKernelMath.lean`)

Pure facts behind `LeafStmt` (`CCore/SkelDefs.lean`): at a leaf the C-core value
`cCoreVal ρ j0 e h z` is computed by `e` individual kernels, one per selected-bit field.

* `gatesR ρ j0 n h z`: the individual kernels `gateR` (`Math/Networks/Proofs/CCoreCorrect.lean`) on the
  selected bit `ρ` of the chunks `j0, …, j0+n−1`, on the full row class `topC`.
  `gatesR_eq_cCoreVal`: for `n = e` this is `cCoreVal ρ j0 e h z`.
* `growth_gateR`: one kernel raises the growth bound by one (`ArrGrowth P b → ArrGrowth P (b+1)`).
* `gridInt_gate0`, `gridInt_gate1`: on the `G`-grid, the numerators at precision `G + 1` of the
  two outputs `a·u + b·v`, `b·u + a·v` are the driver's integer kernels `cgate0`, `cgate1`
  (`Layer/DrvPreDefs.lean`) of the input numerators; the halving there is exact.
* (next part) block structure of the lexicographic record order (`layerAddrs`): for the field of
  chunk `j`, bit `ρ`, the record pairs are `(i, i + W)` inside blocks of `2W` records,
  `W = S·2^(K(D−1−j)+ρ)`; hence one kernel on the stored records is `cgateBlock W` blockwise.
-/

namespace SubNLogN.Machine.CCore.LeafKernelAux

open SubNLogN.Math.Walsh SubNLogN.Math.Common SubNLogN.Math.Networks
open SubNLogN.Math.Networks.Model SubNLogN.Math.Networks.CCoreAux
open SubNLogN.Machine.Layer

/-! ## The individual kernels compose to `cCoreVal` -/

section Gates

variable {A K D S r : ℕ}

/-- The full row class of the layer layout (row field `0`, modulus `1`). -/
def topC (A K D S : ℕ) : RowClass (layerLayout A K D S) :=
  RowClass.top ⟨0, by simp [layerLayout]⟩

theorem topC_mem (A K D S : ℕ) (y : (layerLayout A K D S).Addr) : (topC A K D S).mem y := by
  unfold topC RowClass.top RowClass.mem
  exact Nat.mod_one _

theorem topC_row (A K D S : ℕ) : (topC A K D S).row.val = 0 := rfl

/-- The individual kernels on the selected bit `ρ` of the chunks `j0, …, j0+n−1` (in this
order), on every address. -/
noncomputable def gatesR (ρ : Fin K) (j0 : ℕ) : (n : ℕ) → j0 + n ≤ D →
    RArr (LayerAddr A K D S) r → RArr (LayerAddr A K D S) r
  | 0, _, z => z
  | n + 1, h, z => gateR ρ ⟨j0 + n, by omega⟩ (topC A K D S) (gatesR ρ j0 n (by omega) z)

theorem gatesR_eq_cdonR (ρ : Fin K) (j0 : ℕ) :
    ∀ (n : ℕ) (h : j0 + n ≤ D) (z : RArr (LayerAddr A K D S) r),
      gatesR ρ j0 n h z = cdonR ρ (grpSet D j0 n) (topC A K D S) z
  | 0, _, z => by
    have : grpSet D j0 0 = ∅ := by
      ext j
      simp only [grpSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      omega
    rw [this, cdonR_empty]
    rfl
  | n + 1, h, z => by
    have hj : j0 + n < D := by omega
    show gateR ρ ⟨j0 + n, hj⟩ (topC A K D S) (gatesR ρ j0 n (by omega) z) = _
    rw [gatesR_eq_cdonR ρ j0 n (by omega) z, gateR_eq_cdonR,
      cdonR_comp ρ (topC_row A K D S) (disjoint_grpSet j0 n hj), grpSet_succ j0 n hj]

/-- **The leaf value**: the `e` individual kernels of the group give `cCoreVal`. -/
theorem gatesR_eq_cCoreVal (ρ : Fin K) (j0 e : ℕ) (h : j0 + e ≤ D)
    (z : RArr (LayerAddr A K D S) r) : gatesR ρ j0 e h z = cCoreVal ρ j0 e h z := by
  rw [gatesR_eq_cdonR, cdonR_grp]
  funext x
  rw [if_pos (topC_mem A K D S _)]

/-- One kernel on the full class, pointwise. -/
theorem gateR_topC_apply (ρ : Fin K) (j : Fin D) (z : RArr (LayerAddr A K D S) r)
    (x : LayerAddr A K D S) (k : Fin r) :
    gateR ρ j (topC A K D S) z x k = ka * z x k + kb * z (flipSel ρ j x) k := by
  simp only [gateR, if_pos (topC_mem A K D S (encodeAddr x)), Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]

end Gates

/-! ## The kernel constants -/

section Consts

theorem ka_re : ka.re = 1 / 2 := by simp [ka]
theorem ka_im : ka.im = 1 / 2 := by simp [ka]
theorem kb_re : kb.re = 1 / 2 := by simp [kb]
theorem kb_im : kb.im = -(1 / 2) := by simp [kb]; norm_num

theorem norm_ka_le : ‖ka‖ ≤ 1 := by
  unfold ka
  rw [norm_div]
  have h1 : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := by
    calc ‖(1 : ℂ) + Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one, Complex.norm_I]; norm_num
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, div_le_one (by norm_num)]
  exact h1

theorem norm_kb_le : ‖kb‖ ≤ 1 := by
  unfold kb
  rw [norm_div]
  have h1 : ‖(1 : ℂ) - Complex.I‖ ≤ 2 := by
    calc ‖(1 : ℂ) - Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, Complex.norm_I]; norm_num
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, div_le_one (by norm_num)]
  exact h1

/-- Real part of the first output `a·u + b·v`. -/
theorem gate0_re (u v : ℂ) : (ka * u + kb * v).re = (u.re - u.im + v.re + v.im) / 2 := by
  simp only [Complex.add_re, Complex.mul_re, ka_re, ka_im, kb_re, kb_im]
  ring

theorem gate0_im (u v : ℂ) : (ka * u + kb * v).im = (u.re + u.im - v.re + v.im) / 2 := by
  simp only [Complex.add_im, Complex.mul_im, ka_re, ka_im, kb_re, kb_im]
  ring

/-- Real part of the second output `b·u + a·v`. -/
theorem gate1_re (u v : ℂ) : (kb * u + ka * v).re = (u.re + u.im + v.re - v.im) / 2 := by
  simp only [Complex.add_re, Complex.mul_re, ka_re, ka_im, kb_re, kb_im]
  ring

theorem gate1_im (u v : ℂ) : (kb * u + ka * v).im = (-u.re + u.im + v.re + v.im) / 2 := by
  simp only [Complex.add_im, Complex.mul_im, ka_re, ka_im, kb_re, kb_im]
  ring

end Consts

/-! ## Growth of one kernel -/

section Growth

variable {A K D S r : ℕ}

theorem onGrid_gate {q : ℕ} {u v : ℂ} (hu : OnGrid q u) (hv : OnGrid q v) :
    OnGrid (q + 1) (ka * u + kb * v) := by
  have e : ka * u + kb * v = ((u + v) + (u - v) * Complex.I) / 2 := by
    unfold ka kb
    ring
  rw [e]
  exact ((hu.add hv).add ((hu.sub hv).mul_I)).half

/-- **One kernel raises the growth bound by one.** -/
theorem growth_gateR (ρ : Fin K) (j : Fin D) {P b : ℕ} {z : RArr (LayerAddr A K D S) r}
    (hz : ArrGrowth P b z) : ArrGrowth P (b + 1) (gateR ρ j (topC A K D S) z) := by
  intro x k
  rw [gateR_topC_apply]
  obtain ⟨g1, n1⟩ := hz x k
  obtain ⟨g2, n2⟩ := hz (flipSel ρ j x) k
  refine ⟨?_, ?_⟩
  · have := onGrid_gate g1 g2
    rwa [Nat.add_assoc] at this
  · calc ‖ka * z x k + kb * z (flipSel ρ j x) k‖
        ≤ ‖ka‖ * ‖z x k‖ + ‖kb‖ * ‖z (flipSel ρ j x) k‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 * 2 ^ b + 1 * 2 ^ b := by
          gcongr
          · exact norm_ka_le
          · exact norm_kb_le
      _ = 2 ^ (b + 1) := by ring

/-- Growth after `n` kernels. -/
theorem growth_gatesR (ρ : Fin K) (j0 : ℕ) {P b : ℕ} :
    ∀ (n : ℕ) (h : j0 + n ≤ D) {z : RArr (LayerAddr A K D S) r},
      ArrGrowth P b z → ArrGrowth P (b + n) (gatesR ρ j0 n h z)
  | 0, _, _, hz => hz
  | n + 1, h, _, hz => growth_gateR ρ _ (growth_gatesR ρ j0 n (by omega) hz)

end Growth

/-! ## The kernel on numerators -/

section Numerators

theorem gridUnit_mul_two_pow_self (F : ℕ) : gridUnit F * 2 ^ F = 1 := by
  unfold gridUnit
  exact inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)

theorem gridUnit_succ (G : ℕ) : gridUnit G = 2 * gridUnit (G + 1) := by
  unfold gridUnit
  rw [pow_succ, mul_inv, ← mul_assoc, mul_comm (2 : ℝ), mul_assoc, mul_inv_cancel₀ two_ne_zero,
    mul_one]

/-- `gridInt` of an exact grid point. -/
theorem gridInt_of_re_im {F : ℕ} {z : ℂ} {a b : ℤ} (ha : z.re = a * gridUnit F)
    (hb : z.im = b * gridUnit F) : gridInt F z = (a, b) := by
  simp only [gridInt, ha, hb, mul_assoc, gridUnit_mul_two_pow_self, mul_one, round_intCast]

theorem tdiv_two_mul (m : ℤ) : (2 * m).tdiv 2 = m := Int.mul_tdiv_cancel_left m two_ne_zero

/-- **First output on numerators.** On the `G`-grid, the numerators at precision `G + 1` of
`a·u + b·v` are `cgate0` of the input numerators (the halving is exact). -/
theorem gridInt_gate0 {G : ℕ} {u v : ℂ} (hu : OnGrid G u) (hv : OnGrid G v) :
    gridInt (G + 1) (ka * u + kb * v) = cgate0 (gridInt (G + 1) u) (gridInt (G + 1) v) := by
  obtain ⟨⟨a1, ha1⟩, ⟨a2, ha2⟩⟩ := hu
  obtain ⟨⟨b1, hb1⟩, ⟨b2, hb2⟩⟩ := hv
  have hU := gridUnit_succ G
  rw [gridInt_of_re_im (z := u) (a := 2 * a1) (b := 2 * a2) (by rw [ha1, hU]; push_cast; ring)
      (by rw [ha2, hU]; push_cast; ring),
    gridInt_of_re_im (z := v) (a := 2 * b1) (b := 2 * b2) (by rw [hb1, hU]; push_cast; ring)
      (by rw [hb2, hU]; push_cast; ring),
    gridInt_of_re_im (z := ka * u + kb * v) (a := a1 - a2 + b1 + b2) (b := a1 + a2 - b1 + b2)
      (by rw [gate0_re, ha1, ha2, hb1, hb2, hU]; push_cast; ring)
      (by rw [gate0_im, ha1, ha2, hb1, hb2, hU]; push_cast; ring)]
  have e1 : 2 * a1 + 2 * b1 - (2 * a2 - 2 * b2) = 2 * (a1 - a2 + b1 + b2) := by ring
  have e2 : 2 * a2 + 2 * b2 + (2 * a1 - 2 * b1) = 2 * (a1 + a2 - b1 + b2) := by ring
  simp only [cgate0, tdivPow, pow_one, e1, e2, tdiv_two_mul]

/-- **Second output on numerators**: `b·u + a·v` gives `cgate1`. -/
theorem gridInt_gate1 {G : ℕ} {u v : ℂ} (hu : OnGrid G u) (hv : OnGrid G v) :
    gridInt (G + 1) (kb * u + ka * v) = cgate1 (gridInt (G + 1) u) (gridInt (G + 1) v) := by
  obtain ⟨⟨a1, ha1⟩, ⟨a2, ha2⟩⟩ := hu
  obtain ⟨⟨b1, hb1⟩, ⟨b2, hb2⟩⟩ := hv
  have hU := gridUnit_succ G
  rw [gridInt_of_re_im (z := u) (a := 2 * a1) (b := 2 * a2) (by rw [ha1, hU]; push_cast; ring)
      (by rw [ha2, hU]; push_cast; ring),
    gridInt_of_re_im (z := v) (a := 2 * b1) (b := 2 * b2) (by rw [hb1, hU]; push_cast; ring)
      (by rw [hb2, hU]; push_cast; ring),
    gridInt_of_re_im (z := kb * u + ka * v) (a := a1 + a2 + b1 - b2) (b := -a1 + a2 + b1 + b2)
      (by rw [gate1_re, ha1, ha2, hb1, hb2, hU]; push_cast; ring)
      (by rw [gate1_im, ha1, ha2, hb1, hb2, hU]; push_cast; ring)]
  have e1 : 2 * a1 + 2 * b1 + (2 * a2 - 2 * b2) = 2 * (a1 + a2 + b1 - b2) := by ring
  have e2 : 2 * a2 + 2 * b2 - (2 * a1 - 2 * b1) = 2 * (-a1 + a2 + b1 + b2) := by ring
  simp only [cgate1, tdivPow, pow_one, e1, e2, tdiv_two_mul]

end Numerators

/-! ## Addresses of the lexicographic record order -/

section Addr

variable {A K D S : ℕ}

/-- Position of bit `k` of chunk `j` in `i / S` (lexicographic order). -/
theorem pos_lt {j k : ℕ} (hj : j < D) (hk : k < K) : k + K * (D - 1 - j) < K * D := by
  have h1 : K * (D - j) = K * (D - 1 - j) + K := by
    rw [show D - j = (D - 1 - j) + 1 by omega, Nat.mul_succ]
  have h2 : K * (D - j) ≤ K * D := Nat.mul_le_mul_left _ (by omega)
  omega

theorem pos_inj {j j' k k' : ℕ} (hj : j < D) (hj' : j' < D) (hk : k < K) (hk' : k' < K)
    (h : k' + K * (D - 1 - j') = k + K * (D - 1 - j)) : j' = j ∧ k' = k := by
  have hK : 0 < K := by omega
  have hkk : k' = k := by
    have e1 : (k' + K * (D - 1 - j')) % K = k' := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk']
    have e2 : (k + K * (D - 1 - j)) % K = k := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
    rw [← e1, ← e2, h]
  subst hkk
  have h3 : K * (D - 1 - j') = K * (D - 1 - j) := by omega
  have h4 := Nat.eq_of_mul_eq_mul_left hK h3
  exact ⟨by omega, rfl⟩

theorem addr_fst_val (hA : 0 < A) (hS : 0 < S) (i : ℕ) :
    (layerAddrOfIndex A K D S hA hS i).1.val = i / S / 2 ^ (K * D) % A := by
  show i / (2 ^ (K * D) * S) % A = _
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm S]

theorem addr_snd_val (hA : 0 < A) (hS : 0 < S) (i : ℕ) :
    (layerAddrOfIndex A K D S hA hS i).2.2.val = i % S := rfl

theorem addr_bit (hA : 0 < A) (hS : 0 < S) (i : ℕ) (j : Fin D) (k : Fin K) :
    (layerAddrOfIndex A K D S hA hS i).2.1 j k =
      (i / S).testBit (k.val + K * (D - 1 - j.val)) := by
  simp only [layerAddrOfIndex, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, k.isLt,
    decide_true, Bool.true_and, pos_lt j.isLt k.isLt]

/-- Record weight of the selected bit `ρ` of chunk `j` in the lexicographic order. -/
def wSel (K D S ρ j : ℕ) : ℕ := S * 2 ^ (ρ + K * (D - 1 - j))

theorem div_block (hS : 0 < S) (p β m : ℕ) (hm : m < S * 2 ^ p) :
    (2 * (S * 2 ^ p) * β + m) / S = 2 ^ (p + 1) * β + m / S ∧
      (2 * (S * 2 ^ p) * β + m + S * 2 ^ p) / S = 2 ^ (p + 1) * β + (2 ^ p + m / S) ∧
      m / S < 2 ^ p := by
  refine ⟨?_, ?_, Nat.div_lt_of_lt_mul hm⟩
  · rw [show 2 * (S * 2 ^ p) * β + m = S * (2 ^ (p + 1) * β) + m by ring, Nat.mul_add_div hS]
  · rw [show 2 * (S * 2 ^ p) * β + m + S * 2 ^ p = S * (2 ^ (p + 1) * β + 2 ^ p) + m by ring,
      Nat.mul_add_div hS, Nat.add_assoc]

theorem mod_block (p β m : ℕ) :
    (2 * (S * 2 ^ p) * β + m) % S = m % S ∧ (2 * (S * 2 ^ p) * β + m + S * 2 ^ p) % S = m % S := by
  refine ⟨?_, ?_⟩
  · rw [show 2 * (S * 2 ^ p) * β + m = m + S * (2 * 2 ^ p * β) by ring, Nat.add_mul_mod_self_left]
  · rw [show 2 * (S * 2 ^ p) * β + m + S * 2 ^ p = m + S * (2 * 2 ^ p * β + 2 ^ p) by ring,
      Nat.add_mul_mod_self_left]

/-- Bits of `2^(p+1)·β + μ` with `μ < 2^(p+1)`. -/
theorem testBit_blk (p β μ q : ℕ) (hμ : μ < 2 ^ (p + 1)) :
    (2 ^ (p + 1) * β + μ).testBit q = if q < p + 1 then μ.testBit q else β.testBit (q - (p + 1)) :=
  Nat.testBit_two_pow_mul_add β hμ q

/-- **The partner record.** In the block decomposition `i = 2Wβ + m`, `m < W`, the address of
record `i + W` is the address of record `i` with the selected bit `ρ` of chunk `j` flipped, and that
bit of record `i` is `0`. -/
theorem addr_add_wSel (hA : 0 < A) (hS : 0 < S) (ρ : Fin K) (j : Fin D) (β m : ℕ)
    (hm : m < wSel K D S ρ j) :
    layerAddrOfIndex A K D S hA hS (2 * wSel K D S ρ j * β + m + wSel K D S ρ j) =
        flipSel ρ j (layerAddrOfIndex A K D S hA hS (2 * wSel K D S ρ j * β + m)) ∧
      (layerAddrOfIndex A K D S hA hS (2 * wSel K D S ρ j * β + m)).2.1 j ρ = false := by
  obtain ⟨p, hp⟩ : ∃ p, p = ρ.val + K * (D - 1 - j.val) := ⟨_, rfl⟩
  have hW : wSel K D S ρ j = S * 2 ^ p := by rw [hp]; rfl
  rw [hW] at hm ⊢
  obtain ⟨hn, hn', hμ⟩ := div_block hS p β m hm
  obtain ⟨hr, hr'⟩ := mod_block (S := S) p β m
  have hpK : p < K * D := hp ▸ pos_lt j.isLt ρ.isLt
  have hμ1 : m / S < 2 ^ (p + 1) := lt_of_lt_of_le hμ (Nat.pow_le_pow_right two_pos (Nat.le_succ p))
  have hμ2 : 2 ^ p + m / S < 2 ^ (p + 1) := by rw [pow_succ]; omega
  have hμp : (m / S).testBit p = false := Nat.testBit_lt_two_pow hμ
  have bitn : ∀ q, ((2 * (S * 2 ^ p) * β + m) / S).testBit q =
      if q < p + 1 then (m / S).testBit q else β.testBit (q - (p + 1)) := fun q => by
    rw [hn]; exact testBit_blk p β (m / S) q hμ1
  have bitn' : ∀ q, ((2 * (S * 2 ^ p) * β + m + S * 2 ^ p) / S).testBit q =
      if q < p + 1 then (2 ^ p + m / S).testBit q else β.testBit (q - (p + 1)) := fun q => by
    rw [hn']; exact testBit_blk p β (2 ^ p + m / S) q hμ2
  refine ⟨Prod.ext ?_ (Prod.ext ?_ ?_), ?_⟩
  · apply Fin.ext
    show (layerAddrOfIndex A K D S hA hS (2 * (S * 2 ^ p) * β + m + S * 2 ^ p)).1.val =
      (layerAddrOfIndex A K D S hA hS (2 * (S * 2 ^ p) * β + m)).1.val
    rw [addr_fst_val, addr_fst_val]
    congr 1
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, bitn, bitn', if_neg (by omega),
      if_neg (by omega)]
  · funext j' k'
    simp only [flipSel_bit, addr_bit, bitn, bitn', ← hp]
    by_cases hq : k'.val + K * (D - 1 - j'.val) = p
    · obtain ⟨h1, h2⟩ := pos_inj j.isLt j'.isLt ρ.isLt k'.isLt (hq.trans hp)
      have hj' : j' = j := Fin.ext h1
      have hk' : k' = ρ := Fin.ext h2
      subst hj' hk'
      simp only [hq, and_self, if_true, Nat.lt_succ_self,
        Nat.testBit_two_pow_add_eq, hμp]
    · have hne : ¬ (j' = j ∧ k' = ρ) := fun h => hq (by rw [h.1, h.2, hp])
      simp only [hne, if_false]
      by_cases hlt : k'.val + K * (D - 1 - j'.val) < p
      · simp only [show k'.val + K * (D - 1 - j'.val) < p + 1 by omega, if_true,
          Nat.testBit_two_pow_add_gt hlt]
      · simp only [show ¬ (k'.val + K * (D - 1 - j'.val) < p + 1) by omega, if_false]
  · apply Fin.ext
    show (2 * (S * 2 ^ p) * β + m + S * 2 ^ p) % S = (2 * (S * 2 ^ p) * β + m) % S
    rw [hr, hr']
  · rw [addr_bit, ← hp, bitn, if_pos (Nat.lt_succ_self p)]
    exact hμp

end Addr

/-! ## One kernel on the stored records: `cgateBlock` blockwise -/

section Blocks

variable {A K D S r : ℕ}

theorem flipSel_flipSel (ρ : Fin K) (j : Fin D) (x : LayerAddr A K D S) :
    flipSel ρ j (flipSel ρ j x) = x := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext j' t'
  rw [flipSel_bit, flipSel_bit, flipSel_bit]
  by_cases h : j' = j ∧ t' = ρ
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

/-- Stored record of the address `x` at precision `F`. -/
noncomputable def recAt (F : ℕ) (z : RArr (LayerAddr A K D S) r) (x : LayerAddr A K D S) :
    List CInt :=
  (List.finRange r).map fun k => gridInt F (z x k)

theorem length_recAt (F : ℕ) (z : RArr (LayerAddr A K D S) r) (x : LayerAddr A K D S) :
    (recAt F z x).length = r := by
  simp [recAt]

theorem encArr_layerAddrs (F : ℕ) (hA : 0 < A) (hS : 0 < S) (z : RArr (LayerAddr A K D S) r) :
    encArr F (layerAddrs A K D S hA hS) z =
      (List.range (A * 2 ^ (K * D) * S)).map
        fun i => recAt F z (layerAddrOfIndex A K D S hA hS i) := by
  simp [encArr, layerAddrs, recAt, Function.comp_def]

/-- Number of blocks of `2W` records. -/
def nBlk (A K D ρ j : ℕ) : ℕ := A * 2 ^ (K * D - (ρ + K * (D - 1 - j)) - 1)

theorem nBlk_mul {ρ j : ℕ} (hρ : ρ < K) (hj : j < D) :
    nBlk A K D ρ j * (2 * wSel K D S ρ j) = A * 2 ^ (K * D) * S := by
  have hp := pos_lt hj hρ
  obtain ⟨t, ht⟩ : ∃ t, K * D = ρ + K * (D - 1 - j) + 1 + t :=
    ⟨K * D - (ρ + K * (D - 1 - j)) - 1, by omega⟩
  unfold nBlk wSel
  rw [ht, show ρ + K * (D - 1 - j) + 1 + t - (ρ + K * (D - 1 - j)) - 1 = t by omega]
  ring

/-- The stored records of `z` in blocks of `2W` consecutive records (`W = wSel K D S ρ j`). -/
noncomputable def recBlocks (F : ℕ) (hA : 0 < A) (hS : 0 < S) (ρ j : ℕ)
    (z : RArr (LayerAddr A K D S) r) : List (List (List CInt)) :=
  (List.range (nBlk A K D ρ j)).map fun β => (List.range (2 * wSel K D S ρ j)).map fun m =>
    recAt F z (layerAddrOfIndex A K D S hA hS (2 * wSel K D S ρ j * β + m))

theorem flatten_range_blocks {α : Type*} (f : ℕ → α) (c : ℕ) : ∀ nb : ℕ,
    ((List.range nb).map fun β => (List.range c).map fun m => f (c * β + m)).flatten =
      (List.range (nb * c)).map f
  | 0 => by simp
  | nb + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, flatten_range_blocks f c nb,
      Nat.succ_mul, List.range_add, List.map_append, List.map_map]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    congr 1
    refine List.map_congr_left fun m _ => ?_
    simp only [Function.comp, Nat.mul_comm c nb]

theorem recBlocks_flatten (F : ℕ) (hA : 0 < A) (hS : 0 < S) (ρ : Fin K) (j : Fin D)
    (z : RArr (LayerAddr A K D S) r) :
    (recBlocks F hA hS ρ j z).flatten = encArr F (layerAddrs A K D S hA hS) z := by
  rw [recBlocks, flatten_range_blocks (fun i => recAt F z (layerAddrOfIndex A K D S hA hS i)),
    nBlk_mul ρ.isLt j.isLt, encArr_layerAddrs]

end Blocks

section BlockGate

variable {A K D S r : ℕ}

theorem range_two_mul (W : ℕ) :
    List.range (2 * W) = List.range W ++ (List.range W).map (W + ·) := by
  rw [two_mul, List.range_add]

theorem take_drop_halves {α : Type*} (W : ℕ) (g g' : ℕ → α) :
    ((List.range W).map g ++ (List.range W).map g').take W = (List.range W).map g ∧
      ((List.range W).map g ++ (List.range W).map g').drop W = (List.range W).map g' :=
  ⟨List.take_left' (by simp), List.drop_left' (by simp)⟩

/-- First output of the kernel on one record pair. -/
theorem zipWith_cgate0_recAt {G : ℕ} (z : RArr (LayerAddr A K D S) r)
    (hz : ∀ x k, OnGrid G (z x k)) (ρ : Fin K) (j : Fin D) (x : LayerAddr A K D S) :
    List.zipWith cgate0 (recAt (G + 1) z x) (recAt (G + 1) z (flipSel ρ j x)) =
      recAt (G + 1) (gateR ρ j (topC A K D S) z) x := by
  simp only [recAt, List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun k _ => ?_
  rw [gateR_topC_apply, gridInt_gate0 (hz x k) (hz _ k)]

/-- Second output of the kernel on one record pair. -/
theorem zipWith_cgate1_recAt {G : ℕ} (z : RArr (LayerAddr A K D S) r)
    (hz : ∀ x k, OnGrid G (z x k)) (ρ : Fin K) (j : Fin D) (x : LayerAddr A K D S) :
    List.zipWith cgate1 (recAt (G + 1) z x) (recAt (G + 1) z (flipSel ρ j x)) =
      recAt (G + 1) (gateR ρ j (topC A K D S) z) (flipSel ρ j x) := by
  simp only [recAt, List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun k _ => ?_
  rw [gateR_topC_apply, flipSel_flipSel, add_comm (ka * _), gridInt_gate1 (hz x k) (hz _ k)]

/-- **One block.** `cgateBlock W` on the block `β` of the stored records of `z` is the block `β`
of the stored records of one kernel applied to `z`. -/
theorem cgateBlock_block {G : ℕ} (hA : 0 < A) (hS : 0 < S) (ρ : Fin K) (j : Fin D)
    (z : RArr (LayerAddr A K D S) r) (hz : ∀ x k, OnGrid G (z x k)) (β : ℕ) :
    cgateBlock (wSel K D S ρ j) ((List.range (2 * wSel K D S ρ j)).map fun m =>
        recAt (G + 1) z (layerAddrOfIndex A K D S hA hS (2 * wSel K D S ρ j * β + m))) =
      (List.range (2 * wSel K D S ρ j)).map fun m =>
        recAt (G + 1) (gateR ρ j (topC A K D S) z)
          (layerAddrOfIndex A K D S hA hS (2 * wSel K D S ρ j * β + m)) := by
  have hpart : ∀ m < wSel K D S ρ j,
      layerAddrOfIndex A K D S hA hS (2 * wSel K D S ρ j * β + (wSel K D S ρ j + m)) =
        flipSel ρ j (layerAddrOfIndex A K D S hA hS (2 * wSel K D S ρ j * β + m)) :=
    fun m hm => by
      rw [show 2 * wSel K D S ρ j * β + (wSel K D S ρ j + m) =
        2 * wSel K D S ρ j * β + m + wSel K D S ρ j by ring]
      exact (addr_add_wSel hA hS ρ j β m hm).1
  rw [range_two_mul, List.map_append, List.map_append, List.map_map, List.map_map]
  unfold cgateBlock
  rw [(take_drop_halves _ _ _).1, (take_drop_halves _ _ _).2, List.zipWith_map, List.zipWith_map,
    List.zipWith_self, List.zipWith_self]
  congr 1
  · refine List.map_congr_left fun m hm => ?_
    simp only [Function.comp_apply]
    rw [hpart m (List.mem_range.1 hm), zipWith_cgate0_recAt z hz]
  · refine List.map_congr_left fun m hm => ?_
    simp only [Function.comp_apply]
    rw [hpart m (List.mem_range.1 hm), zipWith_cgate1_recAt z hz]

theorem recBlocks_gate {G : ℕ} (hA : 0 < A) (hS : 0 < S) (ρ : Fin K) (j : Fin D)
    (z : RArr (LayerAddr A K D S) r) (hz : ∀ x k, OnGrid G (z x k)) :
    (recBlocks (G + 1) hA hS ρ j z).map (cgateBlock (wSel K D S ρ j)) =
      recBlocks (G + 1) hA hS ρ j (gateR ρ j (topC A K D S) z) := by
  unfold recBlocks
  rw [List.map_map]
  exact List.map_congr_left fun β _ => cgateBlock_block hA hS ρ j z hz β

theorem getD_map_range_length {n i : ℕ} (f : ℕ → List CInt) (hf : ∀ m, (f m).length = r)
    (hi : i < n) : (((List.range n).map f).getD i []).length = r := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [hf]

theorem recBlocks_ok (F : ℕ) (hA : 0 < A) (hS : 0 < S) (ρ j : ℕ)
    (z : RArr (LayerAddr A K D S) r) :
    ∀ blk ∈ recBlocks F hA hS ρ j z, CGateBlockOK (wSel K D S ρ j) blk := by
  intro blk hblk
  obtain ⟨β, -, rfl⟩ := List.mem_map.1 hblk
  refine ⟨by simp, fun i hi => ?_⟩
  rw [getD_map_range_length _ (fun m => length_recAt F z _) (by omega),
    getD_map_range_length _ (fun m => length_recAt F z _) (by omega)]

end BlockGate

/-! ## Stored numerators fit the guarded width -/

section Fits

variable {A K D S r : ℕ}

theorem fitsTwos_of_abs {w : ℕ} {a : ℤ} (h : |a| < 2 ^ (w - 1)) : FitsTwos w a := by
  refine ⟨?_, lt_of_le_of_lt (le_abs_self a) h⟩
  have := neg_abs_le a
  linarith

theorem fits_gridInt {P Δ b : ℕ} (hb : b ≤ Δ) {z : ℂ} (hg : OnGrid (P + b) z)
    (hn : ‖z‖ ≤ 2 ^ b) :
    FitsTwos (P + 2 * Δ + 3) (gridInt (P + Δ) z).1 ∧
      FitsTwos (P + 2 * Δ + 3) (gridInt (P + Δ) z).2 := by
  obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := hg.mono (show P + b ≤ P + Δ by omega)
  rw [gridInt_of_re_im ha hc]
  have key : ∀ (a : ℤ) (x : ℝ), x = a * gridUnit (P + Δ) → |x| ≤ 2 ^ b →
      FitsTwos (P + 2 * Δ + 3) a := by
    intro a x hx hxb
    have h1 : |(a : ℝ)| ≤ 2 ^ b * 2 ^ (P + Δ) := by
      have e : |(a : ℝ)| = |x| * 2 ^ (P + Δ) := by
        rw [hx, abs_mul, abs_of_pos (gridUnit_pos _), mul_assoc, gridUnit_mul_two_pow_self,
          mul_one]
      rw [e]
      exact mul_le_mul_of_nonneg_right hxb (by positivity)
    have h2 : (2 : ℝ) ^ b * 2 ^ (P + Δ) < 2 ^ (P + 2 * Δ + 3 - 1) := by
      rw [← pow_add]
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    have h4 : |a| < 2 ^ (P + 2 * Δ + 3 - 1) := by
      have h3 : |(a : ℝ)| < 2 ^ (P + 2 * Δ + 3 - 1) := lt_of_le_of_lt h1 h2
      exact_mod_cast h3
    exact fitsTwos_of_abs h4
  exact ⟨key a z.re ha (le_trans (Complex.abs_re_le_norm z) hn),
    key c z.im hc (le_trans (Complex.abs_im_le_norm z) hn)⟩

/-- **The stored array fits `w_g = P + 2Δ + 3` bits** when the growth bound is at most `Δ`. -/
theorem encArr_fits {P Δ b : ℕ} (hb : b ≤ Δ) (hA : 0 < A) (hS : 0 < S)
    (z : RArr (LayerAddr A K D S) r) (hz : ArrGrowth P b z) :
    CArrFits (P + 2 * Δ + 3) (encArr (P + Δ) (layerAddrs A K D S hA hS) z) := by
  intro cs hcs c hc
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hcs
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc
  exact fits_gridInt hb (hz x k).1 (hz x k).2

end Fits

end SubNLogN.Machine.CCore.LeafKernelAux
