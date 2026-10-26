/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelMathDefs

/-!
# C-core skeleton, math leaf (M4): the bands are inherited by every child context

Proof of `ChildBandsStmt p` (`CCore/SkelMathDefs.lean`): if a call `t` of depth `k + 1` satisfies
the bands `CCoreBands p P₀ t`, then every child context `childRT t k a b'` satisfies the bands at
the **same** cutoff `P₀`, for every `p` (the admissibility `p.OK` is not needed). The child context
divides `A` and `R` by `W = W_c`, lowers the depth to `k`, moves `j0` to the slot `a`, and keeps every
other descriptor field:
* `A/W ≥ 1`: `A` is a positive multiple of `R`, which is a positive multiple of `W^(k+1)`;
* `R/W ∣ A/W` and `W^k ∣ R/W`: write `R = W·W^k·q`, `A = R·q'`;
* `j0 + a·m^k + m^k ≤ j0 + m^(k+1) ≤ D` since `a < m`;
* `log₂ M' ≤ log₂ M` since `0 < M' ≤ M` (`M' = (A/W)·S·2^(KD)`).
-/

namespace SubNLogN.Machine.CCore

open SubNLogN.Math.Networks

namespace M4Aux

theorem Wn_pos : 0 < Wn := by
  norm_num [Wn, tripleWc, tripleN, tripleV, tripleI, tripleZc]

end M4Aux

/-- **(M4) The bands are inherited by every child context**, at the same cutoff. -/
theorem childBands_holds (p : LayerParams) : ChildBandsStmt p := by
  intro P₀ t k a b' hB hk
  obtain ⟨hP, hd1, hd2, hr1, hr2, hK, hΔ, hA, hS, hRA, hWR, hj, hρ, hM⟩ := hB
  have hW : 0 < Wn := M4Aux.Wn_pos
  have hWR' : Wn ^ (k + 1) ∣ t.R := by rw [← hk]; exact hWR
  obtain ⟨q, hq⟩ := hWR'
  obtain ⟨q', hq'⟩ := hRA
  have hq'pos : 0 < q' := by
    rcases Nat.eq_zero_or_pos q' with h | h
    · rw [h, mul_zero] at hq'; omega
    · exact h
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero] at hq; rw [hq, zero_mul] at hq'; omega
    · exact h
  have hR' : t.R = Wn * (Wn ^ k * q) := by rw [hq, pow_succ]; ring
  have hA' : t.A = Wn * (Wn ^ k * q * q') := by rw [hq', hR']; ring
  have hRdiv : t.R / Wn = Wn ^ k * q := by rw [hR', Nat.mul_div_cancel_left _ hW]
  have hAdiv : t.A / Wn = Wn ^ k * q * q' := by rw [hA', Nat.mul_div_cancel_left _ hW]
  have hApos : 0 < t.A / Wn := by
    rw [hAdiv]; exact Nat.mul_pos (Nat.mul_pos (pow_pos hW k) hqpos) hq'pos
  have he : t.e = mn ^ k * mn := by
    show tripleM 100 ^ t.k = mn ^ k * mn
    rw [hk, pow_succ]
  have hMle : (childRT t k a b').M ≤ t.M := by
    show t.A / Wn * t.S * 2 ^ (t.K * t.D) ≤ t.A * t.S * 2 ^ (t.K * t.D)
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.div_le_self _ _))
  have hMpos : 0 < (childRT t k a b').M := by
    show 0 < t.A / Wn * t.S * 2 ^ (t.K * t.D)
    exact Nat.mul_pos (Nat.mul_pos hApos hS) (pow_pos (by norm_num) _)
  refine ⟨hP, hd1, hd2, hr1, hr2, hK, hΔ, ?_, hS, ?_, ?_, ?_, hρ, ?_⟩
  · show 1 ≤ t.A / Wn
    exact hApos
  · show t.R / Wn ∣ t.A / Wn
    rw [hRdiv, hAdiv]
    exact Dvd.intro q' rfl
  · show Wn ^ k ∣ t.R / Wn
    rw [hRdiv]
    exact Dvd.intro q rfl
  · show t.j0 + a.val * mn ^ k + mn ^ k ≤ t.D
    have h1 : (a.val + 1) * mn ^ k ≤ mn * mn ^ k := Nat.mul_le_mul_right _ a.isLt
    have h2 : (a.val + 1) * mn ^ k = a.val * mn ^ k + mn ^ k := by ring
    have h3 : mn * mn ^ k = mn ^ k * mn := by ring
    rw [he] at hj
    omega
  · calc Real.logb 2 ((childRT t k a b').M : ℝ) ≤ Real.logb 2 (t.M : ℝ) :=
          Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hMpos) (by exact_mod_cast hMle)
      _ ≤ p.C_M * t.P := hM

/-! ## Node and leaf premises (for `CCore/SkelNode.lean`)

Exported helper names: (a) `node_k_pos`, (b) `node_W_dvd`, (c) `K_ge_six`,
(d) `leaf_cDepth`, (e) `node_cDepth`, (f) `childRT_volG`, `compactRT_volG`, (g) `childRT_e`,
`childRT_j0_e`, (h) `bands_mono`; plus `bands_basic`. `W = Wn` and `m = mn` are never computed
(only `0 < W`, `M4Aux.Wn_pos`, is used). -/

/-- **(a)** Not a leaf (the header-test flag is false) implies depth `≥ 1`. -/
theorem node_k_pos {βn βd : ℕ} (t : CCoreRT) (h : ¬ (t.k = 0 ∨ (mn ^ t.k) ^ βd < t.d ^ βn)) :
    1 ≤ t.k := by
  push_neg at h
  omega

/-- **(b)** At a node (`1 ≤ k`) in the bands: `W ∣ A`, `0 < A / W` and `W^k ∣ A` (premises of
`Split`, `Collect`, `Phase`, `RowAdd`, `ScalarRow`). -/
theorem node_W_dvd {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (hB : CCoreBands p P₀ t)
    (hk : 1 ≤ t.k) : Wn ∣ t.A ∧ 0 < t.A / Wn ∧ Wn ^ t.k ∣ t.A := by
  obtain ⟨-, -, -, -, -, -, -, hA, -, hRA, hWR, -⟩ := hB
  have hW : 0 < Wn := M4Aux.Wn_pos
  have hdvd : Wn ∣ t.A :=
    ((dvd_pow_self Wn (by omega : t.k ≠ 0)).trans hWR).trans hRA
  exact ⟨hdvd, Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hW, hWR.trans hRA⟩

/-- **(c)** For admissible constants there is a cutoff above which every call in the bands has
`6 ≤ K` (premise of the Lemma A.9 row addition and of `NodeValueStmt`): `K = ⌊d^c⌋₊` and
`d ≥ a_d P^ε`. -/
theorem K_ge_six {p : LayerParams} (hp : p.OK) :
    ∃ P₁ : ℕ, ∀ P₀ ≥ P₁, ∀ t : CCoreRT, CCoreBands p P₀ t → 6 ≤ t.K := by
  obtain ⟨-, -, -, -, -, -, -, -, hc, hε, -, -, -, -, -, -, -, -, had, -⟩ := hp
  set X : ℝ := (6 : ℝ) ^ p.c⁻¹ / p.a_d with hXdef
  have hX0 : 0 ≤ X := div_nonneg (Real.rpow_nonneg (by norm_num) _) had.le
  refine ⟨⌈X ^ p.ε⁻¹⌉₊, fun P₀ hP₁ t hB => ?_⟩
  obtain ⟨hP, hd1, -, -, -, hK, -⟩ := hB
  have hP' : (⌈X ^ p.ε⁻¹⌉₊ : ℝ) ≤ (t.P : ℝ) := by exact_mod_cast hP₁.trans hP
  have h1 : X ^ p.ε⁻¹ ≤ (t.P : ℝ) := (Nat.le_ceil _).trans hP'
  have h2 : X ≤ (t.P : ℝ) ^ p.ε := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) h1 hε.le
    rwa [Real.rpow_inv_rpow hX0 hε.ne'] at this
  have h3 : (6 : ℝ) ^ p.c⁻¹ ≤ (t.d : ℝ) := by
    have h4 : (6 : ℝ) ^ p.c⁻¹ = p.a_d * X := by
      rw [hXdef]; field_simp
    rw [h4]
    exact (mul_le_mul_of_nonneg_left h2 had.le).trans hd1
  have h5 : (6 : ℝ) ≤ (t.d : ℝ) ^ p.c := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h3 hc.le
    rwa [Real.rpow_inv_rpow (by norm_num) hc.ne'] at this
  rw [hK]
  exact Nat.le_floor (by exact_mod_cast h5)

/-- **(d)** At a leaf (flag true) the depth bound is `8e`. -/
theorem leaf_cDepth {βn βd E : ℕ} (t : CCoreRT) (h : t.k = 0 ∨ (mn ^ t.k) ^ βd < t.d ^ βn) :
    cDepth t.d βn βd E t.k = 8 * t.e := by
  rcases Nat.eq_zero_or_pos t.k with hk | hk
  · simp [cDepth, CCoreRT.e, hk]
  · obtain ⟨k, hk'⟩ : ∃ k, t.k = k + 1 := ⟨t.k - 1, by omega⟩
    have h' : (mn ^ (k + 1)) ^ βd < t.d ^ βn := by
      rcases h with h | h
      · omega
      · rwa [hk'] at h
    have he : t.e = mn ^ (k + 1) := by show tripleM 100 ^ t.k = _; rw [hk']
    rw [hk', he]
    simp only [cDepth]
    rw [if_pos h']

/-- **(e)** At a node (flag false, `t.k = k + 1`) the depth bound unfolds to `s·A(k) + E`. -/
theorem node_cDepth {βn βd E k : ℕ} (t : CCoreRT) (h : ¬ (t.k = 0 ∨ (mn ^ t.k) ^ βd < t.d ^ βn))
    (hk : t.k = k + 1) :
    cDepth t.d βn βd E (k + 1) = sn * cDepth t.d βn βd E k + E := by
  push_neg at h
  have h' : ¬ (mn ^ (k + 1)) ^ βd < t.d ^ βn := by
    rw [← hk]; exact not_lt.2 h.2
  simp only [cDepth]
  rw [if_neg h']

/-- **(f)** At a node in the bands, `W ∣ V_g` and a child context has volume `V_g / W`. -/
theorem childRT_volG {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} {k : ℕ} (a : Fin mn) (b' : ℕ)
    (hB : CCoreBands p P₀ t) (hk : t.k = k + 1) :
    Wn ∣ t.volG ∧ (childRT t k a b').volG = t.volG / Wn := by
  obtain ⟨hdvd, -, -⟩ := node_W_dvd hB (by omega)
  obtain ⟨A₁, hA₁⟩ := hdvd
  have hW : 0 < Wn := M4Aux.Wn_pos
  have hv : t.volG = Wn * (2 * (A₁ * t.S * 2 ^ (t.K * t.D)) * t.r * t.wg) := by
    show 2 * (t.A * t.S * 2 ^ (t.K * t.D)) * t.r * t.wg = _
    rw [hA₁]; ring
  refine ⟨⟨_, hv⟩, ?_⟩
  show 2 * (t.A / Wn * t.S * 2 ^ (t.K * t.D)) * t.r * t.wg = t.volG / Wn
  rw [hv, Nat.mul_div_cancel_left _ hW, hA₁, Nat.mul_div_cancel_left _ hW]

/-- **(f')** At a node in the bands, the compact (role-stream) context has volume `V_g / W`. -/
theorem compactRT_volG {p : LayerParams} {P₀ : ℕ} {t : CCoreRT}
    (hB : CCoreBands p P₀ t) (hk : 1 ≤ t.k) :
    Wn ∣ t.volG ∧ (compactRT t).volG = t.volG / Wn := by
  obtain ⟨hdvd, -, -⟩ := node_W_dvd hB hk
  obtain ⟨A₁, hA₁⟩ := hdvd
  have hW : 0 < Wn := M4Aux.Wn_pos
  have hv : t.volG = Wn * (2 * (A₁ * t.S * 2 ^ (t.K * t.D)) * t.r * t.wg) := by
    show 2 * (t.A * t.S * 2 ^ (t.K * t.D)) * t.r * t.wg = _
    rw [hA₁]; ring
  refine ⟨⟨_, hv⟩, ?_⟩
  show 2 * (t.A / Wn * t.S * 2 ^ (t.K * t.D)) * t.r * t.wg = t.volG / Wn
  rw [hv, Nat.mul_div_cancel_left _ hW, hA₁, Nat.mul_div_cancel_left _ hW]

/-- **(g)** The group size of a child context. -/
theorem childRT_e (t : CCoreRT) (k : ℕ) (a : Fin mn) (b' : ℕ) : (childRT t k a b').e = mn ^ k :=
  rfl

/-- **(g')** Every child group fits in the parent's chunk range. -/
theorem childRT_j0_e {t : CCoreRT} {k : ℕ} (hk : t.k = k + 1) (hj : t.j0 + t.e ≤ t.D) :
    ∀ (a : Fin mn) (b' : ℕ), (childRT t k a b').j0 + (childRT t k a b').e ≤ t.D := by
  intro a b'
  show t.j0 + a.val * mn ^ k + mn ^ k ≤ t.D
  have he : t.e = mn ^ k * mn := by show tripleM 100 ^ t.k = _; rw [hk, pow_succ]
  have h1 : (a.val + 1) * mn ^ k ≤ mn * mn ^ k := Nat.mul_le_mul_right _ a.isLt
  have h2 : (a.val + 1) * mn ^ k = a.val * mn ^ k + mn ^ k := by ring
  have h3 : mn * mn ^ k = mn ^ k * mn := by ring
  rw [he] at hj
  omega

/-- **(h)** The bands are monotone in the cutoff. -/
theorem bands_mono {p : LayerParams} {P₀ P₁ : ℕ} {t : CCoreRT} (h : P₀ ≤ P₁)
    (hB : CCoreBands p P₁ t) : CCoreBands p P₀ t :=
  ⟨h.trans hB.1, hB.2⟩

/-- The bands give the remaining premises of the leaf kernel (`LeafStmt`) and of `CCoreStmt`:
`0 < A`, `0 < S`, `ρ < K`, `j0 + e ≤ D`. -/
theorem bands_basic {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (hB : CCoreBands p P₀ t) :
    0 < t.A ∧ 0 < t.S ∧ t.ρ < t.K ∧ t.j0 + t.e ≤ t.D := by
  obtain ⟨-, -, -, -, -, -, -, hA, hS, -, -, hj, hρ, -⟩ := hB
  exact ⟨hA, hS, hρ, hj⟩

end SubNLogN.Machine.CCore
