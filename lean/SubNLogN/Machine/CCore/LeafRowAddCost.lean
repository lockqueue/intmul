/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs
import SubNLogN.Machine.Contracts.AppC
import SubNLogN.Machine.CCore.LeafRowAddCostAsym

/-!
# C-core leaf 9 (Lemma A.9 row addition): cost absorption (`CCore/LeafRowAddCost.lean`)

Cost part of `RowAddStmt` (`CCore/SkelDefs.lean`), for the reduction to
`C7PackedXorStmt` (`Contracts/AppC.lean`; `c7` is the earlier-draft prefix for Lemma A.9).
Paper: Lemma A.9 (`lem:transfer13`), eq. (`eq:transfer-packed`), where the extra terms are absorbed
into `O(V(L^τ+1))` once `(A+1)^3 ≤ R` and `160(f-1)(A+1) ≤ 2^K` in the layer bands (Section A.6).

## Proved here (complete), for admissible constants `p.OK` and calls `t` in the bands
* `hdr_bounds`: `K·D, D, K ≤ c(P+1)` and `A, S, r, d ≤ 2^(c(P+1))`.
* `poly_absorb`: every polynomial `c (P+1)^n` is at most `V_g` above a cutoff.
* `c7Cost_absorb`: the Lemma A.9 cost of one row addition on a compact role stream (`M` records of
  width `R = 2 r w_g`, `f = m^(k-1)`) is at most `4 · V_g · (Uτ(eK) + 1)`.

Route. From the bands: `d ≥ 1`, `r ≥ 1`, `M ≤ 2^(⌈C_M⌉ P)`, `K·D ≤ ⌈C_M⌉ P`, `r ≤ 2^(⌈b_r⌉ P)`,
so `lgVol V ≤ c₁ (P+1)`. Since `r ≥ 2^((a_r/b_d) P^(1-ε))` and `2^K ≥ 2^(a_d^c P^(εc))/2`
beat every polynomial in `P` (`poly_le_two_rpow`), above a cutoff `(lgVol V + 1)^3 ≤ r` and
`160 f lgVol V ≤ 2^K`. Then the three terms of `c7Cost` are at most `2 V_g (U+1)`, `V_g` and
`V_g` (`c7_combine`, pure ℕ arithmetic over variables). No closed arithmetic over `W_c` or
`m` is evaluated (`Wn` enters only through `Nat.div_le_self`).
-/

namespace SubNLogN.Machine.CCore.LeafRowAddCostAux

open SubNLogN.Machine

/-! ## 1. Constants and the admissibility facts used -/

/-- `⌈C_M⌉`. -/
noncomputable def cM (p : LayerParams) : ℕ := ⌈p.C_M⌉₊

/-- `⌈b_r⌉`. -/
noncomputable def cR (p : LayerParams) : ℕ := ⌈p.b_r⌉₊

/-- `⌈b_d⌉`. -/
noncomputable def cD (p : LayerParams) : ℕ := ⌈p.b_d⌉₊

/-- The constant of the `lgVol` bound. -/
noncomputable def c1 (p : LayerParams) : ℕ := cM p + cR p + 6

theorem le_cM (p : LayerParams) : p.C_M ≤ (cM p : ℝ) := Nat.le_ceil _

theorem le_cR (p : LayerParams) : p.b_r ≤ (cR p : ℝ) := Nat.le_ceil _

theorem le_cD (p : LayerParams) : p.b_d ≤ (cD p : ℝ) := Nat.le_ceil _

/-- The admissibility facts used here. -/
theorem ok_facts {p : LayerParams} (hp : p.OK) :
    0 < p.τ ∧ 0 < p.c ∧ 0 < p.ε ∧ p.ε < 1 ∧ 0 < p.a_d ∧ p.a_d ≤ p.b_d ∧ 0 < p.a_r ∧
      p.a_r ≤ p.b_r ∧ 0 < p.C_M := by
  obtain ⟨h1, -, -, -, -, -, -, -, h9, h10, h11, -, -, -, -, -, -, -, h19, h20, h21, h22, h23,
    -, -⟩ := hp
  exact ⟨h1, h9, h10, h11, h19, h20, h21, h22, h23⟩

/-! ## 2. Consequences of the bands -/

theorem bands_mono {p : LayerParams} {P₀ P₁ : ℕ} {t : CCoreRT} (h : P₀ ≤ P₁)
    (hb : CCoreBands p P₁ t) : CCoreBands p P₀ t := by
  unfold CCoreBands at hb ⊢
  exact ⟨h.trans hb.1, hb.2⟩

/-- Basic positivity facts in the bands (cutoff `P₀ ≥ 1`). -/
theorem bands_basic {p : LayerParams} (hp : p.OK) {P₀ : ℕ} (hP₀ : 1 ≤ P₀) {t : CCoreRT}
    (hb : CCoreBands p P₀ t) :
    1 ≤ t.P ∧ 1 ≤ t.d ∧ 1 ≤ t.r ∧ 1 ≤ t.K ∧ 1 ≤ t.D ∧ 1 ≤ t.A ∧ 1 ≤ t.S ∧ t.Δ ≤ t.P ∧
      t.e ≤ t.D := by
  obtain ⟨-, -, -, -, had, -, har, -, -⟩ := ok_facts hp
  unfold CCoreBands at hb
  obtain ⟨hP, hd1, -, hr1, -, -, hΔ, hA, hS, -, -, hje, hρ, -⟩ := hb
  have hP1 : 1 ≤ t.P := hP₀.trans hP
  have hPr : (0 : ℝ) < t.P := by exact_mod_cast hP1
  have hdpos : (0 : ℝ) < t.d := lt_of_lt_of_le (mul_pos had (Real.rpow_pos_of_pos hPr _)) hd1
  have hd : 1 ≤ t.d := Nat.succ_le_of_lt (Nat.cast_pos.mp hdpos)
  have hr : (1 : ℝ) ≤ t.r := le_trans (Real.one_le_rpow (by norm_num)
    (div_nonneg (mul_nonneg har.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _))) hr1
  have he : 1 ≤ t.e := by
    show 1 ≤ tripleM 100 ^ t.k
    exact Nat.one_le_pow _ _ (by unfold tripleM; positivity)
  refine ⟨hP1, hd, by exact_mod_cast hr, by omega, by omega, hA, hS, hΔ, by omega⟩

/-- Sizes in the bands: `M ≤ 2^(⌈C_M⌉ P)`, `K·D ≤ ⌈C_M⌉ P`, `r ≤ 2^(⌈b_r⌉ P)`, `d ≤ ⌈b_d⌉ P`. -/
theorem bands_size {p : LayerParams} (hp : p.OK) {P₀ : ℕ} (hP₀ : 1 ≤ P₀) {t : CCoreRT}
    (hb : CCoreBands p P₀ t) :
    t.M ≤ 2 ^ (cM p * t.P) ∧ t.K * t.D ≤ cM p * t.P ∧ t.r ≤ 2 ^ (cR p * t.P) ∧
      t.d ≤ cD p * t.P := by
  obtain ⟨hP1, hd1, hr1, hK1, hD1, hA1, hS1, hΔ, heD⟩ := bands_basic hp hP₀ hb
  obtain ⟨-, -, -, hε1, had, hadb, har, harb, -⟩ := ok_facts hp
  unfold CCoreBands at hb
  obtain ⟨-, -, hd2, -, hr2, -, -, -, -, -, -, -, -, hlog⟩ := hb
  have hPr : (1 : ℝ) ≤ t.P := by exact_mod_cast hP1
  have hP0 : (0 : ℝ) ≤ t.P := Nat.cast_nonneg _
  have hcast : ∀ n : ℕ, (2 : ℝ) ^ (n : ℝ) = ((2 ^ n : ℕ) : ℝ) := fun n => by
    rw [Real.rpow_natCast]; push_cast; rfl
  have hMpos' : 0 < t.M := by
    unfold CCoreRT.M
    exact Nat.mul_pos (Nat.mul_pos hA1 hS1) (Nat.two_pow_pos _)
  have hMpos : (0 : ℝ) < t.M := by exact_mod_cast hMpos'
  have hM : t.M ≤ 2 ^ (cM p * t.P) := by
    have h1 : (t.M : ℝ) ≤ (2 : ℝ) ^ (p.C_M * t.P) :=
      (Real.logb_le_iff_le_rpow (by norm_num) hMpos).mp hlog
    have h2 : (2 : ℝ) ^ (p.C_M * t.P) ≤ (2 : ℝ) ^ (((cM p * t.P : ℕ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      exact mul_le_mul_of_nonneg_right (le_cM p) hP0
    have h3 := h1.trans h2
    rw [hcast] at h3
    exact_mod_cast h3
  have hKD : t.K * t.D ≤ cM p * t.P := by
    have h1 : 2 ^ (t.K * t.D) ≤ t.M := by
      unfold CCoreRT.M
      exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hA1 hS1)
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (h1.trans hM)
  have hr : t.r ≤ 2 ^ (cR p * t.P) := by
    have hdr : (1 : ℝ) ≤ t.d := by exact_mod_cast hd1
    have h1 : p.b_r * t.P / t.d ≤ ((cR p * t.P : ℕ) : ℝ) := by
      push_cast
      calc p.b_r * t.P / t.d ≤ p.b_r * t.P :=
            div_le_self (mul_nonneg (har.le.trans harb) hP0) hdr
        _ ≤ (cR p : ℝ) * t.P := mul_le_mul_of_nonneg_right (le_cR p) hP0
    have h2 := hr2.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) h1)
    rw [hcast] at h2
    exact_mod_cast h2
  have hd : t.d ≤ cD p * t.P := by
    have h1 : (t.P : ℝ) ^ p.ε ≤ t.P := by
      calc (t.P : ℝ) ^ p.ε ≤ (t.P : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hPr hε1.le
        _ = t.P := Real.rpow_one _
    have h2 : (t.d : ℝ) ≤ (cD p : ℝ) * t.P :=
      hd2.trans ((mul_le_mul_of_nonneg_left h1 (had.le.trans hadb)).trans
        (mul_le_mul_of_nonneg_right (le_cD p) hP0))
    exact_mod_cast h2
  exact ⟨hM, hKD, hr, hd⟩

/-! ## 3. Pure arithmetic over variables -/

theorem three_mul_add_three_le : ∀ P : ℕ, 3 * P + 3 ≤ 2 ^ (P + 2)
  | 0 => by norm_num
  | P + 1 => by
    have ih := three_mul_add_three_le P
    have h4 : 4 ≤ 2 ^ (P + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (P + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show P + 1 + 2 = (P + 2) + 1 by ring, pow_succ]
    omega

/-- `2V ≤ 2^(a+b+c+3)` for `V = M'(2rw+1)` with `M' ≤ M ≤ 2^a`, `r ≤ 2^b`, `w ≤ 2^c`. -/
theorem two_vol_le (M' M r w a b c : ℕ) (hM' : M' ≤ M) (hM : M ≤ 2 ^ a) (hr : r ≤ 2 ^ b)
    (hw : w ≤ 2 ^ c) (hr1 : 1 ≤ r) (hw1 : 1 ≤ w) :
    2 * (M' * (2 * r * w + 1)) ≤ 2 ^ (a + b + c + 3) := by
  have hrw : 1 ≤ r * w := Nat.mul_le_mul hr1 hw1
  have h1 : 2 * r * w + 1 ≤ 4 * (r * w) := by
    have e : 2 * r * w = 2 * (r * w) := by ring
    omega
  calc 2 * (M' * (2 * r * w + 1)) ≤ 2 * (M * (4 * (r * w))) := by gcongr
    _ = 8 * (M * r * w) := by ring
    _ ≤ 8 * (2 ^ a * 2 ^ b * 2 ^ c) := by gcongr
    _ = 2 ^ (a + b + c + 3) := by rw [pow_add, pow_add, pow_add]; ring

theorem arith_c1 (a b P : ℕ) : a * P + b * P + (P + 2) + 3 ≤ (a + b + 6) * (P + 1) := by
  nlinarith [Nat.zero_le a, Nat.zero_le b, Nat.zero_le P]

/-- The record count of a compact role stream is at most `M`. -/
theorem M'_le_M (t : CCoreRT) : t.A / Wn * 2 ^ (t.K * t.D) * t.S ≤ t.M := by
  unfold CCoreRT.M
  calc t.A / Wn * 2 ^ (t.K * t.D) * t.S ≤ t.A * 2 ^ (t.K * t.D) * t.S :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.div_le_self _ _))
    _ = t.A * t.S * 2 ^ (t.K * t.D) := by ring

/-- **Term 1 of `c7Cost`**: `⌈V((fK)^τ + 1)⌉ ≤ V (Uτ(eK) + 1)` for `f ≤ e`, `τ ≥ 0`. -/
theorem term1_le (τ : ℝ) (hτ : 0 ≤ τ) (V f e K : ℕ) (hfe : f ≤ e) :
    ⌈(V : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1)⌉₊ ≤ V * (Utau τ (e * K) + 1) := by
  have h1 : ((f * K : ℕ) : ℝ) ^ τ ≤ ((e * K : ℕ) : ℝ) ^ τ :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.mul_le_mul_right K hfe)) hτ
  have h2 : ((e * K : ℕ) : ℝ) ^ τ ≤ (Utau τ (e * K) : ℝ) := Nat.le_ceil _
  have e1 : ((V * (Utau τ (e * K) + 1) : ℕ) : ℝ) = (V : ℝ) * ((Utau τ (e * K) : ℝ) + 1) := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have h3 : (V : ℝ) * (((f * K : ℕ) : ℝ) ^ τ + 1) ≤ ((V * (Utau τ (e * K) + 1) : ℕ) : ℝ) := by
    rw [e1]
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg V)
  exact Nat.ceil_le.mpr h3

/-- **Assembly of the three terms of `c7Cost`** (pure ℕ arithmetic over variables). -/
theorem c7_combine (M' M R r w f K L B U T1 : ℕ)
    (hT1 : T1 ≤ M' * (R + 1) * (U + 1)) (hR : R = 2 * r * w) (hR1 : 1 ≤ R) (hM' : M' ≤ M)
    (hL3 : (L + 1) ^ 3 ≤ R) (hLR : L + 2 ≤ R) (hB : B * 2 ^ K ≤ 80 * f * M')
    (h160 : 160 * f * L ≤ 2 ^ K) :
    T1 + M' * (L + 1) ^ 3 + B * L * (R + L + 2) ≤ 4 * (2 * M * r * w * (U + 1)) := by
  have hvol : 2 * M * r * w = M * R := by rw [hR]; ring
  rw [hvol]
  have h1 : T1 ≤ 2 * (M * R * (U + 1)) := by
    calc T1 ≤ M' * (R + 1) * (U + 1) := hT1
      _ ≤ M * (2 * R) * (U + 1) := by gcongr; omega
      _ = 2 * (M * R * (U + 1)) := by ring
  have h2 : M' * (L + 1) ^ 3 ≤ M * R * (U + 1) := by
    calc M' * (L + 1) ^ 3 ≤ M * R := Nat.mul_le_mul hM' hL3
      _ ≤ M * R * (U + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos U)
  have h3 : B * L * (R + L + 2) ≤ M * R * (U + 1) := by
    have hK : 0 < 2 ^ K := Nat.two_pow_pos K
    have h3a : B * L * (R + L + 2) ≤ 2 * (B * L * R) := by
      calc B * L * (R + L + 2) ≤ B * L * (2 * R) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (B * L * R) := by ring
    have h3b : 2 * (B * L * R) * 2 ^ K ≤ M' * R * 2 ^ K := by
      calc 2 * (B * L * R) * 2 ^ K = 2 * L * R * (B * 2 ^ K) := by ring
        _ ≤ 2 * L * R * (80 * f * M') := Nat.mul_le_mul_left _ hB
        _ = (160 * f * L) * (M' * R) := by ring
        _ ≤ 2 ^ K * (M' * R) := Nat.mul_le_mul_right _ h160
        _ = M' * R * 2 ^ K := by ring
    have h3c : 2 * (B * L * R) ≤ M' * R := Nat.le_of_mul_le_mul_right h3b hK
    calc B * L * (R + L + 2) ≤ 2 * (B * L * R) := h3a
      _ ≤ M' * R := h3c
      _ ≤ M * R := Nat.mul_le_mul_right _ hM'
      _ ≤ M * R * (U + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos U)
  calc T1 + M' * (L + 1) ^ 3 + B * L * (R + L + 2)
      ≤ 2 * (M * R * (U + 1)) + M * R * (U + 1) + M * R * (U + 1) :=
        Nat.add_le_add (Nat.add_le_add h1 h2) h3
    _ = 4 * (M * R * (U + 1)) := by ring

/-! ## 4. Sizes of the Lemma A.9 call -/

/-- `lgVol V ≤ c₁ (P+1)` for the record list of a compact role stream. -/
theorem lgVol_le {p : LayerParams} (hp : p.OK) {P₀ : ℕ} (hP₀ : 1 ≤ P₀) {t : CCoreRT}
    (hb : CCoreBands p P₀ t) :
    lgVol (t.A / Wn * 2 ^ (t.K * t.D) * t.S * (2 * t.r * t.wg + 1)) ≤ c1 p * (t.P + 1) := by
  obtain ⟨hP1, hd1, hr1, hK1, hD1, hA1, hS1, hΔ, heD⟩ := bands_basic hp hP₀ hb
  obtain ⟨hM, hKD, hr, hd⟩ := bands_size hp hP₀ hb
  have hwg : t.wg ≤ 2 ^ (t.P + 2) := by
    have : t.wg ≤ 3 * t.P + 3 := by unfold CCoreRT.wg; omega
    exact this.trans (three_mul_add_three_le t.P)
  have hwg1 : 1 ≤ t.wg := by unfold CCoreRT.wg; omega
  unfold lgVol
  apply Nat.clog_le_of_le_pow
  calc 2 * (t.A / Wn * 2 ^ (t.K * t.D) * t.S * (2 * t.r * t.wg + 1))
      ≤ 2 ^ (cM p * t.P + cR p * t.P + (t.P + 2) + 3) :=
        two_vol_le _ _ _ _ _ _ _ (M'_le_M t) hM hr hwg hr1 hwg1
    _ ≤ 2 ^ (c1 p * (t.P + 1)) := Nat.pow_le_pow_right (by norm_num) (arith_c1 _ _ _)

/-- **The record length dominates every polynomial in `P`** (`r ≥ 2^((a_r/b_d) P^(1-ε))`). -/
theorem r_ge_poly (p : LayerParams) (hp : p.OK) (κ : ℝ) (n : ℕ) :
    ∃ P₀ : ℕ, 1 ≤ P₀ ∧ ∀ t : CCoreRT, CCoreBands p P₀ t → κ * ((t.P : ℝ) + 1) ^ n ≤ t.r := by
  obtain ⟨-, -, -, hε1, had, hadb, har, -, -⟩ := ok_facts hp
  have hbd : 0 < p.b_d := had.trans_le hadb
  obtain ⟨P₁, hP₁⟩ := poly_le_two_rpow (1 - p.ε) (p.a_r / p.b_d) κ n (by linarith)
    (div_pos har hbd)
  refine ⟨max P₁ 1, le_max_right _ _, fun t hb => ?_⟩
  unfold CCoreBands at hb
  obtain ⟨hP, hd1, hd2, hr1, -⟩ := hb
  have hP1 : 1 ≤ t.P := (le_max_right _ _).trans hP
  have hPr : (0 : ℝ) < t.P := by exact_mod_cast hP1
  have hPε : (0 : ℝ) < (t.P : ℝ) ^ p.ε := Real.rpow_pos_of_pos hPr _
  have hdpos : (0 : ℝ) < t.d := lt_of_lt_of_le (mul_pos had hPε) hd1
  have hexp : p.a_r / p.b_d * (t.P : ℝ) ^ (1 - p.ε) ≤ p.a_r * t.P / t.d := by
    rw [Real.rpow_sub hPr, Real.rpow_one, div_mul_div_comm]
    exact div_le_div_of_nonneg_left (mul_nonneg har.le hPr.le) hdpos hd2
  calc κ * ((t.P : ℝ) + 1) ^ n ≤ (2 : ℝ) ^ (p.a_r / p.b_d * (t.P : ℝ) ^ (1 - p.ε)) :=
        hP₁ t.P ((le_max_left _ _).trans hP)
    _ ≤ (2 : ℝ) ^ (p.a_r * t.P / t.d) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ ≤ t.r := hr1

/-- **`2^K` dominates every polynomial in `P`** (`K = ⌊d^c⌋`, `d ≥ a_d P^ε`). -/
theorem twoK_ge_poly (p : LayerParams) (hp : p.OK) (κ : ℝ) (n : ℕ) :
    ∃ P₀ : ℕ, 1 ≤ P₀ ∧ ∀ t : CCoreRT, CCoreBands p P₀ t →
      κ * ((t.P : ℝ) + 1) ^ n ≤ (2 : ℝ) ^ t.K := by
  obtain ⟨-, hc0, hε0, -, had, -, -, -, -⟩ := ok_facts hp
  obtain ⟨P₁, hP₁⟩ := poly_le_two_rpow (p.ε * p.c) (p.a_d ^ p.c) (2 * κ) n (mul_pos hε0 hc0)
    (Real.rpow_pos_of_pos had _)
  refine ⟨max P₁ 1, le_max_right _ _, fun t hb => ?_⟩
  unfold CCoreBands at hb
  obtain ⟨hP, hd1, -, -, -, hK, -⟩ := hb
  have hP0 : (0 : ℝ) ≤ t.P := Nat.cast_nonneg _
  have hdc : p.a_d ^ p.c * (t.P : ℝ) ^ (p.ε * p.c) ≤ (t.d : ℝ) ^ p.c := by
    rw [Real.rpow_mul hP0, ← Real.mul_rpow had.le (Real.rpow_nonneg hP0 _)]
    exact Real.rpow_le_rpow (mul_nonneg had.le (Real.rpow_nonneg hP0 _)) hd1 hc0.le
  have hK1 : (t.d : ℝ) ^ p.c < t.K + 1 := by rw [hK]; exact Nat.lt_floor_add_one _
  have h2 : (2 : ℝ) ^ (p.a_d ^ p.c * (t.P : ℝ) ^ (p.ε * p.c)) ≤ 2 * (2 : ℝ) ^ t.K := by
    calc (2 : ℝ) ^ (p.a_d ^ p.c * (t.P : ℝ) ^ (p.ε * p.c)) ≤ (2 : ℝ) ^ ((t.K : ℝ) + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (hdc.trans hK1.le)
      _ = 2 * (2 : ℝ) ^ t.K := by
          rw [Real.rpow_add two_pos, Real.rpow_one, Real.rpow_natCast]; ring
  have h3 := hP₁ t.P ((le_max_left _ _).trans hP)
  linarith

/-! ## 5. The three targets -/

/-- **Header bounds in the bands**: `K·D, D, K ≤ c(P+1)` and `A, S, r, d ≤ 2^(c(P+1))`. -/
theorem hdr_bounds (p : LayerParams) (hp : p.OK) : ∃ P₀ c : ℕ, ∀ t : CCoreRT,
    CCoreBands p P₀ t →
    t.K * t.D ≤ c * (t.P + 1) ∧ t.A ≤ 2 ^ (c * (t.P + 1)) ∧ t.S ≤ 2 ^ (c * (t.P + 1)) ∧
    t.r ≤ 2 ^ (c * (t.P + 1)) ∧ t.d ≤ 2 ^ (c * (t.P + 1)) ∧ t.D ≤ c * (t.P + 1) ∧
    t.K ≤ c * (t.P + 1) := by
  refine ⟨1, cM p + cR p + cD p, fun t hb => ?_⟩
  obtain ⟨hP1, hd1, hr1, hK1, hD1, hA1, hS1, hΔ, heD⟩ := bands_basic hp le_rfl hb
  obtain ⟨hM, hKD, hr, hd⟩ := bands_size hp le_rfl hb
  have hle : ∀ x : ℕ, x ≤ cM p + cR p + cD p → x * t.P ≤ (cM p + cR p + cD p) * (t.P + 1) :=
    fun x hx => Nat.mul_le_mul hx (Nat.le_succ _)
  have hcM := hle (cM p) (by omega)
  have hcR := hle (cR p) (by omega)
  have hcD := hle (cD p) (by omega)
  have h2 : ∀ {a b : ℕ}, a ≤ b → 2 ^ a ≤ 2 ^ b := fun h => Nat.pow_le_pow_right (by norm_num) h
  have hAM : t.A ≤ t.M := by
    unfold CCoreRT.M
    calc t.A ≤ t.A * t.S := Nat.le_mul_of_pos_right _ hS1
      _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have hSM : t.S ≤ t.M := by
    unfold CCoreRT.M
    calc t.S ≤ t.A * t.S := Nat.le_mul_of_pos_left _ hA1
      _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  refine ⟨hKD.trans hcM, hAM.trans (hM.trans (h2 hcM)), hSM.trans (hM.trans (h2 hcM)),
    hr.trans (h2 hcR),
    hd.trans (hcD.trans (Nat.lt_two_pow_self (n := (cM p + cR p + cD p) * (t.P + 1))).le),
    ?_, ?_⟩
  · exact (Nat.le_mul_of_pos_left _ hK1).trans (hKD.trans hcM)
  · exact (Nat.le_mul_of_pos_right _ hD1).trans (hKD.trans hcM)

/-- **Polynomials in `P` are below `V_g`** above a cutoff. -/
theorem poly_absorb (p : LayerParams) (hp : p.OK) (c n : ℕ) : ∃ P₀ : ℕ, ∀ t : CCoreRT,
    CCoreBands p P₀ t → c * (t.P + 1) ^ n ≤ t.volG := by
  obtain ⟨P₀, hP₀, h⟩ := r_ge_poly p hp c n
  refine ⟨P₀, fun t hb => ?_⟩
  have h1 : c * (t.P + 1) ^ n ≤ t.r := by exact_mod_cast h t hb
  obtain ⟨-, -, -, -, -, hA1, hS1, -, -⟩ := bands_basic hp hP₀ hb
  have hM1 : 1 ≤ t.M := by
    unfold CCoreRT.M
    exact Nat.mul_pos (Nat.mul_pos hA1 hS1) (Nat.two_pow_pos _)
  have hwg1 : 1 ≤ t.wg := by unfold CCoreRT.wg; omega
  have h2 : t.r ≤ t.volG := by
    unfold CCoreRT.volG
    calc t.r ≤ 2 * t.M * t.r := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ 2 * t.M * t.r * t.wg := Nat.le_mul_of_pos_right _ hwg1
  exact h1.trans h2

/-- **The Lemma A.9 cost of one row addition is `O(V_g (Uτ(eK) + 1))`** above a cutoff: for the
record list of a compact role stream (`M' = A/W_c · 2^{KD} · S` records of width
`R = 2 r w_g`, volume `M'(R+1)`, `f = m^(k-1)`), `c7Cost ≤ 4 · V_g · (Uτ(eK) + 1)`. -/
theorem c7Cost_absorb (p : LayerParams) (hp : p.OK) : ∃ P₀ C₀ : ℕ, ∀ t : CCoreRT,
    CCoreBands p P₀ t → 1 ≤ t.k → 6 ≤ t.K →
    c7Cost p.τ t.K (mn ^ (t.k - 1)) (t.A / Wn * 2 ^ (t.K * t.D) * t.S)
      (t.A / Wn * 2 ^ (t.K * t.D) * t.S * (2 * t.r * t.wg + 1)) (2 * t.r * t.wg)
      ≤ C₀ * (t.volG * (Utau p.τ (t.e * t.K) + 1)) := by
  obtain ⟨hτ0, -, -, -, -, -, -, -, -⟩ := ok_facts hp
  obtain ⟨P₁, hP₁, hr⟩ := r_ge_poly p hp (((c1 p + 1) ^ 3 : ℕ) : ℝ) 3
  obtain ⟨P₂, hP₂, hK⟩ := twoK_ge_poly p hp ((160 * cM p * c1 p : ℕ) : ℝ) 2
  refine ⟨max P₁ P₂, 4, fun t hb _hk _hK6 => ?_⟩
  have hb1 := bands_mono (le_max_left P₁ P₂) hb
  have hb2 := bands_mono (le_max_right P₁ P₂) hb
  obtain ⟨hP1, hd1, hr1, hK1, hD1, hA1, hS1, hΔ, heD⟩ := bands_basic hp hP₁ hb1
  obtain ⟨hM, hKD, hrs, hd⟩ := bands_size hp hP₁ hb1
  have hL := lgVol_le hp hP₁ hb1
  have hr3 : (c1 p + 1) ^ 3 * (t.P + 1) ^ 3 ≤ t.r := by exact_mod_cast hr t hb1
  have h2K : 160 * cM p * c1 p * (t.P + 1) ^ 2 ≤ 2 ^ t.K := by exact_mod_cast hK t hb2
  have hM'M := M'_le_M t
  have hmn : 0 < mn := by show 0 < tripleM 100; unfold tripleM; positivity
  have hfe : mn ^ (t.k - 1) ≤ t.e := by
    show mn ^ (t.k - 1) ≤ tripleM 100 ^ t.k
    exact Nat.pow_le_pow_right hmn (Nat.sub_le _ _)
  have hDle : t.D ≤ cM p * t.P := (Nat.le_mul_of_pos_left _ hK1).trans hKD
  have hfD : mn ^ (t.k - 1) ≤ cM p * t.P := hfe.trans (heD.trans hDle)
  have hT1 := term1_le p.τ hτ0.le (t.A / Wn * 2 ^ (t.K * t.D) * t.S * (2 * t.r * t.wg + 1))
    (mn ^ (t.k - 1)) t.e t.K hfe
  unfold c7Cost CCoreRT.volG
  generalize hM'e : t.A / Wn * 2 ^ (t.K * t.D) * t.S = M' at hM'M hL hT1 ⊢
  generalize hLe : lgVol (M' * (2 * t.r * t.wg + 1)) = L at hL ⊢
  generalize hfe' : mn ^ (t.k - 1) = f at hfD hT1 ⊢
  have hwg1 : 1 ≤ t.wg := by unfold CCoreRT.wg; omega
  have hrR : t.r ≤ 2 * t.r * t.wg := by
    calc t.r ≤ 2 * t.r := by omega
      _ ≤ 2 * t.r * t.wg := Nat.le_mul_of_pos_right _ hwg1
  have hR1 : 1 ≤ 2 * t.r * t.wg := hr1.trans hrR
  have hL1 : L + 1 ≤ (c1 p + 1) * (t.P + 1) := by
    calc L + 1 ≤ c1 p * (t.P + 1) + (t.P + 1) := by omega
      _ = (c1 p + 1) * (t.P + 1) := by ring
  have hrL : (L + 1) ^ 3 ≤ t.r := by
    calc (L + 1) ^ 3 ≤ ((c1 p + 1) * (t.P + 1)) ^ 3 := Nat.pow_le_pow_left hL1 3
      _ = (c1 p + 1) ^ 3 * (t.P + 1) ^ 3 := by ring
      _ ≤ t.r := hr3
  have hL3 : (L + 1) ^ 3 ≤ 2 * t.r * t.wg := hrL.trans hrR
  have hLR : L + 2 ≤ 2 * t.r * t.wg := by
    have h1 : L + 1 ≤ (L + 1) ^ 3 := by
      calc L + 1 = (L + 1) ^ 1 := (pow_one _).symm
        _ ≤ (L + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos L) (by norm_num)
    have h2 : 2 * t.r ≤ 2 * t.r * t.wg := Nat.le_mul_of_pos_right _ hwg1
    omega
  have h160 : 160 * f * L ≤ 2 ^ t.K := by
    calc 160 * f * L ≤ 160 * (cM p * t.P) * (c1 p * (t.P + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hfD) hL
      _ = 160 * cM p * c1 p * (t.P * (t.P + 1)) := by ring
      _ ≤ 160 * cM p * c1 p * (t.P + 1) ^ 2 := by
          apply Nat.mul_le_mul_left
          rw [pow_two]
          exact Nat.mul_le_mul_right _ (Nat.le_succ _)
      _ ≤ 2 ^ t.K := h2K
  have hB : badMax t.K f M' * 2 ^ t.K ≤ 80 * f * M' := by
    unfold badMax
    calc min M' (80 * (f - 1) * M' / 2 ^ t.K) * 2 ^ t.K
        ≤ 80 * (f - 1) * M' / 2 ^ t.K * 2 ^ t.K := Nat.mul_le_mul_right _ (min_le_right _ _)
      _ ≤ 80 * (f - 1) * M' := Nat.div_mul_le_self _ _
      _ ≤ 80 * f * M' := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  exact c7_combine M' t.M (2 * t.r * t.wg) t.r t.wg f t.K L (badMax t.K f M')
    (Utau p.τ (t.e * t.K)) _ hT1 rfl hR1 hM'M hL3 hLR hB h160

end SubNLogN.Machine.CCore.LeafRowAddCostAux
