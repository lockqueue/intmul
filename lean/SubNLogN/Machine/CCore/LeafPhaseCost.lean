/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseProg
import WP.W3s.Math

/-!
# C-core leaves 8/10: cost bounds against `t.volG` (`CCore/LeafPhaseCost.lean`)

**Scope (honest summary).** Under the bands `CCoreBands p P₀ t` (`Contracts/CCore.lean:196`) with
`1 ≤ P`, every descriptor field except `d` is at most `t.volG = 2·M·r·w_g`, and
`bitLen d ≤ Cd p · P` from `d ≤ b_d · P^ε` (`Cd p = bitLen ⌈b_d⌉₊ + ⌈ε⌉₊`; no admissibility of `p`
is used). Hence the header read/write costs are `O(t.volG)` with a constant depending on `p` only
(`hdrCost_le`, `wgCost_le`, `dropCost_le`). The stored compact role array has volume
`≤ 2·t.volG` (`cvol_encArr`, `cvol_le`); `map_selRecs` commutes record maps with selection.
Everything is proved.
-/

namespace SubNLogN.Machine.CCore.LeafScalarAux

open TMFw TMFw.Contracts SubNLogN.Machine

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n :=
  TMFw.W3s.bitLen_le_of_lt (Nat.lt_two_pow_self)

/-- The constant of the `d`-field bound. -/
noncomputable def Cd (p : LayerParams) : ℕ := bitLen ⌈p.b_d⌉₊ + ⌈p.ε⌉₊

theorem bitLen_d_le (p : LayerParams) (t : CCoreRT) (hP : 1 ≤ t.P)
    (hd : (t.d : ℝ) ≤ p.b_d * (t.P : ℝ) ^ p.ε) : bitLen t.d ≤ Cd p * t.P := by
  set B := ⌈p.b_d⌉₊
  set E := ⌈p.ε⌉₊
  have hP1 : (1 : ℝ) ≤ t.P := by exact_mod_cast hP
  have hpos : 0 < (t.P : ℝ) ^ p.ε := Real.rpow_pos_of_pos (by linarith) _
  have hrpow : (t.P : ℝ) ^ p.ε ≤ (t.P : ℝ) ^ (E : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (Nat.le_ceil _)
  have hdle : t.d ≤ B * t.P ^ E := by
    have : (t.d : ℝ) ≤ (B : ℝ) * (t.P : ℝ) ^ E := by
      rcases le_or_gt p.b_d 0 with hb | hb
      · have h0 : p.b_d * (t.P : ℝ) ^ p.ε ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb hpos.le
        have : (0 : ℝ) ≤ (B : ℝ) * (t.P : ℝ) ^ E := by positivity
        linarith
      · have hB : p.b_d ≤ (B : ℝ) := Nat.le_ceil _
        calc (t.d : ℝ) ≤ p.b_d * (t.P : ℝ) ^ p.ε := hd
          _ ≤ (B : ℝ) * (t.P : ℝ) ^ p.ε := mul_le_mul_of_nonneg_right hB hpos.le
          _ ≤ (B : ℝ) * (t.P : ℝ) ^ (E : ℝ) :=
              mul_le_mul_of_nonneg_left hrpow (by positivity)
          _ = (B : ℝ) * (t.P : ℝ) ^ E := by rw [Real.rpow_natCast]
    exact_mod_cast this
  have hlt : t.d < 2 ^ (bitLen B + E * bitLen t.P) := by
    have h1 : B < 2 ^ bitLen B := TMFw.W3s.lt_two_pow_bitLen B
    have h2 : t.P ^ E ≤ 2 ^ (E * bitLen t.P) := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_le_pow_left (TMFw.W3s.lt_two_pow_bitLen t.P).le E
    have h3 : 0 < 2 ^ (E * bitLen t.P) := by positivity
    calc t.d ≤ B * t.P ^ E := hdle
      _ ≤ B * 2 ^ (E * bitLen t.P) := Nat.mul_le_mul_left _ h2
      _ < 2 ^ bitLen B * 2 ^ (E * bitLen t.P) := Nat.mul_lt_mul_of_pos_right h1 h3
      _ = 2 ^ (bitLen B + E * bitLen t.P) := by rw [pow_add]
  have h4 := TMFw.W3s.bitLen_le_of_lt hlt
  have h5 : E * bitLen t.P ≤ E * t.P := Nat.mul_le_mul_left _ (bitLen_le_self _)
  have h6 : bitLen B ≤ bitLen B * t.P := Nat.le_mul_of_pos_right _ hP
  simp only [Cd]
  nlinarith

/-! ## The bands give `O(volG)` fields -/

/-- Size facts from the bands. -/
theorem bands_facts {p : LayerParams} {P₀ : ℕ} {t : CCoreRT} (hb : CCoreBands p P₀ t) :
    1 ≤ t.r ∧ 1 ≤ t.M ∧ 1 ≤ t.K ∧ 1 ≤ t.D ∧ t.A ≤ t.M ∧ t.S ≤ t.M ∧ 2 ^ (t.K * t.D) ≤ t.M ∧
      t.M ≤ t.volG ∧ t.r ≤ t.volG ∧ t.wg ≤ t.volG := by
  obtain ⟨_, _, hd, hr1, _, _, _, hA, hS, _, _, hj, hρ, _⟩ := hb
  have hr : 1 ≤ t.r := by
    have h0 : (0 : ℝ) < (2 : ℝ) ^ (p.a_r * t.P / t.d) := Real.rpow_pos_of_pos (by norm_num) _
    have : (0 : ℝ) < t.r := lt_of_lt_of_le h0 hr1
    exact_mod_cast this
  have hK : 1 ≤ t.K := by omega
  have he : 1 ≤ t.e := Nat.one_le_pow _ _ (by norm_num [tripleM])
  have hD : 1 ≤ t.D := by omega
  have h2 : 1 ≤ 2 ^ (t.K * t.D) := Nat.one_le_two_pow
  have hM1 : t.A ≤ t.M := by
    simp only [CCoreRT.M]
    calc t.A = t.A * 1 * 1 := by ring
      _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hS) h2
  have hM2 : t.S ≤ t.M := by
    simp only [CCoreRT.M]
    calc t.S = 1 * t.S * 1 := by ring
      _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hA) h2
  have hM3 : 2 ^ (t.K * t.D) ≤ t.M := by
    simp only [CCoreRT.M]
    calc 2 ^ (t.K * t.D) = 1 * 1 * 2 ^ (t.K * t.D) := by ring
      _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := Nat.mul_le_mul (Nat.mul_le_mul hA hS) le_rfl
  have hM : 1 ≤ t.M := le_trans hA hM1
  have hw : 1 ≤ t.wg := by simp [CCoreRT.wg]
  have hrw : 1 ≤ t.r * t.wg := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hMw : 1 ≤ t.M * t.wg := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hMr : 1 ≤ t.M * t.r := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  refine ⟨hr, hM, hK, hD, hM1, hM2, hM3, ?_, ?_, ?_⟩
  · calc t.M = t.M * 1 := (mul_one _).symm
      _ ≤ t.M * (2 * (t.r * t.wg)) := Nat.mul_le_mul_left _ (by omega)
      _ = t.volG := by simp only [CCoreRT.volG]; ring
  · calc t.r = t.r * 1 := (mul_one _).symm
      _ ≤ t.r * (2 * (t.M * t.wg)) := Nat.mul_le_mul_left _ (by omega)
      _ = t.volG := by simp only [CCoreRT.volG]; ring
  · calc t.wg = t.wg * 1 := (mul_one _).symm
      _ ≤ t.wg * (2 * (t.M * t.r)) := Nat.mul_le_mul_left _ (by omega)
      _ = t.volG := by simp only [CCoreRT.volG]; ring

/-- Every descriptor field (and the width counter) is `O(volG)` (with the extra constant `Cd p` for
the field `d`). -/
theorem fields_le {p : LayerParams} {t : CCoreRT} (hb : CCoreBands p 1 t) :
    bitLen t.P ≤ t.volG ∧ bitLen t.r ≤ t.volG ∧ bitLen t.Δ ≤ t.volG ∧ bitLen t.A ≤ t.volG ∧
      bitLen t.R ≤ t.volG ∧ bitLen t.K ≤ t.volG ∧ bitLen t.D ≤ t.volG ∧ bitLen t.S ≤ t.volG ∧
      bitLen t.j0 ≤ t.volG ∧ bitLen t.k ≤ t.volG ∧ bitLen t.ρ ≤ t.volG ∧
      bitLen t.wg ≤ t.volG ∧ bitLen (t.P + t.Δ) ≤ t.volG ∧ bitLen (t.P + t.Δ + t.Δ) ≤ t.volG ∧
      bitLen (t.k - 1) ≤ t.volG ∧ bitLen t.d ≤ Cd p * t.volG ∧ 1 ≤ t.volG ∧
      t.wg + 1 ≤ 2 * t.volG ∧ 2 ^ (t.K * t.D) ≤ t.volG ∧ t.S ≤ t.volG ∧ t.D ≤ t.volG ∧
      t.A * t.S * 2 ^ (t.K * t.D) * (2 * t.wg * t.r + 1) ≤ 2 * t.volG := by
  obtain ⟨hr, hM, hK, hD, hAM, hSM, h2M, hMV, hrV, hwV⟩ := bands_facts hb
  obtain ⟨hP1, _, hdb, _, _, _, _, hA, hS, hRA, _, hj, hρ, _⟩ := hb
  have hwg : t.wg = t.P + 2 * t.Δ + 3 := rfl
  have bl := bitLen_le_self
  have hKD1 : t.K ≤ t.K * t.D := Nat.le_mul_of_pos_right _ hD
  have hKD2 : t.D ≤ t.K * t.D := Nat.le_mul_of_pos_left _ hK
  have hKD3 : t.K * t.D < 2 ^ (t.K * t.D) := Nat.lt_two_pow_self
  have hRA' : t.R ≤ t.A := Nat.le_of_dvd hA hRA
  have he : t.k < t.e := Nat.lt_pow_self (by norm_num [tripleM])
  have hed : t.e ≤ t.D := by omega
  have hdP := bitLen_d_le p t hP1 hdb
  have hPV : t.P ≤ t.volG := by omega
  have hdV : Cd p * t.P ≤ Cd p * t.volG := Nat.mul_le_mul_left _ hPV
  have hvol : t.A * t.S * 2 ^ (t.K * t.D) * (2 * t.wg * t.r + 1) ≤ 2 * t.volG := by
    have hw1 : 1 ≤ t.wg := by omega
    have : 2 * t.wg * t.r + 1 ≤ 4 * t.wg * t.r := by nlinarith
    calc t.A * t.S * 2 ^ (t.K * t.D) * (2 * t.wg * t.r + 1) ≤ t.M * (4 * t.wg * t.r) :=
          Nat.mul_le_mul le_rfl this
      _ = 2 * t.volG := by simp only [CCoreRT.volG]; ring
  have b1 := bl t.P
  have b2 := bl t.r
  have b3 := bl t.Δ
  have b4 := bl t.A
  have b5 := bl t.R
  have b6 := bl t.K
  have b7 := bl t.D
  have b8 := bl t.S
  have b9 := bl t.j0
  have b10 := bl t.k
  have b11 := bl t.ρ
  have b12 := bl t.wg
  have b13 := bl (t.P + t.Δ)
  have b14 := bl (t.P + t.Δ + t.Δ)
  have b15 := bl (t.k - 1)
  have hV1 : 1 ≤ t.volG := by omega
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, hV1, by omega, by omega,
    by omega, by omega, hvol⟩

theorem hdrCost_le {p : LayerParams} {t : CCoreRT} (hb : CCoreBands p 1 t) :
    hdrCost t ≤ 600 * t.volG + 19 * (Cd p * t.volG) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -, -, -, -, hd, hV, -⟩ := fields_le hb
  simp only [hdrCost, hdrFields, hdrActs, rdCost, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

theorem wgCost_le {p : LayerParams} {t : CCoreRT} (hb : CCoreBands p 1 t) :
    wgCost t ≤ 300 * t.volG := by
  obtain ⟨h1, -, h3, -, -, -, -, -, -, -, -, -, h13, h14, -, -, hV, -⟩ := fields_le hb
  have h3' : bitLen 3 = 2 := by decide
  simp only [wgCost, h3']
  omega

theorem dropCost_le {p : LayerParams} {t : CCoreRT} (hb : CCoreBands p 1 t) :
    dropCost t ≤ 40 * t.volG := by
  obtain ⟨h1, -, h3, -, -, h6, h7, h8, h9, h10, h11, h12, -, -, -, -, hV, -⟩ := fields_le hb
  simp only [dropCost]
  omega

open SubNLogN.Math.Common SubNLogN.Math.Walsh

/-! ## Volumes of the stored arrays -/

theorem length_layerAddrs (A K D S : ℕ) (hA : 0 < A) (hS : 0 < S) :
    (layerAddrs A K D S hA hS).length = A * 2 ^ (K * D) * S := by
  simp [layerAddrs]

theorem cvol_encArr {α : Type} {r : ℕ} (w F : ℕ) (addrs : List α) (z : α → Fin r → ℂ) :
    cvol w (encArr F addrs z) = addrs.length * (2 * w * r + 1) := by
  rw [cvol, length_carrSyms]
  simp only [encArr, List.map_map, Function.comp_def, List.length_map, List.length_finRange]
  rw [List.map_const', List.sum_replicate, smul_eq_mul]

theorem cvol_le {p : LayerParams} {t : CCoreRT} (hb : CCoreBands p 1 t) (hA' : 0 < t.A / Wn)
    (hS : 0 < t.S) (z : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) (F : ℕ) :
    cvol t.wg (encArr F (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) z) ≤ 2 * t.volG := by
  rw [cvol_encArr, length_layerAddrs]
  have h := (fields_le hb).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hAW : t.A / Wn ≤ t.A := Nat.div_le_self _ _
  calc t.A / Wn * 2 ^ (t.K * t.D) * t.S * (2 * t.wg * t.r + 1)
      ≤ t.A * t.S * 2 ^ (t.K * t.D) * (2 * t.wg * t.r + 1) := by
        apply Nat.mul_le_mul_right
        calc t.A / Wn * 2 ^ (t.K * t.D) * t.S = t.A / Wn * t.S * 2 ^ (t.K * t.D) := by ring
          _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := by
            apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_right _ hAW
    _ ≤ 2 * t.volG := h

theorem map_selRecs {α β : Type} [Inhabited α] [Inhabited β] (b : ℕ → Bool) (f : α → β)
    (hf : f default = default) (v vn : List α) :
    (selRecs b v vn).map f = selRecs b (v.map f) (vn.map f) := by
  simp only [selRecs, List.map_map, List.length_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  have key : ∀ l : List α, f (l.getD i default) = (l.map f).getD i default := by
    intro l
    rw [← hf, List.getD_map]
  split_ifs <;> exact key _

end SubNLogN.Machine.CCore.LeafScalarAux
