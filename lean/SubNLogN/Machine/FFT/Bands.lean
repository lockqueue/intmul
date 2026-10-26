/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.MiddleMath

/-!
# K4 band discharge (`Machine/FFT/Bands.lean`): Proposition A.11's bands at every layer call of the middle

**Scope (honest summary).** The middle's contract (`WalshMiddleMachineGenStmt Band lam'`,
`Contracts/FFT.lean`) assumes `MidCallsBand Band q ℓ K w a`: every layer call it makes is
admissible (chunk rounds at precision `q`, width `w`; CNOT batches at `q + 8d`, `w + 8d`). With
`Band = LayerBands p' P₀` (`Contracts/Layer.lean`) this is a list of real inequalities per call.
This file derives it from the paper-form hypotheses of Theorem 6.5 / Corollary 6.6 at `q`
(`MidFamilyBands`: the comparison bands of Proposition A.11 at `q`, `K = ⌊d^c⌋`, `w ≤ C_w q`,
`dℓ ≤ C_ℓ q`), for the constants `p' = midLayerParams p C_ℓ`: the lower comparison constants of `p`
halved (Lemma 5.3, `lem:walsh-lift`; Corollary 6.6, `cor:walsh-middle`), `C_M = C_ℓ + 1`
and `C_desc = 32(C_ℓ + C_w + 1)` (as chosen in Section 6.4, `sec:direct-fft-thm`). Everything is
proved (no `sorry`); the analytic step is `walsh_lift_bands` (Lemma 5.3, `Math/Walsh/Exact.lean`).

* `midLayerParams`, `midLayerParams_OK` (admissible constants stay admissible).
* `MidFamilyBands p C_ℓ q D ℓ K w`: the paper-form hypotheses at `q` (`d = D + 1`, `r = 2^ℓ`).
* `midCallsBand_of_bands`: there is a cutoff `P₁` (from Lemma 5.3) such that for `q ≥ P₀, P₁`,
  `MidShapeOK` and `MidFamilyBands` give `MidCallsBand (LayerBands (midLayerParams p C_ℓ) P₀)`.
  Helpers are in `SubNLogN.Machine.FFT.BandsAux`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common

/-- **The constants of Proposition A.11 for the middle's layer calls**: `p` with the lower
comparison constants halved (`a_d/2`, `a_r/2`; Lemma 5.3, `lem:walsh-lift`: the bands at `q`
imply those at `q_* = q + 8d` with halved lower constants), `C_M = C_ℓ + 1` and
`C_desc = 32(C_ℓ + C_w + 1)` (Section 6.4, `sec:direct-fft-thm`). -/
noncomputable def midLayerParams (p : LayerParams) (Cℓ : ℕ) : LayerParams where
  τ := p.τ
  σ := p.σ
  β := p.β
  c := p.c
  ε := p.ε
  lam := p.lam
  lam' := p.lam'
  C₁ := p.C₁
  a_d := p.a_d / 2
  b_d := p.b_d
  a_r := p.a_r / 2
  b_r := p.b_r
  C_M := (Cℓ : ℝ) + 1
  C_desc := 32 * ((Cℓ : ℝ) + p.C_w + 1)
  C_w := p.C_w

/-- Halving the lower comparison constants and enlarging `C_M`, `C_desc` keeps the constants
admissible. -/
theorem midLayerParams_OK {p : LayerParams} (Cℓ : ℕ) (hp : p.OK) : (midLayerParams p Cℓ).OK := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, had,
    hadb, har, harb, -, -, hCw⟩ := hp
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, ?_, ?_,
    ?_, ?_, ?_, ?_, hCw⟩
  · show 0 < p.a_d / 2; linarith
  · show p.a_d / 2 ≤ p.b_d; linarith
  · show 0 < p.a_r / 2; linarith
  · show p.a_r / 2 ≤ p.b_r; linarith
  · show 0 < (Cℓ : ℝ) + 1; positivity
  · show 0 < 32 * ((Cℓ : ℝ) + p.C_w + 1); have : (0 : ℝ) ≤ Cℓ := Nat.cast_nonneg _; nlinarith

/-- **The paper-form hypotheses of Theorem 6.5 (`thm:direct-fft`) and Corollary 6.6 (`cor:walsh-middle`)**
at precision `q` (Proposition A.11, eq. `eq:walsh-layer-bands`), with `d = D + 1`, `r = 2^ℓ`: the
comparison bands of Proposition A.11 at `q` with the constants of `p`
(`a_d q^ε ≤ d ≤ b_d q^ε`, `2^{a_r q/d} ≤ r ≤ 2^{b_r q/d}`), `K = ⌊d^c⌋`, `w ≤ C_w q` and
`dℓ ≤ C_ℓ q`. (The cutoff `q ≥ P₀` is kept separate.) -/
def MidFamilyBands (p : LayerParams) (Cℓ : ℕ) (q D ℓ K w : ℕ) : Prop :=
  p.a_d * (q : ℝ) ^ p.ε ≤ ((D + 1 : ℕ) : ℝ) ∧ ((D + 1 : ℕ) : ℝ) ≤ p.b_d * (q : ℝ) ^ p.ε ∧
  (2 : ℝ) ^ (p.a_r * q / ((D + 1 : ℕ) : ℝ)) ≤ ((2 ^ ℓ : ℕ) : ℝ) ∧
  ((2 ^ ℓ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (p.b_r * q / ((D + 1 : ℕ) : ℝ)) ∧
  K = ⌊((D + 1 : ℕ) : ℝ) ^ p.c⌋₊ ∧ (w : ℝ) ≤ p.C_w * q ∧ (D + 1) * ℓ ≤ Cℓ * q

end SubNLogN.Machine

namespace SubNLogN.Machine.FFT.BandsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
  SubNLogN.Machine

theorem length_hdrSyms (fs : List ℕ) :
    (hdrSyms fs).length = (fs.map fun n => bitLen n + 1).sum := by
  induction fs with
  | nil => simp [hdrSyms]
  | cons n fs ih =>
    simp only [hdrSyms, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih, length_natSyms, List.length_singleton]

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n :=
  WP.W9comp.bitLen_le_of_lt_two_pow (Nat.lt_two_pow_self)

theorem bitLen_two_pow_le (k : ℕ) : bitLen (2 ^ k) ≤ k + 1 :=
  WP.W9comp.bitLen_le_of_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))

/-- Header length of a layer call with record length `2^k`. -/
theorem length_hdr_layerRT (P d k w K j₀ D nS ρ : ℕ) :
    (layerRT P d (2 ^ k) w K j₀ D nS ρ).hdr.length ≤
      P + d + (k + 1) + D + (j₀ + 1) + (nS + 1) + K + (ρ + 1) + w + 9 := by
  show (hdrSyms [P, d, 2 ^ k, D, 2 ^ j₀, 2 ^ nS, K, ρ + 1, w]).length ≤ _
  rw [length_hdrSyms]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have := bitLen_le_self P
  have := bitLen_le_self d
  have := bitLen_two_pow_le k
  have := bitLen_le_self D
  have := bitLen_two_pow_le j₀
  have := bitLen_two_pow_le nS
  have := bitLen_le_self K
  have := bitLen_le_self (ρ + 1)
  have := bitLen_le_self w
  omega

/-- `log₂ (2M) = m + 1` for the `2^m` records of a slice shape. -/
theorem logb_M {j₀ D K nS m : ℕ} (hm : j₀ + D * K + nS = m) :
    Real.logb 2 (2 * ((2 ^ j₀ * 2 ^ nS * 2 ^ (K * D) : ℕ) : ℝ)) = (m : ℝ) + 1 := by
  have he : j₀ + nS + K * D = m := by rw [Nat.mul_comm]; omega
  have h : 2 ^ j₀ * 2 ^ nS * 2 ^ (K * D) = 2 ^ m := by rw [← pow_add, ← pow_add, he]
  rw [h]
  have h2 : (2 : ℝ) * ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ ((m + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; ring
  rw [h2, Real.logb_rpow (by norm_num) (by norm_num)]
  push_cast
  ring

end SubNLogN.Machine.FFT.BandsAux

namespace SubNLogN.Machine.FFT.BandsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
  SubNLogN.Machine

/-- Size facts from the shape and family hypotheses: `m₀ ≤ C_ℓ q`, `d ≤ C_ℓ q`, `1 ≤ q`. -/
theorem size_facts {p : LayerParams} {Cℓ q ℓ K w D : ℕ} {a : Fin D → ℕ}
    (hshape : MidShapeOK q ℓ K w a) (hfam : MidFamilyBands p Cℓ q D ℓ K w) :
    addrBits a ≤ Cℓ * q ∧ D + 1 ≤ Cℓ * q ∧ 1 ≤ q := by
  obtain ⟨hq8, -, hℓ2, -, -, -, ha, -⟩ := hshape
  obtain ⟨-, -, -, -, -, -, hdℓ⟩ := hfam
  have hm : addrBits a ≤ D * ℓ :=
    FFT.MiddleAux.addrBits_le_mul (fun i => by rcases ha i with h | h <;> omega)
  have h1 : D * ℓ ≤ (D + 1) * ℓ := Nat.mul_le_mul_right _ (Nat.le_succ D)
  have h2 : (D + 1) * 2 ≤ (D + 1) * ℓ := Nat.mul_le_mul_left _ hℓ2
  refine ⟨by omega, by omega, by omega⟩

/-- **Every chunk-round call is admissible** (Theorem 6.5, `thm:direct-fft`, Section 6.4). -/
theorem chunk_band {p : LayerParams} (hp : p.OK) (Cℓ : ℕ) {P₀ q ℓ K w D : ℕ} {a : Fin D → ℕ}
    (hP₀ : P₀ ≤ q) (hshape : MidShapeOK q ℓ K w a) (hfam : MidFamilyBands p Cℓ q D ℓ K w)
    {j₀ nS ρ : ℕ} (hm : j₀ + D * K + nS = addrBits a) (hρ : ρ < K) :
    LayerBands (midLayerParams p Cℓ) P₀ (layerRT q (D + 1) (2 ^ ℓ) w K j₀ D nS ρ) := by
  obtain ⟨hmC, hdC, hq1⟩ := size_facts hshape hfam
  obtain ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hw⟩ := hshape
  obtain ⟨hd1, hd2, hr1, hr2, hK, hwC, hdℓ⟩ := hfam
  obtain ⟨-, -, -, -, -, -, -, -, -, hε0, hε1, -, -, -, -, -, -, -, had, hadb, har, harb, -, -,
    hCw⟩ := hp
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine ⟨hP₀, ?_, hd2, ?_, hr2, hK, hD1, Nat.le_succ D, Nat.one_le_two_pow, Nat.one_le_two_pow,
    hρ, ?_, hw, hwC, ?_⟩
  · show p.a_d / 2 * (q : ℝ) ^ p.ε ≤ ((D + 1 : ℕ) : ℝ)
    have := Real.rpow_nonneg hq0 p.ε
    nlinarith
  · show (2 : ℝ) ^ (p.a_r / 2 * (q : ℝ) / ((D + 1 : ℕ) : ℝ)) ≤ ((2 ^ ℓ : ℕ) : ℝ)
    refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) hr1
    have hd0 : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) := by positivity
    gcongr
    linarith
  · show Real.logb 2 (2 * ((2 ^ j₀ * 2 ^ nS * 2 ^ (K * D) : ℕ) : ℝ)) ≤ ((Cℓ : ℝ) + 1) * q
    rw [logb_M hm]
    have h : addrBits a + 1 ≤ (Cℓ + 1) * q := by
      have : (Cℓ + 1) * q = Cℓ * q + q := by ring
      omega
    exact_mod_cast h
  · show (((layerRT q (D + 1) (2 ^ ℓ) w K j₀ D nS ρ).hdr.length : ℕ) : ℝ) ≤
      32 * ((Cℓ : ℝ) + p.C_w + 1) * q
    have hlen := length_hdr_layerRT q (D + 1) ℓ w K j₀ D nS ρ
    have hjn : j₀ + nS ≤ addrBits a := by omega
    have hnat : (layerRT q (D + 1) (2 ^ ℓ) w K j₀ D nS ρ).hdr.length ≤ (18 + 3 * Cℓ) * q + w := by
      have : (18 + 3 * Cℓ) * q = 18 * q + 3 * (Cℓ * q) := by ring
      omega
    have hcast : (((layerRT q (D + 1) (2 ^ ℓ) w K j₀ D nS ρ).hdr.length : ℕ) : ℝ) ≤
        (18 + 3 * (Cℓ : ℝ)) * q + w := by exact_mod_cast hnat
    have hC0 : (0 : ℝ) ≤ Cℓ := Nat.cast_nonneg _
    nlinarith

/-- **Every CNOT-batch call is admissible** (at `q + 8d`, `w + 8d`, with the halved lower
constants of Lemma 5.3, `lem:walsh-lift`; Corollary 6.6, `cor:walsh-middle`). `hlift` is the
conclusion of `walsh_lift_bands` at `q`. -/
theorem slice_band {p : LayerParams} (hp : p.OK) (Cℓ : ℕ) {P₀ q ℓ K w D : ℕ} {a : Fin D → ℕ}
    (hP₀ : P₀ ≤ q) (hshape : MidShapeOK q ℓ K w a) (hfam : MidFamilyBands p Cℓ q D ℓ K w)
    (hlift : q + 8 * (D + 1) ≤ 2 * q ∧
      p.a_d / 2 * ((q + 8 * (D + 1) : ℕ) : ℝ) ^ p.ε ≤ ((D + 1 : ℕ) : ℝ) ∧
      ((D + 1 : ℕ) : ℝ) ≤ p.b_d * ((q + 8 * (D + 1) : ℕ) : ℝ) ^ p.ε ∧
      (2 : ℝ) ^ (p.a_r / 2 * ((q + 8 * (D + 1) : ℕ) : ℝ) / ((D + 1 : ℕ) : ℝ)) ≤ ((2 ^ ℓ : ℕ) : ℝ) ∧
      ((2 ^ ℓ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (p.b_r * ((q + 8 * (D + 1) : ℕ) : ℝ) / ((D + 1 : ℕ) : ℝ)))
    {j₀ D' nS ρ : ℕ} (hm : j₀ + D' * K + nS = addrBits a) (hD1 : 1 ≤ D') (hDd : D' ≤ D + 1)
    (hρ : ρ < K) :
    LayerBands (midLayerParams p Cℓ) P₀ (sliceRT q (D + 1) (2 ^ ℓ) w K j₀ D' nS ρ) := by
  obtain ⟨hmC, hdC, hq1⟩ := size_facts hshape hfam
  obtain ⟨hq8, hD1', hℓ2, hℓq, hK1, hKℓ, ha, hw⟩ := hshape
  obtain ⟨hd1, hd2, hr1, hr2, hK, hwC, hdℓ⟩ := hfam
  obtain ⟨-, -, -, -, -, -, -, -, -, hε0, hε1, -, -, -, -, -, -, -, had, hadb, har, harb, -, -,
    hCw⟩ := hp
  obtain ⟨-, hl1, hl2, hl3, hl4⟩ := hlift
  refine ⟨by show P₀ ≤ q + 8 * (D + 1); omega, hl1, hl2, hl3, hl4, hK, hD1, hDd,
    Nat.one_le_two_pow, Nat.one_le_two_pow, hρ, ?_, by show q + 8 * (D + 1) + 2 ≤ w + 8 * (D + 1); omega, ?_, ?_⟩
  · show Real.logb 2 (2 * ((2 ^ j₀ * 2 ^ nS * 2 ^ (K * D') : ℕ) : ℝ)) ≤
      ((Cℓ : ℝ) + 1) * ((q + 8 * (D + 1) : ℕ) : ℝ)
    rw [logb_M hm]
    have h : addrBits a + 1 ≤ (Cℓ + 1) * (q + 8 * (D + 1)) := by
      have : (Cℓ + 1) * (q + 8 * (D + 1)) = Cℓ * q + q + (Cℓ + 1) * (8 * (D + 1)) := by ring
      omega
    exact_mod_cast h
  · show (((w + 8 * (D + 1) : ℕ)) : ℝ) ≤ p.C_w * ((q + 8 * (D + 1) : ℕ) : ℝ)
    push_cast
    have : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
    nlinarith
  · show (((sliceRT q (D + 1) (2 ^ ℓ) w K j₀ D' nS ρ).hdr.length : ℕ) : ℝ) ≤
      32 * ((Cℓ : ℝ) + p.C_w + 1) * ((q + 8 * (D + 1) : ℕ) : ℝ)
    have hlen := length_hdr_layerRT (q + 8 * (D + 1)) (D + 1) ℓ (w + 8 * (D + 1)) K j₀ D' nS ρ
    have hjn : j₀ + nS ≤ addrBits a := by omega
    have hnat : (sliceRT q (D + 1) (2 ^ ℓ) w K j₀ D' nS ρ).hdr.length ≤
        (17 + 19 * Cℓ) * q + w := by
      have : (17 + 19 * Cℓ) * q = 17 * q + 19 * (Cℓ * q) := by ring
      have hs : (sliceRT q (D + 1) (2 ^ ℓ) w K j₀ D' nS ρ) =
          layerRT (q + 8 * (D + 1)) (D + 1) (2 ^ ℓ) (w + 8 * (D + 1)) K j₀ D' nS ρ := rfl
      rw [hs]
      omega
    have hcast : (((sliceRT q (D + 1) (2 ^ ℓ) w K j₀ D' nS ρ).hdr.length : ℕ) : ℝ) ≤
        (17 + 19 * (Cℓ : ℝ)) * q + w := by exact_mod_cast hnat
    have hC0 : (0 : ℝ) ≤ Cℓ := Nat.cast_nonneg _
    have hqq : (q : ℝ) ≤ ((q + 8 * (D + 1) : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right q _
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith

end SubNLogN.Machine.FFT.BandsAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Math.Walsh SubNLogN.Machine.FFT.BandsAux

/-- **Band discharge for the Walsh middle** (Corollary 6.6, `cor:walsh-middle`; Lemma 5.3,
`lem:walsh-lift`; header and record-count constants as in Section 6.4, `sec:direct-fft-thm`). For
admissible constants `p` and any `C_ℓ` there is a cutoff `P₁` such that, whenever `q ≥ P₀` (the
layer contract's cutoff) and `q ≥ P₁`, Theorem 6.5's shape hypotheses (`MidShapeOK`) and the
paper-form bands at `q` (`MidFamilyBands p C_ℓ`) imply that every layer call of the middle is in
Proposition A.11's bands for the constants `midLayerParams p C_ℓ`: the chunk rounds at `q` and the
CNOT batches at `q + 8d`, `w + 8d`. -/
theorem midCallsBand_of_bands {p : LayerParams} (hp : p.OK) (Cℓ : ℕ) :
    ∃ P₁ : ℕ, ∀ (P₀ q ℓ K w D : ℕ) (a : Fin D → ℕ), P₀ ≤ q → P₁ ≤ q →
      MidShapeOK q ℓ K w a → MidFamilyBands p Cℓ q D ℓ K w →
      MidCallsBand (LayerBands (midLayerParams p Cℓ) P₀) q ℓ K w a := by
  have hp' := hp
  obtain ⟨-, -, -, -, -, -, -, -, -, hε0, hε1, -, -, -, -, -, -, -, had, hadb, har, harb, -, -,
    -⟩ := hp'
  obtain ⟨P₁, hP₁⟩ := walsh_lift_bands p.ε p.a_d p.b_d p.a_r p.b_r hε0 hε1 had hadb har harb
  refine ⟨P₁, fun P₀ q ℓ K w D a hP₀ hq hshape hfam => ⟨?_, ?_⟩⟩
  · intro j₀ nS ρ hm hρ
    exact chunk_band hp Cℓ hP₀ hshape hfam hm hρ
  · intro j₀ D' nS ρ hm hD1 hDd hρ
    have hlift := hP₁ q (D + 1) (2 ^ ℓ) hq hfam.1 hfam.2.1 hfam.2.2.1 hfam.2.2.2.1
    exact slice_band hp Cℓ hP₀ hshape hfam hlift hm hD1 hDd hρ

end SubNLogN.Machine
