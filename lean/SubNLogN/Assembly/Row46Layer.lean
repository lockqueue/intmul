import SubNLogN.Machine.Contracts.Layer
import SubNLogN.Math.Cost.Row46
import SubNLogN.Math.Networks.Proofs.Deficit
import SubNLogN.Machine.FFT.Bands
import SubNLogN.Math.Cost.WalshOKW8

/-!
# Assembly: the `C₁ = 14` Walsh row as constants of Proposition A.11 (`row46Layer`)

The `κ = 2^{-46}` row of Table 6 (`tab:walsh-rows`, `C₁ = 14`, `ξ = 2^{-42}`, Section 7.5) packaged as
`LayerParams` (`Machine/Contracts/Layer.lean`), with the exact rationals of
`Math/Cost/Row46.lean`: `τ = 1 − 4ξ = 1 − 2^{-40}`, `σ = 1 − ξ = 1 − 2^{-42}`, `β = 1/64`,
`c = ξ/256 = 2^{-50}`, `ε = 1/15`, `λ = 1 − 63ξ/64`, `λ' = 1 − 31ξ/32`, `C₁ = 14`, and the
comparison constants of Lemma 7.1 (`lem:root-family`, eq. (`eq:bands`)): `a_d = 1/4`, `b_d = 1`,
`a_r = 1/128`, `b_r = 1/8`, `C_M = 1`, `C_desc = 1`, `C_w = 2` (`midLayerParams` halves
`a_d`, `a_r` and replaces `C_M`, `C_desc` for the middle's calls, Lemma 5.3 (`lem:walsh-lift`)).

* `row46Layer : LayerParams` and `row46Layer_OK : row46Layer.OK`: the sign and ordering
  conditions from `Row46`'s exact rationals (`(eq:walsh-layer-a)`, `(eq:walsh-layer-b)`, `εC₁ < 1`;
  note `σ + β(1 − σ) = λ` exactly at this row), and the two deficit conditions from the proved
  `deficitsH100_holds` (Proposition A.2 (`prop:deficits`): `s_b/W_b < m^{1−2^{-40}} = m^τ`, `s_c/W_c < m^{1−2^{-42}} = m^σ`).
* `midShapeOK_row46`, `midFamilyBands_row46`: Theorem 6.5's (`thm:direct-fft`) shape conditions and the paper-form
  bands `MidFamilyBands row46Layer 1` (`Machine/FFT/Bands.lean`) for the `κ = 2^{-46}` row at
  any `q` with `16K0 ≤ q ≤ 64K0` (`2^15 ≤ K0`), from the integer band bounds.
* `midBands_w8_of_width`: eventually at the W8 root parameters (`K0 = W8.hK0 n`,
  `p0 = W8.hP0 n`, `q = schedP p0 K0 + 2`), for every width `w` with `q + 2 ≤ w ≤ 2q`,
  `MidShapeOK ∧ MidFamilyBands row46Layer 1 ∧ P₀ ≤ q ∧ P₁ ≤ q`; `MidBandsW8Stmt` /
  `midBandsW8_holds`: instantiated at internal width `wI = schedP p0 K0 + K0 + 8`.
  Helpers are in `SubNLogN.Assembly.Row46LayerAux`.
-/

namespace SubNLogN.Assembly

open SubNLogN.Machine SubNLogN.Math.Cost

/-- **The `C₁ = 14` row (Table 6 (`tab:walsh-rows`)) as constants of Proposition A.11 (`prop:prop14-param`).** The exponents are the
exact rationals of `Math/Cost/Row46.lean` (cast to `ℝ`); the comparison constants are those of
Lemma 7.1 (`lem:root-family`, eq. (`eq:bands`): `a_d = 1/4`, `b_d = 1`, `a_r = 1/128`, `b_r = 1/8`), with
`C_M = 1`, `C_desc = 1`, `C_w = 2`. -/
noncomputable def row46Layer : LayerParams where
  τ := ((Row46.tau : ℚ) : ℝ)
  σ := ((Row46.sigma : ℚ) : ℝ)
  β := ((Row46.beta : ℚ) : ℝ)
  c := ((Row46.c : ℚ) : ℝ)
  ε := ((Row46.eps : ℚ) : ℝ)
  lam := ((Row46.lam : ℚ) : ℝ)
  lam' := ((Row46.lam' : ℚ) : ℝ)
  C₁ := Row46.C1
  a_d := 1 / 4
  b_d := 1
  a_r := 1 / 128
  b_r := 1 / 8
  C_M := 1
  C_desc := 1
  C_w := 2

/-- `τ = 1 − 2^{-40}` (the bit-network deficit exponent of Proposition A.2 (`prop:deficits`)). -/
theorem row46Layer_tau : row46Layer.τ = (1 : ℝ) - (2 : ℝ)⁻¹ ^ 40 := by
  show ((Row46.tau : ℚ) : ℝ) = _
  norm_num [Row46.tau, Row46.xi]

/-- `σ = 1 − 2^{-42}` (the complex-network deficit exponent of Proposition A.2 (`prop:deficits`)). -/
theorem row46Layer_sigma : row46Layer.σ = (1 : ℝ) - (2 : ℝ)⁻¹ ^ 42 := by
  show ((Row46.sigma : ℚ) : ℝ) = _
  norm_num [Row46.sigma, Row46.xi]

/-- **The `C₁ = 14` row is admissible** (`LayerParams.OK`). -/
theorem row46Layer_OK : row46Layer.OK := by
  obtain ⟨hb, hc⟩ := SubNLogN.Math.Networks.deficitsH100_holds
  refine ⟨?_, ?_, ?_, ?_, by rw [row46Layer_tau]; exact hb, by rw [row46Layer_sigma]; exact hc,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  norm_num [row46Layer, Row46.tau, Row46.sigma, Row46.beta, Row46.c, Row46.eps, Row46.lam,
    Row46.lam', Row46.C1, Row46.xi]


/-! ## The middle's band discharge at the W8 root parameters

For the Walsh branch at the W8 root parameters (`K0 = W8.hK0 n`, `p0 = W8.hP0 n`,
`q = schedP p0 K0 + 2`, `d = dK row46 K0 = D + 1`, `ℓ = lK row46 K0`, `K = KK row46 K0`,
`a = fnewA row46 K0`), eventually: Theorem 6.5's (`thm:direct-fft`) shape conditions `MidShapeOK` and the paper-form
bands `MidFamilyBands row46Layer 1` at `q`, for every record width `w` with `q + 2 ≤ w ≤ 2q`, and
`P₀, P₁ ≤ q` for given cutoffs. The proof uses the integer bounds (`Row46Int.lean`,
`WalshOKW8.lean`: `2 ≤ d < ℓ ≤ K0`, `1 ≤ K ≤ d`, the integer bands `BandsNat row46 q K0` for
`16K0 ≤ q ≤ 64K0`) and `16 K0 ≤ P ≤ 32 K0`, `K0 → ∞` at the W8 parameters (`FamilyW8.lean`). -/

namespace Row46LayerAux

/-- `ε = 1/15` as the inverse of the natural number `15`. -/
theorem eps_eq_inv : ((Row46.eps : ℚ) : ℝ) = ((15 : ℕ) : ℝ)⁻¹ := by
  norm_num [Row46.eps]

/-- `x ≤ y^15` gives `x^ε ≤ y` (`ε = 1/15`). -/
theorem rpow_eps_le_of_le_pow {x y : ℕ} (h : x ≤ y ^ 15) :
    (x : ℝ) ^ ((Row46.eps : ℚ) : ℝ) ≤ y := by
  rw [eps_eq_inv]
  have h' : (x : ℝ) ≤ (y : ℝ) ^ 15 := by exact_mod_cast h
  calc (x : ℝ) ^ ((15 : ℕ) : ℝ)⁻¹ ≤ ((y : ℝ) ^ 15) ^ ((15 : ℕ) : ℝ)⁻¹ :=
        Real.rpow_le_rpow (by positivity) h' (by positivity)
    _ = y := Real.pow_rpow_inv_natCast (by positivity) (by norm_num)

/-- `x^15 ≤ y` gives `x ≤ y^ε` (`ε = 1/15`). -/
theorem le_rpow_eps_of_pow_le {x y : ℕ} (h : x ^ 15 ≤ y) :
    (x : ℝ) ≤ (y : ℝ) ^ ((Row46.eps : ℚ) : ℝ) := by
  rw [eps_eq_inv]
  have h' : (x : ℝ) ^ 15 ≤ (y : ℝ) := by exact_mod_cast h
  calc (x : ℝ) = ((x : ℝ) ^ 15) ^ ((15 : ℕ) : ℝ)⁻¹ :=
        (Real.pow_rpow_inv_natCast (by positivity) (by norm_num)).symm
    _ ≤ (y : ℝ) ^ ((15 : ℕ) : ℝ)⁻¹ := Real.rpow_le_rpow (by positivity) h' (by positivity)

/-- `2^ℓ` as a real power. -/
theorem two_pow_cast (ℓ : ℕ) : ((2 ^ ℓ : ℕ) : ℝ) = (2 : ℝ) ^ (ℓ : ℝ) := by
  rw [Real.rpow_natCast]
  push_cast
  rfl

end Row46LayerAux

open Row46LayerAux SubNLogN.Math.Bridge IntMulTM.Contracts

/-- **Shape conditions of Theorem 6.5** (`MidShapeOK`) for the `κ = 2^{-46}` row at `q = P + 2`,
once `2^15 ≤ K0` and `16 K0 ≤ P`, for every width `w ≥ q + 2`. -/
theorem midShapeOK_row46 {K0 P w : ℕ} (hK : 2 ^ 15 ≤ K0) (hP : 16 * K0 ≤ P) (hw : P + 2 + 2 ≤ w) :
    MidShapeOK (P + 2) (fnewL row46 K0) (KK row46 K0) w (fnewA row46 K0) := by
  have hd2 := two_le_dK46 hK
  have hdlt := dK46_lt_lK46 hK
  have hKK := KK46_bounds (K0 := K0) (by omega)
  have hlK := lK_le row46 K0 (by omega)
  have hK' : 32768 ≤ K0 := by simpa using hK
  have hl : fnewL row46 K0 = lK row46 K0 := rfl
  have hD : fnewD row46 K0 = dK row46 K0 - 1 := rfl
  refine ⟨by omega, by omega, by omega, by omega, hKK.1, by omega, fun i => ?_, hw⟩
  unfold fnewA
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The paper-form bands at `q`** (`MidFamilyBands row46Layer 1`) for the `κ = 2^{-46}` row,
once `2^15 ≤ K0` and `16 K0 ≤ q ≤ 64 K0`, for every width `w ≤ 2q`: `¼q^ε ≤ d ≤ q^ε`,
`2^{q/(128d)} ≤ 2^ℓ ≤ 2^{q/(8d)}`, `K = ⌊d^c⌋`, `w ≤ 2q`, `dℓ ≤ q` (`d = D + 1`). -/
theorem midFamilyBands_row46 {K0 q w : ℕ} (hK : 2 ^ 15 ≤ K0) (hlo : 16 * K0 ≤ q)
    (hhi : q ≤ 64 * K0) (hw : w ≤ 2 * q) :
    MidFamilyBands row46Layer 1 q (fnewD row46 K0) (fnewL row46 K0) (KK row46 K0) w := by
  have hd2 := two_le_dK46 hK
  have hB := bandsNat_row46_of_bounds hK hlo hhi
  unfold BandsNat at hB
  simp only [show row46.e₁ = 1 from rfl, show row46.e₂ = 15 from rfl, pow_one] at hB
  obtain ⟨hq4d, hdq, hq128, h8q, hdlq, -⟩ := hB
  have hD1 : fnewD row46 K0 + 1 = dK row46 K0 := by unfold fnewD; omega
  have hl : fnewL row46 K0 = lK row46 K0 := rfl
  have hdpos : (0 : ℝ) < (dK row46 K0 : ℝ) := by exact_mod_cast (by omega : 0 < dK row46 K0)
  unfold MidFamilyBands
  rw [hD1, hl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (1 / 4 : ℝ) * (q : ℝ) ^ ((Row46.eps : ℚ) : ℝ) ≤ (dK row46 K0 : ℝ)
    have h1 := rpow_eps_le_of_le_pow hq4d
    push_cast at h1
    linarith
  · show (dK row46 K0 : ℝ) ≤ 1 * (q : ℝ) ^ ((Row46.eps : ℚ) : ℝ)
    rw [one_mul]
    exact le_rpow_eps_of_pow_le hdq
  · show (2 : ℝ) ^ ((1 / 128 : ℝ) * q / (dK row46 K0 : ℝ)) ≤ ((2 ^ lK row46 K0 : ℕ) : ℝ)
    rw [two_pow_cast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [div_le_iff₀ hdpos]
    have h : (q : ℝ) ≤ 128 * (dK row46 K0 : ℝ) * (lK row46 K0 : ℝ) := by exact_mod_cast hq128
    linarith
  · show ((2 ^ lK row46 K0 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((1 / 8 : ℝ) * q / (dK row46 K0 : ℝ))
    rw [two_pow_cast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [le_div_iff₀ hdpos]
    have h : 8 * (dK row46 K0 : ℝ) * (lK row46 K0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h8q
    linarith
  · show KK row46 K0 = ⌊((dK row46 K0 : ℕ) : ℝ) ^ ((Row46.c : ℚ) : ℝ)⌋₊
    rw [← Row46.row46_c_eq]
    exact floorRatPow_eq_floor_rpow (show (0 : ℕ) < 2 ^ 50 by positivity)
  · show (w : ℝ) ≤ 2 * (q : ℝ)
    exact_mod_cast hw
  · omega

/-- **Band discharge for the Walsh middle at the W8 root parameters, any width.** For all cutoffs
`P₀, P₁` there is `N` such that for `n ≥ N` (`K0 = W8.hK0 n`, `p0 = W8.hP0 n`,
`q = schedP p0 K0 + 2`) and every record width `w` with `q + 2 ≤ w ≤ 2q`: `MidShapeOK` and
`MidFamilyBands row46Layer 1` hold at `(q, D, ℓ, K, w, a) = (q, fnewD row46 K0, fnewL row46 K0,
KK row46 K0, w, fnewA row46 K0)`, and `P₀ ≤ q`, `P₁ ≤ q`. -/
theorem midBands_w8_of_width (P₀ P₁ : ℕ) : ∃ N, ∀ n ≥ N, ∀ w : ℕ,
    schedP (W8.hP0 n) (W8.hK0 n) + 2 + 2 ≤ w → w ≤ 2 * (schedP (W8.hP0 n) (W8.hK0 n) + 2) →
    MidShapeOK (schedP (W8.hP0 n) (W8.hK0 n) + 2) (fnewL row46 (W8.hK0 n)) (KK row46 (W8.hK0 n)) w
      (fnewA row46 (W8.hK0 n)) ∧
    MidFamilyBands row46Layer 1 (schedP (W8.hP0 n) (W8.hK0 n) + 2) (fnewD row46 (W8.hK0 n))
      (fnewL row46 (W8.hK0 n)) (KK row46 (W8.hK0 n)) w ∧
    P₀ ≤ schedP (W8.hP0 n) (W8.hK0 n) + 2 ∧ P₁ ≤ schedP (W8.hP0 n) (W8.hK0 n) + 2 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (((tendsto_w8K.eventually_ge_atTop (2 ^ 15)).and eventually_w8_P_bounds).and
      (tendsto_w8K.eventually_ge_atTop (P₀ + P₁)))
  refine ⟨N, fun n hn w hw1 hw2 => ?_⟩
  obtain ⟨⟨hK, -, hP16, hP32⟩, hKP⟩ := hN n hn
  have hs : schedP (W8.hP0 n) (W8.hK0 n) = PBK (w8B n) (w8K n) := rfl
  have hK0 : W8.hK0 n = w8K n := rfl
  rw [hs, hK0]
  rw [hs] at hw1 hw2
  exact ⟨midShapeOK_row46 hK hP16 hw1, midFamilyBands_row46 hK (by omega) (by omega) hw2,
    by omega, by omega⟩

/-- **Pipe-width specialization of the band discharge** (`Machine/Pipe/BranchDefs.lean`, `md.MOK`), with the
bridge's internal record width `wI = schedP p0 K0 + K0 + 8` (satisfying
`q + K0 + 6 ≤ wI`): for all cutoffs `P₀, P₁`, eventually at the W8 root parameters
`MidShapeOK q ℓ K wI a ∧ MidFamilyBands row46Layer 1 q D ℓ K wI ∧ P₀ ≤ q ∧ P₁ ≤ q`. -/
def MidBandsW8Stmt : Prop :=
  ∀ P₀ P₁ : ℕ, ∃ N, ∀ n ≥ N,
    MidShapeOK (schedP (W8.hP0 n) (W8.hK0 n) + 2) (fnewL row46 (W8.hK0 n)) (KK row46 (W8.hK0 n))
      (schedP (W8.hP0 n) (W8.hK0 n) + W8.hK0 n + 8) (fnewA row46 (W8.hK0 n)) ∧
    MidFamilyBands row46Layer 1 (schedP (W8.hP0 n) (W8.hK0 n) + 2) (fnewD row46 (W8.hK0 n))
      (fnewL row46 (W8.hK0 n)) (KK row46 (W8.hK0 n))
      (schedP (W8.hP0 n) (W8.hK0 n) + W8.hK0 n + 8) ∧
    P₀ ≤ schedP (W8.hP0 n) (W8.hK0 n) + 2 ∧ P₁ ≤ schedP (W8.hP0 n) (W8.hK0 n) + 2

/-- `MidBandsW8Stmt` holds (from `midBands_w8_of_width`; `q + 2 ≤ wI ≤ 2q` since
`K0 + 4 ≤ schedP p0 K0`). -/
theorem midBandsW8_holds : MidBandsW8Stmt := by
  intro P₀ P₁
  obtain ⟨N, hN⟩ := midBands_w8_of_width P₀ P₁
  refine ⟨N, fun n hn => hN n hn _ (by omega) ?_⟩
  have h : W8.hK0 n + 4 ≤ schedP (W8.hP0 n) (W8.hK0 n) := by unfold schedP; omega
  omega

end SubNLogN.Assembly
