import SubNLogN.Math.Bridge.RootW8
import WP.W11b.Root

/-!
# Bridge: `RootW8_FnewStmt` from Theorem 4.7

`rootW8_Fnew_of` proves `RootW8_FnewStmt` (`Math/Bridge/RootW8.lean`; for every nearest rounding
`rr` and the map `FnewOfR rr`) from the contracts `Bridge_precisionStmt` (Theorem 4.7) and
`WalshOK_balancedStmt`. `RootPackingRndStmt` is not used: its
single chunk count `N` with `2N ≤ 2^{K0}` does not cover `k1 ≠ k2` with only `k1 + k2 ≤ 2^{K0}`.

Route (all helpers live in `SubNLogN.Math.Bridge.RootW8Proof`):
1. On an input of size `2^{K0}` that passes the input guard `ArrW (p0 + p_in + 1) x`,
   `FnewOfR rr ρ Tab mid p_in cSpec` is `encodeArr p0 ∘ br ∘ decodeArr p_in R`, where
   `br = bridgeFixedR rr p0 (schedP p0 K0) (fnewShape ρ K0) (Tab p0 K0) (mid p0 K0)` and
   `R = totalLen (fnewShape ρ K0) = 2^{K0}` (`FnewOfR_eq_of_size`). The guard holds at both root
   calls by `WP.W11b.arrW_input`: the decoded inputs have modulus `≤ √2 ≤ 2^1` (at `p_in = b`) and
   `≤ 85/32 ≤ 2^2` (at `p_in = p0`), and `1 + b + 3 ≤ p0 + b + 1`, `2 + p0 + 3 ≤ p0 + p0 + 1`.
2. Theorem 4.7 gives `BrOK R p0 br` (`brOK_bridgeFixed`): on `(p0+2)`-grid inputs of norm `≤ 2^{p0}`
   the output is on the `(p0+2)`-grid and within `2^{-p0} max(1,‖x‖)` of `F_R x`. The constant
   `√2/8 + 2^{-12} + 2^{-23}` is `≤ 1`.
3. Exact recovery is IntMul's transform-generic `IntMul.dftApproxConvApprox_round_eq`. It allows
   `k1 + k2 ≤ 2^{K0}` and uses IntMul's half-up `complexQuantize` and floor extraction. We apply it to
   `gridF R p0 br`, which is `br` on grid inputs and the exact `dft1D` elsewhere (`gridF_err`).
   `encodeArr` is exact on the grid, so the integer stages (`rootSquareV`, `rootExtractV`,
   `reconstructChunksTree`) are read off as in IntMul's
   `computablePaperFastDFTMultiply_faithful_eq_mul`.
4. Norms: `‖ŷ‖ ≤ (9/8)√2`, `‖ŵ‖ ≤ 85/32`, `‖ẑ‖ ≤ 765/256 ≤ 4`. Widths come from `WP.W11b.arrW_input`
   and `WP.W11b.bitLen_digit_le`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common SubNLogN.Math.Cost TMFw.Contracts TMFw.Contracts.W9
open scoped BigOperators

namespace RootW8Proof

/-! ## Grid and encoding facts -/

/-- A decoded integer pair lies on the `(p+2)`-grid. -/
theorem onGrid_toScaledComplex (p : ℕ) (z : ℤ × ℤ) :
    OnGrid (p + 2) (IntMul.toScaledComplex p z) :=
  ⟨⟨z.1, by simp [IntMul.toScaledComplex, gridUnit, div_eq_mul_inv]⟩,
    ⟨z.2, by simp [IntMul.toScaledComplex, gridUnit, div_eq_mul_inv]⟩⟩

/-- Rounding `x·2^q` is exact for `x` on the `q`-grid. -/
theorem round_mul_pow_of_onGridR {q : ℕ} {x : ℝ} (h : OnGridR q x) :
    ((round (x * (2 : ℝ) ^ q) : ℤ) : ℝ) = x * (2 : ℝ) ^ q := by
  obtain ⟨a, rfl⟩ := h
  have ha : (a : ℝ) * gridUnit q * (2 : ℝ) ^ q = (a : ℝ) := by
    unfold gridUnit
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero q two_ne_zero), mul_one]
  rw [ha, round_intCast]

/-- `encodeC` is inverted by `toScaledComplex` on the `(p+2)`-grid. -/
theorem toScaledComplex_encodeC {p : ℕ} {z : ℂ} (h : OnGrid (p + 2) z) :
    IntMul.toScaledComplex p (encodeC p z) = z := by
  apply Complex.ext
  · show ((round (z.re * (2 : ℝ) ^ (p + 2)) : ℤ) : ℝ) / (2 : ℝ) ^ (p + 2) = z.re
    rw [round_mul_pow_of_onGridR h.1, mul_div_assoc, div_self (pow_ne_zero _ two_ne_zero),
      mul_one]
  · show ((round (z.im * (2 : ℝ) ^ (p + 2)) : ℤ) : ℝ) / (2 : ℝ) ^ (p + 2) = z.im
    rw [round_mul_pow_of_onGridR h.2, mul_div_assoc, div_self (pow_ne_zero _ two_ne_zero),
      mul_one]

/-- The imaginary integer of `encodeC` on the grid. -/
theorem encodeC_snd {p : ℕ} {z : ℂ} (h : OnGrid (p + 2) z) :
    (((encodeC p z).2 : ℤ) : ℝ) = z.im * (2 : ℝ) ^ (p + 2) :=
  round_mul_pow_of_onGridR h.2

theorem size_encodeArr (p : ℕ) {R : ℕ} (y : Fin R → ℂ) : (encodeArr p y).size = R := by
  simp [encodeArr]

theorem read1D_encodeArr (p : ℕ) {R : ℕ} (y : Fin R → ℂ) {u : ℕ} (hu : u < R) :
    IntMul.read1D (encodeArr p y) u = encodeC p (y ⟨u, hu⟩) :=
  IntMul.read1D_ofFn_of_lt R _ hu

theorem toScaledComplex_read1D_encodeArr {p R : ℕ} {y : Fin R → ℂ}
    (hy : ∀ f, OnGrid (p + 2) (y f)) {u : ℕ} (hu : u < R) :
    IntMul.toScaledComplex p (IntMul.read1D (encodeArr p y) u) = y ⟨u, hu⟩ := by
  rw [read1D_encodeArr p y hu, toScaledComplex_encodeC (hy _)]

/-! ## The bridge contract and its extension to all inputs -/

/-- The conclusion of Theorem 4.7 in the form used here (error constant `≤ 1`): on `(p+2)`-grid
inputs of norm `≤ 2^p`, `br` returns `(p+2)`-grid outputs within `2^{-p} max(1,‖x‖)` of `F_R x`. -/
def BrOK (R p : ℕ) (br : (Fin R → ℂ) → (Fin R → ℂ)) : Prop :=
  ∀ x : Fin R → ℂ, (∀ j, OnGrid (p + 2) (x j)) → ‖x‖ ≤ (2 : ℝ) ^ p →
    (∀ f, OnGrid (p + 2) (br x f)) ∧ ‖br x - dft R x‖ ≤ (2 : ℝ) ^ (-(p : ℤ)) * max 1 ‖x‖

open Classical in
/-- `br` extended to all of `ℕ → ℂ`, as an approximate DFT in IntMul's format: on inputs whose
first `R` entries lie on the `(p+2)`-grid with modulus `≤ 2^p` it is `br` (and `0` at indices
`≥ R`); on all other inputs it is the exact `IntMul.dft1D R`. -/
noncomputable def gridF (R p : ℕ) (br : (Fin R → ℂ) → (Fin R → ℂ)) (x : ℕ → ℂ) (u : ℕ) : ℂ :=
  if (∀ k < R, OnGrid (p + 2) (x k)) ∧ (∀ k < R, ‖x k‖ ≤ (2 : ℝ) ^ p) then
    (if hu : u < R then br (fun j => x j) ⟨u, hu⟩ else 0)
  else IntMul.dft1D R x u

/-- `IntMul.dft1D R x` at `u < R` is `F_R` of the restriction of `x` to `[R]`. -/
theorem dft1D_eq_dft (R : ℕ) (x : ℕ → ℂ) {u : ℕ} (hu : u < R) :
    IntMul.dft1D R x u = dft R (fun j : Fin R => x j) ⟨u, hu⟩ := by
  rw [dft_eq_intMul_dft1D]
  unfold IntMul.dft1D
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  dsimp only
  rw [dif_pos (Finset.mem_range.1 hj)]

theorem gridF_eq {R p : ℕ} (br : (Fin R → ℂ) → (Fin R → ℂ)) (x : ℕ → ℂ)
    (hg : ∀ k < R, OnGrid (p + 2) (x k)) (hn : ∀ k < R, ‖x k‖ ≤ (2 : ℝ) ^ p) {u : ℕ}
    (hu : u < R) :
    gridF R p br x u = br (fun j => x j) ⟨u, hu⟩ := by
  unfold gridF
  rw [if_pos ⟨hg, hn⟩, dif_pos hu]

/-- `gridF R p br` satisfies the error hypothesis of `IntMul.dftApproxConvApprox_round_eq`. -/
theorem gridF_err {R p : ℕ} {br : (Fin R → ℂ) → (Fin R → ℂ)} (hbr : BrOK R p br)
    (x : ℕ → ℂ) (M : ℝ) (hM : 1 ≤ M) (hx : ∀ k < R, ‖x k‖ ≤ M) (u : ℕ) (hu : u < R) :
    ‖gridF R p br x u - IntMul.dft1D R x u‖ ≤ (2 : ℝ) ^ (-(p : ℤ)) * M := by
  by_cases hc : (∀ k < R, OnGrid (p + 2) (x k)) ∧ (∀ k < R, ‖x k‖ ≤ (2 : ℝ) ^ p)
  · obtain ⟨hg, hn⟩ := hc
    rw [gridF_eq br x hg hn hu, dft1D_eq_dft R x hu]
    have hg' : ∀ j : Fin R, OnGrid (p + 2) (x j) := fun j => hg j j.is_lt
    have hn' : ‖(fun j : Fin R => x j)‖ ≤ (2 : ℝ) ^ p :=
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => hn j j.is_lt
    have hxM : ‖(fun j : Fin R => x j)‖ ≤ M :=
      (pi_norm_le_iff_of_nonneg (by linarith)).2 fun j => hx j j.is_lt
    calc ‖br (fun j => x j) ⟨u, hu⟩ - dft R (fun j : Fin R => x j) ⟨u, hu⟩‖
        = ‖(br (fun j => x j) - dft R (fun j : Fin R => x j)) ⟨u, hu⟩‖ := rfl
      _ ≤ ‖br (fun j => x j) - dft R (fun j : Fin R => x j)‖ := norm_le_pi_norm _ _
      _ ≤ (2 : ℝ) ^ (-(p : ℤ)) * max 1 ‖(fun j : Fin R => x j)‖ := (hbr _ hg' hn').2
      _ ≤ (2 : ℝ) ^ (-(p : ℤ)) * M := by
          gcongr
          exact max_le hM hxM
  · unfold gridF
    rw [if_neg hc, sub_self, norm_zero]
    positivity

/-! ## Theorem 4.7 for `FnewOf` -/

theorem bridge_const_le_one :
    Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ) ≤ 1 := by
  have hs : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h12 : (2 : ℝ) ^ (-12 : ℤ) ≤ 1 / 4 := by norm_num
  have h23 : (2 : ℝ) ^ (-23 : ℤ) ≤ 1 / 4 := by norm_num
  linarith

/-- Theorem 4.7 at `p = p0 = rootPrecision b K0` for the bridge run by `FnewOfR rr`. -/
theorem brOK_bridgeFixed (hprec : Bridge_precisionStmt) (hbal : WalshOK_balancedStmt)
    (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr) (ρ : RowExps) (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ))
    (b K0 : ℕ) (hb : 1 ≤ b) (hOK : WalshOK ρ (IntMul.rootPrecision b K0) K0 = true)
    (hT : TablesCertifiedR rr
      (alphaDefault (schedOmega (IntMul.rootPrecision b K0) K0 (fnewD ρ K0 + 1)))
      (schedP (IntMul.rootPrecision b K0) K0) (fnewShape ρ K0)
      (Tab (IntMul.rootPrecision b K0) K0))
    (Emid : ℝ) (δmid : ℕ)
    (hmid : IsMiddleTransform (fnewShape ρ K0) (schedP (IntMul.rootPrecision b K0) K0) Emid
      δmid (mid (IntMul.rootPrecision b K0) K0)) :
    BrOK (totalLen (fnewShape ρ K0)) (IntMul.rootPrecision b K0)
      (bridgeFixedR rr (IntMul.rootPrecision b K0) (schedP (IntMul.rootPrecision b K0) K0)
        (fnewShape ρ K0) (Tab (IntMul.rootPrecision b K0) K0)
        (mid (IntMul.rootPrecision b K0) K0)) := by
  intro x hx hxn
  have hp : max 8 K0 ≤ IntMul.rootPrecision b K0 := by
    unfold IntMul.rootPrecision
    omega
  obtain ⟨hg, he⟩ := hprec rr hrr (fnewShape ρ K0) K0 (fnewL ρ K0) (IntMul.rootPrecision b K0)
    (hbal ρ _ K0 hOK) hp x hx hxn (Tab _ K0) hT Emid δmid (mid _ K0) hmid
  refine ⟨hg, le_of_lt (lt_of_lt_of_le he ?_)⟩
  have hnn : 0 ≤ (2 : ℝ) ^ (-(IntMul.rootPrecision b K0 : ℤ)) * max 1 ‖x‖ := by positivity
  calc (Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ)) *
        (2 : ℝ) ^ (-(IntMul.rootPrecision b K0 : ℤ)) * max 1 ‖x‖
      = (Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ)) *
        ((2 : ℝ) ^ (-(IntMul.rootPrecision b K0 : ℤ)) * max 1 ‖x‖) := by ring
    _ ≤ 1 * ((2 : ℝ) ^ (-(IntMul.rootPrecision b K0 : ℤ)) * max 1 ‖x‖) :=
        mul_le_mul_of_nonneg_right bridge_const_le_one hnn
    _ = _ := one_mul _

/-- `FnewOfR rr` on an input of size `2^{K0}` that passes the input guard. -/
theorem FnewOfR_eq_of_size (rr : ℕ → ℝ → ℝ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ))
    (p_in : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (K0 : ℕ) (x : Array (ℤ × ℤ))
    (hx : x.size = 2 ^ K0) (hguard : ArrW (cSpec.p + p_in + 1) x) :
    FnewOfR rr ρ Tab mid p_in cSpec x =
      encodeArr cSpec.p (bridgeFixedR rr cSpec.p (schedP cSpec.p K0) (fnewShape ρ K0)
        (Tab cSpec.p K0) (mid cSpec.p K0) (decodeArr p_in (totalLen (fnewShape ρ K0)) x)) := by
  have hlog : Nat.log2 x.size = K0 := by rw [hx, Nat.log2_two_pow]
  rw [FnewOfR_eq_bridge rr ρ Tab mid p_in cSpec x hguard, hlog]

/-! ## Digit extraction -/

/-- The root digit extraction `divRoundPow2 · 9` (a shift by 9 at `p0 = 2b + 2K0 + 6`) of the
imaginary integer of `encodeC p0 w` is IntMul's rounding `⌊Im(conj w)·2^{2b+2K0-1} + 1/2⌋`. -/
theorem divRoundPow2_encodeC_eq_floor {b K0 p0 : ℕ} (hp0 : p0 = 2 * b + 2 * K0 + 6) {w : ℂ}
    (hw : OnGrid (p0 + 2) w) :
    IntMul.divRoundPow2 (-(encodeC p0 w).2) 9 =
      ⌊(star w).im * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) + 1 / 2⌋ := by
  have hn : (((encodeC p0 w).2 : ℤ) : ℝ) = w.im * (2 : ℝ) ^ (p0 + 2) := encodeC_snd hw
  have hpow : (2 : ℝ) ^ (p0 + 2) = (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) * 512 := by
    rw [show (512 : ℝ) = (2 : ℝ) ^ (9 : ℤ) by norm_num, ← zpow_add₀ two_ne_zero, ← zpow_natCast]
    congr 1
    rw [hp0]
    push_cast
    ring
  have hE : (0 : ℝ) < (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) := by positivity
  have hdiv : IntMul.divRoundPow2 (-(encodeC p0 w).2) 9 = (-(encodeC p0 w).2 + 256) / 512 := by
    unfold IntMul.divRoundPow2
    rw [if_neg (by norm_num)]
    norm_num
  rw [hdiv, ← IntMul.floor_intCast_div_eq_ediv _ 512 (by norm_num)]
  congr 1
  have hwim : w.im = (((encodeC p0 w).2 : ℤ) : ℝ) /
      ((2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) * 512) := by
    rw [← hpow, hn, mul_div_assoc, div_self (pow_ne_zero _ two_ne_zero), mul_one]
  rw [Complex.star_def, Complex.conj_im, hwim]
  push_cast
  field_simp
  ring

/-! ## The root pipeline for an abstract bridge -/

/-- The conclusion of `RootW8_FnewStmt` for any length-`R` (`R = 2^{K0}`) procedure `br` with
`BrOK R p0 br`, run through `encodeArr p0 ∘ br ∘ decodeArr p_in R`. -/
theorem rootFacts_core {b K0 k1 k2 A1 A2 R p0 : ℕ} (hb : 1 ≤ b) (hk : k1 + k2 ≤ 2 ^ K0)
    (hA1 : A1 < 2 ^ (b * k1)) (hA2 : A2 < 2 ^ (b * k2)) (hR : R = 2 ^ K0)
    (hp0 : p0 = 2 * b + 2 * K0 + 6) {br : (Fin R → ℂ) → (Fin R → ℂ)} (hbr : BrOK R p0 br)
    {x0 yF x1 yI : Array (ℤ × ℤ)} (hx0 : x0 = rootPackV b K0 k1 k2 A1 A2)
    (hyF : ArrW (p0 + b + 1) x0 → yF = encodeArr p0 (br (decodeArr b R x0)))
    (hx1 : x1 = rootSquareV p0 K0 yF)
    (hyI : ArrW (p0 + p0 + 1) x1 → yI = encodeArr p0 (br (decodeArr p0 R x1))) :
    yF.size = 2 ^ K0 ∧ yI.size = 2 ^ K0 ∧
      (∀ u < 2 ^ K0, ‖IntMul.toScaledComplex p0 (IntMul.read1D yF u)‖ ≤ 4) ∧
      (∀ u < 2 ^ K0, ‖IntMul.toScaledComplex p0 (IntMul.read1D yI u)‖ ≤ 4) ∧
      ArrW (4 * p0) x0 ∧ ArrW (4 * p0) yF ∧ ArrW (4 * p0) x1 ∧ ArrW (4 * p0) yI ∧
      (∀ c ∈ rootDigits b K0 k1 k2 yI, bitLen c ≤ 4 * p0) ∧
      IntMul.reconstructChunksTree b (rootDigits b K0 k1 k2 yI) = A1 * A2 := by
  subst hR
  have hp0r : IntMul.rootPrecision b K0 = p0 := by
    unfold IntMul.rootPrecision
    omega
  have hp8 : 8 ≤ p0 := by omega
  -- numeric constants
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have he : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ 1 / 8 := by
    calc (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (2 : ℝ) ^ (-3 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 / 8 := by norm_num
  have hpow4 : (4 : ℝ) ≤ (2 : ℝ) ^ p0 := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p0 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hq : IntMul.complexQuantizeMaxErr p0 ≤ 1 / 8 := by
    have := IntMul.complexQuantizeMaxErr_lt p0
    linarith
  -- forward stage: the decoded input and `ŷ = br x`
  set xin : Fin (2 ^ K0) → ℂ := decodeArr b (2 ^ K0) x0 with hxin
  have hxin_eq : ∀ j : Fin (2 ^ K0), xin j = IntMul.packNormalizedChunks b k1 k2 A1 A2 j := by
    intro j
    rw [hxin, hx0]
    exact IntMul.toScaledComplex_computablePackChunksExact_eq b k1 k2 (2 ^ K0) A1 A2 j j.is_lt
  have hxin_grid : ∀ j, OnGrid (p0 + 2) (xin j) := fun j =>
    OnGrid.mono (by omega) (onGrid_toScaledComplex b _)
  have hxin_norm : ‖xin‖ ≤ Real.sqrt 2 :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg 2)).2 fun j => by
      rw [hxin_eq]
      exact IntMul.norm_packNormalizedChunks_le_sqrt_two _ _ _ _ _ _
  have hx0_size : x0.size = 2 ^ K0 := by rw [hx0]; exact WP.W11b.size_rootPackV _ _ _ _ _ _
  replace hyF := hyF (WP.W11b.arrW_input (p := 1) (p_in := b) hx0_size
    (fun k hk => (norm_le_pi_norm xin ⟨k, hk⟩).trans (hxin_norm.trans (by rw [pow_one]; linarith)))
    (by omega))
  obtain ⟨hy_grid, hy_err⟩ := hbr xin hxin_grid (hxin_norm.trans (by linarith))
  set y := br xin with hy
  have hy_norm : ∀ f, ‖y f‖ ≤ 9 / 8 * Real.sqrt 2 := by
    intro f
    have h1 : ‖dft (2 ^ K0) xin f‖ ≤ Real.sqrt 2 :=
      (norm_le_pi_norm (dft (2 ^ K0) xin) f).trans ((norm_dft_le _ xin).trans hxin_norm)
    have h2 : ‖y f - dft (2 ^ K0) xin f‖ ≤ 1 / 8 * Real.sqrt 2 :=
      calc ‖y f - dft (2 ^ K0) xin f‖ = ‖(y - dft (2 ^ K0) xin) f‖ := rfl
        _ ≤ ‖y - dft (2 ^ K0) xin‖ := norm_le_pi_norm _ f
        _ ≤ (2 : ℝ) ^ (-(p0 : ℤ)) * max 1 ‖xin‖ := hy_err
        _ ≤ 1 / 8 * Real.sqrt 2 :=
            mul_le_mul he (max_le hs1 hxin_norm) (by positivity) (by norm_num)
    have h3 := norm_add_le (y f - dft (2 ^ K0) xin f) (dft (2 ^ K0) xin f)
    rw [sub_add_cancel] at h3
    linarith
  have hyF_size : yF.size = 2 ^ K0 := by rw [hyF, size_encodeArr]
  have hyF_read : ∀ u (hu : u < 2 ^ K0),
      IntMul.toScaledComplex p0 (IntMul.read1D yF u) = y ⟨u, hu⟩ := by
    intro u hu
    rw [hyF]
    exact toScaledComplex_read1D_encodeArr hy_grid hu
  -- squaring stage: `ŵ = conj(round(ŷ²))`
  set w : Fin (2 ^ K0) → ℂ := decodeArr p0 (2 ^ K0) x1 with hw
  have hw_eq : ∀ j : Fin (2 ^ K0), w j = star (IntMul.complexQuantize p0 (y j * y j)) := by
    intro j
    rw [hw, hx1]
    show IntMul.toScaledComplex p0 (IntMul.read1D (rootSquareV p0 K0 yF) j) = _
    unfold rootSquareV
    rw [IntMul.read1D_runSequentialScanSteps_eq _ _ _ j.is_lt, IntMul.toScaledComplex_gConj,
      IntMul.toScaledComplex_gMulScaled_eq_complexQuantize_mul, hyF_read j j.is_lt]
  have hw_grid : ∀ j, OnGrid (p0 + 2) (w j) := fun j => onGrid_toScaledComplex p0 _
  have hw_norm_pt : ∀ j, ‖w j‖ ≤ 85 / 32 := by
    intro j
    rw [hw_eq, norm_star]
    have h1 := IntMul.norm_complexQuantize_le p0 (y j * y j)
    have h2 : ‖y j * y j‖ ≤ 81 / 32 := by
      rw [norm_mul]
      calc ‖y j‖ * ‖y j‖ ≤ (9 / 8 * Real.sqrt 2) * (9 / 8 * Real.sqrt 2) :=
            mul_le_mul (hy_norm j) (hy_norm j) (norm_nonneg _) (by positivity)
        _ = 81 / 64 * (Real.sqrt 2 * Real.sqrt 2) := by ring
        _ = 81 / 32 := by rw [hss]; norm_num
    linarith
  have hw_norm : ‖w‖ ≤ 85 / 32 := (pi_norm_le_iff_of_nonneg (by norm_num)).2 hw_norm_pt
  have hx1_size : x1.size = 2 ^ K0 := by rw [hx1]; exact WP.W11b.size_rootSquareV _ _ _
  have h4 : (85 / 32 : ℝ) ≤ (2 : ℝ) ^ 2 := by norm_num
  replace hyI := hyI (WP.W11b.arrW_input (p := 2) (p_in := p0) hx1_size
    (fun k hk => (norm_le_pi_norm w ⟨k, hk⟩).trans (hw_norm.trans h4)) (by omega))
  obtain ⟨hz_grid, hz_err⟩ := hbr w hw_grid (hw_norm.trans (by linarith))
  set z := br w with hz
  have hz_norm : ∀ f, ‖z f‖ ≤ 765 / 256 := by
    intro f
    have h1 : ‖dft (2 ^ K0) w f‖ ≤ 85 / 32 :=
      (norm_le_pi_norm (dft (2 ^ K0) w) f).trans ((norm_dft_le _ w).trans hw_norm)
    have h2 : ‖z f - dft (2 ^ K0) w f‖ ≤ 1 / 8 * (85 / 32) :=
      calc ‖z f - dft (2 ^ K0) w f‖ = ‖(z - dft (2 ^ K0) w) f‖ := rfl
        _ ≤ ‖z - dft (2 ^ K0) w‖ := norm_le_pi_norm _ f
        _ ≤ (2 : ℝ) ^ (-(p0 : ℤ)) * max 1 ‖w‖ := hz_err
        _ ≤ 1 / 8 * (85 / 32) :=
            mul_le_mul he (max_le (by norm_num) hw_norm) (by positivity) (by norm_num)
    have h3 := norm_add_le (z f - dft (2 ^ K0) w f) (dft (2 ^ K0) w f)
    rw [sub_add_cancel] at h3
    linarith
  -- inverse stage
  have hyI_size : yI.size = 2 ^ K0 := by rw [hyI, size_encodeArr]
  have hyI_read : ∀ u (hu : u < 2 ^ K0),
      IntMul.toScaledComplex p0 (IntMul.read1D yI u) = z ⟨u, hu⟩ := by
    intro u hu
    rw [hyI]
    exact toScaledComplex_read1D_encodeArr hz_grid hu
  -- exact recovery through `IntMul.dftApproxConvApprox_round_eq` applied to `gridF`
  have hxAB_grid : ∀ k < 2 ^ K0,
      OnGrid (p0 + 2) (IntMul.packNormalizedChunks b k1 k2 A1 A2 k) := fun k hk => by
    have h := hxin_grid ⟨k, hk⟩
    rwa [hxin_eq] at h
  have hxAB_norm : ∀ k < 2 ^ K0,
      ‖IntMul.packNormalizedChunks b k1 k2 A1 A2 k‖ ≤ (2 : ℝ) ^ p0 := fun k _ =>
    (IntMul.norm_packNormalizedChunks_le_sqrt_two _ _ _ _ _ _).trans (by linarith)
  have hgF1 : ∀ u (hu : u < 2 ^ K0),
      gridF (2 ^ K0) p0 br (IntMul.packNormalizedChunks b k1 k2 A1 A2) u = y ⟨u, hu⟩ := by
    intro u hu
    have hfun : (fun j : Fin (2 ^ K0) => IntMul.packNormalizedChunks b k1 k2 A1 A2 j) = xin :=
      funext fun j => (hxin_eq j).symm
    rw [gridF_eq br _ hxAB_grid hxAB_norm hu, hfun]
  have hS : ∀ u (hu : u < 2 ^ K0),
      star (IntMul.complexQuantize p0
        (gridF (2 ^ K0) p0 br (IntMul.packNormalizedChunks b k1 k2 A1 A2) u ^ 2)) = w ⟨u, hu⟩ := by
    intro u hu
    rw [hgF1 u hu, sq, hw_eq]
  have hS_grid : ∀ k < 2 ^ K0, OnGrid (p0 + 2) (star (IntMul.complexQuantize p0
      (gridF (2 ^ K0) p0 br (IntMul.packNormalizedChunks b k1 k2 A1 A2) k ^ 2))) :=
    fun k hk => by rw [hS k hk]; exact hw_grid _
  have hS_norm : ∀ k < 2 ^ K0, ‖star (IntMul.complexQuantize p0
      (gridF (2 ^ K0) p0 br (IntMul.packNormalizedChunks b k1 k2 A1 A2) k ^ 2))‖ ≤
        (2 : ℝ) ^ p0 :=
    fun k hk => by rw [hS k hk]; exact (hw_norm_pt _).trans (by linarith)
  have hgF2 : ∀ j (hj : j < 2 ^ K0),
      gridF (2 ^ K0) p0 br (fun u => star (IntMul.complexQuantize p0
        (gridF (2 ^ K0) p0 br (IntMul.packNormalizedChunks b k1 k2 A1 A2) u ^ 2))) j =
        z ⟨j, hj⟩ := by
    intro j hj
    have hfun : (fun i : Fin (2 ^ K0) => star (IntMul.complexQuantize p0
        (gridF (2 ^ K0) p0 br (IntMul.packNormalizedChunks b k1 k2 A1 A2) i ^ 2))) = w :=
      funext fun i => hS i i.is_lt
    rw [gridF_eq br _ hS_grid hS_norm hj, hfun]
  have hdigit : ∀ j, j < k1 + k2 →
      IntMul.read1D (rootExtractV (IntMul.rootPrecision b K0) b K0 yI) j =
        (IntMul.polyMulList (IntMul.splitChunks b k1 A1) (IntMul.splitChunks b k2 A2)).getD j 0 := by
    intro j hjk
    have hj : j < 2 ^ K0 := by omega
    have hround := IntMul.dftApproxConvApprox_round_eq (gridF (2 ^ K0) p0 br) b K0 k1 k2 A1 A2
      (fun x M hM hx u hu => by rw [hp0r]; exact gridF_err hbr x M hM hx u hu) hk j hj
    dsimp only at hround
    rw [hp0r, hgF2 j hj] at hround
    unfold rootExtractV
    rw [IntMul.read1D_runSequentialScanSteps_eq _ _ _ hj,
      IntMulTM.Contracts.W8_extractRootSlot_shift_holds, hyI, read1D_encodeArr p0 z hj,
      divRoundPow2_encodeC_eq_floor hp0 (hz_grid _), hround, Int.toNat_natCast]
  have hmap : rootDigits b K0 k1 k2 yI = (List.range (k1 + k2)).map (fun j =>
      (IntMul.polyMulList (IntMul.splitChunks b k1 A1) (IntMul.splitChunks b k2 A2)).getD j 0) := by
    unfold rootDigits
    exact List.map_congr_left fun j hj => hdigit j (List.mem_range.1 hj)
  have hpoly_len : (IntMul.polyMulList (IntMul.splitChunks b k1 A1)
      (IntMul.splitChunks b k2 A2)).length ≤ k1 + k2 := by
    have h := IntMul.length_polyMulList_le (IntMul.splitChunks b k1 A1) (IntMul.splitChunks b k2 A2)
    rwa [IntMul.length_splitChunks, IntMul.length_splitChunks] at h
  have hrec : IntMul.reconstructChunksTree b (rootDigits b K0 k1 k2 yI) = A1 * A2 := by
    rw [hmap, IntMul.reconstructChunksTree_eq_reconstructChunks,
      IntMul.reconstructChunks_eq_evalRadix, IntMul.evalRadix_range_getD (2 ^ b) _ (k1 + k2) hpoly_len,
      ← IntMul.reconstructChunks_eq_evalRadix]
    exact IntMul.reconstructChunks_polyMulList_splitChunks b k1 k2 A1 A2
      (by rw [← pow_mul]; exact hA1) (by rw [← pow_mul]; exact hA2)
  -- widths
  have hwx0 : ArrW (4 * p0) x0 := WP.W11b.arrW_input (p := 1) (p_in := b) hx0_size
    (fun k hk => (norm_le_pi_norm xin ⟨k, hk⟩).trans (hxin_norm.trans (by rw [pow_one]; linarith)))
    (by omega)
  have hwyF : ArrW (4 * p0) yF := WP.W11b.arrW_input (p := 2) (p_in := p0) hyF_size
    (fun k hk => by rw [hyF_read k hk]; exact (hy_norm _).trans (by nlinarith)) (by omega)
  have hwx1 : ArrW (4 * p0) x1 := WP.W11b.arrW_input (p := 2) (p_in := p0) hx1_size
    (fun k hk => (norm_le_pi_norm w ⟨k, hk⟩).trans (hw_norm.trans h4)) (by omega)
  have hwyI : ArrW (4 * p0) yI := WP.W11b.arrW_input (p := 2) (p_in := p0) hyI_size
    (fun k hk => by rw [hyI_read k hk]; exact (hz_norm _).trans (by norm_num)) (by omega)
  have hdw : ∀ c ∈ rootDigits b K0 k1 k2 yI, bitLen c ≤ 4 * p0 := by
    intro c hc
    simp only [rootDigits, List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    have hj' : j < 2 ^ K0 := by omega
    unfold rootExtractV
    rw [IntMul.read1D_runSequentialScanSteps_eq _ _ j hj',
      IntMulTM.Contracts.W8_extractRootSlot_shift_holds]
    exact WP.W11b.bitLen_digit_le (WP.W11b.entryW_read1D_of_arrW hwyI j) le_rfl
  refine ⟨hyF_size, hyI_size, fun u hu => ?_, fun u hu => ?_, hwx0, hwyF, hwx1, hwyI, hdw, hrec⟩
  · rw [hyF_read u hu]
    exact (hy_norm _).trans (by nlinarith)
  · rw [hyI_read u hu]
    exact (hz_norm _).trans (by norm_num)

end RootW8Proof

open RootW8Proof in
/-- `RootW8_FnewStmt` (for every nearest rounding `rr` and `FnewOfR rr`) from Theorem 4.7
(`Bridge_precisionStmt`) and `WalshOK_balancedStmt`. Exact recovery is IntMul's transform-generic
`dftApproxConvApprox_round_eq`; `RootPackingRndStmt` is not needed. -/
theorem rootW8_Fnew_of (hprec : Bridge_precisionStmt) (hbal : WalshOK_balancedStmt) :
    RootW8_FnewStmt := by
  intro rr hrr ρ Tab mid b K0 k1 k2 A1 A2 cSpec hb hk hA1 hA2 hp hOK hT Emid δmid hmid
  dsimp only
  have hR : totalLen (fnewShape ρ K0) = 2 ^ K0 := (hbal ρ _ K0 hOK).2.1
  have hbr := brOK_bridgeFixed hprec hbal rr hrr ρ Tab mid b K0 hb hOK hT Emid δmid hmid
  have hF : ∀ (p_in : ℕ) (x : Array (ℤ × ℤ)), x.size = 2 ^ K0 →
      ArrW (IntMul.rootPrecision b K0 + p_in + 1) x →
      FnewOfR rr ρ Tab mid p_in cSpec x =
        encodeArr (IntMul.rootPrecision b K0)
          (bridgeFixedR rr (IntMul.rootPrecision b K0) (schedP (IntMul.rootPrecision b K0) K0)
            (fnewShape ρ K0) (Tab (IntMul.rootPrecision b K0) K0)
            (mid (IntMul.rootPrecision b K0) K0) (decodeArr p_in (totalLen (fnewShape ρ K0)) x)) := by
    intro p_in x hx hguard
    rw [FnewOfR_eq_of_size rr ρ Tab mid p_in cSpec K0 x hx (by rwa [hp]), hp]
  exact rootFacts_core hb hk hA1 hA2 hR rfl hbr rfl
    (hF b _ (WP.W11b.size_rootPackV _ _ _ _ _ _)) rfl (hF _ _ (WP.W11b.size_rootSquareV _ _ _))

end SubNLogN.Math.Bridge
