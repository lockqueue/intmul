/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.BranchDefs
import SubNLogN.Math.Bridge.Proofs.Wiring
import SubNLogN.Math.Bridge.Proofs.FnewFinal
import SubNLogN.Math.Bridge.Proofs.WalshOK
import SubNLogN.Math.Bridge.Proofs.Precision_Arith
import SubNLogN.Math.Bridge.Proofs.Precision_Widths
import SubNLogN.Math.Bridge.Proofs.TablesConcrete
import SubNLogN.Math.Walsh.Proofs.Wiring
import SubNLogN.Math.Cost.WalshOKW8
import WP.W3s.Math

/-!
# K7 (`Machine/Pipe/BranchMath.lean`): the value-level premise of the Walsh branch

`branchMath_of`: `∃ N, BranchMathStmt fnewSched (walshMid row46) md N` (`BranchDefs.lean`), i.e. at
the W8 root parameters for large `n`, on every pipe input passing the input guard: the shape has length
`|x|`, the middle is eligible, `1 ≤ ω`, and `BridgeHyps` at the pipe's bridge parameters
`fnewPar fnewSched p0 K0 p_in`, tables `tabOf … = TabConcreteR roundHalfUpR row46 p0 K0`, middle
`walshMid row46 p0 K0` and input `x' = decodeArr p_in (2^{K0}) x`.

Proved inputs (all unconditional): `Math.Cost.walshOK_eventually_holds`, `walshOK_balanced`,
`shapeOK_of_balanced`, `tabConcrete_certified`, `Wired.bridge_spread_admissible`,
`Wired.bridge_widths`, `Wired.bridge_precision`, `FnewFinalProof.walshMid_isMiddle` with
`Walsh.direct_fft`, `norm_dft_le`, `fitsWidth_of_norm_lt`. Explicit premise contracts
(proved in `BranchMathSpread.lean`, `BranchMathSolve.lean`, `BranchMathTables.lean`, `BranchFinal.lean`):
`Bridge_spreadPart_widthsStmt`, `Bridge_solve_widthsStmt`, `TabConcrete_fitStmt`, and `MidOKW8Stmt md`
(discharged via `midBands_w8_of_width`). Proved here: the grid/window facts of certified tables
(`tablesOnGrid_of_certifiedR`, `tapsWindowed_of_certifiedR`), the input facts from the input guard
(`onGrid_decodeArr`, `norm_decodeArr_lt`, `fitsTwos_of_bound`, `arrFits_in_of_guard`), the output fit
(from `bridge_precision` and `norm_dft_le`).
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Bridge

/-! ## Value-level contract statements -/

/-- **[CONTRACT] Widths of the partial spreads** (extends `Bridge_widthsStmt`,
Table 4 (`tab:widths`) and Theorem 4.7 (`thm:bridge-precision`), to the arrays after `n` of the `d - 1` spreading stages, with the
machine rounding `roundHalfUpR`): under the hypotheses of `Bridge_spread_admissibleStmt`, every
entry of `spreadPart (q) t T (preScaled x ∘ encIn) n` (`Contracts/Bridge.lean`) has component width
`q + 2` on the `q`-grid, `q = schedP p k + 2`. -/
def Bridge_spreadPart_widthsStmt : Prop :=
  ∀ {d : ℕ} (t : Fin d → ℕ) (k ℓ p : ℕ), BalancedShape t k ℓ → max 8 k ≤ p →
  ∀ (x : Fin (totalLen t) → ℂ), (∀ j, OnGrid (p + 2) (x j)) → ‖x‖ ≤ (2 : ℝ) ^ p →
  ∀ (T : BridgeTables t),
    TablesCertifiedR roundHalfUpR (alphaDefault (schedOmega p k d)) (schedP p k) t T →
  ∀ (n : ℕ) (j : Idx t), FitsWidth (schedP p k + 2) (schedP p k + 4)
    (spreadPart (schedP p k + 2) t T (fun j => preScaled t x (encIn t j)) n j)

/-- **[CONTRACT] Widths of the solver sweeps** (Table 4 (`tab:widths`),
Lemma 4.6 (`lem:bridge-C`) (bridge Lemma C)(iv)): under the hypotheses of `Bridge_widthsStmt`, every deconvolution stage's sweep states,
closure values and scaled inputs (`SolveFits`, `Contracts/Bridge.lean`) fit the pipe's internal
width `schedP p k + 2k + 16` on the `q`-grid (from `Wired.lemmaC_iv` (`< 7t·max(1,‖Y‖)`) and the
`q + k + 6` widths of the partial deconvolutions). -/
def Bridge_solve_widthsStmt : Prop :=
  ∀ {d : ℕ} (t : Fin d → ℕ) (k ℓ p : ℕ), BalancedShape t k ℓ → max 8 k ≤ p →
  ∀ (x : Fin (totalLen t) → ℂ), (∀ j, OnGrid (p + 2) (x j)) → ‖x‖ ≤ (2 : ℝ) ^ p →
  ∀ (T : BridgeTables t),
    TablesCertifiedR roundHalfUpR (alphaDefault (schedOmega p k d)) (schedP p k) t T →
  ∀ (Emid : ℝ) (δmid : ℕ) (run : (Idx t → ℂ) → (Idx t → ℂ)),
    IsMiddleTransform t (schedP p k) Emid δmid run →
  ∀ (n : ℕ) (i : Fin d), (deconvOrder d)[n]? = some i →
    SolveFits (schedP p k + 2 * k + 16) (schedP p k + 2) t T i
      (deconvPart (schedP p k + 2) t T
        (fun f => run (spreadStageR roundHalfUpR (schedP p k) t T x) ((encFreq t).symm f)) n)

/-- **[CONTRACT] The concrete table entries fit the pipe's table width**
`schedP p0 K0 + 2 K0 + 16` (entry bounds `|tap| ≤ 1 + v`, `μ̂ ≤ c_max⁻¹ + v`, `0 ≤ â ≤ 1 + v`,
`γ̂ ≤ (1 - â^L)⁻¹ + v` at every eligible pair). -/
def TabConcrete_fitStmt : Prop :=
  ∀ (ρ : Math.Cost.RowExps) (p0 K0 : ℕ), WalshOK ρ p0 K0 = true →
    TablesFit (schedP p0 K0 + 2 * K0 + 16) (schedP p0 K0) (fnewShape ρ K0)
      (TabConcreteR roundHalfUpR ρ p0 K0)

/-- **[CONTRACT] The middle machine is eligible at the W8 pipe calls** for large `n`
(for `md.MOK := MidShapeOK ∧ MidFamilyBands ∧ P₀ ≤ q ∧ P₁ ≤ q` this follows from
`Assembly.midBands_w8_of_width` at the width `wI`). -/
def MidOKW8Stmt (md : MidData) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ pin : ℕ, md.MOK (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin

/-! ## Helper facts -/

namespace BranchMathAux

theorem onGridR_mono {q q' : ℕ} (h : q ≤ q') {x : ℝ} (hx : OnGridR q x) : OnGridR q' x := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨a * 2 ^ (q' - q), ?_⟩
  have e : (2 : ℝ) ^ q' = 2 ^ q * 2 ^ (q' - q) := by
    rw [← pow_add]
    congr 1
    omega
  unfold gridUnit
  rw [e]
  push_cast
  field_simp

theorem onGrid_mono {q q' : ℕ} (h : q ≤ q') {z : ℂ} (hz : OnGrid q z) : OnGrid q' z :=
  ⟨onGridR_mono h hz.1, onGridR_mono h hz.2⟩

theorem onGrid_decodeArr (pin R : ℕ) (x : Array (ℤ × ℤ)) (j : Fin R) :
    OnGrid (pin + 2) (decodeArr pin R x j) := by
  refine ⟨⟨(IntMul.read1D x (j : ℕ)).1, ?_⟩, ⟨(IntMul.read1D x (j : ℕ)).2, ?_⟩⟩ <;>
    simp [decodeArr, IntMul.toScaledComplex, gridUnit, div_eq_mul_inv]

/-- An integer whose magnitude has bit length `≤ m` has absolute value `< 2^m`. -/
theorem natAbs_lt_of_bitLen {z : ℤ} {m : ℕ} (h : bitLen z.natAbs ≤ m) :
    ((z.natAbs : ℕ) : ℤ) < 2 ^ m := by
  have := (TMFw.W3s.bitLen_le_iff m z.natAbs).1 h
  exact_mod_cast this

/-- Every entry `read1D x j` obeys the guard's bound (entries beyond `|x|` read as `0`). -/
theorem read1D_bound {g : ℕ} {x : Array (ℤ × ℤ)} (hg : ArrW g x) (j : ℕ) :
    (((IntMul.read1D x j).1.natAbs : ℕ) : ℤ) < 2 ^ g ∧
      (((IntMul.read1D x j).2.natAbs : ℕ) : ℤ) < 2 ^ g := by
  unfold IntMul.read1D
  split_ifs with hj
  · have hm : x[j] ∈ x.toList := by simp
    obtain ⟨h1, h2⟩ := hg _ hm
    exact ⟨natAbs_lt_of_bitLen h1, natAbs_lt_of_bitLen h2⟩
  · refine ⟨?_, ?_⟩ <;> simp

theorem abs_div_lt_of_natAbs {a : ℤ} {p0 pin : ℕ} (ha : ((a.natAbs : ℕ) : ℤ) < 2 ^ (p0 + pin + 1)) :
    |(a : ℝ) / 2 ^ (pin + 2)| < 2 ^ p0 / 2 := by
  have ha' : |(a : ℝ)| < 2 ^ (p0 + pin + 1) := by
    have h1 : ((((a.natAbs : ℕ) : ℤ)) : ℝ) < (((2 : ℤ) ^ (p0 + pin + 1) : ℤ) : ℝ) := by
      exact_mod_cast ha
    have h2 : ((((a.natAbs : ℕ) : ℤ)) : ℝ) = |(a : ℝ)| := by
      rw [Int.cast_natCast, Nat.cast_natAbs, Int.cast_abs]
    rw [h2] at h1
    simpa using h1
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (pin + 2)), div_lt_iff₀ (by positivity)]
  calc |(a : ℝ)| < 2 ^ (p0 + pin + 1) := ha'
    _ = 2 ^ p0 / 2 * 2 ^ (pin + 2) := by rw [pow_add, pow_add, pow_add]; ring

/-- **Input norm from the input guard**: `ArrW (p0 + p_in + 1) x` gives `‖x'_j‖ < 2^{p0}` for the
decoded input `x' = decodeArr p_in R x`. -/
theorem norm_decodeArr_lt (p0 pin R : ℕ) (x : Array (ℤ × ℤ)) (hg : ArrW (p0 + pin + 1) x)
    (j : Fin R) : ‖decodeArr pin R x j‖ < (2 : ℝ) ^ p0 := by
  obtain ⟨h1, h2⟩ := read1D_bound hg j
  have hn := Complex.norm_le_abs_re_add_abs_im (decodeArr pin R x j)
  have e1 : (decodeArr pin R x j).re = ((IntMul.read1D x (j : ℕ)).1 : ℝ) / 2 ^ (pin + 2) := rfl
  have e2 : (decodeArr pin R x j).im = ((IntMul.read1D x (j : ℕ)).2 : ℝ) / 2 ^ (pin + 2) := rfl
  rw [e1, e2] at hn
  have k1 := abs_div_lt_of_natAbs h1
  have k2 := abs_div_lt_of_natAbs h2
  linarith

theorem fitsTwos_of_bound {w : ℕ} {a : ℤ} (h : ((a.natAbs : ℕ) : ℤ) < 2 ^ (w - 1)) :
    FitsTwos w a := by
  have h' : |a| < 2 ^ (w - 1) := by rwa [Int.abs_eq_natAbs]
  exact ⟨le_of_lt (abs_lt.1 h').1, (abs_lt.1 h').2⟩

/-- **Input fit from the input guard**: `ArrFits (p0 + p_in + 2) (p_in + 2) x'`. -/
theorem arrFits_in_of_guard (p0 pin R : ℕ) (x : Array (ℤ × ℤ)) (hR : R = x.size)
    (hg : ArrW (p0 + pin + 1) x) : ArrFits (p0 + pin + 2) (pin + 2) (decodeArr pin R x) := by
  intro j
  have hj : (j : ℕ) < x.size := hR ▸ j.isLt
  unfold FitsC
  rw [gridInt_decodeArr pin R x j hj]
  obtain ⟨h1, h2⟩ := read1D_bound hg j
  simp only [IntMul.read1D, dif_pos hj] at h1 h2
  exact ⟨fitsTwos_of_bound (by simpa using h1), fitsTwos_of_bound (by simpa using h2)⟩

theorem fitsC_of_fitsWidth {q w w' : ℕ} {z : ℂ} (h : FitsWidth q w z) (hw : w ≤ w') :
    FitsC w' q z := by
  obtain ⟨⟨a, ha, ha1, ha2⟩, ⟨b, hb, hb1, hb2⟩⟩ := h
  have hq : gridUnit q * (2 : ℝ) ^ q = 1 := by unfold gridUnit; field_simp
  have hra : round (z.re * 2 ^ q) = a := by rw [ha, mul_assoc, hq, mul_one, round_intCast]
  have hrb : round (z.im * 2 ^ q) = b := by rw [hb, mul_assoc, hq, mul_one, round_intCast]
  have hp : (2 : ℤ) ^ (w - 1) ≤ 2 ^ (w' - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  unfold FitsC FitsTwos gridInt
  rw [hra, hrb]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem arrFits_of_fitsWidth {ι : Type} {q w w' : ℕ} {Z : ι → ℂ} (h : ∀ j, FitsWidth q w (Z j))
    (hw : w ≤ w') : ArrFits w' q Z := fun j => fitsC_of_fitsWidth (h j) hw

/-- Certified tables lie on the grid (`TablesOnGrid`, `Contracts/Bridge.lean` §3). -/
theorem tablesOnGrid_of_certifiedR {d : ℕ} {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) {α : ℝ}
    {P : ℕ} {t : Fin d → ℕ} {T : BridgeTables t} (h : TablesCertifiedR rr α P t T) :
    TablesOnGrid P t T := by
  intro i hi
  obtain ⟨htap, hu⟩ := h i hi
  refine ⟨fun a ha e => (htap a ha e).1, fun u hu' => ?_⟩
  obtain ⟨hmu, hah, -, -, -, hgam⟩ := hu u hu'
  refine ⟨hmu, hah, ?_⟩
  rw [hgam]
  exact rr_onGridR hrr _ _

/-- Certified taps have the window structure (`TapsWindowed`, `Contracts/Bridge.lean` §3). -/
theorem tapsWindowed_of_certifiedR {d : ℕ} {rr : ℕ → ℝ → ℝ} {α : ℝ} {P : ℕ} {t : Fin d → ℕ}
    {T : BridgeTables t} (h : TablesCertifiedR rr α P t T) : TapsWindowed P t T := by
  intro i hi a ha e
  obtain ⟨htap, -⟩ := h i hi
  obtain ⟨-, -, hz, hper⟩ := htap a ha e
  exact ⟨hz, hper⟩

/-- **Output fit** (from `Wired.bridge_precision` and the `1/R`-normalized `norm_dft_le`): the
bridge output is on the `(p+2)`-grid with `‖·‖ < 2^p + 1 ≤ 2^{p+1}`, so it fits any width
`≥ 2p + 4`. -/
theorem out_fits {d : ℕ} (t : Fin d → ℕ) (k ℓ p : ℕ) (hshape : BalancedShape t k ℓ)
    (hp : max 8 k ≤ p) (x : Fin (totalLen t) → ℂ) (hx : ∀ j, OnGrid (p + 2) (x j))
    (hxn : ‖x‖ ≤ (2 : ℝ) ^ p) (T : BridgeTables t)
    (hT : TablesCertifiedR roundHalfUpR (alphaDefault (schedOmega p k d)) (schedP p k) t T)
    (Emid : ℝ) (δmid : ℕ) (run : (Idx t → ℂ) → (Idx t → ℂ))
    (hmid : IsMiddleTransform t (schedP p k) Emid δmid run) (w : ℕ) (hw : 2 * p + 4 ≤ w) :
    ArrFits w (p + 2) (bridgeFixedR roundHalfUpR p (schedP p k) t T run x) := by
  obtain ⟨hgrid, herr⟩ := Wired.bridge_precision roundHalfUpR isNearestRounding_roundHalfUpR t k ℓ p
    hshape hp x hx hxn T hT Emid δmid run hmid
  set y := bridgeFixedR roundHalfUpR p (schedP p k) t T run x with hy
  set D := dft (totalLen t) x with hD
  have hc : Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ) < 1 := by
    have h1 : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have h2 : (2 : ℝ) ^ (-12 : ℤ) ≤ 1 / 4 := by norm_num
    have h3 : (2 : ℝ) ^ (-23 : ℤ) ≤ 1 / 4 := by norm_num
    linarith
  have hpos : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have hm : max 1 ‖x‖ ≤ 2 ^ p := max_le hpos hxn
  have hzp : (2 : ℝ) ^ (-(p : ℤ)) * 2 ^ p = 1 := by
    rw [zpow_neg, zpow_natCast]
    field_simp
  have herr' : ‖y - D‖ < 1 := by
    have hz0 : (0 : ℝ) ≤ (Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ)) *
        (2 : ℝ) ^ (-(p : ℤ)) := by positivity
    calc ‖y - D‖ < (Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ)) *
          (2 : ℝ) ^ (-(p : ℤ)) * max 1 ‖x‖ := herr
      _ ≤ (Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ)) *
          (2 : ℝ) ^ (-(p : ℤ)) * 2 ^ p := mul_le_mul_of_nonneg_left hm hz0
      _ = Real.sqrt 2 / 8 + (2 : ℝ) ^ (-12 : ℤ) + (2 : ℝ) ^ (-23 : ℤ) := by
          rw [mul_assoc, hzp, mul_one]
      _ < 1 := hc
  have hyD : ‖y‖ ≤ ‖D‖ + ‖y - D‖ := by
    calc ‖y‖ = ‖D + (y - D)‖ := by rw [add_sub_cancel]
      _ ≤ ‖D‖ + ‖y - D‖ := norm_add_le _ _
  have hDx : ‖D‖ ≤ ‖x‖ := norm_dft_le _ x
  intro f
  have hb : ‖y f‖ < (2 : ℝ) ^ (p + 1) := by
    have hyf : ‖y f‖ ≤ ‖y‖ := norm_le_pi_norm y f
    rw [pow_succ]
    linarith
  exact fitsC_of_fitsWidth (PrecisionWidthsProof.fitsWidth_of_norm_lt (hgrid f) hb le_rfl)
    (by omega)

end BranchMathAux

open BranchMathAux

/-- **The value-level premise of the Walsh branch (`branchMath_of`, 0 `sorry`).** Given the middle's
eligibility at the W8 calls (`MidOKW8Stmt md`) and the three width statements
(`Bridge_spreadPart_widthsStmt`, `Bridge_solve_widthsStmt`, `TabConcrete_fitStmt`), there is `N`
with `BranchMathStmt fnewSched (walshMid row46) md N`: for `n ≥ N` (eventual eligibility
`walshOK_eventually_holds`), the balanced shape (`walshOK_balanced`) has length `2^{K0} = |x|`, and
under the input guard every conjunct of `BridgeHyps` holds at the pipe's bridge parameters (from
`bridge_spread_admissible`, `bridge_widths`, `bridge_precision`, `tabConcrete_certified`,
`walshMid_isMiddle`, and the input facts implied by the guard). -/
theorem branchMath_of (md : MidData) (hMOK : MidOKW8Stmt md) (hSP : Bridge_spreadPart_widthsStmt)
    (hSV : Bridge_solve_widthsStmt) (hTF : TabConcrete_fitStmt) :
    ∃ N : ℕ, BranchMathStmt fnewSched (walshMid Math.Cost.row46) md N := by
  obtain ⟨N1, hN1⟩ := Math.Cost.walshOK_eventually_holds
  obtain ⟨N2, hN2⟩ := hMOK
  refine ⟨max N1 N2, fun n cSpec pin x hn hj hsz hwx hp => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) hn
  have hOK : WalshOK Math.Cost.row46 (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) =
      true := hN1 n hn1
  have hbal : BalancedShape (fnewShape Math.Cost.row46 (W8.hK0 n)) (W8.hK0 n)
      (fnewL Math.Cost.row46 (W8.hK0 n)) := walshOK_balanced Math.Cost.row46 _ _ hOK
  have htot : totalLen (fnewShape Math.Cost.row46 (W8.hK0 n)) = 2 ^ W8.hK0 n := hbal.2.1
  have hR : totalLen (fnewShape Math.Cost.row46 (W8.hK0 n)) = x.size := htot.trans hsz.symm
  refine ⟨hR, fun hg => ?_⟩
  have hgA : ArrW (IntMul.rootPrecision (W8.hB n) (W8.hK0 n) + pin + 1) x := (guardB_iff _ _).1 hg
  have hb1 : 1 ≤ W8.hB n := le_max_left _ _
  have hrp : IntMul.rootPrecision (W8.hB n) (W8.hK0 n) = 2 * W8.hB n + 2 * W8.hK0 n + 6 := rfl
  have hpin : pin ≤ IntMul.rootPrecision (W8.hB n) (W8.hK0 n) := by
    rcases hp with h | h <;> omega
  have hpp : max 8 (W8.hK0 n) ≤ IntMul.rootPrecision (W8.hB n) (W8.hK0 n) := by
    rw [hrp]
    omega
  have hx'g : ∀ j, OnGrid (IntMul.rootPrecision (W8.hB n) (W8.hK0 n) + 2)
      (decodeArr pin (totalLen (fnewShape Math.Cost.row46 (W8.hK0 n))) x j) :=
    fun j => onGrid_mono (by omega) (onGrid_decodeArr pin _ x j)
  have hx'n : ‖decodeArr pin (totalLen (fnewShape Math.Cost.row46 (W8.hK0 n))) x‖ ≤
      (2 : ℝ) ^ IntMul.rootPrecision (W8.hB n) (W8.hK0 n) :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j =>
      le_of_lt (norm_decodeArr_lt _ pin _ x hgA j)
  have hT := tabConcrete_certified roundHalfUpR isNearestRounding_roundHalfUpR Math.Cost.row46
    (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) hOK
  have hSA := Wired.bridge_spread_admissible roundHalfUpR isNearestRounding_roundHalfUpR _ _ _ _
    hbal hpp _ hx'g hx'n _ hT
  have hmid := FnewFinalProof.walshMid_isMiddle SubNLogN.Math.Walsh.direct_fft Math.Cost.row46 _ _ hOK
  have hWd := Wired.bridge_widths roundHalfUpR isNearestRounding_roundHalfUpR _ _ _ _ hbal hpp _
    hx'g hx'n _ hT _ _ _ hmid
  have hSP' := hSP _ _ _ _ hbal hpp _ hx'g hx'n _ hT
  have hSV' := hSV _ _ _ _ hbal hpp _ hx'g hx'n _ hT _ _ _ hmid
  have hTF' := hTF Math.Cost.row46 _ _ hOK
  have hout := out_fits _ _ _ _ hbal hpp _ hx'g hx'n _ hT _ _ _ hmid
    (2 * IntMul.rootPrecision (W8.hB n) (W8.hK0 n) + W8.hK0 n + 8) (by omega)
  refine ⟨hN2 n hn2 pin, ?_, ?_⟩
  · show 1 ≤ schedOmega _ _ _
    unfold schedOmega
    omega
  refine ⟨hbal.1, PrecisionArith.shapeOK_of_balanced hbal, ⟨_, _, hbal⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun j =>
    onGrid_decodeArr pin _ x j, hSA.1, tablesOnGrid_of_certifiedR isNearestRounding_roundHalfUpR hT,
    tapsWindowed_of_certifiedR hT, hSA.2.2, fun u => hmid.out_onGrid _ hSA.2.1 hSA.2.2 u, ?_⟩
  · show 1 ≤ IntMul.rootPrecision (W8.hB n) (W8.hK0 n) + pin + 2
    omega
  · show 1 ≤ schedP (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) + 2 * W8.hK0 n + 16
    omega
  · show 1 ≤ schedP (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) + 2 * W8.hK0 n + 16
    omega
  · show 1 ≤ 2 * IntMul.rootPrecision (W8.hB n) (W8.hK0 n) + W8.hK0 n + 8
    omega
  · show schedP (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) + 2 ≤
      schedP (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) + 2 * W8.hK0 n + 16
    omega
  · show Nat.log2 (totalLen (fnewShape Math.Cost.row46 (W8.hK0 n))) ≤
      schedP (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) + 2 * W8.hK0 n + 16
    rw [htot, Nat.log2_two_pow]
    omega
  · have hwI : (fnewPar fnewSched (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin).wI =
        schedP (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) + 2 * W8.hK0 n + 16 := rfl
    refine ⟨arrFits_in_of_guard _ pin _ x hR hgA, arrFits_of_fitsWidth hWd.1 (by rw [hwI]; omega),
      fun m => arrFits_of_fitsWidth (hSP' m) (by rw [hwI]; omega),
      fun m => arrFits_of_fitsWidth (fun f => hWd.2.2 m f) (by rw [hwI]; omega), hSV', hTF', hout⟩

end SubNLogN.Machine.Pipe
