/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.BranchMath

/-!
# BM-SV (`Machine/Pipe/BranchMathSolve.lean`): widths of the solver sweeps

Proves `bridge_solve_widths : Bridge_solve_widthsStmt` (the contract of `BranchMath.lean`;
Lemma 4.6 (`lem:bridge-C`)(iv), Theorem 4.7 (`thm:bridge-precision`), Table 4 (`tab:widths`)), unconditionally: every stored state of every
deconvolution stage's two-pass sweeps (`SolveFits`, `Contracts/Bridge.lean`: the scaled inputs
`b_j = rnd(μ̂ Y_j)`, the prefix states from `0`, the closure value and the second-pass states) fits
the width `schedP p k + 2k + 16` at precision `q = schedP p k + 2`.

Proof. Fix the stage `n` (axis `i ≠ 0`, cycle length `L = A_i`, even, so `L ≥ 2`) and a frequency
`f` with digit `u`. Let `M = max(1, ‖Y_cyc‖_∞)` for the cycle `Y_cyc = cycVec t i Y f` of the stage
input `Y = deconvPart … n`.
* `Wired.lemmaC_iv` (hypotheses from `TablesCertifiedR roundHalfUpR` and `Wired.lemmaC_v`, as in
  `PrecisionDeconvProof.deconvAxisFixed_stage`) bounds by `B = 7 t_i M` the prefix states from `0`
  and the outputs of `cycSweepFwdR`, i.e. the closure value (output `L - 1`) and the second-pass
  states `n < L - 1`, for the input `extNat Y_cyc` (forward case) resp. `reorientIn L (extNat Y_cyc)`
  (backward case); `SolveFits` uses the same functions on `[0, L)` (`sweep_bounds_congr`).
* The two kinds of states not output by `cycSweepFwdR` follow from the recurrence with
  `0 ≤ â ≤ a' + v ≤ 2` (`kernelG_pos`): `b_n = z_n - rnd(-â z_{n-1})` gives `‖b_n‖ ≤ 3B + 1`, and the
  second-pass state `L - 1` is `b_{L-1} + rnd(-â Z_{L-2})`, of modulus `≤ 5B + 2`
  (`sweep_states_bound`).
* `Wired.bridge_widths` gives the stage input component width `q + k + 6`, so `M ≤ 2^{k+6}`; with
  `t_i ≤ 2^k`, `5B + 2 < 2^{2k+13}`, and every state (a `q`-grid value) fits
  `q + (2k + 13) + 1 = schedP p k + 2k + 16` bits (`fitsC_of_norm_lt`).
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Bridge

namespace BranchMathSolveAux

/-- `2^{-q} ≤ 1`. -/
theorem gridUnit_le_one (q : ℕ) : gridUnit q ≤ 1 := by
  unfold gridUnit
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- A nearest complex rounding moves a value by at most `1` (in fact `≤ 2^{-q}`). -/
theorem norm_crnd_le {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ) (z : ℂ) :
    ‖crnd rr q z‖ ≤ ‖z‖ + 1 := by
  have h1 : ‖crnd rr q z - z‖ ≤ gridUnit q := by
    have h := Complex.norm_le_abs_re_add_abs_im (crnd rr q z - z)
    have h2 := abs_re_crnd_sub_le hrr q z
    have h3 := abs_im_crnd_sub_le hrr q z
    linarith
  have h4 := gridUnit_le_one q
  calc ‖crnd rr q z‖ = ‖(crnd rr q z - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖crnd rr q z - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ ‖z‖ + 1 := by linarith

/-- A real of component width `w ≤ q + e + 1` at precision `q` has `|x| ≤ 2^e`. -/
theorem abs_le_of_fitsWidthR {q w e : ℕ} {x : ℝ} (h : FitsWidthR q w x) (hw : w ≤ q + e + 1) :
    |x| ≤ (2 : ℝ) ^ e := by
  obtain ⟨a, rfl, h1, h2⟩ := h
  have hpow : (2 : ℤ) ^ (w - 1) ≤ 2 ^ (q + e) := pow_le_pow_right₀ (by norm_num) (by omega)
  have ha : |a| ≤ (2 : ℤ) ^ (q + e) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha' : |(a : ℝ)| ≤ (2 : ℝ) ^ (q + e) := by
    have h3 : ((|a| : ℤ) : ℝ) ≤ (((2 : ℤ) ^ (q + e) : ℤ) : ℝ) := by exact_mod_cast ha
    push_cast at h3
    exact h3
  rw [abs_mul, abs_of_pos (gridUnit_pos q)]
  calc |(a : ℝ)| * gridUnit q ≤ 2 ^ (q + e) * gridUnit q :=
        mul_le_mul_of_nonneg_right ha' (gridUnit_pos q).le
    _ = 2 ^ e := by
        unfold gridUnit
        rw [pow_add, mul_comm ((2 : ℝ) ^ q), mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]

/-- A complex number of component width `w ≤ q + e + 1` at precision `q` has `‖z‖ ≤ 2^{e+1}`. -/
theorem norm_le_of_fitsWidth {q w e : ℕ} {z : ℂ} (h : FitsWidth q w z) (hw : w ≤ q + e + 1) :
    ‖z‖ ≤ (2 : ℝ) ^ (e + 1) := by
  have h1 := abs_le_of_fitsWidthR h.1 hw
  have h2 := abs_le_of_fitsWidthR h.2 hw
  have h3 := Complex.norm_le_abs_re_add_abs_im z
  rw [pow_succ]
  linarith

/-- A `q`-grid value of modulus `< 2^e` fits `FitsC w q` when `q + e + 1 ≤ w`. -/
theorem fitsC_of_norm_lt {q w e : ℕ} {z : ℂ} (hz : OnGrid q z) (hb : ‖z‖ < (2 : ℝ) ^ e)
    (hw : q + e + 1 ≤ w) : FitsC w q z :=
  BranchMathAux.fitsC_of_fitsWidth (PrecisionWidthsProof.fitsWidth_of_norm_lt hz hb hw) le_rfl

/-- The two sweep bounds of Lemma 4.6 (bridge Lemma C)(iv) transfer between inputs that agree on the cycle `[0, L)`. -/
theorem sweep_bounds_congr {rr : ℕ → ℝ → ℝ} {q : ℕ} {mu ahat gam : ℝ} {L : ℕ} {Y Y' : ℕ → ℂ}
    {B : ℝ} (hY : ∀ j < L, Y j = Y' j)
    (hz : ∀ n < L, ‖sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * Y' j)) 0 n‖ < B)
    (hZ : ∀ n < L, ‖cycSweepFwdR rr q mu ahat gam L Y' n‖ < B) :
    (∀ n < L, ‖sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * Y j)) 0 n‖ ≤ B) ∧
      ∀ n < L, ‖cycSweepFwdR rr q mu ahat gam L Y n‖ ≤ B := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · have e := PrecisionDeconvProof.sweepPrefix_congr rr q ahat
      (fun j => crnd rr q ((mu : ℂ) * Y j)) (fun j => crnd rr q ((mu : ℂ) * Y' j)) 0 n
      (fun j hj => by simp only [hY j (by omega)])
    rw [e]
    exact (hz n hn).le
  · rw [PrecisionDeconvProof.cycSweepFwd_congr rr q mu ahat gam L Y Y' hY n hn]
    exact (hZ n hn).le

/-- **All stored states of a forward sweep.** If the prefix states from `0` and the outputs of
`cycSweepFwdR` (the closure value at `L - 1`, the second-pass states below `L - 1`) have modulus
`≤ B`, and `|â| ≤ 2`, then every state listed by `SweepFits` has modulus `≤ 5B + 2`: the closure
value and the states below `L - 1` directly; the scaled inputs by `b_n = z_n - rnd(-â z_{n-1})`
(`≤ 3B + 1`); the second-pass state at `L - 1` by `Z_{L-1} = b_{L-1} + rnd(-â Z_{L-2})`. -/
theorem sweep_states_bound {rr : ℕ → ℝ → ℝ} (hrr : IsNearestRounding rr) (q : ℕ)
    (mu ahat gam : ℝ) (L : ℕ) (Y : ℕ → ℂ) (B : ℝ) (hL : 2 ≤ L) (ha : |ahat| ≤ 2)
    (hz : ∀ n < L, ‖sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * Y j)) 0 n‖ ≤ B)
    (hZ : ∀ n < L, ‖cycSweepFwdR rr q mu ahat gam L Y n‖ ≤ B) :
    ‖crnd rr q ((gam : ℂ) *
        sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * Y j)) 0 (L - 1))‖ ≤ 5 * B + 2 ∧
      ∀ n, n < L →
        ‖crnd rr q ((mu : ℂ) * Y n)‖ ≤ 5 * B + 2 ∧
        ‖sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * Y j)) 0 n‖ ≤ 5 * B + 2 ∧
        ‖sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * Y j))
          (crnd rr q ((gam : ℂ) *
            sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * Y j)) 0 (L - 1))) n‖ ≤
          5 * B + 2 := by
  set b : ℕ → ℂ := fun j => crnd rr q ((mu : ℂ) * Y j) with hb
  set zL : ℂ := crnd rr q ((gam : ℂ) * sweepPrefixR rr q ahat b 0 (L - 1)) with hzL
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hz 0 (by omega))
  have hrnd : ∀ z : ℂ, ‖crnd rr q (-(ahat : ℂ) * z)‖ ≤ 2 * ‖z‖ + 1 := by
    intro z
    have h1 := norm_crnd_le hrr q (-(ahat : ℂ) * z)
    have h2 : ‖-(ahat : ℂ) * z‖ = |ahat| * ‖z‖ := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have h3 : |ahat| * ‖z‖ ≤ 2 * ‖z‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    linarith
  have hout : ∀ n, n ≠ L - 1 →
      cycSweepFwdR rr q mu ahat gam L Y n = sweepPrefixR rr q ahat b zL n := by
    intro n hne
    unfold cycSweepFwdR
    exact if_neg hne
  have hlast : cycSweepFwdR rr q mu ahat gam L Y (L - 1) = zL := by
    unfold cycSweepFwdR
    exact if_pos rfl
  have hsec : ∀ n < L, n ≠ L - 1 → ‖sweepPrefixR rr q ahat b zL n‖ ≤ B := fun n hn hne => by
    rw [← hout n hne]; exact hZ n hn
  have hbn : ∀ n < L, ‖b n‖ ≤ 3 * B + 1 := by
    intro n hn
    cases n with
    | zero =>
      have e : b 0 = sweepPrefixR rr q ahat b 0 0 - crnd rr q (-(ahat : ℂ) * 0) := by
        rw [show sweepPrefixR rr q ahat b 0 0 = b 0 + crnd rr q (-(ahat : ℂ) * 0) from rfl]
        ring
      have k1 := hz 0 hn
      have k2 := hrnd 0
      rw [norm_zero] at k2
      rw [e]
      calc _ ≤ ‖sweepPrefixR rr q ahat b 0 0‖ + ‖crnd rr q (-(ahat : ℂ) * 0)‖ := norm_sub_le _ _
        _ ≤ 3 * B + 1 := by linarith
    | succ m =>
      have e : b (m + 1) = sweepPrefixR rr q ahat b 0 (m + 1) -
          crnd rr q (-(ahat : ℂ) * sweepPrefixR rr q ahat b 0 m) := by
        rw [show sweepPrefixR rr q ahat b 0 (m + 1) =
          b (m + 1) + crnd rr q (-(ahat : ℂ) * sweepPrefixR rr q ahat b 0 m) from rfl]
        ring
      have k1 := hz (m + 1) hn
      have k2 := hrnd (sweepPrefixR rr q ahat b 0 m)
      have k3 := hz m (by omega)
      rw [e]
      calc _ ≤ ‖sweepPrefixR rr q ahat b 0 (m + 1)‖ +
            ‖crnd rr q (-(ahat : ℂ) * sweepPrefixR rr q ahat b 0 m)‖ := norm_sub_le _ _
        _ ≤ 3 * B + 1 := by linarith
  refine ⟨?_, fun n hn => ⟨?_, ?_, ?_⟩⟩
  · have h := hZ (L - 1) (by omega)
    rw [hlast] at h
    linarith
  · exact (hbn n hn).trans (by linarith)
  · exact (hz n hn).trans (by linarith)
  · by_cases hne : n = L - 1
    · have hL1 : n = (L - 2) + 1 := by omega
      rw [hL1]
      have e : sweepPrefixR rr q ahat b zL (L - 2 + 1) =
          b (L - 2 + 1) + crnd rr q (-(ahat : ℂ) * sweepPrefixR rr q ahat b zL (L - 2)) := rfl
      rw [e]
      have k1 := hbn (L - 2 + 1) (by omega)
      have k2 := hrnd (sweepPrefixR rr q ahat b zL (L - 2))
      have k3 := hsec (L - 2) (by omega) (by omega)
      calc _ ≤ ‖b (L - 2 + 1)‖ +
            ‖crnd rr q (-(ahat : ℂ) * sweepPrefixR rr q ahat b zL (L - 2))‖ := norm_add_le _ _
        _ ≤ 5 * B + 2 := by linarith
    · exact (hsec n hn hne).trans (by linarith)

/-- `SweepFits w q` from the two Lemma 4.6 (bridge Lemma C)(iv) bounds (`≤ B`), `|â| ≤ 2` and `5B + 2 < 2^e`,
`q + e + 1 ≤ w` (every stored state is a `q`-grid value, `sweepPrefixR_onGrid`). -/
theorem sweepFits_of_bounds {q w e : ℕ} (mu ahat gam : ℝ) (L : ℕ) (Y : ℕ → ℂ) (B : ℝ)
    (hL : 2 ≤ L) (ha : |ahat| ≤ 2)
    (hz : ∀ n < L, ‖sweepPrefixR roundHalfUpR q ahat
      (fun j => crnd roundHalfUpR q ((mu : ℂ) * Y j)) 0 n‖ ≤ B)
    (hZ : ∀ n < L, ‖cycSweepFwdR roundHalfUpR q mu ahat gam L Y n‖ ≤ B)
    (hB : 5 * B + 2 < (2 : ℝ) ^ e) (hw : q + e + 1 ≤ w) :
    SweepFits w q mu ahat gam L Y := by
  have hrr := isNearestRounding_roundHalfUpR
  obtain ⟨h1, h2⟩ := sweep_states_bound hrr q mu ahat gam L Y B hL ha hz hZ
  have hbg : ∀ n, OnGrid q (crnd roundHalfUpR q ((mu : ℂ) * Y n)) :=
    fun n => crnd_onGrid hrr q _
  refine ⟨fitsC_of_norm_lt (crnd_onGrid hrr q _) (h1.trans_lt hB) hw, fun n hn => ?_⟩
  obtain ⟨k1, k2, k3⟩ := h2 n hn
  exact ⟨fitsC_of_norm_lt (crnd_onGrid hrr q _) (k1.trans_lt hB) hw,
    fitsC_of_norm_lt (PrecisionWidthsProof.sweepPrefixR_onGrid hrr q ahat _ 0 hbg n)
      (k2.trans_lt hB) hw,
    fitsC_of_norm_lt (PrecisionWidthsProof.sweepPrefixR_onGrid hrr q ahat _ _ hbg n)
      (k3.trans_lt hB) hw⟩

/-- The width budget: `5·(7 t M) + 2 < 2^{2k+13}` for `t ≤ 2^k` and `1 ≤ M ≤ 2^{k+6}`. -/
theorem budget_lt {t M : ℝ} {k : ℕ} (ht : t ≤ 2 ^ k) (hM1 : 1 ≤ M) (hM : M ≤ 2 ^ (k + 6)) :
    5 * (7 * t * M) + 2 < (2 : ℝ) ^ (2 * k + 13) := by
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 2 ^ k * 2 ^ (k + 6) := ⟨_, rfl⟩
  have h1 : t * M ≤ X := by
    rw [hX]
    exact mul_le_mul ht hM (by linarith) (by positivity)
  have h2 : (2 : ℝ) ^ (2 * k + 13) = 128 * X := by rw [hX]; ring
  have h3 : (1 : ℝ) ≤ X := by
    rw [hX]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have h5 : 5 * (7 * t * M) = 35 * (t * M) := by ring
  rw [h2, h5]
  linarith

end BranchMathSolveAux

open BranchMathSolveAux in
/-- **BM-SV: widths of the solver sweeps** (`Bridge_solve_widthsStmt`; Lemma 4.6 (`lem:bridge-C`)(iv),
Table 4 (`tab:widths`)), unconditional. See the module docstring for the argument. -/
theorem bridge_solve_widths : Bridge_solve_widthsStmt := by
  unfold Bridge_solve_widthsStmt
  intro d t k ℓ p hshape hp x hx hxn T hT Emid δmid run hmid n i hi
  have hrr := isNearestRounding_roundHalfUpR
  have hW := (Wired.bridge_widths roundHalfUpR hrr t k ℓ p hshape hp x hx hxn T hT Emid δmid run
    hmid).2.2 n
  have hsh := PrecisionBasic.shapeOK_of_balancedShape hshape
  have hdk := PrecisionWidthsProof.d_le_k hshape
  obtain ⟨hd2, hR, -, -, -⟩ := hshape
  have hPdef : schedP p k = 2 * p + 12 * k + 32 * Nat.clog 2 (p + k + 2) + 256 := by
    unfold schedP; rfl
  have hi0 : (i : ℕ) ≠ 0 :=
    PrecisionDeconvProof.mem_deconvOrder'.mp (List.mem_iff_getElem?.mpr ⟨n, hi⟩)
  set P := schedP p k with hP
  set α := alphaDefault (schedOmega p k d) with hα_def
  have hωP : schedOmega p k d ≤ P := by
    have hlg : lg d ≤ k := by
      unfold lg
      have h1 : Nat.clog 2 d ≤ d := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
      exact max_le (h1.trans hdk) (by omega)
    unfold schedOmega; omega
  have hC : LemmaCParams P (schedOmega p k d) α :=
    PrecisionWidthsProof.lemmaCParams_default (by omega) (by unfold schedOmega; omega) hωP
  -- the stage input `Y = deconvPart … n` has component width `q + k + 6` (`Wired.bridge_widths`)
  set Ys := deconvPart (P + 2) t T
    (fun f => run (spreadStageR roundHalfUpR P t T x) ((encFreq t).symm f)) n with hYs
  have hWs : ∀ f, FitsWidth (P + 2) (P + 2 + k + 6) (Ys f) := hW
  have hYsn : ‖Ys‖ ≤ (2 : ℝ) ^ (k + 6) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun f => ?_
    rw [show k + 6 = (k + 5) + 1 by ring]
    exact norm_le_of_fitsWidth (hWs f) (by omega)
  -- the axis `i`: cycle length `L = A_i` (even, so `2 ≤ L`), `t_i ≤ 2^k`, `v ≤ 1/(64 t_i)`
  have hL0 : 0 < prefixProd t i := PrecisionDeconvProof.prefixProd_pos hsh i
  have hLe : Even (prefixProd t i) := PrecisionDeconvProof.even_prefixProd hsh hi0
  have hL2 : 2 ≤ prefixProd t i := by
    obtain ⟨r, hr⟩ := hLe
    omega
  have hti : (t i : ℝ) ≤ 2 ^ k := by exact_mod_cast PrecisionWidthsProof.t_le_two_pow hR i
  have hg1 : gridUnit (P + 2) ≤ 1 := gridUnit_le_one _
  have hg := gridUnit_pos (P + 2)
  have htpos : (0 : ℝ) < t i := by
    have := (hsh i).1
    exact_mod_cast (by omega : 0 < t i)
  have hv : gridUnit (P + 2) ≤ 1 / (64 * (t i : ℝ)) := by
    have h4 := PrecisionWidthsProof.two_pow_mul_gridUnit P
    have hbig : (2 : ℝ) ^ (k + 4) ≤ 2 ^ P := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [le_div_iff₀ (mul_pos (by norm_num) htpos)]
    calc gridUnit (P + 2) * (64 * (t i : ℝ)) ≤ gridUnit (P + 2) * (64 * 2 ^ k) :=
          mul_le_mul_of_nonneg_left (by linarith) hg.le
      _ = 2 ^ (k + 4) * gridUnit (P + 2) * 4 := by rw [pow_add]; ring
      _ ≤ 2 ^ P * gridUnit (P + 2) * 4 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbig hg.le) (by norm_num)
      _ = 1 := by rw [h4]; norm_num
  intro f
  have hu : (((encFreq t).symm f i : Fin (t i)) : ℕ) < t i := ((encFreq t).symm f i).isLt
  set u : ℕ := (((encFreq t).symm f i : Fin (t i)) : ℕ) with hu_def
  obtain ⟨-, -, hmu, ha, ha0, hgam⟩ := (hT i hi0).2 u hu
  have hgam' : |T.gam i u - (1 - T.ahat i u ^ prefixProd t i)⁻¹| ≤ gridUnit (P + 2) := by
    rw [hgam]
    exact Wired.lemmaC_v roundHalfUpR hrr P _ α hC (t i) (hsh i) u hu hv _ (prefixProd t i) hLe
      hL0 ha ha0
  set Yc := PrecisionDeconvProof.cycVec t i Ys f with hYc
  obtain ⟨-, h2, h3⟩ := Wired.lemmaC_iv roundHalfUpR hrr P _ α hC (t i) (hsh i) u hu hv
    (T.mu i u) (T.ahat i u) (T.gam i u) (prefixProd t i) hLe hL0 hmu ha ha0 hgam' Yc
  -- `0 ≤ â ≤ a' + v ≤ 2`
  have hahat : |T.ahat i u| ≤ 2 := by
    have hα : 0 < α := hC.2.2.2.1
    have hc0 : 0 < coeffC0 α (t i) u := kernelG_pos α hα _
    have hmax : 0 < max (coeffC0 α (t i) u) (coeffC1 α (t i) u) := lt_max_of_lt_left hc0
    have hr : min (coeffC0 α (t i) u) (coeffC1 α (t i) u) /
        max (coeffC0 α (t i) u) (coeffC1 α (t i) u) ≤ 1 := (div_le_one hmax).2 min_le_max
    have h1 := (abs_le.mp ha).2
    rw [abs_of_nonneg ha0]
    linarith
  -- `B = 7 t_i M` with `M = max(1, ‖Y_cyc‖) ≤ 2^{k+6}`: `5B + 2 < 2^{2k+13}`
  set M : ℝ := max 1 ‖Yc‖ with hM_def
  have hM : M ≤ 2 ^ (k + 6) :=
    max_le (one_le_pow₀ (by norm_num)) ((PrecisionDeconvProof.norm_cycVec_le t i Ys f).trans hYsn)
  have hB : 5 * (7 * (t i : ℝ) * M) + 2 < (2 : ℝ) ^ (2 * k + 13) :=
    budget_lt hti (le_max_left _ _) hM
  -- `SolveFits` reads the same cycle as Lemma 4.6 (bridge Lemma C)(iv) on `[0, L)` (literally, after `reorientIn`)
  set F : ℕ → ℂ := fun j : ℕ => Ys (shiftFin f (((j : ℤ) - (((f : ℕ) / aliasStep t i : ℕ) : ℤ)) *
    (aliasStep t i : ℤ))) with hF
  have hext : ∀ j < prefixProd t i, F j = extNat Yc j := by
    intro j hj
    simp only [extNat, dif_pos hj]
    rfl
  have hYY : ∀ j < prefixProd t i,
      (if 2 * u < t i then F else reorientIn (prefixProd t i) F) j =
        (if decide (2 * u < t i) then extNat Yc else reorientIn (prefixProd t i) (extNat Yc)) j := by
    intro j hj
    by_cases hfw : 2 * u < t i
    · rw [if_pos hfw, if_pos (decide_eq_true hfw)]
      exact hext j hj
    · rw [if_neg hfw, if_neg (show ¬(decide (2 * u < t i) = true) by simpa using hfw),
        PrecisionDeconvProof.reorientIn_congr _ hL0 F (extNat Yc) hext]
  obtain ⟨hz, hZ⟩ := sweep_bounds_congr hYY h2 h3
  exact sweepFits_of_bounds _ _ _ _ _ _ hL2 hahat hz hZ hB (by omega)

end SubNLogN.Machine.Pipe
