/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DriverSpec
import SubNLogN.Math.Cost.Recurrence
import SubNLogN.Math.Networks.Proofs.Counting
import IntMulTM.SpecFacts

/-!
# Layer driver math, helpers (`Machine/Layer/DrvMathAux.lean`)

Helper facts for the two math leaves `DrvCostStmt` and `DrvCtxStmt` of the layer driver
(`Machine/Layer/DriverSpec.lean`). Everything here is proved, with the hypotheses stated in each
lemma; there is no `sorry`.

* Base-`m` pieces (`piecesOf`): every piece fits (`offset + m^k ≤ e`), and there are at most
  `(m - 1)(⌊log₂ e⌋ + 1)` of them.
* Integer sizes in the row case: `padR ≤ 2^{q₀K+1}`, the stage record count `M' ≤ 2M`, the guarded
  volume `V_g ≤ 6V`, and the piece descriptor length `≤ 6·|hdr| + 2M + 12`.
* Logarithm absorption: `⌊log₂ d⌋ + 1 ≤ (4/δ)·d^δ` for `0 < δ ≤ 1`, and an integer form.
* Growth bounds (`ArrGrowth`) through the exact value-level semantics: address re-encodings, `𝒮_D`,
  one individual kernel on a binary field (`+1`), zero padding, `C^{⊗e}` (`+e`), one driver piece
  (`+cDepth k`), and the folds over phase 1 and over the pieces.
-/

namespace SubNLogN.Machine.Layer.DrvMathAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Machine SubNLogN.Machine.Layer
open SubNLogN.Math.Networks (q0Of padR piecesOf piecesAux useRows k0Of layerPhase1 embedArr
  encodeArr decodeArr cCoreVal layerLayout sDiag dgate cGate selField topClass mH Wc ka kb CD
  groupBits groupSel encodeAddr decodeAddr cardRole_holds)
open SubNLogN.Math.Networks.Model (ProcK Step RowClass)

/-! ## 1. Base-`m` pieces -/

/-- `mH` (the network ground dimension `m`) is `tripleM 100`. -/
theorem mH_eq : mH = tripleM 100 := by decide

theorem two_le_mH : 2 ≤ mH := by decide

/-- Offsets and lengths of `piecesAux ds j₀ o₀` (same statement as `mem_piecesAux`). -/
theorem mem_piecesAux' {j o : ℕ} : ∀ (ds : List ℕ) (j₀ o₀ : ℕ), (j, o) ∈ piecesAux ds j₀ o₀ →
    o₀ ≤ o ∧ o + mH ^ j ≤ o₀ + mH ^ j₀ * Nat.ofDigits mH ds
  | [], _, _, h => by simp [piecesAux] at h
  | a :: ds, j₀, o₀, h => by
    simp only [piecesAux, List.mem_append, List.mem_map, List.mem_range] at h
    rw [Nat.ofDigits_cons]
    rcases h with ⟨t, ht, he⟩ | h
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨by omega, ?_⟩
      have hle : (t + 1) * mH ^ j₀ ≤ a * mH ^ j₀ := Nat.mul_le_mul_right _ (by omega)
      nlinarith [Nat.zero_le (mH ^ j₀ * (mH * Nat.ofDigits mH ds))]
    · obtain ⟨h1, h2⟩ := mem_piecesAux' ds (j₀ + 1) (o₀ + a * mH ^ j₀) h
      refine ⟨by omega, ?_⟩
      have e : mH ^ (j₀ + 1) * Nat.ofDigits mH ds = mH ^ j₀ * (mH * Nat.ofDigits mH ds) := by
        ring
      nlinarith [e]

/-- Number of pieces of `piecesAux ds j o`: the digit sum. -/
theorem length_piecesAux : ∀ (ds : List ℕ) (j o : ℕ), (piecesAux ds j o).length = ds.sum
  | [], _, _ => by simp [piecesAux]
  | a :: ds, j, o => by
    simp only [piecesAux, List.length_append, List.length_map, List.length_range,
      length_piecesAux ds, List.sum_cons]

/-- Every base-`m` piece `(k, j0)` of `e` chunks fits: `j0 + m^k ≤ e`. -/
theorem piece_fits {e : ℕ} {pc : ℕ × ℕ} (h : pc ∈ piecesOf e) : pc.2 + mH ^ pc.1 ≤ e := by
  obtain ⟨k, o⟩ := pc
  have h2 := (mem_piecesAux' (Nat.digits mH e) 0 0 h).2
  simpa [Nat.ofDigits_digits] using h2

/-- The number of base-`m` pieces of `e` chunks is at most `(m - 1)(⌊log₂ e⌋ + 1)`. -/
theorem length_piecesOf_le (e : ℕ) : (piecesOf e).length ≤ (mH - 1) * (Nat.log2 e + 1) := by
  rw [piecesOf, length_piecesAux]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  have hlen := Nat.length_digits mH e (by decide) he.ne'
  have hsum : (Nat.digits mH e).sum ≤ (Nat.digits mH e).length • (mH - 1) :=
    List.sum_le_card_nsmul _ _ (fun x hx => Nat.le_pred_of_lt (Nat.digits_lt_base (by decide) hx))
  have hlog : Nat.log mH e ≤ Nat.log2 e := by
    rw [Nat.log2_eq_log_two]; exact Nat.log_anti_left (by norm_num) two_le_mH
  rw [smul_eq_mul, hlen] at hsum
  calc (Nat.digits mH e).sum ≤ (Nat.log mH e + 1) * (mH - 1) := hsum
    _ ≤ (Nat.log2 e + 1) * (mH - 1) := Nat.mul_le_mul_right _ (by omega)
    _ = (mH - 1) * (Nat.log2 e + 1) := by ring

/-- Depth of a piece of `e ≥ m^k` chunks: `k ≤ k₀(d) = ⌈log_m d⌉` when `e ≤ d`. -/
theorem piece_depth_le_k0 {k d : ℕ} (h : mH ^ k ≤ d) : k ≤ k0Of d := by
  unfold k0Of
  exact (Nat.le_log_of_pow_le (by decide) h).trans (Nat.log_le_clog _ _)

/-! ## 2. Bit lengths and descriptor lengths -/

theorem bitLen_eq_size' (n : ℕ) : bitLen n = Nat.size n := IntMulTM.length_encodeNat n

theorem bitLen_mono' {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  rw [bitLen_eq_size', bitLen_eq_size']; exact Nat.size_le_size h

theorem bitLen_le_self' (n : ℕ) : bitLen n ≤ n := by
  rw [bitLen_eq_size']; exact Nat.size_le.2 Nat.lt_two_pow_self

theorem bitLen_mul_le (a b : ℕ) : bitLen (a * b) ≤ bitLen a + bitLen b := by
  rw [bitLen_eq_size', bitLen_eq_size', bitLen_eq_size', Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem length_hdrSyms' (fs : List ℕ) : (hdrSyms fs).length = (fs.map bitLen).sum + fs.length := by
  induction fs with
  | nil => simp [hdrSyms]
  | cons f fs ih =>
    simp only [hdrSyms, List.flatMap_cons, List.length_append, length_natSyms,
      List.length_cons, List.length_nil, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem bitLen_le_hdr {fs : List ℕ} {x : ℕ} (hx : x ∈ fs) : bitLen x ≤ (hdrSyms fs).length := by
  rw [length_hdrSyms']
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := bitLen) hx)
  omega

/-! ## 3. Logarithm absorption -/

/-- `⌊log₂ d⌋ + 1 ≤ (4/δ)·d^δ` for `0 < δ ≤ 1` and `d ≥ 1`. -/
theorem log2_succ_le_rpow {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {d : ℕ} (hd : 1 ≤ d) :
    ((Nat.log2 d : ℕ) : ℝ) + 1 ≤ 4 / δ * (d : ℝ) ^ δ := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  rcases (show d = 1 ∨ 2 ≤ d by omega) with h | h
  · subst h
    simp only [Nat.cast_one, Real.one_rpow, mul_one]
    have : Nat.log2 1 = 0 := by decide
    rw [this, Nat.cast_zero, zero_add, le_div_iff₀ hδ]
    linarith
  · have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast h
    have habs := SubNLogN.Math.Cost.logb_pow_le_factorial_mul_rpow hd2 hδ 1
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at habs
    have hl2 : ((Nat.log2 d : ℕ) : ℝ) ≤ Real.logb 2 d := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hd0, Real.rpow_natCast]
      exact_mod_cast Nat.log2_self_le (by omega)
    have hl3 : Real.logb 2 (2 * d) = 1 + Real.logb 2 d := by
      rw [Real.logb_mul (by norm_num) hd0.ne', Real.logb_self_eq_one (by norm_num)]
    linarith

/-- Integer form: `(⌊log₂ d⌋ + 1)·⌈d^μ⌉₊ ≤ ⌈8/(λ' - μ)⌉₊·⌈d^{λ'}⌉₊` for `0 ≤ μ < λ' ≤ μ + 1`,
`d ≥ 1`. -/
theorem log2_mul_ceil_le {μ lam' : ℝ} (hμ : 0 ≤ μ) (hml : μ < lam') (hl1 : lam' - μ ≤ 1) {d : ℕ}
    (hd : 1 ≤ d) :
    (Nat.log2 d + 1) * ⌈(d : ℝ) ^ μ⌉₊ ≤ ⌈8 / (lam' - μ)⌉₊ * ⌈(d : ℝ) ^ lam'⌉₊ := by
  have hδ : 0 < lam' - μ := sub_pos.2 hml
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hL := log2_succ_le_rpow hδ hl1 hd
  have hY1 : (1 : ℝ) ≤ (d : ℝ) ^ μ := Real.one_le_rpow hd1 hμ
  have hY := SubNLogN.Math.Cost.Recurrence.ceil_le_two_mul hY1
  have h8 : 8 / (lam' - μ) ≤ (⌈8 / (lam' - μ)⌉₊ : ℝ) := Nat.le_ceil _
  have hdl : (d : ℝ) ^ lam' ≤ (⌈(d : ℝ) ^ lam'⌉₊ : ℝ) := Nat.le_ceil _
  have hsplit : (d : ℝ) ^ lam' = (d : ℝ) ^ (lam' - μ) * (d : ℝ) ^ μ := by
    rw [← Real.rpow_add hd0, sub_add_cancel]
  have hdδ : (0 : ℝ) ≤ (d : ℝ) ^ (lam' - μ) := by positivity
  have hdμ : (0 : ℝ) ≤ (d : ℝ) ^ μ := by positivity
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  calc (((Nat.log2 d : ℕ) : ℝ) + 1) * (⌈(d : ℝ) ^ μ⌉₊ : ℝ)
      ≤ (4 / (lam' - μ) * (d : ℝ) ^ (lam' - μ)) * (2 * (d : ℝ) ^ μ) :=
        mul_le_mul hL hY (by positivity) (by positivity)
    _ = 8 / (lam' - μ) * (d : ℝ) ^ lam' := by rw [hsplit]; ring
    _ ≤ (⌈8 / (lam' - μ)⌉₊ : ℝ) * (⌈(d : ℝ) ^ lam'⌉₊ : ℝ) :=
        mul_le_mul h8 hdl (by positivity) (by positivity)

/-- `⌈log_m 2d⌉ ≤ ⌊log₂ d⌋ + 2`. -/
theorem clog_two_mul_le (d : ℕ) : Nat.clog mH (2 * d) ≤ Nat.log2 d + 2 := by
  apply Nat.clog_le_of_le_pow
  have h1 : d < 2 ^ (Nat.log2 d + 1) := Nat.lt_log2_self
  have h2 : 2 ^ (Nat.log2 d + 2) ≤ mH ^ (Nat.log2 d + 2) := Nat.pow_le_pow_left two_le_mH _
  rw [pow_succ] at h2
  omega

/-- `q₀ + 1 ≤ (2⌈lg W_c⌉ + 1)(⌊log₂ d⌋ + 1)`. -/
theorem q0_succ_le (d : ℕ) : q0Of d + 1 ≤ (2 * Nat.clog 2 Wc + 1) * (Nat.log2 d + 1) := by
  unfold q0Of
  have h := Nat.mul_le_mul_left (Nat.clog 2 Wc) (clog_two_mul_le d)
  generalize Nat.clog 2 Wc = c at h ⊢
  generalize Nat.clog mH (2 * d) = a at h ⊢
  generalize Nat.log2 d = L at h ⊢
  have e1 : c * (L + 2) = c * L + 2 * c := by ring
  have e2 : (2 * c + 1) * (L + 1) = 2 * (c * L) + 2 * c + L + 1 := by ring
  rw [e2]
  omega

/-- The `q₀` bound with an existential constant (so that `⌈lg W_c⌉` never appears in later
arithmetic). -/
theorem q0_succ_le_exists : ∃ Cq : ℕ, ∀ d, q0Of d + 1 ≤ Cq * (Nat.log2 d + 1) :=
  ⟨_, q0_succ_le⟩

/-! ## 4. Integer sizes of the row case

`W_c = Fintype.card (Role .complex 100)` is a closed term whose value must never be computed by
the kernel. The lemmas below about `W_c^{k₀}` are therefore proved for an arbitrary `W` first and
only then instantiated (all comparisons with `W_c` are then syntactic). -/

/-- Abstract form of `W^{k₀} ≤ 2^{q₀}`, for any `W`. -/
theorem pow_clog_le_aux (W d : ℕ) :
    W ^ Nat.clog mH d ≤ 2 ^ (Nat.clog 2 W * Nat.clog mH (2 * d)) := by
  have hW : W ≤ 2 ^ Nat.clog 2 W := Nat.le_pow_clog (by norm_num) _
  have hk : Nat.clog mH d ≤ Nat.clog mH (2 * d) := Nat.clog_mono_right _ (by omega)
  calc W ^ Nat.clog mH d ≤ (2 ^ Nat.clog 2 W) ^ Nat.clog mH d := Nat.pow_le_pow_left hW _
    _ = 2 ^ (Nat.clog 2 W * Nat.clog mH d) := (pow_mul 2 _ _).symm
    _ ≤ 2 ^ (Nat.clog 2 W * Nat.clog mH (2 * d)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hk)

theorem wc_pow_k0_le (d : ℕ) : Wc ^ k0Of d ≤ 2 ^ q0Of d := pow_clog_le_aux Wc d

/-- The rounding in `padR`: `w·⌊(a + w - 1)/w⌋ ≤ 2a` for `w ≤ a`. -/
theorem mul_ceil_div_le {w a : ℕ} (hw : w ≤ a) : w * ((a + w - 1) / w) ≤ a * 2 := by
  have h1 : w * ((a + w - 1) / w) ≤ a + w - 1 := Nat.mul_div_le _ _
  calc w * ((a + w - 1) / w) ≤ a + w - 1 := h1
    _ ≤ a * 2 := by omega

/-- `padR ≤ 2^{q₀K+1}` for `K ≥ 1`. -/
theorem padR_le (d K : ℕ) (hK : 1 ≤ K) : padR d K ≤ 2 ^ (q0Of d * K + 1) := by
  have hw : Wc ^ k0Of d ≤ 2 ^ (q0Of d * K) :=
    (wc_pow_k0_le d).trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hK))
  unfold padR
  calc Wc ^ k0Of d * ((2 ^ (q0Of d * K) + Wc ^ k0Of d - 1) / Wc ^ k0Of d)
      ≤ 2 ^ (q0Of d * K) * 2 := mul_ceil_div_le hw
    _ = 2 ^ (q0Of d * K + 1) := (pow_succ 2 _).symm

/-- In the row case, `padR ≤ 2^{KD} ≤ M`. -/
theorem padR_le_M (t : LayerRT) (h : DrvRows t) (hK : 1 ≤ t.K) (hA : 1 ≤ t.A) (hS : 1 ≤ t.S) :
    padR t.d t.K ≤ t.M := by
  have hp := padR_le t.d t.K hK
  have hq : q0Of t.d + 1 ≤ t.D := Nat.succ_le_of_lt h.1
  have h0 := Nat.mul_le_mul_right t.K hq
  have e1 : (q0Of t.d + 1) * t.K = q0Of t.d * t.K + t.K := by ring
  have e2 : t.D * t.K = t.K * t.D := Nat.mul_comm _ _
  have h1 : q0Of t.d * t.K + 1 ≤ t.K * t.D := by omega
  calc padR t.d t.K ≤ 2 ^ (q0Of t.d * t.K + 1) := hp
    _ ≤ 2 ^ (t.K * t.D) := Nat.pow_le_pow_right (by norm_num) h1
    _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := Nat.le_mul_of_pos_left _ (Nat.mul_pos hA hS)

/-- In the row case the stage record count is at most twice the layer's: `M' ≤ 2M`. -/
theorem ctxM_le (t : LayerRT) (h : DrvRows t) (hK : 1 ≤ t.K) (b : ℕ) (pc : ℕ × ℕ) :
    (drvCtx t b pc).M ≤ 2 * t.M := by
  have hq : q0Of t.d < t.D := h.1
  have hp := padR_le t.d t.K hK
  obtain ⟨e, he⟩ : ∃ e, t.D = q0Of t.d + e := ⟨t.D - q0Of t.d, by omega⟩
  have hpe : padR t.d t.K * 2 ^ (t.K * (t.D - q0Of t.d)) ≤ 2 * 2 ^ (t.K * t.D) := by
    rw [he, Nat.add_sub_cancel_left]
    calc padR t.d t.K * 2 ^ (t.K * e) ≤ 2 ^ (q0Of t.d * t.K + 1) * 2 ^ (t.K * e) :=
          Nat.mul_le_mul_right _ hp
      _ = 2 * 2 ^ (t.K * (q0Of t.d + e)) := by
          rw [← pow_add, ← pow_succ']; congr 1; ring
  have hM : (drvCtx t b pc).M = t.A * padR t.d t.K * t.S * 2 ^ (t.K * (t.D - q0Of t.d)) := rfl
  rw [hM]
  calc t.A * padR t.d t.K * t.S * 2 ^ (t.K * (t.D - q0Of t.d))
      = t.A * t.S * (padR t.d t.K * 2 ^ (t.K * (t.D - q0Of t.d))) := by ring
    _ ≤ t.A * t.S * (2 * 2 ^ (t.K * t.D)) := Nat.mul_le_mul_left _ hpe
    _ = 2 * t.M := by simp only [LayerRT.M]; ring

/-- In the row case the guarded volume of a piece call is at most `6V`. -/
theorem ctx_volG_le (t : LayerRT) (h : DrvRows t) (hK : 1 ≤ t.K) (hw : t.P + 2 ≤ t.w) (b : ℕ)
    (pc : ℕ × ℕ) : (drvCtx t b pc).volG ≤ 6 * t.vol := by
  have hM := ctxM_le t h hK b pc
  have hwg : t.P + 2 * t.P + 3 ≤ 3 * t.w := by omega
  have hV : (drvCtx t b pc).volG = 2 * (drvCtx t b pc).M * t.r * (t.P + 2 * t.P + 3) := rfl
  rw [hV]
  calc 2 * (drvCtx t b pc).M * t.r * (t.P + 2 * t.P + 3) ≤ 2 * (2 * t.M) * t.r * (3 * t.w) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hM)) hwg
    _ = 6 * t.vol := by simp only [LayerRT.vol]; ring

/-! ## 5. Driver pieces: membership, descriptors, C-core cost -/

theorem drvPieces_of_rows {t : LayerRT} (h : DrvRows t) : drvPieces t = piecesOf (drvD' t) := by
  unfold drvPieces; rw [if_pos h]

theorem drvPieces_of_not_rows {t : LayerRT} (h : ¬ DrvRows t) : drvPieces t = [] := by
  unfold drvPieces; rw [if_neg h]

/-- A driver piece `(k, j0)` fits into the `D - q₀` stage chunks. -/
theorem piece_le_D {t : LayerRT} (h : DrvRows t) {pc : ℕ × ℕ} (hpc : pc ∈ drvPieces t) :
    pc.2 + mH ^ pc.1 ≤ t.D - q0Of t.d := by
  rw [drvPieces_of_rows h] at hpc
  exact piece_fits hpc

theorem log2_succ_le_of_le {x d : ℕ} (hx : x ≤ d) (hd : 1 ≤ d) : Nat.log2 x + 1 ≤ d := by
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · have : Nat.log2 0 = 0 := by decide
    omega
  · have h1 : 2 ^ Nat.log2 x ≤ x := Nat.log2_self_le hx0.ne'
    have h2 : Nat.log2 x < 2 ^ Nat.log2 x := Nat.lt_two_pow_self
    omega

/-- The number of driver pieces is at most `m·(⌊log₂ d⌋ + 1)` (for `D ≤ d`). -/
theorem length_drvPieces_le (t : LayerRT) (hDd : t.D ≤ t.d) :
    (drvPieces t).length ≤ mH * (Nat.log2 t.d + 1) := by
  by_cases h : DrvRows t
  · rw [drvPieces_of_rows h]
    have h1 := length_piecesOf_le (drvD' t)
    have h2 : Nat.log2 (drvD' t) ≤ Nat.log2 t.d := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.log_mono_right ((Nat.sub_le _ _).trans hDd)
    calc _ ≤ (mH - 1) * (Nat.log2 (drvD' t) + 1) := h1
      _ ≤ mH * (Nat.log2 t.d + 1) := Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
  · rw [drvPieces_of_not_rows h]; simp

theorem length_hdrSyms12 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : ℕ) :
    (hdrSyms [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]).length =
      bitLen a1 + bitLen a2 + bitLen a3 + bitLen a4 + bitLen a5 + bitLen a6 + bitLen a7 +
        bitLen a8 + bitLen a9 + bitLen a10 + bitLen a11 + bitLen a12 + 12 := by
  rw [length_hdrSyms']
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil]
  ring

theorem length_hdrSyms9 (a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℕ) :
    (hdrSyms [a1, a2, a3, a4, a5, a6, a7, a8, a9]).length =
      bitLen a1 + bitLen a2 + bitLen a3 + bitLen a4 + bitLen a5 + bitLen a6 + bitLen a7 +
        bitLen a8 + bitLen a9 + 9 := by
  rw [length_hdrSyms']
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil]
  ring

/-- Descriptor length of a piece call: at most `11·|hdr| + 2M + 12`. (`q₀` and `padR` are
generalized before any arithmetic automation runs, so that `W_c` is never evaluated.) -/
theorem ctx_hdr_le (t : LayerRT) (h : DrvRows t) (hK : 1 ≤ t.K) (hA : 1 ≤ t.A) (hS : 1 ≤ t.S)
    (b : ℕ) (pc : ℕ × ℕ) (hpc : pc ∈ drvPieces t) :
    (drvCtx t b pc).hdr.length ≤ 11 * t.hdr.length + 2 * t.M + 12 := by
  have hfit := piece_le_D h hpc
  have hfit' : pc.2 + mH ^ pc.1 ≤ t.D := le_trans hfit (Nat.sub_le _ _)
  have hj0 : pc.2 ≤ t.D := le_trans (Nat.le_add_right _ _) hfit'
  have hk : pc.1 ≤ t.D := by
    have h1 : pc.1 < mH ^ pc.1 := Nat.lt_pow_self (by decide)
    exact le_trans h1.le (le_trans (Nat.le_add_left _ _) hfit')
  have hR : bitLen (padR t.d t.K) ≤ t.M := (bitLen_le_self' _).trans (padR_le_M t h hK hA hS)
  have h1 := bitLen_mul_le t.A (padR t.d t.K)
  have h2 : bitLen (t.D - q0Of t.d) ≤ bitLen t.D := bitLen_mono' (Nat.sub_le _ _)
  have h3 : bitLen pc.2 ≤ bitLen t.D := bitLen_mono' hj0
  have h4 : bitLen pc.1 ≤ bitLen t.D := bitLen_mono' hk
  have h5 : bitLen t.ρ ≤ bitLen (t.ρ + 1) := bitLen_mono' (Nat.le_succ _)
  have e : (drvCtx t b pc).hdr = hdrSyms [t.P, t.d, t.r, t.P, t.A * padR t.d t.K,
      padR t.d t.K, t.K, t.D - q0Of t.d, t.S, pc.2, pc.1, t.ρ] := rfl
  have eT : t.hdr = hdrSyms [t.P, t.d, t.r, t.D, t.A, t.S, t.K, t.ρ + 1, t.w] := rfl
  rw [e, eT, length_hdrSyms12, length_hdrSyms9]
  clear e eT hfit hfit' hpc hj0 hk h
  generalize q0Of t.d = q at h2 ⊢
  generalize padR t.d t.K = R at h1 hR ⊢
  generalize bitLen (t.A * R) = xAR at h1 ⊢
  generalize bitLen R = xR at h1 hR ⊢
  generalize bitLen (t.D - q) = xD' at h2 ⊢
  generalize bitLen pc.2 = xj at h3 ⊢
  generalize bitLen pc.1 = xk at h4 ⊢
  generalize bitLen (t.ρ + 1) = xρ1 at h5 ⊢
  generalize bitLen t.ρ = xρ at h5 ⊢
  generalize bitLen t.D = xD at h2 h3 h4 ⊢
  generalize bitLen t.A = xA at h1 ⊢
  generalize t.M = M at hR ⊢
  omega

/-- C-core cost of a piece call: at most `12·V·⌈d^μ⌉₊`, for `μ ≥ λ` and `μ ≥ σ + β(1-σ)`. -/
theorem ccoreCost_le (p : LayerParams) (βn βd : ℕ) (t : LayerRT) (h : DrvRows t) (hK : 1 ≤ t.K)
    (hw : t.P + 2 ≤ t.w) (hDd : t.D ≤ t.d) (hσ : 0 ≤ p.σ) (hl : 0 ≤ p.lam) {μ : ℝ}
    (hμ1 : p.lam ≤ μ) (hμ2 : p.σ + (βn : ℝ) / βd * (1 - p.σ) ≤ μ) (b : ℕ) (pc : ℕ × ℕ)
    (hpc : pc ∈ drvPieces t) :
    cCoreCost p βn βd (drvCtx t b pc) ≤ 12 * t.vol * ⌈(t.d : ℝ) ^ μ⌉₊ := by
  have he : mH ^ pc.1 ≤ t.d :=
    le_trans (le_trans (Nat.le_add_left _ _) (le_trans (piece_le_D h hpc) (Nat.sub_le _ _))) hDd
  have hd : 1 ≤ t.d := le_trans (Nat.one_le_pow _ _ (by decide)) he
  have hV := ctx_volG_le t h hK hw b pc
  have hee : (drvCtx t b pc).e = mH ^ pc.1 := by rw [mH_eq]; rfl
  have hdc : (drvCtx t b pc).d = t.d := rfl
  have hcc : cCoreCost p βn βd (drvCtx t b pc) = ⌈((drvCtx t b pc).volG : ℝ) *
      (((mH ^ pc.1 : ℕ) : ℝ) ^ p.lam + ((mH ^ pc.1 : ℕ) : ℝ) ^ p.σ *
        (t.d : ℝ) ^ ((βn : ℝ) / βd * (1 - p.σ)))⌉₊ := by
    unfold cCoreCost
    rw [hee, hdc]
  rw [hcc]
  clear hcc hee hdc hpc h
  generalize (drvCtx t b pc).volG = Vg at hV ⊢
  generalize mH ^ pc.1 = E at he ⊢
  have hd1 : (1 : ℝ) ≤ t.d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < t.d := by linarith
  have he0 : (0 : ℝ) ≤ (E : ℝ) := Nat.cast_nonneg _
  have he' : (E : ℝ) ≤ t.d := by exact_mod_cast he
  have hV' : (Vg : ℝ) ≤ 6 * (t.vol : ℝ) := by exact_mod_cast hV
  have hF1 : (E : ℝ) ^ p.lam ≤ (t.d : ℝ) ^ μ :=
    (Real.rpow_le_rpow he0 he' hl).trans (Real.rpow_le_rpow_of_exponent_le hd1 hμ1)
  have hF2 : (E : ℝ) ^ p.σ * (t.d : ℝ) ^ ((βn : ℝ) / βd * (1 - p.σ)) ≤ (t.d : ℝ) ^ μ := by
    calc (E : ℝ) ^ p.σ * (t.d : ℝ) ^ ((βn : ℝ) / βd * (1 - p.σ))
        ≤ (t.d : ℝ) ^ p.σ * (t.d : ℝ) ^ ((βn : ℝ) / βd * (1 - p.σ)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow he0 he' hσ) (by positivity)
      _ = (t.d : ℝ) ^ (p.σ + (βn : ℝ) / βd * (1 - p.σ)) := (Real.rpow_add hd0 _ _).symm
      _ ≤ (t.d : ℝ) ^ μ := Real.rpow_le_rpow_of_exponent_le hd1 hμ2
  have hY : (t.d : ℝ) ^ μ ≤ (⌈(t.d : ℝ) ^ μ⌉₊ : ℝ) := Nat.le_ceil _
  have hF0 : 0 ≤ (E : ℝ) ^ p.lam + (E : ℝ) ^ p.σ * (t.d : ℝ) ^ ((βn : ℝ) / βd * (1 - p.σ)) :=
    add_nonneg (Real.rpow_nonneg he0 _)
      (mul_nonneg (Real.rpow_nonneg he0 _) (Real.rpow_nonneg hd0.le _))
  apply Nat.ceil_le.2
  push_cast
  calc (Vg : ℝ) * ((E : ℝ) ^ p.lam + (E : ℝ) ^ p.σ * (t.d : ℝ) ^ ((βn : ℝ) / βd * (1 - p.σ)))
      ≤ (6 * (t.vol : ℝ)) * (2 * (⌈(t.d : ℝ) ^ μ⌉₊ : ℝ)) :=
        mul_le_mul hV' (by linarith) hF0 (by positivity)
    _ = 12 * (t.vol : ℝ) * (⌈(t.d : ℝ) ^ μ⌉₊ : ℝ) := by ring

/-! ## 6. Growth bounds through the value semantics -/

theorem arrGrowth_mono {α : Type} {r P b b' : ℕ} {z : RArr α r} (h : b ≤ b')
    (hz : ArrGrowth P b z) : ArrGrowth P b' z := fun x k =>
  ⟨(hz x k).1.mono (by omega), (hz x k).2.trans (pow_le_pow_right₀ (by norm_num) h)⟩

theorem arrGrowth_of_disk {α : Type} {r P : ℕ} {z : RArr α r} (hz : ArrOnDiskGrid P z) :
    ArrGrowth P 0 z := fun x k => ⟨by simpa using (hz x k).1, by simpa using (hz x k).2⟩

theorem arrGrowth_comp {α γ : Type} {r P b : ℕ} {z : RArr α r} (f : γ → α)
    (hz : ArrGrowth P b z) : ArrGrowth P b (fun y => z (f y)) := fun y k => hz (f y) k

theorem encodeArr_growth {A K D S r P b : ℕ} {z : RArr (LayerAddr A K D S) r}
    (hz : ArrGrowth P b z) : ArrGrowth P b (encodeArr z) := arrGrowth_comp decodeAddr hz

theorem decodeArr_growth {A K D S r P b : ℕ} {y : (layerLayout A K D S).Addr → Fin r → ℂ}
    (hy : ArrGrowth P b y) : ArrGrowth P b (decodeArr y) := arrGrowth_comp encodeAddr hy

theorem onGrid_one' (q : ℕ) : OnGrid q 1 := by
  have h := onGrid_intCast q 1 0
  convert h using 1
  apply Complex.ext <;> simp

theorem onGrid_ka : OnGrid 1 ka := by
  have h0 : OnGrid 0 (1 + Complex.I) := by
    have h := onGrid_intCast 0 1 1
    convert h using 1
    apply Complex.ext <;> simp
  have h := h0.half
  simpa [ka] using h

theorem onGrid_kb : OnGrid 1 kb := by
  have h0 : OnGrid 0 (1 - Complex.I) := by
    have h := onGrid_intCast 0 1 (-1)
    convert h using 1
    apply Complex.ext <;> simp
  have h := h0.half
  simpa [kb] using h

theorem norm_ka_le : ‖ka‖ ≤ 1 := by
  unfold ka
  have h1 : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := by
    calc ‖(1 : ℂ) + Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one, Complex.norm_I]; norm_num
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp, div_le_one (by norm_num)]
  exact h1

theorem norm_kb_le : ‖kb‖ ≤ 1 := by
  unfold kb
  have h1 : ‖(1 : ℂ) - Complex.I‖ ≤ 2 := by
    calc ‖(1 : ℂ) - Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, Complex.norm_I]; norm_num
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp, div_le_one (by norm_num)]
  exact h1

theorem onGrid_I_pow_mul {q : ℕ} {z : ℂ} (hz : OnGrid q z) :
    ∀ n : ℕ, OnGrid q (Complex.I ^ n * z)
  | 0 => by simpa using hz
  | n + 1 => by
    have := (onGrid_I_pow_mul hz n).mul_I
    rw [pow_succ, mul_right_comm]; exact this

theorem onGrid_prod_fin : ∀ (n : ℕ) (g : Fin n → ℂ), (∀ j, OnGrid 1 (g j)) → OnGrid n (∏ j, g j)
  | 0, g, _ => by rw [Fin.prod_univ_zero]; exact onGrid_one' 0
  | n + 1, g, hg => by
    rw [Fin.prod_univ_succ]
    have := (hg 0).mul (onGrid_prod_fin n (fun j => g j.succ) (fun j => hg j.succ))
    rwa [show 1 + n = n + 1 by omega] at this

theorem runIn_growth {L : SubNLogN.Math.Networks.Model.Layout} {rr P b b' : ℕ} (c : RowClass L)
    (s : Step L (Fin rr → ℂ)) (A : L.Addr → Fin rr → ℂ) (hA : ArrGrowth P b A) (hbb : b ≤ b')
    (hs : ArrGrowth P b' (s.run A)) : ArrGrowth P b' (Step.runIn c s A) := by
  intro x k
  simp only [Step.runIn]
  split_ifs
  · exact hs x k
  · exact (arrGrowth_mono hbb hA) x k

theorem sDiag_run_growth {A K D S rr P b : ℕ} (ρ : ℕ)
    (Ar : (layerLayout A K D S).Addr → Fin rr → ℂ) (h : ArrGrowth P b Ar) :
    ArrGrowth P b ((sDiag (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ).run Ar) := by
  intro x k
  simp only [sDiag, Step.run, Pi.smul_apply, smul_eq_mul]
  obtain ⟨hg, hn⟩ := h x k
  refine ⟨onGrid_I_pow_mul hg _, ?_⟩
  rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  exact hn

/-- One individual kernel `C(u, v) = (au + bv, bu + av)` on a binary field: growth `+1`. -/
theorem cGate_growth {n rr P b : ℕ} (hn : n = 2) (v : Fin n → Fin rr → ℂ)
    (hv : ∀ t k, OnGrid (P + b) (v t k) ∧ ‖v t k‖ ≤ 2 ^ b) (t : Fin n) (k : Fin rr) :
    OnGrid (P + (b + 1)) (cGate v t k) ∧ ‖cGate v t k‖ ≤ 2 ^ (b + 1) := by
  subst hn
  have hsum : (∑ t' ∈ Finset.univ.erase t, v t') k = ∑ t' ∈ Finset.univ.erase t, v t' k :=
    Finset.sum_apply k _ _
  simp only [cGate, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsum]
  have hS : OnGrid (P + b) (∑ t' ∈ Finset.univ.erase t, v t' k) :=
    Finset.sum_induction _ (OnGrid (P + b)) (fun _ _ ha hb => ha.add hb) (onGrid_zero _)
      (fun t' _ => (hv t' k).1)
  have hq : 1 + (P + b) = P + (b + 1) := by omega
  refine ⟨?_, ?_⟩
  · have h1 := onGrid_ka.mul (hv t k).1
    have h2 := onGrid_kb.mul hS
    rw [hq] at h1 h2
    exact h1.add h2
  · have hcard : (Finset.univ.erase t).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have hSn : ‖∑ t' ∈ Finset.univ.erase t, v t' k‖ ≤ 2 ^ b := by
      calc ‖∑ t' ∈ Finset.univ.erase t, v t' k‖ ≤ ∑ t' ∈ Finset.univ.erase t, ‖v t' k‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _t' ∈ Finset.univ.erase t, (2 : ℝ) ^ b := Finset.sum_le_sum (fun t' _ => (hv t' k).2)
        _ = 2 ^ b := by rw [Finset.sum_const, hcard, one_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    calc ‖ka‖ * ‖v t k‖ + ‖kb‖ * ‖∑ t' ∈ Finset.univ.erase t, v t' k‖ ≤ 1 * 2 ^ b + 1 * 2 ^ b :=
          add_le_add (mul_le_mul norm_ka_le (hv t k).2 (norm_nonneg _) zero_le_one)
            (mul_le_mul norm_kb_le hSn (norm_nonneg _) zero_le_one)
      _ = 2 ^ (b + 1) := by ring

theorem digitGate_run_growth {L : SubNLogN.Math.Networks.Model.Layout} {rr P b : ℕ} (i : Fin L.n)
    (hi : L.r i = 2) (A : L.Addr → Fin rr → ℂ) (h : ArrGrowth P b A) :
    ArrGrowth P (b + 1) ((Step.digitGate i cGate : Step L (Fin rr → ℂ)).run A) := by
  intro x k
  simp only [Step.run]
  exact cGate_growth hi _ (fun t k => h _ k) (x i) k

theorem mem_dgate {A K D S rr i : ℕ} {s : Step (layerLayout A K D S) (Fin rr → ℂ)}
    (hs : s ∈ (dgate i : List (Step (layerLayout A K D S) (Fin rr → ℂ)))) :
    ∃ h : i < (layerLayout A K D S).n, s = .digitGate ⟨i, h⟩ cGate := by
  unfold dgate at hs
  split_ifs at hs with h
  · exact ⟨h, List.mem_singleton.1 hs⟩
  · simp at hs

/-- The selected-bit field of chunk `j < D` is binary. -/
theorem layerLayout_r_sel {A K D S j ρ : ℕ} (hj : j < D) (hρ : ρ < K)
    (h : selField K ρ j < (layerLayout A K D S).n) :
    (layerLayout A K D S).r ⟨selField K ρ j, h⟩ = 2 := by
  have h1 : (j + 1) * K ≤ D * K := Nat.mul_le_mul_right _ hj
  rw [Nat.succ_mul] at h1
  simp only [layerLayout, selField]
  split_ifs <;> omega

theorem foldl_runIn_growth {L : SubNLogN.Math.Networks.Model.Layout} {rr P : ℕ} (c : RowClass L) :
    ∀ (l : List (Step L (Fin rr → ℂ))) (b : ℕ) (A : L.Addr → Fin rr → ℂ),
      (∀ s ∈ l, ∀ (b' : ℕ) (A' : L.Addr → Fin rr → ℂ), ArrGrowth P b' A' →
        ArrGrowth P (b' + 1) (s.run A')) →
      ArrGrowth P b A → ArrGrowth P (b + l.length) (l.foldl (fun X s => Step.runIn c s X) A)
  | [], b, A, _, hA => by simpa using hA
  | s :: l, b, A, hl, hA => by
    simp only [List.foldl_cons, List.length_cons]
    have h1 : ArrGrowth P (b + 1) (Step.runIn c s A) :=
      runIn_growth c s A hA (by omega) (hl s (by simp) b A hA)
    have h2 := foldl_runIn_growth c l (b + 1) _ (fun s' hs' => hl s' (by simp [hs'])) h1
    rwa [show b + 1 + l.length = b + (l.length + 1) by omega] at h2

theorem length_dgates_le (A K D S rr ρ n : ℕ) :
    ((List.range n).flatMap fun j =>
      (dgate (selField K ρ j) : List (Step (layerLayout A K D S) (Fin rr → ℂ)))).length ≤ n := by
  rw [List.length_flatMap]
  have h : ∀ x ∈ (List.range n).map (fun j =>
      (dgate (selField K ρ j) : List (Step (layerLayout A K D S) (Fin rr → ℂ))).length), x ≤ 1 := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    unfold dgate; split_ifs <;> simp
  have := List.sum_le_card_nsmul _ 1 h
  simpa using this

/-- Abstract phase 1: `𝒮_D`, then the individual kernels on the first `n ≤ D` chunks, raise the
growth bound by at most `n`. -/
theorem phase1_growth_aux {A K D S rr ρ P : ℕ} (hρ : ρ < K) (n : ℕ) (hn : n ≤ D)
    (Ar : (layerLayout A K D S).Addr → Fin rr → ℂ) (h : ArrGrowth P 0 Ar) :
    ArrGrowth P n (List.foldl (fun X s => Step.runIn (topClass A K D S) s X) Ar
      ([sDiag ρ] ++ (List.range n).flatMap fun j => dgate (selField K ρ j))) := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have h0 : ArrGrowth P 0 (Step.runIn (topClass A K D S) (sDiag ρ) Ar) :=
    runIn_growth _ _ _ h le_rfl (sDiag_run_growth ρ Ar h)
  have hrest := foldl_runIn_growth (topClass A K D S)
    ((List.range n).flatMap fun j => dgate (selField K ρ j)) 0 _ ?_ h0
  · have hlen := length_dgates_le A K D S rr ρ n
    exact arrGrowth_mono (by omega) hrest
  · intro s hs b' A' hA'
    obtain ⟨j, hj, hs'⟩ := List.mem_flatMap.1 hs
    obtain ⟨hi, rfl⟩ := mem_dgate hs'
    have hjD : j < D := lt_of_lt_of_le (List.mem_range.1 hj) hn
    exact digitGate_run_growth _ (layerLayout_r_sel hjD hρ hi) A' hA'

/-- Phase 1 (`𝒮_D`, then at most `q₀` individual kernels) raises the growth bound by at most
`q₀`. -/
theorem phase1_growth {A K D S rr ρ d P : ℕ} (hρ : ρ < K)
    (Ar : (layerLayout A K D S).Addr → Fin rr → ℂ) (h : ArrGrowth P 0 Ar) :
    ArrGrowth P (q0Of d) (ProcK.run 0 (layerPhase1 A K D S rr ρ d) (topClass A K D S) Ar) := by
  have e1 : ProcK.run 0 (layerPhase1 A K D S rr ρ d) (topClass A K D S) Ar =
      List.foldl (fun X s => Step.runIn (topClass A K D S) s X) Ar
        ([sDiag ρ] ++ (List.range (min (q0Of d) D)).flatMap fun j => dgate (selField K ρ j)) :=
    rfl
  rw [e1]
  generalize q0Of d = q
  exact arrGrowth_mono (min_le_left _ _) (phase1_growth_aux hρ (min q D) (min_le_right _ _) Ar h)

/-- Zero padding keeps the growth bound. -/
theorem embedArr_growth {A K D S q R rr P b : ℕ} (hR : 0 < R) (hq : q ≤ D)
    (A0 : (layerLayout A K D S).Addr → Fin rr → ℂ) (h : ArrGrowth P b A0) :
    ArrGrowth P b (embedArr hR hq A0) := by
  intro y k
  simp only [embedArr]
  split_ifs with hy
  · exact h _ k
  · exact ⟨onGrid_zero _, by simp⟩

/-- `C^{⊗e}` raises the growth bound by at most `e`: each output coefficient is a sum of `2^e`
products of `e` factors `a, b ∈ 2^{-1}ℤ[i]` (of modulus `≤ 1`) with an input coefficient. -/
theorem cCoreVal_growth {r A K D S P b : ℕ} (ρ : Fin K) (j0 e : ℕ) (h : j0 + e ≤ D)
    (z : RArr (LayerAddr A K D S) r) (hz : ArrGrowth P b z) :
    ArrGrowth P (b + e) (cCoreVal ρ j0 e h z) := by
  intro x k
  simp only [cCoreVal, CD]
  have hq : e + (P + b) = P + (b + e) := by omega
  have hprod : ∀ e' : Fin e → Bool,
      OnGrid e (∏ j, (if groupBits ρ j0 e h x j = e' j then ka else kb)) := fun e' =>
    onGrid_prod_fin e _ (fun j => by split_ifs; exacts [onGrid_ka, onGrid_kb])
  have hpn : ∀ e' : Fin e → Bool,
      ‖∏ j, (if groupBits ρ j0 e h x j = e' j then ka else kb)‖ ≤ 1 := fun e' => by
    rw [norm_prod]
    apply Finset.prod_le_one (fun j _ => norm_nonneg _)
    intro j _
    split_ifs
    exacts [norm_ka_le, norm_kb_le]
  refine ⟨?_, ?_⟩
  · apply Finset.sum_induction _ (OnGrid (P + (b + e))) (fun _ _ ha hb => ha.add hb)
      (onGrid_zero _)
    intro e' _
    have := (hprod e').mul (hz (groupSel ρ j0 e x e') k).1
    rwa [hq] at this
  · refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _e' : Fin e → Bool, (2 : ℝ) ^ b := by
          apply Finset.sum_le_sum
          intro e' _
          rw [norm_mul]
          calc _ ≤ 1 * 2 ^ b := mul_le_mul (hpn e') (hz _ k).2 (norm_nonneg _) zero_le_one
            _ = 2 ^ b := one_mul _
      _ = 2 ^ (b + e) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring

theorem tripleM_le_tripleSc : tripleM 100 ≤ tripleSc 100 := by decide

/-- `m^k ≤ A(k)` (`cDepth`): the depth bound dominates the growth of one piece. -/
theorem pow_le_cDepth (d βn βd E : ℕ) : ∀ k, tripleM 100 ^ k ≤ cDepth d βn βd E k
  | 0 => by simp [cDepth]
  | k + 1 => by
    have ih := pow_le_cDepth d βn βd E k
    simp only [cDepth]
    split_ifs
    · omega
    · calc tripleM 100 ^ (k + 1) = tripleM 100 ^ k * tripleM 100 := pow_succ _ _
        _ ≤ cDepth d βn βd E k * tripleSc 100 := Nat.mul_le_mul ih tripleM_le_tripleSc
        _ ≤ tripleSc 100 * cDepth d βn βd E k + E := by rw [Nat.mul_comm]; omega

/-- `A(k) ≤ (8 + E_*)·(m^k)^5` (`depth_le_of_rec`, with `s_c < m^5`). -/
theorem cDepth_le (d βn βd E k : ℕ) : cDepth d βn βd E k ≤ (8 + E) * (tripleM 100 ^ k) ^ 5 :=
  SubNLogN.Math.Cost.Recurrence.depth_le_of_rec (D := cDepth d βn βd E) (by decide)
    SubNLogN.Math.Networks.sc_lt_m_pow5 (by simp [cDepth])
    (fun k => by simp only [cDepth]; split_ifs <;> simp) k

/-- One driver piece raises the growth bound by at most `cDepth k`. -/
theorem pieceStep_growth (t : LayerRT) (hρ : t.ρ < t.K) (βn βd E : ℕ) (pc : ℕ × ℕ)
    (y : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r) (b : ℕ) (hy : ArrGrowth t.P b y) :
    ArrGrowth t.P (b + cDepth t.d βn βd E pc.1) (pieceStep t hρ pc y) := by
  unfold pieceStep
  split_ifs with hg
  · exact arrGrowth_mono (by have := pow_le_cDepth t.d βn βd E pc.1; omega)
      (cCoreVal_growth _ _ _ hg y hy)
  · exact arrGrowth_mono (by omega) hy

theorem foldl_pieceStep_growth (t : LayerRT) (hρ : t.ρ < t.K) (βn βd E : ℕ) :
    ∀ (l : List (ℕ × ℕ)) (b : ℕ) (y : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r),
      ArrGrowth t.P b y →
      ArrGrowth t.P (b + (l.map fun pc => cDepth t.d βn βd E pc.1).sum)
        (l.foldl (fun y pc => pieceStep t hρ pc y) y)
  | [], b, y, h => by simpa using h
  | pc :: l, b, y, h => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have := foldl_pieceStep_growth t hρ βn βd E l _ _ (pieceStep_growth t hρ βn βd E pc y b h)
    rwa [Nat.add_assoc] at this

/-- The stage array before piece `i` has growth bound `drvB i`. -/
theorem drvYs_growth (t : LayerRT) (hρ : t.ρ < t.K) (βn βd E : ℕ)
    (y₀ : RArr (LayerAddr (drvA' t) t.K (drvD' t) t.S) t.r) (hy : ArrGrowth t.P (q0Of t.d) y₀)
    (i : ℕ) : ArrGrowth t.P (drvB t βn βd E i) (drvYs t hρ y₀ i) :=
  foldl_pieceStep_growth t hρ βn βd E _ _ _ hy

theorem drvA1_growth (t : LayerRT) (hρ : t.ρ < t.K) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r)
    (hz : ArrOnDiskGrid t.P z) : ArrGrowth t.P (q0Of t.d) (drvA1 t z) :=
  decodeArr_growth (phase1_growth hρ _ (encodeArr_growth (arrGrowth_of_disk hz)))

theorem drvStageIn_growth (t : LayerRT) (hρ : t.ρ < t.K) (h : DrvRows t)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (hz : ArrOnDiskGrid t.P z) :
    ArrGrowth t.P (q0Of t.d) (drvStageIn t h z) :=
  decodeArr_growth (embedArr_growth _ _ _
    (phase1_growth hρ _ (encodeArr_growth (arrGrowth_of_disk hz))))

/-! ## 7. Guard arithmetic -/

/-- `drvB` steps by the depth of the current piece. -/
theorem drvB_succ (t : LayerRT) (βn βd E i : ℕ) (hi : i < (drvPieces t).length) :
    drvB t βn βd E i + cDepth t.d βn βd E ((drvPieces t).get ⟨i, hi⟩).1 =
      drvB t βn βd E (i + 1) := by
  unfold drvB
  generalize q0Of t.d = q
  have e1 : (drvPieces t).get ⟨i, hi⟩ = (drvPieces t)[i] := List.get_eq_getElem
  rw [e1, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem sum_map_take_le {α : Type} (f : α → ℕ) (l : List α) (i : ℕ) :
    ((l.take i).map f).sum ≤ (l.map f).sum := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.map_append, List.sum_append]
  omega

/-- `drvB i ≤ q₀ + Σ_pieces cDepth`. -/
theorem drvB_le (t : LayerRT) (βn βd E i : ℕ) :
    drvB t βn βd E i ≤ q0Of t.d + ((drvPieces t).map fun pc => cDepth t.d βn βd E pc.1).sum := by
  unfold drvB
  generalize q0Of t.d = q
  have := sum_map_take_le (fun pc : ℕ × ℕ => cDepth t.d βn βd E pc.1) (drvPieces t) i
  omega

theorem drvB_length (t : LayerRT) (βn βd E : ℕ) :
    drvB t βn βd E (drvPieces t).length =
      q0Of t.d + ((drvPieces t).map fun pc => cDepth t.d βn βd E pc.1).sum := by
  unfold drvB
  rw [List.take_length]

theorem drvB_zero (t : LayerRT) (βn βd E : ℕ) : drvB t βn βd E 0 = q0Of t.d := by
  unfold drvB
  rw [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero]

/-- `Σ_pieces cDepth(k) ≤ #pieces·(8 + E_*)·d^5`. -/
theorem sum_cDepth_le (t : LayerRT) (hDd : t.D ≤ t.d) (βn βd E : ℕ) :
    ((drvPieces t).map fun pc => cDepth t.d βn βd E pc.1).sum ≤
      (drvPieces t).length * ((8 + E) * t.d ^ 5) := by
  by_cases h : DrvRows t
  · have := List.sum_le_card_nsmul ((drvPieces t).map fun pc => cDepth t.d βn βd E pc.1)
      ((8 + E) * t.d ^ 5) ?_
    · simpa using this
    · intro x hx
      obtain ⟨pc, hpc, rfl⟩ := List.mem_map.1 hx
      have hfit := piece_le_D h hpc
      have he : tripleM 100 ^ pc.1 ≤ t.d := by
        rw [← mH_eq]
        have : t.D - q0Of t.d ≤ t.D := Nat.sub_le _ _
        omega
      calc cDepth t.d βn βd E pc.1 ≤ (8 + E) * (tripleM 100 ^ pc.1) ^ 5 := cDepth_le _ _ _ _ _
        _ ≤ (8 + E) * t.d ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he 5)
  · rw [drvPieces_of_not_rows h]; simp

/-- The total guard demand `q₀ + Σ cDepth + D` is at most `C_g·d^6` for a constant `C_g`
depending only on `E_*`. -/
theorem guard_le_exists (βn βd E : ℕ) : ∃ Cg : ℕ, ∀ t : LayerRT, t.D ≤ t.d → 1 ≤ t.d →
    q0Of t.d + ((drvPieces t).map fun pc => cDepth t.d βn βd E pc.1).sum + t.D ≤
      Cg * t.d ^ 6 := by
  obtain ⟨Cq, hCq⟩ := q0_succ_le_exists
  refine ⟨Cq + mH * (8 + E) + 1, fun t hDd hd => ?_⟩
  have hq := hCq t.d
  have hlog : Nat.log2 t.d + 1 ≤ t.d := log2_succ_le_of_le le_rfl hd
  have hd6 : t.d ≤ t.d ^ 6 := Nat.le_self_pow (by norm_num) _
  have hN : (drvPieces t).length ≤ mH * t.d :=
    (length_drvPieces_le t hDd).trans (Nat.mul_le_mul_left _ hlog)
  have hsum : ((drvPieces t).map fun pc => cDepth t.d βn βd E pc.1).sum ≤
      mH * (8 + E) * t.d ^ 6 := by
    calc _ ≤ (drvPieces t).length * ((8 + E) * t.d ^ 5) := sum_cDepth_le t hDd βn βd E
      _ ≤ (mH * t.d) * ((8 + E) * t.d ^ 5) := Nat.mul_le_mul_right _ hN
      _ = mH * (8 + E) * t.d ^ 6 := by ring
  have hq' : q0Of t.d + 1 ≤ Cq * t.d ^ 6 :=
    hq.trans ((Nat.mul_le_mul_left _ hlog).trans (Nat.mul_le_mul_left _ hd6))
  generalize ((drvPieces t).map fun pc => cDepth t.d βn βd E pc.1).sum = S at hsum ⊢
  generalize t.d ^ 6 = X at hq' hsum hd6 ⊢
  generalize q0Of t.d = q at hq' ⊢
  have e : (Cq + mH * (8 + E) + 1) * X = Cq * X + mH * (8 + E) * X + X := by ring
  rw [e]
  omega

end SubNLogN.Machine.Layer.DrvMathAux
