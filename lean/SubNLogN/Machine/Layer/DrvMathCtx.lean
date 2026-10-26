/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvMathAux

/-!
# Layer driver math: context facts (`Machine/Layer/DrvMathCtx.lean`)

Proves `DrvCtxStmt p βn βd` (`Machine/Layer/DriverSpec.lean`) for admissible constants `p`
(`p.OK`) and every leaf exponent `βn/βd` (`drvCtx_holds`). No `sorry`.

Proof outline.
* **Bands of the piece calls** (`ctx_bands`): the root bands are the layer's; `Δ = P`; the stage
  prefix `A·padR` is positive and divisible by `padR`, which is a multiple of `W_c^{k₀}` and hence
  of `W_c^k` (a piece of `m^k ≤ d` chunks has `k ≤ k₀ = ⌈log_m d⌉`); every piece fits
  (`j0 + m^k ≤ D - q₀`); and `lg M' ≤ lg 2M ≤ C_M P` since `M' ≤ 2M`.
* **Growth** (`DrvMathAux`, §6): a disk-grid input has growth `0`; phase 1 adds at most `q₀`
  (one per individual kernel); zero padding and address re-encodings add nothing; piece `i`
  (`C^{⊗m^k}`) adds at most `m^k ≤ cDepth k`. So the array before piece `i` has growth `drvB i`.
* **Guard**: `q₀ + Σ cDepth + D ≤ C_g d^6` (`DrvMathAux.guard_le_exists`, using `s_c < m^5`), and
  `C_g d^6 ≤ C_g (b_d P^ε)^6 ≤ P` above a cutoff because `6ε < 1` (from `14 ≤ C₁`, `εC₁ < 1`).
-/

namespace SubNLogN.Machine.Layer

open SubNLogN.Machine SubNLogN.Machine.Layer.DrvMathAux
open SubNLogN.Math.Networks (q0Of padR mH Wc k0Of cardRole_holds)
open Filter

/-- For `6ε < 1` there is a cutoff above which `C·(b_d P^ε)^6 ≤ P`. -/
theorem guard_cutoff_exists (Cg bd ε : ℝ) (hε6 : 6 * ε < 1) :
    ∃ P₁ : ℕ, ∀ P : ℕ, P₁ ≤ P → Cg * (bd * (P : ℝ) ^ ε) ^ 6 ≤ P := by
  have hκ : 0 < 1 - 6 * ε := by linarith
  have ht : Tendsto (fun P : ℕ => (P : ℝ) ^ (1 - 6 * ε)) atTop atTop :=
    (tendsto_rpow_atTop hκ).comp tendsto_natCast_atTop_atTop
  obtain ⟨P₁, hP₁⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop (Cg * bd ^ 6))
  refine ⟨max P₁ 1, fun P hP => ?_⟩
  have hP1 : 1 ≤ P := le_trans (le_max_right _ _) hP
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP1
  have h1 : Cg * bd ^ 6 ≤ (P : ℝ) ^ (1 - 6 * ε) := hP₁ P (le_trans (le_max_left _ _) hP)
  have h2 : (bd * (P : ℝ) ^ ε) ^ 6 = bd ^ 6 * (P : ℝ) ^ (6 * ε) := by
    rw [mul_pow, ← Real.rpow_natCast ((P : ℝ) ^ ε) 6, ← Real.rpow_mul hPpos.le]
    congr 2
    push_cast
    ring
  have h3 : (P : ℝ) ^ (1 - 6 * ε) * (P : ℝ) ^ (6 * ε) = P := by
    rw [← Real.rpow_add hPpos, show 1 - 6 * ε + 6 * ε = 1 by ring, Real.rpow_one]
  rw [h2]
  calc Cg * (bd ^ 6 * (P : ℝ) ^ (6 * ε)) = (Cg * bd ^ 6) * (P : ℝ) ^ (6 * ε) := by ring
    _ ≤ (P : ℝ) ^ (1 - 6 * ε) * (P : ℝ) ^ (6 * ε) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = P := h3

/-- The context hypotheses of a C-core piece call, in the row case. -/
theorem ctx_bands (p : LayerParams) (P₀c : ℕ) (t : LayerRT) (h : DrvRows t) (b : ℕ)
    (pc : ℕ × ℕ) (hpc : pc ∈ drvPieces t) (hP : P₀c ≤ t.P)
    (had' : p.a_d * (t.P : ℝ) ^ p.ε ≤ t.d) (hbd' : (t.d : ℝ) ≤ p.b_d * (t.P : ℝ) ^ p.ε)
    (har' : (2 : ℝ) ^ (p.a_r * t.P / t.d) ≤ t.r) (hbr' : (t.r : ℝ) ≤ (2 : ℝ) ^ (p.b_r * t.P / t.d))
    (hKc : t.K = ⌊(t.d : ℝ) ^ p.c⌋₊) (hDd : t.D ≤ t.d) (hA1 : 1 ≤ t.A) (hS1 : 1 ≤ t.S)
    (hρK : t.ρ < t.K) (hlogM : Real.logb 2 (2 * (t.M : ℝ)) ≤ p.C_M * t.P) :
    CCoreBands p P₀c (drvCtx t b pc) := by
  have hK : 1 ≤ t.K := by omega
  have hfit := piece_le_D h hpc
  have he : mH ^ pc.1 ≤ t.d := by
    have : t.D - q0Of t.d ≤ t.D := Nat.sub_le _ _
    omega
  have hk0 : pc.1 ≤ k0Of t.d := piece_depth_le_k0 he
  have hWc : Wc = tripleWc 100 := (cardRole_holds 100).2
  have hdvd0 : Wc ^ pc.1 ∣ padR t.d t.K := by
    have h2 : Wc ^ k0Of t.d ∣ padR t.d t.K := by
      unfold padR
      exact Nat.dvd_mul_right _ _
    exact (pow_dvd_pow Wc hk0).trans h2
  have hdvd : tripleWc 100 ^ pc.1 ∣ padR t.d t.K := by
    rw [← hWc]
    exact hdvd0
  have hM := ctxM_le t h hK b pc
  have hMpos : 0 < (drvCtx t b pc).M := by
    show 0 < t.A * padR t.d t.K * t.S * 2 ^ (t.K * (t.D - q0Of t.d))
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hA1 h.2) hS1) (pow_pos (by norm_num) _)
  have hlog' : Real.logb 2 ((drvCtx t b pc).M : ℝ) ≤ p.C_M * t.P := by
    refine le_trans ?_ hlogM
    apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hMpos)
    exact_mod_cast hM
  have hfit' : pc.2 + tripleM 100 ^ pc.1 ≤ t.D - q0Of t.d := by rw [← mH_eq]; exact hfit
  unfold CCoreBands
  exact ⟨hP, had', hbd', har', hbr', hKc, le_refl _, Nat.mul_pos hA1 h.2, hS1,
    (dvd_mul_left (padR t.d t.K) t.A : padR t.d t.K ∣ t.A * padR t.d t.K), hdvd, hfit', hρK,
    hlog'⟩

/-- **`DrvCtxStmt` holds** for admissible constants `p` and every leaf exponent `βn/βd`. -/
theorem drvCtx_holds (p : LayerParams) (hp : p.OK) (βn βd : ℕ) : DrvCtxStmt p βn βd := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hε0, -, -, -, -, -, -, hC14, hεC, -, -, -, -, -, -, -⟩ :=
    hp
  intro Estar P₀c
  have hε14 : 14 * p.ε < 1 := by
    have h14 : (14 : ℝ) ≤ p.C₁ := by exact_mod_cast hC14
    nlinarith
  have hε6 : 6 * p.ε < 1 := by linarith
  obtain ⟨Cg, hCg⟩ := guard_le_exists βn βd Estar
  obtain ⟨P₁, hP₁⟩ := guard_cutoff_exists (Cg : ℝ) p.b_d p.ε hε6
  refine ⟨max P₀c (max P₁ 1), ?_⟩
  intro t hρ z hb hz
  obtain ⟨hP0, had', hbd', har', hbr', hKc, hD1, hDd, hA1, hS1, hρK, hlogM, -, -, -⟩ := hb
  have hd : 1 ≤ t.d := by omega
  have hguard : q0Of t.d + ((drvPieces t).map fun pc => cDepth t.d βn βd Estar pc.1).sum + t.D ≤
      t.P := by
    have h1 := hCg t hDd hd
    have hP := hP₁ t.P (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hP0)
    have hd6 : (t.d : ℝ) ^ 6 ≤ (p.b_d * (t.P : ℝ) ^ p.ε) ^ 6 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hbd' 6
    have h2 : ((Cg * t.d ^ 6 : ℕ) : ℝ) ≤ t.P := by
      push_cast
      calc (Cg : ℝ) * (t.d : ℝ) ^ 6 ≤ (Cg : ℝ) * (p.b_d * (t.P : ℝ) ^ p.ε) ^ 6 :=
            mul_le_mul_of_nonneg_left hd6 (Nat.cast_nonneg _)
        _ ≤ t.P := hP
    have h3 : Cg * t.d ^ 6 ≤ t.P := by exact_mod_cast h2
    omega
  have hP₀c : P₀c ≤ t.P := le_trans (le_max_left _ _) hP0
  refine ⟨fun h => ⟨fun i hi => ⟨?_, ?_, ?_⟩, ?_⟩, fun h => ?_, ?_⟩
  · exact ctx_bands p P₀c t h _ _ (List.get_mem _ _) hP₀c had' hbd' har' hbr' hKc hDd hA1 hS1 hρK
      hlogM
  · exact drvYs_growth t hρ βn βd Estar _ (drvStageIn_growth t hρ h z hz) i
  · rw [drvB_succ t βn βd Estar i hi]
    have := drvB_le t βn βd Estar (i + 1)
    unfold drvDelta
    omega
  · exact drvYs_growth t hρ βn βd Estar _ (drvStageIn_growth t hρ h z hz) _
  · rw [drvB_zero]
    exact drvA1_growth t hρ z hz
  · rw [drvB_length]
    unfold drvDelta
    omega

end SubNLogN.Machine.Layer
