/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvParamsDefs
import SubNLogN.Machine.Layer.DrvMathAux

/-!
# Layer driver pre-phase: two band facts on `q₀` (`Machine/Layer/DrvPreBandsT1.lean`, T1)

* `q0Of_succ_le_P`: with `p.OK`, beyond a cutoff, every call in the bands has `q₀(d) + 1 ≤ P`.
  Here `q₀(d) + 1 ≤ C_q (⌊log₂ d⌋ + 1) ≤ C_q d` (`DrvMathAux.q0_succ_le_exists`), and
  `d ≤ b_d P^ε` with `ε < 1`; the cutoff is `max 1 ⌈(C_q b_d)^{1/(1-ε)}⌉₊`.
* `one_le_drvQ1`: with `p.OK`, every call in the bands with `P ≥ 1` has `min(q₀(d), D) ≥ 1`
  (`D ≥ 1`; `d ≥ a_d P^ε > 0`; `W_c ≥ 2` (`one_lt_Wc`) and `m ≥ 2`, so both `⌈·⌉`-logs are `≥ 1`).

**Scope (honest summary).** Pure arithmetic lemmas, all proved; no statement is assumed.
Helpers live in `SubNLogN.Machine.Layer.DrvBandsT1`.
-/

namespace SubNLogN.Machine.Layer.DrvBandsT1

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Layer
open SubNLogN.Math.Networks (q0Of Wc mH)

/-- The complex network has at least two role streams (`X` and `Y` roles differ). -/
theorem one_lt_Wc : 1 < Wc :=
  Fintype.one_lt_card_iff_nontrivial.mpr
    ⟨⟨SubNLogN.Math.Networks.Role.X
        (SubNLogN.Math.Networks.tri012, SubNLogN.Math.Networks.tri012,
          SubNLogN.Math.Networks.tri012),
      SubNLogN.Math.Networks.Role.Y
        (SubNLogN.Math.Networks.tri012, SubNLogN.Math.Networks.tri012,
          SubNLogN.Math.Networks.tri012),
      fun h => by cases h⟩⟩

/-- **(a)** With `p.OK`, beyond a cutoff, `q₀(d) + 1 ≤ P` for every call in the bands. -/
theorem q0Of_succ_le_P (p : LayerParams) (hp : p.OK) :
    ∃ P₀ : ℕ, ∀ t : LayerRT, LayerBands p P₀ t → q0Of t.d + 1 ≤ t.P := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hε0, hε1, _, _, _, _, _, _, _, had, hadb, _⟩ := hp
  obtain ⟨Cq, hCq⟩ := DrvMathAux.q0_succ_le_exists
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (Cq : ℝ) * p.b_d := ⟨_, rfl⟩
  have hbd : 0 < p.b_d := lt_of_lt_of_le had hadb
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hδ : 0 < 1 - p.ε := by linarith
  refine ⟨max 1 ⌈κ ^ (1 / (1 - p.ε))⌉₊, fun t ht => ?_⟩
  obtain ⟨hP₀, hd1, hd2, _⟩ := ht
  have hP1 : 1 ≤ t.P := le_trans (le_max_left _ _) hP₀
  have hP1' : (1 : ℝ) ≤ (t.P : ℝ) := by exact_mod_cast hP1
  have hPpos : (0 : ℝ) < (t.P : ℝ) := by linarith
  have hPε : 0 < (t.P : ℝ) ^ p.ε := Real.rpow_pos_of_pos hPpos _
  have hdpos : (0 : ℝ) < t.d := lt_of_lt_of_le (mul_pos had hPε) hd1
  have hd1' : 1 ≤ t.d := by
    have := Nat.cast_pos.mp hdpos
    omega
  have hq : q0Of t.d + 1 ≤ Cq * t.d :=
    (hCq t.d).trans (Nat.mul_le_mul_left _ (DrvMathAux.log2_succ_le_of_le le_rfl hd1'))
  have hPκ : κ ^ (1 / (1 - p.ε)) ≤ (t.P : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hP₀)
  have hκP : κ ≤ (t.P : ℝ) ^ (1 - p.ε) := by
    calc κ = (κ ^ (1 / (1 - p.ε))) ^ (1 - p.ε) := by
          rw [← Real.rpow_mul hκ0, one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
      _ ≤ (t.P : ℝ) ^ (1 - p.ε) := Real.rpow_le_rpow (Real.rpow_nonneg hκ0 _) hPκ hδ.le
  have hreal : ((q0Of t.d + 1 : ℕ) : ℝ) ≤ (t.P : ℝ) := by
    have h1 : ((q0Of t.d + 1 : ℕ) : ℝ) ≤ (Cq : ℝ) * (t.d : ℝ) := by exact_mod_cast hq
    have h2 : (Cq : ℝ) * (t.d : ℝ) ≤ (Cq : ℝ) * (p.b_d * (t.P : ℝ) ^ p.ε) :=
      mul_le_mul_of_nonneg_left hd2 (by positivity)
    have h3 : (Cq : ℝ) * (p.b_d * (t.P : ℝ) ^ p.ε) = κ * (t.P : ℝ) ^ p.ε := by
      rw [hκ]
      ring
    have h4 : κ * (t.P : ℝ) ^ p.ε ≤ (t.P : ℝ) ^ (1 - p.ε) * (t.P : ℝ) ^ p.ε :=
      mul_le_mul_of_nonneg_right hκP hPε.le
    have h5 : (t.P : ℝ) ^ (1 - p.ε) * (t.P : ℝ) ^ p.ε = (t.P : ℝ) := by
      rw [← Real.rpow_add hPpos, sub_add_cancel, Real.rpow_one]
    linarith
  exact_mod_cast hreal

/-- **(b)** With `p.OK`, every call in the bands with `P ≥ 1` has `drvQ1 t = min(q₀(d), D) ≥ 1`. -/
theorem one_le_drvQ1 (p : LayerParams) (hp : p.OK) (P₀ : ℕ) (t : LayerRT)
    (ht : LayerBands p P₀ t) (hP : 1 ≤ t.P) : 1 ≤ drvQ1 t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, had, _⟩ := hp
  obtain ⟨_, hd1, _, _, _, _, hD1, _⟩ := ht
  have hP1' : (1 : ℝ) ≤ (t.P : ℝ) := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < (t.P : ℝ) := by linarith
  have hPε : 0 < (t.P : ℝ) ^ p.ε := Real.rpow_pos_of_pos hPpos _
  have hdpos : (0 : ℝ) < t.d := lt_of_lt_of_le (mul_pos had hPε) hd1
  have hd : 1 ≤ t.d := by
    have := Nat.cast_pos.mp hdpos
    omega
  have hc1 : 0 < Nat.clog 2 Wc := Nat.clog_pos (by norm_num) one_lt_Wc
  have hc2 : 0 < Nat.clog mH (2 * t.d) := Nat.clog_pos DrvMathAux.two_le_mH (by omega)
  have hq : 1 ≤ q0Of t.d := Nat.mul_pos hc1 hc2
  exact le_min hq hD1

end SubNLogN.Machine.Layer.DrvBandsT1
