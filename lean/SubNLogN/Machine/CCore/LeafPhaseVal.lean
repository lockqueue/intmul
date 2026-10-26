/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs
import SubNLogN.Machine.Layer.DrvPreKDefs
import SubNLogN.Math.Networks.Proofs.LayerCoreFacts

/-!
# C-core phase leaf: value-level lemmas (`CCore/LeafPhaseVal.lean`)

**Scope (honest summary).** Pure lemmas, everything proved:
* `runSteps_recMap`, `runSteps_addrMap`: one T2 step on a compact array (`runSteps`,
  `CCore/SkelDefs.lean:120`) through the layout round trip `decodeEncodeAddr_holds`;
* `gridInt_Ipow`: on the grid, `gridInt` commutes with multiplication by `i^e` (`rotIPowC e`,
  `Machine/Layer/DrvPreKDefs.lean:28`);
* `fits_gridInt`: under a growth bound `b ≤ Δ` (`ArrGrowth`, `Contracts/CCore.lean:168`) the
  numerators at precision `P + Δ` fit the guarded width `w_g = P + 2Δ + 3` with margin.
-/

namespace SubNLogN.Machine.CCore.LeafScalarAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
open SubNLogN.Math.Networks SubNLogN.Machine.Layer.DrvPreK

/-! ## One step on a compact array -/

theorem runSteps_recMap {A K D S r : ℕ} (g : (Fin r → ℂ) → (Fin r → ℂ))
    (w : RArr (LayerAddr A K D S) r) :
    runSteps [Model.Step.recMap g] w = fun x => g (w x) := by
  funext x
  show g (w (decodeAddr (encodeAddr x))) = g (w x)
  rw [show decodeAddr (encodeAddr x) = x from decodeEncodeAddr_holds _ _ _ _ x]

theorem runSteps_addrMap {A K D S r : ℕ}
    (g : (layerLayout A K D S).Addr → (Fin r → ℂ) → (Fin r → ℂ))
    (w : RArr (LayerAddr A K D S) r) :
    runSteps [Model.Step.addrMap g] w = fun x => g (encodeAddr x) (w x) := by
  funext x
  show g (encodeAddr x) (w (decodeAddr (encodeAddr x))) = g (encodeAddr x) (w x)
  rw [show decodeAddr (encodeAddr x) = x from decodeEncodeAddr_holds _ _ _ _ x]

/-! ## Grid numerators -/

theorem gridUnit_mul_pow (F : ℕ) : gridUnit F * 2 ^ F = 1 := by
  unfold gridUnit
  have : (0 : ℝ) < 2 ^ F := by positivity
  field_simp

theorem gridInt_of_onGrid {F : ℕ} {z : ℂ} (h : OnGrid F z) :
    ∃ a b : ℤ, z.re = a * gridUnit F ∧ z.im = b * gridUnit F ∧ gridInt F z = (a, b) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  refine ⟨a, b, ha, hb, ?_⟩
  simp only [gridInt, ha, hb, mul_assoc, gridUnit_mul_pow, mul_one, round_intCast]

theorem I_pow_mod (e : ℕ) : Complex.I ^ e = Complex.I ^ (e % 4) := by
  conv_lhs => rw [← Nat.div_add_mod e 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

theorem rotIPowC_mod (e : ℕ) (c : CInt) : rotIPowC e c = rotIPowC (e % 4) c := by
  simp [rotIPowC, Nat.mod_mod]

/-- **`gridInt` commutes with `i^e`** on the grid. -/
theorem gridInt_Ipow {F : ℕ} {z : ℂ} (h : OnGrid F z) (e : ℕ) :
    gridInt F (Complex.I ^ e * z) = rotIPowC e (gridInt F z) := by
  obtain ⟨a, b, ha, hb, hg⟩ := gridInt_of_onGrid h
  rw [hg, I_pow_mod, rotIPowC_mod]
  have h4 : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have key : ∀ (u v : ℤ), gridInt F ⟨(u : ℝ) * gridUnit F, (v : ℝ) * gridUnit F⟩ = (u, v) := by
    intro u v
    simp only [gridInt, mul_assoc, gridUnit_mul_pow, mul_one, round_intCast]
  have hz : z = ⟨(a : ℝ) * gridUnit F, (b : ℝ) * gridUnit F⟩ := Complex.ext ha hb
  interval_cases (e % 4)
  · rw [pow_zero, one_mul, hz, key]; rfl
  · rw [pow_one, hz]
    have : Complex.I * (⟨(a : ℝ) * gridUnit F, (b : ℝ) * gridUnit F⟩ : ℂ) =
        ⟨((-b : ℤ) : ℝ) * gridUnit F, (a : ℝ) * gridUnit F⟩ := by
      apply Complex.ext <;> simp
    rw [this, key]; rfl
  · rw [hz]
    have : Complex.I ^ 2 * (⟨(a : ℝ) * gridUnit F, (b : ℝ) * gridUnit F⟩ : ℂ) =
        ⟨((-a : ℤ) : ℝ) * gridUnit F, ((-b : ℤ) : ℝ) * gridUnit F⟩ := by
      apply Complex.ext <;> simp [Complex.I_sq]
    rw [this, key]; rfl
  · rw [hz]
    have : Complex.I ^ 3 * (⟨(a : ℝ) * gridUnit F, (b : ℝ) * gridUnit F⟩ : ℂ) =
        ⟨(b : ℝ) * gridUnit F, ((-a : ℤ) : ℝ) * gridUnit F⟩ := by
      rw [pow_succ, Complex.I_sq]
      apply Complex.ext <;> simp
    rw [this, key]; rfl

/-- `encArr` of a pointwise `i^e` multiple is `mapC (rotIPowC e)` of `encArr`, on the grid. -/
theorem encArr_Ipow {α : Type} {r : ℕ} (F : ℕ) (addrs : List α) (z : α → Fin r → ℂ) (e : ℕ)
    (h : ∀ x k, OnGrid F (z x k)) :
    encArr F addrs (fun x => Complex.I ^ e • z x) = mapC (rotIPowC e) (encArr F addrs z) := by
  simp only [encArr, mapC, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply, List.map_map]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  exact gridInt_Ipow (h x k) e

/-! ## Fitting the guarded width -/

/-- Numerators of a growth-bounded value at precision `P + Δ` are at most `2^(P + 2Δ)`. -/
theorem abs_gridInt_le {P b Δ : ℕ} (hb : b ≤ Δ) {z : ℂ} (hg : OnGrid (P + b) z)
    (hn : ‖z‖ ≤ 2 ^ b) :
    |(gridInt (P + Δ) z).1| ≤ 2 ^ (P + 2 * Δ) ∧ |(gridInt (P + Δ) z).2| ≤ 2 ^ (P + 2 * Δ) := by
  have hg' : OnGrid (P + Δ) z := hg.mono (by omega)
  obtain ⟨a, c, ha, hc, hgi⟩ := gridInt_of_onGrid hg'
  rw [hgi]
  have hpos : (0 : ℝ) < 2 ^ (P + Δ) := by positivity
  have hu : gridUnit (P + Δ) = ((2 : ℝ) ^ (P + Δ))⁻¹ := rfl
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hpow : (2 : ℝ) ^ b * 2 ^ (P + Δ) ≤ 2 ^ (P + 2 * Δ) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have ka : (a : ℝ) = z.re * 2 ^ (P + Δ) := by
    rw [ha, hu, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
  have kc : (c : ℝ) = z.im * 2 ^ (P + Δ) := by
    rw [hc, hu, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
  constructor
  · have : |(a : ℝ)| ≤ 2 ^ (P + 2 * Δ) := by
      rw [ka, abs_mul, abs_of_pos hpos]
      calc |z.re| * 2 ^ (P + Δ) ≤ 2 ^ b * 2 ^ (P + Δ) :=
            mul_le_mul_of_nonneg_right (hre.trans hn) hpos.le
        _ ≤ _ := hpow
    exact_mod_cast this
  · have : |(c : ℝ)| ≤ 2 ^ (P + 2 * Δ) := by
      rw [kc, abs_mul, abs_of_pos hpos]
      calc |z.im| * 2 ^ (P + Δ) ≤ 2 ^ b * 2 ^ (P + Δ) :=
            mul_le_mul_of_nonneg_right (him.trans hn) hpos.le
        _ ≤ _ := hpow
    exact_mod_cast this

theorem fitsTwos_of_abs_le {P Δ : ℕ} {a : ℤ} (h : |a| ≤ 2 ^ (P + 2 * Δ)) :
    FitsTwos (P + 2 * Δ + 3) a := by
  have h2 : (2 : ℤ) ^ (P + 2 * Δ + 3 - 1) = 4 * 2 ^ (P + 2 * Δ) := by
    rw [show P + 2 * Δ + 3 - 1 = (P + 2 * Δ) + 2 by omega, pow_add]; ring
  have hp : (0 : ℤ) < 2 ^ (P + 2 * Δ) := by positivity
  rw [abs_le] at h
  unfold FitsTwos
  rw [h2]
  constructor <;> linarith [h.1, h.2]

end SubNLogN.Machine.CCore.LeafScalarAux
