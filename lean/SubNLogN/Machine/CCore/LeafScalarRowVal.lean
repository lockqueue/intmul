/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafScalarDefs
import SubNLogN.Machine.CCore.LeafPhaseVal

/-!
# C-core scalar row: value facts for the machine (`CCore/LeafScalarRowVal.lean`)

Value-level lemmas used by the scalar-row machine (`LeafScalarRow*.lean`), bridging stored
integer arrays and complex grid values. Everything is proved.

* `gridInt_accC`, `onGrid_acc`: one accumulation step `a + c·b` (`c ∈ {±1, ±1/2}`) on stored
  numerators is `accC c`, when `a` is on the `F`-grid and `b` on a coarser grid `G + 1 ≤ F` (so
  the halving of `b`'s numerator is exact).
* `zipC_accC_encArr`: the same on stored record arrays (`encArr`, any address order).
* `cAligned_encArr`: two stored arrays in the same address order are aligned.
* `cArrFits_encArr`: a growth-bounded array (`ArrGrowth P b`, `b ≤ Δ`) stored at precision `P + Δ`
  fits the guarded width `P + 2Δ + 3`.
* `gateVal_terms`: the term form (V1 of `ScalarRowValStmt`) read pointwise on role streams.

Helpers: `coefR` (real value of a coefficient), `coef_val_eq`, `coef_int_real`, `zipWith_map_map`,
`list_sum_apply`.
-/

namespace SubNLogN.Machine.CCore.LeafScalarRowVal

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Networks
open SubNLogN.Machine.CCore.LeafScalarAux SubNLogN.Math.Walsh

/-! ## Helpers -/

/-- The real value of a coefficient. -/
noncomputable def coefR : Coef → ℝ
  | .pos => 1
  | .neg => -1
  | .halfPos => 2⁻¹
  | .halfNeg => -2⁻¹

theorem coef_val_eq (c : Coef) : c.val = (coefR c : ℂ) := by
  cases c <;> simp [Coef.val, coefR]

/-- The coefficient acting on an even numerator `2m`, as a real identity. -/
theorem coef_int_real (c : Coef) (x m : ℤ) :
    (x : ℝ) + coefR c * ((2 * m : ℤ) : ℝ) = ((x + coefInt c (2 * m) : ℤ) : ℝ) := by
  have h2 : (2 * m) / 2 = m := by omega
  cases c <;> simp only [coefR, coefInt, h2] <;> push_cast <;> ring

theorem zipWith_map_map {β γ δ ε : Type} (f : γ → δ → ε) (g : β → γ) (h : β → δ) :
    ∀ l : List β, List.zipWith f (l.map g) (l.map h) = l.map (fun a => f (g a) (h a))
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.zipWith_cons_cons, zipWith_map_map f g h l]

theorem list_sum_apply {β M : Type} [AddCommMonoid M] (l : List (β → M)) (b : β) :
    l.sum b = (l.map (fun f => f b)).sum := by
  induction l with
  | nil => rfl
  | cons f l ih => simp only [List.sum_cons, Pi.add_apply, ih, List.map_cons]

/-! ## One accumulation step -/

theorem gridInt_accC (c : Coef) {F G : ℕ} {a b : ℂ} (ha : OnGrid F a) (hb : OnGrid G b)
    (hGF : G + 1 ≤ F) : gridInt F (a + c.val * b) = accC c (gridInt F a) (gridInt F b) := by
  obtain ⟨k, rfl⟩ : ∃ k, F = G + 1 + k := ⟨F - (G + 1), by omega⟩
  obtain ⟨a1, a2, ha1, ha2, hga⟩ := gridInt_of_onGrid ha
  obtain ⟨b1, b2, hb1, hb2, -⟩ := gridInt_of_onGrid hb
  have hpa : ∀ x : ℤ, (x : ℝ) * gridUnit (G + 1 + k) * 2 ^ (G + 1 + k) = x := fun x => by
    rw [mul_assoc, gridUnit_mul_pow, mul_one]
  have hpb : ∀ x : ℤ, (x : ℝ) * gridUnit G * 2 ^ (G + 1 + k) = ((2 * (x * 2 ^ k) : ℤ) : ℝ) :=
    fun x => by
      have hu := gridUnit_mul_pow G
      have h : (x : ℝ) * gridUnit G * 2 ^ (G + 1 + k) = 2 * ((x : ℝ) * 2 ^ k) := by
        calc (x : ℝ) * gridUnit G * 2 ^ (G + 1 + k) = x * (gridUnit G * 2 ^ G) * 2 * 2 ^ k := by
              ring
          _ = 2 * ((x : ℝ) * 2 ^ k) := by rw [hu]; ring
      exact_mod_cast h
  have key : ∀ x y : ℤ, ((x : ℝ) * gridUnit (G + 1 + k) + coefR c * ((y : ℝ) * gridUnit G)) *
      2 ^ (G + 1 + k) = ((x + coefInt c (2 * (y * 2 ^ k)) : ℤ) : ℝ) := fun x y => by
    rw [← coef_int_real c x (y * 2 ^ k), ← hpb y]
    calc ((x : ℝ) * gridUnit (G + 1 + k) + coefR c * ((y : ℝ) * gridUnit G)) * 2 ^ (G + 1 + k)
        = (x : ℝ) * gridUnit (G + 1 + k) * 2 ^ (G + 1 + k) +
          coefR c * ((y : ℝ) * gridUnit G * 2 ^ (G + 1 + k)) := by ring
      _ = x + coefR c * ((y : ℝ) * gridUnit G * 2 ^ (G + 1 + k)) := by rw [hpa]
  have hgb : gridInt (G + 1 + k) b = (2 * (b1 * 2 ^ k), 2 * (b2 * 2 ^ k)) := by
    simp only [gridInt, hb1, hb2, hpb, round_intCast]
  rw [hga, hgb, coef_val_eq]
  have e1 : (a + (coefR c : ℂ) * b).re * 2 ^ (G + 1 + k) =
      ((a1 + coefInt c (2 * (b1 * 2 ^ k)) : ℤ) : ℝ) := by
    rw [Complex.add_re, Complex.re_ofReal_mul, ha1, hb1]
    exact key a1 b1
  have e2 : (a + (coefR c : ℂ) * b).im * 2 ^ (G + 1 + k) =
      ((a2 + coefInt c (2 * (b2 * 2 ^ k)) : ℤ) : ℝ) := by
    rw [Complex.add_im, Complex.im_ofReal_mul, ha2, hb2]
    exact key a2 b2
  simp only [gridInt, e1, e2, round_intCast, accC]

theorem onGrid_acc (c : Coef) {F G : ℕ} {a b : ℂ} (ha : OnGrid F a) (hb : OnGrid G b)
    (hGF : G + 1 ≤ F) : OnGrid F (a + c.val * b) := by
  have hb' : OnGrid F b := hb.mono (by omega)
  have hh : OnGrid F (b / 2) := hb.half.mono hGF
  cases c
  · rw [show a + Coef.pos.val * b = a + b by simp only [Coef.val]; ring]
    exact ha.add hb'
  · rw [show a + Coef.neg.val * b = a + -b by simp only [Coef.val]; ring]
    exact ha.add hb'.neg
  · rw [show a + Coef.halfPos.val * b = a + b / 2 by simp only [Coef.val]; ring]
    exact ha.add hh
  · rw [show a + Coef.halfNeg.val * b = a + -(b / 2) by simp only [Coef.val]; ring]
    exact ha.add hh.neg

/-! ## Stored arrays -/

theorem zipC_accC_encArr {α : Type} {r F G : ℕ} (c : Coef) (addrs : List α)
    (z0 z : α → Fin r → ℂ) (h0 : ∀ x k, OnGrid F (z0 x k)) (hz : ∀ x k, OnGrid G (z x k))
    (hGF : G + 1 ≤ F) :
    zipC (accC c) (encArr F addrs z0) (encArr F addrs z) =
      encArr F addrs (fun x k => z0 x k + c.val * z x k) := by
  unfold zipC encArr
  rw [zipWith_map_map]
  apply List.map_congr_left
  intro x _
  dsimp only
  rw [zipWith_map_map]
  apply List.map_congr_left
  intro k _
  exact (gridInt_accC c (h0 x k) (hz x k) hGF).symm

theorem cAligned_encArr {α : Type} {r F : ℕ} (addrs : List α) (z1 z2 : α → Fin r → ℂ) :
    CAligned (encArr F addrs z1) (encArr F addrs z2) := by
  unfold CAligned encArr
  induction addrs with
  | nil => exact List.Forall₂.nil
  | cons x l ih => exact List.Forall₂.cons (by simp) ih

theorem cArrFits_encArr {α : Type} {r P b Δ : ℕ} (addrs : List α) (z : α → Fin r → ℂ)
    (hz : ArrGrowth P b z) (hb : b ≤ Δ) : CArrFits (P + 2 * Δ + 3) (encArr (P + Δ) addrs z) := by
  intro cs hcs c hc
  simp only [encArr, List.mem_map] at hcs
  obtain ⟨x, -, rfl⟩ := hcs
  simp only [List.mem_map] at hc
  obtain ⟨k, -, rfl⟩ := hc
  obtain ⟨h1, h2⟩ := abs_gridInt_le hb (hz x k).1 (hz x k).2
  exact ⟨fitsTwos_of_abs_le h1, fitsTwos_of_abs_le h2⟩

/-! ## The term form on role streams -/

theorem gateVal_terms (T : Fin Wn → List (Coef × Fin Wn)) {j : Stage} {ι : Fix 100}
    {r8 : Fin 8}
    (hV1 : ∀ (rr : ℕ) (vals : Fin Wn → Fin rr → ℂ) (idx : Fin Wn),
      gateFn j ι r8 vals idx = vals idx + ((T idx).map fun p => p.1.val • vals p.2).sum)
    {A K D S rr : ℕ} (w : Fin Wn → RArr (LayerAddr A K D S) rr) (u : Fin Wn)
    (x : LayerAddr A K D S) (k : Fin rr) :
    gateVal j ι r8 w u x k = w u x k + ((T u).map fun p => p.1.val * w p.2 x k).sum := by
  show gateFn j ι r8 (fun u' => w u' x) u k = _
  rw [hV1, Pi.add_apply, list_sum_apply, List.map_map]
  simp only [Function.comp_def, Pi.smul_apply, smul_eq_mul]

#assert_std_axioms gridInt_accC onGrid_acc zipC_accC_encArr cAligned_encArr cArrFits_encArr
  gateVal_terms

end SubNLogN.Machine.CCore.LeafScalarRowVal
