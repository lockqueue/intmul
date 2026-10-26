import SubNLogN.Math.Networks.AppCLayerProc

/-!
# Guard corollaries for the layer procedure

With `Δ = ⌈C₀ d^{14}⌉` (`C₀ = guardC0 100`) as in `Prop71GuardStmt` (`AppCLayerProc.lean`):

* `guardDelta_width_le`: in the band `d ≤ b_d P^{1/15}`, eventually `2Δ + 3 ≤ P`; hence `Δ ≤ P` and the
  guarded component width `P + 2Δ + 3` is at most `2P`. (Elementary: `d^{14} ≤ b_d^{14}
  P^{14/15}`; the cutoff is the explicit `P₀ = (4 C₀ b_d^{14} + 2)^{15}`.)
* `onGuardGrid_encodeArr_of_disk`: the entry state is guarded: a disk-grid input (`2^{-P}` grid,
  modulus `≤ 1`) is on the `2^{-(P+Δ)}` grid with `|Re|, |Im| ≤ 1 < 2^{Δ+2}`, for every `Δ`.
* `prop71Guard_full`: from `Prop71GuardStmt` (a hypothesis here), the same conclusion with, inside the
  same `∃ P₀`, the two extra conjuncts `2Δ + 3 ≤ P` and `OnGuardGrid P Δ (encodeArr z)`.
-/

namespace SubNLogN.Math.Networks

open Model SubNLogN.Math.Walsh SubNLogN.Math.Common

namespace LayerGuardCorAux

/-- `(x^{1/15})^{15} = x` for `x ≥ 0`. -/
theorem rpow_inv15_pow (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 15)) ^ 15 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- `(y^{15})^{1/15} = y` for `y ≥ 0`. -/
theorem pow15_rpow_inv (y : ℝ) (hy : 0 ≤ y) : (y ^ 15) ^ ((1 : ℝ) / 15) = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

end LayerGuardCorAux

open LayerGuardCorAux

/-- **Width**: in the band `d ≤ b_d P^{1/15}`, eventually `2⌈C₀ d^{14}⌉ + 3 ≤ P`. -/
theorem guardDelta_width_le (aD bD : ℝ) (haD : 0 < aD) (hab : aD ≤ bD) :
    ∃ P₀ : ℝ, ∀ P d : ℕ, P₀ ≤ P → (d : ℝ) ≤ bD * (P : ℝ) ^ ((1 : ℝ) / 15) →
      2 * ⌈(guardC0 100 : ℝ) * (d : ℝ) ^ 14⌉₊ + 3 ≤ P := by
  set C : ℝ := (guardC0 100 : ℝ) with hCdef
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hb : 0 < bD := lt_of_lt_of_le haD hab
  have hCb : 0 ≤ C * bD ^ 14 := mul_nonneg hC (pow_nonneg hb.le 14)
  set M : ℝ := 4 * C * bD ^ 14 + 2 with hM
  have hM2 : 2 ≤ M := by rw [hM]; nlinarith
  have hM0 : 0 ≤ M := by linarith
  refine ⟨M ^ 15, fun P d hP hd => ?_⟩
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  set t : ℝ := (P : ℝ) ^ ((1 : ℝ) / 15) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hP0 _
  have htP : t ^ 15 = (P : ℝ) := rpow_inv15_pow _ hP0
  have hMt : M ≤ t := by
    calc M = (M ^ 15) ^ ((1 : ℝ) / 15) := (pow15_rpow_inv M hM0).symm
      _ ≤ (P : ℝ) ^ ((1 : ℝ) / 15) := Real.rpow_le_rpow (pow_nonneg hM0 15) hP (by norm_num)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdt : (d : ℝ) ^ 14 ≤ (bD * t) ^ 14 := pow_le_pow_left₀ hd0 hd 14
  have hceil : (⌈C * (d : ℝ) ^ 14⌉₊ : ℝ) < C * (d : ℝ) ^ 14 + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hC (pow_nonneg hd0 14))
  have hCd : C * (d : ℝ) ^ 14 ≤ C * bD ^ 14 * t ^ 14 := by
    calc C * (d : ℝ) ^ 14 ≤ C * (bD * t) ^ 14 := mul_le_mul_of_nonneg_left hdt hC
      _ = C * bD ^ 14 * t ^ 14 := by ring
  have ht2 : 2 ≤ t := le_trans hM2 hMt
  have ht14 : (5 : ℝ) / 2 ≤ t ^ 14 := by
    have h214 : (2 : ℝ) ^ 14 ≤ t ^ 14 := pow_le_pow_left₀ (by norm_num) ht2 14
    have : (5 : ℝ) / 2 ≤ (2 : ℝ) ^ 14 := by norm_num
    linarith
  have hX : 0 ≤ C * bD ^ 14 * t ^ 14 := mul_nonneg hCb (pow_nonneg ht0 14)
  have hmain : 2 * (C * bD ^ 14 * t ^ 14 + 1) + 3 ≤ t ^ 15 := by
    have h1 : M * t ^ 14 ≤ t * t ^ 14 := mul_le_mul_of_nonneg_right hMt (pow_nonneg ht0 14)
    have h2 : t ^ 15 = t * t ^ 14 := by ring
    have h3 : M * t ^ 14 = 4 * (C * bD ^ 14 * t ^ 14) + 2 * t ^ 14 := by rw [hM]; ring
    linarith
  have key : ((2 * ⌈C * (d : ℝ) ^ 14⌉₊ + 3 : ℕ) : ℝ) < (P : ℝ) := by
    push_cast
    calc 2 * (⌈C * (d : ℝ) ^ 14⌉₊ : ℝ) + 3 < 2 * (C * (d : ℝ) ^ 14 + 1) + 3 := by linarith
      _ ≤ 2 * (C * bD ^ 14 * t ^ 14 + 1) + 3 := by linarith
      _ ≤ t ^ 15 := hmain
      _ = P := htP
  exact_mod_cast key.le

/-- **Entry state**: a disk-grid input is on the guard grid, for every `Δ`. -/
theorem onGuardGrid_encodeArr_of_disk {A K D S rr : ℕ} (P Δ : ℕ) (z : RArr (LayerAddr A K D S) rr)
    (hz : ArrOnDiskGrid P z) : OnGuardGrid P Δ (encodeArr z) := by
  intro y k
  obtain ⟨hg, hn⟩ := hz (decodeAddr y) k
  have h1 : (1 : ℝ) < 2 ^ (Δ + 2) := one_lt_pow₀ (by norm_num) (by omega)
  exact ⟨hg.mono (Nat.le_add_right P Δ),
    lt_of_le_of_lt ((Complex.abs_re_le_norm _).trans hn) h1,
    lt_of_le_of_lt ((Complex.abs_im_le_norm _).trans hn) h1⟩

/-- **Guard, full form**: `Prop71GuardStmt` together with, inside the same `∃ P₀`, the width bound
`2Δ + 3 ≤ P` (so `Δ ≤ P` and `P + 2Δ + 3 ≤ 2P`) and the guarded entry state. -/
theorem prop71Guard_full (hG : Prop71GuardStmt) :
    ComplexNetCert → GuardGrowthStmt → GuardSmallStmt →
    ∀ (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData),
      (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) →
    ∀ (aD bD : ℝ), 0 < aD → aD ≤ bD → ∃ P₀ : ℝ, ∀ (P d rr K D A S : ℕ) (ρ : Fin K)
      (z : RArr (LayerAddr A K D S) rr),
      P₀ ≤ P → aD * (P : ℝ) ^ ((1 : ℝ) / 15) ≤ d → (d : ℝ) ≤ bD * (P : ℝ) ^ ((1 : ℝ) / 15) →
      K = ⌊(d : ℝ) ^ c46⌋₊ → 1 ≤ D → D ≤ d → ArrOnDiskGrid P z →
        LayerGuarded P A K D S rr ρ.val d ⌈(guardC0 100 : ℝ) * (d : ℝ) ^ 14⌉₊ cdat z ∧
        2 * ⌈(guardC0 100 : ℝ) * (d : ℝ) ^ 14⌉₊ + 3 ≤ P ∧
        OnGuardGrid P ⌈(guardC0 100 : ℝ) * (d : ℝ) ^ 14⌉₊ (encodeArr z) := by
  intro hcert hgrow hsmall cdat hval aD bD haD hab
  obtain ⟨P₁, h₁⟩ := hG hcert hgrow hsmall cdat hval aD bD haD hab
  obtain ⟨P₂, h₂⟩ := guardDelta_width_le aD bD haD hab
  refine ⟨max P₁ P₂, fun P d rr K D A S ρ z hP hlo hhi hK hD1 hDd hz => ⟨?_, ?_, ?_⟩⟩
  · exact h₁ P d rr K D A S ρ z (le_trans (le_max_left _ _) hP) hlo hhi hK hD1 hDd hz
  · exact h₂ P d (le_trans (le_max_right _ _) hP) hhi
  · exact onGuardGrid_encodeArr_of_disk P _ z hz

end SubNLogN.Math.Networks
