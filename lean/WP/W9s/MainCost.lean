import WP.W9s.RecSpec

/-!
# WP.W9s.MainCost — the whole kernel's cost is `O(synBound)`

`synCostB` is the host cost of `synProg` (header, conversions, the recursion, cleanup).
`synCostB_le`: it is at most `CM · synBound w h`, `CM = KS + 500`.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- The kernel's constant. -/
def CM (CA CS CH : ℕ) : ℕ := KS CA CS CH + 500

/-- Host cost of the whole kernel. -/
def synCostB (CA CS CH w : ℕ) (h : PreHdr) : ℕ :=
  40 * (h.hdrLen + h.r + 1) + (40 * (h.t1 * (h.r * (eb w + 1) + 1) + h.r + 1) +
    (costF CA CS CH w h.r h.mt1 + 2 + (40 * (h.t1 * (h.r * (eb w + 1) + 1) + 1) +
    (3 * (2 * h.r / h.t1) + 3 + (3 * h.r + 3)))))

theorem t1_MF_le (CA CS CH w t1 r : ℕ) (hr : 1 ≤ r) :
    t1 * MF CA CS CH w r ≤ (KS CA CS CH + 130) * (t1 * r * eb w) + 101 * t1 := by
  have hE : 4 ≤ eb w := by unfold eb; omega
  have e1 : t1 * MF CA CS CH w r = 30 * (t1 * r * eb w) + 60 * (t1 * r) + 30 * t1 +
      (t1 * r * (KS CA CS CH * (w + 1))) + 12 * (t1 * r * w) + 44 * (t1 * r) + 36 * t1 +
      33 * (t1 * r) + 71 * t1 := by
    unfold MF rowCostB eb
    ring
  have k1 : t1 * r * (KS CA CS CH * (w + 1)) ≤ KS CA CS CH * (t1 * r * eb w) := by
    have : t1 * r * (KS CA CS CH * (w + 1)) = KS CA CS CH * (t1 * r * (w + 1)) := by ring
    rw [this]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by unfold eb; omega))
  have k2 : 12 * (t1 * r * w) ≤ 6 * (t1 * r * eb w) := by
    have : 6 * (t1 * r * eb w) = 12 * (t1 * r * w) + 24 * (t1 * r) := by unfold eb; ring
    omega
  have k3 : t1 * r * 4 ≤ t1 * r * eb w := Nat.mul_le_mul_left _ hE
  have k4 : t1 ≤ t1 * r := Nat.le_mul_of_pos_right _ hr
  have e2 : (KS CA CS CH + 130) * (t1 * r * eb w) =
      KS CA CS CH * (t1 * r * eb w) + 130 * (t1 * r * eb w) := by ring
  omega

theorem synCostB_le (CA CS CH w : ℕ) (h : PreHdr) (hD : PreDims h) :
    synCostB CA CS CH w h ≤ CM CA CS CH * synBound w h := by
  obtain ⟨ht1, hr1, -, -⟩ := hD
  have ht : 1 ≤ h.t1 := by rw [ht1]; exact Nat.one_le_two_pow
  have hr : 1 ≤ h.r := by rw [hr1]; exact Nat.one_le_two_pow
  have hE : 4 ≤ eb w := by unfold eb; omega
  have hN : h.N = h.t1 * h.r := rfl
  have hdiv : 2 * h.r / h.t1 ≤ 2 * h.r := Nat.div_le_self _ _
  have hcF : costF CA CS CH w h.r h.mt1 = (h.mt1 + 1) * (h.t1 * MF CA CS CH w h.r) := by
    unfold costF
    rw [← ht1]
    ring
  have f1 := t1_MF_le CA CS CH w h.t1 h.r hr
  set P := h.t1 * h.r * eb w with hP
  have q1 : h.t1 ≤ h.t1 * h.r := Nat.le_mul_of_pos_right _ hr
  have q2 : h.r ≤ h.t1 * h.r := Nat.le_mul_of_pos_left _ ht
  have q3 : h.t1 * h.r * 4 ≤ P := Nat.mul_le_mul_left _ hE
  have f2 : h.t1 * MF CA CS CH w h.r ≤ (KS CA CS CH + 130) * P + 101 * h.t1 := f1
  have f3 : h.t1 * MF CA CS CH w h.r ≤ (KS CA CS CH + 130) * (P + 1) + 101 * (P + 1) := by
    have : (KS CA CS CH + 130) * P ≤ (KS CA CS CH + 130) * (P + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have f4 : (h.mt1 + 1) * (h.t1 * MF CA CS CH w h.r) ≤
      (KS CA CS CH + 231) * ((h.mt1 + 1) * (P + 1)) := by
    calc (h.mt1 + 1) * (h.t1 * MF CA CS CH w h.r)
        ≤ (h.mt1 + 1) * ((KS CA CS CH + 130) * (P + 1) + 101 * (P + 1)) :=
          Nat.mul_le_mul_left _ f3
      _ = (KS CA CS CH + 231) * ((h.mt1 + 1) * (P + 1)) := by ring
  have hS : synBound w h = (h.mt1 + 1) * (P + 1) + h.hdrLen := by
    unfold synBound
    rw [hN, hP]
  have g1 : h.t1 * (h.r * (eb w + 1) + 1) ≤ 2 * P := by
    have : h.t1 * (h.r * (eb w + 1) + 1) = P + h.t1 * h.r + h.t1 := by rw [hP]; ring
    omega
  have g2 : P + 1 ≤ (h.mt1 + 1) * (P + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have e3 : CM CA CS CH * synBound w h = (KS CA CS CH + 231) * ((h.mt1 + 1) * (P + 1)) +
      269 * ((h.mt1 + 1) * (P + 1)) + (KS CA CS CH + 500) * h.hdrLen := by
    rw [hS]
    unfold CM
    ring
  have g3 : 40 * h.hdrLen ≤ (KS CA CS CH + 500) * h.hdrLen := Nat.mul_le_mul_right _ (by omega)
  unfold synCostB
  rw [hcF]
  omega

#assert_std_axioms t1_MF_le synCostB_le

end WP.W9s
