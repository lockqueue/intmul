import WP.W9gx.CostFFT
import WP.W9g.Top

/-!
# WP.W9gx.CostLeaf — W9g's `leafCost` is `O(leafNodeBound)`

`leafCost_le`: `leafCost CM CA CS CL CR Mul w p_in p K ≤ 1500·(k+30)·leafNodeBound Mul w p_in p K`
with `k = CM + CA + CS + CL + CR + 1`. The FFT phase is `fft_part_le`; the F4 rescale pass is
`2^K` rescales of `|p − q| = p + K + 8`; the setup and cleanup are linear in the header bit lengths,
each bounded by the entry factor `G = 2·eb w + p_in + 2p + K + 8 ≤ 2^K·G ≤ leafNodeBound`.
-/

namespace WP.W9gx

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W9g

theorem natAbs_sub_le' (a b : ℕ) : ((a : ℤ) - b).natAbs ≤ a + b := by omega

theorem natAbs_sub_eq (a b : ℕ) (h : a ≤ b) : ((a : ℤ) - b).natAbs = b - a := by omega

/-- **The leaf kernel's cost.** -/
theorem leafCost_le (CM CA CS CL CR : ℕ) (Mul : ℕ → ℕ) (w pin p K : ℕ) :
    leafCost CM CA CS CL CR Mul w pin p K ≤
      1500 * (CM + CA + CS + CL + CR + 1 + 30) * leafNodeBound Mul w pin p K := by
  have hfft := fft_part_le CM CA CS CL CR Mul w pin p K
    (((2 * p + K + 8 : ℕ) : ℤ) - pin).natAbs (by have := natAbs_sub_le' (2 * p + K + 8) pin; omega)
  obtain ⟨k, hk⟩ : ∃ k, k = CM + CA + CS + CL + CR + 1 := ⟨_, rfl⟩
  rw [← hk] at hfft ⊢
  have hd2 := natAbs_sub_eq p (2 * p + K + 8) (by omega)
  have hres := rescCost_le (CL := CL) (CA := CA) (CR := CR) (k := k) (by omega) (by omega)
    (by omega) w (((p : ℤ) - ((2 * p + K + 8 : ℕ) : ℤ))).natAbs
  have heb : 4 ≤ eb w := by unfold eb; omega
  have hebw : w ≤ eb w := by unfold eb; omega
  obtain ⟨G, hG⟩ : ∃ G, G = 2 * eb w + pin + 2 * p + K + 8 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = leafNodeBound Mul w pin p K := ⟨_, rfl⟩
  have hT2 : 2 ^ K * G ≤ L := by rw [hL, hG]; unfold leafNodeBound; omega
  have hGT : G ≤ 2 ^ K * G := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos K)
  rw [← hL] at hfft ⊢
  have e1 : 1100 * (k + 30) * L = 1100 * ((k + 30) * L) := by ring
  have e2 : 1500 * (k + 30) * L = 1500 * ((k + 30) * L) := by ring
  rw [e1] at hfft
  rw [e2]
  have hQ30 : 30 * L ≤ (k + 30) * L := Nat.mul_le_mul_right _ (by omega)
  have hP : (k + 30) * (2 ^ K * G) ≤ (k + 30) * L := Nat.mul_le_mul_left _ hT2
  have hkG : k * G ≤ (k + 30) * L :=
    (Nat.mul_le_mul_right _ (by omega : k ≤ k + 30)).trans (Nat.mul_le_mul_left _ (hGT.trans hT2))
  have hkk : k ≤ k * G := Nat.le_mul_of_pos_right _ (by omega)
  -- the F4 rescale pass
  have h11 : 2 ^ K * (rescCost CL CA CR w (((p : ℤ) - ((2 * p + K + 8 : ℕ) : ℤ))).natAbs +
      14 * eb w + 8) ≤ 233 * ((k + 30) * (2 ^ K * G)) := by
    have hin : rescCost CL CA CR w (((p : ℤ) - ((2 * p + K + 8 : ℕ) : ℤ))).natAbs + 14 * eb w + 8 ≤
        233 * (k + 30) * G := by
      have h1 : 230 * (k + 30) * (w + (((p : ℤ) - ((2 * p + K + 8 : ℕ) : ℤ))).natAbs + 1) ≤
          230 * (k + 30) * G := Nat.mul_le_mul_left _ (by rw [hd2, hG]; omega)
      have e : 233 * (k + 30) * G = 230 * (k + 30) * G + 3 * (k * G) + 90 * G := by ring
      omega
    calc 2 ^ K * (rescCost CL CA CR w (((p : ℤ) - ((2 * p + K + 8 : ℕ) : ℤ))).natAbs +
          14 * eb w + 8) ≤ 2 ^ K * (233 * (k + 30) * G) := Nat.mul_le_mul_left _ hin
      _ = 233 * ((k + 30) * (2 ^ K * G)) := by ring
  -- the `$D` pass
  have h7 : 2 ^ K * (12 * eb w + 10) ≤ 13 * (2 ^ K * G) :=
    calc 2 ^ K * (12 * eb w + 10) ≤ 2 ^ K * (13 * G) := Nat.mul_le_mul_left _ (by rw [hG]; omega)
      _ = 13 * (2 ^ K * G) := by ring
  -- the counters
  have hCS : CS ≤ k := by omega
  have h6 : CS * (bitLen (2 * p + K + 8) + bitLen pin + 1) ≤ 2 * (k * G) + k := by
    have hb1 := bitLen_le_self (2 * p + K + 8)
    have hb2 := bitLen_le_self pin
    calc CS * (bitLen (2 * p + K + 8) + bitLen pin + 1) ≤ k * (2 * G + 1) :=
          Nat.mul_le_mul hCS (by rw [hG]; omega)
      _ = 2 * (k * G) + k := by ring
  have h10 : CS * (bitLen p + bitLen (2 * p + K + 8) + 1) ≤ 2 * (k * G) + k := by
    have hb1 := bitLen_le_self (2 * p + K + 8)
    have hb2 := bitLen_le_self p
    calc CS * (bitLen p + bitLen (2 * p + K + 8) + 1) ≤ k * (2 * G + 1) :=
          Nat.mul_le_mul hCS (by rw [hG]; omega)
      _ = 2 * (k * G) + k := by ring
  -- bit lengths
  have b1 := bitLen_le_self p
  have b2 := bitLen_le_self K
  have b3 := bitLen_le_self (2 * p + K + 8)
  have b4 := bitLen_le_self pin
  have b5 := bitLen_le_self (2 * p + K + 8 + 1)
  have b6 := bitLen_le_self (2 * p + K + 8 + 1 + 1)
  have b7 := bitLen_le_self (((2 * p + K + 8 : ℕ) : ℤ) - pin).natAbs
  have b8 := bitLen_le_self (((p : ℤ) - ((2 * p + K + 8 : ℕ) : ℤ))).natAbs
  have b9 := natAbs_sub_le' (2 * p + K + 8) pin
  unfold leafCost leafCostQ
  omega

#assert_std_axioms natAbs_sub_le' natAbs_sub_eq leafCost_le

end WP.W9gx
