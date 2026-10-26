import WP.W9g.FFTDefs
import Contracts.W9.Leaf
import Mathlib.Tactic.Ring

/-!
# WP.W9gx.CostFFT — W9g's per-phase costs against `leafNodeBound`

With `k = CM + CA + CS + CL + CR + 1`, `q = 2p + K + 8`, the cell factor
`F = 4·Mul w + 2·eb w + 2p + K + 10` and the entry factor `G = 2·eb w + p_in + 2p + K + 8`
(the two per-entry factors of `leafNodeBound`):
* `drCost_le`, `rescCost_le`, `fftA_le` (`≤ 233(k+30)·G` for a rescale amount `d ≤ p_in + q`),
  `fftB_le` (`≤ 841(k+30)·F`), `fftO_le` (`≤ 14(K+1)·F`);
* `fft_part_le`: the FFT phase `fftCost … K + 2 ≤ 1100(k+30)·leafNodeBound`.
-/

namespace WP.W9gx

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W9g

section Bounds

variable {CM CA CS CL CR k : ℕ}

theorem drCost_le (hL : CL ≤ k) (hA : CA ≤ k) (hR : CR ≤ k) (L s : ℕ) :
    drCost CL CA CR L s ≤ (k + 30) * (5 * (L + s) + 100) := by
  unfold drCost
  have h1 : CL * (2 * s) ≤ k * (2 * s) := Nat.mul_le_mul_right _ hL
  have h2 : CA * (L + s + 1) ≤ k * (L + s + 1) := Nat.mul_le_mul_right _ hA
  have h3 : CR * (L + 2 * s + 2) ≤ k * (L + 2 * s + 2) := Nat.mul_le_mul_right _ hR
  have e : (k + 30) * (5 * (L + s) + 100) =
      5 * (k * L) + 5 * (k * s) + 100 * k + 150 * L + 150 * s + 3000 := by ring
  have e2 : k * (2 * s) = 2 * (k * s) := by ring
  have e3 : k * (L + s + 1) = k * L + k * s + k := by ring
  have e4 : k * (L + 2 * s + 2) = k * L + 2 * (k * s) + 2 * k := by ring
  omega

theorem rescCost_le (hL : CL ≤ k) (hA : CA ≤ k) (hR : CR ≤ k) (w d : ℕ) :
    rescCost CL CA CR w d ≤ 230 * (k + 30) * (w + d + 1) := by
  unfold rescCost coordCost
  have h0 := drCost_le hL hA hR w d
  have h1 : CL * (2 * d + 1) ≤ k * (2 * d + 1) := Nat.mul_le_mul_right _ hL
  have e : 230 * (k + 30) * (w + d + 1) =
      230 * (k * w) + 230 * (k * d) + 230 * k + 6900 * w + 6900 * d + 6900 := by ring
  have e1 : (k + 30) * (5 * (w + d) + 100) =
      5 * (k * w) + 5 * (k * d) + 100 * k + 150 * w + 150 * d + 3000 := by ring
  have e2 : k * (2 * d + 1) = 2 * (k * d) + k := by ring
  omega

theorem fftA_le (hL : CL ≤ k) (hA : CA ≤ k) (hR : CR ≤ k) (w d : ℕ) :
    fftA CL CA CR w d ≤ 233 * (k + 30) * (w + d + 1) := by
  unfold fftA eb
  have h0 := rescCost_le hL hA hR w d
  have e : 233 * (k + 30) * (w + d + 1) = 230 * (k + 30) * (w + d + 1) + 3 * (k + 30) * (w + d + 1) :=
    by ring
  have e2 : 3 * (k + 30) * (w + d + 1) = 3 * (k * (w + d + 1)) + 90 * w + 90 * d + 90 := by ring
  omega

theorem fftB_le (hM : CM ≤ k) (hA : CA ≤ k) (hS : CS ≤ k) (hL : CL ≤ k) (hR : CR ≤ k)
    (Mul : ℕ → ℕ) (w p K : ℕ) :
    fftB (cellCost CM CA CS CL CR Mul w (2 * p + K + 8)) w ≤
      841 * (k + 30) * (4 * Mul w + 2 * eb w + 2 * p + K + 10) := by
  unfold fftB cellCost bflyCost blkCost eb
  have hd := drCost_le hL hA hR (2 * w + (2 * p + K + 8) + 10) (2 * p + K + 8 + 2)
  have h1 : CM * Mul w ≤ k * Mul w := Nat.mul_le_mul_right _ hM
  have h2 : (CA + CS) * (4 * w + 1) ≤ (2 * k) * (4 * w + 1) := Nat.mul_le_mul_right _ (by omega)
  have h3 : CA * (3 * w + (2 * p + K + 8) + 6) ≤ k * (3 * w + (2 * p + K + 8) + 6) :=
    Nat.mul_le_mul_right _ hA
  have e1 : (k + 30) * (5 * (2 * w + (2 * p + K + 8) + 10 + (2 * p + K + 8 + 2)) + 100) =
      10 * (k * w) + 20 * (k * p) + 10 * (k * K) + 240 * k + 300 * w + 600 * p + 300 * K + 7200 := by
    ring
  have e2 : 841 * (k + 30) * (4 * Mul w + 2 * (2 * w + 4) + 2 * p + K + 10) =
      3364 * (k * Mul w) + 3364 * (k * w) + 1682 * (k * p) + 841 * (k * K) + 15138 * k +
        100920 * Mul w + 100920 * w + 50460 * p + 25230 * K + 454140 := by ring
  have e3 : (2 * k) * (4 * w + 1) = 8 * (k * w) + 2 * k := by ring
  have e4 : k * (3 * w + (2 * p + K + 8) + 6) = 3 * (k * w) + 2 * (k * p) + k * K + 14 * k := by ring
  omega

theorem fftO_le (K p : ℕ) : fftO K ≤ 14 * (K + 1) * (2 * p + K + 10) := by
  unfold fftO
  have hb : bitLen K ≤ K := bitLen_le_self K
  have h1 : K * (6 * bitLen K + 20) ≤ K * (6 * K + 20) := Nat.mul_le_mul_left _ (by omega)
  have e : 14 * (K + 1) * (2 * p + K + 10) = 28 * (K * p) + 14 * (K * K) + 154 * K + 28 * p + 140 :=
    by ring
  have e2 : K * (6 * K + 20) = 6 * (K * K) + 20 * K := by ring
  omega

end Bounds

/-- **The FFT phase** against `leafNodeBound`, for a rescale amount `d ≤ p_in + q`. -/
theorem fft_part_le (CM CA CS CL CR : ℕ) (Mul : ℕ → ℕ) (w pin p K d : ℕ)
    (hd : d ≤ pin + (2 * p + K + 8)) :
    fftCost (fftA CL CA CR w d) (fftO K) (fftB (cellCost CM CA CS CL CR Mul w (2 * p + K + 8)) w) K
        + 2 ≤ 1100 * (CM + CA + CS + CL + CR + 1 + 30) * leafNodeBound Mul w pin p K := by
  obtain ⟨k, hk⟩ : ∃ k, k = CM + CA + CS + CL + CR + 1 := ⟨_, rfl⟩
  rw [← hk]
  have hA := fftA_le (CL := CL) (CA := CA) (CR := CR) (k := k) (by omega) (by omega) (by omega) w d
  have hB := fftB_le (CM := CM) (CA := CA) (CS := CS) (CL := CL) (CR := CR) (k := k) (by omega)
    (by omega) (by omega) (by omega) (by omega) Mul w p K
  have hO := fftO_le K p
  have hf := fftCost_le (fftA CL CA CR w d) (fftO K)
    (fftB (cellCost CM CA CS CL CR Mul w (2 * p + K + 8)) w) K
  obtain ⟨A, hAd⟩ : ∃ A, A = fftA CL CA CR w d := ⟨_, rfl⟩
  obtain ⟨O, hOd⟩ : ∃ O, O = fftO K := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = fftB (cellCost CM CA CS CL CR Mul w (2 * p + K + 8)) w := ⟨_, rfl⟩
  rw [← hAd, ← hOd, ← hBd] at hf ⊢
  rw [← hAd] at hA
  rw [← hOd] at hO
  rw [← hBd] at hB
  obtain ⟨Fc, hFd⟩ : ∃ Fc, Fc = fftCost A O B K := ⟨_, rfl⟩
  rw [← hFd] at hf ⊢
  unfold leafNodeBound
  obtain ⟨N, hN⟩ : ∃ N, N = 2 ^ K := ⟨_, rfl⟩
  rw [← hN] at hf ⊢
  obtain ⟨F, hF⟩ : ∃ F, F = 4 * Mul w + 2 * eb w + 2 * p + K + 10 := ⟨_, rfl⟩
  rw [← hF] at hB ⊢
  obtain ⟨G, hG⟩ : ∃ G, G = 2 * eb w + pin + 2 * p + K + 8 := ⟨_, rfl⟩
  rw [← hG]
  have hwG : w + d + 1 ≤ G := by rw [hG]; unfold eb; omega
  have hOF : 2 * p + K + 10 ≤ F := by rw [hF]; omega
  have f1 : N * A ≤ 233 * ((k + 30) * (N * G)) :=
    calc N * A ≤ N * (233 * (k + 30) * G) :=
          Nat.mul_le_mul_left _ (hA.trans (Nat.mul_le_mul_left _ hwG))
      _ = 233 * ((k + 30) * (N * G)) := by ring
  have f2 : N * O ≤ 14 * ((K + 1) * N * F) :=
    calc N * O ≤ N * (14 * (K + 1) * F) :=
          Nat.mul_le_mul_left _ (hO.trans (Nat.mul_le_mul_left _ hOF))
      _ = 14 * ((K + 1) * N * F) := by ring
  have f3 : N * (K * B) ≤ 841 * ((k + 30) * ((K + 1) * N * F)) :=
    calc N * (K * B) ≤ N * ((K + 1) * (841 * (k + 30) * F)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) hB)
      _ = 841 * ((k + 30) * ((K + 1) * N * F)) := by ring
  have f4 : N * (A + O + K * B) = N * A + N * O + N * (K * B) := by ring
  have f5 : (K + 1) * N * F ≤ (k + 30) * ((K + 1) * N * F) := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨Rst, hR⟩ : ∃ Rst, Rst = (K + 1) * 2 ^ (K + 1) * eb w + (hdrSyms (leafFields p K)).length +
      bitLen pin := ⟨_, rfl⟩
  have e : 1100 * (k + 30) * ((K + 1) * N * F + N * G + (K + 1) * 2 ^ (K + 1) * eb w +
      (hdrSyms (leafFields p K)).length + bitLen pin + 2) =
      1100 * ((k + 30) * ((K + 1) * N * F)) + 1100 * ((k + 30) * (N * G)) +
        1100 * ((k + 30) * (Rst + 2)) := by
    rw [hR]
    ring
  have f6 : 2 ≤ (k + 30) * (Rst + 2) :=
    le_trans (by omega : 2 ≤ Rst + 2) (Nat.le_mul_of_pos_left _ (by omega))
  rw [e]
  omega

#assert_std_axioms drCost_le rescCost_le fftA_le fftB_le fftO_le fft_part_le

end WP.W9gx
