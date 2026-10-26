import WP.W9ex.Phases
import Contracts.W9.Root

/-!
# WP.W9ex.Cost — width and length facts, and the cost arithmetic of the extract program
-/

namespace WP.W9ex

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

theorem hdrSyms_nil : hdrSyms [] = [] := rfl

/-- A digit is no wider than `|im|`. -/
theorem bitLen_mdig (z : ℤ × ℤ) : bitLen (mdig z) ≤ bitLen z.2.natAbs := by
  unfold mdig
  split_ifs
  · have hx := Nat.div_le_self z.2.natAbs (2 ^ 8)
    exact bitLen_mono _ _ (by omega)
  · simp [bitLen_zero]

theorem length_hdrSyms_le (w : ℕ) : ∀ ds : List ℕ, (∀ d ∈ ds, bitLen d ≤ w) →
    (hdrSyms ds).length ≤ ds.length * (w + 1)
  | [], _ => by simp [hdrSyms]
  | d :: ds, h => by
    have h1 := h d (List.mem_cons_self ..)
    have h2 := length_hdrSyms_le w ds (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [hdrSyms_cons, List.length_append, List.length_cons, length_natSyms, List.length_cons,
      add_mul, one_mul]
    omega

theorem rootHdrLen_eq (b K0 k1 k2 : ℕ) :
    rootHdrLen b K0 k1 k2 = bitLen b + bitLen K0 + bitLen k1 + bitLen k2 + 4 := by
  simp only [rootHdrLen, hdrSyms_cons, hdrSyms_nil, List.length_append, List.length_cons,
    List.length_nil, length_natSyms]
  omega

/-- Bit lengths of a counter below `2^K0`. -/
theorem bitLen_succ_le {K0 n : ℕ} (hn : n ≤ 2 ^ K0) :
    ∀ i, i < n → bitLen (i + 1) ≤ K0 + 1 := by
  intro i hi
  apply bitLen_le_of_lt_two_pow
  have : 2 ^ (K0 + 1) = 2 * 2 ^ K0 := by ring
  omega

/-- The cost arithmetic: the program's exact phase costs fit `64 · (budget)`. -/
theorem cost_le (N K0 b ebw k1 k2 blb blK0 blk1 blk2 Lh R Ld : ℕ) (hk : k1 + k2 ≤ N)
    (heb : 4 ≤ ebw) (hLh : Lh = blk1 + 1 + (blK0 + 1 + (blb + 1))) (hR : R ≤ N * ebw)
    (hLd : Ld ≤ N * ebw) :
    3 + ((3 * blb + 3 + (3 * blK0 + 3 + (7 * blk1 + 7 +
        (k1 * (6 * (K0 + 1) + 12 * ebw + 10) + 2)))) +
      ((3 * blk1 + 3 + (7 * blk2 + 7 + (k2 * (6 * (K0 + 1) + 12 * ebw + 10) + 2))) +
        (3 * Lh + 2 + (2 * R + 2 + (1 + (3 * Ld + 2 + 1)))))) ≤
    64 * (N * (ebw + b + K0) + (blb + blK0 + blk1 + blk2 + 4) + 1) := by
  have h1 : k1 * (6 * (K0 + 1) + 12 * ebw + 10) + k2 * (6 * (K0 + 1) + 12 * ebw + 10) ≤
      N * (6 * (K0 + 1) + 12 * ebw + 10) := by
    rw [← add_mul]
    exact Nat.mul_le_mul_right _ hk
  have h2 : N * (6 * (K0 + 1) + 12 * ebw + 10) = 6 * (N * K0) + 12 * (N * ebw) + 16 * N := by
    ring
  have h3 : N * 4 ≤ N * ebw := Nat.mul_le_mul_left _ heb
  have h4 : N * (ebw + b + K0) = N * ebw + N * b + N * K0 := by ring
  rw [h4]
  omega

#assert_std_axioms hdrSyms_nil bitLen_mdig length_hdrSyms_le rootHdrLen_eq bitLen_succ_le cost_le

end WP.W9ex
