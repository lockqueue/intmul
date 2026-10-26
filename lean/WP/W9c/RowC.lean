import WP.W9c.RowCSpec

/-!
# WP.W9c.RowC — phase C of the row driver: two coordinate passes and the zip (`RowCOK`)
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

theorem chunks_mem (W : ℕ) : ∀ (n : ℕ) (v blk : List ℤ), blk ∈ chunks W n v →
    blk.length ≤ W ∧ ∀ x ∈ blk, x ∈ v
  | 0, _, _, h => by simp [chunks] at h
  | n + 1, [], _, h => by simp [chunks] at h
  | n + 1, y :: ys, blk, h => by
    simp only [chunks, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨List.length_take_le _ _, fun x hx => List.mem_of_mem_take hx⟩
    · obtain ⟨h1, h2⟩ := chunks_mem W n _ blk h
      exact ⟨h1, fun x hx => List.mem_of_mem_drop (h2 x hx)⟩

theorem length_chunks_congr (W : ℕ) (hW : 1 ≤ W) : ∀ (n : ℕ) (v u : List ℤ),
    v.length = u.length → (chunks W n v).length = (chunks W n u).length
  | 0, _, _, _ => rfl
  | n + 1, [], [], _ => rfl
  | n + 1, [], _ :: _, h => by simp at h
  | n + 1, _ :: _, [], h => by simp at h
  | n + 1, y :: ys, z :: zs, h => by
    simp only [chunks, List.length_cons]
    rw [length_chunks_congr W hW n ((y :: ys).drop W) ((z :: zs).drop W) (by simp at h ⊢; omega)]

theorem length_chunks_mul (W : ℕ) (hW : 1 ≤ W) : ∀ (n : ℕ) (v : List ℤ),
    (chunks W n v).length * W ≤ v.length + W - 1
  | 0, v => by simp [chunks]
  | n + 1, [] => by simp [chunks]
  | n + 1, y :: ys => by
    simp only [chunks, List.length_cons]
    have ih := length_chunks_mul W hW n ((y :: ys).drop W)
    simp only [List.length_drop, List.length_cons] at ih
    rw [Nat.add_mul, Nat.one_mul]
    by_cases h : W ≤ ys.length + 1
    · omega
    · have : (chunks W n ((y :: ys).drop W)) = [] := by
        rw [List.drop_eq_nil_of_le (by simp; omega)]
        cases n <;> rfl
      rw [this]; simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]; omega

end WP.W9c
