import WP.W7k3c.State

/-!
# WP.W7k3c.Macro — one machine step on the abstract state

Each lemma runs one contract call (or raw push/pop) on scratch stacks of `St S V dv` and gives the
new abstract state, with the **uniform cost** `U C W = 4·C²·(W+2)⁴` whenever every operand has bit
length `≤ W` (shift amounts and counters `≤ W`). Summing over the program then gives
`(#steps)·U C W`.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- The uniform per-step cost bound. -/
def U (C W : ℕ) : ℕ := 4 * C * C * (W + 2) ^ 4

theorem U_of {C W x : ℕ} (hC : 1 ≤ C) (hx : x ≤ 4 * (W + 2) ^ 4) : C * x ≤ U C W := by
  unfold U
  calc C * x ≤ C * (4 * (W + 2) ^ 4) := Nat.mul_le_mul_left _ hx
    _ ≤ C * C * (4 * (W + 2) ^ 4) := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left C hC)
    _ = 4 * C * C * (W + 2) ^ 4 := by ring

theorem pow4_ge (W : ℕ) : W + 2 ≤ (W + 2) ^ 4 := Nat.le_self_pow (by norm_num) _

theorem pow24 (W : ℕ) : (W + 2) ^ 2 ≤ (W + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem one_le_U {C W : ℕ} (hC : 1 ≤ C) : 1 ≤ U C W := by
  have h := U_of (W := W) hC (x := 1) (by have := pow4_ge W; omega)
  omega

theorem U_lin {C W x : ℕ} (hC : 1 ≤ C) (hx : x ≤ 3 * W + 3) : C * x ≤ U C W :=
  U_of hC (by have := pow4_ge W; omega)

theorem U_quad {C W a b : ℕ} (hC : 1 ≤ C) (ha : a ≤ W + 1) (hb : b ≤ W + 1) :
    C * (a * b + a + b + 1) ≤ U C W := by
  refine U_of hC ?_
  have h1 : a * b + a + b + 1 = (a + 1) * (b + 1) := by ring
  have h2 : (a + 1) * (b + 1) ≤ (W + 2) * (W + 2) := Nat.mul_le_mul (by omega) (by omega)
  have h3 := pow24 W
  have h4 : (W + 2) * (W + 2) = (W + 2) ^ 2 := by ring
  omega

theorem U_sq {C W a : ℕ} (hC : 1 ≤ C) (ha : a ≤ W + 1) : C * (a * a + 1) ≤ U C W :=
  le_trans (Nat.mul_le_mul_left _ (by omega)) (U_quad hC ha ha)

theorem U_four {C W B : ℕ} (hC : 1 ≤ C) (hB : B ≤ W) : C * (B + 1) ^ 4 ≤ U C W := by
  refine U_of hC ?_
  have h := Nat.pow_le_pow_left (show B + 1 ≤ W + 2 by omega) 4
  omega

theorem U_ser {C W n W' : ℕ} (hC : 1 ≤ C) (hn : n ≤ W) (hW : W' ≤ W) :
    C * (n + 1) * (W' + 2) ^ 2 ≤ U C W := by
  rw [mul_assoc]
  refine U_of hC ?_
  calc (n + 1) * (W' + 2) ^ 2 ≤ (W + 2) * (W + 2) ^ 2 :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
    _ = (W + 2) ^ 3 := by ring
    _ ≤ (W + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ 4 * (W + 2) ^ 4 := by omega

theorem U_mul {C W w : ℕ} {Mul : ℕ → ℕ} (hC : 1 ≤ C) (hM : ∀ w, Mul w ≤ C * (w + 1) ^ 2)
    (hw : w ≤ W) : C * Mul w + C ≤ U C W := by
  have h1 : Mul w ≤ C * (W + 2) ^ 2 :=
    le_trans (hM w) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have h2 := pow24 W
  have h3 : 1 ≤ (W + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold U
  calc C * Mul w + C ≤ C * (C * (W + 2) ^ 2) + C * (C * (W + 2) ^ 2) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h1)
          (by nlinarith [Nat.mul_le_mul_left C (Nat.mul_le_mul hC h3)])
    _ = 2 * C * C * (W + 2) ^ 2 := by ring
    _ ≤ 4 * C * C * (W + 2) ^ 4 := by
        have := Nat.mul_le_mul_left (2 * C * C) h2
        nlinarith

#assert_std_axioms U_of pow4_ge pow24 one_le_U U_lin U_quad U_sq U_four U_ser U_mul

end WP.W7k3c
