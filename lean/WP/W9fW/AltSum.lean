import WP.W9fW.Builders

/-!
# WP.W9fW.AltSum — the Nyquist alternating sum

`W8.solveNyqBarrett` forms `alt_part = sumRangePair (fun v => gAltTerm v (read1D Z v)) t1` with
`Z = W8.zPartNyqBarrett q H μ a Y (t1 - 1)`. Every entry of `Z` has `|coord| ≤ 2^H`
(`zPartNyqBarrett_abs_le`), `gAltTerm` only flips signs, so
* `altSum_abs_le`: `|alt_part.j| ≤ t1·2^H` for every `t1`;
* `altSum_abs_lt`: `|alt_part.j| < t1·(2^H + 1)` for `t1 > 0` (for `t1 = 0` both sides are `0`).
-/

namespace WP.W9fW

open IntMul IntMulTM.Contracts TMFw.Contracts

/-- A termwise bound `B` on `n` summands gives `n·B`. -/
theorem sumRangePair_abs_le (f : ℕ → ℤ × ℤ) (B : ℤ) :
    ∀ n, (∀ i < n, |(f i).1| ≤ B ∧ |(f i).2| ≤ B) →
      |(sumRangePair f n).1| ≤ (n : ℤ) * B ∧ |(sumRangePair f n).2| ≤ (n : ℤ) * B := by
  intro n
  induction n with
  | zero =>
    intro _
    have e : sumRangePair f 0 = (0, 0) := rfl
    rw [e]
    simp
  | succ n ih =>
    intro h
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => h i (by omega))
    obtain ⟨h1, h2⟩ := h n (by omega)
    have e : sumRangePair f (n + 1) = gAdd (sumRangePair f n) (f n) := rfl
    rw [e]
    simp only [gAdd]
    push_cast
    obtain ⟨a1, a2⟩ := abs_le.mp ih1
    obtain ⟨b1, b2⟩ := abs_le.mp h1
    obtain ⟨c1, c2⟩ := abs_le.mp ih2
    obtain ⟨d1, d2⟩ := abs_le.mp h2
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- `gAltTerm` only flips signs. -/
theorem gAltTerm_abs (v : ℕ) (z : ℤ × ℤ) :
    |(gAltTerm v z).1| = |z.1| ∧ |(gAltTerm v z).2| = |z.2| := by
  unfold gAltTerm
  split_ifs
  · exact ⟨rfl, rfl⟩
  · exact ⟨abs_neg z.1, abs_neg z.2⟩

/-- **Alternating sum, non-strict** (every `t1`). -/
theorem altSum_abs_le (q H t1 : ℕ) (a : ℤ) (Y : Array (ℤ × ℤ)) (ha : 0 < a)
    (hb : W8.zPartNyqBound q H a Y (t1 - 1)) :
    |(sumRangePair (fun v => gAltTerm v
        (read1D (W8.zPartNyqBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a Y (t1 - 1)) v)) t1).1| ≤
        (t1 : ℤ) * ((2 ^ H : ℕ) : ℤ) ∧
      |(sumRangePair (fun v => gAltTerm v
        (read1D (W8.zPartNyqBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a Y (t1 - 1)) v)) t1).2| ≤
        (t1 : ℤ) * ((2 ^ H : ℕ) : ℤ) := by
  apply sumRangePair_abs_le
  intro i _
  obtain ⟨e1, e2⟩ := gAltTerm_abs i
    (read1D (W8.zPartNyqBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a Y (t1 - 1)) i)
  obtain ⟨h1, h2⟩ := zPartNyqBarrett_abs_le q H a Y (t1 - 1) ha hb i
  exact ⟨e1.le.trans h1, e2.le.trans h2⟩

/-- **Alternating sum, strict** (`t1 > 0`), the form W9f consumes. -/
theorem altSum_abs_lt (q H t1 : ℕ) (a : ℤ) (Y : Array (ℤ × ℤ)) (ha : 0 < a)
    (hb : W8.zPartNyqBound q H a Y (t1 - 1)) (ht1 : 0 < t1) :
    |(sumRangePair (fun v => gAltTerm v
        (read1D (W8.zPartNyqBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a Y (t1 - 1)) v)) t1).1| <
        (t1 : ℤ) * (((2 ^ H : ℕ) : ℤ) + 1) ∧
      |(sumRangePair (fun v => gAltTerm v
        (read1D (W8.zPartNyqBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a Y (t1 - 1)) v)) t1).2| <
        (t1 : ℤ) * (((2 ^ H : ℕ) : ℤ) + 1) := by
  obtain ⟨h1, h2⟩ := altSum_abs_le q H t1 a Y ha hb
  have ht : (0 : ℤ) < (t1 : ℤ) := by exact_mod_cast ht1
  have hlt : (t1 : ℤ) * ((2 ^ H : ℕ) : ℤ) < (t1 : ℤ) * (((2 ^ H : ℕ) : ℤ) + 1) := by
    rw [mul_add, mul_one]
    linarith
  exact ⟨lt_of_le_of_lt h1 hlt, lt_of_le_of_lt h2 hlt⟩

#assert_std_axioms sumRangePair_abs_le gAltTerm_abs altSum_abs_le altSum_abs_lt

end WP.W9fW
