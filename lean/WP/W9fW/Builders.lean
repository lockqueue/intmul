import WP.W9fW.Basic

/-!
# WP.W9fW.Builders — widths of the three reciprocal column builders (Contracts/W6.lean)

With `μ = ⌊2^H / a⌋` and `a > 0`, under the snapshot-side dividend bounds:

| builder | bound hypothesis | extra | conclusion, every index `k` |
|---|---|---|---|
| `W8.zPartFwdBarrett q H μ a c Y n` | `W8.zPartFwdBound q H a c Y n` | – | `|coord| ≤ 2^H`, `EntryW (H+1)` |
| `W8.zHomFwdBarrett q H μ a c n` | `W8.zHomFwdBound q H a c n` | `q + 2 ≤ H` | same |
| `W8.zPartNyqBarrett q H μ a Y n` | `W8.zPartNyqBound q H a Y n` | – | same |

Indices `k > n` read `(0, 0)`. The `ArrW (H+1)` forms follow (`arrW_of_read1D`).

Proof: induction on `n`. The new entry is one reciprocal step whose numerator is bounded because
the prefix equals the snapshot's exact builder (`W8_zPartFwd_reciprocal_holds` etc.).
`q + 2 ≤ H` is needed for zHom's first entry `(2^(q+2), 0)`: without it the claim fails
(`q = H = 0`, `n = 0`: the entry `(4, 0)` has `bitLen 3 > 1`).
-/

namespace WP.W9fW

open IntMul IntMulTM.Contracts TMFw.Contracts

theorem zPartFwdBarrett_magLe_aux (q H : ℕ) (a c : ℤ) (Y : Array (ℤ × ℤ)) (ha : 0 < a) :
    ∀ n, W8.zPartFwdBound q H a c Y n →
      ∀ k, MagLe H (read1D (W8.zPartFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c Y n) k) := by
  intro n
  induction n with
  | zero =>
    intro _ k
    exact magLe_read1D_singleton (magLe_zero H) k
  | succ n ih =>
    intro hb
    have hb' : W8.zPartFwdBound q H a c Y n := fun m hm => hb m (by omega)
    have heq := W8_zPartFwd_reciprocal_holds q H a c Y n ha hb'
    have hx := recStepBarrett_magLe q H a c (read1D Y (n + 1))
      (read1D (W8.zPartFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c Y n) n) ha
      (by rw [heq]; exact hb n (by omega))
    simp only [W8.zPartFwdBarrett]
    exact magLe_read1D_push (ih hb') hx

theorem zHomFwdBarrett_magLe_aux (q H : ℕ) (a c : ℤ) (ha : 0 < a) (hqH : q + 2 ≤ H) :
    ∀ n, W8.zHomFwdBound q H a c n →
      ∀ k, MagLe H (read1D (W8.zHomFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c n) k) := by
  intro n
  induction n with
  | zero =>
    intro _ k
    have hP : (0 : ℤ) ≤ ((2 ^ H : ℕ) : ℤ) := by positivity
    have hpow := Nat.pow_le_pow_right (show 2 > 0 by decide) hqH
    have hle : ((2 ^ (q + 2) : ℕ) : ℤ) ≤ ((2 ^ H : ℕ) : ℤ) := by exact_mod_cast hpow
    have h0 : MagLe H (((2 ^ (q + 2) : ℕ) : ℤ), 0) := by
      refine ⟨?_, (abs_zero : |(0 : ℤ)| = 0).le.trans hP⟩
      show |((2 ^ (q + 2) : ℕ) : ℤ)| ≤ _
      rw [abs_of_nonneg (by positivity)]
      exact hle
    exact magLe_read1D_singleton h0 k
  | succ n ih =>
    intro hb
    have hb' : W8.zHomFwdBound q H a c n := fun m hm => hb m (by omega)
    have heq := W8_zHomFwd_reciprocal_holds q H a c n ha hb'
    have hx := recStepBarrett_magLe q H a c (0, 0)
      (read1D (W8.zHomFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c n) n) ha
      (by rw [heq]; exact hb n (by omega))
    simp only [W8.zHomFwdBarrett]
    exact magLe_read1D_push (ih hb') hx

theorem zPartNyqBarrett_magLe_aux (q H : ℕ) (a : ℤ) (Y : Array (ℤ × ℤ)) (ha : 0 < a) :
    ∀ n, W8.zPartNyqBound q H a Y n →
      ∀ k, MagLe H (read1D (W8.zPartNyqBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a Y n) k) := by
  intro n
  induction n with
  | zero =>
    intro _ k
    exact magLe_read1D_singleton (magLe_zero H) k
  | succ n ih =>
    intro hb
    have hb' : W8.zPartNyqBound q H a Y n := fun m hm => hb m (by omega)
    have heq := W8_zPartNyq_reciprocal_holds q H a Y n ha hb'
    have hx := recStepBarrett_magLe q H a a (read1D Y (n + 1))
      (read1D (W8.zPartNyqBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a Y n) n) ha
      (by rw [heq]; exact hb n (by omega))
    simp only [W8.zPartNyqBarrett]
    exact magLe_read1D_push (ih hb') hx

/-! ## Exported forms (agreed with W9f) -/

/-- zPart (Fwd; the Bwd column is this lemma with swapped coefficients and reversed input):
every entry has `|coord| ≤ 2^H`. -/
theorem zPartFwdBarrett_abs_le (q H : ℕ) (a c : ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) (ha : 0 < a)
    (hb : W8.zPartFwdBound q H a c Y n) (k : ℕ) :
    |(read1D (W8.zPartFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c Y n) k).1| ≤ ((2 ^ H : ℕ) : ℤ) ∧
      |(read1D (W8.zPartFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c Y n) k).2| ≤
        ((2 ^ H : ℕ) : ℤ) :=
  zPartFwdBarrett_magLe_aux q H a c Y ha n hb k

theorem zPartFwdBarrett_entryW (q H : ℕ) (a c : ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) (ha : 0 < a)
    (hb : W8.zPartFwdBound q H a c Y n) :
    ∀ k, W9.EntryW (H + 1) (read1D (W8.zPartFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c Y n) k) :=
  fun k => entryW_of_magLe (zPartFwdBarrett_magLe_aux q H a c Y ha n hb k)

theorem zPartFwdBarrett_arrW (q H : ℕ) (a c : ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) (ha : 0 < a)
    (hb : W8.zPartFwdBound q H a c Y n) :
    W9.ArrW (H + 1) (W8.zPartFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c Y n) :=
  arrW_of_read1D (zPartFwdBarrett_entryW q H a c Y n ha hb)

/-- zHom: every entry has `|coord| ≤ 2^H` (needs `q + 2 ≤ H` for the first entry `2^(q+2)`). -/
theorem zHomFwdBarrett_abs_le (q H : ℕ) (a c : ℤ) (n : ℕ) (ha : 0 < a) (hqH : q + 2 ≤ H)
    (hb : W8.zHomFwdBound q H a c n) (k : ℕ) :
    |(read1D (W8.zHomFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c n) k).1| ≤ ((2 ^ H : ℕ) : ℤ) ∧
      |(read1D (W8.zHomFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c n) k).2| ≤ ((2 ^ H : ℕ) : ℤ) :=
  zHomFwdBarrett_magLe_aux q H a c ha hqH n hb k

theorem zHomFwdBarrett_entryW (q H : ℕ) (a c : ℤ) (n : ℕ) (ha : 0 < a) (hqH : q + 2 ≤ H)
    (hb : W8.zHomFwdBound q H a c n) :
    ∀ k, W9.EntryW (H + 1) (read1D (W8.zHomFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c n) k) :=
  fun k => entryW_of_magLe (zHomFwdBarrett_magLe_aux q H a c ha hqH n hb k)

theorem zHomFwdBarrett_arrW (q H : ℕ) (a c : ℤ) (n : ℕ) (ha : 0 < a) (hqH : q + 2 ≤ H)
    (hb : W8.zHomFwdBound q H a c n) :
    W9.ArrW (H + 1) (W8.zHomFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c n) :=
  arrW_of_read1D (zHomFwdBarrett_entryW q H a c n ha hqH hb)

/-- Nyquist zPart: every entry has `|coord| ≤ 2^H`. -/
theorem zPartNyqBarrett_abs_le (q H : ℕ) (a : ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) (ha : 0 < a)
    (hb : W8.zPartNyqBound q H a Y n) (k : ℕ) :
    |(read1D (W8.zPartNyqBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a Y n) k).1| ≤ ((2 ^ H : ℕ) : ℤ) ∧
      |(read1D (W8.zPartNyqBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a Y n) k).2| ≤ ((2 ^ H : ℕ) : ℤ) :=
  zPartNyqBarrett_magLe_aux q H a Y ha n hb k

theorem zPartNyqBarrett_entryW (q H : ℕ) (a : ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) (ha : 0 < a)
    (hb : W8.zPartNyqBound q H a Y n) :
    ∀ k, W9.EntryW (H + 1) (read1D (W8.zPartNyqBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a Y n) k) :=
  fun k => entryW_of_magLe (zPartNyqBarrett_magLe_aux q H a Y ha n hb k)

theorem zPartNyqBarrett_arrW (q H : ℕ) (a : ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) (ha : 0 < a)
    (hb : W8.zPartNyqBound q H a Y n) :
    W9.ArrW (H + 1) (W8.zPartNyqBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a Y n) :=
  arrW_of_read1D (zPartNyqBarrett_entryW q H a Y n ha hb)

#assert_std_axioms zPartFwdBarrett_magLe_aux zHomFwdBarrett_magLe_aux zPartNyqBarrett_magLe_aux
  zPartFwdBarrett_abs_le zPartFwdBarrett_entryW zPartFwdBarrett_arrW zHomFwdBarrett_abs_le
  zHomFwdBarrett_entryW zHomFwdBarrett_arrW zPartNyqBarrett_abs_le zPartNyqBarrett_entryW
  zPartNyqBarrett_arrW

end WP.W9fW
