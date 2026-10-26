import Contracts.W7.Kernels

/-!
# WP.W7k2.Canon.Series — the fixed-point Taylor recurrence, value part

The snapshot's series evaluator `runRecurrenceSeriesCosted` (CTr:126) carries a width argument `w`
that only affects the cost component. This module restates its value component as a plain
recursion `serState` and proves the two equal (`runRecurrenceSeriesCosted_fst_eq`). Every kernel
of W7k2 (`stdChar`, sinc, exp, half-erf) runs this recurrence; the machine runs it as one counted
loop whose body is `serStep`.

One step from state `(a_k, s_k)` (CTr:112):
* `s_{k+1} = s_k + a_k`;
* `a_{k+1} = divRoundRatInt (a_k · c · f k) (g k · d)`.
-/

namespace WP.W7k2

open IntMul

/-- One recurrence step (CTr:112, values only); state `(a_k, s_k)`. -/
def serStep (c : ℤ) (d : ℕ) (f g : ℕ → ℕ) (k : ℕ) (st : ℤ × ℤ) : ℤ × ℤ :=
  (IntMul.divRoundRatInt (st.1 * c * ((f k : ℕ) : ℤ)) (((g k : ℕ) : ℤ) * (d : ℤ)), st.2 + st.1)

/-- `n` recurrence steps from `(a0, 0)` (CTr:126, values only). -/
def serState (a0 c : ℤ) (d : ℕ) (f g : ℕ → ℕ) : ℕ → ℤ × ℤ
  | 0 => (a0, 0)
  | n + 1 => serStep c d f g n (serState a0 c d f g n)

theorem serState_zero (a0 c : ℤ) (d : ℕ) (f g : ℕ → ℕ) : serState a0 c d f g 0 = (a0, 0) := rfl

theorem serState_succ (a0 c : ℤ) (d : ℕ) (f g : ℕ → ℕ) (n : ℕ) :
    serState a0 c d f g (n + 1) = serStep c d f g n (serState a0 c d f g n) := rfl

/-- **The snapshot's series value is `serState`**, for every width `w`. -/
theorem runRecurrenceSeriesCosted_fst_eq (w : ℕ) (a0 c : ℤ) (d : ℕ) (f g : ℕ → ℕ) (n : ℕ) :
    (runRecurrenceSeriesCosted w a0 c d f g n).1 = serState a0 c d f g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [runRecurrenceSeriesCosted, recurrenceStepCosted, costedDivRoundRatInt,
      costedMulInt]
    rw [ih]
    rfl

#assert_std_axioms serState_zero serState_succ runRecurrenceSeriesCosted_fst_eq

end WP.W7k2
