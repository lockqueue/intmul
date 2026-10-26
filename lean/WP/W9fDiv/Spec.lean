import Contracts.Machine.W6a
import IntMul.MaterializedAndComputable.ComputablePrimitives

/-!
# WP.W9fDiv.Spec — the W9fDiv statement (shape agreed with W9f)

* `W9fDiv_divRound`: `z += IntMul.divRoundRatInt a b` for signed `a` and `b`. The result is `0`
  when `b ≤ 0`, as in the snapshot's definition (ComputablePrimitives.lean:625).
* `divRound_bridge`: the snapshot's `IntMul.divRoundRatInt` and the restatement
  `TMFw.Contracts.divRoundRatInt` of `Contracts.Machine.W6a` are the same function (`rfl`).

This module imports the snapshot (for `IntMul.divRoundRatInt`) and the frozen contracts, nothing
else.
-/

namespace WP.W9fDiv

open TMFw TMFw.Contracts

/-- **W9fDiv.divRound**: `z += IntMul.divRoundRatInt a b`.

* Stacks: `.inl 0` = signed `a`, `.inl 1` = signed `b` (both restored), `.inl 2` = destination.
* Up to 16 scratch stacks (arbitrary content, restored).
* Cost `C·(|a|·|b| + |a| + |b| + 1)`, where `|·|` is the bit length of the magnitude.

Matches the binary-operation contract shape consumed by `WP.W9fF.Kit` and `WP.W9fN.Kit`. -/
def W9fDiv_divRound : Prop :=
  MContract Unit 3 16 Unit fun _ m _ C _ P =>
    ∀ (a b : ℤ) (ra rb : List Sym) (S : Loc 3 m → List Sym), TermOK ra → TermOK rb →
      TermOK (S (.inl 2)) → S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
      Runs P S (Function.update S (.inl 2) (intSyms (IntMul.divRoundRatInt a b) ++ S (.inl 2)))
        (fun _ => True)
        (C * (bitLen a.natAbs * bitLen b.natAbs + bitLen a.natAbs + bitLen b.natAbs + 1))

/-- The snapshot's `divRoundRatInt` is the restatement of `Contracts.Machine.W6a`. -/
theorem divRound_bridge : IntMul.divRoundRatInt = TMFw.Contracts.divRoundRatInt := rfl

example : IntMul.divRoundRatInt 5 2 = 3 := by decide
example : IntMul.divRoundRatInt (-5) 2 = -2 := by decide
example : IntMul.divRoundRatInt 7 (-3) = 0 := by decide
example : IntMul.divRoundRatInt 7 0 = 0 := by decide

#assert_std_axioms divRound_bridge

end WP.W9fDiv
