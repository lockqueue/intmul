import Contracts.Machine.Common

/-!
# Contracts.Machine.W6a — long division and signed rounding division

Conventions: `Contracts.Machine.Common` (unsigned `natSyms`, signed `intSyms`, `MContract`, exact
final stacks). Operands are restored; results are pushed on top of the destinations' previous
content; up to 6 scratch stacks.

* `W6a_divModNat`: floor division and remainder of naturals. Cost `O(w₁·w₂ + w₁ + w₂)` with
  `w₁ = |a|`, `w₂ = |b|` (bit lengths). This is schoolbook long division: `w₁ − w₂ + 1` quotient
  bits, each one `O(w₂)` compare-and-subtract.
* `W6a_divRound`: the snapshot's `divRoundRatInt` (ComputablePrimitives.lean:625), nearest-integer
  rounding `⌊num/den + 1/2⌋ = (2·num + den) / (2·den)` (Euclidean `/`), for a signed numerator and
  a positive natural denominator, as a wrapper around long division.

**Mutation-test ideas.**
* A quotient off by one when `b ∣ a`, i.e. `a / b + 1` because of a `<` vs `≤` slip in the subtract
  test: the exact post-state fails at `a = b = 1`.
* Truncating instead of floor rounding for negative numerators (`Int.tdiv`): `divRound` fails at
  `num = -5, den = 2`. The examples below pin `divRoundRatInt (-5) 2 = -2`.
* Restarting each quotient-bit step from the LSB of the whole dividend gives `O(w₁²·w₂)`, which
  violates the bound for `w₁ ≫ w₂`.
-/

namespace TMFw.Contracts

/-- **W6a.divMod**: `q += a / b` on stack `2` and `r += a % b` on stack `3`, for `b > 0`.
* Stacks: `0` = `a`, `1` = `b` (restored).
* Cost `C·(|a|·|b| + |a| + |b| + 1)`. -/
def W6a_divModNat : Prop :=
  MContract Unit 4 6 Unit fun _ m _ C _ P =>
    ∀ (a b : ℕ) (ra rb : List Sym) (S : Loc 4 m → List Sym), 0 < b → TermOK ra → TermOK rb →
      S (.inl 0) = natSyms a ++ ra → S (.inl 1) = natSyms b ++ rb →
      Runs P S (Function.update (Function.update S (.inl 2) (natSyms (a / b) ++ S (.inl 2)))
          (.inl 3) (natSyms (a % b) ++ S (.inl 3))) (fun _ => True)
        (C * (bitLen a * bitLen b + bitLen a + bitLen b + 1))

/-- The snapshot's `divRoundRatInt` (ComputablePrimitives.lean:625), restated verbatim:
`⌊num/den + 1/2⌋` for `0 < den`, and `0` otherwise. -/
def divRoundRatInt (num den : ℤ) : ℤ :=
  if 0 < den then (2 * num + den) / (2 * den) else 0

example : divRoundRatInt 5 2 = 3 := by decide
example : divRoundRatInt (-5) 2 = -2 := by decide
example : divRoundRatInt 7 3 = 2 := by decide
example : divRoundRatInt (-7) 3 = -2 := by decide

/-- **W6a.divRound**: `z += divRoundRatInt num den`.
* Stacks: `0` = signed `num`, `1` = natural `den > 0` (restored), `2` = destination.
* Cost `C·(|num|·|den| + |num| + |den| + 1)`. -/
def W6a_divRound : Prop :=
  MContract Unit 3 6 Unit fun _ m _ C _ P =>
    ∀ (num : ℤ) (den : ℕ) (ra rb : List Sym) (S : Loc 3 m → List Sym), 0 < den →
      TermOK ra → TermOK rb →
      S (.inl 0) = intSyms num ++ ra → S (.inl 1) = natSyms den ++ rb →
      Runs P S (Function.update S (.inl 2) (intSyms (divRoundRatInt num den) ++ S (.inl 2)))
        (fun _ => True)
        (C * (bitLen num.natAbs * bitLen den + bitLen num.natAbs + bitLen den + 1))

end TMFw.Contracts
