import Contracts.Machine.Common

/-!
# Contracts.Machine.W5 — signed Toom-3 multiplication

Conventions: `Contracts.Machine.Common` (signed numbers `intSyms z`: sign symbol on top, then the
magnitude LSB-first; `MContract`; exact final stacks).
* Named stacks: `x`, `y` (operands, restored) and `z` (the product is pushed on top).
* Up to 8 scratch stacks, matching the arithmetic register bank `A, B, R, T1..T6, U` minus the
  operands and result.
* Operands are non-destructive (restored on exit).

## Cost recurrence

`T3 c0 c1 w0 w` is the explicit Toom-3 recurrence:
* above the threshold: `T3(w) = 5·T3(⌈w/3⌉ + c0) + c1·w`;
* for `w ≤ w0` (or when the recursion would not shrink): the constant schoolbook base
  `c1·(w0+1)²`.

Taking the base cost at the threshold makes `T3` **monotone** (`T3_mono`, proved below). An
implementation may therefore recurse on the actual operand lengths, while the contract quantifies
over every declared width `w` ≥ both lengths.

## Interface to the pipeline cost proof

`W5_T3_bound` (pure, open) is `T3(w)·log₂ w ≤ C'·w·√w` for `w ≥ 4`, i.e.
`T3(w) = O(w^{3/2} / log w)`. It is true because `T3(w) = Θ(w^{log₃ 5})` with `log₃ 5 ≈ 1.465 < 1.5`.

**Mutation-test ideas.**
* A Toom-3 with a sign bug in interpolation: the product is wrong for `x = -1, y = 1`.
* Schoolbook at every level, i.e. `4`-way instead of `5`-way recursion, or no recursion: correct,
  but `T3`-cost fails for large `w`. Run `Triple.cost_ge` with `C` fixed.
* Destroying an operand: the exact-frame post-state fails.
-/

namespace TMFw.Contracts

/-- **Toom-3 cost recurrence** with constant schoolbook base `c1·(w0+1)²`; `⌈w/3⌉ = (w+2)/3`. -/
def T3 (c0 c1 w0 : ℕ) (w : ℕ) : ℕ :=
  if h : w0 < w ∧ (w + 2) / 3 + c0 < w then 5 * T3 c0 c1 w0 ((w + 2) / 3 + c0) + c1 * w
  else c1 * (w0 + 1) * (w0 + 1)
termination_by w
decreasing_by omega

/-- **W5.toom3Mul**: signed multiplication `z += a·b`.
* Stacks: `x`, `y` (operands, restored), `z` (destination).
* Cost: for every declared width `w` bounding both magnitudes' bit lengths, at most
  `C·T3 c0 c1 w0 w + C`. The constants `c0 c1 w0` are chosen by the implementer, before `C`. -/
def W5_toom3Mul : Prop :=
  ∃ c0 c1 w0 : ℕ, MContract Unit 3 8 Unit fun _ m _ C _ P =>
    ∀ (w : ℕ) (a b : ℤ) (ra rb : List Sym) (S : Loc 3 m → List Sym),
      bitLen a.natAbs ≤ w → bitLen b.natAbs ≤ w → TermOK ra → TermOK rb →
      S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
      Runs P S (Function.update S (.inl 2) (intSyms (a * b) ++ S (.inl 2))) (fun _ => True)
        (C * T3 c0 c1 w0 w + C)

/-- **Multiplication at a given cost function.**
The body of `W5_toom3Mul` with `C * Mul w + C` in place of `C * T3 c0 c1 w0 w + C`.
Every multiplication-using kernel (W7, W9) is stated as `∀ Mul, W5_mulAt Mul → … → Kernel Mul`, so that ONE
shared cost function (instantiated at assembly as `T3 c0 c1 w0` from `W5_toom3Mul`) serves all kernels. -/
def W5_mulAt (Mul : ℕ → ℕ) : Prop :=
  MContract Unit 3 8 Unit fun _ m _ C _ P =>
    ∀ (w : ℕ) (a b : ℤ) (ra rb : List Sym) (S : Loc 3 m → List Sym),
      bitLen a.natAbs ≤ w → bitLen b.natAbs ≤ w → TermOK ra → TermOK rb →
      S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
      Runs P S (Function.update S (.inl 2) (intSyms (a * b) ++ S (.inl 2))) (fun _ => True)
        (C * Mul w + C)

theorem W5_toom3Mul_iff_mulAt : W5_toom3Mul ↔ ∃ c0 c1 w0, W5_mulAt (T3 c0 c1 w0) := Iff.rfl

/-- **Pipeline interface (pure; open, owner W5 or W10).** For all constants,
`T3(w) ≤ C'·w^{3/2} / log₂ w` for `w ≥ 4`, stated in `ℕ` as `T3(w)·log₂ w ≤ C'·(w·⌊√w⌋)`. -/
def W5_T3_bound : Prop :=
  ∀ c0 c1 w0 : ℕ, ∃ C' : ℕ, ∀ w : ℕ, 4 ≤ w → T3 c0 c1 w0 w * Nat.log2 w ≤ C' * (w * Nat.sqrt w)

/-! ## Proved facts about `T3` -/

theorem T3_unfold (c0 c1 w0 w : ℕ) : T3 c0 c1 w0 w =
    if w0 < w ∧ (w + 2) / 3 + c0 < w then 5 * T3 c0 c1 w0 ((w + 2) / 3 + c0) + c1 * w
    else c1 * (w0 + 1) * (w0 + 1) := by
  rw [T3, dite_eq_ite]

/-- `T3` is at least the schoolbook base. -/
theorem T3_ge_base (c0 c1 w0 : ℕ) : ∀ w, c1 * (w0 + 1) * (w0 + 1) ≤ T3 c0 c1 w0 w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rw [T3_unfold]
    split_ifs with h
    · have := ih _ h.2
      omega
    · exact le_refl _

/-- One-step monotonicity. -/
theorem T3_le_succ (c0 c1 w0 : ℕ) : ∀ w, T3 c0 c1 w0 w ≤ T3 c0 c1 w0 (w + 1) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rw [T3_unfold c0 c1 w0 w, T3_unfold c0 c1 w0 (w + 1)]
    by_cases h1 : w0 < w + 1 ∧ (w + 1 + 2) / 3 + c0 < w + 1
    · rw [if_pos h1]
      by_cases h0 : w0 < w ∧ (w + 2) / 3 + c0 < w
      · rw [if_pos h0]
        have hmono : T3 c0 c1 w0 ((w + 2) / 3 + c0) ≤ T3 c0 c1 w0 ((w + 1 + 2) / 3 + c0) := by
          by_cases heq : (w + 1 + 2) / 3 = (w + 2) / 3
          · rw [heq]
          · have e1 : (w + 1 + 2) / 3 + c0 = ((w + 2) / 3 + c0) + 1 := by omega
            rw [e1]
            exact ih _ h0.2
        have hc : c1 * w ≤ c1 * (w + 1) := Nat.mul_le_mul_left _ (by omega)
        omega
      · rw [if_neg h0]
        have := T3_ge_base c0 c1 w0 ((w + 1 + 2) / 3 + c0)
        omega
    · rw [if_neg h1]
      have h0 : ¬ (w0 < w ∧ (w + 2) / 3 + c0 < w) := by omega
      rw [if_neg h0]

/-- **`T3` is monotone**, so a bound at the actual operand width implies the bound at any declared
width. -/
theorem T3_mono (c0 c1 w0 : ℕ) : Monotone (T3 c0 c1 w0) :=
  monotone_nat_of_le_succ (T3_le_succ c0 c1 w0)

#assert_std_axioms T3_unfold T3_ge_base T3_le_succ T3_mono

end TMFw.Contracts
