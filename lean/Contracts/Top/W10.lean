import IntMulTM.Framework.Accept
import IntMulTM.Framework.AxiomGuard
import IntMulTM.SpecFacts

/-!
# Contracts.Top.W10 — cost interface: per-stage bounds ⟹ `O(L log L)`

The composed program's source-level cost is assembled from per-stage bounds, as functions of the
operand bit length `n` (`StageCosts`): input stage, tables, root stage, copy-out, and per pipeline
level the non-multiplication work plus `mulCount` multiplications of width `mulWidth`.

`W10_cost` is the **pure arithmetic obligation**: under the level-synchronous per-stage bounds
(`StageBounds`) and the W5 interface `M(w) ≤ C·w^{3/2}/log₂ w` (`MulBound`, the ℕ form of
`W5_T3_bound`), the total is `O(n log n)`.

Why the `w^{3/2}/log w` rate suffices: each level multiplies `O(n)` bits in total, at widths
`w ≤ A·(log₂ n + 1)²`. So a level costs `O(n·√w/log w) = O(n log n / log log n)`, and there are
`O(log log n)` levels.

The proved bridges convert to what W12 consumes (`T L + 1 ≤ C·L·log₂ L`, measured in the input length
`L`):
* `nlogn_succ`: add the wrapper's `+ 1`;
* `cost_le_at_inputLength`: monotone stage costs evaluated at `n = operandBits a b ≤ L` (the input
  bridge) are bounded by their value at `L`.

So W12 can take `T := c.total M`.

Statement status: `W10_cost` is stated, not proved. It is true; the argument is above. Owner: W10.
-/

namespace IntMulTM.Contracts.Top

open Computability

/-- Stage-cost functions of the composed program, as functions of the operand bit length `n`.
`ℓ` indexes pipeline levels (sweeps). -/
structure StageCosts where
  /-- copy-in, parse, schedule (W0m) -/
  input : ℕ → ℕ
  /-- table construction and serialization (W7) -/
  tables : ℕ → ℕ
  /-- root stage: split/pack, pointwise squaring, extraction, reconstruction (W9 root) -/
  root : ℕ → ℕ
  /-- copy-out and cleanup -/
  output : ℕ → ℕ
  /-- number of pipeline levels (sweeps) -/
  levels : ℕ → ℕ
  /-- work of level `ℓ` other than multiplications: routing, scans, table streaming (W4/W9) -/
  levelLin : ℕ → ℕ → ℕ
  /-- number of multiplications at level `ℓ` (W5/W6 calls) -/
  mulCount : ℕ → ℕ → ℕ
  /-- their width in bits -/
  mulWidth : ℕ → ℕ → ℕ

/-- Total source-level cost with multiplication cost function `M`. -/
def StageCosts.total (c : StageCosts) (M : ℕ → ℕ) (n : ℕ) : ℕ :=
  c.input n + c.tables n + c.root n + c.output n +
    ((List.range (c.levels n)).map fun ℓ => c.levelLin n ℓ + c.mulCount n ℓ * M (c.mulWidth n ℓ)).sum

/-- **Per-stage bounds** for the level-synchronous pipeline, one constant `A`, for `n ≥ 2`:
* input, tables, root and output together: `≤ A·n·log₂ n`;
* levels: `≤ A·(log₂ log₂ n + 1)`;
* non-multiplication work summed over levels: `≤ A·n·log₂ n` (charged routing `Θ(R0·E·K_ℓ)`
  with `Σ K_ℓ ≤ 2K0 + D`);
* per level: at most `A·n` multiplications, `A·n` multiplied bits in total, widths
  `≤ A·(log₂ n + 1)²`. -/
def StageBounds (c : StageCosts) (A : ℕ) : Prop :=
  ∀ n, 2 ≤ n →
    c.input n + c.tables n + c.root n + c.output n ≤ A * n * Nat.log2 n ∧
    c.levels n ≤ A * (Nat.log2 (Nat.log2 n) + 1) ∧
    ((List.range (c.levels n)).map fun ℓ => c.levelLin n ℓ).sum ≤ A * n * Nat.log2 n ∧
    ∀ ℓ < c.levels n, c.mulCount n ℓ ≤ A * n ∧ c.mulCount n ℓ * c.mulWidth n ℓ ≤ A * n ∧
      c.mulWidth n ℓ ≤ A * (Nat.log2 n + 1) ^ 2

/-- **Multiplication cost interface** (W5, ℕ form of `w^{3/2}/log₂ w`). -/
def MulBound (M : ℕ → ℕ) (CM : ℕ) : Prop :=
  (∀ w, 4 ≤ w → M w * Nat.log2 w ≤ CM * (w * Nat.sqrt w)) ∧ ∀ w < 4, M w ≤ CM

/-- `f n ≤ C·n·log₂ n` eventually. -/
def NLogN (f : ℕ → ℕ) : Prop := ∃ C N₀ : ℕ, ∀ n ≥ N₀, f n ≤ C * n * Nat.log2 n

/-- **W10_cost (pure arithmetic obligation; stated, owner W10).** Per-stage bounds and the W5
multiplication interface give an `O(n log n)` total. -/
def W10_cost : Prop :=
  ∀ (c : StageCosts) (A : ℕ), StageBounds c A →
    ∀ (M : ℕ → ℕ) (CM : ℕ), MulBound M CM → NLogN (c.total M)

/-- The form W12 consumes: the wrapper's `+ 1` is absorbed. -/
theorem nlogn_succ {f : ℕ → ℕ} (h : NLogN f) : ∃ C N₀ : ℕ, ∀ L ≥ N₀, f L + 1 ≤ C * L * Nat.log2 L :=
  TMFw.nlogn_add_one h

/-- Monotone stage costs measured at the operand bit length are bounded by their value at the input
length (input bridge: `operandBits a b ≤ |encNatPair (a, b)|`). -/
theorem cost_le_at_inputLength {f : ℕ → ℕ} (hf : Monotone f) (a b : ℕ) :
    f (operandBits a b) ≤ f (encNatPair.encode (a, b)).length :=
  hf (input_bridge a b).2.2.1

#assert_std_axioms nlogn_succ cost_le_at_inputLength

end IntMulTM.Contracts.Top
