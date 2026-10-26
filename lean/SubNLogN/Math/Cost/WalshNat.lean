import Mathlib
import SubNLogN.Math.Cost.Family

/-!
# Cost: the Walsh-route cost expression with natural-number values (machine interface)

Machine step counts are natural numbers, so the machine layer (`SubNLogN.Machine`) states its cost bound with
the ℕ-valued version `walshCostNatBK` of the paper's cost expression (Section 7.2, eq. (`eq:root-cost`),
Section 7.3, eq. (`eq:setup`), Section 7.3, eq. (`eq:cost-W`); real version `walshCostBK` in `WalshCore.lean`),
in which the real powers `d^{λ'}` and `ℓ^τ` are rounded up (`⌈·⌉₊`) and the per-bit
multiplication-cost envelope `m : ℕ → ℕ` is natural-valued. `walshCostNatW8` is its instance at the W8
root parameters (`b = w8B n`, `k = w8K n`), the parameters at which the machine runs `F_newKR roundHalfUpR Kc`.
`m` is an upper-bound envelope: the machine analysis charges each framed multiplier call at
its actual operand widths by one fixed majorant `M̄(N) = A·N·(lg 2N)^J` (entry, framing,
conversion and cleanup included), bounded by `N·m(N')` for the widths `N ≤ N'` occurring here.

This file contains definitions only (no `sorry`); the conversion to `HeadlineCost` is
`headlineCost_walshNat46_W8` (`WalshW8.lean`).
-/

namespace SubNLogN.Math.Cost

/-- ℕ-valued Walsh-route cost expression at `(b, k)` and input length `n`:
`V·[dK + ℓ⌈d^{λ'}⌉ + ℓ·m(P) + d(1 + ⌈ℓ^τ⌉) + d(m(P) + m(P²))] + V·m(P) + n
  + (2^k/r)·P^{D_set} + r·P^{D_set} + P^{D_set}`,
with `V = VBK b k = 2^k P`, `P = PBK b k`, `d = dK ρ k`, `ℓ = lK ρ k`, `K = KK ρ k`, `r = rK ρ k`
(the expression of `walshCost`, `Walsh46.lean`, with real powers rounded up). -/
noncomputable def walshCostNatBK (ρ : RowExps) (lam' tau : ℝ) (m : ℕ → ℕ) (Dset b k n : ℕ) : ℕ :=
  VBK b k * (dK ρ k * KK ρ k + lK ρ k * ⌈(dK ρ k : ℝ) ^ lam'⌉₊ + lK ρ k * m (PBK b k)
      + dK ρ k * (1 + ⌈(lK ρ k : ℝ) ^ tau⌉₊) + dK ρ k * (m (PBK b k) + m (PBK b k ^ 2)))
    + VBK b k * m (PBK b k) + n
    + (2 ^ k / rK ρ k * PBK b k ^ Dset + rK ρ k * PBK b k ^ Dset + PBK b k ^ Dset)

/-- `walshCostNatBK` at the W8 root parameters `b = w8B n` (`= W8.hB n`), `k = w8K n`
(`= W8.hK0 n`). -/
noncomputable def walshCostNatW8 (ρ : RowExps) (lam' tau : ℝ) (m : ℕ → ℕ) (Dset n : ℕ) : ℕ :=
  walshCostNatBK ρ lam' tau m Dset (w8B n) (w8K n) n

end SubNLogN.Math.Cost
