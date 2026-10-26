import SubNLogN.Math.Bridge.RootPacking
import SubNLogN.Math.Bridge.Fnew
import Contracts.W9.Root

/-!
# Bridge: feeding Theorem 4.7 (`thm:bridge-precision`) into the W8/W9 root framework

Target: `RootOKSubNLogN F cSpec b K0 k1 k2 A1 A2 wd wR` for `F = F_newKR rr Kc ρ Tab mid` on its
bridge branch, i.e. for `F = FnewOfR rr ρ Tab mid` (`Fnew.lean`; `SubNLogN/S5/TopDispatcher.lean`,
`RootOKSubNLogN`) at `b = W8.hB n`, `K0 = W8.hK0 n`, `p0 = IntMul.rootPrecision b K0 = 2b + 2K0 + 6`, with
`wR = WP.W11b.wRHead n = 4·p0`.

The root stages are IntMul's integer stages (`Contracts/W9/Root.lean`):
* `rootPackV` packs the chunks as `(4a_j, 4b_j)`, i.e. `x_j = 2^{-b}(α_j + iβ_j)` at scale `2^{b+2}`;
* `rootSquareV p0` is `conj(round_{p0+2}(y²))`, with half-up rounding (`gMulScaled`);
* `rootDigits` is `-Im` shifted by 9;
* `reconstructChunksTree` does the carries.

Plan (Theorem 4.7 → `RootOKSubNLogN`):
1. On its input guard `ArrW (p0 + p_in + 1) x`, `FnewOfR rr ρ Tab mid p_in cSpec x` is
   `encode_{p0}(bridgeFixedR rr (decode_{p_in} x))` (`Fnew.lean`), at `p = p0`. The guard holds at both root calls (call 1: `|4a_j| < 2^{b+2}`; call 2: the
   numerators of `x1` are `≲ 2^{p0+7}`). Decoding at `p_in ∈ {b, p0}` puts both root inputs on the
   `(p0+2)`-grid, with norms `< √2` and `< 2.0001`, so Theorem 4.7 applies at `p = p0`
   (`p0 ≥ max(8, K0)`).
2. Exact recovery: the no-wrap argument of Proposition 7.2 with unequal supports (`k1`, `k2` chunks,
   `k1 + k2 ≤ 2^{K0}`), IntMul's half-up rounding, and the extraction
   `-Im·2^{2b+2K0-1} = -n_j/512` (shift 9); proved via `IntMul.dftApproxConvApprox_round_eq` (`Proofs/RootW8.lean`).
   (`RootPackingRndStmt` below is the equal-support form `N = k1 = k2`; that proof does not use it.)
3. Widths (`ArrW (4 p0)`) follow from the norm bounds:
   * bridge outputs: `‖ŷ‖ < √2 + 1`, so entries are `< 2^{p0+3}` at scale `2^{p0+2}`;
   * squares: `< 2.0001·2^{p0+2}`;
   * digits: `c_j ≤ N(2^b-1)² < 2^{2b+K0}`, so `bitLen ≤ 2b + K0 ≤ 4p0`.
4. `ChainOK` concerns the old radix-2 chain premise of `cSpec` on `x0` and `x1`. It is not about the
   bridge: derived from magnitude bounds via `WP.W11b.chainOK_of`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common SubNLogN.Math.Cost
open scoped BigOperators

/-- CONTRACT (Proposition 7.2, generalized; `prop:root-packing`): exact recovery for an arbitrary
nearest rounding `rnd` onto the `(p+2)`-grid (e.g. `quantC`, or IntMul's half-up rounding), with
`N` chunks per operand, `2N ≤ R = 2^{K0}`, and `p = 2b + 2K0 + 6` (`= IntMul.rootPrecision b K0`).
Hypotheses: `b ≥ 1` and `p ≥ 14` (Proposition 7.2 (`prop:root-packing`)). [Not used by the proof of
`RootW8_FnewStmt`, which handles unequal supports `k1 ≠ k2` directly.] -/
def RootPackingRndStmt : Prop :=
  ∀ (b K0 N A B : ℕ) (_hb : 1 ≤ b) (_hp : 14 ≤ 2 * b + 2 * K0 + 6) (_hN : 2 * N ≤ 2 ^ K0)
    (_hA : A < 2 ^ (b * N)) (_hB : B < 2 ^ (b * N)) (rnd : ℂ → ℂ)
    (_hrnd : ∀ z, OnGrid (2 * b + 2 * K0 + 8) (rnd z) ∧
      ‖rnd z - z‖ ≤ Real.sqrt 2 / 2 * gridUnit (2 * b + 2 * K0 + 8))
    (br : (Fin (2 ^ K0) → ℂ) → (Fin (2 ^ K0) → ℂ))
    (_hbr : BridgeContract (2 ^ K0) (2 * b + 2 * K0 + 6) br) (j : Fin (2 ^ K0)),
    rootCoeff b (br (fun u => star (rnd (br (rootInput b N A B) u * br (rootInput b N A B) u)))) j =
      ∑ a ∈ Finset.range ((j : ℕ) + 1), ((digit b A a * digit b B ((j : ℕ) - a) : ℕ) : ℤ)

/-- CONTRACT (Theorem 4.7 + Proposition 7.2 at the W8 root parameters, for `FnewOfR rr`).
Hypotheses:
* `b ≥ 1`, `k1 + k2 ≤ 2^{K0}`, `A1 < 2^{b k1}`, `A2 < 2^{b k2}`;
* `cSpec.p = p0 = IntMul.rootPrecision b K0`, and `WalshOK ρ p0 K0`;
* the tables `Tab p0 K0` are certified (`TablesCertifiedR rr`) at
  `α = alphaDefault (schedOmega p0 K0 d)` and
  `P = schedP p0 K0`;
* `mid p0 K0` is a middle transform (Definition 4.5) at `P = schedP p0 K0`.

Then, for `F = FnewOfR rr ρ Tab mid`, the non-`ChainOK` conjuncts of `RootOKSubNLogN`
(`SubNLogN/S5/TopDispatcher.lean`) hold with `wR = 4 p0`:
* sizes `2^{K0}`;
* the decoded outputs have modulus `≤ 4` (from which assembly derives `ChainOK` via `root_parts`,
  `WP/W11b/Root.lean`);
* entry widths `≤ 4 p0` for `x0, yF, x1, yI`, and digit widths `≤ 4 p0`;
* exact recovery `reconstructChunksTree b (rootDigits b K0 k1 k2 yI) = A1 * A2`.

Proof route: the input guard holds at both calls; `Bridge_precisionStmt` at `p = p0` for both
calls (inputs on the `(p0+2)`-grid, norms `< √2` and `< 2.0001`); exact recovery by the no-wrap
argument with unequal supports (`IntMul.dftApproxConvApprox_round_eq`) and IntMul's half-up
rounding; then IntMul's carries; widths from the norm bounds.
Stated for every nearest rounding `rr` (`IsNearestRounding rr`, `Common/RoundNearest.lean`). -/
def RootW8_FnewStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ (ρ : RowExps) (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ))
    (b K0 k1 k2 A1 A2 : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (_hb : 1 ≤ b)
    (_hk : k1 + k2 ≤ 2 ^ K0) (_hA1 : A1 < 2 ^ (b * k1)) (_hA2 : A2 < 2 ^ (b * k2))
    (_hp : cSpec.p = IntMul.rootPrecision b K0)
    (_hOK : WalshOK ρ (IntMul.rootPrecision b K0) K0 = true)
    (_hT : TablesCertifiedR rr
      (alphaDefault (schedOmega (IntMul.rootPrecision b K0) K0 (fnewD ρ K0 + 1)))
      (schedP (IntMul.rootPrecision b K0) K0) (fnewShape ρ K0)
      (Tab (IntMul.rootPrecision b K0) K0))
    (Emid : ℝ) (δmid : ℕ)
    (_hmid : IsMiddleTransform (fnewShape ρ K0) (schedP (IntMul.rootPrecision b K0) K0) Emid
      δmid (mid (IntMul.rootPrecision b K0) K0)),
    let p0 := IntMul.rootPrecision b K0
    let F := FnewOfR rr ρ Tab mid
    let x0 := TMFw.Contracts.W9.rootPackV b K0 k1 k2 A1 A2
    let yF := F b cSpec x0
    let x1 := TMFw.Contracts.W9.rootSquareV p0 K0 yF
    let yI := F p0 cSpec x1
    yF.size = 2 ^ K0 ∧ yI.size = 2 ^ K0 ∧
      (∀ u < 2 ^ K0, ‖IntMul.toScaledComplex p0 (IntMul.read1D yF u)‖ ≤ 4) ∧
      (∀ u < 2 ^ K0, ‖IntMul.toScaledComplex p0 (IntMul.read1D yI u)‖ ≤ 4) ∧
      TMFw.Contracts.W9.ArrW (4 * p0) x0 ∧ TMFw.Contracts.W9.ArrW (4 * p0) yF ∧
      TMFw.Contracts.W9.ArrW (4 * p0) x1 ∧ TMFw.Contracts.W9.ArrW (4 * p0) yI ∧
      (∀ c ∈ TMFw.Contracts.W9.rootDigits b K0 k1 k2 yI, TMFw.Contracts.bitLen c ≤ 4 * p0) ∧
      IntMul.reconstructChunksTree b (TMFw.Contracts.W9.rootDigits b K0 k1 k2 yI) = A1 * A2

end SubNLogN.Math.Bridge
