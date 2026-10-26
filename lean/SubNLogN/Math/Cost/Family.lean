import Mathlib
import SubNLogN.Math.Cost.Params

/-!
# Cost: root-parameter families

`Params.lean` fixes the paper's root family (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)): `b = ⌊log₂ n⌋`,
`N_dig = ⌈n/b⌉`, `R = 2^k` the least power of two `≥ 2 N_dig`. The machine layer instead runs the
transform at the W8 root parameters of the existing IntMul framework (Section 8 (`sec:lean`), Departures (1);
`Contracts/W8.lean`): `b = max 1 ⌊log₂ n⌋`, `⌊n/b⌋ + 1` chunks and
`k := K0 = max 4 (⌊log₂(2·chunks)⌋ + 2)` (so `R = 2^{K0}` is at most `4` times the paper's `R`;
constants only). This file makes the cost parameters functions of `(b, k)` so that the cost
theorem can be stated for any family `n ↦ (b n, k n)`:

* `pBK, PBK, qBK, VBK` (functions of `(b, k)`) and `dK, lK, rK, KK` (functions of `k` and the row);
  the `Params` functions are these at `(bOf n, kOf n)`, definitionally (`POf_eq_PBK`, ...);
* `BandsK ρ P' k`: the bands of Lemma 7.1 (eq. (`eq:bands`)) at `k`; `Bands ρ P' n` (`Asymptotics`) is
  definitionally `BandsK ρ P' (kOf n)`;
* `FamFacts b k`: the four growth facts of a family used by the cost theorem (`k → ∞`,
  `16k ≤ P ≤ 64k`, `V = O(n)`, `P = O(log n)` eventually);
* the W8 family `w8B`, `w8N`, `w8K` (equal to `W8.hB`, `W8.hK`, `W8.hK0` by `rfl`; the link is
  made in `SubNLogN/Assembly`, which imports both).

This file contains definitions and definitional equalities only (no `sorry`).
-/

namespace SubNLogN.Math.Cost

open Filter

/-! ## Parameters as functions of `(b, k)` -/

/-- `p = 2b + 2k + 6` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)), at `(b, k)`. Equal to `IntMul.rootPrecision b k`. -/
def pBK (b k : ℕ) : ℕ := 2 * b + 2 * k + 6

/-- `P = 2p + 12k + 32⌈lg(p+k+2)⌉ + 256` (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:schedule`)), at `(b, k)`. -/
def PBK (b k : ℕ) : ℕ := 2 * pBK b k + 12 * k + 32 * Nat.clog 2 (pBK b k + k + 2) + 256

/-- `q = P + 2` (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:schedule`)), at `(b, k)`. -/
def qBK (b k : ℕ) : ℕ := PBK b k + 2

/-- The volume `V = RP = 2^k P` (Section 7.3 (`sec:main-tables`)), at `(b, k)`. -/
def VBK (b k : ℕ) : ℕ := 2 ^ k * PBK b k

/-- `d = ⌊k^ε⌋` by integer comparison (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)), at `k`. -/
def dK (ρ : RowExps) (k : ℕ) : ℕ := floorRatPow k ρ.e₁ ρ.e₂

/-- `ℓ = ⌈k/d⌉` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)), at `k`. -/
def lK (ρ : RowExps) (k : ℕ) : ℕ := (k + dK ρ k - 1) / dK ρ k

/-- `r = 2^ℓ` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)), at `k`. -/
def rK (ρ : RowExps) (k : ℕ) : ℕ := 2 ^ lK ρ k

/-- `K = ⌊d^c⌋` by integer comparison (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)), at `k`. -/
def KK (ρ : RowExps) (k : ℕ) : ℕ := floorRatPow (dK ρ k) ρ.c₁ ρ.c₂

theorem pOf_eq_pBK (n : ℕ) : pOf n = pBK (bOf n) (kOf n) := rfl
theorem POf_eq_PBK (n : ℕ) : POf n = PBK (bOf n) (kOf n) := rfl
theorem qOf_eq_qBK (n : ℕ) : qOf n = qBK (bOf n) (kOf n) := rfl
theorem ROf_eq_pow (n : ℕ) : ROf n = 2 ^ kOf n := rfl
theorem VOf_eq_VBK (n : ℕ) : VOf n = VBK (bOf n) (kOf n) := rfl
theorem dOf_eq_dK (ρ : RowExps) (n : ℕ) : dOf ρ n = dK ρ (kOf n) := rfl
theorem lOf_eq_lK (ρ : RowExps) (n : ℕ) : lOf ρ n = lK ρ (kOf n) := rfl
theorem rOf_eq_rK (ρ : RowExps) (n : ℕ) : rOf ρ n = rK ρ (kOf n) := rfl
theorem KOf_eq_KK (ρ : RowExps) (n : ℕ) : KOf ρ n = KK ρ (kOf n) := rfl

/-- `PBK b k ≥ 256` (so `2 ≤ P` always). -/
theorem le_PBK (b k : ℕ) : 256 ≤ PBK b k := by
  unfold PBK; omega

/-! ## Bands at `k` -/

/-- The bands of Lemma 7.1 at a precision `P'` and transform exponent `k` (Lemma 7.1 (`lem:root-family`), eq. (`eq:bands`)
with `a_d = 1/4`, `b_d = 1`, `a_r = 1/128`, `b_r = 1/8`, `C_ℓ = 1`; proof of Lemma 7.1 (`lem:root-family`)):
`¼P'^ε ≤ d ≤ P'^ε`, `P'/(128d) ≤ ℓ ≤ P'/(8d)`, `dℓ ≤ P'` and `k - ℓ ≤ P'`, with `d = dK ρ k`,
`ℓ = lK ρ k`. -/
def BandsK (ρ : RowExps) (P' k : ℕ) : Prop :=
  (1 / 4 : ℝ) * (P' : ℝ) ^ ρ.eps ≤ dK ρ k ∧ (dK ρ k : ℝ) ≤ (P' : ℝ) ^ ρ.eps ∧
    (P' : ℝ) / (128 * dK ρ k) ≤ lK ρ k ∧ (lK ρ k : ℝ) ≤ (P' : ℝ) / (8 * dK ρ k) ∧
    dK ρ k * lK ρ k ≤ P' ∧ k - lK ρ k ≤ P'

/-! ## Growth facts of a family -/

/-- The growth facts of a root-parameter family `n ↦ (b n, k n)` used by the cost theorem
(Lemma 7.1 (`lem:root-family`) for the paper family): `k → ∞`; eventually `16k ≤ P ≤ 64k` (`P = PBK (b n) (k n)`);
`V = 2^k P = O(n)` and `P = O(⌊log₂ n⌋)` (explicit but unspecified real constants). -/
structure FamFacts (b k : ℕ → ℕ) : Prop where
  /-- `k → ∞` -/
  tendsto_k : Tendsto k atTop atTop
  /-- eventually `16 k ≤ P ≤ 64 k` -/
  P_band : ∀ᶠ n in atTop, 16 * k n ≤ PBK (b n) (k n) ∧ PBK (b n) (k n) ≤ 64 * k n
  /-- `V = O(n)` -/
  V_le : ∃ cV : ℝ, ∀ᶠ n in atTop, (VBK (b n) (k n) : ℝ) ≤ cV * n
  /-- `P = O(⌊log₂ n⌋)` -/
  P_log : ∃ cP : ℝ, ∀ᶠ n in atTop, (PBK (b n) (k n) : ℝ) ≤ cP * (Nat.log2 n : ℝ)

/-! ## The W8 family (the machine's root parameters) -/

/-- W8 digit width `b = max 1 ⌊log₂ n⌋` (`W8.hB`, `Contracts/W8.lean`). -/
def w8B (n : ℕ) : ℕ := max 1 (Nat.log2 n)

/-- W8 chunk count `⌊n/b⌋ + 1` (`W8.hK`, `Contracts/W8.lean`). -/
def w8N (n : ℕ) : ℕ := n / w8B n + 1

/-- W8 transform exponent `K0 = max 4 (⌊log₂(2·chunks)⌋ + 2)` (`W8.hK0`, `Contracts/W8.lean`);
`R = 2^{K0}`. -/
def w8K (n : ℕ) : ℕ := max 4 (Nat.log2 (2 * w8N n) + 2)

end SubNLogN.Math.Cost
