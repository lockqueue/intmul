import SubNLogN.Math.Bridge.Precision

/-!
# Bridge: Proposition 7.2, two-call root packing and exact recovery (`prop:root-packing`)

Proposition 7.2 uses the bridge only through the contract of Theorem 4.7 (`BridgeContract`), so it is
stated for an arbitrary bridge procedure `br`. `bridgeFixed_contract` instantiates it with
`bridgeFixed`. The cost clause of Proposition 7.2 (`O(R M(P) + n)` outside the bridge calls) is proved in `SubNLogN/Math/Cost/`.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

/-! ## Root parameters (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)) -/

/-- `b = ⌊log₂ n⌋`. -/
def rootB (n : ℕ) : ℕ := Nat.log 2 n

/-- `N_dig = ⌈n/b⌉`. -/
def rootNdig (n : ℕ) : ℕ := (n + rootB n - 1) / rootB n

/-- `k`, where `R = 2^k` is the least power of two with `R ≥ 2 N_dig`. -/
def rootK (n : ℕ) : ℕ := Nat.clog 2 (2 * rootNdig n)

/-- `p = 2b + 2k + 6` (eq. (`eq:root-sizes`)). -/
def rootP (n : ℕ) : ℕ := 2 * rootB n + 2 * rootK n + 6

/-- The radix-`2^b` digit `j` of `A`. -/
def digit (b A j : ℕ) : ℕ := (A / 2 ^ (b * j)) % 2 ^ b

/-- The conclusion of Theorem 4.7 as a contract on a length-`R` bridge procedure at precision `p`: for
every `x` on the `(p+2)`-grid with `‖x‖_∞ ≤ 2^p`, the output lies on the `(p+2)`-grid and is
within `0.177021·2^{-p} max(1,‖x‖_∞)` of `F_R x`. -/
def BridgeContract (R p : ℕ) (br : (Fin R → ℂ) → (Fin R → ℂ)) : Prop :=
  ∀ x : Fin R → ℂ, (∀ j, OnGrid (p + 2) (x j)) → ‖x‖ ≤ (2 : ℝ) ^ p →
    (∀ f, OnGrid (p + 2) (br x f)) ∧
      ‖br x - dft R x‖ < 0.177021 * (2 : ℝ) ^ (-(p : ℤ)) * max 1 ‖x‖

/-- The packed input `x_j = 2^{-b}(α_j + iβ_j)` for `j < N_dig`, `0` otherwise (Proposition 7.2 (`prop:root-packing`)). -/
noncomputable def rootInput {R : ℕ} (b N A B : ℕ) : Fin R → ℂ :=
  fun j => if (j : ℕ) < N then
    (((digit b A j : ℕ) : ℂ) + ((digit b B j : ℕ) : ℂ) * Complex.I) / (2 : ℂ) ^ b else 0

/-- `ŵ = conj(Quant_{p+2}(ŷ ⊙ ŷ))` (Proposition 7.2 (`prop:root-packing`)). -/
noncomputable def rootSquare {R : ℕ} (p : ℕ) (y : Fin R → ℂ) : Fin R → ℂ :=
  fun u => star (quantC (p + 2) (y u * y u))

/-- `c_j = round(-2^{2b-1} R² Im ẑ_j)` (Proposition 7.2 (`prop:root-packing`)). -/
noncomputable def rootCoeff {R : ℕ} (b : ℕ) (z : Fin R → ℂ) (j : Fin R) : ℤ :=
  round (-((2 : ℝ) ^ (2 * b) / 2 * (R : ℝ) ^ 2 * (z j).im))

/-- Carries `C_0 = 0`, `C_{j+1} = ⌊(c_j + C_j)/2^b⌋` (Proposition 7.2 (`prop:root-packing`)). -/
def carrySeq (b : ℕ) (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (c j + carrySeq b c j) / 2 ^ b

/-- Output digits `D_j = (c_j + C_j) mod 2^b` (Proposition 7.2 (`prop:root-packing`)). -/
def carryDigit (b : ℕ) (c : ℕ → ℕ) (j : ℕ) : ℕ := (c j + carrySeq b c j) % 2 ^ b

/-! ## Contracts -/

/-- CONTRACT, Proposition 7.2 (`prop:root-packing`): for large `n`, inputs `A, B < 2^n`,
`R = 2^k` and any bridge `br`
satisfying the contract of Theorem 4.7 at precision `p`, the two-call root packing recovers every
coefficient exactly:
`round(-2^{2b-1}R² Im ẑ_j) = ∑_{a+b'=j} α_a β_{b'}`, with `ŷ = br x`, `ŵ = conj(Quant_{p+2}(ŷ⊙ŷ))`,
`ẑ = br ŵ`.
[Interpretation: "large n" (Section 7.1 (`sec:main-alg`)) is used in the proof of Proposition 7.2 only for
`p ≥ 14` (`prop:root-packing`) ("as p ≥ 14"), plus `b ≥ 1`. We take `n ≥ 16`: then `b = ⌊log₂ n⌋ ≥ 4`,
`k ≥ 1`, `p = 2b+2k+6 ≥ 16 ≥ 14`, and `p ≥ max(8,k)` as Theorem 4.7 requires.] -/
def Root_packingStmt : Prop :=
  ∀ (n : ℕ) (_hn : 16 ≤ n) (A B : ℕ) (_hA : A < 2 ^ n) (_hB : B < 2 ^ n) (R : ℕ) (_hR : R = 2 ^ rootK n) (br : (Fin R → ℂ) → (Fin R → ℂ)) (_hbr : BridgeContract R (rootP n) br) (j : Fin R),
    rootCoeff (rootB n)
        (br (rootSquare (rootP n) (br (rootInput (rootB n) (rootNdig n) A B)))) j =
      ∑ a ∈ Finset.range ((j : ℕ) + 1),
        ((digit (rootB n) A a * digit (rootB n) B ((j : ℕ) - a) : ℕ) : ℤ)

/-- CONTRACT (Proposition 7.2 (`prop:root-packing`)): the coefficients satisfy
`0 ≤ c_j ≤ N_dig (2^b - 1)²`, and since `2N_dig - 1 ≤ R` there is no cyclic wrap:
`A·B = ∑_{j<R} c_j 2^{bj}`. -/
def Root_coeffs_evalStmt : Prop :=
  ∀ (n : ℕ) (_hn : 16 ≤ n) (A B : ℕ) (_hA : A < 2 ^ n) (_hB : B < 2 ^ n),
    (∀ j, ∑ a ∈ Finset.range (j + 1), digit (rootB n) A a * digit (rootB n) B (j - a) ≤
        rootNdig n * (2 ^ rootB n - 1) ^ 2) ∧
      A * B = ∑ j ∈ Finset.range (2 ^ rootK n),
        (∑ a ∈ Finset.range (j + 1), digit (rootB n) A a * digit (rootB n) B (j - a)) *
          2 ^ (rootB n * j)

/-- CONTRACT (Proposition 7.2 (`prop:root-packing`)): carry propagation in radix `2^b` is exact:
`∑_{j<M} D_j 2^{bj} + C_M 2^{bM} = ∑_{j<M} c_j 2^{bj}`, and every `D_j < 2^b`. -/
def Carry_propagationStmt : Prop :=
  ∀ (b : ℕ) (c : ℕ → ℕ) (M : ℕ),
    (∑ j ∈ Finset.range M, carryDigit b c j * 2 ^ (b * j) + carrySeq b c M * 2 ^ (b * M) =
      ∑ j ∈ Finset.range M, c j * 2 ^ (b * j)) ∧ ∀ j, carryDigit b c j < 2 ^ b

/-- CONTRACT (Proposition 7.2 (`prop:root-packing`)): the product is below `2^{2n}`, so exactly `2n` output bits
are emitted. -/
def Product_ltStmt : Prop :=
  ∀ (n A B : ℕ) (_hA : A < 2 ^ n) (_hB : B < 2 ^ n),
    A * B < 2 ^ (2 * n)

/-- CONTRACT (Theorem 4.7 ⟹ the contract used by Proposition 7.2): under the hypotheses of Theorem 4.7,
`bridgeFixedR rr` satisfies `BridgeContract`.
Stated for every nearest rounding `rr` (`IsNearestRounding rr`, `Common/RoundNearest.lean`). -/
def BridgeFixed_contractStmt : Prop :=
  ∀ (rr : ℕ → ℝ → ℝ), IsNearestRounding rr →
  ∀ {d : ℕ} (t : Fin d → ℕ) (k ℓ p : ℕ) (_hshape : BalancedShape t k ℓ) (_hp : max 8 k ≤ p) (T : BridgeTables t) (_hT : TablesCertifiedR rr (alphaDefault (schedOmega p k d)) (schedP p k) t T) (Emid : ℝ) (δmid : ℕ) (run : (Idx t → ℂ) → (Idx t → ℂ)) (_hmid : IsMiddleTransform t (schedP p k) Emid δmid run),
    BridgeContract (totalLen t) p (bridgeFixedR rr p (schedP p k) t T run)

end SubNLogN.Math.Bridge
