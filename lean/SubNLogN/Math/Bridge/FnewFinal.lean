import SubNLogN.Math.Bridge.TablesConcrete
import SubNLogN.Math.Bridge.RootW8
import SubNLogN.Math.Walsh.Middle

/-!
# Bridge: the closed transform map (final instantiation of `F_newK`)

`F_newConcreteK Kc ρ = F_newKR roundHalfUpR Kc ρ (TabConcreteR roundHalfUpR ρ) (walshMid ρ)`:
* the guard is `WalshOK ρ p0 K0 && decide (Kc ≤ K0)` (`Fnew.lean`);
  the cutoff `Kc` is a parameter chosen by the top-level assembly
  (`F_newConcrete ρ` is the instance `Kc = KstarOf ρ`);
* every nearest rounding of the bridge and of the tables is `roundHalfUpR` (ties toward `+∞`, the
  machine's rounding; `isNearestRounding_roundHalfUpR`);
* the bridge `FnewOfR roundHalfUpR` checks the input guard `ArrW (p0 + p_in + 1) x` first;
* the concrete certified tables `TabConcreteR roundHalfUpR` (`TablesConcrete.lean`, certified
  on the machine);
* the Walsh middle with the ideal layer: `walshMid ρ p0 K0 =
  walshMiddle idealLayer (schedP p0 K0 + 2) (fnewD ρ K0) (fnewL ρ K0) (KK ρ K0) (fnewA ρ K0)`.
  At the value level the layer is `idealLayer` (LayerSpec by `rfl`). Proposition A.11 is needed only at
  machine level, where the TM must compute `idealLayer` at the call shapes.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common SubNLogN.Math.Cost

/-- The Walsh middle (Corollary 6.6 procedure) at grid precision `q = schedP p0 K0 + 2` with the ideal
layer, on the shape `fnewShape ρ K0` (definitionally `fftShape (fnewA ρ K0) (fnewL ρ K0)`). -/
noncomputable def walshMid (ρ : RowExps) (p0 K0 : ℕ) :
    (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ) :=
  SubNLogN.Math.Walsh.walshMiddle SubNLogN.Math.Walsh.idealLayer (schedP p0 K0 + 2) (fnewD ρ K0)
    (fnewL ρ K0) (KK ρ K0) (fnewA ρ K0)

/-- The closed transform map for row `ρ` (intended `ρ = Cost.row46`) with cutoff `Kc`: rounding
`roundHalfUpR`, tables `TabConcreteR roundHalfUpR ρ`, middle `walshMid ρ`. -/
noncomputable def F_newConcreteK (Kc : ℕ) (ρ : RowExps) :
    ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ) :=
  F_newKR roundHalfUpR Kc ρ (TabConcreteR roundHalfUpR ρ) (walshMid ρ)

/-- The closed transform map at the cutoff `Kc = KstarOf ρ` (the final assembly may use a larger
cutoff, i.e. `F_newConcreteK Kc ρ` with `KstarOf ρ ≤ Kc`). -/
noncomputable def F_newConcrete (ρ : RowExps) :
    ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ) :=
  F_newConcreteK (KstarOf ρ) ρ

theorem F_newConcrete_eq_K (ρ : RowExps) : F_newConcrete ρ = F_newConcreteK (KstarOf ρ) ρ := rfl

/-- CONTRACT (final; Theorem 4.7 + Proposition 7.2 for the closed `F_newConcreteK`, bridge branch): the
non-`ChainOK` conjuncts of `RootOKSubNLogN` (`SubNLogN/S5/TopDispatcher.lean`, `wR = 4 p0`)
hold for `F = F_newConcreteK Kc ρ`. Hypotheses: `b ≥ 1`, `k1 + k2 ≤ 2^{K0}`, `A_i < 2^{b k_i}`,
`cSpec.p = p0 = IntMul.rootPrecision b K0`, the cutoff `Kc ≤ K0` and eligibility
`WalshOK ρ p0 K0 = true`, so both calls take the bridge branch. There are no table or layer
hypotheses: the tables are `TabConcreteR roundHalfUpR` and the layer is `idealLayer`. (The
radix-2 branch is covered by the existing IntMul root proof; that case split is the assembly's
dispatch.)
Derivation route:
* `F_newKR_eq_FnewOfR` for both calls (`x0`, `x1` have size `2^{K0}`, so `log₂` of the size is
  `K0`);
* `RootW8_FnewStmt` at `rr = roundHalfUpR` (`isNearestRounding_roundHalfUpR`) with
  `Tab = TabConcreteR roundHalfUpR ρ` and `mid = walshMid ρ`;
* `TabConcrete_certifiedStmt` at `rr = roundHalfUpR` for the tables;
* `Walsh.walsh_middle_ideal` (Corollary 6.6 for `idealLayer`, proved in `Walsh/Proofs/Wiring.lean`) for
  the middle. Its side conditions `8 ≤ q`, `1 ≤ D`, `2 ≤ ℓ < q`, `1 ≤ K ≤ ℓ - 1` and
  `a_i ∈ {ℓ-1, ℓ}` follow from `WalshOK`. -/
def FnewConcreteK_rootStmt : Prop :=
  ∀ (Kc : ℕ) (ρ : RowExps) (b K0 k1 k2 A1 A2 : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (_hb : 1 ≤ b) (_hk : k1 + k2 ≤ 2 ^ K0) (_hA1 : A1 < 2 ^ (b * k1)) (_hA2 : A2 < 2 ^ (b * k2))
    (_hp : cSpec.p = IntMul.rootPrecision b K0) (_hK : Kc ≤ K0)
    (_hOK : WalshOK ρ (IntMul.rootPrecision b K0) K0 = true),
    let p0 := IntMul.rootPrecision b K0
    let F := F_newConcreteK Kc ρ
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

/-- CONTRACT (Theorem 4.7 + Proposition 7.2 for `F_newConcrete`, the instance `Kc = KstarOf ρ`): the
non-`ChainOK` conjuncts of `RootOKSubNLogN` (`SubNLogN/S5/TopDispatcher.lean`,
`wR = 4 p0`) hold for `F = F_newConcrete ρ`. Hypotheses: `b ≥ 1`, `k1 + k2 ≤ 2^{K0}`,
`A_i < 2^{b k_i}`,
`cSpec.p = p0 = IntMul.rootPrecision b K0`, the cutoff `KstarOf ρ ≤ K0` (so both calls take the
bridge branch) and eligibility `WalshOK ρ p0 K0 = true`. (At the W8 root parameters with
`ρ = row46`, eligibility follows from the cutoff by `Kstar_spec_of`, given
`WalshOK_eventuallyStmt`.) There are no table or layer hypotheses: the tables are
`TabConcreteR roundHalfUpR` and the layer is `idealLayer`. It follows from
`FnewConcreteK_rootStmt` at `Kc = KstarOf ρ` (`fnewConcrete_root_of_K`). -/
def FnewConcrete_rootStmt : Prop :=
  ∀ (ρ : RowExps) (b K0 k1 k2 A1 A2 : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (_hb : 1 ≤ b) (_hk : k1 + k2 ≤ 2 ^ K0) (_hA1 : A1 < 2 ^ (b * k1)) (_hA2 : A2 < 2 ^ (b * k2))
    (_hp : cSpec.p = IntMul.rootPrecision b K0) (_hK : KstarOf ρ ≤ K0)
    (_hOK : WalshOK ρ (IntMul.rootPrecision b K0) K0 = true),
    let p0 := IntMul.rootPrecision b K0
    let F := F_newConcrete ρ
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

/-- `FnewConcrete_rootStmt` is the instance `Kc = KstarOf ρ` of `FnewConcreteK_rootStmt`. -/
theorem fnewConcrete_root_of_K (h : FnewConcreteK_rootStmt) : FnewConcrete_rootStmt :=
  fun ρ b K0 k1 k2 A1 A2 cSpec hb hk hA1 hA2 hp hK hOK =>
    h (KstarOf ρ) ρ b K0 k1 k2 A1 A2 cSpec hb hk hA1 hA2 hp hK hOK

end SubNLogN.Math.Bridge
