import SubNLogN.Math.Bridge.Algorithm
import SubNLogN.Math.Cost.Family
import IntMul.MaterializedAndComputable.PaperHeadlinePipeline
import Contracts.W9.Common

/-!
# Bridge: the integer transform maps `FnewOfR` and `F_newKR` (interface file)

`F_newKR rr Kc ρ Tab mid p_in cSpec x :=
   if (WalshOK ρ p0 K0 && decide (Kc ≤ K0)) = true then FnewOfR rr ρ Tab mid p_in cSpec x
   else IntMul.computablePaperFastDFT p_in cSpec x`,
with `p0 = cSpec.p` and `K0 = log₂ x.size`. This is the final transform shape: the shape-and-band
guard `WalshOK` plus a cutoff parameter `Kc`, and the bridge's nearest
rounding `rr : ℕ → ℝ → ℝ` as a parameter (`Common/RoundNearest.lean`). The closed map
`F_newConcreteK` of `FnewFinal.lean` uses `rr = roundHalfUpR`.

* The branch depends only on `(p0, K0)` (and the constant `Kc`), which are the same in the forward
  and inverse calls of the root (`RootOKSubNLogN`) when both inputs have size `2^{K0}`, so both
  calls take the same branch. It does not depend on `p_in`.
* The bridge branch is taken only under `WalshOK`, so the root contracts can hold for every `Kc`;
  the final assembly picks `Kc` large enough for the machine kernels.
* `KstarOf ρ` is a fixed constant (noncomputable): the least `K` such that
  `WalshOKProp ρ (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n)` holds for every `n` with
  `K ≤ w8K n` (`sInf`; it is `0` if there is no such `K`). `Kstar = KstarOf row46`.
  `Kstar_spec_of` proves, assuming `WalshOK_eventuallyStmt`, that `Kstar ≤ w8K n` implies
  `WalshOKProp row46 (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n)`; hence on W8 root inputs
  with `Kstar ≤ Kc` the guard of `F_newKR rr Kc row46` reduces to `Kc ≤ K0`
  (`F_newKR_row46_eq_cutoff`).
* `FnewOfR rr` first checks the input guard `ArrW (p0 + p_in + 1) x` (the W9 width predicate:
  both coordinates `u` of every entry have `bitLen |u| ≤ p0 + p_in + 1`; this width guard
  implies Theorem 4.7's norm precondition `‖x‖_∞ ≤ 2^{p0}` at
  scale `2^{-(p_in+2)}`). Off the guard it returns `x.map (fun _ => (0, 0))`. On the guard it
  decodes the input at `p_in` (IntMul fixed point: `(u + iv)·2^{-(p_in+2)}`) and runs
  `bridgeFixedR rr` at target precision `p = p0` (working precision `P = schedP p0 K0`). The shape
  is the balanced shape of Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`): `d = dK ρ K0` (rational power by integer
  comparison), `ℓ = ⌈K0/d⌉`, and `d ℓ - K0` axes of length `r/2`, the short axes first, then
  `r = 2^ℓ` axes. The output is encoded at `p0 + 2` fractional bits, the scale at which
  `rootSquareV`/`rootExtractV` read it.
* The table family `Tab` and the middle `mid` are parameters (functions of `(p0, K0)`). The
  intended middle is `Walsh.walshMiddle layer (P+2) D ℓ K a`. `fnewShape ρ K0` is
  definitionally `Walsh.fftShape (fnewA ρ K0) (fnewL ρ K0)`, so that instantiation typechecks.
* `WalshOKProp` (Boolean form `WalshOK`) is a shape-and-band test at `(p0, K0)`: bounds on
  `d, ℓ, K, p0, q` and the integer bands `BandsNat` at `q` and `q + 8d`. Its eventual truth at the
  W8 parameters is `WalshOK_eventuallyStmt`. It is a conjunct of the guard of `F_newKR` and a
  hypothesis of the correctness contracts (`RootW8_FnewStmt`, `TabConcrete_certifiedStmt`,
  `WalshOK_balancedStmt`). It is not the full fast-kernel cutoff: tape thresholds and the layer
  guard live in the machine/pipe obligations, hence the separate cutoff `Kc`.
* Legacy `quantR` specializations retained for compatibility with `Machine/Pipe/Contract.lean`
  (prefer the `rr`-parametric `FnewOfR` and `F_newKR` above):
  `FnewOf ρ Tab mid` (the `quantC` bridge map `bridgeFixed` without the input width guard),
  `F_newK Kc ρ Tab mid` (guard `WalshOK && Kc ≤ K0`, bridge `FnewOf`), and `F_new ρ Tab mid`
  (guard `WalshOK` without the explicit cutoff `Kc`, bridge `FnewOf`).
  [Implementation note: on machines, `KK ρ K0 = ⌊d^c⌋` with `c = 2^{-50}` is decided by bit-length
  bounds rather than by evaluating `y^{2^50}` directly.]
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common SubNLogN.Math.Cost
open scoped BigOperators

/-! ## Shape from `(ρ, K0)` -/

/-- Number of record axes `D = d - 1`, `d = dK ρ K0` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)). -/
def fnewD (ρ : RowExps) (K0 : ℕ) : ℕ := dK ρ K0 - 1

/-- `ℓ = ⌈K0/d⌉` (Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`)). -/
def fnewL (ρ : RowExps) (K0 : ℕ) : ℕ := lK ρ K0

/-- Record-axis exponents: the first `dℓ - K0` axes have exponent `ℓ - 1`, the others `ℓ`
(Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`); short `r/2` axes placed first). -/
def fnewA (ρ : RowExps) (K0 : ℕ) : Fin (fnewD ρ K0) → ℕ :=
  fun i => if (i : ℕ) < dK ρ K0 * lK ρ K0 - K0 then lK ρ K0 - 1 else lK ρ K0

/-- The balanced shape `(2^{a_0}, …, 2^{a_{D-1}}, 2^ℓ)`; definitionally
`Walsh.fftShape (fnewA ρ K0) (fnewL ρ K0)`. -/
def fnewShape (ρ : RowExps) (K0 : ℕ) : Fin (fnewD ρ K0 + 1) → ℕ :=
  fun i => 2 ^ (if h : (i : ℕ) < fnewD ρ K0 then fnewA ρ K0 ⟨i, h⟩ else fnewL ρ K0)

/-- Definitional identification: the bridge working precision at `p = pBK b k` equals `Cost.PBK b k`. -/
theorem schedP_pBK (b k : ℕ) : schedP (pBK b k) k = PBK b k := rfl

/-! ## Eligibility -/

/-- Shape and precision conditions of `WalshOK`:
* `d ≥ 2`, `ℓ ≥ 2`, `d ℓ - K0 < d` (so the last axis is a full `r` axis);
* chunk width `1 ≤ K ≤ ℓ - 1` (Theorem 6.5);
* `p0 ≥ max(8, K0)` (Theorem 4.7);
* `8 ≤ q` and `ℓ < q`, with `q = schedP p0 K0 + 2` (Theorem 6.5 at `q`). -/
def WalshShapeOK (ρ : RowExps) (p0 K0 : ℕ) : Prop :=
  2 ≤ dK ρ K0 ∧ 2 ≤ lK ρ K0 ∧ dK ρ K0 * lK ρ K0 - K0 < dK ρ K0 ∧
    1 ≤ KK ρ K0 ∧ KK ρ K0 ≤ lK ρ K0 - 1 ∧ 8 ≤ p0 ∧ K0 ≤ p0 ∧
    8 ≤ schedP p0 K0 + 2 ∧ lK ρ K0 < schedP p0 K0 + 2

/-- The bands of Lemma 7.1 (eq. (`eq:bands`)) at a precision `P'`, in
integer form. With `ε = e₁/e₂` the conditions are:
* `¼P'^ε ≤ d ⟺ P'^{e₁} ≤ (4d)^{e₂}` and `d ≤ P'^ε ⟺ d^{e₂} ≤ P'^{e₁}`;
* `2^{P'/(128d)} ≤ r ≤ 2^{P'/(8d)} ⟺ P' ≤ 128dℓ ∧ 8dℓ ≤ P'`;
* `dℓ ≤ P'` (`C_ℓ = 1`) and `K0 - ℓ ≤ P'` (proof of Lemma 7.1 (`lem:root-family`)). -/
def BandsNat (ρ : RowExps) (P' K0 : ℕ) : Prop :=
  P' ^ ρ.e₁ ≤ (4 * dK ρ K0) ^ ρ.e₂ ∧ dK ρ K0 ^ ρ.e₂ ≤ P' ^ ρ.e₁ ∧
    P' ≤ 128 * dK ρ K0 * lK ρ K0 ∧ 8 * dK ρ K0 * lK ρ K0 ≤ P' ∧
    dK ρ K0 * lK ρ K0 ≤ P' ∧ K0 - lK ρ K0 ≤ P'

/-- `WalshOKProp ρ p0 K0`: the shape-and-band test at output precision `p0` and length `2^{K0}`:
the shape conditions `WalshShapeOK` (bounds on `d, ℓ, K, p0, q`) plus the integer bands `BandsNat`
at both precisions `q` and `q + 8d` used by the layers (Lemma 7.1 (`lem:root-family`), eq. (`eq:bands`)). It depends only
on `(p0, K0)`. Its eventual truth at the W8 parameters is `WalshOK_eventuallyStmt`. It is not the
full fast-kernel cutoff (tape thresholds and the layer guard are machine/pipe obligations). -/
def WalshOKProp (ρ : RowExps) (p0 K0 : ℕ) : Prop :=
  WalshShapeOK ρ p0 K0 ∧ BandsNat ρ (schedP p0 K0 + 2) K0 ∧
    BandsNat ρ (schedP p0 K0 + 2 + 8 * dK ρ K0) K0

instance (ρ : RowExps) (p0 K0 : ℕ) : Decidable (WalshOKProp ρ p0 K0) := by
  unfold WalshOKProp WalshShapeOK BandsNat; exact inferInstance

/-- `WalshOK ρ p0 K0 : Bool`, the boolean form of `WalshOKProp` (plain `ℕ` comparisons; design
(c), condition (3)). -/
def WalshOK (ρ : RowExps) (p0 K0 : ℕ) : Bool := decide (WalshOKProp ρ p0 K0)

theorem WalshOK_iff (ρ : RowExps) (p0 K0 : ℕ) : WalshOK ρ p0 K0 = true ↔ WalshOKProp ρ p0 K0 := by
  simp [WalshOK]

/-! ## Fixed-point encoding (IntMul conventions) -/

/-- Decode an integer array at scale `2^{p+2}` (`IntMul.toScaledComplex`) into a length-`R`
array (entries beyond the array size read as `0`). -/
noncomputable def decodeArr (p R : ℕ) (x : Array (ℤ × ℤ)) : Fin R → ℂ :=
  fun j => IntMul.toScaledComplex p (IntMul.read1D x j)

/-- Encode a complex number as integers at scale `2^{p+2}`; exact on the `(p+2)`-grid. -/
noncomputable def encodeC (p : ℕ) (z : ℂ) : ℤ × ℤ :=
  (round (z.re * 2 ^ (p + 2)), round (z.im * 2 ^ (p + 2)))

/-- Encode a length-`R` array at scale `2^{p+2}`. -/
noncomputable def encodeArr (p : ℕ) {R : ℕ} (y : Fin R → ℂ) : Array (ℤ × ℤ) :=
  Array.ofFn (fun j => encodeC p (y j))

/-- Decidability of the W9 width predicate `ArrW` (the input guard of `FnewOfR`). -/
instance decArrW (w : ℕ) (x : Array (ℤ × ℤ)) : Decidable (TMFw.Contracts.W9.ArrW w x) := by
  unfold TMFw.Contracts.W9.ArrW TMFw.Contracts.W9.EntryW; exact inferInstance

/-! ## The cutoff `KstarOf` -/

/-- `KstarOf ρ`: the least `K` such that every W8 root parameter pair with `K ≤ w8K n` passes the
shape-and-band test, i.e. `WalshOKProp ρ (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n)`; it is
`0` if there is no such `K` (the `sInf` convention on `ℕ`). A fixed constant (noncomputable).
Nothing is claimed about it without the eventual-truth hypothesis; see `KstarOf_spec_of`. -/
noncomputable def KstarOf (ρ : RowExps) : ℕ :=
  sInf {K : ℕ | ∀ n : ℕ, K ≤ w8K n →
    WalshOKProp ρ (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n)}

/-- The cutoff of the `κ = 2^{-46}` row. -/
noncomputable def Kstar : ℕ := KstarOf row46

theorem Kstar_eq : Kstar = KstarOf row46 := rfl

/-! ## The maps -/

/-- `FnewOfR rr ρ Tab mid p_in cSpec x` (`p0 = cSpec.p`, `K0 = log₂ x.size`): if the input guard
`ArrW (p0 + p_in + 1) x` fails, `x.map (fun _ => (0, 0))`; otherwise decode `x` at `p_in`, run
`bridgeFixedR rr` at `p = p0` with working precision `schedP p0 K0` on the shape `fnewShape ρ K0`,
with tables `Tab p0 K0` and middle `mid p0 K0`, and encode at `p0 + 2`. -/
noncomputable def FnewOfR (rr : ℕ → ℝ → ℝ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) :
    ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ) :=
  fun p_in cSpec x =>
    if TMFw.Contracts.W9.ArrW (cSpec.p + p_in + 1) x then
      encodeArr cSpec.p
        (bridgeFixedR rr cSpec.p (schedP cSpec.p (Nat.log2 x.size)) (fnewShape ρ (Nat.log2 x.size))
          (Tab cSpec.p (Nat.log2 x.size)) (mid cSpec.p (Nat.log2 x.size))
          (decodeArr p_in (totalLen (fnewShape ρ (Nat.log2 x.size))) x))
    else x.map (fun _ => ((0 : ℤ), (0 : ℤ)))

/-- On the input guard, `FnewOfR` is the encoded bridge output. -/
theorem FnewOfR_eq_bridge (rr : ℕ → ℝ → ℝ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) (p_in : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (h : TMFw.Contracts.W9.ArrW (cSpec.p + p_in + 1) x) :
    FnewOfR rr ρ Tab mid p_in cSpec x =
      encodeArr cSpec.p
        (bridgeFixedR rr cSpec.p (schedP cSpec.p (Nat.log2 x.size)) (fnewShape ρ (Nat.log2 x.size))
          (Tab cSpec.p (Nat.log2 x.size)) (mid cSpec.p (Nat.log2 x.size))
          (decodeArr p_in (totalLen (fnewShape ρ (Nat.log2 x.size))) x)) :=
  if_pos h

/-- Off the input guard, `FnewOfR` is the zero array of the input's length. -/
theorem FnewOfR_eq_zero (rr : ℕ → ℝ → ℝ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) (p_in : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (h : ¬ TMFw.Contracts.W9.ArrW (cSpec.p + p_in + 1) x) :
    FnewOfR rr ρ Tab mid p_in cSpec x = x.map (fun _ => ((0 : ℤ), (0 : ℤ))) :=
  if_neg h

/-- On the input guard, `FnewOfR` returns an array of length `totalLen (fnewShape ρ K0)`. -/
theorem FnewOfR_size (rr : ℕ → ℝ → ℝ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) (p_in : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (h : TMFw.Contracts.W9.ArrW (cSpec.p + p_in + 1) x) :
    (FnewOfR rr ρ Tab mid p_in cSpec x).size = totalLen (fnewShape ρ (Nat.log2 x.size)) := by
  rw [FnewOfR_eq_bridge rr ρ Tab mid p_in cSpec x h]
  simp [encodeArr]

/-- Off the input guard, `FnewOfR` returns an array of the input's length. -/
theorem FnewOfR_size_off (rr : ℕ → ℝ → ℝ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) (p_in : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (h : ¬ TMFw.Contracts.W9.ArrW (cSpec.p + p_in + 1) x) :
    (FnewOfR rr ρ Tab mid p_in cSpec x).size = x.size := by
  rw [FnewOfR_eq_zero rr ρ Tab mid p_in cSpec x h]
  simp

/-- `F_newKR rr Kc ρ Tab mid` (final transform shape): the bridge `FnewOfR rr` when
`WalshOK ρ cSpec.p (log₂ x.size)` holds and `Kc ≤ log₂ x.size`, otherwise the existing
`IntMul.computablePaperFastDFT`. On W8 root inputs with `Kstar ≤ Kc`, `Kc ≤ K0` implies
`WalshOK` (`Kstar_spec_of`, given `WalshOK_eventuallyStmt`), so the guard reduces to the constant
cutoff `Kc ≤ K0` (`F_newKR_row46_eq_cutoff`); this is the only test the machine performs. -/
noncomputable def F_newKR (rr : ℕ → ℝ → ℝ) (Kc : ℕ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) :
    ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ) :=
  fun p_in cSpec x =>
    if (WalshOK ρ cSpec.p (Nat.log2 x.size) && decide (Kc ≤ Nat.log2 x.size)) = true then
      FnewOfR rr ρ Tab mid p_in cSpec x
    else IntMul.computablePaperFastDFT p_in cSpec x

/-- `F_newKR` unfolds literally to the dispatch (for the machine dispatch lemma). -/
theorem F_newKR_def (rr : ℕ → ℝ → ℝ) (Kc : ℕ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) :
    F_newKR rr Kc ρ Tab mid = fun p_in cSpec x =>
      if (WalshOK ρ cSpec.p (Nat.log2 x.size) && decide (Kc ≤ Nat.log2 x.size)) = true then
        FnewOfR rr ρ Tab mid p_in cSpec x
      else IntMul.computablePaperFastDFT p_in cSpec x := rfl

/-- On the bridge branch (`WalshOK` and `Kc ≤ log₂ x.size`), `F_newKR rr Kc` is `FnewOfR rr`. -/
theorem F_newKR_eq_FnewOfR (rr : ℕ → ℝ → ℝ) (Kc : ℕ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) (p_in : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (hOK : WalshOK ρ cSpec.p (Nat.log2 x.size) = true) (hK : Kc ≤ Nat.log2 x.size) :
    F_newKR rr Kc ρ Tab mid p_in cSpec x = FnewOfR rr ρ Tab mid p_in cSpec x := by
  have h : (WalshOK ρ cSpec.p (Nat.log2 x.size) && decide (Kc ≤ Nat.log2 x.size)) = true := by
    rw [hOK, Bool.true_and, decide_eq_true_eq]
    exact hK
  exact if_pos h

/-- Otherwise (`WalshOK` fails or `log₂ x.size < Kc`), `F_newKR rr Kc` is IntMul's radix-2
transform `IntMul.computablePaperFastDFT`. -/
theorem F_newKR_eq_radix2 (rr : ℕ → ℝ → ℝ) (Kc : ℕ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) (p_in : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (h : ¬ (WalshOK ρ cSpec.p (Nat.log2 x.size) = true ∧ Kc ≤ Nat.log2 x.size)) :
    F_newKR rr Kc ρ Tab mid p_in cSpec x = IntMul.computablePaperFastDFT p_in cSpec x := by
  have h' : ¬ ((WalshOK ρ cSpec.p (Nat.log2 x.size) && decide (Kc ≤ Nat.log2 x.size)) = true) := by
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact h
  exact if_neg h'

/-- CONTRACT (shape facts from `WalshOK`, Section 7.1 (`sec:main-alg`), eq. (`eq:root-sizes`) and Section 4.4 (`sec:bridge-alg`)):
`WalshOK ρ p0 K0` implies that `fnewShape ρ K0` is a balanced shape with `R = 2^{K0}`, `d ≥ 2`,
`t_d = 2^ℓ`, `ℓ ≥ 2`, and every `t_i ∈ {r/2, r}`. -/
def WalshOK_balancedStmt : Prop :=
  ∀ (ρ : RowExps) (p0 K0 : ℕ), WalshOK ρ p0 K0 = true →
    BalancedShape (fnewShape ρ K0) K0 (fnewL ρ K0)

/-! ## Legacy `quantR` specializations (retained for compatibility) -/

/-- Legacy `quantR` specialization (prefer `FnewOfR`): the `quantC` bridge map `bridgeFixed`
without the input width guard, retained for compatibility with
`Machine/Pipe/Contract.lean`. -/
noncomputable def FnewOf (ρ : RowExps) (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) :
    ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ) :=
  fun p_in cSpec x =>
    encodeArr cSpec.p
      (bridgeFixed cSpec.p (schedP cSpec.p (Nat.log2 x.size))
        (fnewShape ρ (Nat.log2 x.size)) (Tab cSpec.p (Nat.log2 x.size))
        (mid cSpec.p (Nat.log2 x.size))
        (decodeArr p_in (totalLen (fnewShape ρ (Nat.log2 x.size))) x))

/-- Legacy specialization (see `FnewOf`): `FnewOf` returns an array of length `totalLen (fnewShape ρ K0)`. -/
theorem FnewOf_size (ρ : RowExps) (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) (p_in : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ)) :
    (FnewOf ρ Tab mid p_in cSpec x).size = totalLen (fnewShape ρ (Nat.log2 x.size)) := by
  simp [FnewOf, encodeArr]

/-- Legacy `quantR` specialization (prefer `F_newKR`): guard `WalshOK && Kc ≤ K0` with `FnewOf`,
retained for compatibility with `Machine/Pipe/Contract.lean`. -/
noncomputable def F_newK (Kc : ℕ) (ρ : RowExps) (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) :
    ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ) :=
  fun p_in cSpec x =>
    if (WalshOK ρ cSpec.p (Nat.log2 x.size) && decide (Kc ≤ Nat.log2 x.size)) = true then
      FnewOf ρ Tab mid p_in cSpec x
    else IntMul.computablePaperFastDFT p_in cSpec x

/-- Legacy specialization (see `F_newK`): `F_newK` unfolds literally to its dispatch. -/
theorem F_newK_def (Kc : ℕ) (ρ : RowExps) (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) :
    F_newK Kc ρ Tab mid = fun p_in cSpec x =>
      if (WalshOK ρ cSpec.p (Nat.log2 x.size) && decide (Kc ≤ Nat.log2 x.size)) = true then
        FnewOf ρ Tab mid p_in cSpec x
      else IntMul.computablePaperFastDFT p_in cSpec x := rfl

/-- Legacy specialization (see `F_newK`): on the bridge branch, `F_newK Kc` is `FnewOf`. -/
theorem F_newK_eq_FnewOf (Kc : ℕ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) (p_in : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (hOK : WalshOK ρ cSpec.p (Nat.log2 x.size) = true) (hK : Kc ≤ Nat.log2 x.size) :
    F_newK Kc ρ Tab mid p_in cSpec x = FnewOf ρ Tab mid p_in cSpec x := by
  have h : (WalshOK ρ cSpec.p (Nat.log2 x.size) && decide (Kc ≤ Nat.log2 x.size)) = true := by
    rw [hOK, Bool.true_and, decide_eq_true_eq]
    exact hK
  exact if_pos h

/-- Legacy specialization (see `F_newK`): otherwise, `F_newK Kc` is IntMul's radix-2 transform. -/
theorem F_newK_eq_radix2 (Kc : ℕ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) (p_in : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (h : ¬ (WalshOK ρ cSpec.p (Nat.log2 x.size) = true ∧ Kc ≤ Nat.log2 x.size)) :
    F_newK Kc ρ Tab mid p_in cSpec x = IntMul.computablePaperFastDFT p_in cSpec x := by
  have h' : ¬ ((WalshOK ρ cSpec.p (Nat.log2 x.size) && decide (Kc ≤ Nat.log2 x.size)) = true) := by
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact h
  exact if_neg h'

/-! ## Legacy `quantR` alias `F_new` (without explicit cutoff `Kc`) -/

/-- Legacy `quantR` alias retained for compatibility with `Machine/Pipe/Contract.lean`
(prefer `F_newKR`): runs `FnewOf` when
`WalshOK ρ cSpec.p (log₂ x.size)` holds, otherwise `IntMul.computablePaperFastDFT` (no cutoff). -/
noncomputable def F_new (ρ : RowExps) (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) :
    ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ) :=
  fun p_in cSpec x =>
    if WalshOK ρ cSpec.p (Nat.log2 x.size) then FnewOf ρ Tab mid p_in cSpec x
    else IntMul.computablePaperFastDFT p_in cSpec x

/-- Legacy specialization (see `F_new`): `F_new` unfolds literally to its dispatch. -/
theorem F_new_def (ρ : RowExps) (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) :
    F_new ρ Tab mid = fun p_in cSpec x =>
      if WalshOK ρ cSpec.p (Nat.log2 x.size) then FnewOf ρ Tab mid p_in cSpec x
      else IntMul.computablePaperFastDFT p_in cSpec x := rfl

/-- Legacy specialization (see `F_new`): on the `WalshOK` branch, `F_new` is `FnewOf`. -/
theorem F_new_eq_FnewOf (ρ : RowExps) (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)) (p_in : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (h : WalshOK ρ cSpec.p (Nat.log2 x.size) = true) :
    F_new ρ Tab mid p_in cSpec x = FnewOf ρ Tab mid p_in cSpec x := by
  simp [F_new, h]

/-- CONTRACT (eventual eligibility at the W8 root parameters, for the `κ = 2^{-46}` row):
there is `N` such that for all `n ≥ N`, `WalshOK row46 p0 K0 = true` with `b = w8B n`,
`K0 = w8K n`, `p0 = IntMul.rootPrecision b K0`. (Each conjunct is an asymptotic fact:
`d, ℓ → ∞`, `d ℓ ≈ K0`, `q ≈ 20 K0`, `K ≤ d^{c} ≪ ℓ`.) -/
def WalshOK_eventuallyStmt : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    WalshOK row46 (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n) = true

/-! ## Correctness of the cutoff (modulo eventual eligibility) -/

/-- If `WalshOKProp ρ` holds at the W8 root parameters for all `n ≥ N`, then it holds at every `n`
with `KstarOf ρ ≤ w8K n`. (`w8K` is not monotone, e.g. `w8K 511 = 9` and `w8K 512 = 8`; the
witness cutoff used is `1 + max_{n < N} w8K n`.) -/
theorem KstarOf_spec_of (ρ : RowExps)
    (hev : ∃ N : ℕ, ∀ n ≥ N, WalshOKProp ρ (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n)) :
    ∀ n : ℕ, KstarOf ρ ≤ w8K n →
      WalshOKProp ρ (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n) := by
  obtain ⟨N, hN⟩ := hev
  have hmem : (Finset.range N).sup w8K + 1 ∈
      {K : ℕ | ∀ n : ℕ, K ≤ w8K n →
        WalshOKProp ρ (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n)} := by
    rw [Set.mem_ofPred_eq]
    intro n hn
    refine hN n ?_
    by_contra hlt
    have h1 : w8K n ≤ (Finset.range N).sup w8K :=
      Finset.le_sup (f := w8K) (Finset.mem_range.mpr (by omega))
    omega
  have h := Nat.sInf_mem ⟨_, hmem⟩
  rw [Set.mem_ofPred_eq] at h
  exact h

/-- The cutoff is correct for the `κ = 2^{-46}` row, given eventual eligibility: under
`WalshOK_eventuallyStmt`, every `n` with `Kstar ≤ w8K n` satisfies
`WalshOKProp row46 (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n)`. (`w8B n`, `w8K n` and
`IntMul.rootPrecision (w8B n) (w8K n)` are definitionally `W8.hB n`, `W8.hK0 n` and `W8.hP0 n`;
the unconditional `W8.hK0` form is `Kstar_spec` in `Proofs/Kstar.lean`.) -/
theorem Kstar_spec_of (hev : WalshOK_eventuallyStmt) :
    ∀ n : ℕ, Kstar ≤ w8K n →
      WalshOKProp row46 (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n) := by
  obtain ⟨N, hN⟩ := hev
  exact KstarOf_spec_of row46 ⟨N, fun n hn => (WalshOK_iff _ _ _).mp (hN n hn)⟩

/-- Any cutoff `Kc ≥ Kstar` has the same property, given eventual eligibility. -/
theorem Kstar_spec_of_le (hev : WalshOK_eventuallyStmt) (Kc : ℕ) (hKc : Kstar ≤ Kc) :
    ∀ n : ℕ, Kc ≤ w8K n →
      WalshOKProp row46 (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n) :=
  fun n hn => Kstar_spec_of hev n (le_trans hKc hn)

/-- On W8 root inputs (`cSpec.p = IntMul.rootPrecision (w8B n) (w8K n)`, `log₂ x.size = w8K n`),
for a cutoff `Kc ≥ Kstar` and given eventual eligibility, the guard of `F_newKR rr Kc row46`
reduces to the cutoff `Kc ≤ log₂ x.size`. -/
theorem F_newKR_row46_eq_cutoff (hev : WalshOK_eventuallyStmt) (rr : ℕ → ℝ → ℝ) (Kc : ℕ)
    (hKc : Kstar ≤ Kc)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape row46 K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape row46 K0) → ℂ) → (Idx (fnewShape row46 K0) → ℂ))
    (n p_in : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (hp : cSpec.p = IntMul.rootPrecision (w8B n) (w8K n)) (hx : Nat.log2 x.size = w8K n) :
    F_newKR rr Kc row46 Tab mid p_in cSpec x =
      if Kc ≤ Nat.log2 x.size then FnewOfR rr row46 Tab mid p_in cSpec x
      else IntMul.computablePaperFastDFT p_in cSpec x := by
  by_cases hK : Kc ≤ Nat.log2 x.size
  · rw [if_pos hK]
    refine F_newKR_eq_FnewOfR rr Kc row46 Tab mid p_in cSpec x ?_ hK
    rw [WalshOK_iff, hp, hx]
    exact Kstar_spec_of_le hev Kc hKc n (by rw [← hx]; exact hK)
  · rw [if_neg hK]
    exact F_newKR_eq_radix2 rr Kc row46 Tab mid p_in cSpec x (fun h => hK h.2)

/-- Legacy specialization (see `F_newK`): the same reduction for `F_newK Kc row46`. -/
theorem F_newK_row46_eq_cutoff (hev : WalshOK_eventuallyStmt) (Kc : ℕ) (hKc : Kstar ≤ Kc)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape row46 K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape row46 K0) → ℂ) → (Idx (fnewShape row46 K0) → ℂ))
    (n p_in : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (x : Array (ℤ × ℤ))
    (hp : cSpec.p = IntMul.rootPrecision (w8B n) (w8K n)) (hx : Nat.log2 x.size = w8K n) :
    F_newK Kc row46 Tab mid p_in cSpec x =
      if Kc ≤ Nat.log2 x.size then FnewOf row46 Tab mid p_in cSpec x
      else IntMul.computablePaperFastDFT p_in cSpec x := by
  by_cases hK : Kc ≤ Nat.log2 x.size
  · rw [if_pos hK]
    refine F_newK_eq_FnewOf Kc row46 Tab mid p_in cSpec x ?_ hK
    rw [WalshOK_iff, hp, hx]
    exact Kstar_spec_of_le hev Kc hKc n (by rw [← hx]; exact hK)
  · rw [if_neg hK]
    exact F_newK_eq_radix2 Kc row46 Tab mid p_in cSpec x (fun h => hK h.2)

end SubNLogN.Math.Bridge
