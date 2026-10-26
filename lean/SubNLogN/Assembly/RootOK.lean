import SubNLogN.Assembly.Top
import SubNLogN.Math.Bridge.RootW8

/-!
# Assembly: the root invariant `RootOKSubNLogN` for the dispatching transform `F_newKR`

`F_newKR rr Kc ρ Tab mid` (`Math/Bridge/Fnew.lean`, with explicit cutoff parameter `Kc`, Section 7.6)
runs the bridge `FnewOfR rr ρ Tab mid` (`rr` a nearest rounding; `roundHalfUpR` in the final
map) when
`WalshOK ρ cSpec.p (log₂ x.size)` holds and `Kc ≤ log₂ x.size`, and IntMul's radix-2
`computablePaperFastDFT` otherwise. At the headline root parameters both transform calls of the
root composite see `cSpec.p = p0 = rootPrecision b K0` and inputs of size `2^{K0}`, so they take
the same branch, for every `Kc`.

* `RootFacts F cSpec b K0 k1 k2 A1 A2`: the non-`ChainOK` root facts of `F` (the conclusion of
  `RootW8_FnewStmt`, `Math/Bridge/RootW8.lean`, Proposition 7.2 (`prop:root-packing`), with `F` for `FnewOfR rr ρ Tab mid`): output
  sizes `2^{K0}`, decoded outputs of modulus `≤ 4`, entry widths `≤ 4 p0` for `x0, yF, x1, yI`,
  digit widths `≤ 4 p0`, and exact recovery.
* `rootOK_of_rootFacts`: at the headline root parameters, `RootFacts F` implies
  `RootOKSubNLogN F` (the two `ChainOK` conjuncts concern IntMul's radix-2 chain premise on `x0` and
  on `x1 = rootSquareV p0 K0 yF`; they follow from the modulus bounds via `WP.W11b.chainOK_of`, as
  in `WP.W11b.w9RootOK_of` and `WP.W11b.root_parts`).
* `rootOKAll_F_newKR`: if the bridge branch has `RootFacts` whenever `WalshOK` holds, then
  `RootOKAllStmt (F_newKR rr Kc ρ Tab mid)` for every cutoff `Kc` (the other branch is
  `rootOKSubNLogN_computablePaperFastDFT`).
* `rootFacts_of_rootW8`: `RootW8_FnewStmt`, instantiated at the headline root parameters, gives
  the bridge-branch hypothesis of `rootOKAll_F_newKR` from table certification and a Definition 4.5 (`def:middle-contract`) middle
  transform at every eligible `(p0, K0)`.

The three CONTRACT theorems are proved here. Helpers: `rootOK_norm_rootSquareV_le`,
`rootOK_nodeInv_rootSquareV`, `rootOK_chainOK_rootSquareV` (`ChainOK` of `x1` from the modulus
bound on `yF`), `rootOKSubNLogN_of_agree` (`RootOKSubNLogN` depends on `F` only through the two
root calls), `F_newKR_eq_FnewOfR_of_size`, `F_newKR_eq_radix2_of_size` (the dispatch of `F_newKR rr Kc`
on inputs of size `2^{K0}` with `cSpec.p = p0`).
-/

namespace SubNLogN.Assembly

open SubNLogN SubNLogN.S5 SubNLogN.Math.Cost SubNLogN.Math.Bridge SubNLogN.Math.Common
  Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  IntMulTM.Contracts.Top

/-- The non-`ChainOK` root facts of a transform `F` at root parameters `(b, K0, k1, k2)` and
operands `A1, A2` (the conclusion of `RootW8_FnewStmt` with `F` in place of `FnewOfR rr ρ Tab mid`):
with `p0 = rootPrecision b K0`, `x0 = rootPackV b K0 k1 k2 A1 A2`, `yF = F b cSpec x0`,
`x1 = rootSquareV p0 K0 yF`, `yI = F p0 cSpec x1`: `yF.size = yI.size = 2^{K0}`; for `u < 2^{K0}`,
`‖toScaledComplex p0 yF[u]‖ ≤ 4` and `‖toScaledComplex p0 yI[u]‖ ≤ 4`; `ArrW (4 p0)` for
`x0, yF, x1, yI`; every digit of `rootDigits b K0 k1 k2 yI` has `bitLen ≤ 4 p0`; and
`reconstructChunksTree b (rootDigits b K0 k1 k2 yI) = A1 * A2`. -/
def RootFacts (F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (b K0 k1 k2 A1 A2 : ℕ) : Prop :=
  let p0 := IntMul.rootPrecision b K0
  let x0 := rootPackV b K0 k1 k2 A1 A2
  let yF := F b cSpec x0
  let x1 := rootSquareV p0 K0 yF
  let yI := F p0 cSpec x1
  yF.size = 2 ^ K0 ∧ yI.size = 2 ^ K0 ∧
    (∀ u < 2 ^ K0, ‖IntMul.toScaledComplex p0 (IntMul.read1D yF u)‖ ≤ 4) ∧
    (∀ u < 2 ^ K0, ‖IntMul.toScaledComplex p0 (IntMul.read1D yI u)‖ ≤ 4) ∧
    ArrW (4 * p0) x0 ∧ ArrW (4 * p0) yF ∧ ArrW (4 * p0) x1 ∧ ArrW (4 * p0) yI ∧
    (∀ c ∈ rootDigits b K0 k1 k2 yI, bitLen c ≤ 4 * p0) ∧
    IntMul.reconstructChunksTree b (rootDigits b K0 k1 k2 yI) = A1 * A2

/-! ## Helper lemmas -/

/-- Under `WP.Top.Joint n cSpec`, the table spec's precision is the root precision
`rootPrecision (W8.hB n) (W8.hK0 n)` (matching `SubNLogN.Machine.Pipe.joint_p`, via
`TablesFaithful.p_eq`). -/
private theorem joint_p_root {n : ℕ} {cSpec : IntMul.ComputablePaperFastDFTSpec}
    (hj : WP.Top.Joint n cSpec) : cSpec.p = IntMul.rootPrecision (W8.hB n) (W8.hK0 n) := by
  rw [IntMul.TablesFaithful.p_eq hj.faithful]
  exact IntMul.buildQuantizedSpecPaperStop_p _ _ _

/-- `k + k ≤ 2^{K0}` at the headline parameters (`k = W8.hK n`, `K0 = W8.hK0 n`; as in
`W8_parametricHeadline_holds`). -/
private theorem hK_add_hK_le_two_pow (n : ℕ) : W8.hK n + W8.hK n ≤ 2 ^ W8.hK0 n := by
  have hlt := IntMul.lt_two_pow_log2_succ (2 * W8.hK n)
  have hle_exp : Nat.log2 (2 * W8.hK n) + 1 ≤ W8.hK0 n := by
    have : Nat.log2 (2 * W8.hK n) + 2 ≤ W8.hK0 n :=
      le_max_right 4 (Nat.log2 (2 * W8.hK n) + 2)
    omega
  have hpow_le : 2 ^ (Nat.log2 (2 * W8.hK n) + 1) ≤ 2 ^ W8.hK0 n :=
    Nat.pow_le_pow_right zero_lt_two hle_exp
  omega

/-- `n ≤ b·k` at the headline parameters (`b = W8.hB n`, `k = W8.hK n`; as in
`W8_parametricHeadline_holds`). -/
private theorem le_hB_mul_hK (n : ℕ) : n ≤ W8.hB n * W8.hK n := by
  have hb_pos : 1 ≤ W8.hB n := le_max_left 1 (Nat.log2 n)
  unfold W8.hK
  have hdiv := Nat.div_add_mod n (W8.hB n)
  have hmod : n % W8.hB n < W8.hB n := Nat.mod_lt n (by omega)
  have hmul : W8.hB n * (n / W8.hB n + 1) = W8.hB n * (n / W8.hB n) + W8.hB n := by ring
  omega

/-- An operand below `2^n` is below `2^{b·k}` at the headline parameters. -/
private theorem lt_two_pow_hB_mul_hK {n A : ℕ} (hA : A < 2 ^ n) :
    A < 2 ^ (W8.hB n * W8.hK n) :=
  hA.trans_le (Nat.pow_le_pow_right (by norm_num) (le_hB_mul_hK n))

attribute [local instance 10000] IntMul.instZeroIntElementary in
/-- If the `u`-th entry of `y` decodes (at `p`) to modulus `≤ 4`, then for `u < 2^{K0}` the `u`-th
entry of `rootSquareV p K0 y = conj(round_{p+2}(y²))` decodes to modulus `≤ 17` (as `hz17` in
`WP.W11b.root_parts`). -/
theorem rootOK_norm_rootSquareV_le (p K0 : ℕ) (y : Array (ℤ × ℤ)) (u : ℕ) (hu : u < 2 ^ K0)
    (hy : ‖IntMul.toScaledComplex p (IntMul.read1D y u)‖ ≤ 4) :
    ‖IntMul.toScaledComplex p (IntMul.read1D (rootSquareV p K0 y) u)‖ ≤ 17 := by
  unfold rootSquareV
  rw [IntMul.read1D_runSequentialScanSteps_eq _ _ u hu, IntMul.toScaledComplex_gConj,
    IntMul.toScaledComplex_gMulScaled_eq_complexQuantize_mul, norm_star]
  have hsq : ‖IntMul.toScaledComplex p (IntMul.read1D y u) *
      IntMul.toScaledComplex p (IntMul.read1D y u)‖ ≤ 16 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (IntMul.toScaledComplex p (IntMul.read1D y u))]
  have h1 := IntMul.norm_complexQuantize_le p
    (IntMul.toScaledComplex p (IntMul.read1D y u) * IntMul.toScaledComplex p (IntMul.read1D y u))
  have hq : IntMul.complexQuantizeMaxErr p ≤ 1 := by
    have hlt := IntMul.complexQuantizeMaxErr_lt p
    have hpow : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    linarith
  linarith

/-- `NodeInv` of the headline schedule `W8.hSpec n` at `p0 = rootPrecision (W8.hB n) (W8.hK0 n)` for
`rootSquareV p0 K0 y` (`K0 = W8.hK0 n`), from `‖y_u‖ ≤ 4` (decoded at `p0`) for `u < 2^{K0}`: the
squares have modulus `≤ 17 ≤ 2^{p0}` since `p0 ≥ 8` (as `hNz` in `WP.W11b.root_parts`). -/
theorem rootOK_nodeInv_rootSquareV (n : ℕ) (y : Array (ℤ × ℤ))
    (hy : ∀ u < 2 ^ W8.hK0 n,
      ‖IntMul.toScaledComplex (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (IntMul.read1D y u)‖ ≤ 4) :
    WP.W11b.NodeInv (W8.hSpec n) (IntMul.rootPrecision (W8.hB n) (W8.hK0 n))
      (rootSquareV (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) y) := by
  have hp0 : 8 ≤ W8.hP0 n := (W7.headline_pre n).1
  have hsize : (W8.hSpec n).size = 2 ^ W8.hK0 n := IntMul.buildQuantizedSpecPaperStop_size _ _ _
  have hsp : (W8.hSpec n).p = W8.hP0 n := IntMul.buildQuantizedSpecPaperStop_p _ _ _
  have h17 : (17 : ℝ) ≤ (2 : ℝ) ^ (W8.hSpec n).p := by
    rw [hsp]
    calc (17 : ℝ) ≤ (2 : ℝ) ^ 8 := by norm_num
      _ ≤ (2 : ℝ) ^ W8.hP0 n := pow_le_pow_right₀ (by norm_num) hp0
  refine ⟨by rw [hsize]; exact WP.W11b.size_rootSquareV _ _ _, fun u hu => ?_⟩
  have hu' : u < 2 ^ W8.hK0 n := hsize ▸ hu
  exact (rootOK_norm_rootSquareV_le (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) y u hu'
    (hy u hu')).trans h17

/-- `ChainOK` (widths `wdHead n`) of the inverse-transform input `rootSquareV p0 K0 y` under
`WP.Top.Joint n cSpec`, from `‖y_u‖ ≤ 4` (decoded at `p0`) for `u < 2^{K0}` (`WP.W11b.chainOK_of`
with `WP.W11b.leafChainOK` and `WP.W11b.reqW_le`, as in `WP.W11b.w9RootOK_of`). -/
theorem rootOK_chainOK_rootSquareV (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (hj : WP.Top.Joint n cSpec) (y : Array (ℤ × ℤ))
    (hy : ∀ u < 2 ^ W8.hK0 n,
      ‖IntMul.toScaledComplex (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (IntMul.read1D y u)‖ ≤ 4) :
    ChainOK (fun _ => WP.W11b.wdHead n) cSpec (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) 0
      [rootSquareV (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) y] := by
  have hfaith : IntMul.TablesFaithful cSpec (W8.hSpec n) := hj.faithful
  have hp0 : 8 ≤ W8.hP0 n := (W7.headline_pre n).1
  have hvalid : (W8.hSpec n).Valid := IntMul.buildQuantizedSpecPaperStop_valid _ _ _ hp0
  have hsp : (W8.hSpec n).p = W8.hP0 n := IntMul.buildQuantizedSpecPaperStop_p _ _ _
  have e : W8.hP0 n = IntMul.rootPrecision (W8.hB n) (W8.hK0 n) := rfl
  have hreq : ∀ _ℓ : ℕ,
      WP.W11b.reqW cSpec (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) ≤ WP.W11b.wdHead n := by
    intro _
    refine (WP.W11b.reqW_le hvalid hfaith _).trans ?_
    rw [hsp]
    unfold WP.W11b.wdHead
    omega
  exact WP.W11b.chainOK_of WP.W11b.leafChainOK (fun _ => WP.W11b.wdHead n) hvalid cSpec hfaith
    hj.canonical hj.widths _ 0 _ hreq (by simpa using rootOK_nodeInv_rootSquareV n y hy)

/-- `RootOKSubNLogN` sees the transform only through the two calls of the root composite: if `F₂`
agrees with `F₁` on the forward call `(b, cSpec, x0)` and on the inverse call
`(p0, cSpec, rootSquareV p0 K0 (F₁ b cSpec x0))`, then `RootOKSubNLogN F₁` implies
`RootOKSubNLogN F₂` (same parameters). -/
theorem rootOKSubNLogN_of_agree
    {F₁ F₂ : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ)}
    {cSpec : IntMul.ComputablePaperFastDFTSpec} {b K0 k1 k2 A1 A2 wd wR : ℕ}
    (h : RootOKSubNLogN F₁ cSpec b K0 k1 k2 A1 A2 wd wR)
    (h0 : F₂ b cSpec (rootPackV b K0 k1 k2 A1 A2) = F₁ b cSpec (rootPackV b K0 k1 k2 A1 A2))
    (h1 : F₂ (IntMul.rootPrecision b K0) cSpec
        (rootSquareV (IntMul.rootPrecision b K0) K0 (F₁ b cSpec (rootPackV b K0 k1 k2 A1 A2))) =
      F₁ (IntMul.rootPrecision b K0) cSpec
        (rootSquareV (IntMul.rootPrecision b K0) K0 (F₁ b cSpec (rootPackV b K0 k1 k2 A1 A2)))) :
    RootOKSubNLogN F₂ cSpec b K0 k1 k2 A1 A2 wd wR := by
  simpa only [RootOKSubNLogN, h0, h1] using h

/-- On an input of size `2^{K0}`, with `cSpec.p = p0`, `WalshOK ρ p0 K0` and `Kc ≤ K0`,
`F_newKR rr Kc` runs the bridge `FnewOfR rr`. -/
theorem F_newKR_eq_FnewOfR_of_size {rr : ℕ → ℝ → ℝ} {Kc : ℕ} {ρ : RowExps}
    {Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0)}
    {mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)}
    {p_in p0 K0 : ℕ} {cSpec : IntMul.ComputablePaperFastDFTSpec} {x : Array (ℤ × ℤ)}
    (hp : cSpec.p = p0) (hx : x.size = 2 ^ K0) (hOK : WalshOK ρ p0 K0 = true) (hK : Kc ≤ K0) :
    F_newKR rr Kc ρ Tab mid p_in cSpec x = FnewOfR rr ρ Tab mid p_in cSpec x :=
  F_newKR_eq_FnewOfR rr Kc ρ Tab mid p_in cSpec x (by rw [hx, Nat.log2_two_pow, hp]; exact hOK)
    (by rw [hx, Nat.log2_two_pow]; exact hK)

/-- On an input of size `2^{K0}`, with `cSpec.p = p0` and `¬ (WalshOK ρ p0 K0 = true ∧ Kc ≤ K0)`,
`F_newKR rr Kc` runs IntMul's radix-2 `computablePaperFastDFT`. -/
theorem F_newKR_eq_radix2_of_size {rr : ℕ → ℝ → ℝ} {Kc : ℕ} {ρ : RowExps}
    {Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0)}
    {mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ)}
    {p_in p0 K0 : ℕ} {cSpec : IntMul.ComputablePaperFastDFTSpec} {x : Array (ℤ × ℤ)}
    (hp : cSpec.p = p0) (hx : x.size = 2 ^ K0) (hc : ¬ (WalshOK ρ p0 K0 = true ∧ Kc ≤ K0)) :
    F_newKR rr Kc ρ Tab mid p_in cSpec x = IntMul.computablePaperFastDFT p_in cSpec x :=
  F_newKR_eq_radix2 rr Kc ρ Tab mid p_in cSpec x (by rw [hx, Nat.log2_two_pow, hp]; exact hc)

/-- CONTRACT (`ChainOK` packaging; as in `WP.W11b.w9RootOK_of`, `WP/W11b/Main.lean:61`, and
`WP.W11b.root_parts`, `WP/W11b/Root.lean:47`): at the headline root parameters
(`n = operandBits a b`), `WP.Top.Joint n cSpec` and `RootFacts F` imply `RootOKSubNLogN F` with
widths `wdHead n`, `wRHead n`. -/
theorem rootOK_of_rootFacts
    (F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (hj : WP.Top.Joint (operandBits a b) cSpec)
    (h : RootFacts F cSpec (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
      (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) a b) :
    RootOKSubNLogN F cSpec (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
      (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) a b
      (WP.W11b.wdHead (operandBits a b)) (WP.W11b.wRHead (operandBits a b)) := by
  obtain ⟨hc0, -⟩ := rootOKSubNLogN_computablePaperFastDFT a b cSpec hj
  obtain ⟨hsF, hsI, hnF, -, hw0, hwF, hw1, hwI, hdig, hrec⟩ := h
  exact ⟨hc0, rootOK_chainOK_rootSquareV (operandBits a b) cSpec hj _ hnF, hw0, hsF, hwF, hw1,
    hsI, hwI, hdig, hrec⟩

/-- CONTRACT (the dispatch): if, for every input whose root parameters are eligible
(`WalshOK ρ p0 K0`), the bridge `FnewOfR rr ρ Tab mid` has `RootFacts` at the headline root
parameters, then for every cutoff `Kc` the transform `F_newKR rr Kc ρ Tab mid` satisfies the root
invariant for all inputs. -/
theorem rootOKAll_F_newKR (rr : ℕ → ℝ → ℝ) (ρ : RowExps)
    (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ))
    (hW : ∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      WP.Top.Joint (operandBits a b) cSpec →
      WalshOK ρ (IntMul.rootPrecision (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b)))
        (W8.hK0 (operandBits a b)) = true →
      RootFacts (FnewOfR rr ρ Tab mid) cSpec (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
        (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) a b) (Kc : ℕ) :
    RootOKAllStmt (F_newKR rr Kc ρ Tab mid) := by
  intro a b cSpec hj
  have hp := joint_p_root hj
  by_cases hc : WalshOK ρ (IntMul.rootPrecision (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b)))
      (W8.hK0 (operandBits a b)) = true ∧ Kc ≤ W8.hK0 (operandBits a b)
  · exact rootOKSubNLogN_of_agree
      (rootOK_of_rootFacts (FnewOfR rr ρ Tab mid) a b cSpec hj (hW a b cSpec hj hc.1))
      (F_newKR_eq_FnewOfR_of_size hp (WP.W11b.size_rootPackV _ _ _ _ _ _) hc.1 hc.2)
      (F_newKR_eq_FnewOfR_of_size hp (WP.W11b.size_rootSquareV _ _ _) hc.1 hc.2)
  · exact rootOKSubNLogN_of_agree (rootOKSubNLogN_computablePaperFastDFT a b cSpec hj)
      (F_newKR_eq_radix2_of_size hp (WP.W11b.size_rootPackV _ _ _ _ _ _) hc)
      (F_newKR_eq_radix2_of_size hp (WP.W11b.size_rootSquareV _ _ _) hc)

/-- CONTRACT (instantiating `RootW8_FnewStmt` at the headline root parameters, Proposition 7.2 (`prop:root-packing`)): for a nearest
rounding `rr`, if the tables are certified (`TablesCertifiedR rr`) and `mid` is a Definition 4.5 middle
transform at every eligible `(p0, K0)`, the bridge branch `FnewOfR rr ρ Tab mid` has `RootFacts` at
every eligible headline input. -/
theorem rootFacts_of_rootW8 (hW8 : RootW8_FnewStmt) (rr : ℕ → ℝ → ℝ) (hrr : IsNearestRounding rr)
    (ρ : RowExps) (Tab : (p0 K0 : ℕ) → BridgeTables (fnewShape ρ K0))
    (mid : (p0 K0 : ℕ) → (Idx (fnewShape ρ K0) → ℂ) → (Idx (fnewShape ρ K0) → ℂ))
    (hT : ∀ p0 K0 : ℕ, WalshOK ρ p0 K0 = true →
      TablesCertifiedR rr (alphaDefault (schedOmega p0 K0 (fnewD ρ K0 + 1))) (schedP p0 K0)
        (fnewShape ρ K0) (Tab p0 K0))
    (hM : ∀ p0 K0 : ℕ, WalshOK ρ p0 K0 = true →
      ∃ (Emid : ℝ) (δmid : ℕ), IsMiddleTransform (fnewShape ρ K0) (schedP p0 K0) Emid δmid
        (mid p0 K0))
    (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (hj : WP.Top.Joint (operandBits a b) cSpec)
    (hOK : WalshOK ρ (IntMul.rootPrecision (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b)))
        (W8.hK0 (operandBits a b)) = true) :
    RootFacts (FnewOfR rr ρ Tab mid) cSpec (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
      (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) a b := by
  obtain ⟨hAa, hBb, -, -⟩ := input_bridge a b
  obtain ⟨Emid, δmid, hmid⟩ := hM _ _ hOK
  exact hW8 rr hrr ρ Tab mid (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
    (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) a b cSpec
    (le_max_left 1 (Nat.log2 (operandBits a b))) (hK_add_hK_le_two_pow _)
    (lt_two_pow_hB_mul_hK hAa) (lt_two_pow_hB_mul_hK hBb) (joint_p_root hj) hOK (hT _ _ hOK)
    Emid δmid hmid

end SubNLogN.Assembly
