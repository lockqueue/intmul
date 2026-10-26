import Contracts.W7.Shapes

/-!
# Contracts.W7.Schedule — schedule parameterisation and the snapshot instance

W7 is **parametric in the schedule** (supporting both `snapshotSchedule` and `paperSchedule`). The schedule tree is always
`buildQuantizedSpecPaperStop L p K`, at the snapshot or at the paper root parameters. A
`W7.TableSchedule` fixes the remaining data:
* the tape constants (`q_leaf`, `H`);
* the faithfulness predicate;
* the pure **reference builder**, whose integers the machine reproduces bit-exactly
  (bit-exact to the reference table builder).

| Instance | `Faithful` | `ref` | `ref_faithful` |
|---|---|---|---|
| `W7.snapshotSchedule` (here) | `TablesFaithful` (FTP:36) | `buildComputablePaperTables` (CTB:150) | **proved**: CTB:274, PSR:77, PHP:37 |
| paper (W14, later) | `TablesFaithfulAt paperSchedule` | `tablesAt paperSchedule` (parametric CTB) | W14's non-vacuity theorem |

Also here (proved):
* `W7.headline_pre`: the headline inputs `(L, p, K) = (hL n, hP0 n, hK0 n)` meet W7's premises;
* `W7_tableCost_headline`: the explicit sublinear table-work bound, from CTB:715;
* `W7_headline_compose`: W7's joint output plus W9's bit-exactness give `A * B` through
  `W8_machineInterface`.
-/

namespace TMFw.Contracts

open IntMul (ComputablePaperFastDFTSpec QuantizedFastDFTSpec)

/-- A **table schedule**: what W7 must build for one schedule family. -/
structure W7.TableSchedule extends W7.TapeFormat where
  /-- Faithfulness: `TablesFaithful` (snapshot), or W14's `TablesFaithfulAt S` (paper). -/
  Faithful : ComputablePaperFastDFTSpec → QuantizedFastDFTSpec → Prop
  /-- Faithful hierarchies follow the schedule's node chain (`p`, `t1`, `r`, leaf size). -/
  faithful_sameShape : ∀ cSpec spec, Faithful cSpec spec → W7.SameShape cSpec spec
  /-- The pure reference builder that the machine reproduces bit-exactly. -/
  ref : QuantizedFastDFTSpec → ComputablePaperFastDFTSpec
  /-- The reference tables are faithful on every schedule W7 is called with. -/
  ref_faithful : ∀ L p K : ℕ, 8 ≤ p → K ≤ 2 ^ (L + 1) →
    Faithful (ref (IntMul.buildQuantizedSpecPaperStop L p K)) (IntMul.buildQuantizedSpecPaperStop L p K)

/-- `TablesFaithful` forces the structural correspondence (FTP:36-90; proved). -/
theorem W7.sameShape_of_faithful {cSpec : ComputablePaperFastDFTSpec} {spec : QuantizedFastDFTSpec}
    (h : IntMul.TablesFaithful cSpec spec) : W7.SameShape cSpec spec := by
  induction h with
  | base => exact ⟨rfl, rfl⟩
  | step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ⟨rfl, rfl, rfl, ih⟩

/-- **The snapshot schedule.** Reference: `buildComputablePaperTables` (CTB:92-151). Its
faithfulness is the snapshot's CTB:274, with validity (PSR:77) and executability (PHP:37) of the
paper-stop schedule. -/
def W7.snapshotSchedule : W7.TableSchedule where
  toTapeFormat := W7.snapshotFormat
  Faithful := IntMul.TablesFaithful
  faithful_sameShape _ _ h := W7.sameShape_of_faithful h
  ref := IntMul.buildComputablePaperTables
  ref_faithful L p K hp hK := IntMul.buildComputablePaperTables_faithful _
    (IntMul.buildQuantizedSpecPaperStop_valid L p K hp)
    (IntMul.buildQuantizedSpecPaperStop_paperExecutableValid L p K hp hK)

/-- Shape, width and size facts about the reference tables (pure; owner W7). Together with
`ref_faithful`, they turn a bit-exact machine (`W7_buildTablesRef`) into the joint output contract
(`W7_buildTables_of_ref`, Contracts/W7/Tables.lean).

*Route (snapshot):*
* shapes from `Array.size_ofFn` and the scan sizes in CTB:97-140; rows have length `W_eff` by
  `costedFoldRawTapRow` (CTB:35);
* widths from `W7_entryWidths_of_faithful`;
* size from `W7_tapeSize`. -/
def W7.RefFacts (Sch : W7.TableSchedule) : Prop :=
  ∀ L p K : ℕ, 8 ≤ p → K ≤ 2 ^ (L + 1) →
    W7.Canonical (Sch.ref (IntMul.buildQuantizedSpecPaperStop L p K)) ∧
    W7.EntryWidths Sch.toTapeFormat (Sch.ref (IntMul.buildQuantizedSpecPaperStop L p K)) ∧
    (W7.tape Sch.toTapeFormat (Sch.ref (IntMul.buildQuantizedSpecPaperStop L p K))).length ≤
      W7.tapeBound Sch.toTapeFormat (Sch.ref (IntMul.buildQuantizedSpecPaperStop L p K))

/-! ## The headline instance -/

/-- The headline inputs `(L, p, K) = (hL n, hP0 n, hK0 n)` (CSWS:2264-2269, `W8.hSpec`) satisfy
W7's premises `8 ≤ p` and `K ≤ 2^(L+1)`. -/
theorem W7.headline_pre (n : ℕ) :
    8 ≤ IntMulTM.Contracts.W8.hP0 n ∧
      IntMulTM.Contracts.W8.hK0 n ≤ 2 ^ (IntMulTM.Contracts.W8.hL n + 1) := by
  have hK0 : 4 ≤ IntMulTM.Contracts.W8.hK0 n :=
    le_max_left 4 (Nat.log2 (2 * IntMulTM.Contracts.W8.hK n) + 2)
  constructor
  · unfold IntMulTM.Contracts.W8.hP0 IntMul.rootPrecision
    omega
  · have h := IntMul.lt_two_pow_log2_succ (IntMulTM.Contracts.W8.hK0 n - 1)
    unfold IntMulTM.Contracts.W8.hL
    omega

/-- **Explicit sublinear table work along the headline schedule** (CTB:715). The total is
`(L+1)·2^(K0 − ⌊K0/2⌋)·2^67·P^6`, with `P = leafPrecision L p0 K0 = O(log n)`. This is
`O(√(n/log n)·log log n·log⁶ n)`, hence `o(n log n)`; `W7_tableCost_sqrt` states the
closed form in `n`. -/
theorem W7_tableCost_headline (n : ℕ) :
    (IntMulTM.Contracts.W8.hSpec n).precomputeSeriesTableCost ≤
      (IntMulTM.Contracts.W8.hL n + 1) *
        2 ^ (IntMulTM.Contracts.W8.hK0 n - IntMulTM.Contracts.W8.hK0 n / 2) *
        (2 ^ 67 * IntMul.leafPrecision (IntMulTM.Contracts.W8.hL n) (IntMulTM.Contracts.W8.hP0 n)
          (IntMulTM.Contracts.W8.hK0 n) ^ 6) := by
  have hpre := W7.headline_pre n
  have h := IntMul.buildQuantizedSpecPaperStop_precomputeSeriesTableCost_le
    (IntMulTM.Contracts.W8.hL n) (IntMulTM.Contracts.W8.hP0 n) (IntMulTM.Contracts.W8.hK0 n)
    (by omega) hpre.2
  exact h

/-- **W7 → W11 composition (proved).** Suppose:
* the decoded tables satisfy W7's joint output for the headline schedule;
* the machine's output equals the pipeline value on those tables (W9).

Then the output is `A * B`. This is `W8_machineInterface` with W7's faithfulness clause. -/
theorem W7_headline_compose (n A B out : ℕ) (hA : A < 2 ^ n) (hB : B < 2 ^ n)
    (cSpec : ComputablePaperFastDFTSpec)
    (hj : W7.JointOutput W7.snapshotSchedule.toTapeFormat W7.snapshotSchedule.Faithful
      (IntMulTM.Contracts.W8.hSpec n) cSpec)
    (hout : out = IntMul.computablePaperFastDFTMultiply cSpec (IntMulTM.Contracts.W8.hB n)
      (IntMulTM.Contracts.W8.hK0 n) (IntMulTM.Contracts.W8.hK n) (IntMulTM.Contracts.W8.hK n) A B) :
    out = A * B :=
  IntMulTM.Contracts.W8_machineInterface_holds n A B out hA hB ⟨cSpec, hj.faithful, hout⟩

/-- **W7_tableCost_sqrt** (pure; statement only; owner W7/W10). The closed form of
`W7_tableCost_headline` in `n`: `O(√n·log⁸ n)`.

*Route:* `2^(K0−⌊K0/2⌋) ≤ 2·√(2^K0)` and `2^K0 ≤ 16·(n/b + 1)`; `L + 1 ≤ log₂ K0 + 1`;
`P = p0 + 2·sumLogLen L K0 + 12L = O(log n)` (`leafPrecision_eq`). -/
def W7_tableCost_sqrt : Prop :=
  ∃ C N₀ : ℕ, ∀ n ≥ N₀,
    (IntMulTM.Contracts.W8.hSpec n).precomputeSeriesTableCost ≤
      C * (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8

/-- **W7_tapeBound_sqrt** (pure; statement only; owner W7/W10). The table tape of any canonical
faithful hierarchy for the headline schedule has `O(√n·log³ n)` symbols.

*Route:*
* at the top level, `t1·W_eff·pSub ≤ 2^(K0/2)·(2·pSub + 1)·pSub` and `r·(pSub + H) ≤ 2·√(2^K0)·O(pSub)`;
* the levels shrink geometrically;
* the leaf has `2^K ≤ 4p²` entries. -/
def W7_tapeBound_sqrt : Prop :=
  ∃ C N₀ : ℕ, ∀ n ≥ N₀, ∀ cSpec : ComputablePaperFastDFTSpec,
    W7.Canonical cSpec → IntMul.TablesFaithful cSpec (IntMulTM.Contracts.W8.hSpec n) →
      W7.tapeBound W7.snapshotFormat cSpec ≤ C * (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3

#assert_std_axioms W7.sameShape_of_faithful W7.headline_pre W7_tableCost_headline W7_headline_compose

end TMFw.Contracts
