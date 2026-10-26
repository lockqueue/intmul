import Contracts.W7.Schedule
import Contracts.W7.Kernels
import Contracts.Machine.W3
import Contracts.Machine.W5
import Contracts.Machine.W6a

/-!
# Contracts.W7.Tables — the joint table-builder output contract

**`W7_buildTables Sch`.** A closed program reads the schedule inputs `(L, p, K)` and pushes onto the
table stack `TR` (named stack `0`) the tape `W7.tape Sch cSpec` of a hierarchy `cSpec` such that:
1. `cSpec` is faithful (`Sch.Faithful`, i.e. `TablesFaithful` for the snapshot). So FTP:2304, or the
   paper's `_at` variant, applies to the decoded tables.
2. `cSpec` is canonical, and the tape lists exactly the used entries (`W7.Canonical`, `W7.tape`).
3. The record widths are bounded (`W7.EntryWidths`).
4. The serialized size is bounded (`W7.tapeBound`).
5. Construction cost is at most
   `C·(precomputeSeriesTableCost(spec) + |tape| + |L| + |p| + |K| + 1)`, with at most
   `W7.maxScratch` scratch stacks.
   * `precomputeSeriesTableCost` is the snapshot's explicit per-level budget (CTB:421-438); it is
     `O(√(n/log n)·polylog n)` along the headline schedule (`W7_tableCost_headline`, proved).
   * The bound charges each schedule level once (the spec is a chain), so per-node construction is
     ruled out.
6. Segments appear in sweep consumption order: pre segments top-down, then the leaf, then post segments bottom-up
   (matching the level-synchronous pipeline).

**Implementation route.** `W7_buildTablesRef` reproduces `Sch.ref spec` bit-exactly. Then
`W7_buildTables_of_ref` (proved) uses the reference's faithfulness (`Sch.ref_faithful`, proved for
the snapshot) and its shape and width facts (`W7.RefFacts`, pure).

**Hypotheses.** The implementation may assume the frozen machine contracts `W7.Hyps` (W3, W4's
record move, W5, W6a) as explicit contract hypotheses. W6b (Barrett) is not needed: tables use
long division only.
-/

namespace TMFw.Contracts

open IntMul (ComputablePaperFastDFTSpec QuantizedFastDFTSpec)

/-- Scratch stacks available to the table builder. The pipeline's idle work stacks serve; the table
phase runs before the forward and inverse transforms. -/
def W7.maxScratch : ℕ := 32

/-- **W7.buildTables** (joint table-builder output contract), parametric in the schedule `Sch`.
* Stacks: `0` = `TR` (receives the tape on top), `1` = `L`, `2` = `p`, `3` = `K` (binary, restored).
* Schedule: `spec = buildQuantizedSpecPaperStop L p K`, with `8 ≤ p` and `K ≤ 2^(L+1)`; the headline
  inputs satisfy these (`W7.headline_pre`).
* Output: the tape of a hierarchy satisfying `W7.JointOutput`.
* Cost bound as in the module docstring. -/
def W7_buildTables (Sch : W7.TableSchedule) : Prop :=
  MContract Unit 4 W7.maxScratch Unit fun _ m _ C _ P =>
    ∀ (L p K : ℕ) (rL rp rK : List Sym) (S : Loc 4 m → List Sym),
      8 ≤ p → K ≤ 2 ^ (L + 1) → TermOK rL → TermOK rp → TermOK rK →
      S (.inl 1) = natSyms L ++ rL → S (.inl 2) = natSyms p ++ rp → S (.inl 3) = natSyms K ++ rK →
      ∃ cSpec : ComputablePaperFastDFTSpec,
        W7.JointOutput Sch.toTapeFormat Sch.Faithful (IntMul.buildQuantizedSpecPaperStop L p K) cSpec ∧
        Runs P S (Function.update S (.inl 0) (W7.tape Sch.toTapeFormat cSpec ++ S (.inl 0)))
          (fun _ => True)
          (C * ((IntMul.buildQuantizedSpecPaperStop L p K).precomputeSeriesTableCost +
            (W7.tape Sch.toTapeFormat cSpec).length + bitLen L + bitLen p + bitLen K + 1))

/-- **W7.buildTablesRef** (implementation route, decision D1): the same machine, but the tape is that
of the reference tables `Sch.ref spec`, reproduced bit-exactly. -/
def W7_buildTablesRef (Sch : W7.TableSchedule) : Prop :=
  MContract Unit 4 W7.maxScratch Unit fun _ m _ C _ P =>
    ∀ (L p K : ℕ) (rL rp rK : List Sym) (S : Loc 4 m → List Sym),
      8 ≤ p → K ≤ 2 ^ (L + 1) → TermOK rL → TermOK rp → TermOK rK →
      S (.inl 1) = natSyms L ++ rL → S (.inl 2) = natSyms p ++ rp → S (.inl 3) = natSyms K ++ rK →
      Runs P S (Function.update S (.inl 0)
          (W7.tape Sch.toTapeFormat (Sch.ref (IntMul.buildQuantizedSpecPaperStop L p K)) ++ S (.inl 0)))
        (fun _ => True)
        (C * ((IntMul.buildQuantizedSpecPaperStop L p K).precomputeSeriesTableCost +
          (W7.tape Sch.toTapeFormat (Sch.ref (IntMul.buildQuantizedSpecPaperStop L p K))).length +
          bitLen L + bitLen p + bitLen K + 1))

/-- **Bit-exact reproduction implies the joint output contract (proved).** Faithfulness comes from
`Sch.ref_faithful`; shapes, widths and size from `W7.RefFacts`. -/
theorem W7_buildTables_of_ref (Sch : W7.TableSchedule) (h : W7_buildTablesRef Sch)
    (hf : W7.RefFacts Sch) : W7_buildTables Sch := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun u => ?_⟩
  obtain ⟨m, R, obs, P, hm, hR, hRne, hcl, hspec⟩ := hC u
  refine ⟨m, R, obs, P, hm, hR, hRne, hcl, ?_⟩
  intro L p K rL rp rK S hp hK h1 h2 h3 e1 e2 e3
  obtain ⟨hcan, hw, hsz⟩ := hf L p K hp hK
  exact ⟨Sch.ref (IntMul.buildQuantizedSpecPaperStop L p K),
    ⟨Sch.ref_faithful L p K hp hK, hcan, hw, hsz⟩,
    hspec L p K rL rp rK S hp hK h1 h2 h3 e1 e2 e3⟩

/-! ## Pure obligations for the snapshot reference -/

/-- **W7_refCanonical** (pure; **proved** below as `W7_refCanonical_holds`, with no schedule premise).
The snapshot builder's arrays have exactly the canonical lengths:
* `Array.size_ofFn` for `filterTaps`, `c0Table`, `c1Table` and the leaf stages;
* the scan-output sizes for `preTwiddles`, `postTwiddles` and the stage arrays (CTB:97-140);
* row length `W_eff` from `costedFoldRawTapRow` (CTB:35-39). -/
def W7_refCanonical : Prop :=
  ∀ L p K : ℕ, 8 ≤ p → K ≤ 2 ^ (L + 1) →
    W7.Canonical (IntMul.buildComputablePaperTables (IntMul.buildQuantizedSpecPaperStop L p K))

/-- The snapshot builder's arrays always have the canonical lengths (proved; no schedule premise). -/
theorem W7.canonical_buildComputablePaperTables :
    ∀ spec : QuantizedFastDFTSpec, W7.Canonical (IntMul.buildComputablePaperTables spec)
  | .base p R => by
      dsimp only [W7.Canonical, IntMul.buildComputablePaperTables,
        IntMul.buildComputablePaperTablesWithProgramCost]
      refine ⟨Array.size_ofFn, fun s hs => ?_⟩
      simp [IntMul.array_getD_ofFn_of_lt _ _ _ s hs]
  | .step p K t1 r c1 v1Of child => by
      dsimp only [W7.Canonical, IntMul.buildComputablePaperTables,
        IntMul.buildComputablePaperTablesWithProgramCost]
      refine ⟨Array.size_ofFn, fun j1 hj1 => ?_, by simp, by simp, Array.size_ofFn,
        Array.size_ofFn, W7.canonical_buildComputablePaperTables child⟩
      simp [IntMul.array_getD_ofFn_of_lt _ _ _ j1 hj1]

theorem W7_refCanonical_holds : W7_refCanonical :=
  fun _ _ _ _ _ => W7.canonical_buildComputablePaperTables _

/-- The snapshot's `W7.RefFacts` follows from the two remaining pure obligations (proved). -/
theorem W7.refFacts_snapshot (hw : W7_entryWidths_of_faithful) (hs : W7_tapeSize) :
    W7.RefFacts W7.snapshotSchedule := by
  intro L p K hp hK
  have hf : IntMul.TablesFaithful
      (IntMul.buildComputablePaperTables (IntMul.buildQuantizedSpecPaperStop L p K))
      (IntMul.buildQuantizedSpecPaperStop L p K) :=
    W7.snapshotSchedule.ref_faithful L p K hp hK
  have hc := W7_refCanonical_holds L p K hp hK
  exact ⟨hc, hw L p K hp hK _ hf, hs _ _ hc (hw L p K hp hK _ hf)⟩

/-! ## Hypotheses and deliverable -/

/-- The machine-contract hypotheses assumed by W7's table-builder implementation. -/
def W7.Hyps : Prop :=
  (W3_copyNat ∧ W3_dropNat ∧ W3_normNat ∧ W3_isZeroNat ∧ W3_cmpNat ∧ W3_addNat ∧ W3_subNat ∧
    W3_shlConst ∧ W3_shrConst ∧ W3_shlVar ∧ W3_shrVar ∧ W3_splitAt ∧ W3_concatAt ∧
    W3_incNat ∧ W3_decNat ∧ W3_natToInt ∧ W3_attachSign ∧ W3_splitSign ∧ W3_negInt ∧
    W3_signInt ∧ W3_addInt ∧ W3_subInt ∧ W3_cmpInt ∧ W3_smallOpInt) ∧
  W4_moveRecord ∧ W5_toom3Mul ∧ W6a_divModNat ∧ W6a_divRound

/-- **W7 deliverable** (the main theorem's shape): the joint output contract for the snapshot schedule
from the frozen machine contracts. The paper-schedule deliverable is
`W7.Hyps → W7_buildTables paperTableSchedule`, once W14 supplies the instance. -/
def W7_deliverable : Prop := W7.Hyps → W7_buildTables W7.snapshotSchedule

/-- **W7 implementation plan** (shape):
* the kernels from W3/W5/W6a;
* the bit-exact driver from the kernels;
* the two remaining pure facts (canonical shapes are proved above). -/
def W7_plan : Prop :=
  (W7.Hyps → W7_kernels) ∧
  (W7.Hyps → W7_kernels → W7_buildTablesRef W7.snapshotSchedule) ∧
  W7_entryWidths_of_faithful ∧ W7_tapeSize

/-- The plan discharges the deliverable (proved). -/
theorem W7_deliverable_of_plan (h : W7_plan) : W7_deliverable := fun hyps =>
  W7_buildTables_of_ref _ (h.2.1 hyps (h.1 hyps)) (W7.refFacts_snapshot h.2.2.1 h.2.2.2)

#assert_std_axioms W7_buildTables_of_ref W7.canonical_buildComputablePaperTables W7_refCanonical_holds
  W7.refFacts_snapshot W7_deliverable_of_plan

end TMFw.Contracts
