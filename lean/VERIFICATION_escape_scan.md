# Escape-hatch scan of the distributed tree (from git archive 3480d37), comments and strings stripped

Files scanned: 2011 library .lean files under AxiomCheck.lean, Contracts, IntMul, IntMul.lean, IntMulTM, LevelSync, WP, SubNLogN (the lakefile defaultTargets; standalone replay wrappers and negative-control .lean files in replay/ are not part of the lake build targets and are excluded).

| pattern | hits |
|---|---|
| sorry | 0 |
| admit | 0 |
| axiom decl | 0 |
| native_decide | 0 |
| decide +kernel | 41 |
| ofReduceBool/ofReduceNat | 2 |
| implemented_by | 0 |
| extern | 0 |
| unsafe | 0 |
| opaque | 0 |
| partial def | 0 |
| skipKernelTC/debug.* | 0 |
| #exit | 0 |
| macro_rules | 0 |
| macro decl | 0 |
| syntax decl | 17 |
| elab decl | 6 |
| notation/infix/prefix/postfix | 9 |
| run_cmd/run_tac/run_elab | 2 |
| attribute [-...] (instance/simp removal) | 0 |
| local/scoped instance | 83 |
| import Lean | 5 |
| Lean.Elab/Lean.Meta use | 0 |
| csimp | 0 |
| Decidable instance decl | 8 |
| Classical.choice explicit | 12 |

`set_option` names used (count): backward.dsimp.instances×5, linter.style.haveILetI×1, linter.unusedSimpArgs×30, linter.unusedVariables×2, maxHeartbeats×74, maxRecDepth×1, synthInstance.maxHeartbeats×3, synthInstance.maxSize×4


## decide +kernel (41 hits; first 40)
```
SubNLogN/Math/Networks/CellCalc.lean:177: theorem rank_total_bit : totalBit 100 = tripleSb 100 := by decide +kernel
SubNLogN/Math/Networks/CellCalc.lean:182: theorem rank_total_complex : totalComplex 100 = tripleSc 100 := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCenterGen.lean:26: have hT : cT (aCenter .one 3, aCenter .one 4) = [(.C, .L 0, .L 0)] := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCenterGen.lean:27: have hH : cH (aCenter .one 3, aCenter .one 4) = [] := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCenterGen.lean:28: have h0 : (eR (aCenter .one 3, aCenter .one 4) 0).length = 0 := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCenterGen.lean:33: decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCenterGen.lean:34: have hH : cH (aCenter .two 3, aCenter .two 4) = [(.C, .C, .L 0)] := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCenterGen.lean:35: have h0 : (eR (aCenter .two 3, aCenter .two 4) 0).length = 1 := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCenterGen.lean:36: have h1 : (eR (aCenter .two 3, aCenter .two 4) 1).length = 0 := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCenterGen.lean:43: [(.L 0, .L 0, .C), (.L 0, .C, .C), (.C, .L 0, .C), (.C, .C, .C)] := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCenterGen.lean:45: [(.C, .L 0, .C), (.C, .C, .C), (.L 0, .C, .C)] := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCenterGen.lean:46: have h0 : (eR (aCenter .three 3, aCenter .three 4) 0).length = 1 := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCenterGen.lean:47: have h1 : (eR (aCenter .three 3, aCenter .three 4) 1).length = 1 := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCenterGen.lean:48: have h2 : (eR (aCenter .three 3, aCenter .three 4) 2).length = 0 := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:117: | X => decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:118: | Y => decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:119: | side j => cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:120: | center j => cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:125: | X => decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:126: | Y => decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:127: | side j => cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:128: | center j => cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:130: theorem classEdges_inc_X : ∀ e ∈ classEdges .X, ∀ x ∈ cT e, x ∈ cH e := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:132: theorem classEdges_inc_Y : ∀ e ∈ classEdges .Y, ∀ x ∈ cT e, x ∈ cH e := by decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:135: cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:146: cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:153: cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:156: revert r; cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/CellSoundCommon.lean:159: revert r; cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/Lemma6AbsSum.lean:62: theorem classAbsDimSum_X : classAbsDimSum 100 .X = 999999 := by decide +kernel
SubNLogN/Math/Networks/Proofs/Lemma6AbsSum.lean:65: theorem classAbsDimSum_Y : classAbsDimSum 100 .Y = 999999 := by decide +kernel
SubNLogN/Math/Networks/Proofs/Lemma6AbsSum.lean:69: cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/Lemma6AbsSum.lean:73: cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/TotalsGen.lean:173: lemma classRankC_X : classRankC .X = ⟨8, 12, 6, 1⟩ := by decide +kernel
SubNLogN/Math/Networks/Proofs/TotalsGen.lean:176: lemma classRankC_Y : classRankC .Y = ⟨7, 12, 6, 1⟩ := by decide +kernel
SubNLogN/Math/Networks/Proofs/TotalsGen.lean:180: cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/TotalsGen.lean:184: cases j <;> decide +kernel
SubNLogN/Math/Networks/Proofs/TotalsGen.lean:187: lemma classDimC_X : classDimC .X = ⟨7, 12, 6, 1⟩ := by decide +kernel
SubNLogN/Math/Networks/Proofs/TotalsGen.lean:190: lemma classDimC_Y : classDimC .Y = ⟨7, 12, 6, 1⟩ := by decide +kernel
SubNLogN/Math/Networks/Proofs/TotalsGen.lean:194: cases j <;> decide +kernel
```

## ofReduceBool/ofReduceNat (2 hits; first 40)
```
IntMulTM/Gate.lean:87: def nativeAxioms : Array Name := #[``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]
SubNLogN/Gate.lean:26: def nativeAxioms : Array Name := #[``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]
```

## syntax decl (17 hits; first 40)
```
IntMulTM/Audit/Cone.lean:260: syntax (name := coneReportCmd) "" ident "" ident,* "" : command
IntMulTM/Audit/Cone.lean:264: syntax (name := statementBoundaryCmd) "" ident : command
IntMulTM/Audit/Cone.lean:267: syntax (name := coneExcludesCmd) "" ident "" ident,* "" : command
IntMulTM/Audit/Cone.lean:270: syntax (name := coneIncludesCmd) "" ident "" ident,* "" : command
IntMulTM/Audit/Cone.lean:273: syntax (name := notImportedCmd) "" "" ident,* "" : command
IntMulTM/Gate.lean:514: syntax (name := gateCheckCmd) "" "" ident,* "" : command
IntMulTM/Gate.lean:518: syntax (name := gateModulesCmd) "" (ident <|> str)+ : command
IntMulTM/Gate.lean:522: syntax (name := gateExpectCmd) "" "" ident,* ""
IntMulTM/Gate.lean:527: syntax (name := gateExpectModulesCmd) "" "" ident,* ""
IntMulTM/Gate.lean:532: syntax (name := gateCrossCheckCmd) "" "" ident,* "" : command
IntMulTM/Gate.lean:535: syntax (name := gateCrossCheckModulesCmd) "" "" ident,* "" :
SubNLogN/Gate.lean:393: syntax (name := gateCheckCmd) "" "" ident,* "" : command
SubNLogN/Gate.lean:395: syntax (name := gateModulesCmd) "" (ident <|> str)+ : command
SubNLogN/Gate.lean:397: syntax (name := gateExpectCmd) "" "" ident,* ""
SubNLogN/Gate.lean:400: syntax (name := gateExpectModulesCmd) "" "" ident,* ""
SubNLogN/Gate.lean:403: syntax (name := gateCrossCheckCmd) "" "" ident,* "" : command
SubNLogN/Gate.lean:405: syntax (name := gateCrossCheckModulesCmd) "" "" ident,* "" :
```

## elab decl (6 hits; first 40)
```
AxiomCheck.lean:8: elab "" pfx:ident : command => do
Contracts/AxiomCheck.lean:12: elab "" pfx:ident : command => do
IntMulTM/Audit/Cone.lean:305: elab_rules : command
IntMulTM/Framework/AxiomGuard.lean:23: elab "" ids:ident+ : command => do
IntMulTM/Gate.lean:538: elab_rules : command
SubNLogN/Gate.lean:408: elab_rules : command
```

## notation/infix/prefix/postfix (9 hits; first 40)
```
IntMul/MaterializedAndComputable/ComputableTranscendentals.lean:1525: local notation "" N:arg y:arg =>
IntMul/MaterializedAndComputable/ComputableTranscendentals.lean:1528: local notation "" N:arg y:arg =>
IntMul/MaterializedAndComputable/ComputableTranscendentals.lean:1611: local notation "" N:arg θ:arg =>
IntMul/MaterializedAndComputable/ComputableTranscendentals.lean:1614: local notation "" N:arg θ:arg =>
IntMul/MaterializedAndComputable/ComputableTranscendentals.lean:1617: local notation "" N:arg θ:arg =>
IntMul/MaterializedAndComputable/ComputableTranscendentals.lean:1620: local notation "" N:arg θ:arg =>
IntMul/MaterializedAndComputable/ComputableTranscendentals.lean:1739: local notation "" N:arg θ:arg =>
IntMul/MaterializedAndComputable/ComputableTranscendentals.lean:1848: local notation "" N:arg z:arg =>
WP/W9fM/Move.lean:32: local notation "" => ([] : List (SProg MStk))
```

## run_cmd/run_tac/run_elab (2 hits; first 40)
```
IntMul.lean:1148: run_cmd do
IntMul.lean:1209: run_cmd do
```

## local/scoped instance (83 hits; first 40)
```
Contracts/W9/Leaf.lean:27: attribute [local instance 10000] instZeroIntElementary
Contracts/W9/Leaf.lean:62: attribute [local instance 10000] instZeroIntElementary
Contracts/W9/Post.lean:43: attribute [local instance 10000] instZeroIntElementary
Contracts/W9/Post.lean:218: attribute [local instance 10000] instZeroIntElementary
Contracts/W9/Pre.lean:49: attribute [local instance 10000] instZeroIntElementary
Contracts/W9/Pre.lean:232: attribute [local instance 10000] instZeroIntElementary
Contracts/W9/Root.lean:28: attribute [local instance 10000] instZeroIntElementary
Contracts/W9/Root.lean:76: attribute [local instance 10000] instZeroIntElementary
Contracts/W9/Tables.lean:38: attribute [local instance 10000] instZeroIntElementary
IntMul/MaterializedAndComputable/ComputableTableBuilder.lean:29: attribute [local instance 10000] instZeroIntElementary
IntMul/MaterializedAndComputable/ComputableTranscendentals.lean:16: attribute [local instance 10000] instZeroIntElementary
IntMul/MaterializedAndComputable/PaperHeadlinePipeline.lean:12: attribute [local instance 10000] instZeroIntElementary
IntMul/MaterializedAndComputable/ProgramCostPrimitives.lean:18: attribute [local instance 10000] instZeroIntElementary
LevelSync/Factor.lean:24: attribute [local instance 10000] instZeroIntElementary
LevelSync/Iter.lean:17: attribute [local instance 10000] instZeroIntElementary
LevelSync/Pure.lean:18: attribute [local instance 10000] instZeroIntElementary
LevelSync/Sizes.lean:14: attribute [local instance 10000] instZeroIntElementary
LevelSync/Unroll.lean:24: attribute [local instance 10000] instZeroIntElementary
SubNLogN/Assembly/RootOK.lean:101: attribute [local instance 10000] IntMul.instZeroIntElementary in
SubNLogN/Machine/Bridge/SolveAxisRuns.lean:38: scoped instance instDecEqEPd {Ep Es Em Er Ej Ew : Type} [DecidableEq Ep] [DecidableEq Es]
SubNLogN/Machine/Bridge/SolveAxisRuns.lean:44: scoped instance instDecEqDK {EP : Type} [DecidableEq EP] : DecidableEq (DK EP) :=
SubNLogN/S5/PipeExtended.lean:209: attribute [local instance 10000] IntMul.instZeroIntElementary in
SubNLogN/S5/TopDispatcher.lean:827: attribute [local instance 10000] IntMul.instZeroIntElementary in
WP/F9/MulRun.lean:30: attribute [local instance 10000] instZeroIntElementary
WP/F9/PipeRun.lean:24: attribute [local instance 10000] instZeroIntElementary
WP/F9/PostLevelRun.lean:24: attribute [local instance 10000] instZeroIntElementary
WP/F9/PostLevelRunC.lean:31: attribute [local instance 10000] instZeroIntElementary
WP/F9/PostRun.lean:24: attribute [local instance 10000] instZeroIntElementary
WP/F9/PreBRun.lean:20: attribute [local instance 10000] instZeroIntElementary
WP/F9/PreLevelRun.lean:30: attribute [local instance 10000] instZeroIntElementary
WP/F9/StepPipeRun.lean:33: attribute [local instance 10000] instZeroIntElementary
WP/W11b/Acs.lean:17: attribute [local instance 10000] instZeroIntElementary
WP/W11b/Chain.lean:21: attribute [local instance 10000] instZeroIntElementary
WP/W11b/Column.lean:16: attribute [local instance 10000] instZeroIntElementary
WP/W11b/Defs.lean:19: attribute [local instance 10000] instZeroIntElementary
WP/W11b/Leaf.lean:25: attribute [local instance 10000] instZeroIntElementary
WP/W11b/Main.lean:21: attribute [local instance 10000] instZeroIntElementary
WP/W11b/PostNode.lean:19: attribute [local instance 10000] instZeroIntElementary
WP/W11b/PostOK.lean:17: attribute [local instance 10000] instZeroIntElementary
WP/W11b/PreEq.lean:16: attribute [local instance 10000] instZeroIntElementary
```

## import Lean (5 hits; first 40)
```
AxiomCheck.lean:2: import Lean
Contracts/AxiomCheck.lean:2: import Lean
IntMulTM/Audit/Cone.lean:1: import Lean
IntMulTM/Gate.lean:1: import Lean
SubNLogN/Gate.lean:1: import Lean
```

## Decidable instance decl (8 hits; first 40)
```
SubNLogN/Machine/AppC/C5KitDefs.lean:125: noncomputable instance instDecEqSC : DecidableEq (SC hL) := by
SubNLogN/Machine/AppC/C5KitDefs.lean:142: noncomputable instance instDecEqKE : DecidableEq (KE hL) := instDecidableEqSum
SubNLogN/Machine/AppC/C5KitDefs.lean:144: noncomputable instance instDecEqKK : DecidableEq (KLoc (Fin 6) (KE hL)) := instDecidableEqSum
SubNLogN/Machine/FFT/RoundsRuns.lean:127: instance decEqPCT : DecidableEq (EP ⊕ (EC ⊕ ET)) := instDecidableEqSum
SubNLogN/Machine/FFT/RoundsRuns.lean:128: instance decEqRE : DecidableEq (RE EP EC ET) := instDecidableEqSum
SubNLogN/Machine/FFT/RoundsRuns.lean:129: instance decEqRK : DecidableEq (RK EP EC ET) := instDecidableEqSum
SubNLogN/Machine/Layer/DrvPreProg.lean:65: instance instDecEqQE2 [DecidableEq Epad] [DecidableEq Edsc] : DecidableEq (QE2 Epad Edsc) :=
SubNLogN/Math/Networks/Proofs/Incidence.lean:1145: instance decidableValid : DecidablePred (Gate.Valid (h := h)) := fun g => by
```

## Classical.choice explicit (12 hits; first 40)
```
IntMulTM/Framework/AxiomGuard.lean:20: def stdAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]
IntMulTM/Gate.lean:84: def allowedAxioms : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
SubNLogN/Gate.lean:23: def allowedAxioms : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
SubNLogN/Machine/AppC/C5KitDefs.lean:56: Classical.choice (KPack.nonempty h p)
SubNLogN/Machine/Bridge/PrePostW3.lean:73: noncomputable def theW3Kit : W3Kit := Classical.choice nonempty_W3Kit
SubNLogN/S5/TopDispatcher.lean:357: let σ0 : SubNLogNTopRegs σi Rcore := (Classical.choice hni, Classical.choice hnc, none)
SubNLogN/S5/TopDispatcher.lean:558: (Classical.choice hni, Classical.choice hn7, Classical.choice hnc, Classical.choice hn9, none)
SubNLogN/S5/TopExtended.lean:395: (Classical.choice hni, Classical.choice hn7, Classical.choice hnc, Classical.choice hn9, none)
WP/Top/Main.lean:145: (Classical.choice hni, Classical.choice hn7, Classical.choice hnc, Classical.choice hn9, none) a b
WP/Top/Main.lean:203: (Classical.choice hni, Classical.choice hn7, Classical.choice hnc, Classical.choice hn9, none)
WP/W9fN/Main.lean:32: le_rfl, inferInstance, ⟨(((none, .eq), fun o => Classical.choice (K.good o).2.2),
WP/W9fN/Main.lean:33: Classical.choice IF.ne)⟩, nyqProg_closed K.I (fun o => (K.good o).1) IF, ?_⟩⟩
```
