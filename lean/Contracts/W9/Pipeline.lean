import Contracts.W9.Levels
import Contracts.W9.Root
import Contracts.Machine.W3
import Contracts.Machine.W5
import Contracts.Machine.W6a

/-!
# Contracts.W9.Pipeline — the composed level-synchronous transform and multiplier

This is the interface that W10 (cost) and W11 (refinement) consume.

* `W9_pipeline Mul`: **one** program with the following behaviour, for **every** chain spec
  `cSpec` (schedule-parametric; the program reads the schedule from the table tape `tapeSyms cSpec`,
  so W14's paper schedule is an instance), every input precision `p_in`, and every list of root
  nodes `xs`. It maps the level stream `⟦xs⟧` on `S` to `⟦levelEvalV cSpec p_in xs⟧`
  (`= ⟦xs.map (computablePaperFastDFT p_in cSpec)⟧`, by `pipeline_out_eq_map`). Every other stack is
  restored (table head, RET/RQ, counters, scratch). The cost is `C · (pipeBound … + |tape| + 1)`,
  where `pipeBound` is the **sum over levels** of the per-level bounds of Levels.lean:
  `M_ℓ ×` the per-node kernel bound, plus the sweep traffic.
* `W9_multiply Mul`: the root composite. It maps `A` on `OA` and `B` on `OB` to the snapshot's
  `computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B` on `OA`, at cost
  `C·(rootBound + pipeBound(forward) + pipeBound(inverse) + |tape| + 1)`. With
  `W8_machineInterface` (proved) the result is `A * B` for any faithful table hierarchy.
* Assembly statements (Props, to be proved by W9): how these follow from the stage contracts.

**Hypotheses.** `ChainOK wd cSpec p_in 0 xs` collects, level by level along the chain, the
following:
* power-of-two dimensions;
* table widths, real POST coefficients (`hC01`), and node sizes;
* the G-OPSIZE width bounds `wd ℓ` (`PreNodeOK`, `PostNodeOK`, `LeafOK`), including
  `SpreadStrideOK`;
* the W8 'Left to W9' column hypotheses (`ColumnOK` inside `PostNodeOK`).

Each is evaluated on the actual level data (`preNodeV` images going down, `levelEvalV` images coming
up).
-/

namespace TMFw.Contracts

namespace W9

open IntMul IntMul.LevelSync

/-! ## Generic level evaluation (the pure image of `W9_level`) -/

/-- One step level as pure operations. -/
structure LevelOps where
  t1 : ℕ
  pre : Array (ℤ × ℤ) → Array (Array (ℤ × ℤ))
  alt : Array (ℤ × ℤ) → ℤ × ℤ
  post : ℤ × ℤ → Array (Array (ℤ × ℤ)) → Array (ℤ × ℤ)

/-- Level-synchronous evaluation of a chain of step levels and a leaf map. -/
def genEval : List LevelOps → (Array (ℤ × ℤ) → Array (ℤ × ℤ)) → List (Array (ℤ × ℤ)) →
    List (Array (ℤ × ℤ))
  | [], leaf, xs => xs.map leaf
  | o :: os, leaf, xs =>
      postLevel o.post o.t1 (xs.map o.alt) (genEval os leaf (xs.flatMap fun x => (o.pre x).toList))

/-- The step levels of a chain spec, top-down (each level's `p_in` is the parent's `pSub`). -/
def opsOf : ComputablePaperFastDFTSpec → ℕ → List LevelOps
  | .basePow2 _ _ _, _ => []
  | .step p pSub m1 t1 r ft preTw postTw c0T c1T child, p_in =>
      ⟨t1, preNodeV p_in pSub m1 t1 r ft preTw postTw, altNodeV p_in pSub t1 r,
        postNodeV p pSub t1 r c0T c1T child.p⟩ :: opsOf child pSub

/-- The leaf map of a chain spec. -/
def leafOf : ComputablePaperFastDFTSpec → ℕ → Array (ℤ × ℤ) → Array (ℤ × ℤ)
  | .basePow2 p K tw, p_in => fun x => (computableBaseRadix2FFTWithProgramCost p_in p K tw x).1
  | .step _ pSub _ _ _ _ _ _ _ _ child, _ => leafOf child pSub

/-- **The generic evaluation of the chain is levelsync's `levelEvalV`** (proved). So the
`W9_level` rule, instantiated with the level contracts, yields the `W9_pipeline` value. -/
theorem genEval_opsOf : ∀ (cSpec : ComputablePaperFastDFTSpec) (p_in : ℕ)
    (xs : List (Array (ℤ × ℤ))), genEval (opsOf cSpec p_in) (leafOf cSpec p_in) xs =
      levelEvalV cSpec p_in xs
  | .basePow2 _ _ _, _, _ => rfl
  | .step p pSub m1 t1 r ft preTw postTw c0T c1T child, p_in, xs => by
    simp only [opsOf, leafOf, genEval, levelEvalV]
    rw [genEval_opsOf child pSub]

/-! ## Hypotheses and cost along the chain -/

/-- **Pipeline hypotheses**, level by level (`ℓ` is the depth, `wd ℓ` the level's working width). -/
def ChainOK (wd : ℕ → ℕ) : ComputablePaperFastDFTSpec → ℕ → ℕ → List (Array (ℤ × ℤ)) → Prop
  | .basePow2 p K tw, p_in, ℓ, xs =>
      LeafTwW (wd ℓ) K tw ∧ ∀ x ∈ xs, x.size = 2 ^ K ∧ LeafOK (wd ℓ) p_in p K tw x
  | .step p pSub m1 t1 r ft preTw postTw c0T c1T child, p_in, ℓ, xs =>
      PreDims ⟨p_in, pSub, m1, t1, r⟩ ∧ PreTablesW (wd ℓ) m1 t1 r ft preTw postTw ∧
        PostTablesW (barrettH pSub) r c0T c1T ∧
        (∀ x ∈ xs, x.size = t1 * r ∧ PreNodeOK (wd ℓ) ⟨p_in, pSub, m1, t1, r⟩ ft preTw postTw x) ∧
        (∀ i < xs.length, PostNodeOK (wd ℓ) ⟨p, pSub, t1, r, child.p⟩ c0T c1T
          (altNodeV p_in pSub t1 r (xs.getD i #[]))
          (groupAt t1 (levelEvalV child pSub
            (xs.flatMap fun x => (preNodeV p_in pSub m1 t1 r ft preTw postTw x).toList)) i).toArray) ∧
        ChainOK wd child pSub (ℓ + 1)
          (xs.flatMap fun x => (preNodeV p_in pSub m1 t1 r ft preTw postTw x).toList)

/-- **Total cost bound: the sum over levels** of the per-level bounds (PRE and POST of every step
level, the LEAF level, and `O(1)` per level for the level loop). `M` is the number of nodes at depth
`ℓ` (`M·t1` at depth `ℓ+1`). -/
def pipeBound (Mul : ℕ → ℕ) (wd : ℕ → ℕ) : ComputablePaperFastDFTSpec → ℕ → ℕ → ℕ → ℕ
  | .basePow2 p K _, p_in, ℓ, M => leafLevelBound Mul (wd ℓ) p_in p K M + 1
  | .step p pSub m1 t1 r _ _ _ _ _ child, p_in, ℓ, M =>
      preLevelBound Mul (wd ℓ) (wd (ℓ + 1)) ⟨p_in, pSub, m1, t1, r⟩ M +
        postLevelBound Mul (wd ℓ) (wd (ℓ + 1)) ⟨p, pSub, t1, r, child.p⟩ M + 2 +
        pipeBound Mul wd child pSub (ℓ + 1) (M * t1)

/-- The pipeline output is the snapshot transform mapped over the root nodes (from levelsync's
`levelEvalV_eq_map`). -/
theorem pipeline_out_eq_map (cSpec : ComputablePaperFastDFTSpec) (p_in : ℕ)
    (xs : List (Array (ℤ × ℤ))) :
    streamSyms (levelEvalV cSpec p_in xs) = streamSyms (xs.map (computablePaperFastDFT p_in cSpec)) := by
  rw [levelEvalV_eq_map]

/-- Root hypotheses: chain hypotheses for both transforms, sizes and root widths. -/
def RootOK (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ) (wdF wdI : ℕ → ℕ) (wR : ℕ) :
    Prop :=
  ChainOK wdF cSpec b 0 [rootPackV b K0 k1 k2 A B] ∧
    ChainOK wdI cSpec (rootPrecision b K0) 0
      [rootSquareV (rootPrecision b K0) K0 (computablePaperFastDFT b cSpec (rootPackV b K0 k1 k2 A B))] ∧
    (computablePaperFastDFT b cSpec (rootPackV b K0 k1 k2 A B)).size = 2 ^ K0 ∧
    ArrW wR (rootPackV b K0 k1 k2 A B) ∧
    ArrW wR (computablePaperFastDFT b cSpec (rootPackV b K0 k1 k2 A B)) ∧
    ArrW wR (rootSquareV (rootPrecision b K0) K0
      (computablePaperFastDFT b cSpec (rootPackV b K0 k1 k2 A B))) ∧
    (computablePaperFastDFT (rootPrecision b K0) cSpec (rootSquareV (rootPrecision b K0) K0
      (computablePaperFastDFT b cSpec (rootPackV b K0 k1 k2 A B)))).size = 2 ^ K0 ∧
    ArrW wR (computablePaperFastDFT (rootPrecision b K0) cSpec (rootSquareV (rootPrecision b K0) K0
      (computablePaperFastDFT b cSpec (rootPackV b K0 k1 k2 A B)))) ∧
    ∀ c ∈ rootDigits b K0 k1 k2 (computablePaperFastDFT (rootPrecision b K0) cSpec
      (rootSquareV (rootPrecision b K0) K0
        (computablePaperFastDFT b cSpec (rootPackV b K0 k1 k2 A B)))), bitLen c ≤ wR

end W9

open W9 IntMul IntMul.LevelSync

/-! ## The pipeline and the multiplier -/

/-- **W9.pipeline (the level-synchronous transform).** There is one program `P` with one constant
`C` such that, for every chain spec `cSpec`, `p_in`, width profile `wd` and root nodes `xs`
satisfying `ChainOK`, with the table tape at the head and `p_in` on top of `C1`, it holds that
`stream(S) := ⟦levelEvalV cSpec p_in xs⟧`. All other stacks are restored. The cost is
`C·(Σ_levels bound + |tape| + 1)`.
* The symbol after the tape must not be a POST tag, so the ascent loop of `W9_level` stops at the
  tape end. W7 delivers `TR = T` exactly, so `restT = []`.
* The table head is restored by pushing `symGuard` on `TL` before the first level and, after the
  last POST level, rewinding the whole tape down to it. `TL`'s old content is arbitrary. -/
def W9_pipeline (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (cSpec : ComputablePaperFastDFTSpec) (p_in : ℕ) (wd : ℕ → ℕ) (xs : List (Array (ℤ × ℤ)))
      (σ : BLoc m → List Sym) (restS restT r1 : List Sym),
      ChainOK wd cSpec p_in 0 xs →
      σ (.inl .S) = streamSyms xs ++ restS → σ (.inl .W0) = [] →
      σ (.inl .TR) = tapeSyms cSpec ++ restT → restT.head? ≠ some symPost →
      σ (.inl .C1) = hdrSyms [p_in] ++ r1 →
      Runs P σ (Function.update σ (.inl .S) (streamSyms (levelEvalV cSpec p_in xs) ++ restS))
        (fun _ => True) (C * (pipeBound Mul wd cSpec p_in 0 xs.length + (tapeSyms cSpec).length + 1))

/-- **W9.multiply (the root composite).** It maps `OA = A`, `OB = B` (consumed) to
`OA = computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B`, with the root parameters on `C0` and
the table tape at the head. All other stacks are restored. -/
def W9_multiply (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ) (wdF wdI : ℕ → ℕ) (wR : ℕ)
      (σ : BLoc m → List Sym) (rA rB r0 restT : List Sym),
      A < 2 ^ (b * k1) → B < 2 ^ (b * k2) → k1 + k2 ≤ 2 ^ K0 → TermOK rA → TermOK rB →
      RootOK cSpec b K0 k1 k2 A B wdF wdI wR →
      σ (.inl .OA) = natSyms A ++ rA → σ (.inl .OB) = natSyms B ++ rB →
      σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 → σ (.inl .W0) = [] →
      σ (.inl .TR) = tapeSyms cSpec ++ restT → restT.head? ≠ some symPost →
      Runs P σ (Function.update (Function.update σ (.inl .OA)
          (natSyms (computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B) ++ rA)) (.inl .OB) rB)
        (fun _ => True)
        (C * (rootBound Mul wR b K0 k1 k2 + pipeBound Mul wdF cSpec b 0 1 +
          pipeBound Mul wdI cSpec (rootPrecision b K0) 0 1 + (tapeSyms cSpec).length + 1))

/-! ## Assembly statements (Props; W9 proves them) -/

/-- PRE node kernel from its phases (P1–P8) and the RET push. -/
def W9_preNode_of_phases (Mul : ℕ → ℕ) : Prop :=
  W9_preTranspose → W9_altSum → W9_spread Mul → W9_preTwist Mul → W9_synFFT → W9_postTwist Mul →
    W9_emitRows → W9_preNode Mul

/-- POST node kernel from its phases (Q2–Q6). `W9_columns` performs the node's RQ pop. -/
def W9_postNode_of_phases (Mul : ℕ → ℕ) : Prop :=
  W9_postTranspose → W9_columnRoutes → W9_columns Mul → W9_postOutput → W9_postNode Mul

/-- Level programs from the sweep, the RET operations and the node kernels. -/
def W9_levels_of_kernels (Mul : ℕ → ℕ) : Prop :=
  W9_sweep → W9_retMark → W9_retFlip → W9_preNode Mul → W9_leafFFT Mul → W9_postNode Mul →
    W9_preLevelProg Mul ∧ W9_leafLevelProg Mul ∧ W9_postLevelProg Mul

/-- The pipeline from the level driver and the level programs. The value step is `genEval_opsOf`. -/
def W9_pipeline_of_levels (Mul : ℕ → ℕ) : Prop :=
  W9_level → W9_preLevelProg Mul → W9_leafLevelProg Mul → W9_postLevelProg Mul → W9_pipeline Mul

/-- The multiplier from the pipeline and the root stages. The value step is
`multiply_eq_root_phases` plus `levelEvalV_eq_map`. -/
def W9_multiply_of_parts (Mul : ℕ → ℕ) : Prop :=
  W9_pipeline Mul → W9_splitPack → W9_square Mul → W9_extract → W9_reconstruct → W9_multiply Mul

/-- All frozen W3 contracts (the kernels may use any of them). -/
def W3_all : Prop :=
  W3_copyNat ∧ W3_dropNat ∧ W3_normNat ∧ W3_isZeroNat ∧ W3_cmpNat ∧ W3_addNat ∧ W3_subNat ∧
    W3_shlConst ∧ W3_shrConst ∧ W3_shlVar ∧ W3_shrVar ∧ W3_splitAt ∧ W3_concatAt ∧ W3_incNat ∧
    W3_decNat ∧ W3_dec_amortised ∧ W3_natToInt ∧ W3_attachSign ∧ W3_splitSign ∧ W3_negInt ∧
    W3_signInt ∧ W3_addInt ∧ W3_subInt ∧ W3_cmpInt ∧ W3_smallOpInt

/-- The W4 routing contracts in the level-synchronous stream orientation (`.down` throughout). -/
def W4_all : Prop :=
  W4_transpose .down .down ∧ W4_oddStrideFactor ∧ W4_oddRoute .down .down ∧ W4_moveRecord

/-- The W6a division contracts (class-B boundary divisions of the column solvers). -/
def W6a_all : Prop := W6a_divModNat ∧ W6a_divRound

/-- **Kernels from the machine-contract hypotheses** (W9's composition obligation). From
W3, W4, W6a and W5, every W9 kernel holds, with `Mul := T3 c0 c1 w0` for **one** triple of W5
constants shared by all multiplication kernels. A single `Mul` then flows into `W9_pipeline Mul`. -/
def W9_kernels_of_machine : Prop :=
  W3_all → W4_all → W6a_all → W5_toom3Mul → ∃ c0 c1 w0 : ℕ,
    W9_preTranspose ∧ W9_altSum ∧ W9_spread (T3 c0 c1 w0) ∧ W9_preTwist (T3 c0 c1 w0) ∧
      W9_synFFT ∧ W9_postTwist (T3 c0 c1 w0) ∧ W9_emitRows ∧
      W9_postTranspose ∧ W9_columnRoutes ∧ W9_columns (T3 c0 c1 w0) ∧ W9_postOutput ∧
      W9_leafFFT (T3 c0 c1 w0) ∧
      W9_splitPack ∧ W9_square (T3 c0 c1 w0) ∧ W9_extract ∧ W9_reconstruct ∧
      W9_retFlip ∧ W9_sweep ∧ W9_level

#assert_std_axioms genEval_opsOf pipeline_out_eq_map

end TMFw.Contracts
