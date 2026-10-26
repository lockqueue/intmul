import LevelSync.Unroll

/-!
# Level-synchronous evaluation, part 4: size invariants for the machine encoding

The machine stores a level as a stream of nodes with exactly `N` entries each. These lemmas give
the sizes that the encoding invariant needs; none of them is needed by `levelEval_eq_map` itself.
-/

namespace IntMul.LevelSync

open IntMul

attribute [local instance 10000] instZeroIntElementary

/-- Node size of a level spec. -/
def cSize : ComputablePaperFastDFTSpec → ℕ
  | .basePow2 _ K _ => 2 ^ K
  | .step _ _ _ t1 r _ _ _ _ _ _ => t1 * r

/-- Leaf outputs have `2 ^ K` entries. -/
theorem leaf_output_size (p_in p K : ℕ) (twiddles : Array (Array (ℤ × ℤ)))
    (xArr : Array (ℤ × ℤ)) :
    (computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr).1.size = 2 ^ K := by
  simp [computableBaseRadix2FFTWithProgramCost]

/-- Every node output has the level's node size. -/
theorem computablePaperFastDFT_size : ∀ (spec : ComputablePaperFastDFTSpec) (p_in : ℕ)
    (xArr : Array (ℤ × ℤ)), (computablePaperFastDFT p_in spec xArr).size = cSize spec
  | .basePow2 p K twiddles, p_in, xArr => leaf_output_size p_in p K twiddles xArr
  | .step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child, p_in, xArr => by
    rw [computablePaperFastDFT_step_eq, postNode_size]
    rfl

/-- Level outputs: every node has the level's node size. -/
theorem levelEval_size (spec : ComputablePaperFastDFTSpec) (p_in : ℕ)
    (xs : List (Array (ℤ × ℤ))) : ∀ y ∈ levelEval spec p_in xs, y.size = cSize spec := by
  rw [levelEval_eq_map]
  intro y hy
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
  exact computablePaperFastDFT_size spec p_in x

/-- The PRE map produces exactly `t1` children per node. -/
theorem preLevel_length (p_in pSub m1 t1 r : ℕ) (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles : Array (ℤ × ℤ)) (xs : List (Array (ℤ × ℤ))) :
    (preLevel p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles xs).length =
      xs.length * t1 := by
  induction xs with
  | nil => simp [preLevel]
  | cons x xs ih =>
    simp only [preLevel] at ih ⊢
    simp only [List.flatMap_cons, List.length_append, Array.length_toList, preNode_size, ih,
      List.length_cons]
    ring

/-- Every child input produced by the PRE map has exactly `r` entries. -/
theorem preLevel_size (p_in pSub m1 t1 r : ℕ) (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles : Array (ℤ × ℤ)) (xs : List (Array (ℤ × ℤ))) :
    ∀ y ∈ preLevel p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles xs, y.size = r := by
  intro y hy
  simp only [preLevel, List.mem_flatMap, Array.mem_toList_iff] at hy
  obtain ⟨x, -, hyx⟩ := hy
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hyx
  have hit : i < t1 := by
    rwa [preNode_size] at hi
  have h := preNode_row_size p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles x i hit
  simpa [Array.getD, hi] using h

end IntMul.LevelSync

#print axioms IntMul.LevelSync.computablePaperFastDFT_size
#print axioms IntMul.LevelSync.levelEval_size
#print axioms IntMul.LevelSync.preLevel_length
#print axioms IntMul.LevelSync.preLevel_size
