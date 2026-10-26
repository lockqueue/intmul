import LevelSync.Unroll

/-!
# Level-synchronous evaluation, part 3: the iterative (loop-shaped) schedule

A machine whose level control is two `while` loops (descend: PRE sweeps root → leaf, then the
LEAF sweep, then ascend: POST sweeps leaf → root) instead of `fix`/`recur` over levels computes
`runIter`. Its stack of pending levels corresponds, on the machine, to the RET segments (`alts`)
plus the table-tape segments (`spec`). `runIter_eq_levelEval` is the fold lemma; together with
`levelEval_eq_map` it is the correctness spec of the iterative machine.
-/

namespace IntMul.LevelSync

open IntMul

attribute [local instance 10000] instZeroIntElementary

/-- A pending level: its (step) spec, whose tables live on the table tape, and its RET segment. -/
structure Pending where
  spec : ComputablePaperFastDFTSpec
  alts : List (ℤ × ℤ)

/-- The POST sweep of a pending level. -/
def Pending.post (P : Pending) (zs : List (Array (ℤ × ℤ))) : List (Array (ℤ × ℤ)) :=
  match P.spec with
  | .step p pSub _ t1 r _ _ _ c0Table c1Table child =>
      postLevel (postNode p pSub t1 r c0Table c1Table child.p) t1 P.alts zs
  | .basePow2 _ _ _ => zs

/-- Descending loop (PRE sweeps, root → leaf). Returns the pending levels innermost-first, the leaf
level's node inputs, the leaf spec and the leaf's `p_in`. -/
def descend : ComputablePaperFastDFTSpec → ℕ → List (Array (ℤ × ℤ)) →
    List Pending × List (Array (ℤ × ℤ)) × ComputablePaperFastDFTSpec × ℕ
  | .basePow2 p K twiddles, p_in, xs => ([], xs, .basePow2 p K twiddles, p_in)
  | .step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child, p_in, xs =>
      let d := descend child pSub
        (preLevel p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles xs)
      (d.1 ++ [⟨.step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child,
                altLevel p_in pSub t1 r xs⟩], d.2)

/-- Ascending loop (POST sweeps, leaf → root). -/
def ascend : List Pending → List (Array (ℤ × ℤ)) → List (Array (ℤ × ℤ))
  | [], zs => zs
  | P :: Ps, zs => ascend Ps (P.post zs)

/-- The LEAF sweep (the second case never occurs: `descend` always stops at a leaf). -/
def leafSweep : ComputablePaperFastDFTSpec → ℕ → List (Array (ℤ × ℤ)) → List (Array (ℤ × ℤ))
  | .basePow2 p K twiddles, p_in, xs =>
      xs.map (fun x => (computableBaseRadix2FFTWithProgramCost p_in p K twiddles x).1)
  | .step _ _ _ _ _ _ _ _ _ _ _, _, xs => xs

/-- The iterative schedule: descend, leaf, ascend. -/
def runIter (spec : ComputablePaperFastDFTSpec) (p_in : ℕ) (xs : List (Array (ℤ × ℤ))) :
    List (Array (ℤ × ℤ)) :=
  let d := descend spec p_in xs
  ascend d.1 (leafSweep d.2.2.1 d.2.2.2 d.2.1)

theorem ascend_append (Ps Qs : List Pending) (zs : List (Array (ℤ × ℤ))) :
    ascend (Ps ++ Qs) zs = ascend Qs (ascend Ps zs) := by
  induction Ps generalizing zs with
  | nil => rfl
  | cons P Ps ih => exact ih (P.post zs)

/-- **Fold lemma**: the iterative (two-loop) schedule computes `levelEval`. -/
theorem runIter_eq_levelEval : ∀ (spec : ComputablePaperFastDFTSpec) (p_in : ℕ)
    (xs : List (Array (ℤ × ℤ))), runIter spec p_in xs = levelEval spec p_in xs
  | .basePow2 p K twiddles, p_in, xs => rfl
  | .step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child, p_in, xs => by
    have ih := runIter_eq_levelEval child pSub
      (preLevel p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles xs)
    simp only [runIter] at ih ⊢
    simp only [descend, ascend_append]
    rw [ih]
    rfl

/-- Correctness spec of the iterative machine schedule. -/
theorem runIter_eq_map (spec : ComputablePaperFastDFTSpec) (p_in : ℕ)
    (xs : List (Array (ℤ × ℤ))) :
    runIter spec p_in xs = xs.map (computablePaperFastDFT p_in spec) := by
  rw [runIter_eq_levelEval, levelEval_eq_map]

end IntMul.LevelSync

#print axioms IntMul.LevelSync.runIter_eq_levelEval
#print axioms IntMul.LevelSync.runIter_eq_map
