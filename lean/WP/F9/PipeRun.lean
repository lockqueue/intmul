import WP.F9.MulRun
import WP.W9gx.Concrete

/-!
# WP.F9.PipeRun — the W9 pipeline on leaf-only chains, run

`pipeLeaf` is the generic pipeline `pipeA` (WP.F9.Assemble), i.e. `W9_pipeline_of_levels_holds`'s
witness. Its LEAF level carries the concrete leaf kernel `WP.W9gx.Concrete.progC`. The
PRE/POST node slots hold `holeB`, which is never executed on a leaf-only chain: the tape has no
PRE/POST segments.

The run follows `W9_pipeline`'s contract under `runTabled`:
* start: `S = streamSyms xs ++ restS`, `W0 = []`, `TR = tapeSyms cSpec ++ restT`,
  `C1 = hdrSyms [p_in] ++ r1`, and junk on every other stack (scratch included);
* check: `S = streamSyms (levelEvalV cSpec p_in xs) ++ restS` with the snapshot value, and every
  other stack restored. The run therefore exercises the level driver, the guard/rewind, the sweep
  (load, group, emit) and the leaf kernel.
-/

namespace WP.F9.PipeRun

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.F9.MulRun

attribute [local instance 10000] instZeroIntElementary

/-- The pipeline with the concrete leaf kernel. -/
def pipeLeaf := pipeA (preLevelA holeB) (leafLevelA WP.W9gx.Concrete.progC) (postLevelA holeB)

/-- Its initial registers. -/
def pipeLeafR0 := pipeR0 (preLevelR0 ()) (leafLevelR0 WP.W9gx.Concrete.r0C) (postLevelR0 ())

/-- Scratch count of `pipeLeaf`. -/
abbrev mP : ℕ := max (max (max (max 0 0) 4) (max 56 4)) (max (max 0 0) 4)

/-- Start stacks of `W9_pipeline`. -/
def st0 (cSpec : ComputablePaperFastDFTSpec) (p_in : ℕ) (xs : List (Array (ℤ × ℤ))) :
    BLoc mP → List Sym
  | .inl .S => streamSyms xs ++ [.tag 9]
  | .inl .W0 => []
  | .inl .TR => tapeSyms cSpec ++ [.tag 3, .bit false]
  | .inl .C1 => hdrSyms [p_in] ++ [.tag 2]
  | _ => junk

/-- Run: `(all stacks as specified, steps)`. -/
def row (cSpec : ComputablePaperFastDFTSpec) (p_in : ℕ) (xs : List (Array (ℤ × ℤ))) : Bool × ℕ :=
  let S := st0 cSpec p_in xs
  let E := Function.update S (.inl .S) (streamSyms (levelEvalV cSpec p_in xs) ++ [.tag 9])
  match runTabled pipeLeaf pipeLeafR0 (keysB mP) ⟨pipeLeafR0, S⟩ 5000000 with
  | none => (false, 0)
  | some (n, S') => ((keysB mP).all (fun k => S' k == E k), n)

def rows : List (Bool × ℕ) :=
  [row (leafSpec 3 0) 2 [#[(5, -3)]],
   row (leafSpec 3 1) 2 [#[(5, -3), (7, 2)]],
   row (leafSpec 3 1) 2 [#[(1, 0), (0, 1)], #[(-2, 3), (4, -1)]]]

-- Pipeline on leaf-only chains: `(stacks ok, steps)`.
#eval rows
#guard rows.all (·.1)

end WP.F9.PipeRun
