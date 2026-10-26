import WP.F9.StepRun
import WP.W9c.Concrete
import WP.W9f.Concrete

/-!
# WP.F9.StepPipeRun — the W9 pipeline with every node kernel, run on a step-level chain

`pipeC` is the pipeline component of `P9C` (WP.F9.Top):
* PRE level with the concrete PRE node (all seven phases);
* LEAF level with the concrete leaf FFT;
* POST level with the concrete POST node (W9e Q2, Q3+Q4, Q6 and the W9f columns Q5).

On `stepChain 12 2` (one PRE, one LEAF and one POST level; `t1 = r = 2`) the run executes **every
node kernel inside the real pipeline**. It runs under `runTabledIxR`, i.e. the framework machine:
`runTabledIxR_sound`, with the column registers normalized by W9f's `normColsC`, proved the identity.

Start state of `W9_pipeline`:
* `S = streamSyms xs ++ restS`;
* `W0 = []`;
* `TR = tapeSyms cSpec ++ restT`;
* `C1 = hdrSyms [p_in] ++ r1`;
* junk elsewhere.

Check: `S = streamSyms (levelEvalV cSpec p_in xs) ++ restS` (the snapshot), and every other stack
restored.
-/

namespace WP.F9.StepPipeRun

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.F9.MulRun
  WP.F9.StepRun

attribute [local instance 10000] instZeroIntElementary

/-- The concrete PRE node. -/
def preNodeK := preNodeC (WP.W9cS.Concrete.progC WP.W9c.Concrete.progC) WP.W9d.Concrete.Pre.progC
  WP.W9s.Concrete.progC WP.W9d.Concrete.Post.progC

/-- The pipeline with every kernel concrete. -/
def pipeC := pipeA (preLevelA preNodeK) (leafLevelA WP.W9gx.Concrete.progC)
  (postLevelA (postNodeC WP.W9f.Concrete.progColsC))

/-- Its initial registers. -/
def pipeR0C := pipeR0
  (preLevelR0 (preNodeR0 WP.W9b.Concrete.P1.r0C WP.W9b.Concrete.P2.r0C
    (WP.W9cS.Concrete.r0C WP.W9c.Concrete.r0C) WP.W9d.Concrete.Pre.r0C WP.W9s.Concrete.r0C
    WP.W9d.Concrete.Post.r0C WP.W9b.Concrete.P8.r0C))
  (leafLevelR0 WP.W9gx.Concrete.r0C)
  (postLevelR0 (postNodeR0 WP.W9e.Concrete.Q2.r0C WP.W9e.Concrete.Q34.r0C
    WP.W9f.Concrete.r0ColsC WP.W9e.Concrete.Q6.r0C))

/-- Register normalizer of the pipeline (the column solver's registers). -/
def nrPipe {A B R2 R3 R5 R6 : Type} (nq : R5 → R5) :
    (((A × (B × ((WP.W9comp.PostRegs R2 R3 R5 R6 × Option Sym) × (Option Sym × Option Sym)))) ×
      Option Sym) × Option Sym) →
    (((A × (B × ((WP.W9comp.PostRegs R2 R3 R5 R6 × Option Sym) × (Option Sym × Option Sym)))) ×
      Option Sym) × Option Sym)
  | (((a, (b, (((r2, r3, r5, r6, g), o1), o2))), q1), q2) =>
    (((a, (b, (((r2, r3, nq r5, r6, g), o1), o2))), q1), q2)

theorem nrPipe_eq {A B R2 R3 R5 R6 : Type} (nq : R5 → R5) (h : ∀ v, nq v = v) :
    ∀ v : (((A × (B × ((WP.W9comp.PostRegs R2 R3 R5 R6 × Option Sym) ×
      (Option Sym × Option Sym)))) × Option Sym) × Option Sym), nrPipe nq v = v
  | (((a, (b, (((r2, r3, r5, r6, g), o1), o2))), q1), q2) => by simp [nrPipe, h]

/-- Scratch count of a W9 stage program. -/
def mOf {m : ℕ} {σ : Type} (_ : Prog (BLoc m) (fun _ => Sym) σ) : ℕ := m

/-- The pipeline run on chain `cs` with `p_in` and node stream `xs`: `(stacks ok, steps)`. -/
def rowPipe (cs : ComputablePaperFastDFTSpec) (p_in : ℕ) (xs : List (Array (ℤ × ℤ))) : Bool × ℕ :=
  let m := mOf pipeC
  let S : BLoc m → List Sym := fun k =>
    match k with
    | .inl .S => streamSyms xs ++ [.tag 9]
    | .inl .W0 => []
    | .inl .TR => tapeSyms cs ++ [.tag 3, .bit false]
    | .inl .C1 => hdrSyms [p_in] ++ [.tag 2]
    | _ => junk
  let E := Function.update S (.inl .S) (streamSyms (levelEvalV cs p_in xs) ++ [.tag 9])
  match runTabledIxR pipeC pipeR0C (keysB m) (ixB m) (nrPipe WP.W9f.Concrete.normColsC)
      ⟨pipeR0C, S⟩ 200000000 with
  | none => (false, 0)
  | some (n, S') => ((keysB m).all (fun k => S' k == E k), n)

/-- One node of size 4 on the step chain `stepChain 12 2`, with `p_in = 1`. -/
def rows : List (Bool × ℕ) := [rowPipe (stepChain 12 2) 1 [#[(3, 0), (-2, 1), (0, 0), (1, -1)]]]

-- `#eval rows` runs every node kernel inside the real pipeline and returns `(stacks ok, steps)`.
-- It is not run here, because in the Lean interpreter it takes far longer than the 900 s build cap
-- (exceeding the `#eval` timeout). The PRE level alone takes about 5M steps (`WP.F9.PreLevelRun`).
-- The POST level of `stepChain 12 2` (pSub = 56, H = 170) does not finish within 7M steps
-- (`WP.F9.PostLevelRunC`, which runs the POST level at a small header instead).

end WP.F9.StepPipeRun
