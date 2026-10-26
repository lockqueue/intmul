import WP.F9.StepRun
import WP.W9c.Concrete

/-!
# WP.F9.PreLevelRun — the PRE level with every concrete PRE kernel, run on a step chain

`preLevelC` is `preLevelA` (W9a's PRE level, i.e. `W9_preLevelProg_holds`' witness: sweep, retMark).
Its node kernel is the concrete PRE node with all seven phases, which run inside the real level
program:
* P1, P2, P8: W9b;
* P3: the W9cS driver with the W9c spread row;
* P4, P7: W9d;
* P5: W9s.

The run follows the level's contract (`PreLevelSpec`) under `runTabledIx`. The input is the stream
of nodes on `S` and the PRE segment of the step chain on `TR`. Checked:
* `S` holds the children `preNodeV …`;
* `RET` gets the `alt_q` segment;
* `TL` gets the reversed PRE segment;
* `C1` gets `pSub` pushed;
* every other stack is restored.
All values come from the snapshot.
-/

namespace WP.F9.PreLevelRun

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.F9.MulRun
  WP.F9.StepRun

attribute [local instance 10000] instZeroIntElementary

/-- The concrete PRE node. -/
def preNodeK := preNodeC (WP.W9cS.Concrete.progC WP.W9c.Concrete.progC) WP.W9d.Concrete.Pre.progC
  WP.W9s.Concrete.progC WP.W9d.Concrete.Post.progC

/-- The PRE level program with the concrete node. -/
def preLevelC := preLevelA preNodeK

/-- Its initial registers. -/
def preLevelR0C := preLevelR0 (preNodeR0 WP.W9b.Concrete.P1.r0C WP.W9b.Concrete.P2.r0C
  (WP.W9cS.Concrete.r0C WP.W9c.Concrete.r0C) WP.W9d.Concrete.Pre.r0C WP.W9s.Concrete.r0C
  WP.W9d.Concrete.Post.r0C WP.W9b.Concrete.P8.r0C)

/-- Scratch count of the PRE level. -/
def mOf {m : ℕ} {σ : Type} (_ : Prog (BLoc m) (fun _ => Sym) σ) : ℕ := m

/-- Arbitrary content. -/
def junkS : List Sym := [.bit true, .tag 9]

/-- The PRE-level run on node stream `xs` with `p_in`, at the top level of chain `cs`:
`(stacks ok, steps)`. -/
def rowPre (cs : ComputablePaperFastDFTSpec) (p_in : ℕ) (xs : List (Array (ℤ × ℤ))) : Bool × ℕ :=
  match cs with
  | .step _ pSub m1 t1 r ft preTw postTw _ _ _ =>
    let m := mOf preLevelC
    let S : BLoc m → List Sym := fun k =>
      match k with
      | .inl .S => streamSyms xs ++ [.tag 9]
      | .inl .W0 => []
      | .inl .TR => preSeg pSub m1 t1 r ft preTw postTw ++ [.tag 3, .bit false]
      | .inl .C1 => hdrSyms [p_in] ++ [.tag 2]
      | _ => junkS
    let E := Function.update (Function.update (Function.update (Function.update
      (Function.update S (.inl .S) (streamSyms (xs.flatMap fun x =>
        (preNodeV p_in pSub m1 t1 r ft preTw postTw x).toList) ++ [.tag 9]))
      (.inl .TR) [.tag 3, .bit false])
      (.inl .TL) ((preSeg pSub m1 t1 r ft preTw postTw).reverse ++ S (.inl .TL)))
      (.inl .RET) (retSeg (xs.map (altNodeV p_in pSub t1 r)) ++ S (.inl .RET)))
      (.inl .C1) (hdrSyms [pSub] ++ S (.inl .C1))
    match runTabledIx preLevelC preLevelR0C (keysB m) (ixB m) ⟨preLevelR0C, S⟩ 50000000 with
    | none => (false, 0)
    | some (n, S') => ((keysB m).all (fun k => S' k == E k), n)
  | _ => (false, 0)

/-- One node of size 4 on the step chain `stepChain 12 2` (`t1 = r = 2`). -/
def rows : List (Bool × ℕ) := [rowPre (stepChain 12 2) 1 [#[(3, 0), (-2, 1), (0, 0), (1, -1)]]]

#eval rows

end WP.F9.PreLevelRun
