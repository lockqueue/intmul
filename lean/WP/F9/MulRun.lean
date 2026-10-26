import WP.F9.Pipe
import WP.F9.Run

/-!
# WP.F9.MulRun — harness for runs of the W9 multiplier (`W9_multiply`'s contract)

`runMul P r0 cSpec b K0 k1 k2 A B` runs a `W9_multiply`-shaped program under `runTabled`, from the
contract's start state:
* `OA = natSyms A ++ rA`, `OB = natSyms B ++ rB`;
* `C0 = hdrSyms [b, K0, k1, k2] ++ r0`;
* `W0 = []`;
* `TR = tapeSyms cSpec ++ restT`, where `restT` starts with a non-POST tag;
* every other stack, scratch included, holds junk.

It reports three things:
* whether every stack after the run equals the contract's post-state, i.e.
  `OA = natSyms (computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B) ++ rA`, `OB = rB`, and all
  else restored;
* whether that snapshot value is `A * B`;
* the steps.

`leafSpec p K` is a leaf-only chain (`.basePow2`, tables from the snapshot's computable builder).
On it only the LEAF level of the pipeline runs (WP.F9.Pipe).
-/

namespace WP.F9.MulRun

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 9]

/-- All stacks of `BLoc m`. -/
def keysB (m : ℕ) : List (BLoc m) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2,
    .inl .C3, .inl .OA, .inl .OB] ++ (List.finRange m).map Sum.inr

/-- Start stacks of `W9_multiply`. -/
def mulSt0 (m : ℕ) (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ) : BLoc m → List Sym
  | .inl .OA => natSyms A ++ [.mark]
  | .inl .OB => natSyms B ++ [.mark, .bit true]
  | .inl .C0 => hdrSyms [b, K0, k1, k2] ++ [.tag 2]
  | .inl .W0 => []
  | .inl .TR => tapeSyms cSpec ++ [.tag 3, .bit false]
  | _ => junk

/-- Post-state of `W9_multiply`. -/
def mulExp (m : ℕ) (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ) : BLoc m → List Sym :=
  let S := mulSt0 m cSpec b K0 k1 k2 A B
  Function.update (Function.update S (.inl .OA)
    (natSyms (computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B) ++ [.mark])) (.inl .OB)
    [.mark, .bit true]

/-- Run: `(all stacks as the contract says, snapshot value = A·B, steps)`. -/
def runMul {m : ℕ} {σ : Type} (P : Prog (BLoc m) (fun _ => Sym) σ) (r0 : σ)
    (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B fuel : ℕ) : Bool × Bool × ℕ :=
  let E := mulExp m cSpec b K0 k1 k2 A B
  match runTabled P r0 (keysB m) ⟨r0, mulSt0 m cSpec b K0 k1 k2 A B⟩ fuel with
  | none => (false, false, 0)
  | some (n, S') => ((keysB m).all (fun k => S' k == E k),
      computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B == A * B, n)

/-- Index of a named W9 stack (the order of `keysB`). -/
def ixLB : LB → ℕ
  | .S => 0 | .W0 => 1 | .TL => 2 | .TR => 3 | .RET => 4 | .RQ => 5 | .C0 => 6 | .C1 => 7
  | .C2 => 8 | .C3 => 9 | .OA => 10 | .OB => 11

/-- Index of a W9 stack (the order of `keysB`). -/
def ixB (m : ℕ) : BLoc m → ℕ
  | .inl l => ixLB l
  | .inr j => 12 + j.val

/-- `keysB` is indexed by `ixB` (the hypothesis of `runTabledIx_sound` / `_of_eval`). -/
theorem keysB_ix (m : ℕ) : ∀ k : BLoc m, (keysB m)[ixB m k]? = some k
  | .inl l => by cases l <;> rfl
  | .inr j => by
    unfold keysB ixB
    rw [List.getElem?_append_right (by simp)]
    simp

/-- As `runMul`, with the indexed runner `runTabledIx`. -/
def runMulIx {m : ℕ} {σ : Type} (P : Prog (BLoc m) (fun _ => Sym) σ) (r0 : σ)
    (cSpec : ComputablePaperFastDFTSpec) (b K0 k1 k2 A B fuel : ℕ) : Bool × Bool × ℕ :=
  let E := mulExp m cSpec b K0 k1 k2 A B
  match runTabledIx P r0 (keysB m) (ixB m) ⟨r0, mulSt0 m cSpec b K0 k1 k2 A B⟩ fuel with
  | none => (false, false, 0)
  | some (n, S') => ((keysB m).all (fun k => S' k == E k),
      computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B == A * B, n)

/-- A leaf-only chain of size `2^K` and precision `p` (snapshot's computable table builder). -/
def leafSpec (p K : ℕ) : ComputablePaperFastDFTSpec := buildComputablePaperTables (.base p (2 ^ K))

#assert_std_axioms keysB_ix

end WP.F9.MulRun
