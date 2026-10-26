import WP.F9.StepRun

/-!
# WP.F9.PostLevelRun — the POST level with the concrete POST node, on a step chain (harness)

`postLevelC colK` is `postLevelA` (W9a's POST level, i.e. `W9_postLevelProg_holds`' witness: sweep,
retFlip). Its node kernel is the concrete POST node (W9e Q2, Q3+Q4, Q6 and the column solver `colK`).
`rowPost` runs it under `runTabledIx` from `PostLevelSpec`'s start state at the POST level of a step
chain:
* `S` holds the children's leaf outputs `levelEvalV child pSub (preNodeV … x)`;
* `RET` holds the `alt_q` segment of `x`;
* `TR` holds the POST segment;
* `C1` holds `pSub`.

It checks every stack against the post-state with snapshot values: `S` holds
`postLevel (postNodeV …) t1 alts ys`, `TL` the reversed POST segment, `RET` and `C1` are popped, and
everything else is restored. The column solver is a parameter until it is concrete.
-/

namespace WP.F9.PostLevelRun

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.F9.MulRun

attribute [local instance 10000] instZeroIntElementary

/-- Arbitrary content. -/
def junkS : List Sym := [.bit true, .tag 9]

/-- Scratch count of a W9 stage program. -/
def mOf {m : ℕ} {σ : Type} (_ : Prog (BLoc m) (fun _ => Sym) σ) : ℕ := m

section Plug

variable {mq : ℕ} {Rq : Type}

/-- The POST level program with the concrete POST node. -/
def postLevelC (colK : Prog (BLoc mq) (fun _ => Sym) Rq) := postLevelA (postNodeC colK)

/-- Its initial registers. -/
def postLevelR0C (r0q : Rq) := postLevelR0 (postNodeR0 WP.W9e.Concrete.Q2.r0C
  WP.W9e.Concrete.Q34.r0C r0q WP.W9e.Concrete.Q6.r0C)

/-- Register normalizer of the POST level (the column solver's registers). -/
def nrPostL {R2 R3 R5 R6 : Type} (nq : R5 → R5) :
    ((WP.W9comp.PostRegs R2 R3 R5 R6 × Option Sym) × (Option Sym × Option Sym)) →
    ((WP.W9comp.PostRegs R2 R3 R5 R6 × Option Sym) × (Option Sym × Option Sym))
  | (((r2, r3, r5, r6, g), o1), o2) => (((r2, r3, nq r5, r6, g), o1), o2)

theorem nrPostL_eq {R2 R3 R5 R6 : Type} (nq : R5 → R5) (h : ∀ v, nq v = v) :
    ∀ v : ((WP.W9comp.PostRegs R2 R3 R5 R6 × Option Sym) × (Option Sym × Option Sym)),
      nrPostL nq v = v
  | (((r2, r3, r5, r6, g), o1), o2) => by simp [nrPostL, h]

/-- Indices (in the key list) of the stacks where `S'` and `E` differ. -/
def diffIx {κ : Type} (S' E : κ → List Sym) : List κ → ℕ → List ℕ
  | [], _ => []
  | k :: ks, i => if S' k == E k then diffIx S' E ks (i + 1) else i :: diffIx S' E ks (i + 1)

/-- The POST-level run on raw data. POST header `(p, pSub, t1, r, pChild)`, tables `c0T`, `c1T`,
retained values `alts` (one per node) and child outputs `ys` (`t1` per node). Returns
`(stacks ok, steps, indices of the stacks that differ)`, or `(false, 0, [])` if out of `fuel`.
`nq` normalizes the column solver's registers (`runTabledIxR`). -/
def rowPostRaw (colK : Prog (BLoc mq) (fun _ => Sym) Rq) (r0q : Rq) (nq : Rq → Rq)
    (p pSub t1 r pChild : ℕ) (c0T c1T : Array (ℤ × ℤ)) (alts : List (ℤ × ℤ))
    (ys : List (Array (ℤ × ℤ))) (fuel : ℕ := 80000000) : Bool × ℕ × List ℕ :=
  let P := postLevelC colK
  let m := mOf P
  let S : BLoc m → List Sym := fun k =>
    match k with
    | .inl .S => streamSyms ys ++ [.tag 9]
    | .inl .W0 => []
    | .inl .TR => postSeg p pSub t1 r c0T c1T pChild ++ [.tag 3, .bit false]
    | .inl .RET => retSeg alts ++ [.tag 4]
    | .inl .C1 => hdrSyms [pSub] ++ [.tag 2]
    | _ => junkS
  let E := Function.update (Function.update (Function.update (Function.update
    (Function.update S (.inl .S)
      (streamSyms (postLevel (postNodeV p pSub t1 r c0T c1T pChild) t1 alts ys) ++ [.tag 9]))
    (.inl .TR) [.tag 3, .bit false])
    (.inl .TL) ((postSeg p pSub t1 r c0T c1T pChild).reverse ++ S (.inl .TL)))
    (.inl .RET) [.tag 4])
    (.inl .C1) [.tag 2]
  let r0 := postLevelR0C r0q
  match runTabledIxR P r0 (keysB m) (ixB m) (nrPostL nq) ⟨r0, S⟩ fuel with
  | none => (false, 0, [])
  | some (n, S') => ((keysB m).all (fun k => S' k == E k), n, diffIx S' E (keysB m) 0)

/-- The POST-level run for root node `x` (with `p_in`) on step chain `cs`. The child outputs are
the snapshot's `levelEvalV child pSub (preNodeV … x)` and the retained value is `altNodeV … x`. -/
def rowPost (colK : Prog (BLoc mq) (fun _ => Sym) Rq) (r0q : Rq) (nq : Rq → Rq)
    (cs : ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ)) (fuel : ℕ := 80000000) :
    Bool × ℕ × List ℕ :=
  match cs with
  | .step p pSub m1 t1 r ft preTw postTw c0T c1T child =>
    rowPostRaw colK r0q nq p pSub t1 r child.p c0T c1T [altNodeV p_in pSub t1 r x]
      (levelEvalV child pSub (preNodeV p_in pSub m1 t1 r ft preTw postTw x).toList) fuel
  | _ => (false, 0, [])

end Plug

end WP.F9.PostLevelRun
