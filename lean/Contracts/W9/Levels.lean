import Contracts.W9.Sweep
import Contracts.W9.Pre
import Contracts.W9.Post
import Contracts.W9.Leaf
import Contracts.W9.Ret

/-!
# Contracts.W9.Levels — one PRE, LEAF or POST level as a single program

A level program is what `W9_level` iterates. Each one does the following:
* read the segment header from the tape onto `C0`, and set the sweep's group size on `C2`;
* PRE only: push `#` on RET (`W9_retMark`); POST only: flip the level's RET segment onto RQ
  (`W9_retFlip`);
* run `W9_sweep` with the node kernel (`W9_preNode`, `W9_leafFFT` or `W9_postNode`);
* skip the segment body (the head ends at the next segment, TS5), pop `C0` and `C2`, and update the
  precision stack `C1`: PRE pushes `pSub` (the next level's `p_in`), POST pops it.

The value of each level is levelsync's pure level map: `preLevel`/`altLevel` (as `flatMap`/`map` of
`preNodeV`/`altNodeV`), the leaf map, and `postLevel (postNodeV …)`. The cost is
`M ×` the per-node bound, plus the sweep overhead in entries × `eb` of the level widths, plus the
segment length. Widths: `w` is level ℓ's working width and `w'` the width of the stream that the
level hands to (PRE) or receives from (POST) level ℓ+1.
-/

namespace TMFw.Contracts

namespace W9

open IntMul IntMul.LevelSync

/-- PRE level bound for `M` nodes: kernels plus sweep traffic (input `M·N` entries, output `M·t1·r`
entries). -/
def preLevelBound (Mul : ℕ → ℕ) (w w' : ℕ) (h : PreHdr) (M : ℕ) : ℕ :=
  M * preNodeBound Mul w h + M * (h.N * eb w + 1) + M * h.t1 * (h.r * eb w' + 1) + M * eb w + 1

/-- LEAF level bound for `M` nodes. -/
def leafLevelBound (Mul : ℕ → ℕ) (w p_in p K : ℕ) (M : ℕ) : ℕ :=
  M * leafNodeBound Mul w p_in p K + 2 * M * (2 ^ K * eb w + 1) + 1

/-- POST level bound for `M` parent nodes. The input is `M·t1` child outputs of `r` entries, the
output `M` nodes of `N` entries, and the RET → RQ flip moves `M` alts. -/
def postLevelBound (Mul : ℕ → ℕ) (w w' : ℕ) (h : PostHdr) (M : ℕ) : ℕ :=
  M * postNodeBound Mul w h + M * h.t1 * (h.r * eb w' + 1) + M * (h.N * eb w + 1) +
    M * (eb w + 1) * (h.mt1 + 1) + 1

end W9

open W9 IntMul IntMul.LevelSync

/-- **W9.preLevelProg (PRE(ℓ)).** It maps the level stream `⟦xs⟧` to `⟦xs.flatMap preNodeV⟧`
(levelsync `preLevel`, canonical order: node `i`, child `v1` ↦ `i·t1 + v1`). It pushes the RET
segment `retSeg (xs.map altNodeV)` (levelsync `altLevel`), moves the head from the segment tag to
the next segment, and pushes `pSub` on the precision stack. -/
def W9_preLevelProg (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PreHdr) (w w' : ℕ) (ft : Array (List ℤ)) (preTw postTw : Array (ℤ × ℤ))
      (xs : List (Array (ℤ × ℤ))) (σ : BLoc m → List Sym) (restS restT r1 : List Sym),
      PreDims h → PreTablesW w h.m1 h.t1 h.r ft preTw postTw →
      (∀ x ∈ xs, x.size = h.N ∧ PreNodeOK w h ft preTw postTw x) →
      StreamW w' (xs.flatMap fun x => (preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x).toList) →
      σ (.inl .S) = streamSyms xs ++ restS → σ (.inl .W0) = [] →
      σ (.inl .TR) = preSeg h.pSub h.m1 h.t1 h.r ft preTw postTw ++ restT →
      σ (.inl .C1) = hdrSyms [h.p_in] ++ r1 →
      Runs P σ
        (Function.update (Function.update (Function.update (Function.update (Function.update σ
          (.inl .S) (streamSyms (xs.flatMap fun x =>
            (preNodeV h.p_in h.pSub h.m1 h.t1 h.r ft preTw postTw x).toList) ++ restS))
          (.inl .TR) restT)
          (.inl .TL) ((preSeg h.pSub h.m1 h.t1 h.r ft preTw postTw).reverse ++ σ (.inl .TL)))
          (.inl .RET) (retSeg (xs.map (altNodeV h.p_in h.pSub h.t1 h.r)) ++ σ (.inl .RET)))
          (.inl .C1) (hdrSyms [h.pSub] ++ σ (.inl .C1)))
        (fun _ => True)
        (C * (preLevelBound Mul w w' h xs.length + (preSeg h.pSub h.m1 h.t1 h.r ft preTw postTw).length))

/-- **W9.leafLevelProg (LEAF).** It maps `⟦xs⟧` to `⟦xs.map leaf⟧` and moves the head across the
leaf segment. -/
def W9_leafLevelProg (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (p_in p K w : ℕ) (tw : Array (Array (ℤ × ℤ))) (xs : List (Array (ℤ × ℤ)))
      (σ : BLoc m → List Sym) (restS restT r1 : List Sym),
      LeafTwW w K tw → (∀ x ∈ xs, x.size = 2 ^ K ∧ LeafOK w p_in p K tw x) →
      σ (.inl .S) = streamSyms xs ++ restS → σ (.inl .W0) = [] →
      σ (.inl .TR) = leafSeg p K tw ++ restT → σ (.inl .C1) = hdrSyms [p_in] ++ r1 →
      Runs P σ
        (Function.update (Function.update (Function.update σ
          (.inl .S) (streamSyms (xs.map fun x =>
            (computableBaseRadix2FFTWithProgramCost p_in p K tw x).1) ++ restS))
          (.inl .TR) restT)
          (.inl .TL) ((leafSeg p K tw).reverse ++ σ (.inl .TL)))
        (fun _ => True)
        (C * (leafLevelBound Mul w p_in p K xs.length + (leafSeg p K tw).length))

/-- **W9.postLevelProg (POST(ℓ)).**
* Input: `M·t1` child outputs `ys` on `S`, and level ℓ's RET segment `retSeg alts` on top of RET.
* It flips the segment to RQ, then runs the sweep with `g = t1`.
* Output: `⟦postLevel (postNodeV …) t1 alts ys⟧`. The segment is consumed, the head is moved
  across the POST segment, and `pSub` is popped from the precision stack. -/
def W9_postLevelProg (Mul : ℕ → ℕ) : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (h : PostHdr) (w w' : ℕ) (c0T c1T : Array (ℤ × ℤ)) (alts : List (ℤ × ℤ))
      (ys : List (Array (ℤ × ℤ))) (σ : BLoc m → List Sym) (restS restT ret r1 : List Sym),
      PostDims h → PostTablesW h.H h.r c0T c1T → ys.length = h.t1 * alts.length →
      (∀ y ∈ ys, y.size = h.r) → StreamW w' ys → (∀ a ∈ alts, EntryW w a) →
      (∀ i < alts.length,
        PostNodeOK w h c0T c1T (alts.getD i (0, 0)) (groupAt h.t1 ys i).toArray) →
      σ (.inl .S) = streamSyms ys ++ restS → σ (.inl .W0) = [] →
      σ (.inl .TR) = postSeg h.p h.pSub h.t1 h.r c0T c1T h.pChild ++ restT →
      σ (.inl .RET) = retSeg alts ++ ret → σ (.inl .C1) = hdrSyms [h.pSub] ++ r1 →
      Runs P σ
        (Function.update (Function.update (Function.update (Function.update (Function.update σ
          (.inl .S) (streamSyms (postLevel (postNodeV h.p h.pSub h.t1 h.r c0T c1T h.pChild) h.t1
            alts ys) ++ restS))
          (.inl .TR) restT)
          (.inl .TL) ((postSeg h.p h.pSub h.t1 h.r c0T c1T h.pChild).reverse ++ σ (.inl .TL)))
          (.inl .RET) ret)
          (.inl .C1) r1)
        (fun _ => True)
        (C * (postLevelBound Mul w w' h alts.length +
          (postSeg h.p h.pSub h.t1 h.r c0T c1T h.pChild).length))

end TMFw.Contracts
