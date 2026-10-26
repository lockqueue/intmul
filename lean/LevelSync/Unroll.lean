import LevelSync.Factor

/-!
# Level-synchronous evaluation, part 2: `levelEval` and the unrolling lemma (W9-L strategy B)

`levelEval spec p_in xs` evaluates the snapshot's pipeline **level by level** over a list `xs` of
node inputs (one level of the recursion tree, canonical node order):

* PRE map (`preLevel`): every node's `preNode`, children inputs concatenated node-major;
* RET segment (`altLevel`): every node's retained `alt_q`, in node order;
* recursion down the chain spec on the whole next level (`levelEval child pSub`);
* LEAF map at `.basePow2`;
* POST map (`postLevel`): pops the retained values in FIFO order, one per parent, and consumes
  `t1` consecutive child outputs per parent.

Main result: `levelEval_eq_map : levelEval spec p_in xs = xs.map (computablePaperFastDFT p_in spec)`,
unconditionally (no size hypotheses on `xs`).
-/

namespace IntMul.LevelSync

open IntMul

attribute [local instance 10000] instZeroIntElementary

/-- POST map of one level: pops the retained values in FIFO order (one per parent node) and
consumes `t1` consecutive child outputs per parent node. -/
def postLevel (post : ℤ × ℤ → Array (Array (ℤ × ℤ)) → Array (ℤ × ℤ)) (t1 : ℕ) :
    List (ℤ × ℤ) → List (Array (ℤ × ℤ)) → List (Array (ℤ × ℤ))
  | [], _ => []
  | a :: as, zs => post a (zs.take t1).toArray :: postLevel post t1 as (zs.drop t1)

/-- PRE map of one level: the next level's node inputs in canonical order
(node `i`, child `v1` ↦ position `i * t1 + v1`). -/
def preLevel (p_in pSub m1 t1 r : ℕ) (filterTaps : Array (List ℤ))
    (preTwiddles postTwiddles : Array (ℤ × ℤ)) (xs : List (Array (ℤ × ℤ))) :
    List (Array (ℤ × ℤ)) :=
  xs.flatMap (fun x => (preNode p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles x).toList)

/-- Retained values of one level (the RET segment), in canonical node order. -/
def altLevel (p_in pSub t1 r : ℕ) (xs : List (Array (ℤ × ℤ))) : List (ℤ × ℤ) :=
  xs.map (altNode p_in pSub t1 r)

/-- **Level-synchronous evaluation** over a list of node inputs. -/
def levelEval : ComputablePaperFastDFTSpec → ℕ → List (Array (ℤ × ℤ)) → List (Array (ℤ × ℤ))
  | .basePow2 p K twiddles, p_in, xs =>
      xs.map (fun x => (computableBaseRadix2FFTWithProgramCost p_in p K twiddles x).1)
  | .step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child, p_in, xs =>
      postLevel (postNode p pSub t1 r c0Table c1Table child.p) t1
        (altLevel p_in pSub t1 r xs)
        (levelEval child pSub (preLevel p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles xs))

/-- Chunk algebra: the POST map undoes a node-major concatenation of `t1`-element blocks. -/
theorem postLevel_flatMap {α : Type} (post : ℤ × ℤ → Array (Array (ℤ × ℤ)) → Array (ℤ × ℤ))
    (t1 : ℕ) (alt : α → ℤ × ℤ) (G : α → Array (Array (ℤ × ℤ))) (hG : ∀ x, (G x).size = t1) :
    ∀ xs : List α, postLevel post t1 (xs.map alt) (xs.flatMap (fun x => (G x).toList)) =
      xs.map (fun x => post (alt x) (G x))
  | [] => rfl
  | x :: xs => by
    have hlen : (G x).toList.length = t1 := by simp [hG x]
    simp only [List.map_cons, List.flatMap_cons, postLevel]
    rw [List.take_left' hlen, List.drop_left' hlen, postLevel_flatMap post t1 alt G hG xs]
    -- closes by `rfl`: `Array.toArray_toList` is definitional

/-- **Unrolling lemma.** Level-synchronous evaluation of a whole level equals the snapshot's
recursive node function mapped over the level's nodes. -/
theorem levelEval_eq_map : ∀ (spec : ComputablePaperFastDFTSpec) (p_in : ℕ)
    (xs : List (Array (ℤ × ℤ))), levelEval spec p_in xs = xs.map (computablePaperFastDFT p_in spec)
  | .basePow2 p K twiddles, p_in, xs => rfl
  | .step p pSub m1 t1 r filterTaps preTwiddles postTwiddles c0Table c1Table child, p_in, xs => by
    simp only [levelEval, preLevel, altLevel]
    rw [levelEval_eq_map child pSub, List.map_flatMap]
    have hrow : ∀ x : Array (ℤ × ℤ),
        (preNode p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles x).toList.map
            (computablePaperFastDFT pSub child) =
          ((preNode p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles x).map
            (computablePaperFastDFT pSub child)).toList := by
      intro x
      simp
    simp only [hrow]
    rw [postLevel_flatMap _ t1 (altNode p_in pSub t1 r)
      (fun x => (preNode p_in pSub m1 t1 r filterTaps preTwiddles postTwiddles x).map
        (computablePaperFastDFT pSub child))
      (fun x => by simp [preNode_size])]
    apply List.map_congr_left
    intro x _
    rw [computablePaperFastDFT_step_eq]

/-- Root-level corollary (`M = 1`): the machine's level-synchronous run on the single root node
computes the snapshot's transform. -/
theorem levelEval_singleton (spec : ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ)) :
    levelEval spec p_in [x] = [computablePaperFastDFT p_in spec x] := by
  rw [levelEval_eq_map]
  rfl

end IntMul.LevelSync

#print axioms IntMul.LevelSync.computablePaperFastDFT_step_eq
#print axioms IntMul.LevelSync.levelEval_eq_map
#print axioms IntMul.LevelSync.levelEval_singleton
#print axioms IntMul.LevelSync.preNode_row_size
#print axioms IntMul.LevelSync.postNode_size
