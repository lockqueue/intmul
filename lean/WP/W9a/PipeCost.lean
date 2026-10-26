import WP.W9a.Chain

/-!
# WP.W9a.PipeCost — the per-level costs of a chain and their sum

For a chain `s`, input precision `p`, first level index `ℓ0` and root nodes `xs`:
* `preB … ℓ` and `postB … ℓ` are the PRE and POST level bounds at depth `ℓ` plus the segment
  length (`0` at the leaf);
* `leafB` is the LEAF level bound plus the leaf segment length.

`chain_cost`: the sum over all levels is at most `pipeBound … + |tapeSyms s|`.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability IntMul IntMul.LevelSync

/-- PRE cost at depth `ℓ`, without the contract constant. -/
def preB (Mul wd : ℕ → ℕ) (s : ComputablePaperFastDFTSpec) (p ℓ0 : ℕ)
    (xs : List (Array (ℤ × ℤ))) (ℓ : ℕ) : ℕ :=
  match specAt s ℓ with
  | .basePow2 _ _ _ => 0
  | .step _ pSub m1 t1 r ft preTw postTw _ _ _ =>
      preLevelBound Mul (wd (ℓ0 + ℓ)) (wd (ℓ0 + ℓ + 1)) ⟨pinAt s p ℓ, pSub, m1, t1, r⟩
        (xsAt s p xs ℓ).length + (preSeg pSub m1 t1 r ft preTw postTw).length

/-- POST cost at depth `ℓ`, without the contract constant. -/
def postB (Mul wd : ℕ → ℕ) (s : ComputablePaperFastDFTSpec) (p ℓ0 : ℕ)
    (xs : List (Array (ℤ × ℤ))) (ℓ : ℕ) : ℕ :=
  match specAt s ℓ with
  | .basePow2 _ _ _ => 0
  | .step q pSub _ t1 r _ _ _ c0T c1T child =>
      postLevelBound Mul (wd (ℓ0 + ℓ)) (wd (ℓ0 + ℓ + 1)) ⟨q, pSub, t1, r, child.p⟩
        (xsAt s p xs ℓ).length + (postSeg q pSub t1 r c0T c1T child.p).length

/-- LEAF cost, without the contract constant. -/
def leafB (Mul wd : ℕ → ℕ) (s : ComputablePaperFastDFTSpec) (p ℓ0 : ℕ)
    (xs : List (Array (ℤ × ℤ))) : ℕ :=
  match specAt s (depthOf s) with
  | .basePow2 q K tw =>
      leafLevelBound Mul (wd (ℓ0 + depthOf s)) (pinAt s p (depthOf s)) q K
        (xsAt s p xs (depthOf s)).length + (leafSeg q K tw).length
  | .step _ _ _ _ _ _ _ _ _ _ _ => 0

section At

variable {Mul wd : ℕ → ℕ} {s : ComputablePaperFastDFTSpec} {p ℓ0 : ℕ} {xs : List (Array (ℤ × ℤ))}
  {ℓ q pSub m1 t1 r K : ℕ} {ft : Array (List ℤ)} {preTw postTw c0T c1T : Array (ℤ × ℤ)}
  {child : ComputablePaperFastDFTSpec} {tw : Array (Array (ℤ × ℤ))}

theorem preB_at (h : specAt s ℓ = .step q pSub m1 t1 r ft preTw postTw c0T c1T child) :
    preB Mul wd s p ℓ0 xs ℓ = preLevelBound Mul (wd (ℓ0 + ℓ)) (wd (ℓ0 + ℓ + 1))
      ⟨pinAt s p ℓ, pSub, m1, t1, r⟩ (xsAt s p xs ℓ).length +
        (preSeg pSub m1 t1 r ft preTw postTw).length := by
  simp only [preB, h]

theorem postB_at (h : specAt s ℓ = .step q pSub m1 t1 r ft preTw postTw c0T c1T child) :
    postB Mul wd s p ℓ0 xs ℓ = postLevelBound Mul (wd (ℓ0 + ℓ)) (wd (ℓ0 + ℓ + 1))
      ⟨q, pSub, t1, r, child.p⟩ (xsAt s p xs ℓ).length +
        (postSeg q pSub t1 r c0T c1T child.p).length := by
  simp only [postB, h]

theorem leafB_at (h : specAt s (depthOf s) = .basePow2 q K tw) :
    leafB Mul wd s p ℓ0 xs = leafLevelBound Mul (wd (ℓ0 + depthOf s)) (pinAt s p (depthOf s)) q K
      (xsAt s p xs (depthOf s)).length + (leafSeg q K tw).length := by
  simp only [leafB, h]

end At

section Shift

variable (Mul wd : ℕ → ℕ) (q pSub m1 t1 r : ℕ) (ft : Array (List ℤ))
  (preTw postTw c0T c1T : Array (ℤ × ℤ)) (child : ComputablePaperFastDFTSpec) (p ℓ0 : ℕ)
  (xs : List (Array (ℤ × ℤ)))

theorem preB_zero :
    preB Mul wd (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p ℓ0 xs 0 =
      preLevelBound Mul (wd ℓ0) (wd (ℓ0 + 1)) ⟨p, pSub, m1, t1, r⟩ xs.length +
        (preSeg pSub m1 t1 r ft preTw postTw).length := by
  simp only [preB, specAt_zero, pinAt_zero, xsAt_zero, Nat.add_zero]

theorem postB_zero :
    postB Mul wd (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p ℓ0 xs 0 =
      postLevelBound Mul (wd ℓ0) (wd (ℓ0 + 1)) ⟨q, pSub, t1, r, child.p⟩ xs.length +
        (postSeg q pSub t1 r c0T c1T child.p).length := by
  simp only [postB, specAt_zero, xsAt_zero, Nat.add_zero]

theorem preB_succ (i : ℕ) :
    preB Mul wd (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p ℓ0 xs (i + 1) =
      preB Mul wd child pSub (ℓ0 + 1)
        (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList) i := by
  simp only [preB, specAt_succ_step, pinAt_succ_step, xsAt_succ_step,
    show ℓ0 + (i + 1) = ℓ0 + 1 + i by omega]

theorem postB_succ (i : ℕ) :
    postB Mul wd (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p ℓ0 xs (i + 1) =
      postB Mul wd child pSub (ℓ0 + 1)
        (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList) i := by
  simp only [postB, specAt_succ_step, xsAt_succ_step, show ℓ0 + (i + 1) = ℓ0 + 1 + i by omega]

theorem leafB_step :
    leafB Mul wd (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p ℓ0 xs =
      leafB Mul wd child pSub (ℓ0 + 1)
        (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList) := by
  simp only [leafB, depthOf, specAt_succ_step, pinAt_succ_step, xsAt_succ_step,
    show ℓ0 + (depthOf child + 1) = ℓ0 + 1 + depthOf child by omega]

theorem length_tapeSyms_step :
    (tapeSyms (.step q pSub m1 t1 r ft preTw postTw c0T c1T child)).length =
      (preSeg pSub m1 t1 r ft preTw postTw).length + (tapeSyms child).length +
        (postSeg q pSub t1 r c0T c1T child.p).length := by
  simp only [tapeSyms, preSegs, leafSegOf, postSegsUp, List.length_append]
  omega

end Shift

theorem leafB_base (Mul wd : ℕ → ℕ) (q K : ℕ) (tw : Array (Array (ℤ × ℤ))) (p ℓ0 : ℕ)
    (xs : List (Array (ℤ × ℤ))) :
    leafB Mul wd (.basePow2 q K tw) p ℓ0 xs =
      leafLevelBound Mul (wd ℓ0) p q K xs.length + (leafSeg q K tw).length := by
  simp only [leafB, depthOf, specAt_zero, pinAt_zero, xsAt_zero, Nat.add_zero]

/-- **The level costs sum to the pipeline bound.** -/
theorem chain_cost (Mul wd : ℕ → ℕ) : ∀ (s : ComputablePaperFastDFTSpec) (p ℓ0 : ℕ)
    (xs : List (Array (ℤ × ℤ))),
    sumTo (depthOf s) (preB Mul wd s p ℓ0 xs) + leafB Mul wd s p ℓ0 xs +
        sumTo (depthOf s) (postB Mul wd s p ℓ0 xs) ≤
      pipeBound Mul wd s p ℓ0 xs.length + (tapeSyms s).length
  | .basePow2 q K tw, p, ℓ0, xs => by
    rw [leafB_base]
    simp only [depthOf, sumTo_zero, pipeBound, tapeSyms, preSegs, leafSegOf, postSegsUp,
      List.nil_append, List.append_nil]
    omega
  | .step q pSub m1 t1 r ft preTw postTw c0T c1T child, p, ℓ0, xs => by
    have ih := chain_cost Mul wd child pSub (ℓ0 + 1)
      (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList)
    rw [length_flatMap_preNodeV] at ih
    have e1 : sumTo (depthOf child + 1)
        (preB Mul wd (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p ℓ0 xs) =
        preB Mul wd (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p ℓ0 xs 0 +
          sumTo (depthOf child) (preB Mul wd child pSub (ℓ0 + 1)
            (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList)) := by
      rw [sumTo_succ', sumTo_congr
        (fun i => preB Mul wd (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p ℓ0 xs (i + 1))
        (preB Mul wd child pSub (ℓ0 + 1)
          (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList)) _
        (fun i _ => preB_succ Mul wd q pSub m1 t1 r ft preTw postTw c0T c1T child p ℓ0 xs i)]
    have e2 : sumTo (depthOf child + 1)
        (postB Mul wd (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p ℓ0 xs) =
        postB Mul wd (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p ℓ0 xs 0 +
          sumTo (depthOf child) (postB Mul wd child pSub (ℓ0 + 1)
            (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList)) := by
      rw [sumTo_succ', sumTo_congr
        (fun i => postB Mul wd (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) p ℓ0 xs (i + 1))
        (postB Mul wd child pSub (ℓ0 + 1)
          (xs.flatMap fun x => (preNodeV p pSub m1 t1 r ft preTw postTw x).toList)) _
        (fun i _ => postB_succ Mul wd q pSub m1 t1 r ft preTw postTw c0T c1T child p ℓ0 xs i)]
    have hd : depthOf (.step q pSub m1 t1 r ft preTw postTw c0T c1T child) = depthOf child + 1 := by
      simp only [depthOf]
    rw [hd, e1, e2, leafB_step, preB_zero, postB_zero, length_tapeSyms_step]
    simp only [pipeBound]
    omega

#assert_std_axioms preB_at postB_at leafB_at preB_zero postB_zero preB_succ postB_succ leafB_step
  length_tapeSyms_step leafB_base chain_cost

end WP.W9a
