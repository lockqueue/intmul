import WP.W9a.Basic
import Contracts.W9.Ret

/-!
# WP.W9a.Ret — the RET → RQ flip (`W9_retFlip`)

`retFlipProg = moveUntil RET RQ (= #)`: the level's segment `retSeg alts = (blkE alts).reverse ++ #`
is moved symbol by symbol onto `RQ`, which restores canonical order and orientation
(`blkE alts`); the bottom marker `#` is popped into the register. Entries contain no tag, so the
first `#` from the top is the segment's own. Cost `3·|blkE alts| + 2 ≤ 3·(|retSeg alts| + 1)`.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

/-- The flip program (no scratch). -/
def retFlipProg : SProg (BLoc 0) := moveUntil (.inl .RET) (.inl .RQ) (isSym symRet)

theorem retSeg_eq (alts : List (ℤ × ℤ)) : retSeg alts = (blkE alts).reverse ++ [symRet] := rfl

theorem length_retSeg (alts : List (ℤ × ℤ)) : (retSeg alts).length = (blkE alts).length + 1 := by
  rw [retSeg_eq, List.length_append, List.length_reverse, List.length_singleton]

theorem W9_retFlip_holds : W9_retFlip := by
  refine ⟨3, fun _ => ⟨0, Option Sym, retFlipProg, Nat.zero_le _, inferInstance, ⟨none⟩,
    closed_moveUntil _ _ _, ?_⟩⟩
  intro alts ret σ hRET
  have hne : (.inl .RET : BLoc 0) ≠ .inl .RQ := by simp
  have hd : ∀ x ∈ (blkE alts).reverse, isSym symRet (some x) = false := by
    intro x hx
    refine isSym_some_of_ne (fun e => ?_)
    have hx' := List.mem_reverse.1 hx
    rw [e] at hx'
    exact tag_not_mem_blkE 2 alts hx'
  have hS : σ (.inl .RET) = (blkE alts).reverse ++ symRet :: ret := by
    rw [hRET, retSeg_eq, List.append_assoc]
    rfl
  refine Runs.of_eval fun v => ⟨some symRet, _,
    (moveUntil_eval hne (isSym symRet) v (blkE alts).reverse (symRet :: ret) σ hd
      (isSym_some_self _) hS).of_eq (by rw [List.reverse_reverse]; rfl) rfl, trivial, ?_⟩
  rw [length_retSeg, List.length_reverse]
  omega

#assert_std_axioms retSeg_eq length_retSeg W9_retFlip_holds

end WP.W9a
