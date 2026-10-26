import Contracts.W9.Common

/-!
# Contracts.W9.Ret — the level LIFO stack `RET` of retained Nyquist sums `alt_q`

* PRE(ℓ) first pushes `#` (`W9_retMark`). Then each node pushes its `alt_q` **reversed**
  (`W9_retPush`: the record is moved symbol by symbol from the kernel workspace, which reverses it).
  After the level, `RET = blk .up ⟦alts⟧ ++ # ++ R` (`retSeg`).
* POST(ℓ) starts with level ℓ's segment on top: deeper segments were pushed later and have been
  consumed by POST(ℓ+1..D−1). `W9_retFlip` moves the segment to RQ symbol by symbol. That restores
  canonical order and normal orientation, `RQ = blk .down ⟦alts⟧ ++ RQ` (FIFO), and pops `#`.
* Node `i` of POST(ℓ) then reads `alt_i` from the top of RQ (Nyquist column) and pops it. That
  pop is part of `W9_columns` (Post.lean); `W9_rqPop` is the stand-alone primitive (move to `W0`).

`W9_retMark`, `W9_retPush` and `W9_rqPop` are **proved** here, as non-vacuity witnesses for the
`BContract` shape. `W9_retPush` and `W9_rqPop` reuse W4's proved `moveRec`. `W9_retFlip` is stated
only (it moves symbols down to `#`, the first tag from the top).
-/

namespace TMFw.Contracts

namespace W9

/-- RET segment of one PRE level: the alts reversed and in reverse order (last on top), then `#`. -/
def retSeg (alts : List (ℤ × ℤ)) : List Sym := blk .up (alts.map entrySyms) ++ [symRet]

end W9

open W9

/-- **W9.retMark.** Push `#` on RET (start of a PRE level's segment). Cost `C`. -/
def W9_retMark : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ σ : BLoc m → List Sym,
      Runs P σ (Function.update σ (.inl .RET) (symRet :: σ (.inl .RET))) (fun _ => True) C

/-- **W9.retPush.** Move the record `⟦alt⟧` on top of `W0` to RET. One transfer reverses it.
Cost `C·(|⟦alt⟧| + 1)`. -/
def W9_retPush : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (a : ℤ × ℤ) (rest : List Sym) (σ : BLoc m → List Sym),
      σ (.inl .W0) = entrySyms a ++ rest →
      Runs P σ (Function.update (Function.update σ (.inl .W0) rest) (.inl .RET)
          ((entrySyms a).reverse ++ σ (.inl .RET))) (fun _ => True)
        (C * ((entrySyms a).length + 1))

/-- **W9.retFlip.** Move level ℓ's RET segment to RQ in canonical order, normal orientation, and pop
`#`. Cost `C·(|segment| + 1)`. -/
def W9_retFlip : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (alts : List (ℤ × ℤ)) (ret : List Sym) (σ : BLoc m → List Sym),
      σ (.inl .RET) = retSeg alts ++ ret →
      Runs P σ (Function.update (Function.update σ (.inl .RET) ret) (.inl .RQ)
          (blkE alts ++ σ (.inl .RQ))) (fun _ => True)
        (C * ((retSeg alts).length + 1))

/-- **W9.rqPop.** Pop `⟦alt⟧` from RQ into the workspace `W0` (reversed). Cost `C·(|⟦alt⟧| + 1)`. -/
def W9_rqPop : Prop :=
  BContract Unit w9Scratch fun _ m _ C P =>
    ∀ (a : ℤ × ℤ) (rest : List Sym) (σ : BLoc m → List Sym),
      σ (.inl .RQ) = entrySyms a ++ rest →
      Runs P σ (Function.update (Function.update σ (.inl .RQ) rest) (.inl .W0)
          ((entrySyms a).reverse ++ σ (.inl .W0))) (fun _ => True)
        (C * ((entrySyms a).length + 1))

/-! ## Proved instances -/

theorem w9_retMark : W9_retMark := by
  refine ⟨1, fun _ => ⟨0, Unit, .push (.inl .RET) (fun _ => symRet), Nat.zero_le _, inferInstance,
    ⟨()⟩, ?_, ?_⟩⟩
  · simp [Prog.Closed, Prog.FreeBelow]
  · intro σ
    exact Runs.of_eval fun v => ⟨v, 1, Eval.push _ _ _ _ _, trivial, le_refl _⟩

/-- Moving one entry record between two distinct named stacks (W4's `moveRec`). -/
theorem moveEntry_runs {m : ℕ} (src dst : LB) (hne : src ≠ dst) (a : ℤ × ℤ) (rest : List Sym)
    (σ : BLoc m → List Sym) (hS : σ (.inl src) = entrySyms a ++ rest) :
    Runs (moveRec (.inl src : BLoc m) (.inl dst)) σ
      (Function.update (Function.update σ (.inl src) rest) (.inl dst)
        ((entrySyms a).reverse ++ σ (.inl dst))) (fun _ => True) (3 * ((entrySyms a).length + 1)) := by
  obtain ⟨d, hd, hdd⟩ := entrySyms_recOK a
  have hne' : (.inl src : BLoc m) ≠ .inl dst := fun h => hne (Sum.inl_injective h)
  refine Runs.of_eval fun v => ⟨some Sym.sep, _,
    (moveRec_eval (src := .inl src) (dst := .inl dst) hne' v d rest σ hdd
      (by rw [hS, hd, List.append_assoc, List.singleton_append])).of_eq ?_ rfl, trivial, ?_⟩
  · simp [hd, List.reverse_append]
  · simp only [hd, List.length_append, List.length_singleton]
    omega

theorem w9_retPush : W9_retPush := by
  refine ⟨3, fun _ => ⟨0, Option Sym, moveRec (.inl .W0) (.inl .RET), Nat.zero_le _,
    inferInstance, ⟨none⟩, ?_, ?_⟩⟩
  · simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, Lib.pushR, Lib.popR]
  · intro a rest σ hS
    exact moveEntry_runs .W0 .RET (by decide) a rest σ hS

theorem w9_rqPop : W9_rqPop := by
  refine ⟨3, fun _ => ⟨0, Option Sym, moveRec (.inl .RQ) (.inl .W0), Nat.zero_le _,
    inferInstance, ⟨none⟩, ?_, ?_⟩⟩
  · simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, Lib.pushR, Lib.popR]
  · intro a rest σ hS
    exact moveEntry_runs .RQ .W0 (by decide) a rest σ hS

#assert_std_axioms w9_retMark moveEntry_runs w9_retPush w9_rqPop

end TMFw.Contracts
