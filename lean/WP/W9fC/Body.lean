import WP.W9fC.Inner
import WP.W9fC.Call

/-!
# WP.W9fC.Body — one column of the driver

`runs_colBody`: from the loop invariant before column `u2 < r` to the invariant before `u2 + 1`.
`CW := t1`; move the `t1` entries of column `u2` from `M2` to `T` (`runs_cntLoop`); drop the `CW`
guard; rewind `T → W0` (the column, in order); call the solver (`runs_call`); transfer the output
`W0 → A`; `C3 += 1`.
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp Computability IntMul

attribute [local instance 10000] instZeroIntElementary

variable {m : ℕ}

/-- Per-column cost bound of the driver. -/
def colTb (Mul : ℕ → ℕ) (Ccs : ℕ) (h : PostHdr) : ℕ :=
  Ccs * columnBound Mul h + h.t1 * (9 * eb h.H + 6 * bitLen h.t1 + 10) + 7 * bitLen h.t1 +
    6 * bitLen h.r + 25

theorem runs_colBody (hm : 7 ≤ m) {mc : ℕ} {Rc : Type} (hmc : mc ≤ m)
    {Pcs : Prog (BLoc mc) (fun _ => Sym) Rc} (Mul : ℕ → ℕ) (Ccs : ℕ) (hspec : CSpec Mul Ccs Pcs)
    (D : Dat m) (hD : PostDims D.h) (hctx : PostCtx D.h D.σ)
    (hRQ : D.σ (.inl .RQ) = entrySyms D.alt ++ D.rq) (hY : D.Y.size = D.h.r)
    (hcols : ∀ col ∈ D.Y.toList, col.size = D.h.t1)
    (hok : ∀ u2 < D.h.r, ColumnOK D.h.pSub D.h.t1 D.h.r u2 (read1D D.c0T u2) (read1D D.c1T u2)
      (D.Y.getD u2 #[]) D.alt)
    (hZ : MatW D.h.H D.Z) (u2 : ℕ) (hu : u2 < D.h.r) :
    Runs (colBody hm hmc Pcs) (cst D.σ (D.colV hm u2)) (cst D.σ (D.colV hm (u2 + 1)))
      (fun _ => True) (colTb Mul Ccs D.h) := by
  have hY' : u2 < D.Y.size := by rw [hY]; exact hu
  have hcl : (D.Y.getD u2 #[]).toList.length = D.h.t1 := by
    rw [Array.length_toList]
    exact hcols _ (getD_mem_toList hY')
  have hW : ArrW D.h.H (D.Y.getD u2 #[]) := (hok u2 hu).2.2.2.2.2.2.2.1
  have hout : ArrW D.h.H (D.Z.getD u2 #[]) :=
    hZ _ (getD_mem_toList (by rw [D.Z_size]; exact hu))
  have hos : (D.Z.getD u2 #[]).toList.length = D.h.t1 := by
    rw [Array.length_toList]
    exact D.Z_col_size hu
  have hLin : (blkE (D.Y.getD u2 #[]).toList).length ≤ D.h.t1 * eb D.h.H := by
    have := length_blkE_le D.h.H _ hW
    rwa [hcl] at this
  have hLout : (blkE (D.Z.getD u2 #[]).toList).length ≤ D.h.t1 * eb D.h.H := by
    have := length_blkE_le D.h.H _ hout
    rwa [hos] at this
  have hbu : bitLen u2 ≤ bitLen D.h.r := bl_mono (le_of_lt hu)
  have hsm2 : blkE (D.colsFrom u2) ++ D.σ (sM2 hm) = blkE ((D.Y.getD u2 #[]).toList.drop 0) ++
      (blkE (D.colsFrom (u2 + 1)) ++ D.σ (sM2 hm)) := by
    rw [D.colsFrom_succ hY', blkE_append, List.drop_zero, List.append_assoc]
  have hsm2' : blkE ((D.Y.getD u2 #[]).toList.drop D.h.t1) ++
      (blkE (D.colsFrom (u2 + 1)) ++ D.σ (sM2 hm)) = blkE (D.colsFrom (u2 + 1)) ++ D.σ (sM2 hm) := by
    rw [List.drop_of_length_le (le_of_eq hcl), blkE_nil, List.nil_append]
  have hsa : (blkE (D.Z.getD u2 #[]).toList).reverse ++
      ((blkE (D.outsUpTo u2)).reverse ++ symGuard :: D.σ (sA hm)) =
      (blkE (D.outsUpTo (u2 + 1))).reverse ++ symGuard :: D.σ (sA hm) := by
    rw [D.outsUpTo_succ hu, blkE_append, List.reverse_append, List.append_assoc]
  have hw0 : (blkE ((D.Y.getD u2 #[]).toList.take D.h.t1)).reverse.reverse ++ [] =
      blkE (D.Y.getD u2 #[]).toList := by
    rw [List.reverse_reverse, List.append_nil, List.take_of_length_le (le_of_eq hcl)]
  have e : D.h.t1 * (3 * eb D.h.H + 6 * bitLen D.h.t1 + 8 + 2) + 3 * (D.h.t1 * eb D.h.H) +
      3 * (D.h.t1 * eb D.h.H) = D.h.t1 * (9 * eb D.h.H + 6 * bitLen D.h.t1 + 10) := by ring
  unfold colBody colTb
  exact runs_mono
    (runs_seq (runs_pushC' Rc (sCW hm) symGuard _ _ (upd_scw D.σ _ _ hm)) <|
     runs_seq (runs_copyNat Rc (ne_scr _ _ (by decide)) (ne_scr _ _ (by decide)) (ne_scr _ _ (by decide)) D.h.t1
        (symGuard :: D.σ (sCT hm)) _ _ (termOK_guard _) (by exact rfl) (upd_scw D.σ _ _ hm)) <|
     runs_seq (runs_pushC' Rc (sT hm) symGuard _ _ ((upd_st D.σ _ _ hm).trans (by
        exact congrArg (cst D.σ) (Vals.ext' rfl rfl rfl rfl rfl rfl rfl hsm2 rfl rfl rfl rfl)))) <|
     runs_seq (runs_cntLoop hm Rc D u2 hcl hW) <|
     runs_seq (runs_pop' Rc (sCW hm) symGuard (D.σ (sCW hm)) _ _
        (by
          show natSyms (D.h.t1 - D.h.t1) ++ _ = _
          simp [natSyms_zero])
        (upd_scw D.σ _ _ hm)) <|
     runs_seq (runs_rewind' Rc (ne_inr_inl _ _) symGuard
        (blkE ((D.Y.getD u2 #[]).toList.take D.h.t1)).reverse (D.σ (sT hm)) _ _
        (guard_not_mem_rev_blkE _) (by exact rfl) (upd2 (upd_st D.σ _ _ hm) (upd_w0 D.σ _ _))) <|
     runs_seq (runs_call hmc Mul Ccs hspec D hD hctx hRQ hY hcols hok hZ u2 hu _
        (by exact hw0) (by exact rfl) (by exact rfl) (by exact rfl) (by exact rfl)) <|
     runs_seq (runs_xfer' Rc (ne_inl_inr _ _) (blkE (D.Z.getD u2 #[]).toList) _ _ (by exact rfl)
        (upd2 (upd_w0 D.σ _ _) (upd_sa D.σ _ _ hm))) <|
     runs_inc' Rc (ne_inl_inr _ _) u2 (Sym.mark :: D.σ (.inl .C3)) _ _ (termOK_mark _) (by exact rfl)
        ((upd_c3 D.σ _ _).trans (by
          exact congrArg (cst D.σ)
            (Vals.ext' rfl rfl (D.tlAt_succ u2) rfl rfl rfl rfl hsm2' rfl hsa rfl rfl))))
    (fun _ _ => trivial)
    (by
      rw [List.length_reverse, List.take_of_length_le (le_of_eq hcl)]
      omega)

#assert_std_axioms runs_colBody

end WP.W9fC
