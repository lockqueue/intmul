import WP.W9fC.Facts
import WP.W9fC.Steps

/-!
# WP.W9fC.Inner — the counted move of one input column

`inV u2 j`: before column `u2`'s solve, after `j` of its `t1` entries were moved `M2 → T` (`T` holds
them reversed above a guard; `CW = t1 - j` above a guard). `runs_cntBody` moves one entry,
`runs_cntLoop` all `t1` (`runs_peekLoop`, test `CW ≠ 0`).
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp Computability IntMul

variable {m : ℕ}

/-- The stacks after `j` entries of column `u2` were moved to `T`. -/
def Dat.inV (D : Dat m) (hm : 7 ≤ m) (u2 j : ℕ) : Vals :=
  { D.colV hm u2 with
    sm2 := blkE ((D.Y.getD u2 #[]).toList.drop j) ++ (blkE (D.colsFrom (u2 + 1)) ++ D.σ (sM2 hm))
    st := (blkE ((D.Y.getD u2 #[]).toList.take j)).reverse ++ symGuard :: D.σ (sT hm)
    scw := natSyms (D.h.t1 - j) ++ symGuard :: D.σ (sCW hm) }

theorem take_succ_rev_blkE (cl : List (ℤ × ℤ)) (j : ℕ) (hj : j < cl.length) (X : List Sym) :
    Sym.sep :: ((recD (cl[j]'hj)).reverse ++ ((blkE (cl.take j)).reverse ++ X)) =
      (blkE (cl.take (j + 1))).reverse ++ X := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, blkE_append, blkE_cons,
    blkE_nil, List.append_nil, List.reverse_append, entrySyms_eq_recD, List.reverse_append]
  simp

theorem runs_cntBody (hm : 7 ≤ m) (R : Type) (D : Dat m) (u2 j : ℕ)
    (hcl : (D.Y.getD u2 #[]).toList.length = D.h.t1) (hj : j < D.h.t1)
    (hW : ArrW D.h.H (D.Y.getD u2 #[])) :
    Runs (cntBody hm R) (cst D.σ (D.inV hm u2 j)) (cst D.σ (D.inV hm u2 (j + 1))) (fun _ => True)
      (3 * eb D.h.H + 6 * bitLen D.h.t1 + 8) := by
  have hjl : j < (D.Y.getD u2 #[]).toList.length := by omega
  have hz : EntryW D.h.H ((D.Y.getD u2 #[]).toList[j]'hjl) := hW _ (List.getElem_mem hjl)
  have hst := take_succ_rev_blkE (D.Y.getD u2 #[]).toList j hjl (symGuard :: D.σ (sT hm))
  have h1 := length_recD ((D.Y.getD u2 #[]).toList[j]'hjl)
  have h2 := length_entrySyms_le hz
  have h3 := bl_mono (show D.h.t1 - (j + 1) + 1 ≤ D.h.t1 by omega)
  unfold cntBody
  exact runs_mono
    (runs_seq (runs_moveRec' R (ne_scr _ _ (by decide)) (recD ((D.Y.getD u2 #[]).toList[j]'hjl))
        (blkE ((D.Y.getD u2 #[]).toList.drop (j + 1)) ++
          (blkE (D.colsFrom (u2 + 1)) ++ D.σ (sM2 hm))) _ _
        (isData_recD _)
        (by
          show blkE ((D.Y.getD u2 #[]).toList.drop j) ++ _ = _
          rw [List.drop_eq_getElem_cons hjl, blkE_cons, List.append_assoc, entrySyms_append])
        (upd2 (upd_sm2 D.σ _ _ hm) (upd_st D.σ _ _ hm))) <|
     runs_dec' R (ne_scr _ _ (by decide)) (D.h.t1 - (j + 1)) (symGuard :: D.σ (sCW hm)) _ _ (termOK_guard _)
        (by
          show natSyms (D.h.t1 - j) ++ _ = _
          rw [show D.h.t1 - j = D.h.t1 - (j + 1) + 1 by omega])
        ((upd_scw D.σ _ _ hm).trans (by
          exact congrArg (cst D.σ) (Vals.ext' rfl rfl rfl rfl rfl rfl rfl rfl hst rfl rfl rfl))))
    (fun _ _ => trivial)
    (by omega)

theorem runs_cntLoop (hm : 7 ≤ m) (R : Type) (D : Dat m) (u2 : ℕ)
    (hcl : (D.Y.getD u2 #[]).toList.length = D.h.t1) (hW : ArrW D.h.H (D.Y.getD u2 #[])) :
    Runs (cntLoop hm R) (cst D.σ (D.inV hm u2 0)) (cst D.σ (D.inV hm u2 D.h.t1)) (fun _ => True)
      (D.h.t1 * (3 * eb D.h.H + 6 * bitLen D.h.t1 + 8 + 2) + 2) := by
  have hl := runs_peekLoop (fun v : R × Option Sym => optIsBit v.2) (cntPk hm R) (cntBody hm R)
    (fun n => cst D.σ (D.inV hm u2 (D.h.t1 - n))) D.h.t1 (3 * eb D.h.H + 6 * bitLen D.h.t1 + 8)
    (fun n hn v => ⟨_, eval_peek_snd (sCW hm) v _, by
      show optIsBit (natSyms (D.h.t1 - (D.h.t1 - n)) ++ symGuard :: D.σ (sCW hm)).head? = _
      rw [show D.h.t1 - (D.h.t1 - n) = n by omega]
      exact optIsBit_head_natSyms n (termOK_guard _)⟩)
    (fun n hn => by
      have e : D.h.t1 - n = D.h.t1 - (n + 1) + 1 := by omega
      show Runs _ (cst D.σ (D.inV hm u2 (D.h.t1 - (n + 1)))) (cst D.σ (D.inV hm u2 (D.h.t1 - n)))
        _ _
      rw [e]
      exact runs_cntBody hm R D u2 _ hcl (by omega) hW)
  simp only [Nat.sub_self, Nat.sub_zero] at hl
  exact hl

#assert_std_axioms take_succ_rev_blkE runs_cntBody runs_cntLoop

end WP.W9fC
