import WP.W9fC.Body

/-!
# WP.W9fC.Loop — all columns

`runs_colLoop`: `colPk ; while (head of TR is data) (colBody ; colPk)` runs the `r` columns
(`runs_peekLoop` with `S n = cst σ (colV (r - n))`; the test is `Dat.head_trAt`).
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp Computability IntMul

attribute [local instance 10000] instZeroIntElementary

variable {m : ℕ}

theorem runs_colLoop (hm : 7 ≤ m) {mc : ℕ} {Rc : Type} (hmc : mc ≤ m)
    {Pcs : Prog (BLoc mc) (fun _ => Sym) Rc} (Mul : ℕ → ℕ) (Ccs : ℕ) (hspec : CSpec Mul Ccs Pcs)
    (D : Dat m) (hD : PostDims D.h) (hctx : PostCtx D.h D.σ)
    (hRQ : D.σ (.inl .RQ) = entrySyms D.alt ++ D.rq) (hY : D.Y.size = D.h.r)
    (hcols : ∀ col ∈ D.Y.toList, col.size = D.h.t1)
    (hok : ∀ u2 < D.h.r, ColumnOK D.h.pSub D.h.t1 D.h.r u2 (read1D D.c0T u2) (read1D D.c1T u2)
      (D.Y.getD u2 #[]) D.alt)
    (hZ : MatW D.h.H D.Z) :
    Runs (colLoop hm hmc Pcs) (cst D.σ (D.colV hm 0)) (cst D.σ (D.colV hm D.h.r)) (fun _ => True)
      (D.h.r * (colTb Mul Ccs D.h + 2) + 2) := by
  have hl := runs_peekLoop (fun v : Rc × Option Sym => isDataR v.2) (colPk Rc)
    (colBody hm hmc Pcs) (fun n => cst D.σ (D.colV hm (D.h.r - n))) D.h.r (colTb Mul Ccs D.h)
    (fun n hn v => ⟨_, eval_peek_snd (.inl .TR : BLoc m) v _, by
      show isDataR (D.trAt (D.h.r - n)).head? = _
      rw [D.head_trAt]
      exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩⟩)
    (fun n hn => by
      have e : D.h.r - n = D.h.r - (n + 1) + 1 := by omega
      show Runs _ (cst D.σ (D.colV hm (D.h.r - (n + 1)))) (cst D.σ (D.colV hm (D.h.r - n))) _ _
      rw [e]
      exact runs_colBody hm hmc Mul Ccs hspec D hD hctx hRQ hY hcols hok hZ _ (by omega))
  simp only [Nat.sub_self, Nat.sub_zero] at hl
  exact hl

#assert_std_axioms runs_colLoop

end WP.W9fC
