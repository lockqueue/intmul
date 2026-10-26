import WP.W9fC.Loop
import WP.W9fC.Setup
import WP.W9fC.Finish
import WP.W9fC.Cost
import WP.W9fC.Sizes
import Contracts.W9.Pipeline

/-!
# WP.W9fC.Main — `W9_columns_of_columnSolve`

The column driver `colsProg` (setup ; column loop ; finish) with the column solver of
`W9_columnSolve` embedded by `callB` (scratch `max mc 7`, registers `Rc × Option Sym`). Cost constant
`C_columnSolve + 100`. The W3/W4 hypotheses of the S3 statement are not needed: the driver uses the
framework library (`Lib.Basic`, `Lib.Counter`) and W4's proved `moveRec` directly.
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp Computability IntMul

attribute [local instance 10000] instZeroIntElementary

variable {m : ℕ}

theorem Dat.setupV_eq (D : Dat m) (hm : 7 ≤ m) (hW0 : D.σ (.inl .W0) = matSyms D.Y)
    (hTR : D.σ (.inl .TR) = postBody D.h.pSub D.h.r D.c0T D.c1T ++ D.restT) :
    setupV D.σ hm D.h.t1 = D.colV hm 0 :=
  Vals.ext' rfl (hTR.trans D.trAt_zero.symm)
    (by
      show D.σ (.inl .TL) = D.tlAt 0
      simp [Dat.tlAt])
    (by
      show Sym.mark :: D.σ (.inl .C3) = natSyms 0 ++ Sym.mark :: D.σ (.inl .C3)
      simp [natSyms_zero])
    rfl rfl rfl
    (by
      show D.σ (.inl .W0) ++ D.σ (sM2 hm) = blkE (D.colsFrom 0) ++ D.σ (sM2 hm)
      rw [D.colsFrom_zero, hW0])
    rfl
    (by
      show symGuard :: D.σ (sA hm) = (blkE (D.outsUpTo 0)).reverse ++ symGuard :: D.σ (sA hm)
      simp [D.outsUpTo_zero, blkE_nil])
    rfl rfl

theorem runs_cols (hm : 7 ≤ m) {mc : ℕ} {Rc : Type} (hmc : mc ≤ m)
    {Pcs : Prog (BLoc mc) (fun _ => Sym) Rc} (Mul : ℕ → ℕ) (Ccs : ℕ) (hspec : CSpec Mul Ccs Pcs)
    (D : Dat m) (hD : PostDims D.h) (hctx : PostCtx D.h D.σ) (hY : D.Y.size = D.h.r)
    (hcols : ∀ col ∈ D.Y.toList, col.size = D.h.t1)
    (hok : ∀ u2 < D.h.r, ColumnOK D.h.pSub D.h.t1 D.h.r u2 (read1D D.c0T u2) (read1D D.c1T u2)
      (D.Y.getD u2 #[]) D.alt)
    (hZ : MatW D.h.H D.Z) (hW0 : D.σ (.inl .W0) = matSyms D.Y)
    (hTR : D.σ (.inl .TR) = postBody D.h.pSub D.h.r D.c0T D.c1T ++ D.restT)
    (hRQ : D.σ (.inl .RQ) = entrySyms D.alt ++ D.rq) :
    Runs (colsProg hm hmc Pcs) D.σ
      (Function.update (Function.update (Function.update (Function.update D.σ (.inl .W0)
        (matSyms D.Z)) (.inl .TR) D.restT) (.inl .TL)
        ((postBody D.h.pSub D.h.r D.c0T D.c1T).reverse ++ D.σ (.inl .TL))) (.inl .RQ) D.rq)
      (fun _ => True)
      ((Ccs + 100) * (D.h.r * columnBound Mul D.h + D.h.N * eb D.h.H + eb D.h.H + 1)) := by
  obtain ⟨rest3, hC0⟩ := c0_split hctx
  have hgW : symGuard ∉ D.σ (.inl .W0) := by
    rw [hW0]
    exact guard_not_mem_blkE _
  have hset := runs_setup hm Rc D.σ D.h.p D.h.pSub D.h.t1 rest3 hC0 hgW
  rw [D.setupV_eq hm hW0 hTR] at hset
  have hloop := runs_colLoop hm hmc Mul Ccs hspec D hD hctx hRQ hY hcols hok hZ
  have hfin := runs_finish hm Rc D hY hRQ
  obtain ⟨hr, hcolB, hhdr, htb, heb⟩ := colB_facts Mul D.h hD
  have hhl := hdrLen_ge D.h
  have hmY : (D.σ (.inl .W0)).length ≤ D.h.t1 * D.h.r * eb D.h.H := by
    rw [hW0]
    exact D.lenY_le hY hcols hok
  have hmZ := D.lenZ_le hZ (fun u2 hu => D.Z_col_size hu)
  have heA : (entrySyms D.alt).length ≤ eb D.h.H :=
    length_entrySyms_le (hok 0 (by omega)).2.2.2.2.2.2.2.2.1
  refine runs_mono (runs_seq hset (runs_seq hloop hfin)) (fun _ _ => trivial) ?_
  unfold colTb
  exact cost_total_le Ccs D.h.r D.h.t1 (columnBound Mul D.h) (eb D.h.H) (bitLen D.h.t1)
    (bitLen D.h.r) (bitLen D.h.p) (bitLen D.h.pSub) D.h.hdrLen _ _ _ hr hcolB hhdr (by omega)
    (by omega) (by omega) (by omega) htb hmY hmZ heb heA

/-- **S3 of the column solvers.** -/
theorem W9_columns_of_columnSolve (Mul : ℕ → ℕ) (_h3 : W3_all) (_h4 : W4_all)
    (h : W9_columnSolve Mul) : W9_columns Mul := by
  obtain ⟨Ccs, hcs⟩ := h
  refine ⟨Ccs + 100, fun _ => ?_⟩
  obtain ⟨mc, Rc, Pcs, hmc, hfin, hne, hcl, hspec⟩ := hcs ()
  haveI := hfin
  haveI := hne
  refine ⟨max mc 7, Rc × Option Sym, colsProg (le_max_right mc 7) (le_max_left mc 7) Pcs,
    max_le hmc (by decide), inferInstance, inferInstance,
    colsProg_closed (le_max_right mc 7) (le_max_left mc 7) hcl, ?_⟩
  intro hdr c0T c1T alt Y σ restT rq hD hctx _htab hY hcols hok hZ hW0 hTR hRQ
  exact runs_cols (le_max_right mc 7) (le_max_left mc 7) Mul Ccs hspec
    ⟨σ, hdr, c0T, c1T, alt, Y, restT, rq⟩ hD hctx hY hcols hok hZ hW0 hTR hRQ

#assert_std_axioms Dat.setupV_eq runs_cols W9_columns_of_columnSolve

end WP.W9fC
