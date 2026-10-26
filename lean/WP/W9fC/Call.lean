import WP.W9fC.Facts
import WP.W9fC.Prog

/-!
# WP.W9fC.Call — one column-solver call inside the driver

`runs_call`: from a `cst` state whose `W0` holds column `u2` of `Y`, whose `TR` is before record
`u2`, with `C3 = u2` and the node's `alt` on `RQ`, the embedded column solver (`callB`, registers
through `Lens.fst`) leaves column `u2` of `Z` on `W0` and moves record `u2` from `TR` to `TL`; every
scratch stack is untouched (the solver's own scratch is restored by its contract).
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp Computability IntMul

attribute [local instance 10000] instZeroIntElementary

theorem getD_mem_toList {α : Type} {M : Array (Array α)} {i : ℕ} (hi : i < M.size) :
    M.getD i #[] ∈ M.toList := by
  have : M.getD i #[] = M[i] := by simp [Array.getD, hi]
  rw [this, Array.mem_toList_iff]
  exact Array.getElem_mem hi

variable {m : ℕ}

/-- The `W9_columnSolve` specification of a program `Pcs` with cost constant `C` (the body of the
contract, verbatim). -/
def CSpec (Mul : ℕ → ℕ) {mc : ℕ} {Rc : Type} (C : ℕ) (Pcs : Prog (BLoc mc) (fun _ => Sym) Rc) :
    Prop :=
  ∀ (h : PostHdr) (u2 : ℕ) (c0 c1 alt : ℤ × ℤ) (Y : Array (ℤ × ℤ))
    (σ : BLoc mc → List Sym) (restT rq r3 : List Sym),
    PostDims h → PostCtx h σ → u2 < h.r → Y.size = h.t1 →
    ColumnOK h.pSub h.t1 h.r u2 c0 c1 Y alt →
    ArrW h.H (IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H h.t1 h.mt1 h.r u2 c0.1 c1.1 Y
      alt) →
    σ (.inl .C3) = natSyms u2 ++ r3 → TermOK r3 →
    σ (.inl .W0) = blkE Y.toList →
    σ (.inl .TR) = postRecSyms c0.1 c1.1 (postMu h.H h.r u2 c0.1 c1.1) ++ restT →
    σ (.inl .RQ) = entrySyms alt ++ rq →
    Runs Pcs σ (Function.update (Function.update (Function.update σ (.inl .W0)
          (blkE (IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H h.t1 h.mt1 h.r u2 c0.1 c1.1
            Y alt).toList))
        (.inl .TR) restT)
        (.inl .TL) ((postRecSyms c0.1 c1.1 (postMu h.H h.r u2 c0.1 c1.1)).reverse ++
          σ (.inl .TL)))
      (fun _ => True) (C * columnBound Mul h)

theorem columnSolveBarrett_size (pSub H t1 mt r u2 : ℕ) (a c : ℤ) (Y : Array (ℤ × ℤ))
    (alt : ℤ × ℤ) :
    (IntMulTM.Contracts.W8.columnSolveBarrett pSub H t1 mt r u2 a c Y alt).size = t1 := by
  unfold IntMulTM.Contracts.W8.columnSolveBarrett IntMulTM.Contracts.W8.solveFwdBarrett
    IntMulTM.Contracts.W8.solveNyqBarrett IntMulTM.Contracts.W8.solveBwdBarrett
  split_ifs <;> simp [size_runSequentialScanSteps, size_runReverseSteps]

theorem Dat.Z_col_size (D : Dat m) {u2 : ℕ} (hu : u2 < D.h.r) : (D.Z.getD u2 #[]).size = D.h.t1 := by
  rw [D.Z_getD hu]
  exact columnSolveBarrett_size _ _ _ _ _ _ _ _ _ _

theorem cst_inr_set3 (σ : BLoc m → List Sym) (V : Vals) (a b c : List Sym) (j : Fin m) :
    cst σ (((V.setW0 a).setTr b).setTl c) (.inr j) = cst σ V (.inr j) := by
  exact cst_inr_eq σ (V := V) (V' := ((V.setW0 a).setTr b).setTl c) rfl rfl rfl rfl rfl rfl j

theorem runs_call {mc : ℕ} {Rc : Type} (hmc : mc ≤ m) {Pcs : Prog (BLoc mc) (fun _ => Sym) Rc}
    (Mul : ℕ → ℕ) (Ccs : ℕ) (hspec : CSpec Mul Ccs Pcs)
    (D : Dat m) (hD : PostDims D.h) (hctx : PostCtx D.h D.σ)
    (hRQ : D.σ (.inl .RQ) = entrySyms D.alt ++ D.rq) (hY : D.Y.size = D.h.r)
    (hcols : ∀ col ∈ D.Y.toList, col.size = D.h.t1)
    (hok : ∀ u2 < D.h.r, ColumnOK D.h.pSub D.h.t1 D.h.r u2 (read1D D.c0T u2) (read1D D.c1T u2)
      (D.Y.getD u2 #[]) D.alt)
    (hZ : MatW D.h.H D.Z) (u2 : ℕ) (hu : u2 < D.h.r) (V : Vals)
    (hw0 : V.w0 = blkE (D.Y.getD u2 #[]).toList) (htr : V.tr = D.trAt u2)
    (hc3 : V.c3 = natSyms u2 ++ Sym.mark :: D.σ (.inl .C3)) (hrq : V.rq = D.σ (.inl .RQ))
    (hc0 : V.c0 = D.σ (.inl .C0)) :
    Runs (callB hmc (Lens.fst Rc (Option Sym)) Pcs) (cst D.σ V)
      (cst D.σ (((V.setW0 (blkE (D.Z.getD u2 #[]).toList)).setTr (D.trAt (u2 + 1))).setTl
        ((D.recOf u2).reverse ++ V.tl))) (fun _ => True) (Ccs * columnBound Mul D.h) := by
  have hY' : u2 < D.Y.size := by rw [hY]; exact hu
  have hsize : (D.Y.getD u2 #[]).size = D.h.t1 := hcols _ (getD_mem_toList hY')
  have hArr : ArrW D.h.H (IntMulTM.Contracts.W8.columnSolveBarrett D.h.pSub D.h.H D.h.t1 D.h.mt1
      D.h.r u2 (read1D D.c0T u2).1 (read1D D.c1T u2).1 (D.Y.getD u2 #[]) D.alt) := by
    rw [← D.Z_getD hu]
    exact hZ _ (getD_mem_toList (by rw [D.Z_size]; exact hu))
  have hctx' : PostCtx D.h ((cst D.σ V) ∘ emb hmc) := by
    obtain ⟨r0, hr0⟩ := hctx
    exact ⟨r0, hc0.trans hr0⟩
  have htr' : ((cst D.σ V) ∘ emb hmc) (.inl .TR) = postRecSyms (read1D D.c0T u2).1
      (read1D D.c1T u2).1 (postMu D.h.H D.h.r u2 (read1D D.c0T u2).1 (read1D D.c1T u2).1) ++
      D.trAt (u2 + 1) := by
    show V.tr = _
    rw [htr, D.trAt_succ hu]
    rfl
  have hP := hspec D.h u2 (read1D D.c0T u2) (read1D D.c1T u2) D.alt (D.Y.getD u2 #[])
    ((cst D.σ V) ∘ emb hmc) (D.trAt (u2 + 1)) D.rq (Sym.mark :: D.σ (.inl .C3)) hD hctx' hu hsize
    (hok u2 hu) hArr hc3 (termOK_mark _) hw0 htr' (hrq.trans hRQ)
  rw [upd_comp_emb, upd_comp_emb, upd_comp_emb, upd_w0, upd_tr, upd_tl, ← D.Z_getD hu] at hP
  exact runs_callB hmc (Lens.fst Rc (Option Sym)) hP (cst_inr_set3 D.σ V _ _ _)

#assert_std_axioms getD_mem_toList columnSolveBarrett_size Dat.Z_col_size cst_inr_set3 runs_call

end WP.W9fC
