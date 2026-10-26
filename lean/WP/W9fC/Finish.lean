import WP.W9fC.Facts
import WP.W9fC.Steps

/-!
# WP.W9fC.Finish — the final phase of the column driver

From the column-loop invariant after the last column (`colV r`): rewind `A → W0` (the outputs, in
order: `matSyms Z`), move `symSub` `TR → TL` (the table head ends after the POST body), drop the
`C3` counter, pop `entrySyms alt` from `RQ`, drop the `CT` counter. Every other stack is back to `σ`.

`fin_runs` runs the phase on an arbitrary `cst σ V`: the stack values are hypotheses, so every
definitional check is between variables. `runs_finish` instantiates it at `V = colV r`.
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp Computability IntMul

attribute [local instance 10000] instZeroIntElementary

/-- Four updates of a `cst` state. -/
theorem fin_upd4 {m : ℕ} (σ : BLoc m → List Sym) (V : Vals) (a b c d : List Sym) :
    Function.update (Function.update (Function.update (Function.update (cst σ V) (.inl .W0) a)
      (.inl .TR) b) (.inl .TL) c) (.inl .RQ) d =
      cst σ ((((V.setW0 a).setTr b).setTl c).setRq d) :=
  upd2 (upd2 (upd2 (upd_w0 σ V a) (upd_tr σ _ b)) (upd_tl σ _ c)) (upd_rq σ _ d)

/-- The plain-`σ` target of `runs_finish` as a `cst` state. -/
theorem fin_target {m : ℕ} (hm : 7 ≤ m) (σ : BLoc m → List Sym) (a b c d : List Sym) :
    Function.update (Function.update (Function.update (Function.update σ (.inl .W0) a)
      (.inl .TR) b) (.inl .TL) c) (.inl .RQ) d =
      cst σ (((((V0 σ hm).setW0 a).setTr b).setTl c).setRq d) := by
  have h := fin_upd4 σ (V0 σ hm) a b c d
  rw [cst_V0] at h
  exact h

/-- The final phase on any `cst σ V` with the expected stack shapes. -/
theorem fin_runs {m : ℕ} (hm : 7 ≤ m) (R : Type) (σ : BLoc m → List Sym) (V : Vals)
    (La trR d rq : List Sym) (r t1 : ℕ) (hgL : symGuard ∉ La) (hsd : Sym.sep ∉ d)
    (hsa : V.sa = La ++ symGuard :: σ (sA hm)) (htr : V.tr = symSub :: trR)
    (hc3 : V.c3 = natSyms r ++ Sym.mark :: σ (.inl .C3)) (hrq : V.rq = d ++ Sym.sep :: rq)
    (hct : V.sct = natSyms t1 ++ symGuard :: σ (sCT hm)) :
    Runs (finishProg hm R) (cst σ V)
      (cst σ (((((((V.setSa (σ (sA hm))).setW0 (La.reverse ++ V.w0)).setTr trR).setTl
        (symSub :: V.tl)).setC3 (σ (.inl .C3))).setRq rq).setSct (σ (sCT hm))))
      (fun _ => True)
      (3 * La.length + 2 + (2 + (2 * (natSyms r).length + 2 +
        (2 * d.length + 2 + (2 * (natSyms t1).length + 2))))) :=
  runs_seq (runs_rewind' R (ne_inr_inl _ _) symGuard La (σ (sA hm)) _ _ hgL hsa
      (upd2 (upd_sa σ V _ hm) (upd_w0 σ _ _))) <|
  runs_seq (runs_popPush' R (by intro h; cases h) symSub trR _ _ htr
      (upd2 (upd_tr σ _ _) (upd_tl σ _ _))) <|
  runs_seq (runs_drop' R Sym.mark (natSyms r) (σ (.inl .C3)) _ _ (not_mem_natSyms rfl) hc3
      (upd_c3 σ _ _)) <|
  runs_seq (runs_drop' R Sym.sep d rq _ _ hsd hrq (upd_rq σ _ _)) <|
  runs_drop' R symGuard (natSyms t1) (σ (sCT hm)) _ _ (not_mem_natSyms rfl) hct (upd_sct σ _ _ hm)

theorem runs_finish {m : ℕ} (hm : 7 ≤ m) (R : Type) (D : Dat m) (hY : D.Y.size = D.h.r)
    (hRQ : D.σ (.inl .RQ) = entrySyms D.alt ++ D.rq) :
    Runs (finishProg hm R) (cst D.σ (D.colV hm D.h.r))
      (Function.update (Function.update (Function.update (Function.update D.σ (.inl .W0)
        (matSyms D.Z)) (.inl .TR) D.restT) (.inl .TL)
        ((postBody D.h.pSub D.h.r D.c0T D.c1T).reverse ++ D.σ (.inl .TL))) (.inl .RQ) D.rq)
      (fun _ => True)
      (3 * (matSyms D.Z).length + 2 * bitLen D.h.r + 2 * bitLen D.h.t1 +
        2 * (entrySyms D.alt).length + 10) := by
  have hl := length_recD D.alt
  rw [fin_target hm D.σ]
  refine runs_mono (runs_congr (fin_runs hm R D.σ (D.colV hm D.h.r)
    (blkE (D.outsUpTo D.h.r)).reverse D.restT (recD D.alt) D.rq D.h.r D.h.t1
    (guard_not_mem_rev_blkE _) (sep_not_mem_recD D.alt)
    (by simp only [Dat.colV]) (by simp only [Dat.colV]; exact D.trAt_r) (by simp only [Dat.colV])
    (by simp only [Dat.colV]; rw [hRQ, entrySyms_append]) (by simp only [Dat.colV])) ?_)
    (fun _ _ => trivial) ?_
  · apply congrArg (cst D.σ)
    apply Vals.ext' <;>
      simp only [Vals.setSa, Vals.setW0, Vals.setTr, Vals.setTl, Vals.setC3, Vals.setRq,
        Vals.setSct, Dat.colV, V0, List.reverse_reverse, List.append_nil, D.outsUpTo_r,
        D.tl_final, D.colsFrom_r hY, blkE_nil, List.nil_append]
  · simp only [List.length_reverse, length_natSyms, D.outsUpTo_r]
    omega

#assert_std_axioms fin_upd4 fin_target fin_runs runs_finish

end WP.W9fC
