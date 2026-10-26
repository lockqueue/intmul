/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafScalarRowDefs

/-!
# Scalar row leaf: the programs and the one-term safe run (`CCore/LeafScalarRowProg.lean`)

**Scope (honest summary).** Programs on the big layout `BL Er` (`CCore/LeafPhaseBase.lean`) of the
scalar-row kernel (`ScalarRowStmt`, `CCore/SkelDefs.lean:288`), parametric in four accumulation
calls `acc` with the work-layout specification `AccW` (`CCore/LeafScalarRowDefs.lean`), and exact
safe runs of the pieces of one term:
* `cpIn s`: certified copy of role `s` (above its owned `mark`) onto `X2`, the role is restored
  (`safe_cpIn`);
* `mvOutX u`: certified move of `X` (above its floor) onto role `u` (`safe_mvOutX`);
* `yToX`: move `Y` onto `X` on the work layout (`runs_yToX`);
* `termProg acc c s`: `cpIn s`, then (scratch only) `acc c` and `yToX`; the accumulator `u` on `X`
  becomes `zipC (accC c) u v`, `v` the array of role `s` (`runs_termW`, `safe_term`);
* the static loops `chainProg` (the terms of one role, then `mvOutX`), `tgtProg` (`mvIn`, then the
  chain), `rolesProg` (the roles of a list, then a final program) and `rowProg` (`preW psS`, every
  role of a list `L`, `postW psS`); their runs are in `LeafScalarRowLoop.lean`;
* `setRoles` bookkeeping lemmas.
Everything here is proved.
-/

namespace SubNLogN.Machine.CCore.LeafScalarRowAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability
open SubNLogN.Machine.CCore.LeafScalarAux

variable {Er : Type}

/-! ## Programs -/

/-- Copy role `s` (above its owned `mark`) onto `X2`, through `Tm`; role `s` is restored. -/
def cpIn (Rr : Type) (s : Fin Wn) : Prog (BL Er) (fun _ => Sym) (σ Rr) :=
  (passC Sym.mark (roleL s) (scr .Tm) (scr .X2)).liftRegs (lO Rr)

/-- Move the array on `X` (above its floor `mark`) onto role `u`, through `Tm`. -/
def mvOutX (Rr : Type) (u : Fin Wn) : Prog (BL Er) (fun _ => Sym) (σ Rr) :=
  (passS Sym.mark (scr .X) (scr .Tm) (roleL u)).liftRegs (lO Rr)

/-- Move the array on `Y` (above its floor) onto `X` (work layout). -/
def yToX (Rr : Type) : Prog (Lw Er) (fun _ => Sym) (σ Rr) :=
  (passS Sym.mark (wS .Y) (wS .Tm) (wS .X)).liftRegs (lO Rr)

/-- One term `(c, s)`: copy role `s` onto `X2`; then `X ← zipC (accC c) X X2` through `Y`. -/
def termProg {Rr : Type} (acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)) (c : Coef)
    (s : Fin Wn) : Prog (BL Er) (fun _ => Sym) (σ Rr) :=
  .seq (cpIn Rr s) (callInj ιw (lid _) (.seq (acc c) (yToX Rr)))

/-- The terms `τ` of role `u`, then the move of `X` back onto role `u`. -/
def chainProg {Rr : Type} (acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)) (u : Fin Wn) :
    List (Coef × Fin Wn) → Prog (BL Er) (fun _ => Sym) (σ Rr)
  | [] => mvOutX Rr u
  | p :: τ => .seq (termProg acc p.1 p.2) (chainProg acc u τ)

/-- Role `u` with terms `τ`: move it onto `X`, accumulate, move it back. -/
def tgtProg {Rr : Type} (acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)) (u : Fin Wn)
    (τ : List (Coef × Fin Wn)) : Prog (BL Er) (fun _ => Sym) (σ Rr) :=
  .seq (mvIn Rr u) (chainProg acc u τ)

/-- The roles of a list (role `u` with terms `T u`), then `post`. -/
def rolesProg {Rr : Type} (acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr))
    (T : Fin Wn → List (Coef × Fin Wn)) (post : Prog (BL Er) (fun _ => Sym) (σ Rr)) :
    List (Fin Wn) → Prog (BL Er) (fun _ => Sym) (σ Rr)
  | [] => post
  | u :: us => .seq (tgtProg acc u (T u)) (rolesProg acc T post us)

/-- **The scalar-row program** for the term function `T` and the role list `L` (the kernel uses
`L = List.finRange Wn`; the list is a parameter so that no lemma ever unfolds `List.finRange Wn`):
read the descriptor and push the floors, process the roles of `L`, pop the floors and drop the
counters. -/
def rowProg {Rr : Type} (acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr))
    (T : Fin Wn → List (Coef × Fin Wn)) (L : List (Fin Wn)) : Prog (BL Er) (fun _ => Sym) (σ Rr) :=
  .seq (callInj ιw (lid _) (preW psS)) (rolesProg acc T (callInj ιw (lid _) (postW psS)) L)

theorem closed_cpIn (Rr : Type) (s : Fin Wn) : (cpIn (Er := Er) Rr s).Closed :=
  WP.W9comp.closed_liftRegs _ (closed_passC _ _ _ _)

theorem closed_mvOutX (Rr : Type) (u : Fin Wn) : (mvOutX (Er := Er) Rr u).Closed :=
  WP.W9comp.closed_liftRegs _ (closed_passS _ _ _ _)

theorem closed_yToX (Rr : Type) : (yToX (Er := Er) Rr).Closed :=
  WP.W9comp.closed_liftRegs _ (closed_passS _ _ _ _)

theorem closed_termProg {Rr : Type} {acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)}
    (hacc : ∀ c, (acc c).Closed) (c : Coef) (s : Fin Wn) : (termProg acc c s).Closed :=
  ⟨closed_cpIn _ _, closed_callInj _ _ ⟨hacc c, closed_yToX _⟩⟩

theorem closed_chainProg {Rr : Type} {acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)}
    (hacc : ∀ c, (acc c).Closed) (u : Fin Wn) : ∀ τ, (chainProg acc u τ).Closed
  | [] => closed_mvOutX _ u
  | p :: τ => ⟨closed_termProg hacc p.1 p.2, closed_chainProg hacc u τ⟩

theorem closed_tgtProg {Rr : Type} {acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)}
    (hacc : ∀ c, (acc c).Closed) (u : Fin Wn) (τ : List (Coef × Fin Wn)) :
    (tgtProg acc u τ).Closed :=
  ⟨closed_mvIn _ _, closed_chainProg hacc u τ⟩

theorem closed_rolesProg {Rr : Type} {acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)}
    (hacc : ∀ c, (acc c).Closed) (T : Fin Wn → List (Coef × Fin Wn))
    {post : Prog (BL Er) (fun _ => Sym) (σ Rr)} (hpost : post.Closed) :
    ∀ L, (rolesProg acc T post L).Closed
  | [] => hpost
  | u :: us => ⟨closed_tgtProg hacc u (T u), closed_rolesProg hacc T hpost us⟩

theorem closed_rowProg {Rr : Type} {acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)}
    (hacc : ∀ c, (acc c).Closed) (T : Fin Wn → List (Coef × Fin Wn)) (L : List (Fin Wn)) :
    (rowProg acc T L).Closed :=
  ⟨closed_callInj _ _ (closed_preW _),
    closed_rolesProg hacc T (closed_callInj _ _ (closed_postW _)) L⟩

/-! ## `setRoles` bookkeeping -/

theorem setRoles_role (S : BL Er → List Sym) (g : Fin Wn → List Sym) (u : Fin Wn) :
    setRoles S g (roleL u) = g u := rfl

theorem setRoles_desc (S : BL Er → List Sym) (g : Fin Wn → List Sym) :
    setRoles S g descL = S descL := rfl

theorem kClean_setRoles (S : BL Er → List Sym) (hS : KClean S) (g : Fin Wn → List Sym) :
    KClean (setRoles S g) := fun e => hS e

variable [DecidableEq Er]

theorem update_setRoles (S : BL Er → List Sym) (g : Fin Wn → List Sym) (u : Fin Wn)
    (l : List Sym) :
    Function.update (setRoles S g) (roleL u) l = setRoles S (Function.update g u l) := by
  funext k
  rcases k with (_ | _ | _ | v) | e
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : v = u
    · subst h
      show Function.update (setRoles S g) (roleL v) l (roleL v) = Function.update g v l v
      rw [Function.update_self, Function.update_self]
    · have h' : (roleL v : BL Er) ≠ roleL u := by simpa using h
      rw [Function.update_of_ne h']
      show g v = Function.update g u l v
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl

theorem setRoles_self (S : BL Er → List Sym) (g : Fin Wn → List Sym)
    (hg : ∀ u, S (roleL u) = g u) : setRoles S g = S := by
  funext k
  rcases k with (_ | _ | _ | v) | e
  · rfl
  · rfl
  · rfl
  · exact (hg v).symm
  · rfl

/-! ## The pieces of one term -/

theorem safe_cpIn (Rr : Type) (s : Fin Wn) (S0 : BL Er → List Sym) (sc : PS → List Sym)
    (xs : List Sym) (hxs : Sym.mark ∉ xs) (hs : S0 (roleL s) = xs ++ [Sym.mark])
    (hT : sc .Tm = [Sym.mark]) (hX2 : sc .X2 = [Sym.mark]) :
    SafeRunsIn ccoreFramed [] (cpIn (Er := Er) Rr s) (stv S0 sc)
      (stv S0 (Function.update sc .X2 (xs ++ [Sym.mark]))) (fun _ => True)
      (9 * xs.length + 4) := by
  have h := safe_passC (g := Sym.mark) (src := roleL (E := PS ⊕ Er) s) (tmp := scr .Tm)
    (dst := scr .X2) (by simp) (by simp) (by simp) xs [] [] hxs (stv S0 sc) hs hT []
  refine SafeRunsIn.congr (safe_liftO_safe h (closed_passC _ _ _ _)) ?_ le_rfl
  rw [update_stv_scr]
  simp [hX2]

theorem safe_mvOutX (Rr : Type) (u : Fin Wn) (S0 : BL Er → List Sym) (sc : PS → List Sym)
    (xs : List Sym) (hxs : Sym.mark ∉ xs) (hu : S0 (roleL u) = [Sym.mark])
    (hT : sc .Tm = [Sym.mark]) (hX : sc .X = xs ++ [Sym.mark]) :
    SafeRunsIn ccoreFramed [] (mvOutX (Er := Er) Rr u) (stv S0 sc)
      (stv (Function.update S0 (roleL u) (xs ++ [Sym.mark])) (Function.update sc .X [Sym.mark]))
      (fun _ => True) (8 * xs.length + 4) := by
  have h := safe_passS (g := Sym.mark) (src := scr (Er := Er) .X) (tmp := scr .Tm)
    (dst := roleL u) (by simp) (by simp) (by simp) xs [] [] hxs (stv S0 sc) hX hT []
  refine SafeRunsIn.congr (safe_liftO_safe h (closed_passS _ _ _ _)) ?_ le_rfl
  rw [update_stv_scr, update_stv_inl]
  simp [hu]

theorem runs_yToX (Rr : Type) (d : List Sym) (sc : PS → List Sym) (er : Er → List Sym)
    (ys : List Sym) (hys : Sym.mark ∉ ys) (hY : sc .Y = ys ++ [Sym.mark])
    (hT : sc .Tm = [Sym.mark]) :
    Runs (yToX (Er := Er) Rr) (wst d sc er)
      (wst d (Function.update (Function.update sc .Y [Sym.mark]) .X (ys ++ sc .X)) er)
      (fun _ => True) (8 * ys.length + 4) := by
  have h := runs_passS (g := Sym.mark) (src := wS (Er := Er) .Y) (tmp := wS .Tm)
    (dst := wS .X) (by simp) (by simp) (by simp) ys [] [] hys (wst d sc er) hY hT
  have h' := WP.W0m.runs_liftRegs (lO Rr) h
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h' ?_) (fun _ _ => trivial) le_rfl
  simp only [update_wst_S, wst_S]

/-- `safe_callW` for a clean state: the sub-kernel scratch is empty. -/
theorem safe_callW0 {Rr : Type} {P : Prog (Lw Er) (fun _ => Sym) (σ Rr)} (hc : P.Closed)
    (S0 : BL Er → List Sym) (hcl : KClean S0) (sc sc' : PS → List Sym) {Q : σ Rr → Prop} {T : ℕ}
    (h : Runs P (wst (S0 descL) sc (fun _ => [])) (wst (S0 descL) sc' (fun _ => [])) Q T) :
    SafeRunsIn ccoreFramed [] (callInj ιw (lid (σ Rr)) P) (stv S0 sc) (stv S0 sc')
      (fun _ => True) T := by
  have her : (fun e => S0 (.inr (.inr e))) = (fun _ : Er => ([] : List Sym)) :=
    funext fun e => hcl (.inr e)
  exact safe_callW hc S0 sc sc' (by rw [her]; exact h)

/-- **One accumulation on the work layout**: `acc c`, then `yToX`. The accumulator `u` on `X` and
the source `v` on `X2` (above their floors) become `zipC (accC c) u v` on `X`; `X2` keeps its
floor; `Y` and `Tm` hold only their floors before and after. -/
theorem runs_termW {Rr : Type} {acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)} {Cacc : ℕ}
    (hacc : AccW acc Cacc) (c : Coef) (d : List Sym) (sc : PS → List Sym) (w : ℕ)
    (u v : List (List CInt)) (hw : 1 ≤ w) (hal : CAligned u v) (hf : CArrFits w v)
    (hX : sc .X = carrSyms w u ++ [Sym.mark]) (hX2 : sc .X2 = carrSyms w v ++ [Sym.mark])
    (hW : sc .cW = natSyms w) (hY : sc .Y = [Sym.mark]) (hT : sc .Tm = [Sym.mark]) :
    Runs (.seq (acc c) (yToX Rr)) (wst d sc (fun _ => []))
      (wst d (Function.update (Function.update sc .X
        (carrSyms w (zipC (accC c) u v) ++ [Sym.mark])) .X2 [Sym.mark]) (fun _ => []))
      (fun _ => True)
      (Cacc * (cvol w u + cvol w v + w + 1) + (8 * cvol w (zipC (accC c) u v) + 4)) := by
  have r1 := hacc.2 c d sc w u v hw hal hf hX hX2 hW
  have r2 := runs_yToX (Er := Er) Rr d
    (Function.update (Function.update (Function.update sc .X [Sym.mark]) .X2 [Sym.mark]) .Y
      (carrSyms w (zipC (accC c) u v) ++ sc .Y)) (fun _ => []) (carrSyms w (zipC (accC c) u v))
    (mark_not_mem_arrSyms' _) (by simp [hY]) (by simp [hT])
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq r1 r2) ?_
  congr 1
  funext q
  by_cases hqX : q = .X
  · subst hqX; simp
  · by_cases hqX2 : q = .X2
    · subst hqX2; simp
    · by_cases hqY : q = .Y
      · subst hqY; simp [hY]
      · simp [Function.update_apply, hqX, hqX2, hqY]

/-- **One term**, exact safe run on the big layout: the accumulator `u` on `X` (above its floor)
becomes `zipC (accC c) u v`, where `v` is the array of role `s`; role `s` and every other stack
are restored. -/
theorem safe_term {Rr : Type} {acc : Coef → Prog (Lw Er) (fun _ => Sym) (σ Rr)} {Cacc : ℕ}
    (hacc : AccW acc Cacc) (t : CCoreRT) (c : Coef) (s : Fin Wn) (S0 : BL Er → List Sym)
    (hcl : KClean S0) (u v : List (List CInt)) (hal : CAligned u v) (hf : CArrFits t.wg v)
    (hs : S0 (roleL s) = carrSyms t.wg v ++ [Sym.mark]) :
    SafeRunsIn ccoreFramed [] (termProg acc c s)
      (stv S0 (Function.update (scP psS t) .X (carrSyms t.wg u ++ [Sym.mark])))
      (stv S0 (Function.update (scP psS t) .X
        (carrSyms t.wg (zipC (accC c) u v) ++ [Sym.mark])))
      (fun _ => True)
      (9 * cvol t.wg v + 4 + (Cacc * (cvol t.wg u + cvol t.wg v + t.wg + 1) +
        (8 * cvol t.wg (zipC (accC c) u v) + 4))) := by
  have hw : 1 ≤ t.wg := by simp [CCoreRT.wg]
  have s1 := safe_cpIn (Er := Er) Rr s S0
    (Function.update (scP psS t) .X (carrSyms t.wg u ++ [Sym.mark])) (carrSyms t.wg v)
    (mark_not_mem_arrSyms' _) hs (by simp [scP]) (by simp [scP])
  have r := runs_termW hacc c (S0 descL)
    (Function.update (Function.update (scP psS t) .X (carrSyms t.wg u ++ [Sym.mark])) .X2
      (carrSyms t.wg v ++ [Sym.mark])) t.wg u v hw hal hf (by simp) (by simp)
    (by simp [scP, scW]) (by simp [scP]) (by simp [scP])
  have s2 := safe_callW0 (P := .seq (acc c) (yToX Rr)) ⟨hacc.1 c, closed_yToX Rr⟩ S0 hcl
    (Function.update (Function.update (scP psS t) .X (carrSyms t.wg u ++ [Sym.mark])) .X2
      (carrSyms t.wg v ++ [Sym.mark]))
    (Function.update (Function.update (Function.update (Function.update (scP psS t) .X
      (carrSyms t.wg u ++ [Sym.mark])) .X2 (carrSyms t.wg v ++ [Sym.mark])) .X
      (carrSyms t.wg (zipC (accC c) u v) ++ [Sym.mark])) .X2 [Sym.mark]) r
  refine SafeRunsIn.congr (SafeRunsIn.seq s1 s2) ?_ (by simp only [cvol]; omega)
  congr 1
  funext q
  by_cases hqX : q = .X
  · subst hqX; simp
  · by_cases hqX2 : q = .X2
    · subst hqX2; simp [scP]
    · simp [Function.update_apply, hqX, hqX2]

end SubNLogN.Machine.CCore.LeafScalarRowAux
