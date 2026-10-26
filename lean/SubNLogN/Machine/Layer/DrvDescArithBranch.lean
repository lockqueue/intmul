/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvDescArith

/-!
# Layer driver pre-phase: the value kernel, branch (`Machine/Layer/DrvDescArithBranch.lean`)

**Scope (honest summary).** Part of the proof of `DrvDescArithStmt`
(`Machine/Layer/DrvDescDefs.lean`). After the parse (`Machine/Layer/DrvDescArith.lean`) the
floored stacks hold `q₀` (`sq`), `D` (`sD`), `d` (`sd`), `K` (`sK`), `A` (`sA`). The branch
compares `q₀` with `D` (`cmpN`) and puts one floored value on each of `se`, `sR`, `sa`:
* rows case `q₀ < D` (`rowsProg`): `e = D − q₀` (`subN`), `R = padR d K` (`DrvArith.padRN`; its second
  output `2^{q₀K}` is dropped at once), `a = A·R` (`mulN`);
* otherwise (`norowsProg`): `e = R = a = 0` (three bare floors; `2^{q₀K}` is never computed).
All proved (no `sorry`), with exact final stacks and explicit costs (`rowsCost`; the other case
costs `3`). Paper: Section A.6 (`sec:transfer-layer`), proof of Proposition A.11 (`prop:prop14-param`).
The values are generic (`q` for `q₀`): the lemmas never unfold `q0Of`/`padR` (avoiding
kernel unfolding of the large network constant `W_c`).
-/

namespace SubNLogN.Machine.Layer.DrvDescArithAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.Layer.DrvArith (fl fl_self fl_ne runs_fl padRN runs_padRN closed_padRN
  padRCost Reg2 lN isLtR runs_seq_ite_true runs_seq_ite_false runs_cmpN closed_cmpN')
open SubNLogN.Math.Networks (q0Of padR)

/-! ## 1. Stacks of `padRN`; lifting -/

/-- The stacks of `padRN`: `st 0 = sd` (`d`), `st i = .inr (36 + i)` otherwise, so that
`st 1 = sK`, `st 2 = sR`, `st 3 = sX`. -/
def stP (i : Fin 32) : AK := if i.val = 0 then sd else .inr ⟨36 + i.val, by have := i.isLt; omega⟩

theorem stP_inj : Function.Injective stP := by
  intro i j h
  have key : ∀ k : Fin 32, stP k =
      .inr ⟨if k.val = 0 then 20 else 36 + k.val, by have := k.isLt; split_ifs <;> omega⟩ := by
    intro k
    unfold stP
    split_ifs <;> rfl
  rw [key i, key j] at h
  simp only [Sum.inr.injEq, Fin.mk.injEq] at h
  apply Fin.ext
  split_ifs at h <;> omega

theorem stP_zero : stP 0 = sd := rfl
theorem stP_one : stP 1 = sK := rfl
theorem stP_two : stP 2 = sR := rfl
theorem stP_three : stP 3 = sX := rfl

/-- Lifting a `Runs` fact (postcondition `True`) through `lN`. -/
theorem runs_lN {p : Prog AK (fun _ => Sym) Reg} {S S' : AK → List Sym} {T : ℕ}
    (h : Runs p S S' (fun _ => True) T) : Runs (p.liftRegs lN) S S' (fun _ => True) T :=
  DrvArith.runs_liftRegs' lN h

/-! ## 2. The rows case -/

/-- Rows case: `e = D − q₀` on `se`, `R = padR d K` on `sR`, `a = A·R` on `sa` (each floored). -/
noncomputable def rowsProg : Prog AK (fun _ => Sym) Reg2 :=
  .seq ((Prog.seq (pushMark se) (subN sD sq se t0 t1 t2)).liftRegs lN)
  (.seq ((Prog.seq (pushMark sR) (pushMark sX)).liftRegs lN)
  (.seq (padRN stP)
  (.seq ((dropF sX).liftRegs lN)
  ((Prog.seq (pushMark sa) (mulN sA sR sa t0 t1 t2 t3)).liftRegs lN))))

theorem closed_rowsProg : rowsProg.Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (WP.W9comp.closed_seq (closed_pushMark _)
    (closed_subN _ _ _ _ _ _)))
  (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (WP.W9comp.closed_seq (closed_pushMark _)
    (closed_pushMark _)))
  (WP.W9comp.closed_seq (closed_padRN _)
  (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (closed_dropF _))
  (WP.W9comp.closed_liftRegs lN (WP.W9comp.closed_seq (closed_pushMark _)
    (closed_mulN _ _ _ _ _ _ _))))))

/-- The cost of the rows case (`PR` the cost of `padRN`, `X = 2^{q₀K}`, `R = padR d K`). -/
def rowsCost (D q PR X A R : ℕ) : ℕ :=
  (1 + 20 * (bitLen D + bitLen q + 1)) +
    ((1 + 1) + (PR + ((2 * bitLen X + 2) + (1 + mulCost A R))))

/-- **The rows case**, from a state `C` holding `d, K, A, D, q` floored on `sd, sK, sA, sD, sq`
(`q ≤ D`): pushes the floored values `D − q`, `padR d K`, `A·padR d K` on `se`, `sR`, `sa`; every
other stack is restored. -/
theorem runs_rows (C : AK → List Sym) (d K A D q : ℕ) (hqD : q ≤ D)
    (Jd JK JA JD Jq : List Sym)
    (hd : C sd = natSyms d ++ Sym.mark :: Jd) (hK : C sK = natSyms K ++ Sym.mark :: JK)
    (hA : C sA = natSyms A ++ Sym.mark :: JA) (hD : C sD = natSyms D ++ Sym.mark :: JD)
    (hq : C sq = natSyms q ++ Sym.mark :: Jq) :
    Runs rowsProg C (fl (fl (fl C se (D - q)) sR (padR d K)) sa (A * padR d K)) (fun _ => True)
      (rowsCost D q (padRCost d K) (2 ^ (q0Of d * K)) A (padR d K)) := by
  obtain ⟨F, hF⟩ : ∃ T, T = fl C se (D - q) := ⟨_, rfl⟩
  have hFk : ∀ k, k ≠ se → F k = C k := fun k hk => by rw [hF, fl_ne hk]
  -- 1. `e = D − q` above a floor on `se`
  have r1 : Runs ((Prog.seq (pushMark se) (subN sD sq se t0 t1 t2)).liftRegs lN) C F
      (fun _ => True) (1 + 20 * (bitLen D + bitLen q + 1)) := by
    rw [hF]
    refine runs_lN (runs_fl ?_)
    have h := runs_subN (x := sD) (y := sq) (z := se) (t1 := t0) (t2 := t1) (t3 := t2) (by decide)
      D q (Sym.mark :: JD) (Sym.mark :: Jq) (Function.update C se (Sym.mark :: C se))
      (termOK_mark _) (termOK_mark _) hqD
      (by rw [Function.update_of_ne (show sD ≠ se by decide)]; exact hD)
      (by rw [Function.update_of_ne (show sq ≠ se by decide)]; exact hq)
    rwa [Function.update_self] at h
  -- 2. floors on `sR` and `sX`
  obtain ⟨S3, hS3⟩ : ∃ T, T = Function.update (Function.update F sR (Sym.mark :: C sR)) sX
      (Sym.mark :: C sX) := ⟨_, rfl⟩
  have r2 : Runs ((Prog.seq (pushMark sR) (pushMark sX)).liftRegs lN) F S3 (fun _ => True)
      (1 + 1) := by
    have h := WP.W9comp.runs_seq (runs_pushMark sR F)
      (runs_pushMark sX (Function.update F sR (Sym.mark :: F sR)))
    rw [Function.update_of_ne (show sX ≠ sR by decide), hFk sX (by decide),
      hFk sR (by decide)] at h
    rw [hS3]
    exact runs_lN h
  -- 3. `padRN`: `padR d K` on `sR`, `2^{q₀K}` on `sX`
  have r3 := runs_padRN stP_inj d K (Sym.mark :: Jd) (Sym.mark :: JK) S3 (termOK_mark _)
    (termOK_mark _)
    (by rw [stP_zero, hS3, Function.update_of_ne (show sd ≠ sX by decide),
          Function.update_of_ne (show sd ≠ sR by decide), hFk sd (by decide)]
        exact hd)
    (by rw [stP_one, hS3, Function.update_of_ne (show sK ≠ sX by decide),
          Function.update_of_ne (show sK ≠ sR by decide), hFk sK (by decide)]
        exact hK)
  have e3R : S3 sR = Sym.mark :: C sR := by
    rw [hS3, Function.update_of_ne (show sR ≠ sX by decide), Function.update_self]
  have e3X : S3 sX = Sym.mark :: C sX := by rw [hS3, Function.update_self]
  rw [stP_two, stP_three, e3R, e3X] at r3
  -- 4. drop `2^{q₀K}`
  obtain ⟨S4, hS4⟩ : ∃ T, T = Function.update (Function.update S3 sR
      (natSyms (padR d K) ++ Sym.mark :: C sR)) sX
      (natSyms (2 ^ (q0Of d * K)) ++ Sym.mark :: C sX) := ⟨_, rfl⟩
  rw [← hS4] at r3
  have r4 := runs_dropF sX (2 ^ (q0Of d * K)) Sym.mark (C sX) S4 rfl
    (by rw [hS4, Function.update_self])
  -- 5. `a = A·R` above a floor on `sa`
  obtain ⟨S5, hS5⟩ : ∃ T, T = fl F sR (padR d K) := ⟨_, rfl⟩
  have e45 : Function.update S4 sX (C sX) = S5 := by
    rw [hS4, hS5, hS3, hF]
    funext k
    simp only [Function.update_apply, fl_apply]
    split_ifs <;> simp_all
  rw [e45] at r4
  have r5 : Runs ((Prog.seq (pushMark sa) (mulN sA sR sa t0 t1 t2 t3)).liftRegs lN) S5
      (fl S5 sa (A * padR d K)) (fun _ => True) (1 + mulCost A (padR d K)) := by
    refine runs_lN (runs_fl ?_)
    have h := runs_mulN (x := sA) (y := sR) (z := sa) (A := t0) (Bs := t1) (Acc := t2) (T := t3)
      (by decide) A (padR d K) (Sym.mark :: JA) (Sym.mark :: C sR)
      (Function.update S5 sa (Sym.mark :: S5 sa)) (termOK_mark _) (termOK_mark _)
      (by rw [Function.update_of_ne (show sA ≠ sa by decide), hS5,
            fl_ne (show sA ≠ sR by decide), hFk sA (by decide)]
          exact hA)
      (by rw [Function.update_of_ne (show sR ≠ sa by decide), hS5, fl_self, hFk sR (by decide)])
    rwa [Function.update_self] at h
  have hall := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq (runs_lN r4) r5)))
  rw [hS5, hF] at hall
  exact hall

/-! ## 3. The other case -/

/-- Otherwise: three bare floors (`e = R = a = 0`). -/
def norowsProg : Prog AK (fun _ => Sym) Reg2 :=
  (Prog.seq (pushMark se) (Prog.seq (pushMark sR) (pushMark sa))).liftRegs lN

theorem closed_norowsProg : norowsProg.Closed :=
  WP.W9comp.closed_liftRegs lN (WP.W9comp.closed_seq (closed_pushMark _)
    (WP.W9comp.closed_seq (closed_pushMark _) (closed_pushMark _)))

theorem runs_norows (C : AK → List Sym) :
    Runs norowsProg C (fl (fl (fl C se 0) sR 0) sa 0) (fun _ => True) (1 + (1 + 1)) := by
  have h := WP.W9comp.runs_seq (runs_pushMark se C) (WP.W9comp.runs_seq
    (runs_pushMark sR (Function.update C se (Sym.mark :: C se)))
    (runs_pushMark sa (Function.update (Function.update C se (Sym.mark :: C se)) sR
      (Sym.mark :: Function.update C se (Sym.mark :: C se) sR))))
  refine runs_lN (WP.W9comp.runs_congr h ?_)
  rw [fl_zero, fl_zero, fl_zero]

/-! ## 4. The branch -/

/-- The branch: compare `q₀` (`sq`) with `D` (`sD`); the rows case iff `q₀ < D`. -/
noncomputable def branchProg : Prog AK (fun _ => Sym) Reg2 :=
  .seq ((cmpN sq sD t0 t1).liftRegs lN) (.ite (fun r => isLtR r.1) rowsProg norowsProg)

theorem closed_branchProg : branchProg.Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (closed_cmpN' _ _ _ _))
    ⟨closed_rowsProg, closed_norowsProg⟩

/-- The comparison of `q` (`sq`) with `D` (`sD`), lifted to `Reg2`. -/
theorem runs_cmpL (C : AK → List Sym) (q D : ℕ) (Jq JD : List Sym)
    (hq : C sq = natSyms q ++ Sym.mark :: Jq) (hD : C sD = natSyms D ++ Sym.mark :: JD) :
    Runs ((cmpN sq sD t0 t1).liftRegs lN) C C (fun r => (lN.get r).2.2.2.2 = TMFw.Lib.ordOf q D)
      (12 * min (bitLen q) (bitLen D) + 15) :=
  DrvArith.runs_liftRegs' lN
    (runs_cmpN (x := sq) (y := sD) (t1 := t0) (t2 := t1) (by decide) q D _ _ C (termOK_mark _)
      (termOK_mark _) hq hD)

/-- **Branch, rows case** (`q < D`). -/
theorem runs_branch_rows (C : AK → List Sym) (d K A D q : ℕ) (hqD : q < D)
    (Jd JK JA JD Jq : List Sym)
    (hd : C sd = natSyms d ++ Sym.mark :: Jd) (hK : C sK = natSyms K ++ Sym.mark :: JK)
    (hA : C sA = natSyms A ++ Sym.mark :: JA) (hD : C sD = natSyms D ++ Sym.mark :: JD)
    (hq : C sq = natSyms q ++ Sym.mark :: Jq) :
    Runs branchProg C (fl (fl (fl C se (D - q)) sR (padR d K)) sa (A * padR d K)) (fun _ => True)
      (12 * min (bitLen q) (bitLen D) + 15 +
        (rowsCost D q (padRCost d K) (2 ^ (q0Of d * K)) A (padR d K) + 1)) :=
  runs_seq_ite_true (runs_cmpL C q D Jq JD hq hD)
    (fun v hv => by
      show decide (v.1.2.2.2.2 = Ordering.lt) = true
      rw [show v.1.2.2.2.2 = TMFw.Lib.ordOf q D from hv]
      simp [TMFw.Lib.ordOf, hqD])
    (runs_rows C d K A D q hqD.le Jd JK JA JD Jq hd hK hA hD hq)

/-- **Branch, other case** (`¬ q < D`). -/
theorem runs_branch_norows (C : AK → List Sym) (D q : ℕ) (hqD : ¬ q < D) (JD Jq : List Sym)
    (hD : C sD = natSyms D ++ Sym.mark :: JD) (hq : C sq = natSyms q ++ Sym.mark :: Jq) :
    Runs branchProg C (fl (fl (fl C se 0) sR 0) sa 0) (fun _ => True)
      (12 * min (bitLen q) (bitLen D) + 15 + (1 + (1 + 1) + 1)) :=
  runs_seq_ite_false (runs_cmpL C q D Jq JD hq hD)
    (fun v hv => by
      show decide (v.1.2.2.2.2 = Ordering.lt) = false
      rw [show v.1.2.2.2.2 = TMFw.Lib.ordOf q D from hv]
      unfold TMFw.Lib.ordOf
      split_ifs <;> simp_all)
    (runs_norows C)

end SubNLogN.Machine.Layer.DrvDescArithAux
