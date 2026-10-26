/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvCostKit
import SubNLogN.Machine.Layer.DrvArithBounds

/-!
# Layer driver: kernels of the pre-phase parameters (`Machine/Layer/DrvPreParamsKit.lean`)

NatArith kernels over an injective stack map `st : Fin n → K` (every stack other than the
destination is restored, temporaries may hold arbitrary content), used by `DrvPreParamsStmt`
(`Machine/Layer/DrvParamsDefs.lean`) and by the post-phase parameters:
* `wgN`: `P ↦ 3P + 3` (the guarded width `drvWg`);
* `q0BrN`: `q₀ = q0Of d` on a floored work stack, the test `q₀ < D`, a branch, the drop of the floor;
  `rowsN` pushes the rows flag `bit (decide (q₀ < D))`, `q1N` pushes `min q₀ D` (`drvQ1`).
Each comes with an explicit cost (`wgCost`, `rowsCost`, `q1Cost`) and a polynomial bound; `wgN2`,
`rowsN2`, `q1N2` are the lifts to the registers `DrvArith.Reg2`. Fully proved, no placeholders.
-/

namespace SubNLogN.Machine.Layer.DrvPreParamsAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.NatArith
open SubNLogN.Machine.Layer.DrvArith SubNLogN.Machine.Layer.DrvParamsAux
open SubNLogN.Math.Networks (q0Of Wc mH)

/-! ## 1. `P ↦ 3P + 3` -/

section Wg

variable {K : Type}

/-- `P ↦ 3P + 3`: `natSyms P` on `st 0` (restored) ↦ pushes `natSyms (P * 3 + 3)` on `st 1`;
`st 2`, `st 3` floored work stacks, `st 4 … st 10` temporaries (restored). -/
def wgN (st : Fin 12 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (.seq (pushMark (st 2)) (.seq (copyN (st 0) (st 2) (st 4))
    (mulConstN (st 2) 3 (st 5) (st 6) (st 7) (st 8) (st 9) (st 10))))
  (.seq (.seq (pushMark (st 3)) (pushNat (st 3) 3))
  (.seq (addN (st 2) (st 3) (st 1) (st 4) (st 5) (st 6))
  (.seq (dropF (st 3)) (dropF (st 2)))))

/-- `wgN` on the registers `Reg2`. -/
def wgN2 (st : Fin 12 → K) : Prog K (fun _ => Sym) Reg2 := (wgN st).liftRegs lN

theorem closed_wgN (st : Fin 12 → K) : (wgN st).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq
    (closed_copyN _ _ _) (closed_mulConstN _ _ _ _ _ _ _ _)))
  (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (closed_pushNat _ _))
  (WP.W9comp.closed_seq (closed_addN _ _ _ _ _ _)
  (WP.W9comp.closed_seq (closed_dropF _) (closed_dropF _))))

theorem closed_wgN2 (st : Fin 12 → K) : (wgN2 st).Closed :=
  WP.W9comp.closed_liftRegs lN (closed_wgN st)

/-- The cost of `wgN`. -/
def wgCost (P : ℕ) : ℕ :=
  (1 + ((7 * bitLen P + 7) + mulConstCost P 3)) + ((1 + (bitLen 3 + 1)) +
    (20 * (bitLen (P * 3) + bitLen 3 + 1) + ((2 * bitLen 3 + 2) + (2 * bitLen (P * 3) + 2))))

theorem wgCost_le (P : ℕ) : wgCost P ≤ 3000 * (bitLen P + 1) ^ 2 := by
  have h3 : bitLen 3 ≤ 2 := bitLen_le_of_lt' (by norm_num)
  have hm3 : bitLen (P * 3) ≤ bitLen P + 2 := le_trans (bitLen_mul_le' P 3) (by omega)
  have hc := mulConstCost_le' (a := P) (c := 3) (X := bitLen P + 2) (by omega) (by omega) hm3
  have e1 : (bitLen P + 2 + 1) ^ 2 ≤ 9 * (bitLen P + 1) ^ 2 := by nlinarith
  have e2 : bitLen P + 1 ≤ (bitLen P + 1) ^ 2 := by nlinarith
  unfold wgCost
  omega

variable [DecidableEq K]

theorem runs_wgN {st : Fin 12 → K} (hst : Function.Injective st) (P : ℕ) (rP : List Sym)
    (S : K → List Sym) (hrP : TermOK rP) (hP : S (st 0) = natSyms P ++ rP) :
    Runs (wgN st) S (Function.update S (st 1) (natSyms (P * 3 + 3) ++ S (st 1))) (fun _ => True)
      (wgCost P) := by
  have hnd : ∀ l : List (Fin 12), l.Nodup → (l.map st).Nodup := fun l hl => hl.map hst
  obtain ⟨S1, hS1⟩ : ∃ T, T = fl S (st 2) (P * 3) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ T, T = fl S1 (st 3) 3 := ⟨_, rfl⟩
  have r1 : Runs (.seq (pushMark (st 2)) (.seq (copyN (st 0) (st 2) (st 4))
      (mulConstN (st 2) 3 (st 5) (st 6) (st 7) (st 8) (st 9) (st 10)))) S S1 (fun _ => True)
      (1 + ((7 * bitLen P + 7) + mulConstCost P 3)) := by
    rw [hS1]
    apply runs_fl
    have c1 := runs_copyN (src := st 0) (dst := st 2) (tmp := st 4) (hst.ne (by decide))
      (hst.ne (by decide)) (hst.ne (by decide)) P rP
      (Function.update S (st 2) (Sym.mark :: S (st 2))) hrP
      (by rw [Function.update_of_ne (hst.ne (show (0 : Fin 12) ≠ 2 by decide)), hP])
    have c2 := runs_mulConstN (k := st 2) (Q := st 5) (Tdst := st 6) (A := st 7) (Bs := st 8)
      (Acc := st 9) (T := st 10) (hnd [2, 5, 6, 7, 8, 9, 10] (by decide)) 3 P
      (Sym.mark :: S (st 2))
      (Function.update (Function.update S (st 2) (Sym.mark :: S (st 2))) (st 2)
        (natSyms P ++ Function.update S (st 2) (Sym.mark :: S (st 2)) (st 2)))
      (termOK_mark _) (by rw [Function.update_self, Function.update_self])
    refine WP.W9comp.runs_congr (WP.W9comp.runs_seq c1 c2) ?_
    rw [Function.update_idem]
  have r2 : Runs (.seq (pushMark (st 3)) (pushNat (st 3) 3)) S1 S2 (fun _ => True)
      (1 + (bitLen 3 + 1)) := by
    rw [hS2]
    apply runs_fl
    have c := runs_pushNat (st 3) 3 (Function.update S1 (st 3) (Sym.mark :: S1 (st 3)))
    rw [Function.update_self] at c
    exact c
  have r3 : Runs (addN (st 2) (st 3) (st 1) (st 4) (st 5) (st 6)) S2
      (Function.update S2 (st 1) (natSyms (P * 3 + 3) ++ S (st 1))) (fun _ => True)
      (20 * (bitLen (P * 3) + bitLen 3 + 1)) := by
    have c := runs_addN (x := st 2) (y := st 3) (z := st 1) (t1 := st 4) (t2 := st 5)
      (t3 := st 6) (hnd [2, 3, 1, 4, 5, 6] (by decide)) (P * 3) 3 (Sym.mark :: S (st 2))
      (Sym.mark :: S1 (st 3)) S2 (termOK_mark _) (termOK_mark _)
      (by simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false])
      (by simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false])
    have e1 : S2 (st 1) = S (st 1) := by
      simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
    rw [e1] at c
    exact c
  have d1 := runs_dropF (st 3) 3 Sym.mark (S (st 3))
    (Function.update S2 (st 1) (natSyms (P * 3 + 3) ++ S (st 1))) rfl
    (by simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false])
  have d2 := runs_dropF (st 2) (P * 3) Sym.mark (S (st 2))
    (Function.update (Function.update S2 (st 1) (natSyms (P * 3 + 3) ++ S (st 1))) (st 3)
      (S (st 3))) rfl
    (by simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r1
    (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3 (WP.W9comp.runs_seq d1 d2)))) ?_)
    (fun _ _ => trivial) le_rfl
  funext k
  rcases eq_or_ne k (st 1) with rfl | h1
  · simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
  rcases eq_or_ne k (st 2) with rfl | h2
  · simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
  rcases eq_or_ne k (st 3) with rfl | h3
  · simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
  simp only [hS2, hS1, fl, Function.update_apply, h1, h2, h3, if_false]

theorem runs_wgN2 {st : Fin 12 → K} (hst : Function.Injective st) (P : ℕ) (rP : List Sym)
    (S : K → List Sym) (hrP : TermOK rP) (hP : S (st 0) = natSyms P ++ rP) :
    Runs (wgN2 st) S (Function.update S (st 1) (natSyms (P * 3 + 3) ++ S (st 1))) (fun _ => True)
      (wgCost P) :=
  runs_lN (runs_wgN hst P rP S hrP hP)

end Wg

/-! ## 2. The `q₀` branch: rows flag and `min q₀ D` -/

section Q0Br

variable {K : Type}

/-- The `q0N` stacks inside `q0BrN`: `d` on `st 0`, `q₀` onto `st 3`, temporaries `st 4 … st 17`. -/
def q0BrMap : Fin 16 → Fin 20 := ![0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

/-- `q₀ = q0Of d` on a floored `st 3` (`d` on `st 0`), the test `q₀ < D` (`D` on `st 1`), the
branch `p` / `q`, the drop of the floor; `st 18`, `st 19` are the comparison temporaries. -/
noncomputable def q0BrN (st : Fin 20 → K) (p q : Prog K (fun _ => Sym) Reg) :
    Prog K (fun _ => Sym) Reg :=
  .seq (.seq (pushMark (st 3)) (q0N (st ∘ q0BrMap)))
    (.seq (.seq (cmpN (st 3) (st 1) (st 18) (st 19)) (.ite isLtR p q)) (dropF (st 3)))

theorem closed_q0BrN (st : Fin 20 → K) (p q : Prog K (fun _ => Sym) Reg) (hp : p.Closed)
    (hq : q.Closed) : (q0BrN st p q).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (closed_q0N _))
    (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_cmpN' _ _ _ _) ⟨hp, hq⟩)
      (closed_dropF _))

/-- **The rows flag**: `d`, `D` on `st 0`, `st 1` (restored) ↦ pushes `bit (decide (q₀ < D))` on
`st 2`. -/
noncomputable def rowsN (st : Fin 20 → K) : Prog K (fun _ => Sym) Reg :=
  q0BrN st (pushW (st 2) (.bit true)) (pushW (st 2) (.bit false))

noncomputable def rowsN2 (st : Fin 20 → K) : Prog K (fun _ => Sym) Reg2 := (rowsN st).liftRegs lN

/-- **`min q₀ D`** (`drvQ1`): `d`, `D` on `st 0`, `st 1` (restored) ↦ pushes `natSyms (min q₀ D)`
on `st 2`. -/
noncomputable def q1N (st : Fin 20 → K) : Prog K (fun _ => Sym) Reg :=
  q0BrN st (copyN (st 3) (st 2) (st 18)) (copyN (st 1) (st 2) (st 18))

noncomputable def q1N2 (st : Fin 20 → K) : Prog K (fun _ => Sym) Reg2 := (q1N st).liftRegs lN

theorem closed_rowsN2 (st : Fin 20 → K) : (rowsN2 st).Closed :=
  WP.W9comp.closed_liftRegs lN (closed_q0BrN st _ _ (closed_pushW _ _) (closed_pushW _ _))

theorem closed_q1N2 (st : Fin 20 → K) : (q1N2 st).Closed :=
  WP.W9comp.closed_liftRegs lN (closed_q0BrN st _ _ (closed_copyN _ _ _) (closed_copyN _ _ _))

/-- The cost of `rowsN`. -/
noncomputable def rowsCost (d D : ℕ) : ℕ :=
  (1 + q0Cost d) + ((12 * min (bitLen (q0Of d)) (bitLen D) + 15 + (max 1 1 + 1)) +
    (2 * bitLen (q0Of d) + 2))

/-- The cost of `q1N`. -/
noncomputable def q1Cost (d D : ℕ) : ℕ :=
  (1 + q0Cost d) + ((12 * min (bitLen (q0Of d)) (bitLen D) + 15 +
    (max (7 * bitLen (q0Of d) + 7) (7 * bitLen D + 7) + 1)) + (2 * bitLen (q0Of d) + 2))

theorem isLtR_of_ordOf {r : Reg} {a b : ℕ} (h : r.2.2.2.2 = ordOf a b) :
    isLtR r = decide (a < b) := by
  unfold isLtR
  rw [h]
  unfold ordOf
  by_cases hab : a < b
  · simp [hab]
  · by_cases hab' : a = b
    · simp [hab, hab']
    · simp [hab, hab']

variable [DecidableEq K]

theorem runs_q0BrN {st : Fin 20 → K} (hst : Function.Injective st)
    (p q : Prog K (fun _ => Sym) Reg) (d D : ℕ) (rd rD : List Sym) (S : K → List Sym)
    (hrd : TermOK rd) (hrD : TermOK rD) (hd : S (st 0) = natSyms d ++ rd)
    (hD : S (st 1) = natSyms D ++ rD) (Z1 Z2 : List Sym) (T1 T2 : ℕ)
    (hp : q0Of d < D → Runs p (fl S (st 3) (q0Of d))
      (Function.update (fl S (st 3) (q0Of d)) (st 2) Z1) (fun _ => True) T1)
    (hq : ¬ q0Of d < D → Runs q (fl S (st 3) (q0Of d))
      (Function.update (fl S (st 3) (q0Of d)) (st 2) Z2) (fun _ => True) T2) :
    Runs (q0BrN st p q) S (Function.update S (st 2) (if q0Of d < D then Z1 else Z2))
      (fun _ => True) ((1 + q0Cost d) + ((12 * min (bitLen (q0Of d)) (bitLen D) + 15 +
        (max T1 T2 + 1)) + (2 * bitLen (q0Of d) + 2))) := by
  have hnd : ∀ l : List (Fin 20), l.Nodup → (l.map st).Nodup := fun l hl => hl.map hst
  have r1 : Runs (.seq (pushMark (st 3)) (q0N (st ∘ q0BrMap))) S (fl S (st 3) (q0Of d))
      (fun _ => True) (1 + q0Cost d) := by
    apply runs_fl
    have c := runs_q0N (hst.comp (by decide : Function.Injective q0BrMap)) d rd
      (Function.update S (st 3) (Sym.mark :: S (st 3))) hrd
      (by rw [show (st ∘ q0BrMap) 0 = st 0 from rfl,
            Function.update_of_ne (hst.ne (show (0 : Fin 20) ≠ 3 by decide)), hd])
    rw [show (st ∘ q0BrMap) 1 = st 3 from rfl, Function.update_self] at c
    exact c
  have h0 := runs_cmpN (x := st 3) (y := st 1) (t1 := st 18) (t2 := st 19)
    (hnd [3, 1, 18, 19] (by decide)) (q0Of d) D (Sym.mark :: S (st 3)) rD
    (fl S (st 3) (q0Of d)) (termOK_mark _) hrD (fl_self S (st 3) (q0Of d))
    (by rw [fl_ne (hst.ne (show (1 : Fin 20) ≠ 3 by decide)), hD])
  have rm : Runs (.seq (cmpN (st 3) (st 1) (st 18) (st 19)) (.ite isLtR p q))
      (fl S (st 3) (q0Of d))
      (Function.update (fl S (st 3) (q0Of d)) (st 2) (if q0Of d < D then Z1 else Z2))
      (fun _ => True) (12 * min (bitLen (q0Of d)) (bitLen D) + 15 + (max T1 T2 + 1)) := by
    by_cases h : q0Of d < D
    · rw [if_pos h]
      exact runs_seq_ite_true h0 (fun v hv => by rw [isLtR_of_ordOf hv]; exact decide_eq_true h)
        (WP.W9comp.runs_mono (hp h) (fun _ _ => trivial) (le_max_left _ _))
    · rw [if_neg h]
      exact runs_seq_ite_false h0 (fun v hv => by rw [isLtR_of_ordOf hv]; exact decide_eq_false h)
        (WP.W9comp.runs_mono (hq h) (fun _ _ => trivial) (le_max_right _ _))
  have r3 := runs_dropF (st 3) (q0Of d) Sym.mark (S (st 3))
    (Function.update (fl S (st 3) (q0Of d)) (st 2) (if q0Of d < D then Z1 else Z2)) rfl
    (by rw [Function.update_of_ne (hst.ne (show (3 : Fin 20) ≠ 2 by decide)), fl_self])
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq rm r3)) ?_
  rw [fl]
  exact upd_drop_under (hst.ne (show (3 : Fin 20) ≠ 2 by decide)) S _ _

theorem runs_rowsN {st : Fin 20 → K} (hst : Function.Injective st) (d D : ℕ) (rd rD : List Sym)
    (S : K → List Sym) (hrd : TermOK rd) (hrD : TermOK rD) (hd : S (st 0) = natSyms d ++ rd)
    (hD : S (st 1) = natSyms D ++ rD) :
    Runs (rowsN st) S (Function.update S (st 2) (Sym.bit (decide (q0Of d < D)) :: S (st 2)))
      (fun _ => True) (rowsCost d D) := by
  have e2 : fl S (st 3) (q0Of d) (st 2) = S (st 2) :=
    fl_ne (hst.ne (show (2 : Fin 20) ≠ 3 by decide)) _
  have c := runs_q0BrN hst (pushW (st 2) (.bit true)) (pushW (st 2) (.bit false)) d D rd rD S
    hrd hrD hd hD (Sym.bit true :: S (st 2)) (Sym.bit false :: S (st 2)) 1 1
    (fun _ => by
      have h1 := runs_pushW (st 2) (Sym.bit true) (fl S (st 3) (q0Of d))
      rwa [e2] at h1)
    (fun _ => by
      have h1 := runs_pushW (st 2) (Sym.bit false) (fl S (st 3) (q0Of d))
      rwa [e2] at h1)
  refine WP.W9comp.runs_congr c ?_
  by_cases h : q0Of d < D
  · rw [if_pos h, decide_eq_true h]
  · rw [if_neg h, decide_eq_false h]

theorem runs_rowsN2 {st : Fin 20 → K} (hst : Function.Injective st) (d D : ℕ) (rd rD : List Sym)
    (S : K → List Sym) (hrd : TermOK rd) (hrD : TermOK rD) (hd : S (st 0) = natSyms d ++ rd)
    (hD : S (st 1) = natSyms D ++ rD) :
    Runs (rowsN2 st) S (Function.update S (st 2) (Sym.bit (decide (q0Of d < D)) :: S (st 2)))
      (fun _ => True) (rowsCost d D) :=
  runs_lN (runs_rowsN hst d D rd rD S hrd hrD hd hD)

theorem runs_q1N {st : Fin 20 → K} (hst : Function.Injective st) (d D : ℕ) (rd rD : List Sym)
    (S : K → List Sym) (hrd : TermOK rd) (hrD : TermOK rD) (hd : S (st 0) = natSyms d ++ rd)
    (hD : S (st 1) = natSyms D ++ rD) :
    Runs (q1N st) S (Function.update S (st 2) (natSyms (min (q0Of d) D) ++ S (st 2)))
      (fun _ => True) (q1Cost d D) := by
  have e2 : fl S (st 3) (q0Of d) (st 2) = S (st 2) :=
    fl_ne (hst.ne (show (2 : Fin 20) ≠ 3 by decide)) _
  have c := runs_q0BrN hst (copyN (st 3) (st 2) (st 18)) (copyN (st 1) (st 2) (st 18)) d D rd rD
    S hrd hrD hd hD (natSyms (q0Of d) ++ S (st 2)) (natSyms D ++ S (st 2))
    (7 * bitLen (q0Of d) + 7) (7 * bitLen D + 7)
    (fun _ => by
      have h1 := runs_copyN (src := st 3) (dst := st 2) (tmp := st 18) (hst.ne (by decide))
        (hst.ne (by decide)) (hst.ne (by decide)) (q0Of d) (Sym.mark :: S (st 3))
        (fl S (st 3) (q0Of d)) (termOK_mark _) (fl_self S (st 3) (q0Of d))
      rwa [e2] at h1)
    (fun _ => by
      have h1 := runs_copyN (src := st 1) (dst := st 2) (tmp := st 18) (hst.ne (by decide))
        (hst.ne (by decide)) (hst.ne (by decide)) D rD (fl S (st 3) (q0Of d)) hrD
        (by rw [fl_ne (hst.ne (show (1 : Fin 20) ≠ 3 by decide)), hD])
      rwa [e2] at h1)
  refine WP.W9comp.runs_congr c ?_
  by_cases h : q0Of d < D
  · rw [if_pos h, min_eq_left (le_of_lt h)]
  · rw [if_neg h, min_eq_right (not_lt.1 h)]

theorem runs_q1N2 {st : Fin 20 → K} (hst : Function.Injective st) (d D : ℕ) (rd rD : List Sym)
    (S : K → List Sym) (hrd : TermOK rd) (hrD : TermOK rD) (hd : S (st 0) = natSyms d ++ rd)
    (hD : S (st 1) = natSyms D ++ rD) :
    Runs (q1N2 st) S (Function.update S (st 2) (natSyms (min (q0Of d) D) ++ S (st 2)))
      (fun _ => True) (q1Cost d D) :=
  runs_lN (runs_q1N hst d D rd rD S hrd hrD hd hD)

end Q0Br

/-! ## 3. Cost bounds of the `q₀` branch -/

theorem rowsCost_le : ∃ c, ∀ d D, rowsCost d D ≤ c * (bitLen d + bitLen D + 1) ^ 3 := by
  obtain ⟨c0, hc0⟩ := q0Cost_le
  obtain ⟨cW, hcW⟩ : ∃ cW, cW = Nat.clog 2 Wc := ⟨_, rfl⟩
  refine ⟨c0 + 2 * cW + 40, fun d D => ?_⟩
  have h1 := hc0 d
  have h2 : bitLen (q0Of d) ≤ cW * (bitLen d + 1) := by
    rw [hcW]; exact le_trans (bitLen_le_self' _) (q0Of_le d)
  unfold rowsCost
  generalize q0Cost d = A at h1 ⊢
  generalize bitLen (q0Of d) = Bq at h2 ⊢
  generalize bitLen d = Bd at h1 h2 ⊢
  generalize bitLen D = BD
  have e0 : Bd + BD + 1 ≤ (Bd + BD + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have e1 : c0 * (Bd + 1) ^ 3 ≤ c0 * (Bd + BD + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have e2 : cW * (Bd + 1) ≤ cW * (Bd + BD + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (le_trans (by omega) e0)
  have e3 : (c0 + 2 * cW + 40) * (Bd + BD + 1) ^ 3 = c0 * (Bd + BD + 1) ^ 3 +
      2 * (cW * (Bd + BD + 1) ^ 3) + 40 * (Bd + BD + 1) ^ 3 := by ring
  have h3 : min Bq BD ≤ BD := min_le_right _ _
  rw [e3]
  omega

theorem q1Cost_le : ∃ c, ∀ d D, q1Cost d D ≤ c * (bitLen d + bitLen D + 1) ^ 3 := by
  obtain ⟨c0, hc0⟩ := q0Cost_le
  obtain ⟨cW, hcW⟩ : ∃ cW, cW = Nat.clog 2 Wc := ⟨_, rfl⟩
  refine ⟨c0 + 9 * cW + 60, fun d D => ?_⟩
  have h1 := hc0 d
  have h2 : bitLen (q0Of d) ≤ cW * (bitLen d + 1) := by
    rw [hcW]; exact le_trans (bitLen_le_self' _) (q0Of_le d)
  unfold q1Cost
  generalize q0Cost d = A at h1 ⊢
  generalize bitLen (q0Of d) = Bq at h2 ⊢
  generalize bitLen d = Bd at h1 h2 ⊢
  generalize bitLen D = BD
  have e0 : Bd + BD + 1 ≤ (Bd + BD + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have e1 : c0 * (Bd + 1) ^ 3 ≤ c0 * (Bd + BD + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have e2 : cW * (Bd + 1) ≤ cW * (Bd + BD + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (le_trans (by omega) e0)
  have e3 : (c0 + 9 * cW + 60) * (Bd + BD + 1) ^ 3 = c0 * (Bd + BD + 1) ^ 3 +
      9 * (cW * (Bd + BD + 1) ^ 3) + 60 * (Bd + BD + 1) ^ 3 := by ring
  have h3 : min Bq BD ≤ BD := min_le_right _ _
  rw [e3]
  omega

end SubNLogN.Machine.Layer.DrvPreParamsAux
