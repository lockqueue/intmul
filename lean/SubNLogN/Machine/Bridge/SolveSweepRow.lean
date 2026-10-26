/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveSweepLoop
import SubNLogN.Machine.Bridge.SolveSweepOut

/-!
# K5-SOLVE (1h): row passes of the sweep kernel

One row of each pass: the element loop (driven by the state row or the parameter row) followed by
the rewinds of the touched rows (`drP`, record order restored):
* `r1`: prefix row `0` (`e1` per column, driven by the `μ` row);
* `r2`: prefix row `j ≥ 1` (`e2` per column);
* `r3`: the closure row (`e3` per column);
* `r4`: a second-pass row (`e4` per column, `b` from the stream `bS2`).
All proved.
-/

namespace SubNLogN.Machine.Bridge.SolveAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine

/-! ## List helpers -/

/-- A parameter as a one-coefficient record value. -/
def toP (m : ℤ) : CInt := (m, 0)

theorem rec1s_drop_cons (w : ℕ) (l : List CInt) (s : ℕ) (hs : s < l.length) :
    rec1s w (l.drop s) = carrSyms w [[l[s]]] ++ rec1s w (l.drop (s + 1)) := by
  rw [List.drop_eq_getElem_cons hs, rec1s_cons]

theorem rec1s_take_succ_rev (w : ℕ) (l : List CInt) (s : ℕ) (hs : s < l.length) :
    rec1s w (l.take (s + 1)).reverse = carrSyms w [[l[s]]] ++ rec1s w (l.take s).reverse := by
  rw [List.take_succ, List.getElem?_eq_getElem hs, Option.toList_some, List.reverse_append,
    List.reverse_singleton, rec1s_append, rec1s_cons, rec1s_nil, List.append_nil]

theorem rec1s_drop_length (w : ℕ) (l : List CInt) : rec1s w (l.drop l.length) = [] := by simp

section Rows

variable {Ecm Erh Eca Rcm Rrh Rca : Type} [Fintype Ecm] [DecidableEq Ecm] [Fintype Erh]
  [DecidableEq Erh] [Fintype Eca] [DecidableEq Eca]
variable (G : LeafProgs Ecm Erh Eca Rcm Rrh Rca)

/-- Prefix row `j ≥ 1`: the element loop (driven by the state row `stI`), then the rewinds of the
state row and the two parameter rows. -/
def r2 : PS Ecm Erh Eca Rcm Rrh Rca :=
  .seq (whileP lS (.inr .stI) (e2 G)) (.seq (drP lS (.inr .stO) (.inr .stI))
    (.seq (drP lS (.inr .muO) (.inl .mu)) (drP lS (.inr .naO) (.inl .na))))

/-- State of the prefix row after `s` columns. `V0` gives the stacks below the row records. -/
def r2V (V0 : SwD ⊕ SwW → List Sym) (q wI wT M : ℕ) (yr : List CInt) (D : List Sym)
    (mus nas : List ℤ) (prev : List CInt) (s : ℕ) : SwD ⊕ SwW → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update V0
      (.inl .dat) (rec1s wI (yr.drop s) ++ D))
      (.inl .mu) (rec1s wT ((mus.map toP).drop s) ++ V0 (.inl .mu)))
      (.inr .muO) (rec1s wT ((mus.map toP).take s).reverse ++ V0 (.inr .muO)))
      (.inl .na) (rec1s wT ((nas.map toP).drop s) ++ V0 (.inl .na)))
      (.inr .naO) (rec1s wT ((nas.map toP).take s).reverse ++ V0 (.inr .naO)))
      (.inr .stI) (rec1s wI (prev.drop s) ++ V0 (.inr .stI)))
      (.inr .stO) (rec1s wI ((stepRowI q M mus nas yr prev).take s).reverse ++ V0 (.inr .stO)))
      (.inr .bS) (rec1s wI ((bRowI q M mus yr).take s).reverse ++ V0 (.inr .bS))

end Rows

end SubNLogN.Machine.Bridge.SolveAux

namespace SubNLogN.Machine.Bridge.SolveAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine

section RowsProofs

variable {Ecm Erh Eca Rcm Rrh Rca : Type} [Fintype Ecm] [DecidableEq Ecm] [Fintype Erh]
  [DecidableEq Erh] [Fintype Eca] [DecidableEq Eca]
variable (G : LeafProgs Ecm Erh Eca Rcm Rrh Rca)

theorem getD_eq_getElem' {α : Type} (l : List α) (d : α) (s : ℕ) (h : s < l.length) :
    l.getD s d = l[s] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem bRowI_getElem (q M : ℕ) (mus : List ℤ) (yr : List CInt) (s : ℕ) (hs : s < M) :
    (bRowI q M mus yr)[s]'(by simp [bRowI]; exact hs) = bI q (mus.getD s 0) (yr.getD s 0) := by
  simp [bRowI]

theorem stepRowI_getElem (q M : ℕ) (mus nas : List ℤ) (yr prev : List CInt) (s : ℕ) (hs : s < M) :
    (stepRowI q M mus nas yr prev)[s]'(by simp [stepRowI]; exact hs) =
      stepI q (nas.getD s 0) (bI q (mus.getD s 0) (yr.getD s 0)) (prev.getD s 0) := by
  simp [stepRowI]

/-- Width premises of one prefix row. -/
structure Row2Fits (q wI wT M : ℕ) (mus nas : List ℤ) (yr prev : List CInt) : Prop where
  y : ∀ s, s < M → Fits2 wI (yr.getD s 0)
  mu : ∀ s, s < M → FitsTwos wT (mus.getD s 0)
  na : ∀ s, s < M → FitsTwos wT (nas.getD s 0)
  p : ∀ s, s < M → Fits2 wI (prev.getD s 0)
  b : ∀ s, s < M → Fits2 wI (bI q (mus.getD s 0) (yr.getD s 0))
  p' : ∀ s, s < M →
    Fits2 wI (stepI q (nas.getD s 0) (bI q (mus.getD s 0) (yr.getD s 0)) (prev.getD s 0))

theorem runs_r2_step {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V0 : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V0)
    {yr prev : List CInt} {D : List Sym} {mus nas : List ℤ}
    (hyr : yr.length = M) (hpr : prev.length = M) (hmus : mus.length = M) (hnas : nas.length = M)
    (hF : Row2Fits q wI wT M mus nas yr prev) (s : ℕ) (hs : s < M) :
    Runs (e2 G) (mk base (r2V V0 q wI wT M yr D mus nas prev s))
      (mk base (r2V V0 q wI wT M yr D mus nas prev (s + 1))) (fun _ => True)
      (e2Cost Ccm Crh Cca wI wT q) := by
  have hy : s < yr.length := by omega
  have hp : s < prev.length := by omega
  have hm : s < (mus.map toP).length := by simp; omega
  have hn : s < (nas.map toP).length := by simp; omega
  have hb : s < (bRowI q M mus yr).length := by simp [bRowI]; omega
  have hst : s < (stepRowI q M mus nas yr prev).length := by simp [stepRowI]; omega
  have gy : yr.getD s 0 = yr[s] := getD_eq_getElem' _ _ _ hy
  have gp : prev.getD s 0 = prev[s] := getD_eq_getElem' _ _ _ hp
  have gm : mus.getD s 0 = mus[s]'(by omega) := getD_eq_getElem' _ _ _ (by omega)
  have gn : nas.getD s 0 = nas[s]'(by omega) := getD_eq_getElem' _ _ _ (by omega)
  have hT' : TempsEmpty (r2V V0 q wI wT M yr D mus nas prev s) := by
    constructor <;> simp [r2V, Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg,
      hT.tmp]
  have h := runs_e2 G scm srh sca hB hwI hwT (r2V V0 q wI wT M yr D mus nas prev s) hT'
    (y := yr[s]) (p := prev[s]) (mu := mus[s]'(by omega)) (na := nas[s]'(by omega))
    (D := rec1s wI (yr.drop (s + 1)) ++ D)
    (Mu := rec1s wT ((mus.map toP).drop (s + 1)) ++ V0 (.inl .mu))
    (Na := rec1s wT ((nas.map toP).drop (s + 1)) ++ V0 (.inl .na))
    (St := rec1s wI (prev.drop (s + 1)) ++ V0 (.inr .stI))
    (by simp [r2V, Function.update_apply, rec1s_drop_cons wI yr s hy])
    (by simp [r2V, Function.update_apply, rec1s_drop_cons wT (mus.map toP) s hm, toP])
    (by simp [r2V, Function.update_apply, rec1s_drop_cons wT (nas.map toP) s hn, toP])
    (by simp [r2V, Function.update_apply, rec1s_drop_cons wI prev s hp])
    (gy ▸ hF.y s hs) (gm ▸ hF.mu s hs) (gn ▸ hF.na s hs) (gp ▸ hF.p s hs)
    (by rw [← gm, ← gy]; exact hF.b s hs) (by rw [← gm, ← gy, ← gn, ← gp]; exact hF.p' s hs)
  refine WP.W9comp.runs_congr h ?_
  congr 1
  have e1 := rec1s_take_succ_rev wT (mus.map toP) s hm
  have e2 := rec1s_take_succ_rev wT (nas.map toP) s hn
  have e3 := rec1s_take_succ_rev wI (stepRowI q M mus nas yr prev) s hst
  have e4 := rec1s_take_succ_rev wI (bRowI q M mus yr) s hb
  rw [stepRowI_getElem q M mus nas yr prev s hs, gy, gp, gm, gn] at e3
  rw [bRowI_getElem q M mus yr s hs, gy, gm] at e4
  simp only [List.getElem_map, toP] at e1 e2
  funext x
  rcases x with d | w
  · cases d <;> simp [e2Post, r2V, Function.update_apply, e1, e2]
  · cases w <;> simp [e2Post, r2V, Function.update_apply, e1, e2, e3, e4]

theorem runs_r2_loop {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V0 : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V0)
    (hSt : TermOK (V0 (.inr .stI)))
    {yr prev : List CInt} {D : List Sym} {mus nas : List ℤ}
    (hyr : yr.length = M) (hpr : prev.length = M) (hmus : mus.length = M) (hnas : nas.length = M)
    (hF : Row2Fits q wI wT M mus nas yr prev) :
    Runs (whileP lS (.inr .stI) (e2 G)) (mk base (r2V V0 q wI wT M yr D mus nas prev 0))
      (mk base (r2V V0 q wI wT M yr D mus nas prev M)) (fun _ => True)
      (1 + loopCost (fun _ => e2Cost Ccm Crh Cca wI wT q + 1) M) := by
  have htop : ∀ n, n ≤ M → optIsBit ((mk base (r2V V0 q wI wT M yr D mus nas prev (M - n)))
      (loc (.inr .stI))).head? = decide (0 < n) := by
    intro n hn
    have e : (mk base (r2V V0 q wI wT M yr D mus nas prev (M - n))) (loc (.inr .stI)) =
        rec1s wI (prev.drop (M - n)) ++ V0 (.inr .stI) := by
      simp [r2V, Function.update_apply]
    rw [e, optIsBit_rec1s wI hwI _ _ hSt, List.length_drop, hpr, Nat.sub_sub_self hn]
  have hstep : ∀ n, n < M →
      Runs (e2 G) (mk base (r2V V0 q wI wT M yr D mus nas prev (M - (n + 1))))
        (mk base (r2V V0 q wI wT M yr D mus nas prev (M - n))) (fun _ => True)
        (e2Cost Ccm Crh Cca wI wT q) := by
    intro n hn
    have e : M - n = M - (n + 1) + 1 := by omega
    rw [e]
    exact runs_r2_step G scm srh sca hB hwI hwT V0 hT hyr hpr hmus hnas hF (M - (n + 1)) (by omega)
  have h := runs_whileP lS (.inr .stI) (e2 G)
    (fun n => mk base (r2V V0 q wI wT M yr D mus nas prev (M - n))) M
    (fun _ => e2Cost Ccm Crh Cca wI wT q) htop hstep
  simp only [Nat.sub_self, Nat.sub_zero] at h
  exact h

/-- Cost of one prefix row. -/
def r2Cost (Ccm Crh Cca wI wT q M : ℕ) : ℕ :=
  M * (e2Cost Ccm Crh Cca wI wT q + 2 + (12 * wI + 12) + 2 * (12 * wT + 12)) + 8

/-- **One prefix row** `j ≥ 1`: consumes the data row, replaces the state row by the new states,
pushes the row's `b` values (reversed) on `bS`; the parameter rows are restored. -/
theorem runs_r2 {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V)
    {yr prev : List CInt} {D Mu Na St : List Sym} {mus nas : List ℤ}
    (hyr : yr.length = M) (hpr : prev.length = M) (hmus : mus.length = M) (hnas : nas.length = M)
    (hF : Row2Fits q wI wT M mus nas yr prev)
    (hdat : V (.inl .dat) = rec1s wI yr ++ D)
    (hmu : V (.inl .mu) = rec1s wT (mus.map toP) ++ Mu)
    (hna : V (.inl .na) = rec1s wT (nas.map toP) ++ Na)
    (hst : V (.inr .stI) = rec1s wI prev ++ St) (tSt : TermOK St)
    (hmuO : V (.inr .muO) = []) (hnaO : V (.inr .naO) = []) (hstO : V (.inr .stO) = []) :
    Runs (r2 G) (mk base V)
      (mk base (Function.update (Function.update (Function.update V (.inl .dat) D)
        (.inr .stI) (rec1s wI (stepRowI q M mus nas yr prev) ++ St))
        (.inr .bS) (rec1s wI (bRowI q M mus yr).reverse ++ V (.inr .bS))))
      (fun _ => True) (r2Cost Ccm Crh Cca wI wT q M) := by
  obtain ⟨V0, hV0⟩ : ∃ V0 : SwD ⊕ SwW → List Sym, V0 = Function.update (Function.update
      (Function.update V (.inl .mu) Mu) (.inl .na) Na) (.inr .stI) St := ⟨_, rfl⟩
  have hT0 : TempsEmpty V0 := by
    constructor <;> simp [hV0, Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg,
      hT.tmp]
  have hS0 : TermOK (V0 (.inr .stI)) := by simpa [hV0] using tSt
  have hstart : r2V V0 q wI wT M yr D mus nas prev 0 = V := by
    funext x
    rcases x with d | w
    · cases d <;> simp [r2V, hV0, Function.update_apply, hdat, hmu, hna]
    · cases w <;> simp [r2V, hV0, Function.update_apply, hst, hmuO, hnaO, hstO]
  have hL := runs_r2_loop G scm srh sca hB hwI hwT V0 hT0 hS0 hyr hpr hmus hnas hF (D := D)
  rw [hstart] at hL
  have d1 : yr.drop M = [] := List.drop_eq_nil_of_le (by omega)
  have d2 : mus.drop M = [] := List.drop_eq_nil_of_le (by omega)
  have d2' : (mus.map toP).drop M = [] := List.drop_eq_nil_of_le (by simp; omega)
  have d3 : nas.drop M = [] := List.drop_eq_nil_of_le (by omega)
  have d3' : (nas.map toP).drop M = [] := List.drop_eq_nil_of_le (by simp; omega)
  have d4 : prev.drop M = [] := List.drop_eq_nil_of_le (by omega)
  have t1 : mus.take M = mus := List.take_of_length_le (by omega)
  have t1' : (mus.map toP).take M = mus.map toP := List.take_of_length_le (by simp; omega)
  have t2 : nas.take M = nas := List.take_of_length_le (by omega)
  have t2' : (nas.map toP).take M = nas.map toP := List.take_of_length_le (by simp; omega)
  have t3 : (stepRowI q M mus nas yr prev).take M = stepRowI q M mus nas yr prev :=
    List.take_of_length_le (by simp [stepRowI])
  have t4 : (bRowI q M mus yr).take M = bRowI q M mus yr :=
    List.take_of_length_le (by simp [bRowI])
  unfold r2
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq hL
    (WP.W9comp.runs_seq (runs_drP1 lS (x := .inr .stO) (y := .inr .stI) (by decide) (by decide)
      (by decide) base _ hwI (stepRowI q M mus nas yr prev).reverse (rx := []) ?h1 TermOK.nil ?h2)
    (WP.W9comp.runs_seq (runs_drP1 lS (x := .inr .muO) (y := .inl .mu) (by decide) (by decide)
      (by decide) base _ hwT (mus.map toP).reverse (rx := []) ?h3 TermOK.nil ?h4)
    (runs_drP1 lS (x := .inr .naO) (y := .inl .na) (by decide) (by decide)
      (by decide) base _ hwT (nas.map toP).reverse (rx := []) ?h5 TermOK.nil ?h6)))) ?he)
    (fun _ _ => trivial) ?hc
  case h1 => simp [r2V, hV0, Function.update_apply, t3, hstO]
  case h2 => simp [r2V, hV0, Function.update_apply, hT.tmp]
  case h3 => simp [r2V, hV0, Function.update_apply, t1', t1, hmuO]
  case h4 => simp [r2V, hV0, Function.update_apply, hT.tmp]
  case h5 => simp [r2V, hV0, Function.update_apply, t2', t2, hnaO]
  case h6 => simp [r2V, hV0, Function.update_apply, hT.tmp]
  case he =>
    congr 1
    funext x
    rcases x with d | w
    · cases d <;> simp [r2V, hV0, Function.update_apply, d1, d2, d2', d3, d3', hmu, hna]
    · cases w <;> simp [r2V, hV0, Function.update_apply, d4, t3, t4, hmuO, hnaO, hstO]
  case hc =>
    simp only [r2Cost, loopCost_const, List.length_reverse, List.length_map, hmus, hnas]
    rw [show (stepRowI q M mus nas yr prev).length = M by simp [stepRowI]]
    apply le_of_eq; ring

end RowsProofs

section Row1

variable {Ecm Erh Eca Rcm Rrh Rca : Type} [Fintype Ecm] [DecidableEq Ecm] [Fintype Erh]
  [DecidableEq Erh] [Fintype Eca] [DecidableEq Eca]
variable (G : LeafProgs Ecm Erh Eca Rcm Rrh Rca)

/-- Prefix row `0`: the element loop (driven by the `μ` row), then the rewinds of the state row and
the `μ` row. -/
def r1 : PS Ecm Erh Eca Rcm Rrh Rca :=
  .seq (whileP lS (.inl .mu) (e1 G)) (.seq (drP lS (.inr .stO) (.inr .stI))
    (drP lS (.inr .muO) (.inl .mu)))

/-- State of prefix row `0` after `s` columns. -/
def r1V (V0 : SwD ⊕ SwW → List Sym) (q wI wT M : ℕ) (yr : List CInt) (D : List Sym)
    (mus : List ℤ) (s : ℕ) : SwD ⊕ SwW → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update V0
    (.inl .dat) (rec1s wI (yr.drop s) ++ D))
    (.inl .mu) (rec1s wT ((mus.map toP).drop s) ++ V0 (.inl .mu)))
    (.inr .muO) (rec1s wT ((mus.map toP).take s).reverse ++ V0 (.inr .muO)))
    (.inr .stO) (rec1s wI ((bRowI q M mus yr).take s).reverse ++ V0 (.inr .stO)))
    (.inr .bS) (rec1s wI ((bRowI q M mus yr).take s).reverse ++ V0 (.inr .bS))

/-- Width premises of prefix row `0`. -/
structure Row1Fits (q wI wT M : ℕ) (mus : List ℤ) (yr : List CInt) : Prop where
  y : ∀ s, s < M → Fits2 wI (yr.getD s 0)
  mu : ∀ s, s < M → FitsTwos wT (mus.getD s 0)
  b : ∀ s, s < M → Fits2 wI (bI q (mus.getD s 0) (yr.getD s 0))

theorem runs_r1_step {Ccm Crh : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V0 : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V0)
    {yr : List CInt} {D : List Sym} {mus : List ℤ}
    (hyr : yr.length = M) (hmus : mus.length = M)
    (hF : Row1Fits q wI wT M mus yr) (s : ℕ) (hs : s < M) :
    Runs (e1 G) (mk base (r1V V0 q wI wT M yr D mus s))
      (mk base (r1V V0 q wI wT M yr D mus (s + 1))) (fun _ => True)
      (e1Cost Ccm Crh wI wT q) := by
  have hy : s < yr.length := by omega
  have hm : s < (mus.map toP).length := by simp; omega
  have hb : s < (bRowI q M mus yr).length := by simp [bRowI]; omega
  have gy : yr.getD s 0 = yr[s] := getD_eq_getElem' _ _ _ hy
  have gm : mus.getD s 0 = mus[s]'(by omega) := getD_eq_getElem' _ _ _ (by omega)
  have hT' : TempsEmpty (r1V V0 q wI wT M yr D mus s) := by
    constructor <;> simp [r1V, Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg,
      hT.tmp]
  have h := runs_e1 G scm srh hB hwI hwT (r1V V0 q wI wT M yr D mus s) hT'
    (y := yr[s]) (mu := mus[s]'(by omega))
    (D := rec1s wI (yr.drop (s + 1)) ++ D)
    (Mu := rec1s wT ((mus.map toP).drop (s + 1)) ++ V0 (.inl .mu))
    (by simp [r1V, Function.update_apply, rec1s_drop_cons wI yr s hy])
    (by simp [r1V, Function.update_apply, rec1s_drop_cons wT (mus.map toP) s hm, toP])
    (gy ▸ hF.y s hs) (gm ▸ hF.mu s hs) (by rw [← gm, ← gy]; exact hF.b s hs)
  refine WP.W9comp.runs_congr h ?_
  congr 1
  have e1 := rec1s_take_succ_rev wT (mus.map toP) s hm
  have e4 := rec1s_take_succ_rev wI (bRowI q M mus yr) s hb
  rw [bRowI_getElem q M mus yr s hs, gy, gm] at e4
  simp only [List.getElem_map, toP] at e1
  funext x
  rcases x with d | w
  · cases d <;> simp [e1Post, r1V, Function.update_apply, e1]
  · cases w <;> simp [e1Post, r1V, Function.update_apply, e1, e4]

theorem runs_r1_loop {Ccm Crh : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V0 : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V0)
    (hMu : TermOK (V0 (.inl .mu)))
    {yr : List CInt} {D : List Sym} {mus : List ℤ}
    (hyr : yr.length = M) (hmus : mus.length = M) (hF : Row1Fits q wI wT M mus yr) :
    Runs (whileP lS (.inl .mu) (e1 G)) (mk base (r1V V0 q wI wT M yr D mus 0))
      (mk base (r1V V0 q wI wT M yr D mus M)) (fun _ => True)
      (1 + loopCost (fun _ => e1Cost Ccm Crh wI wT q + 1) M) := by
  have htop : ∀ n, n ≤ M → optIsBit ((mk base (r1V V0 q wI wT M yr D mus (M - n)))
      (loc (.inl .mu))).head? = decide (0 < n) := by
    intro n hn
    have e : (mk base (r1V V0 q wI wT M yr D mus (M - n))) (loc (.inl .mu)) =
        rec1s wT ((mus.map toP).drop (M - n)) ++ V0 (.inl .mu) := by
      simp [r1V, Function.update_apply]
    rw [e, optIsBit_rec1s wT hwT _ _ hMu, List.length_drop, List.length_map, hmus,
      Nat.sub_sub_self hn]
  have hstep : ∀ n, n < M →
      Runs (e1 G) (mk base (r1V V0 q wI wT M yr D mus (M - (n + 1))))
        (mk base (r1V V0 q wI wT M yr D mus (M - n))) (fun _ => True)
        (e1Cost Ccm Crh wI wT q) := by
    intro n hn
    have e : M - n = M - (n + 1) + 1 := by omega
    rw [e]
    exact runs_r1_step G scm srh hB hwI hwT V0 hT hyr hmus hF (M - (n + 1)) (by omega)
  have h := runs_whileP lS (.inl .mu) (e1 G)
    (fun n => mk base (r1V V0 q wI wT M yr D mus (M - n))) M
    (fun _ => e1Cost Ccm Crh wI wT q) htop hstep
  simp only [Nat.sub_self, Nat.sub_zero] at h
  exact h

/-- Cost of prefix row `0` (also the closure row). -/
def r1Cost (Ccm Crh wI wT q M : ℕ) : ℕ :=
  M * (e1Cost Ccm Crh wI wT q + 2 + (12 * wI + 12) + (12 * wT + 12)) + 6

/-- **Prefix row `0`**: consumes the data row; the state row (pushed on `stI`) is the row of `b`
values, which are also pushed (reversed) on `bS`; the `μ` row is restored. -/
theorem runs_r1 {Ccm Crh : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V)
    {yr : List CInt} {D Mu : List Sym} {mus : List ℤ}
    (hyr : yr.length = M) (hmus : mus.length = M) (hF : Row1Fits q wI wT M mus yr)
    (hdat : V (.inl .dat) = rec1s wI yr ++ D)
    (hmu : V (.inl .mu) = rec1s wT (mus.map toP) ++ Mu) (tMu : TermOK Mu)
    (hmuO : V (.inr .muO) = []) (hstO : V (.inr .stO) = []) :
    Runs (r1 G) (mk base V)
      (mk base (Function.update (Function.update (Function.update V (.inl .dat) D)
        (.inr .stI) (rec1s wI (bRowI q M mus yr) ++ V (.inr .stI)))
        (.inr .bS) (rec1s wI (bRowI q M mus yr).reverse ++ V (.inr .bS))))
      (fun _ => True) (r1Cost Ccm Crh wI wT q M) := by
  obtain ⟨V0, hV0⟩ : ∃ V0 : SwD ⊕ SwW → List Sym, V0 = Function.update V (.inl .mu) Mu :=
    ⟨_, rfl⟩
  have hT0 : TempsEmpty V0 := by
    constructor <;> simp [hV0, Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg,
      hT.tmp]
  have hM0 : TermOK (V0 (.inl .mu)) := by simpa [hV0] using tMu
  have hstart : r1V V0 q wI wT M yr D mus 0 = V := by
    funext x
    rcases x with d | w
    · cases d <;> simp [r1V, hV0, Function.update_apply, hdat, hmu]
    · cases w <;> simp [r1V, hV0, Function.update_apply, hmuO, hstO]
  have hL := runs_r1_loop G scm srh hB hwI hwT V0 hT0 hM0 hyr hmus hF (D := D)
  rw [hstart] at hL
  have d1 : yr.drop M = [] := List.drop_eq_nil_of_le (by omega)
  have d2 : mus.drop M = [] := List.drop_eq_nil_of_le (by omega)
  have d2' : (mus.map toP).drop M = [] := List.drop_eq_nil_of_le (by simp; omega)
  have t1 : mus.take M = mus := List.take_of_length_le (by omega)
  have t1' : (mus.map toP).take M = mus.map toP := List.take_of_length_le (by simp; omega)
  have t4 : (bRowI q M mus yr).take M = bRowI q M mus yr :=
    List.take_of_length_le (by simp [bRowI])
  unfold r1
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq hL
    (WP.W9comp.runs_seq (runs_drP1 lS (x := .inr .stO) (y := .inr .stI) (by decide) (by decide)
      (by decide) base _ hwI (bRowI q M mus yr).reverse (rx := []) ?h1 TermOK.nil ?h2)
    (runs_drP1 lS (x := .inr .muO) (y := .inl .mu) (by decide) (by decide)
      (by decide) base _ hwT (mus.map toP).reverse (rx := []) ?h3 TermOK.nil ?h4))) ?he)
    (fun _ _ => trivial) ?hc
  case h1 => simp [r1V, hV0, Function.update_apply, t4, hstO]
  case h2 => simp [r1V, hV0, Function.update_apply, hT.tmp]
  case h3 => simp [r1V, hV0, Function.update_apply, t1', t1, hmuO]
  case h4 => simp [r1V, hV0, Function.update_apply, hT.tmp]
  case he =>
    congr 1
    funext x
    rcases x with d | w
    · cases d <;> simp [r1V, hV0, Function.update_apply, d1, d2, d2', hmu]
    · cases w <;> simp [r1V, hV0, Function.update_apply, t4, hmuO, hstO]
  case hc =>
    simp only [r1Cost, loopCost_const, List.length_reverse, List.length_map, hmus]
    rw [show (bRowI q M mus yr).length = M by simp [bRowI]]
    apply le_of_eq; ring

end Row1

section Row3

variable {Ecm Erh Eca Rcm Rrh Rca : Type} [Fintype Ecm] [DecidableEq Ecm] [Fintype Erh]
  [DecidableEq Erh] [Fintype Eca] [DecidableEq Eca]
variable (G : LeafProgs Ecm Erh Eca Rcm Rrh Rca)

/-- The closure row: the element loop (driven by the state row), then the rewinds of the state row
(now the closure row) and the `γ` row. -/
def r3 : PS Ecm Erh Eca Rcm Rrh Rca :=
  .seq (whileP lS (.inr .stI) (e3 G)) (.seq (drP lS (.inr .stO) (.inr .stI))
    (drP lS (.inr .gmO) (.inl .gm)))

/-- State of the closure row after `s` columns. -/
def r3V (V0 : SwD ⊕ SwW → List Sym) (q wI wT M : ℕ) (gms : List ℤ) (prev : List CInt) (s : ℕ) :
    SwD ⊕ SwW → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update V0
    (.inr .stI) (rec1s wI (prev.drop s) ++ V0 (.inr .stI)))
    (.inl .gm) (rec1s wT ((gms.map toP).drop s) ++ V0 (.inl .gm)))
    (.inr .gmO) (rec1s wT ((gms.map toP).take s).reverse ++ V0 (.inr .gmO)))
    (.inr .cS) (rec1s wI ((closRow q M gms prev).take s).reverse ++ V0 (.inr .cS)))
    (.inr .stO) (rec1s wI ((closRow q M gms prev).take s).reverse ++ V0 (.inr .stO))

/-- Width premises of the closure row. -/
structure Row3Fits (q wI wT M : ℕ) (gms : List ℤ) (prev : List CInt) : Prop where
  gm : ∀ s, s < M → FitsTwos wT (gms.getD s 0)
  p : ∀ s, s < M → Fits2 wI (prev.getD s 0)
  c : ∀ s, s < M → Fits2 wI (rI q (gms.getD s 0) (prev.getD s 0))

theorem closRow_getElem (q M : ℕ) (gms : List ℤ) (p : List CInt) (s : ℕ) (hs : s < M) :
    (closRow q M gms p)[s]'(by simp [closRow]; exact hs) = rI q (gms.getD s 0) (p.getD s 0) := by
  simp [closRow]

theorem runs_r3_step {Ccm Crh : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V0 : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V0)
    {prev : List CInt} {gms : List ℤ}
    (hpr : prev.length = M) (hgms : gms.length = M)
    (hF : Row3Fits q wI wT M gms prev) (s : ℕ) (hs : s < M) :
    Runs (e3 G) (mk base (r3V V0 q wI wT M gms prev s))
      (mk base (r3V V0 q wI wT M gms prev (s + 1))) (fun _ => True)
      (e1Cost Ccm Crh wI wT q) := by
  have hp : s < prev.length := by omega
  have hg : s < (gms.map toP).length := by simp; omega
  have hc : s < (closRow q M gms prev).length := by simp [closRow]; omega
  have gp : prev.getD s 0 = prev[s] := getD_eq_getElem' _ _ _ hp
  have gg : gms.getD s 0 = gms[s]'(by omega) := getD_eq_getElem' _ _ _ (by omega)
  have hT' : TempsEmpty (r3V V0 q wI wT M gms prev s) := by
    constructor <;> simp [r3V, Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg,
      hT.tmp]
  have h := runs_e3 G scm srh hB hwI hwT (r3V V0 q wI wT M gms prev s) hT'
    (p := prev[s]) (gm := gms[s]'(by omega))
    (St := rec1s wI (prev.drop (s + 1)) ++ V0 (.inr .stI))
    (Gm := rec1s wT ((gms.map toP).drop (s + 1)) ++ V0 (.inl .gm))
    (by simp [r3V, Function.update_apply, rec1s_drop_cons wI prev s hp])
    (by simp [r3V, Function.update_apply, rec1s_drop_cons wT (gms.map toP) s hg, toP])
    (gp ▸ hF.p s hs) (gg ▸ hF.gm s hs) (by rw [← gg, ← gp]; exact hF.c s hs)
  refine WP.W9comp.runs_congr h ?_
  congr 1
  have e1 := rec1s_take_succ_rev wT (gms.map toP) s hg
  have e4 := rec1s_take_succ_rev wI (closRow q M gms prev) s hc
  rw [closRow_getElem q M gms prev s hs, gp, gg] at e4
  simp only [List.getElem_map, toP] at e1
  funext x
  rcases x with d | w
  · cases d <;> simp [e3Post, r3V, Function.update_apply, e1]
  · cases w <;> simp [e3Post, r3V, Function.update_apply, e1, e4]

theorem runs_r3_loop {Ccm Crh : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V0 : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V0)
    (hSt : TermOK (V0 (.inr .stI)))
    {prev : List CInt} {gms : List ℤ}
    (hpr : prev.length = M) (hgms : gms.length = M) (hF : Row3Fits q wI wT M gms prev) :
    Runs (whileP lS (.inr .stI) (e3 G)) (mk base (r3V V0 q wI wT M gms prev 0))
      (mk base (r3V V0 q wI wT M gms prev M)) (fun _ => True)
      (1 + loopCost (fun _ => e1Cost Ccm Crh wI wT q + 1) M) := by
  have htop : ∀ n, n ≤ M → optIsBit ((mk base (r3V V0 q wI wT M gms prev (M - n)))
      (loc (.inr .stI))).head? = decide (0 < n) := by
    intro n hn
    have e : (mk base (r3V V0 q wI wT M gms prev (M - n))) (loc (.inr .stI)) =
        rec1s wI (prev.drop (M - n)) ++ V0 (.inr .stI) := by
      simp [r3V, Function.update_apply]
    rw [e, optIsBit_rec1s wI hwI _ _ hSt, List.length_drop, hpr, Nat.sub_sub_self hn]
  have hstep : ∀ n, n < M →
      Runs (e3 G) (mk base (r3V V0 q wI wT M gms prev (M - (n + 1))))
        (mk base (r3V V0 q wI wT M gms prev (M - n))) (fun _ => True)
        (e1Cost Ccm Crh wI wT q) := by
    intro n hn
    have e : M - n = M - (n + 1) + 1 := by omega
    rw [e]
    exact runs_r3_step G scm srh hB hwI hwT V0 hT hpr hgms hF (M - (n + 1)) (by omega)
  have h := runs_whileP lS (.inr .stI) (e3 G)
    (fun n => mk base (r3V V0 q wI wT M gms prev (M - n))) M
    (fun _ => e1Cost Ccm Crh wI wT q) htop hstep
  simp only [Nat.sub_self, Nat.sub_zero] at h
  exact h

/-- **The closure row**: replaces the state row `p` by the closure row `Quant_q(γ p)`, pushed also
(reversed) on `cS`; the `γ` row is restored. -/
theorem runs_r3 {Ccm Crh : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V)
    {prev : List CInt} {Gm St : List Sym} {gms : List ℤ}
    (hpr : prev.length = M) (hgms : gms.length = M) (hF : Row3Fits q wI wT M gms prev)
    (hst : V (.inr .stI) = rec1s wI prev ++ St) (tSt : TermOK St)
    (hgm : V (.inl .gm) = rec1s wT (gms.map toP) ++ Gm)
    (hgmO : V (.inr .gmO) = []) (hstO : V (.inr .stO) = []) :
    Runs (r3 G) (mk base V)
      (mk base (Function.update (Function.update V
        (.inr .stI) (rec1s wI (closRow q M gms prev) ++ St))
        (.inr .cS) (rec1s wI (closRow q M gms prev).reverse ++ V (.inr .cS))))
      (fun _ => True) (r1Cost Ccm Crh wI wT q M) := by
  obtain ⟨V0, hV0⟩ : ∃ V0 : SwD ⊕ SwW → List Sym,
      V0 = Function.update (Function.update V (.inl .gm) Gm) (.inr .stI) St := ⟨_, rfl⟩
  have hT0 : TempsEmpty V0 := by
    constructor <;> simp [hV0, Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg,
      hT.tmp]
  have hS0 : TermOK (V0 (.inr .stI)) := by simpa [hV0] using tSt
  have hstart : r3V V0 q wI wT M gms prev 0 = V := by
    funext x
    rcases x with d | w
    · cases d <;> simp [r3V, hV0, Function.update_apply, hgm]
    · cases w <;> simp [r3V, hV0, Function.update_apply, hst, hgmO, hstO]
  have hL := runs_r3_loop G scm srh hB hwI hwT V0 hT0 hS0 hpr hgms hF
  rw [hstart] at hL
  have d2 : gms.drop M = [] := List.drop_eq_nil_of_le (by omega)
  have d2' : (gms.map toP).drop M = [] := List.drop_eq_nil_of_le (by simp; omega)
  have d4 : prev.drop M = [] := List.drop_eq_nil_of_le (by omega)
  have t1 : gms.take M = gms := List.take_of_length_le (by omega)
  have t1' : (gms.map toP).take M = gms.map toP := List.take_of_length_le (by simp; omega)
  have t4 : (closRow q M gms prev).take M = closRow q M gms prev :=
    List.take_of_length_le (by simp [closRow])
  unfold r3
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq hL
    (WP.W9comp.runs_seq (runs_drP1 lS (x := .inr .stO) (y := .inr .stI) (by decide) (by decide)
      (by decide) base _ hwI (closRow q M gms prev).reverse (rx := []) ?h1 TermOK.nil ?h2)
    (runs_drP1 lS (x := .inr .gmO) (y := .inl .gm) (by decide) (by decide)
      (by decide) base _ hwT (gms.map toP).reverse (rx := []) ?h3 TermOK.nil ?h4))) ?he)
    (fun _ _ => trivial) ?hc
  case h1 => simp [r3V, hV0, Function.update_apply, t4, hstO]
  case h2 => simp [r3V, hV0, Function.update_apply, hT.tmp]
  case h3 => simp [r3V, hV0, Function.update_apply, t1', t1, hgmO]
  case h4 => simp [r3V, hV0, Function.update_apply, hT.tmp]
  case he =>
    congr 1
    funext x
    rcases x with d | w
    · cases d <;> simp [r3V, hV0, Function.update_apply, d2, d2', hgm]
    · cases w <;> simp [r3V, hV0, Function.update_apply, d4, t4, hgmO, hstO]
  case hc =>
    simp only [r1Cost, loopCost_const, List.length_reverse, List.length_map, hgms]
    rw [show (closRow q M gms prev).length = M by simp [closRow]]
    apply le_of_eq; ring

end Row3

section Row4

variable {Ecm Erh Eca Rcm Rrh Rca : Type} [Fintype Ecm] [DecidableEq Ecm] [Fintype Erh]
  [DecidableEq Erh] [Fintype Eca] [DecidableEq Eca]
variable (G : LeafProgs Ecm Erh Eca Rcm Rrh Rca)

/-- A second-pass row: the element loop (driven by the state row; `b` from the stream `bS2`), then
the rewinds of the state row and the `-â` row. -/
def r4 : PS Ecm Erh Eca Rcm Rrh Rca :=
  .seq (whileP lS (.inr .stI) (e4 G)) (.seq (drP lS (.inr .stO) (.inr .stI))
    (drP lS (.inr .naO) (.inl .na)))

/-- State of a second-pass row after `s` columns. -/
def r4V (V0 : SwD ⊕ SwW → List Sym) (q wI wT M : ℕ) (nas : List ℤ) (br : List CInt)
    (B2 : List Sym) (prev : List CInt) (s : ℕ) : SwD ⊕ SwW → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update V0
    (.inr .bS2) (rec1s wI (br.drop s) ++ B2))
    (.inr .stI) (rec1s wI (prev.drop s) ++ V0 (.inr .stI)))
    (.inl .na) (rec1s wT ((nas.map toP).drop s) ++ V0 (.inl .na)))
    (.inr .naO) (rec1s wT ((nas.map toP).take s).reverse ++ V0 (.inr .naO)))
    (.inr .oS) (rec1s wI ((stepRowB q M nas br prev).take s).reverse ++ V0 (.inr .oS)))
    (.inr .stO) (rec1s wI ((stepRowB q M nas br prev).take s).reverse ++ V0 (.inr .stO))

/-- Width premises of a second-pass row. -/
structure Row4Fits (q wI wT M : ℕ) (nas : List ℤ) (br prev : List CInt) : Prop where
  b : ∀ s, s < M → Fits2 wI (br.getD s 0)
  na : ∀ s, s < M → FitsTwos wT (nas.getD s 0)
  p : ∀ s, s < M → Fits2 wI (prev.getD s 0)
  z : ∀ s, s < M → Fits2 wI (stepI q (nas.getD s 0) (br.getD s 0) (prev.getD s 0))

theorem stepRowB_getElem (q M : ℕ) (nas : List ℤ) (br prev : List CInt) (s : ℕ) (hs : s < M) :
    (stepRowB q M nas br prev)[s]'(by simp [stepRowB]; exact hs) =
      stepI q (nas.getD s 0) (br.getD s 0) (prev.getD s 0) := by
  simp [stepRowB]

theorem runs_r4_step {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V0 : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V0)
    {br prev : List CInt} {B2 : List Sym} {nas : List ℤ}
    (hbr : br.length = M) (hpr : prev.length = M) (hnas : nas.length = M)
    (hF : Row4Fits q wI wT M nas br prev) (s : ℕ) (hs : s < M) :
    Runs (e4 G) (mk base (r4V V0 q wI wT M nas br B2 prev s))
      (mk base (r4V V0 q wI wT M nas br B2 prev (s + 1))) (fun _ => True)
      (e4Cost Ccm Crh Cca wI wT q) := by
  have hb : s < br.length := by omega
  have hp : s < prev.length := by omega
  have hn : s < (nas.map toP).length := by simp; omega
  have hz : s < (stepRowB q M nas br prev).length := by simp [stepRowB]; omega
  have gb : br.getD s 0 = br[s] := getD_eq_getElem' _ _ _ hb
  have gp : prev.getD s 0 = prev[s] := getD_eq_getElem' _ _ _ hp
  have gn : nas.getD s 0 = nas[s]'(by omega) := getD_eq_getElem' _ _ _ (by omega)
  have hT' : TempsEmpty (r4V V0 q wI wT M nas br B2 prev s) := by
    constructor <;> simp [r4V, Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg,
      hT.tmp]
  have h := runs_e4 G scm srh sca hB hwI hwT (r4V V0 q wI wT M nas br B2 prev s) hT'
    (b := br[s]) (p := prev[s]) (na := nas[s]'(by omega))
    (B2 := rec1s wI (br.drop (s + 1)) ++ B2)
    (St := rec1s wI (prev.drop (s + 1)) ++ V0 (.inr .stI))
    (Na := rec1s wT ((nas.map toP).drop (s + 1)) ++ V0 (.inl .na))
    (by simp [r4V, Function.update_apply, rec1s_drop_cons wI br s hb])
    (by simp [r4V, Function.update_apply, rec1s_drop_cons wI prev s hp])
    (by simp [r4V, Function.update_apply, rec1s_drop_cons wT (nas.map toP) s hn, toP])
    (gb ▸ hF.b s hs) (gn ▸ hF.na s hs) (gp ▸ hF.p s hs)
    (by rw [← gn, ← gb, ← gp]; exact hF.z s hs)
  refine WP.W9comp.runs_congr h ?_
  congr 1
  have e2 := rec1s_take_succ_rev wT (nas.map toP) s hn
  have e3 := rec1s_take_succ_rev wI (stepRowB q M nas br prev) s hz
  rw [stepRowB_getElem q M nas br prev s hs, gb, gp, gn] at e3
  simp only [List.getElem_map, toP] at e2
  funext x
  rcases x with d | w
  · cases d <;> simp [e4Post, r4V, Function.update_apply, e2]
  · cases w <;> simp [e4Post, r4V, Function.update_apply, e2, e3]

theorem runs_r4_loop {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V0 : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V0)
    (hSt : TermOK (V0 (.inr .stI)))
    {br prev : List CInt} {B2 : List Sym} {nas : List ℤ}
    (hbr : br.length = M) (hpr : prev.length = M) (hnas : nas.length = M)
    (hF : Row4Fits q wI wT M nas br prev) :
    Runs (whileP lS (.inr .stI) (e4 G)) (mk base (r4V V0 q wI wT M nas br B2 prev 0))
      (mk base (r4V V0 q wI wT M nas br B2 prev M)) (fun _ => True)
      (1 + loopCost (fun _ => e4Cost Ccm Crh Cca wI wT q + 1) M) := by
  have htop : ∀ n, n ≤ M → optIsBit ((mk base (r4V V0 q wI wT M nas br B2 prev (M - n)))
      (loc (.inr .stI))).head? = decide (0 < n) := by
    intro n hn
    have e : (mk base (r4V V0 q wI wT M nas br B2 prev (M - n))) (loc (.inr .stI)) =
        rec1s wI (prev.drop (M - n)) ++ V0 (.inr .stI) := by
      simp [r4V, Function.update_apply]
    rw [e, optIsBit_rec1s wI hwI _ _ hSt, List.length_drop, hpr, Nat.sub_sub_self hn]
  have hstep : ∀ n, n < M →
      Runs (e4 G) (mk base (r4V V0 q wI wT M nas br B2 prev (M - (n + 1))))
        (mk base (r4V V0 q wI wT M nas br B2 prev (M - n))) (fun _ => True)
        (e4Cost Ccm Crh Cca wI wT q) := by
    intro n hn
    have e : M - n = M - (n + 1) + 1 := by omega
    rw [e]
    exact runs_r4_step G scm srh sca hB hwI hwT V0 hT hbr hpr hnas hF (M - (n + 1)) (by omega)
  have h := runs_whileP lS (.inr .stI) (e4 G)
    (fun n => mk base (r4V V0 q wI wT M nas br B2 prev (M - n))) M
    (fun _ => e4Cost Ccm Crh Cca wI wT q) htop hstep
  simp only [Nat.sub_self, Nat.sub_zero] at h
  exact h

/-- Cost of a second-pass row. -/
def r4Cost (Ccm Crh Cca wI wT q M : ℕ) : ℕ :=
  M * (e4Cost Ccm Crh Cca wI wT q + 2 + (12 * wI + 12) + (12 * wT + 12)) + 6

/-- **A second-pass row**: consumes the row's `b` values from `bS2`, replaces the state row by the
new states, which are also pushed (reversed) on `oS`; the `-â` row is restored. -/
theorem runs_r4 {Ccm Crh Cca : ℕ} (scm : CMSpec Ecm Rcm Ccm G.Pcm)
    (srh : RHSpec Erh Rrh Crh G.Prh) (sca : CASpec Eca Rca Cca G.Pca)
    {base : KS (LEs Ecm Erh Eca) → List Sym} {q wI wT M : ℕ} (hB : BaseOK base wI wT q)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (V : SwD ⊕ SwW → List Sym) (hT : TempsEmpty V)
    {br prev : List CInt} {B2 Na St : List Sym} {nas : List ℤ}
    (hbr : br.length = M) (hpr : prev.length = M) (hnas : nas.length = M)
    (hF : Row4Fits q wI wT M nas br prev)
    (hb2 : V (.inr .bS2) = rec1s wI br ++ B2)
    (hst : V (.inr .stI) = rec1s wI prev ++ St) (tSt : TermOK St)
    (hna : V (.inl .na) = rec1s wT (nas.map toP) ++ Na)
    (hnaO : V (.inr .naO) = []) (hstO : V (.inr .stO) = []) :
    Runs (r4 G) (mk base V)
      (mk base (Function.update (Function.update (Function.update V (.inr .bS2) B2)
        (.inr .stI) (rec1s wI (stepRowB q M nas br prev) ++ St))
        (.inr .oS) (rec1s wI (stepRowB q M nas br prev).reverse ++ V (.inr .oS))))
      (fun _ => True) (r4Cost Ccm Crh Cca wI wT q M) := by
  obtain ⟨V0, hV0⟩ : ∃ V0 : SwD ⊕ SwW → List Sym,
      V0 = Function.update (Function.update V (.inl .na) Na) (.inr .stI) St := ⟨_, rfl⟩
  have hT0 : TempsEmpty V0 := by
    constructor <;> simp [hV0, Function.update_apply, hT.xa, hT.xb, hT.xc, hT.xd, hT.xf, hT.xg,
      hT.tmp]
  have hS0 : TermOK (V0 (.inr .stI)) := by simpa [hV0] using tSt
  have hstart : r4V V0 q wI wT M nas br B2 prev 0 = V := by
    funext x
    rcases x with d | w
    · cases d <;> simp [r4V, hV0, Function.update_apply, hna]
    · cases w <;> simp [r4V, hV0, Function.update_apply, hb2, hst, hnaO, hstO]
  have hL := runs_r4_loop G scm srh sca hB hwI hwT V0 hT0 hS0 hbr hpr hnas hF (B2 := B2)
  rw [hstart] at hL
  have d1 : br.drop M = [] := List.drop_eq_nil_of_le (by omega)
  have d3 : nas.drop M = [] := List.drop_eq_nil_of_le (by omega)
  have d3' : (nas.map toP).drop M = [] := List.drop_eq_nil_of_le (by simp; omega)
  have d4 : prev.drop M = [] := List.drop_eq_nil_of_le (by omega)
  have t2 : nas.take M = nas := List.take_of_length_le (by omega)
  have t2' : (nas.map toP).take M = nas.map toP := List.take_of_length_le (by simp; omega)
  have t3 : (stepRowB q M nas br prev).take M = stepRowB q M nas br prev :=
    List.take_of_length_le (by simp [stepRowB])
  unfold r4
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq hL
    (WP.W9comp.runs_seq (runs_drP1 lS (x := .inr .stO) (y := .inr .stI) (by decide) (by decide)
      (by decide) base _ hwI (stepRowB q M nas br prev).reverse (rx := []) ?h1 TermOK.nil ?h2)
    (runs_drP1 lS (x := .inr .naO) (y := .inl .na) (by decide) (by decide)
      (by decide) base _ hwT (nas.map toP).reverse (rx := []) ?h3 TermOK.nil ?h4))) ?he)
    (fun _ _ => trivial) ?hc
  case h1 => simp [r4V, hV0, Function.update_apply, t3, hstO]
  case h2 => simp [r4V, hV0, Function.update_apply, hT.tmp]
  case h3 => simp [r4V, hV0, Function.update_apply, t2', t2, hnaO]
  case h4 => simp [r4V, hV0, Function.update_apply, hT.tmp]
  case he =>
    congr 1
    funext x
    rcases x with d | w
    · cases d <;> simp [r4V, hV0, Function.update_apply, d3, d3', hna]
    · cases w <;> simp [r4V, hV0, Function.update_apply, d1, d4, t3, hnaO, hstO]
  case hc =>
    simp only [r4Cost, loopCost_const, List.length_reverse, List.length_map, hnas]
    rw [show (stepRowB q M nas br prev).length = M by simp [stepRowB]]
    apply le_of_eq; ring

end Row4


end SubNLogN.Machine.Bridge.SolveAux
