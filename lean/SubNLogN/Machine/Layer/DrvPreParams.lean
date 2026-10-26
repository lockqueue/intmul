/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreParamsCost
import SubNLogN.Machine.Layer.DrvPreParamsOut

/-!
# Layer driver: the pre-phase parameters (`Machine/Layer/DrvPreParams.lean`)

`drvPreParams_holds : DrvPreParamsStmt` (`Machine/Layer/DrvParamsDefs.lean`). The kernel `preProg`
works on the stacks `KLoc (Fin 12) (Fin 64)` with the registers `DrvArith.Reg2` and no assumption
on the initial scratch content (every private stack gets a `mark` floor first and is restored):
* loads: the header fields `P, d, D, S, K, ρ + 1` onto floored work stacks (`copyFieldN`), then
  `ρ` (`decL`) and `w_g = 3P + 3` (`wgN`);
* outputs, each pushed on top of the old content of `.inl 1 … .inl 11`: `w`, `w_g`, `Δ = P`, the
  phase-scan header `hdrSyms [S, K, ρ, D, 0, 0, w_g, w_g]`, `min q₀ D` (`q1N`), `w₀` (`w0N`), `K`,
  the rows flag (`rowsN`), `keep` (`keepN`), `n_pad` (`npadN`), `r`;
* drops of the work stacks.
The final stacks are identified with `drvPreParamsPost` by `preOut_eq`
(`Machine/Layer/DrvPreParamsOut.lean`); the cost `preCostP t` is bounded by
`C·(|hdr| + D·K + 1)^3` by `preCostP_le` (`Machine/Layer/DrvPreParamsCost.lean`). Fully proved, no
placeholders, no contract hypotheses: only proved kernels (W3, W6a, NatArith) are used.
-/

namespace SubNLogN.Machine.Layer.DrvPreParamsAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability SubNLogN.Machine
open SubNLogN.Machine.NatArith
open SubNLogN.Machine.Layer.DrvArith SubNLogN.Machine.Layer.DrvParamsAux
open SubNLogN.Machine.Layer.DrvParamsShared SubNLogN.Machine.Layer.DrvPreParamsW0Aux
open SubNLogN.Math.Networks (q0Of)

/-! ## 1. Stacks and stack maps -/

/-- The stacks of the kernel: header `.inl 0`, outputs `.inl 1 … .inl 11`, work stacks
`.inr 0 … .inr 7`, scratch `.inr 8 … .inr 63`. -/
abbrev K12 : Type := KLoc (Fin 12) (Fin 64)

abbrev sH : K12 := .inl 0
abbrev wP : K12 := .inr 0
abbrev wd : K12 := .inr 1
abbrev wD : K12 := .inr 2
abbrev wS : K12 := .inr 3
abbrev wK : K12 := .inr 4
abbrev wR1 : K12 := .inr 5
abbrev wR : K12 := .inr 6
abbrev wG : K12 := .inr 7
abbrev sPk : K12 := .inr 8
abbrev sTm : K12 := .inr 9

/-- A stack map: the entries of `ins`, then the scratch stacks `.inr (8 + k)`. -/
def smap {n : ℕ} (ins : List K12) (k : Fin n) : K12 :=
  if h : k.val < ins.length then ins[k.val] else .inr ⟨(8 + k.val) % 64, Nat.mod_lt _ (by omega)⟩

/-- The named entries of a stack map: outputs or work stacks (`.inr j`, `j < 8`). -/
def lowOK (x : K12) : Bool :=
  match x with
  | .inl _ => true
  | .inr j => decide (j.val < 8)

theorem smap_injective {n : ℕ} (ins : List K12) (hn : n ≤ 56) (hnd : ins.Nodup)
    (hins : ins.all lowOK = true) : Function.Injective (smap (n := n) ins) := by
  intro a b hab
  have ha' := a.isLt
  have hb' := b.isLt
  by_cases ha : a.val < ins.length
  · by_cases hb : b.val < ins.length
    · rw [smap, dif_pos ha, smap, dif_pos hb] at hab
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 hab)
    · rw [smap, dif_pos ha, smap, dif_neg hb] at hab
      have h1 := List.all_eq_true.1 hins _ (List.getElem_mem ha)
      rw [hab] at h1
      have h2 : (8 + b.val) % 64 < 8 := of_decide_eq_true h1
      omega
  · by_cases hb : b.val < ins.length
    · rw [smap, dif_neg ha, smap, dif_pos hb] at hab
      have h1 := List.all_eq_true.1 hins _ (List.getElem_mem hb)
      rw [← hab] at h1
      have h2 : (8 + a.val) % 64 < 8 := of_decide_eq_true h1
      omega
    · rw [smap, dif_neg ha, smap, dif_neg hb] at hab
      have h2 := congrArg Fin.val (Sum.inr_injective hab)
      have h3 : (8 + a.val) % 64 = (8 + b.val) % 64 := h2
      exact Fin.ext (by omega)

/-- `P` ↦ `w_g` onto the floored `wG`. -/
def stWg : Fin 12 → K12 := smap [wP, wG]
/-- `d, D` ↦ `min q₀ D` onto `.inl 5`. -/
def stQ1 : Fin 20 → K12 := smap [wd, wD, .inl 5]
/-- `D, S, K, ρ` ↦ `w₀` onto `.inl 6`. -/
def stW0 : Fin 16 → K12 := smap [wD, wS, wK, wR, .inl 6]
/-- `d, D` ↦ the rows flag onto `.inl 8`. -/
def stRw : Fin 20 → K12 := smap [wd, wD, .inl 8]
/-- `D, K, S` ↦ `keep` onto `.inl 9`. -/
def stKp : Fin 16 → K12 := smap [wD, wK, wS, .inl 9]
/-- `d, D, K, S` ↦ `n_pad` onto `.inl 10`. -/
def stNp : Fin 40 → K12 := smap [wd, wD, wK, wS, .inl 10]

theorem stWg_inj : Function.Injective stWg := smap_injective _ (by norm_num) (by decide) (by decide)
theorem stQ1_inj : Function.Injective stQ1 := smap_injective _ (by norm_num) (by decide) (by decide)
theorem stW0_inj : Function.Injective stW0 := smap_injective _ (by norm_num) (by decide) (by decide)
theorem stRw_inj : Function.Injective stRw := smap_injective _ (by norm_num) (by decide) (by decide)
theorem stKp_inj : Function.Injective stKp := smap_injective _ (by norm_num) (by decide) (by decide)
theorem stNp_inj : Function.Injective stNp := smap_injective _ (by norm_num) (by decide) (by decide)

/-! ## 2. The work stacks after the loads -/

/-- The eight floored work values `P, d, D, S, K, ρ + 1, ρ, w_g` above `X`. -/
def Fl (t : LayerRT) (X : K12 → List Sym) : K12 → List Sym :=
  fl (fl (fl (fl (fl (fl (fl (fl X wP t.P) wd t.d) wD t.D) wS t.S) wK t.K) wR1 (t.ρ + 1)) wR t.ρ)
    wG (t.P * 3 + 3)

theorem fl_upd_inl (X : K12 → List Sym) (j : Fin 64) (v : ℕ) (i : Fin 12) (Z : List Sym) :
    Function.update (fl X (.inr j) v) (.inl i) Z =
      fl (Function.update X (.inl i) Z) (.inr j) v := by
  unfold fl
  rw [Function.update_comm (Sum.inr_ne_inl : (Sum.inr j : K12) ≠ .inl i),
    Function.update_of_ne (Sum.inr_ne_inl : (Sum.inr j : K12) ≠ .inl i)]

theorem Fl_upd (t : LayerRT) (X : K12 → List Sym) (i : Fin 12) (Z : List Sym) :
    Function.update (Fl t X) (.inl i) Z = Fl t (Function.update X (.inl i) Z) := by
  simp only [Fl, fl_upd_inl]

theorem Fl_inl (t : LayerRT) (X : K12 → List Sym) (i : Fin 12) : Fl t X (.inl i) = X (.inl i) := by
  simp [Fl, fl]

theorem fl_inl' (X : K12 → List Sym) (j : Fin 64) (v : ℕ) (i : Fin 12) :
    fl X (.inr j) v (.inl i) = X (.inl i) :=
  fl_ne Sum.inl_ne_inr v

theorem Fl_wP (t : LayerRT) (X : K12 → List Sym) : Fl t X wP = natSyms t.P ++ Sym.mark :: X wP := by
  simp +decide [Fl, fl]
theorem Fl_wd (t : LayerRT) (X : K12 → List Sym) : Fl t X wd = natSyms t.d ++ Sym.mark :: X wd := by
  simp +decide [Fl, fl]
theorem Fl_wD (t : LayerRT) (X : K12 → List Sym) : Fl t X wD = natSyms t.D ++ Sym.mark :: X wD := by
  simp +decide [Fl, fl]
theorem Fl_wS (t : LayerRT) (X : K12 → List Sym) : Fl t X wS = natSyms t.S ++ Sym.mark :: X wS := by
  simp +decide [Fl, fl]
theorem Fl_wK (t : LayerRT) (X : K12 → List Sym) : Fl t X wK = natSyms t.K ++ Sym.mark :: X wK := by
  simp +decide [Fl, fl]
theorem Fl_wR (t : LayerRT) (X : K12 → List Sym) : Fl t X wR = natSyms t.ρ ++ Sym.mark :: X wR := by
  simp +decide [Fl, fl]
theorem Fl_wG (t : LayerRT) (X : K12 → List Sym) :
    Fl t X wG = natSyms (t.P * 3 + 3) ++ Sym.mark :: X wG := by
  simp +decide [Fl, fl]

/-- An output step: a push onto `.inl i` above the work stacks moves into the base. -/
theorem out_step {p : Prog K12 (fun _ => Sym) Reg2} {T : ℕ} (t : LayerRT) (B : K12 → List Sym)
    (i : Fin 12) (Z S0 : List Sym) (hBi : B (.inl i) = S0)
    (h : Runs p (Fl t B) (Function.update (Fl t B) (.inl i) (Z ++ Fl t B (.inl i)))
      (fun _ => True) T) :
    Runs p (Fl t B) (Fl t (Function.update B (.inl i) (Z ++ S0))) (fun _ => True) T := by
  rwa [Fl_inl, hBi, Fl_upd] at h

/-! ## 3. The loads -/

/-- Load the header field `i` onto the floored work stack `.inr j`. -/
def ldF (i : ℕ) (j : Fin 64) : Prog K12 (fun _ => Sym) Reg :=
  .seq (pushMark (.inr j)) (copyFieldN i sH (.inr j) sPk sTm)

/-- The loads: `P, d, D, S, K, ρ + 1` from the header, then `ρ` and `w_g`. -/
def loadU : Prog K12 (fun _ => Sym) Reg :=
  .seq (ldF 0 0) (.seq (ldF 1 1) (.seq (ldF 3 2) (.seq (ldF 5 3) (.seq (ldF 6 4) (.seq (ldF 7 5)
  (.seq (.seq (pushMark wR) (.seq (copyN wR1 wR sTm) (decL wR sTm)))
    (.seq (pushMark wG) (wgN stWg))))))))

theorem runs_ldF (t : LayerRT) (hrest : List Sym) (X : K12 → List Sym)
    (hX : X sH = t.hdr ++ hrest) (i : ℕ) (hi : i < 9) (j : Fin 64) (hj8 : j ≠ 8) (hj9 : j ≠ 9)
    (v : ℕ) (hv : (hfs t)[i]'(by simpa [hfs] using hi) = v) :
    Runs (ldF i j) X (fl X (.inr j) v) (fun _ => True) (1 + copyFieldCost (hfs t)) := by
  unfold ldF
  apply runs_fl
  have c := runs_copyFieldN (src := sH) (dst := (.inr j : K12)) (pk := sPk) (tmp := sTm)
    (by simp [List.nodup_cons, hj8, hj9]) (hfs t) i (by simpa [hfs] using hi) hrest
    (Function.update X (.inr j) (Sym.mark :: X (.inr j)))
    (by rw [Function.update_of_ne (Sum.inl_ne_inr : sH ≠ .inr j)]; exact hX)
  rw [Function.update_self, hv] at c
  exact c

theorem runs_loadU (t : LayerRT) (hrest : List Sym) (S : K12 → List Sym)
    (hH : S sH = t.hdr ++ hrest) :
    Runs loadU S (Fl t S) (fun _ => True) (loadCostP t) := by
  obtain ⟨X1, hX1⟩ : ∃ T, T = fl S wP t.P := ⟨_, rfl⟩
  obtain ⟨X2, hX2⟩ : ∃ T, T = fl X1 wd t.d := ⟨_, rfl⟩
  obtain ⟨X3, hX3⟩ : ∃ T, T = fl X2 wD t.D := ⟨_, rfl⟩
  obtain ⟨X4, hX4⟩ : ∃ T, T = fl X3 wS t.S := ⟨_, rfl⟩
  obtain ⟨X5, hX5⟩ : ∃ T, T = fl X4 wK t.K := ⟨_, rfl⟩
  obtain ⟨X6, hX6⟩ : ∃ T, T = fl X5 wR1 (t.ρ + 1) := ⟨_, rfl⟩
  obtain ⟨X7, hX7⟩ : ∃ T, T = fl X6 wR t.ρ := ⟨_, rfl⟩
  have hF : Fl t S = fl X7 wG (t.P * 3 + 3) := by
    rw [hX7, hX6, hX5, hX4, hX3, hX2, hX1]; rfl
  have r1 : Runs (ldF 0 0) S X1 (fun _ => True) (1 + copyFieldCost (hfs t)) := by
    rw [hX1]; exact runs_ldF t hrest S hH 0 (by norm_num) 0 (by decide) (by decide) t.P rfl
  have r2 : Runs (ldF 1 1) X1 X2 (fun _ => True) (1 + copyFieldCost (hfs t)) := by
    rw [hX2]
    exact runs_ldF t hrest X1 (by simp only [hX1, fl_inl']; exact hH) 1 (by norm_num) 1
      (by decide) (by decide) t.d rfl
  have r3 : Runs (ldF 3 2) X2 X3 (fun _ => True) (1 + copyFieldCost (hfs t)) := by
    rw [hX3]
    exact runs_ldF t hrest X2 (by simp only [hX2, hX1, fl_inl']; exact hH)
      3 (by norm_num) 2 (by decide) (by decide) t.D rfl
  have r4 : Runs (ldF 5 3) X3 X4 (fun _ => True) (1 + copyFieldCost (hfs t)) := by
    rw [hX4]
    exact runs_ldF t hrest X3 (by simp only [hX3, hX2, hX1, fl_inl']; exact hH) 5 (by norm_num) 3 (by decide) (by decide) t.S rfl
  have r5 : Runs (ldF 6 4) X4 X5 (fun _ => True) (1 + copyFieldCost (hfs t)) := by
    rw [hX5]
    exact runs_ldF t hrest X4 (by simp only [hX4, hX3, hX2, hX1, fl_inl']; exact hH) 6 (by norm_num) 4 (by decide)
      (by decide) t.K rfl
  have r6 : Runs (ldF 7 5) X5 X6 (fun _ => True) (1 + copyFieldCost (hfs t)) := by
    rw [hX6]
    exact runs_ldF t hrest X5 (by simp only [hX5, hX4, hX3, hX2, hX1, fl_inl']; exact hH) 7 (by norm_num) 5 (by decide) (by decide) (t.ρ + 1) rfl
  have r7 : Runs (.seq (pushMark wR) (.seq (copyN wR1 wR sTm) (decL wR sTm))) X6 X7 (fun _ => True)
      (1 + ((7 * bitLen (t.ρ + 1) + 7) + (6 * bitLen (t.ρ + 1) + 8))) := by
    rw [hX7]
    apply runs_fl
    have c1 := runs_copyN (src := wR1) (dst := wR) (tmp := sTm) (by decide) (by decide) (by decide)
      (t.ρ + 1) (Sym.mark :: X5 wR1) (Function.update X6 wR (Sym.mark :: X6 wR)) (termOK_mark _)
      (by rw [Function.update_of_ne (show wR1 ≠ wR by decide), hX6, fl_self])
    have c2 := runs_decL (k := wR) (t := sTm) (by decide) t.ρ (Sym.mark :: X6 wR)
      (Function.update (Function.update X6 wR (Sym.mark :: X6 wR)) wR
        (natSyms (t.ρ + 1) ++ Function.update X6 wR (Sym.mark :: X6 wR) wR))
      (termOK_mark _) (by rw [Function.update_self, Function.update_self])
    refine WP.W9comp.runs_congr (WP.W9comp.runs_seq c1 c2) ?_
    rw [Function.update_idem]
  have r8 : Runs (.seq (pushMark wG) (wgN stWg)) X7 (Fl t S) (fun _ => True)
      (1 + wgCost t.P) := by
    rw [hF]
    apply runs_fl
    have c := runs_wgN stWg_inj t.P (Sym.mark :: S wP)
      (Function.update X7 wG (Sym.mark :: X7 wG)) (termOK_mark _)
      (by
        rw [show stWg 0 = wP from rfl, Function.update_of_ne (show wP ≠ wG by decide)]
        simp +decide only [hX7, hX6, hX5, hX4, hX3, hX2, hX1, fl, Function.update_apply, if_true,
          if_false])
    rw [show stWg 1 = wG from rfl, Function.update_self] at c
    exact c
  exact WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6
    (WP.W9comp.runs_seq r7 r8))))))

/-! ## 4. The header output -/

/-- `hdrSyms [S, K, ρ, D, 0, 0, w_g, w_g]` onto `.inl 4`, bottom-up. -/
def hdrU : Prog K12 (fun _ => Sym) Reg :=
  .seq (pushW (.inl 4) .mark) (.seq (copyN wG (.inl 4) sTm)
  (.seq (pushW (.inl 4) .mark) (.seq (copyN wG (.inl 4) sTm)
  (.seq (pushW (.inl 4) .mark) (.seq (pushW (.inl 4) .mark) (.seq (pushW (.inl 4) .mark)
  (.seq (copyN wD (.inl 4) sTm) (.seq (pushW (.inl 4) .mark) (.seq (copyN wR (.inl 4) sTm)
  (.seq (pushW (.inl 4) .mark) (.seq (copyN wK (.inl 4) sTm)
  (.seq (pushW (.inl 4) .mark) (copyN wS (.inl 4) sTm)))))))))))))

theorem hdr_pw (t : LayerRT) (B : K12 → List Sym) (cur : List Sym) :
    Runs (pushW (.inl 4 : K12) .mark) (Fl t (Function.update B (.inl 4) cur))
      (Fl t (Function.update B (.inl 4) (Sym.mark :: cur))) (fun _ => True) 1 := by
  have c := runs_pushW (.inl 4 : K12) Sym.mark (Fl t (Function.update B (.inl 4) cur))
  rwa [Fl_inl, Function.update_self, Fl_upd, Function.update_idem] at c

theorem hdr_cp (t : LayerRT) (B : K12 → List Sym) (cur : List Sym) (w : K12) (v : ℕ)
    (hw4 : w ≠ .inl 4) (hw9 : w ≠ sTm)
    (hw : Fl t (Function.update B (.inl 4) cur) w = natSyms v ++ Sym.mark :: B w) :
    Runs (copyN w (.inl 4) sTm) (Fl t (Function.update B (.inl 4) cur))
      (Fl t (Function.update B (.inl 4) (natSyms v ++ cur))) (fun _ => True)
      (7 * bitLen v + 7) := by
  have c := runs_copyN (src := w) (dst := (.inl 4 : K12)) (tmp := sTm) hw4 hw9 (by decide) v
    (Sym.mark :: B w) (Fl t (Function.update B (.inl 4) cur)) (termOK_mark _) hw
  rwa [Fl_inl, Function.update_self, Fl_upd, Function.update_idem] at c

theorem runs_hdrU (t : LayerRT) (B : K12 → List Sym) :
    Runs hdrU (Fl t B) (Fl t (Function.update B (.inl 4)
      (hdrSyms [t.S, t.K, t.ρ, t.D, 0, 0, t.P * 3 + 3, t.P * 3 + 3] ++ B (.inl 4))))
      (fun _ => True) (hdrCostP t) := by
  have e0 : Fl t B = Fl t (Function.update B (.inl 4) (B (.inl 4))) := by
    rw [Function.update_eq_self]
  have hG : ∀ cur, Fl t (Function.update B (.inl 4) cur) wG =
      natSyms (t.P * 3 + 3) ++ Sym.mark :: B wG := fun cur => by
    rw [Fl_wG, Function.update_of_ne (show wG ≠ .inl 4 by decide)]
  have hD : ∀ cur, Fl t (Function.update B (.inl 4) cur) wD = natSyms t.D ++ Sym.mark :: B wD :=
    fun cur => by rw [Fl_wD, Function.update_of_ne (show wD ≠ .inl 4 by decide)]
  have hR : ∀ cur, Fl t (Function.update B (.inl 4) cur) wR = natSyms t.ρ ++ Sym.mark :: B wR :=
    fun cur => by rw [Fl_wR, Function.update_of_ne (show wR ≠ .inl 4 by decide)]
  have hK : ∀ cur, Fl t (Function.update B (.inl 4) cur) wK = natSyms t.K ++ Sym.mark :: B wK :=
    fun cur => by rw [Fl_wK, Function.update_of_ne (show wK ≠ .inl 4 by decide)]
  have hS : ∀ cur, Fl t (Function.update B (.inl 4) cur) wS = natSyms t.S ++ Sym.mark :: B wS :=
    fun cur => by rw [Fl_wS, Function.update_of_ne (show wS ≠ .inl 4 by decide)]
  rw [e0]
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq (hdr_pw t B _) (WP.W9comp.runs_seq
    (hdr_cp t B _ wG _ (by decide) (by decide) (hG _)) (WP.W9comp.runs_seq (hdr_pw t B _)
    (WP.W9comp.runs_seq (hdr_cp t B _ wG _ (by decide) (by decide) (hG _))
    (WP.W9comp.runs_seq (hdr_pw t B _) (WP.W9comp.runs_seq (hdr_pw t B _)
    (WP.W9comp.runs_seq (hdr_pw t B _)
    (WP.W9comp.runs_seq (hdr_cp t B _ wD _ (by decide) (by decide) (hD _))
    (WP.W9comp.runs_seq (hdr_pw t B _)
    (WP.W9comp.runs_seq (hdr_cp t B _ wR _ (by decide) (by decide) (hR _))
    (WP.W9comp.runs_seq (hdr_pw t B _)
    (WP.W9comp.runs_seq (hdr_cp t B _ wK _ (by decide) (by decide) (hK _))
    (WP.W9comp.runs_seq (hdr_pw t B _)
    (hdr_cp t B _ wS _ (by decide) (by decide) (hS _))))))))))))))) ?_
  congr 2
  simp only [hdrSyms_cons_append', natSyms_zero, List.nil_append] <;> rfl

/-! ## 5. The outputs -/

/-- The eleven outputs, each pushed on top of the old content of `.inl 1 … .inl 11`. -/
noncomputable def outU : Prog K12 (fun _ => Sym) Reg2 :=
  .seq ((copyFieldN 8 sH (.inl 1) sPk sTm).liftRegs lN)
  (.seq ((copyN wG (.inl 2) sTm).liftRegs lN)
  (.seq ((copyN wP (.inl 3) sTm).liftRegs lN)
  (.seq (hdrU.liftRegs lN)
  (.seq (q1N2 stQ1)
  (.seq (w0N2 stW0)
  (.seq ((copyN wK (.inl 7) sTm).liftRegs lN)
  (.seq (rowsN2 stRw)
  (.seq (keepN stKp)
  (.seq (npadN stNp)
  ((copyFieldN 2 sH (.inl 11) sPk sTm).liftRegs lN))))))))))

theorem runs_outU (t : LayerRT) (hD1 : 1 ≤ t.D) (hrest : List Sym) (S : K12 → List Sym)
    (hH : S sH = t.hdr ++ hrest) :
    Runs outU (Fl t S) (Fl t (preOut t S)) (fun _ => True) (outCostP t) := by
  obtain ⟨B1, hB1⟩ : ∃ T, T = Function.update S (.inl 1) (natSyms t.w ++ S (.inl 1)) := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ T, T = Function.update B1 (.inl 2) (natSyms (t.P * 3 + 3) ++ S (.inl 2)) :=
    ⟨_, rfl⟩
  obtain ⟨B3, hB3⟩ : ∃ T, T = Function.update B2 (.inl 3) (natSyms t.P ++ S (.inl 3)) := ⟨_, rfl⟩
  obtain ⟨B4, hB4⟩ : ∃ T, T = Function.update B3 (.inl 4)
      (hdrSyms [t.S, t.K, t.ρ, t.D, 0, 0, t.P * 3 + 3, t.P * 3 + 3] ++ S (.inl 4)) := ⟨_, rfl⟩
  obtain ⟨B5, hB5⟩ : ∃ T, T = Function.update B4 (.inl 5)
      (natSyms (min (q0Of t.d) t.D) ++ S (.inl 5)) := ⟨_, rfl⟩
  obtain ⟨B6, hB6⟩ : ∃ T, T = Function.update B5 (.inl 6)
      (natSyms (t.S * 2 ^ (t.K * (t.D - 1) + t.ρ)) ++ S (.inl 6)) := ⟨_, rfl⟩
  obtain ⟨B7, hB7⟩ : ∃ T, T = Function.update B6 (.inl 7) (natSyms t.K ++ S (.inl 7)) := ⟨_, rfl⟩
  obtain ⟨B8, hB8⟩ : ∃ T, T = Function.update B7 (.inl 8)
      ([Sym.bit (decide (q0Of t.d < t.D))] ++ S (.inl 8)) := ⟨_, rfl⟩
  obtain ⟨B9, hB9⟩ : ∃ T, T = Function.update B8 (.inl 9)
      (natSyms (2 ^ (t.K * t.D) * t.S) ++ S (.inl 9)) := ⟨_, rfl⟩
  obtain ⟨B10, hB10⟩ : ∃ T, T = Function.update B9 (.inl 10)
      (natSyms (npadVal t.d t.D t.K t.S) ++ S (.inl 10)) := ⟨_, rfl⟩
  have hP : preOut t S = Function.update B10 (.inl 11) (natSyms t.r ++ S (.inl 11)) := by
    rw [hB10, hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1]; rfl
  have o1 : Runs ((copyFieldN 8 sH (.inl 1) sPk sTm).liftRegs lN) (Fl t S) (Fl t B1)
      (fun _ => True) (copyFieldCost (hfs t)) := by
    rw [hB1]
    refine out_step t S 1 (natSyms t.w) (S (.inl 1)) rfl (runs_lN ?_)
    exact runs_copyFieldN (by decide) (hfs t) 8 (by simp [hfs]) hrest (Fl t S)
      (by rw [Fl_inl]; exact hH)
  have o2 : Runs ((copyN wG (.inl 2) sTm).liftRegs lN) (Fl t B1) (Fl t B2) (fun _ => True)
      (7 * bitLen (t.P * 3 + 3) + 7) := by
    rw [hB2]
    refine out_step t B1 2 (natSyms (t.P * 3 + 3)) (S (.inl 2)) (by simp (disch := decide) only [hB1, Function.update_of_ne]) (runs_lN ?_)
    exact runs_copyN (by decide) (by decide) (by decide) (t.P * 3 + 3) (Sym.mark :: B1 wG)
      (Fl t B1) (termOK_mark _) (Fl_wG t B1)
  have o3 : Runs ((copyN wP (.inl 3) sTm).liftRegs lN) (Fl t B2) (Fl t B3) (fun _ => True)
      (7 * bitLen t.P + 7) := by
    rw [hB3]
    refine out_step t B2 3 (natSyms t.P) (S (.inl 3)) (by simp (disch := decide) only [hB2, hB1, Function.update_of_ne]) (runs_lN ?_)
    exact runs_copyN (by decide) (by decide) (by decide) t.P (Sym.mark :: B2 wP)
      (Fl t B2) (termOK_mark _) (Fl_wP t B2)
  have o4 : Runs (hdrU.liftRegs lN) (Fl t B3) (Fl t B4) (fun _ => True) (hdrCostP t) := by
    have e : B3 (.inl 4) = S (.inl 4) := by simp (disch := decide) only [hB3, hB2, hB1, Function.update_of_ne]
    have c := runs_lN (runs_hdrU t B3)
    rw [e] at c
    rw [hB4]
    exact c
  have o5 : Runs (q1N2 stQ1) (Fl t B4) (Fl t B5) (fun _ => True) (q1Cost t.d t.D) := by
    rw [hB5]
    refine out_step t B4 5 (natSyms (min (q0Of t.d) t.D)) (S (.inl 5))
      (by simp (disch := decide) only [hB4, hB3, hB2, hB1, Function.update_of_ne]) ?_
    exact runs_q1N2 stQ1_inj t.d t.D (Sym.mark :: B4 wd) (Sym.mark :: B4 wD) (Fl t B4)
      (termOK_mark _) (termOK_mark _) (Fl_wd t B4) (Fl_wD t B4)
  have o6 : Runs (w0N2 stW0) (Fl t B5) (Fl t B6) (fun _ => True) (w0Cost t.D t.S t.K t.ρ) := by
    rw [hB6]
    refine out_step t B5 6 (natSyms (t.S * 2 ^ (t.K * (t.D - 1) + t.ρ))) (S (.inl 6))
      (by simp (disch := decide) only [hB5, hB4, hB3, hB2, hB1, Function.update_of_ne]) ?_
    exact runs_w0N2 stW0_inj t.D t.S t.K t.ρ hD1 (Sym.mark :: B5 wD) (Sym.mark :: B5 wS)
      (Sym.mark :: B5 wK) (Sym.mark :: B5 wR) (Fl t B5) (termOK_mark _) (termOK_mark _)
      (termOK_mark _) (termOK_mark _) (Fl_wD t B5) (Fl_wS t B5) (Fl_wK t B5) (Fl_wR t B5)
  have o7 : Runs ((copyN wK (.inl 7) sTm).liftRegs lN) (Fl t B6) (Fl t B7) (fun _ => True)
      (7 * bitLen t.K + 7) := by
    rw [hB7]
    refine out_step t B6 7 (natSyms t.K) (S (.inl 7)) (by simp (disch := decide) only [hB6, hB5, hB4, hB3, hB2, hB1, Function.update_of_ne])
      (runs_lN ?_)
    exact runs_copyN (by decide) (by decide) (by decide) t.K (Sym.mark :: B6 wK)
      (Fl t B6) (termOK_mark _) (Fl_wK t B6)
  have o8 : Runs (rowsN2 stRw) (Fl t B7) (Fl t B8) (fun _ => True) (rowsCost t.d t.D) := by
    rw [hB8]
    refine out_step t B7 8 [Sym.bit (decide (q0Of t.d < t.D))] (S (.inl 8))
      (by simp (disch := decide) only [hB7, hB6, hB5, hB4, hB3, hB2, hB1, Function.update_of_ne]) ?_
    exact runs_rowsN2 stRw_inj t.d t.D (Sym.mark :: B7 wd) (Sym.mark :: B7 wD) (Fl t B7)
      (termOK_mark _) (termOK_mark _) (Fl_wd t B7) (Fl_wD t B7)
  have o9 : Runs (keepN stKp) (Fl t B8) (Fl t B9) (fun _ => True) (keepCost t.D t.K t.S) := by
    rw [hB9]
    refine out_step t B8 9 (natSyms (2 ^ (t.K * t.D) * t.S)) (S (.inl 9))
      (by simp (disch := decide) only [hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1, Function.update_of_ne]) ?_
    exact runs_keepN stKp_inj t.D t.K t.S (Sym.mark :: B8 wD) (Sym.mark :: B8 wK)
      (Sym.mark :: B8 wS) (Fl t B8) (termOK_mark _) (termOK_mark _) (termOK_mark _)
      (Fl_wD t B8) (Fl_wK t B8) (Fl_wS t B8)
  have o10 : Runs (npadN stNp) (Fl t B9) (Fl t B10) (fun _ => True)
      (npadCost t.d t.D t.K t.S) := by
    rw [hB10]
    refine out_step t B9 10 (natSyms (npadVal t.d t.D t.K t.S)) (S (.inl 10))
      (by simp (disch := decide) only [hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1, Function.update_of_ne]) ?_
    exact runs_npadN stNp_inj t.d t.D t.K t.S (Sym.mark :: B9 wd) (Sym.mark :: B9 wD)
      (Sym.mark :: B9 wK) (Sym.mark :: B9 wS) (Fl t B9) (termOK_mark _) (termOK_mark _)
      (termOK_mark _) (termOK_mark _) (Fl_wd t B9) (Fl_wD t B9) (Fl_wK t B9) (Fl_wS t B9)
  have o11 : Runs ((copyFieldN 2 sH (.inl 11) sPk sTm).liftRegs lN) (Fl t B10)
      (Fl t (preOut t S)) (fun _ => True) (copyFieldCost (hfs t)) := by
    rw [hP]
    refine out_step t B10 11 (natSyms t.r) (S (.inl 11))
      (by simp (disch := decide) only [hB10, hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1, Function.update_of_ne]) (runs_lN ?_)
    exact runs_copyFieldN (by decide) (hfs t) 2 (by simp [hfs]) hrest (Fl t B10)
      (by rw [Fl_inl, show B10 sH = S sH by simp (disch := decide) only [hB10, hB9, hB8, hB7, hB6, hB5, hB4, hB3,
        hB2, hB1, Function.update_of_ne]]; exact hH)
  exact WP.W9comp.runs_seq o1 (WP.W9comp.runs_seq o2 (WP.W9comp.runs_seq o3
    (WP.W9comp.runs_seq o4 (WP.W9comp.runs_seq o5 (WP.W9comp.runs_seq o6
    (WP.W9comp.runs_seq o7 (WP.W9comp.runs_seq o8 (WP.W9comp.runs_seq o9
    (WP.W9comp.runs_seq o10 o11)))))))))

/-! ## 6. The drops and the whole kernel -/

/-- Drop the eight work stacks (with their floors). -/
def dropU : Prog K12 (fun _ => Sym) Reg :=
  .seq (dropF wG) (.seq (dropF wR) (.seq (dropF wR1) (.seq (dropF wK) (.seq (dropF wS)
  (.seq (dropF wD) (.seq (dropF wd) (dropF wP)))))))

theorem runs_dropU (t : LayerRT) (X : K12 → List Sym) :
    Runs dropU (Fl t X) X (fun _ => True) (dropCostP t) := by
  unfold dropU Fl
  exact WP.W9comp.runs_seq runs_dropF_fl (WP.W9comp.runs_seq runs_dropF_fl
    (WP.W9comp.runs_seq runs_dropF_fl (WP.W9comp.runs_seq runs_dropF_fl
    (WP.W9comp.runs_seq runs_dropF_fl (WP.W9comp.runs_seq runs_dropF_fl
    (WP.W9comp.runs_seq runs_dropF_fl runs_dropF_fl))))))

/-- **The kernel of the pre-phase parameters**: loads, outputs, drops. -/
noncomputable def preProg : Prog K12 (fun _ => Sym) Reg2 :=
  .seq (loadU.liftRegs lN) (.seq outU (dropU.liftRegs lN))

theorem closed_ldF (i : ℕ) (j : Fin 64) : (ldF i j).Closed :=
  WP.W9comp.closed_seq (closed_pushMark _) (closed_copyFieldN _ _ _ _ _)

theorem closed_loadU : loadU.Closed :=
  WP.W9comp.closed_seq (closed_ldF _ _) (WP.W9comp.closed_seq (closed_ldF _ _)
    (WP.W9comp.closed_seq (closed_ldF _ _) (WP.W9comp.closed_seq (closed_ldF _ _)
    (WP.W9comp.closed_seq (closed_ldF _ _) (WP.W9comp.closed_seq (closed_ldF _ _)
    (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _)
      (WP.W9comp.closed_seq (closed_copyN _ _ _) (closed_decL _ _)))
    (WP.W9comp.closed_seq (closed_pushMark _) (closed_wgN _))))))))

theorem closed_hdrU : hdrU.Closed :=
  WP.W9comp.closed_seq (closed_pushW _ _) (WP.W9comp.closed_seq (closed_copyN _ _ _)
  (WP.W9comp.closed_seq (closed_pushW _ _) (WP.W9comp.closed_seq (closed_copyN _ _ _)
  (WP.W9comp.closed_seq (closed_pushW _ _) (WP.W9comp.closed_seq (closed_pushW _ _)
  (WP.W9comp.closed_seq (closed_pushW _ _) (WP.W9comp.closed_seq (closed_copyN _ _ _)
  (WP.W9comp.closed_seq (closed_pushW _ _) (WP.W9comp.closed_seq (closed_copyN _ _ _)
  (WP.W9comp.closed_seq (closed_pushW _ _) (WP.W9comp.closed_seq (closed_copyN _ _ _)
  (WP.W9comp.closed_seq (closed_pushW _ _) (closed_copyN _ _ _)))))))))))))

theorem closed_outU : outU.Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (closed_copyFieldN _ _ _ _ _))
  (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (closed_copyN _ _ _))
  (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (closed_copyN _ _ _))
  (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN closed_hdrU)
  (WP.W9comp.closed_seq (closed_q1N2 _)
  (WP.W9comp.closed_seq (closed_w0N2 _)
  (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (closed_copyN _ _ _))
  (WP.W9comp.closed_seq (closed_rowsN2 _)
  (WP.W9comp.closed_seq (closed_keepN _)
  (WP.W9comp.closed_seq (closed_npadN _)
  (WP.W9comp.closed_liftRegs lN (closed_copyFieldN _ _ _ _ _)))))))))))

theorem closed_dropU : dropU.Closed :=
  WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (WP.W9comp.closed_seq (closed_dropF _)
  (WP.W9comp.closed_seq (closed_dropF _) (closed_dropF _)))))))

theorem closed_preProg : preProg.Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN closed_loadU)
    (WP.W9comp.closed_seq closed_outU (WP.W9comp.closed_liftRegs lN closed_dropU))

theorem runs_preProg (t : LayerRT) (hD1 : 1 ≤ t.D) (hrest : List Sym) (S : K12 → List Sym)
    (hH : S sH = t.hdr ++ hrest) :
    Runs preProg S (drvPreParamsPost t S) (fun _ => True) (preCostP t) := by
  have h := WP.W9comp.runs_seq (runs_lN (runs_loadU t hrest S hH))
    (WP.W9comp.runs_seq (runs_outU t hD1 hrest S hH) (runs_lN (runs_dropU t (preOut t S))))
  rw [preOut_eq] at h
  exact h

end SubNLogN.Machine.Layer.DrvPreParamsAux

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Layer.DrvArith
open SubNLogN.Machine.Layer.DrvPreParamsAux

/-- **The pre-phase parameter kernel** (`DrvPreParamsStmt`, exponent `J = 3`), from the proved
NatArith / W3 / W6a programs only. Fully proved, no placeholders. -/
theorem drvPreParams_holds : DrvPreParamsStmt := by
  obtain ⟨C, hC⟩ := preCostP_le
  refine ⟨3, C, fun _ => ⟨Fin 64, inferInstance, inferInstance, Reg2, preProg, inferInstance,
    inferInstance, closed_preProg, ?_⟩⟩
  intro t hrest S hρK hD1 hS0
  exact WP.W9comp.runs_mono (runs_preProg t hD1 hrest S hS0) (fun _ _ => trivial) (hC t hρK hD1)

end SubNLogN.Machine.Layer
