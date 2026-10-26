/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveAxisSetup

/-!
# K5-SOLVE driver (4): the sub-kernel calls between driver states (`Bridge/SolveAxisCalls.lean`)

`ParSpec`, `SpSpec`, `MgSpec`, `RISpec`, `RJSpec`, `SwSpec` are the bodies of the contracts
`SolParamRowsStmt`, `SolveHalfSplitStmt`, `SolveHalfMergeStmt`, `SolveReindexIStmt`,
`SolveReindexJStmt` and `SolveSweepStmt` for one program (so that `obtain` on a contract gives
them by `rfl`). `runs_par'`, `runs_sp'`, `runs_mg'`, `runs_ri'`, `runs_rj'`, `runs_sw'` run
the embedded sub-kernels (`callInj (ιG f inj)`) between the driver states `mk base (dV …)`.

All proved (no `sorry`). Helpers live in `SubNLogN.Machine.Bridge.SolveDrvAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveDrvAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability
  SubNLogN.Math.Common SubNLogN.Math.Bridge
open SubNLogN.Machine.Bridge.SolveAux (SwN Fits2 ColFitsI rec1s sweepHalfI)

/-! ## Contract bodies -/

/-- Body of `SolParamRowsStmt`. -/
def ParSpec (E R : Type) [Fintype E] [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc (Fin 7) E) (fun _ => Sym) R) : Prop :=
  ∀ (b : BrPar) (m h : ℕ) (i : Fin b.d) (T : BridgeTables b.t)
      (rsol rpar rax rh : List Sym) (S : KLoc (Fin 7) E → List Sym),
      KClean S → ShapeOK b.t → (i : ℕ) ≠ 0 → (i : ℕ) + m = b.d → h ≤ 1 → 1 ≤ b.wT →
      TablesOnGrid b.P b.t T → TablesFit b.wT b.P b.t T →
      TermOK rax → TermOK rh →
      S (.inl 0) = solTabSyms b.wT b.P b.t T ++ rsol →
      S (.inl 1) = hdrSyms b.hdr ++ rpar →
      S (.inl 2) = natSyms m ++ rax →
      S (.inl 3) = natSyms h ++ rh →
      Runs P S
        (Function.update (Function.update (Function.update S
          (.inl 4) (carrSyms (b.wT + 1) (solParamRow b i h (solGMu b.P T i)) ++ S (.inl 4)))
          (.inl 5) (carrSyms (b.wT + 1) (solParamRow b i h (solGNa b.P T i)) ++ S (.inl 5)))
          (.inl 6) (carrSyms (b.wT + 1) (solParamRow b i h (solGGm b.P T i)) ++ S (.inl 6)))
        (fun _ => True)
        (C * (solHalfM b i * (b.wT + Nat.log2 (totalLen b.t) + 1) + solTabLen b + b.setup))

/-- Body of `SolveHalfSplitStmt`. -/
def SpSpec (E R : Type) [Fintype E] [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc (Fin 4) E) (fun _ => Sym) R) : Prop :=
  ∀ (wd L M : ℕ) (v : List (List CInt)) (rest rM : List Sym) (S : KLoc (Fin 4) E → List Sym),
      KClean S → 1 ≤ M → v.length = L * (2 * M) → BlkTerm rest → TermOK rM →
      S (.inl 0) = carrSyms wd v ++ rest → S (.inl 3) = natSyms M ++ rM →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) rest)
          (.inl 1) (carrSyms wd (SolveSplit.fwdHalf M v) ++ S (.inl 1)))
          (.inl 2) (carrSyms wd (SolveSplit.bwdHalf M v) ++ S (.inl 2)))
        (fun _ => True) (C * (cvol wd v + v.length * (bitLen M + 1) + 1))

/-- Body of `SolveHalfMergeStmt`. -/
def MgSpec (E R : Type) [Fintype E] [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc (Fin 4) E) (fun _ => Sym) R) : Prop :=
  ∀ (wd L M : ℕ) (F B : List (List CInt)) (rF rB rM : List Sym)
      (S : KLoc (Fin 4) E → List Sym),
      KClean S → 1 ≤ M → F.length = L * M → B.length = L * M → BlkTerm rF → BlkTerm rB →
      TermOK rM →
      S (.inl 1) = carrSyms wd F ++ rF → S (.inl 2) = carrSyms wd B ++ rB →
      S (.inl 3) = natSyms M ++ rM →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 1) rF) (.inl 2) rB)
          (.inl 0) (carrSyms wd (SolveSplit.mergeHalves M F B) ++ S (.inl 0)))
        (fun _ => True)
        (C * (cvol wd F + cvol wd B + (F.length + B.length) * (bitLen M + 1) + 1))

/-- Body of `SolveReindexIStmt`. -/
def RISpec (E R : Type) [Fintype E] [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc (Fin 2) E) (fun _ => Sym) R) : Prop :=
  ∀ (wd L M : ℕ) (u : List (List CInt)) (rest rM : List Sym) (S : KLoc (Fin 2) E → List Sym),
      KClean S → 1 ≤ M → 2 ≤ L → u.length = L * M → BlkTerm rest → TermOK rM →
      S (.inl 0) = carrSyms wd u ++ rest → S (.inl 1) = natSyms M ++ rM →
      Runs P S (Function.update S (.inl 0) (carrSyms wd (SolveSplit.reindexI M u) ++ rest))
        (fun _ => True) (C * (cvol wd u + u.length * (bitLen M + 1) + 1))

/-- Body of `SolveReindexJStmt`. -/
def RJSpec (E R : Type) [Fintype E] [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc (Fin 2) E) (fun _ => Sym) R) : Prop :=
  ∀ (wd L M : ℕ) (u : List (List CInt)) (rest rM : List Sym) (S : KLoc (Fin 2) E → List Sym),
      KClean S → 1 ≤ M → 2 ≤ L → u.length = L * M → BlkTerm rest → TermOK rM →
      S (.inl 0) = carrSyms wd u ++ rest → S (.inl 1) = natSyms M ++ rM →
      Runs P S (Function.update S (.inl 0) (carrSyms wd (SolveSplit.reindexJ M u) ++ rest))
        (fun _ => True) (C * (cvol wd u + u.length * (bitLen M + 1) + 1))

/-- Body of `SolveSweepStmt` (after its four premises). -/
def SwSpec (E R : Type) [Fintype E] [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc SwN E) (fun _ => Sym) R) : Prop :=
  ∀ (wI wT q L M : ℕ) (ys : List CInt) (mus nas gms : List ℤ)
      (rdat rmu rna rgm r1 r2 r3 r4 r5 r6 r7 : List Sym) (S : KLoc SwN E → List Sym),
      KClean S → 1 ≤ wI → 1 ≤ wT → 1 ≤ L → 1 ≤ M →
      ys.length = L * M → mus.length = M → nas.length = M → gms.length = M →
      (∀ y ∈ ys, Fits2 wI y) → (∀ m ∈ mus, FitsTwos wT m) → (∀ m ∈ nas, FitsTwos wT m) →
      (∀ m ∈ gms, FitsTwos wT m) →
      (∀ s, s < M → ColFitsI wI q (mus.getD s 0) (nas.getD s 0) (gms.getD s 0) L
        (fun j => ys.getD (j * M + s) 0)) →
      TermOK rdat → TermOK rmu → TermOK rna → TermOK rgm → TermOK r1 → TermOK r2 → TermOK r3 →
      TermOK r4 → TermOK r5 → TermOK r6 → TermOK r7 →
      S (.inl .dat) = rec1s wI ys ++ rdat →
      S (.inl .mu) = rec1s wT (mus.map fun m => (m, 0)) ++ rmu →
      S (.inl .na) = rec1s wT (nas.map fun m => (m, 0)) ++ rna →
      S (.inl .gm) = rec1s wT (gms.map fun m => (m, 0)) ++ rgm →
      S (.inl .cwI) = natSyms wI ++ r1 → S (.inl .cwI2) = natSyms wI ++ r2 →
      S (.inl .cwI1) = natSyms (wI + 1) ++ r3 → S (.inl .cwT) = natSyms wT ++ r4 →
      S (.inl .cwP) = natSyms (wI + wT + 1) ++ r5 → S (.inl .cq) = natSyms q ++ r6 →
      S (.inl .c0) = natSyms 0 ++ r7 →
      Runs P S
        (Function.update (Function.update S (.inl .dat) rdat) (.inl .dst)
          (rec1s wI (sweepHalfI q L M mus nas gms ys) ++ S (.inl .dst)))
        (fun _ => True) (C * (L * M * (mulW (wI + wT + 1) + bitLen q + 1) + 1))

/-! ## Calls between driver states -/

section Calls

variable {EP : Type} [DecidableEq EP] {σ : Type}

/-- The parameter-row kernel: rows `MU`, `NA`, `GM` from empty stacks. -/
theorem runs_par' {Ep Rp : Type} [Fintype Ep] [DecidableEq Ep] {Cp : ℕ}
    {Pp : Prog (KLoc (Fin 7) Ep) (fun _ => Sym) Rp} (hs : ParSpec Ep Rp Cp Pp)
    {inj : Ep → EP} (hinj : Function.Injective inj) (lp : Lens σ Rp)
    (base : DK EP → List Sym) (hb : ∀ e, base (.inr (.inr e)) = []) (V : DX → List Sym)
    (b : BrPar) (m h : ℕ) (i : Fin b.d) (T : BridgeTables b.t) (rsol rpar rax : List Sym)
    (hsh : ShapeOK b.t) (hi : (i : ℕ) ≠ 0) (him : (i : ℕ) + m = b.d) (hh : h ≤ 1)
    (hwT : 1 ≤ b.wT) (htg : TablesOnGrid b.P b.t T) (htf : TablesFit b.wT b.P b.t T)
    (hrax : TermOK rax) (hsol : base (kN .solTab) = solTabSyms b.wT b.P b.t T ++ rsol)
    (hpar : base (kN .par) = hdrSyms b.hdr ++ rpar) (hax : V (.inl .ax) = natSyms m ++ rax)
    (hKH : V (.inr .KH) = natSyms h) (hMU : V (.inr .MU) = []) (hNA : V (.inr .NA) = [])
    (hGM : V (.inr .GM) = []) :
    Runs (callInj (ιG fPar inj) lp Pp) (mk base V)
      (mk base (Function.update (Function.update (Function.update V
        (.inr .MU) (carrSyms (b.wT + 1) (solParamRow b i h (solGMu b.P T i))))
        (.inr .NA) (carrSyms (b.wT + 1) (solParamRow b i h (solGNa b.P T i))))
        (.inr .GM) (carrSyms (b.wT + 1) (solParamRow b i h (solGGm b.P T i)))))
      (fun _ => True)
      (Cp * (solHalfM b i * (b.wT + Nat.log2 (totalLen b.t) + 1) + solTabLen b + b.setup)) := by
  have hι : Function.Injective (ιG (fPar (EP := EP)) inj) := ιG_injective fPar_inj hinj fPar_ne
  have hr := hs b m h i T rsol rpar rax [] (mk base V ∘ ιG fPar inj) (clean_comp _ _ _ _ hb) hsh
    hi him hh hwT htg htf hrax TermOK.nil hsol hpar hax (by rw [List.append_nil]; exact hKH)
  have e4 : (mk base V ∘ ιG fPar inj) (.inl 4) = [] := hMU
  have e5 : (mk base V ∘ ιG fPar inj) (.inl 5) = [] := hNA
  have e6 : (mk base V ∘ ιG fPar inj) (.inl 6) = [] := hGM
  rw [e4, e5, e6] at hr
  simp only [List.append_nil] at hr
  rw [upd_comp_mk hι (a := .inl 4) (x := .inr .MU) rfl,
    upd_comp_mk hι (a := .inl 5) (x := .inr .NA) rfl,
    upd_comp_mk hι (a := .inl 6) (x := .inr .GM) rfl] at hr
  refine runs_call_mk hι lp hr ?_
  intro x hx
  have h4 : x ≠ .inr .MU := by rintro rfl; exact hx (.inl 4) rfl
  have h5 : x ≠ .inr .NA := by rintro rfl; exact hx (.inl 5) rfl
  have h6 : x ≠ .inr .GM := by rintro rfl; exact hx (.inl 6) rfl
  rw [Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4]

/-- The split kernel: `arr → F0, B0`. -/
theorem runs_sp' {Es Rs : Type} [Fintype Es] [DecidableEq Es] {Cs : ℕ}
    {Ps : Prog (KLoc (Fin 4) Es) (fun _ => Sym) Rs} (hs : SpSpec Es Rs Cs Ps)
    {inj : Es → EP} (hinj : Function.Injective inj) (ls : Lens σ Rs)
    (base : DK EP → List Sym) (hb : ∀ e, base (.inr (.inr e)) = []) (V : DX → List Sym)
    (wd L M : ℕ) (v : List (List CInt)) (rest : List Sym) (hM : 1 ≤ M)
    (hv : v.length = L * (2 * M)) (hrest : BlkTerm rest)
    (harr : V (.inl .arr) = carrSyms wd v ++ rest) (hKM : V (.inr .KM) = natSyms M)
    (hF0 : V (.inr .F0) = []) (hB0 : V (.inr .B0) = []) :
    Runs (callInj (ιG fSp inj) ls Ps) (mk base V)
      (mk base (Function.update (Function.update (Function.update V (.inl .arr) rest)
        (.inr .F0) (carrSyms wd (SolveSplit.fwdHalf M v)))
        (.inr .B0) (carrSyms wd (SolveSplit.bwdHalf M v))))
      (fun _ => True) (Cs * (cvol wd v + v.length * (bitLen M + 1) + 1)) := by
  have hι : Function.Injective (ιG (fSp (EP := EP)) inj) := ιG_injective fSp_inj hinj fSp_ne
  have hr := hs wd L M v rest [] (mk base V ∘ ιG fSp inj) (clean_comp _ _ _ _ hb) hM hv hrest
    TermOK.nil harr (by rw [List.append_nil]; exact hKM)
  have e1 : (mk base V ∘ ιG fSp inj) (.inl 1) = [] := hF0
  have e2 : (mk base V ∘ ιG fSp inj) (.inl 2) = [] := hB0
  rw [e1, e2] at hr
  simp only [List.append_nil] at hr
  rw [upd_comp_mk hι (a := .inl 0) (x := .inl .arr) rfl,
    upd_comp_mk hι (a := .inl 1) (x := .inr .F0) rfl,
    upd_comp_mk hι (a := .inl 2) (x := .inr .B0) rfl] at hr
  refine runs_call_mk hι ls hr ?_
  intro x hx
  have h0 : x ≠ .inl .arr := by rintro rfl; exact hx (.inl 0) rfl
  have h1 : x ≠ .inr .F0 := by rintro rfl; exact hx (.inl 1) rfl
  have h2 : x ≠ .inr .B0 := by rintro rfl; exact hx (.inl 2) rfl
  rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]

/-- The merge kernel: `F1, B1 → arr`. -/
theorem runs_mg' {Em Rm : Type} [Fintype Em] [DecidableEq Em] {Cm : ℕ}
    {Pm : Prog (KLoc (Fin 4) Em) (fun _ => Sym) Rm} (hs : MgSpec Em Rm Cm Pm)
    {inj : Em → EP} (hinj : Function.Injective inj) (lm : Lens σ Rm)
    (base : DK EP → List Sym) (hb : ∀ e, base (.inr (.inr e)) = []) (V : DX → List Sym)
    (wd L M : ℕ) (F B : List (List CInt)) (hM : 1 ≤ M) (hF : F.length = L * M)
    (hB : B.length = L * M) (hF1 : V (.inr .F1) = carrSyms wd F)
    (hB1 : V (.inr .B1) = carrSyms wd B) (hKM : V (.inr .KM) = natSyms M) :
    Runs (callInj (ιG fMg inj) lm Pm) (mk base V)
      (mk base (Function.update (Function.update (Function.update V (.inr .F1) [])
        (.inr .B1) []) (.inl .arr) (carrSyms wd (SolveSplit.mergeHalves M F B) ++ V (.inl .arr))))
      (fun _ => True)
      (Cm * (cvol wd F + cvol wd B + (F.length + B.length) * (bitLen M + 1) + 1)) := by
  have hι : Function.Injective (ιG (fMg (EP := EP)) inj) := ιG_injective fMg_inj hinj fMg_ne
  have hr := hs wd L M F B [] [] [] (mk base V ∘ ιG fMg inj) (clean_comp _ _ _ _ hb) hM hF hB
    (fun _ h => by simp at h) (fun _ h => by simp at h) TermOK.nil
    (by rw [List.append_nil]; exact hF1) (by rw [List.append_nil]; exact hB1)
    (by rw [List.append_nil]; exact hKM)
  rw [upd_comp_mk hι (a := .inl 1) (x := .inr .F1) rfl,
    upd_comp_mk hι (a := .inl 2) (x := .inr .B1) rfl,
    upd_comp_mk hι (a := .inl 0) (x := .inl .arr) rfl] at hr
  refine runs_call_mk hι lm hr ?_
  intro x hx
  have h0 : x ≠ .inl .arr := by rintro rfl; exact hx (.inl 0) rfl
  have h1 : x ≠ .inr .F1 := by rintro rfl; exact hx (.inl 1) rfl
  have h2 : x ≠ .inr .B1 := by rintro rfl; exact hx (.inl 2) rfl
  rw [Function.update_of_ne h0, Function.update_of_ne h2, Function.update_of_ne h1]

/-- The reindex kernel `I` on `B0`. -/
theorem runs_ri' {Er Rr : Type} [Fintype Er] [DecidableEq Er] {Cr : ℕ}
    {Pr : Prog (KLoc (Fin 2) Er) (fun _ => Sym) Rr} (hs : RISpec Er Rr Cr Pr)
    {inj : Er → EP} (hinj : Function.Injective inj) (lr : Lens σ Rr)
    (base : DK EP → List Sym) (hb : ∀ e, base (.inr (.inr e)) = []) (V : DX → List Sym)
    (wd L M : ℕ) (u : List (List CInt)) (hM : 1 ≤ M) (hL : 2 ≤ L) (hu : u.length = L * M)
    (hA : V (.inr .B0) = carrSyms wd u) (hKM : V (.inr .KM) = natSyms M) :
    Runs (callInj (ιG (fRe .B0) inj) lr Pr) (mk base V)
      (mk base (Function.update V (.inr .B0) (carrSyms wd (SolveSplit.reindexI M u))))
      (fun _ => True) (Cr * (cvol wd u + u.length * (bitLen M + 1) + 1)) := by
  have hι : Function.Injective (ιG (fRe (EP := EP) .B0) inj) :=
    ιG_injective (fRe_inj (by decide)) hinj (fRe_ne .B0)
  have hr := hs wd L M u [] [] (mk base V ∘ ιG (fRe .B0) inj) (clean_comp _ _ _ _ hb) hM hL hu
    (fun _ h => by simp at h) TermOK.nil (by rw [List.append_nil]; exact hA)
    (by rw [List.append_nil]; exact hKM)
  simp only [List.append_nil] at hr
  rw [upd_comp_mk hι (a := .inl 0) (x := .inr .B0) rfl] at hr
  refine runs_call_mk hι lr hr ?_
  intro x hx
  have h0 : x ≠ .inr .B0 := by rintro rfl; exact hx (.inl 0) rfl
  rw [Function.update_of_ne h0]

/-- The reindex kernel `J` on `B1`. -/
theorem runs_rj' {Er Rr : Type} [Fintype Er] [DecidableEq Er] {Cr : ℕ}
    {Pr : Prog (KLoc (Fin 2) Er) (fun _ => Sym) Rr} (hs : RJSpec Er Rr Cr Pr)
    {inj : Er → EP} (hinj : Function.Injective inj) (lr : Lens σ Rr)
    (base : DK EP → List Sym) (hb : ∀ e, base (.inr (.inr e)) = []) (V : DX → List Sym)
    (wd L M : ℕ) (u : List (List CInt)) (hM : 1 ≤ M) (hL : 2 ≤ L) (hu : u.length = L * M)
    (hA : V (.inr .B1) = carrSyms wd u) (hKM : V (.inr .KM) = natSyms M) :
    Runs (callInj (ιG (fRe .B1) inj) lr Pr) (mk base V)
      (mk base (Function.update V (.inr .B1) (carrSyms wd (SolveSplit.reindexJ M u))))
      (fun _ => True) (Cr * (cvol wd u + u.length * (bitLen M + 1) + 1)) := by
  have hι : Function.Injective (ιG (fRe (EP := EP) .B1) inj) :=
    ιG_injective (fRe_inj (by decide)) hinj (fRe_ne .B1)
  have hr := hs wd L M u [] [] (mk base V ∘ ιG (fRe .B1) inj) (clean_comp _ _ _ _ hb) hM hL hu
    (fun _ h => by simp at h) TermOK.nil (by rw [List.append_nil]; exact hA)
    (by rw [List.append_nil]; exact hKM)
  simp only [List.append_nil] at hr
  rw [upd_comp_mk hι (a := .inl 0) (x := .inr .B1) rfl] at hr
  refine runs_call_mk hι lr hr ?_
  intro x hx
  have h0 : x ≠ .inr .B1 := by rintro rfl; exact hx (.inl 0) rfl
  rw [Function.update_of_ne h0]

/-- The sweep kernel on the half `A` (data, consumed) into `B` (destination, empty). -/
theorem runs_sw' {Ew Rw : Type} [Fintype Ew] [DecidableEq Ew] {Cw : ℕ}
    {Pw : Prog (KLoc SwN Ew) (fun _ => Sym) Rw} (hs : SwSpec Ew Rw Cw Pw)
    {inj : Ew → EP} (hinj : Function.Injective inj) (lw : Lens σ Rw)
    {A B : DW} (hg : Function.Injective (gSw A B))
    (base : DK EP → List Sym) (hb : ∀ e, base (.inr (.inr e)) = []) (V : DX → List Sym)
    (wI wT q L M : ℕ) (ys : List CInt) (mus nas gms : List ℤ)
    (hwI : 1 ≤ wI) (hwT : 1 ≤ wT) (hL : 1 ≤ L) (hM : 1 ≤ M) (hys : ys.length = L * M)
    (hmus : mus.length = M) (hnas : nas.length = M) (hgms : gms.length = M)
    (hfy : ∀ y ∈ ys, Fits2 wI y) (hfm : ∀ m ∈ mus, FitsTwos wT m)
    (hfn : ∀ m ∈ nas, FitsTwos wT m) (hfg : ∀ m ∈ gms, FitsTwos wT m)
    (hcol : ∀ s, s < M → ColFitsI wI q (mus.getD s 0) (nas.getD s 0) (gms.getD s 0) L
      (fun j => ys.getD (j * M + s) 0))
    (hA : V (.inr A) = rec1s wI ys) (hB : V (.inr B) = [])
    (hMU : V (.inr .MU) = rec1s wT (mus.map fun m => (m, 0)))
    (hNA : V (.inr .NA) = rec1s wT (nas.map fun m => (m, 0)))
    (hGM : V (.inr .GM) = rec1s wT (gms.map fun m => (m, 0)))
    (h1 : V (.inr .cwI) = natSyms wI) (h2 : V (.inr .cwI2) = natSyms wI)
    (h3 : V (.inr .cwI1) = natSyms (wI + 1)) (h4 : V (.inr .cwT) = natSyms wT)
    (h5 : V (.inr .cwP) = natSyms (wI + wT + 1)) (h6 : V (.inr .cq) = natSyms q)
    (h7 : V (.inr .c0) = natSyms 0) :
    Runs (callInj (ιG (fSw A B) inj) lw Pw) (mk base V)
      (mk base (Function.update (Function.update V (.inr A) []) (.inr B)
        (rec1s wI (sweepHalfI q L M mus nas gms ys))))
      (fun _ => True) (Cw * (L * M * (mulW (wI + wT + 1) + bitLen q + 1) + 1)) := by
  have hι : Function.Injective (ιG (fSw (EP := EP) A B) inj) :=
    ιG_injective (fSw_inj hg) hinj (fSw_ne A B)
  have hr := hs wI wT q L M ys mus nas gms [] [] [] [] [] [] [] [] [] [] []
    (mk base V ∘ ιG (fSw A B) inj) (clean_comp _ _ _ _ hb) hwI hwT hL hM hys hmus hnas hgms
    hfy hfm hfn hfg hcol TermOK.nil TermOK.nil TermOK.nil TermOK.nil TermOK.nil TermOK.nil
    TermOK.nil TermOK.nil TermOK.nil TermOK.nil TermOK.nil
    (by rw [List.append_nil]; exact hA) (by rw [List.append_nil]; exact hMU)
    (by rw [List.append_nil]; exact hNA) (by rw [List.append_nil]; exact hGM)
    (by rw [List.append_nil]; exact h1) (by rw [List.append_nil]; exact h2)
    (by rw [List.append_nil]; exact h3) (by rw [List.append_nil]; exact h4)
    (by rw [List.append_nil]; exact h5) (by rw [List.append_nil]; exact h6)
    (by rw [List.append_nil]; exact h7)
  have eB : (mk base V ∘ ιG (fSw A B) inj) (.inl .dst) = [] := hB
  rw [eB, List.append_nil, upd_comp_mk hι (a := .inl .dat) (x := .inr A) rfl,
    upd_comp_mk hι (a := .inl .dst) (x := .inr B) rfl] at hr
  refine runs_call_mk hι lw hr ?_
  intro x hx
  have hxA : x ≠ .inr A := by rintro rfl; exact hx (.inl .dat) rfl
  have hxB : x ≠ .inr B := by rintro rfl; exact hx (.inl .dst) rfl
  rw [Function.update_of_ne hxB, Function.update_of_ne hxA]

end Calls

end SubNLogN.Machine.Bridge.SolveDrvAux
