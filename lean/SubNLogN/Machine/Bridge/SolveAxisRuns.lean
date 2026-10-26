/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveAxisGlue
import SubNLogN.Machine.Bridge.SolveAxisCostDefs

/-!
# K5-SOLVE driver (6): the driver program and its run (`Bridge/SolveAxisRuns.lean`)

`drvProg Pp Ps Pm Pr Pj Pw`: the deconvolution-stage driver on `KLoc BrK (DW ⊕ EPd …)`, calling the
parameter-row (`Pp`, twice), split (`Ps`), merge (`Pm`), reindex (`Pr`, `Pj`) and sweep (`Pw`,
twice) kernels:
setup; rows h=0; count `M`; split; sweep `F0 → F1`; erase rows; `KH := 1`; rows h=1; `KH := 0`;
reindex `I` (`B0`); sweep `B0 → B1`; reindex `J` (`B1`); erase rows; merge into `arr`; erase
the counters.
`runs_drv_core`: from the contract bodies of the six kernels, the run from the state with the
input `encVec q Y` on `arr` to the state with `encVec q (deconvAxisFixedR roundHalfUpR q t T i Y)`
(value glue `deconvAxis_glue`, width glue `sweepFits_of_solveFits`), cost `drvCost`.

All proved (no `sorry`). Helpers live in `SubNLogN.Machine.Bridge.SolveDrvAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveDrvAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability
  SubNLogN.Math.Common SubNLogN.Math.Bridge
open SubNLogN.Machine.Bridge.SolveAux (SwN Fits2 ColFitsI rec1s sweepHalfI recsOf)

/-- Scratch of the sub-kernels. -/
abbrev EPd (Ep Es Em Er Ej Ew : Type) : Type := Ep ⊕ (Es ⊕ (Em ⊕ (Er ⊕ (Ej ⊕ Ew))))

/-- Registers of the driver. -/
abbrev σd (Rp Rs Rm Rr Rj Rw : Type) : Type :=
  Option Sym × (Rp × (Rs × (Rm × (Rr × (Rj × Rw)))))

/-- Shortcut instance: decidable equality of the sub-kernel scratch (avoids deep instance search). -/
scoped instance instDecEqEPd {Ep Es Em Er Ej Ew : Type} [DecidableEq Ep] [DecidableEq Es]
    [DecidableEq Em] [DecidableEq Er] [DecidableEq Ej] [DecidableEq Ew] :
    DecidableEq (EPd Ep Es Em Er Ej Ew) :=
  inferInstanceAs (DecidableEq (Ep ⊕ (Es ⊕ (Em ⊕ (Er ⊕ (Ej ⊕ Ew))))))

/-- Shortcut instance: decidable equality of the driver layout. -/
scoped instance instDecEqDK {EP : Type} [DecidableEq EP] : DecidableEq (DK EP) :=
  inferInstanceAs (DecidableEq (BrK ⊕ (DW ⊕ EP)))

/-- The backward sweep output (before the readout `J`). -/
noncomputable def solveX (P : ℕ) {d : ℕ} {t : Fin d → ℕ} (T : BridgeTables t) (i : Fin d)
    (Y : Fin (totalLen t) → ℂ) : List CInt :=
  sweepHalfI (P + 2) (prefixProd t i) (solveM t i) (solveRowB t i (solveGMu P T i))
    (solveRowB t i (solveGNa P T i)) (solveRowB t i (solveGGm P T i))
    (SolveSplit.reindexI (solveM t i) (SolveSplit.bwdHalf (solveM t i) (solveYs (P + 2) Y)))

theorem runs_cost_eq {K σ : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T T' : ℕ} (h : Runs P S S' Q T) (hT : T = T') :
    Runs P S S' Q T' := hT ▸ h

theorem sum_map_const_len2 (k a c : ℕ) : ∀ l : List (List Bool), (∀ bs ∈ l, bs.length = k) →
    (l.map fun bs => 12 * bs.length + a + c).sum = l.length * (12 * k + a + c)
  | [], _ => by simp
  | bs :: l, h => by
    have ih := sum_map_const_len2 k a c l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, h bs (List.mem_cons_self ..)]
    ring

section Closed

variable {K : Type} [DecidableEq K]

theorem closed_clearStk (k : K) : (clearStk k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, clearStk, peekR, popR]

theorem closed_cntAll (A B T C : K) : (cntAll A B T C).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, cntAll, cntBody, SolveAux.moveRec, moveBlock, moveBits,
    moveBitsBody, restoreR, popR, pushC, pushR, peekR, inc, incFix, scanLoop, Lib.scanBody,
    SolveAux.drainRecs, SolveAux.drainBody, skip]

end Closed

section Drv

variable {Ep Es Em Er Ej Ew Rp Rs Rm Rr Rj Rw : Type}

def iP : Ep → EPd Ep Es Em Er Ej Ew := Sum.inl
def iS : Es → EPd Ep Es Em Er Ej Ew := fun e => .inr (.inl e)
def iM : Em → EPd Ep Es Em Er Ej Ew := fun e => .inr (.inr (.inl e))
def iR : Er → EPd Ep Es Em Er Ej Ew := fun e => .inr (.inr (.inr (.inl e)))
def iJ : Ej → EPd Ep Es Em Er Ej Ew := fun e => .inr (.inr (.inr (.inr (.inl e))))
def iW : Ew → EPd Ep Es Em Er Ej Ew := fun e => .inr (.inr (.inr (.inr (.inr e))))

theorem iP_inj : Function.Injective (@iP Ep Es Em Er Ej Ew) := fun _ _ h => Sum.inl_injective h
theorem iS_inj : Function.Injective (@iS Ep Es Em Er Ej Ew) := fun _ _ h => by simpa [iS] using h
theorem iM_inj : Function.Injective (@iM Ep Es Em Er Ej Ew) := fun _ _ h => by simpa [iM] using h
theorem iR_inj : Function.Injective (@iR Ep Es Em Er Ej Ew) := fun _ _ h => by simpa [iR] using h
theorem iJ_inj : Function.Injective (@iJ Ep Es Em Er Ej Ew) := fun _ _ h => by simpa [iJ] using h
theorem iW_inj : Function.Injective (@iW Ep Es Em Er Ej Ew) := fun _ _ h => by simpa [iW] using h

def lS : Lens (σd Rp Rs Rm Rr Rj Rw) (Option Sym) := Lens.fst _ _
def lP : Lens (σd Rp Rs Rm Rr Rj Rw) Rp := (Lens.snd _ _).comp (Lens.fst _ _)
def lSp : Lens (σd Rp Rs Rm Rr Rj Rw) Rs :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lM : Lens (σd Rp Rs Rm Rr Rj Rw) Rm :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lR : Lens (σd Rp Rs Rm Rr Rj Rw) Rr :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
def lJ : Lens (σd Rp Rs Rm Rr Rj Rw) Rj :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))
def lW : Lens (σd Rp Rs Rm Rr Rj Rw) Rw :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.snd _ _)))))


/-- Empty the private stack `x`. -/
def clr [DecidableEq Ep] [DecidableEq Es] [DecidableEq Em] [DecidableEq Er]
    [DecidableEq Ej] [DecidableEq Ew] (x : DW) : Prog (DK (EPd Ep Es Em Er Ej Ew)) (fun _ => Sym) (σd Rp Rs Rm Rr Rj Rw) :=
  (clearStk (loc (.inr x))).liftRegs lS

/-- Count the records of `MU` into `KM`. -/
def cntP [DecidableEq Ep] [DecidableEq Es] [DecidableEq Em] [DecidableEq Er]
    [DecidableEq Ej] [DecidableEq Ew] : Prog (DK (EPd Ep Es Em Er Ej Ew)) (fun _ => Sym) (σd Rp Rs Rm Rr Rj Rw) :=
  (cntAll (loc (.inr .MU)) (loc (.inr .TR)) (loc (.inr .TT)) (loc (.inr .KM))).liftRegs lS

/-- **The driver program.** -/
def drvProg [DecidableEq Ep] [DecidableEq Es] [DecidableEq Em] [DecidableEq Er]
    [DecidableEq Ej] [DecidableEq Ew] (Pp : Prog (KLoc (Fin 7) Ep) (fun _ => Sym) Rp)
    (Ps : Prog (KLoc (Fin 4) Es) (fun _ => Sym) Rs) (Pm : Prog (KLoc (Fin 4) Em) (fun _ => Sym) Rm)
    (Pr : Prog (KLoc (Fin 2) Er) (fun _ => Sym) Rr) (Pj : Prog (KLoc (Fin 2) Ej) (fun _ => Sym) Rj)
    (Pw : Prog (KLoc SwN Ew) (fun _ => Sym) Rw) :
    Prog (DK (EPd Ep Es Em Er Ej Ew)) (fun _ => Sym) (σd Rp Rs Rm Rr Rj Rw) :=
  .seq (setupP lS) 
    (.seq (callInj (ιG fPar iP) lP Pp)
    (.seq cntP
    (.seq (callInj (ιG fSp iS) lSp Ps)
    (.seq (callInj (ιG (fSw .F0 .F1) iW) lW Pw)
    (.seq (clr .MU)
    (.seq (clr .NA)
    (.seq (clr .GM)
    (.seq ((pushC (loc (.inr .KH)) (.bit true)).liftRegs lS)
    (.seq (callInj (ιG fPar iP) lP Pp)
    (.seq ((popR (loc (.inr .KH))).liftRegs lS)
    (.seq (callInj (ιG (fRe .B0) iR) lR Pr)
    (.seq (callInj (ιG (fSw .B0 .B1) iW) lW Pw)
    (.seq (callInj (ιG (fRe .B1) iJ) lJ Pj)
    (.seq (clr .MU)
    (.seq (clr .NA)
    (.seq (clr .GM)
    (.seq (callInj (ιG fMg iM) lM Pm)
    (.seq (clr .cwI)
    (.seq (clr .cwI2)
    (.seq (clr .cwI1)
    (.seq (clr .cwT)
    (.seq (clr .cwP)
    (.seq (clr .cq)
    (clr .KM))))))))))))))))))))))))

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
theorem closed_drvProg [DecidableEq Ep] [DecidableEq Es] [DecidableEq Em] [DecidableEq Er]
    [DecidableEq Ej] [DecidableEq Ew] {Pp : Prog (KLoc (Fin 7) Ep) (fun _ => Sym) Rp}
    {Ps : Prog (KLoc (Fin 4) Es) (fun _ => Sym) Rs} {Pm : Prog (KLoc (Fin 4) Em) (fun _ => Sym) Rm}
    {Pr : Prog (KLoc (Fin 2) Er) (fun _ => Sym) Rr} {Pj : Prog (KLoc (Fin 2) Ej) (fun _ => Sym) Rj}
    {Pw : Prog (KLoc SwN Ew) (fun _ => Sym) Rw} (h1 : Pp.Closed) (h2 : Ps.Closed) (h3 : Pm.Closed)
    (h4 : Pr.Closed) (h5 : Pj.Closed) (h6 : Pw.Closed) :
    (drvProg Pp Ps Pm Pr Pj Pw).Closed := by
  have hc : ∀ x : DW,
      (clr x : Prog (DK (EPd Ep Es Em Er Ej Ew)) (fun _ => Sym) (σd Rp Rs Rm Rr Rj Rw)).Closed :=
    fun x => WP.W9comp.closed_liftRegs _ (closed_clearStk _)
  have hn : (cntP : Prog (DK (EPd Ep Es Em Er Ej Ew)) (fun _ => Sym)
      (σd Rp Rs Rm Rr Rj Rw)).Closed := WP.W9comp.closed_liftRegs _ (closed_cntAll _ _ _ _)
  have hpu : ((pushC (loc (EP := EPd Ep Es Em Er Ej Ew) (.inr .KH)) (.bit true)).liftRegs
      (lS : Lens (σd Rp Rs Rm Rr Rj Rw) (Option Sym))).Closed :=
    WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, pushC])
  have hpo : ((popR (loc (EP := EPd Ep Es Em Er Ej Ew) (.inr .KH))).liftRegs
      (lS : Lens (σd Rp Rs Rm Rr Rj Rw) (Option Sym))).Closed :=
    WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, popR])
  simp only [drvProg, Prog.Closed, Prog.FreeBelow]
  exact ⟨closed_setupP _, closed_callInj _ _ h1, hn, closed_callInj _ _ h2, closed_callInj _ _ h6,
    hc _, hc _, hc _, hpu, closed_callInj _ _ h1, hpo, closed_callInj _ _ h4,
    closed_callInj _ _ h6, closed_callInj _ _ h5, hc _, hc _, hc _, closed_callInj _ _ h3,
    hc _, hc _, hc _, hc _, hc _, hc _, hc _⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The driver run** from the contract bodies of the six kernels: from the input `encVec q Y` on
`arr` (all private stacks empty) to `encVec q (deconvAxisFixedR roundHalfUpR q t T i Y)` on `arr`,
everything else restored, within `drvCost`. -/
theorem runs_drv_core [DecidableEq Ep] [DecidableEq Es] [DecidableEq Em] [DecidableEq Er]
    [DecidableEq Ej] [DecidableEq Ew] [Fintype Ep] [Fintype Es] [Fintype Em] [Fintype Er] [Fintype Ej]
    [Fintype Ew] {Cp Cs Cm Cr Cj Cw : ℕ}
    {Pp : Prog (KLoc (Fin 7) Ep) (fun _ => Sym) Rp} {Ps : Prog (KLoc (Fin 4) Es) (fun _ => Sym) Rs}
    {Pm : Prog (KLoc (Fin 4) Em) (fun _ => Sym) Rm} {Pr : Prog (KLoc (Fin 2) Er) (fun _ => Sym) Rr}
    {Pj : Prog (KLoc (Fin 2) Ej) (fun _ => Sym) Rj} {Pw : Prog (KLoc SwN Ew) (fun _ => Sym) Rw}
    (hsP : ParSpec Ep Rp Cp Pp) (hsS : SpSpec Es Rs Cs Ps) (hsM : MgSpec Em Rm Cm Pm)
    (hsR : RISpec Er Rr Cr Pr) (hsJ : RJSpec Ej Rj Cj Pj) (hsW : SwSpec Ew Rw Cw Pw)
    (b : BrPar) (m : ℕ) (i : Fin b.d) (T : BridgeTables b.t) (Y : Fin (totalLen b.t) → ℂ)
    (rarr rax rpar rsol ax ex : List Sym) (base : DK (EPd Ep Es Em Er Ej Ew) → List Sym)
    (hb : ∀ e, base (.inr (.inr e)) = [])
    (hshape : ShapeOK b.t) (hi : (i : ℕ) ≠ 0) (him : (i : ℕ) + m = b.d)
    (hwI : 1 ≤ b.wI) (hwT : 1 ≤ b.wT) (hP : b.P + 2 ≤ b.wI)
    (htg : TablesOnGrid b.P b.t T) (htf : TablesFit b.wT b.P b.t T)
    (hY : ∀ f, OnGrid (b.P + 2) (Y f)) (hYf : ArrFits b.wI (b.P + 2) Y)
    (hSF : SolveFits b.wI (b.P + 2) b.t T i Y) (hrarr : BlkTerm rarr) (hrax : TermOK rax)
    (hax : ax = natSyms m ++ rax) (hpar : base (kN .par) = hdrSyms b.hdr ++ rpar)
    (hsol : base (kN .solTab) = solTabSyms b.wT b.P b.t T ++ rsol) :
    Runs (drvProg Pp Ps Pm Pr Pj Pw)
      (mk base (eV ax ex (carrSyms b.wI (encVec (b.P + 2) Y) ++ rarr)))
      (mk base (eV ax ex (carrSyms b.wI (encVec (b.P + 2)
        (deconvAxisFixedR roundHalfUpR (b.P + 2) b.t T i Y)) ++ rarr)))
      (fun _ => True) (drvCost b i Cp Cs Cm Cr Cj Cw) := by
  obtain ⟨-, hM0, -, -, -, hR, -⟩ := SolveMathAux.solve_arith hshape i
  have hL2 : 2 ≤ prefixProd b.t i := two_le_prefixProd hshape i hi
  have hysl : (solveYs (b.P + 2) Y).length = prefixProd b.t i * (2 * solveM b.t i) := by
    rw [len_solveYs, hR]
  have hv : encVec (b.P + 2) Y = (solveYs (b.P + 2) Y).map fun c => [c] := encVec_eq_map _ Y
  have hvl : (encVec (b.P + 2) Y).length = prefixProd b.t i * (2 * solveM b.t i) := by
    rw [hv, List.length_map, hysl]
  have hvl0 : (encVec (b.P + 2) Y).length = totalLen b.t := by rw [hvl, ← hR]
  have hsv : ∀ cs ∈ encVec (b.P + 2) Y, cs.length = 1 := by
    rw [hv]; exact forall_len_map_one' _
  have hML : solHalfM b i = solveM b.t i := rfl
  have hfwl := SolveSplit.length_fwdHalf hM0 hysl
  have hbwl := SolveSplit.length_bwdHalf hM0 hysl
  have hril := SolveSplit.length_reindexI hM0 hbwl
  have hbwv := SolveSplit.length_bwdHalf hM0 hvl
  have hsbw : ∀ cs ∈ SolveSplit.bwdHalf (solveM b.t i) (encVec (b.P + 2) Y), cs.length = 1 :=
    fun cs hcs => hsv cs (mem_of_mem_bwdHalf hM0 hvl hcs)
  have hXl : ((solveX b.P T i Y).map fun c => [c]).length = prefixProd b.t i * solveM b.t i := by
    rw [List.length_map]; exact SolveMathAux.length_sweepHalfI _ _ _ _ _ _ _
  have hFl : ((solveF b.P T i Y).map fun c => [c]).length = prefixProd b.t i * solveM b.t i := by
    rw [List.length_map]; exact SolveMathAux.length_sweepHalfI _ _ _ _ _ _ _
  have hJl : (SolveSplit.reindexJ (solveM b.t i) ((solveX b.P T i Y).map fun c => [c])).length =
      prefixProd b.t i * solveM b.t i := SolveSplit.length_reindexJ hM0 hXl
  have hsJ1 : ∀ cs ∈ SolveSplit.reindexJ (solveM b.t i) ((solveX b.P T i Y).map fun c => [c]),
      cs.length = 1 := by
    rw [SolveSplit.reindexJ_map]; exact forall_len_map_one' _
  have hsF := sweepFits_of_solveFits b.wI b.P T i Y hshape hi htg hY hSF
  obtain ⟨fmF, fnF, fgF⟩ := fits_rowF (T := T) (i := i) hshape hi hwT htf
  obtain ⟨fmB, fnB, fgB⟩ := fits_rowB (T := T) (i := i) hshape hi hwT htf
  have fys := fits_solveYs hYf
  have hrowlen : ∀ (h : ℕ) (g : ℕ → ℤ), (carrSyms (b.wT + 1) (solParamRow b i h g)).length =
      solveM b.t i * (2 * (b.wT + 1) + 1) := by
    intro h g
    rw [len_carrSyms_one _ _ (by
      intro cs hcs
      simp only [solParamRow] at hcs
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hcs
      rfl)]
    simp [solParamRow, solHalfM, solveM]
  obtain ⟨A0, hA0⟩ : ∃ x, x = carrSyms b.wI (encVec (b.P + 2) Y) ++ rarr := ⟨_, rfl⟩
  obtain ⟨P0m, hP0m⟩ : ∃ x, x = carrSyms (b.wT + 1) (solParamRow b i 0 (solGMu b.P T i)) :=
    ⟨_, rfl⟩
  obtain ⟨P0n, hP0n⟩ : ∃ x, x = carrSyms (b.wT + 1) (solParamRow b i 0 (solGNa b.P T i)) :=
    ⟨_, rfl⟩
  obtain ⟨P0g, hP0g⟩ : ∃ x, x = carrSyms (b.wT + 1) (solParamRow b i 0 (solGGm b.P T i)) :=
    ⟨_, rfl⟩
  obtain ⟨P1m, hP1m⟩ : ∃ x, x = carrSyms (b.wT + 1) (solParamRow b i 1 (solGMu b.P T i)) :=
    ⟨_, rfl⟩
  obtain ⟨P1n, hP1n⟩ : ∃ x, x = carrSyms (b.wT + 1) (solParamRow b i 1 (solGNa b.P T i)) :=
    ⟨_, rfl⟩
  obtain ⟨P1g, hP1g⟩ : ∃ x, x = carrSyms (b.wT + 1) (solParamRow b i 1 (solGGm b.P T i)) :=
    ⟨_, rfl⟩
  obtain ⟨Fh, hFh⟩ : ∃ x, x = carrSyms b.wI (SolveSplit.fwdHalf (solveM b.t i)
      (encVec (b.P + 2) Y)) := ⟨_, rfl⟩
  obtain ⟨Bh, hBh⟩ : ∃ x, x = carrSyms b.wI (SolveSplit.bwdHalf (solveM b.t i)
      (encVec (b.P + 2) Y)) := ⟨_, rfl⟩
  obtain ⟨Fo, hFo⟩ : ∃ x, x = rec1s b.wI (solveF b.P T i Y) := ⟨_, rfl⟩
  obtain ⟨Bi, hBi⟩ : ∃ x, x = carrSyms b.wI (SolveSplit.reindexI (solveM b.t i)
      (SolveSplit.bwdHalf (solveM b.t i) (encVec (b.P + 2) Y))) := ⟨_, rfl⟩
  obtain ⟨Bo, hBo⟩ : ∃ x, x = rec1s b.wI (solveX b.P T i Y) := ⟨_, rfl⟩
  obtain ⟨Bj, hBj⟩ : ∃ x, x = carrSyms b.wI (SolveSplit.reindexJ (solveM b.t i)
      ((solveX b.P T i Y).map fun c => [c])) := ⟨_, rfl⟩
  obtain ⟨Res, hRes⟩ : ∃ x, x = carrSyms b.wI (SolveSplit.mergeHalves (solveM b.t i)
      ((solveF b.P T i Y).map fun c => [c])
      (SolveSplit.reindexJ (solveM b.t i) ((solveX b.P T i Y).map fun c => [c]))) ++ rarr :=
    ⟨_, rfl⟩
  have hFo' : Fo = rec1s b.wI (sweepHalfI (b.P + 2) (prefixProd b.t i) (solveM b.t i)
      (solveRowF b.t i (solveGMu b.P T i)) (solveRowF b.t i (solveGNa b.P T i))
      (solveRowF b.t i (solveGGm b.P T i))
      (SolveSplit.fwdHalf (solveM b.t i) (solveYs (b.P + 2) Y))) := hFo
  have hBo' : Bo = rec1s b.wI (sweepHalfI (b.P + 2) (prefixProd b.t i) (solveM b.t i)
      (solveRowB b.t i (solveGMu b.P T i)) (solveRowB b.t i (solveGNa b.P T i))
      (solveRowB b.t i (solveGGm b.P T i))
      (SolveSplit.reindexI (solveM b.t i)
        (SolveSplit.bwdHalf (solveM b.t i) (solveYs (b.P + 2) Y)))) := hBo
  have r1 : Runs (setupP lS) (mk base (eV ax ex A0)) (mk base (dV b ax ex A0 [] [] [] [] [] [] [] [] [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (setupCost b) := by
    rw [hA0]; exact runs_setup lS b rpar ax ex _ base hP hpar
  have r2 : Runs (callInj (ιG fPar iP) lP Pp) (mk base (dV b ax ex A0 [] [] [] [] [] [] [] [] [])) (mk base (dV b ax ex A0 [] [] [] [] P0m P0n P0g [] [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (Cp * (solveM b.t i * (b.wT + Nat.log2 (totalLen b.t) + 1) + solTabLen b + b.setup)) := by
    have h := runs_par' (σ := σd Rp Rs Rm Rr Rj Rw) hsP iP_inj lP base hb (dV b ax ex A0 [] [] [] [] [] [] [] [] []) b m 0 i T rsol rpar rax hshape hi
      him (by omega) hwT htg htf hrax hsol hpar hax natSyms_zero'.symm rfl rfl rfl
    rw [upd_MU, upd_NA, upd_GM, hML, ← hP0m, ← hP0n, ← hP0g] at h
    exact h
  have r3 : Runs (cntP) (mk base (dV b ax ex A0 [] [] [] [] P0m P0n P0g [] [])) (mk base (dV b ax ex A0 [] [] [] [] P0m P0n P0g (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (solveM b.t i * (24 * b.wT + 6 * bitLen (solveM b.t i) + 57) + 4) := by
    have hrows : P0m = recsOf ((solParamRow b i 0 (solGMu b.P T i)).map (crecBits (b.wT + 1))) := by
      rw [hP0m, SolveAux.carrSyms_eq_recsOf]
    have hk : ∀ bs ∈ (solParamRow b i 0 (solGMu b.P T i)).map (crecBits (b.wT + 1)),
        bs.length = 2 * (b.wT + 1) := by
      intro bs hbs
      obtain ⟨cs, hcs, rfl⟩ := List.mem_map.1 hbs
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hcs
      exact len_crecBits_one' _ _
    have hne : ∀ bs ∈ (solParamRow b i 0 (solGMu b.P T i)).map (crecBits (b.wT + 1)), bs ≠ [] := by
      intro bs hbs h0
      have := hk bs hbs
      rw [h0, List.length_nil] at this
      omega
    have hlen : ((solParamRow b i 0 (solGMu b.P T i)).map (crecBits (b.wT + 1))).length =
        solveM b.t i := by simp [solParamRow, solHalfM, solveM]
    have h := runs_cnt (σ := σd Rp Rs Rm Rr Rj Rw) lS base (dV b ax ex A0 [] [] [] [] P0m P0n P0g [] []) _ hne 0 (bitLen (solveM b.t i)) hrows rfl rfl
      natSyms_zero'.symm (le_of_eq (by rw [hlen, Nat.zero_add]))
    rw [upd_KM, hlen, Nat.zero_add] at h
    refine runs_cost_eq h ?_
    rw [sum_map_const_len2 (2 * (b.wT + 1)) _ _ _ hk, hlen]
    ring
  have r4 : Runs (callInj (ιG fSp iS) lSp Ps) (mk base (dV b ax ex A0 [] [] [] [] P0m P0n P0g (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex rarr Fh Bh [] [] P0m P0n P0g (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (Cs * (totalLen b.t * (2 * b.wI + 1) + totalLen b.t * (bitLen (solveM b.t i) + 1) + 1)) := by
    have h := runs_sp' (σ := σd Rp Rs Rm Rr Rj Rw) hsS iS_inj lSp base hb (dV b ax ex A0 [] [] [] [] P0m P0n P0g (natSyms (solveM b.t i)) []) b.wI (prefixProd b.t i) (solveM b.t i)
      (encVec (b.P + 2) Y) rarr hM0 hvl hrarr hA0 rfl rfl rfl
    rw [upd_arr, upd_F0, upd_B0, ← hFh, ← hBh] at h
    refine runs_cost_eq h ?_
    simp only [cvol]
    rw [len_carrSyms_one _ _ hsv, hvl0]
  have r5 : Runs (callInj (ιG (fSw .F0 .F1) iW) lW Pw) (mk base (dV b ax ex rarr Fh Bh [] [] P0m P0n P0g (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex rarr [] Bh Fo [] P0m P0n P0g (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (Cw * (prefixProd b.t i * solveM b.t i * (mulW (b.wI + (b.wT + 1) + 1) + bitLen (b.P + 2) + 1) + 1)) := by
    have h := runs_sw' (σ := σd Rp Rs Rm Rr Rj Rw) hsW iW_inj lW gSw_F_inj base hb (dV b ax ex rarr Fh Bh [] [] P0m P0n P0g (natSyms (solveM b.t i)) []) b.wI (b.wT + 1) (b.P + 2)
      (prefixProd b.t i) (solveM b.t i) (SolveSplit.fwdHalf (solveM b.t i) (solveYs (b.P + 2) Y))
      (solveRowF b.t i (solveGMu b.P T i)) (solveRowF b.t i (solveGNa b.P T i))
      (solveRowF b.t i (solveGGm b.P T i)) hwI (by omega) (by omega) hM0 hfwl (len_solveRowF _ _)
      (len_solveRowF _ _) (len_solveRowF _ _) (fun y hy => fys y (mem_of_mem_fwdHalf hM0 hysl hy))
      fmF fnF fgF hsF.1 (by show Fh = _; rw [hFh, hv, SolveSplit.fwdHalf_map] <;> rfl) rfl
      (by show P0m = _; rw [hP0m, rowF_eq] <;> rfl) (by show P0n = _; rw [hP0n, rowF_eq] <;> rfl)
      (by show P0g = _; rw [hP0g, rowF_eq] <;> rfl) rfl rfl rfl rfl
      (by rw [show b.wI + (b.wT + 1) + 1 = b.wI + b.wT + 2 by omega] <;> rfl) rfl
      natSyms_zero'.symm
    rw [upd_F0, upd_F1, ← hFo'] at h
    exact h
  have r6 : Runs (clr .MU) (mk base (dV b ax ex rarr [] Bh Fo [] P0m P0n P0g (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex rarr [] Bh Fo [] [] P0n P0g (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * (solveM b.t i * (2 * (b.wT + 1) + 1)) + 2) := by
    have h := runs_clear (σ := σd Rp Rs Rm Rr Rj Rw) lS base (dV b ax ex rarr [] Bh Fo [] P0m P0n P0g (natSyms (solveM b.t i)) []) (.inr .MU)
    rw [upd_MU] at h
    refine runs_cost_eq h ?_
    show 3 * P0m.length + 2 = _
    rw [hP0m, hrowlen]
  have r7 : Runs (clr .NA) (mk base (dV b ax ex rarr [] Bh Fo [] [] P0n P0g (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex rarr [] Bh Fo [] [] [] P0g (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * (solveM b.t i * (2 * (b.wT + 1) + 1)) + 2) := by
    have h := runs_clear (σ := σd Rp Rs Rm Rr Rj Rw) lS base (dV b ax ex rarr [] Bh Fo [] [] P0n P0g (natSyms (solveM b.t i)) []) (.inr .NA)
    rw [upd_NA] at h
    refine runs_cost_eq h ?_
    show 3 * P0n.length + 2 = _
    rw [hP0n, hrowlen]
  have r8 : Runs (clr .GM) (mk base (dV b ax ex rarr [] Bh Fo [] [] [] P0g (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex rarr [] Bh Fo [] [] [] [] (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * (solveM b.t i * (2 * (b.wT + 1) + 1)) + 2) := by
    have h := runs_clear (σ := σd Rp Rs Rm Rr Rj Rw) lS base (dV b ax ex rarr [] Bh Fo [] [] [] P0g (natSyms (solveM b.t i)) []) (.inr .GM)
    rw [upd_GM] at h
    refine runs_cost_eq h ?_
    show 3 * P0g.length + 2 = _
    rw [hP0g, hrowlen]
  have r15 : Runs (clr .MU) (mk base (dV b ax ex rarr [] [] Fo Bj P1m P1n P1g (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex rarr [] [] Fo Bj [] P1n P1g (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * (solveM b.t i * (2 * (b.wT + 1) + 1)) + 2) := by
    have h := runs_clear (σ := σd Rp Rs Rm Rr Rj Rw) lS base (dV b ax ex rarr [] [] Fo Bj P1m P1n P1g (natSyms (solveM b.t i)) []) (.inr .MU)
    rw [upd_MU] at h
    refine runs_cost_eq h ?_
    show 3 * P1m.length + 2 = _
    rw [hP1m, hrowlen]
  have r16 : Runs (clr .NA) (mk base (dV b ax ex rarr [] [] Fo Bj [] P1n P1g (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex rarr [] [] Fo Bj [] [] P1g (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * (solveM b.t i * (2 * (b.wT + 1) + 1)) + 2) := by
    have h := runs_clear (σ := σd Rp Rs Rm Rr Rj Rw) lS base (dV b ax ex rarr [] [] Fo Bj [] P1n P1g (natSyms (solveM b.t i)) []) (.inr .NA)
    rw [upd_NA] at h
    refine runs_cost_eq h ?_
    show 3 * P1n.length + 2 = _
    rw [hP1n, hrowlen]
  have r17 : Runs (clr .GM) (mk base (dV b ax ex rarr [] [] Fo Bj [] [] P1g (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex rarr [] [] Fo Bj [] [] [] (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * (solveM b.t i * (2 * (b.wT + 1) + 1)) + 2) := by
    have h := runs_clear (σ := σd Rp Rs Rm Rr Rj Rw) lS base (dV b ax ex rarr [] [] Fo Bj [] [] P1g (natSyms (solveM b.t i)) []) (.inr .GM)
    rw [upd_GM] at h
    refine runs_cost_eq h ?_
    show 3 * P1g.length + 2 = _
    rw [hP1g, hrowlen]
  have r9 : Runs ((pushC (loc (.inr .KH)) (.bit true)).liftRegs lS) (mk base (dV b ax ex rarr [] Bh Fo [] [] [] [] (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex rarr [] Bh Fo [] [] [] [] (natSyms (solveM b.t i)) [Sym.bit true])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (1) := by
    have h := runs_push (σ := σd Rp Rs Rm Rr Rj Rw) lS base (dV b ax ex rarr [] Bh Fo [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .KH) (.bit true)
    rw [upd_KH] at h
    exact h
  have r10 : Runs (callInj (ιG fPar iP) lP Pp) (mk base (dV b ax ex rarr [] Bh Fo [] [] [] [] (natSyms (solveM b.t i)) [Sym.bit true])) (mk base (dV b ax ex rarr [] Bh Fo [] P1m P1n P1g (natSyms (solveM b.t i)) [Sym.bit true])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (Cp * (solveM b.t i * (b.wT + Nat.log2 (totalLen b.t) + 1) + solTabLen b + b.setup)) := by
    have h := runs_par' (σ := σd Rp Rs Rm Rr Rj Rw) hsP iP_inj lP base hb (dV b ax ex rarr [] Bh Fo [] [] [] [] (natSyms (solveM b.t i)) [Sym.bit true]) b m 1 i T rsol rpar rax hshape hi
      him le_rfl hwT htg htf hrax hsol hpar hax natSyms_one'.symm rfl rfl rfl
    rw [upd_MU, upd_NA, upd_GM, hML, ← hP1m, ← hP1n, ← hP1g] at h
    exact h
  have r11 : Runs ((popR (loc (.inr .KH))).liftRegs lS) (mk base (dV b ax ex rarr [] Bh Fo [] P1m P1n P1g (natSyms (solveM b.t i)) [Sym.bit true])) (mk base (dV b ax ex rarr [] Bh Fo [] P1m P1n P1g (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (1) := by
    have h := runs_pop (σ := σd Rp Rs Rm Rr Rj Rw) lS base (dV b ax ex rarr [] Bh Fo [] P1m P1n P1g (natSyms (solveM b.t i)) [Sym.bit true]) (.inr .KH) (.bit true) [] rfl
    rw [upd_KH] at h
    exact h
  have r12 : Runs (callInj (ιG (fRe .B0) iR) lR Pr) (mk base (dV b ax ex rarr [] Bh Fo [] P1m P1n P1g (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex rarr [] Bi Fo [] P1m P1n P1g (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (Cr * (prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) + prefixProd b.t i * solveM b.t i * (bitLen (solveM b.t i) + 1) + 1)) := by
    have h := runs_ri' (σ := σd Rp Rs Rm Rr Rj Rw) hsR iR_inj lR base hb (dV b ax ex rarr [] Bh Fo [] P1m P1n P1g (natSyms (solveM b.t i)) []) b.wI (prefixProd b.t i) (solveM b.t i)
      (SolveSplit.bwdHalf (solveM b.t i) (encVec (b.P + 2) Y)) hM0 hL2 hbwv hBh rfl
    rw [upd_B0, ← hBi] at h
    refine runs_cost_eq h ?_
    simp only [cvol]
    rw [len_carrSyms_one _ _ hsbw, hbwv]
  have r13 : Runs (callInj (ιG (fSw .B0 .B1) iW) lW Pw) (mk base (dV b ax ex rarr [] Bi Fo [] P1m P1n P1g (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex rarr [] [] Fo Bo P1m P1n P1g (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (Cw * (prefixProd b.t i * solveM b.t i * (mulW (b.wI + (b.wT + 1) + 1) + bitLen (b.P + 2) + 1) + 1)) := by
    have h := runs_sw' (σ := σd Rp Rs Rm Rr Rj Rw) hsW iW_inj lW gSw_B_inj base hb (dV b ax ex rarr [] Bi Fo [] P1m P1n P1g (natSyms (solveM b.t i)) []) b.wI (b.wT + 1) (b.P + 2)
      (prefixProd b.t i) (solveM b.t i)
      (SolveSplit.reindexI (solveM b.t i) (SolveSplit.bwdHalf (solveM b.t i) (solveYs (b.P + 2) Y)))
      (solveRowB b.t i (solveGMu b.P T i)) (solveRowB b.t i (solveGNa b.P T i))
      (solveRowB b.t i (solveGGm b.P T i)) hwI (by omega) (by omega) hM0 hril (len_solveRowB _ _)
      (len_solveRowB _ _) (len_solveRowB _ _)
      (fun y hy => fys y (mem_of_mem_bwdHalf hM0 hysl (mem_of_mem_reindexI hM0 hbwl hy)))
      fmB fnB fgB hsF.2
      (by show Bi = _; rw [hBi, hv, SolveSplit.bwdHalf_map, SolveSplit.reindexI_map] <;> rfl) rfl
      (by show P1m = _; rw [hP1m, rowB_eq] <;> rfl) (by show P1n = _; rw [hP1n, rowB_eq] <;> rfl)
      (by show P1g = _; rw [hP1g, rowB_eq] <;> rfl) rfl rfl rfl rfl
      (by rw [show b.wI + (b.wT + 1) + 1 = b.wI + b.wT + 2 by omega] <;> rfl) rfl
      natSyms_zero'.symm
    rw [upd_B0, upd_B1, ← hBo'] at h
    exact h
  have r14 : Runs (callInj (ιG (fRe .B1) iJ) lJ Pj) (mk base (dV b ax ex rarr [] [] Fo Bo P1m P1n P1g (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex rarr [] [] Fo Bj P1m P1n P1g (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (Cj * (prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) + prefixProd b.t i * solveM b.t i * (bitLen (solveM b.t i) + 1) + 1)) := by
    have h := runs_rj' (σ := σd Rp Rs Rm Rr Rj Rw) hsJ iJ_inj lJ base hb (dV b ax ex rarr [] [] Fo Bo P1m P1n P1g (natSyms (solveM b.t i)) []) b.wI (prefixProd b.t i) (solveM b.t i)
      ((solveX b.P T i Y).map fun c => [c]) hM0 hL2 hXl (by show Bo = _; rw [hBo] <;> rfl) rfl
    rw [upd_B1, ← hBj] at h
    refine runs_cost_eq h ?_
    simp only [cvol]
    rw [len_carrSyms_one _ _ (forall_len_map_one' _), hXl]
  have r18 : Runs (callInj (ιG fMg iM) lM Pm) (mk base (dV b ax ex rarr [] [] Fo Bj [] [] [] (natSyms (solveM b.t i)) [])) (mk base (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (Cm * (prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) + prefixProd b.t i * solveM b.t i * (2 * b.wI + 1) + (prefixProd b.t i * solveM b.t i + prefixProd b.t i * solveM b.t i) * (bitLen (solveM b.t i) + 1) + 1)) := by
    have h := runs_mg' (σ := σd Rp Rs Rm Rr Rj Rw) hsM iM_inj lM base hb (dV b ax ex rarr [] [] Fo Bj [] [] [] (natSyms (solveM b.t i)) []) b.wI (prefixProd b.t i) (solveM b.t i)
      ((solveF b.P T i Y).map fun c => [c])
      (SolveSplit.reindexJ (solveM b.t i) ((solveX b.P T i Y).map fun c => [c])) hM0 hFl hJl
      (by show Fo = _; rw [hFo] <;> rfl) hBj rfl
    have e : (dV b ax ex rarr [] [] Fo Bj [] [] [] (natSyms (solveM b.t i)) []) (.inl .arr) = rarr := rfl
    rw [upd_F1, upd_B1, upd_arr, e, ← hRes] at h
    refine runs_cost_eq h ?_
    simp only [cvol]
    rw [len_carrSyms_one _ _ (forall_len_map_one' _), len_carrSyms_one _ _ hsJ1, hFl, hJl]
  have r19 : Runs (clr .cwI) (mk base (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) [])) (mk base (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * bitLen b.wI + 2) := by
    refine runs_cost_eq (runs_clear lS base (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI)) ?_
    show 3 * (natSyms b.wI).length + 2 = _
    rw [len_natSyms]
  have r20 : Runs (clr .cwI2) (mk base (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) [])) (mk base (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * bitLen b.wI + 2) := by
    refine runs_cost_eq (runs_clear lS base (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2)) ?_
    show 3 * (natSyms b.wI).length + 2 = _
    rw [len_natSyms]
  have r21 : Runs (clr .cwI1) (mk base (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) [])) (mk base (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * bitLen (b.wI + 1) + 2) := by
    refine runs_cost_eq (runs_clear lS base (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1)) ?_
    show 3 * (natSyms (b.wI + 1)).length + 2 = _
    rw [len_natSyms]
  have r22 : Runs (clr .cwT) (mk base (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) [])) (mk base (Function.update (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) []) (.inr .cwT) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * bitLen (b.wT + 1) + 2) := by
    refine runs_cost_eq (runs_clear lS base (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) []) (.inr .cwT)) ?_
    show 3 * (natSyms (b.wT + 1)).length + 2 = _
    rw [len_natSyms]
  have r23 : Runs (clr .cwP) (mk base (Function.update (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) []) (.inr .cwT) [])) (mk base (Function.update (Function.update (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) []) (.inr .cwT) []) (.inr .cwP) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * bitLen (b.wI + b.wT + 2) + 2) := by
    refine runs_cost_eq (runs_clear lS base (Function.update (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) []) (.inr .cwT) []) (.inr .cwP)) ?_
    show 3 * (natSyms (b.wI + b.wT + 2)).length + 2 = _
    rw [len_natSyms]
  have r24 : Runs (clr .cq) (mk base (Function.update (Function.update (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) []) (.inr .cwT) []) (.inr .cwP) [])) (mk base (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) []) (.inr .cwT) []) (.inr .cwP) []) (.inr .cq) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * bitLen (b.P + 2) + 2) := by
    refine runs_cost_eq (runs_clear lS base (Function.update (Function.update (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) []) (.inr .cwT) []) (.inr .cwP) []) (.inr .cq)) ?_
    show 3 * (natSyms (b.P + 2)).length + 2 = _
    rw [len_natSyms]
  have r25 : Runs (clr .KM) (mk base (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) []) (.inr .cwT) []) (.inr .cwP) []) (.inr .cq) [])) (mk base (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) []) (.inr .cwT) []) (.inr .cwP) []) (.inr .cq) []) (.inr .KM) [])) (fun _ : σd Rp Rs Rm Rr Rj Rw => True)
      (3 * bitLen (solveM b.t i) + 2) := by
    refine runs_cost_eq (runs_clear lS base (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) []) (.inr .cwT) []) (.inr .cwP) []) (.inr .cq) []) (.inr .KM)) ?_
    show 3 * ((natSyms (solveM b.t i))).length + 2 = _
    rw [len_natSyms]
  have hfin : (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (dV b ax ex Res [] [] [] [] [] [] [] (natSyms (solveM b.t i)) []) (.inr .cwI) []) (.inr .cwI2) []) (.inr .cwI1) []) (.inr .cwT) []) (.inr .cwP) []) (.inr .cq) []) (.inr .KM) []) = eV ax ex Res := by
    funext x
    rcases x with w | x
    · cases w <;> rfl
    · cases x <;> rfl
  have e1 : SolveSplit.mergeHalves (solveM b.t i) ((solveF b.P T i Y).map fun c => [c])
      (SolveSplit.reindexJ (solveM b.t i) ((solveX b.P T i Y).map fun c => [c])) =
      (SolveSplit.mergeHalves (solveM b.t i) (solveF b.P T i Y) (solveB b.P T i Y)).map
        fun c => [c] :=
    (congrArg (SolveSplit.mergeHalves (solveM b.t i) ((solveF b.P T i Y).map fun c => [c]))
      (SolveSplit.reindexJ_map (fun c : CInt => [c]) (solveM b.t i) (solveX b.P T i Y))).trans
      (SolveSplit.mergeHalves_map (fun c : CInt => [c]) (solveM b.t i) (solveF b.P T i Y)
        (SolveSplit.reindexJ (solveM b.t i) (solveX b.P T i Y)))
  have hRes' : Res = carrSyms b.wI (encVec (b.P + 2)
      (deconvAxisFixedR roundHalfUpR (b.P + 2) b.t T i Y)) ++ rarr := by
    rw [hRes, e1, deconvAxis_glue b.P T i Y hshape hi htg hY]
  have chain := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3 (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6 (WP.W9comp.runs_seq r7 (WP.W9comp.runs_seq r8 (WP.W9comp.runs_seq r9 (WP.W9comp.runs_seq r10 (WP.W9comp.runs_seq r11 (WP.W9comp.runs_seq r12 (WP.W9comp.runs_seq r13 (WP.W9comp.runs_seq r14 (WP.W9comp.runs_seq r15 (WP.W9comp.runs_seq r16 (WP.W9comp.runs_seq r17 (WP.W9comp.runs_seq r18 (WP.W9comp.runs_seq r19 (WP.W9comp.runs_seq r20 (WP.W9comp.runs_seq r21 (WP.W9comp.runs_seq r22 (WP.W9comp.runs_seq r23 (WP.W9comp.runs_seq r24 r25)))))))))))))))))))))))
  rw [hA0] at chain
  unfold drvProg
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr chain
    ((congrArg (mk base) hfin).trans (congrArg (fun a => mk base (eV ax ex a)) hRes')))
    (fun _ _ => trivial) ?_
  simp only [drvCost, Nat.add_assoc, le_refl]

end Drv

end SubNLogN.Machine.Bridge.SolveDrvAux
