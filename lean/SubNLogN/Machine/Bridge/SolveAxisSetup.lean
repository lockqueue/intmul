/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveAxisPrims

/-!
# K5-SOLVE driver (3): driver states and the counter setup (`Bridge/SolveAxisSetup.lean`)

* `dV b ax ex arr F0 B0 F1 B1 MU NA GM KM KH`: the tracked stacks in the main phase of the driver
  (the sweep counters hold `natSyms` of `wI, wI, wI+1, wT+1, wI+wT+2, P+2`; `c0` and the
  temporaries are empty), with one update lemma per field;
* `setupP`: the counter setup from the header (`fetchField`, `inc`, `addLoop`), and `runs_setup`:
  from empty private stacks to `dV` (cost `setupCost b`).

All proved (no `sorry`). Helpers live in `SubNLogN.Machine.Bridge.SolveDrvAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveDrvAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability

/-! ## Driver states of the main phase -/

/-- The tracked stacks in the main phase of the driver. -/
def dV (b : BrPar) (ax ex arr F0 B0 F1 B1 MU NA GM KM KH : List Sym) : DX → List Sym
  | .inl .arr => arr
  | .inl .ax => ax
  | .inl .ex => ex
  | .inr .F0 => F0
  | .inr .B0 => B0
  | .inr .F1 => F1
  | .inr .B1 => B1
  | .inr .MU => MU
  | .inr .NA => NA
  | .inr .GM => GM
  | .inr .KM => KM
  | .inr .KH => KH
  | .inr .cwI => natSyms b.wI
  | .inr .cwI2 => natSyms b.wI
  | .inr .cwI1 => natSyms (b.wI + 1)
  | .inr .cwT => natSyms (b.wT + 1)
  | .inr .cwP => natSyms (b.wI + b.wT + 2)
  | .inr .cq => natSyms (b.P + 2)
  | .inr .c0 => []
  | .inr .G => []
  | .inr .TT => []
  | .inr .X => []
  | .inr .TR => []

section Upd

variable (b : BrPar) (ax ex arr F0 B0 F1 B1 MU NA GM KM KH v : List Sym)

theorem upd_arr : Function.update (dV b ax ex arr F0 B0 F1 B1 MU NA GM KM KH) (.inl .arr) v =
    dV b ax ex v F0 B0 F1 B1 MU NA GM KM KH := by
  funext x; rcases x with w | x
  · cases w <;> rfl
  · cases x <;> rfl

theorem upd_F0 : Function.update (dV b ax ex arr F0 B0 F1 B1 MU NA GM KM KH) (.inr .F0) v =
    dV b ax ex arr v B0 F1 B1 MU NA GM KM KH := by
  funext x; rcases x with w | x
  · cases w <;> rfl
  · cases x <;> rfl

theorem upd_B0 : Function.update (dV b ax ex arr F0 B0 F1 B1 MU NA GM KM KH) (.inr .B0) v =
    dV b ax ex arr F0 v F1 B1 MU NA GM KM KH := by
  funext x; rcases x with w | x
  · cases w <;> rfl
  · cases x <;> rfl

theorem upd_F1 : Function.update (dV b ax ex arr F0 B0 F1 B1 MU NA GM KM KH) (.inr .F1) v =
    dV b ax ex arr F0 B0 v B1 MU NA GM KM KH := by
  funext x; rcases x with w | x
  · cases w <;> rfl
  · cases x <;> rfl

theorem upd_B1 : Function.update (dV b ax ex arr F0 B0 F1 B1 MU NA GM KM KH) (.inr .B1) v =
    dV b ax ex arr F0 B0 F1 v MU NA GM KM KH := by
  funext x; rcases x with w | x
  · cases w <;> rfl
  · cases x <;> rfl

theorem upd_MU : Function.update (dV b ax ex arr F0 B0 F1 B1 MU NA GM KM KH) (.inr .MU) v =
    dV b ax ex arr F0 B0 F1 B1 v NA GM KM KH := by
  funext x; rcases x with w | x
  · cases w <;> rfl
  · cases x <;> rfl

theorem upd_NA : Function.update (dV b ax ex arr F0 B0 F1 B1 MU NA GM KM KH) (.inr .NA) v =
    dV b ax ex arr F0 B0 F1 B1 MU v GM KM KH := by
  funext x; rcases x with w | x
  · cases w <;> rfl
  · cases x <;> rfl

theorem upd_GM : Function.update (dV b ax ex arr F0 B0 F1 B1 MU NA GM KM KH) (.inr .GM) v =
    dV b ax ex arr F0 B0 F1 B1 MU NA v KM KH := by
  funext x; rcases x with w | x
  · cases w <;> rfl
  · cases x <;> rfl

theorem upd_KM : Function.update (dV b ax ex arr F0 B0 F1 B1 MU NA GM KM KH) (.inr .KM) v =
    dV b ax ex arr F0 B0 F1 B1 MU NA GM v KH := by
  funext x; rcases x with w | x
  · cases w <;> rfl
  · cases x <;> rfl

theorem upd_KH : Function.update (dV b ax ex arr F0 B0 F1 B1 MU NA GM KM KH) (.inr .KH) v =
    dV b ax ex arr F0 B0 F1 B1 MU NA GM KM v := by
  funext x; rcases x with w | x
  · cases w <;> rfl
  · cases x <;> rfl

end Upd

/-- The tracked stacks with all private stacks empty. -/
def eV (ax ex arr : List Sym) : DX → List Sym
  | .inl .arr => arr
  | .inl .ax => ax
  | .inl .ex => ex
  | .inr _ => []

/-! ## The counter setup -/

section Setup

variable {EP : Type} [DecidableEq EP] {σ : Type} (l : Lens σ (Option Sym))

/-- Fetch header field `j` onto the private stack `x`. -/
def fF (x : DW) (j : ℕ) : Prog (DK EP) (fun _ => Sym) σ :=
  (BridgePP.fetchField (kN .par) (loc (EP := EP) (.inr .G)) (loc (.inr .TT)) (loc (.inr x))
    j).liftRegs l

/-- Increment the private counter `x`. -/
def fI (x : DW) : Prog (DK EP) (fun _ => Sym) σ :=
  (inc (loc (EP := EP) (.inr x)) (loc (.inr .TT))).liftRegs l

/-- `cwP := cwP + X`, `X := 0`. -/
def fAdd : Prog (DK EP) (fun _ => Sym) σ :=
  (addLoop (loc (EP := EP) (.inr .X)) (loc (.inr .cwP)) (loc (.inr .TT))).liftRegs l

/-- The counter setup: `cwI, cwI2 := wI`, `cwI1 := wI+1`, `cwT := wT+1`, `cwP := wI+wT+2`,
`cq := P+2` (header fields `P` = 1, `wI` = 3, `wT` = 4). -/
def setupP : Prog (DK EP) (fun _ => Sym) σ :=
  .seq (fF l .cwI 3) (.seq (fF l .cwI2 3) (.seq (fF l .cwI1 3) (.seq (fI l .cwI1)
  (.seq (fF l .cwT 4) (.seq (fI l .cwT) (.seq (fF l .cwP 3) (.seq (fF l .X 4)
  (.seq (fAdd l) (.seq (fI l .cwP) (.seq (fI l .cwP) (.seq (fF l .cq 1)
  (.seq (fI l .cq) (fI l .cq)))))))))))))

theorem closed_fF (x : DW) (j : ℕ) : (fF (EP := EP) l x j).Closed :=
  WP.W9comp.closed_liftRegs l (BridgePP.closed_fetchField _ _ _ _ j)

theorem closed_fI (x : DW) : (fI (EP := EP) l x).Closed :=
  WP.W9comp.closed_liftRegs l (by
    simp [Prog.Closed, Prog.FreeBelow, inc, incFix, scanLoop, Lib.scanBody, moveBits,
      moveBitsBody, pushC, popR, pushR, peekR, skip, restoreR])

theorem closed_fAdd : (fAdd (EP := EP) l).Closed :=
  WP.W9comp.closed_liftRegs l (by
    simp [Prog.Closed, Prog.FreeBelow, addLoop, addBody, inc, incFix, dec, decFix, scanLoop,
      Lib.scanBody, moveBits, moveBitsBody, pushC, popR, pushR, peekR, skip, restoreR])

theorem closed_setupP : (setupP (EP := EP) l).Closed := by
  simp only [setupP, Prog.Closed, Prog.FreeBelow]
  exact ⟨closed_fF l _ _, closed_fF l _ _, closed_fF l _ _, closed_fI l _, closed_fF l _ _,
    closed_fI l _, closed_fF l _ _, closed_fF l _ _, closed_fAdd l, closed_fI l _, closed_fI l _,
    closed_fF l _ _, closed_fI l _, closed_fI l _⟩

/-- Cost bound of the counter setup. -/
def setupCost (b : BrPar) : ℕ :=
  7 * (9 * (hdrSyms b.hdr).length + 11) + 7 * (6 * bitLen (b.wI + b.wT + 2) + 9) +
    (b.wT * (6 * bitLen (b.wI + b.wT) + 6 * bitLen b.wT + 19) + 2)

/-- **The counter setup** from empty private stacks. -/
theorem runs_setup (b : BrPar) (rpar ax ex arr : List Sym) (base : DK EP → List Sym)
    (hP : b.P + 2 ≤ b.wI) (hpar : base (kN .par) = hdrSyms b.hdr ++ rpar) :
    Runs (setupP l) (mk base (eV ax ex arr))
      (mk base (dV b ax ex arr [] [] [] [] [] [] [] [] [])) (fun _ => True) (setupCost b) := by
  have F : ∀ (W : DX → List Sym) (x : DW), x ≠ .G → x ≠ .TT → W (.inr x) = [] →
      ∀ (fs1 : List ℕ) (a : ℕ) (fs2 : List ℕ), b.hdr = fs1 ++ a :: fs2 →
      Runs ((BridgePP.fetchField (kN .par) (loc (EP := EP) (.inr .G)) (loc (.inr .TT))
          (loc (.inr x)) fs1.length).liftRegs l)
        (mk base W) (mk base (Function.update W (.inr x) (natSyms a))) (fun _ => True)
        (9 * (hdrSyms b.hdr).length + 11) := by
    intro W x hxG hxT hW fs1 a fs2 hh
    have h := runs_fetch l base W x hxG hxT fs1 a fs2 rpar (by rw [hpar, hh])
    rw [hW, List.append_nil, ← hh] at h
    exact h
  have hh3 : b.hdr = [b.p, b.P, b.ω] ++ b.wI ::
      ([b.wT, b.wOut, b.pIn, b.wIn, b.d] ++ List.ofFn b.t) := rfl
  have hh4 : b.hdr = [b.p, b.P, b.ω, b.wI] ++ b.wT ::
      ([b.wOut, b.pIn, b.wIn, b.d] ++ List.ofFn b.t) := rfl
  have hh1 : b.hdr = [b.p] ++ b.P ::
      ([b.ω, b.wI, b.wT, b.wOut, b.pIn, b.wIn, b.d] ++ List.ofFn b.t) := rfl
  set W0 := eV ax ex arr with hW0
  set W1 := Function.update W0 (.inr .cwI) (natSyms b.wI) with hW1
  set W2 := Function.update W1 (.inr .cwI2) (natSyms b.wI) with hW2
  set W3 := Function.update W2 (.inr .cwI1) (natSyms b.wI) with hW3
  set W4 := Function.update W3 (.inr .cwI1) (natSyms (b.wI + 1)) with hW4
  set W5 := Function.update W4 (.inr .cwT) (natSyms b.wT) with hW5
  set W6 := Function.update W5 (.inr .cwT) (natSyms (b.wT + 1)) with hW6
  set W7 := Function.update W6 (.inr .cwP) (natSyms b.wI) with hW7
  set W8 := Function.update W7 (.inr .X) (natSyms b.wT) with hW8
  set W9 := Function.update (Function.update W8 (.inr .X) []) (.inr .cwP)
    (natSyms (b.wI + b.wT)) with hW9
  set W10 := Function.update W9 (.inr .cwP) (natSyms (b.wI + b.wT + 1)) with hW10
  set W11 := Function.update W10 (.inr .cwP) (natSyms (b.wI + b.wT + 2)) with hW11
  set W12 := Function.update W11 (.inr .cq) (natSyms b.P) with hW12
  set W13 := Function.update W12 (.inr .cq) (natSyms (b.P + 1)) with hW13
  set W14 := Function.update W13 (.inr .cq) (natSyms (b.P + 2)) with hW14
  have r1 : Runs (fF l .cwI 3) (mk base W0) (mk base W1) (fun _ => True)
      (9 * (hdrSyms b.hdr).length + 11) := F W0 .cwI (by decide) (by decide) rfl _ _ _ hh3
  have r2 : Runs (fF l .cwI2 3) (mk base W1) (mk base W2) (fun _ => True)
      (9 * (hdrSyms b.hdr).length + 11) :=
    F W1 .cwI2 (by decide) (by decide) (by simp [hW1, hW0, eV, Function.update_apply]) _ _ _ hh3
  have r3 : Runs (fF l .cwI1 3) (mk base W2) (mk base W3) (fun _ => True)
      (9 * (hdrSyms b.hdr).length + 11) :=
    F W2 .cwI1 (by decide) (by decide) (by simp [hW2, hW1, hW0, eV, Function.update_apply])
      _ _ _ hh3
  have r4 : Runs (fI l .cwI1) (mk base W3) (mk base W4) (fun _ => True) (6 * bitLen b.wI + 9) :=
    runs_inc l base W3 .cwI1 (by decide) b.wI (by simp [hW3])
  have r5 : Runs (fF l .cwT 4) (mk base W4) (mk base W5) (fun _ => True)
      (9 * (hdrSyms b.hdr).length + 11) :=
    F W4 .cwT (by decide) (by decide)
      (by simp [hW4, hW3, hW2, hW1, hW0, eV, Function.update_apply]) _ _ _ hh4
  have r6 : Runs (fI l .cwT) (mk base W5) (mk base W6) (fun _ => True) (6 * bitLen b.wT + 9) :=
    runs_inc l base W5 .cwT (by decide) b.wT (by simp [hW5])
  have r7 : Runs (fF l .cwP 3) (mk base W6) (mk base W7) (fun _ => True)
      (9 * (hdrSyms b.hdr).length + 11) :=
    F W6 .cwP (by decide) (by decide)
      (by simp [hW6, hW5, hW4, hW3, hW2, hW1, hW0, eV, Function.update_apply]) _ _ _ hh3
  have r8 : Runs (fF l .X 4) (mk base W7) (mk base W8) (fun _ => True)
      (9 * (hdrSyms b.hdr).length + 11) :=
    F W7 .X (by decide) (by decide)
      (by simp [hW7, hW6, hW5, hW4, hW3, hW2, hW1, hW0, eV, Function.update_apply]) _ _ _ hh4
  have r9 : Runs (fAdd l) (mk base W8) (mk base W9) (fun _ => True)
      (b.wT * (6 * bitLen (b.wI + b.wT) + 6 * bitLen b.wT + 19) + 2) :=
    runs_add l base W8 .X .cwP (by decide) (by decide) (by decide) b.wT b.wI (by simp [hW8])
      (by simp [hW8, hW7, Function.update_apply])
  have r10 : Runs (fI l .cwP) (mk base W9) (mk base W10) (fun _ => True)
      (6 * bitLen (b.wI + b.wT) + 9) :=
    runs_inc l base W9 .cwP (by decide) (b.wI + b.wT) (by simp [hW9])
  have r11 : Runs (fI l .cwP) (mk base W10) (mk base W11) (fun _ => True)
      (6 * bitLen (b.wI + b.wT + 1) + 9) :=
    runs_inc l base W10 .cwP (by decide) (b.wI + b.wT + 1) (by simp [hW10])
  have r12 : Runs (fF l .cq 1) (mk base W11) (mk base W12) (fun _ => True)
      (9 * (hdrSyms b.hdr).length + 11) :=
    F W11 .cq (by decide) (by decide)
      (by simp [hW11, hW10, hW9, hW8, hW7, hW6, hW5, hW4, hW3, hW2, hW1, hW0, eV,
        Function.update_apply]) _ _ _ hh1
  have r13 : Runs (fI l .cq) (mk base W12) (mk base W13) (fun _ => True) (6 * bitLen b.P + 9) :=
    runs_inc l base W12 .cq (by decide) b.P (by simp [hW12])
  have r14 : Runs (fI l .cq) (mk base W13) (mk base W14) (fun _ => True)
      (6 * bitLen (b.P + 1) + 9) :=
    runs_inc l base W13 .cq (by decide) (b.P + 1) (by simp [hW13])
  have hfin : W14 = dV b ax ex arr [] [] [] [] [] [] [] [] [] := by
    funext x
    rcases x with w | x
    · cases w <;> simp [hW14, hW13, hW12, hW11, hW10, hW9, hW8, hW7, hW6, hW5, hW4, hW3, hW2,
        hW1, hW0, eV, dV, Function.update_apply]
    · cases x <;> simp [hW14, hW13, hW12, hW11, hW10, hW9, hW8, hW7, hW6, hW5, hW4, hW3, hW2,
        hW1, hW0, eV, dV, Function.update_apply]
  rw [← hfin]
  unfold setupP
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3 (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6
    (WP.W9comp.runs_seq r7 (WP.W9comp.runs_seq r8 (WP.W9comp.runs_seq r9 (WP.W9comp.runs_seq r10 (WP.W9comp.runs_seq r11 (WP.W9comp.runs_seq r12
    (WP.W9comp.runs_seq r13 r14))))))))))))) (fun _ _ => trivial) ?_
  have hb1 : bitLen b.wI ≤ bitLen (b.wI + b.wT + 2) := bitLen_mono_d (by omega)
  have hb2 : bitLen b.wT ≤ bitLen (b.wI + b.wT + 2) := bitLen_mono_d (by omega)
  have hb3 : bitLen (b.wI + b.wT) ≤ bitLen (b.wI + b.wT + 2) := bitLen_mono_d (by omega)
  have hb4 : bitLen (b.wI + b.wT + 1) ≤ bitLen (b.wI + b.wT + 2) := bitLen_mono_d (by omega)
  have hb5 : bitLen b.P ≤ bitLen (b.wI + b.wT + 2) := bitLen_mono_d (by omega)
  have hb6 : bitLen (b.P + 1) ≤ bitLen (b.wI + b.wT + 2) := bitLen_mono_d (by omega)
  unfold setupCost
  omega

end Setup

end SubNLogN.Machine.Bridge.SolveDrvAux
