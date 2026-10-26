/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreKCore
import SubNLogN.Machine.Layer.DrvPreKRot
import SubNLogN.Machine.Arith.CAdd
import SubNLogN.Machine.Arith.Shift
import SubNLogN.Machine.K1.DistributeBlk

/-!
# Driver pre-phase: the individual kernel pass (`Machine/Layer/DrvPreK.lean`)

**Scope (honest summary).** `drvCKernel_holds : DrvCKernelStmt` (no hypotheses): the
individual-kernel pass `DrvCKernelStmt` (`Machine/Layer/DrvPreDefs.lean`). It is
`drvCKernel_of rotIPow_holds`, where `drvCKernel_of (hRot : RotIPowStmt) : DrvCKernelStmt` uses the
rotation kernel `RotIPowStmt` (`Machine/Layer/DrvPreKDefs.lean`, proved as `rotIPow_holds` in
`Machine/Layer/DrvPreKRot.lean`) and the proved kernels `k2DistributeBlk_holds 2`,
`k2MergeBlk_holds 2 (Equiv.refl _)`, `cAdd_holds`, `cSub_holds`, `truncShift_holds`.

## Program (`kernelProg`)
A `mark` guard on every own stack (`protectAllCall`), then (`bodyProg`): the counters
(`setupProg`); the cyclic distribution of the rows of `W` records into the halves `U`, `V`
(`K2DistributeBlk 2`); the arithmetic core (`coreProg`, `Machine/Layer/DrvPreKCore.lean`); the merge
of the output streams `C0`, `C1` back onto the array stack (`K2MergeBlk 2`); the counters removed
(`tearProg`). Cost `C·(cvol w X + w + 1)` for the array `X`, which is within the contract's
`C·(V + N·(bitLen W + 1) + w + 1)`.
-/

-- `DecidableEq` of the nested sum of all scratch types exceeds the default instance size.
set_option synthInstance.maxSize 4096

namespace SubNLogN.Machine.Layer.DrvPreK

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability

/-- The sub-kernels' scratch. -/
abbrev ZZ (Ed Em Ea Es Er Et : Type) : Type := Ed ⊕ (Em ⊕ (Ea ⊕ (Es ⊕ (Er ⊕ Et))))

/-- The registers: `Option Sym` for the own steps, then the sub-kernels' registers. -/
abbrev RG (Rd Rm Ra Rs Rr Rt : Type) : Type :=
  Option Sym × (Rd × (Rm × (Ra × (Rs × (Rr × Rt)))))

section Body

variable {Ed Em Ea Es Er Et Rd Rm Ra Rs Rr Rt : Type} [DecidableEq Ed] [DecidableEq Em]
  [DecidableEq Ea] [DecidableEq Es] [DecidableEq Er] [DecidableEq Et]

/-- Lenses of the registers. -/
def lO' : Lens (RG Rd Rm Ra Rs Rr Rt) (Option Sym) := Lens.fst _ _
def ld' : Lens (RG Rd Rm Ra Rs Rr Rt) Rd := (Lens.snd _ _).comp (Lens.fst _ _)
def lm' : Lens (RG Rd Rm Ra Rs Rr Rt) Rm :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def la' : Lens (RG Rd Rm Ra Rs Rr Rt) Ra :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def ls' : Lens (RG Rd Rm Ra Rs Rr Rt) Rs :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
def lr' : Lens (RG Rd Rm Ra Rs Rr Rt) Rr :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))
def lt' : Lens (RG Rd Rm Ra Rs Rr Rt) Rt :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.snd _ _)))))

/-- Injections of the sub-kernels' scratch. -/
def jd' : Ed → ZZ Ed Em Ea Es Er Et := Sum.inl
def jm' : Em → ZZ Ed Em Ea Es Er Et := fun e => .inr (.inl e)
def ja' : Ea → ZZ Ed Em Ea Es Er Et := fun e => .inr (.inr (.inl e))
def js' : Es → ZZ Ed Em Ea Es Er Et := fun e => .inr (.inr (.inr (.inl e)))
def jr' : Er → ZZ Ed Em Ea Es Er Et := fun e => .inr (.inr (.inr (.inr (.inl e))))
def jt' : Et → ZZ Ed Em Ea Es Er Et := fun e => .inr (.inr (.inr (.inr (.inr e))))

theorem jd'_inj : Function.Injective (jd' (Ed := Ed) (Em := Em) (Ea := Ea) (Es := Es) (Er := Er)
    (Et := Et)) := fun _ _ h => by simpa [jd'] using h
theorem jm'_inj : Function.Injective (jm' (Ed := Ed) (Em := Em) (Ea := Ea) (Es := Es) (Er := Er)
    (Et := Et)) := fun _ _ h => by simpa [jm'] using h
theorem ja'_inj : Function.Injective (ja' (Ed := Ed) (Em := Em) (Ea := Ea) (Es := Es) (Er := Er)
    (Et := Et)) := fun _ _ h => by simpa [ja'] using h
theorem js'_inj : Function.Injective (js' (Ed := Ed) (Em := Em) (Ea := Ea) (Es := Es) (Er := Er)
    (Et := Et)) := fun _ _ h => by simpa [js'] using h
theorem jr'_inj : Function.Injective (jr' (Ed := Ed) (Em := Em) (Ea := Ea) (Es := Es) (Er := Er)
    (Et := Et)) := fun _ _ h => by simpa [jr'] using h
theorem jt'_inj : Function.Injective (jt' (Ed := Ed) (Em := Em) (Ea := Ea) (Es := Es) (Er := Er)
    (Et := Et)) := fun _ _ h => by simpa [jt'] using h

variable (Pd : Prog (KLoc (Fin 2 ⊕ Fin 2) Ed) (fun _ => Sym) Rd)
  (Pm : Prog (KLoc (Fin 2 ⊕ Fin 2) Em) (fun _ => Sym) Rm)
  (Pa : Prog (KLoc (Fin 6) Ea) (fun _ => Sym) Ra) (Ps : Prog (KLoc (Fin 6) Es) (fun _ => Sym) Rs)
  (Pr : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr) (Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt)

/-- The body: counters, distribution, arithmetic core, merge, counters removed. -/
def bodyProg : Prog (KK (ZZ Ed Em Ea Es Er Et)) (fun _ => Sym) (RG Rd Rm Ra Rs Rr Rt) :=
  ((((setupProg lO').seq (callInj (embR .U .V jd') ld' Pd)).seq
    (coreProg lO' ja' la' Pa js' ls' Ps jr' lr' Pr jt' lt' Pt)).seq
    (callInj (embR .C0 .C1 jm') lm' Pm)).seq (tearProg lO')

/-- **The kernel**: the body with a `mark` guard on every own stack. -/
def kernelProg : Prog (KK (ZZ Ed Em Ea Es Er Et)) (fun _ => Sym) (RG Rd Rm Ra Rs Rr Rt) :=
  protectAllCall lO' (KS.all.map ds) (bodyProg Pd Pm Pa Ps Pr Pt)

theorem closed_kernelProg (hPd : Pd.Closed) (hPm : Pm.Closed) (hPa : Pa.Closed)
    (hPs : Ps.Closed) (hPr : Pr.Closed) (hPt : Pt.Closed) :
    (kernelProg Pd Pm Pa Ps Pr Pt).Closed :=
  closed_protectAllCall _ _ ⟨⟨⟨⟨closed_setupProg _, closed_callInj _ _ hPd⟩,
    closed_coreProg _ _ _ _ _ _ _ _ _ hPa hPs hPr hPt⟩, closed_callInj _ _ hPm⟩,
    closed_tearProg _⟩

variable {Pd Pm Pa Ps Pr Pt}

theorem runs_body {Cd Cm Ca Cs Cr Ct : ℕ} (hD : DSpec Ed Rd Cd Pd) (hM : MSpec Em Rm Cm Pm)
    (hA : BinSpec caddC Ea Ra Ca Pa) (hS : BinSpec csubC Es Rs Cs Ps) (hR : RSpec 1 Er Rr Cr Pr)
    (hT : TSpec Et Rt Ct Pt) (W w : ℕ) (blks : List (List (List CInt))) (rest r1 r2 : List Sym)
    (S : KK (ZZ Ed Em Ea Es Er Et) → List Sym) (hw : 1 ≤ w)
    (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) (hfit : CArrFits w blks.flatten)
    (hfit' : CArrFits w (blks.map (cgateBlock W)).flatten) (hrest : BlkTerm rest)
    (hr1 : TermOK r1) (hr2 : TermOK r2) (hS1 : S (.inl 1) = natSyms W ++ r1)
    (hS2 : S (.inl 2) = natSyms w ++ r2) :
    Runs (bodyProg Pd Pm Pa Ps Pr Pt) (st S (carrSyms w blks.flatten ++ rest) (fun _ => []))
      (st S (carrSyms w (blks.map (cgateBlock W)).flatten ++ rest) (fun _ => []))
      (fun _ => True)
      ((120 + Cd + 2 * Cm + (70 + 11 * Ca + 11 * Cs + 2 * Cr + 8 * Ct)) *
        (cvol w blks.flatten + w + 1)) := by
  have hal := aligned_halves hblk
  have hu : cvol w (halvesU W blks) ≤ cvol w blks.flatten := by
    have := cvol_halves (W := W) (blks := blks) w; omega
  have hc0 : cvol w (zipC cgate0 (halvesU W blks) (halvesV W blks)) = cvol w (halvesU W blks) :=
    cvol_zipC _ _ _ _ hal
  have hc1 : cvol w (zipC cgate1 (halvesU W blks) (halvesV W blks)) = cvol w (halvesU W blks) :=
    cvol_zipC _ _ _ _ hal
  have e1 := runs_setup (lO' : Lens (RG Rd Rm Ra Rs Rr Rt) (Option Sym)) S (carrSyms w blks.flatten ++ rest) w r2 hr2 hS2
  have e2 := runsSeq e1 (runs_distCall hD jd'_inj (ld' : Lens (RG Rd Rm Ra Rs Rr Rt) Rd) S (ctrPre w) W w blks rest r1 hblk hrest hr1
    hS1 (by simp [ctrPre]) (by simp [ctrPre]))
  have e3 := runsSeq e2 (runs_core (lO' : Lens (RG Rd Rm Ra Rs Rr Rt) (Option Sym)) ja'_inj (la' : Lens (RG Rd Rm Ra Rs Rr Rt) Ra) hA js'_inj
    (ls' : Lens (RG Rd Rm Ra Rs Rr Rt) Rs) hS jr'_inj (lr' : Lens (RG Rd Rm Ra Rs Rr Rt) Rr) hR jt'_inj (lt' : Lens (RG Rd Rm Ra Rs Rr Rt) Rt) hT
    S rest w hw (halvesU W blks) (halvesV W blks) (fits_halvesU hfit) (fits_halvesV hfit) hal
    (fits_zip0 hblk hfit') (fits_zip1 hblk hfit'))
  have e4 := runsSeq e3 (runs_mergeCall hM jm'_inj (lm' : Lens (RG Rd Rm Ra Rs Rr Rt) Rm) S rest _ W w blks r1 hblk hr1 hS1
    (by simp [Function.update_apply]) (by simp [Function.update_apply]))
  have e4' := runsCongr e4 (congrArg (st S _) (funext fun d => by
    cases d <;> simp [Function.update_apply, ctrPre]) :
      _ = st S (carrSyms w (blks.map (cgateBlock W)).flatten ++ rest) (ctrPre w))
  have e5 := runsSeq e4' (runs_tear (lO' : Lens (RG Rd Rm Ra Rs Rr Rt) (Option Sym)) S (carrSyms w (blks.map (cgateBlock W)).flatten ++ rest) w)
  refine runsMono e5 (fun _ _ => trivial) ?_
  rw [hc0, hc1]
  have t1 : Cd * (cvol w blks.flatten + 1) ≤ Cd * (cvol w blks.flatten + w + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have t2 : (70 + 11 * Ca + 11 * Cs + 2 * Cr + 8 * Ct) * (cvol w (halvesU W blks) + w + 1) ≤
      (70 + 11 * Ca + 11 * Cs + 2 * Cr + 8 * Ct) * (cvol w blks.flatten + w + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have t3 : Cm * (cvol w (halvesU W blks) + cvol w (halvesU W blks) + 1) ≤
      Cm * (2 * (cvol w blks.flatten + w + 1)) := Nat.mul_le_mul_left _ (by omega)
  nlinarith [t1, t2, t3]

theorem protState_eq (S : KK (ZZ Ed Em Ea Es Er Et) → List Sym) :
    protState (KS.all.map ds) S = st S (S (.inl 0)) (fun _ => []) := by
  funext k
  rcases k with i | d | z
  · by_cases h : i = 0
    · subst h; simp [protState, st]
    · simp [protState, st, h]
  · simp [protState, st, KS.mem_all]
  · simp [protState, st]

theorem runs_kernel {Cd Cm Ca Cs Cr Ct : ℕ} (hD : DSpec Ed Rd Cd Pd) (hM : MSpec Em Rm Cm Pm)
    (hA : BinSpec caddC Ea Ra Ca Pa) (hS : BinSpec csubC Es Rs Cs Ps) (hR : RSpec 1 Er Rr Cr Pr)
    (hT : TSpec Et Rt Ct Pt) (W w : ℕ) (blks : List (List (List CInt))) (rest r1 r2 : List Sym)
    (S : KK (ZZ Ed Em Ea Es Er Et) → List Sym) (hw : 1 ≤ w)
    (hblk : ∀ blk ∈ blks, CGateBlockOK W blk) (hfit : CArrFits w blks.flatten)
    (hfit' : CArrFits w (blks.map (cgateBlock W)).flatten) (hrest : BlkTerm rest)
    (hr1 : TermOK r1) (hr2 : TermOK r2) (hS0 : S (.inl 0) = carrSyms w blks.flatten ++ rest)
    (hS1 : S (.inl 1) = natSyms W ++ r1) (hS2 : S (.inl 2) = natSyms w ++ r2) :
    Runs (kernelProg Pd Pm Pa Ps Pr Pt) S
      (Function.update S (.inl 0) (carrSyms w (blks.map (cgateBlock W)).flatten ++ rest))
      (fun _ => True)
      ((120 + Cd + 2 * Cm + (70 + 11 * Ca + 11 * Cs + 2 * Cr + 8 * Ct) + 42) *
        (cvol w blks.flatten + blks.flatten.length * (bitLen W + 1) + w + 1)) := by
  have hb := runs_body hD hM hA hS hR hT W w blks rest r1 r2 S hw hblk hfit hfit' hrest hr1 hr2
    hS1 hS2
  rw [← hS0, ← protState_eq] at hb
  have hnd : (KS.all.map (ds (Z := ZZ Ed Em Ea Es Er Et))).Nodup :=
    KS.nodup_all.map (fun a b h => by simpa using h)
  have hp := runsIn_protectAllCall (ρ := []) (lO' : Lens (RG Rd Rm Ra Rs Rr Rt) (Option Sym)) hnd (RunsIn.iff_runs.mpr hb) (fun k hk => by
    obtain ⟨d, _, rfl⟩ := List.mem_map.1 hk
    simp)
  refine runsMono (runsCongr (RunsIn.iff_runs.mp hp) ?_) (fun _ _ => trivial) ?_
  · funext k
    rcases k with i | d | z
    · by_cases h : i = 0
      · subst h; simp [st]
      · simp [st, h, Function.update_apply]
    · simp [st, KS.mem_all, Function.update_apply]
    · simp [st, Function.update_apply]
  · have hlen : (KS.all.map (ds (Z := ZZ Ed Em Ea Es Er Et))).length = 20 := rfl
    rw [hlen]
    nlinarith [Nat.zero_le (blks.flatten.length * (bitLen W + 1))]

end Body

/-- **The individual kernel pass** (`DrvCKernelStmt`), from the rotation kernel. -/
theorem drvCKernel_of (hRot : RotIPowStmt) : DrvCKernelStmt := by
  obtain ⟨Cd, hd⟩ := k2DistributeBlk_holds 2
  obtain ⟨Ed, _, _, Rd, Pd, _, _, hPd, hD⟩ := hd ()
  obtain ⟨Cm, hm⟩ := k2MergeBlk_holds 2 (Equiv.refl (Fin 2))
  obtain ⟨Em, _, _, Rm, Pm, _, _, hPm, hM⟩ := hm ()
  obtain ⟨Ca, ha⟩ := Arith.cAdd_holds
  obtain ⟨Ea, _, _, Ra, Pa, _, _, hPa, hA⟩ := ha ()
  obtain ⟨Cs, hs⟩ := Arith.cSub_holds
  obtain ⟨Es, _, _, Rs, Ps, _, _, hPs, hS⟩ := hs ()
  obtain ⟨Cr, hr⟩ := hRot
  obtain ⟨Er, _, _, Rr, Pr, _, _, hPr, hR⟩ := hr 1
  obtain ⟨Ct, ht⟩ := Arith.truncShift_holds
  obtain ⟨Et, _, _, Rt, Pt, _, _, hPt, hT⟩ := ht ()
  refine ⟨120 + Cd + 2 * Cm + (70 + 11 * Ca + 11 * Cs + 2 * Cr + 8 * Ct) + 42, fun _ => ?_⟩
  refine ⟨KS ⊕ ZZ Ed Em Ea Es Er Et, inferInstance, inferInstance, RG Rd Rm Ra Rs Rr Rt,
    kernelProg Pd Pm Pa Ps Pr Pt, inferInstance, inferInstance,
    closed_kernelProg Pd Pm Pa Ps Pr Pt hPd hPm hPa hPs hPr hPt, ?_⟩
  intro W w blks rest r1 r2 S _ hw hblk hfit hfit' hrest hr1 hr2 hS0 hS1 hS2
  exact runs_kernel hD hM hA hS hR hT W w blks rest r1 r2 S hw hblk hfit hfit' hrest hr1 hr2 hS0
    hS1 hS2

/-- **`DrvCKernelStmt` holds**: the individual kernel pass, with no hypothesis. -/
theorem drvCKernel_holds : DrvCKernelStmt := drvCKernel_of rotIPow_holds

end SubNLogN.Machine.Layer.DrvPreK
