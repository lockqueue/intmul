/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafKernelCost
import SubNLogN.Machine.CCore.MathM6
import SubNLogN.Machine.Layer.DrvPreK

/-!
# C-core leaf kernel: `LeafStmt` (`CCore/LeafKernel.lean`)

**Theorem** `leaf_of_cost p βn βd (hcost : LeafCostStmt p) : LeafStmt p βn βd`. The only hypothesis
is the pure cost inequality `LeafCostStmt p` (`CCore/LeafKernelCost.lean`); the kernels are the
proved `Layer.DrvPreK.drvCKernel_holds` (DrvC), `WP.Inst.shlVar.ok`, `WP.Inst.shrVar.ok`,
`WP.Inst.decNat.ok`, and the encoding bound is `encLen_holds`.

Proof: the inner program (`innerP`, `CCore/LeafKernelProg.lean`) runs from the entry state
(restricted along `ιO`) through phases H, A, L, C (`runs_phaseH`, `runs_phaseA`, `runs_phaseL`,
`runs_phaseC`) to the entry state with the array replaced by `Enc t (gatesR ρ j0 e z)`, which is
`Enc t (cCoreVal …)` (`gatesR_eq_cCoreVal`). `callInj` embeds it (`runs_callInj`), and since the
leaf program reads only unframed stacks (`readsIn_leafProg`), `SafeRunsIn.of_runs_readsIn` gives the
boundary-safe run.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability
open SubNLogN.Math.Walsh
open LeafKernelAux

/-- **`LeafStmt` from the leaf cost inequality.** -/
theorem leaf_of_cost (p : LayerParams) (βn βd : ℕ) (hcost : LeafCostStmt p) :
    LeafStmt p βn βd := by
  obtain ⟨P₀e, henc⟩ := encLen_holds p
  obtain ⟨Cc, hC⟩ := Layer.DrvPreK.drvCKernel_holds
  obtain ⟨C1, h1⟩ := WP.Inst.shlVar.ok
  obtain ⟨C2, h2⟩ := WP.Inst.shrVar.ok
  obtain ⟨C3, h3⟩ := WP.Inst.decNat.ok
  obtain ⟨P₀c, Ccost, hcb⟩ := hcost C1 C2 C3 Cc
  obtain ⟨Ec, _, _, Rc, Pc, hRc1, hRc2, hPc, hsC⟩ := hC ()
  obtain ⟨m1, R1, -, P1, -, hR11, hR12, hP1, hs1⟩ := h1 ()
  obtain ⟨m2, R2, -, P2, -, hR21, hR22, hP2, hs2⟩ := h2 ()
  obtain ⟨m3, R3, -, P3, -, hR31, hR32, hP3, hs3⟩ := h3 ()
  have := hRc1; have := hRc2; have := hR11; have := hR12
  have := hR21; have := hR22; have := hR31; have := hR32
  refine ⟨max P₀e P₀c, Ccost, fun _ => ⟨EL Ec m1 m2 m3, inferInstance, inferInstance,
    σL Rc R1 R2 R3, leafProg Pc P1 P2 P3, inferInstance, inferInstance,
    closed_leafProg hPc hP1 hP2 hP3, ?_⟩⟩
  intro t hA hS hρ hg z tio tdesc S hband hgrowth hdepth _hleaf htio hio hdesc _hframed hclean
  have hbe : CCoreBands p P₀e t := ⟨le_trans (le_max_left _ _) hband.1, hband.2⟩
  have hbc : CCoreBands p P₀c t := ⟨le_trans (le_max_right _ _) hband.1, hband.2⟩
  have he1 : 1 ≤ t.e := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by norm_num [tripleM]))
  have hjD : t.j0 < t.D := by omega
  refine SafeRunsIn.of_runs_readsIn ?_ (closed_leafProg hPc hP1 hP2 hP3)
    (readsIn_leafProg Pc P1 P2 P3) []
  -- the inner entry state
  have hSIsc : ∀ i, (S ∘ ιO Ec m1 m2 m3) (sc i) = [] := fun i => hclean (.inl i)
  have hSIsc' : ∀ i : Fin NS, S (ιO Ec m1 m2 m3 (Sum.inr (Sum.inl i))) = [] :=
    fun i => hclean (.inl i)
  have hSIds : (S ∘ ιO Ec m1 m2 m3) dsI =
      W9.hdrSyms [t.P, t.d, t.r, t.Δ, t.A, t.R, t.K, t.D, t.S, t.j0, t.k, t.ρ] ++ tdesc := hdesc
  have hH := runs_phaseH (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3) (S ∘ ιO Ec m1 m2 m3)
    t.P t.d t.r t.Δ t.A t.R t.K t.D t.S t.j0 t.k t.ρ tdesc hSIds hSIsc
  have hA' := runs_phaseA (m2 := m2) (Rc := Rc) (R2 := R2) hs1 hs3 (S ∘ ιO Ec m1 m2 m3)
    t.P t.Δ t.K t.D t.S t.j0 t.k t.ρ hjD hSIsc
  -- the state after phase A
  have h3io : stA (S ∘ ιO Ec m1 m2 m3) t.K (t.P + t.Δ + (t.Δ + 3)) (1 * mn ^ t.k)
      (t.S * 2 ^ (t.ρ + t.K * (t.D - t.j0 - 1))) ioI =
      ioFun t.P t.Δ hA hS ⟨t.ρ, hρ⟩ t.j0 z tio 0 := by
    simp [stA, ioFun, gatesUpTo_zero, ιO, hio, Enc, CCoreRT.wg]
  have h3Ct : stA (S ∘ ιO Ec m1 m2 m3) t.K (t.P + t.Δ + (t.Δ + 3)) (1 * mn ^ t.k)
      (t.S * 2 ^ (t.ρ + t.K * (t.D - t.j0 - 1))) (sc iCt) = natSyms t.e := by
    simp [stA, CCoreRT.e, mn]
  have h3W : stA (S ∘ ιO Ec m1 m2 m3) t.K (t.P + t.Δ + (t.Δ + 3)) (1 * mn ^ t.k)
      (t.S * 2 ^ (t.ρ + t.K * (t.D - t.j0 - 1))) (sc iW) =
      natSyms (wSel t.K t.D t.S (⟨t.ρ, hρ⟩ : Fin t.K) t.j0) := by
    simp only [stA, Function.update_self]
    rw [show t.D - t.j0 - 1 = t.D - 1 - t.j0 by omega]
    rfl
  have h3Wg : stA (S ∘ ιO Ec m1 m2 m3) t.K (t.P + t.Δ + (t.Δ + 3)) (1 * mn ^ t.k)
      (t.S * 2 ^ (t.ρ + t.K * (t.D - t.j0 - 1))) (sc iWg) = natSyms (t.P + 2 * t.Δ + 3) := by
    have e1 : t.P + t.Δ + (t.Δ + 3) = t.P + 2 * t.Δ + 3 := by ring
    simp [stA, e1]
  have h3K : stA (S ∘ ιO Ec m1 m2 m3) t.K (t.P + t.Δ + (t.Δ + 3)) (1 * mn ^ t.k)
      (t.S * 2 ^ (t.ρ + t.K * (t.D - t.j0 - 1))) (sc iK) = natSyms t.K := by
    simp [stA]
  have hV1 : ∀ i ≤ t.e, cvol (t.P + 2 * t.Δ + 3) (encArr (t.P + t.Δ)
      (layerAddrs t.A t.K t.D t.S hA hS) (gatesUpTo ⟨t.ρ, hρ⟩ t.j0 z i)) ≤ 2 * t.volG := by
    intro i _
    have h := henc t hA hS (gatesUpTo ⟨t.ρ, hρ⟩ t.j0 z i) hbe
    simp only [Enc, CCoreRT.wg] at h
    unfold cvol
    omega
  have hL := runs_phaseL (m1 := m1) (R1 := R1) hsC hs2 hs3 hA hS t.P t.Δ t.b ⟨t.ρ, hρ⟩ t.j0 t.e hg
    z tio htio hgrowth (by omega) (2 * t.volG) hV1 _ h3io h3Ct h3W h3Wg h3K
  have nWgW : (sc iWg : LI Ec m1 m2 m3) ≠ sc iW := by simp
  have nWgC : (sc iWg : LI Ec m1 m2 m3) ≠ sc iCt := by simp
  have nWgI : (sc iWg : LI Ec m1 m2 m3) ≠ ioI := by simp
  have nKW : (sc iK : LI Ec m1 m2 m3) ≠ sc iW := by simp
  have nKC : (sc iK : LI Ec m1 m2 m3) ≠ sc iCt := by simp
  have nKI : (sc iK : LI Ec m1 m2 m3) ≠ ioI := by simp
  have hC' := runs_phaseC (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3)
    (stL (stA (S ∘ ιO Ec m1 m2 m3) t.K (t.P + t.Δ + (t.Δ + 3)) (1 * mn ^ t.k)
      (t.S * 2 ^ (t.ρ + t.K * (t.D - t.j0 - 1))))
      (ioFun t.P t.Δ hA hS ⟨t.ρ, hρ⟩ t.j0 z tio) (wFun t.K t.D t.S t.ρ t.j0) t.e 0)
    (wFun t.K t.D t.S t.ρ t.j0 t.e) (t.P + 2 * t.Δ + 3) t.K (by simp [stL])
    (by simp only [stL, Function.update_of_ne nWgW, Function.update_of_ne nWgC,
          Function.update_of_ne nWgI]; exact h3Wg)
    (by simp only [stL, Function.update_of_ne nKW, Function.update_of_ne nKC,
          Function.update_of_ne nKI]; exact h3K)
  have hin := WP.W9comp.runs_seq hH (WP.W9comp.runs_seq hA' (WP.W9comp.runs_seq hL hC'))
  have hval : gatesUpTo ⟨t.ρ, hρ⟩ t.j0 z t.e = SubNLogN.Math.Networks.cCoreVal ⟨t.ρ, hρ⟩ t.j0 t.e hg z := by
    rw [gatesUpTo_eq _ _ _ hg, gatesR_eq_cCoreVal]
  have hfin := WP.W9comp.runs_congr hin (S'' := Function.update (S ∘ ιO Ec m1 m2 m3) ioI
    (Enc t hA hS (SubNLogN.Math.Networks.cCoreVal ⟨t.ρ, hρ⟩ t.j0 t.e hg z) ++ tio)) (by
      funext x
      rcases x with i | i | e
      · fin_cases i
        · simp [stL, ioFun, hval, Enc, CCoreRT.wg]
        · simp [stL, stA]
      · fin_cases i <;> simp +decide [stL, stA, hSIsc', NatArith.natSyms_zero, Function.update_apply]
      · simp [stL, stA])
  exact WP.W9comp.runs_mono
    (runs_inj_upd1 (ιO_inj Ec m1 m2 m3) (lensId _) S (.inl 0) _ hfin)
    (fun _ _ => trivial) (hcb t hA hS hρ hg hbc)

end SubNLogN.Machine.CCore
