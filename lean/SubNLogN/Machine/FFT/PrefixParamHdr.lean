/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixParamKit
import SubNLogN.Machine.FFT.TwiddleHdr

/-!
# K4-PREFIX parameter phase: reading the header (`Machine/FFT/PrefixParamHdr.lean`)

**Scope (honest summary).** A generic routine `prmHdr` (any stack type, registers through a lens):
from the header `midHdr q ℓ K w a` it copies `D`, `ℓ`, `K`, `w` (binary) onto four private stacks
and `w` once more onto an output stack; the fields `q, D, ℓ, K` in front of `w` are parked on `PK`
one by one and moved back, so the header is restored and every skipped field is paid
(cost `≤ 27·|midHdr|`). Proved, no `sorry`.
-/

namespace SubNLogN.Machine.FFT.PrefixParamAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine SubNLogN.Machine.FFT.DIF
  SubNLogN.Machine.FFT.TwiddleAux

theorem midHdr_split5 {D : ℕ} (q ℓ Kp w : ℕ) (a : Fin D → ℕ) (hrest : List Sym) :
    midHdr q ℓ Kp w a ++ hrest = natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark ::
      (natSyms ℓ ++ Sym.mark :: (natSyms Kp ++ Sym.mark ::
        (natSyms w ++ Sym.mark :: (W9.hdrSyms (List.ofFn a) ++ hrest))))) := by
  simp [midHdr, W9.hdrSyms]

section Hdr

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- Read `D, ℓ, K, w` from the header (`w` twice); the header is restored. -/
def prmHdr (HDR PK TC BD BL BK BW O5 : K) : Prog K (fun _ => Sym) σ :=
  .seq ((Calculus.moveFieldTo HDR PK).liftRegs lO)
  (.seq (copyBits lO HDR BD TC)
  (.seq ((Calculus.moveFieldTo HDR PK).liftRegs lO)
  (.seq (copyBits lO HDR BL TC)
  (.seq ((Calculus.moveFieldTo HDR PK).liftRegs lO)
  (.seq (copyBits lO HDR BK TC)
  (.seq ((Calculus.moveFieldTo HDR PK).liftRegs lO)
  (.seq (copyBits lO HDR BW TC)
  (.seq (copyBits lO HDR O5 TC)
    ((forEachRange 4 (fun _ => Calculus.moveFieldBack PK HDR)).liftRegs lO)))))))))

omit [DecidableEq K] in
theorem closed_prmHdr (HDR PK TC BD BL BK BW O5 : K) :
    (prmHdr lO HDR PK TC BD BL BK BW O5).Closed :=
  ⟨closed_liftRegs lO (Calculus.closed_moveFieldTo HDR PK), closed_copyBits lO HDR BD TC,
    closed_liftRegs lO (Calculus.closed_moveFieldTo HDR PK), closed_copyBits lO HDR BL TC,
    closed_liftRegs lO (Calculus.closed_moveFieldTo HDR PK), closed_copyBits lO HDR BK TC,
    closed_liftRegs lO (Calculus.closed_moveFieldTo HDR PK), closed_copyBits lO HDR BW TC,
    closed_copyBits lO HDR O5 TC,
    closed_liftRegs lO (closed_forEachRange 4 _ (fun _ _ => Calculus.closed_moveFieldBack PK HDR))⟩

set_option linter.unusedSimpArgs false in
/-- The final stacks of `prmHdr`. -/
theorem prmHdr_final {HDR PK BD BL BK BW O5 : K} (dHP : HDR ≠ PK) (dHD : HDR ≠ BD)
    (dHL : HDR ≠ BL) (dHK : HDR ≠ BK) (dHW : HDR ≠ BW) (dHO : HDR ≠ O5) (dPD : PK ≠ BD)
    (dPL : PK ≠ BL) (dPK : PK ≠ BK) (dPW : PK ≠ BW) (dPO : PK ≠ O5) (dDL : BD ≠ BL)
    (dDK : BD ≠ BK) (dDW : BD ≠ BW) (dDO : BD ≠ O5) (dLK : BL ≠ BK) (dLW : BL ≠ BW)
    (dLO : BL ≠ O5) (dKW : BK ≠ BW) (dKO : BK ≠ O5) (dWO : BW ≠ O5)
    (S : K → List Sym) (D ℓ Kp w : ℕ) (t1 t2 t3 X Y m1 m2 m3 m4 : List Sym)
    (hH : S HDR = Y ++ X) (hPK : S PK = []) (hBD : S BD = []) (hBL : S BL = [])
    (hBK : S BK = []) (hBW : S BW = []) :
    let S1 := Function.update (Function.update S HDR t1) PK (m1 ++ S PK)
    let S2 := Function.update S1 BD (natSyms D ++ S1 BD)
    let S3 := Function.update (Function.update S2 HDR t2) PK (m2 ++ S2 PK)
    let S4 := Function.update S3 BL (natSyms ℓ ++ S3 BL)
    let S5 := Function.update (Function.update S4 HDR t3) PK (m3 ++ S4 PK)
    let S6 := Function.update S5 BK (natSyms Kp ++ S5 BK)
    let S7 := Function.update (Function.update S6 HDR X) PK (m4 ++ S6 PK)
    let S8 := Function.update S7 BW (natSyms w ++ S7 BW)
    let S9 := Function.update S8 O5 (natSyms w ++ S8 O5)
    Function.update (Function.update S9 PK []) HDR (Y ++ S9 HDR) =
      Function.update (Function.update (Function.update (Function.update (Function.update S
        BD (natSyms D)) BL (natSyms ℓ)) BK (natSyms Kp)) BW (natSyms w)) O5 (natSyms w ++ S O5) := by
  intro S1 S2 S3 S4 S5 S6 S7 S8 S9
  funext j
  simp only [S9, S8, S7, S6, S5, S4, S3, S2, S1, Function.update_apply, dHP, dHD, dHL, dHK, dHW,
    dHO, dPD, dPL, dPK, dPW, dPO, dDL, dDK, dDW, dDO, dLK, dLW, dLO, dKW, dKO, dWO, dHP.symm,
    dHD.symm, dHL.symm, dHK.symm, dHW.symm, dHO.symm, dPD.symm, dPL.symm, dPK.symm, dPW.symm,
    dPO.symm, dDL.symm, dDK.symm, dDW.symm, dDO.symm, dLK.symm, dLW.symm, dLO.symm, dKW.symm,
    dKO.symm, dWO.symm, if_false, if_true]
  split_ifs <;> simp_all

theorem runs_prmHdr {HDR PK TC BD BL BK BW O5 : K}
    (hd : [HDR, PK, TC, BD, BL, BK, BW, O5].Nodup) (S : K → List Sym) {D : ℕ} (q ℓ Kp w : ℕ)
    (a : Fin D → ℕ) (hrest : List Sym) (hH : S HDR = midHdr q ℓ Kp w a ++ hrest)
    (hPK : S PK = []) (hTC : S TC = []) (hBD : S BD = []) (hBL : S BL = []) (hBK : S BK = [])
    (hBW : S BW = []) :
    Runs (prmHdr lO HDR PK TC BD BL BK BW O5) S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        BD (natSyms D)) BL (natSyms ℓ)) BK (natSyms Kp)) BW (natSyms w)) O5 (natSyms w ++ S O5))
      (fun _ => True) (27 * (midHdr q ℓ Kp w a).length) := by
  have p0 := List.pairwise_cons.1 hd
  have dHP : HDR ≠ PK := p0.1 PK (by simp)
  have dHC : HDR ≠ TC := p0.1 TC (by simp)
  have dHD : HDR ≠ BD := p0.1 BD (by simp)
  have dHL : HDR ≠ BL := p0.1 BL (by simp)
  have dHK : HDR ≠ BK := p0.1 BK (by simp)
  have dHW : HDR ≠ BW := p0.1 BW (by simp)
  have dHO : HDR ≠ O5 := p0.1 O5 (by simp)
  have p1 := List.pairwise_cons.1 p0.2
  have dPC : PK ≠ TC := p1.1 TC (by simp)
  have dPD : PK ≠ BD := p1.1 BD (by simp)
  have dPL : PK ≠ BL := p1.1 BL (by simp)
  have dPK : PK ≠ BK := p1.1 BK (by simp)
  have dPW : PK ≠ BW := p1.1 BW (by simp)
  have dPO : PK ≠ O5 := p1.1 O5 (by simp)
  have p2 := List.pairwise_cons.1 p1.2
  have dCD : TC ≠ BD := p2.1 BD (by simp)
  have dCL : TC ≠ BL := p2.1 BL (by simp)
  have dCK : TC ≠ BK := p2.1 BK (by simp)
  have dCW : TC ≠ BW := p2.1 BW (by simp)
  have dCO : TC ≠ O5 := p2.1 O5 (by simp)
  have p3 := List.pairwise_cons.1 p2.2
  have dDL : BD ≠ BL := p3.1 BL (by simp)
  have dDK : BD ≠ BK := p3.1 BK (by simp)
  have dDW : BD ≠ BW := p3.1 BW (by simp)
  have dDO : BD ≠ O5 := p3.1 O5 (by simp)
  have p4 := List.pairwise_cons.1 p3.2
  have dLK : BL ≠ BK := p4.1 BK (by simp)
  have dLW : BL ≠ BW := p4.1 BW (by simp)
  have dLO : BL ≠ O5 := p4.1 O5 (by simp)
  have p5 := List.pairwise_cons.1 p4.2
  have dKW : BK ≠ BW := p5.1 BW (by simp)
  have dKO : BK ≠ O5 := p5.1 O5 (by simp)
  have dWO : BW ≠ O5 := (List.pairwise_cons.1 p5.2).1 O5 (by simp)
  have hlen := length_midHdr_ge q ℓ Kp w a
  set X := natSyms w ++ Sym.mark :: (W9.hdrSyms (List.ofFn a) ++ hrest) with hX
  set t3 := natSyms Kp ++ Sym.mark :: X with ht3
  set t2 := natSyms ℓ ++ Sym.mark :: t3 with ht2
  set t1 := natSyms D ++ Sym.mark :: t2 with ht1
  have hH' : S HDR = natSyms q ++ Sym.mark :: t1 := by rw [hH, midHdr_split5]
  -- 1. park `q`, copy `D`
  have e1 := runs_liftS lO (Calculus.runs_moveFieldTo dHP q t1 S hH')
  set S1 := Function.update (Function.update S HDR t1) PK (Calculus.fieldRev q ++ S PK) with hS1
  have h1H : S1 HDR = t1 := by rw [hS1, Function.update_of_ne dHP, Function.update_self]
  have h1C : S1 TC = [] := by
    rw [hS1, Function.update_of_ne dPC.symm, Function.update_of_ne dHC.symm, hTC]
  have e2 := runs_copyNat lO dHD dHC dCD.symm S1 D _ (by rw [h1H]) (TermOK.cons rfl _)
    (by rw [h1C]; exact termOK_nil')
  set S2 := Function.update S1 BD (natSyms D ++ S1 BD) with hS2
  have h2H : S2 HDR = t1 := by rw [hS2, Function.update_of_ne dHD, h1H]
  have h2C : S2 TC = [] := by rw [hS2, Function.update_of_ne dCD, h1C]
  -- 2. park `D`, copy `ℓ`
  have e3 := runs_liftS lO (Calculus.runs_moveFieldTo dHP D t2 S2 (by rw [h2H]))
  set S3 := Function.update (Function.update S2 HDR t2) PK (Calculus.fieldRev D ++ S2 PK)
    with hS3
  have h3H : S3 HDR = t2 := by rw [hS3, Function.update_of_ne dHP, Function.update_self]
  have h3C : S3 TC = [] := by
    rw [hS3, Function.update_of_ne dPC.symm, Function.update_of_ne dHC.symm, h2C]
  have e4 := runs_copyNat lO dHL dHC dCL.symm S3 ℓ _ (by rw [h3H]) (TermOK.cons rfl _)
    (by rw [h3C]; exact termOK_nil')
  set S4 := Function.update S3 BL (natSyms ℓ ++ S3 BL) with hS4
  have h4H : S4 HDR = t2 := by rw [hS4, Function.update_of_ne dHL, h3H]
  have h4C : S4 TC = [] := by rw [hS4, Function.update_of_ne dCL, h3C]
  -- 3. park `ℓ`, copy `K`
  have e5 := runs_liftS lO (Calculus.runs_moveFieldTo dHP ℓ t3 S4 (by rw [h4H]))
  set S5 := Function.update (Function.update S4 HDR t3) PK (Calculus.fieldRev ℓ ++ S4 PK)
    with hS5
  have h5H : S5 HDR = t3 := by rw [hS5, Function.update_of_ne dHP, Function.update_self]
  have h5C : S5 TC = [] := by
    rw [hS5, Function.update_of_ne dPC.symm, Function.update_of_ne dHC.symm, h4C]
  have e6 := runs_copyNat lO dHK dHC dCK.symm S5 Kp _ (by rw [h5H]) (TermOK.cons rfl _)
    (by rw [h5C]; exact termOK_nil')
  set S6 := Function.update S5 BK (natSyms Kp ++ S5 BK) with hS6
  have h6H : S6 HDR = t3 := by rw [hS6, Function.update_of_ne dHK, h5H]
  have h6C : S6 TC = [] := by rw [hS6, Function.update_of_ne dCK, h5C]
  -- 4. park `K`, copy `w` twice
  have e7 := runs_liftS lO (Calculus.runs_moveFieldTo dHP Kp X S6 (by rw [h6H]))
  set S7 := Function.update (Function.update S6 HDR X) PK (Calculus.fieldRev Kp ++ S6 PK)
    with hS7
  have h7H : S7 HDR = X := by rw [hS7, Function.update_of_ne dHP, Function.update_self]
  have h7C : S7 TC = [] := by
    rw [hS7, Function.update_of_ne dPC.symm, Function.update_of_ne dHC.symm, h6C]
  have e8 := runs_copyNat lO dHW dHC dCW.symm S7 w _ (by rw [h7H]) (TermOK.cons rfl _)
    (by rw [h7C]; exact termOK_nil')
  set S8 := Function.update S7 BW (natSyms w ++ S7 BW) with hS8
  have h8H : S8 HDR = X := by rw [hS8, Function.update_of_ne dHW, h7H]
  have h8C : S8 TC = [] := by rw [hS8, Function.update_of_ne dCW, h7C]
  have e9 := runs_copyNat lO dHO dHC dCO.symm S8 w _ (by rw [h8H]) (TermOK.cons rfl _)
    (by rw [h8C]; exact termOK_nil')
  set S9 := Function.update S8 O5 (natSyms w ++ S8 O5) with hS9
  -- 5. move the four fields back
  have h9P : S9 PK = [Kp, ℓ, D, q].flatMap Calculus.fieldRev ++ [] := by
    rw [hS9, Function.update_of_ne dPO, hS8, Function.update_of_ne dPW, hS7,
      Function.update_self, hS6, Function.update_of_ne dPK, hS5, Function.update_self, hS4,
      Function.update_of_ne dPL, hS3, Function.update_self, hS2, Function.update_of_ne dPD, hS1,
      Function.update_self, hPK]
    simp
  have e10 := runs_liftS lO (Calculus.runs_moveFieldsBack dHP.symm [Kp, ℓ, D, q] [] S9
    termOK_nil' h9P)
  refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 (runs_seq' e3 (runs_seq' e4
    (runs_seq' e5 (runs_seq' e6 (runs_seq' e7 (runs_seq' e8 (runs_seq' e9 e10)))))))))
    (fun _ _ => trivial) ?_) ?_
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · exact prmHdr_final dHP dHD dHL dHK dHW dHO dPD dPL dPK dPW dPO dDL dDK dDW dDO dLK dLW dLO
      dKW dKO dWO S D ℓ Kp w t1 t2 t3 X (W9.hdrSyms [Kp, ℓ, D, q].reverse) _ _ _ _
      (by rw [hH, midHdr_split]; rfl) hPK hBD hBL hBK hBW

end Hdr

end SubNLogN.Machine.FFT.PrefixParamAux
