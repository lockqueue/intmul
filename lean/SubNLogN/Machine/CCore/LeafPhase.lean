/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMask
import SubNLogN.Machine.CCore.LeafPhaseCost
import SubNLogN.Machine.CCore.LeafPhaseMaskVal
import SubNLogN.Machine.Layer.DrvPreKRot

/-!
# C-core leaf 8: the phase kernel (`CCore/LeafPhase.lean`)

**Result.** `phase_holds_of (hMS : MaskSelStmt) (p) : PhaseStmt p` (`CCore/SkelDefs.lean:257`).
The only hypothesis is the machine statement `MaskSelStmt` (`LeafPhaseMaskDefs.lean`, the
record-wise sign selection of `zSlot`/`zMask`, proved in `LeafPhaseMaskSelFinal.lean`). `RotIPowStmt` enters as
the proved `Layer.DrvPreK.rotIPow_holds`, `MaskValStmt` as the proved `maskVal_holds`.

**The kernel** (static role `u`, static kind `κ`; matching the value-level `cxNodeOps`):
* `neg` (`×(-1) = ×i²`): `rotProg u P₂`;
* `negIPow` (`×(-i)^f`), `iPow27` (`×i^{27f}`), `f = m^(k-1)`: `kProg u P₃` — at `k = 1` both are
  `×i³`; at `k ≥ 2` both are the identity (`4 ∣ m = 10^6`), tested on the descriptor at run time;
* `zSlot sl`, `zMask a`: `maskProg u P₂ Pm` — record-wise selection between the role array and its
  negation by the parity of the selected bits of the record address (`kindSlots`, `selBit`).
Paper: Lemma A.10 (`lem:transfer-phase`), Section A.5 (phases `Z_{a,f}`, `Z^{⊗f}`, `(-i)^f`, `i^{27f}`, `-1`
at an internal node), and Lemma A.5 (`lem:transfer-long-record`; per-record phases in `{±1, ±i}`).

**Cost** `C·t.volG` with `C = 2000 + 10·C_rot + 20·C_ms + 20·Cd p` (`Cd p` from the `d`-band, no
admissibility of `p` needed); cutoff `P₀ = 1`.
-/

namespace SubNLogN.Machine.CCore.LeafScalarAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability
open SubNLogN.Math.Common SubNLogN.Math.Walsh SubNLogN.Math.Networks SubNLogN.Machine.Layer.DrvPreK

/-! ## The mask program -/

/-- The floors of the mask path. -/
abbrev psM : List PS := [.X, .Y, .Tm, .X2, .Xn]

theorem floorsOK_psM : FloorsOK psM := by
  refine ⟨by decide, ?_⟩
  intro q hq
  simp only [psM, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide

section MaskProg

variable {E2 Em R2 Rm : Type} [DecidableEq E2] [DecidableEq Em]

/-- **The `zSlot`/`zMask` kernel.** -/
def maskProg (u : Fin Wn) (P2 : Prog (KLoc (Fin 3) E2) (fun _ => Sym) R2)
    (Pm : Prog (KLoc (Fin 9) Em) (fun _ => Sym) Rm) :
    Prog (BL (E2 ⊕ Em)) (fun _ => Sym) (σ (R2 × Rm)) :=
  .seq (callInj ιw (lid _) (preW psM)) (.seq (maskMid u P2 Pm) (callInj ιw (lid _) (postW psM)))

theorem closed_maskProg (u : Fin Wn) {P2 : Prog (KLoc (Fin 3) E2) (fun _ => Sym) R2}
    {Pm : Prog (KLoc (Fin 9) Em) (fun _ => Sym) Rm} (h2 : P2.Closed) (hm : Pm.Closed) :
    (maskProg u P2 Pm).Closed :=
  ⟨closed_callInj _ _ (closed_preW _), closed_maskMid u h2 hm, closed_callInj _ _ (closed_postW _)⟩

end MaskProg

/-! ## Safe runs of the three programs -/

section Runs3

variable {Er Rr : Type} [DecidableEq Er]

theorem kTestCost_le (t : CCoreRT) : bitLen 1 + 1 + 20 * (bitLen t.k + bitLen 1 + 1) +
    (2 * bitLen (t.k - 1) + 4 + (2 * bitLen 1 + 4)) ≤ 60 + 20 * bitLen t.k + 2 * bitLen (t.k - 1) := by
  have h1 : bitLen 1 = 1 := by decide
  rw [h1]; omega

/-- The `k ≥ 2` branch of `kProg`: nothing changes. -/
theorem safe_kProg_ge {P : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr} (u : Fin Wn) (t : CCoreRT)
    (tdesc : List Sym) (S : BL Er → List Sym) (hcl : KClean S) (hd : S descL = t.hdr ++ tdesc)
    (hk : 2 ≤ t.k) :
    SafeRunsIn ccoreFramed [] (kProg u P) S S (fun _ => True)
      (hdrCost t + wgCost t + 4 + (bitLen 1 + 1 + 20 * (bitLen t.k + bitLen 1 + 1)) +
        (1 + ((2 * bitLen (t.k - 1) + 4 + (2 * bitLen 1 + 4)) + (4 + dropCost t) + 1))) := by
  have e0 := stv_of_clean S hcl
  have c1 := safe_callW (Rr := Rr)
    (P := (Prog.seq (preW psR) kTestW : Prog (Lw Er) (fun _ => Sym) (σ Rr)))
    ⟨closed_preW psR, ⟨WP.W9comp.closed_liftRegs _
      (NatArith.closed_pushNat _ _), WP.W9comp.closed_liftRegs _ (NatArith.closed_subN _ _ _ _ _ _)⟩⟩
    S (fun _ => []) (scK t)
    (WP.W9comp.runs_seq (by rw [hd]; exact runs_preW psR floorsOK_psR t tdesc _)
      (runs_kTestW t (by omega) _ _))
  rw [← e0] at c1
  have hp := safe_peekCt (Er := Er) (Rr := Rr) S (scK t)
  have hct : optIsBit ((scK t) .ct).head? = true := by
    simp only [scK, Function.update_self]
    rw [optIsBit_head_natSyms]; simp; omega
  rw [hct] at hp
  have c3 := safe_callW (Rr := Rr)
    (P := (Prog.seq kUndoW (postW psR) : Prog (Lw Er) (fun _ => Sym) (σ Rr)))
    ⟨⟨WP.W9comp.closed_liftRegs _ (NatArith.closed_dropN _),
      WP.W9comp.closed_liftRegs _ (NatArith.closed_dropN _)⟩, closed_postW psR⟩ S (scK t)
    (fun _ => []) (WP.W9comp.runs_seq (runs_kUndoW t _ _) (runs_postW psR floorsOK_psR t _ _))
  rw [← e0] at c3
  exact SafeRunsIn.seq c1 (SafeRunsIn.ite_true hp c3)

/-- The `k = 1` branch of `kProg`: the rotation by `i^3`. -/
theorem safe_kProg_one {C : ℕ} {P : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr}
    (hspec : ∀ (w : ℕ) (v : List (List CInt)) (rest r2 : List Sym)
      (S : KLoc (Fin 3) Er → List Sym),
      1 ≤ w → CArrFits w v → CArrFits w (mapC (rotIPowC 3) v) → BlkTerm rest → TermOK r2 →
      S (.inl 0) = carrSyms w v ++ rest → S (.inl 2) = natSyms w ++ r2 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (carrSyms w (mapC (rotIPowC 3) v) ++ S (.inl 1)))
        (fun _ => True) (C * (cvol w v + w + 1)))
    (hP : P.Closed) (u : Fin Wn) (t : CCoreRT) (tdesc : List Sym) (v : List (List CInt))
    (S : BL Er → List Sym) (hcl : KClean S) (hd : S descL = t.hdr ++ tdesc) (hk : t.k = 1)
    (hu : S (roleL u) = carrSyms t.wg v ++ [Sym.mark])
    (hf1 : CArrFits t.wg v) (hf2 : CArrFits t.wg (mapC (rotIPowC 3) v)) :
    SafeRunsIn ccoreFramed [] (kProg u P) S
      (Function.update S (roleL u) (carrSyms t.wg (mapC (rotIPowC 3) v) ++ [Sym.mark]))
      (fun _ => True)
      (hdrCost t + wgCost t + 4 + (bitLen 1 + 1 + 20 * (bitLen t.k + bitLen 1 + 1)) +
        (1 + ((16 * cvol t.wg v + 8 + C * (cvol t.wg v + t.wg + 1)) +
          ((2 * bitLen (t.k - 1) + 4 + (2 * bitLen 1 + 4)) + (4 + dropCost t)) + 1))) := by
  have e0 := stv_of_clean S hcl
  have c1 := safe_callW (Rr := Rr)
    (P := (Prog.seq (preW psR) kTestW : Prog (Lw Er) (fun _ => Sym) (σ Rr)))
    ⟨closed_preW psR, ⟨WP.W9comp.closed_liftRegs _
      (NatArith.closed_pushNat _ _), WP.W9comp.closed_liftRegs _ (NatArith.closed_subN _ _ _ _ _ _)⟩⟩
    S (fun _ => []) (scK t)
    (WP.W9comp.runs_seq (by rw [hd]; exact runs_preW psR floorsOK_psR t tdesc _)
      (runs_kTestW t (by omega) _ _))
  rw [← e0] at c1
  have hp := safe_peekCt (Er := Er) (Rr := Rr) S (scK t)
  have hct : optIsBit ((scK t) .ct).head? = false := by
    simp only [scK, Function.update_self, hk]
    rfl
  rw [hct] at hp
  have hw : 1 ≤ t.wg := by simp [CCoreRT.wg]
  have c2 := safe_rotMid hspec hP u t.wg hw v S (scK t) hu (by simp [scK, scP])
    (by simp [scK, scP]) (by simp [scK, scP]) (by simp [scK, scP, scW]) hf1 hf2
  have c3 := safe_callW (Rr := Rr)
    (P := (Prog.seq kUndoW (postW psR) : Prog (Lw Er) (fun _ => Sym) (σ Rr)))
    ⟨⟨WP.W9comp.closed_liftRegs _ (NatArith.closed_dropN _),
      WP.W9comp.closed_liftRegs _ (NatArith.closed_dropN _)⟩, closed_postW psR⟩
    (Function.update S (roleL u) (carrSyms t.wg (mapC (rotIPowC 3) v) ++ [Sym.mark])) (scK t)
    (fun _ => []) (WP.W9comp.runs_seq (runs_kUndoW t _ _) (runs_postW psR floorsOK_psR t _ _))
  rw [stv_update_role_clean S hcl] at c3
  exact SafeRunsIn.seq c1 (SafeRunsIn.ite_false hp (SafeRunsIn.seq c2 c3))

theorem safe_maskProg {E2 Em R2 Rm : Type} [DecidableEq E2] [DecidableEq Em] {C2 Cm : ℕ}
    {ss : Finset (Fin mn)}
    {P2 : Prog (KLoc (Fin 3) E2) (fun _ => Sym) R2} {Pm : Prog (KLoc (Fin 9) Em) (fun _ => Sym) Rm}
    (hspec2 : ∀ (w : ℕ) (v : List (List CInt)) (rest r2 : List Sym)
      (S : KLoc (Fin 3) E2 → List Sym),
      1 ≤ w → CArrFits w v → CArrFits w (mapC (rotIPowC 2) v) → BlkTerm rest → TermOK r2 →
      S (.inl 0) = carrSyms w v ++ rest → S (.inl 2) = natSyms w ++ r2 →
      Runs P2 S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (carrSyms w (mapC (rotIPowC 2) v) ++ S (.inl 1)))
        (fun _ => True) (C2 * (cvol w v + w + 1)))
    (hspecm : ∀ (K D S j0 k ρ : ℕ) (v vn : List (List Bool))
      (rx rxn r3 r4 r5 r6 r7 r8 : List Sym) (St : KLoc (Fin 9) Em → List Sym),
      KClean St → 1 ≤ k → ρ < K → j0 + mn ^ k ≤ D → 1 ≤ S → v.length = vn.length →
      BlkTerm rx → BlkTerm rxn →
      TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 → TermOK r7 → TermOK r8 →
      St (.inl 0) = arrSyms v ++ rx → St (.inl 1) = arrSyms vn ++ rxn →
      St (.inl 3) = natSyms K ++ r3 → St (.inl 4) = natSyms D ++ r4 →
      St (.inl 5) = natSyms S ++ r5 → St (.inl 6) = natSyms j0 ++ r6 →
      St (.inl 7) = natSyms k ++ r7 → St (.inl 8) = natSyms ρ ++ r8 →
      Runs Pm St
        (Function.update (Function.update (Function.update St (.inl 0) rx) (.inl 1) rxn) (.inl 2)
          (arrSyms (selRecs (selBit ss K D S j0 (mn ^ (k - 1)) ρ) v vn) ++ St (.inl 2)))
        (fun _ => True) (Cm * (vol v + vol vn + 2 ^ (K * D) + S + D + 1)))
    (h2 : P2.Closed) (hm : Pm.Closed) (u : Fin Wn) (t : CCoreRT) (tdesc : List Sym)
    (hk : 1 ≤ t.k) (hρ : t.ρ < t.K) (hjD : t.j0 + mn ^ t.k ≤ t.D) (hS : 1 ≤ t.S)
    (v : List (List CInt)) (S : BL (E2 ⊕ Em) → List Sym) (hcl : KClean S)
    (hd : S descL = t.hdr ++ tdesc) (hu : S (roleL u) = carrSyms t.wg v ++ [Sym.mark])
    (hf1 : CArrFits t.wg v) (hf2 : CArrFits t.wg (mapC (rotIPowC 2) v)) :
    SafeRunsIn ccoreFramed [] (maskProg u P2 Pm) S
      (Function.update S (roleL u)
        (arrSyms (selRecs (selBit ss t.K t.D t.S t.j0 (mn ^ (t.k - 1)) t.ρ)
          (v.map (crecBits t.wg)) ((mapC (rotIPowC 2) v).map (crecBits t.wg))) ++ [Sym.mark]))
      (fun _ => True)
      ((hdrCost t + wgCost t + (psM.length + 1)) +
        ((8 * cvol t.wg v + 4 + (9 * cvol t.wg v + 4 + C2 * (cvol t.wg v + t.wg + 1) +
          Cm * (cvol t.wg v + cvol t.wg v + 2 ^ (t.K * t.D) + t.S + t.D + 1)) +
          (8 * (arrSyms (selRecs (selBit ss t.K t.D t.S t.j0 (mn ^ (t.k - 1)) t.ρ)
            (v.map (crecBits t.wg)) ((mapC (rotIPowC 2) v).map (crecBits t.wg)))).length + 4)) +
          (psM.length + 1 + dropCost t))) := by
  have e0 := stv_of_clean S hcl
  have c1 := safe_callW (Rr := R2 × Rm) (closed_preW psM) S (fun _ => []) (scP psM t)
    (by rw [hd]; exact runs_preW psM floorsOK_psM t tdesc _)
  rw [← e0] at c1
  have c2 := safe_maskMid (ss := ss) hspec2 hspecm h2 hm u t hk hρ hjD hS v S
    (fun e => hcl (.inr e)) (scP psM t) hu (by simp [scP]) (by simp [scP]) (by simp [scP])
    (by simp [scP]) (by simp [scP]) (by simp [scP, scW]) (by simp [scP, scW, scHdr])
    (by simp [scP, scW, scHdr]) (by simp [scP, scW, scHdr]) (by simp [scP, scW, scHdr])
    (by simp [scP, scW, scHdr]) (by simp [scP, scW, scHdr]) hf1 hf2
  have c3 := safe_callW (Rr := R2 × Rm) (closed_postW psM) (Function.update S (roleL u)
      (arrSyms (selRecs (selBit ss t.K t.D t.S t.j0 (mn ^ (t.k - 1)) t.ρ)
        (v.map (crecBits t.wg)) ((mapC (rotIPowC 2) v).map (crecBits t.wg))) ++ [Sym.mark]))
    (scP psM t) (fun _ => []) (runs_postW psM floorsOK_psM t _ _)
  rw [stv_update_role_clean S hcl] at c3
  exact SafeRunsIn.seq c1 (SafeRunsIn.seq c2 c3)

end Runs3

/-! ## Cost bounds -/

/-- The cost constant of the phase kernel. -/
noncomputable def phaseC (p : LayerParams) (Crot Cms : ℕ) : ℕ :=
  2000 + 10 * Crot + 20 * Cms + 20 * Cd p

theorem rotCost_le {p : LayerParams} {t : CCoreRT} (hb : CCoreBands p 1 t) (Crot Cms V : ℕ)
    (hV : V ≤ 2 * t.volG) : rotCost t Crot V ≤ phaseC p Crot Cms * t.volG := by
  have h1 := hdrCost_le hb
  have h2 := wgCost_le hb
  have h3 := dropCost_le hb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hV1, hw1, -⟩ := fields_le hb
  have h4 : Crot * (V + t.wg + 1) ≤ 4 * (Crot * t.volG) := by
    calc Crot * (V + t.wg + 1) ≤ Crot * (4 * t.volG) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * (Crot * t.volG) := by ring
  have e : phaseC p Crot Cms * t.volG =
      2000 * t.volG + 10 * (Crot * t.volG) + 20 * (Cms * t.volG) + 20 * (Cd p * t.volG) := by
    simp only [phaseC]; ring
  rw [e]
  simp only [rotCost]
  omega

theorem kCost_le {p : LayerParams} {t : CCoreRT} (hb : CCoreBands p 1 t) (Crot Cms V : ℕ)
    (hV : V ≤ 2 * t.volG) :
    hdrCost t + wgCost t + 4 + (bitLen 1 + 1 + 20 * (bitLen t.k + bitLen 1 + 1)) +
        (1 + ((16 * V + 8 + Crot * (V + t.wg + 1)) +
          ((2 * bitLen (t.k - 1) + 4 + (2 * bitLen 1 + 4)) + (4 + dropCost t)) + 1)) ≤
      phaseC p Crot Cms * t.volG := by
  have h1 := hdrCost_le hb
  have h2 := wgCost_le hb
  have h3 := dropCost_le hb
  obtain ⟨-, -, -, -, -, -, -, -, -, hk, -, -, -, -, hk1, -, hV1, hw1, -⟩ := fields_le hb
  have hb1 : bitLen 1 = 1 := by decide
  have h4 : Crot * (V + t.wg + 1) ≤ 4 * (Crot * t.volG) := by
    calc Crot * (V + t.wg + 1) ≤ Crot * (4 * t.volG) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * (Crot * t.volG) := by ring
  have e : phaseC p Crot Cms * t.volG =
      2000 * t.volG + 10 * (Crot * t.volG) + 20 * (Cms * t.volG) + 20 * (Cd p * t.volG) := by
    simp only [phaseC]; ring
  rw [e, hb1]
  omega

theorem maskCost_le {p : LayerParams} {t : CCoreRT} (hb : CCoreBands p 1 t) (Crot Cms V V2 : ℕ)
    (hV : V ≤ 2 * t.volG) (hV2 : V2 ≤ 2 * t.volG) :
    (hdrCost t + wgCost t + (psM.length + 1)) +
        ((8 * V + 4 + (9 * V + 4 + Crot * (V + t.wg + 1) +
          Cms * (V + V + 2 ^ (t.K * t.D) + t.S + t.D + 1)) + (8 * V2 + 4)) +
          (psM.length + 1 + dropCost t)) ≤
      phaseC p Crot Cms * t.volG := by
  have h1 := hdrCost_le hb
  have h2 := wgCost_le hb
  have h3 := dropCost_le hb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hV1, hw1, hKD, hS, hD, -⟩ := fields_le hb
  have h4 : Crot * (V + t.wg + 1) ≤ 4 * (Crot * t.volG) := by
    calc Crot * (V + t.wg + 1) ≤ Crot * (4 * t.volG) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * (Crot * t.volG) := by ring
  have h5 : Cms * (V + V + 2 ^ (t.K * t.D) + t.S + t.D + 1) ≤ 8 * (Cms * t.volG) := by
    calc Cms * (V + V + 2 ^ (t.K * t.D) + t.S + t.D + 1) ≤ Cms * (8 * t.volG) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 8 * (Cms * t.volG) := by ring
  have e : phaseC p Crot Cms * t.volG =
      2000 * t.volG + 10 * (Crot * t.volG) + 20 * (Cms * t.volG) + 20 * (Cd p * t.volG) := by
    simp only [phaseC]; ring
  rw [e]
  simp only [psM, List.length_cons, List.length_nil]
  omega

end SubNLogN.Machine.CCore.LeafScalarAux

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus LeafScalarAux
open SubNLogN.Math.Common SubNLogN.Math.Walsh SubNLogN.Math.Networks SubNLogN.Machine.Layer.DrvPreK

/-- **[LEAF 8] The phase kernel**, from the machine statement `MaskSelStmt` of the record-wise
sign selection (`LeafPhaseMaskDefs.lean`). Cutoff `P₀ = 1`, constant `phaseC p C_rot C_ms`. -/
theorem phase_holds_of (hMS : MaskSelStmt) (p : LayerParams) : PhaseStmt p := by
  obtain ⟨Crot, hrot⟩ := rotIPow_holds
  obtain ⟨Cms, hms⟩ := hMS
  refine ⟨1, phaseC p Crot Cms, ?_⟩
  rintro ⟨u, κ⟩
  obtain ⟨E2, hF2, hD2, R2, P2, hfin2, hne2, hcl2, hspec2⟩ := hrot 2
  obtain ⟨E3, hF3, hD3, R3, P3, hfin3, hne3, hcl3, hspec3⟩ := hrot 3
  let _ := hF2; let _ := hD2; let _ := hF3; let _ := hD3
  haveI := hfin2; haveI := hne2; haveI := hfin3; haveI := hne3
  cases κ with
  | neg =>
    refine ⟨PS ⊕ E2, inferInstance, inferInstance, σ R2, rotProg u P2, inferInstance,
      inferInstance, closed_rotProg u hcl2, ?_⟩
    intro t hA' hS w b tdesc S hb hk hg hbΔ hcl hd hu
    have hgrid := onGrid_of_growth hg hbΔ
    have hval : Enc (compactRT t) hA' hS (runSteps [phaseStep t .neg] w) =
        carrSyms t.wg (mapC (rotIPowC 2)
          (encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) w)) := by
      rw [Enc_eq, runSteps_neg, encArr_Ipow _ _ _ _ hgrid]
    rw [hval]
    exact SafeRunsIn.mono (safe_rotProg hspec2 hcl2 u t tdesc _ S hcl hd hu
      (fits_encArr0 hg hbΔ _) (fits_encArr hg hbΔ _ 2)) (fun _ _ => trivial)
      (rotCost_le hb Crot Cms _ (cvol_le hb hA' hS w _))
  | negIPow =>
    refine ⟨PS ⊕ E3, inferInstance, inferInstance, σ R3, kProg u P3, inferInstance,
      inferInstance, closed_kProg u hcl3, ?_⟩
    intro t hA' hS w b tdesc S hb hk hg hbΔ hcl hd hu
    have hgrid := onGrid_of_growth hg hbΔ
    by_cases hk2 : 2 ≤ t.k
    · have hval : runSteps [phaseStep t .negIPow] w = w := by
        rw [runSteps_negIPow]; funext x; rw [I_pow_c_mn hk2, one_smul]
      rw [hval, ← hu, Function.update_eq_self]
      exact SafeRunsIn.mono (safe_kProg_ge (P := P3) u t tdesc S hcl hd hk2) (fun _ _ => trivial)
        (le_trans (by omega) (kCost_le hb Crot Cms 0 (by omega)))
    · have hk1 : t.k = 1 := by omega
      have hval : Enc (compactRT t) hA' hS (runSteps [phaseStep t .negIPow] w) =
          carrSyms t.wg (mapC (rotIPowC 3)
            (encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) w)) := by
        rw [Enc_eq, runSteps_negIPow, encArr_Ipow _ _ _ _ hgrid, hk1, rotIPowC_3_mn_one]
      rw [hval]
      exact SafeRunsIn.mono (safe_kProg_one hspec3 hcl3 u t tdesc _ S hcl hd hk1 hu
        (fits_encArr0 hg hbΔ _) (fits_encArr hg hbΔ _ 3)) (fun _ _ => trivial)
        (kCost_le hb Crot Cms _ (cvol_le hb hA' hS w _))
  | iPow27 =>
    refine ⟨PS ⊕ E3, inferInstance, inferInstance, σ R3, kProg u P3, inferInstance,
      inferInstance, closed_kProg u hcl3, ?_⟩
    intro t hA' hS w b tdesc S hb hk hg hbΔ hcl hd hu
    have hgrid := onGrid_of_growth hg hbΔ
    by_cases hk2 : 2 ≤ t.k
    · have hval : runSteps [phaseStep t .iPow27] w = w := by
        rw [runSteps_iPow27]; funext x; rw [I_pow_c_mn hk2, one_smul]
      rw [hval, ← hu, Function.update_eq_self]
      exact SafeRunsIn.mono (safe_kProg_ge (P := P3) u t tdesc S hcl hd hk2) (fun _ _ => trivial)
        (le_trans (by omega) (kCost_le hb Crot Cms 0 (by omega)))
    · have hk1 : t.k = 1 := by omega
      have hval : Enc (compactRT t) hA' hS (runSteps [phaseStep t .iPow27] w) =
          carrSyms t.wg (mapC (rotIPowC 3)
            (encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) w)) := by
        rw [Enc_eq, runSteps_iPow27, encArr_Ipow _ _ _ _ hgrid, hk1, rotIPowC_27_mn_one]
      rw [hval]
      exact SafeRunsIn.mono (safe_kProg_one hspec3 hcl3 u t tdesc _ S hcl hd hk1 hu
        (fits_encArr0 hg hbΔ _) (fits_encArr hg hbΔ _ 3)) (fun _ _ => trivial)
        (kCost_le hb Crot Cms _ (cvol_le hb hA' hS w _))
  | zMask a =>
    obtain ⟨Em, hFm, hDm, Rm, Pm, hfinm, hnem, hclm, hspecm⟩ := hms (kindSlots (.zMask a))
    letI := hFm; letI := hDm; haveI := hfinm; haveI := hnem
    refine ⟨PS ⊕ (E2 ⊕ Em), inferInstance, inferInstance, σ (R2 × Rm), maskProg u P2 Pm,
      inferInstance, inferInstance, closed_maskProg u hcl2 hclm, ?_⟩
    intro t hA' hS w b tdesc S hb hk hg hbΔ hcl hd hu
    have hb' := hb
    obtain ⟨_, _, _, _, _, _, _, _, hS1, _, _, hjD, hρ, _⟩ := hb'
    have hgrid := onGrid_of_growth hg hbΔ
    have hMV := maskVal_holds t hA' hS (.zMask a) (Or.inr ⟨a, rfl⟩) hk hρ hjD w hgrid
    have hcr : crecBits t.wg default = default := rfl
    have hval : Enc (compactRT t) hA' hS (runSteps [phaseStep t (.zMask a)] w) =
        arrSyms (selRecs (selBit (kindSlots (.zMask a)) t.K t.D t.S t.j0 (mn ^ (t.k - 1)) t.ρ)
          ((encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) w).map (crecBits t.wg))
          ((mapC (rotIPowC 2) (encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS)
            w)).map (crecBits t.wg))) := by
      rw [Enc_eq, hMV, carrSyms, map_selRecs _ _ hcr]
    rw [hval]
    have hlen2 := cvol_le hb hA' hS (runSteps [phaseStep t (.zMask a)] w) (t.P + t.Δ)
    rw [cvol, ← Enc_eq, hval] at hlen2
    exact SafeRunsIn.mono (safe_maskProg (ss := kindSlots (.zMask a)) hspec2 hspecm hcl2 hclm u t
      tdesc hk hρ hjD hS1 _ S hcl hd hu (fits_encArr0 hg hbΔ _) (fits_encArr hg hbΔ _ 2))
      (fun _ _ => trivial) (maskCost_le hb Crot Cms _ _ (cvol_le hb hA' hS w _) hlen2)
  | zSlot sl =>
    obtain ⟨Em, hFm, hDm, Rm, Pm, hfinm, hnem, hclm, hspecm⟩ := hms (kindSlots (.zSlot sl))
    letI := hFm; letI := hDm; haveI := hfinm; haveI := hnem
    refine ⟨PS ⊕ (E2 ⊕ Em), inferInstance, inferInstance, σ (R2 × Rm), maskProg u P2 Pm,
      inferInstance, inferInstance, closed_maskProg u hcl2 hclm, ?_⟩
    intro t hA' hS w b tdesc S hb hk hg hbΔ hcl hd hu
    have hb' := hb
    obtain ⟨_, _, _, _, _, _, _, _, hS1, _, _, hjD, hρ, _⟩ := hb'
    have hgrid := onGrid_of_growth hg hbΔ
    have hMV := maskVal_holds t hA' hS (.zSlot sl) (Or.inl ⟨sl, rfl⟩) hk hρ hjD w hgrid
    have hcr : crecBits t.wg default = default := rfl
    have hval : Enc (compactRT t) hA' hS (runSteps [phaseStep t (.zSlot sl)] w) =
        arrSyms (selRecs (selBit (kindSlots (.zSlot sl)) t.K t.D t.S t.j0 (mn ^ (t.k - 1)) t.ρ)
          ((encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) w).map (crecBits t.wg))
          ((mapC (rotIPowC 2) (encArr (t.P + t.Δ) (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS)
            w)).map (crecBits t.wg))) := by
      rw [Enc_eq, hMV, carrSyms, map_selRecs _ _ hcr]
    rw [hval]
    have hlen2 := cvol_le hb hA' hS (runSteps [phaseStep t (.zSlot sl)] w) (t.P + t.Δ)
    rw [cvol, ← Enc_eq, hval] at hlen2
    exact SafeRunsIn.mono (safe_maskProg (ss := kindSlots (.zSlot sl)) hspec2 hspecm hcl2 hclm u t
      tdesc hk hρ hjD hS1 _ S hcl hd hu (fits_encArr0 hg hbΔ _) (fits_encArr hg hbΔ _ 2))
      (fun _ _ => trivial) (maskCost_le hb Crot Cms _ _ (cvol_le hb hA' hS w _) hlen2)

end SubNLogN.Machine.CCore
