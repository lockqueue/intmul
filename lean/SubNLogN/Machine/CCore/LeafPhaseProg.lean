/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseCall

/-!
# C-core phase leaf: the rotation path (`CCore/LeafPhaseProg.lean`)

**Scope (honest summary).** The program `rotProg u P` of the phase kinds that multiply every
coefficient by a fixed `i^e`, with the sub-kernel `P` of `RotIPowStmt` (`Layer/DrvPreKDefs.lean:42`),
and its exact safe run `safe_rotProg`:
1. (scratch) read the descriptor, form `natSyms w_g`, push floors on `X, Y, Tm`;
2. (certified pass) move role `u`'s array onto `X`;
3. (scratch) `RotIPowStmt`: `X ↦ Y`;
4. (certified pass) move `Y` back onto role `u`;
5. (scratch) pop the floors, drop the counters.
Also: volumes of stored arrays (`length_carrSyms`, `cvol_mapC`). Everything is proved.
-/

namespace SubNLogN.Machine.CCore.LeafScalarAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability
open SubNLogN.Machine.Layer.DrvPreK

variable {Er Rr : Type}

/-! ## Pre and post programs on the work layout -/

/-- Read the descriptor, form the width counter, push floors on `ps`. -/
def preW (ps : List PS) : Prog (Lw Er) (fun _ => Sym) (σ Rr) :=
  .seq (readHdr.liftRegs (lO Rr)) (.seq (wgProg.liftRegs (lN Rr)) ((pushMarks ps).liftRegs (lO Rr)))

/-- Pop the floors on `ps`, drop the counters. -/
def postW (ps : List PS) : Prog (Lw Er) (fun _ => Sym) (σ Rr) :=
  .seq ((popMarks ps).liftRegs (lO Rr)) (dropCtrs.liftRegs (lN Rr))

theorem closed_preW (ps : List PS) : (preW (Er := Er) (Rr := Rr) ps).Closed :=
  ⟨WP.W9comp.closed_liftRegs _ closed_readHdr, WP.W9comp.closed_liftRegs _ closed_wgProg,
    WP.W9comp.closed_liftRegs _ (closed_pushMarks ps)⟩

theorem closed_postW (ps : List PS) : (postW (Er := Er) (Rr := Rr) ps).Closed :=
  ⟨WP.W9comp.closed_liftRegs _ (closed_popMarks ps), WP.W9comp.closed_liftRegs _ closed_dropCtrs⟩

/-- The scratch after `preW ps`: floors on `ps`, the counters of `scW t` elsewhere. -/
def scP (ps : List PS) (t : CCoreRT) : PS → List Sym :=
  fun q => if q ∈ ps then [Sym.mark] else scW t q

/-- The floors are on stacks without counters. -/
def FloorsOK (ps : List PS) : Prop :=
  ps.Nodup ∧ ∀ q ∈ ps, q ≠ .cP ∧ q ≠ .cDl ∧ q ≠ .cK ∧ q ≠ .cDD ∧ q ≠ .cS ∧ q ≠ .cJ ∧ q ≠ .cKk ∧
    q ≠ .cRho ∧ q ≠ .cW

theorem scW_eq_nil_of (t : CCoreRT) (q : PS) (h : q ≠ .cP ∧ q ≠ .cDl ∧ q ≠ .cK ∧ q ≠ .cDD ∧
    q ≠ .cS ∧ q ≠ .cJ ∧ q ≠ .cKk ∧ q ≠ .cRho ∧ q ≠ .cW) : scW t q = [] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  cases q <;> simp_all [scW, scHdr, Function.update_apply]

variable [DecidableEq Er]

theorem runs_preW (ps : List PS) (hps : FloorsOK ps) (t : CCoreRT) (tdesc : List Sym)
    (er : Er → List Sym) :
    Runs (preW (Er := Er) (Rr := Rr) ps) (wst (t.hdr ++ tdesc) (fun _ => []) er)
      (wst (t.hdr ++ tdesc) (scP ps t) er) (fun _ => True)
      (hdrCost t + wgCost t + (ps.length + 1)) := by
  have h1 := WP.W0m.runs_liftRegs (lO Rr) (runs_readHdr (Er := Er) t tdesc er)
  have h2 := WP.W0m.runs_liftRegs (lN Rr) (runs_wgProg (Er := Er) t (t.hdr ++ tdesc) er)
  have h3 := WP.W0m.runs_liftRegs (lO Rr) (runs_pushMarks (Er := Er) (t.hdr ++ tdesc) er ps
    (scW t) hps.1)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1
    (WP.W9comp.runs_seq h2 h3)) ?_) (fun _ _ => trivial) (by omega)
  congr 1
  funext q
  by_cases hq : q ∈ ps
  · simp [scP, hq, scW_eq_nil_of t q (hps.2 q hq)]
  · simp [scP, hq]

theorem runs_postW (ps : List PS) (hps : FloorsOK ps) (t : CCoreRT) (d : List Sym)
    (er : Er → List Sym) :
    Runs (postW (Er := Er) (Rr := Rr) ps) (wst d (scP ps t) er) (wst d (fun _ => []) er)
      (fun _ => True) (ps.length + 1 + dropCost t) := by
  have h1 := WP.W0m.runs_liftRegs (lO Rr) (runs_popMarks (Er := Er) d er ps (scP ps t) hps.1
    (fun q hq => by simp [scP, hq]))
  have h2 := WP.W0m.runs_liftRegs (lN Rr) (runs_dropCtrs (Er := Er) t d er
    (fun q => if q ∈ ps then [] else scP ps t q)
    (by
      intro q h1 h2 h3 h4 h5 h6 h7 h8 h9
      by_cases hq : q ∈ ps
      · simp [hq]
      · simp only [hq, if_false, scP]
        exact scW_eq_nil_of t q ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)
    (by have := hps.2 PS.cP; by_cases hq : PS.cP ∈ ps
        · exact absurd rfl (this hq).1
        · simp [hq, scP, scW, scHdr])
    (by have := hps.2 PS.cDl; by_cases hq : PS.cDl ∈ ps
        · exact absurd rfl (this hq).2.1
        · simp [hq, scP, scW, scHdr])
    (by have := hps.2 PS.cK; by_cases hq : PS.cK ∈ ps
        · exact absurd rfl (this hq).2.2.1
        · simp [hq, scP, scW, scHdr])
    (by have := hps.2 PS.cDD; by_cases hq : PS.cDD ∈ ps
        · exact absurd rfl (this hq).2.2.2.1
        · simp [hq, scP, scW, scHdr])
    (by have := hps.2 PS.cS; by_cases hq : PS.cS ∈ ps
        · exact absurd rfl (this hq).2.2.2.2.1
        · simp [hq, scP, scW, scHdr])
    (by have := hps.2 PS.cJ; by_cases hq : PS.cJ ∈ ps
        · exact absurd rfl (this hq).2.2.2.2.2.1
        · simp [hq, scP, scW, scHdr])
    (by have := hps.2 PS.cKk; by_cases hq : PS.cKk ∈ ps
        · exact absurd rfl (this hq).2.2.2.2.2.2.1
        · simp [hq, scP, scW, scHdr])
    (by have := hps.2 PS.cRho; by_cases hq : PS.cRho ∈ ps
        · exact absurd rfl (this hq).2.2.2.2.2.2.2.1
        · simp [hq, scP, scW, scHdr])
    (by have := hps.2 PS.cW; by_cases hq : PS.cW ∈ ps
        · exact absurd rfl (this hq).2.2.2.2.2.2.2.2
        · simp [hq, scP, scW]))
  exact WP.W9comp.runs_mono (WP.W9comp.runs_seq h1 h2) (fun _ _ => trivial) le_rfl

/-! ## Volumes -/

theorem arrSyms_cons' (p : List Bool) (v : List (List Bool)) :
    arrSyms (p :: v) = recSyms p ++ arrSyms v := rfl

theorem mark_not_mem_arrSyms' : ∀ v : List (List Bool), Sym.mark ∉ arrSyms v
  | [] => by simp [arrSyms, blk]
  | p :: v => by
    rw [arrSyms_cons', List.mem_append, not_or]
    refine ⟨?_, mark_not_mem_arrSyms' v⟩
    simp [recSyms]


theorem length_twosBits' (w : ℕ) (z : ℤ) : (twosBits w z).length = w := by
  simp [twosBits, bitsLE]

theorem length_carrSyms (w : ℕ) :
    ∀ v : List (List CInt), (carrSyms w v).length = (v.map fun cs => 2 * w * cs.length + 1).sum
  | [] => rfl
  | cs :: v => by
    have h := length_carrSyms w v
    simp only [carrSyms, List.map_cons] at h ⊢
    rw [arrSyms_cons', List.length_append, h, List.sum_cons]
    simp only [recSyms, crecBits, List.length_append, List.length_map, List.length_cons,
      List.length_nil, List.length_flatMap, coefBits, length_twosBits']
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
    ring

theorem cvol_mapC (w : ℕ) (f : CInt → CInt) (v : List (List CInt)) :
    cvol w (mapC f v) = cvol w v := by
  simp only [cvol, length_carrSyms, mapC, List.map_map]
  congr 1
  apply List.map_congr_left
  intro cs _
  simp

/-! ## The rotation path -/

/-- The floors of the rotation path. -/
abbrev psR : List PS := [.X, .Y, .Tm]

theorem floorsOK_psR : FloorsOK psR := by
  refine ⟨by decide, ?_⟩
  intro q hq
  simp only [psR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> decide

/-- **The rotation path** of the phase kernel (static role `u`, sub-kernel `P` of
`RotIPowStmt` for a fixed `e`). -/
def rotProg (u : Fin Wn) (P : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr) :
    Prog (BL Er) (fun _ => Sym) (σ Rr) :=
  .seq (callInj ιw (lid _) (preW psR))
  (.seq (mvIn Rr u)
  (.seq (callInj ιw (lid _) (callInj (ι3 .X .Y .cW id) (lR Rr) P))
  (.seq (mvOut Rr u)
    (callInj ιw (lid _) (postW psR)))))

theorem closed_rotProg (u : Fin Wn) {P : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr}
    (hP : P.Closed) : (rotProg u P).Closed :=
  ⟨closed_callInj _ _ (closed_preW _), closed_mvIn _ _,
    closed_callInj _ _ (closed_callInj _ _ hP), closed_mvOut _ _,
    closed_callInj _ _ (closed_postW _)⟩

/-- The cost bound of the rotation path (`V` the volume of the role array). -/
def rotCost (t : CCoreRT) (C V : ℕ) : ℕ :=
  (hdrCost t + wgCost t + 4) + (8 * V + 4) + C * (V + t.wg + 1) + (8 * V + 4) +
    (4 + dropCost t)

theorem stv_update_role_clean (S : BL Er → List Sym) (hS : KClean S) (u : Fin Wn)
    (l : List Sym) : stv (Function.update S (roleL u) l) (fun _ => []) =
      Function.update S (roleL u) l := by
  refine (stv_of_clean _ ?_).symm
  intro e
  rw [Function.update_of_ne (by simp)]
  exact hS e

/-- **Exact safe run of the rotation path.** -/
theorem safe_rotProg {e C : ℕ} {P : Prog (KLoc (Fin 3) Er) (fun _ => Sym) Rr}
    (hspec : ∀ (w : ℕ) (v : List (List CInt)) (rest r2 : List Sym)
      (S : KLoc (Fin 3) Er → List Sym),
      1 ≤ w → CArrFits w v → CArrFits w (mapC (rotIPowC e) v) → BlkTerm rest → TermOK r2 →
      S (.inl 0) = carrSyms w v ++ rest → S (.inl 2) = natSyms w ++ r2 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (carrSyms w (mapC (rotIPowC e) v) ++ S (.inl 1)))
        (fun _ => True) (C * (cvol w v + w + 1)))
    (hP : P.Closed) (u : Fin Wn) (t : CCoreRT) (tdesc : List Sym) (v : List (List CInt))
    (S : BL Er → List Sym) (hcl : KClean S) (hd : S descL = t.hdr ++ tdesc)
    (hu : S (roleL u) = carrSyms t.wg v ++ [Sym.mark])
    (hf1 : CArrFits t.wg v) (hf2 : CArrFits t.wg (mapC (rotIPowC e) v)) :
    SafeRunsIn ccoreFramed [] (rotProg u P) S
      (Function.update S (roleL u) (carrSyms t.wg (mapC (rotIPowC e) v) ++ [Sym.mark]))
      (fun _ => True) (rotCost t C (cvol t.wg v)) := by
  have hmk : ∀ w (x : List (List CInt)), Sym.mark ∉ carrSyms w x := fun w x =>
    mark_not_mem_arrSyms' _
  have hlen : (carrSyms t.wg (mapC (rotIPowC e) v)).length = cvol t.wg v :=
    cvol_mapC t.wg _ v
  have hw : 1 ≤ t.wg := by simp [CCoreRT.wg]
  -- step 1
  have s1 := safe_callW (Rr := Rr) (closed_preW psR) S (fun _ => []) (scP psR t)
    (by rw [hd]; exact runs_preW psR floorsOK_psR t tdesc _)
  rw [← stv_of_clean S hcl] at s1
  -- step 2
  have s2 := safe_mvIn (Er := Er) Rr u S (scP psR t) (carrSyms t.wg v) (hmk _ _) hu
    (by simp [scP]) (by simp [scP])
  -- step 3
  have s3 := safe_callW (Rr := Rr) (closed_callInj _ _ hP) (Function.update S (roleL u) [Sym.mark])
    (Function.update (scP psR t) .X (carrSyms t.wg v ++ [Sym.mark]))
    (Function.update (Function.update (Function.update (scP psR t) .X
      (carrSyms t.wg v ++ [Sym.mark])) .X [Sym.mark]) .Y
      (carrSyms t.wg (mapC (rotIPowC e) v) ++ [Sym.mark]))
    (runs_rotCall (lR Rr) hspec (a := .X) (b := .Y) (c := .cW) (by decide) (by decide) (by decide)
      Function.injective_id _ _ _
      t.wg v hw hf1 hf2 (by simp) (by simp [scP]) (by simp [scP, scW]))
  -- step 4
  have s4 := safe_mvOut (Er := Er) Rr u (Function.update S (roleL u) [Sym.mark])
    (Function.update (Function.update (Function.update (scP psR t) .X
      (carrSyms t.wg v ++ [Sym.mark])) .X [Sym.mark]) .Y
      (carrSyms t.wg (mapC (rotIPowC e) v) ++ [Sym.mark]))
    (carrSyms t.wg (mapC (rotIPowC e) v)) (hmk _ _) (by simp) (by simp [scP]) (by simp)
  replace s4 := SafeRunsIn.congr s4 (S₂ := stv (Function.update S (roleL u)
    (carrSyms t.wg (mapC (rotIPowC e) v) ++ [Sym.mark])) (scP psR t)) (by
      rw [Function.update_idem]
      congr 1
      funext q
      by_cases hX : q = .X
      · subst hX; simp [scP]
      · by_cases hY : q = .Y
        · subst hY; simp [scP]
        · simp [Function.update_apply, hX, hY]) le_rfl
  -- step 5
  have s5 := safe_callW (Rr := Rr) (closed_postW psR)
    (Function.update S (roleL u) (carrSyms t.wg (mapC (rotIPowC e) v) ++ [Sym.mark]))
    (scP psR t) (fun _ => []) (runs_postW psR floorsOK_psR t _ _)
  rw [stv_update_role_clean S hcl] at s5
  refine SafeRunsIn.mono (SafeRunsIn.seq s1 (SafeRunsIn.seq s2 (SafeRunsIn.seq s3
    (SafeRunsIn.seq s4 s5)))) (fun _ _ => trivial) ?_
  simp only [rotCost, psR, List.length_cons, List.length_nil, hlen, cvol]
  omega

end SubNLogN.Machine.CCore.LeafScalarAux
