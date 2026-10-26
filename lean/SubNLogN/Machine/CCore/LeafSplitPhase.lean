/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafSplitLay

/-!
# C-core leaves 6-7 (split / collect), part 5: work-stack phases and lengths
(`CCore/LeafSplitPhase.lean`)

Proved here (no hypotheses):
* `safe_initCtr`: guards on `TT`, `CD2`; copy of the header fields `K, D, S`; `K·D` zero bits;
  ends with the row-size counter `natSyms (2^(K·D)·S) ++ [mark]` on `CB` (`wkMid`).
* `safe_cleanup`: erases every work stack (`wkMid → []`).
* length facts: `vol (recs t z) = M·(2·r·w_g + 1)`, `(recs t z).length = A·B`, and the compact
  volume `W·M_c = M`.
-/

namespace SubNLogN.Machine.CCore.LeafSplitAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
open SubNLogN.Machine.CCore SubNLogN.Math.Walsh

/-- The work stacks between the counter phase and the clean-up. -/
def wkMid (B D : ℕ) : Fin 6 → List Sym := fun i =>
  if i = iCB then natSyms B ++ [Sym.mark] else if i = iCD then natSyms D ++ [Sym.mark]
  else if i = iHT then [] else [Sym.mark]

section Phases

variable {E₂ : Type} [DecidableEq E₂]

/-- The counter phase. -/
def initCtr : SProg (CL (SE E₂)) :=
  .seq (pushC (wkL iTT) .mark) (.seq (pushC (wkL iCD2) .mark)
    (.seq (hdrKDS descL (wkL iHT) (wkL iCB) (wkL iCD) (wkL iCK))
      (pushZeros (wkL iCK) (wkL iCD) (wkL iCD2) (wkL iTT) (wkL iCB))))

/-- The clean-up phase. -/
def cleanup : SProg (CL (SE E₂)) :=
  .seq (popR (wkL iTT)) (.seq (popR (wkL iCD2)) (.seq (popR (wkL iCK))
    (.seq (passE .mark (wkL iCB)) (.seq (popR (wkL iCB))
      (.seq (passE .mark (wkL iCD)) (popR (wkL iCD)))))))

theorem closed_initCtr : (initCtr (E₂ := E₂)).Closed := by
  refine ⟨?_, ?_, closed_hdrKDS _ _ _ _ _, closed_pushZeros _ _ _ _ _⟩ <;>
    simp [Prog.Closed, Prog.FreeBelow, pushC]

theorem closed_cleanup : (cleanup (E₂ := E₂)).Closed := by
  simp [cleanup, Prog.Closed, Prog.FreeBelow, popR, passE, passEBody, peekR]

theorem safe_pushC_wk {framed : CL (SE E₂) → Prop} (i : Fin 6) (a : Sym) (io desc park : List Sym)
    (R : Fin Wn → List Sym) (wk : Fin 6 → List Sym) (Bf : Fin Wn → List Sym) (ex : E₂ → List Sym)
    (ρ : List (SProg (CL (SE E₂)))) :
    SafeRunsIn framed ρ (pushC (wkL i) a) (mkS io desc park R wk Bf ex)
      (mkS io desc park R (Function.update wk i (a :: wk i)) Bf ex) (fun _ => True) 1 := by
  have h := (safe_pushC (wkL i) a (mkS io desc park R wk Bf ex) ρ).mono_framed
    (framed' := framed) (fun _ _ => trivial)
  rw [mkS_upd_wk] at h
  exact h

theorem safe_popR_wk {framed : CL (SE E₂) → Prop} (i : Fin 6) (a : Sym) (l : List Sym)
    (io desc park : List Sym) (R : Fin Wn → List Sym) (wk : Fin 6 → List Sym)
    (Bf : Fin Wn → List Sym) (ex : E₂ → List Sym) (h : wk i = a :: l)
    (ρ : List (SProg (CL (SE E₂)))) :
    SafeRunsIn framed ρ (popR (wkL i)) (mkS io desc park R wk Bf ex)
      (mkS io desc park R (Function.update wk i l) Bf ex) (fun _ => True) 1 := by
  have h' := (safe_popR (wkL i) a l (mkS io desc park R wk Bf ex) h ρ).mono_framed
    (framed' := framed) (fun _ _ => trivial)
  rw [mkS_upd_wk] at h'
  exact h'.mono (fun _ _ => trivial) le_rfl

theorem safe_passE_wk {framed : CL (SE E₂) → Prop} (i : Fin 6) (xs ts : List Sym)
    (hg : Sym.mark ∉ xs) (io desc park : List Sym) (R : Fin Wn → List Sym)
    (wk : Fin 6 → List Sym) (Bf : Fin Wn → List Sym) (ex : E₂ → List Sym)
    (h : wk i = xs ++ Sym.mark :: ts) (ρ : List (SProg (CL (SE E₂)))) :
    SafeRunsIn framed ρ (passE .mark (wkL i)) (mkS io desc park R wk Bf ex)
      (mkS io desc park R (Function.update wk i (Sym.mark :: ts)) Bf ex) (fun _ => True)
      (3 * xs.length + 2) := by
  have h' := (safe_passE (src := wkL i) xs ts hg (mkS io desc park R wk Bf ex) h ρ).mono_framed
    (framed' := framed) (fun _ _ => trivial)
  rw [mkS_upd_wk] at h'
  exact h'.mono (fun _ _ => trivial) le_rfl

theorem termOK_nil' : TermOK [] := fun _ hd => by simp at hd

theorem termOK_mark' (l : List Sym) : TermOK (Sym.mark :: l) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  rfl

theorem safe_hdrKDS_mkS (t : CCoreRT) (io park tdesc : List Sym) (R : Fin Wn → List Sym)
    (w : Fin 6 → List Sym) (Bf : Fin Wn → List Sym) (ex : E₂ → List Sym) (hw : w iHT = [])
    (ρ : List (SProg (CL (SE E₂)))) :
    SafeRunsIn ccoreFramed ρ (hdrKDS descL (wkL iHT) (wkL iCB) (wkL iCD) (wkL iCK))
      (mkS io (t.hdr ++ tdesc) park R w Bf ex)
      (mkS io (t.hdr ++ tdesc) park R (Function.update (Function.update (Function.update w iCB
        (natSyms t.S ++ Sym.mark :: w iCB)) iCD (natSyms t.D ++ Sym.mark :: w iCD)) iCK
        (natSyms t.K ++ Sym.mark :: w iCK)) Bf ex) (fun _ => True) (13 * t.hdr.length + 100) := by
  have h := safe_hdrKDS (framed := ccoreFramed) (desc := descL) (ht := wkL (E₂ := E₂) iHT)
    (cS := wkL iCB) (cD := wkL iCD) (cK := wkL iCK) (by simp [ccoreFramed])
    (by simp [ccoreFramed]) (by simp) (by simp) (by simp) (by simp) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT])
    (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) t.P t.d t.r t.Δ t.A t.R t.K t.D t.S t.j0
    t.k t.ρ tdesc (mkS io (t.hdr ++ tdesc) park R w Bf ex) rfl
    (by show TermOK (w iHT); rw [hw]; exact termOK_nil') ρ
  rw [mkS_upd_wk, mkS_upd_wk, mkS_upd_wk] at h
  exact h

theorem safe_pushZeros_mkS (fK fD : ℕ) (io desc park : List Sym) (R : Fin Wn → List Sym)
    (w : Fin 6 → List Sym) (Bf : Fin Wn → List Sym) (ex : E₂ → List Sym)
    (hK : w iCK = natSyms fK ++ [Sym.mark]) (hD : w iCD = natSyms fD ++ [Sym.mark])
    (hD2 : w iCD2 = [Sym.mark]) (htt : w iTT = [Sym.mark]) (ρ : List (SProg (CL (SE E₂)))) :
    SafeRunsIn ccoreFramed ρ (pushZeros (wkL iCK) (wkL iCD) (wkL iCD2) (wkL iTT) (wkL iCB))
      (mkS io desc park R w Bf ex)
      (mkS io desc park R (Function.update (Function.update w iCK [Sym.mark]) iCB
        (List.replicate (fK * fD) (Sym.bit false) ++ w iCB)) Bf ex) (fun _ => True)
      (countdownCost (fun _ => 9 * bitLen fD + 4 + countdownCost (fun _ => 1) fD) fK) := by
  have h := (safe_pushZeros (cK := wkL (E₂ := E₂) iCK) (cD := wkL iCD) (cD2 := wkL iCD2)
    (tt := wkL iTT) (cb := wkL iCB) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT])
    (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) (by simp [iTT, iCB, iCD, iCK, iCD2, iHT]) fK fD [Sym.mark] [] [] []
    (termOK_mark' []) (by simp) (mkS io desc park R w Bf ex) hK hD hD2 htt ρ).mono_framed
    (framed' := ccoreFramed) (fun _ _ => trivial)
  rw [mkS_upd_wk, mkS_upd_wk] at h
  exact h

/-- Cost of the counter phase. -/
def initCost (t : CCoreRT) : ℕ :=
  2 + (13 * t.hdr.length + 100) +
    countdownCost (fun _ => 9 * bitLen t.D + 4 + countdownCost (fun _ => 1) t.D) t.K

theorem safe_initCtr (t : CCoreRT) (hS : 0 < t.S) (io park tdesc : List Sym)
    (R Bf : Fin Wn → List Sym) (ex : E₂ → List Sym) (ρ : List (SProg (CL (SE E₂)))) :
    SafeRunsIn ccoreFramed ρ initCtr (mkS io (t.hdr ++ tdesc) park R (fun _ => []) Bf ex)
      (mkS io (t.hdr ++ tdesc) park R (wkMid (rowSz t) t.D) Bf ex) (fun _ => True)
      (initCost t) := by
  refine (SafeRunsIn.seq (safe_pushC_wk iTT Sym.mark io (t.hdr ++ tdesc) park R (fun _ => []) Bf
      ex ρ) (SafeRunsIn.seq (safe_pushC_wk iCD2 Sym.mark io (t.hdr ++ tdesc) park R _ Bf ex ρ)
      (SafeRunsIn.seq (safe_hdrKDS_mkS t io park tdesc R _ Bf ex ?hw ρ)
        (safe_pushZeros_mkS t.K t.D io (t.hdr ++ tdesc) park R _ Bf ex ?hK ?hD ?hD2 ?htt ρ)))).congr
    ?heq ?hcost
  case hw => simp [Function.update_apply, iTT, iCB, iCD, iCK, iCD2, iHT]
  case hK => simp [Function.update_apply, iTT, iCB, iCD, iCK, iCD2, iHT]
  case hD => simp [Function.update_apply, iTT, iCB, iCD, iCK, iCD2, iHT]
  case hD2 => simp [Function.update_apply, iTT, iCB, iCD, iCK, iCD2, iHT]
  case htt => simp [Function.update_apply, iTT, iCB, iCD, iCK, iCD2, iHT]
  case heq =>
    congr 1
    funext i
    fin_cases i <;> simp [wkMid, Function.update_apply, natSyms_two_pow_mul _ hS, iTT, iCB, iCD, iCK, iCD2, iHT]
  case hcost =>
    unfold initCost
    omega

theorem safe_cleanup (B D : ℕ) (io desc park : List Sym) (R Bf : Fin Wn → List Sym)
    (ex : E₂ → List Sym) (ρ : List (SProg (CL (SE E₂)))) :
    SafeRunsIn ccoreFramed ρ cleanup (mkS io desc park R (wkMid B D) Bf ex)
      (mkS io desc park R (fun _ => []) Bf ex) (fun _ => True)
      (3 * bitLen B + 3 * bitLen D + 11) := by
  refine (SafeRunsIn.seq (safe_popR_wk iTT Sym.mark [] io desc park R (wkMid B D) Bf ex ?h1 ρ)
    (SafeRunsIn.seq (safe_popR_wk iCD2 Sym.mark [] io desc park R _ Bf ex ?h2 ρ)
    (SafeRunsIn.seq (safe_popR_wk iCK Sym.mark [] io desc park R _ Bf ex ?h3 ρ)
    (SafeRunsIn.seq (safe_passE_wk iCB (natSyms B) [] (mark_not_mem_natSyms B) io desc park R _
      Bf ex ?h4 ρ)
    (SafeRunsIn.seq (safe_popR_wk iCB Sym.mark [] io desc park R _ Bf ex ?h5 ρ)
    (SafeRunsIn.seq (safe_passE_wk iCD (natSyms D) [] (mark_not_mem_natSyms D) io desc park R _
      Bf ex ?h6 ρ)
      (safe_popR_wk iCD Sym.mark [] io desc park R _ Bf ex ?h7 ρ))))))).congr ?heq ?hcost
  case h1 => simp [wkMid, iTT, iCB, iCD, iCK, iCD2, iHT]
  case h2 => simp [wkMid, Function.update_apply, iTT, iCB, iCD, iCK, iCD2, iHT]
  case h3 => simp [wkMid, Function.update_apply, iTT, iCB, iCD, iCK, iCD2, iHT]
  case h4 => simp [wkMid, Function.update_apply, iTT, iCB, iCD, iCK, iCD2, iHT]
  case h5 => simp [wkMid, Function.update_apply, iTT, iCB, iCD, iCK, iCD2, iHT]
  case h6 => simp [wkMid, Function.update_apply, iTT, iCB, iCD, iCK, iCD2, iHT]
  case h7 => simp [wkMid, Function.update_apply, iTT, iCB, iCD, iCK, iCD2, iHT]
  case heq =>
    congr 1
    funext i
    fin_cases i <;> simp [wkMid, Function.update_apply, iTT, iCB, iCD, iCK, iCD2, iHT]
  case hcost =>
    simp only [length_natSyms]
    omega

end Phases

/-! ## Lengths -/

theorem length_twosBits (w : ℕ) (z : ℤ) : (twosBits w z).length = w := by
  simp [twosBits, bitsLE]

theorem length_crecBits (w : ℕ) (cs : List CInt) : (crecBits w cs).length = cs.length * (2 * w) := by
  induction cs with
  | nil => simp [crecBits]
  | cons c cs ih =>
    simp only [crecBits, List.flatMap_cons, List.length_append] at ih ⊢
    simp [coefBits, length_twosBits, ih]
    ring

theorem length_recOf (t : CCoreRT) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r)
    (x : LayerAddr t.A t.K t.D t.S) : (recOf t z x).length = 2 * t.r * t.wg := by
  simp [recOf, length_crecBits]
  ring

theorem arrSyms_length_const (c : ℕ) :
    ∀ v : List (List Bool), (∀ p ∈ v, p.length = c) → (arrSyms v).length = v.length * (c + 1)
  | [], _ => by simp [arrSyms, blk]
  | p :: v, h => by
    have ih := arrSyms_length_const c v (fun q hq => h q (List.mem_cons_of_mem p hq))
    have hp := h p List.mem_cons_self
    simp only [arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append] at ih ⊢
    simp [recSyms, hp, ih]
    ring

theorem length_recs (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) : (recs t hA hS z).length = t.A * rowSz t := by
  simp [recs, layerAddrs]
  ring

theorem vol_recs (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) :
    vol (recs t hA hS z) = t.M * (2 * t.r * t.wg + 1) := by
  unfold vol
  rw [arrSyms_length_const (2 * t.r * t.wg) _ (fun p hp => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hp
    exact length_recOf t z x), length_recs]
  unfold CCoreRT.M rowSz
  ring

theorem compact_M (t : CCoreRT) (hW : Wn ∣ t.A) : Wn * (compactRT t).M = t.M := by
  unfold CCoreRT.M compactRT
  simp only
  rw [← Nat.mul_div_cancel' hW]
  ring_nf
  rw [Nat.mul_div_cancel_left _ Wn_pos']

end SubNLogN.Machine.CCore.LeafSplitAux
