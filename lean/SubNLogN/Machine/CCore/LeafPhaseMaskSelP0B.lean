/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelP0Kit

/-!
# C-core phase leaf, record-wise sign selection: phase 0, part B (`LeafPhaseMaskSelP0B.lean`)

**Scope (honest summary).** Proves `MaskP0BAux.phase0B_holds : PhaseMaskAux.Phase0BStmt`
(statement, program `phase0B` and cost `cost0B` in `LeafPhaseMaskSelP0Kit.lean`). No
hypotheses beyond the statement's own.

The proof (`phase0B_aux`, for a general chunk count `f` with `j0 + m·f ≤ D`) follows the program:
* `R := D` and `J := j0` (copies);
* the `j0` leading zero chunks (`msCd` on `J`);
* the slot chunks (`msB` over the slot table, an `msU` loop of `f` chunks per slot);
* the trailing zero chunks (`msCd` on `R`);
* the reversal of `Tmp` onto `Msk`;
* the two drops.

Every intermediate state is a `msSt St (p0m …)` state. The emitted chunk lists are kept behind
the definition `memB` (not unfolded by `simp`), so that the `tmpOf` step lemma `tmpOf_rep_succ`
applies.

Helpers are in the namespace `SubNLogN.Machine.CCore.MaskP0BAux`.
-/

namespace SubNLogN.Machine.CCore.MaskP0BAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP Computability
open SubNLogN.Machine.CCore.PhaseMaskAux

/-- The chunks emitted after the prefix and the slot chunks of `done`. -/
def memB (j0 f : ℕ) (done : List Bool) : List Bool :=
  List.replicate j0 false ++ done.flatMap (fun b => List.replicate f b)

theorem memB_nil (j0 f : ℕ) : memB j0 f [] = List.replicate j0 false := by
  simp [memB]

theorem memB_snoc (j0 f : ℕ) (done : List Bool) (b : Bool) :
    memB j0 f (done ++ [b]) = memB j0 f done ++ List.replicate f b := by
  simp [memB, List.flatMap_append]

theorem tmpOf_rep_succ (K ρ : ℕ) (L : List Bool) (b : Bool) (c : ℕ) :
    tmpOf K ρ (L ++ List.replicate (c + 1) b) = List.replicate ρ (Sym.bit false) ++ Sym.bit b ::
      (List.replicate (K - 1 - ρ) (Sym.bit false) ++ tmpOf K ρ (L ++ List.replicate c b)) := by
  rw [List.replicate_succ', ← List.append_assoc, tmpOf_snoc]

theorem tmpOf_rep0_succ (K ρ : ℕ) (b : Bool) (c : ℕ) :
    tmpOf K ρ (List.replicate (c + 1) b) = List.replicate ρ (Sym.bit false) ++ Sym.bit b ::
      (List.replicate (K - 1 - ρ) (Sym.bit false) ++ tmpOf K ρ (List.replicate c b)) := by
  rw [List.replicate_succ', tmpOf_snoc]

theorem runs_fix0 {K' σ : Type} [DecidableEq K'] {P : Prog K' (fun _ => Sym) σ}
    {S S' S'' : K' → List Sym} {Q : σ → Prop} {T T' : ℕ} (h : Runs P S S' Q T) (hS : S' = S'')
    (hT : T ≤ T') : Runs P S S'' (fun _ => True) T' :=
  WP.W9comp.runs_mono (WP.W9comp.runs_congr h hS) (fun _ _ => trivial) hT

section Main

variable {St : ML → List Sym} {ss : Finset (Fin mn)} {K D j0 f ρ : ℕ} {r8 : List Sym}
  {X0 F0 : List Sym}

/-- One chunk of the prefix loop. -/
theorem runs_b3body (hρ : ρ < K) (h8 : TermOK r8) (hS8 : St (nm 8) = natSyms ρ ++ r8)
    (hX0 : X0 = natSyms (K - 1 - ρ)) (T0 : List Sym) (j m : ℕ) :
    Runs (.seq p0DecR (p0Emit false))
      (Function.update (msSt St (p0m T0 X0 F0 (natSyms (D - j)) []
        (tmpOf K ρ (List.replicate j false)) [])) (sc .J) (natSyms m ++ []))
      (Function.update (msSt St (p0m T0 X0 F0 (natSyms (D - (j + 1))) []
        (tmpOf K ρ (List.replicate (j + 1) false)) [])) (sc .J) (natSyms m ++ []))
      (fun _ => True) (8 * D + 30 * K + 40) := by
  rw [update_msSt_inr, update_msSt_inr, upd_p0m_J, upd_p0m_J]
  have d := runs_p0body (St := St) false K ρ hρ r8 h8 hS8 (D - j)
    (p0m T0 X0 F0 (natSyms (D - j)) (natSyms m ++ []) (tmpOf K ρ (List.replicate j false)) [])
    hX0 rfl rfl
  refine runs_fix0 d (msSt_ext fun e => ?_) (by omega)
  rw [tmpOf_rep0_succ]
  cases e <;> simp [Function.update_apply, show D - j - 1 = D - (j + 1) by omega]

/-- One chunk of the slot loop (slot bit `b`, chunk `c` of the slot). -/
theorem runs_b4body (hρ : ρ < K) (h8 : TermOK r8) (hS8 : St (nm 8) = natSyms ρ ++ r8)
    (hX0 : X0 = natSyms (K - 1 - ρ)) (done : List Bool) (b : Bool) (rest : List Bool)
    (c a b' : ℕ) :
    Runs (.seq p0DecR (p0Emit b))
      (Function.update (Function.update (msSt St (p0m (rest.map Sym.bit ++ []) X0 []
        (natSyms (D - j0 - done.length * f - c)) [] (tmpOf K ρ (memB j0 f done ++
          List.replicate c b)) [])) (sc .Fu) (List.replicate a (Sym.bit false) ++ [])) (sc .Fu2)
        (List.replicate b' (Sym.bit false)))
      (Function.update (Function.update (msSt St (p0m (rest.map Sym.bit ++ []) X0 []
        (natSyms (D - j0 - done.length * f - (c + 1))) [] (tmpOf K ρ (memB j0 f done ++
          List.replicate (c + 1) b)) [])) (sc .Fu) (List.replicate a (Sym.bit false) ++ []))
        (sc .Fu2) (List.replicate b' (Sym.bit false)))
      (fun _ => True) (8 * D + 30 * K + 40) := by
  rw [update_msSt_inr, update_msSt_inr, update_msSt_inr, update_msSt_inr]
  have d := runs_p0body (St := St) b K ρ hρ r8 h8 hS8 (D - j0 - done.length * f - c)
    (Function.update (Function.update (p0m (rest.map Sym.bit ++ []) X0 []
      (natSyms (D - j0 - done.length * f - c)) [] (tmpOf K ρ (memB j0 f done ++
        List.replicate c b)) []) .Fu (List.replicate a (Sym.bit false) ++ [])) .Fu2
      (List.replicate b' (Sym.bit false)))
    (by simp [Function.update_apply, hX0]) (by simp [Function.update_apply])
    (by simp [Function.update_apply])
  refine runs_fix0 d (msSt_ext fun e => ?_) (by omega)
  rw [tmpOf_rep_succ]
  cases e <;> simp [Function.update_apply,
    show D - j0 - done.length * f - c - 1 = D - j0 - done.length * f - (c + 1) by omega]

/-- The slot loop body: one slot (`f` chunks of the slot bit `b`). -/
theorem runs_b4slot (hρ : ρ < K) (h8 : TermOK r8) (hS8 : St (nm 8) = natSyms ρ ++ r8)
    (hX0 : X0 = natSyms (K - 1 - ρ)) (hF0 : F0 = List.replicate f (Sym.bit false))
    (done : List Bool) (b : Bool) (rest : List Bool) :
    Runs (if b then msU (sc .Fu) (sc .Fu2) (.seq p0DecR (p0Emit true))
        else msU (sc .Fu) (sc .Fu2) (.seq p0DecR (p0Emit false)))
      (Function.update (msSt St (p0m [] X0 F0 (natSyms (D - j0 - done.length * f)) []
        (tmpOf K ρ (memB j0 f done)) [])) (sc .Tss) (rest.map Sym.bit ++ []))
      (Function.update (msSt St (p0m [] X0 F0 (natSyms (D - j0 - (done ++ [b]).length * f)) []
        (tmpOf K ρ (memB j0 f (done ++ [b]))) [])) (sc .Tss) (rest.map Sym.bit ++ []))
      (fun _ => True) (f * (8 * D + 30 * K + 44) + 3 * f + 6) := by
  have hif : (if b then msU (sc .Fu) (sc .Fu2) (.seq p0DecR (p0Emit true))
      else msU (sc .Fu) (sc .Fu2) (.seq p0DecR (p0Emit false))) =
      msU (sc .Fu) (sc .Fu2) (.seq p0DecR (p0Emit b)) := by cases b <;> rfl
  rw [hif]
  have u := runs_msU (F := sc .Fu) (F2 := sc .Fu2) (by decide) (.seq p0DecR (p0Emit b)) []
    TermOK.nil (fun c => msSt St (p0m (rest.map Sym.bit ++ []) X0 []
      (natSyms (D - j0 - done.length * f - c)) [] (tmpOf K ρ (memB j0 f done ++
        List.replicate c b)) [])) (8 * D + 30 * K + 40)
    (fun c a b' => runs_b4body (D := D) hρ h8 hS8 hX0 done b rest c a b') f
  have e0 : Function.update (msSt St (p0m [] X0 F0 (natSyms (D - j0 - done.length * f)) []
      (tmpOf K ρ (memB j0 f done)) [])) (sc .Tss) (rest.map Sym.bit ++ []) =
      Function.update (Function.update (msSt St (p0m (rest.map Sym.bit ++ []) X0 []
        (natSyms (D - j0 - done.length * f - 0)) [] (tmpOf K ρ (memB j0 f done ++
          List.replicate 0 b)) [])) (sc .Fu) (List.replicate f (Sym.bit false) ++ [])) (sc .Fu2)
        [] := by
    rw [update_msSt_inr, update_msSt_inr, update_msSt_inr]
    exact msSt_ext fun e => by cases e <;> simp [Function.update_apply, hF0]
  have e1 : Function.update (Function.update (msSt St (p0m (rest.map Sym.bit ++ []) X0 []
        (natSyms (D - j0 - done.length * f - f)) [] (tmpOf K ρ (memB j0 f done ++
          List.replicate f b)) [])) (sc .Fu) (List.replicate f (Sym.bit false) ++ [])) (sc .Fu2)
        [] =
      Function.update (msSt St (p0m [] X0 F0 (natSyms (D - j0 - (done ++ [b]).length * f)) []
        (tmpOf K ρ (memB j0 f (done ++ [b]))) [])) (sc .Tss) (rest.map Sym.bit ++ []) := by
    have hl : D - j0 - (done ++ [b]).length * f = D - j0 - done.length * f - f := by
      rw [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
      omega
    rw [hl, memB_snoc, update_msSt_inr, update_msSt_inr, update_msSt_inr]
    exact msSt_ext fun e => by cases e <;> simp [Function.update_apply, hF0]
  exact runs_congr_start (runs_fix0 u e1 (le_of_eq (by ring))) e0.symm

/-- One chunk of the trailing loop. -/
theorem runs_b5body (hρ : ρ < K) (h8 : TermOK r8) (hS8 : St (nm 8) = natSyms ρ ++ r8)
    (hX0 : X0 = natSyms (K - 1 - ρ)) (L : List Bool) (j m : ℕ) :
    Runs (p0Emit false)
      (Function.update (msSt St (p0m [] X0 F0 [] [] (tmpOf K ρ (L ++ List.replicate j false)) []))
        (sc .R) (natSyms m ++ []))
      (Function.update (msSt St (p0m [] X0 F0 [] []
        (tmpOf K ρ (L ++ List.replicate (j + 1) false)) [])) (sc .R) (natSyms m ++ []))
      (fun _ => True) (30 * K + 30) := by
  rw [update_msSt_inr, update_msSt_inr, upd_p0m_R, upd_p0m_R]
  have d := runs_msSt_emit (St := St) (m := p0m [] X0 F0 (natSyms m ++ []) []
    (tmpOf K ρ (L ++ List.replicate j false)) []) false (K - 1 - ρ) ρ r8 h8 hS8
    (by simp [hX0]) rfl
  rw [upd_p0m_Tmp, p0m_Tmp, ← tmpOf_rep_succ] at d
  exact runs_fix0 d rfl (by omega)

end Main

/-- **Phase 0, part B**, for a general chunk count `f` (`j0 + m·f ≤ D`). -/
theorem phase0B_aux (ss : Finset (Fin mn)) (K D j0 f ρ : ℕ) (r4 r6 r8 : List Sym)
    (St : ML → List Sym) (hρ : ρ < K) (hjD : j0 + mn * f ≤ D)
    (h4 : TermOK r4) (h6 : TermOK r6) (h8 : TermOK r8)
    (hS4 : St (nm 4) = natSyms D ++ r4) (hS6 : St (nm 6) = natSyms j0 ++ r6)
    (hS8 : St (nm 8) = natSyms ρ ++ r8) :
    Runs phase0B
      (msSt St (p0m ((slotBools ss).map Sym.bit) (natSyms (K - 1 - ρ))
        (List.replicate f (Sym.bit false)) [] [] [] []))
      (msSt St (p0m [] [] [] [] [] [] ((maskMSB K ρ (membList ss j0 f D)).map Sym.bit)))
      (fun _ => True)
      ((7 * D + 7) + (7 * j0 + 7) + (j0 * (8 * D + 30 * K + 40 + 8 * j0 + 13) + 2) +
        (mn * (f * (8 * D + 30 * K + 44) + 3 * f + 6 + 4) + 2) +
        (D * (30 * K + 30 + 8 * D + 13) + 2) + (3 * (K * D) + 4) + (3 * K + 2) + (3 * f + 2)) := by
  obtain ⟨T0, hT0⟩ : ∃ T0, T0 = (slotBools ss).map Sym.bit := ⟨_, rfl⟩
  obtain ⟨X0, hX0⟩ : ∃ X0, X0 = natSyms (K - 1 - ρ) := ⟨_, rfl⟩
  obtain ⟨F0, hF0⟩ : ∃ F0, F0 = List.replicate f (Sym.bit false) := ⟨_, rfl⟩
  rw [← hT0, ← hX0, ← hF0]
  have hlenB : (slotBools ss).length = mn := by
    rw [slotBools, List.length_map, List.length_finRange]
  -- B1: `R := D`
  have b1 : Runs (msLift (copyBlock (nm 4) (sc .R) (sc .C2)))
      (msSt St (p0m T0 X0 F0 [] [] [] [])) (msSt St (p0m T0 X0 F0 (natSyms D) [] [] []))
      (fun _ => True) (7 * bitLen D + 7) := by
    have h := runs_msSt_cb0 (St := St) (m := p0m T0 X0 F0 [] [] [] []) (src := nm 4) (e := .R)
      (e2 := .C2) (by decide) (by decide) (by decide) D r4 h4 hS4 rfl
    rw [upd_p0m_R] at h
    exact h
  -- B2: `J := j0`
  have b2 : Runs (msLift (copyBlock (nm 6) (sc .J) (sc .C2)))
      (msSt St (p0m T0 X0 F0 (natSyms D) [] [] []))
      (msSt St (p0m T0 X0 F0 (natSyms D) (natSyms j0) [] []))
      (fun _ => True) (7 * bitLen j0 + 7) := by
    have h := runs_msSt_cb0 (St := St) (m := p0m T0 X0 F0 (natSyms D) [] [] []) (src := nm 6)
      (e := .J) (e2 := .C2) (by decide) (by decide) (by decide) j0 r6 h6 hS6 rfl
    rw [upd_p0m_J] at h
    exact h
  -- B3: the `j0` leading zero chunks
  have b3 : Runs (msCd (sc .J) (sc .U) (.seq p0DecR (p0Emit false)))
      (msSt St (p0m T0 X0 F0 (natSyms D) (natSyms j0) [] []))
      (msSt St (p0m T0 X0 F0 (natSyms (D - j0)) [] (tmpOf K ρ (List.replicate j0 false)) []))
      (fun _ => True) (j0 * (8 * D + 30 * K + 40 + 8 * bitLen j0 + 13) + 2) := by
    have h := runs_msCd (C := sc .J) (U := sc .U) (by decide) (.seq p0DecR (p0Emit false)) []
      TermOK.nil (fun j => msSt St (p0m T0 X0 F0 (natSyms (D - j)) []
        (tmpOf K ρ (List.replicate j false)) [])) (8 * D + 30 * K + 40)
      (fun j m => runs_b3body (F0 := F0) hρ h8 hS8 hX0 T0 j m) j0
    have e0 : Function.update (msSt St (p0m T0 X0 F0 (natSyms (D - 0)) []
        (tmpOf K ρ (List.replicate 0 false)) [])) (sc .J) (natSyms j0 ++ []) =
        msSt St (p0m T0 X0 F0 (natSyms D) (natSyms j0) [] []) := by
      rw [update_msSt_inr, upd_p0m_J]
      exact msSt_ext fun e => by cases e <;> simp [tmpOf_nil]
    have e1 : Function.update (msSt St (p0m T0 X0 F0 (natSyms (D - j0)) []
        (tmpOf K ρ (List.replicate j0 false)) [])) (sc .J) [] =
        msSt St (p0m T0 X0 F0 (natSyms (D - j0)) [] (tmpOf K ρ (List.replicate j0 false)) []) := by
      rw [update_msSt_inr, upd_p0m_J]
    exact runs_congr_start (WP.W9comp.runs_congr h e1) e0
  -- B4: the slot chunks
  have b4 : Runs (msB (sc .Tss) (msU (sc .Fu) (sc .Fu2) (.seq p0DecR (p0Emit true)))
        (msU (sc .Fu) (sc .Fu2) (.seq p0DecR (p0Emit false))))
      (msSt St (p0m T0 X0 F0 (natSyms (D - j0)) [] (tmpOf K ρ (List.replicate j0 false)) []))
      (msSt St (p0m [] X0 F0 (natSyms (D - j0 - mn * f)) []
        (tmpOf K ρ (memB j0 f (slotBools ss))) []))
      (fun _ => True) (mn * (f * (8 * D + 30 * K + 44) + 3 * f + 6 + 4) + 2) := by
    have h := runs_msB (T := sc .Tss) (msU (sc .Fu) (sc .Fu2) (.seq p0DecR (p0Emit true)))
      (msU (sc .Fu) (sc .Fu2) (.seq p0DecR (p0Emit false))) [] TermOK.nil
      (fun done => msSt St (p0m [] X0 F0 (natSyms (D - j0 - done.length * f)) []
        (tmpOf K ρ (memB j0 f done)) []))
      (f * (8 * D + 30 * K + 44) + 3 * f + 6)
      (fun done b rest => runs_b4slot hρ h8 hS8 hX0 hF0 done b rest) (slotBools ss)
    have e0 : Function.update (msSt St (p0m [] X0 F0
        (natSyms (D - j0 - ([] : List Bool).length * f)) [] (tmpOf K ρ (memB j0 f [])) []))
        (sc .Tss) ((slotBools ss).map Sym.bit ++ []) =
        msSt St (p0m T0 X0 F0 (natSyms (D - j0)) [] (tmpOf K ρ (List.replicate j0 false)) []) := by
      rw [update_msSt_inr, upd_p0m_Tss]
      exact msSt_ext fun e => by cases e <;> simp [memB_nil, hT0]
    have e1 : Function.update (msSt St (p0m [] X0 F0
        (natSyms (D - j0 - (slotBools ss).length * f)) []
        (tmpOf K ρ (memB j0 f (slotBools ss))) [])) (sc .Tss) [] =
        msSt St (p0m [] X0 F0 (natSyms (D - j0 - mn * f)) []
          (tmpOf K ρ (memB j0 f (slotBools ss))) []) := by
      rw [update_msSt_inr, upd_p0m_Tss, hlenB]
    have h' := runs_congr_start (WP.W9comp.runs_congr h e1) e0
    rw [hlenB] at h'
    exact h'
  -- B5: the trailing zero chunks
  have b5 : Runs (msCd (sc .R) (sc .U) (p0Emit false))
      (msSt St (p0m [] X0 F0 (natSyms (D - j0 - mn * f)) []
        (tmpOf K ρ (memB j0 f (slotBools ss))) []))
      (msSt St (p0m [] X0 F0 [] [] (tmpOf K ρ (memB j0 f (slotBools ss) ++
        List.replicate (D - j0 - mn * f) false)) []))
      (fun _ => True)
      ((D - j0 - mn * f) * (30 * K + 30 + 8 * bitLen (D - j0 - mn * f) + 13) + 2) := by
    have h := runs_msCd (C := sc .R) (U := sc .U) (by decide) (p0Emit false) [] TermOK.nil
      (fun j => msSt St (p0m [] X0 F0 [] [] (tmpOf K ρ (memB j0 f (slotBools ss) ++
        List.replicate j false)) [])) (30 * K + 30)
      (fun j m => runs_b5body (F0 := F0) hρ h8 hS8 hX0 (memB j0 f (slotBools ss)) j m)
      (D - j0 - mn * f)
    have e0 : Function.update (msSt St (p0m [] X0 F0 [] [] (tmpOf K ρ (memB j0 f (slotBools ss) ++
        List.replicate 0 false)) [])) (sc .R) (natSyms (D - j0 - mn * f) ++ []) =
        msSt St (p0m [] X0 F0 (natSyms (D - j0 - mn * f)) []
          (tmpOf K ρ (memB j0 f (slotBools ss))) []) := by
      rw [update_msSt_inr, upd_p0m_R]
      exact msSt_ext fun e => by cases e <;> simp
    have e1 : Function.update (msSt St (p0m [] X0 F0 [] [] (tmpOf K ρ (memB j0 f (slotBools ss) ++
        List.replicate (D - j0 - mn * f) false)) [])) (sc .R) [] =
        msSt St (p0m [] X0 F0 [] [] (tmpOf K ρ (memB j0 f (slotBools ss) ++
          List.replicate (D - j0 - mn * f) false)) []) := by
      rw [update_msSt_inr, upd_p0m_R]
    exact runs_congr_start (WP.W9comp.runs_congr h e1) e0
  -- B6: reverse `Tmp` onto `Msk`
  have hmem : memB j0 f (slotBools ss) ++ List.replicate (D - j0 - mn * f) false =
      membList ss j0 f D := by
    simp only [memB, membList, slots_eq, Nat.sub_sub]
  have b6 : Runs (msLift (moveBlock (sc .Tmp) (sc .Msk)))
      (msSt St (p0m [] X0 F0 [] [] (tmpOf K ρ (memB j0 f (slotBools ss) ++
        List.replicate (D - j0 - mn * f) false)) []))
      (msSt St (p0m [] X0 F0 [] [] [] ((maskMSB K ρ (membList ss j0 f D)).map Sym.bit)))
      (fun _ => True) (3 * (K * D) + 4) := by
    have h := runs_msSt_mb (St := St) (m := p0m [] X0 F0 [] [] (tmpOf K ρ
      (memB j0 f (slotBools ss) ++ List.replicate (D - j0 - mn * f) false)) []) (e := .Tmp)
      (e' := .Msk) (by decide) (maskMSB K ρ (membList ss j0 f D)).reverse [] TermOK.nil
      (by rw [p0m_Tmp, hmem]; simp [tmpOf])
    rw [upd_p0m_Tmp, upd_p0m_Msk, p0m_Msk, List.reverse_reverse, List.append_nil] at h
    refine runs_fix0 h rfl (le_of_eq ?_)
    rw [List.length_reverse, length_maskMSB K ρ hρ, length_membList ss j0 f D hjD]
  -- B7: drop `X`
  have b7 : Runs (msDropBits (sc .X))
      (msSt St (p0m [] X0 F0 [] [] [] ((maskMSB K ρ (membList ss j0 f D)).map Sym.bit)))
      (msSt St (p0m [] [] F0 [] [] [] ((maskMSB K ρ (membList ss j0 f D)).map Sym.bit)))
      (fun _ => True) (3 * bitLen (K - 1 - ρ) + 2) := by
    have h := runs_msSt_drop (St := St) (m := p0m [] X0 F0 [] [] []
      ((maskMSB K ρ (membList ss j0 f D)).map Sym.bit)) .X (encodeNat (K - 1 - ρ)) [] TermOK.nil
      (by rw [p0m_X, hX0, natSyms_eq_map_m, List.append_nil])
    rw [upd_p0m_X] at h
    exact h
  -- B8: drop `Fu`
  have b8 : Runs (msDropBits (sc .Fu))
      (msSt St (p0m [] [] F0 [] [] [] ((maskMSB K ρ (membList ss j0 f D)).map Sym.bit)))
      (msSt St (p0m [] [] [] [] [] [] ((maskMSB K ρ (membList ss j0 f D)).map Sym.bit)))
      (fun _ => True) (3 * f + 2) := by
    have h := runs_msSt_drop (St := St) (m := p0m [] [] F0 [] [] []
      ((maskMSB K ρ (membList ss j0 f D)).map Sym.bit)) .Fu (List.replicate f false) [] TermOK.nil
      (by rw [p0m_Fu, hF0]; simp)
    rw [upd_p0m_Fu] at h
    exact runs_fix0 h rfl (by simp)
  -- compose
  have hall := WP.W9comp.runs_seq b1 (WP.W9comp.runs_seq b2 (WP.W9comp.runs_seq b3
    (WP.W9comp.runs_seq b4 (WP.W9comp.runs_seq b5 (WP.W9comp.runs_seq b6
      (WP.W9comp.runs_seq b7 b8))))))
  refine runs_fix0 hall rfl ?_
  have hbD := bitLen_le_self_m D
  have hbj := bitLen_le_self_m j0
  have hbX := bitLen_le_self_m (K - 1 - ρ)
  have hbR := bitLen_le_self_m (D - j0 - mn * f)
  have m1 : j0 * (8 * D + 30 * K + 40 + 8 * bitLen j0 + 13) ≤
      j0 * (8 * D + 30 * K + 40 + 8 * j0 + 13) := Nat.mul_le_mul_left _ (by omega)
  have m2 : (D - j0 - mn * f) * (30 * K + 30 + 8 * bitLen (D - j0 - mn * f) + 13) ≤
      D * (30 * K + 30 + 8 * D + 13) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- **Phase 0, part B** (`Phase0BStmt`). -/
theorem phase0B_holds : PhaseMaskAux.Phase0BStmt := by
  intro ss K D j0 k ρ r4 r6 r8 St hk hρ hD h4 h6 h8 hS4 hS6 hS8
  have hmf : mn ^ k = mn * mn ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  have hjD : j0 + mn * mn ^ (k - 1) ≤ D := by rw [← hmf]; exact hD
  exact phase0B_aux ss K D j0 (mn ^ (k - 1)) ρ r4 r6 r8 St hρ hjD h4 h6 h8 hS4 hS6 hS8

end SubNLogN.Machine.CCore.MaskP0BAux
