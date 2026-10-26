/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafScalarRowLoop
import SubNLogN.Machine.CCore.LeafScalarRowAcc
import SubNLogN.Machine.CCore.LeafScalarRowCost
import SubNLogN.Machine.CCore.LeafScalarVal

/-!
# C-core leaf (10): the scalar row (`CCore/LeafScalarRowTop.lean`)

**Scope (honest summary).** `scalarRow_holds p : ScalarRowStmt p` (`CCore/SkelDefs.lean:288`) for
every `p : LayerParams`, with no hypotheses: cutoff `P₀ = 1`, arithmetic depth `Erow = 1` (inputs
with growth bound `b`, `b + 1 ≤ Δ`), one constant `C` for all rows `(j, ι, r)`.

The kernel of row `par = (j, ι, r)` is `rowProg acc T (List.finRange Wn)`
(`CCore/LeafScalarRowProg.lean`) on the layout `BL Er` (`CCore/LeafPhaseBase.lean`), where
* `T = rowTermsN j ι r` comes from `scalarRowVal_holds` (`CCore/LeafScalarVal.lean:301`): the static
  term lists, with V3 (a source is never updated) and V1 (`gateFn` is `vals u + Σ c • vals s`);
* `acc` are the four accumulation calls of `accW_holds` (`CCore/LeafScalarRowAcc.lean`, built from
  `acc_holds`, `CCore/LeafScalarAcc.lean`).
For every role `u` (in a static list): move role `u` to scratch `X`; for each term `(c, s)` copy role
`s` to `X2` with the certified pass `passC` and replace `X` by `zipC (accC c) X X2`; move `X` back.
Safety for `ccoreFramed` (park and role stacks framed): the role stacks are read only by the
certified passes, which stop at the owned `mark`; everything else is on unframed scratch.
Exactness: on the grid `P + Δ` the accumulation equals the encoding of `gateVal` (halving exact
since `b + 1 ≤ Δ`, `CCore/LeafScalarRowVal.lean`); the sources fit `w_g` since `b ≤ Δ`.
Cost `C · t.volG` with `C = 950 + 19·Cd p + 40·W_c + N·(42 + 6·C_acc)` (`rowCost_le`,
`CCore/LeafScalarRowCost.lean`), `N` a bound, uniform over the finitely many rows, of the total
number of terms (`exists_bound_of_finite`), `C_acc` the constant of `accW_holds`.
Paper: the coefficientwise Gaussian dyadic scalar gates of Lemma A.10(3) (`lem:transfer-phase`)
on the role streams of an internal node (cyclic row split `W_c g + w`, Section A.6
(`sec:transfer-layer`), Proposition A.11); the gates are the scalar rows of the complex triple
network (Definition A.1(b) (`def:fixed-network-premises`), Appendix D.2, [OAI26, §3.1]).
-/

namespace SubNLogN.Machine.CCore.LeafScalarRowAux

/-- A uniform bound of a natural-valued function on a finite type (used for the number of terms of
the finitely many rows; no enumeration of the type). -/
theorem exists_bound_of_finite {β : Type} [Finite β] (f : β → ℕ) : ∃ N, ∀ b, f b ≤ N := by
  obtain ⟨N, hN⟩ := (Set.finite_range f).bddAbove
  exact ⟨N, fun b => hN ⟨b, rfl⟩⟩

end SubNLogN.Machine.CCore.LeafScalarRowAux

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability
open SubNLogN.Math.Common SubNLogN.Math.Walsh SubNLogN.Math.Networks
open SubNLogN.Machine.CCore.LeafScalarAux SubNLogN.Machine.CCore.LeafScalarRowAux
open SubNLogN.Machine.CCore.LeafScalarRowVal

/-- **[LEAF 10] The scalar row kernel exists** (see the module doc): `ScalarRowStmt p` for every
`p`, unconditionally. -/
theorem scalarRow_holds (p : LayerParams) : ScalarRowStmt p := by
  obtain ⟨Er, iF, iD, Rr, iRf, iRn, acc, Cacc, hacc⟩ := LeafScalarRowAcc.accW_holds
  obtain ⟨T, hV3, hV1⟩ := scalarRowVal_holds
  obtain ⟨Nmax, hNmax⟩ : ∃ N, ∀ par : Stage × Fix 100 × Fin 8,
      ((List.finRange Wn).map fun u => (T par.1 par.2.1 par.2.2 u).length).sum ≤ N :=
    exists_bound_of_finite _
  refine ⟨1, 950 + 19 * Cd p + 40 * Wn + Nmax * (42 + 6 * Cacc),
    fun par => ⟨PS ⊕ Er, inferInstance, inferInstance, σ Rr,
    rowProg acc (T par.1 par.2.1 par.2.2) (List.finRange Wn), inferInstance, inferInstance,
    closed_rowProg hacc.1 _ _, ?_⟩⟩
  refine ⟨1, fun t hA' hS w b tdesc S hb hgr hbΔ hcl hd hroles => ?_⟩
  -- read the descriptor, push the floors
  have s0 := safe_callW (Rr := Rr) (closed_preW psS) S (fun _ => []) (scP psS t)
    (by rw [hd]; exact runs_preW psS floorsOK_psS t tdesc _)
  rw [← stv_of_clean S hcl] at s0
  -- pop the floors, drop the counters
  have hpost : ∀ g, SafeRunsIn ccoreFramed [] (callInj ιw (lid (σ Rr)) (postW psS))
      (stv (setRoles S g) (scP psS t)) (setRoles S g) (fun _ => True)
      (psS.length + 1 + dropCost t) := fun g => by
    have h := safe_callW (Rr := Rr) (closed_postW psS) (setRoles S g) (scP psS t) (fun _ => [])
      (runs_postW psS floorsOK_psS t _ _)
    rwa [← stv_of_clean _ (kClean_setRoles S hcl g)] at h
  -- every role
  have hG : t.P + b + 1 ≤ t.P + t.Δ := by omega
  have s1 := safe_roles_all hacc t (layerAddrs (t.A / Wn) t.K t.D t.S hA' hS) w hG
    (fun s x k => (hgr s x k).1)
    (fun s => cArrFits_encArr _ (w s) (hgr s) (by omega))
    (T par.1 par.2.1 par.2.2) (fun u c s h => hV3 _ _ _ u c s h)
    (fun u => gateVal par.1 par.2.1 par.2.2 w u)
    (fun u x k => gateVal_terms _ (hV1 par.1 par.2.1 par.2.2) w u x k) S hcl hroles _ _ hpost
    (List.finRange Wn) (List.nodup_finRange Wn) List.mem_finRange
    (fun u => Enc (compactRT t) hA' hS (gateVal par.1 par.2.1 par.2.2 w u) ++ [Sym.mark])
    (fun _ => rfl)
  -- the cost
  have hV := cvol_le hb hA' hS (fun _ _ => 0) (t.P + t.Δ)
  rw [cvol_encArr] at hV
  refine SafeRunsIn.mono (SafeRunsIn.seq s0 s1) (fun _ _ => trivial) ?_
  have hN := hNmax par
  have hL : (List.finRange Wn).length ≤ Wn := le_of_eq List.length_finRange
  generalize List.finRange Wn = L at hN hL ⊢
  exact LeafScalarRowCost.rowCost_le hb L (fun u => (T par.1 par.2.1 par.2.2 u).length) Nmax
    Cacc _ hL hN hV

end SubNLogN.Machine.CCore
