/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafSplitProg

/-!
# C-core leaf 7: collect with the fused relabel (`CCore/LeafSplitCollect.lean`)

**Proved:** `SubNLogN.Machine.CCore.collect_holds (p) : CollectStmt p` (`CCore/SkelDefs.lean:243`),
with no hypotheses, for every static `π : Equiv.Perm (Fin W_c)`. Paper: the inverse of the cyclic
row split of an internal node (Section A.6 (`sec:transfer-layer`), Proposition A.11), stream
primitive (4) of Lemma A.4 (`lem:transfer-streams`), with the final relabel
of the node fused into the merge order.

Program (`collectProg π P₃`, one closed program per static `π`; private scratch `SE E₃`):
1. `preC`: the counter phase (`initCtr`), then for every role `u`: pass S from role stack `u`
   (guarded by its owned `mark`, so every read is on a non-empty framed stack) onto buffer `u`,
   and pop the owned `mark`;
2. the K2 block merge with class order `π` (`k2MergeBlk_holds W π`, embedded by `callInj` along
   `ιK`, image unframed): round `t` appends row `t` of buffers `π 0, …, π (W-1)` to `io`;
3. `cleanup`.
Value layer: `mergeBlocks_recs` (`CCore/LeafSplitVal.lean`). Cost `C·V_g`,
`C = 3·C₃ + 7·W + 201`.
-/

namespace SubNLogN.Machine.CCore.LeafSplitAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
open SubNLogN.Machine.CCore SubNLogN.Math.Walsh

section Collect

variable {E₂ R₂ : Type} [DecidableEq E₂]

/-- The part before the K2 merge. -/
def preC : SProg (CL (SE E₂)) :=
  .seq initCtr
    (forEachFin Wn (fun u => .seq (passS .mark (roleL u) (wkL iTT) (bufL u)) (popR (roleL u))))

theorem closed_preC : (preC (E₂ := E₂)).Closed :=
  closed_seq_forEachFin' Wn _ _ closed_initCtr (fun _ => WP.W9comp.closed_seq
    (WP.W9comp.closed_seq (closed_passM _ _ _) (closed_passM _ _ _))
    (by simp [Prog.Closed, Prog.FreeBelow, popR]))

/-- **The collect program** for the K2 merge program `P₃`. -/
def collectProg (P₃ : Prog (KLoc (Fin 2 ⊕ Fin Wn) E₂) (fun _ => Sym) R₂) :
    Prog (CL (SE E₂)) (fun _ => Sym) (Option Sym × R₂) :=
  .seq ((preC (E₂ := E₂)).liftRegs (Lens.fst (Option Sym) R₂))
    (.seq (callInj ιK (Lens.snd (Option Sym) R₂) P₃)
      ((cleanup (E₂ := E₂)).liftRegs (Lens.fst (Option Sym) R₂)))

theorem closed_collectProg (P₃ : Prog (KLoc (Fin 2 ⊕ Fin Wn) E₂) (fun _ => Sym) R₂)
    (hcl : P₃.Closed) : (collectProg P₃).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs _ closed_preC)
    (WP.W9comp.closed_seq (closed_callInj _ _ hcl) (WP.W9comp.closed_liftRegs _ closed_cleanup))

theorem safe_rolesToBufs (R : Fin Wn → List Sym) (io desc park : List Sym) (B D : ℕ)
    (ex : E₂ → List Sym) (T : ℕ) (hlen : ∀ u, (R u).length = T)
    (hm : ∀ u, Sym.mark ∉ R u) (ρ : List (SProg (CL (SE E₂)))) :
    SafeRunsIn ccoreFramed ρ
      (forEachFin Wn (fun u => .seq (passS .mark (roleL u) (wkL iTT) (bufL (E₂ := E₂) u))
        (popR (roleL u))))
      (mkS io desc park (fun u => R u ++ [Sym.mark]) (wkMid B D) (fun _ => []) ex)
      (mkS io desc park (fun _ => []) (wkMid B D) R ex) (fun _ => True) (Wn * (8 * T + 5) + 1) := by
  refine safe_forEachFin_rb _ (8 * T + 5) io desc park (wkMid B D) ex (fun u => R u ++ [Sym.mark])
    (fun _ => []) (fun _ => []) R (fun u Rr Bf hR hB => ?_)
  have h1 := (safe_passS (src := roleL u) (tmp := wkL iTT) (dst := bufL u) (by simp) (by simp)
    (by simp) (R u) [] [] (hm u) (mkS io desc park Rr (wkMid B D) Bf ex) hR
    (by simp [mkS, wkMid, iTT, iCB, iCD, iHT]) ρ).mono_framed (framed' := ccoreFramed)
    (fun _ _ => trivial)
  rw [mkS_upd_role, mkS_upd_buf] at h1
  refine (SafeRunsIn.seq (h1.mono (fun _ _ => trivial) le_rfl)
    (SafeRunsIn.mono ((safe_popR (roleL u) Sym.mark [] _ (by simp [mkS]) ρ).mono_framed
      (framed' := ccoreFramed) (fun _ _ => trivial)) (fun _ _ => trivial) le_rfl)).congr ?_ ?_
  · rw [mkS_upd_role, Function.update_idem]
    have eB : mkS io desc park Rr (wkMid B D) Bf ex (bufL u) = [] := hB
    rw [eB, List.append_nil]
  · have := hlen u
    omega

end Collect

/-- `f a ≤ sup f` over a finite type (stated generically: elaborating `Finset.mem_univ π` for
`π : Equiv.Perm (Fin W_c)` directly would make `whnf` enumerate the permutations). -/
theorem le_sup_univ' {α : Type} [Fintype α] (f : α → ℕ) (a : α) : f a ≤ Finset.univ.sup f :=
  Finset.le_sup (Finset.mem_univ a)

/-- The cost arithmetic of the collect. -/
theorem collect_cost_arith (W' C C' vg M V hdr Z bB bD : ℕ) (hCC : C ≤ C') (hV : V ≤ 2 * vg)
    (hM : M ≤ vg) (h1 : 1 ≤ vg) (hh : hdr + 1 ≤ vg) (hZ : Z ≤ 48 * M + 2) (hbB : bB ≤ M)
    (hbD : bD ≤ M) :
    (2 + (13 * hdr + 100) + Z + (V * 8 + W' * 5 + 1)) + (C * (V + 1) + (3 * bB + 3 * bD + 11)) ≤
      (3 * C' + 7 * W' + 201) * vg := by
  have a1 : C * (V + 1) ≤ 3 * (C' * vg) := by
    calc C * (V + 1) ≤ C' * (3 * vg) := Nat.mul_le_mul hCC (by omega)
      _ = 3 * (C' * vg) := by ring
  have a2 : W' ≤ W' * vg := Nat.le_mul_of_pos_right _ h1
  have e : (3 * C' + 7 * W' + 201) * vg = 3 * (C' * vg) + 7 * (W' * vg) + 201 * vg := by ring
  rw [e]
  generalize C' * vg = a at a1 ⊢
  generalize W' * vg = b at a2 ⊢
  generalize C * (V + 1) = c at a1 ⊢
  omega

end SubNLogN.Machine.CCore.LeafSplitAux

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
open LeafSplitAux

/-- **[LEAF 7, PROVED] Collect with the fused relabel** (`CollectStmt p`,
`CCore/SkelDefs.lean:243`), for every `p` and every static `π`, with no hypotheses. The cutoff is
that of `hdrLen_holds p`; the kernel is `collectProg π` around the proved K2 block merge
`k2MergeBlk_holds W_c π` (`K1/DistributeBlk.lean`) with class order `π`; the cost constant
`3·C₃ + 7·W_c + 201` uses `C₃ = max_π` of the K2 merge constants (a finite maximum). Paper: the
inverse of the cyclic row split (Section A.6 (`sec:transfer-layer`), Proposition A.11), stream
primitive (4) of Lemma A.4 (`lem:transfer-streams`). -/
theorem collect_holds (p : LayerParams) : CollectStmt p := by
  obtain ⟨P₀, hP₀⟩ := hdrLen_holds p
  have hK3 : ∀ π : Equiv.Perm (Fin Wn), K2MergeBlkStmt Wn π := fun π => k2MergeBlk_holds Wn π
  choose C₃ hC₃ using hK3
  refine ⟨P₀, 3 * (Finset.univ.sup C₃) + 7 * Wn + 201, fun π => ?_⟩
  obtain ⟨E₃, iF, iD, R₃, P₃, hfin, hne, hcl, hspec⟩ := hC₃ π ()
  refine ⟨SE E₃, inferInstance, inferInstance, Option Sym × R₃, collectProg P₃, inferInstance,
    ⟨(none, hne.some)⟩, closed_collectProg P₃ hcl, ?_⟩
  intro t hA hS hA' z' tio tdesc S hB hW hKC hBT hio hdesc hroles
  obtain ⟨pk, hpk⟩ : ∃ pk, S parkL = pk := ⟨_, rfl⟩
  have hS0 : S = mkS tio (t.hdr ++ tdesc) pk
      (fun w => Enc (compactRT t) hA' hS (restrictRole t (π.symm w) z') ++ [Sym.mark])
      (fun _ => []) (fun _ => []) (fun _ => []) := by
    funext k
    rcases k with ((_ | _ | _ | w) | (i | (w | e)))
    · exact hio
    · exact hdesc
    · exact hpk
    · have h := hroles (π.symm w)
      rwa [Equiv.apply_symm_apply] at h
    · exact hKC _
    · exact hKC _
    · exact hKC _
  subst hS0
  have hfinal : setRoles (Function.update (mkS (E₂ := E₃) tio (t.hdr ++ tdesc) pk
      (fun w => Enc (compactRT t) hA' hS (restrictRole t (π.symm w) z') ++ [Sym.mark])
      (fun _ => []) (fun _ => []) (fun _ => [])) ioL (Enc t hA hS z' ++ tio)) (fun _ => []) =
      mkS (Enc t hA hS z' ++ tio) (t.hdr ++ tdesc) pk (fun _ => []) (fun _ => []) (fun _ => [])
        (fun _ => []) := by
    funext k
    rcases k with ((_ | _ | _ | u) | (i | (u | e))) <;> simp [setRoles, mkS]
  rw [hfinal]
  have h1 := safe_initCtr (E₂ := E₃) t hS tio pk tdesc
    (fun w => Enc (compactRT t) hA' hS (restrictRole t (π.symm w) z') ++ [Sym.mark]) (fun _ => [])
    (fun _ => []) []
  have h2 := safe_rolesToBufs (E₂ := E₃)
    (fun w => Enc (compactRT t) hA' hS (restrictRole t (π.symm w) z')) tio (t.hdr ++ tdesc) pk
    (rowSz t) t.D (fun _ => []) (Lc t) (fun w => length_Enc_compact t hA' hS _ z')
    (fun w => by rw [Enc_eq_arrSyms]; exact mark_not_mem_arrSyms _) []
  have hpre := SafeRunsIn.liftRegs (Lens.fst (Option Sym) R₃) (closed_preC (E₂ := E₃))
    (SafeRunsIn.seq h1 h2) []
  have hcall := safe_mergeCall π P₃ hcl (C₃ π) hspec (t.A / Wn) (rowSz t)
    (fun w => recs (compactRT t) hA' hS (restrictRole t (π.symm w) z'))
    (fun w => length_recs (compactRT t) hA' hS _) tio [Sym.mark] (termOK_mark' [])
    (t.hdr ++ tdesc) pk (fun _ => []) (wkMid (rowSz t) t.D) (fun _ => [])
    (by simp [wkMid, iCB]) []
  rw [mergeBlocks_recs t hA hS hA' hW z' π
    (fun w => recs (compactRT t) hA' hS (restrictRole t (π.symm w) z'))
    (fun c => by simp only [Equiv.symm_apply_apply])] at hcall
  simp only [← Enc_eq_arrSyms] at hcall
  have hcl2 := SafeRunsIn.liftRegs (Lens.fst (Option Sym) R₃) (closed_cleanup (E₂ := E₃))
    (safe_cleanup (E₂ := E₃) (rowSz t) t.D (Enc t hA hS z' ++ tio) (t.hdr ++ tdesc) pk
      (fun _ => []) (fun _ => []) (fun _ => []) []) []
  refine (SafeRunsIn.seq hpre (SafeRunsIn.seq hcall hcl2)).mono (fun _ _ => trivial) ?_
  -- cost
  have hsum : ((List.finRange Wn).map fun w =>
      vol (recs (compactRT t) hA' hS (restrictRole t (π.symm w) z'))).sum = Wn * Lc t := by
    rw [List.map_congr_left (g := fun _ => Lc t)
      (fun w _ => vol_recs (compactRT t) hA' hS _), sum_finRange_const]
  rw [hsum]
  have hhdr := hP₀ t hB
  have hr := one_le_r_of_bands hB
  obtain ⟨-, -, -, -, -, -, -, hA1, hS1, -, -, hg, hρ, -⟩ := hB
  have hK1 : 1 ≤ t.K := by omega
  have hD1 : 1 ≤ t.D := by
    have := one_le_e t
    omega
  have hM2 := two_pow_le_M t hA1 hS1
  have hKD : t.K * t.D < 2 ^ (t.K * t.D) := Nat.lt_two_pow_self
  have hKle : t.K ≤ t.K * t.D := Nat.le_mul_of_pos_right _ hD1
  have hDle : t.D ≤ t.K * t.D := Nat.le_mul_of_pos_left _ hK1
  have hM1 : 1 ≤ t.M := le_trans Nat.one_le_two_pow hM2
  have hrw : 1 ≤ 2 * t.r * t.wg := by
    have hwg : 3 ≤ t.wg := by
      unfold CCoreRT.wg
      omega
    have h1 : 1 * 1 ≤ t.r * t.wg := Nat.mul_le_mul hr (by omega)
    have h2 : t.r * t.wg ≤ 2 * t.r * t.wg := by
      rw [Nat.mul_assoc]
      omega
    omega
  have hMvg : t.M ≤ t.volG := by
    have e : t.volG = t.M * (2 * t.r * t.wg) := by unfold CCoreRT.volG; ring
    rw [e]
    exact Nat.le_mul_of_pos_right _ hrw
  have hvg1 : 1 ≤ t.volG := le_trans hM1 hMvg
  have hV : t.M * (2 * t.r * t.wg + 1) ≤ 2 * t.volG := by
    have e : t.volG = t.M * (2 * t.r * t.wg) := by unfold CCoreRT.volG; ring
    have e2 : t.M * (2 * t.r * t.wg + 1) = t.M * (2 * t.r * t.wg) + t.M := by ring
    rw [e2]
    omega
  have hWL0 : Wn * Lc t = t.M * (2 * t.r * t.wg + 1) := by
    unfold Lc
    rw [← compact_M t hW]
    ring
  have hWL : Wn * (8 * Lc t + 5) = t.M * (2 * t.r * t.wg + 1) * 8 + Wn * 5 := by
    rw [← hWL0]
    ring
  have hZ : countdownCost (fun _ => 9 * bitLen t.D + 4 + countdownCost (fun _ => 1) t.D) t.K ≤
      48 * t.M + 2 := by
    have h26 := pushZeros_cost_le t.K t.D
    generalize t.K * t.D = L at h26 hKD hKle hM2
    generalize 2 ^ L = X at hKD hM2
    omega
  have hBM : rowSz t ≤ t.M := by
    unfold rowSz CCoreRT.M
    calc 2 ^ (t.K * t.D) * t.S = 1 * t.S * 2 ^ (t.K * t.D) := by ring
      _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := by gcongr
  have hbB : bitLen (rowSz t) ≤ t.M := le_trans (bitLen_le_self' _) hBM
  have hbD : bitLen t.D ≤ t.M :=
    le_trans (bitLen_le_self' _) (le_trans hDle (le_trans hKD.le hM2))
  have hCC : C₃ π ≤ Finset.univ.sup C₃ := le_sup_univ' C₃ π
  have key := collect_cost_arith Wn (C₃ π) (Finset.univ.sup C₃) t.volG t.M
    (t.M * (2 * t.r * t.wg + 1)) t.hdr.length _ _ _ hCC hV hMvg hvg1 hhdr hZ hbB hbD
  unfold initCost
  rw [hWL, hWL0]
  refine le_trans (le_of_eq ?_) key
  ring

end SubNLogN.Machine.CCore
