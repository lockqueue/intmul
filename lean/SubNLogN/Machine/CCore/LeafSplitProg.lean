/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafSplitPhase
import SubNLogN.Machine.K1.DistributeBlk

/-!
# C-core leaf 6: the row split (`CCore/LeafSplitProg.lean`)

**Proved:** `SubNLogN.Machine.CCore.split_holds (p) : SplitStmt p` (`CCore/SkelDefs.lean:229`),
with no hypotheses. Paper: the cyclic row split `a = a'·W_c + u` of an internal node (Section A.6
(`sec:transfer-layer`), Proposition A.11), stream primitive (4) of
Lemma A.4 (`lem:transfer-streams`).

Program (`splitProg`, one closed program for the fixed `W = W_c`; private scratch
`SE E₂ = Fin 6 ⊕ (Fin W ⊕ E₂)` where `E₂` is the scratch of the proved K2 kernel):
1. `preS`: a guard `mark` on every private role buffer, the owned `mark` on every (empty) role
   stack, then the counter phase (`initCtr`: the header fields `K, D, S` and the row size
   `natSyms (2^(K·D)·S) ++ [mark]` on `CB`);
2. the K2 block distribution (`k2DistributeBlk_holds W`, embedded by `callInj` along `ιK`, whose
   image is unframed): rows of `B = 2^(K·D)·S` records go from `io` to buffer `row mod W`;
3. `postS`: pass S from every buffer onto its role stack (same symbol order, above the owned
   `mark`), drop the buffer guards, erase the work stacks.
Value layer: `roleBlocks_recs` (`CCore/LeafSplitVal.lean`). Cost: `C·V_g` with
`C = 3·C₂ + 7·W + 201`, `C₂` the K2 constant (`|Enc t z| ≤ 2·V_g`, `hdrLen_holds`, `K·D ≤ M`).
-/

namespace SubNLogN.Machine.CCore.LeafSplitAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
open SubNLogN.Machine.CCore SubNLogN.Math.Walsh

theorem mark_not_mem_arrSyms (v : List (List Bool)) : Sym.mark ∉ arrSyms v := by
  simp [arrSyms, blk, recSyms]

/-- The compact record volume of one role stream. -/
def Lc (t : CCoreRT) : ℕ := (compactRT t).M * (2 * t.r * t.wg + 1)

theorem length_Enc_compact (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S) (u : Fin Wn)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) :
    (Enc (compactRT t) hA' hS (restrictRole t u z)).length = Lc t := by
  rw [Enc_eq_arrSyms]
  exact vol_recs (compactRT t) hA' hS (restrictRole t u z)

section Split

variable {E₂ R₂ : Type} [DecidableEq E₂]

/-- The part before the K2 call. -/
def preS : SProg (CL (SE E₂)) :=
  .seq (forEachFin Wn (fun u => pushC (bufL u) .mark))
    (.seq (forEachFin Wn (fun u => pushC (roleL u) .mark)) initCtr)

/-- The part after the K2 call. -/
def postS : SProg (CL (SE E₂)) :=
  .seq (forEachFin Wn (fun u => .seq (passS .mark (bufL u) (wkL iTT) (roleL u)) (popR (bufL u))))
    cleanup

/-- **The split program** for the K2 distribution program `P₂`. -/
def splitProg (P₂ : Prog (KLoc (Fin 2 ⊕ Fin Wn) E₂) (fun _ => Sym) R₂) :
    Prog (CL (SE E₂)) (fun _ => Sym) (Option Sym × R₂) :=
  .seq ((preS (E₂ := E₂)).liftRegs (Lens.fst (Option Sym) R₂))
    (.seq (callInj ιK (Lens.snd (Option Sym) R₂) P₂)
      ((postS (E₂ := E₂)).liftRegs (Lens.fst (Option Sym) R₂)))

/-- A `forEachFin` loop followed by a closed program is closed (stated for a generic count `n`;
instantiating a lemma whose conclusion is `(forEachFin W_c g).Closed` itself would make the
elaborator's `whnf` unfold `List.finRange W_c`). -/
theorem closed_seq_forEachFin {K σ : Type} (n : ℕ) (g : Fin n → Prog K (fun _ => Sym) σ)
    (q : Prog K (fun _ => Sym) σ) (hg : ∀ i, (g i).Closed) (hq : q.Closed) :
    (Prog.seq (forEachFin n g) q).Closed :=
  WP.W9comp.closed_seq (closed_forEachFin n g hg) hq

/-- A closed program followed by a `forEachFin` loop is closed (generic count `n`). -/
theorem closed_seq_forEachFin' {K σ : Type} (n : ℕ) (g : Fin n → Prog K (fun _ => Sym) σ)
    (p : Prog K (fun _ => Sym) σ) (hp : p.Closed) (hg : ∀ i, (g i).Closed) :
    (Prog.seq p (forEachFin n g)).Closed :=
  WP.W9comp.closed_seq hp (closed_forEachFin n g hg)

theorem closed_preS : (preS (E₂ := E₂)).Closed :=
  closed_seq_forEachFin Wn _ _ (fun _ => by simp [Prog.Closed, Prog.FreeBelow, pushC])
    (closed_seq_forEachFin Wn _ _ (fun _ => by simp [Prog.Closed, Prog.FreeBelow, pushC])
      closed_initCtr)

theorem closed_postS : (postS (E₂ := E₂)).Closed :=
  closed_seq_forEachFin Wn _ _ (fun _ => WP.W9comp.closed_seq
    (WP.W9comp.closed_seq (closed_passM _ _ _) (closed_passM _ _ _))
    (by simp [Prog.Closed, Prog.FreeBelow, popR])) closed_cleanup

theorem closed_splitProg (P₂ : Prog (KLoc (Fin 2 ⊕ Fin Wn) E₂) (fun _ => Sym) R₂)
    (hcl : P₂.Closed) : (splitProg P₂).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs _ closed_preS)
    (WP.W9comp.closed_seq (closed_callInj _ _ hcl) (WP.W9comp.closed_liftRegs _ closed_postS))

theorem safe_preS (t : CCoreRT) (hS : 0 < t.S) (io park tdesc : List Sym) (ex : E₂ → List Sym)
    (ρ : List (SProg (CL (SE E₂)))) :
    SafeRunsIn ccoreFramed ρ preS
      (mkS io (t.hdr ++ tdesc) park (fun _ => []) (fun _ => []) (fun _ => []) ex)
      (mkS io (t.hdr ++ tdesc) park (fun _ => [Sym.mark]) (wkMid (rowSz t) t.D)
        (fun _ => [Sym.mark]) ex) (fun _ => True) ((Wn * 1 + 1) + ((Wn * 1 + 1) + initCost t)) := by
  have ha : SafeRunsIn ccoreFramed ρ (forEachFin Wn (fun u => pushC (bufL (E₂ := E₂) u) .mark))
      (mkS io (t.hdr ++ tdesc) park (fun _ => []) (fun _ => []) (fun _ => []) ex)
      (mkS io (t.hdr ++ tdesc) park (fun _ => []) (fun _ => []) (fun _ => [Sym.mark]) ex)
      (fun _ => True) (Wn * 1 + 1) := by
    refine safe_forEachFin_rb _ 1 io (t.hdr ++ tdesc) park (fun _ => []) ex (fun _ => [])
      (fun _ => []) (fun _ => []) (fun _ => [Sym.mark]) (fun u R Bf hR hB => ?_)
    have h := (safe_pushC (bufL u) Sym.mark (mkS io (t.hdr ++ tdesc) park R (fun _ => []) Bf ex)
      ρ).mono_framed (framed' := ccoreFramed) (fun _ _ => trivial)
    rw [mkS_upd_buf] at h
    refine h.congr ?_ le_rfl
    have e : Function.update R u [] = R := by
      rw [Function.update_eq_self_iff]
      exact hR.symm
    simp only [e]
    congr 2
    show Sym.mark :: Bf u = [Sym.mark]
    rw [hB]
  have hb : SafeRunsIn ccoreFramed ρ (forEachFin Wn (fun u => pushC (roleL (E := SE E₂) u) .mark))
      (mkS io (t.hdr ++ tdesc) park (fun _ => []) (fun _ => []) (fun _ => [Sym.mark]) ex)
      (mkS io (t.hdr ++ tdesc) park (fun _ => [Sym.mark]) (fun _ => []) (fun _ => [Sym.mark]) ex)
      (fun _ => True) (Wn * 1 + 1) := by
    refine safe_forEachFin_rb _ 1 io (t.hdr ++ tdesc) park (fun _ => []) ex (fun _ => [])
      (fun _ => [Sym.mark]) (fun _ => [Sym.mark]) (fun _ => [Sym.mark]) (fun u R Bf hR hB => ?_)
    have h := (safe_pushC (roleL u) Sym.mark (mkS io (t.hdr ++ tdesc) park R (fun _ => []) Bf ex)
      ρ).mono_framed (framed' := ccoreFramed) (fun _ _ => trivial)
    rw [mkS_upd_role] at h
    refine h.congr ?_ le_rfl
    have e : Function.update Bf u [Sym.mark] = Bf := by
      rw [Function.update_eq_self_iff]
      exact hB.symm
    simp only [e]
    congr 2
    show Sym.mark :: R u = [Sym.mark]
    rw [hR]
  exact SafeRunsIn.seq ha (SafeRunsIn.seq hb (safe_initCtr t hS io park tdesc _ _ ex ρ))

theorem safe_postS (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S) (hA' : 0 < t.A / Wn)
    (hW : Wn ∣ t.A) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (tio desc park : List Sym)
    (ex : E₂ → List Sym) (ρ : List (SProg (CL (SE E₂)))) :
    SafeRunsIn ccoreFramed ρ postS
      (mkS tio desc park (fun _ => [Sym.mark]) (wkMid (rowSz t) t.D)
        (fun u => arrSyms (roleBlocks Wn u.val (rowSz t) (recs t hA hS z)) ++ [Sym.mark]) ex)
      (mkS tio desc park (fun u => Enc (compactRT t) hA' hS (restrictRole t u z) ++ [Sym.mark])
        (fun _ => []) (fun _ => []) ex) (fun _ => True)
      ((Wn * (8 * Lc t + 5) + 1) + (3 * bitLen (rowSz t) + 3 * bitLen t.D + 11)) := by
  refine SafeRunsIn.seq (Q₁ := fun _ => True) ?a (safe_cleanup _ _ tio desc park _ _ ex ρ)
  refine safe_forEachFin_rb _ (8 * Lc t + 5) tio desc park (wkMid (rowSz t) t.D) ex
    (fun _ => [Sym.mark]) (fun u => Enc (compactRT t) hA' hS (restrictRole t u z) ++ [Sym.mark])
    (fun u => arrSyms (roleBlocks Wn u.val (rowSz t) (recs t hA hS z)) ++ [Sym.mark])
    (fun _ => []) (fun u R Bf hR hB => ?_)
  have hxs : arrSyms (roleBlocks Wn u.val (rowSz t) (recs t hA hS z)) =
      Enc (compactRT t) hA' hS (restrictRole t u z) := by
    rw [roleBlocks_recs t hA hS hA' hW z u, Enc_eq_arrSyms]
  have hg : Sym.mark ∉ Enc (compactRT t) hA' hS (restrictRole t u z) := by
    rw [Enc_eq_arrSyms]
    exact mark_not_mem_arrSyms _
  have h1 := (safe_passS (src := bufL u) (tmp := wkL iTT) (dst := roleL u) (by simp) (by simp)
    (by simp) (Enc (compactRT t) hA' hS (restrictRole t u z)) [] [] hg
    (mkS tio desc park R (wkMid (rowSz t) t.D) Bf ex)
    (by show Bf u = _; rw [hB, hxs]) (by simp [mkS, wkMid, iTT, iCB, iCD, iHT]) ρ).mono_framed
    (framed' := ccoreFramed) (fun _ _ => trivial)
  rw [mkS_upd_buf, mkS_upd_role] at h1
  refine (SafeRunsIn.seq (h1.mono (fun _ _ => trivial) le_rfl)
    (SafeRunsIn.mono ((safe_popR (bufL u) Sym.mark [] _ (by simp [mkS]) ρ).mono_framed
      (framed' := ccoreFramed) (fun _ _ => trivial)) (fun _ _ => trivial) le_rfl)).congr ?_ ?_
  · rw [mkS_upd_buf, Function.update_idem]
    have eR : mkS tio desc park R (wkMid (rowSz t) t.D) Bf ex (roleL u) = [Sym.mark] := hR
    rw [eR]
  · have := length_Enc_compact t hA' hS u z
    omega

/-- The cost arithmetic of the split. -/
theorem split_cost_arith (W' C₂ vg M V hdr Z bB bD : ℕ) (hV : V ≤ 2 * vg) (hM : M ≤ vg)
    (h1 : 1 ≤ vg) (hh : hdr + 1 ≤ vg) (hZ : Z ≤ 48 * M + 2) (hbB : bB ≤ M) (hbD : bD ≤ M) :
    (W' * 1 + 1 + (W' * 1 + 1 + (2 + (13 * hdr + 100) + Z))) +
      (C₂ * (V + 1) + ((V * 8 + W' * 5 + 1) + (3 * bB + 3 * bD + 11))) ≤
      (3 * C₂ + 7 * W' + 201) * vg := by
  have a1 : C₂ * (V + 1) ≤ 3 * (C₂ * vg) := by
    calc C₂ * (V + 1) ≤ C₂ * (3 * vg) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (C₂ * vg) := by ring
  have a2 : W' ≤ W' * vg := Nat.le_mul_of_pos_right _ h1
  have e : (3 * C₂ + 7 * W' + 201) * vg = 3 * (C₂ * vg) + 7 * (W' * vg) + 201 * vg := by ring
  rw [e]
  generalize C₂ * vg = a at a1 ⊢
  generalize W' * vg = b at a2 ⊢
  generalize C₂ * (V + 1) = c at a1 ⊢
  omega

end Split

end SubNLogN.Machine.CCore.LeafSplitAux

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
open LeafSplitAux

/-- **[LEAF 6, PROVED] Row split** (`SplitStmt p`, `CCore/SkelDefs.lean:229`), for every `p`, with
no hypotheses. The cutoff is that of `hdrLen_holds p`; the kernel is `splitProg` around the
proved K2 block distribution `k2DistributeBlk_holds W_c` (`K1/DistributeBlk.lean`); cost constant
`3·C₂ + 7·W_c + 201` with `C₂` the K2 constant. Paper: the cyclic row split of an internal node
(Section A.6 (`sec:transfer-layer`), Proposition A.11), with stream primitive (4) of Lemma A.4
(`lem:transfer-streams`). -/
theorem split_holds (p : LayerParams) : SplitStmt p := by
  obtain ⟨P₀, hP₀⟩ := hdrLen_holds p
  obtain ⟨C₂, hK2⟩ := k2DistributeBlk_holds Wn
  obtain ⟨E₂, iF, iD, R₂, P₂, hfin, hne, hcl, hspec⟩ := hK2 ()
  refine ⟨P₀, 3 * C₂ + 7 * Wn + 201, fun _ => ⟨SE E₂, inferInstance, inferInstance,
    Option Sym × R₂, splitProg P₂, inferInstance, ⟨(none, hne.some)⟩, closed_splitProg P₂ hcl,
    ?_⟩⟩
  intro t hA hS hA' z tio tdesc S hB hW hKC hBT hio hdesc hroles
  obtain ⟨pk, hpk⟩ : ∃ pk, S parkL = pk := ⟨_, rfl⟩
  have hS0 : S = mkS (Enc t hA hS z ++ tio) (t.hdr ++ tdesc) pk (fun _ => []) (fun _ => [])
      (fun _ => []) (fun _ => []) := by
    funext k
    rcases k with ((_ | _ | _ | u) | (i | (u | e)))
    · exact hio
    · exact hdesc
    · exact hpk
    · exact hroles u
    · exact hKC _
    · exact hKC _
    · exact hKC _
  subst hS0
  have hfinal : setRoles (Function.update (mkS (E₂ := E₂) (Enc t hA hS z ++ tio)
      (t.hdr ++ tdesc) pk (fun _ => []) (fun _ => []) (fun _ => []) (fun _ => [])) ioL tio)
      (fun u => Enc (compactRT t) hA' hS (restrictRole t u z) ++ [Sym.mark]) =
      mkS tio (t.hdr ++ tdesc) pk (fun u => Enc (compactRT t) hA' hS (restrictRole t u z) ++
        [Sym.mark]) (fun _ => []) (fun _ => []) (fun _ => []) := by
    funext k
    rcases k with ((_ | _ | _ | u) | (i | (u | e))) <;> simp [setRoles, mkS]
  rw [hfinal]
  have hpre := SafeRunsIn.liftRegs (Lens.fst (Option Sym) R₂) (closed_preS (E₂ := E₂))
    (safe_preS (E₂ := E₂) t hS (Enc t hA hS z ++ tio) pk tdesc (fun _ => []) []) []
  have hcall := safe_distCall P₂ hcl C₂ hspec t.A (rowSz t) (recs t hA hS z) tio [Sym.mark]
    (length_recs t hA hS z) hBT (termOK_mark' []) (t.hdr ++ tdesc) pk (fun _ => [Sym.mark])
    (wkMid (rowSz t) t.D) (fun _ => [Sym.mark]) (fun _ => [])
    (by simp [wkMid, iCB]) []
  rw [← Enc_eq_arrSyms] at hcall
  have hpost := SafeRunsIn.liftRegs (Lens.fst (Option Sym) R₂) (closed_postS (E₂ := E₂))
    (safe_postS (E₂ := E₂) t hA hS hA' hW z tio (t.hdr ++ tdesc) pk (fun _ => []) []) []
  refine (SafeRunsIn.seq hpre (SafeRunsIn.seq hcall hpost)).mono (fun _ _ => trivial) ?_
  -- cost
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
  have hwg : 3 ≤ t.wg := by
    unfold CCoreRT.wg
    omega
  have hrw : 1 ≤ 2 * t.r * t.wg := by
    have : 1 ≤ t.r * t.wg := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have hMvg : t.M ≤ t.volG := by
    have e : t.volG = t.M * (2 * t.r * t.wg) := by unfold CCoreRT.volG; ring
    rw [e]
    exact Nat.le_mul_of_pos_right _ hrw
  have hvg1 : 1 ≤ t.volG := le_trans hM1 hMvg
  have hvol := vol_recs t hA hS z
  have hV : t.M * (2 * t.r * t.wg + 1) ≤ 2 * t.volG := by
    have e : t.volG = t.M * (2 * t.r * t.wg) := by unfold CCoreRT.volG; ring
    have e2 : t.M * (2 * t.r * t.wg + 1) = t.M * (2 * t.r * t.wg) + t.M := by ring
    rw [e2]
    omega
  have hWL : Wn * (8 * Lc t + 5) = t.M * (2 * t.r * t.wg + 1) * 8 + Wn * 5 := by
    unfold Lc
    rw [← compact_M t hW]
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
  have key := split_cost_arith Wn C₂ t.volG t.M (t.M * (2 * t.r * t.wg + 1)) t.hdr.length _ _ _
    hV hMvg hvg1 hhdr hZ hbB hbD
  unfold initCost
  rw [hvol, hWL]
  refine le_trans (le_of_eq ?_) key
  ring

end SubNLogN.Machine.CCore
