/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.NodeCodeBase
import SubNLogN.Math.Networks.Proofs.CCoreEdgeBits2

/-!
# C-core node code (II): row independence of the role steps (`CCore/NodeCodeRow.lean`)

The phase steps (`zMask`, `zSlot`, scalar `recMap`s) and the Lemma A.9 packed row addition
(`packedAddProc`) do not see the row field: run in role class `k` of the top class of the full
layout (rows `A`), they act on role array `toN k` exactly as the corresponding steps of the compact
layout (rows `A/W`) act on the compact array (`sim_zMask`, `sim_zSlot`, `sim_recMap`,
`sim_rowAdd`). For Lemma A.9 this uses `PackedProcCorrectStmt` on both layouts and the bit-level
`addrXorAll_encode_holds` (`addrXorAll (encodeAddr x) = encodeAddr (rowAddL x)`), and `rowAddL`
commutes with `roleEmb`. Helpers are in `SubNLogN.Machine.CCore.NodeCodeAux`.
-/

namespace SubNLogN.Machine.CCore

namespace NodeCodeAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks Model

/-! ## Phase steps -/

section Phase

theorem zMask_run {A K D S rr : ℕ} (ρ f j0 : ℕ) (a : Addr 100)
    (B : (layerLayout A K D S).Addr → (Fin rr → ℂ)) (y : (layerLayout A K D S).Addr) :
    (zMask (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 a).run B y =
      ((-1 : ℂ) ^ (∑ c ∈ Finset.range f, ∑ p : Cube 100, (ua a p).val *
        slotBit (A := A) (D := D) (S := S) K ρ f j0 (cubeEquiv p) c y)) • B y := rfl

theorem zSlot_run {A K D S rr : ℕ} (ρ f j0 tt : ℕ)
    (B : (layerLayout A K D S).Addr → (Fin rr → ℂ)) (y : (layerLayout A K D S).Addr) :
    (zSlot (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 tt).run B y =
      ((-1 : ℂ) ^ (∑ c ∈ Finset.range f,
        slotBit (A := A) (D := D) (S := S) K ρ f j0 tt c y)) • B y := rfl

theorem phaseStep_zMask (t : CCoreRT) (a : Addr 100) :
    phaseStep t (.zMask a) = zMask t.ρ (mn ^ (t.k - 1)) t.j0 a := rfl

theorem phaseStep_zSlot (t : CCoreRT) (sl : Fin mn) :
    phaseStep t (.zSlot sl) = zSlot t.ρ (mn ^ (t.k - 1)) t.j0 sl.val := rfl

variable {t : CCoreRT} {crun : Crun t}

theorem sim_zMask (k : Fin Wc) (a : Addr 100) :
    Sim crun [RoleOp.prim k (zMask t.ρ (mn ^ (t.k - 1)) t.j0 a)] [MOp.phase (toN k) (.zMask a)] := by
  refine sim_prim k _ _ (fun Arr x => ?_)
  rw [zMask_run, phaseStep_zMask, zMask_run, encodeArr_encodeAddr, Φ_apply]
  simp only [slotBit_roleEmb]

theorem sim_zSlot (k : Fin Wc) (sl : Fin mn) :
    Sim crun [RoleOp.prim k (zSlot t.ρ (mn ^ (t.k - 1)) t.j0 sl.val)]
      [MOp.phase (toN k) (.zSlot sl)] := by
  refine sim_prim k _ _ (fun Arr x => ?_)
  rw [zSlot_run, phaseStep_zSlot, zSlot_run, encodeArr_encodeAddr, Φ_apply]
  simp only [slotBit_roleEmb]

theorem sim_recMap (k : Fin Wc) (c : ℂ) (κ : PhaseKind)
    (hκ : phaseStep t κ = .recMap fun v => c • v) :
    Sim crun [RoleOp.prim k (.recMap fun v => c • v)] [MOp.phase (toN k) κ] := by
  refine sim_prim k _ _ (fun Arr x => ?_)
  rw [hκ, recMap_run, recMap_run, encodeArr_encodeAddr, Φ_apply]

end Phase

/-! ## The Lemma A.9 packed row addition -/

/-- The Lemma A.9 layout hypotheses for three distinct slots of a node, for any row range `A`. -/
theorem packedHyps_slots' {A K D S f j0 : ℕ} (ρ : Fin K) (hK : 6 ≤ K) (hf : 1 ≤ f)
    (hfit : j0 + mH * f ≤ D) (i j t3 : ℕ) (hi : i < mH) (hj : j < mH) (ht3 : t3 < mH)
    (hij : i ≠ j) (hit : i ≠ t3) (hjt : j ≠ t3) :
    PackedHyps (layerLayout A K D S) (f * K) K ρ.val f
      ⟨1 + (j0 + j * f) * K, 1 + (j0 + i * f) * K, 1 + (j0 + t3 * f) * K⟩ := by
  have hs : ∀ s, s < mH → 1 + (j0 + s * f) * K + f * K ≤ D * K + 1 := by
    intro s hsm
    have h1 := CCoreNode.slot_le hfit hsm
    have h2 : (j0 + s * f + f) * K ≤ D * K := Nat.mul_le_mul_right K h1
    have h3 : (j0 + s * f + f) * K = (j0 + s * f) * K + f * K := by ring
    omega
  have hdisj : ∀ s s', s ≠ s' → 1 + (j0 + s * f) * K + f * K ≤ 1 + (j0 + s' * f) * K ∨
      1 + (j0 + s' * f) * K + f * K ≤ 1 + (j0 + s * f) * K := by
    intro s s' hss'
    rcases Nat.lt_or_gt_of_ne hss' with h | h
    · left
      have h1 : (s + 1) * f ≤ s' * f := Nat.mul_le_mul_right f h
      have h2 : (j0 + (s + 1) * f) * K ≤ (j0 + s' * f) * K := Nat.mul_le_mul_right K (by omega)
      have h3 : (j0 + (s + 1) * f) * K = (j0 + s * f) * K + f * K := by ring
      omega
    · right
      have h1 : (s' + 1) * f ≤ s * f := Nat.mul_le_mul_right f h
      have h2 : (j0 + (s' + 1) * f) * K ≤ (j0 + s * f) * K := Nat.mul_le_mul_right K (by omega)
      have h3 : (j0 + (s' + 1) * f) * K = (j0 + s' * f) * K + f * K := by ring
      omega
  have hn : (layerLayout A K D S).n = D * K + 2 := rfl
  refine ⟨hK, rfl, ρ.isLt, hf, ?_, ?_, ?_, hdisj j i (Ne.symm hij), hdisj j t3 hjt,
    hdisj i t3 hit, ?_⟩
  · have := hs j hj
    simp only [hn]
    omega
  · have := hs i hi
    simp only [hn]
    omega
  · have := hs t3 ht3
    simp only [hn]
    omega
  · intro m hm
    apply CCoreEdgeAux.layer_r_mid
    · rcases hm with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only at h1 <;> omega
    · have := hs j hj
      have := hs i hi
      have := hs t3 ht3
      rcases hm with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ <;> simp only at h2 <;> omega

/-- Unrestricted runs of steps are runs in the top class. -/
theorem foldl_run_eq_top {L : Layout} {β : Type} (row : Fin L.n) (l : List (Step L β))
    (B : L.Addr → β) : l.foldl (fun B s => s.run B) B = ProcK.run 0 l (RowClass.top row) B := by
  show l.foldl (fun B s => s.run B) B = l.foldl (fun A s => Step.runIn (RowClass.top row) s A) B
  have hfun : (fun (B : L.Addr → β) (s : Step L β) => s.run B) =
      fun A s => Step.runIn (RowClass.top row) s A := by
    funext A s x
    show s.run A x = if (RowClass.top row).mem x then s.run A x else A x
    rw [if_pos (show (RowClass.top row).mem x from Nat.mod_one _)]
  rw [hfun]

/-- `foldl_run_eq_top` for a depth-`0` procedure (the list has type `ProcK L β 0`). -/
theorem foldl_run_eq_top' {L : Layout} {β : Type} (row : Fin L.n) (l : ProcK L β 0)
    (B : L.Addr → β) :
    List.foldl (fun B s => Step.run s B) B l = ProcK.run 0 l (RowClass.top row) B :=
  foldl_run_eq_top row l B

theorem rowAddL_roleEmb (t : CCoreRT) (ρ : Fin t.K) (f j0 i j : ℕ) (u : Fin Wn)
    (x : LayerAddr (t.A / Wn) t.K t.D t.S) :
    CCoreEdgeAux.rowAddL ρ f j0 i j (roleEmb t u x) =
      roleEmb t u (CCoreEdgeAux.rowAddL ρ f j0 i j x) := rfl

/-- The Lemma A.9 row addition on role `k` (slots `p.2 → p.1`) is the skeleton's `rowAdd`. -/
theorem sim_rowAdd {t : CCoreRT} {crun : Crun t} (hρ : t.ρ < t.K) (hR8 : RunEightSpecStmt)
    (hPA : PackedAgreeStmt) (hPP : PackedProcCorrectStmt) (hK : 6 ≤ t.K)
    (hfit : t.j0 + mH * mn ^ (t.k - 1) ≤ t.D) (k : Fin Wc) (p : Fin mH × Fin mH)
    (hp : p.1 ≠ p.2) :
    Sim crun (CCoreEdgeAux.rowAddOps (A := t.A) (D := t.D) (S := t.S) (rr := t.r) (Child := ℕ)
        ⟨t.ρ, hρ⟩ (mn ^ (t.k - 1)) t.j0 k p)
      [MOp.rowAdd (toN k) (Fin.cast mH_eq_mn p.1) (Fin.cast mH_eq_mn p.2)] := by
  have hf : 1 ≤ mn ^ (t.k - 1) := Nat.one_le_pow _ _ (by norm_num [mn, tripleM])
  have hp' : p.1.val ≠ p.2.val := fun h => hp (Fin.ext h)
  obtain ⟨h3i, h3j, h3⟩ := CCoreEdgeAux.thirdSlot_spec p.1.val p.2.val
  have h3m : thirdSlot p.1.val p.2.val < mH := lt_of_lt_of_le h3 (by norm_num [mH])
  have hPH := packedHyps_slots' (A := t.A) (S := t.S) ⟨t.ρ, hρ⟩ hK hf hfit p.1.val p.2.val
    (thirdSlot p.1.val p.2.val) p.1.isLt p.2.isLt h3m hp' (Ne.symm h3i) (Ne.symm h3j)
  have hPH' := packedHyps_slots' (A := t.A / Wn) (S := t.S) ⟨t.ρ, hρ⟩ hK hf hfit p.1.val p.2.val
    (thirdSlot p.1.val p.2.val) p.1.isLt p.2.isLt h3m hp' (Ne.symm h3i) (Ne.symm h3j)
  have hrow : ((topC t).sub Wc Wc_pos k).row.val = 0 := by
    rw [CCoreEdgeAux.sub_row, topC_eq]
    rfl
  intro Arr
  funext u x
  unfold CCoreEdgeAux.rowAddOps
  have hpr := CCoreEdgeAux.runOps_prims (crun := crun) (topC t) k
    (packedAddProc (Ly := FL t) (β := Fin t.r → ℂ) (mn ^ (t.k - 1) * t.K) t.K
      (⟨t.ρ, hρ⟩ : Fin t.K).val (mn ^ (t.k - 1))
      ⟨1 + (t.j0 + p.2.val * mn ^ (t.k - 1)) * t.K, 1 + (t.j0 + p.1.val * mn ^ (t.k - 1)) * t.K,
        1 + (t.j0 + (thirdSlot p.1.val p.2.val) * mn ^ (t.k - 1)) * t.K⟩) Arr
  rw [Φ_apply, hpr, hPP hR8 hPA (FL t) (Fin t.r → ℂ) _ t.K (⟨t.ρ, hρ⟩ : Fin t.K).val
    (mn ^ (t.k - 1)) _ hPH ((topC t).sub Wc Wc_pos k)
    (Or.inl (by rw [hrow]; show 0 < 1 + _; omega)) (Or.inl (by rw [hrow]; show 0 < 1 + _; omega))
    (Or.inl (by rw [hrow]; show 0 < 1 + _; omega)) Arr, mopsVal_single, mopVal_rowAdd]
  beta_reduce
  by_cases hu : u = toN k
  · subst hu
    rw [if_pos ((sub_mem_roleEmb t k _ x).mpr rfl), Function.update_self,
      addrXorAll_encode_holds t.A t.K t.D t.S ⟨t.ρ, hρ⟩ (mn ^ (t.k - 1)) t.j0 p.1.val p.2.val _ hf
        p.1.isLt p.2.isLt hfit, rowAddL_roleEmb, runSteps_apply]
    unfold rowAddSteps
    simp only [Fin.val_cast]
    rw [foldl_run_eq_top' (⟨0, by show 0 < t.D * t.K + 2; omega⟩ : Fin (CLy t).n),
      hPP hR8 hPA (CLy t) (Fin t.r → ℂ) _ t.K t.ρ (mn ^ (t.k - 1)) _ hPH'
      (RowClass.top (⟨0, by show 0 < t.D * t.K + 2; omega⟩ : Fin (CLy t).n))
      (Or.inl (show 0 < 1 + _ by omega)) (Or.inl (show 0 < 1 + _ by omega))
      (Or.inl (show 0 < 1 + _ by omega)) (encodeArr (Φ t Arr (toN k)))]
    beta_reduce
    rw [if_pos (top_mem (⟨0, by show 0 < t.D * t.K + 2; omega⟩ : Fin (CLy t).n) (encodeAddr x)),
      addrXorAll_encode_holds (t.A / Wn) t.K t.D t.S ⟨t.ρ, hρ⟩ (mn ^ (t.k - 1)) t.j0 p.1.val
        p.2.val _ hf p.1.isLt p.2.isLt hfit, encodeArr_encodeAddr, Φ_apply]
  · rw [if_neg (fun h => hu ((sub_mem_roleEmb t k u x).mp h).symm), Function.update_of_ne hu,
      Φ_apply]

end NodeCodeAux

end SubNLogN.Machine.CCore
