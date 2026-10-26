/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPh1BridgeAux
import SubNLogN.Machine.Layer.DrvPh1BridgeIdx

/-!
# Phase-1 value bridge (`Machine/Layer/DrvPh1Bridge.lean`)

**`drvPh1Bridge_holds : DrvPh1BridgeStmt`** (statement in `Machine/Layer/DrvPreMathDefs.lean`),
unconditional. For a disk-grid input `z` at precision `P`, `ρ < K` and `min(q₀, D) ≤ Δ`, the stored
phase-1 array `drvA1 t z` at precision `P + Δ` is `ph1Int t` of the stored `z`.

Proof. By `phase1_eq`, `drvA1 t z = Zs ρ (twist ρ z) q₁` (`DrvPh1BridgeAux.lean`). Induction on
the number `m ≤ q₁` of kernels (`ph1_inv`): the integer list after `m` passes of `ph1Step` is the
stored `Zs ρ (twist ρ z) m` (record `i` = `recOf … i`), and every value of `Zs … m` lies on the
`(P + m)`-grid.
* `m = 0`: `phaseRec … 0 0` is `rotC (selCount)` on numerators (`gridInt_rot`, `sDiag_sum_eq`).
* `m → m + 1` (`rec_step`): `ph1Step` is pointwise (`DrvPh1Idx.chunks_cgate`); the partner of
  record `i` under the kernel on chunk `m` is `i ± drvWj t m` (`DrvPh1Idx.addr_set_true/false`);
  the halving is exact at precision `P + Δ` since `P + m + 1 ≤ P + Δ` (`halve0`, `halve1`).
-/

namespace SubNLogN.Machine.Layer.DrvPh1Aux

open SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
open SubNLogN.Math.Networks (ka kb)

/-- Record `i` (lexicographic order) of the stored array `Z` at precision `F`. -/
noncomputable def recOf {A K D S rr : ℕ} (hA : 0 < A) (hS : 0 < S) (F : ℕ)
    (Z : RArr (LayerAddr A K D S) rr) (i : ℕ) : List CInt :=
  (List.finRange rr).map fun k => gridInt F (Z (layerAddrOfIndex A K D S hA hS i) k)

theorem encArr_eq {A K D S rr : ℕ} (hA : 0 < A) (hS : 0 < S) (F : ℕ)
    (Z : RArr (LayerAddr A K D S) rr) :
    encArr F (layerAddrs A K D S hA hS) Z =
      (List.range (A * 2 ^ (K * D) * S)).map (recOf hA hS F Z) :=
  DrvPPAux.encArr_layerAddrs hA hS F Z

theorem zipWith_finRange {rr : ℕ} (f : CInt → CInt → CInt) (g h : Fin rr → CInt) :
    List.zipWith f ((List.finRange rr).map g) ((List.finRange rr).map h) =
      (List.finRange rr).map fun k => f (g k) (h k) := by
  rw [List.zipWith_map, List.zipWith_self]

theorem phaseRec_zero (S K ρ D x : ℕ) (cs : List CInt) :
    phaseRec S K ρ D 0 0 x cs = cs.map (rotC (selCount S K ρ D x)) := by
  unfold phaseRec
  refine List.map_congr_left fun c _ => ?_
  simp

/-- `M = A·2^{KD}·S = drvNBj·2·drvWj` for a chunk `m < D` (`ρ < K`). -/
theorem M_eq (t : LayerRT) (hρ : t.ρ < t.K) {m : ℕ} (hm : m < t.D) :
    t.A * 2 ^ (t.K * t.D) * t.S = drvNBj t m * (2 * drvWj t m) := by
  unfold drvNBj drvWj
  have h1 : t.K * t.D = t.K * m + t.K + t.K * (t.D - 1 - m) := by
    rw [← Nat.mul_succ, ← Nat.mul_add]
    congr 1
    omega
  have h2 : (2 : ℕ) ^ (t.K * t.D) =
      2 ^ (t.K * m + (t.K - 1 - t.ρ)) * 2 * 2 ^ (t.K * (t.D - 1 - m) + t.ρ) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  rw [h2]
  ring

theorem drvWj_pos (t : LayerRT) (hS : 0 < t.S) (m : ℕ) : 0 < drvWj t m := by
  unfold drvWj
  positivity

/-- **One kernel pass on the stored records**: if `Z'` is `Z` after the kernel on bit `ρ` of chunk
`m` and `Z` lies on the `G`-grid, record `i` of `Z'` at precision `G + 1` is `cgate0` of records
`i, i + W` (bit `0`) or `cgate1` of records `i - W, i` (bit `1`), `W = S·2^{K(D-1-m)+ρ}`. -/
theorem rec_step {A K D S rr : ℕ} (hA : 0 < A) (hS : 0 < S) {ρ m : ℕ} (hρ : ρ < K) (hm : m < D)
    {G F : ℕ} (hF : G + 1 = F) (Z Z' : RArr (LayerAddr A K D S) rr)
    (hZ : ∀ x k, OnGrid G (Z x k))
    (hstep : ∀ x, Z' x = ka • Z x + kb • Z (setB x ⟨m, hm⟩ ⟨ρ, hρ⟩ (!(x.2.1 ⟨m, hm⟩ ⟨ρ, hρ⟩))))
    (i : ℕ) :
    recOf hA hS F Z' i =
      if i % (2 * (S * 2 ^ (K * (D - 1 - m) + ρ))) < S * 2 ^ (K * (D - 1 - m) + ρ) then
        List.zipWith cgate0 (recOf hA hS F Z i)
          (recOf hA hS F Z (i + S * 2 ^ (K * (D - 1 - m) + ρ)))
      else List.zipWith cgate1 (recOf hA hS F Z (i - S * 2 ^ (K * (D - 1 - m) + ρ)))
          (recOf hA hS F Z i) := by
  have hbit := DrvPPAux.layerAddr_bit (A := A) hA hS i m ρ hm hρ
  unfold recOf
  split_ifs with hlt
  · have hb : (i / S).testBit (K * (D - 1 - m) + ρ) = false :=
      (DrvPh1Idx.bit_iff_mod hS i).2 hlt
    rw [zipWith_finRange]
    refine List.map_congr_left fun k _ => ?_
    rw [hstep, hbit, hb, Bool.not_false]
    rw [show setB (layerAddrOfIndex A K D S hA hS i) ⟨m, hm⟩ ⟨ρ, hρ⟩ true =
        layerAddrOfIndex A K D S hA hS (i + S * 2 ^ (K * (D - 1 - m) + ρ)) from
      DrvPh1Idx.addr_set_true hA hS hm hρ i hb]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact halve0 hF (hZ _ k) (hZ _ k)
  · have hb : (i / S).testBit (K * (D - 1 - m) + ρ) = true := by
      cases h : (i / S).testBit (K * (D - 1 - m) + ρ)
      · exact absurd ((DrvPh1Idx.bit_iff_mod hS i).1 h) hlt
      · rfl
    rw [zipWith_finRange]
    refine List.map_congr_left fun k _ => ?_
    rw [hstep, hbit, hb, Bool.not_true]
    rw [show setB (layerAddrOfIndex A K D S hA hS i) ⟨m, hm⟩ ⟨ρ, hρ⟩ false =
        layerAddrOfIndex A K D S hA hS (i - S * 2 ^ (K * (D - 1 - m) + ρ)) from
      DrvPh1Idx.addr_set_false hA hS hm hρ i hb]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_comm (ka * Z (layerAddrOfIndex A K D S hA hS i) k)]
    exact halve1 hF (hZ _ k) (hZ _ k)

/-- **The phase-1 invariant.** After `m ≤ q₁` kernel passes, the integer list is the stored
`Zs ρ (twist ρ z) m` at precision `P + Δ`, and `Zs ρ (twist ρ z) m` lies on the `(P + m)`-grid. -/
theorem ph1_inv (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (hρ : t.ρ < t.K)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (hz : ArrOnDiskGrid t.P z)
    (hq : drvQ1 t ≤ drvDelta t) :
    ∀ m, m ≤ drvQ1 t →
      (List.range m).foldl (ph1Step t)
          ((encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) z).mapIdx
            (phaseRec t.S t.K t.ρ t.D 0 0)) =
        (List.range (t.A * 2 ^ (t.K * t.D) * t.S)).map
          (recOf hA hS (t.P + drvDelta t) (Zs t.ρ (twist ⟨t.ρ, hρ⟩ z) m)) ∧
      ∀ x k, OnGrid (t.P + m) (Zs t.ρ (twist ⟨t.ρ, hρ⟩ z) m x k) := by
  have hQD : drvQ1 t ≤ t.D := by
    unfold drvQ1
    exact min_le_right _ _
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · rw [List.range_zero, List.foldl_nil, Zs_zero, encArr_eq, DrvPPAux.mapIdx_map_range]
      refine List.map_congr_left fun i _ => ?_
      have hcard : (Finset.univ.filter fun j =>
          (layerAddrOfIndex t.A t.K t.D t.S hA hS i).2.1 j ⟨t.ρ, hρ⟩ = true).card =
          selCount t.S t.K t.ρ t.D i :=
        (SubNLogN.Math.Networks.LayerSpecPadAux.selCount_encodeAddr ⟨t.ρ, hρ⟩ _).symm.trans
          (DrvPPAux.sDiag_sum_eq hA hS hρ i)
      rw [phaseRec_zero]
      unfold recOf
      rw [List.map_map]
      refine List.map_congr_left fun k _ => ?_
      simp only [Function.comp_apply, twist]
      rw [hcard]
      exact (gridInt_rot (OnGrid.mono (by omega) (hz _ k).1) _).symm
    · intro x k
      rw [Zs_zero]
      exact onGrid_rot (hz x k).1 _
  | succ m ih =>
    intro hm
    obtain ⟨ihL, ihG⟩ := ih (by omega)
    have hmD : m < t.D := by omega
    have hmq : m + 1 ≤ drvDelta t := le_trans hm hq
    refine ⟨?_, ?_⟩
    · rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ihL]
      unfold ph1Step
      rw [M_eq t hρ hmD, DrvPh1Idx.chunks_cgate _ (drvWj_pos t hS m)]
      refine List.map_congr_left fun i _ => ?_
      rw [rec_step hA hS hρ hmD (G := t.P + drvDelta t - 1) (by omega) _ _
        (fun x k => OnGrid.mono (by omega) (ihG x k)) (fun x => Zs_succ_apply hρ hmD _ x) i]
      rfl
    · intro x k
      rw [Zs_succ_apply hρ hmD]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact onGrid_ka_kb (ihG _ k) (ihG _ k)

end SubNLogN.Machine.Layer.DrvPh1Aux

namespace SubNLogN.Machine.Layer

open SubNLogN.Machine SubNLogN.Math.Walsh DrvPh1Aux

/-- **[MATH] Phase 1 on the stored array** (`DrvPh1BridgeStmt`, unconditional): for a disk-grid
input `z` at precision `P`, `ρ < K` and `min(q₀, D) ≤ Δ`, the phase-1 array `drvA1 t z` stored at
precision `P + Δ` is `ph1Int t` of `z` stored at precision `P + Δ`. -/
theorem drvPh1Bridge_holds : DrvPh1BridgeStmt := by
  intro t hA hS z hρ _hD hq hz
  obtain ⟨hL, -⟩ := ph1_inv t hA hS hρ z hz hq (drvQ1 t) le_rfl
  have hA1 : drvA1 t z = Zs t.ρ (twist ⟨t.ρ, hρ⟩ z) (drvQ1 t) :=
    congrArg SubNLogN.Math.Networks.decodeArr
      (SubNLogN.Math.Networks.LayerSpecPadAux.phase1_eq t.d ⟨t.ρ, hρ⟩ z)
  unfold ph1Int
  rw [hL, encArr_eq, hA1]

end SubNLogN.Machine.Layer
