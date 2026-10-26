/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskDefs
import SubNLogN.Machine.CCore.LeafPhaseVal
import SubNLogN.Math.Networks.Proofs.CCoreEdgeBits

/-!
# C-core phase leaf: the value statement of the signs `zSlot`/`zMask` (`LeafPhaseMaskVal.lean`)

Proves `maskVal_holds : LeafScalarAux.MaskValStmt` (`CCore/LeafPhaseMaskDefs.lean`): for
`κ = zSlot sl` or `κ = zMask a`, the stored array of `runSteps [phaseStep t κ] w` is the record-wise
selection between the stored input and its negation (`rotIPowC 2`) by
`selBit (kindSlots κ) K D S j0 (m^(k-1)) ρ`.

Proof. Both kinds are value-level `addrMap` steps multiplying record `x` by `(-1)^{n x}`
(`runSteps_addrMap`). On the lexicographic record `i` (address `layerAddrOfIndex … i`), the selected
bit of chunk `j0 + s f + c` read by `slotBit` is `chunkBit K D S i (j0 + s f + c) ρ`
(`CCoreEdgeAux.slotBit_encode`), so `n` is the slot sum of `selBit` (for `zMask`: exchange the sums,
the coefficients `(u_a)_p ∈ {0,1}` select the slots `p` with `(u_a)_p = 1`, reindexed by
`cubeEquiv`). On the grid, `gridInt` of `(-1)^n z` is `rotIPowC 2` of `gridInt z` for odd `n`
(`gridInt_Ipow`), which gives the selection record by record (`encArr_sign_m`).
-/

namespace SubNLogN.Machine.CCore.PhaseMaskAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
open SubNLogN.Math.Networks SubNLogN.Machine.Layer.DrvPreK SubNLogN.Machine.CCore.LeafScalarAux

/-- The sign `(-1)^n` on the grid. -/
theorem gridInt_neg_one_pow_m {F : ℕ} {z : ℂ} (h : OnGrid F z) (n : ℕ) :
    gridInt F ((-1 : ℂ) ^ n * z) = if Odd n then rotIPowC 2 (gridInt F z) else gridInt F z := by
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, one_mul, if_neg (Nat.not_odd_iff_even.mpr he)]
  · rw [ho.neg_one_pow, if_pos ho, ← gridInt_Ipow h 2, Complex.I_sq]

/-- Record-wise selection: the stored array of `x ↦ (-1)^{n x} w x` selects the negated record
exactly where `n` is odd. -/
theorem encArr_sign_m {A K D S r F : ℕ} (hA : 0 < A) (hS : 0 < S)
    (w : RArr (LayerAddr A K D S) r) (hw : ∀ x k, OnGrid F (w x k))
    (n : LayerAddr A K D S → ℕ) (b : ℕ → Bool)
    (hb : ∀ i, i < A * 2 ^ (K * D) * S →
      b i = decide (Odd (n (layerAddrOfIndex A K D S hA hS i)))) :
    encArr F (layerAddrs A K D S hA hS) (fun x => (-1 : ℂ) ^ (n x) • w x) =
      selRecs b (encArr F (layerAddrs A K D S hA hS) w)
        (mapC (rotIPowC 2) (encArr F (layerAddrs A K D S hA hS) w)) := by
  have hlen : (encArr F (layerAddrs A K D S hA hS) w).length = A * 2 ^ (K * D) * S := by
    simp [encArr, layerAddrs]
  unfold selRecs
  rw [hlen]
  simp only [encArr, layerAddrs, mapC, List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hget : ∀ (g : ℕ → List CInt),
      ((List.range (A * 2 ^ (K * D) * S)).map g).getD i default = g i := by
    intro g
    simp [List.getD_eq_getElem?_getD, hi]
  rw [hget, hget, hb i hi]
  by_cases ho : Odd (n (layerAddrOfIndex A K D S hA hS i))
  · rw [if_pos (by simp [ho])]
    simp only [Function.comp_apply, List.map_map]
    apply List.map_congr_left
    intro c _
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [gridInt_neg_one_pow_m (hw _ c), if_pos ho]
  · rw [if_neg (by simp [ho])]
    simp only [Function.comp_apply]
    apply List.map_congr_left
    intro c _
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [gridInt_neg_one_pow_m (hw _ c), if_neg ho]

/-- The selected-bit sum of slot `s` of record `i` (the inner sum of `selBit`). -/
def slotSum (K D S j0 f ρ i s : ℕ) : ℕ :=
  ∑ c ∈ Finset.range f, (if chunkBit K D S i (j0 + s * f + c) ρ then 1 else 0)

theorem selBit_eq_m (ss : Finset (Fin mn)) (K D S j0 f ρ i : ℕ) :
    selBit ss K D S j0 f ρ i = decide (Odd (∑ s ∈ ss, slotSum K D S j0 f ρ i s.val)) := rfl

/-- The value-level slot sum on the encoded lexicographic address `i` is `slotSum`. -/
theorem slotBit_sum_encode_m {A K D S : ℕ} (hA : 0 < A) (hS : 0 < S) (j0 f ρ s i : ℕ)
    (hρ : ρ < K) (hb : j0 + s * f + f ≤ D) :
    ∑ c ∈ Finset.range f, slotBit (A := A) (D := D) (S := S) K ρ f j0 s c
        (encodeAddr (layerAddrOfIndex A K D S hA hS i)) = slotSum K D S j0 f ρ i s := by
  unfold slotSum
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mem_range] at hc
  rw [CCoreEdgeAux.slotBit_encode ⟨ρ, hρ⟩ f j0 s c (by omega)]
  rfl

/-- Slots fit: `j0 + s f + f ≤ D` for `s < m`, `f = m^(k-1)`, `j0 + m^k ≤ D`, `1 ≤ k`. -/
theorem slot_le_m {k j0 D s : ℕ} (hk : 1 ≤ k) (hD : j0 + mn ^ k ≤ D) (hs : s < mn) :
    j0 + s * mn ^ (k - 1) + mn ^ (k - 1) ≤ D := by
  have hf : mn ^ k = mn * mn ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : (s + 1) * mn ^ (k - 1) ≤ mn * mn ^ (k - 1) := Nat.mul_le_mul_right _ hs
  nlinarith

theorem ua_val_m (z : ZMod 2) : z.val = if z = 1 then 1 else 0 := by
  revert z
  decide

end PhaseMaskAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
  SubNLogN.Math.Networks SubNLogN.Machine.Layer.DrvPreK SubNLogN.Machine.CCore.LeafScalarAux
  PhaseMaskAux in
/-- **`MaskValStmt`**: the signs `zSlot`/`zMask` on the stored array are the record-wise selection
by `selBit (kindSlots κ) K D S j0 (m^(k-1)) ρ` between the input and its negation. -/
theorem maskVal_holds : LeafScalarAux.MaskValStmt := by
  intro t hA' hS κ hκ hk hρ hD w hw
  rcases hκ with ⟨sl, rfl⟩ | ⟨a, rfl⟩
  · have hrun : runSteps [phaseStep t (.zSlot sl)] w = fun x =>
        (-1 : ℂ) ^ (∑ c ∈ Finset.range (mn ^ (t.k - 1)),
          slotBit (A := t.A / Wn) (D := t.D) (S := t.S) t.K t.ρ (mn ^ (t.k - 1)) t.j0 sl.val c
            (encodeAddr x)) • w x :=
      runSteps_addrMap _ w
    rw [hrun]
    refine encArr_sign_m hA' hS w hw _ _ fun i _ => ?_
    rw [selBit_eq_m, show kindSlots (.zSlot sl) = {sl} from rfl, Finset.sum_singleton]
    exact congrArg (fun m => decide (Odd m))
      (slotBit_sum_encode_m hA' hS t.j0 (mn ^ (t.k - 1)) t.ρ sl.val i hρ
        (slot_le_m hk hD sl.isLt)).symm
  · have hrun : runSteps [phaseStep t (.zMask a)] w = fun x =>
        (-1 : ℂ) ^ (∑ c ∈ Finset.range (mn ^ (t.k - 1)), ∑ p : Cube 100,
          (ua a p).val * slotBit (A := t.A / Wn) (D := t.D) (S := t.S) t.K t.ρ (mn ^ (t.k - 1))
            t.j0 (cubeEquiv p) c (encodeAddr x)) • w x :=
      runSteps_addrMap _ w
    rw [hrun]
    refine encArr_sign_m hA' hS w hw _ _ fun i _ => ?_
    have key : (∑ c ∈ Finset.range (mn ^ (t.k - 1)), ∑ p : Cube 100,
          (ua a p).val * slotBit (A := t.A / Wn) (D := t.D) (S := t.S) t.K t.ρ (mn ^ (t.k - 1))
            t.j0 (cubeEquiv p) c (encodeAddr (layerAddrOfIndex (t.A / Wn) t.K t.D t.S hA' hS i))) =
        ∑ s ∈ kindSlots (.zMask a), slotSum t.K t.D t.S t.j0 (mn ^ (t.k - 1)) t.ρ i s.val := by
      rw [Finset.sum_comm]
      simp only [kindSlots]
      rw [Finset.sum_image (fun p _ q _ h => cubeEquiv.injective (Fin.cast_injective _ h)),
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.mul_sum, slotBit_sum_encode_m hA' hS t.j0 (mn ^ (t.k - 1)) t.ρ (cubeEquiv p) i
        hρ (slot_le_m hk hD (lt_of_lt_of_eq (cubeEquiv p).isLt mH_eq_mn)), ua_val_m]
      split_ifs <;> simp
    rw [selBit_eq_m]
    exact congrArg (fun m => decide (Odd m)) key.symm

end SubNLogN.Machine.CCore
