/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreShl
import SubNLogN.Machine.Layer.DrvMathAux

/-!
# Layer driver pre-phase: the value assembly (`Machine/Layer/DrvPreMidT1.lean`, T1)

* `mid_eq`: the pre-phase output (shift by `Δ`, phase 1 on the stored array (`ph1Int`), then the
  padding of every prefix block) is `drvMidSyms t hA hS z`, given the two value bridges
  `DrvPh1BridgeStmt` and `DrvPadBridgeStmt` (rows case: the pad bridge; otherwise `drvNpad t = 0`
  and the blocks just flatten back).
* `pad_shape`: the padded array has records of length `r` when the input does.
* `pad_len`: the padded array has at most `2M` records when the input has `M`
  (`drvNpad t ≤ drvKeep t`, `drvNpad_le_keep`).

**Scope (honest summary).** Proved lemmas only (the two bridges enter as hypotheses of `mid_eq`).
Helpers live in `SubNLogN.Machine.Layer.DrvPreMidT1`.
-/

namespace SubNLogN.Machine.Layer.DrvPreMidT1

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
  SubNLogN.Machine.Layer
open SubNLogN.Math.Networks (padR q0Of)

/-- An element of a chunk is an element of the list. -/
theorem mem_of_mem_chunksOf {α : Type} (n : ℕ) : ∀ (k : ℕ) (l blk : List α),
    blk ∈ DrvPPAux.chunksOf n k l → ∀ x ∈ blk, x ∈ l
  | 0, l, blk, h => by simp [DrvPPAux.chunksOf] at h
  | k + 1, l, blk, h => by
    intro x hx
    simp only [DrvPPAux.chunksOf, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_of_mem_take hx
    · exact List.mem_of_mem_drop (mem_of_mem_chunksOf n k (l.drop n) blk h x hx)

/-- The length of padded blocks of length `m`. -/
theorem length_flatten_padBlock (Npad r m : ℕ) : ∀ (blks : List (List (List CInt))),
    (∀ blk ∈ blks, blk.length = m) →
      ((blks.map (padBlock Npad r)).flatten).length = blks.length * (m + Npad)
  | [], _ => by simp
  | blk :: blks, h => by
    rw [List.map_cons, List.flatten_cons, List.length_append,
      length_flatten_padBlock Npad r m blks (fun b hb => h b (List.mem_cons_of_mem _ hb)),
      List.length_cons]
    have hb := h blk List.mem_cons_self
    simp only [padBlock, List.length_append, List.length_replicate, hb]
    ring

/-- `drvNpad t ≤ drvKeep t` (for `K ≥ 1`): `padR - 2^{q₀K} ≤ 2^{q₀K}` (`padR_le`). -/
theorem drvNpad_le_keep (t : LayerRT) (hK : 1 ≤ t.K) : drvNpad t ≤ drvKeep t := by
  unfold drvNpad drvKeep
  split_ifs with h
  · have hq : q0Of t.d < t.D := h.1
    have hp := DrvMathAux.padR_le t.d t.K hK
    rw [pow_succ] at hp
    have hsub : padR t.d t.K - 2 ^ (q0Of t.d * t.K) ≤ 2 ^ (q0Of t.d * t.K) := by omega
    have h1 : q0Of t.d * t.K + t.K * (t.D - q0Of t.d) = t.K * t.D := by
      rw [Nat.mul_comm (q0Of t.d), ← Nat.mul_add, Nat.add_sub_cancel' hq.le]
    have e : 2 ^ (q0Of t.d * t.K) * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S) =
        2 ^ (t.K * t.D) * t.S := by
      rw [← Nat.mul_assoc, ← pow_add, h1]
    calc (padR t.d t.K - 2 ^ (q0Of t.d * t.K)) * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S)
        ≤ 2 ^ (q0Of t.d * t.K) * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S) :=
          Nat.mul_le_mul_right _ hsub
      _ = 2 ^ (t.K * t.D) * t.S := e
  · exact Nat.zero_le _

/-- **The pre-phase value**: shift, phase 1, padding, then the guarded-width encoding, is
`drvMidSyms` (given the phase-1 and pad bridges). -/
theorem mid_eq (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (hρ : t.ρ < t.K) (hD : 1 ≤ t.D)
    (hq : drvQ1 t ≤ drvDelta t) (hz : ArrOnDiskGrid t.P z) (hPh1 : DrvPh1BridgeStmt)
    (hPadB : DrvPadBridgeStmt) :
    carrSyms (drvWg t) (((DrvPPAux.chunksOf (drvKeep t) t.A
      (ph1Int t (mapC (shlC (drvDelta t)) (encLayer hA hS t.P z)))).map
        (padBlock (drvNpad t) t.r)).flatten) = drvMidSyms t hA hS z := by
  rw [DrvPreShlAux.shl_enc t hA hS z hz, ← hPh1 t hA hS z hρ hD hq hz]
  unfold drvMidSyms
  split_ifs with h
  · rw [hPadB t h hA hS (t.P + drvDelta t) z]
  · have hnp : drvNpad t = 0 := by
      unfold drvNpad
      exact if_neg h
    have hpad0 : ∀ blk : List (List CInt), padBlock 0 t.r blk = blk := by
      intro blk
      simp [padBlock]
    have hmap : ∀ l : List (List (List CInt)), l.map (padBlock 0 t.r) = l := by
      intro l
      induction l with
      | nil => rfl
      | cons b l ih => rw [List.map_cons, hpad0, ih]
    have hlen : (encArr (t.P + drvDelta t) (layerAddrs t.A t.K t.D t.S hA hS) (drvA1 t z)).length =
        drvKeep t * t.A := by
      rw [DrvPPAux.encArr_length', DrvPPAux.layerAddrs_length']
      unfold drvKeep
      ring
    rw [hnp, hmap, DrvPPAux.chunksOf_flatten (drvKeep t) t.A _ hlen]

/-- **Record shape of the padded array**: every record has `r` coefficients. -/
theorem pad_shape (t : LayerRT) (L : List (List CInt)) (hL : ∀ cs ∈ L, cs.length = t.r) :
    ∀ cs ∈ ((DrvPPAux.chunksOf (drvKeep t) t.A L).map (padBlock (drvNpad t) t.r)).flatten,
      cs.length = t.r := by
  intro cs hcs
  simp only [List.mem_flatten, List.mem_map] at hcs
  obtain ⟨_, ⟨blk, hblk, rfl⟩, hcs⟩ := hcs
  unfold padBlock at hcs
  rcases List.mem_append.1 hcs with h | h
  · exact hL cs (mem_of_mem_chunksOf _ _ _ blk hblk cs h)
  · rw [List.eq_of_mem_replicate h, List.length_replicate]

/-- **Record count of the padded array**: at most `2M` (for `K ≥ 1` and `M` input records). -/
theorem pad_len (t : LayerRT) (hK : 1 ≤ t.K) (L : List (List CInt)) (hL : L.length = t.M) :
    (((DrvPPAux.chunksOf (drvKeep t) t.A L).map (padBlock (drvNpad t) t.r)).flatten).length ≤
      2 * t.M := by
  have hM : drvKeep t * t.A = t.M := by
    unfold drvKeep LayerRT.M
    ring
  have hLk : L.length = drvKeep t * t.A := by rw [hL, hM]
  rw [length_flatten_padBlock (drvNpad t) t.r (drvKeep t) _
    (DrvPPAux.chunksOf_length_mem (drvKeep t) t.A L hLk), DrvPPAux.chunksOf_length]
  have hnp := drvNpad_le_keep t hK
  calc t.A * (drvKeep t + drvNpad t) ≤ t.A * (2 * drvKeep t) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * t.M := by rw [← hM]; ring

end SubNLogN.Machine.Layer.DrvPreMidT1
