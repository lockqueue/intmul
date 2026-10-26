/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreMathDefs

/-!
# The row reshape on the stored array (`Machine/Layer/DrvPadBridge.lean`)

**Theorem** (`drvPadBridge_holds : DrvPadBridgeStmt`, fully proved): in the rows case, the stored
stage input `drvStageIn t h z` (lexicographic order of the reshaped layout) is the stored phase-1
array `drvA1 t z` with `drvNpad t` zero records inserted after every prefix block of `drvKeep t`
records, at any precision `F`.

Proof (namespace `SubNLogN.Machine.Layer.DrvPadBridgeAux`):
* `pad_chunksOf_map_range`: inserting `p` copies of `c` after every block of `n` elements of a
  `List.range`-indexed list is the `List.range`-indexed list of the padded positions;
* `embed_rec`: at lexicographic index `i` of the reshaped layout, the embedded array is the
  original record at index `⌊i/B⌋·keep + i mod B` if `i mod B < keep` (`unpad_addr` of
  `DrvPostMath.lean` and injectivity of `mergeAddr`), and zero otherwise (the prefix field of a
  merged address has row part `< 2^{qK}`); `B = R·2^{K(D-q)}·S`, `keep = 2^{KD}·S`.
-/

namespace SubNLogN.Machine.Layer.DrvPadBridgeAux

open SubNLogN.Machine SubNLogN.Machine.Layer SubNLogN.Machine.Layer.DrvPPAux
open SubNLogN.Math.Networks (layerLayout encodeAddr decodeAddr mergeAddr embedArr encodeArr
  decodeArr padR q0Of)
open SubNLogN.Math.Walsh (RArr LayerAddr)

/-! ## Padded lists over index ranges -/

theorem pad_range_split {β : Type} (n p : ℕ) (g : ℕ → β) (c : β) :
    (List.range (n + p)).map (fun i => if i < n then g i else c) =
      (List.range n).map g ++ List.replicate p c := by
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · exact List.map_congr_left fun i hi => by rw [List.mem_range] at hi; simp [hi]
  · apply List.ext_getElem (by simp)
    intro j h1 h2
    simp [show ¬ (n + j < n) by omega]

/-- Padding every block of `n` elements by `p` copies of `c`. -/
theorem pad_chunksOf_map_range {β : Type} (n p : ℕ) (c : β) (hnp : 0 < n + p) :
    ∀ (k : ℕ) (g : ℕ → β),
      ((chunksOf n k ((List.range (k * n)).map g)).map
          (fun blk => blk ++ List.replicate p c)).flatten =
        (List.range (k * (n + p))).map fun i =>
          if i % (n + p) < n then g (i / (n + p) * n + i % (n + p)) else c
  | 0, g => by simp [chunksOf]
  | k + 1, g => by
    rw [show (k + 1) * n = n + k * n by ring,
      show (k + 1) * (n + p) = (n + p) + k * (n + p) by ring,
      List.range_add, List.range_add, List.map_append, List.map_append]
    have hlen : ((List.range n).map g).length = n := by simp
    simp only [chunksOf, List.map_cons, List.flatten_cons]
    rw [List.take_left' hlen, List.drop_left' hlen, List.map_map,
      pad_chunksOf_map_range n p c hnp k (g ∘ (n + ·)), List.map_map]
    congr 1
    · rw [← pad_range_split n p g c]
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      simp only [Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi, Nat.zero_mul, Nat.zero_add]
    · refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp]
      rw [Nat.add_mod_left, Nat.add_div_left _ hnp]
      split_ifs
      · congr 1
        ring
      · rfl

/-! ## The embedded array in lexicographic order -/

/-- At lexicographic index `i` of the reshaped layout the embedded array is the original record at
index `⌊i/B⌋·keep + i mod B` if `i mod B < keep`, and zero otherwise. -/
theorem embed_rec {A K D S q R r : ℕ} (hA : 0 < A) (hS : 0 < S) (hR : 0 < R) (hq : q ≤ D)
    (hRq : 2 ^ (K * q) ≤ R) (w : RArr (LayerAddr A K D S) r) (i : ℕ)
    (hi : i < A * (R * (2 ^ (K * (D - q)) * S))) :
    decodeArr (embedArr hR hq (encodeArr w))
        (layerAddrOfIndex (A * R) K (D - q) S (Nat.mul_pos hA hR) hS i) =
      if i % (R * (2 ^ (K * (D - q)) * S)) < 2 ^ (K * D) * S then
        w (layerAddrOfIndex A K D S hA hS
          (i / (R * (2 ^ (K * (D - q)) * S)) * (2 ^ (K * D) * S) +
            i % (R * (2 ^ (K * (D - q)) * S))))
      else 0 := by
  have hB'pos : 0 < 2 ^ (K * (D - q)) * S := by positivity
  have hBlkpos : 0 < R * (2 ^ (K * (D - q)) * S) := Nat.mul_pos hR hB'pos
  have hdec : 2 ^ (K * D) * S = 2 ^ (K * q) * (2 ^ (K * (D - q)) * S) := by
    rw [← mul_assoc, ← pow_add, ← Nat.mul_add, Nat.add_sub_cancel' hq]
  have hi_eq : i = i / (R * (2 ^ (K * (D - q)) * S)) * (R * (2 ^ (K * (D - q)) * S)) +
      i % (R * (2 ^ (K * (D - q)) * S)) := (Nat.div_add_mod' i _).symm
  have ha_lt : i / (R * (2 ^ (K * (D - q)) * S)) < A :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  have hrem_lt : i % (R * (2 ^ (K * (D - q)) * S)) < R * (2 ^ (K * (D - q)) * S) :=
    Nat.mod_lt _ hBlkpos
  generalize ha : i / (R * (2 ^ (K * (D - q)) * S)) = a at hi_eq ha_lt ⊢
  generalize hrem : i % (R * (2 ^ (K * (D - q)) * S)) = rem at hi_eq hrem_lt ⊢
  show embedArr hR hq (encodeArr w)
    (encodeAddr (layerAddrOfIndex (A * R) K (D - q) S (Nat.mul_pos hA hR) hS i)) = _
  split_ifs with hlt
  · -- a data record
    have hkpos : 0 < 2 ^ (K * D) * S := by positivity
    have hj_lt : a * (2 ^ (K * D) * S) + rem < A * (2 ^ (K * D) * S) := by
      calc a * (2 ^ (K * D) * S) + rem < a * (2 ^ (K * D) * S) + 2 ^ (K * D) * S := by omega
        _ = (a + 1) * (2 ^ (K * D) * S) := by ring
        _ ≤ A * (2 ^ (K * D) * S) := Nat.mul_le_mul_right _ ha_lt
    have hjdiv : (a * (2 ^ (K * D) * S) + rem) / (2 ^ (K * D) * S) = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hkpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
    have hjmod : (a * (2 ^ (K * D) * S) + rem) % (2 ^ (K * D) * S) = rem := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    have haddr := unpad_addr hA hS hR hq hRq (a * (2 ^ (K * D) * S) + rem) hj_lt
    rw [hjdiv, hjmod, ← hi_eq] at haddr
    have hmerge : encodeAddr (layerAddrOfIndex (A * R) K (D - q) S (Nat.mul_pos hA hR) hS i) =
        mergeAddr A K D S q R hR hq
          (encodeAddr (layerAddrOfIndex A K D S hA hS (a * (2 ^ (K * D) * S) + rem))) := by
      rw [← haddr, SubNLogN.Math.Networks.LayerSpecPadAux.encodeAddr_decodeAddr]
    rw [hmerge]
    have hRq' : 2 ^ (q * K) ≤ R := by rw [Nat.mul_comm]; exact hRq
    have hex : ∃ x, mergeAddr A K D S q R hR hq x = mergeAddr A K D S q R hR hq
        (encodeAddr (layerAddrOfIndex A K D S hA hS (a * (2 ^ (K * D) * S) + rem))) := ⟨_, rfl⟩
    have heq := SubNLogN.Math.Networks.LayerSpecPadAux.mergeAddr_injective hR hq hRq'
      (Classical.choose_spec hex)
    simp only [embedArr, dif_pos hex, heq, encodeArr,
      SubNLogN.Math.Networks.LayerSpecPadAux.decodeAddr_encodeAddr]
  · -- a padding record
    have hne : ¬ ∃ x, mergeAddr A K D S q R hR hq x =
        encodeAddr (layerAddrOfIndex (A * R) K (D - q) S (Nat.mul_pos hA hR) hS i) := by
      rintro ⟨x, hx⟩
      have e0 : (mergeAddr A K D S q R hR hq x ⟨0, by simp [layerLayout]⟩).val =
          (encodeAddr (layerAddrOfIndex (A * R) K (D - q) S (Nat.mul_pos hA hR) hS i)
            ⟨0, by simp [layerLayout]⟩).val := by rw [hx]
      rw [mergeAddr_zero] at e0
      have hrhs : (encodeAddr (layerAddrOfIndex (A * R) K (D - q) S (Nat.mul_pos hA hR) hS i)
          ⟨0, by simp [layerLayout]⟩).val = i / (2 ^ (K * (D - q)) * S) % (A * R) := rfl
      rw [hrhs] at e0
      have hqK : q * K ≤ D * K := Nat.mul_le_mul_right _ hq
      have hn : 1 + q * K ≤ (layerLayout A K D S).n := by simp only [layerLayout]; omega
      have hbx : (layerLayout A K D S).blockVal 1 (1 + q * K) x < 2 ^ (K * q) := by
        have h1 :=
          SubNLogN.Math.Networks.LayerSpecPadAux.blockVal_lt_blockRange 1 (1 + q * K) hn x
        rw [SubNLogN.Math.Networks.LayerSpecPadAux.blockRange_chunks (q * K) hqK] at h1
        rw [Nat.mul_comm K q]; exact h1
      have hbxR : (layerLayout A K D S).blockVal 1 (1 + q * K) x < R := lt_of_lt_of_le hbx hRq
      have hw : i / (2 ^ (K * (D - q)) * S) = a * R + rem / (2 ^ (K * (D - q)) * S) := by
        rw [hi_eq, show a * (R * (2 ^ (K * (D - q)) * S)) + rem =
            rem + a * R * (2 ^ (K * (D - q)) * S) by ring,
          Nat.add_mul_div_right _ _ hB'pos, Nat.add_comm]
      have hwR : rem / (2 ^ (K * (D - q)) * S) < R := (Nat.div_lt_iff_lt_mul hB'pos).2 hrem_lt
      have hwge : 2 ^ (K * q) ≤ rem / (2 ^ (K * (D - q)) * S) :=
        (Nat.le_div_iff_mul_le hB'pos).2 (by rw [← hdec]; omega)
      have hlt' : a * R + rem / (2 ^ (K * (D - q)) * S) < A * R := by
        calc a * R + rem / (2 ^ (K * (D - q)) * S) < a * R + R := by omega
          _ = (a + 1) * R := by ring
          _ ≤ A * R := Nat.mul_le_mul_right R ha_lt
      rw [hw, Nat.mod_eq_of_lt hlt', Nat.mod_eq_of_lt hbxR] at e0
      have h2 : ((layerLayout A K D S).blockVal 1 (1 + q * K) x +
          (x ⟨0, by simp [layerLayout]⟩).val * R) % R =
          (rem / (2 ^ (K * (D - q)) * S) + a * R) % R := by
        rw [Nat.add_comm _ ((x ⟨0, by simp [layerLayout]⟩).val * R),
          Nat.add_comm (rem / (2 ^ (K * (D - q)) * S)), e0]
      rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbxR,
        Nat.mod_eq_of_lt hwR] at h2
      omega
    simp only [embedArr, dif_neg hne]

end SubNLogN.Machine.Layer.DrvPadBridgeAux

namespace SubNLogN.Machine.Layer

open SubNLogN.Machine SubNLogN.Machine.Layer.DrvPPAux SubNLogN.Machine.Layer.DrvPadBridgeAux
open SubNLogN.Math.Networks (embedArr encodeArr decodeArr padR q0Of)

/-- **The row reshape on the stored array** (`DrvPadBridgeStmt`). -/
theorem drvPadBridge_holds : DrvPadBridgeStmt := by
  intro t h hA hS F z
  have hR : 0 < padR t.d t.K := h.2
  have hq : q0Of t.d ≤ t.D := h.1.le
  have hRq : 2 ^ (t.K * q0Of t.d) ≤ padR t.d t.K := le_padR t.d t.K
  have hNpad : drvNpad t =
      (padR t.d t.K - 2 ^ (q0Of t.d * t.K)) * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S) := by
    unfold drvNpad; rw [if_pos h]
  have hKeep : drvKeep t = 2 ^ (t.K * t.D) * t.S := rfl
  have hdec : 2 ^ (t.K * t.D) * t.S =
      2 ^ (t.K * q0Of t.d) * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S) := by
    rw [← mul_assoc, ← pow_add, ← Nat.mul_add, Nat.add_sub_cancel' hq]
  have hBlk : drvKeep t + drvNpad t = padR t.d t.K * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S) := by
    rw [hNpad, hKeep, hdec, Nat.mul_comm (q0Of t.d) t.K, ← Nat.add_mul,
      Nat.add_sub_cancel' hRq]
  have hKpos : 0 < drvKeep t := by rw [hKeep]; positivity
  have e1 : drvStageIn t h z = decodeArr (embedArr h.2 h.1.le (encodeArr (drvA1 t z))) := by
    unfold drvStageIn drvA1
    rw [SubNLogN.Math.Networks.LayerSpecPadAux.encodeArr_decodeArr]
  rw [e1, encArr_layerAddrs (Nat.mul_pos hA h.2) hS, encArr_layerAddrs hA hS,
    show drvA' t * 2 ^ (t.K * drvD' t) * t.S = t.A * (drvKeep t + drvNpad t) by
      rw [hBlk]; unfold drvA' drvD'; ring,
    show t.A * 2 ^ (t.K * t.D) * t.S = t.A * drvKeep t by rw [hKeep]; ring]
  unfold padBlock
  rw [pad_chunksOf_map_range (drvKeep t) (drvNpad t) (List.replicate t.r (0, 0)) (by omega)]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have hi' : i < t.A * (padR t.d t.K * (2 ^ (t.K * (t.D - q0Of t.d)) * t.S)) := by
    rwa [← hBlk]
  have hrec := embed_rec hA hS hR hq hRq (drvA1 t z) i hi'
  rw [← hBlk, ← hKeep] at hrec
  split_ifs with hlt
  · rw [if_pos hlt] at hrec
    rw [hrec]
  · rw [if_neg hlt] at hrec
    rw [hrec]
    simp [gridInt]

end SubNLogN.Machine.Layer
