import WP.W9ex.Cost

/-!
# WP.W9ex.Main — the extract program and its machine-level specification

`extractProg = setup; phaseA; phaseB; finish` over `BLoc 4`. `xt_extract`: from any state with the
root header on `C0` and the one-node stream `⟦[v]⟧` on `S`, the program consumes the stream and
pushes `hdrSyms ((v.toList.take (k1 + k2)).map mdig)` on `OA` (digit 0 on top); every other stack,
including the four scratch stacks, is restored. Cost `≤ 64 · (2^K0 · (eb wR + b + K0) +
rootHdrLen + 1)`.
-/

namespace WP.W9ex

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-- **The extract program** (root phase R5). -/
def extractProg : SProg K4 := .seq setup (.seq phaseA (.seq phaseB finish))

theorem extractProg_closed : extractProg.Closed := freeBelow_of_noRec _ 0 rfl

theorem guard_not_mem_rev (ds : List ℕ) : symGuard ∉ (hdrSyms ds).reverse := by
  rw [List.mem_reverse]
  exact tag_not_mem_hdrSyms 7 ds

theorem not_mem_append' {x : Sym} {A B : List Sym} (hA : x ∉ A) (hB : x ∉ B) : x ∉ A ++ B := by
  rw [List.mem_append]
  exact fun h => h.elim hA hB

/-- **Machine-level specification of the extract program.** -/
theorem xt_extract (σ : K4 → List Sym) (b K0 k1 k2 wR : ℕ) (v : Array (ℤ × ℤ))
    (restS r0 : List Sym) (hv : v.size = 2 ^ K0) (hk : k1 + k2 ≤ 2 ^ K0) (hw : ArrW wR v)
    (hC0 : σ sC0 = hdrSyms [b, K0, k1, k2] ++ r0) (hS : σ sS = streamSyms [v] ++ restS) :
    XT σ extractProg (Function.update (Function.update σ sS restS) sOA
      (hdrSyms ((v.toList.take (k1 + k2)).map mdig) ++ σ sOA))
      (64 * (2 ^ K0 * (eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1)) := by
  set l := v.toList with hl
  have hlen : l.length = 2 ^ K0 := by rw [hl, Array.length_toList, hv]
  have hS' : σ sS = blkE l ++ symNode :: symLevel :: restS := by
    rw [hS]
    simp [streamSyms, nodeSyms, hl]
  have hwl : ∀ z ∈ l, EntryW wR z := hw
  -- the four phases
  have h0 := xt_setup σ (σ sS) (σ sC0) (σ sOA) (σ sD) (σ sH) (σ sc)
  rw [Φ_self, hS', hC0] at h0
  have hA := xt_phaseA σ l (symNode :: symLevel :: restS) b K0 k1 k2 wR r0 (σ sOA) (σ sD) (σ sH)
    (σ sc) (by omega) hwl (bitLen_succ_le (by omega))
  have hB := xt_phaseB σ (l.drop k1) (symNode :: symLevel :: restS) b K0 k1 k2 wR r0 (σ sOA)
    ((hdrSyms ((l.take k1).map mdig)).reverse ++ symGuard :: σ sD) (σ sH) (σ sc)
    (by rw [List.length_drop]; omega) (fun z hz => hwl z (List.mem_of_mem_drop hz))
    (bitLen_succ_le (by omega))
  have hF := xt_finish σ ((l.drop k1).drop k2) restS (hdrSyms [k2] ++ r0) (σ sOA)
    ((hdrSyms (((l.drop k1).take k2).map mdig)).reverse ++
      ((hdrSyms ((l.take k1).map mdig)).reverse ++ symGuard :: σ sD))
    ((hdrSyms [k1]).reverse ++ ((hdrSyms [K0]).reverse ++ ((hdrSyms [b]).reverse ++
      symGuard :: σ sH)))
    ((hdrSyms (((l.drop k1).take k2).map mdig)).reverse ++
      (hdrSyms ((l.take k1).map mdig)).reverse)
    (σ sD) ((hdrSyms [k1]).reverse ++ ((hdrSyms [K0]).reverse ++ (hdrSyms [b]).reverse)) (σ sH)
    (σ sc) (not_mem_append' (guard_not_mem_rev _) (guard_not_mem_rev _))
    (not_mem_append' (guard_not_mem_rev _) (not_mem_append' (guard_not_mem_rev _)
      (guard_not_mem_rev _))) (by simp only [List.append_assoc])
    (by simp only [List.append_assoc])
  -- the final stacks
  have eC : ((hdrSyms [k1]).reverse ++ ((hdrSyms [K0]).reverse ++
      (hdrSyms [b]).reverse)).reverse ++ (hdrSyms [k2] ++ r0) = σ sC0 := by
    rw [hC0]
    simp [hdrSyms]
  have eO : ((hdrSyms (((l.drop k1).take k2).map mdig)).reverse ++
      (hdrSyms ((l.take k1).map mdig)).reverse).reverse =
        hdrSyms ((l.take (k1 + k2)).map mdig) := by
    rw [List.take_add]
    simp [hdrSyms_append]
  -- the cost
  have hLh : ((hdrSyms [k1]).reverse ++ ((hdrSyms [K0]).reverse ++
      (hdrSyms [b]).reverse)).length = bitLen k1 + 1 + (bitLen K0 + 1 + (bitLen b + 1)) := by
    simp only [List.length_append, List.length_reverse, hdrSyms_singleton, List.length_singleton,
      length_natSyms]
  have hR : (blkE ((l.drop k1).drop k2)).length ≤ 2 ^ K0 * eb wR := by
    refine le_trans (length_blkE_le wR _ (fun z hz =>
      hwl z (List.mem_of_mem_drop (List.mem_of_mem_drop hz)))) ?_
    apply Nat.mul_le_mul_right
    simp only [List.length_drop]
    omega
  have hLd : ((hdrSyms (((l.drop k1).take k2).map mdig)).reverse ++
      (hdrSyms ((l.take k1).map mdig)).reverse).length ≤ 2 ^ K0 * eb wR := by
    rw [← List.length_reverse, eO]
    refine le_trans (length_hdrSyms_le wR _ ?_) ?_
    · intro d hd
      rw [List.mem_map] at hd
      obtain ⟨z, hz, rfl⟩ := hd
      exact le_trans (bitLen_mdig z) (hwl z (List.mem_of_mem_take hz)).2
    · rw [List.length_map, List.length_take, hlen, Nat.min_eq_left hk]
      exact Nat.mul_le_mul hk (by unfold eb; omega)
  have hc := cost_le (2 ^ K0) K0 b (eb wR) k1 k2 (bitLen b) (bitLen K0) (bitLen k1) (bitLen k2)
    _ _ _ hk (by unfold eb; omega) hLh hR hLd
  refine ((h0.seq (hA.seq (hB.seq hF))).congr ?_).mono ?_
  · rw [eC, eO, Φ_final]
  · rw [rootHdrLen_eq]
    omega

#assert_std_axioms extractProg_closed guard_not_mem_rev not_mem_append' xt_extract

end WP.W9ex
