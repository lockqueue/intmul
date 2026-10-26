import WP.W10b.LevelLin

/-!
# WP.W10b.Chain — the slots along `buildQuantizedSpecPaperStop L p K`

By induction on the fuel `L` (the schedule is a chain). With `E = M·2^K` (invariant along the chain:
`M ↦ M·t1`, `2^K ↦ r`) and `S ≥` every width, `K`, and `2·leafPrecision L p K` (so every precision
of the chain, `≤ leafPrecision`, and every `pSub = 2·pChild` is `≤ S`):
* `chain_slots`: every slot has `cnt ≤ 8E`, `cnt·wid ≤ 192·E·(S+1)`, `wid ≤ 24·(S+1)²`;
* `chain_lin`: the linear parts sum to `≤ 2^16·E·(S+1)·(2K + 2L + 2)` (per level `(K_d+1)`, and the
  log-lengths halve);
* `chain_length`: at most `4L + 4·(log₂ P + 1) + 1` slots (`P = leafPrecision L p K`): four per step
  level, and the leaf's `K_L + 2 ≤ 4(log₂ P + 1) + 1` slots (stop rule `2^K ≤ 4p²`, or `K ≤ 2` when
  the fuel runs out).
-/

namespace WP.W10b

open TMFw.Contracts TMFw.Contracts.W9 IntMul

/-! ## The three kinds of multiplication slots -/

theorem twist_slot_ok (M K S w : ℕ) (hw : w ≤ S) :
    M * (8 * (2 ^ (K / 2) * 2 ^ (K - K / 2))) ≤ 8 * (M * 2 ^ K) ∧
      M * (8 * (2 ^ (K / 2) * 2 ^ (K - K / 2))) * w ≤ 192 * (M * 2 ^ K) * (S + 1) ∧
      w ≤ 24 * (S + 1) ^ 2 := by
  obtain ⟨hmul, -, -, -⟩ := step_dims K
  rw [hmul]
  have h1 : M * (8 * 2 ^ K) * w ≤ M * (8 * 2 ^ K) * S := Nat.mul_le_mul_left _ hw
  have n1 := Nat.zero_le (M * 2 ^ K * S)
  have n2 := Nat.zero_le (M * 2 ^ K)
  refine ⟨by linarith, by linarith, by nlinarith⟩

theorem spread_slot_ok (M K S w q : ℕ) (hw : w ≤ S) (hq : 2 * q ≤ S) :
    M * (2 * 2 ^ (K / 2) * kroneckerSpreadNumBlocks (2 * q) (2 ^ (K - K / 2))) ≤ 8 * (M * 2 ^ K) ∧
      M * (2 * 2 ^ (K / 2) * kroneckerSpreadNumBlocks (2 * q) (2 ^ (K - K / 2))) *
          ((effectiveFilterWidth (2 * q) (2 ^ (K - K / 2)) + 1) * (strideOf (2 * q) + w)) ≤
        192 * (M * 2 ^ K) * (S + 1) ∧
      (effectiveFilterWidth (2 * q) (2 ^ (K - K / 2)) + 1) * (strideOf (2 * q) + w) ≤
        24 * (S + 1) ^ 2 := by
  obtain ⟨hmul, -, -, -⟩ := step_dims K
  have hrpos : 1 ≤ 2 ^ (K - K / 2) := Nat.one_le_two_pow
  obtain ⟨-, -, hWf, hnbW, hnb⟩ := filter_facts (2 * q) (2 ^ (K - K / 2)) hrpos
  have hs : strideOf (2 * q) + w ≤ 4 * S := by unfold strideOf; omega
  generalize hW : effectiveFilterWidth (2 * q) (2 ^ (K - K / 2)) = W at *
  generalize hnbd : kroneckerSpreadNumBlocks (2 * q) (2 ^ (K - K / 2)) = nb at *
  generalize strideOf (2 * q) + w = sw at *
  rw [← hmul]
  generalize 2 ^ (K / 2) = t1 at *
  generalize 2 ^ (K - K / 2) = r at *
  have hnbW1 : nb * (W + 1) ≤ 4 * r := by
    have e : nb * (W + 1) = nb * W + nb := by ring
    omega
  have hW1 : W + 1 ≤ 2 * S + 2 := by omega
  refine ⟨?_, ?_, ?_⟩
  · have h1 : M * (2 * t1 * nb) ≤ M * (2 * t1 * (2 * r)) := Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left _ hnb)
    have n1 := Nat.zero_le (M * (t1 * r))
    linarith
  · calc M * (2 * t1 * nb) * ((W + 1) * sw) = M * 2 * t1 * (nb * (W + 1)) * sw := by ring
      _ ≤ M * 2 * t1 * (4 * r) * (4 * S) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hnbW1) hs
      _ = 32 * (M * (t1 * r)) * S := by ring
      _ ≤ 192 * (M * (t1 * r)) * (S + 1) := by
          have n1 := Nat.zero_le (M * (t1 * r))
          have n2 := Nat.zero_le (M * (t1 * r) * S)
          nlinarith
  · calc (W + 1) * sw ≤ (2 * S + 2) * (4 * S) := Nat.mul_le_mul hW1 hs
      _ ≤ 24 * (S + 1) ^ 2 := by nlinarith

theorem column_slot_ok (M K S q : ℕ) (hq : 2 * q ≤ S) :
    M * (8 * (2 ^ (K / 2) * 2 ^ (K - K / 2))) ≤ 8 * (M * 2 ^ K) ∧
      M * (8 * (2 ^ (K / 2) * 2 ^ (K - K / 2))) * (8 * (barrettH (2 * q) + 1)) ≤
        192 * (M * 2 ^ K) * (S + 1) ∧
      8 * (barrettH (2 * q) + 1) ≤ 24 * (S + 1) ^ 2 := by
  obtain ⟨hmul, -, -, -⟩ := step_dims K
  rw [hmul]
  have hb : 8 * (barrettH (2 * q) + 1) ≤ 24 * (S + 1) := by unfold barrettH; omega
  refine ⟨le_of_eq (by ring), ?_, ?_⟩
  · calc M * (8 * 2 ^ K) * (8 * (barrettH (2 * q) + 1)) ≤ M * (8 * 2 ^ K) * (24 * (S + 1)) :=
          Nat.mul_le_mul_left _ hb
      _ = 192 * (M * 2 ^ K) * (S + 1) := by ring
  · have : S + 1 ≤ (S + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega

theorem leaf_slot_ok (M K S w : ℕ) (hw : w ≤ S) :
    M * (4 * 2 ^ K) ≤ 8 * (M * 2 ^ K) ∧ M * (4 * 2 ^ K) * w ≤ 192 * (M * 2 ^ K) * (S + 1) ∧
      w ≤ 24 * (S + 1) ^ 2 := by
  have h1 : M * (4 * 2 ^ K) * w ≤ M * (4 * 2 ^ K) * S := Nat.mul_le_mul_left _ hw
  have n1 := Nat.zero_le (M * 2 ^ K * S)
  have n2 := Nat.zero_le (M * 2 ^ K)
  refine ⟨by linarith, by linarith, by nlinarith⟩

/-! ## Induction along the chain -/

/-- The leaf of the schedule as slots. -/
theorem specSlots_base (wd : ℕ → ℕ) (p K p_in ℓ M : ℕ) :
    specSlots wd (.base p (2 ^ K)) p_in ℓ M =
      ⟨leafLin wd p K p_in ℓ M, 0, 0⟩ :: List.replicate (K + 1) ⟨0, M * (4 * 2 ^ K), wd ℓ⟩ := by
  simp only [specSlots, Nat.log2_two_pow]

theorem leaf_slots_ok (wd : ℕ → ℕ) (S : ℕ) (hwd : ∀ j, wd j ≤ S) (p K p_in ℓ M : ℕ) :
    ∀ s ∈ specSlots wd (.base p (2 ^ K)) p_in ℓ M,
      s.cnt ≤ 8 * (M * 2 ^ K) ∧ s.cnt * s.wid ≤ 192 * (M * 2 ^ K) * (S + 1) ∧
        s.wid ≤ 24 * (S + 1) ^ 2 := by
  intro s hs
  rw [specSlots_base, List.mem_cons, List.mem_replicate] at hs
  rcases hs with rfl | ⟨-, rfl⟩
  · simp
  · exact leaf_slot_ok M K S (wd ℓ) (hwd ℓ)

/-- **Slot bounds along the chain.** -/
theorem chain_slots (wd : ℕ → ℕ) (S : ℕ) (hwd : ∀ j, wd j ≤ S) :
    ∀ (L p K p_in ℓ M : ℕ), 8 ≤ p → 2 * leafPrecision L p K ≤ S →
      ∀ s ∈ specSlots wd (buildQuantizedSpecPaperStop L p K) p_in ℓ M,
        s.cnt ≤ 8 * (M * 2 ^ K) ∧ s.cnt * s.wid ≤ 192 * (M * 2 ^ K) * (S + 1) ∧
          s.wid ≤ 24 * (S + 1) ^ 2 := by
  intro L
  induction L with
  | zero =>
    intro p K p_in ℓ M _ _
    exact leaf_slots_ok wd S hwd p K p_in ℓ M
  | succ L ih =>
    intro p K p_in ℓ M hp hPS
    have hP' : leafPrecision (L + 1) p K = leafPrecision L (pChild p K) (K - K / 2) := rfl
    have hqP : pChild p K ≤ leafPrecision L (pChild p K) (K - K / 2) := le_leafPrecision _ _ _
    have hq : 2 * pChild p K ≤ S := by omega
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · exact leaf_slots_ok wd S hwd p K p_in ℓ M
    · intro s hs
      simp only [quantizedBoxGaussianStepSpec, specSlots, List.mem_cons] at hs
      rcases hs with rfl | rfl | rfl | rfl | hs
      · simp
      · simpa [preHdrQ, PreHdr.N] using twist_slot_ok M K S (wd ℓ) (hwd ℓ)
      · simpa [preHdrQ, PreHdr.nb, PreHdr.W, PreHdr.s] using
          spread_slot_ok M K S (wd ℓ) (pChild p K) (hwd ℓ) hq
      · simpa [postHdrQ, PostHdr.H] using column_slot_ok M K S (pChild p K) hq
      · have hc := ih (pChild p K) (K - K / 2) (2 * pChild p K) (ℓ + 1) (M * 2 ^ (K / 2))
          (by rw [pChild_eq_additive]; omega) (by rw [← hP']; exact hPS) s hs
        obtain ⟨hmul, -, -, -⟩ := step_dims K
        have e : M * 2 ^ (K / 2) * 2 ^ (K - K / 2) = M * 2 ^ K := by rw [Nat.mul_assoc, hmul]
        rw [e] at hc
        exact hc

/-- **Linear work along the chain.** -/
theorem chain_lin (wd : ℕ → ℕ) (S : ℕ) (hwd : ∀ j, wd j ≤ S) :
    ∀ (L p K p_in ℓ M : ℕ), 8 ≤ p → p_in ≤ S → K ≤ S → 2 * leafPrecision L p K ≤ S → 1 ≤ M →
      ((specSlots wd (buildQuantizedSpecPaperStop L p K) p_in ℓ M).map Slot.lin).sum ≤
        65536 * (M * 2 ^ K) * (S + 1) * (2 * K + 2 * L + 2) := by
  have hleaf : ∀ (L p K p_in ℓ M : ℕ), p_in ≤ S → K ≤ S → p ≤ S → 1 ≤ M →
      ((specSlots wd (.base p (2 ^ K)) p_in ℓ M).map Slot.lin).sum ≤
        65536 * (M * 2 ^ K) * (S + 1) * (2 * K + 2 * L + 2) := by
    intro L p K p_in ℓ M hpin hKS hpS hM
    rw [specSlots_base, List.map_cons, List.sum_cons, List.map_replicate, List.sum_replicate,
      smul_eq_mul, Nat.mul_zero, Nat.add_zero]
    calc leafLin wd p K p_in ℓ M ≤ 65536 * (M * 2 ^ K) * (S + 1) * (K + 1) :=
          leafLin_le wd p K p_in ℓ M S hwd hpin hpS hKS hM
      _ ≤ 65536 * (M * 2 ^ K) * (S + 1) * (2 * K + 2 * L + 2) :=
          Nat.mul_le_mul_left _ (by omega)
  intro L
  induction L with
  | zero =>
    intro p K p_in ℓ M _ hpin hKS hPS hM
    have hpP := le_leafPrecision 0 p K
    exact hleaf 0 p K p_in ℓ M hpin hKS (by omega) hM
  | succ L ih =>
    intro p K p_in ℓ M hp hpin hKS hPS hM
    have hP' : leafPrecision (L + 1) p K = leafPrecision L (pChild p K) (K - K / 2) := rfl
    have hqP : pChild p K ≤ leafPrecision L (pChild p K) (K - K / 2) := le_leafPrecision _ _ _
    have hq : 2 * pChild p K ≤ S := by omega
    have hpq : p ≤ pChild p K := by rw [pChild_eq_additive]; omega
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · exact hleaf (L + 1) p K p_in ℓ M hpin hKS (by omega) hM
    · simp only [quantizedBoxGaussianStepSpec, specSlots, List.map_cons, List.sum_cons,
        Nat.zero_add]
      have hcp : (buildQuantizedSpecPaperStop L (pChild p K) (K - K / 2)).p = pChild p K :=
        buildQuantizedSpecPaperStop_p _ _ _
      rw [hcp]
      have h1 := stepLin_le wd p K (pChild p K) p_in ℓ M S hp hstop hwd hpin hq (by omega) hM
      have ht1pos : 1 ≤ 2 ^ (K / 2) := Nat.one_le_two_pow
      have h2 := ih (pChild p K) (K - K / 2) (2 * pChild p K) (ℓ + 1) (M * 2 ^ (K / 2))
        (by omega) hq (by omega) (by rw [← hP']; exact hPS) (Nat.mul_le_mul hM ht1pos)
      obtain ⟨hmul, -, -, -⟩ := step_dims K
      have e : M * 2 ^ (K / 2) * 2 ^ (K - K / 2) = M * 2 ^ K := by rw [Nat.mul_assoc, hmul]
      rw [e] at h2
      have hK' : (K + 1) + (2 * (K - K / 2) + 2 * L + 2) ≤ 2 * K + 2 * (L + 1) + 2 := by omega
      calc stepLin wd p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) (pChild p K) p_in ℓ M +
            ((specSlots wd (buildQuantizedSpecPaperStop L (pChild p K) (K - K / 2))
              (2 * pChild p K) (ℓ + 1) (M * 2 ^ (K / 2))).map Slot.lin).sum
          ≤ 65536 * (M * 2 ^ K) * (S + 1) * (K + 1) +
              65536 * (M * 2 ^ K) * (S + 1) * (2 * (K - K / 2) + 2 * L + 2) :=
            Nat.add_le_add h1 h2
        _ = 65536 * (M * 2 ^ K) * (S + 1) * ((K + 1) + (2 * (K - K / 2) + 2 * L + 2)) := by ring
        _ ≤ 65536 * (M * 2 ^ K) * (S + 1) * (2 * K + 2 * (L + 1) + 2) :=
            Nat.mul_le_mul_left _ hK'

/-- **Number of slots along the chain.** -/
theorem chain_length (wd : ℕ → ℕ) :
    ∀ (L p K p_in ℓ M : ℕ), 8 ≤ p → K ≤ 2 ^ (L + 1) →
      (specSlots wd (buildQuantizedSpecPaperStop L p K) p_in ℓ M).length ≤
        4 * L + 4 * (Nat.log2 (leafPrecision L p K) + 1) + 1 := by
  intro L
  induction L with
  | zero =>
    intro p K p_in ℓ M _ hK
    simp only [buildQuantizedSpecPaperStop, specSlots_base, List.length_cons,
      List.length_replicate]
    have : K ≤ 2 := by simpa using hK
    omega
  | succ L ih =>
    intro p K p_in ℓ M hp hK
    have hP' : leafPrecision (L + 1) p K = leafPrecision L (pChild p K) (K - K / 2) := rfl
    dsimp only [buildQuantizedSpecPaperStop]
    split_ifs with hstop
    · rw [specSlots_base, List.length_cons, List.length_replicate]
      have h1 := log_len_add_one_le_of_two_pow_le_four_mul_sq K p hstop
      have h2 : Nat.log2 p ≤ Nat.log2 (leafPrecision (L + 1) p K) :=
        nat_log2_mono (le_leafPrecision (L + 1) p K)
      omega
    · simp only [quantizedBoxGaussianStepSpec, specSlots, List.length_cons]
      have h := ih (pChild p K) (K - K / 2) (2 * pChild p K) (ℓ + 1) (M * 2 ^ (K / 2))
        (by rw [pChild_eq_additive]; omega)
        (by
          have e : 2 ^ (L + 1 + 1) = 2 * 2 ^ (L + 1) := by ring
          omega)
      rw [hP']
      omega

#assert_std_axioms twist_slot_ok spread_slot_ok column_slot_ok leaf_slot_ok specSlots_base
  leaf_slots_ok chain_slots chain_lin chain_length

end WP.W10b
