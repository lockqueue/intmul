import WP.W11b.Defs
import Contracts.W7.Shapes
import LevelSync.Sizes

/-!
# WP.W11b.Leaf — the leaf clause of `ChainOK`

`leafChainOK`: at a `.basePow2 p K tw` leaf with faithful twiddles (`htw`, the T1 clause of
`TablesFaithful`), W7's twiddle widths (`hew`) and a level width `wd ℓ ≥ reqW = max (p + p_in + 3)
(4·q_leaf)`, every node input satisfying `NodeInv` meets `LeafOK`, so `ChainOK` holds.

* input: `entryW_of_norm_le` (width `p + p_in + 3`);
* every core stage (`leafCoreW`): induction on `s ≤ K` over the even/odd sub-arrays, with the
  invariant `∀ k, ‖toScaledComplex p_in (read1D y k)‖ ≤ 2^p` (out-of-range reads are `0`); each stage
  output by CSWS:1400 `programCost_leaf_baseRadix2FFT_widths_sound_of_faithful` applied to the stage
  array itself (`FitsSignedWord (4q)` gives width `4q - 1`);
* output: the same lemma's second conjunct;
* twiddles: `hew` gives width `q_leaf + 3 ≤ 4·q_leaf`.
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

/-- Out-of-range reads dequantize to `0`. -/
theorem toScaledComplex_read1D_of_not_lt {q : ℕ} {y : Array (ℤ × ℤ)} {k : ℕ}
    (hk : ¬ k < y.size) : toScaledComplex q (read1D y k) = 0 := by
  have h : read1D y k = ((0 : ℤ), (0 : ℤ)) := by
    unfold read1D
    rw [dif_neg hk]
    rfl
  rw [h]
  exact toScaledComplex_zero q

/-- An in-range norm bound extends to all reads. -/
theorem norm_read1D_le_of_lt {q M : ℕ} {y : Array (ℤ × ℤ)}
    (h : ∀ k < y.size, ‖toScaledComplex q (read1D y k)‖ ≤ (2 : ℝ) ^ M) (k : ℕ) :
    ‖toScaledComplex q (read1D y k)‖ ≤ (2 : ℝ) ^ M := by
  by_cases hk : k < y.size
  · exact h k hk
  · rw [toScaledComplex_read1D_of_not_lt hk, norm_zero]
    positivity

/-- Reads of an `Array.ofFn` sub-array inherit an entrywise norm bound. -/
theorem norm_read1D_ofFn_le {q M n : ℕ} {f : Fin n → ℤ × ℤ}
    (hf : ∀ j : Fin n, ‖toScaledComplex q (f j)‖ ≤ (2 : ℝ) ^ M) (k : ℕ) :
    ‖toScaledComplex q (read1D (Array.ofFn f) k)‖ ≤ (2 : ℝ) ^ M := by
  refine norm_read1D_le_of_lt (fun i hi => ?_) k
  have hi' : i < n := by simpa using hi
  have e : read1D (Array.ofFn f) i = f ⟨i, hi'⟩ := by simp [read1D, hi']
  rw [e]
  exact hf _

/-- Every leaf core stage `s` has `2^s` entries. -/
theorem size_leafCore (p_in q : ℕ) (tw : Array (Array (ℤ × ℤ))) :
    ∀ (s : ℕ) (y : Array (ℤ × ℤ)),
      (computableBaseRadix2FFTCoreWithProgramCost p_in q tw s y).1.size = 2 ^ s
  | 0, _ => by simp [computableBaseRadix2FFTCoreWithProgramCost]
  | _ + 1, _ => by simp [computableBaseRadix2FFTCoreWithProgramCost]

/-- An array whose reads all dequantize to `≤ 2^p` has width `p + p_in + 3`. -/
theorem arrW_of_norm {w p_in p : ℕ} (hw : p + p_in + 3 ≤ w) {y : Array (ℤ × ℤ)}
    (hy : ∀ k, ‖toScaledComplex p_in (read1D y k)‖ ≤ (2 : ℝ) ^ p) : ArrW w y :=
  arrW_of_read1D fun k _ => entryW_mono (entryW_of_norm_le (hy k)) hw

/-- Width of the core stage `s ≤ K` on any array whose reads dequantize to `≤ 2^p`
(CSWS:1400 applied to the stage array itself). -/
theorem arrW_leafCore_of_norm {w p_in p K : ℕ} {tw : Array (Array (ℤ × ℤ))} (hp : 8 ≤ p)
    (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
      ‖toScaledComplex (2 * p + K + 8) (read1D (tw.getD s #[]) u) -
          stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))‖ ≤ 2 * complexQuantizeMaxErr (2 * p + K + 8))
    (hw : 4 * (2 * p + K + 8) ≤ w) {y : Array (ℤ × ℤ)}
    (hy : ∀ k, ‖toScaledComplex p_in (read1D y k)‖ ≤ (2 : ℝ) ^ p) {s : ℕ} (hs : s ≤ K) :
    ArrW w (computableBaseRadix2FFTCoreWithProgramCost p_in (2 * p + K + 8) tw s y).1 := by
  refine arrW_of_read1D fun u hu => ?_
  rw [size_leafCore] at hu
  have h := programCost_leaf_baseRadix2FFT_widths_sound_of_faithful p_in p K hp tw htw y
    (fun k => toScaledComplex p_in (read1D y k)) (fun _ _ => rfl) (fun k _ => hy k) s u hs hu
  have h1 : FitsSignedWord (4 * (2 * p + K + 8))
      (read1D (computableBaseRadix2FFTCoreWithProgramCost p_in (2 * p + K + 8) tw s y).1 u) := h.1
  exact entryW_of_fitsSignedWord h1 (by omega)

/-- Width of the leaf output (CSWS:1400, second conjunct). -/
theorem arrW_leafOut_of_norm {w p_in p K : ℕ} {tw : Array (Array (ℤ × ℤ))} (hp : 8 ≤ p)
    (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
      ‖toScaledComplex (2 * p + K + 8) (read1D (tw.getD s #[]) u) -
          stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))‖ ≤ 2 * complexQuantizeMaxErr (2 * p + K + 8))
    (hw : 4 * (2 * p + K + 8) ≤ w) {y : Array (ℤ × ℤ)}
    (hy : ∀ k, ‖toScaledComplex p_in (read1D y k)‖ ≤ (2 : ℝ) ^ p) :
    ArrW w (computableBaseRadix2FFTWithProgramCost p_in p K tw y).1 := by
  refine arrW_of_read1D fun u hu => ?_
  rw [leaf_output_size] at hu
  have h := programCost_leaf_baseRadix2FFT_widths_sound_of_faithful p_in p K hp tw htw y
    (fun k => toScaledComplex p_in (read1D y k)) (fun _ _ => rfl) (fun k _ => hy k) K u le_rfl hu
  have h2 : FitsSignedWord (4 * (2 * p + K + 8))
      (read1D (computableBaseRadix2FFTWithProgramCost p_in p K tw y).1 u) := h.2
  exact entryW_of_fitsSignedWord h2 (by omega)

/-- `leafCoreW` at every stage `s ≤ K`, by induction over the even/odd sub-arrays. -/
theorem leafCoreW_of_norm {w p_in p K : ℕ} {tw : Array (Array (ℤ × ℤ))} (hp : 8 ≤ p)
    (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
      ‖toScaledComplex (2 * p + K + 8) (read1D (tw.getD s #[]) u) -
          stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))‖ ≤ 2 * complexQuantizeMaxErr (2 * p + K + 8))
    (hw1 : p + p_in + 3 ≤ w) (hw2 : 4 * (2 * p + K + 8) ≤ w) :
    ∀ s ≤ K, ∀ y : Array (ℤ × ℤ), (∀ k, ‖toScaledComplex p_in (read1D y k)‖ ≤ (2 : ℝ) ^ p) →
      leafCoreW w p_in (2 * p + K + 8) tw s y := by
  intro s
  induction s with
  | zero =>
    intro hs y hy
    simp only [leafCoreW]
    exact ⟨arrW_of_norm hw1 hy, arrW_leafCore_of_norm hp htw hw2 hy hs⟩
  | succ s ih =>
    intro hs y hy
    simp only [leafCoreW]
    exact ⟨ih (by omega) (Array.ofFn fun j : Fin (2 ^ s) => read1D y (2 * j.val))
        (norm_read1D_ofFn_le fun _ => hy _),
      ih (by omega) (Array.ofFn fun j : Fin (2 ^ s) => read1D y (2 * j.val + 1))
        (norm_read1D_ofFn_le fun _ => hy _),
      arrW_leafCore_of_norm hp htw hw2 hy hs⟩

/-- Leaf twiddle widths from W7's record widths (`q_leaf + 3`). -/
theorem leafTwW_of_entryWidths {w p K : ℕ} {tw : Array (Array (ℤ × ℤ))}
    (hew : W7.EntryWidths W7.snapshotFormat (.basePow2 p K tw)) (hw : 2 * p + K + 8 + 3 ≤ w) :
    LeafTwW w K tw := by
  intro s hs u hu
  have h : bitLen (read1D (tw.getD s #[]) u).1.natAbs ≤ 2 * p + K + 8 + 3 ∧
      bitLen (read1D (tw.getD s #[]) u).2.natAbs ≤ 2 * p + K + 8 + 3 := hew s hs u hu
  exact ⟨h.1.trans hw, h.2.trans hw⟩

/-- **(B) The leaf clause of `ChainOK`** (`LeafStmt` for `WP.W11b.Chain`). -/
theorem leafChainOK (wd : ℕ → ℕ) (ℓ p K p_in : ℕ) (tw : Array (Array (ℤ × ℤ))) (hp : 8 ≤ p)
    (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
      ‖toScaledComplex (2 * p + K + 8) (read1D (tw.getD s #[]) u) -
          stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))‖ ≤ 2 * complexQuantizeMaxErr (2 * p + K + 8))
    (hew : W7.EntryWidths W7.snapshotFormat (.basePow2 p K tw))
    (hw : reqW (.basePow2 p K tw) p_in ≤ wd ℓ)
    (xs : List (Array (ℤ × ℤ))) (hxs : ∀ x ∈ xs, NodeInv (.base p (2 ^ K)) p_in x) :
    ChainOK wd (.basePow2 p K tw) p_in ℓ xs := by
  have hw' : max (p + p_in + 3) (4 * (2 * p + K + 8)) ≤ wd ℓ := hw
  have hw1 : p + p_in + 3 ≤ wd ℓ := le_trans (le_max_left _ _) hw'
  have hw2 : 4 * (2 * p + K + 8) ≤ wd ℓ := le_trans (le_max_right _ _) hw'
  show LeafTwW (wd ℓ) K tw ∧ ∀ x ∈ xs, x.size = 2 ^ K ∧ LeafOK (wd ℓ) p_in p K tw x
  refine ⟨leafTwW_of_entryWidths hew (by omega), fun x hx => ?_⟩
  obtain ⟨hsize, hnorm⟩ := hxs x hx
  have hsize' : x.size = 2 ^ K := hsize
  have hnorm' : ∀ k, ‖toScaledComplex p_in (read1D x k)‖ ≤ (2 : ℝ) ^ p :=
    norm_read1D_le_of_lt fun k hk => hnorm k (lt_of_lt_of_eq hk hsize')
  exact ⟨hsize', arrW_of_norm hw1 hnorm', leafCoreW_of_norm hp htw hw1 hw2 K le_rfl x hnorm',
    arrW_leafOut_of_norm hp htw hw2 hnorm'⟩

#assert_std_axioms toScaledComplex_read1D_of_not_lt norm_read1D_le_of_lt norm_read1D_ofFn_le
  size_leafCore arrW_of_norm arrW_leafCore_of_norm arrW_leafOut_of_norm leafCoreW_of_norm
  leafTwW_of_entryWidths leafChainOK

end WP.W11b
