import Contracts.W9.Pipeline
import IntMul.MaterializedAndComputable.CallSiteWidthSoundness
import IntMulTM.SpecFacts

/-!
# WP.W11b.Basic — generic width and array facts used by the `ChainOK` proof

* bit lengths: `bitLen n ≤ k ↔ n < 2^k`, and the passage from the snapshot's
  `FitsSignedWord` / norm bounds to W9's `EntryW`;
* building `ArrW` / `MatW` from `read1D` / `read2D` facts on arrays of known shape
  (`runScan2DWithSteps`, `Array.ofFn`, `runSequentialScanSteps`);
* `groupAt` of a node-major `flatMap` (the POST groups of `ChainOK`);
* sizes of the snapshot's transposes.
-/

namespace WP.W11b

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

/-! ## Bit lengths -/

theorem bitLen_le_iff (n k : ℕ) : bitLen n ≤ k ↔ n < 2 ^ k := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le

theorem bitLen_zero : bitLen 0 = 0 := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat, Nat.size_zero]

theorem bitLen_natAbs_le_of_abs_lt {z : ℤ} {k : ℕ} (h : |z| < (2 : ℤ) ^ k) :
    bitLen z.natAbs ≤ k := by
  rw [bitLen_le_iff]
  have h1 : ((z.natAbs : ℕ) : ℤ) < ((2 ^ k : ℕ) : ℤ) := by
    rw [← Int.abs_eq_natAbs]
    exact_mod_cast h
  exact_mod_cast h1

theorem bitLen_natAbs_le_of_abs_le {z : ℤ} {k : ℕ} (h : |z| ≤ (2 : ℤ) ^ k) :
    bitLen z.natAbs ≤ k + 1 := by
  refine bitLen_natAbs_le_of_abs_lt (lt_of_le_of_lt h ?_)
  exact pow_lt_pow_right₀ (by norm_num) (by omega)

/-! ## Entry widths -/

theorem entryW_mono {w w' : ℕ} {z : ℤ × ℤ} (h : EntryW w z) (hw : w ≤ w') : EntryW w' z :=
  ⟨h.1.trans hw, h.2.trans hw⟩

theorem entryW_zero (w : ℕ) : EntryW w (0 : ℤ × ℤ) := by
  refine ⟨?_, ?_⟩ <;> simp [bitLen_zero]

theorem entryW_zero' (w : ℕ) : EntryW w ((0 : ℤ), (0 : ℤ)) := entryW_zero w

/-- A signed `w`-bit word has width at most `w - 1`. -/
theorem entryW_of_fitsSignedWord {w w' : ℕ} {z : ℤ × ℤ} (h : FitsSignedWord w z)
    (hw : w - 1 ≤ w') : EntryW w' z := by
  obtain ⟨h1, h2⟩ := h
  have hp : (2 : ℤ) ^ (w - 1) ≤ (2 : ℤ) ^ w' := pow_le_pow_right₀ (by norm_num) hw
  exact ⟨bitLen_natAbs_le_of_abs_lt (lt_of_lt_of_le h1 hp),
    bitLen_natAbs_le_of_abs_lt (lt_of_lt_of_le h2 hp)⟩

/-- A dequantized norm bound `‖z / 2^(q+2)‖ ≤ 2^M` gives width `M + q + 3`. -/
theorem entryW_of_norm_le {q M : ℕ} {z : ℤ × ℤ} (h : ‖toScaledComplex q z‖ ≤ (2 : ℝ) ^ M) :
    EntryW (M + q + 3) z :=
  entryW_of_fitsSignedWord (fitsSignedWord_of_norm_toScaledComplex_le q M (M + q + 4) z h (by omega))
    (by omega)

/-- Norm bound `≤ 2` (twiddles and similar unit-size tables). -/
theorem entryW_of_norm_le_two {q : ℕ} {z : ℤ × ℤ} (h : ‖toScaledComplex q z‖ ≤ 2) :
    EntryW (q + 4) z := by
  have h' : ‖toScaledComplex q z‖ ≤ (2 : ℝ) ^ 1 := by simpa using h
  have := entryW_of_norm_le h'
  exact entryW_mono this (by omega)

/-! ## Arrays and matrices -/

theorem exists_read1D_of_mem {x : Array (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ x.toList) :
    ∃ k < x.size, read1D x k = z := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz
  have hk' : k < x.size := by simpa using hk
  refine ⟨k, hk', ?_⟩
  simp [read1D, hk']

theorem arrW_of_read1D {w : ℕ} {x : Array (ℤ × ℤ)} (h : ∀ k < x.size, EntryW w (read1D x k)) :
    ArrW w x := by
  intro z hz
  obtain ⟨k, hk, rfl⟩ := exists_read1D_of_mem hz
  exact h k hk

theorem arrW_mono {w w' : ℕ} {x : Array (ℤ × ℤ)} (h : ArrW w x) (hw : w ≤ w') : ArrW w' x :=
  fun z hz => entryW_mono (h z hz) hw

theorem entryW_read1D_of_arrW {w : ℕ} {x : Array (ℤ × ℤ)} (h : ArrW w x) (k : ℕ) :
    EntryW w (read1D x k) := by
  unfold read1D
  split_ifs with hk
  · exact h _ (by simp)
  · exact entryW_zero w

theorem matW_of_read2D {w : ℕ} {M : Array (Array (ℤ × ℤ))}
    (h : ∀ i < M.size, ∀ j < (M.getD i #[]).size, EntryW w (read2D M i j)) : MatW w M := by
  intro row hrow
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
  have hi' : i < M.size := by simpa using hi
  have hrow_eq : M.toList[i] = M.getD i #[] := by simp [Array.getD, hi']
  rw [hrow_eq]
  apply arrW_of_read1D
  intro k hk
  rw [read1D_array_getD_eq_read2D]
  exact h i hi' k hk

theorem matW_mono {w w' : ℕ} {M : Array (Array (ℤ × ℤ))} (h : MatW w M) (hw : w ≤ w') :
    MatW w' M :=
  fun row hrow => arrW_mono (h row hrow) hw

theorem arrW_getD_of_matW {w : ℕ} {M : Array (Array (ℤ × ℤ))} (h : MatW w M) (i : ℕ) :
    ArrW w (M.getD i #[]) := by
  by_cases hi : i < M.size
  · have : M.getD i #[] = M[i] := by simp [Array.getD, hi]
    rw [this]
    exact h _ (by simp)
  · have : M.getD i #[] = #[] := by simp [Array.getD, hi]
    rw [this]
    intro z hz
    simp at hz

theorem entryW_read2D_of_matW {w : ℕ} {M : Array (Array (ℤ × ℤ))} (h : MatW w M) (i j : ℕ) :
    EntryW w (read2D M i j) := by
  rw [← read1D_array_getD_eq_read2D]
  exact entryW_read1D_of_arrW (arrW_getD_of_matW h i) j

theorem matW_runScan2D {w n1 n2 : ℕ} {f : ℕ → ℕ → ℤ × ℤ}
    (h : ∀ i < n1, ∀ j < n2, EntryW w (f i j)) : MatW w (runScan2DWithSteps n1 n2 f).1 := by
  refine matW_of_read2D fun i hi j hj => ?_
  have hi' : i < n1 := by rwa [runScan2DWithSteps_fst_size] at hi
  have hj' : j < n2 := by rwa [runScan2DWithSteps_row_size _ _ _ i hi'] at hj
  rw [read2D_runScan2DWithSteps_of_lt n1 n2 f hi' hj']
  exact h i hi' j hj'

theorem matW_ofFn {w n : ℕ} {g : Fin n → Array (ℤ × ℤ)} (h : ∀ i : Fin n, ArrW w (g i)) :
    MatW w (Array.ofFn g) := by
  intro row hrow
  simp only [Array.toList_ofFn, List.mem_ofFn] at hrow
  obtain ⟨i, rfl⟩ := hrow
  exact h i

theorem arrW_runSequentialScan {w n : ℕ} {f : ℕ → ℤ × ℤ} (h : ∀ i < n, EntryW w (f i)) :
    ArrW w (runSequentialScanSteps f n).outTape := by
  refine arrW_of_read1D fun k hk => ?_
  rw [size_runSequentialScanSteps] at hk
  rw [read1D_runSequentialScanSteps_eq f n k hk]
  exact h k hk

/-- Every row of a `runScan2DWithSteps` matrix has the declared length. -/
theorem runScan2D_mem_size {α : Type} {n1 n2 : ℕ} {f : ℕ → ℕ → α} {row : Array α}
    (hrow : row ∈ (runScan2DWithSteps n1 n2 f).1.toList) : row.size = n2 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
  have hi' : i < n1 := by simpa [runScan2DWithSteps_fst_size] using hi
  have h := runScan2DWithSteps_row_size n1 n2 f i hi'
  have heq : (runScan2DWithSteps n1 n2 f).1.toList[i] = (runScan2DWithSteps n1 n2 f).1.getD i #[] := by
    have hi'' : i < (runScan2DWithSteps n1 n2 f).1.size := by
      rw [runScan2DWithSteps_fst_size]; exact hi'
    simp [Array.getD, hi'']
  rw [heq]
  exact h

/-! ## Groups of a node-major concatenation -/

theorem groupAt_flatMap {β : Type} (g : ℕ) (G : β → List (Array (ℤ × ℤ)))
    (hG : ∀ b, (G b).length = g) :
    ∀ (xs : List β) (i : ℕ) (hi : i < xs.length), groupAt g (xs.flatMap G) i = G xs[i]
  | [], i, hi => absurd hi (by simp)
  | x :: xs, 0, _ => by
    simp only [groupAt, List.flatMap_cons, Nat.zero_mul, List.drop_zero, List.getElem_cons_zero]
    rw [List.take_left' (hG x)]
  | x :: xs, i + 1, hi => by
    have hi' : i < xs.length := by simpa using hi
    have ih := groupAt_flatMap g G hG xs i hi'
    simp only [groupAt] at ih ⊢
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    have hsplit : (i + 1) * g = (G x).length + i * g := by rw [hG x]; ring
    rw [hsplit, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      Nat.add_sub_cancel_left]
    exact ih

/-! ## Sizes -/

theorem size_runMultiTapeTranspose {α : Type} [Zero α] (m r : ℕ) (tape : ℕ → α) :
    (runMultiTapeTranspose m r tape).size = 2 ^ m * r := by
  induction m generalizing tape with
  | zero => simp [runMultiTapeTranspose]
  | succ m ih =>
    simp only [runMultiTapeTranspose, size_runInterleaveRunsSteps]
    ring

#assert_std_axioms bitLen_le_iff bitLen_zero bitLen_natAbs_le_of_abs_lt bitLen_natAbs_le_of_abs_le
  entryW_mono entryW_zero entryW_zero' entryW_of_fitsSignedWord entryW_of_norm_le
  entryW_of_norm_le_two exists_read1D_of_mem arrW_of_read1D arrW_mono entryW_read1D_of_arrW
  matW_of_read2D matW_mono arrW_getD_of_matW entryW_read2D_of_matW matW_runScan2D matW_ofFn
  arrW_runSequentialScan runScan2D_mem_size groupAt_flatMap size_runMultiTapeTranspose

end WP.W11b
