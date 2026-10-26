import WP.W9f.Spec
import WP.W7k2.Arith

/-!
# WP.W9f.Pure — array, list and width facts for the regime glue

* `runReverseSteps_toList`, `runBwdRevSteps_toList`: the snapshot's reversal passes as lists.
* sizes of `W8.solveFwdBarrett` / `solveNyqBarrett`; `solveBwdBarrett` as a reversed forward run.
* `blkE` / `entrySyms` facts used by the entry movers (`moveRec`, `unwind`).
* `postMu_cast`: the tape's reciprocal is `⌊2^H / d⌋` as an integer; `bitLen μ ≤ H + 1`.
-/

namespace WP.W9f

open IntMul TMFw TMFw.Contracts TMFw.Contracts.W9

section Arrays

variable {α : Type} [Zero α]

theorem array_ext_read1D (A B : Array α) (hs : A.size = B.size)
    (h : ∀ i < A.size, read1D A i = read1D B i) : A = B := by
  apply Array.ext hs
  intro i hi1 hi2
  have := h i hi1
  simp only [read1D, dif_pos hi1, dif_pos hi2] at this
  exact this

theorem read1D_of_lt (A : Array α) {i : ℕ} (hi : i < A.size) : read1D A i = A[i] := by
  simp [read1D, hi]

/-- The reversal pass is the reversed list. -/
theorem runReverseSteps_toList (Z : Array α) (t : ℕ) (hZ : Z.size = t) :
    (runReverseSteps t (read1D Z) t).outTape.toList = Z.toList.reverse := by
  have e : (runReverseSteps t (read1D Z) t).outTape = Z.reverse := by
    apply array_ext_read1D
    · simp [hZ]
    · intro i hi
      rw [size_runReverseSteps] at hi
      have h1 : t - 1 - i < Z.size := by omega
      have h2 : i < Z.reverse.size := by simp; omega
      rw [read1D_runReverseSteps_eq _ _ _ _ hi, read1D_of_lt Z h1, read1D_of_lt Z.reverse h2,
        Array.getElem_reverse]
      congr 1
      omega
  rw [e, Array.toList_reverse]

/-- The cyclic backward reversal pass: `[Y0, Y_{t-1}, …, Y1]`. -/
theorem runBwdRevSteps_toList (Y : Array α) (t : ℕ) (y0 : α) (ytl : List α)
    (hl : Y.toList = y0 :: ytl) (hY : Y.size = t) :
    (runBwdRevSteps t (read1D Y) t).outTape.toList = y0 :: ytl.reverse := by
  have hlen : ytl.length + 1 = t := by
    have := congrArg List.length hl
    simp only [Array.length_toList, List.length_cons] at this
    omega
  apply List.ext_getElem
  · simp only [Array.length_toList, size_runBwdRevSteps, List.length_cons, List.length_reverse]
    omega
  · intro i h1 h2
    have hi : i < t := by simpa [size_runBwdRevSteps] using h1
    rw [Array.getElem_toList, ← read1D_of_lt _ (by simpa [size_runBwdRevSteps] using h1),
      read1D_runBwdRevSteps_eq _ _ _ _ hi]
    rcases i with _ | j
    · rw [if_pos rfl, read1D_of_lt _ (by omega), ← Array.getElem_toList]
      simp [hl]
    · rw [if_neg (by omega), read1D_of_lt _ (by omega), ← Array.getElem_toList]
      have hj : j < ytl.length := by omega
      simp only [List.getElem_cons_succ, List.getElem_reverse]
      rw [List.getElem_of_eq hl]
      have e : t - (j + 1) = (ytl.length - 1 - j) + 1 := by omega
      simp only [e, List.getElem_cons_succ]

end Arrays

theorem size_solveFwdBarrett (q H t1 : ℕ) (μ a c : ℤ) (Y : Array (ℤ × ℤ)) :
    (IntMulTM.Contracts.W8.solveFwdBarrett q H t1 μ a c Y).size = t1 := by
  simp [IntMulTM.Contracts.W8.solveFwdBarrett]

theorem size_solveNyqBarrett (q H t1 m : ℕ) (μ a : ℤ) (Y : Array (ℤ × ℤ)) (alt : ℤ × ℤ) :
    (IntMulTM.Contracts.W8.solveNyqBarrett q H t1 m μ a Y alt).size = t1 := by
  simp [IntMulTM.Contracts.W8.solveNyqBarrett]

/-- The backward solver is the reversed forward run on the cyclically reversed input. -/
theorem solveBwdBarrett_toList (q H t1 : ℕ) (μ a c : ℤ) (Y : Array (ℤ × ℤ)) :
    (IntMulTM.Contracts.W8.solveBwdBarrett q H t1 μ a c Y).toList =
      (IntMulTM.Contracts.W8.solveFwdBarrett q H t1 μ c a
        (runBwdRevSteps t1 (read1D Y) t1).outTape).toList.reverse := by
  unfold IntMulTM.Contracts.W8.solveBwdBarrett
  exact runReverseSteps_toList _ t1 (size_solveFwdBarrett _ _ _ _ _ _ _)

/-! ## Entries and blocks -/

theorem blkE_cons (z : ℤ × ℤ) (xs : List (ℤ × ℤ)) : blkE (z :: xs) = entrySyms z ++ blkE xs := by
  simp [blkE, blk]

theorem blkE_nil : blkE [] = [] := by simp [blkE, blk]

/-- The payload of an entry (all data symbols), followed by its `sep`. -/
def entryData (z : ℤ × ℤ) : List Sym := intSyms z.1 ++ Sym.sep2 :: intSyms z.2

theorem entrySyms_eq (z : ℤ × ℤ) : entrySyms z = entryData z ++ [Sym.sep] := by
  simp [entrySyms, entryData]

theorem entryData_data (z : ℤ × ℤ) : ∀ x ∈ entryData z, isDataSym x = true := by
  intro x hx
  simp only [entryData, List.mem_append, List.mem_cons] at hx
  rcases hx with h | rfl | h
  · exact isData_intSyms _ x h
  · rfl
  · exact isData_intSyms _ x h

theorem entrySyms_noMark (z : ℤ × ℤ) : ∀ x ∈ entrySyms z, x ≠ Sym.mark := by
  intro x hx
  rw [entrySyms_eq] at hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with h | rfl
  · intro e
    subst e
    exact absurd (entryData_data z _ h) (by decide)
  · decide

theorem notEntry_nil : NotEntry [] := by
  intro s h
  cases h

theorem notEntry_mark (l : List Sym) : NotEntry (Sym.mark :: l) := by
  intro s h
  cases h
  exact ⟨by decide, by decide⟩

theorem arrW_toList {w : ℕ} {A B : Array (ℤ × ℤ)} (h : ∀ z ∈ B.toList, z ∈ A.toList)
    (hA : ArrW w A) : ArrW w B := fun z hz => hA z (h z hz)

/-! ## The tape reciprocal -/

theorem postMu_cast (H r u2 : ℕ) (a c : ℤ)
    (hd : 0 < IntMulTM.Contracts.W8.columnDivisor r u2 a c) :
    ((postMu H r u2 a c : ℕ) : ℤ) =
      ((2 ^ H : ℕ) : ℤ) / IntMulTM.Contracts.W8.columnDivisor r u2 a c := by
  unfold postMu
  exact Int.toNat_of_nonneg (Int.ediv_nonneg (by positivity) hd.le)

theorem bitLen_postMu (H r u2 : ℕ) (a c : ℤ)
    (hd : 0 < IntMulTM.Contracts.W8.columnDivisor r u2 a c) :
    bitLen (postMu H r u2 a c) ≤ H + 1 := by
  apply WP.W7k2.bitLen_le_of_lt
  have h1 := postMu_cast H r u2 a c hd
  have h2 : ((2 ^ H : ℕ) : ℤ) / IntMulTM.Contracts.W8.columnDivisor r u2 a c ≤
      ((2 ^ H : ℕ) : ℤ) := Int.ediv_le_self _ (by positivity)
  have h3 : ((postMu H r u2 a c : ℕ) : ℤ) ≤ ((2 ^ H : ℕ) : ℤ) := h1 ▸ h2
  have h4 : postMu H r u2 a c ≤ 2 ^ H := by exact_mod_cast h3
  have h5 : 0 < 2 ^ H := Nat.two_pow_pos H
  rw [pow_succ]
  omega

#assert_std_axioms array_ext_read1D read1D_of_lt runReverseSteps_toList runBwdRevSteps_toList
  size_solveFwdBarrett size_solveNyqBarrett solveBwdBarrett_toList blkE_cons blkE_nil
  entrySyms_eq entryData_data entrySyms_noMark notEntry_nil notEntry_mark arrW_toList
  postMu_cast bitLen_postMu

end WP.W9f
