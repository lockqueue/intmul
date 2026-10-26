import WP.W9fC.Facts

/-!
# WP.W9fC.Sizes: size and width facts for the column driver's cost bound

* `length_flatMap_rows`: a list of rows of size `n` flattens to `length * n` entries.
* `matW_of_getD`: `MatW` from the `getD` form.
* `length_matSyms_le`: symbol length of a matrix block from row count, row size and width.
* `Dat.lenY_le` / `Dat.lenZ_le`: the input `Y` and the output `Z` of one `W9_columns` call have at
  most `t1 · r · eb H` symbols.
* `colB_facts`: elementary bounds on `columnBound` under `PostDims`.
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp Computability IntMul

attribute [local instance 10000] instZeroIntElementary

variable {m : ℕ}

theorem length_flatMap_rows {α : Type} (l : List (Array α)) (n : ℕ)
    (h : ∀ row ∈ l, row.size = n) : (l.flatMap Array.toList).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a.size = n := h a (List.mem_cons_self ..)
    have ih' := ih (fun row hr => h row (List.mem_cons_of_mem _ hr))
    simp only [List.flatMap_cons, List.length_append, Array.length_toList, List.length_cons, ha,
      ih', Nat.add_mul, Nat.one_mul]
    omega

theorem matW_of_getD {M : Array (Array (ℤ × ℤ))} {w : ℕ}
    (h : ∀ i < M.size, ArrW w (M.getD i #[])) : MatW w M := by
  show ∀ row ∈ M.toList, ArrW w row
  intro row hrow
  rw [Array.mem_toList_iff] at hrow
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hrow
  have e : M.getD i #[] = M[i] := by simp [Array.getD, hi]
  have hw := h i hi
  rw [e] at hw
  exact hw

theorem length_matSyms_le {M : Array (Array (ℤ × ℤ))} {w n : ℕ} (hM : MatW w M)
    (hrows : ∀ row ∈ M.toList, row.size = n) : (matSyms M).length ≤ M.size * n * eb w := by
  have hz : ∀ z ∈ M.toList.flatMap Array.toList, EntryW w z := by
    intro z hz
    obtain ⟨row, hrow, hz'⟩ := List.mem_flatMap.mp hz
    exact hM row hrow z hz'
  have hl := length_blkE_le w _ hz
  rw [length_flatMap_rows M.toList n hrows, Array.length_toList] at hl
  exact hl

theorem Dat.lenY_le (D : Dat m) (hY : D.Y.size = D.h.r)
    (hcols : ∀ col ∈ D.Y.toList, col.size = D.h.t1)
    (hok : ∀ u2 < D.h.r, ColumnOK D.h.pSub D.h.t1 D.h.r u2 (read1D D.c0T u2) (read1D D.c1T u2)
      (D.Y.getD u2 #[]) D.alt) :
    (matSyms D.Y).length ≤ D.h.t1 * D.h.r * eb D.h.H := by
  have hW : MatW D.h.H D.Y :=
    matW_of_getD fun i hi => (hok i (lt_of_lt_of_eq hi hY)).2.2.2.2.2.2.2.1
  have hl := length_matSyms_le hW hcols
  rw [hY, Nat.mul_comm D.h.r D.h.t1] at hl
  exact hl

theorem Dat.lenZ_le (D : Dat m) (hZ : MatW D.h.H D.Z)
    (hZs : ∀ u2 < D.h.r, (D.Z.getD u2 #[]).size = D.h.t1) :
    (matSyms D.Z).length ≤ D.h.t1 * D.h.r * eb D.h.H := by
  have hrows : ∀ row ∈ D.Z.toList, row.size = D.h.t1 :=
    rows_of_getD fun i hi => hZs i (lt_of_lt_of_eq hi D.Z_size)
  have hl := length_matSyms_le hZ hrows
  rw [D.Z_size, Nat.mul_comm D.h.r D.h.t1] at hl
  exact hl

theorem colB_facts (Mul : ℕ → ℕ) (h : PostHdr) (hD : PostDims h) :
    1 ≤ h.r ∧ 1 ≤ columnBound Mul h ∧ h.hdrLen ≤ columnBound Mul h ∧
      h.t1 * bitLen h.t1 ≤ columnBound Mul h ∧ 4 ≤ eb h.H := by
  obtain ⟨ht1, hr, -, -⟩ := hD
  have hbl : bitLen h.t1 = h.mt1 + 1 := by
    rw [ht1]
    exact bl_two_pow h.mt1
  have hr1 : 1 ≤ h.r := by
    have hp : 0 < 2 ^ h.mr := pow_pos (by norm_num) _
    omega
  have hmul : h.t1 * (h.mt1 + 1) ≤
      h.t1 * (8 * Mul (8 * (h.H + 1)) + 4 * eb h.H + h.mt1 + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hsq : 0 < (h.H + 1) ^ 2 := by positivity
  refine ⟨hr1, ?_, ?_, ?_, ?_⟩
  · unfold columnBound
    omega
  · unfold columnBound
    omega
  · rw [hbl]
    unfold columnBound
    omega
  · unfold eb
    omega

#assert_std_axioms length_flatMap_rows matW_of_getD length_matSyms_le Dat.lenY_le Dat.lenZ_le
  colB_facts

end WP.W9fC
