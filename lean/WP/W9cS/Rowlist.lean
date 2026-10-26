import WP.W9cS.DriverSpec
import Contracts.W9.Pre

/-!
# WP.W9cS.Rowlist — the rows of a PRE node as driver input, and list facts
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 TMFw.W4 IntMul

/-- One spread row of the static-stride spread. -/
abbrev sRow (h : PreHdr) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ))) (j : ℕ) :
    Array (ℤ × ℤ) :=
  IntMulTM.Contracts.W8.spreadRowWithStride (fun _ _ => h.s) h.p_in h.pSub h.m1 h.r (ft.getD j [])
    (xRows.getD j #[])

/-- Driver rows: input row, spread row, filter-row symbols. -/
def rowsOf (h : PreHdr) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ))) :
    List (List (ℤ × ℤ) × List (ℤ × ℤ) × List Sym) :=
  (List.range h.t1).map fun j =>
    ((xRows.getD j #[]).toList, (sRow h ft xRows j).toList, filterRowSyms (ft.getD j []))

theorem size_sRow (h : PreHdr) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ))) (j : ℕ) :
    (sRow h ft xRows j).size = h.r := by
  simp [sRow, IntMulTM.Contracts.W8.spreadRowWithStride, IntMulTM.Contracts.W8.spreadRowFromPairs]

theorem range_map_getD {α : Type} (A : Array α) (d : α) :
    (List.range A.size).map (fun j => A.getD j d) = A.toList := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < A.size := by simpa using h1
    simp [Array.getD, hi]

theorem toList_w9UStatic (h : PreHdr) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ))) :
    (w9UStatic h.s h.p_in h.pSub h.m1 h.t1 h.r ft xRows).toList =
      (List.range h.t1).map (sRow h ft xRows) := by
  apply List.ext_getElem
  · simp [w9UStatic]
  · intro i h1 h2
    simp [w9UStatic, sRow]

theorem rowsOf_fst (h : PreHdr) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ)))
    (hs : xRows.size = h.t1) :
    (rowsOf h ft xRows).flatMap (·.1) = xRows.toList.flatMap Array.toList := by
  rw [← range_map_getD xRows #[], hs, rowsOf, List.flatMap_map, List.flatMap_map]

theorem rowsOf_snd (h : PreHdr) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ))) :
    (rowsOf h ft xRows).flatMap (·.2.1) =
      (w9UStatic h.s h.p_in h.pSub h.m1 h.t1 h.r ft xRows).toList.flatMap Array.toList := by
  rw [toList_w9UStatic, rowsOf, List.flatMap_map, List.flatMap_map]

theorem rowsOf_trd (h : PreHdr) (ft : Array (List ℤ)) (xRows : Array (Array (ℤ × ℤ))) :
    (rowsOf h ft xRows).flatMap (·.2.2) ++ [symSub] = filterRowsSyms h.t1 ft := by
  rw [rowsOf, List.flatMap_map, filterRowsSyms]

theorem length_flatMap_toList {α : Type} (r : ℕ) :
    ∀ (L : List (Array α)), (∀ a ∈ L, a.size = r) → (L.flatMap Array.toList).length = L.length * r
  | [], _ => by simp
  | a :: L, h => by
    have h1 := h a (by simp)
    have h2 := length_flatMap_toList r L (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons, List.length_append, Array.length_toList, List.length_cons, h1,
      h2]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem entryW_of_mem_flatMap {w : ℕ} {M : Array (Array (ℤ × ℤ))} (hM : MatW w M) :
    ∀ z ∈ M.toList.flatMap Array.toList, EntryW w z := by
  intro z hz
  obtain ⟨row, hrow, hz⟩ := List.mem_flatMap.1 hz
  exact hM row hrow z hz

#assert_std_axioms size_sRow range_map_getD toList_w9UStatic rowsOf_fst rowsOf_snd rowsOf_trd
  length_flatMap_toList entryW_of_mem_flatMap

end WP.W9c
