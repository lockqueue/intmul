import WP.W9fC.State

/-!
# WP.W9fC.Data — the data of one `W9_columns` call and the column-loop invariant

Before column `u2` (`colV u2`): `W0` is empty, `M2` holds the input columns `u2, …, r-1`
(`colsFrom`), `A` holds the reversed outputs of columns `0, …, u2-1` above a guard (`outsUpTo`),
the table head is before record `u2` (`trAt`, `tlAt`), `C3 = u2` above a mark, `CT = t1` above a
guard; the other changed stacks have their initial values.
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp IntMul

attribute [local instance 10000] instZeroIntElementary

/-- The data of one `W9_columns` call. -/
structure Dat (m : ℕ) where
  σ : BLoc m → List Sym
  h : PostHdr
  c0T : Array (ℤ × ℤ)
  c1T : Array (ℤ × ℤ)
  alt : ℤ × ℤ
  Y : Array (Array (ℤ × ℤ))
  restT : List Sym
  rq : List Sym

namespace Dat

variable {m : ℕ} (D : Dat m)

/-- The machine's output matrix (W6b dispatch). -/
def Z : Array (Array (ℤ × ℤ)) := w9ZBarrett D.h.pSub D.h.t1 D.h.r D.c0T D.c1T D.alt D.Y

/-- The table record of column `u2`. -/
def recOf (u2 : ℕ) : List Sym := postRecOf D.h.pSub D.h.r u2 D.c0T D.c1T

/-- The table tape after the head has passed records `0, …, u2-1`. -/
def trAt (u2 : ℕ) : List Sym := ((List.range D.h.r).drop u2).flatMap D.recOf ++ symSub :: D.restT

/-- `TL` after the head has passed records `0, …, u2-1`. -/
def tlAt (u2 : ℕ) : List Sym := ((List.range u2).flatMap D.recOf).reverse ++ D.σ (.inl .TL)

/-- Input entries of columns `u2, …`. -/
def colsFrom (u2 : ℕ) : List (ℤ × ℤ) := (D.Y.toList.drop u2).flatMap Array.toList

/-- Output entries of columns `0, …, u2-1`. -/
def outsUpTo (u2 : ℕ) : List (ℤ × ℤ) := (D.Z.toList.take u2).flatMap Array.toList

/-- The invariant of the column loop before column `u2`. -/
def colV (hm : 7 ≤ m) (u2 : ℕ) : Vals where
  w0 := []
  tr := D.trAt u2
  tl := D.tlAt u2
  c3 := natSyms u2 ++ Sym.mark :: D.σ (.inl .C3)
  rq := D.σ (.inl .RQ)
  c0 := D.σ (.inl .C0)
  sm := D.σ (sM hm)
  sm2 := blkE (D.colsFrom u2) ++ D.σ (sM2 hm)
  st := D.σ (sT hm)
  sa := (blkE (D.outsUpTo u2)).reverse ++ symGuard :: D.σ (sA hm)
  sct := natSyms D.h.t1 ++ symGuard :: D.σ (sCT hm)
  scw := D.σ (sCW hm)

end Dat

theorem blkE_append (l1 l2 : List (ℤ × ℤ)) : blkE (l1 ++ l2) = blkE l1 ++ blkE l2 := by
  simp [blkE, blk]

variable {m : ℕ} (D : Dat m)

theorem Dat.trAt_succ {u2 : ℕ} (hu : u2 < D.h.r) : D.trAt u2 = D.recOf u2 ++ D.trAt (u2 + 1) := by
  unfold Dat.trAt
  rw [List.drop_eq_getElem_cons (by simpa using hu), List.flatMap_cons, List.getElem_range,
    List.append_assoc]

theorem Dat.tlAt_succ (u2 : ℕ) : (D.recOf u2).reverse ++ D.tlAt u2 = D.tlAt (u2 + 1) := by
  unfold Dat.tlAt
  rw [List.range_succ, List.flatMap_append, List.reverse_append]
  simp

theorem Dat.colsFrom_succ {u2 : ℕ} (hu : u2 < D.Y.size) :
    D.colsFrom u2 = (D.Y.getD u2 #[]).toList ++ D.colsFrom (u2 + 1) := by
  unfold Dat.colsFrom
  rw [List.drop_eq_getElem_cons (by simpa using hu), List.flatMap_cons]
  congr 2
  simp [Array.getD, hu]

theorem Dat.Z_size : D.Z.size = D.h.r := by
  simp [Dat.Z, w9ZBarrett]

theorem Dat.Z_getD {u2 : ℕ} (hu : u2 < D.h.r) :
    D.Z.getD u2 #[] = IntMulTM.Contracts.W8.columnSolveBarrett D.h.pSub D.h.H D.h.t1 D.h.mt1 D.h.r
      u2 (read1D D.c0T u2).1 (read1D D.c1T u2).1 (D.Y.getD u2 #[]) D.alt := by
  simp [Dat.Z, w9ZBarrett, Array.getD, hu, PostHdr.H, PostHdr.mt1]

theorem Dat.outsUpTo_succ {u2 : ℕ} (hu : u2 < D.h.r) :
    D.outsUpTo (u2 + 1) = D.outsUpTo u2 ++ (D.Z.getD u2 #[]).toList := by
  have hu' : u2 < D.Z.toList.length := by simpa [D.Z_size] using hu
  unfold Dat.outsUpTo
  rw [List.take_add_one, List.flatMap_append, List.getElem?_eq_getElem hu']
  simp [Array.getD, D.Z_size, hu]

theorem Dat.trAt_zero : D.trAt 0 = postBody D.h.pSub D.h.r D.c0T D.c1T ++ D.restT := by
  unfold Dat.trAt postBody
  rw [List.drop_zero, List.append_assoc]
  rfl

theorem Dat.trAt_r : D.trAt D.h.r = symSub :: D.restT := by
  unfold Dat.trAt
  rw [List.drop_of_length_le (by simp)]
  rfl

theorem Dat.tl_final :
    symSub :: D.tlAt D.h.r = (postBody D.h.pSub D.h.r D.c0T D.c1T).reverse ++ D.σ (.inl .TL) := by
  unfold Dat.tlAt postBody
  rw [List.reverse_append]
  rfl

theorem Dat.colsFrom_zero : blkE (D.colsFrom 0) = matSyms D.Y := by
  simp [Dat.colsFrom, matSyms]

theorem Dat.colsFrom_r (hY : D.Y.size = D.h.r) : D.colsFrom D.h.r = [] := by
  unfold Dat.colsFrom
  rw [List.drop_of_length_le (by simp [hY])]
  rfl

theorem Dat.outsUpTo_zero : D.outsUpTo 0 = [] := by
  simp [Dat.outsUpTo]

theorem Dat.outsUpTo_r : blkE (D.outsUpTo D.h.r) = matSyms D.Z := by
  have hlen : D.Z.toList.length = D.h.r := by simp [D.Z_size]
  unfold Dat.outsUpTo
  rw [List.take_of_length_le (le_of_eq hlen)]
  rfl

theorem Dat.recOf_eq (u2 : ℕ) :
    D.recOf u2 = postRecSyms (read1D D.c0T u2).1 (read1D D.c1T u2).1
      (postMu D.h.H D.h.r u2 (read1D D.c0T u2).1 (read1D D.c1T u2).1) := rfl

#assert_std_axioms blkE_append Dat.trAt_succ Dat.tlAt_succ Dat.colsFrom_succ Dat.Z_size Dat.Z_getD
  Dat.outsUpTo_succ Dat.trAt_zero Dat.trAt_r Dat.tl_final Dat.colsFrom_zero Dat.colsFrom_r
  Dat.outsUpTo_zero Dat.outsUpTo_r Dat.recOf_eq

end WP.W9fC
