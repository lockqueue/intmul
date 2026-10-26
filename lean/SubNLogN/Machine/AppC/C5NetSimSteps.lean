/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5NetSimLayout

/-!
# Proposition A.7 network simulation, part 4: the step shapes of a node (`AppC/C5NetSimSteps.lean`)

At level `k = k' + 1` (`e = m^(k'+1)` digits per chunk, coordinates of `b = m^k'` digits, `m = mH`),
on `nodeLayout q e N0 R N1 G B`, the index maps (`PullMatch`) of the pure-network elementary node steps
(`AppCProc.lean`) are the machine-level `streamMap`s:
* `lowerSteps` unit / shift on chunk `X`, coordinate `i` ↔ `unit X i (E i i)` / `lowShift X i (E i ·)`
  (`pm_lowUnit`, `pm_lowShift`);
* the pivot shift and the shift of `hMinusDSteps` ↔ `hdShift i j false` (`pm_hdPlus`);
* the pivot negation and the unit of `hMinusDSteps` ↔ `unit D j (-1)` (`pm_negD`);
* the shift of `subHSteps` ↔ `hdShift i i true` (`pm_hdMinus`);
and the child interchange `swapBlocks (3 + i b) (4 + e + j b) b` has index map
`swapFieldsInv (q^b) (cG …) (q^b) (cB …)` (`pm_swap`). Row-locality and in-row bounds of these
index maps (`streamMap_rowPerm`, `swap_rowPerm`). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.NetAux

open SubNLogN.Math.Networks
open SubNLogN.Math.Networks.Model (Layout Elem)
open SubNLogN.Math.Networks.Model.LayoutEncodingAux (blockRange_split)

theorem coordOf_lt (m Q cv i : ℕ) (hQ : 0 < Q) : coordOf m Q cv i < Q := Nat.mod_lt _ hQ

theorem ratModC5_neg_one (Q : ℕ) (hQ : 0 < Q) : ratModC5 Q (-1)⁻¹ = Q - 1 := by
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  have h1 : ((-1 : ℚ)⁻¹) = -1 := by norm_num
  have h2 : (-1 : ℚ).num = -1 := rfl
  have h3 : (-1 : ℚ).den = 1 := rfl
  unfold ratModC5
  rw [h1, h2, h3, Int.cast_neg, Int.cast_one, Nat.cast_one, ZMod.inv_one, mul_one,
    Nat.add_sub_cancel]
  exact ZMod.val_neg_one Q'

theorem ratModNat_eq_C5 (R : ℕ) (r : ℚ) : ratModNat R r = ratModC5 R r := rfl

theorem shift_neg_eq (d h Q : ℕ) (hh : h < Q) : (d + Q - (Q - h) % Q) % Q = (d + h) % Q := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · rw [Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.add_zero, Nat.add_mod_right]
  · rw [Nat.mod_eq_of_lt (by omega : Q - h < Q)]
    congr 1
    omega

/-- A row-local index map (rows of `S` records) mapping each row into itself. -/
structure RowPerm (S : ℕ) (f : ℕ → ℕ) : Prop where
  local_eq : ∀ t l, l < S → f (t * S + l) = t * S + f l
  lt : ∀ l < S, f l < S

section Level

variable (q k' N0 R N1 G B : ℕ)

theorem he_level : mH ^ (k' + 1) = mH * mH ^ k' := pow_succ' mH k'

/-- The machine-level stream maps are row-permutations of the rows of `rowSize`. -/
theorem streamMap_rowPerm (hq : 1 ≤ q) (op : StreamOp mH) :
    RowPerm (rowSize q mH (k' + 1) N1 G B) (streamMap q mH op (k' + 1) N1 G B) :=
  ⟨fun t l _ => streamMap_rowLocal q mH op (k' + 1) N1 G B t l,
    fun l hl => streamMap_lt q mH op (k' + 1) N1 G B _ hq (by omega) dvd_rfl l hl⟩

theorem pm_lowUnit (hq : 0 < q) (X : Chunk) (E : Matrix (Fin mH) (Fin mH) ℚ) (i : Fin mH) :
    PullMatch (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)
      (Elem.unit (blk (cstart (mH ^ (k' + 1)) X) (mH ^ k') i).1
        (blk (cstart (mH ^ (k' + 1)) X) (mH ^ k') i).2
        (ratModNat (q ^ mH ^ k') (E i i)) (ratModNat (q ^ mH ^ k') (E i i)⁻¹)).pull
      (streamMap q mH (.unit X i (E i i)) (k' + 1) N1 G B) := by
  intro y hy
  refine (pm_unit_coord q (mH ^ (k' + 1)) N0 R N1 G B mH (mH ^ k') (he_level k') hq X i i.isLt
    (ratModNat (q ^ mH ^ k') (E i i)) (ratModNat (q ^ mH ^ k') (E i i)⁻¹) y hy).trans ?_
  simp only [streamMap, Nat.add_sub_cancel, ratModNat_eq_C5]

theorem pm_lowShift (hq : 0 < q) (X : Chunk) (E : Matrix (Fin mH) (Fin mH) ℚ) (i : Fin mH) :
    PullMatch (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)
      (Elem.shift (blk (cstart (mH ^ (k' + 1)) X) (mH ^ k') i).1
        (blk (cstart (mH ^ (k' + 1)) X) (mH ^ k') i).2 (fun x =>
          ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i),
            ratModNat (q ^ mH ^ k') (E i j) * (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).blockVal
              (blk (cstart (mH ^ (k' + 1)) X) (mH ^ k') j).1
              (blk (cstart (mH ^ (k' + 1)) X) (mH ^ k') j).2 x)).pull
      (streamMap q mH (.lowShift X i (fun j => E i j)) (k' + 1) N1 G B) := by
  refine (pm_shift_coord q (mH ^ (k' + 1)) N0 R N1 G B mH (mH ^ k') (he_level k') hq X i i.isLt _
    (fun y => (∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i),
      ratModC5 (q ^ mH ^ k') (E i j) *
        coordOf mH (q ^ mH ^ k') (chunkVal (q ^ mH ^ (k' + 1)) G B X y) j) % q ^ mH ^ k')
    ?_).congr fun _ _ => rfl
  intro y hy
  simp only [blk]
  refine congrArg (· % q ^ mH ^ k') (Finset.sum_congr rfl fun j _ => ?_)
  obtain ⟨h₁, h₂⟩ := coord_bounds q (mH ^ (k' + 1)) N0 R N1 G B mH (mH ^ k') (he_level k') X j
    j.isLt
  rw [(nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).blockVal_lexEquiv_symm h₁ h₂,
    idxBlock_coord q (mH ^ (k' + 1)) N0 R N1 G B mH (mH ^ k') (he_level k') X j j.isLt,
    ratModNat_eq_C5]

theorem pm_hdPlus (hq : 0 < q) (i j : Fin mH) :
    PullMatch (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)
      (Elem.shift (blk (4 + mH ^ (k' + 1)) (mH ^ k') j).1 (blk (4 + mH ^ (k' + 1)) (mH ^ k') j).2
        (fun x => (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).blockVal (blk 3 (mH ^ k') i).1
          (blk 3 (mH ^ k') i).2 x)).pull
      (streamMap q mH (.hdShift i j false) (k' + 1) N1 G B) := by
  refine (pm_shift_coord q (mH ^ (k' + 1)) N0 R N1 G B mH (mH ^ k') (he_level k') hq .D j j.isLt _
    (fun y => coordOf mH (q ^ mH ^ k') (hvalOf (q ^ mH ^ (k' + 1)) G B y) i) ?_).congr
    fun _ _ => rfl
  intro y hy
  have hb := coord_bounds q (mH ^ (k' + 1)) N0 R N1 G B mH (mH ^ k') (he_level k') .H i i.isLt
  have h₁ : 3 + ↑i * mH ^ k' ≤ 3 + (↑i + 1) * mH ^ k' := hb.1
  have h₂ : 3 + (↑i + 1) * mH ^ k' ≤ (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).n := hb.2
  have hc : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).idxBlock (3 + ↑i * mH ^ k')
      (3 + (↑i + 1) * mH ^ k') y =
      coordOf mH (q ^ mH ^ k') (chunkVal (q ^ mH ^ (k' + 1)) G B .H y) ↑i :=
    idxBlock_coord q (mH ^ (k' + 1)) N0 R N1 G B mH (mH ^ k') (he_level k') .H i i.isLt y
  simp only [blk]
  rw [(nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).blockVal_lexEquiv_symm h₁ h₂, hc,
    Nat.mod_eq_of_lt (coordOf_lt _ _ _ _ (pow_pos hq _))]
  rfl

theorem pm_hdMinus (hq : 0 < q) (i : Fin mH) :
    PullMatch (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)
      (Elem.shift (blk (4 + mH ^ (k' + 1)) (mH ^ k') i).1 (blk (4 + mH ^ (k' + 1)) (mH ^ k') i).2
        (fun x => q ^ mH ^ k' - (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).blockVal
          (blk 3 (mH ^ k') i).1 (blk 3 (mH ^ k') i).2 x % q ^ mH ^ k')).pull
      (streamMap q mH (.hdShift i i true) (k' + 1) N1 G B) := by
  refine (pm_shift_coord q (mH ^ (k' + 1)) N0 R N1 G B mH (mH ^ k') (he_level k') hq .D i i.isLt _
    (fun y => (q ^ mH ^ k' - coordOf mH (q ^ mH ^ k') (hvalOf (q ^ mH ^ (k' + 1)) G B y) i) %
      q ^ mH ^ k') ?_).congr fun y _ => ?_
  · intro y hy
    have hb := coord_bounds q (mH ^ (k' + 1)) N0 R N1 G B mH (mH ^ k') (he_level k') .H i i.isLt
    have h₁ : 3 + ↑i * mH ^ k' ≤ 3 + (↑i + 1) * mH ^ k' := hb.1
    have h₂ : 3 + (↑i + 1) * mH ^ k' ≤ (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).n := hb.2
    have hc : (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).idxBlock (3 + ↑i * mH ^ k')
        (3 + (↑i + 1) * mH ^ k') y =
        coordOf mH (q ^ mH ^ k') (chunkVal (q ^ mH ^ (k' + 1)) G B .H y) ↑i :=
      idxBlock_coord q (mH ^ (k' + 1)) N0 R N1 G B mH (mH ^ k') (he_level k') .H i i.isLt y
    simp only [blk]
    rw [(nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B).blockVal_lexEquiv_symm h₁ h₂, hc,
      Nat.mod_eq_of_lt (coordOf_lt _ _ _ _ (pow_pos hq _))]
    rfl
  · rw [shift_neg_eq _ _ _ (coordOf_lt _ _ _ _ (pow_pos hq _))]
    rfl

theorem pm_negD (hq : 0 < q) (j : Fin mH) :
    PullMatch (nodeLayout q (mH ^ (k' + 1)) N0 R N1 G B)
      (Elem.unit (blk (4 + mH ^ (k' + 1)) (mH ^ k') j).1 (blk (4 + mH ^ (k' + 1)) (mH ^ k') j).2
        (q ^ mH ^ k' - 1) (q ^ mH ^ k' - 1)).pull
      (streamMap q mH (.unit .D j (-1)) (k' + 1) N1 G B) := by
  refine (pm_unit_coord q (mH ^ (k' + 1)) N0 R N1 G B mH (mH ^ k') (he_level k') hq .D j j.isLt
    _ _).congr fun y _ => ?_
  simp only [streamMap, Nat.add_sub_cancel, ratModC5_neg_one (q ^ mH ^ k') (pow_pos hq _)]

end Level

section Swap

variable (q e N0 R N1 G B m b : ℕ) (he : e = m * b)
include he

/-- The child interchange of the coordinates `H_i`, `D_j` (blocks of `b` digits). -/
theorem pm_swap (hq : 0 < q) (hG : 0 < G) (hB : 0 < B) (i j : ℕ) (hi : i < m) (hj : j < m) :
    PullMatch (nodeLayout q e N0 R N1 G B)
      (fun x => (nodeLayout q e N0 R N1 G B).blockSet (4 + e + j * b) (4 + e + j * b + b)
        ((nodeLayout q e N0 R N1 G B).blockSet (3 + i * b) (3 + i * b + b) x
          ((nodeLayout q e N0 R N1 G B).blockVal (4 + e + j * b) (4 + e + j * b + b) x))
        ((nodeLayout q e N0 R N1 G B).blockVal (3 + i * b) (3 + i * b + b) x))
      (swapFieldsInv (q ^ b) (q ^ ((m - 1 - i) * b) * G * q ^ (j * b)) (q ^ b)
        (q ^ ((m - 1 - j) * b) * B)) := by
  have hi1 : i * b + b ≤ m * b := by
    have h : (i + 1) * b ≤ m * b := Nat.mul_le_mul_right b hi
    rwa [Nat.add_mul, Nat.one_mul] at h
  have hj1 : j * b + b ≤ m * b := by
    have h : (j + 1) * b ≤ m * b := Nat.mul_le_mul_right b hj
    rwa [Nat.add_mul, Nat.one_mul] at h
  have hn : (nodeLayout q e N0 R N1 G B).n = 5 + 2 * e := rfl
  have ht : 3 + i * b + b ≤ (nodeLayout q e N0 R N1 G B).n := by rw [hn]; omega
  have hs : 4 + e + j * b + b ≤ (nodeLayout q e N0 R N1 G B).n := by rw [hn]; omega
  have hts : 3 + i * b + b ≤ 4 + e + j * b := by omega
  have hHb : (nodeLayout q e N0 R N1 G B).blockRange (3 + i * b) (3 + i * b + b) = q ^ b := by
    rw [br_chunk q e N0 R N1 G B (3 + i * b) (3 + i * b + b) (by omega)
      (Or.inl ⟨by omega, by omega⟩), Nat.add_sub_cancel_left]
  have hDb : (nodeLayout q e N0 R N1 G B).blockRange (4 + e + j * b) (4 + e + j * b + b) =
      q ^ b := by
    rw [br_chunk q e N0 R N1 G B (4 + e + j * b) (4 + e + j * b + b) (by omega)
      (Or.inr ⟨by omega, by omega⟩), Nat.add_sub_cancel_left]
  have hG' : (nodeLayout q e N0 R N1 G B).blockRange (3 + e) (4 + e) = G := by
    rw [show 4 + e = 3 + e + 1 by omega, br_single' q e N0 R N1 G B (3 + e) (by omega), nodeR_G]
  have hmid : (nodeLayout q e N0 R N1 G B).blockRange (3 + i * b + b) (4 + e + j * b) =
      q ^ ((m - 1 - i) * b) * G * q ^ (j * b) := by
    rw [blockRange_split (by omega : 3 + i * b + b ≤ 3 + e) (by omega : 3 + e ≤ 4 + e + j * b),
      blockRange_split (by omega : 3 + e ≤ 4 + e) (by omega : 4 + e ≤ 4 + e + j * b), hG',
      br_chunk q e N0 R N1 G B (3 + i * b + b) (3 + e) (by omega) (Or.inl ⟨by omega, le_rfl⟩),
      br_chunk q e N0 R N1 G B (4 + e) (4 + e + j * b) (by omega) (Or.inr ⟨le_rfl, by omega⟩),
      Nat.add_sub_cancel_left, show 3 + e - (3 + i * b + b) = (m - 1 - i) * b by
        rw [← exp_tail m b i hi]; omega]
    ring
  have htail : (nodeLayout q e N0 R N1 G B).blockRange (4 + e + j * b + b)
      (nodeLayout q e N0 R N1 G B).n = q ^ ((m - 1 - j) * b) * B := by
    rw [br_D_tail q e N0 R N1 G B (4 + e + j * b + b) (by omega) (by omega),
      show 4 + 2 * e - (4 + e + j * b + b) = (m - 1 - j) * b by rw [← exp_tail m b j hj]; omega]
  intro y hy
  beta_reduce
  rw [Model.lexEquiv_swapBlocks ht hs ⟨y, hy⟩,
    Model.swapIdx_eq_swapFieldsInv hts hs (hHb.trans hDb.symm)
      ⟨by rw [hHb]; exact pow_pos hq b,
        by rw [hmid]; exact Nat.mul_pos (Nat.mul_pos (pow_pos hq _) hG) (pow_pos hq _),
        by rw [htail]; exact Nat.mul_pos (pow_pos hq _) hB⟩,
    hDb, hmid, htail]
  rfl

/-- The child interchange is a row-permutation of the rows of `N1 · q^e · G · q^e · B`. -/
theorem swap_rowPerm (i j : ℕ) (hi : i < m) (hj : j < m) :
    RowPerm (N1 * q ^ e * G * q ^ e * B)
      (swapFieldsInv (q ^ b) (q ^ ((m - 1 - i) * b) * G * q ^ (j * b)) (q ^ b)
        (q ^ ((m - 1 - j) * b) * B)) := by
  have hi1 : i * b + b ≤ m * b := by
    have h : (i + 1) * b ≤ m * b := Nat.mul_le_mul_right b hi
    rwa [Nat.add_mul, Nat.one_mul] at h
  have hj1 : j * b + b ≤ m * b := by
    have h : (j + 1) * b ≤ m * b := Nat.mul_le_mul_right b hj
    rwa [Nat.add_mul, Nat.one_mul] at h
  have hI : q ^ e = q ^ ((m - 1 - i) * b) * q ^ b * q ^ (i * b) := by
    rw [← pow_add, ← pow_add]
    congr 1
    rw [← exp_tail m b i hi]
    omega
  have hJ : q ^ e = q ^ ((m - 1 - j) * b) * q ^ b * q ^ (j * b) := by
    rw [← pow_add, ← pow_add]
    congr 1
    rw [← exp_tail m b j hj]
    omega
  have hS : N1 * q ^ e * G * q ^ e * B =
      (q ^ b * (q ^ ((m - 1 - i) * b) * G * q ^ (j * b)) * q ^ b * (q ^ ((m - 1 - j) * b) * B)) *
        (N1 * q ^ (i * b)) := by
    calc N1 * q ^ e * G * q ^ e * B = N1 * (q ^ ((m - 1 - i) * b) * q ^ b * q ^ (i * b)) * G *
          (q ^ ((m - 1 - j) * b) * q ^ b * q ^ (j * b)) * B := by rw [← hI, ← hJ]
      _ = _ := by ring
  refine ⟨fun t l _ => swapFieldsInv_rowLocal _ _ _ _ _ ⟨N1 * q ^ (i * b), ?_⟩ t l,
    fun l hl => swapFieldsInv_lt _ _ _ _ _ l ⟨N1 * q ^ (i * b), ?_⟩ hl⟩
  · rw [hS]; ring
  · rw [hS]

end Swap

end SubNLogN.Machine.C5.NetAux
