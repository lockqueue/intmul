/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvDescDefs
import SubNLogN.Machine.AppC.C5StreamArith

/-!
# DrvDesc PIECES, part 2 (`Machine/Layer/DrvDescPiecesMath.lean`): pieces as table entries

Pure facts behind the piece-descriptor kernel (`DrvDescPiecesStmt`, `DrvDescDefs.lean`):
* `entsAux ds j o`: the table entries `(count, offset, power, index)` of
  `piecesAux ds j o` (`Math/Networks/AppCLayerProc.lean`); `descOfVals_eq`: the output is the
  concatenation of the entry blocks `entBlk` (pieces `t = 0, …, c - 1` of an entry), then the end
  tag;
* the digit loop on `(q, j, o)` (`dstep`, `dst e i`): it emits `dent (dst e i)` at step `i`, runs
  exactly `(Nat.digits mH e).length` times (`dst_eq_zero_iff`), and its entries are
  `entsAux (Nat.digits mH e) 0 0` (`ents_eq`);
* size bounds used by the cost analysis (`dst_o_lt`, `pow_le_of_lt_len`, `len_le_bitLen`).

**Scope (honest summary).** Definitions and proved lemmas only; no machine statement.
-/

namespace SubNLogN.Machine.Layer.DrvDescPiecesAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine
open SubNLogN.Math.Networks (piecesOf piecesAux mH)

/-- The C-core descriptor of piece `(k, j0)` for the value record `[P, d, r, a, R, K, e, S, ρ]`. -/
def pdesc (P d r a R K e S ρ j0 k : ℕ) : List Sym := hdrSyms [P, d, r, P, a, R, K, e, S, j0, k, ρ]

/-- Table entries of `piecesAux ds j o`: `(count, offset, power, index)`. -/
def entsAux : List ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ × ℕ)
  | [], _, _ => []
  | c :: ds, j, o => (c, o, mH ^ j, j) :: entsAux ds (j + 1) (o + c * mH ^ j)

/-- The descriptors of one entry: pieces `t = 0, …, c - 1`, the first one first. -/
def entBlk (P d r a R K e S ρ : ℕ) (x : ℕ × ℕ × ℕ × ℕ) : List Sym :=
  ((List.range x.1).map fun t => pdesc P d r a R K e S ρ (x.2.1 + t * x.2.2.1) x.2.2.2).flatten

theorem piecesAux_descs (P d r a R K e S ρ : ℕ) : ∀ (ds : List ℕ) (j o : ℕ),
    ((piecesAux ds j o).map fun pc => hdrSyms [P, d, r, P, a, R, K, e, S, pc.2, pc.1, ρ]).flatten
      = (entsAux ds j o).flatMap (entBlk P d r a R K e S ρ)
  | [], _, _ => by simp [piecesAux, entsAux]
  | c :: ds, j, o => by
    rw [piecesAux, entsAux, List.map_append, List.flatten_append, List.flatMap_cons,
      piecesAux_descs P d r a R K e S ρ ds (j + 1) (o + c * mH ^ j)]
    simp [entBlk, pdesc, List.map_map, Function.comp_def]

/-- **The output as entry blocks.** -/
theorem descOfVals_eq (P d r a R K e S ρ : ℕ) :
    descOfVals P d r a R K e S ρ =
      (entsAux (Nat.digits mH e) 0 0).flatMap (entBlk P d r a R K e S ρ) ++ [drvEndTag] := by
  rw [descOfVals, piecesOf, piecesAux_descs]

/-! ## The digit loop -/

theorem one_lt_mH : 1 < mH := by norm_num [mH]

theorem mH_pos : 0 < mH := by norm_num [mH]

theorem bitLen_mH : bitLen mH ≤ 20 := NatArith.bitLen_le_of_lt' (by norm_num [mH])

/-- One digit step on `(q, j, o)`: `q / mH`, `j + 1`, `o + (q % mH)·mH^j`. -/
def dstep (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (x.1 / mH, x.2.1 + 1, x.2.2 + x.1 % mH * mH ^ x.2.1)

/-- The digit-loop state after `i` steps from `(e, 0, 0)`. -/
def dst (e i : ℕ) : ℕ × ℕ × ℕ := dstep^[i] (e, 0, 0)

/-- The table entry emitted at a digit-loop state. -/
def dent (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ := (x.1 % mH, x.2.2, mH ^ x.2.1, x.2.1)

theorem dst_zero (e : ℕ) : dst e 0 = (e, 0, 0) := rfl

theorem dst_succ (e i : ℕ) : dst e (i + 1) = dstep (dst e i) :=
  Function.iterate_succ_apply' dstep i (e, 0, 0)

theorem dst_j (e : ℕ) : ∀ i, (dst e i).2.1 = i
  | 0 => rfl
  | i + 1 => by rw [dst_succ]; simp only [dstep]; rw [dst_j e i]

theorem dst_q (e : ℕ) : ∀ i, (dst e i).1 = e / mH ^ i
  | 0 => by simp [dst_zero]
  | i + 1 => by
    rw [dst_succ]
    simp only [dstep]
    rw [dst_q e i, pow_succ, Nat.div_div_eq_div_mul]

theorem dst_len (e : ℕ) : ∀ i,
    (Nat.digits mH (dst e i).1).length = (Nat.digits mH e).length - i
  | 0 => by simp [dst_zero]
  | i + 1 => by
    have ih := dst_len e i
    rw [dst_succ]
    simp only [dstep]
    by_cases hq : (dst e i).1 = 0
    · rw [hq] at ih ⊢
      simp only [Nat.zero_div, Nat.digits_zero, List.length_nil] at ih ⊢
      omega
    · have h := Nat.digits_def' one_lt_mH (Nat.pos_of_ne_zero hq)
      rw [h, List.length_cons] at ih
      omega

theorem dst_eq_zero_iff (e i : ℕ) : (dst e i).1 = 0 ↔ (Nat.digits mH e).length ≤ i := by
  have h := dst_len e i
  constructor
  · intro h0
    rw [h0, Nat.digits_zero, List.length_nil] at h
    omega
  · intro hle
    have h1 : (Nat.digits mH (dst e i).1).length = 0 := by omega
    rw [List.length_eq_zero_iff, Nat.digits_eq_nil_iff_eq_zero] at h1
    exact h1

theorem ents_split (e : ℕ) : ∀ i, i ≤ (Nat.digits mH e).length →
    (List.range i).map (fun k => dent (dst e k)) ++
      entsAux (Nat.digits mH (dst e i).1) i (dst e i).2.2 = entsAux (Nat.digits mH e) 0 0
  | 0, _ => by simp [dst_zero]
  | i + 1, hi => by
    have hq : (dst e i).1 ≠ 0 := by
      rw [Ne, dst_eq_zero_iff]
      omega
    rw [← ents_split e i (by omega), List.range_succ, List.map_append, List.append_assoc]
    congr 1
    rw [Nat.digits_def' one_lt_mH (Nat.pos_of_ne_zero hq)]
    simp only [entsAux, dst_succ, dstep, dent, dst_j, List.map_cons, List.map_nil,
      List.singleton_append]

/-- **The digit loop's entries** are the table entries of `piecesOf e`. -/
theorem ents_eq (e : ℕ) :
    (List.range (Nat.digits mH e).length).map (fun k => dent (dst e k)) =
      entsAux (Nat.digits mH e) 0 0 := by
  have h := ents_split e _ le_rfl
  have h0 : (dst e (Nat.digits mH e).length).1 = 0 := (dst_eq_zero_iff e _).2 le_rfl
  rw [h0, Nat.digits_zero] at h
  simpa [entsAux] using h

/-! ## Size bounds -/

theorem dst_o_lt (e : ℕ) : ∀ i, (dst e i).2.2 < mH ^ i
  | 0 => by simp [dst_zero]
  | i + 1 => by
    have ih := dst_o_lt e i
    rw [dst_succ]
    simp only [dstep]
    rw [dst_j]
    have hm : (dst e i).1 % mH < mH := Nat.mod_lt _ mH_pos
    have h2 : (dst e i).1 % mH * mH ^ i ≤ (mH - 1) * mH ^ i := Nat.mul_le_mul_right _ (by omega)
    have h3 : (mH - 1) * mH ^ i + mH ^ i = mH ^ (i + 1) := by
      rw [pow_succ, ← Nat.succ_mul, Nat.succ_eq_add_one,
        Nat.sub_add_cancel (show 1 ≤ mH by norm_num [mH]), Nat.mul_comm]
    omega

theorem pow_le_of_lt_len {e i : ℕ} (hi : i < (Nat.digits mH e).length) : mH ^ i ≤ e := by
  have hq : (dst e i).1 ≠ 0 := by
    rw [Ne, dst_eq_zero_iff]
    omega
  rw [dst_q] at hq
  by_contra h
  exact hq (Nat.div_eq_of_lt (by omega))

theorem len_le_bitLen (e : ℕ) : (Nat.digits mH e).length ≤ bitLen e := by
  by_contra h
  have h1 : mH ^ (bitLen e) ≤ e := pow_le_of_lt_len (by omega)
  have h2 : 2 ^ (bitLen e) ≤ mH ^ (bitLen e) := Nat.pow_le_pow_left (by norm_num [mH]) _
  have h3 := NatArith.lt_two_pow_bitLen e
  omega

end SubNLogN.Machine.Layer.DrvDescPiecesAux
