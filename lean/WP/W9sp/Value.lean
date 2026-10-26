import WP.W9sp.Kit
import Mathlib.Tactic.Ring

/-!
# WP.W9sp.Value — the packed root input as an explicit entry list

`rootPackV b K0 k1 k2 A B` (Contracts.W9.Root, the snapshot's PHP:1088-1093) has entry `j`
`ent b A B j = (4·chunk b A j, 4·chunk b B j)` for every `j < 2^K0`, where
`chunk b A j = ⌊A / 2^(b·j)⌋ mod 2^b` (`rootPackV_toList`; out-of-range chunks are `0`, which is
also what `read1D` returns, because `A < 2^(b·k1)`). `packSyms b A B n` is the symbol string of the
first `n` entries; `streamSyms_pack` rewrites the contract's output stream with it.
-/

namespace WP.W9sp

open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul Computability

/-! ## Arrays and chunks -/

theorem toList_runSeq {α : Type} (f : ℕ → α) :
    ∀ n, (runSequentialScanSteps f n).outTape.toList = (List.range n).map f
  | 0 => by simp [runSequentialScanSteps]
  | n + 1 => by
    rw [List.range_succ, List.map_append, ← toList_runSeq f n]
    show (scanHeadStep f (runSequentialScanSteps f n)).outTape.toList = _
    simp only [scanHeadStep, Array.toList_push, runSequentialScanSteps_inHead, List.map_cons,
      List.map_nil]

theorem read1D_toArray (l : List ℕ) (j : ℕ) : read1D l.toArray j = l.getD j 0 := by
  unfold read1D
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem_toArray, List.getElem?_eq_getElem (by simpa using h)]
    rfl
  · rw [List.getElem?_eq_none (by simp at h; omega)]
    rfl

/-- Chunk `j` of `A` in base `2^b`. -/
def chunk (b A j : ℕ) : ℕ := A / 2 ^ (b * j) % 2 ^ b

theorem chunk_lt (b A j : ℕ) : chunk b A j < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)

theorem splitChunks_getD (b : ℕ) :
    ∀ (k A j : ℕ), A < 2 ^ (b * k) → (splitChunks b k A).getD j 0 = chunk b A j
  | 0, A, j, hA => by
    have h0 : A = 0 := by simpa using hA
    subst h0
    simp [splitChunks, chunk]
  | k + 1, A, 0, _ => by
    simp [splitChunks, chunk]
  | k + 1, A, j + 1, hA => by
    have hA' : A / 2 ^ b < 2 ^ (b * k) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b), ← Nat.pow_add]
      rw [show b * k + b = b * (k + 1) by ring]
      exact hA
    simp only [splitChunks, List.getD_cons_succ]
    rw [splitChunks_getD b k (A / 2 ^ b) j hA']
    unfold chunk
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show b + b * j = b * (j + 1) by ring]

/-- Packed entry `j` of the root input. -/
def ent (b A B j : ℕ) : ℤ × ℤ := (4 * (chunk b A j : ℤ), 4 * (chunk b B j : ℤ))

theorem rootPackV_toList {b K0 k1 k2 A B : ℕ} (hA : A < 2 ^ (b * k1)) (hB : B < 2 ^ (b * k2)) :
    (rootPackV b K0 k1 k2 A B).toList = (List.range (2 ^ K0)).map (ent b A B) := by
  unfold rootPackV
  rw [toList_runSeq]
  apply List.map_congr_left
  intro j _
  show ((4 * ((read1D (splitChunksTree b k1 A).toArray j : ℕ) : ℤ)),
    4 * ((read1D (splitChunksTree b k2 B).toArray j : ℕ) : ℤ)) = ent b A B j
  rw [splitChunksTree_eq_splitChunks, splitChunksTree_eq_splitChunks, read1D_toArray,
    read1D_toArray, splitChunks_getD b k1 A j hA, splitChunks_getD b k2 B j hB]
  rfl

/-! ## Symbols -/

theorem natSyms_zero_sp : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]

theorem natSyms_one_sp : natSyms 1 = [Sym.bit true] := by
  have h := encodeNat_add_add_one 0
  rw [encodeNat_zero] at h
  simp [natSyms, h]

theorem rev_natSyms (n : ℕ) : (encodeNat n).reverse.map Sym.bit = (natSyms n).reverse := by
  simp [natSyms, List.map_reverse]

theorem intSyms_four_mul (c : ℕ) : intSyms (4 * (c : ℤ)) = Sym.pos :: natSyms (c * 2 ^ 2) := by
  rw [← intSyms_natCast]
  congr 1
  push_cast
  ring

/-- Symbols of the first `n` packed entries, entry `0` first. -/
def packSyms (b A B n : ℕ) : List Sym :=
  ((List.range n).map fun j => entrySyms (ent b A B j)).flatten

theorem packSyms_zero (b A B : ℕ) : packSyms b A B 0 = [] := rfl

theorem packSyms_succ (b A B n : ℕ) :
    packSyms b A B (n + 1) = packSyms b A B n ++ entrySyms (ent b A B n) := by
  simp only [packSyms, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.flatten_append, List.flatten_singleton]

/-- What one loop iteration pushes on the output scratch stack (entry `j` in natural symbol order,
hence reversed on the stack). -/
theorem rev_entry (b A B j : ℕ) (xo : List Sym) :
    Sym.sep :: ((natSyms (chunk b B j * 2 ^ 2)).reverse ++ Sym.pos :: Sym.sep2 ::
      ((natSyms (chunk b A j * 2 ^ 2)).reverse ++ Sym.pos :: xo)) =
    (entrySyms (ent b A B j)).reverse ++ xo := by
  simp [entrySyms, ent, intSyms_four_mul, List.reverse_append, List.append_assoc]

theorem rev_packSyms_succ (b A B n : ℕ) (xo : List Sym) :
    (entrySyms (ent b A B n)).reverse ++ ((packSyms b A B n).reverse ++ xo) =
      (packSyms b A B (n + 1)).reverse ++ xo := by
  rw [packSyms_succ, List.reverse_append, List.append_assoc]

theorem streamSyms_pack {b K0 k1 k2 A B : ℕ} (hA : A < 2 ^ (b * k1)) (hB : B < 2 ^ (b * k2))
    (rest : List Sym) :
    streamSyms [rootPackV b K0 k1 k2 A B] ++ rest =
      packSyms b A B (2 ^ K0) ++ symNode :: symLevel :: rest := by
  simp only [streamSyms, nodeSyms, blkE, blk, rootPackV_toList hA hB, List.map_map,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append,
    List.nil_append, packSyms]
  rfl

/-- No `mark` in the packed symbols (the transfer stops at the scratch floor). -/
theorem mark_not_mem_packSyms (b A B n : ℕ) : Sym.mark ∉ (packSyms b A B n).reverse := by
  rw [List.mem_reverse]
  induction n with
  | zero => simp [packSyms_zero]
  | succ n ih =>
    rw [packSyms_succ, List.mem_append, not_or]
    refine ⟨ih, ?_⟩
    simp [entrySyms, ent, intSyms_four_mul, natSyms]

theorem length_packSyms_le (b A B : ℕ) :
    ∀ n, (packSyms b A B n).length ≤ n * (2 * b + 8)
  | 0 => by simp [packSyms_zero]
  | n + 1 => by
    have ih := length_packSyms_le b A B n
    rw [packSyms_succ, List.length_append, length_entrySyms]
    have h1 : bitLen (ent b A B n).1.natAbs ≤ b + 2 := by
      show bitLen (4 * (chunk b A n : ℤ)).natAbs ≤ b + 2
      rw [show (4 * (chunk b A n : ℤ)).natAbs = chunk b A n * 2 ^ 2 by omega]
      exact le_trans (WP.W7k2.bitLen_mul_two_pow_le _ 2)
        (by have := WP.W7k2.bitLen_le_of_lt (chunk_lt b A n); omega)
    have h2 : bitLen (ent b A B n).2.natAbs ≤ b + 2 := by
      show bitLen (4 * (chunk b B n : ℤ)).natAbs ≤ b + 2
      rw [show (4 * (chunk b B n : ℤ)).natAbs = chunk b B n * 2 ^ 2 by omega]
      exact le_trans (WP.W7k2.bitLen_mul_two_pow_le _ 2)
        (by have := WP.W7k2.bitLen_le_of_lt (chunk_lt b B n); omega)
    rw [Nat.succ_mul]
    omega

/-! ## Operand bookkeeping -/

theorem div_step (A b j : ℕ) : A / 2 ^ (b * j) / 2 ^ b = A / 2 ^ (b * (j + 1)) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show b * j + b = b * (j + 1) by ring]

theorem div_pow_eq_zero {b k N A : ℕ} (hA : A < 2 ^ (b * k)) (hk : k ≤ N) :
    A / 2 ^ (b * N) = 0 :=
  Nat.div_eq_of_lt (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left b hk)))

theorem hdrSyms_four (b K0 k1 k2 : ℕ) (r0 : List Sym) :
    hdrSyms [b, K0, k1, k2] ++ r0 =
      natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark :: (hdrSyms [k1, k2] ++ r0)) := by
  simp [hdrSyms, List.append_assoc]

#assert_std_axioms toList_runSeq read1D_toArray chunk_lt splitChunks_getD rootPackV_toList
  natSyms_zero_sp natSyms_one_sp rev_natSyms intSyms_four_mul packSyms_succ rev_entry
  rev_packSyms_succ streamSyms_pack mark_not_mem_packSyms length_packSyms_le div_step
  div_pow_eq_zero hdrSyms_four

end WP.W9sp
