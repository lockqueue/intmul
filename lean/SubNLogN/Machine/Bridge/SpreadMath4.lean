/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadBlockC

/-!
# K5 spreading, pure lemmas IV: the block loop of a line (`Bridge/SpreadMath4.lean`)

List facts for driving the block loop over the extended line `E` in chunks of `W` records
(`chunk E W j = (E.drop (jW)).take W`): prefixes, chunk lengths, the convolution of a prefix,
the zero initial tail, and the first symbol of a record array. Everything is proved.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine Computability
open scoped BigOperators

/-- Chunk `j` of the extended line. -/
def chunk (E : List CInt) (W j : ℕ) : List CInt := (E.drop (j * W)).take W

theorem take_append_chunk (E : List CInt) (W j : ℕ) :
    E.take (j * W) ++ chunk E W j = E.take ((j + 1) * W) := by
  rw [chunk, ← List.take_add, Nat.succ_mul]

theorem length_take_mul (E : List CInt) (W j : ℕ) (h : j * W ≤ E.length) :
    (E.take (j * W)).length = j * W := by
  rw [List.length_take]; omega

theorem length_chunk (E : List CInt) (W j : ℕ) :
    (chunk E W j).length = min W (E.length - j * W) := by
  simp [chunk, Nat.min_comm]

theorem drop_succ_chunk (E : List CInt) (W j : ℕ) :
    E.drop ((j + 1) * W) = (E.drop (j * W)).drop W := by
  rw [List.drop_drop, Nat.succ_mul, Nat.add_comm]

/-- The convolution at index `n` only reads entries `≤ n`. -/
theorem ccF_take (E G : List CInt) (L n : ℕ) (h : n < L) : ccF (E.take L) G n = ccF E G n := by
  unfold ccF
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have hiL : i < L := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hiL]

theorem vB_chunk (E G : List CInt) (W j i : ℕ) (hj : j * W ≤ E.length) (hi : i < (chunk E W j).length) :
    vB (E.take (j * W)) (chunk E W j) G i = ccF E G (j * W + i) := by
  unfold vB
  rw [take_append_chunk, length_take_mul E W j hj, ccF_take]
  rw [length_chunk] at hi
  rw [Nat.succ_mul]; omega

theorem twosBits_zero (s : ℕ) : twosBits s 0 = List.replicate s false := by
  unfold twosBits bitsLE
  simp

theorem ccF_nil_left (G : List CInt) (n : ℕ) : ccF [] G n = 0 := by
  unfold ccF
  exact Finset.sum_eq_zero fun i _ => by simp [cmulC_zero_left]

theorem tailBits_replicate_zero (s : ℕ) (f : CInt → ℤ) (hf : f 0 = 0) : ∀ n : ℕ,
    tailBits s f (List.replicate n 0) = List.replicate (n * s) false
  | 0 => by simp [tailBits]
  | n + 1 => by
    have ih := tailBits_replicate_zero s f hf n
    unfold tailBits at ih ⊢
    rw [List.replicate_succ, List.map_cons, List.flatten_cons, ih, hf, twosBits_zero,
      ← List.replicate_add]
    congr 1
    ring

theorem pend_nil (G : List CInt) : pend [] G = List.replicate (G.length - 1) 0 := by
  apply List.ext_getElem
  · simp [pend]
  · intro n h1 h2
    simp [pend, ccF_nil_left]

theorem tailBits_pend_nil (s : ℕ) (f : CInt → ℤ) (hf : f 0 = 0) (G : List CInt) :
    tailBits s f (pend [] G) = List.replicate ((G.length - 1) * s) false := by
  rw [pend_nil, tailBits_replicate_zero s f hf]

/-- A nonempty array of one-coefficient records starts with a bit (`w ≥ 1`). -/
theorem head_carrSyms_cons (w : ℕ) (hw : 1 ≤ w) (x : CInt) (L : List CInt) :
    ∃ b, (carrSyms w ((x :: L).map fun y => [y])).head? = some (Sym.bit b) := by
  rw [SolveAux.carrSyms_eq_recsOf]
  simp only [List.map_cons, SolveAux.recsOf_cons, recSyms, crecBits, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, coefBits]
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  rw [K1.twosBits_succ]
  exact ⟨_, rfl⟩

theorem head_carrSyms_nil (w : ℕ) : (carrSyms w (([] : List CInt).map fun y => [y])).head? = none := by
  rfl

end SubNLogN.Machine.Bridge.SpreadAux
