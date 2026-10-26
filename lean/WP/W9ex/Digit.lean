import WP.W9ex.State

/-!
# WP.W9ex.Digit — one stream entry to one digit

`entryDigit` consumes one entry `⟦(re, im)⟧ = intSyms re ++ sep2 :: intSyms im ++ [sep]` from `S`
and pushes its digit `mdig z`, reversed and followed by its `mark`, on `D`:
* `skipPast S sep2` drops `re`;
* pop the sign of `im` and branch. `neg`: `negBranch` drops 8 bits, increments, drops 1 bit (the
  digit `(|im| / 2^8 + 1) / 2 = (|im| + 2^8) / 2^9`) and moves the digit to `D`. `pos`: digit `0`.
-/

namespace WP.W9ex

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-- The digit the machine computes from an entry. -/
def mdig (z : ℤ × ℤ) : ℕ := if z.2 < 0 then (z.2.natAbs / 2 ^ 8 + 1) / 2 else 0

/-- Branch test: the popped sign is `neg`. -/
def isNegR (r : Option Sym) : Bool := decide (r = some Sym.neg)

/-- Negative `im` (sign popped): the digit `(|im| / 2^8 + 1) / 2`, moved to `D`. -/
def negBranch : SProg K4 :=
  .seq (dropBits sS 8) (.seq (inc sS sT) (.seq (dropBit sS) (.seq (moveBits sS sD)
    (pushC sD .mark))))

/-- Non-negative `im` (sign popped): drop it, digit `0`. -/
def posBranch : SProg K4 := .seq (skipPast sS .sep) (pushC sD .mark)

/-- One entry to one digit. -/
def entryDigit : SProg K4 :=
  .seq (skipPast sS .sep2) (.seq (popR sS) (.ite isNegR negBranch posBranch))

/-! ## Symbol facts -/

theorem sep_not_mem_natSyms (n : ℕ) : Sym.sep ∉ natSyms n := by
  simp [natSyms]

theorem sep2_not_mem_intSyms (z : ℤ) : Sym.sep2 ∉ intSyms z := by
  intro h
  simp only [intSyms, natSyms, List.mem_cons, List.mem_map] at h
  rcases h with h | ⟨b, -, h⟩
  · unfold sgnSym at h
    split_ifs at h
  · cases h

theorem isNegR_sgn (z : ℤ) : isNegR (some (sgnSym z)) = decide (z < 0) := by
  unfold isNegR sgnSym
  split_ifs with hz <;> simp [hz]

theorem entrySyms_eq (z : ℤ × ℤ) (rest : List Sym) :
    entrySyms z ++ rest =
      intSyms z.1 ++ Sym.sep2 :: (sgnSym z.2 :: (natSyms z.2.natAbs ++ Sym.sep :: rest)) := by
  simp [entrySyms, intSyms]

theorem length_intSyms (z : ℤ) : (intSyms z).length = bitLen z.natAbs + 1 := by
  simp [intSyms, length_natSyms]

/-! ## Branches -/

theorem xt_negBranch (σ : K4 → List Sym) (a : ℕ) (rest c0 oa d h c : List Sym) :
    XT (Φ σ (natSyms a ++ Sym.sep :: rest) c0 oa d h c) negBranch
      (Φ σ rest c0 oa ((natSyms ((a / 2 ^ 8 + 1) / 2) ++ [Sym.mark]).reverse ++ d) h c)
      (9 * bitLen a + 40) := by
  have hT : TermOK (Sym.sep :: rest) := TermOK.cons rfl rest
  have h1 := xt_dropBits (k := sS) hT 8 a (Φ σ (natSyms a ++ Sym.sep :: rest) c0 oa d h c) rfl
  rw [upd_S] at h1
  have h2 := xt_inc (k := sS) (t := sT) (by decide)
    (B := Φ σ (natSyms (a / 2 ^ 8) ++ Sym.sep :: rest) c0 oa d h c) (a / 2 ^ 8) hT rfl
  rw [upd_S] at h2
  have h3 := xt_dropBit (k := sS) (n := a / 2 ^ 8 + 1) hT
    (B := Φ σ (natSyms (a / 2 ^ 8 + 1) ++ Sym.sep :: rest) c0 oa d h c) rfl
  rw [upd_S] at h3
  have h4 := xt_moveBits (src := sS) (dst := sD) (by decide)
    (B := Φ σ (natSyms ((a / 2 ^ 8 + 1) / 2) ++ Sym.sep :: rest) c0 oa d h c)
    (encodeNat ((a / 2 ^ 8 + 1) / 2)) hT rfl
  rw [upd_S, upd_D, Φ_D, List.tail_cons] at h4
  have h5 := xt_pushC sD Sym.mark
    (Φ σ rest c0 oa ((encodeNat ((a / 2 ^ 8 + 1) / 2)).reverse.map Sym.bit ++ d) h c)
  rw [upd_D, Φ_D] at h5
  refine ((h1.seq (h2.seq (h3.seq (h4.seq h5)))).congr ?_).mono ?_
  · congr 1
    simp [natSyms]
  · have m1 := bitLen_mono a (a / 2 ^ 8) (Nat.div_le_self _ _)
    have hx : a / 2 ^ 8 ≤ a := Nat.div_le_self _ _
    have m2 := bitLen_mono a ((a / 2 ^ 8 + 1) / 2) (by omega)
    have e1 : (encodeNat ((a / 2 ^ 8 + 1) / 2)).length = bitLen ((a / 2 ^ 8 + 1) / 2) := rfl
    omega

theorem xt_posBranch (σ : K4 → List Sym) (a : ℕ) (rest c0 oa d h c : List Sym) :
    XT (Φ σ (natSyms a ++ Sym.sep :: rest) c0 oa d h c) posBranch
      (Φ σ rest c0 oa ((natSyms 0 ++ [Sym.mark]).reverse ++ d) h c) (2 * bitLen a + 3) := by
  have h1 := xt_skipPast (k := sS) (g := Sym.sep) (rest := rest)
    (B := Φ σ (natSyms a ++ Sym.sep :: rest) c0 oa d h c) (sep_not_mem_natSyms a) rfl
  rw [upd_S] at h1
  have h2 := xt_pushC sD Sym.mark (Φ σ rest c0 oa d h c)
  rw [upd_D, Φ_D] at h2
  refine ((h1.seq h2).congr ?_).mono ?_
  · simp [natSyms_zero]
  · have := length_natSyms a
    omega

/-- **One entry**: `S` loses the entry, `D` gains the digit (reversed, with its `mark`). -/
theorem xt_entryDigit (σ : K4 → List Sym) (z : ℤ × ℤ) (rest c0 oa d h c : List Sym) :
    XT (Φ σ (entrySyms z ++ rest) c0 oa d h c) entryDigit
      (Φ σ rest c0 oa ((natSyms (mdig z) ++ [Sym.mark]).reverse ++ d) h c)
      (2 * bitLen z.1.natAbs + 9 * bitLen z.2.natAbs + 46) := by
  have h1 := xt_skipPast (k := sS) (g := Sym.sep2)
    (rest := sgnSym z.2 :: (natSyms z.2.natAbs ++ Sym.sep :: rest))
    (B := Φ σ (entrySyms z ++ rest) c0 oa d h c) (sep2_not_mem_intSyms z.1)
    (by rw [Φ_S, entrySyms_eq])
  rw [upd_S] at h1
  have h2 := xt_popBranch (k := sS)
    (B := Φ σ (sgnSym z.2 :: (natSyms z.2.natAbs ++ Sym.sep :: rest)) c0 oa d h c)
    (B' := Φ σ rest c0 oa ((natSyms (mdig z) ++ [Sym.mark]).reverse ++ d) h c)
    (x := sgnSym z.2) (rest := natSyms z.2.natAbs ++ Sym.sep :: rest) rfl
    isNegR negBranch posBranch (T₁ := 9 * bitLen z.2.natAbs + 40)
    (T₂ := 2 * bitLen z.2.natAbs + 3)
    (fun hf => by
      rw [isNegR_sgn] at hf
      have hz : z.2 < 0 := of_decide_eq_true hf
      rw [upd_S, mdig, if_pos hz]
      exact xt_negBranch σ _ rest c0 oa d h c)
    (fun hf => by
      rw [isNegR_sgn] at hf
      have hz : ¬ z.2 < 0 := of_decide_eq_false hf
      rw [upd_S, mdig, if_neg hz]
      exact xt_posBranch σ _ rest c0 oa d h c)
  refine (h1.seq h2).mono ?_
  have := length_intSyms z.1
  omega

#assert_std_axioms sep_not_mem_natSyms sep2_not_mem_intSyms isNegR_sgn entrySyms_eq length_intSyms
  xt_negBranch xt_posBranch xt_entryDigit

end WP.W9ex
