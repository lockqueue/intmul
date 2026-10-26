import Contracts.W9.Pre
import WP.W9b.Macros

/-!
# WP.W9b.AltMath — the value of `W9_altSum` (P2) as the machine computes it

`computableNyquistAltSumContiguous p_in q r row` (CES:542) is the snapshot's retained Nyquist value.
For `r = 2^m` it is a `gRescale` of the alternating sum (`nyq_eq_rescale`, the computation of
`W8_nyquistAltSumScale_shift`), so the machine computes:

1. the pairwise accumulators `accRe ps = Σ (a.1 − b.1)` and `accIm ps = Σ (b.2 − a.2)` over the pairs
   `(a, b)` of the row (`altL_unpair`: these are `altSum.1` and `−altSum.2`);
2. a shift of each by `|q − (m + p_in)|` (`W8.gRescale_shift`): left, or a rounding right shift,
   which the machine performs as add `2^(k−1)`, then a floor shift (`intSyms_divRound_nonneg/neg`).

No local `Zero` instance is set in this file: the snapshot's CES file uses the default one, and the
statements here must match it syntactically.

Bit-length helpers follow `WP.W6a.Basic` (re-proved here).
-/

namespace WP.W9b

open IntMul TMFw TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Bit lengths -/

theorem bitLen_add_add_one (n : ℕ) : bitLen (n + n + 1) = bitLen n + 1 := by
  simp [bitLen, encodeNat_add_add_one]

theorem bitLen_add_self_le (n : ℕ) : bitLen (n + n) ≤ bitLen n + 1 := by
  unfold bitLen
  rw [encodeNat_add]
  split_ifs <;> simp

theorem bitLen_add_self (n : ℕ) (h : n ≠ 0) : bitLen (n + n) = bitLen n + 1 := by
  unfold bitLen
  rw [encodeNat_add, if_neg (by rw [encodeNat_eq_nil_iff]; exact h)]
  simp

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · by_cases hk : k = 0
    · subst hk
      simp [bitLen_zero]
    · rw [two_mul, bitLen_add_self k hk, pow_succ]
      have := ih k (by omega)
      omega
  · rw [two_mul, bitLen_add_add_one, pow_succ]
    have := ih k (by omega)
    omega

theorem bitLen_le_of_lt_two_pow {n k : ℕ} (h : n < 2 ^ k) : bitLen n ≤ k := by
  induction k generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    subst hn
    simp [bitLen_zero]
  | succ k ih =>
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [pow_succ] at h
      have h1 := ih (n := j) (by omega)
      have h2 := bitLen_add_self_le j
      rw [two_mul]
      omega
    · rw [pow_succ] at h
      have h1 := ih (n := j) (by omega)
      rw [two_mul, bitLen_add_add_one]
      omega

theorem bitLen_mono {m n : ℕ} (h : m ≤ n) : bitLen m ≤ bitLen n :=
  bitLen_le_of_lt_two_pow (lt_of_le_of_lt h (lt_two_pow_bitLen n))

theorem bitLen_two_pow (k : ℕ) : bitLen (2 ^ k) = k + 1 := by
  induction k with
  | zero => exact (bitLen_add_add_one 0).trans (by rw [bitLen_zero])
  | succ k ih =>
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    rw [h2, bitLen_add_self _ (Nat.two_pow_pos k).ne', ih]

theorem natAbs_lt_of_entryW {w : ℕ} {z : ℤ × ℤ} (h : EntryW w z) :
    z.1.natAbs < 2 ^ w ∧ z.2.natAbs < 2 ^ w :=
  ⟨lt_of_lt_of_le (lt_two_pow_bitLen _) (Nat.pow_le_pow_right (by norm_num) h.1),
    lt_of_lt_of_le (lt_two_pow_bitLen _) (Nat.pow_le_pow_right (by norm_num) h.2)⟩

/-! ## The Nyquist value is a rescale of the alternating sum -/

/-- `W8_nyquistAltSumScale_shift` for `computableNyquistAltSumContiguous` itself. -/
theorem nyq_eq_rescale (p_in q m : ℕ) (row : Array (ℤ × ℤ)) :
    computableNyquistAltSumContiguous p_in q (2 ^ m) row =
      gRescale (m + p_in) q
        (-(sumRangePair (fun j => gAltTerm j (read1D row j)) (2 ^ m)).2,
          (sumRangePair (fun j => gAltTerm j (read1D row j)) (2 ^ m)).1) := by
  unfold computableNyquistAltSumContiguous gRescale
  dsimp only
  have h : ((2 ^ m : ℕ) : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ) = ((2 ^ (m + p_in + 2) : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h]

theorem read1D_eq_getD (a : Array (ℤ × ℤ)) (j : ℕ) : read1D a j = a.toList.getD j 0 := by
  unfold read1D
  by_cases h : j < a.size
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [dif_neg h, List.getD_eq_default _ _ (by simpa using h)]

/-! ## Alternating sums of lists -/

/-- The snapshot's alternating sum `Σ_j (−1)^j l[j]` of a list. -/
def altL (l : List (ℤ × ℤ)) : ℤ × ℤ := sumRangePair (fun j => gAltTerm j (l.getD j 0)) l.length

theorem sumRangePair_front (f : ℕ → ℤ × ℤ) (n : ℕ) :
    sumRangePair f (n + 1) = gAdd (f 0) (sumRangePair (fun j => f (j + 1)) n) := by
  induction n with
  | zero => simp [sumRangePair, gAdd]
  | succ n ih =>
    rw [show sumRangePair f (n + 1 + 1) = gAdd (sumRangePair f (n + 1)) (f (n + 1)) from rfl, ih,
      show sumRangePair (fun j => f (j + 1)) (n + 1) =
        gAdd (sumRangePair (fun j => f (j + 1)) n) (f (n + 1)) from rfl]
    simp only [gAdd, Prod.mk.injEq]
    constructor <;> ring

theorem sumRangePair_neg (f : ℕ → ℤ × ℤ) (n : ℕ) :
    sumRangePair (fun j => gNeg (f j)) n = gNeg (sumRangePair f n) := by
  induction n with
  | zero => simp [sumRangePair, gNeg]
  | succ n ih =>
    rw [show sumRangePair (fun j => gNeg (f j)) (n + 1) =
        gAdd (sumRangePair (fun j => gNeg (f j)) n) (gNeg (f n)) from rfl, ih,
      show sumRangePair f (n + 1) = gAdd (sumRangePair f n) (f n) from rfl]
    simp only [gAdd, gNeg, Prod.mk.injEq]
    constructor <;> ring

theorem gAltTerm_succ (j : ℕ) (z : ℤ × ℤ) : gAltTerm (j + 1) z = gNeg (gAltTerm j z) := by
  unfold gAltTerm
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg (by omega)]
    simp [gNeg]

theorem altL_cons (a : ℤ × ℤ) (l : List (ℤ × ℤ)) : altL (a :: l) = gAdd a (gNeg (altL l)) := by
  unfold altL
  rw [List.length_cons, sumRangePair_front]
  simp only [List.getD_cons_zero, List.getD_cons_succ, gAltTerm_succ]
  rw [sumRangePair_neg]
  congr 1

theorem sum_alt_eq_altL (row : Array (ℤ × ℤ)) :
    sumRangePair (fun j => gAltTerm j (read1D row j)) row.size = altL row.toList := by
  unfold altL
  simp only [read1D_eq_getD, Array.length_toList]

/-! ## Pairs -/

/-- An entry pair `(a, b)` of the row (entries `2i`, `2i+1`). -/
abbrev EPair := (ℤ × ℤ) × (ℤ × ℤ)

/-- Flatten a list of pairs. -/
def unpair : List EPair → List (ℤ × ℤ)
  | [] => []
  | p :: ps => p.1 :: p.2 :: unpair ps

/-- Cut a list into consecutive pairs. -/
def pairUp : List (ℤ × ℤ) → List EPair
  | a :: b :: l => (a, b) :: pairUp l
  | _ => []

/-- Real accumulator: `Σ (a.1 − b.1)`. -/
def accRe (ps : List EPair) : ℤ := (ps.map fun p => p.1.1 - p.2.1).sum

/-- Imaginary accumulator, negated: `Σ (b.2 − a.2)`. -/
def accIm (ps : List EPair) : ℤ := (ps.map fun p => p.2.2 - p.1.2).sum

theorem accRe_append (ps : List EPair) (p : EPair) :
    accRe (ps ++ [p]) = accRe ps + p.1.1 - p.2.1 := by
  simp [accRe]
  ring

theorem accIm_append (ps : List EPair) (p : EPair) :
    accIm (ps ++ [p]) = accIm ps - p.1.2 + p.2.2 := by
  simp [accIm]
  ring

theorem altL_unpair : ∀ ps : List EPair,
    (altL (unpair ps)).1 = accRe ps ∧ -(altL (unpair ps)).2 = accIm ps
  | [] => by simp [altL, unpair, accRe, accIm]
  | p :: ps => by
    obtain ⟨h1, h2⟩ := altL_unpair ps
    simp only [unpair, altL_cons, gAdd, gNeg, accRe, accIm, List.map_cons, List.sum_cons] at h1 h2 ⊢
    constructor <;> linarith

theorem unpair_pairUp : ∀ (n : ℕ) (l : List (ℤ × ℤ)), l.length = 2 * n →
    unpair (pairUp l) = l ∧ (pairUp l).length = n
  | 0, l, h => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [pairUp, unpair]
  | n + 1, a :: b :: l, h => by
    obtain ⟨h1, h2⟩ := unpair_pairUp n l (by simp at h; omega)
    simp [pairUp, unpair, h1, h2]
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega

/-! ## The retained value as the machine computes it -/

/-- **P2 value.** With `r = 2^m` and `m ≥ 1`, the snapshot's retained value is the rescale of the
two pairwise accumulators of the row. -/
theorem nyq_eq_acc (p_in q m : ℕ) (hm : 1 ≤ m) (row : Array (ℤ × ℤ)) (hrow : row.size = 2 ^ m) :
    computableNyquistAltSumContiguous p_in q (2 ^ m) row =
      gRescale (m + p_in) q (accIm (pairUp row.toList), accRe (pairUp row.toList)) := by
  rw [nyq_eq_rescale, ← hrow, sum_alt_eq_altL]
  have hlen : row.toList.length = 2 * 2 ^ (m - 1) := by
    rw [Array.length_toList, hrow, ← pow_succ']
    congr 1
    omega
  obtain ⟨hu, -⟩ := unpair_pairUp _ _ hlen
  obtain ⟨h1, h2⟩ := altL_unpair (pairUp row.toList)
  rw [hu] at h1 h2
  rw [h1, h2]

/-! ## Rounding shifts -/

theorem divRoundPow2_pos (z : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    divRoundPow2 z k = (z + ((2 ^ (k - 1) : ℕ) : ℤ)) / ((2 ^ k : ℕ) : ℤ) := by
  unfold divRoundPow2
  rw [if_neg (by omega)]

theorem ediv_two_pow_of_nonneg (y : ℤ) (hy : 0 ≤ y) (k : ℕ) :
    y / ((2 ^ k : ℕ) : ℤ) = ((y.natAbs / 2 ^ k : ℕ) : ℤ) := by
  rw [Int.natCast_ediv, Int.natAbs_of_nonneg hy]

theorem ediv_two_pow_of_neg (y : ℤ) (hy : y < 0) (k : ℕ) :
    y / ((2 ^ k : ℕ) : ℤ) = -(((y.natAbs - 1) / 2 ^ k + 1 : ℕ) : ℤ) := by
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hy
  rw [Int.natAbs_negSucc, Nat.succ_sub_one]
  have hd : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdiv := Nat.div_add_mod n (2 ^ k)
  have hmod := Nat.mod_lt n hd
  generalize 2 ^ k = d at hd hdiv hmod ⊢
  have hc : (n : ℤ) = (d : ℤ) * ((n / d : ℕ) : ℤ) + ((n % d : ℕ) : ℤ) := by exact_mod_cast hdiv.symm
  have h1 : ((d : ℤ) - 1 - ((n % d : ℕ) : ℤ)) + (d : ℤ) * -(((n / d + 1 : ℕ) : ℤ)) =
      Int.negSucc n := by
    rw [Int.negSucc_eq]
    push_cast at hc ⊢
    linarith [hc]
  have h2 : (0 : ℤ) ≤ (d : ℤ) - 1 - ((n % d : ℕ) : ℤ) := by omega
  have h3 : (d : ℤ) - 1 - ((n % d : ℕ) : ℤ) < (d : ℤ) := by omega
  exact ((Int.ediv_emod_unique (by exact_mod_cast hd)).2 ⟨h1, h2, h3⟩).1

/-- The rounding shift, nonnegative case: `pos`, then `|y| / 2^k`, where `y = z + 2^(k−1)`. -/
theorem intSyms_divRound_nonneg (z : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hy : 0 ≤ z + ((2 ^ (k - 1) : ℕ) : ℤ)) :
    intSyms (divRoundPow2 z k) =
      Sym.pos :: natSyms ((z + ((2 ^ (k - 1) : ℕ) : ℤ)).natAbs / 2 ^ k) := by
  rw [divRoundPow2_pos z k hk, ediv_two_pow_of_nonneg _ hy, intSyms_natCast]

/-- The rounding shift, negative case: `neg`, then `(|y| − 1) / 2^k + 1`. -/
theorem intSyms_divRound_neg (z : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hy : z + ((2 ^ (k - 1) : ℕ) : ℤ) < 0) :
    intSyms (divRoundPow2 z k) =
      Sym.neg :: natSyms (((z + ((2 ^ (k - 1) : ℕ) : ℤ)).natAbs - 1) / 2 ^ k + 1) := by
  rw [divRoundPow2_pos z k hk, ediv_two_pow_of_neg _ hy]
  simp only [intSyms, sgnSym, Int.natAbs_neg, Int.natAbs_natCast]
  rw [if_pos (neg_neg_of_pos (by positivity))]

/-- The left shift keeps the sign and shifts the magnitude. -/
theorem intSyms_mul_two_pow (z : ℤ) (d : ℕ) :
    intSyms (z * ((2 ^ d : ℕ) : ℤ)) = sgnSym z :: natSyms (z.natAbs * 2 ^ d) := by
  have hd : (0 : ℤ) < ((2 ^ d : ℕ) : ℤ) := by positivity
  simp only [intSyms, sgnSym, Int.natAbs_mul, Int.natAbs_natCast]
  congr 1
  by_cases hz : z < 0
  · rw [if_pos hz, if_pos (Int.mul_neg_of_neg_of_pos hz hd)]
  · rw [if_neg hz, if_neg (by nlinarith)]

/-- `intSyms (2^k)`: `pos`, then `k` zeros and a one. -/
theorem intSyms_two_pow (k : ℕ) : intSyms (((2 ^ k : ℕ) : ℤ)) = Sym.pos :: natSyms (2 ^ k) :=
  intSyms_natCast _

/-! ## Width bounds of the accumulators -/

theorem natAbs_accRe_le (B : ℕ) : ∀ ps : List EPair,
    (∀ p ∈ ps, p.1.1.natAbs ≤ B ∧ p.2.1.natAbs ≤ B) → (accRe ps).natAbs ≤ 2 * ps.length * B
  | [], _ => by simp [accRe]
  | p :: ps, h => by
    have hp := h p (List.mem_cons_self ..)
    have ih := natAbs_accRe_le B ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have e : accRe (p :: ps) = (p.1.1 - p.2.1) + accRe ps := by simp [accRe]
    rw [e]
    have h1 := Int.natAbs_add_le (p.1.1 - p.2.1) (accRe ps)
    have h2 := Int.natAbs_sub_le p.1.1 p.2.1
    simp only [List.length_cons]
    nlinarith

theorem natAbs_accIm_le (B : ℕ) : ∀ ps : List EPair,
    (∀ p ∈ ps, p.1.2.natAbs ≤ B ∧ p.2.2.natAbs ≤ B) → (accIm ps).natAbs ≤ 2 * ps.length * B
  | [], _ => by simp [accIm]
  | p :: ps, h => by
    have hp := h p (List.mem_cons_self ..)
    have ih := natAbs_accIm_le B ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have e : accIm (p :: ps) = (p.2.2 - p.1.2) + accIm ps := by simp [accIm]
    rw [e]
    have h1 := Int.natAbs_add_le (p.2.2 - p.1.2) (accIm ps)
    have h2 := Int.natAbs_sub_le p.2.2 p.1.2
    simp only [List.length_cons]
    nlinarith

/-- A sum of at most `2^m` terms of width `≤ w` has width `≤ w + m`. -/
theorem bitLen_le_of_natAbs_le {x c w m : ℕ} (hx : x ≤ c * (2 ^ w - 1)) (hc : c ≤ 2 ^ m) :
    bitLen x ≤ w + m := by
  refine bitLen_le_of_lt_two_pow ?_
  have h1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  have h2 : c * (2 ^ w - 1) ≤ 2 ^ m * (2 ^ w - 1) := Nat.mul_le_mul_right _ hc
  have h3 : 2 ^ m * (2 ^ w - 1) < 2 ^ m * 2 ^ w :=
    Nat.mul_lt_mul_of_pos_left (by omega) (Nat.two_pow_pos m)
  rw [pow_add, Nat.mul_comm (2 ^ w)]
  omega

#assert_std_axioms bitLen_add_add_one bitLen_add_self_le bitLen_add_self lt_two_pow_bitLen
  bitLen_le_of_lt_two_pow bitLen_mono bitLen_two_pow natAbs_lt_of_entryW nyq_eq_rescale
  read1D_eq_getD sumRangePair_front sumRangePair_neg gAltTerm_succ altL_cons sum_alt_eq_altL
  accRe_append accIm_append altL_unpair unpair_pairUp nyq_eq_acc divRoundPow2_pos
  ediv_two_pow_of_nonneg ediv_two_pow_of_neg intSyms_divRound_nonneg intSyms_divRound_neg
  intSyms_mul_two_pow intSyms_two_pow natAbs_accRe_le natAbs_accIm_le bitLen_le_of_natAbs_le

end WP.W9b
