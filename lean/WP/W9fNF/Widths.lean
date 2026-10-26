import WP.W9fNF.Pass2

/-!
# WP.W9fNF.Widths — cleanup, and the bit-length facts used by the assembly

* `cleanup_eval`: drop `D1`, `D2`, `KI`, `ONE` and pop the six guards (exact).
* `accOK_top`: the pass-1 accumulators of a block of `≤ 2^k` entries of width `H + 1` have width
  `≤ H + k + 1`.
* `diff_widths`: every intermediate of `((alt - A) >>> (k - 1) + 1) >>> 1` has width `≤ H + k + 3`.
* `outList_natAbs`, `blkE_length_le`: sizes of the output block.
-/

namespace WP.W9fNF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability WP.W6a

theorem eval_popR' (ρ : List (SProg FS)) (a : FS) (v : Option Sym) (S : FS → List Sym) (x : Sym)
    (l : List Sym) (hS : S a = x :: l) :
    Eval ρ (popR a) ⟨v, S⟩ ⟨some x, Function.update S a l⟩ 1 :=
  eval_pop' ρ a (fun _ o => o) v S _ x l hS rfl

theorem cleanup_eval (B : FS → List Sym) (d1 d2 : ℤ) (k' : ℕ)
    (t0 a10 a20 x0 ki0 one0 : List Sym) (hT : B sT = Sym.mark :: t0)
    (hA1 : B sA1 = intSyms d1 ++ Sym.mark :: a10) (hA2 : B sA2 = intSyms d2 ++ Sym.mark :: a20)
    (hX : B sX = Sym.mark :: x0) (hKI : B sKI = intSyms k' ++ Sym.mark :: ki0)
    (hONE : B sONE = intSyms 1 ++ Sym.mark :: one0) (v : Option Sym) :
    Eval [] cleanup ⟨v, B⟩ ⟨some Sym.mark, Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update B sT t0) sA1 a10) sA2 a20) sX x0) sKI ki0)
      sONE one0⟩ (3 * bitLen d1.natAbs + 3 * bitLen d2.natAbs + 3 * bitLen k' + 21) := by
  refine Eval.of_eq (Eval.seq (dropInt_eval sA1 [] v d1 (Sym.mark :: a10) B (TermOK.cons (by rfl) _) hA1) <|
    Eval.seq (dropInt_eval sA2 [] _ d2 (Sym.mark :: a20) _ (TermOK.cons (by rfl) _)
      (by simpa using hA2)) <|
    Eval.seq (dropInt_eval sKI [] _ (k' : ℤ) (Sym.mark :: ki0) _ (TermOK.cons (by rfl) _)
      (by simpa using hKI)) <|
    Eval.seq (dropInt_eval sONE [] _ 1 (Sym.mark :: one0) _ (TermOK.cons (by rfl) _)
      (by simpa using hONE)) <|
    Eval.seq (eval_popR' [] sT _ _ Sym.mark t0 (by simpa using hT)) <|
    Eval.seq (eval_popR' [] sA1 _ _ Sym.mark a10 (by simp)) <|
    Eval.seq (eval_popR' [] sA2 _ _ Sym.mark a20 (by simp)) <|
    Eval.seq (eval_popR' [] sX _ _ Sym.mark x0 (by simpa using hX)) <|
    Eval.seq (eval_popR' [] sKI _ _ Sym.mark ki0 (by simp)) <|
    eval_popR' [] sONE _ _ Sym.mark one0 (by simp)) ?_ ?_
  · congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simp only [Int.natAbs_natCast, Int.natAbs_one, bitLen_one]
    omega

theorem lt_pow_of_bitLen {n w : ℕ} (h : bitLen n ≤ w) : n < 2 ^ w :=
  lt_of_lt_of_le (lt_two_pow_bitLen n) (Nat.pow_le_pow_right (by norm_num) h)

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := by
  refine bitLen_le_of_lt_two_pow ?_
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

theorem accOK_top (H k : ℕ) (L : List (ℤ × ℤ)) (hlen : L.length ≤ 2 ^ k)
    (hL : ∀ z ∈ L, bitLen z.1.natAbs ≤ H + 1 ∧ bitLen z.2.natAbs ≤ H + 1) :
    AccOK (H + k + 1) (0, 0) L := by
  intro i _
  have hB : ∀ z ∈ L.take i, z.1.natAbs ≤ 2 ^ (H + 1) - 1 ∧ z.2.natAbs ≤ 2 ^ (H + 1) - 1 := by
    intro z hz
    have h := hL z (List.mem_of_mem_take hz)
    have h1 := lt_pow_of_bitLen h.1
    have h2 := lt_pow_of_bitLen h.2
    omega
  obtain ⟨h1, h2⟩ := altAcc_natAbs_le (0, 0) (L.take i) (2 ^ (H + 1) - 1) hB
  have hti : (L.take i).length ≤ 2 ^ k := (List.length_take_le' _ _).trans hlen
  have hpk : 0 < 2 ^ k := by positivity
  have hpH : 0 < 2 ^ (H + 1) := by positivity
  have hm : (L.take i).length * (2 ^ (H + 1) - 1) ≤ 2 ^ k * (2 ^ (H + 1) - 1) :=
    Nat.mul_le_mul_right _ hti
  have he : 2 ^ k * (2 ^ (H + 1) - 1) = 2 ^ k * 2 ^ (H + 1) - 2 ^ k := Nat.mul_sub_one _ _
  have he2 : 2 ^ k * 2 ^ (H + 1) = 2 ^ (H + k + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hkey : (L.take i).length * (2 ^ (H + 1) - 1) < 2 ^ (H + k + 1) := by
    have : 2 ^ k ≤ 2 ^ k * 2 ^ (H + 1) := Nat.le_mul_of_pos_right _ hpH
    omega
  simp only [Int.natAbs_zero, zero_add] at h1 h2
  exact ⟨bitLen_le_of_lt_two_pow (lt_of_le_of_lt h1 hkey),
    bitLen_le_of_lt_two_pow (lt_of_le_of_lt h2 hkey)⟩

theorem diff_widths (H k k' : ℕ) (al a : ℤ) (hal : bitLen al.natAbs ≤ H)
    (ha : bitLen a.natAbs ≤ H + k + 1) :
    bitLen al.natAbs ≤ H + k + 3 ∧ bitLen a.natAbs ≤ H + k + 3 ∧
      bitLen (al - a).natAbs ≤ H + k + 3 ∧ bitLen ((al - a) >>> k').natAbs ≤ H + k + 3 ∧
      bitLen ((al - a) >>> k' + 1).natAbs ≤ H + k + 3 ∧
      bitLen (((al - a) >>> k' + 1) >>> 1).natAbs ≤ H + k + 3 := by
  have h1 := lt_pow_of_bitLen hal
  have h2 := lt_pow_of_bitLen ha
  have hx : (al - a).natAbs < 2 ^ (H + k + 2) := by
    have := Int.natAbs_sub_le al a
    have e1 : 2 ^ H ≤ 2 ^ (H + k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e2 : 2 ^ (H + k + 2) = 2 * 2 ^ (H + k + 1) := by rw [pow_succ]; ring
    omega
  have hy : ((al - a) >>> k').natAbs < 2 ^ (H + k + 2) :=
    lt_of_le_of_lt (natAbs_shiftRight_le _ _) hx
  have hy1 : ((al - a) >>> k' + 1).natAbs < 2 ^ (H + k + 3) := by
    have := Int.natAbs_add_le ((al - a) >>> k') 1
    have e3 : 2 ^ (H + k + 3) = 2 * 2 ^ (H + k + 2) := by rw [pow_succ]; ring
    simp only [Int.natAbs_one] at this
    omega
  have hd : (((al - a) >>> k' + 1) >>> 1).natAbs < 2 ^ (H + k + 3) :=
    lt_of_le_of_lt (natAbs_shiftRight_le _ _) hy1
  refine ⟨by omega, by omega, ?_, ?_, bitLen_le_of_lt_two_pow hy1, bitLen_le_of_lt_two_pow hd⟩
  · exact (bitLen_le_of_lt_two_pow hx).trans (by omega)
  · exact (bitLen_le_of_lt_two_pow hy).trans (by omega)

theorem outList_natAbs (M1 M2 : ℕ) : ∀ (L : List (ℤ × ℤ)) (D : ℤ × ℤ),
    (∀ z ∈ L, z.1.natAbs ≤ M1 ∧ z.2.natAbs ≤ M1) → D.1.natAbs ≤ M2 → D.2.natAbs ≤ M2 →
    ∀ o ∈ outList D L, o.1.natAbs ≤ M1 + M2 ∧ o.2.natAbs ≤ M1 + M2
  | [], _, _, _, _ => by simp [outList]
  | z :: L, D, hL, h1, h2 => by
    intro o ho
    simp only [outList, List.mem_cons] at ho
    rcases ho with rfl | ho
    · have := hL z (List.mem_cons_self ..)
      exact ⟨(Int.natAbs_add_le _ _).trans (by omega), (Int.natAbs_add_le _ _).trans (by omega)⟩
    · exact outList_natAbs M1 M2 L (-D.1, -D.2) (fun y hy => hL y (List.mem_cons_of_mem _ hy))
        (by simpa using h1) (by simpa using h2) o ho

theorem blkE_length_le (w : ℕ) : ∀ xs : List (ℤ × ℤ),
    (∀ o ∈ xs, bitLen o.1.natAbs ≤ w ∧ bitLen o.2.natAbs ≤ w) →
    (blkE xs).length ≤ xs.length * (2 * w + 4)
  | [], _ => by simp [WP.W9fM.blkE_nil]
  | o :: xs, h => by
    rw [WP.W9fM.blkE_cons, List.length_append, List.length_cons, add_mul, one_mul]
    have ho := h o (List.mem_cons_self ..)
    have ih := blkE_length_le w xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have he : (entrySyms o).length = bitLen o.1.natAbs + bitLen o.2.natAbs + 4 := by
      simp [entrySyms, length_intSyms]
      omega
    omega

#assert_std_axioms eval_popR' cleanup_eval lt_pow_of_bitLen bitLen_le_self accOK_top diff_widths
  outList_natAbs blkE_length_le

end WP.W9fNF
