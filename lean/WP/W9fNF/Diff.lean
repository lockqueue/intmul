import WP.W9fNF.Pass1

/-!
# WP.W9fNF.Diff — the rounded difference `D = ((alt - A) >>> (k - 1) + 1) >>> 1`

`diffCoord_eval`: one coordinate, on the accumulator stack `Aj` (which ends up holding `D_j`).
`diff_eval`: both coordinates; the second one is exposed on `AL` by `peel` and restored by
`stageB`.
-/

namespace WP.W9fNF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability WP.W6a

variable {κ : Kit} {Cs Ca Cn Cf : ℕ}

theorem bitLen_one : bitLen 1 = 1 := by
  simpa [bitLen_zero] using bitLen_add_add_one 0

theorem diffCoord_eval (hκ : κ.OK Cs Ca Cn Cf) {Aj : FS} (hAX : Aj ≠ sX) (hAAL : Aj ≠ sAL)
    (hAKI : Aj ≠ sKI) (hAONE : Aj ≠ sONE) (hAp : NotPool Aj) (W2 k' : ℕ) (al a : ℤ)
    (ral raj rx rki rone : List Sym) (B : FS → List Sym) (hral : TermOK ral) (hraj : TermOK raj)
    (hrx : TermOK rx) (hrki : TermOK rki) (hrone : TermOK rone)
    (hAL : B sAL = intSyms al ++ ral) (hA : B Aj = intSyms a ++ raj) (hX : B sX = rx)
    (hKI : B sKI = intSyms k' ++ rki) (hONE : B sONE = intSyms 1 ++ rone)
    (hw1 : bitLen al.natAbs ≤ W2) (hw2 : bitLen a.natAbs ≤ W2)
    (hw3 : bitLen (al - a).natAbs ≤ W2) (hw4 : bitLen ((al - a) >>> k').natAbs ≤ W2)
    (hw5 : bitLen ((al - a) >>> k' + 1).natAbs ≤ W2) (hw6 : bitLen k' ≤ W2) (v : κ.Reg) :
    ∃ w t, Eval [] (diffCoord κ Aj) ⟨v, B⟩
      ⟨w, Function.update B Aj (intSyms (((al - a) >>> k' + 1) >>> 1) ++ raj)⟩ t ∧
      t ≤ (2 * Cs + 2 * Ca + 4 * Cf + 20) * (W2 + 1) := by
  have hXA : sX ≠ Aj := Ne.symm hAX
  -- 1. X += al - a
  obtain ⟨w1, t1, e1, ht1⟩ := callSub_eval hκ ⟨Ne.symm hAAL, by decide, hAX, notPool_inl _, hAp,
    notPool_inr _ (by decide)⟩ al a ral raj B hral hraj hAL hA v
  rw [hX] at e1
  obtain ⟨B1, hB1⟩ : ∃ X, X = Function.update B sX (intSyms (al - a) ++ rx) := ⟨_, rfl⟩
  rw [← hB1] at e1
  -- 2. drop A
  have e2 := liftM_eval (κ := κ) (fun r => dropInt_eval Aj [] r a raj B1 hraj
    (by rw [hB1, Function.update_of_ne hAX]; exact hA)) w1
  obtain ⟨B2, hB2⟩ : ∃ X, X = Function.update B1 Aj raj := ⟨_, rfl⟩
  rw [← hB2] at e2
  -- 3. A += x >>> (k - 1)
  have hB2X : B2 sX = intSyms (al - a) ++ rx := by
    rw [hB2, Function.update_of_ne hXA, hB1, Function.update_self]
  have hB2KI : B2 sKI = intSyms k' ++ rki := by
    rw [hB2, Function.update_of_ne (Ne.symm hAKI), hB1, Function.update_of_ne (by decide)]
    exact hKI
  obtain ⟨w3, t3, e3, ht3⟩ := callShr_eval hκ (tri_X_KI_A Aj hXA (Ne.symm hAKI) hAp) (al - a)
    k' rx rki B2 hrx hrki (by rw [hB2, Function.update_self]; exact hraj) hB2X hB2KI
    (raj.head?, w1.2)
  have hB2A : B2 Aj = raj := by rw [hB2, Function.update_self]
  rw [Int.natAbs_natCast, hB2A] at e3
  rw [Int.natAbs_natCast] at ht3
  obtain ⟨B3, hB3⟩ : ∃ X, X = Function.update B2 Aj (intSyms ((al - a) >>> k') ++ raj) :=
    ⟨_, rfl⟩
  rw [← hB3] at e3
  -- 4. drop X
  have e4 := liftM_eval (κ := κ) (fun r => dropInt_eval sX [] r (al - a) rx B3 hrx
    (by rw [hB3, Function.update_of_ne hXA]; exact hB2X)) w3
  obtain ⟨B4, hB4⟩ : ∃ X, X = Function.update B3 sX rx := ⟨_, rfl⟩
  rw [← hB4] at e4
  -- 5. X += y + 1
  have hB4A : B4 sAL = B sAL ∧ B4 Aj = intSyms ((al - a) >>> k') ++ raj ∧
      B4 sONE = intSyms 1 ++ rone := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hB4, Function.update_of_ne (by decide), hB3, Function.update_of_ne hAAL.symm, hB2,
        Function.update_of_ne hAAL.symm, hB1, Function.update_of_ne (by decide)]
    · rw [hB4, Function.update_of_ne hAX, hB3, Function.update_self]
    · rw [hB4, Function.update_of_ne (by decide), hB3, Function.update_of_ne hAONE.symm, hB2,
        Function.update_of_ne hAONE.symm, hB1, Function.update_of_ne (by decide)]
      exact hONE
  obtain ⟨w5, t5, e5, ht5⟩ := callAdd_eval hκ (tri_A_ONE_X Aj hAONE hAX hAp) ((al - a) >>> k') 1
    raj rone B4 hraj hrone hB4A.2.1 hB4A.2.2 (rx.head?, w3.2)
  have hB4X : B4 sX = rx := by rw [hB4, Function.update_self]
  rw [hB4X] at e5
  obtain ⟨B5, hB5⟩ : ∃ X, X = Function.update B4 sX (intSyms ((al - a) >>> k' + 1) ++ rx) :=
    ⟨_, rfl⟩
  rw [← hB5] at e5
  -- 6. drop A
  have e6 := liftM_eval (κ := κ) (fun r => dropInt_eval Aj [] r ((al - a) >>> k') raj B5 hraj
    (by rw [hB5, Function.update_of_ne hAX]; exact hB4A.2.1)) w5
  obtain ⟨B6, hB6⟩ : ∃ X, X = Function.update B5 Aj raj := ⟨_, rfl⟩
  rw [← hB6] at e6
  -- 7. A += (y + 1) >>> 1
  have hB6X : B6 sX = intSyms ((al - a) >>> k' + 1) ++ rx := by
    rw [hB6, Function.update_of_ne hXA, hB5, Function.update_self]
  have hB6ONE : B6 sONE = intSyms 1 ++ rone := by
    rw [hB6, Function.update_of_ne hAONE.symm, hB5, Function.update_of_ne (by decide)]
    exact hB4A.2.2
  obtain ⟨w7, t7, e7, ht7⟩ := callShr_eval hκ (tri_X_ONE_A Aj hXA hAONE.symm hAp)
    ((al - a) >>> k' + 1) 1 rx rone B6 hrx hrone (by rw [hB6, Function.update_self]; exact hraj)
    hB6X hB6ONE (raj.head?, w5.2)
  have hB6A : B6 Aj = raj := by rw [hB6, Function.update_self]
  rw [Int.natAbs_one, hB6A] at e7
  rw [Int.natAbs_one] at ht7
  obtain ⟨B7, hB7⟩ : ∃ X, X = Function.update B6 Aj
      (intSyms (((al - a) >>> k' + 1) >>> 1) ++ raj) := ⟨_, rfl⟩
  rw [← hB7] at e7
  -- 8. drop X
  have e8 := liftM_eval (κ := κ) (fun r => dropInt_eval sX [] r ((al - a) >>> k' + 1) rx B7 hrx
    (by rw [hB7, Function.update_of_ne hXA]; exact hB6X)) w7
  have hfin : Function.update B7 sX rx =
      Function.update B Aj (intSyms (((al - a) >>> k' + 1) >>> 1) ++ raj) := by
    clear e1 e2 e3 e4 e5 e6 e7 e8
    rw [hB7, hB6, hB5, hB4, hB3, hB2, hB1]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  refine ⟨_, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 e8))))))).of_eq (by rw [hfin]) rfl, ?_⟩
  have h1 : t1 ≤ 2 * (Cs * (W2 + 1)) := by
    refine ht1.trans ?_
    calc Cs * (bitLen al.natAbs + bitLen a.natAbs + 1) ≤ Cs * (2 * (W2 + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (Cs * (W2 + 1)) := by ring
  have h3 : t3 ≤ 2 * (Cf * (W2 + 1)) := by
    refine ht3.trans ?_
    calc Cf * (bitLen (al - a).natAbs + bitLen k' + 1) ≤ Cf * (2 * (W2 + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (Cf * (W2 + 1)) := by ring
  have h5 : t5 ≤ 2 * (Ca * (W2 + 1)) := by
    refine ht5.trans ?_
    rw [Int.natAbs_one, bitLen_one]
    calc Ca * (bitLen ((al - a) >>> k').natAbs + 1 + 1) ≤ Ca * (2 * (W2 + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (Ca * (W2 + 1)) := by ring
  have h7 : t7 ≤ 2 * (Cf * (W2 + 1)) := by
    refine ht7.trans ?_
    rw [bitLen_one]
    calc Cf * (bitLen ((al - a) >>> k' + 1).natAbs + 1 + 1) ≤ Cf * (2 * (W2 + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (Cf * (W2 + 1)) := by ring
  have hE : (2 * Cs + 2 * Ca + 4 * Cf + 20) * (W2 + 1) =
      2 * (Cs * (W2 + 1)) + 2 * (Ca * (W2 + 1)) + 4 * (Cf * (W2 + 1)) + 20 * (W2 + 1) := by ring
  rw [hE]
  generalize Cs * (W2 + 1) = M1 at h1 ⊢
  generalize Ca * (W2 + 1) = M2 at h5 ⊢
  generalize Cf * (W2 + 1) = M3 at h3 h7 ⊢
  omega

theorem diff_eval (hκ : κ.OK Cs Ca Cn Cf) (W2 k' : ℕ) (alt A : ℤ × ℤ)
    (r3 ra1 ra2 rx rki rone : List Sym) (B : FS → List Sym) (hra1 : TermOK ra1)
    (hra2 : TermOK ra2) (hrx : TermOK rx) (hrki : TermOK rki) (hrone : TermOK rone)
    (hAL : B sAL = entrySyms alt ++ r3) (hA1 : B sA1 = intSyms A.1 ++ ra1)
    (hA2 : B sA2 = intSyms A.2 ++ ra2) (hX : B sX = rx) (hKI : B sKI = intSyms k' ++ rki)
    (hONE : B sONE = intSyms 1 ++ rone)
    (hw11 : bitLen alt.1.natAbs ≤ W2) (hw12 : bitLen A.1.natAbs ≤ W2)
    (hw13 : bitLen (alt.1 - A.1).natAbs ≤ W2) (hw14 : bitLen ((alt.1 - A.1) >>> k').natAbs ≤ W2)
    (hw15 : bitLen ((alt.1 - A.1) >>> k' + 1).natAbs ≤ W2)
    (hw21 : bitLen alt.2.natAbs ≤ W2) (hw22 : bitLen A.2.natAbs ≤ W2)
    (hw23 : bitLen (alt.2 - A.2).natAbs ≤ W2) (hw24 : bitLen ((alt.2 - A.2) >>> k').natAbs ≤ W2)
    (hw25 : bitLen ((alt.2 - A.2) >>> k' + 1).natAbs ≤ W2) (hw6 : bitLen k' ≤ W2) (v : κ.Reg) :
    ∃ w t, Eval [] (diff κ) ⟨v, B⟩ ⟨w, Function.update (Function.update B
        sA1 (intSyms (((alt.1 - A.1) >>> k' + 1) >>> 1) ++ ra1))
        sA2 (intSyms (((alt.2 - A.2) >>> k' + 1) >>> 1) ++ ra2)⟩ t ∧
      t ≤ 2 * ((2 * Cs + 2 * Ca + 4 * Cf + 20) * (W2 + 1)) + 7 * W2 + 20 := by
  have hs1 : ∀ x ∈ intSyms alt.1, x ≠ Sym.sep ∧ x ≠ Sym.sep2 ∧ x ≠ Sym.mark :=
    fun _ hx => mem_intSyms hx
  have hAL1 : B sAL = intSyms alt.1 ++ (Sym.sep2 :: (intSyms alt.2 ++ Sym.sep :: r3)) := by
    rw [hAL, entrySyms_split]
  -- 1. first coordinate
  obtain ⟨w1, t1, e1, ht1⟩ := diffCoord_eval hκ (Aj := sA1) (by decide) (by decide) (by decide)
    (by decide) (notPool_inr _ (by decide)) W2 k' alt.1 A.1 _ ra1 rx rki rone B
    (TermOK.cons (by rfl) _) hra1 hrx hrki hrone hAL1 hA1 hX hKI hONE hw11 hw12 hw13 hw14 hw15 hw6
    v
  obtain ⟨B1, hB1⟩ : ∃ X, X = Function.update B sA1
      (intSyms (((alt.1 - A.1) >>> k' + 1) >>> 1) ++ ra1) := ⟨_, rfl⟩
  rw [← hB1] at e1
  -- 2. peel AL
  have e2 := liftM_eval (κ := κ) (fun r => peel_eval (src := sAL) (t := sP) (by decide) [] r
    (intSyms alt.1) (intSyms alt.2 ++ Sym.sep :: r3) B1 (fun x hx => (hs1 x hx).2.1)
    (by rw [hB1, Function.update_of_ne (by decide)]; exact hAL1)) w1
  have hB1P : B1 sP = B sP := by rw [hB1, Function.update_of_ne (by decide)]
  rw [hB1P] at e2
  obtain ⟨B2, hB2⟩ : ∃ X, X = Function.update (Function.update B1 sAL
      (intSyms alt.2 ++ Sym.sep :: r3)) sP
      ((intSyms alt.1 ++ [Sym.sep2]).reverse ++ Sym.mark :: B sP) := ⟨_, rfl⟩
  rw [← hB2] at e2
  -- 3. second coordinate
  obtain ⟨w3, t3, e3, ht3⟩ := diffCoord_eval hκ (Aj := sA2) (by decide) (by decide) (by decide)
    (by decide) (notPool_inr _ (by decide)) W2 k' alt.2 A.2 (Sym.sep :: r3) ra2 rx rki rone B2
    (TermOK.cons (by rfl) _) hra2 hrx hrki hrone (by rw [hB2]; simp)
    (by rw [hB2, hB1]; simpa using hA2) (by rw [hB2, hB1]; simpa using hX)
    (by rw [hB2, hB1]; simpa using hKI) (by rw [hB2, hB1]; simpa using hONE)
    hw21 hw22 hw23 hw24 hw25 hw6 (some Sym.sep2, w1.2)
  obtain ⟨B3, hB3⟩ : ∃ X, X = Function.update B2 sA2
      (intSyms (((alt.2 - A.2) >>> k' + 1) >>> 1) ++ ra2) := ⟨_, rfl⟩
  rw [← hB3] at e3
  -- 4. restore AL
  have hl : ∀ x ∈ (intSyms alt.1 ++ [Sym.sep2]).reverse, x ≠ Sym.mark := by
    intro x hx
    simp only [List.mem_reverse, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact (hs1 x hx).2.2
    · decide
  have e4 := liftM_eval (κ := κ) (fun r => stageB_eval (t := sP) (dst := sAL) (by decide) [] r
    ((intSyms alt.1 ++ [Sym.sep2]).reverse) (B sP) B3 hl (by rw [hB3, hB2]; simp)) w3
  have hfin : Function.update (Function.update B3 sP (B sP)) sAL
      ((intSyms alt.1 ++ [Sym.sep2]).reverse.reverse ++ B3 sAL) =
      Function.update (Function.update B sA1 (intSyms (((alt.1 - A.1) >>> k' + 1) >>> 1) ++ ra1))
        sA2 (intSyms (((alt.2 - A.2) >>> k' + 1) >>> 1) ++ ra2) := by
    clear e1 e2 e3 e4
    have hB3AL : B3 sAL = intSyms alt.2 ++ Sym.sep :: r3 := by rw [hB3, hB2]; simp
    rw [hB3AL, List.reverse_reverse, hB3, hB2, hB1]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all [entrySyms_split]
  refine ⟨_, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq (by rw [hfin]) rfl, ?_⟩
  simp only [List.length_reverse, List.length_append, List.length_singleton, length_intSyms]
  omega

#assert_std_axioms bitLen_one diffCoord_eval diff_eval

end WP.W9fNF
