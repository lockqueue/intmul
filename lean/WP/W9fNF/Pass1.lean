import WP.W9fNF.Setup
import WP.W9fNF.Pure

/-!
# WP.W9fNF.Pass1 — pass 1: the alternating sum

`body1_eval`: one entry `z` on `Z`, accumulator `a` on `A1`/`A2`: afterwards `A = altStep a z`, the
entry is on `T`, `Z` holds the rest, the register holds the next symbol of `Z`.
`loop1_eval`: the whole block, by induction.
-/

namespace WP.W9fNF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability WP.W6a

variable {κ : Kit} {Cs Ca Cn Cf : ℕ}

theorem entrySyms_split (z : ℤ × ℤ) (rest : List Sym) :
    entrySyms z ++ rest = intSyms z.1 ++ (Sym.sep2 :: (intSyms z.2 ++ Sym.sep :: rest)) := by
  simp [entrySyms]

theorem length_intSyms (z : ℤ) : (intSyms z).length = bitLen z.natAbs + 1 := by
  simp [intSyms, length_natSyms]

theorem body1_eval (hκ : κ.OK Cs Ca Cn Cf) (W : ℕ) (z a : ℤ × ℤ) (rest ra1 ra2 rx : List Sym)
    (B : FS → List Sym) (hra1 : TermOK ra1) (hra2 : TermOK ra2) (hrx : TermOK rx)
    (hZ : B sZ = entrySyms z ++ rest) (hA1 : B sA1 = intSyms a.1 ++ ra1)
    (hA2 : B sA2 = intSyms a.2 ++ ra2) (hX : B sX = rx)
    (hw1 : bitLen z.1.natAbs ≤ W) (hw2 : bitLen z.2.natAbs ≤ W) (hw3 : bitLen a.1.natAbs ≤ W)
    (hw4 : bitLen a.2.natAbs ≤ W) (hw5 : bitLen (z.1 - a.1).natAbs ≤ W)
    (hw6 : bitLen (z.2 - a.2).natAbs ≤ W) (v : κ.Reg) :
    ∃ w t, Eval [] (body1 κ) ⟨v, B⟩ ⟨w, Function.update (Function.update (Function.update
        (Function.update B sZ rest) sT (entrySyms z ++ B sT)) sA1 (intSyms (z.1 - a.1) ++ ra1))
        sA2 (intSyms (z.2 - a.2) ++ ra2)⟩ t ∧ w.1 = rest.head? ∧
      t ≤ (4 * Cs + 100) * (W + 1) := by
  have hs1 : ∀ x ∈ intSyms z.1, x ≠ Sym.sep ∧ x ≠ Sym.sep2 ∧ x ≠ Sym.mark :=
    fun _ hx => mem_intSyms hx
  have hs2 : ∀ x ∈ intSyms z.2, x ≠ Sym.sep ∧ x ≠ Sym.sep2 ∧ x ≠ Sym.mark :=
    fun _ hx => mem_intSyms hx
  have hZ1 : B sZ = intSyms z.1 ++ (Sym.sep2 :: (intSyms z.2 ++ Sym.sep :: rest)) := by
    rw [hZ, entrySyms_split]
  -- 1. X += z.1 - a.1
  obtain ⟨w1, t1, e1, ht1⟩ := callSub_eval hκ tri_Z_A1_X z.1 a.1 _ ra1 B
    (TermOK.cons (by rfl) _) hra1 hZ1 hA1 v
  rw [hX] at e1
  obtain ⟨B1, hB1⟩ : ∃ X, X = Function.update B sX (intSyms (z.1 - a.1) ++ rx) := ⟨_, rfl⟩
  rw [← hB1] at e1
  -- 2. A1 := X
  have e2 := liftM_eval (κ := κ) (fun r => replInt_eval (src := sX) (dst := sA1) (t := sM)
    (by decide) (by decide) (by decide) [] r a.1 (z.1 - a.1) ra1 rx B1 hra1 hrx
    (by rw [hB1, Function.update_of_ne (by decide)]; exact hA1)
    (by rw [hB1, Function.update_self])) w1
  obtain ⟨B2, hB2⟩ : ∃ X, X = Function.update (Function.update B1 sX rx) sA1
      (intSyms (z.1 - a.1) ++ ra1) := ⟨_, rfl⟩
  rw [← hB2] at e2
  have hB2Z : B2 sZ = intSyms z.1 ++ (Sym.sep2 :: (intSyms z.2 ++ Sym.sep :: rest)) := by
    rw [hB2, hB1]
    simpa using hZ1
  have hB2P : B2 sP = B sP := by
    rw [hB2, hB1]
    simp
  -- 3. peel Z
  have e3 := liftM_eval (κ := κ) (fun r => peel_eval (src := sZ) (t := sP) (by decide) [] r
    (intSyms z.1) (intSyms z.2 ++ Sym.sep :: rest) B2 (fun x hx => (hs1 x hx).2.1) hB2Z)
    (some Sym.mark, w1.2)
  rw [hB2P] at e3
  obtain ⟨B3, hB3⟩ : ∃ X, X = Function.update (Function.update B2 sZ
      (intSyms z.2 ++ Sym.sep :: rest)) sP
      ((intSyms z.1 ++ [Sym.sep2]).reverse ++ Sym.mark :: B sP) := ⟨_, rfl⟩
  rw [← hB3] at e3
  -- 4. X += z.2 - a.2
  have hB3X : B3 sX = rx := by
    rw [hB3, hB2]
    simp
  obtain ⟨w4, t4, e4, ht4⟩ := callSub_eval hκ tri_Z_A2_X z.2 a.2 (Sym.sep :: rest) ra2 B3
    (TermOK.cons (by rfl) _) hra2 (by rw [hB3]; simp)
    (by rw [hB3, hB2, hB1]; simpa using hA2) (some Sym.sep2, w1.2)
  rw [hB3X] at e4
  obtain ⟨B4, hB4⟩ : ∃ X, X = Function.update B3 sX (intSyms (z.2 - a.2) ++ rx) := ⟨_, rfl⟩
  rw [← hB4] at e4
  -- 5. A2 := X
  have e5 := liftM_eval (κ := κ) (fun r => replInt_eval (src := sX) (dst := sA2) (t := sM)
    (by decide) (by decide) (by decide) [] r a.2 (z.2 - a.2) ra2 rx B4 hra2 hrx
    (by rw [hB4, hB3, hB2, hB1]; simpa using hA2)
    (by rw [hB4, Function.update_self])) w4
  obtain ⟨B5, hB5⟩ : ∃ X, X = Function.update (Function.update B4 sX rx) sA2
      (intSyms (z.2 - a.2) ++ ra2) := ⟨_, rfl⟩
  rw [← hB5] at e5
  -- 6. unpeel P → Z
  have hl : ∀ x ∈ (intSyms z.1 ++ [Sym.sep2]).reverse, x ≠ Sym.mark := by
    intro x hx
    simp only [List.mem_reverse, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact (hs1 x hx).2.2
    · decide
  have hB5Z : B5 sZ = intSyms z.2 ++ Sym.sep :: rest := by
    rw [hB5, hB4, hB3]
    simp
  have e6 := liftM_eval (κ := κ) (fun r => stageB_eval (t := sP) (dst := sZ) (by decide) [] r
    ((intSyms z.1 ++ [Sym.sep2]).reverse) (B sP) B5 hl
    (by rw [hB5, hB4, hB3]; simp)) (some Sym.mark, w4.2)
  rw [hB5Z, List.reverse_reverse] at e6
  obtain ⟨B6, hB6⟩ : ∃ X, X = Function.update (Function.update B5 sP (B sP)) sZ
      (intSyms z.1 ++ [Sym.sep2] ++ (intSyms z.2 ++ Sym.sep :: rest)) := ⟨_, rfl⟩
  rw [← hB6] at e6
  -- 7. move the entry Z → T
  have hd7 : ∀ x ∈ intSyms z.1 ++ Sym.sep2 :: intSyms z.2, x ≠ Sym.sep ∧ x ≠ Sym.mark := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact ⟨(hs1 x hx).1, (hs1 x hx).2.2⟩
    · decide
    · exact ⟨(hs2 x hx).1, (hs2 x hx).2.2⟩
  have hB6T : B6 sT = B sT := by
    rw [hB6, hB5, hB4, hB3, hB2, hB1]
    simp
  have e7 := liftM_eval (κ := κ) (fun r => moveOne_eval (src := sZ) (dst := sT) (t := sM)
    (by decide) (by decide) (by decide) [] r (intSyms z.1 ++ Sym.sep2 :: intSyms z.2) rest B6 hd7
    (by rw [hB6]; simp)) (some Sym.mark, w4.2)
  rw [hB6T] at e7
  obtain ⟨B7, hB7⟩ : ∃ X, X = Function.update (Function.update B6 sZ rest) sT
      ((intSyms z.1 ++ Sym.sep2 :: intSyms z.2) ++ Sym.sep :: B sT) := ⟨_, rfl⟩
  rw [← hB7] at e7
  -- 8. look at the next symbol of Z
  have e8 := liftM_eval (κ := κ) (fun r => Eval.peek [] sZ (fun _ o => o) r B7)
    (some Sym.mark, w4.2)
  have hfin : B7 = Function.update (Function.update (Function.update (Function.update B sZ rest)
      sT (entrySyms z ++ B sT)) sA1 (intSyms (z.1 - a.1) ++ ra1)) sA2
      (intSyms (z.2 - a.2) ++ ra2) := by
    clear e1 e2 e3 e4 e5 e6 e7 e8
    rw [hB7, hB6, hB5, hB4, hB3, hB2, hB1]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all [entrySyms_split]
  refine ⟨_, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 e8))))))).of_eq (by rw [hfin]) rfl, by simp, ?_⟩
  have hM1 : t1 ≤ 2 * (Cs * (W + 1)) := by
    refine ht1.trans ?_
    calc Cs * (bitLen z.1.natAbs + bitLen a.1.natAbs + 1) ≤ Cs * (2 * (W + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (Cs * (W + 1)) := by ring
  have hM4 : t4 ≤ 2 * (Cs * (W + 1)) := by
    refine ht4.trans ?_
    calc Cs * (bitLen z.2.natAbs + bitLen a.2.natAbs + 1) ≤ Cs * (2 * (W + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (Cs * (W + 1)) := by ring
  have hE : (4 * Cs + 100) * (W + 1) = 4 * (Cs * (W + 1)) + 100 * (W + 1) := by ring
  rw [hE]
  simp only [List.length_reverse, List.length_append, List.length_cons, List.length_nil,
    length_intSyms]
  generalize Cs * (W + 1) = M at hM1 hM4 ⊢
  omega

/-- Bit lengths along the pass-1 recurrence. -/
def AccOK (W : ℕ) (A : ℤ × ℤ) (L : List (ℤ × ℤ)) : Prop :=
  ∀ i ≤ L.length, bitLen (altAcc A (L.take i)).1.natAbs ≤ W ∧
    bitLen (altAcc A (L.take i)).2.natAbs ≤ W

theorem loop1_eval (hκ : κ.OK Cs Ca Cn Cf) (W : ℕ) (rest ra1 ra2 rx : List Sym)
    (hrest : WP.W9f.NotEntry rest) (hra1 : TermOK ra1) (hra2 : TermOK ra2) (hrx : TermOK rx) :
    ∀ (L : List (ℤ × ℤ)) (A : ℤ × ℤ) (B : FS → List Sym) (v : κ.Reg),
      (∀ z ∈ L, bitLen z.1.natAbs ≤ W ∧ bitLen z.2.natAbs ≤ W) → AccOK W A L →
      B sZ = blkE L ++ rest → B sA1 = intSyms A.1 ++ ra1 → B sA2 = intSyms A.2 ++ ra2 →
      B sX = rx → v.1 = (blkE L ++ rest).head? →
      ∃ w t, Eval [] (.loop (isSgnR κ) (body1 κ)) ⟨v, B⟩
        ⟨w, Function.update (Function.update (Function.update (Function.update B sZ rest) sT
          (blkE L.reverse ++ B sT)) sA1 (intSyms (altAcc A L).1 ++ ra1))
          sA2 (intSyms (altAcc A L).2 ++ ra2)⟩ t ∧
        t ≤ L.length * ((4 * Cs + 100) * (W + 1) + 1) + 1
  | [], A, B, v, _, _, hZ, hA1, hA2, _, hv => by
    refine ⟨v, 1, (Eval.loop_false ?_).of_eq ?_ rfl, by simp⟩
    · show WP.W9fM.isSgn v.1 = false
      rw [hv]
      exact WP.W9fM.isSgn_of_notEntry rest hrest
    · have hZ' : B sZ = rest := hZ
      congr 1
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all [altAcc, WP.W9fM.blkE_nil]
  | z :: L, A, B, v, hL, hAcc, hZ, hA1, hA2, hX, hv => by
    obtain ⟨hz1, hz2⟩ := hL z (List.mem_cons_self ..)
    obtain ⟨ha1, ha2⟩ := hAcc 0 (Nat.zero_le _)
    obtain ⟨hn1, hn2⟩ := hAcc 1 (by simp)
    simp only [List.take_zero, altAcc] at ha1 ha2
    simp only [List.take_succ_cons, List.take_zero, altAcc, altStep] at hn1 hn2
    have hZ' : B sZ = entrySyms z ++ (blkE L ++ rest) := by
      rw [hZ, WP.W9fM.blkE_cons, List.append_assoc]
    obtain ⟨w1, t1, e1, hw1, ht1⟩ := body1_eval hκ W z A (blkE L ++ rest) ra1 ra2 rx B hra1 hra2
      hrx hZ' hA1 hA2 hX hz1 hz2 ha1 ha2 hn1 hn2 v
    obtain ⟨B1, hB1⟩ : ∃ X, X = Function.update (Function.update (Function.update
        (Function.update B sZ (blkE L ++ rest)) sT (entrySyms z ++ B sT)) sA1
        (intSyms (z.1 - A.1) ++ ra1)) sA2 (intSyms (z.2 - A.2) ++ ra2) := ⟨_, rfl⟩
    rw [← hB1] at e1
    obtain ⟨w2, t2, e2, ht2⟩ := loop1_eval hκ W rest ra1 ra2 rx hrest hra1 hra2 hrx L
      (altStep A z) B1 w1 (fun y hy => hL y (List.mem_cons_of_mem _ hy))
      (fun i hi => by
        have := hAcc (i + 1) (by simp only [List.length_cons]; omega)
        simpa only [List.take_succ_cons, altAcc] using this)
      (by rw [hB1]; simp) (by rw [hB1]; simp [altStep])
      (by rw [hB1]; simp [altStep]) (by rw [hB1]; simp [hX]) hw1
    refine ⟨w2, t1 + t2 + 1, (Eval.loop_true ?_ e1 e2).of_eq ?_ rfl, ?_⟩
    · show WP.W9fM.isSgn v.1 = true
      rw [hv, WP.W9fM.blkE_cons, List.append_assoc]
      exact WP.W9fM.isSgn_entry z _
    · congr 1
      clear e1 e2
      rw [hB1]
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all [altAcc, List.reverse_cons, WP.W9fM.blkE_append, WP.W9fM.blkE_cons,
        WP.W9fM.blkE_nil]
    · rw [List.length_cons, add_mul, one_mul]
      generalize L.length * ((4 * Cs + 100) * (W + 1) + 1) = P at ht2 ⊢
      omega

#assert_std_axioms entrySyms_split length_intSyms body1_eval loop1_eval

end WP.W9fNF
