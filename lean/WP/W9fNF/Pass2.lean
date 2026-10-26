import WP.W9fNF.Diff

/-!
# WP.W9fNF.Pass2 — pass 2: the outputs

`body2_eval`: one entry `z` on `T`, `D` on `A1`/`A2`: pushes the entry `z + D` onto `Z`, drops `z`
from `T`, negates `D`. `loop2_eval`: the whole block, by induction (`outList`).
-/

namespace WP.W9fNF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability WP.W6a

variable {κ : Kit} {Cs Ca Cn Cf : ℕ}

/-- `D` after a pass over a list: negated once per entry. -/
def dFin : List (ℤ × ℤ) → ℤ × ℤ → ℤ × ℤ
  | [], D => D
  | _ :: L, D => dFin L (-D.1, -D.2)

theorem dFin_natAbs : ∀ (L : List (ℤ × ℤ)) (D : ℤ × ℤ),
    (dFin L D).1.natAbs = D.1.natAbs ∧ (dFin L D).2.natAbs = D.2.natAbs
  | [], _ => ⟨rfl, rfl⟩
  | _ :: L, D => by
    obtain ⟨h1, h2⟩ := dFin_natAbs L (-D.1, -D.2)
    exact ⟨h1.trans (Int.natAbs_neg _), h2.trans (Int.natAbs_neg _)⟩

/-- A register-preserving macro on the first register component. -/
theorem liftM_eval_id {p : SProg FS} {S S' : FS → List Sym} {t : ℕ}
    (h : ∀ r, Eval [] p ⟨r, S⟩ ⟨r, S'⟩ t) (v : κ.Reg) :
    Eval [] (liftM κ p) ⟨v, S⟩ ⟨v, S'⟩ t :=
  liftFst (h v.1) v rfl

theorem body2_eval (hκ : κ.OK Cs Ca Cn Cf) (W : ℕ) (z D : ℤ × ℤ) (restT ra1 ra2 : List Sym)
    (B : FS → List Sym) (hra1 : TermOK ra1) (hra2 : TermOK ra2)
    (hT : B sT = entrySyms z ++ restT) (hA1 : B sA1 = intSyms D.1 ++ ra1)
    (hA2 : B sA2 = intSyms D.2 ++ ra2) (hw1 : bitLen z.1.natAbs ≤ W)
    (hw2 : bitLen z.2.natAbs ≤ W) (hw3 : bitLen D.1.natAbs ≤ W) (hw4 : bitLen D.2.natAbs ≤ W)
    (v : κ.Reg) :
    ∃ w t, Eval [] (body2 κ) ⟨v, B⟩ ⟨w, Function.update (Function.update (Function.update
        (Function.update B sT restT) sZ (entrySyms (z.1 + D.1, z.2 + D.2) ++ B sZ)) sA1
        (intSyms (-D.1) ++ ra1)) sA2 (intSyms (-D.2) ++ ra2)⟩ t ∧ w.1 = restT.head? ∧
      t ≤ (4 * Ca + 2 * Cn + 40) * (W + 1) := by
  have hs1 : ∀ x ∈ intSyms z.1, x ≠ Sym.sep ∧ x ≠ Sym.sep2 ∧ x ≠ Sym.mark :=
    fun _ hx => mem_intSyms hx
  have hs2 : ∀ x ∈ intSyms z.2, x ≠ Sym.sep ∧ x ≠ Sym.sep2 ∧ x ≠ Sym.mark :=
    fun _ hx => mem_intSyms hx
  have hT1 : B sT = intSyms z.1 ++ (Sym.sep2 :: (intSyms z.2 ++ Sym.sep :: restT)) := by
    rw [hT, entrySyms_split]
  -- 1. Z := sep :: Z
  have e1 := liftM_eval_id (κ := κ) (fun r => eval_pushC' [] sZ Sym.sep r B (B sZ) rfl) v
  obtain ⟨B1, hB1⟩ : ∃ X, X = Function.update B sZ (Sym.sep :: B sZ) := ⟨_, rfl⟩
  rw [← hB1] at e1
  -- 2. peel T
  have e2 := liftM_eval (κ := κ) (fun r => peel_eval (src := sT) (t := sP) (by decide) [] r
    (intSyms z.1) (intSyms z.2 ++ Sym.sep :: restT) B1 (fun x hx => (hs1 x hx).2.1)
    (by rw [hB1, Function.update_of_ne (by decide)]; exact hT1)) v
  have hB1P : B1 sP = B sP := by rw [hB1, Function.update_of_ne (by decide)]
  rw [hB1P] at e2
  obtain ⟨B2, hB2⟩ : ∃ X, X = Function.update (Function.update B1 sT
      (intSyms z.2 ++ Sym.sep :: restT)) sP
      ((intSyms z.1 ++ [Sym.sep2]).reverse ++ Sym.mark :: B sP) := ⟨_, rfl⟩
  rw [← hB2] at e2
  -- 3. Z += z.2 + D.2
  obtain ⟨w3, t3, e3, ht3⟩ := callAdd_eval hκ tri_T_A2_Z z.2 D.2 (Sym.sep :: restT) ra2 B2
    (TermOK.cons (by rfl) _) hra2 (by rw [hB2]; simp)
    (by rw [hB2, hB1]; simpa using hA2) (some Sym.sep2, v.2)
  have hB2Z : B2 sZ = Sym.sep :: B sZ := by rw [hB2, hB1]; simp
  rw [hB2Z] at e3
  obtain ⟨B3, hB3⟩ : ∃ X, X = Function.update B2 sZ (intSyms (z.2 + D.2) ++ Sym.sep :: B sZ) :=
    ⟨_, rfl⟩
  rw [← hB3] at e3
  -- 4. unpeel P → T
  have hl : ∀ x ∈ (intSyms z.1 ++ [Sym.sep2]).reverse, x ≠ Sym.mark := by
    intro x hx
    simp only [List.mem_reverse, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact (hs1 x hx).2.2
    · decide
  have e4 := liftM_eval (κ := κ) (fun r => stageB_eval (t := sP) (dst := sT) (by decide) [] r
    ((intSyms z.1 ++ [Sym.sep2]).reverse) (B sP) B3 hl
    (by rw [hB3, hB2]; simp)) w3
  have hB3T : B3 sT = intSyms z.2 ++ Sym.sep :: restT := by
    rw [hB3, hB2]; simp
  rw [hB3T, List.reverse_reverse] at e4
  obtain ⟨B4, hB4⟩ : ∃ X, X = Function.update (Function.update B3 sP (B sP)) sT
      (intSyms z.1 ++ [Sym.sep2] ++ (intSyms z.2 ++ Sym.sep :: restT)) := ⟨_, rfl⟩
  rw [← hB4] at e4
  -- 5. Z := sep2 :: Z
  have hB4Z : B4 sZ = intSyms (z.2 + D.2) ++ Sym.sep :: B sZ := by
    rw [hB4, hB3]; simp
  have e5 := liftM_eval_id (κ := κ) (fun r => eval_pushC' [] sZ Sym.sep2 r B4
    (intSyms (z.2 + D.2) ++ Sym.sep :: B sZ) hB4Z) (some Sym.mark, w3.2)
  obtain ⟨B5, hB5⟩ : ∃ X, X = Function.update B4 sZ
      (Sym.sep2 :: (intSyms (z.2 + D.2) ++ Sym.sep :: B sZ)) := ⟨_, rfl⟩
  rw [← hB5] at e5
  -- 6. Z += z.1 + D.1
  have hB5T : B5 sT = intSyms z.1 ++ (Sym.sep2 :: (intSyms z.2 ++ Sym.sep :: restT)) := by
    rw [hB5, hB4]
    simp
  obtain ⟨w6, t6, e6, ht6⟩ := callAdd_eval hκ tri_T_A1_Z z.1 D.1
    (Sym.sep2 :: (intSyms z.2 ++ Sym.sep :: restT)) ra1 B5
    (TermOK.cons (by rfl) _) hra1 hB5T
    (by rw [hB5, hB4, hB3, hB2, hB1]; simpa using hA1)
    (some Sym.mark, w3.2)
  have hB5Z : B5 sZ = Sym.sep2 :: (intSyms (z.2 + D.2) ++ Sym.sep :: B sZ) := by
    rw [hB5, Function.update_self]
  rw [hB5Z] at e6
  obtain ⟨B6, hB6⟩ : ∃ X, X = Function.update B5 sZ
      (intSyms (z.1 + D.1) ++ Sym.sep2 :: (intSyms (z.2 + D.2) ++ Sym.sep :: B sZ)) := ⟨_, rfl⟩
  rw [← hB6] at e6
  -- 7. drop the entry from T
  have hd7 : ∀ x ∈ intSyms z.1 ++ Sym.sep2 :: intSyms z.2, x ≠ Sym.sep := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact (hs1 x hx).1
    · decide
    · exact (hs2 x hx).1
  have e7 := liftM_eval (κ := κ) (fun r => dropUntil_eval Sym.sep sT [] r
    (intSyms z.1 ++ Sym.sep2 :: intSyms z.2) restT B6 hd7
    (by rw [hB6, Function.update_of_ne (by decide), hB5T]; simp)) w6
  obtain ⟨B7, hB7⟩ : ∃ X, X = Function.update B6 sT restT := ⟨_, rfl⟩
  rw [← hB7] at e7
  -- 8, 9. D := -D
  have hB7A1 : B7 sA1 = intSyms D.1 ++ ra1 := by
    rw [hB7, hB6, hB5, hB4, hB3, hB2, hB1]
    simpa using hA1
  obtain ⟨w8, t8, e8, ht8⟩ := callNeg_eval hκ (notPool_inr _ (by decide)) D.1 ra1 B7 hra1 hB7A1
    (some Sym.sep, w6.2)
  obtain ⟨B8, hB8⟩ : ∃ X, X = Function.update B7 sA1 (intSyms (-D.1) ++ ra1) := ⟨_, rfl⟩
  rw [← hB8] at e8
  have hB8A2 : B8 sA2 = intSyms D.2 ++ ra2 := by
    rw [hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1]
    simpa using hA2
  obtain ⟨w9, t9, e9, ht9⟩ := callNeg_eval hκ (notPool_inr _ (by decide)) D.2 ra2 B8 hra2 hB8A2 w8
  obtain ⟨B9, hB9⟩ : ∃ X, X = Function.update B8 sA2 (intSyms (-D.2) ++ ra2) := ⟨_, rfl⟩
  rw [← hB9] at e9
  -- 10. look at the next symbol of T
  have e10 := liftM_eval (κ := κ) (fun r => Eval.peek [] sT (fun _ o => o) r B9) w9
  have hfin : B9 = Function.update (Function.update (Function.update (Function.update B sT restT)
      sZ (entrySyms (z.1 + D.1, z.2 + D.2) ++ B sZ)) sA1 (intSyms (-D.1) ++ ra1)) sA2
      (intSyms (-D.2) ++ ra2) := by
    clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    rw [hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all [entrySyms_split]
  refine ⟨_, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 e10))))))))).of_eq (by rw [hfin]) rfl,
    by simp, ?_⟩
  have h3 : t3 ≤ 2 * (Ca * (W + 1)) := by
    refine ht3.trans ?_
    calc Ca * (bitLen z.2.natAbs + bitLen D.2.natAbs + 1) ≤ Ca * (2 * (W + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (Ca * (W + 1)) := by ring
  have h6 : t6 ≤ 2 * (Ca * (W + 1)) := by
    refine ht6.trans ?_
    calc Ca * (bitLen z.1.natAbs + bitLen D.1.natAbs + 1) ≤ Ca * (2 * (W + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (Ca * (W + 1)) := by ring
  have h89 : Cn ≤ Cn * (W + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hE : (4 * Ca + 2 * Cn + 40) * (W + 1) =
      4 * (Ca * (W + 1)) + 2 * (Cn * (W + 1)) + 40 * (W + 1) := by ring
  rw [hE]
  simp only [List.length_reverse, List.length_append, List.length_cons, List.length_nil,
    length_intSyms]
  generalize Ca * (W + 1) = M1 at h3 h6 ⊢
  generalize Cn * (W + 1) = M2 at h89 ⊢
  omega

theorem loop2_eval (hκ : κ.OK Cs Ca Cn Cf) (W : ℕ) (restT ra1 ra2 : List Sym)
    (hrest : WP.W9f.NotEntry restT) (hra1 : TermOK ra1) (hra2 : TermOK ra2) :
    ∀ (L : List (ℤ × ℤ)) (D : ℤ × ℤ) (B : FS → List Sym) (v : κ.Reg),
      (∀ z ∈ L, bitLen z.1.natAbs ≤ W ∧ bitLen z.2.natAbs ≤ W) →
      bitLen D.1.natAbs ≤ W → bitLen D.2.natAbs ≤ W →
      B sT = blkE L ++ restT → B sA1 = intSyms D.1 ++ ra1 → B sA2 = intSyms D.2 ++ ra2 →
      v.1 = (blkE L ++ restT).head? →
      ∃ w t, Eval [] (.loop (isSgnR κ) (body2 κ)) ⟨v, B⟩
        ⟨w, Function.update (Function.update (Function.update (Function.update B sT restT) sZ
          (blkE (outList D L).reverse ++ B sZ)) sA1 (intSyms (dFin L D).1 ++ ra1))
          sA2 (intSyms (dFin L D).2 ++ ra2)⟩ t ∧
        t ≤ L.length * ((4 * Ca + 2 * Cn + 40) * (W + 1) + 1) + 1
  | [], D, B, v, _, _, _, hT, hA1, hA2, hv => by
    refine ⟨v, 1, (Eval.loop_false ?_).of_eq ?_ rfl, by simp⟩
    · show WP.W9fM.isSgn v.1 = false
      rw [hv]
      exact WP.W9fM.isSgn_of_notEntry restT hrest
    · have hT' : B sT = restT := hT
      congr 1
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all [outList, dFin, WP.W9fM.blkE_nil]
  | z :: L, D, B, v, hL, hd1, hd2, hT, hA1, hA2, hv => by
    obtain ⟨hz1, hz2⟩ := hL z (List.mem_cons_self ..)
    have hT' : B sT = entrySyms z ++ (blkE L ++ restT) := by
      rw [hT, WP.W9fM.blkE_cons, List.append_assoc]
    obtain ⟨w1, t1, e1, hw1, ht1⟩ := body2_eval hκ W z D (blkE L ++ restT) ra1 ra2 B hra1 hra2
      hT' hA1 hA2 hz1 hz2 hd1 hd2 v
    obtain ⟨B1, hB1⟩ : ∃ X, X = Function.update (Function.update (Function.update
        (Function.update B sT (blkE L ++ restT)) sZ (entrySyms (z.1 + D.1, z.2 + D.2) ++ B sZ))
        sA1 (intSyms (-D.1) ++ ra1)) sA2 (intSyms (-D.2) ++ ra2) := ⟨_, rfl⟩
    rw [← hB1] at e1
    obtain ⟨w2, t2, e2, ht2⟩ := loop2_eval hκ W restT ra1 ra2 hrest hra1 hra2 L (-D.1, -D.2) B1
      w1 (fun y hy => hL y (List.mem_cons_of_mem _ hy)) (by simpa using hd1) (by simpa using hd2)
      (by rw [hB1]; simp) (by rw [hB1]; simp) (by rw [hB1]; simp) hw1
    refine ⟨w2, t1 + t2 + 1, (Eval.loop_true ?_ e1 e2).of_eq ?_ rfl, ?_⟩
    · show WP.W9fM.isSgn v.1 = true
      rw [hv, WP.W9fM.blkE_cons, List.append_assoc]
      exact WP.W9fM.isSgn_entry z _
    · congr 1
      clear e1 e2
      rw [hB1]
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all [outList, dFin, List.reverse_cons, WP.W9fM.blkE_append,
        WP.W9fM.blkE_cons, WP.W9fM.blkE_nil]
    · rw [List.length_cons, add_mul, one_mul]
      generalize L.length * ((4 * Ca + 2 * Cn + 40) * (W + 1) + 1) = P at ht2 ⊢
      omega

#assert_std_axioms dFin_natAbs liftM_eval_id body2_eval loop2_eval

end WP.W9fNF
