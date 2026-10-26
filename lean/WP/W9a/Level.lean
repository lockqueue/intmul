import WP.W9a.Basic

/-!
# WP.W9a.Level — the LEVEL driver (`W9_level`)

`lvlProg preP leafP postP` (registers `R × Option Sym`; the level programs run on the first
component, the tag register is the second):

1. peek `TR`; while the head is `symPre`: run `preP`, peek `TR`;
2. run `leafP`;
3. peek `TR`; while the head is `symPost`: run `postP`, peek `TR`.

The descent is an upward indexed loop (`Triple.loop_up`, invariant `A ℓ`), the ascent a counted
loop with the remaining depth as the index (`Triple.loop`, invariant `B n`). Cost: the level costs
plus `4D + 4 ≤ 2·(2D + 3)`.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

section LevelDef

variable {m : ℕ} {R : Type}

/-- The tag register holds `symPre`. -/
def isPreTag (v : R × Option Sym) : Bool := isSym symPre v.2

/-- The tag register holds `symPost`. -/
def isPostTag (v : R × Option Sym) : Bool := isSym symPost v.2

/-- **The level driver.** -/
def lvlProg (a b c : Prog (BLoc m) (fun _ => Sym) R) :
    Prog (BLoc m) (fun _ => Sym) (R × Option Sym) :=
  .seq (liftQ (peekR (.inl .TR)))
    (.seq (.loop isPreTag (.seq (liftK a) (liftQ (peekR (.inl .TR)))))
      (.seq (liftK b)
        (.seq (liftQ (peekR (.inl .TR)))
          (.loop isPostTag (.seq (liftK c) (liftQ (peekR (.inl .TR))))))))

theorem closed_lvlProg {a b c : Prog (BLoc m) (fun _ => Sym) R} (ha : a.Closed) (hb : b.Closed)
    (hc : c.Closed) : (lvlProg a b c).Closed :=
  closed_seq (closed_liftQ (closed_peekR _))
    (closed_seq (closed_loop (closed_seq (closed_liftK ha) (closed_liftQ (closed_peekR _))))
      (closed_seq (closed_liftK hb) (closed_seq (closed_liftQ (closed_peekR _))
        (closed_loop (closed_seq (closed_liftK hc) (closed_liftQ (closed_peekR _)))))))

end LevelDef

theorem loopCost_eq_sumTo (B : ℕ → ℕ) : ∀ N, loopCost B N = sumTo N B + N + 1
  | 0 => rfl
  | N + 1 => by
    rw [loopCost, loopCost_eq_sumTo B N, sumTo_succ]
    omega

theorem W9_level_holds : W9_level := by
  refine ⟨2, fun m R => ⟨Option Sym, lvlProg, inferInstance, ⟨none⟩,
    fun a b c ha hb hc => closed_lvlProg ha hb hc, ?_⟩⟩
  intro preP leafP postP D A B cPre cPost cLeaf hApre hAleaf hBpost hB0 hpre hleaf hpost σ hA0
  rintro ⟨⟨r, q⟩, S⟩ hs
  simp only at hs
  have hs' : σ = S := hs.symm
  subst hs'
  unfold lvlProg
  have e1 := Eval.peek (Γ := fun _ => Sym) [] (.inl .TR : BLoc m) (fun _ o => o) q σ
  -- descent
  have hdesc := Triple.loop_up
    (I := fun ℓ (s : St (BLoc m) (fun _ => Sym) (R × Option Sym)) =>
      A ℓ s.stk ∧ s.var.2 = (s.stk (.inl .TR)).head?)
    (B := fun ℓ => cPre ℓ + 1) (c := isPreTag) (ρ := [])
    (p := .seq (liftK preP) (liftQ (peekR (.inl .TR)))) D
    (by
      rintro ℓ hℓ ⟨⟨r', q'⟩, S'⟩ ⟨hA, -⟩
      obtain ⟨s2, t2, e2, hA2, ht2⟩ := hpre ℓ hℓ S' hA ⟨r', S'⟩ rfl
      have e3 := Eval.peek (Γ := fun _ => Sym) [] (.inl .TR : BLoc m) (fun _ o => o) q' s2.stk
      exact ⟨_, _, Eval.seq (liftK_eval e2 q') (liftQ_eval e3 (s2.var, q') rfl), ⟨hA2, rfl⟩,
        by show t2 + 1 ≤ cPre ℓ + 1; omega⟩)
    (by
      rintro ℓ hℓ s ⟨hA, hv⟩
      simp [isPreTag, isSym, hv, hApre ℓ hℓ s.stk hA])
    (by
      rintro s ⟨hA, hv⟩
      simp only [isPreTag, isSym, hv, hAleaf s.stk hA, Option.some.injEq, decide_eq_false_iff_not]
      decide)
  obtain ⟨sD, tD, eD, ⟨hAD, -⟩, htD⟩ := hdesc ⟨(r, (σ (.inl .TR)).head?), σ⟩ ⟨hA0, rfl⟩
  -- leaf
  obtain ⟨sL, tL, eL, hBD, htL⟩ := hleaf sD.stk hAD ⟨sD.var.1, sD.stk⟩ rfl
  have e2 := Eval.peek (Γ := fun _ => Sym) [] (.inl .TR : BLoc m) (fun _ o => o) sD.var.2 sL.stk
  -- ascent
  have hasc := Triple.loop
    (I := fun n (s : St (BLoc m) (fun _ => Sym) (R × Option Sym)) =>
      n ≤ D ∧ B n s.stk ∧ s.var.2 = (s.stk (.inl .TR)).head?)
    (B := fun n => cPost n + 1) (c := isPostTag) (ρ := [])
    (p := .seq (liftK postP) (liftQ (peekR (.inl .TR))))
    (by
      rintro n ⟨⟨r', q'⟩, S'⟩ ⟨hn, hB', -⟩
      obtain ⟨s2, t2, e2, hB2, ht2⟩ := hpost n (by omega) S' hB' ⟨r', S'⟩ rfl
      have e3 := Eval.peek (Γ := fun _ => Sym) [] (.inl .TR : BLoc m) (fun _ o => o) q' s2.stk
      exact ⟨_, _, Eval.seq (liftK_eval e2 q') (liftQ_eval e3 (s2.var, q') rfl),
        ⟨by omega, hB2, rfl⟩, by show t2 + 1 ≤ cPost n + 1; omega⟩)
    (by
      rintro n s ⟨hn, hB', hv⟩
      simp [isPostTag, isSym, hv, hBpost n (by omega) s.stk hB'])
    (by
      rintro s ⟨-, hB', hv⟩
      simp only [isPostTag, isSym, hv]
      exact decide_eq_false (hB0 s.stk hB')) D
  obtain ⟨sP, tP, eP, ⟨-, hBP, -⟩, htP⟩ := hasc ⟨(sL.var, (sL.stk (.inl .TR)).head?), sL.stk⟩
    ⟨le_rfl, hBD, rfl⟩
  refine ⟨sP, _, Eval.seq (liftQ_eval e1 (r, q) rfl) (Eval.seq eD (Eval.seq
    (liftK_eval eL sD.var.2) (Eval.seq (liftQ_eval e2 (sL.var, sD.var.2) rfl) eP))), hBP, ?_⟩
  rw [loopCost_eq_sumTo] at htP
  have h1 : sumTo D (fun ℓ => cPre ℓ + 1) = sumTo D cPre + D := by
    rw [sumTo_add, sumTo_const, Nat.mul_one]
  have h2 : sumTo D (fun n => cPost n + 1) = sumTo D cPost + D := by
    rw [sumTo_add, sumTo_const, Nat.mul_one]
  rw [h1] at htD
  rw [h2] at htP
  omega

#assert_std_axioms closed_lvlProg loopCost_eq_sumTo W9_level_holds

end WP.W9a
