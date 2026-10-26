import WP.W9fN.Epilogue

/-!
# WP.W9fN.NyqRun — the Nyquist core program and its run (`nyqProg_runs`)

`nyqProg I IF = prologue; zPart loop; finish (IF); pop ZS's mark; drop the variables`, over the
host `HK = Loc 8 48` with registers `GReg I × IF.R`.
-/

namespace WP.W9fN

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fN.IL IntMul IntMulTM.Contracts
  WP.W7k2

/-- The finish contract body for one instance (`W9f_nyqFinish` unfolded). -/
def FinSpec (IF : Inst 4 48 Unit) (CF : ℕ) : Prop :=
  ∀ (H k : ℕ) (alt : ℤ × ℤ) (Z : Array (ℤ × ℤ)) (rZ r2 r3 : List Sym) (S : Loc 4 IF.m → List Sym),
    Z.size = 2 ^ k → 1 ≤ k → ArrW (H + 1) Z → EntryW H alt →
    (∀ s, rZ.head? = some s → s ≠ Sym.pos ∧ s ≠ Sym.neg) → TermOK r2 →
    S (.inl 0) = blkE Z.toList.reverse ++ rZ → S (.inl 2) = natSyms k ++ r2 →
    S (.inl 3) = entrySyms alt ++ r3 →
    Runs IF.P S (Function.update (Function.update S (.inl 0) rZ) (.inl 1)
        (blkE (WP.W9f.nyqOut k alt Z).toList ++ S (.inl 1))) (fun _ => True)
      (CF * (Z.size * (H + k + 1) + (H + 1) ^ 2))

/-- The part after the loop. -/
def postProg (I : Op → OpImpl) (IF : Inst 4 48 Unit) : Prog HK (fun _ => Sym) (GReg I × IF.R) :=
  .seq (callI IF finNamed kTMP (Lens.snd _ _))
    (.seq ((hM I (popR kZS)).liftRegs (Lens.fst _ _))
      ((hM I (LN.dropVars V.all)).liftRegs (Lens.fst _ _)))

/-- **The Nyquist core.** -/
def nyqProg (I : Op → OpImpl) (IF : Inst 4 48 Unit) : Prog HK (fun _ => Sym) (GReg I × IF.R) :=
  .seq ((prologue I).liftRegs (Lens.fst _ _))
    (.seq ((inLoop I).liftRegs (Lens.fst _ _)) (postProg I IF))

/-- Total cost bound. -/
def nyqCost (C CF : ℕ) (Mul : ℕ → ℕ) (H k t1 : ℕ) : ℕ :=
  prologueCost C H + ((t1 - 1) * (bodyCost C Mul H + 2) + 2) +
    (CF * (t1 * (H + k + 1) + (H + 1) ^ 2) + 1 + dMax H)

/-- Final stacks of the contract. -/
def nyqFinal (S : HK → List Sym) (rIn : List Sym) (out : Array (ℤ × ℤ)) : HK → List Sym :=
  Function.update (Function.update S kIN rIn) kOUT (blkE out.toList ++ S kOUT)

theorem post_triple (I : Op → OpImpl) (IF : Inst 4 48 Unit) (CF : ℕ) (hF : FinSpec IF CF)
    (q H μ k : ℕ) (a : ℤ) (alt : ℤ × ℤ) (Ys : Array (ℤ × ℤ)) (rIn r5 r7 : List Sym)
    (S : HK → List Sym) (hsz : Ys.size = 2 ^ k) (hk : 1 ≤ k) (ha : 0 < a)
    (hμ : (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a) (halt : EntryW H alt)
    (hb : W8.zPartNyqBound q H a Ys (Ys.size - 1)) (hr5 : TermOK r5)
    (hS5 : S kPK = natSyms k ++ r5) (hS7 : S kPALT = entrySyms alt ++ r7) :
    Triple [] (fun s => LS q H μ a S Ys rIn (Ys.size - 1) s.stk) (postProg I IF)
      (fun s => s.stk = nyqFinal S rIn (WP.W9f.nyqOut k alt (W8.zPartNyqBarrett q H μ a Ys (Ys.size - 1))))
      (CF * (Ys.size * (H + k + 1) + (H + 1) ^ 2) + 1 + dMax H) := by
  rintro s ⟨env, hs, hI⟩
  have ht1 : 1 ≤ Ys.size := by
    rw [hsz]
    exact Nat.one_le_two_pow
  set Z := W8.zPartNyqBarrett q H (μ : ℤ) a Ys (Ys.size - 1) with hZ
  set X := Xn S Ys rIn Z (Ys.size - 1) with hX
  have hZsize : Z.size = 2 ^ k := by
    rw [hZ, WP.W9f.zPartNyqBarrett_size]
    omega
  have hZW : ArrW (H + 1) Z := by
    have h := WP.W9fW.zPartNyqBarrett_arrW q H a Ys (Ys.size - 1) ha hb
    rw [← hμ] at h
    exact h
  have hB0 : LN.hst S X env kZS = blkE Z.toList.reverse ++ (Sym.mark :: S kZS) := by
    rw [LN.hst_other S X env vL_ne_ZS, hX, Xn, Function.update_self]
  have hB2 : LN.hst S X env kPK = natSyms k ++ r5 := by
    rw [LN.hst_other S X env vL_ne_PK, hX, Xn, Function.update_of_ne (by simp [kPK, kZS]),
      Function.update_of_ne (by simp [kPK, kIN])]
    exact hS5
  have hB3 : LN.hst S X env kPALT = entrySyms alt ++ r7 := by
    rw [LN.hst_other S X env vL_ne_PALT, hX, Xn, Function.update_of_ne (by simp [kPALT, kZS]),
      Function.update_of_ne (by simp [kPALT, kIN])]
    exact hS7
  have f1 := finCall_runs IF CF hF (Lens.snd (GReg I) IF.R) (LN.hst S X env) H k alt Z
    (Sym.mark :: S kZS) r5 r7 hZsize hk hZW halt (notEntry_mark' _) hr5 hB0 hB2 hB3
  have hXo : X kOUT = S kOUT := by
    rw [hX, Xn, Function.update_of_ne (by simp [kOUT, kZS]),
      Function.update_of_ne (by simp [kOUT, kIN])]
  set out := WP.W9f.nyqOut k alt Z with hout
  set X3 := Function.update (Function.update X kZS (Sym.mark :: S kZS)) kOUT
    (blkE out.toList ++ S kOUT) with hX3
  have e1 : Function.update (Function.update (LN.hst S X env) kZS (Sym.mark :: S kZS)) kOUT
      (blkE out.toList ++ LN.hst S X env kOUT) = LN.hst S X3 env := by
    rw [LN.hst_other S X env vL_ne_OUT, hXo, LN.hst_upd_X S X env vL_ne_ZS,
      LN.hst_upd_X S _ env vL_ne_OUT]
  rw [e1] at f1
  have hX3z : X3 kZS = Sym.mark :: S kZS := by
    rw [hX3, Function.update_of_ne (by simp [kOUT, kZS]), Function.update_self]
  have f2 := RunsS.lift (Lens.fst (GReg I) IF.R) (LN.popR_runs I vL_ne_ZS S X3 env Sym.mark _ hX3z)
  set X4 := Function.update X3 kZS (S kZS) with hX4
  have f3 := RunsS.lift (Lens.fst (GReg I) IF.R) (LN.dropVars_runs I S X4 env)
  have hX4v : ∀ v, X4 (LN.varLoc v) = S (LN.varLoc v) := by
    intro v
    rw [hX4, Function.update_of_ne (vL_ne_ZS v), hX3, Function.update_of_ne (vL_ne_OUT v),
      Function.update_of_ne (vL_ne_ZS v), hX, Xn, Function.update_of_ne (vL_ne_ZS v),
      Function.update_of_ne (vL_ne_IN v)]
  rw [LN.hst0_eq S X4 hX4v] at f3
  have hfin : X4 = nyqFinal S rIn out := by
    have hdrop : Ys.toList.drop (Ys.size - 1 + 1) = [] := by
      rw [show Ys.size - 1 + 1 = Ys.size by omega]
      simp
    funext j
    rw [hX4, hX3, hX, nyqFinal]
    by_cases h1 : j = kZS
    · subst h1
      simp [kZS, kIN, kOUT]
    · by_cases h2 : j = kOUT
      · subst h2
        simp [kZS, kIN, kOUT]
      · by_cases h3 : j = kIN
        · subst h3
          simp [kZS, kIN, kOUT, Xn, hdrop, blkE, blk]
        · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3, Xn]
  have f3' := RunsS.of_eq f3 hfin le_rfl
  have hrun := HT.seq f1 (HT.seq f2 f3')
  obtain ⟨s', t, e, hs', ht⟩ := hrun s hs
  refine ⟨s', t, e, hs', ht.trans ?_⟩
  have hd := dCost_le env (WP.W9f.solW H) (fun v => (hI.w v).trans (βstep_le H v)) V.all
  rw [hZsize, ← hsz]
  unfold dMax
  omega

#assert_std_axioms post_triple

end WP.W9fN
