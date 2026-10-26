import WP.W9fN.NyqRun

/-!
# WP.W9fN.NyqComp — the whole run (`nyqProg_runs`) and the cost bound (`nyqCost_le`)
-/

namespace WP.W9fN

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fN.IL IntMul IntMulTM.Contracts
  WP.W7k2

/-- **The Nyquist core runs** from the contract's input stacks to its output stacks. -/
theorem nyqProg_runs (I : Op → OpImpl) (C : ℕ) (Mul : ℕ → ℕ) (IF : Inst 4 48 Unit) (CF : ℕ)
    (hF : FinSpec IF CF) (q H μ k : ℕ) (a : ℤ) (alt : ℤ × ℤ) (Ys : Array (ℤ × ℤ))
    (rIn r2 r3 r4 r5 r6 r7 : List Sym) (S : HK → List Sym)
    (hok : ∀ o, BinOK (I o) (Op.sem o) (kap C Mul (WP.W9f.solW H) o))
    (hsz : Ys.size = 2 ^ k) (hk : 1 ≤ k) (hqH : q + 2 ≤ H) (ha : 0 < a)
    (hμ : (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a) (haW : bitLen a.natAbs ≤ H) (hY : ArrW H Ys)
    (halt : EntryW H alt) (hb : W8.zPartNyqBound q H a Ys (Ys.size - 1))
    (hrIn : WP.W9f.NotEntry rIn) (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4)
    (hr5 : TermOK r5) (hr6 : TermOK r6)
    (hS0 : S kIN = blkE Ys.toList ++ rIn) (hS2 : S kPQ = natSyms q ++ r2)
    (hS3 : S kPH = natSyms H ++ r3) (hS4 : S kPMU = natSyms μ ++ r4)
    (hS5 : S kPK = natSyms k ++ r5) (hS6 : S kPA = intSyms a ++ r6)
    (hS7 : S kPALT = entrySyms alt ++ r7) :
    Runs (nyqProg I IF) S (nyqFinal S rIn (W8.solveNyqBarrett q H Ys.size k μ a Ys alt))
      (fun _ => True) (nyqCost C CF Mul H k Ys.size) := by
  have ht1 : 1 ≤ Ys.size := by
    rw [hsz]
    exact Nat.one_le_two_pow
  obtain ⟨Sx0, hLS0, hpro⟩ := prologue_runs I C Mul q H μ a hok S Ys rIn r2 r3 r4 r6 ht1 hqH
    hμ haW hY hr2 hr3 hr4 hr6 hS0 hS2 hS3 hS4 hS6
  have p1 : Triple [] (fun s => s.stk = S) ((prologue I).liftRegs (Lens.fst (GReg I) IF.R))
      (fun s => LS q H μ a S Ys rIn 0 s.stk) (prologueCost C H) := by
    refine Triple.post (RunsS.lift (Lens.fst (GReg I) IF.R) hpro) (fun s hs => ?_)
    have hs' : s.stk = Sx0 := hs
    rw [hs']
    exact hLS0
  have p2 := tripleS_lift (Lens.fst (GReg I) IF.R)
    (inLoop_triple I C Mul q H μ a hok S Ys rIn ha hμ hY hb hrIn ht1)
  have p3 := post_triple I IF CF hF q H μ k a alt Ys rIn r5 r7 S hsz hk ha hμ halt hb hr5 hS5 hS7
  have h := Triple.seq p1 (Triple.seq p2 p3)
  rw [WP.W9f.solveNyqBarrett_eq_nyqOut q H Ys.size k μ a Ys alt ht1]
  refine (Triple.post h (fun s hs => ⟨hs, trivial⟩)).cost_mono ?_
  unfold nyqCost
  omega

/-- **Cost bound** in the contract's shape. -/
theorem nyqCost_le (C CF : ℕ) (Mul : ℕ → ℕ) (H k t1 : ℕ) (ht1 : 1 ≤ t1) :
    nyqCost C CF Mul H k t1 ≤
      (10000 * (C + 1) + CF) * (t1 * (Mul (WP.W9f.solW H) + H + k + 1) + (H + 1) ^ 2) := by
  set M := Mul (WP.W9f.solW H) with hM
  set X := t1 * (M + H + k + 1) + (H + 1) ^ 2 with hX
  have hlen : V.all.length = 31 := rfl
  have hW : WP.W9f.solW H = 8 * H + 8 := by unfold WP.W9f.solW; ring
  have hsq : H + 1 ≤ (H + 1) ^ 2 := by nlinarith
  have hHX : H + 1 ≤ X := by omega
  have hTM : t1 * M ≤ X := by
    have : t1 * M ≤ t1 * (M + H + k + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hTH : t1 * (H + 1) ≤ X := by
    have : t1 * (H + 1) ≤ t1 * (M + H + k + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hD : t1 * (H + k + 1) + (H + 1) ^ 2 ≤ X := by
    have : t1 * (H + k + 1) ≤ t1 * (M + H + k + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  -- prologue
  have hA : prologueCost C H ≤ 449 * (C + 1) * X := by
    have e1 : prologueCost C H = (C + 1) * (40 * H + 250) + (46 * H + 199) := by
      unfold prologueCost
      rw [hlen]
      ring
    have e2 : 46 * H + 199 ≤ (C + 1) * (46 * H + 199) := Nat.le_mul_of_pos_left _ (by omega)
    have e3 : (C + 1) * (40 * H + 250) + (C + 1) * (46 * H + 199) ≤ (C + 1) * (449 * (H + 1)) := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left _ (by omega)
    have e4 : (C + 1) * (449 * (H + 1)) ≤ (C + 1) * (449 * X) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hHX)
    have e5 : (C + 1) * (449 * X) = 449 * (C + 1) * X := by ring
    omega
  -- loop
  have hB0 : bodyCost C Mul H + 2 ≤ 10 * (C * M) + 7002 * ((C + 1) * (H + 1)) := by
    have e1 : bodyCost C Mul H + 2 =
        10 * (C * M) + 418 * C + 384 * (C * H) + 5476 * H + 6990 := by
      unfold bodyCost
      rw [← hM, hW]
      ring
    have e2 : (C + 1) * (H + 1) = C * H + C + H + 1 := by ring
    rw [e1, e2]
    omega
  have hB1 : (t1 - 1) * (bodyCost C Mul H + 2) ≤ t1 * (bodyCost C Mul H + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have hB2 : t1 * (bodyCost C Mul H + 2) ≤ 10 * C * X + 7002 * (C + 1) * X := by
    have e1 : t1 * (bodyCost C Mul H + 2) ≤ t1 * (10 * (C * M) + 7002 * ((C + 1) * (H + 1))) :=
      Nat.mul_le_mul_left _ hB0
    have e2 : t1 * (10 * (C * M) + 7002 * ((C + 1) * (H + 1))) =
        10 * C * (t1 * M) + 7002 * (C + 1) * (t1 * (H + 1)) := by ring
    have e3 : 10 * C * (t1 * M) ≤ 10 * C * X := Nat.mul_le_mul_left _ hTM
    have e4 : 7002 * (C + 1) * (t1 * (H + 1)) ≤ 7002 * (C + 1) * X := Nat.mul_le_mul_left _ hTH
    omega
  -- finish and cleanup
  have hC : CF * (t1 * (H + k + 1) + (H + 1) ^ 2) ≤ CF * X := Nat.mul_le_mul_left _ hD
  have hE : 1 + dMax H ≤ 700 * X := by
    have e1 : 1 + dMax H = 496 * H + 684 := by
      unfold dMax
      rw [hlen, hW]
      ring
    omega
  have hsum : 449 * (C + 1) * X + (10 * C * X + 7002 * (C + 1) * X + 2 * X) + CF * X + 700 * X ≤
      (10000 * (C + 1) + CF) * X := by
    have e : 449 * (C + 1) * X + (10 * C * X + 7002 * (C + 1) * X + 2 * X) + CF * X + 700 * X =
        (449 * (C + 1) + 10 * C + 7002 * (C + 1) + 2 + CF + 700) * X := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ (by omega)
  unfold nyqCost
  have h2X : 2 ≤ 2 * X := by omega
  omega

#assert_std_axioms nyqProg_runs nyqCost_le

end WP.W9fN
