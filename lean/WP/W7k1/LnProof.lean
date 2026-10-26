import WP.W7k1.LnDefs
import WP.W7k1.LnBounds
import WP.W7k1.PiProof

/-!
# WP.W7k1.LnProof — correctness and cost of the `ln 2` kernel's phases

`lnSetup_spec`, `lnBody_spec`, `lnLoop_spec`, `lnFinal_spec`, `lnClean_spec`: exact host states
(`lnSt`) through the program, each step a contract call charged at most `lnU K B`
(`WP.W7k1.LnBounds`).
-/

namespace WP.W7k1

open TMFw TMFw.Contracts WP.W7k2 Computability

/-! ## Setup -/

theorem lnSetup_spec (J : LnInst) {K : ℕ} (hJ : J.Spec K) (hK : 1 ≤ K) (B : ℕ) (rB : List Sym)
    (S : PL → List Sym) (hrB : TermOK rB) (hB : S (.inl 0) = natSyms B ++ rB) :
    HT [] S (lnSetup J)
      (lnSt S (natSyms (2 ^ (3 * B + 11)) ++ .mark :: S (.inr 0)) (.mark :: S (.inr 1))
        (natSyms (2 ^ (3 * B + 11) + 1 + 1) ++ .mark :: S (.inr 2))
        (natSyms 4 ++ .mark :: S (.inr 3)) (natSyms (B + 2) ++ .mark :: S (.inr 4))
        (.mark :: S (.inr 5)) (.mark :: S (.inr 6)) (S (.inl 1)))
      (29 * lnU K B) := by
  have hy : (B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + B + 1 = 3 * B + 11 := by ring
  have hA0 : bitLen (1 * 2 ^ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + B + 1)) ≤ 8 * B + 44 := by
    rw [hy, one_mul, WP.W7k2.bitLen_two_pow]
    omega
  have hA1 : bitLen (1 * 2 ^ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + B + 1) + 1) ≤ 8 * B + 44 := by
    rw [hy, one_mul]
    refine piwp (k := 3 * B + 12) ?_ (by omega)
    have : 1 ≤ 2 ^ (3 * B + 11) := Nat.one_le_two_pow
    have e : 2 ^ (3 * B + 12) = 2 ^ (3 * B + 11) + 2 ^ (3 * B + 11) := by ring
    omega
  apply HT.mono
  · unfold lnSetup
    refine HT.seq ((HT.pushS (.inr 5) .mark _ []).of_eq (lnSt_init ..) (lnU_one B hK)) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.l0 (.inl 0) (.inr 5) (by decide) (by norm_num) _ B rB hrB
        (by simp [hB]) []).of_eq (by rw [lnSt_5, lnSt_upd5]) (lnU_lin B (piw (by omega)))) <|
      HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 5) (by norm_num) _ B (.mark :: S (.inr 5))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd5 ..) (lnU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 5) (by norm_num) _ (B + 1) (.mark :: S (.inr 5))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd5 ..) (lnU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 5) (by norm_num) _ (B + 1 + 1) (.mark :: S (.inr 5))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd5 ..) (lnU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 5) (by norm_num) _ (B + 1 + 1 + 1)
        (.mark :: S (.inr 5)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd5 ..)
        (lnU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 5) (by norm_num) _ (B + 1 + 1 + 1 + 1)
        (.mark :: S (.inr 5)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd5 ..)
        (lnU_inc B (piw (by omega)))) <| HT.seq
      ((HT.shlConst hJ.shl1 (.inl 0) J.l2 (.inr 5) (by norm_num) _ (B + 1 + 1 + 1 + 1 + 1)
        (.mark :: S (.inr 5)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd5 ..) (lnU_k1 B)) <|
      HT.seq
      ((HT.pushS (.inr 6) .mark _ []).of_eq (by rw [lnSt_6, lnSt_upd6]) (lnU_one B hK)) <| HT.seq
      ((HT.addNat hJ.add (.inl 0) J.l4 (.inr 5) (.inl 0) (.inr 6) (by decide) (by norm_num) _
        ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1) B (.mark :: S (.inr 5)) rB (termOK_mark _) hrB
        (by simp) (by simp [hB]) []).of_eq (by rw [lnSt_6, lnSt_upd6])
        (lnU_two B (piw (by omega)) (piw (by omega)))) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 5) (by norm_num) _
        ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1) (.mark :: S (.inr 5)) (termOK_mark _) (by simp)
        []).of_eq (lnSt_upd5 ..) (lnU_lin B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 6) (by norm_num) _
        ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + B) (.mark :: S (.inr 6)) (termOK_mark _) (by simp)
        []).of_eq (lnSt_upd6 ..) (lnU_inc B (piw (by omega)))) <| HT.seq
      ((HT.pushS (.inr 0) .mark _ []).of_eq (by rw [lnSt_0, lnSt_upd0]) (lnU_one B hK)) <| HT.seq
      ((HT.pushS (.inr 0) (.bit true) _ []).of_eq (by rw [lnSt_0, lnSt_upd0]) (lnU_one B hK)) <|
      HT.seq
      ((HT.shlVar hJ.shlV (.inl 0) J.l3 (.inr 0) (.inr 6) (by decide) (by norm_num) _ 1
        ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + B + 1) (.mark :: S (.inr 0)) (.mark :: S (.inr 6))
        (termOK_mark _) (termOK_mark _) (by simp [natSyms_one']) (by simp) []).of_eq
        (lnSt_upd0 ..) (lnU_shl B (by omega))) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 6) (by norm_num) _
        ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + B + 1) (.mark :: S (.inr 6)) (termOK_mark _) (by simp)
        []).of_eq (lnSt_upd6 ..) (lnU_lin B (piw (by omega)))) <| HT.seq
      ((HT.pushS (.inr 2) .mark _ []).of_eq (by rw [lnSt_2, lnSt_upd2]) (lnU_one B hK)) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.l0 (.inr 0) (.inr 2) (by decide) (by norm_num) _
        (1 * 2 ^ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + B + 1)) (.mark :: S (.inr 0)) (termOK_mark _)
        (by simp) []).of_eq (by rw [lnSt_2, lnSt_upd2]) (lnU_lin B hA0)) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 2) (by norm_num) _
        (1 * 2 ^ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + B + 1)) (.mark :: S (.inr 2)) (termOK_mark _)
        (by simp) []).of_eq (lnSt_upd2 ..) (lnU_inc B hA0)) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 2) (by norm_num) _
        (1 * 2 ^ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + B + 1) + 1) (.mark :: S (.inr 2))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd2 ..) (lnU_inc B hA1)) <| HT.seq
      ((HT.pushS (.inr 3) .mark _ []).of_eq (by rw [lnSt_3, lnSt_upd3]) (lnU_one B hK)) <| HT.seq
      ((HT.pushS (.inr 3) (.bit true) _ []).of_eq (by rw [lnSt_3, lnSt_upd3]) (lnU_one B hK)) <|
      HT.seq
      ((HT.shlConst hJ.shl1 (.inl 0) J.l2 (.inr 3) (by norm_num) _ 1 (.mark :: S (.inr 3))
        (termOK_mark _) (by simp [natSyms_one']) []).of_eq (lnSt_upd3 ..) (lnU_k1 B)) <| HT.seq
      ((HT.shlConst hJ.shl1 (.inl 0) J.l2 (.inr 3) (by norm_num) _ (1 * 2 ^ 1)
        (.mark :: S (.inr 3)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd3 ..) (lnU_k1 B)) <|
      HT.seq
      ((HT.pushS (.inr 1) .mark _ []).of_eq (by rw [lnSt_1, lnSt_upd1]) (lnU_one B hK)) <| HT.seq
      ((HT.pushS (.inr 4) .mark _ []).of_eq (by rw [lnSt_4, lnSt_upd4]) (lnU_one B hK)) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.l0 (.inl 0) (.inr 4) (by decide) (by norm_num) _ B rB hrB
        (by simp [hB]) []).of_eq (by rw [lnSt_4, lnSt_upd4]) (lnU_lin B (piw (by omega)))) <|
      HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ B (.mark :: S (.inr 4))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd4 ..) (lnU_inc B (piw (by omega))))
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1) (.mark :: S (.inr 4))
        (termOK_mark _) (by simp) []).of_eq ?_ (lnU_inc B (piw (by omega))))
    rw [lnSt_upd4, hy, show (1 : ℕ) * 2 ^ 1 * 2 ^ 1 = 4 by norm_num,
      show (1 : ℕ) * 2 ^ (3 * B + 11) = 2 ^ (3 * B + 11) by ring, show B + 1 + 1 = B + 2 by ring]
  · by_contra hc
    omega

/-! ## The loop body and the loop -/

theorem lnBody_spec (J : LnInst) {K : ℕ} (hJ : J.Spec K) (B : ℕ) (S : PL → List Sym)
    (a s X D : ℕ) (hD : 0 < D) (hsa : bitLen (s + a) ≤ 8 * B + 44)
    (hXD : bitLen (X + D) ≤ 8 * B + 44) (hD2 : bitLen (D + 2) ≤ 8 * B + 44) (v4 : List Sym) :
    HT [] (lnSt S (natSyms a ++ .mark :: S (.inr 0)) (natSyms s ++ .mark :: S (.inr 1))
        (natSyms X ++ .mark :: S (.inr 2)) (natSyms D ++ .mark :: S (.inr 3)) v4
        (.mark :: S (.inr 5)) (.mark :: S (.inr 6)) (S (.inl 1))) (lnBody J)
      (lnSt S (natSyms (X / D) ++ .mark :: S (.inr 0)) (natSyms (s + a) ++ .mark :: S (.inr 1))
        (natSyms ((X - X % D + D) / 2 ^ 1 + 1) ++ .mark :: S (.inr 2))
        (natSyms (D + 1 + 1) ++ .mark :: S (.inr 3)) v4
        (.mark :: S (.inr 5)) (.mark :: S (.inr 6)) (S (.inl 1)))
      (15 * lnU K B) := by
  have hs : bitLen s ≤ 8 * B + 44 := le_trans (WP.W7k2.bitLen_mono (Nat.le_add_right s a)) hsa
  have ha : bitLen a ≤ 8 * B + 44 := le_trans (WP.W7k2.bitLen_mono (Nat.le_add_left a s)) hsa
  have hX : bitLen X ≤ 8 * B + 44 := le_trans (WP.W7k2.bitLen_mono (Nat.le_add_right X D)) hXD
  have hDw : bitLen D ≤ 8 * B + 44 := le_trans (WP.W7k2.bitLen_mono (Nat.le_add_left D X)) hXD
  have hr : bitLen (X % D) ≤ 8 * B + 44 := le_trans (WP.W7k2.bitLen_mono (Nat.mod_le X D)) hX
  have hXr : bitLen (X - X % D) ≤ 8 * B + 44 :=
    le_trans (WP.W7k2.bitLen_mono (Nat.sub_le X _)) hX
  have hY : bitLen ((X - X % D + D) / 2 ^ 1) ≤ 8 * B + 44 :=
    le_trans (WP.W7k2.bitLen_mono (le_trans (Nat.div_le_self _ _) (by omega))) hXD
  have hD1 : bitLen (D + 1) ≤ 8 * B + 44 := le_trans (WP.W7k2.bitLen_mono (by omega)) hD2
  apply HT.mono
  · unfold lnBody
    refine HT.seq
      ((HT.addNat hJ.add (.inl 0) J.l4 (.inr 1) (.inr 0) (.inr 6) (by decide) (by norm_num) _ s a
        (.mark :: S (.inr 1)) (.mark :: S (.inr 0)) (termOK_mark _) (termOK_mark _) (by simp)
        (by simp) []).of_eq (by rw [lnSt_6, lnSt_upd6]) (lnU_two B hs ha)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 1) (by norm_num) _ s (.mark :: S (.inr 1))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd1 ..) (lnU_lin B hs)) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.l0 (.inr 6) (.inr 1) (by decide) (by norm_num) _ (s + a)
        (.mark :: S (.inr 6)) (termOK_mark _) (by simp) []).of_eq (by rw [lnSt_1, lnSt_upd1])
        (lnU_lin B hsa)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 6) (by norm_num) _ (s + a) (.mark :: S (.inr 6))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd6 ..) (lnU_lin B hsa)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 0) (by norm_num) _ a (.mark :: S (.inr 0))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd0 ..) (lnU_lin B ha)) <| HT.seq
      ((HT.divModNat hJ.div (.inl 0) J.l11 (.inr 2) (.inr 3) (.inr 0) (.inr 5) (by decide)
        (by norm_num) _ X D (.mark :: S (.inr 2)) (.mark :: S (.inr 3)) hD (termOK_mark _)
        (termOK_mark _) (by simp) (by simp) []).of_eq
        (by rw [lnSt_0, lnSt_upd0, lnSt_5, lnSt_upd5]) (lnU_dm B hX hDw)) <| HT.seq
      ((HT.subNat hJ.sub (.inl 0) J.l5 (.inr 2) (.inr 5) (.inr 6) (by decide) (by norm_num) _ X
        (X % D) (.mark :: S (.inr 2)) (.mark :: S (.inr 5)) (termOK_mark _) (termOK_mark _)
        (Nat.mod_le X D) (by simp) (by simp) []).of_eq (by rw [lnSt_6, lnSt_upd6])
        (lnU_two B hX hr)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 2) (by norm_num) _ X (.mark :: S (.inr 2))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd2 ..) (lnU_lin B hX)) <| HT.seq
      ((HT.addNat hJ.add (.inl 0) J.l4 (.inr 6) (.inr 3) (.inr 2) (by decide) (by norm_num) _
        (X - X % D) D (.mark :: S (.inr 6)) (.mark :: S (.inr 3)) (termOK_mark _) (termOK_mark _)
        (by simp) (by simp) []).of_eq (by rw [lnSt_2, lnSt_upd2]) (lnU_two B hXr hDw)) <| HT.seq
      ((HT.shrConst hJ.shr1 (.inl 0) J.l7 (.inr 2) (by norm_num) _ (X - X % D + D)
        (.mark :: S (.inr 2)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd2 ..) (lnU_k1 B)) <|
      HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 2) (by norm_num) _ ((X - X % D + D) / 2 ^ 1)
        (.mark :: S (.inr 2)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd2 ..)
        (lnU_inc B hY)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 6) (by norm_num) _ (X - X % D)
        (.mark :: S (.inr 6)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd6 ..)
        (lnU_lin B hXr)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 5) (by norm_num) _ (X % D) (.mark :: S (.inr 5))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd5 ..) (lnU_lin B hr)) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 3) (by norm_num) _ D (.mark :: S (.inr 3))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd3 ..) (lnU_inc B hDw))
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 3) (by norm_num) _ (D + 1) (.mark :: S (.inr 3))
        (termOK_mark _) (by simp) []).of_eq ?_ (lnU_inc B hD1))
    rw [lnSt_upd3]
  · omega

/-- The loop state with counter `c`: the series state after `k = B+2-c` steps. -/
def lnLoopSt (S : PL → List Sym) (B c : ℕ) : PL → List Sym :=
  lnSt S (natSyms (lnNatIter B (B + 2 - c)).1 ++ .mark :: S (.inr 0))
    (natSyms (lnNatIter B (B + 2 - c)).2 ++ .mark :: S (.inr 1))
    (natSyms (lnX B (B + 2 - c)) ++ .mark :: S (.inr 2))
    (natSyms (2 * (B + 2 - c) + 4) ++ .mark :: S (.inr 3))
    (natSyms c ++ .mark :: S (.inr 4)) (.mark :: S (.inr 5)) (.mark :: S (.inr 6)) (S (.inl 1))

theorem lnLoop_spec (J : LnInst) {K : ℕ} (hJ : J.Spec K) (B : ℕ) (S : PL → List Sym) :
    HT [] (lnLoopSt S B (B + 2)) (lnLoop J) (lnLoopSt S B 0)
      (K + loopCost (fun i => K * (bitLen (i + 1) + 1) + 15 * lnU K B + K) (B + 2)) := by
  refine HT.cdLoopLt hJ.isz hJ.dec J.l9 J.l10 (.inr 4) (.inl 0) (by norm_num)
    (.mark :: S (.inr 4)) (termOK_mark _) (lnLoopSt S B) (fun i => by simp [lnLoopSt])
    (lnBody J) (fun _ => 15 * lnU K B) [] (B + 2) (fun i hi => ?_)
  have hk : B + 2 - (i + 1) ≤ B + 2 := Nat.sub_le _ _
  have h := lnBody_spec J hJ B S (lnNatIter B (B + 2 - (i + 1))).1
    (lnNatIter B (B + 2 - (i + 1))).2 (lnX B (B + 2 - (i + 1))) (2 * (B + 2 - (i + 1)) + 4)
    (by omega) (piwp (lnSA_le hk) (by omega)) (piwp (lnXD_le hk) (by omega))
    (piw (by omega)) (natSyms i ++ .mark :: S (.inr 4))
  unfold lnLoopSt
  rw [lnSt_upd4, show B + 2 - i = (B + 2 - (i + 1)) + 1 by omega,
    ← lnX_succ B (B + 2 - (i + 1)), lnS_succ B (B + 2 - (i + 1)), ← lnX_div B (B + 2 - (i + 1)),
    show 2 * (B + 2 - (i + 1) + 1) + 4 = 2 * (B + 2 - (i + 1)) + 4 + 1 + 1 by omega]
  exact h

/-! ## Final phase and cleanup -/

theorem lnFinal_spec (J : LnInst) {K : ℕ} (hJ : J.Spec K) (hK : 1 ≤ K) (B : ℕ) (rB : List Sym)
    (S : PL → List Sym) (hrB : TermOK rB) (hB : S (.inl 0) = natSyms B ++ rB) :
    HT [] (lnSt S (natSyms (lnNatIter B (B + 2)).1 ++ .mark :: S (.inr 0))
        (natSyms (lnNatIter B (B + 2)).2 ++ .mark :: S (.inr 1))
        (natSyms (lnX B (B + 2)) ++ .mark :: S (.inr 2))
        (natSyms (2 * (B + 2) + 4) ++ .mark :: S (.inr 3)) (.mark :: S (.inr 4))
        (.mark :: S (.inr 5)) (.mark :: S (.inr 6)) (S (.inl 1)))
      (lnFinal J)
      (lnSt S (natSyms (lnNatIter B (B + 2)).1 ++ .mark :: S (.inr 0))
        (natSyms (log2Nat B) ++ .mark :: S (.inr 1))
        (natSyms (lnX B (B + 2)) ++ .mark :: S (.inr 2))
        (natSyms (2 * (B + 2) + 4) ++ .mark :: S (.inr 3))
        (natSyms (2 * B + 11) ++ .mark :: S (.inr 4))
        (.mark :: S (.inr 5)) (.mark :: S (.inr 6)) (intSyms (log2Nat B : ℤ) ++ S (.inl 1)))
      (13 * lnU K B) := by
  have hsle : (lnNatIter B (B + 2)).2 ≤ 2 ^ (4 * B + 14) :=
    le_trans (Nat.le_add_right _ _) (lnSA_le (le_refl (B + 2)))
  have hsw : bitLen (lnNatIter B (B + 2)).2 ≤ 8 * B + 44 := piwp hsle (by omega)
  have hq0 : bitLen ((lnNatIter B (B + 2)).2 / 2 ^ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + 1)) ≤
      8 * B + 44 := le_trans (WP.W7k2.bitLen_mono (Nat.div_le_self _ _)) hsw
  have hq : bitLen (((lnNatIter B (B + 2)).2 / 2 ^ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + 1) + 1) /
      2 ^ 1) ≤ 8 * B + 44 := by
    refine piwp (k := 4 * B + 15) ?_ (by omega)
    have h1 := Nat.div_le_self (lnNatIter B (B + 2)).2 (2 ^ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + 1))
    have h2 := Nat.div_le_self
      ((lnNatIter B (B + 2)).2 / 2 ^ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + 1) + 1) (2 ^ 1)
    have h3 : 1 ≤ 2 ^ (4 * B + 14) := Nat.one_le_two_pow
    have h4 : 2 ^ (4 * B + 15) = 2 ^ (4 * B + 14) + 2 ^ (4 * B + 14) := by ring
    omega
  apply HT.mono
  · unfold lnFinal
    refine HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.l0 (.inl 0) (.inr 4) (by decide) (by norm_num) _ B rB hrB
        (by simp [hB]) []).of_eq (by rw [lnSt_4, lnSt_upd4]) (lnU_lin B (piw (by omega)))) <|
      HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ B (.mark :: S (.inr 4))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd4 ..) (lnU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1) (.mark :: S (.inr 4))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd4 ..) (lnU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1 + 1) (.mark :: S (.inr 4))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd4 ..) (lnU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1 + 1 + 1)
        (.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd4 ..)
        (lnU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1 + 1 + 1 + 1)
        (.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd4 ..)
        (lnU_inc B (piw (by omega)))) <| HT.seq
      ((HT.shlConst hJ.shl1 (.inl 0) J.l2 (.inr 4) (by norm_num) _ (B + 1 + 1 + 1 + 1 + 1)
        (.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd4 ..) (lnU_k1 B)) <|
      HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1)
        (.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd4 ..)
        (lnU_inc B (piw (by omega)))) <| HT.seq
      ((HT.shrVar hJ.shrV (.inl 0) J.l6 (.inr 1) (.inr 4) (by decide) (by norm_num) _
        (lnNatIter B (B + 2)).2 ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + 1) (.mark :: S (.inr 1))
        (.mark :: S (.inr 4)) (termOK_mark _) (termOK_mark _) (by simp) (by simp) []).of_eq
        (lnSt_upd1 ..) (lnU_shr B (by omega))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 1) (by norm_num) _
        ((lnNatIter B (B + 2)).2 / 2 ^ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + 1)) (.mark :: S (.inr 1))
        (termOK_mark _) (by simp) []).of_eq (lnSt_upd1 ..) (lnU_inc B hq0)) <| HT.seq
      ((HT.shrConst hJ.shr1 (.inl 0) J.l7 (.inr 1) (by norm_num) _
        ((lnNatIter B (B + 2)).2 / 2 ^ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + 1) + 1)
        (.mark :: S (.inr 1)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd1 ..) (lnU_k1 B)) <|
      HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.l0 (.inr 1) (.inl 1) (by decide) (by norm_num) _
        (((lnNatIter B (B + 2)).2 / 2 ^ ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + 1) + 1) / 2 ^ 1)
        (.mark :: S (.inr 1)) (termOK_mark _) (by simp) []).of_eq (by rw [lnSt_d, lnSt_updd])
        (lnU_lin B hq))
      ((HT.pushS (.inl 1) .pos _ []).of_eq ?_ (lnU_one B hK))
    rw [lnSt_d, lnSt_updd, show (B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 + 1 = 2 * B + 11 by ring]
    have hq' : ((lnNatIter B (B + 2)).2 / 2 ^ (2 * B + 11) + 1) / 2 ^ 1 = log2Nat B := by
      unfold log2Nat
      norm_num
    rw [hq', intSyms_natCast]
    rfl
  · omega

theorem lnClean_spec (J : LnInst) {K : ℕ} (hJ : J.Spec K) (hK : 1 ≤ K) (B : ℕ)
    (S : PL → List Sym) (w : List Sym) :
    HT [] (lnSt S (natSyms (lnNatIter B (B + 2)).1 ++ .mark :: S (.inr 0))
        (natSyms (log2Nat B) ++ .mark :: S (.inr 1))
        (natSyms (lnX B (B + 2)) ++ .mark :: S (.inr 2))
        (natSyms (2 * (B + 2) + 4) ++ .mark :: S (.inr 3))
        (natSyms (2 * B + 11) ++ .mark :: S (.inr 4))
        (.mark :: S (.inr 5)) (.mark :: S (.inr 6)) w)
      (lnClean J) (Function.update S (.inl 1) w) (12 * lnU K B) := by
  have hAw : bitLen (lnNatIter B (B + 2)).1 ≤ 8 * B + 44 :=
    piwp (lnNatIter_a_le B (B + 2)) (by omega)
  have hXw : bitLen (lnX B (B + 2)) ≤ 8 * B + 44 :=
    piwp (le_trans (Nat.le_add_right _ _) (lnXD_le (le_refl (B + 2)))) (by omega)
  have hLw : bitLen (log2Nat B) ≤ 8 * B + 44 := by
    refine piwp (k := 4 * B + 15) ?_ (by omega)
    have hs : (lnNatIter B (B + 2)).2 ≤ 2 ^ (4 * B + 14) :=
      le_trans (Nat.le_add_right _ _) (lnSA_le (le_refl (B + 2)))
    have h1 := Nat.div_le_self (lnNatIter B (B + 2)).2 (2 ^ (2 * B + 11))
    have h3 : 1 ≤ 2 ^ (4 * B + 14) := Nat.one_le_two_pow
    have h4 : 2 ^ (4 * B + 15) = 2 ^ (4 * B + 14) + 2 ^ (4 * B + 14) := by ring
    unfold log2Nat
    omega
  apply HT.mono
  · unfold lnClean
    refine HT.seq
      ((HT.popS (.inr 6) _ .mark (S (.inr 6)) (by simp) []).of_eq (lnSt_upd6 ..)
        (lnU_one B hK)) <| HT.seq
      ((HT.popS (.inr 5) _ .mark (S (.inr 5)) (by simp) []).of_eq (lnSt_upd5 ..)
        (lnU_one B hK)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 4) (by norm_num) _ (2 * B + 11)
        (.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd4 ..)
        (lnU_lin B (piw (by omega)))) <| HT.seq
      ((HT.popS (.inr 4) _ .mark (S (.inr 4)) (by simp) []).of_eq (lnSt_upd4 ..)
        (lnU_one B hK)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 3) (by norm_num) _ (2 * (B + 2) + 4)
        (.mark :: S (.inr 3)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd3 ..)
        (lnU_lin B (piw (by omega)))) <| HT.seq
      ((HT.popS (.inr 3) _ .mark (S (.inr 3)) (by simp) []).of_eq (lnSt_upd3 ..)
        (lnU_one B hK)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 2) (by norm_num) _ (lnX B (B + 2))
        (.mark :: S (.inr 2)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd2 ..)
        (lnU_lin B hXw)) <| HT.seq
      ((HT.popS (.inr 2) _ .mark (S (.inr 2)) (by simp) []).of_eq (lnSt_upd2 ..)
        (lnU_one B hK)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 1) (by norm_num) _ (log2Nat B)
        (.mark :: S (.inr 1)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd1 ..)
        (lnU_lin B hLw)) <| HT.seq
      ((HT.popS (.inr 1) _ .mark (S (.inr 1)) (by simp) []).of_eq (lnSt_upd1 ..)
        (lnU_one B hK)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 0) (by norm_num) _ (lnNatIter B (B + 2)).1
        (.mark :: S (.inr 0)) (termOK_mark _) (by simp) []).of_eq (lnSt_upd0 ..)
        (lnU_lin B hAw))
      ((HT.popS (.inr 0) _ .mark (S (.inr 0)) (by simp) []).of_eq ?_ (lnU_one B hK))
    rw [lnSt_upd0, lnSt_final]
  · omega

#assert_std_axioms lnSetup_spec lnBody_spec lnLoop_spec lnFinal_spec lnClean_spec

end WP.W7k1
