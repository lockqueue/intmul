import WP.W7k1.PiDefs
import WP.W7k1.PiCost
import WP.W7k1.Bounds

/-!
# WP.W7k1.PiProof — correctness and cost of the `π` kernel's phases

`piSetup_spec`, `piBody_spec`, `piLoop_spec`, `piFinal_spec`, `piClean_spec`: exact host states
(`piSt`) through the program, each step a contract call (`HT.*` rules) charged at most
`piU K B`. Values: `S = 4B+20`, `P = 2^(S+1)`, `A_k = piIter S k` (`WP.W7k1.Canon`).
-/

namespace WP.W7k1

open TMFw TMFw.Contracts WP.W7k2 Computability

theorem natSyms_zero' : natSyms 0 = [] := by
  simp [natSyms, encodeNat_zero]

/-- `natSyms 1` is one `1` bit. -/
theorem natSyms_one' : natSyms 1 = [Sym.bit true] := by
  have h : encodeNat 1 = [true] := by
    have := encodeNat_add_add_one 0
    simpa [encodeNat_zero] using this
  simp [natSyms, h]

theorem piIter_succ' (S k : ℕ) : piIter S (k + 1) = piStep S (piIter S k) := rfl

/-- Values of at most `8B+44` bits. -/
theorem piw {B x : ℕ} (hx : x ≤ 8 * B + 44) : bitLen x ≤ 8 * B + 44 :=
  le_trans (WP.W7k2.bitLen_le_self x) hx

/-- Values below `2^(k+1)` have at most `k+1 ≤ 8B+44` bits. -/
theorem piwp {B x k : ℕ} (hx : x ≤ 2 ^ k) (hk : k + 1 ≤ 8 * B + 44) : bitLen x ≤ 8 * B + 44 :=
  le_trans (bitLen_le_of_le_pow hx) hk

/-! ## Setup -/

theorem piSetup_spec (J : PiInst) {K : ℕ} (hJ : J.Spec K) (hK : 1 ≤ K) (B : ℕ) (rB : List Sym)
    (S : PL → List Sym) (hrB : TermOK rB) (hB : S (.inl 0) = natSyms B ++ rB) :
    HT [] S (piSetup J)
      (piSt S (natSyms (4 * B + 20) ++ .mark :: S (.inr 0))
        (natSyms (2 ^ (4 * B + 20 + 1)) ++ .mark :: S (.inr 1))
        (.mark :: S (.inr 2)) (.mark :: S (.inr 3)) (natSyms (B + 4) ++ .mark :: S (.inr 4))
        (.mark :: S (.inr 5)) (S (.inl 1)))
      (24 * piU K B) := by
  apply HT.mono
  · unfold piSetup
    refine HT.seq ((HT.pushS (.inr 0) .mark _ []).of_eq (piSt_init ..) (piU_one B hK)) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.l0 (.inl 0) (.inr 0) (by decide) (by norm_num) _ B rB hrB
        (by simp [hB]) []).of_eq (by rw [piSt_0, piSt_upd0]) (piU_lin B (piw (by omega)))) <|
      HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 0) (by norm_num) _ B (.mark :: S (.inr 0))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd0 ..) (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 0) (by norm_num) _ (B + 1) (.mark :: S (.inr 0))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd0 ..) (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 0) (by norm_num) _ (B + 1 + 1) (.mark :: S (.inr 0))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd0 ..) (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 0) (by norm_num) _ (B + 1 + 1 + 1)
        (.mark :: S (.inr 0)) (termOK_mark _) (by simp) []).of_eq (piSt_upd0 ..)
        (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 0) (by norm_num) _ (B + 1 + 1 + 1 + 1)
        (.mark :: S (.inr 0)) (termOK_mark _) (by simp) []).of_eq (piSt_upd0 ..)
        (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.shlConst hJ.shl1 (.inl 0) J.l2 (.inr 0) (by norm_num) _ (B + 1 + 1 + 1 + 1 + 1)
        (.mark :: S (.inr 0)) (termOK_mark _) (by simp) []).of_eq (piSt_upd0 ..) (piU_k1 B)) <|
      HT.seq
      ((HT.shlConst hJ.shl1 (.inl 0) J.l2 (.inr 0) (by norm_num) _
        ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1) (.mark :: S (.inr 0)) (termOK_mark _) (by simp)
        []).of_eq (piSt_upd0 ..) (piU_k1 B)) <| HT.seq
      ((HT.pushS (.inr 5) .mark _ []).of_eq (by rw [piSt_5, piSt_upd5]) (piU_one B hK)) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.l0 (.inr 0) (.inr 5) (by decide) (by norm_num) _
        ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 * 2 ^ 1) (.mark :: S (.inr 0)) (termOK_mark _)
        (by simp) []).of_eq (by rw [piSt_5, piSt_upd5]) (piU_lin B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 5) (by norm_num) _
        ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 * 2 ^ 1) (.mark :: S (.inr 5)) (termOK_mark _)
        (by simp) []).of_eq (piSt_upd5 ..) (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.pushS (.inr 1) .mark _ []).of_eq (by rw [piSt_1, piSt_upd1]) (piU_one B hK)) <| HT.seq
      ((HT.pushS (.inr 1) (.bit true) _ []).of_eq (by rw [piSt_1, piSt_upd1]) (piU_one B hK)) <|
      HT.seq
      ((HT.shlVar hJ.shlV (.inl 0) J.l3 (.inr 1) (.inr 5) (by decide) (by norm_num) _ 1
        ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 * 2 ^ 1 + 1) (.mark :: S (.inr 1)) (.mark :: S (.inr 5))
        (termOK_mark _) (termOK_mark _) (by simp [natSyms_one']) (by simp) []).of_eq
        (piSt_upd1 ..) (piU_shl B (by omega))) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 5) (by norm_num) _
        ((B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 * 2 ^ 1 + 1) (.mark :: S (.inr 5)) (termOK_mark _)
        (by simp) []).of_eq (piSt_upd5 ..) (piU_lin B (piw (by omega)))) <| HT.seq
      ((HT.pushS (.inr 2) .mark _ []).of_eq (by rw [piSt_2, piSt_upd2]) (piU_one B hK)) <| HT.seq
      ((HT.pushS (.inr 3) .mark _ []).of_eq (by rw [piSt_3, piSt_upd3]) (piU_one B hK)) <| HT.seq
      ((HT.pushS (.inr 4) .mark _ []).of_eq (by rw [piSt_4, piSt_upd4]) (piU_one B hK)) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.l0 (.inl 0) (.inr 4) (by decide) (by norm_num) _ B rB hrB
        (by simp [hB]) []).of_eq (by rw [piSt_4, piSt_upd4]) (piU_lin B (piw (by omega)))) <|
      HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ B (.mark :: S (.inr 4))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd4 ..) (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1) (.mark :: S (.inr 4))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd4 ..) (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1 + 1) (.mark :: S (.inr 4))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd4 ..) (piU_inc B (piw (by omega))))
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1 + 1 + 1)
        (.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq ?_
        (piU_inc B (piw (by omega))))
    rw [piSt_upd4, show (B + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 * 2 ^ 1 = 4 * B + 20 by ring,
      show 1 * 2 ^ (4 * B + 20 + 1) = 2 ^ (4 * B + 20 + 1) by ring,
      show B + 1 + 1 + 1 + 1 = B + 4 by ring]
  · by_contra hc
    omega

/-! ## The loop body and the loop -/

theorem piBody_spec (J : PiInst) {K : ℕ} (hJ : J.Spec K) (B : ℕ) (S : PL → List Sym) (A : ℕ)
    (hA : A ≤ 2 ^ (4 * B + 20 + 1)) (v4 : List Sym) :
    HT [] (piSt S (natSyms (4 * B + 20) ++ .mark :: S (.inr 0))
        (natSyms (2 ^ (4 * B + 20 + 1)) ++ .mark :: S (.inr 1)) (natSyms A ++ .mark :: S (.inr 2))
        (.mark :: S (.inr 3)) v4 (.mark :: S (.inr 5)) (S (.inl 1))) (piBody J)
      (piSt S (natSyms (4 * B + 20) ++ .mark :: S (.inr 0))
        (natSyms (2 ^ (4 * B + 20 + 1)) ++ .mark :: S (.inr 1))
        (natSyms (piStep (4 * B + 20) A) ++ .mark :: S (.inr 2))
        (.mark :: S (.inr 3)) v4 (.mark :: S (.inr 5)) (S (.inl 1)))
      (5 * piU K B) := by
  have hAw : bitLen A ≤ 8 * B + 44 := piwp hA (by omega)
  have hPw : bitLen (2 ^ (4 * B + 20 + 1)) ≤ 8 * B + 44 := by
    rw [WP.W7k2.bitLen_two_pow]
    omega
  have hXw : bitLen ((A + 2 ^ (4 * B + 20 + 1)) * 2 ^ (4 * B + 20)) ≤ 8 * B + 44 :=
    piwp (piArg_le _ _ hA) (by omega)
  apply HT.mono
  · unfold piBody
    refine HT.seq
      ((HT.addNat hJ.add (.inl 0) J.l4 (.inr 2) (.inr 1) (.inr 3) (by decide) (by norm_num) _ A
        (2 ^ (4 * B + 20 + 1)) (.mark :: S (.inr 2)) (.mark :: S (.inr 1)) (termOK_mark _)
        (termOK_mark _) (by simp) (by simp) []).of_eq (by rw [piSt_3, piSt_upd3])
        (piU_two B hAw hPw)) <| HT.seq
      ((HT.shlVar hJ.shlV (.inl 0) J.l3 (.inr 3) (.inr 0) (by decide) (by norm_num) _
        (A + 2 ^ (4 * B + 20 + 1)) (4 * B + 20) (.mark :: S (.inr 3)) (.mark :: S (.inr 0))
        (termOK_mark _) (termOK_mark _) (by simp) (by simp) []).of_eq (piSt_upd3 ..)
        (piU_shl B (by omega))) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 2) (by norm_num) _ A (.mark :: S (.inr 2))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd2 ..) (piU_lin B hAw)) <| HT.seq
      ((HT.isqrt hJ.isq (.inl 0) J.l11 (.inr 3) (.inr 2) (by decide) (by norm_num) _
        ((A + 2 ^ (4 * B + 20 + 1)) * 2 ^ (4 * B + 20)) (.mark :: S (.inr 3)) (termOK_mark _)
        (by simp) []).of_eq (by rw [piSt_2, piSt_upd2]) (piU_sq B hXw))
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 3) (by norm_num) _
        ((A + 2 ^ (4 * B + 20 + 1)) * 2 ^ (4 * B + 20)) (.mark :: S (.inr 3)) (termOK_mark _)
        (by simp) []).of_eq ?_ (piU_lin B hXw))
    rw [piSt_upd3, piStep_eq]
  · omega

/-- The loop state with counter `i`: `A = A_{B+4-i}`. -/
def piLoopSt (S : PL → List Sym) (B i : ℕ) : PL → List Sym :=
  piSt S (natSyms (4 * B + 20) ++ .mark :: S (.inr 0))
    (natSyms (2 ^ (4 * B + 20 + 1)) ++ .mark :: S (.inr 1))
    (natSyms (piIter (4 * B + 20) (B + 4 - i)) ++ .mark :: S (.inr 2))
    (.mark :: S (.inr 3)) (natSyms i ++ .mark :: S (.inr 4)) (.mark :: S (.inr 5)) (S (.inl 1))

theorem piLoop_spec (J : PiInst) {K : ℕ} (hJ : J.Spec K) (B : ℕ) (S : PL → List Sym) :
    HT [] (piLoopSt S B (B + 4)) (piLoop J) (piLoopSt S B 0)
      (K + loopCost (fun i => K * (bitLen (i + 1) + 1) + 5 * piU K B + K) (B + 4)) := by
  refine HT.cdLoopLt hJ.isz hJ.dec J.l9 J.l10 (.inr 4) (.inl 0) (by norm_num)
    (.mark :: S (.inr 4)) (termOK_mark _) (piLoopSt S B) (fun i => by simp [piLoopSt])
    (piBody J) (fun _ => 5 * piU K B) [] (B + 4) (fun i hi => ?_)
  have h := piBody_spec J hJ B S (piIter (4 * B + 20) (B + 4 - (i + 1))) (piIter_le _ _)
    (natSyms i ++ .mark :: S (.inr 4))
  unfold piLoopSt
  rw [piSt_upd4, show B + 4 - i = (B + 4 - (i + 1)) + 1 by omega, piIter_succ']
  exact h

/-! ## Final phase and cleanup -/

theorem piFinal_spec (J : PiInst) {K : ℕ} (hJ : J.Spec K) (hK : 1 ≤ K) (B : ℕ) (rB : List Sym)
    (S : PL → List Sym) (hrB : TermOK rB) (hB : S (.inl 0) = natSyms B ++ rB) :
    HT [] (piSt S (natSyms (4 * B + 20) ++ .mark :: S (.inr 0))
        (natSyms (2 ^ (4 * B + 20 + 1)) ++ .mark :: S (.inr 1))
        (natSyms (piIter (4 * B + 20) (B + 4)) ++ .mark :: S (.inr 2))
        (.mark :: S (.inr 3)) (.mark :: S (.inr 4)) (.mark :: S (.inr 5)) (S (.inl 1)))
      (piFinal J)
      (piSt S (natSyms (4 * B + 20) ++ .mark :: S (.inr 0))
        (natSyms (2 ^ (4 * B + 20 + 1)) ++ .mark :: S (.inr 1))
        (natSyms (piIter (4 * B + 20) (B + 4)) ++ .mark :: S (.inr 2))
        (natSyms ((2 ^ (4 * B + 20 + 1) - piIter (4 * B + 20) (B + 4)) * 2 ^ (4 * B + 20)) ++
          .mark :: S (.inr 3))
        (natSyms (2 * B + 14) ++ .mark :: S (.inr 4)) (natSyms (piNat B) ++ .mark :: S (.inr 5))
        (intSyms (piNat B : ℤ) ++ S (.inl 1)))
      (17 * piU K B) := by
  have hAle := piIter_le (4 * B + 20) (B + 4)
  have hAw : bitLen (piIter (4 * B + 20) (B + 4)) ≤ 8 * B + 44 := piwp hAle (by omega)
  have hPw : bitLen (2 ^ (4 * B + 20 + 1)) ≤ 8 * B + 44 := by
    rw [WP.W7k2.bitLen_two_pow]
    omega
  have hYw : bitLen ((2 ^ (4 * B + 20 + 1) - piIter (4 * B + 20) (B + 4)) * 2 ^ (4 * B + 20)) ≤
      8 * B + 44 := piwp (piFinalArg_le _ _) (by omega)
  have hD1 : piD B + 1 ≤ 2 ^ (4 * B + 20 + 2) := by
    have h1 := piD_le B
    have h2 : 1 ≤ 2 ^ (4 * B + 20 + 1) := Nat.one_le_two_pow
    have h3 : 2 ^ (4 * B + 20 + 2) = 2 ^ (4 * B + 20 + 1) + 2 ^ (4 * B + 20 + 1) := by ring
    omega
  have hd1 : bitLen (piD B / 2 ^ ((B + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 2 ^ 1) + 1) ≤ 8 * B + 44 :=
    le_trans (WP.W7k2.bitLen_mono (Nat.add_le_add_right (Nat.div_le_self _ _) 1))
      (piwp hD1 (by omega))
  have hd0 : bitLen (piD B / 2 ^ ((B + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 2 ^ 1)) ≤ 8 * B + 44 :=
    le_trans (WP.W7k2.bitLen_mono (Nat.le_succ _)) hd1
  have hq : bitLen ((piD B / 2 ^ ((B + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 2 ^ 1) + 1) / 2 ^ 1) ≤
      8 * B + 44 := le_trans (WP.W7k2.bitLen_mono (Nat.div_le_self _ _)) hd1
  apply HT.mono
  · unfold piFinal
    refine HT.seq
      ((HT.subNat hJ.sub (.inl 0) J.l5 (.inr 1) (.inr 2) (.inr 3) (by decide) (by norm_num) _
        (2 ^ (4 * B + 20 + 1)) (piIter (4 * B + 20) (B + 4)) (.mark :: S (.inr 1))
        (.mark :: S (.inr 2)) (termOK_mark _) (termOK_mark _) hAle (by simp) (by simp) []).of_eq
        (by rw [piSt_3, piSt_upd3]) (piU_two B hPw hAw)) <| HT.seq
      ((HT.shlVar hJ.shlV (.inl 0) J.l3 (.inr 3) (.inr 0) (by decide) (by norm_num) _
        (2 ^ (4 * B + 20 + 1) - piIter (4 * B + 20) (B + 4)) (4 * B + 20) (.mark :: S (.inr 3))
        (.mark :: S (.inr 0)) (termOK_mark _) (termOK_mark _) (by simp) (by simp) []).of_eq
        (piSt_upd3 ..) (piU_shl B (by omega))) <| HT.seq
      ((HT.isqrt hJ.isq (.inl 0) J.l11 (.inr 3) (.inr 5) (by decide) (by norm_num) _
        ((2 ^ (4 * B + 20 + 1) - piIter (4 * B + 20) (B + 4)) * 2 ^ (4 * B + 20))
        (.mark :: S (.inr 3)) (termOK_mark _) (by simp) []).of_eq (by rw [piSt_5, piSt_upd5])
        (piU_sq B hYw)) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.l0 (.inl 0) (.inr 4) (by decide) (by norm_num) _ B rB hrB
        (by simp [hB]) []).of_eq (by rw [piSt_4, piSt_upd4]) (piU_lin B (piw (by omega)))) <|
      HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ B (.mark :: S (.inr 4))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd4 ..) (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1) (.mark :: S (.inr 4))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd4 ..) (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1 + 1) (.mark :: S (.inr 4))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd4 ..) (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1 + 1 + 1)
        (.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (piSt_upd4 ..)
        (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1 + 1 + 1 + 1)
        (.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (piSt_upd4 ..)
        (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1 + 1 + 1 + 1 + 1)
        (.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (piSt_upd4 ..)
        (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 4) (by norm_num) _ (B + 1 + 1 + 1 + 1 + 1 + 1)
        (.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (piSt_upd4 ..)
        (piU_inc B (piw (by omega)))) <| HT.seq
      ((HT.shlConst hJ.shl1 (.inl 0) J.l2 (.inr 4) (by norm_num) _ (B + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (piSt_upd4 ..) (piU_k1 B)) <|
      HT.seq
      ((HT.shrVar hJ.shrV (.inl 0) J.l6 (.inr 5) (.inr 4) (by decide) (by norm_num) _ (piD B)
        ((B + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 2 ^ 1) (.mark :: S (.inr 5)) (.mark :: S (.inr 4))
        (termOK_mark _) (termOK_mark _) (by simp [piD]) (by simp) []).of_eq (piSt_upd5 ..)
        (piU_shr B (by omega))) <| HT.seq
      ((HT.incNat hJ.inc (.inl 0) J.l1 (.inr 5) (by norm_num) _
        (piD B / 2 ^ ((B + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 2 ^ 1)) (.mark :: S (.inr 5))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd5 ..) (piU_inc B hd0)) <| HT.seq
      ((HT.shrConst hJ.shr1 (.inl 0) J.l7 (.inr 5) (by norm_num) _
        (piD B / 2 ^ ((B + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 2 ^ 1) + 1) (.mark :: S (.inr 5))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd5 ..) (piU_k1 B)) <| HT.seq
      ((HT.copyNat hJ.copy (.inl 0) J.l0 (.inr 5) (.inl 1) (by decide) (by norm_num) _
        ((piD B / 2 ^ ((B + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 2 ^ 1) + 1) / 2 ^ 1)
        (.mark :: S (.inr 5)) (termOK_mark _) (by simp) []).of_eq (by rw [piSt_d, piSt_updd])
        (piU_lin B hq))
      ((HT.pushS (.inl 1) .pos _ []).of_eq ?_ (piU_one B hK))
    rw [piSt_d, piSt_updd, show (B + 1 + 1 + 1 + 1 + 1 + 1 + 1) * 2 ^ 1 = 2 * B + 14 by ring]
    have hq' : (piD B / 2 ^ (2 * B + 14) + 1) / 2 ^ 1 = piNat B := by
      unfold piNat
      norm_num
    rw [hq', intSyms_natCast]
    rfl
  · by_contra hc
    omega

theorem piClean_spec (J : PiInst) {K : ℕ} (hJ : J.Spec K) (hK : 1 ≤ K) (B : ℕ)
    (S : PL → List Sym) (w : List Sym) :
    HT [] (piSt S (natSyms (4 * B + 20) ++ .mark :: S (.inr 0))
        (natSyms (2 ^ (4 * B + 20 + 1)) ++ .mark :: S (.inr 1))
        (natSyms (piIter (4 * B + 20) (B + 4)) ++ .mark :: S (.inr 2))
        (natSyms ((2 ^ (4 * B + 20 + 1) - piIter (4 * B + 20) (B + 4)) * 2 ^ (4 * B + 20)) ++
          .mark :: S (.inr 3))
        (natSyms (2 * B + 14) ++ .mark :: S (.inr 4)) (natSyms (piNat B) ++ .mark :: S (.inr 5)) w)
      (piClean J) (Function.update S (.inl 1) w) (12 * piU K B) := by
  have hAle := piIter_le (4 * B + 20) (B + 4)
  have hAw : bitLen (piIter (4 * B + 20) (B + 4)) ≤ 8 * B + 44 := piwp hAle (by omega)
  have hPw : bitLen (2 ^ (4 * B + 20 + 1)) ≤ 8 * B + 44 := by
    rw [WP.W7k2.bitLen_two_pow]
    omega
  have hYw : bitLen ((2 ^ (4 * B + 20 + 1) - piIter (4 * B + 20) (B + 4)) * 2 ^ (4 * B + 20)) ≤
      8 * B + 44 := piwp (piFinalArg_le _ _) (by omega)
  have hD1 : piD B + 1 ≤ 2 ^ (4 * B + 20 + 2) := by
    have h1 := piD_le B
    have h2 : 1 ≤ 2 ^ (4 * B + 20 + 1) := Nat.one_le_two_pow
    have h3 : 2 ^ (4 * B + 20 + 2) = 2 ^ (4 * B + 20 + 1) + 2 ^ (4 * B + 20 + 1) := by ring
    omega
  have hqle : piNat B ≤ piD B + 1 := by
    unfold piNat
    have := Nat.div_le_self (piD B) (2 ^ (2 * B + 14))
    have := Nat.div_le_self (piD B / 2 ^ (2 * B + 14) + 1) 2
    omega
  have hqw : bitLen (piNat B) ≤ 8 * B + 44 :=
    le_trans (WP.W7k2.bitLen_mono hqle) (piwp hD1 (by omega))
  apply HT.mono
  · unfold piClean
    refine HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 5) (by norm_num) _ (piNat B) (.mark :: S (.inr 5))
        (termOK_mark _) (by simp) []).of_eq (piSt_upd5 ..) (piU_lin B hqw)) <| HT.seq
      ((HT.popS (.inr 5) _ .mark (S (.inr 5)) (by simp) []).of_eq (piSt_upd5 ..)
        (piU_one B hK)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 4) (by norm_num) _ (2 * B + 14)
        (.mark :: S (.inr 4)) (termOK_mark _) (by simp) []).of_eq (piSt_upd4 ..)
        (piU_lin B (piw (by omega)))) <| HT.seq
      ((HT.popS (.inr 4) _ .mark (S (.inr 4)) (by simp) []).of_eq (piSt_upd4 ..)
        (piU_one B hK)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 3) (by norm_num) _
        ((2 ^ (4 * B + 20 + 1) - piIter (4 * B + 20) (B + 4)) * 2 ^ (4 * B + 20))
        (.mark :: S (.inr 3)) (termOK_mark _) (by simp) []).of_eq (piSt_upd3 ..)
        (piU_lin B hYw)) <| HT.seq
      ((HT.popS (.inr 3) _ .mark (S (.inr 3)) (by simp) []).of_eq (piSt_upd3 ..)
        (piU_one B hK)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 2) (by norm_num) _ (piIter (4 * B + 20) (B + 4))
        (.mark :: S (.inr 2)) (termOK_mark _) (by simp) []).of_eq (piSt_upd2 ..)
        (piU_lin B hAw)) <| HT.seq
      ((HT.popS (.inr 2) _ .mark (S (.inr 2)) (by simp) []).of_eq (piSt_upd2 ..)
        (piU_one B hK)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 1) (by norm_num) _ (2 ^ (4 * B + 20 + 1))
        (.mark :: S (.inr 1)) (termOK_mark _) (by simp) []).of_eq (piSt_upd1 ..)
        (piU_lin B hPw)) <| HT.seq
      ((HT.popS (.inr 1) _ .mark (S (.inr 1)) (by simp) []).of_eq (piSt_upd1 ..)
        (piU_one B hK)) <| HT.seq
      ((HT.dropNat hJ.drop (.inl 0) J.l8 (.inr 0) (by norm_num) _ (4 * B + 20)
        (.mark :: S (.inr 0)) (termOK_mark _) (by simp) []).of_eq (piSt_upd0 ..)
        (piU_lin B (piw (by omega))))
      ((HT.popS (.inr 0) _ .mark (S (.inr 0)) (by simp) []).of_eq ?_ (piU_one B hK))
    rw [piSt_upd0, piSt_final]
  · omega

#assert_std_axioms natSyms_zero' natSyms_one' piIter_succ' piw piwp piSetup_spec piBody_spec
  piLoop_spec piFinal_spec piClean_spec

end WP.W7k1
