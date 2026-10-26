/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.TwiddleAddrPass

/-!
# K4-TWIDDLE (B) (`Machine/FFT/TwiddleAddrTop.lean`): the routine and its phases

**Scope (honest summary).** Programs and host rules, all proved (no `sorry`):
* `hdrIn`: park the five fixed header fields `q, D, ℓ, K, w`, copying `D`, `ℓ`, `K` out;
  `hdrOut` puts them back;
* `consts`: the per-call constants `m₀-1, ℓ-1, ℓ-2, b₀ = (ℓ-1) % K, b₀D, DK, ℓ-1-v`, the long
  rank start `L` and the axis counter `D`;
* `finish`: push `2·(acc mod 2^ℓ)` on the destination `sOut`; `cleanup`: drop the constants;
* `twProg`: the whole routine (`hdrIn`, pass 1, `consts`, pass 2, `finish`, `cleanup`,
  `hdrOut`).
-/

namespace SubNLogN.Machine.FFT.TwAddr

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine.FFT.Phase SubNLogN.Math.Walsh

/-! ## Programs -/

section Programs

variable (I : TI)

/-- Park `q, D, ℓ, K, w` (on `kPK`), copying `D, ℓ, K` to `kD, kL, kK`. -/
def hdrIn : TP I :=
  (mvF I sHd kPK).seq <| (tcp I sHd kD).seq <| (mvF I sHd kPK).seq <| (tcp I sHd kL).seq <|
  (mvF I sHd kPK).seq <| (tcp I sHd kK).seq <| (mvF I sHd kPK).seq (mvF I sHd kPK)

/-- Put the five parked fields back. -/
def hdrOut : TP I :=
  (rsF I sHd kPK).seq <| (rsF I sHd kPK).seq <| (rsF I sHd kPK).seq <| (rsF I sHd kPK).seq <|
  rsF I sHd kPK

/-- The per-call constants. -/
def consts : TP I :=
  (tcp I kM kM1).seq <| (tdc I kM1).seq <| (tcp I kL kL1).seq <| (tdc I kL1).seq <|
  (tcp I kL1 kL2).seq <| (tdc I kL2).seq <| (tdm I kL1 kK xQ kB0).seq <| (tdr I xQ).seq <|
  (tnm I kB0 kD kB0D).seq <| (tnm I kD kK kDK).seq <| (tsb I kL1 sV kE).seq <|
  (tcp I kLc kR).seq (tcp I kD kIx)

/-- `sOut += 2·(acc mod 2^ℓ)`, computed as `(acc - ⌊acc/2^ℓ⌋·2^ℓ)·2`. -/
def finish : TP I :=
  (tcp I kAcc xF).seq <| (trv I xF kL).seq <| (tsv I xF kL).seq <| (tsb I kAcc xF xG).seq <|
  (ts1 I xG).seq <| (tcp I xG sOut).seq <| (tdr I xG).seq (tdr I xF)

/-- Drop the accumulator and the constants. -/
def cleanup : TP I :=
  (tdr I kAcc).seq <| (tdr I kE).seq <| (tdr I kDK).seq <| (tdr I kB0D).seq <| (tdr I kB0).seq <|
  (tdr I kL2).seq <| (tdr I kL1).seq <| (tdr I kM1).seq <| (tdr I kLc).seq <| (tdr I kM).seq <|
  (tdr I kK).seq <| (tdr I kL).seq (tdr I kD)

/-- **The twiddle-address routine.** -/
def twProg : TP I :=
  (hdrIn I).seq <| (tcp I kD kC1).seq <| (tcd I kC1 (p1Body I)).seq <| (consts I).seq <|
  (tcd I kIx (axBody I)).seq <| (finish I).seq <| (cleanup I).seq (hdrOut I)

theorem twProg_closed : (twProg I).Closed := by
  refine ⟨?_, callI_closed _ _ _ _, tcd_closed I _ _ (p1Body_closed I), ?_,
    tcd_closed I _ _ (axBody_closed I), ?_, ?_, ?_⟩
  · unfold hdrIn
    exact ⟨mvF_closed I _ _, callI_closed _ _ _ _, mvF_closed I _ _, callI_closed _ _ _ _,
      mvF_closed I _ _, callI_closed _ _ _ _, mvF_closed I _ _, mvF_closed I _ _⟩
  · unfold consts
    exact ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
      callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
      tnm_closed I _ _ _, tnm_closed I _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
      callI_closed _ _ _ _⟩
  · unfold finish
    repeat (first | exact callI_closed _ _ _ _ | refine ⟨?_, ?_⟩)
  · unfold cleanup
    repeat (first | exact callI_closed _ _ _ _ | refine ⟨?_, ?_⟩)
  · unfold hdrOut
    exact ⟨rsF_closed I _ _, rsF_closed I _ _, rsF_closed I _ _, rsF_closed I _ _,
      rsF_closed I _ _⟩

end Programs

theorem pkS5 (q D ℓ K w : ℕ) (r : List Sym) :
    pkS [q, D, ℓ, K, w] ++ r = Sym.mark :: (natSyms w ++ Sym.mark :: (natSyms K ++ Sym.mark ::
      (natSyms ℓ ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms q ++ r))))) := by
  simp [pkS]

/-! ## Host rules of the phases -/

section Rules

variable {I : TI} {Mul : ℕ → ℕ} {C KM : ℕ}

set_option maxHeartbeats 1000000 in
theorem HT.hdrIn (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym) {q D ℓ K w : ℕ}
    {tl : List Sym}
    (hB : B sHd = natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
      (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: tl)))))
    (bq : bitLen q ≤ Q) (bD : bitLen D ≤ Q) (bl : bitLen ℓ ≤ Q) (bK : bitLen K ≤ Q)
    (bw : bitLen w ≤ Q) :
    HT [] B (hdrIn I)
      (Function.update (Function.update (Function.update (Function.update (Function.update B
        sHd tl) kD (natSyms D ++ B kD)) kL (natSyms ℓ ++ B kL)) kK (natSyms K ++ B kK))
        kPK (pkS [q, D, ℓ, K, w] ++ B kPK))
      (13 * U C KM Q + 10) := by
  rw [pkS5]
  refine (HT.seq (HT.mvF hI Q sHd kPK (by decide) B q _ hB bq) <|
    HT.seq (HT.tcp hI Q sHd kD (by decide) _ D
      (Sym.mark :: (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark ::
        tl)))) (termOK_mark _) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bD) <|
    HT.seq (HT.mvF hI Q sHd kPK (by decide) _ D
      (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: tl))) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bD) <|
    HT.seq (HT.tcp hI Q sHd kL (by decide) _ ℓ
      (Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: tl))) (termOK_mark _) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bl) <|
    HT.seq (HT.mvF hI Q sHd kPK (by decide) _ ℓ
      (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: tl)) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bl) <|
    HT.seq (HT.tcp hI Q sHd kK (by decide) _ K (Sym.mark :: (natSyms w ++ Sym.mark :: tl))
      (termOK_mark _) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bK) <|
    HT.seq (HT.mvF hI Q sHd kPK (by decide) _ K (natSyms w ++ Sym.mark :: tl) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bK) <|
    HT.mvF hI Q sHd kPK (by decide) _ w tl (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bw).of_eq ?_ (by omega)
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

set_option maxHeartbeats 1000000 in
theorem HT.hdrOut (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym) {q D ℓ K w : ℕ}
    {r : List Sym} (hr : TermOK r) (hB : B kPK = pkS [q, D, ℓ, K, w] ++ r)
    (bq : bitLen q ≤ Q) (bD : bitLen D ≤ Q) (bl : bitLen ℓ ≤ Q) (bK : bitLen K ≤ Q)
    (bw : bitLen w ≤ Q) :
    HT [] B (hdrOut I)
      (Function.update (Function.update B kPK r) sHd (natSyms q ++ Sym.mark :: (natSyms D ++
        Sym.mark :: (natSyms ℓ ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark ::
        B sHd))))))
      (10 * U C KM Q + 10) := by
  rw [pkS5] at hB
  refine (HT.seq (HT.rsF hI Q sHd kPK (by decide) B w _ (termOK_mark _) hB bw) <|
    HT.seq (HT.rsF hI Q sHd kPK (by decide) _ K
      (Sym.mark :: (natSyms ℓ ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms q ++ r))))
      (termOK_mark _) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bK) <|
    HT.seq (HT.rsF hI Q sHd kPK (by decide) _ ℓ
      (Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms q ++ r))) (termOK_mark _) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bl) <|
    HT.seq (HT.rsF hI Q sHd kPK (by decide) _ D (Sym.mark :: (natSyms q ++ r)) (termOK_mark _)
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bD) <|
    HT.rsF hI Q sHd kPK (by decide) _ q r hr (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bq).of_eq ?_ (by omega)
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

set_option maxHeartbeats 2000000 in
theorem HT.consts (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym) {ℓ K D L m v w : ℕ}
    {rM rL rK rD rLc vr : List Sym}
    (hM : B kM = natSyms m ++ rM) (hrM : TermOK rM) (hL : B kL = natSyms ℓ ++ rL)
    (hrL : TermOK rL) (hK : B kK = natSyms K ++ rK) (hrK : TermOK rK)
    (hD : B kD = natSyms D ++ rD) (hrD : TermOK rD) (hLc : B kLc = natSyms L ++ rLc)
    (hrLc : TermOK rLc) (hv : B sV = natSyms v ++ vr) (hvr : TermOK vr)
    (t1 : TermOK (B kM1)) (t2 : TermOK (B kL1)) (t3 : TermOK (B kL2)) (t4 : TermOK (B xQ))
    (t5 : TermOK (B kB0)) (t6 : TermOK (B xM1)) (t7 : TermOK (B xM2))
    (hP : POK ℓ K D L m w) (hQ : 6 * (m + w + 1) ≤ Q) (hvl : v < ℓ) :
    HT [] B (consts I)
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update B
        kM1 (natSyms (m - 1) ++ B kM1)) kL1 (natSyms (ℓ - 1) ++ B kL1))
        kL2 (natSyms (ℓ - 2) ++ B kL2)) kB0 (natSyms ((ℓ - 1) % K) ++ B kB0))
        kB0D (natSyms ((ℓ - 1) % K * D) ++ B kB0D)) kDK (natSyms (D * K) ++ B kDK))
        kE (natSyms (ℓ - 1 - v) ++ B kE)) kR (natSyms L ++ B kR)) kIx (natSyms D ++ B kIx))
      (21 * U C KM Q + 10) := by
  have hDm := hP.D_le
  have hd1 := hP.d1
  have hl2 := hP.l2
  have hlw := hP.lw
  have hk1 := hP.k1
  have hkl := hP.kl
  have hLD := hP.ld
  have em : m - 1 + 1 = m := by omega
  have el : ℓ - 1 + 1 = ℓ := by omega
  have el2 : ℓ - 2 + 1 = ℓ - 1 := by omega
  have hb0 : (ℓ - 1) % K < K := Nat.mod_lt _ (by omega)
  have hq0 : (ℓ - 1) / K ≤ ℓ := le_trans (Nat.div_le_self _ _) (by omega)
  have hB0D : (ℓ - 1) % K * D ≤ m := le_trans (Nat.mul_le_mul_right D (by omega)) hP.dm
  have hDK : D * K ≤ m := le_trans (Nat.mul_le_mul_left D hkl) (by rw [mul_comm]; exact hP.dm)
  have bm : bitLen m ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bl : bitLen ℓ ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bl1 : bitLen (ℓ - 1) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bK : bitLen K ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bD : bitLen D ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bL : bitLen L ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bv : bitLen v ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bq0 : bitLen ((ℓ - 1) / K) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have bb0 : bitLen ((ℓ - 1) % K) ≤ Q := le_trans (bitLen_le_self _) (by omega)
  refine (HT.seq (HT.tcp hI Q kM kM1 (by decide) B m rM hrM hM bm) <|
    HT.seq (HT.tdc hI Q kM1 _ (m - 1) (B kM1) t1 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, em]) (by rw [em]; exact bm)) <|
    HT.seq (HT.tcp hI Q kL kL1 (by decide) _ ℓ rL hrL (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hL]) bl) <|
    HT.seq (HT.tdc hI Q kL1 _ (ℓ - 1) (B kL1) t2 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, el]) (by rw [el]; exact bl)) <|
    HT.seq (HT.tcp hI Q kL1 kL2 (by decide) _ (ℓ - 1) (B kL1) t2 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bl1) <|
    HT.seq (HT.tdc hI Q kL2 _ (ℓ - 2) (B kL2) t3 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, el2]) (by rw [el2]; exact bl1)) <|
    HT.seq (HT.tdm hI Q kL1 kK xQ kB0 (by decide) _ (ℓ - 1) K (B kL1) rK (by omega) t2 hrK (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hK]) bl1 bK) <|
    HT.seq (HT.tdr hI Q xQ _ ((ℓ - 1) / K) (B xQ) t4 (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bq0) <|
    HT.seq (HT.tnm hI Q kB0 kD kB0D (by decide) (by decide) _ ((ℓ - 1) % K) D (B kB0) rD t5 hrD
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hD]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact t6) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact t7) bb0 bD) <|
    HT.seq (HT.tnm hI Q kD kK kDK (by decide) (by decide) _ D K rD rK hrD hrK (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hD]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hK]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact t6) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]; exact t7) bD bK) <|
    HT.seq (HT.tsb hI Q kL1 sV kE (by decide) _ (ℓ - 1) v (B kL1) vr t2 hvr (by omega) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hv]) bl1 bv) <|
    HT.seq (HT.tcp hI Q kLc kR (by decide) _ L rLc hrLc (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hLc]) bL) <|
    HT.tcp hI Q kD kIx (by decide) _ D rD hrD (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hD]) bD).of_eq ?_ (by omega)
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

set_option maxHeartbeats 1000000 in
theorem HT.finish (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym) {acc ℓ : ℕ}
    {rA rL : List Sym} (hA : B kAcc = natSyms acc ++ rA) (hrA : TermOK rA)
    (hL : B kL = natSyms ℓ ++ rL) (hrL : TermOK rL) (hxF : TermOK (B xF)) (hxG : TermOK (B xG))
    (bacc : bitLen acc ≤ Q) (blQ : ℓ + 1 ≤ Q) :
    HT [] B (finish I)
      (Function.update B sOut (natSyms ((acc - acc / 2 ^ ℓ * 2 ^ ℓ) * 2 ^ 1) ++ B sOut))
      (8 * U C KM Q) := by
  have hd1 : acc / 2 ^ ℓ * 2 ^ ℓ ≤ acc := Nat.div_mul_le_self _ _
  have hmod : acc - acc / 2 ^ ℓ * 2 ^ ℓ < 2 ^ ℓ := by
    have h1 := Nat.mod_lt acc (Nat.two_pow_pos ℓ)
    have e := Nat.div_add_mod acc (2 ^ ℓ)
    have e2 : acc - acc / 2 ^ ℓ * 2 ^ ℓ = acc % 2 ^ ℓ := by
      rw [Nat.mul_comm]; omega
    omega
  have b1 : bitLen (acc / 2 ^ ℓ) ≤ Q := le_trans (bitLen_mono (Nat.div_le_self _ _)) bacc
  have b2 : bitLen (acc / 2 ^ ℓ * 2 ^ ℓ) ≤ Q := le_trans (bitLen_mono hd1) bacc
  have bl : bitLen ℓ ≤ Q := le_trans (bitLen_le_self _) (by omega)
  have b3 : bitLen (acc - acc / 2 ^ ℓ * 2 ^ ℓ) ≤ Q :=
    le_trans (bitLen_mono (Nat.sub_le _ _)) bacc
  have b4 : bitLen ((acc - acc / 2 ^ ℓ * 2 ^ ℓ) * 2 ^ 1) ≤ Q := by
    refine le_trans (bitLen_le_of_lt (k := ℓ + 1) ?_) blQ
    rw [pow_one, pow_succ]
    exact Nat.mul_lt_mul_of_pos_right hmod (by norm_num)
  refine (HT.seq (HT.tcp hI Q kAcc xF (by decide) B acc rA hrA hA bacc) <|
    HT.seq (HT.trv hI Q xF kL (by decide) _ acc ℓ (B xF) rL hxF hrL (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hL]) bacc bl) <|
    HT.seq (HT.tsv hI Q xF kL (by decide) _ (acc / 2 ^ ℓ) ℓ (B xF) rL hxF hrL (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hL]) (by omega)) <|
    HT.seq (HT.tsb hI Q kAcc xF xG (by decide) _ acc (acc / 2 ^ ℓ * 2 ^ ℓ) rA (B xF) hrA hxF hd1
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, hA]) (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) bacc b2) <|
    HT.seq (HT.ts1 hI Q xG _ (acc - acc / 2 ^ ℓ * 2 ^ ℓ) (B xG) hxG (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne])) <|
    HT.seq (HT.tcp hI Q xG sOut (by decide) _ ((acc - acc / 2 ^ ℓ * 2 ^ ℓ) * 2 ^ 1) (B xG) hxG
      (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b4) <|
    HT.seq (HT.tdr hI Q xG _ ((acc - acc / 2 ^ ℓ * 2 ^ ℓ) * 2 ^ 1) (B xG) hxG (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b4) <|
    HT.tdr hI Q xF _ (acc / 2 ^ ℓ * 2 ^ ℓ) (B xF) hxF (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne]) b2).of_eq ?_ (by omega)
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

set_option maxHeartbeats 2000000 in
theorem HT.cleanup (hI : I.Spec Mul C KM) (Q : ℕ) (B : TL → List Sym)
    {xAcc xE xDK xB0D xB0 xL2 xL1 xM1v xLc xMv xKv xLv xDv : ℕ}
    (h1 : B kAcc = natSyms xAcc) (h2 : B kE = natSyms xE) (h3 : B kDK = natSyms xDK)
    (h4 : B kB0D = natSyms xB0D) (h5 : B kB0 = natSyms xB0) (h6 : B kL2 = natSyms xL2)
    (h7 : B kL1 = natSyms xL1) (h8 : B kM1 = natSyms xM1v) (h9 : B kLc = natSyms xLc)
    (h10 : B kM = natSyms xMv) (h11 : B kK = natSyms xKv) (h12 : B kL = natSyms xLv)
    (h13 : B kD = natSyms xDv) (b1 : bitLen xAcc ≤ Q) (b2 : bitLen xE ≤ Q) (b3 : bitLen xDK ≤ Q)
    (b4 : bitLen xB0D ≤ Q) (b5 : bitLen xB0 ≤ Q) (b6 : bitLen xL2 ≤ Q) (b7 : bitLen xL1 ≤ Q)
    (b8 : bitLen xM1v ≤ Q) (b9 : bitLen xLc ≤ Q) (b10 : bitLen xMv ≤ Q) (b11 : bitLen xKv ≤ Q)
    (b12 : bitLen xLv ≤ Q) (b13 : bitLen xDv ≤ Q) :
    HT [] B (cleanup I)
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (B) kAcc []) kE []) kDK []) kB0D []) kB0 []) kL2 []) kL1 []) kM1 []) kLc []) kM []) kK []) kL []) kD [])
      (13 * U C KM Q) := by
  refine (
    HT.seq (HT.tdr hI Q kAcc B xAcc [] TermOK.nil (by rw [h1, List.append_nil]) b1) <|
    HT.seq (HT.tdr hI Q kE _ xE [] TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h2, List.append_nil]) b2) <|
    HT.seq (HT.tdr hI Q kDK _ xDK [] TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h3, List.append_nil]) b3) <|
    HT.seq (HT.tdr hI Q kB0D _ xB0D [] TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h4, List.append_nil]) b4) <|
    HT.seq (HT.tdr hI Q kB0 _ xB0 [] TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h5, List.append_nil]) b5) <|
    HT.seq (HT.tdr hI Q kL2 _ xL2 [] TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h6, List.append_nil]) b6) <|
    HT.seq (HT.tdr hI Q kL1 _ xL1 [] TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h7, List.append_nil]) b7) <|
    HT.seq (HT.tdr hI Q kM1 _ xM1v [] TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h8, List.append_nil]) b8) <|
    HT.seq (HT.tdr hI Q kLc _ xLc [] TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h9, List.append_nil]) b9) <|
    HT.seq (HT.tdr hI Q kM _ xMv [] TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h10, List.append_nil]) b10) <|
    HT.seq (HT.tdr hI Q kK _ xKv [] TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h11, List.append_nil]) b11) <|
    HT.seq (HT.tdr hI Q kL _ xLv [] TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h12, List.append_nil]) b12) <|
    HT.tdr hI Q kD _ xDv [] TermOK.nil (by
        simp (config := { failIfUnchanged := false }) (disch := decide) only
          [Function.update_self, Function.update_of_ne, h13, List.append_nil]) b13).of_eq ?_ (by omega)
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only
      [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
      Function.update_of_ne, List.append_assoc, List.cons_append, List.nil_append]

end Rules

end SubNLogN.Machine.FFT.TwAddr
