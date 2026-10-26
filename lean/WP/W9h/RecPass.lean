import WP.W9h.RecPre

/-!
# WP.W9h.RecPass — one step of each pass of `W9_reconstruct`, the middle and the cleanup
-/

namespace WP.W9h

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-- `C·X + Y ≤ (C+1)·(X+Y)`: collecting a kernel cost under one factor. -/
theorem le_succ_mul (C X Y : ℕ) : C * X + Y ≤ (C + 1) * (X + Y) := by
  nlinarith [Nat.zero_le (C * Y), Nat.zero_le X]

namespace Kit

variable {K : Kit} {C : ℕ} (hK : K.Spec C)
include hK

/-- Carry-pass step: `t := c + carry`, `L += t % 2^b`, `carry := t / 2^b`, digit and its mark
consumed. -/
theorem HT_recBody1 (P : H → List Sym) (x c b : ℕ) (rest rcr rt rb : List Sym)
    (hoa : P hOA = natSyms x ++ Sym.mark :: rest) (hcr : P rCR = natSyms c ++ Sym.mark :: rcr)
    (ht : P rT = Sym.mark :: rt) (hb : P rB = natSyms b ++ Sym.mark :: rb) :
    HT [] P K.recBody1
      (Function.update (Function.update (Function.update P hOA rest) rCR
        (natSyms ((x + c) / 2 ^ b) ++ Sym.mark :: rcr)) rL
        (natSyms ((x + c) % 2 ^ b) ++ Sym.mark :: P rL))
      (C * (2 * bitLen x + 2 * bitLen c + 2 * bitLen ((x + c) / 2 ^ b) + b + bitLen b + 6) + 2) := by
  refine (HT.seq (Kit.HT_ad hK (x := hOA) (y := rCR) (z := rT) (by decide) P x c
      (Sym.mark :: rest) (Sym.mark :: rcr) (termOK_mark' _) (termOK_mark' _) hoa hcr) <|
    HT.seq (Kit.HT_dr hK rCR _ c (Sym.mark :: rcr) (termOK_mark' _) (by simp [hcr])) <|
    HT.seq (Kit.HT_dr hK hOA _ x (Sym.mark :: rest) (termOK_mark' _) (by simp [hoa])) <|
    HT.seq (Kit.HT_pop (K := K) hOA _ .mark rest (by simp)) <|
    HT.seq (Kit.HT_push (K := K) rL .mark _) <|
    HT.seq (Kit.HT_spl hK (x := rT) (c := rB) (y := rL) (by decide) _ (x + c) b (Sym.mark :: rt)
      (Sym.mark :: rb) (termOK_mark' _) (termOK_mark' _) (by simp [ht]) (by simp [hb])) <|
    HT.seq (Kit.HT_cp hK (x := rT) (y := rCR) (by decide) _ ((x + c) / 2 ^ b) (Sym.mark :: rt)
      (termOK_mark' _) (by simp)) <|
    Kit.HT_dr hK rT _ ((x + c) / 2 ^ b) (Sym.mark :: rt) (termOK_mark' _) (by simp)).of_eq ?_ ?_
  · funext k
    by_cases e1 : k = hOA
    · subst e1; simp
    by_cases e2 : k = rCR
    · subst e2; simp
    by_cases e3 : k = rT
    · subst e3; simp [ht]
    by_cases e4 : k = rL
    · subst e4; simp
    simp [e1, e2, e3, e4]
  · have h1 : min b (bitLen (x + c)) ≤ b := min_le_left _ _
    have h2 : C * min b (bitLen (x + c)) ≤ C * b := Nat.mul_le_mul_left _ h1
    ring_nf at h2 ⊢
    omega

/-- Horner step: `OA := lo + OA·2^b`, `lo` and its mark consumed. -/
theorem HT_recBody2 (P : H → List Sym) (hi lo b : ℕ) (rA rl rb : List Sym) (hrA : TermOK rA)
    (hlo : lo < 2 ^ b) (hoa : P hOA = natSyms hi ++ rA) (hl : P rL = natSyms lo ++ Sym.mark :: rl)
    (hb : P rB = natSyms b ++ Sym.mark :: rb) :
    HT [] P K.recBody2
      (Function.update (Function.update P hOA (natSyms (lo + hi * 2 ^ b) ++ rA)) rL rl)
      (C * (b + bitLen b + 1) + 1) := by
  refine (HT.seq (Kit.HT_cat hK (x := hOA) (c := rB) (y := rL) (by decide) P hi lo b rA
      (Sym.mark :: rb) (Sym.mark :: rl) hrA (termOK_mark' _) (termOK_mark' _) hlo hoa hb hl)
    (Kit.HT_pop (K := K) rL _ .mark rl (by simp))).of_eq ?_ le_rfl
  rw [Function.update_idem]

/-- `OA := carry`, carry dropped. -/
theorem HT_recMid (P : H → List Sym) (R : ℕ) (rcr : List Sym)
    (hcr : P rCR = natSyms R ++ Sym.mark :: rcr) :
    HT [] P K.recMid
      (Function.update (Function.update P hOA (natSyms R ++ P hOA)) rCR (Sym.mark :: rcr))
      (C * (bitLen R + 1) + C * (bitLen R + 1)) :=
  HT.seq (Kit.HT_cp hK (x := rCR) (y := hOA) (by decide) P R (Sym.mark :: rcr) (termOK_mark' _)
    hcr) (Kit.HT_dr hK rCR _ R (Sym.mark :: rcr) (termOK_mark' _) (by simp [hcr]))

/-- Cleanup: pop the counter floors, drop `b`, pop the floors of `rB`, `rCR`, `rT`. -/
theorem HT_recPost (P : H → List Sym) (b : ℕ) (c1 c2 c3 c4 c5 : List Sym)
    (h1 : P rCT = Sym.mark :: c1) (h2 : P rCT2 = Sym.mark :: c2)
    (h3 : P rB = natSyms b ++ Sym.mark :: c3) (h4 : P rCR = Sym.mark :: c4)
    (h5 : P rT = Sym.mark :: c5) :
    HT [] P K.recPost
      (Function.update (Function.update (Function.update (Function.update (Function.update P
        rCT c1) rCT2 c2) rB c3) rCR c4) rT c5)
      (C * (bitLen b + 1) + 5) := by
  refine (HT.seq (Kit.HT_pop (K := K) rCT P .mark c1 h1) <|
    HT.seq (Kit.HT_pop (K := K) rCT2 _ .mark c2 (by simp [h2])) <|
    HT.seq (Kit.HT_dr hK rB _ b (Sym.mark :: c3) (termOK_mark' _) (by simp [h3])) <|
    HT.seq (Kit.HT_pop (K := K) rB _ .mark c3 (by simp)) <|
    HT.seq (Kit.HT_pop (K := K) rCR _ .mark c4 (by simp [h4]))
      (Kit.HT_pop (K := K) rT _ .mark c5 (by simp [h5]))).of_eq ?_ (by omega)
  funext k
  by_cases e1 : k = rB
  · subst e1; simp
  simp

end Kit

#assert_std_axioms le_succ_mul Kit.HT_recBody1 Kit.HT_recBody2 Kit.HT_recMid Kit.HT_recPost

end WP.W9h
