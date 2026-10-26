import WP.W9sq.Entry1

/-!
# WP.W9sq.Init — the square kernel's constants from the header (contributed by W9h)

`initK`: from the header `b, K0, k1, k2` on `C0`, push `q = 2b + 2K0 + 8` (`= rootPrecision b K0 + 2`)
on `sQ`, `2^(q-1)` on `sH` and `2^(q-1) - 1` on `sH1`; `C0`, `sA`, `sT1` are restored.

Steps: `sA := b` (copyNat); skip `b` on `C0` (`skipF`, parked on `sT1`); `sQ := b + K0` (addNat);
restore `C0` (`unskipF`); drop `sA`; four increments; push bit `0` (`×2`); `sH := 1·2^q` (push bit `1`,
shlVar); pop the low zero (`2^(q-1)`); `sH1 := sH − 1` (copyNat, decNat).
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

section Skip

variable {na nb : ℕ} {σ : Type}

/-- Move one header field `natSyms v ++ [mark]` from `src` to `tmp` (as `mark :: reversed bits`). -/
def skipF (lS : Lens σ (Option Sym)) (src tmp : Loc na nb) : Prog (Loc na nb) (fun _ => Sym) σ :=
  .seq (moveBlk lS src tmp) (moveTop lS src tmp)

/-- Move one header field back from `tmp` to `src`. -/
def unskipF (lS : Lens σ (Option Sym)) (tmp src : Loc na nb) : Prog (Loc na nb) (fun _ => Sym) σ :=
  .seq (moveTop lS tmp src) (moveBlk lS tmp src)

theorem skipF_closed (lS : Lens σ (Option Sym)) (src tmp : Loc na nb) :
    (skipF lS src tmp).Closed := ⟨moveBlk_closed lS src tmp, moveTop_closed lS src tmp⟩

theorem unskipF_closed (lS : Lens σ (Option Sym)) (tmp src : Loc na nb) :
    (unskipF lS tmp src).Closed := ⟨moveTop_closed lS tmp src, moveBlk_closed lS tmp src⟩

theorem HT.skipF (lS : Lens σ (Option Sym)) {src tmp : Loc na nb} (hne : src ≠ tmp)
    (B : Loc na nb → List Sym) (v : ℕ) (r : List Sym) (hB : B src = natSyms v ++ Sym.mark :: r) :
    HT [] B (skipF lS src tmp)
      (Function.update (Function.update B src r) tmp
        (Sym.mark :: ((Computability.encodeNat v).reverse.map Sym.bit ++ B tmp)))
      (3 * bitLen v + 6) := by
  have h1 := HT.moveBlk lS hne B (Computability.encodeNat v) (Sym.mark :: r) (TermOK.cons rfl r) hB
  refine (HT.seq h1 (HT.moveTop lS hne _ Sym.mark r
    (by rw [Function.update_of_ne hne, Function.update_self]))).of_eq ?_
    (by simp only [bitLen]; omega)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem HT.unskipF (lS : Lens σ (Option Sym)) {src tmp : Loc na nb} (hne : src ≠ tmp)
    (B : Loc na nb → List Sym) (v : ℕ) (rt : List Sym) (hrt : TermOK rt)
    (hB : B tmp = Sym.mark :: ((Computability.encodeNat v).reverse.map Sym.bit ++ rt)) :
    HT [] B (unskipF lS tmp src)
      (Function.update (Function.update B tmp rt) src (natSyms v ++ Sym.mark :: B src))
      (3 * bitLen v + 6) := by
  have h1 := HT.moveTop lS (Ne.symm hne) B Sym.mark _ hB
  have h2 := HT.moveBlk lS (Ne.symm hne)
    (Function.update (Function.update B tmp
      ((Computability.encodeNat v).reverse.map Sym.bit ++ rt)) src (Sym.mark :: B src))
    (Computability.encodeNat v).reverse rt hrt
    (by rw [Function.update_of_ne (Ne.symm hne), Function.update_self])
  refine (HT.seq h1 h2).of_eq ?_ (by simp only [bitLen, List.length_reverse]; omega)
  funext k
  simp only [Function.update_apply, List.reverse_reverse, natSyms]
  split_ifs <;> simp_all

end Skip

/-- `sQ += q`, `sH += 2^(q-1)`, `sH1 += 2^(q-1) - 1`, `q = 2b + 2K0 + 8`. -/
def initK (J : SqI) : Prog HL (fun _ => Sym) J.Reg :=
  (callI J.cp [hC0, sA] dfl J.lCp).seq <|
  (skipF J.lS hC0 sT1).seq <|
  (callI J.an [sA, hC0, sQ] dfl J.lAn).seq <|
  (unskipF J.lS sT1 hC0).seq <|
  (callI J.dr [sA] dfl J.lDr).seq <|
  (callI J.inc [sQ] dfl J.lInc).seq <| (callI J.inc [sQ] dfl J.lInc).seq <|
  (callI J.inc [sQ] dfl J.lInc).seq <| (callI J.inc [sQ] dfl J.lInc).seq <|
  (pushS sQ (.bit false)).seq <|
  (pushS sH (.bit true)).seq <|
  (callI J.sl [sH, sQ] dfl J.lSl).seq <|
  (popS sH).seq <|
  (callI J.cp [sH, sH1] dfl J.lCp).seq
  (callI J.dec [sH1] dfl J.lDec)

theorem initK_closed (J : SqI) : (initK J).Closed :=
  ⟨callI_closed _ _ _ _, skipF_closed _ _ _, callI_closed _ _ _ _, unskipF_closed _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, trivial, trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _,
    callI_closed _ _ _ _⟩


theorem hdrSyms_four_sq (b K0 k1 k2 : ℕ) (r0 : List Sym) :
    hdrSyms [b, K0, k1, k2] ++ r0 = natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark ::
      (natSyms k1 ++ Sym.mark :: (natSyms k2 ++ Sym.mark :: r0))) := by
  simp [hdrSyms]

set_option maxHeartbeats 400000 in
/-- **INIT phase.** -/
theorem initK_spec (J : SqI) {Mul : ℕ → ℕ} {C : ℕ} (hJ : SqI.Spec Mul J C) (B : HL → List Sym)
    (b K0 k1 k2 : ℕ) (r0 : List Sym) (hC0 : B hC0 = hdrSyms [b, K0, k1, k2] ++ r0)
    (tQ : TermOK (B sQ)) (tH : TermOK (B sH)) (tH1 : TermOK (B sH1)) (tA : TermOK (B sA))
    (tT1 : TermOK (B sT1)) :
    HT [] B (initK J)
      (Function.update (Function.update (Function.update B sQ
        (natSyms (2 * b + 2 * K0 + 8) ++ B sQ)) sH (natSyms (2 ^ (2 * b + 2 * K0 + 7)) ++ B sH))
        sH1 (natSyms (2 ^ (2 * b + 2 * K0 + 7) - 1) ++ B sH1))
      (100 * (C + 1) * (b + K0 + 1)) := by
  rw [hdrSyms_four_sq] at hC0
  have vq : natSyms (2 * b + 2 * K0 + 8) = Sym.bit false :: natSyms (b + K0 + 1 + 1 + 1 + 1) := by
    rw [show 2 * b + 2 * K0 + 8 = 2 * (b + K0 + 1 + 1 + 1 + 1) by ring]
    exact natSyms_double (by omega)
  have vh : natSyms (2 ^ (2 * b + 2 * K0 + 8)) =
      Sym.bit false :: natSyms (2 ^ (2 * b + 2 * K0 + 7)) := by
    rw [show 2 * b + 2 * K0 + 8 = (2 * b + 2 * K0 + 7) + 1 by ring]
    exact natSyms_two_pow_succ _
  have vd : 2 ^ (2 * b + 2 * K0 + 7) - 1 + 1 = 2 ^ (2 * b + 2 * K0 + 7) :=
    Nat.sub_add_cancel Nat.one_le_two_pow
  refine (HT.seq (HT.copyNat hJ.cp dfl J.lCp WP.W9sq.hC0 sA (by decide) (by norm_num) B b
      (Sym.mark :: (natSyms K0 ++ Sym.mark :: (natSyms k1 ++ Sym.mark ::
        (natSyms k2 ++ Sym.mark :: r0)))) (TermOK.cons rfl _) hC0 []) <|
    HT.seq (HT.skipF J.lS (src := WP.W9sq.hC0) (tmp := sT1) (by decide) _ b
      (natSyms K0 ++ Sym.mark :: (natSyms k1 ++ Sym.mark :: (natSyms k2 ++ Sym.mark :: r0)))
      (by simp [hC0])) <|
    HT.seq (HT.addNat hJ.an dfl J.lAn sA WP.W9sq.hC0 sQ (by decide) (by norm_num) _ b K0 (B sA)
      (Sym.mark :: (natSyms k1 ++ Sym.mark :: (natSyms k2 ++ Sym.mark :: r0))) tA
      (TermOK.cons rfl _) (by simp) (by simp) []) <|
    HT.seq (HT.unskipF J.lS (src := WP.W9sq.hC0) (tmp := sT1) (by decide) _ b (B sT1) tT1
      (by simp)) <|
    HT.seq (HT.dropNat hJ.dr dfl J.lDr sA (by norm_num) _ b (B sA) tA (by simp) []) <|
    HT.seq (HT.inc hJ.inc dfl J.lInc sQ (by norm_num) _ (b + K0) (B sQ) tQ (by simp) []) <|
    HT.seq (HT.inc hJ.inc dfl J.lInc sQ (by norm_num) _ (b + K0 + 1) (B sQ) tQ (by simp) []) <|
    HT.seq (HT.inc hJ.inc dfl J.lInc sQ (by norm_num) _ (b + K0 + 1 + 1) (B sQ) tQ
      (by simp) []) <|
    HT.seq (HT.inc hJ.inc dfl J.lInc sQ (by norm_num) _ (b + K0 + 1 + 1 + 1) (B sQ) tQ
      (by simp) []) <|
    HT.seq (HT.pushS sQ (.bit false) _ []) <|
    HT.seq (HT.pushS sH (.bit true) _ []) <|
    HT.seq (HT.shlVar hJ.sl dfl J.lSl sH sQ (by decide) (by norm_num) _ 1 (2 * b + 2 * K0 + 8)
      (B sH) (B sQ) tH tQ (by simp [natSyms_one']) (by simp [vq]) []) <|
    HT.seq (HT.popS sH _ (Sym.bit false) (natSyms (2 ^ (2 * b + 2 * K0 + 7)) ++ B sH)
      (by simp [vh]) []) <|
    HT.seq (HT.copyNat hJ.cp dfl J.lCp sH sH1 (by decide) (by norm_num) _
      (2 ^ (2 * b + 2 * K0 + 7)) (B sH) tH (by simp) []) <|
    HT.dec hJ.dec dfl J.lDec sH1 (by norm_num) _ (2 ^ (2 * b + 2 * K0 + 7) - 1) (B sH1) tH1
      (by simp [vd]) []).of_eq ?_ ?_
  · funext k
    by_cases e1 : k = sA
    · subst e1; simp
    by_cases e2 : k = WP.W9sq.hC0
    · subst e2; simp [hC0]
    by_cases e3 : k = sT1
    · subst e3; simp
    by_cases e4 : k = sQ
    · subst e4; simp [vq]
    by_cases e5 : k = sH
    · subst e5; simp
    by_cases e6 : k = sH1
    · subst e6; simp
    simp [e1, e2, e3, e4, e5, e6]
  · rw [vd, bitLen_two_pow]
    have f1 := bitLen_le_self b
    have f2 := bitLen_le_self K0
    have f7 := bitLen_le_self (2 * b + 2 * K0 + 8)
    have f3 : ones (Computability.encodeNat (b + K0)) ≤ b + K0 :=
      le_trans (ones_le_length _) (bitLen_le_self _)
    have f4 : ones (Computability.encodeNat (b + K0 + 1)) ≤ b + K0 + 1 :=
      le_trans (ones_le_length _) (bitLen_le_self _)
    have f5 : ones (Computability.encodeNat (b + K0 + 1 + 1)) ≤ b + K0 + 1 + 1 :=
      le_trans (ones_le_length _) (bitLen_le_self _)
    have f6 : ones (Computability.encodeNat (b + K0 + 1 + 1 + 1)) ≤ b + K0 + 1 + 1 + 1 :=
      le_trans (ones_le_length _) (bitLen_le_self _)
    have f9 : zerosLead (Computability.encodeNat (2 ^ (2 * b + 2 * K0 + 7))) ≤
        2 * b + 2 * K0 + 7 + 1 :=
      le_trans (zerosLead_le_length _) (le_of_eq (bitLen_two_pow _))
    generalize bitLen b = Lb at *
    generalize bitLen K0 = LK at *
    generalize bitLen (2 * b + 2 * K0 + 8) = Lq at *
    generalize ones (Computability.encodeNat (b + K0)) = o0 at *
    generalize ones (Computability.encodeNat (b + K0 + 1)) = o1 at *
    generalize ones (Computability.encodeNat (b + K0 + 1 + 1)) = o2 at *
    generalize ones (Computability.encodeNat (b + K0 + 1 + 1 + 1)) = o3 at *
    generalize zerosLead (Computability.encodeNat (2 ^ (2 * b + 2 * K0 + 7))) = Z at *
    have p1 := Nat.mul_le_mul_left C f1
    have p2 := Nat.mul_le_mul_left C f2
    have p3 := Nat.mul_le_mul_left C f3
    have p4 := Nat.mul_le_mul_left C f4
    have p5 := Nat.mul_le_mul_left C f5
    have p6 := Nat.mul_le_mul_left C f6
    have p7 := Nat.mul_le_mul_left C f7
    have p9 := Nat.mul_le_mul_left C f9
    ring_nf at p1 p2 p3 p4 p5 p6 p7 p9 ⊢
    omega

#assert_std_axioms skipF_closed unskipF_closed HT.skipF HT.unskipF initK_closed hdrSyms_four_sq
  initK_spec

end WP.W9sq
