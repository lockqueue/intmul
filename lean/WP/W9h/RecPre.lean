import WP.W9h.RecProg

/-!
# WP.W9h.RecPre — the prelude of `W9_reconstruct`: fetch `b`, count `n = k2 + k1`, floors
-/

namespace WP.W9h

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-- The header on `C0`, field by field. -/
theorem hdrSyms_four (b K0 k1 k2 : ℕ) (r0 : List Sym) :
    hdrSyms [b, K0, k1, k2] ++ r0 = natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark ::
      (natSyms k1 ++ Sym.mark :: (natSyms k2 ++ Sym.mark :: r0))) := by
  simp [hdrSyms]

theorem termOK_mark' (l : List Sym) : TermOK (Sym.mark :: l) := TermOK.cons rfl l

namespace Kit

variable {K : Kit} {C : ℕ} (hK : K.Spec C)
include hK

theorem HT_recFetchB (B : H → List Sym) (b : ℕ) (r : List Sym)
    (hc0 : B hC0 = natSyms b ++ Sym.mark :: r) :
    HT [] B K.recFetchB (Function.update B rB (natSyms b ++ Sym.mark :: B rB))
      (1 + C * (bitLen b + 1)) := by
  refine (HT.seq (Kit.HT_push (K := K) rB .mark B)
    (Kit.HT_cp hK (x := hC0) (y := rB) (by decide) _ b (.mark :: r) (termOK_mark' _)
      (by rw [Function.update_of_ne (by decide)]; exact hc0))).of_eq ?_ le_rfl
  rw [Function.update_idem, Function.update_self]

set_option maxHeartbeats 400000 in
theorem HT_recCount (B : H → List Sym) (b K0 k1 k2 : ℕ) (r0 : List Sym)
    (hc0 : B hC0 = natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark ::
      (natSyms k1 ++ Sym.mark :: (natSyms k2 ++ Sym.mark :: r0)))) :
    HT [] B K.recCount
      (Function.update (Function.update B rCT (natSyms (k2 + k1) ++ Sym.mark :: B rCT)) rCT2
        (natSyms (k2 + k1) ++ Sym.mark :: B rCT2))
      (C * (4 * bitLen k1 + 2 * bitLen k2 + 5) + 6 * (bitLen b + bitLen K0 + bitLen k1) + 43) := by
  refine (HT.seq (Kit.HT_push (K := K) rTMP .mark B) <|
    HT.seq (HT.skipF K.lS (src := hC0) (tmp := rTMP) (by decide) _ b
      (natSyms K0 ++ Sym.mark :: (natSyms k1 ++ Sym.mark :: (natSyms k2 ++ Sym.mark :: r0)))
      (by simp [hc0])) <|
    HT.seq (HT.skipF K.lS (src := hC0) (tmp := rTMP) (by decide) _ K0
      (natSyms k1 ++ Sym.mark :: (natSyms k2 ++ Sym.mark :: r0)) (by simp)) <|
    HT.seq (Kit.HT_push (K := K) rK1 .mark _) <|
    HT.seq (Kit.HT_cp hK (x := hC0) (y := rK1) (by decide) _ k1
      (Sym.mark :: (natSyms k2 ++ Sym.mark :: r0)) (termOK_mark' _) (by simp)) <|
    HT.seq (HT.skipF K.lS (src := hC0) (tmp := rTMP) (by decide) _ k1
      (natSyms k2 ++ Sym.mark :: r0) (by simp)) <|
    HT.seq (Kit.HT_push (K := K) rCT .mark _) <|
    HT.seq (Kit.HT_ad hK (x := hC0) (y := rK1) (z := rCT) (by decide) _ k2 k1 (Sym.mark :: r0)
      (Sym.mark :: B rK1) (termOK_mark' _) (termOK_mark' _) (by simp) (by simp)) <|
    HT.seq (HT.unskipF K.lS (src := hC0) (tmp := rTMP) (by decide) _ k1
      (Sym.mark :: ((Computability.encodeNat K0).reverse.map Sym.bit ++ Sym.mark ::
        ((Computability.encodeNat b).reverse.map Sym.bit ++ Sym.mark :: B rTMP)))
      (termOK_mark' _) (by simp)) <|
    HT.seq (HT.unskipF K.lS (src := hC0) (tmp := rTMP) (by decide) _ K0
      (Sym.mark :: ((Computability.encodeNat b).reverse.map Sym.bit ++ Sym.mark :: B rTMP))
      (termOK_mark' _) (by simp)) <|
    HT.seq (HT.unskipF K.lS (src := hC0) (tmp := rTMP) (by decide) _ b (Sym.mark :: B rTMP)
      (termOK_mark' _) (by simp)) <|
    HT.seq (Kit.HT_pop (K := K) rTMP _ .mark (B rTMP) (by simp)) <|
    HT.seq (Kit.HT_dr hK rK1 _ k1 (Sym.mark :: B rK1) (termOK_mark' _) (by simp)) <|
    HT.seq (Kit.HT_pop (K := K) rK1 _ .mark (B rK1) (by simp)) <|
    HT.seq (Kit.HT_push (K := K) rCT2 .mark _) <|
    Kit.HT_cp hK (x := rCT) (y := rCT2) (by decide) _ (k2 + k1) (Sym.mark :: B rCT)
      (termOK_mark' _) (by simp)).of_eq ?_ ?_
  · funext k
    by_cases e1 : k = rTMP
    · subst e1; simp
    by_cases e2 : k = hC0
    · subst e2; simp [hc0]
    by_cases e3 : k = rK1
    · subst e3; simp
    by_cases e4 : k = rCT
    · subst e4; simp
    by_cases e5 : k = rCT2
    · subst e5; simp
    simp [e1, e2, e3, e4, e5]
  · have h1 : C * (bitLen (k2 + k1) + 1) ≤ C * (bitLen k1 + bitLen k2 + 2) :=
      Nat.mul_le_mul_left _ (by have := bitLen_add_le k2 k1; omega)
    ring_nf at h1 ⊢
    omega

omit hK in
theorem HT_recInit (B : H → List Sym) :
    HT [] B K.recInit
      (Function.update (Function.update B rCR (.mark :: B rCR)) rT (.mark :: B rT)) 2 :=
  (HT.seq (Kit.HT_push (K := K) rCR .mark B) (Kit.HT_push (K := K) rT .mark _)).of_eq
    (by rw [Function.update_of_ne (show rT ≠ rCR by decide)]) le_rfl

end Kit

#assert_std_axioms hdrSyms_four Kit.HT_recFetchB Kit.HT_recCount Kit.HT_recInit

end WP.W9h
