import WP.W9g.FFT

/-!
# WP.W9g.TopA — setup of the leaf kernel

* `hdrProg`: copy the header fields `p, K, q` of `C0` and `p_in` of `C1` onto `HP`, `HK`, `HQ`,
  `HPin` (each above a `mark`); `C0` is opened field by field and closed again.
* `paramsProg`: the butterfly counters `Q2 = q + 2` and `ONE = 1`.
* `dirshProg X a b`: the rescale parameters for `a → b`... precisely: `SH = |A − B|` and
  `DIR = sgnSym (A − B)` from the naturals `A`, `B` on `a`, `b` (one W3 signed subtraction). With
  `(A, B) = (q, p_in)` this is the F1 rescale `p_in → q`; with `(p, q)` the F4 rescale `q → p`
  (`dirSym_sub`, `rescLD_sub`).
* `marksProg`: a `mark` under every terminated temporary of the butterfly and rescale kernels, the
  stage counter `CS = K`, and the guard on `TL`.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Rescale parameters from a signed difference -/

theorem dirSym_sub (a b : ℕ) : dirSym (decide (b ≤ a)) = sgnSym ((a : ℤ) - b) := by
  unfold dirSym sgnSym
  by_cases h : b ≤ a
  · have h' : ¬ ((a : ℤ) - b < 0) := by omega
    simp [h, h']
  · have h' : (a : ℤ) - b < 0 := by omega
    simp [h, h']

theorem rescLD_sub (pin q : ℕ) (a : ℤ) :
    rescLD (decide (pin ≤ q)) ((q : ℤ) - pin).natAbs a = rescV pin q a := by
  unfold rescLD rescV
  by_cases h : pin ≤ q
  · have e : ((q : ℤ) - pin).natAbs = q - pin := by omega
    simp [h, e]
  · have e : ((q : ℤ) - pin).natAbs = pin - q := by omega
    simp [h, e]

/-! ## Non-duplicating step rules (the old value of the written stack is given explicitly) -/

section StepsX

variable {K τ : Type} [DecidableEq K]

theorem pushC_rs' (k : K) (x : Sym) (σ : K → List Sym) (l : List Sym) (h : σ k = l) :
    RS [] (lm (pushC k x) : MProg K τ) σ (Function.update σ k (x :: l)) 1 := by
  subst h
  exact pushC_rs k x σ

theorem copyNat_rs' {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (n : ℕ) (rest : List Sym) (σ : K → List Sym) (l : List Sym) (hr : TermOK rest)
    (h : σ src = natSyms n ++ rest) (hl : σ dst = l) :
    RS [] (lm (copyBlock src dst tmp) : MProg K τ) σ (Function.update σ dst (natSyms n ++ l))
      (7 * bitLen n + 7) := by
  subst hl
  exact copyNat_rs hsd hst hdt n rest σ hr h

end StepsX

/-! ## Programs -/

theorem incS_closed (k t : Stk) : (inc k t : SProg Stk).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, inc, scanLoop, scanBody, incFix, restoreR, pushC, popR, pushR,
    skip, moveBits, moveBitsBody]

section Prog

variable {τ : Type}

/-- Copy the header fields onto `HP`, `HK`, `HQ`, `HPin`. -/
def hdrProg : MProg Stk τ :=
  (.seq (lm (pushC .HP .mark)) (.seq (lm (copyBlock .C0 .HP .CT)) (.seq (lm (WP.W6a.dropBits .C0)) (.seq (lm (popR .C0)) (.seq (lm (pushC .HK .mark)) (.seq (lm (copyBlock .C0 .HK .CT)) (.seq (lm (WP.W6a.dropBits .C0)) (.seq (lm (popR .C0)) (.seq (lm (pushC .HQ .mark)) (.seq (lm (copyBlock .C0 .HQ .CT)) (.seq (lm (pushC .C0 .mark)) (.seq (lm (copyBlock .HK .C0 .CT)) (.seq (lm (pushC .C0 .mark)) (.seq (lm (copyBlock .HP .C0 .CT)) (.seq (lm (pushC .HPin .mark)) (lm (copyBlock .C1 .HPin .CT)))))))))))))))))

/-- `Q2 = q + 2`, `ONE = 1`. -/
def paramsProg : MProg Stk τ :=
  (.seq (lm (pushC .Q2 .mark)) (.seq (lm (copyBlock .HQ .Q2 .CT)) (.seq (lm (inc .Q2 .CT)) (.seq (lm (inc .Q2 .CT)) (.seq (lm (pushC .ONE .mark)) (lm (pushC .ONE (.bit true))))))))

/-- Marks under the terminated temporaries; `CS = K`; the guard on `TL`. -/
def marksProg : MProg Stk τ :=
  (.seq (lm (pushC .Ra .mark)) (.seq (lm (pushC .Rc .mark)) (.seq (lm (pushC .Rd .mark)) (.seq (lm (pushC .Na .mark)) (.seq (lm (pushC .Nc .mark)) (.seq (lm (pushC .Nd .mark)) (.seq (lm (pushC .Ne .mark)) (.seq (lm (pushC .Nf .mark)) (.seq (lm (pushC .X1 .mark)) (.seq (lm (pushC .X2 .mark)) (.seq (lm (pushC .X5 .mark)) (.seq (lm (pushC .X7 .mark)) (.seq (lm (pushC .X9 .mark)) (.seq (lm (pushC .X11 .mark)) (.seq (lm (pushC .X12 .mark)) (.seq (lm (pushC .CS .mark)) (.seq (lm (copyBlock .HK .CS .CT)) (lm (pushC .TL symGuard)))))))))))))))))))

theorem hdrProg_closed : (hdrProg : MProg Stk τ).Closed := by
  simp only [hdrProg, Prog.Closed, Prog.FreeBelow]
  exact ⟨lm_closed trivial, lm_closed (copyBlockS_closed _ _ _), lm_closed (WP.W6a.closed_dropBits _),
    lm_closed trivial, lm_closed trivial, lm_closed (copyBlockS_closed _ _ _),
    lm_closed (WP.W6a.closed_dropBits _), lm_closed trivial, lm_closed trivial,
    lm_closed (copyBlockS_closed _ _ _), lm_closed trivial, lm_closed (copyBlockS_closed _ _ _),
    lm_closed trivial, lm_closed (copyBlockS_closed _ _ _), lm_closed trivial,
    lm_closed (copyBlockS_closed _ _ _)⟩

theorem paramsProg_closed : (paramsProg : MProg Stk τ).Closed :=
  ⟨lm_closed trivial, lm_closed (copyBlockS_closed _ _ _), lm_closed (incS_closed _ _),
    lm_closed (incS_closed _ _), lm_closed trivial, lm_closed trivial⟩

theorem marksProg_closed : (marksProg : MProg Stk τ).Closed :=
  ⟨lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed trivial, lm_closed (copyBlockS_closed _ _ _), lm_closed trivial⟩

end Prog

/-- The stacks written by `marksProg`. -/
def marksT : List Stk := [.Ra, .Rc, .Rd, .Na, .Nc, .Nd, .Ne, .Nf, .X1, .X2, .X5, .X7, .X9, .X11, .X12, .CS, .TL]

/-- `SH = |A − B|`, `DIR = sgnSym (A − B)` from `A` on `a` and `B` on `b`. -/
def dirshProg (X : Prims) (a b : Stk) : MProg Stk X.Reg :=
  .seq (lm (pushC a .pos)) (.seq (lm (pushC b .pos)) (.seq (lm (pushC .SH .mark))
    (.seq (callSub X .pool a b .SH) (.seq (lm (pushC .DIR .mark))
    (.seq (lm (.seq (popR .SH) (pushR .DIR))) (.seq (lm (popR a)) (lm (popR b))))))))

theorem dirshProg_closed (X : Prims) (a b : Stk) : (dirshProg X a b).Closed :=
  ⟨lm_closed trivial, lm_closed trivial, lm_closed trivial, callSub_closed _ _ _ _ _,
    lm_closed trivial, moveSym_closed _ _, lm_closed trivial, lm_closed trivial⟩

/-! ## Specs -/

section Spec

variable {τ : Type}

theorem hdr_rs (p K q pin : ℕ) (r0 r1 : List Sym) (σ0 σ : Stk → List Sym)
    (hC0 : σ .C0 = natSyms p ++ Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms q ++ Sym.mark :: r0)))
    (hC1 : σ .C1 = natSyms pin ++ Sym.mark :: r1)
    (hag : ∀ k ∈ [Stk.HP, .HK, .HQ, .HPin], σ k = σ0 k) :
    RS [] (hdrProg : MProg Stk τ) σ
      (Function.update (Function.update (Function.update (Function.update σ .HP (natSyms p ++ Sym.mark :: σ0 .HP)) .HK (natSyms K ++ Sym.mark :: σ0 .HK)) .HQ (natSyms q ++ Sym.mark :: σ0 .HQ)) .HPin (natSyms pin ++ Sym.mark :: σ0 .HPin))
      (17 * bitLen p + 17 * bitLen K + 7 * bitLen q + 7 * bitLen pin + 54) := by
  refine ((pushC_rs' (τ := τ) .HP .mark σ (σ0 .HP) (hag .HP (by decide))).seq
      ((copyNat_rs' (src := Stk.C0) (dst := Stk.HP) (tmp := Stk.CT) (by decide) (by decide) (by decide) p (Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms q ++ Sym.mark :: r0))) _ (Sym.mark :: σ0 .HP) (termOK_mark' _) (by exact hC0) (by rfl)).seq
      ((dropNat_rs .C0 p (Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms q ++ Sym.mark :: r0))) _ (termOK_mark' _) (by exact hC0)).seq
      ((popR_rs .C0 _ Sym.mark (natSyms K ++ Sym.mark :: (natSyms q ++ Sym.mark :: r0)) (by rfl)).seq
      ((pushC_rs' .HK .mark _ (σ0 .HK) (by exact hag .HK (by decide))).seq
      ((copyNat_rs' (src := Stk.C0) (dst := Stk.HK) (tmp := Stk.CT) (by decide) (by decide) (by decide) K (Sym.mark :: (natSyms q ++ Sym.mark :: r0)) _ (Sym.mark :: σ0 .HK) (termOK_mark' _) (by rfl) (by rfl)).seq
      ((dropNat_rs .C0 K (Sym.mark :: (natSyms q ++ Sym.mark :: r0)) _ (termOK_mark' _) (by rfl)).seq
      ((popR_rs .C0 _ Sym.mark (natSyms q ++ Sym.mark :: r0) (by rfl)).seq
      ((pushC_rs' .HQ .mark _ (σ0 .HQ) (by exact hag .HQ (by decide))).seq
      ((copyNat_rs' (src := Stk.C0) (dst := Stk.HQ) (tmp := Stk.CT) (by decide) (by decide) (by decide) q (Sym.mark :: r0) _ (Sym.mark :: σ0 .HQ) (termOK_mark' _) (by rfl) (by rfl)).seq
      ((pushC_rs' .C0 .mark _ (natSyms q ++ Sym.mark :: r0) (by rfl)).seq
      ((copyNat_rs' (src := Stk.HK) (dst := Stk.C0) (tmp := Stk.CT) (by decide) (by decide) (by decide) K (Sym.mark :: σ0 .HK) _ (Sym.mark :: (natSyms q ++ Sym.mark :: r0)) (termOK_mark' _) (by rfl) (by rfl)).seq
      ((pushC_rs' .C0 .mark _ (natSyms K ++ Sym.mark :: (natSyms q ++ Sym.mark :: r0)) (by rfl)).seq
      ((copyNat_rs' (src := Stk.HP) (dst := Stk.C0) (tmp := Stk.CT) (by decide) (by decide) (by decide) p (Sym.mark :: σ0 .HP) _ (Sym.mark :: (natSyms K ++ Sym.mark :: (natSyms q ++ Sym.mark :: r0))) (termOK_mark' _) (by rfl) (by rfl)).seq
      ((pushC_rs' .HPin .mark _ (σ0 .HPin) (by exact hag .HPin (by decide))).seq
      (copyNat_rs' (src := Stk.C1) (dst := Stk.HPin) (tmp := Stk.CT) (by decide) (by decide) (by decide) pin (Sym.mark :: r1) _ (Sym.mark :: σ0 .HPin) (termOK_mark' _) (by exact hC1) (by rfl))))))))))))))))).congr ?_ ?_
  · funext k
    cases k <;> first | rfl | exact hC0.symm
  · omega

theorem params_rs (q : ℕ) (hq : List Sym) (σ0 σ : Stk → List Sym)
    (hHQ : σ .HQ = natSyms q ++ Sym.mark :: hq) (hag : ∀ k ∈ [Stk.Q2, .ONE], σ k = σ0 k) :
    RS [] (paramsProg : MProg Stk τ) σ
      (Function.update (Function.update σ .Q2 (natSyms (q + 1 + 1) ++ Sym.mark :: σ0 .Q2)) .ONE (Sym.bit true :: Sym.mark :: σ0 .ONE))
      (19 * bitLen (q + 1) + 28) := by
  refine ((pushC_rs' (τ := τ) .Q2 .mark σ (σ0 .Q2) (hag .Q2 (by decide))).seq
      ((copyNat_rs' (src := Stk.HQ) (dst := Stk.Q2) (tmp := Stk.CT) (by decide) (by decide) (by decide) q (Sym.mark :: hq) _ (Sym.mark :: σ0 .Q2) (termOK_mark' _) (by exact hHQ) (by rfl)).seq
      ((inc_rs (k := Stk.Q2) (t := Stk.CT) (by decide) q (Sym.mark :: σ0 .Q2) _ (termOK_mark' _) (by rfl)).seq
      ((inc_rs (k := Stk.Q2) (t := Stk.CT) (by decide) (q + 1) (Sym.mark :: σ0 .Q2) _ (termOK_mark' _) (by rfl)).seq
      ((pushC_rs' .ONE .mark _ (σ0 .ONE) (by exact hag .ONE (by decide))).seq
      (pushC_rs' .ONE (.bit true) _ (Sym.mark :: σ0 .ONE) (by rfl))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · have := bitLen_mono' (Nat.le_add_right q 1)
    omega

theorem marks_rs (K : ℕ) (hk : List Sym) (σ0 σ : Stk → List Sym)
    (hHK : σ .HK = natSyms K ++ Sym.mark :: hk) (hag : ∀ k ∈ marksT, σ k = σ0 k) :
    RS [] (marksProg : MProg Stk τ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ .Ra (Sym.mark :: σ0 .Ra)) .Rc (Sym.mark :: σ0 .Rc)) .Rd (Sym.mark :: σ0 .Rd)) .Na (Sym.mark :: σ0 .Na)) .Nc (Sym.mark :: σ0 .Nc)) .Nd (Sym.mark :: σ0 .Nd)) .Ne (Sym.mark :: σ0 .Ne)) .Nf (Sym.mark :: σ0 .Nf)) .X1 (Sym.mark :: σ0 .X1)) .X2 (Sym.mark :: σ0 .X2)) .X5 (Sym.mark :: σ0 .X5)) .X7 (Sym.mark :: σ0 .X7)) .X9 (Sym.mark :: σ0 .X9)) .X11 (Sym.mark :: σ0 .X11)) .X12 (Sym.mark :: σ0 .X12)) .CS (natSyms K ++ Sym.mark :: σ0 .CS)) .TL (symGuard :: σ0 .TL))
      (7 * bitLen K + 24) := by
  refine ((pushC_rs' (τ := τ) .Ra .mark σ (σ0 .Ra) (hag .Ra (by decide))).seq
      ((pushC_rs' .Rc .mark _ (σ0 .Rc) (by exact hag .Rc (by decide))).seq
      ((pushC_rs' .Rd .mark _ (σ0 .Rd) (by exact hag .Rd (by decide))).seq
      ((pushC_rs' .Na .mark _ (σ0 .Na) (by exact hag .Na (by decide))).seq
      ((pushC_rs' .Nc .mark _ (σ0 .Nc) (by exact hag .Nc (by decide))).seq
      ((pushC_rs' .Nd .mark _ (σ0 .Nd) (by exact hag .Nd (by decide))).seq
      ((pushC_rs' .Ne .mark _ (σ0 .Ne) (by exact hag .Ne (by decide))).seq
      ((pushC_rs' .Nf .mark _ (σ0 .Nf) (by exact hag .Nf (by decide))).seq
      ((pushC_rs' .X1 .mark _ (σ0 .X1) (by exact hag .X1 (by decide))).seq
      ((pushC_rs' .X2 .mark _ (σ0 .X2) (by exact hag .X2 (by decide))).seq
      ((pushC_rs' .X5 .mark _ (σ0 .X5) (by exact hag .X5 (by decide))).seq
      ((pushC_rs' .X7 .mark _ (σ0 .X7) (by exact hag .X7 (by decide))).seq
      ((pushC_rs' .X9 .mark _ (σ0 .X9) (by exact hag .X9 (by decide))).seq
      ((pushC_rs' .X11 .mark _ (σ0 .X11) (by exact hag .X11 (by decide))).seq
      ((pushC_rs' .X12 .mark _ (σ0 .X12) (by exact hag .X12 (by decide))).seq
      ((pushC_rs' .CS .mark _ (σ0 .CS) (by exact hag .CS (by decide))).seq
      ((copyNat_rs' (src := Stk.HK) (dst := Stk.CS) (tmp := Stk.CT) (by decide) (by decide) (by decide) K (Sym.mark :: hk) _ (Sym.mark :: σ0 .CS) (termOK_mark' _) (by exact hHK) (by rfl)).seq
      (pushC_rs' .TL symGuard _ (σ0 .TL) (by exact hag .TL (by decide)))))))))))))))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · omega

end Spec

theorem dirshQ_rs {X : Prims} {CS : ℕ} (hS : SubOK X.sub CS) (A B : ℕ) (ra rb : List Sym)
    (σ0 σ : Stk → List Sym) (hA : σ .HQ = natSyms A ++ Sym.mark :: ra)
    (hB : σ .HPin = natSyms B ++ Sym.mark :: rb) (hag : ∀ k ∈ [Stk.SH, .DIR], σ k = σ0 k) :
    RS [] (dirshProg X .HQ .HPin) σ
      (Function.update (Function.update (Function.update (Function.update σ
        .HQ (natSyms A ++ Sym.mark :: ra)) .HPin (natSyms B ++ Sym.mark :: rb))
        .SH (natSyms ((A : ℤ) - B).natAbs ++ Sym.mark :: σ0 .SH))
        .DIR (sgnSym ((A : ℤ) - B) :: Sym.mark :: σ0 .DIR))
      (CS * (bitLen A + bitLen B + 1) + 8) := by
  refine ((pushC_rs' (τ := X.Reg) .HQ .pos σ (natSyms A ++ Sym.mark :: ra) hA).seq
      ((pushC_rs' .HPin .pos _ (natSyms B ++ Sym.mark :: rb) (by exact hB)).seq
      ((pushC_rs' .SH .mark _ (σ0 .SH) (by exact hag .SH (by decide))).seq
      ((callSub_rs (x := Stk.HQ) (y := Stk.HPin) (z := Stk.SH) hS pool_inj (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (A : ℤ) (B : ℤ) (Sym.mark :: ra) (Sym.mark :: rb) _ (termOK_mark' _) (termOK_mark' _) (by rw [intSyms_natCast]; rfl) (by rw [intSyms_natCast]; rfl)).seq
      ((pushC_rs' .DIR .mark _ (σ0 .DIR) (by exact hag .DIR (by decide))).seq
      ((moveSym_rs (src := Stk.SH) (dst := Stk.DIR) (by decide) _ (sgnSym ((A : ℤ) - B)) (natSyms ((A : ℤ) - B).natAbs ++ Sym.mark :: σ0 .SH) (by rfl)).seq
      ((popR_rs .HQ _ Sym.pos (natSyms A ++ Sym.mark :: ra) (by rfl)).seq
      (popR_rs .HPin _ Sym.pos (natSyms B ++ Sym.mark :: rb) (by rfl))))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · simp only [Int.natAbs_natCast]
    omega

theorem dirshP_rs {X : Prims} {CS : ℕ} (hS : SubOK X.sub CS) (A B : ℕ) (ra rb : List Sym)
    (σ0 σ : Stk → List Sym) (hA : σ .HP = natSyms A ++ Sym.mark :: ra)
    (hB : σ .HQ = natSyms B ++ Sym.mark :: rb) (hag : ∀ k ∈ [Stk.SH, .DIR], σ k = σ0 k) :
    RS [] (dirshProg X .HP .HQ) σ
      (Function.update (Function.update (Function.update (Function.update σ
        .HP (natSyms A ++ Sym.mark :: ra)) .HQ (natSyms B ++ Sym.mark :: rb))
        .SH (natSyms ((A : ℤ) - B).natAbs ++ Sym.mark :: σ0 .SH))
        .DIR (sgnSym ((A : ℤ) - B) :: Sym.mark :: σ0 .DIR))
      (CS * (bitLen A + bitLen B + 1) + 8) := by
  refine ((pushC_rs' (τ := X.Reg) .HP .pos σ (natSyms A ++ Sym.mark :: ra) hA).seq
      ((pushC_rs' .HQ .pos _ (natSyms B ++ Sym.mark :: rb) (by exact hB)).seq
      ((pushC_rs' .SH .mark _ (σ0 .SH) (by exact hag .SH (by decide))).seq
      ((callSub_rs (x := Stk.HP) (y := Stk.HQ) (z := Stk.SH) hS pool_inj (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (A : ℤ) (B : ℤ) (Sym.mark :: ra) (Sym.mark :: rb) _ (termOK_mark' _) (termOK_mark' _) (by rw [intSyms_natCast]; rfl) (by rw [intSyms_natCast]; rfl)).seq
      ((pushC_rs' .DIR .mark _ (σ0 .DIR) (by exact hag .DIR (by decide))).seq
      ((moveSym_rs (src := Stk.SH) (dst := Stk.DIR) (by decide) _ (sgnSym ((A : ℤ) - B)) (natSyms ((A : ℤ) - B).natAbs ++ Sym.mark :: σ0 .SH) (by rfl)).seq
      ((popR_rs .HP _ Sym.pos (natSyms A ++ Sym.mark :: ra) (by rfl)).seq
      (popR_rs .HQ _ Sym.pos (natSyms B ++ Sym.mark :: rb) (by rfl))))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · simp only [Int.natAbs_natCast]
    omega

#assert_std_axioms pushC_rs' copyNat_rs' dirSym_sub rescLD_sub incS_closed hdrProg_closed paramsProg_closed marksProg_closed
  dirshProg_closed hdr_rs params_rs marks_rs dirshQ_rs dirshP_rs

end WP.W9g
