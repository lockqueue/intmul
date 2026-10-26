import WP.W9g.Stk

/-!
# WP.W9g.Bfly — one butterfly cell on the machine

`bflyProg` reads `y0 = (a, b)` (top of `A2`), `y1 = (e, f)` (top of `B2`) and the twiddle
`ω = (c, d)` (top of `Om`), all non-destructively, and pushes the entry
`cellV (q+2) y0 y1 ω = (drp (a + drp (c·e − d·f) (q+2)) 1, drp (b + drp (c·f + d·e) (q+2)) 1)`
onto `R` (PCP:2181-2185: `costedGMulScaled (q+2)` then `costedButterflyAvg`). Four W5 products, the
linear arithmetic with W3. Every temporary is restored.

Structure: `loadC` (coordinates of `ω`, `y1`), `reBlk`/`imBlk` (one output coordinate each; every
temporary of a block is dropped inside the block), unload, `packEntry`.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Size and cost facts -/

theorem natAbs_drp_le (x : ℤ) (s : ℕ) : (drp x s).natAbs ≤ x.natAbs + 2 ^ s := by
  unfold drp
  split_ifs with h
  · exact Nat.le_add_right _ _
  · have h1 := natAbs_fdiv_le (x + ((2 ^ (s - 1) : ℕ) : ℤ)) s
    have h2 := Int.natAbs_add_le x ((2 ^ (s - 1) : ℕ) : ℤ)
    have h3 : 2 ^ (s - 1) ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : (((2 ^ (s - 1) : ℕ) : ℤ)).natAbs = 2 ^ (s - 1) := rfl
    rw [h4] at h2
    exact h1.trans (h2.trans (Nat.add_le_add_left h3 _))

theorem bitLen_drp_le (x : ℤ) (s : ℕ) : bitLen (drp x s).natAbs ≤ bitLen x.natAbs + s + 2 := by
  have h1 := bitLen_mono' (natAbs_drp_le x s)
  have h2 := bitLen_add_le x.natAbs (2 ^ s)
  rw [bitLen_two_pow] at h2
  omega

theorem drCost_mono {CL CA CR L L' s s' : ℕ} (hL : L ≤ L') (hs : s ≤ s') :
    drCost CL CA CR L s ≤ drCost CL CA CR L' s' := by
  unfold drCost
  have h1 := Nat.mul_le_mul_left CL (show 2 * s ≤ 2 * s' by omega)
  have h2 := Nat.mul_le_mul_left CA (show L + s + 1 ≤ L' + s' + 1 by omega)
  have h3 := Nat.mul_le_mul_left CR (show L + 2 * s + 2 ≤ L' + 2 * s' + 2 by omega)
  omega

theorem entrySyms_append (a b : ℤ) (r : List Sym) :
    entrySyms (a, b) ++ r = intSyms a ++ Sym.sep2 :: (intSyms b ++ Sym.sep :: r) := by
  simp [entrySyms]

theorem termOK_sep2 (l : List Sym) : TermOK (Sym.sep2 :: l) := TermOK.cons rfl l

/-- Cost bound of one coordinate block. -/
def blkCost (CM CA CS CL CR : ℕ) (Mul : ℕ → ℕ) (w q : ℕ) : ℕ :=
  2 * (CM * Mul w + CM) + (CA + CS) * (4 * w + 1) + CA * (3 * w + q + 6) +
    2 * drCost CL CA CR (2 * w + q + 10) (q + 2) + 50 * w + 10 * q + 150

/-- Cost bound of one butterfly cell. -/
def bflyCost (CM CA CS CL CR : ℕ) (Mul : ℕ → ℕ) (w q : ℕ) : ℕ :=
  2 * blkCost CM CA CS CL CR Mul w q + 100 * w + 20 * q + 500

/-! ## Programs -/

section Prog

variable (X : Prims)

/-- Coordinates of the twiddle (`Nc`, `Nd`) and of `y1` (`Ne`, `Nf`). -/
def loadC : MProg Stk X.Reg :=
  (.seq (lm (copyInt .Om .Nc .T1))
  (.seq (lm (copyIm .Om .Nd .T1 .T2))
  (.seq (lm (copyInt .B2 .Ne .T1))
  (lm (copyIm .B2 .Nf .T1 .T2)))))

/-- Real coordinate: `X11 += drp (a + drp (c·e − d·f) (q+2)) 1`. -/
def reBlk : MProg Stk X.Reg :=
  (.seq (callMul X .pool .Nc .Ne .X1)
  (.seq (callMul X .pool .Nd .Nf .X2)
  (.seq (callSub X .pool .X1 .X2 .X5)
  (.seq (lm (dropInt .X2))
  (.seq (lm (dropInt .X1))
  (.seq (drS X .X5 .Q2 .X7)
  (.seq (lm (dropInt .X5))
  (.seq (lm (copyInt .A2 .Na .T1))
  (.seq (callAdd X .pool .Na .X7 .X9)
  (.seq (lm (dropInt .Na))
  (.seq (lm (dropInt .X7))
  (.seq (drS X .X9 .ONE .X11)
  (lm (dropInt .X9))))))))))))))

/-- Imaginary coordinate: `X12 += drp (b + drp (c·f + d·e) (q+2)) 1`. -/
def imBlk : MProg Stk X.Reg :=
  (.seq (callMul X .pool .Nc .Nf .X1)
  (.seq (callMul X .pool .Nd .Ne .X2)
  (.seq (callAdd X .pool .X1 .X2 .X5)
  (.seq (lm (dropInt .X2))
  (.seq (lm (dropInt .X1))
  (.seq (drS X .X5 .Q2 .X7)
  (.seq (lm (dropInt .X5))
  (.seq (lm (copyIm .A2 .Na .T1 .T2))
  (.seq (callAdd X .pool .Na .X7 .X9)
  (.seq (lm (dropInt .Na))
  (.seq (lm (dropInt .X7))
  (.seq (drS X .X9 .ONE .X12)
  (lm (dropInt .X9))))))))))))))

/-- **One butterfly cell.** -/
def bflyProg : MProg Stk X.Reg :=
  (.seq (loadC X)
  (.seq (reBlk X)
  (.seq (imBlk X)
  (.seq (lm (dropInt .Nf))
  (.seq (lm (dropInt .Ne))
  (.seq (lm (dropInt .Nd))
  (.seq (lm (dropInt .Nc))
  (.seq (lm (packEntry .X11 .X12 .R .T1))
  (.seq (lm (dropInt .X12))
  (lm (dropInt .X11)))))))))))

theorem loadC_closed : (loadC X).Closed :=
  ⟨lm_closed (copyInt_closed _ _ _), lm_closed (copyIm_closed _ _ _ _),
    lm_closed (copyInt_closed _ _ _), lm_closed (copyIm_closed _ _ _ _)⟩

theorem reBlk_closed : (reBlk X).Closed :=
  ⟨callMul_closed _ _ _ _ _, callMul_closed _ _ _ _ _, callSub_closed _ _ _ _ _,
    lm_closed (dropInt_closed _), lm_closed (dropInt_closed _), drS_closed _ _ _ _,
    lm_closed (dropInt_closed _), lm_closed (copyInt_closed _ _ _), callAdd_closed _ _ _ _ _,
    lm_closed (dropInt_closed _), lm_closed (dropInt_closed _), drS_closed _ _ _ _,
    lm_closed (dropInt_closed _)⟩

theorem imBlk_closed : (imBlk X).Closed :=
  ⟨callMul_closed _ _ _ _ _, callMul_closed _ _ _ _ _, callAdd_closed _ _ _ _ _,
    lm_closed (dropInt_closed _), lm_closed (dropInt_closed _), drS_closed _ _ _ _,
    lm_closed (dropInt_closed _), lm_closed (copyIm_closed _ _ _ _), callAdd_closed _ _ _ _ _,
    lm_closed (dropInt_closed _), lm_closed (dropInt_closed _), drS_closed _ _ _ _,
    lm_closed (dropInt_closed _)⟩

theorem bflyProg_closed : (bflyProg X).Closed :=
  ⟨loadC_closed X, reBlk_closed X, imBlk_closed X, lm_closed (dropInt_closed _),
    lm_closed (dropInt_closed _), lm_closed (dropInt_closed _), lm_closed (dropInt_closed _),
    lm_closed (packEntry_closed _ _ _ _), lm_closed (dropInt_closed _),
    lm_closed (dropInt_closed _)⟩

end Prog

/-- Number stacks of the butterfly that must have a terminator below (marks at kernel start). -/
def bfTemps : List Stk := [.Na, .Nc, .Nd, .Ne, .Nf, .X1, .X2, .X5, .X7, .X9, .X11, .X12]

theorem reBlk_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (w q : ℕ) (a b c d e f : ℤ)
    (rA rq r1 rc rd re rf : List Sym) (σ : Stk → List Sym)
    (hNc : σ .Nc = intSyms c ++ rc) (hNd : σ .Nd = intSyms d ++ rd)
    (hNe : σ .Ne = intSyms e ++ re) (hNf : σ .Nf = intSyms f ++ rf)
    (hrc : TermOK rc) (hrd : TermOK rd) (hre : TermOK re) (hrf : TermOK rf)
    (hA2 : σ .A2 = entrySyms (a, b) ++ rA)
    (hQ2 : σ .Q2 = natSyms (q + 2) ++ rq) (hrq : TermOK rq)
    (hONE : σ .ONE = natSyms 1 ++ r1) (hr1 : TermOK r1)
    (hT : ∀ k ∈ [Stk.X1, .X2, .X5, .X7, .X9, .Na], TermOK (σ k))
    (hwa : bitLen a.natAbs ≤ w) (hwc : bitLen c.natAbs ≤ w)
    (hwd : bitLen d.natAbs ≤ w) (hwe : bitLen e.natAbs ≤ w) (hwf : bitLen f.natAbs ≤ w) :
    RS [] (reBlk X) σ (Function.update σ .X11 (intSyms (drp (a + (drp (c * e - d * f) (q + 2))) 1) ++ σ .X11))
      (blkCost CM CA CS CL CR Mul w q) := by
  refine (((callMul_rs (x := .Nc) (y := .Ne) (z := .X1) hok.1 pool_inj (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w c e rc re σ hwc hwe hrc hre (by exact hNc) (by exact hNe)).seq
      ((callMul_rs (x := .Nd) (y := .Nf) (z := .X2) hok.1 pool_inj (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w d f rd rf _ hwd hwf hrd hrf (by exact hNd) (by exact hNf)).seq
      ((callSub_rs hok.2.2.1 (x := .X1) (y := .X2) (z := .X5) pool_inj (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (c * e) (d * f) (σ .X1) (σ .X2) _ (hT .X1 (by decide)) (hT .X2 (by decide)) (by rfl) (by rfl)).seq
      ((dropInt_rs .X2 (d * f) (σ .X2) _ (hT .X2 (by decide)) (by rfl)).seq
      ((dropInt_rs .X1 (c * e) (σ .X1) _ (hT .X1 (by decide)) (by rfl)).seq
      ((drS_rs hok.2.2.2.1 hok.2.1 hok.2.2.2.2 drOK_X5 (c * e - d * f) (q + 2) (σ .X5) rq _ (hT .X5 (by decide)) hrq (by rfl) (by exact hQ2)).seq
      ((dropInt_rs .X5 (c * e - d * f) (σ .X5) _ (hT .X5 (by decide)) (by rfl)).seq
      ((copyInt_rs (src := .A2) (dst := .Na) (tmp := .T1) (by decide) (by decide) (by decide) a (Sym.sep2 :: (intSyms b ++ Sym.sep :: rA)) _ (termOK_sep2 _) (by exact hA2.trans (entrySyms_append a b rA))).seq
      ((callAdd_rs (x := .Na) (y := .X7) (z := .X9) hok.2.1 pool_inj (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a (drp (c * e - d * f) (q + 2)) (σ .Na) (σ .X7) _ (hT .Na (by decide)) (hT .X7 (by decide)) (by rfl) (by rfl)).seq
      ((dropInt_rs .Na a (σ .Na) _ (hT .Na (by decide)) (by rfl)).seq
      ((dropInt_rs .X7 (drp (c * e - d * f) (q + 2)) (σ .X7) _ (hT .X7 (by decide)) (by rfl)).seq
      ((drS_rs hok.2.2.2.1 hok.2.1 hok.2.2.2.2 drOK_X9a (a + (drp (c * e - d * f) (q + 2))) 1 (σ .X9) r1 _ (hT .X9 (by decide)) hr1 (by rfl) (by exact hONE)).seq
      (dropInt_rs .X9 (a + (drp (c * e - d * f) (q + 2))) (σ .X9) _ (hT .X9 (by decide)) (by rfl))))))))))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · have hB1 : bitLen (c * e).natAbs ≤ 2 * w := by have := bitLen_natAbs_mul c e; omega
    have hB2 : bitLen (d * f).natAbs ≤ 2 * w := by have := bitLen_natAbs_mul d f; omega
    have hB5 : bitLen (c * e - d * f).natAbs ≤ 2 * w + 1 := by
      have := bitLen_natAbs_sub (c * e) (d * f); omega
    have hB7 : bitLen (drp (c * e - d * f) (q + 2)).natAbs ≤ 2 * w + q + 5 := by
      have := bitLen_drp_le (c * e - d * f) (q + 2); omega
    have hB9 : bitLen (a + (drp (c * e - d * f) (q + 2))).natAbs ≤ 2 * w + q + 6 := by
      have := bitLen_natAbs_add a (drp (c * e - d * f) (q + 2)); omega
    have h3 : CS * (bitLen (c * e).natAbs + bitLen (d * f).natAbs + 1) ≤ CS * (4 * w + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h6 : drCost CL CA CR (bitLen (c * e - d * f).natAbs) (q + 2) ≤
        drCost CL CA CR (2 * w + q + 10) (q + 2) := drCost_mono (by omega) le_rfl
    have h9 : CA * (bitLen a.natAbs + bitLen (drp (c * e - d * f) (q + 2)).natAbs + 1) ≤ CA * (3 * w + q + 6) :=
      Nat.mul_le_mul_left _ (by omega)
    have h12 : drCost CL CA CR (bitLen (a + (drp (c * e - d * f) (q + 2))).natAbs) 1 ≤
        drCost CL CA CR (2 * w + q + 10) (q + 2) := drCost_mono (by omega) (by omega)
    have hCA : (CA + CS) * (4 * w + 1) = CA * (4 * w + 1) + CS * (4 * w + 1) := Nat.add_mul _ _ _
    have hcp : 7 * bitLen a.natAbs + 12 ≤ 13 * w + 29 := by omega
    unfold blkCost
    omega

theorem imBlk_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (w q : ℕ) (a b c d e f : ℤ)
    (rA rq r1 rc rd re rf : List Sym) (σ : Stk → List Sym)
    (hNc : σ .Nc = intSyms c ++ rc) (hNd : σ .Nd = intSyms d ++ rd)
    (hNe : σ .Ne = intSyms e ++ re) (hNf : σ .Nf = intSyms f ++ rf)
    (hrc : TermOK rc) (hrd : TermOK rd) (hre : TermOK re) (hrf : TermOK rf)
    (hA2 : σ .A2 = entrySyms (a, b) ++ rA)
    (hQ2 : σ .Q2 = natSyms (q + 2) ++ rq) (hrq : TermOK rq)
    (hONE : σ .ONE = natSyms 1 ++ r1) (hr1 : TermOK r1)
    (hT : ∀ k ∈ [Stk.X1, .X2, .X5, .X7, .X9, .Na], TermOK (σ k))
    (hwa : bitLen a.natAbs ≤ w) (hwb : bitLen b.natAbs ≤ w) (hwc : bitLen c.natAbs ≤ w)
    (hwd : bitLen d.natAbs ≤ w) (hwe : bitLen e.natAbs ≤ w) (hwf : bitLen f.natAbs ≤ w) :
    RS [] (imBlk X) σ (Function.update σ .X12 (intSyms (drp (b + (drp (c * f + d * e) (q + 2))) 1) ++ σ .X12))
      (blkCost CM CA CS CL CR Mul w q) := by
  refine (((callMul_rs (x := .Nc) (y := .Nf) (z := .X1) hok.1 pool_inj (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w c f rc rf σ hwc hwf hrc hrf (by exact hNc) (by exact hNf)).seq
      ((callMul_rs (x := .Nd) (y := .Ne) (z := .X2) hok.1 pool_inj (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w d e rd re _ hwd hwe hrd hre (by exact hNd) (by exact hNe)).seq
      ((callAdd_rs hok.2.1 (x := .X1) (y := .X2) (z := .X5) pool_inj (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (c * f) (d * e) (σ .X1) (σ .X2) _ (hT .X1 (by decide)) (hT .X2 (by decide)) (by rfl) (by rfl)).seq
      ((dropInt_rs .X2 (d * e) (σ .X2) _ (hT .X2 (by decide)) (by rfl)).seq
      ((dropInt_rs .X1 (c * f) (σ .X1) _ (hT .X1 (by decide)) (by rfl)).seq
      ((drS_rs hok.2.2.2.1 hok.2.1 hok.2.2.2.2 drOK_X5 (c * f + d * e) (q + 2) (σ .X5) rq _ (hT .X5 (by decide)) hrq (by rfl) (by exact hQ2)).seq
      ((dropInt_rs .X5 (c * f + d * e) (σ .X5) _ (hT .X5 (by decide)) (by rfl)).seq
      ((copyIm_rs (src := .A2) (dst := .Na) (t1 := .T1) (t2 := .T2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a b rA _ (by exact hA2)).seq
      ((callAdd_rs (x := .Na) (y := .X7) (z := .X9) hok.2.1 pool_inj (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) b (drp (c * f + d * e) (q + 2)) (σ .Na) (σ .X7) _ (hT .Na (by decide)) (hT .X7 (by decide)) (by rfl) (by rfl)).seq
      ((dropInt_rs .Na b (σ .Na) _ (hT .Na (by decide)) (by rfl)).seq
      ((dropInt_rs .X7 (drp (c * f + d * e) (q + 2)) (σ .X7) _ (hT .X7 (by decide)) (by rfl)).seq
      ((drS_rs hok.2.2.2.1 hok.2.1 hok.2.2.2.2 drOK_X9b (b + (drp (c * f + d * e) (q + 2))) 1 (σ .X9) r1 _ (hT .X9 (by decide)) hr1 (by rfl) (by exact hONE)).seq
      (dropInt_rs .X9 (b + (drp (c * f + d * e) (q + 2))) (σ .X9) _ (hT .X9 (by decide)) (by rfl))))))))))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · have hB1 : bitLen (c * f).natAbs ≤ 2 * w := by have := bitLen_natAbs_mul c f; omega
    have hB2 : bitLen (d * e).natAbs ≤ 2 * w := by have := bitLen_natAbs_mul d e; omega
    have hB5 : bitLen (c * f + d * e).natAbs ≤ 2 * w + 1 := by
      have := bitLen_natAbs_add (c * f) (d * e); omega
    have hB7 : bitLen (drp (c * f + d * e) (q + 2)).natAbs ≤ 2 * w + q + 5 := by
      have := bitLen_drp_le (c * f + d * e) (q + 2); omega
    have hB9 : bitLen (b + (drp (c * f + d * e) (q + 2))).natAbs ≤ 2 * w + q + 6 := by
      have := bitLen_natAbs_add b (drp (c * f + d * e) (q + 2)); omega
    have h3 : CA * (bitLen (c * f).natAbs + bitLen (d * e).natAbs + 1) ≤ CA * (4 * w + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h6 : drCost CL CA CR (bitLen (c * f + d * e).natAbs) (q + 2) ≤
        drCost CL CA CR (2 * w + q + 10) (q + 2) := drCost_mono (by omega) le_rfl
    have h9 : CA * (bitLen b.natAbs + bitLen (drp (c * f + d * e) (q + 2)).natAbs + 1) ≤ CA * (3 * w + q + 6) :=
      Nat.mul_le_mul_left _ (by omega)
    have h12 : drCost CL CA CR (bitLen (b + (drp (c * f + d * e) (q + 2))).natAbs) 1 ≤
        drCost CL CA CR (2 * w + q + 10) (q + 2) := drCost_mono (by omega) (by omega)
    have hCA : (CA + CS) * (4 * w + 1) = CA * (4 * w + 1) + CS * (4 * w + 1) := Nat.add_mul _ _ _
    have hcp : 6 * bitLen a.natAbs + 7 * bitLen b.natAbs + 29 ≤ 13 * w + 29 := by omega
    unfold blkCost
    omega

/-- **One butterfly cell**, exact: `R += ⟦cellV (q+2) y0 y1 ω⟧`, everything else restored. -/
theorem bfly_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (w q : ℕ) (a b c d e f : ℤ)
    (rA rB rO rq r1 : List Sym) (σ : Stk → List Sym)
    (hA2 : σ .A2 = entrySyms (a, b) ++ rA) (hB2 : σ .B2 = entrySyms (e, f) ++ rB)
    (hOm : σ .Om = entrySyms (c, d) ++ rO)
    (hQ2 : σ .Q2 = natSyms (q + 2) ++ rq) (hrq : TermOK rq)
    (hONE : σ .ONE = natSyms 1 ++ r1) (hr1 : TermOK r1)
    (hT : ∀ k ∈ bfTemps, TermOK (σ k))
    (hwa : bitLen a.natAbs ≤ w) (hwb : bitLen b.natAbs ≤ w) (hwc : bitLen c.natAbs ≤ w)
    (hwd : bitLen d.natAbs ≤ w) (hwe : bitLen e.natAbs ≤ w) (hwf : bitLen f.natAbs ≤ w) :
    RS [] (bflyProg X) σ
      (Function.update σ .R (entrySyms (cellV (q + 2) (a, b) (e, f) (c, d)) ++ σ .R))
      (bflyCost CM CA CS CL CR Mul w q) := by
  refine ((((copyInt_rs (src := .Om) (dst := .Nc) (tmp := .T1) (by decide) (by decide) (by decide) c (Sym.sep2 :: (intSyms d ++ Sym.sep :: rO)) σ (termOK_sep2 _) (by exact hOm.trans (entrySyms_append c d rO))).seq
        ((copyIm_rs (src := .Om) (dst := .Nd) (t1 := .T1) (t2 := .T2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) c d rO _ (by exact hOm)).seq
        ((copyInt_rs (src := .B2) (dst := .Ne) (tmp := .T1) (by decide) (by decide) (by decide) e (Sym.sep2 :: (intSyms f ++ Sym.sep :: rB)) _ (termOK_sep2 _) (by exact hB2.trans (entrySyms_append e f rB))).seq
        (copyIm_rs (src := .B2) (dst := .Nf) (t1 := .T1) (t2 := .T2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e f rB _ (by exact hB2))))).seq
      ((reBlk_rs hok w q a b c d e f rA rq r1 (σ .Nc) (σ .Nd) (σ .Ne) (σ .Nf) _ (by rfl) (by rfl) (by rfl) (by rfl) (hT .Nc (by decide)) (hT .Nd (by decide)) (hT .Ne (by decide)) (hT .Nf (by decide)) (by exact hA2) (by exact hQ2) hrq (by exact hONE) hr1 (fun k hk => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hT _ (by decide)) hwa hwc hwd hwe hwf).seq
      ((imBlk_rs hok w q a b c d e f rA rq r1 (σ .Nc) (σ .Nd) (σ .Ne) (σ .Nf) _ (by rfl) (by rfl) (by rfl) (by rfl) (hT .Nc (by decide)) (hT .Nd (by decide)) (hT .Ne (by decide)) (hT .Nf (by decide)) (by exact hA2) (by exact hQ2) hrq (by exact hONE) hr1 (fun k hk => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hT _ (by decide)) hwa hwb hwc hwd hwe hwf).seq
      ((dropInt_rs .Nf f (σ .Nf) _ (hT .Nf (by decide)) (by rfl)).seq
      ((dropInt_rs .Ne e (σ .Ne) _ (hT .Ne (by decide)) (by rfl)).seq
      ((dropInt_rs .Nd d (σ .Nd) _ (hT .Nd (by decide)) (by rfl)).seq
      ((dropInt_rs .Nc c (σ .Nc) _ (hT .Nc (by decide)) (by rfl)).seq
      ((packEntry_rs (nre := .X11) (nim := .X12) (dst := .R) (tmp := .T1) (by decide) (by decide) (by decide) (by decide) (by decide) (drp (a + drp (c * e - d * f) (q + 2)) 1) (drp (b + drp (c * f + d * e) (q + 2)) 1) (σ .X11) (σ .X12) _ (hT .X11 (by decide)) (hT .X12 (by decide)) (by rfl) (by rfl)).seq
      ((dropInt_rs .X12 (drp (b + drp (c * f + d * e) (q + 2)) 1) (σ .X12) _ (hT .X12 (by decide)) (by rfl)).seq
      (dropInt_rs .X11 (drp (a + drp (c * e - d * f) (q + 2)) 1) (σ .X11) _ (hT .X11 (by decide)) (by rfl)))))))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · have hX11 : bitLen (drp (a + drp (c * e - d * f) (q + 2)) 1).natAbs ≤ 2 * w + q + 9 := by
      have h1 := bitLen_drp_le (a + drp (c * e - d * f) (q + 2)) 1
      have h2 := bitLen_natAbs_add a (drp (c * e - d * f) (q + 2))
      have h3 := bitLen_drp_le (c * e - d * f) (q + 2)
      have h4 := bitLen_natAbs_sub (c * e) (d * f)
      have h5 := bitLen_natAbs_mul c e
      have h6 := bitLen_natAbs_mul d f
      omega
    have hX12 : bitLen (drp (b + drp (c * f + d * e) (q + 2)) 1).natAbs ≤ 2 * w + q + 9 := by
      have h1 := bitLen_drp_le (b + drp (c * f + d * e) (q + 2)) 1
      have h2 := bitLen_natAbs_add b (drp (c * f + d * e) (q + 2))
      have h3 := bitLen_drp_le (c * f + d * e) (q + 2)
      have h4 := bitLen_natAbs_add (c * f) (d * e)
      have h5 := bitLen_natAbs_mul c f
      have h6 := bitLen_natAbs_mul d e
      omega
    unfold bflyCost
    omega

#assert_std_axioms natAbs_drp_le bitLen_drp_le drCost_mono entrySyms_append termOK_sep2
  loadC_closed reBlk_closed imBlk_closed bflyProg_closed reBlk_rs imBlk_rs bfly_rs

end WP.W9g
