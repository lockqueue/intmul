import WP.W9f.Phases

/-!
# WP.W9f.Dispatch — the regime dispatch of one column

`dispatch`: compare `u2` (on `C3`) with `r/2` (on `RH`) through `W3_cmpNat` (twice): `lt` runs
the forward regime, `eq` the Nyquist regime, `gt` the backward regime. `HT.dispatch` derives each
regime's premises from `ColumnOK` and leaves `blkE (W8.columnSolveBarrett …)` on `W0`.
-/

namespace WP.W9f

open IntMul TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-- `lt` test. -/
def isLt : Ordering → Bool
  | .lt => true
  | _ => false

/-- `eq` test. -/
def isEq : Ordering → Bool
  | .eq => true
  | _ => false

variable {Mul : ℕ → ℕ} (K : Kit Mul)

/-- The dispatch on `ordOf u2 (r/2)`. -/
def dispatch : KP K :=
  (callI K.IC [hC3, F.RH.loc] dflt (lC K)).seq
    (.ite (fun v => isLt (K.IC.obs ((lC K).get v))) (fwdProg K)
      ((callI K.IC [hC3, F.RH.loc] dflt (lC K)).seq
        (.ite (fun v => isEq (K.IC.obs ((lC K).get v))) (nyqProg K) (bwdProg K))))

theorem ordOf_lt {u v : ℕ} (h : isLt (Lib.ordOf u v) = true) : u < v := by
  unfold Lib.ordOf at h
  split_ifs at h with h1 <;> simp_all [isLt]

theorem ordOf_eq {u v : ℕ} (h1 : isLt (Lib.ordOf u v) = false)
    (h2 : isEq (Lib.ordOf u v) = true) : u = v := by
  unfold Lib.ordOf at h1 h2
  split_ifs at h1 h2 with e1 e2 <;> simp_all [isLt, isEq]

theorem ordOf_gt {u v : ℕ} (h1 : isLt (Lib.ordOf u v) = false)
    (h2 : isEq (Lib.ordOf u v) = false) : v < u := by
  unfold Lib.ordOf at h1 h2
  split_ifs at h1 h2 with e1 e2 <;> simp_all [isLt, isEq]
  omega

theorem two_le_pow {m : ℕ} (hm : 1 ≤ m) : 2 ≤ 2 ^ m := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

theorem half_of_pow {r m : ℕ} (hr : r = 2 ^ m) (hm : 1 ≤ m) : r = 2 * (r / 2) ∧ 0 < r / 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hp : 0 < 2 ^ j := Nat.two_pow_pos j
  rw [hr, pow_succ]
  omega

/-- **Dispatch**: the regime selected by `u2` runs; `W0 := blkE (columnSolveBarrett …)`. -/
theorem HT.dispatch (σ0 : HL → List Sym) (s : F → List Sym) (h : PostHdr) (u2 : ℕ)
    (c0 c1 alt : ℤ × ℤ) (Y : Array (ℤ × ℤ))
    (bX bX' bTT bPQ bPH bPK bPMU bPA bPC bRH r3 rq : List Sym)
    (hd : PostDims h) (hY : Y.size = h.t1) (hok : ColumnOK h.pSub h.t1 h.r u2 c0 c1 Y alt)
    (hO : ArrW h.H (IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H h.t1 h.mt1 h.r u2 c0.1 c1.1
      Y alt))
    (hr3 : TermOK r3) (hC3v : σ0 hC3 = natSyms u2 ++ r3) (hRQv : σ0 hRQ = entrySyms alt ++ rq)
    (hW0 : s .W0 = blkE Y.toList) (hX : s .X = Sym.mark :: bX) (hX' : s .X' = Sym.mark :: bX')
    (hTT : s .TT = Sym.mark :: bTT)
    (hPQ : s .PQ = natSyms h.pSub ++ Sym.mark :: bPQ)
    (hPH : s .PH = natSyms h.H ++ Sym.mark :: bPH)
    (hPK : s .PK = natSyms h.mt1 ++ Sym.mark :: bPK)
    (hPMU : s .PMU = natSyms (postMu h.H h.r u2 c0.1 c1.1) ++ Sym.mark :: bPMU)
    (hPA : s .PA = intSyms c0.1 ++ Sym.mark :: bPA)
    (hPC : s .PC = intSyms c1.1 ++ Sym.mark :: bPC)
    (hRH : s .RH = natSyms (h.r / 2) ++ Sym.mark :: bRH) :
    HT [] (henc σ0 s) (dispatch K)
      (henc σ0 (Function.update s .W0 (blkE (IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H
        h.t1 h.mt1 h.r u2 c0.1 c1.1 Y alt).toList)))
      (2 * (K.CC * (bitLen u2 + bitLen (h.r / 2) + 1)) + kreg K * cbase Mul h.t1 h.H h.mt1 + 2) := by
  obtain ⟨-, -, ht1, hpos, hF, hN, hB, hYw, haltw, hab, hcb⟩ := hok
  obtain ⟨hmt, hmr, hm1, hm2⟩ := hd
  obtain ⟨hr2, -⟩ := half_of_pow hmr (by omega)
  have hqH : h.pSub + 2 ≤ h.H := by
    show h.pSub + 2 ≤ barrettH h.pSub
    unfold barrettH
    omega
  have h2 : 2 ≤ Y.size := by
    rw [hY, hmt]
    exact two_le_pow hm1
  have hμ0 := postMu_cast h.H h.r u2 c0.1 c1.1 hpos
  have hx : henc σ0 s hC3 = natSyms u2 ++ r3 := by rw [henc_other _ _ hC3_ne, hC3v]
  have hy : henc σ0 s F.RH.loc = natSyms (h.r / 2) ++ Sym.mark :: bRH := by rw [henc_loc, hRH]
  have hm : TermOK (Sym.mark :: bRH) := TermOK.cons rfl _
  refine (HT.cmpNat_ite K.hC dflt (lC K) hC3 F.RH.loc (by decide) (by norm_num) (henc σ0 s) _ u2
    (h.r / 2) r3 (Sym.mark :: bRH) hr3 hm hx hy isLt (WP.W9f.fwdProg K) _ []
    (T₁ := kreg K * cbase Mul Y.size h.H h.mt1)
    (T₂ := K.CC * (bitLen u2 + bitLen (h.r / 2) + 1) +
      (max (kreg K * cbase Mul Y.size h.H h.mt1) (kreg K * cbase Mul Y.size h.H h.mt1) + 1))
    ?_ ?_).mono ?_
  · intro hlt
    have hlt' : 2 * u2 < h.r := by have := ordOf_lt hlt; omega
    have hdiv : IntMulTM.Contracts.W8.columnDivisor h.r u2 c0.1 c1.1 = c0.1 := by
      unfold IntMulTM.Contracts.W8.columnDivisor
      rw [if_pos (by omega)]
    have hcs : IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H h.t1 h.mt1 h.r u2 c0.1 c1.1 Y
        alt = IntMulTM.Contracts.W8.solveFwdBarrett h.pSub h.H Y.size
          ((postMu h.H h.r u2 c0.1 c1.1 : ℕ) : ℤ) c0.1 c1.1 Y := by
      unfold IntMulTM.Contracts.W8.columnSolveBarrett
      rw [if_pos hlt', hY, hμ0, hdiv]
    rw [hcs]
    rw [hcs] at hO
    exact HT.fwdProg K σ0 s h.pSub h.H _ h.mt1 c0.1 c1.1 Y bX bX' _ _ _ _ _ h2 hqH
      (hdiv ▸ hpos) (by rw [hμ0, hdiv]) hab hcb hYw (by rw [hY]; exact (hF hlt').1)
      (by rw [hY]; exact (hF hlt').2) hO (TermOK.cons rfl _) (TermOK.cons rfl _)
      (TermOK.cons rfl _) (TermOK.cons rfl _) (TermOK.cons rfl _) hW0 hX hX' hPQ hPH hPMU hPA hPC
  · intro hnlt
    refine (HT.cmpNat_ite K.hC dflt (lC K) hC3 F.RH.loc (by decide) (by norm_num) (henc σ0 s) _ u2
      (h.r / 2) r3 (Sym.mark :: bRH) hr3 hm hx hy isEq (WP.W9f.nyqProg K) (WP.W9f.bwdProg K) []
      (T₁ := kreg K * cbase Mul Y.size h.H h.mt1) (T₂ := kreg K * cbase Mul Y.size h.H h.mt1)
      ?_ ?_).mono le_rfl
    · intro heq
      have heq' : 2 * u2 = h.r := by have := ordOf_eq hnlt heq; omega
      have hdiv : IntMulTM.Contracts.W8.columnDivisor h.r u2 c0.1 c1.1 = c0.1 := by
        unfold IntMulTM.Contracts.W8.columnDivisor
        rw [if_pos (by omega)]
      have hcs : IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H h.t1 h.mt1 h.r u2 c0.1 c1.1
          Y alt = IntMulTM.Contracts.W8.solveNyqBarrett h.pSub h.H Y.size h.mt1
            ((postMu h.H h.r u2 c0.1 c1.1 : ℕ) : ℤ) c0.1 Y alt := by
        unfold IntMulTM.Contracts.W8.columnSolveBarrett
        rw [if_neg (by omega), if_pos heq', hY, hμ0, hdiv]
      rw [hcs]
      rw [hcs] at hO
      exact HT.nyqProg K σ0 s h.pSub h.H _ h.mt1 c0.1 alt Y bX bX' _ _ _ _ _ rq
        (by rw [hY]; exact hmt) hm1 hqH (hdiv ▸ hpos) (by rw [hμ0, hdiv]) hab hYw haltw
        (by rw [hY]; exact hN heq') hO (TermOK.cons rfl _) (TermOK.cons rfl _)
        (TermOK.cons rfl _) (TermOK.cons rfl _) (TermOK.cons rfl _) hRQv hW0 hX hX' hPQ hPH hPMU
        hPK hPA
    · intro hneq
      have hgt : h.r < 2 * u2 := by have := ordOf_gt hnlt hneq; omega
      have hdiv : IntMulTM.Contracts.W8.columnDivisor h.r u2 c0.1 c1.1 = c1.1 := by
        unfold IntMulTM.Contracts.W8.columnDivisor
        rw [if_neg (by omega)]
      have hcs : IntMulTM.Contracts.W8.columnSolveBarrett h.pSub h.H h.t1 h.mt1 h.r u2 c0.1 c1.1
          Y alt = IntMulTM.Contracts.W8.solveBwdBarrett h.pSub h.H Y.size
            ((postMu h.H h.r u2 c0.1 c1.1 : ℕ) : ℤ) c0.1 c1.1 Y := by
        unfold IntMulTM.Contracts.W8.columnSolveBarrett
        rw [if_neg (by omega), if_neg (by omega), hY, hμ0, hdiv]
      rw [hcs]
      rw [hcs] at hO
      exact HT.bwdProg K σ0 s h.pSub h.H _ h.mt1 c0.1 c1.1 Y bX bX' bTT _ _ _ _ _ h2 hqH
        (hdiv ▸ hpos) (by rw [hμ0, hdiv]) hab hcb hYw (by rw [hY]; exact (hB hgt).1)
        (by rw [hY]; exact (hB hgt).2) hO (TermOK.cons rfl _) (TermOK.cons rfl _)
        (TermOK.cons rfl _) (TermOK.cons rfl _) (TermOK.cons rfl _) hW0 hX hX' hTT hPQ hPH hPMU
        hPA hPC
  · rw [hY]
    omega

#assert_std_axioms ordOf_lt ordOf_eq ordOf_gt two_le_pow half_of_pow HT.dispatch

end WP.W9f
