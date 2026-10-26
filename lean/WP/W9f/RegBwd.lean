import WP.W9f.RegFwd

/-!
# WP.W9f.RegBwd — the backward regime in host form

`bwdProg`: move `Y0` off `W0` (one record, reversed, onto `TT`), move `Y1 … Y_{t-1}` onto `X`
(reversed by the entry mover), unwind `Y0` back on top of `X`: `X` now holds
`[Y0, Y_{t-1}, …, Y1]` (= `runBwdRevSteps`). Then the forward core with divisor `c` and multiplier
`a` (OUT = `X'`), and one mover pass `X' → W0` (= `runReverseSteps`).
-/

namespace WP.W9f

open IntMul TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

variable {Mul : ℕ → ℕ} (K : Kit Mul)

/-- Input rotation. -/
def rotProg : KP K :=
  ((moveRec F.W0.loc F.TT.loc).liftRegs (lS K)).seq
    ((mover K .W0 .X).seq ((unwind F.TT.loc F.X.loc).liftRegs (lS K)))

/-- Backward regime. -/
def bwdProg : KP K :=
  (rotProg K).seq
    ((callI K.IF [F.X.loc, F.X'.loc, F.PQ.loc, F.PH.loc, F.PMU.loc, F.PC.loc, F.PA.loc] dflt
      (lF K)).seq (mover K .X' .W0))

theorem noMark_rev_entry (y0 : ℤ × ℤ) :
    ∀ x ∈ Sym.sep :: (entryData y0).reverse, x ≠ Sym.mark := by
  intro x hx
  simp only [List.mem_cons, List.mem_reverse] at hx
  rcases hx with rfl | h
  · decide
  · intro e
    subst e
    exact absurd (entryData_data y0 _ h) (by decide)

/-- **Input rotation**: `W0 = blkE (y0 :: ytl)` gives `X = blkE (y0 :: ytl.reverse) ++ X`. -/
theorem HT.rotate (σ0 : HL → List Sym) (s : F → List Sym) (y0 : ℤ × ℤ) (ytl : List (ℤ × ℤ))
    (bX bTT : List Sym) (hW0 : s .W0 = blkE (y0 :: ytl)) (hX : s .X = Sym.mark :: bX)
    (hTT : s .TT = Sym.mark :: bTT) :
    HT [] (henc σ0 s) (rotProg K)
      (henc σ0 (Function.update (Function.update s .W0 []) .X
        (blkE (y0 :: ytl.reverse) ++ Sym.mark :: bX)))
      (3 * (entryData y0).length + 3 + K.CM * ((blkE ytl).length + 1) +
        (3 * ((entryData y0).length + 1) + 3)) := by
  have h1 := HT.moveRecF (lS K) σ0 s .W0 .TT (by decide) (entryData y0) (blkE ytl)
    (entryData_data y0) (by rw [hW0, blkE_cons, entrySyms_eq, List.append_assoc]; rfl)
  set s1 := Function.update (Function.update s .W0 (blkE ytl)) .TT
    (Sym.sep :: ((entryData y0).reverse ++ s .TT)) with hs1
  have h2 := HT.moverF K σ0 s1 .W0 .X (by decide) ytl [] notEntry_nil
    (by rw [hs1, Function.update_of_ne (by decide), Function.update_self, List.append_nil])
  set s2 := Function.update (Function.update s1 .W0 []) .X (blkE ytl.reverse ++ s1 .X) with hs2
  have h3 := HT.unwindF (lS K) σ0 s2 .TT .X (by decide) (Sym.sep :: (entryData y0).reverse) bTT
    (noMark_rev_entry y0) (by
      rw [hs2, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hs1,
        Function.update_self, hTT]
      rfl)
  refine (HT.seq h1 (HT.seq h2 h3)).of_eq ?_
    (by simp only [List.length_cons, List.length_reverse]; omega)
  congr 1
  funext g
  cases g <;> simp [hs2, hs1, hX, hTT, blkE_cons, entrySyms_eq]

theorem cost_bwd_le {X L1 L2 d CF CM KR B : ℕ} (hX : X ≤ B) (hL1 : L1 + 1 ≤ B) (hL2 : L2 + 1 ≤ B)
    (hd : 6 * d + 9 ≤ 15 * B) (hKR : CF + 2 * CM + 15 ≤ KR) :
    3 * d + 3 + CM * (L1 + 1) + (3 * (d + 1) + 3) + (CF * X + CM * (L2 + 1)) ≤ KR * B := by
  have e1 := Nat.mul_le_mul_left CM hL1
  have e2 := Nat.mul_le_mul_left CF hX
  have e3 := Nat.mul_le_mul_left CM hL2
  have e4 := Nat.mul_le_mul_right B hKR
  nlinarith [e1, e2, e3, e4]

/-- **Backward regime**: `W0 := blkE (solveBwdBarrett …)`; `X`, `X'`, `TT`, parameters restored. -/
theorem HT.bwdProg (σ0 : HL → List Sym) (s : F → List Sym) (q H μ k : ℕ) (a c : ℤ)
    (Y : Array (ℤ × ℤ)) (bX bX' bTT r2 r3 r4 r5 r6 : List Sym)
    (h2 : 2 ≤ Y.size) (hqH : q + 2 ≤ H) (hc : 0 < c) (hμ : (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / c)
    (hab : bitLen a.natAbs ≤ H) (hcb : bitLen c.natAbs ≤ H) (hY : ArrW H Y)
    (hP : IntMulTM.Contracts.W8.zPartFwdBound q H c a
      (runBwdRevSteps Y.size (read1D Y) Y.size).outTape (Y.size - 1))
    (hHm : IntMulTM.Contracts.W8.zHomFwdBound q H c a (Y.size - 1))
    (hO : ArrW H (IntMulTM.Contracts.W8.solveBwdBarrett q H Y.size μ a c Y))
    (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6)
    (hW0 : s .W0 = blkE Y.toList) (hX : s .X = Sym.mark :: bX) (hX' : s .X' = Sym.mark :: bX')
    (hTT : s .TT = Sym.mark :: bTT)
    (hPQ : s .PQ = natSyms q ++ r2) (hPH : s .PH = natSyms H ++ r3)
    (hPMU : s .PMU = natSyms μ ++ r4) (hPA : s .PA = intSyms a ++ r5)
    (hPC : s .PC = intSyms c ++ r6) :
    HT [] (henc σ0 s) (bwdProg K)
      (henc σ0 (Function.update s .W0
        (blkE (IntMulTM.Contracts.W8.solveBwdBarrett q H Y.size μ a c Y).toList)))
      (kreg K * cbase Mul Y.size H k) := by
  obtain ⟨y0, ytl, hl⟩ : ∃ y0 ytl, Y.toList = y0 :: ytl := by
    cases h : Y.toList with
    | nil =>
      have := congrArg List.length h
      simp only [Array.length_toList, List.length_nil] at this
      omega
    | cons y0 ytl => exact ⟨y0, ytl, rfl⟩
  have hlen : ytl.length + 1 = Y.size := by
    have := congrArg List.length hl
    simp only [Array.length_toList, List.length_cons] at this
    omega
  set Y' := (runBwdRevSteps Y.size (read1D Y) Y.size).outTape with hY'
  have hY'l : Y'.toList = y0 :: ytl.reverse := runBwdRevSteps_toList Y Y.size y0 ytl hl rfl
  have hY's : Y'.size = Y.size := size_runBwdRevSteps _ _ _
  set Z' := IntMulTM.Contracts.W8.solveFwdBarrett q H Y'.size μ c a Y' with hZ'
  have hBZ : (IntMulTM.Contracts.W8.solveBwdBarrett q H Y.size μ a c Y).toList =
      Z'.toList.reverse := by
    rw [solveBwdBarrett_toList, hZ', hY's]
  have hOZ : ArrW H Z' := fun z hz => hO z (by rw [hBZ, List.mem_reverse]; exact hz)
  have hY'w : ArrW H Y' := arrW_toList (fun z hz => by
    rw [hY'l, List.mem_cons, List.mem_reverse] at hz
    rw [hl, List.mem_cons]
    exact hz) hY
  have hR := HT.rotate K σ0 s y0 ytl bX bTT (by rw [hW0, hl]) hX hTT
  set s3 := Function.update (Function.update s .W0 []) .X
    (blkE (y0 :: ytl.reverse) ++ Sym.mark :: bX) with hs3
  have hC := HT.callI_upd2 K.IF [F.X.loc, F.X'.loc, F.PQ.loc, F.PH.loc, F.PMU.loc, F.PC.loc,
    F.PA.loc] dflt (by decide) rfl (by norm_num) (lF K) (henc σ0 s3) (.inl 0) (.inl 1) _ _
    (K.hF q H μ c a Y' (Sym.mark :: bX) r2 r3 r4 r6 r5 _ (by rw [hY's]; exact h2) hqH hc hμ hcb
      hab hY'w (by rw [hY's]; exact hP) (by rw [hY's]; exact hHm) hOZ (notEntry_mark _)
      hr2 hr3 hr4 hr6 hr5
      (by show henc σ0 s3 F.X.loc = _; rw [henc_loc, hs3, Function.update_self, hY'l])
      (by show henc σ0 s3 F.PQ.loc = _; simp [hs3, hPQ])
      (by show henc σ0 s3 F.PH.loc = _; simp [hs3, hPH])
      (by show henc σ0 s3 F.PMU.loc = _; simp [hs3, hPMU])
      (by show henc σ0 s3 F.PC.loc = _; simp [hs3, hPC])
      (by show henc σ0 s3 F.PA.loc = _; simp [hs3, hPA])) []
  have hC' : HT [] (henc σ0 s3) (callI K.IF [F.X.loc, F.X'.loc, F.PQ.loc, F.PH.loc, F.PMU.loc,
      F.PC.loc, F.PA.loc] dflt (lF K))
      (henc σ0 (Function.update (Function.update s3 .X (Sym.mark :: bX)) .X'
        (blkE Z'.toList ++ s3 .X')))
      (K.CF * (Y'.size * (Mul (solW H) + H + 1) + (H + 1) ^ 2)) := by
    refine hC.of_eq ?_ le_rfl
    show Function.update (Function.update (henc σ0 s3) F.X.loc (Sym.mark :: bX)) F.X'.loc
      (blkE Z'.toList ++ henc σ0 s3 F.X'.loc) = _
    rw [henc_loc, henc_update, henc_update]
  set s4 := Function.update (Function.update s3 .X (Sym.mark :: bX)) .X'
    (blkE Z'.toList ++ s3 .X') with hs4
  have hM := HT.moverF K σ0 s4 .X' .W0 (by decide) Z'.toList (Sym.mark :: bX') (notEntry_mark _)
    (by simp [hs4, hs3, hX'])
  have hd : (entryData y0).length + 1 ≤ eb H := by
    have h1 := length_entrySyms_le (hY y0 (by rw [hl]; exact List.mem_cons_self ..))
    rw [entrySyms_eq, List.length_append, List.length_singleton] at h1
    exact h1
  have hL1 : (blkE ytl).length ≤ Y.size * eb H := by
    have h1 := length_blkE_le H ytl (fun z hz => hY z (by rw [hl]; exact List.mem_cons_of_mem _ hz))
    have h2 := Nat.mul_le_mul_right (eb H) (show ytl.length ≤ Y.size by omega)
    omega
  have hL2 : (blkE Z'.toList).length ≤ Y.size * eb H := by
    have h1 := length_blkE_le H Z'.toList hOZ
    have hZs : Z'.toList.length = Y.size := by
      rw [Array.length_toList, hZ', size_solveFwdBarrett, hY's]
    rwa [hZs] at h1
  have heb : eb H + 1 ≤ cbase Mul Y.size H k :=
    blk_le_cbase (Nat.le_mul_of_pos_left _ (by omega))
  refine (HT.seq hR (HT.seq hC' hM)).of_eq ?_ ?_
  · congr 1
    funext g
    cases g <;> simp [hs4, hs3, hX, hX', hBZ]
  · rw [hY's]
    exact cost_bwd_le (core_fwd_le _ _ k) (blk_le_cbase hL1) (blk_le_cbase hL2) (by omega)
      (by unfold kreg; omega)

#assert_std_axioms noMark_rev_entry HT.rotate cost_bwd_le HT.bwdProg

end WP.W9f
