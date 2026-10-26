import WP.W9f.Kit
import WP.W9f.Pure

/-!
# WP.W9f.RegFwd — the forward and Nyquist regimes in host form

* `fwdProg`: forward core with IN = `W0`, OUT = `X`, then two entry-mover passes `X → X' → W0`.
* `nyqProg`: Nyquist core (alt from `RQ`, read only), then the same two passes.
* Costs are bounded by `kreg K * cbase Mul t1 H k`.
-/

namespace WP.W9f

open IntMul TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-- Common cost shape of the three regimes. -/
def cbase (Mul : ℕ → ℕ) (t1 H k : ℕ) : ℕ := t1 * (Mul (solW H) + eb H + k + 1) + (H + 1) ^ 2

theorem length_blkE_reverse (xs : List (ℤ × ℤ)) :
    (blkE xs.reverse).length = (blkE xs).length := by
  simp [blkE, blk, List.map_reverse, List.length_flatten, List.sum_reverse]

/-- `RQ` and `C3` are never modified. -/
def hRQ : HL := .inl 5
def hC3 : HL := .inl 9

theorem hRQ_ne (f : F) : f.loc ≠ hRQ := by cases f <;> decide
theorem hC3_ne (f : F) : f.loc ≠ hC3 := by cases f <;> decide

variable {Mul : ℕ → ℕ} (K : Kit Mul)

/-- Constant of the regimes. -/
def kreg : ℕ := K.CF + K.CN + 2 * K.CM + 20

theorem core_fwd_le (t1 H k : ℕ) :
    t1 * (Mul (solW H) + H + 1) + (H + 1) ^ 2 ≤ cbase Mul t1 H k := by
  unfold cbase eb
  have := Nat.mul_le_mul_left t1
    (show Mul (solW H) + H + 1 ≤ Mul (solW H) + (2 * H + 4) + k + 1 by omega)
  omega

theorem core_nyq_le (t1 H k : ℕ) :
    t1 * (Mul (solW H) + H + k + 1) + (H + 1) ^ 2 ≤ cbase Mul t1 H k := by
  unfold cbase eb
  have := Nat.mul_le_mul_left t1
    (show Mul (solW H) + H + k + 1 ≤ Mul (solW H) + (2 * H + 4) + k + 1 by omega)
  omega

theorem blk_le_cbase {t1 H k L : ℕ} (hL : L ≤ t1 * eb H) : L + 1 ≤ cbase Mul t1 H k := by
  unfold cbase
  have h1 := Nat.mul_le_mul_left t1 (show eb H ≤ Mul (solW H) + eb H + k + 1 by omega)
  have h2 : 1 ≤ (H + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem cost_two_le {X L CX CM KR B : ℕ} (hX : X ≤ B) (hL : L + 1 ≤ B) (hKR : CX + 2 * CM ≤ KR) :
    CX * X + 2 * (CM * (L + 1)) ≤ KR * B := by
  calc CX * X + 2 * (CM * (L + 1)) ≤ CX * B + 2 * (CM * B) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hX) (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hL))
    _ = (CX + 2 * CM) * B := by ring
    _ ≤ KR * B := Nat.mul_le_mul_right _ hKR

/-- Forward regime. -/
def fwdProg : KP K :=
  (callI K.IF [F.W0.loc, F.X.loc, F.PQ.loc, F.PH.loc, F.PMU.loc, F.PA.loc, F.PC.loc] dflt
    (lF K)).seq ((mover K .X .X').seq (mover K .X' .W0))

/-- Nyquist regime. -/
def nyqProg : KP K :=
  (callI K.IN [F.W0.loc, F.X.loc, F.PQ.loc, F.PH.loc, F.PMU.loc, F.PK.loc, F.PA.loc, hRQ] dflt
    (lN K)).seq ((mover K .X .X').seq (mover K .X' .W0))

/-- The two mover passes `X → X' → W0` after a core that left `blkE Z ++ X` on `X`. -/
theorem HT.twoPasses (σ0 : HL → List Sym) (s : F → List Sym) (Z : List (ℤ × ℤ)) (bX bX' : List Sym)
    (hX : s .X = blkE Z ++ Sym.mark :: bX) (hX' : s .X' = Sym.mark :: bX') (hW0 : s .W0 = []) :
    HT [] (henc σ0 s) ((mover K .X .X').seq (mover K .X' .W0))
      (henc σ0 (Function.update (Function.update (Function.update s .X (Sym.mark :: bX)) .X'
        (Sym.mark :: bX')) .W0 (blkE Z)))
      (2 * (K.CM * ((blkE Z).length + 1))) := by
  have h1 := HT.moverF K σ0 s .X .X' (by decide) Z (Sym.mark :: bX) (notEntry_mark _) hX
  set s1 := Function.update (Function.update s .X (Sym.mark :: bX)) .X' (blkE Z.reverse ++ s .X')
    with hs1
  have h2 := HT.moverF K σ0 s1 .X' .W0 (by decide) Z.reverse (Sym.mark :: bX') (notEntry_mark _)
    (by rw [hs1, Function.update_self, hX'])
  refine (HT.seq h1 h2).of_eq ?_ (by rw [length_blkE_reverse]; omega)
  congr 1
  funext g
  cases g <;> simp [hs1, hW0]

/-- **Forward regime**: `W0 := blkE (solveFwdBarrett …)`; `X`, `X'` and the parameters restored. -/
theorem HT.fwdProg (σ0 : HL → List Sym) (s : F → List Sym) (q H μ k : ℕ) (a c : ℤ)
    (Y : Array (ℤ × ℤ)) (bX bX' r2 r3 r4 r5 r6 : List Sym)
    (h2 : 2 ≤ Y.size) (hqH : q + 2 ≤ H) (ha : 0 < a) (hμ : (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a)
    (hab : bitLen a.natAbs ≤ H) (hcb : bitLen c.natAbs ≤ H) (hY : ArrW H Y)
    (hP : IntMulTM.Contracts.W8.zPartFwdBound q H a c Y (Y.size - 1))
    (hHm : IntMulTM.Contracts.W8.zHomFwdBound q H a c (Y.size - 1))
    (hO : ArrW H (IntMulTM.Contracts.W8.solveFwdBarrett q H Y.size μ a c Y))
    (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6)
    (hW0 : s .W0 = blkE Y.toList) (hX : s .X = Sym.mark :: bX) (hX' : s .X' = Sym.mark :: bX')
    (hPQ : s .PQ = natSyms q ++ r2) (hPH : s .PH = natSyms H ++ r3)
    (hPMU : s .PMU = natSyms μ ++ r4) (hPA : s .PA = intSyms a ++ r5)
    (hPC : s .PC = intSyms c ++ r6) :
    HT [] (henc σ0 s) (fwdProg K)
      (henc σ0 (Function.update s .W0
        (blkE (IntMulTM.Contracts.W8.solveFwdBarrett q H Y.size μ a c Y).toList)))
      (kreg K * cbase Mul Y.size H k) := by
  set Z := IntMulTM.Contracts.W8.solveFwdBarrett q H Y.size μ a c Y with hZ
  have h1 := HT.callI_upd2 K.IF [F.W0.loc, F.X.loc, F.PQ.loc, F.PH.loc, F.PMU.loc, F.PA.loc,
    F.PC.loc] dflt (by decide) rfl (by norm_num) (lF K) (henc σ0 s) (.inl 0) (.inl 1) _ _
    (K.hF q H μ a c Y [] r2 r3 r4 r5 r6 _ h2 hqH ha hμ hab hcb hY hP hHm hO notEntry_nil
      hr2 hr3 hr4 hr5 hr6
      (by show henc σ0 s F.W0.loc = _; rw [henc_loc, hW0, List.append_nil])
      (by show henc σ0 s F.PQ.loc = _; rw [henc_loc, hPQ])
      (by show henc σ0 s F.PH.loc = _; rw [henc_loc, hPH])
      (by show henc σ0 s F.PMU.loc = _; rw [henc_loc, hPMU])
      (by show henc σ0 s F.PA.loc = _; rw [henc_loc, hPA])
      (by show henc σ0 s F.PC.loc = _; rw [henc_loc, hPC])) []
  have h1' : HT [] (henc σ0 s) (callI K.IF [F.W0.loc, F.X.loc, F.PQ.loc, F.PH.loc, F.PMU.loc,
      F.PA.loc, F.PC.loc] dflt (lF K))
      (henc σ0 (Function.update (Function.update s .W0 []) .X (blkE Z.toList ++ s .X)))
      (K.CF * (Y.size * (Mul (solW H) + H + 1) + (H + 1) ^ 2)) := by
    refine h1.of_eq ?_ le_rfl
    show Function.update (Function.update (henc σ0 s) F.W0.loc []) F.X.loc
      (blkE Z.toList ++ henc σ0 s F.X.loc) = _
    rw [henc_loc, henc_update, henc_update]
  set s1 := Function.update (Function.update s .W0 []) .X (blkE Z.toList ++ s .X) with hs1
  have h2' := HT.twoPasses K σ0 s1 Z.toList bX bX' (by rw [hs1, Function.update_self, hX])
    (by rw [hs1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hX'])
    (by rw [hs1, Function.update_of_ne (by decide), Function.update_self])
  have hlen : (blkE Z.toList).length ≤ Y.size * eb H := by
    have hZs : Z.toList.length = Y.size := by
      rw [Array.length_toList]
      exact size_solveFwdBarrett _ _ _ _ _ _ _
    have := length_blkE_le H Z.toList hO
    rwa [hZs] at this
  refine (HT.seq h1' h2').of_eq ?_ (cost_two_le (core_fwd_le _ _ k) (blk_le_cbase hlen)
    (by unfold kreg; omega))
  congr 1
  funext g
  cases g <;> simp [hs1, hX, hX']

/-- **Nyquist regime**: `W0 := blkE (solveNyqBarrett …)`; alt read from `RQ`. -/
theorem HT.nyqProg (σ0 : HL → List Sym) (s : F → List Sym) (q H μ k : ℕ) (a : ℤ)
    (alt : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (bX bX' r2 r3 r4 r5 r6 rq : List Sym)
    (hk : Y.size = 2 ^ k) (hk1 : 1 ≤ k) (hqH : q + 2 ≤ H) (ha : 0 < a)
    (hμ : (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a) (hab : bitLen a.natAbs ≤ H) (hY : ArrW H Y)
    (halt : EntryW H alt) (hP : IntMulTM.Contracts.W8.zPartNyqBound q H a Y (Y.size - 1))
    (hO : ArrW H (IntMulTM.Contracts.W8.solveNyqBarrett q H Y.size k μ a Y alt))
    (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6)
    (hRQv : σ0 hRQ = entrySyms alt ++ rq)
    (hW0 : s .W0 = blkE Y.toList) (hX : s .X = Sym.mark :: bX) (hX' : s .X' = Sym.mark :: bX')
    (hPQ : s .PQ = natSyms q ++ r2) (hPH : s .PH = natSyms H ++ r3)
    (hPMU : s .PMU = natSyms μ ++ r4) (hPK : s .PK = natSyms k ++ r5)
    (hPA : s .PA = intSyms a ++ r6) :
    HT [] (henc σ0 s) (nyqProg K)
      (henc σ0 (Function.update s .W0
        (blkE (IntMulTM.Contracts.W8.solveNyqBarrett q H Y.size k μ a Y alt).toList)))
      (kreg K * cbase Mul Y.size H k) := by
  set Z := IntMulTM.Contracts.W8.solveNyqBarrett q H Y.size k μ a Y alt with hZ
  have h1 := HT.callI_upd2 K.IN [F.W0.loc, F.X.loc, F.PQ.loc, F.PH.loc, F.PMU.loc, F.PK.loc,
    F.PA.loc, hRQ] dflt (by decide) rfl (by norm_num) (lN K) (henc σ0 s) (.inl 0) (.inl 1) _ _
    (K.hN q H μ k a alt Y [] r2 r3 r4 r5 r6 rq _ hk hk1 hqH ha hμ hab hY halt hP hO
      notEntry_nil hr2 hr3 hr4 hr5 hr6
      (by show henc σ0 s F.W0.loc = _; rw [henc_loc, hW0, List.append_nil])
      (by show henc σ0 s F.PQ.loc = _; rw [henc_loc, hPQ])
      (by show henc σ0 s F.PH.loc = _; rw [henc_loc, hPH])
      (by show henc σ0 s F.PMU.loc = _; rw [henc_loc, hPMU])
      (by show henc σ0 s F.PK.loc = _; rw [henc_loc, hPK])
      (by show henc σ0 s F.PA.loc = _; rw [henc_loc, hPA])
      (by show henc σ0 s hRQ = _; rw [henc_other _ _ hRQ_ne, hRQv])) []
  have h1' : HT [] (henc σ0 s) (callI K.IN [F.W0.loc, F.X.loc, F.PQ.loc, F.PH.loc, F.PMU.loc,
      F.PK.loc, F.PA.loc, hRQ] dflt (lN K))
      (henc σ0 (Function.update (Function.update s .W0 []) .X (blkE Z.toList ++ s .X)))
      (K.CN * (Y.size * (Mul (solW H) + H + k + 1) + (H + 1) ^ 2)) := by
    refine h1.of_eq ?_ le_rfl
    show Function.update (Function.update (henc σ0 s) F.W0.loc []) F.X.loc
      (blkE Z.toList ++ henc σ0 s F.X.loc) = _
    rw [henc_loc, henc_update, henc_update]
  set s1 := Function.update (Function.update s .W0 []) .X (blkE Z.toList ++ s .X) with hs1
  have h2' := HT.twoPasses K σ0 s1 Z.toList bX bX' (by rw [hs1, Function.update_self, hX])
    (by rw [hs1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hX'])
    (by rw [hs1, Function.update_of_ne (by decide), Function.update_self])
  have hlen : (blkE Z.toList).length ≤ Y.size * eb H := by
    have hZs : Z.toList.length = Y.size := by
      rw [Array.length_toList]
      exact size_solveNyqBarrett _ _ _ _ _ _ _ _
    have := length_blkE_le H Z.toList hO
    rwa [hZs] at this
  refine (HT.seq h1' h2').of_eq ?_ (cost_two_le (core_nyq_le _ _ k) (blk_le_cbase hlen)
    (by unfold kreg; omega))
  congr 1
  funext g
  cases g <;> simp [hs1, hX, hX']

#assert_std_axioms length_blkE_reverse hRQ_ne hC3_ne core_fwd_le core_nyq_le blk_le_cbase
  cost_two_le HT.twoPasses HT.fwdProg HT.nyqProg

end WP.W9f
