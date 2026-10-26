/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CAddLoop

/-!
# `SubNLogN.Machine.Arith.CAdd`: exact coefficientwise sum and difference (AR6, AR6')

Paper: Lemma A.4(5) (`lem:transfer-streams`, fixed-width carry scans);
contracts `CAddStmt`, `CSubStmt` (`Contracts/Arith.lean`, used by the bridge's
deconvolution solvers).

## Plan
`cMain f` on `KLoc (Fin 6) (Fin 9)` (`CAddAux.CK`): guards on the private stacks; rulers
`R1 := w1`, `R2 := w2`, `R3 := w3` tokens (`K1.ShiftAux.buildU`: countdown of a copy of each
counter, amortized `O(w)`); the record loop (`CAddLoop`), which runs the field kernel
(`CAddRec.fieldC`: `w3` ripple steps with sign extension of the shorter operand, discard of the
unread bits) on every field; the output buffer is rewound onto the destination; rulers and guards
are removed. With `f = addBit` the output field is `twosBits w3 (a + b)`, with `f = subBit` it
is `twosBits w3 (a - b)` (`K1/Twos.lean`, `ripOut_add`/`ripOut_sub`; the sign extension uses
`FitsTwos w1 a` and `FitsTwos w2 b`).

**Scope (honest summary).** Proved (no `sorry`): `cAdd_holds : CAddStmt` and
`cSub_holds : CSubStmt`, in `SubNLogN.Machine.Arith`; helpers in
`SubNLogN.Machine.Arith.CAddAux`. Of the contracts' hypotheses the proofs use `1 ≤ w1`,
`1 ≤ w2`, the input fits, the alignment, `BlkTerm ru` and the three `TermOK`; `1 ≤ w3`,
`BlkTerm rv` and the output fit `CArrFits w3 (zipC …)` are not needed (the output is the
`w3`-bit field of the exact sum, i.e. modulo `2^w3`).
-/

namespace SubNLogN.Machine.Arith.CAddAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1
  SubNLogN.Machine.K1.AddSubAux SubNLogN.Machine.K1.ShiftAux

/-! ## Programs -/

/-- Guards on the output buffer and the rulers. -/
def setupC : CProg CK :=
  .seq (cpc cT .mark) (.seq (cpc cR1 .mark) (.seq (cpc cR1' .mark) (.seq (cpc cR2 .mark)
    (.seq (cpc cR2' .mark) (.seq (cpc cR3 .mark) (cpc cR3' .mark))))))

/-- Remove the rulers and the guards. -/
def cleanupC : CProg CK :=
  .seq (liftC (dropBits cR1)) (.seq (cpd cR1) (.seq (liftC (dropBits cR2)) (.seq (cpd cR2)
    (.seq (liftC (dropBits cR3)) (.seq (cpd cR3) (.seq (cpd cR1') (.seq (cpd cR2')
      (cpd cR3'))))))))

/-- The sum / difference kernel with bit function `f`. -/
def cMain (f : Bool → Bool → Bool → Bool × Bool) : CProg CK :=
  .seq setupC
  (.seq (liftC (buildU cW1 cC cM cR1)) (.seq (cpd cC)
  (.seq (liftC (buildU cW2 cC cM cR2)) (.seq (cpd cC)
  (.seq (liftC (buildU cW3 cC cM cR3)) (.seq (cpd cC)
  (.seq (cpkO cU)
  (.seq (recLoopC f)
  (.seq (liftCo (WP.W9comp.rewindTo cT cD .mark))
    cleanupC)))))))))

theorem closed_cMain (f : Bool → Bool → Bool → Bool × Bool) : (cMain f).Closed := by
  simp [cMain, setupC, cleanupC, recLoopC, recBodyC, fieldLoopC, fieldC, stepLoop, stepBody,
    readA, readB, dropTok, liftC, liftCo, cpkO, cpkP, cppO, cpd, cpc, setA, setB, pushF, setCF,
    clrC, buildU, uLoop, uBody, dropBits, dropLoop, liftX, pkO, pc, pd, Prog.Closed,
    Prog.FreeBelow, WP.W9comp.freeBelow_liftRegs, dec, copyBlock, moveBlock, moveBits,
    moveBitsDup, restoreR, WP.W9comp.rewindTo, pushC, popR, pushR, peekR, scanLoop, scanBody,
    decFix, skip, moveBitsBody, dupBody, WP.W9comp.rewindBody]

/-! ## Evaluation of the setup and the cleanup -/

theorem setupC_eval (v : CReg) (S : CK → List Sym) :
    Eval [] setupC ⟨v, S⟩
      ⟨v, Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S cT (Sym.mark :: S cT)) cR1 (Sym.mark :: S cR1))
        cR1' (Sym.mark :: S cR1')) cR2 (Sym.mark :: S cR2)) cR2' (Sym.mark :: S cR2'))
        cR3 (Sym.mark :: S cR3)) cR3' (Sym.mark :: S cR3')⟩ 7 := by
  refine (Eval.seq (cpc_eval _ _ _ _) (Eval.seq (cpc_eval _ _ _ _) (Eval.seq (cpc_eval _ _ _ _)
    (Eval.seq (cpc_eval _ _ _ _) (Eval.seq (cpc_eval _ _ _ _) (Eval.seq (cpc_eval _ _ _ _)
      (cpc_eval _ _ _ _))))))).of_eq (st_eqC rfl ?_) rfl
  funext k
  rcases k with k | k <;> fin_cases k <;> simp

theorem cleanupC_eval (w1 w2 w3 : ℕ) (R10 R1'0 R20 R2'0 R30 R3'0 : List Sym) (v : CReg)
    (S : CK → List Sym)
    (hR1 : S cR1 = toks w1 ++ Sym.mark :: R10) (hR1' : S cR1' = Sym.mark :: R1'0)
    (hR2 : S cR2 = toks w2 ++ Sym.mark :: R20) (hR2' : S cR2' = Sym.mark :: R2'0)
    (hR3 : S cR3 = toks w3 ++ Sym.mark :: R30) (hR3' : S cR3' = Sym.mark :: R3'0) :
    ∃ v' : CReg, Eval [] cleanupC ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S cR1 R10) cR1' R1'0) cR2 R20) cR2' R2'0) cR3 R30) cR3' R3'0⟩
      (3 * w1 + 3 * w2 + 3 * w3 + 12) := by
  obtain ⟨o, p, la, lb, c⟩ := v
  have m1 := dropBits_eval cR1 (List.replicate w1 true) (Sym.mark :: R10) o p la lb S
    (TermOK.cons rfl _) (by rw [hR1, toks_eq_map])
  have e1 := Eval.liftRegs lensC m1 (o, p, la, lb, c) rfl
  set S1 := Function.update S cR1 (Sym.mark :: R10) with hS1
  have e2 := cpd_eval cR1 (some Sym.mark, p, la, lb, c) S1 Sym.mark R10 (by simp [hS1])
  set S2 := Function.update S1 cR1 R10 with hS2
  have m3 := dropBits_eval cR2 (List.replicate w2 true) (Sym.mark :: R20) (some Sym.mark) p la lb
    S2 (TermOK.cons rfl _) (by simp [hS2, hS1, hR2, toks_eq_map])
  have e3 := Eval.liftRegs lensC m3 (some Sym.mark, p, la, lb, c) rfl
  set S3 := Function.update S2 cR2 (Sym.mark :: R20) with hS3
  have e4 := cpd_eval cR2 (some Sym.mark, p, la, lb, c) S3 Sym.mark R20 (by simp [hS3])
  set S4 := Function.update S3 cR2 R20 with hS4
  have m5 := dropBits_eval cR3 (List.replicate w3 true) (Sym.mark :: R30) (some Sym.mark) p la lb
    S4 (TermOK.cons rfl _) (by simp [hS4, hS3, hS2, hS1, hR3, toks_eq_map])
  have e5 := Eval.liftRegs lensC m5 (some Sym.mark, p, la, lb, c) rfl
  set S5 := Function.update S4 cR3 (Sym.mark :: R30) with hS5
  have e6 := cpd_eval cR3 (some Sym.mark, p, la, lb, c) S5 Sym.mark R30 (by simp [hS5])
  set S6 := Function.update S5 cR3 R30 with hS6
  have e7 := cpd_eval cR1' (some Sym.mark, p, la, lb, c) S6 Sym.mark R1'0
    (by simp [hS6, hS5, hS4, hS3, hS2, hS1, hR1'])
  set S7 := Function.update S6 cR1' R1'0 with hS7
  have e8 := cpd_eval cR2' (some Sym.mark, p, la, lb, c) S7 Sym.mark R2'0
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hR2'])
  set S8 := Function.update S7 cR2' R2'0 with hS8
  have e9 := cpd_eval cR3' (some Sym.mark, p, la, lb, c) S8 Sym.mark R3'0
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hR3'])
  refine ⟨_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 (Eval.seq e8 e9)))))))).of_eq (st_eqC rfl ?_) ?_⟩
  · clear e1 e2 e3 e4 e5 e6 e7 e8 e9 m1 m3 m5
    funext k
    rcases k with k | k <;> fin_cases k <;> simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]
  · simp only [List.length_replicate]
    omega

/-! ## Volumes and the cost bound -/

theorem cvol_nil' (w : ℕ) : cvol w [] = 0 := rfl

theorem cvol_cons' (w : ℕ) (cs : List CInt) (v : List (List CInt)) :
    cvol w (cs :: v) = 2 * cs.length * w + 1 + cvol w v := by
  simp only [cvol, carrSyms, List.map_cons, arrSyms_cons, List.length_append, recSyms,
    List.length_map, List.length_cons, List.length_nil, crecBits_eq', length_flatMap_twosBits,
    length_compsC]

theorem cvol_zipC (w : ℕ) (h : CInt → CInt → CInt) :
    ∀ (u v : List (List CInt)), CAligned u v → cvol w (zipC h u v) = cvol w u
  | [], [], _ => rfl
  | [], _ :: _, hal => by simp [CAligned] at hal
  | _ :: _, [], hal => by simp [CAligned] at hal
  | cs :: u, ds :: v, hal => by
    rw [CAligned, List.forall₂_cons] at hal
    have ih := cvol_zipC w h u v hal.2
    simp only [zipC, List.zipWith_cons_cons] at ih ⊢
    rw [cvol_cons', cvol_cons', ih, List.length_zipWith, hal.1, min_self]

theorem recCost_le (w1 w2 w3 : ℕ) (hw1 : 1 ≤ w1) :
    ∀ (us vs : List (List CInt)), CAligned us vs →
      (us.map fun cs => 2 * cs.length * (30 * (w1 + w2 + w3) + 22) + 7).sum ≤
        60 * (cvol w1 us + cvol w2 vs + cvol w3 us)
  | [], [], _ => by simp
  | [], _ :: _, hal => by simp [CAligned] at hal
  | _ :: _, [], hal => by simp [CAligned] at hal
  | cs :: us, ds :: vs, hal => by
    rw [CAligned, List.forall₂_cons] at hal
    have ih := recCost_le w1 w2 w3 hw1 us vs hal.2
    rw [List.map_cons, List.sum_cons, cvol_cons', cvol_cons', cvol_cons', ← hal.1]
    have q1 : 2 * cs.length * (30 * (w1 + w2 + w3) + 22) =
        60 * (cs.length * w1) + 60 * (cs.length * w2) + 60 * (cs.length * w3) + 44 * cs.length := by
      ring
    have q2 : 2 * cs.length * w1 = 2 * (cs.length * w1) := by ring
    have q3 : 2 * cs.length * w2 = 2 * (cs.length * w2) := by ring
    have q4 : 2 * cs.length * w3 = 2 * (cs.length * w3) := by ring
    have hn : cs.length ≤ cs.length * w1 := Nat.le_mul_of_pos_right _ hw1
    rw [q1, q2, q3, q4]
    generalize cs.length * w1 = P1 at *
    generalize cs.length * w2 = P2 at *
    generalize cs.length * w3 = P3 at *
    omega

/-! ## The kernel -/

theorem cMain_eval (f : Bool → Bool → Bool → Bool × Bool) (g : ℤ → ℤ → ℤ)
    (hfg : ∀ w a b, ripOut f false (twosBits w a) (twosBits w b) = twosBits w (g a b))
    (h : CInt → CInt → CInt) (hh : ∀ a b, h a b = (g a.1 b.1, g a.2 b.2))
    (w1 w2 w3 : ℕ) (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (u v : List (List CInt)) (ru rv r3 r4 r5 : List Sym) (S : CK → List Sym)
    (hal : CAligned u v) (hfu : CArrFits w1 u) (hfv : CArrFits w2 v) (hru : BlkTerm ru)
    (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5)
    (hU : S cU = carrSyms w1 u ++ ru) (hV : S cV = carrSyms w2 v ++ rv)
    (hW1 : S cW1 = natSyms w1 ++ r3) (hW2 : S cW2 = natSyms w2 ++ r4)
    (hW3 : S cW3 = natSyms w3 ++ r5) (o p : Option Sym) (la lb c : Bool) :
    ∃ (v' : CReg) (t : ℕ), t ≤ 200 * (cvol w1 u + cvol w2 v + cvol w3 u + w1 + w2 + w3 + 1) ∧
      Eval [] (cMain f) ⟨(o, p, la, lb, c), S⟩
        ⟨v', Function.update (Function.update (Function.update S cU ru) cV rv) cD
          (carrSyms w3 (zipC h u v) ++ S cD)⟩ t := by
  -- 1. guards
  have e1 := setupC_eval (o, p, la, lb, c) S
  set S1 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update S cT (Sym.mark :: S cT)) cR1 (Sym.mark :: S cR1))
    cR1' (Sym.mark :: S cR1')) cR2 (Sym.mark :: S cR2)) cR2' (Sym.mark :: S cR2'))
    cR3 (Sym.mark :: S cR3)) cR3' (Sym.mark :: S cR3') with hS1
  -- 2. ruler `w1`
  obtain ⟨t2, ht2, m2⟩ := buildU_eval (kW := cW1) (kC := cC) (kM := cM) (kU := cR1) (by decide)
    (by decide) (by decide) (by decide) w1 r3 hr3 o p la lb S1 (by simp [hS1, hW1])
  have e2 := Eval.liftRegs lensC m2 (o, p, la, lb, c) rfl
  have h1C : S1 cC = S cC := by simp [hS1]
  have h1R1 : S1 cR1 = Sym.mark :: S cR1 := by simp [hS1]
  rw [h1C, h1R1] at e2
  set S2 := Function.update (Function.update S1 cC (Sym.mark :: S cC)) cR1
    (toks w1 ++ Sym.mark :: S cR1) with hS2
  have e3 := cpd_eval cC (some Sym.mark, p, la, lb, c) S2 Sym.mark (S cC) (by simp [hS2])
  set S3 := Function.update S2 cC (S cC) with hS3
  -- 3. ruler `w2`
  obtain ⟨t4, ht4, m4⟩ := buildU_eval (kW := cW2) (kC := cC) (kM := cM) (kU := cR2) (by decide)
    (by decide) (by decide) (by decide) w2 r4 hr4 (some Sym.mark) p la lb S3
    (by simp [hS3, hS2, hS1, hW2])
  have e4 := Eval.liftRegs lensC m4 (some Sym.mark, p, la, lb, c) rfl
  have h3C : S3 cC = S cC := by simp [hS3]
  have h3R2 : S3 cR2 = Sym.mark :: S cR2 := by simp [hS3, hS2, hS1]
  rw [h3C, h3R2] at e4
  set S4 := Function.update (Function.update S3 cC (Sym.mark :: S cC)) cR2
    (toks w2 ++ Sym.mark :: S cR2) with hS4
  have e5 := cpd_eval cC (some Sym.mark, p, la, lb, c) S4 Sym.mark (S cC) (by simp [hS4])
  set S5 := Function.update S4 cC (S cC) with hS5
  -- 4. ruler `w3`
  obtain ⟨t6, ht6, m6⟩ := buildU_eval (kW := cW3) (kC := cC) (kM := cM) (kU := cR3) (by decide)
    (by decide) (by decide) (by decide) w3 r5 hr5 (some Sym.mark) p la lb S5
    (by simp [hS5, hS4, hS3, hS2, hS1, hW3])
  have e6 := Eval.liftRegs lensC m6 (some Sym.mark, p, la, lb, c) rfl
  have h5C : S5 cC = S cC := by simp [hS5]
  have h5R3 : S5 cR3 = Sym.mark :: S cR3 := by simp [hS5, hS4, hS3, hS2, hS1]
  rw [h5C, h5R3] at e6
  set S6 := Function.update (Function.update S5 cC (Sym.mark :: S cC)) cR3
    (toks w3 ++ Sym.mark :: S cR3) with hS6
  have e7 := cpd_eval cC (some Sym.mark, p, la, lb, c) S6 Sym.mark (S cC) (by simp [hS6])
  set S7 := Function.update S6 cC (S cC) with hS7
  -- 5. peek the first operand
  have e8 := cpkO_eval cU (some Sym.mark, p, la, lb, c) S7
  -- 6. records
  obtain ⟨v9, t9, ht9, e9⟩ := recLoopC_eval f g hfg h hh w1 w2 w3 hw1 hw2 (S cR1) (S cR1')
    (S cR2) (S cR2') (S cR3) (S cR3') ru rv hru u v (S7 cU).head? p la lb c S7 hal hfu hfv
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hU])
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hV])
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2]) (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS7, hS6, hS5, hS4]) (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS7, hS6]) (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1]) rfl
  have h7T : S7 cT = Sym.mark :: S cT := by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1]
  rw [h7T] at e9
  set out := carrSyms w3 (zipC h u v) with hout
  set S9 := Function.update (Function.update (Function.update S7 cU ru) cV rv) cT
    (out.reverse ++ Sym.mark :: S cT) with hS9
  -- 7. rewind the output buffer onto the destination
  have hmark : Sym.mark ∉ out.reverse := by
    rw [List.mem_reverse, hout, carrSyms]
    exact mark_not_mem_arrSyms _
  have e10 := Eval.liftRegs lensCo (WP.W9comp.rewindTo_eval (by decide : cT ≠ cD) Sym.mark
    (lensCo.get v9) out.reverse (S cT) S9 hmark (by simp [hS9])) v9 rfl
  have h9D : S9 cD = S cD := by simp [hS9, hS7, hS6, hS5, hS4, hS3, hS2, hS1]
  rw [h9D, List.reverse_reverse] at e10
  set S10 := Function.update (Function.update S9 cT (S cT)) cD (out ++ S cD) with hS10
  -- 8. cleanup
  obtain ⟨v11, e11⟩ := cleanupC_eval w1 w2 w3 (S cR1) (S cR1') (S cR2) (S cR2') (S cR3) (S cR3')
    (lensCo.set v9 (some Sym.mark)) S10
    (by simp [hS10, hS9, hS7, hS6, hS5, hS4, hS3, hS2])
    (by simp [hS10, hS9, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS10, hS9, hS7, hS6, hS5, hS4])
    (by simp [hS10, hS9, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS10, hS9, hS7, hS6])
    (by simp [hS10, hS9, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
  refine ⟨v11, _, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 (Eval.seq e10 e11)))))))))).of_eq
    (st_eqC rfl ?_) rfl⟩
  · have hc := recCost_le w1 w2 w3 hw1 u v hal
    have hb1 := bitLen_le_self w1
    have hb2 := bitLen_le_self w2
    have hb3 := bitLen_le_self w3
    have hlo : out.reverse.length = cvol w3 u := by
      rw [List.length_reverse, hout, ← cvol, cvol_zipC w3 h u v hal]
    rw [hlo]
    omega
  · clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 m2 m4 m6
    funext k
    rcases k with k | k <;> fin_cases k <;>
      simp [hS10, hS9, hS7, hS6, hS5, hS4, hS3, hS2, hS1]

end SubNLogN.Machine.Arith.CAddAux

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.K1 SubNLogN.Machine.Arith.CAddAux

/-- **AR6, exact coefficientwise sum, proved** (`CAddStmt`, `Contracts/Arith.lean`; paper:
Lemma A.4(5) (`lem:transfer-streams`)). Kernel `CAddAux.cMain addBit` on `KLoc (Fin 6) (Fin 9)`, constant `C = 200`. The
hypotheses `1 ≤ w3`, `BlkTerm rv` and the output fit are not used. -/
theorem cAdd_holds : CAddStmt := by
  refine ⟨200, fun _ => ⟨Fin 9, inferInstance, inferInstance, CReg, cMain addBit, inferInstance,
    inferInstance, closed_cMain _, ?_⟩⟩
  intro w1 w2 w3 u v ru rv r3 r4 r5 S hw1 hw2 _ hfu hfv hal _ hru _ hr3 hr4 hr5 hU hV hW1 hW2 hW3
  apply Runs.of_eval
  rintro ⟨o, p, la, lb, c⟩
  obtain ⟨v', t, ht, e⟩ := cMain_eval addBit (· + ·) ripOut_add caddC (fun _ _ => rfl) w1 w2 w3
    hw1 hw2 u v ru rv r3 r4 r5 S hal hfu hfv hru hr3 hr4 hr5 hU hV hW1 hW2 hW3 o p la lb c
  exact ⟨v', t, e, trivial, ht⟩

/-- **AR6', exact coefficientwise difference, proved** (`CSubStmt`, `Contracts/Arith.lean`).
Kernel `CAddAux.cMain subBit`, constant `C = 200`. The hypotheses `1 ≤ w3`, `BlkTerm rv` and the
output fit are not used. -/
theorem cSub_holds : CSubStmt := by
  refine ⟨200, fun _ => ⟨Fin 9, inferInstance, inferInstance, CReg, cMain subBit, inferInstance,
    inferInstance, closed_cMain _, ?_⟩⟩
  intro w1 w2 w3 u v ru rv r3 r4 r5 S hw1 hw2 _ hfu hfv hal _ hru _ hr3 hr4 hr5 hU hV hW1 hW2 hW3
  apply Runs.of_eval
  rintro ⟨o, p, la, lb, c⟩
  obtain ⟨v', t, ht, e⟩ := cMain_eval subBit (· - ·) ripOut_sub csubC (fun _ _ => rfl) w1 w2 w3
    hw1 hw2 u v ru rv r3 r4 r5 S hal hfu hfv hru hr3 hr4 hr5 hU hV hW1 hW2 hW3 o p la lb c
  exact ⟨v', t, e, trivial, ht⟩

end SubNLogN.Machine.Arith
