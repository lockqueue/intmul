/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.HalfSumLoop

/-!
# `SubNLogN.Machine.Arith.HalfSum`: the normalized butterfly `Q((u ± v)/2)` (AR2)

Paper: Theorem 6.5 (`thm:direct-fft`, last-axis DIF step: form each half-sum and
half-difference exactly and truncate to the `q`-grid); contract `HalfSumDiffStmt`
(`Contracts/Arith.lean`).

## Plan
`hMain` on `KLoc (Fin 5) (Fin 13)` (`HalfSumAux.HSK`, program design in `HalfSumProg`): guards
on the private stacks; rulers `R1 := w`, `R2 := w`, `R3 := w + 1` tokens
(`K1.ShiftAux.buildU`, amortized `O(w)`, the counter `w` is restored); the record loop
(`HalfSumLoop`), which runs the field kernel (`HalfSumEmit.fieldH`: `w + 1` ripple steps
computing the exact `(w+1)`-bit fields of `a + b` and `a - b`, then two halvings toward zero)
on every field; both output buffers are rewound onto their destinations; rulers and guards are
removed. The output fields are `twosBits w (tdiv (a ± b) 2)` (`half_bits`; the sign extension
uses `FitsTwos w a`, `FitsTwos w b`, which also give `FitsTwos (w+1) (a ± b)`).

**Scope (honest summary).** Proved (no `sorry`): `halfSumDiff_holds : HalfSumDiffStmt`, in
`SubNLogN.Machine.Arith`; helpers in `SubNLogN.Machine.Arith.HalfSumAux`. Of the contract's
hypotheses the proof uses all except `BlkTerm rv`.
-/

namespace SubNLogN.Machine.Arith.HalfSumAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1
  SubNLogN.Machine.K1.AddSubAux SubNLogN.Machine.K1.ShiftAux SubNLogN.Machine.Arith.CAddAux

/-! ## Evaluation of the setup and the cleanup -/

theorem setupH_eval (v : HReg) (S : HSK → List Sym) :
    Eval [] setupH ⟨v, S⟩
      ⟨v, Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S hkTs (Sym.mark :: S hkTs)) hkTd (Sym.mark :: S hkTd))
        hkR1 (Sym.mark :: S hkR1)) hkR1' (Sym.mark :: S hkR1')) hkR2 (Sym.mark :: S hkR2))
        hkR2' (Sym.mark :: S hkR2')) hkR3 (Sym.mark :: S hkR3)) hkR3' (Sym.mark :: S hkR3'))
        hkA (Sym.mark :: S hkA)) hkB (Sym.mark :: S hkB)) hkA' (Sym.mark :: S hkA')⟩ 11 := by
  refine (Eval.seq (qpc_eval _ _ _ _) (Eval.seq (qpc_eval _ _ _ _) (Eval.seq (qpc_eval _ _ _ _)
    (Eval.seq (qpc_eval _ _ _ _) (Eval.seq (qpc_eval _ _ _ _) (Eval.seq (qpc_eval _ _ _ _)
    (Eval.seq (qpc_eval _ _ _ _) (Eval.seq (qpc_eval _ _ _ _) (Eval.seq (qpc_eval _ _ _ _)
    (Eval.seq (qpc_eval _ _ _ _) (qpc_eval _ _ _ _))))))))))).of_eq (st_eqH rfl ?_) rfl
  funext k
  rcases k with k | k <;> fin_cases k <;> simp

theorem cleanupH_eval (w : ℕ) (R10 R1'0 R20 R2'0 R30 R3'0 RA RB RA' : List Sym) (v : HReg)
    (S : HSK → List Sym)
    (hR1 : S hkR1 = toks w ++ Sym.mark :: R10) (hR1' : S hkR1' = Sym.mark :: R1'0)
    (hR2 : S hkR2 = toks w ++ Sym.mark :: R20) (hR2' : S hkR2' = Sym.mark :: R2'0)
    (hR3 : S hkR3 = toks (w + 1) ++ Sym.mark :: R30) (hR3' : S hkR3' = Sym.mark :: R3'0)
    (hA : S hkA = Sym.mark :: RA) (hB : S hkB = Sym.mark :: RB)
    (hA' : S hkA' = Sym.mark :: RA') :
    ∃ v' : HReg, Eval [] cleanupH ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update S hkR1 R10)
        hkR1' R1'0) hkR2 R20) hkR2' R2'0) hkR3 R30) hkR3' R3'0) hkA RA) hkB RB) hkA' RA'⟩
      (9 * w + 18) := by
  obtain ⟨o, p, la, lb, c1, c2⟩ := v
  have m1 := dropBits_eval hkR1 (List.replicate w true) (Sym.mark :: R10) o p la lb S
    (TermOK.cons rfl _) (by rw [hR1, toks_eq_map])
  have e1 := Eval.liftRegs lensHX m1 (o, p, la, lb, c1, c2) rfl
  set S1 := Function.update S hkR1 (Sym.mark :: R10) with hS1
  have e2 := qpd_eval hkR1 (some Sym.mark, p, la, lb, c1, c2) S1 Sym.mark R10 (by simp [hS1])
  set S2 := Function.update S1 hkR1 R10 with hS2
  have m3 := dropBits_eval hkR2 (List.replicate w true) (Sym.mark :: R20) (some Sym.mark) p la
    lb S2 (TermOK.cons rfl _) (by simp [hS2, hS1, hR2, toks_eq_map])
  have e3 := Eval.liftRegs lensHX m3 (some Sym.mark, p, la, lb, c1, c2) rfl
  set S3 := Function.update S2 hkR2 (Sym.mark :: R20) with hS3
  have e4 := qpd_eval hkR2 (some Sym.mark, p, la, lb, c1, c2) S3 Sym.mark R20 (by simp [hS3])
  set S4 := Function.update S3 hkR2 R20 with hS4
  have m5 := dropBits_eval hkR3 (List.replicate (w + 1) true) (Sym.mark :: R30) (some Sym.mark)
    p la lb S4 (TermOK.cons rfl _) (by simp [hS4, hS3, hS2, hS1, hR3, toks_eq_map])
  have e5 := Eval.liftRegs lensHX m5 (some Sym.mark, p, la, lb, c1, c2) rfl
  set S5 := Function.update S4 hkR3 (Sym.mark :: R30) with hS5
  have e6 := qpd_eval hkR3 (some Sym.mark, p, la, lb, c1, c2) S5 Sym.mark R30 (by simp [hS5])
  set S6 := Function.update S5 hkR3 R30 with hS6
  have e7 := qpd_eval hkR1' (some Sym.mark, p, la, lb, c1, c2) S6 Sym.mark R1'0
    (by simp [hS6, hS5, hS4, hS3, hS2, hS1, hR1'])
  set S7 := Function.update S6 hkR1' R1'0 with hS7
  have e8 := qpd_eval hkR2' (some Sym.mark, p, la, lb, c1, c2) S7 Sym.mark R2'0
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hR2'])
  set S8 := Function.update S7 hkR2' R2'0 with hS8
  have e9 := qpd_eval hkR3' (some Sym.mark, p, la, lb, c1, c2) S8 Sym.mark R3'0
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hR3'])
  set S9 := Function.update S8 hkR3' R3'0 with hS9
  have e10 := qpd_eval hkA (some Sym.mark, p, la, lb, c1, c2) S9 Sym.mark RA
    (by simp [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hA])
  set S10 := Function.update S9 hkA RA with hS10
  have e11 := qpd_eval hkB (some Sym.mark, p, la, lb, c1, c2) S10 Sym.mark RB
    (by simp [hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hB])
  set S11 := Function.update S10 hkB RB with hS11
  have e12 := qpd_eval hkA' (some Sym.mark, p, la, lb, c1, c2) S11 Sym.mark RA'
    (by simp [hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hA'])
  refine ⟨_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 (Eval.seq e10 (Eval.seq e11
      e12))))))))))).of_eq (st_eqH rfl ?_) ?_⟩
  · clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 m1 m3 m5
    funext k
    rcases k with k | k <;> fin_cases k <;>
      simp [hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]
  · simp only [List.length_replicate]
    omega

/-! ## The cost bound -/

theorem recCostH_le (w : ℕ) (hw : 1 ≤ w) :
    ∀ (us : List (List CInt)),
      (us.map fun cs => 2 * cs.length * (50 * w + 82) + 8).sum ≤ 132 * cvol w us
  | [] => by simp
  | cs :: us => by
    have ih := recCostH_le w hw us
    rw [List.map_cons, List.sum_cons, cvol_cons']
    have q1 : 2 * cs.length * (50 * w + 82) = 100 * (cs.length * w) + 164 * cs.length := by ring
    have q2 : 2 * cs.length * w = 2 * (cs.length * w) := by ring
    have hn : cs.length ≤ cs.length * w := Nat.le_mul_of_pos_right _ hw
    rw [q1, q2]
    generalize cs.length * w = P at *
    omega

/-! ## The kernel -/

theorem hMain_eval (w : ℕ) (hw : 1 ≤ w) (u v : List (List CInt)) (ru rv r4 : List Sym)
    (S : HSK → List Sym) (hal : CAligned u v) (hfu : CArrFits w u) (hfv : CArrFits w v)
    (hru : BlkTerm ru) (hr4 : TermOK r4)
    (hU : S hkU = carrSyms w u ++ ru) (hV : S hkV = carrSyms w v ++ rv)
    (hW : S hkW = natSyms w ++ r4) (o p : Option Sym) (la lb c1 c2 : Bool) :
    ∃ (v' : HReg) (t : ℕ), t ≤ 200 * (cvol w u + cvol w v + w + 1) ∧
      Eval [] hMain ⟨(o, p, la, lb, c1, c2), S⟩
        ⟨v', Function.update (Function.update (Function.update (Function.update S hkU ru)
          hkV rv) hkDs (carrSyms w (zipC halfSumC u v) ++ S hkDs))
          hkDd (carrSyms w (zipC halfDiffC u v) ++ S hkDd)⟩ t := by
  -- 1. guards
  have e1 := setupH_eval (o, p, la, lb, c1, c2) S
  set S1 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update S hkTs (Sym.mark :: S hkTs)) hkTd (Sym.mark :: S hkTd))
    hkR1 (Sym.mark :: S hkR1)) hkR1' (Sym.mark :: S hkR1')) hkR2 (Sym.mark :: S hkR2))
    hkR2' (Sym.mark :: S hkR2')) hkR3 (Sym.mark :: S hkR3)) hkR3' (Sym.mark :: S hkR3'))
    hkA (Sym.mark :: S hkA)) hkB (Sym.mark :: S hkB)) hkA' (Sym.mark :: S hkA') with hS1
  -- 2. ruler `R1`
  obtain ⟨t2, ht2, m2⟩ := buildU_eval (kW := hkW) (kC := hkC) (kM := hkM) (kU := hkR1)
    (by decide) (by decide) (by decide) (by decide) w r4 hr4 o p la lb S1 (by simp [hS1, hW])
  have e2 := Eval.liftRegs lensHX m2 (o, p, la, lb, c1, c2) rfl
  have h1C : S1 hkC = S hkC := by simp [hS1]
  have h1R1 : S1 hkR1 = Sym.mark :: S hkR1 := by simp [hS1]
  rw [h1C, h1R1] at e2
  set S2 := Function.update (Function.update S1 hkC (Sym.mark :: S hkC)) hkR1
    (toks w ++ Sym.mark :: S hkR1) with hS2
  have e3 := qpd_eval hkC (some Sym.mark, p, la, lb, c1, c2) S2 Sym.mark (S hkC) (by simp [hS2])
  set S3 := Function.update S2 hkC (S hkC) with hS3
  -- 3. ruler `R2`
  obtain ⟨t4, ht4, m4⟩ := buildU_eval (kW := hkW) (kC := hkC) (kM := hkM) (kU := hkR2)
    (by decide) (by decide) (by decide) (by decide) w r4 hr4 (some Sym.mark) p la lb S3
    (by simp [hS3, hS2, hS1, hW])
  have e4 := Eval.liftRegs lensHX m4 (some Sym.mark, p, la, lb, c1, c2) rfl
  have h3C : S3 hkC = S hkC := by simp [hS3]
  have h3R2 : S3 hkR2 = Sym.mark :: S hkR2 := by simp [hS3, hS2, hS1]
  rw [h3C, h3R2] at e4
  set S4 := Function.update (Function.update S3 hkC (Sym.mark :: S hkC)) hkR2
    (toks w ++ Sym.mark :: S hkR2) with hS4
  have e5 := qpd_eval hkC (some Sym.mark, p, la, lb, c1, c2) S4 Sym.mark (S hkC) (by simp [hS4])
  set S5 := Function.update S4 hkC (S hkC) with hS5
  -- 4. ruler `R3` (`w + 1` tokens)
  obtain ⟨t6, ht6, m6⟩ := buildU_eval (kW := hkW) (kC := hkC) (kM := hkM) (kU := hkR3)
    (by decide) (by decide) (by decide) (by decide) w r4 hr4 (some Sym.mark) p la lb S5
    (by simp [hS5, hS4, hS3, hS2, hS1, hW])
  have e6 := Eval.liftRegs lensHX m6 (some Sym.mark, p, la, lb, c1, c2) rfl
  have h5C : S5 hkC = S hkC := by simp [hS5]
  have h5R3 : S5 hkR3 = Sym.mark :: S hkR3 := by simp [hS5, hS4, hS3, hS2, hS1]
  rw [h5C, h5R3] at e6
  set S6 := Function.update (Function.update S5 hkC (Sym.mark :: S hkC)) hkR3
    (toks w ++ Sym.mark :: S hkR3) with hS6
  have e7 := qpd_eval hkC (some Sym.mark, p, la, lb, c1, c2) S6 Sym.mark (S hkC) (by simp [hS6])
  set S7 := Function.update S6 hkC (S hkC) with hS7
  have e8 := qpc_eval hkR3 (Sym.bit true) (some Sym.mark, p, la, lb, c1, c2) S7
  have h7R3 : S7 hkR3 = toks w ++ Sym.mark :: S hkR3 := by simp [hS7, hS6]
  rw [h7R3] at e8
  set S8 := Function.update S7 hkR3 (Sym.bit true :: (toks w ++ Sym.mark :: S hkR3)) with hS8
  -- 5. peek the first operand
  have e9 := qpkO_eval hkU (some Sym.mark, p, la, lb, c1, c2) S8
  -- 6. records
  obtain ⟨v10, t10, ht10, e10⟩ := recLoopH_eval w hw (S hkR1) (S hkR1') (S hkR2) (S hkR2')
    (S hkR3) (S hkR3') (S hkA) (S hkB) (S hkA') ru rv hru u v (S8 hkU).head? p la lb c1 c2 S8
    hal hfu hfv
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hU])
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hV])
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2])
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS8, hS7, hS6, hS5, hS4])
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS8, toks, List.replicate_succ])
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]) rfl
  have h8Ts : S8 hkTs = Sym.mark :: S hkTs := by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]
  have h8Td : S8 hkTd = Sym.mark :: S hkTd := by simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]
  rw [h8Ts, h8Td] at e10
  set outS := carrSyms w (zipC halfSumC u v) with houtS
  set outD := carrSyms w (zipC halfDiffC u v) with houtD
  set S10 := Function.update (Function.update (Function.update (Function.update S8 hkU ru)
    hkV rv) hkTs (outS.reverse ++ Sym.mark :: S hkTs)) hkTd (outD.reverse ++ Sym.mark :: S hkTd)
    with hS10
  -- 7. rewind the output buffers onto the destinations
  have hmS : Sym.mark ∉ outS.reverse := by
    rw [List.mem_reverse, houtS, carrSyms]
    exact mark_not_mem_arrSyms _
  have hmD : Sym.mark ∉ outD.reverse := by
    rw [List.mem_reverse, houtD, carrSyms]
    exact mark_not_mem_arrSyms _
  have e11 := Eval.liftRegs lensHo (WP.W9comp.rewindTo_eval (by decide : hkTs ≠ hkDs) Sym.mark
    (lensHo.get v10) outS.reverse (S hkTs) S10 hmS (by simp [hS10])) v10 rfl
  have h10Ds : S10 hkDs = S hkDs := by simp [hS10, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]
  rw [h10Ds, List.reverse_reverse] at e11
  set S11 := Function.update (Function.update S10 hkTs (S hkTs)) hkDs (outS ++ S hkDs) with hS11
  have e12 := Eval.liftRegs lensHo (WP.W9comp.rewindTo_eval (by decide : hkTd ≠ hkDd) Sym.mark
    (lensHo.get (lensHo.set v10 (some Sym.mark))) outD.reverse (S hkTd) S11 hmD
    (by simp [hS11, hS10])) (lensHo.set v10 (some Sym.mark)) rfl
  have h11Dd : S11 hkDd = S hkDd := by
    simp [hS11, hS10, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]
  rw [h11Dd, List.reverse_reverse] at e12
  set S12 := Function.update (Function.update S11 hkTd (S hkTd)) hkDd (outD ++ S hkDd) with hS12
  -- 8. cleanup
  obtain ⟨v13, e13⟩ := cleanupH_eval w (S hkR1) (S hkR1') (S hkR2) (S hkR2') (S hkR3) (S hkR3')
    (S hkA) (S hkB) (S hkA') (lensHo.set (lensHo.set v10 (some Sym.mark)) (some Sym.mark)) S12
    (by simp [hS12, hS11, hS10, hS8, hS7, hS6, hS5, hS4, hS3, hS2])
    (by simp [hS12, hS11, hS10, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS12, hS11, hS10, hS8, hS7, hS6, hS5, hS4])
    (by simp [hS12, hS11, hS10, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS12, hS11, hS10, hS8, toks, List.replicate_succ])
    (by simp [hS12, hS11, hS10, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS12, hS11, hS10, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS12, hS11, hS10, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
    (by simp [hS12, hS11, hS10, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1])
  refine ⟨v13, _, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 (Eval.seq e10 (Eval.seq e11
    (Eval.seq e12 e13)))))))))))).of_eq (st_eqH rfl ?_) rfl⟩
  · have hc := recCostH_le w hw u
    have hb := bitLen_le_self w
    have hloS : outS.reverse.length = cvol w u := by
      rw [List.length_reverse, houtS, ← cvol, cvol_zipC w halfSumC u v hal]
    have hloD : outD.reverse.length = cvol w u := by
      rw [List.length_reverse, houtD, ← cvol, cvol_zipC w halfDiffC u v hal]
    rw [hloS, hloD]
    omega
  · clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 m2 m4 m6
    funext k
    rcases k with k | k <;> fin_cases k <;>
      simp [hS12, hS11, hS10, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]

end SubNLogN.Machine.Arith.HalfSumAux

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith.HalfSumAux

/-- **AR2, normalized butterfly `Q((u ± v)/2)`, proved** (`HalfSumDiffStmt`,
`Contracts/Arith.lean`; paper: Theorem 6.5 (`thm:direct-fft`)). Kernel `HalfSumAux.hMain` on
`KLoc (Fin 5) (Fin 13)`, registers `HalfSumAux.HReg`, constant `C = 200`. Every output component
is `tdiv (a ± b) 2` (truncation toward zero, not an arithmetic shift) in a `w`-bit field. The
hypothesis `BlkTerm rv` is not used. -/
theorem halfSumDiff_holds : HalfSumDiffStmt := by
  refine ⟨200, fun _ => ⟨Fin 13, inferInstance, inferInstance, HReg, hMain, inferInstance,
    inferInstance, closed_hMain, ?_⟩⟩
  intro w u v ru rv r4 S hw hfu hfv hal hru _ hr4 hU hV hW
  apply Runs.of_eval
  rintro ⟨o, p, la, lb, c1, c2⟩
  obtain ⟨v', t, ht, e⟩ := hMain_eval w hw u v ru rv r4 S hal hfu hfv hru hr4 hU hV hW o p la lb
    c1 c2
  exact ⟨v', t, e, trivial, ht⟩

end SubNLogN.Machine.Arith
