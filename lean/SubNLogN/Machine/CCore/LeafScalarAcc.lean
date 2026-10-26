/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafScalarAccLoop

/-!
# Scalar row leaf: the record-accumulate kernel `AccStmt` (`CCore/LeafScalarAcc.lean`)

**Main result.** `SubNLogN.Machine.CCore.acc_holds : LeafScalarAux.AccStmt`
(`CCore/LeafScalarDefs.lean`), with no hypotheses. For each coefficient `c ∈ {+1, -1, +1/2, -1/2}`
a closed kernel consumes the aligned record arrays `u` (stack `0`) and `v` (stack `1`) and pushes
`carrSyms w (zipC (accC c) u v)` on stack `2`: the `w`-bit fields (i.e. modulo `2^w`) of
`a + coefInt c b`, with `coefInt c b ∈ {b, -b, ⌊b/2⌋, -⌊b/2⌋}`; the width `w` is read from stack
`3` (restored). Cost `300·(cvol w u + cvol w v + w + 1)`. Of the contract's hypotheses, `KClean S`
and `BlkTerm rv` are not used, and `CArrFits w v` is used only for `c = ±1/2`.

**Kernel** (`aMain`, on the `CAddAux.CK` layout (`Arith/CAddProg.lean`), embedded by `callInj` along `ιA`): `CAddAux` guards
(`setupC`); three unary rulers of `w` tokens built from the width counter
(`K1.ShiftAux.buildU`), for `c = ±1/2` one token of the `v`-ruler dropped (`dropOne`); the record
loop `recLoopA` (`LeafScalarAccLoop.lean`: per field the ripple kernel `CAddAux.fieldC` with the full
adder for `c = +1, +1/2` or the full subtractor for `c = -1, -1/2`, after reading the first bit of
`v` into the sign-extension register for `c = ±1/2`); the output buffer rewound onto stack `2`
(`WP.W9comp.rewindTo`); cleanup (`cleanupC`).
-/

namespace SubNLogN.Machine.CCore.LeafScalarAccAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1
  SubNLogN.Machine.K1.AddSubAux SubNLogN.Machine.K1.ShiftAux SubNLogN.Machine.Arith.CAddAux
  SubNLogN.Machine.CCore.LeafScalarAux

/-! ## The kernel on the `CAddAux.CK` layout -/

/-- Drop one token of the `v`-ruler (halving fields only). -/
def dropOne : Bool → AProg
  | true => cpd cR2
  | false => skip

/-- **The accumulate kernel on the `CAddAux.CK` layout.** The three rulers are built from the width
counter on `cW1`; the slots `cW2`, `cW3` of `CK` are not used. -/
def aMain (pre : Bool) (f : Bool → Bool → Bool → Bool × Bool) : AProg :=
  .seq setupC
  (.seq (liftC (buildU cW1 cC cM cR1)) (.seq (cpd cC)
  (.seq (liftC (buildU cW1 cC cM cR2)) (.seq (cpd cC) (.seq (dropOne pre)
  (.seq (liftC (buildU cW1 cC cM cR3)) (.seq (cpd cC)
  (.seq (cpkO cU)
  (.seq (recLoopA pre f)
  (.seq (liftCo (WP.W9comp.rewindTo cT cD .mark))
    cleanupC))))))))))

theorem closed_aMain (pre : Bool) (f : Bool → Bool → Bool → Bool × Bool) :
    (aMain pre f).Closed := by
  cases pre <;>
  simp [aMain, dropOne, recLoopA, recBodyA, fieldLoopA, fieldA, preB, setupC, cleanupC, fieldC,
    stepLoop, stepBody, readA, readB, dropTok, liftC, liftCo, cpkO, cpkP, cppO, cpd, cpc, setA,
    setB, pushF, setCF, clrC, buildU, uLoop, uBody, dropBits, dropLoop, liftX, pkO, pc, pd,
    Prog.Closed, Prog.FreeBelow, WP.W9comp.freeBelow_liftRegs, dec, copyBlock, moveBlock,
    moveBits, moveBitsDup, restoreR, WP.W9comp.rewindTo, pushC, popR, pushR, peekR, scanLoop,
    scanBody, decFix, skip, moveBitsBody, dupBody, WP.W9comp.rewindBody]

theorem dropOne_eval (pre : Bool) (w : ℕ) (hw : 1 ≤ w) (R : List Sym) (v : AReg)
    (S : CK → List Sym) (hR : S cR2 = toks w ++ R) :
    Eval [] (dropOne pre) ⟨v, S⟩ ⟨v, Function.update S cR2 (toks (wv pre w) ++ R)⟩ 1 := by
  cases pre with
  | false => exact (skip_eval [] ⟨v, S⟩).of_eq (st_eqC rfl (update_eq_of_eq hR).symm) rfl
  | true =>
    obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
    exact cpd_eval cR2 v S (Sym.bit true) (toks k ++ R) (by rw [hR]; rfl)

/-- The record loop's cost is linear in the volume of `u`. -/
theorem recCostA_le (w : ℕ) (hw : 1 ≤ w) :
    ∀ us : List (List CInt),
      (us.map fun cs => 2 * cs.length * (90 * w + 24) + 7).sum ≤ 114 * cvol w us
  | [] => by simp
  | cs :: us => by
    have ih := recCostA_le w hw us
    rw [List.map_cons, List.sum_cons, cvol_cons']
    have q1 : 2 * cs.length * (90 * w + 24) = 180 * (cs.length * w) + 48 * cs.length := by ring
    have q2 : 2 * cs.length * w = 2 * (cs.length * w) := by ring
    have hn : cs.length ≤ cs.length * w := Nat.le_mul_of_pos_right _ hw
    rw [q1, q2]
    generalize cs.length * w = P at *
    omega

/-- **The kernel on the `CAddAux.CK` layout.** -/
theorem aMain_eval (pre : Bool) (f : Bool → Bool → Bool → Bool × Bool) (g : ℤ → ℤ → ℤ)
    (hfg : ∀ w a b, ripOut f false (twosBits w a) (twosBits w b) = twosBits w (g a b))
    (h : CInt → CInt → CInt) (hh : ∀ a b, h a b = (g a.1 (hv pre b.1), g a.2 (hv pre b.2)))
    (w : ℕ) (hw : 1 ≤ w) (u v : List (List CInt)) (ru rv r3 : List Sym) (S : CK → List Sym)
    (hal : CAligned u v) (hfv : pre = true → CArrFits w v) (hru : BlkTerm ru) (hr3 : TermOK r3)
    (hU : S cU = carrSyms w u ++ ru) (hV : S cV = carrSyms w v ++ rv)
    (hW1 : S cW1 = natSyms w ++ r3) (o p : Option Sym) (la lb c : Bool) :
    ∃ (v' : AReg) (t : ℕ), t ≤ 300 * (cvol w u + cvol w v + w + 1) ∧
      Eval [] (aMain pre f) ⟨(o, p, la, lb, c), S⟩
        ⟨v', Function.update (Function.update (Function.update S cU ru) cV rv) cD
          (carrSyms w (zipC h u v) ++ S cD)⟩ t := by
  -- 1. guards
  have e1 := setupC_eval (o, p, la, lb, c) S
  set S1 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update S cT (Sym.mark :: S cT)) cR1 (Sym.mark :: S cR1))
    cR1' (Sym.mark :: S cR1')) cR2 (Sym.mark :: S cR2)) cR2' (Sym.mark :: S cR2'))
    cR3 (Sym.mark :: S cR3)) cR3' (Sym.mark :: S cR3') with hS1
  -- 2. ruler `R1`
  obtain ⟨t2, ht2, m2⟩ := buildU_eval (kW := cW1) (kC := cC) (kM := cM) (kU := cR1) (by decide)
    (by decide) (by decide) (by decide) w r3 hr3 o p la lb S1 (by simp [hS1, hW1])
  have e2 := Eval.liftRegs lensC m2 (o, p, la, lb, c) rfl
  have h1C : S1 cC = S cC := by simp [hS1]
  have h1R1 : S1 cR1 = Sym.mark :: S cR1 := by simp [hS1]
  rw [h1C, h1R1] at e2
  set S2 := Function.update (Function.update S1 cC (Sym.mark :: S cC)) cR1
    (toks w ++ Sym.mark :: S cR1) with hS2
  have e3 := cpd_eval cC (some Sym.mark, p, la, lb, c) S2 Sym.mark (S cC) (by simp [hS2])
  set S3 := Function.update S2 cC (S cC) with hS3
  -- 3. ruler `R2`
  obtain ⟨t4, ht4, m4⟩ := buildU_eval (kW := cW1) (kC := cC) (kM := cM) (kU := cR2) (by decide)
    (by decide) (by decide) (by decide) w r3 hr3 (some Sym.mark) p la lb S3
    (by simp [hS3, hS2, hS1, hW1])
  have e4 := Eval.liftRegs lensC m4 (some Sym.mark, p, la, lb, c) rfl
  have h3C : S3 cC = S cC := by simp [hS3]
  have h3R2 : S3 cR2 = Sym.mark :: S cR2 := by simp [hS3, hS2, hS1]
  rw [h3C, h3R2] at e4
  set S4 := Function.update (Function.update S3 cC (Sym.mark :: S cC)) cR2
    (toks w ++ Sym.mark :: S cR2) with hS4
  have e5 := cpd_eval cC (some Sym.mark, p, la, lb, c) S4 Sym.mark (S cC) (by simp [hS4])
  set S5 := Function.update S4 cC (S cC) with hS5
  -- 4. one token of `R2` less for the halving fields
  have e5' := dropOne_eval pre w hw (Sym.mark :: S cR2) (some Sym.mark, p, la, lb, c) S5
    (by simp [hS5, hS4])
  set S5' := Function.update S5 cR2 (toks (wv pre w) ++ Sym.mark :: S cR2) with hS5'
  -- 5. ruler `R3`
  obtain ⟨t6, ht6, m6⟩ := buildU_eval (kW := cW1) (kC := cC) (kM := cM) (kU := cR3) (by decide)
    (by decide) (by decide) (by decide) w r3 hr3 (some Sym.mark) p la lb S5'
    (by simp [hS5', hS5, hS4, hS3, hS2, hS1, hW1])
  have e6 := Eval.liftRegs lensC m6 (some Sym.mark, p, la, lb, c) rfl
  have h5C : S5' cC = S cC := by simp [hS5', hS5]
  have h5R3 : S5' cR3 = Sym.mark :: S cR3 := by simp [hS5', hS5, hS4, hS3, hS2, hS1]
  rw [h5C, h5R3] at e6
  set S6 := Function.update (Function.update S5' cC (Sym.mark :: S cC)) cR3
    (toks w ++ Sym.mark :: S cR3) with hS6
  have e7 := cpd_eval cC (some Sym.mark, p, la, lb, c) S6 Sym.mark (S cC) (by simp [hS6])
  set S7 := Function.update S6 cC (S cC) with hS7
  -- 6. peek the first operand
  have e8 := cpkO_eval cU (some Sym.mark, p, la, lb, c) S7
  -- 7. records
  obtain ⟨v9, t9, ht9, e9⟩ := recLoopA_eval pre f g hfg h hh w hw (S cR1) (S cR1')
    (S cR2) (S cR2') (S cR3) (S cR3') ru rv hru u v (S7 cU).head? p la lb c S7 hal hfv
    (by simp [hS7, hS6, hS5', hS5, hS4, hS3, hS2, hS1, hU])
    (by simp [hS7, hS6, hS5', hS5, hS4, hS3, hS2, hS1, hV])
    (by simp [hS7, hS6, hS5', hS5, hS4, hS3, hS2])
    (by simp [hS7, hS6, hS5', hS5, hS4, hS3, hS2, hS1])
    (by simp [hS7, hS6, hS5'])
    (by simp [hS7, hS6, hS5', hS5, hS4, hS3, hS2, hS1])
    (by simp [hS7, hS6])
    (by simp [hS7, hS6, hS5', hS5, hS4, hS3, hS2, hS1]) rfl
  have h7T : S7 cT = Sym.mark :: S cT := by simp [hS7, hS6, hS5', hS5, hS4, hS3, hS2, hS1]
  rw [h7T] at e9
  set out := carrSyms w (zipC h u v) with hout
  set S9 := Function.update (Function.update (Function.update S7 cU ru) cV rv) cT
    (out.reverse ++ Sym.mark :: S cT) with hS9
  -- 8. rewind the output buffer onto the destination
  have hmark : Sym.mark ∉ out.reverse := by
    rw [List.mem_reverse, hout, carrSyms]
    exact mark_not_mem_arrSyms _
  have e10 := Eval.liftRegs lensCo (WP.W9comp.rewindTo_eval (by decide : cT ≠ cD) Sym.mark
    (lensCo.get v9) out.reverse (S cT) S9 hmark (by simp [hS9])) v9 rfl
  have h9D : S9 cD = S cD := by simp [hS9, hS7, hS6, hS5', hS5, hS4, hS3, hS2, hS1]
  rw [h9D, List.reverse_reverse] at e10
  set S10 := Function.update (Function.update S9 cT (S cT)) cD (out ++ S cD) with hS10
  -- 9. cleanup
  obtain ⟨v11, e11⟩ := cleanupC_eval w (wv pre w) w (S cR1) (S cR1') (S cR2) (S cR2') (S cR3)
    (S cR3') (lensCo.set v9 (some Sym.mark)) S10
    (by simp [hS10, hS9, hS7, hS6, hS5', hS5, hS4, hS3, hS2])
    (by simp [hS10, hS9, hS7, hS6, hS5', hS5, hS4, hS3, hS2, hS1])
    (by simp [hS10, hS9, hS7, hS6, hS5'])
    (by simp [hS10, hS9, hS7, hS6, hS5', hS5, hS4, hS3, hS2, hS1])
    (by simp [hS10, hS9, hS7, hS6])
    (by simp [hS10, hS9, hS7, hS6, hS5', hS5, hS4, hS3, hS2, hS1])
  refine ⟨v11, _, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e5' (Eval.seq e6 (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 (Eval.seq e10
      e11))))))))))).of_eq (st_eqC rfl ?_) rfl⟩
  · have hc := recCostA_le w hw u
    have hb := bitLen_le_self w
    have hwv : wv pre w ≤ w := by cases pre <;> simp [wv]
    have hlo : out.reverse.length = cvol w u := by
      rw [List.length_reverse, hout, ← cvol, cvol_zipC w h u v hal]
    rw [hlo]
    omega
  · clear e1 e2 e3 e4 e5 e5' e6 e7 e8 e9 e10 e11 m2 m4 m6
    funext k
    rcases k with k | k <;> fin_cases k <;>
      simp [hS10, hS9, hS7, hS6, hS5', hS5, hS4, hS3, hS2, hS1]

/-! ## Coefficients -/

/-- Halving coefficient (`±1/2`): the first bit of `v` is read ahead. -/
def preOf : Coef → Bool
  | .pos => false
  | .neg => false
  | .halfPos => true
  | .halfNeg => true

/-- Bit function: the full adder (`+1`, `+1/2`) or the full subtractor (`-1`, `-1/2`). -/
def fOf : Coef → Bool → Bool → Bool → Bool × Bool
  | .pos => addBit
  | .neg => subBit
  | .halfPos => addBit
  | .halfNeg => subBit

/-- The integer operation of `fOf c`. -/
def gOf : Coef → ℤ → ℤ → ℤ
  | .pos => (· + ·)
  | .neg => (· - ·)
  | .halfPos => (· + ·)
  | .halfNeg => (· - ·)

theorem hfgOf (c : Coef) :
    ∀ w a b, ripOut (fOf c) false (twosBits w a) (twosBits w b) = twosBits w (gOf c a b) := by
  intro w a b
  cases c
  · exact ripOut_add w a b
  · exact ripOut_sub w a b
  · exact ripOut_add w a b
  · exact ripOut_sub w a b

theorem accC_eq (c : Coef) (a b : CInt) :
    accC c a b = (gOf c a.1 (hv (preOf c) b.1), gOf c a.2 (hv (preOf c) b.2)) := by
  cases c <;> simp [accC, coefInt, gOf, hv, preOf, sub_eq_add_neg]

/-! ## Embedding into the contract layout -/

/-- Private stacks of the kernel: two spare stacks (the unused width slots of `CK`) and nine scratch stacks. -/
abbrev AccE : Type := Fin 2 ⊕ Fin 9

/-- Embedding of `CAddAux.CK` inside the contract layout: `u, v, dst, w` to named stacks `0 … 3`,
width slots `4, 5` to the spare stacks, and `CK` scratch to the rest. -/
def ιA : CK → KLoc (Fin 4) AccE :=
  Sum.elim ![.inl 0, .inl 1, .inl 2, .inl 3, .inr (.inl 0), .inr (.inl 1)] fun j => .inr (.inr j)

theorem ιA_injective : Function.Injective ιA := by
  refine Function.Injective.sumElim ?_ (fun e e' h => by simpa using h) ?_
  · intro x y h
    fin_cases x <;> fin_cases y <;> simp_all
  · intro x e
    fin_cases x <;> simp

/-- The identity register lens. -/
def lensIdA : Lens AReg AReg where
  get v := v
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

end SubNLogN.Machine.CCore.LeafScalarAccAux

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith.CAddAux
  SubNLogN.Machine.CCore.LeafScalarAux SubNLogN.Machine.CCore.LeafScalarAccAux

/-- **The record-accumulate kernel of the scalar rows** (`AccStmt`, `CCore/LeafScalarDefs.lean`):
`dst += carrSyms w (zipC (accC c) u v)` for each `c ∈ {+1, -1, +1/2, -1/2}`, modulo `2^w`,
constant `C = 300`. Kernel `callInj ιA (aMain (preOf c) (fOf c))` (see the module docstring);
`KClean S` and `BlkTerm rv` are not used, `CArrFits w v` only for `c = ±1/2`. -/
theorem acc_holds : AccStmt := by
  refine ⟨300, fun c => ⟨AccE, inferInstance, inferInstance, AReg,
    callInj ιA lensIdA (aMain (preOf c) (fOf c)), inferInstance, inferInstance,
    closed_callInj ιA lensIdA (closed_aMain _ _), ?_⟩⟩
  intro w u v ru rv r3 S _ hw hal hfv hru _ hr3 hU hV hW
  refine runs_callInj ιA_injective lensIdA (Q := fun _ => True) ?_ ?_
  · apply Runs.of_eval
    rintro ⟨o, p, la, lb, cc⟩
    obtain ⟨v', t, ht, e⟩ := aMain_eval (preOf c) (fOf c) (gOf c) (hfgOf c) (accC c)
      (accC_eq c) w hw u v ru rv r3 (S ∘ ιA) hal (fun _ => hfv) hru hr3 hU hV hW o p la lb cc
    refine ⟨v', t, e.of_eq (st_eqC rfl ?_) rfl, trivial, ht⟩
    funext k
    rcases k with k | k
    · fin_cases k <;> simp [ιA]
    · simp [ιA]
  · intro k hk
    have h0 : k ≠ .inl 0 := fun h => hk cU (by rw [h]; rfl)
    have h1 : k ≠ .inl 1 := fun h => hk cV (by rw [h]; rfl)
    have h2 : k ≠ .inl 2 := fun h => hk cD (by rw [h]; rfl)
    rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]

end SubNLogN.Machine.CCore
