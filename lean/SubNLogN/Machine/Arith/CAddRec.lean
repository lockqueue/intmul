/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CAddProg
import SubNLogN.Machine.K1.Shift

/-!
# `SubNLogN.Machine.Arith.CAddRec`: the output steps of one field, on the kernel's stacks

**Scope (honest summary).** The concrete stack layout of the sum / difference kernels and the
evaluation lemma of the output-step loop (`stepLoop_eval`). Proved, no `sorry`. Helpers live in
`SubNLogN.Machine.Arith.CAddAux`.
-/

namespace SubNLogN.Machine.Arith.CAddAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1
  SubNLogN.Machine.K1.AddSubAux SubNLogN.Machine.K1.ShiftAux

/-! ## Layout -/

/-- Stacks: six named (`u`, `v`, destination, counters `w1`, `w2`, `w3`) and nine private. -/
abbrev CK : Type := KLoc (Fin 6) (Fin 9)

/-- Operand `u`. -/
abbrev cU : CK := .inl 0
/-- Operand `v`. -/
abbrev cV : CK := .inl 1
/-- Destination. -/
abbrev cD : CK := .inl 2
/-- Counter `w1`. -/
abbrev cW1 : CK := .inl 3
/-- Counter `w2`. -/
abbrev cW2 : CK := .inl 4
/-- Counter `w3`. -/
abbrev cW3 : CK := .inl 5
/-- Output buffer. -/
abbrev cT : CK := .inr 0
/-- Ruler `w1`. -/
abbrev cR1 : CK := .inr 1
/-- Used tokens of `R1`. -/
abbrev cR1' : CK := .inr 2
/-- Ruler `w2`. -/
abbrev cR2 : CK := .inr 3
/-- Used tokens of `R2`. -/
abbrev cR2' : CK := .inr 4
/-- Ruler `w3`. -/
abbrev cR3 : CK := .inr 5
/-- Used tokens of `R3`. -/
abbrev cR3' : CK := .inr 6
/-- Binary counter copy (ruler construction). -/
abbrev cC : CK := .inr 7
/-- Temporary (decrement, copy). -/
abbrev cM : CK := .inr 8

/-! ## Pure helpers -/

theorem padTo_succ_headD (n : ℕ) (la : Bool) (xa : List Bool) :
    padTo (n + 1) (lastOr la xa) xa =
      xa.headD la :: padTo n (lastOr (xa.headD la) xa.tail) xa.tail := by
  cases xa with
  | nil => simp [padTo, List.replicate_succ, lastOr_nil]
  | cons x xs =>
    simp only [padTo, List.take_succ_cons, List.length_cons, List.headD_cons, List.tail_cons,
      lastOr_cons, List.cons_append, Nat.add_sub_add_right]

theorem ctoks_append_toks (a b : ℕ) (L : List Sym) :
    toks a ++ (toks b ++ L) = toks (a + b) ++ L := by
  simp [toks, ← List.append_assoc, List.replicate_append_replicate]

theorem drop_tail' (xa : List Bool) (n : ℕ) : xa.tail.drop n = xa.drop (n + 1) := by
  cases xa <;> simp

/-! ## The output-step loop -/

theorem stepLoop_eval (f : Bool → Bool → Bool → Bool × Bool) (RU RV R10 R20 R30 : List Sym) :
    ∀ (n : ℕ) (xa xb : List Bool) (la lb c : Bool) (o : Option Sym) (S : CK → List Sym),
      S cU = xa.map Sym.bit ++ RU → S cV = xb.map Sym.bit ++ RV →
      S cR1 = toks xa.length ++ Sym.mark :: R10 → S cR2 = toks xb.length ++ Sym.mark :: R20 →
      S cR3 = toks n ++ Sym.mark :: R30 →
      ∃ (v' : CReg) (t : ℕ), t ≤ 20 * n + 1 ∧
        Eval [] (stepLoop cU cV cT cR1 cR1' cR2 cR2' cR3 cR3' f)
          ⟨(o, (S cR3).head?, la, lb, c), S⟩
          ⟨v', Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update (Function.update
            (Function.update S
              cU ((xa.drop n).map Sym.bit ++ RU)) cV ((xb.drop n).map Sym.bit ++ RV))
              cR1 (toks (xa.drop n).length ++ Sym.mark :: R10))
              cR1' (toks (xa.length - (xa.drop n).length) ++ S cR1'))
              cR2 (toks (xb.drop n).length ++ Sym.mark :: R20))
              cR2' (toks (xb.length - (xb.drop n).length) ++ S cR2'))
              cR3 (Sym.mark :: R30)) cR3' (toks n ++ S cR3'))
              cT ((ripOut f c (padTo n (lastOr la xa) xa)
                (padTo n (lastOr lb xb) xb)).reverse.map Sym.bit ++ S cT)⟩ t
  | 0, xa, xb, la, lb, c, o, S, hU, hV, hR1, hR2, hR3 => by
    have hR3' : S cR3 = Sym.mark :: R30 := hR3
    refine ⟨_, 1, le_refl _, (Eval.loop_false ?_).of_eq (st_eqC rfl ?_) rfl⟩
    · show pBitC (o, (S cR3).head?, la, lb, c) = false
      rw [hR3']
      rfl
    · funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [hU, hV, hR1, hR2, hR3', toks, padTo]
  | n + 1, xa, xb, la, lb, c, o, S, hU, hV, hR1, hR2, hR3 => by
    have hR3' : S cR3 = Sym.bit true :: (toks n ++ Sym.mark :: R30) := hR3
    obtain ⟨o1, t1, ht1, e1⟩ := readA_eval (kU := cU) (kR := cR1) (kR' := cR1') (by decide)
      (by decide) (by decide) xa RU R10 o (S cR3).head? la lb c S hU hR1
    set SA := Function.update (Function.update (Function.update S
      cU (xa.tail.map Sym.bit ++ RU)) cR1 (toks xa.tail.length ++ Sym.mark :: R10))
      cR1' (toks (xa.length - xa.tail.length) ++ S cR1') with hSA
    obtain ⟨o2, t2, ht2, e2⟩ := readB_eval (kV := cV) (kR := cR2) (kR' := cR2') (by decide)
      (by decide) (by decide) xb RV R20 o1 (S cR3).head? (xa.headD la) lb c SA
      (by simp [hSA, Function.update_apply, hV]) (by simp [hSA, Function.update_apply, hR2])
    have hSA2 : SA cR2' = S cR2' := by simp [hSA]
    rw [hSA2] at e2
    set SB := Function.update (Function.update (Function.update SA
      cV (xb.tail.map Sym.bit ++ RV)) cR2 (toks xb.tail.length ++ Sym.mark :: R20))
      cR2' (toks (xb.length - xb.tail.length) ++ S cR2') with hSB
    set la1 := xa.headD la with hla1
    set lb1 := xb.headD lb with hlb1
    have e3 := Eval.push [] cT (fun (v : CReg) => Sym.bit (f v.2.2.1 v.2.2.2.1 v.2.2.2.2).1)
      (o2, (S cR3).head?, la1, lb1, c) SB
    have hSBT : SB cT = S cT := by simp [hSB, hSA]
    rw [hSBT] at e3
    set SC := Function.update SB cT (Sym.bit (f la1 lb1 c).1 :: S cT) with hSC
    have e4 := Eval.load [] (fun (v : CReg) => (v.1, v.2.1, v.2.2.1, v.2.2.2.1,
      (f v.2.2.1 v.2.2.2.1 v.2.2.2.2).2)) (o2, (S cR3).head?, la1, lb1, c) SC
    have hSC3 : SC cR3 = Sym.bit true :: (toks n ++ Sym.mark :: R30) := by
      simp [hSC, hSB, hSA, Function.update_apply, hR3']
    have e5 := cpd_eval cR3 (o2, (S cR3).head?, la1, lb1, (f la1 lb1 c).2) SC _ _ hSC3
    set SD := Function.update SC cR3 (toks n ++ Sym.mark :: R30) with hSD
    have e6 := cpc_eval cR3' (Sym.bit true) (o2, (S cR3).head?, la1, lb1, (f la1 lb1 c).2) SD
    have hSD3' : SD cR3' = S cR3' := by simp [hSD, hSC, hSB, hSA]
    rw [hSD3'] at e6
    set SE := Function.update SD cR3' (Sym.bit true :: S cR3') with hSE
    have e7 := cpkP_eval cR3 (o2, (S cR3).head?, la1, lb1, (f la1 lb1 c).2) SE
    obtain ⟨v', t, ht, ih⟩ := stepLoop_eval f RU RV R10 R20 R30 n xa.tail xb.tail la1 lb1
      (f la1 lb1 c).2 o2 SE
      (by simp [hSE, hSD, hSC, hSB, hSA])
      (by simp [hSE, hSD, hSC, hSB, hSA])
      (by simp [hSE, hSD, hSC, hSB, hSA])
      (by simp [hSE, hSD, hSC, hSB, hSA])
      (by simp [hSE, hSD])
    have hE1' : SE cR1' = toks (xa.length - xa.tail.length) ++ S cR1' := by
      simp [hSE, hSD, hSC, hSB, hSA]
    have hE2' : SE cR2' = toks (xb.length - xb.tail.length) ++ S cR2' := by
      simp [hSE, hSD, hSC, hSB, hSA]
    have hE3' : SE cR3' = Sym.bit true :: S cR3' := by simp [hSE]
    have hET : SE cT = Sym.bit (f la1 lb1 c).1 :: S cT := by
      simp [hSE, hSD, hSC]
    rw [hE1', hE2', hE3', hET] at ih
    refine ⟨v', _, ?_, (Eval.loop_true ?_ (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
      (Eval.seq e5 (Eval.seq e6 e7)))))) ih).of_eq (st_eqC rfl ?_) rfl⟩
    · omega
    · show pBitC (o, (S cR3).head?, la, lb, c) = true
      rw [hR3']
      rfl
    · clear e1 e2 e3 e4 e5 e6 e7 ih
      have hpa := padTo_succ_headD n la xa
      have hpb := padTo_succ_headD n lb xb
      rw [← hla1] at hpa
      rw [← hlb1] at hpb
      have hdA := drop_tail' xa n
      have hdB := drop_tail' xb n
      funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [hSE, hSD, hSC, hSB, hSA, Function.update_apply, hpa, hpb, hdA, hdB, toks_succ',
          ctoks_append_toks, ripOut_cons, List.reverse_cons]
      all_goals (congr 1; omega)

/-! ## One field -/

/-- The sign-extended reading of a `w1`-bit field to `w3` bits. -/
theorem padTo_twosBits {w1 w3 : ℕ} {a : ℤ} (hw1 : 1 ≤ w1) (ha : FitsTwos w1 a) (la : Bool) :
    padTo w3 (lastOr la (twosBits w1 a)) (twosBits w1 a) = twosBits w3 a := by
  have hne : twosBits w1 a ≠ [] := by
    intro h
    have := length_twosBits w1 a
    rw [h] at this
    simp at this
    omega
  rw [lastOr_ne_nil la false hne, lastOr_twosBits hw1 ha]
  have h := shiftBits_left (w2 := w3) ha 0
  simpa using h

theorem fieldC_eval (f : Bool → Bool → Bool → Bool × Bool) (w1 w2 w3 : ℕ) (xa xb : List Bool)
    (hxa : xa.length = w1) (hxb : xb.length = w2)
    (RU RV R10 R1'0 R20 R2'0 R30 R3'0 : List Sym) (o p : Option Sym) (la lb c : Bool)
    (S : CK → List Sym)
    (hU : S cU = xa.map Sym.bit ++ RU) (hV : S cV = xb.map Sym.bit ++ RV)
    (hR1 : S cR1 = toks w1 ++ Sym.mark :: R10) (hR1' : S cR1' = Sym.mark :: R1'0)
    (hR2 : S cR2 = toks w2 ++ Sym.mark :: R20) (hR2' : S cR2' = Sym.mark :: R2'0)
    (hR3 : S cR3 = toks w3 ++ Sym.mark :: R30) (hR3' : S cR3' = Sym.mark :: R3'0) :
    ∃ (v' : CReg) (t : ℕ), t ≤ 30 * (w1 + w2 + w3) + 20 ∧
      Eval [] (fieldC cU cV cT cR1 cR1' cR2 cR2' cR3 cR3' f) ⟨(o, p, la, lb, c), S⟩
        ⟨v', Function.update (Function.update (Function.update S cU RU) cV RV) cT
          ((ripOut f false (padTo w3 (lastOr la xa) xa)
            (padTo w3 (lastOr lb xb) xb)).reverse.map Sym.bit ++ S cT)⟩ t := by
  have e1 := Eval.load [] (fun (v : CReg) => (v.1, v.2.1, v.2.2.1, v.2.2.2.1, false))
    (o, p, la, lb, c) S
  have e2 := cpkP_eval cR3 (o, p, la, lb, false) S
  obtain ⟨⟨o3, p3, la3, lb3, c3⟩, t3, ht3, e3⟩ := stepLoop_eval f RU RV R10 R20 R30 w3 xa xb la
    lb false o S hU hV (by rw [hR1, hxa]) (by rw [hR2, hxb]) hR3
  rw [hR1', hR2', hR3'] at e3
  set out := ripOut f false (padTo w3 (lastOr la xa) xa) (padTo w3 (lastOr lb xb) xb) with hout
  set S3 := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update S
      cU ((xa.drop w3).map Sym.bit ++ RU)) cV ((xb.drop w3).map Sym.bit ++ RV))
      cR1 (toks (xa.drop w3).length ++ Sym.mark :: R10))
      cR1' (toks (xa.length - (xa.drop w3).length) ++ Sym.mark :: R1'0))
      cR2 (toks (xb.drop w3).length ++ Sym.mark :: R20))
      cR2' (toks (xb.length - (xb.drop w3).length) ++ Sym.mark :: R2'0))
      cR3 (Sym.mark :: R30)) cR3' (toks w3 ++ Sym.mark :: R3'0))
      cT (out.reverse.map Sym.bit ++ S cT) with hS3
  have e4 := dropTok_eval (kX := cU) (kR := cR1) (kR' := cR1') (by decide) (by decide)
    (by decide) RU R10 (xa.drop w3) o3 p3 la3 lb3 c3 S3 (by simp [hS3]) (by simp [hS3])
  have hS3R1' : S3 cR1' = toks (xa.length - (xa.drop w3).length) ++ Sym.mark :: R1'0 := by
    simp [hS3]
  have hw1e : (xa.drop w3).length + (xa.length - (xa.drop w3).length) = w1 := by
    simp only [List.length_drop]
    omega
  rw [hS3R1', ctoks_append_toks, hw1e] at e4
  set S4 := Function.update (Function.update (Function.update S3 cU RU) cR1 (Sym.mark :: R10))
    cR1' (toks w1 ++ Sym.mark :: R1'0) with hS4
  have e5 := dropTok_eval (kX := cV) (kR := cR2) (kR' := cR2') (by decide) (by decide)
    (by decide) RV R20 (xb.drop w3) (some Sym.mark) p3 la3 lb3 c3 S4 (by simp [hS4, hS3])
    (by simp [hS4, hS3])
  have hS4R2' : S4 cR2' = toks (xb.length - (xb.drop w3).length) ++ Sym.mark :: R2'0 := by
    simp [hS4, hS3]
  have hw2e : (xb.drop w3).length + (xb.length - (xb.drop w3).length) = w2 := by
    simp only [List.length_drop]
    omega
  rw [hS4R2', ctoks_append_toks, hw2e] at e5
  set S5 := Function.update (Function.update (Function.update S4 cV RV) cR2 (Sym.mark :: R20))
    cR2' (toks w2 ++ Sym.mark :: R2'0) with hS5
  have m6 := moveBlock_eval (src := cR1') (dst := cR1) (by decide) []
    (lensCo.get (some Sym.mark, p3, la3, lb3, c3)) (List.replicate w1 true) (Sym.mark :: R1'0) S5
    (TermOK.cons rfl _) (by simp [hS5, hS4, toks_eq_map])
  have e6 := Eval.liftRegs lensCo m6 (some Sym.mark, p3, la3, lb3, c3) rfl
  have hS5R1 : S5 cR1 = Sym.mark :: R10 := by simp [hS5, hS4]
  rw [hS5R1] at e6
  set S6 := Function.update (Function.update S5 cR1' (Sym.mark :: R1'0)) cR1
    ((List.replicate w1 true).reverse.map Sym.bit ++ Sym.mark :: R10) with hS6
  have m7 := moveBlock_eval (src := cR2') (dst := cR2) (by decide) []
    (lensCo.get (some Sym.mark, p3, la3, lb3, c3)) (List.replicate w2 true) (Sym.mark :: R2'0) S6
    (TermOK.cons rfl _) (by simp [hS6, hS5, toks_eq_map])
  have e7 := Eval.liftRegs lensCo m7 (some Sym.mark, p3, la3, lb3, c3) rfl
  have hS6R2 : S6 cR2 = Sym.mark :: R20 := by simp [hS6, hS5]
  rw [hS6R2] at e7
  set S7 := Function.update (Function.update S6 cR2' (Sym.mark :: R2'0)) cR2
    ((List.replicate w2 true).reverse.map Sym.bit ++ Sym.mark :: R20) with hS7
  have m8 := moveBlock_eval (src := cR3') (dst := cR3) (by decide) []
    (lensCo.get (some Sym.mark, p3, la3, lb3, c3)) (List.replicate w3 true) (Sym.mark :: R3'0) S7
    (TermOK.cons rfl _) (by simp [hS7, hS6, hS5, hS4, hS3, toks_eq_map])
  have e8 := Eval.liftRegs lensCo m8 (some Sym.mark, p3, la3, lb3, c3) rfl
  have hS7R3 : S7 cR3 = Sym.mark :: R30 := by simp [hS7, hS6, hS5, hS4, hS3]
  rw [hS7R3] at e8
  refine ⟨_, _, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 (Eval.seq e7 e8))))))).of_eq (st_eqC rfl ?_) rfl⟩
  · simp only [List.length_drop, List.length_replicate]
    omega
  · clear e1 e2 e3 e4 e5 e6 e7 e8 m6 m7 m8
    funext k
    rcases k with k | k <;> fin_cases k <;>
      simp [hS7, hS6, hS5, hS4, hS3, hU, hV, hR1, hR1', hR2, hR2', hR3, hR3',
        List.reverse_replicate, toks, hxa, hxb]

end SubNLogN.Machine.Arith.CAddAux
