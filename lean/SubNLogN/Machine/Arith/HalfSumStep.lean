/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.HalfSumProg

/-!
# `SubNLogN.Machine.Arith.HalfSumStep`: the ripple part of one field of the butterfly kernel

**Scope (honest summary).** Evaluation lemmas of the ripple loop (`stepLoopH_eval`: after `n`
steps, `A` holds the reversed sum bits `ripOut addBit` and `B` the reversed difference bits
`ripOut subBit` of the sign-extended operands) and of the ripple part of one field
(`fieldS_eval`: `A` holds `twosBits (w+1) (a+b)` reversed, `B` holds `twosBits (w+1) (a-b)`
reversed, the rulers are restored). Proved, no `sorry`. Helpers live in
`SubNLogN.Machine.Arith.HalfSumAux`.
-/

namespace SubNLogN.Machine.Arith.HalfSumAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1
  SubNLogN.Machine.K1.AddSubAux SubNLogN.Machine.K1.ShiftAux SubNLogN.Machine.Arith.CAddAux

theorem stepLoopH_eval (RU RV R10 R20 R30 : List Sym) :
    ∀ (n : ℕ) (xa xb : List Bool) (la lb c1 c2 : Bool) (o : Option Sym) (S : HSK → List Sym),
      S hkU = xa.map Sym.bit ++ RU → S hkV = xb.map Sym.bit ++ RV →
      S hkR1 = toks xa.length ++ Sym.mark :: R10 → S hkR2 = toks xb.length ++ Sym.mark :: R20 →
      S hkR3 = toks n ++ Sym.mark :: R30 →
      ∃ (v' : HReg) (t : ℕ), t ≤ 20 * n + 1 ∧
        Eval [] stepLoopH ⟨(o, (S hkR3).head?, la, lb, c1, c2), S⟩
          ⟨v', Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update S
              hkU ((xa.drop n).map Sym.bit ++ RU)) hkV ((xb.drop n).map Sym.bit ++ RV))
              hkR1 (toks (xa.drop n).length ++ Sym.mark :: R10))
              hkR1' (toks (xa.length - (xa.drop n).length) ++ S hkR1'))
              hkR2 (toks (xb.drop n).length ++ Sym.mark :: R20))
              hkR2' (toks (xb.length - (xb.drop n).length) ++ S hkR2'))
              hkR3 (Sym.mark :: R30)) hkR3' (toks n ++ S hkR3'))
              hkA ((ripOut addBit c1 (padTo n (lastOr la xa) xa)
                (padTo n (lastOr lb xb) xb)).reverse.map Sym.bit ++ S hkA))
              hkB ((ripOut subBit c2 (padTo n (lastOr la xa) xa)
                (padTo n (lastOr lb xb) xb)).reverse.map Sym.bit ++ S hkB)⟩ t
  | 0, xa, xb, la, lb, c1, c2, o, S, hU, hV, hR1, hR2, hR3 => by
    have hR3' : S hkR3 = Sym.mark :: R30 := hR3
    refine ⟨_, 1, le_refl _, (Eval.loop_false ?_).of_eq (st_eqH rfl ?_) rfl⟩
    · show qpBit (o, (S hkR3).head?, la, lb, c1, c2) = false
      rw [hR3']
      rfl
    · funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [hU, hV, hR1, hR2, hR3', toks, padTo]
  | n + 1, xa, xb, la, lb, c1, c2, o, S, hU, hV, hR1, hR2, hR3 => by
    have hR3' : S hkR3 = Sym.bit true :: (toks n ++ Sym.mark :: R30) := hR3
    obtain ⟨o1, t1, ht1, e1c⟩ := readA_eval (kU := hkU) (kR := hkR1) (kR' := hkR1') (by decide)
      (by decide) (by decide) xa RU R10 o (S hkR3).head? la lb c1 S hU hR1
    have e1 := Eval.liftRegs lensHC e1c (o, (S hkR3).head?, la, lb, c1, c2) rfl
    set SA := Function.update (Function.update (Function.update S
      hkU (xa.tail.map Sym.bit ++ RU)) hkR1 (toks xa.tail.length ++ Sym.mark :: R10))
      hkR1' (toks (xa.length - xa.tail.length) ++ S hkR1') with hSA
    obtain ⟨o2, t2, ht2, e2c⟩ := readB_eval (kV := hkV) (kR := hkR2) (kR' := hkR2') (by decide)
      (by decide) (by decide) xb RV R20 o1 (S hkR3).head? (xa.headD la) lb c1 SA
      (by simp [hSA, hV]) (by simp [hSA, hR2])
    have e2 := Eval.liftRegs lensHC e2c (o1, (S hkR3).head?, xa.headD la, lb, c1, c2) rfl
    have hSA2 : SA hkR2' = S hkR2' := by simp [hSA]
    rw [hSA2] at e2
    set SB := Function.update (Function.update (Function.update SA
      hkV (xb.tail.map Sym.bit ++ RV)) hkR2 (toks xb.tail.length ++ Sym.mark :: R20))
      hkR2' (toks (xb.length - xb.tail.length) ++ S hkR2') with hSB
    set la1 := xa.headD la with hla1
    set lb1 := xb.headD lb with hlb1
    have e3 := Eval.push [] hkA
      (fun (v : HReg) => Sym.bit (addBit v.2.2.1 v.2.2.2.1 v.2.2.2.2.1).1)
      (o2, (S hkR3).head?, la1, lb1, c1, c2) SB
    have hSBA : SB hkA = S hkA := by simp [hSB, hSA]
    rw [hSBA] at e3
    set SC := Function.update SB hkA (Sym.bit (addBit la1 lb1 c1).1 :: S hkA) with hSC
    have e4 := Eval.load [] (fun (v : HReg) => (v.1, v.2.1, v.2.2.1, v.2.2.2.1,
      (addBit v.2.2.1 v.2.2.2.1 v.2.2.2.2.1).2, v.2.2.2.2.2))
      (o2, (S hkR3).head?, la1, lb1, c1, c2) SC
    have e5 := Eval.push [] hkB
      (fun (v : HReg) => Sym.bit (subBit v.2.2.1 v.2.2.2.1 v.2.2.2.2.2).1)
      (o2, (S hkR3).head?, la1, lb1, (addBit la1 lb1 c1).2, c2) SC
    have hSCB : SC hkB = S hkB := by simp [hSC, hSB, hSA]
    rw [hSCB] at e5
    set SD := Function.update SC hkB (Sym.bit (subBit la1 lb1 c2).1 :: S hkB) with hSD
    have e6 := Eval.load [] (fun (v : HReg) => (v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1,
      (subBit v.2.2.1 v.2.2.2.1 v.2.2.2.2.2).2))
      (o2, (S hkR3).head?, la1, lb1, (addBit la1 lb1 c1).2, c2) SD
    have hSD3 : SD hkR3 = Sym.bit true :: (toks n ++ Sym.mark :: R30) := by
      simp [hSD, hSC, hSB, hSA, hR3']
    have e7 := qpd_eval hkR3
      (o2, (S hkR3).head?, la1, lb1, (addBit la1 lb1 c1).2, (subBit la1 lb1 c2).2) SD _ _ hSD3
    set SE := Function.update SD hkR3 (toks n ++ Sym.mark :: R30) with hSE
    have e8 := qpc_eval hkR3' (Sym.bit true)
      (o2, (S hkR3).head?, la1, lb1, (addBit la1 lb1 c1).2, (subBit la1 lb1 c2).2) SE
    have hSE3' : SE hkR3' = S hkR3' := by simp [hSE, hSD, hSC, hSB, hSA]
    rw [hSE3'] at e8
    set SF := Function.update SE hkR3' (Sym.bit true :: S hkR3') with hSF
    have e9 := qpkP_eval hkR3
      (o2, (S hkR3).head?, la1, lb1, (addBit la1 lb1 c1).2, (subBit la1 lb1 c2).2) SF
    obtain ⟨v', t, ht, ih⟩ := stepLoopH_eval RU RV R10 R20 R30 n xa.tail xb.tail la1 lb1
      (addBit la1 lb1 c1).2 (subBit la1 lb1 c2).2 o2 SF
      (by simp [hSF, hSE, hSD, hSC, hSB, hSA])
      (by simp [hSF, hSE, hSD, hSC, hSB, hSA])
      (by simp [hSF, hSE, hSD, hSC, hSB, hSA])
      (by simp [hSF, hSE, hSD, hSC, hSB, hSA])
      (by simp [hSF, hSE])
    have hF1' : SF hkR1' = toks (xa.length - xa.tail.length) ++ S hkR1' := by
      simp [hSF, hSE, hSD, hSC, hSB, hSA]
    have hF2' : SF hkR2' = toks (xb.length - xb.tail.length) ++ S hkR2' := by
      simp [hSF, hSE, hSD, hSC, hSB, hSA]
    have hF3' : SF hkR3' = Sym.bit true :: S hkR3' := by simp [hSF]
    have hFA : SF hkA = Sym.bit (addBit la1 lb1 c1).1 :: S hkA := by
      simp [hSF, hSE, hSD, hSC]
    have hFB : SF hkB = Sym.bit (subBit la1 lb1 c2).1 :: S hkB := by
      simp [hSF, hSE, hSD]
    rw [hF1', hF2', hF3', hFA, hFB] at ih
    refine ⟨v', _, ?_, (Eval.loop_true ?_ (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4
      (Eval.seq e5 (Eval.seq e6 (Eval.seq e7 (Eval.seq e8 e9)))))))) ih).of_eq
      (st_eqH rfl ?_) rfl⟩
    · omega
    · show qpBit (o, (S hkR3).head?, la, lb, c1, c2) = true
      rw [hR3']
      rfl
    · clear e1 e2 e3 e4 e5 e6 e7 e8 e9 ih e1c e2c
      have hpa := padTo_succ_headD n la xa
      have hpb := padTo_succ_headD n lb xb
      rw [← hla1] at hpa
      rw [← hlb1] at hpb
      have hdA := drop_tail' xa n
      have hdB := drop_tail' xb n
      funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [hSF, hSE, hSD, hSC, hSB, hSA, hpa, hpb, hdA, hdB, toks_succ',
          ctoks_append_toks, ripOut_cons, List.reverse_cons]
      all_goals (congr 1; omega)

/-- The ripple part of one field: `A`, `B` receive the reversed `(w+1)`-bit fields of `a + b`
and `a - b`; the rulers are restored. -/
theorem fieldS_eval (w : ℕ) (hw : 1 ≤ w) (a b : ℤ) (ha : FitsTwos w a) (hb : FitsTwos w b)
    (RU RV R10 R1'0 R20 R2'0 R30 R3'0 : List Sym) (o p : Option Sym) (la lb c1 c2 : Bool)
    (S : HSK → List Sym)
    (hU : S hkU = (twosBits w a).map Sym.bit ++ RU) (hV : S hkV = (twosBits w b).map Sym.bit ++ RV)
    (hR1 : S hkR1 = toks w ++ Sym.mark :: R10) (hR1' : S hkR1' = Sym.mark :: R1'0)
    (hR2 : S hkR2 = toks w ++ Sym.mark :: R20) (hR2' : S hkR2' = Sym.mark :: R2'0)
    (hR3 : S hkR3 = toks (w + 1) ++ Sym.mark :: R30) (hR3' : S hkR3' = Sym.mark :: R3'0) :
    ∃ (v' : HReg) (t : ℕ), t ≤ 30 * w + 40 ∧
      Eval [] fieldS ⟨(o, p, la, lb, c1, c2), S⟩
        ⟨v', Function.update (Function.update (Function.update (Function.update S hkU RU) hkV RV)
          hkA ((twosBits (w + 1) (a + b)).reverse.map Sym.bit ++ S hkA))
          hkB ((twosBits (w + 1) (a - b)).reverse.map Sym.bit ++ S hkB)⟩ t := by
  have e1 := Eval.load [] (fun (v : HReg) => (v.1, v.2.1, v.2.2.1, v.2.2.2.1, false, false))
    (o, p, la, lb, c1, c2) S
  have e2 := qpkP_eval hkR3 (o, p, la, lb, false, false) S
  obtain ⟨⟨o3, p3, la3, lb3, c13, c23⟩, t3, ht3, e3⟩ := stepLoopH_eval RU RV R10 R20 R30 (w + 1)
    (twosBits w a) (twosBits w b) la lb false false o S hU hV (by rw [hR1, length_twosBits])
    (by rw [hR2, length_twosBits]) hR3
  have hda : (twosBits w a).drop (w + 1) = [] :=
    List.drop_of_length_le (by rw [length_twosBits]; omega)
  have hdb : (twosBits w b).drop (w + 1) = [] :=
    List.drop_of_length_le (by rw [length_twosBits]; omega)
  have ht0 : toks 0 = [] := rfl
  rw [hR1', hR2', hR3', padTo_twosBits hw ha, padTo_twosBits hw hb, ripOut_add, ripOut_sub, hda,
    hdb] at e3
  simp only [List.map_nil, List.nil_append, List.length_nil, Nat.sub_zero, length_twosBits,
    ht0] at e3
  set S3 := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update S
      hkU RU) hkV RV)
      hkR1 (Sym.mark :: R10))
      hkR1' (toks w ++ Sym.mark :: R1'0))
      hkR2 (Sym.mark :: R20))
      hkR2' (toks w ++ Sym.mark :: R2'0))
      hkR3 (Sym.mark :: R30)) hkR3' (toks (w + 1) ++ Sym.mark :: R3'0))
      hkA ((twosBits (w + 1) (a + b)).reverse.map Sym.bit ++ S hkA))
      hkB ((twosBits (w + 1) (a - b)).reverse.map Sym.bit ++ S hkB) with hS3
  have m4 := moveBlock_eval (src := hkR1') (dst := hkR1) (by decide) []
    (lensHo.get (o3, p3, la3, lb3, c13, c23)) (List.replicate w true) (Sym.mark :: R1'0) S3
    (TermOK.cons rfl _) (by simp [hS3, toks_eq_map])
  have e4 := Eval.liftRegs lensHo m4 (o3, p3, la3, lb3, c13, c23) rfl
  have hS3R1 : S3 hkR1 = Sym.mark :: R10 := by simp [hS3]
  rw [hS3R1] at e4
  set S4 := Function.update (Function.update S3 hkR1' (Sym.mark :: R1'0)) hkR1
    ((List.replicate w true).reverse.map Sym.bit ++ Sym.mark :: R10) with hS4
  have m5 := moveBlock_eval (src := hkR2') (dst := hkR2) (by decide) []
    (lensHo.get (some Sym.mark, p3, la3, lb3, c13, c23)) (List.replicate w true)
    (Sym.mark :: R2'0) S4 (TermOK.cons rfl _) (by simp [hS4, hS3, toks_eq_map])
  have e5 := Eval.liftRegs lensHo m5 (some Sym.mark, p3, la3, lb3, c13, c23) rfl
  have hS4R2 : S4 hkR2 = Sym.mark :: R20 := by simp [hS4, hS3]
  rw [hS4R2] at e5
  set S5 := Function.update (Function.update S4 hkR2' (Sym.mark :: R2'0)) hkR2
    ((List.replicate w true).reverse.map Sym.bit ++ Sym.mark :: R20) with hS5
  have m6 := moveBlock_eval (src := hkR3') (dst := hkR3) (by decide) []
    (lensHo.get (some Sym.mark, p3, la3, lb3, c13, c23)) (List.replicate (w + 1) true)
    (Sym.mark :: R3'0) S5 (TermOK.cons rfl _) (by simp [hS5, hS4, hS3, toks_eq_map])
  have e6 := Eval.liftRegs lensHo m6 (some Sym.mark, p3, la3, lb3, c13, c23) rfl
  have hS5R3 : S5 hkR3 = Sym.mark :: R30 := by simp [hS5, hS4, hS3]
  rw [hS5R3] at e6
  refine ⟨_, _, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    e6))))).of_eq (st_eqH rfl ?_) rfl⟩
  · simp only [List.length_replicate]
    omega
  · clear e1 e2 e3 e4 e5 e6 m4 m5 m6
    funext k
    rcases k with k | k <;> fin_cases k <;>
      simp [hS5, hS4, hS3, hR1, hR1', hR2, hR2', hR3, hR3', List.reverse_replicate, toks]

end SubNLogN.Machine.Arith.HalfSumAux
