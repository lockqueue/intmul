/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.HalfSumStep

/-!
# `SubNLogN.Machine.Arith.HalfSumEmit`: halving toward zero, and one field of the butterfly

**Scope (honest summary).** Evaluation lemmas of the increment loop (`incLoop_eval`), of the
halving of a buffered field (`emitH_eval`: a buffer holding `s₀ :: rest` reversed yields
`hsIncOut (s₀ ∧ last) rest` on the output buffer), and of one whole field (`fieldH_eval`: the
output buffers receive `twosBits w (tdiv (a+b) 2)` and `twosBits w (tdiv (a-b) 2)`, reversed).
Proved, no `sorry`. Helpers live in `SubNLogN.Machine.Arith.HalfSumAux`.
-/

namespace SubNLogN.Machine.Arith.HalfSumAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1
  SubNLogN.Machine.K1.AddSubAux SubNLogN.Machine.K1.ShiftAux SubNLogN.Machine.Arith.CAddAux

theorem incLoop_eval {kT : HSK} (hT : kT ≠ hkA') (R0 : List Sym) :
    ∀ (xs : List Bool) (p : Option Sym) (la lb c c2 : Bool) (S : HSK → List Sym),
      S hkA' = xs.map Sym.bit ++ Sym.mark :: R0 →
      ∃ v' : HReg, Eval [] (incLoop kT) ⟨((S hkA').head?, p, la, lb, c, c2), S⟩
        ⟨v', Function.update (Function.update S hkA' (Sym.mark :: R0)) kT
          ((hsIncOut c xs).reverse.map Sym.bit ++ S kT)⟩ (5 * xs.length + 1)
  | [], p, la, lb, c, c2, S, hX => by
    have hX' : S hkA' = Sym.mark :: R0 := hX
    refine ⟨_, (Eval.loop_false ?_).of_eq (st_eqH rfl ?_) rfl⟩
    · show qoBit ((S hkA').head?, p, la, lb, c, c2) = false
      rw [hX']
      rfl
    · simp only [hsIncOut, List.reverse_nil, List.map_nil, List.nil_append]
      rw [update_eq_of_eq hX', Function.update_eq_self]
  | x :: xs, p, la, lb, c, c2, S, hX => by
    have hX' : S hkA' = Sym.bit x :: (xs.map Sym.bit ++ Sym.mark :: R0) := hX
    have e1 := qppO_eval hkA' ((S hkA').head?, p, la, lb, c, c2) S _ _ hX'
    set S1 := Function.update S hkA' (xs.map Sym.bit ++ Sym.mark :: R0) with hS1
    have e2 := Eval.push [] kT (fun (v : HReg) => Sym.bit (xor (optBit v.1) v.2.2.2.2.1))
      (some (Sym.bit x), p, la, lb, c, c2) S1
    have h1T : S1 kT = S kT := by rw [hS1, Function.update_of_ne hT]
    rw [h1T] at e2
    set S2 := Function.update S1 kT (Sym.bit (xor x c) :: S kT) with hS2
    have e3 := Eval.load [] (fun (v : HReg) => (v.1, v.2.1, v.2.2.1, v.2.2.2.1,
      optBit v.1 && v.2.2.2.2.1, v.2.2.2.2.2)) (some (Sym.bit x), p, la, lb, c, c2) S2
    have e4 := qpkO_eval hkA' (some (Sym.bit x), p, la, lb, x && c, c2) S2
    have h2X : S2 hkA' = xs.map Sym.bit ++ Sym.mark :: R0 := by
      rw [hS2, Function.update_of_ne hT.symm, hS1, Function.update_self]
    obtain ⟨v', ih⟩ := incLoop_eval hT R0 xs p la lb (x && c) c2 S2 h2X
    have h2T : S2 kT = Sym.bit (xor x c) :: S kT := Function.update_self _ _ _
    rw [h2T] at ih
    refine ⟨v', (Eval.loop_true ?_ (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) ih).of_eq
      (st_eqH rfl ?_) ?_⟩
    · show qoBit ((S hkA').head?, p, la, lb, c, c2) = true
      rw [hX']
      rfl
    · clear e1 e2 e3 e4 ih
      funext k
      simp only [hS2, hS1, Function.update_apply, hsIncOut, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- Halving a buffered field `s₀ :: rest` (stored reversed, its last bit on top) toward zero. -/
theorem emitH_eval {kX kT : HSK} (hXT : kX ≠ kT) (hXA : kX ≠ hkA') (hTA : kT ≠ hkA')
    (s0 : Bool) (rest : List Bool) (RX R0 : List Sym) (o p : Option Sym) (la lb c1 c2 : Bool)
    (S : HSK → List Sym)
    (hX : S kX = (s0 :: rest).reverse.map Sym.bit ++ Sym.mark :: RX)
    (hA' : S hkA' = Sym.mark :: R0) :
    ∃ v' : HReg, Eval [] (emitH kX kT) ⟨(o, p, la, lb, c1, c2), S⟩
      ⟨v', Function.update (Function.update S kX (Sym.mark :: RX)) kT
        ((hsIncOut (s0 && lastOr s0 rest) rest).reverse.map Sym.bit ++ S kT)⟩
      (8 * rest.length + 13) := by
  have e1 := qpkO_eval kX (o, p, la, lb, c1, c2) S
  rw [hX, head?_rev_map] at e1
  have e2 := Eval.load [] (fun (v : HReg) => (v.1, v.2.1, optBit v.1, v.2.2.2.1, v.2.2.2.2.1,
    v.2.2.2.2.2)) (some (Sym.bit (lastOr s0 rest)), p, la, lb, c1, c2) S
  have m3 := moveBlock_eval (src := kX) (dst := hkA') hXA [] (some (Sym.bit (lastOr s0 rest)))
    (s0 :: rest).reverse (Sym.mark :: RX) S (TermOK.cons rfl _) hX
  have e3 := Eval.liftRegs lensHo m3
    (some (Sym.bit (lastOr s0 rest)), p, lastOr s0 rest, lb, c1, c2) rfl
  rw [List.reverse_reverse, hA'] at e3
  set S3 := Function.update (Function.update S kX (Sym.mark :: RX)) hkA'
    ((s0 :: rest).map Sym.bit ++ Sym.mark :: R0) with hS3
  have e4 := qppO_eval hkA' (some Sym.mark, p, lastOr s0 rest, lb, c1, c2) S3 (Sym.bit s0)
    (rest.map Sym.bit ++ Sym.mark :: R0) (by simp [hS3])
  set S4 := Function.update S3 hkA' (rest.map Sym.bit ++ Sym.mark :: R0) with hS4
  have e5 := Eval.load [] (fun (v : HReg) => (v.1, v.2.1, v.2.2.1, v.2.2.2.1,
    optBit v.1 && v.2.2.1, v.2.2.2.2.2)) (some (Sym.bit s0), p, lastOr s0 rest, lb, c1, c2) S4
  have e6 := qpkO_eval hkA' (some (Sym.bit s0), p, lastOr s0 rest, lb, s0 && lastOr s0 rest, c2)
    S4
  have h4A : S4 hkA' = rest.map Sym.bit ++ Sym.mark :: R0 := Function.update_self _ _ _
  obtain ⟨v', e7⟩ := incLoop_eval hTA R0 rest p (lastOr s0 rest) lb (s0 && lastOr s0 rest) c2
    S4 h4A
  have h4T : S4 kT = S kT := by
    rw [hS4, Function.update_of_ne hTA, hS3, Function.update_of_ne hTA,
      Function.update_of_ne hXT.symm]
  rw [h4T] at e7
  refine ⟨v', (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 e7)))))).of_eq (st_eqH rfl ?_) ?_⟩
  · clear e1 e2 e3 e4 e5 e6 e7 m3
    funext k
    simp only [hS4, hS3, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [List.length_reverse, List.length_cons]
    omega

/-- One field: the output buffers receive the `w`-bit fields of `tdiv (a+b) 2` and
`tdiv (a-b) 2`, reversed; the operands' fields are consumed, all scratch is restored. -/
theorem fieldH_eval (w : ℕ) (hw : 1 ≤ w) (a b : ℤ) (ha : FitsTwos w a) (hb : FitsTwos w b)
    (RU RV R10 R1'0 R20 R2'0 R30 R3'0 RA RB RA' : List Sym) (o p : Option Sym)
    (la lb c1 c2 : Bool) (S : HSK → List Sym)
    (hU : S hkU = (twosBits w a).map Sym.bit ++ RU) (hV : S hkV = (twosBits w b).map Sym.bit ++ RV)
    (hR1 : S hkR1 = toks w ++ Sym.mark :: R10) (hR1' : S hkR1' = Sym.mark :: R1'0)
    (hR2 : S hkR2 = toks w ++ Sym.mark :: R20) (hR2' : S hkR2' = Sym.mark :: R2'0)
    (hR3 : S hkR3 = toks (w + 1) ++ Sym.mark :: R30) (hR3' : S hkR3' = Sym.mark :: R3'0)
    (hA : S hkA = Sym.mark :: RA) (hB : S hkB = Sym.mark :: RB)
    (hA' : S hkA' = Sym.mark :: RA') :
    ∃ (v' : HReg) (t : ℕ), t ≤ 50 * w + 80 ∧
      Eval [] fieldH ⟨(o, p, la, lb, c1, c2), S⟩
        ⟨v', Function.update (Function.update (Function.update (Function.update S hkU RU) hkV RV)
          hkTs ((twosBits w ((a + b).tdiv 2)).reverse.map Sym.bit ++ S hkTs))
          hkTd ((twosBits w ((a - b).tdiv 2)).reverse.map Sym.bit ++ S hkTd)⟩ t := by
  obtain ⟨⟨o1, p1, la1, lb1, c11, c21⟩, t1, ht1, e1⟩ := fieldS_eval w hw a b ha hb RU RV R10 R1'0
    R20 R2'0 R30 R3'0 o p la lb c1 c2 S hU hV hR1 hR1' hR2 hR2' hR3 hR3'
  rw [hA, hB, twosBits_succ w (a + b), twosBits_succ w (a - b)] at e1
  set S1 := Function.update (Function.update (Function.update (Function.update S hkU RU) hkV RV)
    hkA ((decide ((a + b) % 2 = 1) :: twosBits w ((a + b) / 2)).reverse.map Sym.bit ++
      Sym.mark :: RA))
    hkB ((decide ((a - b) % 2 = 1) :: twosBits w ((a - b) / 2)).reverse.map Sym.bit ++
      Sym.mark :: RB) with hS1
  obtain ⟨⟨o2, p2, la2, lb2, c12, c22⟩, e2⟩ := emitH_eval (kX := hkA) (kT := hkTs) (by decide)
    (by decide) (by decide) (decide ((a + b) % 2 = 1)) (twosBits w ((a + b) / 2)) RA RA' o1 p1
    la1 lb1 c11 c21 S1 (by simp [hS1]) (by simp [hS1, hA'])
  rw [half_bits (fitsTwos_add' hw ha hb), length_twosBits] at e2
  have h1Ts : S1 hkTs = S hkTs := by simp [hS1]
  rw [h1Ts] at e2
  set S2 := Function.update (Function.update S1 hkA (Sym.mark :: RA)) hkTs
    ((twosBits w ((a + b).tdiv 2)).reverse.map Sym.bit ++ S hkTs) with hS2
  obtain ⟨v3, e3⟩ := emitH_eval (kX := hkB) (kT := hkTd) (by decide) (by decide) (by decide)
    (decide ((a - b) % 2 = 1)) (twosBits w ((a - b) / 2)) RB RA' o2 p2 la2 lb2 c12 c22 S2
    (by simp [hS2, hS1]) (by simp [hS2, hS1, hA'])
  rw [half_bits (fitsTwos_sub' hw ha hb), length_twosBits] at e3
  have h2Td : S2 hkTd = S hkTd := by simp [hS2, hS1]
  rw [h2Td] at e3
  refine ⟨v3, _, ?_, (Eval.seq e1 (Eval.seq e2 e3)).of_eq (st_eqH rfl ?_) rfl⟩
  · omega
  · clear e1 e2 e3
    funext k
    rcases k with k | k <;> fin_cases k <;> simp [hS2, hS1, hA, hB]

end SubNLogN.Machine.Arith.HalfSumAux
