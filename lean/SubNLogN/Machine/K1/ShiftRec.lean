/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.ShiftProg

/-!
# `SubNLogN.Machine.K1.ShiftRec`: one record and the record loop of the shift kernel

Paper: Lemma A.4(5) (`lem:transfer-streams`), Appendix A.1 (`sec:transfer-premises`).

**Scope (honest summary).** Proved evaluation lemmas (no `sorry`):
* `recTailX_eval`: phases C, E, X, the record end and the counter restores.
* `recBodyX_eval`: one record, for both signs of the exponent; its output is `outRec ng w2 d xs`
  (`d` leading zeros or `d` dropped bits, then padding with the sign or truncation to `w2`).
* `recLoopX_eval`: all records; output `arrSyms (xss.map (outRec ng w2 d))`, cost at most
  `M·(25·(w1 + w2 + 1) + 1) + 1`.
-/

namespace SubNLogN.Machine.K1.ShiftAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1 SubNLogN.Machine.K1.AddSubAux

/-- Output bits of one record: for `t < 0` drop `d` bits, for `t ≥ 0` prepend `d` zeros; then
pad with the sign (the last input bit) or truncate, to `w2` bits. -/
def outRec (ng : Bool) (w2 d : ℕ) (xs : List Bool) : List Bool :=
  if ng then padTo w2 (lastOr false xs) (xs.drop d)
  else padTo w2 (lastOr false xs) (List.replicate d false ++ xs)

theorem toks_append_toks (a b : ℕ) (L : List Sym) : toks a ++ (toks b ++ L) = toks (a + b) ++ L := by
  simp [toks, ← List.append_assoc, List.replicate_append_replicate]

theorem lastOr_ne_nil (b b' : Bool) : ∀ {l : List Bool}, l ≠ [] → lastOr b l = lastOr b' l
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

theorem take_min_eq (n : ℕ) (l : List Bool) : l.take (min n l.length) = l.take n := by
  by_cases h : n ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (show l.length ≤ n by omega), List.take_length,
      List.take_of_length_le (show l.length ≤ n by omega)]

/-- The output of phase Z + tail is the padded record (`t ≥ 0`). -/
theorem out_pos_eq (w2 d : ℕ) (xs : List Bool) (lb : Bool) (hxs : xs ≠ []) (hd : d ≤ w2) :
    List.replicate d false ++ (xs.take (min (w2 - d) xs.length) ++
      List.replicate (w2 - d - min (w2 - d) xs.length)
        (lastOr lb (xs.take (min (w2 - d) xs.length)))) =
    padTo w2 (lastOr false xs) (List.replicate d false ++ xs) := by
  unfold padTo
  rw [List.take_append, List.take_of_length_le
      (show (List.replicate d false).length ≤ w2 by simp; omega), List.length_replicate,
    List.length_append, List.length_replicate, List.append_assoc]
  by_cases h : w2 - d ≤ xs.length
  · rw [Nat.min_eq_left h, show w2 - d - (w2 - d) = 0 by omega,
      show w2 - (d + xs.length) = 0 by omega]
    simp
  · rw [Nat.min_eq_right (show xs.length ≤ w2 - d by omega), List.take_length,
      List.take_of_length_le (show xs.length ≤ w2 - d by omega),
      show w2 - d - xs.length = w2 - (d + xs.length) by omega, lastOr_ne_nil lb false hxs]

/-- The output of phase S + tail is the padded record (`t < 0`). -/
theorem out_neg_eq (w2 d : ℕ) (xs : List Bool) (lb : Bool) (hxs : xs ≠ []) :
    (xs.drop d).take (min w2 (xs.drop d).length) ++
      List.replicate (w2 - min w2 (xs.drop d).length)
        (lastOr (lastOr lb (xs.take d)) ((xs.drop d).take (min w2 (xs.drop d).length))) =
    padTo w2 (lastOr false xs) (xs.drop d) := by
  unfold padTo
  by_cases h : w2 ≤ (xs.drop d).length
  · rw [Nat.min_eq_left h, show w2 - w2 = 0 by omega,
      show w2 - (xs.drop d).length = 0 by omega]
    simp
  · rw [Nat.min_eq_right (show (xs.drop d).length ≤ w2 by omega), List.take_length,
      List.take_of_length_le (show (xs.drop d).length ≤ w2 by omega), ← lastOr_append,
      List.take_append_drop, lastOr_ne_nil lb false hxs]

section Rec

variable {K : Type} [DecidableEq K] {kX kT kU kU' kD kD' : K}

theorem recTailX_eval (hXT : kX ≠ kT) (hXU : kX ≠ kU) (hXU' : kX ≠ kU') (hXD : kX ≠ kD)
    (hXD' : kX ≠ kD') (hTU : kT ≠ kU) (hTU' : kT ≠ kU') (hTD : kT ≠ kD) (hTD' : kT ≠ kD')
    (hUU' : kU ≠ kU') (hUD : kU ≠ kD) (hUD' : kU ≠ kD') (hU'D : kU' ≠ kD) (hU'D' : kU' ≠ kD')
    (hDD' : kD ≠ kD')
    (ys : List Bool) (u n d : ℕ) (o p : Option Sym) (lb ng : Bool)
    (R U0 U'0 D0 D'0 : List Sym) (S : K → List Sym)
    (hX : S kX = ys.map Sym.bit ++ Sym.sep :: R) (hU : S kU = toks u ++ Sym.mark :: U0)
    (hU' : S kU' = toks n ++ Sym.mark :: U'0) (hD : S kD = Sym.mark :: D0)
    (hD' : S kD' = toks d ++ Sym.mark :: D'0) :
    ∃ p', Eval [] (recTailX kX kT kU kU' kD kD') ⟨(o, p, lb, ng), S⟩
      ⟨(R.head?, p', lastOr lb (ys.take (min u ys.length)), ng),
        Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update S kX R)
          kT (Sym.sep :: (List.replicate (u - min u ys.length)
            (Sym.bit (lastOr lb (ys.take (min u ys.length)))) ++
            ((ys.take (min u ys.length)).reverse.map Sym.bit ++ S kT))))
          kU (toks (n + u) ++ Sym.mark :: U0)) kU' (Sym.mark :: U'0))
          kD (toks d ++ Sym.mark :: D0)) kD' (Sym.mark :: D'0)⟩
      (8 * min u ys.length + 5 * (u - min u ys.length) + 3 * (ys.length - min u ys.length) +
        3 * (n + u) + 3 * d + 18) := by
  set c := min u ys.length with hc
  set lbE := lastOr lb (ys.take c) with hlbE
  have hcu : c ≤ u := by omega
  have hcy : c ≤ ys.length := by omega
  have e1 := pkO_eval kU (o, p, lb, ng) S
  have e2 := pkP_eval kX ((S kU).head?, p, lb, ng) S
  have e3 := cLoop_eval hXT hXU hXU' hTU hTU' hUU' ys u lb ng U0 R S hU hX
  rw [← hc, ← hlbE] at e3
  set S3 := Function.update (Function.update (Function.update (Function.update S
      kX ((ys.drop c).map Sym.bit ++ Sym.sep :: R))
      kT ((ys.take c).reverse.map Sym.bit ++ S kT))
      kU (toks (u - c) ++ Sym.mark :: U0))
      kU' (toks c ++ S kU') with hS3
  set p3 := ((ys.drop c).map Sym.bit ++ Sym.sep :: R).head? with hp3
  have e4 := pkO_eval kU ((toks (u - c) ++ Sym.mark :: U0).head?, p3, lbE, ng) S3
  have h3U : S3 kU = toks (u - c) ++ Sym.mark :: U0 := by
    rw [hS3, Function.update_of_ne hUU', Function.update_self]
  have h3T : S3 kT = (ys.take c).reverse.map Sym.bit ++ S kT := by
    rw [hS3, Function.update_of_ne hTU', Function.update_of_ne hTU, Function.update_self]
  have h3U' : S3 kU' = toks c ++ S kU' := by
    rw [hS3, Function.update_self]
  have e5 := eLoop_eval hTU hTU' hUU' (u - c) p3 lbE ng U0 S3 h3U
  rw [h3T, h3U'] at e5
  set S5 := Function.update (Function.update (Function.update S3
      kT (List.replicate (u - c) (Sym.bit lbE) ++ ((ys.take c).reverse.map Sym.bit ++ S kT)))
      kU (Sym.mark :: U0)) kU' (toks (u - c) ++ (toks c ++ S kU')) with hS5
  have h5X : S5 kX = (ys.drop c).map Sym.bit ++ Sym.sep :: R := by
    rw [hS5, Function.update_of_ne hXU', Function.update_of_ne hXU, Function.update_of_ne hXT,
      hS3, Function.update_of_ne hXU', Function.update_of_ne hXU, Function.update_of_ne hXT,
      Function.update_self]
  have e6 := dropBits_eval kX (ys.drop c) (Sym.sep :: R) (some Sym.mark) p3 lbE ng S5
    (TermOK.cons rfl _) h5X
  set S6 := Function.update S5 kX (Sym.sep :: R) with hS6
  have e7 := pd_eval kX ((Sym.sep :: R).head?, p3, lbE, ng) S6 Sym.sep R
    (Function.update_self _ _ _)
  set S7 := Function.update S6 kX R with hS7
  have e8 := pc_eval kT Sym.sep ((Sym.sep :: R).head?, p3, lbE, ng) S7
  have h7T : S7 kT = List.replicate (u - c) (Sym.bit lbE) ++
      ((ys.take c).reverse.map Sym.bit ++ S kT) := by
    rw [hS7, Function.update_of_ne hXT.symm, hS6, Function.update_of_ne hXT.symm, hS5,
      Function.update_of_ne hTU', Function.update_of_ne hTU, Function.update_self]
  rw [h7T] at e8
  set S8 := Function.update S7 kT (Sym.sep :: (List.replicate (u - c) (Sym.bit lbE) ++
      ((ys.take c).reverse.map Sym.bit ++ S kT))) with hS8
  have h8U' : S8 kU' = (List.replicate (n + u) true).map Sym.bit ++ Sym.mark :: U'0 := by
    rw [hS8, Function.update_of_ne hTU'.symm, hS7, Function.update_of_ne hXU'.symm, hS6,
      Function.update_of_ne hXU'.symm, hS5, Function.update_self, hU',
      toks_append_toks, toks_append_toks, ← toks_eq_map, show u - c + c + n = n + u by omega]
  have h8U : S8 kU = Sym.mark :: U0 := by
    rw [hS8, Function.update_of_ne hTU.symm, hS7, Function.update_of_ne hXU.symm, hS6,
      Function.update_of_ne hXU.symm, hS5, Function.update_of_ne hUU', Function.update_self]
  have e9 := Eval.liftRegs lensX (moveBlock_eval hUU'.symm [] (lensX.get ((Sym.sep :: R).head?,
    p3, lbE, ng)) (List.replicate (n + u) true) (Sym.mark :: U'0) S8 (TermOK.cons rfl _) h8U')
    ((Sym.sep :: R).head?, p3, lbE, ng) rfl
  rw [h8U] at e9
  set S9 := Function.update (Function.update S8 kU' (Sym.mark :: U'0)) kU
    ((List.replicate (n + u) true).reverse.map Sym.bit ++ Sym.mark :: U0) with hS9
  have h9D' : S9 kD' = (List.replicate d true).map Sym.bit ++ Sym.mark :: D'0 := by
    rw [hS9, Function.update_of_ne hUD'.symm, Function.update_of_ne hU'D'.symm, hS8,
      Function.update_of_ne hTD'.symm, hS7, Function.update_of_ne hXD'.symm, hS6,
      Function.update_of_ne hXD'.symm, hS5, Function.update_of_ne hU'D'.symm,
      Function.update_of_ne hUD'.symm, Function.update_of_ne hTD'.symm, hS3,
      Function.update_of_ne hU'D'.symm, Function.update_of_ne hUD'.symm,
      Function.update_of_ne hTD'.symm, Function.update_of_ne hXD'.symm, hD', toks_eq_map]
  have h9D : S9 kD = Sym.mark :: D0 := by
    rw [hS9, Function.update_of_ne hUD.symm, Function.update_of_ne hU'D.symm, hS8,
      Function.update_of_ne hTD.symm, hS7, Function.update_of_ne hXD.symm, hS6,
      Function.update_of_ne hXD.symm, hS5, Function.update_of_ne hU'D.symm,
      Function.update_of_ne hUD.symm, Function.update_of_ne hTD.symm, hS3,
      Function.update_of_ne hU'D.symm, Function.update_of_ne hUD.symm,
      Function.update_of_ne hTD.symm, Function.update_of_ne hXD.symm, hD]
  have e10 := Eval.liftRegs lensX (moveBlock_eval hDD'.symm [] (lensX.get (some Sym.mark,
    p3, lbE, ng)) (List.replicate d true) (Sym.mark :: D'0) S9 (TermOK.cons rfl _) h9D')
    (some Sym.mark, p3, lbE, ng) rfl
  rw [h9D] at e10
  set S10 := Function.update (Function.update S9 kD' (Sym.mark :: D'0)) kD
    ((List.replicate d true).reverse.map Sym.bit ++ Sym.mark :: D0) with hS10
  have e11 := pkO_eval kX (some Sym.mark, p3, lbE, ng) S10
  have h10X : S10 kX = R := by
    rw [hS10, Function.update_of_ne hXD, Function.update_of_ne hXD', hS9,
      Function.update_of_ne hXU, Function.update_of_ne hXU', hS8, Function.update_of_ne hXT, hS7,
      Function.update_self]
  refine ⟨p3, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 (Eval.seq e10 e11)))))))))).of_eq
      (st_eqX (by rw [h10X]) ?_) ?_⟩
  · clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    funext k
    simp only [hS10, hS9, hS8, hS7, hS6, hS5, hS3, Function.update_apply, List.reverse_replicate,
      ← toks_eq_map]
    split_ifs <;> simp_all
  · simp only [List.length_drop, List.length_replicate]
    omega

theorem recBodyX_eval (hXT : kX ≠ kT) (hXU : kX ≠ kU) (hXU' : kX ≠ kU') (hXD : kX ≠ kD)
    (hXD' : kX ≠ kD') (hTU : kT ≠ kU) (hTU' : kT ≠ kU') (hTD : kT ≠ kD) (hTD' : kT ≠ kD')
    (hUU' : kU ≠ kU') (hUD : kU ≠ kD) (hUD' : kU ≠ kD') (hU'D : kU' ≠ kD) (hU'D' : kU' ≠ kD')
    (hDD' : kD ≠ kD')
    (w2 d : ℕ) (xs : List Bool) (o p : Option Sym) (lb ng : Bool)
    (R U0 U'0 D0 D'0 : List Sym) (S : K → List Sym) (hxs : xs ≠ [])
    (hd : d ≤ (if ng then xs.length else w2))
    (hX : S kX = xs.map Sym.bit ++ Sym.sep :: R) (hU : S kU = toks w2 ++ Sym.mark :: U0)
    (hU' : S kU' = Sym.mark :: U'0) (hD : S kD = toks d ++ Sym.mark :: D0)
    (hD' : S kD' = Sym.mark :: D'0) :
    ∃ (p' : Option Sym) (lb' : Bool) (t : ℕ), t ≤ 25 * (xs.length + w2 + 1) ∧
      Eval [] (recBodyX kX kT kU kU' kD kD') ⟨(o, p, lb, ng), S⟩
        ⟨(R.head?, p', lb', ng), Function.update (Function.update S kX R) kT
          ((recSyms (outRec ng w2 d xs)).reverse ++ S kT)⟩ t := by
  cases ng with
  | true =>
    simp only [if_true] at hd
    have e1 := pkO_eval kD (o, p, lb, true) S
    have e2 := pkP_eval kX ((S kD).head?, p, lb, true) S
    have e3 := sLoop_eval hXD hXD' hDD' d xs lb true D0 R S hd hD hX
    set SS := Function.update (Function.update (Function.update S
        kX ((xs.drop d).map Sym.bit ++ Sym.sep :: R)) kD (Sym.mark :: D0))
        kD' (toks d ++ S kD') with hSS
    obtain ⟨p', e4⟩ := recTailX_eval hXT hXU hXU' hXD hXD' hTU hTU' hTD hTD' hUU' hUD hUD'
      hU'D hU'D' hDD' (xs.drop d) w2 0 d (some Sym.mark)
      (((xs.drop d).map Sym.bit ++ Sym.sep :: R).head?) (lastOr lb (xs.take d)) true
      R U0 U'0 D0 D'0 SS
      (by rw [hSS, Function.update_of_ne hXD', Function.update_of_ne hXD, Function.update_self])
      (by rw [hSS, Function.update_of_ne hUD', Function.update_of_ne hUD,
        Function.update_of_ne hXU.symm, hU])
      (by rw [hSS, Function.update_of_ne hU'D', Function.update_of_ne hU'D,
        Function.update_of_ne hXU'.symm, hU']; rfl)
      (by rw [hSS, Function.update_of_ne hDD', Function.update_self])
      (by rw [hSS, Function.update_self, hD'])
    have hSST : SS kT = S kT := by
      rw [hSS, Function.update_of_ne hTD', Function.update_of_ne hTD, Function.update_of_ne hXT.symm]
    rw [hSST] at e4
    have hT : (recSyms (outRec true w2 d xs)).reverse ++ S kT =
        Sym.sep :: (List.replicate (w2 - min w2 (xs.drop d).length)
          (Sym.bit (lastOr (lastOr lb (xs.take d)) ((xs.drop d).take
            (min w2 (xs.drop d).length)))) ++
          (((xs.drop d).take (min w2 (xs.drop d).length)).reverse.map Sym.bit ++ S kT)) := by
      rw [outRec, if_pos rfl, ← out_neg_eq w2 d xs lb hxs, reverse_recSyms, List.reverse_append,
        List.reverse_replicate, List.map_append, List.map_replicate, List.cons_append,
        List.append_assoc]
    refine ⟨p', _, _, ?_, (Eval.seq (Eval.ite_true rfl (Eval.seq e1 (Eval.seq e2 e3))) e4).of_eq
      (st_eqX rfl ?_) rfl⟩
    · simp only [List.length_drop]
      omega
    · clear e1 e2 e3 e4
      rw [hT]
      funext k
      simp only [hSS, Function.update_apply, Nat.zero_add]
      split_ifs <;> simp_all
  | false =>
    simp only [Bool.false_eq_true, if_false] at hd
    have e1 := pkO_eval kD (o, p, lb, false) S
    have e2 := pkP_eval kU ((S kD).head?, p, lb, false) S
    have e3 := zLoop_eval hTD hTD' hTU hTU' hDD' hUD.symm hU'D.symm hUD'.symm hU'D'.symm hUU'
      d w2 lb false D0 U0 S hd hD hU
    set SZ := Function.update (Function.update (Function.update (Function.update (Function.update S
        kT (List.replicate d (Sym.bit false) ++ S kT)) kD (Sym.mark :: D0))
        kD' (toks d ++ S kD')) kU (toks (w2 - d) ++ Sym.mark :: U0)) kU' (toks d ++ S kU')
      with hSZ
    obtain ⟨p', e4⟩ := recTailX_eval hXT hXU hXU' hXD hXD' hTU hTU' hTD hTD' hUU' hUD hUD'
      hU'D hU'D' hDD' xs (w2 - d) d d (some Sym.mark) ((toks (w2 - d) ++ Sym.mark :: U0).head?)
      lb false R U0 U'0 D0 D'0 SZ
      (by rw [hSZ, Function.update_of_ne hXU', Function.update_of_ne hXU,
        Function.update_of_ne hXD', Function.update_of_ne hXD, Function.update_of_ne hXT, hX])
      (by rw [hSZ, Function.update_of_ne hUU', Function.update_self])
      (by rw [hSZ, Function.update_self, hU'])
      (by rw [hSZ, Function.update_of_ne hU'D.symm, Function.update_of_ne hUD.symm,
        Function.update_of_ne hDD', Function.update_self])
      (by rw [hSZ, Function.update_of_ne hU'D'.symm, Function.update_of_ne hUD'.symm,
        Function.update_self, hD'])
    have hSZT : SZ kT = List.replicate d (Sym.bit false) ++ S kT := by
      rw [hSZ, Function.update_of_ne hTU', Function.update_of_ne hTU, Function.update_of_ne hTD',
        Function.update_of_ne hTD, Function.update_self]
    rw [hSZT] at e4
    have hT : (recSyms (outRec false w2 d xs)).reverse ++ S kT =
        Sym.sep :: (List.replicate (w2 - d - min (w2 - d) xs.length)
          (Sym.bit (lastOr lb (xs.take (min (w2 - d) xs.length)))) ++
          ((xs.take (min (w2 - d) xs.length)).reverse.map Sym.bit ++
            (List.replicate d (Sym.bit false) ++ S kT))) := by
      rw [outRec, if_neg (by decide), ← out_pos_eq w2 d xs lb hxs hd, reverse_recSyms,
        List.reverse_append, List.reverse_append, List.reverse_replicate, List.reverse_replicate,
        List.map_append, List.map_append, List.map_replicate, List.map_replicate,
        List.cons_append, List.append_assoc, List.append_assoc]
    refine ⟨p', _, _, ?_, (Eval.seq (Eval.ite_false rfl (Eval.seq e1 (Eval.seq e2 e3))) e4).of_eq
      (st_eqX rfl ?_) rfl⟩
    · omega
    · clear e1 e2 e3 e4
      rw [hT]
      funext k
      simp only [hSZ, Function.update_apply, show d + (w2 - d) = w2 by omega]
      split_ifs <;> simp_all

theorem recLoopX_eval (hXT : kX ≠ kT) (hXU : kX ≠ kU) (hXU' : kX ≠ kU') (hXD : kX ≠ kD)
    (hXD' : kX ≠ kD') (hTU : kT ≠ kU) (hTU' : kT ≠ kU') (hTD : kT ≠ kD) (hTD' : kT ≠ kD')
    (hUU' : kU ≠ kU') (hUD : kU ≠ kD) (hUD' : kU ≠ kD') (hU'D : kU' ≠ kD) (hU'D' : kU' ≠ kD')
    (hDD' : kD ≠ kD') (w1 w2 d : ℕ) (ng : Bool) (hw1 : 1 ≤ w1)
    (hd : d ≤ (if ng then w1 else w2)) (U0 U'0 D0 D'0 : List Sym) :
    ∀ (xss : List (List Bool)) (R : List Sym) (o p : Option Sym) (lb : Bool) (S : K → List Sym),
      (∀ xs ∈ xss, xs.length = w1) → optIsBit R.head? = false → o = (S kX).head? →
      S kX = arrSyms xss ++ R → S kU = toks w2 ++ Sym.mark :: U0 →
      S kU' = Sym.mark :: U'0 → S kD = toks d ++ Sym.mark :: D0 → S kD' = Sym.mark :: D'0 →
      ∃ (v' : XReg) (t : ℕ), t ≤ xss.length * (25 * (w1 + w2 + 1) + 1) + 1 ∧
        Eval [] (recLoopX kX kT kU kU' kD kD') ⟨(o, p, lb, ng), S⟩
          ⟨v', Function.update (Function.update S kX R) kT
            ((arrSyms (xss.map (outRec ng w2 d))).reverse ++ S kT)⟩ t
  | [], R, o, p, lb, S, _, hR, ho, hX, _, _, _, _ => by
    have hX' : S kX = R := hX
    refine ⟨_, _, by simp, (Eval.loop_false ?_).of_eq (st_eqX rfl ?_) rfl⟩
    · show oBit (o, p, lb, ng) = false
      rw [ho, hX']
      exact hR
    · simp only [List.map_nil, arrSyms_nil, List.reverse_nil, List.nil_append]
      rw [update_eq_of_eq hX', Function.update_eq_self]
  | xs :: xss, R, o, p, lb, S, hxs, hR, ho, hX, hU, hU', hD, hD' => by
    have hxw : xs.length = w1 := hxs xs List.mem_cons_self
    have hne : xs ≠ [] := by
      intro h
      rw [h] at hxw
      simp at hxw
      omega
    have hX' : S kX = xs.map Sym.bit ++ Sym.sep :: (arrSyms xss ++ R) := by
      rw [hX, arrSyms_cons, List.append_assoc, recSyms_append]
    obtain ⟨p1, lb1, t1, ht1, e1⟩ := recBodyX_eval hXT hXU hXU' hXD hXD' hTU hTU' hTD hTD' hUU'
      hUD hUD' hU'D hU'D' hDD' w2 d xs o p lb ng (arrSyms xss ++ R) U0 U'0 D0 D'0 S hne
      (by rw [hxw]; exact hd) hX' hU hU' hD hD'
    set S1 := Function.update (Function.update S kX (arrSyms xss ++ R)) kT
      ((recSyms (outRec ng w2 d xs)).reverse ++ S kT) with hS1
    obtain ⟨v', t2, ht2, e2⟩ := recLoopX_eval hXT hXU hXU' hXD hXD' hTU hTU' hTD hTD' hUU' hUD
      hUD' hU'D hU'D' hDD' w1 w2 d ng hw1 hd U0 U'0 D0 D'0 xss R (arrSyms xss ++ R).head? p1 lb1
      S1 (fun q hq => hxs q (List.mem_cons_of_mem _ hq)) hR
      (by rw [hS1, Function.update_of_ne hXT, Function.update_self])
      (by rw [hS1, Function.update_of_ne hXT, Function.update_self])
      (by rw [hS1, Function.update_of_ne hTU.symm, Function.update_of_ne hXU.symm, hU])
      (by rw [hS1, Function.update_of_ne hTU'.symm, Function.update_of_ne hXU'.symm, hU'])
      (by rw [hS1, Function.update_of_ne hTD.symm, Function.update_of_ne hXD.symm, hD])
      (by rw [hS1, Function.update_of_ne hTD'.symm, Function.update_of_ne hXD'.symm, hD'])
    have h1T : S1 kT = (recSyms (outRec ng w2 d xs)).reverse ++ S kT := by
      rw [hS1, Function.update_self]
    rw [h1T] at e2
    have hc : oBit (o, p, lb, ng) = true := by
      show optIsBit o = true
      rw [ho, hX']
      cases xs with
      | nil => exact absurd rfl hne
      | cons x xs' => rfl
    refine ⟨v', t1 + t2 + 1, ?_, (Eval.loop_true hc e1 e2).of_eq (st_eqX rfl ?_) rfl⟩
    · rw [hxw] at ht1
      simp only [List.length_cons]
      rw [Nat.succ_mul]
      generalize xss.length * (25 * (w1 + w2 + 1) + 1) = A at ht2 ⊢
      omega
    · clear e1 e2
      funext k
      simp only [hS1, Function.update_apply, List.map_cons, arrSyms_cons, List.reverse_append,
        List.append_assoc]
      split_ifs <;> simp_all

end Rec

end SubNLogN.Machine.K1.ShiftAux
