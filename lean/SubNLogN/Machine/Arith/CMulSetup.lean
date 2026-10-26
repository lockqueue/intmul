/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulCoef
import SubNLogN.Machine.Arith.Shift

/-!
# AR, products: setup of the product kernel (`Arith/CMulSetup.lean`)

**Scope (honest summary).** `cmulSetup` builds, from the counters `w1, w2, w3, s` (stacks `.inl
3..6`, restored), the rulers `R1 = w1`, `Rt = w2`, `R2 = w3`, `RW = W`, `Rs = min s W`,
`Rh = W - min s W` marks, `W = 2·max w1 w2 + 1` (computed in binary on `WB`: comparison, copy of the
larger counter, one appended bit), and pushes the guard `mark` on the output stack.
`cmulSetup_eval` (from clean scratch): exact final stacks `setupSt`, cost
`≤ 300 (w1 + w2 + w3 + bitLen s) + 300`. Everything is proved (no `sorry`).
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-- `WB := natSyms (2·max w1 w2 + 1)`. -/
def maxW : AProg CK :=
  .seq ((Lib.cmpNum (.inl 3) (.inl 4) (cs .t1) (cs .t2)).liftRegs lensC)
  (.seq (.ite (fun v => decide (v.ord = .lt))
      ((Lib.copyBlock (.inl 4) (cs .WB) (cs .CT)).liftRegs lensO)
      ((Lib.copyBlock (.inl 3) (cs .WB) (cs .CT)).liftRegs lensO))
    (pushS (cs .WB) (.bit true)))

/-- Compare `s` with `W`. -/
def cmpSW : AProg CK := (Lib.cmpNum (.inl 6) (cs .WB) (cs .t1) (cs .t2)).liftRegs lensC

/-- `Rs := min s W`. -/
def minSW : AProg CK :=
  .ite (fun v => decide (v.ord = .lt)) (buildRuler (.inl 6) (cs .Rs) (cs .C) (cs .Y))
    (.seq (copyRuler (cs .RW) (cs .X) (cs .Rs)) (moveMarks (cs .X) (cs .RW)))

/-- `Rh := W - min s W`. -/
def subSW : AProg CK :=
  .seq (copyRuler (cs .RW) (cs .X) (cs .Rh)) (.seq (moveMarks (cs .X) (cs .RW))
  (.seq (subRuler (cs .Rs) (cs .X) (cs .Rh)) (moveMarks (cs .X) (cs .Rs))))

/-- **Setup of the product kernel.** -/
def cmulSetup : AProg CK :=
  .seq (pushS (cs .T) .mark)
  (.seq (buildRuler (.inl 3) (cs .R1) (cs .C) (cs .Y))
  (.seq (buildRuler (.inl 4) (cs .Rt) (cs .C) (cs .Y))
  (.seq (buildRuler (.inl 5) (cs .R2) (cs .C) (cs .Y))
  (.seq maxW
  (.seq (buildRuler (cs .WB) (cs .RW) (cs .C) (cs .Y))
  (.seq cmpSW (.seq minSW (.seq subSW (drainBits (cs .WB))))))))))

/-- The stacks after the setup (from clean scratch). -/
def setupSt (w1 w2 w3 s : ℕ) (S : CK → List Sym) : CK → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update S (cs .T) [Sym.mark]) (cs .R1) (List.replicate w1 .mark))
    (cs .Rt) (List.replicate w2 .mark)) (cs .R2) (List.replicate w3 .mark))
    (cs .RW) (List.replicate (2 * max w1 w2 + 1) .mark))
    (cs .Rs) (List.replicate (min s (2 * max w1 w2 + 1)) .mark))
    (cs .Rh) (List.replicate (2 * max w1 w2 + 1 - min s (2 * max w1 w2 + 1)) .mark)

theorem natSyms_double_add_one (n : ℕ) : natSyms (2 * n + 1) = Sym.bit true :: natSyms n := by
  rw [show 2 * n + 1 = n + n + 1 by ring]
  simp [natSyms, encodeNat_add_add_one]

theorem cmpC_eval {k1 k2 : CK} (h12 : k1 ≠ k2) (h1a : k1 ≠ cs .t1) (h1b : k1 ≠ cs .t2)
    (h2a : k2 ≠ cs .t1) (h2b : k2 ≠ cs .t2) (a b : ℕ) (ra rb : List Sym) (v : AReg)
    (S : CK → List Sym) (hra : TermOK ra) (hrb : TermOK rb) (ha : S k1 = natSyms a ++ ra)
    (hb : S k2 = natSyms b ++ rb) :
    ∃ v' : AReg, v'.ord = Lib.ordOf a b ∧
      Eval [] ((Lib.cmpNum k1 k2 (cs .t1) (cs .t2)).liftRegs lensC) ⟨v, S⟩ ⟨v', S⟩
        (12 * min (bitLen a) (bitLen b) + 15) := by
  have e := Lib.cmpNum_eval h12 h1a h1b h2a h2b (by decide) (lensC.get v)
    (encodeNat a) (encodeNat b) ra rb S hra hrb ha hb
  have e' := Eval.liftRegs lensC e v rfl
  refine ⟨_, ?_, e'⟩
  show Lib.cmpAll .eq (encodeNat a) (encodeNat b) = Lib.ordOf a b
  rw [Lib.cmpAll_eq_ordOf _ _ (normBits_encodeNat a) (normBits_encodeNat b), bitsVal_encodeNat,
    bitsVal_encodeNat]

theorem maxW_eval (w1 w2 : ℕ) (r3 r4 : List Sym) (v : AReg) (S : CK → List Sym)
    (hr3 : TermOK r3) (hr4 : TermOK r4) (h3 : S (.inl 3) = natSyms w1 ++ r3)
    (h4 : S (.inl 4) = natSyms w2 ++ r4) (hWB : S (cs .WB) = []) :
    ∃ (v' : AReg) (t : ℕ), Eval [] maxW ⟨v, S⟩
      ⟨v', Function.update S (cs .WB) (natSyms (2 * max w1 w2 + 1))⟩ t ∧
      t ≤ 19 * (w1 + w2) + 30 := by
  obtain ⟨v1, hv1, e1⟩ := cmpC_eval (k1 := .inl 3) (k2 := .inl 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) w1 w2 r3 r4 v S hr3 hr4 h3 h4
  have hb1 : (encodeNat w1).length ≤ w1 := bitLen_le_self' w1
  have hb2 : (encodeNat w2).length ≤ w2 := bitLen_le_self' w2
  have hm : min (bitLen w1) (bitLen w2) ≤ w1 := le_trans (min_le_left _ _) (bitLen_le_self' w1)
  by_cases hlt : w1 < w2
  · have hc : decide (v1.ord = .lt) = true := by simp [hv1, Lib.ordOf, hlt]
    have e2 := Lib.copyBlock_eval (src := (.inl 4 : CK)) (dst := cs .WB) (tmp := cs .CT)
      (by decide) (by decide) (by decide) [] (lensO.get v1) (encodeNat w2) r4 S hr4 h4
    have e2' := Eval.liftRegs lensO e2 v1 rfl
    have e3 := eval_pushS (cs .WB) (.bit true) (lensO.set v1 (some .mark))
      (Function.update S (cs .WB) ((encodeNat w2).map Sym.bit ++ S (cs .WB)))
    have E := Eval.seq e1 (Eval.seq (Eval.ite_true (c := fun v : AReg => decide (v.ord = .lt))
      (q := (Lib.copyBlock (.inl 3) (cs .WB) (cs .CT)).liftRegs lensO) hc e2') e3)
    refine ⟨lensO.set v1 (some .mark), _, Eval.of_eq (p := maxW) E ?_ rfl, ?_⟩
    · congr 1
      rw [Function.update_self, Function.update_idem, hWB, List.append_nil, max_eq_right hlt.le,
        natSyms_double_add_one]
      rfl
    · omega
  · have hc : decide (v1.ord = .lt) = false := by
      simp only [hv1, Lib.ordOf, hlt, if_false, decide_eq_false_iff_not]
      split_ifs <;> simp
    have e2 := Lib.copyBlock_eval (src := (.inl 3 : CK)) (dst := cs .WB) (tmp := cs .CT)
      (by decide) (by decide) (by decide) [] (lensO.get v1) (encodeNat w1) r3 S hr3 h3
    have e2' := Eval.liftRegs lensO e2 v1 rfl
    have e3 := eval_pushS (cs .WB) (.bit true) (lensO.set v1 (some .mark))
      (Function.update S (cs .WB) ((encodeNat w1).map Sym.bit ++ S (cs .WB)))
    have E := Eval.seq e1 (Eval.seq (Eval.ite_false (c := fun v : AReg => decide (v.ord = .lt))
      (p := (Lib.copyBlock (.inl 4) (cs .WB) (cs .CT)).liftRegs lensO) hc e2') e3)
    refine ⟨lensO.set v1 (some .mark), _, Eval.of_eq (p := maxW) E ?_ rfl, ?_⟩
    · congr 1
      rw [Function.update_self, Function.update_idem, hWB, List.append_nil,
        max_eq_left (not_lt.mp hlt), natSyms_double_add_one]
      rfl
    · omega

set_option maxHeartbeats 2000000 in
theorem minSW_eval (W s : ℕ) (r6 : List Sym) (v : AReg) (Q : CK → List Sym)
    (hr6 : TermOK r6) (h6 : Q (.inl 6) = natSyms s ++ r6) (hord : v.ord = Lib.ordOf s W)
    (hRs : Q (cs .Rs) = []) (hRW : Q (cs .RW) = List.replicate W .mark) (hX : Q (cs .X) = []) :
    ∃ (v' : AReg) (t : ℕ), Eval [] minSW ⟨v, Q⟩
      ⟨v', Function.update Q (cs .Rs) (List.replicate (min s W) .mark)⟩ t ∧
      t ≤ 9 * W + 16 * bitLen s + 9 := by
  by_cases hlt : s < W
  · have hc : decide (v.ord = .lt) = true := by simp [hord, Lib.ordOf, hlt]
    obtain ⟨v1, t1, e1, ht1⟩ := buildRuler_eval (N := (.inl 6 : CK)) (R := cs .Rs) (C := cs .C)
      (Y := cs .Y) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s r6
      [] v Q hr6 aHead_nil h6 hRs
    refine ⟨v1, t1 + 1, (Eval.ite_true hc e1).of_eq
      (by rw [min_eq_left hlt.le, List.append_nil]) rfl, by omega⟩
  · have hc : decide (v.ord = .lt) = false := by
      simp only [hord, Lib.ordOf, hlt, if_false, decide_eq_false_iff_not]
      split_ifs <;> simp
    have e1a := eval_peekR (cs .RW) v Q
    rw [hRW] at e1a
    have e1b := copyLoop_eval (R := cs .RW) (X := cs .X) (D := cs .Rs) (by decide)
      (by decide) (by decide) W [] (setR v (List.replicate W Sym.mark).head?) Q aHead_nil
      (by rw [hRW, List.append_nil]) (by rw [List.append_nil]; rfl)
    set Q1 := Function.update (Function.update (Function.update Q (cs .RW) []) (cs .X)
      (List.replicate W .mark ++ Q (cs .X))) (cs .Rs) (List.replicate W .mark ++ Q (cs .Rs))
      with hQ1
    have e2 := moveMarks_eval (X := cs .X) (R := cs .RW) (by decide) W []
      { (setR v (List.replicate W Sym.mark).head?) with r := ([] : List Sym).head? } Q1 aHead_nil
      (by simp [hQ1, hX])
    have E : Eval [] minSW ⟨v, Q⟩ ⟨{ { (setR v (List.replicate W Sym.mark).head?) with
        r := ([] : List Sym).head? } with r := ([] : List Sym).head? },
        Function.update Q (cs .Rs) (List.replicate (min s W) .mark)⟩ (9 * W + 5) := by
      unfold minSW
      refine (Eval.ite_false hc (Eval.seq (Eval.seq e1a e1b) e2)).of_eq ?_ (by ring)
      congr 1
      rw [min_eq_right (by omega)]
      funext k
      simp only [hQ1, Function.update_apply]
      split_ifs <;> simp_all
    exact ⟨_, _, E, by omega⟩

set_option maxHeartbeats 2000000 in
theorem subSW_eval (W s' : ℕ) (hs : s' ≤ W) (v : AReg) (Q : CK → List Sym)
    (hRs : Q (cs .Rs) = List.replicate s' .mark) (hRW : Q (cs .RW) = List.replicate W .mark)
    (hRh : Q (cs .Rh) = []) (hX : Q (cs .X) = []) :
    ∃ v' : AReg, Eval [] subSW ⟨v, Q⟩
      ⟨v', Function.update Q (cs .Rh) (List.replicate (W - s') .mark)⟩ (9 * W + 9 * s' + 8) := by
  have e1a := eval_peekR (cs .RW) v Q
  rw [hRW] at e1a
  have e1b := copyLoop_eval (R := cs .RW) (X := cs .X) (D := cs .Rh) (by decide)
    (by decide) (by decide) W [] (setR v (List.replicate W Sym.mark).head?) Q aHead_nil
    (by rw [hRW, List.append_nil]) (by rw [List.append_nil]; rfl)
  set Q1 := Function.update (Function.update (Function.update Q (cs .RW) []) (cs .X)
    (List.replicate W .mark ++ Q (cs .X))) (cs .Rh) (List.replicate W .mark ++ Q (cs .Rh))
    with hQ1
  obtain ⟨u1, e1⟩ : ∃ u, Eval [] (copyRuler (cs .RW) (cs .X) (cs .Rh)) ⟨v, Q⟩ ⟨u, Q1⟩
      (1 + (5 * W + 1)) := ⟨_, Eval.seq e1a e1b⟩
  set Q2 := Function.update Q (cs .Rh) (List.replicate W .mark) with hQ2
  have hP2 : Function.update (Function.update Q1 (cs .X) []) (cs .RW)
      (List.replicate W .mark ++ Q1 (cs .RW)) = Q2 := by
    funext k
    simp only [hQ2, hQ1, Function.update_apply]
    split_ifs <;> simp_all
  obtain ⟨u2, e2⟩ : ∃ u, Eval [] (moveMarks (cs .X) (cs .RW)) ⟨u1, Q1⟩ ⟨u, Q2⟩ (4 * W + 2) :=
    ⟨_, (moveMarks_eval (X := cs .X) (R := cs .RW) (by decide) W [] u1 Q1 aHead_nil
      (by simp [hQ1, hX])).of_eq (by rw [hP2]) rfl⟩
  have h2Rs : Q2 (cs .Rs) = List.replicate s' .mark := by simp [hQ2, hRs]
  have e3a := eval_peekR (cs .Rs) u2 Q2
  rw [h2Rs] at e3a
  have e3b := subLoop_eval (R := cs .Rs) (X := cs .X) (D := cs .Rh) (by decide) (by decide)
    (by decide) s' (W - s') [] [] (setR u2 (List.replicate s' Sym.mark).head?) Q2 aHead_nil
    (by rw [h2Rs, List.append_nil])
    (by simp [hQ2, show s' + (W - s') = W by omega]) (by rw [List.append_nil]; rfl)
  set Q3 := Function.update (Function.update (Function.update Q2 (cs .Rs) []) (cs .X)
    (List.replicate s' .mark ++ Q2 (cs .X))) (cs .Rh) (List.replicate (W - s') .mark ++ [])
    with hQ3
  obtain ⟨u3, e3⟩ : ∃ u, Eval [] (subRuler (cs .Rs) (cs .X) (cs .Rh)) ⟨u2, Q2⟩ ⟨u, Q3⟩
      (1 + (5 * s' + 1)) := ⟨_, Eval.seq e3a e3b⟩
  have hP4 : Function.update (Function.update Q3 (cs .X) []) (cs .Rs)
      (List.replicate s' .mark ++ Q3 (cs .Rs)) =
      Function.update Q (cs .Rh) (List.replicate (W - s') .mark) := by
    funext k
    simp only [hQ3, hQ2, Function.update_apply]
    split_ifs <;> simp_all
  obtain ⟨u4, e4⟩ : ∃ u, Eval [] (moveMarks (cs .X) (cs .Rs)) ⟨u3, Q3⟩
      ⟨u, Function.update Q (cs .Rh) (List.replicate (W - s') .mark)⟩ (4 * s' + 2) :=
    ⟨_, (moveMarks_eval (X := cs .X) (R := cs .Rs) (by decide) s' [] u3 Q3 aHead_nil
      (by simp [hQ3, hQ2, hX])).of_eq (by rw [hP4]) rfl⟩
  exact ⟨u4, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq rfl (by ring)⟩

set_option maxHeartbeats 8000000 in
/-- **The setup**, from clean scratch: exact final stacks, bounded cost. -/
theorem cmulSetup_eval (w1 w2 w3 s : ℕ) (r3 r4 r5 r6 : List Sym) (v : AReg) (S : CK → List Sym)
    (hKC : KClean S) (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6)
    (h3 : S (.inl 3) = natSyms w1 ++ r3) (h4 : S (.inl 4) = natSyms w2 ++ r4)
    (h5 : S (.inl 5) = natSyms w3 ++ r5) (h6 : S (.inl 6) = natSyms s ++ r6) :
    ∃ (v' : AReg) (t : ℕ), Eval [] cmulSetup ⟨v, S⟩ ⟨v', setupSt w1 w2 w3 s S⟩ t ∧
      t ≤ 300 * (w1 + w2 + w3 + bitLen s) + 300 := by
  have hK : ∀ c : CS, S (cs c) = [] := fun c => hKC (.inl c)
  obtain ⟨W, hW⟩ : ∃ W, W = 2 * max w1 w2 + 1 := ⟨_, rfl⟩
  have e1 := eval_pushS (cs .T) .mark v S
  set Q1 := Function.update S (cs .T) (Sym.mark :: S (cs .T)) with hQ1
  obtain ⟨v2, t2, e2, ht2⟩ := buildRuler_eval (N := (.inl 3 : CK)) (R := cs .R1) (C := cs .C)
    (Y := cs .Y) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w1 r3 []
    v Q1 hr3 aHead_nil (by simp [hQ1, h3]) (by simp [hQ1, hK])
  set Q2 := Function.update Q1 (cs .R1) (List.replicate w1 .mark ++ []) with hQ2
  obtain ⟨v3, t3, e3, ht3⟩ := buildRuler_eval (N := (.inl 4 : CK)) (R := cs .Rt) (C := cs .C)
    (Y := cs .Y) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w2 r4 []
    v2 Q2 hr4 aHead_nil (by simp [hQ2, hQ1, h4]) (by simp [hQ2, hQ1, hK])
  set Q3 := Function.update Q2 (cs .Rt) (List.replicate w2 .mark ++ []) with hQ3
  obtain ⟨v4, t4, e4, ht4⟩ := buildRuler_eval (N := (.inl 5 : CK)) (R := cs .R2) (C := cs .C)
    (Y := cs .Y) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w3 r5 []
    v3 Q3 hr5 aHead_nil (by simp [hQ3, hQ2, hQ1, h5]) (by simp [hQ3, hQ2, hQ1, hK])
  set Q4 := Function.update Q3 (cs .R2) (List.replicate w3 .mark ++ []) with hQ4
  obtain ⟨v5, t5, e5, ht5⟩ := maxW_eval w1 w2 r3 r4 v4 Q4 hr3 hr4
    (by simp [hQ4, hQ3, hQ2, hQ1, h3]) (by simp [hQ4, hQ3, hQ2, hQ1, h4])
    (by simp [hQ4, hQ3, hQ2, hQ1, hK])
  rw [← hW] at e5
  set Q5 := Function.update Q4 (cs .WB) (natSyms W) with hQ5
  obtain ⟨v6, t6, e6, ht6⟩ := buildRuler_eval (N := cs .WB) (R := cs .RW) (C := cs .C)
    (Y := cs .Y) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) W [] []
    v5 Q5 aTermOK_nil aHead_nil (by simp [hQ5]) (by simp [hQ5, hQ4, hQ3, hQ2, hQ1, hK])
  set Q6 := Function.update Q5 (cs .RW) (List.replicate W .mark ++ []) with hQ6
  obtain ⟨v7, hv7, e7⟩ := cmpC_eval (k1 := .inl 6) (k2 := cs .WB) (by decide) (by decide)
    (by decide) (by decide) (by decide) s W r6 [] v6 Q6 hr6 aTermOK_nil
    (by simp [hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, h6]) (by simp [hQ6, hQ5])
  obtain ⟨v8, t8, e8, ht8⟩ := minSW_eval W s r6 v7 Q6 hr6
    (by simp [hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, h6]) hv7
    (by simp [hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, hK]) (by simp [hQ6])
    (by simp [hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, hK])
  set Q8 := Function.update Q6 (cs .Rs) (List.replicate (min s W) .mark) with hQ8
  obtain ⟨v9, e9⟩ := subSW_eval W (min s W) (min_le_right _ _) v8 Q8 (by simp [hQ8])
    (by simp [hQ8, hQ6]) (by simp [hQ8, hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, hK])
    (by simp [hQ8, hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, hK])
  set Q9 := Function.update Q8 (cs .Rh) (List.replicate (W - min s W) .mark) with hQ9
  have e10 := drainBits_eval (B := cs .WB) (encodeNat W) [] v9 Q9 aTermOK_nil
    (by simp [hQ9, hQ8, hQ6, hQ5, natSyms])
  refine ⟨{ v9 with q := ([] : List Sym).head? }, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3
    (Eval.seq e4 (Eval.seq e5 (Eval.seq e6 (Eval.seq e7 (Eval.seq e8 (Eval.seq e9
    e10))))))))).of_eq ?_ rfl, ?_⟩
  · congr 1
    funext k
    rcases k with i | c | g
    · simp [setupSt, hQ9, hQ8, hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, Function.update_apply]
    · cases c <;> simp [setupSt, hQ9, hQ8, hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, Function.update_apply,
        hK, ← hW]
    · simp [setupSt, hQ9, hQ8, hQ6, hQ5, hQ4, hQ3, hQ2, hQ1, Function.update_apply]
  · have hb1 := bitLen_le_self' w1
    have hb2 := bitLen_le_self' w2
    have hb3 := bitLen_le_self' w3
    have hbW := bitLen_le_self' W
    have hbW' : (encodeNat W).length ≤ W := bitLen_le_self' W
    have hms : min s W ≤ W := min_le_right _ _
    have hmb : min (bitLen s) (bitLen W) ≤ bitLen s := min_le_left _ _
    have hmax : max w1 w2 ≤ w1 + w2 := by omega
    omega

end SubNLogN.Machine.Arith
