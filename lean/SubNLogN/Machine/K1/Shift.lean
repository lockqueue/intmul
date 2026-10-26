/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.ShiftRec
import SubNLogN.Machine.K1.ShiftPre

/-!
# `SubNLogN.Machine.K1.Shift`: the fieldwise exact binary shift (K3)

Paper: Fact 3.3(5) (`fact:oai-streams`) and Lemma A.4(5) (`lem:transfer-streams`:
binary shifts by a supplied integer exponent, cost linear in the input and output widths,
uniformly in the exponent; proof: partition each word into the
retained interval and the known zero or redundant sign bits; copy and fill in one traversal; not
`t` one-bit shifts).

## Plan (program design, invariants, cost)
`shiftProg` (`K1/ShiftProg.lean`) on `KLoc (Fin 4) (Fin 7)`: named stacks `0` source, `1`
destination, `2` the counter `w2`, `3` the exponent `t`; seven private scratch stacks
(output buffer `T`, room counter `U`/`U'`, shift counter `D`/`D'`, binary counter copy `C`,
temporary `M`).
* If the source is empty: nothing (cost `3`).
* Otherwise: guards; `U := w2` tokens (full countdown of a copy of `w2`, amortized `O(w2)`);
  `ng := (t < 0)`; `D := min(|t|, cap)` tokens, `cap = w1` (first record's bits) if `t < 0`,
  else `w2` (capped countdown of a copy of `|t|`, `O(bitLen |t| + cap)`); the record loop
  (`K1/ShiftRec.lean`, `O(w1 + w2)` per record); rewind of the output buffer onto the
  destination; removal of the counters and guards.
* Record output: `outRec` = `d` leading zeros (`t ≥ 0`) or `d` dropped low bits (`t < 0`), then
  padding with the sign bit or truncation to `w2` bits; by `shiftBits_left`/`shiftBits_right`
  (`K1/ShiftMath.lean`) this is `twosBits w2 (shiftZ a t)` (uses `FitsTwos w1 a`).
* Total cost `≤ 100·(V_in + M·(w2 + 1) + bitLen |t| + 1)`.

**Scope (honest summary).** Proved (no `sorry`): `k3Shift_holds : K3ShiftStmt`
(`Contracts/Streams.lean:314`). Of the contract's hypotheses, the proof uses `1 ≤ w1`,
`FitsTwos w1 a` (sign extension), `BlkTerm ra`, `TermOK r2`, `TermOK r3`; the hypotheses
`1 ≤ w2`, the divisibility `2^(-t) ∣ a` for `t < 0`, and `FitsTwos w2 (shiftZ a t)` are not needed
(the output is the `w2`-bit field of `shiftZ a t` taken modulo `2^w2`, with floor division).
Helper declarations of all `K1/Shift*.lean` files live in `SubNLogN.Machine.K1.ShiftAux`; only
`k3Shift_holds` is in `SubNLogN.Machine.K1`.
-/

namespace SubNLogN.Machine.K1.ShiftAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1 SubNLogN.Machine.K1.AddSubAux

/-! ## The record identity -/

theorem lastOr_twosBits {w : ℕ} {a : ℤ} (hw : 1 ≤ w) (ha : FitsTwos w a) :
    lastOr false (twosBits w a) = decide (a < 0) := by
  rw [lastOr_eq_getLast?, getLast?_twosBits hw ha]
  rfl

theorem drop_min_length (s : ℕ) (xs : List Bool) : xs.drop (min s xs.length) = xs.drop s := by
  by_cases h : s ≤ xs.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (show xs.length ≤ s by omega), List.drop_length,
      List.drop_of_length_le (show xs.length ≤ s by omega)]

/-- **The record identity.** One record of the kernel computes the shifted field. -/
theorem outRec_twosBits {w1 w2 : ℕ} {a : ℤ} (hw1 : 1 ≤ w1) (ha : FitsTwos w1 a) (t : ℤ) :
    outRec (decide (t < 0)) w2
      (if t < 0 then min t.natAbs (twosBits w1 a).length else min t.natAbs w2)
      (twosBits w1 a) = twosBits w2 (shiftZ a t) := by
  unfold outRec shiftZ
  rw [lastOr_twosBits hw1 ha]
  by_cases ht : t < 0
  · rw [if_pos (decide_eq_true ht), if_pos ht, if_neg (by omega), drop_min_length,
      show (-t).toNat = t.natAbs by omega]
    exact shiftBits_right ha t.natAbs
  · rw [if_neg (by simp [ht]), if_neg ht, if_pos (by omega), show t.toNat = t.natAbs by omega]
    exact shiftBits_left ha t.natAbs

theorem map_outRec_fieldArr {w1 w2 : ℕ} (hw1 : 1 ≤ w1) (t : ℤ) (as : List ℤ)
    (hfit : ∀ a ∈ as, FitsTwos w1 a) :
    (fieldArr w1 as).map (outRec (decide (t < 0)) w2
      (if t < 0 then min t.natAbs w1 else min t.natAbs w2)) =
      fieldArr w2 (as.map fun a => shiftZ a t) := by
  simp only [fieldArr, List.map_map]
  apply List.map_congr_left
  intro a ha
  have h := outRec_twosBits (w2 := w2) hw1 (hfit a ha) t
  rw [length_twosBits] at h
  exact h

/-! ## The kernel on its stacks -/

/-- Stacks of the shift kernel: four named stacks and seven private scratch stacks. -/
abbrev SK : Type := KLoc (Fin 4) (Fin 7)

/-- The shift kernel on `SK`. -/
def shiftK : XProg SK :=
  shiftProg (.inl 0) (.inl 1) (.inl 2) (.inl 3) (.inr 0) (.inr 1) (.inr 2) (.inr 3) (.inr 4)
    (.inr 5) (.inr 6)

theorem shiftMain_eval (w1 w2 : ℕ) (t a : ℤ) (as : List ℤ) (ra r2 r3 : List Sym)
    (S : SK → List Sym) (hw1 : 1 ≤ w1) (hfit : ∀ b ∈ a :: as, FitsTwos w1 b) (hra : BlkTerm ra)
    (hr2 : TermOK r2) (hr3 : TermOK r3)
    (hX0 : S (.inl 0) = arrSyms (fieldArr w1 (a :: as)) ++ ra)
    (hW0 : S (.inl 2) = natSyms w2 ++ r2) (hT0 : S (.inl 3) = intSyms t ++ r3)
    (o p : Option Sym) (lb ng : Bool) :
    ∃ (v' : XReg) (tt : ℕ),
      tt ≤ 98 * ((as.length + 1) * (w1 + 1) + (as.length + 1) * (w2 + 1) + bitLen t.natAbs + 1) ∧
      Eval [] (shiftMain (.inl 0) (.inl 1) (.inl 2) (.inl 3) (.inr 0) (.inr 1) (.inr 2) (.inr 3)
        (.inr 4) (.inr 5) (.inr 6)) ⟨(o, p, lb, ng), S⟩
        ⟨v', Function.update (Function.update S (.inl 0) ra) (.inl 1)
          (arrSyms (fieldArr w2 ((a :: as).map fun b => shiftZ b t)) ++ S (.inl 1))⟩ tt := by
  -- 1. guards
  have e1 := setupX_eval (kT := (.inr 0 : SK)) (kU := .inr 1) (kU' := .inr 2) (kD := .inr 3)
    (kD' := .inr 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (o, p, lb, ng) S
  set S1 := Function.update (Function.update (Function.update (Function.update (Function.update S
    (.inr 0) (Sym.mark :: S (.inr 0))) (.inr 1) (Sym.mark :: S (.inr 1)))
    (.inr 2) (Sym.mark :: S (.inr 2))) (.inr 3) (Sym.mark :: S (.inr 3)))
    (.inr 4) (Sym.mark :: S (.inr 4)) with hS1
  -- 2. room counter
  obtain ⟨tU, htU, e2⟩ := buildU_eval (kW := (.inl 2 : SK)) (kC := .inr 5) (kM := .inr 6)
    (kU := .inr 1) (by decide) (by decide) (by decide) (by decide) w2 r2 hr2 o p lb ng S1
    (by simp [hS1, hW0])
  have h1C : S1 (.inr 5) = S (.inr 5) := by simp [hS1]
  have h1U : S1 (.inr 1) = Sym.mark :: S (.inr 1) := by simp [hS1]
  rw [h1C, h1U] at e2
  set S2 := Function.update (Function.update S1 (.inr 5) (Sym.mark :: S (.inr 5))) (.inr 1)
    (toks w2 ++ Sym.mark :: S (.inr 1)) with hS2
  -- 3. sign
  have h2Tc : S2 (.inl 3) = intSyms t ++ r3 := by simp [hS2, hS1, hT0]
  have e3 := readSign_eval (.inl 3 : SK) t r3 (some Sym.mark) p lb ng S2 h2Tc
  -- 4. shift counter
  have h2X : S2 (.inl 0) = (twosBits w1 a).map Sym.bit ++
      (Sym.sep :: (arrSyms (fieldArr w1 as) ++ ra)) := by
    simp [hS2, hS1, hX0, fieldArr, arrSyms_cons, recSyms]
  obtain ⟨o4, p4, lb4, tD, htD, e4⟩ := buildD_eval (kX := (.inl 0 : SK)) (kTc := .inl 3)
    (kC := .inr 5) (kM := .inr 6) (kU := .inr 1) (kU' := .inr 2) (kD := .inr 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    t r3 hr3 w2 (twosBits w1 a) _ (TermOK.cons rfl _) (S (.inr 1)) (S (.inr 2)) (S (.inr 5))
    (some (sgnSym t)) p lb S2 h2Tc (by simp [hS2]) h2X
    (by simp [hS2]) (by simp [hS2, hS1])
  have h2D : S2 (.inr 3) = Sym.mark :: S (.inr 3) := by simp [hS2, hS1]
  rw [h2D, length_twosBits] at e4
  rw [length_twosBits] at htD
  set d := if t < 0 then min t.natAbs w1 else min t.natAbs w2 with hd
  set S3 := Function.update S2 (.inr 3) (toks d ++ Sym.mark :: S (.inr 3)) with hS3
  -- 5. peek the source
  have e5 := pkO_eval (.inl 0 : SK) (o4, p4, lb4, decide (t < 0)) S3
  -- 6. records
  have hdle : d ≤ (if decide (t < 0) then w1 else w2) := by
    by_cases ht : t < 0
    · simp only [hd, if_pos ht, decide_eq_true ht, if_true]
      omega
    · simp only [hd, if_neg ht, decide_eq_false ht]
      simp only [Bool.false_eq_true, if_false]
      omega
  obtain ⟨v6, tR, htR, e6⟩ := recLoopX_eval (kX := (.inl 0 : SK)) (kT := .inr 0) (kU := .inr 1)
    (kU' := .inr 2) (kD := .inr 3) (kD' := .inr 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) w1 w2 d (decide (t < 0)) hw1
    hdle (S (.inr 1)) (S (.inr 2)) (S (.inr 3)) (S (.inr 4)) (fieldArr w1 (a :: as)) ra
    ((S3 (.inl 0)).head?) p4 lb4 S3 (width_fieldArr w1 (a :: as)) (optIsBit_head_of_blkTerm hra)
    rfl (by simp [hS3, hS2, hS1, hX0])
    (by simp [hS3, hS2]) (by simp [hS3, hS2, hS1])
    (by simp [hS3]) (by simp [hS3, hS2, hS1])
  have h3T : S3 (.inr 0) = Sym.mark :: S (.inr 0) := by
    simp [hS3, hS2, hS1]
  rw [h3T, map_outRec_fieldArr hw1 t (a :: as) hfit] at e6
  set out := arrSyms (fieldArr w2 ((a :: as).map fun b => shiftZ b t)) with hout
  set S4 := Function.update (Function.update S3 (.inl 0) ra) (.inr 0)
    (out.reverse ++ Sym.mark :: S (.inr 0)) with hS4
  -- 7. rewind the output buffer
  have h4T : S4 (.inr 0) = out.reverse ++ Sym.mark :: S (.inr 0) := by simp [hS4]
  have hmark : Sym.mark ∉ out.reverse := by
    rw [List.mem_reverse, hout]
    exact mark_not_mem_arrSyms _
  have e7 := Eval.liftRegs lensX (WP.W9comp.rewindTo_eval (by decide : (.inr 0 : SK) ≠ .inl 1)
    Sym.mark (lensX.get v6) out.reverse (S (.inr 0)) S4 hmark h4T) v6 rfl
  have h4Z : S4 (.inl 1) = S (.inl 1) := by simp [hS4, hS3, hS2, hS1]
  rw [h4Z, List.reverse_reverse] at e7
  set S5 := Function.update (Function.update S4 (.inr 0) (S (.inr 0))) (.inl 1)
    (out ++ S (.inl 1)) with hS5
  -- 8. cleanup
  obtain ⟨v8, e8⟩ := cleanupX_eval (kU := (.inr 1 : SK)) (kU' := .inr 2) (kD := .inr 3)
    (kD' := .inr 4) (kC := .inr 5) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) w2 d (S (.inr 1)) (S (.inr 2))
    (S (.inr 3)) (S (.inr 4)) (S (.inr 5)) (some Sym.mark) v6.2.1 v6.2.2.1 v6.2.2.2 S5
    (by simp [hS5, hS4, hS3, hS2])
    (by simp [hS5, hS4, hS3, hS2, hS1])
    (by simp [hS5, hS4, hS3])
    (by simp [hS5, hS4, hS3, hS2, hS1])
    (by simp [hS5, hS4, hS3, hS2])
  refine ⟨v8, _, ?_, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 (Eval.seq e7 e8))))))).of_eq (st_eqX rfl ?_) rfl⟩
  · -- cost
    have hM : (fieldArr w1 (a :: as)).length = as.length + 1 := by simp [fieldArr]
    have hout' : out.reverse.length = (as.length + 1) * (w2 + 1) := by
      rw [List.length_reverse, hout, length_arrSyms_of_width w2 _ (width_fieldArr w2 _)]
      simp [fieldArr]
    have hbw := bitLen_le_self w2
    have hdw : d ≤ w1 + w2 := by
      rw [hd]
      split_ifs <;> omega
    rw [hM] at htR
    rw [hout']
    have hM1 : 0 < as.length + 1 := by omega
    have q1 : (as.length + 1) * (25 * (w1 + w2 + 1) + 1) =
        25 * ((as.length + 1) * w1) + 25 * ((as.length + 1) * w2) + 26 * (as.length + 1) := by
      ring
    have q2 : (as.length + 1) * (w2 + 1) = (as.length + 1) * w2 + (as.length + 1) := by ring
    have q3 : (as.length + 1) * (w1 + 1) = (as.length + 1) * w1 + (as.length + 1) := by ring
    have hw1M : w1 ≤ (as.length + 1) * w1 := Nat.le_mul_of_pos_left w1 hM1
    have hw2M : w2 ≤ (as.length + 1) * w2 := Nat.le_mul_of_pos_left w2 hM1
    rw [q1] at htR
    rw [q2, q3]
    generalize (as.length + 1) * w1 = P1 at *
    generalize (as.length + 1) * w2 = P2 at *
    omega
  · clear e1 e2 e3 e4 e5 e6 e7 e8
    funext k
    rcases k with k | k <;> fin_cases k <;>
      simp [hS5, hS4, hS3, hS2, hS1]

end SubNLogN.Machine.K1.ShiftAux

namespace SubNLogN.Machine.K1

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.K1.AddSubAux
  SubNLogN.Machine.K1.ShiftAux

/-! ## The contract -/

/-- **K3, fieldwise exact binary shift by a supplied exponent, proved** (`K3ShiftStmt`,
`Contracts/Streams.lean`; paper: Lemma A.4(5) (`lem:transfer-streams`)). The kernel is
`shiftK` (seven private scratch stacks, `E = Fin 7`), constant `C = 100`. Of the contract's
hypotheses the proof uses `1 ≤ w1`, `FitsTwos w1 a` (sign extension), `BlkTerm ra`, `TermOK r2`
and `TermOK r3`; `1 ≤ w2`, the exactness hypothesis `2^(-t) ∣ a` (for `t < 0`) and
`FitsTwos w2 (shiftZ a t)` are not needed. -/
theorem k3Shift_holds : K3ShiftStmt := by
  refine ⟨100, fun _ => ⟨Fin 7, inferInstance, inferInstance, XReg, shiftK, inferInstance,
    inferInstance, closed_shiftProg _ _ _ _ _ _ _ _ _ _ _, ?_⟩⟩
  intro w1 w2 t as ra r2 r3 S hw1 _ hfit _ _ hra hr2 hr3 hS0 hS2 hS3
  apply Runs.of_eval
  rintro ⟨o, p, lb, ng⟩
  cases as with
  | nil =>
    have hX : S (.inl 0) = ra := by rw [hS0]; rfl
    refine ⟨((S (.inl 0)).head?, p, lb, ng), 1 + (1 + 1), ?_, trivial, by omega⟩
    refine (Eval.seq (pkO_eval _ _ _) (Eval.ite_false ?_ (skip_eval _ _))).of_eq
      (st_eqX rfl ?_) rfl
    · show optIsBit (S (.inl 0)).head? = false
      rw [hX]
      exact optIsBit_head_of_blkTerm hra
    · simp only [List.map_nil, fieldArr, arrSyms_nil, List.nil_append]
      rw [update_eq_of_eq hX, Function.update_eq_self]
  | cons a as =>
    obtain ⟨v', tt, htt, e⟩ := shiftMain_eval w1 w2 t a as ra r2 r3 S hw1 hfit hra hr2 hr3 hS0
      hS2 hS3 ((S (.inl 0)).head?) p lb ng
    refine ⟨v', 1 + (tt + 1), Eval.seq (pkO_eval _ _ _) (Eval.ite_true ?_ e), trivial, ?_⟩
    · show optIsBit (S (.inl 0)).head? = true
      rw [hS0]
      have hne : twosBits w1 a ≠ [] := by
        intro h
        have := length_twosBits w1 a
        rw [h] at this
        simp at this
        omega
      obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hne
      simp [fieldArr, arrSyms_cons, recSyms, hxs]
    · rw [vol_fieldArr, List.length_cons]
      generalize (as.length + 1) * (w1 + 1) = A at htt ⊢
      generalize (as.length + 1) * (w2 + 1) = B at htt ⊢
      omega

end SubNLogN.Machine.K1
