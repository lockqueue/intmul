/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6PcLoop

/-!
# Lemma A.8 piece-loop test (`Machine/AppC/C6PcTest.lean`): `C6PcTestStmt`

**Program.** `tProg q es` computes `t = c6T q e` (`e` read from the named stack `es`) on scratch
`3` above a `mark`: `k = clog m e` (`satLoop`/`clogStep`, `e` steps), `W = W_b^k` (`powMulN`),
`t = clog (q²) W` (`satLoop`/`clogStep`, `e` steps); every other stack is restored.
`testProg q` (named stacks `Fin 2`: `0` the counter `e`, `1` the offset `o`): `tProg q`, then
`ℓ = e - t` (`subN`), `cmpN o ℓ` (the observation: the compare register is `lt`), and the two scratch
numbers are dropped with their floors (`dropF`, which keeps the compare register). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Proved (no `sorry`).** `c6PcTest_holds (q) (hq : 2 ≤ q) : C6PcTestStmt q`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Lib TMFw.Contracts Computability

namespace AppC.C6PcAux

open NatArith

theorem c6K_le (e : ℕ) : c6K e ≤ e := by
  unfold c6K
  apply Nat.clog_le_of_le_pow
  calc e ≤ 2 ^ e := Nat.lt_two_pow_self.le
    _ ≤ tripleM 100 ^ e := Nat.pow_le_pow_left two_le_tripleM e

theorem bitLen_tripleWb : bitLen (tripleWb 100) ≤ 68 :=
  NatArith.bitLen_le_of_lt' (by decide)

section TProg

variable {N : Type} [DecidableEq N]

/-- `t = c6T q e` on scratch `3` (above a `mark`), `e` read from the named stack `.inl i`. -/
def tProg (q : ℕ) (i : N) : Prog (KLoc N PE) (fun _ => Sym) Reg :=
  .seq (pushMark (sv 0))
  (.seq (pushNat (sv 0) 0)
  (.seq (pushMark (sv 1))
  (.seq (pushNat (sv 1) 1)
  (.seq (satLoop (.inl i) (sv 6) (sv 7) (sv 1) (.inl i) (sv 8) (sv 9)
    (clogStep (sv 1) (sv 0) (sv 10) (sv 11) (sv 12) (sv 13) (sv 14) (sv 7) (sv 15) (tripleM 100)))
  (.seq (dropF (sv 1))
  (.seq (pushMark (sv 2))
  (.seq (pushNat (sv 2) 1)
  (.seq (powMulN (sv 2) (tripleWb 100) (sv 0) (sv 6) (sv 7) (sv 10) (sv 11) (sv 12) (sv 13)
    (sv 14))
  (.seq (dropF (sv 0))
  (.seq (pushMark (sv 3))
  (.seq (pushNat (sv 3) 0)
  (.seq (pushMark (sv 4))
  (.seq (pushNat (sv 4) 1)
  (.seq (satLoop (.inl i) (sv 6) (sv 7) (sv 4) (sv 2) (sv 8) (sv 9)
    (clogStep (sv 4) (sv 3) (sv 10) (sv 11) (sv 12) (sv 13) (sv 14) (sv 7) (sv 15) (q ^ 2)))
  (.seq (dropF (sv 4))
    (dropF (sv 2)))))))))))))))))

theorem closed_tProg (q : ℕ) (i : N) : (tProg q i).Closed :=
  ⟨closed_pushMark _, closed_pushNat _ _, closed_pushMark _, closed_pushNat _ _,
    closed_satLoop _ _ _ _ _ _ _ (closed_clogStep _ _ _ _ _ _ _ _ _ _), closed_dropF _,
    closed_pushMark _, closed_pushNat _ _, closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_dropF _,
    closed_pushMark _, closed_pushNat _ _, closed_pushMark _, closed_pushNat _ _,
    closed_satLoop _ _ _ _ _ _ _ (closed_clogStep _ _ _ _ _ _ _ _ _ _), closed_dropF _,
    closed_dropF _⟩

/-- The cost bound of `tProg`. -/
def tC (q : ℕ) : ℕ := 1000000000 * (bitLen q + 1) ^ 2

theorem tProg_cost_le {q : ℕ} (hq : 2 ≤ q) {e : ℕ} (he : 35 ≤ e) :
    e * (13 * clogM (tripleM 100) e e + 17) +
      e * (13 * clogM (q ^ 2) (tripleWb 100 ^ c6K e) e + 17) +
      powCost (tripleWb 100) 1 (c6K e) + 32 * e + 26 * bitLen e + 2 * bitLen 0 + 3 * bitLen 1 +
      2 * bitLen (tripleM 100 ^ c6K e) + 2 * bitLen (c6K e) + 2 * bitLen ((q ^ 2) ^ c6T q e) +
      2 * bitLen (tripleWb 100 ^ c6K e) + 42 ≤ tC q * (e + 1) ^ 3 := by
  have hq2 : 2 ≤ q ^ 2 := by nlinarith
  have hkle := c6K_le e
  have hb0 : bitLen 0 ≤ 1 := (bitLen_le_self'' 0).trans (by norm_num)
  have hb1 : bitLen 1 ≤ 1 := bitLen_le_self'' 1
  have hbe : bitLen e ≤ e := bitLen_le_self'' e
  have hbm := bitLen_tripleM
  have hbW := bitLen_tripleWb
  have hbk : bitLen (c6K e) ≤ e := (bitLen_le_self'' _).trans hkle
  have hbmk : bitLen (tripleM 100 ^ c6K e) ≤ bitLen e + bitLen (tripleM 100) + 2 :=
    clog_pow_bitLen two_le_tripleM le_rfl
  have hbWk0 : bitLen (tripleWb 100 ^ c6K e) ≤ (c6K e + 1) * bitLen (tripleWb 100) :=
    bitLen_pow_le (by decide) (c6K e)
  have hbWk : bitLen (tripleWb 100 ^ c6K e) ≤ 68 * (e + 1) := by
    have : (c6K e + 1) * bitLen (tripleWb 100) ≤ (e + 1) * 68 := Nat.mul_le_mul (by omega) hbW
    omega
  have hbq2 : bitLen (q ^ 2) ≤ (2 + 1) * bitLen q := bitLen_pow_le hq 2
  have hbqt : bitLen ((q ^ 2) ^ c6T q e) ≤ bitLen (tripleWb 100 ^ c6K e) + bitLen (q ^ 2) + 2 :=
    clog_pow_bitLen hq2 le_rfl
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 200 * (bitLen q + 1) * (e + 1) := ⟨_, rfl⟩
  have hYge : 200 * (e + 1) + 200 * bitLen q ≤ Y := by
    rw [hY]; nlinarith [Nat.zero_le (bitLen q * e)]
  have hY1 : 1 ≤ Y := by omega
  have hc1 : clogM (tripleM 100) e e ≤ 200 * Y ^ 2 := by
    unfold clogM
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hc2 : clogM (q ^ 2) (tripleWb 100 ^ c6K e) e ≤ 200 * Y ^ 2 := by
    unfold clogM
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hp : powCost (tripleWb 100) 1 (c6K e) ≤ (e + 1) * (200 * Y ^ 2) := by
    unfold powCost
    rw [one_mul]
    exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hL1 : e * (13 * clogM (tripleM 100) e e + 17) ≤ (e + 1) * (2600 * Y ^ 2 + 17) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hL2 : e * (13 * clogM (q ^ 2) (tripleWb 100 ^ c6K e) e + 17) ≤
      (e + 1) * (2600 * Y ^ 2 + 17) :=
    Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (e + 1) * Y ^ 2 := ⟨_, rfl⟩
  have hE1 : (e + 1) * (2600 * Y ^ 2 + 17) = 2600 * Z + 17 * (e + 1) := by rw [hZ]; ring
  have hE2 : (e + 1) * (200 * Y ^ 2) = 200 * Z := by rw [hZ]; ring
  have hYZ : Y ≤ Z := by
    rw [hZ]
    calc Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) Y
      _ ≤ (e + 1) * Y ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  have hT : tC q * (e + 1) ^ 3 = 25000 * Z := by rw [hZ, hY]; unfold tC; ring
  rw [hT]
  omega

theorem tProg_runs {q : ℕ} (hq : 2 ≤ q) (i : N) (e : ℕ) (he : 35 ≤ e) (re : List Sym)
    (hre : TermOK re) (S : KLoc N PE → List Sym) (hS : S (.inl i) = natSyms e ++ re) :
    Runs (tProg q i) S (Function.update S (sv 3) (natSyms (c6T q e) ++ Sym.mark :: S (sv 3)))
      (fun _ => True) (tC q * (e + 1) ^ 3) := by
  have hmk : ∀ x, TermOK (Sym.mark :: x) := termOK_mark
  have hq2 : 2 ≤ q ^ 2 := by nlinarith
  have hkle := c6K_le e
  have htle : c6T q e ≤ e := (C6Aux.c6T_lt hq he).2.le
  have e1 := runs_pushMark (sv 0) S
  set s1 := Function.update S (sv 0) (Sym.mark :: S (sv 0)) with hs1
  have e2 := runs_pushNat (sv 0) 0 s1
  rw [show s1 (sv 0) = Sym.mark :: S (sv 0) by simp [hs1]] at e2
  set s2 := Function.update s1 (sv 0) (natSyms 0 ++ Sym.mark :: S (sv 0)) with hs2
  have e3 := runs_pushMark (sv 1) s2
  rw [show s2 (sv 1) = S (sv 1) by simp [hs2, hs1, sv]] at e3
  set s3 := Function.update s2 (sv 1) (Sym.mark :: S (sv 1)) with hs3
  have e4 := runs_pushNat (sv 1) 1 s3
  rw [show s3 (sv 1) = Sym.mark :: S (sv 1) by simp [hs3]] at e4
  set s4 := Function.update s3 (sv 1) (natSyms 1 ++ Sym.mark :: S (sv 1)) with hs4
  have e5 := runs_clogLoop (ns := .inl i) (Kc := sv 6) (t := sv 7) (P := sv 1) (x := .inl i)
    (t1 := sv 8) (t2 := sv 9) (Kk := sv 0) (Q := sv 10) (Tdst := sv 11) (A := sv 12)
    (Bs := sv 13) (Acc := sv 14) (ti := sv 15) (by simp [sv]) (by simp [sv]) (by simp [sv])
    (by simp [sv]) (by simp [sv]) (by simp [sv]) (by simp [sv]) (by simp [sv]) (by simp [sv])
    (by simp [sv]) (by simp [sv]) (tripleM 100) e e two_le_tripleM hkle (Sym.mark :: S (sv 1))
    re (Sym.mark :: S (sv 0)) re s4 (hmk _) hre (hmk _) hre (by simp [hs4])
    (by simp [hs4, hs3, hs2, sv]) (by simp [hs4, hs3, hs2, hs1, sv, hS])
    (by simp [hs4, hs3, hs2, hs1, sv, hS])
  rw [show Nat.clog (tripleM 100) e = c6K e from rfl] at e5
  set s5 := clogSt s4 (sv 1) (sv 0) (tripleM 100) (Sym.mark :: S (sv 1)) (Sym.mark :: S (sv 0))
    (c6K e) with hs5
  have e6 := runs_dropF (sv 1) (tripleM 100 ^ c6K e) Sym.mark (S (sv 1)) s5 rfl
    (by simp [hs5, clogSt, sv])
  set s6 := Function.update s5 (sv 1) (S (sv 1)) with hs6
  have e7 := runs_pushMark (sv 2) s6
  rw [show s6 (sv 2) = S (sv 2) by simp [hs6, hs5, clogSt, hs4, hs3, hs2, hs1, sv]] at e7
  set s7 := Function.update s6 (sv 2) (Sym.mark :: S (sv 2)) with hs7
  have e8 := runs_pushNat (sv 2) 1 s7
  rw [show s7 (sv 2) = Sym.mark :: S (sv 2) by simp [hs7]] at e8
  set s8 := Function.update s7 (sv 2) (natSyms 1 ++ Sym.mark :: S (sv 2)) with hs8
  have e9 := runs_powMulN (k := sv 2) (ns := sv 0) (Kc := sv 6) (t := sv 7) (Q := sv 10)
    (Tdst := sv 11) (A := sv 12) (Bs := sv 13) (Acc := sv 14) (by simp [sv]) (tripleWb 100)
    (by decide) 1 (c6K e) (Sym.mark :: S (sv 2)) (Sym.mark :: S (sv 0)) s8 (hmk _) (hmk _)
    (by simp [hs8]) (by simp [hs8, hs7, hs6, hs5, clogSt, sv])
  rw [one_mul] at e9
  set s9 := Function.update s8 (sv 2) (natSyms (tripleWb 100 ^ c6K e) ++ Sym.mark :: S (sv 2))
    with hs9
  have e10 := runs_dropF (sv 0) (c6K e) Sym.mark (S (sv 0)) s9 rfl
    (by simp [hs9, hs8, hs7, hs6, hs5, clogSt, sv])
  set s10 := Function.update s9 (sv 0) (S (sv 0)) with hs10
  have e11 := runs_pushMark (sv 3) s10
  rw [show s10 (sv 3) = S (sv 3) by
    simp [hs10, hs9, hs8, hs7, hs6, hs5, clogSt, hs4, hs3, hs2, hs1, sv]] at e11
  set s11 := Function.update s10 (sv 3) (Sym.mark :: S (sv 3)) with hs11
  have e12 := runs_pushNat (sv 3) 0 s11
  rw [show s11 (sv 3) = Sym.mark :: S (sv 3) by simp [hs11]] at e12
  set s12 := Function.update s11 (sv 3) (natSyms 0 ++ Sym.mark :: S (sv 3)) with hs12
  have e13 := runs_pushMark (sv 4) s12
  rw [show s12 (sv 4) = S (sv 4) by
    simp [hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, clogSt, hs4, hs3, hs2, hs1, sv]] at e13
  set s13 := Function.update s12 (sv 4) (Sym.mark :: S (sv 4)) with hs13
  have e14 := runs_pushNat (sv 4) 1 s13
  rw [show s13 (sv 4) = Sym.mark :: S (sv 4) by simp [hs13]] at e14
  set s14 := Function.update s13 (sv 4) (natSyms 1 ++ Sym.mark :: S (sv 4)) with hs14
  have e15 := runs_clogLoop (ns := .inl i) (Kc := sv 6) (t := sv 7) (P := sv 4) (x := sv 2)
    (t1 := sv 8) (t2 := sv 9) (Kk := sv 3) (Q := sv 10) (Tdst := sv 11) (A := sv 12)
    (Bs := sv 13) (Acc := sv 14) (ti := sv 15) (by simp [sv]) (by simp [sv]) (by simp [sv])
    (by simp [sv]) (by simp [sv]) (by simp [sv]) (by simp [sv]) (by simp [sv]) (by simp [sv])
    (by simp [sv]) (by simp [sv]) (q ^ 2) (tripleWb 100 ^ c6K e) e hq2 htle
    (Sym.mark :: S (sv 4)) (Sym.mark :: S (sv 2)) (Sym.mark :: S (sv 3)) re s14 (hmk _) (hmk _)
    (hmk _) hre (by simp [hs14]) (by simp [hs14, hs13, hs12, sv])
    (by simp [hs14, hs13, hs12, hs11, hs10, hs9, sv])
    (by simp [hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, clogSt, hs4, hs3, hs2, hs1,
      sv, hS])
  rw [show Nat.clog (q ^ 2) (tripleWb 100 ^ c6K e) = c6T q e from rfl] at e15
  set s15 := clogSt s14 (sv 4) (sv 3) (q ^ 2) (Sym.mark :: S (sv 4)) (Sym.mark :: S (sv 3))
    (c6T q e) with hs15
  have e16 := runs_dropF (sv 4) ((q ^ 2) ^ c6T q e) Sym.mark (S (sv 4)) s15 rfl
    (by simp [hs15, clogSt, sv])
  set s16 := Function.update s15 (sv 4) (S (sv 4)) with hs16
  have e17 := runs_dropF (sv 2) (tripleWb 100 ^ c6K e) Sym.mark (S (sv 2)) s16 rfl
    (by simp [hs16, hs15, clogSt, hs14, hs13, hs12, hs11, hs10, hs9, sv])
  have X := WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq e2 (WP.W9comp.runs_seq e3
    (WP.W9comp.runs_seq e4 (WP.W9comp.runs_seq e5 (WP.W9comp.runs_seq e6
    (WP.W9comp.runs_seq e7 (WP.W9comp.runs_seq e8 (WP.W9comp.runs_seq e9
    (WP.W9comp.runs_seq e10 (WP.W9comp.runs_seq e11 (WP.W9comp.runs_seq e12
    (WP.W9comp.runs_seq e13 (WP.W9comp.runs_seq e14 (WP.W9comp.runs_seq e15
    (WP.W9comp.runs_seq e16 e17)))))))))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ h => h) ?_
  · funext x
    rcases x with j | j
    · simp [hs16, hs15, clogSt, hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4,
        hs3, hs2, hs1, sv]
    · fin_cases j <;> simp [hs16, hs15, clogSt, hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6,
        hs5, hs4, hs3, hs2, hs1, sv]
  · exact le_trans (le_of_eq (by ring)) (tProg_cost_le hq he)

end TProg

/-- The piece-loop test program (named stacks `Fin 2`). -/
def testProg (q : ℕ) : Prog (KLoc (Fin 2) PE) (fun _ => Sym) Reg :=
  .seq (tProg q 0)
  (.seq (pushMark (sv 5))
  (.seq (subN (.inl 0) (sv 3) (sv 5) (sv 16) (sv 17) (sv 18))
  (.seq (cmpN (.inl 1) (sv 5) (sv 8) (sv 9))
  (.seq (dropF (sv 5))
    (dropF (sv 3))))))

theorem closed_testProg (q : ℕ) : (testProg q).Closed :=
  ⟨closed_tProg q 0, closed_pushMark _, closed_subN _ _ _ _ _ _, closed_cmpN' _ _ _ _,
    closed_dropF _, closed_dropF _⟩

theorem test_runs {q : ℕ} (hq : 2 ≤ q) (e o : ℕ) (he : 35 ≤ e) (r0 r1 : List Sym)
    (hr0 : TermOK r0) (hr1 : TermOK r1) (S : KLoc (Fin 2) PE → List Sym)
    (hS0 : S (.inl 0) = natSyms e ++ r0) (hS1 : S (.inl 1) = natSyms o ++ r1) :
    Runs (testProg q) S S (fun r => r.2.2.2.2 = ordOf o (e - c6T q e))
      (tC q * (e + 1) ^ 3 + (1 + (20 * (bitLen e + bitLen (c6T q e) + 1) + (12 * bitLen o + 15 +
        ((2 * bitLen (e - c6T q e) + 2) + (2 * bitLen (c6T q e) + 2)))))) := by
  have hmk : ∀ x, TermOK (Sym.mark :: x) := termOK_mark
  have htle : c6T q e ≤ e := (C6Aux.c6T_lt hq he).2.le
  have h1 := tProg_runs hq (0 : Fin 2) e he r0 hr0 S hS0
  set T1 := Function.update S (sv 3) (natSyms (c6T q e) ++ Sym.mark :: S (sv 3)) with hT1
  have h2 := runs_pushMark (sv 5) T1
  rw [show T1 (sv 5) = S (sv 5) by simp [hT1, sv]] at h2
  set T2 := Function.update T1 (sv 5) (Sym.mark :: S (sv 5)) with hT2
  have h3 := runs_subN (x := .inl 0) (y := sv 3) (z := sv 5) (t1 := sv 16) (t2 := sv 17)
    (t3 := sv 18) (by decide) e (c6T q e) r0 (Sym.mark :: S (sv 3)) T2 hr0 (hmk _) htle
    (by simp [hT2, hT1, sv, hS0]) (by simp [hT2, hT1, sv])
  rw [show T2 (sv 5) = Sym.mark :: S (sv 5) by simp [hT2]] at h3
  set T3 := Function.update T2 (sv 5) (natSyms (e - c6T q e) ++ Sym.mark :: S (sv 5)) with hT3
  have h4 := runs_cmpN (x := .inl 1) (y := sv 5) (t1 := sv 8) (t2 := sv 9) (by decide) o
    (e - c6T q e) r1 (Sym.mark :: S (sv 5)) T3 hr1 (hmk _) (by simp [hT3, hT2, hT1, sv, hS1])
    (by simp [hT3])
  have h5 : ∀ v : Reg, ∃ w τ, Eval [] (.seq (dropF (sv 5)) (dropF (sv 3)) :
      Prog (KLoc (Fin 2) PE) (fun _ => Sym) Reg) ⟨v, T3⟩ ⟨(w, v.2), S⟩ τ ∧
      τ ≤ (2 * bitLen (e - c6T q e) + 2) + (2 * bitLen (c6T q e) + 2) := by
    intro v
    have d1 := dropF_eval_pres (sv 5) (e - c6T q e) Sym.mark (S (sv 5)) T3 rfl (by simp [hT3]) v
    have d2 := dropF_eval_pres (sv 3) (c6T q e) Sym.mark (S (sv 3))
      (Function.update T3 (sv 5) (S (sv 5))) rfl (by simp [hT3, hT2, hT1, sv])
      (some Sym.mark, v.2)
    refine ⟨some Sym.mark, _, (Eval.seq d1 d2).of_eq ?_ rfl, le_rfl⟩
    congr 1
    funext x
    rcases x with j | j <;> fin_cases j <;> simp [hT3, hT2, hT1, sv]
  exact WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2 (WP.W9comp.runs_seq h3
    (runs_seq_pres h4 h5 (fun _ _ h => h))))

/-- The constant of `C6PcTestStmt q`. -/
def testC (q : ℕ) : ℕ := tC q + 200

end AppC.C6PcAux

open AppC.C6PcAux NatArith in
/-- **`C6PcTestStmt q`, proved** (`q ≥ 2`): the program `AppC.C6PcAux.testProg q`, scratch `PE`,
registers `NatArith.Reg`, observation "the compare register is `lt`", constant `testC q`. -/
theorem c6PcTest_holds (q : ℕ) (hq : 2 ≤ q) : C6PcTestStmt q := by
  refine ⟨testC q, fun _ => ⟨PE, inferInstance, inferInstance, Reg, testProg q, inferInstance,
    inferInstance, closed_testProg q, fun r => decide (r.2.2.2.2 = Ordering.lt), ?_⟩⟩
  intro e o r0 r1 S he ho hr0 hr1 hS0 hS1
  refine WP.W9comp.runs_mono (test_runs hq e o he r0 r1 hr0 hr1 S hS0 hS1) (fun r hr => ?_) ?_
  · show decide (r.2.2.2.2 = Ordering.lt) = decide (o < e - c6T q e)
    rw [hr]
    simp only [ordOf_eq_lt_iff]
  · have hbe : bitLen e ≤ e := bitLen_le_self'' e
    have hbt : bitLen (c6T q e) ≤ e :=
      (bitLen_le_self'' _).trans (SubNLogN.Machine.AppC.C6Aux.c6T_lt hq he).2.le
    have hbl : bitLen (e - c6T q e) ≤ e := (bitLen_le_self'' _).trans (by omega)
    have hbo : bitLen o ≤ e := (bitLen_le_self'' o).trans ho
    have h3 : e + 1 ≤ (e + 1) ^ 3 := by
      calc e + 1 = (e + 1) ^ 1 := (pow_one _).symm
        _ ≤ (e + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hR : testC q * (e + 1) ^ 3 = tC q * (e + 1) ^ 3 + 200 * (e + 1) ^ 3 := by
      unfold testC; ring
    rw [hR]
    omega

end SubNLogN.Machine
