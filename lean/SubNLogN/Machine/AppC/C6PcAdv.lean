/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6PcBase

/-!
# Lemma A.8 piece advance (`Machine/AppC/C6PcAdv.lean`): `C6PcAdvStmt`

**Program** (`advProg`; named stacks `Fin 6`: `0` the offset `o`, `1`-`5` the counters
`j, R', q^o, G', B'`; scratch `PE`; registers `NatArith.Reg`): `L ← m^j` on a mark-floored scratch
stack (`pushMark`, `pushNat 1`, `powMulN` reading `j` from stack `1`), `Y ← o + L` (`addN`),
replace `o` by `Y` (`dropN`, `copyN`), drop `Y` and `L` with their floors, pop the five counters
(`dropN`). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Proved (no `sorry`).** `c6PcAdv_holds (q) (hq : 2 ≤ q) : C6PcAdvStmt q`, constant
`advC q = 300000 * (bitLen q + 1)`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

namespace AppC.C6PcAux

open NatArith

/-- The piece-advance program. -/
def advProg : Prog (KLoc (Fin 6) PE) (fun _ => Sym) Reg :=
  .seq (pushMark (sv 0))
  (.seq (pushNat (sv 0) 1)
  (.seq (powMulN (sv 0) (tripleM 100) (.inl 1) (sv 2) (sv 3) (sv 4) (sv 5) (sv 6) (sv 7) (sv 8))
  (.seq (pushMark (sv 1))
  (.seq (addN (.inl 0) (sv 0) (sv 1) (sv 9) (sv 10) (sv 11))
  (.seq (dropN (.inl 0))
  (.seq (copyN (sv 1) (.inl 0) (sv 12))
  (.seq (dropF (sv 1))
  (.seq (dropF (sv 0))
  (.seq (dropN (.inl 1))
  (.seq (dropN (.inl 2))
  (.seq (dropN (.inl 3))
  (.seq (dropN (.inl 4))
    (dropN (.inl 5))))))))))))))

theorem closed_advProg : advProg.Closed :=
  ⟨closed_pushMark _, closed_pushNat _ _, closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_pushMark _,
    closed_addN _ _ _ _ _ _, closed_dropN _, closed_copyN _ _ _, closed_dropF _, closed_dropF _,
    closed_dropN _, closed_dropN _, closed_dropN _, closed_dropN _, closed_dropN _⟩

/-- Cost of `advProg`. -/
def advCost (o j R' P G' B' : ℕ) : ℕ :=
  1 + ((bitLen 1 + 1) + (powCost (tripleM 100) 1 j + (1 + (20 * (bitLen o +
    bitLen (tripleM 100 ^ j) + 1) + ((2 * bitLen o + 4) + ((7 * bitLen (o + tripleM 100 ^ j) + 7) +
    ((2 * bitLen (o + tripleM 100 ^ j) + 2) + ((2 * bitLen (tripleM 100 ^ j) + 2) +
    ((2 * bitLen j + 4) + ((2 * bitLen R' + 4) + ((2 * bitLen P + 4) + ((2 * bitLen G' + 4) +
    (2 * bitLen B' + 4)))))))))))))

theorem adv_runs (o j R' P G' B' : ℕ) (r0 r1 r2 r3 r4 r5 : List Sym)
    (S : KLoc (Fin 6) PE → List Sym) (hr0 : TermOK r0) (hr1 : TermOK r1) (hr2 : TermOK r2)
    (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5)
    (hS0 : S (.inl 0) = natSyms o ++ r0) (hS1 : S (.inl 1) = natSyms j ++ r1)
    (hS2 : S (.inl 2) = natSyms R' ++ r2) (hS3 : S (.inl 3) = natSyms P ++ r3)
    (hS4 : S (.inl 4) = natSyms G' ++ r4) (hS5 : S (.inl 5) = natSyms B' ++ r5) :
    Runs advProg S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S (.inl 0) (natSyms (o + tripleM 100 ^ j) ++ r0))
        (.inl 1) r1) (.inl 2) r2) (.inl 3) r3) (.inl 4) r4) (.inl 5) r5)
      (fun _ => True) (advCost o j R' P G' B') := by
  have hmk : ∀ x, TermOK (Sym.mark :: x) := termOK_mark
  have e1 := runs_pushMark (sv 0) S
  set s1 := Function.update S (sv 0) (Sym.mark :: S (sv 0)) with hs1
  have e2 := runs_pushNat (sv 0) 1 s1
  have h1L : s1 (sv 0) = Sym.mark :: S (sv 0) := by simp [hs1]
  rw [h1L] at e2
  set s2 := Function.update s1 (sv 0) (natSyms 1 ++ Sym.mark :: S (sv 0)) with hs2
  have e3 := runs_powMulN (k := sv 0) (ns := .inl 1) (Kc := sv 2) (t := sv 3) (Q := sv 4)
    (Tdst := sv 5) (A := sv 6) (Bs := sv 7) (Acc := sv 8) (by decide) (tripleM 100)
    (by norm_num [tripleM]) 1 j (Sym.mark :: S (sv 0)) r1 s2 (hmk _) hr1 (by simp [hs2])
    (by simp [hs2, hs1, sv, hS1])
  rw [one_mul] at e3
  set s3 := Function.update s2 (sv 0) (natSyms (tripleM 100 ^ j) ++ Sym.mark :: S (sv 0))
    with hs3
  have e4 := runs_pushMark (sv 1) s3
  have h3Y : s3 (sv 1) = S (sv 1) := by simp [hs3, hs2, hs1, sv]
  rw [h3Y] at e4
  set s4 := Function.update s3 (sv 1) (Sym.mark :: S (sv 1)) with hs4
  have e5 := runs_addN (x := .inl 0) (y := sv 0) (z := sv 1) (t1 := sv 9) (t2 := sv 10)
    (t3 := sv 11) (by decide) o (tripleM 100 ^ j) r0 (Sym.mark :: S (sv 0)) s4 hr0 (hmk _)
    (by simp [hs4, hs3, hs2, hs1, sv, hS0]) (by simp [hs4, hs3, sv])
  have h4Y : s4 (sv 1) = Sym.mark :: S (sv 1) := by simp [hs4]
  rw [h4Y] at e5
  set s5 := Function.update s4 (sv 1) (natSyms (o + tripleM 100 ^ j) ++ Sym.mark :: S (sv 1))
    with hs5
  have e6 := runs_dropN (.inl 0) o r0 s5 hr0 (by simp [hs5, hs4, hs3, hs2, hs1, sv, hS0])
  set s6 := Function.update s5 (.inl 0) r0 with hs6
  have e7 := runs_copyN (src := sv 1) (dst := .inl 0) (tmp := sv 12) (by decide) (by decide)
    (by decide) (o + tripleM 100 ^ j) (Sym.mark :: S (sv 1)) s6 (hmk _) (by simp [hs6, hs5, sv])
  have h6o : s6 (.inl 0) = r0 := by simp [hs6]
  rw [h6o] at e7
  set s7 := Function.update s6 (.inl 0) (natSyms (o + tripleM 100 ^ j) ++ r0) with hs7
  have e8 := runs_dropF (sv 1) (o + tripleM 100 ^ j) Sym.mark (S (sv 1)) s7 rfl
    (by simp [hs7, hs6, hs5, sv])
  set s8 := Function.update s7 (sv 1) (S (sv 1)) with hs8
  have e9 := runs_dropF (sv 0) (tripleM 100 ^ j) Sym.mark (S (sv 0)) s8 rfl
    (by simp [hs8, hs7, hs6, hs5, hs4, hs3, sv])
  set s9 := Function.update s8 (sv 0) (S (sv 0)) with hs9
  have e10 := runs_dropN (.inl 1) j r1 s9 hr1
    (by simp [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv, hS1])
  set s10 := Function.update s9 (.inl 1) r1 with hs10
  have e11 := runs_dropN (.inl 2) R' r2 s10 hr2
    (by simp [hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv, hS2])
  set s11 := Function.update s10 (.inl 2) r2 with hs11
  have e12 := runs_dropN (.inl 3) P r3 s11 hr3
    (by simp [hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv, hS3])
  set s12 := Function.update s11 (.inl 3) r3 with hs12
  have e13 := runs_dropN (.inl 4) G' r4 s12 hr4
    (by simp [hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv, hS4])
  set s13 := Function.update s12 (.inl 4) r4 with hs13
  have e14 := runs_dropN (.inl 5) B' r5 s13 hr5
    (by simp [hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv, hS5])
  have X := WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq e2 (WP.W9comp.runs_seq e3
    (WP.W9comp.runs_seq e4 (WP.W9comp.runs_seq e5 (WP.W9comp.runs_seq e6
    (WP.W9comp.runs_seq e7 (WP.W9comp.runs_seq e8 (WP.W9comp.runs_seq e9
    (WP.W9comp.runs_seq e10 (WP.W9comp.runs_seq e11 (WP.W9comp.runs_seq e12
    (WP.W9comp.runs_seq e13 e14))))))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ h => h) (by unfold advCost; omega)
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, sv]

/-- The constant of `C6PcAdvStmt q`. -/
def advC (q : ℕ) : ℕ := 300000 * (bitLen q + 1)

theorem adv_cost_le {q : ℕ} (hq : 2 ≤ q) {e G B o : ℕ} (he : 35 ≤ e) (ho : o < e - c6T q e) :
    advCost o (c6PJ q e o) (c6Rp q e) (q ^ o) (c6PG q e G o) (c6PB q e B o) ≤
      advC q * (e + bitLen G + bitLen B + 1) ^ 3 := by
  have hL := c6PL_le ho
  have hJ : c6PJ q e o < c6PL q e o := c6PJ_lt
  have hLdef : tripleM 100 ^ c6PJ q e o = c6PL q e o := rfl
  have b0 : bitLen 1 ≤ 1 := bitLen_le_self'' 1
  have b1 : bitLen o ≤ e := (bitLen_le_self'' o).trans (by omega)
  have b2 : bitLen (c6PL q e o) ≤ e := (bitLen_le_self'' _).trans (by omega)
  have b3 : bitLen (o + c6PL q e o) ≤ e := (bitLen_le_self'' _).trans (by omega)
  have b4 : bitLen (c6PJ q e o) ≤ e := (bitLen_le_self'' _).trans (by omega)
  have b5 := bitLen_c6Rp_le hq he
  have b6 := bitLen_qpow_le (e := e) hq (by omega : o ≤ e)
  have b7 := bitLen_c6PG_le (G := G) hq ho
  have b8 := bitLen_c6PB_le (B := B) (o := o) (e := e) hq
  have hX1 : 1 ≤ e + bitLen G + bitLen B + 1 := by omega
  have hp : powCost (tripleM 100) 1 (c6PJ q e o) ≤
      105800 * (e + bitLen G + bitLen B + 1) ^ 3 := by
    unfold powCost
    have h1 : c6PJ q e o + 1 ≤ e + bitLen G + bitLen B + 1 := by omega
    have h2 : bitLen (1 * tripleM 100 ^ c6PJ q e o) + bitLen (tripleM 100) + 2 ≤
        23 * (e + bitLen G + bitLen B + 1) := by
      rw [one_mul, hLdef]
      have := bitLen_tripleM
      omega
    calc (c6PJ q e o + 1) *
          (200 * (bitLen (1 * tripleM 100 ^ c6PJ q e o) + bitLen (tripleM 100) + 2) ^ 2)
        ≤ (e + bitLen G + bitLen B + 1) * (200 * (23 * (e + bitLen G + bitLen B + 1)) ^ 2) :=
          Nat.mul_le_mul h1 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 2))
      _ = 105800 * (e + bitLen G + bitLen B + 1) ^ 3 := by ring
  have hW : e + bitLen G + bitLen B + 1 ≤ (e + bitLen G + bitLen B + 1) ^ 3 := by
    calc e + bitLen G + bitLen B + 1 = (e + bitLen G + bitLen B + 1) ^ 1 := (pow_one _).symm
      _ ≤ (e + bitLen G + bitLen B + 1) ^ 3 := Nat.pow_le_pow_right hX1 (by norm_num)
  have hZ : (e + 1) * bitLen q ≤ bitLen q * (e + bitLen G + bitLen B + 1) ^ 3 := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ ((show e + 1 ≤ e + bitLen G + bitLen B + 1 by omega).trans hW)
  have hRHS : advC q * (e + bitLen G + bitLen B + 1) ^ 3 =
      300000 * (bitLen q * (e + bitLen G + bitLen B + 1) ^ 3) +
        300000 * (e + bitLen G + bitLen B + 1) ^ 3 := by
    unfold advC; ring
  have e5 : (2 * e + 2) * bitLen q = 2 * ((e + 1) * bitLen q) := by ring
  have e7 : 2 * (e + 1) * bitLen q = 2 * ((e + 1) * bitLen q) := by ring
  rw [e5] at b5
  rw [e7] at b7
  unfold advCost
  rw [hLdef, hRHS]
  generalize (e + bitLen G + bitLen B + 1) ^ 3 = W at hp hW hZ ⊢
  generalize bitLen q * W = U at hZ ⊢
  generalize (e + 1) * bitLen q = Z at b5 b6 b7 b8 hZ
  omega

end AppC.C6PcAux

open AppC.C6PcAux NatArith in
/-- **`C6PcAdvStmt q`, proved** (`q ≥ 2`): the program `AppC.C6PcAux.advProg`, scratch `PE`,
registers `NatArith.Reg`, constant `advC q`. -/
theorem c6PcAdv_holds (q : ℕ) (hq : 2 ≤ q) : C6PcAdvStmt q := by
  refine ⟨advC q, fun _ => ⟨PE, inferInstance, inferInstance, Reg, advProg, inferInstance,
    inferInstance, closed_advProg, ?_⟩⟩
  intro e G B o r0 r1 r2 r3 r4 r5 S he _ _ ho hr0 hr1 hr2 hr3 hr4 hr5 hS0 hS1 hS2 hS3 hS4 hS5
  exact WP.W9comp.runs_mono (adv_runs o _ _ _ _ _ r0 r1 r2 r3 r4 r5 S hr0 hr1 hr2 hr3 hr4 hr5
    hS0 hS1 hS2 hS3 hS4 hS5) (fun _ _ => trivial) (adv_cost_le hq he ho)

end SubNLogN.Machine
