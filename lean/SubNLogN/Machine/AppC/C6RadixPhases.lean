/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6RadixSetup

/-!
# Lemma A.8 radix padding, part 5 (`Machine/AppC/C6RadixPhases.lean`): the parameter phases

The concrete stack layout `K6 = KLoc (Fin 6) (Fin 21)` of both kernels (`C6RadixPadStmt`,
`C6RadixUnpadStmt`), and the two parameter phases shared by them (exact-stack `RunsIn` facts):
* `preProg` (`runsIn_pre`): `n = 2^u` in unary on `xn`, from the binary `u` on stack `1`;
* `midProg` (`runsIn_mid`): from `n` on `xn` and `N` on `xN` (and the binary `G`, `B` on stacks
  `2`, `3`) the four block lengths `n·B`, `(N-n)·B`, `n·(G·(N·B))`, `(N-n)·(G·(N·B))` in unary on
  `xKa`, `xKb`, `xKc`, `xKd`; `xn`, `xN` and all temporaries are restored. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)
-/

namespace SubNLogN.Machine.AppC.C6RadixAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine.Calculus Computability

/-- Stacks of both kernels: six named stacks and 21 private ones. -/
abbrev K6 : Type := KLoc (Fin 6) (Fin 21)

/-- Named stacks: the array, the counters `u, G, B, w`, the `e` stack. -/
abbrev sA : K6 := .inl 0
abbrev sU : K6 := .inl 1
abbrev sG : K6 := .inl 2
abbrev sB : K6 := .inl 3
abbrev sW : K6 := .inl 4
abbrev sE : K6 := .inl 5
/-- Private stacks: pass temporaries, setup temporaries, unary values. -/
abbrev xAcc : K6 := .inr 0
abbrev xC1 : K6 := .inr 1
abbrev xC2 : K6 := .inr 2
abbrev xCw : K6 := .inr 3
abbrev xTmp : K6 := .inr 4
abbrev xTb : K6 := .inr 5
abbrev xT2 : K6 := .inr 6
abbrev xEc : K6 := .inr 7
abbrev xU : K6 := .inr 8
abbrev xn : K6 := .inr 9
abbrev xN : K6 := .inr 10
abbrev xD : K6 := .inr 11
abbrev xB : K6 := .inr 12
abbrev xG : K6 := .inr 13
abbrev xNB : K6 := .inr 14
abbrev xGNB : K6 := .inr 15
abbrev xKa : K6 := .inr 16
abbrev xKb : K6 := .inr 17
abbrev xKc : K6 := .inr 18
abbrev xKd : K6 := .inr 19
abbrev xW : K6 := .inr 20

/-! ## Phase 1: `n = 2^u` -/

/-- `n = 2^u` in unary on `xn` (above a new `mark`). -/
def preProg : SProg K6 :=
  .seq (toUnary sU xU xTb xTmp) (.seq (pow2 xU xn xC1 xTmp) (dropU xU))

theorem runsIn_pre {ρ : List (SProg K6)} (u : ℕ) {r1 : List Sym} (hr1 : TermOK r1)
    (S : K6 → List Sym) (hS : S sU = natSyms u ++ r1) :
    RunsIn ρ preProg S (Function.update S xn (ublk (2 ^ u) ++ Sym.mark :: S xn))
      (fun _ => True) (60 * (2 ^ u * 2 ^ u) + 25) := by
  have h := RunsIn.seq (runsIn_toUnary (ρ := ρ) (src := sU) (dst := xU) (tb := xTb)
      (tmp := xTmp) (by decide) (by decide) (by decide) (by decide) u hr1 S hS)
    (RunsIn.seq (runsIn_pow2 (ρ := ρ) (mU := xU) (mn := xn) (c := xC1) (tmp := xTmp)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) u
      (termOK_mark (S xU)) _ (by simp [Function.update_apply]))
    (runsIn_dropU (ρ := ρ) xU u (S xU) _ (by simp [Function.update_apply])))
  have hu : u < 2 ^ u := Nat.lt_two_pow_self
  have h1 : 1 ≤ 2 ^ u := Nat.one_le_two_pow
  have h2 : u * (9 * 2 ^ u + 18) ≤ 2 ^ u * (9 * 2 ^ u + 18) := Nat.mul_le_mul_right _ hu.le
  have h3 : 2 ^ u ≤ 2 ^ u * 2 ^ u := Nat.le_mul_of_pos_left _ (by omega)
  refine RunsIn.congr h ?_ (by nlinarith)
  funext x
  rcases x with i | i <;> fin_cases i <;> simp [Function.update_apply]

/-! ## Phase 3: the four block lengths -/

/-- From `n` (on `xn`) and `N` (on `xN`): `n·B`, `(N-n)·B`, `n·(G·(N·B))`, `(N-n)·(G·(N·B))` on
`xKa`, `xKb`, `xKc`, `xKd`; then `xn`, `xN` are dropped. -/
def midProg : SProg K6 :=
  .seq (subInto xN xn xD xC1 xTmp)
  (.seq (toUnary sB xB xTb xTmp)
  (.seq (mulInto xn xB xKa xC1 xTmp)
  (.seq (mulInto xD xB xKb xC1 xTmp)
  (.seq (toUnary sG xG xTb xTmp)
  (.seq (mulInto xN xB xNB xC1 xTmp)
  (.seq (mulInto xG xNB xGNB xC1 xTmp)
  (.seq (mulInto xn xGNB xKc xC1 xTmp)
  (.seq (mulInto xD xGNB xKd xC1 xTmp)
  (.seq (dropU xGNB) (.seq (dropU xNB) (.seq (dropU xG) (.seq (dropU xB)
  (.seq (dropU xD) (.seq (dropU xN) (dropU xn)))))))))))))))

/-- The product bounds used for the cost of `midProg`. -/
theorem mid_bounds {n N G B : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) (hG : 1 ≤ G) (hB : 1 ≤ B) :
    N * B ≤ N * N * G * B ∧ n * B ≤ N * N * G * B ∧ (N - n) * B ≤ N * N * G * B ∧
    G * (N * B) ≤ N * N * G * B ∧ n * (G * (N * B)) ≤ N * N * G * B ∧
    (N - n) * (G * (N * B)) ≤ N * N * G * B ∧ N ≤ N * N * G * B ∧ G ≤ N * N * G * B ∧
    B ≤ N * N * G * B := by
  have hN : 1 ≤ N := le_trans hn1 hnN
  have e1 : N * N * G * B = N * (G * (N * B)) := by ring
  have h1 : G * (N * B) ≤ N * N * G * B := by
    rw [e1]; exact Nat.le_mul_of_pos_left _ (by omega)
  have h2 : N * B ≤ G * (N * B) := Nat.le_mul_of_pos_left _ (by omega)
  have h3 : n * (G * (N * B)) ≤ N * N * G * B := by
    rw [e1]; exact Nat.mul_le_mul_right _ hnN
  have h4 : (N - n) * (G * (N * B)) ≤ N * N * G * B := by
    rw [e1]; exact Nat.mul_le_mul_right _ (Nat.sub_le N n)
  have h5 : n * B ≤ N * B := Nat.mul_le_mul_right _ hnN
  have h6 : (N - n) * B ≤ N * B := Nat.mul_le_mul_right _ (Nat.sub_le N n)
  have h7 : N ≤ N * B := Nat.le_mul_of_pos_right _ (by omega)
  have h8 : G ≤ G * (N * B) := Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have h9 : B ≤ N * B := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨by omega, by omega, by omega, h1, h3, h4, by omega, by omega, by omega⟩

theorem runsIn_mid {ρ : List (SProg K6)} (n N G B : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) (hG : 1 ≤ G)
    (hB : 1 ≤ B) {r2 r3 Rn RN : List Sym} (hr2 : TermOK r2) (hr3 : TermOK r3)
    (S : K6 → List Sym) (hn : S xn = ublk n ++ Sym.mark :: Rn)
    (hN : S xN = ublk N ++ Sym.mark :: RN) (hSG : S sG = natSyms G ++ r2)
    (hSB : S sB = natSyms B ++ r3) :
    RunsIn ρ midProg S
      (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S xn Rn) xN RN)
        xKa (ublk (n * B) ++ Sym.mark :: S xKa))
        xKb (ublk ((N - n) * B) ++ Sym.mark :: S xKb))
        xKc (ublk (n * (G * (N * B))) ++ Sym.mark :: S xKc))
        xKd (ublk ((N - n) * (G * (N * B))) ++ Sym.mark :: S xKd))
      (fun _ => True) (250 * (N * N * G * B) + 250) := by
  have h := RunsIn.seq (runsIn_subInto (ρ := ρ) (a := xN) (b := xn) (d := xD) (c := xC1)
      (tmp := xTmp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) N n (termOK_mark RN) (termOK_mark Rn) S hN hn)
    (RunsIn.seq (runsIn_toUnary (ρ := ρ) (src := sB) (dst := xB) (tb := xTb) (tmp := xTmp)
      (by decide) (by decide) (by decide) (by decide) B hr3 _
      (by simp [Function.update_apply, hSB]))
    (RunsIn.seq (runsIn_mulInto (ρ := ρ) (a := xn) (b := xB) (d := xKa) (c := xC1)
      (tmp := xTmp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) n B (termOK_mark Rn) (termOK_mark (S xB)) _
      (by simp [Function.update_apply, hn]) (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_mulInto (ρ := ρ) (a := xD) (b := xB) (d := xKb) (c := xC1)
      (tmp := xTmp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (N - n) B (termOK_mark (S xD)) (termOK_mark (S xB)) _
      (by simp [Function.update_apply]) (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_toUnary (ρ := ρ) (src := sG) (dst := xG) (tb := xTb) (tmp := xTmp)
      (by decide) (by decide) (by decide) (by decide) G hr2 _
      (by simp [Function.update_apply, hSG]))
    (RunsIn.seq (runsIn_mulInto (ρ := ρ) (a := xN) (b := xB) (d := xNB) (c := xC1)
      (tmp := xTmp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) N B (termOK_mark RN) (termOK_mark (S xB)) _
      (by simp [Function.update_apply, hN]) (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_mulInto (ρ := ρ) (a := xG) (b := xNB) (d := xGNB) (c := xC1)
      (tmp := xTmp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) G (N * B) (termOK_mark (S xG)) (termOK_mark (S xNB)) _
      (by simp [Function.update_apply]) (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_mulInto (ρ := ρ) (a := xn) (b := xGNB) (d := xKc) (c := xC1)
      (tmp := xTmp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) n (G * (N * B)) (termOK_mark Rn)
      (termOK_mark (S xGNB)) _ (by simp [Function.update_apply, hn])
      (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_mulInto (ρ := ρ) (a := xD) (b := xGNB) (d := xKd) (c := xC1)
      (tmp := xTmp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (N - n) (G * (N * B)) (termOK_mark (S xD))
      (termOK_mark (S xGNB)) _ (by simp [Function.update_apply])
      (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := ρ) xGNB (G * (N * B)) (S xGNB) _
      (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := ρ) xNB (N * B) (S xNB) _ (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := ρ) xG G (S xG) _ (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := ρ) xB B (S xB) _ (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := ρ) xD (N - n) (S xD) _ (by simp [Function.update_apply]))
    (RunsIn.seq (runsIn_dropU (ρ := ρ) xN N RN _ (by simp [Function.update_apply, hN]))
      (runsIn_dropU (ρ := ρ) xn n Rn _ (by simp [Function.update_apply, hn]))))))))))))))))
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := mid_bounds hn1 hnN hG hB
  have b10 : N - n ≤ N := Nat.sub_le N n
  refine RunsIn.congr h ?_ (by nlinarith)
  funext x
  rcases x with i | i <;> fin_cases i <;> simp [Function.update_apply]

end SubNLogN.Machine.AppC.C6RadixAux
