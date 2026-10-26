/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Desc

/-!
# Proposition A.7 leaf L5: the row size (`Machine/AppC/C5RowSize.lean`)

Proves `C5RowSizeStmt q m` (`Machine/AppC/C5Leaves.lean`, leaf L5) from a multiplication program and
a power-multiplication program on `natSyms` counters (`MulSpec`, `C5DescAux.PowMulSpec`: the shapes
of `NatArith.mulN` and `NatArith.powMulN`), with the mark-floor convention for the scratch stacks. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

**Program** (`rowProg`; named stacks `0` = target, `1..4` = `k, N1, G, B`; scratch `Fin 10`):
`m^k` on `mm` (`powMul` from `1`), `N1·G` on `p`, `N1·G·B` on `acc`, then `acc := acc·(q²)^(m^k)`,
`mark` and `acc` pushed on stack `0`, and `acc`, `p`, `mm` dropped. Since
`N1·G·B·(q²)^(m^k) = rowSize q m k N1 G B`, this is the contract. Cost: the two products are
`O(N1 G B)`, the powers `O((bitLen R + 1)³) = O(R)` (`R = rowSize`).

Helpers are in `SubNLogN.Machine.C5RowSizeAux`.
-/

namespace SubNLogN.Machine.C5RowSizeAux

open TMFw TMFw.Contracts SubNLogN.Machine.C5 SubNLogN.Machine.NatArith
  SubNLogN.Machine.C5DescAux

/-- **Interface of `NatArith.mulN`** on a stack type `K`: `prog x y z A Bs Acc T` pushes
`natSyms (a·b)` on `z` (`x`, `y` restored; `A, Bs, Acc, T` temporaries, restored), at cost
`O((bitLen a + 1)(bitLen a + bitLen b + 2))`. -/
structure MulSpec (K : Type) [DecidableEq K] where
  prog : K → K → K → K → K → K → K → Prog K (fun _ => Sym) Reg
  closed : ∀ x y z A Bs Acc T : K, (prog x y z A Bs Acc T).Closed
  cost : ℕ → ℕ → ℕ
  runs : ∀ {x y z A Bs Acc T : K}, [x, y, z, A, Bs, Acc, T].Nodup →
    ∀ (a b : ℕ) (rx ry : List Sym) (S : K → List Sym), TermOK rx → TermOK ry →
      S x = natSyms a ++ rx → S y = natSyms b ++ ry →
      Runs (prog x y z A Bs Acc T) S (Function.update S z (natSyms (a * b) ++ S z))
        (fun _ => True) (cost a b)
  cost_le : ∃ C : ℕ, ∀ a b : ℕ, cost a b ≤ C * ((bitLen a + 1) * (bitLen a + bitLen b + 2))

/-- Stacks of the kernel: five named stacks and ten scratch stacks. -/
abbrev RK : Type := KLoc (Fin 5) (Fin 10)

abbrev r0 : RK := .inl 0
abbrev rk : RK := .inl 1
abbrev rN1 : RK := .inl 2
abbrev rG : RK := .inl 3
abbrev rB : RK := .inl 4
/-- Scratch: `m^k`, `N1·G`, the accumulator. -/
abbrev rM : RK := .inr 0
abbrev rP : RK := .inr 1
abbrev rQ : RK := .inr 2
/-- Scratch temporaries. -/
abbrev rT0 : RK := .inr 3
abbrev rT1 : RK := .inr 4
abbrev rT2 : RK := .inr 5
abbrev rT3 : RK := .inr 6
abbrev rT4 : RK := .inr 7
abbrev rT5 : RK := .inr 8
abbrev rT6 : RK := .inr 9

/-- **The row-size program.** -/
def rowProg (PM : PowMulSpec RK) (MU : MulSpec RK) (q m : ℕ) : Prog RK (fun _ => Sym) Reg :=
  .seq (pushMark rM)
  (.seq (pushNat rM 1)
  (.seq (PM.prog rM m rk rT0 rT1 rT2 rT3 rT4 rT5 rT6)
  (.seq (pushMark rP)
  (.seq (MU.prog rN1 rG rP rT0 rT1 rT2 rT3)
  (.seq (pushMark rQ)
  (.seq (MU.prog rP rB rQ rT0 rT1 rT2 rT3)
  (.seq (PM.prog rQ (q ^ 2) rM rT0 rT1 rT2 rT3 rT4 rT5 rT6)
  (.seq (pushMark r0)
  (.seq (copyN rQ r0 rT0)
  (.seq (dropF rQ)
  (.seq (dropF rP)
    (dropF rM))))))))))))

theorem closed_rowProg (PM : PowMulSpec RK) (MU : MulSpec RK) (q m : ℕ) :
    (rowProg PM MU q m).Closed :=
  ⟨closed_pushMark _, closed_pushNat _ _, PM.closed _ _ _ _ _ _ _ _ _ _, closed_pushMark _,
    MU.closed _ _ _ _ _ _ _, closed_pushMark _, MU.closed _ _ _ _ _ _ _,
    PM.closed _ _ _ _ _ _ _ _ _ _, closed_pushMark _, closed_copyN _ _ _, closed_dropF _,
    closed_dropF _, closed_dropF _⟩

/-- A clean upper bound for the cost of `rowProg`. -/
def rowCostB (PM : PowMulSpec RK) (MU : MulSpec RK) (q m k N1 G B : ℕ) : ℕ :=
  PM.cost m 1 k + MU.cost N1 G + MU.cost (N1 * G) B + PM.cost (q ^ 2) (N1 * G * B) (1 * m ^ k) +
    20 * (bitLen (N1 * G * B * (q ^ 2) ^ (1 * m ^ k)) + bitLen (N1 * G) + bitLen (1 * m ^ k) + 10)

open WP.W9comp in
/-- **The row-size program**: with `k, N1, G, B` on stacks `1..4` (terminated), `rowProg` pushes
`mark` and `N1·G·B·(q²)^(1·m^k)` on stack `0` (arbitrary content); every other stack ends as it
started. -/
theorem runs_rowProg (PM : PowMulSpec RK) (MU : MulSpec RK) (q m k N1 G B : ℕ)
    (r1 r2 r3 r4 : List Sym) (S : RK → List Sym) (hq : 1 ≤ q) (hm : 1 ≤ m) (hr1 : TermOK r1)
    (hr2 : TermOK r2)
    (hr3 : TermOK r3) (hr4 : TermOK r4) (h1 : S rk = natSyms k ++ r1)
    (h2 : S rN1 = natSyms N1 ++ r2) (h3 : S rG = natSyms G ++ r3) (h4 : S rB = natSyms B ++ r4) :
    Runs (rowProg PM MU q m) S
      (Function.update S r0 (natSyms (N1 * G * B * (q ^ 2) ^ (1 * m ^ k)) ++ Sym.mark :: S r0))
      (fun _ => True) (rowCostB PM MU q m k N1 G B) := by
  have s1 := runs_pushMark rM S
  set S1 := Function.update S rM (Sym.mark :: S rM) with hS1
  have s2 := runs_pushNat rM 1 S1
  set S2 := Function.update S1 rM (natSyms 1 ++ S1 rM) with hS2
  have h3M : S2 rM = natSyms 1 ++ (Sym.mark :: S rM) := by
    rw [hS2, Function.update_self, hS1, Function.update_self]
  have h3k : S2 rk = natSyms k ++ r1 := by
    rw [hS2, Function.update_of_ne (by decide), hS1, Function.update_of_ne (by decide), h1]
  have s3 := PM.runs (k := rM) (ns := rk) (t1 := rT0) (t2 := rT1) (t3 := rT2) (t4 := rT3)
    (t5 := rT4) (t6 := rT5) (t7 := rT6) (by decide) m hm 1 k _ r1 S2 (termOK_mark _) hr1 h3M h3k
  set S3 := Function.update S2 rM (natSyms (1 * m ^ k) ++ Sym.mark :: S rM) with hS3
  have s4 := runs_pushMark rP S3
  set S4 := Function.update S3 rP (Sym.mark :: S3 rP) with hS4
  have h5N : S4 rN1 = natSyms N1 ++ r2 := by
    rw [hS4, Function.update_of_ne (by decide), hS3, Function.update_of_ne (by decide), hS2,
      Function.update_of_ne (by decide), hS1, Function.update_of_ne (by decide), h2]
  have h5G : S4 rG = natSyms G ++ r3 := by
    rw [hS4, Function.update_of_ne (by decide), hS3, Function.update_of_ne (by decide), hS2,
      Function.update_of_ne (by decide), hS1, Function.update_of_ne (by decide), h3]
  have s5 := MU.runs (x := rN1) (y := rG) (z := rP) (A := rT0) (Bs := rT1) (Acc := rT2) (T := rT3)
    (by decide) N1 G r2 r3 S4 hr2 hr3 h5N h5G
  set S5 := Function.update S4 rP (natSyms (N1 * G) ++ S4 rP) with hS5
  have s6 := runs_pushMark rQ S5
  set S6 := Function.update S5 rQ (Sym.mark :: S5 rQ) with hS6
  have h7P : S6 rP = natSyms (N1 * G) ++ (Sym.mark :: S rP) := by
    rw [hS6, Function.update_of_ne (by decide), hS5, Function.update_self, hS4,
      Function.update_self, hS3, Function.update_of_ne (by decide), hS2,
      Function.update_of_ne (by decide), hS1, Function.update_of_ne (by decide)]
  have h7B : S6 rB = natSyms B ++ r4 := by
    rw [hS6, Function.update_of_ne (by decide), hS5, Function.update_of_ne (by decide), hS4,
      Function.update_of_ne (by decide), hS3, Function.update_of_ne (by decide), hS2,
      Function.update_of_ne (by decide), hS1, Function.update_of_ne (by decide), h4]
  have s7 := MU.runs (x := rP) (y := rB) (z := rQ) (A := rT0) (Bs := rT1) (Acc := rT2) (T := rT3)
    (by decide) (N1 * G) B _ r4 S6 (termOK_mark _) hr4 h7P h7B
  set S7 := Function.update S6 rQ (natSyms (N1 * G * B) ++ S6 rQ) with hS7
  have h8Q : S7 rQ = natSyms (N1 * G * B) ++ (Sym.mark :: S rQ) := by
    rw [hS7, Function.update_self, hS6, Function.update_self, hS5,
      Function.update_of_ne (by decide), hS4, Function.update_of_ne (by decide), hS3,
      Function.update_of_ne (by decide), hS2, Function.update_of_ne (by decide), hS1,
      Function.update_of_ne (by decide)]
  have h8M : S7 rM = natSyms (1 * m ^ k) ++ (Sym.mark :: S rM) := by
    rw [hS7, Function.update_of_ne (by decide), hS6, Function.update_of_ne (by decide), hS5,
      Function.update_of_ne (by decide), hS4, Function.update_of_ne (by decide), hS3,
      Function.update_self]
  have s8 := PM.runs (k := rQ) (ns := rM) (t1 := rT0) (t2 := rT1) (t3 := rT2) (t4 := rT3)
    (t5 := rT4) (t6 := rT5) (t7 := rT6) (by decide) (q ^ 2) (Nat.one_le_pow _ _ hq) (N1 * G * B)
    (1 * m ^ k) _ _ S7
    (termOK_mark _) (termOK_mark _) h8Q h8M
  set V := N1 * G * B * (q ^ 2) ^ (1 * m ^ k) with hV
  set S8 := Function.update S7 rQ (natSyms V ++ Sym.mark :: S rQ) with hS8
  have s9 := runs_pushMark r0 S8
  set S9 := Function.update S8 r0 (Sym.mark :: S8 r0) with hS9
  have h10 : S9 rQ = natSyms V ++ (Sym.mark :: S rQ) := by
    rw [hS9, Function.update_of_ne (by decide), hS8, Function.update_self]
  have s10 := runs_copyN (src := rQ) (dst := r0) (tmp := rT0) (by decide) (by decide) (by decide)
    V _ S9 (termOK_mark _) h10
  set S10 := Function.update S9 r0 (natSyms V ++ S9 r0) with hS10
  have h11 : S10 rQ = natSyms V ++ Sym.mark :: S rQ := by
    rw [hS10, Function.update_of_ne (by decide), h10]
  have s11 := runs_dropF rQ V Sym.mark (S rQ) S10 rfl h11
  set S11 := Function.update S10 rQ (S rQ) with hS11
  have h12 : S11 rP = natSyms (N1 * G) ++ Sym.mark :: S rP := by
    rw [hS11, Function.update_of_ne (by decide), hS10, Function.update_of_ne (by decide), hS9,
      Function.update_of_ne (by decide), hS8, Function.update_of_ne (by decide), hS7,
      Function.update_of_ne (by decide), h7P]
  have s12 := runs_dropF rP (N1 * G) Sym.mark (S rP) S11 rfl h12
  set S12 := Function.update S11 rP (S rP) with hS12
  have h13 : S12 rM = natSyms (1 * m ^ k) ++ Sym.mark :: S rM := by
    rw [hS12, Function.update_of_ne (by decide), hS11, Function.update_of_ne (by decide), hS10,
      Function.update_of_ne (by decide), hS9, Function.update_of_ne (by decide), hS8,
      Function.update_of_ne (by decide), h8M]
  have s13 := runs_dropF rM (1 * m ^ k) Sym.mark (S rM) S12 rfl h13
  have r := runs_seq s1 (runs_seq s2 (runs_seq s3 (runs_seq s4 (runs_seq s5 (runs_seq s6
    (runs_seq s7 (runs_seq s8 (runs_seq s9 (runs_seq s10 (runs_seq s11 (runs_seq s12 s13)))))))))))
  refine runs_mono (runs_congr r ?_) (fun _ h => h) ?_
  · funext z
    simp only [hS12, hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply]
    by_cases e1 : z = rM
    · subst e1; simp
    · by_cases e2 : z = rP
      · subst e2; simp
      · by_cases e3 : z = rQ
        · subst e3; simp
        · by_cases e4 : z = r0
          · subst e4; simp
          · simp [e1, e2, e3, e4]
  · have hb1 : bitLen 1 = 1 := rfl
    unfold rowCostB
    rw [← hV]
    omega

/-! ## Cost -/

theorem succ_cube_le (s : ℕ) : (s + 1) ^ 3 ≤ 64 * 2 ^ s := by
  induction s with
  | zero => norm_num
  | succ s ih =>
    have h1 := succ_sq_le_eight_pow s
    have h2 : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
    have h3 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have e1 : (s + 1 + 1) ^ 3 = (s + 1) ^ 3 + 3 * (s + 1) ^ 2 + 3 * (s + 1) + 1 := by ring
    have e2 : 64 * 2 ^ (s + 1) = 64 * 2 ^ s + 64 * 2 ^ s := by ring
    rw [e1, e2]
    omega

/-- `(bitLen y + 1)³ ≤ 128 y` for `y ≥ 1`. -/
theorem bitLen_succ_cube_le {y : ℕ} (hy : 1 ≤ y) : (bitLen y + 1) ^ 3 ≤ 128 * y := by
  rw [bitLen_eq_size]
  have hs : 0 < Nat.size y := Nat.size_pos.2 (by omega)
  have h2 : 2 ^ (Nat.size y - 1) ≤ y := Nat.lt_size.1 (by omega)
  have h3 := succ_cube_le (Nat.size y)
  have e : 64 * 2 ^ Nat.size y = 128 * 2 ^ (Nat.size y - 1) := by
    obtain ⟨t, ht⟩ : ∃ t, Nat.size y = t + 1 := ⟨Nat.size y - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, pow_succ]
    ring
  omega

/-- The multiplication cost shape is `O(a b)`. -/
theorem mulCost_arith {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (bitLen a + 1) * (bitLen a + bitLen b + 2) ≤ 20 * (a * b) := by
  have h1 := bitLen_succ_sq_le ha
  have h2 : bitLen a + 1 ≤ 2 * a := by have := bitLen_le_self a; omega
  have h3 : bitLen b + 1 ≤ 2 * b := by have := bitLen_le_self b; omega
  have e : (bitLen a + 1) * (bitLen a + bitLen b + 2) =
      (bitLen a + 1) ^ 2 + (bitLen a + 1) * (bitLen b + 1) := by ring
  have h4 : (bitLen a + 1) * (bitLen b + 1) ≤ 4 * (a * b) :=
    calc (bitLen a + 1) * (bitLen b + 1) ≤ (2 * a) * (2 * b) := Nat.mul_le_mul h2 h3
      _ = 4 * (a * b) := by ring
  have h5 : 16 * a ≤ 16 * (a * b) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hb)
  rw [e]
  omega

/-- `N1·G·B·(q²)^(1·m^k) = rowSize q m k N1 G B`. -/
theorem rowVal_eq (q m k N1 G B : ℕ) :
    N1 * G * B * (q ^ 2) ^ (1 * m ^ k) = rowSize q m k N1 G B := by
  rw [one_mul, ← pow_mul, mul_comm 2 (m ^ k), pow_mul]
  unfold rowSize
  ring

/-- **The cost bound** `rowCostB ≤ (16 C₁ + 40 C₂ + 128 C₄ + 200)·(rowSize + 1)`. -/
theorem rowCostB_le (PM : PowMulSpec RK) (MU : MulSpec RK) {q m C1 C2 C4 : ℕ} (hq : 2 ≤ q)
    (hm : 2 ≤ m) (hC1 : ∀ a n, PM.cost m a n ≤ C1 * ((n + 1) * (bitLen (a * m ^ n) + 1) ^ 2))
    (hC2 : ∀ a b, MU.cost a b ≤ C2 * ((bitLen a + 1) * (bitLen a + bitLen b + 2)))
    (hC4 : ∀ a n, PM.cost (q ^ 2) a n ≤ C4 * ((n + 1) * (bitLen (a * (q ^ 2) ^ n) + 1) ^ 2))
    {k N1 G B : ℕ} (hN1 : 1 ≤ N1) (hG : 1 ≤ G) (hB : 1 ≤ B) :
    rowCostB PM MU q m k N1 G B ≤
      (16 * C1 + 40 * C2 + 128 * C4 + 200) * (rowSize q m k N1 G B + 1) := by
  have hR := rowVal_eq q m k N1 G B
  have hMX : m ^ k ≤ q ^ m ^ k := (lt_pow_of_two_le hq _).le
  have hX1 : 0 < q ^ m ^ k := pow_pos (by omega) _
  have hM1 : 1 ≤ m ^ k := Nat.one_le_pow _ _ (by omega)
  have hRe : rowSize q m k N1 G B = N1 * G * B * (q ^ m ^ k * q ^ m ^ k) := by
    unfold rowSize; ring
  have hNGB : 0 < N1 * G * B := Nat.mul_pos (Nat.mul_pos hN1 hG) hB
  have hXX : q ^ m ^ k * q ^ m ^ k ≤ rowSize q m k N1 G B := by
    rw [hRe]; exact Nat.le_mul_of_pos_left _ hNGB
  have hX : q ^ m ^ k ≤ q ^ m ^ k * q ^ m ^ k := Nat.le_mul_of_pos_left _ hX1
  have hNGBR : N1 * G * B ≤ rowSize q m k N1 G B := by
    rw [hRe]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hX1 hX1)
  have hNG : N1 * G ≤ N1 * G * B := Nat.le_mul_of_pos_right _ hB
  have hR1 : 1 ≤ rowSize q m k N1 G B := le_trans hNGB hNGBR
  have p1 : PM.cost m 1 k ≤ 16 * C1 * rowSize q m k N1 G B := by
    have h1 := hC1 1 k
    rw [one_mul] at h1
    have h2 := bitLen_succ_sq_le hM1
    have hk : k + 1 ≤ m ^ k :=
      le_trans (Nat.lt_two_pow_self (n := k)) (Nat.pow_le_pow_left hm k)
    have h3 : m ^ k * m ^ k ≤ rowSize q m k N1 G B := le_trans (Nat.mul_le_mul hMX hMX) hXX
    calc PM.cost m 1 k ≤ C1 * ((k + 1) * (bitLen (m ^ k) + 1) ^ 2) := h1
      _ ≤ C1 * (m ^ k * (16 * m ^ k)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hk h2)
      _ = 16 * C1 * (m ^ k * m ^ k) := by ring
      _ ≤ 16 * C1 * rowSize q m k N1 G B := Nat.mul_le_mul_left _ h3
  have p2 : MU.cost N1 G ≤ 20 * C2 * rowSize q m k N1 G B :=
    calc MU.cost N1 G ≤ C2 * ((bitLen N1 + 1) * (bitLen N1 + bitLen G + 2)) := hC2 N1 G
      _ ≤ C2 * (20 * (N1 * G)) := Nat.mul_le_mul_left _ (mulCost_arith hN1 hG)
      _ = 20 * C2 * (N1 * G) := by ring
      _ ≤ 20 * C2 * rowSize q m k N1 G B := Nat.mul_le_mul_left _ (le_trans hNG hNGBR)
  have p3 : MU.cost (N1 * G) B ≤ 20 * C2 * rowSize q m k N1 G B :=
    calc MU.cost (N1 * G) B ≤ C2 * ((bitLen (N1 * G) + 1) * (bitLen (N1 * G) + bitLen B + 2)) :=
          hC2 _ _
      _ ≤ C2 * (20 * (N1 * G * B)) :=
          Nat.mul_le_mul_left _ (mulCost_arith (Nat.mul_pos hN1 hG) hB)
      _ = 20 * C2 * (N1 * G * B) := by ring
      _ ≤ 20 * C2 * rowSize q m k N1 G B := Nat.mul_le_mul_left _ hNGBR
  have p4 : PM.cost (q ^ 2) (N1 * G * B) (1 * m ^ k) ≤ 128 * C4 * rowSize q m k N1 G B := by
    have h1 := hC4 (N1 * G * B) (1 * m ^ k)
    rw [hR, one_mul] at h1
    have h2 : 2 ^ m ^ k ≤ rowSize q m k N1 G B :=
      le_trans (Nat.pow_le_pow_left hq _) (le_trans hX hXX)
    have h3 : m ^ k < bitLen (rowSize q m k N1 G B) := by
      rw [bitLen_eq_size]; exact Nat.lt_size.2 h2
    have h4 := bitLen_succ_cube_le hR1
    have h5 : (m ^ k + 1) * (bitLen (rowSize q m k N1 G B) + 1) ^ 2 ≤
        (bitLen (rowSize q m k N1 G B) + 1) ^ 3 := by
      rw [pow_succ (bitLen (rowSize q m k N1 G B) + 1) 2, mul_comm]
      exact Nat.mul_le_mul_left _ (by omega)
    calc PM.cost (q ^ 2) (N1 * G * B) (1 * m ^ k) ≤
        C4 * ((m ^ k + 1) * (bitLen (rowSize q m k N1 G B) + 1) ^ 2) := by
          rw [one_mul]; exact h1
      _ ≤ C4 * (128 * rowSize q m k N1 G B) := Nat.mul_le_mul_left _ (le_trans h5 h4)
      _ = 128 * C4 * rowSize q m k N1 G B := by ring
  have t1 : bitLen (N1 * G * B * (q ^ 2) ^ (1 * m ^ k)) ≤ rowSize q m k N1 G B := by
    rw [hR]; exact bitLen_le_self _
  have t2 : bitLen (N1 * G) ≤ rowSize q m k N1 G B :=
    le_trans (bitLen_le_self _) (le_trans hNG hNGBR)
  have t3 : bitLen (1 * m ^ k) ≤ rowSize q m k N1 G B := by
    rw [one_mul]; exact le_trans (bitLen_le_self _) (le_trans hMX (le_trans hX hXX))
  have hexp : (16 * C1 + 40 * C2 + 128 * C4 + 200) * (rowSize q m k N1 G B + 1) =
      16 * C1 * rowSize q m k N1 G B + 20 * C2 * rowSize q m k N1 G B +
        20 * C2 * rowSize q m k N1 G B + 128 * C4 * rowSize q m k N1 G B +
        (16 * C1 + 40 * C2 + 128 * C4) + 200 * rowSize q m k N1 G B + 200 := by ring
  rw [hexp]
  unfold rowCostB
  omega

/-- **`C5RowSizeStmt` from multiplication and power-multiplication programs.** -/
theorem c5RowSize_of_specs (PM : PowMulSpec RK) (MU : MulSpec RK) (q m : ℕ) (hq : 2 ≤ q)
    (hm : 2 ≤ m) : C5RowSizeStmt q m := by
  obtain ⟨C1, hC1⟩ := PM.cost_le m
  obtain ⟨C2, hC2⟩ := MU.cost_le
  obtain ⟨C4, hC4⟩ := PM.cost_le (q ^ 2)
  refine ⟨16 * C1 + 40 * C2 + 128 * C4 + 200, fun _ => ⟨Fin 10, inferInstance, inferInstance,
    Reg, rowProg PM MU q m, inferInstance, inferInstance, closed_rowProg PM MU q m, ?_⟩⟩
  intro k N1 G B r1 r2 r3 r4 S hN1 hG hB hr1 hr2 hr3 hr4 h1 h2 h3 h4
  have r := runs_rowProg PM MU q m k N1 G B r1 r2 r3 r4 S (by omega) (by omega) hr1 hr2 hr3 hr4
    h1 h2 h3 h4
  rw [rowVal_eq] at r
  exact WP.W9comp.runs_mono r (fun _ h => h) (rowCostB_le PM MU hq hm hC1 hC2 hC4 hN1 hG hB)

/-! ## Instantiation with `NatArith.mulN` and `NatArith.powMulN` -/

/-- `NatArith.mulN` as a `MulSpec`. -/
noncomputable def natArithMul (K : Type) [DecidableEq K] : MulSpec K where
  prog := mulN
  closed := closed_mulN
  cost := mulCost
  runs := fun h a b rx ry S hrx hry hx hy => runs_mulN h a b rx ry S hrx hry hx hy
  cost_le := ⟨100, fun a b => le_of_eq (by unfold mulCost; ring)⟩

end SubNLogN.Machine.C5RowSizeAux

namespace SubNLogN.Machine.C5

/-- **Leaf L5 holds** (`c5RowSize_holds`): for `q ≥ 2` and `m ≥ 2`, `C5RowSizeStmt q m`, by
`rowProg` with `NatArith.mulN` and `NatArith.powMulN`. -/
theorem c5RowSize_holds {q m : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m) : C5RowSizeStmt q m :=
  C5RowSizeAux.c5RowSize_of_specs (C5DescAux.natArithPowMul _) (C5RowSizeAux.natArithMul _) q m
    hq hm

end SubNLogN.Machine.C5
