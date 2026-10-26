/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Leaves
import SubNLogN.Machine.AppC.C5StreamArith

/-!
# Proposition A.7 leaf L4: the child descriptor (`Machine/AppC/C5Desc.lean`)

Proves `C5DescStmt q m i j` (`Machine/AppC/C5Leaves.lean`, leaf L4) from a power-multiplication
program on `natSyms` counters (`PowMulSpec`: `a ↦ a·c^n`, `n` read from a counter stack, the shape
of `NatArith.powMulN`). The kernel uses the mark-floor convention of `NatArith`: every scratch stack
first receives a `mark`, the numbers are computed above it, and `dropF` restores the old (arbitrary)
content, so no cleanliness of the scratch is assumed. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

**Program** (`descProg`; named stacks `0..3` = `k, N1, G, B`; scratch `Fin 11`):
1. `1` on `one`; `k - 1` on `km1` (`subN`); `mark` and `k - 1` on stack `0`;
2. `b = m^(k-1)` on `bb` (`powMul` from `1` with `c = m`, `n = k - 1`);
3. for `(X, e) ∈ {(1, i), (2, (m-1-i)+j), (3, m-1-j)}`: `acc := x`, `acc := x·(q^e)^b`, then `mark`
   and `acc` on `X`, and `acc` dropped (`descPart`);
4. `bb`, `km1`, `one` dropped.
Then `x·(q^e)^b` is `cN1`, `cG`, `cB` (`b = m^(k-1)`). The cost is `O((b+1)(bitLen(x q^{eb})+1)²)`
per part, which is `O(rowSize)` because `(e+1)b ≤ 2m^k`.

Helpers are in `SubNLogN.Machine.C5DescAux`.
-/

namespace SubNLogN.Machine.C5DescAux

open TMFw TMFw.Contracts SubNLogN.Machine.C5 SubNLogN.Machine.NatArith

/-! ## Interface of the power-multiplication program -/

/-- **Interface of `NatArith.powMulN`** on a stack type `K`: `prog k c ns t₁ … t₇` replaces
`natSyms a` on `k` by `natSyms (a·c^n)` for `c ≥ 1` (`n` read from the counter `ns`, restored;
`t₁ … t₇` temporaries with arbitrary content, restored), and its cost is
`O((n+1)(bitLen(a c^n)+1)²)` for each fixed `c`. Instantiated by `natArithPowMul`. -/
structure PowMulSpec (K : Type) [DecidableEq K] where
  prog : K → ℕ → K → K → K → K → K → K → K → K → Prog K (fun _ => Sym) Reg
  closed : ∀ (k : K) (c : ℕ) (ns t1 t2 t3 t4 t5 t6 t7 : K),
    (prog k c ns t1 t2 t3 t4 t5 t6 t7).Closed
  cost : ℕ → ℕ → ℕ → ℕ
  runs : ∀ {k ns t1 t2 t3 t4 t5 t6 t7 : K}, [k, ns, t1, t2, t3, t4, t5, t6, t7].Nodup →
    ∀ (c : ℕ), 1 ≤ c → ∀ (a n : ℕ) (rk rn : List Sym) (S : K → List Sym), TermOK rk → TermOK rn →
      S k = natSyms a ++ rk → S ns = natSyms n ++ rn →
      Runs (prog k c ns t1 t2 t3 t4 t5 t6 t7) S (Function.update S k (natSyms (a * c ^ n) ++ rk))
        (fun _ => True) (cost c a n)
  cost_le : ∀ c : ℕ, ∃ C : ℕ, ∀ a n : ℕ, cost c a n ≤ C * ((n + 1) * (bitLen (a * c ^ n) + 1) ^ 2)

/-! ## Stacks -/

/-- Stacks of the kernel: the four named counters and eleven scratch stacks. -/
abbrev DK : Type := KLoc (Fin 4) (Fin 11)

/-- Named stacks. -/
abbrev sK : DK := .inl 0
abbrev sN1 : DK := .inl 1
abbrev sG : DK := .inl 2
abbrev sB : DK := .inl 3
/-- Scratch: the constant `1`, the counter `k - 1`, `b = m^(k-1)`, the accumulator. -/
abbrev sOne : DK := .inr 0
abbrev sKm1 : DK := .inr 1
abbrev sBb : DK := .inr 2
abbrev sAcc : DK := .inr 3
/-- Scratch temporaries. -/
abbrev sT0 : DK := .inr 4
abbrev sT1 : DK := .inr 5
abbrev sT2 : DK := .inr 6
abbrev sT3 : DK := .inr 7
abbrev sT4 : DK := .inr 8
abbrev sT5 : DK := .inr 9
abbrev sT6 : DK := .inr 10

/-! ## The program -/

/-- One descriptor part: `X ← x·c^b` pushed (with a `mark`) on `X`, using the accumulator. -/
def descPart (PM : PowMulSpec DK) (X : DK) (c : ℕ) : Prog DK (fun _ => Sym) Reg :=
  .seq (pushMark sAcc)
  (.seq (copyN X sAcc sT0)
  (.seq (PM.prog sAcc c sBb sT0 sT1 sT2 sT3 sT4 sT5 sT6)
  (.seq (pushMark X)
  (.seq (copyN sAcc X sT0)
    (dropF sAcc)))))

/-- The initialization: `1`, `k - 1` (also pushed on stack `0`), `b = m^(k-1)`. -/
def descInit (PM : PowMulSpec DK) (m : ℕ) : Prog DK (fun _ => Sym) Reg :=
  .seq (pushMark sOne)
  (.seq (pushNat sOne 1)
  (.seq (pushMark sKm1)
  (.seq (subN sK sOne sKm1 sT0 sT1 sT2)
  (.seq (pushMark sK)
  (.seq (copyN sKm1 sK sT0)
  (.seq (pushMark sBb)
  (.seq (pushNat sBb 1)
    (PM.prog sBb m sKm1 sT0 sT1 sT2 sT3 sT4 sT5 sT6))))))))

/-- **The child-descriptor program.** -/
def descProg (PM : PowMulSpec DK) (q m i j : ℕ) : Prog DK (fun _ => Sym) Reg :=
  .seq (descInit PM m)
  (.seq (descPart PM sN1 (q ^ i))
  (.seq (descPart PM sG (q ^ (m - 1 - i + j)))
  (.seq (descPart PM sB (q ^ (m - 1 - j)))
  (.seq (dropF sBb)
  (.seq (dropF sKm1)
    (dropF sOne))))))

theorem closed_descPart (PM : PowMulSpec DK) (X : DK) (c : ℕ) : (descPart PM X c).Closed :=
  ⟨closed_pushMark _, closed_copyN _ _ _, PM.closed _ _ _ _ _ _ _ _ _ _, closed_pushMark _,
    closed_copyN _ _ _, closed_dropF _⟩

theorem closed_descInit (PM : PowMulSpec DK) (m : ℕ) : (descInit PM m).Closed :=
  ⟨closed_pushMark _, closed_pushNat _ _, closed_pushMark _, closed_subN _ _ _ _ _ _,
    closed_pushMark _, closed_copyN _ _ _, closed_pushMark _, closed_pushNat _ _,
    PM.closed _ _ _ _ _ _ _ _ _ _⟩

theorem closed_descProg (PM : PowMulSpec DK) (q m i j : ℕ) : (descProg PM q m i j).Closed :=
  ⟨closed_descInit PM m, closed_descPart PM _ _, closed_descPart PM _ _, closed_descPart PM _ _,
    closed_dropF _, closed_dropF _, closed_dropF _⟩

/-! ## Specifications of the parts -/

open WP.W9comp in
/-- **One descriptor part** on the named stack `X = .inl t`: if `X` holds `natSyms x ++ rX` and
`bb` holds `natSyms b ++ rb` (terminated), `descPart X c` pushes `mark` and `x·c^b` on `X`; every
other stack (accumulator and temporaries included) ends as it started. -/
theorem runs_descPart (PM : PowMulSpec DK) (t : Fin 4) (c x b : ℕ) (rX rb : List Sym)
    (S : DK → List Sym) (hc : 1 ≤ c) (hrX : TermOK rX) (hrb : TermOK rb) (hSX : S (.inl t) = natSyms x ++ rX)
    (hSb : S sBb = natSyms b ++ rb) :
    Runs (descPart PM (.inl t) c) S
      (Function.update S (.inl t) (natSyms (x * c ^ b) ++ Sym.mark :: S (.inl t)))
      (fun _ => True)
      (1 + ((7 * bitLen x + 7) + (PM.cost c x b + (1 + ((7 * bitLen (x * c ^ b) + 7) +
        (2 * bitLen (x * c ^ b) + 2)))))) := by
  have hXA : (Sum.inl t : DK) ≠ sAcc := Sum.inl_ne_inr
  have hXT : (Sum.inl t : DK) ≠ sT0 := Sum.inl_ne_inr
  have hXb : (Sum.inl t : DK) ≠ sBb := Sum.inl_ne_inr
  have hnd : [sAcc, sBb, sT0, sT1, sT2, sT3, sT4, sT5, sT6].Nodup := by decide
  have r1 := runs_pushMark sAcc S
  set S1 := Function.update S sAcc (Sym.mark :: S sAcc) with hS1
  have h2X : S1 (.inl t) = natSyms x ++ rX := by rw [hS1, Function.update_of_ne hXA, hSX]
  have r2 := runs_copyN (src := (.inl t : DK)) (dst := sAcc) (tmp := sT0) hXA hXT (by decide) x rX
    S1 hrX h2X
  set S2 := Function.update S1 sAcc (natSyms x ++ S1 sAcc) with hS2
  have h3A : S2 sAcc = natSyms x ++ (Sym.mark :: S sAcc) := by
    rw [hS2, Function.update_self, hS1, Function.update_self]
  have h3b : S2 sBb = natSyms b ++ rb := by
    rw [hS2, Function.update_of_ne (by decide), hS1, Function.update_of_ne (by decide), hSb]
  have r3 := PM.runs hnd c hc x b (Sym.mark :: S sAcc) rb S2 (termOK_mark _) hrb h3A h3b
  set S3 := Function.update S2 sAcc (natSyms (x * c ^ b) ++ Sym.mark :: S sAcc) with hS3
  have r4 := runs_pushMark (Sum.inl t : DK) S3
  set S4 := Function.update S3 (.inl t) (Sym.mark :: S3 (.inl t)) with hS4
  have h5A : S4 sAcc = natSyms (x * c ^ b) ++ (Sym.mark :: S sAcc) := by
    rw [hS4, Function.update_of_ne hXA.symm, hS3, Function.update_self]
  have r5 := runs_copyN (src := sAcc) (dst := (.inl t : DK)) (tmp := sT0) hXA.symm (by decide)
    hXT _ _ S4 (termOK_mark _) h5A
  set S5 := Function.update S4 (.inl t) (natSyms (x * c ^ b) ++ S4 (.inl t)) with hS5
  have h6A : S5 sAcc = natSyms (x * c ^ b) ++ Sym.mark :: S sAcc := by
    rw [hS5, Function.update_of_ne hXA.symm, h5A]
  have r6 := runs_dropF sAcc (x * c ^ b) Sym.mark (S sAcc) S5 rfl h6A
  refine runs_congr (runs_seq r1 (runs_seq r2 (runs_seq r3 (runs_seq r4 (runs_seq r5 r6))))) ?_
  funext z
  by_cases hzA : z = sAcc
  · subst hzA
    simp only [Function.update_self, Function.update_of_ne hXA.symm]
  · by_cases hzX : z = .inl t
    · subst hzX
      simp only [hS5, hS4, hS3, hS2, hS1, Function.update_of_ne hXA, Function.update_self]
    · simp only [hS5, hS4, hS3, hS2, hS1, Function.update_of_ne hzA, Function.update_of_ne hzX]

open WP.W9comp in
/-- **The initialization**: from `k ≥ 1` on stack `0`, push `1` (on `one`), `k - 1` (on `km1` and on
stack `0`) and `m^(k-1)` (on `bb`), each above a `mark`. -/
theorem runs_descInit (PM : PowMulSpec DK) (m k : ℕ) (r1 : List Sym) (S : DK → List Sym)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hr1 : TermOK r1) (hSK : S sK = natSyms k ++ r1) :
    Runs (descInit PM m) S
      (Function.update (Function.update (Function.update (Function.update S
        sOne (natSyms 1 ++ Sym.mark :: S sOne))
        sKm1 (natSyms (k - 1) ++ Sym.mark :: S sKm1))
        sK (natSyms (k - 1) ++ Sym.mark :: S sK))
        sBb (natSyms (m ^ (k - 1)) ++ Sym.mark :: S sBb))
      (fun _ => True)
      (1 + ((bitLen 1 + 1) + (1 + (20 * (bitLen k + bitLen 1 + 1) + (1 + ((7 * bitLen (k - 1) + 7) +
        (1 + ((bitLen 1 + 1) + PM.cost m 1 (k - 1))))))))) := by
  have r1' := runs_pushMark sOne S
  set S1 := Function.update S sOne (Sym.mark :: S sOne) with hS1
  have r2 := runs_pushNat sOne 1 S1
  set S2 := Function.update S1 sOne (natSyms 1 ++ S1 sOne) with hS2
  have r3 := runs_pushMark sKm1 S2
  set S3 := Function.update S2 sKm1 (Sym.mark :: S2 sKm1) with hS3
  have h4K : S3 sK = natSyms k ++ r1 := by
    rw [hS3, Function.update_of_ne (by decide), hS2, Function.update_of_ne (by decide), hS1,
      Function.update_of_ne (by decide), hSK]
  have h4O : S3 sOne = natSyms 1 ++ (Sym.mark :: S sOne) := by
    rw [hS3, Function.update_of_ne (by decide), hS2, Function.update_self, hS1, Function.update_self]
  have r4 := runs_subN (x := sK) (y := sOne) (z := sKm1) (t1 := sT0) (t2 := sT1) (t3 := sT2)
    (by decide) k 1 r1 _ S3 hr1 (termOK_mark _) hk h4K h4O
  set S4 := Function.update S3 sKm1 (natSyms (k - 1) ++ S3 sKm1) with hS4
  have r5 := runs_pushMark sK S4
  set S5 := Function.update S4 sK (Sym.mark :: S4 sK) with hS5
  have h6 : S5 sKm1 = natSyms (k - 1) ++ (Sym.mark :: S sKm1) := by
    rw [hS5, Function.update_of_ne (by decide), hS4, Function.update_self, hS3,
      Function.update_self, hS2, Function.update_of_ne (by decide), hS1,
      Function.update_of_ne (by decide)]
  have r6 := runs_copyN (src := sKm1) (dst := sK) (tmp := sT0) (by decide) (by decide) (by decide)
    (k - 1) _ S5 (termOK_mark _) h6
  set S6 := Function.update S5 sK (natSyms (k - 1) ++ S5 sK) with hS6
  have r7 := runs_pushMark sBb S6
  set S7 := Function.update S6 sBb (Sym.mark :: S6 sBb) with hS7
  have r8 := runs_pushNat sBb 1 S7
  set S8 := Function.update S7 sBb (natSyms 1 ++ S7 sBb) with hS8
  have h9b : S8 sBb = natSyms 1 ++ (Sym.mark :: S sBb) := by
    rw [hS8, Function.update_self, hS7, Function.update_self, hS6, Function.update_of_ne (by decide),
      hS5, Function.update_of_ne (by decide), hS4, Function.update_of_ne (by decide), hS3,
      Function.update_of_ne (by decide), hS2, Function.update_of_ne (by decide), hS1,
      Function.update_of_ne (by decide)]
  have h9k : S8 sKm1 = natSyms (k - 1) ++ (Sym.mark :: S sKm1) := by
    rw [hS8, Function.update_of_ne (by decide), hS7, Function.update_of_ne (by decide), hS6,
      Function.update_of_ne (by decide), h6]
  have r9 := PM.runs (k := sBb) (ns := sKm1) (t1 := sT0) (t2 := sT1) (t3 := sT2) (t4 := sT3)
    (t5 := sT4) (t6 := sT5) (t7 := sT6) (by decide) m hm 1 (k - 1) _ _ S8 (termOK_mark _)
    (termOK_mark _) h9b h9k
  refine runs_congr (runs_seq r1' (runs_seq r2 (runs_seq r3 (runs_seq r4 (runs_seq r5
    (runs_seq r6 (runs_seq r7 (runs_seq r8 r9)))))))) ?_
  rw [one_mul]
  funext z
  simp only [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply]
  by_cases h1 : z = sBb
  · subst h1; simp
  · by_cases h2 : z = sK
    · subst h2; simp
    · by_cases h3 : z = sKm1
      · subst h3; simp
      · by_cases h4 : z = sOne
        · subst h4; simp
        · simp [h1, h2, h3, h4]

/-! ## The whole program -/

/-- A clean upper bound for the cost of `descProg`: the four `powMul` calls plus `30` times the
bit lengths of all numbers involved. -/
def descCostB (PM : PowMulSpec DK) (q m i j k N1 G B : ℕ) : ℕ :=
  PM.cost m 1 (k - 1) + PM.cost (q ^ i) N1 (m ^ (k - 1)) +
    PM.cost (q ^ (m - 1 - i + j)) G (m ^ (k - 1)) + PM.cost (q ^ (m - 1 - j)) B (m ^ (k - 1)) +
    30 * (bitLen k + bitLen (k - 1) + bitLen (m ^ (k - 1)) + bitLen N1 + bitLen G + bitLen B +
      bitLen (N1 * (q ^ i) ^ m ^ (k - 1)) + bitLen (G * (q ^ (m - 1 - i + j)) ^ m ^ (k - 1)) +
      bitLen (B * (q ^ (m - 1 - j)) ^ m ^ (k - 1)) + 10)

open WP.W9comp in
/-- **The child-descriptor program**: with `k ≥ 1, N1, G, B` on the named stacks (terminated),
`descProg` pushes `mark` and `k - 1`, `N1·(q^i)^b`, `G·(q^(m-1-i+j))^b`, `B·(q^(m-1-j))^b`
(`b = m^(k-1)`) on them; every scratch stack ends as it started. -/
theorem runs_descProg (PM : PowMulSpec DK) (q m i j k N1 G B : ℕ) (r1 r2 r3 r4 : List Sym)
    (S : DK → List Sym) (hq : 1 ≤ q) (hm : 1 ≤ m) (hk : 1 ≤ k) (hr1 : TermOK r1) (hr2 : TermOK r2) (hr3 : TermOK r3)
    (hr4 : TermOK r4) (h0 : S sK = natSyms k ++ r1) (h1 : S sN1 = natSyms N1 ++ r2)
    (h2 : S sG = natSyms G ++ r3) (h3 : S sB = natSyms B ++ r4) :
    Runs (descProg PM q m i j) S
      (Function.update (Function.update (Function.update (Function.update S
        sK (natSyms (k - 1) ++ Sym.mark :: S sK))
        sN1 (natSyms (N1 * (q ^ i) ^ m ^ (k - 1)) ++ Sym.mark :: S sN1))
        sG (natSyms (G * (q ^ (m - 1 - i + j)) ^ m ^ (k - 1)) ++ Sym.mark :: S sG))
        sB (natSyms (B * (q ^ (m - 1 - j)) ^ m ^ (k - 1)) ++ Sym.mark :: S sB))
      (fun _ => True) (descCostB PM q m i j k N1 G B) := by
  have r0 := runs_descInit PM m k r1 S hm hk hr1 h0
  set S0 := Function.update (Function.update (Function.update (Function.update S
    sOne (natSyms 1 ++ Sym.mark :: S sOne))
    sKm1 (natSyms (k - 1) ++ Sym.mark :: S sKm1))
    sK (natSyms (k - 1) ++ Sym.mark :: S sK))
    sBb (natSyms (m ^ (k - 1)) ++ Sym.mark :: S sBb) with hS0
  have hb0 : S0 sBb = natSyms (m ^ (k - 1)) ++ (Sym.mark :: S sBb) := by
    rw [hS0, Function.update_self]
  have hN0 : S0 sN1 = natSyms N1 ++ r2 := by
    rw [hS0, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), h1]
  have rA := runs_descPart PM 1 (q ^ i) N1 (m ^ (k - 1)) r2 _ S0 (Nat.one_le_pow _ _ hq) hr2
    (termOK_mark _) hN0 hb0
  set SA := Function.update S0 sN1 (natSyms (N1 * (q ^ i) ^ m ^ (k - 1)) ++ Sym.mark :: S0 sN1)
    with hSA
  have hbA : SA sBb = natSyms (m ^ (k - 1)) ++ (Sym.mark :: S sBb) := by
    rw [hSA, Function.update_of_ne (by decide), hb0]
  have hGA : SA sG = natSyms G ++ r3 := by
    rw [hSA, Function.update_of_ne (by decide), hS0, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), h2]
  have rB := runs_descPart PM 2 (q ^ (m - 1 - i + j)) G (m ^ (k - 1)) r3 _ SA
    (Nat.one_le_pow _ _ hq) hr3 (termOK_mark _) hGA hbA
  set SB := Function.update SA sG
    (natSyms (G * (q ^ (m - 1 - i + j)) ^ m ^ (k - 1)) ++ Sym.mark :: SA sG) with hSB
  have hbB : SB sBb = natSyms (m ^ (k - 1)) ++ (Sym.mark :: S sBb) := by
    rw [hSB, Function.update_of_ne (by decide), hbA]
  have hBB : SB sB = natSyms B ++ r4 := by
    rw [hSB, Function.update_of_ne (by decide), hSA, Function.update_of_ne (by decide), hS0,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), h3]
  have rC := runs_descPart PM 3 (q ^ (m - 1 - j)) B (m ^ (k - 1)) r4 _ SB
    (Nat.one_le_pow _ _ hq) hr4 (termOK_mark _) hBB hbB
  set SC := Function.update SB sB
    (natSyms (B * (q ^ (m - 1 - j)) ^ m ^ (k - 1)) ++ Sym.mark :: SB sB) with hSC
  have hd1 : SC sBb = natSyms (m ^ (k - 1)) ++ Sym.mark :: S sBb := by
    rw [hSC, Function.update_of_ne (by decide), hbB]
  have rD1 := runs_dropF sBb (m ^ (k - 1)) Sym.mark (S sBb) SC rfl hd1
  set SD1 := Function.update SC sBb (S sBb) with hSD1
  have hd2 : SD1 sKm1 = natSyms (k - 1) ++ Sym.mark :: S sKm1 := by
    rw [hSD1, Function.update_of_ne (by decide), hSC, Function.update_of_ne (by decide), hSB,
      Function.update_of_ne (by decide), hSA, Function.update_of_ne (by decide), hS0,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  have rD2 := runs_dropF sKm1 (k - 1) Sym.mark (S sKm1) SD1 rfl hd2
  set SD2 := Function.update SD1 sKm1 (S sKm1) with hSD2
  have hd3 : SD2 sOne = natSyms 1 ++ Sym.mark :: S sOne := by
    rw [hSD2, Function.update_of_ne (by decide), hSD1, Function.update_of_ne (by decide), hSC,
      Function.update_of_ne (by decide), hSB, Function.update_of_ne (by decide), hSA,
      Function.update_of_ne (by decide), hS0, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  have rD3 := runs_dropF sOne 1 Sym.mark (S sOne) SD2 rfl hd3
  have r := runs_seq r0 (runs_seq rA (runs_seq rB (runs_seq rC (runs_seq rD1
    (runs_seq rD2 rD3)))))
  refine runs_mono (runs_congr r ?_) (fun _ h => h) ?_
  · funext z
    simp only [hSD2, hSD1, hSC, hSB, hSA, hS0, Function.update_apply]
    by_cases e1 : z = sOne
    · subst e1; simp
    · by_cases e2 : z = sKm1
      · subst e2; simp
      · by_cases e3 : z = sBb
        · subst e3; simp
        · by_cases e4 : z = sK
          · subst e4; simp
          · by_cases e5 : z = sN1
            · subst e5; simp
            · by_cases e6 : z = sG
              · subst e6; simp
              · by_cases e7 : z = sB
                · subst e7; simp
                · simp [e1, e2, e3, e4, e5, e6, e7]
  · have hb1 : bitLen 1 = 1 := rfl
    unfold descCostB
    omega

/-! ## Cost -/

theorem bitLen_eq_size (y : ℕ) : bitLen y = Nat.size y := IntMulTM.length_encodeNat y

theorem bitLen_le_self (y : ℕ) : bitLen y ≤ y := by
  rw [bitLen_eq_size]
  exact Nat.size_le.2 Nat.lt_two_pow_self

theorem succ_sq_le_eight_pow (s : ℕ) : (s + 1) ^ 2 ≤ 8 * 2 ^ s := by
  induction s with
  | zero => norm_num
  | succ s ih =>
    have h1 : 2 * s + 3 ≤ 8 * 2 ^ s := by
      have := Nat.lt_two_pow_self (n := s)
      have h2 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
      omega
    have e1 : (s + 1 + 1) ^ 2 = (s + 1) ^ 2 + (2 * s + 3) := by ring
    have e2 : 8 * 2 ^ (s + 1) = 8 * 2 ^ s + 8 * 2 ^ s := by ring
    rw [e1, e2]
    omega

/-- `(bitLen y + 1)² ≤ 16 y` for `y ≥ 1`. -/
theorem bitLen_succ_sq_le {y : ℕ} (hy : 1 ≤ y) : (bitLen y + 1) ^ 2 ≤ 16 * y := by
  rw [bitLen_eq_size]
  have hs : 0 < Nat.size y := Nat.size_pos.2 (by omega)
  have h2 : 2 ^ (Nat.size y - 1) ≤ y := Nat.lt_size.1 (by omega)
  have h3 := succ_sq_le_eight_pow (Nat.size y)
  have e : 8 * 2 ^ Nat.size y = 16 * 2 ^ (Nat.size y - 1) := by
    obtain ⟨t, ht⟩ : ∃ t, Nat.size y = t + 1 := ⟨Nat.size y - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, pow_succ]
    ring
  omega

theorem lt_pow_of_two_le {q : ℕ} (hq : 2 ≤ q) (n : ℕ) : n < q ^ n :=
  lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hq n)

/-- One `powMul` part: `(b+1)·(x·(q^e)^b) ≤ x·q^M` when `(e+1)·b ≤ M`. -/
theorem part_le {q e b M : ℕ} (hq : 2 ≤ q) (h : (e + 1) * b ≤ M) (x : ℕ) :
    (b + 1) * (x * (q ^ e) ^ b) ≤ x * q ^ M := by
  have h1 : b + 1 ≤ q ^ b := lt_pow_of_two_le hq b
  have h2 : q ^ ((e + 1) * b) ≤ q ^ M := Nat.pow_le_pow_right (by omega) h
  have e1 : q ^ b * (x * (q ^ e) ^ b) = x * q ^ ((e + 1) * b) := by
    rw [← pow_mul, add_one_mul, pow_add]
    ring
  calc (b + 1) * (x * (q ^ e) ^ b) ≤ q ^ b * (x * (q ^ e) ^ b) := Nat.mul_le_mul_right _ h1
    _ = x * q ^ ((e + 1) * b) := e1
    _ ≤ x * q ^ M := Nat.mul_le_mul_left _ h2

/-- The cost of one `powMul` part is at most `16 C x q^M`. -/
theorem partCost_le (PM : PowMulSpec DK) {C q e b M x : ℕ} (hq : 2 ≤ q) (hx : 1 ≤ x)
    (h : (e + 1) * b ≤ M) (hC : ∀ a n, PM.cost (q ^ e) a n ≤ C * ((n + 1) * (bitLen (a * (q ^ e) ^ n) + 1) ^ 2)) :
    PM.cost (q ^ e) x b ≤ 16 * C * (x * q ^ M) := by
  have hy : 1 ≤ x * (q ^ e) ^ b := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (pow_ne_zero _ (by omega))))
  have h1 := hC x b
  have h2 := bitLen_succ_sq_le hy
  have h3 := part_le hq h x
  calc PM.cost (q ^ e) x b ≤ C * ((b + 1) * (bitLen (x * (q ^ e) ^ b) + 1) ^ 2) := h1
    _ ≤ C * ((b + 1) * (16 * (x * (q ^ e) ^ b))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
    _ = 16 * C * ((b + 1) * (x * (q ^ e) ^ b)) := by ring
    _ ≤ 16 * C * (x * q ^ M) := Nat.mul_le_mul_left _ h3

/-- **The cost bound** `descCostB ≤ (16(C₁+C₂+C₃+C₄) + 300)·(rowSize + 1)`, with `C₁, …, C₄` the
cost constants of `powMul` at `c = m, q^i, q^((m-1-i)+j), q^(m-1-j)`. -/
theorem descCostB_le (PM : PowMulSpec DK) {q m i j C1 C2 C3 C4 : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m)
    (hi : i < m) (hj : j < m)
    (hC1 : ∀ a n, PM.cost m a n ≤ C1 * ((n + 1) * (bitLen (a * m ^ n) + 1) ^ 2))
    (hC2 : ∀ a n, PM.cost (q ^ i) a n ≤ C2 * ((n + 1) * (bitLen (a * (q ^ i) ^ n) + 1) ^ 2))
    (hC3 : ∀ a n, PM.cost (q ^ (m - 1 - i + j)) a n ≤
      C3 * ((n + 1) * (bitLen (a * (q ^ (m - 1 - i + j)) ^ n) + 1) ^ 2))
    (hC4 : ∀ a n, PM.cost (q ^ (m - 1 - j)) a n ≤
      C4 * ((n + 1) * (bitLen (a * (q ^ (m - 1 - j)) ^ n) + 1) ^ 2))
    {k N1 G B : ℕ} (hk : 1 ≤ k) (hN1 : 1 ≤ N1) (hG : 1 ≤ G) (hB : 1 ≤ B) :
    descCostB PM q m i j k N1 G B ≤
      (16 * (C1 + C2 + C3 + C4) + 300) * (rowSize q m k N1 G B + 1) := by
  have hb1 : 1 ≤ m ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
  have hMb : m ^ k = m * m ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hkM : k ≤ m ^ k := (lt_pow_of_two_le hm k).le
  have hbM : m ^ (k - 1) ≤ m ^ k := by rw [hMb]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hMX : m ^ k ≤ q ^ m ^ k := (lt_pow_of_two_le hq _).le
  have hX1 : 0 < q ^ m ^ k := pow_pos (by omega) _
  have hRe : rowSize q m k N1 G B = N1 * G * B * (q ^ m ^ k * q ^ m ^ k) := by
    unfold rowSize; ring
  have hNGB : 0 < N1 * G * B := Nat.mul_pos (Nat.mul_pos hN1 hG) hB
  have hN1' : N1 ≤ N1 * G * B :=
    calc N1 = N1 * 1 * 1 := by ring
      _ ≤ N1 * G * B := Nat.mul_le_mul (Nat.mul_le_mul_left _ hG) hB
  have hG' : G ≤ N1 * G * B :=
    calc G = 1 * G * 1 := by ring
      _ ≤ N1 * G * B := Nat.mul_le_mul (Nat.mul_le_mul_right _ hN1) hB
  have hB' : B ≤ N1 * G * B :=
    calc B = 1 * 1 * B := by ring
      _ ≤ N1 * G * B := Nat.mul_le_mul_right _ (Nat.mul_le_mul hN1 hG)
  have hXX : q ^ m ^ k ≤ q ^ m ^ k * q ^ m ^ k := Nat.le_mul_of_pos_left _ hX1
  have hRx : ∀ x, x ≤ N1 * G * B → x * (q ^ m ^ k * q ^ m ^ k) ≤ rowSize q m k N1 G B :=
    fun x hx => by rw [hRe]; exact Nat.mul_le_mul_right _ hx
  have hRXX : q ^ m ^ k * q ^ m ^ k ≤ rowSize q m k N1 G B := by
    rw [hRe]; exact Nat.le_mul_of_pos_left _ hNGB
  have hNGBR : N1 * G * B ≤ rowSize q m k N1 G B := by
    rw [hRe]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hX1 hX1)
  have hkR : k ≤ rowSize q m k N1 G B := le_trans hkM (le_trans hMX (le_trans hXX hRXX))
  -- the four `powMul` costs
  have p1 : PM.cost m 1 (k - 1) ≤ 16 * C1 * rowSize q m k N1 G B := by
    have h1 := hC1 1 (k - 1)
    rw [one_mul, Nat.sub_add_cancel hk] at h1
    have h2 := bitLen_succ_sq_le hb1
    have h3 : k * m ^ (k - 1) ≤ rowSize q m k N1 G B :=
      le_trans (Nat.mul_le_mul (le_trans hkM hMX) (le_trans hbM hMX)) hRXX
    calc PM.cost m 1 (k - 1) ≤ C1 * (k * (bitLen (m ^ (k - 1)) + 1) ^ 2) := h1
      _ ≤ C1 * (k * (16 * m ^ (k - 1))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      _ = 16 * C1 * (k * m ^ (k - 1)) := by ring
      _ ≤ 16 * C1 * rowSize q m k N1 G B := Nat.mul_le_mul_left _ h3
  have p2 : PM.cost (q ^ i) N1 (m ^ (k - 1)) ≤ 16 * C2 * rowSize q m k N1 G B := by
    have hle : (i + 1) * m ^ (k - 1) ≤ m ^ k := by
      rw [hMb]; exact Nat.mul_le_mul_right _ (by omega)
    have h := partCost_le PM (e := i) (b := m ^ (k - 1)) (M := m ^ k) hq hN1 hle hC2
    exact le_trans h (Nat.mul_le_mul_left _ (le_trans (Nat.mul_le_mul_left _ hXX) (hRx N1 hN1')))
  have p3 : PM.cost (q ^ (m - 1 - i + j)) G (m ^ (k - 1)) ≤ 16 * C3 * rowSize q m k N1 G B := by
    have hle : (m - 1 - i + j + 1) * m ^ (k - 1) ≤ 2 * m ^ k := by
      rw [hMb, ← mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
    have h := partCost_le PM (e := m - 1 - i + j) (b := m ^ (k - 1)) (M := 2 * m ^ k) hq hG hle
      hC3
    have h' : G * q ^ (2 * m ^ k) ≤ rowSize q m k N1 G B := by
      rw [two_mul, pow_add]; exact hRx G hG'
    exact le_trans h (Nat.mul_le_mul_left _ h')
  have p4 : PM.cost (q ^ (m - 1 - j)) B (m ^ (k - 1)) ≤ 16 * C4 * rowSize q m k N1 G B := by
    have hle : (m - 1 - j + 1) * m ^ (k - 1) ≤ m ^ k := by
      rw [hMb]; exact Nat.mul_le_mul_right _ (by omega)
    have h := partCost_le PM (e := m - 1 - j) (b := m ^ (k - 1)) (M := m ^ k) hq hB hle hC4
    exact le_trans h (Nat.mul_le_mul_left _ (le_trans (Nat.mul_le_mul_left _ hXX) (hRx B hB')))
  -- the bit lengths
  have hpow : ∀ e x, (e + 1) * m ^ (k - 1) ≤ 2 * m ^ k → x ≤ N1 * G * B →
      bitLen (x * (q ^ e) ^ m ^ (k - 1)) ≤ rowSize q m k N1 G B := by
    intro e x he hx
    have h1 : (q ^ e) ^ m ^ (k - 1) ≤ q ^ m ^ k * q ^ m ^ k := by
      rw [← pow_mul, ← pow_add, ← two_mul]
      exact Nat.pow_le_pow_right (by omega)
        (le_trans (Nat.mul_le_mul_right _ (Nat.le_add_right e 1)) he)
    exact le_trans (bitLen_le_self _) (le_trans (Nat.mul_le_mul_left _ h1) (hRx x hx))
  have t1 := hpow i N1 (by rw [hMb, ← mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)) hN1'
  have t2 := hpow (m - 1 - i + j) G
    (by rw [hMb, ← mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)) hG'
  have t3 := hpow (m - 1 - j) B
    (by rw [hMb, ← mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)) hB'
  have t4 : bitLen k ≤ rowSize q m k N1 G B := le_trans (bitLen_le_self _) hkR
  have t5 : bitLen (k - 1) ≤ rowSize q m k N1 G B :=
    le_trans (bitLen_le_self _) (le_trans (Nat.sub_le _ _) hkR)
  have t6 : bitLen (m ^ (k - 1)) ≤ rowSize q m k N1 G B :=
    le_trans (bitLen_le_self _) (le_trans hbM (le_trans hMX (le_trans hXX hRXX)))
  have t7 : bitLen N1 ≤ rowSize q m k N1 G B :=
    le_trans (bitLen_le_self _) (le_trans hN1' hNGBR)
  have t8 : bitLen G ≤ rowSize q m k N1 G B :=
    le_trans (bitLen_le_self _) (le_trans hG' hNGBR)
  have t9 : bitLen B ≤ rowSize q m k N1 G B :=
    le_trans (bitLen_le_self _) (le_trans hB' hNGBR)
  have hexp : (16 * (C1 + C2 + C3 + C4) + 300) * (rowSize q m k N1 G B + 1) =
      16 * C1 * rowSize q m k N1 G B + 16 * C2 * rowSize q m k N1 G B +
        16 * C3 * rowSize q m k N1 G B + 16 * C4 * rowSize q m k N1 G B +
        16 * (C1 + C2 + C3 + C4) + 300 * rowSize q m k N1 G B + 300 := by ring
  rw [hexp]
  unfold descCostB
  omega

/-- **`C5DescStmt` from a power-multiplication program** (`PowMulSpec`). -/
theorem c5Desc_of_powMul (PM : PowMulSpec DK) (q m : ℕ) (i j : Fin m) (hq : 2 ≤ q) (hm : 2 ≤ m) :
    C5DescStmt q m i j := by
  obtain ⟨C1, hC1⟩ := PM.cost_le m
  obtain ⟨C2, hC2⟩ := PM.cost_le (q ^ (i : ℕ))
  obtain ⟨C3, hC3⟩ := PM.cost_le (q ^ (m - 1 - (i : ℕ) + j))
  obtain ⟨C4, hC4⟩ := PM.cost_le (q ^ (m - 1 - (j : ℕ)))
  refine ⟨16 * (C1 + C2 + C3 + C4) + 300, fun _ => ⟨Fin 11, inferInstance, inferInstance, Reg,
    descProg PM q m i j, inferInstance, inferInstance, closed_descProg PM q m i j, ?_⟩⟩
  intro k N1 G B r1 r2 r3 r4 S hk hN1 hG hB hr1 hr2 hr3 hr4 h0 h1 h2 h3
  have r := runs_descProg PM q m i j k N1 G B r1 r2 r3 r4 S (by omega) (by omega) hk hr1 hr2 hr3
    hr4 h0 h1 h2 h3
  have e1 : N1 * (q ^ (i : ℕ)) ^ m ^ (k - 1) = cN1 q m k N1 i := by
    unfold cN1; rw [← pow_mul]
  have e2 : G * (q ^ (m - 1 - (i : ℕ) + j)) ^ m ^ (k - 1) = cG q m k G i j := by
    unfold cG; rw [← pow_mul, add_mul, pow_add]; ring
  have e3 : B * (q ^ (m - 1 - (j : ℕ))) ^ m ^ (k - 1) = cB q m k B j := by
    unfold cB; rw [← pow_mul]; ring
  rw [e1, e2, e3] at r
  exact WP.W9comp.runs_mono r (fun _ h => h)
    (descCostB_le PM hq hm i.isLt j.isLt hC1 hC2 hC3 hC4 hk hN1 hG hB)

/-! ## Instantiation with `NatArith.powMulN` -/

theorem powCost_le (c a n : ℕ) :
    powCost c a n ≤ 200 * (bitLen c + 2) ^ 2 * ((n + 1) * (bitLen (a * c ^ n) + 1) ^ 2) := by
  unfold powCost
  have e : (bitLen c + 2) * (bitLen (a * c ^ n) + 1) =
      bitLen c * bitLen (a * c ^ n) + bitLen c + 2 * bitLen (a * c ^ n) + 2 := by ring
  have h : bitLen (a * c ^ n) + bitLen c + 2 ≤ (bitLen c + 2) * (bitLen (a * c ^ n) + 1) := by
    rw [e]; omega
  calc (n + 1) * (200 * (bitLen (a * c ^ n) + bitLen c + 2) ^ 2)
      ≤ (n + 1) * (200 * ((bitLen c + 2) * (bitLen (a * c ^ n) + 1)) ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2))
    _ = 200 * (bitLen c + 2) ^ 2 * ((n + 1) * (bitLen (a * c ^ n) + 1) ^ 2) := by ring

/-- `NatArith.powMulN` as a `PowMulSpec`. -/
noncomputable def natArithPowMul (K : Type) [DecidableEq K] : PowMulSpec K where
  prog := powMulN
  closed := closed_powMulN
  cost := powCost
  runs := fun h c hc a n rk rn S hrk hrn hk hn => runs_powMulN h c hc a n rk rn S hrk hrn hk hn
  cost_le := fun c => ⟨200 * (bitLen c + 2) ^ 2, powCost_le c⟩

end SubNLogN.Machine.C5DescAux

namespace SubNLogN.Machine.C5

/-- **Leaf L4 holds** (`c5Desc_holds`): for `q ≥ 2` and `m ≥ 2`, `C5DescStmt q m i j` for every
pivot `(i, j)`, by `descProg` with `NatArith.powMulN`. -/
theorem c5Desc_holds {q m : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m) : ∀ i j : Fin m, C5DescStmt q m i j :=
  fun i j => C5DescAux.c5Desc_of_powMul (C5DescAux.natArithPowMul _) q m i j hq hm

end SubNLogN.Machine.C5
