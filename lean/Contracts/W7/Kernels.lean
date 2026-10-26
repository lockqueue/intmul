import Contracts.W7.Format

/-!
# Contracts.W7.Kernels — W7's machine kernels, bit-exact to the snapshot's table primitives

Design invariant: W7 **reproduces the reference specification's table integers**. Every table entry
is the `.1` of a computable snapshot primitive in `ComputableTranscendentals.lean` (CTr). Those
primitives use only:
* `+`, `−`, `×`;
* `divRoundRatInt`, shifts and clamps;
* `Nat.sqrt`.

So each one is a fixed composition of W3 (add, sub, shifts, compare), W5 (Toom-3 multiply) and W6a
(`divRound`), plus one new kernel, `W7_isqrt`.

Conventions (`Contracts.Machine.Common`):
* exact final stacks; named stacks `.inl 0, 1, …` in docstring order; operands restored;
* results are pushed on the last named stack;
* `≤ 16` scratch stacks, to make room for W5's 8 and W6a's 6;
* one constant `C` per contract.

The cost bounds are polynomial in the call's size parameters. They are all far below the snapshot's
per-entry budget `18000·M⁴` (CTB:421-431), so their sum over a level is `O(precomputeSeriesTableCost)`.
The cost proofs use the snapshot's per-call-site width-soundness theorems (`*_widths_sound`, CTr).

| Kernel | Reference (`.1`) | Cost `≤` | Width source |
|---|---|---|---|
| `W7_isqrt` | `Nat.sqrt a` | `C(|a|²+1)` | – |
| `W7_piScaled` | `computablePiScaledWithCost B` (CTr:968) | `C(B+1)⁴` | `PiScaledWidthSound` |
| `W7_log2Scaled` | `computableLog2ScaledWithCost B` (CTr:1221) | `C(B+1)⁴` | `Log2ScaledWidthSound` |
| `W7_stdChar neg` | `computableStdCharWithProgramCost q num den neg` (CTr:2372) | `C(q+|den|+1)⁴` | `StdCharWidthSound` |
| `W7_sincGaussianTap` | `computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s` (CTr:3619), with `π`, `ln 2` hoisted as in CTB:116-121 | `C(p_work+pSub+|t1|+1)⁴` | `SincGaussianTapWidthSound` |
| `W7_c0c1` | `computableC0C1WithProgramCost p_work pSub r u2` (CTr:5068) | `C(p_work+pSub+|r|+1)⁴` | `C0C1WidthSound` |
| `W7_colRecip` | `W7.colRecip H r u2 a c` (W6b's μ) | `C((H+1)(|d|+1)+…)` | – |

**Mutation-test ideas.**
* A Newton `isqrt` without the final correction is off by one at perfect squares minus one.
* A `stdChar` that hoists `π` at the wrong precision (`q+2` instead of `q+6`) differs from the
  reference already at `q = 6`. The `#guard` lines pin the reference values.
* A tap kernel that reads `s − pSub` as a natural number (truncating at 0) is wrong for `s < pSub`.
-/

namespace TMFw.Contracts

/-- The tap evaluator's internal `π`/`ln 2` precision `B_c` (CTB:51; CTr:3620-3623). The machine
computes `π` and `ln 2` once per level at this precision and passes them to `W7_sincGaussianTap`. -/
def W7.tapPrec (pSub : ℕ) : ℕ :=
  (pSub + 2) + (4 * (4 * (pSub + 1)) + (pSub + 2) + 4) + 3 * (4 * (pSub + 1)) + 6

/-- Hoisting `π` and `ln 2` at `W7.tapPrec` is exact (the snapshot's own `rfl` lemma, CTB:73). -/
theorem W7.tapGiven_eq (p_work pSub t1 j1 s : ℕ) :
    IntMul.computableSincGaussianTapGivenPiLog2 p_work pSub t1
        (IntMul.computablePiScaledWithCost (W7.tapPrec pSub))
        (IntMul.computableLog2ScaledWithCost (W7.tapPrec pSub)) j1 s =
      IntMul.computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s :=
  IntMul.computableSincGaussianTapGivenPiLog2_eq p_work pSub t1 j1 s

/-! ## Reference sanity checks (evaluated; no proof terms) -/

-- `π·2^10 ≈ 3216.99`.
#guard 3215 ≤ (IntMul.computablePiScaledWithCost 10).1 ∧ (IntMul.computablePiScaledWithCost 10).1 ≤ 3218
-- `ln 2·2^10 ≈ 709.78`.
#guard 708 ≤ (IntMul.computableLog2ScaledWithCost 10).1 ∧ (IntMul.computableLog2ScaledWithCost 10).1 ≤ 711
-- `stdChar(1/4) = i` on the `2^(6+2)` grid: `≈ (0, 256)`.
#guard (let z := (IntMul.computableStdCharWithProgramCost 6 1 4 false).1;
  -2 ≤ z.1 ∧ z.1 ≤ 2 ∧ 254 ≤ z.2 ∧ z.2 ≤ 258)

/-! ## Kernel contracts -/

/-- **W7.isqrt**: `z += ⌊√a⌋`.
* Stacks: `0` = `a` (restored), `1` = destination.
* Cost `C·(|a|² + 1)`, e.g. digit-by-digit (restoring) square root. -/
def W7_isqrt : Prop :=
  MContract Unit 2 16 Unit fun _ m _ C _ P =>
    ∀ (a : ℕ) (ra : List Sym) (S : Loc 2 m → List Sym), TermOK ra →
      S (.inl 0) = natSyms a ++ ra →
      Runs P S (Function.update S (.inl 1) (natSyms (Nat.sqrt a) ++ S (.inl 1))) (fun _ => True)
        (C * (bitLen a * bitLen a + 1))

/-- **W7.piScaled**: `z += (computablePiScaledWithCost B).1`, the Archimedes iteration (CTr:957-971).
* Stacks: `0` = `B` (restored), `1` = destination (signed).
* Cost `C·(B + 1)⁴`. -/
def W7_piScaled : Prop :=
  MContract Unit 2 16 Unit fun _ m _ C _ P =>
    ∀ (B : ℕ) (rB : List Sym) (S : Loc 2 m → List Sym), TermOK rB →
      S (.inl 0) = natSyms B ++ rB →
      Runs P S (Function.update S (.inl 1)
          (intSyms (IntMul.computablePiScaledWithCost B).1 ++ S (.inl 1))) (fun _ => True)
        (C * (B + 1) ^ 4)

/-- **W7.log2Scaled**: `z += (computableLog2ScaledWithCost B).1`, the series of CTr:1221-1230.
* Stacks: `0` = `B` (restored), `1` = destination (signed).
* Cost `C·(B + 1)⁴`. -/
def W7_log2Scaled : Prop :=
  MContract Unit 2 16 Unit fun _ m _ C _ P =>
    ∀ (B : ℕ) (rB : List Sym) (S : Loc 2 m → List Sym), TermOK rB →
      S (.inl 0) = natSyms B ++ rB →
      Runs P S (Function.update S (.inl 1)
          (intSyms (IntMul.computableLog2ScaledWithCost B).1 ++ S (.inl 1))) (fun _ => True)
        (C * (B + 1) ^ 4)

/-- **W7.stdChar** (compile-time `neg`). Push the complex record (`W7.cplxRec`) of
`(computableStdCharWithProgramCost q num den neg).1`. The call sites are:
* pre-twiddles: `q = pSub`, `den = 2r`, `neg = false`;
* post-twiddles: the same with `neg = true`;
* leaf: `q = q_leaf`, `den = 2^(s+1)`, `neg = false`.

Stacks `0` = `q`, `1` = `num`, `2` = `den` (restored), `3` = destination. Requires `0 < den` and
`num ≤ den`, the premises of `computableStdCharWithProgramCost_widths_sound`. Cost
`C·(q + |den| + 1)⁴`. -/
def W7_stdChar : Prop :=
  MContract Bool 4 16 Unit fun neg m _ C _ P =>
    ∀ (q num den : ℕ) (r0 r1 r2 : List Sym) (S : Loc 4 m → List Sym),
      0 < den → num ≤ den → TermOK r0 → TermOK r1 → TermOK r2 →
      S (.inl 0) = natSyms q ++ r0 → S (.inl 1) = natSyms num ++ r1 →
      S (.inl 2) = natSyms den ++ r2 →
      Runs P S (Function.update S (.inl 3)
          (W7.cplxRec (IntMul.computableStdCharWithProgramCost q num den neg).1 ++ S (.inl 3)))
        (fun _ => True) (C * (q + bitLen den + 1) ^ 4)

/-- **W7.sincGaussianTap**. Push the signed raw tap
`(computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1` (CTr:3619). `π` and `ln 2` at
`W7.tapPrec pSub` are inputs, computed once per level (CTB:116-121; F6 item 6). They are passed
signed, exactly as `W7_piScaled` and `W7_log2Scaled` push them.

Stacks `0..4` = `p_work, pSub, t1, j1, s` (unsigned), `5` = `πZ`, `6` = `lnZ` (signed), all
restored; `7` = destination. The premises are those of
`computableSincGaussianTapWithProgramCost_widths_sound`. Cost `C·(p_work + pSub + |t1| + 1)⁴`. -/
def W7_sincGaussianTap : Prop :=
  MContract Unit 8 16 Unit fun _ m _ C _ P =>
    ∀ (p_work pSub t1 j1 s : ℕ) (πZ lnZ : ℤ) (r0 r1 r2 r3 r4 r5 r6 : List Sym)
      (S : Loc 8 m → List Sym),
      0 < p_work → 0 < pSub → 0 < t1 → j1 < t1 → s < 2 * pSub + 1 →
      πZ = (IntMul.computablePiScaledWithCost (W7.tapPrec pSub)).1 →
      lnZ = (IntMul.computableLog2ScaledWithCost (W7.tapPrec pSub)).1 →
      TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
      S (.inl 0) = natSyms p_work ++ r0 → S (.inl 1) = natSyms pSub ++ r1 →
      S (.inl 2) = natSyms t1 ++ r2 → S (.inl 3) = natSyms j1 ++ r3 →
      S (.inl 4) = natSyms s ++ r4 → S (.inl 5) = intSyms πZ ++ r5 →
      S (.inl 6) = intSyms lnZ ++ r6 →
      Runs P S (Function.update S (.inl 7)
          (intSyms (IntMul.computableSincGaussianTapWithProgramCost p_work pSub t1 j1 s).1 ++
            S (.inl 7)))
        (fun _ => True) (C * (p_work + pSub + bitLen t1 + 1) ^ 4)

/-- **W7.c0c1**. Push `intSyms c0.1 ++ intSyms c1.1` for
`(c0, c1) = (computableC0C1WithProgramCost p_work pSub r u2).1` (CTr:5068). Both have imaginary part
`0` (CTB:165).

Stacks `0..3` = `p_work, pSub, r, u2` (restored), `4` = destination. Premises as in
`computableC0C1WithProgramCost_widths_sound`. Cost `C·(p_work + pSub + |r| + 1)⁴`. -/
def W7_c0c1 : Prop :=
  MContract Unit 5 16 Unit fun _ m _ C _ P =>
    ∀ (p_work pSub r u2 : ℕ) (r0 r1 r2 r3 : List Sym) (S : Loc 5 m → List Sym),
      0 < p_work → 0 < r → u2 < r →
      TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 →
      S (.inl 0) = natSyms p_work ++ r0 → S (.inl 1) = natSyms pSub ++ r1 →
      S (.inl 2) = natSyms r ++ r2 → S (.inl 3) = natSyms u2 ++ r3 →
      Runs P S (Function.update S (.inl 4)
          (intSyms (IntMul.computableC0C1WithProgramCost p_work pSub r u2).1.1.1 ++
            intSyms (IntMul.computableC0C1WithProgramCost p_work pSub r u2).1.2.1 ++ S (.inl 4)))
        (fun _ => True) (C * (p_work + pSub + bitLen r + 1) ^ 4)

/-- **W7.colRecip**. Push `intSyms μ` with `μ = W7.colRecip H r u2 a c = ⌊2^H / d⌋` and
`d = W8.columnDivisor r u2 a c > 0`. This is the post record's reciprocal, the value W6b's
`W8_columnSolve_callSite` consumes.

Stacks `0` = `H`, `1` = `r`, `2` = `u2` (unsigned), `3` = `a`, `4` = `c` (signed), all restored;
`5` = destination. Cost `C·((H+1)·(|d|+1) + |r| + |u2| + |a| + |c| + 1)`: one shift and one W6a long
division. -/
def W7_colRecip : Prop :=
  MContract Unit 6 16 Unit fun _ m _ C _ P =>
    ∀ (H r u2 : ℕ) (a c : ℤ) (r0 r1 r2 r3 r4 : List Sym) (S : Loc 6 m → List Sym),
      0 < IntMulTM.Contracts.W8.columnDivisor r u2 a c →
      TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = natSyms H ++ r0 → S (.inl 1) = natSyms r ++ r1 → S (.inl 2) = natSyms u2 ++ r2 →
      S (.inl 3) = intSyms a ++ r3 → S (.inl 4) = intSyms c ++ r4 →
      Runs P S (Function.update S (.inl 5) (intSyms (W7.colRecip H r u2 a c) ++ S (.inl 5)))
        (fun _ => True)
        (C * ((H + 1) * (bitLen (IntMulTM.Contracts.W8.columnDivisor r u2 a c).natAbs + 1) +
          bitLen r + bitLen u2 + bitLen a.natAbs + bitLen c.natAbs + 1))

/-- All W7 kernels. -/
def W7_kernels : Prop :=
  W7_isqrt ∧ W7_piScaled ∧ W7_log2Scaled ∧ W7_stdChar ∧ W7_sincGaussianTap ∧ W7_c0c1 ∧ W7_colRecip

#assert_std_axioms W7.tapGiven_eq

end TMFw.Contracts
