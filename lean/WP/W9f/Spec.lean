import Contracts.W9.Post

/-!
# WP.W9f.Spec — sub-kernel interfaces of the column solvers (`W9_columnSolve`)

`W9_columnSolve` (Contracts/W9/Post.lean) is assembled from closed sub-kernels in the frozen
`MContract` shape (named stacks `.inl i`, scratch `.inr j` with arbitrary content restored, exact
final stacks, one cost constant chosen first):

| Prop | role |
|---|---|
| `W9f_fwdCore Mul` | forward bidiagonal solver `W8.solveFwdBarrett` (Fwd regime; Bwd after input reversal) |
| `W9f_nyqCore Mul` | Nyquist solver `W8.solveNyqBarrett` (zPart recurrence, alternating sum, outputs) |
| `W9f_moveEntries` | move all entries of a block to another stack, one at a time (reverses the order) |

Products must be issued at the declared width `solW H = 8·(H+1)` (`Mul` is not monotone).
-/

namespace WP.W9f

open TMFw TMFw.Contracts TMFw.Contracts.W9

/-- Declared width of every W5 product in the column solvers. -/
def solW (H : ℕ) : ℕ := 8 * (H + 1)

/-- The stack top is not the first symbol of an entry (stack bottom or a non-sign symbol). -/
def NotEntry (r : List Sym) : Prop := ∀ s, r.head? = some s → s ≠ Sym.pos ∧ s ≠ Sym.neg

/-- **Forward column core.** Named stacks: `0` IN (the input block, consumed down to `rIn`),
`1` OUT (the result block is pushed, first entry on top), `2` `q`, `3` `H`, `4` `μ` (naturals),
`5` divisor `a`, `6` multiplier `c` (signed). The parameter stacks are restored. -/
def W9f_fwdCore (Mul : ℕ → ℕ) : Prop :=
  MContract Unit 7 48 Unit fun _ m _ C _ P =>
    ∀ (q H μ : ℕ) (a c : ℤ) (Ys : Array (ℤ × ℤ)) (rIn r2 r3 r4 r5 r6 : List Sym)
      (S : Loc 7 m → List Sym),
      2 ≤ Ys.size → q + 2 ≤ H → 0 < a → (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a →
      bitLen a.natAbs ≤ H → bitLen c.natAbs ≤ H → ArrW H Ys →
      IntMulTM.Contracts.W8.zPartFwdBound q H a c Ys (Ys.size - 1) →
      IntMulTM.Contracts.W8.zHomFwdBound q H a c (Ys.size - 1) →
      ArrW H (IntMulTM.Contracts.W8.solveFwdBarrett q H Ys.size μ a c Ys) →
      NotEntry rIn → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
      S (.inl 0) = blkE Ys.toList ++ rIn → S (.inl 2) = natSyms q ++ r2 →
      S (.inl 3) = natSyms H ++ r3 → S (.inl 4) = natSyms μ ++ r4 →
      S (.inl 5) = intSyms a ++ r5 → S (.inl 6) = intSyms c ++ r6 →
      Runs P S (Function.update (Function.update S (.inl 0) rIn) (.inl 1)
          (blkE (IntMulTM.Contracts.W8.solveFwdBarrett q H Ys.size μ a c Ys).toList ++
            S (.inl 1)))
        (fun _ => True) (C * (Ys.size * (Mul (solW H) + H + 1) + (H + 1) ^ 2))

/-- **Nyquist column core.** Named stacks: `0` IN (consumed down to `rIn`), `1` OUT (result
pushed, first entry on top), `2` `q`, `3` `H`, `4` `μ`, `5` `k = log₂ t1` (naturals), `6` divisor
`a` (signed), `7` `alt_q` (one entry, read only). All parameter stacks are restored. -/
def W9f_nyqCore (Mul : ℕ → ℕ) : Prop :=
  MContract Unit 8 48 Unit fun _ m _ C _ P =>
    ∀ (q H μ k : ℕ) (a : ℤ) (alt : ℤ × ℤ) (Ys : Array (ℤ × ℤ))
      (rIn r2 r3 r4 r5 r6 r7 : List Sym) (S : Loc 8 m → List Sym),
      Ys.size = 2 ^ k → 1 ≤ k → q + 2 ≤ H → 0 < a → (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a →
      bitLen a.natAbs ≤ H → ArrW H Ys → EntryW H alt →
      IntMulTM.Contracts.W8.zPartNyqBound q H a Ys (Ys.size - 1) →
      ArrW H (IntMulTM.Contracts.W8.solveNyqBarrett q H Ys.size k μ a Ys alt) →
      NotEntry rIn → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
      S (.inl 0) = blkE Ys.toList ++ rIn → S (.inl 2) = natSyms q ++ r2 →
      S (.inl 3) = natSyms H ++ r3 → S (.inl 4) = natSyms μ ++ r4 →
      S (.inl 5) = natSyms k ++ r5 → S (.inl 6) = intSyms a ++ r6 →
      S (.inl 7) = entrySyms alt ++ r7 →
      Runs P S (Function.update (Function.update S (.inl 0) rIn) (.inl 1)
          (blkE (IntMulTM.Contracts.W8.solveNyqBarrett q H Ys.size k μ a Ys alt).toList ++
            S (.inl 1)))
        (fun _ => True) (C * (Ys.size * (Mul (solW H) + H + k + 1) + (H + 1) ^ 2))

/-- **Entry mover.** All entries of stack `0` (down to a non-entry `r0`) are moved one at a time
onto stack `1`, so they arrive in reverse order (each entry keeps its own symbol order). -/
def W9f_moveEntries : Prop :=
  MContract Unit 2 8 Unit fun _ m _ C _ P =>
    ∀ (xs : List (ℤ × ℤ)) (r0 : List Sym) (S : Loc 2 m → List Sym), NotEntry r0 →
      S (.inl 0) = blkE xs ++ r0 →
      Runs P S (Function.update (Function.update S (.inl 0) r0) (.inl 1)
          (blkE xs.reverse ++ S (.inl 1))) (fun _ => True)
        (C * ((blkE xs).length + 1))

end WP.W9f
