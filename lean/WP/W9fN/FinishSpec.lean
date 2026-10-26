import Contracts.W9.Post

/-!
# WP.W9f (Nyquist finish) — interface of the S2 piece `W9f_nyqFinish`

Shared interface between `WP.W9fN` (`W9f_nyqCore`) and `WP.W9fNF` (`W9f_nyqFinish`
implementation). It imports only `Contracts.W9.Post`, so it can be imported into any
package (namespace `WP.W9f`, like W9f's `Spec.lean`; no name is shared with that file).

* `nyqOut k alt Z`: the part of `W8.solveNyqBarrett` after the zPart array (verbatim body, with
  `t1 := Z.size`).
* `solveNyqBarrett_eq_nyqOut`: `W8.solveNyqBarrett q H t1 k μ a Ys alt = nyqOut k alt Z` for the
  zPart array `Z = W8.zPartNyqBarrett q H μ a Ys (t1 - 1)`, when `1 ≤ t1`.
* `W9f_nyqFinish`: the machine contract. Named stacks:
  - `0`: the Z block, last entry on top, consumed down to `rZ`;
  - `1`: OUT, the result is pushed, first entry on top;
  - `2`: `k`, a natural, restored;
  - `3`: `alt`, one entry, read only, restored exactly.

  The hypothesis on `rZ` is W9f's `NotEntry rZ`, unfolded.
-/

namespace WP.W9f

open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul

/-- The part of `W8.solveNyqBarrett` after the zPart array `Z` (verbatim body, `t1 := Z.size`). -/
def nyqOut (k : ℕ) (alt : ℤ × ℤ) (Z : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  let alt_part : ℤ × ℤ := sumRangePair (fun v => gAltTerm v (read1D Z v)) Z.size
  let diff : ℤ × ℤ := (divRoundPow2 (alt.1 - alt_part.1) k, divRoundPow2 (alt.2 - alt_part.2) k)
  (runSequentialScanSteps (fun u1 => gAdd (read1D Z u1) (gAltTerm u1 diff)) Z.size).outTape

theorem zPartNyqBarrett_size (q H : ℕ) (μ a : ℤ) (Ys : Array (ℤ × ℤ)) (n : ℕ) :
    (IntMulTM.Contracts.W8.zPartNyqBarrett q H μ a Ys n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [IntMulTM.Contracts.W8.zPartNyqBarrett, ih]

theorem solveNyqBarrett_eq_nyqOut (q H t1 k : ℕ) (μ a : ℤ) (Ys : Array (ℤ × ℤ)) (alt : ℤ × ℤ)
    (h : 1 ≤ t1) :
    IntMulTM.Contracts.W8.solveNyqBarrett q H t1 k μ a Ys alt =
      nyqOut k alt (IntMulTM.Contracts.W8.zPartNyqBarrett q H μ a Ys (t1 - 1)) := by
  have hs : (IntMulTM.Contracts.W8.zPartNyqBarrett q H μ a Ys (t1 - 1)).size = t1 := by
    rw [zPartNyqBarrett_size]
    omega
  simp only [IntMulTM.Contracts.W8.solveNyqBarrett, nyqOut, hs]

/-- **Nyquist finish.** Named stacks:
* `0`: the Z block `blkE Z.toList.reverse` (last entry on top), consumed down to `rZ`;
* `1`: OUT (result pushed, first entry on top);
* `2`: `k = log₂ |Z|` (natural);
* `3`: `alt` (one entry, read only).

Stacks `2` and `3` are restored. -/
def W9f_nyqFinish : Prop :=
  MContract Unit 4 48 Unit fun _ m _ C _ P =>
    ∀ (H k : ℕ) (alt : ℤ × ℤ) (Z : Array (ℤ × ℤ)) (rZ r2 r3 : List Sym) (S : Loc 4 m → List Sym),
      Z.size = 2 ^ k → 1 ≤ k → ArrW (H + 1) Z → EntryW H alt →
      (∀ s, rZ.head? = some s → s ≠ Sym.pos ∧ s ≠ Sym.neg) → TermOK r2 →
      S (.inl 0) = blkE Z.toList.reverse ++ rZ → S (.inl 2) = natSyms k ++ r2 →
      S (.inl 3) = entrySyms alt ++ r3 →
      Runs P S (Function.update (Function.update S (.inl 0) rZ) (.inl 1)
          (blkE (nyqOut k alt Z).toList ++ S (.inl 1))) (fun _ => True)
        (C * (Z.size * (H + k + 1) + (H + 1) ^ 2))

#assert_std_axioms zPartNyqBarrett_size solveNyqBarrett_eq_nyqOut

end WP.W9f
