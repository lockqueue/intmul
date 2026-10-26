import SubNLogN.Math.Networks.Proofs.Counting

/-!
# Networks: [OAI26] (7), the absolute label-dimension sum (`Lemma6AbsSumStmt`)

`Lemma6AbsSumStmt` (`Networks/Labels.lean`; [OAI26, §3.3, (7)]): at `h = 100`,
`Σ_w Σ_{e ∈ edges w} |dim lab(e.2) − dim lab(e.1)| = W m − 2N + 2L` for both networks
(`L_b = I·h·h`, `L_c = I·(h+1)·h`).

Proved here (`lemma6AbsSum_of`) from two explicit hypotheses, the per-role soundness of the label
dimensions (`AbsDimSoundBitStmt`, `AbsDimSoundComplexStmt`, discharged by the cell geometry in
`Lemma6Bit.lean`): for every role `w` the per-role sum equals the name-level class sum
`classAbsDimSum 100 (classOf w)`, defined like `Cell.classDimSum` with `|Δ|` of the cell-dimension
sums of the head and tail labels (`edgeAbsDim`).

Proof plan.
1. Kernel evaluation of the eight class sums at `h = 100` (`decide +kernel`): `X, Y ↦ m − 1`,
   `side j ↦ m`, `center j ↦ m + 2h` (`m = 10⁶`).
2. Class counting `Cell.sumClassOf{Bit,Complex}_holds` (`Proofs/Counting.lean`) weighs the classes
   by `N, N` and, per stage, `v²·v·z` (side) and `v²·c` (centre), `c = h` resp. `h + 1`.
3. The resulting numeral identities `2N(m−1) + 3(v³z·m + v²c·(m + 2h)) = W m − 2N + 2·I·c·h` are
   checked by `norm_num`.
-/

namespace SubNLogN.Math.Networks

namespace AbsSumAux

open Cell

/-- Dimension of a name-level label as the sum of the dimensions of its cells (mentioned names
`R`). -/
def labelDim (h : ℕ) (R : Fin 3 → List (Fin 2)) (L : ALabel) : ℕ :=
  ((cells R L).map (cellDim h R)).sum

/-- `|dim head − dim tail|` of a name-level edge, both labels as cell sums over the names of the
edge (`coordNames [t, hd]`, as in `Cell.edgeDim`). -/
def edgeAbsDim (h : ℕ) (t hd : ALabel) : ℕ :=
  Int.natAbs ((labelDim h (coordNames [t, hd]) hd : ℤ) - labelDim h (coordNames [t, hd]) t)

/-- Sum of `|Δ dim|` over the edges of a class (mirrors `Cell.classDimSum`). -/
def classAbsDimSum (h : ℕ) (c : RClass) : ℕ :=
  (((classLabels c).zip (classLabels c).tail).map fun e => edgeAbsDim h e.1 e.2).sum

/-- CONTRACT (cell geometry): per-role soundness of the bit label dimensions at `h = 100`. -/
def AbsDimSoundBitStmt : Prop :=
  ∀ w : Role .bit 100,
    ((edges w).map fun e =>
        Int.natAbs ((Module.finrank ℚ (labB e.2) : ℤ) - Module.finrank ℚ (labB e.1))).sum =
      classAbsDimSum 100 (classOf w)

/-- CONTRACT (cell geometry): per-role soundness of the binary label dimensions at
`h = 100`. -/
def AbsDimSoundComplexStmt : Prop :=
  ∀ w : Role .complex 100,
    ((edges w).map fun e =>
        Int.natAbs ((Module.finrank (ZMod 2) (labC e.2) : ℤ) -
          Module.finrank (ZMod 2) (labC e.1))).sum =
      classAbsDimSum 100 (classOf w)

/-- Kernel evaluation: `X` wires gain `m − 1`. -/
theorem classAbsDimSum_X : classAbsDimSum 100 .X = 999999 := by decide +kernel

/-- Kernel evaluation: `Y` wires gain `m − 1`. -/
theorem classAbsDimSum_Y : classAbsDimSum 100 .Y = 999999 := by decide +kernel

/-- Kernel evaluation: side wires gain `m`. -/
theorem classAbsDimSum_side (j : Stage) : classAbsDimSum 100 (.side j) = 1000000 := by
  cases j <;> decide +kernel

/-- Kernel evaluation: central wires change by `m + 2h` in total (one decreasing edge, `−h`). -/
theorem classAbsDimSum_center (j : Stage) : classAbsDimSum 100 (.center j) = 1000200 := by
  cases j <;> decide +kernel

end AbsSumAux

open AbsSumAux in
/-- [OAI26] (7) at `h = 100` for both networks, from the per-role soundness of the label
dimensions (`AbsDimSoundBitStmt`, `AbsDimSoundComplexStmt`, explicit hypotheses). -/
theorem lemma6AbsSum_of (hB : AbsDimSoundBitStmt) (hC : AbsDimSoundComplexStmt) :
    Lemma6AbsSumStmt := by
  refine ⟨?_, ?_⟩
  · calc _ = ∑ w : Role .bit 100, classAbsDimSum 100 (Cell.classOf w) :=
          Finset.sum_congr rfl fun w _ => hB w
      _ = _ := Cell.sumClassOfBit_holds 100 (classAbsDimSum 100)
      _ = tripleWb 100 * tripleM 100 - 2 * tripleN 100 + 2 * tripleLb 100 := by
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
            classAbsDimSum_X, classAbsDimSum_Y, classAbsDimSum_side, classAbsDimSum_center]
          norm_num [tripleN, tripleV, tripleZb, tripleWb, tripleI, tripleM, tripleLb]
  · calc _ = ∑ w : Role .complex 100, classAbsDimSum 100 (Cell.classOf w) :=
          Finset.sum_congr rfl fun w _ => hC w
      _ = _ := Cell.sumClassOfComplex_holds 100 (classAbsDimSum 100)
      _ = tripleWc 100 * tripleM 100 - 2 * tripleN 100 + 2 * tripleLc 100 := by
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
            classAbsDimSum_X, classAbsDimSum_Y, classAbsDimSum_side, classAbsDimSum_center]
          norm_num [tripleN, tripleV, tripleZc, tripleWc, tripleI, tripleM, tripleLc]

end SubNLogN.Math.Networks
