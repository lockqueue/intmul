import SubNLogN.Math.Networks.Framed
import SubNLogN.Math.Networks.StreamModel

/-!
# Appendix A at the math level (I): shear (Lemma A.6 (`lem:transfer-shear`)), interchanges (Proposition A.7 (`prop:transfer11`), Lemma A.8 (`lem:transfer12`)), packed addition (Lemma A.9 (`lem:transfer13`))

Appendix A: Lemma A.6 (`lem:transfer-shear`), Proposition A.7 (`prop:transfer11`),
Lemma A.8 (`lem:transfer12`), and Lemma A.9 (`lem:transfer13`). Contracts are `def …Stmt : Prop` (Prop-contract style; proofs go to
`Proofs/`). Functional identities are stated on address maps; cost statements are the recurrences of the abstract stream model
(`StreamModel.lean`) and their solutions. No tape code.
-/

namespace SubNLogN.Math.Networks

variable {m Q : ℕ}

/-! ## Lemma A.6 (`lem:transfer-shear`): rational shears via [OAI26] Lemma 9 -/

/-- Two address groups `H, D ∈ (ℤ/Q)^m`. -/
abbrev HD (m Q : ℕ) := (Fin m → ZMod Q) × (Fin m → ZMod Q)

/-- The address shear `(H, D) ↦ (H + A D, D)` (Lemma A.6 (`lem:transfer-shear`), [OAI26, Lemma 10, §4.1]). -/
def shearHD (A : Matrix (Fin m) (Fin m) (ZMod Q)) (x : HD m Q) : HD m Q := (x.1 + A.mulVec x.2, x.2)

/-- Linear change of the `D` group. -/
def linD (E : Matrix (Fin m) (Fin m) (ZMod Q)) (x : HD m Q) : HD m Q := (x.1, E.mulVec x.2)

/-- Linear change of the `H` group. -/
def linH (E : Matrix (Fin m) (Fin m) (ZMod Q)) (x : HD m Q) : HD m Q := (E.mulVec x.1, x.2)

/-- The pivot triple of a one at `(i, j)` (Lemma A.6 (`lem:transfer-shear`)):
`D_j ← D_j + H_i`, interchange `(H_i, D_j)`, `D_j ← H_i − D_j`. Only the middle step interchanges. -/
def pivotTriple (i j : Fin m) (x : HD m Q) : HD m Q :=
  let x₁ : HD m Q := (x.1, Function.update x.2 j (x.2 j + x.1 i))
  let x₂ : HD m Q := (Function.update x₁.1 i (x₁.2 j), Function.update x₁.2 j (x₁.1 i))
  (x₂.1, Function.update x₂.2 j (x₂.1 i - x₂.2 j))

/-- CONTRACT (Lemma A.6 (`lem:transfer-shear`), pivot). The pivot triple sends `(h, d)` to `(h + d, d)` at `(H_i, D_j)`. -/
def PivotTripleEqStmt : Prop :=
  ∀ (m Q : ℕ) (i j : Fin m) (x : HD m Q),
    pivotTriple i j x = (Function.update x.1 i (x.1 i + x.2 j), x.2)

/-- CONTRACT (Lemma A.6 (`lem:transfer-shear`)). If `A = E₁ Π E₂` over
`ℤ/Q` with `E₁ E₁' = 1`, `E₂ E₂' = 1`, and `Π` has its ones exactly at the pivot list (distinct rows,
distinct columns), then `Φ_A = linD E₂' ∘ linH E₁ ∘ (pivot triples) ∘ linH E₁' ∘ linD E₂`; the number
of interchanges is the number of ones of `Π`. -/
def ShearFactorizationStmt : Prop :=
  ∀ (m Q : ℕ) (A E₁ E₁' E₂ E₂' Pm : Matrix (Fin m) (Fin m) (ZMod Q)),
    E₁ * E₁' = 1 → E₂ * E₂' = 1 → A = E₁ * Pm * E₂ →
    ∀ piv : List (Fin m × Fin m), (piv.map Prod.fst).Nodup → (piv.map Prod.snd).Nodup →
      (∀ i j, Pm i j = if (i, j) ∈ piv then 1 else 0) →
      shearHD A = linD E₂' ∘ linH E₁ ∘ (piv.foldr (fun p f => pivotTriple p.1 p.2 ∘ f) id) ∘
        linH E₁' ∘ linD E₂

/-- CONTRACT (Lemma A.6 (`lem:transfer-shear`), streaming triangular maps). A lower-triangular `E` acts on `D` by updating
`D_{m-1}, …, D_0` in descending order, each from itself (×`E_ii`) and the earlier coordinates
(which still hold their original values): each update is one `Elem.shift` plus one `Elem.unit`. -/
def LinDLowerTriStreamingStmt : Prop :=
  ∀ (m Q : ℕ) (E : Matrix (Fin m) (Fin m) (ZMod Q)), (∀ i j, i < j → E i j = 0) → ∀ x : HD m Q,
    linD E x = (List.finRange m).reverse.foldl
      (fun y i => (y.1, Function.update y.2 i (∑ j, E i j * y.2 j))) x

/-- Reduction mod `Q` is multiplicative on `q`-integral matrices (needed to specialize [OAI26] Lemma 9). -/
def RatModMatrixMulStmt : Prop :=
  ∀ (m q b : ℕ), q.Prime → ∀ A B : Matrix (Fin m) (Fin m) ℚ,
    (∀ i j, QIntegral q (A i j)) → (∀ i j, QIntegral q (B i j)) →
    (A * B).map (ratMod (q ^ b)) = A.map (ratMod (q ^ b)) * B.map (ratMod (q ^ b))

/-! ## Proposition A.7 (`prop:transfer11`) and Lemma A.8 (`lem:transfer12`): interchanges -/

/-- CONTRACT (Proposition A.7 (`prop:transfer11`)). The three shears `D ← D − H`, `H ← H + D`,
`D ← H − D` interchange the two groups; the outer two target the later group (`linD`-type, streaming),
only the middle one uses the bit network (`BitArrayCorollaryStmt`). -/
def ThreeShearsSwapStmt : Prop :=
  ∀ (m Q : ℕ) (x : HD m Q),
    (fun y : HD m Q => (y.1, y.1 - y.2)) ((fun y : HD m Q => (y.1 + y.2, y.2))
      ((fun y : HD m Q => (y.1, y.2 - y.1)) x)) = (x.2, x.1)

/-- CONTRACT (Proposition A.7 (`prop:transfer11`) recurrence). If `0 ≤ a < M^τ` (`M > 1`, `τ > 0`),
every normalized cost sequence with `F₀ ≤ c` and `F_{k+1} ≤ a F_k + c` satisfies `F_k ≤ C M^{kτ}`,
with `C` depending only on `a, M, τ, c`. With `a = s_b/W_b`, `M = m` this is `O(V e^τ)`, `e = m^k`. -/
def InterchangeRecurrenceStmt : Prop :=
  ∀ (a M τ c : ℝ), 1 < M → 0 ≤ a → a < M ^ τ → 0 < τ → 0 ≤ c →
    ∃ C : ℝ, ∀ F : ℕ → ℝ, F 0 ≤ c → (∀ k, F (k + 1) ≤ a * F k + c) →
      ∀ k : ℕ, F k ≤ C * M ^ ((k : ℝ) * τ)

/-- CONTRACT (Lemma A.8 (`lem:transfer12`) pieces). With `m ≥ 2` and `τ > 0` there is `C`
such that for every `e ≥ 1` the base-`m` pieces of `e` cost `Σ_j a_j m^{jτ} ≤ C e^τ`. -/
def PiecesCostStmt : Prop :=
  ∀ (mm : ℕ), 2 ≤ mm → ∀ τ : ℝ, 0 < τ →
    ∃ C : ℝ, ∀ e : ℕ, 1 ≤ e →
      (((Nat.digits mm e).zipIdx).map fun p => (p.1 : ℝ) * (mm : ℝ) ^ ((p.2 : ℝ) * τ)).sum ≤
        C * (e : ℝ) ^ τ

/-- CONTRACT (Lemma A.8 (`lem:transfer12`) padding). Padding a row range `R ≥ W^k` to the next
multiple of `W^k` less than doubles it. -/
def RowPaddingLtStmt : Prop :=
  ∀ R Wk : ℕ, 0 < Wk → Wk ≤ R → Wk * ((R + Wk - 1) / Wk) < 2 * R

/-! ## Lemma A.9 (`lem:transfer13`): packed selected-bit addition -/

/-- One line of the eight-operation program on `(u, w)` with control `c` (Lemma A.9 (`lem:transfer13`)):
`(target is u?, sign, parity tested, parity value)`. -/
def eightOps : List (Bool × ℤ × ℕ) :=
  [(true, -1, 0), (false, -1, 0), (true, 1, 0), (false, 1, 0),
   (false, 1, 1), (true, 1, 1), (false, -1, 1), (true, -1, 1)]

/-- Run the eight operations on integers `(u, w)` with control `c ∈ {0,1}`; each predicate tests the
current value of the other coordinate modulo 2. -/
def runEight (c : ℤ) (uw : ℤ × ℤ) : ℤ × ℤ :=
  eightOps.foldl (fun p op =>
    if op.1 then (p.1 + op.2.1 * c * (if p.2 % 2 = op.2.2 then 1 else 0), p.2)
    else (p.1, p.2 + op.2.1 * c * (if p.1 % 2 = op.2.2 then 1 else 0))) uw

/-- CONTRACT (Lemma A.9 (`lem:transfer13`) scalar program). For `c = 0` the program is the
identity; for `c = 1` it flips the low bit of `u` and restores `w`: `(u, w) ↦ (u + 1 − 2(u mod 2), w)`. -/
def RunEightSpecStmt : Prop :=
  ∀ u w : ℤ, runEight 0 (u, w) = (u, w) ∧ runEight 1 (u, w) = (u + 1 - 2 * (u % 2), w)

/-- Bit `j` of a natural number. -/
def bitAt (x j : ℕ) : ℕ := (x / 2 ^ j) % 2

/-- Packed line `op` on three `L`-bit chunks `(x, y, z)` with selected positions `j_i = ρ + iK`,
`i < f − 1`: the target chunk (`y` if `op.1`, else `z`) is cyclically shifted by
`ε Σ_i 2^{j_i} [x_{j_i} = 1][other_{j_i} = parity]` modulo `2^L` (Lemma A.9 (`lem:transfer13`)). -/
def packedLine (L K ρ f : ℕ) (op : Bool × ℤ × ℕ) (xyz : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let x := xyz.1; let y := xyz.2.1; let z := xyz.2.2
  let other := if op.1 then z else y
  let off : ℤ := op.2.1 * ∑ i ∈ Finset.range (f - 1),
    (2 : ℤ) ^ (ρ + i * K) * (if bitAt x (ρ + i * K) = 1 ∧ bitAt other (ρ + i * K) = op.2.2 then 1 else 0)
  let tgt := if op.1 then y else z
  let new := ((tgt + off) % (2 : ℤ) ^ L).toNat
  if op.1 then (x, new, z) else (x, y, new)

/-- The composite `S₀` of the eight packed lines. -/
def packedS0 (L K ρ f : ℕ) (xyz : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  eightOps.foldl (fun p op => packedLine L K ρ f op p) xyz

/-- The ideal map `T₀`: `y_{j_i} ← y_{j_i} ⊕ x_{j_i}` for `i < f − 1`. -/
def packedT0 (K ρ f : ℕ) (xyz : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (xyz.1, Nat.xor xyz.2.1 (∑ i ∈ Finset.range (f - 1), 2 ^ (ρ + i * K) * bitAt xyz.1 (ρ + i * K)),
    xyz.2.2)

/-- Guard values of segment `i` of a chunk: its `K − 1` bits above the selected bit. -/
def guardVal (K ρ i v : ℕ) : ℕ := (v / 2 ^ (ρ + i * K + 1)) % 2 ^ (K - 1)

/-- The good set (complement of `B`, Lemma A.9 (`lem:transfer13`)): all used guards of `y` and `z`
lie in `[10, 2^{K−1} − 11]`. -/
def packedGood (K ρ f : ℕ) (xyz : ℕ × ℕ × ℕ) : Prop :=
  ∀ i < f - 1, 10 ≤ guardVal K ρ i xyz.2.1 ∧ guardVal K ρ i xyz.2.1 + 11 ≤ 2 ^ (K - 1) ∧
    10 ≤ guardVal K ρ i xyz.2.2 ∧ guardVal K ρ i xyz.2.2 + 11 ≤ 2 ^ (K - 1)

/-- CONTRACT (Lemma A.9 (`lem:transfer13`) agreement off `B`). For `K ≥ 6`, `L = fK`,
`ρ < K` and chunks below `2^L`, on the good set the eight packed shifts equal the ideal selected-bit
XOR `T₀`, and `T₀` preserves the good set. -/
def PackedAgreeStmt : Prop :=
  ∀ (L K ρ f : ℕ), 6 ≤ K → L = f * K → ρ < K →
    ∀ xyz : ℕ × ℕ × ℕ, xyz.1 < 2 ^ L → xyz.2.1 < 2 ^ L → xyz.2.2 < 2 ^ L → packedGood K ρ f xyz →
      packedS0 L K ρ f xyz = packedT0 K ρ f xyz ∧ packedGood K ρ f (packedT0 K ρ f xyz)

open Classical in
/-- CONTRACT (Lemma A.9 (`lem:transfer13`) exceptional set, eq. (`eq:transfer-packed`)). Among all `(x, y, z) ∈ [2^L]³`
at most a fraction `80(f−1)2^{−K}` is bad: `2^K · |B| ≤ 80 (f−1) · 2^{3L}`. -/
def PackedBadCardStmt : Prop :=
  ∀ (L K ρ f : ℕ), 6 ≤ K → L = f * K → ρ < K →
    2 ^ K * ((Finset.range (2 ^ L) ×ˢ Finset.range (2 ^ L) ×ˢ Finset.range (2 ^ L)).filter
      (fun xyz => ¬ packedGood K ρ f xyz)).card ≤ 80 * (f - 1) * 2 ^ (3 * L)

end SubNLogN.Math.Networks
