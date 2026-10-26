/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Records
import SubNLogN.Machine.MulBig.Contract

/-!
# `SubNLogN.Machine` contracts, AR (`Contracts/Arith.lean`): coefficientwise record arithmetic

**Scope (honest summary).** This file contains pure integer definitions and kernel contract
*statements* in the `KContract` shape (`Contracts/Layout.lean`). No kernel is implemented and no
contract is proved here. The only proofs are `decide` sanity checks of the pure definitions. The
value-level lemmas relating the integer operations to `truncC` / `quantC`
(`SubNLogN/Math/Common/Grid.lean:52,65`) are proved in `SubNLogN/Machine/Arith/Value.lean`.

Paper references:
* `Q_p` (truncation toward zero) and `Quant_q` (nearest, ties to even): Definition 3.1 (`def:grid`).
* Normalized DIF butterfly: exact half-sum and half-difference, then `Q_q`
  (Theorem 6.5, `thm:direct-fft`; the step `H_0` of Section 6.2, eq. `eq:dif`).
* Disk-preserving products: four exact integer products, then `Q_q`
  (Lemma 6.2, `lem:disk-product`), used in the round protocol
  `z ↦ Q_q(D̃ Q_q(Hz))` (Section 6.4, eq. `eq:round-protocol`).
* Bridge output: exact scaling by a power of two, one rounding `Quant_{p+2}`
  (Section 4.4, step (5), and Theorem 4.7, `thm:bridge-precision`).

## Conventions (decisions recorded here)
* **Data.** Complex record arrays `carrSyms w v` (`Contracts/Records.lean`). A coefficient is
  `twosBits w re ++ twosBits w im`, each field LSB first; a record is its coefficients followed
  by `sep`; first record on top. Records may have any number of coefficients (no shape is
  needed for coefficientwise maps). Two-input kernels need aligned arrays (`CAligned`).
* **Integer level.** At fractional precision `F` a stored pair `c` denotes `gridVal F c`.
  * `truncShiftC s` maps precision `F + s` to `F` by `Q_F`.
  * `quantShiftC s` does the same with `Quant_F`.
  * `halfSumC`, `halfDiffC` are `Q_F((a ± b)/2)` at a fixed precision.
  * `cmulTruncC s` maps precisions `F₁, F₂` to `F₁ + F₂ - s` by `Q` of the exact product.
* **Parameters.** Widths and shift amounts are runtime data: `natSyms` on named parameter stacks,
  restored, with `TermOK` rests (as in `K3ShiftStmt`, `Contracts/Streams.lean:314`).
* **Stacks.** Every source array is consumed (its stack becomes `rest`, `BlkTerm rest`). Every
  result array is pushed on top of its destination's old content (W4 style). All other named
  stacks and all private scratch stacks end unchanged (restored convention). The exception is
  the multiplication kernels: they assume the *clean* convention (`KClean S`, all private
  scratch empty on entry, hence on exit), because `MulBigContract`
  (`SubNLogN/Machine/MulBig/Contract.lean`) needs 76 empty scratch stacks.
* **Guards.** Every width is `≥ 1`, every input component fits its width and every output
  component fits its width (`CArrFits`), stated explicitly. For `HalfSumDiffStmt` the output fit
  is automatic, since `|tdiv (a ± b) 2|` stays in the `w`-bit range.
* **Costs.** `C * (explicit bound)`, `C` fixed before all runtime parameters and data.
  `V = cvol w v` is the stack volume of an array (`= #records + 2·w·#coefficients`). The
  additive width terms (`w1 + w2`, `bitLen s`) pay for reading the parameter counters; they are
  absorbed by `V` whenever the array has a coefficient and `bitLen s ≤ w1`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

/-! ## 1. Pure integer operations -/

/-- Truncation toward zero of `z / 2^s`: the integer form of `Q` (Definition 3.1, `def:grid`). -/
def tdivPow (z : ℤ) (s : ℕ) : ℤ := z.tdiv (2 ^ s)

/-- Nearest rounding of `z / 2^s`, ties to even: the integer form of `Quant`
(Definition 3.1, `def:grid`). Here `z / 2 ^ s` is floor division and `z % 2 ^ s ∈ [0, 2^s)` its
remainder. This matches `roundHalfEven` of `SubNLogN/Math/Common/Grid.lean:55`. -/
def rnePow (z : ℤ) (s : ℕ) : ℤ :=
  if 2 * (z % 2 ^ s) < 2 ^ s then z / 2 ^ s
  else if 2 ^ s < 2 * (z % 2 ^ s) then z / 2 ^ s + 1
  else if z / 2 ^ s % 2 = 0 then z / 2 ^ s else z / 2 ^ s + 1

/-- Nearest rounding of `z / 2^s`, ties toward `+∞` ("half up"): `⌊(z + 2^{s-1}) / 2^s⌋` for
`s ≥ 1`, and `z` for `s = 0` (in `ℤ`, `2 ^ 0 / 2 = 0`). Its error is at most half a unit:
`2·|rhuPow z s · 2^s - z| ≤ 2^s` (`Arith/Value.lean`). -/
def rhuPow (z : ℤ) (s : ℕ) : ℤ := (z + 2 ^ s / 2) / 2 ^ s

/-- Coefficientwise `Q` by `2^s`: truncation toward zero of both components. -/
def truncShiftC (s : ℕ) (c : CInt) : CInt := (tdivPow c.1 s, tdivPow c.2 s)

/-- Coefficientwise `Quant` by `2^s`: nearest rounding (ties to even) of both components. -/
def quantShiftC (s : ℕ) (c : CInt) : CInt := (rnePow c.1 s, rnePow c.2 s)

/-- Coefficientwise nearest rounding by `2^s`, ties toward `+∞`, of both components. -/
def roundHalfUpShiftC (s : ℕ) (c : CInt) : CInt := (rhuPow c.1 s, rhuPow c.2 s)

/-- Coefficientwise exact multiplication by `2^s` (left shift) of both components. -/
def shlC (s : ℕ) (c : CInt) : CInt := (c.1 * 2 ^ s, c.2 * 2 ^ s)

/-- Upper output of the normalized butterfly at a fixed precision: `Q((a + b)/2)`,
componentwise `tdiv (a + b) 2`. -/
def halfSumC (a b : CInt) : CInt := truncShiftC 1 (a.1 + b.1, a.2 + b.2)

/-- Lower output of the normalized butterfly at a fixed precision, before its phase:
`Q((a - b)/2)`, componentwise `tdiv (a - b) 2`. -/
def halfDiffC (a b : CInt) : CInt := truncShiftC 1 (a.1 - b.1, a.2 - b.2)

/-- Exact coefficientwise sum. -/
def caddC (a b : CInt) : CInt := (a.1 + b.1, a.2 + b.2)

/-- Exact coefficientwise difference. -/
def csubC (a b : CInt) : CInt := (a.1 - b.1, a.2 - b.2)

/-- Exact complex product of numerators: `(a₀b₀ - a₁b₁, a₀b₁ + a₁b₀)`. -/
def cmulC (a b : CInt) : CInt := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- Exact complex product, then truncation toward zero of both components by `2^s`
(Lemma 6.2, `lem:disk-product`). -/
def cmulTruncC (s : ℕ) (a b : CInt) : CInt := truncShiftC s (cmulC a b)

/-- Coefficientwise map on a record array. -/
def mapC (f : CInt → CInt) (v : List (List CInt)) : List (List CInt) := v.map (List.map f)

/-- Coefficientwise combination of two aligned record arrays. -/
def zipC (f : CInt → CInt → CInt) (u v : List (List CInt)) : List (List CInt) :=
  List.zipWith (List.zipWith f) u v

/-- Two record arrays are aligned: the same number of records, and equal lengths of
corresponding records. -/
def CAligned (u v : List (List CInt)) : Prop :=
  List.Forall₂ (fun cs ds => cs.length = ds.length) u v

/-- Total number of coefficients of a record array. -/
def ncoef (v : List (List CInt)) : ℕ := (v.map List.length).sum

/-- Stack volume of a complex record array at width `w`. It depends only on the shape:
`#records + 2·w·#coefficients`. -/
def cvol (w : ℕ) (v : List (List CInt)) : ℕ := (carrSyms w v).length

/-- Cost unit of one `mulBig` call at size `n` (`mulBigBound x y = mulW (mulBigSize x y)`,
`SubNLogN/Machine/MulBig/Contract.lean`). Since it is monotone in `n`, one product of a `w1`-bit
and a `w2`-bit magnitude costs at most `C·mulW (w1 + w2 + 1)`. -/
def mulW (n : ℕ) : ℕ := n * (Nat.log2 n + 1) + 1

/-! ### Sanity checks (`decide`) -/

example : tdivPow (-5) 1 = -2 ∧ tdivPow 5 1 = 2 ∧ tdivPow (-4) 2 = -1 ∧ tdivPow (-3) 2 = 0 := by
  decide
example : rnePow 5 1 = 2 ∧ rnePow 7 1 = 4 ∧ rnePow (-5) 1 = -2 ∧ rnePow (-7) 1 = -4 ∧
    rnePow 3 2 = 1 ∧ rnePow (-3) 2 = -1 ∧ rnePow 9 0 = 9 := by
  decide
example : rhuPow 5 1 = 3 ∧ rhuPow (-5) 1 = -2 ∧ rhuPow 3 2 = 1 ∧ rhuPow (-3) 2 = -1 ∧
    rhuPow 9 0 = 9 := by
  decide
example : halfSumC (3, -3) (2, 0) = (2, -1) ∧ halfDiffC (3, -3) (2, 0) = (0, -1) := by decide
example : cmulTruncC 1 (1, 2) (3, -1) = (2, 2) := by decide

/-! ## 2. Contracts: one-input coefficientwise kernels -/

/-- **[CONTRACT] AR1, coefficientwise `Q` by `2^s` with a width change** (`truncC` at the integer
level; Definition 3.1, `def:grid`). Every coefficient `(re, im)` of the array, stored at width `w1`, becomes
`(tdiv re 2^s, tdiv im 2^s)`, stored at width `w2`. At the value level this is
`gridVal F (truncShiftC s c) = truncC F (gridVal (F + s) c)` (`Arith/Value.lean`).
* Named stacks (`Fin 5`): `0` the source array (consumed), `1` the destination, `2`/`3`/`4` the
  counters `w1`, `w2`, `s` (restored).
* Guards: `1 ≤ w1`, `1 ≤ w2`, inputs fit `w1` bits, outputs fit `w2` bits.
* Cost `C·(V_in + V_out + w1 + w2 + bitLen s + 1)`, with `V_in = cvol w1 v`, `V_out = cvol w2 v`. -/
def TruncShiftStmt : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (w1 w2 s : ℕ) (v : List (List CInt)) (rest r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      1 ≤ w1 → 1 ≤ w2 → CArrFits w1 v → CArrFits w2 (mapC (truncShiftC s) v) →
      BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = carrSyms w1 v ++ rest → S (.inl 2) = natSyms w1 ++ r2 →
      S (.inl 3) = natSyms w2 ++ r3 → S (.inl 4) = natSyms s ++ r4 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (carrSyms w2 (mapC (truncShiftC s) v) ++ S (.inl 1)))
        (fun _ => True) (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1))

/-- **[CONTRACT] AR3, coefficientwise `Quant` by `2^s` with a width change** (`quantC` at the
integer level; Definition 3.1, `def:grid`; the bridge's final `Quant_{p+2}`, Section 4.4, step (5)).
Every coefficient `(re, im)` at width `w1` becomes `(rnePow re s, rnePow im s)` (nearest, ties to
even) at width `w2`. At the value level `gridVal F (quantShiftC s c) = quantC F (gridVal (F + s) c)`
(`Arith/Value.lean`). Named stacks, guards and cost as in `TruncShiftStmt`. -/
def QuantShiftStmt : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (w1 w2 s : ℕ) (v : List (List CInt)) (rest r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      1 ≤ w1 → 1 ≤ w2 → CArrFits w1 v → CArrFits w2 (mapC (quantShiftC s) v) →
      BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = carrSyms w1 v ++ rest → S (.inl 2) = natSyms w1 ++ r2 →
      S (.inl 3) = natSyms w2 ++ r3 → S (.inl 4) = natSyms s ++ r4 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (carrSyms w2 (mapC (quantShiftC s) v) ++ S (.inl 1)))
        (fun _ => True) (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1))

/-- **[CONTRACT] AR3', coefficientwise nearest rounding by `2^s`, ties toward `+∞`, with a width
change.** Every coefficient `(re, im)` at width `w1` becomes `(rhuPow re s, rhuPow im s)` at width
`w2`, where `rhuPow z s = ⌊(z + 2^{s-1}) / 2^s⌋` (`z` for `s = 0`). This is a nearest rounding with
ties toward `+∞`, not the ties-to-even `Quant` of `QuantShiftStmt`: the error of each component is
at most half a unit of the output grid (`Arith/Value.lean`). Named stacks, guards and cost as in
`TruncShiftStmt`. -/
def RoundHalfUpShiftStmt : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (w1 w2 s : ℕ) (v : List (List CInt)) (rest r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      1 ≤ w1 → 1 ≤ w2 → CArrFits w1 v → CArrFits w2 (mapC (roundHalfUpShiftC s) v) →
      BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = carrSyms w1 v ++ rest → S (.inl 2) = natSyms w1 ++ r2 →
      S (.inl 3) = natSyms w2 ++ r3 → S (.inl 4) = natSyms s ++ r4 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (carrSyms w2 (mapC (roundHalfUpShiftC s) v) ++ S (.inl 1)))
        (fun _ => True) (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1))

/-- **[CONTRACT] AR5, coefficientwise exact left shift by `2^s` with a width change** (used by
the bridge's pre-scaling and output steps, Section 4.4, `sec:bridge-alg`). Every coefficient
`(re, im)` at width `w1` becomes `(re·2^s, im·2^s)` at width `w2`. Named stacks, guards and cost as
in `TruncShiftStmt`; the output guard `CArrFits w2 (mapC (shlC s) v)` makes the shift exact. -/
def ShlStmt : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (w1 w2 s : ℕ) (v : List (List CInt)) (rest r2 r3 r4 : List Sym)
      (S : KLoc (Fin 5) E → List Sym),
      1 ≤ w1 → 1 ≤ w2 → CArrFits w1 v → CArrFits w2 (mapC (shlC s) v) →
      BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = carrSyms w1 v ++ rest → S (.inl 2) = natSyms w1 ++ r2 →
      S (.inl 3) = natSyms w2 ++ r3 → S (.inl 4) = natSyms s ++ r4 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (carrSyms w2 (mapC (shlC s) v) ++ S (.inl 1)))
        (fun _ => True) (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1))

/-! ## 3. Contracts: two-input coefficientwise kernels -/

/-- **[CONTRACT] AR2, normalized butterfly `Q((u ± v)/2)`** (Theorem 6.5, `thm:direct-fft`: "form
the half-sum and half-difference exactly, truncate each to the `P`-grid"). Two aligned arrays `u`,
`v` at width `w` become the arrays `zipC halfSumC u v` (componentwise `tdiv (u + v) 2`) and
`zipC halfDiffC u v` (componentwise `tdiv (u - v) 2`), both at width `w`. At the value level,
`gridVal F (halfSumC a b) = truncC F ((gridVal F a + gridVal F b) / 2)` and the same with `-`
(`Arith/Value.lean`).
* Named stacks (`Fin 5`): `0` the array `u`, `1` the array `v` (both consumed), `2` the
  destination of the half-sums, `3` the destination of the half-differences, `4` the counter `w`
  (restored).
* Guards: `1 ≤ w`, inputs fit `w` bits, `u` and `v` aligned. The outputs fit `w` bits
  automatically.
* Cost `C·(V_u + V_v + w + 1)`; the output volume equals the input volume. -/
def HalfSumDiffStmt : Prop :=
  KContract (Fin 5) Unit fun _ E _ _ _ C P =>
    ∀ (w : ℕ) (u v : List (List CInt)) (ru rv r4 : List Sym) (S : KLoc (Fin 5) E → List Sym),
      1 ≤ w → CArrFits w u → CArrFits w v → CAligned u v →
      BlkTerm ru → BlkTerm rv → TermOK r4 →
      S (.inl 0) = carrSyms w u ++ ru → S (.inl 1) = carrSyms w v ++ rv →
      S (.inl 4) = natSyms w ++ r4 →
      Runs P S
        (Function.update (Function.update (Function.update (Function.update S (.inl 0) ru)
          (.inl 1) rv) (.inl 2) (carrSyms w (zipC halfSumC u v) ++ S (.inl 2)))
          (.inl 3) (carrSyms w (zipC halfDiffC u v) ++ S (.inl 3)))
        (fun _ => True) (C * (cvol w u + cvol w v + w + 1))

/-- **[CONTRACT] AR6, exact coefficientwise sum of two aligned arrays with width changes**
(requested by the bridge's deconvolution solvers). Two aligned arrays `u` (width `w1`) and `v`
(width `w2`) become the array `zipC caddC u v` (componentwise `u + v`) at width `w3`.
* Named stacks (`Fin 6`): `0` the array `u`, `1` the array `v` (both consumed), `2` the
  destination, `3`/`4`/`5` the counters `w1`, `w2`, `w3` (restored).
* Guards: `1 ≤ w1, w2, w3`, inputs fit their widths, `u` and `v` aligned, outputs fit `w3` bits.
* Cost `C·(V_u + V_v + V_out + w1 + w2 + w3 + 1)`, `V_out = cvol w3 u`. -/
def CAddStmt : Prop :=
  KContract (Fin 6) Unit fun _ E _ _ _ C P =>
    ∀ (w1 w2 w3 : ℕ) (u v : List (List CInt)) (ru rv r3 r4 r5 : List Sym)
      (S : KLoc (Fin 6) E → List Sym),
      1 ≤ w1 → 1 ≤ w2 → 1 ≤ w3 → CArrFits w1 u → CArrFits w2 v → CAligned u v →
      CArrFits w3 (zipC caddC u v) →
      BlkTerm ru → BlkTerm rv → TermOK r3 → TermOK r4 → TermOK r5 →
      S (.inl 0) = carrSyms w1 u ++ ru → S (.inl 1) = carrSyms w2 v ++ rv →
      S (.inl 3) = natSyms w1 ++ r3 → S (.inl 4) = natSyms w2 ++ r4 →
      S (.inl 5) = natSyms w3 ++ r5 →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) ru) (.inl 1) rv) (.inl 2)
          (carrSyms w3 (zipC caddC u v) ++ S (.inl 2)))
        (fun _ => True) (C * (cvol w1 u + cvol w2 v + cvol w3 u + w1 + w2 + w3 + 1))

/-- **[CONTRACT] AR6', exact coefficientwise difference** `u - v`. Same shape as `CAddStmt`. -/
def CSubStmt : Prop :=
  KContract (Fin 6) Unit fun _ E _ _ _ C P =>
    ∀ (w1 w2 w3 : ℕ) (u v : List (List CInt)) (ru rv r3 r4 r5 : List Sym)
      (S : KLoc (Fin 6) E → List Sym),
      1 ≤ w1 → 1 ≤ w2 → 1 ≤ w3 → CArrFits w1 u → CArrFits w2 v → CAligned u v →
      CArrFits w3 (zipC csubC u v) →
      BlkTerm ru → BlkTerm rv → TermOK r3 → TermOK r4 → TermOK r5 →
      S (.inl 0) = carrSyms w1 u ++ ru → S (.inl 1) = carrSyms w2 v ++ rv →
      S (.inl 3) = natSyms w1 ++ r3 → S (.inl 4) = natSyms w2 ++ r4 →
      S (.inl 5) = natSyms w3 ++ r5 →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) ru) (.inl 1) rv) (.inl 2)
          (carrSyms w3 (zipC csubC u v) ++ S (.inl 2)))
        (fun _ => True) (C * (cvol w1 u + cvol w2 v + cvol w3 u + w1 + w2 + w3 + 1))

/-! ## 4. Contracts: products with a final truncation (Lemma `lem:disk-product`) -/

/-- **[CONTRACT] AR4, coefficientwise `Q` of exact complex products** (Lemma 6.2,
`lem:disk-product`: "four exact products of `O(q)`-bit integers and `O(q)` further work").
Two aligned arrays `z` (width `w1`) and `θ` (width `w2`) become the array
`zipC (cmulTruncC s) z θ`: each pair `(a, b)` of coefficients becomes
`(tdiv (a₀b₀ - a₁b₁) 2^s, tdiv (a₀b₁ + a₁b₀) 2^s)`, at width `w3`. With `z`, `θ` on the `P`-grid
and `s = P` this is `Q_P(z·θ)` on the `P`-grid (`Arith/Value.lean`).
* Premise: the multiplier contract `MulBigContract` (`SubNLogN/Machine/MulBig/Contract.lean`); the
  constant `C` may depend on the multiplier instance.
* Named stacks (`Fin 7`): `0` the array `z`, `1` the array `θ` (both consumed), `2` the
  destination, `3`/`4`/`5`/`6` the counters `w1`, `w2`, `w3`, `s` (restored).
* **Clean convention**: all private scratch stacks are empty on entry (`KClean S`); by the exact
  final stacks they are empty on exit.
* Guards: `1 ≤ w1, w2, w3`, inputs fit their widths, `z` and `θ` aligned, outputs fit `w3` bits.
* Cost `C·(M·mulW (w1 + w2 + 1) + V_z + V_θ + V_out + (M + 1)·(bitLen s + 1) + w1 + w2 + w3)`,
  `M = ncoef z` (four products per coefficient). -/
def CMulTruncStmt : Prop :=
  MulBigContract →
  KContract (Fin 7) Unit fun _ E _ _ _ C P =>
    ∀ (w1 w2 w3 s : ℕ) (z θ : List (List CInt)) (rz rθ r3 r4 r5 r6 : List Sym)
      (S : KLoc (Fin 7) E → List Sym),
      KClean S → 1 ≤ w1 → 1 ≤ w2 → 1 ≤ w3 → CArrFits w1 z → CArrFits w2 θ → CAligned z θ →
      CArrFits w3 (zipC (cmulTruncC s) z θ) →
      BlkTerm rz → BlkTerm rθ → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
      S (.inl 0) = carrSyms w1 z ++ rz → S (.inl 1) = carrSyms w2 θ ++ rθ →
      S (.inl 3) = natSyms w1 ++ r3 → S (.inl 4) = natSyms w2 ++ r4 →
      S (.inl 5) = natSyms w3 ++ r5 → S (.inl 6) = natSyms s ++ r6 →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (.inl 2)
          (carrSyms w3 (zipC (cmulTruncC s) z θ) ++ S (.inl 2)))
        (fun _ => True)
        (C * (ncoef z * mulW (w1 + w2 + 1) + cvol w1 z + cvol w2 θ + cvol w3 z +
          (ncoef z + 1) * (bitLen s + 1) + w1 + w2 + w3))

/-- Records of a per-record phase array: one coefficient per record. -/
def bcastArr (θ : List CInt) : List (List CInt) := θ.map fun t => [t]

/-- Every coefficient of record `x` of `z` multiplied by the phase `θ[x]`, then `Q` by `2^s`. -/
def cmulTruncBcast (s : ℕ) (z : List (List CInt)) (θ : List CInt) : List (List CInt) :=
  List.zipWith (fun cs t => cs.map fun c => cmulTruncC s c t) z θ

/-- **[CONTRACT] AR4b (optional variant), one phase per record** (Theorem 6.5, `thm:direct-fft`: "the
phase is found by one scan of the table, and it multiplies every coefficient of the record").
Same as `CMulTruncStmt`, except that `θ` holds one coefficient per record (`bcastArr θ`), with
`θ.length = z.length`, and record `x` of the result is `z[x]` with every coefficient `c` replaced
by `cmulTruncC s c θ[x]`. The phase is reused for every coefficient of its record, so the cost
has the per-coefficient term `(M + 1)·(w2 + bitLen s + 1)`. -/
def CMulTruncBcastStmt : Prop :=
  MulBigContract →
  KContract (Fin 7) Unit fun _ E _ _ _ C P =>
    ∀ (w1 w2 w3 s : ℕ) (z : List (List CInt)) (θ : List CInt) (rz rθ r3 r4 r5 r6 : List Sym)
      (S : KLoc (Fin 7) E → List Sym),
      KClean S → 1 ≤ w1 → 1 ≤ w2 → 1 ≤ w3 → CArrFits w1 z → CArrFits w2 (bcastArr θ) →
      z.length = θ.length → CArrFits w3 (cmulTruncBcast s z θ) →
      BlkTerm rz → BlkTerm rθ → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
      S (.inl 0) = carrSyms w1 z ++ rz → S (.inl 1) = carrSyms w2 (bcastArr θ) ++ rθ →
      S (.inl 3) = natSyms w1 ++ r3 → S (.inl 4) = natSyms w2 ++ r4 →
      S (.inl 5) = natSyms w3 ++ r5 → S (.inl 6) = natSyms s ++ r6 →
      Runs P S
        (Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (.inl 2)
          (carrSyms w3 (cmulTruncBcast s z θ) ++ S (.inl 2)))
        (fun _ => True)
        (C * (ncoef z * mulW (w1 + w2 + 1) + cvol w1 z + cvol w2 (bcastArr θ) + cvol w3 z +
          (ncoef z + 1) * (w2 + bitLen s + 1) + w1 + w2 + w3))

end SubNLogN.Machine
