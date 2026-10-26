import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Encoding

/-!
# Specification: Unconditional Sub-`n log n` Integer Multiplication on a Multi-Stack Turing Machine

This file states the unconditional headline theorems of the `SubNLogN` Lean 4 formalization (Section 8, `sec:lean`).
It imports only `Mathlib.Computability.TuringMachine.Computable` and
`Mathlib.Computability.Encoding`, uses no custom axioms, no `sorry`, no `notation`, `macro`,
`syntax`, `instance`, `attribute`, or `set_option` declarations, and states all complexity bounds
in pure `ℕ` and `ℤ` arithmetic so that any reader can inspect them line by line.

## 1. Machine Model and Encodings

* **Machine model:** Mathlib's `Turing.FinTM2`, bundled as `Turing.TM2ComputableInTime`, with
  the explicit finiteness requirement `∀ k, Finite (M.tm.Γ k)` on every stack alphabet.
  A `k`-stack machine over finite alphabets and a standard multitape Turing machine simulate each
  other with `O(1)` slowdown.
* **Input encoding:** `encodeNatPair (a, b) = bits(a) ++ [sep] ++ bits(b)` over the 3-symbol
  alphabet `PairSym`, where `bits` is Mathlib's little-endian binary `Computability.encodeNat`
  (no leading zeros, `0 ↦ []`).
* **Output encoding:** Mathlib's `Computability.encodingNatBool` (`encodeNat` over `Bool`).
* **Time bound:** For input bit-length `L = |bits a| + |bits b| + 1` and exponent `κ = 2^{-κ_exp}`,
  the bound `M.time L ≤ C · L · (log₂ L)^{1 - 2^{-κ_exp}}` is stated without real-number powers as:
    `(M.time L) ^ (2 ^ κ_exp) ≤ (C * L) ^ (2 ^ κ_exp) * (Nat.log2 L) ^ (2 ^ κ_exp - 1)`.

## 2. Headline Structure (`IntMulSubNLogN` and Component Modules `S1`–`S5`)

* **Primary `TM2` acceptance headlines:**
  - `IntMulSubNLogN (κ_exp : ℕ := 46)`
  - `Headline_TM2_SubNLogN_46`: `κ = 2^{-46}` (`C₁ = 14` parameter-exposed Walsh machine; Theorems 1 and 2, Table 6)
  - `Headline_TM2_SubNLogN_47`: `κ = 2^{-47}` (matching the `C₁ = 20` row of Remark 7.3, Table 10 (`tab:all-rows`);
    deduced from `_46` by `intMulSubNLogN_mono`; row slack checked in `S5/Schedule.lean`)
  - `Headline_TM2_SubNLogN_56`: `κ = 2^{-56}` (matching the printed-interface row of Remark 7.3 (`rem:printed-optimal`),
    Table 10; deduced from `_46` by `intMulSubNLogN_mono`; row slack checked in `S5/Schedule.lean`)
  - `Headline_TM2_LittleO_NLogN`: `M.time L = o(L log₂ L)` on a finite-alphabet `TM2` machine
* **Component module headlines (`S1`–`S5`, historical module identifiers kept for stability):**
  `Headline_S1`–`Headline_S4` are lightweight pure-`ℕ`/`ℤ` arithmetic and finite-algebraic sanity checks
  accompanying the full value-level and `TM2` proofs in `SubNLogN/{Math,Machine,Assembly}` (indexed in
  Table 7 of Section 8 (`sec:lean`)); `Headline_S5_ScheduleAndMain` packages the four unconditional `TM2` bounds:
  - `Headline_S1_TripleNetworks_h100`: Closed-form `h = 100` (`m = 10^6`) network counts, deficits, guard bounds,
    scalar restoration, and `gcd(5, 6) = 1` accompanying `[OAI26, §3]`, Fact 3.4 (`fact:oai-networks`), Definition A.1
    (`def:fixed-network-premises`), Proposition A.2 (`prop:deficits`), and Lemma A.6 (full proofs in `SubNLogN/Math/Networks/`).
  - `Headline_S2_TapeTransfer`: Three elementary `ℤ`/`ℕ` identities (3-step shear, exact role-split division, and
    Euclidean floor-division remainder bound) accompanying Appendix A (`app:parameter-transfer`); full `TM2` stream,
    interchange, and toward-zero `Q_q` layer kernels are proved in `SubNLogN/Machine/{K1,AppC}/` and `Math/Common/Grid.lean`.
  - `Headline_S3_WalshAndDirectFFT`: Six finite `2 × 2` Gaussian-integer, `Bool` XOR-swap, and modular-reflection
    identities accompanying Lemma 5.1 (`lem:walsh-select`), Lemma 5.4 (`lem:cnot`), and Lemma 5.7 (`lem:walsh-involutions`);
    full proofs of Theorem 5.8 (`thm:positional-perm`) and Theorem 6.5 (`thm:direct-fft`) live in `SubNLogN/{Math,Machine}/`.
  - `Headline_S4_BridgePrecision`: Four closed-form integer exponent and rational-enclosure inequalities accompanying
    the master precision margin (Theorem 4.7 (`thm:bridge-precision`)) and two-call root recovery (Proposition 7.2
    (`prop:root-packing`)); full analytical and `TM2` bridge proofs live in `SubNLogN/{Math/Bridge,Machine/Bridge,Machine/Tables}/`.
  - `Headline_S5_ScheduleAndMain`: Conjunction of the four unconditional `TM2` acceptance bounds (`_46`, `_47`, `_56`,
    and `LittleO`, proved in `S5/TopObligation.lean`; closed-form parameter-row slacks for Table 6 (`tab:walsh-rows`),
    Remark 7.3 (`rem:printed-optimal`), and Table 10 (`tab:all-rows`) are checked separately in `S5/Schedule.lean`).
-/

namespace SubNLogN

open Computability

/-! ### 1. Input/Output Encodings and Primary `TM2` Headlines -/

/-- Input alphabet: a bit, or the separator between the two operands. -/
inductive PairSym
  | bit (b : Bool)
  | sep
  deriving DecidableEq, Fintype

/-- Read a bit back (the separator has none). -/
def PairSym.toBool? : PairSym → Option Bool
  | .bit b => some b
  | .sep => none

/-- `encodeNatPair (a, b) = bits(a) ++ sep :: bits(b)`, with Mathlib's little-endian `encodeNat`. -/
def encodeNatPair (p : ℕ × ℕ) : List PairSym :=
  (encodeNat p.1).map PairSym.bit ++ PairSym.sep :: (encodeNat p.2).map PairSym.bit

/-- Split a word at its first separator. -/
def splitSep : List PairSym → Option (List Bool × List Bool)
  | [] => none
  | .sep :: rest => some ([], rest.filterMap PairSym.toBool?)
  | .bit b :: rest => (splitSep rest).map fun xy => (b :: xy.1, xy.2)

/-- Decoder for `encodeNatPair`. -/
def decodeNatPair (l : List PairSym) : Option (ℕ × ℕ) :=
  (splitSep l).map fun xy => (decodeNat xy.1, decodeNat xy.2)

theorem filterMap_toBool?_map_bit (R : List Bool) :
    (R.map PairSym.bit).filterMap PairSym.toBool? = R := by
  induction R with
  | nil => rfl
  | cons b R ih => simp [PairSym.toBool?, ih]

theorem splitSep_append (L R : List Bool) :
    splitSep (L.map PairSym.bit ++ PairSym.sep :: R.map PairSym.bit) = some (L, R) := by
  induction L with
  | nil => simp only [List.map_nil, List.nil_append, splitSep, filterMap_toBool?_map_bit]
  | cons b L ih => simp [splitSep, ih]

theorem decodeNatPair_encodeNatPair (p : ℕ × ℕ) :
    decodeNatPair (encodeNatPair p) = some p := by
  simp [decodeNatPair, encodeNatPair, splitSep_append, decode_encodeNat]

/-- The input encoding as a Mathlib `Encoding`: binary `a`, separator, binary `b`, over the
3-symbol alphabet `PairSym`. -/
def encNatPair : Encoding (ℕ × ℕ) PairSym where
  encode := encodeNatPair
  decode := decodeNatPair
  decode_encode := decodeNatPair_encodeNatPair

theorem encNatPair_encode_length (a b : ℕ) :
    (encNatPair.encode (a, b)).length = (encodeNat a).length + (encodeNat b).length + 1 := by
  simp [encNatPair, encodeNatPair]
  omega

/-- **Primary unconditional `TM2` acceptance statement (`IntMulSubNLogN`).**
For a given dyadic saving exponent `κ = 2^{-κ_exp}`, there exists a multi-stack Turing machine `M`
with finite alphabets on every stack that computes `(a, b) ↦ a * b` under `encNatPair` /
`encodingNatBool` and halts on every input of length `L ≥ N₀` within time
`O(L · (log₂ L)^{1 - 2^{-κ_exp}})`, expressed in pure `ℕ` without real-number imports as:
  `(M.time L) ^ (2 ^ κ_exp) ≤ (C * L) ^ (2 ^ κ_exp) * (Nat.log2 L) ^ (2 ^ κ_exp - 1)`. -/
def IntMulSubNLogN (κ_exp : ℕ := 46) : Prop :=
  ∃ M : Turing.TM2ComputableInTime encNatPair.encode encodingNatBool.encode
      (fun p : ℕ × ℕ => p.1 * p.2),
    (∀ k, Finite (M.tm.Γ k)) ∧
    ∃ C N₀ : ℕ, 0 < C ∧ ∀ L ≥ N₀,
      (M.time L) ^ (2 ^ κ_exp) ≤ (C * L) ^ (2 ^ κ_exp) * (Nat.log2 L) ^ (2 ^ κ_exp - 1)

/-- **Headline 1 (`κ = 2^{-46}`):** Unconditional sub-`n log n` integer multiplication on `TM2`
via the `C₁ = 14` parameter-exposed Walsh route (Theorem 1 (`thm:main`), Theorem 2 (`thm:lean`)). -/
def Headline_TM2_SubNLogN_46 : Prop := IntMulSubNLogN 46

/-- **Headline 2 (`κ = 2^{-47}`):** Unconditional sub-`n log n` integer multiplication on `TM2` at `κ = 2^{-47}`
(matching the `C₁ = 20` row of Remark 7.3 (`rem:printed-optimal`), Table 10 (`tab:all-rows`); deduced from `κ = 2^{-46}` by exponent monotonicity, row slack in `S5/Schedule.lean`). -/
def Headline_TM2_SubNLogN_47 : Prop := IntMulSubNLogN 47

/-- **Headline 3 (`κ = 2^{-56}`):** Unconditional sub-`n log n` integer multiplication on `TM2` at `κ = 2^{-56}`
(matching the printed-interface row of Remark 7.3 (`rem:printed-optimal`), Table 10 (`tab:all-rows`); deduced from `κ = 2^{-46}` by exponent monotonicity, row slack in `S5/Schedule.lean`). -/
def Headline_TM2_SubNLogN_56 : Prop := IntMulSubNLogN 56

/-- **Headline 4 (`o(n log n)`):** Unconditional little-`o(n log n)` integer multiplication on `TM2`:
there exists a finite-alphabet `TM2` multiplier `M` such that for every integer factor `K ≥ 1`,
`K * M.time L ≤ L * Nat.log2 L` holds for all sufficiently large input lengths `L`. -/
def Headline_TM2_LittleO_NLogN : Prop :=
  ∃ M : Turing.TM2ComputableInTime encNatPair.encode encodingNatBool.encode
      (fun p : ℕ × ℕ => p.1 * p.2),
    (∀ k, Finite (M.tm.Γ k)) ∧
    ∀ K : ℕ, 0 < K → ∃ N₀ : ℕ, ∀ L ≥ N₀,
      K * M.time L ≤ L * Nat.log2 L

/-! ### 2. Component S1: Finite Triple Networks and Network Certificates at `h = 100` -/

/-- Number of 3-element subsets of `[h]`: `v = C(h, 3) = h(h-1)(h-2)/6`. -/
def tripleV (h : ℕ) : ℕ := h * (h - 1) * (h - 2) / 6

/-- Number of triple pairs per bank: `N = v^3`. -/
def tripleN (h : ℕ) : ℕ := (tripleV h) ^ 3

/-- Dimension of the 3-tensor factor space: `m = h^3`. -/
def tripleM (h : ℕ) : ℕ := h ^ 3

/-- Number of single-axis invocations across the 3 stages: `I = 3 v^2`. -/
def tripleI (h : ℕ) : ℕ := 3 * (tripleV h) ^ 2

/-- Bit-network neighbor count per triple (`|S ∩ T| = 1`): `z_b = 3 C(h-3, 2)`. -/
def tripleZb (h : ℕ) : ℕ := 3 * ((h - 3) * (h - 4) / 2)

/-- Complex-network neighbor count per triple (`|S ∩ T| ∈ {0, 2}`): `z_c = C(h-3, 3) + 3(h-3)`. -/
def tripleZc (h : ℕ) : ℕ := (h - 3) * (h - 4) * (h - 5) / 6 + 3 * (h - 3)

/-- Total role count of the bit triple network: `W_b = 2N + I(v z_b + h)`. -/
def tripleWb (h : ℕ) : ℕ := 2 * tripleN h + tripleI h * (tripleV h * tripleZb h + h)

/-- Central rank parameter of the bit triple network: `L_b = I · h · h`. -/
def tripleLb (h : ℕ) : ℕ := tripleI h * h * h

/-- Total edge-rank sum of the bit triple network: `s_b = W_b m + 2 L_b - N`. -/
def tripleSb (h : ℕ) : ℕ := tripleWb h * tripleM h + 2 * tripleLb h - tripleN h

/-- Total role count of the complex triple network: `W_c = 2N + I(v z_c + (h + 1))`. -/
def tripleWc (h : ℕ) : ℕ := 2 * tripleN h + tripleI h * (tripleV h * tripleZc h + (h + 1))

/-- Central dimension parameter of the complex triple network: `L_c = I · (h + 1) · h`. -/
def tripleLc (h : ℕ) : ℕ := tripleI h * (h + 1) * h

/-- Total residual-dimension sum of the complex triple network: `s_c = W_c m + 2 L_c - 2N`. -/
def tripleSc (h : ℕ) : ℕ := tripleWc h * tripleM h + 2 * tripleLc h - 2 * tripleN h

/-- Guard-bound quantity `E_net = 64 (W_c + m + 1)^3` (`[OAI26, §5.4]`, `(eq:walsh-guard-constants)`). -/
def guardEnet (h : ℕ) : ℕ := 64 * (tripleWc h + tripleM h + 1) ^ 3

/-- Guard-bound quantity `B_net = s_c + E_net` (`[OAI26, §5.4]`, `(eq:walsh-guard-constants)`). -/
def guardBnet (h : ℕ) : ℕ := tripleSc h + guardEnet h

/-- Guard constant `C_0 = 128 m B_net^2` (`[OAI26, §5.4]`, `(eq:walsh-guard-constants)`). -/
def guardC0 (h : ℕ) : ℕ := 128 * tripleM h * (guardBnet h) ^ 2

/-- State of an abstract Lemma 5 of `[OAI26]` invocation `(x, y, a, c)` over an additive group/module where
`jv` represents the side path `J(V(x))` and `rg` represents the center path `R(G(x))`.
Executing the 8 forward steps `(-J, -R, +V, +G, +R, +J, -G, -V)` in order updates `(x, y, a, c)`:
1. `-J`: `y ↦ y - j_a`
2. `-R`: `y ↦ y - r_c`
3. `+V`: `a ↦ a + v_x` (`j_a ↦ j_a + jv`)
4. `+G`: `c ↦ c + g_x` (`r_c ↦ r_c + rg`)
5. `+R`: `y ↦ y + (r_c + rg)`
6. `+J`: `y ↦ y + (j_a + jv)`
7. `-G`: `c ↦ (c + g_x) - g_x = c`
8. `-V`: `a ↦ (a + v_x) - v_x = a`. -/
def lemma5ForwardState (x y a c j_a r_c v_x g_x jv rg : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  let y1 := y - j_a
  let y2 := y1 - r_c
  let a3 := a + v_x
  let j_a3 := j_a + jv
  let c4 := c + g_x
  let r_c4 := r_c + rg
  let y5 := y2 + r_c4
  let y6 := y5 + j_a3
  let c7 := c4 - g_x
  let a8 := a3 - v_x
  (x, y6, a8, c7)

/-- **Component S1 Headline (`Headline_S1_TripleNetworks_h100`):**
Closed-form `ℕ`/`ℤ` arithmetic and scalar-step checks for the `h = 100` (`m = 10^6`) triple-network parameters
of `[OAI26, §3]` (full finite-network certificates are proved in `SubNLogN/Math/Networks/`; orbit and
intersection-cancellation checks also appear in `S1/{Orbits,Lemma5}.lean`), consisting of the 15 conjuncts:
1. Exact role and rank/residual sums `W_b, s_b, W_c, s_c` matching Definition A.1 (`def:fixed-network-premises`) and Table 8 (`app:cert-closed`);
2. Strict rank savings `s_b < W_b m` and `s_c < W_c m` with exact differences
   `W_b m - s_b = 2659138713000000` and `W_c m - s_c = 6871402692000000`;
3. Certified deficit inequalities (Proposition A.2 (`prop:deficits`)) for `τ = 1 - 2^{-40}` (`L = 14`),
   `σ = 1 - 2^{-42}` (`L = 14`), and the printed `1 - 2^{-50}` (`L = 20`);
4. Guard exponent certificate `m^{10} < B_net ≤ m^{11}` (`ν_net = 11`; eq. (`eq:walsh-guard-constants`)), validating both `C₁ = 14` and
   `C₁ = 20` since `14 ≥ ν_net + 3`;
5. Lemma 5 of `[OAI26]` 8-step scalar restoration (`lemma5ForwardState x y a c j_a r_c v_x g_x jv rg = (x, y + jv + rg, a, c)`)
   for arbitrary initial auxiliary contents `a, c, j_a, r_c` over `ℤ`;
6. Prime radix coprimality `Nat.gcd 5 6 = 1` (Lemma A.6 (`lem:transfer-shear`)): every denominator in `ℤ[1/6]` has prime support
   in `{2, 3}`, so `6` (and every `{2, 3}`-smooth denominator) is coprime to any power `5^b` of `q_rad = 5`. -/
def Headline_S1_TripleNetworks_h100 : Prop :=
  tripleM 100 = 1000000 ∧
  tripleWb 100 = 177176569091445000000 ∧
  tripleSb 100 = 177176569088785861287000000 ∧
  tripleWb 100 * tripleM 100 - tripleSb 100 = 2659138713000000 ∧
  tripleWc 100 = 1873807244643542670000 ∧
  tripleSc 100 = 1873807244636671267308000000 ∧
  tripleWc 100 * tripleM 100 - tripleSc 100 = 6871402692000000 ∧
  (tripleWb 100 * tripleM 100 - tripleSb 100) * (2 ^ 40) > 14 * (tripleWb 100 * tripleM 100) ∧
  (tripleWc 100 * tripleM 100 - tripleSc 100) * (2 ^ 42) > 14 * (tripleWc 100 * tripleM 100) ∧
  (tripleWb 100 * tripleM 100 - tripleSb 100) * (2 ^ 50) > 20 * (tripleWb 100 * tripleM 100) ∧
  (tripleWc 100 * tripleM 100 - tripleSc 100) * (2 ^ 50) > 20 * (tripleWc 100 * tripleM 100) ∧
  (tripleM 100) ^ 10 < guardBnet 100 ∧
  guardBnet 100 ≤ (tripleM 100) ^ 11 ∧
  (∀ x y a c j_a r_c v_x g_x jv rg : ℤ,
    lemma5ForwardState x y a c j_a r_c v_x g_x jv rg = (x, y + jv + rg, a, c)) ∧
  Nat.gcd 5 6 = 1

/-! ### 3. Component S2: Network-to-Tape Transfer on `TM2` (Appendix A) -/

/-- The 3-step elementary shear primitive (the shear primitive of Lemma A.6 (`lem:transfer-shear`)) on a pair `(h, d)`:
1. `d ↦ d + h`
2. `(h, d) ↦ (d, h)`
3. `d ↦ h - d`.
This sends `(h, d)` to `(h + d, d)` using a single field interchange. -/
def shearStepPair (h d : ℤ) : ℤ × ℤ :=
  let d1 := d + h
  let h2 := d1
  let d2 := h
  let d3 := h2 - d2
  (h2, d3)

/-- Componentwise Euclidean integer division by `2^s` (historical identifier `truncationTowardZeroPair`):
computes `(re / 2^s, im / 2^s)` via Lean's `Int.ediv` (floor toward `-∞`, not toward-zero truncation `Q_q` and not
disk-preserving on negative inputs; actual `Q_q` (`eq:walsh-truncation`) and disk preservation are `truncC` in
`SubNLogN/Math/Common/Grid.lean` and `SubNLogN/Machine/AppC/`). -/
def truncationTowardZeroPair (re im : ℤ) (s : ℕ) : ℤ × ℤ :=
  (re / (2 ^ s : ℤ), im / (2 ^ s : ℤ))

/-- **Component S2 Headline (`Headline_S2_TapeTransfer`):**
Three elementary `ℤ`/`ℕ` arithmetic checks accompanying Appendix A (`app:parameter-transfer`)
(the full finite-alphabet `TM2` stream, interchange, and `Q_q` layer kernels are proved in
`SubNLogN/Machine/{K1,AppC}/`):
1. The 3-step scalar shear identity `shearStepPair h d = (h + d, d)` on `ℤ × ℤ`
   (accompanying Lemma A.6 (`lem:transfer-shear`));
2. Exact integer division and zero remainder `(W * g) / W = g ∧ (W * g) % W = 0` for `W > 0`
   (accompanying the cyclic role-split count of Proposition A.7 (`prop:transfer11`));
3. Euclidean floor-division remainder bound on `(re, im) ∈ ℤ × ℤ`: since `0 ≤ x - (x / 2^s) * 2^s < 2^s`
   under `Int.ediv`, `(re - (re / 2^s) * 2^s)^2 + (im - (im / 2^s) * 2^s)^2 < 2 * (2^s)^2` (note: this uses
   `Int.ediv`, whereas true toward-zero `Q_q` and disk preservation are proved in `Math/Common/Grid.lean`). -/
def Headline_S2_TapeTransfer : Prop :=
  (∀ h d : ℤ, shearStepPair h d = (h + d, d)) ∧
  (∀ W g : ℕ, 0 < W → (W * g) / W = g ∧ (W * g) % W = 0) ∧
  (∀ re im : ℤ, ∀ s : ℕ,
    (re - (truncationTowardZeroPair re im s).1 * (2 ^ s : ℤ)) ^ 2 +
    (im - (truncationTowardZeroPair re im s).2 * (2 ^ s : ℤ)) ^ 2 < 2 * ((2 ^ s : ℤ) ^ 2))

/-! ### 4. Component S3: Three-Layer Walsh Permutations and Direct Complex Tensor FFT (Sections 5–6) -/

/-- Exact Gaussian integer representation `ℤ × ℤ` (`a + b i`) with multiplication
`(a₁ + b₁ i)(a₂ + b₂ i) = (a₁ a₂ - b₁ b₂) + (a₁ b₂ + b₁ a₂) i`. -/
def gaussMul (z w : ℤ × ℤ) : ℤ × ℤ :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- Action of `2 H_0 = [[1, 1], [1, -1]]` on a pair of Gaussian integers `(z₀, z₁)`. -/
def twoH0 (p : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((p.1.1 + p.2.1, p.1.2 + p.2.2), (p.1.1 - p.2.1, p.1.2 - p.2.2))

/-- Action of `S = diag(1, i)` on a pair of Gaussian integers `(z₀, z₁)`. -/
def phaseS (p : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  (p.1, (-p.2.2, p.2.1))

/-- Action of `CZ(c)` on a pair of Gaussian integers `(z₀, z₁)` for control bit `c : Bool`. -/
def phaseCZ (c : Bool) (p : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  if c then (p.1, (-p.2.1, -p.2.2)) else p

/-- Three-stage XOR swap on `Bool × Bool`:
`(x, y) ↦ (x ^^ y, y) ↦ (x ^^ y, y ^^ (x ^^ y)) ↦ ((x ^^ y) ^^ (y ^^ (x ^^ y)), y ^^ (x ^^ y)) = (y, x)`. -/
def xorSwapThreeStage (x y : Bool) : Bool × Bool :=
  let x1 := xor x y
  let y2 := xor y x1
  let x3 := xor x1 y2
  (x3, y2)

/-- **Component S3 Headline (`Headline_S3_WalshAndDirectFFT`):**
Six finite algebraic and combinatorial identities accompanying Sections 5–6 (`sec:walsh`, `sec:direct-fft`)
(full value-level and `TM2` proofs of positional permutations, Theorem 5.8 (`thm:positional-perm`), and the
direct complex tensor FFT with `< 12 ℓ · 2^{-q}` error, Theorem 6.5 (`thm:direct-fft`), live in
`SubNLogN/{Math/Walsh,Machine/Walsh,Machine/FFT}/`; see also `S3/DirectFFT.lean`):
1. **Three-layer `2 × 2` selection identities (Lemma 5.1 (`lem:walsh-select`)):**
   - Wanted position (`(2 H_0)^3 = 2 (2 H_0)`, i.e. `H_0^3 = (1/2) H_0`),
   - Unwanted position (`(2 H_0 ∘ S)^3 = 2(1 + i) I`, i.e. `(H_0 S)^3 = ((1 + i)/4) I`);
2. **Controlled `2 × 2` bit flip identities (Lemma 5.4 (`lem:cnot`)):**
   - For `c = false`, `(2 H_0) (CZ false (2 H_0 (z₀, z₁))) = (2 z₀, 2 z₁)` (`2 H_0 I H_0 = 2 I`),
   - For `c = true`, `(2 H_0) (CZ true (2 H_0 (z₀, z₁))) = (2 z₁, 2 z₀)` (`2 H_0 Z H_0 = 2 X`);
3. **Three-stage XOR swap (Lemma 5.7 (`lem:walsh-involutions`)):**
   `xorSwapThreeStage x y = (y, x)` for all `x y : Bool`;
4. **Two-involution cycle decomposition (Lemma 5.7 (`lem:walsh-involutions`)):** on every cycle `j ↦ (j + 1) % n` of
   length `n ≥ 1`, the reflection maps `I₀(k) = (n - k % n) % n` and `I₁(k) = (n + 1 - k % n) % n` are
   involutions on `j < n` whose composition `I₁ (I₀ j)` equals `(j + 1) % n`. -/
def Headline_S3_WalshAndDirectFFT : Prop :=
  (∀ p : (ℤ × ℤ) × (ℤ × ℤ),
    twoH0 (twoH0 (twoH0 p)) =
      ((2 * (twoH0 p).1.1, 2 * (twoH0 p).1.2), (2 * (twoH0 p).2.1, 2 * (twoH0 p).2.2))) ∧
  (∀ p : (ℤ × ℤ) × (ℤ × ℤ),
    twoH0 (phaseS (twoH0 (phaseS (twoH0 (phaseS p))))) =
      ((2 * (p.1.1 - p.1.2), 2 * (p.1.1 + p.1.2)),
       (2 * (p.2.1 - p.2.2), 2 * (p.2.1 + p.2.2)))) ∧
  (∀ p : (ℤ × ℤ) × (ℤ × ℤ),
    twoH0 (phaseCZ false (twoH0 p)) =
      ((2 * p.1.1, 2 * p.1.2), (2 * p.2.1, 2 * p.2.2))) ∧
  (∀ p : (ℤ × ℤ) × (ℤ × ℤ),
    twoH0 (phaseCZ true (twoH0 p)) =
      ((2 * p.2.1, 2 * p.2.2), (2 * p.1.1, 2 * p.1.2))) ∧
  (∀ x y : Bool, xorSwapThreeStage x y = (y, x)) ∧
  (∀ n j : ℕ, 0 < n → j < n →
    let i0 := fun k => (n - k % n) % n
    let i1 := fun k => (n + 1 - k % n) % n
    i0 (i0 j) = j ∧ i1 (i1 j) = j ∧ i1 (i0 j) = (j + 1) % n)

/-! ### 5. Component S4: `d`-Dimensional Fractional-Shift Bridge and Precision Contract (Section 4) -/

/-- Working precision schedule `P(p, k, lg_pk2) = 2p + 12k + 32 lg_pk2 + 256` (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:schedule`)). -/
def bridgeWorkingP (p k lg_pk2 : ℕ) : ℕ :=
  2 * p + 12 * k + 32 * lg_pk2 + 256

/-- Grid precision `q = P + 2` (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:schedule`)). -/
def bridgeGridQ (p k lg_pk2 : ℕ) : ℕ :=
  bridgeWorkingP p k lg_pk2 + 2

/-- Component width `w = q + 2 = P + 4` (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:schedule`)). -/
def bridgeCompW (p k lg_pk2 : ℕ) : ℕ :=
  bridgeGridQ p k lg_pk2 + 2

/-- **Component S4 Headline (`Headline_S4_BridgePrecision`):**
Four closed-form integer exponent and rational-enclosure inequalities accompanying Theorem 4.7
(`thm:bridge-precision`) and Proposition 7.2 (`prop:root-packing`) (full analytical and `TM2` bridge, solver,
and table proofs live in `SubNLogN/Math/Bridge/` and `SubNLogN/Machine/{Bridge,Tables}/`):
1. **Master precision margin (`eq:master-margin`):** for all `p ≥ 8`, `k ≥ 1`, `1 ≤ d ≤ k`, and
   `lg_pk2 ≥ 1` with `bridgeWorkingP p k lg_pk2 + 1 ≤ 2 ^ (lg_pk2 + 6)`,
   `2 ^ 14 * d * (bridgeWorkingP p k lg_pk2 + 1) * (2 ^ (3 * k)) * 2 ^ (p + 12) ≤ 2 ^ (bridgeGridQ p k lg_pk2)`;
2. **Rational `√2` upper enclosure and bridge constant (`eq:bridge-total`):** `2 * 10^{14} < 14142136^2`
   (i.e. `√2 < 14142136 / 10^7`) and the scaled numeral inequality checking
   `1.4142136 / 8 + 2^{-12} + 2^{-23} < 177021 / 10^6 = 0.177021`;
3. **Two-call root recovery numeral check (Proposition 7.2 (`prop:root-packing`)):** the closed inequality
   `12391 * 2 < 10000 * 128`, checking that an accumulated pre-rounding bound `< 1.2391 · 2^{-p}`,
   after scaling by `2^{2b + 2k - 1} = 2^{p - 7}`, is `< 1.2391 / 128 < 1 / 2` (the full two-call
   nearest-integer recovery theorem is proved in `SubNLogN/Assembly/RootOK.lean`). -/
def Headline_S4_BridgePrecision : Prop :=
  (∀ p k d lg_pk2 : ℕ,
    8 ≤ p → 1 ≤ k → 1 ≤ d → d ≤ k → 1 ≤ lg_pk2 →
    bridgeWorkingP p k lg_pk2 + 1 ≤ 2 ^ (lg_pk2 + 6) →
    (2 ^ 14) * d * (bridgeWorkingP p k lg_pk2 + 1) * (2 ^ (3 * k)) * (2 ^ (p + 12)) ≤
      2 ^ (bridgeGridQ p k lg_pk2)) ∧
  2 * (10000000 : ℕ) ^ 2 < (14142136 : ℕ) ^ 2 ∧
  (14142136 : ℕ) * (2 ^ 20) + (10000000 : ℕ) * (2 ^ 11 + 1) < (177021 : ℕ) * 10 * (2 ^ 23) ∧
  (12391 : ℕ) * 2 < 10000 * 128

/-! ### 6. Component S5: Schedule, Parameter Certificates and Unconditional `TM2` Assembly (Section 7) -/

/-- **Component S5 Headline (`Headline_S5_ScheduleAndMain`):**
Four-way conjunction of the unconditional `TM2` acceptance bounds proved in `SubNLogN/S5/TopObligation.lean`:
1. `Headline_TM2_SubNLogN_46`: `IntMulSubNLogN 46` (`κ = 2^{-46}`, constructed via the `C₁ = 14`
   parameter-exposed Walsh machine of Theorem 1 (`thm:main`), Theorem 2 (`thm:lean`), Table 6 (`tab:walsh-rows`));
2. `Headline_TM2_SubNLogN_47`: `IntMulSubNLogN 47` (`κ = 2^{-47}`, deduced from `Headline_TM2_SubNLogN_46`
   by exponent monotonicity `intMulSubNLogN_mono` in `S5/Dispatcher.lean`);
3. `Headline_TM2_SubNLogN_56`: `IntMulSubNLogN 56` (`κ = 2^{-56}`, deduced from `Headline_TM2_SubNLogN_46`
   by exponent monotonicity `intMulSubNLogN_mono` in `S5/Dispatcher.lean`);
4. `Headline_TM2_LittleO_NLogN`: `M.time L = o(L log₂ L)` (deduced from `Headline_TM2_SubNLogN_46`
   by `intMulSubNLogN_46_implies_littleO` in `S5/Dispatcher.lean`).

Companion parameter-row checks (proved separately in `SubNLogN/S5/Schedule.lean` and `SubNLogN/Math/Cost/Row46.lean`,
not conjuncts of `Headline_S5_ScheduleAndMain` itself; see Table 6 (`tab:walsh-rows`), Remark 7.3
(`rem:printed-optimal`), Table 10 (`tab:all-rows`), Sections 7.4–7.5):
* **`C₁ = 14` Walsh row (`κ = 2^{-46}`):** `ε = 1/15`, `β = 1/64`, `c = 2^{-50}`, `τ = 1 - 2^{-40}`,
  `σ = 1 - 2^{-42}`, `λ = 1 - 63 · 2^{-48}`, `λ' = 1 - 31 · 2^{-47}`, giving `g_lay - κ = 1 / (480 · 2^{42}) > 0`
  (this row is instantiated end-to-end on the machine via `SubNLogN/Math/Cost/{Row46,WalshOKW8}.lean`);
* **`C₁ = 20` Walsh row (`κ = 2^{-47}`):** `ε = 1/21`, `β = 1/8`, `c = 2^{-44}`, `τ = 1 - 2^{-40}`,
  `σ = 1 - 2^{-42}`, `λ = 1 - 7 · 2^{-45}`, `λ' = 1 - 3 · 2^{-44}`, `g_lay - κ = 1 / (224 · 2^{42}) > 0` (`walsh_row_47_admissible_and_slack`);
* **Printed-interface Walsh row (`κ = 2^{-56}`):** `C₁ = 20`, `ε = 1/21`, `β = 1/2`, `c = 2^{-53}`,
  `τ = σ = 1 - 2^{-50}`, `λ = 1 - 129 · 2^{-58}`, `λ' = 1 - 63 · 2^{-57}`, `g_lay - κ = 1 / 2^{57} > 0` (`walsh_row_56_admissible_and_slack`);
* **Bluestein comparison rows (`κ = 2^{-84}, 2^{-85}, 2^{-108}, 2^{-182}`):** gap-slack checks in
  `bluestein_rows_slack` (Table 10 (`tab:all-rows`), Appendix C (`app:bluestein`)). -/
def Headline_S5_ScheduleAndMain : Prop :=
  Headline_TM2_SubNLogN_46 ∧
  Headline_TM2_SubNLogN_47 ∧
  Headline_TM2_SubNLogN_56 ∧
  Headline_TM2_LittleO_NLogN

/-! ### 7. Non-Vacuity and Sanity Checks (`#guard` and `example`) -/

theorem encNatPair_encode_eq (p : ℕ × ℕ) : encNatPair.encode p = encodeNatPair p := rfl

-- Encoding / decoding sanity checks
#guard encodeNatPair (5, 3) == [.bit true, .bit false, .bit true, .sep, .bit true, .bit true]
#guard encodeNatPair (0, 0) == [.sep]
#guard decodeNatPair [.bit false, .bit true, .sep, .bit true] == some (2, 1)
#guard decodeNatPair (encodeNatPair (123456789, 987654321)) == some (123456789, 987654321)
#guard encodeNat 6 == [false, true, true]

-- Component S1 sanity checks: exact h = 100 triple network integers and deficit inequalities
#guard tripleV 100 == 161700
#guard tripleM 100 == 1000000
#guard tripleZb 100 == 13968
#guard tripleZc 100 == 147731
#guard tripleWb 100 == 177176569091445000000
#guard tripleSb 100 == 177176569088785861287000000
#guard tripleWb 100 * tripleM 100 - tripleSb 100 == 2659138713000000
#guard tripleWc 100 == 1873807244643542670000
#guard tripleSc 100 == 1873807244636671267308000000
#guard tripleWc 100 * tripleM 100 - tripleSc 100 == 6871402692000000
#guard (tripleWb 100 * tripleM 100 - tripleSb 100) * (2 ^ 40) > 14 * (tripleWb 100 * tripleM 100)
#guard (tripleWc 100 * tripleM 100 - tripleSc 100) * (2 ^ 42) > 14 * (tripleWc 100 * tripleM 100)
#guard (tripleM 100) ^ 10 < guardBnet 100
#guard guardBnet 100 ≤ (tripleM 100) ^ 11
#guard Nat.gcd 5 6 == 1

-- Component S2 & S3 sanity checks
#guard shearStepPair 17 29 == (46, 29)
#guard twoH0 (twoH0 (twoH0 ((1, 0), (0, 1)))) == ((2, 2), (2, -2))
#guard twoH0 (phaseS (twoH0 (phaseS (twoH0 (phaseS ((1, 0), (0, 1))))))) == ((2, 2), (-2, 2))
#guard twoH0 (phaseCZ false (twoH0 ((3, -2), (5, 7)))) == ((6, -4), (10, 14))
#guard twoH0 (phaseCZ true (twoH0 ((3, -2), (5, 7)))) == ((10, 14), (6, -4))
#guard xorSwapThreeStage true false == (false, true)
#guard xorSwapThreeStage false true == (true, false)

-- Component S4 & S5 sanity checks
#guard 2 * (10000000 : ℕ) ^ 2 < (14142136 : ℕ) ^ 2
#guard (14142136 : ℕ) * (2 ^ 20) + (10000000 : ℕ) * (2 ^ 11 + 1) < (177021 : ℕ) * 10 * (2 ^ 23)
#guard (12391 : ℕ) * 2 < 10000 * 128

end SubNLogN
