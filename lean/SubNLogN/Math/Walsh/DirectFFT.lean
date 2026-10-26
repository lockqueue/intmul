import SubNLogN.Math.Walsh.Layout

/-!
# Direct FFT: the Bluestein-free middle transform (Theorem 6.5)

Paper: Section 6 (`sec:direct-fft`): eq. (`eq:dif`) in Section 6.2, combined round eq. (`eq:combined-round`) in
Section 6.3, and Theorem 6.5 (`thm:direct-fft`,
Section 6.4).

Value-level part only. The algorithm (`directFFT`) is:
(i) per record, a normalized positive DIF FFT of the `r = 2^ℓ` coefficients with explicit
rounding (`difLevel`: half-sum and half-difference, each truncated by `Q_P`, the lower output
multiplied by its table phase and truncated again), then bit reversal of the coefficient index
(`lastAxisFFT`);
(ii) the positional map `L` (program of Theorem 5.8 at `P`, internally lifted to `P + 8d`,
`d = D + 1`);
(iii) record-axis rounds at named slots `v = ℓ-1, …, 0`, each implementing the round protocol
`z ↦ Q_P(D̃ Q_P(H z))` (eq. (`eq:round-protocol`)): `Q_P(H z)` by a layer call of
Proposition A.11 at precision `P` for chunk rounds (`b₀ ≤ v ≤ ℓ-2`) and by exact individual
butterflies plus one `Q_P` for prefix rounds; `D̃` is the diagonal of table phases
`θ̃_{2J(x)}` (`roundsProg`);
(iv) the positional map `U = (LB)^{-1}`.

Tensor encoding. The shape is `t = (2^{a_0}, …, 2^{a_{D-1}}, 2^ℓ)` (`fftShape`); a tensor
`Idx t → ℂ` corresponds to a record array on the `m₀`-bit cube (`ofTensor`, `toTensor`): bit `v`
of `j_i` sits at position `origPos a i v` of the record address (natural order, axis `0` most
significant, each index most significant bit first) and `j_D` is the coefficient index.

Component contracts are stated as `def …Stmt : Prop` (proved in `Walsh/Proofs/`); the final target is
`theorem direct_fft_of (…) : DirectFFTStmt` from the upstream statements.
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

/-! ## The last axis -/

/-- Coefficient `k` of a vector, `0` outside. -/
def getCoeff {n : ℕ} (w : Fin n → ℂ) (k : ℕ) : ℂ := if h : k < n then w ⟨k, h⟩ else 0

/-- One rounded normalized DIF level `s` (`0 ≤ s < ℓ`) on a coefficient vector of length `2^ℓ`
(proof of Theorem 6.5 (`thm:direct-fft`)): blocks of length `u = 2^{ℓ-s}`, half `h = u/2`; for a pair
`(k, k + h)` at offset `j = k mod u < h` the upper output is `Q_P((w_k + w_{k+h})/2)` and the lower
output is `Q_P(θ̃_{2^{s+1} j} · Q_P((w_k - w_{k+h})/2))` (`θ_{2^{s+1} j} = e^{2πi j/u}`). -/
noncomputable def difLevel (P ℓ s : ℕ) (θt : ℕ → ℂ) (w : Fin (2 ^ ℓ) → ℂ) : Fin (2 ^ ℓ) → ℂ :=
  fun k =>
    if (k : ℕ) % 2 ^ (ℓ - s) < 2 ^ (ℓ - s - 1) then
      truncC P ((getCoeff w k + getCoeff w ((k : ℕ) + 2 ^ (ℓ - s - 1))) / 2)
    else
      truncC P (θt (2 ^ (s + 1) * ((k : ℕ) % 2 ^ (ℓ - s) - 2 ^ (ℓ - s - 1))) *
        truncC P ((getCoeff w ((k : ℕ) - 2 ^ (ℓ - s - 1)) - getCoeff w k) / 2))

/-- The exact DIF level (Section 6.2, eq. (`eq:dif`)): as `difLevel` without truncations and
with exact phases. -/
noncomputable def difLevelExact (ℓ s : ℕ) (w : Fin (2 ^ ℓ) → ℂ) : Fin (2 ^ ℓ) → ℂ :=
  fun k =>
    if (k : ℕ) % 2 ^ (ℓ - s) < 2 ^ (ℓ - s - 1) then
      (getCoeff w k + getCoeff w ((k : ℕ) + 2 ^ (ℓ - s - 1))) / 2
    else
      theta (2 ^ ℓ) (2 ^ (s + 1) * ((k : ℕ) % 2 ^ (ℓ - s) - 2 ^ (ℓ - s - 1))) *
        ((getCoeff w ((k : ℕ) - 2 ^ (ℓ - s - 1)) - getCoeff w k) / 2)

/-- Bit reversal of the `ℓ`-bit integer `k`. -/
def bitRevNat (ℓ k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range ℓ, if k.testBit i then 2 ^ (ℓ - 1 - i) else 0

/-- Bit reversal of the coefficient index (restoration of natural order inside a record). -/
def coeffBitRev {ℓ : ℕ} (w : Fin (2 ^ ℓ) → ℂ) : Fin (2 ^ ℓ) → ℂ :=
  fun k => getCoeff w (bitRevNat ℓ k)

/-- Step (i): rounded DIF on every record (levels `s = 0, …, ℓ-1`), then bit reversal. -/
noncomputable def lastAxisFFT (P ℓ : ℕ) (θt : ℕ → ℂ) {α : Type} (z : RArr α (2 ^ ℓ)) :
    RArr α (2 ^ ℓ) :=
  fun x => coeffBitRev ((List.range ℓ).foldl (fun w s => difLevel P ℓ s θt w) (z x))

/-- Exact counterpart of step (i). -/
noncomputable def lastAxisExact (ℓ : ℕ) {α : Type} (z : RArr α (2 ^ ℓ)) : RArr α (2 ^ ℓ) :=
  fun x => coeffBitRev ((List.range ℓ).foldl (fun w s => difLevelExact ℓ s w) (z x))

/-- The normalized positive DFT `F_r` on every record. -/
noncomputable def lastAxisDFT (ℓ : ℕ) {α : Type} (z : RArr α (2 ^ ℓ)) : RArr α (2 ^ ℓ) :=
  fun x => dft (2 ^ ℓ) (z x)

/-! ## The record axes and the algorithm -/

/-- The butterfly part of round `v`: a layer call (chunk round, `b₀ ≤ v ≤ ℓ-2`, slice of
`walsh_layout_round_slice`) or exact butterflies plus one `Q_P` (prefix round). -/
noncomputable def roundStep (P D ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) : WStep (addrBits a) :=
  if h : 0 < K ∧ layoutB0 ℓ K ≤ v ∧ v + 2 ≤ ℓ then
    WStep.layer P K (prefixLen ℓ K a + (ℓ - 2 - v) / K * D * K) D
      (addrBits a - (prefixLen ℓ K a + (ℓ - 2 - v) / K * D * K) - D * K)
      ⟨(v - layoutB0 ℓ K) % K, Nat.mod_lt _ h.1⟩
  else WStep.butterflies (roundSet ℓ K a v) P

/-- Step (iii): rounds `v = ℓ-1, …, 0`, each `Q_P(D̃ Q_P(H z))` with `D̃(x) = θ̃_{2J(x)}`. -/
noncomputable def roundsProg (P D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ) :
    List (WStep (addrBits a)) :=
  (List.range ℓ).reverse.flatMap (fun v =>
    [roundStep P D ℓ K a v, WStep.diag (fun x => θt (2 * twJ ℓ K a v x)), WStep.trunc P])

/-- Steps (ii)-(iv) as one Walsh program: `L`, the rounds, `U`. -/
noncomputable def recordAxesProg (P D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ) :
    List (WStep (addrBits a)) :=
  posPermProg P (D + 1) K (layoutL ℓ K a) ++ roundsProg P D ℓ K a θt ++
    posPermProg P (D + 1) K (layoutU ℓ K a)

/-- The direct tensor FFT of Theorem 6.5 on record arrays (natural order in, natural frequency
order out), given a layer oracle and a phase table. -/
noncomputable def directFFT (layer : LayerOracle) (P D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ)
    (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) : RArr (Cube (addrBits a)) (2 ^ ℓ) :=
  runProg layer (2 ^ ℓ) (recordAxesProg P D ℓ K a θt) (lastAxisFFT P ℓ θt z)

/-! ## Tensor encoding -/

/-- Exponent of axis `i` of the shape (`a_i` for record axes, `ℓ` for the last axis). -/
def fftExp {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) (i : Fin (D + 1)) : ℕ :=
  if h : (i : ℕ) < D then a ⟨i, h⟩ else ℓ

/-- The shape `t = (t_1, …, t_d) = (2^{a_0}, …, 2^{a_{D-1}}, 2^ℓ)` (0-based axes, `d = D + 1`). -/
def fftShape {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) : Fin (D + 1) → ℕ := fun i => 2 ^ fftExp a ℓ i

/-- The digit tuple of the coefficient `k` of the record at address `x`. -/
def tensorIdx {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) (x : Cube (addrBits a)) (k : Fin (2 ^ ℓ)) :
    Idx (fftShape a ℓ) :=
  fun i => toFinPow (fftExp a ℓ i) (if h : (i : ℕ) < D then axisVal a x ⟨i, h⟩ else (k : ℕ))

/-- A tensor (natural axis order, last axis contiguous) as a record array on the cube. -/
def ofTensor {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) (U : Idx (fftShape a ℓ) → ℂ) :
    RArr (Cube (addrBits a)) (2 ^ ℓ) :=
  fun x k => U (tensorIdx a ℓ x k)

/-- The record address of a digit tuple: position `origPos a i v` carries bit `v` of `j_i`. -/
def cubeOfIdx {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) (j : Idx (fftShape a ℓ)) : Cube (addrBits a) :=
  fun p => decide (∃ i : Fin D, ∃ v : Fin (a i),
    origPos a i v = (p : ℕ) ∧ (j (Fin.castSucc i) : ℕ).testBit v = true)

/-- The coefficient index (last-axis digit) of a digit tuple. -/
def coeffOfIdx {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) (j : Idx (fftShape a ℓ)) : Fin (2 ^ ℓ) :=
  toFinPow ℓ (j (Fin.last D))

/-- A record array on the cube as a tensor indexed by digit tuples (natural order). -/
def toTensor {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) :
    Idx (fftShape a ℓ) → ℂ :=
  fun j => z (cubeOfIdx a ℓ j) (coeffOfIdx a ℓ j)

/-! ## The layer calls made by the algorithm -/

/-- `WalshLayerOK layer P D ℓ K a`: every layer call made by `directFFT` at precision `P` satisfies
`LayerSpec`: the chunk rounds (precision `P`, `D` chunks, shapes `[2^{j₀}] × [2^K]^D × [2^{nS}]`
of the `m₀`-bit cube, `walsh_layout_round_slice`) and the CNOT batches inside the positional maps
`L`, `U` (precision `P + 8d`, `d = D + 1`, `1 ≤ D' ≤ d` chunks, Proposition 5.5). This single
hypothesis replaces the fixed network premises (Definition A.1 (`def:fixed-network-premises`)) and the parameter bands of Proposition A.11 at the value level:
Proposition A.11 (`prop:prop14-param`) at the bands for `P`, and Lemma 5.3 (`lem:walsh-lift`) for `P + 8d`, discharge it at the machine level. -/
def WalshLayerOK (layer : LayerOracle) (P D ℓ K : ℕ) (a : Fin D → ℕ) : Prop :=
  (∀ (j₀ nS : ℕ) (ρ : Fin K), j₀ + D * K + nS = addrBits a →
      LayerSpec P (2 ^ ℓ) (2 ^ j₀) K D (2 ^ nS) ρ (layer P (2 ^ ℓ) (2 ^ j₀) K D (2 ^ nS) ρ)) ∧
    ∀ (j₀ D' nS : ℕ) (ρ : Fin K), j₀ + D' * K + nS = addrBits a → 1 ≤ D' → D' ≤ D + 1 →
      LayerSpec (P + 8 * (D + 1)) (2 ^ ℓ) (2 ^ j₀) K D' (2 ^ nS) ρ
        (layer (P + 8 * (D + 1)) (2 ^ ℓ) (2 ^ j₀) K D' (2 ^ nS) ρ)

/-! ## Component contract statements (proved in `Walsh/Proofs/`) -/

/-- **Encoding** (natural tensor order, Section 6 (`sec:direct-fft`)): `toTensor` and `ofTensor` are
mutually inverse. CONTRACT (proved in `Walsh/Proofs/`). -/
def TensorEncodingStmt : Prop :=
  ∀ {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ),
    (∀ U : Idx (fftShape a ℓ) → ℂ, toTensor a ℓ (ofTensor a ℓ U) = U) ∧
      ∀ z : RArr (Cube (addrBits a)) (2 ^ ℓ), ofTensor a ℓ (toTensor a ℓ z) = z

/-- **DIF** (Section 6.2, eq. (`eq:dif`), applied inductively): the exact DIF
levels `s = 0, …, ℓ-1` followed by bit reversal compute `F_r` on every record. CONTRACT (proved
in `Walsh/Proofs/`). -/
def DifExactStmt : Prop :=
  ∀ (ℓ : ℕ) {α : Type} (z : RArr α (2 ^ ℓ)), lastAxisExact ℓ z = lastAxisDFT ℓ z

/-- **Tensor factorization** (Definition 3.2; used in the proof of Theorem 6.5 (`thm:direct-fft`)): the normalized positive
tensor DFT `F^+_t` is the record-axis transform composed with the last-axis transform, under the
natural encoding. CONTRACT (proved in `Walsh/Proofs/`). -/
def TensorFactorStmt : Prop :=
  ∀ {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) (U : Idx (fftShape a ℓ) → ℂ),
    toTensor a ℓ (recordDFT a (lastAxisDFT ℓ (ofTensor a ℓ U))) = dftTensor (fftShape a ℓ) U

/-- **Local round estimate** (proof of Theorem 6.5 (`thm:direct-fft`)): for a disk array `z` on the `P`-grid, a
set `T` of positions, computed phases `θ̃` with `|θ̃| ≤ 1` and exact phases `ζ` with `|ζ| = 1` and
`|θ̃ - ζ| < 2 · 2^{-P}`, the round protocol `Q_P(D̃ Q_P(H_T z))` returns a disk array on the
`P`-grid within `(√2 + 2 + √2) 2^{-P} < 6 · 2^{-P}` of the exact round `D_ζ H_T z`.
CONTRACT (proved in `Walsh/Proofs/`). -/
def RoundLocalErrorStmt : Prop :=
  ∀ {m r : ℕ} (P : ℕ) (T : Finset (Fin m)) (θt ζ : Cube m → ℂ) (z : RArr (Cube m) r),
    ArrOnDiskGrid P z → (∀ x, ‖θt x‖ ≤ 1) → (∀ x, ‖ζ x‖ = 1) →
    (∀ x, ‖θt x - ζ x‖ < 2 * gridUnit P) →
      ArrOnDiskGrid P (truncArr P (diagArr θt (truncArr P (hT T z)))) ∧
        ‖truncArr P (diagArr θt (truncArr P (hT T z))) - diagArr ζ (hT T z)‖ < 6 * gridUnit P

/-- **Local last-axis estimate** (proof of Theorem 6.5 (`thm:direct-fft`)): for a disk vector on the `P`-grid and
a table satisfying `PhaseTableSpec`, a rounded DIF level returns a disk vector on the `P`-grid
within `6 · 2^{-P}` of the exact level (upper outputs: one truncation; lower outputs: two
truncations and the phase error). CONTRACT (proved in `Walsh/Proofs/`). -/
def LastAxisLevelErrorStmt : Prop :=
  ∀ (P ℓ s : ℕ) (θt : ℕ → ℂ) (w : Fin (2 ^ ℓ) → ℂ), s < ℓ → PhaseTableSpec P ℓ θt →
    (∀ k, OnDiskGrid P (w k)) →
      (∀ k, OnDiskGrid P (difLevel P ℓ s θt w k)) ∧
        ‖difLevel P ℓ s θt w - difLevelExact ℓ s w‖ < 6 * gridUnit P

/-- **Theorem 6.5** (direct complex tensor FFT, `thm:direct-fft`), value-level part. Let
`d = D + 1 ≥ 2`, `r = 2^ℓ` with `ℓ ≥ 2`, `1 ≤ K ≤ ℓ - 1`, `t_i ∈ {r/2, r}` for the record axes
(`a_i ∈ {ℓ-1, ℓ}`), `θ̃` a table satisfying `PhaseTableSpec P ℓ` (Lemma 6.1), and let the layer
oracle satisfy `WalshLayerOK layer P D ℓ K a` (`LayerSpec` at precision `P` for the chunk-round
shapes and at `P + 8d` for the slice shapes used inside the positional maps). Then for every disk tensor `U` on the `P`-grid in natural
order, the output is a disk tensor on the `P`-grid in natural frequency order (hence of component
width `P + 2 ≤ w`, no `lg M` increment) and `‖F̂^+_t U - F^+_t U‖_∞ < 12 ℓ · 2^{-P}`.
Omitted machine-level hypotheses: the fixed network premises (Definition A.1 (`def:fixed-network-premises`)) and the bands of Proposition A.11 (replaced by
`WalshLayerOK`), `P ≥ 8`, `ℓ < P` (used only by the table, Lemma 6.1) and `dℓ ≤ C_ℓ P`
(header sizes); the time bound is machine level. CONTRACT (proved in `Walsh/Proofs/`). -/
def DirectFFTStmt : Prop :=
  ∀ (layer : LayerOracle) (P D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ),
    1 ≤ D → 2 ≤ ℓ → 1 ≤ K → K ≤ ℓ - 1 → (∀ i, a i = ℓ - 1 ∨ a i = ℓ) →
    PhaseTableSpec P ℓ θt → WalshLayerOK layer P D ℓ K a →
    ∀ U : Idx (fftShape a ℓ) → ℂ, (∀ j, OnDiskGrid P (U j)) →
      (∀ u, OnDiskGrid P (toTensor a ℓ (directFFT layer P D ℓ K a θt (ofTensor a ℓ U)) u)) ∧
        ‖toTensor a ℓ (directFFT layer P D ℓ K a θt (ofTensor a ℓ U)) -
            dftTensor (fftShape a ℓ) U‖ < 12 * (ℓ : ℝ) * gridUnit P

/-- **Theorem 6.5, abstract counts** (proof of Theorem 6.5 (`thm:direct-fft`)): the record-axis program uses at
most `ℓ + 72 N_slice` completed layer calls (chunk rounds at `P`, the two positional maps at
`P + 8d`) and at most `K(D+1) + 2ℓ + 144 N_slice + 12K` passes, with `N_slice ≤ m₀/d + K`
for `m₀ = ∑ a_i`, `d = D + 1`. CONTRACT (proved in `Walsh/Proofs/`). -/
def DirectFFTCountStmt : Prop :=
  ∀ (P D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ),
    1 ≤ D → 2 ≤ ℓ → 1 ≤ K → K ≤ ℓ - 1 → (∀ i, a i = ℓ - 1 ∨ a i = ℓ) →
      progLayerCalls (recordAxesProg P D ℓ K a θt) ≤ ℓ + 72 * nSlice (addrBits a) K (D + 1) ∧
        progPasses (recordAxesProg P D ℓ K a θt) ≤
          K * (D + 1) + 2 * ℓ + 144 * nSlice (addrBits a) K (D + 1) + 12 * K

end SubNLogN.Math.Walsh
