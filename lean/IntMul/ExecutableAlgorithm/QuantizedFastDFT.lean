import IntMul.ExecutableAlgorithm.QuantizedSubstepBridges

namespace IntMul

/-- Multi-level recursion specification for the quantized Sinc-Gaussian Fractional-Shift
Synthetic FFT (`sincGaussianFastDFTQuantized`), carrying the target precision `p` at each node
under the additive schedule `child.p = pChild p K = p + 2 * K + 12` (`[MS]` Lemma 6.5, §6.3, eq. (34)). -/
inductive QuantizedFastDFTSpec where
  | base (p R : ℕ) : QuantizedFastDFTSpec
  | step (p K t1 r c1 : ℕ) (v1Of : ℕ → ℕ → ℕ)
      (child : QuantizedFastDFTSpec) : QuantizedFastDFTSpec

/-- Transform length `R` associated with a `QuantizedFastDFTSpec`. -/
def QuantizedFastDFTSpec.size : QuantizedFastDFTSpec → ℕ
  | .base _ R => R
  | .step _ _ t1 r _ _ _ => t1 * r

/-- Target output precision `p` associated with a `QuantizedFastDFTSpec`. -/
def QuantizedFastDFTSpec.p : QuantizedFastDFTSpec → ℕ
  | .base p _ => p
  | .step p _ _ _ _ _ _ => p

/-- **Multi-Level Quantized Windowed Sinc-Gaussian Recursive `FastDFT` (`sincGaussianFastDFTQuantized` / `windowedSincGaussianFastDFTQuantized`, `[MS]` §§5, 6.2–6.3 & 7)**:
Recursively computes the quantized 1D DFT of length `spec.size` at target precision `spec.p` by:
1. At `.base p R`: computing `dft1D R x u` and quantizing to `p + 2` fractional bits via `complexQuantize p`.
2. At `.step p K t1 r c1 v1Of child`:
   - Spreading `x` via the quantized signed-Kronecker finite `W`-window (`W = 4 p_{child} + 1`, `m ∈ [-2 p_{child}, 2 p_{child}]`)
     Sinc-Gaussian kernel `kroneckerSincGaussianSpreadArray (alphaSchedule (pWork p K)) (2 * pChild p K) (2 * pChild p K) t1 r x`
     (which quantizes inputs and taps to `2 p_{child}` bits and multiplies the pre-folded overlap-add blocks via `polyMulKroneckerSigned`),
   - Pre-twisting by quantized twiddle `complexQuantize (2 * pChild p K) (zetaRoot r k2)` and rounding via `complexQuantize (2 * pChild p K)` (Term B3),
   - Running the addition-only multi-stage Radix-2 Synthetic FFT `syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1)` over `ℂ[y]/(y^r + 1)` (with per-stage rounding) and rounding via `complexQuantize (2 * pChild p K)` (Term B3),
   - Post-twisting by quantized twiddle `complexQuantize (2 * pChild p K) (zetaRoot r (-k2))` and rounding via `complexQuantize (2 * pChild p K)` (Term B3),
   - Making `t_1` recursive quantized calls to `sincGaussianFastDFTQuantized child` (at child precision `pChild p K`),
   - Routing via the odd-stride column permutation `v1Of u2 u1` and rounding `Y` via `complexQuantize (2 * pChild p K)`,
   - Quantizing the Box-Gaussian passband coefficients `c0` and `c1_pass` via `realQuantize (2 * pChild p K)` and
     deconvolving across all three regimes using the step-rounded solvers (`solveBidiagonalFwdQuantized` for `2 * u2 < r`,
     `solveNyquistQuantized` with quantized `nyquistAltSum` for `2 * u2 = r`, and `solveBidiagonalBwdQuantized` for `2 * u2 > r`)
     which round every recurrence step and boundary combine via `complexQuantize (2 * pChild p K)` (Term D), and
   - Quantizing the output to `p + 2` fractional bits via `complexQuantize p`. -/
noncomputable def sincGaussianFastDFTQuantized : QuantizedFastDFTSpec → (ℕ → ℂ) → ℕ → ℂ
  | .base p R, x, u => complexQuantize p (dft1D R x u)
  | .step p K t1 r _c1 v1Of child, x, u =>
    let α := alphaSchedule (pWork p K)
    let pSub := 2 * pChild p K
    let U := kroneckerSincGaussianSpreadArray α pSub (2 * pChild p K) t1 r x
    let P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
    let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
    let qHat : ℕ → ℕ → ℂ := fun v1 u2 => sincGaussianFastDFTQuantized child (qPost v1) u2
    let Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of u2 u1) u2)
    let u2 := u % r
    let u1_tilde := u / r
    let y := (u2 : ℝ) / (r : ℝ)
    let c0 : ℂ := (realQuantize pSub (c0Coeff (realErfScaled α) y) : ℂ)
    let c1_pass : ℂ := (realQuantize pSub (c1Coeff (realErfScaled α) y) : ℂ)
    let z_sub :=
      if 2 * u2 < r then
        solveBidiagonalFwdQuantized pSub t1 c0 c1_pass (Y u2) u1_tilde
      else if 2 * u2 = r then
        solveNyquistQuantized pSub t1 c0 (Y u2) (complexQuantize pSub (nyquistAltSum t1 r x)) u1_tilde
      else
        solveBidiagonalBwdQuantized pSub t1 c0 c1_pass (Y u2) u1_tilde
    complexQuantize p z_sub

/-- Alias `fastDFTQuantized` for `sincGaussianFastDFTQuantized`. -/
noncomputable abbrev fastDFTQuantized : QuantizedFastDFTSpec → (ℕ → ℂ) → ℕ → ℂ :=
  sincGaussianFastDFTQuantized

/-- Structural validity predicate for a multi-level `QuantizedFastDFTSpec`:
requires only purely arithmetic/structural schedule invariants at each recursive step:
- `8 ≤ p`, `2 ≤ K`, `0 < t1 ≤ 2 ^ (K / 2)`, `0 < r ≤ 2 * t1`, `t1 * r = 2 ^ K`, `c1 * t1 = r`, `t1 % 2 = 0`,
- `child.size = r`, `child.p = pChild p K`, `child.Valid`,
- `v1Of u2 u1` satisfies the odd-stride congruence `(2 * u2 - 1) * v1Of u2 u1 ≡ u1 (mod t1)`. -/
inductive QuantizedFastDFTSpec.Valid : QuantizedFastDFTSpec → Prop where
  | base (p R : ℕ) : QuantizedFastDFTSpec.Valid (.base p R)
  | step {p K t1 r c1 : ℕ} {v1Of : ℕ → ℕ → ℕ} {child : QuantizedFastDFTSpec}
      (hp : 8 ≤ p) (hK : 2 ≤ K)
      (ht1 : 0 < t1) (ht1_le : t1 ≤ 2 ^ (K / 2))
      (hr : 0 < r) (hr_le : r ≤ 2 * t1)
      (hsize : t1 * r = 2 ^ K)
      (hc1 : c1 * t1 = r)
      (heven : t1 % 2 = 0)
      (hchild_size : child.size = r)
      (hchild_p : child.p = pChild p K)
      (hchild : child.Valid)
      (hv1 : ∀ u2 < r, ∀ u1 : ℕ, ∃ q : ℤ,
        (2 * (u2 : ℤ) - 1) * (v1Of u2 u1 : ℤ) = (u1 : ℤ) + q * (t1 : ℤ))
      (hv1_lt : ∀ u2 < r, ∀ u1 < t1, v1Of u2 u1 < t1) :
      QuantizedFastDFTSpec.Valid (.step p K t1 r c1 v1Of child)

/-- Single sequential 2-tape unshuffle (de-interleaving) pass: splits `tape` into even indices
`tape (2 * k)` on `[0, half)` and odd indices `tape (2 * k + 1)` on `[half, 2 * half)`. -/
def unshufflePass {α : Type*} (half : ℕ) (tape : ℕ → α) (idx : ℕ) : α :=
  if idx < half then tape (2 * idx) else tape (2 * (idx - half) + 1)

/-- Single sequential 2-tape run-interleaving pass: merges two `2^m × r` half-transposes `top` and `bot`
by streaming runs of length `r` alternately from `top` (even rows `j1`) and `bot` (odd rows `j1`). -/
def interleaveRunsPass {α : Type*} (r : ℕ) (top bot : ℕ → α) (idx : ℕ) : α :=
  let j1 := idx / r
  let i := idx % r
  if j1 % 2 = 0 then top ((j1 / 2) * r + i) else bot ((j1 / 2) * r + i)

/-- Recursive `m`-stage sequential 2-tape matrix transpose of a `2^m × r` matrix:
at each stage `m + 1`, performs `1` `unshufflePass` into even and odd sub-tapes, recursively transposes
both `2^m × r` halves, and merges them in `1` sequential `interleaveRunsPass` of run-length `r`
(`2` sequential passes per stage, `2 * m` passes total, `[MS]` §§3.2, 3.4 (Lemma 3.3)). -/
def sequentialTapeTranspose {α : Type*} : ℕ → ℕ → (ℕ → α) → (ℕ → α)
  | 0, _r, tape => tape
  | m + 1, r, tape =>
    let half := 2 ^ m * r
    let u := unshufflePass half tape
    let top := sequentialTapeTranspose m r (fun k => u k)
    let bot := sequentialTapeTranspose m r (fun k => u (half + k))
    interleaveRunsPass r top bot

/-- Recursive `m`-stage sequential 2-tape matrix transpose of a `2^m × r` matrix paired with its
exact sequential full-tape pass count (`2 * m` passes across `m` stages: `1` `unshufflePass` +
`1` `interleaveRunsPass` per stage, `[MS]` §§3.2, 3.4 (Lemma 3.3)). -/
def sequentialTapeTransposeWithPasses {α : Type*} : ℕ → ℕ → (ℕ → α) → (ℕ → α) × ℕ
  | 0, _r, tape => (tape, 0)
  | m + 1, r, tape =>
    let half := 2 ^ m * r
    let u := unshufflePass half tape
    let top := sequentialTapeTransposeWithPasses m r (fun k => u k)
    let bot := sequentialTapeTransposeWithPasses m r (fun k => u (half + k))
    (interleaveRunsPass r top.1 bot.1, 1 + top.2 + 1)

/-- The first projection of `sequentialTapeTransposeWithPasses` equals `sequentialTapeTranspose`. -/
theorem sequentialTapeTransposeWithPasses_fst {α : Type*} (m r : ℕ) (tape : ℕ → α) :
    (sequentialTapeTransposeWithPasses m r tape).1 = sequentialTapeTranspose m r tape := by
  induction m generalizing tape with
  | zero => rfl
  | succ m ih =>
    dsimp only [sequentialTapeTransposeWithPasses, sequentialTapeTranspose]
    rw [ih, ih]

/-- The second projection of `sequentialTapeTransposeWithPasses m r tape` equals `2 * m` full-tape passes
(`1` `unshufflePass` + `1` `interleaveRunsPass` at each of the `m` recursion stages). -/
theorem sequentialTapeTransposeWithPasses_snd {α : Type*} (m r : ℕ) (tape : ℕ → α) :
    (sequentialTapeTransposeWithPasses m r tape).2 = 2 * m := by
  induction m generalizing tape with
  | zero => rfl
  | succ m ih =>
    dsimp only [sequentialTapeTransposeWithPasses]
    rw [ih]
    omega

/-- **Constructive Correctness of `m`-Stage Sequential 2-Tape Matrix Transposition (`sequentialTapeTranspose_index_eq`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
For any `m, r : ℕ` (`0 < r`), any 1D sequential tape `tape : ℕ → α` holding a `2^m × r` matrix in
stride-`2^m` layout `tape (i * 2 ^ m + j1)`, and any indices `j1 < 2 ^ m` and `i < r`, the `m`-stage
recursive 2-tape split/interleave network `sequentialTapeTranspose m r tape` outputs the exact
row-major transposed entry at index `j1 * r + i`:
`sequentialTapeTranspose m r tape (j1 * r + i) = tape (i * 2 ^ m + j1)`. -/
theorem sequentialTapeTranspose_index_eq {α : Type*} (m r : ℕ) (hr : 0 < r)
    (tape : ℕ → α) (j1 i : ℕ) (hj1 : j1 < 2 ^ m) (hi : i < r) :
    sequentialTapeTranspose m r tape (j1 * r + i) = tape (i * 2 ^ m + j1) := by
  induction m generalizing tape j1 with
  | zero =>
    have hj0 : j1 = 0 := by omega
    subst hj0
    dsimp [sequentialTapeTranspose]
    congr 1
    ring
  | succ m ih =>
    dsimp only [sequentialTapeTranspose, interleaveRunsPass]
    have hdiv : (j1 * r + i) / r = j1 := by
      have hcomm : j1 * r + i = i + j1 * r := add_comm _ _
      rw [hcomm, Nat.add_mul_div_right i j1 hr, Nat.div_eq_of_lt hi, zero_add]
    have hmod : (j1 * r + i) % r = i := by
      have hcomm : j1 * r + i = i + j1 * r := add_comm _ _
      rw [hcomm, Nat.add_mul_mod_self_right i j1 r, Nat.mod_eq_of_lt hi]
    rw [hdiv, hmod]
    have hj_half : j1 / 2 < 2 ^ m := by
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega
    have hk_lt : i * 2 ^ m + j1 / 2 < 2 ^ m * r := by
      have hi1 : i + 1 ≤ r := hi
      have h1 : i * 2 ^ m + j1 / 2 < i * 2 ^ m + 2 ^ m :=
        Nat.add_lt_add_left hj_half (i * 2 ^ m)
      have h2 : i * 2 ^ m + 2 ^ m ≤ 2 ^ m * r := by
        calc i * 2 ^ m + 2 ^ m = 2 ^ m * (i + 1) := by ring
          _ ≤ 2 ^ m * r := Nat.mul_le_mul_left (2 ^ m) hi1
      exact h1.trans_le h2
    split_ifs with hpar
    · rw [ih (fun k => unshufflePass (2 ^ m * r) tape k) (j1 / 2) hj_half]
      unfold unshufflePass
      rw [if_pos hk_lt]
      congr 1
      have hpow : i * 2 ^ (m + 1) = 2 * (i * 2 ^ m) := by ring
      omega
    · rw [ih (fun k => unshufflePass (2 ^ m * r) tape (2 ^ m * r + k)) (j1 / 2) hj_half]
      unfold unshufflePass
      have hnot : ¬ (2 ^ m * r + (i * 2 ^ m + j1 / 2) < 2 ^ m * r) := by omega
      rw [if_neg hnot, Nat.add_sub_cancel_left]
      congr 1
      have hpow : i * 2 ^ (m + 1) = 2 * (i * 2 ^ m) := by ring
      omega

/-- Executes the `m`-stage (`m = ⌊log₂ t₁⌋`) sequential 2-tape transpose network
`sequentialTapeTransposeWithPasses` to gather stride-`t1` input samples `x (j1 + t1 * i)` into
row-contiguous index `j1 * r + i` whenever `t1 = 2^m`, `0 < t1`, `0 < r`, and `idx / t1 < r`. -/
def routedInputGather {α : Type*} (t1 r : ℕ) (x : ℕ → α) (idx : ℕ) : α :=
  let m := Nat.log2 t1
  if t1 = 2 ^ m ∧ 0 < t1 ∧ 0 < r ∧ idx / t1 < r then
    (sequentialTapeTransposeWithPasses m r x).1 ((idx % t1) * r + idx / t1)
  else
    x idx

/-- Pointwise equivalence of `routedInputGather t1 r x` with `x` via `sequentialTapeTranspose_index_eq`. -/
theorem routedInputGather_eq {α : Type*} (t1 r : ℕ) (x : ℕ → α) :
    routedInputGather t1 r x = x := by
  funext idx
  unfold routedInputGather
  dsimp only
  set m := Nat.log2 t1
  split_ifs with h
  · rcases h with ⟨ht1, ht1_pos, hr, hdiv_lt⟩
    rw [sequentialTapeTransposeWithPasses_fst]
    have hmod_lt : idx % t1 < 2 ^ m := by
      rw [← ht1]
      exact Nat.mod_lt idx ht1_pos
    rw [sequentialTapeTranspose_index_eq m r hr x (idx % t1) (idx / t1) hmod_lt hdiv_lt]
    congr 1
    rw [← ht1, mul_comm (idx / t1) t1, Nat.div_add_mod]
  · rfl

/-- Executes the `m`-stage (`m = ⌊log₂ t₁⌋`) sequential 2-tape transpose network
`sequentialTapeTransposeWithPasses` on a 2D array `mat : ℕ → ℕ → α` stored in `u2`-major
layout `idx ↦ mat (idx / 2^m) (idx % 2^m)` whenever `t1 = 2^m`, `0 < r`, and `u / r < 2^m`. -/
def routedTranspose2D {α : Type*} (t1 r : ℕ) (mat : ℕ → ℕ → α) (u : ℕ) : α :=
  let m := Nat.log2 t1
  if t1 = 2 ^ m ∧ 0 < r ∧ u / r < 2 ^ m then
    (sequentialTapeTransposeWithPasses m r (fun idx => mat (idx / 2 ^ m) (idx % 2 ^ m))).1 u
  else
    mat (u % r) (u / r)

/-- Pointwise equivalence of `routedTranspose2D t1 r mat u` with `mat (u % r) (u / r)` via
`sequentialTapeTranspose_index_eq`. -/
theorem routedTranspose2D_eq {α : Type*} (t1 r : ℕ) (mat : ℕ → ℕ → α) (u : ℕ) :
    routedTranspose2D t1 r mat u = mat (u % r) (u / r) := by
  unfold routedTranspose2D
  dsimp only
  set m := Nat.log2 t1
  split_ifs with h
  · rcases h with ⟨_ht1, hr, hur⟩
    rw [sequentialTapeTransposeWithPasses_fst]
    have hu_eq : u = (u / r) * r + u % r := by
      rw [mul_comm (u / r) r, Nat.div_add_mod]
    have hmod_lt : u % r < r := Nat.mod_lt u hr
    conv_lhs => rw [hu_eq]
    rw [sequentialTapeTranspose_index_eq m r hr
      (fun idx => mat (idx / 2 ^ m) (idx % 2 ^ m)) (u / r) (u % r) hur hmod_lt]
    have h2m_pos : 0 < 2 ^ m := pow_pos zero_lt_two m
    have hdiv2 : ((u % r) * 2 ^ m + u / r) / 2 ^ m = u % r := by
      have hcomm : (u % r) * 2 ^ m + u / r = u / r + (u % r) * 2 ^ m := add_comm _ _
      rw [hcomm, Nat.add_mul_div_right _ _ h2m_pos, Nat.div_eq_of_lt hur, zero_add]
    have hmod2 : ((u % r) * 2 ^ m + u / r) % 2 ^ m = u / r := by
      have hcomm : (u % r) * 2 ^ m + u / r = u / r + (u % r) * 2 ^ m := add_comm _ _
      rw [hcomm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hur]
    rw [hdiv2, hmod2]
  · rfl

/-- Modular reduction of `2 * x + rem` (`rem < 2`) modulo `2 ^ (m + 1)`:
`(2 * x + rem) % 2 ^ (m + 1) = 2 * (x % 2 ^ m) + rem`. -/
theorem two_mul_add_mod_two_pow_succ (x rem m : ℕ) (hrem : rem < 2) :
    (2 * x + rem) % 2 ^ (m + 1) = 2 * (x % 2 ^ m) + rem := by
  have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := by ring
  have hmod_lt : x % 2 ^ m < 2 ^ m := Nat.mod_lt x (pow_pos zero_lt_two m)
  have hlt : 2 * (x % 2 ^ m) + rem < 2 ^ (m + 1) := by omega
  have hdiv : 2 * x + rem = (2 * (x % 2 ^ m) + rem) + (x / 2 ^ m) * 2 ^ (m + 1) := by
    have hx := (Nat.div_add_mod x (2 ^ m)).symm
    calc 2 * x + rem = 2 * (2 ^ m * (x / 2 ^ m) + x % 2 ^ m) + rem := by rw [← hx]
      _ = (2 * (x % 2 ^ m) + rem) + (x / 2 ^ m) * (2 ^ m * 2) := by ring
      _ = (2 * (x % 2 ^ m) + rem) + (x / 2 ^ m) * 2 ^ (m + 1) := by rw [← hpow]
  rw [hdiv, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

/-- Single sequential 2-tape parity-interleaving pass: merges two routed `2^m`-element streams
`firstHalf` and `secondHalf` into output index `u1`, selecting which stream supplies indices
matching `parity % 2` vs. the opposite parity (`[MS]` §§3.2, 3.4 (Lemma 3.3)). -/
def interleaveParityPass {α : Type*} (parity : ℕ) (firstHalf secondHalf : ℕ → α) (u1 : ℕ) : α :=
  if u1 % 2 = parity % 2 then firstHalf (u1 / 2) else secondHalf (u1 / 2)

/-- Recursive `m`-stage sequential 2-tape routing network for any affine odd-stride permutation
`u1 ↦ (w * u1 + b) % 2^m` (`w % 2 = 1`):
at each stage `m + 1`, executes `1` `unshufflePass (2 ^ m)` into even and odd source halves,
recursively routes both halves of length `2^m` with offsets `b / 2` and `(w + b) / 2`, and merges
them in `1` `interleaveParityPass (b % 2)` pass (`2` full-tape passes per stage, `[MS]` §§3.2, 3.4 (Lemma 3.3)). -/
def sequentialAffineOddRoute {α : Type*} : ℕ → ℕ → ℕ → (ℕ → α) → (ℕ → α)
  | 0, _w, _b, col => col
  | m + 1, w, b, col =>
    let half := 2 ^ m
    let u := unshufflePass half col
    let bEven := if b % 2 = 0 then b / 2 else (w + b) / 2
    let bOdd := if b % 2 = 0 then (w + b) / 2 else b / 2
    let routedEven := sequentialAffineOddRoute m w bEven (fun k => u k)
    let routedOdd := sequentialAffineOddRoute m w bOdd (fun k => u (half + k))
    interleaveParityPass (b % 2) routedEven routedOdd

/-- Recursive `m`-stage sequential 2-tape affine odd-stride routing network paired with its exact
sequential pass count (`2 * m` passes across `m` stages: `1` `unshufflePass` +
`1` `interleaveParityPass` per stage, `[MS]` §§3.2, 3.4 (Lemma 3.3)). -/
def sequentialAffineOddRouteWithPasses {α : Type*} : ℕ → ℕ → ℕ → (ℕ → α) → (ℕ → α) × ℕ
  | 0, _w, _b, col => (col, 0)
  | m + 1, w, b, col =>
    let half := 2 ^ m
    let u := unshufflePass half col
    let bEven := if b % 2 = 0 then b / 2 else (w + b) / 2
    let bOdd := if b % 2 = 0 then (w + b) / 2 else b / 2
    let routedEven := sequentialAffineOddRouteWithPasses m w bEven (fun k => u k)
    let routedOdd := sequentialAffineOddRouteWithPasses m w bOdd (fun k => u (half + k))
    (interleaveParityPass (b % 2) routedEven.1 routedOdd.1, 1 + routedEven.2 + 1)

/-- The first projection of `sequentialAffineOddRouteWithPasses` equals `sequentialAffineOddRoute`. -/
theorem sequentialAffineOddRouteWithPasses_fst {α : Type*} (m w b : ℕ) (col : ℕ → α) :
    (sequentialAffineOddRouteWithPasses m w b col).1 = sequentialAffineOddRoute m w b col := by
  induction m generalizing b col with
  | zero => rfl
  | succ m ih =>
    dsimp only [sequentialAffineOddRouteWithPasses, sequentialAffineOddRoute]
    rw [ih, ih]

/-- The second projection of `sequentialAffineOddRouteWithPasses m w b col` equals `2 * m`
sequential passes (`1` `unshufflePass` + `1` `interleaveParityPass` at each of the `m` stages). -/
theorem sequentialAffineOddRouteWithPasses_snd {α : Type*} (m w b : ℕ) (col : ℕ → α) :
    (sequentialAffineOddRouteWithPasses m w b col).2 = 2 * m := by
  induction m generalizing b col with
  | zero => rfl
  | succ m ih =>
    dsimp only [sequentialAffineOddRouteWithPasses]
    rw [ih]
    omega

/-- **Constructive Correctness of the `m`-Stage Sequential Affine Odd-Stride Routing Network (`sequentialAffineOddRoute_index_eq`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
For any depth `m : ℕ`, odd multiplier `w : ℕ` (`w % 2 = 1`), offset `b : ℕ`, column `col : ℕ → α`,
and index `u1 < 2 ^ m`, the `m`-stage unshuffle/interleave network `sequentialAffineOddRoute m w b col`
outputs `col ((w * u1 + b) % 2 ^ m)` at position `u1`. -/
theorem sequentialAffineOddRoute_index_eq {α : Type*} (m w b : ℕ) (hw : w % 2 = 1)
    (col : ℕ → α) (u1 : ℕ) (hu1 : u1 < 2 ^ m) :
    sequentialAffineOddRoute m w b col u1 = col ((w * u1 + b) % 2 ^ m) := by
  induction m generalizing b col u1 with
  | zero =>
    have hu0 : u1 = 0 := by omega
    subst hu0
    have hmod : (w * 0 + b) % 2 ^ 0 = 0 := Nat.mod_one _
    rw [hmod]
    rfl
  | succ m ih =>
    dsimp only [sequentialAffineOddRoute, interleaveParityPass]
    have hmod_idem : (b % 2) % 2 = b % 2 := Nat.mod_mod b 2
    rw [hmod_idem]
    have hu1_half : u1 / 2 < 2 ^ m := by
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega
    set bEven := if b % 2 = 0 then b / 2 else (w + b) / 2
    set bOdd := if b % 2 = 0 then (w + b) / 2 else b / 2
    split_ifs with hpar
    · rw [ih bEven (fun k => unshufflePass (2 ^ m) col k) (u1 / 2) hu1_half]
      have hlt_m : (w * (u1 / 2) + bEven) % 2 ^ m < 2 ^ m :=
        Nat.mod_lt _ (pow_pos zero_lt_two m)
      unfold unshufflePass
      rw [if_pos hlt_m]
      have hmod_step := (two_mul_add_mod_two_pow_succ (w * (u1 / 2) + bEven) 0 m (by decide)).symm
      rw [Nat.add_zero] at hmod_step
      rw [hmod_step]
      congr 1
      congr 1
      dsimp only [bEven]
      split_ifs with hb0
      · have hu1_div : u1 = 2 * (u1 / 2) := by omega
        have hb_div : b = 2 * (b / 2) := by omega
        calc 2 * (w * (u1 / 2) + b / 2)
            = w * (2 * (u1 / 2)) + 2 * (b / 2) := by ring
          _ = w * u1 + b := by rw [← hu1_div, ← hb_div]
      · have hu1_div : u1 = 2 * (u1 / 2) + 1 := by omega
        have hwb_div : w + b = 2 * ((w + b) / 2) := by omega
        calc 2 * (w * (u1 / 2) + (w + b) / 2)
            = 2 * w * (u1 / 2) + 2 * ((w + b) / 2) := by ring
          _ = 2 * w * (u1 / 2) + (w + b) := by rw [← hwb_div]
          _ = w * (2 * (u1 / 2) + 1) + b := by ring
          _ = w * u1 + b := by rw [← hu1_div]
    · rw [ih bOdd (fun k => unshufflePass (2 ^ m) col (2 ^ m + k)) (u1 / 2) hu1_half]
      unfold unshufflePass
      have hnot : ¬ (2 ^ m + (w * (u1 / 2) + bOdd) % 2 ^ m < 2 ^ m) := by omega
      rw [if_neg hnot, Nat.add_sub_cancel_left]
      have hmod_step := (two_mul_add_mod_two_pow_succ (w * (u1 / 2) + bOdd) 1 m (by decide)).symm
      rw [hmod_step]
      congr 1
      congr 1
      dsimp only [bOdd]
      split_ifs with hb0
      · have hu1_div : u1 = 2 * (u1 / 2) + 1 := by omega
        have hwb_div : w + b = 2 * ((w + b) / 2) + 1 := by omega
        calc 2 * (w * (u1 / 2) + (w + b) / 2) + 1
            = 2 * w * (u1 / 2) + (2 * ((w + b) / 2) + 1) := by ring
          _ = 2 * w * (u1 / 2) + (w + b) := by rw [← hwb_div]
          _ = w * (2 * (u1 / 2) + 1) + b := by ring
          _ = w * u1 + b := by rw [← hu1_div]
      · have hu1_div : u1 = 2 * (u1 / 2) := by omega
        have hb_div : b = 2 * (b / 2) + 1 := by omega
        calc 2 * (w * (u1 / 2) + b / 2) + 1
            = w * (2 * (u1 / 2)) + (2 * (b / 2) + 1) := by ring
          _ = w * u1 + b := by rw [← hu1_div, ← hb_div]

/-- Odd-stride multiplier `w` for column `u2` at radix-2 depth `m` (`t1 = 2^m`),
satisfying `w % 2 = 1` and `(w * u1) % 2^m = oddStrideInvPow2 m u2 u1` (`[MS]` §3.4 (Lemma 3.3) & §4.1 (Proposition 4.1)). -/
def oddStrideFactor (m u2 : ℕ) : ℕ :=
  if m = 0 then 1 else oddStrideInvPow2 m u2 1

/-- For all `m, u2 : ℕ`, `oddStrideFactor m u2` is odd (`oddStrideFactor m u2 % 2 = 1`). -/
theorem oddStrideFactor_mod_two (m u2 : ℕ) : oddStrideFactor m u2 % 2 = 1 := by
  unfold oddStrideFactor
  split_ifs with hm
  · rfl
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    set w := oddStrideInvPow2 (k + 1) u2 1
    obtain ⟨q, hq⟩ := oddStrideInvPow2_congr (k + 1) u2 1
    change (2 * (u2 : ℤ) - 1) * (w : ℤ) = 1 + q * ((2 ^ (k + 1) : ℕ) : ℤ) at hq
    have hw_div : (w : ℤ) = 2 * ((w / 2 : ℕ) : ℤ) + ((w % 2 : ℕ) : ℤ) := by omega
    have hpow : ((2 ^ (k + 1) : ℕ) : ℤ) = 2 * ((2 ^ k : ℕ) : ℤ) := by
      push_cast
      ring
    set L : ℤ := (2 * (u2 : ℤ) - 1) * ((w / 2 : ℕ) : ℤ) + (u2 : ℤ) * ((w % 2 : ℕ) : ℤ)
    set R : ℤ := q * ((2 ^ k : ℕ) : ℤ)
    have hexp : (2 * (u2 : ℤ) - 1) * (w : ℤ) = 2 * L - ((w % 2 : ℕ) : ℤ) := by
      dsimp only [L]
      rw [hw_div]
      ring
    have hrhs : 1 + q * ((2 ^ (k + 1) : ℕ) : ℤ) = 1 + 2 * R := by
      dsimp only [R]
      rw [hpow]
      ring
    rw [hexp, hrhs] at hq
    omega

/-- For all `m, u2, u1 : ℕ`, `(oddStrideFactor m u2 * u1) % 2 ^ m = oddStrideInvPow2 m u2 u1`. -/
theorem oddStrideFactor_mul_mod_eq (m u2 u1 : ℕ) :
    (oddStrideFactor m u2 * u1) % 2 ^ m = oddStrideInvPow2 m u2 u1 := by
  unfold oddStrideFactor
  split_ifs with hm
  · subst hm
    haveI : NeZero (2 ^ 0) := ⟨by decide⟩
    have hlt : oddStrideInvPow2 0 u2 u1 < 2 ^ 0 := by
      cases u2 <;> { unfold oddStrideInvPow2; exact ZMod.val_lt _ }
    omega
  · haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m (by decide)⟩
    rw [← ZMod.val_natCast (n := 2 ^ m)]
    push_cast
    cases u2 with
    | zero =>
      dsimp [oddStrideInvPow2]
      rw [ZMod.natCast_zmod_val]
      congr 1
      ring
    | succ k =>
      dsimp [oddStrideInvPow2]
      rw [ZMod.natCast_zmod_val]
      congr 1
      simp only [oddStrideEquiv, Equiv.coe_fn_symm_mk]
      ring

/-- Executes the `m`-stage sequential 2-tape affine odd-stride routing network
`sequentialAffineOddRouteWithPasses` on the index tape `id` to route `(u2, u1)` to its source row
index `v1 < 2^m` (`[MS]` §§3.2, 3.4 (Lemma 3.3)). -/
def routedOddStrideIndex (m u2 u1 : ℕ) : ℕ :=
  (sequentialAffineOddRouteWithPasses m (oddStrideFactor m u2) 0 id).1 (u1 % 2 ^ m)

/-- **Constructive Correctness of `routedOddStrideIndex` (`routedOddStrideIndex_eq_oddStrideInvPow2`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
For all `m, u2, u1 : ℕ`, the index routed by the `m`-stage sequential 2-tape unshuffle/interleave
network `routedOddStrideIndex m u2 u1` equals `oddStrideInvPow2 m u2 u1`. -/
theorem routedOddStrideIndex_eq_oddStrideInvPow2 (m u2 u1 : ℕ) :
    routedOddStrideIndex m u2 u1 = oddStrideInvPow2 m u2 u1 := by
  unfold routedOddStrideIndex
  rw [sequentialAffineOddRouteWithPasses_fst]
  have hu1_mod_lt : u1 % 2 ^ m < 2 ^ m := Nat.mod_lt u1 (pow_pos zero_lt_two m)
  rw [sequentialAffineOddRoute_index_eq m (oddStrideFactor m u2) 0 (oddStrideFactor_mod_two m u2)
    id (u1 % 2 ^ m) hu1_mod_lt]
  dsimp only [id]
  rw [Nat.add_zero, Nat.mul_mod_mod, oddStrideFactor_mul_mod_eq m u2 u1]

/-- Routing a column `fun v1 => qHat v1 u2` directly through the `m`-stage sequential 2-tape
network `sequentialAffineOddRouteWithPasses` produces the exact same entry as indexing by
`routedOddStrideIndex m u2 u1` (`= oddStrideInvPow2 m u2 u1`) for all `u1 < 2 ^ m`. -/
theorem sequentialAffineOddRouteWithPasses_qHat_eq {α : Type*} (m : ℕ)
    (qHat : ℕ → ℕ → α) (u2 u1 : ℕ) (hu1 : u1 < 2 ^ m) :
    (sequentialAffineOddRouteWithPasses m (oddStrideFactor m u2) 0 (fun v1 => qHat v1 u2)).1 u1 =
      qHat (routedOddStrideIndex m u2 u1) u2 := by
  rw [sequentialAffineOddRouteWithPasses_fst,
    sequentialAffineOddRoute_index_eq m (oddStrideFactor m u2) 0 (oddStrideFactor_mod_two m u2)
      (fun v1 => qHat v1 u2) u1 hu1,
    Nat.add_zero, oddStrideFactor_mul_mod_eq m u2 u1,
    routedOddStrideIndex_eq_oddStrideInvPow2 m u2 u1]

/-- Routes each column `u2` of `qHat : ℕ → ℕ → α` through the `m`-stage (`m = ⌊log₂ t₁⌋`)
sequential 2-tape network `sequentialAffineOddRouteWithPasses` whenever `t1 = 2^m`,
`u1 < 2^m`, and `v1Of u2 u1 = routedOddStrideIndex m u2 u1` (`[MS]` §§3.2, 3.4 (Lemma 3.3)). -/
def routedColumnEntry {α : Type*} (t1 : ℕ) (v1Of : ℕ → ℕ → ℕ)
    (qHat : ℕ → ℕ → α) (u2 u1 : ℕ) : α :=
  let m := Nat.log2 t1
  if t1 = 2 ^ m ∧ u1 < 2 ^ m ∧ v1Of u2 u1 = routedOddStrideIndex m u2 u1 then
    (sequentialAffineOddRouteWithPasses m (oddStrideFactor m u2) 0 (fun v1 => qHat v1 u2)).1 u1
  else
    qHat (v1Of u2 u1) u2

/-- Pointwise equivalence of `routedColumnEntry t1 v1Of qHat u2 u1` with `qHat (v1Of u2 u1) u2` via
`sequentialAffineOddRouteWithPasses_qHat_eq`. -/
theorem routedColumnEntry_eq {α : Type*} (t1 : ℕ) (v1Of : ℕ → ℕ → ℕ)
    (qHat : ℕ → ℕ → α) (u2 u1 : ℕ) :
    routedColumnEntry t1 v1Of qHat u2 u1 = qHat (v1Of u2 u1) u2 := by
  unfold routedColumnEntry
  dsimp only
  split_ifs with h
  · rcases h with ⟨_ht1, hu1, hv1⟩
    rw [sequentialAffineOddRouteWithPasses_qHat_eq (Nat.log2 t1) qHat u2 u1 hu1, hv1]
  · rfl

/-- Concrete balanced power-of-two `QuantizedFastDFTSpec.step` at precision `p` and log-length `K`
(`t_1 = 2^{⌊K/2⌋}`, `r = 2^{K - ⌊K/2⌋}`, `c_1 = 2^{K - 2⌊K/2⌋}`, `v1Of = routedOddStrideIndex (K / 2)`). -/
def quantizedBoxGaussianStepSpec (p K : ℕ) (child : QuantizedFastDFTSpec) : QuantizedFastDFTSpec :=
  .step p K (2 ^ (K / 2)) (2 ^ (K - K / 2)) (2 ^ (K - K / 2 - K / 2))
    (routedOddStrideIndex (K / 2)) child

/-- **Unconditional Validity of `quantizedBoxGaussianStepSpec`**:
For any `8 ≤ p`, `2 ≤ K`, and valid `child` with `child.size = 2 ^ (K - K / 2)` and
`child.p = pChild p K`, `quantizedBoxGaussianStepSpec p K child` satisfies `QuantizedFastDFTSpec.Valid`. -/
theorem quantizedBoxGaussianStepSpec_valid
    (p K : ℕ) (hp : 8 ≤ p) (hK : 2 ≤ K) (child : QuantizedFastDFTSpec)
    (hchild_size : child.size = 2 ^ (K - K / 2))
    (hchild_p : child.p = pChild p K)
    (hchild : child.Valid) :
    (quantizedBoxGaussianStepSpec p K child).Valid := by
  have ht1 : 0 < 2 ^ (K / 2) := pow_pos zero_lt_two _
  have hr : 0 < 2 ^ (K - K / 2) := pow_pos zero_lt_two _
  have hr_le : 2 ^ (K - K / 2) ≤ 2 * 2 ^ (K / 2) := by
    have hpow : 2 * 2 ^ (K / 2) = 2 ^ (K / 2 + 1) := by ring
    rw [hpow]
    exact Nat.pow_le_pow_right zero_lt_two (by omega)
  have hsize : 2 ^ (K / 2) * 2 ^ (K - K / 2) = 2 ^ K := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self K 2)]
  have hc1 : 2 ^ (K - K / 2 - K / 2) * 2 ^ (K / 2) = 2 ^ (K - K / 2) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have heven : (2 ^ (K / 2)) % 2 = 0 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K / 2 ≠ 0)
    rw [hm, pow_succ']
    exact Nat.mul_mod_right 2 (2 ^ m)
  exact QuantizedFastDFTSpec.Valid.step hp hK ht1 le_rfl hr hr_le hsize hc1 heven
    hchild_size hchild_p hchild
    (fun u2 _ u1 => by
      rw [routedOddStrideIndex_eq_oddStrideInvPow2]
      exact oddStrideInvPow2_congr (K / 2) u2 u1)
    (fun u2 _ u1 _ => by
      rw [routedOddStrideIndex_eq_oddStrideInvPow2]
      haveI : NeZero (2 ^ (K / 2)) := ⟨pow_ne_zero _ (by decide)⟩
      unfold oddStrideInvPow2
      cases u2 <;> exact ZMod.val_lt _)

set_option maxHeartbeats 1600000 in
/-- **Single-Step Error Closure Theorem for Quantized Windowed Sinc-Gaussian `FastDFT` (`sincGaussianFastDFTStep_error_le`, `[MS]` Lemma 6.5, §6.3)**:
Given any recursive child transform `childDFT : (ℕ → ℂ) → ℕ → ℂ` of length `r` satisfying the inductive
error bound `‖childDFT x' u' - dft1D r x' u'‖ ≤ (2 : ℝ) ^ (-(pChild p K : ℤ)) * M'`, one step of the
quantized Sinc-Gaussian Fractional-Shift Synthetic FFT pipeline (Kronecker spread, pre-twist, radix-2
Synthetic FFT, post-twist, child transform, odd-stride routing, 3-regime bidiagonal/Nyquist solver,
and output quantization to `p` bits) satisfies the parent error bound `≤ (2 : ℝ) ^ (-(p : ℤ)) * M`. -/
theorem sincGaussianFastDFTStep_error_le
    {p K t1 r c1 : ℕ} {v1Of : ℕ → ℕ → ℕ}
    (hp : 8 ≤ p) (hK : 2 ≤ K)
    (ht1 : 0 < t1) (ht1_le : t1 ≤ 2 ^ (K / 2))
    (hr : 0 < r) (hr_le : r ≤ 2 * t1)
    (hsize : t1 * r = 2 ^ K)
    (hc1 : c1 * t1 = r)
    (heven : t1 % 2 = 0)
    (hv1 : ∀ u2 < r, ∀ u1 : ℕ, ∃ q : ℤ,
      (2 * (u2 : ℤ) - 1) * (v1Of u2 u1 : ℤ) = (u1 : ℤ) + q * (t1 : ℤ))
    (childDFT : (ℕ → ℂ) → ℕ → ℂ)
    (hchild_err : ∀ (x' : ℕ → ℂ) (M' : ℝ), 1 ≤ M' →
      (∀ k < r, ‖x' k‖ ≤ M') → ∀ u' < r,
      ‖childDFT x' u' - dft1D r x' u'‖ ≤ (2 : ℝ) ^ (-(pChild p K : ℤ)) * M')
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M)
    (hx : ∀ k < t1 * r, ‖x k‖ ≤ M)
    (u : ℕ) (hu : u < t1 * r) :
    let α := alphaSchedule (pWork p K)
    let pSub := 2 * pChild p K
    let U := kroneckerSincGaussianSpreadArray α pSub (2 * pChild p K) t1 r x
    let P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
    let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
    let qHat : ℕ → ℕ → ℂ := fun v1 u2 => childDFT (qPost v1) u2
    let Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of u2 u1) u2)
    let u2 := u % r
    let u1_tilde := u / r
    let y := (u2 : ℝ) / (r : ℝ)
    let c0 : ℂ := (realQuantize pSub (c0Coeff (realErfScaled α) y) : ℂ)
    let c1_pass : ℂ := (realQuantize pSub (c1Coeff (realErfScaled α) y) : ℂ)
    let z_sub :=
      if 2 * u2 < r then
        solveBidiagonalFwdQuantized pSub t1 c0 c1_pass (Y u2) u1_tilde
      else if 2 * u2 = r then
        solveNyquistQuantized pSub t1 c0 (Y u2) (complexQuantize pSub (nyquistAltSum t1 r x)) u1_tilde
      else
        solveBidiagonalBwdQuantized pSub t1 c0 c1_pass (Y u2) u1_tilde
    ‖complexQuantize p z_sub - dft1D (t1 * r) x u‖ ≤ (2 : ℝ) ^ (-(p : ℤ)) * M := by
    dsimp only
    have hM_pos : 0 < M := by linarith
    have hp_work : 8 ≤ pWork p K := by
      unfold pWork
      omega
    set α := alphaSchedule (pWork p K)
    have hα : 0 < α := alphaSchedule_pos (pWork p K) (by omega)
    set pSub := 2 * pChild p K
    let U := kroneckerSincGaussianSpreadArray α pSub (2 * pChild p K) t1 r x
    let U_inf := sincGaussianSpreadArray α t1 r x
    let P_unq : ℕ → ℕ → ℂ := fun j1 k2 => zetaRoot r (k2 : ℝ) * U j1 k2
    let P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
    let Q_unq : ℕ → ℕ → ℂ := syntheticDFT t1 r P_unq
    let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    let qPost_unq : ℕ → ℕ → ℂ := fun v1 k2 => zetaRoot r (-(k2 : ℝ)) * Q_unq v1 k2
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
    let qHat : ℕ → ℕ → ℂ := fun v1 u2 => childDFT (qPost v1) u2
    let Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of u2 u1) u2)
    set u2 := u % r
    set u1_tilde := u / r
    have hu2 : u2 < r := Nat.mod_lt u hr
    have hu1_tilde : u1_tilde < t1 := by
      rw [mul_comm] at hu
      exact Nat.div_lt_of_lt_mul hu
    set y := (u2 : ℝ) / (r : ℝ)
    set c0R : ℝ := c0Coeff (realErfScaled α) y
    set c1R : ℝ := c1Coeff (realErfScaled α) y
    set c0 : ℂ := (c0R : ℂ)
    set c1_pass : ℂ := (c1R : ℂ)
    set c0_qR : ℝ := realQuantize pSub c0R
    set c1_qR : ℝ := realQuantize pSub c1R
    set c0_q : ℂ := (c0_qR : ℂ)
    set c1_q : ℂ := (c1_qR : ℂ)
    set alt_q : ℂ := complexQuantize pSub (nyquistAltSum t1 r x)
    have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hr1_ge1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
    have hMr_ge1 : 1 ≤ ((r : ℝ) + 1) * M := by nlinarith
    have hr_le_2K : r ≤ 2 ^ K := by
      rw [← hsize]
      exact Nat.le_mul_of_pos_left r ht1
    have ht1_le_2K : t1 ≤ 2 ^ K := by
      rw [← hsize]
      exact Nat.le_mul_of_pos_right t1 hr
    have hSub_r_err : complexQuantizeMaxErr pSub * ((r : ℝ) + 1) ≤
        (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) :=
      complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K r hr_le_2K
    have hSub_err := complexQuantizeMaxErr_two_mul_pChild_lt p K
    have hpow_child_pos : (0 : ℝ) < (2 : ℝ) ^ (-(pChild p K : ℤ)) := zpow_pos (by norm_num) _
    have hpow_child_le_one : (2 : ℝ) ^ (-(pChild p K : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hSub_le_pChild_M :
        complexQuantizeMaxErr pSub ≤ (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
      have h1 := hSub_err.1.le
      nlinarith
    have hSub_r_le_pChild_M :
        complexQuantizeMaxErr pSub * (((r : ℝ) + 1) * M) ≤
          (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
      calc complexQuantizeMaxErr pSub * (((r : ℝ) + 1) * M)
          = (complexQuantizeMaxErr pSub * ((r : ℝ) + 1)) * M := by ring
        _ ≤ ((0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ))) * M :=
            mul_le_mul_of_nonneg_right hSub_r_err hM_pos.le
        _ = (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by ring
    have hqSub_nonneg : 0 ≤ complexQuantizeMaxErr pSub := by
      unfold complexQuantizeMaxErr
      positivity
    have hU_norm : ∀ j1 < t1, ∀ k2 < r, ‖U j1 k2‖ ≤ ((r : ℝ) + (0.5 : ℝ)) * M :=
      fun j1 hj1 k2 hk2 =>
        norm_kroneckerSincGaussianSpreadArray_le p K t1 r ht1 hr x M hM1 hx j1 k2 hj1 hk2
    have hP_err : ∀ j1 < t1, ∀ k2 < r,
        ‖P j1 k2 - P_unq j1 k2‖ ≤ (0.02 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
      intro j1 hj1 k2 hk2
      have hsplit : P j1 k2 - P_unq j1 k2 =
          (P j1 k2 - complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2) +
            (complexQuantize pSub (zetaRoot r (k2 : ℝ)) - zetaRoot r (k2 : ℝ)) * U j1 k2 := by
        dsimp only [P_unq]
        ring
      rw [hsplit]
      have h1 : ‖P j1 k2 - complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2‖ ≤
          complexQuantizeMaxErr pSub :=
        norm_complexQuantize_sub_le pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
      have h2_tw : ‖complexQuantize pSub (zetaRoot r (k2 : ℝ)) - zetaRoot r (k2 : ℝ)‖ ≤
          complexQuantizeMaxErr pSub :=
        norm_complexQuantize_sub_le pSub (zetaRoot r (k2 : ℝ))
      have h2_U : ‖U j1 k2‖ ≤ ((r : ℝ) + 1) * M := by
        have := hU_norm j1 hj1 k2 hk2
        linarith
      have h2 : ‖(complexQuantize pSub (zetaRoot r (k2 : ℝ)) - zetaRoot r (k2 : ℝ)) * U j1 k2‖ ≤
          complexQuantizeMaxErr pSub * (((r : ℝ) + 1) * M) := by
        rw [norm_mul]
        exact mul_le_mul h2_tw h2_U (norm_nonneg _) hqSub_nonneg
      have htri_P := norm_add_le
        (P j1 k2 - complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
        ((complexQuantize pSub (zetaRoot r (k2 : ℝ)) - zetaRoot r (k2 : ℝ)) * U j1 k2)
      linarith
    have hQ_err : ∀ v1 : ℕ, ∀ k2 < r,
        ‖Q v1 k2 - Q_unq v1 k2‖ ≤ (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
      intro v1 k2 hk2
      obtain ⟨ht1_pow, hlog_le_2K⟩ := two_pow_log2_eq_and_log2_le_of_mul_eq_two_pow t1 r K hsize
      have h1 := norm_syntheticFFTRadix2Quantized_sub_syntheticDFT_le pSub t1 r ht1_pow hr
        P P_unq ((0.02 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M) hP_err v1 k2 hk2
      have hlog_err : complexQuantizeMaxErr pSub * ((Nat.log2 t1 : ℝ) + 1) ≤
          (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) :=
        complexQuantizeMaxErr_two_mul_pChild_mul_add_one_le_of_le_two_pow p K (Nat.log2 t1) hlog_le_2K
      have hlog_err_M : ((Nat.log2 t1 : ℝ) + 1) * complexQuantizeMaxErr pSub ≤
          (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
        calc ((Nat.log2 t1 : ℝ) + 1) * complexQuantizeMaxErr pSub
            = (complexQuantizeMaxErr pSub * ((Nat.log2 t1 : ℝ) + 1)) * 1 := by ring
          _ ≤ ((0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ))) * M :=
              mul_le_mul hlog_err hM1 (by norm_num) (by positivity)
          _ = (0.01 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by ring
      linarith
    have hQ_unq_norm : ∀ v1 : ℕ, ∀ k2 < r, ‖Q_unq v1 k2‖ ≤ ((r : ℝ) + (0.5 : ℝ)) * M := by
      intro v1 k2 hk2
      dsimp only [Q_unq]
      refine norm_syntheticDFT_le t1 r ht1 hr P_unq (((r : ℝ) + (0.5 : ℝ)) * M) ?_ v1 k2 hk2
      intro j1 hj1 m hm
      dsimp only [P_unq]
      rw [norm_mul, norm_zetaRoot, one_mul]
      exact hU_norm j1 hj1 m hm
    have hQ_norm : ∀ v1 : ℕ, ∀ k2 < r, ‖Q v1 k2‖ ≤ ((r : ℝ) + 1) * M := by
      intro v1 k2 hk2
      have htri_Q := norm_add_le (Q v1 k2 - Q_unq v1 k2) (Q_unq v1 k2)
      rw [sub_add_cancel] at htri_Q
      have h1 := hQ_err v1 k2 hk2
      have h2 := hQ_unq_norm v1 k2 hk2
      nlinarith
    have hqPost_err : ∀ v1 : ℕ, ∀ k2 < r,
        ‖qPost v1 k2 - qPost_unq v1 k2‖ ≤ (0.05 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
      intro v1 k2 hk2
      have hsplit : qPost v1 k2 - qPost_unq v1 k2 =
          (qPost v1 k2 - complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2) +
            (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) - zetaRoot r (-(k2 : ℝ))) * Q v1 k2 +
            zetaRoot r (-(k2 : ℝ)) * (Q v1 k2 - Q_unq v1 k2) := by
        dsimp only [qPost_unq]
        ring
      rw [hsplit]
      have h1 : ‖qPost v1 k2 - complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2‖ ≤
          complexQuantizeMaxErr pSub :=
        norm_complexQuantize_sub_le pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
      have h2_tw : ‖complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) - zetaRoot r (-(k2 : ℝ))‖ ≤
          complexQuantizeMaxErr pSub :=
        norm_complexQuantize_sub_le pSub (zetaRoot r (-(k2 : ℝ)))
      have h2 : ‖(complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) - zetaRoot r (-(k2 : ℝ))) * Q v1 k2‖ ≤
          complexQuantizeMaxErr pSub * (((r : ℝ) + 1) * M) := by
        rw [norm_mul]
        exact mul_le_mul h2_tw (hQ_norm v1 k2 hk2) (norm_nonneg _) hqSub_nonneg
      have h3 : ‖zetaRoot r (-(k2 : ℝ)) * (Q v1 k2 - Q_unq v1 k2)‖ ≤
          (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
        rw [norm_mul, norm_zetaRoot, one_mul]
        exact hQ_err v1 k2 hk2
      have htri_qP1 := norm_add_le
        ((qPost v1 k2 - complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2) +
          (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) - zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
        (zetaRoot r (-(k2 : ℝ)) * (Q v1 k2 - Q_unq v1 k2))
      have htri_qP2 := norm_add_le
        (qPost v1 k2 - complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
        ((complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) - zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
      linarith
    have hqPost_unq_norm : ∀ v1 : ℕ, ∀ k2 < r, ‖qPost_unq v1 k2‖ ≤ ((r : ℝ) + (0.5 : ℝ)) * M := by
      intro v1 k2 hk2
      dsimp only [qPost_unq]
      rw [norm_mul, norm_zetaRoot, one_mul]
      exact hQ_unq_norm v1 k2 hk2
    have hqPost_norm : ∀ v1 : ℕ, ∀ k2 < r, ‖qPost v1 k2‖ ≤ ((r : ℝ) + 1) * M := by
      intro v1 k2 hk2
      have htri_q := norm_add_le (qPost v1 k2 - qPost_unq v1 k2) (qPost_unq v1 k2)
      rw [sub_add_cancel] at htri_q
      have h1 := hqPost_err v1 k2 hk2
      have h2 := hqPost_unq_norm v1 k2 hk2
      nlinarith
    set ε_child : ℝ := (2 : ℝ) ^ (-(pChild p K : ℤ)) * (((r : ℝ) + 1) * M)
    set ε_B : ℝ := (0.6 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M
    set ε_total : ℝ := ε_B + ε_child
    have hε_total_nonneg : 0 ≤ ε_total := by
      dsimp only [ε_total, ε_B, ε_child]
      positivity
    have hY_win_err : ∀ k : ℕ,
        ‖Y u2 k - dft2D t1 r U k u2‖ ≤ (0.1 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M + ε_child := by
      intro k
      rcases hv1 u2 hu2 k with ⟨q, hq⟩
      have hpipe := theorem1_pipeline_computes_dft2D t1 r c1 ht1 hr hc1 U (v1Of u2 k) k u2 q hq
      dsimp only at hpipe
      have hih := hchild_err (qPost (v1Of u2 k)) (((r : ℝ) + 1) * M) hMr_ge1 (hqPost_norm (v1Of u2 k))
        u2 hu2
      have h_dft1D_sub :
          ‖dft1D r (qPost (v1Of u2 k)) u2 - dft1D r (qPost_unq (v1Of u2 k)) u2‖ ≤
            (0.05 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M :=
        norm_dft1D_sub_le r hr (qPost (v1Of u2 k)) (qPost_unq (v1Of u2 k))
          ((0.05 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M) (hqPost_err (v1Of u2 k)) u2
      have h_Y_round : ‖Y u2 k - qHat (v1Of u2 k) u2‖ ≤ complexQuantizeMaxErr pSub :=
        norm_complexQuantize_sub_le pSub (qHat (v1Of u2 k) u2)
      have hpipe_eq : dft1D r (qPost_unq (v1Of u2 k)) u2 = dft2D t1 r U k u2 := hpipe
      have hsplit : Y u2 k - dft2D t1 r U k u2 =
          (Y u2 k - qHat (v1Of u2 k) u2) +
            (qHat (v1Of u2 k) u2 - dft1D r (qPost (v1Of u2 k)) u2) +
            (dft1D r (qPost (v1Of u2 k)) u2 - dft1D r (qPost_unq (v1Of u2 k)) u2) := by
        rw [← hpipe_eq]
        ring
      have htri_Y1 := norm_add_le
        ((Y u2 k - qHat (v1Of u2 k) u2) + (qHat (v1Of u2 k) u2 - dft1D r (qPost (v1Of u2 k)) u2))
        (dft1D r (qPost (v1Of u2 k)) u2 - dft1D r (qPost_unq (v1Of u2 k)) u2)
      have htri_Y2 := norm_add_le
        (Y u2 k - qHat (v1Of u2 k) u2)
        (qHat (v1Of u2 k) u2 - dft1D r (qPost (v1Of u2 k)) u2)
      rw [← hsplit] at htri_Y1
      dsimp only [qHat] at htri_Y1 htri_Y2 h_Y_round
      linarith
    have hB12_err : ∀ k : ℕ,
        ‖dft2D t1 r U k u2 - dft2D t1 r U_inf k u2‖ ≤ (0.5 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M :=
      fun k => norm_dft2D_kroneckerSincGaussianSpreadArray_sub_le p K t1 r ht1 hr x M hM1 hx k u2
    have hY_err : ∀ k : ℕ, ‖Y u2 k - dft2D t1 r U_inf k u2‖ ≤ ε_total := by
      intro k
      have hsplit :
          Y u2 k - dft2D t1 r U_inf k u2 =
            (Y u2 k - dft2D t1 r U k u2) + (dft2D t1 r U k u2 - dft2D t1 r U_inf k u2) := by
        ring
      rw [hsplit]
      have h1 := hY_win_err k
      have h2 := hB12_err k
      have htri_k := norm_add_le (Y u2 k - dft2D t1 r U k u2) (dft2D t1 r U k u2 - dft2D t1 r U_inf k u2)
      dsimp only [ε_total, ε_B]
      linarith
    let X : ℕ → ℂ := fun v => dft1DGrid t1 r x u2 v
    let Y_ideal : ℕ → ℂ := fun k =>
      c0 * X ((((k : ℤ) - 0).emod (t1 : ℤ)).toNat) +
      c1_pass * X ((((k : ℤ) - 1).emod (t1 : ℤ)).toNat)
    let Y_ideal_q : ℕ → ℂ := fun k =>
      c0_q * X ((((k : ℤ) - 0).emod (t1 : ℤ)).toNat) +
      c1_q * X ((((k : ℤ) - 1).emod (t1 : ℤ)).toNat)
    let Y_spread : ℕ → ℂ := fun k => dft2D t1 r U_inf k u2
    have hX_norm : ∀ v : ℕ, ‖X v‖ ≤ M := norm_dft1DGrid_le t1 r ht1 hr x M hx u2 hu2
    have h_bnd_q : Y_ideal_q 0 = c0_q * X 0 + c1_q * X (t1 - 1) := by
      dsimp only [Y_ideal_q]
      rw [emod_sub_zero_toNat t1 0 ht1, emod_zero_sub_one_toNat t1 ht1]
    have h_int_q : ∀ v : ℕ, v + 1 < t1 → Y_ideal_q (v + 1) = c0_q * X (v + 1) + c1_q * X v := by
      intro v hv
      dsimp only [Y_ideal_q]
      rw [emod_sub_zero_toNat t1 (v + 1) hv, emod_succ_sub_one_toNat t1 v hv]
    have h_ideal_q_err : ∀ k : ℕ,
        ‖Y_ideal k - Y_ideal_q k‖ ≤ (0.02 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := by
      intro k
      set v0 := (((k : ℤ) - 0).emod (t1 : ℤ)).toNat
      set v1 := (((k : ℤ) - 1).emod (t1 : ℤ)).toNat
      have hsplit : Y_ideal k - Y_ideal_q k =
          (c0 - c0_q) * X v0 + (c1_pass - c1_q) * X v1 := by
        dsimp only [Y_ideal, Y_ideal_q]
        ring
      rw [hsplit]
      have htri := norm_add_le ((c0 - c0_q) * X v0) ((c1_pass - c1_q) * X v1)
      have hc0_diff : ‖c0 - c0_q‖ ≤ complexQuantizeMaxErr pSub := by
        rw [norm_sub_rev]
        exact (norm_realQuantize_coe_sub_le pSub c0R).2
      have hc1_diff : ‖c1_pass - c1_q‖ ≤ complexQuantizeMaxErr pSub := by
        rw [norm_sub_rev]
        exact (norm_realQuantize_coe_sub_le pSub c1R).2
      have h1 : ‖(c0 - c0_q) * X v0‖ ≤ complexQuantizeMaxErr pSub * M := by
        rw [norm_mul]
        exact mul_le_mul hc0_diff (hX_norm v0) (norm_nonneg _) hqSub_nonneg
      have h2 : ‖(c1_pass - c1_q) * X v1‖ ≤ complexQuantizeMaxErr pSub * M := by
        rw [norm_mul]
        exact mul_le_mul hc1_diff (hX_norm v1) (norm_nonneg _) hqSub_nonneg
      have hSub_M : complexQuantizeMaxErr pSub * M ≤ (0.001 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M :=
        mul_le_mul_of_nonneg_right hSub_err.1.le hM_pos.le
      have hpow_M_pos : 0 < (2 : ℝ) ^ (-(pChild p K : ℤ)) * M := mul_pos hpow_child_pos hM_pos
      linarith
    have h_spread_ideal : ∀ k : ℕ,
        ‖Y_spread k - Y_ideal k‖ ≤ (0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * M :=
      fun k => theorem2_sincGaussian_dft2D_sub_passband_norm_le
        (pWork p K) t1 r (by omega) ht1 hr k u2 hu2 x M hM_pos.le hx
    set ε_rhs : ℝ :=
      (0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * M +
        (ε_total + (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M)
    have hε_rhs_nonneg : 0 ≤ ε_rhs := by
      dsimp only [ε_rhs]
      positivity
    have h_eff_ideal_q :
        ∀ (m : ℕ) (z : ℂ),
          ‖z - Y u2 m‖ ≤ complexQuantizeMaxErr pSub →
          ‖z - Y_ideal_q m‖ ≤ ε_rhs := by
      intro m z hz
      have hsplit : z - Y_ideal_q m =
          (z - Y u2 m) + (Y u2 m - Y_spread m) +
            (Y_spread m - Y_ideal m) + (Y_ideal m - Y_ideal_q m) := by ring
      rw [hsplit]
      have htri1 := norm_add_le
        ((z - Y u2 m) + (Y u2 m - Y_spread m) + (Y_spread m - Y_ideal m))
        (Y_ideal m - Y_ideal_q m)
      have htri2 := norm_add_le
        ((z - Y u2 m) + (Y u2 m - Y_spread m))
        (Y_spread m - Y_ideal m)
      have htri3 := norm_add_le (z - Y u2 m) (Y u2 m - Y_spread m)
      have h2 := hY_err m
      have h3 := h_spread_ideal m
      have h4 := h_ideal_q_err m
      dsimp only [ε_rhs]
      linarith
    have hc0R_pos : 0 < c0R := c0Coeff_realErfScaled_pos α y hα
    have hc1R_pos : 0 < c1R := c1Coeff_realErfScaled_pos α y hα
    have hc01_sum : c0R + c1R ≤ 1 := c0_add_c1_realErfScaled_le_one α y hα
    have hc0R_le1 : c0R ≤ 1 := by linarith
    have hc1R_le1 : c1R ≤ 1 := by linarith
    have hr_pos_real : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
    have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg u2) (Nat.cast_nonneg r)
    have hy1 : y ≤ 1 := (div_le_one hr_pos_real).mpr (by exact_mod_cast hu2.le)
    have hA_lt :
        (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * M) <
          (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
      have h1 := mul_lt_mul_of_pos_right (lemma2_termA_conditioning_mul_zpow_lt p K t1 hK ht1_le) hM_pos
      linarith
    have hBC_lt :
        (2.36 : ℝ) * (t1 : ℝ) * (ε_total + (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M) <
          (0.036 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
      lemma2_windowed_child_and_solver_amplification_error_bound p K t1 r M hK hr hM_pos hsize
    have hpow_p_le1 : (2 : ℝ) ^ (-(p : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have h_cyc_le_M : (2.36 : ℝ) * (t1 : ℝ) * ε_rhs ≤ M := by
      have hsum_lt : (2.36 : ℝ) * (t1 : ℝ) * ε_rhs < (0.039 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
        dsimp only [ε_rhs]
        linarith
      nlinarith
    have ht1_qSub := t1_mul_complexQuantizeMaxErr_two_mul_pChild_le p K t1 ht1_le_2K
    let z_sub : ℂ :=
      if 2 * u2 < r then
        solveBidiagonalFwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde
      else if 2 * u2 = r then
        solveNyquistQuantized pSub t1 c0_q (Y u2) alt_q u1_tilde
      else
        solveBidiagonalBwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde
    have hz_sub_err :
        ‖z_sub - dft1D (t1 * r) x u‖ ≤
          (2.36 : ℝ) * (t1 : ℝ) * ε_rhs +
            (2.001 : ℝ) * complexQuantizeMaxErr pSub +
            8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
      rw [← dft1DGrid_eq_dft1D t1 r x u]
      change ‖z_sub - X u1_tilde‖ ≤
        (2.36 : ℝ) * (t1 : ℝ) * ε_rhs +
          (2.001 : ℝ) * complexQuantizeMaxErr pSub +
          8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M
      dsimp only [z_sub]
      split_ifs with h_fwd h_nyq
      · have hy_half : y ≤ 1 / 2 := by
          dsimp only [y]
          rw [div_le_iff₀ hr_pos_real]
          have : 2 * (u2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h_fwd.le
          linarith
        have hc0R_gt : (0.49999999 : ℝ) ≤ c0R :=
          (c0Coeff_alphaSchedule_gt_049999999 (pWork p K) (by omega) y hy0 hy_half).le
        have hc10R : c1R ≤ c0R := c1Coeff_le_c0Coeff_of_le_half α y hα hy0 hy_half
        have hratioR : (c1R / c0R) ^ t1 ≤ (0.15 : ℝ) :=
          c1_div_c0_pow_le_015_of_balanced (pWork p K) t1 r u2 hp_work ht1 hr hr_le h_fwd
        obtain ⟨hc0_q_ge, hc0_q_le1, hc1_q_nonneg, hc10_q, hratio_q⟩ :=
          quantized_coeff_ratio_pow_le p K t1 ht1_le_2K c0R c1R hc0R_gt hc0R_le1 hc1R_pos.le hc10R hratioR
        have hnorm_c0_q : ‖c0_q‖ = c0_qR := by
          dsimp only [c0_q]
          rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have hnorm_c1_q : ‖c1_q‖ = c1_qR := by
          dsimp only [c1_q]
          rw [Complex.norm_real, Real.norm_of_nonneg hc1_q_nonneg]
        have hc0_q_pos : 0 < ‖c0_q‖ := by linarith
        have hc0_q_ne : c0_q ≠ 0 := norm_pos_iff.mp hc0_q_pos
        have hc0_q_le1_norm : ‖c0_q‖ ≤ 1 := by linarith
        have hc10_q_norm : ‖c1_q‖ ≤ ‖c0_q‖ := by linarith
        have hratio_q_norm : (‖c1_q‖ / ‖c0_q‖) ^ t1 ≤ (0.1501 : ℝ) := by
          rw [hnorm_c1_q, hnorm_c0_q]
          exact hratio_q
        have hdenom_q : c0_q + c1_q * zHomFwd c0_q c1_q (t1 - 1) ≠ 0 :=
          denom_ne_zero_of_relaxed t1 c0_q c1_q (0.4999 : ℝ) (0.1501 : ℝ)
            le_rfl (by linarith) hratio_q_norm le_rfl
        have hrec_q := solveBidiagonalFwd_recover_exact t1 c0_q c1_q ht1 hc0_q_ne hdenom_q
          X Y_ideal_q h_bnd_q h_int_q u1_tilde hu1_tilde
        have hrec_0 := solveBidiagonalFwd_recover_exact t1 c0_q c1_q ht1 hc0_q_ne hdenom_q
          X Y_ideal_q h_bnd_q h_int_q 0 ht1
        have h_eff := norm_solveBidiagonalFwdQuantized_sub_effRHS_le
          pSub t1 ht1 c0_q c1_q (by linarith) hc0_q_le1_norm hc10_q_norm hratio_q_norm
          (by linarith [ht1_qSub.2]) (Y u2) u1_tilde hu1_tilde
        have h_cyc := solveBidiagonalFwd_cyclic_error_bound_relaxed
          t1 ht1 c0_q c1_q Y_ideal_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2))
          (0.4999 : ℝ) (0.1501 : ℝ) ε_rhs le_rfl (by linarith) hc10_q_norm hratio_q_norm le_rfl
          hε_rhs_nonneg
          (fun k => h_eff_ideal_q k _ (norm_zPartFwdEffRHS_sub_le pSub c0_q c1_q hc0_q_ne hc0_q_le1_norm (Y u2) k))
          u1_tilde hu1_tilde
        have h_cyc_0 := solveBidiagonalFwd_cyclic_error_bound_relaxed
          t1 ht1 c0_q c1_q Y_ideal_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2))
          (0.4999 : ℝ) (0.1501 : ℝ) ε_rhs le_rfl (by linarith) hc10_q_norm hratio_q_norm le_rfl
          hε_rhs_nonneg
          (fun k => h_eff_ideal_q k _ (norm_zPartFwdEffRHS_sub_le pSub c0_q c1_q hc0_q_ne hc0_q_le1_norm (Y u2) k))
          0 ht1
        have hZ0_le :
            ‖solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) 0‖ ≤ 2 * M := by
          have htri0 := norm_add_le
            (solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) 0 -
              solveBidiagonalFwd t1 c0_q c1_q Y_ideal_q 0)
            (solveBidiagonalFwd t1 c0_q c1_q Y_ideal_q 0)
          rw [sub_add_cancel, hrec_0] at htri0
          rw [hrec_0] at h_cyc_0
          have hX0 := hX_norm 0
          linarith
        have hmul_Z0 :
            4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) *
              ‖solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) 0‖ ≤
              8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
          calc 4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) *
                ‖solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) 0‖
              ≤ 4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * (2 * M) :=
                mul_le_mul_of_nonneg_left hZ0_le
                  (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg t1) hqSub_nonneg))
            _ = 8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by ring
        rw [← hrec_q]
        have hsplit :
            solveBidiagonalFwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde -
              solveBidiagonalFwd t1 c0_q c1_q Y_ideal_q u1_tilde =
            (solveBidiagonalFwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde -
              solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) u1_tilde) +
            (solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) u1_tilde -
              solveBidiagonalFwd t1 c0_q c1_q Y_ideal_q u1_tilde) := by ring
        rw [hsplit]
        have htri := norm_add_le
          (solveBidiagonalFwdQuantized pSub t1 c0_q c1_q (Y u2) u1_tilde -
            solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) u1_tilde)
          (solveBidiagonalFwd t1 c0_q c1_q (zPartFwdEffRHS pSub c0_q c1_q (Y u2)) u1_tilde -
            solveBidiagonalFwd t1 c0_q c1_q Y_ideal_q u1_tilde)
        linarith
      · have hy_eq : y = 1 / 2 := by
          dsimp only [y]
          rw [div_eq_iff hr_pos_real.ne']
          have : 2 * (u2 : ℝ) = (r : ℝ) := by exact_mod_cast h_nyq
          linarith
        have hc01_eq_nyq : c0R = c1R := by
          dsimp only [c0R, c1R]
          rw [hy_eq]
          have hnyq_eq := theorem3_nyquist_passband_eq (realErfScaled α) (realErfScaled_zero α)
          linarith
        have hc1_q_eq_c0_q : c1_q = c0_q := by
          dsimp only [c0_q, c1_q, c0_qR, c1_qR]
          rw [hc01_eq_nyq]
        have hy_half : y ≤ 1 / 2 := by linarith
        have hc0R_gt : (0.49999999 : ℝ) ≤ c0R :=
          (c0Coeff_alphaSchedule_gt_049999999 (pWork p K) (by omega) y hy0 hy_half).le
        have hzero_ratio : ((0 : ℝ) / c0R) ^ t1 ≤ (0.15 : ℝ) := by
          rw [zero_div, zero_pow ht1.ne']
          norm_num
        obtain ⟨hc0_q_ge, hc0_q_le1, _, _, _⟩ :=
          quantized_coeff_ratio_pow_le p K t1 ht1_le_2K c0R 0 hc0R_gt hc0R_le1 le_rfl hc0R_pos.le hzero_ratio
        have hnorm_c0_q : ‖c0_q‖ = c0_qR := by
          dsimp only [c0_q]
          rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have hc0_q_pos : 0 < ‖c0_q‖ := by linarith
        have hc0_q_ne : c0_q ≠ 0 := norm_pos_iff.mp hc0_q_pos
        have hc0_q_le1_norm : ‖c0_q‖ ≤ 1 := by linarith
        have h_alt := (dft1DGrid_alternating_sum_nyquist_eq t1 r u2 ht1 hr heven h_nyq x).symm
        have h_int_nyq : ∀ v : ℕ, v + 1 < t1 → Y_ideal_q (v + 1) = c0_q * X (v + 1) + c0_q * X v := by
          intro v hv
          rw [h_int_q v hv, hc1_q_eq_c0_q]
        have hrec_q := solveNyquist_recover_exact t1 ht1 c0_q hc0_q_ne
          X Y_ideal_q h_int_nyq (nyquistAltSum t1 r x) h_alt u1_tilde hu1_tilde
        have h_eff := norm_solveNyquistQuantized_sub_effRHS_le
          pSub t1 c0_q hc0_q_ne (Y u2) alt_q u1_tilde
        have h_nyq_cyc := solveNyquist_error_bound_relaxed
          t1 ht1 c0_q Y_ideal_q (zPartNyqEffRHS pSub c0_q (Y u2))
          (nyquistAltSum t1 r x) alt_q (0.4999 : ℝ) ε_rhs (complexQuantizeMaxErr pSub)
          le_rfl (by linarith) hε_rhs_nonneg
          (fun k => h_eff_ideal_q k _ (norm_zPartNyqEffRHS_sub_le pSub c0_q hc0_q_ne hc0_q_le1_norm (Y u2) k))
          (norm_complexQuantize_sub_le pSub (nyquistAltSum t1 r x))
          u1_tilde hu1_tilde
        have ht1_ge1 : (1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast ht1
        have hqSub_le_8 :
            complexQuantizeMaxErr pSub / (t1 : ℝ) ≤
              (0.001 : ℝ) * complexQuantizeMaxErr pSub +
                8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
          have hdiv : complexQuantizeMaxErr pSub / (t1 : ℝ) ≤ complexQuantizeMaxErr pSub :=
            div_le_self hqSub_nonneg ht1_ge1
          have h1 : complexQuantizeMaxErr pSub ≤ (t1 : ℝ) * complexQuantizeMaxErr pSub := by
            calc complexQuantizeMaxErr pSub = 1 * complexQuantizeMaxErr pSub := (one_mul _).symm
              _ ≤ (t1 : ℝ) * complexQuantizeMaxErr pSub :=
                  mul_le_mul_of_nonneg_right ht1_ge1 hqSub_nonneg
          have h2 : (t1 : ℝ) * complexQuantizeMaxErr pSub ≤
              ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
            calc (t1 : ℝ) * complexQuantizeMaxErr pSub
                = ((t1 : ℝ) * complexQuantizeMaxErr pSub) * 1 := (mul_one _).symm
              _ ≤ ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M :=
                  mul_le_mul_of_nonneg_left hM1 (mul_nonneg (Nat.cast_nonneg t1) hqSub_nonneg)
          have h3 : 0 ≤ ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M :=
            mul_nonneg (mul_nonneg (Nat.cast_nonneg t1) hqSub_nonneg) hM_pos.le
          linarith
        rw [← hrec_q]
        have hsplit :
            solveNyquistQuantized pSub t1 c0_q (Y u2) alt_q u1_tilde -
              solveNyquist t1 c0_q Y_ideal_q (nyquistAltSum t1 r x) u1_tilde =
            (solveNyquistQuantized pSub t1 c0_q (Y u2) alt_q u1_tilde -
              solveNyquist t1 c0_q (zPartNyqEffRHS pSub c0_q (Y u2)) alt_q u1_tilde) +
            (solveNyquist t1 c0_q (zPartNyqEffRHS pSub c0_q (Y u2)) alt_q u1_tilde -
              solveNyquist t1 c0_q Y_ideal_q (nyquistAltSum t1 r x) u1_tilde) := by ring
        rw [hsplit]
        have htri := norm_add_le
          (solveNyquistQuantized pSub t1 c0_q (Y u2) alt_q u1_tilde -
            solveNyquist t1 c0_q (zPartNyqEffRHS pSub c0_q (Y u2)) alt_q u1_tilde)
          (solveNyquist t1 c0_q (zPartNyqEffRHS pSub c0_q (Y u2)) alt_q u1_tilde -
            solveNyquist t1 c0_q Y_ideal_q (nyquistAltSum t1 r x) u1_tilde)
        linarith
      · have h_bwd : r < 2 * u2 := by omega
        have hy_half : 1 / 2 ≤ y := by
          dsimp only [y]
          rw [le_div_iff₀ hr_pos_real]
          have : (r : ℝ) ≤ 2 * (u2 : ℝ) := by exact_mod_cast h_bwd.le
          linarith
        have hc1R_gt : (0.49999999 : ℝ) ≤ c1R :=
          (c1Coeff_alphaSchedule_gt_049999999 (pWork p K) (by omega) y hy_half hy1).le
        have hc01R : c0R ≤ c1R := c0Coeff_le_c1Coeff_of_ge_half α y hα hy_half hy1
        have hratioR : (c0R / c1R) ^ t1 ≤ (0.15 : ℝ) :=
          c0_div_c1_pow_le_015_of_balanced (pWork p K) t1 r u2 hp_work ht1 hr hr_le h_bwd hu2
        obtain ⟨hc1_q_ge, hc1_q_le1, hc0_q_nonneg, hc01_q, hratio_q⟩ :=
          quantized_coeff_ratio_pow_le p K t1 ht1_le_2K c1R c0R hc1R_gt hc1R_le1 hc0R_pos.le hc01R hratioR
        have hnorm_c1_q : ‖c1_q‖ = c1_qR := by
          dsimp only [c1_q]
          rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have hnorm_c0_q : ‖c0_q‖ = c0_qR := by
          dsimp only [c0_q]
          rw [Complex.norm_real, Real.norm_of_nonneg hc0_q_nonneg]
        have hc1_q_pos : 0 < ‖c1_q‖ := by linarith
        have hc1_q_ne : c1_q ≠ 0 := norm_pos_iff.mp hc1_q_pos
        have hc1_q_le1_norm : ‖c1_q‖ ≤ 1 := by linarith
        have hc01_q_norm : ‖c0_q‖ ≤ ‖c1_q‖ := by linarith
        have hratio_q_norm : (‖c0_q‖ / ‖c1_q‖) ^ t1 ≤ (0.1501 : ℝ) := by
          rw [hnorm_c0_q, hnorm_c1_q]
          exact hratio_q
        have hdenom_bwd_q : c1_q + c0_q * zHomBwd c0_q c1_q (t1 - 1) ≠ 0 :=
          denom_ne_zero_of_relaxed t1 c1_q c0_q (0.4999 : ℝ) (0.1501 : ℝ)
            le_rfl (by linarith) hratio_q_norm le_rfl
        have hrec_q := solveBidiagonalBwd_recover_exact t1 c0_q c1_q ht1 hc1_q_ne hdenom_bwd_q
          X Y_ideal_q h_bnd_q h_int_q u1_tilde hu1_tilde
        have ht1_sub_lt : t1 - 1 < t1 := Nat.sub_lt ht1 Nat.zero_lt_one
        have hrec_last := solveBidiagonalBwd_recover_exact t1 c0_q c1_q ht1 hc1_q_ne hdenom_bwd_q
          X Y_ideal_q h_bnd_q h_int_q (t1 - 1) ht1_sub_lt
        rw [solveBidiagonalBwd_eq_solveBidiagonalFwd_rev, Nat.sub_self] at hrec_last
        rw [← hrec_q,
            solveBidiagonalBwdQuantized_eq_solveBidiagonalFwdQuantized_rev,
            solveBidiagonalBwd_eq_solveBidiagonalFwd_rev]
        set d := t1 - 1 - u1_tilde
        have hd_lt : d < t1 :=
          Nat.lt_of_le_of_lt (Nat.sub_le (t1 - 1) u1_tilde) (Nat.sub_lt ht1 Nat.zero_lt_one)
        have h_eff := norm_solveBidiagonalFwdQuantized_sub_effRHS_le
          pSub t1 ht1 c1_q c0_q (by linarith) hc1_q_le1_norm hc01_q_norm hratio_q_norm
          (by linarith [ht1_qSub.2]) (bwdRevRHS t1 (Y u2)) d hd_lt
        have h_rev_rhs :
            ∀ k : ℕ,
              ‖zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2)) k -
                  bwdRevRHS t1 Y_ideal_q k‖ ≤ ε_rhs := by
          intro k
          have h_eff_step := norm_zPartFwdEffRHS_sub_le pSub c1_q c0_q hc1_q_ne hc1_q_le1_norm
            (bwdRevRHS t1 (Y u2)) k
          by_cases hk0 : k = 0
          · subst hk0
            have h1 : bwdRevRHS t1 (Y u2) 0 = Y u2 0 := rfl
            have h2 : bwdRevRHS t1 Y_ideal_q 0 = Y_ideal_q 0 := rfl
            rw [h1] at h_eff_step
            rw [h2]
            exact h_eff_ideal_q 0 _ h_eff_step
          · have h1 : bwdRevRHS t1 (Y u2) k = Y u2 (t1 - k) := if_neg hk0
            have h2 : bwdRevRHS t1 Y_ideal_q k = Y_ideal_q (t1 - k) := if_neg hk0
            rw [h1] at h_eff_step
            rw [h2]
            exact h_eff_ideal_q (t1 - k) _ h_eff_step
        have h_cyc := solveBidiagonalFwd_cyclic_error_bound_relaxed
          t1 ht1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q)
          (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2)))
          (0.4999 : ℝ) (0.1501 : ℝ) ε_rhs le_rfl (by linarith) hc01_q_norm hratio_q_norm le_rfl
          hε_rhs_nonneg h_rev_rhs d hd_lt
        have h_cyc_0 := solveBidiagonalFwd_cyclic_error_bound_relaxed
          t1 ht1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q)
          (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2)))
          (0.4999 : ℝ) (0.1501 : ℝ) ε_rhs le_rfl (by linarith) hc01_q_norm hratio_q_norm le_rfl
          hε_rhs_nonneg h_rev_rhs 0 ht1
        have hZ0_le :
            ‖solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) 0‖ ≤ 2 * M := by
          have htri0 := norm_add_le
            (solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) 0 -
              solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) 0)
            (solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) 0)
          rw [sub_add_cancel, hrec_last] at htri0
          rw [hrec_last] at h_cyc_0
          have hXlast := hX_norm (t1 - 1)
          linarith
        have hmul_Z0 :
            4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) *
              ‖solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) 0‖ ≤
              8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by
          calc 4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) *
                ‖solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) 0‖
              ≤ 4 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * (2 * M) :=
                mul_le_mul_of_nonneg_left hZ0_le
                  (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg t1) hqSub_nonneg))
            _ = 8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M := by ring
        have hsplit :
            solveBidiagonalFwdQuantized pSub t1 c1_q c0_q (bwdRevRHS t1 (Y u2)) d -
              solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) d =
            (solveBidiagonalFwdQuantized pSub t1 c1_q c0_q (bwdRevRHS t1 (Y u2)) d -
              solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) d) +
            (solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) d -
              solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) d) := by ring
        rw [hsplit]
        have htri := norm_add_le
          (solveBidiagonalFwdQuantized pSub t1 c1_q c0_q (bwdRevRHS t1 (Y u2)) d -
            solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) d)
          (solveBidiagonalFwd t1 c1_q c0_q (zPartFwdEffRHS pSub c1_q c0_q (bwdRevRHS t1 (Y u2))) d -
            solveBidiagonalFwd t1 c1_q c0_q (bwdRevRHS t1 Y_ideal_q) d)
        linarith
    have hD_lt :
        (2.001 : ℝ) * complexQuantizeMaxErr pSub +
          8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M <
          (0.003 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
      have h2 := hSub_err.2
      have h3 := ht1_qSub.1
      have hpart1 :
          (2.001 : ℝ) * complexQuantizeMaxErr pSub <
            (0.002001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
        calc (2.001 : ℝ) * complexQuantizeMaxErr pSub
            = (2.001 : ℝ) * (complexQuantizeMaxErr pSub * 1) := by ring
          _ ≤ (2.001 : ℝ) * (complexQuantizeMaxErr pSub * M) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM1 hqSub_nonneg) (by norm_num)
          _ < (2.001 : ℝ) * (((0.001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) * M) :=
              mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right h2 hM_pos) (by norm_num)
          _ = (0.002001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by ring
      have hpart2 :
          8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M ≤
            (0.0008 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
        calc 8 * ((t1 : ℝ) * complexQuantizeMaxErr pSub) * M
            ≤ 8 * ((0.0001 : ℝ) * (2 : ℝ) ^ (-(p : ℤ))) * M :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by norm_num)) hM_pos.le
          _ = (0.0008 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by ring
      have hpos_pow_M : 0 < (2 : ℝ) ^ (-(p : ℤ)) * M := by positivity
      linarith
    have hQ_lt :
        ‖complexQuantize p z_sub - z_sub‖ < (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M := by
      have hq_nonneg : 0 ≤ complexQuantizeMaxErr p := by
        unfold complexQuantizeMaxErr
        positivity
      calc ‖complexQuantize p z_sub - z_sub‖
          ≤ complexQuantizeMaxErr p := norm_complexQuantize_sub_le p z_sub
        _ = complexQuantizeMaxErr p * 1 := (mul_one _).symm
        _ ≤ complexQuantizeMaxErr p * M := mul_le_mul_of_nonneg_left hM1 hq_nonneg
        _ < (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
            mul_lt_mul_of_pos_right (complexQuantizeMaxErr_lt p) hM_pos
    have htri_final :
        ‖complexQuantize p z_sub - dft1D (t1 * r) x u‖ ≤
          ‖z_sub - dft1D (t1 * r) x u‖ + ‖complexQuantize p z_sub - z_sub‖ := by
      have hsplit : complexQuantize p z_sub - dft1D (t1 * r) x u =
          (z_sub - dft1D (t1 * r) x u) + (complexQuantize p z_sub - z_sub) := by ring
      rw [hsplit]
      exact norm_add_le _ _
    have hrhs_expand :
        (2.36 : ℝ) * (t1 : ℝ) * ε_rhs =
          (2.36 : ℝ) * (t1 : ℝ) * ((0.15 : ℝ) * (2 : ℝ) ^ (-(pWork p K : ℤ)) * M) +
            (2.36 : ℝ) * (t1 : ℝ) * (ε_total + (0.03 : ℝ) * (2 : ℝ) ^ (-(pChild p K : ℤ)) * M) := by
      dsimp only [ε_rhs]
      ring
    have hpow_p_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) * M :=
      mul_pos (zpow_pos (by norm_num) _) hM_pos
    linarith

/-- **Multi-Level Error Closure Theorem for Quantized Windowed Sinc-Gaussian `FastDFT` (`sincGaussianFastDFTQuantized_error_le`, `[MS]` Lemma 6.5, §6.3)**:
For any valid multi-level recursion tree `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`),
any input vector `x : ℕ → ℂ` and norm bound `1 ≤ M` with `∀ k < spec.size, ‖x k‖ ≤ M`,
and any frequency index `u < spec.size`, the multi-level quantized Sinc-Gaussian recursive
transform `sincGaussianFastDFTQuantized spec x u` (executing the pre-folded overlap-add quantized
signed-Kronecker spread, quantized twiddles, quantized `c0`/`c1` passband coefficients, step-rounded
3-regime solvers `solveBidiagonalFwdQuantized` / `solveNyquistQuantized` / `solveBidiagonalBwdQuantized`,
and sub-step rounding at `P`, `Q`, `qPost`, `Y`, and `z_sub`) satisfies:
`‖sincGaussianFastDFTQuantized spec x u - dft1D spec.size x u‖ ≤ (2 : ℝ) ^ (-(spec.p : ℤ)) * M`. -/
theorem sincGaussianFastDFTQuantized_error_le
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (x : ℕ → ℂ) (M : ℝ) (hM1 : 1 ≤ M)
    (hx : ∀ k < spec.size, ‖x k‖ ≤ M)
    (u : ℕ) (hu : u < spec.size) :
    ‖sincGaussianFastDFTQuantized spec x u - dft1D spec.size x u‖ ≤
      (2 : ℝ) ^ (-(spec.p : ℤ)) * M := by
  induction hvalid generalizing x M u with
  | base p R =>
    dsimp only [sincGaussianFastDFTQuantized, QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p]
    have hM_pos : 0 < M := by linarith
    have hq_nonneg : 0 ≤ complexQuantizeMaxErr p := by
      unfold complexQuantizeMaxErr
      positivity
    have h1 : ‖complexQuantize p (dft1D R x u) - dft1D R x u‖ ≤ complexQuantizeMaxErr p * M := by
      calc ‖complexQuantize p (dft1D R x u) - dft1D R x u‖
          ≤ complexQuantizeMaxErr p := norm_complexQuantize_sub_le p (dft1D R x u)
        _ = complexQuantizeMaxErr p * 1 := (mul_one _).symm
        _ ≤ complexQuantizeMaxErr p * M := mul_le_mul_of_nonneg_left hM1 hq_nonneg
    have h2 : complexQuantizeMaxErr p * M < (0.354 : ℝ) * (2 : ℝ) ^ (-(p : ℤ)) * M :=
      mul_lt_mul_of_pos_right (complexQuantizeMaxErr_lt p) hM_pos
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-(p : ℤ)) * M :=
      mul_pos (zpow_pos (by norm_num) _) hM_pos
    linarith
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p _hchild hv1 _hv1_lt ih =>
    dsimp only [sincGaussianFastDFTQuantized, QuantizedFastDFTSpec.size, QuantizedFastDFTSpec.p] at hx hu ⊢
    exact sincGaussianFastDFTStep_error_le hp hK ht1 ht1_le hr hr_le hsize hc1 heven hv1
      (sincGaussianFastDFTQuantized child)
      (fun x' M' hM1' hx' u' hu' => by
        rw [← hchild_p, ← hchild_size]
        exact ih x' M' hM1' (by rwa [hchild_size]) u' (by rwa [hchild_size]))
      x M hM1 hx u hu

/-- Linearity of `dft1D` under scalar multiplication. -/
theorem dft1D_smul (R : ℕ) (c : ℂ) (f : ℕ → ℂ) (u : ℕ) :
    dft1D R (fun j => c * f j) u = c * dft1D R f u := by
  unfold dft1D
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

/-- Linearity of `dft1D` under addition. -/
theorem dft1D_add (R : ℕ) (f g : ℕ → ℂ) (u : ℕ) :
    dft1D R (fun j => f j + g j) u = dft1D R f u + dft1D R g u := by
  unfold dft1D
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-- Linearity of `dft1D` under subtraction. -/
theorem dft1D_sub (R : ℕ) (f g : ℕ → ℂ) (u : ℕ) :
    dft1D R (fun j => f j - g j) u = dft1D R f u - dft1D R g u := by
  unfold dft1D
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- Natural-number cast of `cyclicConv R`. -/
theorem cyclicConv_natCast_eq (R : ℕ) (f g : ℕ → ℕ) (j : ℕ) :
    cyclicConv R (fun m => (f m : ℂ)) (fun m => (g m : ℂ)) j =
      ((∑ m ∈ Finset.range R, f m * g ((j + R - m % R) % R) : ℕ) : ℂ) := by
  unfold cyclicConv
  push_cast
  rfl

/-- Decomposition of `packNormalizedChunks` as `(1 / 2^b) * (a_j + I * b_j)`. -/
theorem packNormalizedChunks_eq_smul (b k1 k2 A B j : ℕ) :
    packNormalizedChunks b k1 k2 A B j =
      (1 / ((2 ^ b : ℕ) : ℂ)) *
        (((splitChunks b k1 A).getD j 0 : ℂ) +
          Complex.I * ((splitChunks b k2 B).getD j 0 : ℂ)) := by
  unfold packNormalizedChunks
  push_cast
  ring

/-- Exact algebraic expression for `(dft1D R (packNormalizedChunks b k1 k2 A B) u) ^ 2` as the
1D DFT of the normalized cyclic convolution combination `(a ⊛ a - b ⊛ b) + 2 i (a ⊛ b)`. -/
theorem dft1D_packNormalizedChunks_sq_eq
    (R : ℕ) (hR : 0 < R) (b k1 k2 A B u : ℕ) :
    let a : ℕ → ℂ := fun m => ((splitChunks b k1 A).getD m 0 : ℂ)
    let g : ℕ → ℂ := fun m => ((splitChunks b k2 B).getD m 0 : ℂ)
    (dft1D R (packNormalizedChunks b k1 k2 A B) u) ^ 2 =
      dft1D R (fun j =>
        (1 / (((2 ^ b : ℕ) : ℂ) ^ 2 * (R : ℂ))) *
          (cyclicConv R a a j - cyclicConv R g g j + 2 * Complex.I * cyclicConv R a g j)) u := by
  dsimp only
  let a : ℕ → ℂ := fun m => ((splitChunks b k1 A).getD m 0 : ℂ)
  let g : ℕ → ℂ := fun m => ((splitChunks b k2 B).getD m 0 : ℂ)
  have hR_ne : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  have hpack : packNormalizedChunks b k1 k2 A B =
      fun j => (1 / ((2 ^ b : ℕ) : ℂ)) * (a j + Complex.I * g j) :=
    funext (packNormalizedChunks_eq_smul b k1 k2 A B)
  rw [hpack, dft1D_smul, dft1D_complex_pack, mul_pow, two_call_square_identity]
  rw [dft1D_smul, dft1D_add, dft1D_sub, dft1D_smul,
      dft1D_cyclicConv R hR a a u,
      dft1D_cyclicConv R hR g g u,
      dft1D_cyclicConv R hR a g u]
  field_simp [hR_ne]

/-- **Exact 2-Call Conjugate-Inverse Recovery of `polyMulList` from `packNormalizedChunks` (`[MS]` §3.5, Lemma 3.4 & §7.1)**:
When `k1 + k2 ≤ 2 ^ K0` and `j < 2 ^ K0`, taking the conjugate-inverse 1D DFT of
`(dft1D (2 ^ K0) (packNormalizedChunks b k1 k2 A B)) ^ 2`, extracting the imaginary part, and
scaling by `2^{2 b + 2 K0 - 1}` recovers `((polyMulList (splitChunks b k1 A) (splitChunks b k2 B)).getD j 0 : ℝ)`
identically. -/
theorem dft1D_conj_inv_packNormalizedChunks_im_eq
    (b K0 k1 k2 A B : ℕ) (hk : k1 + k2 ≤ 2 ^ K0) (j : ℕ) (hj : j < 2 ^ K0) :
    (star (dft1D (2 ^ K0)
      (fun u => star ((dft1D (2 ^ K0) (packNormalizedChunks b k1 k2 A B) u) ^ 2)) j)).im *
      (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) =
    ((polyMulList (splitChunks b k1 A) (splitChunks b k2 B)).getD j 0 : ℝ) := by
  set R := 2 ^ K0
  have hR : 0 < R := pow_pos zero_lt_two K0
  have hR_ne : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  set xs := splitChunks b k1 A
  set ys := splitChunks b k2 B
  let a : ℕ → ℂ := fun m => (xs.getD m 0 : ℂ)
  let g : ℕ → ℂ := fun m => (ys.getD m 0 : ℂ)
  let F : ℕ → ℂ := fun m =>
    (1 / (((2 ^ b : ℕ) : ℂ) ^ 2 * (R : ℂ))) *
      (cyclicConv R a a m - cyclicConv R g g m + 2 * Complex.I * cyclicConv R a g m)
  have hsq_fun :
      (fun u => star ((dft1D R (packNormalizedChunks b k1 k2 A B) u) ^ 2)) =
      (fun u => star (dft1D R F u)) := by
    funext u
    rw [dft1D_packNormalizedChunks_sq_eq R hR b k1 k2 A B u]
  rw [hsq_fun]
  have hinv := dft1D_conjugate_inversion R hR F j hj
  have hstar_eq : star (dft1D R (fun u => star (dft1D R F u)) j) = (1 / (R : ℂ)) * F j := by
    calc star (dft1D R (fun u => star (dft1D R F u)) j)
        = (1 / (R : ℂ)) * ((R : ℂ) * star (dft1D R (fun u => star (dft1D R F u)) j)) := by
          field_simp [hR_ne]
      _ = (1 / (R : ℂ)) * F j := by rw [hinv]
  rw [hstar_eq]
  dsimp only [F]
  have hlen : xs.length + ys.length ≤ R := by
    rw [length_splitChunks, length_splitChunks]
    exact hk
  have hag : cyclicConv R a g j = ((polyMulList xs ys).getD j 0 : ℂ) :=
    cyclicConv_getD_eq_polyMulList_getD R xs ys hlen j hj
  have haa : cyclicConv R a a j =
      ((∑ m ∈ Finset.range R, xs.getD m 0 * xs.getD ((j + R - m % R) % R) 0 : ℕ) : ℂ) :=
    cyclicConv_natCast_eq R (fun m => xs.getD m 0) (fun m => xs.getD m 0) j
  have hgg : cyclicConv R g g j =
      ((∑ m ∈ Finset.range R, ys.getD m 0 * ys.getD ((j + R - m % R) % R) 0 : ℕ) : ℂ) :=
    cyclicConv_natCast_eq R (fun m => ys.getD m 0) (fun m => ys.getD m 0) j
  rw [hag, haa, hgg]
  set N_aa : ℕ := ∑ m ∈ Finset.range R, xs.getD m 0 * xs.getD ((j + R - m % R) % R) 0
  set N_gg : ℕ := ∑ m ∈ Finset.range R, ys.getD m 0 * ys.getD ((j + R - m % R) % R) 0
  set N_ag : ℕ := (polyMulList xs ys).getD j 0
  have hscale_c :
      (1 / (R : ℂ)) * ((1 / (((2 ^ b : ℕ) : ℂ) ^ 2 * (R : ℂ))) *
        ((N_aa : ℂ) - (N_gg : ℂ) + 2 * Complex.I * (N_ag : ℂ))) =
      ((((1 / (((2 ^ b : ℕ) : ℝ) ^ 2 * (R : ℝ) ^ 2)) * ((N_aa : ℝ) - (N_gg : ℝ)) : ℝ) : ℂ) +
        Complex.I * (((2 * (N_ag : ℝ) / (((2 ^ b : ℕ) : ℝ) ^ 2 * (R : ℝ) ^ 2) : ℝ) : ℂ))) := by
    push_cast
    ring
  rw [hscale_c]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, zero_mul,
    Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
  have hzpow :
      (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) =
        (((2 ^ b : ℕ) : ℝ) ^ 2 * (R : ℝ) ^ 2) / 2 := by
    dsimp [R]
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have hb2 : (2 : ℝ) ^ (2 * (b : ℤ)) = (((2 ^ b : ℕ) : ℝ) ^ 2) := by
      rw [mul_comm (2 : ℤ) (b : ℤ), zpow_mul, zpow_natCast, zpow_two]
      push_cast
      ring
    have hK2 : (2 : ℝ) ^ (2 * (K0 : ℤ)) = (((2 ^ K0 : ℕ) : ℝ) ^ 2) := by
      rw [mul_comm (2 : ℤ) (K0 : ℤ), zpow_mul, zpow_natCast, zpow_two]
      push_cast
      ring
    rw [hb2, hK2]
  rw [hzpow]
  have h2b_ne : ((2 ^ b : ℕ) : ℝ) ≠ 0 := by positivity
  have hR_real_ne : (R : ℝ) ≠ 0 := by positivity
  field_simp [h2b_ne, hR_real_ne]

/-- Approximate real convolution coefficient `C_approx(j)` produced by the multi-level
quantized finite-window Sinc-Gaussian FastDFT root pipeline (`[MS]` §§7.1–7.2):
1. Packs `A, B` into `x_AB = packNormalizedChunks b k1 k2 A B`,
2. Computes the quantized forward transform `y = sincGaussianFastDFTQuantized spec x_AB`,
3. Squares and quantizes pointwise `S_tilde u = complexQuantize (rootPrecision b K0) ((y u) ^ 2)`,
4. Computes the quantized conjugate-inverse transform
   `z_tilde j = star (sincGaussianFastDFTQuantized spec (fun u => star (S_tilde u)) j)`,
5. Extracts the imaginary part scaled by `2^{2b + 2K0 - 1}`. -/
noncomputable def quantizedFastDFTConvApprox
    (spec : QuantizedFastDFTSpec) (b K0 k1 k2 A B j : ℕ) : ℝ :=
  let x_AB := packNormalizedChunks b k1 k2 A B
  let y : ℕ → ℂ := sincGaussianFastDFTQuantized spec x_AB
  let p0 := rootPrecision b K0
  let S_tilde : ℕ → ℂ := fun u => complexQuantize p0 ((y u) ^ 2)
  let z_tilde : ℂ := star (sincGaussianFastDFTQuantized spec (fun u => star (S_tilde u)) j)
  (z_tilde.im) * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)

/-- **End-to-End Multi-Level Quantized Windowed Sinc-Gaussian `FastDFT` Integer Multiplication (`quantizedFastDFTMultiply`, `[MS]` §7)**:
Computes `A * B` via the full finite-precision quantized `sincGaussianFastDFTQuantized` pipeline
(executing the quantized signed-Kronecker spread at every recursive level),
rounding each `quantizedFastDFTConvApprox spec b K0 k1 k2 A B j` to the nearest integer
`⌊C_approx(j) + 1/2⌋.toNat` and reconstructing via carry propagation `reconstructChunks b`. -/
noncomputable def quantizedFastDFTMultiply
    (spec : QuantizedFastDFTSpec) (b K0 k1 k2 A B : ℕ) : ℕ :=
  let convNat : List ℕ :=
    (List.range (k1 + k2)).map (fun j =>
      ⌊quantizedFastDFTConvApprox spec b K0 k1 k2 A B j + (1 / 2 : ℝ)⌋.toNat)
  reconstructChunks b convNat

/-- General root-pipeline exact integer recovery for any approximate DFT operator `F : (ℕ → ℂ) → ℕ → ℂ`
satisfying the `2 ^ (-rootPrecision b K0) * M` norm error bound on `2 ^ K0` (`[MS]` §7.2). -/
theorem dftApproxConvApprox_round_eq
    (F : (ℕ → ℂ) → ℕ → ℂ)
    (b K0 k1 k2 A B : ℕ)
    (hF_err : ∀ (x : ℕ → ℂ) (M : ℝ), 1 ≤ M →
      (∀ k < 2 ^ K0, ‖x k‖ ≤ M) → ∀ u < 2 ^ K0,
      ‖F x u - dft1D (2 ^ K0) x u‖ ≤ (2 : ℝ) ^ (-(rootPrecision b K0 : ℤ)) * M)
    (hk : k1 + k2 ≤ 2 ^ K0) (j : ℕ) (hj : j < 2 ^ K0) :
    let x_AB := packNormalizedChunks b k1 k2 A B
    let y : ℕ → ℂ := F x_AB
    let p0 := rootPrecision b K0
    let S_tilde : ℕ → ℂ := fun u => complexQuantize p0 ((y u) ^ 2)
    let z_tilde : ℂ := star (F (fun u => star (S_tilde u)) j)
    let cApprox : ℝ := (z_tilde.im) * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)
    ⌊cApprox + (1 / 2 : ℝ)⌋ =
      ((polyMulList (splitChunks b k1 A) (splitChunks b k2 B)).getD j 0 : ℤ) := by
  dsimp only
  set R0 := 2 ^ K0
  have hR0 : 0 < R0 := pow_pos zero_lt_two K0
  set p0 := rootPrecision b K0
  have hp0_ge6 : 6 ≤ p0 := by
    dsimp [p0, rootPrecision]
    omega
  let x_AB := packNormalizedChunks b k1 k2 A B
  let w : ℕ → ℂ := dft1D R0 x_AB
  let y : ℕ → ℂ := F x_AB
  let S_tilde : ℕ → ℂ := fun u => complexQuantize p0 ((y u) ^ 2)
  let z_tilde : ℂ := star (F (fun u => star (S_tilde u)) j)
  let z_exact : ℂ := star (dft1D R0 (fun u => star ((w u) ^ 2)) j)
  let cApprox : ℝ := (z_tilde.im) * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)
  have hsqrt2_ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h_w_norm : ∀ u : ℕ, ‖w u‖ ≤ Real.sqrt 2 :=
    fun u => dft1D_packNormalizedChunks_norm_le_sqrt_two R0 hR0 b k1 k2 A B u
  have h_y_err : ∀ u < R0, ‖y u - w u‖ ≤ Real.sqrt 2 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
    intro u hu
    have herr := hF_err x_AB (Real.sqrt 2) hsqrt2_ge1
      (fun k _ => norm_packNormalizedChunks_le_sqrt_two b k1 k2 A B k) u hu
    rw [mul_comm] at herr
    exact herr
  have h_S_err : ∀ u : ℕ, ‖S_tilde u - (y u) ^ 2‖ ≤ complexQuantizeMaxErr p0 :=
    fun u => norm_complexQuantize_sub_le p0 ((y u) ^ 2)
  have h_S_norm : ∀ u < R0, ‖star (S_tilde u)‖ ≤ 3 := by
    intro u hu
    rw [norm_star]
    have h5 := (theorem5_root_squaring_and_pipeline_error_lt_eight_ulp
      p0 hp0_ge6 (w u) (y u) (S_tilde u) 0
      (h_w_norm u) (h_y_err u hu) (h_S_err u) (by positivity)).1
    have hzpow_le : (2 : ℝ) ^ (-(p0 : ℤ)) ≤ (1 / 64 : ℝ) := by
      calc (2 : ℝ) ^ (-(p0 : ℤ))
          ≤ (2 : ℝ) ^ (-6 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = (1 / 64 : ℝ) := by norm_num
    have h_Sw_le1 : ‖S_tilde u - (w u) ^ 2‖ ≤ 1 := by linarith
    have h_w2_le2 : ‖(w u) ^ 2‖ ≤ 2 := by
      rw [norm_pow]
      calc ‖w u‖ ^ 2
          ≤ (Real.sqrt 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h_w_norm u) 2
        _ = 2 := Real.sq_sqrt (by norm_num)
    have htri_S : ‖S_tilde u‖ ≤ ‖S_tilde u - (w u) ^ 2‖ + ‖(w u) ^ 2‖ := by
      have hsplit : S_tilde u = (S_tilde u - (w u) ^ 2) + (w u) ^ 2 := by ring
      conv_lhs => rw [hsplit]
      exact norm_add_le _ _
    linarith
  have h_nonempty : (Finset.range R0).Nonempty := Finset.nonempty_range_iff.mpr hR0.ne'
  obtain ⟨u_max, hu_max_mem, hu_max⟩ :=
    Finset.exists_max_image (Finset.range R0) (fun u => ‖S_tilde u - (w u) ^ 2‖) h_nonempty
  have hu_max_lt : u_max < R0 := Finset.mem_range.mp hu_max_mem
  set err_inv : ℝ := ‖z_tilde - z_exact‖
  have hinv_bound :
      err_inv ≤ ‖S_tilde u_max - (w u_max) ^ 2‖ + 3 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
    dsimp only [err_inv, z_tilde, z_exact]
    rw [← star_sub, norm_star]
    have hsplit :
        F (fun u => star (S_tilde u)) j -
          dft1D R0 (fun u => star ((w u) ^ 2)) j =
        (dft1D R0 (fun u => star (S_tilde u)) j - dft1D R0 (fun u => star ((w u) ^ 2)) j) +
          (F (fun u => star (S_tilde u)) j -
            dft1D R0 (fun u => star (S_tilde u)) j) := by ring
    rw [hsplit]
    have htri := norm_add_le
      (dft1D R0 (fun u => star (S_tilde u)) j - dft1D R0 (fun u => star ((w u) ^ 2)) j)
      (F (fun u => star (S_tilde u)) j -
        dft1D R0 (fun u => star (S_tilde u)) j)
    have h1 :
        ‖dft1D R0 (fun u => star (S_tilde u)) j - dft1D R0 (fun u => star ((w u) ^ 2)) j‖ ≤
          ‖S_tilde u_max - (w u_max) ^ 2‖ := by
      rw [← dft1D_sub]
      refine dft1D_norm_le R0 hR0 _ ‖S_tilde u_max - (w u_max) ^ 2‖ (fun u hu => ?_) j
      rw [← star_sub, norm_star]
      exact hu_max u hu
    have h2 :
        ‖F (fun u => star (S_tilde u)) j -
          dft1D R0 (fun u => star (S_tilde u)) j‖ ≤ 3 * (2 : ℝ) ^ (-(p0 : ℤ)) := by
      have herr := hF_err (fun u => star (S_tilde u)) 3 (by norm_num) h_S_norm j hj
      rw [mul_comm] at herr
      exact herr
    linarith
  set C_int : ℤ := ((polyMulList (splitChunks b k1 A) (splitChunks b k2 B)).getD j 0 : ℤ)
  have hC_bound :
      |cApprox - (C_int : ℝ)| ≤
        err_inv * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) := by
    dsimp only [cApprox, C_int]
    rw [Int.cast_natCast, ← dft1D_conj_inv_packNormalizedChunks_im_eq b K0 k1 k2 A B hk j hj]
    change |z_tilde.im * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) -
            z_exact.im * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)| ≤ _
    have hscale_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1) := by positivity
    rw [← sub_mul, abs_mul, abs_of_pos hscale_pos, ← Complex.sub_im]
    exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm (z_tilde - z_exact)) hscale_pos.le
  exact theorem5_root_pipeline_exact_int_recovery b K0
    (w u_max) (y u_max) (S_tilde u_max)
    err_inv cApprox C_int
    (h_w_norm u_max) (h_y_err u_max hu_max_lt) (h_S_err u_max) hinv_bound hC_bound

/-- **Constructive End-to-End Instantiation of `theorem5_root_pipeline_exact_int_recovery`
via Multi-Level Windowed `sincGaussianFastDFTQuantized` (Discharging `hw`, `hy`, `hS`, `hinv`, and `hC`, `[MS]` §7.2)**:
For any valid multi-level quantized specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`)
with `spec.size = 2 ^ K0` and `spec.p = rootPrecision b K0`, and any `k1 + k2 ≤ 2 ^ K0` and `j < 2 ^ K0`,
the multi-level quantized execution `quantizedFastDFTConvApprox spec b K0 k1 k2 A B j` constructively
discharges all five hypotheses `hw`, `hy`, `hS`, `hinv`, and `hC` of
`theorem5_root_pipeline_exact_int_recovery`, proving that nearest-integer rounding recovers the exact
integer Cauchy convolution coefficient `(polyMulList (splitChunks b k1 A) (splitChunks b k2 B)).getD j 0`. -/
theorem quantizedFastDFTConvApprox_round_eq
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (b K0 k1 k2 A B : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0) (j : ℕ) (hj : j < 2 ^ K0) :
    ⌊quantizedFastDFTConvApprox spec b K0 k1 k2 A B j + (1 / 2 : ℝ)⌋ =
      ((polyMulList (splitChunks b k1 A) (splitChunks b k2 B)).getD j 0 : ℤ) := by
  unfold quantizedFastDFTConvApprox
  exact dftApproxConvApprox_round_eq (sincGaussianFastDFTQuantized spec) b K0 k1 k2 A B
    (fun x M hM1 hx u hu => by
      rw [← hp0, ← hsize]
      exact sincGaussianFastDFTQuantized_error_le spec hvalid x M hM1 (by rwa [hsize]) u (by rwa [hsize]))
    hk j hj

/-- **Master Correctness Theorem for Multi-Level Quantized Windowed `quantizedFastDFTMultiply` (`[MS]` §7)**:
For any valid multi-level quantized Sinc-Gaussian recursion tree `spec : QuantizedFastDFTSpec`
(`hvalid : spec.Valid`) at root length `spec.size = 2 ^ K0` and root precision
`spec.p = rootPrecision b K0 = 2 b + 2 K0 + 6`, any chunk counts `k1 + k2 ≤ 2 ^ K0`, and any
natural numbers `A < (2^b)^{k_1}` and `B < (2^b)^{k_2}`, the finite-precision quantized
pipeline `quantizedFastDFTMultiply spec b K0 k1 k2 A B` (executing the quantized signed-Kronecker spread at every
level) recovers the exact integer product `A * B`. -/
theorem quantizedFastDFTMultiply_eq_mul
    (spec : QuantizedFastDFTSpec) (hvalid : spec.Valid)
    (b K0 k1 k2 : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0)
    (A B : ℕ) (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    quantizedFastDFTMultiply spec b K0 k1 k2 A B = A * B := by
  unfold quantizedFastDFTMultiply
  set xs := splitChunks b k1 A
  set ys := splitChunks b k2 B
  have hmap :
      (List.range (k1 + k2)).map
        (fun j => ⌊quantizedFastDFTConvApprox spec b K0 k1 k2 A B j + (1 / 2 : ℝ)⌋.toNat) =
      (List.range (k1 + k2)).map (fun j => (polyMulList xs ys).getD j 0) := by
    refine List.map_congr_left fun j hj_mem => ?_
    have hj_lt : j < k1 + k2 := List.mem_range.mp hj_mem
    have hj_R0 : j < 2 ^ K0 := by omega
    rw [quantizedFastDFTConvApprox_round_eq spec hvalid b K0 k1 k2 A B hsize hp0 hk j hj_R0,
        Int.toNat_natCast]
  have hpoly_len : (polyMulList xs ys).length ≤ k1 + k2 := by
    have := length_polyMulList_le xs ys
    rw [length_splitChunks, length_splitChunks] at this
    exact this
  dsimp only
  rw [hmap, reconstructChunks_eq_evalRadix, evalRadix_range_getD (2 ^ b) _ (k1 + k2) hpoly_len,
      ← reconstructChunks_eq_evalRadix]
  exact reconstructChunks_polyMulList_splitChunks b k1 k2 A B hA hB

/-- Instrumented multi-level quantized finite-window Sinc-Gaussian recursive `FastDFT`
(`sincGaussianFastDFTQuantizedWithCost`):
returns `(out, totalCost)`, where `out` is identically `sincGaussianFastDFTQuantized spec x`
(executing the quantized signed-Kronecker spread at every recursive level) and `totalCost : ℝ` is the
recursive cost accumulated across all `t_1` child subproblems at each internal node (plus
`localBase l` at each leaf `.base p R`). -/
noncomputable def sincGaussianFastDFTQuantizedWithCost :
    QuantizedFastDFTSpec → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → ℕ → (ℕ → ℂ) → (ℕ → ℂ) × ℝ
  | .base p R, _, _, localBase, l, x =>
    (fun u => complexQuantize p (dft1D R x u), localBase l)
  | .step p K t1 r _c1 v1Of child, localSyn, localOvh, localBase, l, x =>
    let α := alphaSchedule (pWork p K)
    let pSub := 2 * pChild p K
    let U := kroneckerSincGaussianSpreadArray α pSub (2 * pChild p K) t1 r x
    let P : ℕ → ℕ → ℂ := fun j1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (k2 : ℝ)) * U j1 k2)
    let Q : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (syntheticFFTRadix2Quantized pSub r (Nat.log2 t1) (r / t1) P v1 k2)
    let qPost : ℕ → ℕ → ℂ := fun v1 k2 =>
      complexQuantize pSub (complexQuantize pSub (zetaRoot r (-(k2 : ℝ))) * Q v1 k2)
    let childRes := fun v1 =>
      sincGaussianFastDFTQuantizedWithCost child localSyn localOvh localBase (l + 1) (qPost v1)
    let qHat : ℕ → ℕ → ℂ := fun v1 u2 => (childRes v1).1 u2
    let childCostSum : ℝ := ∑ v1 ∈ Finset.range t1, (childRes v1).2
    let Y : ℕ → ℕ → ℂ := fun u2 u1 => complexQuantize pSub (qHat (v1Of u2 u1) u2)
    let out : ℕ → ℂ := fun u =>
      let u2 := u % r
      let u1_tilde := u / r
      let y := (u2 : ℝ) / (r : ℝ)
      let c0 : ℂ := (realQuantize pSub (c0Coeff (realErfScaled α) y) : ℂ)
      let c1_pass : ℂ := (realQuantize pSub (c1Coeff (realErfScaled α) y) : ℂ)
      let z_sub :=
        if 2 * u2 < r then
          solveBidiagonalFwdQuantized pSub t1 c0 c1_pass (Y u2) u1_tilde
        else if 2 * u2 = r then
          solveNyquistQuantized pSub t1 c0 (Y u2) (complexQuantize pSub (nyquistAltSum t1 r x)) u1_tilde
        else
          solveBidiagonalBwdQuantized pSub t1 c0 c1_pass (Y u2) u1_tilde
      complexQuantize p z_sub
    (out, localSyn l + localOvh l + childCostSum)

/-- **First-Projection Equivalence (`sincGaussianFastDFTQuantizedWithCost` computes `sincGaussianFastDFTQuantized`)**:
For any `spec : QuantizedFastDFTSpec`, cost functions `localSyn localOvh localBase : ℕ → ℝ`, depth `l : ℕ`,
and input `x : ℕ → ℂ`, `(sincGaussianFastDFTQuantizedWithCost spec localSyn localOvh localBase l x).1 = sincGaussianFastDFTQuantized spec x`. -/
theorem sincGaussianFastDFTQuantizedWithCost_fst_eq
    (spec : QuantizedFastDFTSpec) (localSyn localOvh localBase : ℕ → ℝ) (l : ℕ) (x : ℕ → ℂ) :
    (sincGaussianFastDFTQuantizedWithCost spec localSyn localOvh localBase l x).1 =
      sincGaussianFastDFTQuantized spec x := by
  induction spec generalizing l x with
  | base p R => rfl
  | step p K t1 r c1 v1Of child ih =>
    funext u
    dsimp only [sincGaussianFastDFTQuantizedWithCost, sincGaussianFastDFTQuantized]
    simp only [ih]

/-- Predicate stating that a `QuantizedFastDFTSpec` tree matches a dimension schedule `(t1, R : ℕ → ℕ)`
with `rem` levels remaining starting at recursion depth `l`. -/
inductive QuantizedFastDFTSpec.MatchesSchedule (t1 R : ℕ → ℕ) : ℕ → ℕ → QuantizedFastDFTSpec → Prop where
  | base (l p : ℕ) : QuantizedFastDFTSpec.MatchesSchedule t1 R 0 l (.base p (R l))
  | step {rem l : ℕ} (p K c1 : ℕ) (v1Of : ℕ → ℕ → ℕ) (child : QuantizedFastDFTSpec)
      (hchild : QuantizedFastDFTSpec.MatchesSchedule t1 R rem (l + 1) child) :
      QuantizedFastDFTSpec.MatchesSchedule t1 R (rem + 1) l
        (.step p K (t1 l) (R (l + 1)) c1 v1Of child)

/-- **Exact Cost-Recurrence Bridge (`sincGaussianFastDFTQuantizedWithCost` Accumulates `fastDFTBranchingCost`)**:
Whenever `QuantizedFastDFTSpec.MatchesSchedule t1 R rem l spec`, the accumulated cost
`(sincGaussianFastDFTQuantizedWithCost spec localSyn localOvh localBase l x).2` equals
`fastDFTBranchingCost t1 localSyn localOvh localBase rem l`. -/
theorem sincGaussianFastDFTQuantizedWithCost_snd_eq_branchingCost
    (t1 R : ℕ → ℕ) (localSyn localOvh localBase : ℕ → ℝ)
    (rem l : ℕ) (spec : QuantizedFastDFTSpec)
    (hsched : QuantizedFastDFTSpec.MatchesSchedule t1 R rem l spec) (x : ℕ → ℂ) :
    (sincGaussianFastDFTQuantizedWithCost spec localSyn localOvh localBase l x).2 =
      fastDFTBranchingCost t1 localSyn localOvh localBase rem l := by
  induction hsched generalizing x with
  | base l p => rfl
  | @step rem l p K c1 v1Of child hchild ih =>
    dsimp only [sincGaussianFastDFTQuantizedWithCost, fastDFTBranchingCost]
    congr 1
    calc _ = ∑ _v1 ∈ Finset.range (t1 l),
          fastDFTBranchingCost t1 localSyn localOvh localBase rem (l + 1) :=
          Finset.sum_congr rfl fun v1 _ => ih _
      _ = (t1 l : ℝ) * fastDFTBranchingCost t1 localSyn localOvh localBase rem (l + 1) := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- Instrumented multi-level quantized finite-window Sinc-Gaussian integer multiplication
(`quantizedFastDFTMultiplyWithCost`, `[MS]` §7):
executes the 2-call complex-packed quantized pipeline using `sincGaussianFastDFTQuantizedWithCost`
for both the forward transform `fwd` and the conjugate-inverse transform `inv`, returning
`(product, fwd.2 + inv.2)`. -/
noncomputable def quantizedFastDFTMultiplyWithCost
    (spec : QuantizedFastDFTSpec) (localSyn localOvh localBase : ℕ → ℝ)
    (b K0 k1 k2 A B : ℕ) : ℕ × ℝ :=
  let x_AB := packNormalizedChunks b k1 k2 A B
  let fwd := sincGaussianFastDFTQuantizedWithCost spec localSyn localOvh localBase 0 x_AB
  let p0 := rootPrecision b K0
  let S_tilde : ℕ → ℂ := fun u => complexQuantize p0 ((fwd.1 u) ^ 2)
  let inv := sincGaussianFastDFTQuantizedWithCost spec localSyn localOvh localBase 0
    (fun u => star (S_tilde u))
  let convNat : List ℕ :=
    (List.range (k1 + k2)).map (fun j =>
      ⌊((star (inv.1 j)).im * (2 : ℝ) ^ (2 * (b : ℤ) + 2 * (K0 : ℤ) - 1)) + (1 / 2 : ℝ)⌋.toNat)
  (reconstructChunks b convNat, fwd.2 + inv.2)

/-- **First-Projection Equivalence (`quantizedFastDFTMultiplyWithCost` computes `quantizedFastDFTMultiply`)**:
For any `spec : QuantizedFastDFTSpec`, cost functions `localSyn localOvh localBase : ℕ → ℝ`, and
inputs `b K0 k1 k2 A B : ℕ`,
`(quantizedFastDFTMultiplyWithCost spec localSyn localOvh localBase b K0 k1 k2 A B).1 = quantizedFastDFTMultiply spec b K0 k1 k2 A B`. -/
theorem quantizedFastDFTMultiplyWithCost_fst_eq
    (spec : QuantizedFastDFTSpec) (localSyn localOvh localBase : ℕ → ℝ)
    (b K0 k1 k2 A B : ℕ) :
    (quantizedFastDFTMultiplyWithCost spec localSyn localOvh localBase b K0 k1 k2 A B).1 =
      quantizedFastDFTMultiply spec b K0 k1 k2 A B := by
  dsimp only [quantizedFastDFTMultiplyWithCost, quantizedFastDFTMultiply, quantizedFastDFTConvApprox]
  rw [sincGaussianFastDFTQuantizedWithCost_fst_eq, sincGaussianFastDFTQuantizedWithCost_fst_eq]

/-- **Master Correctness and `O(n log n)` Cost Bridge for `quantizedFastDFTMultiplyWithCost` (`[MS]` §7)**:
For any valid multi-level quantized specification `spec : QuantizedFastDFTSpec` (`hvalid : spec.Valid`)
matching a unit-expansion schedule `(t1, R)` of depth `L` (`QuantizedFastDFTSpec.MatchesSchedule t1 R L 0 spec`),
with `spec.size = 2 ^ K0`, `spec.p = rootPrecision b K0`, `k1 + k2 ≤ 2 ^ K0`, `A < (2^b)^{k_1}`, and `B < (2^b)^{k_2}`:
1. `(quantizedFastDFTMultiplyWithCost ...).1 = A * B` (exact product recovery from finite-precision arithmetic),
2. `(quantizedFastDFTMultiplyWithCost ...).2 = 2 * fastDFTBranchingCost t1 localSyn localOvh localBase L 0`, and
3. `(quantizedFastDFTMultiplyWithCost ...).2 ≤ 2 * multiplyBitComplexityBound C_syn C_ovh C_base n`. -/
theorem quantizedFastDFTMultiplyWithCost_eq_mul_and_le_multiplyBitComplexityBound
    (L n : ℕ) (t1 R : ℕ → ℕ)
    (localSyn localOvh localBase perElemSyn perElemOvh perElemBase : ℕ → ℝ)
    (C_syn C_ovh C_base K0_P P_log_P : ℝ)
    (spec : QuantizedFastDFTSpec)
    (hvalid : spec.Valid)
    (hsched : QuantizedFastDFTSpec.MatchesSchedule t1 R L 0 spec)
    (hR : ∀ d, R d = t1 d * R (d + 1))
    (hSyn : ∀ d, localSyn d = (R d : ℝ) * perElemSyn d)
    (hOvh : ∀ d, localOvh d = (R d : ℝ) * perElemOvh d)
    (hBase : ∀ d, localBase d = (R d : ℝ) * perElemBase d)
    (hC_syn : 0 ≤ C_syn) (hC_ovh_base : 0 ≤ C_ovh + C_base) (hK0_P : 0 ≤ K0_P)
    (h_syn : ∀ d ∈ Finset.range L, perElemSyn d ≤ C_syn * ((1 / 2 : ℝ) ^ d) * K0_P)
    (h_ovh : ∀ d ∈ Finset.range L, perElemOvh d ≤ C_ovh * P_log_P)
    (h_base : perElemBase L ≤ C_base * (L : ℝ) * P_log_P)
    (h_scale_syn : (R 0 : ℝ) * K0_P ≤ (n : ℝ) * Real.log (n : ℝ))
    (h_scale_ovh : (L : ℝ) * ((R 0 : ℝ) * P_log_P) ≤
      (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2)
    (b K0 k1 k2 A B : ℕ)
    (hsize : spec.size = 2 ^ K0) (hp0 : spec.p = rootPrecision b K0)
    (hk : k1 + k2 ≤ 2 ^ K0)
    (hA : A < (2 ^ b) ^ k1) (hB : B < (2 ^ b) ^ k2) :
    (quantizedFastDFTMultiplyWithCost spec localSyn localOvh localBase b K0 k1 k2 A B).1 = A * B ∧
    (quantizedFastDFTMultiplyWithCost spec localSyn localOvh localBase b K0 k1 k2 A B).2 =
      2 * fastDFTBranchingCost t1 localSyn localOvh localBase L 0 ∧
    (quantizedFastDFTMultiplyWithCost spec localSyn localOvh localBase b K0 k1 k2 A B).2 ≤
      2 * multiplyBitComplexityBound C_syn C_ovh C_base n := by
  have h1 : (quantizedFastDFTMultiplyWithCost spec localSyn localOvh localBase b K0 k1 k2 A B).1 = A * B := by
    rw [quantizedFastDFTMultiplyWithCost_fst_eq]
    exact quantizedFastDFTMultiply_eq_mul spec hvalid b K0 k1 k2 hsize hp0 hk A B hA hB
  have h2 : (quantizedFastDFTMultiplyWithCost spec localSyn localOvh localBase b K0 k1 k2 A B).2 =
      2 * fastDFTBranchingCost t1 localSyn localOvh localBase L 0 := by
    dsimp only [quantizedFastDFTMultiplyWithCost]
    rw [sincGaussianFastDFTQuantizedWithCost_snd_eq_branchingCost t1 R localSyn localOvh localBase L 0 spec hsched,
        sincGaussianFastDFTQuantizedWithCost_snd_eq_branchingCost t1 R localSyn localOvh localBase L 0 spec hsched]
    ring
  have hbound := fastDFTBranchingCost_le_multiplyBitComplexityBound L n t1 R
    localSyn localOvh localBase perElemSyn perElemOvh perElemBase
    C_syn C_ovh C_base K0_P P_log_P
    hR hSyn hOvh hBase hC_syn hC_ovh_base hK0_P h_syn h_ovh h_base h_scale_syn h_scale_ovh
  refine ⟨h1, h2, by linarith⟩

/-- **Conditional Asymptotic `O(n log n)` Bit Complexity of Instrumented `quantizedFastDFTMultiplyWithCost` Given `h_bound`**:
For any family of quantized recursion specifications `spec : ℕ → QuantizedFastDFTSpec`, local cost
schedules `localSyn localOvh localBase : ℕ → ℕ → ℝ`, and inputs `b K0 k1 k2 A B : ℕ → ℕ` whose
accumulated cost `(quantizedFastDFTMultiplyWithCost (spec n) ...).2` is non-negative and bounded by
`2 * multiplyBitComplexityBound C_syn C_ovh C_base n` for all `n ≥ 3` (as established by
`quantizedFastDFTMultiplyWithCost_eq_mul_and_le_multiplyBitComplexityBound`), the instrumented
quantized multiplication cost satisfies
`(fun n => (quantizedFastDFTMultiplyWithCost (spec n) (localSyn n) (localOvh n) (localBase n) (b n) (K0 n) (k1 n) (k2 n) (A n) (B n)).2) =O[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ))`. -/
theorem quantizedFastDFTMultiplyWithCost_snd_isBigO_n_log_n_of_bound
    (spec : ℕ → QuantizedFastDFTSpec)
    (localSyn localOvh localBase : ℕ → ℕ → ℝ)
    (b K0 k1 k2 A B : ℕ → ℕ)
    (C_syn C_ovh C_base : ℝ)
    (hC_ovh_base : 0 ≤ C_ovh + C_base)
    (h_nonneg : ∀ n, 3 ≤ n →
      0 ≤ (quantizedFastDFTMultiplyWithCost (spec n) (localSyn n) (localOvh n) (localBase n)
        (b n) (K0 n) (k1 n) (k2 n) (A n) (B n)).2)
    (h_bound : ∀ n, 3 ≤ n →
      (quantizedFastDFTMultiplyWithCost (spec n) (localSyn n) (localOvh n) (localBase n)
        (b n) (K0 n) (k1 n) (k2 n) (A n) (B n)).2 ≤
        2 * multiplyBitComplexityBound C_syn C_ovh C_base n) :
    (fun n : ℕ => (quantizedFastDFTMultiplyWithCost (spec n) (localSyn n) (localOvh n) (localBase n)
      (b n) (K0 n) (k1 n) (k2 n) (A n) (B n)).2) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound (2 * (2 * C_syn + 4 * (C_ovh + C_base))) ?_
  rw [Filter.eventually_atTop]
  refine ⟨3, fun n hn => ?_⟩
  have hn_real : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog_ge_one : 1 ≤ Real.log (n : ℝ) := one_le_log_of_three_le (n : ℝ) hn_real
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by linarith
  have h_nlogn_nonneg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := mul_nonneg hn_nonneg hlog_nonneg
  have h_cost_nonneg := h_nonneg n hn
  rw [Real.norm_of_nonneg h_cost_nonneg, Real.norm_of_nonneg h_nlogn_nonneg]
  have h1 := h_bound n hn
  have h2 := theorem5_multiply_bit_complexity_le_n_log_n C_syn C_ovh C_base hC_ovh_base n hn
  linarith


end IntMul
