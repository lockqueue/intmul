import Contracts.W8

/-!
# W6b contracts: reciprocal division at the solver call sites

Pure-math part of W6b (division) for the TM2 formalization of the `IntMul` pipeline. Conventions follow
`Contracts/W8.lean`:
* a contract is a `def W8_<name> : Prop`;
* a sanity proof is a `theorem W8_<name>_holds`;
* helpers live under `IntMulTM.Contracts.W8.*`;
* there is no `sorry`.

Division route: one precomputed reciprocal per column, one correction step, bit-exact.

## Divisor inventory of one column
Notation: `S = 2^(q+2)` with `q = pSub`; `h = zHom[t1-1]`. Under `TablesFaithful` both coefficients
are real (`.2 = 0`, FTP:76), so every recurrence division reduces to division by one integer
(`W8_recStep_reduced`).

| column (PHP:200-205) | recurrence (class R; `t1 - 1` steps per builder) | boundary (class B; once) | other |
|---|---|---|---|
| Fwd, `2*u2 < r` | den `(c0.1*S)^2`; reduced divisor `c0.1` | den `‖c0*S + c1*h‖^2` | combine `/2^(q+2)`: shift |
| Nyquist, `2*u2 = r` | divisor `c0.1`; if `c0 = 0` the step is `-prev` | none | `/t1 = 2^m`: shift |
| Bwd, `r < 2*u2` | divisor `c1.1` (Fwd solver with swapped coefficients) | den `‖c1*S + c0*h'‖^2` | combine: shift |

The machine handles the two classes differently:
* **Class R.** One reciprocal `μ = ⌊2^H / d⌋` per column, for
  `d = W8.columnDivisor r u2 c0.1 c1.1`, which equals `max c0.1 c1.1` (`W8_columnDivisor_isMax`).
* **Class B.** The single boundary division per column uses schoolbook long division; the snapshot's
  `gRatioQuantize` is kept verbatim there.

The divisor is positive at every faithful call site (`W8_columnDivisor_pos_of_faithful`, proved),
so the zero branches are unreachable there. They are still stated: `W8_divRound_denNonpos` and
`W8_nyqStep_reduced`.

File:line abbreviations are as in `Contracts/W8.lean`; CES = `ComputableExactSolvers.lean`.
-/

namespace IntMulTM.Contracts

open IntMul

/-! ## (c0) `divRoundRatInt`: zero branch, signed Euclidean form, tie rule -/

/-- **W8_divRound_denNonpos (the `den ≤ 0` branch).** `divRoundRatInt` (CP:625-626)
returns `0` whenever `den ≤ 0`. At a recurrence call site `den = (a·S)^2` (`W8_ratio_classR`), so this
branch fires exactly when the divisor coefficient `a` is `0`. `W8.recStepReduced` keeps the branch. -/
def W8_divRound_denNonpos : Prop :=
  ∀ (num den : ℤ), den ≤ 0 → divRoundRatInt num den = 0

theorem W8_divRound_denNonpos_holds : W8_divRound_denNonpos := by
  intro num den h
  unfold divRoundRatInt
  rw [if_neg (not_lt.mpr h)]

/-- Signed Euclidean form of `divRoundRatInt` for a positive divisor. -/
theorem W8.divRound_euclid (x d : ℤ) (hd : 0 < d) :
    divRoundRatInt x d = x / d + if d ≤ 2 * (x % d) then 1 else 0 := by
  unfold divRoundRatInt
  rw [if_pos hd]
  have hxr : x % d + d * (x / d) = x := Int.emod_add_mul_ediv x d
  have hr0 : 0 ≤ x % d := Int.emod_nonneg x hd.ne'
  have hrd : x % d < d := Int.emod_lt_of_pos x hd
  have h2d : (0 : ℤ) < 2 * d := by omega
  split_ifs with hc
  · exact ((Int.ediv_emod_unique (a := 2 * x + d) (r := 2 * (x % d) - d) (q := x / d + 1)
      h2d).mpr ⟨by linear_combination 2 * hxr, by omega, by omega⟩).1
  · exact ((Int.ediv_emod_unique (a := 2 * x + d) (r := 2 * (x % d) + d) (q := x / d + 0)
      h2d).mpr ⟨by linear_combination 2 * hxr, by omega, by omega⟩).1

/-- **W8_divRound_euclid (signed Euclidean form and tie-breaking rule).** For `d > 0`,
`divRoundRatInt x d = x / d + [d ≤ 2·(x % d)]`, with Lean's Euclidean `/` and `%`
(`0 ≤ x % d < d`), for either sign of `x`. Exact ties `2·(x % d) = d` round toward `+∞`. The
machine's rounding is the Euclidean pair from `W8.barrettEuclid` plus one comparison. Proved below. -/
def W8_divRound_euclid : Prop :=
  ∀ (x d : ℤ), 0 < d → divRoundRatInt x d = x / d + if d ≤ 2 * (x % d) then 1 else 0

theorem W8_divRound_euclid_holds : W8_divRound_euclid := W8.divRound_euclid

/-- **W8_divRound_ties.** Concrete ties: `1/2 ↦ 1`, `-1/2 ↦ 0`, `-3/2 ↦ -1`. Rounding is toward
`+∞`, not away from zero. -/
def W8_divRound_ties : Prop :=
  divRoundRatInt 1 2 = 1 ∧ divRoundRatInt (-1) 2 = 0 ∧ divRoundRatInt (-3) 2 = -1

theorem W8_divRound_ties_holds : W8_divRound_ties := by
  unfold W8_divRound_ties
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Bounded-dividend Barrett division (exact Euclidean quotient from one reciprocal) -/

/-- Reciprocal (Barrett) Euclidean division with one correction step. The machine precomputes
`μ = ⌊2^H / d⌋` once per column. Per dividend `x` it forms the estimate `q̂ = (x·μ) >>> H`, an
arithmetic shift (floor). It then forms the remainder `x − q̂·d` and corrects once by `±1`. The
result is `(quotient, remainder)`. Per dividend this costs one multiplication by `μ`, one by `d`,
and O(1) shifts, additions and comparisons. -/
def W8.barrettEuclid (H : ℕ) (μ x d : ℤ) : ℤ × ℤ :=
  let qh := (x * μ) >>> H
  let rh := x - qh * d
  if rh < 0 then (qh - 1, rh + d) else if d ≤ rh then (qh + 1, rh - d) else (qh, rh)

/-- Barrett's estimate. With `μ = ⌊P / d⌋` and `|x| < P`, the estimate `⌊x·μ / P⌋` lies within one of
the Euclidean quotient `x / d`, for either sign of `x`. -/
theorem W8.barrett_estimate (P x d : ℤ) (hP : 0 < P) (hd : 0 < d) (hx : |x| < P) :
    x / d - 1 ≤ x * (P / d) / P ∧ x * (P / d) / P ≤ x / d + 1 := by
  have hPe : P % d + d * (P / d) = P := Int.emod_add_mul_ediv P d
  have he0 : 0 ≤ P % d := Int.emod_nonneg P hd.ne'
  have hed : P % d < d := Int.emod_lt_of_pos P hd
  have hxr : x % d + d * (x / d) = x := Int.emod_add_mul_ediv x d
  have hr0 : 0 ≤ x % d := Int.emod_nonneg x hd.ne'
  have hrd : x % d < d := Int.emod_lt_of_pos x hd
  obtain ⟨μ, hμ⟩ : ∃ μ, P / d = μ := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, P % d = e := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, x / d = q := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, x % d = r := ⟨_, rfl⟩
  rw [hμ, he] at hPe
  rw [he] at he0 hed
  rw [hq, hr] at hxr
  rw [hr] at hr0 hrd
  rw [hμ, hq]
  have habs1 : x ≤ |x| := le_abs_self x
  have habs2 : -x ≤ |x| := neg_le_abs x
  have hxe1 : x * e ≤ P * d := by
    have h1 : x * e ≤ |x| * e := mul_le_mul_of_nonneg_right habs1 he0
    have h2 : |x| * e ≤ P * e := mul_le_mul_of_nonneg_right hx.le he0
    have h3 : P * e ≤ P * d := mul_le_mul_of_nonneg_left hed.le hP.le
    linarith
  have hxe2 : -(x * e) ≤ P * d := by
    have h1 : -x * e ≤ |x| * e := mul_le_mul_of_nonneg_right habs2 he0
    have h2 : |x| * e ≤ P * e := mul_le_mul_of_nonneg_right hx.le he0
    have h3 : P * e ≤ P * d := mul_le_mul_of_nonneg_left hed.le hP.le
    have h4 : -x * e = -(x * e) := neg_mul x e
    linarith
  have k1 : x * e + x * (d * μ) = x * P := by rw [← mul_add, hPe]
  have k2 : r * P + d * q * P = x * P := by rw [← add_mul, hxr]
  have k3 : 0 ≤ r * P := mul_nonneg hr0 hP.le
  have k4 : r * P < d * P := mul_lt_mul_of_pos_right hrd hP
  constructor
  · rw [Int.le_ediv_iff_mul_le hP]
    have hm : (q - 1) * P * d ≤ x * μ * d := by linarith
    exact le_of_mul_le_mul_right hm hd
  · have hlt : x * μ / P < q + 2 := by
      rw [Int.ediv_lt_iff_lt_mul hP]
      have hm : x * μ * d < (q + 2) * P * d := by linarith
      exact lt_of_mul_lt_mul_right hm hd.le
    omega

/-- The Barrett pair is the exact Euclidean pair whenever `|x| < 2^H`, for any `d > 0`. -/
theorem W8.barrettEuclid_exact (H : ℕ) (x d : ℤ) (hd : 0 < d) (hx : |x| < ((2 ^ H : ℕ) : ℤ)) :
    W8.barrettEuclid H (((2 ^ H : ℕ) : ℤ) / d) x d = (x / d, x % d) := by
  have hP : (0 : ℤ) < ((2 ^ H : ℕ) : ℤ) := by positivity
  obtain ⟨hlo, hhi⟩ := W8.barrett_estimate _ x d hP hd hx
  have hxr : x % d + d * (x / d) = x := Int.emod_add_mul_ediv x d
  have hr0 : 0 ≤ x % d := Int.emod_nonneg x hd.ne'
  have hrd : x % d < d := Int.emod_lt_of_pos x hd
  simp only [W8.barrettEuclid, Int.shiftRight_eq_div_pow]
  obtain ⟨qh, hqh⟩ : ∃ qh, x * (((2 ^ H : ℕ) : ℤ) / d) / ((2 ^ H : ℕ) : ℤ) = qh := ⟨_, rfl⟩
  rw [hqh] at hlo hhi ⊢
  obtain ⟨q, hq⟩ : ∃ q, x / d = q := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, x % d = r := ⟨_, rfl⟩
  rw [hq] at hlo hhi hxr ⊢
  rw [hr] at hxr hr0 hrd ⊢
  rcases (show qh = q - 1 ∨ qh = q ∨ qh = q + 1 by omega) with h | h | h <;> subst h <;>
    split_ifs <;> first | (exfalso; linarith) | (congr 1 <;> linarith)

/-- Reciprocal rounding: the Barrett Euclidean pair plus the tie rule of `W8_divRound_euclid`. -/
def W8.divRoundBarrett (H : ℕ) (μ x d : ℤ) : ℤ :=
  (W8.barrettEuclid H μ x d).1 + if d ≤ 2 * (W8.barrettEuclid H μ x d).2 then 1 else 0

theorem W8.divRoundBarrett_exact (H : ℕ) (x d : ℤ) (hd : 0 < d) (hx : |x| < ((2 ^ H : ℕ) : ℤ)) :
    W8.divRoundBarrett H (((2 ^ H : ℕ) : ℤ) / d) x d = divRoundRatInt x d := by
  simp only [W8.divRoundBarrett, W8.barrettEuclid_exact H x d hd hx, W8.divRound_euclid x d hd]

/-- **W8_barrettEuclid_exact.** Assume the per-column reciprocal `μ = ⌊2^H / d⌋` and the
dividend bound `|x| < 2^H`. Then one correction step gives the exact signed Euclidean pair, for any
`d > 0`. `H` is a static per-node schedule value fixed by the dividend bound
(`W8_numBound_of_widths`).

*Proof (done below):* `W8.barrett_estimate` puts the estimate within one of `x / d`. -/
def W8_barrettEuclid_exact : Prop :=
  ∀ (H : ℕ) (x d : ℤ), 0 < d → |x| < ((2 ^ H : ℕ) : ℤ) →
    W8.barrettEuclid H (((2 ^ H : ℕ) : ℤ) / d) x d = (x / d, x % d)

theorem W8_barrettEuclid_exact_holds : W8_barrettEuclid_exact := W8.barrettEuclid_exact

/-- **W8_divRoundBarrett_exact.** Under the same premises, reciprocal rounding equals the snapshot's
`divRoundRatInt` bit-exactly, including ties toward `+∞`. -/
def W8_divRoundBarrett_exact : Prop :=
  ∀ (H : ℕ) (x d : ℤ), 0 < d → |x| < ((2 ^ H : ℕ) : ℤ) →
    W8.divRoundBarrett H (((2 ^ H : ℕ) : ℤ) / d) x d = divRoundRatInt x d

theorem W8_divRoundBarrett_exact_holds : W8_divRoundBarrett_exact := W8.divRoundBarrett_exact

/-! ## Reduced form at real coefficients (`TablesFaithful`: `c0.2 = c1.2 = 0`, FTP:76) -/

/-- Numerator `y·S − c·z` of a recurrence step with real multiplier `c`, per coordinate. -/
def W8.recNum (q : ℕ) (y : ℤ × ℤ) (c : ℤ) (z : ℤ × ℤ) : ℤ × ℤ :=
  (y.1 * ((2 ^ (q + 2) : ℕ) : ℤ) - c * z.1, y.2 * ((2 ^ (q + 2) : ℕ) : ℤ) - c * z.2)

/-- Reduced recurrence step with real divisor `a` and real multiplier `c`. Per coordinate it is
`divRoundRatInt (sign a · N) |a|` with `N = W8.recNum q y c z`. It is `(0, 0)` when `a = 0`, which
is the snapshot's `den = 0` branch. -/
def W8.recStepReduced (q : ℕ) (a c : ℤ) (y z : ℤ × ℤ) : ℤ × ℤ :=
  if a = 0 then (0, 0)
  else (divRoundRatInt (a.sign * (W8.recNum q y c z).1) |a|,
    divRoundRatInt (a.sign * (W8.recNum q y c z).2) |a|)

/-- `gRatioQuantize` at real coefficients, rewritten over `W8.recNum`. Rounding is unchanged. -/
theorem W8.gRatioQuantize_realCoeff (q : ℕ) (a c : ℤ) (y z : ℤ × ℤ) :
    gRatioQuantize q y (c, 0) z (a, 0) (0, 0) (0, 0) =
      (divRoundRatInt
          ((W8.recNum q y c z).1 * (a * ((2 ^ (q + 2) : ℕ) : ℤ)) * ((2 ^ (q + 2) : ℕ) : ℤ))
          ((a * ((2 ^ (q + 2) : ℕ) : ℤ)) * (a * ((2 ^ (q + 2) : ℕ) : ℤ))),
        divRoundRatInt
          ((W8.recNum q y c z).2 * (a * ((2 ^ (q + 2) : ℕ) : ℤ)) * ((2 ^ (q + 2) : ℕ) : ℤ))
          ((a * ((2 ^ (q + 2) : ℕ) : ℤ)) * (a * ((2 ^ (q + 2) : ℕ) : ℤ)))) := by
  unfold gRatioQuantize gDivQuantizeUnscaled gQuantizeRat gSub gAdd gMulUnit W8.recNum
  dsimp only
  congr 1 <;> congr 1 <;> ring

/-- Cancelling the common factor `|a|·S²` in one coordinate. -/
theorem W8.reduce_coord (N a S : ℤ) (ha : a ≠ 0) (hS : 0 < S) :
    divRoundRatInt (N * (a * S) * S) ((a * S) * (a * S)) = divRoundRatInt (a.sign * N) |a| := by
  have hsa : a.sign * |a| = a := Int.sign_mul_abs a
  have habs : |a| * |a| = a * a := abs_mul_abs_self a
  have hpos : 0 < |a| * (S * S) := mul_pos (abs_pos.mpr ha) (mul_pos hS hS)
  have e1 : N * (a * S) * S = (a.sign * N) * (|a| * (S * S)) := by
    calc N * (a * S) * S = N * (a.sign * |a|) * S * S := by rw [hsa]; ring
      _ = (a.sign * N) * (|a| * (S * S)) := by ring
  have e2 : (a * S) * (a * S) = |a| * (|a| * (S * S)) := by
    calc (a * S) * (a * S) = (a * a) * (S * S) := by ring
      _ = (|a| * |a|) * (S * S) := by rw [habs]
      _ = |a| * (|a| * (S * S)) := by ring
  rw [e1, e2, W8.divRoundRatInt_scale _ _ _ hpos]

theorem W8.recStep_reduced (q : ℕ) (a c : ℤ) (y z : ℤ × ℤ) :
    gRatioQuantize q y (c, 0) z (a, 0) (0, 0) (0, 0) = W8.recStepReduced q a c y z := by
  rw [W8.gRatioQuantize_realCoeff]
  unfold W8.recStepReduced
  have hS : (0 : ℤ) < ((2 ^ (q + 2) : ℕ) : ℤ) := by positivity
  split_ifs with ha
  · subst ha
    simp [divRoundRatInt]
  · rw [W8.reduce_coord _ _ _ ha hS, W8.reduce_coord _ _ _ ha hS]

/-- **W8_recStep_reduced.** At real coefficients, every recurrence step of the Fwd builders (CES:173,
212) and of the Bwd solver (through the swap, CES:306) is one rounded division per coordinate by the
single integer `a`. Here `a = c0.1` (Fwd) or `c1.1` (Bwd). The dividend is `sign a · (y·S − c·z)`
and the divisor `|a|`; the result is `(0, 0)` if `a = 0`. Proved below by cancelling `|a|·S²`
(`W8.divRoundRatInt_scale`). -/
def W8_recStep_reduced : Prop :=
  ∀ (q : ℕ) (a c : ℤ) (y z : ℤ × ℤ),
    gRatioQuantize q y (c, 0) z (a, 0) (0, 0) (0, 0) = W8.recStepReduced q a c y z

theorem W8_recStep_reduced_holds : W8_recStep_reduced := W8.recStep_reduced

/-- **W8_nyqStep_reduced (the Nyquist zero branch).** At a real coefficient `c0 = (a, 0)`
the Nyquist step (CES:363-367) is:
* exactly `-prev` when `a = 0`, not `(0, 0)`, because `gRescale q q` is the identity
  (`W8.gRescale_self`);
* otherwise the reduced step with divisor and multiplier both `a`.

Proved below. -/
def W8_nyqStep_reduced : Prop :=
  ∀ (q : ℕ) (a : ℤ) (y prev : ℤ × ℤ),
    gNyqStepQuantize q (a, 0) y prev =
      if a = 0 then (-prev.1, -prev.2) else W8.recStepReduced q a a y prev

theorem W8_nyqStep_reduced_holds : W8_nyqStep_reduced := by
  intro q a y prev
  unfold gNyqStepQuantize
  rw [W8.recStep_reduced]
  split_ifs <;> first | rfl | (rw [W8.gRescale_self]; rfl) | (exfalso; simp_all)

/-! ## The reciprocal step -/

/-- Both coordinates of `N` lie strictly inside `(−2^H, 2^H)`. This is the Barrett dividend bound. -/
def W8.NumBound (H : ℕ) (N : ℤ × ℤ) : Prop :=
  |N.1| < ((2 ^ H : ℕ) : ℤ) ∧ |N.2| < ((2 ^ H : ℕ) : ℤ)

/-- Reciprocal recurrence step at real coefficients, with divisor `a > 0` and multiplier `c`. Both
coordinates of `y·S − c·z` are divided by `a` using the column reciprocal `μ`. -/
def W8.recStepBarrett (q H : ℕ) (μ a c : ℤ) (y z : ℤ × ℤ) : ℤ × ℤ :=
  (W8.divRoundBarrett H μ (W8.recNum q y c z).1 a, W8.divRoundBarrett H μ (W8.recNum q y c z).2 a)

theorem W8.recStepBarrett_eq_reduced (q H : ℕ) (a c : ℤ) (y z : ℤ × ℤ) (ha : 0 < a)
    (hN : W8.NumBound H (W8.recNum q y c z)) :
    W8.recStepBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c y z = W8.recStepReduced q a c y z := by
  obtain ⟨h1, h2⟩ := hN
  unfold W8.recStepBarrett W8.recStepReduced
  rw [if_neg ha.ne', Int.sign_eq_one_of_pos ha, abs_of_pos ha, one_mul, one_mul,
    W8.divRoundBarrett_exact _ _ _ ha h1, W8.divRoundBarrett_exact _ _ _ ha h2]

theorem W8.recStepBarrett_eq (q H : ℕ) (a c : ℤ) (y z : ℤ × ℤ) (ha : 0 < a)
    (hN : W8.NumBound H (W8.recNum q y c z)) :
    W8.recStepBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c y z =
      gRatioQuantize q y (c, 0) z (a, 0) (0, 0) (0, 0) := by
  rw [W8.recStep_reduced]
  exact W8.recStepBarrett_eq_reduced q H a c y z ha hN

theorem W8.nyqStepBarrett_eq (q H : ℕ) (a : ℤ) (y z : ℤ × ℤ) (ha : 0 < a)
    (hN : W8.NumBound H (W8.recNum q y a z)) :
    W8.recStepBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a a y z = gNyqStepQuantize q (a, 0) y z := by
  rw [W8_nyqStep_reduced_holds q a y z, if_neg ha.ne']
  exact W8.recStepBarrett_eq_reduced q H a a y z ha hN

/-- **W8_recStepBarrett_exact (W6b core, `gRatioQuantize`).** At a recurrence call site
(`d1 = zHom = 0`) with real coefficients, divisor `a > 0` and dividends below `2^H`, the
reciprocal-plus-one-correction step equals the snapshot's `gRatioQuantize` exactly.

*Proof (done below):* `W8_recStep_reduced`, then `W8_divRoundBarrett_exact` per coordinate
(`sign a = 1`, `|a| = a`). -/
def W8_recStepBarrett_exact : Prop :=
  ∀ (q H : ℕ) (a c : ℤ) (y z : ℤ × ℤ), 0 < a → W8.NumBound H (W8.recNum q y c z) →
    W8.recStepBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c y z =
      gRatioQuantize q y (c, 0) z (a, 0) (0, 0) (0, 0)

theorem W8_recStepBarrett_exact_holds : W8_recStepBarrett_exact := W8.recStepBarrett_eq

/-- **W8_nyqStepBarrett_exact (W6b core, `gNyqStepQuantize`).** The same statement for the Nyquist
step with `c0 = (a, 0)`, `a > 0`; divisor and multiplier are both `a`. Proved below. -/
def W8_nyqStepBarrett_exact : Prop :=
  ∀ (q H : ℕ) (a : ℤ) (y prev : ℤ × ℤ), 0 < a → W8.NumBound H (W8.recNum q y a prev) →
    W8.recStepBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a a y prev = gNyqStepQuantize q (a, 0) y prev

theorem W8_nyqStepBarrett_exact_holds : W8_nyqStepBarrett_exact := W8.nyqStepBarrett_eq

/-- `|y·S − c·z| < 2·A·S` from `|y|, |z| < A` and `|c| ≤ S`. -/
theorem W8.abs_mulsub_lt (y z c S A : ℤ) (hS : 0 < S) (hy : |y| < A) (hz : |z| < A)
    (hc : |c| ≤ S) : |y * S - c * z| < 2 * A * S := by
  obtain ⟨hy1, hy2⟩ := abs_lt.mp hy
  obtain ⟨hz1, hz2⟩ := abs_lt.mp hz
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  have k1 : y * S < A * S := mul_lt_mul_of_pos_right hy2 hS
  have k2 : -A * S < y * S := mul_lt_mul_of_pos_right hy1 hS
  have k3 : 0 ≤ (S + c) * (A + z) := mul_nonneg (by linarith) (by linarith)
  have k4 : 0 ≤ (S - c) * (A - z) := mul_nonneg (by linarith) (by linarith)
  have k5 : 0 ≤ (S + c) * (A - z) := mul_nonneg (by linarith) (by linarith)
  have k6 : 0 ≤ (S - c) * (A + z) := mul_nonneg (by linarith) (by linarith)
  rw [abs_lt]
  constructor <;> nlinarith

/-- **W8_numBound_of_widths (Barrett shift `H` from the dividend bound).** Suppose `y` and `z` fit in
signed `w`-bit words (the hypotheses are CSWS's `FitsSignedWord w`, CSWS:15, unfolded) and
`|c| ≤ 2^(q+2)`. Then the recurrence dividend fits below `2^(w+q+2)`.

*Intended instantiation (W9):*
* recurrence states fit `4·p′` signed bits: `programCost_solvers_widths_sound` (CSWS:399), or its
  faithful form CSWS:1235;
* the multiplier satisfies `0 ≤ c ≤ 2^(pSub+2)` (hC01, FTP:77-78), with `pSub = 2·p′`;
* hence `H = 4·p′ + pSub + 2 = 6·p′ + 2`, a static per-node value.

The matching `4·p′` bound for the column input `Y` (the `y` of the zPart builders) must come from
CSWS:416-type input bounds; that derivation is not checked. Proved below. -/
def W8_numBound_of_widths : Prop :=
  ∀ (q w : ℕ) (y z : ℤ × ℤ) (c : ℤ), 1 ≤ w →
    (|y.1| < (2 : ℤ) ^ (w - 1) ∧ |y.2| < (2 : ℤ) ^ (w - 1)) →
    (|z.1| < (2 : ℤ) ^ (w - 1) ∧ |z.2| < (2 : ℤ) ^ (w - 1)) →
    |c| ≤ (2 : ℤ) ^ (q + 2) →
    W8.NumBound (w + q + 2) (W8.recNum q y c z)

theorem W8_numBound_of_widths_holds : W8_numBound_of_widths := by
  intro q w y z c hw hy hz hc
  have hS : ((2 ^ (q + 2) : ℕ) : ℤ) = (2 : ℤ) ^ (q + 2) := by push_cast; ring
  have hSpos : (0 : ℤ) < (2 : ℤ) ^ (q + 2) := by positivity
  have hH : ((2 ^ (w + q + 2) : ℕ) : ℤ) = 2 * (2 : ℤ) ^ (w - 1) * (2 : ℤ) ^ (q + 2) := by
    obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  unfold W8.NumBound W8.recNum
  dsimp only
  rw [hS, hH]
  exact ⟨W8.abs_mulsub_lt _ _ _ _ _ hSpos hy.1 hz.1 hc,
    W8.abs_mulsub_lt _ _ _ _ _ hSpos hy.2 hz.2 hc⟩

/-! ## Column level: builders and solvers with one reciprocal per column -/

/-- zPart builder (CES:167-173) with the reciprocal step. -/
def W8.zPartFwdBarrett (q H : ℕ) (μ a c : ℤ) (Y : Array (ℤ × ℤ)) : ℕ → Array (ℤ × ℤ)
  | 0 => #[(0, 0)]
  | n + 1 =>
    let arr := W8.zPartFwdBarrett q H μ a c Y n
    arr.push (W8.recStepBarrett q H μ a c (read1D Y (n + 1)) (read1D arr n))

/-- zHom builder (CES:207-212) with the reciprocal step. -/
def W8.zHomFwdBarrett (q H : ℕ) (μ a c : ℤ) : ℕ → Array (ℤ × ℤ)
  | 0 => #[(((2 ^ (q + 2) : ℕ) : ℤ), 0)]
  | n + 1 =>
    let arr := W8.zHomFwdBarrett q H μ a c n
    arr.push (W8.recStepBarrett q H μ a c (0, 0) (read1D arr n))

/-- Nyquist zPart builder (CES:395-401) with the reciprocal step. -/
def W8.zPartNyqBarrett (q H : ℕ) (μ a : ℤ) (Y : Array (ℤ × ℤ)) : ℕ → Array (ℤ × ℤ)
  | 0 => #[(0, 0)]
  | n + 1 =>
    let arr := W8.zPartNyqBarrett q H μ a Y n
    arr.push (W8.recStepBarrett q H μ a a (read1D Y (n + 1)) (read1D arr n))

/-- Dividend bounds along the snapshot's own zPart recurrence. -/
def W8.zPartFwdBound (q H : ℕ) (a c : ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) : Prop :=
  ∀ m < n, W8.NumBound H
    (W8.recNum q (read1D Y (m + 1)) c (read1D (buildComputableZPartFwdExact q (a, 0) (c, 0) Y m) m))

/-- Dividend bounds along the snapshot's own zHom recurrence. -/
def W8.zHomFwdBound (q H : ℕ) (a c : ℤ) (n : ℕ) : Prop :=
  ∀ m < n, W8.NumBound H
    (W8.recNum q (0, 0) c (read1D (buildComputableZHomFwdExact q (a, 0) (c, 0) m) m))

/-- Dividend bounds along the snapshot's own Nyquist zPart recurrence. -/
def W8.zPartNyqBound (q H : ℕ) (a : ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) : Prop :=
  ∀ m < n, W8.NumBound H
    (W8.recNum q (read1D Y (m + 1)) a (read1D (buildComputableZPartNyqExact q (a, 0) Y m) m))

/-- **W8_zPartFwd_reciprocal.** The zPart builder with one reciprocal of `a` equals
`buildComputableZPartFwdExact` (CES:167). Proved below by induction (`W8_recStepBarrett_exact`). -/
def W8_zPartFwd_reciprocal : Prop :=
  ∀ (q H : ℕ) (a c : ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ), 0 < a → W8.zPartFwdBound q H a c Y n →
    W8.zPartFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c Y n =
      buildComputableZPartFwdExact q (a, 0) (c, 0) Y n

theorem W8_zPartFwd_reciprocal_holds : W8_zPartFwd_reciprocal := by
  intro q H a c Y n ha
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hb
    have ih' := ih (fun m hm => hb m (by omega))
    simp only [W8.zPartFwdBarrett, buildComputableZPartFwdExact]
    rw [ih']
    congr 1
    exact W8.recStepBarrett_eq q H a c _ _ ha (hb n (by omega))

/-- **W8_zHomFwd_reciprocal.** The zHom builder with one reciprocal of `a` equals
`buildComputableZHomFwdExact` (CES:207). Proved below. -/
def W8_zHomFwd_reciprocal : Prop :=
  ∀ (q H : ℕ) (a c : ℤ) (n : ℕ), 0 < a → W8.zHomFwdBound q H a c n →
    W8.zHomFwdBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a c n = buildComputableZHomFwdExact q (a, 0) (c, 0) n

theorem W8_zHomFwd_reciprocal_holds : W8_zHomFwd_reciprocal := by
  intro q H a c n ha
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hb
    have ih' := ih (fun m hm => hb m (by omega))
    simp only [W8.zHomFwdBarrett, buildComputableZHomFwdExact]
    rw [ih']
    congr 1
    exact W8.recStepBarrett_eq q H a c _ _ ha (hb n (by omega))

/-- **W8_zPartNyq_reciprocal.** The Nyquist builder with one reciprocal of `a` equals
`buildComputableZPartNyqExact` (CES:395). Proved below (`W8_nyqStepBarrett_exact`). -/
def W8_zPartNyq_reciprocal : Prop :=
  ∀ (q H : ℕ) (a : ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ), 0 < a → W8.zPartNyqBound q H a Y n →
    W8.zPartNyqBarrett q H (((2 ^ H : ℕ) : ℤ) / a) a Y n = buildComputableZPartNyqExact q (a, 0) Y n

theorem W8_zPartNyq_reciprocal_holds : W8_zPartNyq_reciprocal := by
  intro q H a Y n ha
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hb
    have ih' := ih (fun m hm => hb m (by omega))
    simp only [W8.zPartNyqBarrett, buildComputableZPartNyqExact]
    rw [ih']
    congr 1
    exact W8.nyqStepBarrett_eq q H a _ _ ha (hb n (by omega))

/-- Forward column solver (CES:253-266) using the reciprocal builders. The class-B boundary `Z0` is
the snapshot's own `gRatioQuantize` (schoolbook, once per column). -/
def W8.solveFwdBarrett (q H t1 : ℕ) (μ a c : ℤ) (Y : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  let zPartArr := W8.zPartFwdBarrett q H μ a c Y (t1 - 1)
  let zHomArr := W8.zHomFwdBarrett q H μ a c (t1 - 1)
  let Z0 := gRatioQuantize q (read1D Y 0) (c, 0) (read1D zPartArr (t1 - 1)) (a, 0) (c, 0)
    (read1D zHomArr (t1 - 1))
  (runSequentialScanSteps
    (fun u1 => gCombineQuantize q (read1D zPartArr u1) Z0 (read1D zHomArr u1)) t1).outTape

/-- Backward column solver (CES:303-314): reverse, run the Fwd solver with swapped coefficients
(divisor `c`), reverse back. -/
def W8.solveBwdBarrett (q H t1 : ℕ) (μ a c : ℤ) (Y : Array (ℤ × ℤ)) : Array (ℤ × ℤ) :=
  (runReverseSteps t1
    (read1D (W8.solveFwdBarrett q H t1 μ c a (runBwdRevSteps t1 (read1D Y) t1).outTape)) t1).outTape

/-- Nyquist column solver (CES:457-470) with the reciprocal builder. The division by `t1 = 2^m` is
a shift (`W8_nyquistDivT1_shift`), and the output `gRescale q q` is dropped (`W8.gRescale_self`). -/
def W8.solveNyqBarrett (q H t1 m : ℕ) (μ a : ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ) :
    Array (ℤ × ℤ) :=
  let zPartArr := W8.zPartNyqBarrett q H μ a Y (t1 - 1)
  let alt_part : ℤ × ℤ := sumRangePair (fun v => gAltTerm v (read1D zPartArr v)) t1
  let diff : ℤ × ℤ :=
    (divRoundPow2 (alt_q.1 - alt_part.1) m, divRoundPow2 (alt_q.2 - alt_part.2) m)
  (runSequentialScanSteps (fun u1 => gAdd (read1D zPartArr u1) (gAltTerm u1 diff)) t1).outTape

/-- **W8_solveFwd_reciprocal.** Forward column solver equality. Proved below. -/
def W8_solveFwd_reciprocal : Prop :=
  ∀ (q H t1 : ℕ) (a c : ℤ) (Y : Array (ℤ × ℤ)), 0 < a →
    W8.zPartFwdBound q H a c Y (t1 - 1) → W8.zHomFwdBound q H a c (t1 - 1) →
    W8.solveFwdBarrett q H t1 (((2 ^ H : ℕ) : ℤ) / a) a c Y =
      computableSolveBidiagonalFwdExact q t1 (a, 0) (c, 0) Y

theorem W8_solveFwd_reciprocal_holds : W8_solveFwd_reciprocal := by
  intro q H t1 a c Y ha hP hH
  have h1 := W8_zPartFwd_reciprocal_holds q H a c Y (t1 - 1) ha hP
  have h2 := W8_zHomFwd_reciprocal_holds q H a c (t1 - 1) ha hH
  simp only [W8.solveFwdBarrett, computableSolveBidiagonalFwdExact,
    computableSolveBidiagonalFwdExactWithSteps, h1, h2]

/-- **W8_solveBwd_reciprocal ((f): the Bwd column divides by `c1`).** The Bwd column's reciprocal is
of `c = c1.1`, not of `c0.1`. Its dividend bounds are along the reversed input with swapped
coefficients. Proved below. -/
def W8_solveBwd_reciprocal : Prop :=
  ∀ (q H t1 : ℕ) (a c : ℤ) (Y : Array (ℤ × ℤ)), 0 < c →
    W8.zPartFwdBound q H c a (runBwdRevSteps t1 (read1D Y) t1).outTape (t1 - 1) →
    W8.zHomFwdBound q H c a (t1 - 1) →
    W8.solveBwdBarrett q H t1 (((2 ^ H : ℕ) : ℤ) / c) a c Y =
      computableSolveBidiagonalBwdExact q t1 (a, 0) (c, 0) Y

theorem W8_solveBwd_reciprocal_holds : W8_solveBwd_reciprocal := by
  intro q H t1 a c Y hc hP hH
  have h := W8_solveFwd_reciprocal_holds q H t1 c a _ hc hP hH
  simp only [W8.solveBwdBarrett, computableSolveBidiagonalBwdExact,
    computableSolveBidiagonalBwdExactWithSteps, h]

/-- **W8_solveNyq_reciprocal.** Nyquist column solver equality for `t1 = 2^m`. Proved below. -/
def W8_solveNyq_reciprocal : Prop :=
  ∀ (q H t1 m : ℕ) (a : ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ), t1 = 2 ^ m → 0 < a →
    W8.zPartNyqBound q H a Y (t1 - 1) →
    W8.solveNyqBarrett q H t1 m (((2 ^ H : ℕ) : ℤ) / a) a Y alt_q =
      computableSolveNyquistExact q t1 (a, 0) Y alt_q

theorem W8_solveNyq_reciprocal_holds : W8_solveNyq_reciprocal := by
  intro q H t1 m a Y alt_q ht1 ha hb
  have hz := W8_zPartNyq_reciprocal_holds q H a Y (t1 - 1) ha hb
  simp only [W8.solveNyqBarrett, computableSolveNyquistExact, computableSolveNyquistExactWithSteps,
    hz, W8.gRescale_self]
  rw [W8_nyquistDivT1_shift_holds t1 m _ _ ht1]

/-- The per-column class-R divisor at a pipeline step (PHP:200-205). Fwd and Nyquist columns divide
by `c0.1`; Bwd columns divide by `c1.1`. -/
def W8.columnDivisor (r u2 : ℕ) (a c : ℤ) : ℤ := if 2 * u2 ≤ r then a else c

/-- The per-column dispatch of PHP:196-205, built on the reciprocal solvers. -/
def W8.columnSolveBarrett (pSub H t1 m r u2 : ℕ) (a c : ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ) :
    Array (ℤ × ℤ) :=
  if 2 * u2 < r then W8.solveFwdBarrett pSub H t1 (((2 ^ H : ℕ) : ℤ) / a) a c Y
  else if 2 * u2 = r then W8.solveNyqBarrett pSub H t1 m (((2 ^ H : ℕ) : ℤ) / a) a Y alt_q
  else W8.solveBwdBarrett pSub H t1 (((2 ^ H : ℕ) : ℤ) / c) a c Y

/-- **W8_columnSolve_reciprocal.** One column of PHP:196-205 (`.1` of the cost-carrying solvers) at
real coefficients `(a, 0)`, `(c, 0)` equals the reciprocal dispatch. The premises are:
* a positive column divisor;
* `t1 = 2^m`;
* the dividend bounds of the active regime.

*Proof (done below):* the `_fst` lemmas PCP:610, 708, 872 and the three solver contracts. -/
def W8_columnSolve_reciprocal : Prop :=
  ∀ (pSub p' H t1 m r u2 : ℕ) (a c : ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ),
    t1 = 2 ^ m → 0 < W8.columnDivisor r u2 a c →
    (2 * u2 < r → W8.zPartFwdBound pSub H a c Y (t1 - 1) ∧ W8.zHomFwdBound pSub H a c (t1 - 1)) →
    (2 * u2 = r → W8.zPartNyqBound pSub H a Y (t1 - 1)) →
    (r < 2 * u2 → W8.zPartFwdBound pSub H c a (runBwdRevSteps t1 (read1D Y) t1).outTape (t1 - 1) ∧
      W8.zHomFwdBound pSub H c a (t1 - 1)) →
    W8.columnSolveBarrett pSub H t1 m r u2 a c Y alt_q =
      (if 2 * u2 < r then computableSolveBidiagonalFwdWithProgramCost pSub p' t1 (a, 0) (c, 0) Y
       else if 2 * u2 = r then computableSolveNyquistWithProgramCost pSub p' t1 (a, 0) Y alt_q
       else computableSolveBidiagonalBwdWithProgramCost pSub p' t1 (a, 0) (c, 0) Y).1

theorem W8_columnSolve_reciprocal_holds : W8_columnSolve_reciprocal := by
  intro pSub p' H t1 m r u2 a c Y alt_q ht1 hpos hF hN hB
  unfold W8.columnSolveBarrett
  unfold W8.columnDivisor at hpos
  split_ifs with h1 h2
  · rw [if_pos (show 2 * u2 ≤ r by omega)] at hpos
    rw [computableSolveBidiagonalFwdWithProgramCost_fst]
    exact W8_solveFwd_reciprocal_holds pSub H t1 a c Y hpos (hF h1).1 (hF h1).2
  · rw [if_pos (show 2 * u2 ≤ r by omega)] at hpos
    rw [computableSolveNyquistWithProgramCost_fst]
    exact W8_solveNyq_reciprocal_holds pSub H t1 m a Y alt_q ht1 hpos (hN h2)
  · rw [if_neg (show ¬ 2 * u2 ≤ r by omega)] at hpos
    rw [computableSolveBidiagonalBwdWithProgramCost_fst]
    exact W8_solveBwd_reciprocal_holds pSub H t1 a c Y hpos (hB (by omega)).1 (hB (by omega)).2

/-- **W8_columnSolve_callSite.** The same equality in the exact call-site shape of PHP:197-205. The
table pairs `c0 = read1D c0Table u2` and `c1 = read1D c1Table u2` have zero imaginary part (hC01,
FTP:76). Proved below from `W8_columnSolve_reciprocal`. -/
def W8_columnSolve_callSite : Prop :=
  ∀ (pSub p' H t1 m r u2 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ),
    c0.2 = 0 → c1.2 = 0 → t1 = 2 ^ m → 0 < W8.columnDivisor r u2 c0.1 c1.1 →
    (2 * u2 < r →
      W8.zPartFwdBound pSub H c0.1 c1.1 Y (t1 - 1) ∧ W8.zHomFwdBound pSub H c0.1 c1.1 (t1 - 1)) →
    (2 * u2 = r → W8.zPartNyqBound pSub H c0.1 Y (t1 - 1)) →
    (r < 2 * u2 →
      W8.zPartFwdBound pSub H c1.1 c0.1 (runBwdRevSteps t1 (read1D Y) t1).outTape (t1 - 1) ∧
        W8.zHomFwdBound pSub H c1.1 c0.1 (t1 - 1)) →
    W8.columnSolveBarrett pSub H t1 m r u2 c0.1 c1.1 Y alt_q =
      (if 2 * u2 < r then computableSolveBidiagonalFwdWithProgramCost pSub p' t1 c0 c1 Y
       else if 2 * u2 = r then computableSolveNyquistWithProgramCost pSub p' t1 c0 Y alt_q
       else computableSolveBidiagonalBwdWithProgramCost pSub p' t1 c0 c1 Y).1

theorem W8_columnSolve_callSite_holds : W8_columnSolve_callSite := by
  rintro pSub p' H t1 m r u2 ⟨a, a2⟩ ⟨c, c2⟩ Y alt_q h0 h1 ht1 hpos hF hN hB
  change a2 = 0 at h0
  change c2 = 0 at h1
  subst h0 h1
  exact W8_columnSolve_reciprocal_holds pSub p' H t1 m r u2 a c Y alt_q ht1 hpos hF hN hB

/-! ## Per-column constancy facts (denominator invariance across recurrence steps) -/

/-- Numerators of a class-R division (`d1 = zHom = 0`). -/
def W8.ratioNum (q : ℕ) (y c1 z c0 : ℤ × ℤ) : ℤ × ℤ :=
  let S : ℤ := ((2 ^ (q + 2) : ℕ) : ℤ)
  let N1 : ℤ := y.1 * S - (c1.1 * z.1 - c1.2 * z.2)
  let N2 : ℤ := y.2 * S - (c1.1 * z.2 + c1.2 * z.1)
  ((N1 * (c0.1 * S) + N2 * (c0.2 * S)) * S, (N2 * (c0.1 * S) - N1 * (c0.2 * S)) * S)

/-- Denominator of a class-R division. It depends on `(q, c0)` only. -/
def W8.ratioDen (q : ℕ) (c0 : ℤ × ℤ) : ℤ :=
  (c0.1 * ((2 ^ (q + 2) : ℕ) : ℤ)) * (c0.1 * ((2 ^ (q + 2) : ℕ) : ℤ)) +
    (c0.2 * ((2 ^ (q + 2) : ℕ) : ℤ)) * (c0.2 * ((2 ^ (q + 2) : ℕ) : ℤ))

/-- **W8_ratio_classR.** At a recurrence call site (`d1 = zHom = 0`), `gRatioQuantize` is one pair
of rounded divisions by `W8.ratioDen q c0`, for arbitrary complex `c0, c1`. That denominator is
independent of `y` and `z`, hence constant along a column (`W8_columnConstancy`). For general `d1`,
`zHom` it is not constant. Proved below. -/
def W8_ratio_classR : Prop :=
  ∀ (q : ℕ) (y c1 z c0 : ℤ × ℤ),
    gRatioQuantize q y c1 z c0 (0, 0) (0, 0) =
      gQuantizeRat (W8.ratioNum q y c1 z c0).1 (W8.ratioNum q y c1 z c0).2 (W8.ratioDen q c0)

theorem W8_ratio_classR_holds : W8_ratio_classR := by
  intro q y c1 z c0
  unfold gRatioQuantize gDivQuantizeUnscaled W8.ratioNum W8.ratioDen gSub gAdd gMulUnit
  dsimp only
  congr 1 <;> ring

/-- **W8_columnConstancy.** Every step of the three recurrence builders is a class-R call, with the
same `(c0, c1)` for the whole column:
* zPart (CES:173) and zHom (CES:212): `gRatioQuantize q _ c1 prev c0 (0,0) (0,0)`;
* Nyquist (CES:401): `gNyqStepQuantize q c0 _ prev`.

All three hold by `rfl`. -/
def W8_columnConstancy : Prop :=
  (∀ (q : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ),
    buildComputableZPartFwdExact q c0 c1 Y (n + 1) =
      (buildComputableZPartFwdExact q c0 c1 Y n).push
        (gRatioQuantize q (read1D Y (n + 1)) c1
          (read1D (buildComputableZPartFwdExact q c0 c1 Y n) n) c0 (0, 0) (0, 0))) ∧
  (∀ (q : ℕ) (c0 c1 : ℤ × ℤ) (n : ℕ),
    buildComputableZHomFwdExact q c0 c1 (n + 1) =
      (buildComputableZHomFwdExact q c0 c1 n).push
        (gRatioQuantize q (0, 0) c1 (read1D (buildComputableZHomFwdExact q c0 c1 n) n) c0
          (0, 0) (0, 0))) ∧
  (∀ (q : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ),
    buildComputableZPartNyqExact q c0 Y (n + 1) =
      (buildComputableZPartNyqExact q c0 Y n).push
        (gNyqStepQuantize q c0 (read1D Y (n + 1)) (read1D (buildComputableZPartNyqExact q c0 Y n) n)))

theorem W8_columnConstancy_holds : W8_columnConstancy :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- Denominator of the class-B boundary division of a Fwd column. -/
def W8.boundaryDen (q t1 : ℕ) (c0 c1 : ℤ × ℤ) : ℤ :=
  let S : ℤ := ((2 ^ (q + 2) : ℕ) : ℤ)
  let h := read1D (buildComputableZHomFwdExact q c0 c1 (t1 - 1)) (t1 - 1)
  let D1 : ℤ := c0.1 * S + (c1.1 * h.1 - c1.2 * h.2)
  let D2 : ℤ := c0.2 * S + (c1.1 * h.2 + c1.2 * h.1)
  D1 * D1 + D2 * D2

/-- **W8_boundary_classB.** The boundary solve `Z0` of the Fwd solver (CES:257) is one pair of
rounded divisions by `W8.boundaryDen q t1 c0 c1`. That denominator is independent of `Y`, but it is
available only after the zHom recurrence completes. It is the second denominator class of the
column. Its numerators depend on `Y` through `zPart[t1-1]`. Holds by `rfl`. -/
def W8_boundary_classB : Prop :=
  ∀ (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)), ∃ nRe nIm : ℤ,
    gRatioQuantize q (read1D Y 0) c1
        (read1D (buildComputableZPartFwdExact q c0 c1 Y (t1 - 1)) (t1 - 1)) c0 c1
        (read1D (buildComputableZHomFwdExact q c0 c1 (t1 - 1)) (t1 - 1)) =
      gQuantizeRat nRe nIm (W8.boundaryDen q t1 c0 c1)

theorem W8_boundary_classB_holds : W8_boundary_classB := fun _ _ _ _ _ => ⟨_, _, rfl⟩

/-- **W8_fwdBoundary_classB.** Structure of the Fwd solver (CES:253-266). The class-B division `Z0`
is computed once per column. Each of the `t1` outputs is a `gCombineQuantize`, which is a shift by
`q + 2` (`W8_gCombineQuantize_shift`). Holds by `rfl`. -/
def W8_fwdBoundary_classB : Prop :=
  ∀ (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)),
    computableSolveBidiagonalFwdExact q t1 c0 c1 Y =
      (runSequentialScanSteps (fun u1 =>
        gCombineQuantize q (read1D (buildComputableZPartFwdExact q c0 c1 Y (t1 - 1)) u1)
          (gRatioQuantize q (read1D Y 0) c1
            (read1D (buildComputableZPartFwdExact q c0 c1 Y (t1 - 1)) (t1 - 1)) c0 c1
            (read1D (buildComputableZHomFwdExact q c0 c1 (t1 - 1)) (t1 - 1)))
          (read1D (buildComputableZHomFwdExact q c0 c1 (t1 - 1)) u1)) t1).outTape

theorem W8_fwdBoundary_classB_holds : W8_fwdBoundary_classB := fun _ _ _ _ _ => rfl

/-- **W8_gCombineQuantize_shift.** The combine step (CES:144-147) divides by `S = 2^(q+2)`, so it is a
shift. Proved below. -/
def W8_gCombineQuantize_shift : Prop :=
  ∀ (q : ℕ) (a b c : ℤ × ℤ),
    gCombineQuantize q a b c =
      (divRoundPow2 (a.1 * ((2 ^ (q + 2) : ℕ) : ℤ) + (b.1 * c.1 - b.2 * c.2)) (q + 2),
       divRoundPow2 (a.2 * ((2 ^ (q + 2) : ℕ) : ℤ) + (b.1 * c.2 + b.2 * c.1)) (q + 2))

theorem W8_gCombineQuantize_shift_holds : W8_gCombineQuantize_shift := by
  intro q a b c
  unfold gCombineQuantize gQuantizeRat gAdd gMulUnit
  dsimp only
  rw [W8.divRoundRatInt_pow2, W8.divRoundRatInt_pow2]

/-! ## (f) Backward-solver divisor audit and divisor positivity -/

/-- **W8_bwdSolver_divisors ((f)).** The Bwd solver (CES:303-314) is `reverse ∘ Fwd(c1, c0) ∘ reverse`.
Its divisors are therefore:
* recurrences: class R with `W8.ratioDen q c1` (reduced divisor `c1.1`);
* boundary: class B with `W8.boundaryDen q t1 c1 c0 = ‖c1·S + c0·zHom'[t1-1]‖²`;
* outputs: combine, a shift by `q + 2`.

The reversals are data movement only (`runBwdRevSteps`, `runReverseSteps`). Holds by `rfl`. -/
def W8_bwdSolver_divisors : Prop :=
  ∀ (q t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)),
    computableSolveBidiagonalBwdExact q t1 c0 c1 Y =
      (runReverseSteps t1
        (read1D (computableSolveBidiagonalFwdExact q t1 c1 c0 (runBwdRevSteps t1 (read1D Y) t1).outTape))
        t1).outTape

theorem W8_bwdSolver_divisors_holds : W8_bwdSolver_divisors := fun _ _ _ _ _ => rfl

/-- **W8_columnDivisor_isMax.** Under the hC01 regime ordering (FTP:83-85; the `2*u2 = r` clause
gives `c1.1 = c0.1` via `congrArg Prod.fst`), the column divisor is `max c0.1 c1.1`. Proved below. -/
def W8_columnDivisor_isMax : Prop :=
  ∀ (r u2 : ℕ) (a c : ℤ),
    (2 * u2 < r → c ≤ a) → (2 * u2 = r → c = a) → (r < 2 * u2 → a ≤ c) →
    W8.columnDivisor r u2 a c = max a c

theorem W8_columnDivisor_isMax_holds : W8_columnDivisor_isMax := by
  intro r u2 a c h1 h2 h3
  unfold W8.columnDivisor
  split_ifs with h
  · rcases Nat.lt_or_eq_of_le h with hlt | heq
    · exact (max_eq_left (h1 hlt)).symm
    · exact (max_eq_left (h2 heq).le).symm
  · exact (max_eq_right (h3 (by omega))).symm

/-- Every step node of a table hierarchy has a positive column divisor in every column `u2 < r`. -/
def W8.ColumnDivisorsPos : ComputablePaperFastDFTSpec → Prop
  | .basePow2 _ _ _ => True
  | .step _ _ _ _ r _ _ _ c0Table c1Table child =>
      (∀ u2 < r, 0 < W8.columnDivisor r u2 (read1D c0Table u2).1 (read1D c1Table u2).1) ∧
        W8.ColumnDivisorsPos child

/-- A real table entry with norm at least `0.4999` (scale `2^(q+2)`) and nonnegative real part is
positive. -/
theorem W8.pos_of_norm_ge (q : ℕ) (c : ℤ × ℤ) (h2 : c.2 = 0) (h1 : 0 ≤ c.1)
    (hn : (0.4999 : ℝ) ≤ ‖toScaledComplex q c‖) : 0 < c.1 := by
  rcases h1.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hz : toScaledComplex q c = 0 := by
      apply Complex.ext <;> simp [toScaledComplex, ← heq, h2]
    rw [hz, norm_zero] at hn
    norm_num at hn

/-- **W8_columnDivisor_pos_of_faithful (positivity of column divisors; zero branches unreachable).** For a valid
schedule and faithful tables, every column divisor is positive, so `0 < a` holds at every reciprocal
call site.

*Proof (done below):* induction on `spec.Valid`. Each column uses
`faithful_c0_c1_solver_preconditions` (FTP:2898; it gives `0.4999 ≤ ‖c_q‖` for the active regime's
divisor) together with hC01's `.2 = 0` and `0 ≤ .1`. -/
def W8_columnDivisor_pos_of_faithful : Prop :=
  ∀ (cSpec : ComputablePaperFastDFTSpec) (spec : QuantizedFastDFTSpec),
    spec.Valid → TablesFaithful cSpec spec → W8.ColumnDivisorsPos cSpec

theorem W8_columnDivisor_pos_of_faithful_holds : W8_columnDivisor_pos_of_faithful := by
  intro cSpec spec hvalid hfaith
  induction hvalid generalizing cSpec with
  | base p R =>
    cases hfaith with
    | @base p K twiddles hp hK_le htw => simp [W8.ColumnDivisorsPos]
  | @step p K t1 r c1 v1Of child hp hK ht1 ht1_le hr hr_le hsize hc1 heven hchild_size hchild_p
      hchild hv1 hv1_lt ih =>
    cases hfaith with
    | @step p K t1 r c1 v1Of filterTaps preTwiddles postTwiddles c0Table c1Table cChild child
        hv1_eq hTaps hPre hPost hC01 hchild_faith =>
      dsimp only [W8.ColumnDivisorsPos]
      refine ⟨fun u2 hu2 => ?_, ih cChild hchild_faith⟩
      obtain ⟨hF, hN, hB⟩ := faithful_c0_c1_solver_preconditions p K t1 r hp hK ht1 hr hr_le hsize
        c0Table c1Table hC01 u2 hu2
      obtain ⟨hc0_im, hc1_im, hc0_nn, -, hc1_nn, -, -, -, -, -, -⟩ := hC01 u2 hu2
      unfold W8.columnDivisor
      split_ifs with h
      · have hn : (0.4999 : ℝ) ≤ ‖toScaledComplex (2 * pChild p K) (read1D c0Table u2)‖ := by
          rcases Nat.lt_or_eq_of_le h with hlt | heq
          · exact (hF hlt).1
          · exact (hN heq).1
        exact W8.pos_of_norm_ge _ _ hc0_im hc0_nn hn
      · exact W8.pos_of_norm_ge _ _ hc1_im hc1_nn (hB (by omega)).1

end IntMulTM.Contracts
