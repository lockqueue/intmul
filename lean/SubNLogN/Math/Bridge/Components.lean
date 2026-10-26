import SubNLogN.Math.Bridge.Operators
import SubNLogN.Math.Common.Grid
import SubNLogN.Math.Common.RoundNearest

/-!
# Bridge: Lemma 4.6 (bridge Lemma C), the finite-precision components (`lem:bridge-C`, Section 4.5)

Throughout `q = P + 2` and `v = 2^{-q} = gridUnit (P+2)` (Section 4.4 (`sec:bridge-alg`), and
`0.10·2^{-P} = 0.40 v` in C(i)). The primitive series evaluators of C(iii) (Machin `π`, `ln 2`,
Taylor series, `erf`) and the bit-cost claims of C(ii),(iii),(v) are tape-level (at machine level; IntMul's
`ComputableTranscendentals` provides certified `π`, `ln 2`, `stdChar`, `sincGaussian`, `c0/c1`
evaluators); here we state the value-level consequences used by Theorem 4.7.

The rounding-parametric versions `spreadAxisFixedR`, `sweepPrefixR`, `cycSweepFwdR`, `cycSweepR`,
`closureFixedR` (nearest rounding `rr`, last section) are the current interface; the
`quantC`/`quantR` versions `spreadAxisFixed`, `sweepPrefix`, `cycSweepFwd`, `cycSweep`,
`closureFixed` are legacy `quantC`/`quantR` specializations retained for compatibility.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

variable {d : ℕ}

/-- Hypotheses of Lemma 4.6 (bridge Lemma C) (`lem:bridge-C`): `P ≥ 20`, `8 ≤ ω ≤ P`,
`α² = 4 λ_G ω ln2/π` for a rational `λ_G ∈ [1,4]`, and `α > 0` (so `α` satisfies eq. (`eq:alpha`)). -/
def LemmaCParams (P ω : ℕ) (α : ℝ) : Prop :=
  20 ≤ P ∧ 8 ≤ ω ∧ ω ≤ P ∧ 0 < α ∧
    ∃ lamG : ℚ, 1 ≤ lamG ∧ lamG ≤ 4 ∧ α ^ 2 = 4 * (lamG : ℝ) * (ω : ℝ) * Real.log 2 / Real.pi

/-! ## Definitions (fixed-point spreading, certified taps, sweep, closure) -/

/-- One fixed-point spreading stage along Lean axis `i` (algorithm step (2), Section 4.4 (`sec:bridge-alg`);
Lemma 4.6 (bridge Lemma C)(ii)): exact accumulation of `∑_a V(update k i a) · tap(lowerIndex k, a - k_i)` (the
"exact product scale") and one nearest rounding `Quant_q` per output. `tap a e` is the stored tap
of shift `δ = a/A_h` at offset `e`. -/
noncomputable def spreadAxisFixed (q : ℕ) (t : Fin d → ℕ) (i : Fin d) (tap : ℕ → ℤ → ℂ)
    (V : Idx t → ℂ) : Idx t → ℂ :=
  fun k => quantC q (∑ a : Fin (t i), V (Function.update k i a) *
    tap (lowerIndex t i k) ((a : ℤ) - ((k i : ℕ) : ℤ)))

/-- Certified taps of one axis (Lemma 4.6 (bridge Lemma C)(ii) hypothesis "every complex tap certified to error
`2v`", `lem:bridge-C`; Theorem 4.7 (`thm:bridge-precision`)). Every stored tap lies on the
`q`-grid within `2v` of the truncated folded filter. Residues with no unfolded sample in `[-P,P]`
are exactly `0` (only the at most `2P+1` effective taps carry errors, proof of Lemma 4.6 (`lem:bridge-C`)(ii)).
Taps are `t_h`-periodic in the offset. -/
def TapsCertified (α : ℝ) (P : ℕ) (t : Fin d → ℕ) (i : Fin d) (tap : ℕ → ℤ → ℂ) : Prop :=
  ∀ a : ℕ, a < prefixProd t i → ∀ e : ℤ,
    OnGrid (P + 2) (tap a e) ∧
    ‖tap a e - truncFoldedFilter α (t i) P ((a : ℝ) / (prefixProd t i : ℝ)) e‖ ≤
      2 * gridUnit (P + 2) ∧
    ((∀ s ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), s % (t i : ℤ) ≠ e % (t i : ℤ)) → tap a e = 0) ∧
    tap a (e + (t i : ℤ)) = tap a e

/-- Prefix recurrence of the sweep (proof of Lemma 4.6 (`lem:bridge-C`)(iv)), started from `zinit`:
`z_0 = b_0 + Quant_q(-â·zinit)`, `z_{n+1} = b_{n+1} + Quant_q(-â·z_n)`. -/
noncomputable def sweepPrefix (q : ℕ) (ahat : ℝ) (b : ℕ → ℂ) (zinit : ℂ) : ℕ → ℂ
  | 0 => b 0 + quantC q (-(ahat : ℂ) * zinit)
  | n + 1 => b (n + 1) + quantC q (-(ahat : ℂ) * sweepPrefix q ahat b zinit n)

/-- The two-pass cyclic sweep in forward orientation (case `c_0 > c_1`,
proof of Lemma 4.6 (`lem:bridge-C`)(iv)), on a cycle `Y_0, …, Y_{L-1}`. Steps: `b_j = Quant_q(μ̂ Y_j)`; a prefix
pass from `z = 0`; the closure `Z_{L-1} = Quant_q(γ̂ z_{L-1})`; and a second pass of the same
recurrence from `Z_{L-1}`, which gives `Z_0, …, Z_{L-2}`. [Interpretation: the output at `L-1` is
the closure value, as in the proof of Lemma 4.6 (`lem:bridge-C`)(iv).] -/
noncomputable def cycSweepFwd (q : ℕ) (mu ahat gam : ℝ) (L : ℕ) (Y : ℕ → ℂ) : ℕ → ℂ :=
  let b : ℕ → ℂ := fun j => quantC q ((mu : ℂ) * Y j)
  let zLast := quantC q ((gam : ℂ) * sweepPrefix q ahat b 0 (L - 1))
  fun j => if j = L - 1 then zLast else sweepPrefix q ahat b zLast j

/-- `n mod L` (for `L > 0`) as a natural number. -/
def imod (n : ℤ) (L : ℕ) : ℕ := (n % (L : ℤ)).toNat

/-- The reorientation of the backward case (`c_1 > c_0`, proof of Lemma 4.6 (`lem:bridge-C`)(iv)):
`y'_i = Y_{(1-i) mod L}`. -/
def reorientIn (L : ℕ) (Y : ℕ → ℂ) : ℕ → ℂ := fun i => Y (imod (1 - (i : ℤ)) L)

/-- The two-pass sweep in either orientation. The backward case solves the reoriented system
and reads `Z_j = z_{(-j) mod L}`. -/
noncomputable def cycSweep (fwd : Bool) (q : ℕ) (mu ahat gam : ℝ) (L : ℕ) (Y : ℕ → ℂ) : ℕ → ℂ :=
  if fwd then cycSweepFwd q mu ahat gam L Y
  else fun j => cycSweepFwd q mu ahat gam L (reorientIn L Y) (imod (-(j : ℤ)) L)

/-- Zero extension of a cycle array to `ℕ`. -/
def extNat {L : ℕ} (Y : Fin L → ℂ) : ℕ → ℂ := fun j => if h : j < L then Y ⟨j, h⟩ else 0

/-- Binary powering of `a` with truncation toward zero at precision `Q` after every product
(Lemma 4.6 (bridge Lemma C)(v), `lem:bridge-C`; square-and-multiply on the binary digits of `L`). -/
noncomputable def powTrunc (Q : ℕ) (a : ℝ) (L : ℕ) : ℝ :=
  if _h : L = 0 then 1 else
    if L % 2 = 0 then truncR Q (powTrunc Q a (L / 2) * powTrunc Q a (L / 2))
    else truncR Q (truncR Q (powTrunc Q a (L / 2) * powTrunc Q a (L / 2)) * a)
termination_by L
decreasing_by all_goals omega

/-- The closure parameter `γ̂` from the stored `â` (Lemma 4.6 (bridge Lemma C)(v), `lem:bridge-C`):
truncated binary powering at precision `Q`, then division and one nearest rounding to the
`q`-grid. [The paper's "guarded division" is modelled as exact division before the final
rounding; a tape implementation must reproduce this value or prove the same bound.] -/
noncomputable def closureFixed (q Q : ℕ) (ahat : ℝ) (L : ℕ) : ℝ :=
  quantR q ((1 - powTrunc Q ahat L)⁻¹)

/-- The closure precision `Q = q + ⌈lg L⌉ + 2⌈lg(4t)⌉ + 10` (Lemma 4.6 (`lem:bridge-C`)(v)). -/
def closurePrec (q L t : ℕ) : ℕ := q + lg L + 2 * lg (4 * t) + 10

/-! ## Parametric-rounding versions (nearest-rounding parameter `rr`)

Each `…R` definition below is the definition of the same name without `R`, with every nearest
rounding replaced by the parameter `rr : ℕ → ℝ → ℝ` (leading argument): `crnd rr q` for complex
values and `rr q` for real values. Correctness statements assume `IsNearestRounding rr`
(`Common/RoundNearest.lean`): `rr q x` lies on the `q`-grid within half a grid unit of `x`.
`quantR` (ties to even; `crnd quantR = quantC`) and `roundHalfUpR` (ties toward `+∞`, the
machine's rounding) are instances. Truncations (`truncR`, `powTrunc`) are not parametrized. The
`quantC`/`quantR` definitions above are legacy `quantC`/`quantR` specializations retained for compatibility. -/

/-- `spreadAxisFixed` with nearest rounding `crnd rr q`: exact accumulation of
`∑_a V(update k i a) · tap(lowerIndex k, a - k_i)` and one rounding per output (Lemma 4.6 (bridge Lemma C)(ii)). -/
noncomputable def spreadAxisFixedR (rr : ℕ → ℝ → ℝ) (q : ℕ) (t : Fin d → ℕ) (i : Fin d)
    (tap : ℕ → ℤ → ℂ) (V : Idx t → ℂ) : Idx t → ℂ :=
  fun k => crnd rr q (∑ a : Fin (t i), V (Function.update k i a) *
    tap (lowerIndex t i k) ((a : ℤ) - ((k i : ℕ) : ℤ)))

/-- `sweepPrefix` with nearest rounding `crnd rr q` (proof of Lemma 4.6 (`lem:bridge-C`)(iv)):
`z_0 = b_0 + rnd(-â·zinit)`, `z_{n+1} = b_{n+1} + rnd(-â·z_n)`. -/
noncomputable def sweepPrefixR (rr : ℕ → ℝ → ℝ) (q : ℕ) (ahat : ℝ) (b : ℕ → ℂ) (zinit : ℂ) :
    ℕ → ℂ
  | 0 => b 0 + crnd rr q (-(ahat : ℂ) * zinit)
  | n + 1 => b (n + 1) + crnd rr q (-(ahat : ℂ) * sweepPrefixR rr q ahat b zinit n)

/-- `cycSweepFwd` with nearest rounding `crnd rr q`: `b_j = rnd(μ̂ Y_j)`, a prefix pass from
`z = 0`, the closure `Z_{L-1} = rnd(γ̂ z_{L-1})`, and a second pass from `Z_{L-1}` giving
`Z_0, …, Z_{L-2}` (proof of Lemma 4.6 (`lem:bridge-C`)(iv); the output at `L-1` is the closure value). -/
noncomputable def cycSweepFwdR (rr : ℕ → ℝ → ℝ) (q : ℕ) (mu ahat gam : ℝ) (L : ℕ) (Y : ℕ → ℂ) :
    ℕ → ℂ :=
  let b : ℕ → ℂ := fun j => crnd rr q ((mu : ℂ) * Y j)
  let zLast := crnd rr q ((gam : ℂ) * sweepPrefixR rr q ahat b 0 (L - 1))
  fun j => if j = L - 1 then zLast else sweepPrefixR rr q ahat b zLast j

/-- `cycSweep` with nearest rounding `rr`: the two-pass sweep in either orientation (the backward
case solves the reoriented system and reads `Z_j = z_{(-j) mod L}`). -/
noncomputable def cycSweepR (rr : ℕ → ℝ → ℝ) (fwd : Bool) (q : ℕ) (mu ahat gam : ℝ) (L : ℕ)
    (Y : ℕ → ℂ) : ℕ → ℂ :=
  if fwd then cycSweepFwdR rr q mu ahat gam L Y
  else fun j => cycSweepFwdR rr q mu ahat gam L (reorientIn L Y) (imod (-(j : ℤ)) L)

/-- `closureFixed` with nearest rounding `rr q` (Lemma 4.6 (bridge Lemma C)(v), `lem:bridge-C`):
truncated binary powering at precision `Q`, then exact division and one rounding `rr q`. -/
noncomputable def closureFixedR (rr : ℕ → ℝ → ℝ) (q Q : ℕ) (ahat : ℝ) (L : ℕ) : ℝ :=
  rr q ((1 - powTrunc Q ahat L)⁻¹)

end SubNLogN.Math.Bridge
