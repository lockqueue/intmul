import SubNLogN.Math.Bridge.Algorithm
import SubNLogN.Math.Common.GridInt

/-!
# Bridge, integer forms: the fixed-point solver on numerators

Integer (`ℤ`-numerator) versions of the solver pieces of `Bridge/Components.lean` and of the
deconvolution stage of `Bridge/Algorithm.lean`, for the bridge's nearest rounding
`rr := roundHalfUpR` (ties toward `+∞`, the machine's rounding; `Common/RoundNearest.lean`), each
with a value lemma proved here against the `rr`-parametric definitions (`…R`). A complex value on
the `q`-grid is `gridValC q c` for a numerator pair `c : ℤ × ℤ`; a real parameter on the `p`-grid
is `A·2^{-p}` (definitionally `gridValR p A`). The roundings are the shared numerator primitives of
`Common/GridInt.lean`: `rhuShift`/`rhuShiftC` (= Machine `rhuPow`/`roundHalfUpShiftC`), `rhuDiv`,
and the truncation `tdivShift` (= `tdivPow`).

* `sweepPrefixInt`, `gridValC_sweepPrefixInt`: `sweepPrefixR roundHalfUpR` with `â = A·2^{-q}`.
* `cycSweepFwdInt`, `gridValC_cycSweepFwdInt`: `cycSweepFwdR roundHalfUpR` with
  `μ̂, â, γ̂ = M, A, G·2^{-q}`.
* `cycSweepInt`, `gridValC_cycSweepInt` (and `gridValC_cycSweepInt_of_eq`): `cycSweepR roundHalfUpR`
  in both orientations. The backward case reorients the input by `imod (1 - i) L` and reads the
  output at `imod (-j) L`, exactly as `cycSweepR`; the orientation flag is passed through unchanged
  (it is `decide (2u < t_h)` in `deconvAxisFixedR`).
* `powTruncInt`, `powTruncInt_spec`: `powTrunc Q (A·2^{-p}) L` (one `tdivShift` after every
  product; truncations are not parametrized).
* `closureFixedInt`, `closureFixedInt_spec`: `closureFixedR roundHalfUpR q Q (A·2^{-p}) L`, i.e. the
  nearest integer with ties toward `+∞` to `2^{Q+q}/(2^Q - X)`, `X` the numerator of the truncated
  power (`rhuDiv`; unconditional: when `2^Q = X` both sides are `0`).
* `deconvAxisInt`, `gridValC_deconvAxisInt`: `deconvAxisFixedR roundHalfUpR` when the tables of the
  axis are `q`-grid values with numerators `M, A, G` (for the digits `u < t_h`).
* `imod_lt`, `imod_one_sub`, `imod_neg`: `ℕ` closed forms of the cyclic index maps,
  `imod (1 - i) L = (L + 1 - i) % L` (`i ≤ L`) and `imod (-j) L = (L - j) % L` (`j ≤ L`).
-/

namespace SubNLogN.Math.Bridge.IntForms

open SubNLogN.Math.Common SubNLogN.Math.Common.GridInt

/-! ### Rounded products -/

/-- `truncR_gridValR` with `gridValR` unfolded. -/
private theorem truncR_shift (F s : ℕ) (z : ℤ) :
    truncR F ((z : ℝ) * gridUnit (F + s)) = (tdivShift z s : ℝ) * gridUnit F :=
  truncR_gridValR F s z

/-- One rounded product: `crnd roundHalfUpR q (a·z) = gridValC q (rhuShiftC q (A·c))` for
`a = A·2^{-q}` and `z = gridValC q c`. -/
theorem crnd_ofReal_mul (q : ℕ) (a : ℤ) (c : ℤ × ℤ) :
    crnd roundHalfUpR q ((((a : ℝ) * gridUnit q : ℝ) : ℂ) * gridValC q c) =
      gridValC q (rhuShiftC q (smulC a c)) :=
  (congrArg (crnd roundHalfUpR q) (ofReal_gridValR_mul_gridValC q q a c)).trans
    (crnd_roundHalfUpR_gridValC q q _)

/-- The rounded product with `-a` (the sweep step `rnd(-â·z)`). -/
theorem crnd_neg_ofReal_mul (q : ℕ) (a : ℤ) (c : ℤ × ℤ) :
    crnd roundHalfUpR q (-(((a : ℝ) * gridUnit q : ℝ) : ℂ) * gridValC q c) =
      gridValC q (rhuShiftC q (smulC (-a) c)) := by
  have h : -(((a : ℝ) * gridUnit q : ℝ) : ℂ) = ((((-a : ℤ) : ℝ) * gridUnit q : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, crnd_ofReal_mul]

/-! ### The two-pass cyclic sweep -/

/-- Integer form of `sweepPrefixR roundHalfUpR`: numerators at precision `q`, `â = A·2^{-q}`. -/
def sweepPrefixInt (q : ℕ) (A : ℤ) (B : ℕ → ℤ × ℤ) (Z0 : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => B 0 + rhuShiftC q (smulC (-A) Z0)
  | n + 1 => B (n + 1) + rhuShiftC q (smulC (-A) (sweepPrefixInt q A B Z0 n))

theorem gridValC_sweepPrefixInt (q : ℕ) (A : ℤ) (B : ℕ → ℤ × ℤ) (Z0 : ℤ × ℤ) (n : ℕ) :
    gridValC q (sweepPrefixInt q A B Z0 n) =
      sweepPrefixR roundHalfUpR q ((A : ℝ) * gridUnit q) (fun j => gridValC q (B j))
        (gridValC q Z0) n := by
  induction n with
  | zero => rw [sweepPrefixInt, sweepPrefixR, gridValC_add, crnd_neg_ofReal_mul]
  | succ n ih => rw [sweepPrefixInt, sweepPrefixR, gridValC_add, ← ih, crnd_neg_ofReal_mul]

/-- Integer form of `cycSweepFwdR roundHalfUpR`: `μ̂ = M·2^{-q}`, `â = A·2^{-q}`,
`γ̂ = G·2^{-q}`, and `Y_j` given by numerators at precision `q`. -/
def cycSweepFwdInt (q : ℕ) (M A G : ℤ) (L : ℕ) (Y : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ :=
  let b : ℕ → ℤ × ℤ := fun j => rhuShiftC q (smulC M (Y j))
  let zLast := rhuShiftC q (smulC G (sweepPrefixInt q A b 0 (L - 1)))
  fun j => if j = L - 1 then zLast else sweepPrefixInt q A b zLast j

/-- `cycSweepFwdR` with its `let`s unfolded. -/
theorem cycSweepFwdR_eq (rr : ℕ → ℝ → ℝ) (q : ℕ) (mu ahat gam : ℝ) (L : ℕ) (Y : ℕ → ℂ)
    (j : ℕ) :
    cycSweepFwdR rr q mu ahat gam L Y j =
      if j = L - 1 then
        crnd rr q ((gam : ℂ) *
          sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * Y j)) 0 (L - 1))
      else sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * Y j))
        (crnd rr q ((gam : ℂ) *
          sweepPrefixR rr q ahat (fun j => crnd rr q ((mu : ℂ) * Y j)) 0 (L - 1))) j := rfl

theorem gridValC_cycSweepFwdInt (q : ℕ) (M A G : ℤ) (L : ℕ) (Y : ℕ → ℤ × ℤ) (j : ℕ) :
    gridValC q (cycSweepFwdInt q M A G L Y j) =
      cycSweepFwdR roundHalfUpR q ((M : ℝ) * gridUnit q) ((A : ℝ) * gridUnit q)
        ((G : ℝ) * gridUnit q) L (fun j => gridValC q (Y j)) j := by
  have hb : (fun j => crnd roundHalfUpR q ((((M : ℝ) * gridUnit q : ℝ) : ℂ) * gridValC q (Y j))) =
      fun j => gridValC q (rhuShiftC q (smulC M (Y j))) :=
    funext fun j => crnd_ofReal_mul q M (Y j)
  rw [cycSweepFwdR_eq, hb]
  simp only [cycSweepFwdInt]
  split_ifs
  · rw [← gridValC_zero q, ← gridValC_sweepPrefixInt, crnd_ofReal_mul]
  · rw [← gridValC_zero q, ← gridValC_sweepPrefixInt, crnd_ofReal_mul,
      ← gridValC_sweepPrefixInt]

/-- Integer form of `cycSweepR roundHalfUpR`: the backward orientation reorients the input by
`i ↦ (1 - i) mod L` and reads the output at `(-j) mod L` (`imod`, as in `cycSweepR`). -/
def cycSweepInt (fwd : Bool) (q : ℕ) (M A G : ℤ) (L : ℕ) (Y : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ :=
  if fwd then cycSweepFwdInt q M A G L Y
  else fun j => cycSweepFwdInt q M A G L (fun i => Y (imod (1 - (i : ℤ)) L)) (imod (-(j : ℤ)) L)

theorem gridValC_cycSweepInt (fwd : Bool) (q : ℕ) (M A G : ℤ) (L : ℕ) (Y : ℕ → ℤ × ℤ)
    (j : ℕ) :
    gridValC q (cycSweepInt fwd q M A G L Y j) =
      cycSweepR roundHalfUpR fwd q ((M : ℝ) * gridUnit q) ((A : ℝ) * gridUnit q)
        ((G : ℝ) * gridUnit q) L (fun j => gridValC q (Y j)) j := by
  cases fwd
  · exact gridValC_cycSweepFwdInt q M A G L (fun i => Y (imod (1 - (i : ℤ)) L))
      (imod (-(j : ℤ)) L)
  · exact gridValC_cycSweepFwdInt q M A G L Y j

/-- `gridValC_cycSweepInt` with the real parameters and the input given by equations. -/
theorem gridValC_cycSweepInt_of_eq (fwd : Bool) (q : ℕ) {mu ahat gam : ℝ} {M A G : ℤ}
    (hmu : mu = (M : ℝ) * gridUnit q) (ha : ahat = (A : ℝ) * gridUnit q)
    (hg : gam = (G : ℝ) * gridUnit q) (L : ℕ) {Yc : ℕ → ℂ} {Y : ℕ → ℤ × ℤ}
    (hY : ∀ j, Yc j = gridValC q (Y j)) (j : ℕ) :
    gridValC q (cycSweepInt fwd q M A G L Y j) = cycSweepR roundHalfUpR fwd q mu ahat gam L Yc j := by
  have hY' : Yc = fun j => gridValC q (Y j) := funext hY
  subst hmu ha hg hY'
  exact gridValC_cycSweepInt fwd q M A G L Y j

/-! ### Truncated powering and the closure parameter -/

/-- Integer form of `powTrunc` at precision `Q` with base `a = A·2^{-p}`: the numerator of the
truncated power (`2^Q` for `L = 0`). -/
def powTruncInt (Q p : ℕ) (A : ℤ) (L : ℕ) : ℤ :=
  if _h : L = 0 then 2 ^ Q else
    if L % 2 = 0 then tdivShift (powTruncInt Q p A (L / 2) * powTruncInt Q p A (L / 2)) Q
    else tdivShift (tdivShift (powTruncInt Q p A (L / 2) * powTruncInt Q p A (L / 2)) Q * A) p
termination_by L
decreasing_by all_goals omega

theorem powTruncInt_spec (Q p : ℕ) (A : ℤ) (L : ℕ) :
    (powTruncInt Q p A L : ℝ) * gridUnit Q = powTrunc Q ((A : ℝ) * gridUnit p) L := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    rw [powTruncInt, powTrunc]
    by_cases h0 : L = 0
    · rw [dif_pos h0, dif_pos h0]
      push_cast
      exact two_pow_mul_gridUnit Q
    · rw [dif_neg h0, dif_neg h0]
      have hP := ih (L / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by norm_num))
      rw [← hP]
      set X := powTruncInt Q p A (L / 2)
      have hsq : (X : ℝ) * gridUnit Q * ((X : ℝ) * gridUnit Q) =
          ((X * X : ℤ) : ℝ) * gridUnit (Q + Q) := by
        push_cast; rw [gridUnit_add]; ring
      split_ifs
      · rw [hsq, truncR_shift]
      · have hmul : (tdivShift (X * X) Q : ℝ) * gridUnit Q * ((A : ℝ) * gridUnit p) =
            ((tdivShift (X * X) Q * A : ℤ) : ℝ) * gridUnit (Q + p) := by
          push_cast; rw [gridUnit_add]; ring
        rw [hsq, truncR_shift, hmul, truncR_shift]

/-- Integer form of `closureFixedR roundHalfUpR`: `γ̂ = rnd_q((1 - P)^{-1})` with `P = X·2^{-Q}`
the truncated power, i.e. the nearest integer (ties toward `+∞`) to `2^{Q+q}/(2^Q - X)`. -/
def closureFixedInt (q Q p : ℕ) (A : ℤ) (L : ℕ) : ℤ :=
  rhuDiv (2 ^ (Q + q)) (2 ^ Q - powTruncInt Q p A L)

theorem closureFixedInt_spec (q Q p : ℕ) (A : ℤ) (L : ℕ) :
    (closureFixedInt q Q p A L : ℝ) * gridUnit q =
      closureFixedR roundHalfUpR q Q ((A : ℝ) * gridUnit p) L := by
  unfold closureFixedR closureFixedInt
  rw [← powTruncInt_spec, roundHalfUpR_eq]
  set X := powTruncInt Q p A L
  have key : (1 - (X : ℝ) * gridUnit Q)⁻¹ * 2 ^ q =
      ((2 ^ (Q + q) : ℤ) : ℝ) / ((2 ^ Q - X : ℤ) : ℝ) := by
    have e : (1 : ℝ) - (X : ℝ) * gridUnit Q = ((2 : ℝ) ^ Q - X) / 2 ^ Q := by
      unfold gridUnit; field_simp
    rw [e, inv_div, pow_add]
    push_cast
    ring
  rw [key, floor_div_add_half]

/-! ### The deconvolution stage `B_h^{-1}` -/

/-- Integer form of `deconvAxisFixedR roundHalfUpR`: the solver parameters of digit `u` are the numerators
`M i u, A i u, G i u` at precision `q`, and the input is given by numerators `Yn`. -/
def deconvAxisInt {d : ℕ} (q : ℕ) (t : Fin d → ℕ) (M A G : Fin d → ℕ → ℤ) (i : Fin d)
    (Yn : Fin (totalLen t) → ℤ × ℤ) : Fin (totalLen t) → ℤ × ℤ :=
  fun f =>
    let w := aliasStep t i
    let j0 := (f : ℕ) / w
    let u := (((encFreq t).symm f i : Fin (t i)) : ℕ)
    cycSweepInt (decide (2 * u < t i)) q (M i u) (A i u) (G i u) (prefixProd t i)
      (fun j => Yn (shiftFin f (((j : ℤ) - (j0 : ℤ)) * (w : ℤ)))) j0

theorem gridValC_deconvAxisInt {d : ℕ} (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (M A G : Fin d → ℕ → ℤ) (i : Fin d)
    (hM : ∀ u, u < t i → T.mu i u = (M i u : ℝ) * gridUnit q)
    (hA : ∀ u, u < t i → T.ahat i u = (A i u : ℝ) * gridUnit q)
    (hG : ∀ u, u < t i → T.gam i u = (G i u : ℝ) * gridUnit q)
    (Yn : Fin (totalLen t) → ℤ × ℤ) (f : Fin (totalLen t)) :
    gridValC q (deconvAxisInt q t M A G i Yn f) =
      deconvAxisFixedR roundHalfUpR q t T i (gridValC q ∘ Yn) f := by
  have hu := ((encFreq t).symm f i).isLt
  simp only [deconvAxisInt, deconvAxisFixedR]
  exact gridValC_cycSweepInt_of_eq _ q (hM _ hu) (hA _ hu) (hG _ hu) _ (fun j => rfl) _

/-! ### Closed forms of the cyclic index maps -/

theorem imod_lt {L : ℕ} (hL : 0 < L) (n : ℤ) : imod n L < L := by
  unfold imod
  have h1 := Int.emod_nonneg n (by exact_mod_cast hL.ne' : (L : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos n (by exact_mod_cast hL : (0 : ℤ) < L)
  omega

/-- The reorientation index: `(1 - i) mod L = (L + 1 - i) mod L` for `i ≤ L` (in `ℕ`). -/
theorem imod_one_sub {L i : ℕ} (hi : i ≤ L) : imod (1 - (i : ℤ)) L = (L + 1 - i) % L := by
  unfold imod
  have e : (((L + 1 - i : ℕ) : ℤ)) = (1 - (i : ℤ)) + 1 * (L : ℤ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h : (1 - (i : ℤ)) % (L : ℤ) = (((L + 1 - i : ℕ) : ℤ)) % (L : ℤ) := by
    rw [e, Int.add_mul_emod_self_right]
  rw [h, ← Int.natCast_mod, Int.toNat_natCast]

/-- The readout index: `(-j) mod L = (L - j) mod L` for `j ≤ L` (in `ℕ`). -/
theorem imod_neg {L j : ℕ} (hj : j ≤ L) : imod (-(j : ℤ)) L = (L - j) % L := by
  unfold imod
  have e : (((L - j : ℕ) : ℤ)) = (-(j : ℤ)) + 1 * (L : ℤ) := by
    rw [Nat.cast_sub hj]; ring
  have h : (-(j : ℤ)) % (L : ℤ) = (((L - j : ℕ) : ℤ)) % (L : ℤ) := by
    rw [e, Int.add_mul_emod_self_right]
  rw [h, ← Int.natCast_mod, Int.toNat_natCast]

end SubNLogN.Math.Bridge.IntForms
