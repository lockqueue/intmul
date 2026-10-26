import SubNLogN.Math.Common.GridInt
import SubNLogN.Math.Walsh.DirectFFT

/-!
# Walsh middle: integer (numerator) forms of the value-level steps

Exact `ℤ`-arithmetic versions of the value-level steps of the Walsh middle (direct FFT, Section 6 (`sec:direct-fft`)), with
equality lemmas against the value-level definitions for the machine-level implementation.

Representation (`SubNLogN.Math.Common.GridInt`): a value on the `P`-grid is a numerator pair
`c : ℤ × ℤ` with value `gridValC P c = (c.1 + i c.2) 2^{-P}`; the stored numerators of a value `z`
are `gridIntC P z`, exact on the `P`-grid (`gridIntC_gridValC`, `gridValC_gridIntC`). `Q_P` of a
value at precision `P + s` is `tdivShiftC s` (`Int.tdiv` by `2^s`, truncation toward zero). The
operations `halfSumC`, `halfDiffC`, `cmulTruncC` below have the same bodies as their namesakes in
`SubNLogN.Machine` (and `GridInt.cmulC`, `tdivShiftC` are `Machine.cmulC`, `truncShiftC`), so the
machine bridge is `rfl`.

Main results (`gridIntC P (math step) = integer step (gridIntC P inputs)` for inputs on the grid):
* `gridIntC_truncC_mul`: Lemma 6.2, `Q_P(θu)` is four integer products and one truncation
  (`lem:disk-product`).
* `gridIntC_difLevel`, `gridIntC_coeffBitRev`, `gridIntC_lastAxisFFT` (and the `_phaseTable`
  versions with `phaseTableNum`): one rounded DIF level (half-sum / half-difference then `Q_P`,
  the lower output multiplied by its table phase and truncated again, proof of Theorem 6.5 (`thm:direct-fft`)),
  the bit reversal, and step (i) of the direct FFT.
* `gridIntC_truncC_hT`, `gridIntC_round`: `Q_P(H_T z)` is the exact signed sum `hTNum` over the
  `2^{|T|}` addresses agreeing off `T` followed by one truncation by `2^{|T|}`; the round protocol
  `Q_P(D̃ Q_P(H_T z))` (Theorem 6.5 (`thm:direct-fft`), eq. (`eq:round-protocol`)) is `roundInt`.
* `gridIntC_phaseTable`: the phase-table entries are the numerators `phaseTableNum`.
* `gridIntC_I_pow_mul`, `gridIntC_sDiag`, `gridIntC_czSign`, `gridIntC_two_pow_mul`,
  `gridIntC_one_sub_I_mul`: fourth-root phases (`rotC`), `S_U`, `CZ`, `2^e` and `1 - i` as exact
  integer maps (lifting to a finer grid is `GridInt.gridIntC_regrid`).
-/

namespace SubNLogN.Math.Walsh.IntForms

open SubNLogN.Math.Common SubNLogN.Math.Common.GridInt SubNLogN.Math.Walsh

/-! ## Arithmetic of numerator pairs (Machine-identical bodies) -/

/-- Upper butterfly output `Q_P((a + b)/2)` on numerators (body of `Machine.halfSumC`). -/
def halfSumC (a b : ℤ × ℤ) : ℤ × ℤ := tdivShiftC 1 (a.1 + b.1, a.2 + b.2)

/-- Lower butterfly output before its phase, `Q_P((a - b)/2)` (body of `Machine.halfDiffC`). -/
def halfDiffC (a b : ℤ × ℤ) : ℤ × ℤ := tdivShiftC 1 (a.1 - b.1, a.2 - b.2)

/-- Exact product, then truncation toward zero by `2^s` (body of `Machine.cmulTruncC`). -/
def cmulTruncC (s : ℕ) (a b : ℤ × ℤ) : ℤ × ℤ := tdivShiftC s (cmulC a b)

private theorem gridUnit_add' (P s : ℕ) : gridUnit (P + s) = gridUnit P * gridUnit s := by
  unfold gridUnit; rw [pow_add, mul_inv]

private theorem gridValC_add' (P : ℕ) (a b : ℤ × ℤ) :
    gridValC P a + gridValC P b = gridValC P (a.1 + b.1, a.2 + b.2) := by
  apply Complex.ext <;> simp [gridValC] <;> ring

private theorem gridValC_sub' (P : ℕ) (a b : ℤ × ℤ) :
    gridValC P a - gridValC P b = gridValC P (a.1 - b.1, a.2 - b.2) := by
  apply Complex.ext <;> simp [gridValC] <;> ring

private theorem gridValC_div_two (P : ℕ) (c : ℤ × ℤ) : gridValC P c / 2 = gridValC (P + 1) c := by
  apply Complex.ext <;> simp [gridValC, gridUnit] <;> ring

/-- `Q_P((x + y)/2)` on numerators (proof of Theorem 6.5 (`thm:direct-fft`)). -/
theorem truncC_halfSum (P : ℕ) (a b : ℤ × ℤ) :
    truncC P ((gridValC P a + gridValC P b) / 2) = gridValC P (halfSumC a b) := by
  rw [gridValC_add', gridValC_div_two, truncC_gridValC]; rfl

/-- `Q_P((x - y)/2)` on numerators. -/
theorem truncC_halfDiff (P : ℕ) (a b : ℤ × ℤ) :
    truncC P ((gridValC P a - gridValC P b) / 2) = gridValC P (halfDiffC a b) := by
  rw [gridValC_sub', gridValC_div_two, truncC_gridValC]; rfl

/-- Lemma 6.2 on numerators: `Q_P(xy) = cmulTruncC P` for `x, y` at precision `P`. -/
theorem truncC_mul_gridValC (P : ℕ) (a b : ℤ × ℤ) :
    truncC P (gridValC P a * gridValC P b) = gridValC P (cmulTruncC P a b) := by
  rw [gridValC_cmulC, truncC_gridValC]; rfl

/-- `gridIntC` form of Lemma 6.2: for `θ, u` on the `P`-grid,
`gridIntC P (Q_P(θu)) = cmulTruncC P (gridIntC P θ) (gridIntC P u)`. -/
theorem gridIntC_truncC_mul {P : ℕ} {θ u : ℂ} (hθ : OnGrid P θ) (hu : OnGrid P u) :
    gridIntC P (truncC P (θ * u)) = cmulTruncC P (gridIntC P θ) (gridIntC P u) := by
  conv_lhs => rw [← gridValC_gridIntC hθ, ← gridValC_gridIntC hu]
  rw [truncC_mul_gridValC, gridIntC_gridValC]

/-! ## The last axis: one rounded DIF level, bit reversal, the whole step (i) -/

/-- Coefficient `k` of a numerator vector, `(0, 0)` outside (integer form of `getCoeff`). -/
def getCoeffInt {n : ℕ} (w : Fin n → ℤ × ℤ) (k : ℕ) : ℤ × ℤ :=
  if h : k < n then w ⟨k, h⟩ else (0, 0)

theorem getCoeff_gridValC {n : ℕ} (P : ℕ) (w : Fin n → ℤ × ℤ) (k : ℕ) :
    getCoeff (fun i => gridValC P (w i)) k = gridValC P (getCoeffInt w k) := by
  unfold getCoeff getCoeffInt
  split_ifs
  · rfl
  · apply Complex.ext <;> simp [gridValC]

/-- `gridIntC` commutes with coefficient access (no grid hypothesis needed). -/
theorem gridIntC_getCoeff {n : ℕ} (P : ℕ) (w : Fin n → ℂ) (k : ℕ) :
    gridIntC P (getCoeff w k) = getCoeffInt (fun i => gridIntC P (w i)) k := by
  unfold getCoeff getCoeffInt
  split_ifs
  · rfl
  · simp [gridIntC]

/-- One rounded DIF level on numerators (integer form of `difLevel`, proof of Theorem 6.5 (`thm:direct-fft`)):
upper outputs `halfSumC`, lower outputs `cmulTruncC P θ̃ (halfDiffC …)`. -/
def difLevelInt (P ℓ s : ℕ) (θn : ℕ → ℤ × ℤ) (w : Fin (2 ^ ℓ) → ℤ × ℤ) :
    Fin (2 ^ ℓ) → ℤ × ℤ :=
  fun k =>
    if (k : ℕ) % 2 ^ (ℓ - s) < 2 ^ (ℓ - s - 1) then
      halfSumC (getCoeffInt w k) (getCoeffInt w ((k : ℕ) + 2 ^ (ℓ - s - 1)))
    else
      cmulTruncC P (θn (2 ^ (s + 1) * ((k : ℕ) % 2 ^ (ℓ - s) - 2 ^ (ℓ - s - 1))))
        (halfDiffC (getCoeffInt w ((k : ℕ) - 2 ^ (ℓ - s - 1))) (getCoeffInt w k))

/-- `difLevel` on numerator-valued data is `difLevelInt`. -/
theorem difLevel_gridValC (P ℓ s : ℕ) (θn : ℕ → ℤ × ℤ) (w : Fin (2 ^ ℓ) → ℤ × ℤ) :
    difLevel P ℓ s (fun j => gridValC P (θn j)) (fun k => gridValC P (w k)) =
      fun k => gridValC P (difLevelInt P ℓ s θn w k) := by
  funext k
  simp only [difLevel, difLevelInt, getCoeff_gridValC]
  split_ifs
  · exact truncC_halfSum P _ _
  · rw [truncC_halfDiff, truncC_mul_gridValC]

/-- **DIF level, integer form**: for inputs and table entries on the `P`-grid,
`gridIntC P (difLevel P ℓ s θ̃ w k) = difLevelInt P ℓ s (gridIntC P ∘ θ̃) (gridIntC P ∘ w) k`. -/
theorem gridIntC_difLevel {P ℓ s : ℕ} {θt : ℕ → ℂ} {w : Fin (2 ^ ℓ) → ℂ}
    (hθ : ∀ j, OnGrid P (θt j)) (hw : ∀ k, OnGrid P (w k)) (k : Fin (2 ^ ℓ)) :
    gridIntC P (difLevel P ℓ s θt w k) =
      difLevelInt P ℓ s (fun j => gridIntC P (θt j)) (fun i => gridIntC P (w i)) k := by
  have e1 : θt = fun j => gridValC P (gridIntC P (θt j)) :=
    funext fun j => (gridValC_gridIntC (hθ j)).symm
  have e2 : w = fun i => gridValC P (gridIntC P (w i)) :=
    funext fun i => (gridValC_gridIntC (hw i)).symm
  conv_lhs => rw [e1, e2, difLevel_gridValC]
  exact gridIntC_gridValC P _

/-- Bit reversal of the coefficient index on numerators. -/
def coeffBitRevInt {ℓ : ℕ} (w : Fin (2 ^ ℓ) → ℤ × ℤ) : Fin (2 ^ ℓ) → ℤ × ℤ :=
  fun k => getCoeffInt w (bitRevNat ℓ k)

theorem coeffBitRev_gridValC {ℓ : ℕ} (P : ℕ) (w : Fin (2 ^ ℓ) → ℤ × ℤ) :
    coeffBitRev (fun k => gridValC P (w k)) = fun k => gridValC P (coeffBitRevInt w k) := by
  funext k
  exact getCoeff_gridValC P w _

/-- `gridIntC` commutes with the bit reversal (no grid hypothesis needed). -/
theorem gridIntC_coeffBitRev {ℓ : ℕ} (P : ℕ) (w : Fin (2 ^ ℓ) → ℂ) (k : Fin (2 ^ ℓ)) :
    gridIntC P (coeffBitRev w k) = coeffBitRevInt (fun i => gridIntC P (w i)) k :=
  gridIntC_getCoeff P w _

/-- Step (i) on numerators: the `ℓ` rounded DIF levels, then bit reversal, on every record. -/
def lastAxisFFTInt (P ℓ : ℕ) (θn : ℕ → ℤ × ℤ) {α : Type} (z : α → Fin (2 ^ ℓ) → ℤ × ℤ) :
    α → Fin (2 ^ ℓ) → ℤ × ℤ :=
  fun x => coeffBitRevInt ((List.range ℓ).foldl (fun w s => difLevelInt P ℓ s θn w) (z x))

theorem foldl_difLevel_gridValC (P ℓ : ℕ) (θn : ℕ → ℤ × ℤ) (L : List ℕ)
    (w : Fin (2 ^ ℓ) → ℤ × ℤ) :
    L.foldl (fun v s => difLevel P ℓ s (fun j => gridValC P (θn j)) v)
        (fun k => gridValC P (w k)) =
      fun k => gridValC P (L.foldl (fun v s => difLevelInt P ℓ s θn v) w k) := by
  induction L generalizing w with
  | nil => rfl
  | cons s L ih => simp only [List.foldl_cons, difLevel_gridValC, ih]

theorem lastAxisFFT_gridValC (P ℓ : ℕ) (θn : ℕ → ℤ × ℤ) {α : Type}
    (z : α → Fin (2 ^ ℓ) → ℤ × ℤ) :
    lastAxisFFT P ℓ (fun j => gridValC P (θn j)) (fun x k => gridValC P (z x k)) =
      fun x k => gridValC P (lastAxisFFTInt P ℓ θn z x k) := by
  funext x
  simp only [lastAxisFFT, lastAxisFFTInt, foldl_difLevel_gridValC, coeffBitRev_gridValC]

/-- **Step (i), integer form**: for a record array and table entries on the `P`-grid,
`gridIntC P (lastAxisFFT P ℓ θ̃ z x k) = lastAxisFFTInt P ℓ (gridIntC P ∘ θ̃) (gridIntC P ∘ z) x k`. -/
theorem gridIntC_lastAxisFFT {P ℓ : ℕ} {θt : ℕ → ℂ} {α : Type} {z : RArr α (2 ^ ℓ)}
    (hθ : ∀ j, OnGrid P (θt j)) (hz : ArrOnGrid P z) (x : α) (k : Fin (2 ^ ℓ)) :
    gridIntC P (lastAxisFFT P ℓ θt z x k) =
      lastAxisFFTInt P ℓ (fun j => gridIntC P (θt j)) (fun y i => gridIntC P (z y i)) x k := by
  have e1 : θt = fun j => gridValC P (gridIntC P (θt j)) :=
    funext fun j => (gridValC_gridIntC (hθ j)).symm
  have e2 : z = fun y i => gridValC P (gridIntC P (z y i)) :=
    funext fun y => funext fun i => (gridValC_gridIntC (hz y i)).symm
  conv_lhs => rw [e1, e2, lastAxisFFT_gridValC]
  exact gridIntC_gridValC P _

/-! ## Record-axis rounds: `H_T` on numerators and the round protocol -/

/-- The signed integer sums of `H_T` (componentwise):
`S(x)_k = ∑_{y =_{T^c} x} (-1)^{#{j ∈ T | x_j = y_j = 1}} z(y)_k`; then
`(H_T z)(x)_k = 2^{-|T|} S(x)_k`, i.e. `S(x)_k` is the numerator at precision `P + |T|`. -/
def hTNum {m r : ℕ} (T : Finset (Fin m)) (z : Cube m → Fin r → ℤ × ℤ) (x : Cube m) (k : Fin r) :
    ℤ × ℤ :=
  (∑ y ∈ Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j),
      (-1 : ℤ) ^ (T.filter (fun j => x j = true ∧ y j = true)).card * (z y k).1,
    ∑ y ∈ Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j),
      (-1 : ℤ) ^ (T.filter (fun j => x j = true ∧ y j = true)).card * (z y k).2)

private theorem intCast_mul_gridValC (P : ℕ) (n : ℤ) (c : ℤ × ℤ) :
    (n : ℂ) * gridValC P c = gridValC P (n * c.1, n * c.2) := by
  apply Complex.ext <;> simp [gridValC] <;> ring

private theorem sum_gridValC {ι : Type*} (P : ℕ) (s : Finset ι) (f : ι → ℤ × ℤ) :
    ∑ i ∈ s, gridValC P (f i) = gridValC P (∑ i ∈ s, (f i).1, ∑ i ∈ s, (f i).2) := by
  induction s using Finset.cons_induction with
  | empty => apply Complex.ext <;> simp [gridValC]
  | cons a s ha ih => rw [Finset.sum_cons, ih, gridValC_add', Finset.sum_cons, Finset.sum_cons]

private theorem inv_two_pow_mul_gridValC (P s : ℕ) (c : ℤ × ℤ) :
    ((2 : ℂ) ^ s)⁻¹ * gridValC P c = gridValC (P + s) c := by
  have h2 : ((2 : ℂ) ^ s)⁻¹ = ((gridUnit s : ℝ) : ℂ) := by
    unfold gridUnit; push_cast; rfl
  rw [h2]
  apply Complex.ext <;> simp [gridValC, gridUnit_add'] <;> ring

/-- `H_T` on numerator-valued data: exact, at precision `P + |T|`. -/
theorem hT_gridValC {m r : ℕ} (P : ℕ) (T : Finset (Fin m)) (z : Cube m → Fin r → ℤ × ℤ)
    (x : Cube m) (k : Fin r) :
    hT T (fun y i => gridValC P (z y i)) x k = gridValC (P + T.card) (hTNum T z x k) := by
  have hsign : ∀ n : ℕ, ((-1 : ℂ) ^ n) = (((-1 : ℤ) ^ n : ℤ) : ℂ) := by
    intro n; push_cast; rfl
  simp only [hT, hsign, intCast_mul_gridValC, sum_gridValC, inv_two_pow_mul_gridValC]
  rfl

/-- `Q_P(H_T z)` on numerators: the exact signed sum, then one truncation by `2^{|T|}`. -/
theorem truncC_hT_gridValC {m r : ℕ} (P : ℕ) (T : Finset (Fin m)) (z : Cube m → Fin r → ℤ × ℤ)
    (x : Cube m) (k : Fin r) :
    truncC P (hT T (fun y i => gridValC P (z y i)) x k) =
      gridValC P (tdivShiftC T.card (hTNum T z x k)) := by
  rw [hT_gridValC, truncC_gridValC]

/-- **`Q_P(H_T z)`, integer form**: for `z` on the `P`-grid,
`gridIntC P (Q_P((H_T z)(x)_k)) = tdivShiftC |T| (hTNum T (gridIntC P ∘ z) x k)`. -/
theorem gridIntC_truncC_hT {m r : ℕ} {P : ℕ} (T : Finset (Fin m)) {z : RArr (Cube m) r}
    (hz : ArrOnGrid P z) (x : Cube m) (k : Fin r) :
    gridIntC P (truncC P (hT T z x k)) =
      tdivShiftC T.card (hTNum T (fun y i => gridIntC P (z y i)) x k) := by
  have e : z = fun y i => gridValC P (gridIntC P (z y i)) :=
    funext fun y => funext fun i => (gridValC_gridIntC (hz y i)).symm
  conv_lhs => rw [e, truncC_hT_gridValC]
  exact gridIntC_gridValC P _

/-- One record-axis round `Q_P(D̃ Q_P(H_T z))` (Theorem 6.5 (`thm:direct-fft`), eq. (`eq:round-protocol`)) on numerators. -/
def roundInt {m r : ℕ} (P : ℕ) (T : Finset (Fin m)) (θn : Cube m → ℤ × ℤ)
    (z : Cube m → Fin r → ℤ × ℤ) (x : Cube m) (k : Fin r) : ℤ × ℤ :=
  cmulTruncC P (θn x) (tdivShiftC T.card (hTNum T z x k))

theorem round_gridValC {m r : ℕ} (P : ℕ) (T : Finset (Fin m)) (θn : Cube m → ℤ × ℤ)
    (z : Cube m → Fin r → ℤ × ℤ) :
    truncArr P (diagArr (fun x => gridValC P (θn x))
        (truncArr P (hT T (fun y i => gridValC P (z y i))))) =
      fun x k => gridValC P (roundInt P T θn z x k) := by
  funext x k
  simp only [truncArr, diagArr, truncC_hT_gridValC, truncC_mul_gridValC]
  rfl

/-- **Round protocol, integer form**: for `z` and the phases `θ̃(x)` on the `P`-grid,
`gridIntC P (Q_P(D̃ Q_P(H_T z))(x)_k) = roundInt P T (gridIntC P ∘ θ̃) (gridIntC P ∘ z) x k`. -/
theorem gridIntC_round {m r : ℕ} {P : ℕ} (T : Finset (Fin m)) {θt : Cube m → ℂ}
    {z : RArr (Cube m) r} (hθ : ∀ x, OnGrid P (θt x)) (hz : ArrOnGrid P z) (x : Cube m)
    (k : Fin r) :
    gridIntC P (truncArr P (diagArr θt (truncArr P (hT T z))) x k) =
      roundInt P T (fun y => gridIntC P (θt y)) (fun y i => gridIntC P (z y i)) x k := by
  have e1 : θt = fun y => gridValC P (gridIntC P (θt y)) :=
    funext fun y => (gridValC_gridIntC (hθ y)).symm
  have e2 : z = fun y i => gridValC P (gridIntC P (z y i)) :=
    funext fun y => funext fun i => (gridValC_gridIntC (hz y i)).symm
  conv_lhs => rw [e1, e2, round_gridValC]
  exact gridIntC_gridValC P _

/-! ## Phase-table entries -/

theorem phaseTable_eq_gridValC (P ℓ j : ℕ) : phaseTable P ℓ j = gridValC P (phaseTableNum P ℓ j) :=
  rfl

/-- The concrete phase-table entries are the numerators `phaseTableNum`. -/
theorem gridIntC_phaseTable (P ℓ j : ℕ) : gridIntC P (phaseTable P ℓ j) = phaseTableNum P ℓ j := by
  rw [phaseTable_eq_gridValC, gridIntC_gridValC]

theorem onGrid_phaseTable (P ℓ j : ℕ) : OnGrid P (phaseTable P ℓ j) := by
  rw [phaseTable_eq_gridValC]
  exact onGrid_gridValC P _

/-- **DIF level with the concrete table**: for inputs on the `P`-grid,
`gridIntC P (difLevel P ℓ s (phaseTable P ℓ) w k) = difLevelInt P ℓ s (phaseTableNum P ℓ) …`. -/
theorem gridIntC_difLevel_phaseTable {P ℓ s : ℕ} {w : Fin (2 ^ ℓ) → ℂ}
    (hw : ∀ k, OnGrid P (w k)) (k : Fin (2 ^ ℓ)) :
    gridIntC P (difLevel P ℓ s (phaseTable P ℓ) w k) =
      difLevelInt P ℓ s (phaseTableNum P ℓ) (fun i => gridIntC P (w i)) k := by
  rw [gridIntC_difLevel (fun j => onGrid_phaseTable P ℓ j) hw]
  simp only [gridIntC_phaseTable]

/-- **Step (i) with the concrete table**, integer form. -/
theorem gridIntC_lastAxisFFT_phaseTable {P ℓ : ℕ} {α : Type} {z : RArr α (2 ^ ℓ)}
    (hz : ArrOnGrid P z) (x : α) (k : Fin (2 ^ ℓ)) :
    gridIntC P (lastAxisFFT P ℓ (phaseTable P ℓ) z x k) =
      lastAxisFFTInt P ℓ (phaseTableNum P ℓ) (fun y i => gridIntC P (z y i)) x k := by
  rw [gridIntC_lastAxisFFT (fun j => onGrid_phaseTable P ℓ j) hz]
  simp only [gridIntC_phaseTable]

/-! ## Exact unit and power-of-two factors on numerators -/

/-- Multiplication by the fourth root of unity `i^k` on numerators (exact). -/
def rotC (k : ℕ) (c : ℤ × ℤ) : ℤ × ℤ :=
  match k % 4 with
  | 0 => c
  | 1 => (-c.2, c.1)
  | 2 => (-c.1, -c.2)
  | _ => (c.2, -c.1)

theorem I_pow_mul_gridValC (F k : ℕ) (c : ℤ × ℤ) :
    Complex.I ^ k * gridValC F c = gridValC F (rotC k c) := by
  have hk : Complex.I ^ k = Complex.I ^ (k % 4) := by
    conv_lhs => rw [← Nat.div_add_mod k 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  rw [hk]
  unfold rotC
  rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h0 | h0 | h0 | h0 <;>
    rw [h0] <;> apply Complex.ext <;> simp [gridValC, pow_succ]

/-- `gridIntC` of `i^k z` for `z` on the grid (fourth-root phases are exact). -/
theorem gridIntC_I_pow_mul {F : ℕ} {z : ℂ} (hz : OnGrid F z) (k : ℕ) :
    gridIntC F (Complex.I ^ k * z) = rotC k (gridIntC F z) := by
  conv_lhs => rw [← gridValC_gridIntC hz, I_pow_mul_gridValC, gridIntC_gridValC]

/-- The diagonal `S_U` on numerators: the fourth-root phase `i^{#{j ∈ U | x_j = 1}}`. -/
theorem gridIntC_sDiag {m r F : ℕ} (U : Finset (Fin m)) {z : RArr (Cube m) r}
    (hz : ArrOnGrid F z) (x : Cube m) (k : Fin r) :
    gridIntC F (sDiag U z x k) = rotC (U.filter (fun j => x j = true)).card (gridIntC F (z x k)) := by
  simp only [sDiag, diagArr, sPhase]
  exact gridIntC_I_pow_mul (hz x k) _

/-- The diagonal `CZ` on numerators: the sign `(-1)^n = i^{2n}`, `n = ∑_j x_{c_j} x_{t_j}`. -/
theorem gridIntC_czSign {m r F : ℕ} (pairs : List (Fin m × Fin m)) {z : RArr (Cube m) r}
    (hz : ArrOnGrid F z) (x : Cube m) (k : Fin r) :
    gridIntC F (diagArr (czSign pairs) z x k) =
      rotC (2 * pairs.countP (fun p => x p.1 && x p.2)) (gridIntC F (z x k)) := by
  simp only [diagArr, czSign]
  rw [show (-1 : ℂ) ^ pairs.countP (fun p => x p.1 && x p.2) =
      Complex.I ^ (2 * pairs.countP (fun p => x p.1 && x p.2)) by rw [pow_mul, Complex.I_sq]]
  exact gridIntC_I_pow_mul (hz x k) _

/-- Multiplication by `2^e` of a value on the grid is exact on numerators. -/
theorem gridIntC_two_pow_mul {F : ℕ} {z : ℂ} (hz : OnGrid F z) (e : ℕ) :
    gridIntC F ((2 : ℂ) ^ e * z) = smulC (2 ^ e) (gridIntC F z) := by
  conv_lhs => rw [← gridValC_gridIntC hz, two_pow_mul_gridValC, gridIntC_gridValC]

/-- Multiplication by `1 - i` on numerators: `(re, im) ↦ (re + im, im - re)`
(Section 5.1 (`sec:walsh-select`)). -/
def mulOneSubIC (c : ℤ × ℤ) : ℤ × ℤ := (c.1 + c.2, c.2 - c.1)

theorem one_sub_I_mul_gridValC (F : ℕ) (c : ℤ × ℤ) :
    (1 - Complex.I) * gridValC F c = gridValC F (mulOneSubIC c) := by
  apply Complex.ext <;> simp [gridValC, mulOneSubIC] <;> ring

theorem gridIntC_one_sub_I_mul {F : ℕ} {z : ℂ} (hz : OnGrid F z) :
    gridIntC F ((1 - Complex.I) * z) = mulOneSubIC (gridIntC F z) := by
  conv_lhs => rw [← gridValC_gridIntC hz, one_sub_I_mul_gridValC, gridIntC_gridValC]

end SubNLogN.Math.Walsh.IntForms
