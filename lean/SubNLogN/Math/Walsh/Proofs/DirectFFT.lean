import SubNLogN.Math.Walsh.DirectFFT

/-!
# Theorem 6.5 (direct tensor FFT): error assembly and abstract counts

Paper: Theorem 6.5 (`thm:direct-fft`, Section 6.4 (`sec:direct-fft-thm`)): the round
protocol eq. (`eq:round-protocol`), the error bound eq. (`eq:direct-fft-error`), and the
layer and pass count analysis.

Main results (no proof placeholders; external sub-contracts enter as `…Stmt` hypotheses).
* `direct_fft_of`: `DirectFFTStmt` from the local estimates (`RoundLocalErrorStmt`,
  `LastAxisLevelErrorStmt`), the exact identities (`DifExactStmt`, `TensorFactorStmt`) and
  Lemma 6.3 (`WalshLayoutPermStmt`, `WalshLayoutRoundSliceStmt`, `WalshLayoutExactStmt`,
  `WalshLayoutUnshuffleStmt`). It uses the theorems `positional_perm` (Theorem 5.8, applied to
  `L` and `U` as permutations) and `sliceCall_eq` (slice transport).
* `direct_fft_count_of`: `DirectFFTCountStmt` from `WalshLayoutPermStmt` (bijectivity of `L` and
  `U` is needed to apply the counts of Theorem 5.8, which are stated for permutations), via the
  ideal layer oracle `idealOracle` (which satisfies `LayerSpec` by `rfl`).

Error proof (proof of Theorem 6.5 (`thm:direct-fft`)). Generic propagation (`foldl_error_le`, `foldl_error_lt`):
if the exact steps are `∞`-norm contractions (here: `1`-Lipschitz maps), the computed steps keep
admissible (disk-grid) inputs admissible and are within `ε_i` of the exact step at every
admissible input, then the composite errors add. Instances: the `ℓ` last-axis levels
(`difLevelExact` is a contraction, `lastAxis_error`) and the `ℓ` record-axis rounds (the exact
round `D_ζ H_T` is a contraction, every computed round is `Q_P(D̃ Q_P(H_T z))` by `roundStep_run`,
`rounds_error`); the positional maps are exact (Theorem 5.8) and, like the tensor encoding,
re-index values, so they do not increase the sup norm. Total: `6ℓu + 6ℓu = 12ℓu`, `u = 2^{-P}`.
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

namespace DirectFFTProof

/-! ## Generic error propagation -/

/-- **Error propagation** (proof of Theorem 6.5 (`thm:direct-fft`)). Let `F s` be `1`-Lipschitz exact steps and
`Fh s` computed steps that preserve an admissibility predicate and are within `ε s` of `F s` at
admissible inputs. Then for an admissible computed input `x` and an arbitrary ideal input `y`,
the composites (steps applied in list order) differ by at most `‖x - y‖ + ∑ ε s`. -/
theorem foldl_error_le {X σ : Type*} [SeminormedAddCommGroup X] (Adm : X → Prop)
    (Fh F : σ → X → X) (ε : σ → ℝ) (steps : List σ)
    (hadm : ∀ s ∈ steps, ∀ x, Adm x → Adm (Fh s x))
    (hlip : ∀ s ∈ steps, ∀ x y, ‖F s x - F s y‖ ≤ ‖x - y‖)
    (hloc : ∀ s ∈ steps, ∀ x, Adm x → ‖Fh s x - F s x‖ ≤ ε s)
    (x y : X) (hx : Adm x) :
    ‖steps.foldl (fun w s => Fh s w) x - steps.foldl (fun w s => F s w) y‖ ≤
      ‖x - y‖ + (steps.map ε).sum := by
  induction steps generalizing x y with
  | nil => simp
  | cons s rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have hs : s ∈ s :: rest := by simp
    have h1 := ih (fun t ht => hadm t (by simp [ht]))
      (fun t ht => hlip t (by simp [ht]))
      (fun t ht => hloc t (by simp [ht])) (Fh s x) (F s y) (hadm s hs x hx)
    have h2 := norm_sub_le_norm_sub_add_norm_sub (Fh s x) (F s x) (F s y)
    have h3 := hloc s hs x hx
    have h4 := hlip s hs x y
    linarith

/-- Strict form of `foldl_error_le`: with strict local errors and at least one step, the
composite error is strictly below `‖x - y‖ + ∑ ε s`. -/
theorem foldl_error_lt {X σ : Type*} [SeminormedAddCommGroup X] (Adm : X → Prop)
    (Fh F : σ → X → X) (ε : σ → ℝ) (steps : List σ) (hne : steps ≠ [])
    (hadm : ∀ s ∈ steps, ∀ x, Adm x → Adm (Fh s x))
    (hlip : ∀ s ∈ steps, ∀ x y, ‖F s x - F s y‖ ≤ ‖x - y‖)
    (hloc : ∀ s ∈ steps, ∀ x, Adm x → ‖Fh s x - F s x‖ < ε s)
    (x y : X) (hx : Adm x) :
    ‖steps.foldl (fun w s => Fh s w) x - steps.foldl (fun w s => F s w) y‖ <
      ‖x - y‖ + (steps.map ε).sum := by
  cases steps with
  | nil => exact absurd rfl hne
  | cons s rest =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have hs : s ∈ s :: rest := by simp
    have h1 := foldl_error_le Adm Fh F ε rest (fun t ht => hadm t (by simp [ht]))
      (fun t ht => hlip t (by simp [ht])) (fun t ht x hx => (hloc t (by simp [ht]) x hx).le)
      (Fh s x) (F s y) (hadm s hs x hx)
    have h2 := norm_sub_le_norm_sub_add_norm_sub (Fh s x) (F s x) (F s y)
    have h3 := hloc s hs x hx
    have h4 := hlip s hs x y
    linarith

/-- Computed steps that preserve admissibility give an admissible composite. -/
theorem foldl_adm {X σ : Type*} (Adm : X → Prop) (Fh : σ → X → X) (steps : List σ)
    (hadm : ∀ s ∈ steps, ∀ x, Adm x → Adm (Fh s x)) (x : X) (hx : Adm x) :
    Adm (steps.foldl (fun w s => Fh s w) x) := by
  induction steps generalizing x with
  | nil => simpa using hx
  | cons s rest ih =>
    simp only [List.foldl_cons]
    exact ih (fun t ht => hadm t (by simp [ht])) _ (hadm s (by simp) x hx)

/-- A constant error per step sums to `length · c`. -/
theorem sum_map_const {σ : Type*} (steps : List σ) (c : ℝ) :
    (steps.map (fun _ => c)).sum = steps.length * c := by
  simp [List.map_const', List.sum_replicate, nsmul_eq_mul]

/-! ## Sup-norm facts for record arrays, re-indexings and exact rounds -/

theorem norm_apply_apply_le {α : Type} [Fintype α] {r : ℕ} (z : RArr α r) (x : α) (k : Fin r) :
    ‖z x k‖ ≤ ‖z‖ :=
  (norm_le_pi_norm (z x) k).trans (norm_le_pi_norm z x)

theorem norm_le_of_forall {α : Type} [Fintype α] {r : ℕ} {z : RArr α r} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x k, ‖z x k‖ ≤ B) : ‖z‖ ≤ B :=
  (pi_norm_le_iff_of_nonneg hB).2 fun x => (pi_norm_le_iff_of_nonneg hB).2 fun k => h x k

theorem norm_lt_of_forall {α : Type} [Fintype α] {r : ℕ} {z : RArr α r} {B : ℝ} (hB : 0 < B)
    (h : ∀ x k, ‖z x k‖ < B) : ‖z‖ < B :=
  (pi_norm_lt_iff hB).2 fun x => (pi_norm_lt_iff hB).2 fun k => h x k

theorem posPermArr_sub {m r : ℕ} (π : Fin m → Fin m) (z z' : RArr (Cube m) r) :
    posPermArr π z - posPermArr π z' = posPermArr π (z - z') := rfl

/-- A positional map re-indexes records: it does not increase the sup norm. -/
theorem norm_posPermArr_le {m r : ℕ} (π : Fin m → Fin m) (z : RArr (Cube m) r) :
    ‖posPermArr π z‖ ≤ ‖z‖ :=
  norm_le_of_forall (norm_nonneg _) fun _ k => norm_apply_apply_le z _ k

theorem posPermArr_onDiskGrid {m r P : ℕ} (π : Fin m → Fin m) {z : RArr (Cube m) r}
    (hz : ArrOnDiskGrid P z) : ArrOnDiskGrid P (posPermArr π z) :=
  fun _ k => hz _ k

theorem toTensor_sub {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) (z z' : RArr (Cube (addrBits a)) (2 ^ ℓ)) :
    toTensor a ℓ z - toTensor a ℓ z' = toTensor a ℓ (z - z') := rfl

/-- The tensor reading re-indexes values: it does not increase the sup norm. -/
theorem norm_toTensor_le {D : ℕ} (a : Fin D → ℕ) (ℓ : ℕ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) :
    ‖toTensor a ℓ z‖ ≤ ‖z‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun _ => norm_apply_apply_le z _ _

theorem diagArr_sub {α : Type} {r : ℕ} (f : α → ℂ) (z z' : RArr α r) :
    diagArr f z - diagArr f z' = diagArr f (z - z') := by
  funext x k
  simp only [diagArr, Pi.sub_apply, mul_sub]

/-- A diagonal with entries of modulus at most `1` does not increase the sup norm. -/
theorem norm_diagArr_le {α : Type} [Fintype α] {r : ℕ} (f : α → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (z : RArr α r) : ‖diagArr f z‖ ≤ ‖z‖ :=
  norm_le_of_forall (norm_nonneg _) fun x k => by
    simp only [diagArr, norm_mul]
    calc ‖f x‖ * ‖z x k‖ ≤ 1 * ‖z‖ :=
          mul_le_mul (hf x) (norm_apply_apply_le z x k) (norm_nonneg _) zero_le_one
      _ = ‖z‖ := one_mul _

theorem hT_sub {m r : ℕ} (T : Finset (Fin m)) (z z' : RArr (Cube m) r) :
    hT T z - hT T z' = hT T (z - z') := by
  funext x k
  simp only [hT, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The cube addresses agreeing with `x` off `T` are `2^{|T|}` many. -/
theorem card_agree (m : ℕ) (T : Finset (Fin m)) (x : Cube m) :
    (Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j)).card = 2 ^ T.card := by
  have hS : Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j) =
      Fintype.piFinset (fun j => if j ∈ T then (Finset.univ : Finset Bool) else {x j}) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      split_ifs with hj
      · exact Finset.mem_univ _
      · exact Finset.mem_singleton.2 (h j hj)
    · intro h j hj
      have hj' := h j
      rw [if_neg hj] at hj'
      exact Finset.mem_singleton.1 hj'
  have hc : ∀ j, ((if j ∈ T then (Finset.univ : Finset Bool) else {x j}).card) =
      if j ∈ T then 2 else 1 := by
    intro j; split_ifs <;> simp
  rw [hS, Fintype.card_piFinset]
  simp_rw [hc]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- `H_T` is an `∞`-norm contraction, pointwise form (`2^{-|T|}` times a signed sum of
`2^{|T|}` coefficients). -/
theorem hT_apply_norm_le {m r : ℕ} (T : Finset (Fin m)) (z : RArr (Cube m) r) {B : ℝ}
    (hz : ∀ y k, ‖z y k‖ ≤ B) (x : Cube m) (k : Fin r) : ‖hT T z x k‖ ≤ B := by
  have hsum : ‖∑ y ∈ Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j),
      (-1 : ℂ) ^ (T.filter (fun j => x j = true ∧ y j = true)).card * z y k‖ ≤
        2 ^ T.card * B := by
    calc ‖∑ y ∈ Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j),
          (-1 : ℂ) ^ (T.filter (fun j => x j = true ∧ y j = true)).card * z y k‖
        ≤ ∑ y ∈ Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j),
          ‖(-1 : ℂ) ^ (T.filter (fun j => x j = true ∧ y j = true)).card * z y k‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _y ∈ Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j), B := by
          apply Finset.sum_le_sum
          intro _y _
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact hz _ _
      _ = 2 ^ T.card * B := by
          rw [Finset.sum_const, card_agree, nsmul_eq_mul]; push_cast; ring
  have h2 : (0 : ℝ) < 2 ^ T.card := by positivity
  calc ‖hT T z x k‖
      = ((2 : ℝ) ^ T.card)⁻¹ * ‖∑ y ∈ Finset.univ.filter
          (fun y : Cube m => ∀ j, j ∉ T → y j = x j),
          (-1 : ℂ) ^ (T.filter (fun j => x j = true ∧ y j = true)).card * z y k‖ := by
        simp only [hT, norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
    _ ≤ ((2 : ℝ) ^ T.card)⁻¹ * (2 ^ T.card * B) := by gcongr
    _ = B := by field_simp

/-- `H_T` is an `∞`-norm contraction. -/
theorem norm_hT_le {m r : ℕ} (T : Finset (Fin m)) (z : RArr (Cube m) r) : ‖hT T z‖ ≤ ‖z‖ :=
  norm_le_of_forall (norm_nonneg _) fun x k =>
    hT_apply_norm_le T z (fun y k' => norm_apply_apply_le z y k') x k

/-- Exact phases have modulus `1`. -/
theorem norm_theta (r j : ℕ) : ‖theta r j‖ = 1 := IntMul.norm_stdChar _

/-- The combined twiddle index is reduced mod `2^ℓ`. -/
theorem twJ_lt {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) (x : Cube (addrBits a)) :
    twJ ℓ K a v x < 2 ^ ℓ :=
  Nat.mod_lt _ (Nat.two_pow_pos ℓ)

/-- The exact round `D_ζ H_T` is `1`-Lipschitz in the sup norm (proof of Theorem 6.5 (`thm:direct-fft`)). -/
theorem exactRound_lip {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) {r : ℕ}
    (z z' : RArr (Cube (addrBits a)) r) :
    ‖exactRound ℓ K a v z - exactRound ℓ K a v z'‖ ≤ ‖z - z'‖ := by
  unfold exactRound
  rw [diagArr_sub, hT_sub]
  exact (norm_diagArr_le _ (fun x => (norm_theta _ _).le) _).trans (norm_hT_le _ _)

/-! ## The last axis -/

theorem getCoeff_sub {n : ℕ} (w w' : Fin n → ℂ) (k : ℕ) :
    getCoeff (w - w') k = getCoeff w k - getCoeff w' k := by
  unfold getCoeff; split_ifs <;> simp

theorem norm_getCoeff_le {n : ℕ} (w : Fin n → ℂ) (k : ℕ) : ‖getCoeff w k‖ ≤ ‖w‖ := by
  unfold getCoeff; split_ifs with h
  · exact norm_le_pi_norm w _
  · simp

theorem difLevelExact_sub (ℓ s : ℕ) (w w' : Fin (2 ^ ℓ) → ℂ) :
    difLevelExact ℓ s w - difLevelExact ℓ s w' = difLevelExact ℓ s (w - w') := by
  funext k
  simp only [difLevelExact, Pi.sub_apply, getCoeff_sub]
  split_ifs <;> ring

/-- An exact DIF level is an `∞`-norm contraction (half-sums, and half-differences times a phase
of modulus `1`). -/
theorem norm_difLevelExact_le (ℓ s : ℕ) (w : Fin (2 ^ ℓ) → ℂ) :
    ‖difLevelExact ℓ s w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun k => ?_
  have hn : ∀ a b : ℂ, ‖a‖ ≤ ‖w‖ → ‖b‖ ≤ ‖w‖ →
      ‖(a + b) / 2‖ ≤ ‖w‖ ∧ ‖(a - b) / 2‖ ≤ ‖w‖ := by
    intro a b ha hb
    have h1 := norm_add_le a b
    have h2 := norm_sub_le a b
    rw [norm_div, norm_div, Complex.norm_ofNat]
    constructor <;> linarith
  unfold difLevelExact
  split_ifs
  · exact (hn _ _ (norm_getCoeff_le w _) (norm_getCoeff_le w _)).1
  · rw [norm_mul, norm_theta, one_mul]
    exact (hn _ _ (norm_getCoeff_le w _) (norm_getCoeff_le w _)).2

theorem difLevelExact_lip (ℓ s : ℕ) (w w' : Fin (2 ^ ℓ) → ℂ) :
    ‖difLevelExact ℓ s w - difLevelExact ℓ s w'‖ ≤ ‖w - w'‖ := by
  rw [difLevelExact_sub]; exact norm_difLevelExact_le ℓ s _

/-- **Step (i), error** (proof of Theorem 6.5 (`thm:direct-fft`)): given the local level estimate, the rounded
last-axis FFT of a disk array on the `P`-grid is a disk array on the `P`-grid within `6ℓ · 2^{-P}`
of the exact last-axis transform (`ℓ` levels; bit reversal re-indexes). -/
theorem lastAxis_error (hLA : LastAxisLevelErrorStmt) {P ℓ : ℕ} {θt : ℕ → ℂ}
    (htab : PhaseTableSpec P ℓ θt) (hℓ : 1 ≤ ℓ) {α : Type} [Fintype α] (z : RArr α (2 ^ ℓ))
    (hz : ArrOnDiskGrid P z) :
    ArrOnDiskGrid P (lastAxisFFT P ℓ θt z) ∧
      ‖lastAxisFFT P ℓ θt z - lastAxisExact ℓ z‖ < 6 * (ℓ : ℝ) * gridUnit P := by
  have hu := gridUnit_pos P
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hadm : ∀ s ∈ List.range ℓ, ∀ w : Fin (2 ^ ℓ) → ℂ, (∀ k, OnDiskGrid P (w k)) →
      (∀ k, OnDiskGrid P (difLevel P ℓ s θt w k)) :=
    fun s hs w hw => (hLA P ℓ s θt w (List.mem_range.1 hs) htab hw).1
  have hloc : ∀ s ∈ List.range ℓ, ∀ w : Fin (2 ^ ℓ) → ℂ, (∀ k, OnDiskGrid P (w k)) →
      ‖difLevel P ℓ s θt w - difLevelExact ℓ s w‖ < 6 * gridUnit P :=
    fun s hs w hw => (hLA P ℓ s θt w (List.mem_range.1 hs) htab hw).2
  have hne : List.range ℓ ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  have hA : ∀ x, ∀ k,
      OnDiskGrid P (((List.range ℓ).foldl (fun w s => difLevel P ℓ s θt w) (z x)) k) :=
    fun x => foldl_adm (fun w : Fin (2 ^ ℓ) → ℂ => ∀ k, OnDiskGrid P (w k))
      (fun s w => difLevel P ℓ s θt w) (List.range ℓ) hadm (z x) (hz x)
  have hE : ∀ x, ‖(List.range ℓ).foldl (fun w s => difLevel P ℓ s θt w) (z x) -
      (List.range ℓ).foldl (fun w s => difLevelExact ℓ s w) (z x)‖ < 6 * ℓ * gridUnit P := by
    intro x
    have h : ‖(List.range ℓ).foldl (fun w s => difLevel P ℓ s θt w) (z x) -
        (List.range ℓ).foldl (fun w s => difLevelExact ℓ s w) (z x)‖ <
        ‖z x - z x‖ + ((List.range ℓ).map (fun _ => 6 * gridUnit P)).sum :=
      foldl_error_lt (fun w : Fin (2 ^ ℓ) → ℂ => ∀ k, OnDiskGrid P (w k))
        (fun s w => difLevel P ℓ s θt w) (fun s w => difLevelExact ℓ s w)
        (fun _ => 6 * gridUnit P) (List.range ℓ) hne hadm
        (fun s _ w w' => difLevelExact_lip ℓ s w w') hloc (z x) (z x) (hz x)
    rw [sub_self, norm_zero, zero_add, sum_map_const, List.length_range] at h
    linarith
  refine ⟨fun x k => ?_, ?_⟩
  · show OnDiskGrid P (getCoeff _ _)
    unfold getCoeff; split_ifs
    · exact hA x _
    · exact ⟨onGrid_zero P, by simp⟩
  · refine norm_lt_of_forall (mul_pos (mul_pos (by norm_num) hℓ') hu) fun x k => ?_
    show ‖getCoeff _ (bitRevNat ℓ k) - getCoeff _ (bitRevNat ℓ k)‖ < _
    rw [← getCoeff_sub]
    exact lt_of_le_of_lt (norm_getCoeff_le _ _) (hE x)

/-! ## Walsh programs -/

theorem run_append (layer : LayerOracle) (r : ℕ) {m : ℕ} (l₁ l₂ : List (WStep m))
    (z : RArr (Cube m) r) :
    runProg layer r (l₁ ++ l₂) z = runProg layer r l₂ (runProg layer r l₁ z) := by
  simp only [runProg, List.foldl_append]

theorem run_flatMap {ι : Type} (layer : LayerOracle) (r : ℕ) {m : ℕ} (l : List ι)
    (f : ι → List (WStep m)) (z : RArr (Cube m) r) :
    runProg layer r (l.flatMap f) z = l.foldl (fun w i => runProg layer r (f i) w) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i rest ih => rw [List.flatMap_cons, run_append, List.foldl_cons, ih]

theorem calls_append {m : ℕ} (l₁ l₂ : List (WStep m)) :
    progLayerCalls (l₁ ++ l₂) = progLayerCalls l₁ + progLayerCalls l₂ := by
  simp only [progLayerCalls, List.map_append, List.sum_append]

theorem passes_append {m : ℕ} (l₁ l₂ : List (WStep m)) :
    progPasses (l₁ ++ l₂) = progPasses l₁ + progPasses l₂ := by
  simp only [progPasses, List.map_append, List.sum_append]

theorem calls_flatMap {m : ℕ} {ι : Type} (l : List ι) (f : ι → List (WStep m)) :
    progLayerCalls (l.flatMap f) = (l.map fun i => progLayerCalls (f i)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, calls_append, ih, List.map_cons, List.sum_cons]

theorem passes_flatMap {m : ℕ} {ι : Type} (l : List ι) (f : ι → List (WStep m)) :
    progPasses (l.flatMap f) = (l.map fun i => progPasses (f i)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, passes_append, ih, List.map_cons, List.sum_cons]

/-! ## The record-axis rounds -/

/-- **Round protocol, butterfly part** (Theorem 6.5 (`thm:direct-fft`), eq. (`eq:round-protocol`)): on a disk array on the `P`-grid,
the butterfly step of round `v` returns exactly `Q_P(H_T z)`, `T = roundSet v`: a chunk round is a
layer call on the slice of Lemma 6.3 (`WalshLayoutRoundSliceStmt`, `sliceCall_eq`, `LayerSpec`
from `WalshLayerOK`); a prefix round is exact butterflies plus one `Q_P` by definition. -/
theorem roundStep_run (hslice : WalshLayoutRoundSliceStmt) {layer : LayerOracle}
    {P D ℓ K : ℕ} {a : Fin D → ℕ} (hℓ : 2 ≤ ℓ) (hK1 : 1 ≤ K) (hK2 : K ≤ ℓ - 1)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (hok : WalshLayerOK layer P D ℓ K a) (v : ℕ)
    (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) (hz : ArrOnDiskGrid P z) :
    (roundStep P D ℓ K a v).run layer (2 ^ ℓ) z = truncArr P (hT (roundSet ℓ K a v) z) := by
  unfold roundStep
  split_ifs with h
  · obtain ⟨-, hb, hv⟩ := h
    obtain ⟨hle, hset⟩ := hslice ℓ K a hK1 hK2 hℓ ha v hb hv
    have hm : prefixLen ℓ K a + (ℓ - 2 - v) / K * D * K + D * K +
        (addrBits a - (prefixLen ℓ K a + (ℓ - 2 - v) / K * D * K) - D * K) = addrBits a := by
      omega
    rw [hset]
    exact sliceCall_eq layer P (2 ^ ℓ) K _ D _ (addrBits a) _ hm (hok.1 _ _ _ hm) z hz
  · rfl

/-- One computed round `v`: the three steps of `roundsProg` for slot `v`. -/
noncomputable def roundRun (layer : LayerOracle) (P D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ)
    (v : ℕ) (w : RArr (Cube (addrBits a)) (2 ^ ℓ)) : RArr (Cube (addrBits a)) (2 ^ ℓ) :=
  runProg layer (2 ^ ℓ)
    [roundStep P D ℓ K a v, WStep.diag (fun x => θt (2 * twJ ℓ K a v x)), WStep.trunc P] w

theorem roundsProg_run (layer : LayerOracle) (P D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ)
    (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) :
    runProg layer (2 ^ ℓ) (roundsProg P D ℓ K a θt) z =
      (List.range ℓ).reverse.foldl (fun w v => roundRun layer P D ℓ K a θt v w) z :=
  run_flatMap layer (2 ^ ℓ) _ _ z

/-- **Step (iii), error** (proof of Theorem 6.5 (`thm:direct-fft`)): on a disk array on the `P`-grid the rounds
return a disk array on the `P`-grid, within `‖z - y‖ + 6ℓ · 2^{-P}` of the exact rounds applied to
an arbitrary `y` (local round estimate + contraction of the exact rounds). -/
theorem rounds_error (hR : RoundLocalErrorStmt) (hslice : WalshLayoutRoundSliceStmt)
    {layer : LayerOracle} {P D ℓ K : ℕ} {a : Fin D → ℕ} {θt : ℕ → ℂ}
    (hℓ : 2 ≤ ℓ) (hK1 : 1 ≤ K) (hK2 : K ≤ ℓ - 1) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ)
    (htab : PhaseTableSpec P ℓ θt) (hok : WalshLayerOK layer P D ℓ K a)
    (z y : RArr (Cube (addrBits a)) (2 ^ ℓ)) (hz : ArrOnDiskGrid P z) :
    ArrOnDiskGrid P (runProg layer (2 ^ ℓ) (roundsProg P D ℓ K a θt) z) ∧
      ‖runProg layer (2 ^ ℓ) (roundsProg P D ℓ K a θt) z - exactRounds ℓ K a y‖ <
        ‖z - y‖ + 6 * (ℓ : ℝ) * gridUnit P := by
  have hθ : ∀ v x, ‖θt (2 * twJ ℓ K a v x)‖ ≤ 1 ∧
      ‖θt (2 * twJ ℓ K a v x) - theta (2 ^ ℓ) (2 * twJ ℓ K a v x)‖ < 2 * gridUnit P := by
    intro v x
    have h := htab (2 * twJ ℓ K a v x) (by have := twJ_lt ℓ K a v x; omega)
    exact ⟨h.2.1, h.2.2⟩
  have hloc : ∀ v, ∀ w, ArrOnDiskGrid P w → ArrOnDiskGrid P (roundRun layer P D ℓ K a θt v w) ∧
      ‖roundRun layer P D ℓ K a θt v w - exactRound ℓ K a v w‖ < 6 * gridUnit P := by
    intro v w hw
    have hrun : roundRun layer P D ℓ K a θt v w = truncArr P (diagArr
        (fun x => θt (2 * twJ ℓ K a v x)) (truncArr P (hT (roundSet ℓ K a v) w))) := by
      show truncArr P (diagArr _ ((roundStep P D ℓ K a v).run layer (2 ^ ℓ) w)) = _
      rw [roundStep_run hslice hℓ hK1 hK2 ha hok v w hw]
    rw [hrun]
    exact hR P (roundSet ℓ K a v) (fun x => θt (2 * twJ ℓ K a v x))
      (fun x => theta (2 ^ ℓ) (2 * twJ ℓ K a v x)) w hw (fun x => (hθ v x).1)
      (fun x => norm_theta _ _) (fun x => (hθ v x).2)
  have hne : (List.range ℓ).reverse ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  rw [roundsProg_run]
  refine ⟨foldl_adm (ArrOnDiskGrid P) (roundRun layer P D ℓ K a θt) _
    (fun v _ w hw => (hloc v w hw).1) z hz, ?_⟩
  have h : ‖(List.range ℓ).reverse.foldl (fun w v => roundRun layer P D ℓ K a θt v w) z -
      (List.range ℓ).reverse.foldl (fun w v => exactRound ℓ K a v w) y‖ <
      ‖z - y‖ + ((List.range ℓ).reverse.map (fun _ => 6 * gridUnit P)).sum :=
    foldl_error_lt (ArrOnDiskGrid P) (roundRun layer P D ℓ K a θt)
      (fun v w => exactRound ℓ K a v w) (fun _ => 6 * gridUnit P) _ hne
      (fun v _ w hw => (hloc v w hw).1) (fun v _ w w' => exactRound_lip ℓ K a v w w')
      (fun v _ w hw => (hloc v w hw).2) z y hz
  rw [sum_map_const, List.length_reverse, List.length_range] at h
  unfold exactRounds
  linarith

/-- `U` is bijective, being a two-sided inverse of `L ∘ B` (`WalshLayoutPermStmt`). -/
theorem layoutU_bijective {D : ℕ} {ℓ K : ℕ} {a : Fin D → ℕ}
    (hUL : ∀ p, layoutU ℓ K a (layoutL ℓ K a (bitRevB a p)) = p)
    (hLU : ∀ p, layoutL ℓ K a (bitRevB a (layoutU ℓ K a p)) = p) :
    Function.Bijective (layoutU ℓ K a) :=
  ⟨Function.LeftInverse.injective (g := fun p => layoutL ℓ K a (bitRevB a p)) hLU,
    Function.RightInverse.surjective (g := fun p => layoutL ℓ K a (bitRevB a p)) hUL⟩

end DirectFFTProof

open DirectFFTProof in
/-- **Theorem 6.5, value-level part** (`thm:direct-fft`), from the sub-contract statements: the
local estimates (round protocol `RoundLocalErrorStmt`, last-axis level `LastAxisLevelErrorStmt`),
the exact identities (DIF `DifExactStmt`, tensor factorization `TensorFactorStmt`) and Lemma 6.3
(`WalshLayoutPermStmt`, `WalshLayoutRoundSliceStmt`, `WalshLayoutExactStmt`,
`WalshLayoutUnshuffleStmt`); Theorem 5.8 (`positional_perm`) and `sliceCall_eq` are used as
theorems. Exact counterpart: `F_t = toTensor ∘ U ∘ exactRounds ∘ L ∘ lastAxisExact ∘ ofTensor`;
error `< 6ℓu` (last axis) `+ 6ℓu` (rounds). -/
theorem direct_fft_of (hR : RoundLocalErrorStmt) (hLA : LastAxisLevelErrorStmt)
    (hdif : DifExactStmt) (hfac : TensorFactorStmt) (hperm : WalshLayoutPermStmt)
    (hslice : WalshLayoutRoundSliceStmt) (hexact : WalshLayoutExactStmt)
    (hunsh : WalshLayoutUnshuffleStmt) : DirectFFTStmt := by
  intro layer P D ℓ K a θt hD hℓ hK1 hK2 ha htab hok U hU
  -- the input as a record array, and step (i)
  have hz0 : ArrOnDiskGrid P (ofTensor a ℓ U) := fun x k => hU _
  obtain ⟨hz1, he1⟩ := lastAxis_error hLA htab (by omega) (ofTensor a ℓ U) hz0
  -- the positional maps `L`, `U` are exact on disk arrays (Theorem 5.8)
  obtain ⟨hLbij, -, hUL, hLU⟩ := hperm ℓ K a hK1 hK2 hℓ ha
  have hUbij := layoutU_bijective hUL hLU
  have hposL := (positional_perm layer P (D + 1) K hK1 (by omega) hok.2
    (Equiv.ofBijective _ hLbij)).1
  have hposU := (positional_perm layer P (D + 1) K hK1 (by omega) hok.2
    (Equiv.ofBijective _ hUbij)).1
  simp only [Equiv.coe_ofBijective] at hposL hposU
  -- step (iii)
  obtain ⟨hz3, he3⟩ := rounds_error hR hslice hℓ hK1 hK2 ha htab hok
    (posPermArr (layoutL ℓ K a) (lastAxisFFT P ℓ θt (ofTensor a ℓ U)))
    (posPermArr (layoutL ℓ K a) (lastAxisExact ℓ (ofTensor a ℓ U)))
    (posPermArr_onDiskGrid _ hz1)
  -- the computed output
  have hout : directFFT layer P D ℓ K a θt (ofTensor a ℓ U) =
      posPermArr (layoutU ℓ K a) (runProg layer (2 ^ ℓ) (roundsProg P D ℓ K a θt)
        (posPermArr (layoutL ℓ K a) (lastAxisFFT P ℓ θt (ofTensor a ℓ U)))) := by
    unfold directFFT recordAxesProg
    rw [run_append, run_append, hposL _ hz1, hposU _ hz3]
  -- the exact output
  have hex : dftTensor (fftShape a ℓ) U = toTensor a ℓ (posPermArr (layoutU ℓ K a)
      (exactRounds ℓ K a (posPermArr (layoutL ℓ K a) (lastAxisExact ℓ (ofTensor a ℓ U))))) := by
    rw [← hfac a ℓ U, hdif ℓ (ofTensor a ℓ U), hexact ℓ K a hK1 hK2 hℓ ha,
      hunsh ℓ K a hK1 hK2 hℓ ha]
  rw [hout, hex]
  refine ⟨fun u => hz3 _ _, ?_⟩
  rw [toTensor_sub, posPermArr_sub]
  have h1 : ‖posPermArr (layoutL ℓ K a) (lastAxisFFT P ℓ θt (ofTensor a ℓ U)) -
      posPermArr (layoutL ℓ K a) (lastAxisExact ℓ (ofTensor a ℓ U))‖ ≤
      ‖lastAxisFFT P ℓ θt (ofTensor a ℓ U) - lastAxisExact ℓ (ofTensor a ℓ U)‖ := by
    rw [posPermArr_sub]; exact norm_posPermArr_le _ _
  have h2 := (norm_toTensor_le a ℓ _).trans (norm_posPermArr_le (layoutU ℓ K a)
    (runProg layer (2 ^ ℓ) (roundsProg P D ℓ K a θt)
        (posPermArr (layoutL ℓ K a) (lastAxisFFT P ℓ θt (ofTensor a ℓ U))) -
      exactRounds ℓ K a (posPermArr (layoutL ℓ K a) (lastAxisExact ℓ (ofTensor a ℓ U)))))
  linarith

/-! ## Abstract counts (proof of Theorem 6.5 (`thm:direct-fft`)) -/

namespace DirectFFTProof

/-- The ideal layer oracle: every call returns exactly `Q_P(H z)`. -/
noncomputable def idealOracle : LayerOracle := fun P _ _ _ _ _ ρ z => truncArr P (layerH ρ z)

theorem idealOracle_spec (P r A K D S : ℕ) (ρ : Fin K) :
    LayerSpec P r A K D S ρ (idealOracle P r A K D S ρ) := fun _ _ => rfl

/-- The counts of Theorem 5.8 for a bijective positional map (via the ideal oracle; the counts do
not depend on the oracle). -/
theorem posPermProg_counts {m₀ : ℕ} (P d K : ℕ) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (π : Fin m₀ → Fin m₀) (hπ : Function.Bijective π) :
    progLayerCalls (posPermProg (m₀ := m₀) P d K π) ≤ 36 * nSlice m₀ K d ∧
      progPasses (posPermProg (m₀ := m₀) P d K π) ≤ 72 * nSlice m₀ K d + 6 * K := by
  have h := positional_perm (r := 1) idealOracle P d K hK hd
    (fun _ _ _ _ _ _ _ => idealOracle_spec _ _ _ _ _ _ _) (Equiv.ofBijective π hπ)
  simp only [Equiv.coe_ofBijective] at h
  exact h.2

/-- A round touches at most one position per record axis. -/
theorem card_roundSet_le {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) :
    (roundSet ℓ K a v).card ≤ D := by
  have hsub : roundSet ℓ K a v ⊆ (Finset.univ : Finset (Fin D)).biUnion
      (fun i => Finset.univ.filter
        (fun p : Fin (addrBits a) => newPos ℓ K a (i, v) = (p : ℕ))) := by
    intro p hp
    simp only [roundSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨i, -, hi⟩ := hp
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨i, hi⟩
  calc (roundSet ℓ K a v).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin D, (Finset.univ.filter
          (fun p : Fin (addrBits a) => newPos ℓ K a (i, v) = (p : ℕ))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin D, 1 := Finset.sum_le_sum fun i _ => Finset.card_le_one.2 fun p hp q hq => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        exact Fin.ext (hp.symm.trans hq)
    _ = D := by simp

/-- At most `b₀ + 1 ≤ K` of the slots `v < ℓ` are prefix rounds (`v < b₀` or `v = ℓ - 1`). -/
theorem card_prefixRounds_le (ℓ K : ℕ) (hK : 1 ≤ K) :
    ((Finset.range ℓ).filter (fun v => ¬ (0 < K ∧ layoutB0 ℓ K ≤ v ∧ v + 2 ≤ ℓ))).card ≤ K := by
  have hb : layoutB0 ℓ K < K := Nat.mod_lt _ (by omega)
  have hsub : (Finset.range ℓ).filter (fun v => ¬ (0 < K ∧ layoutB0 ℓ K ≤ v ∧ v + 2 ≤ ℓ)) ⊆
      insert (ℓ - 1) (Finset.range (layoutB0 ℓ K)) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    simp only [Finset.mem_insert, Finset.mem_range]
    omega
  calc _ ≤ (insert (ℓ - 1) (Finset.range (layoutB0 ℓ K))).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (layoutB0 ℓ K)).card + 1 := Finset.card_insert_le _ _
    _ = layoutB0 ℓ K + 1 := by rw [Finset.card_range]
    _ ≤ K := by omega

theorem list_sum_range (g : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The rounds make at most `ℓ` completed layer calls (one per chunk round). -/
theorem roundsProg_calls_le (P D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ) :
    progLayerCalls (roundsProg P D ℓ K a θt) ≤ ℓ := by
  unfold roundsProg
  rw [calls_flatMap]
  have h := List.sum_le_card_nsmul ((List.range ℓ).reverse.map fun v =>
      progLayerCalls [roundStep P D ℓ K a v, WStep.diag (fun x => θt (2 * twJ ℓ K a v x)),
        WStep.trunc P]) 1 (by
    intro c hc
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hc
    simp only [progLayerCalls, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    unfold roundStep
    split_ifs <;> simp [WStep.layerCalls])
  simpa using h

/-- The rounds use at most `K(D+1) + 2ℓ` passes: two per round (twiddle, truncation) and
`|T| + 1 ≤ D + 1` per prefix round. -/
theorem roundsProg_passes_le (P D ℓ K : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ) (hK : 1 ≤ K) :
    progPasses (roundsProg P D ℓ K a θt) ≤ K * (D + 1) + 2 * ℓ := by
  unfold roundsProg
  rw [passes_flatMap, List.map_reverse, List.sum_reverse, list_sum_range]
  have hblock : ∀ v, progPasses [roundStep P D ℓ K a v,
      WStep.diag (fun x => θt (2 * twJ ℓ K a v x)), WStep.trunc P] ≤
      2 + (if ¬ (0 < K ∧ layoutB0 ℓ K ≤ v ∧ v + 2 ≤ ℓ) then D + 1 else 0) := by
    intro v
    simp only [progPasses, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases h : 0 < K ∧ layoutB0 ℓ K ≤ v ∧ v + 2 ≤ ℓ
    · rw [if_neg (not_not.2 h)]
      unfold roundStep
      rw [dif_pos h]
      simp [WStep.passes]
    · rw [if_pos h]
      unfold roundStep
      rw [dif_neg h]
      simp only [WStep.passes]
      have := card_roundSet_le ℓ K a v
      omega
  refine le_trans (Finset.sum_le_sum fun v _ => hblock v) ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    Finset.card_range, smul_eq_mul, smul_eq_mul]
  have h1 := card_prefixRounds_le ℓ K hK
  have h2 := Nat.mul_le_mul_right (D + 1) h1
  omega

end DirectFFTProof

open DirectFFTProof in
/-- **Theorem 6.5, abstract counts** (proof of Theorem 6.5 (`thm:direct-fft`)), from Lemma 6.3's positional-map
statement (`WalshLayoutPermStmt`: `L` and `U` are permutations, so Theorem 5.8's counts apply):
at most `ℓ + 72 N_slice` layer calls and `K(D+1) + 2ℓ + 144 N_slice + 12K` passes. -/
theorem direct_fft_count_of (hperm : WalshLayoutPermStmt) : DirectFFTCountStmt := by
  intro P D ℓ K a θt hD hℓ hK1 hK2 ha
  obtain ⟨hLbij, -, hUL, hLU⟩ := hperm ℓ K a hK1 hK2 hℓ ha
  obtain ⟨hL1, hL2⟩ := posPermProg_counts P (D + 1) K hK1 (by omega) _ hLbij
  obtain ⟨hU1, hU2⟩ := posPermProg_counts P (D + 1) K hK1 (by omega) _
    (layoutU_bijective hUL hLU)
  have hr1 := roundsProg_calls_le P D ℓ K a θt
  have hr2 := roundsProg_passes_le P D ℓ K a θt hK1
  unfold recordAxesProg
  rw [calls_append, calls_append, passes_append, passes_append]
  constructor <;> omega

end SubNLogN.Math.Walsh
