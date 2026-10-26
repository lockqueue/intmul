import SubNLogN.Math.Networks.AppCShear

/-!
# Proofs of the Appendix A algebra contracts: Lemma A.6 shear and Proposition A.7 / Lemma A.8 recurrences

Proofs of `ShearFactorizationStmt`, `LinDLowerTriStreamingStmt`, `RatModMatrixMulStmt`,
`InterchangeRecurrenceStmt`, `PiecesCostStmt` (statements in `AppCShear.lean`; Appendix A,
`lem:transfer-shear`, `prop:transfer11`, `lem:transfer12`; `AppC` in filenames is a historical prefix retained for stability).

## Plan
* **Shear (Lemma A.6 (`lem:transfer-shear`)).** The pivot triple at `(i, j)` is `(h, d) ↦ (h + d_j e_i, d)` (reproved locally as
  `pivotTriple_eq'`). By induction on the pivot list, if the rows are distinct, the composite of the
  triples is `(h, d) ↦ (h + Π d, d)` with `Π` the 0/1 indicator matrix of the list (the new row `i`
  of the head pivot is absent from the tail, so the tail's contribution at row `i` is `0`). Then
  `E₁ (E₁' h + Π E₂ d) = h + E₁ Π E₂ d` and `E₂' E₂ d = d` (`E₂' E₂ = 1` from `E₂ E₂' = 1` by
  Dedekind-finiteness of square matrices over a commutative ring, `mul_eq_one_comm`). The
  distinct-columns hypothesis `(piv.map Prod.snd).Nodup` of the statement is not needed (unused).
* **Streaming lower-triangular maps.** Invariant for a strictly decreasing list `L` of indices and a
  state `y` whose coordinates `j ≤ i` (`i ∈ L`) are still original: the fold sets exactly the
  coordinates in `L` to `(E x)_j`. The update at `i` reads only `j ≤ i` (entries `j > i` are `0`).
* **`ratMod` multiplicative.** For `q`-integral `r`, `den r` is a unit mod `q^b`; if `r d = n`
  with `d` invertible mod `q^b` (inverse `iv`) then `ratMod r = n · iv` (cross-multiplication in
  `ℤ`, then cast). This gives additivity and multiplicativity on `q`-integral rationals, which are
  closed under `+, ·` (`Rat.add_den_dvd`, `Rat.mul_den_dvd`, `q` prime); sums by induction.
* **Recurrence (Proposition A.7 (`prop:transfer11`)).** `F k ≤ c Σ_{j ≤ k} a^j`; with `ρ = M^τ > 1`, `r = a/ρ ∈ [0,1)`:
  `a^j = r^j ρ^j ≤ r^j ρ^k`, so `Σ_{j≤k} a^j ≤ ρ^k/(1-r)`; and `M^{kτ} = ρ^k`. `C = c/(1-r)`
  (no case split on `a ≤ 1` needed).
* **Pieces (Lemma A.8 (`lem:transfer12`)).** Digits are `≤ m - 1`; `Σ_j a_j ρ^j ≤ (m-1) Σ_{j<L} ρ^j ≤ (m-1) ρ^L/(ρ-1)`,
  `L` = number of digits, and `ρ^L = (m^L)^τ ≤ (m e)^τ = ρ e^τ` (`Nat.base_pow_length_digits_le`).
  `C = (m-1) ρ/(ρ-1)`.
-/

namespace SubNLogN.Math.Networks

open scoped Matrix

/-! ## Lemma A.6 (`lem:transfer-shear`): the shear factorization -/

/-- Local copy of the pivot-triple identity: the triple at `(i, j)` adds `d_j` to `h_i`. -/
private theorem pivotTriple_eq' {m Q : ℕ} (i j : Fin m) (h d : Fin m → ZMod Q) :
    pivotTriple i j (h, d) = (Function.update h i (h i + d j), d) := by
  simp only [pivotTriple, Function.update_self, Function.update_idem, add_sub_cancel_right,
    Function.update_eq_self, Prod.mk.injEq, and_true]
  rw [add_comm]

/-- The pivot triples of a list with pairwise distinct rows compose to `(h, d) ↦ (h + Π d, d)`,
`Π` the 0/1 indicator matrix of the list. -/
private theorem foldr_pivotTriple {m Q : ℕ} (piv : List (Fin m × Fin m))
    (hnd : (piv.map Prod.fst).Nodup) (h d : Fin m → ZMod Q) :
    (piv.foldr (fun p f => pivotTriple p.1 p.2 ∘ f) id) (h, d) =
      (h + (Matrix.of fun i j => if (i, j) ∈ piv then (1 : ZMod Q) else 0) *ᵥ d, d) := by
  induction piv generalizing h with
  | nil =>
    rw [List.foldr_nil, id_eq]
    refine Prod.ext ?_ rfl
    funext k
    simp [Matrix.mulVec, dotProduct]
  | cons p rest ih =>
    obtain ⟨a, c⟩ := p
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hp, hnd'⟩ := hnd
    rw [List.foldr_cons, Function.comp_apply, ih hnd' h, pivotTriple_eq']
    refine Prod.ext ?_ rfl
    funext k
    dsimp only
    by_cases hk : k = a
    · subst hk
      have h0 : ∀ l, (k, l) ∉ rest := fun l hl => hp (List.mem_map.mpr ⟨(k, l), hl, rfl⟩)
      rw [Function.update_self]
      simp [Matrix.mulVec, dotProduct, h0]
    · rw [Function.update_of_ne hk]
      simp [Matrix.mulVec, dotProduct, hk]

theorem shearFactorization_holds : ShearFactorizationStmt := by
  intro m Q A E₁ E₁' E₂ E₂' Pm h1 h2 hA piv hnd1 _hnd2 hPm
  have hPm' : Pm = Matrix.of fun i j => if (i, j) ∈ piv then (1 : ZMod Q) else 0 := by
    ext i j
    rw [hPm i j, Matrix.of_apply]
  have h2' : E₂' * E₂ = 1 := mul_eq_one_comm.mp h2
  funext x
  obtain ⟨h, d⟩ := x
  simp only [Function.comp_apply, linD, linH, shearHD]
  rw [foldr_pivotTriple piv hnd1, ← hPm', hA]
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mul_assoc]
  · simp only [Matrix.mulVec_mulVec, h2', Matrix.one_mulVec]

/-! ## Lemma A.6 (`lem:transfer-shear`): streaming lower-triangular maps -/

/-- Invariant of the descending streaming fold: for a strictly decreasing index list `L` and a
state `y` whose coordinates `j ≤ i` (`i ∈ L`) still hold the original values `x.2 j`, the fold
replaces exactly the coordinates in `L` by `(E x.2)_j`. -/
private theorem linD_foldl_aux {m Q : ℕ} (E : Matrix (Fin m) (Fin m) (ZMod Q))
    (hE : ∀ i j, i < j → E i j = 0) (x : HD m Q) (L : List (Fin m)) :
    ∀ y : HD m Q, L.Pairwise (fun a b => b < a) →
      (∀ i ∈ L, ∀ j, j ≤ i → y.2 j = x.2 j) →
      L.foldl (fun y i => (y.1, Function.update y.2 i (∑ j, E i j * y.2 j))) y =
        (y.1, fun j => if j ∈ L then (E *ᵥ x.2) j else y.2 j) := by
  induction L with
  | nil =>
    intro y _ _
    simp
  | cons i L ih =>
    intro y hpw hy
    rw [List.pairwise_cons] at hpw
    obtain ⟨hlt, hpw'⟩ := hpw
    have hsum : ∑ j, E i j * y.2 j = (E *ᵥ x.2) i := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ≤ i
      · rw [hy i (by simp) j hj]
      · rw [hE i j (not_le.mp hj), zero_mul, zero_mul]
    rw [List.foldl_cons]
    simp only [hsum]
    rw [ih]
    · refine Prod.ext rfl ?_
      funext j
      by_cases hji : j = i
      · subst hji
        simp
      · simp [hji]
    · exact hpw'
    · intro i' hi' j hj
      have hne : j ≠ i := ne_of_lt (lt_of_le_of_lt hj (hlt i' hi'))
      simp only [Function.update_of_ne hne]
      exact hy i' (List.mem_cons.mpr (Or.inr hi')) j hj

theorem linDLowerTriStreaming_holds : LinDLowerTriStreamingStmt := by
  intro m Q E hE x
  rw [linD_foldl_aux E hE x (List.finRange m).reverse x
    (List.pairwise_reverse.mpr (List.sortedLT_finRange m).pairwise) (fun _ _ _ _ => rfl)]
  refine Prod.ext rfl ?_
  funext j
  simp [linD]

/-! ## Reduction mod `q^b` of `q`-integral matrices -/

/-- `0` is `q`-integral. -/
private theorem qIntegral_zero {q : ℕ} (hq : q.Prime) : QIntegral q 0 := by
  intro h
  have h1 : (0 : ℚ).den = 1 := by simp
  rw [h1, Nat.dvd_one] at h
  exact hq.ne_one h

/-- `q`-integral rationals are closed under addition. -/
private theorem qIntegral_add {q : ℕ} (hq : q.Prime) {x y : ℚ} (hx : QIntegral q x)
    (hy : QIntegral q y) : QIntegral q (x + y) := fun h =>
  ((Nat.Prime.dvd_mul hq).mp (dvd_trans h (Rat.add_den_dvd x y))).elim hx hy

/-- `q`-integral rationals are closed under multiplication. -/
private theorem qIntegral_mul {q : ℕ} (hq : q.Prime) {x y : ℚ} (hx : QIntegral q x)
    (hy : QIntegral q y) : QIntegral q (x * y) := fun h =>
  ((Nat.Prime.dvd_mul hq).mp (dvd_trans h (Rat.mul_den_dvd x y))).elim hx hy

/-- The denominator of a `q`-integral rational is invertible modulo `q ^ b`. -/
private theorem den_mul_inv_eq_one {q : ℕ} (b : ℕ) (hq : q.Prime) {r : ℚ} (hr : QIntegral q r) :
    (r.den : ZMod (q ^ b)) * (r.den : ZMod (q ^ b))⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one _
    (Nat.Coprime.pow_right b ((Nat.Prime.coprime_iff_not_dvd hq).mpr hr).symm)

/-- Characterization of `ratMod`: if `r · d = n` for integers `n, d` and `iv` is an inverse of `d`
modulo `q ^ b`, then `ratMod (q ^ b) r = n · iv` (for `q`-integral `r`). -/
private theorem ratMod_eq_of_mul {q : ℕ} (b : ℕ) (hq : q.Prime) {r : ℚ} (hr : QIntegral q r)
    (n d : ℤ) (h : r * d = n) (iv : ZMod (q ^ b)) (hiv : (d : ZMod (q ^ b)) * iv = 1) :
    ratMod (q ^ b) r = n * iv := by
  have hden := den_mul_inv_eq_one b hq hr
  have key : (r.num : ℚ) * d = n * r.den := by
    rw [← Rat.mul_den_eq_num r, ← h]
    ring
  have keyZ : r.num * d = n * (r.den : ℤ) := by exact_mod_cast key
  have keyM : (r.num : ZMod (q ^ b)) * (d : ZMod (q ^ b)) =
      (n : ZMod (q ^ b)) * (r.den : ZMod (q ^ b)) := by
    have := congrArg (Int.cast : ℤ → ZMod (q ^ b)) keyZ
    push_cast at this
    exact this
  unfold ratMod
  linear_combination (-((r.num : ZMod (q ^ b)) * (r.den : ZMod (q ^ b))⁻¹)) * hiv +
    (iv * (r.den : ZMod (q ^ b))⁻¹) * keyM + (iv * (n : ZMod (q ^ b))) * hden

/-- `ratMod (q ^ b)` is additive on `q`-integral rationals. -/
private theorem ratMod_add {q : ℕ} (b : ℕ) (hq : q.Prime) {x y : ℚ} (hx : QIntegral q x)
    (hy : QIntegral q y) : ratMod (q ^ b) (x + y) = ratMod (q ^ b) x + ratMod (q ^ b) y := by
  have hdx := den_mul_inv_eq_one b hq hx
  have hdy := den_mul_inv_eq_one b hq hy
  rw [ratMod_eq_of_mul b hq (qIntegral_add hq hx hy) (x.num * y.den + y.num * x.den)
    (x.den * y.den) ?_ ((x.den : ZMod (q ^ b))⁻¹ * (y.den : ZMod (q ^ b))⁻¹) ?_]
  · unfold ratMod
    push_cast
    linear_combination ((x.num : ZMod (q ^ b)) * (x.den : ZMod (q ^ b))⁻¹) * hdy +
      ((y.num : ZMod (q ^ b)) * (y.den : ZMod (q ^ b))⁻¹) * hdx
  · push_cast
    rw [← Rat.mul_den_eq_num x, ← Rat.mul_den_eq_num y]
    ring
  · push_cast
    linear_combination ((y.den : ZMod (q ^ b)) * (y.den : ZMod (q ^ b))⁻¹) * hdx + hdy

/-- `ratMod (q ^ b)` is multiplicative on `q`-integral rationals. -/
private theorem ratMod_mul {q : ℕ} (b : ℕ) (hq : q.Prime) {x y : ℚ} (hx : QIntegral q x)
    (hy : QIntegral q y) : ratMod (q ^ b) (x * y) = ratMod (q ^ b) x * ratMod (q ^ b) y := by
  have hdx := den_mul_inv_eq_one b hq hx
  have hdy := den_mul_inv_eq_one b hq hy
  rw [ratMod_eq_of_mul b hq (qIntegral_mul hq hx hy) (x.num * y.num) (x.den * y.den) ?_
    ((x.den : ZMod (q ^ b))⁻¹ * (y.den : ZMod (q ^ b))⁻¹) ?_]
  · unfold ratMod
    push_cast
    ring
  · push_cast
    rw [← Rat.mul_den_eq_num x, ← Rat.mul_den_eq_num y]
    ring
  · push_cast
    linear_combination ((y.den : ZMod (q ^ b)) * (y.den : ZMod (q ^ b))⁻¹) * hdx + hdy

/-- `ratMod (q ^ b)` commutes with finite sums of `q`-integral rationals, which are `q`-integral. -/
private theorem ratMod_sum {q : ℕ} (b : ℕ) (hq : q.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, QIntegral q (f i)) :
    ratMod (q ^ b) (∑ i ∈ s, f i) = ∑ i ∈ s, ratMod (q ^ b) (f i) ∧
      QIntegral q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · simp [ratMod]
    · rw [Finset.sum_empty]
      exact qIntegral_zero hq
  | insert a s ha ih =>
    have hfa : QIntegral q (f a) := hf a (Finset.mem_insert_self a s)
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨by rw [ratMod_add b hq hfa ih2, ih1], qIntegral_add hq hfa ih2⟩

theorem ratModMatrixMul_holds : RatModMatrixMulStmt := by
  intro m q b hq A B hA hB
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [(ratMod_sum b hq Finset.univ (fun k => A i k * B k j)
      (fun k _ => qIntegral_mul hq (hA i k) (hB k j))).1]
  exact Finset.sum_congr rfl fun k _ => ratMod_mul b hq (hA i k) (hB k j)

/-! ## Proposition A.7 (`prop:transfer11`): the interchange recurrence -/

theorem interchangeRecurrence_holds : InterchangeRecurrenceStmt := by
  intro a M τ c hM ha haM hτ hc
  have hM0 : (0 : ℝ) ≤ M := le_of_lt (lt_trans zero_lt_one hM)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, M ^ τ = ρ := ⟨_, rfl⟩
  have hρ1 : 1 < ρ := by rw [← hρ]; exact Real.one_lt_rpow hM hτ
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ1
  rw [hρ] at haM
  obtain ⟨r, hr⟩ : ∃ r : ℝ, a / ρ = r := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [← hr]; exact div_nonneg ha hρ0.le
  have hr1 : r < 1 := by rw [← hr]; exact (div_lt_one hρ0).mpr haM
  refine ⟨c / (1 - r), fun F hF0 hF k => ?_⟩
  -- `F n ≤ c Σ_{j ≤ n} a^j`
  have step1 : ∀ n : ℕ, F n ≤ c * ∑ j ∈ Finset.range (n + 1), a ^ j := by
    intro n
    induction n with
    | zero => simpa using hF0
    | succ n ih =>
      have hgeom : ∑ j ∈ Finset.range (n + 1 + 1), a ^ j =
          a * ∑ j ∈ Finset.range (n + 1), a ^ j + 1 := by
        rw [Finset.sum_range_succ', pow_zero, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => pow_succ' a j
      have := mul_le_mul_of_nonneg_left ih ha
      calc F (n + 1) ≤ a * F n + c := hF n
        _ ≤ a * (c * ∑ j ∈ Finset.range (n + 1), a ^ j) + c := by linarith
        _ = c * ∑ j ∈ Finset.range (n + 1 + 1), a ^ j := by rw [hgeom]; ring
  -- `Σ_{j ≤ k} a^j ≤ ρ^k / (1 - r)`, since `a^j = r^j ρ^j ≤ r^j ρ^k`
  have step2 : ∑ j ∈ Finset.range (k + 1), a ^ j ≤ ρ ^ k / (1 - r) := by
    have h1 : ∀ j ∈ Finset.range (k + 1), a ^ j ≤ r ^ j * ρ ^ k := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hrj : a ^ j = r ^ j * ρ ^ j := by
        rw [← hr, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hρ0.ne')]
      rw [hrj]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ1.le hjk) (pow_nonneg hr0 _)
    have hgs : ∑ j ∈ Finset.range (k + 1), r ^ j ≤ 1 / (1 - r) := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := k + 1) hr0 hr1
      rw [pow_zero] at this
      rwa [Finset.range_eq_Ico]
    calc ∑ j ∈ Finset.range (k + 1), a ^ j ≤ ∑ j ∈ Finset.range (k + 1), r ^ j * ρ ^ k :=
          Finset.sum_le_sum h1
      _ = (∑ j ∈ Finset.range (k + 1), r ^ j) * ρ ^ k := by rw [Finset.sum_mul]
      _ ≤ 1 / (1 - r) * ρ ^ k := mul_le_mul_of_nonneg_right hgs (pow_nonneg hρ0.le _)
      _ = ρ ^ k / (1 - r) := by ring
  have hpow : M ^ ((k : ℝ) * τ) = ρ ^ k := by
    rw [mul_comm, Real.rpow_mul hM0, hρ, Real.rpow_natCast]
  rw [hpow]
  calc F k ≤ c * ∑ j ∈ Finset.range (k + 1), a ^ j := step1 k
    _ ≤ c * (ρ ^ k / (1 - r)) := mul_le_mul_of_nonneg_left step2 hc
    _ = c / (1 - r) * ρ ^ k := by ring

/-! ## Lemma A.8 (`lem:transfer12`): the cost of the base-`m` pieces -/

/-- Termwise bound for a `zipIdx`-weighted sum: if all entries are `≤ B` and the weights are
nonnegative, the weighted sum is at most `B` times the sum of the weights. -/
private theorem zipIdx_sum_le (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) (B : ℝ) (l : List ℕ) :
    ∀ n : ℕ, (∀ x ∈ l, (x : ℝ) ≤ B) →
      ((l.zipIdx n).map fun p => (p.1 : ℝ) * g p.2).sum ≤
        B * ∑ j ∈ Finset.range l.length, g (n + j) := by
  induction l with
  | nil =>
    intro n _
    simp
  | cons x l ih =>
    intro n hl
    have hx : (x : ℝ) ≤ B := hl x (by simp)
    have hrest := ih (n + 1) (fun y hy => hl y (by simp [hy]))
    have hshift : ∑ j ∈ Finset.range l.length, g (n + 1 + j) =
        ∑ j ∈ Finset.range l.length, g (n + (j + 1)) :=
      Finset.sum_congr rfl fun j _ => by congr 1; omega
    rw [hshift] at hrest
    have hxg : (x : ℝ) * g n ≤ B * g n := mul_le_mul_of_nonneg_right hx (hg n)
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, List.length_cons,
      Finset.sum_range_succ', add_zero]
    rw [mul_add]
    linarith

theorem piecesCost_holds : PiecesCostStmt := by
  intro mm hmm τ hτ
  have hmm1 : (1 : ℝ) < mm := by exact_mod_cast (by omega : 1 < mm)
  have hmm0 : (0 : ℝ) ≤ mm := by positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, (mm : ℝ) ^ τ = ρ := ⟨_, rfl⟩
  have hρ1 : 1 < ρ := by rw [← hρ]; exact Real.one_lt_rpow hmm1 hτ
  refine ⟨((mm : ℝ) - 1) * ρ / (ρ - 1), fun e he => ?_⟩
  have hB : (0 : ℝ) ≤ (mm : ℝ) - 1 := by linarith
  have hg : ∀ j : ℕ, (mm : ℝ) ^ ((j : ℝ) * τ) = ρ ^ j := fun j => by
    rw [mul_comm, Real.rpow_mul hmm0, hρ, Real.rpow_natCast]
  have hdig : ∀ x ∈ Nat.digits mm e, (x : ℝ) ≤ (mm : ℝ) - 1 := by
    intro x hx
    have h1 : x < mm := Nat.digits_lt_base (by omega) hx
    have h2 : (x : ℝ) + 1 ≤ mm := by exact_mod_cast h1
    linarith
  obtain ⟨L, hL⟩ : ∃ L, (Nat.digits mm e).length = L := ⟨_, rfl⟩
  -- digits are `≤ m - 1`
  have h1 : ((Nat.digits mm e).zipIdx.map
      fun p => (p.1 : ℝ) * (mm : ℝ) ^ ((p.2 : ℝ) * τ)).sum ≤
      ((mm : ℝ) - 1) * ∑ j ∈ Finset.range L, ρ ^ j := by
    refine (zipIdx_sum_le (fun j => (mm : ℝ) ^ ((j : ℝ) * τ)) (fun j => by positivity)
      ((mm : ℝ) - 1) (Nat.digits mm e) 0 hdig).trans (le_of_eq ?_)
    rw [hL]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by simp only [zero_add, hg]
  -- geometric sum
  have h2 : ∑ j ∈ Finset.range L, ρ ^ j ≤ ρ ^ L / (ρ - 1) := by
    rw [geom_sum_eq hρ1.ne' L]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  -- `m^L ≤ m e`
  have h3 : ρ ^ L ≤ ρ * (e : ℝ) ^ τ := by
    have hle : mm ^ L ≤ mm * e := by
      rw [← hL]; exact Nat.base_pow_length_digits_le mm e (by omega) (by omega)
    have hle' : (mm : ℝ) ^ L ≤ (mm : ℝ) * e := by exact_mod_cast hle
    calc ρ ^ L = ((mm : ℝ) ^ L) ^ τ := by
          rw [← hρ, ← Real.rpow_natCast ((mm : ℝ) ^ τ) L, ← Real.rpow_mul hmm0,
            ← Real.rpow_natCast (mm : ℝ) L, ← Real.rpow_mul hmm0, mul_comm]
      _ ≤ ((mm : ℝ) * e) ^ τ := Real.rpow_le_rpow (by positivity) hle' hτ.le
      _ = ρ * (e : ℝ) ^ τ := by rw [Real.mul_rpow hmm0 (by positivity), hρ]
  calc ((Nat.digits mm e).zipIdx.map fun p => (p.1 : ℝ) * (mm : ℝ) ^ ((p.2 : ℝ) * τ)).sum
      ≤ ((mm : ℝ) - 1) * ∑ j ∈ Finset.range L, ρ ^ j := h1
    _ ≤ ((mm : ℝ) - 1) * (ρ ^ L / (ρ - 1)) := mul_le_mul_of_nonneg_left h2 hB
    _ ≤ ((mm : ℝ) - 1) * (ρ * (e : ℝ) ^ τ / (ρ - 1)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h3 (by linarith)) hB
    _ = ((mm : ℝ) - 1) * ρ / (ρ - 1) * (e : ℝ) ^ τ := by ring

end SubNLogN.Math.Networks
