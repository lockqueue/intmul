import SubNLogN.Math.Walsh.DirectFFT

/-!
# Direct FFT, exact part: tensor encoding, exact DIF, tensor factorization

Proofs of the contracts `TensorEncodingStmt`, `DifExactStmt` and `TensorFactorStmt` of
`SubNLogN/Math/Walsh/DirectFFT.lean` (Section 6 (`sec:direct-fft`), eq. (`eq:dif`),
and Theorem 6.5 (`thm:direct-fft`)).

* `tensor_encoding`: the slot map `(i, v) ↦ origPos a i v` is injective (prefix sums) and hence,
  by counting, a bijection onto the `addrBits a` record-address positions; together with the
  LSB-first binary expansion of `axisVal` this makes `tensorIdx` / `(cubeOfIdx, coeffOfIdx)`
  mutually inverse (`tensorEquiv`).
* `dif_exact`: induction on `ℓ`. Level `0` maps `w` to the two halves
  `y^b_j = e^{2πibj/2^{ℓ+1}} (w_j + (-1)^b w_{j+2^ℓ})/2`, with
  `(F_{2^{ℓ+1}} w)_{2v+b} = (F_{2^ℓ} y^b)_v` (eq. (`eq:dif`)); levels `1, …, ℓ` act on each half as the
  levels `0, …, ℓ-1` of length `2^ℓ`; and `bitRev_{ℓ+1}(2v+b) = b·2^ℓ + bitRev_ℓ(v)`.
* `tensor_factor`: reindex the tensor DFT sum by `tensorEquiv` and split the phase
  `∑_{i ≤ D}` into the record axes and the last axis.
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common
open scoped BigOperators

namespace DirectFFTExactProof

/-! ## Binary expansions (LSB first) -/

/-- `∑_{v<k} [bit v of n] 2^v = n` for `n < 2^k`. -/
theorem sum_testBit_eq (k n : ℕ) (hn : n < 2 ^ k) :
    ∑ v ∈ Finset.range k, (if n.testBit v = true then 2 ^ v else 0) = n := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    simp [this]
  | succ k ih =>
    rw [Finset.sum_range_succ']
    have h2 : n / 2 < 2 ^ k := by rw [pow_succ] at hn; omega
    have hterm : ∀ v ∈ Finset.range k, (if n.testBit (v + 1) = true then 2 ^ (v + 1) else 0) =
        2 * (if (n / 2).testBit v = true then 2 ^ v else 0) := by
      intro v _
      rw [Nat.testBit_succ]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ih (n / 2) h2, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

/-- Bit `w < k` of `∑_{v<k} [b v] 2^v` is `b w`. -/
theorem testBit_sum_bits (b : ℕ → Bool) (k w : ℕ) (hw : w < k) :
    (∑ v ∈ Finset.range k, (if b v = true then 2 ^ v else 0)).testBit w = b w := by
  induction k generalizing b w with
  | zero => omega
  | succ k ih =>
    rw [Finset.sum_range_succ']
    have hterm : ∀ v ∈ Finset.range k, (if b (v + 1) = true then 2 ^ (v + 1) else 0) =
        2 * (if b (v + 1) = true then 2 ^ v else 0) := by
      intro v _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have ih' := ih (fun v => b (v + 1))
    set S := ∑ v ∈ Finset.range k, (if b (v + 1) = true then 2 ^ v else 0) with hS
    cases w with
    | zero =>
      rw [Nat.testBit_zero]
      cases h : b 0 <;> simp
    | succ w =>
      rw [Nat.testBit_succ]
      have hdiv : (2 * S + (if b 0 = true then 2 ^ 0 else 0)) / 2 = S := by
        split_ifs <;> omega
      rw [hdiv]
      exact ih' w (by omega)

/-- `∑_{v<k} [b v] 2^v < 2^k`. -/
theorem sum_bits_lt (b : ℕ → Bool) (k : ℕ) :
    ∑ v ∈ Finset.range k, (if b v = true then 2 ^ v else 0) < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    split_ifs <;> omega

/-! ## The original slot positions -/

section Slots

variable {D : ℕ}

theorem axisOffset_eq (a : Fin D → ℕ) (i : Fin D) :
    axisOffset a i = ∑ j ∈ Finset.univ.filter (fun j : Fin D => (j : ℕ) < (i : ℕ)), a j := by
  unfold axisOffset
  exact List.sum_take_ofFn a i

theorem addrBits_eq (a : Fin D → ℕ) : addrBits a = ∑ i, a i := by
  unfold addrBits
  exact List.sum_ofFn

theorem axisOffset_add_le_of_subset (a : Fin D → ℕ) (i : Fin D) (s : Finset (Fin D))
    (hs : insert i (Finset.univ.filter (fun j : Fin D => (j : ℕ) < (i : ℕ))) ⊆ s) :
    axisOffset a i + a i ≤ ∑ j ∈ s, a j := by
  rw [axisOffset_eq]
  have hnot : i ∉ Finset.univ.filter (fun j : Fin D => (j : ℕ) < (i : ℕ)) := by simp
  calc (∑ j ∈ Finset.univ.filter (fun j : Fin D => (j : ℕ) < (i : ℕ)), a j) + a i
      = ∑ j ∈ insert i (Finset.univ.filter (fun j : Fin D => (j : ℕ) < (i : ℕ))), a j := by
        rw [Finset.sum_insert hnot, add_comm]
    _ ≤ ∑ j ∈ s, a j := Finset.sum_le_sum_of_subset hs

/-- Axis `i` occupies the positions `[axisOffset a i, axisOffset a i + a i)` before axis `i'`. -/
theorem axisOffset_add_le (a : Fin D → ℕ) {i i' : Fin D} (h : i < i') :
    axisOffset a i + a i ≤ axisOffset a i' := by
  rw [axisOffset_eq a i']
  apply axisOffset_add_le_of_subset
  intro j hj
  have h' : (i : ℕ) < (i' : ℕ) := Fin.lt_def.mp h
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  rcases hj with rfl | hj
  · exact h'
  · exact lt_trans hj h'

theorem axisOffset_add_le_addrBits (a : Fin D → ℕ) (i : Fin D) :
    axisOffset a i + a i ≤ addrBits a := by
  rw [addrBits_eq]
  exact axisOffset_add_le_of_subset a i _ (Finset.subset_univ _)

theorem origPos_lt (a : Fin D → ℕ) (i : Fin D) {v : ℕ} (hv : v < a i) :
    origPos a i v < addrBits a := by
  have := axisOffset_add_le_addrBits a i
  unfold origPos
  omega

theorem origPos_inj (a : Fin D → ℕ) {i i' : Fin D} {v v' : ℕ} (hv : v < a i) (hv' : v' < a i')
    (h : origPos a i v = origPos a i' v') : i = i' ∧ v = v' := by
  unfold origPos at h
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · have := axisOffset_add_le a hlt
    omega
  · subst heq
    exact ⟨rfl, by omega⟩
  · have := axisOffset_add_le a hgt
    omega

/-- The slot map `(i, v) ↦ origPos a i v` into the record-address positions. -/
def slotPos (a : Fin D → ℕ) (s : Σ i : Fin D, Fin (a i)) : Fin (addrBits a) :=
  ⟨origPos a s.1 s.2, origPos_lt a s.1 s.2.isLt⟩

theorem slotPos_bijective (a : Fin D → ℕ) : Function.Bijective (slotPos a) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, v⟩ ⟨i', v'⟩ h
    have h' : origPos a i v = origPos a i' v' := congrArg Fin.val h
    obtain ⟨rfl, hv⟩ := origPos_inj a v.isLt v'.isLt h'
    have : v = v' := Fin.ext hv
    subst this
    rfl
  · simp [Fintype.card_sigma, addrBits_eq]

theorem exists_origPos (a : Fin D → ℕ) (p : Fin (addrBits a)) :
    ∃ i : Fin D, ∃ v : Fin (a i), origPos a i v = (p : ℕ) := by
  obtain ⟨⟨i, v⟩, h⟩ := (slotPos_bijective a).2 p
  exact ⟨i, v, congrArg Fin.val h⟩

end Slots


/-! ## The tensor encoding -/

section Encoding

variable {D : ℕ}

theorem cubeBit_fin {m : ℕ} (x : Cube m) (p : Fin m) : cubeBit x (p : ℕ) = x p := by
  simp [cubeBit]

theorem cubeBit_lt {m : ℕ} (x : Cube m) {p : ℕ} (hp : p < m) : cubeBit x p = x ⟨p, hp⟩ := by
  simp [cubeBit, hp]

theorem axisVal_lt (a : Fin D → ℕ) {m : ℕ} (x : Cube m) (i : Fin D) : axisVal a x i < 2 ^ a i :=
  sum_bits_lt (fun v => cubeBit x (origPos a i v)) (a i)

theorem testBit_axisVal (a : Fin D → ℕ) {m : ℕ} (x : Cube m) (i : Fin D) {v : ℕ} (hv : v < a i) :
    (axisVal a x i).testBit v = cubeBit x (origPos a i v) :=
  testBit_sum_bits (fun v => cubeBit x (origPos a i v)) (a i) v hv

theorem fftExp_castSucc (a : Fin D → ℕ) (ℓ : ℕ) (i : Fin D) :
    fftExp a ℓ (Fin.castSucc i) = a i := by
  simp [fftExp]

theorem fftExp_last (a : Fin D → ℕ) (ℓ : ℕ) : fftExp a ℓ (Fin.last D) = ℓ := by
  simp [fftExp]

theorem fftShape_castSucc (a : Fin D → ℕ) (ℓ : ℕ) (i : Fin D) :
    fftShape a ℓ (Fin.castSucc i) = 2 ^ a i := by
  simp only [fftShape, fftExp_castSucc]

theorem fftShape_last (a : Fin D → ℕ) (ℓ : ℕ) : fftShape a ℓ (Fin.last D) = 2 ^ ℓ := by
  simp only [fftShape, fftExp_last]

theorem tensorIdx_castSucc_val (a : Fin D → ℕ) (ℓ : ℕ) (x : Cube (addrBits a)) (k : Fin (2 ^ ℓ))
    (i : Fin D) : ((tensorIdx a ℓ x k (Fin.castSucc i) : Fin _) : ℕ) = axisVal a x i := by
  have h : ((Fin.castSucc i : Fin (D + 1)) : ℕ) < D := by simp
  show (if h : ((Fin.castSucc i : Fin (D + 1)) : ℕ) < D then axisVal a x ⟨_, h⟩ else (k : ℕ)) %
    2 ^ fftExp a ℓ (Fin.castSucc i) = axisVal a x i
  rw [dif_pos h, fftExp_castSucc]
  exact Nat.mod_eq_of_lt (axisVal_lt a x i)

theorem tensorIdx_last_val (a : Fin D → ℕ) (ℓ : ℕ) (x : Cube (addrBits a)) (k : Fin (2 ^ ℓ)) :
    ((tensorIdx a ℓ x k (Fin.last D) : Fin _) : ℕ) = k := by
  have h : ¬ ((Fin.last D : Fin (D + 1)) : ℕ) < D := by simp
  show (if h : ((Fin.last D : Fin (D + 1)) : ℕ) < D then axisVal a x ⟨_, h⟩ else (k : ℕ)) %
    2 ^ fftExp a ℓ (Fin.last D) = k
  rw [dif_neg h, fftExp_last]
  exact Nat.mod_eq_of_lt k.isLt

theorem coeffOfIdx_val (a : Fin D → ℕ) (ℓ : ℕ) (j : Idx (fftShape a ℓ)) :
    (coeffOfIdx a ℓ j : ℕ) = (j (Fin.last D) : ℕ) := by
  show (j (Fin.last D) : ℕ) % 2 ^ ℓ = _
  exact Nat.mod_eq_of_lt (lt_of_lt_of_eq (j (Fin.last D)).isLt (fftShape_last a ℓ))

theorem cubeBit_cubeOfIdx (a : Fin D → ℕ) (ℓ : ℕ) (j : Idx (fftShape a ℓ)) (i : Fin D) {v : ℕ}
    (hv : v < a i) :
    cubeBit (cubeOfIdx a ℓ j) (origPos a i v) = (j (Fin.castSucc i) : ℕ).testBit v := by
  rw [cubeBit_lt _ (origPos_lt a i hv)]
  unfold cubeOfIdx
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨i', v', hpos, hbit⟩
    obtain ⟨rfl, hvv⟩ := origPos_inj a v'.isLt hv hpos
    rw [← hvv]
    exact hbit
  · intro h
    exact ⟨i, ⟨v, hv⟩, rfl, h⟩

theorem axisVal_cubeOfIdx (a : Fin D → ℕ) (ℓ : ℕ) (j : Idx (fftShape a ℓ)) (i : Fin D) :
    axisVal a (cubeOfIdx a ℓ j) i = (j (Fin.castSucc i) : ℕ) := by
  unfold axisVal
  have hterm : ∀ v ∈ Finset.range (a i),
      (if cubeBit (cubeOfIdx a ℓ j) (origPos a i v) = true then 2 ^ v else 0) =
        (if (j (Fin.castSucc i) : ℕ).testBit v = true then 2 ^ v else 0) := by
    intro v hv
    rw [cubeBit_cubeOfIdx a ℓ j i (Finset.mem_range.mp hv)]
  rw [Finset.sum_congr rfl hterm]
  exact sum_testBit_eq _ _ (lt_of_lt_of_eq (j (Fin.castSucc i)).isLt (fftShape_castSucc a ℓ i))

theorem cubeOfIdx_tensorIdx (a : Fin D → ℕ) (ℓ : ℕ) (x : Cube (addrBits a)) (k : Fin (2 ^ ℓ)) :
    cubeOfIdx a ℓ (tensorIdx a ℓ x k) = x := by
  funext p
  unfold cubeOfIdx
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨i, v, hpos, hbit⟩
    rw [tensorIdx_castSucc_val, testBit_axisVal a x i v.isLt, hpos, cubeBit_fin] at hbit
    exact hbit
  · intro hx
    obtain ⟨i, v, hiv⟩ := exists_origPos a p
    refine ⟨i, v, hiv, ?_⟩
    rw [tensorIdx_castSucc_val, testBit_axisVal a x i v.isLt, hiv, cubeBit_fin]
    exact hx

theorem coeffOfIdx_tensorIdx (a : Fin D → ℕ) (ℓ : ℕ) (x : Cube (addrBits a)) (k : Fin (2 ^ ℓ)) :
    coeffOfIdx a ℓ (tensorIdx a ℓ x k) = k := by
  apply Fin.ext
  rw [coeffOfIdx_val, tensorIdx_last_val]

theorem tensorIdx_cubeOfIdx (a : Fin D → ℕ) (ℓ : ℕ) (j : Idx (fftShape a ℓ)) :
    tensorIdx a ℓ (cubeOfIdx a ℓ j) (coeffOfIdx a ℓ j) = j := by
  funext i
  apply Fin.ext
  induction i using Fin.lastCases with
  | last => rw [tensorIdx_last_val, coeffOfIdx_val]
  | cast i => rw [tensorIdx_castSucc_val, axisVal_cubeOfIdx]

/-- The tensor encoding as an equivalence `Cube (addrBits a) × Fin (2^ℓ) ≃ Idx (fftShape a ℓ)`. -/
def tensorEquiv (a : Fin D → ℕ) (ℓ : ℕ) : Cube (addrBits a) × Fin (2 ^ ℓ) ≃ Idx (fftShape a ℓ) where
  toFun p := tensorIdx a ℓ p.1 p.2
  invFun j := (cubeOfIdx a ℓ j, coeffOfIdx a ℓ j)
  left_inv p := by
    obtain ⟨x, k⟩ := p
    simp only [cubeOfIdx_tensorIdx, coeffOfIdx_tensorIdx]
  right_inv j := tensorIdx_cubeOfIdx a ℓ j

end Encoding

/-! ## The exact DIF -/

section DIF

theorem getCoeff_of_lt {n : ℕ} (w : Fin n → ℂ) {k : ℕ} (hk : k < n) :
    getCoeff w k = w ⟨k, hk⟩ := by
  simp [getCoeff, hk]

theorem getCoeff_fin {n : ℕ} (w : Fin n → ℂ) (k : Fin n) : getCoeff w k = w k := by
  simp [getCoeff]

theorem dft_apply_fin (R : ℕ) (x : Fin R → ℂ) (u : Fin R) :
    dft R x u = (R : ℂ)⁻¹ *
      ∑ j : Fin R, x j * IntMul.stdChar ((((j : ℕ) * (u : ℕ) : ℕ) : ℝ) / (R : ℝ)) := rfl

/-- `F_R` as a sum over `range R` of the zero-extended coefficients. -/
theorem dft_apply_mk (R : ℕ) (x : Fin R → ℂ) (u : ℕ) (hu : u < R) :
    dft R x ⟨u, hu⟩ = (R : ℂ)⁻¹ *
      ∑ j ∈ Finset.range R, getCoeff x j * IntMul.stdChar (((j * u : ℕ) : ℝ) / (R : ℝ)) := by
  rw [dft_apply_fin]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => getCoeff x j * IntMul.stdChar (((j * u : ℕ) : ℝ) / (R : ℝ))) R]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [getCoeff_fin]

theorem sum_range_two_pow_succ (ℓ : ℕ) (f : ℕ → ℂ) :
    ∑ k ∈ Finset.range (2 ^ (ℓ + 1)), f k =
      ∑ j ∈ Finset.range (2 ^ ℓ), (f j + f (2 ^ ℓ + j)) := by
  rw [pow_succ, mul_two, Finset.sum_range_add, Finset.sum_add_distrib]

theorem stdChar_half : IntMul.stdChar (1 / 2) = -1 := by
  unfold IntMul.stdChar
  have h : (((2 * Real.pi * (1 / 2) : ℝ) : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_pi_mul_I]

/-- The exact DIF levels `0, …, ℓ-1` (before the bit reversal). -/
noncomputable def difAll (ℓ : ℕ) (w : Fin (2 ^ ℓ) → ℂ) : Fin (2 ^ ℓ) → ℂ :=
  (List.range ℓ).foldl (fun w s => difLevelExact ℓ s w) w

/-- Half `b` (`b ∈ {0, 1}`) of a vector of length `2^(ℓ+1)`. -/
noncomputable def halfVec (ℓ b : ℕ) (w : Fin (2 ^ (ℓ + 1)) → ℂ) : Fin (2 ^ ℓ) → ℂ :=
  fun k => getCoeff w (b * 2 ^ ℓ + k)

theorem getCoeff_halfVec (ℓ b : ℕ) (w : Fin (2 ^ (ℓ + 1)) → ℂ) {k : ℕ} (hk : k < 2 ^ ℓ) :
    getCoeff (halfVec ℓ b w) k = getCoeff w (b * 2 ^ ℓ + k) := by
  rw [getCoeff_of_lt _ hk]
  rfl

theorem theta_two_mul (ℓ s X : ℕ) :
    theta (2 ^ (ℓ + 1)) (2 ^ (s + 1 + 1) * X) = theta (2 ^ ℓ) (2 ^ (s + 1) * X) := by
  unfold theta
  congr 1
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem mul_pow_add_mod (b k ℓ s : ℕ) :
    (b * 2 ^ ℓ + k) % 2 ^ (ℓ - s) = k % 2 ^ (ℓ - s) := by
  obtain ⟨c, hc⟩ : 2 ^ (ℓ - s) ∣ 2 ^ ℓ := pow_dvd_pow 2 (Nat.sub_le ℓ s)
  rw [hc, show b * (2 ^ (ℓ - s) * c) = 2 ^ (ℓ - s) * (b * c) by ring, Nat.mul_add_mod]

theorem add_half_lt_of_mod_lt (k ℓ s : ℕ) (hs : s < ℓ) (hk : k < 2 ^ ℓ)
    (hcond : k % 2 ^ (ℓ - s) < 2 ^ (ℓ - s - 1)) : k + 2 ^ (ℓ - s - 1) < 2 ^ ℓ := by
  obtain ⟨c, hc⟩ : 2 ^ (ℓ - s) ∣ 2 ^ ℓ := pow_dvd_pow 2 (Nat.sub_le ℓ s)
  have hu2 : 2 ^ (ℓ - s) = 2 * 2 ^ (ℓ - s - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hupos : 0 < 2 ^ (ℓ - s) := by positivity
  have h1 := Nat.div_add_mod k (2 ^ (ℓ - s))
  rw [hc] at hk ⊢
  have h2 : k / 2 ^ (ℓ - s) < c := by
    rw [Nat.div_lt_iff_lt_mul hupos]
    linarith [mul_comm (2 ^ (ℓ - s)) c]
  have h3 : 2 ^ (ℓ - s) * (k / 2 ^ (ℓ - s) + 1) ≤ 2 ^ (ℓ - s) * c :=
    Nat.mul_le_mul_left _ h2
  rw [mul_add, mul_one] at h3
  linarith

/-- Levels `s + 1` of length `2^(ℓ+1)` act on each half as level `s` of length `2^ℓ`. -/
theorem halfVec_difLevelExact (ℓ s b : ℕ) (hs : s < ℓ) (hb : b < 2)
    (w : Fin (2 ^ (ℓ + 1)) → ℂ) :
    halfVec ℓ b (difLevelExact (ℓ + 1) (s + 1) w) = difLevelExact ℓ s (halfVec ℓ b w) := by
  funext k
  have hk := k.isLt
  have hpow : (2 : ℕ) ^ (ℓ + 1) = 2 * 2 ^ ℓ := by ring
  have hbk : b * 2 ^ ℓ + (k : ℕ) < 2 ^ (ℓ + 1) := by
    rw [hpow]
    interval_cases b <;> omega
  have e1 : ℓ + 1 - (s + 1) = ℓ - s := by omega
  have hmod := mul_pow_add_mod b (k : ℕ) ℓ s
  show getCoeff (difLevelExact (ℓ + 1) (s + 1) w) (b * 2 ^ ℓ + k) =
    difLevelExact ℓ s (halfVec ℓ b w) k
  rw [getCoeff_of_lt _ hbk]
  simp only [difLevelExact, e1, hmod]
  split_ifs with hcond
  · -- upper outputs
    rw [getCoeff_halfVec _ _ _ hk,
      getCoeff_halfVec _ _ _ (add_half_lt_of_mod_lt _ _ _ hs hk hcond), add_assoc]
  · -- lower outputs
    have hk3 : 2 ^ (ℓ - s - 1) ≤ (k : ℕ) := by
      have := Nat.mod_le (k : ℕ) (2 ^ (ℓ - s))
      omega
    rw [theta_two_mul, getCoeff_halfVec _ _ _ (lt_of_le_of_lt (Nat.sub_le _ _) hk),
      getCoeff_halfVec _ _ _ hk, Nat.add_sub_assoc hk3]

theorem difAll_succ (ℓ : ℕ) (w : Fin (2 ^ (ℓ + 1)) → ℂ) :
    difAll (ℓ + 1) w = (List.range ℓ).foldl (fun w s => difLevelExact (ℓ + 1) (s + 1) w)
      (difLevelExact (ℓ + 1) 0 w) := by
  unfold difAll
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]

theorem halfVec_foldl (ℓ b : ℕ) (hb : b < 2) (l : List ℕ) (hl : ∀ s ∈ l, s < ℓ)
    (w : Fin (2 ^ (ℓ + 1)) → ℂ) :
    halfVec ℓ b (l.foldl (fun w s => difLevelExact (ℓ + 1) (s + 1) w) w) =
      l.foldl (fun w s => difLevelExact ℓ s w) (halfVec ℓ b w) := by
  induction l generalizing w with
  | nil => rfl
  | cons s l ih =>
    simp only [List.foldl_cons]
    rw [ih (fun s' hs' => hl s' (List.mem_cons_of_mem _ hs')),
      halfVec_difLevelExact ℓ s b (hl s (by simp)) hb]

theorem bitRevNat_succ (ℓ p : ℕ) :
    bitRevNat (ℓ + 1) p = bitRevNat ℓ (p / 2) + p % 2 * 2 ^ ℓ := by
  unfold bitRevNat
  rw [Finset.sum_range_succ']
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i < ℓ := Finset.mem_range.mp hi
    rw [Nat.testBit_succ]
    have : ℓ + 1 - 1 - (i + 1) = ℓ - 1 - i := by omega
    rw [this]
  · rcases Nat.mod_two_eq_zero_or_one p with h | h <;> simp [h]

theorem bitRevNat_succ' (ℓ p : ℕ) :
    bitRevNat (ℓ + 1) p = p % 2 * 2 ^ ℓ + bitRevNat ℓ (p / 2) :=
  (bitRevNat_succ ℓ p).trans (Nat.add_comm _ _)

theorem bitRevNat_lt (ℓ p : ℕ) : bitRevNat ℓ p < 2 ^ ℓ := by
  induction ℓ generalizing p with
  | zero => simp [bitRevNat]
  | succ ℓ ih =>
    rw [bitRevNat_succ, pow_succ]
    have h1 := ih (p / 2)
    rcases Nat.mod_two_eq_zero_or_one p with h | h <;> rw [h] <;> omega

theorem halfVec_level0_zero (ℓ : ℕ) (w : Fin (2 ^ (ℓ + 1)) → ℂ) {j : ℕ} (hj : j < 2 ^ ℓ) :
    getCoeff (halfVec ℓ 0 (difLevelExact (ℓ + 1) 0 w)) j =
      (getCoeff w j + getCoeff w (2 ^ ℓ + j)) / 2 := by
  have hpow : (2 : ℕ) ^ (ℓ + 1) = 2 * 2 ^ ℓ := by ring
  have hlt : 0 * 2 ^ ℓ + j < 2 ^ (ℓ + 1) := by omega
  rw [getCoeff_halfVec _ _ _ hj, getCoeff_of_lt _ hlt]
  have hc : (0 * 2 ^ ℓ + j) % 2 ^ (ℓ + 1 - 0) < 2 ^ (ℓ + 1 - 0 - 1) := by
    rw [Nat.sub_zero, Nat.add_sub_cancel, zero_mul, zero_add, Nat.mod_eq_of_lt (by omega)]
    exact hj
  simp only [difLevelExact, if_pos hc]
  rw [Nat.sub_zero, Nat.add_sub_cancel, zero_mul, zero_add, add_comm j]

theorem halfVec_level0_one (ℓ : ℕ) (w : Fin (2 ^ (ℓ + 1)) → ℂ) {j : ℕ} (hj : j < 2 ^ ℓ) :
    getCoeff (halfVec ℓ 1 (difLevelExact (ℓ + 1) 0 w)) j =
      theta (2 ^ (ℓ + 1)) (2 * j) * ((getCoeff w j - getCoeff w (2 ^ ℓ + j)) / 2) := by
  have hpow : (2 : ℕ) ^ (ℓ + 1) = 2 * 2 ^ ℓ := by ring
  have hlt : 1 * 2 ^ ℓ + j < 2 ^ (ℓ + 1) := by omega
  rw [getCoeff_halfVec _ _ _ hj, getCoeff_of_lt _ hlt]
  have hmod : (1 * 2 ^ ℓ + j) % 2 ^ (ℓ + 1 - 0) = 2 ^ ℓ + j := by
    rw [Nat.sub_zero, one_mul]
    exact Nat.mod_eq_of_lt (by omega)
  have hc : ¬ (1 * 2 ^ ℓ + j) % 2 ^ (ℓ + 1 - 0) < 2 ^ (ℓ + 1 - 0 - 1) := by
    rw [hmod, Nat.sub_zero, Nat.add_sub_cancel]
    omega
  simp only [difLevelExact, if_neg hc]
  rw [hmod, Nat.sub_zero, Nat.add_sub_cancel, one_mul, Nat.add_sub_cancel_left, zero_add, pow_one]

/-- Eq. (`eq:dif`), even frequencies: `(F_{2^{ℓ+1}} w)_{2v} = (F_{2^ℓ} y^0)_v`. -/
theorem dft_even (ℓ : ℕ) (w : Fin (2 ^ (ℓ + 1)) → ℂ) (p : Fin (2 ^ (ℓ + 1))) (v : ℕ)
    (hpv : (p : ℕ) = 2 * v) (hv : v < 2 ^ ℓ) :
    dft (2 ^ (ℓ + 1)) w p = dft (2 ^ ℓ) (halfVec ℓ 0 (difLevelExact (ℓ + 1) 0 w)) ⟨v, hv⟩ := by
  obtain ⟨pv, hp⟩ := p
  simp only at hpv
  subst hpv
  rw [dft_apply_mk, dft_apply_mk, sum_range_two_pow_succ, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j < 2 ^ ℓ := Finset.mem_range.mp hj
  rw [halfVec_level0_zero ℓ w hj']
  have e1 : IntMul.stdChar (((j * (2 * v) : ℕ) : ℝ) / ((2 ^ (ℓ + 1) : ℕ) : ℝ)) =
      IntMul.stdChar (((j * v : ℕ) : ℝ) / ((2 ^ ℓ : ℕ) : ℝ)) := by
    congr 1
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have e2 : IntMul.stdChar ((((2 ^ ℓ + j) * (2 * v) : ℕ) : ℝ) / ((2 ^ (ℓ + 1) : ℕ) : ℝ)) =
      IntMul.stdChar (((j * v : ℕ) : ℝ) / ((2 ^ ℓ : ℕ) : ℝ)) := by
    have h : ((((2 ^ ℓ + j) * (2 * v) : ℕ) : ℝ) / ((2 ^ (ℓ + 1) : ℕ) : ℝ)) =
        ((j * v : ℕ) : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) + ((v : ℤ) : ℝ) := by
      push_cast
      field_simp
      ring
    rw [h, IntMul.stdChar_add_int]
  rw [e1, e2]
  push_cast
  ring

/-- Eq. (`eq:dif`), odd frequencies: `(F_{2^{ℓ+1}} w)_{2v+1} = (F_{2^ℓ} y^1)_v`. -/
theorem dft_odd (ℓ : ℕ) (w : Fin (2 ^ (ℓ + 1)) → ℂ) (p : Fin (2 ^ (ℓ + 1))) (v : ℕ)
    (hpv : (p : ℕ) = 2 * v + 1) (hv : v < 2 ^ ℓ) :
    dft (2 ^ (ℓ + 1)) w p = dft (2 ^ ℓ) (halfVec ℓ 1 (difLevelExact (ℓ + 1) 0 w)) ⟨v, hv⟩ := by
  obtain ⟨pv, hp⟩ := p
  simp only at hpv
  subst hpv
  rw [dft_apply_mk, dft_apply_mk, sum_range_two_pow_succ, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j < 2 ^ ℓ := Finset.mem_range.mp hj
  rw [halfVec_level0_one ℓ w hj']
  have hth : theta (2 ^ (ℓ + 1)) (2 * j) =
      IntMul.stdChar (((2 * j : ℕ) : ℝ) / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ))) := rfl
  have e1 : IntMul.stdChar (((j * (2 * v + 1) : ℕ) : ℝ) / ((2 ^ (ℓ + 1) : ℕ) : ℝ)) =
      IntMul.stdChar (((j * v : ℕ) : ℝ) / ((2 ^ ℓ : ℕ) : ℝ)) *
        IntMul.stdChar (((2 * j : ℕ) : ℝ) / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ))) := by
    rw [← IntMul.stdChar_add]
    congr 1
    push_cast
    field_simp
    ring
  have e2 : IntMul.stdChar ((((2 ^ ℓ + j) * (2 * v + 1) : ℕ) : ℝ) / ((2 ^ (ℓ + 1) : ℕ) : ℝ)) =
      -(IntMul.stdChar (((j * v : ℕ) : ℝ) / ((2 ^ ℓ : ℕ) : ℝ)) *
        IntMul.stdChar (((2 * j : ℕ) : ℝ) / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ)))) := by
    have h : ((((2 ^ ℓ + j) * (2 * v + 1) : ℕ) : ℝ) / ((2 ^ (ℓ + 1) : ℕ) : ℝ)) =
        (((j * v : ℕ) : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) +
          ((2 * j : ℕ) : ℝ) / (2 * ((2 ^ (ℓ + 1) : ℕ) : ℝ)) + 1 / 2) + ((v : ℤ) : ℝ) := by
      push_cast
      field_simp
      ring
    rw [h, IntMul.stdChar_add_int, IntMul.stdChar_add, IntMul.stdChar_add, stdChar_half]
    ring
  rw [hth, e1, e2]
  push_cast
  ring

/-- The exact DIF levels followed by bit reversal compute `F_{2^ℓ}`. -/
theorem difAll_bitRev : ∀ (ℓ : ℕ) (w : Fin (2 ^ ℓ) → ℂ) (p : Fin (2 ^ ℓ)),
    getCoeff (difAll ℓ w) (bitRevNat ℓ p) = dft (2 ^ ℓ) w p := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro w p
    obtain ⟨pv, hp⟩ := p
    have hpv : pv = 0 := by simpa using hp
    subst hpv
    rw [dft_apply_mk]
    simp [difAll, bitRevNat]
  | succ ℓ ih =>
    intro w p
    have hp := p.isLt
    have hpow : (2 : ℕ) ^ (ℓ + 1) = 2 * 2 ^ ℓ := by ring
    have hv : (p : ℕ) / 2 < 2 ^ ℓ := by omega
    have hlt := bitRevNat_lt ℓ ((p : ℕ) / 2)
    have hb2 : (p : ℕ) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rw [bitRevNat_succ', difAll_succ, ← getCoeff_halfVec ℓ _ _ hlt,
      halfVec_foldl ℓ ((p : ℕ) % 2) hb2 (List.range ℓ) (fun s hs => List.mem_range.mp hs)]
    have key : getCoeff (difAll ℓ (halfVec ℓ ((p : ℕ) % 2) (difLevelExact (ℓ + 1) 0 w)))
        (bitRevNat ℓ ((p : ℕ) / 2)) =
        dft (2 ^ ℓ) (halfVec ℓ ((p : ℕ) % 2) (difLevelExact (ℓ + 1) 0 w)) ⟨(p : ℕ) / 2, hv⟩ :=
      ih _ ⟨(p : ℕ) / 2, hv⟩
    rw [show (List.range ℓ).foldl (fun w s => difLevelExact ℓ s w)
        (halfVec ℓ ((p : ℕ) % 2) (difLevelExact (ℓ + 1) 0 w)) =
        difAll ℓ (halfVec ℓ ((p : ℕ) % 2) (difLevelExact (ℓ + 1) 0 w)) from rfl, key]
    rcases Nat.mod_two_eq_zero_or_one (p : ℕ) with h | h
    · rw [h]
      exact (dft_even ℓ w p ((p : ℕ) / 2) (by omega) hv).symm
    · rw [h]
      exact (dft_odd ℓ w p ((p : ℕ) / 2) (by omega) hv).symm

end DIF

/-! ## Tensor factorization -/

section Factor

variable {D : ℕ}

theorem totalLen_fftShape (a : Fin D → ℕ) (ℓ : ℕ) :
    totalLen (fftShape a ℓ) = 2 ^ addrBits a * 2 ^ ℓ := by
  unfold totalLen
  rw [Fin.prod_univ_castSucc, fftShape_last]
  simp only [fftShape_castSucc]
  rw [Finset.prod_pow_eq_pow_sum, addrBits_eq]

/-- `F_t U` as a sum over record addresses and coefficient indices (reindexing by
`tensorEquiv`). -/
theorem dftTensor_eq_sum_tensorEquiv (a : Fin D → ℕ) (ℓ : ℕ) (U : Idx (fftShape a ℓ) → ℂ)
    (j : Idx (fftShape a ℓ)) :
    dftTensor (fftShape a ℓ) U j = ((totalLen (fftShape a ℓ) : ℕ) : ℂ)⁻¹ *
      ∑ p : Cube (addrBits a) × Fin (2 ^ ℓ), U (tensorIdx a ℓ p.1 p.2) *
        IntMul.stdChar (∑ i, (((tensorIdx a ℓ p.1 p.2 i : ℕ) * (j i : ℕ) : ℕ) : ℝ) /
          (fftShape a ℓ i : ℝ)) := by
  show ((totalLen (fftShape a ℓ) : ℕ) : ℂ)⁻¹ * ∑ j' : Idx (fftShape a ℓ), U j' *
      IntMul.stdChar (∑ i, (((j' i : ℕ) * (j i : ℕ) : ℕ) : ℝ) / (fftShape a ℓ i : ℝ)) = _
  congr 1
  exact ((tensorEquiv a ℓ).sum_comp (fun j' => U j' *
    IntMul.stdChar (∑ i, (((j' i : ℕ) * (j i : ℕ) : ℕ) : ℝ) / (fftShape a ℓ i : ℝ)))).symm

/-- The tensor phase splits into the record-axis phase and the last-axis phase. -/
theorem tensor_phase_split (a : Fin D → ℕ) (ℓ : ℕ) (j : Idx (fftShape a ℓ))
    (y : Cube (addrBits a)) (k : Fin (2 ^ ℓ)) :
    (∑ i, (((tensorIdx a ℓ y k i : ℕ) * (j i : ℕ) : ℕ) : ℝ) / (fftShape a ℓ i : ℝ)) =
      (∑ i : Fin D, ((axisVal a y i * axisVal a (cubeOfIdx a ℓ j) i : ℕ) : ℝ) /
          ((2 : ℝ) ^ a i)) +
        (((k : ℕ) * (coeffOfIdx a ℓ j : ℕ) : ℕ) : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have hden : ((fftShape a ℓ (Fin.castSucc i) : ℕ) : ℝ) = (2 : ℝ) ^ a i := by
      rw [fftShape_castSucc]
      push_cast
      ring
    rw [tensorIdx_castSucc_val, axisVal_cubeOfIdx, hden]
  · have hden : ((fftShape a ℓ (Fin.last D) : ℕ) : ℝ) = ((2 ^ ℓ : ℕ) : ℝ) := by
      rw [fftShape_last]
    rw [tensorIdx_last_val, coeffOfIdx_val, hden]

end Factor

end DirectFFTExactProof

open DirectFFTExactProof

/-- **Encoding** (Section 6 (`sec:direct-fft`)): `toTensor` and `ofTensor` are mutually inverse. -/
theorem tensor_encoding : TensorEncodingStmt := by
  intro D a ℓ
  refine ⟨fun U => ?_, fun z => ?_⟩
  · funext j
    show U (tensorIdx a ℓ (cubeOfIdx a ℓ j) (coeffOfIdx a ℓ j)) = U j
    rw [tensorIdx_cubeOfIdx]
  · funext x k
    show z (cubeOfIdx a ℓ (tensorIdx a ℓ x k)) (coeffOfIdx a ℓ (tensorIdx a ℓ x k)) = z x k
    rw [cubeOfIdx_tensorIdx, coeffOfIdx_tensorIdx]

/-- **DIF** (Section 6.2, eq. (`eq:dif`)): the exact DIF levels `s = 0, …, ℓ-1` followed by
bit reversal compute the normalized positive DFT `F_{2^ℓ}` on every record. -/
theorem dif_exact : DifExactStmt := by
  intro ℓ α z
  funext x k
  exact difAll_bitRev ℓ (z x) k

/-- **Tensor factorization** (Definition 3.2, proof of Theorem 6.5 (`thm:direct-fft`)): under the natural encoding,
`F^+_t` is the record-axis transform composed with the last-axis transform. -/
theorem tensor_factor : TensorFactorStmt := by
  intro D a ℓ U
  funext j
  rw [dftTensor_eq_sum_tensorEquiv]
  show ((2 : ℂ) ^ addrBits a)⁻¹ * ∑ y : Cube (addrBits a),
      dft (2 ^ ℓ) (ofTensor a ℓ U y) (coeffOfIdx a ℓ j) *
        IntMul.stdChar (∑ i : Fin D, ((axisVal a y i * axisVal a (cubeOfIdx a ℓ j) i : ℕ) : ℝ) /
          ((2 : ℝ) ^ a i)) = _
  rw [Finset.mul_sum, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [dft_apply_fin, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hc : ((totalLen (fftShape a ℓ) : ℕ) : ℂ)⁻¹ =
      ((2 : ℂ) ^ addrBits a)⁻¹ * ((2 ^ ℓ : ℕ) : ℂ)⁻¹ := by
    rw [totalLen_fftShape]
    push_cast
    ring
  rw [tensor_phase_split, IntMul.stdChar_add, hc]
  simp only [ofTensor]
  ring

end SubNLogN.Math.Walsh
