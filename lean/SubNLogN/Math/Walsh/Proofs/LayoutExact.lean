import SubNLogN.Math.Walsh.Layout
import SubNLogN.Math.Walsh.Proofs.LayoutRelocate

/-!
# Lemma 6.3, exact counterpart of the layout rounds (`WalshLayoutExactStmt`)

Paper: Sections 6.2–6.3 (`sec:direct-fft-layout`–`sec:direct-fft-twiddle`): DIF step eq. (`eq:dif`),
Lemma 6.3 (`lem:walsh-layout`), and combined twiddle eq. (`eq:combined-round`).

We prove `walsh_layout_exact : WalshLayoutExactStmt`, i.e. `exactRounds (L z) = L (B (F_{t<d} z))`.

Proof. Everything is read in the physical layout `L` (no separate conjugation lemma is needed). For
`v₀ ≤ ℓ` let `done(v₀)` be the set of physical positions `newPos (i, v)` of the named slots with
`v₀ ≤ v < a_i`, and define the closed form (`stateL`)
`S_{v₀} w (x) = 2^{-|done(v₀)|} ∑_{y =_{done(v₀)^c} x} e(∑_i rev_{v₀}(x, i) j_i(y) / 2^{a_i}) w(y)`,
where `j_i(y) = ∑_{v < a_i} 2^v y_{(i,v)}` (`jL`) and `rev_{v₀}(x, i) = ∑_{v₀ ≤ v < a_i} 2^{a_i-1-v}
x_{(i,v)}` (`revL`), all bits read at the physical positions of the named slots. Then
* `S_ℓ w = w` (`stateL_top`: no slot is processed since `a_i ≤ ℓ`);
* `exactRound v (S_{v+1} w) = S_v w` for `v < ℓ` (`exactRound_stateL`): the `H`-sum of round `v` and
  the sum of `S_{v+1}` merge into one sum over `done(v) = roundSet v ⊔ done(v+1)`, and on every axis
  `e(b j^{<v} / 2^{v+1}) (-1)^{b c} e(rev_{v+1} j / 2^{a_i}) = e(rev_v j / 2^{a_i})`, which is the DIF
  step `(dif)` (`axis_identity`); all axes are treated at once (no tensoring is needed);
* `S_0 (L z) = L (B (F z))` (`stateL_zero`): `done(0)` is every position, and the substitution
  `y' = y ∘ L` turns `j_i(y)` into `j_i(y')` and `rev_0(x, i)` into `j_i(x ∘ L ∘ B)`.
The slot bookkeeping (positions of the named slots in `𝒪` and in `𝒫 ‖ 𝒞`, bijectivity of `L`) is
imported from `SubNLogN.Math.Walsh.Proofs.LayoutRelocate` (namespace `LayoutSlot`).
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

namespace LayoutExactProof

/-! ## Generic helpers -/

/-- `e(∑ f) = ∏ e(f)`. -/
theorem stdChar_sum {ι : Type} (s : Finset ι) (f : ι → ℝ) :
    IntMul.stdChar (∑ i ∈ s, f i) = ∏ i ∈ s, IntMul.stdChar (f i) := by
  unfold IntMul.stdChar
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

/-- `e(1/2) = -1`. -/
theorem stdChar_half : IntMul.stdChar (1 / 2) = -1 := by
  unfold IntMul.stdChar
  rw [show ((2 * Real.pi * (1 / 2) : ℝ) : ℂ) * Complex.I = Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- Reducing the numerator modulo `N` does not change `e(S / N)`. -/
theorem stdChar_natMod_div (S N : ℕ) (hN : 0 < N) :
    IntMul.stdChar (((S % N : ℕ) : ℝ) / (N : ℝ)) = IntMul.stdChar ((S : ℝ) / (N : ℝ)) := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have h : (S : ℝ) / N = ((S % N : ℕ) : ℝ) / N + (((S / N : ℕ) : ℤ) : ℝ) := by
    rw [Int.cast_natCast, eq_comm, div_add' _ _ _ hN', div_left_inj' hN']
    exact_mod_cast Nat.mod_add_div' S N
  rw [h, IntMul.stdChar_add_int]

/-- `(-1)^{#{i | Q i}} = ∏_i (if Q i then -1 else 1)`. -/
theorem neg_one_pow_card_filter {ι : Type} [Fintype ι] (Q : ι → Prop) [DecidablePred Q] :
    (-1 : ℂ) ^ (Finset.univ.filter Q).card = ∏ i, (if Q i then (-1 : ℂ) else 1) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-- Merging two nested sums over addresses agreeing with `x` off `T`, resp. with `y'` off `T₁`
(`T`, `T₁` disjoint), into one sum over the addresses agreeing with `x` off `T ∪ T₁`; the outer
address is recovered as `y` on `T` and `x` elsewhere. -/
theorem sum_sum_merge {m : ℕ} (T T₁ : Finset (Fin m)) (hdisj : Disjoint T T₁) (x : Cube m)
    (F : Cube m → Cube m → ℂ) :
    ∑ y' ∈ Finset.univ.filter (fun y' : Cube m => ∀ j, j ∉ T → y' j = x j),
      ∑ y ∈ Finset.univ.filter (fun y : Cube m => ∀ p, p ∉ T₁ → y p = y' p), F y' y =
    ∑ y ∈ Finset.univ.filter (fun y : Cube m => ∀ p, p ∉ T ∪ T₁ → y p = x p),
      F (fun p => if p ∈ T then y p else x p) y := by
  rw [Finset.sum_comm' (t' := Finset.univ.filter (fun y : Cube m => ∀ p, p ∉ T ∪ T₁ → y p = x p))
    (s' := fun y => {fun p => if p ∈ T then y p else x p})]
  · apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_singleton]
  · intro y' y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Finset.mem_union, not_or]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · funext p
        by_cases hp : p ∈ T
        · rw [if_pos hp]
          exact (h2 p (Finset.disjoint_left.1 hdisj hp)).symm
        · rw [if_neg hp]
          exact h1 p hp
      · intro p hp
        rw [h2 p hp.2, h1 p hp.1]
    · rintro ⟨rfl, h⟩
      refine ⟨fun j hj => by simp [hj], fun p hp => ?_⟩
      by_cases hpT : p ∈ T
      · simp [hpT]
      · simp only [if_neg hpT]
        exact h p ⟨hpT, hp⟩

/-- On `T` the merged address is `y`. -/
theorem sign_merge {m : ℕ} (T : Finset (Fin m)) (x y : Cube m) :
    T.filter (fun j => x j = true ∧ (if j ∈ T then y j else x j) = true) =
      T.filter (fun j => x j = true ∧ y j = true) := by
  apply Finset.filter_congr
  intro j hj
  rw [if_pos hj]

/-! ## Standing hypotheses, closed-form state -/

/-- The hypotheses of Lemma 6.3 used here (`K ≤ ℓ - 1` is not needed). -/
structure Hyp {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) : Prop where
  hK : 1 ≤ K
  hℓ : 2 ≤ ℓ
  ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ

variable {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ)

/-- The index `j_i(x) = ∑_{v < a_i} 2^v x_{(i,v)}`, bits read at the layout-`L` positions. -/
def jL (x : Cube (addrBits a)) (i : Fin D) : ℕ :=
  ∑ v ∈ Finset.range (a i), if cubeBit x (newPos ℓ K a (i, v)) = true then 2 ^ v else 0

/-- The partially reversed frequency `rev_{v₀}(x, i) = ∑_{v₀ ≤ v < a_i} 2^{a_i-1-v} x_{(i,v)}`. -/
def revL (v₀ : ℕ) (x : Cube (addrBits a)) (i : Fin D) : ℕ :=
  ∑ v ∈ Finset.Ico v₀ (a i), if cubeBit x (newPos ℓ K a (i, v)) = true then 2 ^ (a i - 1 - v) else 0

/-- The physical positions of the slots `(i, v)` with `v₀ ≤ v < a_i` (processed by the rounds at
named slots `ℓ-1, …, v₀`). -/
def doneSet (v₀ : ℕ) : Finset (Fin (addrBits a)) :=
  Finset.univ.filter (fun p => ∃ i : Fin D, ∃ v ∈ Finset.Ico v₀ (a i), newPos ℓ K a (i, v) = (p : ℕ))

/-- The phase `e(∑_i rev_{v₀}(x, i) j_i(y) / 2^{a_i})`, as a product over the axes. -/
noncomputable def phL (v₀ : ℕ) (x y : Cube (addrBits a)) : ℂ :=
  ∏ i : Fin D, IntMul.stdChar (((revL ℓ K a v₀ x i * jL ℓ K a y i : ℕ) : ℝ) / (2 : ℝ) ^ a i)

/-- The closed form of the state after the rounds at named slots `ℓ-1, …, v₀` (input `w`, already in
layout `L`). -/
noncomputable def stateL (v₀ : ℕ) {r : ℕ} (w : RArr (Cube (addrBits a)) r) :
    RArr (Cube (addrBits a)) r :=
  fun x k => ((2 : ℂ) ^ (doneSet ℓ K a v₀).card)⁻¹ *
    ∑ y ∈ Finset.univ.filter (fun y : Cube (addrBits a) => ∀ p, p ∉ doneSet ℓ K a v₀ → y p = x p),
      phL ℓ K a v₀ x y * w y k

/-- The summand of axis `i` in the twiddle index `twJ`. -/
def twTerm (v : ℕ) (x : Cube (addrBits a)) (i : Fin D) : ℕ :=
  if v < a i ∧ cubeBit x (newPos ℓ K a (i, v)) = true then
    2 ^ (ℓ - v - 1) *
      ∑ b ∈ Finset.range v, (if cubeBit x (newPos ℓ K a (i, b)) = true then 2 ^ b else 0)
  else 0

/-- The butterfly sign of axis `i` in round `v`. -/
noncomputable def sgnTerm (v : ℕ) (x y : Cube (addrBits a)) (i : Fin D) : ℂ :=
  if v < a i ∧ cubeBit x (newPos ℓ K a (i, v)) = true ∧ cubeBit y (newPos ℓ K a (i, v)) = true
  then -1 else 1

/-! ## Processed positions -/

variable {ℓ K a}

theorem nlt (H : Hyp ℓ K a) {i : Fin D} {v : ℕ} (hv : v < a i) : newPos ℓ K a (i, v) < addrBits a :=
  LayoutSlot.newPos_lt ℓ K a H.hK H.hℓ H.ha hv

theorem ninj (H : Hyp ℓ K a) {i i' : Fin D} {v v' : ℕ} (hv : v < a i) (hv' : v' < a i')
    (h : newPos ℓ K a (i, v) = newPos ℓ K a (i', v')) : i = i' ∧ v = v' :=
  LayoutSlot.newPos_inj ℓ K a H.hK H.hℓ H.ha hv hv' h

theorem mem_doneSet {v₀ : ℕ} {p : Fin (addrBits a)} :
    p ∈ doneSet ℓ K a v₀ ↔ ∃ i : Fin D, ∃ v, v₀ ≤ v ∧ v < a i ∧ newPos ℓ K a (i, v) = (p : ℕ) := by
  simp [doneSet, Finset.mem_Ico, and_assoc]

theorem mem_roundSet {v : ℕ} {p : Fin (addrBits a)} :
    p ∈ roundSet ℓ K a v ↔ ∃ i : Fin D, v < a i ∧ newPos ℓ K a (i, v) = (p : ℕ) := by
  simp [roundSet]

theorem newPos_mem_roundSet (H : Hyp ℓ K a) {i : Fin D} {v' : ℕ} (hv' : v' < a i) (v : ℕ) :
    (⟨newPos ℓ K a (i, v'), nlt H hv'⟩ : Fin (addrBits a)) ∈ roundSet ℓ K a v ↔ v' = v := by
  rw [mem_roundSet]
  constructor
  · rintro ⟨i', h1, h2⟩
    exact (ninj H h1 hv' h2).2.symm
  · rintro rfl
    exact ⟨i, hv', rfl⟩

theorem newPos_mem_doneSet (H : Hyp ℓ K a) {i : Fin D} {v' : ℕ} (hv' : v' < a i) (v₀ : ℕ) :
    (⟨newPos ℓ K a (i, v'), nlt H hv'⟩ : Fin (addrBits a)) ∈ doneSet ℓ K a v₀ ↔ v₀ ≤ v' := by
  rw [mem_doneSet]
  constructor
  · rintro ⟨i', v'', h1, h2, h3⟩
    obtain ⟨-, rfl⟩ := ninj H h2 hv' h3
    exact h1
  · intro h
    exact ⟨i, v', h, hv', rfl⟩

theorem doneSet_eq_union (v : ℕ) :
    doneSet ℓ K a v = roundSet ℓ K a v ∪ doneSet ℓ K a (v + 1) := by
  ext p
  rw [Finset.mem_union, mem_doneSet, mem_roundSet, mem_doneSet]
  constructor
  · rintro ⟨i, v', h1, h2, h3⟩
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h
      exact Or.inl ⟨i, h2, h3⟩
    · exact Or.inr ⟨i, v', h, h2, h3⟩
  · rintro (⟨i, h2, h3⟩ | ⟨i, v', h1, h2, h3⟩)
    · exact ⟨i, v, le_rfl, h2, h3⟩
    · exact ⟨i, v', by omega, h2, h3⟩

theorem disjoint_roundSet_doneSet (H : Hyp ℓ K a) (v : ℕ) :
    Disjoint (roundSet ℓ K a v) (doneSet ℓ K a (v + 1)) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨i, h2, h3⟩ := mem_roundSet.1 hp
  obtain ⟨i', v', h1, h2', h3'⟩ := mem_doneSet.1 hq
  obtain ⟨-, rfl⟩ := ninj H h2 h2' (h3.trans h3'.symm)
  omega

theorem doneSet_top (H : Hyp ℓ K a) : doneSet ℓ K a ℓ = ∅ := by
  ext p
  simp only [Finset.notMem_empty, iff_false]
  rw [mem_doneSet]
  rintro ⟨i, v, h1, h2, -⟩
  have := H.ha i
  omega

theorem doneSet_zero (H : Hyp ℓ K a) : doneSet ℓ K a 0 = Finset.univ := by
  ext p
  simp only [Finset.mem_univ, iff_true]
  rw [mem_doneSet]
  obtain ⟨i, v, hv, hp⟩ := LayoutSlot.exists_newPos ℓ K a H.hK H.hℓ H.ha p
  exact ⟨i, v, Nat.zero_le _, hv, hp⟩

/-- Off `done(v)` the two addresses agree, in particular on the slots `(i, b)`, `b < v`. -/
theorem cubeBit_agree (H : Hyp ℓ K a) {v : ℕ} {x y : Cube (addrBits a)}
    (hy : ∀ p, p ∉ doneSet ℓ K a v → y p = x p) {i : Fin D} {b : ℕ} (hb : b < a i)
    (hbv : b < v) : cubeBit y (newPos ℓ K a (i, b)) = cubeBit x (newPos ℓ K a (i, b)) := by
  rw [cubeBit_of_lt y (nlt H hb), cubeBit_of_lt x (nlt H hb)]
  apply hy
  rw [newPos_mem_doneSet H hb]
  omega

/-- `rev_{v+1}` does not read the positions of round `v`. -/
theorem revL_merge (H : Hyp ℓ K a) (v : ℕ) (x y : Cube (addrBits a)) (i : Fin D) :
    revL ℓ K a (v + 1) (fun p => if p ∈ roundSet ℓ K a v then y p else x p) i =
      revL ℓ K a (v + 1) x i := by
  unfold revL
  apply Finset.sum_congr rfl
  intro v' hv'
  rw [Finset.mem_Ico] at hv'
  have hn : (⟨newPos ℓ K a (i, v'), nlt H hv'.2⟩ : Fin (addrBits a)) ∉ roundSet ℓ K a v := by
    rw [newPos_mem_roundSet H hv'.2]
    omega
  rw [cubeBit_of_lt _ (nlt H hv'.2), cubeBit_of_lt x (nlt H hv'.2), if_neg hn]

theorem phL_merge (H : Hyp ℓ K a) (v : ℕ) (x y : Cube (addrBits a)) :
    phL ℓ K a (v + 1) (fun p => if p ∈ roundSet ℓ K a v then y p else x p) y =
      phL ℓ K a (v + 1) x y := by
  unfold phL
  apply Finset.prod_congr rfl
  intro i _
  rw [revL_merge H]

/-- The butterfly sign of round `v` as a count over the participating axes. -/
theorem card_sign_filter (H : Hyp ℓ K a) (v : ℕ) (x y : Cube (addrBits a)) :
    ((roundSet ℓ K a v).filter (fun j => x j = true ∧ y j = true)).card =
      (Finset.univ.filter (fun i : Fin D => v < a i ∧ cubeBit x (newPos ℓ K a (i, v)) = true ∧
        cubeBit y (newPos ℓ K a (i, v)) = true)).card := by
  symm
  refine Finset.card_bij (fun i hi => (⟨newPos ℓ K a (i, v),
    nlt H (Finset.mem_filter.1 hi).2.1⟩ : Fin (addrBits a))) ?_ ?_ ?_
  · intro i hi
    obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hi
    rw [Finset.mem_filter]
    refine ⟨(newPos_mem_roundSet H h1 v).2 rfl, ?_, ?_⟩
    · rwa [cubeBit_of_lt x (nlt H h1)] at h2
    · rwa [cubeBit_of_lt y (nlt H h1)] at h3
  · intro i hi i' hi' h
    exact (ninj H (Finset.mem_filter.1 hi).2.1 (Finset.mem_filter.1 hi').2.1
      (congrArg Fin.val h)).1
  · intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := Finset.mem_filter.1 hp
    obtain ⟨i, hi, hip⟩ := mem_roundSet.1 hp1
    have he : (⟨newPos ℓ K a (i, v), nlt H hi⟩ : Fin (addrBits a)) = p := Fin.ext hip
    refine ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi, ?_, ?_⟩, he⟩
    · rw [cubeBit_of_lt x (nlt H hi), he]
      exact hp2
    · rw [cubeBit_of_lt y (nlt H hi), he]
      exact hp3

/-! ## The phase identity of one round (eq. (`eq:dif`)) -/

/-- The combined twiddle `θ_{2J(x)}` as a product of per-axis phases. -/
theorem theta_twJ (v : ℕ) (x : Cube (addrBits a)) :
    theta (2 ^ ℓ) (2 * twJ ℓ K a v x) =
      ∏ i : Fin D, IntMul.stdChar (((twTerm ℓ K a v x i : ℕ) : ℝ) / (2 : ℝ) ^ ℓ) := by
  unfold theta
  have e1 : (((2 * twJ ℓ K a v x : ℕ) : ℝ) / (2 * ((2 ^ ℓ : ℕ) : ℝ))) =
      ((twJ ℓ K a v x : ℕ) : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, mul_div_mul_left _ _ two_ne_zero]
  rw [e1, show twJ ℓ K a v x = (∑ i, twTerm ℓ K a v x i) % 2 ^ ℓ from rfl,
    stdChar_natMod_div _ _ (by positivity), Nat.cast_sum, Finset.sum_div, stdChar_sum]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- `j_i(y) = j_i^{<v}(y) + 2^v y_{(i,v)} + 2^{v+1} M`. -/
theorem jL_split (y : Cube (addrBits a)) (i : Fin D) {v : ℕ} (hv : v < a i) :
    ∃ M : ℕ, jL ℓ K a y i =
      (∑ b ∈ Finset.range v, if cubeBit y (newPos ℓ K a (i, b)) = true then 2 ^ b else 0) +
        (if cubeBit y (newPos ℓ K a (i, v)) = true then 2 ^ v else 0) + 2 ^ (v + 1) * M := by
  have hdvd : 2 ^ (v + 1) ∣ ∑ b ∈ Finset.Ico (v + 1) (a i),
      (if cubeBit y (newPos ℓ K a (i, b)) = true then 2 ^ b else 0) := by
    apply Finset.dvd_sum
    intro b hb
    rw [Finset.mem_Ico] at hb
    split_ifs
    · exact pow_dvd_pow 2 hb.1
    · exact dvd_zero _
  obtain ⟨M, hM⟩ := hdvd
  refine ⟨M, ?_⟩
  unfold jL
  rw [← Finset.sum_range_add_sum_Ico _ (show v + 1 ≤ a i by omega), Finset.sum_range_succ, hM]

/-- The scalar identity behind one DIF step on one axis: with `jy = J + c 2^v + 2^{v+1} M`,
`e(2^{ℓ-v-1} J / 2^ℓ) (-1)^c e(R' jy / 2^A) = e((2^{A-1-v} + R') jy / 2^A)`. -/
theorem axis_identity (ℓ A v J R' jy M : ℕ) (c : Bool) (hvA : v < A) (hvℓ : v < ℓ)
    (hjy : jy = J + (if c = true then 2 ^ v else 0) + 2 ^ (v + 1) * M) :
    IntMul.stdChar (((2 ^ (ℓ - v - 1) * J : ℕ) : ℝ) / (2 : ℝ) ^ ℓ) *
        (if c = true then (-1 : ℂ) else 1) *
        IntMul.stdChar (((R' * jy : ℕ) : ℝ) / (2 : ℝ) ^ A) =
      IntMul.stdChar ((((2 ^ (A - 1 - v) + R') * jy : ℕ) : ℝ) / (2 : ℝ) ^ A) := by
  subst hjy
  have key : ((((2 ^ (A - 1 - v) + R') * (J + (if c = true then 2 ^ v else 0) +
      2 ^ (v + 1) * M) : ℕ) : ℝ) / (2 : ℝ) ^ A) =
      ((2 ^ (ℓ - v - 1) * J : ℕ) : ℝ) / (2 : ℝ) ^ ℓ + (if c = true then (1 / 2 : ℝ) else 0) +
        ((R' * (J + (if c = true then 2 ^ v else 0) + 2 ^ (v + 1) * M) : ℕ) : ℝ) / (2 : ℝ) ^ A +
        ((M : ℤ) : ℝ) := by
    have hA : (2 : ℝ) ^ A = 2 ^ (A - 1 - v) * (2 ^ v * 2) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      omega
    have hL : (2 : ℝ) ^ ℓ = 2 ^ (ℓ - v - 1) * (2 ^ v * 2) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      omega
    have h1 : (0 : ℝ) < 2 ^ v := by positivity
    have h2 : (0 : ℝ) < 2 ^ (A - 1 - v) := by positivity
    have h3 : (0 : ℝ) < 2 ^ (ℓ - v - 1) := by positivity
    rw [hA, hL]
    split_ifs with hc
    · push_cast
      rw [pow_succ]
      field_simp
      ring
    · push_cast
      rw [pow_succ]
      field_simp
      ring
  have hs : IntMul.stdChar (if c = true then (1 / 2 : ℝ) else 0) =
      if c = true then (-1 : ℂ) else 1 := by
    split_ifs
    · exact stdChar_half
    · exact IntMul.stdChar_zero
  rw [key, IntMul.stdChar_add_int, IntMul.stdChar_add, IntMul.stdChar_add, hs]

/-- One DIF step on axis `i` (eq. (`eq:dif`)): the twiddle, the butterfly sign and the phase of
`S_{v+1}` combine to the phase of `S_v`. -/
theorem axis_step {v : ℕ} (hv : v < ℓ) (x y : Cube (addrBits a)) (i : Fin D)
    (hy : ∀ b, b < v → b < a i →
      cubeBit y (newPos ℓ K a (i, b)) = cubeBit x (newPos ℓ K a (i, b))) :
    IntMul.stdChar (((twTerm ℓ K a v x i : ℕ) : ℝ) / (2 : ℝ) ^ ℓ) * sgnTerm ℓ K a v x y i *
        IntMul.stdChar (((revL ℓ K a (v + 1) x i * jL ℓ K a y i : ℕ) : ℝ) / (2 : ℝ) ^ a i) =
      IntMul.stdChar (((revL ℓ K a v x i * jL ℓ K a y i : ℕ) : ℝ) / (2 : ℝ) ^ a i) := by
  by_cases hva : v < a i
  · have hrev : revL ℓ K a v x i =
        (if cubeBit x (newPos ℓ K a (i, v)) = true then 2 ^ (a i - 1 - v) else 0) +
          revL ℓ K a (v + 1) x i := by
      unfold revL
      rw [Finset.sum_eq_sum_Ico_succ_bot hva]
    rw [hrev]
    unfold twTerm sgnTerm
    by_cases hx : cubeBit x (newPos ℓ K a (i, v)) = true
    · obtain ⟨M, hM⟩ := jL_split y i hva
      have hJ : (∑ b ∈ Finset.range v,
          if cubeBit y (newPos ℓ K a (i, b)) = true then 2 ^ b else 0) =
          ∑ b ∈ Finset.range v, if cubeBit x (newPos ℓ K a (i, b)) = true then 2 ^ b else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.mem_range] at hb
        rw [hy b hb (by omega)]
      rw [hJ] at hM
      simp only [hva, hx, true_and, if_true]
      exact axis_identity ℓ (a i) v _ _ _ M _ hva hv hM
    · simp [hx]
  · have h1 : ∀ v₀, v ≤ v₀ → revL ℓ K a v₀ x i = 0 := by
      intro v₀ hv₀
      unfold revL
      rw [Finset.Ico_eq_empty_of_le (by omega)]
      rfl
    unfold twTerm sgnTerm
    rw [h1 v le_rfl, h1 (v + 1) (by omega)]
    simp [hva]

/-- The phase identity of round `v`: `θ_{2J(x)} (-1)^{#…} φ_{v+1}(x, y) = φ_v(x, y)` for every `y`
agreeing with `x` off `done(v)`. -/
theorem phase_step (H : Hyp ℓ K a) {v : ℕ} (hv : v < ℓ) (x y : Cube (addrBits a))
    (hy : ∀ p, p ∉ doneSet ℓ K a v → y p = x p) :
    theta (2 ^ ℓ) (2 * twJ ℓ K a v x) *
      ((-1 : ℂ) ^ ((roundSet ℓ K a v).filter (fun j => x j = true ∧ y j = true)).card *
        phL ℓ K a (v + 1) x y) = phL ℓ K a v x y := by
  rw [theta_twJ, card_sign_filter H, neg_one_pow_card_filter]
  unfold phL
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← mul_assoc]
  exact axis_step hv x y i (fun b hb hba => cubeBit_agree H hy hba hb)

/-! ## One round, all rounds -/

/-- **One round**: `exactRound v (S_{v+1} w) = S_v w` for `v < ℓ`. -/
theorem exactRound_stateL (H : Hyp ℓ K a) {v : ℕ} (hv : v < ℓ) {r : ℕ}
    (w : RArr (Cube (addrBits a)) r) :
    exactRound ℓ K a v (stateL ℓ K a (v + 1) w) = stateL ℓ K a v w := by
  funext x k
  have hdisj := disjoint_roundSet_doneSet H v
  have hcard : (doneSet ℓ K a v).card =
      (roundSet ℓ K a v).card + (doneSet ℓ K a (v + 1)).card := by
    rw [doneSet_eq_union v, Finset.card_union_of_disjoint hdisj]
  simp only [exactRound, diagArr, hT, stateL, Finset.mul_sum]
  rw [sum_sum_merge _ _ hdisj x, ← doneSet_eq_union v]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mem_filter] at hy
  beta_reduce
  rw [sign_merge, phL_merge H, hcard, pow_add, mul_inv, ← phase_step H hv x y hy.2]
  ring

/-- After the rounds at named slots `n-1, …, 0` the state `S_n w` becomes `S_0 w`. -/
theorem foldl_stateL (H : Hyp ℓ K a) {r : ℕ} (w : RArr (Cube (addrBits a)) r) :
    ∀ n, n ≤ ℓ → (List.range n).reverse.foldl (fun w' v => exactRound ℓ K a v w')
      (stateL ℓ K a n w) = stateL ℓ K a 0 w
  | 0, _ => rfl
  | n + 1, hn => by
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.foldl_cons, exactRound_stateL H (by omega)]
      exact foldl_stateL H w n (by omega)

/-- `S_ℓ w = w`. -/
theorem stateL_top (H : Hyp ℓ K a) {r : ℕ} (w : RArr (Cube (addrBits a)) r) :
    stateL ℓ K a ℓ w = w := by
  funext x k
  unfold stateL
  rw [doneSet_top H]
  have hfilt : Finset.univ.filter (fun y : Cube (addrBits a) =>
      ∀ p, p ∉ (∅ : Finset (Fin (addrBits a))) → y p = x p) = {x} := by
    ext y
    simp [funext_iff]
  rw [hfilt, Finset.sum_singleton]
  have hph : phL ℓ K a ℓ x x = 1 := by
    unfold phL
    apply Finset.prod_eq_one
    intro i _
    have hrev : revL ℓ K a ℓ x i = 0 := by
      unfold revL
      rw [Finset.Ico_eq_empty_of_le (by rcases H.ha i with h | h <;> omega)]
      rfl
    rw [hrev]
    simp
  rw [hph]
  simp

/-! ## The final substitution -/

theorem jL_eq_axisVal (H : Hyp ℓ K a) (y : Cube (addrBits a)) (i : Fin D) :
    jL ℓ K a y i = axisVal a (fun j => y (layoutL ℓ K a j)) i := by
  unfold jL axisVal
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.mem_range] at hv
  have hL : layoutL ℓ K a ⟨origPos a i v, LayoutSlot.origPos_lt a hv⟩ =
      ⟨newPos ℓ K a (i, v), nlt H hv⟩ :=
    Fin.ext (LayoutSlot.layoutL_origPos ℓ K a H.hK H.hℓ H.ha hv)
  rw [cubeBit_of_lt _ (LayoutSlot.origPos_lt a hv), hL, cubeBit_of_lt y (nlt H hv)]

theorem revL_zero_eq_axisVal (H : Hyp ℓ K a) (x : Cube (addrBits a)) (i : Fin D) :
    revL ℓ K a 0 x i = axisVal a (fun j => x (layoutL ℓ K a (bitRevB a j))) i := by
  unfold revL axisVal
  rw [← Finset.range_eq_Ico]
  conv_lhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.mem_range] at hv
  have hv' : a i - 1 - v < a i := by omega
  have hB : bitRevB a ⟨origPos a i v, LayoutSlot.origPos_lt a hv⟩ =
      ⟨origPos a i (a i - 1 - v), LayoutSlot.origPos_lt a hv'⟩ :=
    Fin.ext (LayoutSlot.bitRevB_origPos a hv)
  have hL : layoutL ℓ K a ⟨origPos a i (a i - 1 - v), LayoutSlot.origPos_lt a hv'⟩ =
      ⟨newPos ℓ K a (i, a i - 1 - v), nlt H hv'⟩ :=
    Fin.ext (LayoutSlot.layoutL_origPos ℓ K a H.hK H.hℓ H.ha hv')
  rw [cubeBit_of_lt _ (LayoutSlot.origPos_lt a hv), hB, hL, cubeBit_of_lt x (nlt H hv'),
    show a i - 1 - (a i - 1 - v) = v by omega]

/-- `S_0 (L z) = L (B (F_{t<d} z))`. -/
theorem stateL_zero (H : Hyp ℓ K a) {r : ℕ} (z : RArr (Cube (addrBits a)) r) :
    stateL ℓ K a 0 (posPermArr (layoutL ℓ K a) z) =
      posPermArr (layoutL ℓ K a) (posPermArr (bitRevB a) (recordDFT a z)) := by
  funext x k
  have hbij := LayoutSlot.layoutL_bijective ℓ K a H.hK H.hℓ H.ha
  simp only [stateL, posPermArr, recordDFT]
  rw [doneSet_zero H, Finset.card_univ, Fintype.card_fin]
  have hfilt : Finset.univ.filter (fun y : Cube (addrBits a) =>
      ∀ p, p ∉ (Finset.univ : Finset (Fin (addrBits a))) → y p = x p) = Finset.univ := by
    ext y
    simp
  rw [hfilt]
  congr 1
  refine Fintype.sum_bijective (fun y : Cube (addrBits a) => fun j => y (layoutL ℓ K a j))
    hbij.comp_right _ _ ?_
  intro y
  rw [mul_comm (phL ℓ K a 0 x y)]
  congr 1
  unfold phL
  rw [stdChar_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [jL_eq_axisVal H, revL_zero_eq_axisVal H, Nat.mul_comm]

end LayoutExactProof

/-- **Lemma 6.3, exact counterpart** (`lem:walsh-layout`): the exact DIF
rounds executed in layout `L` on input in the original order compute `L B F^+_{t_{<d}}`. -/
theorem walsh_layout_exact : WalshLayoutExactStmt := by
  unfold WalshLayoutExactStmt
  intro D ℓ K a hK _ hℓ ha r z
  have H : LayoutExactProof.Hyp ℓ K a := ⟨hK, hℓ, ha⟩
  have h := LayoutExactProof.foldl_stateL H (posPermArr (layoutL ℓ K a) z) ℓ le_rfl
  rw [LayoutExactProof.stateL_top H] at h
  unfold exactRounds
  rw [h, LayoutExactProof.stateL_zero H]

end SubNLogN.Math.Walsh
