import SubNLogN.Math.Walsh.Layout

/-!
# Lemma 6.3: slot/position bookkeeping for the layout `L` and the bit reversal `B`

Paper: Section 6.2 (`sec:direct-fft-layout`), Lemma 6.3 (`lem:walsh-layout`).

Facts about the named-slot lists of `Layout.lean`, for record-axis exponents `a i ∈ {ℓ-1, ℓ}`,
`ℓ ≥ 2` and `K ≥ 1` (the bound `K ≤ ℓ - 1` is not needed here):
* slot `(i, v)`, `v < a i`, is entry `origPos a i v` of the original list `𝒪`
  (`origSlots_getElem?_origPos`); hence `origPos` is a bijection from the valid slots onto `[m₀]`
  (`origPos_lt`, `exists_origPos`);
* every valid slot occurs in `𝒫 ‖ 𝒞` (`mem_newSlots`), which has length `m₀` (`length_newSlots`);
  hence `newPos` is a bijection from the valid slots onto `[m₀]` (`newPos_lt`, `newPos_inj`,
  `exists_newPos`);
* `L` moves slot `(i, v)` from `origPos a i v` to `newPos ℓ K a (i, v)` (`layoutL_origPos`) and is
  bijective (`layoutL_bijective`); `B` moves slot `(i, v)` to the original position of
  `(i, a_i - 1 - v)` (`bitRevB_origPos`).
-/

namespace SubNLogN.Math.Walsh.LayoutSlot

open SubNLogN.Math.Common

variable {D : ℕ}

/-! ## A generic indexing lemma -/

/-- Entry `(total length of the first k blocks) + j` of a `flatMap` is entry `j` of block `k`. -/
theorem getElem?_flatMap_of_lt {α β : Type*} (l : List α) (f : α → List β) {k j : ℕ}
    (hk : k < l.length) (hj : j < (f l[k]).length) :
    (l.flatMap f)[((l.take k).map (fun x => (f x).length)).sum + j]? = (f l[k])[j]? := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x l ih =>
    cases k with
    | zero =>
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatMap_cons,
        List.getElem_cons_zero] at hj ⊢
      exact List.getElem?_append_left hj
    | succ k =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons,
        List.getElem_cons_succ] at hj ⊢
      rw [Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact ih (by simpa using hk) hj

/-! ## The original list `𝒪` -/

theorem length_origSlots (a : Fin D → ℕ) : (origSlots a).length = addrBits a := by
  simp [origSlots, addrBits, List.length_flatMap, List.ofFn_eq_map]

theorem origSlots_getElem?_origPos (a : Fin D → ℕ) {i : Fin D} {v : ℕ} (hv : v < a i) :
    (origSlots a)[origPos a i v]? = some (i, v) := by
  have hk : (i : ℕ) < (List.finRange D).length := by simp
  have hoff : axisOffset a i = (((List.finRange D).take i).map
      (fun x => ((List.range (a x)).reverse.map (fun v => (x, v))).length)).sum := by
    simp [axisOffset, List.ofFn_eq_map]
  unfold origSlots origPos
  rw [hoff, getElem?_flatMap_of_lt (List.finRange D) _ hk (by simp; omega)]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta, List.getElem?_map]
  rw [List.getElem?_reverse (by simp; omega), List.getElem?_range (by simp; omega)]
  simp only [List.length_range, Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

theorem origPos_lt (a : Fin D → ℕ) {i : Fin D} {v : ℕ} (hv : v < a i) :
    origPos a i v < addrBits a := by
  have h := origSlots_getElem?_origPos a hv
  rw [← length_origSlots a]
  exact (List.getElem?_eq_some_iff.1 h).1

theorem exists_origPos (a : Fin D → ℕ) (p : Fin (addrBits a)) :
    ∃ (i : Fin D) (v : ℕ) (hv : v < a i), p = ⟨origPos a i v, origPos_lt a hv⟩ := by
  let φ : (Σ i : Fin D, Fin (a i)) → Fin (addrBits a) :=
    fun s => ⟨origPos a s.1 s.2, origPos_lt a s.2.isLt⟩
  have hinj : Function.Injective φ := by
    rintro ⟨i, v⟩ ⟨i', v'⟩ h
    have h1 := origSlots_getElem?_origPos a v.isLt
    have h2 := origSlots_getElem?_origPos a v'.isLt
    have h3 : origPos a i v = origPos a i' v' := congrArg Fin.val h
    rw [h3, h2] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, h4⟩ := h1
    have : v = v' := Fin.ext h4.symm
    subst this
    rfl
  have hcard : Fintype.card (Σ i : Fin D, Fin (a i)) = Fintype.card (Fin (addrBits a)) := by
    simp [addrBits, List.sum_ofFn]
  obtain ⟨⟨i, v⟩, hs⟩ := ((Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩).2 p
  exact ⟨i, v, v.isLt, hs.symm⟩

/-- `B` moves slot `(i, v)` to the original position of slot `(i, a_i - 1 - v)`. -/
theorem bitRevB_origPos (a : Fin D → ℕ) {i : Fin D} {v : ℕ} (hv : v < a i) :
    (bitRevB a ⟨origPos a i v, origPos_lt a hv⟩ : ℕ) = origPos a i (a i - 1 - v) := by
  simp only [bitRevB, Fin.val_mk, origSlots_getElem?_origPos a hv]
  exact Nat.mod_eq_of_lt (origPos_lt a (by omega))

/-! ## The new list `𝒫 ‖ 𝒞` -/

/-- `J_blk K = ℓ - 1 - b₀` (`b₀ = (ℓ-1) mod K`). -/
theorem layoutJblk_mul (ℓ K : ℕ) : layoutJblk ℓ K * K = ℓ - 1 - layoutB0 ℓ K :=
  Nat.div_mul_cancel (Nat.dvd_sub_mod (ℓ - 1))

/-- Every valid slot `(i, v)`, `v < a i`, occurs in `𝒫 ‖ 𝒞`. -/
theorem mem_newSlots (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 1 ≤ K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) {i : Fin D} {v : ℕ} (hv : v < a i) :
    (i, v) ∈ newSlots ℓ K a := by
  have hvℓ : v ≤ ℓ - 1 := by rcases ha i with h | h <;> omega
  unfold newSlots prefixSlots
  by_cases h1 : v = ℓ - 1
  · have hai : a i = ℓ := by rcases ha i with h | h <;> omega
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    rw [h1]
    exact List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_finRange _, by simp [hai]⟩, rfl⟩
  · by_cases h2 : v < layoutB0 ℓ K
    · refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_flatMap.2 ⟨v, List.mem_reverse.2 (List.mem_range.2 h2),
        List.mem_map.2 ⟨i, List.mem_finRange _, rfl⟩⟩
    · refine List.mem_append_right _ ?_
      have hJ := layoutJblk_mul ℓ K
      have hdm := Nat.div_add_mod' (ℓ - 2 - v) K
      unfold chunkSlots
      refine List.mem_flatMap.2 ⟨(ℓ - 2 - v) / K, List.mem_range.2 ?_,
        List.mem_flatMap.2 ⟨i, List.mem_finRange _,
          List.mem_map.2 ⟨(ℓ - 2 - v) % K, List.mem_range.2 (Nat.mod_lt _ (by omega)), ?_⟩⟩⟩
      · rw [Nat.div_lt_iff_lt_mul (by omega), hJ]
        omega
      · simp only [Prod.mk.injEq, true_and]
        omega

/-- `∑_{i ∈ l} a_i = |l| (ℓ - 1) + #{i ∈ l : a_i = ℓ}` when every `a_i ∈ {ℓ-1, ℓ}`. -/
theorem sum_map_of_two_values (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (a : Fin D → ℕ) (l : List (Fin D))
    (ha : ∀ i ∈ l, a i = ℓ - 1 ∨ a i = ℓ) :
    (l.map a).sum = l.length * (ℓ - 1) + (l.filter (fun i => a i = ℓ)).length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := ha x (by simp)
    have ih' := ih (fun i hi => ha i (by simp [hi]))
    have hmul : (l.length + 1) * (ℓ - 1) = l.length * (ℓ - 1) + (ℓ - 1) := by ring
    by_cases h : a x = ℓ
    · simp only [List.map_cons, List.sum_cons, List.length_cons, List.filter_cons, h,
        decide_true, if_true]
      rw [ih', hmul]
      omega
    · simp only [List.map_cons, List.sum_cons, List.length_cons, List.filter_cons, h,
        decide_false, Bool.false_eq_true, if_false]
      rw [ih', hmul]
      omega

theorem addrBits_eq (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (a : Fin D → ℕ) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) :
    addrBits a = D * (ℓ - 1) + ((List.finRange D).filter (fun i => a i = ℓ)).length := by
  rw [addrBits, List.ofFn_eq_map, sum_map_of_two_values ℓ (by omega) a _ (fun i _ => ha i),
    List.length_finRange]

/-- `|𝒫 ‖ 𝒞| = m₀`. -/
theorem length_newSlots (ℓ K : ℕ) (a : Fin D → ℕ) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) : (newSlots ℓ K a).length = addrBits a := by
  rw [addrBits_eq ℓ hℓ a ha]
  have hJ := layoutJblk_mul ℓ K
  have hb : layoutB0 ℓ K ≤ ℓ - 1 := Nat.mod_le _ _
  have h1 : layoutJblk ℓ K * (D * K) = D * (ℓ - 1) - D * layoutB0 ℓ K := by
    rw [show layoutJblk ℓ K * (D * K) = D * (layoutJblk ℓ K * K) by ring, hJ, Nat.mul_sub]
  have h2 : D * layoutB0 ℓ K ≤ D * (ℓ - 1) := Nat.mul_le_mul_left _ hb
  have h3 : layoutB0 ℓ K * D = D * layoutB0 ℓ K := Nat.mul_comm _ _
  simp only [newSlots, prefixSlots, chunkSlots, List.length_append, List.length_map,
    List.length_flatMap, List.length_reverse, List.length_range, List.length_finRange,
    List.map_const', List.sum_replicate, smul_eq_mul]
  omega

theorem newPos_lt (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 1 ≤ K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) {i : Fin D} {v : ℕ} (hv : v < a i) :
    newPos ℓ K a (i, v) < addrBits a := by
  rw [← length_newSlots ℓ K a hℓ ha]
  exact List.idxOf_lt_length_of_mem (mem_newSlots ℓ K a hK hℓ ha hv)

theorem newPos_inj (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 1 ≤ K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) {i i' : Fin D} {v v' : ℕ} (hv : v < a i)
    (hv' : v' < a i') (h : newPos ℓ K a (i, v) = newPos ℓ K a (i', v')) : i = i' ∧ v = v' := by
  have _ := hv'
  have h' : (i, v) = (i', v') := (List.idxOf_inj (mem_newSlots ℓ K a hK hℓ ha hv)).1 h
  exact Prod.mk.inj h'

theorem exists_newPos (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 1 ≤ K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (p : Fin (addrBits a)) :
    ∃ (i : Fin D) (v : ℕ), v < a i ∧ newPos ℓ K a (i, v) = (p : ℕ) := by
  let φ : (Σ i : Fin D, Fin (a i)) → Fin (addrBits a) :=
    fun s => ⟨newPos ℓ K a (s.1, s.2), newPos_lt ℓ K a hK hℓ ha s.2.isLt⟩
  have hinj : Function.Injective φ := by
    rintro ⟨i, v⟩ ⟨i', v'⟩ h
    obtain ⟨rfl, h2⟩ := newPos_inj ℓ K a hK hℓ ha v.isLt v'.isLt (congrArg Fin.val h)
    have : v = v' := Fin.ext h2
    subst this
    rfl
  have hcard : Fintype.card (Σ i : Fin D, Fin (a i)) = Fintype.card (Fin (addrBits a)) := by
    simp [addrBits, List.sum_ofFn]
  obtain ⟨⟨i, v⟩, hs⟩ := ((Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩).2 p
  exact ⟨i, v, v.isLt, congrArg Fin.val hs⟩

/-! ## The positional maps `L` and `B` -/

/-- `L` moves slot `(i, v)` from its original position to its position in `𝒫 ‖ 𝒞`. -/
theorem layoutL_origPos (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 1 ≤ K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) {i : Fin D} {v : ℕ} (hv : v < a i) :
    (layoutL ℓ K a ⟨origPos a i v, origPos_lt a hv⟩ : ℕ) = newPos ℓ K a (i, v) := by
  simp only [layoutL, Fin.val_mk, origSlots_getElem?_origPos a hv]
  exact Nat.mod_eq_of_lt (newPos_lt ℓ K a hK hℓ ha hv)

/-- `L` is a permutation of the `m₀` positions. -/
theorem layoutL_bijective (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 1 ≤ K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) : Function.Bijective (layoutL ℓ K a) := by
  refine Finite.injective_iff_bijective.1 ?_
  intro p q hpq
  obtain ⟨i, v, hv, rfl⟩ := exists_origPos a p
  obtain ⟨i', v', hv', rfl⟩ := exists_origPos a q
  have h := congrArg Fin.val hpq
  rw [layoutL_origPos ℓ K a hK hℓ ha hv, layoutL_origPos ℓ K a hK hℓ ha hv'] at h
  obtain ⟨rfl, rfl⟩ := newPos_inj ℓ K a hK hℓ ha hv hv' h
  rfl

end SubNLogN.Math.Walsh.LayoutSlot
