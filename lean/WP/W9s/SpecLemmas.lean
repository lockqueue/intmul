import WP.W9s.SpecDefs

/-!
# WP.W9s.SpecLemmas — list/array helper lemmas for `WP.W9s.SpecMath` (W9s piece [a])

All in `WP.W9s.SM`: `evensL`/`oddsL`; `getD` on arrays, `Array.ofFn` and `List.map Array.toList`;
`rotL`, `zipB`, `combL`; the key negacyclic lemma (`negDirect_getD_lt`, `negDirect_getD_add`): for
`s < r`, `computableNegacyclicDirect r s f` is `rotL s` with the first `s` entries negated, and at
`s + r` the signs are flipped; and `row_eq`, one butterfly row of the snapshot as a `zipB`.
-/

namespace WP.W9s

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

namespace SM

/-! ## `evensL`, `oddsL` -/

theorem evensL_getElem? {α : Type} : ∀ (l : List α) (j : ℕ), (evensL l)[j]? = l[2 * j]?
  | [], j => by simp [evensL]
  | [_], 0 => by simp [evensL]
  | [_], j + 1 => by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
    simp [evensL]
  | _ :: _ :: _, 0 => by simp [evensL]
  | _ :: _ :: l, j + 1 => by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
    simp only [evensL, List.getElem?_cons_succ]
    exact evensL_getElem? l j

theorem oddsL_getElem? {α : Type} : ∀ (l : List α) (j : ℕ), (oddsL l)[j]? = l[2 * j + 1]?
  | [], j => by simp [oddsL]
  | [_], j => by simp [oddsL]
  | _ :: _ :: _, 0 => by simp [oddsL]
  | _ :: _ :: l, j + 1 => by
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by omega]
    simp only [oddsL, List.getElem?_cons_succ]
    exact oddsL_getElem? l j

theorem evensL_length {α : Type} : ∀ (l : List α), (evensL l).length = (l.length + 1) / 2
  | [] => by simp [evensL]
  | [_] => by simp [evensL]
  | _ :: _ :: l => by
    simp only [evensL, List.length_cons, evensL_length l]
    omega

theorem oddsL_length {α : Type} : ∀ (l : List α), (oddsL l).length = l.length / 2
  | [] => by simp [oddsL]
  | [_] => by simp [oddsL]
  | _ :: _ :: l => by
    simp only [oddsL, List.length_cons, oddsL_length l]
    omega

theorem mem_evensL {α : Type} {x : α} : ∀ (l : List α), x ∈ evensL l → x ∈ l
  | [], h => by simp [evensL] at h
  | [_], h => by simpa [evensL] using h
  | _ :: _ :: l, h => by
    simp only [evensL, List.mem_cons] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (mem_evensL l h))

theorem mem_oddsL {α : Type} {x : α} : ∀ (l : List α), x ∈ oddsL l → x ∈ l
  | [], h => by simp [oddsL] at h
  | [_], h => by simp [oddsL] at h
  | _ :: _ :: l, h => by
    simp only [oddsL, List.mem_cons] at h ⊢
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (mem_oddsL l h))

theorem evensL_map {α β : Type} (f : α → β) :
    ∀ (l : List α), evensL (l.map f) = (evensL l).map f
  | [] => by simp [evensL]
  | [_] => by simp [evensL]
  | _ :: _ :: l => by simp only [List.map_cons, evensL, evensL_map f l]

theorem oddsL_map {α β : Type} (f : α → β) :
    ∀ (l : List α), oddsL (l.map f) = (oddsL l).map f
  | [] => by simp [oddsL]
  | [_] => by simp [oddsL]
  | _ :: _ :: l => by simp only [List.map_cons, oddsL, oddsL_map f l]

/-- The snapshot's `Peven` is `evensL` of the rows. -/
theorem toList_evens {β : Type} (P : Array (Array β)) (m : ℕ) (hP : P.size = 2 * m) :
    (Array.ofFn (fun j1 : Fin m => P.getD (2 * j1.val) #[])).toList = evensL P.toList := by
  apply List.ext_getElem?
  intro j
  rw [evensL_getElem?, Array.toList_ofFn, List.getElem?_ofFn, Array.getElem?_toList]
  by_cases hj : j < m
  · have h1 : 2 * j < P.size := by omega
    rw [dif_pos hj]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some]
  · have h2 : P.size ≤ 2 * j := by omega
    rw [dif_neg hj, Array.getElem?_eq_none h2]

/-- The snapshot's `Podd` is `oddsL` of the rows. -/
theorem toList_odds {β : Type} (P : Array (Array β)) (m : ℕ) (hP : P.size = 2 * m) :
    (Array.ofFn (fun j1 : Fin m => P.getD (2 * j1.val + 1) #[])).toList = oddsL P.toList := by
  apply List.ext_getElem?
  intro j
  rw [oddsL_getElem?, Array.toList_ofFn, List.getElem?_ofFn, Array.getElem?_toList]
  by_cases hj : j < m
  · have h1 : 2 * j + 1 < P.size := by omega
    rw [dif_pos hj]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some]
  · have h2 : P.size ≤ 2 * j + 1 := by omega
    rw [dif_neg hj, Array.getElem?_eq_none h2]

#assert_std_axioms evensL_getElem? oddsL_getElem? evensL_length oddsL_length mem_evensL mem_oddsL
  evensL_map oddsL_map toList_evens toList_odds

/-! ## `getD` on lists and arrays -/

theorem getD_toList {β : Type} (f : Array β) (i : ℕ) (d : β) : f.toList.getD i d = f.getD i d := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

theorem getD_ofFn_arr {β : Type} {n : ℕ} (g : Fin n → β) (i : ℕ) (hi : i < n) (d : β) :
    (Array.ofFn g).getD i d = g ⟨i, hi⟩ := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hi, Option.getD_some]

theorem getD_map_toList {β : Type} (A : Array (Array β)) (n : ℕ) :
    (A.toList.map Array.toList).getD n [] = (A.getD n #[]).toList := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases A[n]? <;> rfl

theorem getD_mem_toList {β : Type} (A : Array β) (i : ℕ) (h : i < A.size) (d : β) :
    A.getD i d ∈ A.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]
  exact Array.getElem_mem_toList h

theorem ofFn_getD_toList {β : Type} (a : Array β) (r : ℕ) (h : a.size = r) (d : β) :
    (Array.ofFn (fun k2 : Fin r => a.getD k2.val d)).toList = a.toList := by
  apply List.ext_getElem?
  intro i
  rw [Array.toList_ofFn, List.getElem?_ofFn, Array.getElem?_toList]
  by_cases hi : i < r
  · have h1 : i < a.size := by omega
    rw [dif_pos hi]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some]
  · have h2 : a.size ≤ i := by omega
    rw [dif_neg hi, Array.getElem?_eq_none h2]

theorem list_ext_getD {β : Type} (d : β) {l₁ l₂ : List β} (hl : l₁.length = l₂.length)
    (h : ∀ n, n < l₁.length → l₁.getD n d = l₂.getD n d) : l₁ = l₂ := by
  apply List.ext_getElem?
  intro n
  by_cases hn : n < l₁.length
  · have hn2 : n < l₂.length := by rw [← hl]; exact hn
    have h1 := h n hn
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn,
      List.getElem?_eq_getElem hn2, Option.getD_some, Option.getD_some] at h1
    rw [List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hn2, h1]
  · have hn1 : l₁.length ≤ n := by omega
    have hn2 : l₂.length ≤ n := by omega
    rw [List.getElem?_eq_none hn1, List.getElem?_eq_none hn2]

theorem getD_mem_of_lt {β : Type} (d : β) : ∀ (L : List β) (u : ℕ), u < L.length → L.getD u d ∈ L
  | [], u, h => by simp at h
  | _ :: _, 0, _ => List.mem_cons.2 (Or.inl rfl)
  | _ :: L, u + 1, h => by
    rw [List.getD_cons_succ]
    rw [List.length_cons] at h
    exact List.mem_cons.2 (Or.inr (getD_mem_of_lt d L u (by omega)))

theorem mem_getD {β : Type} : ∀ (L : List (List β)) (u : ℕ) (z : β), z ∈ L.getD u [] →
    ∃ row ∈ L, z ∈ row
  | [], u, z, h => by simp at h
  | a :: _, 0, z, h => ⟨a, List.mem_cons.2 (Or.inl rfl), by simpa using h⟩
  | _ :: L, u + 1, z, h => by
    rw [List.getD_cons_succ] at h
    obtain ⟨row, hm, hz⟩ := mem_getD L u z h
    exact ⟨row, List.mem_cons.2 (Or.inr hm), hz⟩

#assert_std_axioms getD_toList getD_ofFn_arr getD_map_toList getD_mem_toList ofFn_getD_toList
  list_ext_getD getD_mem_of_lt mem_getD

/-! ## `rotL` -/

theorem rotL_length (s : ℕ) (f : List (ℤ × ℤ)) : (rotL s f).length = f.length := by
  rw [rotL, List.length_append, List.length_drop, List.length_take]
  omega

theorem mem_rotL {s : ℕ} {f : List (ℤ × ℤ)} {z : ℤ × ℤ} (h : z ∈ rotL s f) : z ∈ f := by
  rw [rotL, List.mem_append] at h
  rcases h with h | h
  · exact List.mem_of_mem_drop h
  · exact List.mem_of_mem_take h

theorem getD_rotL {s : ℕ} {f : List (ℤ × ℤ)} (hs : s ≤ f.length) (k : ℕ) (d : ℤ × ℤ)
    (hkl : k < f.length) :
    (rotL s f).getD k d = if k < s then f.getD (f.length - s + k) d else f.getD (k - s) d := by
  have hd : (f.drop (f.length - s)).length = s := by rw [List.length_drop]; omega
  rw [rotL, List.getD_eq_getElem?_getD]
  by_cases hks : k < s
  · have h1 : k < (f.drop (f.length - s)).length := by rw [hd]; exact hks
    rw [if_pos hks, List.getElem?_append_left h1, List.getElem?_drop, List.getD_eq_getElem?_getD]
  · have h2 : (f.drop (f.length - s)).length ≤ k := by rw [hd]; omega
    have h3 : k - s < f.length - s := by omega
    rw [if_neg hks, List.getElem?_append_right h2, hd, List.getElem?_take_of_lt h3,
      List.getD_eq_getElem?_getD]

#assert_std_axioms rotL_length mem_rotL getD_rotL

/-! ## `zipB` -/

theorem zipB_length (neg : Bool) : ∀ (s : ℕ) (as gs : List (ℤ × ℤ)), as.length = gs.length →
    (zipB neg s as gs).length = as.length
  | _, [], _, _ => by simp [zipB]
  | _, _ :: _, [], h => by simp at h
  | 0, _ :: as, _ :: gs, h => by
    simp only [zipB, List.length_cons] at h ⊢
    rw [zipB_length neg 0 as gs (by omega)]
  | s + 1, _ :: as, _ :: gs, h => by
    simp only [zipB, List.length_cons] at h ⊢
    rw [zipB_length neg s as gs (by omega)]

theorem zipB_rows {neg : Bool} {s r : ℕ} {as gs : List (ℤ × ℤ)} (ha : as.length = r)
    (hg : gs.length = r) : (zipB neg s as gs).length = r := by
  rw [zipB_length neg s as gs (by rw [ha, hg]), ha]

theorem getD_zipB (neg : Bool) : ∀ (s : ℕ) (as gs : List (ℤ × ℤ)) (k : ℕ) (d : ℤ × ℤ),
    k < as.length → k < gs.length →
    (zipB neg s as gs).getD k d = bfly (if k < s then !neg else neg) (as.getD k d) (gs.getD k d)
  | _, [], _, _, _, h1, _ => by simp at h1
  | _, _ :: _, [], _, _, _, h2 => by simp at h2
  | 0, _ :: _, _ :: _, 0, _, _, _ => by simp [zipB]
  | 0, _ :: as, _ :: gs, k + 1, d, h1, h2 => by
    simp only [zipB, List.getD_cons_succ, List.length_cons] at h1 h2 ⊢
    rw [getD_zipB neg 0 as gs k d (by omega) (by omega)]
    simp
  | s + 1, _ :: _, _ :: _, 0, _, _, _ => by simp [zipB]
  | s + 1, _ :: as, _ :: gs, k + 1, d, h1, h2 => by
    simp only [zipB, List.getD_cons_succ, List.length_cons] at h1 h2 ⊢
    rw [getD_zipB neg s as gs k d (by omega) (by omega)]
    simp

theorem mem_zipB (neg : Bool) {z : ℤ × ℤ} : ∀ (s : ℕ) (as gs : List (ℤ × ℤ)),
    z ∈ zipB neg s as gs → ∃ b a g, a ∈ as ∧ g ∈ gs ∧ z = bfly b a g
  | _, [], _, h => by simp [zipB] at h
  | _, _ :: _, [], h => by simp [zipB] at h
  | 0, a :: as, g :: gs, h => by
    simp only [zipB, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨neg, a, g, List.mem_cons_self, List.mem_cons_self, h⟩
    · obtain ⟨b, a', g', ha, hg, e⟩ := mem_zipB neg 0 as gs h
      exact ⟨b, a', g', List.mem_cons.2 (Or.inr ha), List.mem_cons.2 (Or.inr hg), e⟩
  | s + 1, a :: as, g :: gs, h => by
    simp only [zipB, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨!neg, a, g, List.mem_cons_self, List.mem_cons_self, h⟩
    · obtain ⟨b, a', g', ha, hg, e⟩ := mem_zipB neg s as gs h
      exact ⟨b, a', g', List.mem_cons.2 (Or.inr ha), List.mem_cons.2 (Or.inr hg), e⟩

#assert_std_axioms zipB_length zipB_rows getD_zipB mem_zipB

/-! ## `combL` -/

theorem combL_length (Δ : ℕ) (Y0 Y1 : List (List (ℤ × ℤ))) :
    (combL Δ Y0 Y1).length = 2 * Y0.length := by
  rw [combL, List.length_append, List.length_map, List.length_map, List.length_range]
  omega

theorem getD_append_map_range {β : Type} (m : ℕ) (F G : ℕ → β) (d : β) (n : ℕ)
    (hn : n < 2 * m) :
    ((List.range m).map F ++ (List.range m).map G).getD n d =
      if n < m then F n else G (n - m) := by
  have hlen : ((List.range m).map F).length = m := by rw [List.length_map, List.length_range]
  rw [List.getD_eq_getElem?_getD]
  by_cases h : n < m
  · have h1 : n < ((List.range m).map F).length := by rw [hlen]; exact h
    rw [if_pos h, List.getElem?_append_left h1, List.getElem?_map, List.getElem?_range h]
    all_goals rfl
  · have h1 : ((List.range m).map F).length ≤ n := by rw [hlen]; omega
    have h2 : n - m < m := by omega
    rw [if_neg h, List.getElem?_append_right h1, hlen, List.getElem?_map, List.getElem?_range h2]
    all_goals rfl

theorem getD_combL (Δ : ℕ) (Y0 Y1 : List (List (ℤ × ℤ))) (n : ℕ) (hn : n < 2 * Y0.length) :
    (combL Δ Y0 Y1).getD n [] =
      if n < Y0.length then zipB false (Δ * n) (Y0.getD n []) (rotL (Δ * n) (Y1.getD n []))
      else zipB true (Δ * (n - Y0.length)) (Y0.getD (n - Y0.length) [])
        (rotL (Δ * (n - Y0.length)) (Y1.getD (n - Y0.length) [])) := by
  unfold combL
  exact getD_append_map_range Y0.length _ _ [] n hn

theorem mem_combL {Δ : ℕ} {Y0 Y1 : List (List (ℤ × ℤ))} {row : List (ℤ × ℤ)}
    (h : row ∈ combL Δ Y0 Y1) : ∃ u, u < Y0.length ∧ ∃ b,
      row = zipB b (Δ * u) (Y0.getD u []) (rotL (Δ * u) (Y1.getD u [])) := by
  simp only [combL, List.mem_append, List.mem_map, List.mem_range] at h
  rcases h with ⟨u, hu, e⟩ | ⟨u, hu, e⟩
  · exact ⟨u, hu, false, e.symm⟩
  · exact ⟨u, hu, true, e.symm⟩

#assert_std_axioms combL_length getD_append_map_range getD_combL mem_combL

/-! ## The negacyclic shift and one butterfly row -/

/-- For `s < r`: `computableNegacyclicDirect r s f` is `rotL s f` with the first `s` entries
negated. -/
theorem negDirect_getD_lt (r s : ℕ) (f : Array (ℤ × ℤ)) (hf : f.size = r) (hs : s < r)
    (k2 : ℕ) (hk : k2 < r) :
    (computableNegacyclicDirect r s f).getD k2 (0, 0) =
      if k2 < s then gNeg ((rotL s f.toList).getD k2 (0, 0))
      else (rotL s f.toList).getD k2 (0, 0) := by
  have hr : r ≠ 0 := by omega
  have hmod : s % (2 * r) = s := Nat.mod_eq_of_lt (by omega)
  have hle : s ≤ r := by omega
  have hlen : s ≤ f.toList.length := by rw [Array.length_toList]; omega
  have hkl : k2 < f.toList.length := by rw [Array.length_toList]; omega
  rw [getD_rotL hlen k2 (0, 0) hkl, Array.length_toList, hf, getD_toList, getD_toList]
  simp only [computableNegacyclicDirect, if_neg hr, hmod, if_pos hle, getD_ofFn_arr _ k2 hk]
  by_cases h : k2 < s
  · simp only [if_pos h]
    rw [show k2 + r - s = r - s + k2 by omega]
  · simp only [if_neg h]

/-- At shift `s + r` (`s < r`) the signs are flipped: the first `s` entries are kept, the rest
negated. -/
theorem negDirect_getD_add (r s : ℕ) (f : Array (ℤ × ℤ)) (hf : f.size = r) (hs : s < r)
    (k2 : ℕ) (hk : k2 < r) :
    (computableNegacyclicDirect r (s + r) f).getD k2 (0, 0) =
      if k2 < s then (rotL s f.toList).getD k2 (0, 0)
      else gNeg ((rotL s f.toList).getD k2 (0, 0)) := by
  have hr : r ≠ 0 := by omega
  have hmod : (s + r) % (2 * r) = s + r := Nat.mod_eq_of_lt (by omega)
  have hlen : s ≤ f.toList.length := by rw [Array.length_toList]; omega
  have hkl : k2 < f.toList.length := by rw [Array.length_toList]; omega
  rw [getD_rotL hlen k2 (0, 0) hkl, Array.length_toList, hf, getD_toList, getD_toList]
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · have hle : 0 + r ≤ r := by omega
    have hk' : k2 < 0 + r := by omega
    simp only [computableNegacyclicDirect, if_neg hr, hmod, if_pos hle, getD_ofFn_arr _ k2 hk,
      if_pos hk', if_neg (Nat.not_lt_zero k2)]
    rw [show k2 + r - (0 + r) = k2 - 0 by omega]
  · have hgt : ¬ (s + r ≤ r) := by omega
    have hsub : s + r - r = s := by omega
    simp only [computableNegacyclicDirect, if_neg hr, hmod, if_neg hgt, hsub,
      getD_ofFn_arr _ k2 hk]
    by_cases h : k2 < s
    · simp only [if_pos h]
      rw [show k2 + r - s = r - s + k2 by omega]
    · simp only [if_neg h]

theorem add_cond (c : Bool) (a x : ℤ × ℤ) :
    (divRoundPow2 (a.1 + (if c then gNeg x else x).1) 1,
      divRoundPow2 (a.2 + (if c then gNeg x else x).2) 1) = bfly c a x := by
  cases c <;> rfl

/-- One butterfly row of the snapshot (`y0 + shifted y1`, rounded) as a `zipB`, given the signs
of the shifted `y1` (`hsh`). -/
theorem row_eq (r s' s : ℕ) (neg : Bool) (y0 y1 : Array (ℤ × ℤ)) (h0 : y0.size = r)
    (h1 : y1.size = r)
    (hsh : ∀ k2, k2 < r → (computableNegacyclicDirect r s' y1).getD k2 (0, 0) =
      if (if k2 < s then !neg else neg) then gNeg ((rotL s y1.toList).getD k2 (0, 0))
      else (rotL s y1.toList).getD k2 (0, 0)) :
    (Array.ofFn (fun k2 : Fin r =>
      (divRoundPow2 ((y0.getD k2.val (0, 0)).1 +
          ((computableNegacyclicDirect r s' y1).getD k2.val (0, 0)).1) 1,
        divRoundPow2 ((y0.getD k2.val (0, 0)).2 +
          ((computableNegacyclicDirect r s' y1).getD k2.val (0, 0)).2) 1))).toList =
      zipB neg s y0.toList (rotL s y1.toList) := by
  have hl0 : y0.toList.length = r := by rw [Array.length_toList, h0]
  have hl1 : (rotL s y1.toList).length = r := by rw [rotL_length, Array.length_toList, h1]
  apply list_ext_getD ((0, 0) : ℤ × ℤ)
  · rw [Array.length_toList, Array.size_ofFn, zipB_rows hl0 hl1]
  · intro k2 hk
    have hk2 : k2 < r := by rw [Array.length_toList, Array.size_ofFn] at hk; exact hk
    rw [getD_toList, getD_ofFn_arr _ k2 hk2]
    try dsimp only
    rw [hsh k2 hk2, add_cond, getD_zipB neg s y0.toList (rotL s y1.toList) k2 (0, 0)
      (by rw [hl0]; exact hk2) (by rw [hl1]; exact hk2), getD_toList y0 k2 (0, 0)]

#assert_std_axioms negDirect_getD_lt negDirect_getD_add add_cond row_eq

end SM

end WP.W9s
