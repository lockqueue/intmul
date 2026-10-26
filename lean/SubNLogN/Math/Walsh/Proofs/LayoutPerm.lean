import SubNLogN.Math.Walsh.Layout

/-!
# Lemma 6.3, combinatorial parts: `L`, `B` are permutations, chunk rounds are slices, `U = (LB)⁻¹`

Paper: Lemma 6.3 (`lem:walsh-layout`, Section 6.2 (`sec:direct-fft-layout`)), eq. (`eq:unshuffle`).

Proves `WalshLayoutPermStmt`, `WalshLayoutRoundSliceStmt` and `WalshLayoutUnshuffleStmt` of
`SubNLogN/Math/Walsh/Layout.lean`. No contract is assumed.

Plan (helpers in the namespace `SubNLogN.Math.Walsh.LayoutPermAux`):
* general list facts: `idxOf` in a `flatMap` (`idxOf_flatMap`), `idxOf` of an entry whose earlier
  entries differ (`idxOf_getElem_of_forall_ne`), lengths of `flatMap`s with blocks of constant
  length, and the inverse by search `invFunFin` of a bijection (`invFunFin_spec`);
* `𝒪`: length `m₀`, `Nodup`, membership `(i, v) ∈ 𝒪 ↔ v < a_i`, `idxOf (i, v) 𝒪 = origPos a i v`;
* `𝒫 ‖ 𝒞`: length `m₀` (`|𝒫| = #{i | a_i = ℓ} + b₀ D`, `|𝒞| = J_blk D K`, `J_blk K + b₀ = ℓ - 1`);
  every slot `(i, v)`, `v < a_i`, occurs in it (`mem_newSlots`); the slot `(i, ℓ-2-jK-t)`
  (`j < J_blk`, `t < K`) sits at position `n_P + j D K + i K + t` (`newPos_chunk`);
* `L`, `B` are injective, hence bijective, so `U = invFunFin (L ∘ B)` inverts `L ∘ B`;
* a round at slot `v ∈ [b₀, ℓ-2]` uses chunk `j = ⌊(ℓ-2-v)/K⌋` of every axis at offset
  `t = (ℓ-2-v) mod K = K - 1 - ((v - b₀) mod K)` (`walsh_layout_round_slice`).
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

namespace LayoutPermAux

/-! ### General list facts -/

/-- `idxOf` in a `flatMap`: if `s` lies in block `j` and in no earlier block, its index is the total
length of the earlier blocks plus its index inside block `j`. -/
theorem idxOf_flatMap {α β : Type} [BEq β] [LawfulBEq β] (L : List α) (f : α → List β)
    (j : ℕ) (hj : j < L.length) (s : β) (hs : s ∈ f L[j])
    (hnot : ∀ (k : ℕ) (hk : k < j), s ∉ f (L[k]'(Nat.lt_trans hk hj))) :
    (L.flatMap f).idxOf s = ((L.take j).map (fun x => (f x).length)).sum + (f L[j]).idxOf s := by
  induction L generalizing j with
  | nil => simp at hj
  | cons x L ih =>
    cases j with
    | zero =>
      have hs0 : s ∈ f x := by simpa using hs
      rw [List.flatMap_cons, List.idxOf_append_of_mem hs0]
      simp
    | succ j =>
      have hx : s ∉ f x := by simpa using hnot 0 (Nat.succ_pos j)
      have hj' : j < L.length := by simpa using hj
      have hs' : s ∈ f L[j] := by simpa using hs
      have hnot' : ∀ (k : ℕ) (hk : k < j), s ∉ f (L[k]'(Nat.lt_trans hk hj')) := by
        intro k hk
        simpa using hnot (k + 1) (by omega)
      rw [List.flatMap_cons, List.idxOf_append_of_notMem hx, ih j hj' hs' hnot']
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      omega

/-- `idxOf` of the entry at index `k` when no earlier entry equals it. -/
theorem idxOf_getElem_of_forall_ne {β : Type} [BEq β] [LawfulBEq β] (l : List β) (k : ℕ)
    (hk : k < l.length) (hne : ∀ (k' : ℕ) (hk' : k' < k), l[k']'(Nat.lt_trans hk' hk) ≠ l[k]) :
    l.idxOf l[k] = k := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x l ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hk' : k < l.length := by simpa using hk
      have hx : x ≠ l[k] := by simpa using hne 0 (Nat.succ_pos k)
      have hne' : ∀ (k' : ℕ) (hk'' : k' < k), l[k']'(Nat.lt_trans hk'' hk') ≠ l[k] := by
        intro k' hk''
        simpa using hne (k' + 1) (by omega)
      simp only [List.getElem_cons_succ]
      rw [List.idxOf_cons_ne _ hx, ih k hk' hne']

/-- Length of a `flatMap` whose blocks all have length `c`. -/
theorem length_flatMap_const {α β : Type} (L : List α) (f : α → List β) (c : ℕ)
    (h : ∀ x ∈ L, (f x).length = c) : (L.flatMap f).length = L.length * c := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.flatMap_cons, List.length_append, h x (by simp),
      ih (fun y hy => h y (by simp [hy])), List.length_cons]
    ring

/-- Sum of a map which is constant `c` on the list. -/
theorem sum_map_const {α : Type} (L : List α) (g : α → ℕ) (c : ℕ) (h : ∀ x ∈ L, g x = c) :
    (L.map g).sum = L.length * c := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.map_cons, List.sum_cons, h x (by simp), ih (fun y hy => h y (by simp [hy])),
      List.length_cons]
    ring

/-- The inverse by search of a bijection is a right inverse. -/
theorem invFunFin_spec {m : ℕ} (f : Fin m → Fin m) (hf : Function.Bijective f) (p : Fin m) :
    f (invFunFin f p) = p := by
  unfold invFunFin
  rcases h : (List.finRange m).find? (fun q => decide (f q = p)) with _ | q
  · exfalso
    obtain ⟨q, hq⟩ := hf.2 p
    rw [List.find?_eq_none] at h
    exact h q (List.mem_finRange q) (by simpa using hq)
  · have hq := List.find?_some h
    simpa using hq

/-- The inverse by search of a bijection is a left inverse. -/
theorem invFunFin_left_inv {m : ℕ} (f : Fin m → Fin m) (hf : Function.Bijective f) (p : Fin m) :
    invFunFin f (f p) = p :=
  hf.1 (invFunFin_spec f hf (f p))

/-! ### The original list `𝒪` -/

variable {D : ℕ}

/-- Block `i` of `𝒪`: `((i, v) : v = a_i - 1, …, 0)`. -/
def origBlock (a : Fin D → ℕ) (i : Fin D) : List (Fin D × ℕ) :=
  (List.range (a i)).reverse.map (fun v => (i, v))

theorem origSlots_eq (a : Fin D → ℕ) : origSlots a = (List.finRange D).flatMap (origBlock a) :=
  rfl

theorem length_origBlock (a : Fin D → ℕ) (i : Fin D) : (origBlock a i).length = a i := by
  simp [origBlock]

theorem mem_origBlock (a : Fin D → ℕ) (i : Fin D) (s : Fin D × ℕ) :
    s ∈ origBlock a i ↔ s.1 = i ∧ s.2 < a i := by
  unfold origBlock
  simp only [List.mem_map, List.mem_reverse, List.mem_range]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨rfl, hv⟩
  · rintro ⟨h1, h2⟩
    exact ⟨s.2, h2, Prod.ext h1.symm rfl⟩

/-- `|𝒪| = m₀`. -/
theorem length_origSlots (a : Fin D → ℕ) : (origSlots a).length = addrBits a := by
  rw [origSlots_eq, List.length_flatMap, addrBits, List.ofFn_eq_map]
  simp only [length_origBlock]

/-- `(i, v) ∈ 𝒪 ↔ v < a_i`. -/
theorem mem_origSlots (a : Fin D → ℕ) (s : Fin D × ℕ) : s ∈ origSlots a ↔ s.2 < a s.1 := by
  rw [origSlots_eq, List.mem_flatMap]
  constructor
  · rintro ⟨i, _, hs⟩
    obtain ⟨h1, h2⟩ := (mem_origBlock a i s).1 hs
    rw [h1]
    exact h2
  · intro h
    exact ⟨s.1, List.mem_finRange _, (mem_origBlock a s.1 s).2 ⟨rfl, h⟩⟩

/-- `𝒪` has no repeated slot. -/
theorem nodup_origSlots (a : Fin D → ℕ) : (origSlots a).Nodup := by
  rw [origSlots_eq, List.nodup_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · unfold origBlock
    exact (List.nodup_reverse.mpr List.nodup_range).map (fun v w h => by simpa using h)
  · refine (List.nodup_finRange D).pairwise_of_forall_ne (fun i _ j _ hij => ?_)
    intro s hs1 hs2
    exact hij (((mem_origBlock a i s).1 hs1).1.symm.trans ((mem_origBlock a j s).1 hs2).1)

theorem idxOf_origBlock (a : Fin D → ℕ) (i : Fin D) (v : ℕ) (hv : v < a i) :
    (origBlock a i).idxOf (i, v) = a i - 1 - v := by
  have hk : a i - 1 - v < (origBlock a i).length := by rw [length_origBlock]; omega
  have hget : ∀ (k : ℕ) (hk : k < (origBlock a i).length),
      (origBlock a i)[k] = (i, a i - 1 - k) := by
    intro k hk
    simp [origBlock, List.getElem_reverse]
  have hval : (origBlock a i)[a i - 1 - v] = (i, v) := by
    rw [hget]
    congr 1
    omega
  rw [← hval]
  refine idxOf_getElem_of_forall_ne _ _ hk (fun k' hk' => ?_)
  rw [hget, hget]
  intro h
  have h2 := (Prod.mk.inj h).2
  rw [length_origBlock] at hk
  omega

/-- The slot `(i, v)` sits at position `origPos a i v` of `𝒪`. -/
theorem idxOf_origSlots (a : Fin D → ℕ) (i : Fin D) (v : ℕ) (hv : v < a i) :
    (origSlots a).idxOf (i, v) = origPos a i v := by
  have hi : (i : ℕ) < (List.finRange D).length := by simp
  have hget : (List.finRange D)[(i : ℕ)] = i := by simp
  have hmem : (i, v) ∈ origBlock a (List.finRange D)[(i : ℕ)] := by
    rw [hget]
    exact (mem_origBlock a i (i, v)).2 ⟨rfl, hv⟩
  have hnot : ∀ (k : ℕ) (hk : k < (i : ℕ)),
      (i, v) ∉ origBlock a ((List.finRange D)[k]'(Nat.lt_trans hk hi)) := by
    intro k hk hk'
    have h1 := congrArg Fin.val ((mem_origBlock a _ (i, v)).1 hk').1
    simp at h1
    omega
  rw [origSlots_eq, idxOf_flatMap (List.finRange D) (origBlock a) i hi (i, v) hmem hnot, hget,
    idxOf_origBlock a i v hv, origPos, axisOffset, List.ofFn_eq_map, ← List.map_take]
  simp only [length_origBlock]

/-- `origPos a i w < m₀` for `w < a_i`. -/
theorem origPos_lt (a : Fin D → ℕ) (i : Fin D) (w : ℕ) (hw : w < a i) :
    origPos a i w < addrBits a := by
  rw [← idxOf_origSlots a i w hw, ← length_origSlots a]
  exact List.idxOf_lt_length_of_mem ((mem_origSlots a _).2 hw)

/-! ### Arithmetic of `b₀` and `J_blk` -/

theorem layoutB0_lt (ℓ K : ℕ) (hK : 0 < K) : layoutB0 ℓ K < K := Nat.mod_lt _ hK

/-- `J_blk K + b₀ = ℓ - 1`. -/
theorem jblk_mul_add_b0 (ℓ K : ℕ) (hK : 0 < K) : layoutJblk ℓ K * K + layoutB0 ℓ K = ℓ - 1 := by
  unfold layoutJblk layoutB0
  have h := Nat.div_add_mod' (ℓ - 1) K
  have h2 : ℓ - 1 - (ℓ - 1) % K = K * ((ℓ - 1) / K) := by
    rw [Nat.mul_comm]
    omega
  rw [h2, Nat.mul_div_cancel_left _ hK]
  exact h

/-! ### The new list `𝒫 ‖ 𝒞`: length and membership -/

/-- The number `#{i | a_i = ℓ}` of long axes. -/
def nLong (ℓ : ℕ) (a : Fin D → ℕ) : ℕ := ((List.finRange D).filter (fun i => a i = ℓ)).length

theorem sum_map_two_widths (ℓ : ℕ) (a : Fin D → ℕ) (hℓ : 1 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (L : List (Fin D)) :
    (L.map a).sum = L.length * (ℓ - 1) + (L.filter (fun i => a i = ℓ)).length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons, List.length_cons]
    have e : (L.length + 1) * (ℓ - 1) = L.length * (ℓ - 1) + (ℓ - 1) := by ring
    rcases ha x with h | h
    · have hne : ¬ a x = ℓ := by omega
      rw [if_neg (by simpa using hne), e, h]
      omega
    · rw [if_pos (by simpa using h), List.length_cons, e, h]
      omega

/-- `m₀ = D (ℓ - 1) + #{i | a_i = ℓ}`. -/
theorem addrBits_eq (ℓ : ℕ) (a : Fin D → ℕ) (hℓ : 1 ≤ ℓ) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) :
    addrBits a = D * (ℓ - 1) + nLong ℓ a := by
  rw [addrBits, List.ofFn_eq_map, sum_map_two_widths ℓ a hℓ ha, List.length_finRange, nLong]

/-- Block `v` of the second part of `𝒫`: `((i, v) : i increasing)`. -/
def prefixBlock (D v : ℕ) : List (Fin D × ℕ) := (List.finRange D).map (fun i => (i, v))

theorem prefixSlots_eq (ℓ K : ℕ) (a : Fin D → ℕ) :
    prefixSlots ℓ K a =
      ((List.finRange D).filter (fun i => a i = ℓ)).map (fun i => (i, ℓ - 1)) ++
        (List.range (layoutB0 ℓ K)).reverse.flatMap (prefixBlock D) :=
  rfl

/-- `n_P = #{i | a_i = ℓ} + b₀ D`. -/
theorem prefixLen_eq (ℓ K : ℕ) (a : Fin D → ℕ) :
    prefixLen ℓ K a = nLong ℓ a + layoutB0 ℓ K * D := by
  rw [prefixLen, prefixSlots_eq, List.length_append, List.length_map, nLong,
    length_flatMap_const _ (prefixBlock D) D (fun v _ => by simp [prefixBlock]),
    List.length_reverse, List.length_range]

/-- Cell `(j, i)` of `𝒞`: `((i, v) : v = ℓ-2-jK, …, ℓ-1-(j+1)K)`. -/
def chunkCell (ℓ K j : ℕ) (i : Fin D) : List (Fin D × ℕ) :=
  (List.range K).map (fun t => (i, ℓ - 2 - j * K - t))

/-- Block `j` of `𝒞`: the cells `(j, i)`, `i` increasing. -/
def chunkBlock (D ℓ K j : ℕ) : List (Fin D × ℕ) := (List.finRange D).flatMap (chunkCell ℓ K j)

theorem chunkSlots_eq (D ℓ K : ℕ) :
    chunkSlots D ℓ K = (List.range (layoutJblk ℓ K)).flatMap (chunkBlock D ℓ K) :=
  rfl

theorem length_chunkCell (ℓ K j : ℕ) (i : Fin D) : (chunkCell ℓ K j i).length = K := by
  simp [chunkCell]

theorem length_chunkBlock (D ℓ K j : ℕ) : (chunkBlock D ℓ K j).length = D * K := by
  rw [chunkBlock, length_flatMap_const _ (chunkCell ℓ K j) K (fun i _ => length_chunkCell ℓ K j i),
    List.length_finRange]

/-- `|𝒞| = J_blk D K`. -/
theorem length_chunkSlots (D ℓ K : ℕ) :
    (chunkSlots D ℓ K).length = layoutJblk ℓ K * (D * K) := by
  rw [chunkSlots_eq,
    length_flatMap_const _ (chunkBlock D ℓ K) (D * K) (fun j _ => length_chunkBlock D ℓ K j),
    List.length_range]

/-- `|𝒫 ‖ 𝒞| = m₀`. -/
theorem length_newSlots (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (hℓ : 1 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) : (newSlots ℓ K a).length = addrBits a := by
  have h1 := prefixLen_eq ℓ K a
  rw [prefixLen] at h1
  rw [newSlots, List.length_append, h1, length_chunkSlots, addrBits_eq ℓ a hℓ ha,
    ← jblk_mul_add_b0 ℓ K hK]
  ring

theorem mem_chunkCell (ℓ K j : ℕ) (i : Fin D) (s : Fin D × ℕ) :
    s ∈ chunkCell ℓ K j i ↔ ∃ t, t < K ∧ (i, ℓ - 2 - j * K - t) = s := by
  simp [chunkCell]

/-- The chunk index of a slot `v ∈ [b₀, ℓ-2]`: `⌊(ℓ-2-v)/K⌋ < J_blk`. -/
theorem chunk_index_lt (ℓ K v : ℕ) (hK : 0 < K) (hv0 : layoutB0 ℓ K ≤ v) (hv1 : v + 2 ≤ ℓ) :
    (ℓ - 2 - v) / K < layoutJblk ℓ K := by
  have h := jblk_mul_add_b0 ℓ K hK
  rw [Nat.div_lt_iff_lt_mul hK]
  omega

/-- Every slot `(i, v)`, `v < a_i`, occurs in `𝒫 ‖ 𝒞`. -/
theorem mem_newSlots (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (s : Fin D × ℕ) (hs : s.2 < a s.1) :
    s ∈ newSlots ℓ K a := by
  obtain ⟨i, v⟩ := s
  simp only at hs
  have hb := layoutB0_lt ℓ K hK
  have hJ := jblk_mul_add_b0 ℓ K hK
  rw [newSlots, prefixSlots_eq, List.mem_append, List.mem_append]
  by_cases hv : v = ℓ - 1
  · left; left
    have hai : a i = ℓ := by rcases ha i with h | h <;> omega
    rw [List.mem_map]
    exact ⟨i, by simp [hai], by rw [hv]⟩
  · by_cases hvb : v < layoutB0 ℓ K
    · left; right
      rw [List.mem_flatMap]
      exact ⟨v, by simp [hvb], by simp [prefixBlock]⟩
    · right
      have hv1 : v + 2 ≤ ℓ := by rcases ha i with h | h <;> omega
      have hjt := Nat.div_add_mod' (ℓ - 2 - v) K
      rw [chunkSlots_eq, List.mem_flatMap]
      refine ⟨(ℓ - 2 - v) / K, List.mem_range.2 (chunk_index_lt ℓ K v hK (by omega) hv1), ?_⟩
      rw [chunkBlock, List.mem_flatMap]
      refine ⟨i, List.mem_finRange i,
        (mem_chunkCell ℓ K _ i _).2 ⟨(ℓ - 2 - v) % K, Nat.mod_lt _ hK, ?_⟩⟩
      congr 1
      omega

/-! ### Positions of chunk slots -/

/-- Chunk slots are not in `𝒫`. -/
theorem not_mem_prefixSlots (ℓ K : ℕ) (a : Fin D → ℕ) (i : Fin D) (v : ℕ)
    (hv0 : layoutB0 ℓ K ≤ v) (hv1 : v + 2 ≤ ℓ) : (i, v) ∉ prefixSlots ℓ K a := by
  rw [prefixSlots_eq, List.mem_append, not_or]
  constructor
  · rw [List.mem_map]
    rintro ⟨i', _, h⟩
    have h2 := (Prod.mk.inj h).2
    omega
  · rw [List.mem_flatMap]
    rintro ⟨v', hv', h⟩
    rw [prefixBlock, List.mem_map] at h
    obtain ⟨i', _, h⟩ := h
    have h2 := (Prod.mk.inj h).2
    rw [List.mem_reverse, List.mem_range] at hv'
    omega

theorem idxOf_chunkCell (ℓ K j : ℕ) (i : Fin D) (t : ℕ) (htK : t < K) (hjt : j * K + t ≤ ℓ - 2) :
    (chunkCell ℓ K j i).idxOf (i, ℓ - 2 - j * K - t) = t := by
  have hlen : t < (chunkCell ℓ K j i).length := by rw [length_chunkCell]; exact htK
  have hget : ∀ (k : ℕ) (hk : k < (chunkCell ℓ K j i).length),
      (chunkCell ℓ K j i)[k] = (i, ℓ - 2 - j * K - k) := by
    intro k hk
    simp [chunkCell]
  rw [← hget t hlen]
  refine idxOf_getElem_of_forall_ne _ _ hlen (fun k' hk' => ?_)
  rw [hget, hget]
  intro h
  have h2 := (Prod.mk.inj h).2
  omega

theorem idxOf_chunkBlock (ℓ K j : ℕ) (i : Fin D) (t : ℕ) (htK : t < K)
    (hjt : j * K + t ≤ ℓ - 2) :
    (chunkBlock D ℓ K j).idxOf (i, ℓ - 2 - j * K - t) = (i : ℕ) * K + t := by
  have hi : (i : ℕ) < (List.finRange D).length := by simp
  have hget : (List.finRange D)[(i : ℕ)] = i := by simp
  have hmem : (i, ℓ - 2 - j * K - t) ∈ chunkCell ℓ K j (List.finRange D)[(i : ℕ)] := by
    rw [hget, mem_chunkCell]
    exact ⟨t, htK, rfl⟩
  have hnot : ∀ (k : ℕ) (hk : k < (i : ℕ)),
      (i, ℓ - 2 - j * K - t) ∉ chunkCell ℓ K j ((List.finRange D)[k]'(Nat.lt_trans hk hi)) := by
    intro k hk hk'
    rw [mem_chunkCell] at hk'
    obtain ⟨t', _, h⟩ := hk'
    have h1 := congrArg Fin.val (Prod.mk.inj h).1
    simp at h1
    omega
  rw [chunkBlock, idxOf_flatMap (List.finRange D) (chunkCell ℓ K j) i hi _ hmem hnot, hget,
    idxOf_chunkCell ℓ K j i t htK hjt,
    sum_map_const _ _ K (fun x _ => length_chunkCell ℓ K j x), List.length_take,
    List.length_finRange, min_eq_left i.isLt.le]

/-- Position of the slot `(i, ℓ-2-jK-t)` (`j < J_blk`, `t < K`) inside `𝒞`. -/
theorem idxOf_chunkSlots (ℓ K : ℕ) (hK : 0 < K) (j t : ℕ) (hjJ : j < layoutJblk ℓ K)
    (htK : t < K) (i : Fin D) :
    (chunkSlots D ℓ K).idxOf (i, ℓ - 2 - j * K - t) = j * (D * K) + ((i : ℕ) * K + t) := by
  have hJ := jblk_mul_add_b0 ℓ K hK
  have hjK : (j + 1) * K ≤ layoutJblk ℓ K * K := Nat.mul_le_mul_right K (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hjK
  have hjt : j * K + t ≤ ℓ - 2 := by omega
  have hjlen : j < (List.range (layoutJblk ℓ K)).length := by simpa using hjJ
  have hgetj : (List.range (layoutJblk ℓ K))[j] = j := List.getElem_range _
  have hmem : (i, ℓ - 2 - j * K - t) ∈ chunkBlock D ℓ K (List.range (layoutJblk ℓ K))[j] := by
    rw [hgetj, chunkBlock, List.mem_flatMap]
    exact ⟨i, List.mem_finRange i, (mem_chunkCell ℓ K j i _).2 ⟨t, htK, rfl⟩⟩
  have hnot : ∀ (k : ℕ) (hk : k < j), (i, ℓ - 2 - j * K - t) ∉
      chunkBlock D ℓ K ((List.range (layoutJblk ℓ K))[k]'(Nat.lt_trans hk hjlen)) := by
    intro k hk hk'
    rw [List.getElem_range, chunkBlock, List.mem_flatMap] at hk'
    obtain ⟨i', _, hk'⟩ := hk'
    rw [mem_chunkCell] at hk'
    obtain ⟨t', ht', h⟩ := hk'
    have h2 := (Prod.mk.inj h).2
    have hkK : (k + 1) * K ≤ j * K := Nat.mul_le_mul_right K (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hkK
    omega
  rw [chunkSlots_eq,
    idxOf_flatMap (List.range (layoutJblk ℓ K)) (chunkBlock D ℓ K) j hjlen _ hmem hnot,
    hgetj, idxOf_chunkBlock ℓ K j i t htK hjt,
    sum_map_const _ _ (D * K) (fun x _ => length_chunkBlock D ℓ K x), List.length_take,
    List.length_range, min_eq_left hjJ.le]

/-- Position of the slot `(i, ℓ-2-jK-t)` (`j < J_blk`, `t < K`) in `𝒫 ‖ 𝒞`:
`n_P + j D K + i K + t`. -/
theorem newPos_chunk (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (j t : ℕ)
    (hjJ : j < layoutJblk ℓ K) (htK : t < K) (i : Fin D) :
    newPos ℓ K a (i, ℓ - 2 - j * K - t) = prefixLen ℓ K a + j * (D * K) + ((i : ℕ) * K + t) := by
  have hJ := jblk_mul_add_b0 ℓ K hK
  have hjK : (j + 1) * K ≤ layoutJblk ℓ K * K := Nat.mul_le_mul_right K (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hjK
  rw [newPos, newSlots,
    List.idxOf_append_of_notMem
      (not_mem_prefixSlots ℓ K a i (ℓ - 2 - j * K - t) (by omega) (by omega)),
    idxOf_chunkSlots ℓ K hK j t hjJ htK i, prefixLen, Nat.add_assoc]

/-! ### `L` and `B` are permutations -/

theorem newPos_lt (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (s : Fin D × ℕ) (hs : s.2 < a s.1) :
    newPos ℓ K a s < addrBits a := by
  rw [← length_newSlots ℓ K a hK (by omega) ha]
  exact List.idxOf_lt_length_of_mem (mem_newSlots ℓ K a hK hℓ ha s hs)

/-- `L` moves the slot at position `p` of `𝒪` to its position in `𝒫 ‖ 𝒞`. -/
theorem layoutL_val (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (p : Fin (addrBits a))
    (hp : (p : ℕ) < (origSlots a).length) :
    ((layoutL ℓ K a p : Fin (addrBits a)) : ℕ) = newPos ℓ K a ((origSlots a)[(p : ℕ)]'hp) := by
  have hs := (mem_origSlots a _).1 (List.getElem_mem hp)
  unfold layoutL
  rw [List.getElem?_eq_getElem hp]
  exact Nat.mod_eq_of_lt (newPos_lt ℓ K a hK hℓ ha _ hs)

theorem layoutL_injective (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) : Function.Injective (layoutL ℓ K a) := by
  intro p q hpq
  have hlen := length_origSlots a
  have hp : (p : ℕ) < (origSlots a).length := by rw [hlen]; exact p.isLt
  have hq : (q : ℕ) < (origSlots a).length := by rw [hlen]; exact q.isLt
  have h := congrArg Fin.val hpq
  rw [layoutL_val ℓ K a hK hℓ ha p hp, layoutL_val ℓ K a hK hℓ ha q hq] at h
  have hsp := mem_newSlots ℓ K a hK hℓ ha _ ((mem_origSlots a _).1 (List.getElem_mem hp))
  unfold newPos at h
  have heq := (List.idxOf_inj hsp).1 h
  exact Fin.ext ((nodup_origSlots a).getElem_inj_iff.1 heq)

/-- `B` maps the slot `(i, v)` at position `p` of `𝒪` to the position of `(i, a_i - 1 - v)`. -/
theorem bitRevB_val (a : Fin D → ℕ) (p : Fin (addrBits a))
    (hp : (p : ℕ) < (origSlots a).length) :
    ((bitRevB a p : Fin (addrBits a)) : ℕ) =
      origPos a ((origSlots a)[(p : ℕ)]'hp).1
        (a ((origSlots a)[(p : ℕ)]'hp).1 - 1 - ((origSlots a)[(p : ℕ)]'hp).2) := by
  have hs := (mem_origSlots a _).1 (List.getElem_mem hp)
  unfold bitRevB
  rw [List.getElem?_eq_getElem hp]
  exact Nat.mod_eq_of_lt (origPos_lt a _ _ (by omega))

theorem bitRevB_injective (a : Fin D → ℕ) : Function.Injective (bitRevB a) := by
  intro p q hpq
  have hlen := length_origSlots a
  have hp : (p : ℕ) < (origSlots a).length := by rw [hlen]; exact p.isLt
  have hq : (q : ℕ) < (origSlots a).length := by rw [hlen]; exact q.isLt
  have h := congrArg Fin.val hpq
  rw [bitRevB_val a p hp, bitRevB_val a q hq] at h
  have hs := (mem_origSlots a _).1 (List.getElem_mem hp)
  have hs' := (mem_origSlots a _).1 (List.getElem_mem hq)
  set s := (origSlots a)[(p : ℕ)]'hp with hs_def
  set s' := (origSlots a)[(q : ℕ)]'hq with hs'_def
  rw [← idxOf_origSlots a s.1 (a s.1 - 1 - s.2) (by omega),
    ← idxOf_origSlots a s'.1 (a s'.1 - 1 - s'.2) (by omega)] at h
  have h2 := (List.idxOf_inj ((mem_origSlots a (s.1, a s.1 - 1 - s.2)).2
    (show a s.1 - 1 - s.2 < a s.1 by omega))).1 h
  obtain ⟨h31, h32⟩ := Prod.mk.inj h2
  have heq : s = s' := by
    refine Prod.ext h31 ?_
    rw [h31] at h32 hs
    omega
  exact Fin.ext ((nodup_origSlots a).getElem_inj_iff.1 heq)

end LayoutPermAux

open LayoutPermAux

/-- **Lemma 6.3, positional maps** (`lem:walsh-layout`, eq. (`eq:unshuffle`)): for `1 ≤ K`, `ℓ ≥ 2` and
`a_i ∈ {ℓ-1, ℓ}`, `L` and `B` are bijections of the `m₀` positions, and
`U = invFunFin (L ∘ B)` is a two-sided inverse of `L ∘ B`. (`K ≤ ℓ - 1` is not needed.) -/
theorem walsh_layout_perm : WalshLayoutPermStmt := by
  intro D ℓ K a hK1 hKℓ hℓ ha
  have hK : 0 < K := by omega
  have hL : Function.Bijective (layoutL ℓ K a) :=
    Finite.injective_iff_bijective.mp (layoutL_injective ℓ K a hK hℓ ha)
  have hB : Function.Bijective (bitRevB a) :=
    Finite.injective_iff_bijective.mp (bitRevB_injective a)
  have hLB : Function.Bijective (fun p => layoutL ℓ K a (bitRevB a p)) := hL.comp hB
  exact ⟨hL, hB, fun p => invFunFin_left_inv _ hLB p, fun p => invFunFin_spec _ hLB p⟩

/-- **Lemma 6.3, chunk rounds are layer shapes** (`lem:walsh-layout`): for a
round at slot `v ∈ [b₀, ℓ-2]`, every axis participates, its slot `(i, v)` lies in chunk
`j = ⌊(ℓ-2-v)/K⌋` at offset `(ℓ-2-v) mod K = K - 1 - ((v - b₀) mod K)` from the start of the
chunk, i.e. at bit `(v - b₀) mod K` from the least significant end, and the selected positions are
exactly `slicePos m₀ K (n_P + j D K) D ((v - b₀) mod K)`. -/
theorem walsh_layout_round_slice : WalshLayoutRoundSliceStmt := by
  intro D ℓ K a hK1 hKℓ hℓ ha v hv0 hv1
  have hK : 0 < K := by omega
  have hJ := jblk_mul_add_b0 ℓ K hK
  have hb := layoutB0_lt ℓ K hK
  have hm : addrBits a = prefixLen ℓ K a + layoutJblk ℓ K * (D * K) := by
    rw [← length_newSlots ℓ K a hK (by omega) ha, newSlots, List.length_append,
      length_chunkSlots, prefixLen]
  have hjJ : (ℓ - 2 - v) / K < layoutJblk ℓ K := chunk_index_lt ℓ K v hK hv0 hv1
  have hjt := Nat.div_add_mod' (ℓ - 2 - v) K
  have htK : (ℓ - 2 - v) % K < K := Nat.mod_lt _ hK
  -- the offset `t = (ℓ-2-v) mod K` equals `K - 1 - ((v - b₀) mod K)`
  have hρ : (ℓ - 2 - v) % K = K - 1 - (v - layoutB0 ℓ K) % K := by
    have hw := Nat.div_add_mod' (v - layoutB0 ℓ K) K
    have hr : (v - layoutB0 ℓ K) % K < K := Nat.mod_lt _ hK
    have hqJ : (v - layoutB0 ℓ K) / K < layoutJblk ℓ K := by
      rw [Nat.div_lt_iff_lt_mul hK]
      omega
    obtain ⟨c, hc⟩ : ∃ c, layoutJblk ℓ K = (v - layoutB0 ℓ K) / K + 1 + c :=
      ⟨layoutJblk ℓ K - ((v - layoutB0 ℓ K) / K + 1), by omega⟩
    have hJK : layoutJblk ℓ K * K = (v - layoutB0 ℓ K) / K * K + K + c * K := by
      rw [hc]
      ring
    have hn : ℓ - 2 - v = c * K + (K - 1 - (v - layoutB0 ℓ K) % K) := by omega
    rw [hn, Nat.mul_add_mod_of_lt (a := c)
      (show K - 1 - (v - layoutB0 ℓ K) % K < K by omega)]
  have hpos : ∀ i : Fin D, newPos ℓ K a (i, v) =
      prefixLen ℓ K a + (ℓ - 2 - v) / K * (D * K) + ((i : ℕ) * K + (ℓ - 2 - v) % K) := by
    intro i
    have h := newPos_chunk ℓ K a hK ((ℓ - 2 - v) / K) ((ℓ - 2 - v) % K) hjJ htK i
    have hv : ℓ - 2 - (ℓ - 2 - v) / K * K - (ℓ - 2 - v) % K = v := by omega
    rw [hv] at h
    exact h
  have e1 : (ℓ - 2 - v) / K * D * K = (ℓ - 2 - v) / K * (D * K) := Nat.mul_assoc _ _ _
  refine ⟨?_, ?_⟩
  · rw [hm]
    have h1 : ((ℓ - 2 - v) / K + 1) * (D * K) ≤ layoutJblk ℓ K * (D * K) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  · ext p
    simp only [roundSet, slicePos, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, _, hi⟩
      rw [hpos i] at hi
      have hiK : ((i : ℕ) + 1) * K ≤ D * K :=
        Nat.mul_le_mul_right K (show (i : ℕ) + 1 ≤ D from i.isLt)
      rw [Nat.add_mul, Nat.one_mul] at hiK
      refine ⟨by omega, by omega, ?_⟩
      have hsub : (p : ℕ) - (prefixLen ℓ K a + (ℓ - 2 - v) / K * D * K) =
          (i : ℕ) * K + (ℓ - 2 - v) % K := by
        omega
      rw [hsub, Nat.mul_add_mod_of_lt htK]
      exact hρ
    · rintro ⟨h1, h2, h3⟩
      have hqlt : (p : ℕ) - (prefixLen ℓ K a + (ℓ - 2 - v) / K * D * K) < D * K := by omega
      have hiD := (Nat.div_lt_iff_lt_mul hK).2 hqlt
      have hqd := Nat.div_add_mod' ((p : ℕ) - (prefixLen ℓ K a + (ℓ - 2 - v) / K * D * K)) K
      rw [h3, ← hρ] at hqd
      refine ⟨⟨_, hiD⟩, by rcases ha ⟨_, hiD⟩ with h | h <;> omega, ?_⟩
      rw [hpos]
      simp only
      omega

/-- **Lemma 6.3, natural-order restoration** (`lem:walsh-layout`, eq. (`eq:unshuffle`)):
`U (L (B w)) = w`, from `U ∘ L ∘ B = id` (`walsh_layout_perm`) and the composition rule of
`posPermArr`. -/
theorem walsh_layout_unshuffle : WalshLayoutUnshuffleStmt := by
  intro D ℓ K a hK1 hKℓ hℓ ha r w
  have h3 := (walsh_layout_perm ℓ K a hK1 hKℓ hℓ ha).2.2.1
  funext y k
  simp only [posPermArr, h3]

end SubNLogN.Math.Walsh
