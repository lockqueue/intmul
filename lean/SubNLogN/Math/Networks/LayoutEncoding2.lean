import SubNLogN.Math.Networks.LayoutEncoding

/-!
# Layout encoding, part 2: role arrays and node operations

For a node split on the row field `ℓ` into `W` roles (`W ∣ r ℓ`; `S = place L.n ℓ` records per row):
* `Layout.roleLayout ℓ W` (field `ℓ` of range `r ℓ / W`) and `Layout.roleEmbed ℓ W k` (row
  `x'_ℓ ↦ x'_ℓ · W + k`); `lexEquiv_roleEmbed` (the index of a role address);
* `roleBlocks_enc`: `roleBlocks W k S (L.enc A)` is the list of the role array
  `A ∘ roleEmbed k` on the role layout;
* reassembly by `mergeBlocks`, the node operations `relabelRun` (merge order `π.symm`) and `gateRun`
  (pointwise on aligned role lists), class-locality of `Step.runIn`, nested classes.
-/

namespace SubNLogN.Math.Networks.Model

open LayoutEncodingAux

/-! ### List lemmas for role arrays -/

namespace LayoutEncodingAux

theorem range_mul (a b : ℕ) :
    List.range (a * b) = (List.range a).flatMap fun i => (List.range b).map fun j => i * b + j := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append]
    simp

theorem flatMap_range_ite {α : Type} (W k : ℕ) (hk : k < W) (X : ℕ → List α) :
    ((List.range W).flatMap fun c => if c = k then X c else []) = X k := by
  induction W with
  | zero => omega
  | succ W ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hkW : k < W
    · rw [ih hkW]
      simp [show W ≠ k by omega]
    · have hkW' : k = W := by omega
      subst hkW'
      have h0 : ((List.range k).flatMap fun c => if c = k then X c else []) = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro c hc
        rw [List.mem_range] at hc
        rw [if_neg (by omega)]
      rw [h0]
      simp

/-- Index of the `y`-th record of role `k`: rows of `S` records, `R` rows per prefix block, the role
of a row is its row index mod `W` (`W ∣ R`), and role `k`'s rows are listed in order. -/
def roleIdxMap (R S W k y : ℕ) : ℕ :=
  y / (R / W * S) * (R * S) + (y / S % (R / W) * W + k) * S + y % S

theorem roleIdxMap_eq (R' S W k t l : ℕ) (hl : l < S) (hW : 0 < W) :
    roleIdxMap (R' * W) S W k (t * S + l) = (t / R' * R' * W + t % R' * W + k) * S + l := by
  have hS : 0 < S := by omega
  unfold roleIdxMap
  rw [Nat.mul_div_cancel _ hW]
  have h1 : (t * S + l) / S = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hl, zero_add]
  have h2 : (t * S + l) % S = l := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  have h3 : (t * S + l) / (R' * S) = t / R' := by
    rw [Nat.mul_comm R' S, ← Nat.div_div_eq_div_mul, h1]
  rw [h1, h2, h3]
  ring

theorem roleIdxMap_eq' (R' S W k t l : ℕ) (hl : l < S) (hW : 0 < W) :
    roleIdxMap (R' * W) S W k (t * S + l) = (t * W + k) * S + l := by
  rw [roleIdxMap_eq R' S W k t l hl hW]
  have h := Nat.div_add_mod t R'
  conv_rhs => rw [← h]
  ring

/-- Role `k` of a list of `N0 · R · S` records (rows of `S` records, role of a row = row index mod
`W`, `W ∣ R`) is the list of the records `roleIdxMap R S W k y`, `y < N0 · (R / W) · S`. -/
theorem roleBlocks_map_range {α : Type} (F : ℕ → α) (N0 R S W k : ℕ) (hW : 0 < W)
    (hWR : W ∣ R) (hk : k < W) :
    roleBlocks W k S ((List.range (N0 * R * S)).map F) =
      (List.range (N0 * (R / W) * S)).map (fun y => F (roleIdxMap R S W k y)) := by
  obtain ⟨R', rfl⟩ := hWR
  have hR' : W * R' / W = R' := Nat.mul_div_cancel_left R' hW
  rw [hR']
  unfold roleBlocks
  rw [List.length_map, List.length_range]
  have e1 : (List.range (N0 * (W * R') * S)).filterMap
      (fun x => if x / S % W = k then ((List.range (N0 * (W * R') * S)).map F)[x]? else none) =
      (List.range (N0 * (W * R') * S)).filterMap
        (fun x => if x / S % W = k then some (F x) else none) := by
    apply List.filterMap_congr
    intro x hx
    rw [List.mem_range] at hx
    simp only [List.getElem?_map, List.getElem?_range hx, Option.map_some]
  rw [e1, show N0 * (W * R') * S = (N0 * R') * W * S by ring, range_mul, range_mul (N0 * R') W]
  rw [show N0 * R' * S = (N0 * R') * S by ring, range_mul (N0 * R') S]
  simp only [List.flatMap_assoc, List.filterMap_flatMap, List.flatMap_map, List.filterMap_map,
    List.map_flatMap, List.map_map]
  refine List.flatMap_congr fun t _ => ?_
  have hc : ∀ c ∈ List.range W,
      ((List.range S).filterMap ((fun x => if x / S % W = k then some (F x) else none) ∘
        fun j => (t * W + c) * S + j)) =
      if c = k then (List.range S).map (fun l => F ((t * W + c) * S + l)) else [] := by
    intro c hc
    rw [List.mem_range] at hc
    have hcond : ∀ l, l < S → ((t * W + c) * S + l) / S % W = c := by
      intro l hl
      have hS : 0 < S := by omega
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hl, zero_add,
        Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
    by_cases hck : c = k
    · rw [if_pos hck]
      rw [← List.filterMap_eq_map]
      apply List.filterMap_congr
      intro l hl
      rw [List.mem_range] at hl
      simp only [Function.comp_apply]
      rw [hcond l hl, if_pos hck]
    · rw [if_neg hck]
      rw [List.filterMap_eq_nil_iff]
      intro l hl
      rw [List.mem_range] at hl
      simp only [Function.comp_apply]
      rw [hcond l hl, if_neg hck]
  rw [List.flatMap_congr hc, flatMap_range_ite W k hk]
  refine List.map_congr_left fun l hl => ?_
  rw [List.mem_range] at hl
  simp only [Function.comp_apply]
  rw [Nat.mul_comm W R', roleIdxMap_eq' R' S W k t l hl hW]

theorem take_drop_map_range {α : Type} (G : ℕ → α) (N a b : ℕ) (h : a + b ≤ N) :
    (((List.range N).map G).drop a).take b = (List.range b).map (fun l => G (a + l)) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range]
    omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]

theorem flatMap_finRange {α : Type} (W : ℕ) (H : ℕ → List α) :
    ((List.finRange W).flatMap fun c => H c.val) = (List.range W).flatMap H := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]

/-- Merging the `W` roles of a list of `N0 · (W · R') · S` records in class order `ord`. -/
theorem mergeBlocks_roleBlocks_map_range {α : Type} (F : ℕ → α) (N0 R' S W : ℕ) (hW : 0 < W)
    (ord : Fin W → Fin W) :
    mergeBlocks W ord (N0 * R') S
        (fun c => roleBlocks W c.val S ((List.range (N0 * (W * R') * S)).map F)) =
      (List.range (N0 * R')).flatMap fun t => (List.finRange W).flatMap fun c =>
        (List.range S).map fun l => F ((t * W + (ord c).val) * S + l) := by
  unfold mergeBlocks
  refine List.flatMap_congr fun t ht => ?_
  rw [List.mem_range] at ht
  refine List.flatMap_congr fun c _ => ?_
  have hR' : W * R' / W = R' := Nat.mul_div_cancel_left R' hW
  dsimp only
  rw [roleBlocks_map_range F N0 (W * R') S W (ord c).val hW (Dvd.intro R' rfl) (ord c).isLt,
    hR', take_drop_map_range]
  · refine List.map_congr_left fun l hl => ?_
    rw [List.mem_range] at hl
    rw [Nat.mul_comm W R', roleIdxMap_eq' R' S W (ord c).val t l hl hW]
  · have h1 : t + 1 ≤ N0 * R' := ht
    calc t * S + S = (t + 1) * S := by ring
      _ ≤ N0 * R' * S := Nat.mul_le_mul_right S h1

/-- A list of `N0 · (W · R') · S` records, grouped by rows `t·W + c` of `S` records. -/
theorem map_range_rows {α : Type} (F : ℕ → α) (N0 R' S W : ℕ) :
    (List.range (N0 * (W * R') * S)).map F =
      (List.range (N0 * R')).flatMap fun t => (List.range W).flatMap fun c =>
        (List.range S).map fun l => F ((t * W + c) * S + l) := by
  rw [show N0 * (W * R') * S = N0 * R' * W * S by ring, range_mul, range_mul (N0 * R') W]
  simp only [List.flatMap_assoc, List.map_flatMap, List.flatMap_map, List.map_map]
  rfl

end LayoutEncodingAux

/-! ### Role arrays -/

namespace Layout

variable (L : Layout)

/-- The index decomposition `card = (∏_{j<ℓ} r j) · r ℓ · (∏_{j>ℓ} r j)` around a field `ℓ`. -/
theorem card_eq_split (ℓ : Fin L.n) : L.card = L.blockRange 0 ℓ.val * L.r ℓ * L.place L.n ℓ := by
  rw [← L.blockRange_zero_n, blockRange_split (Nat.zero_le ℓ.val) (Nat.le_of_lt ℓ.isLt),
    blockRange_split (Nat.le_succ ℓ.val) ℓ.isLt, blockRange_single, ← place_eq_blockRange,
    mul_assoc]

/-- The layout of one role array of a node split on field `ℓ` into `W` roles: field `ℓ` has range
`r ℓ / W`, all other fields are unchanged. -/
abbrev roleLayout (ℓ : Fin L.n) (W : ℕ) : Layout where
  n := L.n
  r := fun i => if i = ℓ then L.r ℓ / W else L.r i

theorem roleLayout_r_self (ℓ : Fin L.n) (W : ℕ) : (L.roleLayout ℓ W).r ℓ = L.r ℓ / W :=
  if_pos rfl

theorem roleLayout_r_of_ne {ℓ i : Fin L.n} (W : ℕ) (h : i ≠ ℓ) : (L.roleLayout ℓ W).r i = L.r i :=
  if_neg h

theorem role_lt {x W k R : ℕ} (hk : k < W) (hWR : W ∣ R) (hx : x < R / W) : x * W + k < R := by
  obtain ⟨m, rfl⟩ := hWR
  have hW : 0 < W := by omega
  rw [Nat.mul_div_cancel_left m hW] at hx
  calc x * W + k < x * W + W := by omega
    _ = (x + 1) * W := by ring
    _ ≤ m * W := Nat.mul_le_mul_right W hx
    _ = W * m := by ring

/-- The address of role `k` at position `x'` of the role array (row `x'_ℓ · W + k`). -/
def roleEmbed (ℓ : Fin L.n) (W : ℕ) (hWr : W ∣ L.r ℓ) (k : Fin W) :
    (L.roleLayout ℓ W).Addr → L.Addr := fun x' i =>
  ⟨if i = ℓ then (x' i).val * W + k.val else (x' i).val, by
    by_cases h : i = ℓ
    · rw [if_pos h]
      have hx : (x' i).val < L.r ℓ / W :=
        lt_of_lt_of_eq (x' i).isLt (by rw [h]; exact L.roleLayout_r_self ℓ W)
      calc (x' i).val * W + k.val < L.r ℓ := role_lt k.isLt hWr hx
        _ = L.r i := by rw [h]
    · rw [if_neg h]
      exact lt_of_lt_of_eq (x' i).isLt (L.roleLayout_r_of_ne W h)⟩

theorem roleEmbed_apply_self {ℓ : Fin L.n} {W : ℕ} (hWr : W ∣ L.r ℓ) (k : Fin W)
    (x' : (L.roleLayout ℓ W).Addr) : (L.roleEmbed ℓ W hWr k x' ℓ).val = (x' ℓ).val * W + k.val :=
  if_pos rfl

theorem roleEmbed_apply_of_ne {ℓ i : Fin L.n} {W : ℕ} (hWr : W ∣ L.r ℓ) (k : Fin W)
    (x' : (L.roleLayout ℓ W).Addr) (h : i ≠ ℓ) : (L.roleEmbed ℓ W hWr k x' i).val = (x' i).val :=
  if_neg h

theorem roleLayout_blockRange {ℓ : Fin L.n} (W : ℕ) {t₀ t₁ : ℕ}
    (h : t₁ ≤ ℓ.val ∨ ℓ.val < t₀) : (L.roleLayout ℓ W).blockRange t₀ t₁ = L.blockRange t₀ t₁ := by
  unfold Layout.blockRange
  refine Finset.prod_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
  refine L.roleLayout_r_of_ne W fun hjl => ?_
  rw [hjl] at hj
  omega

theorem roleLayout_blockVal {ℓ : Fin L.n} {W : ℕ} (hWr : W ∣ L.r ℓ) (k : Fin W)
    (x' : (L.roleLayout ℓ W).Addr) {t₀ t₁ : ℕ} (h : t₁ ≤ ℓ.val ∨ ℓ.val < t₀) :
    (L.roleLayout ℓ W).blockVal t₀ t₁ x' = L.blockVal t₀ t₁ (L.roleEmbed ℓ W hWr k x') := by
  unfold Layout.blockVal
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
  have hjl : j ≠ ℓ := fun hjl => by rw [hjl] at hj; omega
  rw [L.roleEmbed_apply_of_ne hWr k x' hjl]
  congr 1
  unfold Layout.place
  refine Finset.prod_congr rfl fun j' hj' => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
  have hlt := Fin.lt_def.1 hj'.1
  refine L.roleLayout_r_of_ne W fun h' => ?_
  rw [h'] at hlt hj'
  omega

theorem roleLayout_card {ℓ : Fin L.n} (W : ℕ) :
    (L.roleLayout ℓ W).card = L.blockRange 0 ℓ.val * (L.r ℓ / W) * L.place L.n ℓ := by
  rw [(L.roleLayout ℓ W).card_eq_split ℓ, L.roleLayout_blockRange W (Or.inl le_rfl),
    L.roleLayout_r_self, place_eq_blockRange, place_eq_blockRange,
    L.roleLayout_blockRange W (Or.inr (by omega))]

/-- The index of a role address: `roleIdxMap` of the index in the role array. -/
theorem lexEquiv_roleEmbed {ℓ : Fin L.n} {W : ℕ} (hW : 0 < W) (hWr : W ∣ L.r ℓ) (k : Fin W)
    (x' : (L.roleLayout ℓ W).Addr) :
    (L.lexEquiv (L.roleEmbed ℓ W hWr k x')).val =
      roleIdxMap (L.r ℓ) (L.place L.n ℓ) W k.val ((L.roleLayout ℓ W).lexEquiv x').val := by
  have hℓ : ℓ.val + 1 ≤ L.n := ℓ.isLt
  have hl1 : ℓ.val ≤ ℓ.val + 1 := by omega
  have hl2 : ℓ.val < ℓ.val + 1 := by omega
  have e1 := L.idx_decomp hl1 hℓ (L.roleEmbed ℓ W hWr k x')
  have e2 := (L.roleLayout ℓ W).idx_decomp hl1 hℓ x'
  rw [blockRange_single, blockVal_single, ← place_eq_blockRange, L.roleEmbed_apply_self,
    ← L.roleLayout_blockVal hWr k x' (Or.inl le_rfl),
    ← L.roleLayout_blockVal hWr k x' (Or.inr hl2)] at e1
  have hRS : (L.roleLayout ℓ W).blockRange ℓ.val (ℓ.val + 1) = L.r ℓ / W := by
    rw [blockRange_single (L := L.roleLayout ℓ W) ℓ]
    exact L.roleLayout_r_self ℓ W
  rw [blockVal_single (L := L.roleLayout ℓ W) ℓ, hRS, L.roleLayout_blockRange W (Or.inr hl2),
    ← place_eq_blockRange] at e2
  have hQ := blockVal_lt (L := L.roleLayout ℓ W) (ℓ.val + 1) L.n x'
  rw [L.roleLayout_blockRange W (Or.inr hl2), ← place_eq_blockRange] at hQ
  rw [e1, e2]
  have hR : L.r ℓ = L.r ℓ / W * W := (Nat.div_mul_cancel hWr).symm
  generalize (x' ℓ).val = ρ
  generalize (L.roleLayout ℓ W).blockVal 0 ℓ.val x' = P
  generalize (L.roleLayout ℓ W).blockVal (ℓ.val + 1) L.n x' = Q at hQ ⊢
  generalize L.place L.n ℓ = S at hQ ⊢
  generalize L.r ℓ / W = R' at hR ⊢
  rw [hR, show P * (R' * S) + ρ * S + Q = (P * R' + ρ) * S + Q by ring,
    roleIdxMap_eq' R' S W k.val (P * R' + ρ) Q hQ hW]
  ring

/-- **Role arrays**: role `k` of a node split on field `ℓ` into `W` roles (`W ∣ r ℓ`), read in
increasing index order (`roleBlocks W k S`, `S = place L.n ℓ` records per row), is the list of
the role array `A ∘ roleEmbed k` on the role layout. -/
theorem roleBlocks_enc {β : Type} (A : L.Addr → β) (ℓ : Fin L.n) {W : ℕ} (hW : 0 < W)
    (hWr : W ∣ L.r ℓ) (k : Fin W) :
    roleBlocks W k.val (L.place L.n ℓ) (L.enc A) =
      (L.roleLayout ℓ W).enc (A ∘ L.roleEmbed ℓ W hWr k) := by
  have hcard := L.card_eq_split ℓ
  have hcard' := L.roleLayout_card (ℓ := ℓ) W
  by_cases h0 : L.card = 0
  · have hl : L.enc A = [] := List.eq_nil_of_length_eq_zero (by rw [enc_length, h0])
    have hl' : (L.roleLayout ℓ W).enc (A ∘ L.roleEmbed ℓ W hWr k) = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [enc_length, hcard']
      rw [hcard] at h0
      rcases Nat.mul_eq_zero.1 h0 with h | h
      · rcases Nat.mul_eq_zero.1 h with h | h
        · rw [h]; simp
        · rw [h]; simp
      · rw [h]; simp
    rw [hl, hl']
    rfl
  · have hpos : 0 < L.card := Nat.pos_of_ne_zero h0
    obtain ⟨d0, -⟩ : ∃ d : β, d = A (L.lexEquiv.symm ⟨0, hpos⟩) := ⟨_, rfl⟩
    have hv : L.enc A = (List.range L.card).map (fun x => (L.enc A).getD x d0) := by
      apply List.ext_getElem
      · simp [enc_length]
      · intro y h1 h2
        simp only [List.getElem_map, List.getElem_range]
        rw [List.getD_eq_getElem _ _ h1]
    have key := roleBlocks_map_range (fun x => (L.enc A).getD x d0) (L.blockRange 0 ℓ.val)
      (L.r ℓ) (L.place L.n ℓ) W k.val hW hWr k.isLt
    rw [← hcard, ← hv] at key
    rw [key]
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, enc_length, hcard']
    · intro y h1 h2
      have hy' : y < (L.roleLayout ℓ W).card := by rwa [enc_length] at h2
      simp only [List.getElem_map, List.getElem_range]
      have hidx : roleIdxMap (L.r ℓ) (L.place L.n ℓ) W k.val y =
          (L.lexEquiv (L.roleEmbed ℓ W hWr k
            ((L.roleLayout ℓ W).lexEquiv.symm ⟨y, hy'⟩))).val := by
        rw [L.lexEquiv_roleEmbed hW hWr k, Equiv.apply_symm_apply]
      rw [hidx, L.enc_getD A (Fin.isLt _), Fin.eta, Equiv.symm_apply_apply, enc_getElem]
      rfl

end Layout

/-! ### Reassembly, relabelling, gates -/

namespace Layout

variable (L : Layout)

theorem top_mem (ℓ : Fin L.n) (x : L.Addr) : (RowClass.top ℓ).mem x := by
  show (x ℓ).val % 1 = 0
  exact Nat.mod_one _

theorem roleIdx_top_roleEmbed {ℓ : Fin L.n} {W : ℕ} (hW : 0 < W) (hWr : W ∣ L.r ℓ) (k : Fin W)
    (x' : (L.roleLayout ℓ W).Addr) :
    roleIdx (RowClass.top ℓ) W hW (L.roleEmbed ℓ W hWr k x') = k := by
  apply Fin.ext
  show (L.roleEmbed ℓ W hWr k x' ℓ).val / 1 % W = k.val
  rw [L.roleEmbed_apply_self, Nat.div_one, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt k.isLt]

theorem aligned_top_roleEmbed {ℓ : Fin L.n} {W : ℕ} (hW : 0 < W) (hWr : W ∣ L.r ℓ)
    (k k' : Fin W) (x' : (L.roleLayout ℓ W).Addr) :
    aligned (RowClass.top ℓ) W (L.roleEmbed ℓ W hWr k x') k'.val = L.roleEmbed ℓ W hWr k' x' := by
  have hpos : rolePos (RowClass.top ℓ) W (L.roleEmbed ℓ W hWr k x') = (x' ℓ).val := by
    show (L.roleEmbed ℓ W hWr k x' ℓ).val / 1 / W = (x' ℓ).val
    rw [L.roleEmbed_apply_self, Nat.div_one, Nat.add_comm, Nat.add_mul_div_right _ _ hW,
      Nat.div_eq_of_lt k.isLt, zero_add]
  unfold aligned
  rw [hpos]
  show withRow ℓ (L.roleEmbed ℓ W hWr k x') (0 + 1 * (k'.val + W * (x' ℓ).val)) = _
  have hlt : 0 + 1 * (k'.val + W * (x' ℓ).val) < L.r ℓ := by
    have h := (L.roleEmbed ℓ W hWr k' x' ℓ).isLt
    rw [L.roleEmbed_apply_self] at h
    calc 0 + 1 * (k'.val + W * (x' ℓ).val) = (x' ℓ).val * W + k'.val := by ring
      _ < L.r ℓ := h
  unfold withRow
  rw [dif_pos hlt]
  funext i
  by_cases hi : i = ℓ
  · rw [hi, Function.update_self]
    apply Fin.ext
    rw [L.roleEmbed_apply_self]
    show 0 + 1 * (k'.val + W * (x' ℓ).val) = (x' ℓ).val * W + k'.val
    ring
  · rw [Function.update_of_ne hi]
    apply Fin.ext
    rw [L.roleEmbed_apply_of_ne hWr k x' hi, L.roleEmbed_apply_of_ne hWr k' x' hi]

theorem roleLayout_card_mul {ℓ : Fin L.n} {W : ℕ} (hWr : W ∣ L.r ℓ) :
    (L.roleLayout ℓ W).card * W = L.card := by
  rw [L.roleLayout_card, L.card_eq_split ℓ]
  have h := Nat.div_mul_cancel hWr
  calc L.blockRange 0 ℓ.val * (L.r ℓ / W) * L.place L.n ℓ * W =
      L.blockRange 0 ℓ.val * (L.r ℓ / W * W) * L.place L.n ℓ := by ring
    _ = _ := by rw [h]

/-- **Reassembly**: merging the `W` role lists in class order reproduces the list of the array. -/
theorem enc_reassemble {β : Type} (A : L.Addr → β) (ℓ : Fin L.n) {W : ℕ} (hW : 0 < W)
    (hWr : W ∣ L.r ℓ) :
    mergeBlocks W id (L.blockRange 0 ℓ.val * L.r ℓ / W) (L.place L.n ℓ)
      (fun c => roleBlocks W c.val (L.place L.n ℓ) (L.enc A)) = L.enc A := by
  obtain ⟨R', hR'⟩ := hWr
  have hg : L.blockRange 0 ℓ.val * L.r ℓ / W = L.blockRange 0 ℓ.val * R' := by
    rw [hR', show L.blockRange 0 ℓ.val * (W * R') = W * (L.blockRange 0 ℓ.val * R') by ring,
      Nat.mul_div_cancel_left _ hW]
  have hcard : L.card = L.blockRange 0 ℓ.val * (W * R') * L.place L.n ℓ := by
    rw [L.card_eq_split ℓ, hR']
  rw [hg]
  by_cases h0 : L.card = 0
  · have hl : L.enc A = [] := List.eq_nil_of_length_eq_zero (by rw [enc_length, h0])
    rw [hl]
    simp [mergeBlocks, roleBlocks]
  · have hpos : 0 < L.card := Nat.pos_of_ne_zero h0
    obtain ⟨d0, -⟩ : ∃ d : β, d = A (L.lexEquiv.symm ⟨0, hpos⟩) := ⟨_, rfl⟩
    have hv : L.enc A = (List.range L.card).map (fun x => (L.enc A).getD x d0) := by
      apply List.ext_getElem
      · simp [enc_length]
      · intro y h1 h2
        simp only [List.getElem_map, List.getElem_range]
        rw [List.getD_eq_getElem _ _ h1]
    rw [hv, hcard, mergeBlocks_roleBlocks_map_range _ _ _ _ _ hW, map_range_rows]
    refine List.flatMap_congr fun t _ => ?_
    exact flatMap_finRange W (fun c => List.map
      (fun l => (L.enc A).getD ((t * W + c) * L.place L.n ℓ + l) d0) (List.range (L.place L.n ℓ)))

theorem relabelRun_top_roleEmbed {β : Type} (A : L.Addr → β) {ℓ : Fin L.n} {W : ℕ} (hW : 0 < W)
    (hWr : W ∣ L.r ℓ) (π : Equiv.Perm (Fin W)) (k : Fin W) :
    (relabelRun (RowClass.top ℓ) W hW π A) ∘ L.roleEmbed ℓ W hWr k =
      A ∘ L.roleEmbed ℓ W hWr (π.symm k) := by
  funext x'
  show (if (RowClass.top ℓ).mem (L.roleEmbed ℓ W hWr k x') then _ else _) = _
  rw [if_pos (L.top_mem ℓ _), L.roleIdx_top_roleEmbed hW hWr k x',
    L.aligned_top_roleEmbed hW hWr k (π.symm k) x']
  rfl

/-- **Relabel and merge**: a node's final relabelling `π` (role `k` receives the stream of role
`π⁻¹ k`) is `mergeBlocks` in class order `π.symm`. -/
theorem enc_relabelRun {β : Type} (A : L.Addr → β) (ℓ : Fin L.n) {W : ℕ} (hW : 0 < W)
    (hWr : W ∣ L.r ℓ) (π : Equiv.Perm (Fin W)) :
    L.enc (relabelRun (RowClass.top ℓ) W hW π A) =
      mergeBlocks W π.symm (L.blockRange 0 ℓ.val * L.r ℓ / W) (L.place L.n ℓ)
        (fun c => roleBlocks W c.val (L.place L.n ℓ) (L.enc A)) := by
  rw [← L.enc_reassemble (relabelRun (RowClass.top ℓ) W hW π A) ℓ hW hWr]
  have h : ∀ c : Fin W, roleBlocks W c.val (L.place L.n ℓ)
      (L.enc (relabelRun (RowClass.top ℓ) W hW π A)) =
      roleBlocks W (π.symm c).val (L.place L.n ℓ) (L.enc A) := by
    intro c
    rw [L.roleBlocks_enc _ ℓ hW hWr c, L.roleBlocks_enc _ ℓ hW hWr (π.symm c),
      L.relabelRun_top_roleEmbed A hW hWr π c]
  simp only [h]
  rfl

theorem gateRun_top_roleEmbed {β : Type} (A : L.Addr → β) {ℓ : Fin L.n} {W : ℕ} (hW : 0 < W)
    (hWr : W ∣ L.r ℓ) (G : (Fin W → β) → (Fin W → β)) (k : Fin W) :
    (gateRun (RowClass.top ℓ) W hW G A) ∘ L.roleEmbed ℓ W hWr k =
      fun x' => G (fun k' => A (L.roleEmbed ℓ W hWr k' x')) k := by
  funext x'
  show (if (RowClass.top ℓ).mem (L.roleEmbed ℓ W hWr k x') then _ else _) = _
  rw [if_pos (L.top_mem ℓ _), L.roleIdx_top_roleEmbed hW hWr k x']
  congr 1
  funext k'
  rw [L.aligned_top_roleEmbed hW hWr k k' x']

/-- **Gates**: a gate on the `W` aligned role streams acts position-wise on the `W` role lists. -/
theorem enc_gateRun {β : Type} [Inhabited β] (A : L.Addr → β) (ℓ : Fin L.n) {W : ℕ} (hW : 0 < W)
    (hWr : W ∣ L.r ℓ) (G : (Fin W → β) → (Fin W → β)) (k : Fin W) :
    roleBlocks W k.val (L.place L.n ℓ) (L.enc (gateRun (RowClass.top ℓ) W hW G A)) =
      (List.range (L.roleLayout ℓ W).card).map fun y =>
        G (fun k' => (roleBlocks W k'.val (L.place L.n ℓ) (L.enc A)).getD y default) k := by
  rw [L.roleBlocks_enc _ ℓ hW hWr k, L.gateRun_top_roleEmbed A hW hWr G k]
  apply List.ext_getElem
  · simp [enc_length]
  · intro y h1 h2
    have hy : y < (L.roleLayout ℓ W).card := by rwa [enc_length] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [enc_getElem]
    congr 1
    funext k'
    rw [L.roleBlocks_enc _ ℓ hW hWr k', enc_getD _ _ hy]
    rfl

/-! ### Classes: class lists, class-locality of steps, nested classes -/

theorem mem_roleEmbed (c : RowClass L) (hμr : c.μ ∣ L.r c.row) (k : Fin c.μ)
    (x' : (L.roleLayout c.row c.μ).Addr) :
    c.mem (L.roleEmbed c.row c.μ hμr k x') ↔ k.val = c.res := by
  show (L.roleEmbed c.row c.μ hμr k x' c.row).val % c.μ = c.res ↔ _
  rw [L.roleEmbed_apply_self, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt k.isLt]

/-- A step run in class `c` does not change the list of any other class `(c.row, c.μ, k)`. -/
theorem roleBlocks_enc_runIn_ne {β : Type} (A : L.Addr → β) (c : RowClass L)
    (hμr : c.μ ∣ L.r c.row) (s : Step L β) (k : Fin c.μ) (hk : k.val ≠ c.res) :
    roleBlocks c.μ k.val (L.place L.n c.row) (L.enc (s.runIn c A)) =
      roleBlocks c.μ k.val (L.place L.n c.row) (L.enc A) := by
  rw [L.roleBlocks_enc _ c.row c.hμ hμr k, L.roleBlocks_enc _ c.row c.hμ hμr k]
  congr 1
  funext x'
  show (if c.mem (L.roleEmbed c.row c.μ hμr k x') then _ else _) = _
  rw [if_neg (fun h => hk ((L.mem_roleEmbed c hμr k x').1 h))]
  rfl

/-- A step run in class `c` acts on the list of `c` (the class's role array) as `s.run`. -/
theorem roleBlocks_enc_runIn_self {β : Type} (A : L.Addr → β) (c : RowClass L)
    (hμr : c.μ ∣ L.r c.row) (s : Step L β) :
    roleBlocks c.μ c.res (L.place L.n c.row) (L.enc (s.runIn c A)) =
      (L.roleLayout c.row c.μ).enc (s.run A ∘ L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩) := by
  refine (L.roleBlocks_enc (s.runIn c A) c.row c.hμ hμr ⟨c.res, c.hres⟩).trans ?_
  congr 1
  funext x'
  show (if c.mem (L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ x') then _ else _) = _
  rw [if_pos ((L.mem_roleEmbed c hμr ⟨c.res, c.hres⟩ x').2 rfl)]
  rfl

/-- Nested classes: role `k` of class `c` (i.e. `c.sub W k`) is role `k` of `c`'s role array. -/
theorem mem_sub_roleEmbed (c : RowClass L) (hμr : c.μ ∣ L.r c.row) (W : ℕ) (hW : 0 < W)
    (k : Fin W) (x' : (L.roleLayout c.row c.μ).Addr) :
    (c.sub W hW k).mem (L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ x') ↔
      ((RowClass.top c.row : RowClass (L.roleLayout c.row c.μ)).sub W hW k).mem x' := by
  show (L.roleEmbed c.row c.μ hμr ⟨c.res, c.hres⟩ x' c.row).val % (c.μ * W) = c.res + c.μ * k.val ↔
    (x' c.row).val % (1 * W) = 0 + 1 * k.val
  rw [L.roleEmbed_apply_self, one_mul, zero_add, one_mul, Nat.mod_mul]
  have hμ := c.hμ
  have hres := c.hres
  have e1 : ((x' c.row).val * c.μ + c.res) % c.μ = c.res := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hres]
  have e2 : ((x' c.row).val * c.μ + c.res) / c.μ = (x' c.row).val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hμ, Nat.div_eq_of_lt hres, zero_add]
  rw [e1, e2]
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_left hμ (Nat.add_left_cancel h)
  · intro h
    rw [h]

end Layout

end SubNLogN.Math.Networks.Model
