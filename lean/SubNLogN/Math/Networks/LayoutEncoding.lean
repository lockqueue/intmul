import SubNLogN.Math.Networks.AppCModel

/-!
# Layout encoding: lexicographic indices of stream-model addresses (base half)

A fully proved library (no contracts, no hypotheses) for the machine-level refinement of the abstract stream
model of `AppCModel.lean` by list programs (`SubNLogN/Machine/Contracts/Streams.lean`, `AppC.lean`).

* `Layout.lexEquiv : L.Addr ≃ Fin L.card`: the lexicographic (mixed-radix, field `0` most
  significant) index of an address, `↑(lexEquiv x) = blockVal 0 L.n x`; digit `j` of an index `i`
  is `i / place L.n j % r j`.
* Digit-block extraction `Layout.idxBlock` (`blockVal_lexEquiv_symm`) and overwriting
  `Layout.idxSetBlock` (`lexEquiv_blockSet`, `lexEquiv_update`).
* `Layout.enc A = List.ofFn (A ∘ lexEquiv.symm)` (the machine list of an array) and the bridge
  `enc_comp`: an address pull becomes `permByInv` of its index map.
* Copies of the machine-layer list functions `permByInv`, `roleBlocks`, `mergeBlocks`, `swapFieldsInv`
  (identical bodies, hence definitionally equal to those in `Machine/Contracts/`; refer to them qualified).
* Row classes on indices (`RowClass.mem_lexEquiv_symm`, `RowClass.mem_iff_idx`), the cyclic split
  of `RowClass.sub` (`RowClass.mem_sub_iff`), and the role test of a split of the whole array
  (`RowClass.top_sub_mem_iff`).

Role arrays (`roleBlocks_enc`), reassembly by `mergeBlocks`, the node operations `gateRun` and
`relabelRun`, class-locality of `Step.runIn` and nested classes are in `LayoutEncoding2.lean`; the
Step ↔ index-map half is `LayoutEncodingStep.lean`. Both import this file. Generic block
lemmas (copied from `Proofs/InterchangeCorrectRadix.lean`) are in `Model.LayoutEncodingAux`.
-/

namespace SubNLogN.Math.Networks.Model

/-! ### Copies of the machine-layer list functions (`Streams.lean`, `AppC.lean`) -/

/-- (Matches `Machine/Contracts/`) An address permutation given by its inverse `g`: output record `y` is input
record `g y`. -/
def permByInv {α : Type} [Inhabited α] (g : ℕ → ℕ) (v : List α) : List α :=
  (List.range v.length).map fun y => v.getD (g y) default

/-- (Matches `Machine/Contracts/`) The rows of class `w` modulo `W`, in order, where row `r` is the block of records
`[r·s, (r+1)·s)`. -/
def roleBlocks {α : Type} (W w s : ℕ) (v : List α) : List α :=
  (List.range v.length).filterMap fun x => if x / s % W = w then v[x]? else none

/-- (Matches `Machine/Contracts/`) Merge `W` streams of `g` rows of `s` records each, in the fixed class order `ord`:
round `t` emits row `t` of streams `ord 0, ord 1, …, ord (W - 1)`. -/
def mergeBlocks {α : Type} (W : ℕ) (ord : Fin W → Fin W) (g s : ℕ) (us : Fin W → List α) :
    List α :=
  (List.range g).flatMap fun t =>
    (List.finRange W).flatMap fun c => ((us (ord c)).drop (t * s)).take s

/-- (Matches `Machine/Contracts/`) Inverse address map of the field interchange
`[A] × [Hh] × [G] × [Hd] × [B] → [A] × [Hd] × [G] × [Hh] × [B]`, `(a, h, g, d, z) ↦ (a, d, g, h, z)`. -/
def swapFieldsInv (Hh G Hd B : ℕ) (y : ℕ) : ℕ :=
  (((y / (B * Hh * G * Hd) * Hh + y / B % Hh) * G + y / (B * Hh) % G) * Hd +
    y / (B * Hh * G) % Hd) * B + y % B

/-! ### Generic block lemmas (copied from `Proofs/InterchangeCorrectRadix.lean`) -/

namespace LayoutEncodingAux

variable {L : Layout}

theorem blockSet_apply_of_not {t₀ t₁ : ℕ} (x : L.Addr) (v : ℕ) (j : Fin L.n)
    (hj : ¬ (t₀ ≤ j.val ∧ j.val < t₁)) : L.blockSet t₀ t₁ x v j = x j := by
  simp only [Layout.blockSet]
  rw [if_neg (show ¬ inBlock t₀ t₁ j from hj)]

theorem blockVal_congr {t₀ t₁ : ℕ} {x y : L.Addr}
    (h : ∀ j : Fin L.n, t₀ ≤ j.val → j.val < t₁ → x j = y j) :
    L.blockVal t₀ t₁ x = L.blockVal t₀ t₁ y := by
  unfold Layout.blockVal
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, inBlock] at hj
  rw [h j hj.2.1 hj.2.2]

lemma blockRange_of_le {t₀ t₁ : ℕ} (h : t₁ ≤ t₀) : L.blockRange t₀ t₁ = 1 := by
  unfold Layout.blockRange
  refine Finset.prod_eq_one fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
  omega

lemma blockVal_of_le {t₀ t₁ : ℕ} (h : t₁ ≤ t₀) (x : L.Addr) : L.blockVal t₀ t₁ x = 0 := by
  unfold Layout.blockVal
  refine Finset.sum_eq_zero fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
  omega

lemma blockRange_of_n_le {t₀ t₁ : ℕ} (h : L.n ≤ t₀) : L.blockRange t₀ t₁ = 1 := by
  unfold Layout.blockRange
  refine Finset.prod_eq_one fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
  have := j.isLt
  omega

lemma blockVal_of_n_le {t₀ t₁ : ℕ} (h : L.n ≤ t₀) (x : L.Addr) : L.blockVal t₀ t₁ x = 0 := by
  unfold Layout.blockVal
  refine Finset.sum_eq_zero fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
  have := j.isLt
  omega

lemma blockRange_pos (x : L.Addr) (t₀ t₁ : ℕ) : 0 < L.blockRange t₀ t₁ :=
  Finset.prod_pos fun j _ => Fin.pos (x j)

lemma blkF_union {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    Finset.univ.filter (inBlock a c (n := L.n)) =
      Finset.univ.filter (inBlock a b (n := L.n)) ∪ Finset.univ.filter (inBlock b c (n := L.n)) := by
  ext j
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, inBlock]
  omega

lemma blkF_disj (a b c : ℕ) :
    Disjoint (Finset.univ.filter (inBlock a b (n := L.n)))
      (Finset.univ.filter (inBlock b c (n := L.n))) := by
  rw [Finset.disjoint_left]
  intro j h1 h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at h1 h2
  omega

lemma blockRange_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    L.blockRange a c = L.blockRange a b * L.blockRange b c := by
  unfold Layout.blockRange
  rw [blkF_union hab hbc, Finset.prod_union (blkF_disj a b c)]

lemma place_eq_blockRange (t₁ : ℕ) (j : Fin L.n) :
    L.place t₁ j = L.blockRange (j.val + 1) t₁ := by
  unfold Layout.place Layout.blockRange
  congr 1

lemma place_split {b c : ℕ} (hbc : b ≤ c) (j : Fin L.n) (hj : j.val < b) :
    L.place c j = L.place b j * L.blockRange b c := by
  rw [place_eq_blockRange, place_eq_blockRange, blockRange_split (by omega) hbc]

lemma blockVal_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (x : L.Addr) :
    L.blockVal a c x = L.blockVal a b x * L.blockRange b c + L.blockVal b c x := by
  unfold Layout.blockVal
  rw [blkF_union hab hbc, Finset.sum_union (blkF_disj a b c), Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
  rw [place_split hbc j hj.2, mul_assoc]

lemma blkF_single (f : Fin L.n) :
    Finset.univ.filter (inBlock f.val (f.val + 1) (n := L.n)) = {f} := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock, Finset.mem_singleton,
    Fin.ext_iff]
  omega

lemma blockRange_single (f : Fin L.n) : L.blockRange f.val (f.val + 1) = L.r f := by
  unfold Layout.blockRange
  rw [blkF_single, Finset.prod_singleton]

lemma blockVal_single (f : Fin L.n) (x : L.Addr) : L.blockVal f.val (f.val + 1) x = (x f).val := by
  unfold Layout.blockVal
  rw [blkF_single, Finset.sum_singleton, place_eq_blockRange, blockRange_of_le (le_refl _),
    mul_one]

lemma blockVal_head_lt (t₀ : ℕ) (x : L.Addr) :
    L.blockVal t₀ (t₀ + 1) x < L.blockRange t₀ (t₀ + 1) := by
  by_cases hn : t₀ < L.n
  · obtain ⟨f, rfl⟩ : ∃ f : Fin L.n, f.val = t₀ := ⟨⟨t₀, hn⟩, rfl⟩
    rw [blockVal_single, blockRange_single]
    exact (x f).isLt
  · rw [blockVal_of_n_le (by omega), blockRange_of_n_le (by omega)]
    exact Nat.one_pos

lemma mixed_lt {a A b B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B :=
  calc a * B + b < a * B + B := by omega
    _ = (a + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ha)

lemma mod_div_mod (v P Q S : ℕ) : v % (P * Q * S) / S % Q = v / S % Q := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self v,
    Nat.mod_mod_of_dvd v (⟨P, by ring⟩ : S * Q ∣ P * Q * S)]

lemma blockVal_lt_aux (x : L.Addr) (t₁ : ℕ) :
    ∀ d t₀, t₁ - t₀ = d → L.blockVal t₀ t₁ x < L.blockRange t₀ t₁ := by
  intro d
  induction d with
  | zero =>
    intro t₀ hd
    rw [blockVal_of_le (by omega), blockRange_of_le (by omega)]
    exact Nat.one_pos
  | succ d ih =>
    intro t₀ hd
    have h1 : t₀ ≤ t₀ + 1 := Nat.le_succ t₀
    have h2 : t₀ + 1 ≤ t₁ := by omega
    rw [blockVal_split h1 h2, blockRange_split h1 h2]
    exact mixed_lt (blockVal_head_lt t₀ x) (ih (t₀ + 1) (by omega))

lemma blockVal_blockSet_aux (t₁ : ℕ) : ∀ d t₀, t₁ - t₀ = d → ∀ (x : L.Addr) (v : ℕ),
    L.blockVal t₀ t₁ (L.blockSet t₀ t₁ x v) = v % L.blockRange t₀ t₁ := by
  intro d
  induction d with
  | zero =>
    intro t₀ hd x v
    rw [blockVal_of_le (by omega), blockRange_of_le (by omega), Nat.mod_one]
  | succ d ih =>
    intro t₀ hd x v
    have h1 : t₀ ≤ t₀ + 1 := Nat.le_succ t₀
    have h2 : t₀ + 1 ≤ t₁ := by omega
    rw [blockVal_split h1 h2, blockRange_split h1 h2]
    have htail : L.blockVal (t₀ + 1) t₁ (L.blockSet t₀ t₁ x v) =
        v % L.blockRange (t₀ + 1) t₁ := by
      rw [← ih (t₀ + 1) (by omega) x v]
      apply blockVal_congr
      intro j hj1 hj2
      have hA : inBlock t₀ t₁ j := ⟨by omega, hj2⟩
      have hB : inBlock (t₀ + 1) t₁ j := ⟨hj1, hj2⟩
      simp only [Layout.blockSet, if_pos hA, if_pos hB]
    have hhead : L.blockVal t₀ (t₀ + 1) (L.blockSet t₀ t₁ x v) =
        v / L.blockRange (t₀ + 1) t₁ % L.blockRange t₀ (t₀ + 1) := by
      by_cases hn : t₀ < L.n
      · obtain ⟨f, rfl⟩ : ∃ f : Fin L.n, f.val = t₀ := ⟨⟨t₀, hn⟩, rfl⟩
        have hf : inBlock f.val t₁ f := ⟨le_refl _, by omega⟩
        rw [blockVal_single, blockRange_single]
        simp only [Layout.blockSet, if_pos hf]
        rw [place_eq_blockRange]
      · rw [blockVal_of_n_le (t₀ := t₀) (t₁ := t₀ + 1) (by omega),
          blockRange_of_n_le (t₀ := t₀) (t₁ := t₀ + 1) (by omega), Nat.mod_one]
    rw [htail, hhead, mul_comm (L.blockRange t₀ (t₀ + 1)), Nat.mod_mul]
    ring

lemma blockVal_sub_aux {t₀ u₀ u₁ t₁ : ℕ} (h₁ : t₀ ≤ u₀) (h₂ : u₀ ≤ u₁) (h₃ : u₁ ≤ t₁)
    (x : L.Addr) :
    L.blockVal u₀ u₁ x = L.blockVal t₀ t₁ x / L.blockRange u₁ t₁ % L.blockRange u₀ u₁ := by
  have e1 : (L.blockVal t₀ u₁ x * L.blockRange u₁ t₁ + L.blockVal u₁ t₁ x) / L.blockRange u₁ t₁ =
      L.blockVal t₀ u₁ x := by
    rw [add_comm, Nat.add_mul_div_right _ _ (blockRange_pos x u₁ t₁),
      Nat.div_eq_of_lt (blockVal_lt_aux x t₁ (t₁ - u₁) u₁ rfl), zero_add]
  rw [blockVal_split (h₁.trans h₂) h₃, e1, blockVal_split h₁ h₂, add_comm,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (blockVal_lt_aux x u₁ (u₁ - u₀) u₀ rfl)]

theorem blockVal_lt (t₀ t₁ : ℕ) (x : L.Addr) : L.blockVal t₀ t₁ x < L.blockRange t₀ t₁ :=
  blockVal_lt_aux x t₁ (t₁ - t₀) t₀ rfl

theorem blockVal_blockSet (t₀ t₁ : ℕ) (x : L.Addr) (v : ℕ) :
    L.blockVal t₀ t₁ (L.blockSet t₀ t₁ x v) = v % L.blockRange t₀ t₁ :=
  blockVal_blockSet_aux t₁ (t₁ - t₀) t₀ rfl x v

theorem blockSet_blockVal (t₀ t₁ : ℕ) (x : L.Addr) :
    L.blockSet t₀ t₁ x (L.blockVal t₀ t₁ x) = x := by
  funext j
  by_cases hj : inBlock t₀ t₁ j
  · simp only [Layout.blockSet, if_pos hj]
    refine Fin.ext ?_
    show L.blockVal t₀ t₁ x / L.place t₁ j % L.r j = (x j).val
    have h := blockVal_sub_aux (t₀ := t₀) (u₀ := j.val) (u₁ := j.val + 1) (t₁ := t₁) hj.1
      (Nat.le_succ _) hj.2 x
    rw [blockVal_single, blockRange_single, ← place_eq_blockRange] at h
    exact h.symm
  · simp only [Layout.blockSet, if_neg hj]

theorem blockVal_sub {t₀ u₀ u₁ t₁ : ℕ} (h₁ : t₀ ≤ u₀) (h₂ : u₀ ≤ u₁) (h₃ : u₁ ≤ t₁)
    (x : L.Addr) :
    L.blockVal u₀ u₁ x = L.blockVal t₀ t₁ x / L.blockRange u₁ t₁ % L.blockRange u₀ u₁ :=
  blockVal_sub_aux h₁ h₂ h₃ x

theorem blockVal_blockSet_of_disjoint {t₀ t₁ s₀ s₁ : ℕ} (h : t₁ ≤ s₀ ∨ s₁ ≤ t₀) (x : L.Addr)
    (v : ℕ) : L.blockVal s₀ s₁ (L.blockSet t₀ t₁ x v) = L.blockVal s₀ s₁ x := by
  refine blockVal_congr fun j hj₁ hj₂ => blockSet_apply_of_not x v j ?_
  omega

end LayoutEncodingAux

open LayoutEncodingAux

/-! ### The lexicographic index of an address -/

namespace Layout

variable (L : Layout)

theorem blockRange_zero_n : L.blockRange 0 L.n = L.card := by
  unfold Layout.blockRange Layout.card
  congr 1
  exact Finset.filter_true_of_mem fun j _ => ⟨Nat.zero_le _, j.isLt⟩

theorem r_pos_of_lt_card {y : ℕ} (hy : y < L.card) (j : Fin L.n) : 0 < L.r j := by
  have hc : L.card ≠ 0 := by omega
  unfold Layout.card at hc
  exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.1 hc j (Finset.mem_univ j))

/-- The lexicographic index of an address (field `0` most significant), `↑(lexEquiv x) =
blockVal 0 L.n x`; the inverse reads digit `j` of `i` as `i / place L.n j % r j`. -/
def lexEquiv : L.Addr ≃ Fin L.card where
  toFun x := ⟨L.blockVal 0 L.n x, by rw [← L.blockRange_zero_n]; exact blockVal_lt 0 L.n x⟩
  invFun i := fun j => ⟨i.val / L.place L.n j % L.r j,
    Nat.mod_lt _ (L.r_pos_of_lt_card i.isLt j)⟩
  left_inv x := by
    funext j
    have h := congrFun (blockSet_blockVal 0 L.n x) j
    simp only [Layout.blockSet, if_pos (show inBlock 0 L.n j from ⟨Nat.zero_le _, j.isLt⟩)] at h
    exact h
  right_inv i := by
    apply Fin.ext
    show L.blockVal 0 L.n (fun j => ⟨i.val / L.place L.n j % L.r j,
      Nat.mod_lt _ (L.r_pos_of_lt_card i.isLt j)⟩) = i.val
    have hd : (fun j => (⟨i.val / L.place L.n j % L.r j,
        Nat.mod_lt _ (L.r_pos_of_lt_card i.isLt j)⟩ : Fin (L.r j))) =
        L.blockSet 0 L.n (fun j => ⟨i.val / L.place L.n j % L.r j,
          Nat.mod_lt _ (L.r_pos_of_lt_card i.isLt j)⟩) i.val := by
      funext j
      simp only [Layout.blockSet, if_pos (show inBlock 0 L.n j from ⟨Nat.zero_le _, j.isLt⟩)]
    rw [hd, blockVal_blockSet, L.blockRange_zero_n, Nat.mod_eq_of_lt i.isLt]

@[simp] theorem lexEquiv_val (x : L.Addr) : (L.lexEquiv x).val = L.blockVal 0 L.n x := rfl

@[simp] theorem lexEquiv_symm_val (i : Fin L.card) (j : Fin L.n) :
    (L.lexEquiv.symm i j).val = i.val / L.place L.n j % L.r j := rfl

/-- Digit `j` of the index of `x` is the value of field `j`. -/
theorem field_eq_idx (x : L.Addr) (j : Fin L.n) :
    (x j).val = (L.lexEquiv x).val / L.place L.n j % L.r j := by
  have h := L.lexEquiv_symm_val (L.lexEquiv x) j
  rwa [Equiv.symm_apply_apply] at h

/-- The value of the block `[t₀, t₁)` read off an index. -/
def idxBlock (t₀ t₁ y : ℕ) : ℕ := y / L.blockRange t₁ L.n % L.blockRange t₀ t₁

/-- An index with the block `[t₀, t₁)` overwritten by `v` (modulo the block range). -/
def idxSetBlock (t₀ t₁ y v : ℕ) : ℕ :=
  y - L.idxBlock t₀ t₁ y * L.blockRange t₁ L.n + v % L.blockRange t₀ t₁ * L.blockRange t₁ L.n

/-- Digit-block extraction: the value of a block is read off the index. -/
theorem blockVal_eq_idxBlock {t₀ t₁ : ℕ} (h₁ : t₀ ≤ t₁) (h₂ : t₁ ≤ L.n) (x : L.Addr) :
    L.blockVal t₀ t₁ x = L.idxBlock t₀ t₁ (L.lexEquiv x).val :=
  blockVal_sub (Nat.zero_le _) h₁ h₂ x

theorem blockVal_lexEquiv_symm {t₀ t₁ : ℕ} (h₁ : t₀ ≤ t₁) (h₂ : t₁ ≤ L.n) (i : Fin L.card) :
    L.blockVal t₀ t₁ (L.lexEquiv.symm i) = L.idxBlock t₀ t₁ i.val := by
  rw [L.blockVal_eq_idxBlock h₁ h₂, Equiv.apply_symm_apply]

theorem idxBlock_single (j : Fin L.n) (y : ℕ) :
    L.idxBlock j.val (j.val + 1) y = y / L.place L.n j % L.r j := by
  unfold idxBlock
  rw [blockRange_single, ← place_eq_blockRange]

/-- The index split at a block `[t₀, t₁)`: prefix, block value, suffix. -/
theorem idx_decomp {t₀ t₁ : ℕ} (h₁ : t₀ ≤ t₁) (h₂ : t₁ ≤ L.n) (x : L.Addr) :
    (L.lexEquiv x).val = L.blockVal 0 t₀ x * (L.blockRange t₀ t₁ * L.blockRange t₁ L.n) +
      L.blockVal t₀ t₁ x * L.blockRange t₁ L.n + L.blockVal t₁ L.n x := by
  rw [lexEquiv_val, blockVal_split (Nat.zero_le t₀) (h₁.trans h₂), blockVal_split h₁ h₂,
    blockRange_split h₁ h₂]
  ring

/-- Overwriting a block of an address overwrites the corresponding digits of its index. -/
theorem lexEquiv_blockSet {t₀ t₁ : ℕ} (h₁ : t₀ ≤ t₁) (h₂ : t₁ ≤ L.n) (x : L.Addr) (v : ℕ) :
    (L.lexEquiv (L.blockSet t₀ t₁ x v)).val = L.idxSetBlock t₀ t₁ (L.lexEquiv x).val v := by
  have hy := L.idx_decomp h₁ h₂ x
  have hz := L.idx_decomp h₁ h₂ (L.blockSet t₀ t₁ x v)
  rw [blockVal_blockSet,
    blockVal_blockSet_of_disjoint (t₀ := t₀) (t₁ := t₁) (s₀ := 0) (s₁ := t₀) (Or.inr le_rfl),
    blockVal_blockSet_of_disjoint (t₀ := t₀) (t₁ := t₁) (s₀ := t₁) (s₁ := L.n) (Or.inl le_rfl)]
    at hz
  unfold idxSetBlock
  rw [← L.blockVal_eq_idxBlock h₁ h₂ x, hz, hy]
  generalize L.blockVal 0 t₀ x * (L.blockRange t₀ t₁ * L.blockRange t₁ L.n) = a
  generalize L.blockVal t₀ t₁ x * L.blockRange t₁ L.n = b
  generalize v % L.blockRange t₀ t₁ * L.blockRange t₁ L.n = c
  omega

theorem update_eq_blockSet (x : L.Addr) (j : Fin L.n) (d : Fin (L.r j)) :
    Function.update x j d = L.blockSet j.val (j.val + 1) x d.val := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self, Layout.blockSet,
      if_pos (show inBlock i.val (i.val + 1) i from ⟨le_refl _, Nat.lt_succ_self _⟩)]
    refine Fin.ext ?_
    show d.val = d.val / L.place (i.val + 1) i % L.r i
    rw [place_eq_blockRange, blockRange_of_le (le_refl _), Nat.div_one, Nat.mod_eq_of_lt d.isLt]
  · rw [Function.update_of_ne hij, blockSet_apply_of_not]
    intro h
    exact hij (Fin.ext (by omega))

/-- Overwriting one field overwrites the corresponding digit of the index. -/
theorem lexEquiv_update (x : L.Addr) (j : Fin L.n) (d : Fin (L.r j)) :
    (L.lexEquiv (Function.update x j d)).val =
      L.idxSetBlock j.val (j.val + 1) (L.lexEquiv x).val d.val := by
  rw [L.update_eq_blockSet, L.lexEquiv_blockSet (Nat.le_succ _) j.isLt]

/-! ### The machine list of an array -/

/-- The list of records of an array in lexicographic address order (matching `Machine/Contracts/` `enc`). -/
def enc {β : Type} (A : L.Addr → β) : List β := List.ofFn (A ∘ L.lexEquiv.symm)

theorem enc_length {β : Type} (A : L.Addr → β) : (L.enc A).length = L.card := List.length_ofFn

theorem enc_getElem {β : Type} (A : L.Addr → β) (y : ℕ) (hy : y < (L.enc A).length) :
    (L.enc A)[y] = A (L.lexEquiv.symm ⟨y, by rwa [enc_length] at hy⟩) := by
  simp [enc]

theorem enc_getD {β : Type} (A : L.Addr → β) {y : ℕ} (hy : y < L.card) (d : β) :
    (L.enc A).getD y d = A (L.lexEquiv.symm ⟨y, hy⟩) := by
  rw [List.getD_eq_getElem _ _ (by rwa [enc_length]), enc_getElem]

/-- The bridge to `permByInv`: pulling an array along `p` permutes its list by the index map `g` of
`p`. -/
theorem enc_comp {β : Type} [Inhabited β] (A : L.Addr → β) (p : L.Addr → L.Addr) (g : ℕ → ℕ)
    (hg : ∀ y (h : y < L.card), g y = (L.lexEquiv (p (L.lexEquiv.symm ⟨y, h⟩))).val) :
    L.enc (A ∘ p) = permByInv g (L.enc A) := by
  unfold permByInv
  apply List.ext_getElem
  · simp [enc_length]
  · intro y h1 h2
    have hy : y < L.card := by rwa [enc_length] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [hg y hy, L.enc_getD A (Fin.isLt _), Fin.eta, Equiv.symm_apply_apply, enc_getElem]
    rfl

end Layout

/-! ### Row classes on indices -/

/-- Membership in a row class, read off the index. -/
theorem RowClass.mem_lexEquiv_symm {L : Layout} (c : RowClass L) (i : Fin L.card) :
    c.mem (L.lexEquiv.symm i) ↔ L.idxBlock c.row.val (c.row.val + 1) i.val % c.μ = c.res := by
  unfold RowClass.mem
  rw [L.idxBlock_single, L.lexEquiv_symm_val]

theorem RowClass.mem_iff_idx {L : Layout} (c : RowClass L) (x : L.Addr) :
    c.mem x ↔ L.idxBlock c.row.val (c.row.val + 1) (L.lexEquiv x).val % c.μ = c.res := by
  rw [← RowClass.mem_lexEquiv_symm, Equiv.symm_apply_apply]

/-- The cyclic split: role `k` of a node with `W` roles in class `c` is the set of addresses of `c`
with role index `k`. -/
theorem RowClass.mem_sub_iff {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W)
    (x : L.Addr) : (c.sub W hW k).mem x ↔ c.mem x ∧ roleIdx c W hW x = k := by
  show (x c.row).val % (c.μ * W) = c.res + c.μ * k.val ↔
    (x c.row).val % c.μ = c.res ∧ roleIdx c W hW x = k
  rw [Fin.ext_iff]
  show _ ↔ _ ∧ (x c.row).val / c.μ % W = k.val
  rw [Nat.mod_mul]
  generalize (x c.row).val = a
  have hres := c.hres
  have hμ := c.hμ
  constructor
  · intro h
    have h1 : a % c.μ = c.res := by
      have h' := congrArg (· % c.μ) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_mod, Nat.mod_eq_of_lt hres] at h'
      exact h'
    refine ⟨h1, ?_⟩
    rw [h1] at h
    exact Nat.eq_of_mul_eq_mul_left hμ (Nat.add_left_cancel h)
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-- Role `k` of the whole array split by `W` (`W ∣ r ℓ`): the records whose global row index
`idx / S` (`S = place L.n ℓ` records per row) is `≡ k (mod W)` (matching `roleBlocks W k S`). -/
theorem RowClass.top_sub_mem_iff {L : Layout} (ℓ : Fin L.n) (W : ℕ) (hW : 0 < W)
    (hWr : W ∣ L.r ℓ) (k : Fin W) (x : L.Addr) :
    ((RowClass.top ℓ).sub W hW k).mem x ↔ (L.lexEquiv x).val / L.place L.n ℓ % W = k.val := by
  show (x ℓ).val % (1 * W) = 0 + 1 * k.val ↔ _
  rw [one_mul, zero_add, one_mul, L.field_eq_idx x ℓ, Nat.mod_mod_of_dvd _ hWr]

end SubNLogN.Math.Networks.Model
