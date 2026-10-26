import SubNLogN.Math.Networks.AppCProc

/-!
# Proposition A.7 (`prop:transfer11`) correctness, part R: class-restricted pulls and mixed-radix blocks

Generic facts about the abstract stream model (`AppCModel.lean`) used for `InterchangeProcCorrectStmt`:
* `cpull`: every primitive acts on arrays as `A ↦ (x ↦ if x ∈ class then A (pull x) else A x)`, and
  such maps compose by composing pulls (when the later pull preserves the class);
* mixed-radix arithmetic of `Layout.blockVal` / `Layout.blockSet`: digit extraction, overwriting,
  nested sub-blocks, ranges of radix-`q` blocks.
-/

namespace SubNLogN.Math.Networks

open Model

namespace InterchangeCorrect

variable {L : Layout}

/-! ### Class-restricted pulls -/

/-- Class-restricted pull: `A ↦ (x ↦ if P x then A (pull x) else A x)`
(`Step.runIn c (.elem e) = cpull c.mem e.pull`). -/
def cpull {β : Type} (P : L.Addr → Prop) [DecidablePred P] (pull : L.Addr → L.Addr)
    (A : L.Addr → β) : L.Addr → β :=
  fun x => if P x then A (pull x) else A x

theorem runIn_elem {β : Type} (c : RowClass L) (e : Elem L) (A : L.Addr → β) :
    (Step.elem e : Step L β).runIn c A = cpull c.mem e.pull A := rfl

theorem cpull_cpull {β : Type} (P : L.Addr → Prop) [DecidablePred P] (p₁ p₂ : L.Addr → L.Addr)
    (h₂ : ∀ x, P x → P (p₂ x)) (A : L.Addr → β) :
    cpull P p₂ (cpull P p₁ A) = cpull P (p₁ ∘ p₂) A := by
  funext x
  by_cases hx : P x
  · simp [cpull, hx, h₂ x hx]
  · simp [cpull, hx]

theorem cpull_id {β : Type} (P : L.Addr → Prop) [DecidablePred P] (A : L.Addr → β) :
    cpull P id A = A := by
  funext x
  by_cases hx : P x <;> simp [cpull, hx]

theorem cpull_congr {β : Type} (P : L.Addr → Prop) [DecidablePred P] {p p' : L.Addr → L.Addr}
    (h : ∀ x, P x → p x = p' x) (A : L.Addr → β) : cpull P p A = cpull P p' A := by
  funext x
  by_cases hx : P x
  · simp [cpull, hx, h x hx]
  · simp [cpull, hx]

/-! ### Mixed-radix blocks (all statements are for arbitrary layouts and blocks) -/

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

theorem blockSet_blockSet (t₀ t₁ : ℕ) (x : L.Addr) (v v' : ℕ) :
    L.blockSet t₀ t₁ (L.blockSet t₀ t₁ x v) v' = L.blockSet t₀ t₁ x v' := by
  funext j
  by_cases hj : inBlock t₀ t₁ j
  · simp only [Layout.blockSet, if_pos hj]
  · simp only [Layout.blockSet, if_neg hj]

/-! ### Mixed-radix helpers (sub-namespace `RadixAux`) -/

namespace RadixAux

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

/-- The first field of a block is below its range. -/
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

lemma blockRange_eq_pow_aux {q t₁ : ℕ} (hn : t₁ ≤ L.n) : ∀ d t₀, t₁ - t₀ = d → t₀ ≤ t₁ →
    (∀ j : Fin L.n, t₀ ≤ j.val → j.val < t₁ → L.r j = q) → L.blockRange t₀ t₁ = q ^ d := by
  intro d
  induction d with
  | zero =>
    intro t₀ hd ht _
    rw [blockRange_of_le (by omega), pow_zero]
  | succ d ih =>
    intro t₀ hd ht hr
    have hlt : t₀ < L.n := by omega
    rw [blockRange_split (Nat.le_succ t₀) (by omega : t₀ + 1 ≤ t₁),
      ih (t₀ + 1) (by omega) (by omega) (fun j h1 h2 => hr j (by omega) h2)]
    obtain ⟨f, rfl⟩ : ∃ f : Fin L.n, f.val = t₀ := ⟨⟨t₀, hlt⟩, rfl⟩
    rw [blockRange_single, hr f (le_refl _) (by omega), pow_succ']

/-- Sub-block digits (helper form of `blockVal_sub`, usable before it). -/
lemma blockVal_sub_aux {t₀ u₀ u₁ t₁ : ℕ} (h₁ : t₀ ≤ u₀) (h₂ : u₀ ≤ u₁) (h₃ : u₁ ≤ t₁)
    (x : L.Addr) :
    L.blockVal u₀ u₁ x = L.blockVal t₀ t₁ x / L.blockRange u₁ t₁ % L.blockRange u₀ u₁ := by
  have e1 : (L.blockVal t₀ u₁ x * L.blockRange u₁ t₁ + L.blockVal u₁ t₁ x) / L.blockRange u₁ t₁ =
      L.blockVal t₀ u₁ x := by
    rw [add_comm, Nat.add_mul_div_right _ _ (blockRange_pos x u₁ t₁),
      Nat.div_eq_of_lt (blockVal_lt_aux x t₁ (t₁ - u₁) u₁ rfl), zero_add]
  rw [blockVal_split (h₁.trans h₂) h₃, e1, blockVal_split h₁ h₂, add_comm,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (blockVal_lt_aux x u₁ (u₁ - u₀) u₀ rfl)]

end RadixAux

open RadixAux

/-- The value of a block is below its range. -/
theorem blockVal_lt (t₀ t₁ : ℕ) (x : L.Addr) : L.blockVal t₀ t₁ x < L.blockRange t₀ t₁ :=
  blockVal_lt_aux x t₁ (t₁ - t₀) t₀ rfl

/-- Reading back an overwritten block gives the value modulo the range. -/
theorem blockVal_blockSet (t₀ t₁ : ℕ) (x : L.Addr) (v : ℕ) :
    L.blockVal t₀ t₁ (L.blockSet t₀ t₁ x v) = v % L.blockRange t₀ t₁ :=
  blockVal_blockSet_aux t₁ (t₁ - t₀) t₀ rfl x v

/-- Overwriting a block with its own value changes nothing. -/
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

/-- Only the value modulo the range matters. -/
theorem blockSet_mod (t₀ t₁ : ℕ) (x : L.Addr) (v : ℕ) :
    L.blockSet t₀ t₁ x (v % L.blockRange t₀ t₁) = L.blockSet t₀ t₁ x v := by
  funext j
  by_cases hj : inBlock t₀ t₁ j
  · simp only [Layout.blockSet, if_pos hj]
    refine Fin.ext ?_
    show v % L.blockRange t₀ t₁ / L.place t₁ j % L.r j = v / L.place t₁ j % L.r j
    have hR : L.blockRange t₀ t₁ = L.blockRange t₀ j.val * L.r j * L.place t₁ j := by
      rw [blockRange_split hj.1 (le_of_lt hj.2), blockRange_split (Nat.le_succ j.val) hj.2,
        blockRange_single, ← place_eq_blockRange, mul_assoc]
    rw [hR, mod_div_mod]
  · simp only [Layout.blockSet, if_neg hj]

/-- A block of radix-`q` fields inside the layout has range `q ^ (t₁ − t₀)`. -/
theorem blockRange_eq_pow {q t₀ t₁ : ℕ} (ht : t₀ ≤ t₁) (hn : t₁ ≤ L.n)
    (hr : ∀ j : Fin L.n, t₀ ≤ j.val → j.val < t₁ → L.r j = q) :
    L.blockRange t₀ t₁ = q ^ (t₁ - t₀) :=
  blockRange_eq_pow_aux hn (t₁ - t₀) t₀ rfl ht hr

/-- A sub-block `[u₀, u₁) ⊆ [t₀, t₁)` holds the corresponding mixed-radix digits of the block. -/
theorem blockVal_sub {t₀ u₀ u₁ t₁ : ℕ} (h₁ : t₀ ≤ u₀) (h₂ : u₀ ≤ u₁) (h₃ : u₁ ≤ t₁)
    (x : L.Addr) :
    L.blockVal u₀ u₁ x = L.blockVal t₀ t₁ x / L.blockRange u₁ t₁ % L.blockRange u₀ u₁ :=
  blockVal_sub_aux h₁ h₂ h₃ x

/-- After overwriting `[t₀, t₁)` with `v`, a sub-block holds the corresponding digits of `v`. -/
theorem blockVal_sub_blockSet {t₀ u₀ u₁ t₁ : ℕ} (h₁ : t₀ ≤ u₀) (h₂ : u₀ ≤ u₁) (h₃ : u₁ ≤ t₁)
    (x : L.Addr) (v : ℕ) :
    L.blockVal u₀ u₁ (L.blockSet t₀ t₁ x v) = v / L.blockRange u₁ t₁ % L.blockRange u₀ u₁ := by
  rw [blockVal_sub h₁ h₂ h₃, blockVal_blockSet, blockRange_split (h₁.trans h₂) h₃,
    blockRange_split h₁ h₂, mod_div_mod]

theorem blockVal_blockSet_of_disjoint {t₀ t₁ s₀ s₁ : ℕ} (h : t₁ ≤ s₀ ∨ s₁ ≤ t₀) (x : L.Addr)
    (v : ℕ) : L.blockVal s₀ s₁ (L.blockSet t₀ t₁ x v) = L.blockVal s₀ s₁ x := by
  refine blockVal_congr fun j hj₁ hj₂ => blockSet_apply_of_not x v j ?_
  omega

end InterchangeCorrect

end SubNLogN.Math.Networks
