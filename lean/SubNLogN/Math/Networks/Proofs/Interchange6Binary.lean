import SubNLogN.Math.Networks.AppCProc6
import SubNLogN.Math.Networks.Proofs.InterchangeCorrectRadix

/-!
# Lemma A.8 (`lem:transfer12`), binary chunks: numerical padding to radix `q`

Proof of the contract `Interchange6BinaryStmt` (`AppCProc6.lean`; Lemma A.8 (`lem:transfer12`),
Appendix A.3 (`sec:transfer-arbitrary`), binary numerical padding). For two disjoint chunks of `u` binary fields
and any radix `q ≥ 2`, the following composite is the interchange of the binary chunks: pad both
chunks numerically to `e = binDigits q u` radix-`q` digits, interchange the padded chunks, unpad.

## Proof
`binPadAddr = R₁ ∘ R₂` is the composite of two recodings (`recodeAddr`). `R₂` rewrites the later
chunk `[s₀, s₀+u)` of `L` as `e` radix-`q` digits (layout `L₁`). `R₁` does the same for the earlier
chunk `[t₀, t₀+u)` of `L₁` (layout `L₂`).

Generic facts about one recoding `f = recodeAddr L t₀ len r₁ len₁` (namespace
`Interchange6BinAux`, usable for any recoding):
* blocks before the recoded block keep their values and ranges, and so do blocks after it (shifted
  by `len₁ − len`); `f` commutes with overwriting them (`recode_blockVal_before`,
  `recode_blockVal_after`, `recode_blockSet_before`, `recode_blockSet_after`);
* the recoded block of `f x` has value `blockVal x mod r₁^len₁` (`recode_blockVal_new`);
  overwriting the old block with `v < blockRange` becomes overwriting the new block with `v`
  (`recode_blockSet_new`);
* `f` is injective when the old block range is at most `r₁^len₁` (`recodeAddr_injective`).

With `2^u ≤ q^e` (`Nat.le_pow_clog`), both chunk values `v₁, v₂ < 2^u` survive the recoding. Hence
`binPadAddr` commutes with the two swap maps (`binPadAddr_swapPull`) and is injective. Then
`binUnpad (swap (binPad A)) x = binPad A (binPadAddr (swap x)) = A (swap x)`.
-/

namespace SubNLogN.Math.Networks

open Model

namespace Interchange6BinAux

open InterchangeCorrect InterchangeCorrect.RadixAux

/-! ### Index bookkeeping -/

theorem layout_r_congr (L : Layout) {a b : ℕ} (h : a = b) (ha : a < L.n) (hb : b < L.n) :
    L.r ⟨a, ha⟩ = L.r ⟨b, hb⟩ := by
  subst h; rfl

theorem addr_val_congr {L : Layout} (x : L.Addr) {a b : ℕ} (h : a = b) (ha : a < L.n)
    (hb : b < L.n) : (x ⟨a, ha⟩).val = (x ⟨b, hb⟩).val := by
  subst h; rfl

/-- Field values of an overwritten block. -/
theorem blockSet_val (L : Layout) (t₀ t₁ : ℕ) (x : L.Addr) (v : ℕ) (j : Fin L.n) :
    (L.blockSet t₀ t₁ x v j).val =
      if t₀ ≤ j.val ∧ j.val < t₁ then v / L.place t₁ j % L.r j else (x j).val := by
  by_cases h : t₀ ≤ j.val ∧ j.val < t₁
  · have h' : inBlock t₀ t₁ j := h
    simp only [Layout.blockSet, if_pos h', if_pos h]
  · have h' : ¬ inBlock t₀ t₁ j := h
    simp only [Layout.blockSet, if_neg h', if_neg h]

/-- Overwriting a block only depends on the fields outside it. -/
theorem blockSet_eq_of_agree {L : Layout} {t₀ t₁ : ℕ} {x y : L.Addr}
    (h : ∀ j : Fin L.n, ¬ (t₀ ≤ j.val ∧ j.val < t₁) → x j = y j) (v : ℕ) :
    L.blockSet t₀ t₁ x v = L.blockSet t₀ t₁ y v := by
  funext j
  refine Fin.ext ?_
  rw [blockSet_val, blockSet_val]
  split_ifs with hj
  · rfl
  · rw [h j hj]

/-! ### Transport of block ranges and values between layouts -/

/-- Two blocks whose fields have the same ranges (up to an index offset) have the same range. -/
theorem transport_range {L M : Layout} : ∀ (d a c : ℕ), c + d ≤ L.n → a + d ≤ M.n →
    (∀ k, k < d → ∀ (h₁ : a + k < M.n) (h₂ : c + k < L.n), M.r ⟨a + k, h₁⟩ = L.r ⟨c + k, h₂⟩) →
    M.blockRange a (a + d) = L.blockRange c (c + d) := by
  intro d
  induction d with
  | zero =>
    intro a c _ _ _
    rw [blockRange_of_le (by omega), blockRange_of_le (by omega)]
  | succ d ih =>
    intro a c hL hM hr
    rw [blockRange_split (Nat.le_succ a) (show a + 1 ≤ a + (d + 1) by omega),
      blockRange_split (Nat.le_succ c) (show c + 1 ≤ c + (d + 1) by omega)]
    have htail : M.blockRange (a + 1) (a + (d + 1)) = L.blockRange (c + 1) (c + (d + 1)) := by
      have h := ih (a + 1) (c + 1) (by omega) (by omega) (fun k hk h₁ h₂ => by
        rw [layout_r_congr M (show a + 1 + k = a + (k + 1) by omega) h₁ (by omega),
          layout_r_congr L (show c + 1 + k = c + (k + 1) by omega) h₂ (by omega)]
        exact hr (k + 1) (by omega) _ _)
      rwa [show a + 1 + d = a + (d + 1) by omega, show c + 1 + d = c + (d + 1) by omega] at h
    have hhead : M.blockRange a (a + 1) = L.blockRange c (c + 1) := by
      obtain ⟨f, hf⟩ : ∃ f : Fin M.n, f.val = a := ⟨⟨a, by omega⟩, rfl⟩
      obtain ⟨g, hg⟩ : ∃ g : Fin L.n, g.val = c := ⟨⟨c, by omega⟩, rfl⟩
      subst hf
      subst hg
      rw [blockRange_single, blockRange_single]
      have h0 := hr 0 (by omega) (by omega) (by omega)
      simpa using h0
    rw [htail, hhead]

/-- Two blocks whose fields have the same ranges and digits (up to an index offset) have the same
value. -/
theorem transport_val {L M : Layout} (x : L.Addr) (y : M.Addr) : ∀ (d a c : ℕ), c + d ≤ L.n →
    a + d ≤ M.n →
    (∀ k, k < d → ∀ (h₁ : a + k < M.n) (h₂ : c + k < L.n), M.r ⟨a + k, h₁⟩ = L.r ⟨c + k, h₂⟩) →
    (∀ k, k < d → ∀ (h₁ : a + k < M.n) (h₂ : c + k < L.n),
      (y ⟨a + k, h₁⟩).val = (x ⟨c + k, h₂⟩).val) →
    M.blockVal a (a + d) y = L.blockVal c (c + d) x := by
  intro d
  induction d with
  | zero =>
    intro a c _ _ _ _
    rw [blockVal_of_le (by omega), blockVal_of_le (by omega)]
  | succ d ih =>
    intro a c hL hM hr hv
    rw [blockVal_split (Nat.le_succ a) (show a + 1 ≤ a + (d + 1) by omega),
      blockVal_split (Nat.le_succ c) (show c + 1 ≤ c + (d + 1) by omega)]
    have hr' : ∀ k, k < d → ∀ (h₁ : a + 1 + k < M.n) (h₂ : c + 1 + k < L.n),
        M.r ⟨a + 1 + k, h₁⟩ = L.r ⟨c + 1 + k, h₂⟩ := fun k hk h₁ h₂ => by
      rw [layout_r_congr M (show a + 1 + k = a + (k + 1) by omega) h₁ (by omega),
        layout_r_congr L (show c + 1 + k = c + (k + 1) by omega) h₂ (by omega)]
      exact hr (k + 1) (by omega) _ _
    have hv' : ∀ k, k < d → ∀ (h₁ : a + 1 + k < M.n) (h₂ : c + 1 + k < L.n),
        (y ⟨a + 1 + k, h₁⟩).val = (x ⟨c + 1 + k, h₂⟩).val := fun k hk h₁ h₂ => by
      rw [addr_val_congr y (show a + 1 + k = a + (k + 1) by omega) h₁ (by omega),
        addr_val_congr x (show c + 1 + k = c + (k + 1) by omega) h₂ (by omega)]
      exact hv (k + 1) (by omega) _ _
    have hrng : M.blockRange (a + 1) (a + (d + 1)) = L.blockRange (c + 1) (c + (d + 1)) := by
      have h := transport_range d (a + 1) (c + 1) (by omega) (by omega) hr'
      rwa [show a + 1 + d = a + (d + 1) by omega, show c + 1 + d = c + (d + 1) by omega] at h
    have htail : M.blockVal (a + 1) (a + (d + 1)) y = L.blockVal (c + 1) (c + (d + 1)) x := by
      have h := ih (a + 1) (c + 1) (by omega) (by omega) hr' hv'
      rwa [show a + 1 + d = a + (d + 1) by omega, show c + 1 + d = c + (d + 1) by omega] at h
    have hhead : M.blockVal a (a + 1) y = L.blockVal c (c + 1) x := by
      obtain ⟨f, hf⟩ : ∃ f : Fin M.n, f.val = a := ⟨⟨a, by omega⟩, rfl⟩
      obtain ⟨g, hg⟩ : ∃ g : Fin L.n, g.val = c := ⟨⟨c, by omega⟩, rfl⟩
      subst hf
      subst hg
      rw [blockVal_single, blockVal_single]
      have h0 := hv 0 (by omega) (by omega) (by omega)
      simpa using h0
    rw [hrng, htail, hhead]

/-! ### One recoding `f = recodeAddr L t₀ len r₁ len₁` -/

section Recode

variable {L : Layout} {t₀ len r₁ len₁ : ℕ}

theorem recode_r_lt (i : Fin (recodeLayout L t₀ len r₁ len₁).n) (h : i.val < t₀)
    (hn : i.val < L.n) : (recodeLayout L t₀ len r₁ len₁).r i = L.r ⟨i.val, hn⟩ := by
  simp only [recodeLayout, if_pos h, dif_pos hn]

theorem recode_r_mid (i : Fin (recodeLayout L t₀ len r₁ len₁).n) (h1 : ¬ i.val < t₀)
    (h2 : i.val < t₀ + len₁) : (recodeLayout L t₀ len r₁ len₁).r i = r₁ := by
  simp only [recodeLayout, if_neg h1, if_pos h2]

theorem recode_r_hi (i : Fin (recodeLayout L t₀ len r₁ len₁).n) (h1 : ¬ i.val < t₀)
    (h2 : ¬ i.val < t₀ + len₁) (hn : i.val + len - len₁ < L.n) :
    (recodeLayout L t₀ len r₁ len₁).r i = L.r ⟨i.val + len - len₁, hn⟩ := by
  simp only [recodeLayout, if_neg h1, if_neg h2, dif_pos hn]

/-- Blocks before the recoded block keep their range. -/
theorem recode_blockRange_before (ht : t₀ + len ≤ L.n) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ t₀) :
    (recodeLayout L t₀ len r₁ len₁).blockRange a b = L.blockRange a b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  refine transport_range d a a (by omega) (by simp only [recodeLayout]; omega)
    fun k hk h₁ h₂ => ?_
  rw [recode_r_lt ⟨a + k, h₁⟩ (show a + k < t₀ by omega) h₂]

/-- Blocks after the recoded block keep their range (shifted by `len₁ − len`). -/
theorem recode_blockRange_after {a b a' b' : ℕ} (hab : a ≤ b) (ha : t₀ + len ≤ a)
    (hb : b ≤ L.n) (ha' : a' + len = a + len₁) (hb' : b' + len = b + len₁) :
    (recodeLayout L t₀ len r₁ len₁).blockRange a' b' = L.blockRange a b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  obtain rfl : b' = a' + d := by omega
  refine transport_range d a' a (by omega) (by simp only [recodeLayout]; omega)
    fun k hk h₁ h₂ => ?_
  rw [recode_r_hi ⟨a' + k, h₁⟩ (show ¬ a' + k < t₀ by omega)
    (show ¬ a' + k < t₀ + len₁ by omega) (show a' + k + len - len₁ < L.n by omega)]
  exact layout_r_congr L (show a' + k + len - len₁ = a + k by omega) _ _

/-- The recoded block has range `r₁ ^ len₁`. -/
theorem recode_blockRange_new (ht : t₀ + len ≤ L.n) :
    (recodeLayout L t₀ len r₁ len₁).blockRange t₀ (t₀ + len₁) = r₁ ^ len₁ := by
  rw [blockRange_eq_pow (q := r₁) (Nat.le_add_right t₀ len₁) (by simp only [recodeLayout]; omega)
    (fun j h1 h2 => recode_r_mid j (by omega) h2), Nat.add_sub_cancel_left]

/-- Place values inside the recoded block. -/
theorem recode_place_new (ht : t₀ + len ≤ L.n) (i : Fin (recodeLayout L t₀ len r₁ len₁).n)
    (h1 : t₀ ≤ i.val) (h2 : i.val < t₀ + len₁) :
    (recodeLayout L t₀ len r₁ len₁).place (t₀ + len₁) i = r₁ ^ (t₀ + len₁ - 1 - i.val) := by
  rw [place_eq_blockRange, blockRange_eq_pow (q := r₁) (by omega)
    (by simp only [recodeLayout]; omega) (fun j hj1 hj2 => recode_r_mid j (by omega) hj2)]
  congr 1
  omega

variable (hr : 0 < r₁) (ht : t₀ + len ≤ L.n)

theorem recode_val_lt (x : L.Addr) (i : Fin (recodeLayout L t₀ len r₁ len₁).n) (h : i.val < t₀) :
    (recodeAddr L t₀ len r₁ len₁ hr ht x i).val = (x ⟨i.val, by omega⟩).val := by
  simp only [recodeAddr, dif_pos h]

theorem recode_val_mid (x : L.Addr) (i : Fin (recodeLayout L t₀ len r₁ len₁).n)
    (h1 : ¬ i.val < t₀) (h2 : i.val < t₀ + len₁) :
    (recodeAddr L t₀ len r₁ len₁ hr ht x i).val =
      L.blockVal t₀ (t₀ + len) x / r₁ ^ (t₀ + len₁ - 1 - i.val) % r₁ := by
  simp only [recodeAddr, dif_neg h1, dif_pos h2]

theorem recode_val_hi (x : L.Addr) (i : Fin (recodeLayout L t₀ len r₁ len₁).n)
    (h1 : ¬ i.val < t₀) (h2 : ¬ i.val < t₀ + len₁) (hn : i.val + len - len₁ < L.n) :
    (recodeAddr L t₀ len r₁ len₁ hr ht x i).val = (x ⟨i.val + len - len₁, hn⟩).val := by
  simp only [recodeAddr, dif_neg h1, dif_neg h2]

/-- Blocks before the recoded block keep their value. -/
theorem recode_blockVal_before (x : L.Addr) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ t₀) :
    (recodeLayout L t₀ len r₁ len₁).blockVal a b (recodeAddr L t₀ len r₁ len₁ hr ht x) =
      L.blockVal a b x := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  refine transport_val x _ d a a (by omega) (by simp only [recodeLayout]; omega)
    (fun k hk h₁ h₂ => ?_) (fun k hk h₁ h₂ => ?_)
  · rw [recode_r_lt ⟨a + k, h₁⟩ (show a + k < t₀ by omega) h₂]
  · rw [recode_val_lt hr ht x ⟨a + k, h₁⟩ (show a + k < t₀ by omega)]

/-- Blocks after the recoded block keep their value (shifted by `len₁ − len`). -/
theorem recode_blockVal_after (x : L.Addr) {a b a' b' : ℕ} (hab : a ≤ b) (ha : t₀ + len ≤ a)
    (hb : b ≤ L.n) (ha' : a' + len = a + len₁) (hb' : b' + len = b + len₁) :
    (recodeLayout L t₀ len r₁ len₁).blockVal a' b' (recodeAddr L t₀ len r₁ len₁ hr ht x) =
      L.blockVal a b x := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  obtain rfl : b' = a' + d := by omega
  refine transport_val x _ d a' a (by omega) (by simp only [recodeLayout]; omega)
    (fun k hk h₁ h₂ => ?_) (fun k hk h₁ h₂ => ?_)
  · rw [recode_r_hi ⟨a' + k, h₁⟩ (show ¬ a' + k < t₀ by omega)
      (show ¬ a' + k < t₀ + len₁ by omega) (show a' + k + len - len₁ < L.n by omega)]
    exact layout_r_congr L (show a' + k + len - len₁ = a + k by omega) _ _
  · rw [recode_val_hi hr ht x ⟨a' + k, h₁⟩ (show ¬ a' + k < t₀ by omega)
      (show ¬ a' + k < t₀ + len₁ by omega) (show a' + k + len - len₁ < L.n by omega)]
    exact addr_val_congr x (show a' + k + len - len₁ = a + k by omega) _ _

/-- The recoded address holds, on the new block, the digits of the old block value. -/
theorem recode_eq_blockSet (x : L.Addr) :
    recodeAddr L t₀ len r₁ len₁ hr ht x = (recodeLayout L t₀ len r₁ len₁).blockSet t₀ (t₀ + len₁)
      (recodeAddr L t₀ len r₁ len₁ hr ht x) (L.blockVal t₀ (t₀ + len) x) := by
  funext i
  refine Fin.ext ?_
  rw [blockSet_val]
  split_ifs with hi
  · rw [recode_val_mid hr ht x i (by omega) hi.2, recode_place_new ht i hi.1 hi.2,
      recode_r_mid i (by omega) hi.2]
  · rfl

/-- The new block of the recoded address has value `blockVal x mod r₁ ^ len₁`. -/
theorem recode_blockVal_new (x : L.Addr) :
    (recodeLayout L t₀ len r₁ len₁).blockVal t₀ (t₀ + len₁) (recodeAddr L t₀ len r₁ len₁ hr ht x) =
      L.blockVal t₀ (t₀ + len) x % r₁ ^ len₁ := by
  rw [recode_eq_blockSet hr ht x, blockVal_blockSet, recode_blockRange_new ht]

/-- Overwriting a block before the recoded block commutes with the recoding. -/
theorem recode_blockSet_before (x : L.Addr) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ t₀) (v : ℕ) :
    recodeAddr L t₀ len r₁ len₁ hr ht (L.blockSet a b x v) =
      (recodeLayout L t₀ len r₁ len₁).blockSet a b (recodeAddr L t₀ len r₁ len₁ hr ht x) v := by
  funext i
  refine Fin.ext ?_
  rw [blockSet_val]
  by_cases h1 : i.val < t₀
  · rw [recode_val_lt hr ht _ i h1, recode_val_lt hr ht x i h1, blockSet_val]
    simp only
    split_ifs with hi
    · rw [recode_r_lt i h1 (by omega), place_eq_blockRange, place_eq_blockRange,
        recode_blockRange_before ht (show i.val + 1 ≤ b by omega) hb]
    · rfl
  · rw [if_neg (show ¬ (a ≤ i.val ∧ i.val < b) by omega)]
    by_cases h2 : i.val < t₀ + len₁
    · rw [recode_val_mid hr ht _ i h1 h2, recode_val_mid hr ht x i h1 h2,
        blockVal_blockSet_of_disjoint (Or.inl hb)]
    · have hn : i.val + len - len₁ < L.n := by
        have := i.isLt; simp only [recodeLayout] at this; omega
      rw [recode_val_hi hr ht _ i h1 h2 hn, recode_val_hi hr ht x i h1 h2 hn, blockSet_val]
      simp only
      split_ifs with hc
      · exfalso; omega
      · rfl

/-- Overwriting a block after the recoded block commutes with the recoding (with the block shifted
by `len₁ − len`). -/
theorem recode_blockSet_after (x : L.Addr) {a b a' b' : ℕ} (_hab : a ≤ b) (ha : t₀ + len ≤ a)
    (hb : b ≤ L.n) (ha' : a' + len = a + len₁) (hb' : b' + len = b + len₁) (v : ℕ) :
    recodeAddr L t₀ len r₁ len₁ hr ht (L.blockSet a b x v) =
      (recodeLayout L t₀ len r₁ len₁).blockSet a' b' (recodeAddr L t₀ len r₁ len₁ hr ht x) v := by
  funext i
  refine Fin.ext ?_
  rw [blockSet_val]
  by_cases h1 : i.val < t₀
  · rw [if_neg (show ¬ (a' ≤ i.val ∧ i.val < b') by omega), recode_val_lt hr ht _ i h1,
      recode_val_lt hr ht x i h1, blockSet_val]
    simp only
    split_ifs with hc
    · exfalso; omega
    · rfl
  · by_cases h2 : i.val < t₀ + len₁
    · rw [if_neg (show ¬ (a' ≤ i.val ∧ i.val < b') by omega), recode_val_mid hr ht _ i h1 h2,
        recode_val_mid hr ht x i h1 h2, blockVal_blockSet_of_disjoint (Or.inr ha)]
    · have hn : i.val + len - len₁ < L.n := by
        have := i.isLt; simp only [recodeLayout] at this; omega
      rw [recode_val_hi hr ht _ i h1 h2 hn, recode_val_hi hr ht x i h1 h2 hn, blockSet_val]
      simp only
      by_cases hc : a' ≤ i.val ∧ i.val < b'
      · rw [if_pos (show a ≤ i.val + len - len₁ ∧ i.val + len - len₁ < b by omega), if_pos hc,
          recode_r_hi i h1 h2 hn, place_eq_blockRange, place_eq_blockRange,
          recode_blockRange_after (a := i.val + len - len₁ + 1) (b := b) (a' := i.val + 1)
            (b' := b') (by omega) (by omega) hb (by omega) hb']
      · rw [if_neg (show ¬ (a ≤ i.val + len - len₁ ∧ i.val + len - len₁ < b) by omega),
          if_neg hc]

/-- Overwriting the recoded block with a value below its range becomes overwriting the new block. -/
theorem recode_blockSet_new (x : L.Addr) (v : ℕ) (hv : v < L.blockRange t₀ (t₀ + len)) :
    recodeAddr L t₀ len r₁ len₁ hr ht (L.blockSet t₀ (t₀ + len) x v) =
      (recodeLayout L t₀ len r₁ len₁).blockSet t₀ (t₀ + len₁)
        (recodeAddr L t₀ len r₁ len₁ hr ht x) v := by
  funext i
  refine Fin.ext ?_
  rw [blockSet_val]
  by_cases h1 : i.val < t₀
  · rw [if_neg (show ¬ (t₀ ≤ i.val ∧ i.val < t₀ + len₁) by omega), recode_val_lt hr ht _ i h1,
      recode_val_lt hr ht x i h1, blockSet_val]
    simp only
    split_ifs with hc
    · exfalso; omega
    · rfl
  · by_cases h2 : i.val < t₀ + len₁
    · rw [if_pos (show t₀ ≤ i.val ∧ i.val < t₀ + len₁ from ⟨by omega, h2⟩),
        recode_val_mid hr ht _ i h1 h2, blockVal_blockSet, Nat.mod_eq_of_lt hv,
        recode_place_new ht i (by omega) h2, recode_r_mid i h1 h2]
    · have hn : i.val + len - len₁ < L.n := by
        have := i.isLt; simp only [recodeLayout] at this; omega
      rw [if_neg (show ¬ (t₀ ≤ i.val ∧ i.val < t₀ + len₁) by omega),
        recode_val_hi hr ht _ i h1 h2 hn, recode_val_hi hr ht x i h1 h2 hn, blockSet_val]
      simp only
      split_ifs with hc
      · exfalso; omega
      · rfl

/-- The recoding is injective when the old block range is at most `r₁ ^ len₁`. -/
theorem recodeAddr_injective (hle : L.blockRange t₀ (t₀ + len) ≤ r₁ ^ len₁) :
    Function.Injective (recodeAddr L t₀ len r₁ len₁ hr ht) := by
  intro x y hxy
  have hv : L.blockVal t₀ (t₀ + len) x = L.blockVal t₀ (t₀ + len) y := by
    have h := congrArg ((recodeLayout L t₀ len r₁ len₁).blockVal t₀ (t₀ + len₁)) hxy
    rw [recode_blockVal_new hr ht, recode_blockVal_new hr ht,
      Nat.mod_eq_of_lt ((blockVal_lt _ _ x).trans_le hle),
      Nat.mod_eq_of_lt ((blockVal_lt _ _ y).trans_le hle)] at h
    exact h
  have hout : ∀ j : Fin L.n, ¬ (t₀ ≤ j.val ∧ j.val < t₀ + len) → x j = y j := by
    intro j hj
    refine Fin.ext ?_
    by_cases hj0 : j.val < t₀
    · have hi : j.val < (recodeLayout L t₀ len r₁ len₁).n := by
        simp only [recodeLayout]; omega
      have h : (recodeAddr L t₀ len r₁ len₁ hr ht x ⟨j.val, hi⟩).val =
          (recodeAddr L t₀ len r₁ len₁ hr ht y ⟨j.val, hi⟩).val := by rw [hxy]
      rw [recode_val_lt hr ht x ⟨j.val, hi⟩ hj0, recode_val_lt hr ht y ⟨j.val, hi⟩ hj0] at h
      exact h
    · have hi : j.val + len₁ - len < (recodeLayout L t₀ len r₁ len₁).n := by
        have := j.isLt; simp only [recodeLayout]; omega
      have h : (recodeAddr L t₀ len r₁ len₁ hr ht x ⟨j.val + len₁ - len, hi⟩).val =
          (recodeAddr L t₀ len r₁ len₁ hr ht y ⟨j.val + len₁ - len, hi⟩).val := by rw [hxy]
      have hn : j.val + len₁ - len + len - len₁ < L.n := by have := j.isLt; omega
      rw [recode_val_hi hr ht x ⟨j.val + len₁ - len, hi⟩ (show ¬ j.val + len₁ - len < t₀ by omega)
          (show ¬ j.val + len₁ - len < t₀ + len₁ by omega) hn,
        recode_val_hi hr ht y ⟨j.val + len₁ - len, hi⟩ (show ¬ j.val + len₁ - len < t₀ by omega)
          (show ¬ j.val + len₁ - len < t₀ + len₁ by omega) hn,
        addr_val_congr x (show j.val + len₁ - len + len - len₁ = j.val by omega) hn j.isLt,
        addr_val_congr y (show j.val + len₁ - len + len - len₁ = j.val by omega) hn j.isLt] at h
      exact h
  calc x = L.blockSet t₀ (t₀ + len) x (L.blockVal t₀ (t₀ + len) x) := (blockSet_blockVal _ _ x).symm
    _ = L.blockSet t₀ (t₀ + len) y (L.blockVal t₀ (t₀ + len) y) := by
        rw [hv]; exact blockSet_eq_of_agree hout _
    _ = y := blockSet_blockVal _ _ y

end Recode

/-! ### Binary chunks -/

/-- The pull map of `Step.swapBlocks t₀ s₀ len`: `(swapBlocks).run A = A ∘ swapPull`. -/
def swapPull (L : Layout) (t₀ s₀ len : ℕ) (x : L.Addr) : L.Addr :=
  L.blockSet s₀ (s₀ + len) (L.blockSet t₀ (t₀ + len) x (L.blockVal s₀ (s₀ + len) x))
    (L.blockVal t₀ (t₀ + len) x)

theorem swapBlocks_run {L : Layout} {β : Type} (t₀ s₀ len : ℕ) (A : L.Addr → β) :
    (Step.swapBlocks t₀ s₀ len : Step L β).run A = A ∘ swapPull L t₀ s₀ len := rfl

/-- `2^u ≤ q^e` for `e = binDigits q u` (`q ≥ 2`). -/
theorem two_pow_le_binDigits {q : ℕ} (hq : 2 ≤ q) (u : ℕ) : 2 ^ u ≤ q ^ binDigits q u :=
  Nat.le_pow_clog (by omega) _

/-- A chunk of `u` binary fields has range `2^u`. -/
theorem blockRange_binary {L : Layout} {u a : ℕ} (hn : a + u ≤ L.n)
    (hr : ∀ i : Fin L.n, a ≤ i.val ∧ i.val < a + u → L.r i = 2) :
    L.blockRange a (a + u) = 2 ^ u := by
  rw [blockRange_eq_pow (q := 2) (Nat.le_add_right a u) hn (fun j h1 h2 => hr j ⟨h1, h2⟩),
    Nat.add_sub_cancel_left]

/-- Embedding along an injective map, read at an image point. -/
theorem embedAlong_apply {L L' : Layout} {β : Type} [Zero β] {f : L.Addr → L'.Addr}
    (hf : Function.Injective f) (A : L.Addr → β) (x : L.Addr) : embedAlong f A (f x) = A x := by
  have h : ∃ x', f x' = f x := ⟨x, rfl⟩
  simp only [embedAlong, dif_pos h]
  rw [hf (Classical.choose_spec h)]

section Binary

variable {L : Layout} {q u t₀ s₀ : ℕ} (hq : 2 ≤ q) (hb : TwoBlocks L 2 u t₀ s₀)

include hq hb in
/-- The padding map is injective (`2^u ≤ q^e`). -/
theorem binPadAddr_injective : Function.Injective (binPadAddr L q u t₀ s₀ hq hb) := by
  have he := two_pow_le_binDigits hq u
  have hts : t₀ + u ≤ s₀ := hb.1
  have hsn : s₀ + u ≤ L.n := hb.2.1
  have hq0 : 0 < q := by omega
  have hR₂ : L.blockRange s₀ (s₀ + u) = 2 ^ u :=
    blockRange_binary hsn (fun i hi => hb.2.2 i (Or.inr hi))
  have hR₁ : L.blockRange t₀ (t₀ + u) = 2 ^ u :=
    blockRange_binary (by omega) (fun i hi => hb.2.2 i (Or.inl hi))
  have hL₁n : t₀ + u ≤ (recodeLayout L s₀ u q (binDigits q u)).n := by
    simp only [recodeLayout]; omega
  have hinj₂ := recodeAddr_injective (L := L) (t₀ := s₀) (len := u) (r₁ := q)
    (len₁ := binDigits q u) hq0 hsn (by rw [hR₂]; exact he)
  have hinj₁ := recodeAddr_injective (L := recodeLayout L s₀ u q (binDigits q u)) (t₀ := t₀)
    (len := u) (r₁ := q) (len₁ := binDigits q u) hq0 hL₁n
    (by rw [recode_blockRange_before hsn (Nat.le_add_right t₀ u) hts, hR₁]; exact he)
  exact hinj₁.comp hinj₂

include hq hb in
/-- Padding commutes with the two interchanges: the padded image of the swapped binary
address is the swap of the padded address. -/
theorem binPadAddr_swapPull (x : L.Addr) :
    binPadAddr L q u t₀ s₀ hq hb (swapPull L t₀ s₀ u x) =
      swapPull (binPadLayout L q u t₀ s₀) t₀ (s₀ + binDigits q u - u) (binDigits q u)
        (binPadAddr L q u t₀ s₀ hq hb x) := by
  have he := two_pow_le_binDigits hq u
  have hts : t₀ + u ≤ s₀ := hb.1
  have hsn : s₀ + u ≤ L.n := hb.2.1
  have hq0 : 0 < q := by omega
  have hR₂ : L.blockRange s₀ (s₀ + u) = 2 ^ u :=
    blockRange_binary hsn (fun i hi => hb.2.2 i (Or.inr hi))
  have hR₁ : L.blockRange t₀ (t₀ + u) = 2 ^ u :=
    blockRange_binary (by omega) (fun i hi => hb.2.2 i (Or.inl hi))
  have hL₁n : t₀ + u ≤ (recodeLayout L s₀ u q (binDigits q u)).n := by
    simp only [recodeLayout]; omega
  have hR₁' : (recodeLayout L s₀ u q (binDigits q u)).blockRange t₀ (t₀ + u) = 2 ^ u := by
    rw [recode_blockRange_before hsn (Nat.le_add_right t₀ u) hts, hR₁]
  have hv₁ : L.blockVal t₀ (t₀ + u) x < 2 ^ u := hR₁ ▸ blockVal_lt _ _ x
  have hv₂ : L.blockVal s₀ (s₀ + u) x < 2 ^ u := hR₂ ▸ blockVal_lt _ _ x
  have hsn₁ : s₀ + binDigits q u ≤ (recodeLayout L s₀ u q (binDigits q u)).n := by
    simp only [recodeLayout]; omega
  -- the padded image of the swapped address
  have hL : binPadAddr L q u t₀ s₀ hq hb (swapPull L t₀ s₀ u x) =
      (binPadLayout L q u t₀ s₀).blockSet (s₀ + binDigits q u - u)
        (s₀ + binDigits q u - u + binDigits q u)
        ((binPadLayout L q u t₀ s₀).blockSet t₀ (t₀ + binDigits q u)
          (binPadAddr L q u t₀ s₀ hq hb x) (L.blockVal s₀ (s₀ + u) x))
        (L.blockVal t₀ (t₀ + u) x) := by
    show recodeAddr (recodeLayout L s₀ u q (binDigits q u)) t₀ u q (binDigits q u) hq0 hL₁n
      (recodeAddr L s₀ u q (binDigits q u) hq0 hsn (swapPull L t₀ s₀ u x)) = _
    rw [swapPull, recode_blockSet_new hq0 hsn _ _ (by rw [hR₂]; exact hv₁),
      recode_blockSet_before hq0 hsn x (Nat.le_add_right t₀ u) hts,
      recode_blockSet_after hq0 hL₁n _ (a := s₀) (b := s₀ + binDigits q u)
        (a' := s₀ + binDigits q u - u) (b' := s₀ + binDigits q u - u + binDigits q u)
        (Nat.le_add_right _ _) hts hsn₁ (by omega) (by omega),
      recode_blockSet_new hq0 hL₁n _ _ (by rw [hR₁']; exact hv₂)]
    rfl
  -- the two chunk values of the padded address
  have hval₁ : (binPadLayout L q u t₀ s₀).blockVal t₀ (t₀ + binDigits q u)
      (binPadAddr L q u t₀ s₀ hq hb x) = L.blockVal t₀ (t₀ + u) x := by
    show (recodeLayout (recodeLayout L s₀ u q (binDigits q u)) t₀ u q (binDigits q u)).blockVal
      t₀ (t₀ + binDigits q u) (recodeAddr (recodeLayout L s₀ u q (binDigits q u)) t₀ u q
        (binDigits q u) hq0 hL₁n (recodeAddr L s₀ u q (binDigits q u) hq0 hsn x)) = _
    rw [recode_blockVal_new hq0 hL₁n, recode_blockVal_before hq0 hsn x (Nat.le_add_right t₀ u) hts,
      Nat.mod_eq_of_lt (hv₁.trans_le he)]
  have hval₂ : (binPadLayout L q u t₀ s₀).blockVal (s₀ + binDigits q u - u)
      (s₀ + binDigits q u - u + binDigits q u) (binPadAddr L q u t₀ s₀ hq hb x) =
        L.blockVal s₀ (s₀ + u) x := by
    show (recodeLayout (recodeLayout L s₀ u q (binDigits q u)) t₀ u q (binDigits q u)).blockVal
      (s₀ + binDigits q u - u) (s₀ + binDigits q u - u + binDigits q u)
      (recodeAddr (recodeLayout L s₀ u q (binDigits q u)) t₀ u q
        (binDigits q u) hq0 hL₁n (recodeAddr L s₀ u q (binDigits q u) hq0 hsn x)) = _
    rw [recode_blockVal_after hq0 hL₁n _ (a := s₀) (b := s₀ + binDigits q u)
        (Nat.le_add_right _ _) hts hsn₁ (by omega) (by omega),
      recode_blockVal_new hq0 hsn, Nat.mod_eq_of_lt (hv₂.trans_le he)]
  rw [hL, swapPull, hval₁, hval₂]

end Binary

end Interchange6BinAux

open Interchange6BinAux in
/-- **Lemma A.8 (`lem:transfer12`), binary numerical padding**: the contract
`Interchange6BinaryStmt`. -/
theorem interchange6Binary_holds : Interchange6BinaryStmt := by
  intro L β _ q u t₀ s₀ hq hb A
  funext x
  show binPad q u t₀ s₀ hq hb A
      (swapPull (binPadLayout L q u t₀ s₀) t₀ (s₀ + binDigits q u - u) (binDigits q u)
        (binPadAddr L q u t₀ s₀ hq hb x)) = A (swapPull L t₀ s₀ u x)
  rw [← binPadAddr_swapPull hq hb x]
  exact embedAlong_apply (binPadAddr_injective hq hb) A _

end SubNLogN.Math.Networks
