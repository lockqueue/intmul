import SubNLogN.Math.Networks.AppCShear

/-!
# Proof of `PackedBadCardStmt` (Lemma A.9 (`lem:transfer13`) exceptional-set bound)

We prove `packedBadCard_holds : PackedBadCardStmt` (statement in `AppCShear.lean`): for `K ≥ 6`,
`L = fK` and `ρ < K`, the set `B` of triples `(x, y, z) ∈ [2^L]³` outside the good set `packedGood`
satisfies `2^K · |B| ≤ 80 (f − 1) 2^{3L}` (Lemma A.9 (`lem:transfer13`), eq. (`eq:transfer-packed`), [OAI26, §5.2, Lemma 13]).
The proof only uses `1 ≤ K` (implied by `6 ≤ K`), `L = fK` and `ρ < K`; no other hypotheses.

## Plan (union bound)
* Bit fields (`card_filter_field`): for `E ⊆ [0, 2^c)`, exactly `2^a · |E| · 2^h` numbers
  `v < 2^(a+c+h)` have their field `⌊v / 2^a⌋ mod 2^c` in `E`. The bijection onto
  `[2^a] × E × [2^h]` is `v ↦ (v mod 2^a, ⌊v/2^a⌋ mod 2^c, ⌊v/2^(a+c)⌋)` with inverse
  `(l, g, t) ↦ l + 2^a g + 2^(a+c) t` (`decomp`, `parts_of_sum`, `lt_of_parts`).
* One guard (`badChunk_card`): for `i < f − 1` the guard `guardVal K ρ i v` is the field with
  `a = ρ + iK + 1`, `c = K − 1`, and it fits: `a + c = ρ + (i+1)K ≤ L`. The excluded values
  `[0, 2^c) \ [10, 2^c − 11]` lie in `[0, 10) ∪ [2^c − 10, 2^c)`, so there are at most 20 of them
  (`card_excluded_le`), and `2^K · #{v < 2^L : guard i of v is bad} ≤ 2^K · 20 · 2^(L−c) = 40 · 2^L`.
* Triples (`pair_bound`): the triples whose guard `i` of `y` or of `z` is bad form
  `[2^L] × Bᵢ × [2^L] ∪ [2^L] × [2^L] × Bᵢ` (`badTriples`), of size at most `2 · 2^{2L} |Bᵢ|`, so
  `2^K` times their number is at most `80 · 2^{3L}`.
* `B` is contained in the union over `i < f − 1` of these sets (`¬ packedGood` means that some used
  guard fails), and `card_biUnion_le` sums the `f − 1` bounds. For `f ≤ 1` the union is empty.
-/

namespace SubNLogN.Math.Networks

namespace PackedBadAux

/-! ### Bit fields -/

/-- `x < B` and `y < C` give `x + B * y < B * C`. -/
lemma add_mul_lt_mul_of_lt {x y B C : ℕ} (hx : x < B) (hy : y < C) : x + B * y < B * C :=
  calc x + B * y < B + B * y := Nat.add_lt_add_right hx _
    _ = B * (y + 1) := by ring
    _ ≤ B * C := Nat.mul_le_mul_left _ hy

/-- Every `v` is the sum of its low part (below bit `a`), its field (bits `a, …, a + c − 1`) and its
high part (from bit `a + c` on). -/
lemma decomp (a c v : ℕ) :
    v % 2 ^ a + 2 ^ a * (v / 2 ^ a % 2 ^ c) + 2 ^ (a + c) * (v / 2 ^ (a + c)) = v := by
  have h1 := Nat.mod_add_div v (2 ^ a)
  have h2 := Nat.mod_add_div (v / 2 ^ a) (2 ^ c)
  have h3 : v / 2 ^ (a + c) = v / 2 ^ a / 2 ^ c := by rw [pow_add, Nat.div_div_eq_div_mul]
  calc v % 2 ^ a + 2 ^ a * (v / 2 ^ a % 2 ^ c) + 2 ^ (a + c) * (v / 2 ^ (a + c))
      = v % 2 ^ a + 2 ^ a * (v / 2 ^ a % 2 ^ c + 2 ^ c * (v / 2 ^ a / 2 ^ c)) := by
        rw [h3, pow_add]; ring
    _ = v % 2 ^ a + 2 ^ a * (v / 2 ^ a) := by rw [h2]
    _ = v := h1

/-- The low part, field and high part of `l + 2^a g + 2^(a+c) t` (with `l < 2^a`, `g < 2^c`) are
`l`, `g` and `t`. -/
lemma parts_of_sum {a c l g t : ℕ} (hl : l < 2 ^ a) (hg : g < 2 ^ c) :
    (l + 2 ^ a * g + 2 ^ (a + c) * t) % 2 ^ a = l ∧
      (l + 2 ^ a * g + 2 ^ (a + c) * t) / 2 ^ a % 2 ^ c = g ∧
      (l + 2 ^ a * g + 2 ^ (a + c) * t) / 2 ^ (a + c) = t := by
  have hpa : 0 < 2 ^ a := by positivity
  have hpac : 0 < 2 ^ (a + c) := by positivity
  have hlow : l + 2 ^ a * g < 2 ^ (a + c) := by
    rw [pow_add]; exact add_mul_lt_mul_of_lt hl hg
  have e1 : l + 2 ^ a * g + 2 ^ (a + c) * t = l + 2 ^ a * (g + 2 ^ c * t) := by
    rw [pow_add]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  · rw [e1, Nat.add_mul_div_left _ _ hpa, Nat.div_eq_of_lt hl, zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hg]
  · rw [Nat.add_mul_div_left _ _ hpac, Nat.div_eq_of_lt hlow, zero_add]

/-- `l + 2^a g + 2^(a+c) t < 2^(a+c+h)` when `l < 2^a`, `g < 2^c` and `t < 2^h`. -/
lemma lt_of_parts {a c h l g t : ℕ} (hl : l < 2 ^ a) (hg : g < 2 ^ c) (ht : t < 2 ^ h) :
    l + 2 ^ a * g + 2 ^ (a + c) * t < 2 ^ (a + c + h) := by
  have hlow : l + 2 ^ a * g < 2 ^ (a + c) := by
    rw [pow_add]; exact add_mul_lt_mul_of_lt hl hg
  rw [pow_add (2 : ℕ) (a + c) h]
  exact add_mul_lt_mul_of_lt hlow ht

/-- Counting a bit field: for `E ⊆ [0, 2^c)`, exactly `2^a · |E| · 2^h` numbers `v < 2^(a+c+h)`
have their field `⌊v / 2^a⌋ mod 2^c` in `E`. -/
lemma card_filter_field (a c h : ℕ) (E : Finset ℕ) (hE : ∀ g ∈ E, g < 2 ^ c) :
    ((Finset.range (2 ^ (a + c + h))).filter (fun v => v / 2 ^ a % 2 ^ c ∈ E)).card =
      2 ^ a * (E.card * 2 ^ h) := by
  have key : ((Finset.range (2 ^ (a + c + h))).filter (fun v => v / 2 ^ a % 2 ^ c ∈ E)).card =
      (Finset.range (2 ^ a) ×ˢ E ×ˢ Finset.range (2 ^ h)).card := by
    apply Finset.card_nbij' (fun v => (v % 2 ^ a, v / 2 ^ a % 2 ^ c, v / 2 ^ (a + c)))
      (fun p => p.1 + 2 ^ a * p.2.1 + 2 ^ (a + c) * p.2.2)
    · intro v hv
      have hv' := Finset.mem_filter.1 (Finset.mem_coe.1 hv)
      have hvlt : v < 2 ^ (a + c + h) := Finset.mem_range.1 hv'.1
      have hhi : v / 2 ^ (a + c) < 2 ^ h := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]
        calc v < 2 ^ (a + c + h) := hvlt
          _ = 2 ^ h * 2 ^ (a + c) := by rw [pow_add, mul_comm]
      exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ (by positivity)),
        Finset.mem_product.2 ⟨hv'.2, Finset.mem_range.2 hhi⟩⟩)
    · rintro ⟨l, g, t⟩ hp
      have hp' := Finset.mem_product.1 (Finset.mem_coe.1 hp)
      have hl : l < 2 ^ a := Finset.mem_range.1 hp'.1
      have hgE : g ∈ E := (Finset.mem_product.1 hp'.2).1
      have ht : t < 2 ^ h := Finset.mem_range.1 (Finset.mem_product.1 hp'.2).2
      have hg : g < 2 ^ c := hE g hgE
      have hfield : (l + 2 ^ a * g + 2 ^ (a + c) * t) / 2 ^ a % 2 ^ c ∈ E := by
        rw [(parts_of_sum (t := t) hl hg).2.1]; exact hgE
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_of_parts hl hg ht), hfield⟩)
    · intro v _
      exact decomp a c v
    · rintro ⟨l, g, t⟩ hp
      have hp' := Finset.mem_product.1 (Finset.mem_coe.1 hp)
      have hl : l < 2 ^ a := Finset.mem_range.1 hp'.1
      have hg : g < 2 ^ c := hE g (Finset.mem_product.1 hp'.2).1
      obtain ⟨e1, e2, e3⟩ := parts_of_sum (t := t) hl hg
      show ((l + 2 ^ a * g + 2 ^ (a + c) * t) % 2 ^ a,
        (l + 2 ^ a * g + 2 ^ (a + c) * t) / 2 ^ a % 2 ^ c,
        (l + 2 ^ a * g + 2 ^ (a + c) * t) / 2 ^ (a + c)) = (l, g, t)
      rw [e1, e2, e3]
  rw [key, Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range]

/-! ### One guard -/

/-- The chunk values `v < 2^L` whose guard `i` is bad, i.e. outside `[10, 2^(K−1) − 11]`. -/
def badChunk (L K ρ i : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ L)).filter
    (fun v => ¬ (10 ≤ guardVal K ρ i v ∧ guardVal K ρ i v + 11 ≤ 2 ^ (K - 1)))

lemma mem_badChunk {L K ρ i v : ℕ} :
    v ∈ badChunk L K ρ i ↔
      v < 2 ^ L ∧ ¬ (10 ≤ guardVal K ρ i v ∧ guardVal K ρ i v + 11 ≤ 2 ^ (K - 1)) := by
  unfold badChunk; rw [Finset.mem_filter, Finset.mem_range]

/-- At most twenty of the `2^c` values of a `c`-bit field lie outside `[10, 2^c − 11]`. -/
lemma card_excluded_le (c : ℕ) :
    ((Finset.range (2 ^ c)).filter (fun g => ¬ (10 ≤ g ∧ g + 11 ≤ 2 ^ c))).card ≤ 20 := by
  have hsub : (Finset.range (2 ^ c)).filter (fun g => ¬ (10 ≤ g ∧ g + 11 ≤ 2 ^ c)) ⊆
      Finset.range 10 ∪ Finset.Ico (2 ^ c - 10) (2 ^ c) := by
    intro g hg
    rw [Finset.mem_filter, Finset.mem_range] at hg
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  calc _ ≤ (Finset.range 10 ∪ Finset.Ico (2 ^ c - 10) (2 ^ c)).card := Finset.card_le_card hsub
    _ ≤ (Finset.range 10).card + (Finset.Ico (2 ^ c - 10) (2 ^ c)).card :=
        Finset.card_union_le _ _
    _ ≤ 20 := by rw [Finset.card_range, Nat.card_Ico]; omega

/-- Final arithmetic of one guard: `2^(c+1) · 2^a · e · 2^h ≤ 40 · 2^(a+c+h)` when `e ≤ 20`. -/
lemma guard_arith (a c h e : ℕ) (he : e ≤ 20) :
    2 ^ (c + 1) * (2 ^ a * (e * 2 ^ h)) ≤ 40 * 2 ^ (a + c + h) :=
  calc 2 ^ (c + 1) * (2 ^ a * (e * 2 ^ h)) = e * (2 * (2 ^ a * 2 ^ c * 2 ^ h)) := by ring
    _ ≤ 20 * (2 * (2 ^ a * 2 ^ c * 2 ^ h)) := Nat.mul_le_mul_right _ he
    _ = 40 * 2 ^ (a + c + h) := by rw [pow_add, pow_add]; ring

/-- One guard: for `i < f − 1` (with `K ≥ 1`, `L = fK`, `ρ < K`),
`2^K · #{v < 2^L : guard i of v is bad} ≤ 40 · 2^L`. -/
lemma badChunk_card (L K ρ f i : ℕ) (hK : 1 ≤ K) (hL : L = f * K) (hρ : ρ < K)
    (hi : i < f - 1) : 2 ^ K * (badChunk L K ρ i).card ≤ 40 * 2 ^ L := by
  obtain ⟨c, rfl⟩ : ∃ c, K = c + 1 := ⟨K - 1, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, a = ρ + i * (c + 1) + 1 := ⟨_, rfl⟩
  have hfit : a + c ≤ L := by
    have h1 : (i + 2) * (c + 1) ≤ f * (c + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [ha, hL]
    nlinarith
  obtain ⟨h, hh⟩ : ∃ h, L = a + c + h := ⟨L - (a + c), by omega⟩
  have heq : badChunk L (c + 1) ρ i =
      (Finset.range (2 ^ (a + c + h))).filter (fun v => v / 2 ^ a % 2 ^ c ∈
        (Finset.range (2 ^ c)).filter (fun g => ¬ (10 ≤ g ∧ g + 11 ≤ 2 ^ c))) := by
    unfold badChunk guardVal
    rw [← hh, ← ha, Nat.add_sub_cancel]
    apply Finset.filter_congr
    intro v _
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun hb => ⟨Nat.mod_lt _ (by positivity), hb⟩, fun hb => hb.2⟩
  rw [heq, card_filter_field a c h _
    (fun g hg => Finset.mem_range.1 (Finset.mem_filter.1 hg).1), hh]
  exact guard_arith a c h _ (card_excluded_le c)

/-! ### Triples -/

/-- The triples in `[2^L]³` whose guard `i` of `y` or of `z` is bad. -/
def badTriples (L K ρ i : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.range (2 ^ L) ×ˢ badChunk L K ρ i ×ˢ Finset.range (2 ^ L) ∪
    Finset.range (2 ^ L) ×ˢ Finset.range (2 ^ L) ×ˢ badChunk L K ρ i

/-- One guard index for both chunks: `2^K · |badTriples| ≤ 80 · 2^{3L}`. -/
lemma pair_bound (L K ρ f i : ℕ) (hK : 1 ≤ K) (hL : L = f * K) (hρ : ρ < K) (hi : i < f - 1) :
    2 ^ K * (badTriples L K ρ i).card ≤ 80 * 2 ^ (3 * L) := by
  have hB := badChunk_card L K ρ f i hK hL hρ hi
  have hu := Finset.card_union_le
    (Finset.range (2 ^ L) ×ˢ badChunk L K ρ i ×ˢ Finset.range (2 ^ L))
    (Finset.range (2 ^ L) ×ˢ Finset.range (2 ^ L) ×ˢ badChunk L K ρ i)
  simp only [Finset.card_product, Finset.card_range] at hu
  unfold badTriples
  calc _ ≤ 2 ^ K * (2 ^ L * ((badChunk L K ρ i).card * 2 ^ L) +
          2 ^ L * (2 ^ L * (badChunk L K ρ i).card)) := Nat.mul_le_mul_left _ hu
    _ = 2 * 2 ^ L * 2 ^ L * (2 ^ K * (badChunk L K ρ i).card) := by ring
    _ ≤ 2 * 2 ^ L * 2 ^ L * (40 * 2 ^ L) := Nat.mul_le_mul_left _ hB
    _ = 80 * 2 ^ (3 * L) := by ring

/-- A triple in `[2^L]³` outside the good set lies in `badTriples L K ρ i` for some `i < f − 1`
(for any decidability instance used by the filter; the instance is an implicit argument so that it
is found by unification with the contract's classical instance). -/
lemma bad_subset (L K ρ f : ℕ) {inst : DecidablePred (fun xyz : ℕ × ℕ × ℕ => ¬ packedGood K ρ f xyz)} :
    (Finset.range (2 ^ L) ×ˢ Finset.range (2 ^ L) ×ˢ Finset.range (2 ^ L)).filter
        (fun xyz => ¬ packedGood K ρ f xyz) ⊆
      (Finset.range (f - 1)).biUnion (badTriples L K ρ) := by
  intro xyz hxyz
  obtain ⟨hmem, hbad⟩ := Finset.mem_filter.1 hxyz
  simp only [Finset.mem_product, Finset.mem_range] at hmem
  rw [Finset.mem_biUnion]
  by_contra hnot
  apply hbad
  unfold packedGood
  intro i hi
  have hi' : xyz ∉ badTriples L K ρ i := fun h => hnot ⟨i, Finset.mem_range.2 hi, h⟩
  simp only [badTriples, Finset.mem_union, Finset.mem_product, Finset.mem_range,
    mem_badChunk] at hi'
  tauto

end PackedBadAux

open PackedBadAux in
/-- **Lemma A.9 (`lem:transfer13`) exceptional set** (eq. (`eq:transfer-packed`)): for `K ≥ 6`, `L = fK` and `ρ < K`,
the set `B ⊆ [2^L]³` of triples outside `packedGood` satisfies `2^K · |B| ≤ 80 (f − 1) 2^{3L}`. -/
theorem packedBadCard_holds : PackedBadCardStmt := by
  intro L K ρ f hK hL hρ
  have hK1 : 1 ≤ K := by omega
  calc _ ≤ 2 ^ K * ((Finset.range (f - 1)).biUnion (badTriples L K ρ)).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card (bad_subset L K ρ f))
    _ ≤ 2 ^ K * ∑ i ∈ Finset.range (f - 1), (badTriples L K ρ i).card :=
        Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (f - 1), 2 ^ K * (badTriples L K ρ i).card := by rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (f - 1), 80 * 2 ^ (3 * L) :=
        Finset.sum_le_sum fun i hi => pair_bound L K ρ f i hK1 hL hρ (Finset.mem_range.1 hi)
    _ = 80 * (f - 1) * 2 ^ (3 * L) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

end SubNLogN.Math.Networks
