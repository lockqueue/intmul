import SubNLogN.Math.Networks.AppCLayerProc

/-!
# Proposition A.11 (`Prop71LayerSpecStmt`): the encode/decode and padding layer of `layerRun`

Helper lemmas for the proof of `Prop71LayerSpecStmt` (`Math/Networks/AppCLayerProc.lean`),
used in `Proofs/LayerSpecProof.lean` (`Prop71` is a historical identifier prefix retained for stability). Namespace
`SubNLogN.Math.Networks.LayerSpecPadAux`. All results are unconditional (no hypotheses beyond those
displayed).

* (E1) `encodeAddr_decodeAddr`: `encodeAddr ∘ decodeAddr = id` on `layerLayout` addresses, hence
  `encodeArr_decodeArr`. Also `decodeAddr_encodeAddr` (so `DecodeEncodeAddrStmt` holds,
  `decodeEncodeAddr_holds`).
* (E2) `runIn_topClass`: every address is in the prefix class `topClass`.
* (E3) `phase3_decode`: decoding phase 3 gives `Q_P(b^D · i^{#sel} · decode)`.
* (E4) `phase1_eq`: phase 1 on an encoded array is the kernels of phase 1 on the encoded
  `i^{#sel}`-twisted array.
* (E5) `mergeL` (the row reshape on `LayerAddr`): `mergeL_chunk` (chunk `j` of the merged address is
  chunk `q + j`), `mergeL_suffix`, `mergeL_prefix` (the merged prefix depends only on the prefix and
  the chunks `< q`), and `embedArr_mergeL` (padded rows are never read: if `2^{qK} ≤ R`, the
  embedded array at a merged address is the original record).
-/

namespace SubNLogN.Math.Networks.LayerSpecPadAux

open SubNLogN.Math.Networks SubNLogN.Math.Networks.Model SubNLogN.Math.Walsh SubNLogN.Math.Common

/-! ## Generic facts on layouts -/

/-- Values of a dependent address at indices with equal values agree. -/
theorem addr_val_eq {L : Layout} (y : L.Addr) {a : ℕ} (ha : a < L.n) (i : Fin L.n)
    (h : a = i.val) : (y ⟨a, ha⟩).val = (y i).val := by
  subst h
  rfl

/-- Division with remainder by `R` is unique. -/
theorem mul_add_lt_inj {R a b a' b' : ℕ} (hb : b < R) (hb' : b' < R)
    (h : a * R + b = a' * R + b') : a = a' ∧ b = b' := by
  have hR : 0 < R := by omega
  have h1 : (a * R + b) / R = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hb, Nat.zero_add]
  have h2 : (a' * R + b') / R = a' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hb', Nat.zero_add]
  have h3 : (a * R + b) % R = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have h4 : (a' * R + b') % R = b' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb']
  exact ⟨by rw [← h1, ← h2, h], by rw [← h3, ← h4, h]⟩

/-- A block only depends on its fields. -/
theorem blockVal_congr' {L : Layout} {t₀ t₁ : ℕ} {x y : L.Addr}
    (h : ∀ j : Fin L.n, t₀ ≤ j.val → j.val < t₁ → x j = y j) :
    L.blockVal t₀ t₁ x = L.blockVal t₀ t₁ y := by
  unfold Layout.blockVal
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, inBlock] at hj
  rw [h j hj.2.1 hj.2.2]

theorem filter_inBlock_succ {n : ℕ} (t₀ t : ℕ) (h₀ : t₀ ≤ t) (ht : t < n) :
    Finset.univ.filter (inBlock t₀ (t + 1) (n := n)) =
      insert ⟨t, ht⟩ (Finset.univ.filter (inBlock t₀ t (n := n))) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, inBlock,
    Fin.ext_iff]
  omega

theorem not_mem_filter_inBlock {n : ℕ} (t₀ t : ℕ) (ht : t < n) :
    (⟨t, ht⟩ : Fin n) ∉ Finset.univ.filter (inBlock t₀ t (n := n)) := by
  simp [inBlock]

/-- Peeling the last field of a block. -/
theorem blockVal_succ {L : Layout} (t₀ t : ℕ) (h₀ : t₀ ≤ t) (ht : t < L.n) (x : L.Addr) :
    L.blockVal t₀ (t + 1) x = L.blockVal t₀ t x * L.r ⟨t, ht⟩ + (x ⟨t, ht⟩).val := by
  unfold Layout.blockVal
  rw [filter_inBlock_succ t₀ t h₀ ht, Finset.sum_insert (not_mem_filter_inBlock t₀ t ht),
    Finset.sum_mul]
  have hp1 : L.place (t + 1) ⟨t, ht⟩ = 1 := by
    unfold Layout.place
    apply Finset.prod_eq_one
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hj
    omega
  rw [hp1, mul_one, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
  rw [mul_assoc]
  congr 1
  unfold Layout.place
  have hfilt2 : Finset.univ.filter (fun j' : Fin L.n => j < j' ∧ j'.val < t + 1) =
      insert ⟨t, ht⟩ (Finset.univ.filter (fun j' : Fin L.n => j < j' ∧ j'.val < t)) := by
    ext j'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
      Fin.ext_iff]
    omega
  have hnot2 : (⟨t, ht⟩ : Fin L.n) ∉
      Finset.univ.filter (fun j' : Fin L.n => j < j' ∧ j'.val < t) := by
    simp
  rw [hfilt2, Finset.prod_insert hnot2, mul_comm]

theorem blockRange_succ {L : Layout} (t₀ t : ℕ) (h₀ : t₀ ≤ t) (ht : t < L.n) :
    L.blockRange t₀ (t + 1) = L.blockRange t₀ t * L.r ⟨t, ht⟩ := by
  unfold Layout.blockRange
  rw [filter_inBlock_succ t₀ t h₀ ht, Finset.prod_insert (not_mem_filter_inBlock t₀ t ht),
    mul_comm]

theorem blockVal_empty {L : Layout} (t₀ t : ℕ) (h : t ≤ t₀) (x : L.Addr) :
    L.blockVal t₀ t x = 0 := by
  unfold Layout.blockVal
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
  omega

theorem blockRange_empty {L : Layout} (t₀ t : ℕ) (h : t ≤ t₀) : L.blockRange t₀ t = 1 := by
  unfold Layout.blockRange
  apply Finset.prod_eq_one
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
  omega

/-- The value of a block is below its range. -/
theorem blockVal_lt_blockRange {L : Layout} (t₀ : ℕ) :
    ∀ t, t ≤ L.n → ∀ x : L.Addr, L.blockVal t₀ t x < L.blockRange t₀ t := by
  intro t
  induction t with
  | zero =>
    intro _ x
    rw [blockVal_empty _ _ (Nat.zero_le _), blockRange_empty _ _ (Nat.zero_le _)]
    exact Nat.one_pos
  | succ t ih =>
    intro ht x
    by_cases h₀ : t₀ ≤ t
    · rw [blockVal_succ t₀ t h₀ (by omega) x, blockRange_succ t₀ t h₀ (by omega)]
      have h1 := ih (by omega) x
      have h2 := (x ⟨t, by omega⟩).isLt
      have h3 : (L.blockVal t₀ t x + 1) * L.r ⟨t, by omega⟩ ≤
          L.blockRange t₀ t * L.r ⟨t, by omega⟩ := Nat.mul_le_mul_right _ h1
      nlinarith
    · rw [blockVal_empty _ _ (by omega), blockRange_empty _ _ (by omega)]
      exact Nat.one_pos

/-- Equal block values force equal fields. -/
theorem eq_of_blockVal_eq {L : Layout} (t₀ : ℕ) :
    ∀ t, t ≤ L.n → ∀ x y : L.Addr, L.blockVal t₀ t x = L.blockVal t₀ t y →
      ∀ j : Fin L.n, t₀ ≤ j.val → j.val < t → x j = y j := by
  intro t
  induction t with
  | zero => intro _ x y _ j _ hj; omega
  | succ t ih =>
    intro ht x y h j hj₀ hj
    have h₀ : t₀ ≤ t := by omega
    have htn : t < L.n := by omega
    rw [blockVal_succ t₀ t h₀ htn x, blockVal_succ t₀ t h₀ htn y] at h
    obtain ⟨hb, hv⟩ := mul_add_lt_inj (x ⟨t, htn⟩).isLt (y ⟨t, htn⟩).isLt h
    by_cases hjt : j.val = t
    · have hj' : j = ⟨t, htn⟩ := Fin.ext hjt
      subst hj'
      exact Fin.ext hv
    · exact ih (by omega) x y hb j hj₀ (by omega)

/-- A single field as a block. -/
theorem blockVal_single (L : Layout) (t : ℕ) (ht : t < L.n) (y : L.Addr) :
    L.blockVal t (t + 1) y = (y ⟨t, ht⟩).val := by
  rw [blockVal_succ t t le_rfl ht, blockVal_empty t t le_rfl, zero_mul, zero_add]

/-! ## Addresses of `layerLayout` -/

/-- The chunk fields `1 ≤ i ≤ DK` of `layerLayout` are binary. -/
theorem r_chunk {A K D S : ℕ} (i : Fin (layerLayout A K D S).n) (h0 : i.val ≠ 0)
    (h1 : i.val ≤ D * K) : (layerLayout A K D S).r i = 2 := by
  simp only [layerLayout]
  rw [if_neg h0, if_pos h1]

/-- The field of bit `t` of chunk `j` is in range. -/
theorem chunkIdx_lt {A K D S : ℕ} (j : Fin D) (t : Fin K) :
    1 + j.val * K + (K - 1 - t.val) < (layerLayout A K D S).n := by
  have hj := j.isLt
  have ht := t.isLt
  have : j.val * K + K ≤ D * K := by nlinarith
  simp only [layerLayout]
  omega

/-- `encodeAddr` on the prefix field. -/
theorem encodeAddr_val_zero {A K D S : ℕ} (x : LayerAddr A K D S)
    (i : Fin (layerLayout A K D S).n) (h0 : i.val = 0) : ((encodeAddr x) i).val = x.1.val := by
  simp only [encodeAddr, dif_pos h0]

/-- `encodeAddr` on the suffix field. -/
theorem encodeAddr_val_last {A K D S : ℕ} (x : LayerAddr A K D S)
    (i : Fin (layerLayout A K D S).n) (h0 : i.val ≠ 0) (h1 : ¬ i.val ≤ D * K) :
    ((encodeAddr x) i).val = x.2.2.val := by
  simp only [encodeAddr, dif_neg h0, dif_neg h1]

/-- `encodeAddr` on the field of bit `t` of chunk `j`. -/
theorem encodeAddr_val_chunk {A K D S : ℕ} (x : LayerAddr A K D S) (j : Fin D) (t : Fin K)
    (i : Fin (layerLayout A K D S).n) (hi : i.val = 1 + j.val * K + (K - 1 - t.val)) :
    ((encodeAddr x) i).val = if x.2.1 j t then 1 else 0 := by
  have hj := j.isLt
  have ht := t.isLt
  have hK : 0 < K := by omega
  have h0 : i.val ≠ 0 := by omega
  have h1 : i.val ≤ D * K := by
    have : j.val * K + K ≤ D * K := by nlinarith
    omega
  have hsplit : i.val - 1 = (K - 1 - t.val) + j.val * K := by omega
  have hdiv : (i.val - 1) / K = j.val := by
    rw [hsplit, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hmod : K - 1 - (i.val - 1) % K = t.val := by
    rw [hsplit, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  have ej : (⟨(i.val - 1) / K, by rw [hdiv]; exact hj⟩ : Fin D) = j := Fin.ext hdiv
  have et : (⟨K - 1 - (i.val - 1) % K, by omega⟩ : Fin K) = t := Fin.ext hmod
  simp only [encodeAddr, dif_neg h0, dif_pos h1, dif_pos hK, ej, et]

/-- `decodeAddr` on bit `t` of chunk `j`. -/
theorem decodeAddr_chunk {A K D S : ℕ} (y : (layerLayout A K D S).Addr) (j : Fin D) (t : Fin K)
    (i : Fin (layerLayout A K D S).n) (hi : i.val = 1 + j.val * K + (K - 1 - t.val)) :
    (decodeAddr y).2.1 j t = decide ((y i).val = 1) := by
  show decide ((y ⟨1 + j.val * K + (K - 1 - t.val), chunkIdx_lt j t⟩).val = 1) =
    decide ((y i).val = 1)
  rw [addr_val_eq y (chunkIdx_lt j t) i hi.symm]

/-- (E1) `encodeAddr ∘ decodeAddr = id`. -/
theorem encodeAddr_decodeAddr {A K D S : ℕ} (y : (layerLayout A K D S).Addr) :
    encodeAddr (decodeAddr y) = y := by
  funext i
  apply Fin.ext
  have hn := i.isLt
  simp only [layerLayout] at hn
  by_cases h0 : i.val = 0
  · rw [encodeAddr_val_zero _ i h0]
    exact addr_val_eq y _ i h0.symm
  · by_cases h1 : i.val ≤ D * K
    · have hK : 0 < K := by
        rcases Nat.eq_zero_or_pos K with hK | hK
        · subst hK
          omega
        · exact hK
      have hlt : (y i).val < 2 := lt_of_lt_of_eq (y i).isLt (r_chunk i h0 h1)
      have hjD : (i.val - 1) / K < D := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
      have htK : K - 1 - (i.val - 1) % K < K := by omega
      have hi : i.val = 1 + (⟨(i.val - 1) / K, hjD⟩ : Fin D).val * K +
          (K - 1 - (⟨K - 1 - (i.val - 1) % K, htK⟩ : Fin K).val) := by
        have h2 := Nat.div_add_mod' (i.val - 1) K
        have h3 := Nat.mod_lt (i.val - 1) hK
        show i.val = 1 + (i.val - 1) / K * K + (K - 1 - (K - 1 - (i.val - 1) % K))
        omega
      rw [encodeAddr_val_chunk _ _ _ i hi, decodeAddr_chunk y _ _ i hi]
      rcases (show (y i).val = 0 ∨ (y i).val = 1 by omega) with hv | hv <;> simp [hv]
    · rw [encodeAddr_val_last _ i h0 h1]
      exact addr_val_eq y _ i (by omega)

/-- (E1) `encodeArr ∘ decodeArr = id`. -/
theorem encodeArr_decodeArr {A K D S rr : ℕ} (B : (layerLayout A K D S).Addr → Fin rr → ℂ) :
    encodeArr (decodeArr B) = B := by
  funext y
  simp only [encodeArr, decodeArr, encodeAddr_decodeAddr]

/-- `decodeAddr ∘ encodeAddr = id`. -/
theorem decodeAddr_encodeAddr {A K D S : ℕ} (x : LayerAddr A K D S) :
    decodeAddr (encodeAddr x) = x := by
  obtain ⟨a, c, s⟩ := x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Fin.ext
    exact encodeAddr_val_zero (a, c, s) _ rfl
  · funext j t
    rw [decodeAddr_chunk _ j t ⟨_, chunkIdx_lt j t⟩ rfl,
      encodeAddr_val_chunk (a, c, s) j t ⟨_, chunkIdx_lt j t⟩ rfl]
    show decide ((if c j t = true then (1 : ℕ) else 0) = 1) = c j t
    cases c j t <;> rfl
  · apply Fin.ext
    exact encodeAddr_val_last (a, c, s) ⟨D * K + 1, by simp [layerLayout]⟩ (by simp)
      (by simp)

/-- The layout round trip contract holds. -/
theorem decodeEncodeAddr_holds : DecodeEncodeAddrStmt :=
  fun _ _ _ _ x => decodeAddr_encodeAddr x

/-! ## The prefix class -/

theorem topClass_mem {A K D S : ℕ} (y : (layerLayout A K D S).Addr) :
    (topClass A K D S).mem y :=
  Nat.mod_one _

/-- (E2) Every address is in the prefix class. -/
theorem runIn_topClass {A K D S : ℕ} {β : Type} (s : Step (layerLayout A K D S) β)
    (B : (layerLayout A K D S).Addr → β) : s.runIn (topClass A K D S) B = s.run B := by
  funext x
  simp only [Step.runIn, if_pos (topClass_mem x)]

/-! ## Phases 1 and 3 -/

/-- The selected-bit count of an encoded address. -/
theorem selCount_encodeAddr {A K D S : ℕ} (ρ : Fin K) (x : LayerAddr A K D S) :
    ∑ j ∈ Finset.range D, (layerLayout A K D S).blockVal (selField K ρ.val j)
        (selField K ρ.val j + 1) (encodeAddr x) =
      (Finset.univ.filter fun j => x.2.1 j ρ = true).card := by
  rw [Finset.sum_range, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [blockVal_single (layerLayout A K D S) (selField K ρ.val j) (chunkIdx_lt j ρ)]
  exact encodeAddr_val_chunk x j ρ _ rfl

/-- (E3) Decoding phase 3: `Q_P(b^D · i^{#sel} · decode B)`. -/
theorem phase3_decode {A K D S rr : ℕ} (P : ℕ) (ρ : Fin K)
    (B : (layerLayout A K D S).Addr → Fin rr → ℂ) :
    decodeArr (ProcK.run 0 (layerPhase3 A K D S rr ρ.val P) (topClass A K D S) B) =
      truncArr P (fun x k => bD D *
        (Complex.I ^ (Finset.univ.filter fun j => x.2.1 j ρ = true).card * decodeArr B x k)) := by
  funext x k
  simp only [layerPhase3, ProcK.run, List.foldl_cons, List.foldl_nil, runIn_topClass, Step.run,
    sDiag, decodeArr, truncArr, Function.comp_apply, Pi.smul_apply, smul_eq_mul,
    selCount_encodeAddr]

/-- (E4) Phase 1 on an encoded array: `𝒮_D` twists the array by `i^{#sel}`, then the kernels. -/
theorem phase1_eq {A K D S rr : ℕ} (d : ℕ) (ρ : Fin K) (z : RArr (LayerAddr A K D S) rr) :
    ProcK.run 0 (layerPhase1 A K D S rr ρ.val d) (topClass A K D S) (encodeArr z) =
      ProcK.run 0 ((List.range (min (q0Of d) D)).flatMap fun j => dgate (selField K ρ.val j))
        (topClass A K D S)
        (encodeArr (fun y k => Complex.I ^ (Finset.univ.filter fun j => y.2.1 j ρ = true).card *
          z y k)) := by
  have hS : Step.runIn (topClass A K D S) (sDiag ρ.val) (encodeArr z) =
      encodeArr (fun y k => Complex.I ^ (Finset.univ.filter fun j => y.2.1 j ρ = true).card *
        z y k) := by
    funext y k
    rw [runIn_topClass]
    simp only [Step.run, sDiag, encodeArr, Pi.smul_apply, smul_eq_mul]
    rw [← selCount_encodeAddr ρ (decodeAddr y), encodeAddr_decodeAddr]
  show List.foldl (fun B s => Step.runIn (topClass A K D S) s B) (encodeArr z)
      ([sDiag ρ.val] ++ ((List.range (min (q0Of d) D)).flatMap fun j => dgate (selField K ρ.val j))) =
    _
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, hS]
  rfl

/-! ## The row reshape -/

theorem blockRange_chunks {A K D S : ℕ} (m : ℕ) (hm : m ≤ D * K) :
    (layerLayout A K D S).blockRange 1 (1 + m) = 2 ^ m := by
  induction m with
  | zero => exact blockRange_empty _ _ (by omega)
  | succ m ih =>
    have hlt : 1 + m < (layerLayout A K D S).n := by simp only [layerLayout]; omega
    rw [show 1 + (m + 1) = (1 + m) + 1 by omega, blockRange_succ 1 (1 + m) (by omega) hlt,
      ih (by omega), r_chunk ⟨1 + m, hlt⟩ (show 1 + m ≠ 0 by omega) (show 1 + m ≤ D * K by omega),
      pow_succ]

theorem mergeAddr_val_zero {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D)
    (x : (layerLayout A K D S).Addr) (i : Fin (layerLayout (A * R) K (D - q) S).n)
    (h0 : i.val = 0) :
    (mergeAddr A K D S q R hR hq x i).val =
      (x ⟨0, by simp [layerLayout]⟩).val * R +
        (layerLayout A K D S).blockVal 1 (1 + q * K) x % R := by
  simp only [mergeAddr, dif_pos h0]

theorem mergeAddr_val_mid {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D)
    (x : (layerLayout A K D S).Addr) (i : Fin (layerLayout (A * R) K (D - q) S).n)
    (h0 : i.val ≠ 0) (h1 : i.val ≤ (D - q) * K)
    (hlt : i.val + q * K < (layerLayout A K D S).n) :
    (mergeAddr A K D S q R hR hq x i).val = (x ⟨i.val + q * K, hlt⟩).val := by
  simp only [mergeAddr, dif_neg h0, dif_pos h1]

theorem mergeAddr_val_last {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D)
    (x : (layerLayout A K D S).Addr) (i : Fin (layerLayout (A * R) K (D - q) S).n)
    (h0 : i.val ≠ 0) (h1 : ¬ i.val ≤ (D - q) * K) :
    (mergeAddr A K D S q R hR hq x i).val = (x ⟨D * K + 1, by simp [layerLayout]⟩).val := by
  simp only [mergeAddr, dif_neg h0, dif_neg h1]

/-- (E5) The row reshape on `LayerAddr`. -/
def mergeL {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D) (u : LayerAddr A K D S) :
    LayerAddr (A * R) K (D - q) S :=
  decodeAddr (mergeAddr A K D S q R hR hq (encodeAddr u))

theorem encodeAddr_mergeL {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D) (u : LayerAddr A K D S) :
    encodeAddr (mergeL hR hq u) = mergeAddr A K D S q R hR hq (encodeAddr u) :=
  encodeAddr_decodeAddr _

/-- (E5) Chunk `j` of the merged address is chunk `q + j`. -/
theorem mergeL_chunk {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D) (u : LayerAddr A K D S)
    (j : Fin (D - q)) : (mergeL hR hq u).2.1 j = u.2.1 ⟨q + j.val, by omega⟩ := by
  funext t
  have hj := j.isLt
  have ht := t.isLt
  have hjK : (j.val + 1) * K ≤ (D - q) * K := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hjK
  have hqK : q * K + (D - q) * K = D * K := by rw [← Nat.add_mul, Nat.add_sub_cancel' hq]
  have hlt : 1 + j.val * K + (K - 1 - t.val) + q * K < (layerLayout A K D S).n := by
    simp only [layerLayout]; omega
  unfold mergeL
  rw [decodeAddr_chunk (mergeAddr A K D S q R hR hq (encodeAddr u)) j t
      ⟨1 + j.val * K + (K - 1 - t.val), chunkIdx_lt j t⟩ rfl,
    mergeAddr_val_mid hR hq (encodeAddr u) ⟨1 + j.val * K + (K - 1 - t.val), chunkIdx_lt j t⟩
      (show 1 + j.val * K + (K - 1 - t.val) ≠ 0 by omega)
      (show 1 + j.val * K + (K - 1 - t.val) ≤ (D - q) * K by omega) hlt,
    encodeAddr_val_chunk u ⟨q + j.val, by omega⟩ t ⟨1 + j.val * K + (K - 1 - t.val) + q * K, hlt⟩
      (show 1 + j.val * K + (K - 1 - t.val) + q * K = 1 + (q + j.val) * K + (K - 1 - t.val) by
        ring)]
  cases u.2.1 ⟨q + j.val, by omega⟩ t <;> simp

/-- (E5) The merged address keeps the suffix. -/
theorem mergeL_suffix {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D) (u : LayerAddr A K D S) :
    (mergeL hR hq u).2.2 = u.2.2 := by
  apply Fin.ext
  show (mergeAddr A K D S q R hR hq (encodeAddr u)
    ⟨(D - q) * K + 1, by simp [layerLayout]⟩).val = u.2.2.val
  rw [mergeAddr_val_last hR hq (encodeAddr u) ⟨(D - q) * K + 1, by simp [layerLayout]⟩
    (show (D - q) * K + 1 ≠ 0 by omega) (show ¬ (D - q) * K + 1 ≤ (D - q) * K by omega)]
  exact encodeAddr_val_last u ⟨D * K + 1, by simp [layerLayout]⟩ (show D * K + 1 ≠ 0 by omega)
    (show ¬ D * K + 1 ≤ D * K by omega)

/-- (E5) The merged prefix only depends on the prefix and the chunks `< q`. -/
theorem mergeL_prefix {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D) {u u' : LayerAddr A K D S}
    (h1 : u.1 = u'.1) (h2 : ∀ j : Fin D, j.val < q → u.2.1 j = u'.2.1 j) :
    (mergeL hR hq u).1 = (mergeL hR hq u').1 := by
  apply Fin.ext
  show (mergeAddr A K D S q R hR hq (encodeAddr u) ⟨0, by simp [layerLayout]⟩).val =
    (mergeAddr A K D S q R hR hq (encodeAddr u') ⟨0, by simp [layerLayout]⟩).val
  have hb : (layerLayout A K D S).blockVal 1 (1 + q * K) (encodeAddr u) =
      (layerLayout A K D S).blockVal 1 (1 + q * K) (encodeAddr u') := by
    apply blockVal_congr'
    intro i hi1 hi2
    apply Fin.ext
    have hK : 0 < K := by
      rcases Nat.eq_zero_or_pos K with hK | hK
      · subst hK
        omega
      · exact hK
    have hjq : (i.val - 1) / K < q := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hjD : (i.val - 1) / K < D := by omega
    have htK : K - 1 - (i.val - 1) % K < K := by omega
    have hi : i.val = 1 + (⟨(i.val - 1) / K, hjD⟩ : Fin D).val * K +
        (K - 1 - (⟨K - 1 - (i.val - 1) % K, htK⟩ : Fin K).val) := by
      have h2' := Nat.div_add_mod' (i.val - 1) K
      have h3 := Nat.mod_lt (i.val - 1) hK
      show i.val = 1 + (i.val - 1) / K * K + (K - 1 - (K - 1 - (i.val - 1) % K))
      omega
    rw [encodeAddr_val_chunk u _ _ i hi, encodeAddr_val_chunk u' _ _ i hi,
      h2 ⟨(i.val - 1) / K, hjD⟩ hjq]
  rw [mergeAddr_val_zero hR hq (encodeAddr u) ⟨0, by simp [layerLayout]⟩ rfl,
    mergeAddr_val_zero hR hq (encodeAddr u') ⟨0, by simp [layerLayout]⟩ rfl,
    encodeAddr_val_zero u ⟨0, by simp [layerLayout]⟩ rfl,
    encodeAddr_val_zero u' ⟨0, by simp [layerLayout]⟩ rfl, h1, hb]

/-- `mergeAddr` is injective when `2^{qK} ≤ R`. -/
theorem mergeAddr_injective {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D) (hRq : 2 ^ (q * K) ≤ R)
    {x y : (layerLayout A K D S).Addr}
    (h : mergeAddr A K D S q R hR hq x = mergeAddr A K D S q R hR hq y) : x = y := by
  have hqK : q * K ≤ D * K := Nat.mul_le_mul_right _ hq
  have hsub : (D - q) * K = D * K - q * K := Nat.sub_mul D q K
  have hn : 1 + q * K ≤ (layerLayout A K D S).n := by simp only [layerLayout]; omega
  have hrange : (layerLayout A K D S).blockRange 1 (1 + q * K) = 2 ^ (q * K) :=
    blockRange_chunks (q * K) hqK
  have hbx : (layerLayout A K D S).blockVal 1 (1 + q * K) x < R :=
    lt_of_lt_of_le (hrange ▸ blockVal_lt_blockRange 1 (1 + q * K) hn x) hRq
  have hby : (layerLayout A K D S).blockVal 1 (1 + q * K) y < R :=
    lt_of_lt_of_le (hrange ▸ blockVal_lt_blockRange 1 (1 + q * K) hn y) hRq
  have e0 : (mergeAddr A K D S q R hR hq x ⟨0, by simp [layerLayout]⟩).val =
      (mergeAddr A K D S q R hR hq y ⟨0, by simp [layerLayout]⟩).val := by rw [h]
  rw [mergeAddr_val_zero hR hq x ⟨0, by simp [layerLayout]⟩ rfl,
    mergeAddr_val_zero hR hq y ⟨0, by simp [layerLayout]⟩ rfl,
    Nat.mod_eq_of_lt hbx, Nat.mod_eq_of_lt hby] at e0
  obtain ⟨hx0, hbv⟩ := mul_add_lt_inj hbx hby e0
  funext i
  apply Fin.ext
  have hi := i.isLt
  simp only [layerLayout] at hi
  by_cases hi0 : i.val = 0
  · rw [← addr_val_eq x (a := 0) (by simp [layerLayout]) i hi0.symm,
      ← addr_val_eq y (a := 0) (by simp [layerLayout]) i hi0.symm]
    exact hx0
  · by_cases hi1 : i.val ≤ q * K
    · rw [eq_of_blockVal_eq 1 (1 + q * K) hn x y hbv i (by omega) (by omega)]
    · by_cases hi2 : i.val ≤ D * K
      · have hlt' : i.val - q * K < (layerLayout (A * R) K (D - q) S).n := by
          simp only [layerLayout]; omega
        have hlt'' : i.val - q * K + q * K < (layerLayout A K D S).n := by
          simp only [layerLayout]; omega
        have e : (mergeAddr A K D S q R hR hq x ⟨i.val - q * K, hlt'⟩).val =
            (mergeAddr A K D S q R hR hq y ⟨i.val - q * K, hlt'⟩).val := by rw [h]
        rw [mergeAddr_val_mid hR hq x ⟨i.val - q * K, hlt'⟩ (show i.val - q * K ≠ 0 by omega)
            (show i.val - q * K ≤ (D - q) * K by omega) hlt'',
          mergeAddr_val_mid hR hq y ⟨i.val - q * K, hlt'⟩ (show i.val - q * K ≠ 0 by omega)
            (show i.val - q * K ≤ (D - q) * K by omega) hlt'',
          addr_val_eq x hlt'' i (by omega), addr_val_eq y hlt'' i (by omega)] at e
        exact e
      · have hlt' : (D - q) * K + 1 < (layerLayout (A * R) K (D - q) S).n := by
          simp only [layerLayout]; omega
        have e : (mergeAddr A K D S q R hR hq x ⟨(D - q) * K + 1, hlt'⟩).val =
            (mergeAddr A K D S q R hR hq y ⟨(D - q) * K + 1, hlt'⟩).val := by rw [h]
        rw [mergeAddr_val_last hR hq x ⟨(D - q) * K + 1, hlt'⟩
            (show (D - q) * K + 1 ≠ 0 by omega) (show ¬ (D - q) * K + 1 ≤ (D - q) * K by omega),
          mergeAddr_val_last hR hq y ⟨(D - q) * K + 1, hlt'⟩
            (show (D - q) * K + 1 ≠ 0 by omega) (show ¬ (D - q) * K + 1 ≤ (D - q) * K by omega),
          addr_val_eq x (a := D * K + 1) (by simp [layerLayout]) i (by omega),
          addr_val_eq y (a := D * K + 1) (by simp [layerLayout]) i (by omega)] at e
        exact e

/-- (E5) Padded rows are never read: at a merged address the embedded array is the original
record (needs `2^{qK} ≤ R`, so that `mergeAddr` is injective). -/
theorem embedArr_mergeL {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D) (hRq : 2 ^ (q * K) ≤ R)
    {rr : ℕ} (w : RArr (LayerAddr A K D S) rr) (u : LayerAddr A K D S) :
    embedArr hR hq (encodeArr w) (encodeAddr (mergeL hR hq u)) = w u := by
  rw [encodeAddr_mergeL]
  have hex : ∃ x, mergeAddr A K D S q R hR hq x = mergeAddr A K D S q R hR hq (encodeAddr u) :=
    ⟨encodeAddr u, rfl⟩
  have heq := mergeAddr_injective hR hq hRq (Classical.choose_spec hex)
  simp only [embedArr, dif_pos hex, heq, encodeArr, decodeAddr_encodeAddr]

end SubNLogN.Math.Networks.LayerSpecPadAux
