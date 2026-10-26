import SubNLogN.Math.Networks.AppCCore

/-!
# Lemma A.10 (`lem:transfer-phase`) edge operations, part 1: bit-level semantics of the packed row addition on layer addresses

Used in the edge proof of `CCoreProcCorrectStmt` (`AppCCore.lean`). The Lemma A.9 (`lem:transfer13`) packed addition
`packedAddProc` acts (by `PackedProcCorrectStmt`) through the pull `addrXorAll`, which reads and
writes whole chunks of `L = fK` binary fields as binary numbers (`blockVal` / `blockSet`, `Nat.xor`).
Here we compute it bit by bit on encoded layer addresses:

* `blockVal_single`, `place_eq_pow`, `blockVal_bin`: a block of binary fields is the binary number
  whose bit `i` is field `p + L − 1 − i`;
* `testBit_sum_pow`: bits of a sum of distinct powers of two;
* `AddrXorAllEncodeStmt` (`addrXorAll_encode_holds` in `CCoreEdgeBits2.lean`): for the slots of a Lemma A.10 (`lem:transfer-phase`) node (`slotPos t = 1 + (j0 + t f) K`), the packed
  addition of slot `j` into slot `i` is `encodeAddr ∘ rowAddL … i j`, i.e. bit `ρ` of chunk
  `j0 + i f + q` is XORed with bit `ρ` of chunk `j0 + j f + q` (`q < f`), nothing else changes;
* `slotBit_encode`: the selected bit read by `zSlot`.

Everything is in the namespace `SubNLogN.Math.Networks.CCoreEdgeAux`.
-/

namespace SubNLogN.Math.Networks

namespace CCoreEdgeAux

open Model SubNLogN.Math.Walsh

/-! ## 1. Binary blocks of a layout -/

/-- Value of field `m` of `a` (`0` if out of range). -/
def fv {Ly : Layout} (a : Ly.Addr) (m : ℕ) : ℕ := if h : m < Ly.n then (a ⟨m, h⟩).val else 0

theorem fv_of_lt {Ly : Layout} (a : Ly.Addr) {m : ℕ} (h : m < Ly.n) : fv a m = (a ⟨m, h⟩).val :=
  dif_pos h

/-- A single-field block holds the value of that field. -/
theorem blockVal_single {Ly : Layout} (s : ℕ) (a : Ly.Addr) : Ly.blockVal s (s + 1) a = fv a s := by
  unfold Layout.blockVal
  by_cases hs : s < Ly.n
  · rw [fv_of_lt a hs]
    have hfilt : Finset.univ.filter (inBlock s (s + 1) (n := Ly.n)) = {⟨s, hs⟩} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock, Finset.mem_singleton]
      constructor
      · intro h
        exact Fin.ext (show j.val = s by omega)
      · rintro rfl
        simp
    rw [hfilt, Finset.sum_singleton]
    have hp : Ly.place (s + 1) ⟨s, hs⟩ = 1 := by
      unfold Layout.place
      apply Finset.prod_eq_one
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨h1, h2⟩ := hj
      have h3 : s < j.val := h1
      omega
    rw [hp, mul_one]
  · rw [fv, dif_neg hs]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
    exact absurd j.isLt (by omega)

/-- Place values in a block of binary fields are powers of two. -/
theorem place_eq_pow {Ly : Layout} {q : ℕ} (hq : q ≤ Ly.n) (j : Fin Ly.n)
    (hbin : ∀ j' : Fin Ly.n, j.val < j'.val → j'.val < q → Ly.r j' = 2) :
    Ly.place q j = 2 ^ (q - 1 - j.val) := by
  unfold Layout.place
  rw [Finset.prod_congr rfl (g := fun _ => 2) (fun j' hj' => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hj'
    exact hbin j' hj'.1 hj'.2)]
  rw [Finset.prod_const]
  congr 1
  rw [← Finset.card_map Fin.valEmbedding]
  have hmap : (Finset.univ.filter (fun j' : Fin Ly.n => j < j' ∧ j'.val < q)).map Fin.valEmbedding =
      Finset.Ioo j.val q := by
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ioo, Fin.lt_def]
    constructor
    · rintro ⟨j', ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨m, by omega⟩, ⟨h1, h2⟩, rfl⟩
  rw [hmap, Nat.card_Ioo]
  omega

/-- A block `[p, p + L)` of binary fields holds the binary number whose bit `i` is field
`p + L − 1 − i`. -/
theorem blockVal_bin {Ly : Layout} {p L : ℕ} (hq : p + L ≤ Ly.n)
    (hbin : ∀ j : Fin Ly.n, p ≤ j.val → j.val < p + L → Ly.r j = 2) (a : Ly.Addr) :
    Ly.blockVal p (p + L) a = ∑ i ∈ Finset.range L, fv a (p + L - 1 - i) * 2 ^ i := by
  unfold Layout.blockVal
  have h1 : ∀ j ∈ Finset.univ.filter (inBlock p (p + L) (n := Ly.n)),
      (a j).val * Ly.place (p + L) j = fv a j.val * 2 ^ (p + L - 1 - j.val) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
    rw [place_eq_pow hq j (fun j' h1 h2 => hbin j' (by omega) h2), fv_of_lt a j.isLt]
  rw [Finset.sum_congr rfl h1]
  have h2 := Finset.sum_map (Finset.univ.filter (inBlock p (p + L) (n := Ly.n))) Fin.valEmbedding
    (fun m => fv a m * 2 ^ (p + L - 1 - m))
  simp only [Fin.valEmbedding_apply] at h2
  rw [← h2]
  have hmap : (Finset.univ.filter (inBlock p (p + L) (n := Ly.n))).map Fin.valEmbedding =
      Finset.Ico p (p + L) := by
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, inBlock,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨m, by omega⟩, ⟨h1, h2⟩, rfl⟩
  rw [hmap, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  refine Finset.sum_nbij' (fun k => L - 1 - k) (fun i => L - 1 - i) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    congr 2 <;> omega

/-- Overwriting a block of binary fields: field `j` receives bit `q − 1 − j` of the value. -/
theorem blockSet_bin_val {Ly : Layout} {p q : ℕ} (hq : q ≤ Ly.n)
    (hbin : ∀ j : Fin Ly.n, p ≤ j.val → j.val < q → Ly.r j = 2) (a : Ly.Addr) (v : ℕ)
    (j : Fin Ly.n) (hj1 : p ≤ j.val) (hj2 : j.val < q) :
    (Ly.blockSet p q a v j).val = if v.testBit (q - 1 - j.val) then 1 else 0 := by
  have hin : inBlock p q j := ⟨hj1, hj2⟩
  simp only [Layout.blockSet, if_pos hin]
  rw [place_eq_pow hq j (fun j' h1 h2 => hbin j' (by omega) h2), hbin j hj1 hj2,
    Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ (q - 1 - j.val)) with h | h <;> simp [h]

theorem blockSet_apply_of_not {Ly : Layout} {t₀ t₁ : ℕ} (x : Ly.Addr) (v : ℕ) (j : Fin Ly.n)
    (hj : ¬ (t₀ ≤ j.val ∧ j.val < t₁)) : Ly.blockSet t₀ t₁ x v j = x j := by
  simp only [Layout.blockSet]
  rw [if_neg (show ¬ inBlock t₀ t₁ j from hj)]

/-! ## 2. Bits of sums of distinct powers of two -/

theorem sum_pow_lt (pos : ℕ → ℕ) (hpos : StrictMono pos) (g : ℕ → Bool) (n : ℕ) :
    (∑ i ∈ Finset.range n, if g i = true then 2 ^ pos i else 0) < 2 ^ pos n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : pos n + 1 ≤ pos (n + 1) := hpos (Nat.lt_succ_self n)
    have h2 : 2 ^ (pos n + 1) ≤ 2 ^ pos (n + 1) := Nat.pow_le_pow_right (by norm_num) h1
    have h3 : (if g n = true then 2 ^ pos n else 0) ≤ 2 ^ pos n := by split_ifs <;> simp
    rw [pow_succ] at h2
    calc (∑ i ∈ Finset.range n, if g i = true then 2 ^ pos i else 0) +
          (if g n = true then 2 ^ pos n else 0) < 2 ^ pos n + 2 ^ pos n :=
          Nat.add_lt_add_of_lt_of_le ih h3
      _ = 2 ^ pos n * 2 := by ring
      _ ≤ 2 ^ pos (n + 1) := h2

/-- The bits of `Σ_{i<n} [g i] 2^{pos i}` for strictly increasing positions. -/
theorem testBit_sum_pow (pos : ℕ → ℕ) (hpos : StrictMono pos) (g : ℕ → Bool) (n b : ℕ) :
    (∑ i ∈ Finset.range n, if g i = true then 2 ^ pos i else 0).testBit b = true ↔
      ∃ i < n, pos i = b ∧ g i = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hlt := sum_pow_lt pos hpos g n
    by_cases hg : g n = true
    · rw [if_pos hg, add_comm]
      rcases lt_trichotomy b (pos n) with hb | hb | hb
      · rw [Nat.testBit_two_pow_add_gt hb, ih]
        constructor
        · rintro ⟨i, hi, h⟩
          exact ⟨i, by omega, h⟩
        · rintro ⟨i, hi, hpi, hgi⟩
          refine ⟨i, ?_, hpi, hgi⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact h
          · subst h
            omega
      · subst hb
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        simp only [Bool.not_false, true_iff]
        exact ⟨n, by omega, rfl, hg⟩
      · have hbig : 2 ^ pos n + (∑ i ∈ Finset.range n, if g i = true then 2 ^ pos i else 0) <
            2 ^ b := by
          have h5 : 2 ^ (pos n + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
          rw [pow_succ] at h5
          calc 2 ^ pos n + (∑ i ∈ Finset.range n, if g i = true then 2 ^ pos i else 0)
              < 2 ^ pos n + 2 ^ pos n := Nat.add_lt_add_left hlt _
            _ = 2 ^ pos n * 2 := by ring
            _ ≤ 2 ^ b := h5
        rw [Nat.testBit_lt_two_pow hbig]
        simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
        intro i hi hpi
        have : pos i ≤ pos n := hpos.monotone (by omega)
        omega
    · rw [if_neg hg, add_zero, ih]
      constructor
      · rintro ⟨i, hi, h⟩
        exact ⟨i, by omega, h⟩
      · rintro ⟨i, hi, hpi, hgi⟩
        refine ⟨i, ?_, hpi, hgi⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact h
        · subst h
          exact absurd hgi hg

/-- Binary field values are `0` or `1`. -/
theorem fv_bin {Ly : Layout} (a : Ly.Addr) {m : ℕ} (hm : m < Ly.n) (hr : Ly.r ⟨m, hm⟩ = 2) :
    fv a m = 0 ∨ fv a m = 1 := by
  rw [fv_of_lt a hm]
  have h2 : (a ⟨m, hm⟩).val < 2 := lt_of_lt_of_eq (a ⟨m, hm⟩).isLt hr
  omega

/-- The bits of a block of binary fields. -/
theorem testBit_blockVal_bin {Ly : Layout} {p L : ℕ} (hq : p + L ≤ Ly.n)
    (hbin : ∀ j : Fin Ly.n, p ≤ j.val → j.val < p + L → Ly.r j = 2) (a : Ly.Addr) (b : ℕ) :
    (Ly.blockVal p (p + L) a).testBit b = true ↔ b < L ∧ fv a (p + L - 1 - b) = 1 := by
  rw [blockVal_bin hq hbin a]
  have hfv : ∀ i ∈ Finset.range L, fv a (p + L - 1 - i) * 2 ^ i =
      if decide (fv a (p + L - 1 - i) = 1) = true then 2 ^ i else 0 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have hm : p + L - 1 - i < Ly.n := by omega
    rcases fv_bin a hm (hbin ⟨p + L - 1 - i, hm⟩ (by show p ≤ p + L - 1 - i; omega)
      (by show p + L - 1 - i < p + L; omega)) with h | h <;> simp [h]
  rw [Finset.sum_congr rfl hfv, testBit_sum_pow (fun i => i) strictMono_id
    (fun i => decide (fv a (p + L - 1 - i) = 1)) L b]
  constructor
  · rintro ⟨i, hi, rfl, h⟩
    exact ⟨hi, by simpa using h⟩
  · rintro ⟨hb, h⟩
    exact ⟨b, hb, rfl, by simpa using h⟩

theorem chunkBit_eq {Ly : Layout} (L p j : ℕ) (hj : j < p + L) (a : Ly.Addr) :
    chunkBit L p j a = fv a (p + L - 1 - j) := by
  unfold chunkBit
  rw [show p + L - j = (p + L - 1 - j) + 1 by omega, blockVal_single]

/-- The bits of the packed control word `Σ_{i<f} 2^{ρ+iK} x_{ρ+iK}`. -/
theorem testBit_ctrl {Ly : Layout} {K ρ f px : ℕ} (hρ : ρ < K)
    (hq : px + f * K ≤ Ly.n)
    (hbin : ∀ j : Fin Ly.n, px ≤ j.val → j.val < px + f * K → Ly.r j = 2) (a : Ly.Addr) (b : ℕ) :
    (∑ i ∈ Finset.range f, 2 ^ (ρ + i * K) * chunkBit (f * K) px (ρ + i * K) a).testBit b = true ↔
      ∃ i < f, ρ + i * K = b ∧ fv a (px + f * K - 1 - (ρ + i * K)) = 1 := by
  have hpos : StrictMono (fun i => ρ + i * K) := by
    intro i j hij
    have : i * K < j * K := Nat.mul_lt_mul_of_pos_right hij (by omega)
    show ρ + i * K < ρ + j * K
    omega
  have hterm : ∀ i ∈ Finset.range f, 2 ^ (ρ + i * K) * chunkBit (f * K) px (ρ + i * K) a =
      if decide (fv a (px + f * K - 1 - (ρ + i * K)) = 1) = true then 2 ^ (ρ + i * K) else 0 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have hiK : i * K + K ≤ f * K := by
      have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hi)
      rwa [Nat.succ_mul] at this
    have hpl : ρ + i * K < f * K := by omega
    rw [chunkBit_eq (f * K) px (ρ + i * K) (by omega) a]
    have hm : px + f * K - 1 - (ρ + i * K) < Ly.n := by omega
    rcases fv_bin a hm (hbin ⟨_, hm⟩ (by show px ≤ px + f * K - 1 - (ρ + i * K); omega)
      (by show px + f * K - 1 - (ρ + i * K) < px + f * K; omega)) with h | h <;> simp [h]
  rw [Finset.sum_congr rfl hterm, testBit_sum_pow (fun i => ρ + i * K) hpos
    (fun i => decide (fv a (px + f * K - 1 - (ρ + i * K)) = 1)) f b]
  simp only [decide_eq_true_eq]

/-- Bits of `addrXorAll` on its target chunk. -/
theorem addrXorAll_val {Ly : Layout} (L K ρ f : ℕ) (C : Chunks3) (hy : C.py + L ≤ Ly.n)
    (hybin : ∀ j : Fin Ly.n, C.py ≤ j.val → j.val < C.py + L → Ly.r j = 2)
    (a : Ly.Addr) (m : Fin Ly.n) (hm1 : C.py ≤ m.val) (hm2 : m.val < C.py + L) :
    (addrXorAll L K ρ f C a m).val =
      if ((chunkVal L C.py a).testBit (C.py + L - 1 - m.val) ^^
        (∑ i ∈ Finset.range f, 2 ^ (ρ + i * K) * chunkBit L C.px (ρ + i * K) a).testBit
          (C.py + L - 1 - m.val)) = true then 1 else 0 := by
  have hx : ∀ u v i : ℕ, (Nat.xor u v).testBit i = (u.testBit i ^^ v.testBit i) :=
    fun u v i => Nat.testBit_xor u v i
  unfold addrXorAll
  rw [blockSet_bin_val hy hybin _ _ m hm1 hm2, hx]

/-! ## 3. Encoded layer addresses -/

section Encode

variable {A K D S : ℕ}

/-- Field of bit `t` of chunk `j` (`1 + jK + (K−1−t)`) lies in the layout. -/
theorem bitField_lt (j : Fin D) (t : Fin K) :
    1 + j.val * K + (K - 1 - t.val) < (layerLayout A K D S).n := by
  have h1 : j.val * K + K ≤ D * K := by
    have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at this
    exact this
  have := t.isLt
  show 1 + j.val * K + (K - 1 - t.val) < D * K + 2
  omega

/-- The encoded value of bit `t` of chunk `j`. -/
theorem encode_bit (x : LayerAddr A K D S) (j : Fin D) (t : Fin K) :
    (encodeAddr x ⟨1 + j.val * K + (K - 1 - t.val), bitField_lt j t⟩).val =
      if x.2.1 j t then 1 else 0 := by
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) t.isLt
  have ht := t.isLt
  have h0 : 1 + j.val * K + (K - 1 - t.val) ≠ 0 := by omega
  have h1 : 1 + j.val * K + (K - 1 - t.val) ≤ D * K := by
    have : j.val * K + K ≤ D * K := by
      have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt j.isLt)
      rw [Nat.succ_mul] at this
      exact this
    omega
  have hsub : 1 + j.val * K + (K - 1 - t.val) - 1 = (K - 1 - t.val) + j.val * K := by omega
  have hdiv : (1 + j.val * K + (K - 1 - t.val) - 1) / K = j.val := by
    rw [hsub, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt (by omega), zero_add]
  have hmod : K - 1 - (1 + j.val * K + (K - 1 - t.val) - 1) % K = t.val := by
    rw [hsub, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  unfold encodeAddr
  simp only [Fin.val_mk, dif_neg h0, dif_pos h1, dif_pos hK]
  have hj : (⟨(1 + j.val * K + (K - 1 - t.val) - 1) / K, by rw [hdiv]; exact j.isLt⟩ : Fin D) = j :=
    Fin.ext hdiv
  have ht' : (⟨K - 1 - (1 + j.val * K + (K - 1 - t.val) - 1) % K, by omega⟩ : Fin K) = t :=
    Fin.ext hmod
  simp only [hj, ht']

/-- `fv` form of `encode_bit`. -/
theorem fv_encode_bit (x : LayerAddr A K D S) (ch t : ℕ) (hch : ch < D) (ht : t < K) :
    fv (encodeAddr x) (1 + ch * K + (K - 1 - t)) = if x.2.1 ⟨ch, hch⟩ ⟨t, ht⟩ then 1 else 0 := by
  rw [fv_of_lt _ (bitField_lt (A := A) (S := S) ⟨ch, hch⟩ ⟨t, ht⟩)]
  exact encode_bit x ⟨ch, hch⟩ ⟨t, ht⟩

theorem encode_zero (x : LayerAddr A K D S) (i : Fin (layerLayout A K D S).n) (hi : i.val = 0) :
    (encodeAddr x i).val = x.1.val := by
  unfold encodeAddr
  rw [dif_pos hi]

theorem encode_top (x : LayerAddr A K D S) (i : Fin (layerLayout A K D S).n) (h0 : i.val ≠ 0)
    (h1 : ¬ i.val ≤ D * K) : (encodeAddr x i).val = x.2.2.val := by
  unfold encodeAddr
  rw [dif_neg h0, dif_neg h1]

theorem layer_r_mid (i : Fin (layerLayout A K D S).n) (h0 : i.val ≠ 0) (h1 : i.val ≤ D * K) :
    (layerLayout A K D S).r i = 2 := by
  simp [layerLayout, h0, h1]

/-- The selected bit read by `zSlot` / `zMask`. -/
theorem slotBit_encode (ρ : Fin K) (f j0 t col : ℕ) (h : j0 + t * f + col < D)
    (x : LayerAddr A K D S) :
    slotBit (A := A) (D := D) (S := S) K ρ.val f j0 t col (encodeAddr x) =
      if x.2.1 ⟨j0 + t * f + col, h⟩ ρ then 1 else 0 := by
  unfold slotBit selField
  rw [blockVal_single]
  exact fv_encode_bit x _ _ h ρ.isLt

/-- Bit `t` of chunk `ch` of a layer address (`false` out of range). -/
def xbit (x : LayerAddr A K D S) (ch t : ℕ) : Bool :=
  if h : ch < D ∧ t < K then x.2.1 ⟨ch, h.1⟩ ⟨t, h.2⟩ else false

/-- The packed row addition of slot `j` into slot `i` on a layer address (slot `t` = chunks
`j0 + t f + q`, `q < f`): bit `ρ` of chunk `j0 + i f + q` is XORed with bit `ρ` of chunk
`j0 + j f + q`; nothing else changes. -/
def rowAddL (ρ : Fin K) (f j0 i j : ℕ) (x : LayerAddr A K D S) : LayerAddr A K D S :=
  (x.1, fun ch t => if t = ρ ∧ j0 + i * f ≤ ch.val ∧ ch.val < j0 + i * f + f then
      xor (x.2.1 ch t) (xbit x (ch.val - i * f + j * f) ρ.val) else x.2.1 ch t, x.2.2)

end Encode

/-- The packed addition of slot `j` into slot `i` of a Lemma A.10 (`lem:transfer-phase`) node (`slotPos t = 1 + (j0 + t f) K`,
`L = fK`), on encoded addresses, is `rowAddL`. (Proof: `addrXorAll_encode_holds`.) -/
def AddrXorAllEncodeStmt : Prop :=
  ∀ (A K D S : ℕ) (ρ : Fin K) (f j0 i j t3 : ℕ), 1 ≤ f → i < mH → j < mH → j0 + mH * f ≤ D →
    ∀ x : LayerAddr A K D S,
      addrXorAll (Ly := layerLayout A K D S) (f * K) K ρ.val f
        ⟨1 + (j0 + j * f) * K, 1 + (j0 + i * f) * K, 1 + (j0 + t3 * f) * K⟩ (encodeAddr x) =
      encodeAddr (rowAddL ρ f j0 i j x)

end CCoreEdgeAux

end SubNLogN.Math.Networks
