import SubNLogN.Math.Networks.LayoutEncoding2
import SubNLogN.Math.Networks.LayerCore

/-!
# Layout encoding: canonical address codec of the layer layout

`layerLayout A K D S` (`LayerCore.lean`): field `0` the prefix `[A]`, then `D` chunks of `K` binary
fields (bit `t` of chunk `j` at field `1 + jK + (K−1−t)`, most significant bit first), then the
suffix `[S]` (field `DK + 1`). With the lexicographic rank `lexEquiv` of `LayoutEncoding.lean`
(field `0` most significant):
* `layer_card : (layerLayout A K D S).card = A * 2^(K*D) * S`;
* `layer_rank`: the rank of `encodeAddr x` is `(x.a · 2^{KD} + Σ_{j<D} v_j 2^{K(D−1−j)}) · S + x.s`
  with `v_j = Σ_{t<K} 2^t [bit t of chunk j]` (`chunkVal`), i.e. prefix order, chunk order,
  MSB-first bits, suffix order.
The two address inverses are `encodeAddr_decodeAddr` / `decodeAddr_encodeAddr`
(`Proofs/LayerSpecPad.lean`).

Class view: for a complete class `c` (`μ ∣ r_row`), `RowClass.classRankEquiv` is the semantic
factorization `{x // c.mem x} ≃ Fin (r_row / μ) × (other fields)`, and `RowClass.mem_iff_roleEmbed`
identifies the members with the role embeddings of `LayoutEncoding2.lean` (`W = μ`, `k = res`); the
explicit lexicographic order of the class (original field order, row field of range `r_row / μ`) is
then `Layout.lexEquiv_roleEmbed` (index level) and `Layout.roleBlocks_enc` (list level).
Helpers are in `SubNLogN.Math.Networks.Model.LayoutEncodingAux` (prefix `lay_`).
-/

namespace SubNLogN.Math.Networks.Model

open SubNLogN.Math.Walsh LayoutEncodingAux

namespace LayoutEncodingAux

theorem lay_blockVal_field {L : Layout} (p : ℕ) (hp : p < L.n) (x : L.Addr) :
    L.blockVal p (p + 1) x = (x ⟨p, hp⟩).val := blockVal_single ⟨p, hp⟩ x

theorem lay_blockRange_field {L : Layout} (p : ℕ) (hp : p < L.n) :
    L.blockRange p (p + 1) = L.r ⟨p, hp⟩ := blockRange_single ⟨p, hp⟩

variable {A K D S : ℕ}

theorem lay_n : (layerLayout A K D S).n = D * K + 2 := rfl

theorem lay_r_bit {p : ℕ} (h1 : 1 ≤ p) (h2 : p ≤ D * K) (hp : p < (layerLayout A K D S).n) :
    (layerLayout A K D S).r ⟨p, hp⟩ = 2 := by
  show (if p = 0 then A else if p ≤ D * K then 2 else S) = 2
  rw [if_neg (by omega), if_pos h2]

/-- A block of bit fields has range `2^(length)`. -/
theorem lay_blockRange_bits : ∀ (d a : ℕ), 1 ≤ a → a + d ≤ D * K + 1 →
    (layerLayout A K D S).blockRange a (a + d) = 2 ^ d := by
  intro d
  induction d with
  | zero =>
    intro a _ _
    rw [Nat.add_zero, blockRange_of_le (le_refl _), pow_zero]
  | succ d ih =>
    intro a ha had
    rw [show a + (d + 1) = a + d + 1 by ring,
      blockRange_split (Nat.le_add_right a d) (Nat.le_succ (a + d)), ih a ha (by omega),
      lay_blockRange_field (a + d) (by rw [lay_n]; omega),
      lay_r_bit (by omega) (by omega), pow_succ]

end LayoutEncodingAux

variable {A K D S : ℕ}

/-- **Layer cardinality**: `card = A · 2^{KD} · S`. -/
theorem layer_card (A K D S : ℕ) : (layerLayout A K D S).card = A * 2 ^ (K * D) * S := by
  have h0 : (layerLayout A K D S).blockRange 0 1 = A := by
    show (layerLayout A K D S).blockRange 0 (0 + 1) = A
    rw [lay_blockRange_field 0 (by rw [lay_n]; omega)]
    rfl
  have hbits : (layerLayout A K D S).blockRange 1 (D * K + 1) = 2 ^ (D * K) := by
    rw [show D * K + 1 = 1 + D * K by ring]
    exact lay_blockRange_bits (D * K) 1 (le_refl _) (by omega)
  have hS : (layerLayout A K D S).blockRange (D * K + 1) (D * K + 2) = S := by
    show (layerLayout A K D S).blockRange (D * K + 1) (D * K + 1 + 1) = S
    rw [lay_blockRange_field (D * K + 1) (by rw [lay_n]; omega)]
    show (if D * K + 1 = 0 then A else if D * K + 1 ≤ D * K then 2 else S) = S
    rw [if_neg (by omega), if_neg (by omega)]
  rw [← Layout.blockRange_zero_n, lay_n,
    blockRange_split (Nat.zero_le 1) (by omega : 1 ≤ D * K + 2),
    blockRange_split (by omega : 1 ≤ D * K + 1) (by omega : D * K + 1 ≤ D * K + 2), h0, hbits, hS,
    mul_comm K D, mul_assoc]

/-! ### The exact rank of an encoded layer address -/

/-- Bit `t` of chunk `j` of a layer address as `0/1` (`0` out of range). -/
def layerBit (x : LayerAddr A K D S) (j t : ℕ) : ℕ :=
  if h : j < D ∧ t < K then (if x.2.1 ⟨j, h.1⟩ ⟨t, h.2⟩ then 1 else 0) else 0

/-- The value `v_j = Σ_{t<K} 2^t [bit t of chunk j]` of chunk `j`. -/
def chunkVal (x : LayerAddr A K D S) (j : ℕ) : ℕ :=
  ∑ t ∈ Finset.range K, 2 ^ t * layerBit x j t

namespace LayoutEncodingAux

theorem lay_encode_bit (x : LayerAddr A K D S) {j u : ℕ} (hj : j < D) (hu : u < K)
    (hp : 1 + j * K + u < (layerLayout A K D S).n) :
    (encodeAddr x ⟨1 + j * K + u, hp⟩).val = layerBit x j (K - 1 - u) := by
  have hK : 0 < K := by omega
  have hle : 1 + j * K + u ≤ D * K := by
    have h := Nat.mul_le_mul_right K (show j + 1 ≤ D from hj)
    rw [add_one_mul] at h
    omega
  have e1 : (1 + j * K + u - 1) / K = j := by
    rw [show 1 + j * K + u - 1 = u + j * K by omega, Nat.add_mul_div_right _ _ hK,
      Nat.div_eq_of_lt hu, zero_add]
  have e2 : (1 + j * K + u - 1) % K = u := by
    rw [show 1 + j * K + u - 1 = u + j * K by omega, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  have hfj : ∀ p, (⟨(1 + j * K + u - 1) / K, p⟩ : Fin D) = ⟨j, hj⟩ := fun _ => Fin.ext e1
  have hft : ∀ p, (⟨K - 1 - (1 + j * K + u - 1) % K, p⟩ : Fin K) = ⟨K - 1 - u, by omega⟩ :=
    fun _ => Fin.ext (by simp only [e2])
  simp only [encodeAddr, dif_neg (show 1 + j * K + u ≠ 0 by omega), dif_pos hle, dif_pos hK, hfj,
    hft, layerBit, dif_pos (show j < D ∧ K - 1 - u < K from ⟨hj, by omega⟩)]

/-- The value of the first `u'` bit fields of chunk `j`. -/
theorem lay_blockVal_chunk_aux (x : LayerAddr A K D S) {j : ℕ} (hj : j < D) :
    ∀ u', u' ≤ K → (layerLayout A K D S).blockVal (1 + j * K) (1 + j * K + u') (encodeAddr x) =
      ∑ u ∈ Finset.range u', layerBit x j (K - 1 - u) * 2 ^ (u' - 1 - u) := by
  intro u'
  induction u' with
  | zero =>
    intro _
    rw [Nat.add_zero, blockVal_of_le (le_refl _), Finset.sum_range_zero]
  | succ u' ih =>
    intro hu'
    have hle : 1 + j * K + u' + 1 ≤ D * K + 1 := by
      have h := Nat.mul_le_mul_right K (show j + 1 ≤ D from hj)
      rw [add_one_mul] at h
      omega
    have hp : 1 + j * K + u' < (layerLayout A K D S).n := by rw [lay_n]; omega
    rw [show 1 + j * K + (u' + 1) = 1 + j * K + u' + 1 by ring,
      blockVal_split (Nat.le_add_right _ u') (Nat.le_succ _), ih (by omega),
      lay_blockRange_field _ hp, lay_r_bit (by omega) (by omega), lay_blockVal_field _ hp,
      lay_encode_bit x hj (by omega), Finset.sum_range_succ, show u' + 1 - 1 - u' = 0 by omega,
      pow_zero, mul_one, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_range] at hu
    rw [mul_assoc, ← pow_succ, show u' + 1 - 1 - u = u' - 1 - u + 1 by omega]

/-- The value of chunk `j` is `v_j`. -/
theorem lay_blockVal_chunk (x : LayerAddr A K D S) {j : ℕ} (hj : j < D) :
    (layerLayout A K D S).blockVal (1 + j * K) (1 + j * K + K) (encodeAddr x) = chunkVal x j := by
  rw [lay_blockVal_chunk_aux x hj K (le_refl _), chunkVal,
    ← Finset.sum_range_reflect (fun t => 2 ^ t * layerBit x j t) K]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [mul_comm]

/-- The value of the first `d` chunks. -/
theorem lay_blockVal_chunks (x : LayerAddr A K D S) :
    ∀ d, d ≤ D → (layerLayout A K D S).blockVal 1 (1 + d * K) (encodeAddr x) =
      ∑ j ∈ Finset.range d, chunkVal x j * 2 ^ (K * (d - 1 - j)) := by
  intro d
  induction d with
  | zero =>
    intro _
    rw [Nat.zero_mul, Nat.add_zero, blockVal_of_le (le_refl _), Finset.sum_range_zero]
  | succ d ih =>
    intro hd
    have hle : 1 + d * K + K ≤ D * K + 1 := by
      have h := Nat.mul_le_mul_right K hd
      rw [add_one_mul] at h
      omega
    rw [show 1 + (d + 1) * K = 1 + d * K + K by ring,
      blockVal_split (Nat.le_add_right 1 (d * K)) (Nat.le_add_right _ K), ih (by omega),
      lay_blockRange_bits K (1 + d * K) (Nat.le_add_right _ _) hle,
      lay_blockVal_chunk x (by omega), Finset.sum_range_succ, show d + 1 - 1 - d = 0 by omega,
      Nat.mul_zero, pow_zero, mul_one, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [mul_assoc, ← pow_add, show K * (d - 1 - j) + K = K * (d + 1 - 1 - j) by
      rw [show d + 1 - 1 - j = d - 1 - j + 1 by omega, Nat.mul_succ]]

end LayoutEncodingAux

/-- **Exact layer rank**: prefix order, chunk order, MSB-first bits, suffix order. -/
theorem layer_rank (x : LayerAddr A K D S) :
    ((layerLayout A K D S).lexEquiv (encodeAddr x)).val =
      (x.1.val * 2 ^ (K * D) + ∑ j ∈ Finset.range D, chunkVal x j * 2 ^ (K * (D - 1 - j))) * S +
        x.2.2.val := by
  have h0 : (layerLayout A K D S).blockVal 0 1 (encodeAddr x) = x.1.val := by
    show (layerLayout A K D S).blockVal 0 (0 + 1) (encodeAddr x) = x.1.val
    rw [lay_blockVal_field 0 (by rw [lay_n]; omega)]
    simp [encodeAddr]
  have hS : (layerLayout A K D S).blockRange (D * K + 1) (D * K + 2) = S := by
    show (layerLayout A K D S).blockRange (D * K + 1) (D * K + 1 + 1) = S
    rw [lay_blockRange_field (D * K + 1) (by rw [lay_n]; omega)]
    show (if D * K + 1 = 0 then A else if D * K + 1 ≤ D * K then 2 else S) = S
    rw [if_neg (by omega), if_neg (by omega)]
  have hs : (layerLayout A K D S).blockVal (D * K + 1) (D * K + 2) (encodeAddr x) = x.2.2.val := by
    show (layerLayout A K D S).blockVal (D * K + 1) (D * K + 1 + 1) (encodeAddr x) = x.2.2.val
    rw [lay_blockVal_field (D * K + 1) (by rw [lay_n]; omega)]
    simp only [encodeAddr, dif_neg (show D * K + 1 ≠ 0 by omega),
      dif_neg (show ¬ D * K + 1 ≤ D * K by omega)]
  have hbits : (layerLayout A K D S).blockRange 1 (D * K + 1) = 2 ^ (D * K) := by
    rw [show D * K + 1 = 1 + D * K by ring]
    exact lay_blockRange_bits (D * K) 1 (le_refl _) (by omega)
  have hchunks : (layerLayout A K D S).blockVal 1 (D * K + 1) (encodeAddr x) =
      ∑ j ∈ Finset.range D, chunkVal x j * 2 ^ (K * (D - 1 - j)) := by
    rw [show D * K + 1 = 1 + D * K by ring]
    exact lay_blockVal_chunks x D (le_refl _)
  rw [Layout.lexEquiv_val, lay_n,
    blockVal_split (Nat.zero_le 1) (by omega : 1 ≤ D * K + 2),
    blockVal_split (by omega : 1 ≤ D * K + 1) (by omega : D * K + 1 ≤ D * K + 2),
    blockRange_split (by omega : 1 ≤ D * K + 1) (by omega : D * K + 1 ≤ D * K + 2),
    h0, hS, hs, hbits, hchunks, mul_comm K D]
  ring

/-! ### Class view -/

namespace LayoutEncodingAux

theorem lay_class_lt {L : Layout} (c : RowClass L) (hdiv : c.μ ∣ L.r c.row)
    (k : Fin (L.r c.row / c.μ)) : c.res + c.μ * k.val < L.r c.row := by
  obtain ⟨N, hN⟩ := hdiv
  have hN' : L.r c.row / c.μ = N := by rw [hN, Nat.mul_div_cancel_left _ c.hμ]
  have hk : k.val < N := lt_of_lt_of_eq k.isLt hN'
  have hres := c.hres
  calc c.res + c.μ * k.val < c.μ + c.μ * k.val := by omega
    _ = c.μ * (k.val + 1) := by ring
    _ ≤ c.μ * N := Nat.mul_le_mul_left _ hk
    _ = L.r c.row := hN.symm

end LayoutEncodingAux

/-- **Class rank equivalence**: for a complete class (`μ ∣ r_row`), a member is determined by
its row index `(x_row − res) / μ` and its other fields. -/
def RowClass.classRankEquiv {L : Layout} (c : RowClass L) (hdiv : c.μ ∣ L.r c.row) :
    {x : L.Addr // c.mem x} ≃
      Fin (L.r c.row / c.μ) × ((i : {i : Fin L.n // i ≠ c.row}) → Fin (L.r i.1)) where
  toFun x := (⟨(x.1 c.row).val / c.μ, Nat.div_lt_div_of_lt_of_dvd hdiv (x.1 c.row).isLt⟩,
    fun i => x.1 i.1)
  invFun p := ⟨fun i => if h : i = c.row then
      ⟨c.res + c.μ * p.1.val, by subst h; exact lay_class_lt c hdiv p.1⟩ else p.2 ⟨i, h⟩, by
    simp only [RowClass.mem]
    rw [dif_pos trivial]
    show (c.res + c.μ * p.1.val) % c.μ = c.res
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.hres]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    dsimp only
    by_cases h : i = c.row
    · subst h
      rw [dif_pos rfl]
      apply Fin.ext
      show c.res + c.μ * ((x.1 c.row).val / c.μ) = (x.1 c.row).val
      have hm : (x.1 c.row).val % c.μ = c.res := x.2
      rw [← hm]
      exact Nat.mod_add_div _ _
    · rw [dif_neg h]
  right_inv p := by
    obtain ⟨k, f⟩ := p
    refine Prod.ext ?_ ?_
    · apply Fin.ext
      dsimp only
      rw [dif_pos rfl]
      show (c.res + c.μ * k.val) / c.μ = k.val
      rw [Nat.add_mul_div_left _ _ c.hμ, Nat.div_eq_of_lt c.hres, zero_add]
    · funext i
      dsimp only
      rw [dif_neg i.2]

theorem RowClass.classRankEquiv_fst {L : Layout} (c : RowClass L) (hdiv : c.μ ∣ L.r c.row)
    (x : {x : L.Addr // c.mem x}) :
    ((c.classRankEquiv hdiv x).1).val = (x.1 c.row).val / c.μ := rfl

theorem RowClass.classRankEquiv_snd {L : Layout} (c : RowClass L) (hdiv : c.μ ∣ L.r c.row)
    (x : {x : L.Addr // c.mem x}) (i : {i : Fin L.n // i ≠ c.row}) :
    (c.classRankEquiv hdiv x).2 i = x.1 i.1 := rfl

/-- The class members are exactly the role embeddings (`LayoutEncoding2.lean`, `W = μ`, `k = res`);
their lexicographic order is that of the role layout (`Layout.lexEquiv_roleEmbed`,
`Layout.roleBlocks_enc`). -/
theorem RowClass.mem_iff_roleEmbed {L : Layout} (c : RowClass L) (hdiv : c.μ ∣ L.r c.row)
    (x : L.Addr) :
    c.mem x ↔ ∃ x' : (L.roleLayout c.row c.μ).Addr,
      L.roleEmbed c.row c.μ hdiv ⟨c.res, c.hres⟩ x' = x := by
  constructor
  · intro hx
    have hlt : ∀ i : Fin L.n, i = c.row → (x i).val / c.μ < (L.roleLayout c.row c.μ).r i := by
      intro i hi
      subst hi
      rw [L.roleLayout_r_self]
      exact Nat.div_lt_div_of_lt_of_dvd hdiv (x c.row).isLt
    have hlt' : ∀ i : Fin L.n, i ≠ c.row → (x i).val < (L.roleLayout c.row c.μ).r i := by
      intro i hi
      rw [L.roleLayout_r_of_ne c.μ hi]
      exact (x i).isLt
    refine ⟨fun i => if h : i = c.row then ⟨(x i).val / c.μ, hlt i h⟩ else ⟨(x i).val, hlt' i h⟩,
      ?_⟩
    funext i
    apply Fin.ext
    by_cases h : i = c.row
    · subst h
      rw [L.roleEmbed_apply_self, dif_pos rfl]
      show (x c.row).val / c.μ * c.μ + c.res = (x c.row).val
      have hm : (x c.row).val % c.μ = c.res := hx
      rw [← hm, Nat.mul_comm]
      exact Nat.div_add_mod _ _
    · rw [L.roleEmbed_apply_of_ne hdiv _ _ h, dif_neg h]
  · rintro ⟨x', rfl⟩
    exact (L.mem_roleEmbed c hdiv ⟨c.res, c.hres⟩ x').2 rfl

end SubNLogN.Math.Networks.Model
