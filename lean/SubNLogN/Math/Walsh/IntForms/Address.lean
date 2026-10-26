import SubNLogN.Math.Walsh.DirectFFT
import SubNLogN.Math.Walsh.Proofs.LayoutPerm

/-!
# Integer forms for the direct-FFT machine, address level

Exact `ℕ`-valued forms of the address computations made by the direct-FFT machine kernels
(`SubNLogN/Machine/Contracts/FFT.lean`), with equality lemmas to the value-level definitions
(`SubNLogN/Math/Walsh/{Layout,DirectFFT,PhaseTable}.lean`). Paper: Sections 6.2–6.3 (`sec:direct-fft-layout`–`sec:direct-fft-twiddle`).
Only `Math` is imported (no `Machine` module); the arithmetic integer forms (grid numerators,
DIF level, round protocol) are in `SubNLogN/Math/Walsh/IntForms.lean`.

1. Record index ↔ cube address: `cubeOfNat m i` (same body as `SubNLogN.Machine.cubeOfNat`:
   records are stored in increasing index order and position `0` of an address is its most
   significant bit), `addrBit`, `natOfCube`, with the round trips.
2. Positional maps on record indices: `permSrcIdx π i`, with
   `posPermArr π z (cubeOfNat m i) = z (cubeOfNat m (permSrcIdx π i))`.
3. Phase-table indices: the DIF stage index `difTabIdx ℓ s k = 2^{s+1} j` and the twiddle index
   `2 J(x)`, both `< 2r` (`r = 2^ℓ`).
4. Slot positions in layout `L` in closed form (`newPosNat`, `newPosNat_eq`): the long-axis rank
   for `v = ℓ-1`, `n_long + (b₀-1-v)D + i` for `v < b₀`, and `n_P + jDK + iK + t` for chunk slots;
   `n_P = n_long + b₀ D` (`prefixLen_eq_nat`); the positions of round `v` as a list and as a bit
   mask on record indices (`roundSetList`, `mem_roundSet_iff`, `roundSetMask`,
   `testBit_roundSetMask`).
5. The twiddle index of a record as a function of its record index (`twJNat`).
6. The positional maps `L`, `B`, `U` as explicit position lists `[π 0, …, π (m₀-1)]`
   (`layoutLList`, `bitRevBList`, `layoutUList`).
-/

namespace SubNLogN.Math.Walsh.IntForms

open SubNLogN.Math.Common
open SubNLogN.Math.Walsh.LayoutPermAux

/-! ## 1. Record index ↔ cube address -/

/-- The cube address with record index `i`: bit `p` (position `0` most significant) is bit
`m-1-p` of `i`. Same body as `SubNLogN.Machine.cubeOfNat`. -/
def cubeOfNat (m i : ℕ) : Cube m := fun p => i.testBit (m - 1 - (p : ℕ))

/-- Bit `p` of the `m`-bit record index `i` (position `0` most significant); `false` for
`p ≥ m`. -/
def addrBit (m i p : ℕ) : Bool := decide (p < m) && i.testBit (m - 1 - p)

theorem cubeBit_cubeOfNat (m i p : ℕ) : cubeBit (cubeOfNat m i) p = addrBit m i p := by
  unfold cubeBit addrBit cubeOfNat
  by_cases h : p < m
  · simp [h]
  · simp [h]

/-- The record index `∑_p x_p 2^{m-1-p}` of a cube address. -/
def natOfCube {m : ℕ} (x : Cube m) : ℕ := bitsValMSB m (fun p => cubeBit x p)

theorem natOfCube_lt {m : ℕ} (x : Cube m) : natOfCube x < 2 ^ m := bitsValMSB_lt _ _

theorem cubeOfNat_natOfCube {m : ℕ} (x : Cube m) : cubeOfNat m (natOfCube x) = x := by
  funext p
  have hp := p.isLt
  show (natOfCube x).testBit (m - 1 - (p : ℕ)) = x p
  unfold natOfCube
  rw [testBit_bitsValMSB, if_pos (by omega)]
  have e : m - 1 - (m - 1 - (p : ℕ)) = p := by omega
  rw [e]
  unfold cubeBit
  rw [dif_pos hp]

theorem natOfCube_cubeOfNat {m i : ℕ} (hi : i < 2 ^ m) : natOfCube (cubeOfNat m i) = i := by
  apply Nat.eq_of_testBit_eq
  intro t
  unfold natOfCube
  rw [testBit_bitsValMSB]
  by_cases ht : t < m
  · rw [if_pos ht, cubeBit_cubeOfNat]
    unfold addrBit
    rw [show m - 1 - (m - 1 - t) = t by omega]
    simp [show m - 1 - t < m by omega]
  · rw [if_neg ht]
    exact (Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

/-! ## 2. Positional maps on record indices -/

/-- For a positional map `π` (move convention of `posPermArr`), the output record with index
`i` is the input record with index `permSrcIdx π i`: its bit `p` is bit `π p` of `i`. -/
def permSrcIdx {m : ℕ} (π : Fin m → Fin m) (i : ℕ) : ℕ :=
  bitsValMSB m (fun p => if h : p < m then i.testBit (m - 1 - (π ⟨p, h⟩ : ℕ)) else false)

theorem permSrcIdx_lt {m : ℕ} (π : Fin m → Fin m) (i : ℕ) : permSrcIdx π i < 2 ^ m :=
  bitsValMSB_lt _ _

theorem cubeOfNat_permSrcIdx {m : ℕ} (π : Fin m → Fin m) (i : ℕ) :
    cubeOfNat m (permSrcIdx π i) = fun p => cubeOfNat m i (π p) := by
  funext p
  have hp := p.isLt
  show (permSrcIdx π i).testBit (m - 1 - (p : ℕ)) = i.testBit (m - 1 - (π p : ℕ))
  unfold permSrcIdx
  rw [testBit_bitsValMSB, if_pos (by omega)]
  have e : m - 1 - (m - 1 - (p : ℕ)) = p := by omega
  simp [e, hp]

/-- `posPermArr π` read at record indices. -/
theorem posPermArr_cubeOfNat {m r : ℕ} (π : Fin m → Fin m) (z : RArr (Cube m) r) (i : ℕ) :
    posPermArr π z (cubeOfNat m i) = z (cubeOfNat m (permSrcIdx π i)) := by
  rw [cubeOfNat_permSrcIdx]
  rfl

/-! ## 3. Phase-table indices -/

/-- The DIF stage-table index `2^{s+1} j` read by the lower output at coefficient `k` of level `s`
(`j = (k mod 2^{ℓ-s}) - 2^{ℓ-s-1}`; `θ_{2^{s+1} j} = e^{2πi j/2^{ℓ-s}}`). -/
def difTabIdx (ℓ s k : ℕ) : ℕ := 2 ^ (s + 1) * (k % 2 ^ (ℓ - s) - 2 ^ (ℓ - s - 1))

/-- `difLevel` reads the table at `difTabIdx` (definitional). -/
theorem difLevel_eq_difTabIdx (P ℓ s : ℕ) (θt : ℕ → ℂ) (w : Fin (2 ^ ℓ) → ℂ)
    (k : Fin (2 ^ ℓ)) :
    difLevel P ℓ s θt w k =
      if (k : ℕ) % 2 ^ (ℓ - s) < 2 ^ (ℓ - s - 1) then
        truncC P ((getCoeff w k + getCoeff w ((k : ℕ) + 2 ^ (ℓ - s - 1))) / 2)
      else
        truncC P (θt (difTabIdx ℓ s k) *
          truncC P ((getCoeff w ((k : ℕ) - 2 ^ (ℓ - s - 1)) - getCoeff w k) / 2)) :=
  rfl

/-- The stage index is a valid table index: `2^{s+1} j < 2^ℓ < 2r` for `s < ℓ`. -/
theorem difTabIdx_lt {ℓ s : ℕ} (hs : s < ℓ) (k : ℕ) : difTabIdx ℓ s k < 2 ^ ℓ := by
  unfold difTabIdx
  have h1 : k % 2 ^ (ℓ - s) < 2 ^ (ℓ - s) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : 2 ^ (ℓ - s) = 2 * 2 ^ (ℓ - s - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h3 : k % 2 ^ (ℓ - s) - 2 ^ (ℓ - s - 1) < 2 ^ (ℓ - s - 1) := by omega
  calc 2 ^ (s + 1) * (k % 2 ^ (ℓ - s) - 2 ^ (ℓ - s - 1)) < 2 ^ (s + 1) * 2 ^ (ℓ - s - 1) :=
        (Nat.mul_lt_mul_left (Nat.two_pow_pos _)).2 h3
    _ = 2 ^ ℓ := by rw [← pow_add]; congr 1; omega

/-- The combined twiddle index is `< r`, so `2 J(x) < 2r` is a valid table index. -/
theorem twJ_lt {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) (x : Cube (addrBits a)) :
    twJ ℓ K a v x < 2 ^ ℓ := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem two_mul_twJ_lt {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) (x : Cube (addrBits a)) :
    2 * twJ ℓ K a v x < 2 * 2 ^ ℓ := by
  have := twJ_lt ℓ K a v x
  omega

/-! ## 4. Slot positions in layout `L` in closed form -/

section ListFacts

/-- `idxOf` in a filtered list counts the earlier entries that pass the filter. -/
theorem idxOf_filter_eq {α : Type*} [BEq α] [LawfulBEq α] (p : α → Bool) (l : List α) (x : α)
    (hx : x ∈ l) (hp : p x = true) :
    (l.filter p).idxOf x = ((l.take (l.idxOf x)).filter p).length := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    by_cases hxy : y = x
    · subst hxy
      simp [hp]
    · have hx' : x ∈ l := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hxy
        · exact h
      have hb : (y == x) = false := by simpa using hxy
      rw [List.idxOf_cons, hb, cond_false, List.take_succ_cons, List.filter_cons,
        List.filter_cons]
      by_cases hpy : p y = true
      · rw [if_pos hpy, if_pos hpy, List.idxOf_cons, hb, cond_false, ih hx', List.length_cons]
      · rw [if_neg hpy, if_neg hpy, ih hx']

/-- `idxOf` commutes with an injective `map`. -/
theorem idxOf_map_inj {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β}
    (hf : Function.Injective f) (l : List α) (x : α) : (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => simp
  | cons y l ih =>
    by_cases h : y = x
    · subst h; simp
    · have hb : (y == x) = false := by simpa using h
      have hb' : (f y == f x) = false := by simpa using fun e => h (hf e)
      rw [List.map_cons, List.idxOf_cons, hb', cond_false, List.idxOf_cons, hb, cond_false, ih]

end ListFacts

variable {D : ℕ}

/-- `#{i' < i : a_{i'} = ℓ}`, the number of long axes before axis `i` (count of `ℓ` among the
first `i` header exponents). -/
def longRank (ℓ : ℕ) (a : Fin D → ℕ) (i : ℕ) : ℕ := ((List.ofFn a).take i).count ℓ

/-- `n_long = #{i : a_i = ℓ}`. -/
def longCount (ℓ : ℕ) (a : Fin D → ℕ) : ℕ := (List.ofFn a).count ℓ

/-- Position of the slot `(i, v)` (`v < a_i`) in layout `L` (its index in `𝒫 ‖ 𝒞`,
Section 6.2 (`sec:direct-fft-layout`)), in closed form: the long-axis rank for `v = ℓ-1`;
`n_long + (b₀-1-v)D + i` for `v < b₀`; otherwise `n_P + jDK + iK + t` with `ℓ-2-v = jK + t`,
`t < K`, `n_P = n_long + b₀ D`. -/
def newPosNat (ℓ K : ℕ) (a : Fin D → ℕ) (i : Fin D) (v : ℕ) : ℕ :=
  if v = ℓ - 1 then longRank ℓ a i
  else if v < layoutB0 ℓ K then longCount ℓ a + (layoutB0 ℓ K - 1 - v) * D + i
  else longCount ℓ a + layoutB0 ℓ K * D + (ℓ - 2 - v) / K * D * K + (i : ℕ) * K +
    (ℓ - 2 - v) % K

/-- The filtered count over `finRange` is the count of `ℓ` in the header list. -/
theorem length_filter_take_finRange (ℓ : ℕ) (a : Fin D → ℕ) (n : ℕ) :
    (((List.finRange D).take n).filter (fun i' => decide (a i' = ℓ))).length =
      ((List.ofFn a).take n).count ℓ := by
  rw [List.ofFn_eq_map, ← List.map_take, List.count, List.countP_map,
    List.countP_eq_length_filter]
  congr 2

theorem nLong_eq_longCount (ℓ : ℕ) (a : Fin D → ℕ) : nLong ℓ a = longCount ℓ a := by
  have h := length_filter_take_finRange ℓ a D
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)] at h
  exact h

/-- `n_P = n_long + b₀ D` in closed form (the prefix length of layout `L`). -/
theorem prefixLen_eq_nat (ℓ K : ℕ) (a : Fin D → ℕ) :
    prefixLen ℓ K a = longCount ℓ a + layoutB0 ℓ K * D := by
  rw [prefixLen_eq, nLong_eq_longCount]

/-- The long slot `(i, ℓ-1)` (`a_i = ℓ`) sits at the long-axis rank of `i`. -/
theorem newPos_long (ℓ K : ℕ) (a : Fin D → ℕ) (i : Fin D) (hi : a i = ℓ) :
    newPos ℓ K a (i, ℓ - 1) = longRank ℓ a i := by
  have hmemL : (i, ℓ - 1) ∈
      ((List.finRange D).filter (fun i' => decide (a i' = ℓ))).map (fun i' => (i', ℓ - 1)) :=
    List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_finRange i, by simpa using hi⟩, rfl⟩
  have hmemP : (i, ℓ - 1) ∈ prefixSlots ℓ K a := by
    rw [prefixSlots_eq]; exact List.mem_append_left _ hmemL
  have hinj : Function.Injective (fun i' : Fin D => (i', ℓ - 1)) := fun x y h => (Prod.mk.inj h).1
  rw [newPos, newSlots, List.idxOf_append_of_mem hmemP, prefixSlots_eq,
    List.idxOf_append_of_mem hmemL, idxOf_map_inj hinj,
    idxOf_filter_eq _ _ _ (List.mem_finRange i) (by simpa using hi), List.idxOf_finRange,
    length_filter_take_finRange]
  rfl

/-- The short prefix slot `(i, v)`, `v < b₀`, sits at `n_long + (b₀-1-v)D + i`. -/
theorem newPos_short (ℓ K : ℕ) (a : Fin D → ℕ) (i : Fin D) (v : ℕ) (hv : v < layoutB0 ℓ K) :
    newPos ℓ K a (i, v) = longCount ℓ a + (layoutB0 ℓ K - 1 - v) * D + i := by
  have hb₀ℓ : layoutB0 ℓ K ≤ ℓ - 1 := Nat.mod_le _ _
  have hvℓ : v ≠ ℓ - 1 := by omega
  have hnotL : (i, v) ∉
      ((List.finRange D).filter (fun i' => decide (a i' = ℓ))).map (fun i' => (i', ℓ - 1)) := by
    intro h
    obtain ⟨i', _, h'⟩ := List.mem_map.1 h
    exact hvℓ (Prod.mk.inj h').2.symm
  have hj : layoutB0 ℓ K - 1 - v < ((List.range (layoutB0 ℓ K)).reverse).length := by
    simp only [List.length_reverse, List.length_range]; omega
  have hLk : ∀ (k : ℕ) (hk : k < ((List.range (layoutB0 ℓ K)).reverse).length),
      ((List.range (layoutB0 ℓ K)).reverse)[k] = layoutB0 ℓ K - 1 - k := by
    intro k hk
    simp only [List.length_reverse, List.length_range] at hk
    rw [List.getElem_reverse, List.getElem_range]
    simp only [List.length_range]
  have hLj : ((List.range (layoutB0 ℓ K)).reverse)[layoutB0 ℓ K - 1 - v] = v := by
    rw [hLk _ hj]; omega
  have hmemS : (i, v) ∈ prefixBlock D ((List.range (layoutB0 ℓ K)).reverse)[layoutB0 ℓ K - 1 - v] := by
    rw [hLj]; exact List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩
  have hnot : ∀ (k : ℕ) (hk : k < layoutB0 ℓ K - 1 - v),
      (i, v) ∉ prefixBlock D (((List.range (layoutB0 ℓ K)).reverse)[k]'(Nat.lt_trans hk hj)) := by
    intro k hk h
    obtain ⟨i', _, h'⟩ := List.mem_map.1 h
    have h2 := (Prod.mk.inj h').2
    rw [hLk k (Nat.lt_trans hk hj)] at h2
    omega
  have hmemS' : (i, v) ∈ ((List.range (layoutB0 ℓ K)).reverse).flatMap (prefixBlock D) :=
    List.mem_flatMap.2 ⟨_, List.getElem_mem hj, hmemS⟩
  have hmemP : (i, v) ∈ prefixSlots ℓ K a := by
    rw [prefixSlots_eq]; exact List.mem_append_right _ hmemS'
  have hinj : Function.Injective (fun i' : Fin D => (i', v)) := fun x y h => (Prod.mk.inj h).1
  have hblk : (prefixBlock D v).idxOf (i, v) = i := by
    unfold prefixBlock
    rw [idxOf_map_inj hinj, List.idxOf_finRange]
  rw [newPos, newSlots, List.idxOf_append_of_mem hmemP, prefixSlots_eq,
    List.idxOf_append_of_notMem hnotL,
    idxOf_flatMap _ (prefixBlock D) _ hj _ hmemS hnot,
    sum_map_const _ _ D (fun x _ => by simp [prefixBlock]), List.length_take, hLj, hblk,
    List.length_map]
  have hmin : min (layoutB0 ℓ K - 1 - v) ((List.range (layoutB0 ℓ K)).reverse).length =
      layoutB0 ℓ K - 1 - v := min_eq_left hj.le
  rw [hmin]
  have hn := nLong_eq_longCount ℓ a
  unfold nLong at hn
  rw [hn]
  ring

/-- A chunk slot `(i, v)`, `b₀ ≤ v ≤ ℓ-2`, sits at `n_P + jDK + iK + t`, `ℓ-2-v = jK + t`. -/
theorem newPos_chunkNat (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (i : Fin D) (v : ℕ)
    (hv0 : layoutB0 ℓ K ≤ v) (hv1 : v + 2 ≤ ℓ) :
    newPos ℓ K a (i, v) = longCount ℓ a + layoutB0 ℓ K * D + (ℓ - 2 - v) / K * D * K +
      (i : ℕ) * K + (ℓ - 2 - v) % K := by
  have hJ := jblk_mul_add_b0 ℓ K hK
  have hjt : (ℓ - 2 - v) / K * K + (ℓ - 2 - v) % K = ℓ - 2 - v := Nat.div_add_mod' _ _
  have hjJ : (ℓ - 2 - v) / K < layoutJblk ℓ K := by
    rw [Nat.div_lt_iff_lt_mul hK]; omega
  have htK : (ℓ - 2 - v) % K < K := Nat.mod_lt _ hK
  have hv : ℓ - 2 - (ℓ - 2 - v) / K * K - (ℓ - 2 - v) % K = v := by omega
  have h := newPos_chunk ℓ K a hK _ _ hjJ htK i
  rw [hv] at h
  rw [h, prefixLen_eq, nLong_eq_longCount]
  ring

/-- **Closed-form slot positions**: under the shape hypotheses of Theorem 6.5 (`1 ≤ K`, `ℓ ≥ 2`,
`a_i ∈ {ℓ-1, ℓ}`), `newPosNat` is the position `newPos` of every valid slot `(i, v)`, `v < a_i`. -/
theorem newPosNat_eq (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ)
    (i : Fin D) (v : ℕ) (hv : v < a i) :
    newPosNat ℓ K a i v = newPos ℓ K a (i, v) := by
  have hai := ha i
  unfold newPosNat
  by_cases h1 : v = ℓ - 1
  · rw [if_pos h1, h1, newPos_long ℓ K a i (by omega)]
  · rw [if_neg h1]
    by_cases h2 : v < layoutB0 ℓ K
    · rw [if_pos h2, newPos_short ℓ K a i v h2]
    · rw [if_neg h2, newPos_chunkNat ℓ K a hK i v (by omega) (by omega)]

/-- The positions of round `v` (`roundSet`) as an explicit list: the closed-form positions of
the slots `(i, v)` of the participating axes `a_i > v`, axes increasing. -/
def roundSetList (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) : List ℕ :=
  ((List.finRange D).filter (fun i => decide (v < a i))).map (fun i => newPosNat ℓ K a i v)

theorem mem_roundSet_iff (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (v : ℕ) (p : Fin (addrBits a)) :
    p ∈ roundSet ℓ K a v ↔ (p : ℕ) ∈ roundSetList ℓ K a v := by
  unfold roundSet roundSetList
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_map, List.mem_filter,
    List.mem_finRange, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hv, hp⟩
    exact ⟨i, hv, by rw [newPosNat_eq ℓ K a hK ha i v hv, hp]⟩
  · rintro ⟨i, hv, hp⟩
    exact ⟨i, hv, by rw [← newPosNat_eq ℓ K a hK ha i v hv, hp]⟩

/-- `roundSet` as a bit mask on record indices: bit `m₀-1-p` (the bit of position `p`) is set iff
position `p` takes part in round `v`. -/
def roundSetMask (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) : ℕ :=
  bitsValMSB (addrBits a) (fun p => decide (p ∈ roundSetList ℓ K a v))

theorem testBit_roundSetMask (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (v : ℕ) (p : Fin (addrBits a)) :
    (roundSetMask ℓ K a v).testBit (addrBits a - 1 - p) = true ↔ p ∈ roundSet ℓ K a v := by
  have hp := p.isLt
  unfold roundSetMask
  rw [testBit_bitsValMSB, if_pos (by omega),
    show addrBits a - 1 - (addrBits a - 1 - (p : ℕ)) = p by omega, decide_eq_true_eq,
    mem_roundSet_iff ℓ K a hK ha v p]

/-! ## 5. The twiddle index of a record -/

/-- The combined twiddle index of round `v` for the record with index `n`
(Section 6.3 (`sec:direct-fft-twiddle`), eq. (`eq:combined-round`), layout `L`): `J = ∑_{i : a_i > v} 2^{ℓ-v-1} b_i j_i^{<v} mod 2^ℓ`,
with `b_i` the bit of `n` at the position of slot `(i, v)` and `j_i^{<v} = ∑_{b<v} 2^b x_{(i,b)}`,
all positions in closed form (`newPosNat`). -/
def twJNat (ℓ K : ℕ) (a : Fin D → ℕ) (v n : ℕ) : ℕ :=
  (∑ i : Fin D, if v < a i ∧ addrBit (addrBits a) n (newPosNat ℓ K a i v) = true then
      2 ^ (ℓ - v - 1) * ∑ b ∈ Finset.range v,
        (if addrBit (addrBits a) n (newPosNat ℓ K a i b) = true then 2 ^ b else 0)
    else 0) % 2 ^ ℓ

theorem twJNat_lt (ℓ K : ℕ) (a : Fin D → ℕ) (v n : ℕ) : twJNat ℓ K a v n < 2 ^ ℓ :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- **Twiddle index**: `twJNat` is the value-level twiddle index `twJ` of the record with index
`n` (the phase of the diagonal `D̃(x) = θ̃_{2J(x)}` of `roundsProg` / `exactRound`). -/
theorem twJNat_eq (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ)
    (v n : ℕ) : twJNat ℓ K a v n = twJ ℓ K a v (cubeOfNat (addrBits a) n) := by
  unfold twJNat twJ
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hv : v < a i
  · have hc : addrBit (addrBits a) n (newPosNat ℓ K a i v) =
        cubeBit (cubeOfNat (addrBits a) n) (newPos ℓ K a (i, v)) := by
      rw [newPosNat_eq ℓ K a hK ha i v hv, cubeBit_cubeOfNat]
    have hs : (∑ b ∈ Finset.range v,
        (if addrBit (addrBits a) n (newPosNat ℓ K a i b) = true then 2 ^ b else 0)) =
        ∑ b ∈ Finset.range v,
          (if cubeBit (cubeOfNat (addrBits a) n) (newPos ℓ K a (i, b)) = true then 2 ^ b
            else 0) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [newPosNat_eq ℓ K a hK ha i b (lt_trans (Finset.mem_range.1 hb) hv),
        cubeBit_cubeOfNat]
    rw [hc, hs]
  · simp [hv]

/-- The twiddle diagonal of round `v` read at record indices. -/
theorem twiddle_cubeOfNat (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (θt : ℕ → ℂ) (v n : ℕ) :
    θt (2 * twJ ℓ K a v (cubeOfNat (addrBits a) n)) = θt (2 * twJNat ℓ K a v n) := by
  rw [twJNat_eq ℓ K a hK ha]

/-! ## 6. The positional maps `L`, `B`, `U` as explicit position lists -/

/-- `𝒫 ‖ 𝒞` is a permutation of `𝒪` (same valid slots, same length, `𝒪` duplicate-free). -/
theorem perm_origSlots_newSlots (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) : (origSlots a).Perm (newSlots ℓ K a) := by
  have hsub : (origSlots a).Subperm (newSlots ℓ K a) :=
    (nodup_origSlots a).subperm fun s hs =>
      mem_newSlots ℓ K a hK hℓ ha s ((mem_origSlots a s).1 hs)
  exact hsub.perm_of_length_le (by rw [length_newSlots ℓ K a hK (by omega) ha, length_origSlots])

theorem nodup_newSlots (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) : (newSlots ℓ K a).Nodup :=
  (perm_origSlots_newSlots ℓ K a hK hℓ ha).nodup_iff.1 (nodup_origSlots a)

theorem mem_newSlots_iff (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (s : Fin D × ℕ) : s ∈ newSlots ℓ K a ↔ s.2 < a s.1 :=
  (perm_origSlots_newSlots ℓ K a hK hℓ ha).mem_iff.symm.trans (mem_origSlots a s)

/-- The entry of `𝒪` at the position `origPos a i w` of slot `(i, w)` is `(i, w)`. -/
theorem origSlots_getElem_of_eq (a : Fin D → ℕ) (i : Fin D) (w : ℕ) (hw : w < a i) (k : ℕ)
    (hk : k < (origSlots a).length) (hkw : k = origPos a i w) : (origSlots a)[k] = (i, w) := by
  have key : ∀ (k' : ℕ) (hk' : k' < (origSlots a).length), k' = (origSlots a).idxOf (i, w) →
      (origSlots a)[k'] = (i, w) := by
    intro k' hk' e
    subst e
    exact List.getElem_idxOf hk'
  exact key k hk (hkw.trans (idxOf_origSlots a i w hw).symm)

/-- `B` in closed form: the slot `(i, v)` at position `p` of `𝒪` moves to `axisOffset a i + v`. -/
theorem bitRevB_val_eq (a : Fin D → ℕ) (p : Fin (addrBits a))
    (hp : (p : ℕ) < (origSlots a).length) :
    ((bitRevB a p : Fin (addrBits a)) : ℕ) =
      axisOffset a ((origSlots a)[(p : ℕ)]'hp).1 + ((origSlots a)[(p : ℕ)]'hp).2 := by
  rw [bitRevB_val a p hp]
  have hs := (mem_origSlots a _).1 (List.getElem_mem hp)
  unfold origPos
  omega

/-- Runtime data of `L` (`permSyms` order): `[L 0, …, L (m₀-1)]`, generated slot by slot in the
order of `𝒪` (axes increasing, bits `a_i - 1, …, 0`), each by the closed form `newPosNat`. -/
def layoutLList (ℓ K : ℕ) (a : Fin D → ℕ) : List ℕ :=
  (origSlots a).map (fun s => newPosNat ℓ K a s.1 s.2)

/-- Runtime data of `B`: slot `(i, v)` of `𝒪` moves to `axisOffset a i + v`. -/
def bitRevBList (a : Fin D → ℕ) : List ℕ :=
  (origSlots a).map (fun s => axisOffset a s.1 + s.2)

/-- Runtime data of `U = (L ∘ B)^{-1}`: the slot `(i, v)` at position `q` of `𝒫 ‖ 𝒞` gives
`U q = axisOffset a i + v`. -/
def layoutUList (ℓ K : ℕ) (a : Fin D → ℕ) : List ℕ :=
  (newSlots ℓ K a).map (fun s => axisOffset a s.1 + s.2)

theorem ofFn_layoutL (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) :
    List.ofFn (fun p => (layoutL ℓ K a p : ℕ)) = layoutLList ℓ K a := by
  apply List.ext_getElem
  · simp [layoutLList, length_origSlots]
  · intro p h1 h2
    have hp : p < (origSlots a).length := by simpa [layoutLList] using h2
    rw [List.getElem_ofFn]
    simp only [layoutLList, List.getElem_map]
    rw [layoutL_val ℓ K a hK hℓ ha ⟨p, by simpa using h1⟩ hp]
    exact (newPosNat_eq ℓ K a hK ha _ _ ((mem_origSlots a _).1 (List.getElem_mem hp))).symm

theorem ofFn_bitRevB (a : Fin D → ℕ) :
    List.ofFn (fun p => (bitRevB a p : ℕ)) = bitRevBList a := by
  apply List.ext_getElem
  · simp [bitRevBList, length_origSlots]
  · intro p h1 h2
    have hp : p < (origSlots a).length := by simpa [bitRevBList] using h2
    rw [List.getElem_ofFn]
    simp only [bitRevBList, List.getElem_map]
    exact bitRevB_val_eq a ⟨p, by simpa using h1⟩ hp

theorem ofFn_layoutU (ℓ K : ℕ) (a : Fin D → ℕ) (hK : 0 < K) (hℓ : 2 ≤ ℓ)
    (ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) :
    List.ofFn (fun q => (layoutU ℓ K a q : ℕ)) = layoutUList ℓ K a := by
  have hlenN := length_newSlots ℓ K a hK (by omega) ha
  have hlenO := length_origSlots a
  have hLB : Function.Bijective (fun p => layoutL ℓ K a (bitRevB a p)) :=
    Finite.injective_iff_bijective.1
      ((layoutL_injective ℓ K a hK hℓ ha).comp (bitRevB_injective a))
  apply List.ext_getElem
  · simp [layoutUList, hlenN]
  · intro q h1 h2
    have hq : q < (newSlots ℓ K a).length := by simpa [layoutUList] using h2
    rw [List.getElem_ofFn]
    simp only [layoutUList, List.getElem_map]
    set s := (newSlots ℓ K a)[q] with hs_def
    have hsv : s.2 < a s.1 :=
      (mem_newSlots_iff ℓ K a hK hℓ ha s).1 (List.getElem_mem hq)
    -- the source position `p₀ = axisOffset a i + v = origPos a i (a i - 1 - v)`
    have hp0e : axisOffset a s.1 + s.2 = origPos a s.1 (a s.1 - 1 - s.2) := by
      unfold origPos; omega
    have hp0 : axisOffset a s.1 + s.2 < addrBits a := by
      rw [hp0e]; exact origPos_lt a _ _ (by omega)
    set p₀ : Fin (addrBits a) := ⟨axisOffset a s.1 + s.2, hp0⟩ with hp₀_def
    -- `B p₀` is the position of `s` in `𝒪`
    have hB : ((bitRevB a p₀ : Fin (addrBits a)) : ℕ) = origPos a s.1 s.2 := by
      have hp0' : (p₀ : ℕ) < (origSlots a).length := by rw [hlenO]; exact hp0
      rw [bitRevB_val a p₀ hp0']
      have hget : (origSlots a)[(p₀ : ℕ)]'hp0' = (s.1, a s.1 - 1 - s.2) :=
        origSlots_getElem_of_eq a s.1 (a s.1 - 1 - s.2) (by omega) _ hp0' hp0e
      rw [hget]
      dsimp only
      congr 1
      omega
    -- `L (B p₀) = q`
    have hLBq : layoutL ℓ K a (bitRevB a p₀) = ⟨q, by simpa using h1⟩ := by
      apply Fin.ext
      have hBl : ((bitRevB a p₀ : Fin (addrBits a)) : ℕ) < (origSlots a).length := by
        rw [hlenO]; exact (bitRevB a p₀).isLt
      rw [layoutL_val ℓ K a hK hℓ ha _ hBl]
      have hget : (origSlots a)[((bitRevB a p₀ : Fin (addrBits a)) : ℕ)]'hBl = s :=
        origSlots_getElem_of_eq a s.1 s.2 hsv _ hBl hB
      rw [hget]
      show (newSlots ℓ K a).idxOf s = q
      rw [hs_def]
      exact (nodup_newSlots ℓ K a hK hℓ ha).idxOf_getElem q hq
    -- `U q = p₀`
    have hU : layoutU ℓ K a ⟨q, by simpa using h1⟩ = p₀ := by
      unfold layoutU
      rw [← hLBq]
      exact invFunFin_left_inv _ hLB p₀
    rw [hU]

end SubNLogN.Math.Walsh.IntForms
