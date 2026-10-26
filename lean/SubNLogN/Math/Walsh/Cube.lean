import SubNLogN.Math.Walsh.LayerSpec

/-!
# Walsh: record arrays on a complete binary address cube

Paper: Sections 5.1–5.3 (`sec:walsh`), Definition 5.6 (`def:walsh-positional`).

* `Cube m = Fin m → Bool`: a complete `m`-bit record address; **position `0` is the most
  significant** (Section 5.1 (`sec:walsh-select`)).
* `hT T`: `H_0` applied on every position of `T` (the paper's `H_T`; `H_all = hT Sel`).
* `sPhase U`, `czSign pairs`: the recordwise diagonals `S_U` (Section 5.1, eq. (`eq:walsh-SU`)) and `CZ`
  (Section 5.2, eq. (`eq:walsh-CZ`)); `diagArr f`, `scaleArr c`: per-record diagonal and scalar.
* `cnotAddr`, `cnotArr`: `CNOT^{⊗s}` for disjoint pairs (control, target) (Lemma 5.4 (`lem:cnot`)).
* `posPermArr π`: the record operator induced by a positional map `π` with the *move*
  convention (the bit at position `j` is placed at position `π j`, Definition 5.6 (`def:walsh-positional`)).
  Positional maps are plain functions `Fin m → Fin m`; theorems assume bijectivity.
* Definition 5.6 (slices): `numChunks` (`J`), `numGroups` (`⌈J/d⌉`), `nSlice` (`N_slice`),
  `groupStart`, `groupSize`, `slicePos`.
* `cubeToAddr` / `addrToCube` / `sliceCall`: a layer call of Proposition A.11 on a slice of the
  cube, through the identification of `Cube (j0 + D K + nS)` with
  `[2^{j0}] × [2^K]^D × [2^{nS}]` (prefix and suffix read most significant bit first).
* Slice transport (proved): `selEmb` enumerates the slice positions (`slicePos_eq_map`,
  `card_slicePos`); `addrToCube_cubeToAddr` is the round trip; `layerH_cubeToAddr_eq_hT` identifies
  the layer `H` read through the slice with `H_{Sel}`; hence `sliceCall_eq`.
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

/-! ## The cube and Walsh operators -/

/-- A complete `m`-bit record address; position `0` is the most significant bit. -/
abbrev Cube (m : ℕ) : Type := Fin m → Bool

/-- `H_T`: the normalized butterfly `H_0 = (1/2)[[1,1],[1,-1]]` on every position of `T`, identity
elsewhere, identically on every coefficient of a record:
`(H_T z)(x) = 2^{-|T|} ∑_{y =_{T^c} x} (-1)^{#{j ∈ T | x_j = y_j = 1}} z(y)`. -/
noncomputable def hT {m r : ℕ} (T : Finset (Fin m)) (z : RArr (Cube m) r) : RArr (Cube m) r :=
  fun x k => ((2 : ℂ) ^ T.card)⁻¹ *
    ∑ y ∈ Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ T → y j = x j),
      (-1 : ℂ) ^ (T.filter (fun j => x j = true ∧ y j = true)).card * z y k

/-- A per-record diagonal: multiplies every coefficient of the record at `x` by `f x`. -/
def diagArr {α : Type} {r : ℕ} (f : α → ℂ) (z : RArr α r) : RArr α r :=
  fun x k => f x * z x k

/-- Multiplication of every coefficient by the scalar `c`. -/
def scaleArr {α : Type} {r : ℕ} (c : ℂ) (z : RArr α r) : RArr α r :=
  fun x k => c * z x k

/-- The phase of `S_U` (Section 5.1, eq. (`eq:walsh-SU`)): `i^{∑_{j ∈ U} x_j}`. -/
noncomputable def sPhase {m : ℕ} (U : Finset (Fin m)) (x : Cube m) : ℂ :=
  Complex.I ^ (U.filter (fun j => x j = true)).card

/-- The recordwise diagonal `S_U` (Section 5.1, eq. (`eq:walsh-SU`)). -/
noncomputable def sDiag {m r : ℕ} (U : Finset (Fin m)) (z : RArr (Cube m) r) : RArr (Cube m) r :=
  diagArr (sPhase U) z

/-- The sign of `CZ` (Section 5.2, eq. (`eq:walsh-CZ`)) for a list of pairs `(c_j, t_j)` (control, target):
`(-1)^{∑_j x_{c_j} x_{t_j}}`. -/
noncomputable def czSign {m : ℕ} (pairs : List (Fin m × Fin m)) (x : Cube m) : ℂ :=
  (-1 : ℂ) ^ (pairs.countP (fun p => x p.1 && x p.2))

/-- The set `T = {t_1, …, t_s}` of targets of a list of (control, target) pairs. -/
def targets {m : ℕ} (pairs : List (Fin m × Fin m)) : Finset (Fin m) :=
  (pairs.map Prod.snd).toFinset

/-- Validity of a batch of controlled flips (Section 5.2 (`sec:walsh-cnot`)): the `2s` positions
`c_1, t_1, …, c_s, t_s` are pairwise distinct. -/
def CnotPairsValid {m : ℕ} (pairs : List (Fin m × Fin m)) : Prop :=
  (pairs.map Prod.fst ++ pairs.map Prod.snd).Nodup

/-- The address map of `CNOT^{⊗s}`: `x_{t_j} ↦ x_{t_j} ⊕ x_{c_j}` for all `j` (for valid pairs
each position is the target of at most one pair). -/
def cnotAddr {m : ℕ} (pairs : List (Fin m × Fin m)) (x : Cube m) : Cube m :=
  fun p => xor (x p) (pairs.any (fun q => decide (q.2 = p) && x q.1))

/-- The array operator `CNOT^{⊗s}` (pull form): `(CNOT z)(y) = z(cnotAddr y)`. For valid pairs
`cnotAddr` is an involution, so this is the same as moving the record at `x` to `cnotAddr x`
(Lemma 5.4 (`lem:cnot`)). Coefficients are unchanged. -/
def cnotArr {m r : ℕ} (pairs : List (Fin m × Fin m)) (z : RArr (Cube m) r) : RArr (Cube m) r :=
  fun y k => z (cnotAddr pairs y) k

/-- The record operator induced by a positional map `π` with the move convention
(Definition 5.6 (`def:walsh-positional`)): the record at `x` moves to the address `y` with `y (π j) = x j`, i.e.
`(posPermArr π z)(y) = z(y ∘ π)`. Then `posPermArr (f ∘ g) = posPermArr f ∘ posPermArr g`
("`f ∘ g` applies `g` first"). -/
def posPermArr {m r : ℕ} (π : Fin m → Fin m) (z : RArr (Cube m) r) : RArr (Cube m) r :=
  fun y k => z (fun j => y (π j)) k

/-! ## Slices (Definition 5.6) -/

/-- `J = ⌊m₀/K⌋`, the number of complete `K`-bit chunks (Definition 5.6 (`def:walsh-positional`)). -/
def numChunks (m₀ K : ℕ) : ℕ := m₀ / K

/-- `⌈J/d⌉`, the number of groups of at most `d` consecutive chunks. -/
def numGroups (m₀ K d : ℕ) : ℕ := (numChunks m₀ K + d - 1) / d

/-- `N_slice = K ⌈J/d⌉` (Section 5.3, eq. (`eq:walsh-slices`)). -/
def nSlice (m₀ K d : ℕ) : ℕ := K * numGroups m₀ K d

/-- First position `j₀ = g d K` of group `g`. -/
def groupStart (K d g : ℕ) : ℕ := g * d * K

/-- Number of chunks `min(d, J - g d)` of group `g`. -/
def groupSize (m₀ K d g : ℕ) : ℕ := min d (numChunks m₀ K - g * d)

/-- The slice positions `{j₀ + jK + (K-1-ρ) : j < D}` (Definition 5.6 (`def:walsh-positional`)): bit `ρ`, counted
from the least significant end, of each of the `D` consecutive `K`-bit chunks starting at
position `j₀`. -/
def slicePos (m K j₀ D ρ : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun p : Fin m =>
    j₀ ≤ (p : ℕ) ∧ (p : ℕ) < j₀ + D * K ∧ ((p : ℕ) - j₀) % K = K - 1 - ρ)

/-! ## Layer calls on a slice of the cube -/

/-- Bit `p` of a cube address, `false` outside the cube. -/
def cubeBit {m : ℕ} (x : Cube m) (p : ℕ) : Bool :=
  if h : p < m then x ⟨p, h⟩ else false

/-- The value of `n` bits `b 0, …, b (n-1)`, read most significant bit first. -/
def bitsValMSB (n : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range n, if b i then 2 ^ (n - 1 - i) else 0

/-- `v mod 2^n` as an element of `Fin (2^n)` (used only with `v < 2^n`). -/
def toFinPow (n v : ℕ) : Fin (2 ^ n) :=
  ⟨v % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-- Read a cube address as a layer address of shape `[2^{j₀}] × [2^K]^D × [2^{nS}]`: the first
`j₀` positions (prefix, most significant first), then `D` chunks of `K` positions (chunk `j`
occupies positions `j₀ + jK, …, j₀ + jK + K - 1`, its bit `i` from the least significant end is
position `j₀ + jK + (K-1-i)`), then `nS` positions (suffix). -/
def cubeToAddr (K j₀ D nS : ℕ) {m : ℕ} (x : Cube m) : LayerAddr (2 ^ j₀) K D (2 ^ nS) :=
  (toFinPow j₀ (bitsValMSB j₀ (fun i => cubeBit x i)),
   fun j i => cubeBit x (j₀ + (j : ℕ) * K + (K - 1 - (i : ℕ))),
   toFinPow nS (bitsValMSB nS (fun i => cubeBit x (j₀ + D * K + i))))

/-- Bit `i` of chunk `j` of a chunk family, `false` outside. -/
def chunkBitAt {D K : ℕ} (c : Fin D → Fin K → Bool) (j i : ℕ) : Bool :=
  if hj : j < D then (if hi : i < K then c ⟨j, hj⟩ ⟨i, hi⟩ else false) else false

/-- The inverse reading (`addrToCube ∘ cubeToAddr = id` when `j₀ + D K + nS = m`). -/
def addrToCube (K j₀ D nS m : ℕ) (a : LayerAddr (2 ^ j₀) K D (2 ^ nS)) : Cube m := fun p =>
  if (p : ℕ) < j₀ then (a.1 : ℕ).testBit (j₀ - 1 - (p : ℕ))
  else if (p : ℕ) < j₀ + D * K then
    chunkBitAt a.2.1 (((p : ℕ) - j₀) / K) (K - 1 - ((p : ℕ) - j₀) % K)
  else (a.2.2 : ℕ).testBit (nS - 1 - ((p : ℕ) - j₀ - D * K))

/-- A completed layer call of Proposition A.11 at precision `P` on the slice `(j₀, D, ρ)` of the
cube (shape `[2^{j₀}] × [2^K]^D × [2^{nS}]`), made through the oracle `layer`. -/
noncomputable def sliceCall (layer : LayerOracle) (P r K j₀ D nS : ℕ) (ρ : Fin K) {m : ℕ}
    (z : RArr (Cube m) r) : RArr (Cube m) r :=
  fun x => layer P r (2 ^ j₀) K D (2 ^ nS) ρ (fun a => z (addrToCube K j₀ D nS m a))
    (cubeToAddr K j₀ D nS x)

/-! ## Slice transport: re-indexing lemmas -/

/-- MSB-first recursion: `bitsValMSB (n+1) b = 2 · bitsValMSB n b + b n`. -/
theorem bitsValMSB_succ (n : ℕ) (b : ℕ → Bool) :
    bitsValMSB (n + 1) b = 2 * bitsValMSB n b + (if b n then 1 else 0) := by
  unfold bitsValMSB
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.1 hi
    split_ifs
    · rw [← pow_succ']; congr 1; omega
    · rfl
  · simp

/-- Bit `t` (from the least significant end) of `bitsValMSB n b` is `b (n-1-t)` for `t < n`. -/
theorem testBit_bitsValMSB (n : ℕ) (b : ℕ → Bool) (t : ℕ) :
    (bitsValMSB n b).testBit t = if t < n then b (n - 1 - t) else false := by
  induction n generalizing t with
  | zero => simp [bitsValMSB]
  | succ n ih =>
    rw [bitsValMSB_succ]
    cases t with
    | zero =>
      rw [Nat.testBit_zero]
      cases h : b n <;> simp [h]
    | succ t =>
      rw [Nat.testBit_succ]
      have : (2 * bitsValMSB n b + (if b n then 1 else 0)) / 2 = bitsValMSB n b := by
        split_ifs <;> omega
      rw [this, ih]
      by_cases ht : t < n
      · rw [if_pos ht, if_pos (by omega)]; congr 1; omega
      · rw [if_neg ht, if_neg (by omega)]

/-- `bitsValMSB n b < 2^n`. -/
theorem bitsValMSB_lt (n : ℕ) (b : ℕ → Bool) : bitsValMSB n b < 2 ^ n := by
  induction n with
  | zero => simp [bitsValMSB]
  | succ n ih => rw [bitsValMSB_succ, pow_succ]; split_ifs <;> omega

/-- The slice position of chunk `j < D` lies below `j₀ + D K`. -/
theorem selPos_lt {K j₀ D ρ : ℕ} (hρ : ρ < K) {j : ℕ} (hj : j < D) :
    j₀ + j * K + (K - 1 - ρ) < j₀ + D * K := by
  have h : (j + 1) * K ≤ D * K := Nat.mul_le_mul_right K hj
  rw [Nat.add_mul, one_mul] at h
  omega

/-- The slice positions `j₀ + jK + (K-1-ρ)`, `j < D`, as an embedding `Fin D ↪ Fin m`. -/
def selEmb (K j₀ D m : ℕ) (ρ : Fin K) (hm : j₀ + D * K ≤ m) : Fin D ↪ Fin m where
  toFun j := ⟨j₀ + (j : ℕ) * K + (K - 1 - (ρ : ℕ)), lt_of_lt_of_le (selPos_lt ρ.2 j.2) hm⟩
  inj' := by
    intro j j' h
    simp only [Fin.mk.injEq] at h
    have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) ρ.isLt
    ext
    have h' : (j : ℕ) * K = (j' : ℕ) * K := by omega
    exact Nat.eq_of_mul_eq_mul_right hK h'

/-- Value of `selEmb`. -/
theorem selEmb_val (K j₀ D m : ℕ) (ρ : Fin K) (hm : j₀ + D * K ≤ m) (j : Fin D) :
    ((selEmb K j₀ D m ρ hm j : Fin m) : ℕ) = j₀ + (j : ℕ) * K + (K - 1 - (ρ : ℕ)) := rfl

/-- The slice positions are exactly the image of `selEmb` (for `ρ < K`, `j₀ + D K ≤ m`). -/
theorem slicePos_eq_map {K j₀ D m : ℕ} (ρ : Fin K) (hm : j₀ + D * K ≤ m) :
    slicePos m K j₀ D ρ = Finset.univ.map (selEmb K j₀ D m ρ hm) := by
  ext p
  simp only [slicePos, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) ρ.isLt
  have hρ := ρ.isLt
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hq : ((p : ℕ) - j₀) / K < D := by
      rw [Nat.div_lt_iff_lt_mul hK]; omega
    refine ⟨⟨((p : ℕ) - j₀) / K, hq⟩, ?_⟩
    apply Fin.ext
    rw [selEmb_val]
    have := Nat.div_add_mod' ((p : ℕ) - j₀) K
    simp only
    omega
  · rintro ⟨j, rfl⟩
    rw [selEmb_val]
    refine ⟨by omega, selPos_lt hρ j.2, ?_⟩
    have : j₀ + (j : ℕ) * K + (K - 1 - (ρ : ℕ)) - j₀ = (K - 1 - (ρ : ℕ)) + K * j := by
      rw [Nat.mul_comm]; omega
    rw [this, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)

/-- A slice `(j₀, D, ρ)` inside the cube has exactly `D` positions. -/
theorem card_slicePos {K j₀ D m : ℕ} (ρ : Fin K) (hm : j₀ + D * K ≤ m) :
    (slicePos m K j₀ D ρ).card = D := by
  rw [slicePos_eq_map ρ hm, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- `cubeBit` inside the cube. -/
theorem cubeBit_of_lt {m : ℕ} (x : Cube m) {p : ℕ} (hp : p < m) : cubeBit x p = x ⟨p, hp⟩ := by
  simp [cubeBit, hp]

/-- `addrToCube` on a prefix position. -/
theorem addrToCube_prefix {K j₀ D nS m : ℕ} (a : LayerAddr (2 ^ j₀) K D (2 ^ nS)) (p : Fin m)
    (hp : (p : ℕ) < j₀) :
    addrToCube K j₀ D nS m a p = (a.1 : ℕ).testBit (j₀ - 1 - (p : ℕ)) := by
  simp only [addrToCube, if_pos hp]

/-- `addrToCube` on a chunk position. -/
theorem addrToCube_chunk {K j₀ D nS m : ℕ} (a : LayerAddr (2 ^ j₀) K D (2 ^ nS)) (p : Fin m)
    (h1 : j₀ ≤ (p : ℕ)) (h2 : (p : ℕ) < j₀ + D * K) :
    addrToCube K j₀ D nS m a p =
      chunkBitAt a.2.1 (((p : ℕ) - j₀) / K) (K - 1 - ((p : ℕ) - j₀) % K) := by
  simp only [addrToCube, if_neg (show ¬ (p : ℕ) < j₀ by omega), if_pos h2]

/-- `addrToCube` on a suffix position. -/
theorem addrToCube_suffix {K j₀ D nS m : ℕ} (a : LayerAddr (2 ^ j₀) K D (2 ^ nS)) (p : Fin m)
    (h : j₀ + D * K ≤ (p : ℕ)) :
    addrToCube K j₀ D nS m a p = (a.2.2 : ℕ).testBit (nS - 1 - ((p : ℕ) - j₀ - D * K)) := by
  simp only [addrToCube, if_neg (show ¬ (p : ℕ) < j₀ by omega),
    if_neg (show ¬ (p : ℕ) < j₀ + D * K by omega)]

/-- Round trip: `addrToCube ∘ cubeToAddr = id` when `j₀ + D K + nS = m`. -/
theorem addrToCube_cubeToAddr {K j₀ D nS m : ℕ} (hm : j₀ + D * K + nS = m) (x : Cube m) :
    addrToCube K j₀ D nS m (cubeToAddr K j₀ D nS x) = x := by
  funext p
  have hp := p.isLt
  by_cases h1 : (p : ℕ) < j₀
  · rw [addrToCube_prefix _ p h1]
    simp only [cubeToAddr, toFinPow, Nat.mod_eq_of_lt (bitsValMSB_lt _ _), testBit_bitsValMSB]
    rw [if_pos (by omega), cubeBit_of_lt x (by omega)]
    congr 1; apply Fin.ext; simp only; omega
  by_cases h2 : (p : ℕ) < j₀ + D * K
  · rw [addrToCube_chunk _ p (by omega) h2]
    have hK : 0 < K := by
      rcases Nat.eq_zero_or_pos K with h | h
      · subst h; simp at h2; omega
      · exact h
    have hq : ((p : ℕ) - j₀) / K < D := by rw [Nat.div_lt_iff_lt_mul hK]; omega
    have hmod : ((p : ℕ) - j₀) % K < K := Nat.mod_lt _ hK
    have hr : K - 1 - ((p : ℕ) - j₀) % K < K := by omega
    simp only [chunkBitAt, dif_pos hq, dif_pos hr, cubeToAddr]
    have := Nat.div_add_mod' ((p : ℕ) - j₀) K
    rw [cubeBit_of_lt x (by omega)]
    congr 1; apply Fin.ext; simp only; omega
  · rw [addrToCube_suffix _ p (by omega)]
    simp only [cubeToAddr, toFinPow, Nat.mod_eq_of_lt (bitsValMSB_lt _ _), testBit_bitsValMSB]
    rw [if_pos (by omega), cubeBit_of_lt x (by omega)]
    congr 1; apply Fin.ext; simp only; omega

/-- Outside the slice, `setSelBits` does not change the cube address. -/
theorem addrToCube_setSelBits_of_not_mem {K j₀ D nS m : ℕ} (ρ : Fin K)
    (a : LayerAddr (2 ^ j₀) K D (2 ^ nS)) (e : Fin D → Bool) (p : Fin m)
    (hp : p ∉ slicePos m K j₀ D ρ) :
    addrToCube K j₀ D nS m (setSelBits ρ a e) p = addrToCube K j₀ D nS m a p := by
  by_cases h1 : (p : ℕ) < j₀
  · rw [addrToCube_prefix _ p h1, addrToCube_prefix _ p h1]; rfl
  by_cases h2 : (p : ℕ) < j₀ + D * K
  · rw [addrToCube_chunk _ p (by omega) h2, addrToCube_chunk _ p (by omega) h2]
    have h3 : ((p : ℕ) - j₀) % K ≠ K - 1 - ρ := by
      intro h; apply hp
      simp only [slicePos, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by omega, h2, h⟩
    have hρ := ρ.isLt
    have hK : 0 < K := by omega
    have hmod : ((p : ℕ) - j₀) % K < K := Nat.mod_lt _ hK
    unfold chunkBitAt
    split_ifs with hj hi
    · simp only [setSelBits]
      rw [Function.update_of_ne]
      intro heq
      apply h3
      have := congrArg Fin.val heq
      simp only at this
      omega
    · rfl
    · rfl
  · rw [addrToCube_suffix _ p (by omega), addrToCube_suffix _ p (by omega)]; rfl

/-- At the slice position of chunk `j`, `setSelBits` writes `e j`. -/
theorem addrToCube_setSelBits_selEmb {K j₀ D nS m : ℕ} (ρ : Fin K) (hm : j₀ + D * K ≤ m)
    (a : LayerAddr (2 ^ j₀) K D (2 ^ nS)) (e : Fin D → Bool) (j : Fin D) :
    addrToCube K j₀ D nS m (setSelBits ρ a e) (selEmb K j₀ D m ρ hm j) = e j := by
  have hρ := ρ.isLt
  have hK : 0 < K := by omega
  have hj := j.isLt
  rw [addrToCube_chunk _ _ (by rw [selEmb_val]; omega)
    (by rw [selEmb_val]; exact selPos_lt hρ hj)]
  rw [selEmb_val]
  have e1 : j₀ + (j : ℕ) * K + (K - 1 - (ρ : ℕ)) - j₀ = (K - 1 - (ρ : ℕ)) + K * j := by
    rw [Nat.mul_comm]; omega
  have e2 : ((K - 1 - (ρ : ℕ)) + K * j) / K = j := by
    rw [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt (by omega)]; simp
  have e3 : ((K - 1 - (ρ : ℕ)) + K * j) % K = K - 1 - ρ := by
    rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, e3, show K - 1 - (K - 1 - (ρ : ℕ)) = ρ by omega]
  simp only [chunkBitAt, dif_pos hj, dif_pos hρ, setSelBits]
  simp

/-- **Re-indexing**: the layer `H` of Proposition A.11 on the slice `(j₀, D, ρ)`, read through
`cubeToAddr` / `addrToCube`, is the cube operator `H_{Sel}` with `Sel` the slice positions. -/
theorem layerH_cubeToAddr_eq_hT {r K j₀ D nS m : ℕ} (ρ : Fin K) (hm : j₀ + D * K + nS = m)
    (z : RArr (Cube m) r) (x : Cube m) (k : Fin r) :
    layerH ρ (fun a => z (addrToCube K j₀ D nS m a)) (cubeToAddr K j₀ D nS x) k
      = hT (slicePos m K j₀ D ρ) z x k := by
  have hm' : j₀ + D * K ≤ m := by omega
  have hSel := slicePos_eq_map ρ hm'
  unfold layerH hT
  rw [card_slicePos ρ hm']
  congr 1
  apply Finset.sum_nbij' (fun e => addrToCube K j₀ D nS m (setSelBits ρ (cubeToAddr K j₀ D nS x) e))
    (fun y j => y (selEmb K j₀ D m ρ hm' j))
  · intro e _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro p hp
    rw [addrToCube_setSelBits_of_not_mem ρ _ e p hp, addrToCube_cubeToAddr hm]
  · intro y _; exact Finset.mem_univ _
  · intro e _
    funext j
    exact addrToCube_setSelBits_selEmb ρ hm' _ e j
  · intro y hy
    funext p
    by_cases hp : p ∈ slicePos m K j₀ D ρ
    · rw [hSel] at hp
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hp
      exact addrToCube_setSelBits_selEmb ρ hm' _ _ j
    · rw [addrToCube_setSelBits_of_not_mem ρ _ _ p hp, addrToCube_cubeToAddr hm]
      exact ((Finset.mem_filter.1 hy).2 p hp).symm
  · intro e _
    congr 2
    unfold selSignCount
    rw [hSel, Finset.filter_map, Finset.card_map]
    congr 1
    apply Finset.filter_congr
    intro j _
    simp only [Function.comp_apply, addrToCube_setSelBits_selEmb]
    simp only [cubeToAddr]
    rw [cubeBit_of_lt x (lt_of_lt_of_le (selPos_lt ρ.2 j.2) hm')]
    rfl

/-- **Slice transport** (glue for Proposition A.11 on the cube; Definition 5.6 (`def:walsh-positional`),
Lemma 6.3 (`lem:walsh-layout`)). If `j₀ + D K + nS = m` and the oracle satisfies `LayerSpec` at
precision `P` for the shape `[2^{j₀}] × [2^K]^D × [2^{nS}]` and bit `ρ`, then on disk-grid
arrays at precision `P` the slice call returns exactly `Q_P(H_{Sel} z)`, where `Sel` is the set
of slice positions. CONTRACT (glue). -/
theorem sliceCall_eq (layer : LayerOracle) (P r K j₀ D nS m : ℕ) (ρ : Fin K) (hm : j₀ + D * K + nS = m) (hspec : LayerSpec P r (2 ^ j₀) K D (2 ^ nS) ρ (layer P r (2 ^ j₀) K D (2 ^ nS) ρ)) (z : RArr (Cube m) r) (hz : ArrOnDiskGrid P z) :
    sliceCall layer P r K j₀ D nS ρ z = truncArr P (hT (slicePos m K j₀ D ρ) z) := by
  have hz' : ArrOnDiskGrid P (fun a => z (addrToCube K j₀ D nS m a)) := fun a k => hz _ k
  funext x k
  simp only [sliceCall]
  rw [hspec _ hz']
  simp only [truncArr]
  rw [layerH_cubeToAddr_eq_hT ρ hm z x k]

/-! ## Exact Walsh programs and their abstract cost -/

/-- One step of a Walsh program on the `m`-bit cube (Section 5.1 (`sec:walsh-select`), Proposition 5.5 (`prop:cnot-batch`), Theorem 5.8 (`thm:positional-perm`),
and Theorem 6.5 (`thm:direct-fft`)). Abstract cost: `layer` is one completed call of Proposition A.11;
every other step is a constant number of `O(V)` passes (stream operations of Lemma A.4 or
long-record scans of Lemma A.5), counted by `WStep.passes`.
* `layer P K j₀ D nS ρ`: completed layer call at precision `P` on the slice `(j₀, D, ρ)`;
* `butterflies T P`: exact individual butterflies `H_T` followed by one `Q_P` (a prefix round of
  Section 6 (`sec:direct-fft`); `|T|` butterfly passes and one truncation pass);
* `diag f`: per-record value diagonal (`S_U`, `CZ`, twiddles), computed once per record;
* `scale c`: exact scalar (fourth-root phase, `1-i`, binary shift);
* `trunc P`: `Q_P` on every coefficient (lowering to the `P`-grid);
* `lift P`: re-encoding at precision `P` (append zero fractional bits): identity on values;
* `cnot1 c t`: a single controlled flip `x_t ← x_t ⊕ x_c` by a two-digit permutation
  (Lemma A.4(1)), used for leftover targets. -/
inductive WStep (m : ℕ) : Type where
  | layer (P K j₀ D nS : ℕ) (ρ : Fin K)
  | butterflies (T : Finset (Fin m)) (P : ℕ)
  | diag (f : Cube m → ℂ)
  | scale (c : ℂ)
  | trunc (P : ℕ)
  | lift (P : ℕ)
  | cnot1 (c t : Fin m)

/-- Semantics of one step, given a layer oracle. -/
noncomputable def WStep.run (layer : LayerOracle) (r : ℕ) {m : ℕ} :
    WStep m → RArr (Cube m) r → RArr (Cube m) r
  | .layer P K j₀ D nS ρ => sliceCall layer P r K j₀ D nS ρ
  | .butterflies T P => fun z => truncArr P (hT T z)
  | .diag f => diagArr f
  | .scale c => scaleArr c
  | .trunc P => truncArr P
  | .lift _ => id
  | .cnot1 c t => cnotArr [(c, t)]

/-- Run a program (steps in list order). -/
noncomputable def runProg (layer : LayerOracle) (r : ℕ) {m : ℕ} (prog : List (WStep m))
    (z : RArr (Cube m) r) : RArr (Cube m) r :=
  prog.foldl (fun acc s => s.run layer r acc) z

/-- Number of completed layer calls of a step. -/
def WStep.layerCalls {m : ℕ} : WStep m → ℕ
  | .layer .. => 1
  | _ => 0

/-- Number of `O(V)` passes of a step (`butterflies T P` costs `|T| + 1`). -/
def WStep.passes {m : ℕ} : WStep m → ℕ
  | .layer .. => 0
  | .butterflies T _ => T.card + 1
  | _ => 1

/-- Total number of completed layer calls of a program. -/
def progLayerCalls {m : ℕ} (prog : List (WStep m)) : ℕ := (prog.map WStep.layerCalls).sum

/-- Total number of passes of a program. -/
def progPasses {m : ℕ} (prog : List (WStep m)) : ℕ := (prog.map WStep.passes).sum

end SubNLogN.Math.Walsh
