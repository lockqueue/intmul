import SubNLogN.Math.Walsh.PositionalPerm
import SubNLogN.Math.Walsh.PhaseTable

/-!
# Direct FFT: the DIF schedule, the layout `L`, bit reversal `B` and `U = (LB)^{-1}`

Paper: Section 6.2 (`sec:direct-fft-layout`), Lemma 6.3 (`lem:walsh-layout`),
Remark 6.4 (`rem:walsh-unshuffle`),
and Section 6.3 (`sec:direct-fft-twiddle`, eq. (`eq:combined-round`)).

Shape. There are `D = d - 1` record axes (Lean axes `0, …, D-1` are the paper's axes `1, …, d-1`)
with exponents `a i = lg t_i ∈ {ℓ-1, ℓ}`; the last axis (length `r = 2^ℓ`) is the coefficient list
of each record. The record address has `m₀ = ∑ a_i` bits (`addrBits`). Named slots are pairs
`(i, v)`, `v < a i` (bit `v` of the index `j_i`). The original slot list `𝒪` (`origSlots`) is
`(i, v)`, `i` increasing, `v = a_i - 1, …, 0`; slot `(i, v)` sits at position `origPos a i v`.
The new list is `𝒫 ‖ 𝒞` (`prefixSlots`, `chunkSlots`, `newSlots`), with `b₀ = (ℓ-1) mod K`
(`layoutB0`) and `J_blk = (ℓ-1-b₀)/K` (`layoutJblk`). `L` moves each slot from its position in
`𝒪` to its position in `𝒫 ‖ 𝒞` (`layoutL`); `B` is the per-axis bit reversal
`(i, v) ↦ (i, a_i-1-v)` of `𝒪` (`bitRevB`); `U = (L ∘ B)^{-1}` (`layoutU`). Positional maps use
the move convention of `posPermArr`.

Exact record-axis rounds in layout `L` (`exactRound`): round `v` applies `H_0` on the physical
positions of the slots `(i, v)` of the participating axes (`a i > v`, `roundSet`), then the
combined twiddle `ζ(x) = θ_{2J(x)}`, `J(x) = ∑_i (r/u_i) b_i j_i^{<v} mod r` with `u_i = 2^{v+1}`,
`b_i = x_{(i,v)}`, `j_i^{<v} = ∑_{a<v} 2^a x_{(i,a)}` read through the named-slot table (`twJ`).
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

/-! ## Slots, lists and positional maps -/

/-- `m₀ = ∑_i a_i`, the number of record-address bits. -/
def addrBits {D : ℕ} (a : Fin D → ℕ) : ℕ := (List.ofFn a).sum

/-- `∑_{i' < i} a_{i'}`, the first position of axis `i` in `𝒪`. -/
def axisOffset {D : ℕ} (a : Fin D → ℕ) (i : Fin D) : ℕ := ((List.ofFn a).take i).sum

/-- Position of slot `(i, v)` in `𝒪`. -/
def origPos {D : ℕ} (a : Fin D → ℕ) (i : Fin D) (v : ℕ) : ℕ := axisOffset a i + (a i - 1 - v)

/-- The original slot list `𝒪 = ((i, v) : i increasing, v = a_i - 1, …, 0)`. -/
def origSlots {D : ℕ} (a : Fin D → ℕ) : List (Fin D × ℕ) :=
  (List.finRange D).flatMap (fun i => (List.range (a i)).reverse.map (fun v => (i, v)))

/-- `b₀ = (ℓ - 1) mod K`. -/
def layoutB0 (ℓ K : ℕ) : ℕ := (ℓ - 1) % K

/-- `J_blk = (ℓ - 1 - b₀) / K`. -/
def layoutJblk (ℓ K : ℕ) : ℕ := (ℓ - 1 - layoutB0 ℓ K) / K

/-- `𝒫 = ((i, ℓ-1) : a_i = ℓ, i increasing) ‖ ((i, v) : v = b₀-1, …, 0 (outer), i increasing
(inner))` (Section 6.2 (`sec:direct-fft-layout`)). -/
def prefixSlots {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) : List (Fin D × ℕ) :=
  ((List.finRange D).filter (fun i => a i = ℓ)).map (fun i => (i, ℓ - 1)) ++
    (List.range (layoutB0 ℓ K)).reverse.flatMap (fun v => (List.finRange D).map (fun i => (i, v)))

/-- `𝒞 = ‖_{j < J_blk} ‖_{i} ((i, v) : v = ℓ-2-jK, …, ℓ-1-(j+1)K)` (Section 6.2 (`sec:direct-fft-layout`)). -/
def chunkSlots (D ℓ K : ℕ) : List (Fin D × ℕ) :=
  (List.range (layoutJblk ℓ K)).flatMap (fun j => (List.finRange D).flatMap (fun i =>
    (List.range K).map (fun t => (i, ℓ - 2 - j * K - t))))

/-- The new slot list `𝒫 ‖ 𝒞`. -/
def newSlots {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) : List (Fin D × ℕ) :=
  prefixSlots ℓ K a ++ chunkSlots D ℓ K

/-- `n_P = |𝒫|`. -/
def prefixLen {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) : ℕ := (prefixSlots ℓ K a).length

/-- Physical position of a slot in layout `L` (its index in `𝒫 ‖ 𝒞`). -/
def newPos {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (s : Fin D × ℕ) : ℕ := (newSlots ℓ K a).idxOf s

/-- The positional map `L`: the slot at position `p` of `𝒪` moves to its position in `𝒫 ‖ 𝒞`. -/
def layoutL {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (p : Fin (addrBits a)) : Fin (addrBits a) :=
  match (origSlots a)[(p : ℕ)]? with
  | some s => ⟨newPos ℓ K a s % addrBits a, Nat.mod_lt _ p.pos⟩
  | none => p

/-- The positional map `B`: per-axis bit reversal `(i, v) ↦ (i, a_i - 1 - v)` of `𝒪`. -/
def bitRevB {D : ℕ} (a : Fin D → ℕ) (p : Fin (addrBits a)) : Fin (addrBits a) :=
  match (origSlots a)[(p : ℕ)]? with
  | some s => ⟨origPos a s.1 (a s.1 - 1 - s.2) % addrBits a, Nat.mod_lt _ p.pos⟩
  | none => p

/-- Inverse of a map on `Fin m` by search (the compiler's inversion, proof of Lemma 6.3 (`lem:walsh-layout`)); it is
the inverse function whenever `f` is bijective. -/
def invFunFin {m : ℕ} (f : Fin m → Fin m) (p : Fin m) : Fin m :=
  ((List.finRange m).find? (fun q => f q = p)).getD p

/-- `U = (L ∘ B)^{-1} = B^{-1} ∘ L^{-1}` (Lemma 6.3 (`lem:walsh-layout`), eq. (`eq:unshuffle`)). -/
def layoutU {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) : Fin (addrBits a) → Fin (addrBits a) :=
  invFunFin (fun p => layoutL ℓ K a (bitRevB a p))

/-! ## Rounds, twiddles and the record-axis transform -/

/-- The physical positions (layout `L`) of the slots `(i, v)` of the axes participating in round
`v` (those with `a_i > v`). -/
def roundSet {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) : Finset (Fin (addrBits a)) :=
  Finset.univ.filter (fun p => ∃ i : Fin D, v < a i ∧ newPos ℓ K a (i, v) = (p : ℕ))

/-- The combined twiddle index of round `v` in layout `L` (Section 6.3 (`sec:direct-fft-twiddle`), eq. (`eq:combined-round`)):
`J(x) = ∑_{i : a_i > v} 2^{ℓ-v-1} b_i j_i^{<v} mod 2^ℓ`, where `b_i` is the bit at the physical
position of slot `(i, v)` and `j_i^{<v} = ∑_{a<v} 2^a x_{(i,a)}`. -/
def twJ {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) (x : Cube (addrBits a)) : ℕ :=
  (∑ i : Fin D, if v < a i ∧ cubeBit x (newPos ℓ K a (i, v)) = true then
      2 ^ (ℓ - v - 1) *
        ∑ b ∈ Finset.range v, (if cubeBit x (newPos ℓ K a (i, b)) = true then 2 ^ b else 0)
    else 0) % 2 ^ ℓ

/-- The index `j_i = ∑_{v < a_i} 2^v x_{(i,v)}` of record axis `i`, read in the original layout. -/
def axisVal {D : ℕ} (a : Fin D → ℕ) {m : ℕ} (x : Cube m) (i : Fin D) : ℕ :=
  ∑ v ∈ Finset.range (a i), if cubeBit x (origPos a i v) = true then 2 ^ v else 0

/-- The normalized positive DFT over the record axes `F^+_{t_{<d}}` (Lemma 6.3 (`lem:walsh-layout`)),
on record arrays in the original layout: `M = 2^{m₀}` and
`(F z)(x) = M^{-1} ∑_y z(y) exp(2πi ∑_i j_i(y) j_i(x) / t_i)`, identically on every coefficient. -/
noncomputable def recordDFT {D : ℕ} (a : Fin D → ℕ) {r : ℕ} (z : RArr (Cube (addrBits a)) r) :
    RArr (Cube (addrBits a)) r :=
  fun x k => ((2 : ℂ) ^ addrBits a)⁻¹ * ∑ y : Cube (addrBits a), z y k *
    IntMul.stdChar (∑ i : Fin D, ((axisVal a y i * axisVal a x i : ℕ) : ℝ) / ((2 : ℝ) ^ a i))

/-- The exact grouped round `v` in layout `L` (Section 6.3 (`sec:direct-fft-twiddle`), eq. (`eq:combined-round`)):
`z ↦ D_ζ H z` with `H = H_{roundSet v}` and `ζ(x) = θ_{2J(x)}`. -/
noncomputable def exactRound {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (v : ℕ) {r : ℕ}
    (z : RArr (Cube (addrBits a)) r) : RArr (Cube (addrBits a)) r :=
  diagArr (fun x => theta (2 ^ ℓ) (2 * twJ ℓ K a v x)) (hT (roundSet ℓ K a v) z)

/-- All exact record-axis rounds, at named slots `v = ℓ-1, …, 0` in this order. -/
noncomputable def exactRounds {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) {r : ℕ}
    (z : RArr (Cube (addrBits a)) r) : RArr (Cube (addrBits a)) r :=
  (List.range ℓ).reverse.foldl (fun w v => exactRound ℓ K a v w) z

/-! ## Lemma 6.3 -/

/-- **Lemma 6.3, positional maps** (`lem:walsh-layout`, eq. (`eq:unshuffle`)): for `1 ≤ K ≤ ℓ - 1`,
`ℓ ≥ 2` and `a_i ∈ {ℓ-1, ℓ}`, `L` and `B` are permutations of the `m₀` positions and
`U = (L ∘ B)^{-1}`. CONTRACT (proved in `Walsh/Proofs/LayoutPerm.lean`). -/
def WalshLayoutPermStmt : Prop :=
  ∀ {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (_ : 1 ≤ K) (_ : K ≤ ℓ - 1) (_ : 2 ≤ ℓ)
      (_ : ∀ i, a i = ℓ - 1 ∨ a i = ℓ),
    Function.Bijective (layoutL ℓ K a) ∧ Function.Bijective (bitRevB a) ∧
      (∀ p, layoutU ℓ K a (layoutL ℓ K a (bitRevB a p)) = p) ∧
      (∀ p, layoutL ℓ K a (bitRevB a (layoutU ℓ K a p)) = p)

/-- **Lemma 6.3, chunk rounds are layer shapes** (`lem:walsh-layout`): for a
round at named slot `v` with `b₀ ≤ v ≤ ℓ - 2`, every axis participates, and the selected physical
positions are bit `ρ = (v - b₀) mod K` (from the least significant end) of `D` consecutive `K`-bit
chunks starting at position `j₀ = n_P + ⌊(ℓ-2-v)/K⌋ D K`; that is, the round is a layer of shape
`[2^{j₀}] × [2^K]^D × [2^{m₀ - j₀ - DK}]` for Proposition A.11. CONTRACT (proved in `Walsh/Proofs/LayoutPerm.lean`). -/
def WalshLayoutRoundSliceStmt : Prop :=
  ∀ {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (_ : 1 ≤ K) (_ : K ≤ ℓ - 1) (_ : 2 ≤ ℓ)
      (_ : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) (v : ℕ) (_ : layoutB0 ℓ K ≤ v) (_ : v + 2 ≤ ℓ),
    prefixLen ℓ K a + (ℓ - 2 - v) / K * D * K + D * K ≤ addrBits a ∧
      roundSet ℓ K a v = slicePos (addrBits a) K (prefixLen ℓ K a + (ℓ - 2 - v) / K * D * K) D
        ((v - layoutB0 ℓ K) % K)

/-- **Lemma 6.3, exact counterpart** (`lem:walsh-layout`): the exact DIF
rounds executed in layout `L` on input in the original order have exact counterpart `L B F^+_{t_{<d}}`:
`exactRounds (L z) = L (B (F_{t_{<d}} z))`. CONTRACT (proved in `Walsh/Proofs/`). -/
def WalshLayoutExactStmt : Prop :=
  ∀ {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (_ : 1 ≤ K) (_ : K ≤ ℓ - 1) (_ : 2 ≤ ℓ)
      (_ : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) {r : ℕ} (z : RArr (Cube (addrBits a)) r),
    exactRounds ℓ K a (posPermArr (layoutL ℓ K a) z) =
      posPermArr (layoutL ℓ K a) (posPermArr (bitRevB a) (recordDFT a z))

/-- **Lemma 6.3, natural-order restoration** (`lem:walsh-layout`, eq. (`eq:unshuffle`)):
`U (L (B w)) = w` on record arrays, i.e. `U = (LB)^{-1}`. CONTRACT (proved in `Walsh/Proofs/LayoutPerm.lean`). -/
def WalshLayoutUnshuffleStmt : Prop :=
  ∀ {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (_ : 1 ≤ K) (_ : K ≤ ℓ - 1) (_ : 2 ≤ ℓ)
      (_ : ∀ i, a i = ℓ - 1 ∨ a i = ℓ) {r : ℕ} (w : RArr (Cube (addrBits a)) r),
    posPermArr (layoutU ℓ K a) (posPermArr (layoutL ℓ K a) (posPermArr (bitRevB a) w)) = w

/-- **Remark 6.4** (`rem:walsh-unshuffle`), sanity check of the definitions on the paper's
example: record-axis widths `(4, 3)` (`a = (4, 3)`, `ℓ = 4`), `K = 2`; in destination-list notation
`L = (0,3,4,1,5,6,2)` and `B = (3,2,1,0,6,5,4)`. CONTRACT (proved below by `decide`). -/
def WalshUnshuffleExampleStmt : Prop :=
  (List.finRange 7).map (fun p => (layoutL 4 2 ![4, 3] p : ℕ)) = [0, 3, 4, 1, 5, 6, 2] ∧
      (List.finRange 7).map (fun p => (bitRevB ![4, 3] p : ℕ)) = [3, 2, 1, 0, 6, 5, 4]

/-- Remark 6.4's example holds for the definitions (kernel evaluation). -/
theorem walsh_unshuffle_example : WalshUnshuffleExampleStmt := by
  unfold WalshUnshuffleExampleStmt
  decide

end SubNLogN.Math.Walsh
