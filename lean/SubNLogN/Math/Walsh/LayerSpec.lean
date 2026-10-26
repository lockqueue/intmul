import SubNLogN.Math.Common.Grid

/-!
# Walsh: functional specification of the simultaneous butterfly layer

Paper: Proposition A.11 (`prop:prop14-param`, parameterizing Proposition 14 of [OAI26]), value-level part only.

This file fixes the *functional* (value-level) contract of one completed butterfly layer of
Proposition A.11, as a predicate `LayerSpec` on functions between record arrays. Cost, tape format
(signed `w`-bit two's-complement components, headers), internal guard widths and the parameter
bands of Proposition A.11 are *not* part of this predicate; they belong to the machine-level
statement of Proposition A.11, which concludes `LayerSpec` for the input/output function
of its procedure.

Conventions.
* A record array over an address type `α` with records of `r` complex coefficients is
  `RArr α r = α → Fin r → ℂ`; the ring `R_r` of the paper is only a container (no ring product is
  used). The paper's `‖z‖_∞` (largest modulus of a coefficient) is Mathlib's Pi sup norm on
  `α → Fin r → ℂ` (the nested sup norm is the global sup).
* Layer addresses `[A] × [2^K]^D × [S]` are `LayerAddr A K D S = Fin A × (Fin D → Fin K → Bool) × Fin S`.
  A `K`-bit chunk value `c ∈ [2^K]` is represented by its binary digit vector
  `c : Fin K → Bool`, digit `i` having weight `2^i` (`chunkVal`); hence `c ρ` is bit `ρ` *counted
  from the least significant end*, as in Proposition A.11. The lexicographic record order
  (prefix most significant, then chunk `0`, …, chunk `D-1`, then suffix) is `lexIndex`.
* `H_0 = (1/2) [[1, 1], [1, -1]]` (so `H_0^2 = I/2`, Lemma 5.1 (`lem:walsh-select`)).
* `layerH ρ` is the paper's `H`: `H_0` applied on bit `ρ` of each of the `D` chunks.

Main definitions: `RArr`, `truncArr` (coefficientwise `Q_P`), `ArrOnGrid`, `ArrOnDiskGrid`,
`LayerAddr`, `chunkVal`, `lexIndex`, `setSelBits`, `selSignCount`, `layerH`, `LayerSpec`,
`LayerOracle`.
Consequences proved here: the layer `H` is an `∞`-norm contraction; a function satisfying
`LayerSpec` maps disk-grid arrays to disk-grid arrays, with `‖f z - H z‖_∞ < √2 · 2^{-P}`.
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

/-! ## Record arrays -/

/-- A record array: every address `x : α` carries a record of `r` complex coefficients
(coefficient order `Fin r`). -/
abbrev RArr (α : Type) (r : ℕ) : Type := α → Fin r → ℂ

/-- Coefficientwise truncation toward zero `Q_P` of a record array (Definition 3.1 (`def:grid`)). -/
noncomputable def truncArr {α : Type} {r : ℕ} (P : ℕ) (z : RArr α r) : RArr α r :=
  fun x k => truncC P (z x k)

/-- Every coefficient of the array lies on the `P`-grid `2^{-P}(ℤ + iℤ)`. -/
def ArrOnGrid {α : Type} {r : ℕ} (P : ℕ) (z : RArr α r) : Prop :=
  ∀ x k, OnGrid P (z x k)

/-- Disk-grid array at precision `P`: every coefficient lies in `𝔻_P` (on the `P`-grid and of
modulus at most `1`). -/
def ArrOnDiskGrid {α : Type} {r : ℕ} (P : ℕ) (z : RArr α r) : Prop :=
  ∀ x k, OnDiskGrid P (z x k)

/-! ## Layer addresses and the butterfly layer `H` -/

/-- Addresses `[A] × [2^K]^D × [S]` of a layer call: a prefix `a ∈ [A]`, `D` chunk values given by
their binary digit vectors (digit `i` has weight `2^i`), and a suffix `s ∈ [S]`. -/
abbrev LayerAddr (A K D S : ℕ) : Type := Fin A × (Fin D → Fin K → Bool) × Fin S

/-- The value `∑ i, c_i 2^i ∈ [2^K]` of a chunk digit vector. -/
def chunkVal {K : ℕ} (c : Fin K → Bool) : ℕ :=
  ∑ i : Fin K, if c i then 2 ^ (i : ℕ) else 0

/-- Lexicographic record index on `[A] × [2^K]^D × [S]` (prefix most significant, then chunk `0`,
…, chunk `D-1`, then the suffix); this is the record order of the input of Proposition A.11. -/
def lexIndex {A K D S : ℕ} (x : LayerAddr A K D S) : ℕ :=
  ((x.1 : ℕ) * 2 ^ (K * D) + ∑ j : Fin D, chunkVal (x.2.1 j) * 2 ^ (K * (D - 1 - (j : ℕ)))) * S
    + (x.2.2 : ℕ)

/-- `setSelBits ρ x e`: the address `x` with bit `ρ` of chunk `j` replaced by `e j`, for every
chunk `j`. -/
def setSelBits {A K D S : ℕ} (ρ : Fin K) (x : LayerAddr A K D S) (e : Fin D → Bool) :
    LayerAddr A K D S :=
  (x.1, fun j => Function.update (x.2.1 j) ρ (e j), x.2.2)

/-- The number of chunks `j` with bit `ρ` of `x` set and `e j` set; `(-1)^this` is the product of
the `H_0`-matrix signs `∏_j (-1)^{x_{j,ρ} e_j}`. -/
def selSignCount {A K D S : ℕ} (ρ : Fin K) (x : LayerAddr A K D S) (e : Fin D → Bool) : ℕ :=
  (Finset.univ.filter (fun j : Fin D => x.2.1 j ρ = true ∧ e j = true)).card

/-- The normalized butterfly layer `H` of Proposition A.11: `H_0 = (1/2)[[1,1],[1,-1]]` applied on
bit `ρ` (counted from the least significant end) of each of the `D` chunks, identically on every
coefficient of the record:
`(H z)(x) = 2^{-D} ∑_{e ∈ {0,1}^D} (-1)^{∑_j x_{j,ρ} e_j} z(x[bit ρ of chunk j := e_j])`. -/
noncomputable def layerH {r A K D S : ℕ} (ρ : Fin K) (z : RArr (LayerAddr A K D S) r) :
    RArr (LayerAddr A K D S) r :=
  fun x k => ((2 : ℂ) ^ D)⁻¹ *
    ∑ e : Fin D → Bool, (-1 : ℂ) ^ selSignCount ρ x e * z (setSelBits ρ x e) k

/-! ## The functional layer contract -/

/-- **Functional contract of the simultaneous butterfly layer** (value-level part of Proposition A.11
(`prop:prop14-param`)): on every disk-grid input array at precision `P` on `[A] × [2^K]^D × [S]` with
records of length `r`, the function `f` returns exactly `Q_P(H z)`, where `H = layerH ρ`.

Not included (machine level): the tape format and width `w` (any `w ≥ P + 2` holds every
disk-grid component), the header, the parameter bands, internal guard widths and the time bound.
Disk preservation and the error bound `‖Q_P(Hz) - Hz‖_∞ < √2 · 2^{-P}` are consequences
(`LayerSpec.onDiskGrid`, `LayerSpec.norm_sub_lt`). -/
def LayerSpec (P r A K D S : ℕ) (ρ : Fin K)
    (f : RArr (LayerAddr A K D S) r → RArr (LayerAddr A K D S) r) : Prop :=
  ∀ z : RArr (LayerAddr A K D S) r, ArrOnDiskGrid P z → f z = truncArr P (layerH ρ z)

/-- A *layer oracle*: for every precision `P`, record length `r`, shape `(A, K, D, S)` and
selected bit `ρ`, some function on record arrays (for instance the decoded input/output function
of the procedure of Proposition A.11). Users assume `LayerSpec` at the calls they make. -/
def LayerOracle : Type :=
  (P r A K D S : ℕ) → (ρ : Fin K) → RArr (LayerAddr A K D S) r → RArr (LayerAddr A K D S) r

/-! ## Consequences -/

/-- `H` is an `∞`-norm contraction, pointwise form: if every coefficient of `z` has modulus at
most `B`, so does every coefficient of `H z` (each output is `2^{-D}` times a signed sum of `2^D`
input coefficients; Lemma 5.2 (`lem:walsh-exact`), Theorem 6.5 (`thm:direct-fft`)). -/
theorem norm_layerH_apply_le {r A K D S : ℕ} (ρ : Fin K) (z : RArr (LayerAddr A K D S) r)
    {B : ℝ} (hz : ∀ y k, ‖z y k‖ ≤ B) (x : LayerAddr A K D S) (k : Fin r) :
    ‖layerH ρ z x k‖ ≤ B := by
  have hsum : ‖∑ e : Fin D → Bool, (-1 : ℂ) ^ selSignCount ρ x e * z (setSelBits ρ x e) k‖
      ≤ 2 ^ D * B := by
    calc ‖∑ e : Fin D → Bool, (-1 : ℂ) ^ selSignCount ρ x e * z (setSelBits ρ x e) k‖
        ≤ ∑ e : Fin D → Bool, ‖(-1 : ℂ) ^ selSignCount ρ x e * z (setSelBits ρ x e) k‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _e : Fin D → Bool, B := by
          apply Finset.sum_le_sum
          intro e _
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact hz _ _
      _ = 2 ^ D * B := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool]
  have h2 : (0 : ℝ) < 2 ^ D := by positivity
  calc ‖layerH ρ z x k‖
      = ((2 : ℝ) ^ D)⁻¹ *
          ‖∑ e : Fin D → Bool, (-1 : ℂ) ^ selSignCount ρ x e * z (setSelBits ρ x e) k‖ := by
        simp [layerH, norm_inv, norm_pow]
    _ ≤ ((2 : ℝ) ^ D)⁻¹ * (2 ^ D * B) := by gcongr
    _ = B := by field_simp

/-- `H` is an `∞`-norm contraction: `‖H z‖_∞ ≤ ‖z‖_∞`. -/
theorem norm_layerH_le {r A K D S : ℕ} (ρ : Fin K) (z : RArr (LayerAddr A K D S) r) :
    ‖layerH ρ z‖ ≤ ‖z‖ := by
  refine pi_norm_le_iff_of_nonneg (norm_nonneg z) |>.2 fun x => ?_
  refine pi_norm_le_iff_of_nonneg (norm_nonneg z) |>.2 fun k => ?_
  refine norm_layerH_apply_le ρ z (fun y k' => ?_) x k
  exact (norm_le_pi_norm (z y) k').trans (norm_le_pi_norm z y)

/-- **Disk preservation** (Proposition A.11, `prop:prop14-param`): a function satisfying `LayerSpec`
maps disk-grid arrays at precision `P` to disk-grid arrays at precision `P`. -/
theorem LayerSpec.onDiskGrid {P r A K D S : ℕ} {ρ : Fin K}
    {f : RArr (LayerAddr A K D S) r → RArr (LayerAddr A K D S) r}
    (hf : LayerSpec P r A K D S ρ f) {z : RArr (LayerAddr A K D S) r}
    (hz : ArrOnDiskGrid P z) : ArrOnDiskGrid P (f z) := by
  rw [hf z hz]
  intro x k
  exact truncC_mem_diskGrid P _ (norm_layerH_apply_le ρ z (fun y k' => (hz y k').2) x k)

/-- **Layer error bound** (Proposition A.11, `prop:prop14-param`): for a function satisfying
`LayerSpec` and a disk-grid input, `‖f z - H z‖_∞ < √2 · 2^{-P}`. -/
theorem LayerSpec.norm_sub_lt {P r A K D S : ℕ} {ρ : Fin K}
    {f : RArr (LayerAddr A K D S) r → RArr (LayerAddr A K D S) r}
    (hf : LayerSpec P r A K D S ρ f) {z : RArr (LayerAddr A K D S) r}
    (hz : ArrOnDiskGrid P z) : ‖f z - layerH ρ z‖ < Real.sqrt 2 * gridUnit P := by
  rw [hf z hz]
  have hpos : 0 < Real.sqrt 2 * gridUnit P :=
    mul_pos (Real.sqrt_pos.2 two_pos) (gridUnit_pos P)
  refine (pi_norm_lt_iff hpos).2 fun x => ?_
  refine (pi_norm_lt_iff hpos).2 fun k => ?_
  simpa [truncArr] using norm_truncC_sub_lt P (layerH ρ z x k)

end SubNLogN.Math.Walsh
