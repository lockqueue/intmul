import SubNLogN.Math.Bridge.Kernel
import SubNLogN.Math.Common.Norms

/-!
# Bridge: spreading, alias and truncation operators; Lemma 4.2 (bridge Lemma A) and Lemma 4.4 (bridge Lemma B)

Paper: Sections 4.1–4.3 (`sec:bridge-conventions`–`sec:bridge-B`). Lean axes are 0-based: Lean axis `i` is the paper's axis
`h = i + 1`. Spread axes: Lean `i = d-1, …, 1` (paper `h = d, …, 2`). Arrays on the 1-D index
`Fin R` are in input order (`encIn`) or frequency order (`encFreq`); tensors are `Idx t → ℂ`.

Standing assumptions of Section 4 (`sec:bridge`, Section 4.1 (`sec:bridge-conventions`)): `R = t_1⋯t_d` with every `t_i ≥ 2` a power of
two (`ShapeOK t`), alias width `ω ≥ 8` and `α` admissible.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

variable {d : ℕ}

/-- Standing shape assumption of Section 4.1 (`sec:bridge-conventions`): every `t_i ≥ 2` is a power of two. -/
def ShapeOK (t : Fin d → ℕ) : Prop := ∀ i, 2 ≤ t i ∧ ∃ a : ℕ, t i = 2 ^ a

theorem toNat_emod_lt {R : ℕ} (hR : 0 < R) (n : ℤ) : (n % (R : ℤ)).toNat < R := by
  have h1 : 0 ≤ n % (R : ℤ) := Int.emod_nonneg n (by exact_mod_cast hR.ne')
  have h2 : n % (R : ℤ) < (R : ℤ) := Int.emod_lt_of_pos n (by exact_mod_cast hR)
  omega

/-- `(f + n) mod R` as an element of `Fin R`. -/
def shiftFin {R : ℕ} (f : Fin R) (n : ℤ) : Fin R :=
  ⟨(((f : ℕ) + n : ℤ) % (R : ℤ)).toNat, toNat_emod_lt ((Nat.zero_le _).trans_lt f.isLt) _⟩

/-- Lower-digit index `∑_{l<i} j_l A_l ∈ [A_i]` (numerator of `δ_h`, Section 4.1, eq. (`eq:delta`)). -/
def lowerIndex (t : Fin d → ℕ) (i : Fin d) (j : Idx t) : ℕ :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin d => l < i), (j l : ℕ) * prefixProd t l

/-- Fractional shift `δ_h(j) = (∑_{l<h} j_l A_l)/A_h ∈ [0,1)` (Section 4.1, eq. (`eq:delta`)),
for Lean axis `i` (paper `h = i+1`). -/
noncomputable def fracShift (t : Fin d → ℕ) (i : Fin d) (j : Idx t) : ℝ :=
  (lowerIndex t i j : ℝ) / (prefixProd t i : ℝ)

/-- Spreading along Lean axis `i` (Section 4.2, eq. (`eq:spread-axis`)):
`(S_h V)_{…k_h…} = ∑_{j_h} V_{…j_h…} H^{(h)}_{δ_h}(j_h - k_h)`; `δ_h` only reads the digits below
`h`, which `S_h` does not change. -/
noncomputable def spreadAxis (α : ℝ) (t : Fin d → ℕ) (i : Fin d) (V : Idx t → ℂ) : Idx t → ℂ :=
  fun k => ∑ a : Fin (t i), V (Function.update k i a) *
    foldedFilter α (t i) (fracShift t i k) ((a : ℤ) - ((k i : ℕ) : ℤ))

/-- Lean axes in the order in which they are spread: `d-1, …, 1` (paper `h = d, …, 2`,
Section 4.2, eq. (`eq:spread-product`)). -/
def spreadOrder (d : ℕ) : List (Fin d) :=
  (List.finRange d).reverse.filter (fun i => (i : ℕ) ≠ 0)

/-- Lean axes `1, …, d-1` in increasing order (paper `h = 2, …, d`), the chronological order of
the deconvolutions `B_2^{-1}, …, B_d^{-1}` (Section 4.3 (`sec:bridge-B`)). -/
def deconvOrder (d : ℕ) : List (Fin d) :=
  (List.finRange d).filter (fun i => (i : ℕ) ≠ 0)

/-- `U = S_2 S_3 ⋯ S_d V` (`S_d` applied first; Section 4.2, eq. (`eq:spread-product`)). -/
noncomputable def spreadAll (α : ℝ) (t : Fin d → ℕ) (V : Idx t → ℂ) : Idx t → ℂ :=
  (spreadOrder d).foldl (fun W i => spreadAxis α t i W) V

/-- `R/A_h` for paper axis `h = i+1`: the weight of frequency digit `h-1` (Section 4.1, eq. (`eq:freq-digits`)). -/
def aliasStep (t : Fin d → ℕ) (i : Fin d) : ℕ := totalLen t / prefixProd t i

/-- The sample point `y = (u_h(f) + 1/2)/t_h` of frequency `f` (Section 4.2, eq. (`eq:alias-op`) and Section 4.3, eq. (`eq:Bh`)). -/
noncomputable def samplePt (t : Fin d → ℕ) (i : Fin d) (f : Fin (totalLen t)) : ℝ :=
  ((((encFreq t).symm f i : Fin (t i)) : ℕ) + 1 / 2 : ℝ) / (t i : ℝ)

/-- Matrix of the alias operator `A_h` (Section 4.2, eq. (`eq:alias-op`)):
`(A_h Z)_f = ∑_{m∈ℤ} G((u_h(f)+1/2)/t_h - m) Z_{(f - mR/A_h) mod R}`. -/
noncomputable def aliasMatrix (α : ℝ) (t : Fin d → ℕ) (i : Fin d) :
    Matrix (Fin (totalLen t)) (Fin (totalLen t)) ℂ :=
  fun f f' => ∑' m : ℤ,
    if shiftFin f (-(m * (aliasStep t i : ℤ))) = f' then (kernelG α (samplePt t i f - m) : ℂ) else 0

/-- Matrix of the two-term truncation `B_h` (Section 4.3, eq. (`eq:Bh`)):
`(B_h Z)_f = c_0 Z_f + c_1 Z_{(f - R/A_h) mod R}`, `c_0 = G(y)`, `c_1 = G(y - 1)`. -/
noncomputable def truncMatrix (α : ℝ) (t : Fin d → ℕ) (i : Fin d) :
    Matrix (Fin (totalLen t)) (Fin (totalLen t)) ℂ :=
  fun f f' => (if f' = f then (kernelG α (samplePt t i f) : ℂ) else 0) +
    (if f' = shiftFin f (-(aliasStep t i : ℤ)) then (kernelG α (samplePt t i f - 1) : ℂ) else 0)

/-- `A_2 A_3 ⋯ A_d` (Lemma 4.2 (`lem:bridge-A`), eq. (`eq:lemma-A`)). -/
noncomputable def aliasProd (α : ℝ) (t : Fin d → ℕ) : Matrix (Fin (totalLen t)) (Fin (totalLen t)) ℂ :=
  ((deconvOrder d).map (aliasMatrix α t)).prod

/-- `B_2 B_3 ⋯ B_d`; its inverse `(B_2⋯B_d)^{-1}` is Mathlib's matrix inverse (Lemma 4.4 (`lem:bridge-B`)(vi)). -/
noncomputable def truncProd (α : ℝ) (t : Fin d → ℕ) : Matrix (Fin (totalLen t)) (Fin (totalLen t)) ℂ :=
  ((deconvOrder d).map (truncMatrix α t)).prod

/-- The cyclic bidiagonal operator `Z_j ↦ c_0 Z_j + c_1 Z_{j-1}` on a cycle of length `L`
(Lemma 4.4 (bridge Lemma B, `lem:bridge-B`)(v)). -/
noncomputable def cycBidiag (c0 c1 : ℂ) (L : ℕ) : Matrix (Fin L) (Fin L) ℂ :=
  fun j j' => (if j' = j then c0 else 0) + (if j' = shiftFin j (-1) then c1 else 0)

end SubNLogN.Math.Bridge
