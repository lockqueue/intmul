import SubNLogN.Math.Bridge.Components
import SubNLogN.Math.Common.MiddleContract

/-!
# Bridge: the fixed-point bridge `bridgeFixed` (Section 4.4 (`sec:bridge-alg`))

Value-level reference algorithm with explicit rounding points:
1. pre-scaling `x' = x/S` (exact), `S = 2^{H + ⌈(lg D)/2⌉ + 4}`;
2. reorder to tensor order (`encIn`), spread axes `h = d, …, 2` (one `Quant_q` per output);
3. middle transform `run` (Definition 4.5);
4. fixed-point solvers `B_2^{-1}, …, B_d^{-1}` in natural frequency order;
5. exact multiplication by `S`, one `Quant_{p+2}`.
Tables (taps, `μ̂`, `â`, `γ̂`) are parameters and are constrained only by `TablesCertified`. Tape
layout and bit widths are proved at the machine level.

The rounding-parametric versions (`TablesCertifiedR`, `spreadFixedR`, `deconvAxisFixedR`,
`deconvFixedR`, `spreadStageR`, `bridgePreR`, `bridgeFixedR`; nearest rounding `rr`, last
section) are the current interface; the `quantC`/`quantR` versions are legacy `quantC`/`quantR` specializations
retained for compatibility.
-/

namespace SubNLogN.Math.Bridge

open SubNLogN.Math.Common
open scoped BigOperators

variable {d : ℕ}

/-! ## Schedule (Theorem 4.7 (`thm:bridge-precision`), eq. (`eq:schedule`)) -/

/-- Alias width `ω = p + k + ⌈lg d⌉ + 20`. -/
def schedOmega (p k d : ℕ) : ℕ := p + k + lg d + 20

/-- Working precision `P = 2p + 12k + 32⌈lg(p+k+2)⌉ + 256`. Since `p + k + 2 ≥ 2`,
`⌈lg(p+k+2)⌉ = Nat.clog 2 (p+k+2)`. Written with `Nat.clog` so that
`schedP (Cost.pBK b k) k = Cost.PBK b k` holds by `rfl` (definitional identification with `Cost.PBK`). -/
def schedP (p k : ℕ) : ℕ := 2 * p + 12 * k + 32 * Nat.clog 2 (p + k + 2) + 256

/-- Grid precision `q = P + 2`. -/
def schedQ (p k : ℕ) : ℕ := schedP p k + 2

/-- Component width `w = q + 2`. -/
def schedW (p k : ℕ) : ℕ := schedQ p k + 2

/-! ## Tables -/

/-- The bridge tables: taps `tap i a e` (axis `i`, shift `δ = a/A_h`, offset `e`) and solver
parameters `μ̂, â, γ̂` per axis `i` and frequency digit `u`. -/
structure BridgeTables {d : ℕ} (t : Fin d → ℕ) where
  /-- stored folded taps -/
  tap : Fin d → ℕ → ℤ → ℂ
  /-- `μ̂ ≈ c_max^{-1}` -/
  mu : Fin d → ℕ → ℝ
  /-- `â ≈ a' = c_min/c_max` -/
  ahat : Fin d → ℕ → ℝ
  /-- `γ̂ ≈ (1 - â^L)^{-1}`, `L = A_h` -/
  gam : Fin d → ℕ → ℝ

/-- `c_0(u) = G((u+1/2)/t)` (Section 4.3, eq. (`eq:Bh`)). -/
noncomputable def coeffC0 (α : ℝ) (t u : ℕ) : ℝ := kernelG α (((u : ℝ) + 1 / 2) / (t : ℝ))

/-- `c_1(u) = G((u+1/2)/t - 1)` (Section 4.3, eq. (`eq:Bh`)). -/
noncomputable def coeffC1 (α : ℝ) (t u : ℕ) : ℝ := kernelG α (((u : ℝ) + 1 / 2) / (t : ℝ) - 1)

/-- Certified tables for Theorem 4.7 (`thm:bridge-precision`, Section 4.4 (`sec:bridge-alg`)), at `q = P + 2`, `v = 2^{-q}`.
For every spread axis:
* the taps are certified as in `TapsCertified` (complex taps to `2v`);
* `μ̂, â` lie on the `q`-grid with `|μ̂ - c_max^{-1}| ≤ v`, `|â - a'| ≤ v`, `â ≥ 0`;
* `γ̂` is computed from the stored `â` by `closureFixed` with `Q = closurePrec q A_h t_h`. -/
def TablesCertified (α : ℝ) (P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) : Prop :=
  ∀ i : Fin d, (i : ℕ) ≠ 0 →
    TapsCertified α P t i (T.tap i) ∧
    ∀ u : ℕ, u < t i →
      OnGridR (P + 2) (T.mu i u) ∧ OnGridR (P + 2) (T.ahat i u) ∧
      |T.mu i u - (max (coeffC0 α (t i) u) (coeffC1 α (t i) u))⁻¹| ≤ gridUnit (P + 2) ∧
      |T.ahat i u - min (coeffC0 α (t i) u) (coeffC1 α (t i) u) /
        max (coeffC0 α (t i) u) (coeffC1 α (t i) u)| ≤ gridUnit (P + 2) ∧
      0 ≤ T.ahat i u ∧
      T.gam i u = closureFixed (P + 2) (closurePrec (P + 2) (prefixProd t i) (t i)) (T.ahat i u)
        (prefixProd t i)

/-! ## The algorithm -/

/-- `H = 1 + ⌈log₂ C⌉`, `C = max(1, max_j |Re x_j|, max_j |Im x_j|)`, so `X ≤ 2^H < 4X`
(proof of Theorem 4.7 (`thm:bridge-precision`)). -/
noncomputable def preScaleH {R : ℕ} (x : Fin R → ℂ) : ℤ :=
  1 + Int.clog 2 (max 1 (max ‖fun j => (x j).re‖ ‖fun j => (x j).im‖))

/-- `D = R/t_1 = ∏_{h≥2} t_h` (Section 4.4 (`sec:bridge-alg`)). -/
def dimD (t : Fin d → ℕ) : ℕ := ∏ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) ≠ 0), t i

/-- The exponent of `S = 2^{H + ⌈(lg D)/2⌉ + 4}` (step (1), Section 4.4 (`sec:bridge-alg`)). -/
noncomputable def preScaleExp (t : Fin d → ℕ) (x : Fin (totalLen t) → ℂ) : ℕ :=
  (preScaleH x).toNat + (lg (dimD t) + 1) / 2 + 4

/-- Step (2): fixed-point spreading of the axes `h = d, …, 2`. -/
noncomputable def spreadFixed (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (V : Idx t → ℂ) :
    Idx t → ℂ :=
  (spreadOrder d).foldl (fun W i => spreadAxisFixed q t i (T.tap i) W) V

/-- One fixed-point deconvolution stage `B_h^{-1}` (step (4), Section 4.4 (`sec:bridge-alg`);
Section 4.6 (`sec:bridge-D`)). In natural frequency order the cycle of `f` is
`f_j = j·R/A_h + s` (`j ∈ [A_h]`, `s ∈ [R/A_h]`). The digit `u = u_h(f)` is constant on it, and the
orientation is `c_0 > c_1 ⟺ u < t_h/2`. -/
noncomputable def deconvAxisFixed (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (i : Fin d)
    (Y : Fin (totalLen t) → ℂ) : Fin (totalLen t) → ℂ :=
  fun f =>
    let w := aliasStep t i
    let j0 := (f : ℕ) / w
    let u := (((encFreq t).symm f i : Fin (t i)) : ℕ)
    cycSweep (decide (2 * u < t i)) q (T.mu i u) (T.ahat i u) (T.gam i u) (prefixProd t i)
      (fun j => Y (shiftFin f (((j : ℤ) - (j0 : ℤ)) * (w : ℤ)))) j0

/-- Step (4): the solvers `B_2^{-1}, B_3^{-1}, …, B_d^{-1}` in this order. -/
noncomputable def deconvFixed (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (Y : Fin (totalLen t) → ℂ) : Fin (totalLen t) → ℂ :=
  (deconvOrder d).foldl (fun Z i => deconvAxisFixed q t T i Z) Y

/-- The pre-scaled input `x' = x/S` (step (1)). -/
noncomputable def preScaled (t : Fin d → ℕ) (x : Fin (totalLen t) → ℂ) : Fin (totalLen t) → ℂ :=
  fun j => x j / (2 : ℂ) ^ preScaleExp t x

/-- The completed spread array `U` (end of step (2)). -/
noncomputable def spreadStage (P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (x : Fin (totalLen t) → ℂ) : Idx t → ℂ :=
  spreadFixed (P + 2) t T (fun j => preScaled t x (encIn t j))

/-- The value `S·Ẑ` before the final rounding (end of step (5) before rounding). -/
noncomputable def bridgePre (P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (run : (Idx t → ℂ) → (Idx t → ℂ)) (x : Fin (totalLen t) → ℂ) : Fin (totalLen t) → ℂ :=
  fun f => (2 : ℂ) ^ preScaleExp t x *
    deconvFixed (P + 2) t T (fun f' => run (spreadStage P t T x) ((encFreq t).symm f')) f

/-- The fixed-point bridge `F̂_R x` (Section 4.4 (`sec:bridge-alg`)), returned on the `(p+2)`-grid. -/
noncomputable def bridgeFixed (p P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (run : (Idx t → ℂ) → (Idx t → ℂ)) (x : Fin (totalLen t) → ℂ) : Fin (totalLen t) → ℂ :=
  fun f => quantC (p + 2) (bridgePre P t T run x f)

/-- The exact counterpart on the pre-scaled input, rescaled: `S·(B_2⋯B_d)^{-1} F_t U'` with
`U' = S_2⋯S_d x'` (used for the split of the error in Theorem 4.7). -/
noncomputable def bridgeExactScaled (α : ℝ) (t : Fin d → ℕ) (x : Fin (totalLen t) → ℂ) :
    Fin (totalLen t) → ℂ :=
  fun f => (2 : ℂ) ^ preScaleExp t x *
    Matrix.mulVec (truncProd α t)⁻¹
      (fun f' => dftTensor t (spreadAll α t (fun j => preScaled t x (encIn t j))) ((encFreq t).symm f'))
      f

/-- The standing balanced shape of Section 4.4 (`sec:bridge-alg`): `R = t_1⋯t_d = 2^k` with
`d ≥ 2`, `t_d = r = 2^ℓ`, `ℓ ≥ 2`, and `t_i ∈ {r/2, r}`. -/
def BalancedShape (t : Fin d → ℕ) (k ℓ : ℕ) : Prop :=
  2 ≤ d ∧ totalLen t = 2 ^ k ∧ 2 ≤ ℓ ∧ (∀ h : d - 1 < d, t ⟨d - 1, h⟩ = 2 ^ ℓ) ∧
    ∀ i, t i = 2 ^ ℓ ∨ 2 * t i = 2 ^ ℓ

/-! ## Parametric-rounding versions (nearest-rounding parameter `rr`)

Each `…R` definition is the definition of the same name without `R`, with the bridge's nearest
rounding a parameter `rr` (leading argument; see `Components.lean`). The `quantC`/`quantR`
definitions above (`TablesCertified`, `spreadFixed`, `deconvAxisFixed`, `deconvFixed`,
`spreadStage`, `bridgePre`, `bridgeFixed`) are legacy `quantC`/`quantR` specializations retained for compatibility. -/

/-- `TablesCertified` for the rounding `rr`: as `TablesCertified`, with `γ̂` computed from the
stored `â` by `closureFixedR rr` with `Q = closurePrec q A_h t_h`. -/
def TablesCertifiedR (rr : ℕ → ℝ → ℝ) (α : ℝ) (P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) :
    Prop :=
  ∀ i : Fin d, (i : ℕ) ≠ 0 →
    TapsCertified α P t i (T.tap i) ∧
    ∀ u : ℕ, u < t i →
      OnGridR (P + 2) (T.mu i u) ∧ OnGridR (P + 2) (T.ahat i u) ∧
      |T.mu i u - (max (coeffC0 α (t i) u) (coeffC1 α (t i) u))⁻¹| ≤ gridUnit (P + 2) ∧
      |T.ahat i u - min (coeffC0 α (t i) u) (coeffC1 α (t i) u) /
        max (coeffC0 α (t i) u) (coeffC1 α (t i) u)| ≤ gridUnit (P + 2) ∧
      0 ≤ T.ahat i u ∧
      T.gam i u =
        closureFixedR rr (P + 2) (closurePrec (P + 2) (prefixProd t i) (t i)) (T.ahat i u)
          (prefixProd t i)

/-- `spreadFixed` with rounding `rr`: fixed-point spreading of the axes `h = d, …, 2`. -/
noncomputable def spreadFixedR (rr : ℕ → ℝ → ℝ) (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (V : Idx t → ℂ) : Idx t → ℂ :=
  (spreadOrder d).foldl (fun W i => spreadAxisFixedR rr q t i (T.tap i) W) V

/-- `deconvAxisFixed` with rounding `rr`: one fixed-point deconvolution stage `B_h^{-1}` (cycle
`f_j = j·R/A_h + s`, orientation `c_0 > c_1 ⟺ u < t_h/2`). -/
noncomputable def deconvAxisFixedR (rr : ℕ → ℝ → ℝ) (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (i : Fin d) (Y : Fin (totalLen t) → ℂ) : Fin (totalLen t) → ℂ :=
  fun f =>
    let w := aliasStep t i
    let j0 := (f : ℕ) / w
    let u := (((encFreq t).symm f i : Fin (t i)) : ℕ)
    cycSweepR rr (decide (2 * u < t i)) q (T.mu i u) (T.ahat i u) (T.gam i u) (prefixProd t i)
      (fun j => Y (shiftFin f (((j : ℤ) - (j0 : ℤ)) * (w : ℤ)))) j0

/-- `deconvFixed` with rounding `rr`: the solvers `B_2^{-1}, …, B_d^{-1}` in this order. -/
noncomputable def deconvFixedR (rr : ℕ → ℝ → ℝ) (q : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (Y : Fin (totalLen t) → ℂ) : Fin (totalLen t) → ℂ :=
  (deconvOrder d).foldl (fun Z i => deconvAxisFixedR rr q t T i Z) Y

/-- `spreadStage` with rounding `rr`: the completed spread array `U` (end of step (2)). -/
noncomputable def spreadStageR (rr : ℕ → ℝ → ℝ) (P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (x : Fin (totalLen t) → ℂ) : Idx t → ℂ :=
  spreadFixedR rr (P + 2) t T (fun j => preScaled t x (encIn t j))

/-- `bridgePre` with rounding `rr`: the value `S·Ẑ` before the final rounding. -/
noncomputable def bridgePreR (rr : ℕ → ℝ → ℝ) (P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (run : (Idx t → ℂ) → (Idx t → ℂ)) (x : Fin (totalLen t) → ℂ) : Fin (totalLen t) → ℂ :=
  fun f => (2 : ℂ) ^ preScaleExp t x *
    deconvFixedR rr (P + 2) t T (fun f' => run (spreadStageR rr P t T x) ((encFreq t).symm f')) f

/-- `bridgeFixed` with rounding `rr`: the fixed-point bridge `F̂_R x`
(Section 4.4 (`sec:bridge-alg`)), returned on the `(p+2)`-grid by the final rounding `crnd rr (p + 2)`. -/
noncomputable def bridgeFixedR (rr : ℕ → ℝ → ℝ) (p P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t)
    (run : (Idx t → ℂ) → (Idx t → ℂ)) (x : Fin (totalLen t) → ℂ) : Fin (totalLen t) → ℂ :=
  fun f => crnd rr (p + 2) (bridgePreR rr P t T run x f)

end SubNLogN.Math.Bridge
