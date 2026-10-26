import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint

set_option backward.isDefEq.respectTransparency false

/-!
# Uniform 8-Stack Binary Machine (`Turing.FinTM2`) Primitives, Encodings & Routing (`IntMul.TMPrimitives`)

This module formalizes the uniform 8-stack binary machine (`Turing.FinTM2`) infrastructure,
single-bit arithmetic and stream-routing machines, fixed-width word and batch encodings, matrix
transposition and odd-stride column routing specifications, and per-level schedule record encodings
(see Section 3.2 (`sec:prelim-model`), Section 3.4 (`sec:routing`), Section 8 (`sec:lean`), and
Appendix A.2 (`app:tape-schedule`)):

1. **`Turing.FinTM2` Uniform 8-Stack Infrastructure, Finite-Control Capacity Bounds & Step-by-Step
   Uniform Arithmetic Primitives**:
   - An 8-stack binary machine (`Turing.FinTM2`) framework over `TapeIdx = Fin 8` (`kIO = 0` as
     primary input/output stack, `kSched = 1` as schedule stack, and `kWork0..kWork5` as work/merge
     stacks) with stack alphabet `Bool` (8 binary stacks), so `encodeInputBits n A B` and
     `encodeNatBits (2 * n) (A * B)` reside on stack `k₀ = kIO` via `Turing.initList`/`Turing.haltList`.
   - Formal uniformity predicate `IsUniformFinTM2 tm maxLabels maxStates maxAlpha` (`|Λ| ≤ maxLabels`,
     `|σ| ≤ maxStates`, `∀ k, |Γ k| ≤ maxAlpha`) and machine-checked finite-control and alphabet
     capacity bounds (`cannot_store_n_bits_in_uniform_state` and `uniform_push_range_card_le`)
     proving that no uniform `FinTM2` can injectively encode an $N$-bit input buffer into
     `Option tm.Λ × tm.σ` once `(maxLabels + 1) * maxStates < 2 ^ N`.
   - Constant-size 3-bit hardware register `UniformReg` (`bitA, bitB, carry : Bool`,
     `Fintype.card UniformReg = 8`) and **uniform** single-bit step-by-step `FinTM2`
     machines (not indexed by $n$ or word width $w$):
     - `tmUniformRevCopy : Turing.FinTM2` (`|Λ| = 2`, `|σ| = 8`, `|Γ k| = 2`): reverses any
       `xs : List Bool` from `kIO` onto `kWork0` in `2 * xs.length + 1` `TM2.step` transitions.
     - `tmUniformIdCopy : Turing.FinTM2` (`|Λ| = 4`, `|σ| = 8`, `|Γ k| = 2`): copies any
       `xs : List Bool` from `kIO` via `kWork0` preserving order in `4 * xs.length + 2` `TM2.step` transitions.
     - `tmUniformDeinterleave : Turing.FinTM2` (`|Λ| = 4`, `|σ| = 8`, `|Γ k| = 2`): splits any
       even-length paired bitstream on `kIO` into reversed even/odd streams on `kWork0`/`kWork1`
       in `2 * pairs.length + 1` `TM2.step` transitions.
     - `tmUniformRippleAdd : Turing.FinTM2` (`|Λ| = 6`, `|σ| = 8`, `|Γ k| = 2`): pops two $w$-bit
       operands `encodeNatBits w A` (`kWork0`) and `encodeNatBits w B` (`kWork1`) 1 bit per step,
       computes 1-bit full-adder sum/carry (`fullAdderSum`, `fullAdderCarry`) on `UniformReg`, pushes onto
       `kWork2`, and reverses onto `kIO` to produce `encodeNatBits (w + 1) (A + B)` in `5 * w + 5`
       `TM2.step` transitions for all $w \in \mathbb{N}$ and $A, B < 2^w$.
     - `tmUniformRippleSub : Turing.FinTM2` (`|Λ| = 5`, `|σ| = 8`, `|Γ k| = 2`): pops two $w$-bit
       operands `encodeNatBits w A` (`kWork0`) and `encodeNatBits w B` (`kWork1`) 1 bit per step,
       computes 1-bit full-subtractor difference/borrow (`fullSubDiff`, `fullSubBorrow`) on `UniformReg`,
       pushes onto `kWork2`, and reverses onto `kIO` to produce `encodeNatBits w (A - B)` in
       `5 * w + 2` `TM2.step` transitions for all $w \in \mathbb{N}$ and $B \le A < 2^w$.
     - `tmUniformButterflyAddSub : Turing.FinTM2` (`|Λ| = 9`, `|σ| = 16`, `|Γ k| = 2`): pops two
       $w$-bit operands `encodeNatBits w A` (`kWork0`) and `encodeNatBits w B` (`kWork1`) 1 bit per
       step, simultaneously computes 1-bit full-adder sum/carry and full-subtractor difference/borrow
       on `ButterflyReg`, and outputs both `encodeNatBits (w + 1) (A + B)` on `kIO` and
       `encodeNatBits w (A - B)` on `kWork0` in `8 * w + 6` `TM2.step` transitions for all
       $w \in \mathbb{N}$ and $B \le A < 2^w$.
     - `tmUniformBitMulAdd : Turing.FinTM2` (`|Λ| = 7`, `|σ| = 16`, `|Γ k| = 2`): pops one control
       multiplier bit `mBit` (`kIO`) and two $w$-bit streams (`kWork0`, `kWork1`) 1 bit per step,
       computes `encodeNatBits (w + 1) (acc + if mBit then B else 0)` on `kIO`
       in `5 * w + 6` `TM2.step` transitions for all $w \in \mathbb{N}$ and `acc, B < 2^w`.
     - `tmUniformCondSubStep : Turing.FinTM2` (`|Λ| = 8`, `|σ| = 16`, `|Γ k| = 2`): realizes the
       conditional subtract-mux step of $w$-bit restoring division and square root,
       streaming $w$-bit `R` (`kWork0`) and `D` (`kWork1`) in Pass 1 and multiplexing `R - D` vs.
       `R` onto `kIO` (`encodeNatBits w (if D ≤ R then R - D else R)`) while emitting the quotient/root
       bit `[decide (D ≤ R)]` onto `kWork0` in `7 * w + 3 = \Theta(w)` `TM2.step` transitions.
     - `tmUniformInterleave : Turing.FinTM2` (`|Λ| = 6`, `|σ| = 8`, `|Γ k| = 2`): realizes the
       inverse of `tmUniformDeinterleave`, interleaving two bitstreams of length $m$ on
       `kWork0` and `kWork1` into `flattenBitPairs ps` on `kIO` in `8 * m + 2 = \Theta(m)`
       `TM2.step` transitions.

2. **Word / Batch Stack Layouts & Round-Trip Lemmas (Section 3.2 (`sec:prelim-model`))**:
   - Fixed-width signed word encoding (`encodeSignedWord`, `decodeSignedWord`) and fixed-point
     complex word encoding (`encodeFixedComplex`, `decodeFixedComplex`) with exact round-trip
     theorems `decodeSignedWord_encodeSignedWord` and `decodeFixedComplex_encodeFixedComplex`
     derived from `FitsSignedWord` and `WordWidthBounds`.
   - Batch and subproblem-major bit-stream layouts (`batchWords`, `encodeBatchWords`,
     `decodeBatchWords`, `ofBatch`, `toBatch`, `subproblemMajorWords`) and round-trip theorems
     (`decodeBatchWords_encodeBatchWords`, `subproblemMajorWords_toBatch_ofBatch`,
     `batch_toSubproblemMajorWords_ofSubproblemMajorWords`,
     `decodeSubproblemMajorWords_subproblemMajorWords`).

3. **Out-of-Place Matrix Transpose & Odd-Stride Column Routing (Section 3.4 (`sec:routing`),
   Lemma 3.3 (`lem:routing`), Proposition 4.1 (`thm:twisted`), and Theorem 4.2 (`thm:poisson`))**:
   - Out-of-place matrix transposition (`transposeMatrix`) between $t_1 \times r$ and $r \times t_1$
     word matrices with exact functional specification `transposeMatrix_spec`, involution
     `transposeMatrix_transposeMatrix`, and coordinate-key injectivity `transposeKey_injective`.
   - Odd-stride column gather/scatter and routing (`oddStrideGather`, `oddStrideScatter`,
     `oddShiftGather`, `oddColKeyMinusInv`, `oddColScatter`, `oddColGather`) for
     $(j_1 + k_2 t_1) \bmod R$, $(u_1 + (2 u_2 + 1) t_1) \bmod R$, and Step 2d column scatter/gather
     $Y_{(2 u_2 - 1) v_1 \bmod t_1, u_2} = \hat{q}_{v_1, u_2}$ with exact inverse and round-trip
     theorems (`oddColGather_oddColScatter`, `oddColScatter_oddColGather`,
     `oddStrideGather_oddStrideScatter`, `oddStrideScatter_oddStrideGather`).

4. **Multi-Level Schedule Encoding Helpers (`LevelScheduleEntry`, `buildLevelScheduleEntry`,
   `encodeLevelScheduleEntry`, `decodeLevelScheduleEntry`, schedule (34) (`eq:cert-sched`))**:
   - Complete per-level schedule record `LevelScheduleEntry` containing all 11 level-$\ell$
     parameters (`ell`, `K_ell`, `R_ell`, `p_ell`, `k1_ell`, `k2_ell`, `t1_ell`, `r_ell`,
     `pWork_ell`, `pChild_ell`, `qChild_ell`) constructed purely from `(n, ell)` via `cSpec n`
     (`buildLevelScheduleEntry`).
   - Fixed-width binary encoding `encodeLevelScheduleEntry` and decoder `decodeLevelScheduleEntry`
     with exact round-trip theorems `decodeLevelScheduleEntry_encodeLevelScheduleEntry` and
     `decodeLevelScheduleEntry_encodeLevelScheduleEntry_build`.
-/

namespace IntMul

open Turing

universe u

/-! ## 1. `Turing.FinTM2` 8-Stack Infrastructure & Composable Step Bounds -/

/-- Dependent coercion allowing `Turing.EvalsTo f a b` to appear directly as the body of a `Prop`
existential while remaining Mathlib's constructive `Type` structure. -/
instance instCoeDepEvalsToProp {σ : Type u} (f : σ → Option σ) (a : σ) (b : Option σ) :
    CoeDep Type (Turing.EvalsTo f a b) Prop where
  coe := Nonempty (Turing.EvalsTo f a b)

/-- Dependent coercion allowing `Turing.EvalsToInTime f a b m` to appear directly in statements of
the form `∃ t ≤ bound, Turing.EvalsToInTime f a b t` while remaining Mathlib's constructive
`Turing.EvalsToInTime` type (see Section 8 (`sec:lean`)). -/
instance instCoeDepEvalsToInTimeProp {σ : Type u} (f : σ → Option σ) (a : σ) (b : Option σ)
    (m : ℕ) : CoeDep Type (Turing.EvalsToInTime f a b m) Prop where
  coe := Nonempty (Turing.EvalsToInTime f a b m)

/-- Dependent coercion allowing `Turing.TM2Outputs tm l l'` to be used as a `Prop`. -/
instance instCoeDepTM2OutputsProp (tm : Turing.FinTM2) (l : List (tm.Γ tm.k₀))
    (l' : Option (List (tm.Γ tm.k₁))) :
    CoeDep Type (Turing.TM2Outputs tm l l') Prop where
  coe := Nonempty (Turing.TM2Outputs tm l l')

/-- Dependent coercion allowing `Turing.TM2OutputsInTime tm l l' m` to be used as a `Prop`. -/
instance instCoeDepTM2OutputsInTimeProp (tm : Turing.FinTM2) (l : List (tm.Γ tm.k₀))
    (l' : Option (List (tm.Γ tm.k₁))) (m : ℕ) :
    CoeDep Type (Turing.TM2OutputsInTime tm l l' m) Prop where
  coe := Nonempty (Turing.TM2OutputsInTime tm l l' m)

/-- Monotonicity of `Turing.EvalsToInTime` in the time bound `m₁ ≤ m₂`. -/
def EvalsToInTime.mono {σ : Type u} {f : σ → Option σ} {a : σ} {b : Option σ} {m₁ m₂ : ℕ}
    (h : Turing.EvalsToInTime f a b m₁) (hm : m₁ ≤ m₂) :
    Turing.EvalsToInTime f a b m₂ where
  steps := h.steps
  evals_in_steps := h.evals_in_steps
  steps_le_m := le_trans h.steps_le_m hm

/-- Single-step evaluation `f a = b` runs in at most `1` step. -/
def EvalsToInTime.step_one {σ : Type u} {f : σ → Option σ} {a : σ} {b : Option σ}
    (h : f a = b) : Turing.EvalsToInTime f a b 1 where
  steps := 1
  evals_in_steps := h
  steps_le_m := le_rfl

/-- Prepending a single deterministic step `f a = some b` to a run `EvalsToInTime f b c m` yields a
run in `m + 1` steps. -/
def EvalsToInTime.of_step {σ : Type u} {f : σ → Option σ} {a b : σ} {c : Option σ} {m : ℕ}
    (h1 : f a = some b) (h2 : Turing.EvalsToInTime f b c m) :
    Turing.EvalsToInTime f a c (m + 1) :=
  StateTransition.EvalsToInTime.trans f 1 m a b c (EvalsToInTime.step_one h1) h2

/-- Sequential composition of `Turing.EvalsToInTime` with natural left-to-right bound `m₁ + m₂`. -/
def EvalsToInTime.trans' {σ : Type u} {f : σ → Option σ} {m₁ m₂ : ℕ} {a b : σ} {c : Option σ}
    (h₁ : Turing.EvalsToInTime f a (some b) m₁) (h₂ : Turing.EvalsToInTime f b c m₂) :
    Turing.EvalsToInTime f a c (m₁ + m₂) :=
  EvalsToInTime.mono (StateTransition.EvalsToInTime.trans f m₁ m₂ a b c h₁ h₂) (by omega)

/-- Existential reflexivity for `EvalsToInTime` in `0` steps. -/
theorem evalsToInTime_refl_exists {σ : Type u} (f : σ → Option σ) (a : σ) :
    ∃ t ≤ 0, Turing.EvalsToInTime f a (some a) t :=
  ⟨0, le_rfl, ⟨StateTransition.EvalsToInTime.refl f a⟩⟩

/-- Existential single-step evaluation in `≤ 1` step. -/
theorem evalsToInTime_step_one_exists {σ : Type u} {f : σ → Option σ} {a : σ} {b : Option σ}
    (h : f a = b) :
    ∃ t ≤ 1, Turing.EvalsToInTime f a b t :=
  ⟨1, le_rfl, ⟨EvalsToInTime.step_one h⟩⟩

/-- Existential sequential composition of `EvalsToInTime` bounds. -/
theorem evalsToInTime_trans_exists {σ : Type u} {f : σ → Option σ} {a b : σ} {c : Option σ}
    {b₁ b₂ : ℕ}
    (h₁ : ∃ t₁ ≤ b₁, Turing.EvalsToInTime f a (some b) t₁)
    (h₂ : ∃ t₂ ≤ b₂, Turing.EvalsToInTime f b c t₂) :
    ∃ t ≤ b₁ + b₂, Turing.EvalsToInTime f a c t := by
  rcases h₁ with ⟨t₁, ht₁, ⟨e₁⟩⟩
  rcases h₂ with ⟨t₂, ht₂, ⟨e₂⟩⟩
  exact ⟨t₁ + t₂, Nat.add_le_add ht₁ ht₂, ⟨EvalsToInTime.trans' e₁ e₂⟩⟩

/-- Existential monotonicity of `EvalsToInTime` step bounds. -/
theorem evalsToInTime_mono_exists {σ : Type u} {f : σ → Option σ} {a : σ} {b : Option σ}
    {b₁ b₂ : ℕ} (h : ∃ t ≤ b₁, Turing.EvalsToInTime f a b t) (hb : b₁ ≤ b₂) :
    ∃ t ≤ b₂, Turing.EvalsToInTime f a b t := by
  rcases h with ⟨t, ht, ⟨e⟩⟩
  exact ⟨t, le_trans ht hb, ⟨e⟩⟩

/-- Number of stacks in the 8-stack binary machine (`Turing.FinTM2`) architecture. -/
abbrev NumTapes : ℕ := 8

/-- Finite index type of the 8 binary stacks in the `Turing.FinTM2` architecture. -/
abbrev TapeIdx : Type := Fin NumTapes

/-- Primary input/output stack `k₀ = k₁ = 0`. -/
def kIO : TapeIdx := ⟨0, by decide⟩

/-- Dedicated schedule/parameter stack `kSched = 1`. -/
def kSched : TapeIdx := ⟨1, by decide⟩

/-- Work stack 0 (`kWork0 = 2`). -/
def kWork0 : TapeIdx := ⟨2, by decide⟩

/-- Work stack 1 (`kWork1 = 3`). -/
def kWork1 : TapeIdx := ⟨3, by decide⟩

/-- Work stack 2 (`kWork2 = 4`). -/
def kWork2 : TapeIdx := ⟨4, by decide⟩

/-- Work stack 3 (`kWork3 = 5`). -/
def kWork3 : TapeIdx := ⟨5, by decide⟩

/-- Work stack 4 (`kWork4 = 6`). -/
def kWork4 : TapeIdx := ⟨6, by decide⟩

/-- Work stack 5 (`kWork5 = 7`). -/
def kWork5 : TapeIdx := ⟨7, by decide⟩

/-- Every stack in the 8-stack binary machine (`Turing.FinTM2`) uses the binary alphabet `Bool`, so
`encodeInputBits n A B : List Bool` and `encodeNatBits (2 * n) (A * B) : List Bool` have type
`List (BitTapeAlphabet kIO)` definitionally. -/
abbrev BitTapeAlphabet (_ : TapeIdx) : Type := Bool

/-- Construct a `Turing.FinTM2` over the 8-stack binary alphabet `BitTapeAlphabet` with
`k₀ = kIO` and `k₁ = kIO`. -/
def mkBitFinTM2 (Λ : Type) [Fintype Λ] (main : Λ) (σ : Type) [Fintype σ] (initialState : σ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ) : Turing.FinTM2 where
  K := TapeIdx
  k₀ := kIO
  k₁ := kIO
  Γ := BitTapeAlphabet
  Λ := Λ
  main := main
  σ := σ
  initialState := initialState
  m := m

/-- Canonical single-stack assignment with `s` on `kIO` and `[]` on all other stacks. -/
def singleTapeStk (s : List Bool) (k : TapeIdx) : List (BitTapeAlphabet k) :=
  if k = kIO then s else []

@[simp]
theorem singleTapeStk_kIO (s : List Bool) : singleTapeStk s kIO = s := by
  simp [singleTapeStk]

@[simp]
theorem singleTapeStk_ne (s : List Bool) {k : TapeIdx} (hk : k ≠ kIO) :
    singleTapeStk s k = [] := by
  simp [singleTapeStk, hk]

/-- Characterization of `Turing.initList` for any `mkBitFinTM2` machine. -/
theorem initList_mkBitFinTM2 {Λ : Type} [Fintype Λ] (main : Λ) {σ : Type} [Fintype σ]
    (initialState : σ) (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ) (s : List Bool) :
    Turing.initList (mkBitFinTM2 Λ main σ initialState m) s =
      ⟨some main, initialState, singleTapeStk s⟩ :=
  rfl

/-- Characterization of `Turing.haltList` for any `mkBitFinTM2` machine. -/
theorem haltList_mkBitFinTM2 {Λ : Type} [Fintype Λ] (main : Λ) {σ : Type} [Fintype σ]
    (initialState : σ) (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ) (s : List Bool) :
    Turing.haltList (mkBitFinTM2 Λ main σ initialState m) s =
      ⟨none, initialState, singleTapeStk s⟩ :=
  rfl

/-- Canonical two-stack assignment with `s` on `kIO`, `ws` on `kWork0`, and `[]` on all other
stacks. -/
def twoTapeStk (s ws : List Bool) (k : TapeIdx) : List (BitTapeAlphabet k) :=
  if k = kIO then s else if k = kWork0 then ws else []

@[simp]
theorem twoTapeStk_nil (s : List Bool) : twoTapeStk s [] = singleTapeStk s := by
  funext k
  by_cases hk : k = kIO
  · subst hk; simp [twoTapeStk, singleTapeStk]
  · simp [twoTapeStk, singleTapeStk, hk]

@[simp]
theorem twoTapeStk_kIO (s ws : List Bool) : twoTapeStk s ws kIO = s := by
  simp [twoTapeStk]

@[simp]
theorem twoTapeStk_kWork0 (s ws : List Bool) : twoTapeStk s ws kWork0 = ws := by
  have hne : kWork0 ≠ kIO := by decide
  simp [twoTapeStk, hne]

@[simp]
theorem update_twoTapeStk_kIO (s s' ws : List Bool) :
    Function.update (twoTapeStk s ws) kIO s' = twoTapeStk s' ws := by
  funext k
  by_cases hk : k = kIO
  · subst hk; simp [twoTapeStk]
  · simp [twoTapeStk, hk]

@[simp]
theorem update_twoTapeStk_kWork0 (s ws ws' : List Bool) :
    Function.update (twoTapeStk s ws) kWork0 ws' = twoTapeStk s ws' := by
  have hne : kWork0 ≠ kIO := by decide
  funext k
  by_cases hk0 : k = kWork0
  · subst hk0; simp [twoTapeStk, hne]
  · by_cases hk : k = kIO
    · subst hk; simp [twoTapeStk, hk0]
    · simp [twoTapeStk, hk, hk0]

@[simp]
theorem update_singleTapeStk_kIO (s s' : List Bool) :
    Function.update (singleTapeStk s) kIO s' = singleTapeStk s' := by
  rw [← twoTapeStk_nil s, ← twoTapeStk_nil s', update_twoTapeStk_kIO]

/-- Concrete 1-step identity `FinTM2` machine over the 8-stack binary architecture. -/
def tmIdentity : Turing.FinTM2 :=
  mkBitFinTM2 Unit () Unit () (fun _ => Turing.TM2.Stmt.halt)

/-- `tmIdentity` halts in `1` step with the input bit-list unchanged on `kIO`. -/
def tmIdentity_evalsToInTime_concrete (s : List Bool) :
    Turing.EvalsToInTime tmIdentity.step
      (Turing.initList tmIdentity s) (some (Turing.haltList tmIdentity s)) 1 :=
  EvalsToInTime.step_one rfl

theorem tmIdentity_evalsToInTime (s : List Bool) :
    ∃ t ≤ 1, Turing.EvalsToInTime tmIdentity.step
      (Turing.initList tmIdentity s) (some (Turing.haltList tmIdentity s)) t :=
  ⟨1, le_rfl, ⟨tmIdentity_evalsToInTime_concrete s⟩⟩

/-! ### 1.2 Strict Uniformity Predicate & Finite-Control Capacity Bounds (Section 8 (`sec:lean`)) -/

instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
instance (tm : Turing.FinTM2) : Fintype (tm.Γ tm.k₀) := tm.Γk₀Fin

/-- A `Turing.FinTM2` machine satisfies `IsUniformFinTM2 tm maxLabels maxStates maxAlpha` when its
control label type `Λ`, internal register type `σ`, stack index set `K` (`|K| ≤ 8`), input/output
stack alphabet `Γ k₀`, and **all** work-stack alphabets `Γ k` (`∀ k : tm.K`) have finite cardinalities
bounded by constants `(8, maxLabels, maxStates, maxAlpha)` completely independent of any runtime
input length `n` (Section 8 (`sec:lean`)). -/
def IsUniformFinTM2 (tm : Turing.FinTM2) (maxLabels maxStates maxAlpha : ℕ) : Prop :=
  Fintype.card tm.Λ ≤ maxLabels ∧
  Fintype.card tm.σ ≤ maxStates ∧
  Fintype.card (tm.Γ tm.k₀) ≤ maxAlpha ∧
  Fintype.card tm.K ≤ 8 ∧
  ∃ inst : ∀ k : tm.K, Fintype (tm.Γ k),
    ∀ k : tm.K, @Fintype.card (tm.Γ k) (inst k) ≤ maxAlpha

/-- Helper lemma establishing `IsUniformFinTM2` for any 8-stack binary `mkBitFinTM2`
machine (`|K| = 8`, `∀ k, |Γ k| = 2`). -/
theorem isUniformFinTM2_mkBitFinTM2 {Λ : Type} [Fintype Λ] (main : Λ) {σ : Type} [Fintype σ]
    (initialState : σ) (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ)
    {maxLabels maxStates maxAlpha : ℕ}
    (hΛ : Fintype.card Λ ≤ maxLabels)
    (hσ : Fintype.card σ ≤ maxStates)
    (hΓ : 2 ≤ maxAlpha) :
    IsUniformFinTM2 (mkBitFinTM2 Λ main σ initialState m) maxLabels maxStates maxAlpha := by
  have hBool : Fintype.card Bool = 2 := rfl
  have hTape : Fintype.card TapeIdx = 8 := rfl
  refine ⟨hΛ, hσ, ?_, ?_, ⟨fun _ => (inferInstance : Fintype Bool), fun _ => ?_⟩⟩
  · change Fintype.card Bool ≤ maxAlpha; omega
  · change Fintype.card TapeIdx ≤ 8; omega
  · change Fintype.card Bool ≤ maxAlpha; omega

/-- **Finite-Control State-Space Capacity Bound (`cannot_store_n_bits_in_uniform_state`)**:
Any `FinTM2` machine `tm` satisfying `IsUniformFinTM2 tm maxLabels maxStates maxAlpha` has at most
`(maxLabels + 1) * maxStates` combined `(lbl, var)` control-and-register states (`Option tm.Λ × tm.σ`).
Consequently, whenever `(maxLabels + 1) * maxStates < 2 ^ N`, there does not exist any injective
encoding `enc : (Fin N → Bool) → Option tm.Λ × tm.σ` of `N`-bit buffers into the finite control of
`tm`. In particular, a uniform `FinTM2` machine can never buffer an $N$-bit input inside `Λ` or `σ`
for $N > \log_2((\text{maxLabels} + 1) \cdot \text{maxStates})$. -/
theorem cannot_store_n_bits_in_uniform_state (tm : Turing.FinTM2)
    (maxLabels maxStates maxAlpha N : ℕ)
    (hunif : IsUniformFinTM2 tm maxLabels maxStates maxAlpha)
    (hN : (maxLabels + 1) * maxStates < 2 ^ N) :
    ¬ ∃ enc : (Fin N → Bool) → Option tm.Λ × tm.σ, Function.Injective enc := by
  rintro ⟨enc, henc⟩
  have hcard_dom : Fintype.card (Fin N → Bool) = 2 ^ N := by simp
  have hcard_cod : Fintype.card (Option tm.Λ × tm.σ) ≤ (maxLabels + 1) * maxStates := by
    rw [Fintype.card_prod, Fintype.card_option]
    exact Nat.mul_le_mul (Nat.add_le_add_right hunif.1 1) hunif.2.1
  have hle := Fintype.card_le_of_injective enc henc
  omega

/-- **Work-Stack Alphabet Capacity Bound (`cannot_store_n_bits_in_any_uniform_tape_cell`)**:
In any `FinTM2` machine `tm` satisfying `IsUniformFinTM2 tm maxLabels maxStates maxAlpha`, every
stack `k : tm.K` (including every work stack `k ≠ k₀`) has alphabet cardinality at most `maxAlpha`,
so no single stack symbol on any stack `k` can injectively encode an `N`-bit buffer whenever
`maxAlpha < 2 ^ N`. -/
theorem cannot_store_n_bits_in_any_uniform_tape_cell (tm : Turing.FinTM2)
    (maxLabels maxStates maxAlpha N : ℕ)
    (hunif : IsUniformFinTM2 tm maxLabels maxStates maxAlpha)
    (hN : maxAlpha < 2 ^ N) (k : tm.K) :
    ¬ ∃ enc : (Fin N → Bool) → tm.Γ k, Function.Injective enc := by
  rintro ⟨enc, henc⟩
  rcases hunif.2.2.2.2 with ⟨inst, hcard⟩
  letI : Fintype (tm.Γ k) := inst k
  have hcard_dom : Fintype.card (Fin N → Bool) = 2 ^ N := by simp
  have hle := Fintype.card_le_of_injective enc henc
  have hk := hcard k
  omega

/-- **Stack-Count Uniformity Bound (`cannot_use_n_tapes_in_uniform_machine`)**:
Any `FinTM2` machine `tm` satisfying `IsUniformFinTM2 tm maxLabels maxStates maxAlpha` has at most
8 stacks (`Fintype.card tm.K ≤ 8`), so it cannot index $N > 8$ distinct stacks. -/
theorem cannot_use_n_tapes_in_uniform_machine (tm : Turing.FinTM2)
    (maxLabels maxStates maxAlpha N : ℕ)
    (hunif : IsUniformFinTM2 tm maxLabels maxStates maxAlpha)
    (hN : 8 < N) :
    ¬ ∃ enc : Fin N → tm.K, Function.Injective enc := by
  rintro ⟨enc, henc⟩
  have hcard_dom : Fintype.card (Fin N) = N := Fintype.card_fin N
  have hle := Fintype.card_le_of_injective enc henc
  have hK := hunif.2.2.2.1
  omega

/-- **Finite-Register `Stmt.push` Range Bound (`uniform_push_range_card_le`)**:
In any `FinTM2` machine `tm` satisfying `IsUniformFinTM2 tm maxLabels maxStates maxAlpha`, any
pure function `f : tm.σ → β` of the internal register `σ` (such as a `Stmt.push k f` payload or a
`Stmt.load f` transition) has finite image cardinality at most `maxStates`, regardless of the
contents or length of the stacks. -/
theorem uniform_push_range_card_le (tm : Turing.FinTM2)
    (maxLabels maxStates maxAlpha : ℕ)
    (hunif : IsUniformFinTM2 tm maxLabels maxStates maxAlpha)
    {β : Type*} [DecidableEq β] (f : tm.σ → β) :
    (Finset.univ.image f).card ≤ maxStates :=
  le_trans Finset.card_image_le (by simpa using hunif.2.1)

/-- `tmIdentity` is a uniform `FinTM2` machine with `|Λ| = 1`, `|σ| = 1`, `|K| = 8`, and
`∀ k, |Γ k| = 2`. -/
theorem isUniformFinTM2_tmIdentity : IsUniformFinTM2 tmIdentity 1 1 2 :=
  isUniformFinTM2_mkBitFinTM2 () () _ (by decide) (by decide) (by decide)

/-! ### 1.3 8-Stack Helpers & $O(1)$ Register `UniformReg` -/

/-- Canonical three-stack assignment with `s` on `kIO`, `w0` on `kWork0`, `w1` on `kWork1`,
and `[]` on all other stacks. -/
def threeTapeWorkStk (s w0 w1 : List Bool) (k : TapeIdx) : List (BitTapeAlphabet k) :=
  if k = kIO then s else if k = kWork0 then w0 else if k = kWork1 then w1 else []

@[simp]
theorem threeTapeWorkStk_nil (s w0 : List Bool) :
    threeTapeWorkStk s w0 [] = twoTapeStk s w0 := by
  funext k
  by_cases hk : k = kIO
  · subst hk; simp [threeTapeWorkStk, twoTapeStk]
  · by_cases hk0 : k = kWork0
    · subst hk0; simp [threeTapeWorkStk, twoTapeStk, hk]
    · simp [threeTapeWorkStk, twoTapeStk, hk, hk0]

@[simp]
theorem threeTapeWorkStk_kIO (s w0 w1 : List Bool) :
    threeTapeWorkStk s w0 w1 kIO = s := by
  simp [threeTapeWorkStk]

@[simp]
theorem threeTapeWorkStk_kWork0 (s w0 w1 : List Bool) :
    threeTapeWorkStk s w0 w1 kWork0 = w0 := by
  have h1 : kWork0 ≠ kIO := by decide
  simp [threeTapeWorkStk, h1]

@[simp]
theorem threeTapeWorkStk_kWork1 (s w0 w1 : List Bool) :
    threeTapeWorkStk s w0 w1 kWork1 = w1 := by
  have h1 : kWork1 ≠ kIO := by decide
  have h2 : kWork1 ≠ kWork0 := by decide
  simp [threeTapeWorkStk, h1, h2]

@[simp]
theorem update_threeTapeWorkStk_kIO (s s' w0 w1 : List Bool) :
    Function.update (threeTapeWorkStk s w0 w1) kIO s' = threeTapeWorkStk s' w0 w1 := by
  funext k
  by_cases hk : k = kIO
  · subst hk; simp [threeTapeWorkStk]
  · simp [threeTapeWorkStk, hk]

@[simp]
theorem update_threeTapeWorkStk_kWork0 (s w0 w0' w1 : List Bool) :
    Function.update (threeTapeWorkStk s w0 w1) kWork0 w0' = threeTapeWorkStk s w0' w1 := by
  have h1 : kWork0 ≠ kIO := by decide
  funext k
  by_cases hk0 : k = kWork0
  · subst hk0; simp [threeTapeWorkStk, h1]
  · by_cases hk : k = kIO
    · subst hk; simp [threeTapeWorkStk, hk0]
    · simp [threeTapeWorkStk, hk, hk0]

@[simp]
theorem update_threeTapeWorkStk_kWork1 (s w0 w1 w1' : List Bool) :
    Function.update (threeTapeWorkStk s w0 w1) kWork1 w1' = threeTapeWorkStk s w0 w1' := by
  have h1 : kWork1 ≠ kIO := by decide
  have h2 : kWork1 ≠ kWork0 := by decide
  funext k
  by_cases hk1 : k = kWork1
  · subst hk1; simp [threeTapeWorkStk, h1, h2]
  · by_cases hk : k = kIO
    · subst hk; simp [threeTapeWorkStk, hk1]
    · by_cases hk0 : k = kWork0
      · subst hk0; simp [threeTapeWorkStk, hk, hk1]
      · simp [threeTapeWorkStk, hk, hk0, hk1]

/-- Canonical four-stack assignment with `s` on `kIO`, `w0` on `kWork0`, `w1` on `kWork1`,
`w2` on `kWork2`, and `[]` on all other stacks. -/
def fourTapeWorkStk (s w0 w1 w2 : List Bool) (k : TapeIdx) : List (BitTapeAlphabet k) :=
  if k = kIO then s else if k = kWork0 then w0 else if k = kWork1 then w1
  else if k = kWork2 then w2 else []

@[simp]
theorem fourTapeWorkStk_nil (s w0 w1 : List Bool) :
    fourTapeWorkStk s w0 w1 [] = threeTapeWorkStk s w0 w1 := by
  funext k
  by_cases hk : k = kIO
  · subst hk; simp [fourTapeWorkStk, threeTapeWorkStk]
  · by_cases hk0 : k = kWork0
    · subst hk0; simp [fourTapeWorkStk, threeTapeWorkStk, hk]
    · by_cases hk1 : k = kWork1
      · subst hk1; simp [fourTapeWorkStk, threeTapeWorkStk, hk, hk0]
      · simp [fourTapeWorkStk, threeTapeWorkStk, hk, hk0, hk1]

@[simp]
theorem fourTapeWorkStk_kIO (s w0 w1 w2 : List Bool) :
    fourTapeWorkStk s w0 w1 w2 kIO = s := by
  simp [fourTapeWorkStk]

@[simp]
theorem fourTapeWorkStk_kWork0 (s w0 w1 w2 : List Bool) :
    fourTapeWorkStk s w0 w1 w2 kWork0 = w0 := by
  have h1 : kWork0 ≠ kIO := by decide
  simp [fourTapeWorkStk, h1]

@[simp]
theorem fourTapeWorkStk_kWork1 (s w0 w1 w2 : List Bool) :
    fourTapeWorkStk s w0 w1 w2 kWork1 = w1 := by
  have h1 : kWork1 ≠ kIO := by decide
  have h2 : kWork1 ≠ kWork0 := by decide
  simp [fourTapeWorkStk, h1, h2]

@[simp]
theorem fourTapeWorkStk_kWork2 (s w0 w1 w2 : List Bool) :
    fourTapeWorkStk s w0 w1 w2 kWork2 = w2 := by
  have h1 : kWork2 ≠ kIO := by decide
  have h2 : kWork2 ≠ kWork0 := by decide
  have h3 : kWork2 ≠ kWork1 := by decide
  simp [fourTapeWorkStk, h1, h2, h3]

@[simp]
theorem update_fourTapeWorkStk_kIO (s s' w0 w1 w2 : List Bool) :
    Function.update (fourTapeWorkStk s w0 w1 w2) kIO s' = fourTapeWorkStk s' w0 w1 w2 := by
  funext k
  by_cases hk : k = kIO
  · subst hk; simp [fourTapeWorkStk]
  · simp [fourTapeWorkStk, hk]

@[simp]
theorem update_fourTapeWorkStk_kWork0 (s w0 w0' w1 w2 : List Bool) :
    Function.update (fourTapeWorkStk s w0 w1 w2) kWork0 w0' = fourTapeWorkStk s w0' w1 w2 := by
  have h1 : kWork0 ≠ kIO := by decide
  funext k
  by_cases hk0 : k = kWork0
  · subst hk0; simp [fourTapeWorkStk, h1]
  · by_cases hk : k = kIO
    · subst hk; simp [fourTapeWorkStk, hk0]
    · simp [fourTapeWorkStk, hk, hk0]

@[simp]
theorem update_fourTapeWorkStk_kWork1 (s w0 w1 w1' w2 : List Bool) :
    Function.update (fourTapeWorkStk s w0 w1 w2) kWork1 w1' = fourTapeWorkStk s w0 w1' w2 := by
  have h1 : kWork1 ≠ kIO := by decide
  have h2 : kWork1 ≠ kWork0 := by decide
  funext k
  by_cases hk1 : k = kWork1
  · subst hk1; simp [fourTapeWorkStk, h1, h2]
  · by_cases hk : k = kIO
    · subst hk; simp [fourTapeWorkStk, hk1]
    · by_cases hk0 : k = kWork0
      · subst hk0; simp [fourTapeWorkStk, hk, hk1]
      · simp [fourTapeWorkStk, hk, hk0, hk1]

@[simp]
theorem update_fourTapeWorkStk_kWork2 (s w0 w1 w2 w2' : List Bool) :
    Function.update (fourTapeWorkStk s w0 w1 w2) kWork2 w2' = fourTapeWorkStk s w0 w1 w2' := by
  have h1 : kWork2 ≠ kIO := by decide
  have h2 : kWork2 ≠ kWork0 := by decide
  have h3 : kWork2 ≠ kWork1 := by decide
  funext k
  by_cases hk2 : k = kWork2
  · subst hk2; simp [fourTapeWorkStk, h1, h2, h3]
  · by_cases hk : k = kIO
    · subst hk; simp [fourTapeWorkStk, hk2]
    · by_cases hk0 : k = kWork0
      · subst hk0; simp [fourTapeWorkStk, hk, hk2]
      · by_cases hk1 : k = kWork1
        · subst hk1; simp [fourTapeWorkStk, hk, hk0, hk2]
        · simp [fourTapeWorkStk, hk, hk0, hk1, hk2]

/-- Strictly uniform 3-bit internal register (`Fintype.card UniformReg = 8`) holding at most two
operand bits `bitA`, `bitB` and a 1-bit `carry` flag. -/
@[ext]
structure UniformReg where
  /-- First 1-bit operand latch. -/
  bitA : Bool := false
  /-- Second 1-bit operand latch. -/
  bitB : Bool := false
  /-- 1-bit carry/eof latch. -/
  carry : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Explicit equivalence `UniformReg ≃ Bool × Bool × Bool` witnessing `Fintype.card UniformReg = 8`. -/
def uniformRegEquiv : UniformReg ≃ Bool × Bool × Bool where
  toFun r := (r.bitA, r.bitB, r.carry)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv r := by cases r; rfl
  right_inv t := by rcases t with ⟨a, b, c⟩; rfl

instance : Fintype UniformReg :=
  Fintype.ofEquiv (Bool × Bool × Bool) uniformRegEquiv.symm

@[simp]
theorem card_uniformReg : Fintype.card UniformReg = 8 := by decide

@[simp]
theorem uniformReg_default_bitA : (default : UniformReg).bitA = false := rfl

@[simp]
theorem uniformReg_default_bitB : (default : UniformReg).bitB = false := rfl

@[simp]
theorem uniformReg_default_carry : (default : UniformReg).carry = false := rfl

/-! ### 1.4 Uniform Reverse-Copy & Order-Preserving Copy Machines (`tmUniformRevCopy`, `tmUniformIdCopy`) -/

/-- Control labels for the uniform single-machine reverse-copy `FinTM2` (`|Λ| = 2`). -/
inductive RevCopyLabel : Type
  | popIO
  | pushWork
  deriving DecidableEq, Repr, Inhabited

/-- Explicit equivalence `RevCopyLabel ≃ Bool` witnessing `Fintype.card RevCopyLabel = 2`. -/
def revCopyLabelEquiv : RevCopyLabel ≃ Bool where
  toFun
    | .popIO => false
    | .pushWork => true
  invFun
    | false => .popIO
    | true => .pushWork
  left_inv x := by cases x <;> rfl
  right_inv b := by cases b <;> rfl

instance : Fintype RevCopyLabel :=
  Fintype.ofEquiv Bool revCopyLabelEquiv.symm

@[simp]
theorem card_revCopyLabel : Fintype.card RevCopyLabel = 2 := by decide

/-- Single uniform `FinTM2` machine (`|Λ| = 2`, `|σ| = 8`, `|Γ k₀| = 2`, zero length parameters)
that pops any bit list `xs : List Bool` from `kIO` one bit at a time and pushes `xs.reverse` onto
`kWork0`. -/
def tmUniformRevCopy : Turing.FinTM2 :=
  mkBitFinTM2 RevCopyLabel .popIO UniformReg default (fun lbl =>
    match lbl with
    | .popIO =>
      Turing.TM2.Stmt.pop kIO
        (fun _ bOpt =>
          match bOpt with
          | some b => { bitA := b, bitB := false, carry := true }
          | none => default)
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .pushWork))
          Turing.TM2.Stmt.halt)
    | .pushWork =>
      Turing.TM2.Stmt.push kWork0 (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popIO)))

/-- `tmUniformRevCopy` satisfies `IsUniformFinTM2 tmUniformRevCopy 2 8 2`. -/
theorem isUniformFinTM2_tmUniformRevCopy : IsUniformFinTM2 tmUniformRevCopy 2 8 2 :=
  isUniformFinTM2_mkBitFinTM2 _ _ _ (by decide) (by decide) (by decide)

/-- Loop evaluation of `tmUniformRevCopy` transferring `xs` from `kIO` onto `acc` on `kWork0` in
`2 * xs.length + 1` steps. -/
def tmUniformRevCopy_loop_evalsToInTime :
    ∀ (xs acc : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmUniformRevCopy.step
        ⟨some .popIO, r, twoTapeStk xs acc⟩
        (some ⟨none, default, twoTapeStk [] (xs.reverse ++ acc)⟩)
        (2 * xs.length + 1)
  | [], acc, r => by
    refine EvalsToInTime.step_one ?_
    simp [tmUniformRevCopy, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
  | b :: xs, acc, r => by
    have hstep1 : tmUniformRevCopy.step ⟨some .popIO, r, twoTapeStk (b :: xs) acc⟩ =
        some ⟨some .pushWork, { bitA := b, bitB := false, carry := true }, twoTapeStk xs acc⟩ := by
      simp [tmUniformRevCopy, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have hstep2 : tmUniformRevCopy.step
        ⟨some .pushWork, { bitA := b, bitB := false, carry := true }, twoTapeStk xs acc⟩ =
        some ⟨some .popIO, { bitA := b, bitB := false, carry := true },
          twoTapeStk xs (b :: acc)⟩ := by
      simp [tmUniformRevCopy, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have ih := tmUniformRevCopy_loop_evalsToInTime xs (b :: acc)
      { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step hstep1 (EvalsToInTime.of_step hstep2 ih))
      (by simp [List.length_cons]; omega)

/-- Concrete evaluation of the single uniform machine `tmUniformRevCopy` on any input list
`xs : List Bool` in `2 * xs.length + 1` steps. -/
def tmUniformRevCopy_evalsToInTime_concrete (xs : List Bool) :
    Turing.EvalsToInTime tmUniformRevCopy.step
      (Turing.initList tmUniformRevCopy xs)
      (some ⟨none, default, twoTapeStk [] xs.reverse⟩)
      (2 * xs.length + 1) := by
  have hinit : Turing.initList tmUniformRevCopy xs =
      ⟨some .popIO, default, twoTapeStk xs []⟩ := by
    rw [twoTapeStk_nil]
    rfl
  rw [hinit, ← List.append_nil xs.reverse]
  exact tmUniformRevCopy_loop_evalsToInTime xs [] default

/-- Existential step bound for `tmUniformRevCopy` on any input list `xs : List Bool`. -/
theorem tmUniformRevCopy_evalsToInTime (xs : List Bool) :
    ∃ t ≤ 2 * xs.length + 1,
      Turing.EvalsToInTime tmUniformRevCopy.step
        (Turing.initList tmUniformRevCopy xs)
        (some ⟨none, default, twoTapeStk [] xs.reverse⟩) t :=
  ⟨_, le_rfl, ⟨tmUniformRevCopy_evalsToInTime_concrete xs⟩⟩

/-- Control labels for the uniform single-machine order-preserving copy `FinTM2` (`|Λ| = 4`). -/
inductive IdCopyLabel : Type
  | popIO
  | pushWork
  | popWork
  | pushIO
  deriving DecidableEq, Repr, Inhabited

/-- Explicit equivalence `IdCopyLabel ≃ Bool × Bool` witnessing `Fintype.card IdCopyLabel = 4`. -/
def idCopyLabelEquiv : IdCopyLabel ≃ Bool × Bool where
  toFun
    | .popIO => (false, false)
    | .pushWork => (false, true)
    | .popWork => (true, false)
    | .pushIO => (true, true)
  invFun
    | (false, false) => .popIO
    | (false, true) => .pushWork
    | (true, false) => .popWork
    | (true, true) => .pushIO
  left_inv x := by cases x <;> rfl
  right_inv p := by rcases p with ⟨_ | _, _ | _⟩ <;> rfl

instance : Fintype IdCopyLabel :=
  Fintype.ofEquiv (Bool × Bool) idCopyLabelEquiv.symm

@[simp]
theorem card_idCopyLabel : Fintype.card IdCopyLabel = 4 := by decide

/-- Single uniform `FinTM2` machine (`|Λ| = 4`, `|σ| = 8`, `|Γ k₀| = 2`, zero length parameters)
that streams any bit list `xs : List Bool` from `kIO` to `kWork0` (reversing it) and streams it
back from `kWork0` to `kIO` (restoring the original order `xs`) in `4 * xs.length + 2` steps. -/
def tmUniformIdCopy : Turing.FinTM2 :=
  mkBitFinTM2 IdCopyLabel .popIO UniformReg default (fun lbl =>
    match lbl with
    | .popIO =>
      Turing.TM2.Stmt.pop kIO
        (fun _ bOpt =>
          match bOpt with
          | some b => { bitA := b, bitB := false, carry := true }
          | none => default)
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .pushWork))
          (Turing.TM2.Stmt.goto (fun _ => .popWork)))
    | .pushWork =>
      Turing.TM2.Stmt.push kWork0 (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popIO))
    | .popWork =>
      Turing.TM2.Stmt.pop kWork0
        (fun _ bOpt =>
          match bOpt with
          | some b => { bitA := b, bitB := false, carry := true }
          | none => default)
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .pushIO))
          Turing.TM2.Stmt.halt)
    | .pushIO =>
      Turing.TM2.Stmt.push kIO (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popWork)))

/-- `tmUniformIdCopy` satisfies `IsUniformFinTM2 tmUniformIdCopy 4 8 2`. -/
theorem isUniformFinTM2_tmUniformIdCopy : IsUniformFinTM2 tmUniformIdCopy 4 8 2 :=
  isUniformFinTM2_mkBitFinTM2 _ _ _ (by decide) (by decide) (by decide)

/-- First pass of `tmUniformIdCopy`: pops `xs` from `kIO` onto `acc` on `kWork0` in
`2 * xs.length + 1` steps, transitioning to `.popWork`. -/
def tmUniformIdCopy_pass1_evalsToInTime :
    ∀ (xs acc : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmUniformIdCopy.step
        ⟨some .popIO, r, twoTapeStk xs acc⟩
        (some ⟨some .popWork, default, twoTapeStk [] (xs.reverse ++ acc)⟩)
        (2 * xs.length + 1)
  | [], acc, r => by
    refine EvalsToInTime.step_one ?_
    simp [tmUniformIdCopy, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
  | b :: xs, acc, r => by
    have hstep1 : tmUniformIdCopy.step ⟨some .popIO, r, twoTapeStk (b :: xs) acc⟩ =
        some ⟨some .pushWork, { bitA := b, bitB := false, carry := true }, twoTapeStk xs acc⟩ := by
      simp [tmUniformIdCopy, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have hstep2 : tmUniformIdCopy.step
        ⟨some .pushWork, { bitA := b, bitB := false, carry := true }, twoTapeStk xs acc⟩ =
        some ⟨some .popIO, { bitA := b, bitB := false, carry := true },
          twoTapeStk xs (b :: acc)⟩ := by
      simp [tmUniformIdCopy, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have ih := tmUniformIdCopy_pass1_evalsToInTime xs (b :: acc)
      { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step hstep1 (EvalsToInTime.of_step hstep2 ih))
      (by simp [List.length_cons]; omega)

/-- Second pass of `tmUniformIdCopy`: pops `ws` from `kWork0` onto `acc` on `kIO` in
`2 * ws.length + 1` steps and halts. -/
def tmUniformIdCopy_pass2_evalsToInTime :
    ∀ (ws acc : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmUniformIdCopy.step
        ⟨some .popWork, r, twoTapeStk acc ws⟩
        (some ⟨none, default, twoTapeStk (ws.reverse ++ acc) []⟩)
        (2 * ws.length + 1)
  | [], acc, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformIdCopy, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux, twoTapeStk_kWork0, update_twoTapeStk_kWork0, uniformReg_default_carry,
      List.head?_nil, List.tail_nil, List.reverse_nil, List.nil_append, cond_false]
  | b :: ws, acc, r => by
    have hstep1 : tmUniformIdCopy.step ⟨some .popWork, r, twoTapeStk acc (b :: ws)⟩ =
        some ⟨some .pushIO, { bitA := b, bitB := false, carry := true }, twoTapeStk acc ws⟩ := by
      simp [tmUniformIdCopy, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have hstep2 : tmUniformIdCopy.step
        ⟨some .pushIO, { bitA := b, bitB := false, carry := true }, twoTapeStk acc ws⟩ =
        some ⟨some .popWork, { bitA := b, bitB := false, carry := true },
          twoTapeStk (b :: acc) ws⟩ := by
      simp [tmUniformIdCopy, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have ih := tmUniformIdCopy_pass2_evalsToInTime ws (b :: acc)
      { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step hstep1 (EvalsToInTime.of_step hstep2 ih))
      (by simp [List.length_cons]; omega)

/-- Concrete evaluation of the single uniform machine `tmUniformIdCopy` on any input list
`xs : List Bool` in `4 * xs.length + 2` single-bit steps. -/
def tmUniformIdCopy_evalsToInTime_concrete (xs : List Bool) :
    Turing.EvalsToInTime tmUniformIdCopy.step
      (Turing.initList tmUniformIdCopy xs)
      (some (Turing.haltList tmUniformIdCopy xs))
      (4 * xs.length + 2) := by
  have hinit : Turing.initList tmUniformIdCopy xs =
      ⟨some .popIO, default, twoTapeStk xs []⟩ := by
    rw [twoTapeStk_nil]
    rfl
  have hhalt : Turing.haltList tmUniformIdCopy xs =
      ⟨none, default, twoTapeStk (xs.reverse.reverse ++ []) []⟩ := by
    rw [List.reverse_reverse, List.append_nil, twoTapeStk_nil]
    rfl
  rw [hinit, hhalt]
  have hp1 := tmUniformIdCopy_pass1_evalsToInTime xs [] default
  rw [List.append_nil] at hp1
  have hp2 := tmUniformIdCopy_pass2_evalsToInTime xs.reverse [] default
  rw [List.length_reverse] at hp2
  exact EvalsToInTime.mono (EvalsToInTime.trans' hp1 hp2) (by omega)

/-- Existential step bound for `tmUniformIdCopy` on any input list `xs : List Bool`. -/
theorem tmUniformIdCopy_evalsToInTime (xs : List Bool) :
    ∃ t ≤ 4 * xs.length + 2,
      Turing.EvalsToInTime tmUniformIdCopy.step
        (Turing.initList tmUniformIdCopy xs)
        (some (Turing.haltList tmUniformIdCopy xs)) t :=
  ⟨_, le_rfl, ⟨tmUniformIdCopy_evalsToInTime_concrete xs⟩⟩

/-! ### 1.5 Uniform Stream Deinterleave Machine (`tmUniformDeinterleave`) -/

/-- Control labels for the uniform single-machine deinterleave `FinTM2` (`|Λ| = 4`). -/
inductive DeinterleaveLabel : Type
  | popEven
  | pushEven
  | popOdd
  | pushOdd
  deriving DecidableEq, Repr, Inhabited

/-- Explicit equivalence `DeinterleaveLabel ≃ Bool × Bool` witnessing
`Fintype.card DeinterleaveLabel = 4`. -/
def deinterleaveLabelEquiv : DeinterleaveLabel ≃ Bool × Bool where
  toFun
    | .popEven => (false, false)
    | .pushEven => (false, true)
    | .popOdd => (true, false)
    | .pushOdd => (true, true)
  invFun
    | (false, false) => .popEven
    | (false, true) => .pushEven
    | (true, false) => .popOdd
    | (true, true) => .pushOdd
  left_inv x := by cases x <;> rfl
  right_inv p := by rcases p with ⟨_ | _, _ | _⟩ <;> rfl

instance : Fintype DeinterleaveLabel :=
  Fintype.ofEquiv (Bool × Bool) deinterleaveLabelEquiv.symm

@[simp]
theorem card_deinterleaveLabel : Fintype.card DeinterleaveLabel = 4 := by decide

/-- Single uniform `FinTM2` machine (`|Λ| = 4`, `|σ| = 8`, `|Γ k₀| = 2`, zero length parameters)
that pops alternating even/odd bits from `kIO` one bit at a time, pushing even-indexed bits onto
`kWork0` and odd-indexed bits onto `kWork1`. -/
def tmUniformDeinterleave : Turing.FinTM2 :=
  mkBitFinTM2 DeinterleaveLabel .popEven UniformReg default (fun lbl =>
    match lbl with
    | .popEven =>
      Turing.TM2.Stmt.pop kIO
        (fun _ bOpt =>
          match bOpt with
          | some b => { bitA := b, bitB := false, carry := true }
          | none => default)
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .pushEven))
          Turing.TM2.Stmt.halt)
    | .pushEven =>
      Turing.TM2.Stmt.push kWork0 (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popOdd))
    | .popOdd =>
      Turing.TM2.Stmt.pop kIO
        (fun _ bOpt =>
          match bOpt with
          | some b => { bitA := false, bitB := b, carry := true }
          | none => default)
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .pushOdd))
          Turing.TM2.Stmt.halt)
    | .pushOdd =>
      Turing.TM2.Stmt.push kWork1 (fun r => r.bitB)
        (Turing.TM2.Stmt.goto (fun _ => .popEven)))

/-- `tmUniformDeinterleave` satisfies `IsUniformFinTM2 tmUniformDeinterleave 4 8 2`. -/
theorem isUniformFinTM2_tmUniformDeinterleave : IsUniformFinTM2 tmUniformDeinterleave 4 8 2 :=
  isUniformFinTM2_mkBitFinTM2 _ _ _ (by decide) (by decide) (by decide)

/-- Interleave a list of `(evenBit, oddBit)` pairs into a flat `List Bool`. -/
def flattenBitPairs : List (Bool × Bool) → List Bool
  | [] => []
  | (a, b) :: ps => a :: b :: flattenBitPairs ps

@[simp]
theorem length_flattenBitPairs (ps : List (Bool × Bool)) :
    (flattenBitPairs ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a, b⟩
    simp [flattenBitPairs, ih]
    omega

/-- Loop evaluation of `tmUniformDeinterleave` on `flattenBitPairs ps`, pushing `(ps.map Prod.fst).reverse`
onto `kWork0` and `(ps.map Prod.snd).reverse` onto `kWork1` in `4 * ps.length + 1` steps. -/
def tmUniformDeinterleave_loop_evalsToInTime :
    ∀ (ps : List (Bool × Bool)) (w0 w1 : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmUniformDeinterleave.step
        ⟨some .popEven, r, threeTapeWorkStk (flattenBitPairs ps) w0 w1⟩
        (some ⟨none, default,
          threeTapeWorkStk [] ((ps.map Prod.fst).reverse ++ w0)
            ((ps.map Prod.snd).reverse ++ w1)⟩)
        (4 * ps.length + 1)
  | [], w0, w1, r => by
    refine EvalsToInTime.step_one ?_
    simp [tmUniformDeinterleave, flattenBitPairs, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux]
  | (a, b) :: ps, w0, w1, r => by
    have hstep1 : tmUniformDeinterleave.step
        ⟨some .popEven, r, threeTapeWorkStk (a :: b :: flattenBitPairs ps) w0 w1⟩ =
        some ⟨some .pushEven, { bitA := a, bitB := false, carry := true },
          threeTapeWorkStk (b :: flattenBitPairs ps) w0 w1⟩ := by
      simp [tmUniformDeinterleave, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformDeinterleave.step
        ⟨some .pushEven, { bitA := a, bitB := false, carry := true },
          threeTapeWorkStk (b :: flattenBitPairs ps) w0 w1⟩ =
        some ⟨some .popOdd, { bitA := a, bitB := false, carry := true },
          threeTapeWorkStk (b :: flattenBitPairs ps) (a :: w0) w1⟩ := by
      simp [tmUniformDeinterleave, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep3 : tmUniformDeinterleave.step
        ⟨some .popOdd, { bitA := a, bitB := false, carry := true },
          threeTapeWorkStk (b :: flattenBitPairs ps) (a :: w0) w1⟩ =
        some ⟨some .pushOdd, { bitA := false, bitB := b, carry := true },
          threeTapeWorkStk (flattenBitPairs ps) (a :: w0) w1⟩ := by
      simp [tmUniformDeinterleave, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep4 : tmUniformDeinterleave.step
        ⟨some .pushOdd, { bitA := false, bitB := b, carry := true },
          threeTapeWorkStk (flattenBitPairs ps) (a :: w0) w1⟩ =
        some ⟨some .popEven, { bitA := false, bitB := b, carry := true },
          threeTapeWorkStk (flattenBitPairs ps) (a :: w0) (b :: w1)⟩ := by
      simp [tmUniformDeinterleave, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformDeinterleave_loop_evalsToInTime ps (a :: w0) (b :: w1)
      { bitA := false, bitB := b, carry := true }
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono
      (EvalsToInTime.of_step hstep1
        (EvalsToInTime.of_step hstep2
          (EvalsToInTime.of_step hstep3
            (EvalsToInTime.of_step hstep4 ih))))
      (by simp [List.length_cons]; omega)

/-- Concrete evaluation of `tmUniformDeinterleave` on `flattenBitPairs ps` in `4 * ps.length + 1`
steps. -/
def tmUniformDeinterleave_evalsToInTime_concrete (ps : List (Bool × Bool)) :
    Turing.EvalsToInTime tmUniformDeinterleave.step
      (Turing.initList tmUniformDeinterleave (flattenBitPairs ps))
      (some ⟨none, default,
        threeTapeWorkStk [] (ps.map Prod.fst).reverse (ps.map Prod.snd).reverse⟩)
      (4 * ps.length + 1) := by
  have hinit : Turing.initList tmUniformDeinterleave (flattenBitPairs ps) =
      ⟨some .popEven, default, threeTapeWorkStk (flattenBitPairs ps) [] []⟩ := by
    rw [threeTapeWorkStk_nil, twoTapeStk_nil]
    rfl
  rw [hinit, ← List.append_nil (ps.map Prod.fst).reverse,
    ← List.append_nil (ps.map Prod.snd).reverse]
  exact tmUniformDeinterleave_loop_evalsToInTime ps [] [] default

/-- Existential step bound for `tmUniformDeinterleave`. -/
theorem tmUniformDeinterleave_evalsToInTime (ps : List (Bool × Bool)) :
    ∃ t ≤ 4 * ps.length + 1,
      Turing.EvalsToInTime tmUniformDeinterleave.step
        (Turing.initList tmUniformDeinterleave (flattenBitPairs ps))
        (some ⟨none, default,
          threeTapeWorkStk [] (ps.map Prod.fst).reverse (ps.map Prod.snd).reverse⟩) t :=
  ⟨_, le_rfl, ⟨tmUniformDeinterleave_evalsToInTime_concrete ps⟩⟩

/-! ### 1.6 Uniform 1-Bit Ripple-Carry Adder Machine (`tmUniformRippleAdd`) -/

/-- Pure 1-bit full-adder sum bit `a ^^ b ^^ c`. -/
def fullAdderSum (a b c : Bool) : Bool :=
  xor (xor a b) c

/-- Pure 1-bit full-adder carry-out bit `(a && b) || (a && c) || (b && c)`. -/
def fullAdderCarry (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

/-- Fundamental 1-bit full-adder arithmetic identity:
`a.toNat + b.toNat + c.toNat = (fullAdderSum a b c).toNat + 2 * (fullAdderCarry a b c).toNat`. -/
theorem fullAdder_toNat_eq (a b c : Bool) :
    (fullAdderSum a b c).toNat + 2 * (fullAdderCarry a b c).toNat =
      a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

/-- Pure bit-by-bit ripple-carry addition of two equal-length LSB-first bitstreams `xs` and `ys`
with carry-in `c`, accumulating the reversed sum bits onto `acc` (followed by the final carry-out
bit when the streams end). -/
def rippleAddRevLoop : List Bool → List Bool → Bool → List Bool → List Bool
  | [], _, c, acc => c :: acc
  | a :: xs, [], c, acc =>
    rippleAddRevLoop xs [] (fullAdderCarry a false c) (fullAdderSum a false c :: acc)
  | a :: xs, b :: ys, c, acc =>
    rippleAddRevLoop xs ys (fullAdderCarry a b c) (fullAdderSum a b c :: acc)

/-- Control labels for the uniform single-machine ripple-carry adder `FinTM2` (`|Λ| = 6`). -/
inductive RippleAddLabel : Type
  | popA
  | popB
  | pushSumRev
  | pushCarryRev
  | popSumRev
  | pushIO
  deriving DecidableEq, Repr, Inhabited

/-- Explicit equivalence `RippleAddLabel ≃ Fin 6` witnessing `Fintype.card RippleAddLabel = 6`. -/
def rippleAddLabelEquiv : RippleAddLabel ≃ Fin 6 where
  toFun
    | .popA => ⟨0, by decide⟩
    | .popB => ⟨1, by decide⟩
    | .pushSumRev => ⟨2, by decide⟩
    | .pushCarryRev => ⟨3, by decide⟩
    | .popSumRev => ⟨4, by decide⟩
    | .pushIO => ⟨5, by decide⟩
  invFun
    | ⟨0, _⟩ => .popA
    | ⟨1, _⟩ => .popB
    | ⟨2, _⟩ => .pushSumRev
    | ⟨3, _⟩ => .pushCarryRev
    | ⟨4, _⟩ => .popSumRev
    | ⟨_ + 5, _⟩ => .pushIO
  left_inv x := by cases x <;> rfl
  right_inv i := by
    rcases i with ⟨_ | _ | _ | _ | _ | _ | n, hi⟩ <;> try rfl
    omega

instance : Fintype RippleAddLabel :=
  Fintype.ofEquiv (Fin 6) rippleAddLabelEquiv.symm

@[simp]
theorem card_rippleAddLabel : Fintype.card RippleAddLabel = 6 := by decide

/-- Single uniform `FinTM2` machine (`|Λ| = 6`, `|σ| = 8`, `|Γ k₀| = 2`, zero length parameters)
that pops two LSB-first bitstreams `xs` (from `kWork0`) and `ys` (from `kWork1`) one bit at a time,
computes the 1-bit full-adder sum `fullAdderSum` and carry `fullAdderCarry` on `UniformReg`, pushes
the reversed sum bits (plus final carry-out bit) onto `kWork2`, and streams them back onto `kIO` in
LSB-first order. -/
def tmUniformRippleAdd : Turing.FinTM2 :=
  mkBitFinTM2 RippleAddLabel .popA UniformReg default (fun lbl =>
    match lbl with
    | .popA =>
      Turing.TM2.Stmt.pop kWork0
        (fun r bOpt =>
          match bOpt with
          | some a => { r with bitA := a, bitB := true }
          | none => { r with bitA := false, bitB := false })
        (Turing.TM2.Stmt.branch (fun r => r.bitB)
          (Turing.TM2.Stmt.goto (fun _ => .popB))
          (Turing.TM2.Stmt.goto (fun _ => .pushCarryRev)))
    | .popB =>
      Turing.TM2.Stmt.pop kWork1
        (fun r bOpt =>
          let b := bOpt.getD false
          { bitA := fullAdderSum r.bitA b r.carry
            bitB := false
            carry := fullAdderCarry r.bitA b r.carry })
        (Turing.TM2.Stmt.goto (fun _ => .pushSumRev))
    | .pushSumRev =>
      Turing.TM2.Stmt.push kWork2 (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popA))
    | .pushCarryRev =>
      Turing.TM2.Stmt.push kWork2 (fun r => r.carry)
        (Turing.TM2.Stmt.goto (fun _ => .popSumRev))
    | .popSumRev =>
      Turing.TM2.Stmt.pop kWork2
        (fun _ bOpt =>
          match bOpt with
          | some b => { bitA := b, bitB := false, carry := true }
          | none => default)
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .pushIO))
          Turing.TM2.Stmt.halt)
    | .pushIO =>
      Turing.TM2.Stmt.push kIO (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popSumRev)))

/-- `tmUniformRippleAdd` satisfies `IsUniformFinTM2 tmUniformRippleAdd 6 8 2`. -/
theorem isUniformFinTM2_tmUniformRippleAdd : IsUniformFinTM2 tmUniformRippleAdd 6 8 2 :=
  isUniformFinTM2_mkBitFinTM2 _ _ _ (by decide) (by decide) (by decide)

/-- First pass of `tmUniformRippleAdd`: pops equal-length `xs` (`kWork0`) and `ys` (`kWork1`) one
bit at a time, pushing the reversed sum bits and final carry onto `kWork2` in `3 * xs.length + 2`
steps and transitioning to `.popSumRev`. -/
def tmUniformRippleAdd_pass1_evalsToInTime :
    ∀ (xs ys acc : List Bool) (_hlen : xs.length = ys.length) (r : UniformReg),
      Turing.EvalsToInTime tmUniformRippleAdd.step
        ⟨some .popA, r, fourTapeWorkStk [] xs ys acc⟩
        (some ⟨some .popSumRev, { bitA := false, bitB := false, carry := (rippleAddRevLoop xs ys r.carry acc).headD false },
          fourTapeWorkStk [] [] [] (rippleAddRevLoop xs ys r.carry acc)⟩)
        (3 * xs.length + 2)
  | [], [], acc, _, r => by
    rcases r with ⟨bitA, bitB, carry⟩
    have hstep1 : tmUniformRippleAdd.step
        ⟨some .popA, ⟨bitA, bitB, carry⟩, fourTapeWorkStk [] [] [] acc⟩ =
        some ⟨some .pushCarryRev, ⟨false, false, carry⟩, fourTapeWorkStk [] [] [] acc⟩ := by
      simp [tmUniformRippleAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformRippleAdd.step
        ⟨some .pushCarryRev, ⟨false, false, carry⟩, fourTapeWorkStk [] [] [] acc⟩ =
        some ⟨some .popSumRev, ⟨false, false, carry⟩, fourTapeWorkStk [] [] [] (carry :: acc)⟩ := by
      simp [tmUniformRippleAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    exact EvalsToInTime.of_step hstep1 (EvalsToInTime.step_one hstep2)
  | a :: xs, b :: ys, acc, hlen, r => by
    rcases r with ⟨bitA, bitB, carry⟩
    have hlen' : xs.length = ys.length := by simpa using hlen
    have hstep1 : tmUniformRippleAdd.step
        ⟨some .popA, ⟨bitA, bitB, carry⟩, fourTapeWorkStk [] (a :: xs) (b :: ys) acc⟩ =
        some ⟨some .popB, ⟨a, true, carry⟩, fourTapeWorkStk [] xs (b :: ys) acc⟩ := by
      simp [tmUniformRippleAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformRippleAdd.step
        ⟨some .popB, ⟨a, true, carry⟩, fourTapeWorkStk [] xs (b :: ys) acc⟩ =
        some ⟨some .pushSumRev,
          ⟨fullAdderSum a b carry, false, fullAdderCarry a b carry⟩,
          fourTapeWorkStk [] xs ys acc⟩ := by
      simp [tmUniformRippleAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep3 : tmUniformRippleAdd.step
        ⟨some .pushSumRev,
          ⟨fullAdderSum a b carry, false, fullAdderCarry a b carry⟩,
          fourTapeWorkStk [] xs ys acc⟩ =
        some ⟨some .popA,
          ⟨fullAdderSum a b carry, false, fullAdderCarry a b carry⟩,
          fourTapeWorkStk [] xs ys (fullAdderSum a b carry :: acc)⟩ := by
      simp [tmUniformRippleAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformRippleAdd_pass1_evalsToInTime xs ys (fullAdderSum a b carry :: acc) hlen'
      ⟨fullAdderSum a b carry, false, fullAdderCarry a b carry⟩
    dsimp only [rippleAddRevLoop]
    exact EvalsToInTime.mono
      (EvalsToInTime.of_step hstep1 (EvalsToInTime.of_step hstep2 (EvalsToInTime.of_step hstep3 ih)))
      (by simp [List.length_cons]; omega)

/-- Second pass of `tmUniformRippleAdd`: pops `ws` from `kWork2` and pushes `ws.reverse` onto `kIO`
in `2 * ws.length + 1` steps, halting with `default` register state. -/
def tmUniformRippleAdd_pass2_evalsToInTime :
    ∀ (ws acc : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmUniformRippleAdd.step
        ⟨some .popSumRev, r, fourTapeWorkStk acc [] [] ws⟩
        (some ⟨none, default, fourTapeWorkStk (ws.reverse ++ acc) [] [] []⟩)
        (2 * ws.length + 1)
  | [], acc, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformRippleAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux, fourTapeWorkStk_kWork2, update_fourTapeWorkStk_kWork2,
      uniformReg_default_carry, List.head?_nil, List.tail_nil, List.reverse_nil,
      List.nil_append, cond_false]
  | b :: ws, acc, r => by
    have hstep1 : tmUniformRippleAdd.step
        ⟨some .popSumRev, r, fourTapeWorkStk acc [] [] (b :: ws)⟩ =
        some ⟨some .pushIO, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk acc [] [] ws⟩ := by
      simp [tmUniformRippleAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformRippleAdd.step
        ⟨some .pushIO, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk acc [] [] ws⟩ =
        some ⟨some .popSumRev, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk (b :: acc) [] [] ws⟩ := by
      simp [tmUniformRippleAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformRippleAdd_pass2_evalsToInTime ws (b :: acc)
      { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step hstep1 (EvalsToInTime.of_step hstep2 ih))
      (by simp [List.length_cons]; omega)

@[simp]
theorem length_rippleAddRevLoop :
    ∀ (xs ys : List Bool) (_hlen : xs.length = ys.length) (c : Bool) (acc : List Bool),
      (rippleAddRevLoop xs ys c acc).length = xs.length + acc.length + 1
  | [], [], _, c, acc => by simp [rippleAddRevLoop]
  | a :: xs, b :: ys, hlen, c, acc => by
    have hlen' : xs.length = ys.length := by simpa using hlen
    simp only [rippleAddRevLoop, length_rippleAddRevLoop xs ys hlen', List.length_cons]
    omega

/-- Concrete evaluation of the single uniform machine `tmUniformRippleAdd` on any equal-length
operand bitstreams `xs, ys : List Bool` (placed on `kWork0` and `kWork1`) in `5 * xs.length + 5`
steps, writing `(rippleAddRevLoop xs ys false []).reverse` onto `kIO`. -/
def tmUniformRippleAdd_evalsToInTime_concrete (xs ys : List Bool) (hlen : xs.length = ys.length) :
    Turing.EvalsToInTime tmUniformRippleAdd.step
      ⟨some .popA, default, threeTapeWorkStk [] xs ys⟩
      (some (Turing.haltList tmUniformRippleAdd (rippleAddRevLoop xs ys false []).reverse))
      (5 * xs.length + 5) := by
  have hinit : (⟨some .popA, default, threeTapeWorkStk [] xs ys⟩ : tmUniformRippleAdd.Cfg) =
      ⟨some .popA, default, fourTapeWorkStk [] xs ys []⟩ := by
    rw [fourTapeWorkStk_nil]
  have hhalt : Turing.haltList tmUniformRippleAdd (rippleAddRevLoop xs ys false []).reverse =
      ⟨none, default,
        fourTapeWorkStk ((rippleAddRevLoop xs ys false []).reverse ++ []) [] [] []⟩ := by
    rw [List.append_nil, fourTapeWorkStk_nil, threeTapeWorkStk_nil, twoTapeStk_nil]
    rfl
  rw [hinit, hhalt]
  have hp1 := tmUniformRippleAdd_pass1_evalsToInTime xs ys [] hlen default
  have hp2 := tmUniformRippleAdd_pass2_evalsToInTime (rippleAddRevLoop xs ys false []) []
    { bitA := false, bitB := false, carry := (rippleAddRevLoop xs ys false []).headD false }
  have hlen_rev : (rippleAddRevLoop xs ys false []).length = xs.length + 1 := by
    simpa using length_rippleAddRevLoop xs ys hlen false []
  rw [hlen_rev] at hp2
  exact EvalsToInTime.mono (EvalsToInTime.trans' hp1 hp2) (by omega)

/-- Forward LSB-first ripple-carry addition stream corresponding to `(rippleAddRevLoop xs ys c []).reverse`. -/
def rippleAddStream : List Bool → List Bool → Bool → List Bool
  | [], _, c => [c]
  | a :: xs, [], c =>
    fullAdderSum a false c :: rippleAddStream xs [] (fullAdderCarry a false c)
  | a :: xs, b :: ys, c =>
    fullAdderSum a b c :: rippleAddStream xs ys (fullAdderCarry a b c)

/-- Reversing `rippleAddRevLoop xs ys c acc` appends `rippleAddStream xs ys c` to `acc.reverse`. -/
theorem reverse_rippleAddRevLoop :
    ∀ (xs ys : List Bool) (_hlen : xs.length = ys.length) (c : Bool) (acc : List Bool),
      (rippleAddRevLoop xs ys c acc).reverse = acc.reverse ++ rippleAddStream xs ys c
  | [], [], _, c, acc => by
    simp [rippleAddRevLoop, rippleAddStream]
  | a :: xs, b :: ys, hlen, c, acc => by
    have hlen' : xs.length = ys.length := by simpa using hlen
    simp only [rippleAddRevLoop, rippleAddStream,
      reverse_rippleAddRevLoop xs ys hlen' (fullAdderCarry a b c) (fullAdderSum a b c :: acc),
      List.reverse_cons, List.append_assoc, List.singleton_append]

@[simp]
theorem length_rippleAddStream :
    ∀ (xs ys : List Bool) (_hlen : xs.length = ys.length) (c : Bool),
      (rippleAddStream xs ys c).length = xs.length + 1
  | [], [], _, c => by simp [rippleAddStream]
  | a :: xs, b :: ys, hlen, c => by
    have hlen' : xs.length = ys.length := by simpa using hlen
    simp [rippleAddStream, length_rippleAddStream xs ys hlen']

private theorem bif_eq_toNat (b : Bool) : (bif b then 1 else 0) = b.toNat := by
  cases b <;> rfl

/-- Exact arithmetic semantics of `rippleAddStream`: decoding the LSB-first output stream yields
`decodeNatBits xs + decodeNatBits ys + c.toNat`. -/
theorem decodeNatBits_rippleAddStream :
    ∀ (xs ys : List Bool) (_hlen : xs.length = ys.length) (c : Bool),
      decodeNatBits (rippleAddStream xs ys c) =
        decodeNatBits xs + decodeNatBits ys + c.toNat
  | [], [], _, c => by
    simp [rippleAddStream, decodeNatBits, bif_eq_toNat]
  | a :: xs, b :: ys, hlen, c => by
    have hlen' : xs.length = ys.length := by simpa using hlen
    simp only [rippleAddStream, decodeNatBits, decodeNatBits_rippleAddStream xs ys hlen',
      bif_eq_toNat]
    have hfa := fullAdder_toNat_eq a b c
    omega

/-- On `w`-bit encodings `encodeNatBits w A` and `encodeNatBits w B` with `A < 2 ^ w` and
`B < 2 ^ w`, `rippleAddStream` produces `encodeNatBits (w + 1) (A + B)`. -/
@[simp]
theorem rippleAddStream_encodeNatBits (w A B : ℕ) (hA : A < 2 ^ w) (hB : B < 2 ^ w) :
    rippleAddStream (encodeNatBits w A) (encodeNatBits w B) false =
      encodeNatBits (w + 1) (A + B) := by
  have hlen : (encodeNatBits w A).length = (encodeNatBits w B).length := by simp
  have hdec : decodeNatBits (rippleAddStream (encodeNatBits w A) (encodeNatBits w B) false) =
      A + B := by
    rw [decodeNatBits_rippleAddStream _ _ hlen false,
      decodeNatBits_encodeNatBits w A hA, decodeNatBits_encodeNatBits w B hB]
    rfl
  have hout_len : (rippleAddStream (encodeNatBits w A) (encodeNatBits w B) false).length = w + 1 := by
    rw [length_rippleAddStream _ _ hlen false, encodeNatBits_length]
  rw [← hdec, ← hout_len, encodeNatBits_decodeNatBits]

/-- Concrete evaluation of the single uniform machine `tmUniformRippleAdd` on any `w`-bit natural
numbers `A, B < 2 ^ w`, computing `encodeNatBits (w + 1) (A + B)` on `kIO` in `5 * w + 5`
single-bit `FinTM2` steps. -/
def tmUniformRippleAdd_encodeNatBits_evalsToInTime_concrete (w A B : ℕ)
    (hA : A < 2 ^ w) (hB : B < 2 ^ w) :
    Turing.EvalsToInTime tmUniformRippleAdd.step
      ⟨some .popA, default, threeTapeWorkStk [] (encodeNatBits w A) (encodeNatBits w B)⟩
      (some (Turing.haltList tmUniformRippleAdd (encodeNatBits (w + 1) (A + B))))
      (5 * w + 5) := by
  have hlen : (encodeNatBits w A).length = (encodeNatBits w B).length := by simp
  have hrun := tmUniformRippleAdd_evalsToInTime_concrete (encodeNatBits w A) (encodeNatBits w B) hlen
  have hrev : (rippleAddRevLoop (encodeNatBits w A) (encodeNatBits w B) false []).reverse =
      encodeNatBits (w + 1) (A + B) := by
    rw [reverse_rippleAddRevLoop _ _ hlen false [], List.reverse_nil, List.nil_append,
      rippleAddStream_encodeNatBits w A B hA hB]
  rw [hrev, encodeNatBits_length] at hrun
  exact hrun

/-- Unconditional existential step bound and exact functional correctness for the single uniform
machine `tmUniformRippleAdd` on `w`-bit operands `A, B < 2 ^ w`. -/
theorem tmUniformRippleAdd_encodeNatBits_evalsToInTime (w A B : ℕ)
    (hA : A < 2 ^ w) (hB : B < 2 ^ w) :
    ∃ t ≤ 5 * w + 5,
      Turing.EvalsToInTime tmUniformRippleAdd.step
        ⟨some .popA, default, threeTapeWorkStk [] (encodeNatBits w A) (encodeNatBits w B)⟩
        (some (Turing.haltList tmUniformRippleAdd (encodeNatBits (w + 1) (A + B)))) t :=
  ⟨_, le_rfl, ⟨tmUniformRippleAdd_encodeNatBits_evalsToInTime_concrete w A B hA hB⟩⟩

/-! ### 1.7 Uniform 1-Bit Ripple-Borrow Subtractor Machine (`tmUniformRippleSub`) -/

/-- Pure 1-bit full-subtractor difference bit `a ^^ b ^^ borrow`. -/
def fullSubDiff (a b borrow : Bool) : Bool :=
  xor (xor a b) borrow

/-- Pure 1-bit full-subtractor borrow-out bit `(!a && b) || (!a && borrow) || (b && borrow)`. -/
def fullSubBorrow (a b borrow : Bool) : Bool :=
  (!a && b) || (!a && borrow) || (b && borrow)

/-- Fundamental 1-bit full-subtractor arithmetic identity:
`(fullSubDiff a b borrow).toNat + b.toNat + borrow.toNat =
  a.toNat + 2 * (fullSubBorrow a b borrow).toNat`. -/
theorem fullSub_toNat_eq (a b borrow : Bool) :
    (fullSubDiff a b borrow).toNat + b.toNat + borrow.toNat =
      a.toNat + 2 * (fullSubBorrow a b borrow).toNat := by
  cases a <;> cases b <;> cases borrow <;> decide

/-- Pure bit-by-bit ripple-borrow subtraction of two equal-length LSB-first bitstreams `xs` and `ys`
with borrow-in `borrow`, accumulating the reversed difference bits onto `acc`. -/
def rippleSubRevLoop : List Bool → List Bool → Bool → List Bool → List Bool
  | [], _, _, acc => acc
  | a :: xs, [], borrow, acc =>
    rippleSubRevLoop xs [] (fullSubBorrow a false borrow) (fullSubDiff a false borrow :: acc)
  | a :: xs, b :: ys, borrow, acc =>
    rippleSubRevLoop xs ys (fullSubBorrow a b borrow) (fullSubDiff a b borrow :: acc)

/-- Final borrow-out bit after streaming equal-length LSB-first bitstreams `xs` and `ys` with
initial borrow `borrow`. -/
def rippleSubFinalBorrow : List Bool → List Bool → Bool → Bool
  | [], _, borrow => borrow
  | a :: xs, [], borrow => rippleSubFinalBorrow xs [] (fullSubBorrow a false borrow)
  | a :: xs, b :: ys, borrow => rippleSubFinalBorrow xs ys (fullSubBorrow a b borrow)

/-- Control labels for the uniform single-machine ripple-borrow subtractor `FinTM2` (`|Λ| = 5`). -/
inductive RippleSubLabel : Type
  | popA
  | popB
  | pushDiffRev
  | popDiffRev
  | pushIO
  deriving DecidableEq, Repr, Inhabited

/-- Explicit equivalence `RippleSubLabel ≃ Fin 5` witnessing `Fintype.card RippleSubLabel = 5`. -/
def rippleSubLabelEquiv : RippleSubLabel ≃ Fin 5 where
  toFun
    | .popA => ⟨0, by decide⟩
    | .popB => ⟨1, by decide⟩
    | .pushDiffRev => ⟨2, by decide⟩
    | .popDiffRev => ⟨3, by decide⟩
    | .pushIO => ⟨4, by decide⟩
  invFun
    | ⟨0, _⟩ => .popA
    | ⟨1, _⟩ => .popB
    | ⟨2, _⟩ => .pushDiffRev
    | ⟨3, _⟩ => .popDiffRev
    | ⟨_ + 4, _⟩ => .pushIO
  left_inv x := by cases x <;> rfl
  right_inv i := by
    rcases i with ⟨_ | _ | _ | _ | _ | n, hi⟩ <;> try rfl
    omega

instance : Fintype RippleSubLabel :=
  Fintype.ofEquiv (Fin 5) rippleSubLabelEquiv.symm

@[simp]
theorem card_rippleSubLabel : Fintype.card RippleSubLabel = 5 := by decide

/-- Single uniform `FinTM2` machine (`|Λ| = 5`, `|σ| = 8`, `|Γ k₀| = 2`, zero length parameters)
that pops two LSB-first bitstreams `xs` (from `kWork0`) and `ys` (from `kWork1`) one bit at a time,
computes the 1-bit full-subtractor difference `fullSubDiff` and borrow `fullSubBorrow` on `UniformReg`,
pushes the reversed difference bits onto `kWork2`, and streams them back onto `kIO` in LSB-first
order. -/
def tmUniformRippleSub : Turing.FinTM2 :=
  mkBitFinTM2 RippleSubLabel .popA UniformReg default (fun lbl =>
    match lbl with
    | .popA =>
      Turing.TM2.Stmt.pop kWork0
        (fun r bOpt =>
          match bOpt with
          | some a => { r with bitA := a, bitB := true }
          | none => { r with bitA := false, bitB := false })
        (Turing.TM2.Stmt.branch (fun r => r.bitB)
          (Turing.TM2.Stmt.goto (fun _ => .popB))
          (Turing.TM2.Stmt.goto (fun _ => .popDiffRev)))
    | .popB =>
      Turing.TM2.Stmt.pop kWork1
        (fun r bOpt =>
          let b := bOpt.getD false
          { bitA := fullSubDiff r.bitA b r.carry
            bitB := false
            carry := fullSubBorrow r.bitA b r.carry })
        (Turing.TM2.Stmt.goto (fun _ => .pushDiffRev))
    | .pushDiffRev =>
      Turing.TM2.Stmt.push kWork2 (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popA))
    | .popDiffRev =>
      Turing.TM2.Stmt.pop kWork2
        (fun _ bOpt =>
          match bOpt with
          | some b => { bitA := b, bitB := false, carry := true }
          | none => default)
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .pushIO))
          Turing.TM2.Stmt.halt)
    | .pushIO =>
      Turing.TM2.Stmt.push kIO (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popDiffRev)))

/-- `tmUniformRippleSub` satisfies `IsUniformFinTM2 tmUniformRippleSub 5 8 2`. -/
theorem isUniformFinTM2_tmUniformRippleSub : IsUniformFinTM2 tmUniformRippleSub 5 8 2 :=
  isUniformFinTM2_mkBitFinTM2 _ _ _ (by decide) (by decide) (by decide)

/-- First pass of `tmUniformRippleSub`: pops equal-length `xs` (`kWork0`) and `ys` (`kWork1`) one
bit at a time, pushing the reversed difference bits onto `kWork2` in `3 * xs.length + 1` steps and
transitioning to `.popDiffRev`. -/
def tmUniformRippleSub_pass1_evalsToInTime :
    ∀ (xs ys acc : List Bool) (_hlen : xs.length = ys.length) (r : UniformReg),
      Turing.EvalsToInTime tmUniformRippleSub.step
        ⟨some .popA, r, fourTapeWorkStk [] xs ys acc⟩
        (some ⟨some .popDiffRev,
          { bitA := false, bitB := false, carry := rippleSubFinalBorrow xs ys r.carry },
          fourTapeWorkStk [] [] [] (rippleSubRevLoop xs ys r.carry acc)⟩)
        (3 * xs.length + 1)
  | [], [], acc, _, r => by
    rcases r with ⟨bitA, bitB, carry⟩
    refine EvalsToInTime.step_one ?_
    simp [tmUniformRippleSub, rippleSubRevLoop, rippleSubFinalBorrow, mkBitFinTM2,
      Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
  | a :: xs, b :: ys, acc, hlen, r => by
    rcases r with ⟨bitA, bitB, carry⟩
    have hlen' : xs.length = ys.length := by simpa using hlen
    have hstep1 : tmUniformRippleSub.step
        ⟨some .popA, ⟨bitA, bitB, carry⟩, fourTapeWorkStk [] (a :: xs) (b :: ys) acc⟩ =
        some ⟨some .popB, ⟨a, true, carry⟩, fourTapeWorkStk [] xs (b :: ys) acc⟩ := by
      simp [tmUniformRippleSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformRippleSub.step
        ⟨some .popB, ⟨a, true, carry⟩, fourTapeWorkStk [] xs (b :: ys) acc⟩ =
        some ⟨some .pushDiffRev,
          ⟨fullSubDiff a b carry, false, fullSubBorrow a b carry⟩,
          fourTapeWorkStk [] xs ys acc⟩ := by
      simp [tmUniformRippleSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep3 : tmUniformRippleSub.step
        ⟨some .pushDiffRev,
          ⟨fullSubDiff a b carry, false, fullSubBorrow a b carry⟩,
          fourTapeWorkStk [] xs ys acc⟩ =
        some ⟨some .popA,
          ⟨fullSubDiff a b carry, false, fullSubBorrow a b carry⟩,
          fourTapeWorkStk [] xs ys (fullSubDiff a b carry :: acc)⟩ := by
      simp [tmUniformRippleSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformRippleSub_pass1_evalsToInTime xs ys (fullSubDiff a b carry :: acc) hlen'
      ⟨fullSubDiff a b carry, false, fullSubBorrow a b carry⟩
    dsimp only [rippleSubRevLoop, rippleSubFinalBorrow]
    exact EvalsToInTime.mono
      (EvalsToInTime.of_step hstep1 (EvalsToInTime.of_step hstep2 (EvalsToInTime.of_step hstep3 ih)))
      (by simp [List.length_cons]; omega)

/-- Second pass of `tmUniformRippleSub`: pops `ws` from `kWork2` and pushes `ws.reverse` onto `kIO`
in `2 * ws.length + 1` steps, halting with `default` register state. -/
def tmUniformRippleSub_pass2_evalsToInTime :
    ∀ (ws acc : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmUniformRippleSub.step
        ⟨some .popDiffRev, r, fourTapeWorkStk acc [] [] ws⟩
        (some ⟨none, default, fourTapeWorkStk (ws.reverse ++ acc) [] [] []⟩)
        (2 * ws.length + 1)
  | [], acc, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformRippleSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux, fourTapeWorkStk_kWork2, update_fourTapeWorkStk_kWork2,
      uniformReg_default_carry, List.head?_nil, List.tail_nil, List.reverse_nil,
      List.nil_append, cond_false]
  | b :: ws, acc, r => by
    have hstep1 : tmUniformRippleSub.step
        ⟨some .popDiffRev, r, fourTapeWorkStk acc [] [] (b :: ws)⟩ =
        some ⟨some .pushIO, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk acc [] [] ws⟩ := by
      simp [tmUniformRippleSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformRippleSub.step
        ⟨some .pushIO, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk acc [] [] ws⟩ =
        some ⟨some .popDiffRev, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk (b :: acc) [] [] ws⟩ := by
      simp [tmUniformRippleSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformRippleSub_pass2_evalsToInTime ws (b :: acc)
      { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step hstep1 (EvalsToInTime.of_step hstep2 ih))
      (by simp [List.length_cons]; omega)

@[simp]
theorem length_rippleSubRevLoop :
    ∀ (xs ys : List Bool) (_hlen : xs.length = ys.length) (borrow : Bool) (acc : List Bool),
      (rippleSubRevLoop xs ys borrow acc).length = xs.length + acc.length
  | [], [], _, _, acc => by simp [rippleSubRevLoop]
  | a :: xs, b :: ys, hlen, borrow, acc => by
    have hlen' : xs.length = ys.length := by simpa using hlen
    simp only [rippleSubRevLoop, length_rippleSubRevLoop xs ys hlen', List.length_cons]
    omega

/-- Concrete evaluation of the single uniform machine `tmUniformRippleSub` on any equal-length
operand bitstreams `xs, ys : List Bool` (placed on `kWork0` and `kWork1`) in `5 * xs.length + 2`
steps, writing `(rippleSubRevLoop xs ys false []).reverse` onto `kIO`. -/
def tmUniformRippleSub_evalsToInTime_concrete (xs ys : List Bool) (hlen : xs.length = ys.length) :
    Turing.EvalsToInTime tmUniformRippleSub.step
      ⟨some .popA, default, threeTapeWorkStk [] xs ys⟩
      (some (Turing.haltList tmUniformRippleSub (rippleSubRevLoop xs ys false []).reverse))
      (5 * xs.length + 2) := by
  have hinit : (⟨some .popA, default, threeTapeWorkStk [] xs ys⟩ : tmUniformRippleSub.Cfg) =
      ⟨some .popA, default, fourTapeWorkStk [] xs ys []⟩ := by
    rw [fourTapeWorkStk_nil]
  have hhalt : Turing.haltList tmUniformRippleSub (rippleSubRevLoop xs ys false []).reverse =
      ⟨none, default,
        fourTapeWorkStk ((rippleSubRevLoop xs ys false []).reverse ++ []) [] [] []⟩ := by
    rw [List.append_nil, fourTapeWorkStk_nil, threeTapeWorkStk_nil, twoTapeStk_nil]
    rfl
  rw [hinit, hhalt]
  have hp1 := tmUniformRippleSub_pass1_evalsToInTime xs ys [] hlen default
  have hp2 := tmUniformRippleSub_pass2_evalsToInTime (rippleSubRevLoop xs ys false []) []
    { bitA := false, bitB := false, carry := rippleSubFinalBorrow xs ys false }
  have hlen_rev : (rippleSubRevLoop xs ys false []).length = xs.length := by
    simpa using length_rippleSubRevLoop xs ys hlen false []
  rw [hlen_rev] at hp2
  exact EvalsToInTime.mono (EvalsToInTime.trans' hp1 hp2) (by omega)

/-- Forward LSB-first ripple-borrow difference stream corresponding to
`(rippleSubRevLoop xs ys borrow []).reverse`. -/
def rippleSubStream : List Bool → List Bool → Bool → List Bool
  | [], _, _ => []
  | a :: xs, [], borrow =>
    fullSubDiff a false borrow :: rippleSubStream xs [] (fullSubBorrow a false borrow)
  | a :: xs, b :: ys, borrow =>
    fullSubDiff a b borrow :: rippleSubStream xs ys (fullSubBorrow a b borrow)

/-- Reversing `rippleSubRevLoop xs ys borrow acc` appends `rippleSubStream xs ys borrow` to
`acc.reverse`. -/
theorem reverse_rippleSubRevLoop :
    ∀ (xs ys : List Bool) (_hlen : xs.length = ys.length) (borrow : Bool) (acc : List Bool),
      (rippleSubRevLoop xs ys borrow acc).reverse = acc.reverse ++ rippleSubStream xs ys borrow
  | [], [], _, _, acc => by
    simp [rippleSubRevLoop, rippleSubStream]
  | a :: xs, b :: ys, hlen, borrow, acc => by
    have hlen' : xs.length = ys.length := by simpa using hlen
    simp only [rippleSubRevLoop, rippleSubStream,
      reverse_rippleSubRevLoop xs ys hlen' (fullSubBorrow a b borrow) (fullSubDiff a b borrow :: acc),
      List.reverse_cons, List.append_assoc, List.singleton_append]

@[simp]
theorem length_rippleSubStream :
    ∀ (xs ys : List Bool) (_hlen : xs.length = ys.length) (borrow : Bool),
      (rippleSubStream xs ys borrow).length = xs.length
  | [], [], _, _ => by simp [rippleSubStream]
  | a :: xs, b :: ys, hlen, borrow => by
    have hlen' : xs.length = ys.length := by simpa using hlen
    simp [rippleSubStream, length_rippleSubStream xs ys hlen']

/-- Exact arithmetic semantics of `rippleSubStream` and `rippleSubFinalBorrow`:
`decodeNatBits (rippleSubStream xs ys borrow) + decodeNatBits ys + borrow.toNat =
  decodeNatBits xs + 2 ^ xs.length * (rippleSubFinalBorrow xs ys borrow).toNat`. -/
theorem decodeNatBits_rippleSubStream :
    ∀ (xs ys : List Bool) (_hlen : xs.length = ys.length) (borrow : Bool),
      decodeNatBits (rippleSubStream xs ys borrow) + decodeNatBits ys + borrow.toNat =
        decodeNatBits xs + 2 ^ xs.length * (rippleSubFinalBorrow xs ys borrow).toNat
  | [], [], _, borrow => by
    simp [rippleSubStream, rippleSubFinalBorrow, decodeNatBits]
  | a :: xs, b :: ys, hlen, borrow => by
    have hlen' : xs.length = ys.length := by simpa using hlen
    have ih := decodeNatBits_rippleSubStream xs ys hlen' (fullSubBorrow a b borrow)
    have hfs := fullSub_toNat_eq a b borrow
    simp only [rippleSubStream, rippleSubFinalBorrow, decodeNatBits, List.length_cons,
      bif_eq_toNat]
    have hpow : 2 ^ (xs.length + 1) *
        (rippleSubFinalBorrow xs ys (fullSubBorrow a b borrow)).toNat =
        2 * (2 ^ xs.length * (rippleSubFinalBorrow xs ys (fullSubBorrow a b borrow)).toNat) := by
      rw [Nat.pow_succ]
      ring
    omega

/-- On `w`-bit encodings `encodeNatBits w A` and `encodeNatBits w B` with `B ≤ A` and `A < 2 ^ w`,
`rippleSubStream` produces `encodeNatBits w (A - B)`. -/
@[simp]
theorem rippleSubStream_encodeNatBits (w A B : ℕ) (hBA : B ≤ A) (hA : A < 2 ^ w) :
    rippleSubStream (encodeNatBits w A) (encodeNatBits w B) false =
      encodeNatBits w (A - B) := by
  have hB : B < 2 ^ w := lt_of_le_of_lt hBA hA
  have hlen : (encodeNatBits w A).length = (encodeNatBits w B).length := by simp
  have hout_len : (rippleSubStream (encodeNatBits w A) (encodeNatBits w B) false).length = w := by
    rw [length_rippleSubStream _ _ hlen false, encodeNatBits_length]
  have hlt : decodeNatBits (rippleSubStream (encodeNatBits w A) (encodeNatBits w B) false) < 2 ^ w := by
    have h := decodeNatBits_lt (rippleSubStream (encodeNatBits w A) (encodeNatBits w B) false)
    rwa [hout_len] at h
  have hsem := decodeNatBits_rippleSubStream (encodeNatBits w A) (encodeNatBits w B) hlen false
  rw [decodeNatBits_encodeNatBits w A hA, decodeNatBits_encodeNatBits w B hB,
    encodeNatBits_length] at hsem
  have hborrow : (rippleSubFinalBorrow (encodeNatBits w A) (encodeNatBits w B) false).toNat = 0 := by
    cases hbf : rippleSubFinalBorrow (encodeNatBits w A) (encodeNatBits w B) false
    · rfl
    · simp [hbf] at hsem
      omega
  have hf0 : false.toNat = 0 := rfl
  rw [hborrow, mul_zero, add_zero, hf0, add_zero] at hsem
  have hdec : decodeNatBits (rippleSubStream (encodeNatBits w A) (encodeNatBits w B) false) = A - B := by
    omega
  calc
    rippleSubStream (encodeNatBits w A) (encodeNatBits w B) false
      = encodeNatBits (rippleSubStream (encodeNatBits w A) (encodeNatBits w B) false).length
          (decodeNatBits (rippleSubStream (encodeNatBits w A) (encodeNatBits w B) false)) :=
        (encodeNatBits_decodeNatBits _).symm
    _ = encodeNatBits w (A - B) := by rw [hout_len, hdec]

/-- Concrete evaluation of the single uniform machine `tmUniformRippleSub` on any `w`-bit natural
numbers `B ≤ A < 2 ^ w`, computing `encodeNatBits w (A - B)` on `kIO` in `5 * w + 2` single-bit
`FinTM2` steps. -/
def tmUniformRippleSub_encodeNatBits_evalsToInTime_concrete (w A B : ℕ)
    (hBA : B ≤ A) (hA : A < 2 ^ w) :
    Turing.EvalsToInTime tmUniformRippleSub.step
      ⟨some .popA, default, threeTapeWorkStk [] (encodeNatBits w A) (encodeNatBits w B)⟩
      (some (Turing.haltList tmUniformRippleSub (encodeNatBits w (A - B))))
      (5 * w + 2) := by
  have hlen : (encodeNatBits w A).length = (encodeNatBits w B).length := by simp
  have hrun := tmUniformRippleSub_evalsToInTime_concrete (encodeNatBits w A) (encodeNatBits w B) hlen
  have hrev : (rippleSubRevLoop (encodeNatBits w A) (encodeNatBits w B) false []).reverse =
      encodeNatBits w (A - B) := by
    rw [reverse_rippleSubRevLoop _ _ hlen false [], List.reverse_nil, List.nil_append,
      rippleSubStream_encodeNatBits w A B hBA hA]
  rw [hrev, encodeNatBits_length] at hrun
  exact hrun

/-- Unconditional existential step bound and exact functional correctness for the single uniform
machine `tmUniformRippleSub` on `w`-bit operands `B ≤ A < 2 ^ w`. -/
theorem tmUniformRippleSub_encodeNatBits_evalsToInTime (w A B : ℕ)
    (hBA : B ≤ A) (hA : A < 2 ^ w) :
    ∃ t ≤ 5 * w + 2,
      Turing.EvalsToInTime tmUniformRippleSub.step
        ⟨some .popA, default, threeTapeWorkStk [] (encodeNatBits w A) (encodeNatBits w B)⟩
        (some (Turing.haltList tmUniformRippleSub (encodeNatBits w (A - B)))) t :=
  ⟨_, le_rfl, ⟨tmUniformRippleSub_encodeNatBits_evalsToInTime_concrete w A B hBA hA⟩⟩

/-! ### 1.8 Uniform Simultaneous Butterfly Add/Sub Machine (`tmUniformButterflyAddSub`) -/

/-- Canonical five-stack assignment with `s` on `kIO`, `w0` on `kWork0`, `w1` on `kWork1`,
`w2` on `kWork2`, `w3` on `kWork3`, and `[]` on all other stacks. -/
def fiveTapeWorkStk (s w0 w1 w2 w3 : List Bool) (k : TapeIdx) : List (BitTapeAlphabet k) :=
  if k = kIO then s else if k = kWork0 then w0 else if k = kWork1 then w1
  else if k = kWork2 then w2 else if k = kWork3 then w3 else []

@[simp]
theorem fiveTapeWorkStk_nil (s w0 w1 w2 : List Bool) :
    fiveTapeWorkStk s w0 w1 w2 [] = fourTapeWorkStk s w0 w1 w2 := by
  funext k
  by_cases hk : k = kIO
  · subst hk; simp [fiveTapeWorkStk, fourTapeWorkStk]
  · by_cases hk0 : k = kWork0
    · subst hk0; simp [fiveTapeWorkStk, fourTapeWorkStk, hk]
    · by_cases hk1 : k = kWork1
      · subst hk1; simp [fiveTapeWorkStk, fourTapeWorkStk, hk, hk0]
      · by_cases hk2 : k = kWork2
        · subst hk2; simp [fiveTapeWorkStk, fourTapeWorkStk, hk, hk0, hk1]
        · simp [fiveTapeWorkStk, fourTapeWorkStk, hk, hk0, hk1, hk2]

@[simp]
theorem fiveTapeWorkStk_kIO (s w0 w1 w2 w3 : List Bool) :
    fiveTapeWorkStk s w0 w1 w2 w3 kIO = s := by
  simp [fiveTapeWorkStk]

@[simp]
theorem fiveTapeWorkStk_kWork0 (s w0 w1 w2 w3 : List Bool) :
    fiveTapeWorkStk s w0 w1 w2 w3 kWork0 = w0 := by
  have h1 : kWork0 ≠ kIO := by decide
  simp [fiveTapeWorkStk, h1]

@[simp]
theorem fiveTapeWorkStk_kWork1 (s w0 w1 w2 w3 : List Bool) :
    fiveTapeWorkStk s w0 w1 w2 w3 kWork1 = w1 := by
  have h1 : kWork1 ≠ kIO := by decide
  have h2 : kWork1 ≠ kWork0 := by decide
  simp [fiveTapeWorkStk, h1, h2]

@[simp]
theorem fiveTapeWorkStk_kWork2 (s w0 w1 w2 w3 : List Bool) :
    fiveTapeWorkStk s w0 w1 w2 w3 kWork2 = w2 := by
  have h1 : kWork2 ≠ kIO := by decide
  have h2 : kWork2 ≠ kWork0 := by decide
  have h3 : kWork2 ≠ kWork1 := by decide
  simp [fiveTapeWorkStk, h1, h2, h3]

@[simp]
theorem fiveTapeWorkStk_kWork3 (s w0 w1 w2 w3 : List Bool) :
    fiveTapeWorkStk s w0 w1 w2 w3 kWork3 = w3 := by
  have h1 : kWork3 ≠ kIO := by decide
  have h2 : kWork3 ≠ kWork0 := by decide
  have h3 : kWork3 ≠ kWork1 := by decide
  have h4 : kWork3 ≠ kWork2 := by decide
  simp [fiveTapeWorkStk, h1, h2, h3, h4]

@[simp]
theorem update_fiveTapeWorkStk_kIO (s s' w0 w1 w2 w3 : List Bool) :
    Function.update (fiveTapeWorkStk s w0 w1 w2 w3) kIO s' = fiveTapeWorkStk s' w0 w1 w2 w3 := by
  funext k
  by_cases hk : k = kIO
  · subst hk; simp [fiveTapeWorkStk]
  · simp [fiveTapeWorkStk, hk]

@[simp]
theorem update_fiveTapeWorkStk_kWork0 (s w0 w0' w1 w2 w3 : List Bool) :
    Function.update (fiveTapeWorkStk s w0 w1 w2 w3) kWork0 w0' = fiveTapeWorkStk s w0' w1 w2 w3 := by
  have h1 : kWork0 ≠ kIO := by decide
  funext k
  by_cases hk0 : k = kWork0
  · subst hk0; simp [fiveTapeWorkStk, h1]
  · by_cases hk : k = kIO
    · subst hk; simp [fiveTapeWorkStk, hk0]
    · simp [fiveTapeWorkStk, hk, hk0]

@[simp]
theorem update_fiveTapeWorkStk_kWork1 (s w0 w1 w1' w2 w3 : List Bool) :
    Function.update (fiveTapeWorkStk s w0 w1 w2 w3) kWork1 w1' = fiveTapeWorkStk s w0 w1' w2 w3 := by
  have h1 : kWork1 ≠ kIO := by decide
  have h2 : kWork1 ≠ kWork0 := by decide
  funext k
  by_cases hk1 : k = kWork1
  · subst hk1; simp [fiveTapeWorkStk, h1, h2]
  · by_cases hk : k = kIO
    · subst hk; simp [fiveTapeWorkStk, hk1]
    · by_cases hk0 : k = kWork0
      · subst hk0; simp [fiveTapeWorkStk, hk, hk1]
      · simp [fiveTapeWorkStk, hk, hk0, hk1]

@[simp]
theorem update_fiveTapeWorkStk_kWork2 (s w0 w1 w2 w2' w3 : List Bool) :
    Function.update (fiveTapeWorkStk s w0 w1 w2 w3) kWork2 w2' = fiveTapeWorkStk s w0 w1 w2' w3 := by
  have h1 : kWork2 ≠ kIO := by decide
  have h2 : kWork2 ≠ kWork0 := by decide
  have h3 : kWork2 ≠ kWork1 := by decide
  funext k
  by_cases hk2 : k = kWork2
  · subst hk2; simp [fiveTapeWorkStk, h1, h2, h3]
  · by_cases hk : k = kIO
    · subst hk; simp [fiveTapeWorkStk, hk2]
    · by_cases hk0 : k = kWork0
      · subst hk0; simp [fiveTapeWorkStk, hk, hk2]
      · by_cases hk1 : k = kWork1
        · subst hk1; simp [fiveTapeWorkStk, hk, hk0, hk2]
        · simp [fiveTapeWorkStk, hk, hk0, hk1, hk2]

@[simp]
theorem update_fiveTapeWorkStk_kWork3 (s w0 w1 w2 w3 w3' : List Bool) :
    Function.update (fiveTapeWorkStk s w0 w1 w2 w3) kWork3 w3' = fiveTapeWorkStk s w0 w1 w2 w3' := by
  have h1 : kWork3 ≠ kIO := by decide
  have h2 : kWork3 ≠ kWork0 := by decide
  have h3 : kWork3 ≠ kWork1 := by decide
  have h4 : kWork3 ≠ kWork2 := by decide
  funext k
  by_cases hk3 : k = kWork3
  · subst hk3; simp [fiveTapeWorkStk, h1, h2, h3, h4]
  · by_cases hk : k = kIO
    · subst hk; simp [fiveTapeWorkStk, hk3]
    · by_cases hk0 : k = kWork0
      · subst hk0; simp [fiveTapeWorkStk, hk, hk3]
      · by_cases hk1 : k = kWork1
        · subst hk1; simp [fiveTapeWorkStk, hk, hk0, hk3]
        · by_cases hk2 : k = kWork2
          · subst hk2; simp [fiveTapeWorkStk, hk, hk0, hk1, hk3]
          · simp [fiveTapeWorkStk, hk, hk0, hk1, hk2, hk3]

/-- Strictly uniform 4-bit internal butterfly register (`Fintype.card ButterflyReg = 16`) holding
two operand latches `bitA`, `bitB`, a 1-bit `carry` flag, and a 1-bit `borrow` flag. -/
@[ext]
structure ButterflyReg where
  /-- First 1-bit latch (operand A or sum bit). -/
  bitA : Bool := false
  /-- Second 1-bit latch (operand B / eof flag or difference bit). -/
  bitB : Bool := false
  /-- 1-bit full-adder carry latch. -/
  carry : Bool := false
  /-- 1-bit full-subtractor borrow latch. -/
  borrow : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Explicit equivalence `ButterflyReg ≃ (Bool × Bool) × (Bool × Bool)` witnessing
`Fintype.card ButterflyReg = 16`. -/
def butterflyRegEquiv : ButterflyReg ≃ (Bool × Bool) × (Bool × Bool) where
  toFun r := ((r.bitA, r.bitB), (r.carry, r.borrow))
  invFun t := ⟨t.1.1, t.1.2, t.2.1, t.2.2⟩
  left_inv r := by cases r; rfl
  right_inv t := by rcases t with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

instance : Fintype ButterflyReg :=
  Fintype.ofEquiv ((Bool × Bool) × (Bool × Bool)) butterflyRegEquiv.symm

@[simp]
theorem card_butterflyReg : Fintype.card ButterflyReg = 16 := by decide

@[simp]
theorem butterflyReg_default_bitA : (default : ButterflyReg).bitA = false := rfl

@[simp]
theorem butterflyReg_default_bitB : (default : ButterflyReg).bitB = false := rfl

@[simp]
theorem butterflyReg_default_carry : (default : ButterflyReg).carry = false := rfl

@[simp]
theorem butterflyReg_default_borrow : (default : ButterflyReg).borrow = false := rfl

/-- Control labels for the uniform single-machine simultaneous butterfly add/sub `FinTM2`
(`|Λ| = 9`). -/
inductive ButterflyAddSubLabel : Type
  | popA
  | popB
  | pushSumRev
  | pushDiffRev
  | pushCarryRev
  | popSumRev
  | pushSumIO
  | popDiffRev
  | pushDiffWork0
  deriving DecidableEq, Repr, Inhabited

/-- Explicit equivalence `ButterflyAddSubLabel ≃ Fin 9` witnessing
`Fintype.card ButterflyAddSubLabel = 9`. -/
def butterflyAddSubLabelEquiv : ButterflyAddSubLabel ≃ Fin 9 where
  toFun
    | .popA => ⟨0, by decide⟩
    | .popB => ⟨1, by decide⟩
    | .pushSumRev => ⟨2, by decide⟩
    | .pushDiffRev => ⟨3, by decide⟩
    | .pushCarryRev => ⟨4, by decide⟩
    | .popSumRev => ⟨5, by decide⟩
    | .pushSumIO => ⟨6, by decide⟩
    | .popDiffRev => ⟨7, by decide⟩
    | .pushDiffWork0 => ⟨8, by decide⟩
  invFun
    | ⟨0, _⟩ => .popA
    | ⟨1, _⟩ => .popB
    | ⟨2, _⟩ => .pushSumRev
    | ⟨3, _⟩ => .pushDiffRev
    | ⟨4, _⟩ => .pushCarryRev
    | ⟨5, _⟩ => .popSumRev
    | ⟨6, _⟩ => .pushSumIO
    | ⟨7, _⟩ => .popDiffRev
    | ⟨_ + 8, _⟩ => .pushDiffWork0
  left_inv x := by cases x <;> rfl
  right_inv i := by
    rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try rfl
    omega

instance : Fintype ButterflyAddSubLabel :=
  Fintype.ofEquiv (Fin 9) butterflyAddSubLabelEquiv.symm

@[simp]
theorem card_butterflyAddSubLabel : Fintype.card ButterflyAddSubLabel = 9 := by decide

/-- Single uniform `FinTM2` machine (`|Λ| = 9`, `|σ| = 16`, `|Γ k₀| = 2`, zero length parameters)
that pops two LSB-first bitstreams `xs` (from `kWork0`) and `ys` (from `kWork1`) one bit at a time,
simultaneously computes both the 1-bit full-adder sum/carry and 1-bit full-subtractor difference/borrow
on `ButterflyReg`, pushes the reversed sum bits onto `kWork2` and reversed difference bits onto
`kWork3`, and streams the sum onto `kIO` and the difference onto `kWork0` in LSB-first order. -/
def tmUniformButterflyAddSub : Turing.FinTM2 :=
  mkBitFinTM2 ButterflyAddSubLabel .popA ButterflyReg default (fun lbl =>
    match lbl with
    | .popA =>
      Turing.TM2.Stmt.pop kWork0
        (fun r bOpt =>
          match bOpt with
          | some a => { r with bitA := a, bitB := true }
          | none => { r with bitA := false, bitB := false })
        (Turing.TM2.Stmt.branch (fun r => r.bitB)
          (Turing.TM2.Stmt.goto (fun _ => .popB))
          (Turing.TM2.Stmt.goto (fun _ => .pushCarryRev)))
    | .popB =>
      Turing.TM2.Stmt.pop kWork1
        (fun r bOpt =>
          let b := bOpt.getD false
          { bitA := fullAdderSum r.bitA b r.carry
            bitB := fullSubDiff r.bitA b r.borrow
            carry := fullAdderCarry r.bitA b r.carry
            borrow := fullSubBorrow r.bitA b r.borrow })
        (Turing.TM2.Stmt.goto (fun _ => .pushSumRev))
    | .pushSumRev =>
      Turing.TM2.Stmt.push kWork2 (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .pushDiffRev))
    | .pushDiffRev =>
      Turing.TM2.Stmt.push kWork3 (fun r => r.bitB)
        (Turing.TM2.Stmt.goto (fun _ => .popA))
    | .pushCarryRev =>
      Turing.TM2.Stmt.push kWork2 (fun r => r.carry)
        (Turing.TM2.Stmt.goto (fun _ => .popSumRev))
    | .popSumRev =>
      Turing.TM2.Stmt.pop kWork2
        (fun _ bOpt =>
          match bOpt with
          | some b => { bitA := b, bitB := false, carry := true, borrow := false }
          | none => default)
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .pushSumIO))
          (Turing.TM2.Stmt.goto (fun _ => .popDiffRev)))
    | .pushSumIO =>
      Turing.TM2.Stmt.push kIO (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popSumRev))
    | .popDiffRev =>
      Turing.TM2.Stmt.pop kWork3
        (fun _ bOpt =>
          match bOpt with
          | some b => { bitA := b, bitB := false, carry := true, borrow := false }
          | none => default)
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .pushDiffWork0))
          Turing.TM2.Stmt.halt)
    | .pushDiffWork0 =>
      Turing.TM2.Stmt.push kWork0 (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popDiffRev)))

/-- `tmUniformButterflyAddSub` satisfies `IsUniformFinTM2 tmUniformButterflyAddSub 9 16 2`. -/
theorem isUniformFinTM2_tmUniformButterflyAddSub :
    IsUniformFinTM2 tmUniformButterflyAddSub 9 16 2 :=
  isUniformFinTM2_mkBitFinTM2 _ _ _ (by decide) (by decide) (by decide)

/-- First pass of `tmUniformButterflyAddSub`: pops equal-length `xs` (`kWork0`) and `ys` (`kWork1`)
one bit at a time, simultaneously pushing reversed sum bits onto `kWork2` and reversed difference
bits onto `kWork3` in `4 * xs.length + 2` steps and transitioning to `.popSumRev`. -/
def tmUniformButterflyAddSub_pass1_evalsToInTime :
    ∀ (xs ys accSum accDiff : List Bool) (_hlen : xs.length = ys.length) (r : ButterflyReg),
      Turing.EvalsToInTime tmUniformButterflyAddSub.step
        ⟨some .popA, r, fiveTapeWorkStk [] xs ys accSum accDiff⟩
        (some ⟨some .popSumRev,
          { bitA := false
            bitB := false
            carry := (rippleAddRevLoop xs ys r.carry accSum).headD false
            borrow := rippleSubFinalBorrow xs ys r.borrow },
          fiveTapeWorkStk [] [] []
            (rippleAddRevLoop xs ys r.carry accSum)
            (rippleSubRevLoop xs ys r.borrow accDiff)⟩)
        (4 * xs.length + 2)
  | [], [], accSum, accDiff, _, r => by
    rcases r with ⟨bitA, bitB, carry, borrow⟩
    have hstep1 : tmUniformButterflyAddSub.step
        ⟨some .popA, ⟨bitA, bitB, carry, borrow⟩, fiveTapeWorkStk [] [] [] accSum accDiff⟩ =
        some ⟨some .pushCarryRev, ⟨false, false, carry, borrow⟩,
          fiveTapeWorkStk [] [] [] accSum accDiff⟩ := by
      simp [tmUniformButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformButterflyAddSub.step
        ⟨some .pushCarryRev, ⟨false, false, carry, borrow⟩,
          fiveTapeWorkStk [] [] [] accSum accDiff⟩ =
        some ⟨some .popSumRev, ⟨false, false, carry, borrow⟩,
          fiveTapeWorkStk [] [] [] (carry :: accSum) accDiff⟩ := by
      simp [tmUniformButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    exact EvalsToInTime.of_step hstep1 (EvalsToInTime.step_one hstep2)
  | a :: xs, b :: ys, accSum, accDiff, hlen, r => by
    rcases r with ⟨bitA, bitB, carry, borrow⟩
    have hlen' : xs.length = ys.length := by simpa using hlen
    have hstep1 : tmUniformButterflyAddSub.step
        ⟨some .popA, ⟨bitA, bitB, carry, borrow⟩,
          fiveTapeWorkStk [] (a :: xs) (b :: ys) accSum accDiff⟩ =
        some ⟨some .popB, ⟨a, true, carry, borrow⟩,
          fiveTapeWorkStk [] xs (b :: ys) accSum accDiff⟩ := by
      simp [tmUniformButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformButterflyAddSub.step
        ⟨some .popB, ⟨a, true, carry, borrow⟩,
          fiveTapeWorkStk [] xs (b :: ys) accSum accDiff⟩ =
        some ⟨some .pushSumRev,
          ⟨fullAdderSum a b carry, fullSubDiff a b borrow,
            fullAdderCarry a b carry, fullSubBorrow a b borrow⟩,
          fiveTapeWorkStk [] xs ys accSum accDiff⟩ := by
      simp [tmUniformButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep3 : tmUniformButterflyAddSub.step
        ⟨some .pushSumRev,
          ⟨fullAdderSum a b carry, fullSubDiff a b borrow,
            fullAdderCarry a b carry, fullSubBorrow a b borrow⟩,
          fiveTapeWorkStk [] xs ys accSum accDiff⟩ =
        some ⟨some .pushDiffRev,
          ⟨fullAdderSum a b carry, fullSubDiff a b borrow,
            fullAdderCarry a b carry, fullSubBorrow a b borrow⟩,
          fiveTapeWorkStk [] xs ys (fullAdderSum a b carry :: accSum) accDiff⟩ := by
      simp [tmUniformButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep4 : tmUniformButterflyAddSub.step
        ⟨some .pushDiffRev,
          ⟨fullAdderSum a b carry, fullSubDiff a b borrow,
            fullAdderCarry a b carry, fullSubBorrow a b borrow⟩,
          fiveTapeWorkStk [] xs ys (fullAdderSum a b carry :: accSum) accDiff⟩ =
        some ⟨some .popA,
          ⟨fullAdderSum a b carry, fullSubDiff a b borrow,
            fullAdderCarry a b carry, fullSubBorrow a b borrow⟩,
          fiveTapeWorkStk [] xs ys
            (fullAdderSum a b carry :: accSum)
            (fullSubDiff a b borrow :: accDiff)⟩ := by
      simp [tmUniformButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformButterflyAddSub_pass1_evalsToInTime xs ys
      (fullAdderSum a b carry :: accSum) (fullSubDiff a b borrow :: accDiff) hlen'
      ⟨fullAdderSum a b carry, fullSubDiff a b borrow,
        fullAdderCarry a b carry, fullSubBorrow a b borrow⟩
    dsimp only [rippleAddRevLoop, rippleSubRevLoop, rippleSubFinalBorrow]
    exact EvalsToInTime.mono
      (EvalsToInTime.of_step hstep1
        (EvalsToInTime.of_step hstep2
          (EvalsToInTime.of_step hstep3
            (EvalsToInTime.of_step hstep4 ih))))
      (by simp [List.length_cons]; omega)

/-- Second pass of `tmUniformButterflyAddSub`: pops `wsSum` from `kWork2` and pushes `wsSum.reverse`
onto `kIO` in `2 * wsSum.length + 1` steps, transitioning to `.popDiffRev`. -/
def tmUniformButterflyAddSub_pass2_evalsToInTime :
    ∀ (wsSum accSum wsDiff : List Bool) (r : ButterflyReg),
      Turing.EvalsToInTime tmUniformButterflyAddSub.step
        ⟨some .popSumRev, r, fiveTapeWorkStk accSum [] [] wsSum wsDiff⟩
        (some ⟨some .popDiffRev, default,
          fiveTapeWorkStk (wsSum.reverse ++ accSum) [] [] [] wsDiff⟩)
        (2 * wsSum.length + 1)
  | [], accSum, wsDiff, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux, fiveTapeWorkStk_kWork2, update_fiveTapeWorkStk_kWork2,
      butterflyReg_default_carry, List.head?_nil, List.tail_nil, List.reverse_nil,
      List.nil_append, cond_false]
  | b :: wsSum, accSum, wsDiff, r => by
    have hstep1 : tmUniformButterflyAddSub.step
        ⟨some .popSumRev, r, fiveTapeWorkStk accSum [] [] (b :: wsSum) wsDiff⟩ =
        some ⟨some .pushSumIO, { bitA := b, bitB := false, carry := true, borrow := false },
          fiveTapeWorkStk accSum [] [] wsSum wsDiff⟩ := by
      simp [tmUniformButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformButterflyAddSub.step
        ⟨some .pushSumIO, { bitA := b, bitB := false, carry := true, borrow := false },
          fiveTapeWorkStk accSum [] [] wsSum wsDiff⟩ =
        some ⟨some .popSumRev, { bitA := b, bitB := false, carry := true, borrow := false },
          fiveTapeWorkStk (b :: accSum) [] [] wsSum wsDiff⟩ := by
      simp [tmUniformButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformButterflyAddSub_pass2_evalsToInTime wsSum (b :: accSum) wsDiff
      { bitA := b, bitB := false, carry := true, borrow := false }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step hstep1 (EvalsToInTime.of_step hstep2 ih))
      (by simp [List.length_cons]; omega)

/-- Third pass of `tmUniformButterflyAddSub`: pops `wsDiff` from `kWork3` and pushes
`wsDiff.reverse` onto `kWork0` in `2 * wsDiff.length + 1` steps, halting with `default` register
state. -/
def tmUniformButterflyAddSub_pass3_evalsToInTime :
    ∀ (wsDiff sumOut accDiff : List Bool) (r : ButterflyReg),
      Turing.EvalsToInTime tmUniformButterflyAddSub.step
        ⟨some .popDiffRev, r, fiveTapeWorkStk sumOut accDiff [] [] wsDiff⟩
        (some ⟨none, default,
          fiveTapeWorkStk sumOut (wsDiff.reverse ++ accDiff) [] [] []⟩)
        (2 * wsDiff.length + 1)
  | [], sumOut, accDiff, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux, fiveTapeWorkStk_kWork3, update_fiveTapeWorkStk_kWork3,
      butterflyReg_default_carry, List.head?_nil, List.tail_nil, List.reverse_nil,
      List.nil_append, cond_false]
  | b :: wsDiff, sumOut, accDiff, r => by
    have hstep1 : tmUniformButterflyAddSub.step
        ⟨some .popDiffRev, r, fiveTapeWorkStk sumOut accDiff [] [] (b :: wsDiff)⟩ =
        some ⟨some .pushDiffWork0, { bitA := b, bitB := false, carry := true, borrow := false },
          fiveTapeWorkStk sumOut accDiff [] [] wsDiff⟩ := by
      simp [tmUniformButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformButterflyAddSub.step
        ⟨some .pushDiffWork0, { bitA := b, bitB := false, carry := true, borrow := false },
          fiveTapeWorkStk sumOut accDiff [] [] wsDiff⟩ =
        some ⟨some .popDiffRev, { bitA := b, bitB := false, carry := true, borrow := false },
          fiveTapeWorkStk sumOut (b :: accDiff) [] [] wsDiff⟩ := by
      simp [tmUniformButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformButterflyAddSub_pass3_evalsToInTime wsDiff sumOut (b :: accDiff)
      { bitA := b, bitB := false, carry := true, borrow := false }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step hstep1 (EvalsToInTime.of_step hstep2 ih))
      (by simp [List.length_cons]; omega)

/-- Concrete evaluation of the single uniform machine `tmUniformButterflyAddSub` on any equal-length
operand bitstreams `xs, ys : List Bool` (placed on `kWork0` and `kWork1`) in `8 * xs.length + 6`
steps, writing the butterfly sum `(rippleAddRevLoop xs ys false []).reverse` onto `kIO` and the
butterfly difference `(rippleSubRevLoop xs ys false []).reverse` onto `kWork0`. -/
def tmUniformButterflyAddSub_evalsToInTime_concrete (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    Turing.EvalsToInTime tmUniformButterflyAddSub.step
      ⟨some .popA, default, threeTapeWorkStk [] xs ys⟩
      (some ⟨none, default,
        twoTapeStk
          (rippleAddRevLoop xs ys false []).reverse
          (rippleSubRevLoop xs ys false []).reverse⟩)
      (8 * xs.length + 6) := by
  have hinit : (⟨some .popA, default, threeTapeWorkStk [] xs ys⟩ : tmUniformButterflyAddSub.Cfg) =
      ⟨some .popA, default, fiveTapeWorkStk [] xs ys [] []⟩ := by
    rw [fiveTapeWorkStk_nil, fourTapeWorkStk_nil]
  have hhalt : (⟨none, default,
        twoTapeStk
          (rippleAddRevLoop xs ys false []).reverse
          (rippleSubRevLoop xs ys false []).reverse⟩ : tmUniformButterflyAddSub.Cfg) =
      ⟨none, default,
        fiveTapeWorkStk
          ((rippleAddRevLoop xs ys false []).reverse ++ [])
          ((rippleSubRevLoop xs ys false []).reverse ++ [])
          [] [] []⟩ := by
    rw [List.append_nil, List.append_nil, fiveTapeWorkStk_nil, fourTapeWorkStk_nil,
      threeTapeWorkStk_nil]
  rw [hinit, hhalt]
  have hp1 := tmUniformButterflyAddSub_pass1_evalsToInTime xs ys [] [] hlen default
  have hp2 := tmUniformButterflyAddSub_pass2_evalsToInTime
    (rippleAddRevLoop xs ys false []) [] (rippleSubRevLoop xs ys false [])
    { bitA := false
      bitB := false
      carry := (rippleAddRevLoop xs ys false []).headD false
      borrow := rippleSubFinalBorrow xs ys false }
  have hp3 := tmUniformButterflyAddSub_pass3_evalsToInTime
    (rippleSubRevLoop xs ys false [])
    ((rippleAddRevLoop xs ys false []).reverse ++ []) [] default
  have hlen_add : (rippleAddRevLoop xs ys false []).length = xs.length + 1 := by
    simpa using length_rippleAddRevLoop xs ys hlen false []
  have hlen_sub : (rippleSubRevLoop xs ys false []).length = xs.length := by
    simpa using length_rippleSubRevLoop xs ys hlen false []
  rw [hlen_add] at hp2
  rw [hlen_sub] at hp3
  exact EvalsToInTime.mono (EvalsToInTime.trans' (EvalsToInTime.trans' hp1 hp2) hp3) (by omega)

/-- Concrete evaluation of the single uniform machine `tmUniformButterflyAddSub` on any `w`-bit
natural numbers `B ≤ A < 2 ^ w`, simultaneously computing both the butterfly sum
`encodeNatBits (w + 1) (A + B)` on `kIO` and the butterfly difference `encodeNatBits w (A - B)` on
`kWork0` in `8 * w + 6` single-bit `FinTM2` steps. -/
def tmUniformButterflyAddSub_encodeNatBits_evalsToInTime_concrete (w A B : ℕ)
    (hBA : B ≤ A) (hA : A < 2 ^ w) :
    Turing.EvalsToInTime tmUniformButterflyAddSub.step
      ⟨some .popA, default, threeTapeWorkStk [] (encodeNatBits w A) (encodeNatBits w B)⟩
      (some ⟨none, default,
        twoTapeStk (encodeNatBits (w + 1) (A + B)) (encodeNatBits w (A - B))⟩)
      (8 * w + 6) := by
  have hB : B < 2 ^ w := lt_of_le_of_lt hBA hA
  have hlen : (encodeNatBits w A).length = (encodeNatBits w B).length := by simp
  have hrun := tmUniformButterflyAddSub_evalsToInTime_concrete
    (encodeNatBits w A) (encodeNatBits w B) hlen
  have hrev_add : (rippleAddRevLoop (encodeNatBits w A) (encodeNatBits w B) false []).reverse =
      encodeNatBits (w + 1) (A + B) := by
    rw [reverse_rippleAddRevLoop _ _ hlen false [], List.reverse_nil, List.nil_append,
      rippleAddStream_encodeNatBits w A B hA hB]
  have hrev_sub : (rippleSubRevLoop (encodeNatBits w A) (encodeNatBits w B) false []).reverse =
      encodeNatBits w (A - B) := by
    rw [reverse_rippleSubRevLoop _ _ hlen false [], List.reverse_nil, List.nil_append,
      rippleSubStream_encodeNatBits w A B hBA hA]
  rw [hrev_add, hrev_sub, encodeNatBits_length] at hrun
  exact hrun

/-- Unconditional existential step bound and exact functional correctness for the single uniform
simultaneous butterfly machine `tmUniformButterflyAddSub` on `w`-bit operands `B ≤ A < 2 ^ w`. -/
theorem tmUniformButterflyAddSub_encodeNatBits_evalsToInTime (w A B : ℕ)
    (hBA : B ≤ A) (hA : A < 2 ^ w) :
    ∃ t ≤ 8 * w + 6,
      Turing.EvalsToInTime tmUniformButterflyAddSub.step
        ⟨some .popA, default, threeTapeWorkStk [] (encodeNatBits w A) (encodeNatBits w B)⟩
        (some ⟨none, default,
          twoTapeStk (encodeNatBits (w + 1) (A + B)) (encodeNatBits w (A - B))⟩) t :=
  ⟨_, le_rfl, ⟨tmUniformButterflyAddSub_encodeNatBits_evalsToInTime_concrete w A B hBA hA⟩⟩

/-! ### 1.9 Uniform 1-Bit Gated Multiply-Accumulate Machine (`tmUniformBitMulAdd`) -/

/-- Control labels for the uniform single-machine 1-bit gated multiply-accumulate `FinTM2`
(`|Λ| = 7`). -/
inductive BitMulAddLabel : Type
  | popMulBit
  | popA
  | popB
  | pushSumRev
  | pushCarryRev
  | popSumRev
  | pushIO
  deriving DecidableEq, Repr, Inhabited

/-- Explicit equivalence `BitMulAddLabel ≃ Fin 7` witnessing `Fintype.card BitMulAddLabel = 7`. -/
def bitMulAddLabelEquiv : BitMulAddLabel ≃ Fin 7 where
  toFun
    | .popMulBit => ⟨0, by decide⟩
    | .popA => ⟨1, by decide⟩
    | .popB => ⟨2, by decide⟩
    | .pushSumRev => ⟨3, by decide⟩
    | .pushCarryRev => ⟨4, by decide⟩
    | .popSumRev => ⟨5, by decide⟩
    | .pushIO => ⟨6, by decide⟩
  invFun
    | ⟨0, _⟩ => .popMulBit
    | ⟨1, _⟩ => .popA
    | ⟨2, _⟩ => .popB
    | ⟨3, _⟩ => .pushSumRev
    | ⟨4, _⟩ => .pushCarryRev
    | ⟨5, _⟩ => .popSumRev
    | ⟨_ + 6, _⟩ => .pushIO
  left_inv x := by cases x <;> rfl
  right_inv i := by
    rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try rfl
    omega

instance : Fintype BitMulAddLabel :=
  Fintype.ofEquiv (Fin 7) bitMulAddLabelEquiv.symm

@[simp]
theorem card_bitMulAddLabel : Fintype.card BitMulAddLabel = 7 := by decide

/-- **Single Uniform 1-Bit Gated Multiply-Accumulate Machine (`tmUniformBitMulAdd`)**:
A single uniform 8-stack binary `FinTM2` machine (`|Λ| = 7`, `|σ| = 16`, `|Γ k₀| = 2`, zero length parameters)
that pops a multiplier bit `mBit` from `kIO` into `ButterflyReg.borrow`, streams equal-length
LSB-first bitstreams `xs` (accumulator on `kWork0`) and `ys` (multiplicand on `kWork1`) one bit at a
time while computing the 1-bit partial-product gated full-adder sum `fullAdderSum r.bitA (b && r.borrow) r.carry`
and carry `fullAdderCarry r.bitA (b && r.borrow) r.carry`, pushes the reversed sum bits and final
carry-out onto `kWork2`, and streams them back onto `kIO` in LSB-first order. -/
def tmUniformBitMulAdd : Turing.FinTM2 :=
  mkBitFinTM2 BitMulAddLabel .popMulBit ButterflyReg default (fun lbl =>
    match lbl with
    | .popMulBit =>
      Turing.TM2.Stmt.pop kIO
        (fun _ bOpt =>
          { bitA := false, bitB := false, carry := false, borrow := bOpt.getD false })
        (Turing.TM2.Stmt.goto (fun _ => .popA))
    | .popA =>
      Turing.TM2.Stmt.pop kWork0
        (fun r bOpt =>
          match bOpt with
          | some a => { r with bitA := a, bitB := true }
          | none => { r with bitA := false, bitB := false })
        (Turing.TM2.Stmt.branch (fun r => r.bitB)
          (Turing.TM2.Stmt.goto (fun _ => .popB))
          (Turing.TM2.Stmt.goto (fun _ => .pushCarryRev)))
    | .popB =>
      Turing.TM2.Stmt.pop kWork1
        (fun r bOpt =>
          let b := (bOpt.getD false) && r.borrow
          { r with
            bitA := fullAdderSum r.bitA b r.carry
            bitB := false
            carry := fullAdderCarry r.bitA b r.carry })
        (Turing.TM2.Stmt.goto (fun _ => .pushSumRev))
    | .pushSumRev =>
      Turing.TM2.Stmt.push kWork2 (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popA))
    | .pushCarryRev =>
      Turing.TM2.Stmt.push kWork2 (fun r => r.carry)
        (Turing.TM2.Stmt.goto (fun _ => .popSumRev))
    | .popSumRev =>
      Turing.TM2.Stmt.pop kWork2
        (fun _ bOpt =>
          match bOpt with
          | some b => { bitA := b, bitB := false, carry := true, borrow := false }
          | none => default)
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .pushIO))
          Turing.TM2.Stmt.halt)
    | .pushIO =>
      Turing.TM2.Stmt.push kIO (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popSumRev)))

/-- `tmUniformBitMulAdd` satisfies `IsUniformFinTM2 tmUniformBitMulAdd 7 16 2`. -/
theorem isUniformFinTM2_tmUniformBitMulAdd : IsUniformFinTM2 tmUniformBitMulAdd 7 16 2 :=
  isUniformFinTM2_mkBitFinTM2 _ _ _ (by decide) (by decide) (by decide)

/-- First pass of `tmUniformBitMulAdd`: pops equal-length `xs` (`kWork0`) and `ys` (`kWork1`) one
bit at a time, gating each bit of `ys` by `r.borrow`, and pushes the reversed sum bits and final
carry onto `kWork2` in `3 * xs.length + 2` steps. -/
def tmUniformBitMulAdd_pass1_evalsToInTime :
    ∀ (xs ys acc : List Bool) (_hlen : xs.length = ys.length) (r : ButterflyReg),
      Turing.EvalsToInTime tmUniformBitMulAdd.step
        ⟨some .popA, r, fourTapeWorkStk [] xs ys acc⟩
        (some ⟨some .popSumRev,
          { bitA := false
            bitB := false
            carry := (rippleAddRevLoop xs (ys.map (fun b => b && r.borrow)) r.carry acc).headD false
            borrow := r.borrow },
          fourTapeWorkStk [] [] []
            (rippleAddRevLoop xs (ys.map (fun b => b && r.borrow)) r.carry acc)⟩)
        (3 * xs.length + 2)
  | [], [], acc, _, r => by
    rcases r with ⟨bitA, bitB, carry, borrow⟩
    have hstep1 : tmUniformBitMulAdd.step
        ⟨some .popA, ⟨bitA, bitB, carry, borrow⟩, fourTapeWorkStk [] [] [] acc⟩ =
        some ⟨some .pushCarryRev, ⟨false, false, carry, borrow⟩, fourTapeWorkStk [] [] [] acc⟩ := by
      simp [tmUniformBitMulAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformBitMulAdd.step
        ⟨some .pushCarryRev, ⟨false, false, carry, borrow⟩, fourTapeWorkStk [] [] [] acc⟩ =
        some ⟨some .popSumRev, ⟨false, false, carry, borrow⟩,
          fourTapeWorkStk [] [] [] (carry :: acc)⟩ := by
      simp [tmUniformBitMulAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    exact EvalsToInTime.of_step hstep1 (EvalsToInTime.step_one hstep2)
  | a :: xs, b :: ys, acc, hlen, r => by
    rcases r with ⟨bitA, bitB, carry, borrow⟩
    have hlen' : xs.length = ys.length := by simpa using hlen
    have hstep1 : tmUniformBitMulAdd.step
        ⟨some .popA, ⟨bitA, bitB, carry, borrow⟩, fourTapeWorkStk [] (a :: xs) (b :: ys) acc⟩ =
        some ⟨some .popB, ⟨a, true, carry, borrow⟩, fourTapeWorkStk [] xs (b :: ys) acc⟩ := by
      simp [tmUniformBitMulAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformBitMulAdd.step
        ⟨some .popB, ⟨a, true, carry, borrow⟩, fourTapeWorkStk [] xs (b :: ys) acc⟩ =
        some ⟨some .pushSumRev,
          ⟨fullAdderSum a (b && borrow) carry, false, fullAdderCarry a (b && borrow) carry, borrow⟩,
          fourTapeWorkStk [] xs ys acc⟩ := by
      simp [tmUniformBitMulAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep3 : tmUniformBitMulAdd.step
        ⟨some .pushSumRev,
          ⟨fullAdderSum a (b && borrow) carry, false, fullAdderCarry a (b && borrow) carry, borrow⟩,
          fourTapeWorkStk [] xs ys acc⟩ =
        some ⟨some .popA,
          ⟨fullAdderSum a (b && borrow) carry, false, fullAdderCarry a (b && borrow) carry, borrow⟩,
          fourTapeWorkStk [] xs ys (fullAdderSum a (b && borrow) carry :: acc)⟩ := by
      simp [tmUniformBitMulAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformBitMulAdd_pass1_evalsToInTime xs ys
      (fullAdderSum a (b && borrow) carry :: acc) hlen'
      ⟨fullAdderSum a (b && borrow) carry, false, fullAdderCarry a (b && borrow) carry, borrow⟩
    dsimp only [List.map, rippleAddRevLoop]
    exact EvalsToInTime.mono
      (EvalsToInTime.of_step hstep1 (EvalsToInTime.of_step hstep2 (EvalsToInTime.of_step hstep3 ih)))
      (by simp [List.length_cons]; omega)

/-- Second pass of `tmUniformBitMulAdd`: pops `ws` from `kWork2` and pushes `ws.reverse` onto `kIO`
in `2 * ws.length + 1` steps, halting with `default` register state. -/
def tmUniformBitMulAdd_pass2_evalsToInTime :
    ∀ (ws acc : List Bool) (r : ButterflyReg),
      Turing.EvalsToInTime tmUniformBitMulAdd.step
        ⟨some .popSumRev, r, fourTapeWorkStk acc [] [] ws⟩
        (some ⟨none, default, fourTapeWorkStk (ws.reverse ++ acc) [] [] []⟩)
        (2 * ws.length + 1)
  | [], acc, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformBitMulAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux, fourTapeWorkStk_kWork2, update_fourTapeWorkStk_kWork2,
      butterflyReg_default_carry, List.head?_nil, List.tail_nil, List.reverse_nil,
      List.nil_append, cond_false]
  | b :: ws, acc, r => by
    have hstep1 : tmUniformBitMulAdd.step
        ⟨some .popSumRev, r, fourTapeWorkStk acc [] [] (b :: ws)⟩ =
        some ⟨some .pushIO, { bitA := b, bitB := false, carry := true, borrow := false },
          fourTapeWorkStk acc [] [] ws⟩ := by
      simp [tmUniformBitMulAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformBitMulAdd.step
        ⟨some .pushIO, { bitA := b, bitB := false, carry := true, borrow := false },
          fourTapeWorkStk acc [] [] ws⟩ =
        some ⟨some .popSumRev, { bitA := b, bitB := false, carry := true, borrow := false },
          fourTapeWorkStk (b :: acc) [] [] ws⟩ := by
      simp [tmUniformBitMulAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformBitMulAdd_pass2_evalsToInTime ws (b :: acc)
      { bitA := b, bitB := false, carry := true, borrow := false }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step hstep1 (EvalsToInTime.of_step hstep2 ih))
      (by simp [List.length_cons]; omega)

/-- Concrete evaluation of `tmUniformBitMulAdd` on multiplier bit `[mBit]` (`kIO`) and equal-length
operand bitstreams `xs` (`kWork0`) and `ys` (`kWork1`) in `5 * xs.length + 6` steps. -/
def tmUniformBitMulAdd_evalsToInTime_concrete (mBit : Bool) (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    Turing.EvalsToInTime tmUniformBitMulAdd.step
      ⟨some .popMulBit, default, threeTapeWorkStk [mBit] xs ys⟩
      (some (Turing.haltList tmUniformBitMulAdd
        (rippleAddRevLoop xs (ys.map (fun b => b && mBit)) false []).reverse))
      (5 * xs.length + 6) := by
  have hinit : (⟨some .popMulBit, default, threeTapeWorkStk [mBit] xs ys⟩ : tmUniformBitMulAdd.Cfg) =
      ⟨some .popMulBit, default, fourTapeWorkStk [mBit] xs ys []⟩ := by
    rw [fourTapeWorkStk_nil]
  have hhalt : Turing.haltList tmUniformBitMulAdd
        (rippleAddRevLoop xs (ys.map (fun b => b && mBit)) false []).reverse =
      ⟨none, default,
        fourTapeWorkStk ((rippleAddRevLoop xs (ys.map (fun b => b && mBit)) false []).reverse ++ []) [] [] []⟩ := by
    rw [List.append_nil, fourTapeWorkStk_nil, threeTapeWorkStk_nil, twoTapeStk_nil]
    rfl
  rw [hinit, hhalt]
  have hstep0 : tmUniformBitMulAdd.step
      ⟨some .popMulBit, default, fourTapeWorkStk [mBit] xs ys []⟩ =
      some ⟨some .popA, ⟨false, false, false, mBit⟩, fourTapeWorkStk [] xs ys []⟩ := by
    simp [tmUniformBitMulAdd, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux]
  have hp1 := tmUniformBitMulAdd_pass1_evalsToInTime xs ys [] hlen ⟨false, false, false, mBit⟩
  have hlen_map : xs.length = (ys.map (fun b => b && mBit)).length := by
    simpa using hlen
  have hp2 := tmUniformBitMulAdd_pass2_evalsToInTime
    (rippleAddRevLoop xs (ys.map (fun b => b && mBit)) false []) []
    { bitA := false
      bitB := false
      carry := (rippleAddRevLoop xs (ys.map (fun b => b && mBit)) false []).headD false
      borrow := mBit }
  have hlen_rev : (rippleAddRevLoop xs (ys.map (fun b => b && mBit)) false []).length = xs.length + 1 := by
    simpa using length_rippleAddRevLoop xs (ys.map (fun b => b && mBit)) hlen_map false []
  rw [hlen_rev] at hp2
  exact EvalsToInTime.mono
    (EvalsToInTime.of_step hstep0 (EvalsToInTime.trans' hp1 hp2)) (by omega)

/-- Bitwise gating of `encodeNatBits w B` by `mBit` produces `encodeNatBits w (if mBit then B else 0)`. -/
@[simp]
theorem map_and_encodeNatBits (w B : ℕ) (mBit : Bool) :
    (encodeNatBits w B).map (fun b => b && mBit) =
      encodeNatBits w (if mBit then B else 0) := by
  unfold encodeNatBits
  rw [List.map_ofFn]
  congr 1
  funext i
  cases mBit <;> simp

/-- Concrete evaluation of the single uniform machine `tmUniformBitMulAdd` on multiplier bit `mBit`
and any `w`-bit natural numbers `acc, B < 2 ^ w`, computing
`encodeNatBits (w + 1) (acc + if mBit then B else 0)` on `kIO` in `5 * w + 6` single-bit `FinTM2`
steps. -/
def tmUniformBitMulAdd_encodeNatBits_evalsToInTime_concrete (mBit : Bool) (w acc B : ℕ)
    (hacc : acc < 2 ^ w) (hB : B < 2 ^ w) :
    Turing.EvalsToInTime tmUniformBitMulAdd.step
      ⟨some .popMulBit, default, threeTapeWorkStk [mBit] (encodeNatBits w acc) (encodeNatBits w B)⟩
      (some (Turing.haltList tmUniformBitMulAdd
        (encodeNatBits (w + 1) (acc + if mBit then B else 0))))
      (5 * w + 6) := by
  have hlen : (encodeNatBits w acc).length = (encodeNatBits w B).length := by simp
  have hrun := tmUniformBitMulAdd_evalsToInTime_concrete mBit
    (encodeNatBits w acc) (encodeNatBits w B) hlen
  have hB' : (if mBit then B else 0) < 2 ^ w := by
    cases mBit <;> simp [hB]
  have hlen' : (encodeNatBits w acc).length = (encodeNatBits w (if mBit then B else 0)).length := by
    simp
  have hrev :
      (rippleAddRevLoop (encodeNatBits w acc)
        ((encodeNatBits w B).map (fun b => b && mBit)) false []).reverse =
      encodeNatBits (w + 1) (acc + if mBit then B else 0) := by
    rw [map_and_encodeNatBits,
      reverse_rippleAddRevLoop _ _ hlen' false [], List.reverse_nil, List.nil_append,
      rippleAddStream_encodeNatBits w acc (if mBit then B else 0) hacc hB']
  rw [hrev, encodeNatBits_length] at hrun
  exact hrun

/-- Unconditional existential step bound and exact functional correctness for the single uniform
machine `tmUniformBitMulAdd` on `w`-bit operands `acc, B < 2 ^ w`. -/
theorem tmUniformBitMulAdd_encodeNatBits_evalsToInTime (mBit : Bool) (w acc B : ℕ)
    (hacc : acc < 2 ^ w) (hB : B < 2 ^ w) :
    ∃ t ≤ 5 * w + 6,
      Turing.EvalsToInTime tmUniformBitMulAdd.step
        ⟨some .popMulBit, default, threeTapeWorkStk [mBit] (encodeNatBits w acc) (encodeNatBits w B)⟩
        (some (Turing.haltList tmUniformBitMulAdd
          (encodeNatBits (w + 1) (acc + if mBit then B else 0)))) t :=
  ⟨_, le_rfl, ⟨tmUniformBitMulAdd_encodeNatBits_evalsToInTime_concrete mBit w acc B hacc hB⟩⟩

/-! ### 1.10 Uniform Conditional Subtract-Mux Machine for Restoring Division & Square Root (`tmUniformCondSubStep`) -/

/-- Control labels for the uniform single-machine conditional subtract-mux `FinTM2` (`|Λ| = 8`). -/
inductive CondSubStepLabel : Type
  | popA
  | popB
  | pushDiffRev
  | pushOrigRev
  | popMuxDiff
  | popMuxOrig
  | pushMuxIO
  | pushQuotBit
  deriving DecidableEq, Repr, Inhabited

/-- Explicit equivalence `CondSubStepLabel ≃ Fin 8` witnessing `Fintype.card CondSubStepLabel = 8`. -/
def condSubStepLabelEquiv : CondSubStepLabel ≃ Fin 8 where
  toFun
    | .popA => ⟨0, by decide⟩
    | .popB => ⟨1, by decide⟩
    | .pushDiffRev => ⟨2, by decide⟩
    | .pushOrigRev => ⟨3, by decide⟩
    | .popMuxDiff => ⟨4, by decide⟩
    | .popMuxOrig => ⟨5, by decide⟩
    | .pushMuxIO => ⟨6, by decide⟩
    | .pushQuotBit => ⟨7, by decide⟩
  invFun
    | ⟨0, _⟩ => .popA
    | ⟨1, _⟩ => .popB
    | ⟨2, _⟩ => .pushDiffRev
    | ⟨3, _⟩ => .pushOrigRev
    | ⟨4, _⟩ => .popMuxDiff
    | ⟨5, _⟩ => .popMuxOrig
    | ⟨6, _⟩ => .pushMuxIO
    | ⟨_ + 7, _⟩ => .pushQuotBit
  left_inv x := by cases x <;> rfl
  right_inv i := by
    rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try rfl
    omega

instance : Fintype CondSubStepLabel :=
  Fintype.ofEquiv (Fin 8) condSubStepLabelEquiv.symm

@[simp]
theorem card_condSubStepLabel : Fintype.card CondSubStepLabel = 8 := by decide

/-- **Single Uniform Conditional Subtract-Mux Machine (`tmUniformCondSubStep`)**:
A single uniform 8-stack binary `FinTM2` machine (`|Λ| = 8`, `|σ| = 16`, `|Γ k₀| = 2`, zero length parameters)
realizing one step of $w$-bit restoring division (`binaryRestoringDivModRegAux w`) or restoring
square root (`binaryRestoringSqrtRegAux w`):
- Pass 1 streams `xs = encodeNatBits w R` (`kWork0`) and `ys = encodeNatBits w D` (`kWork1`) one
  bit at a time, computing the ripple-borrow difference bit `fullSubDiff` (pushed onto `kWork2`)
  and preserving the original bit `a` (pushed onto `kWork3`).
- At the end of Pass 1, `r.borrow = rippleSubFinalBorrow xs ys false` equals `decide (R < D)`.
- Pass 2 pops `kWork2` and `kWork3` in lockstep, multiplexing `if r.borrow then a else d` onto
  `kIO` to output `encodeNatBits w (if D ≤ R then R - D else R)` on `kIO` and pushing the
  quotient/root bit `[decide (D ≤ R)]` onto `kWork0` in `7 * w + 3` `TM2.step` transitions. -/
def tmUniformCondSubStep : Turing.FinTM2 :=
  mkBitFinTM2 CondSubStepLabel .popA ButterflyReg default (fun lbl =>
    match lbl with
    | .popA =>
      Turing.TM2.Stmt.pop kWork0
        (fun r bOpt =>
          match bOpt with
          | some a => { r with bitA := a, carry := true }
          | none => { bitA := false, bitB := false, carry := false, borrow := r.borrow })
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .popB))
          (Turing.TM2.Stmt.goto (fun _ => .popMuxDiff)))
    | .popB =>
      Turing.TM2.Stmt.pop kWork1
        (fun r bOpt =>
          let b := bOpt.getD false
          { bitA := r.bitA
            bitB := fullSubDiff r.bitA b r.borrow
            carry := false
            borrow := fullSubBorrow r.bitA b r.borrow })
        (Turing.TM2.Stmt.goto (fun _ => .pushDiffRev))
    | .pushDiffRev =>
      Turing.TM2.Stmt.push kWork2 (fun r => r.bitB)
        (Turing.TM2.Stmt.goto (fun _ => .pushOrigRev))
    | .pushOrigRev =>
      Turing.TM2.Stmt.push kWork3 (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popA))
    | .popMuxDiff =>
      Turing.TM2.Stmt.pop kWork2
        (fun r bOpt =>
          match bOpt with
          | some d => { r with bitB := d, carry := true }
          | none => { bitA := false, bitB := false, carry := false, borrow := r.borrow })
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .popMuxOrig))
          (Turing.TM2.Stmt.goto (fun _ => .pushQuotBit)))
    | .popMuxOrig =>
      Turing.TM2.Stmt.pop kWork3
        (fun r bOpt =>
          let a := bOpt.getD false
          { bitA := if r.borrow then a else r.bitB
            bitB := false
            carry := false
            borrow := r.borrow })
        (Turing.TM2.Stmt.goto (fun _ => .pushMuxIO))
    | .pushMuxIO =>
      Turing.TM2.Stmt.push kIO (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popMuxDiff))
    | .pushQuotBit =>
      Turing.TM2.Stmt.push kWork0 (fun r => !r.borrow)
        (Turing.TM2.Stmt.load (fun _ => default)
          Turing.TM2.Stmt.halt))

/-- `tmUniformCondSubStep` satisfies `IsUniformFinTM2 tmUniformCondSubStep 8 16 2`. -/
theorem isUniformFinTM2_tmUniformCondSubStep :
    IsUniformFinTM2 tmUniformCondSubStep 8 16 2 :=
  isUniformFinTM2_mkBitFinTM2 _ _ _ (by decide) (by decide) (by decide)

/-- First pass of `tmUniformCondSubStep`: pops equal-length `xs` (`kWork0`) and `ys` (`kWork1`)
one bit at a time, pushing reversed difference bits onto `kWork2` and reversed original bits onto
`kWork3` in `4 * xs.length + 1` steps. -/
def tmUniformCondSubStep_pass1_evalsToInTime :
    ∀ (xs ys accDiff accOrig : List Bool) (_hlen : xs.length = ys.length) (r : ButterflyReg),
      Turing.EvalsToInTime tmUniformCondSubStep.step
        ⟨some .popA, r, fiveTapeWorkStk [] xs ys accDiff accOrig⟩
        (some ⟨some .popMuxDiff,
          { bitA := false
            bitB := false
            carry := false
            borrow := rippleSubFinalBorrow xs ys r.borrow },
          fiveTapeWorkStk [] [] []
            (rippleSubRevLoop xs ys r.borrow accDiff)
            (xs.reverse ++ accOrig)⟩)
        (4 * xs.length + 1)
  | [], [], accDiff, accOrig, _, r => by
    rcases r with ⟨bitA, bitB, carry, borrow⟩
    refine EvalsToInTime.step_one ?_
    simp [tmUniformCondSubStep, rippleSubRevLoop, rippleSubFinalBorrow, mkBitFinTM2,
      Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
  | a :: xs, b :: ys, accDiff, accOrig, hlen, r => by
    rcases r with ⟨bitA, bitB, carry, borrow⟩
    have hlen' : xs.length = ys.length := by simpa using hlen
    have hstep1 : tmUniformCondSubStep.step
        ⟨some .popA, ⟨bitA, bitB, carry, borrow⟩,
          fiveTapeWorkStk [] (a :: xs) (b :: ys) accDiff accOrig⟩ =
        some ⟨some .popB, ⟨a, bitB, true, borrow⟩,
          fiveTapeWorkStk [] xs (b :: ys) accDiff accOrig⟩ := by
      simp [tmUniformCondSubStep, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformCondSubStep.step
        ⟨some .popB, ⟨a, bitB, true, borrow⟩,
          fiveTapeWorkStk [] xs (b :: ys) accDiff accOrig⟩ =
        some ⟨some .pushDiffRev,
          ⟨a, fullSubDiff a b borrow, false, fullSubBorrow a b borrow⟩,
          fiveTapeWorkStk [] xs ys accDiff accOrig⟩ := by
      simp [tmUniformCondSubStep, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep3 : tmUniformCondSubStep.step
        ⟨some .pushDiffRev,
          ⟨a, fullSubDiff a b borrow, false, fullSubBorrow a b borrow⟩,
          fiveTapeWorkStk [] xs ys accDiff accOrig⟩ =
        some ⟨some .pushOrigRev,
          ⟨a, fullSubDiff a b borrow, false, fullSubBorrow a b borrow⟩,
          fiveTapeWorkStk [] xs ys (fullSubDiff a b borrow :: accDiff) accOrig⟩ := by
      simp [tmUniformCondSubStep, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep4 : tmUniformCondSubStep.step
        ⟨some .pushOrigRev,
          ⟨a, fullSubDiff a b borrow, false, fullSubBorrow a b borrow⟩,
          fiveTapeWorkStk [] xs ys (fullSubDiff a b borrow :: accDiff) accOrig⟩ =
        some ⟨some .popA,
          ⟨a, fullSubDiff a b borrow, false, fullSubBorrow a b borrow⟩,
          fiveTapeWorkStk [] xs ys
            (fullSubDiff a b borrow :: accDiff)
            (a :: accOrig)⟩ := by
      simp [tmUniformCondSubStep, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformCondSubStep_pass1_evalsToInTime xs ys
      (fullSubDiff a b borrow :: accDiff) (a :: accOrig) hlen'
      ⟨a, fullSubDiff a b borrow, false, fullSubBorrow a b borrow⟩
    dsimp only [rippleSubRevLoop, rippleSubFinalBorrow]
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono
      (EvalsToInTime.of_step hstep1
        (EvalsToInTime.of_step hstep2
          (EvalsToInTime.of_step hstep3
            (EvalsToInTime.of_step hstep4 ih))))
      (by simp [List.length_cons]; omega)

/-- Lockstep reverse multiplexer loop used in Pass 2 of `tmUniformCondSubStep`. -/
def muxRevLoop (borrow : Bool) : List Bool → List Bool → List Bool → List Bool
  | [], _, acc => acc
  | d :: ds, [], acc => muxRevLoop borrow ds [] ((if borrow then false else d) :: acc)
  | d :: ds, a :: os, acc => muxRevLoop borrow ds os ((if borrow then a else d) :: acc)

@[simp]
theorem muxRevLoop_eq_ite :
    ∀ (borrow : Bool) (wsDiff wsOrig acc : List Bool) (_hlen : wsDiff.length = wsOrig.length),
      muxRevLoop borrow wsDiff wsOrig acc =
        (if borrow then wsOrig.reverse else wsDiff.reverse) ++ acc
  | borrow, [], [], acc, _ => by
    cases borrow <;> simp [muxRevLoop]
  | borrow, d :: wsDiff, a :: wsOrig, acc, hlen => by
    have hlen' : wsDiff.length = wsOrig.length := by simpa using hlen
    rw [muxRevLoop, muxRevLoop_eq_ite borrow wsDiff wsOrig _ hlen']
    cases borrow <;> simp [List.reverse_cons, List.append_assoc]

/-- Second pass of `tmUniformCondSubStep`: pops equal-length `wsDiff` (`kWork2`) and `wsOrig`
(`kWork3`) in lockstep, pushes the multiplexed stream `(if r.borrow then wsOrig.reverse else wsDiff.reverse)`
onto `kIO`, pushes `[!r.borrow]` onto `kWork0`, and halts in `3 * wsDiff.length + 2` steps. -/
def tmUniformCondSubStep_pass2_evalsToInTime :
    ∀ (wsDiff wsOrig acc : List Bool) (_hlen : wsDiff.length = wsOrig.length) (r : ButterflyReg),
      Turing.EvalsToInTime tmUniformCondSubStep.step
        ⟨some .popMuxDiff, r, fiveTapeWorkStk acc [] [] wsDiff wsOrig⟩
        (some ⟨none, default,
          fiveTapeWorkStk (muxRevLoop r.borrow wsDiff wsOrig acc) [!r.borrow] [] [] []⟩)
        (3 * wsDiff.length + 2)
  | [], [], acc, _, r => by
    rcases r with ⟨bitA, bitB, carry, borrow⟩
    have hstep1 : tmUniformCondSubStep.step
        ⟨some .popMuxDiff, ⟨bitA, bitB, carry, borrow⟩, fiveTapeWorkStk acc [] [] [] []⟩ =
        some ⟨some .pushQuotBit, ⟨false, false, false, borrow⟩,
          fiveTapeWorkStk acc [] [] [] []⟩ := by
      simp only [tmUniformCondSubStep, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux, fiveTapeWorkStk_kWork2, update_fiveTapeWorkStk_kWork2,
        List.head?_nil, List.tail_nil, cond_false]
    have hstep2 : tmUniformCondSubStep.step
        ⟨some .pushQuotBit, ⟨false, false, false, borrow⟩, fiveTapeWorkStk acc [] [] [] []⟩ =
        some ⟨none, default, fiveTapeWorkStk acc [!borrow] [] [] []⟩ := by
      simp only [tmUniformCondSubStep, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux, fiveTapeWorkStk_kWork0, update_fiveTapeWorkStk_kWork0]
    exact EvalsToInTime.of_step hstep1 (EvalsToInTime.step_one hstep2)
  | d :: wsDiff, a :: wsOrig, acc, hlen, r => by
    rcases r with ⟨bitA, bitB, carry, borrow⟩
    have hlen' : wsDiff.length = wsOrig.length := by simpa using hlen
    have hstep1 : tmUniformCondSubStep.step
        ⟨some .popMuxDiff, ⟨bitA, bitB, carry, borrow⟩,
          fiveTapeWorkStk acc [] [] (d :: wsDiff) (a :: wsOrig)⟩ =
        some ⟨some .popMuxOrig, ⟨bitA, d, true, borrow⟩,
          fiveTapeWorkStk acc [] [] wsDiff (a :: wsOrig)⟩ := by
      simp [tmUniformCondSubStep, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformCondSubStep.step
        ⟨some .popMuxOrig, ⟨bitA, d, true, borrow⟩,
          fiveTapeWorkStk acc [] [] wsDiff (a :: wsOrig)⟩ =
        some ⟨some .pushMuxIO, ⟨if borrow then a else d, false, false, borrow⟩,
          fiveTapeWorkStk acc [] [] wsDiff wsOrig⟩ := by
      simp [tmUniformCondSubStep, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep3 : tmUniformCondSubStep.step
        ⟨some .pushMuxIO, ⟨if borrow then a else d, false, false, borrow⟩,
          fiveTapeWorkStk acc [] [] wsDiff wsOrig⟩ =
        some ⟨some .popMuxDiff, ⟨if borrow then a else d, false, false, borrow⟩,
          fiveTapeWorkStk ((if borrow then a else d) :: acc) [] [] wsDiff wsOrig⟩ := by
      simp [tmUniformCondSubStep, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformCondSubStep_pass2_evalsToInTime wsDiff wsOrig
      ((if borrow then a else d) :: acc) hlen'
      ⟨if borrow then a else d, false, false, borrow⟩
    dsimp only [muxRevLoop]
    exact EvalsToInTime.mono
      (EvalsToInTime.of_step hstep1
        (EvalsToInTime.of_step hstep2
          (EvalsToInTime.of_step hstep3 ih)))
      (by simp [List.length_cons]; omega)

/-- Exact characterization of `rippleSubFinalBorrow` on `w`-bit unsigned operands `R, D < 2 ^ w`:
the final borrow bit is `decide (R < D)` (`false` iff `D ≤ R`). -/
@[simp]
theorem rippleSubFinalBorrow_encodeNatBits (w R D : ℕ) (hR : R < 2 ^ w) (hD : D < 2 ^ w) :
    rippleSubFinalBorrow (encodeNatBits w R) (encodeNatBits w D) false = decide (R < D) := by
  have hlen : (encodeNatBits w R).length = (encodeNatBits w D).length := by simp
  have hout_len : (rippleSubStream (encodeNatBits w R) (encodeNatBits w D) false).length = w := by
    rw [length_rippleSubStream _ _ hlen false, encodeNatBits_length]
  have hlt : decodeNatBits (rippleSubStream (encodeNatBits w R) (encodeNatBits w D) false) < 2 ^ w := by
    have h := decodeNatBits_lt (rippleSubStream (encodeNatBits w R) (encodeNatBits w D) false)
    rwa [hout_len] at h
  have hsem := decodeNatBits_rippleSubStream (encodeNatBits w R) (encodeNatBits w D) hlen false
  rw [decodeNatBits_encodeNatBits w R hR, decodeNatBits_encodeNatBits w D hD,
    encodeNatBits_length] at hsem
  have hf0 : false.toNat = 0 := rfl
  rw [hf0, add_zero] at hsem
  cases hbf : rippleSubFinalBorrow (encodeNatBits w R) (encodeNatBits w D) false
  · rw [hbf] at hsem
    have hf : (false : Bool).toNat = 0 := rfl
    rw [hf, mul_zero, add_zero] at hsem
    have hnot : ¬ (R < D) := by omega
    simp [hnot]
  · rw [hbf] at hsem
    have ht : (true : Bool).toNat = 1 := rfl
    rw [ht, mul_one] at hsem
    have hRD : R < D := by omega
    simp [hRD]

/-- Concrete evaluation of the single uniform machine `tmUniformCondSubStep` on any `w`-bit natural
numbers `R, D < 2 ^ w`, computing the conditional remainder
`encodeNatBits w (if D ≤ R then R - D else R)` on `kIO` and quotient/root bit `[decide (D ≤ R)]`
on `kWork0` in `7 * w + 3` single-bit `FinTM2` steps. -/
def tmUniformCondSubStep_encodeNatBits_evalsToInTime_concrete (w R D : ℕ)
    (hR : R < 2 ^ w) (hD : D < 2 ^ w) :
    Turing.EvalsToInTime tmUniformCondSubStep.step
      ⟨some .popA, default, threeTapeWorkStk [] (encodeNatBits w R) (encodeNatBits w D)⟩
      (some ⟨none, default,
        twoTapeStk (encodeNatBits w (if D ≤ R then R - D else R)) [decide (D ≤ R)]⟩)
      (7 * w + 3) := by
  set xs := encodeNatBits w R
  set ys := encodeNatBits w D
  have hlen : xs.length = ys.length := by simp [xs, ys]
  have hinit : (⟨some .popA, default, threeTapeWorkStk [] xs ys⟩ : tmUniformCondSubStep.Cfg) =
      ⟨some .popA, default, fiveTapeWorkStk [] xs ys [] []⟩ := by
    rw [fiveTapeWorkStk_nil, fourTapeWorkStk_nil]
  have hp1 := tmUniformCondSubStep_pass1_evalsToInTime xs ys [] [] hlen default
  rw [List.append_nil] at hp1
  have hlen_p2 : (rippleSubRevLoop xs ys false []).length = xs.reverse.length := by
    simp [length_rippleSubRevLoop xs ys hlen false []]
  have hp2 := tmUniformCondSubStep_pass2_evalsToInTime
    (rippleSubRevLoop xs ys false []) xs.reverse [] hlen_p2
    { bitA := false
      bitB := false
      carry := false
      borrow := rippleSubFinalBorrow xs ys false }
  have hlen_sub : (rippleSubRevLoop xs ys false []).length = w := by
    simpa [xs] using length_rippleSubRevLoop xs ys hlen false []
  have hlen_xs : xs.length = w := by simp [xs]
  rw [hlen_xs] at hp1
  rw [hlen_sub] at hp2
  have hmux :
      muxRevLoop (rippleSubFinalBorrow xs ys false) (rippleSubRevLoop xs ys false []) xs.reverse [] =
        encodeNatBits w (if D ≤ R then R - D else R) := by
    rw [muxRevLoop_eq_ite _ _ _ [] hlen_p2, List.append_nil, List.reverse_reverse,
      reverse_rippleSubRevLoop xs ys hlen false [], List.reverse_nil, List.nil_append,
      rippleSubFinalBorrow_encodeNatBits w R D hR hD]
    by_cases hDR : D ≤ R
    · have hnot : ¬ (R < D) := not_lt.mpr hDR
      simp [hDR, hnot, xs, ys, rippleSubStream_encodeNatBits w R D hDR hR]
    · have hlt : R < D := not_le.mp hDR
      simp [hDR, hlt, xs]
  have hqbit : (!rippleSubFinalBorrow xs ys false) = decide (D ≤ R) := by
    rw [rippleSubFinalBorrow_encodeNatBits w R D hR hD]
    by_cases hDR : D ≤ R
    · have hnot : ¬ (R < D) := not_lt.mpr hDR
      simp [hDR, hnot]
    · have hlt : R < D := not_le.mp hDR
      simp [hDR, hlt]
  have hhalt :
      (⟨none, default,
        fiveTapeWorkStk
          (muxRevLoop (rippleSubFinalBorrow xs ys false) (rippleSubRevLoop xs ys false []) xs.reverse [])
          [!(rippleSubFinalBorrow xs ys false)] [] [] []⟩ : tmUniformCondSubStep.Cfg) =
      ⟨none, default,
        twoTapeStk (encodeNatBits w (if D ≤ R then R - D else R)) [decide (D ≤ R)]⟩ := by
    rw [hmux, hqbit, fiveTapeWorkStk_nil, fourTapeWorkStk_nil, threeTapeWorkStk_nil]
  rw [hinit, ← hhalt]
  exact EvalsToInTime.mono (EvalsToInTime.trans' hp1 hp2) (by omega)

/-- Unconditional existential step bound and exact functional correctness for the single uniform
conditional subtract-mux machine `tmUniformCondSubStep` on `w`-bit operands `R, D < 2 ^ w`. -/
theorem tmUniformCondSubStep_encodeNatBits_evalsToInTime (w R D : ℕ)
    (hR : R < 2 ^ w) (hD : D < 2 ^ w) :
    ∃ t ≤ 7 * w + 3,
      Turing.EvalsToInTime tmUniformCondSubStep.step
        ⟨some .popA, default, threeTapeWorkStk [] (encodeNatBits w R) (encodeNatBits w D)⟩
        (some ⟨none, default,
          twoTapeStk (encodeNatBits w (if D ≤ R then R - D else R)) [decide (D ≤ R)]⟩) t :=
  ⟨_, le_rfl, ⟨tmUniformCondSubStep_encodeNatBits_evalsToInTime_concrete w R D hR hD⟩⟩

/-! ### 1.11 Uniform 1-Pass Radix-2 Bit-Interleaving Shuffle Machine (`tmUniformInterleave`) -/

/-- Control labels for the uniform single-machine bit-interleaving `FinTM2` (`|Λ| = 6`). -/
inductive InterleaveLabel : Type
  | popEven
  | popOdd
  | pushEvenRev
  | pushOddRev
  | popRev
  | pushIO
  deriving DecidableEq, Repr, Inhabited

/-- Explicit equivalence `InterleaveLabel ≃ Fin 6` witnessing `Fintype.card InterleaveLabel = 6`. -/
def interleaveLabelEquiv : InterleaveLabel ≃ Fin 6 where
  toFun
    | .popEven => ⟨0, by decide⟩
    | .popOdd => ⟨1, by decide⟩
    | .pushEvenRev => ⟨2, by decide⟩
    | .pushOddRev => ⟨3, by decide⟩
    | .popRev => ⟨4, by decide⟩
    | .pushIO => ⟨5, by decide⟩
  invFun
    | ⟨0, _⟩ => .popEven
    | ⟨1, _⟩ => .popOdd
    | ⟨2, _⟩ => .pushEvenRev
    | ⟨3, _⟩ => .pushOddRev
    | ⟨4, _⟩ => .popRev
    | ⟨_ + 5, _⟩ => .pushIO
  left_inv x := by cases x <;> rfl
  right_inv i := by
    rcases i with ⟨_ | _ | _ | _ | _ | _ | n, hi⟩ <;> try rfl
    omega

instance : Fintype InterleaveLabel :=
  Fintype.ofEquiv (Fin 6) interleaveLabelEquiv.symm

@[simp]
theorem card_interleaveLabel : Fintype.card InterleaveLabel = 6 := by decide

/-- **Single Uniform Bit-Interleaving Shuffle Machine (`tmUniformInterleave`)**:
A single uniform 8-stack binary `FinTM2` machine (`|Λ| = 6`, `|σ| = 8`, `|Γ k₀| = 2`, zero length parameters)
that pops two equal-length bitstreams `ps.map Prod.fst` (`kWork0`) and `ps.map Prod.snd` (`kWork1`)
one bit at a time, pushes the reversed interleaved stream `(flattenBitPairs ps).reverse` onto `kWork2`,
and reverses onto `kIO` to output `flattenBitPairs ps` in `8 * ps.length + 2` `TM2.step` transitions. -/
def tmUniformInterleave : Turing.FinTM2 :=
  mkBitFinTM2 InterleaveLabel .popEven UniformReg default (fun lbl =>
    match lbl with
    | .popEven =>
      Turing.TM2.Stmt.pop kWork0
        (fun r bOpt =>
          match bOpt with
          | some a => { r with bitA := a, carry := true }
          | none => default)
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .popOdd))
          (Turing.TM2.Stmt.goto (fun _ => .popRev)))
    | .popOdd =>
      Turing.TM2.Stmt.pop kWork1
        (fun r bOpt =>
          { bitA := r.bitA, bitB := bOpt.getD false, carry := false })
        (Turing.TM2.Stmt.goto (fun _ => .pushEvenRev))
    | .pushEvenRev =>
      Turing.TM2.Stmt.push kWork2 (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .pushOddRev))
    | .pushOddRev =>
      Turing.TM2.Stmt.push kWork2 (fun r => r.bitB)
        (Turing.TM2.Stmt.goto (fun _ => .popEven))
    | .popRev =>
      Turing.TM2.Stmt.pop kWork2
        (fun _ bOpt =>
          match bOpt with
          | some b => { bitA := b, bitB := false, carry := true }
          | none => default)
        (Turing.TM2.Stmt.branch (fun r => r.carry)
          (Turing.TM2.Stmt.goto (fun _ => .pushIO))
          Turing.TM2.Stmt.halt)
    | .pushIO =>
      Turing.TM2.Stmt.push kIO (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .popRev)))

/-- `tmUniformInterleave` satisfies `IsUniformFinTM2 tmUniformInterleave 6 8 2`. -/
theorem isUniformFinTM2_tmUniformInterleave : IsUniformFinTM2 tmUniformInterleave 6 8 2 :=
  isUniformFinTM2_mkBitFinTM2 _ _ _ (by decide) (by decide) (by decide)

/-- First pass of `tmUniformInterleave`: pops `ps.map Prod.fst` (`kWork0`) and `ps.map Prod.snd`
(`kWork1`) one pair at a time, pushing `(flattenBitPairs ps).reverse ++ acc` onto `kWork2` in
`4 * ps.length + 1` steps. -/
def tmUniformInterleave_pass1_evalsToInTime :
    ∀ (ps : List (Bool × Bool)) (acc : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmUniformInterleave.step
        ⟨some .popEven, r, fourTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd) acc⟩
        (some ⟨some .popRev, default,
          fourTapeWorkStk [] [] [] ((flattenBitPairs ps).reverse ++ acc)⟩)
        (4 * ps.length + 1)
  | [], acc, r => by
    refine EvalsToInTime.step_one ?_
    simp [tmUniformInterleave, flattenBitPairs, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux]
  | (a, b) :: ps, acc, r => by
    rcases r with ⟨bitA, bitB, carry⟩
    have hstep1 : tmUniformInterleave.step
        ⟨some .popEven, ⟨bitA, bitB, carry⟩,
          fourTapeWorkStk [] (a :: ps.map Prod.fst) (b :: ps.map Prod.snd) acc⟩ =
        some ⟨some .popOdd, ⟨a, bitB, true⟩,
          fourTapeWorkStk [] (ps.map Prod.fst) (b :: ps.map Prod.snd) acc⟩ := by
      simp [tmUniformInterleave, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformInterleave.step
        ⟨some .popOdd, ⟨a, bitB, true⟩,
          fourTapeWorkStk [] (ps.map Prod.fst) (b :: ps.map Prod.snd) acc⟩ =
        some ⟨some .pushEvenRev, ⟨a, b, false⟩,
          fourTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd) acc⟩ := by
      simp [tmUniformInterleave, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep3 : tmUniformInterleave.step
        ⟨some .pushEvenRev, ⟨a, b, false⟩,
          fourTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd) acc⟩ =
        some ⟨some .pushOddRev, ⟨a, b, false⟩,
          fourTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd) (a :: acc)⟩ := by
      simp [tmUniformInterleave, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep4 : tmUniformInterleave.step
        ⟨some .pushOddRev, ⟨a, b, false⟩,
          fourTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd) (a :: acc)⟩ =
        some ⟨some .popEven, ⟨a, b, false⟩,
          fourTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd) (b :: a :: acc)⟩ := by
      simp [tmUniformInterleave, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformInterleave_pass1_evalsToInTime ps (b :: a :: acc) ⟨a, b, false⟩
    have hrev : (flattenBitPairs ((a, b) :: ps)).reverse ++ acc =
        (flattenBitPairs ps).reverse ++ (b :: a :: acc) := by
      simp [flattenBitPairs, List.reverse_cons, List.append_assoc]
    rw [List.map_cons, List.map_cons, hrev]
    exact EvalsToInTime.mono
      (EvalsToInTime.of_step hstep1
        (EvalsToInTime.of_step hstep2
          (EvalsToInTime.of_step hstep3
            (EvalsToInTime.of_step hstep4 ih))))
      (by simp [List.length_cons]; omega)

/-- Second pass of `tmUniformInterleave`: pops `ws` from `kWork2` and pushes `ws.reverse` onto `kIO`
in `2 * ws.length + 1` steps, halting with `default` register state. -/
def tmUniformInterleave_pass2_evalsToInTime :
    ∀ (ws acc : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmUniformInterleave.step
        ⟨some .popRev, r, fourTapeWorkStk acc [] [] ws⟩
        (some ⟨none, default, fourTapeWorkStk (ws.reverse ++ acc) [] [] []⟩)
        (2 * ws.length + 1)
  | [], acc, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformInterleave, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux, fourTapeWorkStk_kWork2, update_fourTapeWorkStk_kWork2,
      uniformReg_default_carry, List.head?_nil, List.tail_nil, List.reverse_nil,
      List.nil_append, cond_false]
  | b :: ws, acc, r => by
    have hstep1 : tmUniformInterleave.step
        ⟨some .popRev, r, fourTapeWorkStk acc [] [] (b :: ws)⟩ =
        some ⟨some .pushIO, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk acc [] [] ws⟩ := by
      simp [tmUniformInterleave, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformInterleave.step
        ⟨some .pushIO, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk acc [] [] ws⟩ =
        some ⟨some .popRev, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk (b :: acc) [] [] ws⟩ := by
      simp [tmUniformInterleave, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformInterleave_pass2_evalsToInTime ws (b :: acc)
      { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step hstep1 (EvalsToInTime.of_step hstep2 ih))
      (by simp [List.length_cons]; omega)

/-- Concrete evaluation of `tmUniformInterleave` on `ps.map Prod.fst` (`kWork0`) and
`ps.map Prod.snd` (`kWork1`) in `8 * ps.length + 2` steps, producing `flattenBitPairs ps` on `kIO`. -/
def tmUniformInterleave_evalsToInTime_concrete (ps : List (Bool × Bool)) :
    Turing.EvalsToInTime tmUniformInterleave.step
      ⟨some .popEven, default, threeTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd)⟩
      (some (Turing.haltList tmUniformInterleave (flattenBitPairs ps)))
      (8 * ps.length + 2) := by
  have hinit :
      (⟨some .popEven, default, threeTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd)⟩ :
        tmUniformInterleave.Cfg) =
      ⟨some .popEven, default, fourTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd) []⟩ := by
    rw [fourTapeWorkStk_nil]
  have hhalt : Turing.haltList tmUniformInterleave (flattenBitPairs ps) =
      ⟨none, default,
        fourTapeWorkStk (((flattenBitPairs ps).reverse).reverse ++ []) [] [] []⟩ := by
    rw [List.reverse_reverse, List.append_nil, fourTapeWorkStk_nil, threeTapeWorkStk_nil,
      twoTapeStk_nil]
    rfl
  rw [hinit, hhalt]
  have hp1 := tmUniformInterleave_pass1_evalsToInTime ps [] default
  rw [List.append_nil] at hp1
  have hp2 := tmUniformInterleave_pass2_evalsToInTime (flattenBitPairs ps).reverse [] default
  have hlen : (flattenBitPairs ps).reverse.length = 2 * ps.length := by simp
  rw [hlen] at hp2
  exact EvalsToInTime.mono (EvalsToInTime.trans' hp1 hp2) (by omega)

/-- Unconditional existential step bound and exact functional correctness for `tmUniformInterleave`. -/
theorem tmUniformInterleave_evalsToInTime (ps : List (Bool × Bool)) :
    ∃ t ≤ 8 * ps.length + 2,
      Turing.EvalsToInTime tmUniformInterleave.step
        ⟨some .popEven, default, threeTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd)⟩
        (some (Turing.haltList tmUniformInterleave (flattenBitPairs ps))) t :=
  ⟨_, le_rfl, ⟨tmUniformInterleave_evalsToInTime_concrete ps⟩⟩


/-! ## 2. Word / Batch Stack Layouts & Round-Trip Lemmas -/

/-! ### 2.1 Natural Number Bit Encodings (`encodeNatBits`, `decodeNatBits`, `encodeInputBits`) -/

@[simp]
theorem length_encodeNatBits (w x : ℕ) : (encodeNatBits w x).length = w := by
  simp [encodeNatBits]

@[simp]
theorem length_encodeInputBits (n A B : ℕ) :
    (encodeInputBits n A B).length = 2 * n := by
  simp [encodeInputBits, Nat.two_mul]

@[simp]
theorem take_encodeInputBits (n A B : ℕ) :
    (encodeInputBits n A B).take n = encodeNatBits n A := by
  simp [encodeInputBits]

@[simp]
theorem drop_encodeInputBits (n A B : ℕ) :
    (encodeInputBits n A B).drop n = encodeNatBits n B := by
  simp [encodeInputBits]

/-! ### 2.2 Fixed-Width Signed Word & FixedComplex Encodings -/

/-- Internalized extraction of `|m| < 2^w` from `FitsSignedWord w m`. -/
theorem FitsSignedWord.abs_lt {w : ℕ} {m : ℤ} (hm : FitsSignedWord w m) :
    |m| < (2 : ℤ) ^ w := hm

/-- Internalized lower bound `-2^w < m` from `FitsSignedWord w m`. -/
theorem FitsSignedWord.neg_pow_lt {w : ℕ} {m : ℤ} (hm : FitsSignedWord w m) :
    -((2 : ℤ) ^ w) < m :=
  (_root_.abs_lt.mp hm).1

/-- Internalized upper bound `m < 2^w` from `FitsSignedWord w m`. -/
theorem FitsSignedWord.lt_pow {w : ℕ} {m : ℤ} (hm : FitsSignedWord w m) :
    m < (2 : ℤ) ^ w :=
  (_root_.abs_lt.mp hm).2

/-- Internalized real-part bound from `WordWidthBounds w z`. -/
theorem WordWidthBounds.re_fits {w q : ℕ} {z : FixedComplex q} (hz : WordWidthBounds w z) :
    FitsSignedWord w z.re := hz.1

/-- Internalized imaginary-part bound from `WordWidthBounds w z`. -/
theorem WordWidthBounds.im_fits {w q : ℕ} {z : FixedComplex q} (hz : WordWidthBounds w z) :
    FitsSignedWord w z.im := hz.2

/-- Internalized real-part magnitude bound `|z.re| < 2^w` from `WordWidthBounds w z`. -/
theorem WordWidthBounds.re_abs_lt {w q : ℕ} {z : FixedComplex q} (hz : WordWidthBounds w z) :
    |z.re| < (2 : ℤ) ^ w := hz.1

/-- Internalized imaginary-part magnitude bound `|z.im| < 2^w` from `WordWidthBounds w z`. -/
theorem WordWidthBounds.im_abs_lt {w q : ℕ} {z : FixedComplex q} (hz : WordWidthBounds w z) :
    |z.im| < (2 : ℤ) ^ w := hz.2

/-- Bit-width `w + 1` of an encoded signed word with `w` magnitude bits. -/
def signedWordBits (w : ℕ) : ℕ := w + 1

/-- Fixed-width `(w + 1)`-bit offset-binary encoding of a signed integer `m : ℤ` with
`FitsSignedWord w m` (`|m| < 2^w`). -/
def encodeSignedWord (w : ℕ) (m : ℤ) : List Bool :=
  encodeNatBits (w + 1) (m + (2 : ℤ) ^ w).toNat

/-- Decode a `(w + 1)`-bit encoded signed word back to `ℤ`. -/
def decodeSignedWord (w : ℕ) (bs : List Bool) : ℤ :=
  (decodeNatBits (bs.take (w + 1)) : ℤ) - (2 : ℤ) ^ w

@[simp]
theorem length_encodeSignedWord (w : ℕ) (m : ℤ) :
    (encodeSignedWord w m).length = w + 1 := by
  simp [encodeSignedWord]

@[simp]
theorem decodeSignedWord_append (w : ℕ) (bs rest : List Bool) (h : bs.length = w + 1) :
    decodeSignedWord w (bs ++ rest) = decodeSignedWord w bs := by
  simp [decodeSignedWord, List.take_append_of_le_length (le_of_eq h.symm)]

/-- Exact round-trip theorem for signed words under `FitsSignedWord w m`. -/
theorem decodeSignedWord_encodeSignedWord (w : ℕ) (m : ℤ) (hm : FitsSignedWord w m) :
    decodeSignedWord w (encodeSignedWord w m) = m := by
  have h1 : -((2 : ℤ) ^ w) < m := hm.neg_pow_lt
  have h2 : m < (2 : ℤ) ^ w := hm.lt_pow
  have hnonneg : 0 ≤ m + (2 : ℤ) ^ w := by omega
  have hlt_int : m + (2 : ℤ) ^ w < (2 : ℤ) ^ (w + 1) := by
    rw [pow_succ]
    omega
  have hlt_nat : (m + (2 : ℤ) ^ w).toNat < 2 ^ (w + 1) := by
    zify
    rw [Int.toNat_of_nonneg hnonneg]
    exact hlt_int
  unfold decodeSignedWord encodeSignedWord
  rw [List.take_of_length_le (by simp), decodeNatBits_encodeNatBits (w + 1) _ hlt_nat]
  rw [Int.toNat_of_nonneg hnonneg]
  ring

/-- Bit-width `2 * (w + 1)` of an encoded `FixedComplex q` word with `w` magnitude bits per coordinate. -/
def complexWordBits (w : ℕ) : ℕ := 2 * (w + 1)

/-- Fixed-width `2 * (w + 1)`-bit encoding of `z : FixedComplex q`. -/
def encodeFixedComplex (w : ℕ) {q : ℕ} (z : FixedComplex q) : List Bool :=
  encodeSignedWord w z.re ++ encodeSignedWord w z.im

/-- Decode a `2 * (w + 1)`-bit slice into `FixedComplex q`. -/
def decodeFixedComplex (w q : ℕ) (bs : List Bool) : FixedComplex q where
  re := decodeSignedWord w (bs.take (w + 1))
  im := decodeSignedWord w ((bs.drop (w + 1)).take (w + 1))

@[simp]
theorem length_encodeFixedComplex (w : ℕ) {q : ℕ} (z : FixedComplex q) :
    (encodeFixedComplex w z).length = complexWordBits w := by
  simp [encodeFixedComplex, complexWordBits, Nat.two_mul]

@[simp]
theorem decodeFixedComplex_append (w q : ℕ) (bs rest : List Bool)
    (h : bs.length = complexWordBits w) :
    decodeFixedComplex w q (bs ++ rest) = decodeFixedComplex w q bs := by
  have hlen : bs.length = 2 * (w + 1) := h
  have h1 : w + 1 ≤ bs.length := by omega
  have h2 : w + 1 ≤ (bs.drop (w + 1)).length := by
    simp [hlen]
    omega
  unfold decodeFixedComplex
  congr 1
  · rw [List.take_append_of_le_length h1]
  · rw [List.drop_append_of_le_length h1, List.take_append_of_le_length h2]

/-- Exact round-trip theorem for `FixedComplex q` words under `WordWidthBounds w z`. -/
theorem decodeFixedComplex_encodeFixedComplex (w : ℕ) {q : ℕ} (z : FixedComplex q)
    (hz : WordWidthBounds w z) :
    decodeFixedComplex w q (encodeFixedComplex w z) = z := by
  ext
  · unfold decodeFixedComplex encodeFixedComplex
    dsimp only
    rw [List.take_append_of_le_length (le_of_eq (length_encodeSignedWord w z.re).symm),
      List.take_of_length_le (le_of_eq (length_encodeSignedWord w z.re)),
      decodeSignedWord_encodeSignedWord w z.re hz.re_fits]
  · unfold decodeFixedComplex encodeFixedComplex
    dsimp only
    rw [List.drop_append,
      List.drop_eq_nil_of_le (le_of_eq (length_encodeSignedWord w z.re)),
      List.nil_append, length_encodeSignedWord, Nat.sub_self, List.drop,
      List.take_of_length_le (le_of_eq (length_encodeSignedWord w z.im)),
      decodeSignedWord_encodeSignedWord w z.im hz.im_fits]

/-! ### 2.3 Batch & Subproblem-Major Layouts and Round-Trip Equivalence -/

/-- General fixed-width slice recovery from `(List.ofFn f).flatten`. -/
theorem drop_take_flatten_ofFn {n : ℕ} {α : Type*} (L : ℕ) (f : Fin n → List α)
    (hL : ∀ i : Fin n, (f i).length = L) (i : Fin n) :
    (((List.ofFn f).flatten).drop (i.val * L)).take L = f i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ ?_ i
    · simp [List.take_append_of_le_length (le_of_eq (hL 0).symm),
        List.take_of_length_le (le_of_eq (hL 0))]
    · intro j
      simp only [Fin.val_succ, Nat.add_mul, Nat.one_mul]
      have hlen0 : (f 0).length ≤ j.val * L + L := by
        rw [hL 0]
        exact Nat.le_add_left L (j.val * L)
      rw [List.drop_append,
        List.drop_eq_nil_of_le hlen0, List.nil_append, hL 0, Nat.add_sub_cancel]
      exact ih (fun k => f k.succ) (fun k => hL k.succ) j

/-- Length of `(List.ofFn f).flatten` when every block `f i` has fixed length `L`. -/
theorem length_flatten_ofFn {n : ℕ} {α : Type*} (L : ℕ) (f : Fin n → List α)
    (hL : ∀ i : Fin n, (f i).length = L) :
    ((List.ofFn f).flatten).length = n * L := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hL 0,
      ih (fun k => f k.succ) (fun k => hL k.succ), Nat.succ_mul, Nat.add_comm]

/-- List of encoded fixed-width complex words for a 1D batch `v : Fin R → FixedComplex q`. -/
def batchWords {R q : ℕ} (w : ℕ) (v : Fin R → FixedComplex q) : List (List Bool) :=
  List.ofFn (fun i : Fin R => encodeFixedComplex w (v i))

/-- Flattened bit-list encoding of a 1D batch `v : Fin R → FixedComplex q`. -/
def encodeBatchWords {R q : ℕ} (w : ℕ) (v : Fin R → FixedComplex q) : List Bool :=
  (batchWords w v).flatten

/-- Decode a flattened bit-list into a 1D batch `Fin R → FixedComplex q`. -/
def decodeBatchWords (R w q : ℕ) (bs : List Bool) : Fin R → FixedComplex q :=
  fun i => decodeFixedComplex w q ((bs.drop (i.val * complexWordBits w)).take (complexWordBits w))

@[simp]
theorem length_encodeBatchWords {R q : ℕ} (w : ℕ) (v : Fin R → FixedComplex q) :
    (encodeBatchWords w v).length = R * complexWordBits w := by
  unfold encodeBatchWords batchWords
  exact length_flatten_ofFn (complexWordBits w) _ (fun i => length_encodeFixedComplex w (v i))

/-- Exact round-trip theorem for 1D batch word encoding under `WordWidthBounds`. -/
theorem decodeBatchWords_encodeBatchWords {R q : ℕ} (w : ℕ)
    (v : Fin R → FixedComplex q) (hv : ∀ i : Fin R, WordWidthBounds w (v i)) :
    decodeBatchWords R w q (encodeBatchWords w v) = v := by
  funext i
  unfold decodeBatchWords encodeBatchWords batchWords
  rw [drop_take_flatten_ofFn (complexWordBits w) (fun j => encodeFixedComplex w (v j))
    (fun j => length_encodeFixedComplex w (v j)) i]
  exact decodeFixedComplex_encodeFixedComplex w (v i) (hv i)

/-- Flatten a batch of `S` subproblems of size `R` (`Fin S → Fin R → α`) into a single
subproblem-major vector `Fin (S * R) → α`. -/
def ofBatch {S R : ℕ} {α : Type*} (B : Fin S → Fin R → α) : Fin (S * R) → α :=
  fun k =>
    have hR : 0 < R := by
      by_contra h
      have h0 : R = 0 := by omega
      have hk := k.isLt
      simp [h0] at hk
    B ⟨k.val / R, (Nat.div_lt_iff_lt_mul hR).mpr k.isLt⟩ ⟨k.val % R, Nat.mod_lt k.val hR⟩

/-- Unflatten a subproblem-major vector `Fin (S * R) → α` back into a batch of `S` subproblems of
size `R` (`Fin S → Fin R → α`). -/
def toBatch {S R : ℕ} {α : Type*} (M : Fin (S * R) → α) : Fin S → Fin R → α :=
  fun s j =>
    have hlt : s.val * R + j.val < S * R := by
      calc s.val * R + j.val < s.val * R + R := Nat.add_lt_add_left j.isLt _
        _ = (s.val + 1) * R := by ring
        _ ≤ S * R := Nat.mul_le_mul_right R (Nat.succ_le_of_lt s.isLt)
    M ⟨s.val * R + j.val, hlt⟩

/-- Round-trip identity `toBatch (ofBatch B) = B` converting a batch to subproblem-major layout and
back. -/
@[simp]
theorem subproblemMajorWords_toBatch_ofBatch {S R : ℕ} {α : Type*}
    (B : Fin S → Fin R → α) :
    toBatch (ofBatch B) = B := by
  funext s j
  unfold toBatch ofBatch
  simp only []
  have hj := j.isLt
  have hR : 0 < R := by omega
  have hdiv : (s.val * R + j.val) / R = s.val := by
    rw [Nat.mul_comm s.val R, Nat.mul_add_div hR, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hmod : (s.val * R + j.val) % R = j.val := by
    rw [Nat.mul_comm s.val R, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
  congr 1 <;> exact Fin.ext (by assumption)

/-- Round-trip identity `ofBatch (toBatch M) = M` converting subproblem-major layout to a batch and
back. -/
@[simp]
theorem batch_toSubproblemMajorWords_ofSubproblemMajorWords {S R : ℕ} {α : Type*}
    (M : Fin (S * R) → α) :
    ofBatch (toBatch M) = M := by
  funext k
  unfold ofBatch toBatch
  simp only []
  congr 1
  exact Fin.ext (by
    have h := Nat.div_add_mod k.val R
    linarith [Nat.mul_comm R (k.val / R)])

/-- Encoded bit-list representation of `S` subproblems of size `R` in subproblem-major order. -/
def subproblemMajorWords {S R q : ℕ} (w : ℕ) (B : Fin S → Fin R → FixedComplex q) : List Bool :=
  encodeBatchWords w (ofBatch B)

/-- Decode a subproblem-major bit-list back into `Fin S → Fin R → FixedComplex q`. -/
def decodeSubproblemMajorWords (S R w q : ℕ) (bs : List Bool) : Fin S → Fin R → FixedComplex q :=
  toBatch (decodeBatchWords (S * R) w q bs)

@[simp]
theorem length_subproblemMajorWords {S R q : ℕ} (w : ℕ) (B : Fin S → Fin R → FixedComplex q) :
    (subproblemMajorWords w B).length = (S * R) * complexWordBits w := by
  simp [subproblemMajorWords]

/-- Exact round-trip theorem for `subproblemMajorWords` under `WordWidthBounds`. -/
theorem decodeSubproblemMajorWords_subproblemMajorWords {S R q : ℕ} (w : ℕ)
    (B : Fin S → Fin R → FixedComplex q)
    (hB : ∀ (s : Fin S) (j : Fin R), WordWidthBounds w (B s j)) :
    decodeSubproblemMajorWords S R w q (subproblemMajorWords w B) = B := by
  unfold decodeSubproblemMajorWords subproblemMajorWords
  rw [decodeBatchWords_encodeBatchWords w (ofBatch B)]
  · exact subproblemMajorWords_toBatch_ofBatch B
  · intro k
    unfold ofBatch
    exact hB _ _

/-! ## 3. Out-of-Place Matrix Transpose & Odd-Stride Column Routing (Section 3.4 (`sec:routing`), Section 4.1 (`sec:twisted`), Section 4.2 (`sec:poisson`)) -/

/-! ### 3.1 Matrix Transposition ($t_1 \times r \leftrightarrow r \times t_1$) -/

/-- Injectivity of the transpose target key `i.val * t1 + j.val` on `Fin t1 × Fin r`
(Section 3.4 (`sec:routing`), Lemma 3.3(i) (`lem:routing`)):
each pair `(j, i)` has a unique destination index `i.val * t1 + j.val < r * t1` corresponding
to row `i`, column `j` in `transposeMatrix M`. -/
theorem transposeKey_injective {t1 r : ℕ} (p1 p2 : Fin t1 × Fin r)
    (hkey : p1.2.val * t1 + p1.1.val = p2.2.val * t1 + p2.1.val) :
    p1 = p2 := by
  have hj1 : p1.1.val < t1 := p1.1.isLt
  have hj2 : p2.1.val < t1 := p2.1.isLt
  have ht1 : 0 < t1 := lt_of_le_of_lt (Nat.zero_le _) hj1
  have hmod1 : (p1.2.val * t1 + p1.1.val) % t1 = p1.1.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj1]
  have hmod2 : (p2.2.val * t1 + p2.1.val) % t1 = p2.1.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj2]
  have hj_eq : p1.1.val = p2.1.val := by rw [← hmod1, ← hmod2, hkey]
  have hi_eq : p1.2.val = p2.2.val := by
    have hmul : p1.2.val * t1 = p2.2.val * t1 := by omega
    exact Nat.eq_of_mul_eq_mul_right ht1 hmul
  ext
  · exact hj_eq
  · exact hi_eq

/-- Out-of-place matrix transposition transforming a $t_1 \times r$ matrix `M : Fin t1 → Fin r → α`
into an $r \times t_1$ matrix `Fin r → Fin t1 → α` (Section 3.4 (`sec:routing`), Lemma 3.3(i) (`lem:routing`)). -/
def transposeMatrix {t1 r : ℕ} {α : Type*} (M : Fin t1 → Fin r → α) : Fin r → Fin t1 → α :=
  fun i j => M j i

/-- Exact functional specification of `transposeMatrix` (Lemma 3.3(i) (`lem:routing`)). -/
@[simp]
theorem transposeMatrix_spec {t1 r : ℕ} {α : Type*} (M : Fin t1 → Fin r → α)
    (i : Fin r) (j : Fin t1) :
    transposeMatrix M i j = M j i :=
  rfl

/-- Applying `transposeMatrix` twice is the identity on $t_1 \times r$ matrices. -/
@[simp]
theorem transposeMatrix_transposeMatrix {t1 r : ℕ} {α : Type*} (M : Fin t1 → Fin r → α) :
    transposeMatrix (transposeMatrix M) = M :=
  rfl

/-! ### 3.2 Odd-Stride Column Gather/Scatter and Routing (Section 3.4 (`sec:routing`), Section 4.1 (`sec:twisted`), Section 4.2 (`sec:poisson`)) -/

/-- Stride-$t_1$ modular index $(j_1 + k_2 t_1) \bmod R$ used in Step 1 input de-interleaving
(Theorem 4.2 (`thm:poisson`), equation (17) (`eq:u-ideal`)). -/
def strideModIndex (t1 r R : ℕ) (hR : 0 < R) (j1 : Fin t1) (k2 : Fin r) : Fin R :=
  ⟨(j1.val + k2.val * t1) % R, Nat.mod_lt _ hR⟩

/-- Odd-stride modular index $(u_1 + (2 u_2 + 1) t_1) \bmod R$ (Section 3.4 (`sec:routing`)). -/
def oddStrideModIndex (t1 r R : ℕ) (hR : 0 < R) (u1 : Fin t1) (u2 : Fin r) : Fin R :=
  ⟨(u1.val + (2 * u2.val + 1) * t1) % R, Nat.mod_lt _ hR⟩

/-- Step 2d odd-stride column destination key $u_1 = (2 u_2 - 1) v_1 \bmod t_1$
(Lemma 3.3(ii) (`lem:routing`), Proposition 4.1 (`thm:twisted`), equation (14) (`eq:odd-perm`)). -/
def oddColKeyMinus (t1 : ℕ) (ht1 : 0 < t1) (u2 : ℕ) (v1 : Fin t1) : Fin t1 :=
  ⟨((2 * u2 + t1 - 1) * v1.val) % t1, Nat.mod_lt _ ht1⟩

/-- Odd-stride column destination key $u_1 = (2 u_2 + 1) v_1 \bmod t_1$ (Section 3.4 (`sec:routing`)). -/
def oddColKeyPlus (t1 : ℕ) (ht1 : 0 < t1) (u2 : ℕ) (v1 : Fin t1) : Fin t1 :=
  ⟨((2 * u2 + 1) * v1.val) % t1, Nat.mod_lt _ ht1⟩

/-- Canonical modular inverse of `m` modulo `t1` in `ℕ` computed via Bézout coefficient `Nat.gcdA`. -/
def modInvNat (m t1 : ℕ) : ℕ :=
  (Nat.gcdA m t1 % (t1 : ℤ)).toNat

/-- Whenever `0 < t1` and `Nat.Coprime m t1`, `modInvNat m t1` is a multiplicative inverse of `m`
modulo `t1`. -/
theorem mul_modInvNat_mod (m t1 : ℕ) (ht1 : 0 < t1) (hcop : Nat.Coprime m t1) :
    (m * modInvNat m t1) % t1 = 1 % t1 := by
  have ht1_z : (0 : ℤ) < (t1 : ℤ) := Nat.cast_pos.mpr ht1
  have hnonneg : 0 ≤ Nat.gcdA m t1 % (t1 : ℤ) := Int.emod_nonneg _ (ne_of_gt ht1_z)
  have hbez : (1 : ℤ) = (m : ℤ) * Nat.gcdA m t1 + (t1 : ℤ) * Nat.gcdB m t1 := by
    have h := Nat.gcd_eq_gcd_ab m t1
    rwa [hcop.gcd_eq_one, Nat.cast_one] at h
  zify
  unfold modInvNat
  rw [Int.toNat_of_nonneg hnonneg, Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
  have h1 : (m : ℤ) * Nat.gcdA m t1 = 1 + (t1 : ℤ) * (-Nat.gcdB m t1) := by linarith
  rw [h1, Int.add_mul_emod_self_left]

theorem modInvNat_mul_mod (m t1 : ℕ) (ht1 : 0 < t1) (hcop : Nat.Coprime m t1) :
    (modInvNat m t1 * m) % t1 = 1 % t1 := by
  rw [Nat.mul_comm, mul_modInvNat_mod m t1 ht1 hcop]

/-- For every power of two $t_1 = 2^{k_1}$, the odd multiplier $2 u_2 + t_1 - 1$ is coprime to $t_1$. -/
theorem coprime_oddColMultiplier_two_pow (t1 k1 u2 : ℕ) (hk1 : t1 = 2 ^ k1) :
    Nat.Coprime (2 * u2 + t1 - 1) t1 := by
  subst hk1
  cases k1 with
  | zero =>
    exact Nat.coprime_one_right _
  | succ k =>
    apply Nat.Coprime.pow_right
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
    have hpow : 0 < 2 ^ k := Nat.two_pow_pos k
    have hmod : (2 * u2 + 2 ^ (k + 1) - 1) % 2 = 1 := by
      rw [Nat.pow_succ]
      omega
    rw [hmod]
    rfl

/-- Modular inverse key `v1 = (2 * u2 - 1)⁻¹ * u1 mod t1` inverting `oddColKeyMinus` when $t_1 = 2^{k_1}$
(Lemma 3.3(ii) (`lem:routing`), Proposition 4.1 (`thm:twisted`), Step 5). -/
def oddColKeyMinusInv (t1 : ℕ) (ht1 : 0 < t1) (u2 : ℕ) (u1 : Fin t1) : Fin t1 :=
  ⟨(modInvNat (2 * u2 + t1 - 1) t1 * u1.val) % t1, Nat.mod_lt _ ht1⟩

/-- Right-inverse identity `oddColKeyMinus ∘ oddColKeyMinusInv = id` when $t_1 = 2^{k_1}$. -/
@[simp]
theorem oddColKeyMinus_oddColKeyMinusInv (t1 : ℕ) (ht1 : 0 < t1)
    (ht1_pow : ∃ k1, t1 = 2 ^ k1) (u2 : ℕ) (u1 : Fin t1) :
    oddColKeyMinus t1 ht1 u2 (oddColKeyMinusInv t1 ht1 u2 u1) = u1 := by
  rcases ht1_pow with ⟨k1, hk1⟩
  have hcop := coprime_oddColMultiplier_two_pow t1 k1 u2 hk1
  apply Fin.ext
  unfold oddColKeyMinus oddColKeyMinusInv
  dsimp only
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc,
    Nat.mul_mod ((2 * u2 + t1 - 1) * modInvNat (2 * u2 + t1 - 1) t1),
    mul_modInvNat_mod _ t1 ht1 hcop, ← Nat.mul_mod, Nat.one_mul,
    Nat.mod_eq_of_lt u1.isLt]

/-- Left-inverse identity `oddColKeyMinusInv ∘ oddColKeyMinus = id` when $t_1 = 2^{k_1}$. -/
@[simp]
theorem oddColKeyMinusInv_oddColKeyMinus (t1 : ℕ) (ht1 : 0 < t1)
    (ht1_pow : ∃ k1, t1 = 2 ^ k1) (u2 : ℕ) (v1 : Fin t1) :
    oddColKeyMinusInv t1 ht1 u2 (oddColKeyMinus t1 ht1 u2 v1) = v1 := by
  rcases ht1_pow with ⟨k1, hk1⟩
  have hcop := coprime_oddColMultiplier_two_pow t1 k1 u2 hk1
  apply Fin.ext
  unfold oddColKeyMinus oddColKeyMinusInv
  dsimp only
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc,
    Nat.mul_mod (modInvNat (2 * u2 + t1 - 1) t1 * (2 * u2 + t1 - 1)),
    modInvNat_mul_mod _ t1 ht1 hcop, ← Nat.mul_mod, Nat.one_mul,
    Nat.mod_eq_of_lt v1.isLt]

/-- Step 2d column scatter operator placing $(\hat{q}_{v_1})_{u_2}$ at destination row
$u_1 = (2 u_2 - 1) v_1 \bmod t_1$, so $Y_{(2 u_2 - 1) v_1 \bmod t_1, u_2} = \hat{q}_{v_1, u_2}$
(Lemma 3.3(ii) (`lem:routing`), Proposition 4.1 (`thm:twisted`) Step 5, and Section 7.1 (`sec:alg-spec`) `FastDFT`). -/
def oddColScatter {t1 r : ℕ} (ht1 : 0 < t1) (_ht1_pow : ∃ k1, t1 = 2 ^ k1) {α : Type*}
    (Qhat : Fin t1 → Fin r → α) : Fin t1 → Fin r → α :=
  fun u1 u2 => Qhat (oddColKeyMinusInv t1 ht1 u2.val u1) u2

/-- Step 2d inverse column gather operator reading $Y_{(2 u_2 - 1) v_1 \bmod t_1, u_2}$
(Lemma 3.3(ii) (`lem:routing`), Proposition 4.1 (`thm:twisted`)). -/
def oddColGather {t1 r : ℕ} (ht1 : 0 < t1) {α : Type*} (Y : Fin t1 → Fin r → α) :
    Fin t1 → Fin r → α :=
  fun v1 u2 => Y (oddColKeyMinus t1 ht1 u2.val v1) u2

/-- Alias `oddColRoute` for `oddColGather`. -/
abbrev oddColRoute {t1 r : ℕ} (ht1 : 0 < t1) {α : Type*} (Y : Fin t1 → Fin r → α) :
    Fin t1 → Fin r → α :=
  oddColGather ht1 Y

/-- Exact Step 2d scatter specification in the paper:
`(oddColScatter ht1 ht1_pow Qhat) ((2 * u2 - 1) * v1 mod t1) u2 = Qhat v1 u2`
(Proposition 4.1 (`thm:twisted`) Step 5, Section 7.1 (`sec:alg-spec`) `FastDFT`). -/
@[simp]
theorem oddColScatter_spec {t1 r : ℕ} (ht1 : 0 < t1) (ht1_pow : ∃ k1, t1 = 2 ^ k1)
    {α : Type*} (Qhat : Fin t1 → Fin r → α) (v1 : Fin t1) (u2 : Fin r) :
    oddColScatter ht1 ht1_pow Qhat (oddColKeyMinus t1 ht1 u2.val v1) u2 = Qhat v1 u2 := by
  unfold oddColScatter
  rw [oddColKeyMinusInv_oddColKeyMinus t1 ht1 ht1_pow u2.val v1]

@[simp]
theorem oddColGather_spec {t1 r : ℕ} (ht1 : 0 < t1) {α : Type*}
    (Y : Fin t1 → Fin r → α) (v1 : Fin t1) (u2 : Fin r) :
    oddColGather ht1 Y v1 u2 = Y ⟨((2 * u2.val + t1 - 1) * v1.val) % t1, Nat.mod_lt _ ht1⟩ u2 :=
  rfl

@[simp]
theorem oddColRoute_spec {t1 r : ℕ} (ht1 : 0 < t1) {α : Type*}
    (Y : Fin t1 → Fin r → α) (v1 : Fin t1) (u2 : Fin r) :
    oddColRoute ht1 Y v1 u2 = Y ⟨((2 * u2.val + t1 - 1) * v1.val) % t1, Nat.mod_lt _ ht1⟩ u2 :=
  rfl

/-- Round-trip identity `oddColGather ∘ oddColScatter = id` when $t_1 = 2^{k_1}$. -/
@[simp]
theorem oddColGather_oddColScatter {t1 r : ℕ} (ht1 : 0 < t1) (ht1_pow : ∃ k1, t1 = 2 ^ k1)
    {α : Type*} (Qhat : Fin t1 → Fin r → α) :
    oddColGather ht1 (oddColScatter ht1 ht1_pow Qhat) = Qhat := by
  funext v1 u2
  unfold oddColGather
  exact oddColScatter_spec ht1 ht1_pow Qhat v1 u2

/-- Round-trip identity `oddColScatter ∘ oddColGather = id` when $t_1 = 2^{k_1}$. -/
@[simp]
theorem oddColScatter_oddColGather {t1 r : ℕ} (ht1 : 0 < t1) (ht1_pow : ∃ k1, t1 = 2 ^ k1)
    {α : Type*} (Y : Fin t1 → Fin r → α) :
    oddColScatter ht1 ht1_pow (oddColGather ht1 Y) = Y := by
  funext u1 u2
  unfold oddColScatter oddColGather
  rw [oddColKeyMinus_oddColKeyMinusInv t1 ht1 ht1_pow u2.val u1]

/-- Gather operator transforming a 1D vector `x : Fin R → α` into a $t_1 \times r$ matrix via index
$(j_1 + k_2 t_1) \bmod R$ (Lemma 3.3(i) (`lem:routing`), Theorem 4.2 (`thm:poisson`)). -/
def oddStrideGather (t1 r : ℕ) {R : ℕ} (hR : 0 < R) {α : Type*} (x : Fin R → α) :
    Fin t1 → Fin r → α :=
  fun j1 k2 => x (strideModIndex t1 r R hR j1 k2)

/-- Exact functional specification of `oddStrideGather` for $(j_1 + k_2 t_1) \bmod R$. -/
@[simp]
theorem oddStrideGather_spec (t1 r : ℕ) {R : ℕ} (hR : 0 < R) {α : Type*}
    (x : Fin R → α) (j1 : Fin t1) (k2 : Fin r) :
    oddStrideGather t1 r hR x j1 k2 = x ⟨(j1.val + k2.val * t1) % R, Nat.mod_lt _ hR⟩ :=
  rfl

/-- Scatter operator transforming a $t_1 \times r$ matrix `M : Fin t1 → Fin r → α` back to a 1D
vector `Fin R → α` when `R = t1 * r` (Section 3.4 (`sec:routing`), Lemma 3.3(i) (`lem:routing`)). -/
def oddStrideScatter (t1 r : ℕ) {R : ℕ} (hR : R = t1 * r) {α : Type*}
    (M : Fin t1 → Fin r → α) : Fin R → α :=
  fun idx =>
    have ht1 : 0 < t1 := by
      by_contra h
      have h0 : t1 = 0 := by omega
      have hlt := idx.isLt
      simp [hR, h0] at hlt
    have hk2 : idx.val / t1 < r := by
      rw [Nat.div_lt_iff_lt_mul ht1, Nat.mul_comm]
      exact hR ▸ idx.isLt
    M ⟨idx.val % t1, Nat.mod_lt _ ht1⟩ ⟨idx.val / t1, hk2⟩

/-- Round-trip identity `oddStrideGather ∘ oddStrideScatter = id` when `R = t1 * r`. -/
@[simp]
theorem oddStrideGather_oddStrideScatter (t1 r : ℕ) {R : ℕ} (hR : R = t1 * r) (hR_pos : 0 < R)
    {α : Type*} (M : Fin t1 → Fin r → α) :
    oddStrideGather t1 r hR_pos (oddStrideScatter t1 r hR M) = M := by
  funext j1 k2
  unfold oddStrideGather oddStrideScatter strideModIndex
  simp only []
  have hj1 := j1.isLt
  have hk2 := k2.isLt
  have ht1 : 0 < t1 := by omega
  have hltR : j1.val + k2.val * t1 < R := by
    rw [hR]
    calc j1.val + k2.val * t1 < t1 + k2.val * t1 := Nat.add_lt_add_right hj1 _
      _ = t1 * (k2.val + 1) := by ring
      _ ≤ t1 * r := Nat.mul_le_mul_left t1 (Nat.succ_le_of_lt hk2)
  have hmodR : (j1.val + k2.val * t1) % R = j1.val + k2.val * t1 := Nat.mod_eq_of_lt hltR
  have hmod_t1 : ((j1.val + k2.val * t1) % R) % t1 = j1.val := by
    rw [hmodR, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj1]
  have hdiv_t1 : ((j1.val + k2.val * t1) % R) / t1 = k2.val := by
    rw [hmodR, Nat.add_mul_div_right _ _ ht1, Nat.div_eq_of_lt hj1, Nat.zero_add]
  congr 1 <;> exact Fin.ext (by assumption)

/-- Round-trip identity `oddStrideScatter ∘ oddStrideGather = id` when `R = t1 * r`. -/
@[simp]
theorem oddStrideScatter_oddStrideGather (t1 r : ℕ) {R : ℕ} (hR : R = t1 * r) (hR_pos : 0 < R)
    {α : Type*} (x : Fin R → α) :
    oddStrideScatter t1 r hR (oddStrideGather t1 r hR_pos x) = x := by
  funext idx
  unfold oddStrideScatter oddStrideGather strideModIndex
  simp only []
  congr 1
  apply Fin.ext
  dsimp only
  have hdiv := Nat.div_add_mod idx.val t1
  have hsum : idx.val % t1 + idx.val / t1 * t1 = idx.val := by
    linarith [Nat.mul_comm t1 (idx.val / t1)]
  rw [hsum, Nat.mod_eq_of_lt idx.isLt]

/-- Odd-stride gather operator for $(u_1 + (2 u_2 + 1) t_1) \bmod R$ (Section 3.4 (`sec:routing`)). -/
def oddShiftGather (t1 r : ℕ) {R : ℕ} (hR : 0 < R) {α : Type*} (x : Fin R → α) :
    Fin t1 → Fin r → α :=
  fun u1 u2 => x (oddStrideModIndex t1 r R hR u1 u2)

/-- Exact functional specification of `oddShiftGather` for $(u_1 + (2 u_2 + 1) t_1) \bmod R$. -/
@[simp]
theorem oddShiftGather_spec (t1 r : ℕ) {R : ℕ} (hR : 0 < R) {α : Type*}
    (x : Fin R → α) (u1 : Fin t1) (u2 : Fin r) :
    oddShiftGather t1 r hR x u1 u2 = x ⟨(u1.val + (2 * u2.val + 1) * t1) % R, Nat.mod_lt _ hR⟩ :=
  rfl

/-! ## 4. Full Multi-Level Schedule Encoding Helpers (`LevelScheduleEntry`, schedule (34) (`eq:cert-sched`)) -/

/-- Complete per-level data-independent schedule entry at recursion depth `ell`
(schedule (34) (`eq:cert-sched`), Section 6.3 (`sec:forward-error`), and Section 7.1 (`sec:alg-spec`)). -/
@[ext]
structure LevelScheduleEntry where
  /-- Recursion depth $\ell$. -/
  ell : ℕ
  /-- Level log-length $K_\ell$. -/
  K_ell : ℕ
  /-- Level transform length $R_\ell = 2^{K_\ell}$. -/
  R_ell : ℕ
  /-- Level target precision $p_\ell$. -/
  p_ell : ℕ
  /-- First-axis log-dimension $k_{1,\ell} = \lfloor K_\ell / 2 \rfloor$. -/
  k1_ell : ℕ
  /-- Second-axis log-dimension $k_{2,\ell} = \lceil K_\ell / 2 \rceil$. -/
  k2_ell : ℕ
  /-- First-axis dimension $t_{1,\ell} = 2^{k_{1,\ell}}$. -/
  t1_ell : ℕ
  /-- Second-axis (recursive) dimension $r_\ell = 2^{k_{2,\ell}}$. -/
  r_ell : ℕ
  /-- Working cutoff precision $p_{\text{work},\ell} = p_\ell + K_\ell + 6$. -/
  pWork_ell : ℕ
  /-- Child target precision $p_{\ell+1} = p_{\text{work},\ell} + K_\ell + 6$. -/
  pChild_ell : ℕ
  /-- Child fixed-point quantization precision $q_{\text{child},\ell} = p_{\ell+1} + 2$. -/
  qChild_ell : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Pure data-independent constructor building the level-`ell` schedule entry from `(n, ell)`
via `cSpec n` and the recurrence definitions in `IntMul.Defs` / `IntMul.Schedule`
(schedule (34) (`eq:cert-sched`), Section 6.3 (`sec:forward-error`), and Section 7.1 (`sec:alg-spec`)). -/
def buildLevelScheduleEntry (n ell : ℕ) : LevelScheduleEntry :=
  let spec := cSpec n
  let K := levelK spec.K0 ell
  let R := levelR spec.K0 ell
  let p := levelP spec.K0 spec.p0 ell
  { ell := ell
    K_ell := K
    R_ell := R
    p_ell := p
    k1_ell := k1Ell K
    k2_ell := k2Ell K
    t1_ell := t1Ell K
    r_ell := rEll K
    pWork_ell := pWorkEll K p
    pChild_ell := pChildEll K p
    qChild_ell := qChildEll K p }

@[simp]
theorem buildLevelScheduleEntry_ell (n ell : ℕ) :
    (buildLevelScheduleEntry n ell).ell = ell := rfl

@[simp]
theorem buildLevelScheduleEntry_K_ell (n ell : ℕ) :
    (buildLevelScheduleEntry n ell).K_ell = levelK (rootK0 n) ell := rfl

@[simp]
theorem buildLevelScheduleEntry_R_ell (n ell : ℕ) :
    (buildLevelScheduleEntry n ell).R_ell = levelR (rootK0 n) ell := rfl

@[simp]
theorem buildLevelScheduleEntry_p_ell (n ell : ℕ) :
    (buildLevelScheduleEntry n ell).p_ell = levelP (rootK0 n) (rootP0 n) ell := rfl

@[simp]
theorem buildLevelScheduleEntry_k1_ell (n ell : ℕ) :
    (buildLevelScheduleEntry n ell).k1_ell = k1Ell (levelK (rootK0 n) ell) := rfl

@[simp]
theorem buildLevelScheduleEntry_k2_ell (n ell : ℕ) :
    (buildLevelScheduleEntry n ell).k2_ell = k2Ell (levelK (rootK0 n) ell) := rfl

@[simp]
theorem buildLevelScheduleEntry_t1_ell (n ell : ℕ) :
    (buildLevelScheduleEntry n ell).t1_ell = t1Ell (levelK (rootK0 n) ell) := rfl

@[simp]
theorem buildLevelScheduleEntry_r_ell (n ell : ℕ) :
    (buildLevelScheduleEntry n ell).r_ell = rEll (levelK (rootK0 n) ell) := rfl

@[simp]
theorem buildLevelScheduleEntry_pWork_ell (n ell : ℕ) :
    (buildLevelScheduleEntry n ell).pWork_ell =
      pWorkEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) := rfl

@[simp]
theorem buildLevelScheduleEntry_pChild_ell (n ell : ℕ) :
    (buildLevelScheduleEntry n ell).pChild_ell =
      pChildEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) := rfl

@[simp]
theorem buildLevelScheduleEntry_qChild_ell (n ell : ℕ) :
    (buildLevelScheduleEntry n ell).qChild_ell =
      qChildEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) := rfl

/-- Extract the `i`-th field (`i : Fin 11`) of `e : LevelScheduleEntry`. -/
def levelScheduleFieldVec (e : LevelScheduleEntry) : Fin 11 → ℕ
  | ⟨0, _⟩ => e.ell
  | ⟨1, _⟩ => e.K_ell
  | ⟨2, _⟩ => e.R_ell
  | ⟨3, _⟩ => e.p_ell
  | ⟨4, _⟩ => e.k1_ell
  | ⟨5, _⟩ => e.k2_ell
  | ⟨6, _⟩ => e.t1_ell
  | ⟨7, _⟩ => e.r_ell
  | ⟨8, _⟩ => e.pWork_ell
  | ⟨9, _⟩ => e.pChild_ell
  | ⟨10, _⟩ => e.qChild_ell

/-- Total bit-length `11 * w` of an encoded `LevelScheduleEntry` with `w` bits per field. -/
def levelScheduleEntryBits (w : ℕ) : ℕ := 11 * w

/-- Canonical `11 * w`-bit binary encoding of a `LevelScheduleEntry`. -/
def encodeLevelScheduleEntry (w : ℕ) (e : LevelScheduleEntry) : List Bool :=
  (List.ofFn (fun i : Fin 11 => encodeNatBits w (levelScheduleFieldVec e i))).flatten

@[simp]
theorem length_encodeLevelScheduleEntry (w : ℕ) (e : LevelScheduleEntry) :
    (encodeLevelScheduleEntry w e).length = 11 * w := by
  unfold encodeLevelScheduleEntry
  exact length_flatten_ofFn w _ (fun i => length_encodeNatBits w (levelScheduleFieldVec e i))

/-- Decode the `i`-th `w`-bit unsigned field (`i : Fin 11`) from an encoded `LevelScheduleEntry`. -/
def decodeLevelScheduleField (w : ℕ) (bs : List Bool) (i : Fin 11) : ℕ :=
  decodeNatBits ((bs.drop (i.val * w)).take w)

/-- Decode an `11 * w`-bit list `bs : List Bool` into a `LevelScheduleEntry`. -/
def decodeLevelScheduleEntry (w : ℕ) (bs : List Bool) : LevelScheduleEntry where
  ell := decodeLevelScheduleField w bs ⟨0, by decide⟩
  K_ell := decodeLevelScheduleField w bs ⟨1, by decide⟩
  R_ell := decodeLevelScheduleField w bs ⟨2, by decide⟩
  p_ell := decodeLevelScheduleField w bs ⟨3, by decide⟩
  k1_ell := decodeLevelScheduleField w bs ⟨4, by decide⟩
  k2_ell := decodeLevelScheduleField w bs ⟨5, by decide⟩
  t1_ell := decodeLevelScheduleField w bs ⟨6, by decide⟩
  r_ell := decodeLevelScheduleField w bs ⟨7, by decide⟩
  pWork_ell := decodeLevelScheduleField w bs ⟨8, by decide⟩
  pChild_ell := decodeLevelScheduleField w bs ⟨9, by decide⟩
  qChild_ell := decodeLevelScheduleField w bs ⟨10, by decide⟩

/-- Predicate asserting that all 11 fields of `e : LevelScheduleEntry` fit within `w`-bit unsigned
words (`< 2 ^ w`). -/
def FitsLevelScheduleEntry (w : ℕ) (e : LevelScheduleEntry) : Prop :=
  e.ell < 2 ^ w ∧
  e.K_ell < 2 ^ w ∧
  e.R_ell < 2 ^ w ∧
  e.p_ell < 2 ^ w ∧
  e.k1_ell < 2 ^ w ∧
  e.k2_ell < 2 ^ w ∧
  e.t1_ell < 2 ^ w ∧
  e.r_ell < 2 ^ w ∧
  e.pWork_ell < 2 ^ w ∧
  e.pChild_ell < 2 ^ w ∧
  e.qChild_ell < 2 ^ w

theorem FitsLevelScheduleEntry.mono {w1 w2 : ℕ} {e : LevelScheduleEntry}
    (he : FitsLevelScheduleEntry w1 e) (hw : w1 ≤ w2) :
    FitsLevelScheduleEntry w2 e := by
  have hpow : 2 ^ w1 ≤ 2 ^ w2 := Nat.pow_le_pow_right (by norm_num) hw
  rcases he with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨lt_of_lt_of_le h0 hpow, lt_of_lt_of_le h1 hpow, lt_of_lt_of_le h2 hpow,
    lt_of_lt_of_le h3 hpow, lt_of_lt_of_le h4 hpow, lt_of_lt_of_le h5 hpow,
    lt_of_lt_of_le h6 hpow, lt_of_lt_of_le h7 hpow, lt_of_lt_of_le h8 hpow,
    lt_of_lt_of_le h9 hpow, lt_of_lt_of_le h10 hpow⟩

theorem levelScheduleFieldVec_lt_of_fits {w : ℕ} {e : LevelScheduleEntry}
    (he : FitsLevelScheduleEntry w e) (i : Fin 11) :
    levelScheduleFieldVec e i < 2 ^ w := by
  rcases he with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  fin_cases i <;> simp [levelScheduleFieldVec, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

@[simp]
theorem decodeLevelScheduleField_encodeLevelScheduleEntry (w : ℕ) (e : LevelScheduleEntry)
    (i : Fin 11) (hi : levelScheduleFieldVec e i < 2 ^ w) :
    decodeLevelScheduleField w (encodeLevelScheduleEntry w e) i = levelScheduleFieldVec e i := by
  unfold decodeLevelScheduleField encodeLevelScheduleEntry
  rw [drop_take_flatten_ofFn w
    (fun j : Fin 11 => encodeNatBits w (levelScheduleFieldVec e j))
    (fun j => length_encodeNatBits w (levelScheduleFieldVec e j)) i]
  exact decodeNatBits_encodeNatBits w (levelScheduleFieldVec e i) hi

/-- **Round-Trip Theorem for Per-Level Schedule Entries (`decodeLevelScheduleEntry_encodeLevelScheduleEntry`)**:
For any `e : LevelScheduleEntry` whose fields are `< 2 ^ w` (`FitsLevelScheduleEntry w e`),
decoding `encodeLevelScheduleEntry w e` recovers `e` bit-exactly. -/
@[simp]
theorem decodeLevelScheduleEntry_encodeLevelScheduleEntry (w : ℕ) (e : LevelScheduleEntry)
    (he : FitsLevelScheduleEntry w e) :
    decodeLevelScheduleEntry w (encodeLevelScheduleEntry w e) = e := by
  have hf : ∀ i : Fin 11,
      decodeLevelScheduleField w (encodeLevelScheduleEntry w e) i = levelScheduleFieldVec e i :=
    fun i => decodeLevelScheduleField_encodeLevelScheduleEntry w e i
      (levelScheduleFieldVec_lt_of_fits he i)
  ext <;> simp [decodeLevelScheduleEntry, hf, levelScheduleFieldVec]

private theorem linear_lt_two_pow_two_mul_add_eight (n : ℕ) :
    26 * n + 76 < 2 ^ (2 * n + 8) := by
  have h1 : 2 * n + 3 < 2 ^ (2 * n + 3) := Nat.lt_two_pow_self
  have h2 : 32 * 2 ^ (2 * n + 3) = 2 ^ (2 * n + 8) := by
    have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
    rw [h32, ← pow_add]
    congr 1
    omega
  omega

/-- Every field of `buildLevelScheduleEntry n ell` (for any `ell ≤ rootK0 n`) fits in `w` unsigned
bits whenever `2 * n + 8 ≤ w`. -/
theorem fitsLevelScheduleEntry_buildLevelScheduleEntry (n ell w : ℕ)
    (hell : ell ≤ rootK0 n) (hw : 2 * n + 8 ≤ w) :
    FitsLevelScheduleEntry w (buildLevelScheduleEntry n ell) := by
  apply FitsLevelScheduleEntry.mono (w1 := 2 * n + 8) ?_ hw
  unfold FitsLevelScheduleEntry
  simp only [buildLevelScheduleEntry_ell, buildLevelScheduleEntry_K_ell,
    buildLevelScheduleEntry_R_ell, buildLevelScheduleEntry_p_ell,
    buildLevelScheduleEntry_k1_ell, buildLevelScheduleEntry_k2_ell,
    buildLevelScheduleEntry_t1_ell, buildLevelScheduleEntry_r_ell,
    buildLevelScheduleEntry_pWork_ell, buildLevelScheduleEntry_pChild_ell,
    buildLevelScheduleEntry_qChild_ell]
  have hb := chunkBits_le_add_four n
  have hK0 := rootK0_le_add_two n
  have hK_le : levelK (rootK0 n) ell ≤ rootK0 n := levelK_le_K0 (rootK0 n) ell
  have hp0_eq : rootP0 n = 2 * chunkBits n + 2 * rootK0 n + 6 := rfl
  have hp_le := levelP_le (rootK0 n) (rootP0 n) ell
  have hlin := linear_lt_two_pow_two_mul_add_eight n
  have hk1 : k1Ell (levelK (rootK0 n) ell) ≤ levelK (rootK0 n) ell := by
    unfold k1Ell; omega
  have hk2 : k2Ell (levelK (rootK0 n) ell) ≤ levelK (rootK0 n) ell := by
    unfold k2Ell; omega
  have hpWork : pWorkEll (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell) =
      levelP (rootK0 n) (rootP0 n) ell + levelK (rootK0 n) ell + 6 := rfl
  have hpChild := pChildEll_eq (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)
  have hqChild := qChildEll_eq (levelK (rootK0 n) ell) (levelP (rootK0 n) (rootP0 n) ell)
  refine ⟨by omega, by omega, ?_, by omega, by omega, by omega, ?_, ?_, by omega, by omega, by omega⟩
  · unfold levelR
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · unfold t1Ell
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · unfold rEll
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- Unconditional round-trip recovery of `buildLevelScheduleEntry n ell` for any `ell ≤ rootK0 n`
and `2 * n + 8 ≤ w`. -/
@[simp]
theorem decodeLevelScheduleEntry_encodeLevelScheduleEntry_build (n ell w : ℕ)
    (hell : ell ≤ rootK0 n) (hw : 2 * n + 8 ≤ w) :
    decodeLevelScheduleEntry w (encodeLevelScheduleEntry w (buildLevelScheduleEntry n ell)) =
      buildLevelScheduleEntry n ell :=
  decodeLevelScheduleEntry_encodeLevelScheduleEntry w (buildLevelScheduleEntry n ell)
    (fitsLevelScheduleEntry_buildLevelScheduleEntry n ell w hell hw)

end IntMul

#print axioms IntMul.evalsToInTime_trans_exists
#print axioms IntMul.cannot_store_n_bits_in_uniform_state
#print axioms IntMul.uniform_push_range_card_le
#print axioms IntMul.isUniformFinTM2_tmUniformRevCopy
#print axioms IntMul.tmUniformRevCopy_evalsToInTime
#print axioms IntMul.isUniformFinTM2_tmUniformIdCopy
#print axioms IntMul.tmUniformIdCopy_evalsToInTime
#print axioms IntMul.isUniformFinTM2_tmUniformDeinterleave
#print axioms IntMul.tmUniformDeinterleave_evalsToInTime
#print axioms IntMul.isUniformFinTM2_tmUniformRippleAdd
#print axioms IntMul.tmUniformRippleAdd_encodeNatBits_evalsToInTime
#print axioms IntMul.isUniformFinTM2_tmUniformRippleSub
#print axioms IntMul.tmUniformRippleSub_encodeNatBits_evalsToInTime
#print axioms IntMul.isUniformFinTM2_tmUniformButterflyAddSub
#print axioms IntMul.tmUniformButterflyAddSub_encodeNatBits_evalsToInTime
#print axioms IntMul.isUniformFinTM2_tmUniformBitMulAdd
#print axioms IntMul.tmUniformBitMulAdd_encodeNatBits_evalsToInTime
#print axioms IntMul.isUniformFinTM2_tmUniformCondSubStep
#print axioms IntMul.tmUniformCondSubStep_encodeNatBits_evalsToInTime
#print axioms IntMul.isUniformFinTM2_tmUniformInterleave
#print axioms IntMul.tmUniformInterleave_evalsToInTime
#print axioms IntMul.decodeSignedWord_encodeSignedWord
#print axioms IntMul.decodeFixedComplex_encodeFixedComplex
#print axioms IntMul.decodeBatchWords_encodeBatchWords
#print axioms IntMul.subproblemMajorWords_toBatch_ofBatch
#print axioms IntMul.batch_toSubproblemMajorWords_ofSubproblemMajorWords
#print axioms IntMul.decodeSubproblemMajorWords_subproblemMajorWords
#print axioms IntMul.transposeKey_injective
#print axioms IntMul.transposeMatrix_spec
#print axioms IntMul.oddColKeyMinus_oddColKeyMinusInv
#print axioms IntMul.oddColKeyMinusInv_oddColKeyMinus
#print axioms IntMul.oddColScatter_spec
#print axioms IntMul.oddColGather_oddColScatter
#print axioms IntMul.oddColScatter_oddColGather
#print axioms IntMul.oddStrideGather_oddStrideScatter
#print axioms IntMul.oddStrideScatter_oddStrideGather
#print axioms IntMul.decodeLevelScheduleEntry_encodeLevelScheduleEntry
#print axioms IntMul.fitsLevelScheduleEntry_buildLevelScheduleEntry
#print axioms IntMul.decodeLevelScheduleEntry_encodeLevelScheduleEntry_build

