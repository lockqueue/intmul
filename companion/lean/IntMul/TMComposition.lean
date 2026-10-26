import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint
import IntMul.TMPrimitives

set_option backward.isDefEq.respectTransparency false

/-!
# Uniform 8-Stack Binary Machine (`Turing.FinTM2`) Composition & Streaming Stages (`IntMul.TMComposition`)

This module implements the uniform 8-stack binary machine (`Turing.FinTM2`) composition
infrastructure and multi-pass streaming stage realizations on 8 binary stacks (`TapeIdx = Fin 8`,
`BitTapeAlphabet k = Bool`; see Section 3.2 (`sec:prelim-model`), Section 8 (`sec:lean`), and
Appendix A.2 (`app:tape-schedule`)):

1. **Universal Step-Simulation Lifting (`EvalsTo.map_simulation`, `EvalsToInTime.map_simulation`)**:
   - Any step-preserving simulation map `φ : α → β` (`∀ x y, f x = some y → g (φ x) = some (φ y)`)
     lifts constructive `Turing.EvalsTo` and `Turing.EvalsToInTime` derivations directly without
     re-proving machine-specific inductions.

2. **Uniform 8-Stack `Turing.FinTM2` Composition Combinators**:
   - **Register Lifting (`liftUniformRegTM`)**: Lifts any 8-stack binary machine (`Turing.FinTM2`)
     over the 3-bit register `UniformReg` (`|σ| = 8`) to `ButterflyReg` (`|σ| = 16`) while
     preserving control label cardinality `|Λ|` and exact `TM2.step` transition counts `t`.
   - **Stack Permutation / Relocation (`remapTapesTM`)**: Relocates any 8-stack binary machine
     (`Turing.FinTM2`) across any stack bijection `π : TapeIdx ≃ TapeIdx` (`remapStk π`) while
     preserving `|Λ|`, `|σ|`, `|Γ k| = 2`, and exact `TM2.step` transition counts `t`.
   - **Sequential Composition (`seqBitFinTM2`)**: Composes any two 8-stack binary machines
     (`Turing.FinTM2`) `M₁` (`|Λ₁|` labels) and `M₂` (`|Λ₂|` labels) over a shared $O(1)$ register
     `σ` by redirecting `Stmt.halt` in `M₁` to reset `σ` and jump to `Sum.inr main₂`, proving
     `IsUniformFinTM2` with `|Λ₁ ⊕ Λ₂| = |Λ₁| + |Λ₂|` and `t₁ + t₂` `TM2.step` transitions
     (`seqBitFinTM2_evalsToInTime_concrete`).
   - **Counter-Stack Loop / Iteration Composition (`loopTapeBitFinTM2`)**: Wraps any 8-stack binary
     body machine (`Turing.FinTM2`) `M` (`|Λ|` labels) into an `Option Λ` loop machine (`|Λ| + 1`
     labels, zero $n$-dependent state) that pops one token bit per pass from counter stack `kCnt`
     (such as `kSched` or `kWork5`), running `k = (T kCnt).length` passes of `M` in
     `k * (B + 1) + 1` `TM2.step` transitions (`loopTapeBitFinTM2_evalsToInTime_concrete`).

3. **Composed Multi-Pass Uniform `FinTM2` Stages, Signed Arithmetic (`encodeSignedWord`), &
   Single-Input-Stack `Turing.initList` Realizations**:
   - **Parameterized Stack-to-Stack Reverse Copy (`tmUniformRevCopyBetween kSrc kDst`) & Composed
     Order-Preserving Copy (`tmComposedIdCopy`)**: Sequential composition of `tmUniformRevCopy`
     (`kIO → kWork0`) and `tmUniformRevCopyBetween kWork0 kIO` (`kWork0 → kIO`) via `seqBitFinTM2`,
     accounting for both forward transit and reversal passes in `4 * xs.length + 2` `TM2.step` transitions.
   - **Composed 2-Stage Deinterleave-Interleave Pass (`tmComposedDeinterleaveInterleave`),
     Composed 4-Stage Order-Preserving Bit-Shuffle Pass (`tmComposedOrderPreservingShuffle`), and
     Schedule-Driven Multi-Pass Bit-Transpose (`tmComposedMultiPassTranspose`)**:
     Composes `tmUniformDeinterleave` and `tmUniformInterleave` via `seqBitFinTM2` and iterates
     across `K = (T kSched).length` passes via `loopTapeBitFinTM2 kSched`, proving exact output
     recovery `flattenBitPairs ps` and an unconditional `K * (24 * m + 7) + 1 = Θ(K * m)`
     bound on `TM2.step` transitions across all 8 binary stacks.
   - **Composed Simultaneous Butterfly + Difference Packing Stage (`tmComposedButterflyStage`)**:
     Composes `tmUniformButterflyAddSub` (`|Λ| = 9`, `|σ| = 16`) with a 2-pass order-preserving
     transfer of the butterfly difference from `kWork0` onto `kIO` (`|Λ| = 13`, `|σ| = 16`),
     streaming both `w`-bit operands and emitting both `encodeNatBits w (A - B)` and
     `encodeNatBits (w + 1) (A + B)` on `kIO` in `12 * w + 8 = Θ(w)` `TM2.step` transitions.
   - **Composed Restoring Conditional-Subtract + Remainder-Return Pass (`tmComposedCondSubPass`)**:
     Composes `tmUniformCondSubStep` (`|Λ| = 8`, `|σ| = 16`) with `tmReturnRemIOViaWork2ToWork0`
     (`kIO → kWork0`) via `seqBitFinTM2` (`|Λ| = 12`, `|σ| = 16`), executing a conditional
     subtract-mux step and returning the updated remainder and quotient bit to `kWork0` in
     $11 w + 5 = \Theta(w)$ `TM2.step` transitions (matching the $\Theta(w)$ per-step register
     cost of $w$-bit restoring division and square root).
   - **Signed Offset-Binary Arithmetic for Arbitrary `x, y : ℤ` (`encodeSignedWord`,
     `tmUniformRippleAdd_encodeSignedWord_evalsToInTime`, `tmUniformSignedButterflyAddSub`,
     `tmComposedSignedButterflyStage`)**:
     Proves that for **arbitrary signed integers `x, y : ℤ` of any sign** satisfying
     `FitsSignedWord w x` and `FitsSignedWord w y` (with **no** `y ≤ x` restriction),
     `tmUniformRippleAdd` computes `encodeSignedWord (w + 1) (x + y)` in `5 * w + 10` `TM2.step` transitions, and
     the uniform signed butterfly machine `tmUniformSignedButterflyAddSub` (`|Λ| = 10`, `|σ| = 16`)
     simultaneously computes both `encodeSignedWord (w + 1) (x + y)` on `kIO` and
     `encodeSignedWord (w + 1) (x - y)` on `kWork0` in `8 * w + 17` `TM2.step` transitions (`tmComposedSignedButterflyStage`
     packs both onto `kIO` in `12 * w + 27` `TM2.step` transitions).
   - **Single-Input-Stack `Turing.initList` Deinterleave-and-Restore Front-End (`tmDeinterleaveAndRestore`)
     & Signed Arithmetic Machines (`tmSingleTapeSignedAdd`, `tmSingleTapeSignedButterfly`)**:
     Composes `tmDeinterleaveAndRestore` (`kIO → kWork2, kWork3 → kWork0, kWork1`, restoring forward
     LSB-first order on `kWork0` and `kWork1` in `8 * m + 3` `TM2.step` transitions) with `tmUniformRippleAdd` and
     `tmComposedSignedButterflyStage` via `seqBitFinTM2`, so the composed machines start directly
     from `Turing.initList` on `kIO` (with all other binary stacks empty) and halt at
     `Turing.haltList` on `kIO`.
-/

namespace IntMul

open Turing

universe u v

/-! ## 1. Universal Step-Simulation Lifting (`EvalsTo.map_simulation`, `EvalsToInTime.map_simulation`) -/

/-- Step-by-step simulation of `(flip bind f)^[n]` by `(flip bind g)^[n]` along any map `φ : α → β`
satisfying `∀ x y, f x = some y → g (φ x) = some (φ y)`. -/
theorem iterate_flip_bind_map_simulation {α : Type u} {β : Type v}
    (f : α → Option α) (g : β → Option β) (φ : α → β)
    (hstep : ∀ x y : α, f x = some y → g (φ x) = some (φ y)) :
    ∀ (n : ℕ) (a b : α),
      (flip bind f)^[n] (some a) = some b →
      (flip bind g)^[n] (some (φ a)) = some (φ b)
  | 0, a, b, h => by
    injection h with hab
    subst hab
    rfl
  | n + 1, a, b, h => by
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind f)^[n] (f a) = some b at h
    cases hfa : f a with
    | none =>
      rw [hfa] at h
      have hnone : ∀ k : ℕ, (flip bind f)^[k] (none : Option α) = none := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply]; exact ih
      rw [hnone n] at h
      cases h
    | some a' =>
      rw [hfa] at h
      have hg : g (φ a) = some (φ a') := hstep a a' hfa
      change (flip bind g)^[n] (g (φ a)) = some (φ b)
      rw [hg]
      exact iterate_flip_bind_map_simulation f g φ hstep n a' b h

/-- Constructive lifting of `Turing.EvalsTo` along a step-preserving simulation map `φ : α → β`. -/
def EvalsTo.map_simulation {α : Type u} {β : Type v}
    {f : α → Option α} {g : β → Option β} (φ : α → β)
    (hstep : ∀ x y : α, f x = some y → g (φ x) = some (φ y))
    {a b : α} (h : Turing.EvalsTo f a (some b)) :
    Turing.EvalsTo g (φ a) (some (φ b)) where
  steps := h.steps
  evals_in_steps := iterate_flip_bind_map_simulation f g φ hstep h.steps a b h.evals_in_steps

/-- Constructive lifting of `Turing.EvalsToInTime` along a step-preserving simulation map `φ : α → β`
with identical step bound `m`. -/
def EvalsToInTime.map_simulation {α : Type u} {β : Type v}
    {f : α → Option α} {g : β → Option β} (φ : α → β)
    (hstep : ∀ x y : α, f x = some y → g (φ x) = some (φ y))
    {a b : α} {m : ℕ} (h : Turing.EvalsToInTime f a (some b) m) :
    Turing.EvalsToInTime g (φ a) (some (φ b)) m where
  toEvalsTo := EvalsTo.map_simulation φ hstep h.toEvalsTo
  steps_le_m := h.steps_le_m

/-! ## 2. Register Lifting Combinator (`liftUniformRegTM`) -/

/-- Canonical embedding of the 3-bit register `UniformReg` (`|σ| = 8`) into the 4-bit register
`ButterflyReg` (`|σ| = 16`) with `borrow := false`. -/
def uniformToButterflyReg (r : UniformReg) : ButterflyReg :=
  ⟨r.bitA, r.bitB, r.carry, false⟩

/-- Projection from `ButterflyReg` onto `UniformReg` forgetting the `borrow` bit. -/
def butterflyToUniformReg (r : ButterflyReg) : UniformReg :=
  ⟨r.bitA, r.bitB, r.carry⟩

@[simp]
theorem butterflyToUniformReg_uniformToButterflyReg (r : UniformReg) :
    butterflyToUniformReg (uniformToButterflyReg r) = r := by
  cases r; rfl

@[simp]
theorem uniformToButterflyReg_default :
    uniformToButterflyReg default = default := rfl

/-- Lift a `Turing.TM2.Stmt` over `UniformReg` to operate on `ButterflyReg`. -/
def liftUniformRegStmt {Λ : Type} :
    Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg →
      Turing.TM2.Stmt BitTapeAlphabet Λ ButterflyReg
  | .push k f q =>
    .push k (fun r => f (butterflyToUniformReg r)) (liftUniformRegStmt q)
  | .peek k f q =>
    .peek k (fun r bOpt => uniformToButterflyReg (f (butterflyToUniformReg r) bOpt))
      (liftUniformRegStmt q)
  | .pop k f q =>
    .pop k (fun r bOpt => uniformToButterflyReg (f (butterflyToUniformReg r) bOpt))
      (liftUniformRegStmt q)
  | .load a q =>
    .load (fun r => uniformToButterflyReg (a (butterflyToUniformReg r)))
      (liftUniformRegStmt q)
  | .branch p q₁ q₂ =>
    .branch (fun r => p (butterflyToUniformReg r))
      (liftUniformRegStmt q₁) (liftUniformRegStmt q₂)
  | .goto l =>
    .goto (fun r => l (butterflyToUniformReg r))
  | .halt => .halt

/-- Map a configuration over `UniformReg` to a configuration over `ButterflyReg`. -/
def mapUniformToButterflyCfg {Λ : Type}
    (cfg : Turing.TM2.Cfg BitTapeAlphabet Λ UniformReg) :
    Turing.TM2.Cfg BitTapeAlphabet Λ ButterflyReg :=
  ⟨cfg.l, uniformToButterflyReg cfg.var, cfg.stk⟩

/-- Exact step-simulation of `liftUniformRegStmt` on any `UniformReg` state. -/
theorem stepAux_liftUniformRegStmt {Λ : Type} :
    ∀ (q : Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg) (v : UniformReg)
      (stk : ∀ k : TapeIdx, List (BitTapeAlphabet k)),
      Turing.TM2.stepAux (liftUniformRegStmt q) (uniformToButterflyReg v) stk =
        mapUniformToButterflyCfg (Turing.TM2.stepAux q v stk)
  | .push k f q, v, stk => by
    dsimp [liftUniformRegStmt, Turing.TM2.stepAux]
    rw [butterflyToUniformReg_uniformToButterflyReg]
    exact stepAux_liftUniformRegStmt q v _
  | .peek k f q, v, stk => by
    dsimp [liftUniformRegStmt, Turing.TM2.stepAux]
    rw [butterflyToUniformReg_uniformToButterflyReg]
    exact stepAux_liftUniformRegStmt q _ stk
  | .pop k f q, v, stk => by
    dsimp [liftUniformRegStmt, Turing.TM2.stepAux]
    rw [butterflyToUniformReg_uniformToButterflyReg]
    exact stepAux_liftUniformRegStmt q _ _
  | .load a q, v, stk => by
    dsimp [liftUniformRegStmt, Turing.TM2.stepAux]
    rw [butterflyToUniformReg_uniformToButterflyReg]
    exact stepAux_liftUniformRegStmt q _ stk
  | .branch p q₁ q₂, v, stk => by
    dsimp [liftUniformRegStmt, Turing.TM2.stepAux]
    rw [butterflyToUniformReg_uniformToButterflyReg]
    cases p v <;> simp [stepAux_liftUniformRegStmt]
  | .goto l, v, stk => by
    dsimp [liftUniformRegStmt, Turing.TM2.stepAux, mapUniformToButterflyCfg]
    rw [butterflyToUniformReg_uniformToButterflyReg]
  | .halt, v, stk => rfl

/-- Lift an 8-stack binary machine (`Turing.FinTM2`) over `UniformReg` to `ButterflyReg` (`|σ| = 16`)
so it can be composed sequentially with 16-state machines such as `tmUniformButterflyAddSub`
and `tmUniformCondSubStep`. -/
def liftUniformRegTM (Λ : Type) [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg) : Turing.FinTM2 :=
  mkBitFinTM2 Λ main ButterflyReg default (fun l => liftUniformRegStmt (m l))

theorem isUniformFinTM2_liftUniformRegTM {Λ : Type} [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg)
    {maxLabels : ℕ} (hΛ : Fintype.card Λ ≤ maxLabels) :
    IsUniformFinTM2 (liftUniformRegTM Λ main m) maxLabels 16 2 :=
  isUniformFinTM2_mkBitFinTM2 main default _ hΛ (by decide) (by decide)

theorem step_liftUniformRegTM {Λ : Type} [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg)
    (x y : (mkBitFinTM2 Λ main UniformReg default m).Cfg)
    (h : (mkBitFinTM2 Λ main UniformReg default m).step x = some y) :
    (liftUniformRegTM Λ main m).step (mapUniformToButterflyCfg x) =
      some (mapUniformToButterflyCfg y) := by
  rcases x with ⟨lOpt, v, stk⟩
  cases lOpt with
  | none => cases h
  | some l =>
    injection h with hy
    subst hy
    dsimp [liftUniformRegTM, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      mapUniformToButterflyCfg]
    exact congrArg some (stepAux_liftUniformRegStmt (m l) v stk)

/-- Constructive step-bound lifting for `liftUniformRegTM`. -/
def liftUniformRegTM_evalsToInTime_concrete {Λ : Type} [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg)
    {cfg₁ cfg₂ : (mkBitFinTM2 Λ main UniformReg default m).Cfg} {t : ℕ}
    (h : Turing.EvalsToInTime (mkBitFinTM2 Λ main UniformReg default m).step
      cfg₁ (some cfg₂) t) :
    Turing.EvalsToInTime (liftUniformRegTM Λ main m).step
      (mapUniformToButterflyCfg cfg₁) (some (mapUniformToButterflyCfg cfg₂)) t :=
  EvalsToInTime.map_simulation mapUniformToButterflyCfg (step_liftUniformRegTM main m) h

/-- Constructive step-bound lifting for `liftUniformRegTM` on `default` start/halt registers. -/
def liftUniformRegTM_evalsToInTime_default_concrete {Λ : Type} [Fintype Λ] (main : Λ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg)
    {l₁ : Option Λ} {T₁ T₂ : ∀ k : TapeIdx, List (BitTapeAlphabet k)} {t : ℕ}
    (h : Turing.EvalsToInTime (mkBitFinTM2 Λ main UniformReg default m).step
      ⟨l₁, default, T₁⟩ (some ⟨none, default, T₂⟩) t) :
    Turing.EvalsToInTime (liftUniformRegTM Λ main m).step
      ⟨l₁, default, T₁⟩ (some ⟨none, default, T₂⟩) t :=
  liftUniformRegTM_evalsToInTime_concrete main m h

/-! ## 3. Stack Permutation / Relocation Combinator (`remapTapesTM`) -/

/-- Relocate a stack assignment `stk` along a tape permutation `π : TapeIdx ≃ TapeIdx` so that
`(remapStk π stk) (π k) = stk k`. -/
def remapStk (π : TapeIdx ≃ TapeIdx)
    (stk : ∀ k : TapeIdx, List (BitTapeAlphabet k)) :
    ∀ k : TapeIdx, List (BitTapeAlphabet k) :=
  fun k => stk (π.symm k)

@[simp]
theorem remapStk_apply (π : TapeIdx ≃ TapeIdx)
    (stk : ∀ k : TapeIdx, List (BitTapeAlphabet k)) (k : TapeIdx) :
    remapStk π stk (π k) = stk k := by
  unfold remapStk
  rw [Equiv.symm_apply_apply]

@[simp]
theorem update_remapStk (π : TapeIdx ≃ TapeIdx)
    (stk : ∀ k : TapeIdx, List (BitTapeAlphabet k)) (k : TapeIdx) (v : List Bool) :
    Function.update (remapStk π stk) (π k) v = remapStk π (Function.update stk k v) := by
  funext k'
  by_cases hk : k' = π k
  · subst hk
    unfold remapStk
    rw [Function.update_self, Equiv.symm_apply_apply, Function.update_self]
  · have hsymm : π.symm k' ≠ k := by
      intro heq
      apply hk
      rw [← heq, Equiv.apply_symm_apply]
    simp [remapStk, hk, hsymm]

/-- Relocate all tape indices in a `Turing.TM2.Stmt` by a bijection `π : TapeIdx ≃ TapeIdx`. -/
def remapTapesStmt (π : TapeIdx ≃ TapeIdx) {Λ σ : Type} :
    Turing.TM2.Stmt BitTapeAlphabet Λ σ → Turing.TM2.Stmt BitTapeAlphabet Λ σ
  | .push k f q => .push (π k) f (remapTapesStmt π q)
  | .peek k f q => .peek (π k) f (remapTapesStmt π q)
  | .pop k f q => .pop (π k) f (remapTapesStmt π q)
  | .load a q => .load a (remapTapesStmt π q)
  | .branch p q₁ q₂ => .branch p (remapTapesStmt π q₁) (remapTapesStmt π q₂)
  | .goto l => .goto l
  | .halt => .halt

/-- Map a configuration by relocating its tape stacks via `remapStk π`. -/
def mapRemapTapesCfg (π : TapeIdx ≃ TapeIdx) {Λ σ : Type}
    (cfg : Turing.TM2.Cfg BitTapeAlphabet Λ σ) :
    Turing.TM2.Cfg BitTapeAlphabet Λ σ :=
  ⟨cfg.l, cfg.var, remapStk π cfg.stk⟩

/-- Exact step-simulation of `remapTapesStmt π` under `remapStk π`. -/
theorem stepAux_remapTapesStmt (π : TapeIdx ≃ TapeIdx) {Λ σ : Type} :
    ∀ (q : Turing.TM2.Stmt BitTapeAlphabet Λ σ) (v : σ)
      (stk : ∀ k : TapeIdx, List (BitTapeAlphabet k)),
      Turing.TM2.stepAux (remapTapesStmt π q) v (remapStk π stk) =
        mapRemapTapesCfg π (Turing.TM2.stepAux q v stk)
  | .push k f q, v, stk => by
    dsimp [remapTapesStmt, Turing.TM2.stepAux]
    rw [remapStk_apply, update_remapStk]
    exact stepAux_remapTapesStmt π q v _
  | .peek k f q, v, stk => by
    dsimp [remapTapesStmt, Turing.TM2.stepAux]
    rw [remapStk_apply]
    exact stepAux_remapTapesStmt π q _ stk
  | .pop k f q, v, stk => by
    dsimp [remapTapesStmt, Turing.TM2.stepAux]
    rw [remapStk_apply, update_remapStk]
    exact stepAux_remapTapesStmt π q _ _
  | .load a q, v, stk => stepAux_remapTapesStmt π q _ stk
  | .branch p q₁ q₂, v, stk => by
    dsimp [remapTapesStmt, Turing.TM2.stepAux]
    cases p v <;> simp [stepAux_remapTapesStmt π]
  | .goto l, v, stk => rfl
  | .halt, v, stk => rfl

/-- Relocate an 8-stack binary machine (`Turing.FinTM2`) across a stack permutation `π : TapeIdx ≃ TapeIdx`. -/
def remapTapesTM (π : TapeIdx ≃ TapeIdx) (Λ : Type) [Fintype Λ] (main : Λ)
    (σ : Type) [Fintype σ] (initialState : σ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ) : Turing.FinTM2 :=
  mkBitFinTM2 Λ main σ initialState (fun l => remapTapesStmt π (m l))

theorem isUniformFinTM2_remapTapesTM (π : TapeIdx ≃ TapeIdx)
    {Λ : Type} [Fintype Λ] (main : Λ) {σ : Type} [Fintype σ] (initialState : σ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ)
    {maxLabels maxStates maxAlpha : ℕ}
    (hΛ : Fintype.card Λ ≤ maxLabels)
    (hσ : Fintype.card σ ≤ maxStates)
    (hΓ : 2 ≤ maxAlpha) :
    IsUniformFinTM2 (remapTapesTM π Λ main σ initialState m) maxLabels maxStates maxAlpha :=
  isUniformFinTM2_mkBitFinTM2 main initialState _ hΛ hσ hΓ

theorem step_remapTapesTM (π : TapeIdx ≃ TapeIdx)
    {Λ : Type} [Fintype Λ] (main : Λ) {σ : Type} [Fintype σ] (initialState : σ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ)
    (x y : (mkBitFinTM2 Λ main σ initialState m).Cfg)
    (h : (mkBitFinTM2 Λ main σ initialState m).step x = some y) :
    (remapTapesTM π Λ main σ initialState m).step (mapRemapTapesCfg π x) =
      some (mapRemapTapesCfg π y) := by
  rcases x with ⟨lOpt, v, stk⟩
  cases lOpt with
  | none => cases h
  | some l =>
    injection h with hy
    subst hy
    dsimp [remapTapesTM, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, mapRemapTapesCfg]
    exact congrArg some (stepAux_remapTapesStmt π (m l) v stk)

/-- Constructive step-bound lifting for `remapTapesTM`. -/
def remapTapesTM_evalsToInTime_concrete (π : TapeIdx ≃ TapeIdx)
    {Λ : Type} [Fintype Λ] (main : Λ) {σ : Type} [Fintype σ] (initialState : σ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ)
    {cfg₁ cfg₂ : (mkBitFinTM2 Λ main σ initialState m).Cfg} {t : ℕ}
    (h : Turing.EvalsToInTime (mkBitFinTM2 Λ main σ initialState m).step
      cfg₁ (some cfg₂) t) :
    Turing.EvalsToInTime (remapTapesTM π Λ main σ initialState m).step
      (mapRemapTapesCfg π cfg₁) (some (mapRemapTapesCfg π cfg₂)) t :=
  EvalsToInTime.map_simulation (mapRemapTapesCfg π) (step_remapTapesTM π main initialState m) h

/-! ## 4. Sequential Composition Combinator (`seqBitFinTM2`) -/

/-- Redirect `Stmt.halt` in a Phase-1 statement over `Λ₁` to reset the register to `resetReg : σ`
and jump to `Sum.inr entry₂ : Λ₁ ⊕ Λ₂`. -/
def redirectHaltStmt {Λ₁ Λ₂ σ : Type} (entry₂ : Λ₂) (resetReg : σ) :
    Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ → Turing.TM2.Stmt BitTapeAlphabet (Λ₁ ⊕ Λ₂) σ
  | .push k f q => .push k f (redirectHaltStmt entry₂ resetReg q)
  | .peek k f q => .peek k f (redirectHaltStmt entry₂ resetReg q)
  | .pop k f q => .pop k f (redirectHaltStmt entry₂ resetReg q)
  | .load a q => .load a (redirectHaltStmt entry₂ resetReg q)
  | .branch p q₁ q₂ =>
    .branch p (redirectHaltStmt entry₂ resetReg q₁) (redirectHaltStmt entry₂ resetReg q₂)
  | .goto l => .goto (fun v => Sum.inl (l v))
  | .halt => .load (fun _ => resetReg) (.goto (fun _ => Sum.inr entry₂))

/-- Lift a Phase-2 statement over `Λ₂` into `Λ₁ ⊕ Λ₂` via `Sum.inr`. -/
def liftInrStmt {Λ₁ Λ₂ σ : Type} :
    Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ → Turing.TM2.Stmt BitTapeAlphabet (Λ₁ ⊕ Λ₂) σ
  | .push k f q => .push k f (liftInrStmt q)
  | .peek k f q => .peek k f (liftInrStmt q)
  | .pop k f q => .pop k f (liftInrStmt q)
  | .load a q => .load a (liftInrStmt q)
  | .branch p q₁ q₂ => .branch p (liftInrStmt q₁) (liftInrStmt q₂)
  | .goto l => .goto (fun v => Sum.inr (l v))
  | .halt => .halt

/-- **Sequential Composition of Uniform 8-Stack Binary Machines (`Turing.FinTM2`, `seqBitFinTM2`)**:
Composes `M₁ = mkBitFinTM2 Λ₁ main₁ σ init₁ m₁` and `M₂ = mkBitFinTM2 Λ₂ main₂ σ init₂ m₂`
into a single uniform `FinTM2` machine over 8 binary stacks with control label type `Λ₁ ⊕ Λ₂`
(`|Λ₁ ⊕ Λ₂| = |Λ₁| + |Λ₂|`), internal register `σ`, entry label `Sum.inl main₁`, and initial
state `init₁`. When `M₁` halts, the composed machine resets `var := init₂` and transitions directly
to `Sum.inr main₂`. -/
def seqBitFinTM2 (Λ₁ : Type) [Fintype Λ₁] (main₁ : Λ₁)
    (Λ₂ : Type) [Fintype Λ₂] (main₂ : Λ₂)
    (σ : Type) [Fintype σ] (init₁ init₂ : σ)
    (m₁ : Λ₁ → Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ)
    (m₂ : Λ₂ → Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ) : Turing.FinTM2 :=
  mkBitFinTM2 (Λ₁ ⊕ Λ₂) (Sum.inl main₁) σ init₁ (fun lbl =>
    match lbl with
    | Sum.inl l₁ => redirectHaltStmt main₂ init₂ (m₁ l₁)
    | Sum.inr l₂ => liftInrStmt (m₂ l₂))

/-- `seqBitFinTM2` preserves strict uniformity (`IsUniformFinTM2`), adding the control label bounds
`maxLabels₁ + maxLabels₂` and keeping `maxStates` and `maxAlpha` unchanged. -/
theorem isUniformFinTM2_seqBitFinTM2
    {Λ₁ : Type} [Fintype Λ₁] (main₁ : Λ₁)
    {Λ₂ : Type} [Fintype Λ₂] (main₂ : Λ₂)
    {σ : Type} [Fintype σ] (init₁ init₂ : σ)
    (m₁ : Λ₁ → Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ)
    (m₂ : Λ₂ → Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ)
    {maxLabels₁ maxLabels₂ maxStates maxAlpha : ℕ}
    (hΛ₁ : Fintype.card Λ₁ ≤ maxLabels₁)
    (hΛ₂ : Fintype.card Λ₂ ≤ maxLabels₂)
    (hσ : Fintype.card σ ≤ maxStates)
    (hΓ : 2 ≤ maxAlpha) :
    IsUniformFinTM2 (seqBitFinTM2 Λ₁ main₁ Λ₂ main₂ σ init₁ init₂ m₁ m₂)
      (maxLabels₁ + maxLabels₂) maxStates maxAlpha := by
  refine isUniformFinTM2_mkBitFinTM2 (Sum.inl main₁) init₁ _ ?_ hσ hΓ
  rw [Fintype.card_sum]
  exact Nat.add_le_add hΛ₁ hΛ₂

/-- Map a Phase-1 configuration into the sequential composition `Λ₁ ⊕ Λ₂`, mapping a halted Phase-1
configuration (`l = none`) to the Phase-2 entry `(some (Sum.inr entry₂), resetReg)`. -/
def mapSeqInlCfg {Λ₁ Λ₂ σ : Type} (entry₂ : Λ₂) (resetReg : σ)
    (cfg : Turing.TM2.Cfg BitTapeAlphabet Λ₁ σ) :
    Turing.TM2.Cfg BitTapeAlphabet (Λ₁ ⊕ Λ₂) σ :=
  match cfg.l with
  | some l₁ => ⟨some (Sum.inl l₁), cfg.var, cfg.stk⟩
  | none => ⟨some (Sum.inr entry₂), resetReg, cfg.stk⟩

/-- Map a Phase-2 configuration into the sequential composition `Λ₁ ⊕ Λ₂` via `Option.map Sum.inr`. -/
def mapSeqInrCfg {Λ₁ Λ₂ σ : Type}
    (cfg : Turing.TM2.Cfg BitTapeAlphabet Λ₂ σ) :
    Turing.TM2.Cfg BitTapeAlphabet (Λ₁ ⊕ Λ₂) σ :=
  ⟨cfg.l.map Sum.inr, cfg.var, cfg.stk⟩

theorem stepAux_redirectHaltStmt {Λ₁ Λ₂ σ : Type} (entry₂ : Λ₂) (resetReg : σ) :
    ∀ (q : Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ) (v : σ)
      (stk : ∀ k : TapeIdx, List (BitTapeAlphabet k)),
      Turing.TM2.stepAux (redirectHaltStmt entry₂ resetReg q) v stk =
        mapSeqInlCfg entry₂ resetReg (Turing.TM2.stepAux q v stk)
  | .push k f q, v, stk => stepAux_redirectHaltStmt entry₂ resetReg q v _
  | .peek k f q, v, stk => stepAux_redirectHaltStmt entry₂ resetReg q _ stk
  | .pop k f q, v, stk => stepAux_redirectHaltStmt entry₂ resetReg q _ _
  | .load a q, v, stk => stepAux_redirectHaltStmt entry₂ resetReg q _ stk
  | .branch p q₁ q₂, v, stk => by
    dsimp [redirectHaltStmt, Turing.TM2.stepAux]
    cases p v <;> simp [stepAux_redirectHaltStmt entry₂ resetReg]
  | .goto l, v, stk => rfl
  | .halt, v, stk => rfl

theorem stepAux_liftInrStmt {Λ₁ Λ₂ σ : Type} :
    ∀ (q : Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ) (v : σ)
      (stk : ∀ k : TapeIdx, List (BitTapeAlphabet k)),
      Turing.TM2.stepAux (liftInrStmt (Λ₁ := Λ₁) q) v stk =
        mapSeqInrCfg (Turing.TM2.stepAux q v stk)
  | .push k f q, v, stk => stepAux_liftInrStmt q v _
  | .peek k f q, v, stk => stepAux_liftInrStmt q _ stk
  | .pop k f q, v, stk => stepAux_liftInrStmt q _ _
  | .load a q, v, stk => stepAux_liftInrStmt q _ stk
  | .branch p q₁ q₂, v, stk => by
    dsimp [liftInrStmt, Turing.TM2.stepAux]
    cases p v <;> simp [stepAux_liftInrStmt]
  | .goto l, v, stk => rfl
  | .halt, v, stk => rfl

theorem step_seqBitFinTM2_inl
    {Λ₁ : Type} [Fintype Λ₁] (main₁ : Λ₁)
    {Λ₂ : Type} [Fintype Λ₂] (main₂ : Λ₂)
    {σ : Type} [Fintype σ] (init₁ init₂ : σ)
    (m₁ : Λ₁ → Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ)
    (m₂ : Λ₂ → Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ)
    (x y : (mkBitFinTM2 Λ₁ main₁ σ init₁ m₁).Cfg)
    (h : (mkBitFinTM2 Λ₁ main₁ σ init₁ m₁).step x = some y) :
    (seqBitFinTM2 Λ₁ main₁ Λ₂ main₂ σ init₁ init₂ m₁ m₂).step
      (mapSeqInlCfg main₂ init₂ x) =
      some (mapSeqInlCfg main₂ init₂ y) := by
  rcases x with ⟨lOpt, v, stk⟩
  cases lOpt with
  | none => cases h
  | some l₁ =>
    injection h with hy
    subst hy
    dsimp [seqBitFinTM2, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, mapSeqInlCfg]
    exact congrArg some (stepAux_redirectHaltStmt main₂ init₂ (m₁ l₁) v stk)

theorem step_seqBitFinTM2_inr
    {Λ₁ : Type} [Fintype Λ₁] (main₁ : Λ₁)
    {Λ₂ : Type} [Fintype Λ₂] (main₂ : Λ₂)
    {σ : Type} [Fintype σ] (init₁ init₂ : σ)
    (m₁ : Λ₁ → Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ)
    (m₂ : Λ₂ → Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ)
    (x y : (mkBitFinTM2 Λ₂ main₂ σ init₂ m₂).Cfg)
    (h : (mkBitFinTM2 Λ₂ main₂ σ init₂ m₂).step x = some y) :
    (seqBitFinTM2 Λ₁ main₁ Λ₂ main₂ σ init₁ init₂ m₁ m₂).step
      (mapSeqInrCfg x) =
      some (mapSeqInrCfg y) := by
  rcases x with ⟨lOpt, v, stk⟩
  cases lOpt with
  | none => cases h
  | some l₂ =>
    injection h with hy
    subst hy
    dsimp [seqBitFinTM2, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, mapSeqInrCfg]
    exact congrArg some (stepAux_liftInrStmt (m₂ l₂) v stk)

/-- **Sequential Composition Step-Bound Theorem (`seqBitFinTM2_evalsToInTime_concrete`)**:
If Phase 1 (`mkBitFinTM2 Λ₁ main₁ σ init₁ m₁`) evaluates `⟨some l₁, r₁, T₁⟩` to halted stack state
`⟨none, r_mid, T₂⟩` in `t₁` steps, and Phase 2 (`mkBitFinTM2 Λ₂ main₂ σ init₂ m₂`) evaluates
`⟨some main₂, init₂, T₂⟩` to halted stack state `⟨none, r₂, T₃⟩` in `t₂` steps, then the single
composed machine `seqBitFinTM2 Λ₁ main₁ Λ₂ main₂ σ init₁ init₂ m₁ m₂` evaluates
`⟨some (Sum.inl l₁), r₁, T₁⟩` to `⟨none, r₂, T₃⟩` in `t₁ + t₂` steps. -/
def seqBitFinTM2_evalsToInTime_concrete
    {Λ₁ : Type} [Fintype Λ₁] (main₁ : Λ₁)
    {Λ₂ : Type} [Fintype Λ₂] (main₂ : Λ₂)
    {σ : Type} [Fintype σ] (init₁ init₂ : σ)
    (m₁ : Λ₁ → Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ)
    (m₂ : Λ₂ → Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ)
    {l₁ : Λ₁} {r₁ r_mid r₂ : σ}
    {T₁ T₂ T₃ : ∀ k : TapeIdx, List (BitTapeAlphabet k)}
    {t₁ t₂ : ℕ}
    (h₁ : Turing.EvalsToInTime (mkBitFinTM2 Λ₁ main₁ σ init₁ m₁).step
      ⟨some l₁, r₁, T₁⟩ (some ⟨none, r_mid, T₂⟩) t₁)
    (h₂ : Turing.EvalsToInTime (mkBitFinTM2 Λ₂ main₂ σ init₂ m₂).step
      ⟨some main₂, init₂, T₂⟩ (some ⟨none, r₂, T₃⟩) t₂) :
    Turing.EvalsToInTime (seqBitFinTM2 Λ₁ main₁ Λ₂ main₂ σ init₁ init₂ m₁ m₂).step
      ⟨some (Sum.inl l₁), r₁, T₁⟩ (some ⟨none, r₂, T₃⟩) (t₁ + t₂) := by
  have hp₁ : Turing.EvalsToInTime (seqBitFinTM2 Λ₁ main₁ Λ₂ main₂ σ init₁ init₂ m₁ m₂).step
      ⟨some (Sum.inl l₁), r₁, T₁⟩ (some ⟨some (Sum.inr main₂), init₂, T₂⟩) t₁ :=
    EvalsToInTime.map_simulation (mapSeqInlCfg main₂ init₂)
      (step_seqBitFinTM2_inl main₁ main₂ init₁ init₂ m₁ m₂) h₁
  have hp₂ : Turing.EvalsToInTime (seqBitFinTM2 Λ₁ main₁ Λ₂ main₂ σ init₁ init₂ m₁ m₂).step
      ⟨some (Sum.inr main₂), init₂, T₂⟩ (some ⟨none, r₂, T₃⟩) t₂ :=
    EvalsToInTime.map_simulation mapSeqInrCfg
      (step_seqBitFinTM2_inr main₁ main₂ init₁ init₂ m₁ m₂) h₂
  exact EvalsToInTime.trans' hp₁ hp₂

/-! ## 5. Counter-Stack Loop / Iteration Combinator (`loopTapeBitFinTM2`) -/

/-- Redirect `Stmt.halt` in a loop-body statement over `Λ` to reset the register to `init : σ` and
return to the loop header `none : Option Λ`. -/
def redirectLoopBodyStmt {Λ σ : Type} (init : σ) :
    Turing.TM2.Stmt BitTapeAlphabet Λ σ → Turing.TM2.Stmt BitTapeAlphabet (Option Λ) σ
  | .push k f q => .push k f (redirectLoopBodyStmt init q)
  | .peek k f q => .peek k f (redirectLoopBodyStmt init q)
  | .pop k f q => .pop k f (redirectLoopBodyStmt init q)
  | .load a q => .load a (redirectLoopBodyStmt init q)
  | .branch p q₁ q₂ =>
    .branch p (redirectLoopBodyStmt init q₁) (redirectLoopBodyStmt init q₂)
  | .goto l => .goto (fun v => some (l v))
  | .halt => .load (fun _ => init) (.goto (fun _ => none))

/-- **Counter-Stack Loop Combinator (`loopTapeBitFinTM2`)**:
Wraps any 8-stack binary body machine (`Turing.FinTM2`) `(Λ, main, σ, init, m)` into a loop machine
over `Option Λ` (`|Option Λ| = |Λ| + 1` control labels, zero $n$-dependent state) controlled by
popping one token bit per iteration from counter/schedule stack `kCnt : TapeIdx`:
- At `none : Option Λ` (the loop header), the machine pops `kCnt`. If a token bit `some b` is
  present (`bOpt.isSome = true`), it resets the register to `init` and transitions to `some main`.
  If `kCnt` is empty (`bOpt = none`), it resets the register to `init` and halts.
- Inside `some l : Option Λ`, the machine executes `m l`, redirecting `Stmt.halt` back to `none`. -/
def loopTapeBitFinTM2 (kCnt : TapeIdx) (Λ : Type) [Fintype Λ] (main : Λ)
    (σ : Type) [Fintype σ] (init : σ)
    (setFlag : Bool → σ) (getFlag : σ → Bool)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ) : Turing.FinTM2 :=
  mkBitFinTM2 (Option Λ) none σ init (fun lbl =>
    match lbl with
    | none =>
      Turing.TM2.Stmt.pop kCnt
        (fun _ bOpt => setFlag bOpt.isSome)
        (Turing.TM2.Stmt.branch getFlag
          (Turing.TM2.Stmt.load (fun _ => init) (Turing.TM2.Stmt.goto (fun _ => some main)))
          (Turing.TM2.Stmt.load (fun _ => init) Turing.TM2.Stmt.halt))
    | some l => redirectLoopBodyStmt init (m l))

/-- `loopTapeBitFinTM2` adds only `+ 1` control label (`|Option Λ| = |Λ| + 1`) and preserves `|σ|`
and `|Γ k| = 2` (`IsUniformFinTM2`). -/
theorem isUniformFinTM2_loopTapeBitFinTM2 (kCnt : TapeIdx)
    {Λ : Type} [Fintype Λ] (main : Λ) {σ : Type} [Fintype σ] (init : σ)
    (setFlag : Bool → σ) (getFlag : σ → Bool)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ)
    {maxLabels maxStates maxAlpha : ℕ}
    (hΛ : Fintype.card Λ ≤ maxLabels)
    (hσ : Fintype.card σ ≤ maxStates)
    (hΓ : 2 ≤ maxAlpha) :
    IsUniformFinTM2 (loopTapeBitFinTM2 kCnt Λ main σ init setFlag getFlag m)
      (maxLabels + 1) maxStates maxAlpha := by
  refine isUniformFinTM2_mkBitFinTM2 none init _ ?_ hσ hΓ
  rw [Fintype.card_option]
  exact Nat.add_le_add_right hΛ 1

/-- Map a body configuration into `Option Λ`, sending `none` (body halt) to the loop header
`some none`. -/
def mapLoopBodyCfg {Λ σ : Type} (init : σ)
    (cfg : Turing.TM2.Cfg BitTapeAlphabet Λ σ) :
    Turing.TM2.Cfg BitTapeAlphabet (Option Λ) σ :=
  match cfg.l with
  | some l => ⟨some (some l), cfg.var, cfg.stk⟩
  | none => ⟨some none, init, cfg.stk⟩

theorem stepAux_redirectLoopBodyStmt {Λ σ : Type} (init : σ) :
    ∀ (q : Turing.TM2.Stmt BitTapeAlphabet Λ σ) (v : σ)
      (stk : ∀ k : TapeIdx, List (BitTapeAlphabet k)),
      Turing.TM2.stepAux (redirectLoopBodyStmt init q) v stk =
        mapLoopBodyCfg init (Turing.TM2.stepAux q v stk)
  | .push k f q, v, stk => stepAux_redirectLoopBodyStmt init q v _
  | .peek k f q, v, stk => stepAux_redirectLoopBodyStmt init q _ stk
  | .pop k f q, v, stk => stepAux_redirectLoopBodyStmt init q _ _
  | .load a q, v, stk => stepAux_redirectLoopBodyStmt init q _ stk
  | .branch p q₁ q₂, v, stk => by
    dsimp [redirectLoopBodyStmt, Turing.TM2.stepAux]
    cases p v <;> simp [stepAux_redirectLoopBodyStmt init]
  | .goto l, v, stk => rfl
  | .halt, v, stk => rfl

theorem step_loopTapeBitFinTM2_body (kCnt : TapeIdx)
    {Λ : Type} [Fintype Λ] (main : Λ) {σ : Type} [Fintype σ] (init : σ)
    (setFlag : Bool → σ) (getFlag : σ → Bool)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ)
    (x y : (mkBitFinTM2 Λ main σ init m).Cfg)
    (h : (mkBitFinTM2 Λ main σ init m).step x = some y) :
    (loopTapeBitFinTM2 kCnt Λ main σ init setFlag getFlag m).step
      (mapLoopBodyCfg init x) =
      some (mapLoopBodyCfg init y) := by
  rcases x with ⟨lOpt, v, stk⟩
  cases lOpt with
  | none => cases h
  | some l =>
    injection h with hy
    subst hy
    dsimp [loopTapeBitFinTM2, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, mapLoopBodyCfg]
    exact congrArg some (stepAux_redirectLoopBodyStmt init (m l) v stk)

/-- One body pass inside `loopTapeBitFinTM2` lifts any `B`-step body evaluation to a `B`-step
transition from `some (some main)` back to the loop header `some none`. -/
def loopTapeBitFinTM2_body_evalsToInTime_concrete (kCnt : TapeIdx)
    {Λ : Type} [Fintype Λ] (main : Λ) {σ : Type} [Fintype σ] (init : σ)
    (setFlag : Bool → σ) (getFlag : σ → Bool)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ)
    {r_end : σ} {T₁ T₂ : ∀ k : TapeIdx, List (BitTapeAlphabet k)} {B : ℕ}
    (hbody : Turing.EvalsToInTime (mkBitFinTM2 Λ main σ init m).step
      ⟨some main, init, T₁⟩ (some ⟨none, r_end, T₂⟩) B) :
    Turing.EvalsToInTime (loopTapeBitFinTM2 kCnt Λ main σ init setFlag getFlag m).step
      ⟨some (some main), init, T₁⟩ (some ⟨some none, init, T₂⟩) B :=
  EvalsToInTime.map_simulation (mapLoopBodyCfg init)
    (step_loopTapeBitFinTM2_body kCnt main init setFlag getFlag m) hbody

/-- **Multi-Pass Counter-Tape Loop Theorem (`loopTapeBitFinTM2_evalsToInTime_concrete`)**:
For any stack state family `stkOf : ℕ → (∀ k : TapeIdx, List (BitTapeAlphabet k))` where each pass
`i` (`i < cnt.length`) transforms `Function.update (stkOf i) kCnt cnt_tail` to
`Function.update (stkOf (i + 1)) kCnt cnt_tail` in at most `B` steps of the body machine, the
single uniform loop machine `loopTapeBitFinTM2 kCnt Λ main σ init setFlag getFlag m` executes
`cnt.length` passes and halts at `Function.update (stkOf cnt.length) kCnt []` in at most
`cnt.length * (B + 1) + 1` steps. -/
def loopTapeBitFinTM2_evalsToInTime_concrete (kCnt : TapeIdx)
    {Λ : Type} [Fintype Λ] (main : Λ) {σ : Type} [Fintype σ] (init : σ)
    (setFlag : Bool → σ) (getFlag : σ → Bool)
    (hFlagT : getFlag (setFlag true) = true)
    (hFlagF : getFlag (setFlag false) = false)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ)
    (B : ℕ) :
    ∀ (cnt : List Bool) (stkOf : ℕ → (∀ k : TapeIdx, List (BitTapeAlphabet k)))
      (rEndOf : ℕ → List Bool → σ),
      (∀ (i : ℕ) (rest : List Bool),
        Turing.EvalsToInTime (mkBitFinTM2 Λ main σ init m).step
          ⟨some main, init, Function.update (stkOf i) kCnt rest⟩
          (some ⟨none, rEndOf i rest, Function.update (stkOf (i + 1)) kCnt rest⟩) B) →
      Turing.EvalsToInTime (loopTapeBitFinTM2 kCnt Λ main σ init setFlag getFlag m).step
        ⟨some none, init, Function.update (stkOf 0) kCnt cnt⟩
        (some ⟨none, init, Function.update (stkOf cnt.length) kCnt []⟩)
        (cnt.length * (B + 1) + 1)
  | [], stkOf, _, _ => by
    refine EvalsToInTime.mono (EvalsToInTime.step_one ?_) (by simp)
    simp [loopTapeBitFinTM2, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux, hFlagF]
  | b :: cnt, stkOf, rEndOf, hpass => by
    have hpop : (loopTapeBitFinTM2 kCnt Λ main σ init setFlag getFlag m).step
        ⟨some none, init, Function.update (stkOf 0) kCnt (b :: cnt)⟩ =
        some ⟨some (some main), init, Function.update (stkOf 0) kCnt cnt⟩ := by
      simp [loopTapeBitFinTM2, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux, hFlagT]
    have hbody := hpass 0 cnt
    have hbody_lifted := loopTapeBitFinTM2_body_evalsToInTime_concrete kCnt main init
      setFlag getFlag m hbody
    have ih := loopTapeBitFinTM2_evalsToInTime_concrete kCnt main init setFlag getFlag
      hFlagT hFlagF m B cnt (fun i => stkOf (i + 1))
      (fun i rest => rEndOf (i + 1) rest)
      (fun i rest => hpass (i + 1) rest)
    have hstep1 := EvalsToInTime.of_step hpop hbody_lifted
    have hcomb := EvalsToInTime.trans' hstep1 ih
    simp only [List.length_cons] at hcomb ⊢
    exact EvalsToInTime.mono hcomb (by ring_nf; omega)

/-! ## 6. Composed Multi-Pass Uniform `FinTM2` Stages & Head-Transit / Reversal Bounds -/

/-! ### 6.1 Parameterized Stack-to-Stack Reverse Copy (`tmUniformRevCopyBetween`) & Composed Order-Preserving Copy (`tmComposedIdCopy`) -/

/-- Transition function for a uniform single-bit reverse-copy pass from source tape `kSrc` to
destination tape `kDst` over `UniformReg`. -/
def revCopyBetweenStmt (kSrc kDst : TapeIdx) :
    RevCopyLabel → Turing.TM2.Stmt BitTapeAlphabet RevCopyLabel UniformReg
  | .popIO =>
    Turing.TM2.Stmt.pop kSrc
      (fun _ bOpt =>
        match bOpt with
        | some b => { bitA := b, bitB := false, carry := true }
        | none => default)
      (Turing.TM2.Stmt.branch (fun r => r.carry)
        (Turing.TM2.Stmt.goto (fun _ => .pushWork))
        Turing.TM2.Stmt.halt)
  | .pushWork =>
    Turing.TM2.Stmt.push kDst (fun r => r.bitA)
      (Turing.TM2.Stmt.goto (fun _ => .popIO))

/-- Uniform 8-stack binary machine (`Turing.FinTM2`, `|Λ| = 2`, `|σ| = 8`, `|Γ k| = 2`) that reverses
any bitstream from stack `kSrc` onto stack `kDst` in `2 * xs.length + 1` `TM2.step` transitions. -/
def tmUniformRevCopyBetween (kSrc kDst : TapeIdx) : Turing.FinTM2 :=
  mkBitFinTM2 RevCopyLabel .popIO UniformReg default (revCopyBetweenStmt kSrc kDst)

theorem isUniformFinTM2_tmUniformRevCopyBetween (kSrc kDst : TapeIdx) :
    IsUniformFinTM2 (tmUniformRevCopyBetween kSrc kDst) 2 8 2 :=
  isUniformFinTM2_mkBitFinTM2 RevCopyLabel.popIO default (revCopyBetweenStmt kSrc kDst)
    (by decide) (by decide) (by decide)

/-- Loop evaluation of `tmUniformRevCopyBetween kWork0 kIO` reversing `ws` from `kWork0` onto `acc`
on `kIO` while leaving `w1` on `kWork1` unchanged, in `2 * ws.length + 1` steps. -/
def tmUniformRevCopy_work0_to_io_loop :
    ∀ (ws acc w1 : List Bool) (r : UniformReg),
      Turing.EvalsToInTime (tmUniformRevCopyBetween kWork0 kIO).step
        ⟨some .popIO, r, threeTapeWorkStk acc ws w1⟩
        (some ⟨none, default, threeTapeWorkStk (ws.reverse ++ acc) [] w1⟩)
        (2 * ws.length + 1)
  | [], acc, w1, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformRevCopyBetween, revCopyBetweenStmt, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, threeTapeWorkStk_kWork0, update_threeTapeWorkStk_kWork0,
      uniformReg_default_carry, List.head?_nil, List.tail_nil, List.reverse_nil, List.nil_append,
      cond_false]
  | b :: ws, acc, w1, r => by
    have h1 : (tmUniformRevCopyBetween kWork0 kIO).step
        ⟨some .popIO, r, threeTapeWorkStk acc (b :: ws) w1⟩ =
        some ⟨some .pushWork, { bitA := b, bitB := false, carry := true },
          threeTapeWorkStk acc ws w1⟩ := by
      simp [tmUniformRevCopyBetween, revCopyBetweenStmt, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux]
    have h2 : (tmUniformRevCopyBetween kWork0 kIO).step
        ⟨some .pushWork, { bitA := b, bitB := false, carry := true },
          threeTapeWorkStk acc ws w1⟩ =
        some ⟨some .popIO, { bitA := b, bitB := false, carry := true },
          threeTapeWorkStk (b :: acc) ws w1⟩ := by
      simp [tmUniformRevCopyBetween, revCopyBetweenStmt, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux]
    have ih := tmUniformRevCopy_work0_to_io_loop ws (b :: acc) w1
      { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step h1 (EvalsToInTime.of_step h2 ih))
      (by simp [List.length_cons]; omega)

/-- Loop evaluation of `tmUniformRevCopyBetween kIO kWork0` reversing `xs` from `kIO` onto `acc`
on `kWork0` while leaving `w1` on `kWork1` unchanged, in `2 * xs.length + 1` steps. -/
def tmUniformRevCopy_io_to_work0_loop :
    ∀ (xs acc w1 : List Bool) (r : UniformReg),
      Turing.EvalsToInTime (tmUniformRevCopyBetween kIO kWork0).step
        ⟨some .popIO, r, threeTapeWorkStk xs acc w1⟩
        (some ⟨none, default, threeTapeWorkStk [] (xs.reverse ++ acc) w1⟩)
        (2 * xs.length + 1)
  | [], acc, w1, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformRevCopyBetween, revCopyBetweenStmt, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, threeTapeWorkStk_kIO, update_threeTapeWorkStk_kIO,
      uniformReg_default_carry, List.head?_nil, List.tail_nil, List.reverse_nil, List.nil_append,
      cond_false]
  | b :: xs, acc, w1, r => by
    have h1 : (tmUniformRevCopyBetween kIO kWork0).step
        ⟨some .popIO, r, threeTapeWorkStk (b :: xs) acc w1⟩ =
        some ⟨some .pushWork, { bitA := b, bitB := false, carry := true },
          threeTapeWorkStk xs acc w1⟩ := by
      simp [tmUniformRevCopyBetween, revCopyBetweenStmt, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux]
    have h2 : (tmUniformRevCopyBetween kIO kWork0).step
        ⟨some .pushWork, { bitA := b, bitB := false, carry := true },
          threeTapeWorkStk xs acc w1⟩ =
        some ⟨some .popIO, { bitA := b, bitB := false, carry := true },
          threeTapeWorkStk xs (b :: acc) w1⟩ := by
      simp [tmUniformRevCopyBetween, revCopyBetweenStmt, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux]
    have ih := tmUniformRevCopy_io_to_work0_loop xs (b :: acc) w1
      { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step h1 (EvalsToInTime.of_step h2 ih))
      (by simp [List.length_cons]; omega)

/-- **Composed Order-Preserving Copy Machine (`tmComposedIdCopy`)**:
Constructed via `seqBitFinTM2` from `tmUniformRevCopyBetween kIO kWork0` (`|Λ₁| = 2`) followed by
`tmUniformRevCopyBetween kWork0 kIO` (`|Λ₂| = 2`). Streams `xs` from `kIO` to `kWork0` and back to
`kIO`, accounting for both forward head transit and head reversal in `4 * xs.length + 2` steps. -/
def tmComposedIdCopy : Turing.FinTM2 :=
  seqBitFinTM2 RevCopyLabel .popIO RevCopyLabel .popIO UniformReg default default
    (revCopyBetweenStmt kIO kWork0) (revCopyBetweenStmt kWork0 kIO)

theorem isUniformFinTM2_tmComposedIdCopy : IsUniformFinTM2 tmComposedIdCopy 4 8 2 :=
  isUniformFinTM2_mkBitFinTM2 (Sum.inl RevCopyLabel.popIO) default tmComposedIdCopy.m
    (by decide) (by decide) (by decide)

/-- Constructive evaluation of `tmComposedIdCopy` on `xs` (with arbitrary `w1` on `kWork1`) in
`4 * xs.length + 2` steps via `seqBitFinTM2_evalsToInTime_concrete`. -/
def tmComposedIdCopy_threeTape_evalsToInTime_concrete (xs w1 : List Bool) :
    Turing.EvalsToInTime tmComposedIdCopy.step
      ⟨some (Sum.inl RevCopyLabel.popIO), default, threeTapeWorkStk xs [] w1⟩
      (some ⟨none, default, threeTapeWorkStk xs [] w1⟩)
      (4 * xs.length + 2) := by
  have hp1 := tmUniformRevCopy_io_to_work0_loop xs [] w1 default
  rw [List.append_nil] at hp1
  have hp2 := tmUniformRevCopy_work0_to_io_loop xs.reverse [] w1 default
  rw [List.reverse_reverse, List.append_nil, List.length_reverse] at hp2
  exact EvalsToInTime.mono
    (seqBitFinTM2_evalsToInTime_concrete RevCopyLabel.popIO RevCopyLabel.popIO default default
      (revCopyBetweenStmt kIO kWork0) (revCopyBetweenStmt kWork0 kIO) hp1 hp2)
    (by omega)

/-- Concrete evaluation of `tmComposedIdCopy` from `Turing.initList` to `Turing.haltList` in
`4 * xs.length + 2` steps. -/
def tmComposedIdCopy_evalsToInTime_concrete (xs : List Bool) :
    Turing.EvalsToInTime tmComposedIdCopy.step
      (Turing.initList tmComposedIdCopy xs)
      (some (Turing.haltList tmComposedIdCopy xs))
      (4 * xs.length + 2) := by
  have hinit : Turing.initList tmComposedIdCopy xs =
      ⟨some (Sum.inl RevCopyLabel.popIO), default, threeTapeWorkStk xs [] []⟩ := by
    rw [threeTapeWorkStk_nil, twoTapeStk_nil]; rfl
  have hhalt : Turing.haltList tmComposedIdCopy xs =
      ⟨none, default, threeTapeWorkStk xs [] []⟩ := by
    rw [threeTapeWorkStk_nil, twoTapeStk_nil]; rfl
  rw [hinit, hhalt]
  exact tmComposedIdCopy_threeTape_evalsToInTime_concrete xs []

theorem tmComposedIdCopy_evalsToInTime (xs : List Bool) :
    ∃ t ≤ 4 * xs.length + 2,
      Turing.EvalsToInTime tmComposedIdCopy.step
        (Turing.initList tmComposedIdCopy xs)
        (some (Turing.haltList tmComposedIdCopy xs)) t :=
  ⟨_, le_rfl, ⟨tmComposedIdCopy_evalsToInTime_concrete xs⟩⟩

/-! ### 6.2 Composed Deinterleave-Interleave Pass, Order-Preserving Shuffle Pass & Multi-Pass Bit-Transpose -/

/-- Transition function of `tmUniformDeinterleave`. -/
def deinterleaveStmt :
    DeinterleaveLabel → Turing.TM2.Stmt BitTapeAlphabet DeinterleaveLabel UniformReg :=
  tmUniformDeinterleave.m

/-- Transition function of `tmUniformInterleave`. -/
def interleaveStmt :
    InterleaveLabel → Turing.TM2.Stmt BitTapeAlphabet InterleaveLabel UniformReg :=
  tmUniformInterleave.m

/-- **Composed 2-Stage Deinterleave-Interleave Machine (`tmComposedDeinterleaveInterleave`)**:
Sequential composition (`seqBitFinTM2`) of `tmUniformDeinterleave` (`|Λ₁| = 4`, splitting `kIO`
into reversed even/odd streams on `kWork0`/`kWork1`) and `tmUniformInterleave` (`|Λ₂| = 6`,
interleaving `kWork0` and `kWork1` back onto `kIO`). Has `|Λ| = 10`, `|σ| = 8`, `|Γ k| = 2`,
and transforms `flattenBitPairs ps` on `kIO` into `flattenBitPairs ps.reverse` on `kIO` in
`12 * ps.length + 3` single-bit steps. -/
def tmComposedDeinterleaveInterleave : Turing.FinTM2 :=
  seqBitFinTM2 DeinterleaveLabel .popEven InterleaveLabel .popEven
    UniformReg default default deinterleaveStmt interleaveStmt

theorem isUniformFinTM2_tmComposedDeinterleaveInterleave :
    IsUniformFinTM2 tmComposedDeinterleaveInterleave 10 8 2 :=
  isUniformFinTM2_mkBitFinTM2 (Sum.inl DeinterleaveLabel.popEven) default
    tmComposedDeinterleaveInterleave.m (by decide) (by decide) (by decide)

/-- Constructive evaluation of `tmComposedDeinterleaveInterleave` on `flattenBitPairs ps` in
`12 * ps.length + 3` steps via `seqBitFinTM2_evalsToInTime_concrete`. -/
def tmComposedDeinterleaveInterleave_evalsToInTime_concrete (ps : List (Bool × Bool)) :
    Turing.EvalsToInTime tmComposedDeinterleaveInterleave.step
      (Turing.initList tmComposedDeinterleaveInterleave (flattenBitPairs ps))
      (some (Turing.haltList tmComposedDeinterleaveInterleave (flattenBitPairs ps.reverse)))
      (12 * ps.length + 3) := by
  have hp1 : Turing.EvalsToInTime
      (mkBitFinTM2 DeinterleaveLabel .popEven UniformReg default deinterleaveStmt).step
      ⟨some .popEven, default, singleTapeStk (flattenBitPairs ps)⟩
      (some ⟨none, default,
        threeTapeWorkStk [] (ps.map Prod.fst).reverse (ps.map Prod.snd).reverse⟩)
      (4 * ps.length + 1) :=
    tmUniformDeinterleave_evalsToInTime_concrete ps
  have hp2_raw := tmUniformInterleave_evalsToInTime_concrete ps.reverse
  simp only [List.map_reverse, List.length_reverse] at hp2_raw
  have hp2 : Turing.EvalsToInTime
      (mkBitFinTM2 InterleaveLabel .popEven UniformReg default interleaveStmt).step
      ⟨some .popEven, default,
        threeTapeWorkStk [] (ps.map Prod.fst).reverse (ps.map Prod.snd).reverse⟩
      (some ⟨none, default, singleTapeStk (flattenBitPairs ps.reverse)⟩)
      (8 * ps.length + 2) := hp2_raw
  have hseq := seqBitFinTM2_evalsToInTime_concrete
    DeinterleaveLabel.popEven InterleaveLabel.popEven default default
    deinterleaveStmt interleaveStmt hp1 hp2
  exact EvalsToInTime.mono hseq (by omega)

theorem tmComposedDeinterleaveInterleave_evalsToInTime (ps : List (Bool × Bool)) :
    ∃ t ≤ 12 * ps.length + 3,
      Turing.EvalsToInTime tmComposedDeinterleaveInterleave.step
        (Turing.initList tmComposedDeinterleaveInterleave (flattenBitPairs ps))
        (some (Turing.haltList tmComposedDeinterleaveInterleave (flattenBitPairs ps.reverse))) t :=
  ⟨_, le_rfl, ⟨tmComposedDeinterleaveInterleave_evalsToInTime_concrete ps⟩⟩

/-- **Composed Order-Preserving Bit-Shuffle Pass (`tmComposedOrderPreservingShuffle`)**:
Sequential composition (`seqBitFinTM2`) of two `tmComposedDeinterleaveInterleave` passes (`|Λ| = 20`,
`|σ| = 8`, `|Γ k| = 2`). Performs a full deinterleave onto `kWork0`/`kWork1`, re-interleaves onto
`kIO`, deinterleaves again onto `kWork0`/`kWork1`, and re-interleaves onto `kIO` to recover
`flattenBitPairs ps` in `24 * ps.length + 6` single-bit steps (accounting for all head transits
and reversals across `kIO`, `kWork0`, `kWork1`, and `kWork2`). -/
def tmComposedOrderPreservingShuffle : Turing.FinTM2 :=
  seqBitFinTM2
    (DeinterleaveLabel ⊕ InterleaveLabel) (Sum.inl .popEven)
    (DeinterleaveLabel ⊕ InterleaveLabel) (Sum.inl .popEven)
    UniformReg default default
    tmComposedDeinterleaveInterleave.m
    tmComposedDeinterleaveInterleave.m

theorem isUniformFinTM2_tmComposedOrderPreservingShuffle :
    IsUniformFinTM2 tmComposedOrderPreservingShuffle 20 8 2 :=
  isUniformFinTM2_mkBitFinTM2 (Sum.inl (Sum.inl DeinterleaveLabel.popEven)) default
    tmComposedOrderPreservingShuffle.m (by decide) (by decide) (by decide)

/-- Constructive evaluation of `tmComposedOrderPreservingShuffle` recovering `flattenBitPairs ps`
in `24 * ps.length + 6` steps. -/
def tmComposedOrderPreservingShuffle_evalsToInTime_concrete (ps : List (Bool × Bool)) :
    Turing.EvalsToInTime tmComposedOrderPreservingShuffle.step
      (Turing.initList tmComposedOrderPreservingShuffle (flattenBitPairs ps))
      (some (Turing.haltList tmComposedOrderPreservingShuffle (flattenBitPairs ps)))
      (24 * ps.length + 6) := by
  have hp1 : Turing.EvalsToInTime
      (mkBitFinTM2 (DeinterleaveLabel ⊕ InterleaveLabel) (Sum.inl DeinterleaveLabel.popEven)
        UniformReg default tmComposedDeinterleaveInterleave.m).step
      ⟨some (Sum.inl DeinterleaveLabel.popEven), default, singleTapeStk (flattenBitPairs ps)⟩
      (some ⟨none, default, singleTapeStk (flattenBitPairs ps.reverse)⟩)
      (12 * ps.length + 3) :=
    tmComposedDeinterleaveInterleave_evalsToInTime_concrete ps
  have hp2_raw := tmComposedDeinterleaveInterleave_evalsToInTime_concrete ps.reverse
  rw [List.reverse_reverse, List.length_reverse] at hp2_raw
  have hp2 : Turing.EvalsToInTime
      (mkBitFinTM2 (DeinterleaveLabel ⊕ InterleaveLabel) (Sum.inl DeinterleaveLabel.popEven)
        UniformReg default tmComposedDeinterleaveInterleave.m).step
      ⟨some (Sum.inl DeinterleaveLabel.popEven), default,
        singleTapeStk (flattenBitPairs ps.reverse)⟩
      (some ⟨none, default, singleTapeStk (flattenBitPairs ps)⟩)
      (12 * ps.length + 3) := hp2_raw
  have hseq := seqBitFinTM2_evalsToInTime_concrete
    (Sum.inl DeinterleaveLabel.popEven) (Sum.inl DeinterleaveLabel.popEven)
    default default tmComposedDeinterleaveInterleave.m tmComposedDeinterleaveInterleave.m
    hp1 hp2
  exact EvalsToInTime.mono hseq (by omega)

theorem tmComposedOrderPreservingShuffle_evalsToInTime (ps : List (Bool × Bool)) :
    ∃ t ≤ 24 * ps.length + 6,
      Turing.EvalsToInTime tmComposedOrderPreservingShuffle.step
        (Turing.initList tmComposedOrderPreservingShuffle (flattenBitPairs ps))
        (some (Turing.haltList tmComposedOrderPreservingShuffle (flattenBitPairs ps))) t :=
  ⟨_, le_rfl, ⟨tmComposedOrderPreservingShuffle_evalsToInTime_concrete ps⟩⟩

/-- Two-tape stack assignment with `s` on `kIO` and `sched` on `kSched` (`kWork0..kWork5 = []`). -/
def ioSchedStk (s sched : List Bool) (k : TapeIdx) : List (BitTapeAlphabet k) :=
  Function.update (singleTapeStk s) kSched sched k

@[simp]
theorem ioSchedStk_nil (s : List Bool) :
    ioSchedStk s [] = singleTapeStk s := by
  funext k
  by_cases hk : k = kSched
  · subst hk
    have hne : kSched ≠ kIO := by decide
    simp [ioSchedStk, singleTapeStk, hne]
  · simp [ioSchedStk, hk]

/-- **Schedule-Driven Multi-Pass Bit-Transpose Machine (`tmComposedMultiPassTranspose`)**:
Wraps `tmComposedOrderPreservingShuffle` in `loopTapeBitFinTM2 kSched` (`|Λ| = 21`, `|σ| = 8`,
`|Γ k| = 2`). Pops one pass token per stage from `kSched`, executing `K = sched.length` streaming
deinterleave/interleave passes across `kIO`, `kWork0`, `kWork1`, and `kWork2` in
`K * (24 * ps.length + 7) + 1 = Θ(K * ps.length)` single-bit `FinTM2` steps. -/
def tmComposedMultiPassTranspose : Turing.FinTM2 :=
  loopTapeBitFinTM2 kSched
    tmComposedOrderPreservingShuffle.Λ (Sum.inl (Sum.inl .popEven))
    UniformReg default
    (fun b => { bitA := false, bitB := false, carry := b })
    (fun r => r.carry)
    tmComposedOrderPreservingShuffle.m

theorem isUniformFinTM2_tmComposedMultiPassTranspose :
    IsUniformFinTM2 tmComposedMultiPassTranspose 21 8 2 :=
  isUniformFinTM2_mkBitFinTM2 none default tmComposedMultiPassTranspose.m
    (by decide) (by decide) (by decide)

/-- Predicate stating that a `Turing.TM2.Stmt` never accesses tape `kSched`. -/
def StmtAvoidsSched {Λ σ : Type} : Turing.TM2.Stmt BitTapeAlphabet Λ σ → Prop
  | .push k _ q => k ≠ kSched ∧ StmtAvoidsSched q
  | .peek k _ q => k ≠ kSched ∧ StmtAvoidsSched q
  | .pop k _ q => k ≠ kSched ∧ StmtAvoidsSched q
  | .load _ q => StmtAvoidsSched q
  | .branch _ q₁ q₂ => StmtAvoidsSched q₁ ∧ StmtAvoidsSched q₂
  | .goto _ => True
  | .halt => True

def mapUpdateSchedCfg {Λ σ : Type} (sched : List Bool)
    (cfg : Turing.TM2.Cfg BitTapeAlphabet Λ σ) :
    Turing.TM2.Cfg BitTapeAlphabet Λ σ :=
  ⟨cfg.l, cfg.var, Function.update cfg.stk kSched sched⟩

theorem stepAux_preserveSchedTape {Λ σ : Type} (sched : List Bool) :
    ∀ (q : Turing.TM2.Stmt BitTapeAlphabet Λ σ) (_hq : StmtAvoidsSched q) (v : σ)
      (stk : ∀ k : TapeIdx, List (BitTapeAlphabet k)),
      Turing.TM2.stepAux q v (Function.update stk kSched sched) =
        mapUpdateSchedCfg sched (Turing.TM2.stepAux q v stk)
  | .push k f q, ⟨hne, hq⟩, v, stk => by
    dsimp [Turing.TM2.stepAux]
    have hget : Function.update stk kSched sched k = stk k := Function.update_of_ne hne _ _
    have hupd : Function.update (Function.update stk kSched sched) k (f v :: stk k) =
        Function.update (Function.update stk k (f v :: stk k)) kSched sched :=
      Function.update_comm hne.symm _ _ _
    rw [hget, hupd]
    exact stepAux_preserveSchedTape sched q hq v _
  | .peek k f q, ⟨hne, hq⟩, v, stk => by
    dsimp [Turing.TM2.stepAux]
    have hget : Function.update stk kSched sched k = stk k := Function.update_of_ne hne _ _
    rw [hget]
    exact stepAux_preserveSchedTape sched q hq _ stk
  | .pop k f q, ⟨hne, hq⟩, v, stk => by
    dsimp [Turing.TM2.stepAux]
    have hget : Function.update stk kSched sched k = stk k := Function.update_of_ne hne _ _
    have hupd : Function.update (Function.update stk kSched sched) k (stk k).tail =
        Function.update (Function.update stk k (stk k).tail) kSched sched :=
      Function.update_comm hne.symm _ _ _
    rw [hget, hupd]
    exact stepAux_preserveSchedTape sched q hq _ _
  | .load a q, hq, v, stk => stepAux_preserveSchedTape sched q hq _ stk
  | .branch p q₁ q₂, ⟨hq₁, hq₂⟩, v, stk => by
    dsimp [Turing.TM2.stepAux]
    cases p v
    · exact stepAux_preserveSchedTape sched q₂ hq₂ v stk
    · exact stepAux_preserveSchedTape sched q₁ hq₁ v stk
  | .goto l, _, v, stk => rfl
  | .halt, _, v, stk => rfl

/-- Any `mkBitFinTM2` machine whose statements avoid `kSched` preserves arbitrary contents `sched`
on `kSched` step-for-step. -/
def evalsToInTime_update_kSched {Λ : Type} [Fintype Λ] (main : Λ)
    {σ : Type} [Fintype σ] (init : σ)
    (m : Λ → Turing.TM2.Stmt BitTapeAlphabet Λ σ)
    (hm : ∀ l : Λ, StmtAvoidsSched (m l))
    (sched : List Bool)
    {l₁ : Option Λ} {r₁ r₂ : σ}
    {T₁ T₂ : ∀ k : TapeIdx, List (BitTapeAlphabet k)} {t : ℕ}
    (h : Turing.EvalsToInTime (mkBitFinTM2 Λ main σ init m).step
      ⟨l₁, r₁, T₁⟩ (some ⟨none, r₂, T₂⟩) t) :
    Turing.EvalsToInTime (mkBitFinTM2 Λ main σ init m).step
      ⟨l₁, r₁, Function.update T₁ kSched sched⟩
      (some ⟨none, r₂, Function.update T₂ kSched sched⟩) t :=
  EvalsToInTime.map_simulation
    (mapUpdateSchedCfg sched)
    (fun x y hstep => by
      rcases x with ⟨lOpt, v, stk⟩
      cases lOpt with
      | none => cases hstep
      | some l =>
        injection hstep with hy
        subst hy
        dsimp [mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step, mapUpdateSchedCfg]
        exact congrArg some (stepAux_preserveSchedTape sched (m l) (hm l) v stk))
    h

theorem stmtAvoidsSched_redirectHaltStmt {Λ₁ Λ₂ σ : Type} (entry₂ : Λ₂) (resetReg : σ) :
    ∀ (q : Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ),
      StmtAvoidsSched q → StmtAvoidsSched (redirectHaltStmt entry₂ resetReg q)
  | .push _ _ q, ⟨hne, hq⟩ => ⟨hne, stmtAvoidsSched_redirectHaltStmt entry₂ resetReg q hq⟩
  | .peek _ _ q, ⟨hne, hq⟩ => ⟨hne, stmtAvoidsSched_redirectHaltStmt entry₂ resetReg q hq⟩
  | .pop _ _ q, ⟨hne, hq⟩ => ⟨hne, stmtAvoidsSched_redirectHaltStmt entry₂ resetReg q hq⟩
  | .load _ q, hq => stmtAvoidsSched_redirectHaltStmt entry₂ resetReg q hq
  | .branch _ q₁ q₂, ⟨hq₁, hq₂⟩ =>
    ⟨stmtAvoidsSched_redirectHaltStmt entry₂ resetReg q₁ hq₁,
     stmtAvoidsSched_redirectHaltStmt entry₂ resetReg q₂ hq₂⟩
  | .goto _, _ => trivial
  | .halt, _ => trivial

theorem stmtAvoidsSched_liftInrStmt {Λ₁ Λ₂ σ : Type} :
    ∀ (q : Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ),
      StmtAvoidsSched q → StmtAvoidsSched (liftInrStmt (Λ₁ := Λ₁) q)
  | .push _ _ q, ⟨hne, hq⟩ => ⟨hne, stmtAvoidsSched_liftInrStmt q hq⟩
  | .peek _ _ q, ⟨hne, hq⟩ => ⟨hne, stmtAvoidsSched_liftInrStmt q hq⟩
  | .pop _ _ q, ⟨hne, hq⟩ => ⟨hne, stmtAvoidsSched_liftInrStmt q hq⟩
  | .load _ q, hq => stmtAvoidsSched_liftInrStmt q hq
  | .branch _ q₁ q₂, ⟨hq₁, hq₂⟩ =>
    ⟨stmtAvoidsSched_liftInrStmt q₁ hq₁, stmtAvoidsSched_liftInrStmt q₂ hq₂⟩
  | .goto _, _ => trivial
  | .halt, _ => trivial

theorem stmtAvoidsSched_liftUniformRegStmt {Λ : Type} :
    ∀ (q : Turing.TM2.Stmt BitTapeAlphabet Λ UniformReg),
      StmtAvoidsSched q → StmtAvoidsSched (liftUniformRegStmt q)
  | .push _ _ q, ⟨hne, hq⟩ => ⟨hne, stmtAvoidsSched_liftUniformRegStmt q hq⟩
  | .peek _ _ q, ⟨hne, hq⟩ => ⟨hne, stmtAvoidsSched_liftUniformRegStmt q hq⟩
  | .pop _ _ q, ⟨hne, hq⟩ => ⟨hne, stmtAvoidsSched_liftUniformRegStmt q hq⟩
  | .load _ q, hq => stmtAvoidsSched_liftUniformRegStmt q hq
  | .branch _ q₁ q₂, ⟨hq₁, hq₂⟩ =>
    ⟨stmtAvoidsSched_liftUniformRegStmt q₁ hq₁, stmtAvoidsSched_liftUniformRegStmt q₂ hq₂⟩
  | .goto _, _ => trivial
  | .halt, _ => trivial

theorem stmtAvoidsSched_deinterleaveStmt (l : DeinterleaveLabel) :
    StmtAvoidsSched (deinterleaveStmt l) := by
  cases l <;> refine ⟨by decide, ?_⟩ <;> trivial

theorem stmtAvoidsSched_interleaveStmt (l : InterleaveLabel) :
    StmtAvoidsSched (interleaveStmt l) := by
  cases l <;> refine ⟨by decide, ?_⟩ <;> trivial

theorem stmtAvoidsSched_tmComposedDeinterleaveInterleave
    (l : DeinterleaveLabel ⊕ InterleaveLabel) :
    StmtAvoidsSched (tmComposedDeinterleaveInterleave.m l) := by
  rcases l with l₁ | l₂
  · exact stmtAvoidsSched_redirectHaltStmt _ _ _ (stmtAvoidsSched_deinterleaveStmt l₁)
  · exact stmtAvoidsSched_liftInrStmt _ (stmtAvoidsSched_interleaveStmt l₂)

theorem stmtAvoidsSched_tmComposedOrderPreservingShuffle
    (l : tmComposedOrderPreservingShuffle.Λ) :
    StmtAvoidsSched (tmComposedOrderPreservingShuffle.m l) := by
  rcases l with l₁ | l₂
  · exact stmtAvoidsSched_redirectHaltStmt _ _ _
      (stmtAvoidsSched_tmComposedDeinterleaveInterleave l₁)
  · exact stmtAvoidsSched_liftInrStmt _
      (stmtAvoidsSched_tmComposedDeinterleaveInterleave l₂)

/-- **Constructive Multi-Pass Bit-Transpose Step-Bound Theorem
(`tmComposedMultiPassTranspose_evalsToInTime_concrete`)**:
For any pair stream `ps : List (Bool × Bool)` on `kIO` and any `K = sched.length` pass tokens on
`kSched`, the single uniform machine `tmComposedMultiPassTranspose` (`|Λ| = 21`, `|σ| = 8`,
`|Γ k| = 2`) executes `sched.length` full streaming deinterleave/interleave passes across the work
tapes and halts with `flattenBitPairs ps` on `kIO` and `[]` on `kSched` in at most
`sched.length * (24 * ps.length + 7) + 1` single-bit `FinTM2` steps. -/
def tmComposedMultiPassTranspose_evalsToInTime_concrete
    (sched : List Bool) (ps : List (Bool × Bool)) :
    Turing.EvalsToInTime tmComposedMultiPassTranspose.step
      ⟨some none, default, ioSchedStk (flattenBitPairs ps) sched⟩
      (some (Turing.haltList tmComposedMultiPassTranspose (flattenBitPairs ps)))
      (sched.length * (24 * ps.length + 7) + 1) := by
  have hrun := loopTapeBitFinTM2_evalsToInTime_concrete kSched
    (Sum.inl (Sum.inl DeinterleaveLabel.popEven)) default
    (fun b => { bitA := false, bitB := false, carry := b })
    (fun r => r.carry) rfl rfl
    tmComposedOrderPreservingShuffle.m
    (24 * ps.length + 6)
    sched
    (fun _ => singleTapeStk (flattenBitPairs ps))
    (fun _ _ => default)
    (fun _ rest =>
      evalsToInTime_update_kSched
        (Sum.inl (Sum.inl DeinterleaveLabel.popEven)) default
        tmComposedOrderPreservingShuffle.m
        stmtAvoidsSched_tmComposedOrderPreservingShuffle
        rest
        (tmComposedOrderPreservingShuffle_evalsToInTime_concrete ps))
  have hstk : Function.update (singleTapeStk (flattenBitPairs ps)) kSched [] =
      singleTapeStk (flattenBitPairs ps) :=
    ioSchedStk_nil (flattenBitPairs ps)
  rw [hstk] at hrun
  exact hrun

theorem tmComposedMultiPassTranspose_evalsToInTime
    (sched : List Bool) (ps : List (Bool × Bool)) :
    ∃ t ≤ sched.length * (24 * ps.length + 7) + 1,
      Turing.EvalsToInTime tmComposedMultiPassTranspose.step
        ⟨some none, default, ioSchedStk (flattenBitPairs ps) sched⟩
        (some (Turing.haltList tmComposedMultiPassTranspose (flattenBitPairs ps))) t :=
  ⟨_, le_rfl, ⟨tmComposedMultiPassTranspose_evalsToInTime_concrete sched ps⟩⟩

/-! ### 6.3 Composed Simultaneous Butterfly + Difference Packing Stage (`tmComposedButterflyStage`) -/

/-- Transition function of `tmUniformButterflyAddSub`. -/
def butterflyAddSubStmt :
    ButterflyAddSubLabel → Turing.TM2.Stmt BitTapeAlphabet ButterflyAddSubLabel ButterflyReg :=
  tmUniformButterflyAddSub.m

/-- Transition function for a 2-pass order-preserving transfer of the butterfly difference from
`kWork0` (via `kWork1`) onto `kIO` (`|Λ| = 4`, `|σ| = 8`). -/
def transferWork0ViaWork1ToIOStmt :
    IdCopyLabel → Turing.TM2.Stmt BitTapeAlphabet IdCopyLabel UniformReg
  | .popIO =>
    Turing.TM2.Stmt.pop kWork0
      (fun _ bOpt =>
        match bOpt with
        | some b => { bitA := b, bitB := false, carry := true }
        | none => default)
      (Turing.TM2.Stmt.branch (fun r => r.carry)
        (Turing.TM2.Stmt.goto (fun _ => .pushWork))
        (Turing.TM2.Stmt.goto (fun _ => .popWork)))
  | .pushWork =>
    Turing.TM2.Stmt.push kWork1 (fun r => r.bitA)
      (Turing.TM2.Stmt.goto (fun _ => .popIO))
  | .popWork =>
    Turing.TM2.Stmt.pop kWork1
      (fun _ bOpt =>
        match bOpt with
        | some b => { bitA := b, bitB := false, carry := true }
        | none => default)
      (Turing.TM2.Stmt.branch (fun r => r.carry)
        (Turing.TM2.Stmt.goto (fun _ => .pushIO))
        Turing.TM2.Stmt.halt)
  | .pushIO =>
    Turing.TM2.Stmt.push kIO (fun r => r.bitA)
      (Turing.TM2.Stmt.goto (fun _ => .popWork))

def tmTransferWork0ViaWork1ToIO : Turing.FinTM2 :=
  mkBitFinTM2 IdCopyLabel .popIO UniformReg default transferWork0ViaWork1ToIOStmt

def tmTransferWork0ViaWork1ToIO_pass1 :
    ∀ (ws acc s : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmTransferWork0ViaWork1ToIO.step
        ⟨some .popIO, r, threeTapeWorkStk s ws acc⟩
        (some ⟨some .popWork, default, threeTapeWorkStk s [] (ws.reverse ++ acc)⟩)
        (2 * ws.length + 1)
  | [], acc, s, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmTransferWork0ViaWork1ToIO, transferWork0ViaWork1ToIOStmt, mkBitFinTM2,
      Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux, threeTapeWorkStk_kWork0,
      update_threeTapeWorkStk_kWork0, uniformReg_default_carry, List.head?_nil, List.tail_nil,
      List.reverse_nil, List.nil_append, cond_false]
  | b :: ws, acc, s, r => by
    have h1 : tmTransferWork0ViaWork1ToIO.step
        ⟨some .popIO, r, threeTapeWorkStk s (b :: ws) acc⟩ =
        some ⟨some .pushWork, { bitA := b, bitB := false, carry := true },
          threeTapeWorkStk s ws acc⟩ := by
      simp [tmTransferWork0ViaWork1ToIO, transferWork0ViaWork1ToIOStmt, mkBitFinTM2,
        Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have h2 : tmTransferWork0ViaWork1ToIO.step
        ⟨some .pushWork, { bitA := b, bitB := false, carry := true },
          threeTapeWorkStk s ws acc⟩ =
        some ⟨some .popIO, { bitA := b, bitB := false, carry := true },
          threeTapeWorkStk s ws (b :: acc)⟩ := by
      simp [tmTransferWork0ViaWork1ToIO, transferWork0ViaWork1ToIOStmt, mkBitFinTM2,
        Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have ih := tmTransferWork0ViaWork1ToIO_pass1 ws (b :: acc) s
      { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step h1 (EvalsToInTime.of_step h2 ih))
      (by simp [List.length_cons]; omega)

def tmTransferWork0ViaWork1ToIO_pass2 :
    ∀ (ws s : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmTransferWork0ViaWork1ToIO.step
        ⟨some .popWork, r, threeTapeWorkStk s [] ws⟩
        (some ⟨none, default, threeTapeWorkStk (ws.reverse ++ s) [] []⟩)
        (2 * ws.length + 1)
  | [], s, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmTransferWork0ViaWork1ToIO, transferWork0ViaWork1ToIOStmt, mkBitFinTM2,
      Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux, threeTapeWorkStk_kWork1,
      update_threeTapeWorkStk_kWork1, uniformReg_default_carry, List.head?_nil, List.tail_nil,
      List.reverse_nil, List.nil_append, cond_false]
  | b :: ws, s, r => by
    have h1 : tmTransferWork0ViaWork1ToIO.step
        ⟨some .popWork, r, threeTapeWorkStk s [] (b :: ws)⟩ =
        some ⟨some .pushIO, { bitA := b, bitB := false, carry := true },
          threeTapeWorkStk s [] ws⟩ := by
      simp [tmTransferWork0ViaWork1ToIO, transferWork0ViaWork1ToIOStmt, mkBitFinTM2,
        Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have h2 : tmTransferWork0ViaWork1ToIO.step
        ⟨some .pushIO, { bitA := b, bitB := false, carry := true },
          threeTapeWorkStk s [] ws⟩ =
        some ⟨some .popWork, { bitA := b, bitB := false, carry := true },
          threeTapeWorkStk (b :: s) [] ws⟩ := by
      simp [tmTransferWork0ViaWork1ToIO, transferWork0ViaWork1ToIOStmt, mkBitFinTM2,
        Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have ih := tmTransferWork0ViaWork1ToIO_pass2 ws (b :: s)
      { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step h1 (EvalsToInTime.of_step h2 ih))
      (by simp [List.length_cons]; omega)

def tmTransferWork0ViaWork1ToIO_evalsToInTime_concrete (ws s : List Bool) :
    Turing.EvalsToInTime tmTransferWork0ViaWork1ToIO.step
      ⟨some .popIO, default, twoTapeStk s ws⟩
      (some (Turing.haltList tmTransferWork0ViaWork1ToIO (ws ++ s)))
      (4 * ws.length + 2) := by
  have hinit : (⟨some .popIO, default, twoTapeStk s ws⟩ : tmTransferWork0ViaWork1ToIO.Cfg) =
      ⟨some .popIO, default, threeTapeWorkStk s ws []⟩ := by
    rw [threeTapeWorkStk_nil]
  have hhalt : Turing.haltList tmTransferWork0ViaWork1ToIO (ws ++ s) =
      ⟨none, default, threeTapeWorkStk (ws.reverse.reverse ++ s) [] []⟩ := by
    rw [List.reverse_reverse, threeTapeWorkStk_nil, twoTapeStk_nil]; rfl
  rw [hinit, hhalt]
  have hp1 := tmTransferWork0ViaWork1ToIO_pass1 ws [] s default
  rw [List.append_nil] at hp1
  have hp2 := tmTransferWork0ViaWork1ToIO_pass2 ws.reverse s default
  rw [List.length_reverse] at hp2
  exact EvalsToInTime.mono (EvalsToInTime.trans' hp1 hp2) (by omega)

/-- **Composed Simultaneous Butterfly + Difference Packing Stage (`tmComposedButterflyStage`)**:
Composes `tmUniformButterflyAddSub` (`|Λ₁| = 9`, `|σ| = 16`) with the register-lifted
`liftUniformRegTM IdCopyLabel .popIO transferWork0ViaWork1ToIOStmt` (`|Λ₂| = 4`, `|σ| = 16`) via
`seqBitFinTM2` (`|Λ| = 13`, `|σ| = 16`, `|Γ k| = 2`).
Streams two `w`-bit operands `encodeNatBits w A` (`kWork0`) and `encodeNatBits w B` (`kWork1`),
simultaneously computes their butterfly sum `A + B` and difference `A - B`, and packs both results
onto `kIO` as `encodeNatBits w (A - B) ++ encodeNatBits (w + 1) (A + B)` in `12 * w + 8` single-bit
`FinTM2` steps (including all inter-stage head transit and reversal steps). -/
def tmComposedButterflyStage : Turing.FinTM2 :=
  seqBitFinTM2
    ButterflyAddSubLabel .popA
    IdCopyLabel .popIO
    ButterflyReg default default
    butterflyAddSubStmt
    (fun l => liftUniformRegStmt (transferWork0ViaWork1ToIOStmt l))

theorem isUniformFinTM2_tmComposedButterflyStage :
    IsUniformFinTM2 tmComposedButterflyStage 13 16 2 :=
  isUniformFinTM2_mkBitFinTM2 (Sum.inl ButterflyAddSubLabel.popA) default
    tmComposedButterflyStage.m (by decide) (by decide) (by decide)

/-- Constructive evaluation of `tmComposedButterflyStage` on `w`-bit operands `B ≤ A < 2 ^ w` in
`12 * w + 8` single-bit `FinTM2` steps. -/
def tmComposedButterflyStage_encodeNatBits_evalsToInTime_concrete (w A B : ℕ)
    (hBA : B ≤ A) (hA : A < 2 ^ w) :
    Turing.EvalsToInTime tmComposedButterflyStage.step
      ⟨some (Sum.inl ButterflyAddSubLabel.popA), default,
        threeTapeWorkStk [] (encodeNatBits w A) (encodeNatBits w B)⟩
      (some (Turing.haltList tmComposedButterflyStage
        (encodeNatBits w (A - B) ++ encodeNatBits (w + 1) (A + B))))
      (12 * w + 8) := by
  have hp1 := tmUniformButterflyAddSub_encodeNatBits_evalsToInTime_concrete w A B hBA hA
  have hp2_unif := tmTransferWork0ViaWork1ToIO_evalsToInTime_concrete
    (encodeNatBits w (A - B)) (encodeNatBits (w + 1) (A + B))
  rw [encodeNatBits_length] at hp2_unif
  have hp2 := liftUniformRegTM_evalsToInTime_default_concrete IdCopyLabel.popIO
    transferWork0ViaWork1ToIOStmt hp2_unif
  have hseq := seqBitFinTM2_evalsToInTime_concrete
    ButterflyAddSubLabel.popA IdCopyLabel.popIO default default
    butterflyAddSubStmt (fun l => liftUniformRegStmt (transferWork0ViaWork1ToIOStmt l))
    hp1 hp2
  exact EvalsToInTime.mono hseq (by omega)

theorem tmComposedButterflyStage_encodeNatBits_evalsToInTime (w A B : ℕ)
    (hBA : B ≤ A) (hA : A < 2 ^ w) :
    ∃ t ≤ 12 * w + 8,
      Turing.EvalsToInTime tmComposedButterflyStage.step
        ⟨some (Sum.inl .popA), default,
          threeTapeWorkStk [] (encodeNatBits w A) (encodeNatBits w B)⟩
        (some (Turing.haltList tmComposedButterflyStage
          (encodeNatBits w (A - B) ++ encodeNatBits (w + 1) (A + B)))) t :=
  ⟨_, le_rfl, ⟨tmComposedButterflyStage_encodeNatBits_evalsToInTime_concrete w A B hBA hA⟩⟩

/-! ### 6.4 Composed Restoring Conditional-Subtract & Remainder-Return Pass (`tmReturnRemIOViaWork2ToWork0`, `tmComposedCondSubPass`) -/

/-- Transition function for a 2-pass order-preserving remainder return from `kIO` (via `kWork2`)
back onto `kWork0`, while preserving the emitted quotient/root bit on `kWork0` (`|Λ| = 4`, `|σ| = 8`). -/
def returnRemIOViaWork2ToWork0Stmt :
    IdCopyLabel → Turing.TM2.Stmt BitTapeAlphabet IdCopyLabel UniformReg
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
    Turing.TM2.Stmt.push kWork2 (fun r => r.bitA)
      (Turing.TM2.Stmt.goto (fun _ => .popIO))
  | .popWork =>
    Turing.TM2.Stmt.pop kWork2
      (fun _ bOpt =>
        match bOpt with
        | some b => { bitA := b, bitB := false, carry := true }
        | none => default)
      (Turing.TM2.Stmt.branch (fun r => r.carry)
        (Turing.TM2.Stmt.goto (fun _ => .pushIO))
        Turing.TM2.Stmt.halt)
  | .pushIO =>
    Turing.TM2.Stmt.push kWork0 (fun r => r.bitA)
      (Turing.TM2.Stmt.goto (fun _ => .popWork))

def tmReturnRemIOViaWork2ToWork0 : Turing.FinTM2 :=
  mkBitFinTM2 IdCopyLabel .popIO UniformReg default returnRemIOViaWork2ToWork0Stmt

def tmReturnRemIOViaWork2ToWork0_pass1 :
    ∀ (xs qbits acc : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmReturnRemIOViaWork2ToWork0.step
        ⟨some .popIO, r, fourTapeWorkStk xs qbits [] acc⟩
        (some ⟨some .popWork, default, fourTapeWorkStk [] qbits [] (xs.reverse ++ acc)⟩)
        (2 * xs.length + 1)
  | [], qbits, acc, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmReturnRemIOViaWork2ToWork0, returnRemIOViaWork2ToWork0Stmt, mkBitFinTM2,
      Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux, fourTapeWorkStk_kIO,
      update_fourTapeWorkStk_kIO, uniformReg_default_carry, List.head?_nil, List.tail_nil,
      List.reverse_nil, List.nil_append, cond_false]
  | b :: xs, qbits, acc, r => by
    have h1 : tmReturnRemIOViaWork2ToWork0.step
        ⟨some .popIO, r, fourTapeWorkStk (b :: xs) qbits [] acc⟩ =
        some ⟨some .pushWork, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk xs qbits [] acc⟩ := by
      simp [tmReturnRemIOViaWork2ToWork0, returnRemIOViaWork2ToWork0Stmt, mkBitFinTM2,
        Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have h2 : tmReturnRemIOViaWork2ToWork0.step
        ⟨some .pushWork, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk xs qbits [] acc⟩ =
        some ⟨some .popIO, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk xs qbits [] (b :: acc)⟩ := by
      simp [tmReturnRemIOViaWork2ToWork0, returnRemIOViaWork2ToWork0Stmt, mkBitFinTM2,
        Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have ih := tmReturnRemIOViaWork2ToWork0_pass1 xs qbits (b :: acc)
      { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step h1 (EvalsToInTime.of_step h2 ih))
      (by simp [List.length_cons]; omega)

def tmReturnRemIOViaWork2ToWork0_pass2 :
    ∀ (ws qbits : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmReturnRemIOViaWork2ToWork0.step
        ⟨some .popWork, r, fourTapeWorkStk [] qbits [] ws⟩
        (some ⟨none, default, fourTapeWorkStk [] (ws.reverse ++ qbits) [] []⟩)
        (2 * ws.length + 1)
  | [], qbits, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmReturnRemIOViaWork2ToWork0, returnRemIOViaWork2ToWork0Stmt, mkBitFinTM2,
      Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux, fourTapeWorkStk_kWork2,
      update_fourTapeWorkStk_kWork2, uniformReg_default_carry, List.head?_nil, List.tail_nil,
      List.reverse_nil, List.nil_append, cond_false]
  | b :: ws, qbits, r => by
    have h1 : tmReturnRemIOViaWork2ToWork0.step
        ⟨some .popWork, r, fourTapeWorkStk [] qbits [] (b :: ws)⟩ =
        some ⟨some .pushIO, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk [] qbits [] ws⟩ := by
      simp [tmReturnRemIOViaWork2ToWork0, returnRemIOViaWork2ToWork0Stmt, mkBitFinTM2,
        Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have h2 : tmReturnRemIOViaWork2ToWork0.step
        ⟨some .pushIO, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk [] qbits [] ws⟩ =
        some ⟨some .popWork, { bitA := b, bitB := false, carry := true },
          fourTapeWorkStk [] (b :: qbits) [] ws⟩ := by
      simp [tmReturnRemIOViaWork2ToWork0, returnRemIOViaWork2ToWork0Stmt, mkBitFinTM2,
        Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have ih := tmReturnRemIOViaWork2ToWork0_pass2 ws (b :: qbits)
      { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step h1 (EvalsToInTime.of_step h2 ih))
      (by simp [List.length_cons]; omega)

def tmReturnRemIOViaWork2ToWork0_evalsToInTime_concrete (xs qbits : List Bool) :
    Turing.EvalsToInTime tmReturnRemIOViaWork2ToWork0.step
      ⟨some .popIO, default, twoTapeStk xs qbits⟩
      (some ⟨none, default, twoTapeStk [] (xs ++ qbits)⟩)
      (4 * xs.length + 2) := by
  have hinit : (⟨some .popIO, default, twoTapeStk xs qbits⟩ : tmReturnRemIOViaWork2ToWork0.Cfg) =
      ⟨some .popIO, default, fourTapeWorkStk xs qbits [] []⟩ := by
    rw [fourTapeWorkStk_nil, threeTapeWorkStk_nil]
  have hhalt : (⟨none, default, twoTapeStk [] (xs ++ qbits)⟩ : tmReturnRemIOViaWork2ToWork0.Cfg) =
      ⟨none, default, fourTapeWorkStk [] (xs.reverse.reverse ++ qbits) [] []⟩ := by
    rw [List.reverse_reverse, fourTapeWorkStk_nil, threeTapeWorkStk_nil]
  rw [hinit, hhalt]
  have hp1 := tmReturnRemIOViaWork2ToWork0_pass1 xs qbits [] default
  rw [List.append_nil] at hp1
  have hp2 := tmReturnRemIOViaWork2ToWork0_pass2 xs.reverse qbits default
  rw [List.length_reverse] at hp2
  exact EvalsToInTime.mono (EvalsToInTime.trans' hp1 hp2) (by omega)

/-- **Composed Restoring Conditional-Subtract + Remainder-Return Pass (`tmComposedCondSubPass`)**:
Composes `tmUniformCondSubStep` (`|Λ₁| = 8`, `|σ| = 16`) with the register-lifted
`returnRemIOViaWork2ToWork0Stmt` (`|Λ₂| = 4`, `|σ| = 16`) via `seqBitFinTM2` (`|Λ| = 12`,
`|σ| = 16`, `|Γ k| = 2`).
Streams `w`-bit `R` (`kWork0`) and `D` (`kWork1`), conditionally subtracts `D` if `D ≤ R`, and
returns the updated `w`-bit remainder `encodeNatBits w (if D ≤ R then R - D else R)` followed by
the quotient/root bit `[decide (D ≤ R)]` onto `kWork0` in `11 * w + 5` single-bit `FinTM2` steps
(accounting for both conditional subtract-mux passes and head-reversal return to `kWork0`). -/
def tmComposedCondSubPass : Turing.FinTM2 :=
  seqBitFinTM2
    CondSubStepLabel .popA
    IdCopyLabel .popIO
    ButterflyReg default default
    tmUniformCondSubStep.m
    (fun l => liftUniformRegStmt (returnRemIOViaWork2ToWork0Stmt l))

theorem isUniformFinTM2_tmComposedCondSubPass :
    IsUniformFinTM2 tmComposedCondSubPass 12 16 2 :=
  isUniformFinTM2_mkBitFinTM2 (Sum.inl CondSubStepLabel.popA) default
    tmComposedCondSubPass.m (by decide) (by decide) (by decide)

/-- Constructive evaluation of `tmComposedCondSubPass` on `w`-bit operands `R, D < 2 ^ w` in
`11 * w + 5` single-bit `FinTM2` steps. -/
def tmComposedCondSubPass_encodeNatBits_evalsToInTime_concrete (w R D : ℕ)
    (hR : R < 2 ^ w) (hD : D < 2 ^ w) :
    Turing.EvalsToInTime tmComposedCondSubPass.step
      ⟨some (Sum.inl CondSubStepLabel.popA), default,
        threeTapeWorkStk [] (encodeNatBits w R) (encodeNatBits w D)⟩
      (some ⟨none, default,
        twoTapeStk [] (encodeNatBits w (if D ≤ R then R - D else R) ++ [decide (D ≤ R)])⟩)
      (11 * w + 5) := by
  have hp1 := tmUniformCondSubStep_encodeNatBits_evalsToInTime_concrete w R D hR hD
  have hp2_unif := tmReturnRemIOViaWork2ToWork0_evalsToInTime_concrete
    (encodeNatBits w (if D ≤ R then R - D else R)) [decide (D ≤ R)]
  rw [encodeNatBits_length] at hp2_unif
  have hp2 := liftUniformRegTM_evalsToInTime_default_concrete IdCopyLabel.popIO
    returnRemIOViaWork2ToWork0Stmt hp2_unif
  have hseq := seqBitFinTM2_evalsToInTime_concrete
    CondSubStepLabel.popA IdCopyLabel.popIO default default
    tmUniformCondSubStep.m (fun l => liftUniformRegStmt (returnRemIOViaWork2ToWork0Stmt l))
    hp1 hp2
  exact EvalsToInTime.mono hseq (by omega)

theorem tmComposedCondSubPass_encodeNatBits_evalsToInTime (w R D : ℕ)
    (hR : R < 2 ^ w) (hD : D < 2 ^ w) :
    ∃ t ≤ 11 * w + 5,
      Turing.EvalsToInTime tmComposedCondSubPass.step
        ⟨some (Sum.inl .popA), default,
          threeTapeWorkStk [] (encodeNatBits w R) (encodeNatBits w D)⟩
        (some ⟨none, default,
          twoTapeStk [] (encodeNatBits w (if D ≤ R then R - D else R) ++ [decide (D ≤ R)])⟩) t :=
  ⟨_, le_rfl, ⟨tmComposedCondSubPass_encodeNatBits_evalsToInTime_concrete w R D hR hD⟩⟩

/-! ### 6.5 Signed Offset-Binary Arithmetic for Arbitrary `x, y : ℤ` (`encodeSignedWord`) -/

/-- For any `x : ℤ` satisfying `FitsSignedWord w x`, the offset-binary representative
`(x + 2^w).toNat` is strictly bounded by `2 ^ (w + 1)` and satisfies
`((x + 2^w).toNat : ℤ) = x + 2^w`. -/
theorem toNat_add_two_pow_lt_and_eq {w : ℕ} {x : ℤ} (hx : FitsSignedWord w x) :
    (x + (2 : ℤ) ^ w).toNat < 2 ^ (w + 1) ∧
    ((x + (2 : ℤ) ^ w).toNat : ℤ) = x + (2 : ℤ) ^ w := by
  have h1 : -((2 : ℤ) ^ w) < x := hx.neg_pow_lt
  have h2 : x < (2 : ℤ) ^ w := hx.lt_pow
  have hnn : 0 ≤ x + (2 : ℤ) ^ w := by omega
  have hlt : x + (2 : ℤ) ^ w < (2 : ℤ) ^ (w + 1) := by
    rw [pow_succ]; omega
  refine ⟨?_, Int.toNat_of_nonneg hnn⟩
  zify
  rw [Int.toNat_of_nonneg hnn]
  exact hlt

/-- Exact offset-binary sum identity for arbitrary signed integers `x, y : ℤ` satisfying
`FitsSignedWord w x` and `FitsSignedWord w y` (regardless of sign):
`encodeNatBits (w + 2) ((x + 2^w).toNat + (y + 2^w).toNat) = encodeSignedWord (w + 1) (x + y)`. -/
theorem encodeNatBits_add_toNat_eq_encodeSignedWord (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    encodeNatBits (w + 2) ((x + (2 : ℤ) ^ w).toNat + (y + (2 : ℤ) ^ w).toNat) =
      encodeSignedWord (w + 1) (x + y) := by
  have hx' := (toNat_add_two_pow_lt_and_eq hx).2
  have hy' := (toNat_add_two_pow_lt_and_eq hy).2
  have hsum_nn : 0 ≤ (x + y) + (2 : ℤ) ^ (w + 1) := by
    have h1 := hx.neg_pow_lt
    have h2 := hy.neg_pow_lt
    have hpow : (2 : ℤ) ^ (w + 1) = (2 : ℤ) ^ w + (2 : ℤ) ^ w := by rw [pow_succ]; ring
    linarith
  have heq : (x + (2 : ℤ) ^ w).toNat + (y + (2 : ℤ) ^ w).toNat =
      ((x + y) + (2 : ℤ) ^ (w + 1)).toNat := by
    zify
    rw [hx', hy', Int.toNat_of_nonneg hsum_nn, pow_succ]
    ring
  unfold encodeSignedWord
  rw [heq]

/-- **Signed Offset-Binary Addition on `tmUniformRippleAdd` for Arbitrary `x, y : ℤ`
(`tmUniformRippleAdd_encodeSignedWord_evalsToInTime_concrete`)**:
For **any** signed integers `x, y : ℤ` of arbitrary sign satisfying `FitsSignedWord w x` and
`FitsSignedWord w y`, `tmUniformRippleAdd` (`|Λ| = 6`, `|σ| = 8`) streams `encodeSignedWord w x`
(`kWork0`) and `encodeSignedWord w y` (`kWork1`) and outputs `encodeSignedWord (w + 1) (x + y)`
on `kIO` in `5 * w + 10` single-bit `FinTM2` steps. -/
def tmUniformRippleAdd_encodeSignedWord_evalsToInTime_concrete (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    Turing.EvalsToInTime tmUniformRippleAdd.step
      ⟨some .popA, default,
        threeTapeWorkStk [] (encodeSignedWord w x) (encodeSignedWord w y)⟩
      (some (Turing.haltList tmUniformRippleAdd (encodeSignedWord (w + 1) (x + y))))
      (5 * w + 10) := by
  have hx_lt := (toNat_add_two_pow_lt_and_eq hx).1
  have hy_lt := (toNat_add_two_pow_lt_and_eq hy).1
  have hrun := tmUniformRippleAdd_encodeNatBits_evalsToInTime_concrete (w + 1)
    (x + (2 : ℤ) ^ w).toNat (y + (2 : ℤ) ^ w).toNat hx_lt hy_lt
  rw [encodeNatBits_add_toNat_eq_encodeSignedWord w x y hx hy] at hrun
  exact EvalsToInTime.mono hrun (by omega)

theorem tmUniformRippleAdd_encodeSignedWord_evalsToInTime (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    ∃ t ≤ 5 * w + 10,
      Turing.EvalsToInTime tmUniformRippleAdd.step
        ⟨some .popA, default,
          threeTapeWorkStk [] (encodeSignedWord w x) (encodeSignedWord w y)⟩
        (some (Turing.haltList tmUniformRippleAdd (encodeSignedWord (w + 1) (x + y)))) t :=
  ⟨_, le_rfl, ⟨tmUniformRippleAdd_encodeSignedWord_evalsToInTime_concrete w x y hx hy⟩⟩

/-- Bitwise complement identity for LSB-first bit lists:
`decodeNatBits bs + decodeNatBits (bs.map (!·)) + 1 = 2 ^ bs.length`. -/
theorem decodeNatBits_add_decodeNatBits_map_not :
    ∀ (bs : List Bool),
      decodeNatBits bs + decodeNatBits (bs.map (!·)) + 1 = 2 ^ bs.length
  | [] => rfl
  | b :: bs => by
    have ih := decodeNatBits_add_decodeNatBits_map_not bs
    have hb : (bif b then 1 else 0) + (bif (!b) then 1 else 0) = 1 := by
      cases b <;> rfl
    simp only [List.map_cons, decodeNatBits, List.length_cons, Nat.pow_succ]
    omega

/-- Exact offset-binary difference identity for **arbitrary** signed integers `x, y : ℤ`
(even when `x < y` or `x, y < 0`) satisfying `FitsSignedWord w x` and `FitsSignedWord w y`:
running `rippleAddStream` with `ys` bitwise-negated (`(encodeSignedWord w y).map (!·)`) and initial
carry-in `true` (`1`) produces `encodeSignedWord (w + 1) (x - y)` bit-exactly. -/
@[simp]
theorem rippleAddStream_not_encodeSignedWord (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    rippleAddStream (encodeSignedWord w x) ((encodeSignedWord w y).map (!·)) true =
      encodeSignedWord (w + 1) (x - y) := by
  set xs := encodeSignedWord w x
  set ys := encodeSignedWord w y
  have hlen : xs.length = (ys.map (!·)).length := by
    simp [xs, ys]
  have hout_len : (rippleAddStream xs (ys.map (!·)) true).length = w + 2 := by
    rw [length_rippleAddStream _ _ hlen true]
    simp [xs]
  have hx_lt := (toNat_add_two_pow_lt_and_eq hx).1
  have hx_eq := (toNat_add_two_pow_lt_and_eq hx).2
  have hy_lt := (toNat_add_two_pow_lt_and_eq hy).1
  have hy_eq := (toNat_add_two_pow_lt_and_eq hy).2
  have hdec_xs : decodeNatBits xs = (x + (2 : ℤ) ^ w).toNat :=
    decodeNatBits_encodeNatBits (w + 1) _ hx_lt
  have hdec_ys : decodeNatBits ys = (y + (2 : ℤ) ^ w).toNat :=
    decodeNatBits_encodeNatBits (w + 1) _ hy_lt
  have hnot_ys := decodeNatBits_add_decodeNatBits_map_not ys
  have hys_len : ys.length = w + 1 := by simp [ys]
  rw [hys_len, hdec_ys] at hnot_ys
  have hdiff_nn : 0 ≤ (x - y) + (2 : ℤ) ^ (w + 1) := by
    have h1 := hx.neg_pow_lt
    have h2 := hy.lt_pow
    have hpow : (2 : ℤ) ^ (w + 1) = (2 : ℤ) ^ w + (2 : ℤ) ^ w := by rw [pow_succ]; ring
    linarith
  have hdec_stream :
      decodeNatBits (rippleAddStream xs (ys.map (!·)) true) =
        ((x - y) + (2 : ℤ) ^ (w + 1)).toNat := by
    rw [decodeNatBits_rippleAddStream xs (ys.map (!·)) hlen true, hdec_xs]
    change (x + (2 : ℤ) ^ w).toNat + decodeNatBits (ys.map (!·)) + 1 =
      ((x - y) + (2 : ℤ) ^ (w + 1)).toNat
    zify at hnot_ys ⊢
    rw [hy_eq] at hnot_ys
    rw [hx_eq]
    rw [Int.toNat_of_nonneg hdiff_nn]
    have hpow : (2 : ℤ) ^ (w + 1) = (2 : ℤ) ^ w + (2 : ℤ) ^ w := by rw [pow_succ]; ring
    linarith
  calc
    rippleAddStream xs (ys.map (!·)) true
      = encodeNatBits (rippleAddStream xs (ys.map (!·)) true).length
          (decodeNatBits (rippleAddStream xs (ys.map (!·)) true)) :=
        (encodeNatBits_decodeNatBits _).symm
    _ = encodeSignedWord (w + 1) (x - y) := by
        rw [hout_len, hdec_stream]
        rfl

/-- Control labels for the uniform simultaneous signed offset-binary butterfly `FinTM2` (`|Λ| = 10`). -/
inductive SignedButterflyLabel : Type
  | initBorrow
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

def signedButterflyLabelEquiv : SignedButterflyLabel ≃ Fin 10 where
  toFun
    | .initBorrow => ⟨0, by decide⟩
    | .popA => ⟨1, by decide⟩
    | .popB => ⟨2, by decide⟩
    | .pushSumRev => ⟨3, by decide⟩
    | .pushDiffRev => ⟨4, by decide⟩
    | .pushCarryRev => ⟨5, by decide⟩
    | .popSumRev => ⟨6, by decide⟩
    | .pushSumIO => ⟨7, by decide⟩
    | .popDiffRev => ⟨8, by decide⟩
    | .pushDiffWork0 => ⟨9, by decide⟩
  invFun
    | ⟨0, _⟩ => .initBorrow
    | ⟨1, _⟩ => .popA
    | ⟨2, _⟩ => .popB
    | ⟨3, _⟩ => .pushSumRev
    | ⟨4, _⟩ => .pushDiffRev
    | ⟨5, _⟩ => .pushCarryRev
    | ⟨6, _⟩ => .popSumRev
    | ⟨7, _⟩ => .pushSumIO
    | ⟨8, _⟩ => .popDiffRev
    | ⟨_ + 9, _⟩ => .pushDiffWork0
  left_inv x := by cases x <;> rfl
  right_inv i := by
    rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try rfl
    omega

instance : Fintype SignedButterflyLabel :=
  Fintype.ofEquiv (Fin 10) signedButterflyLabelEquiv.symm

@[simp]
theorem card_signedButterflyLabel : Fintype.card SignedButterflyLabel = 10 := by decide

/-- **Single Uniform Signed Offset-Binary Simultaneous Butterfly Machine
(`tmUniformSignedButterflyAddSub`)**:
A single uniform 8-stack binary machine (`Turing.FinTM2`, `|Λ| = 10`, `|σ| = 16`, `|Γ k| = 2`, zero length parameters)
that pops `encodeSignedWord w x` (`kWork0`) and `encodeSignedWord w y` (`kWork1`) for **arbitrary
signed integers `x, y : ℤ` of any sign** (`FitsSignedWord w x`, `FitsSignedWord w y`, **no `y ≤ x`
assumption**), simultaneously computes both the signed sum `encodeSignedWord (w + 1) (x + y)` (via
`fullAdderSum a b carry` with initial `carry = false`) and the signed difference
`encodeSignedWord (w + 1) (x - y)` (via `fullAdderSum a (!b) borrow` with initial `borrow = true`),
and outputs `encodeSignedWord (w + 1) (x + y)` on `kIO` and `encodeSignedWord (w + 1) (x - y)` on
`kWork0` in `8 * w + 17` `TM2.step` transitions. -/
def tmUniformSignedButterflyAddSub : Turing.FinTM2 :=
  mkBitFinTM2 SignedButterflyLabel .initBorrow ButterflyReg default (fun lbl =>
    match lbl with
    | .initBorrow =>
      Turing.TM2.Stmt.load (fun _ => { bitA := false, bitB := false, carry := false, borrow := true })
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
          let b := bOpt.getD false
          { bitA := fullAdderSum r.bitA b r.carry
            bitB := fullAdderSum r.bitA (!b) r.borrow
            carry := fullAdderCarry r.bitA b r.carry
            borrow := fullAdderCarry r.bitA (!b) r.borrow })
        (Turing.TM2.Stmt.goto (fun _ => .pushSumRev))
    | .pushSumRev =>
      Turing.TM2.Stmt.push kWork2 (fun r => r.bitA)
        (Turing.TM2.Stmt.goto (fun _ => .pushDiffRev))
    | .pushDiffRev =>
      Turing.TM2.Stmt.push kWork3 (fun r => r.bitB)
        (Turing.TM2.Stmt.goto (fun _ => .popA))
    | .pushCarryRev =>
      Turing.TM2.Stmt.push kWork2 (fun r => r.carry)
        (Turing.TM2.Stmt.push kWork3 (fun r => r.borrow)
          (Turing.TM2.Stmt.goto (fun _ => .popSumRev)))
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

theorem isUniformFinTM2_tmUniformSignedButterflyAddSub :
    IsUniformFinTM2 tmUniformSignedButterflyAddSub 10 16 2 :=
  isUniformFinTM2_mkBitFinTM2 SignedButterflyLabel.initBorrow default
    tmUniformSignedButterflyAddSub.m (by decide) (by decide) (by decide)

def tmUniformSignedButterflyAddSub_pass1 :
    ∀ (xs ys accSum accDiff : List Bool) (_hlen : xs.length = ys.length) (r : ButterflyReg),
      Turing.EvalsToInTime tmUniformSignedButterflyAddSub.step
        ⟨some .popA, r, fiveTapeWorkStk [] xs ys accSum accDiff⟩
        (some ⟨some .popSumRev,
          { bitA := false
            bitB := false
            carry := (rippleAddRevLoop xs ys r.carry accSum).headD false
            borrow := (rippleAddRevLoop xs (ys.map (!·)) r.borrow accDiff).headD false },
          fiveTapeWorkStk [] [] []
            (rippleAddRevLoop xs ys r.carry accSum)
            (rippleAddRevLoop xs (ys.map (!·)) r.borrow accDiff)⟩)
        (4 * xs.length + 2)
  | [], [], accSum, accDiff, _, r => by
    rcases r with ⟨bitA, bitB, carry, borrow⟩
    have hstep1 : tmUniformSignedButterflyAddSub.step
        ⟨some .popA, ⟨bitA, bitB, carry, borrow⟩, fiveTapeWorkStk [] [] [] accSum accDiff⟩ =
        some ⟨some .pushCarryRev, ⟨false, false, carry, borrow⟩,
          fiveTapeWorkStk [] [] [] accSum accDiff⟩ := by
      simp [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformSignedButterflyAddSub.step
        ⟨some .pushCarryRev, ⟨false, false, carry, borrow⟩,
          fiveTapeWorkStk [] [] [] accSum accDiff⟩ =
        some ⟨some .popSumRev, ⟨false, false, carry, borrow⟩,
          fiveTapeWorkStk [] [] [] (carry :: accSum) (borrow :: accDiff)⟩ := by
      simp [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    exact EvalsToInTime.of_step hstep1 (EvalsToInTime.step_one hstep2)
  | a :: xs, b :: ys, accSum, accDiff, hlen, r => by
    rcases r with ⟨bitA, bitB, carry, borrow⟩
    have hlen' : xs.length = ys.length := by simpa using hlen
    have hstep1 : tmUniformSignedButterflyAddSub.step
        ⟨some .popA, ⟨bitA, bitB, carry, borrow⟩,
          fiveTapeWorkStk [] (a :: xs) (b :: ys) accSum accDiff⟩ =
        some ⟨some .popB, ⟨a, true, carry, borrow⟩,
          fiveTapeWorkStk [] xs (b :: ys) accSum accDiff⟩ := by
      simp [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep2 : tmUniformSignedButterflyAddSub.step
        ⟨some .popB, ⟨a, true, carry, borrow⟩,
          fiveTapeWorkStk [] xs (b :: ys) accSum accDiff⟩ =
        some ⟨some .pushSumRev,
          ⟨fullAdderSum a b carry, fullAdderSum a (!b) borrow,
            fullAdderCarry a b carry, fullAdderCarry a (!b) borrow⟩,
          fiveTapeWorkStk [] xs ys accSum accDiff⟩ := by
      simp [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep3 : tmUniformSignedButterflyAddSub.step
        ⟨some .pushSumRev,
          ⟨fullAdderSum a b carry, fullAdderSum a (!b) borrow,
            fullAdderCarry a b carry, fullAdderCarry a (!b) borrow⟩,
          fiveTapeWorkStk [] xs ys accSum accDiff⟩ =
        some ⟨some .pushDiffRev,
          ⟨fullAdderSum a b carry, fullAdderSum a (!b) borrow,
            fullAdderCarry a b carry, fullAdderCarry a (!b) borrow⟩,
          fiveTapeWorkStk [] xs ys (fullAdderSum a b carry :: accSum) accDiff⟩ := by
      simp [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have hstep4 : tmUniformSignedButterflyAddSub.step
        ⟨some .pushDiffRev,
          ⟨fullAdderSum a b carry, fullAdderSum a (!b) borrow,
            fullAdderCarry a b carry, fullAdderCarry a (!b) borrow⟩,
          fiveTapeWorkStk [] xs ys (fullAdderSum a b carry :: accSum) accDiff⟩ =
        some ⟨some .popA,
          ⟨fullAdderSum a b carry, fullAdderSum a (!b) borrow,
            fullAdderCarry a b carry, fullAdderCarry a (!b) borrow⟩,
          fiveTapeWorkStk [] xs ys
            (fullAdderSum a b carry :: accSum)
            (fullAdderSum a (!b) borrow :: accDiff)⟩ := by
      simp [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformSignedButterflyAddSub_pass1 xs ys
      (fullAdderSum a b carry :: accSum) (fullAdderSum a (!b) borrow :: accDiff) hlen'
      ⟨fullAdderSum a b carry, fullAdderSum a (!b) borrow,
        fullAdderCarry a b carry, fullAdderCarry a (!b) borrow⟩
    dsimp only [List.map, rippleAddRevLoop]
    exact EvalsToInTime.mono
      (EvalsToInTime.of_step hstep1
        (EvalsToInTime.of_step hstep2
          (EvalsToInTime.of_step hstep3
            (EvalsToInTime.of_step hstep4 ih))))
      (by simp [List.length_cons]; omega)

def tmUniformSignedButterflyAddSub_pass2 :
    ∀ (wsSum accSum wsDiff : List Bool) (r : ButterflyReg),
      Turing.EvalsToInTime tmUniformSignedButterflyAddSub.step
        ⟨some .popSumRev, r, fiveTapeWorkStk accSum [] [] wsSum wsDiff⟩
        (some ⟨some .popDiffRev, default,
          fiveTapeWorkStk (wsSum.reverse ++ accSum) [] [] [] wsDiff⟩)
        (2 * wsSum.length + 1)
  | [], accSum, wsDiff, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux, fiveTapeWorkStk_kWork2, update_fiveTapeWorkStk_kWork2,
      butterflyReg_default_carry, List.head?_nil, List.tail_nil, List.reverse_nil,
      List.nil_append, cond_false]
  | b :: wsSum, accSum, wsDiff, r => by
    have h1 : tmUniformSignedButterflyAddSub.step
        ⟨some .popSumRev, r, fiveTapeWorkStk accSum [] [] (b :: wsSum) wsDiff⟩ =
        some ⟨some .pushSumIO, { bitA := b, bitB := false, carry := true, borrow := false },
          fiveTapeWorkStk accSum [] [] wsSum wsDiff⟩ := by
      simp [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have h2 : tmUniformSignedButterflyAddSub.step
        ⟨some .pushSumIO, { bitA := b, bitB := false, carry := true, borrow := false },
          fiveTapeWorkStk accSum [] [] wsSum wsDiff⟩ =
        some ⟨some .popSumRev, { bitA := b, bitB := false, carry := true, borrow := false },
          fiveTapeWorkStk (b :: accSum) [] [] wsSum wsDiff⟩ := by
      simp [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformSignedButterflyAddSub_pass2 wsSum (b :: accSum) wsDiff
      { bitA := b, bitB := false, carry := true, borrow := false }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step h1 (EvalsToInTime.of_step h2 ih))
      (by simp [List.length_cons]; omega)

def tmUniformSignedButterflyAddSub_pass3 :
    ∀ (wsDiff sumOut accDiff : List Bool) (r : ButterflyReg),
      Turing.EvalsToInTime tmUniformSignedButterflyAddSub.step
        ⟨some .popDiffRev, r, fiveTapeWorkStk sumOut accDiff [] [] wsDiff⟩
        (some ⟨none, default,
          fiveTapeWorkStk sumOut (wsDiff.reverse ++ accDiff) [] [] []⟩)
        (2 * wsDiff.length + 1)
  | [], sumOut, accDiff, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux, fiveTapeWorkStk_kWork3, update_fiveTapeWorkStk_kWork3,
      butterflyReg_default_carry, List.head?_nil, List.tail_nil, List.reverse_nil,
      List.nil_append, cond_false]
  | b :: wsDiff, sumOut, accDiff, r => by
    have h1 : tmUniformSignedButterflyAddSub.step
        ⟨some .popDiffRev, r, fiveTapeWorkStk sumOut accDiff [] [] (b :: wsDiff)⟩ =
        some ⟨some .pushDiffWork0, { bitA := b, bitB := false, carry := true, borrow := false },
          fiveTapeWorkStk sumOut accDiff [] [] wsDiff⟩ := by
      simp [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have h2 : tmUniformSignedButterflyAddSub.step
        ⟨some .pushDiffWork0, { bitA := b, bitB := false, carry := true, borrow := false },
          fiveTapeWorkStk sumOut accDiff [] [] wsDiff⟩ =
        some ⟨some .popDiffRev, { bitA := b, bitB := false, carry := true, borrow := false },
          fiveTapeWorkStk sumOut (b :: accDiff) [] [] wsDiff⟩ := by
      simp [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
        Turing.TM2.stepAux]
    have ih := tmUniformSignedButterflyAddSub_pass3 wsDiff sumOut (b :: accDiff)
      { bitA := b, bitB := false, carry := true, borrow := false }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step h1 (EvalsToInTime.of_step h2 ih))
      (by simp [List.length_cons]; omega)

/-- **Constructive Evaluation of `tmUniformSignedButterflyAddSub` on Arbitrary Signed Integers
`x, y : ℤ` (`tmUniformSignedButterflyAddSub_encodeSignedWord_evalsToInTime_concrete`)**:
For **all** `x, y : ℤ` satisfying `FitsSignedWord w x` and `FitsSignedWord w y` (with **no**
sign or ordering restriction `y ≤ x`), `tmUniformSignedButterflyAddSub` simultaneously outputs
`encodeSignedWord (w + 1) (x + y)` on `kIO` and `encodeSignedWord (w + 1) (x - y)` on `kWork0`
in `8 * w + 17` single-bit `FinTM2` steps. -/
def tmUniformSignedButterflyAddSub_encodeSignedWord_evalsToInTime_concrete (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    Turing.EvalsToInTime tmUniformSignedButterflyAddSub.step
      ⟨some .initBorrow, default,
        threeTapeWorkStk [] (encodeSignedWord w x) (encodeSignedWord w y)⟩
      (some ⟨none, default,
        twoTapeStk (encodeSignedWord (w + 1) (x + y)) (encodeSignedWord (w + 1) (x - y))⟩)
      (8 * w + 17) := by
  set xs := encodeSignedWord w x
  set ys := encodeSignedWord w y
  have hlen : xs.length = ys.length := by simp [xs, ys]
  have hlen_not : xs.length = (ys.map (!·)).length := by simp [xs, ys]
  have hinit : (⟨some .initBorrow, default, threeTapeWorkStk [] xs ys⟩ :
      tmUniformSignedButterflyAddSub.Cfg) =
      ⟨some .initBorrow, default, fiveTapeWorkStk [] xs ys [] []⟩ := by
    rw [fiveTapeWorkStk_nil, fourTapeWorkStk_nil]
  have hstep0 : tmUniformSignedButterflyAddSub.step
      ⟨some .initBorrow, default, fiveTapeWorkStk [] xs ys [] []⟩ =
      some ⟨some .popA, { bitA := false, bitB := false, carry := false, borrow := true },
        fiveTapeWorkStk [] xs ys [] []⟩ := by
    simp [tmUniformSignedButterflyAddSub, mkBitFinTM2, Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux]
  have hp1 := tmUniformSignedButterflyAddSub_pass1 xs ys [] [] hlen
    { bitA := false, bitB := false, carry := false, borrow := true }
  have hp2 := tmUniformSignedButterflyAddSub_pass2
    (rippleAddRevLoop xs ys false []) []
    (rippleAddRevLoop xs (ys.map (!·)) true [])
    { bitA := false
      bitB := false
      carry := (rippleAddRevLoop xs ys false []).headD false
      borrow := (rippleAddRevLoop xs (ys.map (!·)) true []).headD false }
  have hp3 := tmUniformSignedButterflyAddSub_pass3
    (rippleAddRevLoop xs (ys.map (!·)) true [])
    ((rippleAddRevLoop xs ys false []).reverse ++ []) [] default
  have hlen_xs : xs.length = w + 1 := by simp [xs]
  have hlen_add : (rippleAddRevLoop xs ys false []).length = w + 2 := by
    simpa [xs] using length_rippleAddRevLoop xs ys hlen false []
  have hlen_sub : (rippleAddRevLoop xs (ys.map (!·)) true []).length = w + 2 := by
    simpa [xs] using length_rippleAddRevLoop xs (ys.map (!·)) hlen_not true []
  rw [hlen_xs] at hp1
  rw [hlen_add] at hp2
  rw [hlen_sub] at hp3
  have hx_lt := (toNat_add_two_pow_lt_and_eq hx).1
  have hy_lt := (toNat_add_two_pow_lt_and_eq hy).1
  have hrev_add : (rippleAddRevLoop xs ys false []).reverse =
      encodeSignedWord (w + 1) (x + y) := by
    rw [reverse_rippleAddRevLoop xs ys hlen false [], List.reverse_nil, List.nil_append]
    change rippleAddStream (encodeNatBits (w + 1) (x + (2 : ℤ) ^ w).toNat)
      (encodeNatBits (w + 1) (y + (2 : ℤ) ^ w).toNat) false = _
    rw [rippleAddStream_encodeNatBits (w + 1) _ _ hx_lt hy_lt,
      encodeNatBits_add_toNat_eq_encodeSignedWord w x y hx hy]
  have hrev_sub : (rippleAddRevLoop xs (ys.map (!·)) true []).reverse =
      encodeSignedWord (w + 1) (x - y) := by
    rw [reverse_rippleAddRevLoop xs (ys.map (!·)) hlen_not true [],
      List.reverse_nil, List.nil_append,
      rippleAddStream_not_encodeSignedWord w x y hx hy]
  have hhalt : (⟨none, default,
      fiveTapeWorkStk
        ((rippleAddRevLoop xs ys false []).reverse ++ [])
        ((rippleAddRevLoop xs (ys.map (!·)) true []).reverse ++ [])
        [] [] []⟩ : tmUniformSignedButterflyAddSub.Cfg) =
      ⟨none, default,
        twoTapeStk (encodeSignedWord (w + 1) (x + y)) (encodeSignedWord (w + 1) (x - y))⟩ := by
    rw [List.append_nil, List.append_nil, hrev_add, hrev_sub,
      fiveTapeWorkStk_nil, fourTapeWorkStk_nil, threeTapeWorkStk_nil]
  rw [hinit, ← hhalt]
  exact EvalsToInTime.mono
    (EvalsToInTime.of_step hstep0 (EvalsToInTime.trans' (EvalsToInTime.trans' hp1 hp2) hp3))
    (by omega)

theorem tmUniformSignedButterflyAddSub_encodeSignedWord_evalsToInTime (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    ∃ t ≤ 8 * w + 17,
      Turing.EvalsToInTime tmUniformSignedButterflyAddSub.step
        ⟨some .initBorrow, default,
          threeTapeWorkStk [] (encodeSignedWord w x) (encodeSignedWord w y)⟩
        (some ⟨none, default,
          twoTapeStk (encodeSignedWord (w + 1) (x + y)) (encodeSignedWord (w + 1) (x - y))⟩) t :=
  ⟨_, le_rfl, ⟨tmUniformSignedButterflyAddSub_encodeSignedWord_evalsToInTime_concrete w x y hx hy⟩⟩

/-- **Composed Signed Butterfly Stage Packing Both `x - y` and `x + y` onto `kIO`
(`tmComposedSignedButterflyStage`)**:
Composes `tmUniformSignedButterflyAddSub` (`|Λ₁| = 10`, `|σ| = 16`) with the register-lifted
`transferWork0ViaWork1ToIOStmt` (`|Λ₂| = 4`, `|σ| = 16`) via `seqBitFinTM2` (`|Λ| = 14`, `|σ| = 16`).
For **all** signed integers `x, y : ℤ` (`FitsSignedWord w x`, `FitsSignedWord w y`), streams both
operands and outputs `encodeSignedWord (w + 1) (x - y) ++ encodeSignedWord (w + 1) (x + y)` on `kIO`
in `12 * w + 27` single-bit `FinTM2` steps. -/
def tmComposedSignedButterflyStage : Turing.FinTM2 :=
  seqBitFinTM2
    SignedButterflyLabel .initBorrow
    IdCopyLabel .popIO
    ButterflyReg default default
    tmUniformSignedButterflyAddSub.m
    (fun l => liftUniformRegStmt (transferWork0ViaWork1ToIOStmt l))

theorem isUniformFinTM2_tmComposedSignedButterflyStage :
    IsUniformFinTM2 tmComposedSignedButterflyStage 14 16 2 :=
  isUniformFinTM2_mkBitFinTM2 (Sum.inl SignedButterflyLabel.initBorrow) default
    tmComposedSignedButterflyStage.m (by decide) (by decide) (by decide)

def tmComposedSignedButterflyStage_encodeSignedWord_evalsToInTime_concrete (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    Turing.EvalsToInTime tmComposedSignedButterflyStage.step
      ⟨some (Sum.inl SignedButterflyLabel.initBorrow), default,
        threeTapeWorkStk [] (encodeSignedWord w x) (encodeSignedWord w y)⟩
      (some (Turing.haltList tmComposedSignedButterflyStage
        (encodeSignedWord (w + 1) (x - y) ++ encodeSignedWord (w + 1) (x + y))))
      (12 * w + 27) := by
  have hp1 := tmUniformSignedButterflyAddSub_encodeSignedWord_evalsToInTime_concrete w x y hx hy
  have hp2_unif := tmTransferWork0ViaWork1ToIO_evalsToInTime_concrete
    (encodeSignedWord (w + 1) (x - y)) (encodeSignedWord (w + 1) (x + y))
  rw [length_encodeSignedWord] at hp2_unif
  have hp2 := liftUniformRegTM_evalsToInTime_default_concrete IdCopyLabel.popIO
    transferWork0ViaWork1ToIOStmt hp2_unif
  have hseq := seqBitFinTM2_evalsToInTime_concrete
    SignedButterflyLabel.initBorrow IdCopyLabel.popIO default default
    tmUniformSignedButterflyAddSub.m
    (fun l => liftUniformRegStmt (transferWork0ViaWork1ToIOStmt l))
    hp1 hp2
  exact EvalsToInTime.mono hseq (by omega)

theorem tmComposedSignedButterflyStage_encodeSignedWord_evalsToInTime (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    ∃ t ≤ 12 * w + 27,
      Turing.EvalsToInTime tmComposedSignedButterflyStage.step
        ⟨some (Sum.inl .initBorrow), default,
          threeTapeWorkStk [] (encodeSignedWord w x) (encodeSignedWord w y)⟩
        (some (Turing.haltList tmComposedSignedButterflyStage
          (encodeSignedWord (w + 1) (x - y) ++ encodeSignedWord (w + 1) (x + y)))) t :=
  ⟨_, le_rfl, ⟨tmComposedSignedButterflyStage_encodeSignedWord_evalsToInTime_concrete w x y hx hy⟩⟩

/-! ### 6.6 Single-Input-Stack `Turing.initList` Deinterleave-and-Restore Front-End & Signed Arithmetic Machines -/

/-- Deinterleave from `kIO` onto `kWork2` (even bits) and `kWork3` (odd bits) so that two
subsequent reversal passes (`kWork2 → kWork0` and `kWork3 → kWork1`) restore forward LSB-first
order on `kWork0` and `kWork1`. -/
def deinterleaveToWork2Work3Stmt :
    DeinterleaveLabel → Turing.TM2.Stmt BitTapeAlphabet DeinterleaveLabel UniformReg
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
    Turing.TM2.Stmt.push kWork2 (fun r => r.bitA)
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
    Turing.TM2.Stmt.push kWork3 (fun r => r.bitB)
      (Turing.TM2.Stmt.goto (fun _ => .popEven))

def tmDeinterleaveToWork2Work3 : Turing.FinTM2 :=
  mkBitFinTM2 DeinterleaveLabel .popEven UniformReg default deinterleaveToWork2Work3Stmt

def tmDeinterleaveToWork2Work3_loop :
    ∀ (ps : List (Bool × Bool)) (w2 w3 : List Bool) (r : UniformReg),
      Turing.EvalsToInTime tmDeinterleaveToWork2Work3.step
        ⟨some .popEven, r, fiveTapeWorkStk (flattenBitPairs ps) [] [] w2 w3⟩
        (some ⟨none, default,
          fiveTapeWorkStk [] [] [] ((ps.map Prod.fst).reverse ++ w2)
            ((ps.map Prod.snd).reverse ++ w3)⟩)
        (4 * ps.length + 1)
  | [], w2, w3, r => by
    refine EvalsToInTime.step_one ?_
    simp [tmDeinterleaveToWork2Work3, deinterleaveToWork2Work3Stmt, flattenBitPairs, mkBitFinTM2,
      Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
  | (a, b) :: ps, w2, w3, r => by
    have h1 : tmDeinterleaveToWork2Work3.step
        ⟨some .popEven, r, fiveTapeWorkStk (a :: b :: flattenBitPairs ps) [] [] w2 w3⟩ =
        some ⟨some .pushEven, { bitA := a, bitB := false, carry := true },
          fiveTapeWorkStk (b :: flattenBitPairs ps) [] [] w2 w3⟩ := by
      simp [tmDeinterleaveToWork2Work3, deinterleaveToWork2Work3Stmt, mkBitFinTM2,
        Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have h2 : tmDeinterleaveToWork2Work3.step
        ⟨some .pushEven, { bitA := a, bitB := false, carry := true },
          fiveTapeWorkStk (b :: flattenBitPairs ps) [] [] w2 w3⟩ =
        some ⟨some .popOdd, { bitA := a, bitB := false, carry := true },
          fiveTapeWorkStk (b :: flattenBitPairs ps) [] [] (a :: w2) w3⟩ := by
      simp [tmDeinterleaveToWork2Work3, deinterleaveToWork2Work3Stmt, mkBitFinTM2,
        Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have h3 : tmDeinterleaveToWork2Work3.step
        ⟨some .popOdd, { bitA := a, bitB := false, carry := true },
          fiveTapeWorkStk (b :: flattenBitPairs ps) [] [] (a :: w2) w3⟩ =
        some ⟨some .pushOdd, { bitA := false, bitB := b, carry := true },
          fiveTapeWorkStk (flattenBitPairs ps) [] [] (a :: w2) w3⟩ := by
      simp [tmDeinterleaveToWork2Work3, deinterleaveToWork2Work3Stmt, mkBitFinTM2,
        Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have h4 : tmDeinterleaveToWork2Work3.step
        ⟨some .pushOdd, { bitA := false, bitB := b, carry := true },
          fiveTapeWorkStk (flattenBitPairs ps) [] [] (a :: w2) w3⟩ =
        some ⟨some .popEven, { bitA := false, bitB := b, carry := true },
          fiveTapeWorkStk (flattenBitPairs ps) [] [] (a :: w2) (b :: w3)⟩ := by
      simp [tmDeinterleaveToWork2Work3, deinterleaveToWork2Work3Stmt, mkBitFinTM2,
        Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
    have ih := tmDeinterleaveToWork2Work3_loop ps (a :: w2) (b :: w3)
      { bitA := false, bitB := b, carry := true }
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono
      (EvalsToInTime.of_step h1 (EvalsToInTime.of_step h2 (EvalsToInTime.of_step h3
        (EvalsToInTime.of_step h4 ih))))
      (by simp [List.length_cons]; omega)

def tmRevWork2ToWork0_loop :
    ∀ (w2 w0 w3 : List Bool) (r : UniformReg),
      Turing.EvalsToInTime (tmUniformRevCopyBetween kWork2 kWork0).step
        ⟨some .popIO, r, fiveTapeWorkStk [] w0 [] w2 w3⟩
        (some ⟨none, default, fiveTapeWorkStk [] (w2.reverse ++ w0) [] [] w3⟩)
        (2 * w2.length + 1)
  | [], w0, w3, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformRevCopyBetween, revCopyBetweenStmt, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, fiveTapeWorkStk_kWork2, update_fiveTapeWorkStk_kWork2,
      uniformReg_default_carry, List.head?_nil, List.tail_nil, List.reverse_nil, List.nil_append,
      cond_false]
  | b :: w2, w0, w3, r => by
    have h1 : (tmUniformRevCopyBetween kWork2 kWork0).step
        ⟨some .popIO, r, fiveTapeWorkStk [] w0 [] (b :: w2) w3⟩ =
        some ⟨some .pushWork, { bitA := b, bitB := false, carry := true },
          fiveTapeWorkStk [] w0 [] w2 w3⟩ := by
      simp [tmUniformRevCopyBetween, revCopyBetweenStmt, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux]
    have h2 : (tmUniformRevCopyBetween kWork2 kWork0).step
        ⟨some .pushWork, { bitA := b, bitB := false, carry := true },
          fiveTapeWorkStk [] w0 [] w2 w3⟩ =
        some ⟨some .popIO, { bitA := b, bitB := false, carry := true },
          fiveTapeWorkStk [] (b :: w0) [] w2 w3⟩ := by
      simp [tmUniformRevCopyBetween, revCopyBetweenStmt, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux]
    have ih := tmRevWork2ToWork0_loop w2 (b :: w0) w3 { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step h1 (EvalsToInTime.of_step h2 ih))
      (by simp [List.length_cons]; omega)

def tmRevWork3ToWork1_loop :
    ∀ (w3 w0 w1 : List Bool) (r : UniformReg),
      Turing.EvalsToInTime (tmUniformRevCopyBetween kWork3 kWork1).step
        ⟨some .popIO, r, fiveTapeWorkStk [] w0 w1 [] w3⟩
        (some ⟨none, default, fiveTapeWorkStk [] w0 (w3.reverse ++ w1) [] []⟩)
        (2 * w3.length + 1)
  | [], w0, w1, r => by
    refine EvalsToInTime.step_one ?_
    simp only [tmUniformRevCopyBetween, revCopyBetweenStmt, mkBitFinTM2, Turing.FinTM2.step,
      Turing.TM2.step, Turing.TM2.stepAux, fiveTapeWorkStk_kWork3, update_fiveTapeWorkStk_kWork3,
      uniformReg_default_carry, List.head?_nil, List.tail_nil, List.reverse_nil, List.nil_append,
      cond_false]
  | b :: w3, w0, w1, r => by
    have h1 : (tmUniformRevCopyBetween kWork3 kWork1).step
        ⟨some .popIO, r, fiveTapeWorkStk [] w0 w1 [] (b :: w3)⟩ =
        some ⟨some .pushWork, { bitA := b, bitB := false, carry := true },
          fiveTapeWorkStk [] w0 w1 [] w3⟩ := by
      simp [tmUniformRevCopyBetween, revCopyBetweenStmt, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux]
    have h2 : (tmUniformRevCopyBetween kWork3 kWork1).step
        ⟨some .pushWork, { bitA := b, bitB := false, carry := true },
          fiveTapeWorkStk [] w0 w1 [] w3⟩ =
        some ⟨some .popIO, { bitA := b, bitB := false, carry := true },
          fiveTapeWorkStk [] w0 (b :: w1) [] w3⟩ := by
      simp [tmUniformRevCopyBetween, revCopyBetweenStmt, mkBitFinTM2, Turing.FinTM2.step,
        Turing.TM2.step, Turing.TM2.stepAux]
    have ih := tmRevWork3ToWork1_loop w3 w0 (b :: w1) { bitA := b, bitB := false, carry := true }
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact EvalsToInTime.mono (EvalsToInTime.of_step h1 (EvalsToInTime.of_step h2 ih))
      (by simp [List.length_cons]; omega)

/-- Composed 2-stage work-tape reversal `kWork2 → kWork0` followed by `kWork3 → kWork1` (`|Λ| = 4`, `|σ| = 8`). -/
def tmRevWork23ToWork01 : Turing.FinTM2 :=
  seqBitFinTM2 RevCopyLabel .popIO RevCopyLabel .popIO UniformReg default default
    (revCopyBetweenStmt kWork2 kWork0) (revCopyBetweenStmt kWork3 kWork1)

/-- **Composed 3-Stage Deinterleave-and-Restore Front-End (`tmDeinterleaveAndRestore`)**:
Composes `tmDeinterleaveToWork2Work3` (`|Λ₁| = 4`) with `tmRevWork23ToWork01` (`|Λ₂| = 4`) via
`seqBitFinTM2` (`|Λ| = 8`, `|σ| = 8`, `|Γ k| = 2`).
Starting from `Turing.initList tmDeinterleaveAndRestore (flattenBitPairs ps)` on the single input
tape `kIO` (with all work tapes empty), splits `kIO` into `kWork2`/`kWork3` and reverses both onto
`kWork0`/`kWork1` to produce `threeTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd)` in forward
LSB-first order in `8 * ps.length + 3` single-bit `FinTM2` steps. -/
def tmDeinterleaveAndRestore : Turing.FinTM2 :=
  seqBitFinTM2 DeinterleaveLabel .popEven (RevCopyLabel ⊕ RevCopyLabel) (Sum.inl .popIO)
    UniformReg default default
    deinterleaveToWork2Work3Stmt tmRevWork23ToWork01.m

theorem isUniformFinTM2_tmDeinterleaveAndRestore :
    IsUniformFinTM2 tmDeinterleaveAndRestore 8 8 2 :=
  isUniformFinTM2_mkBitFinTM2 (Sum.inl DeinterleaveLabel.popEven) default
    tmDeinterleaveAndRestore.m (by decide) (by decide) (by decide)

def tmDeinterleaveAndRestore_evalsToInTime_concrete (ps : List (Bool × Bool)) :
    Turing.EvalsToInTime tmDeinterleaveAndRestore.step
      (Turing.initList tmDeinterleaveAndRestore (flattenBitPairs ps))
      (some ⟨none, default,
        threeTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd)⟩)
      (8 * ps.length + 3) := by
  have hinit : Turing.initList tmDeinterleaveAndRestore (flattenBitPairs ps) =
      ⟨some (Sum.inl DeinterleaveLabel.popEven), default,
        fiveTapeWorkStk (flattenBitPairs ps) [] [] [] []⟩ := by
    rw [fiveTapeWorkStk_nil, fourTapeWorkStk_nil, threeTapeWorkStk_nil, twoTapeStk_nil]; rfl
  have hhalt : (⟨none, default,
      threeTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd)⟩ : tmDeinterleaveAndRestore.Cfg) =
      ⟨none, default, fiveTapeWorkStk [] (ps.map Prod.fst) (ps.map Prod.snd) [] []⟩ := by
    rw [fiveTapeWorkStk_nil, fourTapeWorkStk_nil]
  rw [hinit, hhalt]
  have hp1 := tmDeinterleaveToWork2Work3_loop ps [] [] default
  rw [List.append_nil, List.append_nil] at hp1
  have hp2a := tmRevWork2ToWork0_loop (ps.map Prod.fst).reverse [] (ps.map Prod.snd).reverse default
  rw [List.reverse_reverse, List.append_nil, List.length_reverse, List.length_map] at hp2a
  have hp2b := tmRevWork3ToWork1_loop (ps.map Prod.snd).reverse (ps.map Prod.fst) [] default
  rw [List.reverse_reverse, List.append_nil, List.length_reverse, List.length_map] at hp2b
  have hp2 := seqBitFinTM2_evalsToInTime_concrete RevCopyLabel.popIO RevCopyLabel.popIO
    default default
    (revCopyBetweenStmt kWork2 kWork0) (revCopyBetweenStmt kWork3 kWork1) hp2a hp2b
  have hseq := seqBitFinTM2_evalsToInTime_concrete
    DeinterleaveLabel.popEven (Sum.inl RevCopyLabel.popIO) default default
    deinterleaveToWork2Work3Stmt tmRevWork23ToWork01.m hp1 hp2
  exact EvalsToInTime.mono hseq (by omega)

/-- **Single-Tape Signed Offset-Binary Adder (`tmSingleTapeSignedAdd`)**:
Composes `tmDeinterleaveAndRestore` (`|Λ₁| = 8`, `|σ| = 8`) with `tmUniformRippleAdd` (`|Λ₂| = 6`,
`|σ| = 8`) via `seqBitFinTM2` (`|Λ| = 14`, `|σ| = 8`, `|Γ k| = 2`).
Starts from `Turing.initList` on `kIO` (with all work tapes empty) and halts at
`Turing.haltList` on `kIO` with `encodeSignedWord (w + 1) (x + y)` in `13 * w + 21` steps for any
signed integers `x, y : ℤ` (`FitsSignedWord w x`, `FitsSignedWord w y`). -/
def tmSingleTapeSignedAdd : Turing.FinTM2 :=
  seqBitFinTM2
    tmDeinterleaveAndRestore.Λ (Sum.inl .popEven)
    RippleAddLabel .popA
    UniformReg default default
    tmDeinterleaveAndRestore.m
    tmUniformRippleAdd.m

theorem isUniformFinTM2_tmSingleTapeSignedAdd :
    IsUniformFinTM2 tmSingleTapeSignedAdd 14 8 2 :=
  isUniformFinTM2_mkBitFinTM2 (Sum.inl (Sum.inl DeinterleaveLabel.popEven)) default
    tmSingleTapeSignedAdd.m (by decide) (by decide) (by decide)

@[simp]
theorem map_fst_zip_eq_of_length_eq {α β : Type*} :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (List.zip xs ys).map Prod.fst = xs
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp [List.zip_cons_cons, map_fst_zip_eq_of_length_eq xs ys (by simpa using h)]

@[simp]
theorem map_snd_zip_eq_of_length_eq {α β : Type*} :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (List.zip xs ys).map Prod.snd = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp [List.zip_cons_cons, map_snd_zip_eq_of_length_eq xs ys (by simpa using h)]

/-- Constructive evaluation of `tmSingleTapeSignedAdd` from `Turing.initList` on `kIO` to
`Turing.haltList` on `kIO` for arbitrary signed integers `x, y : ℤ` (`FitsSignedWord w x`,
`FitsSignedWord w y`) in `13 * w + 21` single-bit `FinTM2` steps. -/
def tmSingleTapeSignedAdd_encodeSignedWord_evalsToInTime_concrete (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    Turing.EvalsToInTime tmSingleTapeSignedAdd.step
      (Turing.initList tmSingleTapeSignedAdd
        (flattenBitPairs (List.zip (encodeSignedWord w x) (encodeSignedWord w y))))
      (some (Turing.haltList tmSingleTapeSignedAdd (encodeSignedWord (w + 1) (x + y))))
      (13 * w + 21) := by
  set ps := List.zip (encodeSignedWord w x) (encodeSignedWord w y)
  have hlen_xy : (encodeSignedWord w x).length = (encodeSignedWord w y).length := by simp
  have hfst : ps.map Prod.fst = encodeSignedWord w x :=
    map_fst_zip_eq_of_length_eq _ _ hlen_xy
  have hsnd : ps.map Prod.snd = encodeSignedWord w y :=
    map_snd_zip_eq_of_length_eq _ _ hlen_xy
  have hlen_ps : ps.length = w + 1 := by
    simp [ps]
  have hp1_raw := tmDeinterleaveAndRestore_evalsToInTime_concrete ps
  rw [hfst, hsnd, hlen_ps] at hp1_raw
  have hp1 : Turing.EvalsToInTime
      (mkBitFinTM2 tmDeinterleaveAndRestore.Λ (Sum.inl DeinterleaveLabel.popEven)
        UniformReg default tmDeinterleaveAndRestore.m).step
      ⟨some (Sum.inl DeinterleaveLabel.popEven), default, singleTapeStk (flattenBitPairs ps)⟩
      (some ⟨none, default,
        threeTapeWorkStk [] (encodeSignedWord w x) (encodeSignedWord w y)⟩)
      (8 * (w + 1) + 3) := hp1_raw
  have hp2 : Turing.EvalsToInTime
      (mkBitFinTM2 RippleAddLabel RippleAddLabel.popA UniformReg default tmUniformRippleAdd.m).step
      ⟨some RippleAddLabel.popA, default,
        threeTapeWorkStk [] (encodeSignedWord w x) (encodeSignedWord w y)⟩
      (some ⟨none, default, singleTapeStk (encodeSignedWord (w + 1) (x + y))⟩)
      (5 * w + 10) :=
    tmUniformRippleAdd_encodeSignedWord_evalsToInTime_concrete w x y hx hy
  have hseq := seqBitFinTM2_evalsToInTime_concrete
    (Sum.inl DeinterleaveLabel.popEven) RippleAddLabel.popA default default
    tmDeinterleaveAndRestore.m tmUniformRippleAdd.m hp1 hp2
  exact EvalsToInTime.mono hseq (by omega)

theorem tmSingleTapeSignedAdd_encodeSignedWord_evalsToInTime (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    ∃ t ≤ 13 * w + 21,
      Turing.EvalsToInTime tmSingleTapeSignedAdd.step
        (Turing.initList tmSingleTapeSignedAdd
           (flattenBitPairs (List.zip (encodeSignedWord w x) (encodeSignedWord w y))))
        (some (Turing.haltList tmSingleTapeSignedAdd (encodeSignedWord (w + 1) (x + y)))) t :=
  ⟨_, le_rfl, ⟨tmSingleTapeSignedAdd_encodeSignedWord_evalsToInTime_concrete w x y hx hy⟩⟩

/-- **Single-Tape Simultaneous Signed Butterfly Machine (`tmSingleTapeSignedButterfly`)**:
Composes the register-lifted `tmDeinterleaveAndRestore` (`|Λ₁| = 8`, `|σ| = 16`) with
`tmComposedSignedButterflyStage` (`|Λ₂| = 14`, `|σ| = 16`) via `seqBitFinTM2` (`|Λ| = 22`,
`|σ| = 16`, `|Γ k| = 2`).
Starts from `Turing.initList` on the single input tape `kIO` (with all work tapes empty)
and halts at `Turing.haltList` on `kIO` with
`encodeSignedWord (w + 1) (x - y) ++ encodeSignedWord (w + 1) (x + y)` in `20 * w + 38` steps
for **all** signed integers `x, y : ℤ` (`FitsSignedWord w x`, `FitsSignedWord w y`, **no `y ≤ x`
assumption**). -/
def tmSingleTapeSignedButterfly : Turing.FinTM2 :=
  seqBitFinTM2
    tmDeinterleaveAndRestore.Λ (Sum.inl .popEven)
    tmComposedSignedButterflyStage.Λ (Sum.inl .initBorrow)
    ButterflyReg default default
    (fun l => liftUniformRegStmt (tmDeinterleaveAndRestore.m l))
    tmComposedSignedButterflyStage.m

theorem isUniformFinTM2_tmSingleTapeSignedButterfly :
    IsUniformFinTM2 tmSingleTapeSignedButterfly 22 16 2 :=
  isUniformFinTM2_mkBitFinTM2 (Sum.inl (Sum.inl DeinterleaveLabel.popEven)) default
    tmSingleTapeSignedButterfly.m (by decide) (by decide) (by decide)

def tmSingleTapeSignedButterfly_encodeSignedWord_evalsToInTime_concrete (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    Turing.EvalsToInTime tmSingleTapeSignedButterfly.step
      (Turing.initList tmSingleTapeSignedButterfly
        (flattenBitPairs (List.zip (encodeSignedWord w x) (encodeSignedWord w y))))
      (some (Turing.haltList tmSingleTapeSignedButterfly
        (encodeSignedWord (w + 1) (x - y) ++ encodeSignedWord (w + 1) (x + y))))
      (20 * w + 38) := by
  set ps := List.zip (encodeSignedWord w x) (encodeSignedWord w y)
  have hlen_xy : (encodeSignedWord w x).length = (encodeSignedWord w y).length := by simp
  have hfst : ps.map Prod.fst = encodeSignedWord w x :=
    map_fst_zip_eq_of_length_eq _ _ hlen_xy
  have hsnd : ps.map Prod.snd = encodeSignedWord w y :=
    map_snd_zip_eq_of_length_eq _ _ hlen_xy
  have hlen_ps : ps.length = w + 1 := by simp [ps]
  have hp1_unif := tmDeinterleaveAndRestore_evalsToInTime_concrete ps
  rw [hfst, hsnd, hlen_ps] at hp1_unif
  have hp1 := liftUniformRegTM_evalsToInTime_default_concrete
    (Sum.inl DeinterleaveLabel.popEven) tmDeinterleaveAndRestore.m hp1_unif
  have hp2 : Turing.EvalsToInTime
      (mkBitFinTM2 tmComposedSignedButterflyStage.Λ
        (Sum.inl SignedButterflyLabel.initBorrow)
        ButterflyReg default tmComposedSignedButterflyStage.m).step
      ⟨some (Sum.inl SignedButterflyLabel.initBorrow), default,
        threeTapeWorkStk [] (encodeSignedWord w x) (encodeSignedWord w y)⟩
      (some ⟨none, default,
        singleTapeStk (encodeSignedWord (w + 1) (x - y) ++ encodeSignedWord (w + 1) (x + y))⟩)
      (12 * w + 27) :=
    tmComposedSignedButterflyStage_encodeSignedWord_evalsToInTime_concrete w x y hx hy
  have hseq := seqBitFinTM2_evalsToInTime_concrete
    (Sum.inl DeinterleaveLabel.popEven) (Sum.inl SignedButterflyLabel.initBorrow)
    default default
    (fun l => liftUniformRegStmt (tmDeinterleaveAndRestore.m l))
    tmComposedSignedButterflyStage.m hp1 hp2
  exact EvalsToInTime.mono hseq (by omega)

theorem tmSingleTapeSignedButterfly_encodeSignedWord_evalsToInTime (w : ℕ) (x y : ℤ)
    (hx : FitsSignedWord w x) (hy : FitsSignedWord w y) :
    ∃ t ≤ 20 * w + 38,
      Turing.EvalsToInTime tmSingleTapeSignedButterfly.step
        (Turing.initList tmSingleTapeSignedButterfly
          (flattenBitPairs (List.zip (encodeSignedWord w x) (encodeSignedWord w y))))
        (some (Turing.haltList tmSingleTapeSignedButterfly
          (encodeSignedWord (w + 1) (x - y) ++ encodeSignedWord (w + 1) (x + y)))) t :=
  ⟨_, le_rfl, ⟨tmSingleTapeSignedButterfly_encodeSignedWord_evalsToInTime_concrete w x y hx hy⟩⟩

/-! ## 7. Inhabited Uniform `FinTM2` Composition Suite (`UniformTMCompositionSuite`, `canonicalUniformTMCompositionSuite`) -/

/-- **Inhabited Uniform 8-Stack Binary Machine (`Turing.FinTM2`) Composition Bundle
(`UniformTMCompositionSuite`)**:
Packages the composed multi-stage uniform 8-stack binary machines (`Turing.FinTM2`) with their
`IsUniformFinTM2` bounds and unconditional `EvalsToInTime` `TM2.step` transition bounds (including
inter-stage stack reversals, schedule-driven multi-pass loops, signed offset-binary
arithmetic for arbitrary `x, y : ℤ`, and `Turing.initList` realizations on 8 binary stacks). -/
structure UniformTMCompositionSuite : Prop where
  /-- `tmComposedIdCopy` is a composed uniform `FinTM2` (`|Λ| ≤ 4`, `|σ| ≤ 8`, `|Γ k| ≤ 2`). -/
  unif_composedIdCopy : IsUniformFinTM2 tmComposedIdCopy 4 8 2
  /-- `tmComposedIdCopy` streams `xs` from `kIO` to `kWork0` and back in `≤ 4 * xs.length + 2` steps. -/
  eval_composedIdCopy :
    ∀ xs : List Bool,
      ∃ t ≤ 4 * xs.length + 2,
        Turing.EvalsToInTime tmComposedIdCopy.step
          (Turing.initList tmComposedIdCopy xs)
          (some (Turing.haltList tmComposedIdCopy xs)) t
  /-- `tmComposedDeinterleaveInterleave` is a composed uniform `FinTM2` (`|Λ| ≤ 10`, `|σ| ≤ 8`). -/
  unif_deinterleaveInterleave : IsUniformFinTM2 tmComposedDeinterleaveInterleave 10 8 2
  /-- `tmComposedDeinterleaveInterleave` splits and re-interleaves `flattenBitPairs ps` in
  `≤ 12 * ps.length + 3` steps. -/
  eval_deinterleaveInterleave :
    ∀ ps : List (Bool × Bool),
      ∃ t ≤ 12 * ps.length + 3,
        Turing.EvalsToInTime tmComposedDeinterleaveInterleave.step
          (Turing.initList tmComposedDeinterleaveInterleave (flattenBitPairs ps))
          (some (Turing.haltList tmComposedDeinterleaveInterleave (flattenBitPairs ps.reverse))) t
  /-- `tmComposedOrderPreservingShuffle` is a composed uniform `FinTM2` (`|Λ| ≤ 20`, `|σ| ≤ 8`). -/
  unif_orderPreservingShuffle : IsUniformFinTM2 tmComposedOrderPreservingShuffle 20 8 2
  /-- `tmComposedOrderPreservingShuffle` recovers `flattenBitPairs ps` on `kIO` in
  `≤ 24 * ps.length + 6` steps. -/
  eval_orderPreservingShuffle :
    ∀ ps : List (Bool × Bool),
      ∃ t ≤ 24 * ps.length + 6,
        Turing.EvalsToInTime tmComposedOrderPreservingShuffle.step
          (Turing.initList tmComposedOrderPreservingShuffle (flattenBitPairs ps))
          (some (Turing.haltList tmComposedOrderPreservingShuffle (flattenBitPairs ps))) t
  /-- `tmComposedMultiPassTranspose` is a schedule-driven loop uniform `FinTM2` (`|Λ| ≤ 21`, `|σ| ≤ 8`). -/
  unif_multiPassTranspose : IsUniformFinTM2 tmComposedMultiPassTranspose 21 8 2
  /-- `tmComposedMultiPassTranspose` executes `sched.length` streaming transpose passes in
  `≤ sched.length * (24 * ps.length + 7) + 1` steps. -/
  eval_multiPassTranspose :
    ∀ (sched : List Bool) (ps : List (Bool × Bool)),
      ∃ t ≤ sched.length * (24 * ps.length + 7) + 1,
        Turing.EvalsToInTime tmComposedMultiPassTranspose.step
          ⟨some none, default, ioSchedStk (flattenBitPairs ps) sched⟩
          (some (Turing.haltList tmComposedMultiPassTranspose (flattenBitPairs ps))) t
  /-- `tmComposedButterflyStage` is a composed uniform `FinTM2` (`|Λ| ≤ 13`, `|σ| ≤ 16`). -/
  unif_butterflyStage : IsUniformFinTM2 tmComposedButterflyStage 13 16 2
  /-- `tmComposedButterflyStage` computes and packs both `A - B` and `A + B` onto `kIO` in
  `≤ 12 * w + 8` steps. -/
  eval_butterflyStage :
    ∀ w A B : ℕ, B ≤ A → A < 2 ^ w →
      ∃ t ≤ 12 * w + 8,
        Turing.EvalsToInTime tmComposedButterflyStage.step
          ⟨some (Sum.inl .popA), default,
            threeTapeWorkStk [] (encodeNatBits w A) (encodeNatBits w B)⟩
          (some (Turing.haltList tmComposedButterflyStage
            (encodeNatBits w (A - B) ++ encodeNatBits (w + 1) (A + B)))) t
  /-- `tmComposedCondSubPass` is a composed uniform `FinTM2` (`|Λ| ≤ 12`, `|σ| ≤ 16`). -/
  unif_condSubPass : IsUniformFinTM2 tmComposedCondSubPass 12 16 2
  /-- `tmComposedCondSubPass` executes conditional subtract-mux and returns the remainder and
  quotient bit to `kWork0` in `≤ 11 * w + 5` steps. -/
  eval_condSubPass :
    ∀ w R D : ℕ, R < 2 ^ w → D < 2 ^ w →
      ∃ t ≤ 11 * w + 5,
        Turing.EvalsToInTime tmComposedCondSubPass.step
          ⟨some (Sum.inl .popA), default,
            threeTapeWorkStk [] (encodeNatBits w R) (encodeNatBits w D)⟩
          (some ⟨none, default,
            twoTapeStk [] (encodeNatBits w (if D ≤ R then R - D else R) ++ [decide (D ≤ R)])⟩) t
  /-- `tmUniformSignedButterflyAddSub` is a uniform `FinTM2` (`|Λ| ≤ 10`, `|σ| ≤ 16`). -/
  unif_signedButterflyAddSub : IsUniformFinTM2 tmUniformSignedButterflyAddSub 10 16 2
  /-- `tmUniformSignedButterflyAddSub` computes both `encodeSignedWord (w + 1) (x + y)` on `kIO` and
  `encodeSignedWord (w + 1) (x - y)` on `kWork0` in `≤ 8 * w + 17` steps for all `x, y : ℤ`
  (`FitsSignedWord w x`, `FitsSignedWord w y`). -/
  eval_signedButterflyAddSub :
    ∀ (w : ℕ) (x y : ℤ), FitsSignedWord w x → FitsSignedWord w y →
      ∃ t ≤ 8 * w + 17,
        Turing.EvalsToInTime tmUniformSignedButterflyAddSub.step
          ⟨some .initBorrow, default,
            threeTapeWorkStk [] (encodeSignedWord w x) (encodeSignedWord w y)⟩
          (some ⟨none, default,
            twoTapeStk (encodeSignedWord (w + 1) (x + y)) (encodeSignedWord (w + 1) (x - y))⟩) t
  /-- `tmComposedSignedButterflyStage` is a composed uniform `FinTM2` (`|Λ| ≤ 14`, `|σ| ≤ 16`). -/
  unif_composedSignedButterflyStage : IsUniformFinTM2 tmComposedSignedButterflyStage 14 16 2
  /-- `tmComposedSignedButterflyStage` computes and packs both `encodeSignedWord (w + 1) (x - y)` and
  `encodeSignedWord (w + 1) (x + y)` onto `kIO` in `≤ 12 * w + 27` steps for all `x, y : ℤ`
  (`FitsSignedWord w x`, `FitsSignedWord w y`). -/
  eval_composedSignedButterflyStage :
    ∀ (w : ℕ) (x y : ℤ), FitsSignedWord w x → FitsSignedWord w y →
      ∃ t ≤ 12 * w + 27,
        Turing.EvalsToInTime tmComposedSignedButterflyStage.step
          ⟨some (Sum.inl .initBorrow), default,
            threeTapeWorkStk [] (encodeSignedWord w x) (encodeSignedWord w y)⟩
          (some (Turing.haltList tmComposedSignedButterflyStage
            (encodeSignedWord (w + 1) (x - y) ++ encodeSignedWord (w + 1) (x + y)))) t
  /-- `tmSingleTapeSignedAdd` is a composed single-tape uniform `FinTM2` (`|Λ| ≤ 14`, `|σ| ≤ 8`). -/
  unif_singleTapeSignedAdd : IsUniformFinTM2 tmSingleTapeSignedAdd 14 8 2
  /-- `tmSingleTapeSignedAdd` evaluates from `Turing.initList` on `kIO` to `Turing.haltList` on `kIO`
  with `encodeSignedWord (w + 1) (x + y)` in `≤ 13 * w + 21` steps for all `x, y : ℤ`
  (`FitsSignedWord w x`, `FitsSignedWord w y`). -/
  eval_singleTapeSignedAdd :
    ∀ (w : ℕ) (x y : ℤ), FitsSignedWord w x → FitsSignedWord w y →
      ∃ t ≤ 13 * w + 21,
        Turing.EvalsToInTime tmSingleTapeSignedAdd.step
          (Turing.initList tmSingleTapeSignedAdd
            (flattenBitPairs (List.zip (encodeSignedWord w x) (encodeSignedWord w y))))
          (some (Turing.haltList tmSingleTapeSignedAdd (encodeSignedWord (w + 1) (x + y)))) t
  /-- `tmSingleTapeSignedButterfly` is a composed single-tape uniform `FinTM2` (`|Λ| ≤ 22`, `|σ| ≤ 16`). -/
  unif_singleTapeSignedButterfly : IsUniformFinTM2 tmSingleTapeSignedButterfly 22 16 2
  /-- `tmSingleTapeSignedButterfly` evaluates from `Turing.initList` on `kIO` to `Turing.haltList` on
  `kIO` with `encodeSignedWord (w + 1) (x - y) ++ encodeSignedWord (w + 1) (x + y)` in
  `≤ 20 * w + 38` steps for **all** signed integers `x, y : ℤ` (`FitsSignedWord w x`,
  `FitsSignedWord w y`, with **no** `y ≤ x` restriction). -/
  eval_singleTapeSignedButterfly :
    ∀ (w : ℕ) (x y : ℤ), FitsSignedWord w x → FitsSignedWord w y →
      ∃ t ≤ 20 * w + 38,
        Turing.EvalsToInTime tmSingleTapeSignedButterfly.step
          (Turing.initList tmSingleTapeSignedButterfly
            (flattenBitPairs (List.zip (encodeSignedWord w x) (encodeSignedWord w y))))
          (some (Turing.haltList tmSingleTapeSignedButterfly
            (encodeSignedWord (w + 1) (x - y) ++ encodeSignedWord (w + 1) (x + y)))) t

/-- Concrete, unconditional inhabitant of `UniformTMCompositionSuite`. -/
theorem canonicalUniformTMCompositionSuite : UniformTMCompositionSuite where
  unif_composedIdCopy := isUniformFinTM2_tmComposedIdCopy
  eval_composedIdCopy := tmComposedIdCopy_evalsToInTime
  unif_deinterleaveInterleave := isUniformFinTM2_tmComposedDeinterleaveInterleave
  eval_deinterleaveInterleave := tmComposedDeinterleaveInterleave_evalsToInTime
  unif_orderPreservingShuffle := isUniformFinTM2_tmComposedOrderPreservingShuffle
  eval_orderPreservingShuffle := tmComposedOrderPreservingShuffle_evalsToInTime
  unif_multiPassTranspose := isUniformFinTM2_tmComposedMultiPassTranspose
  eval_multiPassTranspose := tmComposedMultiPassTranspose_evalsToInTime
  unif_butterflyStage := isUniformFinTM2_tmComposedButterflyStage
  eval_butterflyStage := tmComposedButterflyStage_encodeNatBits_evalsToInTime
  unif_condSubPass := isUniformFinTM2_tmComposedCondSubPass
  eval_condSubPass := tmComposedCondSubPass_encodeNatBits_evalsToInTime
  unif_signedButterflyAddSub := isUniformFinTM2_tmUniformSignedButterflyAddSub
  eval_signedButterflyAddSub := tmUniformSignedButterflyAddSub_encodeSignedWord_evalsToInTime
  unif_composedSignedButterflyStage := isUniformFinTM2_tmComposedSignedButterflyStage
  eval_composedSignedButterflyStage := tmComposedSignedButterflyStage_encodeSignedWord_evalsToInTime
  unif_singleTapeSignedAdd := isUniformFinTM2_tmSingleTapeSignedAdd
  eval_singleTapeSignedAdd := tmSingleTapeSignedAdd_encodeSignedWord_evalsToInTime
  unif_singleTapeSignedButterfly := isUniformFinTM2_tmSingleTapeSignedButterfly
  eval_singleTapeSignedButterfly := tmSingleTapeSignedButterfly_encodeSignedWord_evalsToInTime

end IntMul

#print axioms IntMul.EvalsToInTime.map_simulation
#print axioms IntMul.isUniformFinTM2_liftUniformRegTM
#print axioms IntMul.liftUniformRegTM_evalsToInTime_concrete
#print axioms IntMul.isUniformFinTM2_remapTapesTM
#print axioms IntMul.remapTapesTM_evalsToInTime_concrete
#print axioms IntMul.isUniformFinTM2_seqBitFinTM2
#print axioms IntMul.seqBitFinTM2_evalsToInTime_concrete
#print axioms IntMul.isUniformFinTM2_loopTapeBitFinTM2
#print axioms IntMul.loopTapeBitFinTM2_evalsToInTime_concrete
#print axioms IntMul.tmComposedIdCopy_evalsToInTime
#print axioms IntMul.tmComposedDeinterleaveInterleave_evalsToInTime
#print axioms IntMul.tmComposedOrderPreservingShuffle_evalsToInTime
#print axioms IntMul.tmComposedMultiPassTranspose_evalsToInTime
#print axioms IntMul.tmComposedButterflyStage_encodeNatBits_evalsToInTime
#print axioms IntMul.tmComposedCondSubPass_encodeNatBits_evalsToInTime
#print axioms IntMul.tmUniformRippleAdd_encodeSignedWord_evalsToInTime
#print axioms IntMul.tmUniformSignedButterflyAddSub_encodeSignedWord_evalsToInTime
#print axioms IntMul.tmSingleTapeSignedAdd_encodeSignedWord_evalsToInTime
#print axioms IntMul.tmSingleTapeSignedButterfly_encodeSignedWord_evalsToInTime
#print axioms IntMul.canonicalUniformTMCompositionSuite
