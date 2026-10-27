import IntMul.Defs
import IntMul.Schedule
import IntMul.FixedPoint
import IntMul.SyntheticFFT
import IntMul.PoissonKernel
import IntMul.KroneckerSpread
import IntMul.Deconvolution
import IntMul.TMPrimitives
import IntMul.TMComposition
import IntMul.FastDFT
import IntMul.ComputableSchedule
import IntMul.ComputableCore
import IntMul.TrackedCore
import IntMul.EndToEnd
import IntMul.TMCompiler
import IntMul.TMStages
import IntMul.TMArithStages
import IntMul.TMStageEval
import IntMul.TMSchedule
import IntMul.TMScheduleTree
import IntMul.TMSpreadFFT
import IntMul.TMKronecker
import IntMul.TMFastDFT
import IntMul.TMDeconvolution
import IntMul.TMFastDFTRecursive
import IntMul.TMEndToEnd

set_option backward.isDefEq.respectTransparency false

/-!
# Windowed Sinc-Gaussian Fractional-Shift Integer Multiplication (`IntMul`)

Umbrella module for the Lean 4 formalization of the
windowed sinc-Gaussian fractional-shift integer multiplication algorithm via the
polynomial transform (`syntheticFFT` in this development), establishing
Theorem 2 (`thm:lean`) as described in Section 8 (`sec:lean`) of the paper.

## Trust Boundary

To verify the statement of the unconditional $O(n \log n)$ integer multiplication theorem
(Theorem 2 (`thm:lean`)), a reader needs only to inspect the following definitions and theorems
and Mathlib's `Turing.TM2` / `Turing.EvalsToInTime`:
1. **Bit encodings (`IntMul/Defs.lean`)**:
   - `encodeNatBits (w : ℕ) (x : ℕ) : List Bool := List.ofFn (fun i : Fin w => x.testBit i.val)`
   - `encodeInputBits (n A B : ℕ) : List Bool := encodeNatBits n A ++ encodeNatBits n B`
2. **Uniformity predicate (`IntMul/TMPrimitives.lean`)**:
   - `IsUniformFinTM2 (tm : Turing.FinTM2) (maxLabels maxStates maxAlpha : ℕ) : Prop` asserting
     `Fintype.card tm.Λ ≤ maxLabels`, `Fintype.card tm.σ ≤ maxStates`,
     `Fintype.card (tm.Γ tm.k₀) ≤ maxAlpha`, `Fintype.card tm.K ≤ 8`, and
     `∀ k, Fintype.card (tm.Γ k) ≤ maxAlpha`.
3. **Concrete parameter-free machine & uniformity proof (`IntMul/TMEndToEnd.lean`)**:
   - `def tmIntMul : Turing.FinTM2 := (bmRunRaw bmIntMulCore).toFinTM2`
   - `theorem isUniformFinTM2_tmIntMul : IsUniformFinTM2 tmIntMul (bmRunRaw bmIntMulCore).numLabels 32 2`
4. **End-to-end $O(n \log n)$ stack-machine theorems (`IntMul/TMEndToEnd.lean`, `IntMul.lean`)**:
   - `theorem tmIntMul_evalsToInTime_n_log_n : ∃ C > 0, ∀ n : ℕ, 2 ≤ n → ∀ A B : ℕ, A < 2 ^ n → B < 2 ^ n → ∃ t ≤ C * n * Nat.log 2 n, Turing.EvalsToInTime tmIntMul.step (Turing.initList tmIntMul (encodeInputBits n A B)) (some (Turing.haltList tmIntMul (encodeNatBits (2 * n) (A * B)))) t`
   - `theorem tmIntMul_elementary_stack_ops_n_log_n` (bounding both `TM2.step` transitions and
     elementary single-bit `push`/`pop`/`peek`/`load`/`branch`/`goto`/`halt` operations by
     $O(n \log n)$, together with the data-level 2-stack-per-tape pairing
     `eightStacksEquivFourBiInfiniteTapes : (Fin 8 → List Bool) ≃ (Fin 4 → List Bool × List Bool)`).

## Module Overview
- **Analytic Accuracy, Polynomial Transform, and Earlier-Draft Barrier Results**: `IntMul.PoissonKernel`,
  `IntMul.SyntheticFFT`, `IntMul.KroneckerSpread`, `IntMul.Deconvolution`, `IntMul.FastDFT`
  (formalizing Section 3 (`sec:prelim`) through Section 6 (`sec:spread-and-error`) of the paper,
  together with algebraic barrier identities from the restricted-model section of an earlier draft,
  which is omitted from the published paper;
  see `IntMul.SyntheticFFT` Part 7).
- **Layer 1 (Counted Bit-Operation Model `CostM`)**: `IntMul.ComputableSchedule`,
  `IntMul.ComputableCore`, `IntMul.TrackedCore`, `IntMul.EndToEnd`
  (`computableNatMulTracked_spec`, `computableNatMulBitsTracked_spec`,
  `intMul_endToEnd_unconditional_summary`, `auditTrackedDeclarations`).
- **Layer 2 (Uniform 8-Stack `Turing.FinTM2` Realization)**: `IntMul.TMCompiler`,
  `IntMul.TMStages`, `IntMul.TMArithStages`, `IntMul.TMStageEval`, `IntMul.TMSchedule`,
  `IntMul.TMScheduleTree`, `IntMul.TMSpreadFFT`, `IntMul.TMKronecker`, `IntMul.TMFastDFT`,
  `IntMul.TMDeconvolution`, `IntMul.TMFastDFTRecursive`, `IntMul.TMEndToEnd`.
-/

namespace IntMul

/-! ## Elementary Single-Bit Stack Operations per `TM2.step` & 8-Stack / 4-Tape Pairing (Section 8 (`sec:lean`)) -/

/-- Worst-case number of elementary single-bit operations (`push`, `pop`, `peek`, `load`,
`branch`, `goto`, `halt`) executed in a single `Turing.TM2.stepAux` call on statement `q`
(Section 8 (`sec:lean`)). -/
def stmtMaxElemOps {K : Type*} {Γ : K → Type*} {Λ σ : Type*} :
    Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + stmtMaxElemOps q
  | .peek _ _ q => 1 + stmtMaxElemOps q
  | .pop _ _ q => 1 + stmtMaxElemOps q
  | .load _ q => 1 + stmtMaxElemOps q
  | .branch _ q₁ q₂ => 1 + max (stmtMaxElemOps q₁) (stmtMaxElemOps q₂)
  | .goto _ => 1
  | .halt => 1

/-- Exact number of elementary single-bit operations (`push`, `pop`, `peek`, `load`, `branch`,
`goto`, `halt`) executed by `Turing.TM2.stepAux q v stk` on a concrete register `v` and stack
assignment `stk`. -/
def stepAuxElemOps {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*} :
    Turing.TM2.Stmt Γ Λ σ → σ → (∀ k : K, List (Γ k)) → ℕ
  | .push k f q, v, stk => 1 + stepAuxElemOps q v (Function.update stk k (f v :: stk k))
  | .peek k f q, v, stk => 1 + stepAuxElemOps q (f v (stk k).head?) stk
  | .pop k f q, v, stk =>
    1 + stepAuxElemOps q (f v (stk k).head?) (Function.update stk k (stk k).tail)
  | .load a q, v, stk => 1 + stepAuxElemOps q (a v) stk
  | .branch p q₁ q₂, v, stk =>
    1 + cond (p v) (stepAuxElemOps q₁ v stk) (stepAuxElemOps q₂ v stk)
  | .goto _, _, _ => 1
  | .halt, _, _ => 1

/-- Every concrete `stepAux` execution performs at most `stmtMaxElemOps q` elementary single-bit
stack/register operations. -/
theorem stepAuxElemOps_le_stmtMaxElemOps {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*} :
    ∀ (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (stk : ∀ k : K, List (Γ k)),
      stepAuxElemOps q v stk ≤ stmtMaxElemOps q
  | .push k f q, v, stk =>
    Nat.add_le_add_left (stepAuxElemOps_le_stmtMaxElemOps q v _) 1
  | .peek k f q, v, stk =>
    Nat.add_le_add_left (stepAuxElemOps_le_stmtMaxElemOps q _ stk) 1
  | .pop k f q, v, stk =>
    Nat.add_le_add_left (stepAuxElemOps_le_stmtMaxElemOps q _ _) 1
  | .load a q, v, stk =>
    Nat.add_le_add_left (stepAuxElemOps_le_stmtMaxElemOps q _ stk) 1
  | .branch p q₁ q₂, v, stk => by
    dsimp [stepAuxElemOps, stmtMaxElemOps]
    cases p v
    · exact Nat.add_le_add_left
        (le_trans (stepAuxElemOps_le_stmtMaxElemOps q₂ v stk) (le_max_right _ _)) 1
    · exact Nat.add_le_add_left
        (le_trans (stepAuxElemOps_le_stmtMaxElemOps q₁ v stk) (le_max_left _ _)) 1
  | .goto _, _, _ => le_rfl
  | .halt, _, _ => le_rfl

/-- Compositional statement potential (`stmtPotential q`), which assigns weight `2` to `.halt` and
`1` to `.goto` so that `redirectHaltStmt`, `liftInrStmt`, `redirectLoopBodyStmt`, `remapTapesStmt`,
`liftSomeInlStmt`, and `liftSomeInrStmt` preserve `stmtPotential` with **exact equality**. -/
def stmtPotential {K : Type*} {Γ : K → Type*} {Λ σ : Type*} :
    Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + stmtPotential q
  | .peek _ _ q => 1 + stmtPotential q
  | .pop _ _ q => 1 + stmtPotential q
  | .load _ q => 1 + stmtPotential q
  | .branch _ q₁ q₂ => 1 + max (stmtPotential q₁) (stmtPotential q₂)
  | .goto _ => 1
  | .halt => 2

theorem stmtMaxElemOps_le_stmtPotential {K : Type*} {Γ : K → Type*} {Λ σ : Type*} :
    ∀ q : Turing.TM2.Stmt Γ Λ σ, stmtMaxElemOps q ≤ stmtPotential q
  | .push _ _ q => Nat.add_le_add_left (stmtMaxElemOps_le_stmtPotential q) 1
  | .peek _ _ q => Nat.add_le_add_left (stmtMaxElemOps_le_stmtPotential q) 1
  | .pop _ _ q => Nat.add_le_add_left (stmtMaxElemOps_le_stmtPotential q) 1
  | .load _ q => Nat.add_le_add_left (stmtMaxElemOps_le_stmtPotential q) 1
  | .branch _ q₁ q₂ =>
    Nat.add_le_add_left
      (max_le_max (stmtMaxElemOps_le_stmtPotential q₁) (stmtMaxElemOps_le_stmtPotential q₂)) 1
  | .goto _ => le_rfl
  | .halt => Nat.le_succ 1

@[simp]
theorem stmtPotential_remapTapesStmt (π : TapeIdx ≃ TapeIdx) {Λ σ : Type} :
    ∀ q : Turing.TM2.Stmt BitTapeAlphabet Λ σ,
      stmtPotential (remapTapesStmt π q) = stmtPotential q
  | .push _ _ q => congrArg (1 + ·) (stmtPotential_remapTapesStmt π q)
  | .peek _ _ q => congrArg (1 + ·) (stmtPotential_remapTapesStmt π q)
  | .pop _ _ q => congrArg (1 + ·) (stmtPotential_remapTapesStmt π q)
  | .load _ q => congrArg (1 + ·) (stmtPotential_remapTapesStmt π q)
  | .branch _ q₁ q₂ => by
    simp [remapTapesStmt, stmtPotential,
      stmtPotential_remapTapesStmt π q₁, stmtPotential_remapTapesStmt π q₂]
  | .goto _ => rfl
  | .halt => rfl

@[simp]
theorem stmtPotential_redirectHaltStmt {Λ₁ Λ₂ σ : Type} (entry₂ : Λ₂) (resetReg : σ) :
    ∀ q : Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ,
      stmtPotential (redirectHaltStmt entry₂ resetReg q) = stmtPotential q
  | .push _ _ q => congrArg (1 + ·) (stmtPotential_redirectHaltStmt entry₂ resetReg q)
  | .peek _ _ q => congrArg (1 + ·) (stmtPotential_redirectHaltStmt entry₂ resetReg q)
  | .pop _ _ q => congrArg (1 + ·) (stmtPotential_redirectHaltStmt entry₂ resetReg q)
  | .load _ q => congrArg (1 + ·) (stmtPotential_redirectHaltStmt entry₂ resetReg q)
  | .branch _ q₁ q₂ => by
    simp [redirectHaltStmt, stmtPotential,
      stmtPotential_redirectHaltStmt entry₂ resetReg q₁,
      stmtPotential_redirectHaltStmt entry₂ resetReg q₂]
  | .goto _ => rfl
  | .halt => rfl

@[simp]
theorem stmtPotential_liftInrStmt {Λ₁ Λ₂ σ : Type} :
    ∀ q : Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ,
      stmtPotential (liftInrStmt (Λ₁ := Λ₁) q) = stmtPotential q
  | .push _ _ q => congrArg (1 + ·) (stmtPotential_liftInrStmt q)
  | .peek _ _ q => congrArg (1 + ·) (stmtPotential_liftInrStmt q)
  | .pop _ _ q => congrArg (1 + ·) (stmtPotential_liftInrStmt q)
  | .load _ q => congrArg (1 + ·) (stmtPotential_liftInrStmt q)
  | .branch _ q₁ q₂ => by
    simp [liftInrStmt, stmtPotential,
      stmtPotential_liftInrStmt q₁, stmtPotential_liftInrStmt q₂]
  | .goto _ => rfl
  | .halt => rfl

@[simp]
theorem stmtPotential_redirectLoopBodyStmt {Λ σ : Type} (init : σ) :
    ∀ q : Turing.TM2.Stmt BitTapeAlphabet Λ σ,
      stmtPotential (redirectLoopBodyStmt init q) = stmtPotential q
  | .push _ _ q => congrArg (1 + ·) (stmtPotential_redirectLoopBodyStmt init q)
  | .peek _ _ q => congrArg (1 + ·) (stmtPotential_redirectLoopBodyStmt init q)
  | .pop _ _ q => congrArg (1 + ·) (stmtPotential_redirectLoopBodyStmt init q)
  | .load _ q => congrArg (1 + ·) (stmtPotential_redirectLoopBodyStmt init q)
  | .branch _ q₁ q₂ => by
    simp [redirectLoopBodyStmt, stmtPotential,
      stmtPotential_redirectLoopBodyStmt init q₁,
      stmtPotential_redirectLoopBodyStmt init q₂]
  | .goto _ => rfl
  | .halt => rfl

@[simp]
theorem stmtPotential_liftSomeInlStmt {Λ₁ Λ₂ σ : Type} :
    ∀ q : Turing.TM2.Stmt BitTapeAlphabet Λ₁ σ,
      stmtPotential (BitMachine.liftSomeInlStmt (Λ₂ := Λ₂) q) = stmtPotential q
  | .push _ _ q => congrArg (1 + ·) (stmtPotential_liftSomeInlStmt q)
  | .peek _ _ q => congrArg (1 + ·) (stmtPotential_liftSomeInlStmt q)
  | .pop _ _ q => congrArg (1 + ·) (stmtPotential_liftSomeInlStmt q)
  | .load _ q => congrArg (1 + ·) (stmtPotential_liftSomeInlStmt q)
  | .branch _ q₁ q₂ => by
    simp [BitMachine.liftSomeInlStmt, stmtPotential,
      stmtPotential_liftSomeInlStmt q₁, stmtPotential_liftSomeInlStmt q₂]
  | .goto _ => rfl
  | .halt => rfl

@[simp]
theorem stmtPotential_liftSomeInrStmt {Λ₁ Λ₂ σ : Type} :
    ∀ q : Turing.TM2.Stmt BitTapeAlphabet Λ₂ σ,
      stmtPotential (BitMachine.liftSomeInrStmt (Λ₁ := Λ₁) q) = stmtPotential q
  | .push _ _ q => congrArg (1 + ·) (stmtPotential_liftSomeInrStmt q)
  | .peek _ _ q => congrArg (1 + ·) (stmtPotential_liftSomeInrStmt q)
  | .pop _ _ q => congrArg (1 + ·) (stmtPotential_liftSomeInrStmt q)
  | .load _ q => congrArg (1 + ·) (stmtPotential_liftSomeInrStmt q)
  | .branch _ q₁ q₂ => by
    simp [BitMachine.liftSomeInrStmt, stmtPotential,
      stmtPotential_liftSomeInrStmt q₁, stmtPotential_liftSomeInrStmt q₂]
  | .goto _ => rfl
  | .halt => rfl

/-- Maximum number of elementary single-bit operations (`push`, `pop`, `peek`, `load`, `branch`,
`goto`, `halt`) in any single control-label statement `M.m l` of a `Turing.FinTM2` machine. -/
@[nospecialize, irreducible]
def finTM2MaxStmtElemOps (M : Turing.FinTM2) : ℕ :=
  Finset.univ.sup (fun l : M.Λ => stmtMaxElemOps (M.m l))

/-- Every control label `l : M.Λ` of any `Turing.FinTM2` machine `M` executes at most
`finTM2MaxStmtElemOps M` elementary single-bit stack/register operations per `TM2.step`. -/
theorem stmtMaxElemOps_le_finTM2MaxStmtElemOps (M : Turing.FinTM2) (l : M.Λ) :
    stmtMaxElemOps (M.m l) ≤ finTM2MaxStmtElemOps M := by
  unfold finTM2MaxStmtElemOps
  exact Finset.le_sup (f := fun l : M.Λ => stmtMaxElemOps (M.m l)) (Finset.mem_univ l)

/-- `FinTM2BoundedElemOps M C_step` states that every single transition `M.m l` of `M : Turing.FinTM2`
has worst-case elementary single-bit operation depth `stmtMaxElemOps (M.m l) ≤ C_step` (and hence
every concrete `stepAux` execution performs at most `C_step` elementary `push`/`pop`/`peek`/`load`/
`branch`/`goto`/`halt` operations by `stepAuxElemOps_le_stmtMaxElemOps`; Section 8 (`sec:lean`)). -/
def FinTM2BoundedElemOps (M : Turing.FinTM2) (C_step : ℕ) : Prop :=
  ∀ l : M.Λ, stmtMaxElemOps (M.m l) ≤ C_step

theorem finTM2BoundedElemOps_self (M : Turing.FinTM2) :
    FinTM2BoundedElemOps M (finTM2MaxStmtElemOps M + 1) :=
  fun l => le_trans (stmtMaxElemOps_le_finTM2MaxStmtElemOps M l)
    (Nat.le_succ (finTM2MaxStmtElemOps M))

/-- General lifting of an $O(n \log n)$ `EvalsToInTime` bound on any `M : Turing.FinTM2` to a joint
step-count and elementary stack-operation bound. -/
theorem evalsToInTime_elementary_stack_ops_of_evalsToInTime (M : Turing.FinTM2)
    (fIn : ℕ → ℕ → ℕ → List (M.Γ M.k₀))
    (fOut : ℕ → ℕ → ℕ → List (M.Γ M.k₁))
    (hrun : ∃ C > 0, ∀ n : ℕ, 2 ≤ n → ∀ A B : ℕ, A < 2 ^ n → B < 2 ^ n →
      ∃ t ≤ C * n * Nat.log 2 n,
        Turing.EvalsToInTime M.step (Turing.initList M (fIn n A B))
          (some (Turing.haltList M (fOut n A B))) t) :
    ∃ C_step C_time C_ops : ℕ, 0 < C_step ∧ 0 < C_time ∧ 0 < C_ops ∧
      FinTM2BoundedElemOps M C_step ∧
      ∀ n : ℕ, 2 ≤ n → ∀ A B : ℕ, A < 2 ^ n → B < 2 ^ n →
        ∃ t ≤ C_time * n * Nat.log 2 n,
          C_step * t ≤ C_ops * n * Nat.log 2 n ∧
          Turing.EvalsToInTime M.step (Turing.initList M (fIn n A B))
            (some (Turing.haltList M (fOut n A B))) t := by
  rcases hrun with ⟨C_time, hC_time, hrun⟩
  refine ⟨finTM2MaxStmtElemOps M + 1, C_time, (finTM2MaxStmtElemOps M + 1) * C_time,
    Nat.succ_pos _, hC_time, Nat.mul_pos (Nat.succ_pos _) hC_time,
    finTM2BoundedElemOps_self M, ?_⟩
  intro n hn A B hA hB
  rcases hrun n hn A B hA hB with ⟨t, ht, heval⟩
  refine ⟨t, ht, ?_, heval⟩
  have hm := Nat.mul_le_mul_left (finTM2MaxStmtElemOps M + 1) ht
  simpa only [Nat.mul_assoc] using hm

/-- **End-to-End $O(n \log n)$ Elementary Single-Bit Stack-Operation Theorem for `tmIntMul`
(`tmIntMul_elementary_stack_ops_n_log_n`, Theorem 2 (`thm:lean`), Section 8 (`sec:lean`))**:
Every single transition of `tmIntMul` executes at most `C_step = O(1)` elementary
single-bit stack/register operations (`FinTM2BoundedElemOps tmIntMul C_step`), and for all $n \ge 2$
and $A, B < 2^n$, `tmIntMul` evaluates `Turing.initList tmIntMul (encodeInputBits n A B)` to
`some (Turing.haltList tmIntMul (encodeNatBits (2 * n) (A * B)))` in $t \le C_{\text{time}} n \log_2 n$
`TM2` steps and at most $C_{\text{step}} \cdot t \le C_{\text{ops}} \cdot n \cdot \lfloor\log_2 n\rfloor$
elementary single-bit operations. -/
theorem tmIntMul_elementary_stack_ops_n_log_n :
    ∃ C_step C_time C_ops : ℕ, 0 < C_step ∧ 0 < C_time ∧ 0 < C_ops ∧
      FinTM2BoundedElemOps tmIntMul C_step ∧
      ∀ n : ℕ, 2 ≤ n → ∀ A B : ℕ, A < 2 ^ n → B < 2 ^ n →
        ∃ t ≤ C_time * n * Nat.log 2 n,
          C_step * t ≤ C_ops * n * Nat.log 2 n ∧
          Turing.EvalsToInTime tmIntMul.step
            (Turing.initList tmIntMul (encodeInputBits n A B))
            (some (Turing.haltList tmIntMul (encodeNatBits (2 * n) (A * B)))) t :=
  evalsToInTime_elementary_stack_ops_of_evalsToInTime tmIntMul
    (fun n A B => encodeInputBits n A B)
    (fun n A B => encodeNatBits (2 * n) (A * B))
    tmIntMul_evalsToInTime_n_log_n

/-- Data-level 2-stack-per-tape pairing equivalence between an 8-stack `FinTM2` configuration
(`Fin 8 → List Bool`) and four `(left, right)` list pairs
(`Fin 4 → List Bool × List Bool`), where stacks `2 * j` and `2 * j + 1` represent the
two halves associated with pair `j` (Section 8 (`sec:lean`)). -/
def eightStacksEquivFourBiInfiniteTapes :
    (Fin 8 → List Bool) ≃ (Fin 4 → List Bool × List Bool) where
  toFun stk j :=
    (stk ⟨2 * j.val, by omega⟩, stk ⟨2 * j.val + 1, by omega⟩)
  invFun tapes k :=
    if hk : k.val % 2 = 0 then
      (tapes ⟨k.val / 2, by omega⟩).1
    else
      (tapes ⟨k.val / 2, by omega⟩).2
  left_inv stk := by
    funext ⟨k, hk⟩
    dsimp only
    split_ifs with hmod
    · congr 1; ext; dsimp; omega
    · congr 1; ext; dsimp; omega
  right_inv tapes := by
    funext ⟨j, hj⟩
    have hj1 : (2 * j) % 2 = 0 := by omega
    have hj2 : ¬ ((2 * j + 1) % 2 = 0) := by omega
    have hdiv1 : (⟨(2 * j) / 2, by omega⟩ : Fin 4) = ⟨j, hj⟩ := Fin.ext (by dsimp; omega)
    have hdiv2 : (⟨(2 * j + 1) / 2, by omega⟩ : Fin 4) = ⟨j, hj⟩ := Fin.ext (by dsimp; omega)
    exact Prod.ext (by dsimp only; rw [dif_pos hj1, hdiv1])
      (by dsimp only; rw [dif_neg hj2, hdiv2])

open Lean Elab Command in
/-- Compile-time command verifying via `Lean.collectAxioms` that the transitive axiom closure of
`id` contains ONLY the standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`), and
throwing a hard compile error if `sorryAx` or any custom axiom is present (Section 8 (`sec:lean`)). -/
elab "#verify_standard_axioms " id:ident : command => do
  let nm ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  let axioms ← liftCoreM (Lean.collectAxioms nm)
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for ax in axioms do
    if !allowed.contains ax then
      throwError "Non-standard axiom '{ax}' found in transitive closure of '{nm}'!"

#verify_tracked_declarations_ast_audit
#verify_standard_axioms IntMul.tmIntMul
#verify_standard_axioms IntMul.isUniformFinTM2_tmIntMul
#verify_standard_axioms IntMul.tmIntMul_evalsToInTime_n_log_n
#verify_standard_axioms IntMul.tmIntMul_elementary_stack_ops_n_log_n
#verify_standard_axioms IntMul.intMul_complete_endToEnd_summary
#verify_standard_axioms IntMul.intMul_endToEnd_unconditional_summary

end IntMul

#print axioms IntMul.tmIntMul
#print axioms IntMul.isUniformFinTM2_tmIntMul
#print axioms IntMul.tmIntMul_evalsToInTime_n_log_n
#print axioms IntMul.tmIntMul_elementary_stack_ops_n_log_n
#print axioms IntMul.intMul_complete_endToEnd_summary
#print axioms IntMul.intMul_endToEnd_unconditional_summary
