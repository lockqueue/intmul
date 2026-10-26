import WP.Top.Correct
import WP.Top.CostArith

/-!
# WP.Top.Cost — the cost glue: stage bounds → W10's `StageCosts` / `StageBounds`

**Per-input cost** (`top_triple`): `Tin + tabCost + convCost + glueCost + w9Cost + outCost`.
For `n = operandBits a b` above a threshold, each stage bound is a function of `n`
(`actual_le_total`, proved in `WP.Top.Main`):

| `StageCosts` field | function | covers |
|---|---|---|
| `input` | `inCostN C0 n = C0·(2n+2) + C0·288·(n+1)` | W0m: `C0·(L+1) + C0·(Λ+1)²`, with `(Λ+1)² ≤ 144·(L+1)` (`sq_bitLen_le`) |
| `tables` | `tabsN … n = auxα·Q n + auxβ·n + auxγ` | W7 build, tape conversion, glue, W9's tape term `C9·(|tapeSyms|+1)` |
| `root`, `levels`, `levelLin`, `mulCount`, `mulWidth` | `pc` from `W9CostShape` | W9's `C9·(rootBound + pipeBound F + pipeBound I)` |
| `output` | `outN … n = outα·Q n + 3064·n + outγ` | copy-out and cleanup of `≤ 76·w9OutBound` symbols |

Here `Q n = (√n+1)(log₂ n+1)^8` (`sqP`). `tables` and `output` are guarded: they are `0` below the
threshold `N`, where W7's `√n` bounds do not apply yet; `WP.Top.Main` absorbs small inputs into a
constant. **`topCosts_bounds`**: every field satisfies `StageBounds` with
`Ab = 580·C0 + Kaux + Kout + A9` (`poly_le`).
-/

namespace WP.Top

open Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  IntMulTM.Contracts.Top

/-- `Q n = (√n + 1)·(log₂ n + 1)^8`, the unit of the sublinear bounds. -/
def sqP (n : ℕ) : ℕ := (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8

/-- Input-stage bound. -/
def inCostN (C0 n : ℕ) : ℕ := C0 * (2 * n + 2) + C0 * (288 * (n + 1))

/-- Coefficients of the auxiliary bound (tables, conversion, glue, W9 tape term). -/
def auxα (C7 Cp Ct Cc C9 : ℕ) : ℕ := C7 * (Cp + Ct) + Cc * Ct + C9 * (Cc * Ct)
/-- Linear coefficient of the auxiliary bound. -/
def auxβ (C7 : ℕ) : ℕ := 10 * C7 + 35
/-- Constant of the auxiliary bound. -/
def auxγ (C7 Cc C9 : ℕ) : ℕ := 31 * C7 + Cc + C9 * Cc + C9 + 88

/-- Auxiliary stages, guarded at `N`. -/
def tabsN (C7 Cp Ct Cc C9 N n : ℕ) : ℕ :=
  if N ≤ n then auxα C7 Cp Ct Cc C9 * sqP n + auxβ C7 * n + auxγ C7 Cc C9 else 0

/-- Output stage, guarded at `N`. -/
def outN (Cc Ct N n : ℕ) : ℕ :=
  if N ≤ n then 152 * (Cc * Ct) * sqP n + 3064 * n + (152 * Cc + 6708) else 0

/-- **The stage-cost functions of the composed program.** -/
def topCosts (C0 C7 Cp Ct Cc C9 N : ℕ) (pc : PipeCosts) : StageCosts where
  input := inCostN C0
  tables := tabsN C7 Cp Ct Cc C9 N
  root := pc.root
  output := outN Cc Ct N
  levels := pc.levels
  levelLin := pc.levelLin
  mulCount := pc.mulCount
  mulWidth := pc.mulWidth

theorem topCosts_total (C0 C7 Cp Ct Cc C9 N : ℕ) (pc : PipeCosts) (M : ℕ → ℕ) (n : ℕ) :
    (topCosts C0 C7 Cp Ct Cc C9 N pc).total M n =
      inCostN C0 n + tabsN C7 Cp Ct Cc C9 N n + outN Cc Ct N n + pc.cost M n := by
  simp only [StageCosts.total, topCosts, PipeCosts.cost]
  omega

/-! ## `StageBounds` -/

theorem inCostN_le (C0 n : ℕ) (hn : 2 ≤ n) : inCostN C0 n ≤ (580 * C0) * (n * Nat.log2 n) := by
  have h := poly_le 0 (290 * C0) (290 * C0) n hn
  have e : inCostN C0 n = 0 * sqP n + 290 * C0 * n + 290 * C0 := by unfold inCostN; ring
  have e2 : (0 * 2 ^ 42 + 290 * C0 + 290 * C0) = 580 * C0 := by ring
  rw [e]
  unfold sqP
  rw [e2] at h
  exact h

theorem tabsN_le (C7 Cp Ct Cc C9 N n : ℕ) (hn : 2 ≤ n) :
    tabsN C7 Cp Ct Cc C9 N n ≤
      (auxα C7 Cp Ct Cc C9 * 2 ^ 42 + auxβ C7 + auxγ C7 Cc C9) * (n * Nat.log2 n) := by
  unfold tabsN
  split_ifs
  · exact poly_le _ _ _ n hn
  · exact Nat.zero_le _

theorem outN_le (Cc Ct N n : ℕ) (hn : 2 ≤ n) :
    outN Cc Ct N n ≤ (152 * (Cc * Ct) * 2 ^ 42 + 3064 + (152 * Cc + 6708)) * (n * Nat.log2 n) := by
  unfold outN
  split_ifs
  · exact poly_le _ _ _ n hn
  · exact Nat.zero_le _

/-- **`StageBounds` for the composed program.** -/
theorem topCosts_bounds {C0 C7 Cp Ct Cc C9 N : ℕ} {pc : PipeCosts} {A9 : ℕ}
    (hpb : PipeBounds pc A9) :
    StageBounds (topCosts C0 C7 Cp Ct Cc C9 N pc)
      (580 * C0 + (auxα C7 Cp Ct Cc C9 * 2 ^ 42 + auxβ C7 + auxγ C7 Cc C9) +
        (152 * (Cc * Ct) * 2 ^ 42 + 3064 + (152 * Cc + 6708)) + A9) := by
  intro n hn
  obtain ⟨h1, h2, h3, h4⟩ := hpb n hn
  set KA := auxα C7 Cp Ct Cc C9 * 2 ^ 42 + auxβ C7 + auxγ C7 Cc C9 with hKA
  set KO := 152 * (Cc * Ct) * 2 ^ 42 + 3064 + (152 * Cc + 6708) with hKO
  have hA9 : A9 ≤ 580 * C0 + KA + KO + A9 := by omega
  have hX : ∀ K, K * n * Nat.log2 n = K * (n * Nat.log2 n) := fun K => Nat.mul_assoc _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · show inCostN C0 n + tabsN C7 Cp Ct Cc C9 N n + pc.root n + outN Cc Ct N n ≤ _
    have e1 := inCostN_le C0 n hn
    have e2 := tabsN_le C7 Cp Ct Cc C9 N n hn
    have e3 := outN_le Cc Ct N n hn
    rw [hX] at h1 ⊢
    rw [← hKA] at e2
    rw [← hKO] at e3
    have e : (580 * C0 + KA + KO + A9) * (n * Nat.log2 n) =
        580 * C0 * (n * Nat.log2 n) + KA * (n * Nat.log2 n) + KO * (n * Nat.log2 n) +
          A9 * (n * Nat.log2 n) := by ring
    rw [e]
    omega
  · exact h2.trans (Nat.mul_le_mul_right _ hA9)
  · rw [hX] at h3 ⊢
    exact h3.trans (Nat.mul_le_mul_right _ hA9)
  · intro ℓ hℓ
    obtain ⟨a1, a2, a3⟩ := h4 ℓ hℓ
    exact ⟨a1.trans (Nat.mul_le_mul_right _ hA9), a2.trans (Nat.mul_le_mul_right _ hA9),
      a3.trans (Nat.mul_le_mul_right _ hA9)⟩

/-! ## Per-stage bounds at the operand bit length -/

theorem bitLen_mul_le (a b : ℕ) : bitLen (a * b) ≤ 2 * operandBits a b := by
  obtain ⟨hA, hB, -, -⟩ := input_bridge a b
  have h : a * b < 2 ^ (2 * operandBits a b) := by
    calc a * b ≤ a * 2 ^ operandBits a b := Nat.mul_le_mul_left a hB.le
      _ < 2 ^ operandBits a b * 2 ^ operandBits a b :=
          Nat.mul_lt_mul_of_pos_right hA (Nat.two_pow_pos _)
      _ = 2 ^ (2 * operandBits a b) := by rw [← pow_add, two_mul]
  rw [WP.W0m.bitLen_eq_size]
  exact Nat.size_le.mpr h

/-- The input stage's bound at `n = operandBits a b`. -/
theorem tin_le (C0 a b : ℕ) :
    C0 * ((encNatPair.encode (a, b)).length + 1) +
        C0 * ((WP.W0m.lam a b + 1) * (WP.W0m.lam a b + 1)) ≤ inCostN C0 (operandBits a b) := by
  have hL : (encNatPair.encode (a, b)).length = WP.W0m.inLen a b := by
    rw [encNatPair_encode_length]
    rfl
  obtain ⟨-, -, -, hL2⟩ := input_bridge a b
  have hsq := sq_bitLen_le (18 * (WP.W0m.inLen a b + 1)) (by omega)
  have hlam : WP.W0m.lam a b = bitLen (18 * (WP.W0m.inLen a b + 1)) := rfl
  rw [← hlam] at hsq
  rw [hL] at hL2 ⊢
  unfold inCostN
  have h1 : C0 * (WP.W0m.inLen a b + 1) ≤ C0 * (2 * operandBits a b + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : C0 * ((WP.W0m.lam a b + 1) * (WP.W0m.lam a b + 1)) ≤
      C0 * (288 * (operandBits a b + 1)) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Schedule values are linear in `n` (bit lengths are at most the values). -/
theorem sched_bitLens (n : ℕ) (hn : 1 ≤ n) :
    bitLen n ≤ n ∧ bitLen (W8.hB n) ≤ n ∧ bitLen (W8.hK n) ≤ n + 1 ∧
      bitLen (W8.hK0 n) ≤ 2 * n + 6 ∧ bitLen (W8.hL n) ≤ 2 * n + 6 ∧
      bitLen (W8.hP0 n) ≤ 6 * n + 18 :=
  ⟨WP.W0m.bitLen_le_self n, le_trans (WP.W0m.bitLen_le_self _) (WP.W0m.sB_le hn),
    le_trans (WP.W0m.bitLen_le_self _) (WP.W0m.sK_le n),
    le_trans (WP.W0m.bitLen_le_self _) (WP.W0m.sK0_le n),
    le_trans (WP.W0m.bitLen_le_self _) (WP.W0m.sL_le n),
    le_trans (WP.W0m.bitLen_le_self _) (WP.W0m.sP0_le hn)⟩

/-- The auxiliary stages' bound. -/
theorem aux_le (C7 Cp Ct Cc C9 n : ℕ) (hn : 1 ≤ n) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (hP : (W8.hSpec n).precomputeSeriesTableCost ≤ Cp * sqP n)
    (hT7 : (W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length ≤ Ct * sqP n)
    (hTS : (tapeSyms cSpec).length ≤
      Cc * ((W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length + 1)) :
    tabCost C7 n cSpec + (convCost Cc cSpec + (glueCost n + C9 * ((tapeSyms cSpec).length + 1))) ≤
      auxα C7 Cp Ct Cc C9 * sqP n + auxβ C7 * n + auxγ C7 Cc C9 := by
  obtain ⟨-, bB, bK, bK0, bL, bP⟩ := sched_bitLens n hn
  unfold tabCost convCost glueCost
  have h1 : C7 * ((W8.hSpec n).precomputeSeriesTableCost +
      (W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length +
      bitLen (W8.hL n) + bitLen (W8.hP0 n) + bitLen (W8.hK0 n) + 1) ≤
      C7 * (Cp * sqP n + Ct * sqP n + (10 * n + 31)) := Nat.mul_le_mul_left _ (by omega)
  have h2 : Cc * ((W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length + 1) ≤
      Cc * (Ct * sqP n + 1) := Nat.mul_le_mul_left _ (by omega)
  have h3 : (tapeSyms cSpec).length ≤ Cc * (Ct * sqP n + 1) :=
    hTS.trans (Nat.mul_le_mul_left _ (by omega))
  have h4 : C9 * ((tapeSyms cSpec).length + 1) ≤ C9 * (Cc * (Ct * sqP n + 1) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  calc _ ≤ C7 * (Cp * sqP n + Ct * sqP n + (10 * n + 31)) +
        (Cc * (Ct * sqP n + 1) + ((35 * n + 88) + C9 * (Cc * (Ct * sqP n + 1) + 1))) := by
        omega
    _ = auxα C7 Cp Ct Cc C9 * sqP n + auxβ C7 * n + auxγ C7 Cc C9 := by
        unfold auxα auxβ auxγ
        ring

/-- The output stage's bound. -/
theorem out_le (Cc Ct a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (hT7 : (W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length ≤ Ct * sqP (operandBits a b))
    (hTS : (tapeSyms cSpec).length ≤
      Cc * ((W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length + 1)) :
    outCost (bitLen (a * b)) (totalSize (w9Out (operandBits a b) a b cSpec (a * b))) ≤
      152 * (Cc * Ct) * sqP (operandBits a b) + 3064 * operandBits a b + (152 * Cc + 6708) := by
  set n := operandBits a b with hn
  have hn1 : 1 ≤ n := WP.W0m.operandBits_pos a b
  obtain ⟨bn, bB, bK, bK0, bL, bP⟩ := sched_bitLens n hn1
  have hJ := totalSize_w9Out_le n a b cSpec (a * b)
  unfold w9OutBound at hJ
  have hv : bitLen (a * b) ≤ 2 * n := bitLen_mul_le a b
  have hTS' : (tapeSyms cSpec).length ≤ Cc * (Ct * sqP n + 1) :=
    hTS.trans (Nat.mul_le_mul_left _ (by omega))
  have hhdr : (rootHdr n).length ≤ 5 * n + 12 := by
    unfold rootHdr
    rw [length_hdrSyms]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have e : Cc * (Ct * sqP n + 1) = Cc * Ct * sqP n + Cc := by ring
  have e2 : 152 * (Cc * Ct) * sqP n = 152 * (Cc * Ct * sqP n) := by ring
  unfold outCost
  rw [length_allGW, e2]
  omega

#assert_std_axioms topCosts_total inCostN_le tabsN_le outN_le topCosts_bounds bitLen_mul_le tin_le
  sched_bitLens aux_le out_le

end WP.Top
