import WP.Top.Obligations
import WP.Top.CostArith
import WP.W10b.Main
import WP.W10b.Tape

/-!
# WP.Top.CostShape — `W9CostShape` from W10b

`W9CostShape_of_W10b`: given the tape converter and a width bound
`wd, wR ≤ cw·(log₂ n + 1)` (owned by W11b), the cost-shape obligation holds. The pieces:

* **`pc`** is W10b's plain functions as a record literal:
  `⟨w9Root C wR T, w9Levels …, w9LevelLin C …, w9MulCount …, w9MulWidth …⟩`, with `K := C` and
  `N₀ := 2`.
  * The widths are clamped to `0` at `n = 0` (`clampW`, `clampR`). W10b's bounds quantify over all
    `n`, while the width hypothesis starts at `n = 1`.
  * Clamping changes nothing at `n ≥ 1`.
* **Bounds:** `PipeBounds pc (w9Const C cw cT)` is W10b's `w9_bounds`.
* **Cost:** the cost inequality is W10b's `w9_cost_le`, minus the tape term
  `C·(|tapeSyms| + 1) ≥ 0`, which Top charges to the table stage.
* **Tape:** `T n = Cc·(64·C₇·n·log₂ n + 1)` (`tapeT`). It combines TapeConv's size clause
  `|tapeSyms| ≤ Cc·(|W7.tape| + 1)` with W10b's `w7_tape_le` (`|W7.tape| ≤ 64·C₇·n·log₂ n`,
  `C₇ = WP.W7pure.tapeBoundConst`).
* **Junk:** there is no `junk` field here. W9's exit state is exact (`w9Out`), and the output stage's
  cost (`WP.Top.Cost.out_le`, `outN`) already bounds the symbols it clears.
-/

namespace WP.Top

open Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  IntMulTM.Contracts.Top

/-- A width profile, clamped to `0` at `n = 0`. -/
def clampW (f : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ := fun n ℓ => if 1 ≤ n then f n ℓ else 0

/-- A root width, clamped to `0` at `n = 0`. -/
def clampR (f : ℕ → ℕ) : ℕ → ℕ := fun n => if 1 ≤ n then f n else 0

theorem clampW_eq {f : ℕ → ℕ → ℕ} {n : ℕ} (hn : 1 ≤ n) : clampW f n = f n :=
  funext fun _ => if_pos hn

theorem clampR_eq {f : ℕ → ℕ} {n : ℕ} (hn : 1 ≤ n) : clampR f n = f n := if_pos hn

theorem clampW_le {f : ℕ → ℕ → ℕ} {cw : ℕ} (h : ∀ n ≥ 1, ∀ ℓ, f n ℓ ≤ cw * (Nat.log2 n + 1)) :
    ∀ n ℓ, clampW f n ℓ ≤ cw * (Nat.log2 n + 1) := by
  intro n ℓ
  unfold clampW
  split_ifs with hn
  · exact h n hn ℓ
  · exact Nat.zero_le _

theorem clampR_le {f : ℕ → ℕ} {cw : ℕ} (h : ∀ n ≥ 1, f n ≤ cw * (Nat.log2 n + 1)) :
    ∀ n, clampR f n ≤ cw * (Nat.log2 n + 1) := by
  intro n
  unfold clampR
  split_ifs with hn
  · exact h n hn
  · exact Nat.zero_le _

/-- The bound on W9's table tape: TapeConv's size clause over W10b's `w7_tape_le`. -/
def tapeT (Cc n : ℕ) : ℕ := Cc * (64 * WP.W7pure.tapeBoundConst * n * Nat.log2 n + 1)

theorem tapeT_le (Cc n : ℕ) (hn : 2 ≤ n) :
    tapeT Cc n ≤ Cc * (64 * WP.W7pure.tapeBoundConst + 1) * n * Nat.log2 n := by
  have hX : 1 ≤ n * Nat.log2 n := le_trans (by omega) (Nat.le_mul_of_pos_right n (log2_pos hn))
  unfold tapeT
  calc Cc * (64 * WP.W7pure.tapeBoundConst * n * Nat.log2 n + 1)
      ≤ Cc * (64 * WP.W7pure.tapeBoundConst * n * Nat.log2 n + n * Nat.log2 n) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = Cc * (64 * WP.W7pure.tapeBoundConst + 1) * n * Nat.log2 n := by ring

/-- **`W9CostShape` from W10b**, given the tape converter and the width bound (W11b). -/
theorem W9CostShape_of_W10b {wdF wdI : ℕ → ℕ → ℕ} {wR : ℕ → ℕ} (hconv : TapeConv)
    (hw : ∃ cw, ∀ n ≥ 1, ∀ ℓ, wdF n ℓ ≤ cw * (Nat.log2 n + 1) ∧ wdI n ℓ ≤ cw * (Nat.log2 n + 1) ∧
      wR n ≤ cw * (Nat.log2 n + 1)) :
    W9CostShape wdF wdI wR := by
  obtain ⟨cw, hcw⟩ := hw
  obtain ⟨Cc, hCc⟩ := hconv
  obtain ⟨mc, Rc, obs, Pc, -, -, -, -, hspecc⟩ := hCc ()
  -- W9's tape is at most `tapeT Cc n` (TapeConv's size clause over `w7_tape_le`)
  have hTS : ∀ n (cSpec : IntMul.ComputablePaperFastDFTSpec), 2 ≤ n → Joint n cSpec →
      (tapeSyms cSpec).length ≤ tapeT Cc n := by
    intro n cSpec hn hj
    have h1 := (hspecc n cSpec (fun _ => W7.tape W7.snapshotSchedule.toTapeFormat cSpec) hj rfl).1
    have h2 : (W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length ≤
        64 * WP.W7pure.tapeBoundConst * n * Nat.log2 n := WP.W10b.w7_tape_le hn cSpec hj
    unfold tapeT
    exact h1.trans (Nat.mul_le_mul_left _ (by omega))
  intro c0 c1 w0 C
  refine ⟨⟨WP.W10b.w9Root C (clampR wR) (tapeT Cc),
      WP.W10b.w9Levels (clampW wdF) (clampW wdI) (clampR wR),
      WP.W10b.w9LevelLin C (clampW wdF) (clampW wdI) (clampR wR),
      WP.W10b.w9MulCount (clampW wdF) (clampW wdI) (clampR wR),
      WP.W10b.w9MulWidth (clampW wdF) (clampW wdI) (clampR wR)⟩,
    WP.W10b.w9Const C cw (Cc * (64 * WP.W7pure.tapeBoundConst + 1)), C, 2, ?_, ?_⟩
  · exact WP.W10b.w9_bounds C cw _ (clampW wdF) (clampW wdI) (clampR wR) (tapeT Cc)
      (clampW_le fun n hn ℓ => (hcw n hn ℓ).1) (clampW_le fun n hn ℓ => (hcw n hn ℓ).2.1)
      (clampR_le fun n hn => (hcw n hn 0).2.2) (fun n hn => tapeT_le Cc n hn)
  · intro n hn cSpec hj
    have hn1 : 1 ≤ n := by omega
    have h := WP.W10b.w9_cost_le C (clampW wdF) (clampW wdI) (clampR wR) (tapeT Cc) (T3 c0 c1 w0) n
      cSpec hj.faithful (hTS n cSpec hn hj)
    rw [clampW_eq hn1, clampW_eq hn1, clampR_eq hn1] at h
    refine le_trans ?_ h
    exact Nat.mul_le_mul_left _ (by omega)

#assert_std_axioms clampW_eq clampR_eq clampW_le clampR_le tapeT_le W9CostShape_of_W10b

end WP.Top
