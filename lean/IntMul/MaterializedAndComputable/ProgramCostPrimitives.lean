import IntMul.MaterializedAndComputable.PaperStopAndRadix2Leaf
import IntMul.MaterializedAndComputable.ComputableExactSolvers

/-!
# Part 1 — Generic Bit-Cell Simulation, `BitCostM` Primitive Cost Interface, and Program-Costed Subroutines
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

/-- Elementary `Zero ℤ` dictionary (`0 : ℤ`), activated strictly via `attribute [local instance 10000]`
inside audited `BitCostM` modules so that `read1D`/`read2D` array accesses do not synthesize
`Zero ℤ` via Mathlib's `Int.instNormedCommRing` while leaving global `Zero ℤ` synthesis untouched. -/
@[instance_reducible] def instZeroIntElementary : Zero ℤ := ⟨0⟩

attribute [local instance 10000] instZeroIntElementary

/-! ### Program-Derived Bit-Operation Cost Interface, Sequential-Transducer-to-Bit-Cell Simulation, & Paper-Stop `BaseRadix2FFT` Computable Pipeline (`[MS]` §§3.2, 6 & 7) -/

/-- Valid single-step record-head transition (`RecordHeadStepValid`, `[MS]` §3.2):
in one sequential transducer step, a tape head index `h` either stays at `h` (`0`),
advances to `h + 1` (`+1`), or (when `0 < h`) steps back to `h - 1` (`-1`). -/
def RecordHeadStepValid (h h' : ℕ) : Prop :=
  h' = h ∨ h' = h + 1 ∨ (0 < h ∧ h' = h - 1)

theorem unshuffleHeadStep_inHead_valid {α : Type*} (inTape : ℕ → α) (st : MultiTapeUnshuffleState α) :
    RecordHeadStepValid st.inHead (unshuffleHeadStep inTape st).inHead := by
  dsimp [unshuffleHeadStep, RecordHeadStepValid]
  split_ifs <;> simp

theorem interleaveRunsHeadStep_heads_valid {α : Type*} (r : ℕ) (topTape botTape : ℕ → α)
    (st : MultiTapeRunInterleaveState α) :
    RecordHeadStepValid st.topHead (interleaveRunsHeadStep r topTape botTape st).topHead ∧
    RecordHeadStepValid st.botHead (interleaveRunsHeadStep r topTape botTape st).botHead := by
  dsimp [interleaveRunsHeadStep, RecordHeadStepValid]
  split_ifs <;> simp

theorem interleaveParityHeadStep_heads_valid {α : Type*} (parity : ℕ) (firstTape secondTape : ℕ → α)
    (st : MultiTapeParityInterleaveState α) :
    RecordHeadStepValid st.firstHead (interleaveParityHeadStep parity firstTape secondTape st).firstHead ∧
    RecordHeadStepValid st.secondHead (interleaveParityHeadStep parity firstTape secondTape st).secondHead := by
  dsimp [interleaveParityHeadStep, RecordHeadStepValid]
  split_ifs <;> simp

theorem scanHeadStep_inHead_valid {α : Type*} (inTape : ℕ → α) (st : MultiTapeScanState α) :
    RecordHeadStepValid st.inHead (scanHeadStep inTape st).inHead := by
  dsimp [scanHeadStep, RecordHeadStepValid]
  simp

theorem seekForwardHeadStep_inHead_valid {α : Type*} (st : MultiTapeScanState α) :
    RecordHeadStepValid st.inHead (seekForwardHeadStep st).inHead := by
  dsimp [seekForwardHeadStep, RecordHeadStepValid]
  simp

theorem reverseHeadStep_inHead_valid {α : Type*} (inTape : ℕ → α) (st : MultiTapeScanState α) :
    RecordHeadStepValid st.inHead (reverseHeadStep inTape st).inHead := by
  dsimp [reverseHeadStep, RecordHeadStepValid]
  rcases Nat.eq_zero_or_pos st.inHead with h0 | hpos
  · left; omega
  · right; right; exact ⟨hpos, rfl⟩

theorem unshuffleHeadStep_valid {α : Type*} (inTape : ℕ → α) (st : MultiTapeUnshuffleState α) :
    RecordHeadStepValid st.inHead (unshuffleHeadStep inTape st).inHead :=
  unshuffleHeadStep_inHead_valid inTape st

theorem interleaveRunsHeadStep_valid {α : Type*} (r : ℕ) (topTape botTape : ℕ → α)
    (st : MultiTapeRunInterleaveState α) :
    RecordHeadStepValid st.topHead (interleaveRunsHeadStep r topTape botTape st).topHead ∧
    RecordHeadStepValid st.botHead (interleaveRunsHeadStep r topTape botTape st).botHead :=
  interleaveRunsHeadStep_heads_valid r topTape botTape st

theorem interleaveParityHeadStep_valid {α : Type*} (parity : ℕ) (firstTape secondTape : ℕ → α)
    (st : MultiTapeParityInterleaveState α) :
    RecordHeadStepValid st.firstHead (interleaveParityHeadStep parity firstTape secondTape st).firstHead ∧
    RecordHeadStepValid st.secondHead (interleaveParityHeadStep parity firstTape secondTape st).secondHead :=
  interleaveParityHeadStep_heads_valid parity firstTape secondTape st

theorem scanHeadStep_valid {α : Type*} (inTape : ℕ → α) (st : MultiTapeScanState α) :
    RecordHeadStepValid st.inHead (scanHeadStep inTape st).inHead :=
  scanHeadStep_inHead_valid inTape st

theorem seekForwardHeadStep_valid {α : Type*} (st : MultiTapeScanState α) :
    RecordHeadStepValid st.inHead (seekForwardHeadStep st).inHead :=
  seekForwardHeadStep_inHead_valid st

theorem reverseHeadStep_valid {α : Type*} (inTape : ℕ → α) (st : MultiTapeScanState α) :
    RecordHeadStepValid st.inHead (reverseHeadStep inTape st).inHead :=
  reverseHeadStep_inHead_valid inTape st

/-- Bit-cell tape head position corresponding to the start of `w`-bit record `r`. -/
def bitHeadOfRecord (w r : ℕ) : ℕ := w * r

/-- Absolute distance `|a - b|` between two natural-number tape cell positions. -/
def natDist (a b : ℕ) : ℕ := (a - b) + (b - a)

/-- **Single-Step Record-to-Bit-Cell Simulation Bound (`bitCellDistance_le_of_recordHeadStepValid`, `[MS]` §3.2)**:
When records have fixed bit-width `w`, any valid record-head transition `RecordHeadStepValid r r'`
(`r' ∈ {r - 1, r, r + 1}`) changes the starting bit-cell position `bitHeadOfRecord w r = w * r` by
at most `w` bit cells, so sweeping the `w` bits of record `r` and positioning at record `r'` takes
at most `2 * w` bit-cell head moves. -/
theorem bitCellDistance_le_of_recordHeadStepValid (w r r' : ℕ) (hstep : RecordHeadStepValid r r') :
    natDist (bitHeadOfRecord w r) (bitHeadOfRecord w r') + w ≤ 2 * w := by
  rcases hstep with rfl | rfl | ⟨hr_pos, rfl⟩
  · dsimp [natDist, bitHeadOfRecord]
    omega
  · dsimp [natDist, bitHeadOfRecord]
    have h1 : w * (r + 1) = w * r + w := by ring
    omega
  · dsimp [natDist, bitHeadOfRecord]
    have h1 : w * r = w * (r - 1) + w := by
      have hr_eq : r = (r - 1) + 1 := by omega
      conv_lhs => rw [hr_eq]
      ring
    omega

/-- Total bit-cell head moves required to simulate a sequence of record-head positions `tr : List ℕ`
on `w`-bit records. -/
def bitCellHeadMovesOfRecordTrace (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | [_] => w
  | r :: r' :: rest =>
    (natDist (bitHeadOfRecord w r) (bitHeadOfRecord w r') + w) +
      bitCellHeadMovesOfRecordTrace w (r' :: rest)

/-- Validity predicate for a record-head trace `tr : List ℕ`: every consecutive pair `(r, r')`
satisfies `RecordHeadStepValid r r'`. -/
def RecordTraceValid : List ℕ → Prop
  | [] => True
  | [_] => True
  | r :: r' :: rest => RecordHeadStepValid r r' ∧ RecordTraceValid (r' :: rest)

/-- **Generic Sequential-Transducer-to-Bit-Cell Simulation Theorem
(`bitCellHeadMovesOfRecordTrace_le_two_mul_width_mul_steps`, `[MS]` §3.2)**:
Any sequential record-level transducer trace `tr : List ℕ` satisfying `RecordTraceValid tr` on
`w`-bit records simulates on a bit-cell tape in at most `2 * w * tr.length` bit-cell head moves. -/
theorem bitCellHeadMovesOfRecordTrace_le_two_mul_width_mul_steps
    (w : ℕ) : ∀ (tr : List ℕ), RecordTraceValid tr →
      bitCellHeadMovesOfRecordTrace w tr ≤ 2 * w * tr.length
  | [], _ => by simp [bitCellHeadMovesOfRecordTrace]
  | [_], _ => by
    simp [bitCellHeadMovesOfRecordTrace]
    omega
  | r :: r' :: rest, ⟨hstep, hrest⟩ => by
    dsimp only [bitCellHeadMovesOfRecordTrace, List.length_cons]
    have h1 := bitCellDistance_le_of_recordHeadStepValid w r r' hstep
    have ih := bitCellHeadMovesOfRecordTrace_le_two_mul_width_mul_steps w (r' :: rest) hrest
    dsimp only [List.length_cons] at ih
    linarith

/-- Bit-cell cost of `recordSteps` sequential record transitions on `w`-bit records. -/
def multitapeBitCellSteps (w recordSteps : ℕ) : ℕ :=
  recordSteps * addBitCost w

@[simp]
theorem multitapeBitCellSteps_eq_recordSteps_mul_width (w recordSteps : ℕ) :
    multitapeBitCellSteps w recordSteps = recordSteps * w := rfl

/-- Writer-monad / cost-accumulator type pairing a computed value `α` with its accumulated
integer bit-operation cost `ℕ` (`BitCostM α := α × ℕ`). -/
abbrev BitCostM (α : Type) : Type := α × ℕ

instance : Pure BitCostM where
  pure a := (a, 0)

instance : Bind BitCostM where
  bind m f :=
    let r := f m.1
    (r.1, m.2 + r.2)

instance : Monad BitCostM where

@[simp]
theorem BitCostM.pure_def {α : Type} (a : α) : (pure a : BitCostM α) = (a, 0) := rfl

@[simp]
theorem BitCostM.pure_fst {α : Type} (a : α) : (pure a : BitCostM α).1 = a := rfl

@[simp]
theorem BitCostM.pure_snd {α : Type} (a : α) : (pure a : BitCostM α).2 = 0 := rfl

@[simp]
theorem BitCostM.bind_def {α β : Type} (m : BitCostM α) (f : α → BitCostM β) :
    (m >>= f) = ((f m.1).1, m.2 + (f m.1).2) := rfl

@[simp]
theorem BitCostM.bind_fst {α β : Type} (m : BitCostM α) (f : α → BitCostM β) :
    (m >>= f).1 = (f m.1).1 := rfl

@[simp]
theorem BitCostM.bind_snd {α β : Type} (m : BitCostM α) (f : α → BitCostM β) :
    (m >>= f).2 = m.2 + (f m.1).2 := rfl

/-- Record a primitive bit-operation cost `c : ℕ` in `BitCostM`. -/
def BitCostM.tick (c : ℕ) : BitCostM Unit := ((), c)

@[simp]
theorem BitCostM.tick_fst (c : ℕ) : (BitCostM.tick c).1 = () := rfl

@[simp]
theorem BitCostM.tick_snd (c : ℕ) : (BitCostM.tick c).2 = c := rfl

/-- Monadic array comprehension in `BitCostM`: evaluates `f i` once for each `i : Fin n`,
extracts the array of first projections via `pairs.map Prod.fst`, and sums the second projections
via `sumArrayCosts pairs`. -/
def BitCostM.ofFnM {α : Type} (n : ℕ) (f : Fin n → BitCostM α) : BitCostM (Array α) :=
  let pairs := Array.ofFn f
  (pairs.map Prod.fst, sumArrayCosts pairs)

@[simp]
theorem BitCostM.ofFnM_fst {α : Type} (n : ℕ) (f : Fin n → BitCostM α) :
    (BitCostM.ofFnM n f).1 = Array.ofFn (fun i => (f i).1) := by
  dsimp [BitCostM.ofFnM]
  ext i hi1 hi2 <;> simp

@[simp]
theorem BitCostM.ofFnM_snd {α : Type} (n : ℕ) (f : Fin n → BitCostM α) :
    (BitCostM.ofFnM n f).2 = sumArrayCosts (Array.ofFn f) := rfl

theorem BitCostM.ofFnM_snd_const {α : Type} (n c : ℕ) (f : Fin n → BitCostM α)
    (hc : ∀ i : Fin n, (f i).2 = c) :
    (BitCostM.ofFnM n f).2 = n * c :=
  sumArrayCosts_ofFn_const n f c (fun i hi => hc ⟨i, hi⟩)

/-- Monadic list map in `BitCostM`: evaluates `f x` once for each `x ∈ xs` and accumulates
the `BitCostM` costs via `Monad BitCostM`. -/
def BitCostM.mapListM {α β : Type} (f : α → BitCostM β) : List α → BitCostM (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← BitCostM.mapListM f xs
    pure (y :: ys)

@[simp]
theorem BitCostM.mapListM_fst {α β : Type} (f : α → BitCostM β) (xs : List α) :
    (BitCostM.mapListM f xs).1 = xs.map (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [BitCostM.mapListM, ih]

theorem BitCostM.mapListM_snd_const {α β : Type} (f : α → BitCostM β) (xs : List α) (c : ℕ)
    (hc : ∀ x ∈ xs, (f x).2 = c) :
    (BitCostM.mapListM f xs).2 = xs.length * c := by
  induction xs with
  | nil => simp [BitCostM.mapListM]
  | cons x xs ih =>
    simp only [BitCostM.mapListM, BitCostM.bind_snd, BitCostM.pure_snd, add_zero, List.length_cons]
    rw [hc x List.mem_cons_self, ih (fun y hy => hc y (List.mem_cons_of_mem x hy))]
    ring

/-- Costed signed integer addition `a + b` at bit-width `w` (`addBitCost w`). -/
def costedAddInt (w : ℕ) (a b : ℤ) : BitCostM ℤ :=
  (a + b, addBitCost w)

/-- Costed Gaussian-integer addition at word bit-width `w` (`2 * addBitCost w`). -/
def costedGAdd (w : ℕ) (z w_in : ℤ × ℤ) : BitCostM (ℤ × ℤ) :=
  (gAdd z w_in, 2 * addBitCost w)

/-- Costed Gaussian-integer subtraction at word bit-width `w` (`2 * addBitCost w`). -/
def costedGSub (w : ℕ) (z w_in : ℤ × ℤ) : BitCostM (ℤ × ℤ) :=
  (gSub z w_in, 2 * addBitCost w)

/-- Costed alternating-sign parity flip `gAltTerm v z = (-1)^v * z` (`costedGAltTerm`, `[MS]` §§5.1–5.2):
applies `gAltTerm v z` at sign-bit cost `0` (charging the sign-conditioned addition in the
enclosing `sumRangePairWithCost` or `costedGAdd`). -/
def costedGAltTerm (v : ℕ) (z : ℤ × ℤ) : BitCostM (ℤ × ℤ) :=
  (gAltTerm v z, 0)

/-- Costed initial homogeneous recurrence vector `#[(((2 ^ (q + 2) : ℕ) : ℤ), 0)]` (`costedZHomInit`, `[MS]` §§5.1–5.2). -/
def costedZHomInit (q : ℕ) : BitCostM (Array (ℤ × ℤ)) :=
  (#[(((2 ^ (q + 2) : ℕ) : ℤ), 0)], 0)

/-- Costed 1-bit rounded complex butterfly average `(divRoundPow2 (a.1 + b.1) 1, divRoundPow2 (a.2 + b.2) 1)`
at word bit-width `w` (`2 * addBitCost w`). -/
def costedButterflyAvg (w : ℕ) (a b : ℤ × ℤ) : BitCostM (ℤ × ℤ) :=
  ((divRoundPow2 (a.1 + b.1) 1, divRoundPow2 (a.2 + b.2) 1), 2 * addBitCost w)

/-- Costed scaled Gaussian-integer multiplication `gMulScaled q a b` charged at the true operand
bit-width `w` (`4 * computableMulBitCost w + 4 * addBitCost w` for the 4 real products and 4 real
additions/shifts). -/
def costedGMulScaled (q w : ℕ) (a b : ℤ × ℤ) : BitCostM (ℤ × ℤ) :=
  (gMulScaled q a b, 4 * computableMulBitCost w + 4 * addBitCost w)

/-- Costed pre-twist product `gPreTwistU q tw uRaw` charged at the true operand bit-width `w`
(`w = 6 * p'` where `uRaw` is scaled by `2^(2 * pSub) = 2^(4 * p')` with integer part `≤ 2^p`). -/
def costedGPreTwistU (q w : ℕ) (tw uRaw : ℤ × ℤ) : BitCostM (ℤ × ℤ) :=
  (gPreTwistU q tw uRaw, 4 * computableMulBitCost w + 4 * addBitCost w)

/-- Costed fixed-point precision rescaling `gRescale p_in p_out z` (power-of-two shift and rounding)
at word bit-width `w` (`2 * addBitCost w`). -/
def costedGRescale (p_in p_out w : ℕ) (z : ℤ × ℤ) : BitCostM (ℤ × ℤ) :=
  (gRescale p_in p_out z, 2 * addBitCost w)

/-- Costed rational solver step `gRatioQuantize q y c1 zPart c0 d1 zHom` charged at the true
unshifted temporary bit-width `w` (`w = 10 * p'` for recurrence steps where `d1 = 0`, and
`w = 22 * p'` for the boundary solve `Z0`). -/
def costedGRatioQuantize (q w : ℕ) (y c1 zPart c0 d1 zHom : ℤ × ℤ) : BitCostM (ℤ × ℤ) :=
  (gRatioQuantize q y c1 zPart c0 d1 zHom, 6 * computableMulBitCost w + 6 * addBitCost w)

/-- Costed boundary linear combination `gCombineQuantize q a b c` charged at the true temporary
bit-width `w` (`w = 22 * p'`). -/
def costedGCombineQuantize (q w : ℕ) (a b c : ℤ × ℤ) : BitCostM (ℤ × ℤ) :=
  (gCombineQuantize q a b c, 4 * computableMulBitCost w + 4 * addBitCost w)

/-- Costed Nyquist recurrence step `gNyqStepQuantize q c0 y prev` charged at the true temporary
bit-width `w` (`w = 10 * p'`). -/
def costedGNyqStepQuantize (q w : ℕ) (c0 y prev : ℤ × ℤ) : BitCostM (ℤ × ℤ) :=
  (gNyqStepQuantize q c0 y prev, 6 * computableMulBitCost w + 6 * addBitCost w)

/-- Costed integer rational rounding `divRoundRatInt num den` charged at operand bit-width `w`
(`2 * computableMulBitCost w + 2 * addBitCost w`). -/
def costedDivRoundRatInt (w : ℕ) (num den : ℤ) : BitCostM ℤ :=
  (divRoundRatInt num den, 2 * computableMulBitCost w + 2 * addBitCost w)

/-- Costed Gaussian-integer rational rounding `gQuantizeRat reNum imNum den` charged at operand
bit-width `w` (`4 * computableMulBitCost w + 4 * addBitCost w`). -/
def costedGQuantizeRat (w : ℕ) (reNum imNum den : ℤ) : BitCostM (ℤ × ℤ) :=
  (gQuantizeRat reNum imNum den, 4 * computableMulBitCost w + 4 * addBitCost w)

/-- Costed input coordinate quantization `gQuantizeCoordToScale p_in q v` charged at operand
bit-width `w` (`2 * addBitCost w`). -/
def costedGQuantizeCoordToScale (p_in q w : ℕ) (v : ℤ) : BitCostM ℤ :=
  (gQuantizeCoordToScale p_in q v, 2 * addBitCost w)

/-- Costed direct $O(r)$ negacyclic rotation `computableNegacyclicDirect r s P` at word bit-width
`w` (`r * (2 * addBitCost w)` for reading/negating `r` complex pairs). -/
def computableNegacyclicDirectWithCost (w r s : ℕ) (P : Array (ℤ × ℤ)) : BitCostM (Array (ℤ × ℤ)) :=
  (computableNegacyclicDirect r s P, r * (2 * addBitCost w))

@[simp]
theorem computableNegacyclicDirectWithCost_fst (w r s : ℕ) (P : Array (ℤ × ℤ)) :
    (computableNegacyclicDirectWithCost w r s P).1 = computableNegacyclicDirect r s P := rfl

@[simp]
theorem computableNegacyclicDirectWithCost_snd (w r s : ℕ) (P : Array (ℤ × ℤ)) :
    (computableNegacyclicDirectWithCost w r s P).2 = r * (2 * addBitCost w) := rfl

/-- Sequential 1D scan over `n` costed operations `f : ℕ → BitCostM α` (`runSequentialScanCostedSteps`):
executes `runSequentialScanSteps (fun i => (f i).1) n` while summing the per-element `BitCostM`
primitive costs `(f i).2` via `sumArrayCosts` and recording the scan head-step count `stVal.steps`. -/
def runSequentialScanCostedSteps {α : Type} (f : ℕ → BitCostM α) (n : ℕ) :
    Array α × ℕ × ℕ :=
  let stVal := runSequentialScanSteps (fun i => (f i).1) n
  let costPairs := Array.ofFn (fun i : Fin n => f i.val)
  (stVal.outTape, stVal.steps, sumArrayCosts costPairs)

@[simp]
theorem runSequentialScanCostedSteps_fst {α : Type} (f : ℕ → BitCostM α) (n : ℕ) :
    (runSequentialScanCostedSteps f n).1 =
      (runSequentialScanSteps (fun i => (f i).1) n).outTape := rfl

@[simp]
theorem runSequentialScanCostedSteps_steps {α : Type} (f : ℕ → BitCostM α) (n : ℕ) :
    (runSequentialScanCostedSteps f n).2.1 = n :=
  runSequentialScanSteps_steps (fun i => (f i).1) n

theorem runSequentialScanCostedSteps_cost_const {α : Type} (f : ℕ → BitCostM α) (n c : ℕ)
    (hc : ∀ i, i < n → (f i).2 = c) :
    (runSequentialScanCostedSteps f n).2.2 = n * c :=
  sumArrayCosts_ofFn_const n _ c (fun i hi => hc i hi)

/-- Sequential 2D `n1 × n2` scan over costed operations `f : ℕ → ℕ → BitCostM α`
(`runScan2DCostedWithSteps`):
executes `runScan2DWithSteps n1 n2 (fun i j => (f i j).1)` while summing the per-cell `BitCostM`
primitive costs `(f i j).2` across all `n1 × n2` cells via `sumArrayCosts` and recording the 2D scan
head-step count `valRes.2`. -/
def runScan2DCostedWithSteps {α : Type} (n1 n2 : ℕ) (f : ℕ → ℕ → BitCostM α) :
    Array (Array α) × ℕ × ℕ :=
  let valRes := runScan2DWithSteps n1 n2 (fun i j => (f i j).1)
  let rowCosts : Array (Unit × ℕ) :=
    Array.ofFn (fun i : Fin n1 =>
      let cellPairs := Array.ofFn (fun j : Fin n2 => f i.val j.val)
      ((), sumArrayCosts cellPairs))
  (valRes.1, valRes.2, sumArrayCosts rowCosts)

@[simp]
theorem runScan2DCostedWithSteps_fst {α : Type} (n1 n2 : ℕ) (f : ℕ → ℕ → BitCostM α) :
    (runScan2DCostedWithSteps n1 n2 f).1 =
      (runScan2DWithSteps n1 n2 (fun i j => (f i j).1)).1 := rfl

@[simp]
theorem runScan2DCostedWithSteps_steps {α : Type} (n1 n2 : ℕ) (f : ℕ → ℕ → BitCostM α) :
    (runScan2DCostedWithSteps n1 n2 f).2.1 = n1 * n2 :=
  runScan2DWithSteps_snd n1 n2 (fun i j => (f i j).1)

theorem runScan2DCostedWithSteps_cost_const {α : Type} (n1 n2 c : ℕ) (f : ℕ → ℕ → BitCostM α)
    (hc : ∀ i, i < n1 → ∀ j, j < n2 → (f i j).2 = c) :
    (runScan2DCostedWithSteps n1 n2 f).2.2 = (n1 * n2) * c := by
  unfold runScan2DCostedWithSteps
  dsimp only
  rw [sumArrayCosts_ofFn_const n1 _ (n2 * c)
        (fun i hi => sumArrayCosts_ofFn_const n2 _ c (fun j hj => hc i hi j hj)),
      mul_assoc]

/-- **Program-Cost-Accumulating Multi-Stage Radix-2 Synthetic FFT
(`computableSyntheticFFTRadix2WithProgramCost`, `[MS]` §3.5 (Lemma 3.5))**:
Executes `computableNegacyclicDirectWithCost (4 * p')` on each row `v1` and `costedButterflyAvg (4 * p')`
at every butterfly output cell `(v1, k2)` of stage `m + 1` in a single monadic pass via `BitCostM.ofFnM`
and `Monad BitCostM` (without duplicate `rowPairs`/`outMat` passes). -/
def computableSyntheticFFTRadix2WithProgramCost (p' V r : ℕ) :
    ℕ → ℕ → Array (Array (ℤ × ℤ)) → BitCostM (Array (Array (ℤ × ℤ)))
  | 0, _, P =>
    pure (Array.ofFn (fun _ : Fin 1 =>
      Array.ofFn (fun k2 : Fin r => (P.getD 0 #[]).getD k2.val (0, 0))))
  | m + 1, c1, P => do
    let Peven := Array.ofFn (fun j1 : Fin (2 ^ m) => P.getD (2 * j1.val) #[])
    let Podd := Array.ofFn (fun j1 : Fin (2 ^ m) => P.getD (2 * j1.val + 1) #[])
    let Y0 ← computableSyntheticFFTRadix2WithProgramCost p' V r m (2 * c1) Peven
    let Y1 ← computableSyntheticFFTRadix2WithProgramCost p' V r m (2 * c1) Podd
    BitCostM.ofFnM (2 ^ (m + 1)) (fun v1 => do
      let y0_row := Y0.getD (v1.val % 2 ^ m) #[]
      let y1_shifted ← computableNegacyclicDirectWithCost (4 * p') r (2 * c1 * v1.val)
        (Y1.getD (v1.val % 2 ^ m) #[])
      BitCostM.ofFnM r (fun k2 =>
        let a := y0_row.getD k2.val (0, 0)
        let b := y1_shifted.getD k2.val (0, 0)
        costedButterflyAvg (4 * p') a b))

@[simp]
theorem computableSyntheticFFTRadix2WithProgramCost_fst
    (p' V r m c1 : ℕ) (P : Array (Array (ℤ × ℤ))) :
    (computableSyntheticFFTRadix2WithProgramCost p' V r m c1 P).1 =
      computableSyntheticFFTRadix2 V r m c1 P := by
  induction m generalizing c1 P with
  | zero => rfl
  | succ m ih =>
    simp only [computableSyntheticFFTRadix2WithProgramCost, computableSyntheticFFTRadix2,
      BitCostM.bind_fst, BitCostM.ofFnM_fst, computableNegacyclicDirectWithCost_fst,
      costedButterflyAvg, ih]

@[simp]
theorem computableSyntheticFFTRadix2WithProgramCost_snd
    (p' V r m c1 : ℕ) (P : Array (Array (ℤ × ℤ))) :
    (computableSyntheticFFTRadix2WithProgramCost p' V r m c1 P).2 =
      2 * (2 * syntheticFFTRadix2AddOps r m * addBitCost (4 * p')) := by
  induction m generalizing c1 P with
  | zero => simp [computableSyntheticFFTRadix2WithProgramCost, syntheticFFTRadix2AddOps]
  | succ m ih =>
    simp only [computableSyntheticFFTRadix2WithProgramCost, syntheticFFTRadix2AddOps,
      BitCostM.bind_snd]
    rw [ih, ih,
        BitCostM.ofFnM_snd_const (2 ^ (m + 1)) (2 * (r * (2 * addBitCost (4 * p')))) _ (fun v1 => by
          simp only [BitCostM.bind_snd, computableNegacyclicDirectWithCost_snd]
          rw [BitCostM.ofFnM_snd_const r (2 * addBitCost (4 * p')) _ (fun _ => rfl)]
          ring),
        pow_succ]
    ring

/-- **Call-Site True Operand Bit-Width Coverage & `mulBitCost` Scaling Theorem
(`programCost_callsite_operand_widths_covered`, `[MS]` §§3.2, 5.2 & 7.2)**:
For any step parameters `p, K : ℕ` with `8 ≤ p` and `p' = pChild p K`:
1. The pre-twist (`gPreTwistU`) and post-twist (`gMulScaled`) operand bit-widths (up to `p + 4 * p' + 4`
   bits on `uRaw` and `4 * p'` bits on `Q`) are bounded by `6 * p'`,
2. The forward/Nyquist/backward recurrence (`zPart`, `zHom`) unshifted product bit-widths
   (`6 * p' + 4 * p'`) are bounded by `10 * p'`,
3. The boundary solve (`Z0`, `gCombineQuantize`) unshifted product bit-widths
   (`10 * p' + 10 * p' + 2 * p'`) are bounded by `22 * p'`, and
4. `mulBitCost` at these three call-site widths is bounded by constant multiples (`18`, `27`, `96`)
   of `mulBitCost (4 * p')`. -/
theorem programCost_callsite_operand_widths_covered (p K : ℕ) :
    let p' := pChild p K
    p + 4 * p' + 4 ≤ 6 * p' ∧
    6 * p' + 4 * p' ≤ 10 * p' ∧
    10 * p' + 10 * p' + 2 * p' ≤ 22 * p' ∧
    mulBitCost (6 * p') ≤ 18 * mulBitCost (4 * p') ∧
    mulBitCost (10 * p') ≤ 27 * mulBitCost (4 * p') ∧
    mulBitCost (22 * p') ≤ 96 * mulBitCost (4 * p') := by
  dsimp only
  have hp' : p + 4 ≤ pChild p K := by unfold pChild pWork; omega
  have hmul := mulBitCost_raw_temporaries_le_four_mul_pChild (pChild p K)
  refine ⟨by omega, by omega, by omega, hmul.1, hmul.2.1, hmul.2.2⟩

@[simp]
theorem runMultiTapeTransposeFullSteps_fst {α : Type*} [Zero α] (m r : ℕ) (tape : ℕ → α) :
    (runMultiTapeTransposeFullSteps m r tape).1 = runMultiTapeTranspose m r tape := by
  induction m generalizing tape with
  | zero => rfl
  | succ m ih =>
    dsimp only [runMultiTapeTransposeFullSteps, runMultiTapeTranspose]
    rw [ih, ih]

@[simp]
theorem runMultiTapeAffineOddRouteFullSteps_fst {α : Type*} [Zero α] (m w b : ℕ) (col : ℕ → α) :
    (runMultiTapeAffineOddRouteFullSteps m w b col).1 = runMultiTapeAffineOddRoute m w b col := by
  induction m generalizing b col with
  | zero => rfl
  | succ m ih =>
    dsimp only [runMultiTapeAffineOddRouteFullSteps, runMultiTapeAffineOddRoute]
    rw [ih, ih]

theorem sumArrayCosts_ofFn_le_const {α : Type*} (n : ℕ) (f : Fin n → α × ℕ) (c : ℕ)
    (hc : ∀ i (hi : i < n), (f ⟨i, hi⟩).2 ≤ c) :
    sumArrayCosts (Array.ofFn f) ≤ n * c := by
  rw [sumArrayCosts_ofFn_eq_sum n f (fun i => if hi : i < n then (f ⟨i, hi⟩).2 else 0)
    (fun i hi => by simp [hi])]
  calc ∑ i ∈ Finset.range n, (if hi : i < n then (f ⟨i, hi⟩).2 else 0)
      ≤ ∑ _i ∈ Finset.range n, c := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi_lt : i < n := Finset.mem_range.mp hi
        rw [dif_pos hi_lt]
        exact hc i hi_lt
    _ = n * c := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem sumArrayCosts_ofFn_cast_le_const {α : Type*} (n : ℕ) (f : Fin n → α × ℕ) (B : ℝ)
    (hB : ∀ i (hi : i < n), (((f ⟨i, hi⟩).2 : ℕ) : ℝ) ≤ B) :
    ((sumArrayCosts (Array.ofFn f) : ℕ) : ℝ) ≤ (n : ℝ) * B := by
  rw [sumArrayCosts_ofFn_eq_sum n f (fun i => if hi : i < n then (f ⟨i, hi⟩).2 else 0)
    (fun i hi => by simp [hi])]
  push_cast
  calc ∑ i ∈ Finset.range n, (((if hi : i < n then (f ⟨i, hi⟩).2 else 0) : ℕ) : ℝ)
      ≤ ∑ _i ∈ Finset.range n, B := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi_lt : i < n := Finset.mem_range.mp hi
        rw [dif_pos hi_lt]
        exact hB i hi_lt
    _ = (n : ℝ) * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Program-cost-accumulating builder for `zPartFwdQuantized` (`buildComputableZPartFwdWithProgramCost`):
executes `costedGRatioQuantize q w` at each step in `Monad BitCostM` and accumulates the exact primitive bit-operation cost. -/
def buildComputableZPartFwdWithProgramCost
    (q w : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) : ℕ → BitCostM (Array (ℤ × ℤ))
  | 0 => pure #[(0, 0)]
  | n + 1 => do
    let prevArr ← buildComputableZPartFwdWithProgramCost q w c0 c1 Y n
    let prev := read1D prevArr n
    let y_next := read1D Y (n + 1)
    let stepVal ← costedGRatioQuantize q w y_next c1 prev c0 (0, 0) (0, 0)
    pure (prevArr.push stepVal)

@[simp]
theorem buildComputableZPartFwdWithProgramCost_fst
    (q w : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) :
    (buildComputableZPartFwdWithProgramCost q w c0 c1 Y n).1 =
      buildComputableZPartFwdExact q c0 c1 Y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [buildComputableZPartFwdWithProgramCost, buildComputableZPartFwdExact,
      Bind.bind, Pure.pure, costedGRatioQuantize]
    rw [ih]

@[simp]
theorem buildComputableZPartFwdWithProgramCost_snd
    (q w : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) :
    (buildComputableZPartFwdWithProgramCost q w c0 c1 Y n).2 =
      n * (6 * mulBitCost w + 6 * addBitCost w) := by
  induction n with
  | zero => simp [buildComputableZPartFwdWithProgramCost, Pure.pure]
  | succ n ih =>
    dsimp only [buildComputableZPartFwdWithProgramCost, Bind.bind, Pure.pure, costedGRatioQuantize]
    rw [ih, computableMulBitCost_eq]
    ring

/-- Program-cost-accumulating builder for `zHomFwdQuantized` (`buildComputableZHomFwdWithProgramCost`):
executes `costedGRatioQuantize q w` at each step in `Monad BitCostM` and accumulates the exact primitive bit-operation cost. -/
def buildComputableZHomFwdWithProgramCost
    (q w : ℕ) (c0 c1 : ℤ × ℤ) : ℕ → BitCostM (Array (ℤ × ℤ))
  | 0 => costedZHomInit q
  | n + 1 => do
    let prevArr ← buildComputableZHomFwdWithProgramCost q w c0 c1 n
    let prev := read1D prevArr n
    let stepVal ← costedGRatioQuantize q w (0, 0) c1 prev c0 (0, 0) (0, 0)
    pure (prevArr.push stepVal)

@[simp]
theorem buildComputableZHomFwdWithProgramCost_fst
    (q w : ℕ) (c0 c1 : ℤ × ℤ) (n : ℕ) :
    (buildComputableZHomFwdWithProgramCost q w c0 c1 n).1 =
      buildComputableZHomFwdExact q c0 c1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [buildComputableZHomFwdWithProgramCost, buildComputableZHomFwdExact,
      Bind.bind, Pure.pure, costedGRatioQuantize]
    rw [ih]

@[simp]
theorem buildComputableZHomFwdWithProgramCost_snd
    (q w : ℕ) (c0 c1 : ℤ × ℤ) (n : ℕ) :
    (buildComputableZHomFwdWithProgramCost q w c0 c1 n).2 =
      n * (6 * mulBitCost w + 6 * addBitCost w) := by
  induction n with
  | zero => simp [buildComputableZHomFwdWithProgramCost, costedZHomInit]
  | succ n ih =>
    dsimp only [buildComputableZHomFwdWithProgramCost, Bind.bind, Pure.pure, costedGRatioQuantize]
    rw [ih, computableMulBitCost_eq]
    ring

/-- Program-cost-accumulating forward cyclic bidiagonal column solver
(`computableSolveBidiagonalFwdWithProgramCost`, `[MS]` §§5.1–5.2):
wires the recurrence builders `buildComputableZPartFwdWithProgramCost` and
`buildComputableZHomFwdWithProgramCost` (at true width `10 * p'`), the boundary solve `Z0`
(at true width `22 * p'`), and the `t1`-element costed output scan `runSequentialScanCostedSteps`
calling `costedGCombineQuantize q (22 * p')` (summing `.2` via `sumArrayCosts`) plus
`stOut.2.1 * addBitCost (8 * p')` directly into `Monad BitCostM`. -/
def computableSolveBidiagonalFwdWithProgramCost
    (q p' t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) : BitCostM (Array (ℤ × ℤ)) := do
  let zPartArr ← buildComputableZPartFwdWithProgramCost q (10 * p') c0 c1 Y (t1 - 1)
  let zHomArr ← buildComputableZHomFwdWithProgramCost q (10 * p') c0 c1 (t1 - 1)
  let Z0 ← costedGRatioQuantize q (22 * p') (read1D Y 0) c1
    (read1D zPartArr (t1 - 1)) c0 c1 (read1D zHomArr (t1 - 1))
  let stOut := runSequentialScanCostedSteps (fun u1 =>
    costedGCombineQuantize q (22 * p') (read1D zPartArr u1) Z0 (read1D zHomArr u1)) t1
  BitCostM.tick (stOut.2.2 + stOut.2.1 * addBitCost (8 * p'))
  pure stOut.1

@[simp]
theorem computableSolveBidiagonalFwdWithProgramCost_fst
    (q p' t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    (computableSolveBidiagonalFwdWithProgramCost q p' t1 c0 c1 Y).1 =
      computableSolveBidiagonalFwdExact q t1 c0 c1 Y := by
  dsimp only [computableSolveBidiagonalFwdWithProgramCost, computableSolveBidiagonalFwdExact,
    computableSolveBidiagonalFwdExactWithSteps, runSequentialScanCostedSteps,
    Bind.bind, Pure.pure, BitCostM.tick, costedGRatioQuantize, costedGCombineQuantize]
  rw [buildComputableZPartFwdWithProgramCost_fst, buildComputableZHomFwdWithProgramCost_fst]

theorem computableSolveBidiagonalFwdWithProgramCost_snd_eq
    (q p' t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    (computableSolveBidiagonalFwdWithProgramCost q p' t1 c0 c1 Y).2 =
      (t1 - 1) * (6 * mulBitCost (10 * p') + 6 * addBitCost (10 * p')) +
      (t1 - 1) * (6 * mulBitCost (10 * p') + 6 * addBitCost (10 * p')) +
      (6 * mulBitCost (22 * p') + 6 * addBitCost (22 * p')) +
      t1 * (4 * mulBitCost (22 * p') + 4 * addBitCost (22 * p')) +
      t1 * addBitCost (8 * p') := by
  dsimp only [computableSolveBidiagonalFwdWithProgramCost, Bind.bind, Pure.pure,
    BitCostM.tick, costedGRatioQuantize]
  have hcomb_cost :
      (runSequentialScanCostedSteps (fun u1 =>
        costedGCombineQuantize q (22 * p')
          (read1D (buildComputableZPartFwdWithProgramCost q (10 * p') c0 c1 Y (t1 - 1)).1 u1)
          (gRatioQuantize q (read1D Y 0) c1
            (read1D (buildComputableZPartFwdWithProgramCost q (10 * p') c0 c1 Y (t1 - 1)).1 (t1 - 1))
            c0 c1 (read1D (buildComputableZHomFwdWithProgramCost q (10 * p') c0 c1 (t1 - 1)).1 (t1 - 1)))
          (read1D (buildComputableZHomFwdWithProgramCost q (10 * p') c0 c1 (t1 - 1)).1 u1)) t1).2.2 =
      t1 * (4 * mulBitCost (22 * p') + 4 * addBitCost (22 * p')) := by
    refine runSequentialScanCostedSteps_cost_const _ t1 _ (fun u1 _ => ?_)
    dsimp [costedGCombineQuantize]
    rw [computableMulBitCost_eq]
  rw [buildComputableZPartFwdWithProgramCost_snd, buildComputableZHomFwdWithProgramCost_snd,
      hcomb_cost, runSequentialScanCostedSteps_steps, computableMulBitCost_eq]
  ring

theorem computableSolveBidiagonalFwdWithProgramCost_snd_le
    (q p' t1 : ℕ) (ht1 : 1 ≤ t1) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    (computableSolveBidiagonalFwdWithProgramCost q p' t1 c0 c1 Y).2 ≤
      81 * t1 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')) := by
  rw [computableSolveBidiagonalFwdWithProgramCost_snd_eq]
  obtain ⟨_, h10, h22⟩ := mulBitCost_raw_temporaries_le_four_mul_pChild p'
  have ht1_sub : t1 - 1 ≤ t1 := Nat.sub_le t1 1
  have hpart_le :
      (t1 - 1) * (6 * mulBitCost (10 * p') + 6 * addBitCost (10 * p')) ≤
        t1 * (162 * mulBitCost (4 * p') + 15 * addBitCost (4 * p')) := by
    have hstep : 6 * mulBitCost (10 * p') + 6 * addBitCost (10 * p') ≤
        162 * mulBitCost (4 * p') + 15 * addBitCost (4 * p') := by
      dsimp [addBitCost]
      omega
    exact Nat.mul_le_mul ht1_sub hstep
  have hZ0_le :
      6 * mulBitCost (22 * p') + 6 * addBitCost (22 * p') ≤
        t1 * (576 * mulBitCost (4 * p') + 36 * addBitCost (4 * p')) := by
    have hstep : 6 * mulBitCost (22 * p') + 6 * addBitCost (22 * p') ≤
        1 * (576 * mulBitCost (4 * p') + 36 * addBitCost (4 * p')) := by
      dsimp [addBitCost]
      omega
    exact hstep.trans (Nat.mul_le_mul_right _ ht1)
  have hcomb_le :
      t1 * (4 * mulBitCost (22 * p') + 4 * addBitCost (22 * p')) + t1 * addBitCost (8 * p') ≤
        t1 * (384 * mulBitCost (4 * p') + 26 * addBitCost (4 * p')) := by
    have hstep : 4 * mulBitCost (22 * p') + 4 * addBitCost (22 * p') + addBitCost (8 * p') ≤
        384 * mulBitCost (4 * p') + 26 * addBitCost (4 * p') := by
      dsimp [addBitCost]
      omega
    calc t1 * (4 * mulBitCost (22 * p') + 4 * addBitCost (22 * p')) + t1 * addBitCost (8 * p')
        = t1 * (4 * mulBitCost (22 * p') + 4 * addBitCost (22 * p') + addBitCost (8 * p')) := by ring
      _ ≤ t1 * (384 * mulBitCost (4 * p') + 26 * addBitCost (4 * p')) := Nat.mul_le_mul_left t1 hstep
  calc (t1 - 1) * (6 * mulBitCost (10 * p') + 6 * addBitCost (10 * p')) +
        (t1 - 1) * (6 * mulBitCost (10 * p') + 6 * addBitCost (10 * p')) +
        (6 * mulBitCost (22 * p') + 6 * addBitCost (22 * p')) +
        t1 * (4 * mulBitCost (22 * p') + 4 * addBitCost (22 * p')) +
        t1 * addBitCost (8 * p')
      ≤ t1 * (162 * mulBitCost (4 * p') + 15 * addBitCost (4 * p')) +
        t1 * (162 * mulBitCost (4 * p') + 15 * addBitCost (4 * p')) +
        t1 * (576 * mulBitCost (4 * p') + 36 * addBitCost (4 * p')) +
        t1 * (384 * mulBitCost (4 * p') + 26 * addBitCost (4 * p')) := by omega
    _ = t1 * (1284 * mulBitCost (4 * p') + 92 * addBitCost (4 * p')) := by ring
    _ ≤ t1 * (1296 * mulBitCost (4 * p') + 1296 * addBitCost (4 * p')) := by
        refine Nat.mul_le_mul_left t1 ?_
        omega
    _ = 81 * t1 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')) := by ring

/-- Program-cost-accumulating backward cyclic bidiagonal column solver
(`computableSolveBidiagonalBwdWithProgramCost`, `[MS]` §§5.1–5.2):
counts all forward-seek and backward-sweep steps in `stIn := runBwdRevSteps t1 (read1D Y) t1`
and `stOut := runReverseSteps t1 (read1D fwdArr) t1` (`(stIn.steps + stOut.steps) * addBitCost (8 * p')`)
together with the full internal forward-solver cost from `computableSolveBidiagonalFwdWithProgramCost`
inside `Monad BitCostM`. -/
def computableSolveBidiagonalBwdWithProgramCost
    (q p' t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) : BitCostM (Array (ℤ × ℤ)) := do
  let stIn := runBwdRevSteps t1 (read1D Y) t1
  let fwdArr ← computableSolveBidiagonalFwdWithProgramCost q p' t1 c1 c0 stIn.outTape
  let stOut := runReverseSteps t1 (read1D fwdArr) t1
  BitCostM.tick ((stIn.steps + stOut.steps) * addBitCost (8 * p'))
  pure stOut.outTape

@[simp]
theorem computableSolveBidiagonalBwdWithProgramCost_fst
    (q p' t1 : ℕ) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    (computableSolveBidiagonalBwdWithProgramCost q p' t1 c0 c1 Y).1 =
      computableSolveBidiagonalBwdExact q t1 c0 c1 Y := by
  dsimp only [computableSolveBidiagonalBwdWithProgramCost, computableSolveBidiagonalBwdExact,
    computableSolveBidiagonalBwdExactWithSteps, Bind.bind, Pure.pure, BitCostM.tick]
  rw [computableSolveBidiagonalFwdWithProgramCost_fst]

theorem computableSolveBidiagonalBwdWithProgramCost_snd_le
    (q p' t1 : ℕ) (ht1 : 1 ≤ t1) (c0 c1 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) :
    (computableSolveBidiagonalBwdWithProgramCost q p' t1 c0 c1 Y).2 ≤
      81 * t1 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')) := by
  dsimp only [computableSolveBidiagonalBwdWithProgramCost, Bind.bind, Pure.pure, BitCostM.tick]
  set stIn := runBwdRevSteps t1 (read1D Y) t1
  set fwdRes := computableSolveBidiagonalFwdWithProgramCost q p' t1 c1 c0 stIn.outTape
  set stOut := runReverseSteps t1 (read1D fwdRes.1) t1
  have hrev_steps : stIn.steps + stOut.steps ≤ 4 * t1 := by
    dsimp [stIn, stOut]
    rw [runBwdRevSteps_steps, runReverseSteps_steps]
    split_ifs <;> omega
  have hrev_cost : (stIn.steps + stOut.steps) * addBitCost (8 * p') ≤ t1 * (8 * addBitCost (4 * p')) := by
    calc (stIn.steps + stOut.steps) * addBitCost (8 * p')
        ≤ (4 * t1) * addBitCost (8 * p') := Nat.mul_le_mul_right _ hrev_steps
      _ = t1 * (8 * addBitCost (4 * p')) := by
          dsimp [addBitCost]
          ring
  have hfwd_tight :
      fwdRes.2 ≤ t1 * (1284 * mulBitCost (4 * p') + 92 * addBitCost (4 * p')) := by
    dsimp only [fwdRes]
    rw [computableSolveBidiagonalFwdWithProgramCost_snd_eq]
    obtain ⟨_, h10, h22⟩ := mulBitCost_raw_temporaries_le_four_mul_pChild p'
    have ht1_sub : t1 - 1 ≤ t1 := Nat.sub_le t1 1
    have hpart_le :
        (t1 - 1) * (6 * mulBitCost (10 * p') + 6 * addBitCost (10 * p')) ≤
          t1 * (162 * mulBitCost (4 * p') + 15 * addBitCost (4 * p')) := by
      refine Nat.mul_le_mul ht1_sub ?_
      dsimp [addBitCost]; omega
    have hZ0_le :
        6 * mulBitCost (22 * p') + 6 * addBitCost (22 * p') ≤
          t1 * (576 * mulBitCost (4 * p') + 36 * addBitCost (4 * p')) := by
      have hstep : 6 * mulBitCost (22 * p') + 6 * addBitCost (22 * p') ≤
          1 * (576 * mulBitCost (4 * p') + 36 * addBitCost (4 * p')) := by
        dsimp [addBitCost]; omega
      exact hstep.trans (Nat.mul_le_mul_right _ ht1)
    have hcomb_le :
        t1 * (4 * mulBitCost (22 * p') + 4 * addBitCost (22 * p')) + t1 * addBitCost (8 * p') ≤
          t1 * (384 * mulBitCost (4 * p') + 26 * addBitCost (4 * p')) := by
      have hstep : 4 * mulBitCost (22 * p') + 4 * addBitCost (22 * p') + addBitCost (8 * p') ≤
          384 * mulBitCost (4 * p') + 26 * addBitCost (4 * p') := by
        dsimp [addBitCost]; omega
      calc t1 * (4 * mulBitCost (22 * p') + 4 * addBitCost (22 * p')) + t1 * addBitCost (8 * p')
          = t1 * (4 * mulBitCost (22 * p') + 4 * addBitCost (22 * p') + addBitCost (8 * p')) := by ring
        _ ≤ t1 * (384 * mulBitCost (4 * p') + 26 * addBitCost (4 * p')) := Nat.mul_le_mul_left t1 hstep
    calc (t1 - 1) * (6 * mulBitCost (10 * p') + 6 * addBitCost (10 * p')) +
          (t1 - 1) * (6 * mulBitCost (10 * p') + 6 * addBitCost (10 * p')) +
          (6 * mulBitCost (22 * p') + 6 * addBitCost (22 * p')) +
          t1 * (4 * mulBitCost (22 * p') + 4 * addBitCost (22 * p')) +
          t1 * addBitCost (8 * p')
        ≤ t1 * (162 * mulBitCost (4 * p') + 15 * addBitCost (4 * p')) +
          t1 * (162 * mulBitCost (4 * p') + 15 * addBitCost (4 * p')) +
          t1 * (576 * mulBitCost (4 * p') + 36 * addBitCost (4 * p')) +
          t1 * (384 * mulBitCost (4 * p') + 26 * addBitCost (4 * p')) := by omega
      _ = t1 * (1284 * mulBitCost (4 * p') + 92 * addBitCost (4 * p')) := by ring
  calc fwdRes.2 + ((stIn.steps + stOut.steps) * addBitCost (8 * p') + 0)
      = fwdRes.2 + (stIn.steps + stOut.steps) * addBitCost (8 * p') := by ring
    _ ≤ t1 * (1284 * mulBitCost (4 * p') + 92 * addBitCost (4 * p')) +
          t1 * (8 * addBitCost (4 * p')) := Nat.add_le_add hfwd_tight hrev_cost
    _ = t1 * (1284 * mulBitCost (4 * p') + 100 * addBitCost (4 * p')) := by ring
    _ ≤ t1 * (1296 * mulBitCost (4 * p') + 1296 * addBitCost (4 * p')) := by
        refine Nat.mul_le_mul_left t1 ?_
        omega
    _ = 81 * t1 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')) := by ring

/-- Program-cost-accumulating builder for `zPartNyqQuantized` (`buildComputableZPartNyqWithProgramCost`):
executes `costedGNyqStepQuantize q w` at each step in `Monad BitCostM` and accumulates the primitive bit-operation cost. -/
def buildComputableZPartNyqWithProgramCost
    (q w : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) : ℕ → BitCostM (Array (ℤ × ℤ))
  | 0 => pure #[(0, 0)]
  | n + 1 => do
    let prevArr ← buildComputableZPartNyqWithProgramCost q w c0 Y n
    let prev := read1D prevArr n
    let y_next := read1D Y (n + 1)
    let stepVal ← costedGNyqStepQuantize q w c0 y_next prev
    pure (prevArr.push stepVal)

@[simp]
theorem buildComputableZPartNyqWithProgramCost_fst
    (q w : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) :
    (buildComputableZPartNyqWithProgramCost q w c0 Y n).1 =
      buildComputableZPartNyqExact q c0 Y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [buildComputableZPartNyqWithProgramCost, buildComputableZPartNyqExact,
      Bind.bind, Pure.pure, costedGNyqStepQuantize]
    rw [ih]

@[simp]
theorem buildComputableZPartNyqWithProgramCost_snd
    (q w : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (n : ℕ) :
    (buildComputableZPartNyqWithProgramCost q w c0 Y n).2 =
      n * (6 * mulBitCost w + 6 * addBitCost w) := by
  induction n with
  | zero => simp [buildComputableZPartNyqWithProgramCost, Pure.pure]
  | succ n ih =>
    dsimp only [buildComputableZPartNyqWithProgramCost, Bind.bind, Pure.pure, costedGNyqStepQuantize]
    rw [ih, computableMulBitCost_eq]
    ring

/-- Costed structural-recursion Gaussian-integer sum over `0 .. n - 1` (`sumRangePairWithCost`):
at each step `k`, executes `f k` and `costedGAdd w` in `Monad BitCostM`, computing the exact same
Gaussian-integer sum as `sumRangePair` while charging `2 * addBitCost w` per addition in a single pass. -/
def sumRangePairWithCost (w : ℕ) (f : ℕ → BitCostM (ℤ × ℤ)) : ℕ → BitCostM (ℤ × ℤ)
  | 0 => pure (0, 0)
  | n + 1 => do
    let acc ← sumRangePairWithCost w f n
    let v ← f n
    costedGAdd w acc v

@[simp]
theorem sumRangePairWithCost_fst (w : ℕ) (f : ℕ → BitCostM (ℤ × ℤ)) (n : ℕ) :
    (sumRangePairWithCost w f n).1 = sumRangePair (fun k => (f k).1) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [sumRangePairWithCost, sumRangePair, Bind.bind, Pure.pure, costedGAdd]
    rw [ih]

theorem sumRangePairWithCost_snd_const (w : ℕ) (f : ℕ → BitCostM (ℤ × ℤ)) (n c : ℕ)
    (hc : ∀ k < n, (f k).2 = c) :
    (sumRangePairWithCost w f n).2 = n * (c + 2 * addBitCost w) := by
  induction n with
  | zero => simp [sumRangePairWithCost, Pure.pure]
  | succ n ih =>
    dsimp only [sumRangePairWithCost, Bind.bind, Pure.pure, costedGAdd]
    rw [ih (fun k hk => hc k (Nat.lt_succ_of_lt hk)), hc n (Nat.lt_succ_self n)]
    ring

/-- Costed Nyquist midpoint alternating-sum rational scaling (`costedGNyqAltSumScale`, `[MS]` §§5.1–5.2):
scales `(-altSum.2, altSum.1)` by `2 ^ (q + 2) / (r * 2 ^ (p_in + 2))` via `costedGQuantizeRat w`. -/
def costedGNyqAltSumScale (p_in q w r : ℕ) (altSum : ℤ × ℤ) : BitCostM (ℤ × ℤ) :=
  let S_out : ℤ := ((2 ^ (q + 2) : ℕ) : ℤ)
  let den : ℤ := (r : ℤ) * ((2 ^ (p_in + 2) : ℕ) : ℤ)
  costedGQuantizeRat w (-altSum.2 * S_out) (altSum.1 * S_out) den

/-- Program-cost-accumulating Nyquist column solver (`computableSolveNyquistWithProgramCost`, `[MS]` §§5.1–5.2):
executes `buildComputableZPartNyqWithProgramCost` (at width `10 * p'`), the single-pass `t1`-term
costed alternating sum `sumRangePairWithCost (4 * p')` (eliminating duplicate `altPartScan`/`alt_part`),
`costedGSub (4 * p')`, `costedGQuantizeRat (10 * p')`, and the `t1`-element costed output scan `stOut`
(`runSequentialScanCostedSteps`) inside `Monad BitCostM`. -/
def computableSolveNyquistWithProgramCost
    (q p' t1 : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ) : BitCostM (Array (ℤ × ℤ)) := do
  let zPartArr ← buildComputableZPartNyqWithProgramCost q (10 * p') c0 Y (t1 - 1)
  let alt_part ← sumRangePairWithCost (4 * p') (fun v => costedGAltTerm v (read1D zPartArr v)) t1
  let diff ← costedGSub (4 * p') alt_q alt_part
  let diffRat ← costedGQuantizeRat (10 * p') diff.1 diff.2 (t1 : ℤ)
  let stOut := runSequentialScanCostedSteps (fun u1 => do
    let term ← costedGAltTerm u1 diffRat
    let comb ← costedGAdd (4 * p') (read1D zPartArr u1) term
    costedGRescale q q (4 * p') comb) t1
  BitCostM.tick (stOut.2.2 + stOut.2.1 * addBitCost (8 * p'))
  pure stOut.1

@[simp]
theorem computableSolveNyquistWithProgramCost_fst
    (q p' t1 : ℕ) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ) :
    (computableSolveNyquistWithProgramCost q p' t1 c0 Y alt_q).1 =
      computableSolveNyquistExact q t1 c0 Y alt_q := by
  dsimp only [computableSolveNyquistWithProgramCost, computableSolveNyquistExact,
    computableSolveNyquistExactWithSteps, runSequentialScanCostedSteps,
    Bind.bind, Pure.pure, BitCostM.tick, costedGAltTerm, costedGSub, costedGAdd,
    costedGQuantizeRat, costedGRescale]
  rw [buildComputableZPartNyqWithProgramCost_fst, sumRangePairWithCost_fst]
  rfl

theorem computableSolveNyquistWithProgramCost_snd_le
    (q p' t1 : ℕ) (ht1 : 1 ≤ t1) (c0 : ℤ × ℤ) (Y : Array (ℤ × ℤ)) (alt_q : ℤ × ℤ) :
    (computableSolveNyquistWithProgramCost q p' t1 c0 Y alt_q).2 ≤
      81 * t1 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')) := by
  dsimp only [computableSolveNyquistWithProgramCost, Bind.bind, BitCostM.tick,
    costedGSub, gSub, costedGQuantizeRat]
  rw [BitCostM.pure_snd]
  have halt_cost :
      (sumRangePairWithCost (4 * p')
        (fun v => costedGAltTerm v (read1D (buildComputableZPartNyqWithProgramCost q (10 * p') c0 Y (t1 - 1)).1 v))
        t1).2 =
      t1 * (2 * addBitCost (4 * p')) := by
    simpa using sumRangePairWithCost_snd_const (4 * p') _ t1 0 (fun _ _ => rfl)
  rw [buildComputableZPartNyqWithProgramCost_snd, halt_cost,
      runSequentialScanCostedSteps_cost_const _ t1 (4 * addBitCost (4 * p'))
        (fun _ _ => by dsimp [Bind.bind, costedGAltTerm, costedGAdd, costedGRescale]; ring),
      runSequentialScanCostedSteps_steps, computableMulBitCost_eq]
  obtain ⟨_, h10, _⟩ := mulBitCost_raw_temporaries_le_four_mul_pChild p'
  have ht1_sub : t1 - 1 ≤ t1 := Nat.sub_le t1 1
  have hpart_le :
      (t1 - 1) * (6 * mulBitCost (10 * p') + 6 * addBitCost (10 * p')) ≤
        t1 * (162 * mulBitCost (4 * p') + 15 * addBitCost (4 * p')) := by
    refine Nat.mul_le_mul ht1_sub ?_
    dsimp [addBitCost]; omega
  have hdiff_le :
      2 * addBitCost (4 * p') + (4 * mulBitCost (10 * p') + 4 * addBitCost (10 * p')) ≤
        t1 * (108 * mulBitCost (4 * p') + 12 * addBitCost (4 * p')) := by
    have hstep : 2 * addBitCost (4 * p') + (4 * mulBitCost (10 * p') + 4 * addBitCost (10 * p')) ≤
        1 * (108 * mulBitCost (4 * p') + 12 * addBitCost (4 * p')) := by
      dsimp [addBitCost]; omega
    exact hstep.trans (Nat.mul_le_mul_right _ ht1)
  have hout_eq :
      t1 * (2 * addBitCost (4 * p')) + (t1 * (4 * addBitCost (4 * p')) + t1 * addBitCost (8 * p') + 0) =
        t1 * (8 * addBitCost (4 * p')) := by
    dsimp [addBitCost]
    ring
  calc (t1 - 1) * (6 * mulBitCost (10 * p') + 6 * addBitCost (10 * p')) +
        (t1 * (2 * addBitCost (4 * p')) +
          (2 * addBitCost (4 * p') +
            (4 * mulBitCost (10 * p') + 4 * addBitCost (10 * p') +
              (t1 * (4 * addBitCost (4 * p')) + t1 * addBitCost (8 * p') + 0))))
      = (t1 - 1) * (6 * mulBitCost (10 * p') + 6 * addBitCost (10 * p')) +
        (2 * addBitCost (4 * p') + (4 * mulBitCost (10 * p') + 4 * addBitCost (10 * p'))) +
        (t1 * (2 * addBitCost (4 * p')) + (t1 * (4 * addBitCost (4 * p')) + t1 * addBitCost (8 * p') + 0)) := by ring
    _ ≤ t1 * (162 * mulBitCost (4 * p') + 15 * addBitCost (4 * p')) +
        t1 * (108 * mulBitCost (4 * p') + 12 * addBitCost (4 * p')) +
        t1 * (8 * addBitCost (4 * p')) := by linarith [hpart_le, hdiff_le, hout_eq]
    _ = t1 * (270 * mulBitCost (4 * p') + 35 * addBitCost (4 * p')) := by ring
    _ ≤ t1 * (1296 * mulBitCost (4 * p') + 1296 * addBitCost (4 * p')) := by
        refine Nat.mul_le_mul_left t1 ?_
        omega
    _ = 81 * t1 * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p')) := by ring

/-- Program-cost-accumulating contiguous midpoint-row alternating sum
(`computableNyquistAltSumContiguousWithProgramCost`, `[MS]` §§5.1–5.2):
accumulates the `r`-element alternating sum in a single pass via `sumRangePairWithCost (4 * p')`
(eliminating duplicate `altScan`/`altSum`) and scales via `costedGNyqAltSumScale p_in q (6 * p') r`. -/
def computableNyquistAltSumContiguousWithProgramCost
    (p_in q p' r : ℕ) (xMidRow : Array (ℤ × ℤ)) : BitCostM (ℤ × ℤ) := do
  let altSum ← sumRangePairWithCost (4 * p') (fun j2 => costedGAltTerm j2 (read1D xMidRow j2)) r
  costedGNyqAltSumScale p_in q (6 * p') r altSum

@[simp]
theorem computableNyquistAltSumContiguousWithProgramCost_fst
    (p_in q p' r : ℕ) (xMidRow : Array (ℤ × ℤ)) :
    (computableNyquistAltSumContiguousWithProgramCost p_in q p' r xMidRow).1 =
      computableNyquistAltSumContiguous p_in q r xMidRow := by
  dsimp only [computableNyquistAltSumContiguousWithProgramCost, computableNyquistAltSumContiguous,
    Bind.bind, Pure.pure, costedGAltTerm, costedGNyqAltSumScale, costedGQuantizeRat]
  rw [sumRangePairWithCost_fst]

theorem computableNyquistAltSumContiguousWithProgramCost_snd_le
    (p_in q p' t1 r : ℕ) (ht1 : 1 ≤ t1) (hr : 1 ≤ r) (xMidRow : Array (ℤ × ℤ)) :
    (computableNyquistAltSumContiguousWithProgramCost p_in q p' r xMidRow).2 ≤
      5 * (t1 * r * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p'))) := by
  dsimp only [computableNyquistAltSumContiguousWithProgramCost, Bind.bind,
    costedGNyqAltSumScale, costedGQuantizeRat]
  have halt_cost :
      (sumRangePairWithCost (4 * p') (fun j2 => costedGAltTerm j2 (read1D xMidRow j2)) r).2 =
      r * (2 * addBitCost (4 * p')) := by
    simpa using sumRangePairWithCost_snd_const (4 * p') _ r 0 (fun _ _ => rfl)
  rw [halt_cost, computableMulBitCost_eq]
  obtain ⟨h6, _, _⟩ := mulBitCost_raw_temporaries_le_four_mul_pChild p'
  have hr_le : r ≤ t1 * r := Nat.le_mul_of_pos_left r ht1
  have h1_le : 1 ≤ t1 * r := Nat.mul_pos ht1 hr
  have hterm1 : r * (2 * addBitCost (4 * p')) ≤ (t1 * r) * (2 * addBitCost (4 * p')) :=
    Nat.mul_le_mul_right _ hr_le
  have hterm2 :
      4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p') ≤
        (t1 * r) * (72 * mulBitCost (4 * p') + 6 * addBitCost (4 * p')) := by
    have hstep : 4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p') ≤
        1 * (72 * mulBitCost (4 * p') + 6 * addBitCost (4 * p')) := by
      dsimp [addBitCost]; omega
    exact hstep.trans (Nat.mul_le_mul_right _ h1_le)
  calc r * (2 * addBitCost (4 * p')) + (4 * mulBitCost (6 * p') + 4 * addBitCost (6 * p'))
      ≤ (t1 * r) * (2 * addBitCost (4 * p')) +
          (t1 * r) * (72 * mulBitCost (4 * p') + 6 * addBitCost (4 * p')) := by omega
    _ = (t1 * r) * (72 * mulBitCost (4 * p') + 8 * addBitCost (4 * p')) := by ring
    _ ≤ (t1 * r) * (80 * mulBitCost (4 * p') + 80 * addBitCost (4 * p')) := by
        refine Nat.mul_le_mul_left (t1 * r) ?_
        omega
    _ = 5 * (t1 * r * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p'))) := by ring

/-- Costed real input block extractor (`computableSpreadRowBlockReContiguousWithCost`, `[MS]` §6.2):
maps `costedGQuantizeCoordToScale p_in q w` over `List.range W_eff` in a single pass via
`BitCostM.mapListM` (eliminating duplicate `vals`/`costPairs` passes). -/
def computableSpreadRowBlockReContiguousWithCost
    (p_in q w m1 r : ℕ) (xRow : Array (ℤ × ℤ)) (b : ℕ) : BitCostM (List ℤ) :=
  let W_eff := effectiveFilterWidth m1 r
  BitCostM.mapListM (fun a =>
    if b * W_eff + a < r then
      costedGQuantizeCoordToScale p_in q w (read1D xRow (b * W_eff + a)).1
    else do
      BitCostM.tick (2 * addBitCost w)
      pure 0) (List.range W_eff)

/-- Costed imaginary input block extractor (`computableSpreadRowBlockImContiguousWithCost`, `[MS]` §6.2):
maps `costedGQuantizeCoordToScale p_in q w` over `List.range W_eff` in a single pass via
`BitCostM.mapListM` (eliminating duplicate `vals`/`costPairs` passes). -/
def computableSpreadRowBlockImContiguousWithCost
    (p_in q w m1 r : ℕ) (xRow : Array (ℤ × ℤ)) (b : ℕ) : BitCostM (List ℤ) :=
  let W_eff := effectiveFilterWidth m1 r
  BitCostM.mapListM (fun a =>
    if b * W_eff + a < r then
      costedGQuantizeCoordToScale p_in q w (read1D xRow (b * W_eff + a)).2
    else do
      BitCostM.tick (2 * addBitCost w)
      pure 0) (List.range W_eff)

@[simp]
theorem computableSpreadRowBlockReContiguousWithCost_fst
    (p_in q w m1 r : ℕ) (xRow : Array (ℤ × ℤ)) (b : ℕ) :
    (computableSpreadRowBlockReContiguousWithCost p_in q w m1 r xRow b).1 =
      computableSpreadRowBlockReContiguous p_in q m1 r xRow b := by
  dsimp only [computableSpreadRowBlockReContiguousWithCost, computableSpreadRowBlockReContiguous]
  rw [BitCostM.mapListM_fst]
  refine List.map_congr_left fun a _ => ?_
  split_ifs <;> rfl

@[simp]
theorem computableSpreadRowBlockImContiguousWithCost_fst
    (p_in q w m1 r : ℕ) (xRow : Array (ℤ × ℤ)) (b : ℕ) :
    (computableSpreadRowBlockImContiguousWithCost p_in q w m1 r xRow b).1 =
      computableSpreadRowBlockImContiguous p_in q m1 r xRow b := by
  dsimp only [computableSpreadRowBlockImContiguousWithCost, computableSpreadRowBlockImContiguous]
  rw [BitCostM.mapListM_fst]
  refine List.map_congr_left fun a _ => ?_
  split_ifs <;> rfl

@[simp]
theorem computableSpreadRowBlockReContiguousWithCost_snd
    (p_in q w m1 r : ℕ) (xRow : Array (ℤ × ℤ)) (b : ℕ) :
    (computableSpreadRowBlockReContiguousWithCost p_in q w m1 r xRow b).2 =
      effectiveFilterWidth m1 r * (2 * addBitCost w) := by
  dsimp only [computableSpreadRowBlockReContiguousWithCost]
  rw [BitCostM.mapListM_snd_const _ _ (2 * addBitCost w) (fun a _ => by split_ifs <;> rfl),
      List.length_range]

@[simp]
theorem computableSpreadRowBlockImContiguousWithCost_snd
    (p_in q w m1 r : ℕ) (xRow : Array (ℤ × ℤ)) (b : ℕ) :
    (computableSpreadRowBlockImContiguousWithCost p_in q w m1 r xRow b).2 =
      effectiveFilterWidth m1 r * (2 * addBitCost w) := by
  dsimp only [computableSpreadRowBlockImContiguousWithCost]
  rw [BitCostM.mapListM_snd_const _ _ (2 * addBitCost w) (fun a _ => by split_ifs <;> rfl),
      List.length_range]

/-- Costed $O(1)$ in-place bucket update on `acc : Array ℤ` (`accumBucketIntWithCost`, `[MS]` §6.2):
executes `accumBucketInt acc idx v` and charges `addBitCost w` for the bucket addition. -/
def accumBucketIntWithCost (w : ℕ) (acc : Array ℤ) (idx : ℕ) (v : ℤ) : BitCostM (Array ℤ) :=
  (accumBucketInt acc idx v, addBitCost w)

/-- Costed single-pass inner loop over `i ∈ 0 .. n - 1` accumulating `valFn i` into bucket `idxFn i`
via `accumBucketIntWithCost w` in `Monad BitCostM`. -/
def accumBucketsRangeWithCost (w : ℕ) (idxFn : ℕ → ℕ) (valFn : ℕ → ℤ) :
    ℕ → Array ℤ → BitCostM (Array ℤ)
  | 0, acc => pure acc
  | n + 1, acc => do
    let acc' ← accumBucketsRangeWithCost w idxFn valFn n acc
    accumBucketIntWithCost w acc' (idxFn n) (valFn n)

@[simp]
theorem accumBucketsRangeWithCost_fst (w : ℕ) (idxFn : ℕ → ℕ) (valFn : ℕ → ℤ) (n : ℕ) (acc : Array ℤ) :
    (accumBucketsRangeWithCost w idxFn valFn n acc).1 = accumBucketsRange idxFn valFn n acc := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [accumBucketsRangeWithCost, accumBucketsRange, Bind.bind, accumBucketIntWithCost]
    rw [ih]

@[simp]
theorem accumBucketsRangeWithCost_snd (w : ℕ) (idxFn : ℕ → ℕ) (valFn : ℕ → ℤ) (n : ℕ) (acc : Array ℤ) :
    (accumBucketsRangeWithCost w idxFn valFn n acc).2 = n * addBitCost w := by
  induction n with
  | zero => simp [accumBucketsRangeWithCost, Pure.pure]
  | succ n ih =>
    dsimp only [accumBucketsRangeWithCost, Bind.bind, accumBucketIntWithCost]
    rw [ih]
    ring

/-- Costed single-pass 2-level overlap-add bucket accumulation helper over `b ∈ 0 .. numBlocks - 1`
and `i ∈ 0 .. W2 - 1` in `Monad BitCostM`. -/
def overlapAddBucketsSinglePassAuxWithCost (w W2 : ℕ) (idxFn : ℕ → ℕ → ℕ) (valFn : ℕ → ℕ → ℤ) :
    ℕ → Array ℤ → BitCostM (Array ℤ)
  | 0, acc => pure acc
  | b + 1, acc => do
    let acc' ← overlapAddBucketsSinglePassAuxWithCost w W2 idxFn valFn b acc
    accumBucketsRangeWithCost w (idxFn b) (valFn b) W2 acc'

@[simp]
theorem overlapAddBucketsSinglePassAuxWithCost_fst
    (w W2 : ℕ) (idxFn : ℕ → ℕ → ℕ) (valFn : ℕ → ℕ → ℤ) (b : ℕ) (acc : Array ℤ) :
    (overlapAddBucketsSinglePassAuxWithCost w W2 idxFn valFn b acc).1 =
      overlapAddBucketsSinglePassAux W2 idxFn valFn b acc := by
  induction b with
  | zero => rfl
  | succ b ih =>
    dsimp only [overlapAddBucketsSinglePassAuxWithCost, overlapAddBucketsSinglePassAux, Bind.bind]
    rw [accumBucketsRangeWithCost_fst, ih]

@[simp]
theorem overlapAddBucketsSinglePassAuxWithCost_snd
    (w W2 : ℕ) (idxFn : ℕ → ℕ → ℕ) (valFn : ℕ → ℕ → ℤ) (b : ℕ) (acc : Array ℤ) :
    (overlapAddBucketsSinglePassAuxWithCost w W2 idxFn valFn b acc).2 =
      b * (W2 * addBitCost w) := by
  induction b with
  | zero => simp [overlapAddBucketsSinglePassAuxWithCost, Pure.pure]
  | succ b ih =>
    dsimp only [overlapAddBucketsSinglePassAuxWithCost, Bind.bind]
    rw [ih, accumBucketsRangeWithCost_snd]
    ring

/-- Costed single-pass $O(r)$ overlap-add bucket accumulator (`overlapAddBucketsSinglePassWithCost`, `[MS]` §6.2):
runs `overlapAddBucketsSinglePassAuxWithCost` directly in `Monad BitCostM` (without duplicate
`buckets`/`blockBucketCosts` passes), charging `addBitCost w` at each of the `numBlocks × W2`
in-place bucket updates. -/
def overlapAddBucketsSinglePassWithCost
    (w r numBlocks W2 : ℕ) (idxFn : ℕ → ℕ → ℕ) (valFn : ℕ → ℕ → ℤ) : BitCostM (Array ℤ) :=
  overlapAddBucketsSinglePassAuxWithCost w W2 idxFn valFn numBlocks (Array.replicate r 0)

@[simp]
theorem overlapAddBucketsSinglePassWithCost_fst
    (w r numBlocks W2 : ℕ) (idxFn : ℕ → ℕ → ℕ) (valFn : ℕ → ℕ → ℤ) :
    (overlapAddBucketsSinglePassWithCost w r numBlocks W2 idxFn valFn).1 =
      overlapAddBucketsSinglePass r numBlocks W2 idxFn valFn :=
  overlapAddBucketsSinglePassAuxWithCost_fst w W2 idxFn valFn numBlocks (Array.replicate r 0)

@[simp]
theorem overlapAddBucketsSinglePassWithCost_snd
    (w r numBlocks W2 : ℕ) (idxFn : ℕ → ℕ → ℕ) (valFn : ℕ → ℕ → ℤ) :
    (overlapAddBucketsSinglePassWithCost w r numBlocks W2 idxFn valFn).2 =
      numBlocks * (W2 * addBitCost w) :=
  overlapAddBucketsSinglePassAuxWithCost_snd w W2 idxFn valFn numBlocks (Array.replicate r 0)

/-! ### Divide-and-Conquer Binary-Tree Signed Kronecker Pack, Unpack, and Polynomial Multiplication (`[MS]` §6.2) -/

theorem int_shiftLeft_eq_mul_pow (a : ℤ) (n : ℕ) :
    a <<< n = a * ((2 ^ n : ℕ) : ℤ) := by
  simpa using Int.shiftLeft_eq' a n

theorem int_shiftRight_eq_ediv_pow (a : ℤ) (n : ℕ) :
    a >>> n = a / ((2 ^ n : ℕ) : ℤ) :=
  Int.shiftRight_eq_div_pow a n

theorem int_sub_shiftRight_shiftLeft_eq_emod_pow (a : ℤ) (n : ℕ) :
    a - ((a >>> n) <<< n) = a % ((2 ^ n : ℕ) : ℤ) := by
  rw [int_shiftRight_eq_ediv_pow, int_shiftLeft_eq_mul_pow]
  have h := Int.mul_ediv_add_emod a ((2 ^ n : ℕ) : ℤ)
  linarith

theorem nat_shiftLeft_eq_mul_pow (a n : ℕ) :
    a <<< n = a * 2 ^ n :=
  Nat.shiftLeft_eq a n

theorem nat_shiftRight_eq_div_pow (a n : ℕ) :
    a >>> n = a / 2 ^ n :=
  Nat.shiftRight_eq_div_pow a n

theorem nat_sub_shiftRight_shiftLeft_eq_mod_pow (a n : ℕ) :
    a - ((a >>> n) <<< n) = a % 2 ^ n := by
  rw [nat_shiftRight_eq_div_pow, nat_shiftLeft_eq_mul_pow]
  have h := Nat.div_add_mod a (2 ^ n)
  have hmul : (a / 2 ^ n) * 2 ^ n = 2 ^ n * (a / 2 ^ n) := Nat.mul_comm _ _
  omega

theorem two_mul_two_pow_sub_one_eq_int (s : ℕ) :
    2 * ((2 ^ (s - 1) : ℕ) : ℤ) = ((2 ^ ((s - 1) + 1) : ℕ) : ℤ) := by
  rw [pow_succ']
  push_cast
  ring

theorem two_mul_two_pow_sub_one_pow_eq_int (s k1 : ℕ) :
    (2 * ((2 ^ (s - 1) : ℕ) : ℤ)) ^ k1 = ((2 ^ (((s - 1) + 1) * k1) : ℕ) : ℤ) := by
  rw [two_mul_two_pow_sub_one_eq_int, ← Int.natCast_pow, ← pow_mul]

/-- Costed leaf primitive for signed Kronecker packing (`costedPackSignedLeaf`, `[MS]` §6.2):
returns coefficient `c` and charges `addBitCost s`. -/
def costedPackSignedLeaf (s : ℕ) (c : ℤ) : BitCostM ℤ :=
  (c, addBitCost s)

/-- Costed internal-node bit-shift-and-combine primitive for signed Kronecker packing
(`costedCombineSignedPack`, `[MS]` §6.2):
combines low half `lo` and high half `hi` at bit-stride `((s - 1) + 1)` over `k1` slots via the
left bit-shift `lo + (hi <<< (((s - 1) + 1) * k1))` and charges `addBitCost (k * s)` for the
combined `k * s`-bit word operation. -/
def costedCombineSignedPack (k s k1 : ℕ) (lo hi : ℤ) : BitCostM ℤ :=
  let shiftBits := ((s - 1) + 1) * k1
  (lo + (hi <<< shiftBits), addBitCost (k * s))

theorem costedCombineSignedPack_fst (k s k1 : ℕ) (lo hi : ℤ) :
    (costedCombineSignedPack k s k1 lo hi).1 =
      lo + (2 * ((2 ^ (s - 1) : ℕ) : ℤ)) ^ k1 * hi := by
  dsimp only [costedCombineSignedPack]
  rw [int_shiftLeft_eq_mul_pow, ← two_mul_two_pow_sub_one_pow_eq_int, mul_comm]

@[simp]
theorem costedCombineSignedPack_snd (k s k1 : ℕ) (lo hi : ℤ) :
    (costedCombineSignedPack k s k1 lo hi).2 = addBitCost (k * s) := rfl

/-- Costed single-slot bit-shift/mask extraction and carry-shift primitive for signed Kronecker
unpacking (`costedUnpackSignedSlot`, `[MS]` §6.2):
extracts `(extractSignedSlot H C, shiftSignedSlot H C)` for `H = 2 ^ (s - 1)` using bit-shifts
`<<<`, `>>>` and subtraction masks, and charges `2 * addBitCost s`. -/
def costedUnpackSignedSlot (s : ℕ) (C : ℤ) : BitCostM (ℤ × ℤ) :=
  let hShift := s - 1
  let slotBits := (s - 1) + 1
  let H : ℤ := (1 : ℤ) <<< hShift
  let twoH : ℤ := (1 : ℤ) <<< slotBits
  let qSlot := C >>> slotBits
  let rem := C - (qSlot <<< slotBits)
  let c_j := if rem ≥ H then rem - twoH else rem
  let nextC := (C - c_j) >>> slotBits
  ((c_j, nextC), 2 * addBitCost s)

theorem costedUnpackSignedSlot_fst (s : ℕ) (C : ℤ) :
    let H : ℤ := ((2 ^ (s - 1) : ℕ) : ℤ)
    (costedUnpackSignedSlot s C).1 = (extractSignedSlot H C, shiftSignedSlot H C) := by
  dsimp only [costedUnpackSignedSlot, extractSignedSlot, shiftSignedSlot]
  have hH : ((1 : ℤ) <<< (s - 1)) = ((2 ^ (s - 1) : ℕ) : ℤ) := by
    rw [int_shiftLeft_eq_mul_pow, one_mul]
  have htwoH : ((1 : ℤ) <<< ((s - 1) + 1)) = 2 * ((2 ^ (s - 1) : ℕ) : ℤ) := by
    rw [int_shiftLeft_eq_mul_pow, one_mul, ← two_mul_two_pow_sub_one_eq_int]
  rw [hH, htwoH, int_sub_shiftRight_shiftLeft_eq_emod_pow, int_shiftRight_eq_ediv_pow,
      ← two_mul_two_pow_sub_one_eq_int]

@[simp]
theorem costedUnpackSignedSlot_snd (s : ℕ) (C : ℤ) :
    (costedUnpackSignedSlot s C).2 = 2 * addBitCost s := rfl

/-- Costed internal-node bit-aligned split primitive for signed Kronecker unpacking
(`costedSplitSignedPower`, `[MS]` §6.2):
splits `C` at bit-offset `shiftBits = ((s - 1) + 1) * k1` via `hi := C >>> shiftBits` and
`lo := C - (hi <<< shiftBits)` and charges `addBitCost (k * s)`. -/
def costedSplitSignedPower (k s k1 : ℕ) (C : ℤ) : BitCostM (ℤ × ℤ) :=
  let shiftBits := ((s - 1) + 1) * k1
  let hi := C >>> shiftBits
  let lo := C - (hi <<< shiftBits)
  ((lo, hi), addBitCost (k * s))

theorem costedSplitSignedPower_fst (k s k1 : ℕ) (C : ℤ) :
    let M : ℤ := (2 * ((2 ^ (s - 1) : ℕ) : ℤ)) ^ k1
    (costedSplitSignedPower k s k1 C).1 = (C % M, C / M) := by
  dsimp only [costedSplitSignedPower]
  rw [int_sub_shiftRight_shiftLeft_eq_emod_pow, int_shiftRight_eq_ediv_pow,
      ← two_mul_two_pow_sub_one_pow_eq_int]

@[simp]
theorem costedSplitSignedPower_snd (k s k1 : ℕ) (C : ℤ) :
    (costedSplitSignedPower k s k1 C).2 = addBitCost (k * s) := rfl

/-- Costed internal-node carry-propagation addition for signed Kronecker unpacking
(`costedAddCarrySignedPower`, `[MS]` §6.2):
adds `carry + hi` and charges `addBitCost (k * s)`. -/
def costedAddCarrySignedPower (k s : ℕ) (carry hi : ℤ) : BitCostM ℤ :=
  (carry + hi, addBitCost (k * s))

/-- Costed integer multiplication primitive (`costedMulInt`):
multiplies `a * b` and charges `computableMulBitCost w`. -/
def costedMulInt (w : ℕ) (a b : ℤ) : BitCostM ℤ :=
  (a * b, computableMulBitCost w)

/-- Evaluates `packSignedKronecker M (xs ++ ys)` as `packSignedKronecker M xs + M ^ xs.length * packSignedKronecker M ys`. -/
theorem packSignedKronecker_append (M : ℤ) (xs ys : List ℤ) :
    packSignedKronecker M (xs ++ ys) =
      packSignedKronecker M xs + (M ^ xs.length) * packSignedKronecker M ys := by
  induction xs with
  | nil => simp [packSignedKronecker]
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, packSignedKronecker, ih, pow_succ']
    ring

/-- Binary-tree recursion fuel `⌈log₂ k⌉ + 2` on an $O(\log n)$-bit chunk/coefficient count `k`. -/
def natTreeFuel (k : ℕ) : ℕ := natLog2Fuel k k + 2

/-- Binary-tree left-half count `k / 2` on an $O(\log n)$-bit chunk/coefficient count `k`. -/
def natTreeLeftHalf (k : ℕ) : ℕ := k / 2

/-- Binary-tree right-half count `k - k / 2` on an $O(\log n)$-bit chunk/coefficient count `k`. -/
def natTreeRightHalf (k : ℕ) : ℕ := k - k / 2

/-- Balanced divide-and-conquer binary-tree helper for signed Kronecker packing
(`packSignedKroneckerTreeAuxWithCost`, `[MS]` §6.2):
recursively packs `cs.take (k / 2)` and `cs.drop (k / 2)` and combines them by bit-shift via
`costedCombineSignedPack k s (k / 2)`, charging `addBitCost (k * s)` at every tree node of size `k`. -/
def packSignedKroneckerTreeAuxWithCost : ℕ → ℕ → ℕ → List ℤ → BitCostM ℤ
  | 0, _, _, _ => pure 0
  | fuel + 1, s, k, cs =>
    if k = 0 then pure 0
    else if k = 1 then costedPackSignedLeaf s (cs.headD 0)
    else do
      let k1 := natTreeLeftHalf k
      let k2 := natTreeRightHalf k
      let l ← packSignedKroneckerTreeAuxWithCost fuel s k1 (cs.take k1)
      let r ← packSignedKroneckerTreeAuxWithCost fuel s k2 (cs.drop k1)
      costedCombineSignedPack k s k1 l r

/-- Balanced divide-and-conquer binary-tree signed Kronecker packer
(`packSignedKroneckerTreeWithCost`, `[MS]` §6.2):
uses `fuel = natTreeFuel cs.length` ($\lceil \log_2 |cs| \rceil + 2$ levels) so both
literal work and charged cost are $O(|cs| \cdot s \log |cs|)$ instead of Horner $\Theta(|cs|^2 s)$. -/
def packSignedKroneckerTreeWithCost (s : ℕ) (_H : ℤ) (cs : List ℤ) : BitCostM ℤ :=
  packSignedKroneckerTreeAuxWithCost (natTreeFuel cs.length) s cs.length cs

theorem packSignedKroneckerTreeAuxWithCost_fst :
    ∀ (fuel s k : ℕ) (cs : List ℤ),
      cs.length = k → k ≤ 2 ^ fuel →
      (packSignedKroneckerTreeAuxWithCost (fuel + 1) s k cs).1 =
        packSignedKronecker (2 * ((2 ^ (s - 1) : ℕ) : ℤ)) cs
  | 0, s, k, cs, hlen, hk => by
    have hk1 : k = 0 ∨ k = 1 := by omega
    rcases hk1 with rfl | rfl
    · obtain rfl : cs = [] := List.eq_nil_of_length_eq_zero hlen
      rfl
    · obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := List.length_eq_one_iff.mp hlen
      simp [packSignedKroneckerTreeAuxWithCost, costedPackSignedLeaf, packSignedKronecker]
  | fuel + 1, s, k, cs, hlen, hk => by
    unfold packSignedKroneckerTreeAuxWithCost
    dsimp only [natTreeLeftHalf, natTreeRightHalf]
    split_ifs with h0 h1
    · subst h0
      obtain rfl : cs = [] := List.eq_nil_of_length_eq_zero hlen
      rfl
    · subst h1
      obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := List.length_eq_one_iff.mp hlen
      simp [costedPackSignedLeaf, packSignedKronecker]
    · simp only [BitCostM.bind_fst, costedCombineSignedPack_fst]
      have hk_pow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
      have hk1_le : k / 2 ≤ 2 ^ fuel := by omega
      have hk2_le : k - k / 2 ≤ 2 ^ fuel := by omega
      have hlen1 : (cs.take (k / 2)).length = k / 2 := by simp [hlen]; omega
      have hlen2 : (cs.drop (k / 2)).length = k - k / 2 := by simp [hlen]
      rw [packSignedKroneckerTreeAuxWithCost_fst fuel s (k / 2) (cs.take (k / 2)) hlen1 hk1_le,
          packSignedKroneckerTreeAuxWithCost_fst fuel s (k - k / 2) (cs.drop (k / 2)) hlen2 hk2_le]
      conv_rhs => rw [← List.take_append_drop (k / 2) cs, packSignedKronecker_append, hlen1]

@[simp]
theorem packSignedKroneckerTreeWithCost_fst (s : ℕ) (H : ℤ) (cs : List ℤ) :
    (packSignedKroneckerTreeWithCost s H cs).1 =
      packSignedKronecker (2 * ((2 ^ (s - 1) : ℕ) : ℤ)) cs := by
  unfold packSignedKroneckerTreeWithCost natTreeFuel
  rw [natLog2Fuel_self]
  exact packSignedKroneckerTreeAuxWithCost_fst (Nat.log2 cs.length + 1) s cs.length cs rfl
    (lt_two_pow_log2_succ cs.length).le

theorem packSignedKroneckerTreeAuxWithCost_snd_le :
    ∀ (fuel s k : ℕ) (cs : List ℤ),
      (packSignedKroneckerTreeAuxWithCost fuel s k cs).2 ≤
        fuel * k * addBitCost s
  | 0, s, k, cs => by simp [packSignedKroneckerTreeAuxWithCost, Pure.pure]
  | fuel + 1, s, k, cs => by
    unfold packSignedKroneckerTreeAuxWithCost
    dsimp only [natTreeLeftHalf, natTreeRightHalf]
    split_ifs with h0 h1
    · simp [Pure.pure]
    · subst h1
      dsimp [costedPackSignedLeaf]
      have h1_le : 1 ≤ (fuel + 1) * 1 := by omega
      simpa only [one_mul] using Nat.mul_le_mul_right (addBitCost s) h1_le
    · simp only [BitCostM.bind_snd, costedCombineSignedPack_snd]
      have ih1 := packSignedKroneckerTreeAuxWithCost_snd_le fuel s (k / 2) (cs.take (k / 2))
      have ih2 := packSignedKroneckerTreeAuxWithCost_snd_le fuel s (k - k / 2) (cs.drop (k / 2))
      have hadd_ks : addBitCost (k * s) = k * addBitCost s := rfl
      have hsum :
          fuel * (k / 2) * addBitCost s + (fuel * (k - k / 2) * addBitCost s + k * addBitCost s) =
            (fuel + 1) * k * addBitCost s := by
        have hk : k / 2 + (k - k / 2) = k := by omega
        calc fuel * (k / 2) * addBitCost s + (fuel * (k - k / 2) * addBitCost s + k * addBitCost s)
            = fuel * (k / 2 + (k - k / 2)) * addBitCost s + k * addBitCost s := by ring
          _ = fuel * k * addBitCost s + k * addBitCost s := by rw [hk]
          _ = (fuel + 1) * k * addBitCost s := by ring
      linarith

theorem packSignedKroneckerTreeWithCost_snd_le (s : ℕ) (H : ℤ) (cs : List ℤ) :
    (packSignedKroneckerTreeWithCost s H cs).2 ≤
      (Nat.log2 cs.length + 2) * cs.length * addBitCost s := by
  unfold packSignedKroneckerTreeWithCost natTreeFuel
  rw [natLog2Fuel_self]
  exact packSignedKroneckerTreeAuxWithCost_snd_le (Nat.log2 cs.length + 2) s cs.length cs

/-- Iterated upper-word shift after extracting `k` signed Kronecker slots. -/
def shiftSignedSlotIter (H : ℤ) : ℕ → ℤ → ℤ
  | 0, C => C
  | k + 1, C => shiftSignedSlotIter H k (shiftSignedSlot H C)

theorem extractSignedSlot_add_mul_right (H A Q : ℤ) :
    extractSignedSlot H (A + (2 * H) * Q) = extractSignedSlot H A := by
  unfold extractSignedSlot
  dsimp only
  rw [Int.add_mul_emod_self_left]

theorem shiftSignedSlot_add_mul_right (H A Q : ℤ) (hH : 0 < H) :
    shiftSignedSlot H (A + (2 * H) * Q) = shiftSignedSlot H A + Q := by
  unfold shiftSignedSlot
  rw [extractSignedSlot_add_mul_right]
  have hsub : A + 2 * H * Q - extractSignedSlot H A =
      (A - extractSignedSlot H A) + (2 * H) * Q := by ring
  rw [hsub, Int.add_mul_ediv_left _ _ (by omega)]

theorem unpackSignedKronecker_add (H : ℤ) :
    ∀ (k1 k2 : ℕ) (C : ℤ),
      unpackSignedKronecker H (k1 + k2) C =
        unpackSignedKronecker H k1 C ++ unpackSignedKronecker H k2 (shiftSignedSlotIter H k1 C)
  | 0, k2, C => by simp [unpackSignedKronecker, shiftSignedSlotIter]
  | k1 + 1, k2, C => by
    rw [Nat.succ_add]
    simp only [unpackSignedKronecker, shiftSignedSlotIter, List.cons_append]
    rw [unpackSignedKronecker_add H k1 k2 (shiftSignedSlot H C)]

theorem shiftSignedSlotIter_add (H : ℤ) :
    ∀ (k1 k2 : ℕ) (C : ℤ),
      shiftSignedSlotIter H (k1 + k2) C =
        shiftSignedSlotIter H k2 (shiftSignedSlotIter H k1 C)
  | 0, k2, C => by simp [shiftSignedSlotIter]
  | k1 + 1, k2, C => by
    rw [Nat.succ_add]
    simp only [shiftSignedSlotIter]
    exact shiftSignedSlotIter_add H k1 k2 (shiftSignedSlot H C)

theorem unpackSignedKronecker_add_pow_mul (H : ℤ) (hH : 0 < H) :
    ∀ (k : ℕ) (A Q : ℤ),
      unpackSignedKronecker H k (A + (2 * H) ^ k * Q) = unpackSignedKronecker H k A
  | 0, A, Q => rfl
  | k + 1, A, Q => by
    simp only [unpackSignedKronecker]
    have hpow : A + (2 * H) ^ (k + 1) * Q = A + (2 * H) * ((2 * H) ^ k * Q) := by
      rw [pow_succ']
      ring
    rw [hpow, extractSignedSlot_add_mul_right, shiftSignedSlot_add_mul_right H A _ hH,
        unpackSignedKronecker_add_pow_mul H hH k (shiftSignedSlot H A) Q]

theorem shiftSignedSlotIter_add_pow_mul (H : ℤ) (hH : 0 < H) :
    ∀ (k : ℕ) (A Q : ℤ),
      shiftSignedSlotIter H k (A + (2 * H) ^ k * Q) = shiftSignedSlotIter H k A + Q
  | 0, A, Q => by simp [shiftSignedSlotIter]
  | k + 1, A, Q => by
    simp only [shiftSignedSlotIter]
    have hpow : A + (2 * H) ^ (k + 1) * Q = A + (2 * H) * ((2 * H) ^ k * Q) := by
      rw [pow_succ']
      ring
    rw [hpow, shiftSignedSlot_add_mul_right H A _ hH,
        shiftSignedSlotIter_add_pow_mul H hH k (shiftSignedSlot H A) Q]

/-- Balanced divide-and-conquer binary-tree helper for signed Kronecker unpacking
(`unpackSignedKroneckerTreeAuxWithCost`, `[MS]` §6.2):
splits `C` at bit-offset `((s - 1) + 1) * (k / 2)` via `costedSplitSignedPower k s (k / 2)`,
unpacks the low `k / 2` slots returning carry `l.2`, adds `l.2 + rq.2` via
`costedAddCarrySignedPower k s`, and unpacks the high `k - k / 2` slots, charging `2 * addBitCost (k * s)`
at every tree node of size `k`. -/
def unpackSignedKroneckerTreeAuxWithCost : ℕ → ℕ → ℕ → ℤ → BitCostM (List ℤ × ℤ)
  | 0, _, _, C => pure ([], C)
  | fuel + 1, s, k, C =>
    if k = 0 then pure ([], C)
    else if k = 1 then do
      let sc ← costedUnpackSignedSlot s C
      pure ([sc.1], sc.2)
    else do
      let k1 := natTreeLeftHalf k
      let k2 := natTreeRightHalf k
      let rq ← costedSplitSignedPower k s k1 C
      let l ← unpackSignedKroneckerTreeAuxWithCost fuel s k1 rq.1
      let cHi ← costedAddCarrySignedPower k s l.2 rq.2
      let r ← unpackSignedKroneckerTreeAuxWithCost fuel s k2 cHi
      pure (l.1 ++ r.1, r.2)

/-- Balanced divide-and-conquer binary-tree signed Kronecker unpacker
(`unpackSignedKroneckerTreeWithCost`, `[MS]` §6.2):
uses `fuel = natTreeFuel k` ($\lceil \log_2 k \rceil + 2$ levels) so both literal work and
charged cost are $O(k \cdot s \log k)$ instead of sequential $\Theta(k^2 s)$. -/
def unpackSignedKroneckerTreeWithCost (s : ℕ) (_H : ℤ) (k : ℕ) (C : ℤ) : BitCostM (List ℤ × ℤ) :=
  unpackSignedKroneckerTreeAuxWithCost (natTreeFuel k) s k C

theorem unpackSignedKroneckerTreeAuxWithCost_fst :
    ∀ (fuel s k : ℕ) (C : ℤ),
      let H : ℤ := ((2 ^ (s - 1) : ℕ) : ℤ)
      k ≤ 2 ^ fuel →
      (unpackSignedKroneckerTreeAuxWithCost (fuel + 1) s k C).1 =
        (unpackSignedKronecker H k C, shiftSignedSlotIter H k C)
  | 0, s, k, C, hk => by
    have hk1 : k = 0 ∨ k = 1 := by omega
    rcases hk1 with rfl | rfl
    · rfl
    · simp only [unpackSignedKroneckerTreeAuxWithCost, ↓reduceIte, Nat.one_ne_zero,
        BitCostM.bind_fst, BitCostM.pure_fst, costedUnpackSignedSlot_fst,
        unpackSignedKronecker, shiftSignedSlotIter]
  | fuel + 1, s, k, C, hk => by
    unfold unpackSignedKroneckerTreeAuxWithCost
    dsimp only [natTreeLeftHalf, natTreeRightHalf]
    split_ifs with h0 h1
    · subst h0; rfl
    · subst h1
      simp only [BitCostM.bind_fst, BitCostM.pure_fst, costedUnpackSignedSlot_fst,
        unpackSignedKronecker, shiftSignedSlotIter]
    · simp only [BitCostM.bind_fst, BitCostM.pure_fst, costedSplitSignedPower_fst,
        costedAddCarrySignedPower]
      set H : ℤ := ((2 ^ (s - 1) : ℕ) : ℤ)
      have hH : (0 : ℤ) < H := by dsimp [H]; positivity
      have hk_pow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
      have hk1_le : k / 2 ≤ 2 ^ fuel := by omega
      have hk2_le : k - k / 2 ≤ 2 ^ fuel := by omega
      set k1 := k / 2
      set k2 := k - k / 2
      set M1 : ℤ := (2 * H) ^ k1
      rw [unpackSignedKroneckerTreeAuxWithCost_fst fuel s k1 (C % M1) hk1_le,
          unpackSignedKroneckerTreeAuxWithCost_fst fuel s k2
            (shiftSignedSlotIter H k1 (C % M1) + C / M1) hk2_le]
      have hdiv : C % M1 + M1 * (C / M1) = C := by
        have h := Int.mul_ediv_add_emod C M1
        linarith
      have hunpack1 : unpackSignedKronecker H k1 (C % M1) = unpackSignedKronecker H k1 C := by
        conv_rhs => rw [← hdiv]
        exact (unpackSignedKronecker_add_pow_mul H hH k1 (C % M1) (C / M1)).symm
      have hshift1 : shiftSignedSlotIter H k1 (C % M1) + C / M1 = shiftSignedSlotIter H k1 C := by
        conv_rhs => rw [← hdiv]
        exact (shiftSignedSlotIter_add_pow_mul H hH k1 (C % M1) (C / M1)).symm
      rw [hunpack1, hshift1]
      have hk_eq : k = k1 + k2 := by omega
      conv_rhs => rw [hk_eq, unpackSignedKronecker_add H k1 k2 C, shiftSignedSlotIter_add H k1 k2 C]

@[simp]
theorem unpackSignedKroneckerTreeWithCost_fst_fst (s : ℕ) (H : ℤ) (k : ℕ) (C : ℤ) :
    (unpackSignedKroneckerTreeWithCost s H k C).1.1 =
      unpackSignedKronecker ((2 ^ (s - 1) : ℕ) : ℤ) k C := by
  unfold unpackSignedKroneckerTreeWithCost natTreeFuel
  rw [natLog2Fuel_self,
      unpackSignedKroneckerTreeAuxWithCost_fst (Nat.log2 k + 1) s k C
        (lt_two_pow_log2_succ k).le]

theorem unpackSignedKroneckerTreeAuxWithCost_snd_le :
    ∀ (fuel s k : ℕ) (C : ℤ),
      (unpackSignedKroneckerTreeAuxWithCost fuel s k C).2 ≤
        2 * fuel * k * addBitCost s
  | 0, s, k, C => by simp [unpackSignedKroneckerTreeAuxWithCost, Pure.pure]
  | fuel + 1, s, k, C => by
    unfold unpackSignedKroneckerTreeAuxWithCost
    dsimp only [natTreeLeftHalf, natTreeRightHalf]
    split_ifs with h0 h1
    · simp [Pure.pure]
    · subst h1
      simp only [BitCostM.bind_snd, BitCostM.pure_snd, costedUnpackSignedSlot_snd, add_zero]
      have h1_le : 2 ≤ 2 * (fuel + 1) * 1 := by omega
      simpa only [one_mul] using Nat.mul_le_mul_right (addBitCost s) h1_le
    · simp only [BitCostM.bind_snd, BitCostM.pure_snd, costedSplitSignedPower_snd,
        costedAddCarrySignedPower, add_zero]
      set k1 := k / 2
      set k2 := k - k1
      set rq := (costedSplitSignedPower k s k1 C).1
      have ih1 := unpackSignedKroneckerTreeAuxWithCost_snd_le fuel s k1 rq.1
      have ih2 := unpackSignedKroneckerTreeAuxWithCost_snd_le fuel s k2
        ((unpackSignedKroneckerTreeAuxWithCost fuel s k1 rq.1).1.2 + rq.2)
      have hadd_ks : addBitCost (k * s) = k * addBitCost s := rfl
      have hsum :
          k * addBitCost s +
            (2 * fuel * k1 * addBitCost s +
              (k * addBitCost s + 2 * fuel * k2 * addBitCost s)) =
            2 * (fuel + 1) * k * addBitCost s := by
        have hk : k1 + k2 = k := by omega
        calc k * addBitCost s +
              (2 * fuel * k1 * addBitCost s +
                (k * addBitCost s + 2 * fuel * k2 * addBitCost s))
            = 2 * fuel * (k1 + k2) * addBitCost s + 2 * k * addBitCost s := by ring
          _ = 2 * fuel * k * addBitCost s + 2 * k * addBitCost s := by rw [hk]
          _ = 2 * (fuel + 1) * k * addBitCost s := by ring
      linarith

theorem unpackSignedKroneckerTreeWithCost_snd_le (s : ℕ) (H : ℤ) (k : ℕ) (C : ℤ) :
    (unpackSignedKroneckerTreeWithCost s H k C).2 ≤
      2 * (Nat.log2 k + 2) * k * addBitCost s := by
  unfold unpackSignedKroneckerTreeWithCost natTreeFuel
  rw [natLog2Fuel_self]
  exact unpackSignedKroneckerTreeAuxWithCost_snd_le (Nat.log2 k + 2) s k C

/-- Balanced divide-and-conquer binary-tree signed-Kronecker polynomial multiplier
(`polyMulKroneckerSignedTreeWithCost`, `[MS]` §6.2):
packs `f` and `g` via `packSignedKroneckerTreeWithCost`, multiplies the packed integers via
`costedMulInt (f.length * s)`, and unpacks the product via `unpackSignedKroneckerTreeWithCost`
inside `Monad BitCostM`. -/
def polyMulKroneckerSignedTreeWithCost (s : ℕ) (f g : List ℤ) : BitCostM (List ℤ) := do
  let outLen := if f.isEmpty then 0 else if g.isEmpty then f.length else f.length + g.length - 1
  let Pf ← packSignedKroneckerTreeWithCost s 0 f
  let Pg ← packSignedKroneckerTreeWithCost s 0 g
  let C ← costedMulInt (f.length * s) Pf Pg
  let u ← unpackSignedKroneckerTreeWithCost s 0 outLen C
  pure u.1

@[simp]
theorem polyMulKroneckerSignedTreeWithCost_fst (s : ℕ) (f g : List ℤ) :
    (polyMulKroneckerSignedTreeWithCost s f g).1 =
      polyMulKroneckerSignedComputable s f g := by
  dsimp only [polyMulKroneckerSignedTreeWithCost, polyMulKroneckerSignedComputable,
    polyMulKroneckerSignedH, Bind.bind, Pure.pure, costedMulInt]
  rw [packSignedKroneckerTreeWithCost_fst, packSignedKroneckerTreeWithCost_fst,
      unpackSignedKroneckerTreeWithCost_fst_fst]
  congr 1
  by_cases hf : f = [] <;> by_cases hg : g = [] <;> simp [hf, hg]

theorem mul_log2_add_one_le_mulBitCost (w : ℕ) :
    w * (Nat.log2 w + 1) ≤ mulBitCost w := by
  dsimp [mulBitCost]
  have h1 : 1 ≤ Nat.log2 (Nat.log2 w + 1) + 1 := by omega
  calc w * (Nat.log2 w + 1)
      = w * (Nat.log2 w + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ w * (Nat.log2 w + 1) * (Nat.log2 (Nat.log2 w + 1) + 1) :=
        Nat.mul_le_mul_left _ h1

theorem log2_add_two_mul_le_two_mul_mulBitCost (k W s : ℕ) (hk : k ≤ W) (hs : 1 ≤ s) :
    (Nat.log2 k + 2) * k * addBitCost s ≤ 2 * mulBitCost (W * s) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp [mulBitCost]
  · have hks_le : k ≤ W * s := by
      calc k = k * 1 := (Nat.mul_one k).symm
        _ ≤ W * s := Nat.mul_le_mul hk hs
    have hlog : Nat.log2 k ≤ Nat.log2 (W * s) := nat_log2_mono hks_le
    have h1 : Nat.log2 k + 2 ≤ 2 * (Nat.log2 (W * s) + 1) := by omega
    have h2 : k * addBitCost s ≤ W * s := by
      dsimp [addBitCost]
      exact Nat.mul_le_mul_right s hk
    have h3 := mul_log2_add_one_le_mulBitCost (W * s)
    calc (Nat.log2 k + 2) * k * addBitCost s
        = (Nat.log2 k + 2) * (k * addBitCost s) := by ring
      _ ≤ (2 * (Nat.log2 (W * s) + 1)) * (W * s) := Nat.mul_le_mul h1 h2
      _ = 2 * ((W * s) * (Nat.log2 (W * s) + 1)) := by ring
      _ ≤ 2 * mulBitCost (W * s) := Nat.mul_le_mul_left 2 h3

theorem two_mul_log2_add_two_mul_le_twelve_mul_mulBitCost
    (k W s : ℕ) (hk : k ≤ 2 * W) (hs : 1 ≤ s) :
    2 * (Nat.log2 k + 2) * k * addBitCost s ≤ 12 * mulBitCost (W * s) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp [mulBitCost]
  · have hk_le_2Ws : k ≤ 2 * (W * s) := by
      calc k ≤ 2 * W := hk
        _ = 2 * (W * 1) := by ring
        _ ≤ 2 * (W * s) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left W hs)
    have hlt : k < 2 ^ (Nat.log2 (W * s) + 2) := by
      have hWs_lt := lt_two_pow_log2_succ (W * s)
      have hpow : 2 ^ (Nat.log2 (W * s) + 2) = 2 * 2 ^ (Nat.log2 (W * s) + 1) := by ring
      omega
    have hlog_lt : Nat.log2 k < Nat.log2 (W * s) + 2 := (Nat.log2_lt hk_pos.ne').mpr hlt
    have h1 : Nat.log2 k + 2 ≤ 3 * (Nat.log2 (W * s) + 1) := by omega
    have h2 : k * addBitCost s ≤ 2 * (W * s) := by
      dsimp [addBitCost]
      calc k * s ≤ (2 * W) * s := Nat.mul_le_mul_right s hk
        _ = 2 * (W * s) := by ring
    have h3 := mul_log2_add_one_le_mulBitCost (W * s)
    calc 2 * (Nat.log2 k + 2) * k * addBitCost s
        = 2 * ((Nat.log2 k + 2) * (k * addBitCost s)) := by ring
      _ ≤ 2 * ((3 * (Nat.log2 (W * s) + 1)) * (2 * (W * s))) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul h1 h2)
      _ = 12 * ((W * s) * (Nat.log2 (W * s) + 1)) := by ring
      _ ≤ 12 * mulBitCost (W * s) := Nat.mul_le_mul_left 12 h3

theorem polyMulKroneckerSignedTreeWithCost_snd_le
    (s : ℕ) (hs : 1 ≤ s) (f g : List ℤ) (hg : g.length ≤ f.length) :
    (polyMulKroneckerSignedTreeWithCost s f g).2 ≤
      17 * mulBitCost (f.length * s) := by
  dsimp only [polyMulKroneckerSignedTreeWithCost, Bind.bind, Pure.pure, costedMulInt]
  set outLen := if f.isEmpty then 0 else if g.isEmpty then f.length else f.length + g.length - 1
  set H : ℤ := 0
  have hout_le : outLen ≤ 2 * f.length := by
    dsimp [outLen]
    split_ifs <;> omega
  have hpack_f : (packSignedKroneckerTreeWithCost s H f).2 ≤ 2 * mulBitCost (f.length * s) :=
    (packSignedKroneckerTreeWithCost_snd_le s H f).trans
      (log2_add_two_mul_le_two_mul_mulBitCost f.length f.length s le_rfl hs)
  have hpack_g : (packSignedKroneckerTreeWithCost s H g).2 ≤ 2 * mulBitCost (f.length * s) :=
    (packSignedKroneckerTreeWithCost_snd_le s H g).trans
      (log2_add_two_mul_le_two_mul_mulBitCost g.length f.length s hg hs)
  have hunpack :
      (unpackSignedKroneckerTreeWithCost s H outLen
        ((packSignedKroneckerTreeWithCost s H f).1 * (packSignedKroneckerTreeWithCost s H g).1)).2 ≤
        12 * mulBitCost (f.length * s) :=
    (unpackSignedKroneckerTreeWithCost_snd_le s H outLen _).trans
      (two_mul_log2_add_two_mul_le_twelve_mul_mulBitCost outLen f.length s hout_le hs)
  rw [computableMulBitCost_eq]
  linarith

/-- Cyclic bucket index `((b * W_eff + i - m1) mod r)` for single-pass overlap-add accumulation
(`overlapAddBucketIdx`, `[MS]` §6.2). -/
def overlapAddBucketIdx (W_eff m1 r b i : ℕ) : ℕ :=
  ((((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ)).toNat

/-- Program-cost-accumulating contiguous-row Kronecker spread
(`computableSpreadRowContiguousWithProgramCost`, `[MS]` §6.2):
executes in a single monadic pass over `Monad BitCostM` (without duplicate `quantPairs`/`blockPairs`
or `outScan`/`outArr` passes):
1. For each block `b < numBlocks`, quantizes the real and imaginary input blocks via
   `computableSpreadRowBlockReContiguousWithCost` and `computableSpreadRowBlockImContiguousWithCost`,
   and multiplies by `gTapFold` via balanced divide-and-conquer `polyMulKroneckerSignedTreeWithCost`;
2. Accumulates all block products into `r` buckets in a single $O(r)$ pass via
   `overlapAddBucketsSinglePassWithCost`;
3. Reads out the `r` output buckets via `BitCostM.ofFnM` charging `2 * addBitCost (6 * p')` per cell. -/
def computableSpreadRowContiguousWithProgramCost
    (p_in q p' m1 r : ℕ) (gTapFold : List ℤ) (xRow : Array (ℤ × ℤ)) : BitCostM (Array (ℤ × ℤ)) := do
  let W_eff := effectiveFilterWidth m1 r
  let numBlocks := kroneckerSpreadNumBlocks m1 r
  let blockProds ← BitCostM.ofFnM numBlocks (fun b : Fin numBlocks => do
    let fBlockRe ← computableSpreadRowBlockReContiguousWithCost p_in q (6 * p') m1 r xRow b.val
    let fBlockIm ← computableSpreadRowBlockImContiguousWithCost p_in q (6 * p') m1 r xRow b.val
    let sRe := computableKroneckerBitStride fBlockRe gTapFold
    let sIm := computableKroneckerBitStride fBlockIm gTapFold
    let prodRe ← polyMulKroneckerSignedTreeWithCost sRe fBlockRe gTapFold
    let prodIm ← polyMulKroneckerSignedTreeWithCost sIm fBlockIm gTapFold
    pure (prodRe.toArray, prodIm.toArray))
  let idxFn := fun b i => overlapAddBucketIdx W_eff m1 r b i
  let bucketsRe ← overlapAddBucketsSinglePassWithCost (6 * p') r numBlocks (2 * W_eff) idxFn
    (fun b i =>
      let prodReArr := if hb : b < blockProds.size then blockProds[b].1 else #[]
      read1D prodReArr i)
  let bucketsIm ← overlapAddBucketsSinglePassWithCost (6 * p') r numBlocks (2 * W_eff) idxFn
    (fun b i =>
      let prodImArr := if hb : b < blockProds.size then blockProds[b].2 else #[]
      read1D prodImArr i)
  BitCostM.ofFnM r (fun k2 : Fin r => do
    BitCostM.tick (2 * addBitCost (6 * p'))
    pure (read1D bucketsRe k2.val, read1D bucketsIm k2.val))

@[simp]
theorem computableSpreadRowContiguousWithProgramCost_fst
    (p_in q p' m1 r : ℕ) (gTapFold : List ℤ) (xRow : Array (ℤ × ℤ)) :
    (computableSpreadRowContiguousWithProgramCost p_in q p' m1 r gTapFold xRow).1 =
      (computableSpreadRowContiguousWithCost p_in q m1 r gTapFold xRow).1 := by
  dsimp only [computableSpreadRowContiguousWithProgramCost, computableSpreadRowContiguousWithCost,
    overlapAddBucketIdx]
  simp only [BitCostM.bind_fst, BitCostM.ofFnM_fst, BitCostM.pure_fst,
    computableSpreadRowBlockReContiguousWithCost_fst,
    computableSpreadRowBlockImContiguousWithCost_fst,
    polyMulKroneckerSignedTreeWithCost_fst,
    overlapAddBucketsSinglePassWithCost_fst,
    Array.size_ofFn, Array.getElem_ofFn]

theorem computableSpreadRowContiguousWithProgramCost_snd_le
    (p_in q p' m1 r : ℕ) (gTapFold : List ℤ) (hg : gTapFold.length ≤ effectiveFilterWidth m1 r)
    (xRow : Array (ℤ × ℤ)) :
    (computableSpreadRowContiguousWithProgramCost p_in q p' m1 r gTapFold xRow).2 ≤
      17 * (computableSpreadRowContiguousWithCost p_in q m1 r gTapFold xRow).2 +
        (kroneckerSpreadNumBlocks m1 r * (8 * effectiveFilterWidth m1 r * addBitCost (6 * p')) +
          r * (2 * addBitCost (6 * p'))) := by
  dsimp only [computableSpreadRowContiguousWithProgramCost, computableSpreadRowContiguousWithCost,
    overlapAddBucketIdx]
  simp only [BitCostM.bind_snd, BitCostM.ofFnM_snd,
    overlapAddBucketsSinglePassWithCost_snd]
  set W_eff := effectiveFilterWidth m1 r
  set numBlocks := kroneckerSpreadNumBlocks m1 r
  have hout :
      sumArrayCosts
        (Array.ofFn (fun k2 : Fin r => (do
          BitCostM.tick (2 * addBitCost (6 * p'))
          pure
            (read1D
              (overlapAddBucketsSinglePassWithCost (6 * p') r numBlocks (2 * W_eff)
                (fun b i => ((((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ)).toNat)
                (fun b i =>
                  let prodReArr := if hb : b < (BitCostM.ofFnM numBlocks (fun b : Fin numBlocks => do
                    let fBlockRe ← computableSpreadRowBlockReContiguousWithCost p_in q (6 * p') m1 r xRow b.val
                    let fBlockIm ← computableSpreadRowBlockImContiguousWithCost p_in q (6 * p') m1 r xRow b.val
                    let sRe := computableKroneckerBitStride fBlockRe gTapFold
                    let sIm := computableKroneckerBitStride fBlockIm gTapFold
                    let prodRe ← polyMulKroneckerSignedTreeWithCost sRe fBlockRe gTapFold
                    let prodIm ← polyMulKroneckerSignedTreeWithCost sIm fBlockIm gTapFold
                    pure (prodRe.toArray, prodIm.toArray))).1.size then
                    (BitCostM.ofFnM numBlocks (fun b : Fin numBlocks => do
                      let fBlockRe ← computableSpreadRowBlockReContiguousWithCost p_in q (6 * p') m1 r xRow b.val
                      let fBlockIm ← computableSpreadRowBlockImContiguousWithCost p_in q (6 * p') m1 r xRow b.val
                      let sRe := computableKroneckerBitStride fBlockRe gTapFold
                      let sIm := computableKroneckerBitStride fBlockIm gTapFold
                      let prodRe ← polyMulKroneckerSignedTreeWithCost sRe fBlockRe gTapFold
                      let prodIm ← polyMulKroneckerSignedTreeWithCost sIm fBlockIm gTapFold
                      pure (prodRe.toArray, prodIm.toArray))).1[b].1 else #[]
                  read1D prodReArr i)).1 k2.val,
            read1D
              (overlapAddBucketsSinglePassWithCost (6 * p') r numBlocks (2 * W_eff)
                (fun b i => ((((b * W_eff + i : ℕ) : ℤ) - (m1 : ℤ)) % (r : ℤ)).toNat)
                (fun b i =>
                  let prodImArr := if hb : b < (BitCostM.ofFnM numBlocks (fun b : Fin numBlocks => do
                    let fBlockRe ← computableSpreadRowBlockReContiguousWithCost p_in q (6 * p') m1 r xRow b.val
                    let fBlockIm ← computableSpreadRowBlockImContiguousWithCost p_in q (6 * p') m1 r xRow b.val
                    let sRe := computableKroneckerBitStride fBlockRe gTapFold
                    let sIm := computableKroneckerBitStride fBlockIm gTapFold
                    let prodRe ← polyMulKroneckerSignedTreeWithCost sRe fBlockRe gTapFold
                    let prodIm ← polyMulKroneckerSignedTreeWithCost sIm fBlockIm gTapFold
                    pure (prodRe.toArray, prodIm.toArray))).1.size then
                    (BitCostM.ofFnM numBlocks (fun b : Fin numBlocks => do
                      let fBlockRe ← computableSpreadRowBlockReContiguousWithCost p_in q (6 * p') m1 r xRow b.val
                      let fBlockIm ← computableSpreadRowBlockImContiguousWithCost p_in q (6 * p') m1 r xRow b.val
                      let sRe := computableKroneckerBitStride fBlockRe gTapFold
                      let sIm := computableKroneckerBitStride fBlockIm gTapFold
                      let prodRe ← polyMulKroneckerSignedTreeWithCost sRe fBlockRe gTapFold
                      let prodIm ← polyMulKroneckerSignedTreeWithCost sIm fBlockIm gTapFold
                      pure (prodRe.toArray, prodIm.toArray))).1[b].2 else #[]
                  read1D prodImArr i)).1 k2.val) : BitCostM (ℤ × ℤ)))) =
      r * (2 * addBitCost (6 * p')) :=
    sumArrayCosts_ofFn_const r _ (2 * addBitCost (6 * p')) (fun _ _ => rfl)
  rw [hout]
  set fNew := fun b : Fin numBlocks => do
    let fBlockRe ← computableSpreadRowBlockReContiguousWithCost p_in q (6 * p') m1 r xRow b.val
    let fBlockIm ← computableSpreadRowBlockImContiguousWithCost p_in q (6 * p') m1 r xRow b.val
    let sRe := computableKroneckerBitStride fBlockRe gTapFold
    let sIm := computableKroneckerBitStride fBlockIm gTapFold
    let prodRe ← polyMulKroneckerSignedTreeWithCost sRe fBlockRe gTapFold
    let prodIm ← polyMulKroneckerSignedTreeWithCost sIm fBlockIm gTapFold
    pure (prodRe.toArray, prodIm.toArray)
  set fOld := fun b : Fin numBlocks =>
    let fBlockRe := computableSpreadRowBlockReContiguous p_in q m1 r xRow b.val
    let fBlockIm := computableSpreadRowBlockImContiguous p_in q m1 r xRow b.val
    let sRe := computableKroneckerBitStride fBlockRe gTapFold
    let sIm := computableKroneckerBitStride fBlockIm gTapFold
    let prodRe := polyMulKroneckerSignedComputable sRe fBlockRe gTapFold
    let prodIm := polyMulKroneckerSignedComputable sIm fBlockIm gTapFold
    let blockCost :=
      computableMulBitCost (fBlockRe.length * sRe) +
      computableMulBitCost (fBlockIm.length * sIm) +
      2 * W_eff * addBitCost sRe +
      2 * W_eff * addBitCost sIm
    ((prodRe.toArray, prodIm.toArray), blockCost)
  have hsum_new :
      sumArrayCosts (Array.ofFn fNew) =
        ∑ b ∈ Finset.range numBlocks, (if hb : b < numBlocks then (fNew ⟨b, hb⟩).2 else 0) :=
    sumArrayCosts_ofFn_eq_sum numBlocks fNew _ (fun b hb => by simp [hb])
  have hsum_old :
      sumArrayCosts (Array.ofFn fOld) =
        ∑ b ∈ Finset.range numBlocks, (if hb : b < numBlocks then (fOld ⟨b, hb⟩).2 else 0) :=
    sumArrayCosts_ofFn_eq_sum numBlocks fOld _ (fun b hb => by simp [hb])
  have hblock_le :
      ∑ b ∈ Finset.range numBlocks, (if hb : b < numBlocks then (fNew ⟨b, hb⟩).2 else 0) ≤
        ∑ b ∈ Finset.range numBlocks,
          (17 * (if hb : b < numBlocks then (fOld ⟨b, hb⟩).2 else 0) +
            4 * W_eff * addBitCost (6 * p')) := by
    refine Finset.sum_le_sum fun b hb => ?_
    have hb_lt : b < numBlocks := Finset.mem_range.mp hb
    rw [dif_pos hb_lt, dif_pos hb_lt]
    dsimp only [fNew, fOld, Bind.bind, Pure.pure]
    rw [computableSpreadRowBlockReContiguousWithCost_snd,
        computableSpreadRowBlockImContiguousWithCost_snd,
        computableSpreadRowBlockReContiguousWithCost_fst,
        computableSpreadRowBlockImContiguousWithCost_fst]
    set fRe := computableSpreadRowBlockReContiguous p_in q m1 r xRow b
    set fIm := computableSpreadRowBlockImContiguous p_in q m1 r xRow b
    set sRe := computableKroneckerBitStride fRe gTapFold
    set sIm := computableKroneckerBitStride fIm gTapFold
    have hsRe : 1 ≤ sRe := by dsimp [sRe, computableKroneckerBitStride]; omega
    have hsIm : 1 ≤ sIm := by dsimp [sIm, computableKroneckerBitStride]; omega
    have hlenRe : fRe.length = W_eff := by simp [fRe, computableSpreadRowBlockReContiguous, W_eff]
    have hlenIm : fIm.length = W_eff := by simp [fIm, computableSpreadRowBlockImContiguous, W_eff]
    have hprodRe := polyMulKroneckerSignedTreeWithCost_snd_le sRe hsRe fRe gTapFold (by omega)
    have hprodIm := polyMulKroneckerSignedTreeWithCost_snd_le sIm hsIm fIm gTapFold (by omega)
    have hW_add : effectiveFilterWidth m1 r * (2 * addBitCost (6 * p')) +
        effectiveFilterWidth m1 r * (2 * addBitCost (6 * p')) =
        4 * W_eff * addBitCost (6 * p') := by
      dsimp [W_eff]; ring
    rw [computableMulBitCost_eq, computableMulBitCost_eq]
    omega
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      smul_eq_mul] at hblock_le
  rw [hsum_new, hsum_old]
  linarith

theorem computableSpreadRowContiguousWithProgramCost_extra_le
    (p' r : ℕ) :
    let m1 := 2 * p'
    let W_eff := effectiveFilterWidth m1 r
    let numBlocks := kroneckerSpreadNumBlocks m1 r
    numBlocks * (8 * W_eff * addBitCost (6 * p')) + r * (2 * addBitCost (6 * p')) ≤
      7 * (r * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p'))) := by
  dsimp only
  have hcancel := kroneckerSpreadNumBlocks_mul_effectiveFilterWidth_le (2 * p') r
  have h1 :
      kroneckerSpreadNumBlocks (2 * p') r * (8 * effectiveFilterWidth (2 * p') r * addBitCost (6 * p')) =
        (kroneckerSpreadNumBlocks (2 * p') r * effectiveFilterWidth (2 * p') r) * (8 * addBitCost (6 * p')) := by
    ring
  have h2 :
      (kroneckerSpreadNumBlocks (2 * p') r * effectiveFilterWidth (2 * p') r) * (8 * addBitCost (6 * p')) ≤
        (2 * r) * (8 * addBitCost (6 * p')) :=
    Nat.mul_le_mul_right _ hcancel
  rw [h1]
  calc (kroneckerSpreadNumBlocks (2 * p') r * effectiveFilterWidth (2 * p') r) * (8 * addBitCost (6 * p')) +
        r * (2 * addBitCost (6 * p'))
      ≤ (2 * r) * (8 * addBitCost (6 * p')) + r * (2 * addBitCost (6 * p')) :=
        Nat.add_le_add_right h2 _
    _ = r * (27 * addBitCost (4 * p')) := by
        dsimp [addBitCost]; ring
    _ ≤ r * (112 * mulBitCost (4 * p') + 112 * addBitCost (4 * p')) := by
        refine Nat.mul_le_mul_left r ?_
        omega
    _ = 7 * (r * (16 * mulBitCost (4 * p') + 16 * addBitCost (4 * p'))) := by ring

/-- Costed leaf primitive for binary-tree chunk splitting (`costedSplitChunkLeaf`):
extracts the low `b` bits of `A` via `A - ((A >>> b) <<< b)` and charges `addBitCost b`. -/
def costedSplitChunkLeaf (b A : ℕ) : BitCostM (List ℕ) :=
  ([A - ((A >>> b) <<< b)], addBitCost b)

theorem costedSplitChunkLeaf_fst (b A : ℕ) :
    (costedSplitChunkLeaf b A).1 = [A % (2 ^ b)] := by
  dsimp only [costedSplitChunkLeaf]
  rw [nat_sub_shiftRight_shiftLeft_eq_mod_pow]

@[simp]
theorem costedSplitChunkLeaf_snd (b A : ℕ) :
    (costedSplitChunkLeaf b A).2 = addBitCost b := rfl

/-- Costed internal-node bit-shift split primitive for binary-tree chunk splitting
(`costedSplitChunkStep`):
splits `A` at bit-offset `b * k1` via `hi := A >>> (b * k1)` and `lo := A - (hi <<< (b * k1))`
and charges `addBitCost (k * b)` (real combined bit-width `k * b`). -/
def costedSplitChunkStep (b k k1 A : ℕ) : BitCostM (ℕ × ℕ) :=
  let shiftBits := b * k1
  let hi := A >>> shiftBits
  let lo := A - (hi <<< shiftBits)
  ((lo, hi), addBitCost (k * b))

theorem costedSplitChunkStep_fst (b k k1 A : ℕ) :
    (costedSplitChunkStep b k k1 A).1 = (A % ((2 ^ b) ^ k1), A / ((2 ^ b) ^ k1)) := by
  dsimp only [costedSplitChunkStep]
  rw [nat_sub_shiftRight_shiftLeft_eq_mod_pow, nat_shiftRight_eq_div_pow, pow_mul]

@[simp]
theorem costedSplitChunkStep_snd (b k k1 A : ℕ) :
    (costedSplitChunkStep b k k1 A).2 = addBitCost (k * b) := rfl

/-- Program-cost-accumulating helper for balanced divide-and-conquer binary-tree chunk splitting:
uses `costedSplitChunkLeaf` at leaves and `costedSplitChunkStep` at internal nodes, charging
`addBitCost (k * b)` at each internal node of size `k` (real combined bit-width `k * b`). -/
def splitChunksTreeAuxWithCost : ℕ → ℕ → ℕ → ℕ → BitCostM (List ℕ)
  | 0, _, _, _ => pure []
  | fuel + 1, b, k, A =>
    if k = 0 then pure []
    else if k = 1 then costedSplitChunkLeaf b A
    else do
      let k1 := natTreeLeftHalf k
      let k2 := natTreeRightHalf k
      let lh ← costedSplitChunkStep b k k1 A
      let l ← splitChunksTreeAuxWithCost fuel b k1 lh.1
      let r ← splitChunksTreeAuxWithCost fuel b k2 lh.2
      pure (l ++ r)

/-- Program-cost-accumulating balanced binary-tree chunk splitter (`splitChunksTreeWithProgramCost`):
uses `fuel = natTreeFuel k` ($\lceil \log_2 k \rceil + 2$ levels) and charges `addBitCost (k * b)`
at each internal node of size `k`. -/
def splitChunksTreeWithProgramCost (b k A : ℕ) : BitCostM (List ℕ) :=
  splitChunksTreeAuxWithCost (natTreeFuel k) b k A

theorem splitChunksTreeAuxWithCost_fst :
    ∀ fuel b k A : ℕ, (splitChunksTreeAuxWithCost fuel b k A).1 = splitChunksTreeAux fuel b k A
  | 0, _, _, _ => rfl
  | fuel + 1, b, k, A => by
    unfold splitChunksTreeAuxWithCost splitChunksTreeAux
    dsimp only [natTreeLeftHalf, natTreeRightHalf]
    split_ifs with h0 h1
    · rfl
    · exact costedSplitChunkLeaf_fst b A
    · simp only [BitCostM.bind_fst, BitCostM.pure_fst, costedSplitChunkStep_fst]
      rw [splitChunksTreeAuxWithCost_fst fuel b (k / 2),
          splitChunksTreeAuxWithCost_fst fuel b (k - k / 2)]

theorem splitChunksTreeAux_eq_splitChunks_of_le_pow :
    ∀ fuel b k A : ℕ, k ≤ 2 ^ fuel →
      splitChunksTreeAux (fuel + 1) b k A = splitChunks b k A
  | 0, b, k, A, hk => by
    have hk1 : k = 0 ∨ k = 1 := by omega
    rcases hk1 with rfl | rfl
    · rfl
    · simp [splitChunksTreeAux, splitChunks]
  | fuel + 1, b, k, A, hk => by
    unfold splitChunksTreeAux
    split_ifs with h0 h1
    · subst h0; rfl
    · subst h1; simp [splitChunks]
    · dsimp only
      have hk_pow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
      have hk1 : k / 2 ≤ 2 ^ fuel := by omega
      have hk2 : k - k / 2 ≤ 2 ^ fuel := by omega
      have hsum : k = k / 2 + (k - k / 2) := by omega
      rw [splitChunksTreeAux_eq_splitChunks_of_le_pow fuel b (k / 2) _ hk1,
          splitChunksTreeAux_eq_splitChunks_of_le_pow fuel b (k - k / 2) _ hk2]
      conv_rhs => rw [hsum, splitChunks_add]

@[simp]
theorem splitChunksTreeWithProgramCost_fst (b k A : ℕ) :
    (splitChunksTreeWithProgramCost b k A).1 = splitChunksTree b k A := by
  unfold splitChunksTreeWithProgramCost natTreeFuel
  rw [splitChunksTreeAuxWithCost_fst, natLog2Fuel_self, splitChunksTree_eq_splitChunks]
  exact splitChunksTreeAux_eq_splitChunks_of_le_pow (Nat.log2 k + 1) b k A
    (lt_two_pow_log2_succ k).le

theorem splitChunksTreeAuxWithCost_snd_le :
    ∀ fuel b k A : ℕ,
      (splitChunksTreeAuxWithCost fuel b k A).2 ≤ fuel * k * addBitCost b
  | 0, b, k, A => by simp [splitChunksTreeAuxWithCost, Pure.pure]
  | fuel + 1, b, k, A => by
    unfold splitChunksTreeAuxWithCost
    dsimp only [natTreeLeftHalf, natTreeRightHalf]
    split_ifs with h0 h1
    · simp [Pure.pure]
    · subst h1
      simp only [costedSplitChunkLeaf_snd]
      have h1_le : 1 ≤ (fuel + 1) * 1 := by omega
      simpa only [one_mul] using Nat.mul_le_mul_right (addBitCost b) h1_le
    · simp only [BitCostM.bind_snd, BitCostM.pure_snd, costedSplitChunkStep_snd, add_zero]
      set lh := (costedSplitChunkStep b k (k / 2) A).1
      have ih1 := splitChunksTreeAuxWithCost_snd_le fuel b (k / 2) lh.1
      have ih2 := splitChunksTreeAuxWithCost_snd_le fuel b (k - k / 2) lh.2
      have hadd_kb : addBitCost (k * b) = k * addBitCost b := rfl
      have hsum :
          k * addBitCost b + (fuel * (k / 2) * addBitCost b + fuel * (k - k / 2) * addBitCost b) =
            (fuel + 1) * k * addBitCost b := by
        have hk : k / 2 + (k - k / 2) = k := by omega
        calc k * addBitCost b + (fuel * (k / 2) * addBitCost b + fuel * (k - k / 2) * addBitCost b)
            = fuel * (k / 2 + (k - k / 2)) * addBitCost b + k * addBitCost b := by ring
          _ = fuel * k * addBitCost b + k * addBitCost b := by rw [hk]
          _ = (fuel + 1) * k * addBitCost b := by ring
      linarith

theorem splitChunksTreeWithProgramCost_snd_le (b k A : ℕ) :
    (splitChunksTreeWithProgramCost b k A).2 ≤ (Nat.log2 k + 2) * k * addBitCost b := by
  unfold splitChunksTreeWithProgramCost natTreeFuel
  rw [natLog2Fuel_self]
  exact splitChunksTreeAuxWithCost_snd_le (Nat.log2 k + 2) b k A

/-- Costed leaf primitive for binary-tree radix reconstruction (`costedReconstructChunkLeaf`):
returns chunk `c` and charges `addBitCost (3 * b)`. -/
def costedReconstructChunkLeaf (b c : ℕ) : BitCostM ℕ :=
  (c, addBitCost (3 * b))

@[simp]
theorem costedReconstructChunkLeaf_fst (b c : ℕ) :
    (costedReconstructChunkLeaf b c).1 = c := rfl

@[simp]
theorem costedReconstructChunkLeaf_snd (b c : ℕ) :
    (costedReconstructChunkLeaf b c).2 = addBitCost (3 * b) := rfl

/-- Costed internal-node bit-shift-and-add primitive for binary-tree radix reconstruction
(`costedReconstructChunkStep`):
combines low half `l` and high half `r` at bit-offset `b * k1` via `l + (r <<< (b * k1))`
and charges `addBitCost (k * (3 * b))` (real combined bit-width `3 * k * b`). -/
def costedReconstructChunkStep (b k k1 l r : ℕ) : BitCostM ℕ :=
  let shiftBits := b * k1
  (l + (r <<< shiftBits), addBitCost (k * (3 * b)))

theorem costedReconstructChunkStep_fst (b k k1 l r : ℕ) :
    (costedReconstructChunkStep b k k1 l r).1 = l + ((2 ^ b) ^ k1) * r := by
  dsimp only [costedReconstructChunkStep]
  rw [nat_shiftLeft_eq_mul_pow, ← pow_mul, mul_comm]

@[simp]
theorem costedReconstructChunkStep_snd (b k k1 l r : ℕ) :
    (costedReconstructChunkStep b k k1 l r).2 = addBitCost (k * (3 * b)) := rfl

/-- Program-cost-accumulating helper for balanced divide-and-conquer binary-tree radix reconstruction:
uses `costedReconstructChunkLeaf` at leaves and `costedReconstructChunkStep` at internal nodes,
charging `addBitCost (k * (3 * b))` at each internal node of size `k` (real combined bit-width `3 * k * b`). -/
def reconstructChunksTreeAuxWithCost : ℕ → ℕ → ℕ → List ℕ → BitCostM ℕ
  | 0, _, _, _ => pure 0
  | fuel + 1, b, k, cs =>
    if k = 0 then pure 0
    else if k = 1 then costedReconstructChunkLeaf b (cs.headD 0)
    else do
      let k1 := natTreeLeftHalf k
      let k2 := natTreeRightHalf k
      let l ← reconstructChunksTreeAuxWithCost fuel b k1 (cs.take k1)
      let r ← reconstructChunksTreeAuxWithCost fuel b k2 (cs.drop k1)
      costedReconstructChunkStep b k k1 l r

/-- Program-cost-accumulating balanced binary-tree radix reconstruction (`reconstructChunksTreeWithProgramCost`):
uses `fuel = natTreeFuel cs.length` ($\lceil \log_2 |cs| \rceil + 2$ levels) and charges
`addBitCost (k * (3 * b))` at each internal node of size `k`. -/
def reconstructChunksTreeWithProgramCost (b : ℕ) (cs : List ℕ) : BitCostM ℕ :=
  reconstructChunksTreeAuxWithCost (natTreeFuel cs.length) b cs.length cs

theorem reconstructChunksTreeAuxWithCost_fst :
    ∀ (fuel b k : ℕ) (cs : List ℕ),
      (reconstructChunksTreeAuxWithCost fuel b k cs).1 = reconstructChunksTreeAux fuel (2 ^ b) k cs
  | 0, _, _, _ => rfl
  | fuel + 1, b, k, cs => by
    unfold reconstructChunksTreeAuxWithCost reconstructChunksTreeAux
    dsimp only [natTreeLeftHalf, natTreeRightHalf]
    split_ifs with h0 h1
    · rfl
    · rfl
    · simp only [BitCostM.bind_fst, costedReconstructChunkStep_fst]
      rw [reconstructChunksTreeAuxWithCost_fst fuel b (k / 2),
          reconstructChunksTreeAuxWithCost_fst fuel b (k - k / 2)]

theorem reconstructChunksTreeAux_eq_evalRadix_of_le_pow :
    ∀ (fuel B k : ℕ) (cs : List ℕ), cs.length = k → k ≤ 2 ^ fuel →
      reconstructChunksTreeAux (fuel + 1) B k cs = evalRadix B cs
  | 0, B, k, cs, hlen, hk => by
    have hk1 : k = 0 ∨ k = 1 := by omega
    rcases hk1 with rfl | rfl
    · obtain rfl : cs = [] := List.eq_nil_of_length_eq_zero hlen
      rfl
    · obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := List.length_eq_one_iff.mp hlen
      simp [reconstructChunksTreeAux, evalRadix]
  | fuel + 1, B, k, cs, hlen, hk => by
    unfold reconstructChunksTreeAux
    split_ifs with h0 h1
    · subst h0
      obtain rfl : cs = [] := List.eq_nil_of_length_eq_zero hlen
      rfl
    · subst h1
      obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := List.length_eq_one_iff.mp hlen
      simp [evalRadix]
    · dsimp only
      have hk_pow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
      have hk1 : k / 2 ≤ 2 ^ fuel := by omega
      have hk2 : k - k / 2 ≤ 2 ^ fuel := by omega
      have hlen1 : (cs.take (k / 2)).length = k / 2 := by simp [hlen]; omega
      have hlen2 : (cs.drop (k / 2)).length = k - k / 2 := by simp [hlen]
      rw [reconstructChunksTreeAux_eq_evalRadix_of_le_pow fuel B (k / 2) (cs.take (k / 2)) hlen1 hk1,
          reconstructChunksTreeAux_eq_evalRadix_of_le_pow fuel B (k - k / 2) (cs.drop (k / 2)) hlen2 hk2]
      conv_rhs => rw [← List.take_append_drop (k / 2) cs, evalRadix_append, hlen1]

@[simp]
theorem reconstructChunksTreeWithProgramCost_fst (b : ℕ) (cs : List ℕ) :
    (reconstructChunksTreeWithProgramCost b cs).1 = reconstructChunksTree b cs := by
  unfold reconstructChunksTreeWithProgramCost natTreeFuel
  rw [reconstructChunksTreeAuxWithCost_fst, natLog2Fuel_self, reconstructChunksTree_eq_evalRadix]
  exact reconstructChunksTreeAux_eq_evalRadix_of_le_pow (Nat.log2 cs.length + 1) (2 ^ b) cs.length cs rfl
    (lt_two_pow_log2_succ cs.length).le

theorem reconstructChunksTreeAuxWithCost_snd_le :
    ∀ (fuel b k : ℕ) (cs : List ℕ),
      (reconstructChunksTreeAuxWithCost fuel b k cs).2 ≤
        3 * fuel * k * addBitCost b
  | 0, b, k, _ => by simp [reconstructChunksTreeAuxWithCost, Pure.pure]
  | fuel + 1, b, k, cs => by
    unfold reconstructChunksTreeAuxWithCost
    dsimp only [natTreeLeftHalf, natTreeRightHalf]
    split_ifs with h0 h1
    · simp [Pure.pure]
    · subst h1
      simp only [costedReconstructChunkLeaf_snd]
      have h3b : addBitCost (3 * b) = 3 * addBitCost b := rfl
      rw [h3b]
      have h1_le : 3 ≤ 3 * (fuel + 1) * 1 := by omega
      simpa only [one_mul] using Nat.mul_le_mul_right (addBitCost b) h1_le
    · simp only [BitCostM.bind_snd, costedReconstructChunkStep_snd]
      have ih1 := reconstructChunksTreeAuxWithCost_snd_le fuel b (k / 2) (cs.take (k / 2))
      have ih2 := reconstructChunksTreeAuxWithCost_snd_le fuel b (k - k / 2) (cs.drop (k / 2))
      have hadd_k3b : addBitCost (k * (3 * b)) = 3 * k * addBitCost b := by
        dsimp [addBitCost]; ring
      have hsum :
          3 * fuel * (k / 2) * addBitCost b +
            (3 * fuel * (k - k / 2) * addBitCost b + 3 * k * addBitCost b) =
            3 * (fuel + 1) * k * addBitCost b := by
        have hk : k / 2 + (k - k / 2) = k := by omega
        calc 3 * fuel * (k / 2) * addBitCost b +
              (3 * fuel * (k - k / 2) * addBitCost b + 3 * k * addBitCost b)
            = 3 * fuel * (k / 2 + (k - k / 2)) * addBitCost b + 3 * k * addBitCost b := by ring
          _ = 3 * fuel * k * addBitCost b + 3 * k * addBitCost b := by rw [hk]
          _ = 3 * (fuel + 1) * k * addBitCost b := by ring
      linarith

theorem reconstructChunksTreeWithProgramCost_snd_le (b : ℕ) (cs : List ℕ) :
    (reconstructChunksTreeWithProgramCost b cs).2 ≤
      3 * (Nat.log2 cs.length + 2) * cs.length * addBitCost b := by
  unfold reconstructChunksTreeWithProgramCost natTreeFuel
  rw [natLog2Fuel_self]
  exact reconstructChunksTreeAuxWithCost_snd_le (Nat.log2 cs.length + 2) b cs.length cs

/-- **Program-Cost-Accumulating Computable `BaseRadix2FFT` Core (`computableBaseRadix2FFTCoreWithProgramCost`, `[MS]` §7)**:
100% computable (`def`, zero `noncomputable`, zero `Real`, zero `Complex`) Cooley-Tukey radix-2 FFT core
over `Array (ℤ × ℤ)` at leaf working precision `q_leaf = 2 * p + K + 8` that executes in a single
monadic pass over `Monad BitCostM` (without duplicate `cellPairs`/`outArr` passes):
- at `s = 0`: `costedGRescale p_in q_leaf (4 * q_leaf) (read1D xArr 0)`,
- at `s + 1`: recursive even/odd half-length transforms `Y0`, `Y1` followed by `BitCostM.ofFnM (2 ^ (s + 1))`
  butterfly cells calling `costedGMulScaled (q_leaf + 2) (4 * q_leaf)` and `costedButterflyAvg (4 * q_leaf)`. -/
def computableBaseRadix2FFTCoreWithProgramCost
    (p_in q_leaf : ℕ) (twiddles : Array (Array (ℤ × ℤ))) :
    ℕ → Array (ℤ × ℤ) → BitCostM (Array (ℤ × ℤ))
  | 0, xArr => do
    let z0 ← costedGRescale p_in q_leaf (4 * q_leaf) (read1D xArr 0)
    pure #[z0]
  | s + 1, xArr => do
    let xEven := Array.ofFn (fun j : Fin (2 ^ s) => read1D xArr (2 * j.val))
    let xOdd := Array.ofFn (fun j : Fin (2 ^ s) => read1D xArr (2 * j.val + 1))
    let Y0 ← computableBaseRadix2FFTCoreWithProgramCost p_in q_leaf twiddles s xEven
    let Y1 ← computableBaseRadix2FFTCoreWithProgramCost p_in q_leaf twiddles s xOdd
    let twStage := twiddles.getD s #[]
    BitCostM.ofFnM (2 ^ (s + 1)) (fun u : Fin (2 ^ (s + 1)) => do
      let y0 := read1D Y0 (u.val % 2 ^ s)
      let y1 := read1D Y1 (u.val % 2 ^ s)
      let ω := read1D twStage u.val
      let prod ← costedGMulScaled (q_leaf + 2) (4 * q_leaf) ω y1
      costedButterflyAvg (4 * q_leaf) y0 prod)

/-- **Program-Cost-Accumulating Computable `BaseRadix2FFT` (`computableBaseRadix2FFTWithProgramCost`, `[MS]` §7)**:
Executes `computableBaseRadix2FFTCoreWithProgramCost` at `q_leaf = 2 * p + K + 8` followed by a
sequential output rescaling pass `outScan` to target precision `p` inside `Monad BitCostM`. -/
def computableBaseRadix2FFTWithProgramCost
    (p_in p K : ℕ) (twiddles : Array (Array (ℤ × ℤ))) (xArr : Array (ℤ × ℤ)) :
    BitCostM (Array (ℤ × ℤ)) := do
  let q_leaf := 2 * p + K + 8
  let R := 2 ^ K
  let coreArr ← computableBaseRadix2FFTCoreWithProgramCost p_in q_leaf twiddles K xArr
  let outScan := runSequentialScanCostedSteps (fun u =>
    costedGRescale q_leaf p (4 * q_leaf) (read1D coreArr u)) R
  BitCostM.tick outScan.2.2
  pure outScan.1

theorem toScaledComplex_computableBaseRadix2FFTCoreWithProgramCost_eq
    (p_in q_leaf K : ℕ)
    (twiddles : Array (Array (ℤ × ℤ)))
    (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
      read1D (twiddles.getD s #[]) u =
        (realQuantizeInt q_leaf (stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))).re,
         realQuantizeInt q_leaf (stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))).im))
    (s : ℕ) (hs : s ≤ K)
    (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < 2 ^ s, x k = toScaledComplex p_in (read1D xArr k))
    (u : ℕ) (hu : u < 2 ^ s) :
    toScaledComplex q_leaf
      (read1D (computableBaseRadix2FFTCoreWithProgramCost p_in q_leaf twiddles s xArr).1 u) =
      baseRadix2FFTQuantizedCore q_leaf s x u := by
  induction s generalizing xArr x u with
  | zero =>
    have hu0 : u = 0 := by simpa using hu
    subst hu0
    dsimp only [computableBaseRadix2FFTCoreWithProgramCost, baseRadix2FFTQuantizedCore,
      Bind.bind, Pure.pure, costedGRescale]
    have hread : read1D #[gRescale p_in q_leaf (read1D xArr 0)] 0 = gRescale p_in q_leaf (read1D xArr 0) := rfl
    rw [hread, toScaledComplex_gRescale_eq, ← hx 0 (by decide)]
  | succ s ih =>
    simp only [computableBaseRadix2FFTCoreWithProgramCost, baseRadix2FFTQuantizedCore,
      BitCostM.bind_fst, BitCostM.ofFnM_fst]
    rw [read1D_ofFn_of_lt (2 ^ (s + 1)) _ hu]
    dsimp only [Bind.bind, costedButterflyAvg, costedGMulScaled]
    rw [toScaledComplex_divRoundPow2_one_eq_complexQuantize_avg,
        toScaledComplex_gMulScaled_eq_complexQuantize_mul]
    have hu_mod : u % 2 ^ s < 2 ^ s := Nat.mod_lt u (pow_pos zero_lt_two s)
    have hs_lt : s < K := Nat.lt_of_succ_le hs
    have hxEven : ∀ j < 2 ^ s,
        x (2 * j) = toScaledComplex p_in (read1D (Array.ofFn (fun j : Fin (2 ^ s) => read1D xArr (2 * j.val))) j) := by
      intro j hj
      rw [read1D_ofFn_of_lt (2 ^ s) _ hj]
      exact hx (2 * j) (by rw [pow_succ']; omega)
    have hxOdd : ∀ j < 2 ^ s,
        x (2 * j + 1) = toScaledComplex p_in (read1D (Array.ofFn (fun j : Fin (2 ^ s) => read1D xArr (2 * j.val + 1))) j) := by
      intro j hj
      rw [read1D_ofFn_of_lt (2 ^ s) _ hj]
      exact hx (2 * j + 1) (by rw [pow_succ']; omega)
    have hY0 := ih (Nat.le_of_succ_le hs)
      (Array.ofFn (fun j : Fin (2 ^ s) => read1D xArr (2 * j.val)))
      (fun j => x (2 * j)) hxEven (u % 2 ^ s) hu_mod
    have hY1 := ih (Nat.le_of_succ_le hs)
      (Array.ofFn (fun j : Fin (2 ^ s) => read1D xArr (2 * j.val + 1)))
      (fun j => x (2 * j + 1)) hxOdd (u % 2 ^ s) hu_mod
    rw [baseRadix2FFTQuantizedCore_mod] at hY0 hY1
    have hω :
        toScaledComplex q_leaf (read1D (twiddles.getD s #[]) u) =
          complexQuantize q_leaf
            (stdChar (((u % 2 ^ (s + 1) : ℕ) : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))) := by
      rw [htw s hs_lt u hu, Nat.mod_eq_of_lt hu]
      exact toScaledComplex_realQuantizeInt_pair q_leaf _
    rw [hY0, hY1, hω]

theorem toScaledComplex_computableBaseRadix2FFTWithProgramCost_eq
    (p_in p K : ℕ)
    (twiddles : Array (Array (ℤ × ℤ)))
    (htw : ∀ s < K, ∀ u < 2 ^ (s + 1),
      read1D (twiddles.getD s #[]) u =
        (realQuantizeInt (2 * p + K + 8) (stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))).re,
         realQuantizeInt (2 * p + K + 8) (stdChar ((u : ℝ) / ((2 ^ (s + 1) : ℕ) : ℝ))).im))
    (xArr : Array (ℤ × ℤ)) (x : ℕ → ℂ)
    (hx : ∀ k < 2 ^ K, x k = toScaledComplex p_in (read1D xArr k))
    (u : ℕ) (hu : u < 2 ^ K) :
    toScaledComplex p
      (read1D (computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr).1 u) =
      baseRadix2FFTQuantized p K x u := by
  unfold computableBaseRadix2FFTWithProgramCost baseRadix2FFTQuantized
  dsimp only [Bind.bind, Pure.pure, BitCostM.tick, costedGRescale, runSequentialScanCostedSteps]
  rw [read1D_runSequentialScanSteps_eq _ (2 ^ K) u hu,
      toScaledComplex_gRescale_eq,
      toScaledComplex_computableBaseRadix2FFTCoreWithProgramCost_eq p_in (2 * p + K + 8) K
        twiddles htw K le_rfl xArr x hx u hu]

theorem computableBaseRadix2FFTCoreWithProgramCost_snd_eq
    (p_in q_leaf : ℕ) (twiddles : Array (Array (ℤ × ℤ))) (s : ℕ) (xArr : Array (ℤ × ℤ)) :
    (computableBaseRadix2FFTCoreWithProgramCost p_in q_leaf twiddles s xArr).2 =
      2 ^ s * s * (4 * mulBitCost (4 * q_leaf) + 6 * addBitCost (4 * q_leaf)) +
        2 ^ s * (2 * addBitCost (4 * q_leaf)) := by
  induction s generalizing xArr with
  | zero =>
    simp [computableBaseRadix2FFTCoreWithProgramCost, Bind.bind, Pure.pure, costedGRescale]
  | succ s ih =>
    simp only [computableBaseRadix2FFTCoreWithProgramCost, BitCostM.bind_snd]
    rw [ih, ih,
        BitCostM.ofFnM_snd_const (2 ^ (s + 1)) (4 * mulBitCost (4 * q_leaf) + 6 * addBitCost (4 * q_leaf)) _
          (fun _ => by
            dsimp only [Bind.bind, costedGMulScaled, costedButterflyAvg]
            rw [computableMulBitCost_eq]
            ring),
        pow_succ]
    ring

theorem computableBaseRadix2FFTWithProgramCost_snd_eq
    (p_in p K : ℕ) (twiddles : Array (Array (ℤ × ℤ))) (xArr : Array (ℤ × ℤ)) :
    let q_leaf := 2 * p + K + 8
    (computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr).2 =
      2 ^ K * K * (4 * mulBitCost (4 * q_leaf) + 6 * addBitCost (4 * q_leaf)) +
        2 ^ K * (4 * addBitCost (4 * q_leaf)) := by
  dsimp only [computableBaseRadix2FFTWithProgramCost, Bind.bind, Pure.pure, BitCostM.tick]
  have hout :
      (runSequentialScanCostedSteps (fun u =>
        costedGRescale (2 * p + K + 8) p (4 * (2 * p + K + 8))
          (read1D (computableBaseRadix2FFTCoreWithProgramCost p_in (2 * p + K + 8) twiddles K xArr).1 u))
        (2 ^ K)).2.2 =
      2 ^ K * (2 * addBitCost (4 * (2 * p + K + 8))) :=
    runSequentialScanCostedSteps_cost_const _ (2 ^ K) _ (fun _ _ => rfl)
  rw [computableBaseRadix2FFTCoreWithProgramCost_snd_eq, hout]
  ring

theorem computableBaseRadix2FFTWithProgramCost_snd_le
    (p_in p K : ℕ) (hp : 8 ≤ p) (hK : K ≤ 5 * p)
    (twiddles : Array (Array (ℤ × ℤ))) (xArr : Array (ℤ × ℤ)) :
    ((computableBaseRadix2FFTWithProgramCost p_in p K twiddles xArr).2 : ℝ) ≤
      6272 * (QuantizedFastDFTSpec.base p (2 ^ K)).intrinsicCostRadix2Leaf := by
  dsimp only [QuantizedFastDFTSpec.intrinsicCostRadix2Leaf]
  rw [nat_log2_two_pow, computableBaseRadix2FFTWithProgramCost_snd_eq]
  set q_leaf := 2 * p + K + 8
  have hq_le : 4 * q_leaf ≤ 32 * p := by
    dsimp [q_leaf]
    omega
  have hmul_mono : mulBitCost (4 * q_leaf) ≤ mulBitCost (32 * p) :=
    mulBitCost_mono hq_le
  have hmul_32 : mulBitCost (32 * p) ≤ 896 * mulBitCost p := by
    have h := mulBitCost_mul_le 32 p
    have hconst : mulBitCostScaleFactor 32 = 896 := by decide
    rwa [hconst] at h
  have hmul_q : mulBitCost (4 * q_leaf) ≤ 1568 * mulBitCost p := by omega
  have hadd_q : addBitCost (4 * q_leaf) ≤ 32 * addBitCost p := by
    dsimp [addBitCost]
    exact hq_le
  have hstep :
      4 * mulBitCost (4 * q_leaf) + 6 * addBitCost (4 * q_leaf) ≤
        6272 * (mulBitCost p + addBitCost p) := by
    omega
  have hout :
      4 * addBitCost (4 * q_leaf) ≤ 6272 * (mulBitCost p + addBitCost p) := by
    omega
  have hnat :
      2 ^ K * K * (4 * mulBitCost (4 * q_leaf) + 6 * addBitCost (4 * q_leaf)) +
        2 ^ K * (4 * addBitCost (4 * q_leaf)) ≤
      6272 * (2 ^ K * (K + 1) * (mulBitCost p + addBitCost p)) := by
    calc 2 ^ K * K * (4 * mulBitCost (4 * q_leaf) + 6 * addBitCost (4 * q_leaf)) +
          2 ^ K * (4 * addBitCost (4 * q_leaf))
        ≤ 2 ^ K * K * (6272 * (mulBitCost p + addBitCost p)) +
          2 ^ K * (6272 * (mulBitCost p + addBitCost p)) :=
          Nat.add_le_add (Nat.mul_le_mul_left (2 ^ K * K) hstep) (Nat.mul_le_mul_left (2 ^ K) hout)
      _ = 6272 * (2 ^ K * (K + 1) * (mulBitCost p + addBitCost p)) := by ring
  exact_mod_cast hnat

end IntMul
