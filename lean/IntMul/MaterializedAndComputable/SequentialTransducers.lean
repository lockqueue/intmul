import IntMul.MaterializedAndComputable.MaterializedArrays

/-!
# Step-Instrumented Record-Level Sequential Array Transducers & Linear Head-Movement Semantics
-/

namespace IntMul

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators

/-! ## Explicit Multitape Sequential Turing Machine State & Linear Head-Movement Semantics -/

/-- Configuration of a 3-tape sequential unshuffle machine (`MultiTapeUnshuffleState`, `[MS]` §§3.2, 3.4 (Lemma 3.3)):
- `inHead : ℕ` is the read head position on the input tape (advancing by `+1` at every step),
- `evenTape : Array α` is the sequential write-only output tape for even-indexed records,
- `oddTape : Array α` is the sequential write-only output tape for odd-indexed records,
- `steps : ℕ` is the runtime head-step counter incremented by `+1` at every single step. -/
structure MultiTapeUnshuffleState (α : Type*) where
  inHead : ℕ
  evenTape : Array α
  oddTape : Array α
  steps : ℕ

/-- Single sequential head-step of the 3-tape unshuffle machine:
reads `inTape st.inHead`, advances `inHead` by `+1`, appends (`Array.push`, advancing the
corresponding write head by `+1` and the other write head by `0`) to `evenTape` or `oddTape`,
and increments the runtime step counter `st.steps` by `+1`. -/
def unshuffleHeadStep {α : Type*} (inTape : ℕ → α) (st : MultiTapeUnshuffleState α) :
    MultiTapeUnshuffleState α :=
  let x := inTape st.inHead
  if st.inHead % 2 = 0 then
    ⟨st.inHead + 1, st.evenTape.push x, st.oddTape, st.steps + 1⟩
  else
    ⟨st.inHead + 1, st.evenTape, st.oddTape.push x, st.steps + 1⟩

/-- Execute `n` single-head steps of `unshuffleHeadStep` starting from empty output tapes, `inHead = 0`, and `steps = 0`. -/
def runUnshuffleSteps {α : Type*} (inTape : ℕ → α) : ℕ → MultiTapeUnshuffleState α
  | 0 => ⟨0, #[], #[], 0⟩
  | n + 1 => unshuffleHeadStep inTape (runUnshuffleSteps inTape n)

@[simp]
theorem runUnshuffleSteps_inHead {α : Type*} (inTape : ℕ → α) (n : ℕ) :
    (runUnshuffleSteps inTape n).inHead = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [runUnshuffleSteps, unshuffleHeadStep]
    split_ifs <;> simp [ih]

@[simp]
theorem runUnshuffleSteps_steps {α : Type*} (inTape : ℕ → α) (n : ℕ) :
    (runUnshuffleSteps inTape n).steps = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [runUnshuffleSteps, unshuffleHeadStep]
    split_ifs <;> simp [ih]

/-- After `2 * k` single-head steps of `runUnshuffleSteps`:
`evenTape` has size `k` with `evenTape[i] = inTape (2 * i)`, and
`oddTape` has size `k` with `oddTape[i] = inTape (2 * i + 1)`. -/
theorem runUnshuffleSteps_two_mul_spec {α : Type*} [Zero α] (inTape : ℕ → α) (k : ℕ) :
    (runUnshuffleSteps inTape (2 * k)).evenTape.size = k ∧
    (runUnshuffleSteps inTape (2 * k)).oddTape.size = k ∧
    (∀ i < k, read1D (runUnshuffleSteps inTape (2 * k)).evenTape i = inTape (2 * i)) ∧
    (∀ i < k, read1D (runUnshuffleSteps inTape (2 * k)).oddTape i = inTape (2 * i + 1)) := by
  induction k with
  | zero =>
    refine ⟨rfl, rfl, ?_, ?_⟩ <;> (intro i hi; omega)
  | succ k ih =>
    rcases ih with ⟨he_sz, ho_sz, he_val, ho_val⟩
    have hstep : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [hstep]
    dsimp only [runUnshuffleSteps, unshuffleHeadStep]
    have hhead_even : (runUnshuffleSteps inTape (2 * k)).inHead = 2 * k :=
      runUnshuffleSteps_inHead inTape (2 * k)
    have hmod_even : (runUnshuffleSteps inTape (2 * k)).inHead % 2 = 0 := by omega
    simp only [hmod_even, ↓reduceIte]
    have hmod_odd : (2 * k + 1) % 2 ≠ 0 := by omega
    simp only [hhead_even, hmod_odd, ↓reduceIte]
    refine ⟨by rw [Array.size_push, he_sz], by rw [Array.size_push, ho_sz], ?_, ?_⟩
    · intro i hi
      rw [read1D_push _ _ i (by omega), he_sz]
      split_ifs with hlt
      · exact he_val i hlt
      · have hi_eq : i = k := by omega
        subst hi_eq
        rfl
    · intro i hi
      rw [read1D_push _ _ i (by omega), ho_sz]
      split_ifs with hlt
      · exact ho_val i hlt
      · have hi_eq : i = k := by omega
        subst hi_eq
        rfl

/-- Sequential concatenation of `evenTape` and `oddTape` produced by `runUnshuffleSteps`. -/
def readUnshuffleOutput {α : Type*} [Zero α] (half : ℕ) (st : MultiTapeUnshuffleState α) (idx : ℕ) : α :=
  if idx < half then read1D st.evenTape idx else read1D st.oddTape (idx - half)

/-- **Multitape Linear Head-Movement Correctness of `unshufflePass` (`runUnshuffleSteps_eq_unshufflePass`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
After `2 * half` sequential head steps (each advancing `inHead` by `+1` and appending `1` record
to either `evenTape` or `oddTape`), `readUnshuffleOutput half (runUnshuffleSteps inTape (2 * half))`
equals `unshufflePass half inTape` on all `idx < 2 * half`. -/
theorem runUnshuffleSteps_eq_unshufflePass {α : Type*} [Zero α]
    (half : ℕ) (inTape : ℕ → α) (idx : ℕ) (hidx : idx < 2 * half) :
    readUnshuffleOutput half (runUnshuffleSteps inTape (2 * half)) idx =
      unshufflePass half inTape idx := by
  obtain ⟨_, _, he_val, ho_val⟩ := runUnshuffleSteps_two_mul_spec inTape half
  unfold readUnshuffleOutput unshufflePass
  split_ifs with hlt
  · exact he_val idx hlt
  · exact ho_val (idx - half) (by omega)

/-- Configuration of a 3-tape sequential run-interleaving machine (`MultiTapeRunInterleaveState`, `[MS]` §§3.2, 3.4 (Lemma 3.3)):
- `topHead : ℕ` is the read head on `topTape`,
- `botHead : ℕ` is the read head on `botTape`,
- `outTape : Array α` is the sequential write-only output tape,
- `steps : ℕ` is the runtime head-step counter incremented by `+1` at every single step. -/
structure MultiTapeRunInterleaveState (α : Type*) where
  topHead : ℕ
  botHead : ℕ
  outTape : Array α
  steps : ℕ

/-- Single sequential head-step of the 3-tape run-interleaving machine for run length `r`:
at output step `idx = st.outTape.size`, if `(idx / r) % 2 = 0` it reads `topTape st.topHead`,
advances `topHead` by `+1` (`botHead` by `0`), pushes onto `outTape`, and increments `st.steps` by `+1`;
otherwise it reads `botTape st.botHead`, advances `botHead` by `+1` (`topHead` by `0`), pushes onto `outTape`,
and increments `st.steps` by `+1`. -/
def interleaveRunsHeadStep {α : Type*} (r : ℕ) (topTape botTape : ℕ → α)
    (st : MultiTapeRunInterleaveState α) : MultiTapeRunInterleaveState α :=
  let idx := st.outTape.size
  if (idx / r) % 2 = 0 then
    ⟨st.topHead + 1, st.botHead, st.outTape.push (topTape st.topHead), st.steps + 1⟩
  else
    ⟨st.topHead, st.botHead + 1, st.outTape.push (botTape st.botHead), st.steps + 1⟩

/-- Execute `n` single-head steps of `interleaveRunsHeadStep`. -/
def runInterleaveRunsSteps {α : Type*} (r : ℕ) (topTape botTape : ℕ → α) :
    ℕ → MultiTapeRunInterleaveState α
  | 0 => ⟨0, 0, #[], 0⟩
  | n + 1 => interleaveRunsHeadStep r topTape botTape (runInterleaveRunsSteps r topTape botTape n)

@[simp]
theorem size_runInterleaveRunsSteps {α : Type*} (r : ℕ) (topTape botTape : ℕ → α) (n : ℕ) :
    (runInterleaveRunsSteps r topTape botTape n).outTape.size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [runInterleaveRunsSteps, interleaveRunsHeadStep]
    split_ifs <;> simp [ih]

@[simp]
theorem runInterleaveRunsSteps_steps {α : Type*} (r : ℕ) (topTape botTape : ℕ → α) (n : ℕ) :
    (runInterleaveRunsSteps r topTape botTape n).steps = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [runInterleaveRunsSteps, interleaveRunsHeadStep]
    split_ifs <;> simp [ih]

/-- Exact head-position invariant for `runInterleaveRunsSteps`: after `n` single-head steps (`0 < r`),
if `j1 = n / r` and `i = n % r`, then:
- when `j1 % 2 = 0`, `topHead = (j1 / 2) * r + i` and `botHead = (j1 / 2) * r`,
- when `j1 % 2 ≠ 0`, `topHead = (j1 / 2 + 1) * r` and `botHead = (j1 / 2) * r + i`. -/
theorem runInterleaveRunsSteps_heads {α : Type*} (r : ℕ) (hr : 0 < r)
    (topTape botTape : ℕ → α) (n : ℕ) :
    (runInterleaveRunsSteps r topTape botTape n).topHead =
      (if (n / r) % 2 = 0 then ((n / r) / 2) * r + n % r else ((n / r) / 2 + 1) * r) ∧
    (runInterleaveRunsSteps r topTape botTape n).botHead =
      (if (n / r) % 2 = 0 then ((n / r) / 2) * r else ((n / r) / 2) * r + n % r) := by
  induction n with
  | zero =>
    simp [runInterleaveRunsSteps]
  | succ n ih =>
    rcases ih with ⟨htop, hbot⟩
    dsimp only [runInterleaveRunsSteps, interleaveRunsHeadStep]
    rw [size_runInterleaveRunsSteps]
    have hdiv_mod := (Nat.div_add_mod n r).symm
    have hmod_lt : n % r < r := Nat.mod_lt n hr
    by_cases hwrap : n % r + 1 < r
    · have hdiv_succ : (n + 1) / r = n / r := by
        have h1 : n + 1 = (n % r + 1) + (n / r) * r := by
          calc n + 1 = (r * (n / r) + n % r) + 1 := by rw [← hdiv_mod]
            _ = (n % r + 1) + (n / r) * r := by ring
        rw [h1, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt hwrap, zero_add]
      have hmod_succ : (n + 1) % r = n % r + 1 := by
        have h1 : n + 1 = (n % r + 1) + (n / r) * r := by
          calc n + 1 = (r * (n / r) + n % r) + 1 := by rw [← hdiv_mod]
            _ = (n % r + 1) + (n / r) * r := by ring
        rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hwrap]
      rw [hdiv_succ, hmod_succ]
      split_ifs with hpar <;> simp [htop, hbot, hpar] <;> omega
    · have hmod_eq : n % r + 1 = r := by omega
      have hdiv_succ : (n + 1) / r = n / r + 1 := by
        have h1 : n + 1 = (n / r + 1) * r := by
          calc n + 1 = r * (n / r) + (n % r + 1) := by linarith [hdiv_mod]
            _ = r * (n / r) + r := by rw [hmod_eq]
            _ = (n / r + 1) * r := by ring
        rw [h1, Nat.mul_div_cancel _ hr]
      have hmod_succ : (n + 1) % r = 0 := by
        have h1 : n + 1 = (n / r + 1) * r := by
          calc n + 1 = r * (n / r) + (n % r + 1) := by linarith [hdiv_mod]
            _ = r * (n / r) + r := by rw [hmod_eq]
            _ = (n / r + 1) * r := by ring
        rw [h1, Nat.mul_mod_left]
      rw [hdiv_succ, hmod_succ]
      by_cases hpar : (n / r) % 2 = 0
      · have hpar_succ : ¬ ((n / r + 1) % 2 = 0) := by omega
        have hhalf_succ : (n / r + 1) / 2 = (n / r) / 2 := by omega
        rw [if_pos hpar, if_neg hpar_succ, if_neg hpar_succ, hhalf_succ]
        simp only [htop, hbot, if_pos hpar]
        constructor <;> linarith [hmod_eq]
      · have hpar_succ : (n / r + 1) % 2 = 0 := by omega
        have hhalf_succ : (n / r + 1) / 2 = (n / r) / 2 + 1 := by omega
        rw [if_neg hpar, if_pos hpar_succ, if_pos hpar_succ, hhalf_succ]
        simp only [htop, hbot, if_neg hpar]
        constructor <;> linarith [hmod_eq]

/-- **Multitape Linear Head-Movement Correctness of `interleaveRunsPass` (`runInterleaveRunsSteps_eq_interleaveRunsPass`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
For any `0 < r` and any `n : ℕ`, after `n` single-head steps of `interleaveRunsHeadStep` (each advancing
one input read head by `+1` and `outTape` by `+1`),
`∀ idx < n, read1D (runInterleaveRunsSteps r topTape botTape n).outTape idx = interleaveRunsPass r topTape botTape idx`. -/
theorem runInterleaveRunsSteps_eq_interleaveRunsPass {α : Type*} [Zero α]
    (r : ℕ) (hr : 0 < r) (topTape botTape : ℕ → α) (n idx : ℕ) (hidx : idx < n) :
    read1D (runInterleaveRunsSteps r topTape botTape n).outTape idx =
      interleaveRunsPass r topTape botTape idx := by
  induction n generalizing idx with
  | zero => omega
  | succ n ih =>
    obtain ⟨htop, hbot⟩ := runInterleaveRunsSteps_heads r hr topTape botTape n
    dsimp only [runInterleaveRunsSteps, interleaveRunsHeadStep]
    have hsize := size_runInterleaveRunsSteps r topTape botTape n
    rw [hsize]
    split_ifs with hpar
    · rw [read1D_push _ _ idx (by omega), hsize]
      split_ifs with hlt
      · exact ih idx hlt
      · have hidx_eq : idx = n := by omega
        subst hidx_eq
        unfold interleaveRunsPass
        rw [if_pos hpar, htop, if_pos hpar]
    · rw [read1D_push _ _ idx (by omega), hsize]
      split_ifs with hlt
      · exact ih idx hlt
      · have hidx_eq : idx = n := by omega
        subst hidx_eq
        unfold interleaveRunsPass
        rw [if_neg hpar, hbot, if_neg hpar]

/-- Configuration of a 3-tape sequential parity-interleaving machine (`MultiTapeParityInterleaveState`, `[MS]` §§3.2, 3.4 (Lemma 3.3)):
- `firstHead : ℕ` is the read head on `firstTape`,
- `secondHead : ℕ` is the read head on `secondTape`,
- `outTape : Array α` is the sequential write-only output tape,
- `steps : ℕ` is the runtime head-step counter incremented by `+1` at every single step. -/
structure MultiTapeParityInterleaveState (α : Type*) where
  firstHead : ℕ
  secondHead : ℕ
  outTape : Array α
  steps : ℕ

/-- Single sequential head-step of the 3-tape parity-interleaving machine:
at output step `u1 = st.outTape.size`, if `u1 % 2 = parity % 2` it reads `firstTape st.firstHead`,
advances `firstHead` by `+1`, pushes onto `outTape`, and increments `st.steps` by `+1`;
otherwise it reads `secondTape st.secondHead`, advances `secondHead` by `+1`, pushes onto `outTape`,
and increments `st.steps` by `+1`. -/
def interleaveParityHeadStep {α : Type*} (parity : ℕ) (firstTape secondTape : ℕ → α)
    (st : MultiTapeParityInterleaveState α) : MultiTapeParityInterleaveState α :=
  let u1 := st.outTape.size
  if u1 % 2 = parity % 2 then
    ⟨st.firstHead + 1, st.secondHead, st.outTape.push (firstTape st.firstHead), st.steps + 1⟩
  else
    ⟨st.firstHead, st.secondHead + 1, st.outTape.push (secondTape st.secondHead), st.steps + 1⟩

/-- Execute `n` single-head steps of `interleaveParityHeadStep`. -/
def runInterleaveParitySteps {α : Type*} (parity : ℕ) (firstTape secondTape : ℕ → α) :
    ℕ → MultiTapeParityInterleaveState α
  | 0 => ⟨0, 0, #[], 0⟩
  | n + 1 => interleaveParityHeadStep parity firstTape secondTape
      (runInterleaveParitySteps parity firstTape secondTape n)

@[simp]
theorem size_runInterleaveParitySteps {α : Type*} (parity : ℕ) (firstTape secondTape : ℕ → α) (n : ℕ) :
    (runInterleaveParitySteps parity firstTape secondTape n).outTape.size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [runInterleaveParitySteps, interleaveParityHeadStep]
    split_ifs <;> simp [ih]

@[simp]
theorem runInterleaveParitySteps_steps {α : Type*} (parity : ℕ) (firstTape secondTape : ℕ → α) (n : ℕ) :
    (runInterleaveParitySteps parity firstTape secondTape n).steps = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [runInterleaveParitySteps, interleaveParityHeadStep]
    split_ifs <;> simp [ih]

/-- **Multitape Linear Head-Movement Correctness of `interleaveParityPass` (`runInterleaveParitySteps_eq_interleaveParityPass`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
Note that `interleaveParityPass parity firstTape secondTape` is the exact `r = 1` specialization of
`interleaveRunsPass`: after `n` single-head steps of `interleaveParityHeadStep`,
`∀ u1 < n, read1D (runInterleaveParitySteps parity firstTape secondTape n).outTape u1 = interleaveParityPass parity firstTape secondTape u1`. -/
theorem runInterleaveParitySteps_heads_and_eq {α : Type*} [Zero α]
    (parity : ℕ) (firstTape secondTape : ℕ → α) (n : ℕ) :
    (runInterleaveParitySteps parity firstTape secondTape n).firstHead =
      (if parity % 2 = 0 then (n + 1) / 2 else n / 2) ∧
    (runInterleaveParitySteps parity firstTape secondTape n).secondHead =
      (if parity % 2 = 0 then n / 2 else (n + 1) / 2) ∧
    (∀ u1 < n, read1D (runInterleaveParitySteps parity firstTape secondTape n).outTape u1 =
      interleaveParityPass parity firstTape secondTape u1) := by
  induction n with
  | zero =>
    refine ⟨by simp [runInterleaveParitySteps], by simp [runInterleaveParitySteps], ?_⟩
    intro u1 hu1
    omega
  | succ n ih =>
    rcases ih with ⟨hf, hs, hval⟩
    dsimp only [runInterleaveParitySteps, interleaveParityHeadStep]
    have hsize := size_runInterleaveParitySteps parity firstTape secondTape n
    rw [hsize]
    by_cases hpar : n % 2 = parity % 2
    · rw [if_pos hpar]
      dsimp only
      refine ⟨by rw [hf]; split_ifs <;> omega, by rw [hs]; split_ifs <;> omega, ?_⟩
      intro u1 hu1
      rw [read1D_push _ _ u1 (by omega), hsize]
      split_ifs with hlt
      · exact hval u1 hlt
      · have hu1_eq : u1 = n := by omega
        subst hu1_eq
        unfold interleaveParityPass
        rw [if_pos hpar, hf]
        congr 1
        split_ifs <;> omega
    · rw [if_neg hpar]
      dsimp only
      refine ⟨by rw [hf]; split_ifs <;> omega, by rw [hs]; split_ifs <;> omega, ?_⟩
      intro u1 hu1
      rw [read1D_push _ _ u1 (by omega), hsize]
      split_ifs with hlt
      · exact hval u1 hlt
      · have hu1_eq : u1 = n := by omega
        subst hu1_eq
        unfold interleaveParityPass
        rw [if_neg hpar, hs]
        congr 1
        split_ifs <;> omega

/-- Configuration of a 2-tape sequential scan / reversal machine (`MultiTapeScanState`, `[MS]` §3.2):
- `inHead : ℕ` is the sequential step index (advancing by `+1`),
- `outTape : Array α` is the sequential write-only output tape,
- `steps : ℕ` is the runtime head-step counter incremented by `+1` at every single step. -/
structure MultiTapeScanState (α : Type*) where
  inHead : ℕ
  outTape : Array α
  steps : ℕ

/-- Single sequential head-step of a 2-tape linear scan (`scanHeadStep`):
reads `inTape st.inHead`, advances `inHead` by `+1`, appends to `outTape`, and increments `steps` by `+1`. -/
def scanHeadStep {α : Type*} (inTape : ℕ → α) (st : MultiTapeScanState α) :
    MultiTapeScanState α :=
  ⟨st.inHead + 1, st.outTape.push (inTape st.inHead), st.steps + 1⟩

/-- Execute `n` single-head steps of `scanHeadStep`. -/
def runSequentialScanSteps {α : Type*} (inTape : ℕ → α) : ℕ → MultiTapeScanState α
  | 0 => ⟨0, #[], 0⟩
  | n + 1 => scanHeadStep inTape (runSequentialScanSteps inTape n)

@[simp]
theorem runSequentialScanSteps_inHead {α : Type*} (inTape : ℕ → α) (n : ℕ) :
    (runSequentialScanSteps inTape n).inHead = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [runSequentialScanSteps, scanHeadStep, ih]

@[simp]
theorem runSequentialScanSteps_steps {α : Type*} (inTape : ℕ → α) (n : ℕ) :
    (runSequentialScanSteps inTape n).steps = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [runSequentialScanSteps, scanHeadStep, ih]

@[simp]
theorem size_runSequentialScanSteps {α : Type*} (inTape : ℕ → α) (n : ℕ) :
    (runSequentialScanSteps inTape n).outTape.size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [runSequentialScanSteps, scanHeadStep, ih]

theorem read1D_runSequentialScanSteps_eq {α : Type*} [Zero α] (inTape : ℕ → α) (n i : ℕ) (hi : i < n) :
    read1D (runSequentialScanSteps inTape n).outTape i = inTape i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    dsimp only [runSequentialScanSteps, scanHeadStep]
    rw [read1D_push _ _ i (by rw [size_runSequentialScanSteps]; omega),
        size_runSequentialScanSteps, runSequentialScanSteps_inHead]
    split_ifs with hlt
    · exact ih i hlt
    · have hi_eq : i = n := by omega
      subst hi_eq
      rfl

/-- Single forward-seek head-step (`seekForwardHeadStep`, `[MS]` §3.2):
advances the input read head `inHead` by `+1` (`st.inHead + 1`) and increments `steps` by `+1`
without writing to `outTape`. -/
def seekForwardHeadStep {α : Type*} (st : MultiTapeScanState α) : MultiTapeScanState α :=
  ⟨st.inHead + 1, st.outTape, st.steps + 1⟩

/-- Advance `inHead` by `k` single-cell `+1` head steps (`runSeekForwardSteps`). -/
def runSeekForwardSteps {α : Type*} : ℕ → MultiTapeScanState α → MultiTapeScanState α
  | 0, st => st
  | k + 1, st => seekForwardHeadStep (runSeekForwardSteps k st)

@[simp]
theorem runSeekForwardSteps_inHead {α : Type*} (k : ℕ) (st : MultiTapeScanState α) :
    (runSeekForwardSteps k st).inHead = st.inHead + k := by
  induction k with
  | zero => simp [runSeekForwardSteps]
  | succ k ih =>
    simp only [runSeekForwardSteps, seekForwardHeadStep, ih]
    omega

@[simp]
theorem runSeekForwardSteps_outTape {α : Type*} (k : ℕ) (st : MultiTapeScanState α) :
    (runSeekForwardSteps k st).outTape = st.outTape := by
  induction k with
  | zero => rfl
  | succ k ih => simp [runSeekForwardSteps, seekForwardHeadStep, ih]

@[simp]
theorem runSeekForwardSteps_steps {α : Type*} (k : ℕ) (st : MultiTapeScanState α) :
    (runSeekForwardSteps k st).steps = st.steps + k := by
  induction k with
  | zero => simp [runSeekForwardSteps]
  | succ k ih =>
    simp only [runSeekForwardSteps, seekForwardHeadStep, ih]
    omega

/-- Single sequential backward-scan head-step (`reverseHeadStep`, `[MS]` §3.2):
reads `inTape st.inHead` directly at the current input head position `st.inHead` (with zero
`total - 1 - st.inHead` index subtraction), decrements the input read head by `-1` (`st.inHead - 1`),
appends to `outTape` (`+1`), and increments `steps` by `+1`. -/
def reverseHeadStep {α : Type*} (inTape : ℕ → α) (st : MultiTapeScanState α) :
    MultiTapeScanState α :=
  ⟨st.inHead - 1, st.outTape.push (inTape st.inHead), st.steps + 1⟩

/-- Execute `n` single-head backward-scan steps of `reverseHeadStep` starting from state `st`. -/
def runReverseFromState {α : Type*} (inTape : ℕ → α) :
    ℕ → MultiTapeScanState α → MultiTapeScanState α
  | 0, st => st
  | n + 1, st => reverseHeadStep inTape (runReverseFromState inTape n st)

@[simp]
theorem runReverseFromState_inHead {α : Type*} (inTape : ℕ → α) (n : ℕ) (st : MultiTapeScanState α) :
    (runReverseFromState inTape n st).inHead = st.inHead - n := by
  induction n with
  | zero => simp [runReverseFromState]
  | succ n ih =>
    simp only [runReverseFromState, reverseHeadStep, ih]
    omega

@[simp]
theorem runReverseFromState_steps {α : Type*} (inTape : ℕ → α) (n : ℕ) (st : MultiTapeScanState α) :
    (runReverseFromState inTape n st).steps = st.steps + n := by
  induction n with
  | zero => simp [runReverseFromState]
  | succ n ih =>
    simp only [runReverseFromState, reverseHeadStep, ih]
    omega

@[simp]
theorem size_runReverseFromState {α : Type*} (inTape : ℕ → α) (n : ℕ) (st : MultiTapeScanState α) :
    (runReverseFromState inTape n st).outTape.size = st.outTape.size + n := by
  induction n with
  | zero => simp [runReverseFromState]
  | succ n ih =>
    simp only [runReverseFromState, reverseHeadStep, Array.size_push, ih]
    omega

/-- Execute a 2-tape reversal pass over a segment of length `total` (`runReverseSteps`, `[MS]` §3.2):
first positions `inHead` at `total - 1` via `total - 1` single-cell `+1` forward-seek steps of
`seekForwardHeadStep` from `0` (counting all `total - 1` seek steps), then executes `n` single-cell
`-1` backward-scan steps of `reverseHeadStep` reading `inTape st.inHead` directly at each step. -/
def runReverseSteps {α : Type*} (total : ℕ) (inTape : ℕ → α) (n : ℕ) : MultiTapeScanState α :=
  runReverseFromState inTape n (runSeekForwardSteps (total - 1) ⟨0, #[], 0⟩)

@[simp]
theorem runReverseSteps_inHead {α : Type*} (total : ℕ) (inTape : ℕ → α) (n : ℕ) :
    (runReverseSteps total inTape n).inHead = total - 1 - n := by
  simp [runReverseSteps]

@[simp]
theorem runReverseSteps_steps {α : Type*} (total : ℕ) (inTape : ℕ → α) (n : ℕ) :
    (runReverseSteps total inTape n).steps = total - 1 + n := by
  simp [runReverseSteps]

@[simp]
theorem size_runReverseSteps {α : Type*} (total : ℕ) (inTape : ℕ → α) (n : ℕ) :
    (runReverseSteps total inTape n).outTape.size = n := by
  simp [runReverseSteps]

theorem read1D_runReverseSteps_eq {α : Type*} [Zero α] (total : ℕ) (inTape : ℕ → α) (n i : ℕ) (hi : i < n) :
    read1D (runReverseSteps total inTape n).outTape i = inTape (total - 1 - i) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    change read1D (reverseHeadStep inTape (runReverseSteps total inTape n)).outTape i = _
    dsimp only [reverseHeadStep]
    rw [read1D_push _ _ i (by rw [size_runReverseSteps]; omega),
        size_runReverseSteps, runReverseSteps_inHead]
    split_ifs with hlt
    · exact ih i hlt
    · have hi_eq : i = n := by omega
      subst hi_eq
      rfl

/-- Execute the cyclic backward-RHS reversal pass (`runBwdRevSteps`, `[MS]` §§3.2, 5.2) using strictly
single-cell `0`, `+1`, and `-1` head movements and direct `inTape st.inHead` reads:
- at step `1`, reads `inTape st0.inHead` at `st0.inHead = 0` (`inTape 0`) and seeks `inHead` forward
  from `0` to `t1 - 1` via `t1 - 1` single-cell `+1` steps of `seekForwardHeadStep` (counting all
  `t1 - 1` seek steps),
- at each subsequent step `m + 2`, executes `reverseHeadStep inTape` (reading `inTape st.inHead`
  directly and decrementing `st.inHead` by `-1`). -/
def runBwdRevSteps {α : Type*} (t1 : ℕ) (inTape : ℕ → α) : ℕ → MultiTapeScanState α
  | 0 => ⟨0, #[], 0⟩
  | n + 1 =>
    let st0 : MultiTapeScanState α := ⟨0, #[], 0⟩
    let st1 : MultiTapeScanState α := ⟨st0.inHead, st0.outTape.push (inTape st0.inHead), st0.steps + 1⟩
    let stSeek := runSeekForwardSteps (t1 - 1) st1
    runReverseFromState inTape n stSeek

@[simp]
theorem runBwdRevSteps_steps {α : Type*} (t1 : ℕ) (inTape : ℕ → α) (n : ℕ) :
    (runBwdRevSteps t1 inTape n).steps = if n = 0 then 0 else t1 - 1 + n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [runBwdRevSteps, runReverseFromState_steps, runSeekForwardSteps_steps,
      Nat.succ_ne_zero, ↓reduceIte]
    omega

@[simp]
theorem size_runBwdRevSteps {α : Type*} (t1 : ℕ) (inTape : ℕ → α) (n : ℕ) :
    (runBwdRevSteps t1 inTape n).outTape.size = n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [runBwdRevSteps, size_runReverseFromState, runSeekForwardSteps_outTape,
      Array.size_push, List.size_toArray, List.length_nil]
    omega

theorem read1D_runBwdRevSteps_eq {α : Type*} [Zero α] (t1 : ℕ) (inTape : ℕ → α) (n i : ℕ) (hi : i < n) :
    read1D (runBwdRevSteps t1 inTape n).outTape i =
      (if i = 0 then inTape 0 else inTape (t1 - i)) := by
  cases n with
  | zero => omega
  | succ m =>
    dsimp only [runBwdRevSteps]
    set st0 : MultiTapeScanState α := ⟨0, #[], 0⟩
    set st1 : MultiTapeScanState α := ⟨st0.inHead, st0.outTape.push (inTape st0.inHead), st0.steps + 1⟩
    set stSeek := runSeekForwardSteps (t1 - 1) st1
    induction m generalizing i with
    | zero =>
      have hi0 : i = 0 := by omega
      subst hi0
      dsimp only [runReverseFromState, stSeek, st1, st0]
      rw [runSeekForwardSteps_outTape, read1D_push _ _ 0 (by simp)]
      simp
    | succ m ih =>
      dsimp only [runReverseFromState, reverseHeadStep]
      have hsize : (runReverseFromState inTape m stSeek).outTape.size = m + 1 := by
        simp [stSeek, st1, st0]
        omega
      have hinHead : (runReverseFromState inTape m stSeek).inHead = t1 - (m + 1) := by
        simp [stSeek, st1, st0]
        omega
      rw [read1D_push _ _ i (by rw [hsize]; omega), hsize, hinHead]
      by_cases hlt : i < m + 1
      · rw [if_pos hlt]
        exact ih i hlt
      · rw [if_neg hlt]
        have hi_eq : i = m + 1 := by omega
        subst hi_eq
        simp

/-- Configuration of a sequential 2D-to-1D row-major flattening machine (`MultiTapeFlatten2DState`, `[MS]` §3.2):
- `rowHead : ℕ` is the current row index (`0 .. R - 1`),
- `colHead : ℕ` is the current column index within `rowHead` (`0 .. C - 1`), advancing by `+1`
  each step and wrapping to `0` when `rowHead` advances by `+1` (zero `/` or `%` division/modulo),
- `outTape : Array α` is the sequential write-only 1D output tape,
- `steps : ℕ` is the runtime head-step counter incremented by `+1` at every single step. -/
structure MultiTapeFlatten2DState (α : Type*) where
  rowHead : ℕ
  colHead : ℕ
  outTape : Array α
  steps : ℕ

/-- Single sequential head-step of the 2D-to-1D row-major flattening machine (`flatten2DHeadStep`):
reads `read2D mat st.rowHead st.colHead`, appends to `outTape`, increments `steps` by `+1`, and
advances `(rowHead, colHead)` to the next cell using only `+ 1` comparisons (zero `/` or `%`). -/
def flatten2DHeadStep {α : Type*} [Zero α] (C : ℕ) (mat : Array (Array α))
    (st : MultiTapeFlatten2DState α) : MultiTapeFlatten2DState α :=
  let val := read2D mat st.rowHead st.colHead
  if st.colHead + 1 < C then
    ⟨st.rowHead, st.colHead + 1, st.outTape.push val, st.steps + 1⟩
  else
    ⟨st.rowHead + 1, 0, st.outTape.push val, st.steps + 1⟩

/-- Execute `n` single-head steps of `flatten2DHeadStep`. -/
def runFlatten2DSteps {α : Type*} [Zero α] (C : ℕ) (mat : Array (Array α)) :
    ℕ → MultiTapeFlatten2DState α
  | 0 => ⟨0, 0, #[], 0⟩
  | n + 1 => flatten2DHeadStep C mat (runFlatten2DSteps C mat n)

@[simp]
theorem size_runFlatten2DSteps {α : Type*} [Zero α] (C : ℕ) (mat : Array (Array α)) (n : ℕ) :
    (runFlatten2DSteps C mat n).outTape.size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [runFlatten2DSteps, flatten2DHeadStep]
    split_ifs <;> simp [ih]

@[simp]
theorem runFlatten2DSteps_steps {α : Type*} [Zero α] (C : ℕ) (mat : Array (Array α)) (n : ℕ) :
    (runFlatten2DSteps C mat n).steps = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [runFlatten2DSteps, flatten2DHeadStep]
    split_ifs <;> simp [ih]

theorem runFlatten2DSteps_heads {α : Type*} [Zero α] (C : ℕ) (hC : 0 < C)
    (mat : Array (Array α)) (n : ℕ) :
    (runFlatten2DSteps C mat n).rowHead = n / C ∧
    (runFlatten2DSteps C mat n).colHead = n % C := by
  induction n with
  | zero => simp [runFlatten2DSteps]
  | succ n ih =>
    rcases ih with ⟨hrow, hcol⟩
    dsimp only [runFlatten2DSteps, flatten2DHeadStep]
    rw [hrow, hcol]
    have hdiv_mod := (Nat.div_add_mod n C).symm
    have hmod_lt : n % C < C := Nat.mod_lt n hC
    by_cases hwrap : n % C + 1 < C
    · have hdiv_succ : (n + 1) / C = n / C := by
        have h1 : n + 1 = (n % C + 1) + (n / C) * C := by
          calc n + 1 = (C * (n / C) + n % C) + 1 := by rw [← hdiv_mod]
            _ = (n % C + 1) + (n / C) * C := by ring
        rw [h1, Nat.add_mul_div_right _ _ hC, Nat.div_eq_of_lt hwrap, zero_add]
      have hmod_succ : (n + 1) % C = n % C + 1 := by
        have h1 : n + 1 = (n % C + 1) + (n / C) * C := by
          calc n + 1 = (C * (n / C) + n % C) + 1 := by rw [← hdiv_mod]
            _ = (n % C + 1) + (n / C) * C := by ring
        rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hwrap]
      rw [if_pos hwrap, hdiv_succ, hmod_succ]
      exact ⟨rfl, rfl⟩
    · have hmod_eq : n % C + 1 = C := by omega
      have hdiv_succ : (n + 1) / C = n / C + 1 := by
        have h1 : n + 1 = (n / C + 1) * C := by
          calc n + 1 = C * (n / C) + (n % C + 1) := by linarith [hdiv_mod]
            _ = C * (n / C) + C := by rw [hmod_eq]
            _ = (n / C + 1) * C := by ring
        rw [h1, Nat.mul_div_cancel _ hC]
      have hmod_succ : (n + 1) % C = 0 := by
        have h1 : n + 1 = (n / C + 1) * C := by
          calc n + 1 = C * (n / C) + (n % C + 1) := by linarith [hdiv_mod]
            _ = C * (n / C) + C := by rw [hmod_eq]
            _ = (n / C + 1) * C := by ring
        rw [h1, Nat.mul_mod_left]
      rw [if_neg hwrap, hdiv_succ, hmod_succ]
      exact ⟨rfl, rfl⟩

/-- **Sequential 2D-to-1D Flattening Correctness (`read1D_runFlatten2DSteps_eq`, `[MS]` §3.2)**:
For any `0 < C` and any `n : ℕ`, after `n` single-head steps of `flatten2DHeadStep`,
`∀ idx < n, read1D (runFlatten2DSteps C mat n).outTape idx = read2D mat (idx / C) (idx % C)`. -/
theorem read1D_runFlatten2DSteps_eq {α : Type*} [Zero α]
    (C : ℕ) (hC : 0 < C) (mat : Array (Array α)) (n idx : ℕ) (hidx : idx < n) :
    read1D (runFlatten2DSteps C mat n).outTape idx = read2D mat (idx / C) (idx % C) := by
  induction n generalizing idx with
  | zero => omega
  | succ n ih =>
    obtain ⟨hrow, hcol⟩ := runFlatten2DSteps_heads C hC mat n
    dsimp only [runFlatten2DSteps, flatten2DHeadStep]
    have hsize := size_runFlatten2DSteps C mat n
    split_ifs with hwrap <;>
      (rw [read1D_push _ _ idx (by omega), hsize];
       split_ifs with hlt;
       · exact ih idx hlt;
       · have hidx_eq : idx = n := by omega;
         subst hidx_eq;
         rw [hrow, hcol])

/-- **Multi-Pass Multitape Head-Step Matrix Transpose (`runMultiTapeTranspose`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
Composes the explicit single-head-step machines `runUnshuffleSteps` and `runInterleaveRunsSteps`
across `m` recursive stages (`2 * m` sequential full-tape passes) to transpose a `2^m × r` matrix
using strictly `0` or `+1` head movements per step. -/
def runMultiTapeTranspose {α : Type*} [Zero α] : ℕ → ℕ → (ℕ → α) → Array α
  | 0, r, tape => (runSequentialScanSteps tape r).outTape
  | m + 1, r, tape =>
    let half := 2 ^ m * r
    let stU := runUnshuffleSteps tape (2 * half)
    let topArr := runMultiTapeTranspose m r (read1D stU.evenTape)
    let botArr := runMultiTapeTranspose m r (read1D stU.oddTape)
    (runInterleaveRunsSteps r (read1D topArr) (read1D botArr) (2 * half)).outTape

/-- **Step-Instrumented Multi-Pass Multitape Matrix Transpose (`runMultiTapeTransposeWithSteps`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
Runs `runMultiTapeTranspose` while accumulating the total head-step count directly from the `.steps`
counter fields of the executed `MultiTapeUnshuffleState` and `MultiTapeRunInterleaveState` machines
(`stU.steps + top.2 + bot.2 + stI.steps`). -/
def runMultiTapeTransposeWithSteps {α : Type*} [Zero α] : ℕ → ℕ → (ℕ → α) → Array α × ℕ
  | 0, r, tape => ((runSequentialScanSteps tape r).outTape, 0)
  | m + 1, r, tape =>
    let half := 2 ^ m * r
    let stU := runUnshuffleSteps tape (2 * half)
    let top := runMultiTapeTransposeWithSteps m r (read1D stU.evenTape)
    let bot := runMultiTapeTransposeWithSteps m r (read1D stU.oddTape)
    let stI := runInterleaveRunsSteps r (read1D top.1) (read1D bot.1) (2 * half)
    (stI.outTape, stU.steps + top.2 + bot.2 + stI.steps)

@[simp]
theorem runMultiTapeTransposeWithSteps_fst {α : Type*} [Zero α] (m r : ℕ) (tape : ℕ → α) :
    (runMultiTapeTransposeWithSteps m r tape).1 = runMultiTapeTranspose m r tape := by
  induction m generalizing tape with
  | zero => rfl
  | succ m ih =>
    dsimp only [runMultiTapeTransposeWithSteps, runMultiTapeTranspose]
    rw [ih, ih]

@[simp]
theorem runMultiTapeTransposeWithSteps_snd {α : Type*} [Zero α] (m r : ℕ) (tape : ℕ → α) :
    (runMultiTapeTransposeWithSteps m r tape).2 = (2 * m) * (2 ^ m * r) := by
  induction m generalizing tape with
  | zero => simp [runMultiTapeTransposeWithSteps]
  | succ m ih =>
    dsimp only [runMultiTapeTransposeWithSteps]
    rw [runUnshuffleSteps_steps, runInterleaveRunsSteps_steps, ih, ih, pow_succ]
    ring

/-- **Multi-Pass Head-Step Equivalence with `sequentialTapeTranspose` (`read1D_runMultiTapeTranspose_eq`, `[MS]` §§3.2, 3.4)**:
For any `m, r : ℕ` (`0 < r`) and any tapes `t1, t2 : ℕ → α` agreeing on `0 .. 2^m * r - 1`,
every output entry `idx < 2 ^ m * r` produced by the composed multi-pass head-step machine
`runMultiTapeTranspose m r t1` equals `sequentialTapeTranspose m r t2 idx`. -/
theorem read1D_runMultiTapeTranspose_eq {α : Type*} [Zero α]
    (m r : ℕ) (hr : 0 < r) (t1 t2 : ℕ → α)
    (ht : ∀ k < 2 ^ m * r, t1 k = t2 k)
    (idx : ℕ) (hidx : idx < 2 ^ m * r) :
    read1D (runMultiTapeTranspose m r t1) idx = sequentialTapeTranspose m r t2 idx := by
  induction m generalizing t1 t2 idx with
  | zero =>
    dsimp only [runMultiTapeTranspose, sequentialTapeTranspose]
    have hidx_r : idx < r := by simpa using hidx
    rw [read1D_runSequentialScanSteps_eq t1 r idx hidx_r]
    exact ht idx hidx
  | succ m ih =>
    dsimp only [runMultiTapeTranspose, sequentialTapeTranspose]
    set half := 2 ^ m * r
    have h2half_eq : 2 * half = 2 ^ (m + 1) * r := by
      dsimp [half]
      ring
    have hidx_2half : idx < 2 * half := h2half_eq.symm ▸ hidx
    obtain ⟨_, _, he_val, ho_val⟩ := runUnshuffleSteps_two_mul_spec t1 half
    set stU := runUnshuffleSteps t1 (2 * half)
    set topArr := runMultiTapeTranspose m r (read1D stU.evenTape)
    set botArr := runMultiTapeTranspose m r (read1D stU.oddTape)
    set u := unshufflePass half t2
    have he_eq : ∀ k < half, read1D stU.evenTape k = u k := by
      intro k hk
      rw [he_val k hk]
      dsimp only [u, unshufflePass]
      rw [if_pos hk]
      exact ht (2 * k) (by omega)
    have ho_eq : ∀ k < half, read1D stU.oddTape k = u (half + k) := by
      intro k hk
      rw [ho_val k hk]
      dsimp only [u, unshufflePass]
      have hnot : ¬ (half + k < half) := by omega
      rw [if_neg hnot, Nat.add_sub_cancel_left]
      exact ht (2 * k + 1) (by omega)
    rw [runInterleaveRunsSteps_eq_interleaveRunsPass r hr (read1D topArr) (read1D botArr)
        (2 * half) idx hidx_2half]
    unfold interleaveRunsPass
    dsimp only
    have hj_half : (idx / r) / 2 < 2 ^ m := by
      have hdiv_lt : idx / r < 2 * 2 ^ m := by
        rw [Nat.div_lt_iff_lt_mul hr]
        dsimp [half] at hidx_2half
        linarith
      omega
    have hi_lt : idx % r < r := Nat.mod_lt idx hr
    have hsub_idx : ((idx / r) / 2) * r + idx % r < half := by
      have hj_le : (idx / r) / 2 + 1 ≤ 2 ^ m := hj_half
      calc ((idx / r) / 2) * r + idx % r
          < ((idx / r) / 2) * r + r := Nat.add_lt_add_left hi_lt _
        _ = ((idx / r) / 2 + 1) * r := by ring
        _ ≤ 2 ^ m * r := Nat.mul_le_mul_right r hj_le
    split_ifs with hpar
    · exact ih (read1D stU.evenTape) (fun k => u k) he_eq _ hsub_idx
    · exact ih (read1D stU.oddTape) (fun k => u (half + k)) ho_eq _ hsub_idx

/-- **End-to-End Multi-Pass Head-Step Matrix Transpose Index Identity (`read1D_runMultiTapeTranspose_index_eq`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
For any `m, r : ℕ` (`0 < r`), any tape `tape : ℕ → α`, and any `j1 < 2 ^ m`, `i < r`,
`read1D (runMultiTapeTranspose m r tape) (j1 * r + i) = tape (i * 2 ^ m + j1)`. -/
theorem read1D_runMultiTapeTranspose_index_eq {α : Type*} [Zero α]
    (m r : ℕ) (hr : 0 < r) (tape : ℕ → α) (j1 i : ℕ) (hj1 : j1 < 2 ^ m) (hi : i < r) :
    read1D (runMultiTapeTranspose m r tape) (j1 * r + i) = tape (i * 2 ^ m + j1) := by
  have hlt : j1 * r + i < 2 ^ m * r := by
    have hj1_le : j1 + 1 ≤ 2 ^ m := hj1
    calc j1 * r + i < j1 * r + r := Nat.add_lt_add_left hi _
      _ = (j1 + 1) * r := by ring
      _ ≤ 2 ^ m * r := Nat.mul_le_mul_right r hj1_le
  rw [read1D_runMultiTapeTranspose_eq m r hr tape tape (fun _ _ => rfl) (j1 * r + i) hlt]
  exact sequentialTapeTranspose_index_eq m r hr tape j1 i hj1 hi

/-- **Multi-Pass Head-Step Matrix Transpose on 2D `Array (Array α)` (`read1D_runMultiTapeTranspose_mat_eq`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
For any `m, R, C : ℕ` with `2 ^ m = R` and `0 < C`, flattening a `C × R` array `mat` (`c < C`, `r < R`)
as `fun idx => read2D mat (idx / R) (idx % R)` and transposing via `runMultiTapeTranspose m C` yields
`read1D (runMultiTapeTranspose m C (fun idx => read2D mat (idx / R) (idx % R))) (r * C + c) = read2D mat c r`. -/
theorem read1D_runMultiTapeTranspose_mat_eq {α : Type*} [Zero α]
    (m R C : ℕ) (hR : 2 ^ m = R) (hC : 0 < C)
    (mat : Array (Array α)) (r c : ℕ) (hr : r < R) (hc : c < C) :
    read1D (runMultiTapeTranspose m C (fun idx => read2D mat (idx / R) (idx % R))) (r * C + c) =
      read2D mat c r := by
  have hr_m : r < 2 ^ m := hR.symm ▸ hr
  have hR_pos : 0 < R := by omega
  rw [read1D_runMultiTapeTranspose_index_eq m C hC _ r c hr_m hc]
  rw [hR]
  have hdiv : (c * R + r) / R = c := by
    rw [mul_comm c R, Nat.mul_add_div hR_pos, Nat.div_eq_of_lt hr, add_zero]
  have hmod : (c * R + r) % R = r := by
    rw [mul_comm c R, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  rw [hdiv, hmod]

/-- **Sequential Flatten + Multi-Pass Head-Step Matrix Transpose on 2D `Array (Array α)` (`read1D_runMultiTapeTranspose_flatten2D_eq`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
Flattening a `C × R` array `mat` sequentially via `runFlatten2DSteps R mat (C * R)` (with zero `/` or `%`
division/modulo) and transposing via `runMultiTapeTranspose m C` (`2 ^ m = R`, `0 < C`) yields
`read2D mat c r` at index `r * C + c` for all `r < R` and `c < C`. -/
theorem read1D_runMultiTapeTranspose_flatten2D_eq {α : Type*} [Zero α]
    (m R C : ℕ) (hR : 2 ^ m = R) (hC : 0 < C)
    (mat : Array (Array α)) (r c : ℕ) (hr : r < R) (hc : c < C) :
    read1D (runMultiTapeTranspose m C (read1D (runFlatten2DSteps R mat (C * R)).outTape)) (r * C + c) =
      read2D mat c r := by
  have hr_m : r < 2 ^ m := hR.symm ▸ hr
  have hR_pos : 0 < R := by omega
  have hlt : r * C + c < 2 ^ m * C := by
    have hr_le : r + 1 ≤ 2 ^ m := hr_m
    calc r * C + c < r * C + C := Nat.add_lt_add_left hc _
      _ = (r + 1) * C := by ring
      _ ≤ 2 ^ m * C := Nat.mul_le_mul_right C hr_le
  have hcongr : ∀ k < 2 ^ m * C,
      read1D (runFlatten2DSteps R mat (C * R)).outTape k = read2D mat (k / R) (k % R) := by
    intro k hk
    have hk_CR : k < C * R := by rw [mul_comm C R, ← hR]; exact hk
    exact read1D_runFlatten2DSteps_eq R hR_pos mat (C * R) k hk_CR
  rw [read1D_runMultiTapeTranspose_eq m C hC
        (read1D (runFlatten2DSteps R mat (C * R)).outTape)
        (fun idx => read2D mat (idx / R) (idx % R)) hcongr (r * C + c) hlt,
      ← read1D_runMultiTapeTranspose_eq m C hC
        (fun idx => read2D mat (idx / R) (idx % R))
        (fun idx => read2D mat (idx / R) (idx % R)) (fun _ _ => rfl) (r * C + c) hlt]
  exact read1D_runMultiTapeTranspose_mat_eq m R C hR hC mat r c hr hc

/-- **Multi-Pass Multitape Head-Step Affine Odd-Stride Router (`runMultiTapeAffineOddRoute`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
Composes `runUnshuffleSteps` and `runInterleaveParitySteps` across `m` recursive stages (`2 * m`
sequential passes) to route any affine odd-stride permutation `u1 ↦ (w * u1 + b) % 2^m` (`w % 2 = 1`)
using strictly `0` or `+1` head movements per step. -/
def runMultiTapeAffineOddRoute {α : Type*} [Zero α] : ℕ → ℕ → ℕ → (ℕ → α) → Array α
  | 0, _w, _b, col => (runSequentialScanSteps col 1).outTape
  | m + 1, w, b, col =>
    let half := 2 ^ m
    let stU := runUnshuffleSteps col (2 * half)
    let bEven := if b % 2 = 0 then b / 2 else (w + b) / 2
    let bOdd := if b % 2 = 0 then (w + b) / 2 else b / 2
    let evenArr := runMultiTapeAffineOddRoute m w bEven (read1D stU.evenTape)
    let oddArr := runMultiTapeAffineOddRoute m w bOdd (read1D stU.oddTape)
    (runInterleaveParitySteps (b % 2) (read1D evenArr) (read1D oddArr) (2 * half)).outTape

/-- **Step-Instrumented Multi-Pass Multitape Affine Odd-Stride Router (`runMultiTapeAffineOddRouteWithSteps`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
Runs `runMultiTapeAffineOddRoute` while accumulating the total head-step count directly from the `.steps`
counter fields of the executed `MultiTapeUnshuffleState` and `MultiTapeParityInterleaveState` machines
(`stU.steps + evenRes.2 + oddRes.2 + stI.steps`). -/
def runMultiTapeAffineOddRouteWithSteps {α : Type*} [Zero α] : ℕ → ℕ → ℕ → (ℕ → α) → Array α × ℕ
  | 0, _w, _b, col => ((runSequentialScanSteps col 1).outTape, 0)
  | m + 1, w, b, col =>
    let half := 2 ^ m
    let stU := runUnshuffleSteps col (2 * half)
    let bEven := if b % 2 = 0 then b / 2 else (w + b) / 2
    let bOdd := if b % 2 = 0 then (w + b) / 2 else b / 2
    let evenRes := runMultiTapeAffineOddRouteWithSteps m w bEven (read1D stU.evenTape)
    let oddRes := runMultiTapeAffineOddRouteWithSteps m w bOdd (read1D stU.oddTape)
    let stI := runInterleaveParitySteps (b % 2) (read1D evenRes.1) (read1D oddRes.1) (2 * half)
    (stI.outTape, stU.steps + evenRes.2 + oddRes.2 + stI.steps)

@[simp]
theorem runMultiTapeAffineOddRouteWithSteps_fst {α : Type*} [Zero α] (m w b : ℕ) (col : ℕ → α) :
    (runMultiTapeAffineOddRouteWithSteps m w b col).1 = runMultiTapeAffineOddRoute m w b col := by
  induction m generalizing b col with
  | zero => rfl
  | succ m ih =>
    dsimp only [runMultiTapeAffineOddRouteWithSteps, runMultiTapeAffineOddRoute]
    rw [ih, ih]

@[simp]
theorem runMultiTapeAffineOddRouteWithSteps_snd {α : Type*} [Zero α] (m w b : ℕ) (col : ℕ → α) :
    (runMultiTapeAffineOddRouteWithSteps m w b col).2 = (2 * m) * 2 ^ m := by
  induction m generalizing b col with
  | zero => simp [runMultiTapeAffineOddRouteWithSteps]
  | succ m ih =>
    dsimp only [runMultiTapeAffineOddRouteWithSteps]
    rw [runUnshuffleSteps_steps, runInterleaveParitySteps_steps, ih, ih, pow_succ]
    ring

/-- **Multi-Pass Head-Step Equivalence with `sequentialAffineOddRoute` (`read1D_runMultiTapeAffineOddRoute_eq`, `[MS]` §§3.2, 3.4)**:
For any `m, w, b : ℕ` and any columns `c1, c2 : ℕ → α` agreeing on `0 .. 2^m - 1`,
every output entry `u1 < 2 ^ m` produced by `runMultiTapeAffineOddRoute m w b c1` equals
`sequentialAffineOddRoute m w b c2 u1`. -/
theorem read1D_runMultiTapeAffineOddRoute_eq {α : Type*} [Zero α]
    (m w b : ℕ) (c1 c2 : ℕ → α) (hc : ∀ k < 2 ^ m, c1 k = c2 k)
    (u1 : ℕ) (hu1 : u1 < 2 ^ m) :
    read1D (runMultiTapeAffineOddRoute m w b c1) u1 =
      sequentialAffineOddRoute m w b c2 u1 := by
  induction m generalizing b c1 c2 u1 with
  | zero =>
    dsimp only [runMultiTapeAffineOddRoute, sequentialAffineOddRoute]
    have hu1_1 : u1 < 1 := by simpa using hu1
    rw [read1D_runSequentialScanSteps_eq c1 1 u1 hu1_1]
    exact hc u1 hu1
  | succ m ih =>
    dsimp only [runMultiTapeAffineOddRoute, sequentialAffineOddRoute]
    set half := 2 ^ m
    have h2half_eq : 2 * half = 2 ^ (m + 1) := by
      dsimp [half]
      ring
    have hu1_2half : u1 < 2 * half := h2half_eq.symm ▸ hu1
    obtain ⟨_, _, he_val, ho_val⟩ := runUnshuffleSteps_two_mul_spec c1 half
    set stU := runUnshuffleSteps c1 (2 * half)
    set bEven := if b % 2 = 0 then b / 2 else (w + b) / 2
    set bOdd := if b % 2 = 0 then (w + b) / 2 else b / 2
    set evenArr := runMultiTapeAffineOddRoute m w bEven (read1D stU.evenTape)
    set oddArr := runMultiTapeAffineOddRoute m w bOdd (read1D stU.oddTape)
    set u := unshufflePass half c2
    have he_eq : ∀ k < half, read1D stU.evenTape k = u k := by
      intro k hk
      rw [he_val k hk]
      dsimp only [u, unshufflePass]
      rw [if_pos hk]
      exact hc (2 * k) (by omega)
    have ho_eq : ∀ k < half, read1D stU.oddTape k = u (half + k) := by
      intro k hk
      rw [ho_val k hk]
      dsimp only [u, unshufflePass]
      have hnot : ¬ (half + k < half) := by omega
      rw [if_neg hnot, Nat.add_sub_cancel_left]
      exact hc (2 * k + 1) (by omega)
    have hpar_eq := (runInterleaveParitySteps_heads_and_eq (b % 2) (read1D evenArr) (read1D oddArr) (2 * half)).2.2
      u1 hu1_2half
    rw [hpar_eq]
    unfold interleaveParityPass
    have hu1_half : u1 / 2 < half := by omega
    split_ifs with hpar
    · exact ih bEven (read1D stU.evenTape) (fun k => u k) he_eq (u1 / 2) hu1_half
    · exact ih bOdd (read1D stU.oddTape) (fun k => u (half + k)) ho_eq (u1 / 2) hu1_half

/-- **End-to-End Multi-Pass Head-Step Affine Odd-Stride Routing Identity (`read1D_runMultiTapeAffineOddRoute_index_eq`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
For any depth `m : ℕ`, odd multiplier `w : ℕ` (`w % 2 = 1`), offset `b : ℕ`, column `col : ℕ → α`,
and index `u1 < 2 ^ m`,
`read1D (runMultiTapeAffineOddRoute m w b col) u1 = col ((w * u1 + b) % 2 ^ m)`. -/
theorem read1D_runMultiTapeAffineOddRoute_index_eq {α : Type*} [Zero α]
    (m w b : ℕ) (hw : w % 2 = 1) (col : ℕ → α) (u1 : ℕ) (hu1 : u1 < 2 ^ m) :
    read1D (runMultiTapeAffineOddRoute m w b col) u1 = col ((w * u1 + b) % 2 ^ m) := by
  rw [read1D_runMultiTapeAffineOddRoute_eq m w b col col (fun _ _ => rfl) u1 hu1]
  exact sequentialAffineOddRoute_index_eq m w b hw col u1 hu1

/-- **Multi-Pass Head-Step Odd-Stride Column Routing Identity (`read1D_runMultiTapeAffineOddRoute_oddStrideFactor_eq`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
For any depth `m : ℕ`, column index `u2 : ℕ`, output index `u1 < 2 ^ m`, and column `col : ℕ → α`,
routing `col` through `runMultiTapeAffineOddRoute m (oddStrideFactor m u2) 0 col` yields
`col (oddStrideInvPow2 m u2 u1)` at index `u1`. -/
theorem read1D_runMultiTapeAffineOddRoute_oddStrideFactor_eq {α : Type*} [Zero α]
    (m u2 u1 : ℕ) (col : ℕ → α) (hu1 : u1 < 2 ^ m) :
    read1D (runMultiTapeAffineOddRoute m (oddStrideFactor m u2) 0 col) u1 =
      col (oddStrideInvPow2 m u2 u1) := by
  rw [read1D_runMultiTapeAffineOddRoute_index_eq m (oddStrideFactor m u2) 0
        (oddStrideFactor_mod_two m u2) col u1 hu1,
      Nat.add_zero, oddStrideFactor_mul_mod_eq]

/-- Total number of single-head-step transitions (`unshuffleHeadStep` + `interleaveRunsHeadStep`)
executed across all recursive stages of `runMultiTapeTranspose m r`. -/
def runMultiTapeTransposeHeadSteps : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, r =>
    let half := 2 ^ m * r
    (2 * half) + runMultiTapeTransposeHeadSteps m r +
      runMultiTapeTransposeHeadSteps m r + (2 * half)

/-- **Exact Head-Step Count of `runMultiTapeTransposeWithSteps` (`runMultiTapeTransposeHeadSteps_eq`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
Across `m` recursive stages on a `2^m × r` array, the runtime step counter `(runMultiTapeTransposeWithSteps m r tape).2`
accumulated directly from `stU.steps` and `stI.steps` equals `runMultiTapeTransposeHeadSteps m r = (2 * m) * (2 ^ m * r)`,
matching `(sequentialTapeTransposeWithPasses m r tape).2 * (2 ^ m * r)`. -/
theorem runMultiTapeTransposeHeadSteps_eq {α : Type*} [Zero α] (m r : ℕ) (tape : ℕ → α) :
    (runMultiTapeTransposeWithSteps m r tape).2 = (2 * m) * (2 ^ m * r) ∧
    runMultiTapeTransposeHeadSteps m r = (2 * m) * (2 ^ m * r) ∧
    (runMultiTapeTransposeWithSteps m r tape).2 =
      (sequentialTapeTransposeWithPasses m r tape).2 * (2 ^ m * r) := by
  have h1 : runMultiTapeTransposeHeadSteps m r = (2 * m) * (2 ^ m * r) := by
    induction m with
    | zero => simp [runMultiTapeTransposeHeadSteps]
    | succ m ih =>
      dsimp only [runMultiTapeTransposeHeadSteps]
      rw [ih, pow_succ]
      ring
  have h0 := runMultiTapeTransposeWithSteps_snd m r tape
  exact ⟨h0, h1, by rw [h0, sequentialTapeTransposeWithPasses_snd]⟩

/-- Total number of single-head-step transitions (`unshuffleHeadStep` + `interleaveParityHeadStep`)
executed across all recursive stages of `runMultiTapeAffineOddRoute m`. -/
def runMultiTapeAffineOddRouteHeadSteps : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    let half := 2 ^ m
    (2 * half) + runMultiTapeAffineOddRouteHeadSteps m +
      runMultiTapeAffineOddRouteHeadSteps m + (2 * half)

/-- **Exact Head-Step Count of `runMultiTapeAffineOddRouteWithSteps` (`runMultiTapeAffineOddRouteHeadSteps_eq`, `[MS]` §§3.2, 3.4 (Lemma 3.3))**:
Across `m` recursive stages on a column of length `2^m`, the runtime step counter `(runMultiTapeAffineOddRouteWithSteps m w b col).2`
accumulated directly from `stU.steps` and `stI.steps` equals `runMultiTapeAffineOddRouteHeadSteps m = (2 * m) * 2 ^ m`,
matching `(sequentialAffineOddRouteWithPasses m w b col).2 * 2 ^ m`. -/
theorem runMultiTapeAffineOddRouteHeadSteps_eq {α : Type*} [Zero α] (m w b : ℕ) (col : ℕ → α) :
    (runMultiTapeAffineOddRouteWithSteps m w b col).2 = (2 * m) * 2 ^ m ∧
    runMultiTapeAffineOddRouteHeadSteps m = (2 * m) * 2 ^ m ∧
    (runMultiTapeAffineOddRouteWithSteps m w b col).2 =
      (sequentialAffineOddRouteWithPasses m w b col).2 * 2 ^ m := by
  have h1 : runMultiTapeAffineOddRouteHeadSteps m = (2 * m) * 2 ^ m := by
    induction m with
    | zero => simp [runMultiTapeAffineOddRouteHeadSteps]
    | succ m ih =>
      dsimp only [runMultiTapeAffineOddRouteHeadSteps]
      rw [ih, pow_succ]
      ring
  have h0 := runMultiTapeAffineOddRouteWithSteps_snd m w b col
  exact ⟨h0, h1, by rw [h0, sequentialAffineOddRouteWithPasses_snd]⟩

/-- Full-step matrix transpose (`runMultiTapeTransposeFullSteps`, `[MS]` §§3.2, 3.4) that also counts the
`m = 0` base-case `runSequentialScanSteps tape r` pass (`st.steps = r`), yielding `(2 * m + 1) * (2 ^ m * r)`
total steps (`≤ 2 * (runMultiTapeTransposeWithSteps m r tape).2` for all `1 ≤ m`). -/
def runMultiTapeTransposeFullSteps {α : Type*} [Zero α] : ℕ → ℕ → (ℕ → α) → Array α × ℕ
  | 0, r, tape =>
    let st := runSequentialScanSteps tape r
    (st.outTape, st.steps)
  | m + 1, r, tape =>
    let half := 2 ^ m * r
    let stU := runUnshuffleSteps tape (2 * half)
    let top := runMultiTapeTransposeFullSteps m r (read1D stU.evenTape)
    let bot := runMultiTapeTransposeFullSteps m r (read1D stU.oddTape)
    let stI := runInterleaveRunsSteps r (read1D top.1) (read1D bot.1) (2 * half)
    (stI.outTape, stU.steps + top.2 + bot.2 + stI.steps)

@[simp]
theorem runMultiTapeTransposeFullSteps_snd {α : Type*} [Zero α] (m r : ℕ) (tape : ℕ → α) :
    (runMultiTapeTransposeFullSteps m r tape).2 = (2 * m + 1) * (2 ^ m * r) := by
  induction m generalizing tape with
  | zero => simp [runMultiTapeTransposeFullSteps]
  | succ m ih =>
    dsimp only [runMultiTapeTransposeFullSteps]
    rw [runUnshuffleSteps_steps, runInterleaveRunsSteps_steps, ih, ih, pow_succ]
    ring

theorem runMultiTapeTransposeFullSteps_snd_le {α : Type*} [Zero α] (m r : ℕ) (hm : 1 ≤ m) (tape : ℕ → α) :
    (runMultiTapeTransposeFullSteps m r tape).2 ≤ 2 * (runMultiTapeTransposeWithSteps m r tape).2 := by
  rw [runMultiTapeTransposeFullSteps_snd, runMultiTapeTransposeWithSteps_snd]
  have h1 : 2 * m + 1 ≤ 2 * (2 * m) := by omega
  calc (2 * m + 1) * (2 ^ m * r)
      ≤ (2 * (2 * m)) * (2 ^ m * r) := Nat.mul_le_mul_right (2 ^ m * r) h1
    _ = 2 * ((2 * m) * (2 ^ m * r)) := by ring

/-- Full-step affine odd-stride router (`runMultiTapeAffineOddRouteFullSteps`, `[MS]` §§3.2, 3.4) that also counts
the `m = 0` base-case `runSequentialScanSteps col 1` pass (`st.steps = 1`), yielding `(2 * m + 1) * 2 ^ m`
total steps (`≤ 2 * (runMultiTapeAffineOddRouteWithSteps m w b col).2` for all `1 ≤ m`). -/
def runMultiTapeAffineOddRouteFullSteps {α : Type*} [Zero α] : ℕ → ℕ → ℕ → (ℕ → α) → Array α × ℕ
  | 0, _w, _b, col =>
    let st := runSequentialScanSteps col 1
    (st.outTape, st.steps)
  | m + 1, w, b, col =>
    let half := 2 ^ m
    let stU := runUnshuffleSteps col (2 * half)
    let bEven := if b % 2 = 0 then b / 2 else (w + b) / 2
    let bOdd := if b % 2 = 0 then (w + b) / 2 else b / 2
    let evenRes := runMultiTapeAffineOddRouteFullSteps m w bEven (read1D stU.evenTape)
    let oddRes := runMultiTapeAffineOddRouteFullSteps m w bOdd (read1D stU.oddTape)
    let stI := runInterleaveParitySteps (b % 2) (read1D evenRes.1) (read1D oddRes.1) (2 * half)
    (stI.outTape, stU.steps + evenRes.2 + oddRes.2 + stI.steps)

@[simp]
theorem runMultiTapeAffineOddRouteFullSteps_snd {α : Type*} [Zero α] (m w b : ℕ) (col : ℕ → α) :
    (runMultiTapeAffineOddRouteFullSteps m w b col).2 = (2 * m + 1) * 2 ^ m := by
  induction m generalizing b col with
  | zero => simp [runMultiTapeAffineOddRouteFullSteps]
  | succ m ih =>
    dsimp only [runMultiTapeAffineOddRouteFullSteps]
    rw [runUnshuffleSteps_steps, runInterleaveParitySteps_steps, ih, ih, pow_succ]
    ring

theorem runMultiTapeAffineOddRouteFullSteps_snd_le {α : Type*} [Zero α]
    (m w b : ℕ) (hm : 1 ≤ m) (col : ℕ → α) :
    (runMultiTapeAffineOddRouteFullSteps m w b col).2 ≤
      2 * (runMultiTapeAffineOddRouteWithSteps m w b col).2 := by
  rw [runMultiTapeAffineOddRouteFullSteps_snd, runMultiTapeAffineOddRouteWithSteps_snd]
  have h1 : 2 * m + 1 ≤ 2 * (2 * m) := by omega
  calc (2 * m + 1) * 2 ^ m
      ≤ (2 * (2 * m)) * 2 ^ m := Nat.mul_le_mul_right (2 ^ m) h1
    _ = 2 * ((2 * m) * 2 ^ m) := by ring

/-- Step-instrumented backward bidiagonal column solver (`solveBidiagonalBwdMaterializedWithSteps`, `[MS]` §§5.1–5.2):
uses the sequential reversal state machines `runBwdRevSteps` and `runReverseSteps` (stepping the read
head by `-1` and write head by `+1` with zero random-access `t1 - 1 - u1`) and returns `(stOut.outTape, stOut.outTape.size)`
(the `t1` output entries to be weighted by `16 * mulBitCost + 16 * addBitCost` per entry in the annotated cost model,
while `stIn.steps + stOut.steps = 2 * (t1 - 1 + t1)` counts all seek and reverse head steps). -/
noncomputable def solveBidiagonalBwdMaterializedWithSteps
    (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) : Array ℂ × ℕ :=
  let stIn := runBwdRevSteps t1 Y t1
  let revArr : Array ℂ := solveBidiagonalFwdMaterialized q t1 c1 c0 (read1D stIn.outTape)
  let stOut := runReverseSteps t1 (read1D revArr) t1
  (stOut.outTape, stOut.outTape.size)

@[simp]
theorem solveBidiagonalBwdMaterializedWithSteps_snd
    (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) :
    (solveBidiagonalBwdMaterializedWithSteps q t1 c0 c1 Y).2 = t1 := by
  simp [solveBidiagonalBwdMaterializedWithSteps]

theorem read1D_solveBidiagonalBwdMaterializedWithSteps_eq
    (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (u1 : ℕ) (hu1 : u1 < t1) :
    read1D (solveBidiagonalBwdMaterializedWithSteps q t1 c0 c1 Y).1 u1 =
      solveBidiagonalBwdQuantized q t1 c0 c1 Y u1 := by
  dsimp only [solveBidiagonalBwdMaterializedWithSteps]
  rw [read1D_runReverseSteps_eq t1 _ t1 u1 hu1,
      read1D_solveBidiagonalFwdMaterialized_eq q t1 c1 c0 _ (t1 - 1 - u1) (by omega),
      solveBidiagonalBwdQuantized_eq_solveBidiagonalFwdQuantized_rev]
  refine solveBidiagonalFwdQuantized_congr_lt q t1 c1 c0 _ (bwdRevRHS t1 Y) (fun k hk => ?_) (t1 - 1 - u1) (by omega)
  rw [read1D_runBwdRevSteps_eq t1 Y t1 k hk]
  rfl

/-- Step-instrumented forward bidiagonal column solver (`solveBidiagonalFwdMaterializedWithSteps`, `[MS]` §§5.1–5.2):
combines `zPartArr` and `zHomArr` via `runSequentialScanSteps` and returns `(outArr, stOut.steps)`. -/
noncomputable def solveBidiagonalFwdMaterializedWithSteps
    (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) : Array ℂ × ℕ :=
  let zPartArr : Array ℂ := buildZPartFwdArray q c0 c1 Y (t1 - 1)
  let zHomArr : Array ℂ := buildZHomFwdArray q c0 c1 (t1 - 1)
  let Z0 : ℂ := complexQuantize q
    ((Y 0 - c1 * read1D zPartArr (t1 - 1)) /
      (c0 + c1 * read1D zHomArr (t1 - 1)))
  let stOut := runSequentialScanSteps (fun u1 =>
    complexQuantize q (read1D zPartArr u1 + Z0 * read1D zHomArr u1)) t1
  (stOut.outTape, stOut.steps)

@[simp]
theorem solveBidiagonalFwdMaterializedWithSteps_snd
    (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) :
    (solveBidiagonalFwdMaterializedWithSteps q t1 c0 c1 Y).2 = t1 := by
  simp [solveBidiagonalFwdMaterializedWithSteps]

theorem read1D_solveBidiagonalFwdMaterializedWithSteps_eq
    (q t1 : ℕ) (c0 c1 : ℂ) (Y : ℕ → ℂ) (u1 : ℕ) (hu1 : u1 < t1) :
    read1D (solveBidiagonalFwdMaterializedWithSteps q t1 c0 c1 Y).1 u1 =
      solveBidiagonalFwdQuantized q t1 c0 c1 Y u1 := by
  dsimp only [solveBidiagonalFwdMaterializedWithSteps]
  rw [read1D_runSequentialScanSteps_eq _ t1 u1 hu1]
  have h := read1D_solveBidiagonalFwdMaterialized_eq q t1 c0 c1 Y u1 hu1
  unfold solveBidiagonalFwdMaterialized at h
  rwa [read1D_materialize1D_of_lt t1 _ hu1] at h

/-- Step-instrumented Nyquist column solver (`solveNyquistMaterializedWithSteps`, `[MS]` §§5.1–5.2):
combines `zPartArr` and `diff` via `runSequentialScanSteps` and returns `(outArr, stOut.steps)`. -/
noncomputable def solveNyquistMaterializedWithSteps
    (q t1 : ℕ) (c0 : ℂ) (Y : ℕ → ℂ) (alt_q : ℂ) : Array ℂ × ℕ :=
  let zPartArr : Array ℂ := buildZPartNyqArray q c0 Y (t1 - 1)
  let alt_part : ℂ := ∑ v ∈ Finset.range t1, (-1 : ℂ) ^ v * read1D zPartArr v
  let diff : ℂ := complexQuantize q ((alt_q - alt_part) / (t1 : ℂ))
  let stOut := runSequentialScanSteps (fun u1 =>
    complexQuantize q (read1D zPartArr u1 + (-1 : ℂ) ^ u1 * diff)) t1
  (stOut.outTape, stOut.steps)

@[simp]
theorem solveNyquistMaterializedWithSteps_snd
    (q t1 : ℕ) (c0 : ℂ) (Y : ℕ → ℂ) (alt_q : ℂ) :
    (solveNyquistMaterializedWithSteps q t1 c0 Y alt_q).2 = t1 := by
  simp [solveNyquistMaterializedWithSteps]

theorem read1D_solveNyquistMaterializedWithSteps_eq
    (q t1 : ℕ) (c0 : ℂ) (Y : ℕ → ℂ) (alt_q : ℂ) (u1 : ℕ) (hu1 : u1 < t1) :
    read1D (solveNyquistMaterializedWithSteps q t1 c0 Y alt_q).1 u1 =
      solveNyquistQuantized q t1 c0 Y alt_q u1 := by
  dsimp only [solveNyquistMaterializedWithSteps]
  rw [read1D_runSequentialScanSteps_eq _ t1 u1 hu1]
  have h := read1D_solveNyquistMaterialized_eq q t1 c0 Y alt_q u1 hu1
  unfold solveNyquistMaterialized at h
  rwa [read1D_materialize1D_of_lt t1 _ hu1] at h

/-- Routes column `u2` of length `t1` from a transposed `r × V` buffer `qHat_T_flat` using
the step-instrumented multi-pass head-step machine `runMultiTapeAffineOddRouteWithSteps` whenever
`2 ^ (Nat.log2 t1) = t1` and `v1Of u2` agrees with `oddStrideInvPow2 (Nat.log2 t1) u2` on `0 .. t1 - 1`,
returning `(colArr, colSteps)` accumulated directly from `stU.steps` and `stI.steps`. -/
noncomputable def routeMaterializedColumnWithSteps (t1 V : ℕ) (v1Of : ℕ → ℕ → ℕ)
    (qHat_T_flat : Array ℂ) (u2 : ℕ) : Array ℂ × ℕ :=
  let m := Nat.log2 t1
  let col : ℕ → ℂ := fun v1 => read1D qHat_T_flat (u2 * V + v1)
  letI := Classical.propDecidable
  if 2 ^ m = t1 ∧ ∀ u1 < t1, v1Of u2 u1 = oddStrideInvPow2 m u2 u1 then
    runMultiTapeAffineOddRouteWithSteps m (oddStrideFactor m u2) 0 col
  else
    let st := runSequentialScanSteps (fun u1 => col (v1Of u2 u1)) t1
    (st.outTape, (2 * m) * 2 ^ m)

/-- Routes column `u2` of length `t1` from a transposed `r × V` buffer `qHat_T_flat`. -/
noncomputable def routeMaterializedColumn (t1 V : ℕ) (v1Of : ℕ → ℕ → ℕ)
    (qHat_T_flat : Array ℂ) (u2 : ℕ) : Array ℂ :=
  (routeMaterializedColumnWithSteps t1 V v1Of qHat_T_flat u2).1

@[simp]
theorem routeMaterializedColumnWithSteps_snd (t1 V : ℕ) (v1Of : ℕ → ℕ → ℕ)
    (qHat_T_flat : Array ℂ) (u2 : ℕ) :
    (routeMaterializedColumnWithSteps t1 V v1Of qHat_T_flat u2).2 =
      (2 * Nat.log2 t1) * 2 ^ (Nat.log2 t1) := by
  unfold routeMaterializedColumnWithSteps
  dsimp only
  split_ifs <;> simp

theorem read1D_routeMaterializedColumnWithSteps_eq (t1 V : ℕ) (v1Of : ℕ → ℕ → ℕ)
    (qHat_T_flat : Array ℂ) (u2 u1 : ℕ) (hu1 : u1 < t1) :
    read1D (routeMaterializedColumnWithSteps t1 V v1Of qHat_T_flat u2).1 u1 =
      read1D qHat_T_flat (u2 * V + v1Of u2 u1) := by
  unfold routeMaterializedColumnWithSteps
  dsimp only
  split_ifs with h
  · rcases h with ⟨ht1_pow, hv1_eq⟩
    have hu1_m : u1 < 2 ^ (Nat.log2 t1) := ht1_pow.symm ▸ hu1
    rw [runMultiTapeAffineOddRouteWithSteps_fst,
        read1D_runMultiTapeAffineOddRoute_oddStrideFactor_eq (Nat.log2 t1) u2 u1 _ hu1_m,
        ← hv1_eq u1 hu1]
  · rw [read1D_runSequentialScanSteps_eq _ t1 u1 hu1]

theorem read1D_routeMaterializedColumn_eq (t1 V : ℕ) (v1Of : ℕ → ℕ → ℕ)
    (qHat_T_flat : Array ℂ) (u2 u1 : ℕ) (hu1 : u1 < t1) :
    read1D (routeMaterializedColumn t1 V v1Of qHat_T_flat u2) u1 =
      read1D qHat_T_flat (u2 * V + v1Of u2 u1) :=
  read1D_routeMaterializedColumnWithSteps_eq t1 V v1Of qHat_T_flat u2 u1 hu1

theorem array_getD_getD_eq_read2D {α : Type*} [Zero α] (mat : Array (Array α)) (i j : ℕ) :
    (mat.getD i #[]).getD j 0 = read2D mat i j := by
  unfold read2D Array.getD
  dsimp only
  by_cases hi : i < mat.size
  · rw [dif_pos hi, dif_pos hi]
    rfl
  · rw [dif_neg hi, dif_neg hi]
    have hj : ¬ (j < (#[] : Array α).size) := by simp
    rw [dif_neg hj]

theorem array_getD_getD_eq_read2D_pair (mat : Array (Array (ℤ × ℤ))) (i j : ℕ) :
    (mat.getD i #[]).getD j (0, 0) = read2D mat i j :=
  array_getD_getD_eq_read2D mat i j

theorem array_getD_eq_read1D {α : Type*} [Zero α] (arr : Array α) (i : ℕ) :
    arr.getD i 0 = read1D arr i := by
  unfold read1D Array.getD
  split_ifs <;> rfl

theorem read1D_array_getD_eq_read2D {α : Type*} [Zero α] (mat : Array (Array α)) (i j : ℕ) :
    read1D (mat.getD i #[]) j = read2D mat i j := by
  rw [← array_getD_eq_read1D, array_getD_getD_eq_read2D]

/-- Materializes a 2D `n1 × n2` array by executing `n1` sequential row scans
`runSequentialScanSteps (f i.val) n2` and summing their `.steps` counters (`sumArrayCosts`). -/
def runScan2DWithSteps {α : Type*} (n1 n2 : ℕ) (f : ℕ → ℕ → α) : Array (Array α) × ℕ :=
  let rows : Array (Array α × ℕ) :=
    Array.ofFn (fun i : Fin n1 =>
      let st := runSequentialScanSteps (f i.val) n2
      (st.outTape, st.steps))
  (Array.ofFn (fun i : Fin n1 => if h : i.val < rows.size then rows[i.val].1 else #[]),
   sumArrayCosts rows)

@[simp]
theorem runScan2DWithSteps_snd {α : Type*} (n1 n2 : ℕ) (f : ℕ → ℕ → α) :
    (runScan2DWithSteps n1 n2 f).2 = n1 * n2 := by
  unfold runScan2DWithSteps
  dsimp only
  refine sumArrayCosts_ofFn_const n1 _ n2 (fun i _ => ?_)
  simp [runSequentialScanSteps_steps]

theorem read2D_runScan2DWithSteps_of_lt {α : Type*} [Zero α] (n1 n2 : ℕ) (f : ℕ → ℕ → α)
    {i j : ℕ} (hi : i < n1) (hj : j < n2) :
    read2D (runScan2DWithSteps n1 n2 f).1 i j = f i j := by
  unfold runScan2DWithSteps
  dsimp only
  rw [read2D_ofFn_of_lt n1 _ hi j]
  simp only [Array.size_ofFn, hi, ↓reduceDIte, Array.getElem_ofFn,
    read1D_runSequentialScanSteps_eq (f i) n2 j hj]

end IntMul
