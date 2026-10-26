import WP.W6a.DivRound

/-!
# WP.W6a.Smoke — run the compiled machines (`#eval`)

`divModProg` and `divRoundProg` are parametrized by the `W3_subNat` program, which W3 proves in
parallel. To run them now we instantiate them with `tsub`.

* `tsub` is **unverified test scaffolding**: a simple borrow-subtractor with three scratch stacks.
  It is used by no theorem.

**How the machines run.**

* `runProg` runs the compiled machine `machine p σ0` (framework `Sim`) under Mathlib's `TM2.step`.
  This is exactly the code that `toFinTM2` packages, and the setting of `machine_run`.
* We do not build the `FinTM2` itself. Its `Fintype` field for the register type
  `σ × Option (Option (Lab p))` has about 10⁸ elements here, and computing it ran out of memory
  if materialized eagerly as a `Fintype` table.
* By `machine_run`, a run that halts after `n` steps has `Eval` cost `n − 1`.

**What each row checks.**

* The outputs.
* That the operands are restored and the scratch stacks are left empty.
* The step count, against the proved bounds `(2·Cs + 70)·(|a|·|b| + |a| + |b| + 1)` (`divMod`) and
  `(2·Cs + 140)·(…)` (`divRound`). These are evaluated at `Cs = 25`.
* `Cs = 25` bounds `tsub`'s measured cost on these inputs (`rowSub`). That is a measurement, not a
  proof.
-/

namespace WP.W6a.Smoke

open TMFw TMFw.Lib TMFw.Contracts Computability Turing

/-! ## Running a compiled program -/

/-- Run the compiled machine of `p` from user stacks `S`, for at most `fuel` steps. On halting,
return the number of steps and the final user stacks. -/
def runProg {K : Type} [DecidableEq K] {σ : Type} (p : Prog K (fun _ => Sym) σ) (σ0 : σ)
    (S : K → List Sym) (fuel : ℕ) : Option (ℕ × (K → List Sym)) :=
  go fuel 0 ⟨some (some p.entry), (σ0, none), liftStk S []⟩
where
  /-- the step loop -/
  go : ℕ → ℕ → TM2.Cfg (MachΓ K (fun _ => Sym) (Option p.Lab)) (Option p.Lab)
      (σ × Option (Option p.Lab)) → Option (ℕ × (K → List Sym))
    | 0, _, _ => none
    | fuel + 1, n, c =>
      match TM2.step (machine p σ0) c with
      | none => some (n, fun k => c.stk (some k))
      | some c' => go fuel (n + 1) c'

/-! ## A test-only subtractor (unverified) -/

/-- Registers of `tsub`: the bit of `x`, the bit of `y`, the borrow. -/
abbrev TReg := Option Sym × Option Sym × Bool

/-- Stacks of `tsub`: named `x y z`, scratch `s0` (difference bits), `s1`, `s2` (saved bits). -/
abbrev TStk := Loc 3 3

/-- Difference bit `x − y − borrow (mod 2)`. -/
def diffBit (v : TReg) : Bool := xor (xor (optBit v.1) (optBit v.2.1)) v.2.2

/-- Borrow out of `x − y − borrow`. -/
def newBorrow (v : TReg) : Bool :=
  (!optBit v.1 && (optBit v.2.1 || v.2.2)) || (optBit v.2.1 && v.2.2)

/-- Move the bit block on `src` onto `dst`, reversing it. -/
def moveAll (src dst : TStk) : Prog TStk (fun _ => Sym) TReg :=
  .seq (.peek src fun v o => (o, v.2)) (.loop (fun v => optIsBit v.1)
    (.seq (.pop src fun v o => (o, v.2)) (.seq (.push dst fun v => v.1.getD .sep)
      (.peek src fun v o => (o, v.2)))))

/-- `z += x − y` for `y ≤ x` (test only). -/
def tsub : Prog TStk (fun _ => Sym) TReg :=
  .seq (.push (.inr 0) fun _ => .mark) (.seq (.push (.inr 1) fun _ => .mark)
  (.seq (.push (.inr 2) fun _ => .mark) (.seq (.load fun v => (v.1, v.2.1, false))
  (.seq (.peek (.inl 0) fun v o => (o, v.2))
  (.seq (.loop (fun v => optIsBit v.1)
      (.seq (.pop (.inl 0) fun v o => (o, v.2))
      (.seq (.push (.inr 1) fun v => v.1.getD .sep)
      (.seq (.peek (.inl 1) fun v o => (v.1, o, v.2.2))
      (.seq (.ite (fun v => optIsBit v.2.1)
          (.seq (.pop (.inl 1) fun v _ => v) (.push (.inr 2) fun v => v.2.1.getD .sep))
          (.load fun v => (v.1, some (.bit false), v.2.2)))
      (.seq (.push (.inr 0) fun v => .bit (diffBit v))
      (.seq (.load fun v => (v.1, v.2.1, newBorrow v))
      (.peek (.inl 0) fun v o => (o, v.2)))))))))
  (.seq (moveAll (.inr 1) (.inl 0)) (.seq (.pop (.inr 1) fun v _ => v)
  (.seq (moveAll (.inr 2) (.inl 1)) (.seq (.pop (.inr 2) fun v _ => v)
  (.seq (.peek (.inr 0) fun v o => (o, v.2))
  (.seq (.loop (fun v => decide (v.1 = some (.bit false)))
      (.seq (.pop (.inr 0) fun v _ => v) (.peek (.inr 0) fun v o => (o, v.2))))
  (.seq (moveAll (.inr 0) (.inl 2)) (.pop (.inr 0) fun v _ => v)))))))))))))

/-! ## Rows: outputs, frame, and step counts -/

/-- Proved `divMod` bound with subtractor constant `Cs`. -/
def boundDM (Cs a b : ℕ) : ℕ := (2 * Cs + 70) * (bitLen a * bitLen b + bitLen a + bitLen b + 1)

/-- Proved `divRound` bound with subtractor constant `Cs`. -/
def boundDR (Cs : ℕ) (num : ℤ) (den : ℕ) : ℕ :=
  (2 * Cs + 140) * (bitLen num.natAbs * bitLen den + bitLen num.natAbs + bitLen den + 1)

/-- `tsub` alone: `(x, y, z = x − y, x and y restored and scratch empty, cost, 25·(|x|+|y|+1))`. -/
def rowSub (x y : ℕ) : ℕ × ℕ × Bool × Bool × ℕ × ℕ :=
  let S : TStk → List Sym := fun k =>
    if k = .inl 0 then natSyms x else if k = .inl 1 then natSyms y else []
  match runProg tsub ((none, none, false) : TReg) S 100000 with
  | none => (x, y, false, false, 0, 0)
  | some (n, S') =>
    (x, y, S' (.inl 2) == natSyms (x - y),
      S' (.inl 0) == natSyms x && S' (.inl 1) == natSyms y && S' (.inr 0) == [] &&
        S' (.inr 1) == [] && S' (.inr 2) == [],
      n - 1, 25 * (bitLen x + bitLen y + 1))

/-- Initial registers of `divMod`. -/
def σ0 : DReg TReg := (none, false, (none, none, .eq), (none, none, false))

/-- `divMod`: `(a, b, q ok, r ok, frame ok, cost, proved bound at Cs = 25)`. -/
def rowDM (a b : ℕ) : ℕ × ℕ × Bool × Bool × Bool × ℕ × ℕ :=
  match runProg (divModProg tsub) σ0 (st (natSyms a) (natSyms b) [] [] [] [] []) 1000000 with
  | none => (a, b, false, false, false, 0, 0)
  | some (n, S) =>
    (a, b, S sQ == natSyms (a / b), S sR == natSyms (a % b),
      S sA == natSyms a && S sB == natSyms b && S sT == [] && S sX == [] && S sZ == [],
      n - 1, boundDM 25 a b)

/-- `divRound`: `(num, den, output ok, frame ok, cost, proved bound at Cs = 25)`. -/
def rowDR (num : ℤ) (den : ℕ) : ℤ × ℕ × Bool × Bool × ℕ × ℕ :=
  match runProg (divRoundProg tsub) ((none, none, (none, none, .eq), σ0) : RReg TReg)
      (rst (intSyms num) (natSyms den) [] [] [] [] []) 1000000 with
  | none => (num, den, false, false, 0, 0)
  | some (n, S) =>
    (num, den, S rO == intSyms (divRoundRatInt num den),
      S rN == intSyms num && S rD == natSyms den && S rY == [] && S rM == [] && S rW1 == [] &&
        S rW2 == [],
      n - 1, boundDR 25 num den)

-- `tsub` measured against `Cs = 25`.
#eval [rowSub 0 0, rowSub 1 1, rowSub 2 1, rowSub 13 5, rowSub 64 1, rowSub 255 255,
  rowSub 1000 999, rowSub 12345 678]

-- `divMod`: quotient, remainder and frame checked; cost against the proved bound.
#eval [rowDM 0 1, rowDM 1 1, rowDM 7 2, rowDM 13 3, rowDM 100 7, rowDM 255 16, rowDM 1000 37,
  rowDM 12345 1, rowDM 12345 12345, rowDM 65535 255]

-- `divRound`: ties toward +∞ (5/2 ↦ 3, −5/2 ↦ −2, 1/2 ↦ 1, −1/2 ↦ 0, −3/2 ↦ −1), and more.
#eval [rowDR 5 2, rowDR (-5) 2, rowDR 7 3, rowDR (-7) 3, rowDR 1 2, rowDR (-1) 2, rowDR (-3) 2,
  rowDR 0 5, rowDR (-1) 5, rowDR 1000 37, rowDR (-1000) 37, rowDR (-12345) 100]

end WP.W6a.Smoke
