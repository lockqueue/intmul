import WP.W9ex.Concrete
import WP.F9.Run

/-!
# WP.W9ex.ConcreteRun — `runTabled` runs of the concrete extract kernel (Phase F smoke)

`progC` runs under `WP.F9.runTabled`, i.e. the framework machine itself (`tabled_eq`,
`runTabled_sound`). Start: the contract's `C0` header and one-node stream on `S`, junk on `OA` and
on every other stack (including the four scratch stacks). Check: `S = restS`, `OA = hdrSyms
(rootDigits …) ++ OA₀` (the snapshot value), every other stack restored. Rows:
`(stacks ok, steps, proved bound + 1)`.
-/

namespace WP.W9ex.ConcreteRun

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.W9ex.Concrete

/-- Every stack of `BLoc mC`. -/
def keys : List (BLoc mC) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2,
    .inl .C3, .inl .OA, .inl .OB] ++ (List.finRange mC).map .inr

theorem keys_complete : ∀ k : BLoc mC, k ∈ keys := by
  intro k
  rcases k with k | j
  · cases k <;> simp [keys]
  · simp [keys]

/-- Junk (bits, `mark`, the rewind guard). -/
def junk : List Sym := [symGuard, .bit true, .mark, .bit false]

def restS0 : List Sym := [.mark, .bit true]

def oa0 : List Sym := [.bit true, .sep]

/-- Initial stacks. -/
def st0 (b K0 k1 k2 : ℕ) (v : Array (ℤ × ℤ)) : BLoc mC → List Sym
  | .inl .S => streamSyms [v] ++ restS0
  | .inl .C0 => hdrSyms [b, K0, k1, k2] ++ [.sep, .bit true]
  | .inl .OA => oa0
  | _ => junk

/-- `(stacks ok, steps, bound + 1)` for one run. -/
def row (b K0 k1 k2 wR : ℕ) (v : Array (ℤ × ℤ)) : Bool × ℕ × ℕ :=
  let S := st0 b K0 k1 k2 v
  let E := Function.update (Function.update S (.inl .S) restS0) (.inl .OA)
    (hdrSyms (rootDigits b K0 k1 k2 v) ++ oa0)
  let bound := 64 * (2 ^ K0 * (eb wR + b + K0) + rootHdrLen b K0 k1 k2 + 1) + 1
  match runTabled progC r0C keys ⟨r0C, S⟩ 200000 with
  | none => (false, 0, bound)
  | some (n, S') => (keys.all fun k => S' k == E k, n, bound)

def v0 : Array (ℤ × ℤ) := #[(5, -1000), (-3, 700), (0, -255), (7, -513)]

def v1 : Array (ℤ × ℤ) :=
  #[(1, -256), (-2, -257), (0, 0), (9, -767), (-4, -768), (3, 255), (0, -1), (6, -100000)]

def rows : List (Bool × ℕ × ℕ) := [row 3 2 1 2 10 v0, row 5 3 3 5 17 v1, row 0 3 0 0 17 v1]

-- `(stacks ok, steps, bound + 1)`: digits of v0 are 2, 0, 0(, 1); of v1 1, 1, 0, 1, 2, 0, 0, 195
#eval rows
#guard rows.all (·.1)

#assert_std_axioms keys_complete

end WP.W9ex.ConcreteRun
