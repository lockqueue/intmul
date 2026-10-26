import WP.W9e.SmokeStubs

/-!
# WP.W9e.Smoke — run the compiled Q2, Q3+Q4 and Q6 programs (`#eval`)

The programs are `q2Prog`, `q34Prog` and `q6Prog`, with the unverified stubs of SmokeStubs in
place of the hypothesis programs. They run under the framework `machine` (`runProg`).

* **Stub rows** `(post-state ok, cost, contract cost expression at C = 1)`. A stub's measured
  constant is its maximal ratio, rounded up (`cOf`).
* **Phase rows** `(stacks ok, cost, proved bound)`.
  - The first entry checks every local stack after the run: `W0` holds the contract's output, and
    every other stack is restored, including the junk-filled private stacks and the tail under the
    `C0` header.
  - The proved bound is evaluated at the stubs' measured constants: `(CT + 40)·postTransposeBound`,
    `q34K … · routesBound` or `q6K … · outBound`.
  - The width `w` is the maximal coordinate bit length over the phase's input and output.
-/

namespace WP.W9e.Smoke

open IntMul IntMul.LevelSync TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

attribute [local instance 10000] instZeroIntElementary

/-! ## Data -/

/-- Sample entries. -/
def ents : List (ℤ × ℤ) :=
  [(0, 0), (1, -1), (-5, 3), (12, -7), (-2, 0), (6, 9), (-13, -1), (3, 4), (7, -8), (-1, 1)]

/-- Entry `i` of the sample cycle. -/
def ent (i : ℕ) : ℤ × ℤ := ents.getD (i % ents.length) (0, 0)

/-- `n` sample records. -/
def recs (n : ℕ) : List (List Sym) := (List.range n).map fun i => entrySyms (ent i)

/-- Arbitrary content of private stacks (to check restoration). -/
def junk : List Sym := [.bit true, .tag 9]

/-! ## Stub calibration -/

/-- Stacks `l[i]` on named stack `i`. -/
def tStk {n : ℕ} (l : List (List Sym)) : Loc n 0 → List Sym
  | .inl i => l.getD i.val []
  | .inr _ => []

/-- All stacks of `Loc n 0`. -/
def allL (n : ℕ) : List (Loc n 0) := (List.finRange n).map Sum.inl

/-- Run stub `p` from `S` and compare with `E` (and the register test `q`): `(ok, cost, bnd)`. -/
def check {n : ℕ} (p : TP n) (S E : List (List Sym)) (bnd : ℕ)
    (q : SR → Bool := fun _ => true) : Bool × ℕ × ℕ :=
  match runProgV (allL n) p SR.init (tStk S) 100000 with
  | none => (false, 0, bnd)
  | some (t, v, S') => ((allL n).all (fun k => S' k == tStk E k) && q v, t, bnd)

/-- Measured constant: the maximal `⌈cost / bnd⌉`. -/
def cOf (rows : List (Bool × ℕ × ℕ)) : ℕ :=
  rows.foldl (fun m r => max m ((r.2.1 + r.2.2 - 1) / r.2.2)) 0

/-- Transpose `2^a × 2^b`. -/
def rowTr (a b : ℕ) : Bool × ℕ × ℕ :=
  let v := recs (2 ^ a * 2 ^ b)
  check sTr [blk .down v ++ [.tag 7], junk, natSyms a ++ [.mark], natSyms b ++ [.mark]]
    [[.tag 7], blk .down (transposeL (2 ^ a) (2 ^ b) v) ++ junk, natSyms a ++ [.mark],
      natSyms b ++ [.mark]]
    (((blk .down v).length + 1) * (min a b + 1) + (bitLen a + bitLen b + 1))

/-- Odd route `(k, w, b)`. -/
def rowOr (k w b : ℕ) : Bool × ℕ × ℕ :=
  let v := recs (2 ^ k)
  check sOr [blk .down v, junk, natSyms k ++ [.mark], natSyms w, natSyms b ++ [.tag 1]]
    [[], blk .down (oddRouteL k w b v) ++ junk, natSyms k ++ [.mark], natSyms w,
      natSyms b ++ [.tag 1]]
    (((blk .down v).length + 1) * (k + 1))

/-- Odd-stride factor `(k, u2)`. -/
def rowOf (k u2 : ℕ) : Bool × ℕ × ℕ :=
  check sOf [natSyms k ++ [.mark], natSyms u2, junk]
    [natSyms k ++ [.mark], natSyms u2,
      natSyms (TMFw.Contracts.computableOddStrideFactor k u2) ++ junk]
    ((k + 1) ^ 2 + bitLen u2)

/-- `shlVar (a, c)`. -/
def rowShl (a c : ℕ) : Bool × ℕ × ℕ :=
  check sShl [natSyms a ++ [.mark], natSyms c ++ [.tag 3]]
    [natSyms (a * 2 ^ c) ++ [.mark], natSyms c ++ [.tag 3]] (c + bitLen c + 1)

/-- `splitAt (a, c)`. -/
def rowSplit (a c : ℕ) : Bool × ℕ × ℕ :=
  check sSplit [natSyms a ++ [.mark], natSyms c, junk]
    [natSyms (a / 2 ^ c) ++ [.mark], natSyms c, natSyms (a % 2 ^ c) ++ junk]
    (min c (bitLen a) + bitLen c + 1)

/-- `subNat (a, b)`. -/
def rowSub (a b : ℕ) : Bool × ℕ × ℕ :=
  check sSub [natSyms a ++ [.mark], natSyms b, junk]
    [natSyms a ++ [.mark], natSyms b, natSyms (a - b) ++ junk] (bitLen a + bitLen b + 1)

/-- `cmpNat (a, b)`, with the observation. -/
def rowCmp (a b : ℕ) : Bool × ℕ × ℕ :=
  check sCmp [natSyms a ++ [.mark], natSyms b] [natSyms a ++ [.mark], natSyms b]
    (bitLen a + bitLen b + 1) (fun v => v.obs == ordOf a b)

def rowsTr : List (Bool × ℕ × ℕ) :=
  [(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2)].map fun (a, b) => rowTr a b
def rowsOr : List (Bool × ℕ × ℕ) :=
  [(0, 1, 0), (1, 1, 0), (1, 3, 1), (2, 1, 0), (2, 3, 0), (2, 5, 3), (2, 7, 2)].map
    fun (k, w, b) => rowOr k w b
def rowsOf : List (Bool × ℕ × ℕ) :=
  (List.range 3).flatMap fun k => (List.range 4).map fun u2 => rowOf k u2
def rowsShl : List (Bool × ℕ × ℕ) :=
  [0, 1, 5, 12].flatMap fun a => (List.range 4).map fun c => rowShl a c
def rowsSplit : List (Bool × ℕ × ℕ) :=
  [0, 1, 5, 13].flatMap fun a => [0, 1, 2, 3].map fun c => rowSplit a c
def rowsSub : List (Bool × ℕ × ℕ) :=
  [(0, 0), (1, 0), (1, 1), (5, 3), (6, 4), (12, 5), (13, 13)].map fun (a, b) => rowSub a b
def rowsCmp : List (Bool × ℕ × ℕ) :=
  [(0, 0), (0, 1), (1, 0), (5, 3), (4, 6), (12, 12), (13, 2)].map fun (a, b) => rowCmp a b

/-- Measured stub constants. -/
def kTr : ℕ := cOf rowsTr
def kOr : ℕ := cOf rowsOr
def kOf : ℕ := cOf rowsOf
def kShl : ℕ := cOf rowsShl
def kSplit : ℕ := cOf rowsSplit
def kSub : ℕ := cOf rowsSub
def kCmp : ℕ := cOf rowsCmp

-- Stubs: every post-state as the contract says, and the measured constants
-- `[CT, CR, CF, Ch, Cp, Cb, Cc]`.
#eval ((rowsTr ++ rowsOr ++ rowsOf ++ rowsShl ++ rowsSplit ++ rowsSub ++ rowsCmp).all (·.1),
  [kTr, kOr, kOf, kShl, kSplit, kSub, kCmp])
#guard (rowsTr ++ rowsOr ++ rowsOf ++ rowsShl ++ rowsSplit ++ rowsSub ++ rowsCmp).all (·.1)

end WP.W9e.Smoke
