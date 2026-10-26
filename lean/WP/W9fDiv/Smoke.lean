import WP.W9fDiv.Proof
import WP.W6a.Smoke

/-!
# WP.W9fDiv.Smoke — run the compiled machine (`#eval`)

* **The program:** `w9Prog` instantiated with W6a's `divRoundProg tsub`. Here `tsub` is W6a's
  **unverified** test-only subtractor.
* **The run:** the compiled `machine p σ0` under Mathlib's `TM2.step` (`WP.W6a.Smoke.runProg`); no
  `toFinTM2`.

**What each row checks:**

* the output `intSyms (divRoundRatInt a b)` on `z`;
* that `a` and `b` are restored and all scratch stacks are left empty;
* the cost, `steps − 1` by `machine_run`, against the proved bound `(Cr + 5)·(…)`. Here `Cr` is
  `divRoundProg`'s constant `2·Cs + 140`, evaluated with `Cs = 25`, a measured bound for `tsub`.
-/

namespace WP.W9fDiv.Smoke

open TMFw TMFw.Contracts Computability WP.W6a WP.W6a.Smoke

/-- `w9Prog` with W6a's `divRoundProg` and the test subtractor. -/
def prog : Prog FStk (fun _ => Sym) (FReg (RReg TReg)) := w9Prog (divRoundProg tsub)

/-- Initial registers. -/
def ρ0 : FReg (RReg TReg) := (none, none, (none, none, (none, none, .eq), σ0))

/-- The proved bound, for a `divRound` constant `Cr`. -/
def bound (Cr : ℕ) (a b : ℤ) : ℕ :=
  (Cr + 5) * (bitLen a.natAbs * bitLen b.natAbs + bitLen a.natAbs + bitLen b.natAbs + 1)

/-- `(a, b, z ok, frame ok, cost, bound at Cr = 2·25 + 140)`. -/
def row (a b : ℤ) : ℤ × ℤ × Bool × Bool × ℕ × ℕ :=
  let S : FStk → List Sym := fun k =>
    if k = .inl 0 then intSyms a else if k = .inl 1 then intSyms b else []
  match runProg prog ρ0 S 1000000 with
  | none => (a, b, false, false, 0, 0)
  | some (n, S') =>
    (a, b, S' (.inl 2) == intSyms (divRoundRatInt a b),
      S' (.inl 0) == intSyms a && S' (.inl 1) == intSyms b &&
        ([0, 1, 2, 3, 4, 5] : List (Fin 6)).all (fun j => S' (.inr j) == []),
      n - 1, bound (2 * 25 + 140) a b)

-- Ties toward +∞; `b ≤ 0` gives `0`.
#eval [row 5 2, row (-5) 2, row 7 3, row (-7) 3, row 1 2, row (-1) 2, row (-3) 2, row 7 (-3),
  row (-7) (-3), row 7 0, row 0 0, row 0 5, row 1000 37, row (-1000) 37, row (-12345) 100]

end WP.W9fDiv.Smoke
