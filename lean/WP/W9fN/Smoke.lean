import WP.W9fN.Lay8
import WP.W6a.Smoke

/-!
# WP.W9fN.Smoke — run the compiled entry macros and the entry loop (`#eval`)

Execution smoke test for `WP.W9fN`. No arithmetic ops (`I0 : Empty → OpImpl`). The program,
on the Nyquist core's layout `LN` (`HK = Loc 8 48`):

`initVars V.all ; popEntry IN (Y1, Y2) ; push mark on ZS ; pushEntry (Z1, Z2) → ZS ;
 whileEnt IN (popEntry IN (Y1, Y2) ; pushEntry (Y1, Y2) → ZS) ; dropVars V.all`.

The run is the compiled `machine p σ0` under Mathlib's `TM2.step` (`WP.W6a.Smoke.runProg`),
never `toFinTM2`. Each row checks:
* `IN = []` and `ZS = blkE (Ys.tail.reverse ++ [(0,0)]) ++ [mark]`;
* every other stack is restored, including junk on a variable stack, on `TMP` and on an unused
  scratch stack;
* `steps − 1` (the `Eval` cost, `machine_run`) against the sum of the proved bounds: `initVars`
  `2·31+1`, `popEntry` `9|y1|+9|y2|+2|e1|+2|e2|+46`, `pushC` `1`, `pushEntry` `7|e1|+7|e2|+26`,
  `whileEnt` `N·(Bc+2)+2` with `Bc = 36·w + 72` (`w` = max coordinate width), `dropVars` `dCost`.
-/

namespace WP.W9fN.Smoke

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fN WP.W9fN.IL WP.W6a.Smoke

/-- No arithmetic operations. -/
def I0 : Empty → OpImpl := fun e => e.elim

/-- Initial registers. -/
def ρ0 : GReg I0 := ((none, .eq), fun e => e.elim)

/-- The loop body: move one entry from `IN` to `ZS` through `Y1, Y2`. -/
def body : Prog HK (fun _ => Sym) (GReg I0) :=
  (hM I0 (popEntry kIN (vL .Y1) (vL .Y2) kTMP)).seq (hM I0 (pushEntry (vL .Y1) (vL .Y2) kZS kTMP))

/-- The smoke program. -/
def prog : Prog HK (fun _ => Sym) (GReg I0) :=
  (hM I0 (LN.initVars V.all)).seq
    ((hM I0 (popEntry kIN (vL .Y1) (vL .Y2) kTMP)).seq
      ((hM I0 (pushC kZS .mark)).seq
        ((hM I0 (pushEntry (vL .Z1) (vL .Z2) kZS kTMP)).seq
          ((whileEnt I0 kIN body).seq (hM I0 (LN.dropVars V.all))))))

/-- All host stacks. -/
def allHK : List HK := (List.finRange 8).map Sum.inl ++ (List.finRange 48).map Sum.inr

/-- Junk below the working stacks (restoration check). -/
def junk : List Sym := [Sym.tag 3, Sym.bit true, Sym.sep]

/-- Initial stacks: the input block on `IN`, junk on `Y1`'s stack, on `TMP` and on `.inr 40`. -/
def S0 (Ys : List (ℤ × ℤ)) : HK → List Sym := fun k =>
  if k = kIN then blkE Ys
  else if k = vL .Y1 ∨ k = kTMP ∨ k = (.inr 40 : HK) then junk
  else []

/-- Width of a coordinate pair. -/
def wE (y : ℤ × ℤ) : ℕ := max (bitLen y.1.natAbs) (bitLen y.2.natAbs)

/-- The sum of the proved bounds. -/
def bound (Ys : List (ℤ × ℤ)) : ℕ :=
  let y0 := Ys.headD (0, 0)
  let yl := Ys.getLastD (0, 0)
  let w := (Ys.map wE).foldr max 0
  let N := Ys.length - 1
  (2 * 31 + 1) + (9 * bitLen y0.1.natAbs + 9 * bitLen y0.2.natAbs + 46) + 1 + 26 +
    (N * ((36 * w + 72) + 2) + 2) +
    (31 * 6 + 1 + 2 * bitLen yl.1.natAbs + 2 * bitLen yl.2.natAbs)

/-- `(|Ys|, IN ok, ZS ok, others restored, steps − 1, bound)`. -/
def row (Ys : List (ℤ × ℤ)) : ℕ × Bool × Bool × Bool × ℕ × ℕ :=
  match runProg prog ρ0 (S0 Ys) 1000000 with
  | none => (Ys.length, false, false, false, 0, 0)
  | some (n, S') =>
    (Ys.length, S' kIN == [],
      S' kZS == blkE (Ys.tail.reverse ++ [(0, 0)]) ++ [Sym.mark],
      allHK.all (fun k => k == kIN || k == kZS || S' k == S0 Ys k),
      n - 1, bound Ys)

#eval [row [(1, 2), (-3, 4)], row [(0, 0), (5, -6), (-7, 8), (9, 10)],
  row [(3, -1), (-12, 7), (100, -255), (0, 1), (-1, 0), (65535, -2), (17, 33), (-4096, 4095)]]

end WP.W9fN.Smoke
