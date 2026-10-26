import WP.Inst.W3
import IntMulTM.Exec.Runner

/-!
# WP.Inst.Smoke — the W3 instances run through `machine p σ0`

Every instance program of `WP.Inst.W3` is run with `IntMulTM.Exec.runMachine` (the TM2 machine itself,
from the `machine_run` start configuration) on operands up to 2–3 words. Each check requires the exact
final contents of the named stacks given by the contract, and all scratch stacks empty again (the
contracts' final states are exact, so scratch is restored). Observations (`isZeroNat`, `cmpNat`,
`splitSign`) live in the registers, which the machine resets when it halts, so only their stacks are
checked here; the observations are covered by the contract theorems (`WP.Inst.W3Ok`).
-/

namespace WP.Inst.Smoke

open TMFw TMFw.Lib TMFw.Contracts IntMulTM.Exec WP.Inst

/-- All stacks of `Loc n m`. -/
def locKeys (n m : ℕ) : List (Loc n m) :=
  (List.finRange n).map Sum.inl ++ (List.finRange m).map Sum.inr

/-- Named stacks `.inl i` from `xs`; scratch stacks empty. -/
def stk0 {n m : ℕ} (xs : List (List Sym)) : Loc n m → List Sym
  | .inl i => xs.getD i.val []
  | .inr _ => []

/-- Run `prog` from `r0` on the named stacks `xs`: steps, final named stacks, scratch all empty. -/
def run {n m : ℕ} {R : Type} (prog : Prog (Loc n m) (fun _ => Sym) R) (r0 : R)
    (xs : List (List Sym)) (fuel : ℕ := 200000) : Option (ℕ × List (List Sym) × Bool) :=
  (runMachine prog r0 (locKeys n m) ⟨r0, stk0 xs⟩ fuel).map fun (t, S) =>
    (t, (List.finRange n).map (fun i => S (.inl i)), (List.finRange m).all fun j => (S (.inr j)).isEmpty)

/-- The run halts with named stacks `ys` and empty scratch. -/
def check {n m : ℕ} {R : Type} (prog : Prog (Loc n m) (fun _ => Sym) R) (r0 : R)
    (xs ys : List (List Sym)) : Bool :=
  match run prog r0 xs with
  | some (_, out, true) => out == ys
  | _ => false

/-- Operand pairs, `b ≤ a`. -/
def pairs : List (ℕ × ℕ) :=
  [(0, 0), (1, 0), (1, 1), (5, 3), (255, 1), (256, 255), (2 ^ 64 - 1, 2 ^ 63 + 5),
    (2 ^ 128 + 7, 3), (2 ^ 191 + 2 ^ 100, 2 ^ 150 - 1)]

/-- Single operands. -/
def nums : List ℕ := [0, 1, 2, 3, 7, 8, 255, 256, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 150 + 12345]

#guard complete (locKeys 3 3)

#guard pairs.all fun (a, b) =>
  check addNat.prog addNat.r0 [natSyms a, natSyms b, []] [natSyms a, natSyms b, natSyms (a + b)] &&
  check addNat.prog addNat.r0 [natSyms b, natSyms a, []] [natSyms b, natSyms a, natSyms (a + b)]

#guard pairs.all fun (a, b) =>
  check subNat.prog subNat.r0 [natSyms a, natSyms b, []] [natSyms a, natSyms b, natSyms (a - b)]

#guard pairs.all fun (a, b) =>
  check copyNat.prog copyNat.r0 [natSyms a, natSyms b] [natSyms a, natSyms a ++ natSyms b] &&
  check cmpNat.prog cmpNat.r0 [natSyms a, natSyms b] [natSyms a, natSyms b]

#guard nums.all fun a =>
  check isZeroNat.prog isZeroNat.r0 [natSyms a] [natSyms a] &&
  check incNat.prog incNat.r0 [natSyms a] [natSyms (a + 1)] &&
  check decNat.prog decNat.r0 [natSyms (a + 1)] [natSyms a] &&
  check natToInt.prog natToInt.r0 [natSyms a] [intSyms (a : ℤ)] &&
  check splitSign.prog splitSign.r0 [intSyms (-(a : ℤ))] [natSyms a] &&
  check dropNat.prog dropNat.r0 [natSyms a] [[]] &&
  check normNat.prog normNat.r0 [natSyms a ++ [Sym.bit false, Sym.bit false]] [natSyms a]

#guard nums.all fun a => [0, 1, 2, 5, 64, 70].all fun c =>
  check splitAt.prog splitAt.r0 [natSyms a, natSyms c, []]
      [natSyms (a / 2 ^ c), natSyms c, natSyms (a % 2 ^ c)] &&
  check concatAt.prog concatAt.r0 [natSyms a, natSyms c, natSyms (a % 2 ^ c)]
      [natSyms (a % 2 ^ c + a * 2 ^ c), natSyms c, []] &&
  check shrVar.prog shrVar.r0 [natSyms a, natSyms c] [natSyms (a / 2 ^ c), natSyms c] &&
  check shlVar.prog shlVar.r0 [natSyms a, natSyms c] [natSyms (a * 2 ^ c), natSyms c] &&
  check (shlConst.prog c) shlConst.r0 [natSyms a] [natSyms (a * 2 ^ c)] &&
  check (shrConst.prog c) shrConst.r0 [natSyms a] [natSyms (a / 2 ^ c)]

-- `(a, b, steps of addNat, steps of subNat)`
#eval pairs.map fun (a, b) =>
  (a, b, (run addNat.prog addNat.r0 [natSyms a, natSyms b, []]).map Prod.fst,
    (run subNat.prog subNat.r0 [natSyms a, natSyms b, []]).map Prod.fst)

end WP.Inst.Smoke
