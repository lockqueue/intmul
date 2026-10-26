import WP.W7k3.ConcreteStd
import WP.F9.Run

/-!
# WP.W7k3.ConcreteStdRun — the concrete `stdChar` kernel, run

`WP.W7k3.ConcreteStd.progC neg` under `WP.F9.runTabled` (the framework machine): the destination
receives `W7.cplxRec (computableStdCharWithProgramCost q num den neg).1` (the snapshot value), the
inputs and the sixteen scratch stacks (junk at the start) are restored. Row: `(ok, steps)`.
-/

namespace WP.W7k3.ConcreteStdRun

open TMFw TMFw.Contracts WP.W7k2 WP.W7k3 WP.W7k3.ConcreteStd WP.F9

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 9]

/-- All stacks of `Loc 4 16`. -/
def keys : List (Loc 4 16) := (List.finRange 4).map Sum.inl ++ (List.finRange 16).map Sum.inr

/-- Start stacks. -/
def st0 (q num den : ℕ) : Loc 4 16 → List Sym
  | .inl 0 => natSyms q ++ [.mark]
  | .inl 1 => natSyms num ++ [.tag 3]
  | .inl 2 => natSyms den ++ [.sep]
  | _ => junk

/-- `(all stacks as specified, steps)`. -/
def row (neg : Bool) (q num den : ℕ) : Bool × ℕ :=
  let S := st0 q num den
  let E := Function.update S (.inl 3)
    (W7.cplxRec (IntMul.computableStdCharWithProgramCost q num den neg).1 ++ S (.inl 3))
  match runTabled (progC neg) r0C keys ⟨r0C, S⟩ 400000000 with
  | none => (false, 0)
  | some (t, S') => (keys.all fun k => S' k == E k, t)

/-- `stdChar(1/4) = i` on the `2^2` grid (`q = 0`). -/
def r1 : Bool × ℕ := row false 0 1 4

-- `(ok, steps)`.
#eval r1
#guard r1.1

end WP.W7k3.ConcreteStdRun
