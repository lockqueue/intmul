import WP.W4o.OddRoute
import IntMulTM.Framework.Sim

/-!
# WP.W4o.Smoke — compiled runs of the odd-stride router

`runRoute` compiles `oddRouteProg` to the framework machine (`machine p σ0`, Mathlib's
`TM2.step`) and runs it from an explicit initial stack assignment (no preload prefix). The step
count is the program's evaluation cost plus one final step (register reset and halt), see
`machine_run`. Each run checks the destination stack against the contract's pure spec
`blk .down (oddRouteL k w b v)`, that the source is consumed, that every other stack is
restored, and the step count against the proved bound `300·(|blk|+1)·(k+1)`.
-/

namespace TMFw.W4o.Smoke

open TMFw TMFw.Lib TMFw.Contracts Turing Computability

/-- Re-materialize the stack function of a configuration. `TM2.step` builds the new stack
function as a `Function.update` closure over the old one, so without this the closure chain (and
the interpreter's recursion depth) grows with the number of steps. -/
def normCfg {Λ σ' : Type} (c : TM2.Cfg (MachΓ L54 (fun _ => Sym) Λ) Λ σ') :
    TM2.Cfg (MachΓ L54 (fun _ => Sym) Λ) Λ σ' :=
  let s0 : List Λ := c.stk none
  let x : List Sym := c.stk (some sX)
  let y : List Sym := c.stk (some sY)
  let kk : List Sym := c.stk (some sK)
  let w : List Sym := c.stk (some sW)
  let bs : List Sym := c.stk (some sBs)
  let a : List Sym := c.stk (some sA)
  let b : List Sym := c.stk (some sB)
  let t : List Sym := c.stk (some sT)
  let u : List Sym := c.stk (some sV)
  ⟨c.l, c.var, fun k => match k with
    | none => s0
    | some k => st9 x y kk w bs a b t u k⟩

/-- Run `machine p σ0` from stacks `S`: `some (steps, the nine final stacks)` if it halts. -/
def runMach9 (p : RProg L54) (σ0 : Reg) (S : L54 → List Sym) (fuel : ℕ) :
    Option (ℕ × List (List Sym)) :=
  go fuel 0 ⟨some (some p.entry), (σ0, none), liftStk S []⟩
where
  /-- the loop -/
  go : ℕ → ℕ → TM2.Cfg (MachΓ L54 (fun _ => Sym) (Option p.Lab)) (Option p.Lab)
      (Reg × Option (Option p.Lab)) → Option (ℕ × List (List Sym))
    | 0, _, _ => none
    | fuel + 1, n, c =>
      match TM2.step (machine p σ0) c with
      | none => some (n, [c.stk (some sX), c.stk (some sY), c.stk (some sK), c.stk (some sW),
          c.stk (some sBs), c.stk (some sA), c.stk (some sB), c.stk (some sT), c.stk (some sV)])
      | some c' => go fuel (n + 1) (normCfg c')

/-- Initial stacks of the contract: block on `sX` (bottom after it), `k`, `w`, `b` with a
`tag 3` terminator, and some junk on the destination and the scratch stacks. -/
def initS (k w b : ℕ) (v : List (List Sym)) : L54 → List Sym :=
  st9 (blk .down v) [Sym.tag 7] (natSyms k ++ [Sym.tag 3]) (natSyms w ++ [Sym.tag 3])
    (natSyms b ++ [Sym.tag 3]) [Sym.bit true] [Sym.sep] [] [Sym.bit false, Sym.mark]

/-- Expected final stacks. -/
def finalS (k w b : ℕ) (v : List (List Sym)) : List (List Sym) :=
  [[], blk .down (oddRouteL k w b v) ++ [Sym.tag 7], natSyms k ++ [Sym.tag 3],
    natSyms w ++ [Sym.tag 3], natSyms b ++ [Sym.tag 3], [Sym.bit true], [Sym.sep], [],
    [Sym.bit false, Sym.mark]]

/-- Run the router on `(k, w, b, v)`. -/
def runRoute (k w b : ℕ) (v : List (List Sym)) : Option (ℕ × List (List Sym)) :=
  runMach9 oddRouteProg (none, none, false) (initS k w b v) 2000000

/-- `(steps, output correct and all other stacks restored, steps ≤ bound + 1)`. -/
def check (k w b : ℕ) (v : List (List Sym)) : Option (ℕ × Bool × Bool) :=
  (runRoute k w b v).map fun (n, stks) =>
    (n, decide (stks = finalS k w b v),
      decide (n ≤ 300 * ((blk .down v).length + 1) * (k + 1) + 1))

/-- Records `⟨i⟩ = bits of i, then sep` (LSB first, so distinct and of varying length). -/
def recs (n : ℕ) : List (List Sym) := (List.range n).map fun i => natSyms i ++ [Sym.sep]

-- `u ↦ (3u + 1) mod 4` (the contract's pinned example): output = [v1, v0, v3, v2]
#guard (runRoute 2 3 1 (recs 4)).map (·.2.getD 1 []) =
  some (blk .down [natSyms 1 ++ [Sym.sep], natSyms 0 ++ [Sym.sep], natSyms 3 ++ [Sym.sep],
    natSyms 2 ++ [Sym.sep]] ++ [Sym.tag 7])
#guard (check 2 3 1 (recs 4)).map (·.2) = some (true, true)
-- k = 0: one record
#guard (check 0 1 0 (recs 1)).map (·.2) = some (true, true)
-- w = 2^(k+1) − 1 (largest admissible multiplier), b = 2^k − 1
#guard (check 3 15 7 (recs 8)).map (·.2) = some (true, true)
-- w = 5, b = 6, mixed payloads (signs, sep2)
#guard (check 3 5 6 ((recs 8).map fun r => Sym.pos :: Sym.sep2 :: r)).map (·.2) =
  some (true, true)
-- b = 0, w = 1: identity
#guard (check 4 1 0 (recs 16)).map (·.2) = some (true, true)
-- the pipeline's multiplier (computableOddStrideFactor 4 3 = 13), b = 0
#guard (check 4 13 0 (recs 16)).map (·.2) = some (true, true)

#eval [check 0 1 0 (recs 1), check 2 3 1 (recs 4), check 3 15 7 (recs 8),
  check 4 13 0 (recs 16), check 5 21 9 (recs 32)]

end TMFw.W4o.Smoke
