import WP.W7k1.Concrete
import WP.F9.Run

/-!
# WP.W7k1.ConcreteRun — the concrete W7k1 kernels on the machine (`#eval`)

`WP.F9.runTabled progC r0C keys ⟨r0C, S⟩ fuel` runs the framework machine `machine progC r0C`
(`tabled_eq`; `runTabled_sound` and `runTabled_of_eval` are in `WP.F9.Run`). `keys m` lists every
stack of `Loc 2 m` (`complete` checks it). Input: `x` on `.inl 0` above a `mark` and junk; junk on
the destination `.inl 1` and on every scratch stack. Each row prints
`(halted, destination ok, every other stack restored, machine steps)`: the destination must be the
snapshot value pushed on top of its old content (an `Eval` cost `t` takes `t + 1` steps).
-/

namespace WP.W7k1.ConcreteRun

open TMFw TMFw.Contracts WP.W7k1.Concrete

/-- Every stack of `Loc 2 m`. -/
def keys (m : ℕ) : List (Loc 2 m) := [.inl 0, .inl 1] ++ (List.finRange m).map .inr

/-- Junk. -/
def jk : List Sym := [Sym.bit true, Sym.mark, Sym.bit false, Sym.sep, Sym.tag 5]

/-- Initial stacks: `x` on `.inl 0` above a mark and junk; junk everywhere else. -/
def st (m x : ℕ) : Loc 2 m → List Sym := fun k =>
  if k = .inl 0 then natSyms x ++ Sym.mark :: jk else jk

/-- `(halted, destination ok, every other stack restored, steps)`. -/
def row {m : ℕ} {R : Type} (P : Prog (Loc 2 m) (fun _ => Sym) R) (r0 : R) (x : ℕ)
    (out : List Sym) (fuel : ℕ) : Bool × Bool × Bool × ℕ :=
  match WP.F9.runTabled P r0 (keys m) ⟨r0, st m x⟩ fuel with
  | none => (false, false, false, 0)
  | some (n, S) =>
    (true, S (.inl 1) == out ++ st m x (.inl 1),
      (keys m).all (fun k => k == .inl 1 || S k == st m x k), n)

-- `keys` lists every stack (`Loc 2 6`, `Loc 2 16`).
#eval (WP.F9.complete (keys Isqrt.mC), WP.F9.complete (keys Pi.mC))

-- `W7_isqrt` on `a = 1000`: `⌊√1000⌋ = 31` (the snapshot uses `Nat.sqrt`).
#eval row Isqrt.progC Isqrt.r0C 1000 (natSyms (Nat.sqrt 1000)) 1000000

-- `W7_piScaled`, `B = 1`: `(snapshot value, row)`.
#eval ((IntMul.computablePiScaledWithCost 1).1,
  row Pi.progC Pi.r0C 1 (intSyms (IntMul.computablePiScaledWithCost 1).1) 2000000)

-- `W7_log2Scaled`, `B = 1`: `(snapshot value, row)`.
#eval ((IntMul.computableLog2ScaledWithCost 1).1,
  row Ln.progC Ln.r0C 1 (intSyms (IntMul.computableLog2ScaledWithCost 1).1) 2000000)

-- Larger: `a = 2^20 + 3`, and `B = 4` for `π` and `ln 2`.
#eval row Isqrt.progC Isqrt.r0C 1048579 (natSyms (Nat.sqrt 1048579)) 1000000

#eval ((IntMul.computablePiScaledWithCost 4).1,
  row Pi.progC Pi.r0C 4 (intSyms (IntMul.computablePiScaledWithCost 4).1) 2000000)

#eval ((IntMul.computableLog2ScaledWithCost 4).1,
  row Ln.progC Ln.r0C 4 (intSyms (IntMul.computableLog2ScaledWithCost 4).1) 2000000)

end WP.W7k1.ConcreteRun
