import WP.W9gx.Concrete
import WP.F9.Run

/-!
# WP.W9gx.ConcreteRun — the concrete LEAF kernel, run against the snapshot

`progC` (WP.W9gx.Concrete) runs under `runTabled`, i.e. the framework machine itself (`tabled_eq`,
`runTabled_sound`). Start: the contract's layout (`W0 = ⟦x⟧`, the leaf header on `C0` and `p_in` on
`C1`, each with a tail, the leaf body `leafBody K tw` on `TR` with a tail) and junk on every other
named and scratch stack. Check: all 68 stacks after the run; `W0` must be the snapshot's node
`nodeSyms (computableBaseRadix2FFTWithProgramCost p_in p K tw x).1` and every other stack restored.
Each row is `(stacks ok, steps)`, steps counted as in `machine_run` (cost + 1).
-/

namespace WP.W9gx.ConcreteRun

open IntMul TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.F9 WP.W9gx.Concrete

attribute [local instance 10000] instZeroIntElementary

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 9]

/-- All stacks of `BLoc mC`. -/
def keys : List (BLoc mC) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2,
    .inl .C3, .inl .OA, .inl .OB] ++ (List.finRange mC).map Sum.inr

theorem keys_complete : ∀ k : BLoc mC, k ∈ keys := by
  intro k
  rcases k with l | j
  · cases l <;> simp [keys]
  · simp [keys]

/-- Start stacks in the contract's layout. -/
def st0 (p_in p K : ℕ) (tw : Array (Array (ℤ × ℤ))) (x : Array (ℤ × ℤ)) :
    BLoc mC → List Sym
  | .inl .W0 => blkE x.toList
  | .inl .C0 => hdrSyms (leafFields p K) ++ [.tag 2, .bit true]
  | .inl .C1 => hdrSyms [p_in] ++ [.tag 3]
  | .inl .TR => leafBody K tw ++ [.tag 5]
  | _ => junk

/-- `(all stacks as specified, steps)`. -/
def row (p_in p K : ℕ) (tw : Array (Array (ℤ × ℤ))) (x : Array (ℤ × ℤ)) : Bool × ℕ :=
  let S := st0 p_in p K tw x
  let E := Function.update S (.inl .W0)
    (nodeSyms (computableBaseRadix2FFTWithProgramCost p_in p K tw x).1)
  match runTabled progC r0C keys ⟨r0C, S⟩ 100000000 with
  | none => (false, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n)

/-- `K = 0` (one entry: rescale `p_in → q_leaf → p`), `K = 1` (one butterfly stage). -/
def rows : List (Bool × ℕ) :=
  [row 2 3 0 #[] #[(5, -3)],
   row 2 3 1 #[#[(32768, 0), (0, 32768)]] #[(5, -3), (7, 2)]]

-- `(stacks ok, steps)`.
#eval rows
#guard rows.all (·.1)

#assert_std_axioms keys_complete

end WP.W9gx.ConcreteRun
