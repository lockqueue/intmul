import WP.W9s.Concrete
import WP.F9.Run

/-!
# WP.W9s.ConcreteRun — tabled runs of the concrete synthetic FFT

`progC` (WP.W9s.Concrete) runs under `WP.F9.runTabled`, i.e. the framework machine itself
(`tabled_eq`, `runTabled_sound`; `keys_complete` lists every stack).
* Start: `W0 = matSyms Pm`; `C0` holds the PRE header followed by junk; `C1` holds `p_in` followed by
  junk; every other stack (named and scratch) holds junk.
* Check: all 32 stacks after the run. `W0` must hold the snapshot value
  `matSyms (w9Q pSub t1 r (w9Syn t1 r Pm))`; every other stack must be restored.
Each row is `(stacks ok, steps)` (steps as in `machine_run`: cost + 1).
-/

namespace WP.W9s.ConcreteRun

open TMFw TMFw.Contracts TMFw.Contracts.W9 IntMul IntMul.LevelSync WP.F9 WP.W9s.Concrete

attribute [local instance 10000] instZeroIntElementary

/-- Arbitrary content (to check restoration). -/
def junk : List Sym := [.bit true, .tag 9]

/-- All stacks of `BLoc mC`. -/
def keys : List (BLoc mC) :=
  [.inl .S, .inl .W0, .inl .TL, .inl .TR, .inl .RET, .inl .RQ, .inl .C0, .inl .C1, .inl .C2,
    .inl .C3, .inl .OA, .inl .OB] ++ (List.finRange mC).map .inr

theorem keys_complete : ∀ k : BLoc mC, k ∈ keys := by
  intro k
  rcases k with k | k
  · cases k <;> simp [keys]
  · simp [keys]

/-- Start stacks. -/
def st0 (h : PreHdr) (Pm : Array (Array (ℤ × ℤ))) : BLoc mC → List Sym
  | .inl .W0 => matSyms Pm
  | .inl .C0 => hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ junk
  | .inl .C1 => hdrSyms [h.p_in] ++ junk
  | _ => junk

/-- `(all stacks as `W9_synFFT` says, steps)`. -/
def row (h : PreHdr) (Pm : Array (Array (ℤ × ℤ))) : Bool × ℕ :=
  let S := st0 h Pm
  let E := Function.update S (.inl .W0) (matSyms (w9Q h.pSub h.t1 h.r (w9Syn h.t1 h.r Pm)))
  match runTabled progC r0C keys ⟨r0C, S⟩ 5000000 with
  | none => (false, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n)

/-- `t1 = r = 2`. -/
def hA : PreHdr := ⟨2, 3, 1, 2, 2⟩
/-- `t1 = 2`, `r = 4`. -/
def hB : PreHdr := ⟨1, 4, 2, 2, 4⟩
/-- `t1 = r = 4`. -/
def hC : PreHdr := ⟨3, 5, 1, 4, 4⟩

def PA : Array (Array (ℤ × ℤ)) := #[#[(3, -1), (0, 2)], #[(-4, 5), (1, 1)]]
def PB : Array (Array (ℤ × ℤ)) := #[#[(1, 2), (-3, 0), (5, -1), (0, 7)],
  #[(2, 2), (-1, -6), (0, 0), (9, -4)]]
def PC : Array (Array (ℤ × ℤ)) := #[#[(1, 0), (2, -1), (0, 3), (4, 4)],
  #[(-5, 1), (6, 0), (7, 7), (0, -2)], #[(3, 3), (-2, 1), (1, -1), (8, 0)],
  #[(0, 5), (-7, 2), (2, 2), (-1, -1)]]

def rows : List (Bool × ℕ) := [row hA PA, row hB PB, row hC PC]

-- `(stacks ok, steps)`.
#eval rows
#guard rows.all (·.1)

#assert_std_axioms keys_complete

end WP.W9s.ConcreteRun
