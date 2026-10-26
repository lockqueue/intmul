import WP.W9c.ConcreteKit
import WP.F9.Run

/-!
# WP.W9c.ConcreteSubRun — the concrete unpack, window and cycEmit programs, run

Each program runs under `WP.F9.runTabled` (the framework machine) on its own contract layout, from
inputs satisfying the contract's hypotheses; every other stack (scratch included) starts with junk.
A row is `(ok, steps)`, `ok` iff the final stacks are exactly the contract's:

* `upRow k n Pz` (`W9c_unpack`, `Loc 4 8`): `D = listSyms (unpackSignedKronecker 2^(k-1) n Pz) ++ D`,
  `X` popped to its terminator, everything else restored;
* `wnRow W ds ws` (`W9c_window`, `Loc 4 4`): `winStep W ws ds`;
* `ceRow cells vs p` (`W9c_cycEmit`, `Loc 3 4`): `cycAdd`, read through `tapeL` / `tapeR`.
-/

namespace WP.W9c.ConcreteSubRun

open TMFw TMFw.Contracts WP.F9 WP.W9c WP.W9c.Concrete IntMul

/-- Arbitrary content (restoration check). -/
def junk : List Sym := [.bit true, .tag 9]

/-- All stacks of `Loc a b`. -/
def keys (a b : ℕ) : List (Loc a b) :=
  (List.finRange a).map Sum.inl ++ (List.finRange b).map Sum.inr

/-! ## Unpack -/

def upSt (k n : ℕ) (Pz : ℤ) : Loc 4 8 → List Sym
  | .inl 0 => intSyms Pz ++ [.mark]
  | .inl 1 => natSyms k ++ [.tag 3]
  | .inl 2 => natSyms n ++ [.sep]
  | _ => junk

def upRow (k n : ℕ) (Pz : ℤ) : Bool × ℕ :=
  let S := upSt k n Pz
  let E := Function.update (Function.update S (.inl 0) [.mark]) (.inl 3)
    (listSyms (unpackSignedKronecker ((2 ^ (k - 1) : ℕ) : ℤ) n Pz) ++ S (.inl 3))
  match runTabled (Unp.unpackP uJ) upR0 (keys 4 8) ⟨upR0, S⟩ 5000000 with
  | none => (false, 0)
  | some (t, S') => ((keys 4 8).all fun x => S' x == E x, t)

def upRows : List (Bool × ℕ) :=
  [upRow 3 4 37, upRow 1 3 (-5), upRow 4 0 12345, upRow 2 6 0, upRow 5 3 (2 ^ 14 + 3),
    upRow 8 5 (-(2 ^ 30 + 12345))]

-- `(ok, steps)`
#eval upRows
#guard upRows.all (·.1)

/-! ## Window -/

def wnSt (W : ℕ) (ds ws : List ℤ) : Loc 4 4 → List Sym
  | .inl 0 => listSyms ds ++ [.mark]
  | .inl 1 => listSyms ws ++ [.tag 3]
  | .inl 3 => natSyms W ++ [.sep]
  | _ => junk

def wnRow (W : ℕ) (ds ws : List ℤ) : Bool × ℕ :=
  let S := wnSt W ds ws
  let E := Function.update (Function.update (Function.update S (.inl 0) [.mark]) (.inl 1)
    (listSyms (winStep W ws ds).2 ++ [.tag 3])) (.inl 2) (listSyms (winStep W ws ds).1 ++ S (.inl 2))
  match runTabled (CK.winProg aiI) wnR0 (keys 4 4) ⟨wnR0, S⟩ 5000000 with
  | none => (false, 0)
  | some (t, S') => ((keys 4 4).all fun x => S' x == E x, t)

def wnRows : List (Bool × ℕ) :=
  [wnRow 2 [3, 4, -5] [1, -2], wnRow 3 [1, 2, 3, 4, 5, 6] [0, 0, 0], wnRow 1 [-7] [7],
    wnRow 2 [100, -100] [-1000, 999]]

-- `(ok, steps)`
#eval wnRows
#guard wnRows.all (·.1)

/-! ## Cyclic emit -/

def ceSt (cells vs : List ℤ) (p : ℕ) : Loc 3 4 → List Sym
  | .inl 0 => listSyms vs ++ [.mark]
  | .inl 1 => tapeL cells p ++ [.tag 3]
  | .inl 2 => tapeR cells p ++ [.tag 4]
  | _ => junk

def ceRow (cells vs : List ℤ) (p : ℕ) : Bool × ℕ :=
  let S := ceSt cells vs p
  let r := cycAdd cells.length cells p vs
  let E := Function.update (Function.update (Function.update S (.inl 0) [.mark]) (.inl 1)
    (tapeL r.1 r.2 ++ [.tag 3])) (.inl 2) (tapeR r.1 r.2 ++ [.tag 4])
  match runTabled (CK.cycProg aiI) ceR0 (keys 3 4) ⟨ceR0, S⟩ 5000000 with
  | none => (false, 0)
  | some (t, S') => ((keys 3 4).all fun x => S' x == E x, t)

def ceRows : List (Bool × ℕ) :=
  [ceRow [0, 0, 0, 0] [1, 2, 3] 2, ceRow [5, -5, 10] [1] 3, ceRow [1] [] 0,
    ceRow [0, 0] [1, 2, 3, 4, 5] 1]

-- `(ok, steps)`
#eval ceRows
#guard ceRows.all (·.1)

end WP.W9c.ConcreteSubRun
