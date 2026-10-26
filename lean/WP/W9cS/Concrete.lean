import WP.W9cS.Main

/-!
# WP.W9cS.Concrete — the concrete spread driver (the witness of `W9_spread_of_spreadRow`)

Concrete spread-driver exports. `W9_spread_of_spreadRow (Mul) (hrow : W9_spreadRow Mul)` takes the row
kernel from its contract; its witness is `⟨max mr 6, Option Sym × Rr, spreadProg Pr, …⟩`. The row
kernel (`W9_spreadRow`) is still open, so everything here is **parametrized by the row kernel's
concrete program** `Pr : Prog (BLoc mr) (fun _ => Sym) Rr` (and its initial registers `r0r`):
`mC mr = max mr 6`, `RC Rr = Option Sym × Rr`, `r0C r0r = (none, r0r)`, `progC Pr = spreadProg Pr`.
The program does not depend on the cost parameter `Mul`. F9 instantiates `Pr` with the row
kernel's `progC` once it exists.
-/

namespace WP.W9cS.Concrete

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9c

/-- Scratch count of the witness, for a row kernel with `mr` scratch stacks. -/
abbrev mC (mr : ℕ) : ℕ := max mr 6

/-- Registers of the witness: the driver's symbol register, then the row kernel's. -/
abbrev RC (Rr : Type) : Type := Option Sym × Rr

/-- Initial registers, from the row kernel's `r0r`. -/
def r0C {Rr : Type} (r0r : Rr) : RC Rr := (none, r0r)

/-- **The witness program of `W9_spread_of_spreadRow`** for the row kernel `Pr`. -/
def progC {mr : ℕ} {Rr : Type} (Pr : Prog (BLoc mr) (fun _ => Sym) Rr) :
    Prog (BLoc (mC mr)) (fun _ => Sym) (RC Rr) :=
  spreadProg Pr

theorem hmC {mr : ℕ} (hmr : mr ≤ w9Scratch) : mC mr ≤ w9Scratch :=
  Nat.max_le.2 ⟨hmr, by decide⟩

theorem closedC {mr : ℕ} {Rr : Type} {Pr : Prog (BLoc mr) (fun _ => Sym) Rr} (hc : Pr.Closed) :
    (progC Pr).Closed :=
  spreadProg_closed hc

#assert_std_axioms hmC closedC

end WP.W9cS.Concrete
