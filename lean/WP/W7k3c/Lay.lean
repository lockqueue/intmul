import WP.W7k3c.Mac

/-!
# WP.W7k3c.Lay — scratch layout between the phases of the `W7_c0c1` program

After phase 1 the shared half-erf arguments sit on scratch `0 … 6` (the `v0 … v6` of `sHe`):
`A`, `2^Bint`, `P·2^Bint`, `2^(S+B_e)`, `denZ`, `denZ²`, `N`; all other scratch stacks are empty.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- The scratch contents after phase 1. -/
def V1 (pw ps r : ℕ) : Fin 16 → Option Val :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (fun _ => none)
    0 (some (.int ((vA pw ps : ℕ) : ℤ))))
    1 (some (.int ((2 ^ vBint pw ps : ℕ) : ℤ))))
    2 (some (.nat (vP pw ps * 2 ^ vBint pw ps))))
    3 (some (.int ((2 ^ (vS pw ps + vBe ps) : ℕ) : ℤ))))
    4 (some (.nat (vDZ pw ps r))))
    5 (some (.nat (vDS pw ps r))))
    6 (some (.nat (vN pw ps)))

example (pw ps r : ℕ) : V1 pw ps r 0 = some (.int ((vA pw ps : ℕ) : ℤ)) := rfl
example (pw ps r : ℕ) : V1 pw ps r 6 = some (.nat (vN pw ps)) := rfl
example (pw ps r : ℕ) : V1 pw ps r 9 = none := rfl

/-- The scratch contents after phase 3 (the three half-erf values `h₊`, `h₋`, `h₃` on 10, 11, 7;
shared values still on 0 … 6). -/
def V3 (pw ps r : ℕ) (hP hM h3 : ℤ) : Fin 16 → Option Val :=
  Function.update (Function.update (Function.update (V1 pw ps r)
    7 (some (.int h3))) 10 (some (.int hP))) 11 (some (.int hM))

example (pw ps r : ℕ) (hP hM h3 : ℤ) : V3 pw ps r hP hM h3 2 =
    some (.nat (vP pw ps * 2 ^ vBint pw ps)) := rfl
example (pw ps r : ℕ) (hP hM h3 : ℤ) : V3 pw ps r hP hM h3 10 = some (.int hP) := rfl
example (pw ps r : ℕ) (hP hM h3 : ℤ) : V3 pw ps r hP hM h3 12 = none := rfl

end WP.W7k3c
