/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Arith

/-!
# Driver pre-phase kernel: the rotation statement (`Machine/Layer/DrvPreKDefs.lean`)

**Scope (honest summary).** Definitions and one named statement only; nothing is proved here.
* `rotIPowC e c`: exact multiplication of a coefficient by `i^e` (`e` taken mod `4`).
* `RotIPowStmt`: a whole-array kernel multiplying every coefficient by `i^e` (`e` a compile-time
  parameter), at one width `w`. Its shape is that of `TruncShiftStmt` (`Contracts/Arith.lean`):
  named stacks `0` the source (consumed), `1` the destination, `2` the counter `w` (restored).
  Width changes compose with `truncShift_holds` at shift `0`.

It is proved in `Machine/Layer/DrvPreKRot.lean` (`rotIPow_holds`) and used by the individual
kernel pass `DrvCKernelStmt` (`Machine/Layer/DrvPreDefs.lean`), proved in
`Machine/Layer/DrvPreK.lean`.
-/

namespace SubNLogN.Machine.Layer.DrvPreK

open TMFw TMFw.Contracts SubNLogN.Machine

/-- Exact multiplication of a coefficient by `i^e`: `c`, `i·c = (-im, re)`, `-c`, `-i·c = (im, -re)`
for `e ≡ 0, 1, 2, 3 (mod 4)`. -/
def rotIPowC (e : ℕ) (c : CInt) : CInt :=
  if e % 4 = 0 then c
  else if e % 4 = 1 then (-c.2, c.1)
  else if e % 4 = 2 then (-c.1, -c.2)
  else (c.2, -c.1)

/-- **[CONTRACT] Coefficientwise multiplication by `i^e` at one width.** Every coefficient
`(re, im)` of the array, stored at width `w`, becomes `rotIPowC e (re, im)`, stored at width `w`.
* Compile-time parameter: `e : ℕ` (only `e % 4` matters).
* Named stacks (`Fin 3`): `0` the source array (consumed), `1` the destination, `2` the counter `w`
  (restored).
* Guards: `1 ≤ w`, inputs and outputs fit `w` bits.
* Every other stack is unchanged (restored convention, arbitrary private scratch at entry).
* Cost `C·(V + w + 1)`, `V = cvol w v` (the output volume equals the input volume). -/
def RotIPowStmt : Prop :=
  KContract (Fin 3) ℕ fun e E _ _ _ C P =>
    ∀ (w : ℕ) (v : List (List CInt)) (rest r2 : List Sym) (S : KLoc (Fin 3) E → List Sym),
      1 ≤ w → CArrFits w v → CArrFits w (mapC (rotIPowC e) v) → BlkTerm rest → TermOK r2 →
      S (.inl 0) = carrSyms w v ++ rest → S (.inl 2) = natSyms w ++ r2 →
      Runs P S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (carrSyms w (mapC (rotIPowC e) v) ++ S (.inl 1)))
        (fun _ => True) (C * (cvol w v + w + 1))

example : rotIPowC 1 (3, -2) = (2, 3) ∧ rotIPowC 2 (3, -2) = (-3, 2) ∧
    rotIPowC 3 (3, -2) = (-2, -3) ∧ rotIPowC 4 (3, -2) = (3, -2) := by decide

end SubNLogN.Machine.Layer.DrvPreK
