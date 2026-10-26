import WP.W9fF.KitW3

/-!
# WP.W9fF.Ops — the column ops for S1 (`OpsOK`, `opsOK_exists`)

`OpsOK Mul I C`: every op implementation is `Good` and satisfies `BinOK` against its cost with one
constant `C` (`mul` at every declared width `W`). It is the field-by-field unfolding of W9f's
`Kit` (`WP.W9fF.Kit`, copied from `WP.W9fN.Kit`): `kap C Mul W o` reduces to the stated costs.
`opsOK_exists` follows from `kit_exists_W3` (W5 `mulAt`, W3 `addInt`/`subInt`/`shlVar`/`shrVar`,
W6a `divRound` via W9fDiv, and W9fOps).
-/

namespace WP.W9fF

open TMFw TMFw.Contracts WP.W9fF.IL

/-- The column ops with one cost constant. -/
structure OpsOK (Mul : ℕ → ℕ) (I : Op → IL.OpImpl) (C : ℕ) : Prop where
  good : ∀ o, (I o).Good
  add : IL.BinOK (I .add) (Op.sem .add) (fun a b => C * (bitLen a.natAbs + bitLen b.natAbs + 1))
  sub : IL.BinOK (I .sub) (Op.sem .sub) (fun a b => C * (bitLen a.natAbs + bitLen b.natAbs + 1))
  mul : ∀ W, IL.BinOK (I .mul) (Op.sem .mul)
          (fun a b => C * Mul (max W (max (bitLen a.natAbs) (bitLen b.natAbs))) + C)
  shl : IL.BinOK (I .shl) (Op.sem .shl)
          (fun a b => C * (bitLen a.natAbs + bitLen b.natAbs + b.natAbs + 1))
  sar : IL.BinOK (I .sar) (Op.sem .sar) (fun a b => C * (bitLen a.natAbs + bitLen b.natAbs + 1))
  le : IL.BinOK (I .le) (Op.sem .le) (fun a b => C * (bitLen a.natAbs + bitLen b.natAbs + 1))
  divR : IL.BinOK (I .divR) (Op.sem .divR)
          (fun a b => C * (bitLen a.natAbs * bitLen b.natAbs + bitLen a.natAbs + bitLen b.natAbs + 1))

/-- A kit gives `OpsOK` (each field is `Kit.ok` at the op; `mul` keeps the width `W`). -/
theorem opsOK_of_kit {Mul : ℕ → ℕ} (K : Kit Mul) : OpsOK Mul K.I K.C :=
  ⟨K.good, K.ok 0 .add, K.ok 0 .sub, fun W => K.ok W .mul, K.ok 0 .shl, K.ok 0 .sar, K.ok 0 .le,
    K.ok 0 .divR⟩

theorem opsOK_exists (Mul : ℕ → ℕ) (h5 : W5_mulAt Mul) (h3 : W3_all) (h6 : W6a_all) :
    ∃ (I : Op → IL.OpImpl) (C : ℕ), OpsOK Mul I C := by
  obtain ⟨K⟩ := kit_exists_W3 Mul h5 h3 h6
  exact ⟨K.I, K.C, opsOK_of_kit K⟩

#assert_std_axioms opsOK_of_kit opsOK_exists

end WP.W9fF
