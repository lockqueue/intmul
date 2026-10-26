import WP.W9fF.Kit

/-!
# WP.W9fF.Regs — the register type of the forward core is finite and nonempty

The program runs with IntLang's registers `GReg I = (Option Sym × Ordering) × ((o : Op) → (I o).R)`;
it is finite and nonempty when every op implementation is good.
-/

namespace WP.W9fF

open TMFw TMFw.Contracts WP.W9fF.IL

/-- Index of an op (for finiteness). -/
def Op.toFin : Op → Fin 7
  | .add => 0 | .sub => 1 | .mul => 2 | .shl => 3 | .sar => 4 | .le => 5 | .divR => 6

theorem Op.toFin_injective : Function.Injective Op.toFin := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

instance : Finite Op := Finite.of_injective Op.toFin Op.toFin_injective

theorem finite_GReg (I : Op → OpImpl) (h : ∀ o, (I o).Good) : Finite (GReg I) := by
  haveI : ∀ o, Finite (I o).R := fun o => (h o).2.1
  infer_instance

theorem nonempty_GReg (I : Op → OpImpl) (h : ∀ o, (I o).Good) : Nonempty (GReg I) :=
  ⟨((none, .eq), fun o => (h o).2.2.some)⟩

#assert_std_axioms Op.toFin_injective finite_GReg nonempty_GReg

end WP.W9fF
