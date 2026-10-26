import WP.W9g.DR
import WP.W9g.Pure

/-!
# WP.W9g.Stk — the stacks of the leaf machine

`Stk` names every stack of the leaf kernel. The final contract maps `W0`, `TL`, `TR`, `C0`, `C1` to
the layout-B stacks and every other constructor to a private scratch stack.

| group | stacks |
|---|---|
| layout B | `W0` node workspace, `TL`/`TR` table tape, `C0` header, `C1` precision stack |
| data | `R` results, `A`/`B` combine operands, `A2`/`B2` saved operands, `E`/`O` unshuffle, `Om` twiddle |
| temporaries | `T1`, `T2` (entry macros) |
| counters | `CS` recursion stage, `CK` table skip, `CT` counter temporary |
| parameters | `Q2` (`q_leaf+2`), `ONE` (`1`), `SH`/`DIR` (rescale shift and direction), `HP`, `HK`, `HQ`, `HPin` (header copies) |
| butterfly | `Na`…`Nf` coordinates, `X1`…`X12` intermediate values |
| rounding shift | `U1`, `U2`, `U3` |
| rescale | `RI`, `RO`, `Ra`, `Rc`, `Rd`, `Sg` |
| contract scratch | `pool i` |
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts

/-- Stacks of the leaf machine. -/
inductive Stk
  | W0 | TL | TR | C0 | C1
  | R | A | B | A2 | B2 | E | O | Om | T1 | T2
  | CS | CK | CT
  | Q2 | ONE | SH | DIR | HP | HK | HQ | HPin
  | Na | Nb | Nc | Nd | Ne | Nf
  | X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9 | X10 | X11 | X12
  | U1 | U2 | U3
  | RI | RO | Ra | Rc | Rd | Sg
  | pool (i : Fin 8)
  deriving DecidableEq

theorem pool_inj : Function.Injective Stk.pool := fun _ _ h => Stk.pool.inj h

theorem pool_inj' : ∀ i j, Stk.pool i = Stk.pool j → i = j := fun _ _ h => Stk.pool.inj h

/-- Placement of the rounding shift: `x`, `s`, `z` and the fixed temporaries `U1 U2 U3 T1`. -/
def vDr (x s z : Stk) : Fin 7 → Stk
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => s
  | ⟨2, _⟩ => z
  | ⟨3, _⟩ => .U1
  | ⟨4, _⟩ => .U2
  | ⟨5, _⟩ => .U3
  | _ => .T1

/-- The rounding shift on host stacks `x s z`. -/
def drS (X : Prims) (x s z : Stk) : MProg Stk X.Reg := drH X (vDr x s z) Stk.pool

theorem drS_closed (X : Prims) (x s z : Stk) : (drS X x s z).Closed := drH_closed X _ _

/-- Admissible placements of the rounding shift (decidable side conditions). -/
def DrOK (x s z : Stk) : Prop :=
  (∀ i j, vDr x s z i = vDr x s z j → i = j) ∧ (∀ i j, vDr x s z i ≠ Stk.pool j)

theorem drS_rs {X : Prims} {CL CA CR : ℕ} (hL : ShlOK X.shl CL) (hA : AddOK X.add CA)
    (hR : ShrOK X.shr CR) {x s z : Stk} (hok : DrOK x s z) (x0 : ℤ) (s0 : ℕ) (rx rs : List Sym)
    (σ : Stk → List Sym) (hrx : TermOK rx) (hrs : TermOK rs) (hX : σ x = intSyms x0 ++ rx)
    (hS : σ s = natSyms s0 ++ rs) :
    RS [] (drS X x s z) σ (Function.update σ z (intSyms (drp x0 s0) ++ σ z))
      (drCost CL CA CR (bitLen x0.natAbs) s0) :=
  drH_rs hL hA hR hok.1 pool_inj' hok.2 x0 s0 rx rs σ hrx hrs hX hS

theorem drOK_X5 : DrOK .X5 .Q2 .X7 := by unfold DrOK; decide
theorem drOK_X9a : DrOK .X9 .ONE .X11 := by unfold DrOK; decide
theorem drOK_X9b : DrOK .X9 .ONE .X12 := by unfold DrOK; decide
theorem drOK_Ra : DrOK .Ra .SH .Rc := by unfold DrOK; decide

#assert_std_axioms pool_inj pool_inj' drS_closed drS_rs drOK_X5 drOK_X9a drOK_X9b drOK_Ra

end WP.W9g
