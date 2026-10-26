import Contracts.W9.Pipeline
import Contracts.W8
import WP.W7k2.Ops
import WP.W7k2.Arith

/-!
# WP.W9h.Host — host stacks of the root kernels and the transport to `BLoc`

Every root kernel is written over the host `H = Loc 12 nS` (`nS = 24` scratch stacks), so the W7k2
composition layer (`callI`, `HT`, `HT.callI_upd`, …) applies unchanged. Named host stack `i` is the
layout-B stack `lbOf i`: 0 S, 1 W0, 2 TL, 3 TR, 4 RET, 5 RQ, 6 C0, 7 C1, 8 C2, 9 C3, 10 OA, 11 OB.
`eH : H → BLoc nS` is a bijection, so a host triple `HT [] (toH σ) P (toH σ') T` is the stage
contract's `Runs (P.mapStk eH) σ σ' _ T` (`runs_of_HT`).
-/

namespace WP.W9h

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-- Scratch stacks of every root kernel. -/
abbrev nS : ℕ := 24

/-- Host stacks. -/
abbrev H : Type := Loc 12 nS

/-- Named host stack `i` as a layout-B stack. -/
def lbOf (i : Fin 12) : LB :=
  match i.val with
  | 0 => .S | 1 => .W0 | 2 => .TL | 3 => .TR | 4 => .RET | 5 => .RQ
  | 6 => .C0 | 7 => .C1 | 8 => .C2 | 9 => .C3 | 10 => .OA | _ => .OB

/-- Layout-B stack as a named host stack. -/
def finOf : LB → Fin 12
  | .S => 0 | .W0 => 1 | .TL => 2 | .TR => 3 | .RET => 4 | .RQ => 5
  | .C0 => 6 | .C1 => 7 | .C2 => 8 | .C3 => 9 | .OA => 10 | .OB => 11

theorem lbOf_finOf (k : LB) : lbOf (finOf k) = k := by
  cases k <;> rfl

theorem finOf_lbOf (i : Fin 12) : finOf (lbOf i) = i := by
  fin_cases i <;> rfl

/-- The transport bijection. -/
def eH : H → BLoc nS
  | .inl i => .inl (lbOf i)
  | .inr j => .inr j

/-- Its inverse. -/
def eHinv : BLoc nS → H
  | .inl k => .inl (finOf k)
  | .inr j => .inr j

theorem eH_eHinv (x : BLoc nS) : eH (eHinv x) = x := by
  rcases x with k | j
  · exact congrArg Sum.inl (lbOf_finOf k)
  · rfl

theorem eHinv_eH (x : H) : eHinv (eH x) = x := by
  rcases x with i | j
  · exact congrArg Sum.inl (finOf_lbOf i)
  · rfl

theorem eH_injective : Function.Injective eH := fun x y h => by
  rw [← eHinv_eH x, ← eHinv_eH y, h]

/-- Host view of a layout-B state. -/
def toH (σ : BLoc nS → List Sym) : H → List Sym := σ ∘ eH

theorem toH_update (σ : BLoc nS → List Sym) (k : LB) (v : List Sym) :
    toH (Function.update σ (.inl k) v) = Function.update (toH σ) (.inl (finOf k)) v := by
  have e : (.inl k : BLoc nS) = eH (.inl (finOf k)) := by
    show (Sum.inl k : BLoc nS) = Sum.inl (lbOf (finOf k))
    rw [lbOf_finOf]
  unfold toH
  rw [e]
  exact Function.update_comp_eq_of_injective σ eH_injective _ v

/-- **Transport**: a host triple from `toH σ` to `toH σ'` is the layout-B `Runs`. -/
theorem runs_of_HT {R : Type} {P : Prog H (fun _ => Sym) R} {σ σ' : BLoc nS → List Sym} {T : ℕ}
    (h : HT [] (toH σ) P (toH σ') T) : Runs (P.mapStk eH) σ σ' (fun _ => True) T := by
  have h1 := Runs.embed eH_injective (HT.runs h) σ (fun _ => rfl)
  intro s hs
  obtain ⟨s', t, e, ⟨hin, -, -⟩, ht⟩ := h1 s hs
  refine ⟨s', t, e, ⟨?_, trivial⟩, ht⟩
  funext x
  rw [← eH_eHinv x]
  exact hin (eHinv x)

theorem closed_mapStk_eH {R : Type} {P : Prog H (fun _ => Sym) R} (h : P.Closed) :
    (P.mapStk eH).Closed :=
  freeBelow_mapStk eH P 0 h

/-! ## Host names -/

/-- The level stream `S`. -/
abbrev hS : H := .inl 0
/-- The header stack `C0`. -/
abbrev hC0 : H := .inl 6
/-- The operand / result stack `OA`. -/
abbrev hOA : H := .inl 10
/-- The operand stack `OB`. -/
abbrev hOB : H := .inl 11
/-- Scratch stack `j`. -/
abbrev sc (j : Fin nS) : H := .inr j

theorem toH_S (σ : BLoc nS → List Sym) : toH σ hS = σ (.inl .S) := rfl
theorem toH_C0 (σ : BLoc nS → List Sym) : toH σ hC0 = σ (.inl .C0) := rfl
theorem toH_OA (σ : BLoc nS → List Sym) : toH σ hOA = σ (.inl .OA) := rfl
theorem toH_OB (σ : BLoc nS → List Sym) : toH σ hOB = σ (.inl .OB) := rfl

theorem finOf_S : finOf .S = 0 := rfl
theorem finOf_OA : finOf .OA = 10 := rfl
theorem finOf_OB : finOf .OB = 11 := rfl

#assert_std_axioms lbOf_finOf finOf_lbOf eH_eHinv eHinv_eH eH_injective toH_update runs_of_HT
  closed_mapStk_eH toH_S toH_C0 toH_OA toH_OB

end WP.W9h
