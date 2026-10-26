import WP.W9fC.Prims
import Contracts.W9.Post

/-!
# WP.W9fC.State — the stacks the column driver changes

`cst σ V` is the stack map that equals `V` on the twelve stacks the driver changes (named `W0 TR TL
C3 RQ C0`, scratch `0..5` = `M M2 T A CT CW`) and `σ` elsewhere. Scratch `6` (`X`) is the temporary
of `copyBlock`/`inc`/`dec`, which restore it. `Function.update` on a changed stack is a field update
of `V` (`upd_*`), so every intermediate state of the proofs stays in `cst` form.
-/

namespace WP.W9fC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9comp

/-- Values of the twelve stacks the driver changes. -/
structure Vals where
  w0 : List Sym
  tr : List Sym
  tl : List Sym
  c3 : List Sym
  rq : List Sym
  c0 : List Sym
  sm : List Sym
  sm2 : List Sym
  st : List Sym
  sa : List Sym
  sct : List Sym
  scw : List Sym

namespace Vals

/-! Setters. The `upd_*` lemmas produce `cst σ (V.setF x)`: chains of steps then build terms of
linear size (a structure instance `{V with f := x}` copies every other field of `V`). -/

def setW0 (V : Vals) (x : List Sym) : Vals := { V with w0 := x }
def setTr (V : Vals) (x : List Sym) : Vals := { V with tr := x }
def setTl (V : Vals) (x : List Sym) : Vals := { V with tl := x }
def setC3 (V : Vals) (x : List Sym) : Vals := { V with c3 := x }
def setRq (V : Vals) (x : List Sym) : Vals := { V with rq := x }
def setC0 (V : Vals) (x : List Sym) : Vals := { V with c0 := x }
def setSm (V : Vals) (x : List Sym) : Vals := { V with sm := x }
def setSm2 (V : Vals) (x : List Sym) : Vals := { V with sm2 := x }
def setSt (V : Vals) (x : List Sym) : Vals := { V with st := x }
def setSa (V : Vals) (x : List Sym) : Vals := { V with sa := x }
def setSct (V : Vals) (x : List Sym) : Vals := { V with sct := x }
def setScw (V : Vals) (x : List Sym) : Vals := { V with scw := x }

end Vals

variable {m : ℕ}

/-- `V` on the changed stacks, `σ` elsewhere. -/
def cst (σ : BLoc m → List Sym) (V : Vals) : BLoc m → List Sym
  | .inl .W0 => V.w0
  | .inl .TR => V.tr
  | .inl .TL => V.tl
  | .inl .C3 => V.c3
  | .inl .RQ => V.rq
  | .inl .C0 => V.c0
  | .inl k => σ (.inl k)
  | .inr ⟨0, _⟩ => V.sm
  | .inr ⟨1, _⟩ => V.sm2
  | .inr ⟨2, _⟩ => V.st
  | .inr ⟨3, _⟩ => V.sa
  | .inr ⟨4, _⟩ => V.sct
  | .inr ⟨5, _⟩ => V.scw
  | .inr j => σ (.inr j)

/-- Scratch stacks of the driver. -/
def sM (hm : 7 ≤ m) : BLoc m := .inr ⟨0, by omega⟩
def sM2 (hm : 7 ≤ m) : BLoc m := .inr ⟨1, by omega⟩
def sT (hm : 7 ≤ m) : BLoc m := .inr ⟨2, by omega⟩
def sA (hm : 7 ≤ m) : BLoc m := .inr ⟨3, by omega⟩
def sCT (hm : 7 ≤ m) : BLoc m := .inr ⟨4, by omega⟩
def sCW (hm : 7 ≤ m) : BLoc m := .inr ⟨5, by omega⟩
def sX (hm : 7 ≤ m) : BLoc m := .inr ⟨6, by omega⟩

section Upd

variable (σ : BLoc m → List Sym) (V : Vals) (x : List Sym)

theorem upd_w0 : Function.update (cst σ V) (.inl .W0) x = cst σ (V.setW0 x) := by
  funext k
  rw [Function.update_apply]
  split_ifs with hk
  · subst hk; rfl
  · rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
    · cases k <;> first | rfl | exact absurd rfl hk
    all_goals rfl

theorem upd_tr : Function.update (cst σ V) (.inl .TR) x = cst σ (V.setTr x) := by
  funext k
  rw [Function.update_apply]
  split_ifs with hk
  · subst hk; rfl
  · rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
    · cases k <;> first | rfl | exact absurd rfl hk
    all_goals rfl

theorem upd_tl : Function.update (cst σ V) (.inl .TL) x = cst σ (V.setTl x) := by
  funext k
  rw [Function.update_apply]
  split_ifs with hk
  · subst hk; rfl
  · rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
    · cases k <;> first | rfl | exact absurd rfl hk
    all_goals rfl

theorem upd_c3 : Function.update (cst σ V) (.inl .C3) x = cst σ (V.setC3 x) := by
  funext k
  rw [Function.update_apply]
  split_ifs with hk
  · subst hk; rfl
  · rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
    · cases k <;> first | rfl | exact absurd rfl hk
    all_goals rfl

theorem upd_rq : Function.update (cst σ V) (.inl .RQ) x = cst σ (V.setRq x) := by
  funext k
  rw [Function.update_apply]
  split_ifs with hk
  · subst hk; rfl
  · rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
    · cases k <;> first | rfl | exact absurd rfl hk
    all_goals rfl

theorem upd_c0 : Function.update (cst σ V) (.inl .C0) x = cst σ (V.setC0 x) := by
  funext k
  rw [Function.update_apply]
  split_ifs with hk
  · subst hk; rfl
  · rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
    · cases k <;> first | rfl | exact absurd rfl hk
    all_goals rfl

variable (hm : 7 ≤ m)

theorem upd_sm : Function.update (cst σ V) (sM hm) x = cst σ (V.setSm x) := by
  funext k
  rw [Function.update_apply]
  split_ifs with hk
  · subst hk; rfl
  · rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
    · cases k <;> rfl
    all_goals first | rfl | exact absurd rfl hk

theorem upd_sm2 : Function.update (cst σ V) (sM2 hm) x = cst σ (V.setSm2 x) := by
  funext k
  rw [Function.update_apply]
  split_ifs with hk
  · subst hk; rfl
  · rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
    · cases k <;> rfl
    all_goals first | rfl | exact absurd rfl hk

theorem upd_st : Function.update (cst σ V) (sT hm) x = cst σ (V.setSt x) := by
  funext k
  rw [Function.update_apply]
  split_ifs with hk
  · subst hk; rfl
  · rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
    · cases k <;> rfl
    all_goals first | rfl | exact absurd rfl hk

theorem upd_sa : Function.update (cst σ V) (sA hm) x = cst σ (V.setSa x) := by
  funext k
  rw [Function.update_apply]
  split_ifs with hk
  · subst hk; rfl
  · rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
    · cases k <;> rfl
    all_goals first | rfl | exact absurd rfl hk

theorem upd_sct : Function.update (cst σ V) (sCT hm) x = cst σ (V.setSct x) := by
  funext k
  rw [Function.update_apply]
  split_ifs with hk
  · subst hk; rfl
  · rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
    · cases k <;> rfl
    all_goals first | rfl | exact absurd rfl hk

theorem upd_scw : Function.update (cst σ V) (sCW hm) x = cst σ (V.setScw x) := by
  funext k
  rw [Function.update_apply]
  split_ifs with hk
  · subst hk; rfl
  · rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
    · cases k <;> rfl
    all_goals first | rfl | exact absurd rfl hk

end Upd

/-- Two updates in a row (term-mode composition of `upd_*` lemmas). -/
theorem upd2 {S S1 S2 : BLoc m → List Sym} {a b : BLoc m} {x y : List Sym}
    (h1 : Function.update S a x = S1) (h2 : Function.update S1 b y = S2) :
    Function.update (Function.update S a x) b y = S2 := by
  rw [h1, h2]

/-- The values of `σ` itself. -/
def V0 (σ : BLoc m → List Sym) (hm : 7 ≤ m) : Vals :=
  ⟨σ (.inl .W0), σ (.inl .TR), σ (.inl .TL), σ (.inl .C3), σ (.inl .RQ), σ (.inl .C0),
    σ (sM hm), σ (sM2 hm), σ (sT hm), σ (sA hm), σ (sCT hm), σ (sCW hm)⟩

theorem cst_V0 (σ : BLoc m → List Sym) (hm : 7 ≤ m) : cst σ (V0 σ hm) = σ := by
  funext k
  rcases k with k | ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
  · cases k <;> rfl
  all_goals rfl

/-- Scratch stacks are unchanged between two `cst` states with the same scratch values. -/
theorem cst_inr_eq (σ : BLoc m → List Sym) {V V' : Vals} (h1 : V.sm = V'.sm) (h2 : V.sm2 = V'.sm2)
    (h3 : V.st = V'.st) (h4 : V.sa = V'.sa) (h5 : V.sct = V'.sct) (h6 : V.scw = V'.scw)
    (j : Fin m) : cst σ V' (.inr j) = cst σ V (.inr j) := by
  rcases j with ⟨_ | _ | _ | _ | _ | _ | j, hj⟩
  · exact h1.symm
  · exact h2.symm
  · exact h3.symm
  · exact h4.symm
  · exact h5.symm
  · exact h6.symm
  · rfl

#assert_std_axioms upd_w0 upd_tr upd_tl upd_c3 upd_rq upd_c0 upd_sm upd_sm2 upd_st upd_sa upd_sct
  upd_scw upd2 cst_V0 cst_inr_eq

end WP.W9fC
