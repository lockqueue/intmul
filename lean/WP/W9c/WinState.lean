import WP.W9c.CMoves

/-!
# WP.W9c.WinState — host stacks of the window kernel

`Loc 4 4`: named `sD` (digits), `sWn` (window), `sE` (emitted values), `sWc` (counter `W`, never
touched); scratch `sTD`, `sTW` (reversed operand lists), `sU` (unary counter of the zero padding),
`sX` (temporary of `mvNum`). `WS` lists the eight stack contents and `WS.f` is the stack map; the
`f_*` lemmas read one stack and the `upd_*` lemmas turn an update of `WS.f` back into a record.
-/

namespace WP.W9c.CK

open TMFw TMFw.Contracts WP.W7k2

/-- Host stacks of the window kernel. -/
abbrev WL := Loc 4 4

/-- digits -/
abbrev sD : WL := .inl 0
/-- window -/
abbrev sWn : WL := .inl 1
/-- emitted values -/
abbrev sE : WL := .inl 2
/-- the counter `W` (untouched) -/
abbrev sWc : WL := .inl 3
/-- reversed digits -/
abbrev sTD : WL := .inr 0
/-- reversed window -/
abbrev sTW : WL := .inr 1
/-- unary counter -/
abbrev sU : WL := .inr 2
/-- temporary -/
abbrev sX : WL := .inr 3

/-- The eight stack contents of the window kernel. -/
structure WS where
  /-- digits -/
  d : List Sym
  /-- window -/
  w : List Sym
  /-- emitted values -/
  e : List Sym
  /-- counter -/
  c : List Sym
  /-- reversed digits -/
  td : List Sym
  /-- reversed window -/
  tw : List Sym
  /-- unary counter -/
  u : List Sym
  /-- temporary -/
  x : List Sym

/-- The stack map of a record. -/
def WS.f (s : WS) : WL → List Sym
  | .inl i => [s.d, s.w, s.e, s.c].getD i.1 []
  | .inr j => [s.td, s.tw, s.u, s.x].getD j.1 []

section
variable (d w e c td tw u x v : List Sym)

@[simp] theorem f_d : WS.f ⟨d, w, e, c, td, tw, u, x⟩ sD = d := rfl
@[simp] theorem f_w : WS.f ⟨d, w, e, c, td, tw, u, x⟩ sWn = w := rfl
@[simp] theorem f_e : WS.f ⟨d, w, e, c, td, tw, u, x⟩ sE = e := rfl
@[simp] theorem f_c : WS.f ⟨d, w, e, c, td, tw, u, x⟩ sWc = c := rfl
@[simp] theorem f_td : WS.f ⟨d, w, e, c, td, tw, u, x⟩ sTD = td := rfl
@[simp] theorem f_tw : WS.f ⟨d, w, e, c, td, tw, u, x⟩ sTW = tw := rfl
@[simp] theorem f_u : WS.f ⟨d, w, e, c, td, tw, u, x⟩ sU = u := rfl
@[simp] theorem f_x : WS.f ⟨d, w, e, c, td, tw, u, x⟩ sX = x := rfl

theorem upd_d : Function.update (WS.f ⟨d, w, e, c, td, tw, u, x⟩) sD v =
    WS.f ⟨v, w, e, c, td, tw, u, x⟩ := by
  funext k
  by_cases h : k = sD
  · subst h
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    rcases k with ⟨_ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩ <;>
      first | rfl | exact absurd rfl h

theorem upd_w : Function.update (WS.f ⟨d, w, e, c, td, tw, u, x⟩) sWn v =
    WS.f ⟨d, v, e, c, td, tw, u, x⟩ := by
  funext k
  by_cases h : k = sWn
  · subst h
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    rcases k with ⟨_ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩ <;>
      first | rfl | exact absurd rfl h

theorem upd_e : Function.update (WS.f ⟨d, w, e, c, td, tw, u, x⟩) sE v =
    WS.f ⟨d, w, v, c, td, tw, u, x⟩ := by
  funext k
  by_cases h : k = sE
  · subst h
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    rcases k with ⟨_ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩ <;>
      first | rfl | exact absurd rfl h

theorem upd_td : Function.update (WS.f ⟨d, w, e, c, td, tw, u, x⟩) sTD v =
    WS.f ⟨d, w, e, c, v, tw, u, x⟩ := by
  funext k
  by_cases h : k = sTD
  · subst h
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    rcases k with ⟨_ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩ <;>
      first | rfl | exact absurd rfl h

theorem upd_tw : Function.update (WS.f ⟨d, w, e, c, td, tw, u, x⟩) sTW v =
    WS.f ⟨d, w, e, c, td, v, u, x⟩ := by
  funext k
  by_cases h : k = sTW
  · subst h
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    rcases k with ⟨_ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩ <;>
      first | rfl | exact absurd rfl h

theorem upd_u : Function.update (WS.f ⟨d, w, e, c, td, tw, u, x⟩) sU v =
    WS.f ⟨d, w, e, c, td, tw, v, x⟩ := by
  funext k
  by_cases h : k = sU
  · subst h
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    rcases k with ⟨_ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩ <;>
      first | rfl | exact absurd rfl h

end

/-- Every stack map is a record. -/
theorem WS.eta (B : WL → List Sym) :
    B = WS.f ⟨B sD, B sWn, B sE, B sWc, B sTD, B sTW, B sU, B sX⟩ := by
  funext k
  rcases k with ⟨_ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩ <;> first | rfl | omega

#assert_std_axioms f_d f_w f_e f_c f_td f_tw f_u f_x upd_d upd_w upd_e upd_td upd_tw upd_u WS.eta

end WP.W9c.CK
