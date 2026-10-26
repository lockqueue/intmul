import WP.W9c.CMoves

/-!
# WP.W9c.CycState — host stacks and list facts of the cyclic emit kernel

`Loc 3 4`: named `cV` (values, consumed), `cL` (`tapeL`), `cR` (`tapeR`); scratch `cX` (temporary
of `mvNum`) and three more stacks that only the adder uses (as its scratch, restored). `CS` lists
the seven stack contents and `CS.f` is the stack map (`cf_*` read, `cupd_*` update).

Facts about `cycAdd`: the cursor after a wrap test (`qOf`), one step (`cycAdd_cons`), lengths, the
number of wraps `nwr` and its bound `nwr_le` (the contract's `(p + |vs| - 1) / r`).
-/

namespace WP.W9c.CK

open TMFw TMFw.Contracts WP.W7k2

/-- Host stacks of the cyclic emit kernel. -/
abbrev CL := Loc 3 4

/-- values -/
abbrev cV : CL := .inl 0
/-- left tape stack -/
abbrev cL : CL := .inl 1
/-- right tape stack -/
abbrev cR : CL := .inl 2
/-- temporary -/
abbrev cX : CL := .inr 0

/-- The seven stack contents of the cyclic emit kernel. -/
structure CS where
  /-- values -/
  v : List Sym
  /-- left tape stack -/
  l : List Sym
  /-- right tape stack -/
  r : List Sym
  /-- temporary -/
  x : List Sym
  /-- adder scratch -/
  s1 : List Sym
  /-- adder scratch -/
  s2 : List Sym
  /-- adder scratch -/
  s3 : List Sym

/-- The stack map of a record. -/
def CS.f (s : CS) : CL → List Sym
  | .inl i => [s.v, s.l, s.r].getD i.1 []
  | .inr j => [s.x, s.s1, s.s2, s.s3].getD j.1 []

section
variable (v l r x s1 s2 s3 w : List Sym)

@[simp] theorem cf_v : CS.f ⟨v, l, r, x, s1, s2, s3⟩ cV = v := rfl
@[simp] theorem cf_l : CS.f ⟨v, l, r, x, s1, s2, s3⟩ cL = l := rfl
@[simp] theorem cf_r : CS.f ⟨v, l, r, x, s1, s2, s3⟩ cR = r := rfl
@[simp] theorem cf_x : CS.f ⟨v, l, r, x, s1, s2, s3⟩ cX = x := rfl

theorem cupd_v : Function.update (CS.f ⟨v, l, r, x, s1, s2, s3⟩) cV w =
    CS.f ⟨w, l, r, x, s1, s2, s3⟩ := by
  funext k
  by_cases h : k = cV
  · subst h
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    rcases k with ⟨_ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩ <;>
      first | rfl | exact absurd rfl h

theorem cupd_l : Function.update (CS.f ⟨v, l, r, x, s1, s2, s3⟩) cL w =
    CS.f ⟨v, w, r, x, s1, s2, s3⟩ := by
  funext k
  by_cases h : k = cL
  · subst h
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    rcases k with ⟨_ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩ <;>
      first | rfl | exact absurd rfl h

theorem cupd_r : Function.update (CS.f ⟨v, l, r, x, s1, s2, s3⟩) cR w =
    CS.f ⟨v, l, w, x, s1, s2, s3⟩ := by
  funext k
  by_cases h : k = cR
  · subst h
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    rcases k with ⟨_ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩ <;>
      first | rfl | exact absurd rfl h

end

/-- Every stack map is a record. -/
theorem CS.eta (B : CL → List Sym) :
    B = CS.f ⟨B cV, B cL, B cR, B cX, B (.inr 1), B (.inr 2), B (.inr 3)⟩ := by
  funext k
  rcases k with ⟨_ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩ <;> first | rfl | omega

/-! ## Lists -/

theorem drop_eq_getD_cons (l : List ℤ) (q : ℕ) (h : q < l.length) :
    l.drop q = l.getD q 0 :: l.drop (q + 1) := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem take_set_succ : ∀ (l : List ℤ) (q : ℕ) (y : ℤ), q < l.length →
    (l.set q y).take (q + 1) = l.take q ++ [y]
  | [], _, _, h => absurd h (by simp)
  | _ :: _, 0, _, _ => rfl
  | a :: l, q + 1, y, h => by
    simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append]
    rw [take_set_succ l q y (by simpa using h)]

theorem drop_set_succ (l : List ℤ) (q : ℕ) (y : ℤ) : (l.set q y).drop (q + 1) = l.drop (q + 1) :=
  List.drop_set_of_lt (Nat.lt_succ_self q)

theorem tapeL_app (cells : List ℤ) (p : ℕ) (rL : List Sym) :
    tapeL cells p ++ rL = listSyms (cells.take p).reverse ++ Sym.mark :: rL := by
  simp [tapeL]

theorem tapeR_app (cells : List ℤ) (p : ℕ) (rR : List Sym) :
    tapeR cells p ++ rR = listSyms (cells.drop p) ++ Sym.mark :: rR := by
  simp [tapeR]

/-! ## `cycAdd` -/

/-- The cell written by the next value: the cursor after the wrap test. -/
def qOf (r p : ℕ) : ℕ := if p = r then 0 else p

theorem cycAdd_cons (r : ℕ) (cells : List ℤ) (p : ℕ) (v : ℤ) (vs : List ℤ) :
    cycAdd r cells p (v :: vs) =
      cycAdd r (cells.set (qOf r p) (cells.getD (qOf r p) 0 + v)) (qOf r p + 1) vs := rfl

theorem cycAdd_nil (r : ℕ) (cells : List ℤ) (p : ℕ) : cycAdd r cells p [] = (cells, p) := rfl

theorem qOf_lt {r p : ℕ} (hr : 0 < r) (hp : p ≤ r) : qOf r p < r := by
  unfold qOf
  split_ifs with h
  · exact hr
  · omega

/-- The number of wraps while adding `vs` from cursor `p`. -/
def nwr (r : ℕ) : ℕ → List ℤ → ℕ
  | _, [] => 0
  | p, _ :: vs => (if p = r then 1 else 0) + nwr r (qOf r p + 1) vs

theorem nwr_le (r : ℕ) (hr : 0 < r) :
    ∀ (vs : List ℤ) (p : ℕ), p ≤ r → nwr r p vs ≤ (p + vs.length - 1) / r
  | [], _, _ => Nat.zero_le _
  | _ :: vs, p, hp => by
    simp only [nwr, qOf, List.length_cons]
    by_cases h : p = r
    · rw [if_pos h, if_pos h, Nat.zero_add]
      have ih := nwr_le r hr vs 1 hr
      rw [show 1 + vs.length - 1 = vs.length by omega] at ih
      rw [show p + (vs.length + 1) - 1 = vs.length + r by omega, Nat.add_div_right _ hr]
      omega
    · rw [if_neg h, if_neg h]
      have ih := nwr_le r hr vs (p + 1) (by omega)
      rw [show p + 1 + vs.length - 1 = p + vs.length by omega] at ih
      rw [show p + (vs.length + 1) - 1 = p + vs.length by omega]
      omega

#assert_std_axioms cf_v cf_l cf_r cf_x cupd_v cupd_l cupd_r CS.eta drop_eq_getD_cons take_set_succ
  drop_set_succ tapeL_app tapeR_app cycAdd_cons cycAdd_nil qOf_lt nwr_le

end WP.W9c.CK
