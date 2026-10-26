import WP.W4o.Basic

/-!
# WP.W4o.RouteState — the router's nine stacks as an explicit record

The router runs over `Loc 5 4`: named stacks `sX` (source), `sY` (destination), `sK` (`k`, never
touched by the recursion), `sW` (`w`), `sBs` (`b`, and the offset blocks of the recursion);
scratch stacks `sA`, `sB`, `sT`, `sV`. `st9 x y k w bs a b t u` is the stack assignment with these
nine components; `st9_eta` writes any assignment this way, and the `upd_*` lemmas push a
`Function.update` into the record, so each step of the router's proof is a plain record rewrite.
-/

namespace TMFw.W4o

open TMFw TMFw.Contracts

/-- The router's stack type. -/
abbrev L54 := Loc 5 4

/-- stack `X` -/
abbrev sX : L54 := .inl 0

/-- stack `Y` -/
abbrev sY : L54 := .inl 1

/-- stack `K` -/
abbrev sK : L54 := .inl 2

/-- stack `W` -/
abbrev sW : L54 := .inl 3

/-- stack `Bs` -/
abbrev sBs : L54 := .inl 4

/-- stack `A` -/
abbrev sA : L54 := .inr 0

/-- stack `B` -/
abbrev sB : L54 := .inr 1

/-- stack `T` -/
abbrev sT : L54 := .inr 2

/-- stack `V` -/
abbrev sV : L54 := .inr 3

/-- The stack assignment with the nine given components. -/
def st9 (x y k w bs a b t u : List Sym) : L54 → List Sym
  | .inl i => if i.val = 0 then x else if i.val = 1 then y else if i.val = 2 then k
      else if i.val = 3 then w else bs
  | .inr j => if j.val = 0 then a else if j.val = 1 then b else if j.val = 2 then t else u

@[simp] theorem st9_X (x y k w bs a b t u : List Sym) : st9 x y k w bs a b t u sX = x := rfl

@[simp] theorem st9_Y (x y k w bs a b t u : List Sym) : st9 x y k w bs a b t u sY = y := rfl

@[simp] theorem st9_K (x y k w bs a b t u : List Sym) : st9 x y k w bs a b t u sK = k := rfl

@[simp] theorem st9_W (x y k w bs a b t u : List Sym) : st9 x y k w bs a b t u sW = w := rfl

@[simp] theorem st9_Bs (x y k w bs a b t u : List Sym) : st9 x y k w bs a b t u sBs = bs := rfl

@[simp] theorem st9_A (x y k w bs a b t u : List Sym) : st9 x y k w bs a b t u sA = a := rfl

@[simp] theorem st9_B (x y k w bs a b t u : List Sym) : st9 x y k w bs a b t u sB = b := rfl

@[simp] theorem st9_T (x y k w bs a b t u : List Sym) : st9 x y k w bs a b t u sT = t := rfl

@[simp] theorem st9_V (x y k w bs a b t u : List Sym) : st9 x y k w bs a b t u sV = u := rfl

theorem st9_eta (S : L54 → List Sym) :
    S = st9 (S sX) (S sY) (S sK) (S sW) (S sBs) (S sA) (S sB) (S sT) (S sV) := by
  funext l
  rcases l with ⟨_ | _ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

@[simp] theorem upd_X (x y k w bs a b t u z : List Sym) :
    Function.update (st9 x y k w bs a b t u) sX z = st9 z y k w bs a b t u := by
  funext l
  rcases l with ⟨_ | _ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

@[simp] theorem upd_Y (x y k w bs a b t u z : List Sym) :
    Function.update (st9 x y k w bs a b t u) sY z = st9 x z k w bs a b t u := by
  funext l
  rcases l with ⟨_ | _ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

@[simp] theorem upd_K (x y k w bs a b t u z : List Sym) :
    Function.update (st9 x y k w bs a b t u) sK z = st9 x y z w bs a b t u := by
  funext l
  rcases l with ⟨_ | _ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

@[simp] theorem upd_W (x y k w bs a b t u z : List Sym) :
    Function.update (st9 x y k w bs a b t u) sW z = st9 x y k z bs a b t u := by
  funext l
  rcases l with ⟨_ | _ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

@[simp] theorem upd_Bs (x y k w bs a b t u z : List Sym) :
    Function.update (st9 x y k w bs a b t u) sBs z = st9 x y k w z a b t u := by
  funext l
  rcases l with ⟨_ | _ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

@[simp] theorem upd_A (x y k w bs a b t u z : List Sym) :
    Function.update (st9 x y k w bs a b t u) sA z = st9 x y k w bs z b t u := by
  funext l
  rcases l with ⟨_ | _ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

@[simp] theorem upd_B (x y k w bs a b t u z : List Sym) :
    Function.update (st9 x y k w bs a b t u) sB z = st9 x y k w bs a z t u := by
  funext l
  rcases l with ⟨_ | _ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

@[simp] theorem upd_T (x y k w bs a b t u z : List Sym) :
    Function.update (st9 x y k w bs a b t u) sT z = st9 x y k w bs a b z u := by
  funext l
  rcases l with ⟨_ | _ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

@[simp] theorem upd_V (x y k w bs a b t u z : List Sym) :
    Function.update (st9 x y k w bs a b t u) sV z = st9 x y k w bs a b t z := by
  funext l
  rcases l with ⟨_ | _ | _ | _ | _ | i, hi⟩ | ⟨_ | _ | _ | _ | j, hj⟩
  all_goals first | rfl | exact absurd hi (by omega) | exact absurd hj (by omega)

#assert_std_axioms st9_eta upd_X upd_Y upd_K upd_W upd_Bs upd_A upd_B upd_T upd_V

end TMFw.W4o
