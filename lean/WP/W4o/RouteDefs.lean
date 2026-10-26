import Contracts.Machine.W4
import WP.W4o.AddT

/-!
# WP.W4o.RouteDefs — the list combinators of the router (pure)

* `sel β v`: the elements of `v` at positions `≡ β (mod 2)` (`sel false` = even positions);
* `inter l m`: interleave `[a0, b0, a1, b1, …]`;
* `rt W n B v`: the machine router's recursion (offset block `B`, multiplier bits `W`);
  `WP.W4o.RouteMath` proves `rt (encodeNat w) n B v = oddRouteL n w (bitsVal B) v`.
-/

namespace TMFw.W4o

open TMFw TMFw.Contracts Computability

/-- Elements at positions `≡ β (mod 2)`: `sel false` = even positions, `sel true` = odd ones. -/
def sel {α : Type} : Bool → List α → List α
  | _, [] => []
  | false, a :: l => a :: sel true l
  | true, _ :: l => sel false l

/-- Interleave `[a0, a1, …] [b0, b1, …] ↦ [a0, b0, a1, b1, …]` (leftovers appended). -/
def inter {α : Type} : List α → List α → List α
  | a :: l, b :: m => a :: b :: inter l m
  | [], m => m
  | l, [] => l

/-- The machine router's recursion, driven by the `n`-bit offset block `B` (LSB first):
even outputs come from input parity `B.head`, with offset block `B.tail`; odd outputs from the
other parity, with offset block `(B + W mod 2^n).tail`. -/
def rt {α : Type} (W : List Bool) : ℕ → List Bool → List α → List α
  | 0, _, v => v
  | n + 1, B, v =>
    inter (rt W n B.tail (sel (B.headD false) v))
      (rt W n (addT false B W false).tail (sel (!B.headD false) v))

theorem inter_nil_right {α : Type} (l : List α) : inter l [] = l := by
  cases l <;> rfl

theorem inter_append_pair {α : Type} (a b : α) :
    ∀ (l m : List α), l.length = m.length → inter (l ++ [a]) (m ++ [b]) = inter l m ++ [a, b]
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: l, y :: m, h => by
    show x :: y :: inter (l ++ [a]) (m ++ [b]) = x :: y :: inter l m ++ [a, b]
    rw [inter_append_pair a b l m (by simpa using h)]
    rfl

/-- Interleaving reversed lists, reversed, swaps the roles. -/
theorem inter_rev {α : Type} :
    ∀ (l m : List α), l.length = m.length → (inter l.reverse m.reverse).reverse = inter m l
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: m, h => by
    have hl : l.length = m.length := by simpa using h
    rw [List.reverse_cons, List.reverse_cons,
      inter_append_pair a b l.reverse m.reverse (by simpa using hl), List.reverse_append,
      inter_rev l m hl]
    rfl

theorem sel_cons_cons {α : Type} (a b : α) (l : List α) :
    sel false (a :: b :: l) = a :: sel false l ∧ sel true (a :: b :: l) = b :: sel true l :=
  ⟨rfl, rfl⟩

#assert_std_axioms inter_nil_right inter_append_pair inter_rev sel_cons_cons

end TMFw.W4o
