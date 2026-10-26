import Contracts.Machine.W4

/-!
# WP.W4.Pure — perfect unshuffle and riffle on lists

* `unsh l = dealE l ++ dealO l`: entries at even positions, then entries at odd positions;
* `riff l = inter (take h l) (drop h l)`, `h = |l| / 2`: interleave the two halves.

Index behaviour in `getElem?` form (no side conditions), lengths, and permutation facts.
-/

namespace TMFw.W4

/-- Entries at even positions. -/
def dealE {α : Type} : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: l => x :: dealE l

/-- Entries at odd positions. -/
def dealO {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | _ :: y :: l => y :: dealO l

/-- Perfect unshuffle. -/
def unsh {α : Type} (l : List α) : List α := dealE l ++ dealO l

/-- Interleave two lists (stops at the shorter one). -/
def inter {α : Type} : List α → List α → List α
  | x :: xs, y :: ys => x :: y :: inter xs ys
  | _, _ => []

/-- Perfect riffle (out-shuffle): interleave the first and the second half. -/
def riff {α : Type} (l : List α) : List α := inter (l.take (l.length / 2)) (l.drop (l.length / 2))

variable {α : Type}

@[simp] theorem dealE_nil : dealE ([] : List α) = [] := rfl
@[simp] theorem dealE_single (x : α) : dealE [x] = [x] := rfl
@[simp] theorem dealE_cons_cons (x y : α) (l : List α) : dealE (x :: y :: l) = x :: dealE l := rfl
@[simp] theorem dealO_nil : dealO ([] : List α) = [] := rfl
@[simp] theorem dealO_single (x : α) : dealO [x] = [] := rfl
@[simp] theorem dealO_cons_cons (x y : α) (l : List α) : dealO (x :: y :: l) = y :: dealO l := rfl
@[simp] theorem inter_cons_cons (x y : α) (xs ys : List α) :
    inter (x :: xs) (y :: ys) = x :: y :: inter xs ys := rfl
@[simp] theorem inter_nil_left (ys : List α) : inter [] ys = [] := rfl
@[simp] theorem inter_nil_right (xs : List α) : inter xs [] = [] := by cases xs <;> rfl

/-! ## Lengths -/

theorem length_dealE : ∀ l : List α, (dealE l).length = (l.length + 1) / 2
  | [] => by simp
  | [_] => by simp
  | _ :: _ :: l => by
    simp only [dealE_cons_cons, List.length_cons, length_dealE l]
    omega

theorem length_dealO : ∀ l : List α, (dealO l).length = l.length / 2
  | [] => by simp
  | [_] => by simp
  | _ :: _ :: l => by
    simp only [dealO_cons_cons, List.length_cons, length_dealO l]
    omega

theorem length_unsh (l : List α) : (unsh l).length = l.length := by
  simp only [unsh, List.length_append, length_dealE, length_dealO]
  omega

theorem length_inter : ∀ (A B : List α), A.length = B.length → (inter A B).length = 2 * A.length
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | _ :: A, _ :: B, h => by
    simp only [inter_cons_cons, List.length_cons] at h ⊢
    rw [length_inter A B (by omega)]
    omega

theorem length_take_half (l : List α) (h : l.length % 2 = 0) :
    (l.take (l.length / 2)).length = l.length / 2 := by
  simp only [List.length_take]
  omega

theorem length_drop_half (l : List α) (h : l.length % 2 = 0) :
    (l.drop (l.length / 2)).length = l.length / 2 := by
  simp only [List.length_drop]
  omega

theorem length_riff (l : List α) (h : l.length % 2 = 0) : (riff l).length = l.length := by
  unfold riff
  rw [length_inter _ _ (by rw [length_take_half l h, length_drop_half l h]), length_take_half l h]
  omega

/-! ## Index behaviour -/

theorem getElem?_dealE : ∀ (l : List α) (m : ℕ), (dealE l)[m]? = l[2 * m]?
  | [], m => by simp
  | [_], 0 => by simp
  | [_], m + 1 => by
    rw [List.getElem?_eq_none (by simp), List.getElem?_eq_none (by simp; omega)]
  | _ :: _ :: l, 0 => by simp
  | _ :: _ :: l, m + 1 => by
    rw [dealE_cons_cons, List.getElem?_cons_succ, getElem?_dealE l m,
      show 2 * (m + 1) = 2 * m + 1 + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_cons_succ]

theorem getElem?_dealO : ∀ (l : List α) (m : ℕ), (dealO l)[m]? = l[2 * m + 1]?
  | [], m => by simp
  | [_], m => by
    rw [dealO_single, List.getElem?_nil, List.getElem?_eq_none (by simp)]
  | _ :: _ :: l, 0 => by simp
  | _ :: _ :: l, m + 1 => by
    rw [dealO_cons_cons, List.getElem?_cons_succ, getElem?_dealO l m,
      show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_cons_succ]

theorem getElem?_inter_even : ∀ (A B : List α), A.length = B.length →
    ∀ m, (inter A B)[2 * m]? = A[m]?
  | [], [], _, m => by simp
  | _ :: A, _ :: B, _, 0 => by simp
  | _ :: A, _ :: B, h, m + 1 => by
    rw [inter_cons_cons, show 2 * (m + 1) = 2 * m + 1 + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_cons_succ, getElem?_inter_even A B (by simpa using h) m,
      List.getElem?_cons_succ]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

theorem getElem?_inter_odd : ∀ (A B : List α), A.length = B.length →
    ∀ m, (inter A B)[2 * m + 1]? = B[m]?
  | [], [], _, m => by simp
  | _ :: A, _ :: B, _, 0 => by simp
  | _ :: A, _ :: B, h, m + 1 => by
    rw [inter_cons_cons, show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_cons_succ, getElem?_inter_odd A B (by simpa using h) m,
      List.getElem?_cons_succ]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

/-- `unsh`, low half: `(unsh l)[q] = l[2q]` for `q < ⌈|l|/2⌉`. -/
theorem getElem?_unsh_lo (l : List α) (q : ℕ) (hq : q < (l.length + 1) / 2) :
    (unsh l)[q]? = l[2 * q]? := by
  unfold unsh
  rw [List.getElem?_append_left (by rw [length_dealE]; exact hq), getElem?_dealE]

/-- `unsh`, high half: `(unsh l)[⌈|l|/2⌉ + q] = l[2q + 1]`. -/
theorem getElem?_unsh_hi (l : List α) (q : ℕ) :
    (unsh l)[(l.length + 1) / 2 + q]? = l[2 * q + 1]? := by
  unfold unsh
  rw [List.getElem?_append_right (by rw [length_dealE]; omega), length_dealE,
    show (l.length + 1) / 2 + q - (l.length + 1) / 2 = q by omega, getElem?_dealO]

/-- `riff`, even positions: the first half. -/
theorem getElem?_riff_even (l : List α) (h : l.length % 2 = 0) (m : ℕ) (hm : m < l.length / 2) :
    (riff l)[2 * m]? = l[m]? := by
  unfold riff
  rw [getElem?_inter_even _ _ (by rw [length_take_half l h, length_drop_half l h]),
    List.getElem?_take_of_lt hm]

/-- `riff`, odd positions: the second half. -/
theorem getElem?_riff_odd (l : List α) (h : l.length % 2 = 0) (m : ℕ) :
    (riff l)[2 * m + 1]? = l[l.length / 2 + m]? := by
  unfold riff
  rw [getElem?_inter_odd _ _ (by rw [length_take_half l h, length_drop_half l h]),
    List.getElem?_drop]

/-! ## Permutations -/

theorem perm_unsh : ∀ l : List α, (unsh l).Perm l
  | [] => List.Perm.nil
  | [_] => List.Perm.refl _
  | x :: y :: l => by
    have ih := perm_unsh l
    unfold unsh at ih ⊢
    rw [dealE_cons_cons, dealO_cons_cons, List.cons_append]
    exact List.Perm.cons x (List.perm_middle.trans (List.Perm.cons y ih))

theorem perm_inter : ∀ (A B : List α), A.length = B.length → (inter A B).Perm (A ++ B)
  | [], [], _ => List.Perm.nil
  | x :: A, y :: B, h => by
    rw [inter_cons_cons, List.cons_append]
    exact List.Perm.cons x ((List.Perm.cons y (perm_inter A B (by simpa using h))).trans
      List.perm_middle.symm)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem perm_riff (l : List α) (h : l.length % 2 = 0) : (riff l).Perm l := by
  unfold riff
  have := perm_inter (l.take (l.length / 2)) (l.drop (l.length / 2))
    (by rw [length_take_half l h, length_drop_half l h])
  rwa [List.take_append_drop] at this

theorem length_flatten_of_perm {l₁ l₂ : List (List α)} (h : l₁.Perm l₂) :
    l₁.flatten.length = l₂.flatten.length := h.flatten.length_eq

#assert_std_axioms length_dealE length_dealO length_unsh length_inter length_riff getElem?_dealE
  getElem?_dealO getElem?_inter_even getElem?_inter_odd getElem?_unsh_lo getElem?_unsh_hi
  getElem?_riff_even getElem?_riff_odd perm_unsh perm_inter perm_riff length_flatten_of_perm

end TMFw.W4
