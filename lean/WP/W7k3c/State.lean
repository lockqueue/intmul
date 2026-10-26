import WP.W7k3c.Base

/-!
# WP.W7k3c.State — abstract kernel states

The kernel keeps at most one value on each of its sixteen scratch stacks, above a `mark` floor
(so every value is `TermOK`-terminated). `St S V dv` is the host state with named stacks as in `S`,
destination content `dv`, and scratch stack `j` holding `V j`. Every machine step is then an update of
`V` (`St_set`) or of `dv` (`St_setd`). The marks are pushed first (`HT.pushMarks`) and popped last
(`HT.popMarks`).
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

/-- A value held on a scratch stack. -/
inductive Val
  | nat (a : ℕ)
  | int (z : ℤ)

/-- Encoding of a value. -/
def Val.enc : Val → List Sym
  | .nat a => natSyms a
  | .int z => intSyms z

/-- Encoding of an optional value (`none` is the empty stack above the floor). -/
def encO : Option Val → List Sym
  | none => []
  | some v => v.enc

@[simp] theorem encO_none : encO none = [] := rfl
@[simp] theorem encO_nat (a : ℕ) : encO (some (.nat a)) = natSyms a := rfl
@[simp] theorem encO_int (z : ℤ) : encO (some (.int z)) = intSyms z := rfl

/-- The kernel state. -/
def St (S : HL → List Sym) (V : Fin 16 → Option Val) (dv : List Sym) : HL → List Sym
  | .inl i => if i = 4 then dv else S (.inl i)
  | .inr j => encO (V j) ++ Sym.mark :: S (.inr j)

section St

variable (S : HL → List Sym) (V : Fin 16 → Option Val) (dv : List Sym)

@[simp] theorem St_scr (j : Fin 16) : St S V dv (.inr j) = encO (V j) ++ Sym.mark :: S (.inr j) :=
  rfl

@[simp] theorem St_dst : St S V dv (.inl 4) = dv := rfl

theorem St_in (i : Fin 5) (hi : i ≠ 4) : St S V dv (.inl i) = S (.inl i) := by
  simp [St, hi]

@[simp] theorem St_in0 : St S V dv (.inl 0) = S (.inl 0) := rfl
@[simp] theorem St_in1 : St S V dv (.inl 1) = S (.inl 1) := rfl
@[simp] theorem St_in2 : St S V dv (.inl 2) = S (.inl 2) := rfl
@[simp] theorem St_in3 : St S V dv (.inl 3) = S (.inl 3) := rfl

theorem St_set (j : Fin 16) (o : Option Val) :
    Function.update (St S V dv) (.inr j) (encO o ++ Sym.mark :: S (.inr j)) =
      St S (Function.update V j o) dv := by
  funext x
  rcases x with i | k
  · rw [Function.update_of_ne (by simp)]
    rfl
  · by_cases h : k = j
    · subst h
      simp
    · rw [Function.update_of_ne (by simpa using h)]
      simp [Function.update_of_ne h]

theorem St_setd (w : List Sym) : Function.update (St S V dv) (.inl 4) w = St S V w := by
  funext x
  rcases x with i | k
  · by_cases h : i = 4
    · subst h
      simp
    · rw [Function.update_of_ne (by simpa using h)]
      simp [St, h]
  · rw [Function.update_of_ne (by simp)]
    rfl

/-- The final state with every scratch stack empty is `S` with the new destination content. -/
theorem St_empty_eq (w : List Sym) :
    (fun x => match x with
      | .inl i => St S (fun _ => none) w (.inl i)
      | .inr j => S (.inr j)) = Function.update S (.inl 4) w := by
  funext x
  rcases x with i | k
  · by_cases h : i = 4
    · subst h
      simp
    · simp [St, h, Function.update_of_ne (show (Sum.inl i : HL) ≠ .inl 4 by simpa using h)]
  · simp [Function.update_of_ne (show (Sum.inr k : HL) ≠ .inl 4 by simp)]

end St

/-! ## Floors -/

variable {I : CI}

/-- Push a `mark` on each listed scratch stack. -/
def pushMarks : List (Fin 16) → CP I
  | [] => .load id
  | j :: l => (pushS (.inr j) .mark).seq (pushMarks l)

/-- Pop the top symbol of each listed scratch stack. -/
def popMarks : List (Fin 16) → CP I
  | [] => .load id
  | j :: l => (popS (.inr j)).seq (popMarks l)

theorem pushMarks_closed : ∀ l : List (Fin 16), (pushMarks (I := I) l).Closed
  | [] => trivial
  | _ :: l => ⟨trivial, pushMarks_closed l⟩

theorem popMarks_closed : ∀ l : List (Fin 16), (popMarks (I := I) l).Closed
  | [] => trivial
  | _ :: l => ⟨trivial, popMarks_closed l⟩

theorem HT.load_id (B : HL → List Sym) : HT (σ := I.R) [] B (.load id) B 1 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  exact ⟨⟨v, S⟩, 1, Eval.load [] id v S, rfl, le_rfl⟩

/-- Marks on the listed scratch stacks. -/
def withMarks (B : HL → List Sym) (l : List (Fin 16)) : HL → List Sym
  | .inl i => B (.inl i)
  | .inr j => if j ∈ l then Sym.mark :: B (.inr j) else B (.inr j)

theorem HT.pushMarks : ∀ (l : List (Fin 16)) (B : HL → List Sym), l.Nodup →
    HT (σ := I.R) [] B (pushMarks l) (withMarks B l) (l.length + 1)
  | [], B, _ => by
    refine (HT.load_id B).of_eq ?_ le_rfl
    funext x
    rcases x with i | k <;> simp [withMarks]
  | j :: l, B, hnd => by
    have hj : j ∉ l := (List.nodup_cons.mp hnd).1
    refine (HT.seq (HT.pushS (.inr j) .mark B []) (HT.pushMarks l _ (List.nodup_cons.mp hnd).2)).of_eq
      ?_ (by simp only [List.length_cons]; omega)
    funext x
    rcases x with i | k
    · simp [withMarks]
    · by_cases h : k = j
      · subst h
        simp [withMarks, hj]
      · simp [withMarks, h, Function.update_of_ne (show (Sum.inr k : HL) ≠ .inr j by simpa using h)]

/-- Marks removed from the listed scratch stacks. -/
theorem HT.popMarks : ∀ (l : List (Fin 16)) (B : HL → List Sym), l.Nodup →
    HT (σ := I.R) [] (withMarks B l) (popMarks l) B (l.length + 1)
  | [], B, _ => by
    refine (HT.load_id _).of_eq ?_ le_rfl
    funext x
    rcases x with i | k <;> simp [withMarks]
  | j :: l, B, hnd => by
    have hj : j ∉ l := (List.nodup_cons.mp hnd).1
    have heq : Function.update (withMarks B (j :: l)) (.inr j) (B (.inr j)) = withMarks B l := by
      funext x
      rcases x with i | k
      · simp [withMarks]
      · by_cases h : k = j
        · subst h
          simp [withMarks, hj]
        · simp [withMarks, h, Function.update_of_ne (show (Sum.inr k : HL) ≠ .inr j by simpa using h)]
    have h1 := HT.popS (σ := I.R) (.inr j) (withMarks B (j :: l)) Sym.mark (B (.inr j))
      (by simp [withMarks]) []
    rw [heq] at h1
    exact (HT.seq h1 (HT.popMarks l B (List.nodup_cons.mp hnd).2)).mono
      (by simp only [List.length_cons]; omega)

#assert_std_axioms St_in St_set St_setd St_empty_eq pushMarks_closed popMarks_closed HT.load_id
  HT.pushMarks HT.popMarks

end WP.W7k3c
