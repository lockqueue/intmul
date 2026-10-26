import SubNLogN.Math.Networks.Basic

/-!
# Networks: the actual gates

`Gate h` (Basic.lean) also contains constructors that are not gates of the circuit (e.g. a side gate
at time 1). The actual gates of the eight-row schedule are the side gates at times `0, 2, 5, 7` and
the centre gates at times `1, 3, 4, 6` ([OAI26, §§3.1, 3.3, (2)]). Every gate that touches a role (its
`touch` list, hence every gate vertex on an edge) is actual (`touch_valid`); circuit counts and
executions range over `ActualGate h` only.
-/

namespace SubNLogN.Math.Networks

/-- A gate of the circuit: side gates at times `0, 2, 5, 7`, centre gates at times `1, 3, 4, 6`. -/
def Gate.Valid {h : ℕ} : Gate h → Prop
  | .side _ _ r _ => r = 0 ∨ r = 2 ∨ r = 5 ∨ r = 7
  | .center _ _ r => r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 6

/-- The actual gates of the circuit. -/
abbrev ActualGate (h : ℕ) := {g : Gate h // g.Valid}

/-- Every gate touching a role is an actual gate of the circuit. -/
theorem touch_valid {κ : Kind} {h : ℕ} (w : Role κ h) (g : Gate h) (hg : g ∈ touch w) :
    g.Valid := by
  cases w with
  | X a =>
    simp only [touch, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hg
    obtain ⟨j, _, hj⟩ := hg
    rcases hj with rfl | rfl | rfl | rfl <;> simp [Gate.Valid]
  | Y a =>
    simp only [touch, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hg
    obtain ⟨j, _, hj⟩ := hg
    rcases hj with rfl | rfl | rfl | rfl <;> simp [Gate.Valid]
  | side j ι p =>
    simp only [touch, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp [Gate.Valid]
  | center j ι c =>
    simp only [touch, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp [Gate.Valid]

end SubNLogN.Math.Networks
