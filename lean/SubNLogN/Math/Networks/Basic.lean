import Mathlib
import SubNLogN.Spec

/-!
# Networks, part 1: index sets, roles, gates ([OAI26] §3)

Lean data for the two finite triple networks of [OAI26, §3] ([OAI26, §3.1]; Fact 3.4 (`fact:oai-networks`),
Appendix D.2, Proposition D.3 (`oai:networks`)): the set `𝒯` of 3-subsets of `[h]`, the data banks `X_a, Y_a` (`a ∈ 𝒯³`),
the three stages, the `v²` invocations per stage, their side wires `A_{ST}` and central wires
`C_i` (and `C_*` in the complex construction), and the gates of the eight-row schedule (2) ([OAI26, §3.1, (2)]).

Conventions (a fixed indexing choice for stages, invocations, and side wires):
* stage `j` varies coordinate `j` of `a`; the invocation index `ι` is the pair of the other two
  coordinates in increasing coordinate order;
* a side wire is indexed by an ordered neighbouring pair `(S, T)` with `S` the logical target
  triple and `T` the logical source triple of its invocation.
-/

namespace SubNLogN.Math.Networks

/-- The set `𝒯` of three-element subsets of `[h] = Fin h` ([OAI26, §3.1]). -/
abbrev Tri (h : ℕ) := {S : Finset (Fin h) // S.card = 3}

/-- A data index `a = (a₁, a₂, a₃) ∈ 𝒯³` ([OAI26, §3.1]). -/
abbrev Addr (h : ℕ) := Tri h × Tri h × Tri h

/-- The two constructions of [OAI26, §3]: the bit network (scalars in `𝔽₂`) and the complex
network (scalars in `ℤ[i, 1/2]`). -/
inductive Kind
  | bit
  | complex
  deriving DecidableEq, Repr

/-- The three stages; stage `j` varies coordinate `j` ([OAI26, §3.1]). -/
inductive Stage
  | one
  | two
  | three
  deriving DecidableEq, Repr

instance : Fintype Stage := ⟨{.one, .two, .three}, by intro x; cases x <;> simp⟩

/-- `|S ∩ T|`. -/
def inter {h : ℕ} (S T : Tri h) : ℕ := (S.1 ∩ T.1).card

/-- Neighbour rule ([OAI26, §3.1]): bit: `|S ∩ T| = 1`; complex: `S ≠ T` and `|S ∩ T|` even. -/
def Nbr {h : ℕ} : Kind → Tri h → Tri h → Prop
  | .bit, S, T => inter S T = 1
  | .complex, S, T => S ≠ T ∧ (inter S T = 0 ∨ inter S T = 2)

instance {h : ℕ} (κ : Kind) : DecidableRel (Nbr (h := h) κ) := fun S T => by
  cases κ <;> unfold Nbr <;> infer_instance

/-- Index of the extra central wire `C_*`: none in the bit network, one in the complex network. -/
def CStar : Kind → Type
  | .bit => Empty
  | .complex => Unit

instance (κ : Kind) : Fintype (CStar κ) := by cases κ <;> unfold CStar <;> infer_instance
instance (κ : Kind) : DecidableEq (CStar κ) := by cases κ <;> unfold CStar <;> infer_instance

/-- Central wires of one invocation: `C_i` (`inl i`, `i < h`) and, in the complex network, `C_*`
(`inr ()`). -/
abbrev Center (κ : Kind) (h : ℕ) := Fin h ⊕ CStar κ

/-- Side-wire index of one invocation: an ordered neighbouring pair `(S, T)`. -/
abbrev SideIdx (κ : Kind) (h : ℕ) := {p : Tri h × Tri h // Nbr κ p.1 p.2}

/-- Invocation index at a stage: the two fixed coordinates. -/
abbrev Fix (h : ℕ) := Tri h × Tri h

/-- Roles (= wires) of the network ([OAI26, §3.1]): the two banks, and per invocation `(j, ι)` its
own side and central scratch wires. -/
inductive Role (κ : Kind) (h : ℕ) where
  | X (a : Addr h)
  | Y (a : Addr h)
  | side (j : Stage) (ι : Fix h) (p : SideIdx κ h)
  | center (j : Stage) (ι : Fix h) (c : Center κ h)

/-- The role type as a sum of finite types (used for its `Fintype` structure). -/
def Role.equivSum (κ : Kind) (h : ℕ) :
    Role κ h ≃ (Addr h ⊕ Addr h) ⊕ ((Stage × Fix h × SideIdx κ h) ⊕ (Stage × Fix h × Center κ h)) where
  toFun
    | .X a => .inl (.inl a)
    | .Y a => .inl (.inr a)
    | .side j ι p => .inr (.inl (j, ι, p))
    | .center j ι c => .inr (.inr (j, ι, c))
  invFun
    | .inl (.inl a) => .X a
    | .inl (.inr a) => .Y a
    | .inr (.inl (j, ι, p)) => .side j ι p
    | .inr (.inr (j, ι, c)) => .center j ι c
  left_inv w := by cases w <;> rfl
  right_inv x := by rcases x with (a | a) | (⟨j, ι, p⟩ | ⟨j, ι, c⟩) <;> rfl

instance (κ : Kind) (h : ℕ) : Fintype (Role κ h) := Fintype.ofEquiv _ (Role.equivSum κ h).symm
noncomputable instance (κ : Kind) (h : ℕ) : DecidableEq (Role κ h) := Classical.decEq _

/-- Scratch (auxiliary) roles: all side and central wires. -/
def Role.IsScratch {κ : Kind} {h : ℕ} : Role κ h → Prop
  | .X _ => False
  | .Y _ => False
  | .side _ _ _ => True
  | .center _ _ _ => True

/-- The role permutation `ρ` of [OAI26, §§3.4–3.5, Props. 7–8]: exchange `X_a ↔ Y_a`, fix scratch. -/
def Role.rho {κ : Kind} {h : ℕ} : Role κ h → Role κ h
  | .X a => .Y a
  | .Y a => .X a
  | w => w

/-! ### Coordinates of an address at a stage -/

/-- The varying coordinate `a_j` of `a` at stage `j`. -/
def Addr.var {h : ℕ} : Stage → Addr h → Tri h
  | .one, a => a.1
  | .two, a => a.2.1
  | .three, a => a.2.2

/-- The invocation `ι` of stage `j` containing the data index `a` (its other two coordinates). -/
def Addr.fix {h : ℕ} : Stage → Addr h → Fix h
  | .one, a => (a.2.1, a.2.2)
  | .two, a => (a.1, a.2.2)
  | .three, a => (a.1, a.2.1)

/-- Reassemble an address from a stage, its invocation and the varying coordinate. -/
def Addr.mk {h : ℕ} : Stage → Fix h → Tri h → Addr h
  | .one, ι, S => (S, ι.1, ι.2)
  | .two, ι, S => (ι.1, S, ι.2)
  | .three, ι, S => (ι.1, ι.2, S)

/-! ### Gates and their time order -/

/-- Gates ([OAI26, §§3.1, 3.3, (2)]): at stage `j`, invocation `ι` and time `r`,
side times `0, 2, 5, 7` have one gate per bank triple `t`, centre times `1, 3, 4, 6` one gate on
the whole bank and all central wires. -/
inductive Gate (h : ℕ) where
  | side (j : Stage) (ι : Fix h) (r : Fin 8) (t : Tri h)
  | center (j : Stage) (ι : Fix h) (r : Fin 8)
  deriving DecidableEq

/-- Is stage `j` run with the inverse schedule and exchanged logical banks (stage 2, [OAI26, §3.1])? -/
def Stage.isInverse : Stage → Bool
  | .two => true
  | _ => false

/-- The gates touching a role, in time order (physical touch order `Y`-side, `Y`-centre,
`X`-side, `X`-centre, `Y`-centre, `Y`-side, `X`-centre, `X`-side at times `0, …, 7` of every
stage, [OAI26, §3.3]). A side wire `A_{ST}` meets the `Y`-side gates of its physical `Y` triple and
the `X`-side gates of its physical `X` triple; in stage 2 the logical banks are exchanged. -/
def touch {κ : Kind} {h : ℕ} : Role κ h → List (Gate h)
  | .X a => [Stage.one, .two, .three].flatMap fun j =>
      [.side j (a.fix j) 2 (a.var j), .center j (a.fix j) 3, .center j (a.fix j) 6,
        .side j (a.fix j) 7 (a.var j)]
  | .Y a => [Stage.one, .two, .three].flatMap fun j =>
      [.side j (a.fix j) 0 (a.var j), .center j (a.fix j) 1, .center j (a.fix j) 4,
        .side j (a.fix j) 5 (a.var j)]
  | .side j ι p =>
      let yb := if j.isInverse then p.1.2 else p.1.1
      let xb := if j.isInverse then p.1.1 else p.1.2
      [.side j ι 0 yb, .side j ι 2 xb, .side j ι 5 yb, .side j ι 7 xb]
  | .center j ι _ => [.center j ι 1, .center j ι 3, .center j ι 4, .center j ι 6]

/-- Vertices of a wire: its source, the gates touching it in time order, and its sink. -/
inductive Vertex (κ : Kind) (h : ℕ) where
  | source (w : Role κ h)
  | gate (g : Gate h)
  | sink (w : Role κ h)

/-- The vertex list of a role. -/
def vertices {κ : Kind} {h : ℕ} (w : Role κ h) : List (Vertex κ h) :=
  [.source w] ++ (touch w).map .gate ++ [.sink w]

/-- The edges of a role: consecutive pairs of its vertex list (tail, head). -/
def edges {κ : Kind} {h : ℕ} (w : Role κ h) : List (Vertex κ h × Vertex κ h) :=
  (vertices w).zip (vertices w).tail

/-! ### Counting contracts (stated as `Prop`s; proved in `Networks/Proofs/`) -/

/-- CONTRACT. `|𝒯| = v = C(h,3)` ([OAI26, §3.1]). Holds for every `h`. -/
def CardTriStmt : Prop := ∀ h : ℕ, Fintype.card (Tri h) = tripleV h

/-- CONTRACT. Neighbour counts ([OAI26, §3.1, (3)–(4)]): a triple has `z_b = 3·C(h-3,2)` bit neighbours and
`z_c = C(h-3,3) + 3(h-3)` complex neighbours. Holds for every `h`. -/
def CardNbrStmt : Prop := ∀ (h : ℕ) (S : Tri h),
    (Finset.univ.filter (fun T => Nbr .bit S T)).card = tripleZb h ∧
    (Finset.univ.filter (fun T => Nbr .complex S T)).card = tripleZc h

/-- CONTRACT. Wire counts (3)-(4) ([OAI26, §3.1, (3)–(4)]; Appendix D.2, Proposition D.3 (`oai:networks`)):
`W_b = 2N + I(v z_b + h)` and `W_c = 2N + I(v z_c + (h + 1))` roles. Holds for every `h`. -/
def CardRoleStmt : Prop := ∀ h : ℕ,
    Fintype.card (Role .bit h) = tripleWb h ∧ Fintype.card (Role .complex h) = tripleWc h

end SubNLogN.Math.Networks
