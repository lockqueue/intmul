import Mathlib

/-!
# Networks: abstract stream/array cost model (interface to be refined at the `FinTM2` machine level in `SubNLogN/Machine/`)

Conventions of Section 3.2 (`sec:prelim-model`), Appendix A (`app:parameter-transfer`), and Appendix D.1 (`sec:prelim-oai-model`), made explicit:

* An array lives on a complete rectangle of fields `[r₀] × ⋯ × [r_{n−1}]` stored in lexicographic
  order (field `0` most significant; addresses implicit), one record of `w` bits per address.
  Its logical volume is `V = (∏ rᵢ) · w` (`Layout.card L * w`).
* Primitive steps (Fact 3.3 (`fact:oai-streams`); Lemmas A.4–A.5 (`lem:transfer-streams`, `lem:transfer-long-record`))
  are charged `c · V` for the stream they act on, with one fixed constant `c` (depending only on the
  fixed radix bound `B`, the fixed networks and the fixed coefficients, never on field lengths or data):
  `Elem.pair` (fixed bijection of two fields of range `≤ B`), `Elem.shift` (cyclic shift of a target
  field by an offset depending only on earlier fields), `Elem.unit` (target field × fixed unit),
  `Step.recMap` (fixed streaming record map), `Step.addrMap` (address-dependent record map; long
  records, `lem:transfer-long-record`).
* A network node splits a row field cyclically into `W` role streams (charged `c · V`), runs node
  steps (`NStep`): primitives on one role stream (`c · V/W`), pointwise gates across aligned role
  streams (`c · (touched streams) · V/W`) and child calls on one role stream (charged by the child's
  own cost), and merges back (`c · V`).

Machine-level obligations (proved in `SubNLogN/Machine/`, not modelled here): offsets of `Elem.shift` and maps of `recMap`,
`addrMap`, `gate` are the explicit formulas used by the procedures (fixed rational linear
combinations, packed indicator sums, fixed-width dyadic arithmetic) and are computable within the
charged budget; descriptor/counter/head-return/cleanup work is `O(V)` per step.
-/

namespace SubNLogN.Math.Networks.Stream

/-- A rectangular layout: field ranges in physical order (field `0` most significant). -/
structure Layout where
  /-- number of fields -/
  n : ℕ
  /-- field ranges -/
  r : Fin n → ℕ

/-- Addresses of a layout. -/
abbrev Layout.Addr (L : Layout) : Type := (i : Fin L.n) → Fin (L.r i)

/-- Number of addresses `∏ rᵢ`. -/
def Layout.card (L : Layout) : ℕ := ∏ i, L.r i

/-- Elementary address bijections of Fact 3.3 (`fact:oai-streams`) and Lemma A.4 (`lem:transfer-streams`). -/
inductive Elem (L : Layout) (B : ℕ) where
  /-- a fixed bijection of the value pair of two small fields (`(1)-(3)`) -/
  | pair (i j : Fin L.n) (hij : i ≠ j) (hi : L.r i ≤ B) (hj : L.r j ≤ B)
      (g : Equiv.Perm (Fin (L.r i) × Fin (L.r j)))
  /-- controlled cyclic shift `x_t ← x_t + off(x) (mod r_t)`; `off` reads only fields before `t` -/
  | shift (t : Fin L.n) (off : L.Addr → ℕ)
      (hoff : ∀ x y : L.Addr, (∀ i, i < t → x i = y i) → off x = off y)
  /-- multiplication of field `t` by a unit `u` modulo `r_t`, `u'` its inverse -/
  | unit (t : Fin L.n) (u u' : ℕ) (huu' : (u * u') % L.r t = 1 % L.r t)

/-- The *pull* map of an elementary step: the array after the step is `A ∘ pull` (move convention
`(fA)(f x) = A x`, Section 3.2 (`sec:prelim-model`), Appendix D.1 (`sec:prelim-oai-model`)). -/
def Elem.pull {L : Layout} {B : ℕ} : Elem L B → L.Addr → L.Addr
  | .pair i j _ _ _ g, x =>
      let p := g.symm (x i, x j)
      Function.update (Function.update x i p.1) j p.2
  | .shift t off _, x =>
      Function.update x t ⟨((x t).val + L.r t - off x % L.r t) % L.r t, Nat.mod_lt _ (Fin.pos (x t))⟩
  | .unit t _ u' _, x =>
      Function.update x t ⟨(u' * (x t).val) % L.r t, Nat.mod_lt _ (Fin.pos (x t))⟩

/-- Steps on one stream with payload `β`. -/
inductive Step (L : Layout) (B : ℕ) (β : Type) where
  /-- an elementary address bijection -/
  | elem (e : Elem L B)
  /-- a fixed streaming record map -/
  | recMap (f : β → β)
  /-- an address-dependent record map (long records) -/
  | addrMap (f : L.Addr → β → β)

/-- Semantics of a step. -/
def Step.run {L : Layout} {B : ℕ} {β : Type} : Step L B β → (L.Addr → β) → (L.Addr → β)
  | .elem e, A => A ∘ e.pull
  | .recMap f, A => f ∘ A
  | .addrMap f, A => fun x => f x (A x)

/-- Straight-line programs on one stream. -/
abbrev Prog (L : Layout) (B : ℕ) (β : Type) := List (Step L B β)

/-- Semantics of a straight-line program (steps in list order). -/
def Prog.run {L : Layout} {B : ℕ} {β : Type} (p : Prog L B β) (A : L.Addr → β) : L.Addr → β :=
  p.foldl (fun A s => s.run A) A

/-- Cost of a straight-line program: `c · V` per step, `V = card · w`. -/
def Prog.cost {L : Layout} {B : ℕ} {β : Type} (c w : ℕ) (p : Prog L B β) : ℕ :=
  c * p.length * (L.card * w)

/-- Node steps on `W` aligned role streams of layout `L` (one network node). -/
inductive NStep (W : ℕ) (L : Layout) (B : ℕ) (β : Type) where
  /-- a primitive on one role stream -/
  | onRole (k : Fin W) (s : Step L B β)
  /-- a pointwise gate on aligned role streams (only the roles in `touched` may change) -/
  | gate (G : (Fin W → β) → (Fin W → β)) (touched : Finset (Fin W))
  /-- a child call on one role stream, with its semantics and its (already established) cost -/
  | call (k : Fin W) (child : (L.Addr → β) → (L.Addr → β)) (childCost : ℕ)

/-- Semantics of a node step on the family of role streams. -/
def NStep.run {W : ℕ} {L : Layout} {B : ℕ} {β : Type} :
    NStep W L B β → (Fin W → L.Addr → β) → (Fin W → L.Addr → β)
  | .onRole k s, A => Function.update A k (s.run (A k))
  | .gate G _, A => fun k x => G (fun k' => A k' x) k
  | .call k child _, A => Function.update A k (child (A k))

/-- Cost of a node step: `c · V/W` per primitive, `c · |touched| · V/W` per gate, child cost per call
(`V/W = card · w` is the role-stream volume). -/
def NStep.cost {W : ℕ} {L : Layout} {B : ℕ} {β : Type} (c w : ℕ) : NStep W L B β → ℕ
  | .onRole _ _ => c * (L.card * w)
  | .gate _ t => c * t.card * (L.card * w)
  | .call _ _ cc => cc

/-- A node program: role split, node steps, merge. -/
abbrev NProg (W : ℕ) (L : Layout) (B : ℕ) (β : Type) := List (NStep W L B β)

/-- Semantics of a node program on role streams. -/
def NProg.run {W : ℕ} {L : Layout} {B : ℕ} {β : Type} (p : NProg W L B β)
    (A : Fin W → L.Addr → β) : Fin W → L.Addr → β :=
  p.foldl (fun A s => s.run A) A

/-- Cost of a node program: split and merge `2 · c · V` (`V = W · card · w`) plus its steps. -/
def NProg.cost {W : ℕ} {L : Layout} {B : ℕ} {β : Type} (c w : ℕ) (p : NProg W L B β) : ℕ :=
  2 * c * (W * (L.card * w)) + (p.map (NStep.cost c w)).sum

/-- Number of child calls of a node program. -/
def NProg.calls {W : ℕ} {L : Layout} {B : ℕ} {β : Type} (p : NProg W L B β) : ℕ :=
  (p.filter fun s => match s with | .call _ _ _ => true | _ => false).length

end SubNLogN.Math.Networks.Stream
