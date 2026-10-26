import Mathlib

/-!
# Networks: abstract stream/array cost model, v2 (`AppCModel`; refined at the `FinTM2` machine level in `SubNLogN/Machine/`)

(`StreamModel.lean` is the frozen v1, imported by `AppCShear.lean`; this file supersedes it for the
Appendix A procedures and uses the separate namespace `SubNLogN.Math.Networks.Model`.)

(`AppC` in filenames is a historical prefix retained for stability, corresponding to Appendix A (`app:parameter-transfer`).)
Conventions of Section 3.2 (`sec:prelim-model`), Appendix A, and Appendix D.1 (`sec:prelim-oai-model`), made explicit:

* An array lives on a complete rectangle of fields `[r₀] × ⋯ × [r_{n−1}]` in lexicographic order
  (field `0` most significant, addresses implicit), one record of type `β` per address; with a declared
  record width `w` bits the logical volume is `V = (∏ rᵢ) · w`.
* A *block* `[t₀, t₁)` of consecutive fields is read as one mixed-radix number (a big field of range
  `∏ rⱼ`, e.g. `b` radix-`q` digits).
* *Row classes* model role streams: the class `(row, μ, res)` is the set of addresses whose `row`
  field is `≡ res (mod μ)`; a network node with `W` roles in class `c` runs role `k` in the class
  `(row, μW, res + μk)`. Volume of a class: `V/μ`.
* **Nominal costs.** `*.cost` is a nominal model cost; no theorem here bounds TM2 time (all machine
  step bounds are proved in `SubNLogN/Machine/`; the contracts here on Appendix A procedures are functional:
  `…CorrectStmt`, `…WFStmt`). Nominally, primitives (`Elem`, `Step`) each cost
  `c₀ · (volume of the class they act in)`, with one fixed `c₀` (depending only on the fixed radix
  bound, networks and coefficients); `swapBlocks` (an interchange of two equal blocks, used by the
  *outer* procedures and realized by Lemma A.8 (`lem:transfer12`)) costs `swapCost len · volume` (a parameter; nothing about it
  is proved here); `sparsePerm` (Lemma A.9 (`lem:transfer13`) repair) costs `c₀ (vol + |supp| A (w + A))` with `A = ⌈lg 2V⌉`.
* Procedures are depth-indexed (`ProcK d`): depth `0` straight-line, depth `d+1` lists of class
  primitives and *nodes* (role split, role primitives, gates, child calls of depth `d`, role relabels,
  merge). `run` and the nominal `cost` are defined by recursion on `d`.

Machine-level obligations (proved in `SubNLogN/Machine/`, not modelled here): every `off`, `recMap`, `addrMap`, gate map used is an
explicit formula from a fixed finite family computable within the charged budget; parking of role
streams, descriptors, counters, head returns and cleanup cost `O(V)` per node.
-/

namespace SubNLogN.Math.Networks.Model

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

/-! ## Blocks of fields -/

/-- Is field `j` in the block `[t₀, t₁)`? -/
def inBlock (t₀ t₁ : ℕ) {n : ℕ} (j : Fin n) : Prop := t₀ ≤ j.val ∧ j.val < t₁

instance (t₀ t₁ : ℕ) {n : ℕ} : DecidablePred (inBlock t₀ t₁ (n := n)) := fun j => by
  unfold inBlock; infer_instance

/-- Place value of field `j` in a block ending at `t₁`: the product of the ranges of the later block
fields. -/
def Layout.place (L : Layout) (t₁ : ℕ) (j : Fin L.n) : ℕ :=
  ∏ j' ∈ Finset.univ.filter (fun j' : Fin L.n => j < j' ∧ j'.val < t₁), L.r j'

/-- Range `∏_{t₀ ≤ j < t₁} r_j` of a block. -/
def Layout.blockRange (L : Layout) (t₀ t₁ : ℕ) : ℕ :=
  ∏ j ∈ Finset.univ.filter (inBlock t₀ t₁ (n := L.n)), L.r j

/-- Mixed-radix value of a block (first field most significant). -/
def Layout.blockVal (L : Layout) (t₀ t₁ : ℕ) (x : L.Addr) : ℕ :=
  ∑ j ∈ Finset.univ.filter (inBlock t₀ t₁ (n := L.n)), (x j).val * L.place t₁ j

/-- Overwrite a block with the mixed-radix digits of `v` (taken modulo the block range). -/
def Layout.blockSet (L : Layout) (t₀ t₁ : ℕ) (x : L.Addr) (v : ℕ) : L.Addr := fun j =>
  if inBlock t₀ t₁ j then ⟨(v / L.place t₁ j) % L.r j, Nat.mod_lt _ (Fin.pos (x j))⟩ else x j

/-! ## Elementary steps -/

/-- Elementary address bijections of Fact 3.3 (`fact:oai-streams`) and Lemma A.4 (`lem:transfer-streams`), each `O(V)`.
Side conditions (small fields, controls before the target block, invertible units) are collected in
`Elem.WF`, so that procedures are plain data. -/
inductive Elem (L : Layout) where
  /-- a fixed bijection of the value pair of two small fields (`(1)-(3)`) -/
  | pair (i j : Fin L.n) (g : Equiv.Perm (Fin (L.r i) × Fin (L.r j)))
  /-- controlled cyclic shift of the block `[t₀, t₁)` by `off(x)` (modulo its range) -/
  | shift (t₀ t₁ : ℕ) (off : L.Addr → ℕ)
  /-- multiplication of the block `[t₀, t₁)` by `u` modulo its range (`u'` the inverse) -/
  | unit (t₀ t₁ : ℕ) (u u' : ℕ)

/-- Well-formedness of an elementary step (radix bound `B`): two distinct small fields; a shift
whose offset reads only fields before its target block; a unit with inverse `u'`. -/
def Elem.WF {L : Layout} (B : ℕ) : Elem L → Prop
  | .pair i j _ => i ≠ j ∧ L.r i ≤ B ∧ L.r j ≤ B
  | .shift t₀ t₁ off => t₀ ≤ t₁ ∧ t₁ ≤ L.n ∧
      ∀ x y : L.Addr, (∀ i : Fin L.n, i.val < t₀ → x i = y i) → off x = off y
  | .unit t₀ t₁ u u' => t₀ ≤ t₁ ∧ t₁ ≤ L.n ∧
      (u * u') % L.blockRange t₀ t₁ = 1 % L.blockRange t₀ t₁

/-- The *pull* map of an elementary step: the array after the step is `A ∘ pull` (move convention
`(fA)(f x) = A x`, Section 3.2 (`sec:prelim-model`), Appendix D.1 (`sec:prelim-oai-model`)). -/
def Elem.pull {L : Layout} : Elem L → L.Addr → L.Addr
  | .pair i j g, x =>
      let p := g.symm (x i, x j)
      Function.update (Function.update x i p.1) j p.2
  | .shift t₀ t₁ off, x =>
      let R := L.blockRange t₀ t₁
      L.blockSet t₀ t₁ x ((L.blockVal t₀ t₁ x + R - off x % R) % R)
  | .unit t₀ t₁ _ u', x =>
      L.blockSet t₀ t₁ x ((u' * L.blockVal t₀ t₁ x) % L.blockRange t₀ t₁)

/-- Steps on one stream (or one row class) with payload `β`. -/
inductive Step (L : Layout) (β : Type) where
  /-- an elementary address bijection -/
  | elem (e : Elem L)
  /-- a fixed streaming record map -/
  | recMap (f : β → β)
  /-- an address-dependent record map (long records, `lem:transfer-long-record`) -/
  | addrMap (f : L.Addr → β → β)
  /-- a permutation of addresses supported on `supp`, given by its pull map (Lemma A.9 (`lem:transfer13`) repair by stable
  radix sorting); bijectivity and support are side conditions (`Step.WF`) -/
  | sparsePerm (pull : L.Addr → L.Addr) (supp : Finset L.Addr)
  /-- interchange of the equal-range blocks `[t₀, t₀+len)` and `[s₀, s₀+len)` (outer procedures only;
  realized by Lemma A.8 (`lem:transfer12`) at the machine level; disjointness, range and equal block ranges are `Step.WF`) -/
  | swapBlocks (t₀ s₀ len : ℕ)
  /-- a fixed pointwise map on the `r_i` aligned sub-streams obtained by splitting on the small field
  `i` (`lem:transfer-streams` (3)); e.g. an individual butterfly kernel on a selected bit -/
  | digitGate (i : Fin L.n) (G : (Fin (L.r i) → β) → (Fin (L.r i) → β))

/-- Semantics of a step. -/
def Step.run {L : Layout} {β : Type} : Step L β → (L.Addr → β) → (L.Addr → β)
  | .elem e, A => A ∘ e.pull
  | .recMap f, A => f ∘ A
  | .addrMap f, A => fun x => f x (A x)
  | .sparsePerm pull _, A => A ∘ pull
  | .swapBlocks t₀ s₀ len, A => fun x =>
      A (L.blockSet s₀ (s₀ + len) (L.blockSet t₀ (t₀ + len) x (L.blockVal s₀ (s₀ + len) x))
        (L.blockVal t₀ (t₀ + len) x))
  | .digitGate i G, A => fun x => G (fun v => A (Function.update x i v)) (x i)

/-! ## Row classes -/

/-- A row class: addresses whose field `row` is `≡ res (mod μ)` (a role stream). -/
structure RowClass (L : Layout) where
  /-- the row field -/
  row : Fin L.n
  /-- modulus -/
  μ : ℕ
  /-- residue -/
  res : ℕ
  hμ : 0 < μ
  hres : res < μ

/-- Membership in a row class. -/
def RowClass.mem {L : Layout} (c : RowClass L) (x : L.Addr) : Prop := (x c.row).val % c.μ = c.res

instance {L : Layout} (c : RowClass L) : DecidablePred c.mem := fun x => by
  unfold RowClass.mem; infer_instance

/-- The whole array as a class. -/
def RowClass.top {L : Layout} (row : Fin L.n) : RowClass L := ⟨row, 1, 0, Nat.one_pos, Nat.one_pos⟩

/-- Role `k` of a node with `W` roles in class `c`. -/
def RowClass.sub {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W) : RowClass L where
  row := c.row
  μ := c.μ * W
  res := c.res + c.μ * k
  hμ := Nat.mul_pos c.hμ hW
  hres := by
    have h1 := c.hres
    have h2 := k.isLt
    calc c.res + c.μ * k < c.μ + c.μ * k := by omega
      _ = c.μ * (k + 1) := by ring
      _ ≤ c.μ * W := Nat.mul_le_mul_left _ (by omega)

/-- Replace the row value of an address (unchanged if out of range). -/
def withRow {L : Layout} (row : Fin L.n) (x : L.Addr) (v : ℕ) : L.Addr :=
  if h : v < L.r row then Function.update x row ⟨v, h⟩ else x

/-- Role index of `x` at a node with `W` roles in class `c`. -/
def roleIdx {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (x : L.Addr) : Fin W :=
  ⟨((x c.row).val / c.μ) % W, Nat.mod_lt _ hW⟩

/-- Position of `x` inside its role stream. -/
def rolePos {L : Layout} (c : RowClass L) (W : ℕ) (x : L.Addr) : ℕ := ((x c.row).val / c.μ) / W

/-- The address aligned with `x` in role `k'` (same position, same other fields). -/
def aligned {L : Layout} (c : RowClass L) (W : ℕ) (x : L.Addr) (k' : ℕ) : L.Addr :=
  withRow c.row x (c.res + c.μ * (k' + W * rolePos c W x))

/-- Run a step inside a class (addresses outside are unchanged). -/
def Step.runIn {L : Layout} {β : Type} (c : RowClass L) (s : Step L β)
    (A : L.Addr → β) : L.Addr → β :=
  fun x => if c.mem x then s.run A x else A x

/-- A pointwise gate on the aligned role streams of a node. -/
def gateRun {L : Layout} {β : Type} (c : RowClass L) (W : ℕ) (hW : 0 < W)
    (G : (Fin W → β) → (Fin W → β)) (A : L.Addr → β) : L.Addr → β := fun x =>
  if c.mem x then G (fun k' => A (aligned c W x k')) (roleIdx c W hW x) else A x

/-- A relabelling of role streams: role `k` receives the stream of role `π⁻¹ k`. -/
def relabelRun {L : Layout} {β : Type} (c : RowClass L) (W : ℕ) (hW : 0 < W)
    (π : Equiv.Perm (Fin W)) (A : L.Addr → β) : L.Addr → β := fun x =>
  if c.mem x then A (aligned c W x (π.symm (roleIdx c W hW x))) else A x

/-! ## Depth-indexed procedures -/

/-- Operations on the `W` role streams of a node. -/
inductive RoleOp (L : Layout) (β : Type) (W : ℕ) (Child : Type) where
  /-- a primitive on one role stream -/
  | prim (k : Fin W) (s : Step L β)
  /-- a pointwise gate on aligned role streams (only `touched` roles are read or changed) -/
  | gate (G : (Fin W → β) → (Fin W → β)) (touched : Finset (Fin W))
  /-- a child procedure on one role stream -/
  | call (k : Fin W) (child : Child)
  /-- a fixed permutation of the role streams (merge in a fixed order of row classes) -/
  | relabel (π : Equiv.Perm (Fin W))

/-- Operations of a procedure: a primitive on the current class, or a network node. -/
inductive Op (L : Layout) (β : Type) (Child : Type) where
  /-- a primitive on the current class -/
  | prim (s : Step L β)
  /-- a node: cyclic split into `W` role streams, role operations, merge -/
  | node (W : ℕ) (hW : 0 < W) (ops : List (RoleOp L β W Child))

/-- Procedures of recursion depth `d`. -/
def ProcK (L : Layout) (β : Type) : ℕ → Type
  | 0 => List (Step L β)
  | d + 1 => List (Op L β (ProcK L β d))

/-- Semantics of a role operation, given the semantics of children. -/
def RoleOp.run {L : Layout} {β : Type} {W : ℕ} {Child : Type}
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L) (hW : 0 < W) :
    RoleOp L β W Child → (L.Addr → β) → (L.Addr → β)
  | .prim k s, A => s.runIn (c.sub W hW k) A
  | .gate G _, A => gateRun c W hW G A
  | .call k ch, A => crun ch (c.sub W hW k) A
  | .relabel π, A => relabelRun c W hW π A

/-- Semantics of an operation in class `c`. -/
def Op.run {L : Layout} {β : Type} {Child : Type}
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L) :
    Op L β Child → (L.Addr → β) → (L.Addr → β)
  | .prim s, A => s.runIn c A
  | .node _ hW ops, A => ops.foldl (fun A o => o.run crun c hW A) A

/-- Semantics of a depth-`d` procedure run in class `c`. -/
def ProcK.run {L : Layout} {β : Type} :
    (d : ℕ) → ProcK L β d → RowClass L → (L.Addr → β) → (L.Addr → β)
  | 0, p, c, A => List.foldl (fun A s => Step.runIn c s A) A p
  | d + 1, p, c, A => List.foldl (fun A o => Op.run (ProcK.run d) c o A) A p

/-! ## Nominal costs

`*.cost` is a nominal model cost; no theorem here bounds TM2 time. All machine step bounds are proved in `SubNLogN/Machine/`. -/

/-- Parameters of the nominal model cost (`*.cost` is a nominal model cost; no theorem here bounds TM2
time). -/
structure CostParams where
  /-- cost per unit volume of every primitive -/
  c₀ : ℝ
  /-- record width in bits (volume = card · w) -/
  w : ℝ
  /-- nominal per-unit-volume cost of `swapBlocks` of `len` fields (a parameter) -/
  swapCost : ℕ → ℝ
  /-- `A = ⌈lg 2V⌉` for the repair primitive -/
  lgV : ℝ

/-- Volume `card · w / μ` of a row class (records of `w` bits; used by the nominal costs). -/
noncomputable def RowClass.vol {L : Layout} (P : CostParams) (c : RowClass L) : ℝ :=
  (L.card : ℝ) * P.w / c.μ

/-- Nominal model cost of a step run in class `c` (no theorem here bounds TM2 time). The repair step
pays only for the exceptional addresses of `c`. -/
noncomputable def Step.cost {L : Layout} {β : Type} (P : CostParams) (c : RowClass L) :
    Step L β → ℝ
  | .elem _ => P.c₀ * c.vol P
  | .recMap _ => P.c₀ * c.vol P
  | .addrMap _ => P.c₀ * c.vol P
  | .sparsePerm _ supp =>
      P.c₀ * (c.vol P + (supp.filter c.mem).card * P.lgV * (P.w + P.lgV))
  | .swapBlocks _ _ len => P.swapCost len * c.vol P
  | .digitGate _ _ => P.c₀ * c.vol P

/-- Nominal model cost of a role operation at a node in class `c` with `W` roles (role `k` runs in
`c.sub W k`, of volume `c.vol / W`); no theorem here bounds TM2 time. -/
noncomputable def RoleOp.cost {L : Layout} {β : Type} {W : ℕ} {Child : Type}
    (ccost : Child → RowClass L → ℝ) (P : CostParams) (c : RowClass L) (hW : 0 < W) :
    RoleOp L β W Child → ℝ
  | .prim k s => s.cost P (c.sub W hW k)
  | .gate _ t => P.c₀ * t.card * (c.vol P / W)
  | .call k ch => ccost ch (c.sub W hW k)
  | .relabel _ => P.c₀ * c.vol P

/-- Nominal model cost of an operation in class `c`: a node also pays split and merge (`2 c₀ vol`);
no theorem here bounds TM2 time. -/
noncomputable def Op.cost {L : Layout} {β : Type} {Child : Type} (ccost : Child → RowClass L → ℝ)
    (P : CostParams) (c : RowClass L) : Op L β Child → ℝ
  | .prim s => s.cost P c
  | .node _ hW ops => 2 * P.c₀ * c.vol P + (ops.map (RoleOp.cost ccost P c hW)).sum

/-- Nominal model cost of a depth-`d` procedure run in class `c` (`*.cost` is a nominal model cost; no
theorem here bounds TM2 time). -/
noncomputable def ProcK.cost {L : Layout} {β : Type} (P : CostParams) :
    (d : ℕ) → ProcK L β d → RowClass L → ℝ
  | 0, p, c => (List.map (Step.cost P c) p).sum
  | d + 1, p, c => (List.map (Op.cost (ProcK.cost P d) P c) p).sum

/-! ## Well-formedness -/

/-- Well-formedness of a step (radix bound `B`): elementary steps satisfy `Elem.WF`; a sparse
permutation has a bijective pull fixing every address outside its support; a digit gate acts on a field
of range `≤ B`; a block interchange `swapBlocks t₀ s₀ len` exchanges two disjoint blocks that both lie
inside the layout and have equal ranges (`blockRange`). Record maps have no side condition. -/
def Step.WF {L : Layout} {β : Type} (B : ℕ) : Step L β → Prop
  | .elem e => e.WF B
  | .sparsePerm pull supp => Function.Bijective pull ∧ ∀ x, x ∉ supp → pull x = x
  | .digitGate i _ => L.r i ≤ B
  | .swapBlocks t₀ s₀ len => (t₀ + len ≤ s₀ ∨ s₀ + len ≤ t₀) ∧ t₀ + len ≤ L.n ∧ s₀ + len ≤ L.n ∧
      L.blockRange t₀ (t₀ + len) = L.blockRange s₀ (s₀ + len)
  | _ => True

/-- Well-formedness of a role operation: primitives well formed, gates read and change only their
`touched` roles, children well formed. -/
def RoleOp.WF {L : Layout} {β : Type} {W : ℕ} {Child : Type} (cwf : Child → Prop) (B : ℕ) :
    RoleOp L β W Child → Prop
  | .prim _ s => s.WF B
  | .gate G t => (∀ v v' : Fin W → β, (∀ k ∈ t, v k = v' k) → ∀ k ∈ t, G v k = G v' k) ∧
      ∀ v : Fin W → β, ∀ k, k ∉ t → G v k = v k
  | .call _ ch => cwf ch
  | .relabel _ => True

/-- Well-formedness of an operation. -/
def Op.WF {L : Layout} {β : Type} {Child : Type} (cwf : Child → Prop) (B : ℕ) : Op L β Child → Prop
  | .prim s => s.WF B
  | .node _ _ ops => ∀ o ∈ ops, o.WF cwf B

/-- Well-formedness of a depth-`d` procedure. -/
def ProcK.WF {L : Layout} {β : Type} (B : ℕ) : (d : ℕ) → ProcK L β d → Prop
  | 0, p => ∀ s ∈ @id (List (Step L β)) p, Step.WF B s
  | d + 1, p => ∀ o ∈ @id (List (Op L β (ProcK L β d))) p, Op.WF (ProcK.WF B d) B o

end SubNLogN.Math.Networks.Model
