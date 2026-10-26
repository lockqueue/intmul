import SubNLogN.Math.Networks.PhaseFrames

/-!
# Networks, part 8: the name-level cell calculus (checker + soundness contracts)

A computable 3-atom cell calculus for the tensor-cube subspace labels of [OAI26, §3.3], working on
*names* instead of triples, so that no triple, role or orbit is ever enumerated. In every label of
one role, coordinate `k` mentions at most two triples, named `0` (the role's own/bank triple, or the
invocation's fixed triple) and `1` (the neighbour `T` of a side wire `A_{ST}`); they are orthogonal
nondegenerate lines in both label fields. The atoms of coordinate `k` are the mentioned lines and
their joint complement (dimension `h − #names`); labels are unions of cells (`≤ 27`); residual
dimensions and bit ranks are sums of cell dimensions.

Soundness (contracts below): for every role `w` of a class `c`, the concrete per-role sums equal
the name-level sums of `c`. The evaluation at `h = 100` (`rank_total_bit`, `rank_total_complex`)
is by `decide +kernel`.

**Status (read this before citing the totals).** `rank_total_bit` and `rank_total_complex` are
evaluations of this name-level checker only. The checker itself does NOT verify that cell lists are
duplicate-free, that summands of a label do not overlap, that referenced names are valid, or that
adjacent labels are nested (verified separately by the soundness proofs). Hence the two totals say
nothing about the networks by themselves. They yield the network facts B4/C4 (`prop7_rank_sum`,
`prop8_count`) only together with the soundness contracts `SoundBitStmt`/`SoundComplexStmt` (which
are hypotheses of those theorems; their proofs must establish the four conditions above) and the
class-counting contracts.
-/

namespace SubNLogN.Math.Networks.Cell

/-- Name-level tokens. -/
inductive ATok
  | zero
  | full
  | line (i : Fin 2)
  | perp (i : Fin 2)
  | perp2
  deriving DecidableEq

/-- Name-level labels. -/
abbrev ALabel := List (ATok × ATok × ATok)

/-- Atoms of one coordinate: a mentioned line, or the complement of all mentioned lines. -/
inductive Atom
  | L (i : Fin 2)
  | C
  deriving DecidableEq

/-- Names mentioned by a token. -/
def tokNames : ATok → List (Fin 2)
  | .line i => [i]
  | .perp i => [i]
  | .perp2 => [0, 1]
  | _ => []

/-- Names mentioned at coordinate `k` by a list of labels. -/
def coordNames (Ls : List ALabel) (k : Fin 3) : List (Fin 2) :=
  ((Ls.flatMap id).flatMap fun σ =>
    tokNames (if k = 0 then σ.1 else if k = 1 then σ.2.1 else σ.2.2)).dedup

/-- The atoms of a coordinate with mentioned names `R`. -/
def atoms (R : List (Fin 2)) : List Atom := R.map .L ++ [.C]

/-- A token as a set (list) of atoms. -/
def tokAtoms (R : List (Fin 2)) : ATok → List Atom
  | .zero => []
  | .full => atoms R
  | .line i => [.L i]
  | .perp i => (atoms R).filter (· ≠ .L i)
  | .perp2 => (atoms R).filter (fun a => a ≠ .L 0 ∧ a ≠ .L 1)

/-- Dimension of an atom. -/
def atomDim (h : ℕ) (R : List (Fin 2)) : Atom → ℕ
  | .L _ => 1
  | .C => h - R.length

/-- Cells of a label. -/
def cells (R : Fin 3 → List (Fin 2)) (L : ALabel) : List (Atom × Atom × Atom) :=
  L.flatMap fun σ => (tokAtoms (R 0) σ.1).flatMap fun x => (tokAtoms (R 1) σ.2.1).flatMap fun y =>
    (tokAtoms (R 2) σ.2.2).map fun z => (x, y, z)

/-- Dimension of a cell. -/
def cellDim (h : ℕ) (R : Fin 3 → List (Fin 2)) (c : Atom × Atom × Atom) : ℕ :=
  atomDim h (R 0) c.1 * atomDim h (R 1) c.2.1 * atomDim h (R 2) c.2.2

/-- Residual dimension `|dim head − dim tail|` of a nested edge, as a cell sum. -/
def edgeDim (h : ℕ) (t hd : ALabel) : ℕ :=
  let R := coordNames [t, hd]
  let ct := cells R t
  let ch := cells R hd
  ((ch.filter (· ∉ ct)) ++ (ct.filter (· ∉ ch))).foldr (fun c acc => cellDim h R c + acc) 0

/-- Bit rank of `s_hd P_hd − s_t P_t` as a cell sum (`s = −1` only at the `X` sources). -/
def edgeRank (h : ℕ) (st sh : ℤ) (t hd : ALabel) : ℕ :=
  let R := coordNames [t, hd]
  let ct := cells R t
  let ch := cells R hd
  ((ch ++ ct.filter (· ∉ ch)).filter fun c =>
      sh * (if c ∈ ch then 1 else 0) - st * (if c ∈ ct then 1 else 0) ≠ 0).foldr
    (fun c acc => cellDim h R c + acc) 0

/-! ### Name-level stage tables (mirror `Labels.lean`) -/

/-- `A ⊗ τ ⊗ Q`. -/
def aA : Stage → ATok → ALabel
  | .one, τ => [(τ, .line 0, .line 0)]
  | .two, τ => [(.full, τ, .line 0)]
  | .three, τ => [(.full, .full, τ)]

/-- `B ⊗ τ ⊗ Q`. -/
def aB : Stage → ATok → ALabel
  | .one, _ => []
  | .two, τ => [(.perp 0, τ, .line 0)]
  | .three, τ => [(.perp 0, .full, τ), (.line 0, .perp 0, τ)]

/-- `P ⊗ τ ⊗ Q`. -/
def aP : Stage → ATok → ALabel
  | .one, τ => [(τ, .line 0, .line 0)]
  | .two, τ => [(.line 0, τ, .line 0)]
  | .three, τ => [(.line 0, .line 0, τ)]

/-- Side gate label at time `r` with bank-triple name `t` (table (6), [OAI26, §3.3, (6)]). -/
def aSide (j : Stage) (r : Fin 8) (t : Fin 2) : ALabel :=
  if r = 0 then aB j (.line t) else if r = 2 then aB j .full ++ aP j (.line t)
  else if r = 5 then aB j .full ++ aP j (.perp t) else aA j .full

/-- Centre gate label at time `r`. -/
def aCenter (j : Stage) (r : Fin 8) : ALabel := if r = 3 ∨ r = 6 then aA j .full else aB j .full

/-- Role classes (orbit representatives under coordinate symmetries). -/
inductive RClass
  | X
  | Y
  | side (j : Stage)
  | center (j : Stage)

/-- Name-level vertex labels of a class, with the frame sign of the first vertex. -/
def classLabels : RClass → List ALabel
  | .X => [[(.line 0, .line 0, .line 0)]] ++ [Stage.one, .two, .three].flatMap
      (fun j => [aSide j 2 0, aCenter j 3, aCenter j 6, aSide j 7 0]) ++ [[(.full, .full, .full)]]
  | .Y => [[]] ++ [Stage.one, .two, .three].flatMap
      (fun j => [aSide j 0 0, aCenter j 1, aCenter j 4, aSide j 5 0]) ++
      [[(.perp 0, .full, .full), (.line 0, .perp 0, .full), (.line 0, .line 0, .perp 0)]]
  | .side j =>
      let yb : Fin 2 := if j.isInverse then 1 else 0
      let xb : Fin 2 := if j.isInverse then 0 else 1
      [[], aSide j 0 yb, aSide j 2 xb, aSide j 5 yb, aSide j 7 xb, [(.full, .full, .full)]]
  | .center j => [[], aCenter j 1, aCenter j 3, aCenter j 4, aCenter j 6, [(.full, .full, .full)]]

/-- Sum of residual dimensions over the edges of a class. -/
def classDimSum (h : ℕ) (c : RClass) : ℕ :=
  let Ls := classLabels c
  ((Ls.zip Ls.tail).map fun e => edgeDim h e.1 e.2).sum

/-- Sum of bit ranks over the edges of a class (source sign `−1` for `X`). -/
def classRankSum (h : ℕ) (c : RClass) : ℕ :=
  let Ls := classLabels c
  let s0 : ℤ := match c with | .X => -1 | _ => 1
  ((Ls.zip Ls.tail).zipIdx.map fun e => edgeRank h (if e.2 = 0 then s0 else 1) 1 e.1.1 e.1.2).sum

/-- Class multiplicities (by role-class symmetry): `N, N`, and per stage `v²·v·z` side wires and
`v²·c` central wires. -/
def totalBit (h : ℕ) : ℕ :=
  tripleN h * (classRankSum h .X + classRankSum h .Y) +
  ([Stage.one, .two, .three].map fun j =>
    tripleV h ^ 2 * (tripleV h * tripleZb h) * classRankSum h (.side j) +
    tripleV h ^ 2 * h * classRankSum h (.center j)).sum

/-- Complex total (`c = h + 1` central wires per invocation). -/
def totalComplex (h : ℕ) : ℕ :=
  tripleN h * (classDimSum h .X + classDimSum h .Y) +
  ([Stage.one, .two, .three].map fun j =>
    tripleV h ^ 2 * (tripleV h * tripleZc h) * classDimSum h (.side j) +
    tripleV h ^ 2 * (h + 1) * classDimSum h (.center j)).sum

/-- Kernel evaluation of the name-level checker: its bit rank total at `h = 100` equals the integer
`s_b`. This is a statement about the checker, not about the network (see the module docstring). -/
theorem rank_total_bit : totalBit 100 = tripleSb 100 := by decide +kernel

/-- Kernel evaluation of the name-level checker: its complex residual total at `h = 100` equals the
integer `s_c`. This is a statement about the checker, not about the network (see the module
docstring). -/
theorem rank_total_complex : totalComplex 100 = tripleSc 100 := by decide +kernel

/-! ### Soundness against the network definitions -/

/-- The class of a role. -/
def classOf {κ : Kind} {h : ℕ} : Role κ h → RClass
  | .X _ => .X
  | .Y _ => .Y
  | .side j _ _ => .side j
  | .center j _ _ => .center j

/-- CONTRACT (cell soundness, bit). At `h = 100`, for every role `w`, the rational ranks of its edge
matrices sum to the name-level class sum (3-atom cell calculus for [OAI26, §3.3, Lemma 6] and
the [OAI26, §3.4, Prop. 7] rank rule). Proof route: `labelSub` of a label = span of its cells;
cells are orthogonal; `P_V − P_U = Σ λ_c P_c`; rank = Σ dims; names ↦ the role's triples. -/
def SoundBitStmt : Prop :=
  ∀ w : Role .bit 100,
    ((edges w).map fun e => rankQ (edgeMatB e)).sum = classRankSum 100 (classOf w)

/-- CONTRACT (cell soundness, complex). At `h = 100`, for every role `w`, the residual dimensions
of its edges sum to the name-level class sum. -/
def SoundComplexStmt : Prop :=
  ∀ w : Role .complex 100,
    ((edges w).map fun e => Module.finrank (ZMod 2) (residC e)).sum = classDimSum 100 (classOf w)

/-- CONTRACT (class counting, bit). Every `h`: summing a class function over
all roles weighs `X`, `Y` by `N` and, per stage, side wires by `v²·v·z_b`, central wires by `v²·h`. -/
def SumClassOfBitStmt : Prop :=
  ∀ (h : ℕ) (f : RClass → ℕ),
    ∑ w : Role .bit h, f (classOf w) = tripleN h * (f .X + f .Y) +
      ([Stage.one, .two, .three].map fun j =>
        tripleV h ^ 2 * (tripleV h * tripleZb h) * f (.side j) + tripleV h ^ 2 * h * f (.center j)).sum

/-- CONTRACT (class counting, complex): side weight `v²·v·z_c`, central weight `v²·(h+1)`. -/
def SumClassOfComplexStmt : Prop :=
  ∀ (h : ℕ) (f : RClass → ℕ),
    ∑ w : Role .complex h, f (classOf w) = tripleN h * (f .X + f .Y) +
      ([Stage.one, .two, .three].map fun j =>
        tripleV h ^ 2 * (tripleV h * tripleZc h) * f (.side j) +
          tripleV h ^ 2 * (h + 1) * f (.center j)).sum

/-- (B4) [OAI26, §3.4, Prop. 7, (8)–(9)]: at `h = 100` the rational ranks of all edge matrices
sum to `s_b = W_b m − N + 2L_b` (`tripleSb 100`). Proved from the contracts `SoundBitStmt`, `SumClassOfBitStmt`
(hypotheses) and the kernel evaluation `rank_total_bit`. -/
theorem prop7_rank_sum (hsound : SoundBitStmt) (hcount : SumClassOfBitStmt) :
    ∑ w : Role .bit 100, ((edges w).map fun e => rankQ (edgeMatB e)).sum = tripleSb 100 := by
  rw [Finset.sum_congr rfl (fun w _ => hsound w), hcount, ← rank_total_bit]
  rfl

/-- (C4) [OAI26, §3.5, Prop. 8]: at `h = 100` the residual dimensions (= orthonormal
basis lengths) sum to `s_c = W_c m − 2N + 2L_c` (`tripleSc 100`). -/
theorem prop8_count (hsound : SoundComplexStmt) (hcount : SumClassOfComplexStmt) :
    ∑ w : Role .complex 100, ((edges w).map fun e => Module.finrank (ZMod 2) (residC e)).sum =
      tripleSc 100 := by
  rw [Finset.sum_congr rfl (fun w _ => hsound w), hcount, ← rank_total_complex]
  rfl

end SubNLogN.Math.Networks.Cell
