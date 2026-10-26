import Contracts.W9.Common

/-!
# Contracts.W9.Sweep — the generic SWEEP and LEVEL combinators

Both combinators are **program transformers**. Each contract asserts that a combinator exists,
together with its program-logic rule. The rules are stated as `Triple`s over the layout-B stacks
`BLoc m`. They are not proved here; W9 implements and proves them.

* `W9_sweep` (generic SWEEP skeleton). It runs a node kernel `κ` once per group of `g`
  consecutive nodes of the level stream on `S`, in canonical order:
  * LOAD the group onto `W0` (entries only, terminators dropped: `groupSyms`);
  * run `κ`;
  * EMIT `W0` onto the private output stack S′ (scratch);
  * at `$`, FLIP S′ back onto `S`.

  The kernel may change the outer stacks (`outer`: tables, RET/RQ, counters, root stacks). Their
  evolution is an arbitrary indexed invariant `J i`, so one rule covers PRE (RET push), LEAF, and
  POST (`g = t1`, RQ pop).
* `W9_level` (generic LEVEL driver). It is the descent loop "while the tape head is at a PRE segment, run
  PRE", then LEAF, then the ascent loop "while at a POST segment, run POST". It is generic in the
  per-level state predicates `A ℓ` (before PRE(ℓ)) and `B ℓ` (after POST(ℓ)); the segment tags
  `symPre`, `symLeaf`, `symPost` on `TR` drive the loops.

Costs are the per-call costs plus an explicit overhead:
* sweep: linear in the stream symbols moved, plus `bitLen g` per group;
* level: `O(1)` per level.

A "no rewind after the last node" shortcut is not modelled. Instead, kernels restore the
table head and the level program skips the segment once. This changes constants only.
-/

namespace TMFw.Contracts

namespace W9

/-- The `i`-th group of `g` consecutive nodes. -/
def groupAt (g : ℕ) (xs : List (Array (ℤ × ℤ))) (i : ℕ) : List (Array (ℤ × ℤ)) :=
  (xs.drop (i * g)).take g

/-- LOAD format of a node group on `W0`: all entries of the group as one block, terminators dropped. -/
def groupSyms (grp : List (Array (ℤ × ℤ))) : List Sym := blkE (grp.flatMap Array.toList)

/-- `∑_{i<M} f i`. -/
def sumTo (M : ℕ) (f : ℕ → ℕ) : ℕ := ((List.range M).map f).sum

/-- Sanity: the second group of two nodes. -/
example : groupAt 2 [#[(0, 0)], #[(1, 1)], #[(2, 2)], #[(3, 3)]] 1 = [#[(2, 2)], #[(3, 3)]] := rfl

/-- The LOAD format of a group is the workspace-matrix format of the group as an array (`t1` child
outputs = the `t1 × r` matrix `qHat` of `W9_postNode`). -/
theorem groupSyms_eq_matSyms (grp : List (Array (ℤ × ℤ))) : groupSyms grp = matSyms grp.toArray := by
  simp [groupSyms, matSyms]

end W9

open W9

/-- **W9.sweep (generic SWEEP combinator).** There is a combinator `sweep` with one constant
`C`. For every kernel `κ` it works as follows. Suppose that for each group `i < M`, from any state
whose outer stacks satisfy `J i` and whose `W0` holds the group (`groupSyms`), `κ` produces the
following within `c i` steps:
* `out i` on `W0`;
* `S` untouched and all scratch restored;
* outer stacks satisfying `J (i+1)`.

Then `sweep κ` maps the stream `streamSyms xs ++ rest` on `S` to `out 0 ++ … ++ out (M−1) ++ $ ++ rest`,
with `J M` at the end and all scratch restored. The group size `g` is read from `C2`. The cost is
`∑ c i` plus `C·(|stream in| + |stream out| + M·(|g|+1) + 1)`.

The sweep keeps its own state (S′, the LOAD reversal stack, the group counter) on scratch stacks,
which the kernel restores; hence `4 ≤ m`. The FLIP stops at the sweep's own `$` marker on S′, so
outputs must not contain `$`. Instances:
* PRE: `g = 1`, `out i` = the children's `nodeSyms`, and `J` tracks the RET pushes;
* LEAF: `g = 1`;
* POST: `g = t1`, `out i` = one `nodeSyms`, and `J` tracks the RQ pops. `groupSyms` of a group is
  `matSyms` of the group as an array, the format `W9_postNode` expects. -/
def W9_sweep : Prop :=
  ∃ C : ℕ, ∀ (m : ℕ) (R : Type), 4 ≤ m →
    ∃ (Q : Type) (sweep : Prog (BLoc m) (fun _ => Sym) R → Prog (BLoc m) (fun _ => Sym) (R × Q)),
      Finite Q ∧ Nonempty Q ∧ (∀ κ : Prog (BLoc m) (fun _ => Sym) R, κ.Closed → (sweep κ).Closed) ∧
      ∀ (κ : Prog (BLoc m) (fun _ => Sym) R) (g M : ℕ) (xs : List (Array (ℤ × ℤ)))
        (out : ℕ → List Sym) (J : ℕ → (LB → List Sym) → Prop) (c : ℕ → ℕ),
        0 < g → xs.length = g * M → (∀ i < M, symLevel ∉ out i) →
        (∀ i < M, ∀ σ : BLoc m → List Sym, J i (outer σ) →
          σ (.inl .W0) = groupSyms (groupAt g xs i) →
          Triple [] (fun s => s.stk = σ) κ
            (fun s => s.stk (.inl .W0) = out i ∧ s.stk (.inl .S) = σ (.inl .S) ∧
              (∀ j, s.stk (.inr j) = σ (.inr j)) ∧ J (i + 1) (outer s.stk)) (c i)) →
        ∀ (σ : BLoc m → List Sym) (rest r2 : List Sym),
          σ (.inl .S) = streamSyms xs ++ rest → σ (.inl .W0) = [] →
          σ (.inl .C2) = natSyms g ++ r2 → TermOK r2 → J 0 (outer σ) →
          Triple [] (fun s => s.stk = σ) (sweep κ)
            (fun s => s.stk (.inl .S) = (List.range M).flatMap out ++ symLevel :: rest ∧
              s.stk (.inl .W0) = [] ∧ (∀ j, s.stk (.inr j) = σ (.inr j)) ∧ J M (outer s.stk))
            (sumTo M c + C * ((streamSyms xs).length + sumTo M (fun i => (out i).length) +
              M * (bitLen g + 1) + 1))

/-- **W9.level (generic LEVEL driver).** There is a combinator `lvl` with one
constant `C`, built from a PRE level program `preP`, a LEAF level program `leafP` and a POST level
program `postP`:
* while the head of `TR` is `symPre`, run `preP`;
* then run `leafP`;
* then, while the head of `TR` is `symPost`, run `postP`.

The rule is the chain rule for any depth `D` and state predicates `A ℓ` (before PRE(ℓ); `A D` is
before LEAF) and `B ℓ` (after POST(ℓ); `B D` is after LEAF), provided:
* the tape tags select the right branch;
* PRE(ℓ) maps `A ℓ` to `A (ℓ+1)`, LEAF maps `A D` to `B D`, and POST(ℓ) maps `B (ℓ+1)` to `B ℓ`.

Cost: the sum of the level costs plus `C·(2D+3)` for the loop tests. -/
def W9_level : Prop :=
  ∃ C : ℕ, ∀ (m : ℕ) (R : Type),
    ∃ (Q : Type) (lvl : Prog (BLoc m) (fun _ => Sym) R → Prog (BLoc m) (fun _ => Sym) R →
        Prog (BLoc m) (fun _ => Sym) R → Prog (BLoc m) (fun _ => Sym) (R × Q)),
      Finite Q ∧ Nonempty Q ∧
      (∀ a b c : Prog (BLoc m) (fun _ => Sym) R, a.Closed → b.Closed → c.Closed →
        (lvl a b c).Closed) ∧
      ∀ (preP leafP postP : Prog (BLoc m) (fun _ => Sym) R) (D : ℕ)
        (A B : ℕ → (BLoc m → List Sym) → Prop) (cPre cPost : ℕ → ℕ) (cLeaf : ℕ),
        (∀ ℓ < D, ∀ σ, A ℓ σ → (σ (.inl .TR)).head? = some symPre) →
        (∀ σ, A D σ → (σ (.inl .TR)).head? = some symLeaf) →
        (∀ ℓ < D, ∀ σ, B (ℓ + 1) σ → (σ (.inl .TR)).head? = some symPost) →
        (∀ σ, B 0 σ → (σ (.inl .TR)).head? ≠ some symPost) →
        (∀ ℓ < D, ∀ σ, A ℓ σ →
          Triple [] (fun s => s.stk = σ) preP (fun s => A (ℓ + 1) s.stk) (cPre ℓ)) →
        (∀ σ, A D σ → Triple [] (fun s => s.stk = σ) leafP (fun s => B D s.stk) cLeaf) →
        (∀ ℓ < D, ∀ σ, B (ℓ + 1) σ →
          Triple [] (fun s => s.stk = σ) postP (fun s => B ℓ s.stk) (cPost ℓ)) →
        ∀ σ, A 0 σ →
          Triple [] (fun s => s.stk = σ) (lvl preP leafP postP) (fun s => B 0 s.stk)
            (sumTo D cPre + cLeaf + sumTo D cPost + C * (2 * D + 3))

/-- The three segment tags are distinct, so the two loops of `W9_level` stop where intended. -/
theorem symTags_distinct : symPre ≠ symLeaf ∧ symPre ≠ symPost ∧ symLeaf ≠ symPost := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

#assert_std_axioms symTags_distinct W9.groupSyms_eq_matSyms

end TMFw.Contracts
