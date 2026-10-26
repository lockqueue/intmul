import Contracts.Machine.W4

/-!
# Contracts.W9.Common — layout-B vocabulary of the W9 stage contracts

The level-synchronous stack architecture (layout-B) runs the
snapshot's recursive transform level by level: PRE sweeps top-down, one LEAF sweep, then POST sweeps
bottom-up. Each sweep is one pass over a level stream. This file fixes the following, once for every
W9 contract:

* the named stacks `LB` and the stage-contract shape `BContract`;
* the stream encodings `entrySyms`, `blkE`, `nodeSyms`, `streamSyms`, `matSyms` and `hdrSyms`;
* the width measures `EntryW`, `ArrW`, `MatW`, `StreamW` and the per-entry symbol bound `eb`.

## Stacks

| `LB` | stack symbol | role in the W9 contracts |
|---|---|---|
| `S` | S | level stream `streamSyms xs`, canonical node order, first symbol on top |
| `W0` | W0 | node workspace: the interface between a sweep and its node kernel |
| `TL`, `TR` | TL, TR | table tape. The head is between them; `TR` is the unread part, first symbol on top |
| `RET` | RET | retained `alt_q`, the level LIFO |
| `RQ` | RQ | `alt_q` queue of the running POST level |
| `C0` | C0 | the current level's header (`hdrSyms`), copied from the tape |
| `C1` | C1 | stack of input precisions (`hdrSyms`); its top is the current level's `p_in` |
| `C2` | C2 | sweep group size `g` (`natSyms`) |
| `C3` | C3 | kernel-local index, e.g. the column `u2` |
| `OA`, `OB` | OA, OB | root operands and result |

All other layout-B stacks are private scratch (`Fin m`), and every stage restores them, as in the
`MContract` convention. These are S′, W1–W3, F/F′, the multiplier bank MB0–MB9 and the spare counters.

## Encodings

* **Entry**: `⟦(a, b)⟧ = intSyms a ++ [sep2] ++ intSyms b ++ [sep]`. It is a W4 record
  (`entrySyms_recOK`); `sep2` and `sep` delimit the real and imaginary coordinates.
* **Block** `blkE v`: the entries of `v`, first entry on top (`blk .down`).
* **Node** `nodeSyms x = blkE x ++ [|]`, and **level stream** `streamSyms xs`, the nodes followed by `$`.
* **Matrix** `matSyms M`: row-major block without row terminators. This is the workspace format of
  the node kernels; the counters on `C0` give the dimensions.
* **Header / precision stack** `hdrSyms fs`: naturals, each followed by `mark`.
-/

namespace TMFw.Contracts

namespace W9

/-! ## Stacks and the contract shape -/

/-- Named stacks of layout B that appear in W9 contracts. The table in the module doc gives the
role of each named stack in the level-synchronous pipeline. -/
inductive LB
  | S | W0 | TL | TR | RET | RQ | C0 | C1 | C2 | C3 | OA | OB
  deriving DecidableEq, Repr

/-- Stacks of a W9 stage: the named layout-B stacks plus `m` private scratch stacks. -/
abbrev BLoc (m : ℕ) : Type := LB ⊕ Fin m

/-- Scratch cap of a W9 stage. It covers the stage-private stacks (S′, W1–W3, F/F′, MB0–MB9,
spare counters), the scratch of the W3/W4/W5/W6 kernels that a stage embeds, and the combinators'
own scratch in the composites (`W9_pipeline`, `W9_multiply`). Kernels share scratch: each restores
it. -/
def w9Scratch : ℕ := 64

/-- **Shape of every W9 stage contract.** It is `MContract` (Contracts.Machine.Common) with the named
stacks fixed to `LB`, so W9 stages compose without renaming. There is one cost constant `C`. For
each compile-time parameter `p : Par` there is a **closed** program with `m ≤ maxScratch` scratch
stacks and a finite, nonempty register type `R`, satisfying `spec p m R C P`. As in `MContract`,
specs use `Runs` with exact final stacks, so every stack that is not updated is restored. -/
def BContract (Par : Type) (maxScratch : ℕ)
    (spec : Par → (m : ℕ) → (R : Type) → ℕ → Prog (BLoc m) (fun _ => Sym) R → Prop) : Prop :=
  ∃ C : ℕ, ∀ p : Par, ∃ (m : ℕ) (R : Type) (P : Prog (BLoc m) (fun _ => Sym) R),
    m ≤ maxScratch ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧ spec p m R C P

/-- The named stacks a node kernel may see: everything except the stream `S` and the workspace `W0`,
which belong to the sweep. They are used by `W9_sweep`'s invariant. -/
def outer {m : ℕ} (σ : BLoc m → List Sym) (k : LB) : List Sym :=
  if k = .S ∨ k = .W0 then [] else σ (.inl k)

/-! ## Layout symbols -/

/-- `|`: end of node. -/
def symNode : Sym := .tag 0
/-- `$`: end of level. -/
def symLevel : Sym := .tag 1
/-- `#`: bottom of a RET segment. -/
def symRet : Sym := .tag 2
/-- `§`: start of a PRE table segment. -/
def symPre : Sym := .tag 3
/-- Start of the LEAF table segment. -/
def symLeaf : Sym := .tag 4
/-- Start of a POST table segment. -/
def symPost : Sym := .tag 5
/-- `‖`: end of a table row or sub-table. -/
def symSub : Sym := .tag 6
/-- Rewind sentinel. It never occurs in streams or tapes. A stage that must restore a stack whose
old content is arbitrary first pushes `symGuard` and later rewinds down to it. Example: a node kernel
rewinding the table head onto `TL` (a filter row's length is not fixed, so the reversed PRE body
cannot be parsed back without a delimiter), or the pipeline's final tape rewind. -/
def symGuard : Sym := .tag 7

/-! ## Stream encodings -/

/-- Entry `⟦(a, b)⟧ = sgn a · bits|a| · sep2 · sgn b · bits|b| · sep` (LSB first). -/
def entrySyms (z : ℤ × ℤ) : List Sym := intSyms z.1 ++ Sym.sep2 :: (intSyms z.2 ++ [Sym.sep])

/-- A block of entries, first entry on top (`blk .down`). -/
def blkE (v : List (ℤ × ℤ)) : List Sym := blk .down (v.map entrySyms)

/-- Node `⟦x⟧ₙ = ⟦x₀⟧ … ⟦x_{N−1}⟧ |`. -/
def nodeSyms (x : Array (ℤ × ℤ)) : List Sym := blkE x.toList ++ [symNode]

/-- Level stream `⟦xs⟧ = ⟦x⁰⟧ₙ … ⟦x^{M−1}⟧ₙ $`. -/
def streamSyms (xs : List (Array (ℤ × ℤ))) : List Sym := xs.flatMap nodeSyms ++ [symLevel]

/-- Workspace matrix: row-major block of all entries, no row terminators. -/
def matSyms (M : Array (Array (ℤ × ℤ))) : List Sym := blkE (M.toList.flatMap Array.toList)

/-- Naturals, each followed by `mark`: level headers on the tape and on `C0`, the precision stack
`C1`, root parameters, and the root digit list. -/
def hdrSyms (fs : List ℕ) : List Sym := fs.flatMap fun n => natSyms n ++ [Sym.mark]

/-! ## Width measures -/

/-- Both coordinates have magnitude bit length at most `w`. -/
def EntryW (w : ℕ) (z : ℤ × ℤ) : Prop := bitLen z.1.natAbs ≤ w ∧ bitLen z.2.natAbs ≤ w

/-- Every entry of the array has width at most `w`. -/
def ArrW (w : ℕ) (x : Array (ℤ × ℤ)) : Prop := ∀ z ∈ x.toList, EntryW w z

/-- Every entry of the matrix has width at most `w`. -/
def MatW (w : ℕ) (M : Array (Array (ℤ × ℤ))) : Prop := ∀ row ∈ M.toList, ArrW w row

/-- Every entry of every node of the stream has width at most `w`. -/
def StreamW (w : ℕ) (xs : List (Array (ℤ × ℤ))) : Prop := ∀ x ∈ xs, ArrW w x

/-- Symbols per entry of width `w`: `2·w + 4` (`length_entrySyms_le`). -/
def eb (w : ℕ) : ℕ := 2 * w + 4

/-! ## Cheap facts -/

theorem isData_intSyms (z : ℤ) : ∀ x ∈ intSyms z, isDataSym x = true := by
  intro x hx
  simp only [intSyms, natSyms, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨b, -, rfl⟩
  · unfold sgnSym
    split <;> rfl
  · rfl

/-- Entries are W4 records, so the W4 routing kernels move them. -/
theorem entrySyms_recOK (z : ℤ × ℤ) : RecOK (entrySyms z) := by
  refine ⟨intSyms z.1 ++ Sym.sep2 :: intSyms z.2, by simp [entrySyms], ?_⟩
  intro x hx
  simp only [List.mem_append, List.mem_cons] at hx
  rcases hx with h | rfl | h
  · exact isData_intSyms _ x h
  · rfl
  · exact isData_intSyms _ x h

theorem length_entrySyms (z : ℤ × ℤ) :
    (entrySyms z).length = bitLen z.1.natAbs + bitLen z.2.natAbs + 4 := by
  simp only [entrySyms, intSyms, List.length_append, List.length_cons, List.length_nil,
    length_natSyms]
  omega

theorem length_entrySyms_le {w : ℕ} {z : ℤ × ℤ} (h : EntryW w z) : (entrySyms z).length ≤ eb w := by
  rw [length_entrySyms]
  unfold eb
  obtain ⟨h1, h2⟩ := h
  omega

/-- Symbol length of a block from entry count and width (used to convert the symbol-measured costs
of the W4 kernels and of the sweeps). -/
theorem length_blkE_le (w : ℕ) :
    ∀ v : List (ℤ × ℤ), (∀ z ∈ v, EntryW w z) → (blkE v).length ≤ v.length * eb w
  | [], _ => by simp [blkE, blk]
  | z :: v, h => by
    have h1 := length_entrySyms_le (h z (List.mem_cons_self ..))
    have h2 := length_blkE_le w v (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [blkE, blk, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons] at h2 ⊢
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- The rewind sentinel differs from every layout tag. Data symbols are never tags, so it occurs in
no stream or tape. -/
theorem symGuard_fresh : symGuard ≠ symNode ∧ symGuard ≠ symLevel ∧ symGuard ≠ symRet ∧
    symGuard ≠ symPre ∧ symGuard ≠ symLeaf ∧ symGuard ≠ symPost ∧ symGuard ≠ symSub := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

#assert_std_axioms isData_intSyms entrySyms_recOK length_entrySyms length_entrySyms_le
  length_blkE_le symGuard_fresh

end W9

end TMFw.Contracts
