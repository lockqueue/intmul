import SubNLogN.Math.Networks.AppCShear
import SubNLogN.Math.Networks.AppCModel

/-!
# Appendix A procedures (II): packed selected-bit addition (Lemma A.9 (`lem:transfer13`)) as an explicit abstract procedure

Lemma A.9 (`lem:transfer13`), Appendix A.4 (`sec:transfer-packed`). Three chunks `x, y, z` of `L = fK` binary
fields (most significant field first) at arbitrary physical positions `px, py, pz`. The procedure
`packedAddProc` performs `y_{j_i} ← y_{j_i} ⊕ x_{j_i}` (`j_i = ρ + iK`, `i < f`) and restores `z`:
1. the eight packed lines (`eightOps`): each moves its target chunk to the rightmost of the three chunk
   positions by `swapBlocks` (the Lemma A.8 (`lem:transfer12`) interchange, costed by its bound), shifts it by the packed offset
   `ε Σ_{i<f−1} 2^{j_i}[x_{j_i}=1][other_{j_i}=b]` (controls now precede the target), and moves it back;
2. the repair `sparsePerm` (pull `S₀ ∘ T₀`, supported on the exceptional set `B`);
3. the omitted top selected bit by one more shift of a single binary field.
-/

namespace SubNLogN.Math.Networks

open Model

/-- Physical positions (first fields) of the three chunks. -/
structure Chunks3 where
  /-- position of `x` -/
  px : ℕ
  /-- position of `y` -/
  py : ℕ
  /-- position of `z` -/
  pz : ℕ

/-- Bit `j` (from the least significant end) of the chunk of `L` binary fields at position `p`
(field `p` most significant): the single-field block `[p + L − 1 − j, p + L − j)`. -/
def chunkBit {Ly : Layout} (L p j : ℕ) (a : Ly.Addr) : ℕ := Ly.blockVal (p + L - 1 - j) (p + L - j) a

/-- Value of the chunk of `L` fields at position `p`. -/
def chunkVal {Ly : Layout} (L p : ℕ) (a : Ly.Addr) : ℕ := Ly.blockVal p (p + L) a

/-- Rightmost of the three chunk positions. -/
def Chunks3.right (C : Chunks3) : ℕ := max C.px (max C.py C.pz)

/-- Position of a chunk after interchanging the chunks at `pt` and `pr`. -/
def movedPos (pt pr p : ℕ) : ℕ := if p = pr then pt else if p = pt then pr else p

/-- One packed line (Lemma A.9 (`lem:transfer13`)). -/
def lineSteps {Ly : Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3) (op : Bool × ℤ × ℕ) :
    List (Step Ly β) :=
  let pt := if op.1 then C.py else C.pz
  let po := if op.1 then C.pz else C.py
  let pr := C.right
  let swp : List (Step Ly β) := if pt = pr then [] else [.swapBlocks pt pr L]
  let off : Ly.Addr → ℕ := fun a =>
    let s := ∑ i ∈ Finset.range (f - 1), 2 ^ (ρ + i * K) *
      (if chunkBit L (movedPos pt pr C.px) (ρ + i * K) a = 1 ∧
          chunkBit L (movedPos pt pr po) (ρ + i * K) a = op.2.2 then 1 else 0)
    if op.2.1 = 1 then s % 2 ^ L else (2 ^ L - s % 2 ^ L) % 2 ^ L
  swp ++ [.elem (.shift pr (pr + L) off)] ++ swp

/-- The omitted top selected bit `j = ρ + (f−1)K`: `y_j ← y_j ⊕ x_j` (Lemma A.9 (`lem:transfer13`)). -/
def topBitSteps {Ly : Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3) : List (Step Ly β) :=
  let pt := C.py
  let pr := C.right
  let j := ρ + (f - 1) * K
  let swp : List (Step Ly β) := if pt = pr then [] else [.swapBlocks pt pr L]
  swp ++ [.elem (.shift (pr + L - 1 - j) (pr + L - j) (fun a => chunkBit L (movedPos pt pr C.px) j a))] ++
    swp

/-- The chunk values `(x, y, z)` at an address. -/
def chunkVals {Ly : Layout} (L : ℕ) (C : Chunks3) (a : Ly.Addr) : ℕ × ℕ × ℕ :=
  (chunkVal L C.px a, chunkVal L C.py a, chunkVal L C.pz a)

/-- The address map `S₀` of the eight packed lines (on chunk values, `packedS0`). -/
def addrS0 {Ly : Layout} (L K ρ f : ℕ) (C : Chunks3) (a : Ly.Addr) : Ly.Addr :=
  let o := packedS0 L K ρ f (chunkVals L C a)
  Ly.blockSet C.pz (C.pz + L) (Ly.blockSet C.py (C.py + L) a o.2.1) o.2.2

/-- The ideal address map `T₀` (selected-bit XOR without the top bit, `packedT0`). -/
def addrT0 {Ly : Layout} (L K ρ f : ℕ) (C : Chunks3) (a : Ly.Addr) : Ly.Addr :=
  Ly.blockSet C.py (C.py + L) a (packedT0 K ρ f (chunkVals L C a)).2.1

open Classical in
/-- The repair step: pull `S₀ ∘ T₀` (moves the entry at `S₀ x₀` to `T₀ x₀`), supported on the
exceptional addresses (Lemma A.9 (`lem:transfer13`)). -/
noncomputable def repairStep {Ly : Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3) : Step Ly β :=
  .sparsePerm (fun a => addrS0 L K ρ f C (addrT0 L K ρ f C a))
    (Finset.univ.filter fun a => ¬ packedGood K ρ f (chunkVals L C a))

/-- **The Lemma A.9 (`lem:transfer13`) procedure** (straight-line, depth 0). -/
noncomputable def packedAddProc {Ly : Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3) : ProcK Ly β 0 :=
  eightOps.flatMap (lineSteps L K ρ f C) ++ [repairStep L K ρ f C] ++ topBitSteps L K ρ f C

/-- The full ideal map: `y ← y XOR Σ_{i<f} 2^{j_i} x_{j_i}` (an involution, so it is its own pull). -/
def addrXorAll {Ly : Layout} (L K ρ f : ℕ) (C : Chunks3) (a : Ly.Addr) : Ly.Addr :=
  Ly.blockSet C.py (C.py + L) a (Nat.xor (chunkVal L C.py a)
    (∑ i ∈ Finset.range f, 2 ^ (ρ + i * K) * chunkBit L C.px (ρ + i * K) a))

/-- Layout hypotheses for Lemma A.9 (`lem:transfer13`): `K ≥ 6`, `L = fK`, `ρ < K`, `f ≥ 1`; the three chunk blocks are
pairwise disjoint, inside the layout, and consist of binary fields. -/
def PackedHyps (Ly : Layout) (L K ρ f : ℕ) (C : Chunks3) : Prop :=
  6 ≤ K ∧ L = f * K ∧ ρ < K ∧ 1 ≤ f ∧
  C.px + L ≤ Ly.n ∧ C.py + L ≤ Ly.n ∧ C.pz + L ≤ Ly.n ∧
  (C.px + L ≤ C.py ∨ C.py + L ≤ C.px) ∧ (C.px + L ≤ C.pz ∨ C.pz + L ≤ C.px) ∧
  (C.py + L ≤ C.pz ∨ C.pz + L ≤ C.py) ∧
  ∀ i : Fin Ly.n, (C.px ≤ i.val ∧ i.val < C.px + L) ∨ (C.py ≤ i.val ∧ i.val < C.py + L) ∨
    (C.pz ≤ i.val ∧ i.val < C.pz + L) → Ly.r i = 2

/-- CONTRACT (Lemma A.9 (`lem:transfer13`) correctness). Using the scalar eight-operation program and the
agreement of the packed shifts with `T₀` off the exceptional set (explicit hypotheses; they are
only needed for well-formedness, so keeping them is harmless), the procedure computes exactly the
selected-bit XOR `y_{j_i} ⊕= x_{j_i}` (`i < f`) in any class `c` **whose row field lies outside the
three chunks** (every pull of the procedure changes only chunk fields, so it preserves membership
in `c`; without this condition a pull modifying the row field could leave `c`), for any
payload, with `x`, `z`, the other address fields and all records preserved. -/
def PackedProcCorrectStmt : Prop :=
  RunEightSpecStmt → PackedAgreeStmt →
  ∀ (Ly : Layout) (β : Type) (L K ρ f : ℕ) (C : Chunks3), PackedHyps Ly L K ρ f C →
    ∀ (c : RowClass Ly), (c.row.val < C.px ∨ C.px + L ≤ c.row.val) →
      (c.row.val < C.py ∨ C.py + L ≤ c.row.val) → (c.row.val < C.pz ∨ C.pz + L ≤ c.row.val) →
    ∀ (A : Ly.Addr → β),
      ProcK.run 0 (packedAddProc (Ly := Ly) (β := β) L K ρ f C) c A =
        fun a => if c.mem a then A (addrXorAll L K ρ f C a) else A a

/-- CONTRACT (Lemma A.9 (`lem:transfer13`) well-formedness). Every shift reads only fields before its target block, and the
repair pull is a bijection supported on its exceptional set (`PackedAgreeStmt`). -/
def PackedProcWFStmt : Prop :=
  PackedAgreeStmt →
  ∀ (Ly : Layout) (β : Type) (L K ρ f : ℕ) (C : Chunks3), PackedHyps Ly L K ρ f C →
    ProcK.WF 2 0 (packedAddProc (Ly := Ly) (β := β) L K ρ f C)

end SubNLogN.Math.Networks
