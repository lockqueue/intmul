import SubNLogN.Math.Networks.AppCCore

/-!
# Class-local safety of the Appendix A procedures (contract file)

(`AppC` in filenames is a historical prefix retained for stability, corresponding to Appendix A (`app:parameter-transfer`).)
`Step.WF` (`AppCModel.lean`) does not imply that a primitive run inside a row class `c` (a role
stream) reads only addresses of `c`, nor that role splits are complete (`withRow` silently returns
its argument when the new row value is out of range). A well-formed restricted permutation whose pull
leaves the class would duplicate data. This file defines the missing class-safety predicates
(definitions only) and states as contracts:

* class safety implies class-local reads and writes of a whole procedure (`SafeRunLocalStmt`);
* aligned partner addresses of a complete role split behave as intended (`AlignedSpecStmt`,
  `AlignedSelfStmt`);
* the Appendix A procedures Proposition A.7 (`prop:transfer11`) `interchangeProc`, Lemma A.9 (`lem:transfer13`) `packedAddProc` and Lemma A.10 (`lem:transfer-phase`) `cCoreProc` are class safe
  under the hypotheses of their correctness/WF contracts.

These are value-level facts about the abstract model. Well-formedness (`ProcK.WF`) is a separate
predicate, established by the `…WFStmt` contracts; `ProcK.ClassSafe` deliberately does not include
it. Machine-level executability and step bounds are proved in `SubNLogN/Machine/`.
-/

namespace SubNLogN.Math.Networks.Model

/-- A map of addresses preserves membership in the class `c`, in both directions. -/
def PreservesClass {L : Layout} (c : RowClass L) (f : L.Addr → L.Addr) : Prop :=
  ∀ x, c.mem (f x) ↔ c.mem x

/-- `F` reads only the class `c`: arrays agreeing on `c` have images agreeing on `c`. -/
def ReadsWithin {L : Layout} {β : Type} (c : RowClass L)
    (F : (L.Addr → β) → (L.Addr → β)) : Prop :=
  ∀ A B : L.Addr → β, (∀ x, c.mem x → A x = B x) → ∀ x, c.mem x → F A x = F B x

/-- `F` changes no address outside the class `c`. -/
def WritesWithin {L : Layout} {β : Type} (c : RowClass L)
    (F : (L.Addr → β) → (L.Addr → β)) : Prop :=
  ∀ (A : L.Addr → β) (x : L.Addr), ¬ c.mem x → F A x = A x

/-- The cyclic split of `c` into `W` role streams is complete: `μ·W` divides the row range, so every
aligned partner address exists (no silent fallback in `withRow`). -/
def CompleteRoles {L : Layout} (c : RowClass L) (W : ℕ) : Prop :=
  0 < W ∧ c.μ * W ∣ L.r c.row

/-- The pull map of `swapBlocks t₀ s₀ len` (exactly as in `Step.run`). -/
def swapPullMap (L : Layout) (t₀ s₀ len : ℕ) (x : L.Addr) : L.Addr :=
  L.blockSet s₀ (s₀ + len) (L.blockSet t₀ (t₀ + len) x (L.blockVal s₀ (s₀ + len) x))
    (L.blockVal t₀ (t₀ + len) x)

/-- Class safety of one primitive run in class `c`: every address read for an output address of
`c` lies in `c` (pull maps preserve the class; gate fibres stay in the class). -/
def Step.ClassSafe {L : Layout} {β : Type} (c : RowClass L) : Step L β → Prop
  | .elem e => PreservesClass c e.pull
  | .recMap _ => True
  | .addrMap _ => True
  | .sparsePerm pull _ => PreservesClass c pull
  | .swapBlocks t₀ s₀ len => PreservesClass c (swapPullMap L t₀ s₀ len)
  | .digitGate i _ => ∀ (x : L.Addr) (v : Fin (L.r i)), c.mem x → c.mem (Function.update x i v)

/-- Class safety of a role operation of a node in class `c` with `W` roles (children are checked in
their sub-classes by `csafe`). -/
def RoleOp.ClassSafe {L : Layout} {β : Type} {W : ℕ} {Child : Type}
    (csafe : Child → RowClass L → Prop) (c : RowClass L) (hW : 0 < W) :
    RoleOp L β W Child → Prop
  | .prim k s => Step.ClassSafe (c.sub W hW k) s
  | .gate _ _ => True
  | .call k ch => csafe ch (c.sub W hW k)
  | .relabel _ => True

/-- Class safety of an operation in class `c`; a node also needs a complete role split. -/
def Op.ClassSafe {L : Layout} {β : Type} {Child : Type}
    (csafe : Child → RowClass L → Prop) (c : RowClass L) : Op L β Child → Prop
  | .prim s => Step.ClassSafe c s
  | .node W hW ops => CompleteRoles c W ∧ ∀ o ∈ ops, RoleOp.ClassSafe csafe c hW o

/-- Class safety of a depth-`d` procedure run in class `c` (recursively; children in their
sub-classes). Does not include `ProcK.WF`. `List.Forall P l ↔ ∀ x ∈ l, P x` is
`List.forall_iff_forall_mem`. -/
def ProcK.ClassSafe {L : Layout} {β : Type} : (d : ℕ) → ProcK L β d → RowClass L → Prop
  | 0, p, c => List.Forall (fun s => Step.ClassSafe c s) p
  | d + 1, p, c => List.Forall (fun o => Op.ClassSafe (ProcK.ClassSafe d) c o) p

/-- CONTRACT (`AlignedSpecStmt`, proved as `alignedSpec_holds`). For `x` in `c` and a complete split into `W` roles, the
aligned partner of `x` in role `k` is in `c`, has role `k`, the same role position, and differs
from `x` only in the row field. -/
def AlignedSpecStmt : Prop :=
  ∀ (L : Layout) (c : RowClass L) (W : ℕ) (x : L.Addr), c.mem x →
    ∀ (hcomplete : CompleteRoles c W) (k : Fin W),
      c.mem (aligned c W x (k : ℕ)) ∧ roleIdx c W hcomplete.1 (aligned c W x (k : ℕ)) = k ∧
      rolePos c W (aligned c W x (k : ℕ)) = rolePos c W x ∧
      ∀ i, i ≠ c.row → aligned c W x (k : ℕ) i = x i

/-- CONTRACT (`AlignedSelfStmt`, proved as `alignedSelf_holds`). -/
def AlignedSelfStmt : Prop :=
  ∀ (L : Layout) (c : RowClass L) (W : ℕ) (x : L.Addr), c.mem x →
    ∀ (hcomplete : CompleteRoles c W), aligned c W x (roleIdx c W hcomplete.1 x : ℕ) = x

/-- CONTRACT (`SafeRunLocalStmt`, proved as `safeRunLocal_holds`). A class-safe procedure run in class `c` reads only
`c` and writes only `c`. -/
def SafeRunLocalStmt : Prop :=
  ∀ (L : Layout) (β : Type) (d : ℕ) (p : ProcK L β d) (c : RowClass L),
    ProcK.ClassSafe d p c → ReadsWithin c (ProcK.run d p c) ∧ WritesWithin c (ProcK.run d p c)

end SubNLogN.Math.Networks.Model

namespace SubNLogN.Math.Networks

open Model

/-- CONTRACT (`InterchangeProcClassSafeStmt`; Proposition A.7 (`prop:transfer11`)). Same hypotheses as `InterchangeProcWFStmt`. -/
def InterchangeProcClassSafeStmt : Prop :=
  ∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ) (c : RowClass L),
    InterchangeHyps L q fac k h₀ d₀ c →
      ProcK.ClassSafe k (interchangeProc (L := L) (β := β) q fac k h₀ d₀) c

/-- CONTRACT (`PackedProcClassSafeStmt`; Lemma A.9 (`lem:transfer13`)). Same hypotheses as `PackedProcCorrectStmt`
(row field outside the three chunks), without `RunEightSpecStmt`/`PackedAgreeStmt`. -/
def PackedProcClassSafeStmt : Prop :=
  ∀ (Ly : Layout) (β : Type) (L K ρ f : ℕ) (C : Chunks3), PackedHyps Ly L K ρ f C →
    ∀ (c : RowClass Ly), (c.row.val < C.px ∨ C.px + L ≤ c.row.val) →
      (c.row.val < C.py ∨ C.py + L ≤ c.row.val) → (c.row.val < C.pz ∨ C.pz + L ≤ c.row.val) →
      ProcK.ClassSafe 0 (packedAddProc (Ly := Ly) (β := β) L K ρ f C) c

/-- CONTRACT (`CCoreProcClassSafeStmt`; Lemma A.10 (`lem:transfer-phase`)). Same class hypotheses as `CCoreProcWFStmt`
(`CCoreHyps`), with no certificate or edge-data validity assumption (addressing does not depend
on the edge data). -/
def CCoreProcClassSafeStmt : Prop :=
  ∀ (A K D S rr ρ kLeaf : ℕ) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (k j0 : ℕ) (c : RowClass (layerLayout A K D S)), CCoreHyps A K D S ρ cdat k j0 c →
      ProcK.ClassSafe k (cCoreProc A K D S rr ρ kLeaf cdat k j0) c

end SubNLogN.Math.Networks
