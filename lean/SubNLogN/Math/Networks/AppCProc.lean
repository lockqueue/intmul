import SubNLogN.Math.Networks.Cert
import SubNLogN.Math.Networks.Deficit
import SubNLogN.Math.Networks.AppCShear
import SubNLogN.Math.Networks.AppCModel

/-!
# Appendix A procedures (I): the power-width interchange (Proposition A.7 (`prop:transfer11`)) as an explicit abstract procedure

Proposition A.7 (`prop:transfer11`) on top of Lemma A.6 (`lem:transfer-shear`), Appendix A.2 (`sec:transfer-power`), written in
the abstract stream model v2 (`AppCModel.lean`, row classes, depth-indexed procedures).
`interchangeProc q fac k h₀ d₀` exchanges the two chunks of `m^k` radix-`q` digit fields starting at
fields `h₀` and `d₀` (`m = 10⁶`, the bit network at `h = 100`):
* depth 0: one digit interchange (`Elem.pair`);
* depth `k+1`: `D ← D − H` (shifts of the later group), one *network node* realizing `H ← H + D`, and
  `D ← H − D`. The node splits the class into the `W_b` role streams and runs the framed bit network in
  time order: before each gate the incoming edge of every touched wire is applied as the Lemma A.6 (`lem:transfer-shear`) shear program
  for `A_e mod q^b` (lower-triangular unit/shift steps and, per pivot, two shifts around one child
  interchange of depth `k`), then the gate (the scalar row of `Scalar.lean`); finally the sink edges and
  the role relabelling `ρ`.
The factorizations (`fac`) and the prime `q` are parameters; their validity is a hypothesis of the
contracts. The network facts are explicit hypotheses (`BitNetCert` of `Cert.lean`).
-/

namespace SubNLogN.Math.Networks

open Model

/- `mH`, `cubeEquiv`, `FacData`, `FacData.Valid`, `edgeMatFin`, `ExistsValidFacStmt` are in `Cert.lean`. -/

/-- Residue of a rational modulo `R`, as a natural number. -/
def ratModNat (R : ℕ) (r : ℚ) : ℕ := (ratMod R r).val

/-- Field block of coordinate `i` in a chunk starting at field `t₀` with `b` fields per coordinate. -/
def blk (t₀ b : ℕ) (i : Fin mH) : ℕ × ℕ := (t₀ + i.val * b, t₀ + (i.val + 1) * b)

/-- `X_i ← Σ_j E_ij X_j` (lower-triangular `E`) on the chunk at `t₀`, coordinates in descending order,
each as a unit step on `X_i` followed by a shift reading the earlier `X_j`; modulus `R = q^b`. -/
def lowerSteps {L : Layout} {β : Type} (R t₀ b : ℕ) (E : Matrix (Fin mH) (Fin mH) ℚ) :
    List (Step L β) :=
  (List.finRange mH).reverse.flatMap fun i =>
    [.elem (.unit (blk t₀ b i).1 (blk t₀ b i).2 (ratModNat R (E i i)) (ratModNat R (E i i)⁻¹)),
     .elem (.shift (blk t₀ b i).1 (blk t₀ b i).2 (fun x =>
        ∑ j ∈ Finset.univ.filter (fun j : Fin mH => j < i),
          ratModNat R (E i j) * L.blockVal (blk t₀ b j).1 (blk t₀ b j).2 x))]

/-- The Lemma A.6 (`lem:transfer-shear`) shear program on one role stream: `linD E₂`, `linH E₁⁻¹`, pivot triples (child interchange in
the middle), `linH E₁`, `linD E₂⁻¹`. -/
def shearOps {L : Layout} {β : Type} {W : ℕ} {Child : Type} (R h₀ d₀ b : ℕ) (k : Fin W) (F : FacData)
    (childOf : Fin mH → Fin mH → Child) : List (RoleOp L β W Child) :=
  (lowerSteps R d₀ b F.E₂).map (.prim k) ++ (lowerSteps R h₀ b F.E₁').map (.prim k) ++
  F.piv.flatMap (fun p =>
    [.prim k (.elem (.shift (blk d₀ b p.2).1 (blk d₀ b p.2).2
        (fun x => L.blockVal (blk h₀ b p.1).1 (blk h₀ b p.1).2 x))),
     .call k (childOf p.1 p.2),
     .prim k (.elem (.unit (blk d₀ b p.2).1 (blk d₀ b p.2).2 (R - 1) (R - 1))),
     .prim k (.elem (.shift (blk d₀ b p.2).1 (blk d₀ b p.2).2
        (fun x => L.blockVal (blk h₀ b p.1).1 (blk h₀ b p.1).2 x)))]) ++
  (lowerSteps R h₀ b F.E₁).map (.prim k) ++ (lowerSteps R d₀ b F.E₂').map (.prim k)

/-- Number of role streams of the bit network node: `W_b`. -/
noncomputable abbrev Wb : ℕ := Fintype.card (Role .bit 100)

/-- Role indices of the bit network. -/
noncomputable def roleIdxB : Role .bit 100 ≃ Fin Wb := Fintype.equivFin _

/-- A concrete triple, witnessing nonemptiness. -/
def tri012 : Tri 100 := ⟨{0, 1, 2}, by decide⟩

theorem Wb_pos : 0 < Wb := Fintype.card_pos_iff.mpr ⟨Role.X (tri012, tri012, tri012)⟩

/-- `ρ` as a permutation of roles. -/
def rhoEquiv : Equiv.Perm (Role .bit 100) where
  toFun := Role.rho
  invFun := Role.rho
  left_inv w := by cases w <;> rfl
  right_inv w := by cases w <;> rfl

/-- `ρ` on role indices (output role `ρ(w)` is sent back to role `w`). -/
noncomputable def rhoPerm : Equiv.Perm (Fin Wb) := (roleIdxB.symm.trans rhoEquiv).trans roleIdxB

/-- The gate at `(j, ι, r)` as a pointwise map on the aligned role streams. -/
noncomputable def gateOpB {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {Child : Type}
    (j : Stage) (ι : Fix 100) (r : Fin 8) : RoleOp L β Wb Child :=
  .gate (fun vals idx => rowUpd .bit (0 : ZMod 2) j ι (rowOp j r) ((rowSign j r : ℤ) : ZMod 2)
      (fun w => vals (roleIdxB w)) (roleIdxB.symm idx))
    ((Finset.univ.filter fun w : Role .bit 100 => (gateAt j ι r w).isSome).map roleIdxB.toEmbedding)

/-- The Lemma A.6 (`lem:transfer-shear`) shear program of the edge of `w` entering `v` (empty if there is none). -/
noncomputable def edgeOpsB {L : Layout} {β : Type} {Child : Type} (R h₀ d₀ b : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (childOf : Fin mH → Fin mH → Child)
    (w : Role .bit 100) (v : Vertex .bit 100) : List (RoleOp L β Wb Child) :=
  match edgeInto w v with
  | some e => shearOps R h₀ d₀ b (roleIdxB w) (fac (edgeMatFin e)) childOf
  | none => []

/-- The role operations of one bit-network node, in time order (mirrors `framedNet`). -/
noncomputable def bitNodeOps {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    {Child : Type} (R h₀ d₀ b : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (childOf : Fin mH → Fin mH → Child) : List (RoleOp L β Wb Child) :=
  ([Stage.one, .two, .three].flatMap fun j => (Finset.univ : Finset (Fix 100)).toList.flatMap fun ι =>
    (List.finRange 8).flatMap fun r =>
      ((Finset.univ : Finset (Role .bit 100)).toList.flatMap fun w =>
        match gateAt j ι r w with
        | some g => edgeOpsB R h₀ d₀ b fac childOf w (.gate g)
        | none => []) ++ [gateOpB j ι r]) ++
  ((Finset.univ : Finset (Role .bit 100)).toList.flatMap fun w =>
    edgeOpsB R h₀ d₀ b fac childOf w (.sink w)) ++
  [.relabel rhoPerm]

/-- `D_i ← D_i − H_i` for all coordinates (shifts of the later group). -/
def subHSteps {L : Layout} {β : Type} (R h₀ d₀ b : ℕ) : List (Step L β) :=
  (List.finRange mH).map fun i =>
    .elem (.shift (blk d₀ b i).1 (blk d₀ b i).2
      (fun x => R - L.blockVal (blk h₀ b i).1 (blk h₀ b i).2 x % R))

/-- `D_i ← H_i − D_i` for all coordinates (negation, then a shift by `H_i`). -/
def hMinusDSteps {L : Layout} {β : Type} (R h₀ d₀ b : ℕ) : List (Step L β) :=
  (List.finRange mH).flatMap fun i =>
    [.elem (.unit (blk d₀ b i).1 (blk d₀ b i).2 (R - 1) (R - 1)),
     .elem (.shift (blk d₀ b i).1 (blk d₀ b i).2
        (fun x => L.blockVal (blk h₀ b i).1 (blk h₀ b i).2 x))]

/-- Interchange of two digit values as a fixed bijection of a field pair (equal ranges). -/
def finSwapPerm (a b : ℕ) : Equiv.Perm (Fin a × Fin b) :=
  if hab : a = b then
    { toFun := fun p => (Fin.cast hab.symm p.2, Fin.cast hab p.1)
      invFun := fun p => (Fin.cast hab.symm p.2, Fin.cast hab p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  else Equiv.refl _

/-- **The Proposition A.7 (`prop:transfer11`) procedure**: interchange of the chunks of `m^k` digit fields at `h₀` and `d₀`. -/
noncomputable def interchangeProc {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) : (k : ℕ) → ℕ → ℕ → ProcK L β k
  | 0, h₀, d₀ =>
      if hh : h₀ < L.n ∧ d₀ < L.n then
        [.elem (.pair ⟨h₀, hh.1⟩ ⟨d₀, hh.2⟩ (finSwapPerm _ _))]
      else []
  | k + 1, h₀, d₀ =>
      let b := mH ^ k
      let R := q ^ b
      (subHSteps R h₀ d₀ b).map .prim ++
        [.node Wb Wb_pos (bitNodeOps R h₀ d₀ b fac
          (fun i j => interchangeProc q fac k (h₀ + i.val * b) (d₀ + j.val * b)))] ++
        (hMinusDSteps R h₀ d₀ b).map .prim

/-! ## Contracts for Proposition A.7 (`prop:transfer11`) (explicit hypotheses: network facts and Lemma A.6 (`lem:transfer-shear`) facts) -/

/-- The Lemma A.6 (`lem:transfer-shear`) shear facts used by Proposition A.7 (`prop:transfer11`). -/
structure ShearFacts : Prop where
  /-- pivot triple -/
  pivot : PivotTripleEqStmt
  /-- shear factorization -/
  factor : ShearFactorizationStmt
  /-- streaming triangular maps -/
  streaming : LinDLowerTriStreamingStmt
  /-- reduction mod `Q` -/
  ratMod : RatModMatrixMulStmt
  /-- three shears interchange -/
  threeShears : ThreeShearsSwapStmt

/-- Hypotheses on the parameters of `interchangeProc q fac k h₀ d₀` run in class `c`:
an odd prime `q` avoiding all frame denominators; valid factorizations of every edge matrix; both
chunks consist of radix-`q` fields; `H` precedes `D`; the row field precedes both chunks and its range
is divisible by `μ · W_b^k` (complete role streams at every depth, Proposition A.7 (`prop:transfer11`)). -/
def InterchangeHyps (L : Layout) (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ)
    (c : RowClass L) : Prop :=
  q.Prime ∧ q ≠ 2 ∧
  (∀ (v : Vertex .bit 100) (i j : Cube 100), QIntegral q (matB v i j)) ∧
  (∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e)) ∧
  (∀ i : Fin L.n, (h₀ ≤ i.val ∧ i.val < h₀ + mH ^ k) ∨ (d₀ ≤ i.val ∧ i.val < d₀ + mH ^ k) →
    L.r i = q) ∧
  h₀ + mH ^ k ≤ d₀ ∧ d₀ + mH ^ k ≤ L.n ∧ c.row.val < h₀ ∧ c.μ * Wb ^ k ∣ L.r c.row

/-- CONTRACT (Proposition A.7 (`prop:transfer11`) correctness). Under the network
facts and the Lemma A.6 (`lem:transfer-shear`) shear facts, `interchangeProc q fac k h₀ d₀`, run in class `c`, interchanges the two chunks
of `m^k` digit fields (exactly the address permutation `swapBlocks h₀ d₀ (m^k)` on `c`, any payload
`β` that is an `𝔽₂`-module, arbitrary data). -/
def InterchangeProcCorrectStmt : Prop :=
  BitNetCert → ShearFacts →
  ∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ) (c : RowClass L),
    InterchangeHyps L q fac k h₀ d₀ c → ∀ A : L.Addr → β,
      ProcK.run k (interchangeProc (L := L) (β := β) q fac k h₀ d₀) c A =
        (Step.swapBlocks h₀ d₀ (mH ^ k) : Step L β).runIn c A

/-- CONTRACT (Proposition A.7 (`prop:transfer11`) well-formedness, model level). Every primitive of `interchangeProc` satisfies its
side condition (`ProcK.WF`, radix bound `q`): pair steps act on two distinct fields of range `≤ q`,
shift offsets read only fields before their target block, units are invertible modulo the block range,
gates read and change only their `touched` roles, recursively in the children. This is a side condition
of the abstract model only, not a machine-time bound (all machine step bounds are proved in `SubNLogN/Machine/`). -/
def InterchangeProcWFStmt : Prop :=
  ∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ) (c : RowClass L),
    InterchangeHyps L q fac k h₀ d₀ c →
      ProcK.WF q k (interchangeProc (L := L) (β := β) q fac k h₀ d₀)

/-- CONTRACT (Proposition A.7 (`prop:transfer11`) cost; **nominal model cost**: `ProcK.cost` is a
nominal model cost and no theorem here bounds TM2 time). With `τ = 1 − 2^{-40}` (`DeficitsH100Stmt`):
there is `C` (depending only on `c₀`) such that the abstract cost of `interchangeProc` in a class `c`
(volume `c.vol P = card·w/μ`) is at most `C · c.vol P · (m^k)^τ`, i.e. `O(V e^τ)` for chunks of `e = m^k` digits. The node
recurrence is `T_{k+1}(vol) ≤ c'·vol + s_b · T_k(vol / W_b)`. Dependencies, all explicit:
`#children = Σ_e (edgeMatFin e).rank` (`FacData.Valid`: `piv.length = rank`), which equals
`Σ_e rankQ (edgeMatB e) = tripleSb 100` (`BitNetCert.rank_sum`; rank is invariant under `reindex` and
`LinearMap.toMatrix'`, a Mathlib-level lemma); `W_b = tripleWb 100` (`BitNetCert.card_roles`);
`s_b/W_b < m^τ` (`DeficitsH100Stmt`); the recurrence solution (`InterchangeRecurrenceStmt`). -/
def InterchangeProcCostStmt : Prop :=
  BitNetCert → DeficitsH100Stmt → InterchangeRecurrenceStmt →
  ∀ P : CostParams, 0 ≤ P.c₀ →
    ∃ C : ℝ, ∀ (L : Layout) (β : Type) [AddCommGroup β] [Module (ZMod 2) β]
      (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ) (c : RowClass L),
      InterchangeHyps L q fac k h₀ d₀ c → 0 ≤ P.w →
        ProcK.cost P k (interchangeProc (L := L) (β := β) q fac k h₀ d₀) c ≤
          C * c.vol P * ((mH ^ k : ℕ) : ℝ) ^ ((1 : ℝ) - (2 : ℝ)⁻¹ ^ 40)

end SubNLogN.Math.Networks
