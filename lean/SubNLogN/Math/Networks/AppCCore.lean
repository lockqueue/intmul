import SubNLogN.Math.Networks.LayerCore
import SubNLogN.Math.Networks.AppCPacked
import SubNLogN.Math.Networks.AppCProc

/-!
# Appendix A procedures (III): the exact recursive complex core (Lemma A.10 (`lem:transfer-phase`)) as an explicit procedure

Lemma A.10 (`lem:transfer-phase`) and Proposition A.11 (`prop:prop14-param`), Appendix A.5–A.6.
`cCoreProc A K D S rr ρ kLeaf cdat k j0 : ProcK (layerLayout A K D S) (Fin rr → ℂ) k` computes
`C^{⊗e}`, `e = m^k`, on the selected bit `ρ` of the chunks `j0, …, j0+e−1` of a layer array, run in a
class of the prefix field (field `0`):
* leaves (`k < kLeaf`, i.e. `e < d^β`; depth `0` always): `e` individual kernels (`digitGate`);
* internal nodes: one complex-network node with `W_c` role streams. In time order: the source masks
  `Z_{a,f}` on the `X` roles; then, before every gate, the incoming edge of each touched wire as
  `P_M⁻¹` (Lemma A.9 (`lem:transfer13`) row additions between slots), one child `C^{⊗f}` per residual basis vector (wrapped as
  `(−i)^f Z^{⊗f} C^{⊗f} Z^{⊗f}` for inverse kernels), `P_M`; then the gate (the complex scalar row);
  finally the sink edges, the sink corrections `i^{27f} Z_{a,f}` on `Y_a` and `−1` on `X_a`, and the
  role relabelling `ρ`.
Slots are the `m` groups of `f = m^{k−1}` consecutive chunks (slot `t` ↔ coordinate
`cubeEquiv.symm t` of `𝔽₂^m`); columns are the chunk positions inside a slot. The edge data
(`CxEdgeData`: residual ONB with signs, row-addition words for `P_M^{±1}`) is a parameter; its validity
is a hypothesis of the contracts.
-/

namespace SubNLogN.Math.Networks

open Model SubNLogN.Math.Walsh

/-- Number of role streams of the complex network node: `W_c`. -/
noncomputable abbrev Wc : ℕ := Fintype.card (Role .complex 100)

/-- Role indices of the complex network. -/
noncomputable def roleIdxC : Role .complex 100 ≃ Fin Wc := Fintype.equivFin _

theorem Wc_pos : 0 < Wc := Fintype.card_pos_iff.mpr ⟨Role.X (tri012, tri012, tri012)⟩

/-- `ρ` on complex roles. -/
def rhoEquivC : Equiv.Perm (Role .complex 100) where
  toFun := Role.rho
  invFun := Role.rho
  left_inv w := by cases w <;> rfl
  right_inv w := by cases w <;> rfl

/-- `ρ` on complex role indices. -/
noncomputable def rhoPermC : Equiv.Perm (Fin Wc) := (roleIdxC.symm.trans rhoEquivC).trans roleIdxC

/-- Field of bit `ρ` of chunk `j` in `layerLayout`. -/
def selField (K ρ j : ℕ) : ℕ := 1 + j * K + (K - 1 - ρ)

/-- The individual kernel on a binary field: `C(u, v) = (a u + b v, b u + a v)`. -/
noncomputable def cGate {n rr : ℕ} (v : Fin n → (Fin rr → ℂ)) (t : Fin n) : Fin rr → ℂ :=
  ka • v t + kb • ∑ t' ∈ Finset.univ.erase t, v t'

/-- One individual kernel on the selected-bit field `i` (empty if out of range). -/
noncomputable def dgate {A K D S rr : ℕ} (i : ℕ) : List (Step (layerLayout A K D S) (Fin rr → ℂ)) :=
  if h : i < (layerLayout A K D S).n then [.digitGate ⟨i, h⟩ cGate] else []

/-- Selected bit of chunk `c` of slot `t` (slot = `f` chunks from chunk `j0 + t f`). -/
def slotBit {A K D S : ℕ} (K' ρ f j0 t c : ℕ) (x : (layerLayout A K D S).Addr) : ℕ :=
  (layerLayout A K D S).blockVal (selField K' ρ (j0 + t * f + c)) (selField K' ρ (j0 + t * f + c) + 1) x

/-- `Z^{⊗f}` on the selected bits of slot `t`: sign `(−1)^{Σ_c x_{t,c}}`. -/
noncomputable def zSlot {A K D S rr : ℕ} (ρ f j0 t : ℕ) : Step (layerLayout A K D S) (Fin rr → ℂ) :=
  .addrMap fun x v => ((-1 : ℂ) ^ (∑ c ∈ Finset.range f, slotBit (A := A) (D := D) (S := S) K ρ f j0 t c x)) • v

/-- `Z_{a,f}`: `Z` on the coordinates of `supp u_a` in each of the `f` columns. -/
noncomputable def zMask {A K D S rr : ℕ} (ρ f j0 : ℕ) (a : Addr 100) :
    Step (layerLayout A K D S) (Fin rr → ℂ) :=
  .addrMap fun x v => ((-1 : ℂ) ^ (∑ c ∈ Finset.range f, ∑ p : Cube 100,
    (ua a p).val * slotBit (A := A) (D := D) (S := S) K ρ f j0 (cubeEquiv p) c x)) • v

/-- Data of one complex-network edge: an orthonormal residual basis with its kernel signs, and
row-addition words (time order, pairs `(i, j)` meaning slot `i ← slot i + slot j`) realizing `P_M⁻¹`
and `P_M` for a basis extension `M`. -/
structure CxEdgeData where
  /-- orthonormal basis of the residual -/
  basis : List (Pt 100)
  /-- kernel signs -/
  eps : List ℤ
  /-- row additions realizing `P_M⁻¹` -/
  rowsInv : List (Fin mH × Fin mH)
  /-- row additions realizing `P_M` -/
  rowsM : List (Fin mH × Fin mH)

/-- The binary move of a row-addition word (applied in time order). -/
def rowsMove (l : List (Fin mH × Fin mH)) (x : Pt 100) : Pt 100 :=
  l.foldl (fun x p => Function.update x (cubeEquiv.symm p.1)
    (x (cubeEquiv.symm p.1) + x (cubeEquiv.symm p.2))) x

/-- Validity of edge data (Lemma A.10 (`lem:transfer-phase`)): an orthonormal basis of the residual,
its signs `epsC`, and row-addition words (distinct slots, at most `m(m−1)+3m` each) realizing `x ↦ Mx`
and `x ↦ M⁻¹x` for an invertible `M` whose first columns are the basis vectors. -/
def CxEdgeData.Valid (e : Vertex .complex 100 × Vertex .complex 100) (Dd : CxEdgeData) : Prop :=
  IsONB (residC e) Dd.basis ∧ Dd.eps = Dd.basis.map (epsC e) ∧
  (∀ p ∈ Dd.rowsInv ++ Dd.rowsM, p.1 ≠ p.2) ∧
  Dd.rowsInv.length ≤ mH * (mH - 1) + 3 * mH ∧ Dd.rowsM.length ≤ mH * (mH - 1) + 3 * mH ∧
  ∃ M M' : Matrix (Cube 100) (Cube 100) (ZMod 2), M * M' = 1 ∧
    (∀ (t : ℕ) (ht : t < Dd.basis.length) (htm : t < mH), ∀ p,
      M p (cubeEquiv.symm ⟨t, htm⟩) = Dd.basis.get ⟨t, ht⟩ p) ∧
    (∀ x, rowsMove Dd.rowsM x = M.mulVec x) ∧ (∀ x, rowsMove Dd.rowsInv x = M'.mulVec x)

/-- A third slot different from `i` and `j` (the restored auxiliary chunk of Lemma A.9 (`lem:transfer13`)). -/
def thirdSlot (i j : ℕ) : ℕ := if i ≠ 0 ∧ j ≠ 0 then 0 else if i ≠ 1 ∧ j ≠ 1 then 1 else 2

/-- The edge operator `P_M (Π_t K_{e_t}^{ε_t}) P_M⁻¹` on one role stream (Lemma A.10 (`lem:transfer-phase`)). -/
noncomputable def coreEdgeOps {A K D S rr : ℕ} {Child : Type} (ρ f j0 : ℕ) (Dd : CxEdgeData)
    (childOf : ℕ → Child) (k : Fin Wc) : List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child) :=
  let slotPos : ℕ → ℕ := fun t => 1 + (j0 + t * f) * K
  let rowAdd : Fin mH × Fin mH → List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child) :=
    fun p => (packedAddProc (Ly := layerLayout A K D S) (β := Fin rr → ℂ) (f * K) K ρ f
      ⟨slotPos p.2.val, slotPos p.1.val, slotPos (thirdSlot p.1.val p.2.val)⟩ :
        List (Step (layerLayout A K D S) (Fin rr → ℂ))).map (.prim k)
  let kern : ℕ × ℤ → List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child) := fun p =>
    if p.2 = 1 then [.call k (childOf p.1)]
    else [.prim k (zSlot ρ f j0 p.1), .call k (childOf p.1), .prim k (zSlot ρ f j0 p.1),
      .prim k (.recMap fun v => ((-Complex.I) ^ f) • v)]
  Dd.rowsInv.flatMap rowAdd ++ ((List.range Dd.basis.length).zip Dd.eps).flatMap kern ++
    Dd.rowsM.flatMap rowAdd

/-- The gate at `(j, ι, r)`: the complex scalar row on the aligned role streams. -/
noncomputable def gateOpC {A K D S rr : ℕ} {Child : Type} (j : Stage) (ι : Fix 100) (r : Fin 8) :
    RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child :=
  .gate (fun vals idx => rowUpd .complex (2⁻¹ : ℂ) j ι (rowOp j r) ((rowSign j r : ℤ) : ℂ)
      (fun w => vals (roleIdxC w)) (roleIdxC.symm idx))
    ((Finset.univ.filter fun w : Role .complex 100 => (gateAt j ι r w).isSome).map roleIdxC.toEmbedding)

/-- The edge operations of wire `w` entering vertex `v` (empty if there is no such edge). -/
noncomputable def coreEdgeOpsAt {A K D S rr : ℕ} {Child : Type} (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (childOf : ℕ → Child)
    (w : Role .complex 100) (v : Vertex .complex 100) :
    List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child) :=
  match edgeInto w v with
  | some e => coreEdgeOps ρ f j0 (cdat e) childOf (roleIdxC w)
  | none => []

/-- The role operations of one complex-network node, in time order. -/
noncomputable def cxNodeOps {A K D S rr : ℕ} {Child : Type} (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (childOf : ℕ → Child) :
    List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child) :=
  ((Finset.univ : Finset (Addr 100)).toList.map fun a => .prim (roleIdxC (.X a)) (zMask ρ f j0 a)) ++
  ([Stage.one, .two, .three].flatMap fun j => (Finset.univ : Finset (Fix 100)).toList.flatMap fun ι =>
    (List.finRange 8).flatMap fun r =>
      ((Finset.univ : Finset (Role .complex 100)).toList.flatMap fun w =>
        match gateAt j ι r w with
        | some g => coreEdgeOpsAt ρ f j0 cdat childOf w (.gate g)
        | none => []) ++ [gateOpC j ι r]) ++
  ((Finset.univ : Finset (Role .complex 100)).toList.flatMap fun w =>
    coreEdgeOpsAt ρ f j0 cdat childOf w (.sink w)) ++
  ((Finset.univ : Finset (Addr 100)).toList.flatMap fun a =>
    [.prim (roleIdxC (.Y a)) (zMask ρ f j0 a),
     .prim (roleIdxC (.Y a)) (.recMap fun v => (Complex.I ^ (27 * f)) • v),
     .prim (roleIdxC (.X a)) (.recMap fun v => (-1 : ℂ) • v)]) ++
  [.relabel rhoPermC]

/-- **The Lemma A.10 (`lem:transfer-phase`) core procedure**: `C^{⊗(m^k)}` on the selected bit `ρ` of the chunks from `j0`. -/
noncomputable def cCoreProc (A K D S rr ρ kLeaf : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) :
    (k : ℕ) → ℕ → ProcK (layerLayout A K D S) (Fin rr → ℂ) k
  | 0, j0 => dgate (selField K ρ j0)
  | k + 1, j0 =>
      if k + 1 < kLeaf then
        (List.range (mH ^ (k + 1))).flatMap fun t => (dgate (selField K ρ (j0 + t))).map .prim
      else
        [.node Wc Wc_pos (cxNodeOps ρ (mH ^ k) j0 cdat
          (fun t => cCoreProc A K D S rr ρ kLeaf cdat k (j0 + t * mH ^ k)))]

/-! ## Contracts for Lemma A.10 (`lem:transfer-phase`) (explicit hypotheses: `ComplexNetCert`, Lemma A.9 (`lem:transfer13`) statements) -/

/-- The `κ = 2^{-46}` row exponents (Table 6 (`tab:walsh-rows`), Section 7.5 (`sec:main-rows`), `ξ = 2^{-42}`): `τ = 1−4ξ`. -/
noncomputable def tau46 : ℝ := 1 - 4 * xi46
/-- `σ = 1 − ξ`. -/
noncomputable def sigma46 : ℝ := 1 - xi46
/-- `β = 1/64`. -/
noncomputable def beta46 : ℝ := 1 / 64
/-- `c = ξ/256`. -/
noncomputable def c46 : ℝ := xi46 / 256
/-- `λ = 1 − 63ξ/64`. -/
noncomputable def lam46 : ℝ := 1 - 63 * xi46 / 64
/-- `λ' = 1 − 31ξ/32`. -/
noncomputable def lam46' : ℝ := 1 - 31 * xi46 / 32

/-- Hypotheses (`CCoreHyps A K D S ρ cdat k j0 c`) on `cCoreProc A K D S rr ρ kLeaf cdat k j0` run
in class `c` (no condition on `rr` or `kLeaf` is needed): `K ≥ 6` (Lemma A.9 (`lem:transfer13`)), `ρ < K`,
the piece of `m^k` chunks lies in the chunk range, `c` is a prefix class (row field `0`) whose role
splits are complete down to depth `k` (`μ · W_c^k ∣ A`), and all edge data are valid. -/
def CCoreHyps (A K D S ρ : ℕ) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (k j0 : ℕ) (c : RowClass (layerLayout A K D S)) : Prop :=
  6 ≤ K ∧ ρ < K ∧ j0 + mH ^ k ≤ D ∧ c.row.val = 0 ∧ c.μ * Wc ^ k ∣ A ∧
    ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e

/-- CONTRACT (Lemma A.10 (`lem:transfer-phase`) exactness).
For **every** array (no disk or grid condition: exact algebra), `cCoreProc … k j0` run in class `c`
computes exactly `C^{⊗(m^k)}` on the selected bit `ρ` of the chunks `j0, …, j0+m^k−1` of the
addresses in `c` (`cCoreVal`), leaving the other addresses unchanged. -/
def CCoreProcCorrectStmt : Prop :=
  ComplexNetCert → RunEightSpecStmt → PackedAgreeStmt → PackedProcCorrectStmt → TranslationConjStmt →
  ∀ (A K D S rr kLeaf : ℕ) (ρ : Fin K) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (k j0 : ℕ) (c : RowClass (layerLayout A K D S)) (h : j0 + mH ^ k ≤ D),
    CCoreHyps A K D S ρ.val cdat k j0 c → ∀ z : RArr (LayerAddr A K D S) rr,
      decodeArr (ProcK.run k (cCoreProc A K D S rr ρ.val kLeaf cdat k j0) c (encodeArr z)) =
        fun x => if c.mem (encodeAddr x) then cCoreVal ρ j0 (mH ^ k) h z x else z x

/-- CONTRACT (Lemma A.10 (`lem:transfer-phase`) well-formedness, radix bound 2): every primitive satisfies its side condition. -/
def CCoreProcWFStmt : Prop :=
  ComplexNetCert → PackedAgreeStmt →
  ∀ (A K D S rr ρ kLeaf : ℕ) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (k j0 : ℕ) (c : RowClass (layerLayout A K D S)), CCoreHyps A K D S ρ cdat k j0 c →
      ProcK.WF 2 k (cCoreProc A K D S rr ρ kLeaf cdat k j0)

/-- CONTRACT (existence of valid complex edge data; [OAI26] Lemma 6 ONB, basis extension, row additions). -/
def ExistsValidCxDataStmt : Prop :=
  ∃ cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData,
    ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e

end SubNLogN.Math.Networks
