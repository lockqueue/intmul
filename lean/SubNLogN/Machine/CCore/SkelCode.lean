/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs

/-!
# C-core skeleton: the fixed node code and its value semantics (`CCore/SkelCode.lean`)

* `MOp`: the machine operations of a node (phase, Lemma A.9 row addition, child call, scalar row).
* `nodeCode cdat`: the fixed node code. It mirrors the value-level `cxNodeOps` (`Math/Networks/AppCCore.lean`)
  constructor by constructor, with the final relabel fused into `collect collectPerm`.
* `mopVal t o`: the value-level effect of one machine operation on the vector of compact role
  arrays. These are the effects promised by the leaf kernels of `SkelDefs.lean`; a child call has
  the effect `childVal` (`cCoreVal` at the child context).
* `nodeVal t cdat w₀`: the fold of `mopVal` over `nodeCode cdat`.

The value-level correctness of the node code (`NodeValueStmt`), the numerical invariant
(`NodeGrowthStmt`) and the inheritance of the bands (`ChildBandsStmt`) are stated in
`CCore/SkelMathDefs.lean` as named statements, not proved here.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks

/-- The network parameter `mH` equals `m`. -/
theorem mH_eq_mn : mH = mn := by norm_num [mH, mn, tripleM]

/-- A slot index of the edge data as a static slot (`t % m`; for valid edge data `t < m`). -/
def slotOf (t : ℕ) : Fin mn := ⟨t % mn, Nat.mod_lt _ (by norm_num [mn, tripleM])⟩

/-- Machine operations of the fixed node code. -/
inductive MOp where
  /-- a phase kernel on role `u` -/
  | phase (u : Fin Wn) (κ : PhaseKind)
  /-- a Lemma A.9 row addition on role `u`, slot `p₁ ← p₁ + p₂` -/
  | rowAdd (u : Fin Wn) (p₁ p₂ : Fin mn)
  /-- a child call on role `u`, slot `a` -/
  | child (u : Fin Wn) (a : Fin mn)
  /-- the scalar row `(j, ι, r)` on the aligned role streams -/
  | gate (j : Stage) (ι : Fix 100) (r : Fin 8)

/-- The machine code of an edge operator on role `u` (`coreEdgeOps`). -/
def edgeCode (Dd : CxEdgeData) (u : Fin Wn) : List MOp :=
  Dd.rowsInv.map (fun p => MOp.rowAdd u (Fin.cast mH_eq_mn p.1) (Fin.cast mH_eq_mn p.2)) ++
  ((List.range Dd.basis.length).zip Dd.eps).flatMap (fun p =>
    if p.2 = 1 then [MOp.child u (slotOf p.1)]
    else [MOp.phase u (.zSlot (slotOf p.1)), MOp.child u (slotOf p.1),
      MOp.phase u (.zSlot (slotOf p.1)), MOp.phase u .negIPow]) ++
  Dd.rowsM.map (fun p => MOp.rowAdd u (Fin.cast mH_eq_mn p.1) (Fin.cast mH_eq_mn p.2))

/-- The edge operations of wire `w` entering vertex `v` (`coreEdgeOpsAt`). -/
noncomputable def edgeCodeAt (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (w : Role .complex 100) (v : Vertex .complex 100) : List MOp :=
  match edgeInto w v with
  | some e => edgeCode (cdat e) (roleIdxN w)
  | none => []

/-- **The fixed node code** (`cxNodeOps` without the final relabel). -/
noncomputable def nodeCode (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) :
    List MOp :=
  ((Finset.univ : Finset (Addr 100)).toList.map fun a =>
    MOp.phase (roleIdxN (.X a)) (.zMask a)) ++
  ([Stage.one, .two, .three].flatMap fun j => (Finset.univ : Finset (Fix 100)).toList.flatMap
    fun ι => (List.finRange 8).flatMap fun r =>
      ((Finset.univ : Finset (Role .complex 100)).toList.flatMap fun w =>
        match gateAt j ι r w with
        | some g => edgeCodeAt cdat w (.gate g)
        | none => []) ++ [MOp.gate j ι r]) ++
  ((Finset.univ : Finset (Role .complex 100)).toList.flatMap fun w =>
    edgeCodeAt cdat w (.sink w)) ++
  ((Finset.univ : Finset (Addr 100)).toList.flatMap fun a =>
    [MOp.phase (roleIdxN (.Y a)) (.zMask a), MOp.phase (roleIdxN (.Y a)) .iPow27,
      MOp.phase (roleIdxN (.X a)) .neg])

/-- The physical-to-class permutation of `collect` (the final relabel by `ρ`). Class `u` is
read from physical role `collectPerm u`. -/
noncomputable def collectPerm : Equiv.Perm (Fin Wn) :=
  ((roleIdxN.symm.trans rhoEquivC).trans roleIdxN).symm

/-- The child's value effect on role array `w`: `cCoreVal` on the child's group (slot `a`,
`f = m^(t.k - 1)` chunks). Outside the valid range it is the identity. -/
noncomputable def childVal (t : CCoreRT) (a : Fin mn)
    (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r :=
  if h : t.ρ < t.K ∧ t.j0 + a.val * mn ^ (t.k - 1) + mn ^ (t.k - 1) ≤ t.D then
    cCoreVal ⟨t.ρ, h.1⟩ (t.j0 + a.val * mn ^ (t.k - 1)) (mn ^ (t.k - 1)) h.2 w
  else w

/-- Value-level effect of one machine operation on the compact role arrays. -/
noncomputable def mopVal (t : CCoreRT) :
    MOp → (Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) →
      (Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r)
  | .phase u κ, w => Function.update w u (runSteps [phaseStep t κ] (w u))
  | .rowAdd u p₁ p₂, w => Function.update w u (runSteps (rowAddSteps t p₁ p₂) (w u))
  | .child u a, w => Function.update w u (childVal t a (w u))
  | .gate j ι r, w => gateVal j ι r w

/-- Value-level effect of a list of machine operations. -/
noncomputable def mopsVal (t : CCoreRT) (ops : List MOp)
    (w : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) :
    Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r :=
  ops.foldl (fun w o => mopVal t o w) w

end SubNLogN.Machine.CCore
