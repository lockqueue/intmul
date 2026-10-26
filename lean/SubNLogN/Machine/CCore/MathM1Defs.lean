/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelMathDefs
import SubNLogN.Math.Networks.Proofs.CCoreRole
import SubNLogN.Math.Networks.AppCLayerProc

/-!
# M1 interface: ideal children and the node-code transport (`CCore/MathM1Defs.lean`)

Shared definitions for the proof of `NodeValueStmt` (M1, `CCore/SkelMathDefs.lean`).

* `crunI t hρ`: the **ideal child semantics** at a node of context `t` (`f = m^(t.k-1)` columns per
  slot). Child `s`, run in a class `c'` of the full layout `layerLayout t.A t.K t.D t.S`, applies
  `cCoreVal` on the selected bit `t.ρ` of slot `s` (chunks `t.j0 + s·f, …, t.j0 + s·f + f - 1`) to
  the addresses of `c'` and leaves the other addresses unchanged. If the slot does not fit below
  `t.D`, the child is the identity. This satisfies `ChildSpecC` by construction.
* `NodeTransportStmt cdat`: the op-by-op transport from the value-level run of
  `cxNodeOps` (top class, ideal children `crunI`, child names `id`) on the full layout to the
  skeleton's `mopsVal t (nodeCode cdat)` on the compact role arrays (`restrictRole`), with the
  final relabel `rhoPermC` read through `collectPerm`.
* M1 is assembled in `CCore/MathM1.lean` from `NodeTransportStmt`, the Lemma A.10 (`lem:transfer-phase`)
  lemma `cxNode_correct_holds`, `coreEdgeRoleSpec_holds` and `serialEqFramed_holds`.

Nothing is proved here.
-/

namespace SubNLogN.Machine.CCore

open SubNLogN.Math.Networks SubNLogN.Math.Networks.Model

/-- **Ideal child semantics** at a node of context `t` (`f = m^(t.k-1)`): child `s` run in the class
`c'` applies `cCoreVal` on slot `s` to the addresses of `c'`; the identity if the slot does not fit. -/
noncomputable def crunI (t : CCoreRT) (hρ : t.ρ < t.K) (s : ℕ)
    (c' : RowClass (layerLayout t.A t.K t.D t.S))
    (Z : (layerLayout t.A t.K t.D t.S).Addr → (Fin t.r → ℂ)) :
    (layerLayout t.A t.K t.D t.S).Addr → (Fin t.r → ℂ) :=
  if hs : t.j0 + s * mn ^ (t.k - 1) + mn ^ (t.k - 1) ≤ t.D then
    encodeArr (fun x => if c'.mem (encodeAddr x) then
      cCoreVal ⟨t.ρ, hρ⟩ (t.j0 + s * mn ^ (t.k - 1)) (mn ^ (t.k - 1)) hs (decodeArr Z) x
      else decodeArr Z x)
  else Z

/-- **(M1a) Node-code transport.** At an internal node of context `t` (in the
hypotheses of M1), the value-level run of `cxNodeOps` with `f = m^(t.k-1)` in the top class of the full layout,
with the ideal children `crunI t hρ` (child names `id`), restricted to row class `u`, equals the
skeleton's node code run on the compact role arrays, read at physical role `collectPerm u`. -/
def NodeTransportStmt (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) : Prop :=
  ComplexNetCert → RunEightSpecStmt → PackedAgreeStmt → PackedProcCorrectStmt → ValidCdat cdat →
  ∀ (t : CCoreRT) (hρ : t.ρ < t.K), t.j0 + t.e ≤ t.D → 1 ≤ t.k → 6 ≤ t.K → Wn ^ t.k ∣ t.A →
    ∀ (Z : (layerLayout t.A t.K t.D t.S).Addr → (Fin t.r → ℂ)) (u : Fin Wn),
      restrictRole t u (decodeArr (CCoreNode.runOps (crunI t hρ) (topClass t.A t.K t.D t.S)
        (cxNodeOps (A := t.A) (K := t.K) (D := t.D) (S := t.S) (rr := t.r) t.ρ (mn ^ (t.k - 1))
          t.j0 cdat id) Z)) =
      mopsVal t (nodeCode cdat) (fun u' => restrictRole t u' (decodeArr Z)) (collectPerm u)

end SubNLogN.Machine.CCore
