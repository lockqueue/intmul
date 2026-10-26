/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelCore

/-!
# C-core skeleton: the node run (`CCore/SkelNode.lean`)

* `NodeSpecs`: the big-layout `SafeRunsIn` facts of the node kernels (split, collect, phase, Lemma A.9
  row addition, scalar row, and the child-protocol kernels), with explicit cost constants. These
  are the leaf statements of `SkelDefs.lean` transported to the big layout `CL E`
  (`SkelLayout.lean`).
* `nodeOpCost`: the cost charged to one machine operation. A child operation is charged the two
  transfers, the two header kernels, and `Tc + 2` for the recursive call.
* `NodeRunStmt`: the node run. From the entry state of a non-leaf call, the node branch
  `split ; nodeCode ; collect` reaches `io = Enc t z' ++ tio`, with every other stack restored.
  Here `z'` is any array whose role streams are the result of the node code. The hypotheses are:
  the growth requirements `opReq` of every operation (explicit; `NodeGrowthStmt` supplies them);
  a child oracle `IHk` for `recur 0`, with arbitrary framed content (frame tails); and bounds on
  the encoding and header lengths.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks

variable {E σ : Type} [DecidableEq E]

/-- Big-layout specifications of the node kernels of `L`, with cost constants. `Erow` is the
arithmetic depth of each scalar row. -/
structure NodeSpecs (p : LayerParams) (P₀ : ℕ) (L : CoreProgs E σ)
    (Erow : Stage × Fix 100 × Fin 8 → ℕ) (cS cC cPh cRA cG cR2I cPush cDrop cI2R : ℕ) : Prop where
  split : ∀ (ρ : List (Prog (CL E) (fun _ => Sym) σ)) (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (hA' : 0 < t.A / Wn) (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (tio tdesc : List Sym)
    (S : CL E → List Sym),
    CCoreBands p P₀ t → Wn ∣ t.A → KClean S → BlkTerm tio →
    S ioL = Enc t hA hS z ++ tio → S descL = t.hdr ++ tdesc → (∀ u, S (roleL u) = []) →
    Calculus.SafeRunsIn ccoreFramed ρ L.split S
      (setRoles (Function.update S ioL tio)
        (fun u => Enc (compactRT t) hA' hS (restrictRole t u z) ++ [Sym.mark]))
      (fun _ => True) (cS * t.volG)
  coll : ∀ (ρ : List (Prog (CL E) (fun _ => Sym) σ)) (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (hA' : 0 < t.A / Wn) (z' : RArr (LayerAddr t.A t.K t.D t.S) t.r) (tio tdesc : List Sym)
    (S : CL E → List Sym),
    CCoreBands p P₀ t → Wn ∣ t.A → KClean S → BlkTerm tio → S ioL = tio →
    S descL = t.hdr ++ tdesc →
    (∀ u, S (roleL (collectPerm u)) =
      Enc (compactRT t) hA' hS (restrictRole t u z') ++ [Sym.mark]) →
    Calculus.SafeRunsIn ccoreFramed ρ L.coll S
      (setRoles (Function.update S ioL (Enc t hA hS z' ++ tio)) (fun _ => []))
      (fun _ => True) (cC * t.volG)
  phase : ∀ (u : Fin Wn) (κ : PhaseKind) (ρ : List (Prog (CL E) (fun _ => Sym) σ)) (t : CCoreRT)
    (hA' : 0 < t.A / Wn) (hS : 0 < t.S) (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r)
    (b : ℕ) (tdesc : List Sym) (S : CL E → List Sym),
    CCoreBands p P₀ t → 1 ≤ t.k → ArrGrowth t.P b w → b ≤ t.Δ → KClean S →
    S descL = t.hdr ++ tdesc → S (roleL u) = Enc (compactRT t) hA' hS w ++ [Sym.mark] →
    Calculus.SafeRunsIn ccoreFramed ρ (L.phase u κ) S
      (Function.update S (roleL u)
        (Enc (compactRT t) hA' hS (runSteps [phaseStep t κ] w) ++ [Sym.mark]))
      (fun _ => True) (cPh * t.volG)
  rowAdd : ∀ (u : Fin Wn) (p₁ p₂ : Fin mn) (ρ : List (Prog (CL E) (fun _ => Sym) σ))
    (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
    (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) (tdesc : List Sym) (S : CL E → List Sym),
    CCoreBands p P₀ t → 1 ≤ t.k → 6 ≤ t.K → p₁ ≠ p₂ → KClean S → S descL = t.hdr ++ tdesc →
    S (roleL u) = Enc (compactRT t) hA' hS w ++ [Sym.mark] →
    Calculus.SafeRunsIn ccoreFramed ρ (L.rowAdd u p₁ p₂) S
      (Function.update S (roleL u)
        (Enc (compactRT t) hA' hS (runSteps (rowAddSteps t p₁ p₂) w) ++ [Sym.mark]))
      (fun _ => True) (cRA * (t.volG * (Utau p.τ (t.e * t.K) + 1)))
  gate : ∀ (j : Stage) (ι : Fix 100) (r : Fin 8) (ρ : List (Prog (CL E) (fun _ => Sym) σ))
    (t : CCoreRT) (hA' : 0 < t.A / Wn) (hS : 0 < t.S)
    (w : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) (b : ℕ) (tdesc : List Sym)
    (S : CL E → List Sym),
    CCoreBands p P₀ t → (∀ u, ArrGrowth t.P b (w u)) → b + Erow (j, ι, r) ≤ t.Δ → KClean S →
    S descL = t.hdr ++ tdesc →
    (∀ u, S (roleL u) = Enc (compactRT t) hA' hS (w u) ++ [Sym.mark]) →
    Calculus.SafeRunsIn ccoreFramed ρ (L.gate j ι r) S
      (setRoles S (fun u => Enc (compactRT t) hA' hS (gateVal j ι r w u) ++ [Sym.mark]))
      (fun _ => True) (cG * t.volG)
  r2i : ∀ (u : Fin Wn) (ρ : List (Prog (CL E) (fun _ => Sym) σ)) (v : List (List Bool))
    (tio : List Sym) (S : CL E → List Sym),
    KClean S → S (roleL u) = arrSyms v ++ [Sym.mark] → S ioL = tio →
    Calculus.SafeRunsIn ccoreFramed ρ (L.r2i u) S
      (Function.update (Function.update S (roleL u) [Sym.mark]) ioL (arrSyms v ++ tio))
      (fun _ => True) (cR2I * ((arrSyms v).length + 1))
  push : ∀ (a : Fin mn) (ρ : List (Prog (CL E) (fun _ => Sym) σ)) (t : CCoreRT)
    (tdesc : List Sym) (S : CL E → List Sym),
    CCoreBands p P₀ t → 1 ≤ t.k → KClean S → S descL = t.hdr ++ tdesc →
    Calculus.SafeRunsIn ccoreFramed ρ (L.push a) S
      (Function.update S descL (childHdr t a ++ (t.hdr ++ tdesc))) (fun _ => True)
      (cPush * t.volG)
  drop : ∀ (ρ : List (Prog (CL E) (fun _ => Sym) σ)) (fs : List ℕ) (rest : List Sym)
    (S : CL E → List Sym),
    fs.length = 12 → KClean S → S descL = hdrSyms fs ++ rest →
    Calculus.SafeRunsIn ccoreFramed ρ L.drop S (Function.update S descL rest) (fun _ => True)
      (cDrop * ((hdrSyms fs).length + 1))
  i2r : ∀ (u : Fin Wn) (ρ : List (Prog (CL E) (fun _ => Sym) σ)) (v : List (List Bool))
    (tio : List Sym) (S : CL E → List Sym),
    KClean S → BlkTerm tio → S ioL = arrSyms v ++ tio → S (roleL u) = [Sym.mark] →
    Calculus.SafeRunsIn ccoreFramed ρ (L.i2r u) S
      (Function.update (Function.update S ioL tio) (roleL u) (arrSyms v ++ [Sym.mark]))
      (fun _ => True) (cI2R * ((arrSyms v).length + 1))

/-- The cost charged to one machine operation of the node code at context `t` (volume `V`):
`Lenc` bounds the encoding lengths plus one, `Lhdr` the child header lengths plus one, and `Tc`
the cost of a child body. -/
noncomputable def nodeOpCost (τ : ℝ) (t : CCoreRT)
    (cPh cRA cG cR2I cPush cDrop cI2R Lenc Lhdr Tc : ℕ) : MOp → ℕ
  | .phase _ _ => cPh * t.volG
  | .rowAdd _ _ _ => cRA * (t.volG * (Utau τ (t.e * t.K) + 1))
  | .gate _ _ _ => cG * t.volG
  | .child _ _ => cR2I * Lenc + cPush * t.volG + (Tc + 2) + cDrop * Lhdr + cI2R * Lenc

/-- **The node run (statement).** From the entry state of a non-leaf call `t` (array `z` on `io`,
descriptor on `desc`, empty framed stacks, clean scratch), the node branch reaches the state
where `io` holds `Enc t z' ++ tio` and every other stack is as at entry. The run is safe for
`ccoreFramed` in the environment `L.body cdat :: ρ` of the enclosing `fix`. Here `z'` is any array
whose role stream `u` is the class-`u` result of the node code, read from physical role
`collectPerm u`. The cost is split + the charged operations (`nodeOpCost`) + the terminal
`skip` + collect. The hypotheses are: the growth requirements of every operation, length bounds,
and the child oracle `IHk` for `recur 0`. `IHk` allows arbitrary framed content (the frame tails
of the child). -/
def NodeRunStmt : Prop :=
  ∀ {E σ : Type} [DecidableEq E] (p : LayerParams) (P₀ βn βd Estar : ℕ)
    (Erow : Stage × Fix 100 × Fin 8 → ℕ) (cS cC cPh cRA cG cR2I cPush cDrop cI2R : ℕ)
    (L : CoreProgs E σ) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData),
    NodeSpecs p P₀ L Erow cS cC cPh cRA cG cR2I cPush cDrop cI2R →
    ∀ (ρ : List (Prog (CL E) (fun _ => Sym) σ)) (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
      (hA' : 0 < t.A / Wn) (z z' : RArr (LayerAddr t.A t.K t.D t.S) t.r) (tio tdesc : List Sym)
      (S : CL E → List Sym) (bs : ℕ → ℕ) (Lenc Lhdr Tc : ℕ),
      CCoreBands p P₀ t → 1 ≤ t.k → 6 ≤ t.K → Wn ∣ t.A →
      (∀ u p₁ p₂, MOp.rowAdd u p₁ p₂ ∈ nodeCode cdat → p₁ ≠ p₂) →
      BlkTerm tio → S ioL = Enc t hA hS z ++ tio → S descL = t.hdr ++ tdesc →
      (∀ k, ccoreFramed k → S k = []) → KClean S →
      (∀ (i : ℕ) (hi : i < (nodeCode cdat).length),
        opReq βn βd Estar Erow t (bs i) ((nodeCode cdat)[i])
          (mopsVal t ((nodeCode cdat).take i) (fun u => restrictRole t u z))) →
      (∀ w, (Enc (compactRT t) hA' hS w).length + 1 ≤ Lenc) →
      (∀ a, (childHdr t a).length + 1 ≤ Lhdr) →
      (∀ (u : Fin Wn) (a : Fin mn) (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) (b' : ℕ)
        (Sc : CL E → List Sym),
        ArrGrowth t.P b' w → b' + cDepth t.d βn βd Estar (t.k - 1) ≤ t.Δ → KClean Sc →
        Sc ioL = Enc (compactRT t) hA' hS w ++ tio →
        Sc descL = childHdr t a ++ (t.hdr ++ tdesc) →
        Calculus.SafeRunsIn ccoreFramed (L.body cdat :: ρ) (.recur 0) Sc
          (Function.update Sc ioL (Enc (compactRT t) hA' hS (childVal t a w) ++ tio))
          (fun _ => True) (Tc + 2)) →
      (∀ u, restrictRole t u z' =
        mopsVal t (nodeCode cdat) (fun u => restrictRole t u z) (collectPerm u)) →
      Calculus.SafeRunsIn ccoreFramed (L.body cdat :: ρ) (L.nodeProg cdat) S
        (Function.update S ioL (Enc t hA hS z' ++ tio)) (fun _ => True)
        (cS * t.volG + (((nodeCode cdat).map
          (nodeOpCost p.τ t cPh cRA cG cR2I cPush cDrop cI2R Lenc Lhdr Tc)).sum + 1) +
            cC * t.volG)

end SubNLogN.Machine.CCore
