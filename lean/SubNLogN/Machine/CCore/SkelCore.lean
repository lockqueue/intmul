/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelMathDefs
import SubNLogN.Machine.CCore.MathM4
import SubNLogN.Machine.Calculus.SafeFold

/-!
# C-core skeleton: the program and its recursion on a big layout (`CCore/SkelCore.lean`)

Fix a big layout `CL E` (named stacks `CCoreN W` plus a private scratch type `E`) and registers
`σ`. `CoreProgs E σ` collects one program per kernel instance:
* the header test with its observation `obs`;
* the leaf kernel; split and collect;
* the role kernels (phase, Lemma A.9 row addition, scalar row);
* the child-protocol kernels (role-to-io, push child header, drop header, io-to-role).

`CoreProgs.prog L cdat = .fix (L.body cdat)` is the C-core program. Its body runs the header test,
then branches on `obs` to either the leaf kernel or the node branch
`split ; forEachProg (nodeCode cdat) opProg ; collect`. A child operation is
`roleToIo u ; pushChildHdr a ; recur 0 ; dropHdr ; ioToRole u`.

`CoreTopSpecs` (`PartsDefs.lean`) and `NodeSpecs` (`SkelNode.lean`) state the big-layout `SafeRunsIn`
facts of these programs (the leaf statements of `SkelDefs.lean` transported via `SkelLayout.lean`).
The theorem `PartsAux.core_fix_spec` (`Parts.lean`) proves the C-core specification of
`L.prog cdat` from `CoreTopSpecs`, `NodeSpecs`, and the mathematical leaves, by `SafeRunsIn.fix`.
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks

/-- The programs of the C-core skeleton on the big layout `CL E` with registers `σ`. -/
structure CoreProgs (E σ : Type) where
  /-- header test -/
  hdr : Prog (CL E) (fun _ => Sym) σ
  /-- the leaf flag computed by `hdr` -/
  obs : σ → Bool
  /-- leaf kernel -/
  leaf : Prog (CL E) (fun _ => Sym) σ
  /-- row split -/
  split : Prog (CL E) (fun _ => Sym) σ
  /-- collect with the relabel `collectPerm` -/
  coll : Prog (CL E) (fun _ => Sym) σ
  /-- phase kernels -/
  phase : Fin Wn → PhaseKind → Prog (CL E) (fun _ => Sym) σ
  /-- Lemma A.9 row additions -/
  rowAdd : Fin Wn → Fin mn → Fin mn → Prog (CL E) (fun _ => Sym) σ
  /-- scalar rows -/
  gate : Stage → Fix 100 → Fin 8 → Prog (CL E) (fun _ => Sym) σ
  /-- move a role stream to `io` -/
  r2i : Fin Wn → Prog (CL E) (fun _ => Sym) σ
  /-- push a child header -/
  push : Fin mn → Prog (CL E) (fun _ => Sym) σ
  /-- drop a 12-field header -/
  drop : Prog (CL E) (fun _ => Sym) σ
  /-- move `io` back to a role stream -/
  i2r : Fin Wn → Prog (CL E) (fun _ => Sym) σ

namespace CoreProgs

variable {E σ : Type}

/-- The program of one machine operation; a child call uses `recur 0`. -/
def opProg (L : CoreProgs E σ) : MOp → Prog (CL E) (fun _ => Sym) σ
  | .phase u κ => L.phase u κ
  | .rowAdd u p₁ p₂ => L.rowAdd u p₁ p₂
  | .gate j ι r => L.gate j ι r
  | .child u a => .seq (L.r2i u) (.seq (L.push a) (.seq (.recur 0) (.seq L.drop (L.i2r u))))

/-- The node branch: split, the fixed node code, collect. -/
noncomputable def nodeProg (L : CoreProgs E σ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) :
    Prog (CL E) (fun _ => Sym) σ :=
  .seq L.split (.seq (forEachProg (nodeCode cdat) L.opProg) L.coll)

/-- The body: header test, then leaf kernel or node branch. -/
noncomputable def body (L : CoreProgs E σ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) :
    Prog (CL E) (fun _ => Sym) σ :=
  .seq L.hdr (.ite L.obs L.leaf (L.nodeProg cdat))

/-- **The C-core program.** -/
noncomputable def prog (L : CoreProgs E σ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) :
    Prog (CL E) (fun _ => Sym) σ :=
  .fix (L.body cdat)

/-- All kernel programs are closed. -/
def Closed (L : CoreProgs E σ) : Prop :=
  L.hdr.Closed ∧ L.leaf.Closed ∧ L.split.Closed ∧ L.coll.Closed ∧
    (∀ u κ, (L.phase u κ).Closed) ∧ (∀ u p₁ p₂, (L.rowAdd u p₁ p₂).Closed) ∧
    (∀ j ι r, (L.gate j ι r).Closed) ∧ (∀ u, (L.r2i u).Closed) ∧ (∀ a, (L.push a).Closed) ∧
    L.drop.Closed ∧ (∀ u, (L.i2r u).Closed)

theorem freeBelow_mono' {K : Type} {Γ : K → Type} :
    ∀ (p : Prog K Γ σ) {d d' : ℕ}, p.FreeBelow d → d ≤ d' → p.FreeBelow d'
  | .push _ _, _, _, _, _ => trivial
  | .peek _ _, _, _, _, _ => trivial
  | .pop _ _, _, _, _, _ => trivial
  | .load _, _, _, _, _ => trivial
  | .seq p q, _, _, h, hd => ⟨freeBelow_mono' p h.1 hd, freeBelow_mono' q h.2 hd⟩
  | .ite _ p q, _, _, h, hd => ⟨freeBelow_mono' p h.1 hd, freeBelow_mono' q h.2 hd⟩
  | .loop _ p, _, _, h, hd => freeBelow_mono' p h hd
  | .fix b, _, _, h, hd => freeBelow_mono' b h (Nat.succ_le_succ hd)
  | .recur _, _, _, h, hd => lt_of_lt_of_le h hd

theorem freeBelow_forEachProg' {K : Type} {Γ : K → Type} {α : Type} (d : ℕ)
    (f : α → Prog K Γ σ) : ∀ l : List α, (∀ a ∈ l, (f a).FreeBelow d) →
      (forEachProg l f).FreeBelow d
  | [], _ => trivial
  | a :: l, h => ⟨h a List.mem_cons_self,
      freeBelow_forEachProg' d f l (fun b hb => h b (List.mem_cons_of_mem a hb))⟩

theorem closed_prog (L : CoreProgs E σ) (hL : L.Closed)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) : (L.prog cdat).Closed := by
  obtain ⟨hh, hl, hs, hc, hph, hra, hg, hr, hp, hd, hi⟩ := hL
  have h1 : ∀ {p : Prog (CL E) (fun _ => Sym) σ}, p.Closed → p.FreeBelow 1 :=
    fun h => freeBelow_mono' _ h (Nat.zero_le 1)
  have hop : ∀ o : MOp, (L.opProg o).FreeBelow 1 := by
    intro o
    cases o with
    | phase u κ => exact h1 (hph u κ)
    | rowAdd u p₁ p₂ => exact h1 (hra u p₁ p₂)
    | gate j ι r => exact h1 (hg j ι r)
    | child u a =>
      exact ⟨h1 (hr u), h1 (hp a), Nat.zero_lt_one, h1 hd, h1 (hi u)⟩
  exact ⟨h1 hh, h1 hl, h1 hs,
    freeBelow_forEachProg' 1 L.opProg (nodeCode cdat) (fun o _ => hop o), h1 hc⟩

end CoreProgs

end SubNLogN.Machine.CCore
