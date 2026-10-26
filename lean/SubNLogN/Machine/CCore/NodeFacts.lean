/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelMathDefs

/-!
# C-core node code: distinct row-addition slots (`CCore/NodeFacts.lean`)

* `nodeCode_rowAdd_ne cdat hval`: for valid edge data (`ValidCdat cdat`), every row addition
  `MOp.rowAdd u p₁ p₂` of the fixed node code `nodeCode cdat` (`CCore/SkelCode.lean`) has distinct
  slots `p₁ ≠ p₂`. This is the premise `∀ u p₁ p₂, MOp.rowAdd u p₁ p₂ ∈ nodeCode cdat → p₁ ≠ p₂`
  of `NodeRunStmt` (`CCore/SkelNode.lean`).
* The same fact per operation (`nodeCode_rowAdd_ne_op`) and by index
  (`nodeCode_getElem_rowAdd_ne`).

Proof: row additions occur in `nodeCode` only inside edge codes `edgeCode (cdat e) (roleIdxN w)`
with `edgeInto w v = some e`; then `e ∈ edges w` (`NodeFactsAux.edgeInto_mem_nf`, the argument of
`FI.edgeInto_mem`), so `(cdat e).Valid e` holds, whose third conjunct says that every pair of
`rowsInv ++ rowsM` has distinct entries; `Fin.cast` preserves this. Nothing is enumerated:
`Wn`, `Fintype.card` and the `Finset.toList`s are never evaluated.

(The band fact `6 ≤ t.K` above a cutoff is `K_ge_six` in `CCore/MathM4.lean`.)
-/

namespace SubNLogN.Machine.CCore

open SubNLogN.Math.Networks

namespace NodeFactsAux

/-- The edge returned by `edgeInto` is an edge of the wire (the argument of
`FI.edgeInto_mem`, restated here to keep the imports small). -/
theorem edgeInto_mem_nf {w : Role .complex 100} {v : Vertex .complex 100}
    {e : Vertex .complex 100 × Vertex .complex 100} (he : edgeInto w v = some e) :
    e ∈ edges w := by
  unfold edgeInto at he
  exact List.mem_of_find?_eq_some he

/-- A row-addition pair with distinct entries stays distinct after `Fin.cast`. -/
theorem cast_ne_nf (p : Fin mH × Fin mH) (hp : p.1 ≠ p.2) :
    Fin.cast mH_eq_mn p.1 ≠ Fin.cast mH_eq_mn p.2 := by
  intro heq
  exact hp (Fin.ext (congrArg Fin.val heq))

/-- Row additions of an edge code have distinct slots, if the pairs of the edge data do. -/
theorem edgeCode_rowAdd_ne (Dd : CxEdgeData) (hD : ∀ p ∈ Dd.rowsInv ++ Dd.rowsM, p.1 ≠ p.2)
    (u u' : Fin Wn) (p₁ p₂ : Fin mn) (h : MOp.rowAdd u' p₁ p₂ ∈ edgeCode Dd u) : p₁ ≠ p₂ := by
  unfold edgeCode at h
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨p, hp, hpe⟩ := List.mem_map.1 h
      simp only [MOp.rowAdd.injEq] at hpe
      obtain ⟨-, h1, h2⟩ := hpe
      subst h1
      subst h2
      exact cast_ne_nf p (hD p (List.mem_append_left _ hp))
    · obtain ⟨q, -, hq⟩ := List.mem_flatMap.1 h
      by_cases hc : q.2 = 1 <;> simp [hc] at hq
  · obtain ⟨p, hp, hpe⟩ := List.mem_map.1 h
    simp only [MOp.rowAdd.injEq] at hpe
    obtain ⟨-, h1, h2⟩ := hpe
    subst h1
    subst h2
    exact cast_ne_nf p (hD p (List.mem_append_right _ hp))

/-- Row additions of the edge code of wire `w` entering vertex `v` have distinct slots. -/
theorem edgeCodeAt_rowAdd_ne (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ValidCdat cdat) (w : Role .complex 100) (v : Vertex .complex 100) (u : Fin Wn)
    (p₁ p₂ : Fin mn) (h : MOp.rowAdd u p₁ p₂ ∈ edgeCodeAt cdat w v) : p₁ ≠ p₂ := by
  unfold edgeCodeAt at h
  split at h
  · next e he =>
    exact edgeCode_rowAdd_ne (cdat e) (hval w e (edgeInto_mem_nf he)).2.2.1 _ u p₁ p₂ h
  · simp at h

end NodeFactsAux

/-- **Distinct row-addition slots in the node code.** For valid edge data, every row addition
`MOp.rowAdd u p₁ p₂` of `nodeCode cdat` has `p₁ ≠ p₂` (the premise of `NodeRunStmt`). -/
theorem nodeCode_rowAdd_ne (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ValidCdat cdat) : ∀ u p₁ p₂, MOp.rowAdd u p₁ p₂ ∈ nodeCode cdat → p₁ ≠ p₂ := by
  intro u p₁ p₂ h
  unfold nodeCode at h
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨a, -, ha⟩ := List.mem_map.1 h
        simp at ha
      · obtain ⟨j, -, h⟩ := List.mem_flatMap.1 h
        obtain ⟨ι, -, h⟩ := List.mem_flatMap.1 h
        obtain ⟨r, -, h⟩ := List.mem_flatMap.1 h
        rcases List.mem_append.1 h with h | h
        · obtain ⟨w, -, h⟩ := List.mem_flatMap.1 h
          split at h
          · exact NodeFactsAux.edgeCodeAt_rowAdd_ne cdat hval w _ u p₁ p₂ h
          · simp at h
        · simp at h
    · obtain ⟨w, -, h⟩ := List.mem_flatMap.1 h
      exact NodeFactsAux.edgeCodeAt_rowAdd_ne cdat hval w _ u p₁ p₂ h
  · obtain ⟨a, -, h⟩ := List.mem_flatMap.1 h
    simp at h

/-- `nodeCode_rowAdd_ne` per operation (the form of the `hdist` premise in
`CCore/SkelNodeRun.lean`). -/
theorem nodeCode_rowAdd_ne_op (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ValidCdat cdat) :
    ∀ o ∈ nodeCode cdat, ∀ u p₁ p₂, o = MOp.rowAdd u p₁ p₂ → p₁ ≠ p₂ := by
  intro o ho u p₁ p₂ hoe
  subst hoe
  exact nodeCode_rowAdd_ne cdat hval u p₁ p₂ ho

/-- `nodeCode_rowAdd_ne` by index into the node code. -/
theorem nodeCode_getElem_rowAdd_ne
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (hval : ValidCdat cdat) :
    ∀ (i : ℕ) (hi : i < (nodeCode cdat).length) (u : Fin Wn) (p₁ p₂ : Fin mn),
      (nodeCode cdat)[i] = MOp.rowAdd u p₁ p₂ → p₁ ≠ p₂ := by
  intro i hi u p₁ p₂ h
  have hm : (nodeCode cdat)[i] ∈ nodeCode cdat := List.getElem_mem hi
  rw [h] at hm
  exact nodeCode_rowAdd_ne cdat hval u p₁ p₂ hm

end SubNLogN.Machine.CCore
