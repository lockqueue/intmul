/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelMathDefs
import SubNLogN.Math.Networks.Proofs.CCoreCounts

/-!
# C-core node code: the exact child count (M5, `CCore/NodeCodeCount.lean`)

Proof of `NodeChildCountStmt cdat` (`CCore/SkelMathDefs.lean`): given the complex-network certificate and
valid complex edge data, the fixed node code `nodeCode cdat` (`CCore/SkelCode.lean`) contains
exactly `s_c` child calls. The count mirrors the value-level count of `cxNodeOps`
(`Math/Networks/Proofs/CCoreCounts.lean`):
* `edgeCode Dd u` has one child call per element of `(range |basis|).zip eps` (`mc_edgeCode`);
* `nodeCode cdat` has `Σ_{j,ι,r,w} gcnt + Σ_w ecnt (sink w)` calls (`mc_nodeCode`), which is
  `Σ_w Σ_{e ∈ edges w} dim residual e` (`nodeEdgeSchedule_sum`, `edge_calls_eq`), i.e. `s_c`
  by the certificate (`ComplexNetCert.count`).

Implementation note: the zero counts of the phase lists are proved by induction over a general list
(`mc_map_phase`, `mc_flatMap_phase3`), never by arithmetic on the closed lengths
`(Finset.univ : Finset (Addr 100)).toList.length` (the kernel would evaluate them).

Helpers are in `SubNLogN.Machine.CCore.NodeCodeAux`.
-/

namespace SubNLogN.Machine.CCore

open SubNLogN.Math.Networks

namespace NodeCodeAux

/-- The number of child calls in a list of machine operations. -/
def mc (l : List MOp) : ℕ := (l.filter MOp.isChild).length

theorem mc_nil : mc [] = 0 := rfl

theorem mc_cons (o : MOp) (l : List MOp) : mc (o :: l) = (if o.isChild then 1 else 0) + mc l := by
  unfold mc
  rw [List.filter_cons]
  split_ifs <;> simp [Nat.add_comm]

theorem mc_append (l₁ l₂ : List MOp) : mc (l₁ ++ l₂) = mc l₁ + mc l₂ := by
  unfold mc
  rw [List.filter_append, List.length_append]

theorem mc_flatMap {α : Type*} (l : List α) (f : α → List MOp) :
    mc (l.flatMap f) = (l.map fun a => mc (f a)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, mc_append, ih, List.map_cons, List.sum_cons]

theorem mc_map_phase {α : Type*} (l : List α) (u : α → Fin Wn) (κ : α → PhaseKind) :
    mc (l.map fun a => MOp.phase (u a) (κ a)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, mc_cons, ih]
    all_goals rfl

theorem mc_flatMap_phase3 {α : Type*} (l : List α) (u₁ u₂ u₃ : α → Fin Wn)
    (κ₁ κ₂ κ₃ : α → PhaseKind) :
    mc (l.flatMap fun a => [MOp.phase (u₁ a) (κ₁ a), MOp.phase (u₂ a) (κ₂ a),
      MOp.phase (u₃ a) (κ₃ a)]) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, mc_append, ih]
    all_goals rfl

theorem mc_map_rowAdd {α : Type*} (l : List α) (u : Fin Wn) (p₁ p₂ : α → Fin mn) :
    mc (l.map fun a => MOp.rowAdd u (p₁ a) (p₂ a)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, mc_cons, ih]
    all_goals rfl

theorem mc_gate (j : Stage) (ι : Fix 100) (r : Fin 8) : mc [MOp.gate j ι r] = 0 := rfl

theorem mc_kern (u : Fin Wn) (p : ℕ × ℤ) :
    mc (if p.2 = 1 then [MOp.child u (slotOf p.1)]
      else [MOp.phase u (.zSlot (slotOf p.1)), MOp.child u (slotOf p.1),
        MOp.phase u (.zSlot (slotOf p.1)), MOp.phase u .negIPow]) = 1 := by
  split_ifs <;> rfl

theorem sum_map_one {α : Type*} (l : List α) (g : α → ℕ) (h : ∀ a, g a = 1) :
    (l.map g).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.sum_cons, h a, ih, List.length_cons, Nat.add_comm]

/-- One child call per element of `(range |basis|).zip eps` (an inverse kernel is one call). -/
theorem mc_edgeCode (Dd : CxEdgeData) (u : Fin Wn) :
    mc (edgeCode Dd u) = min Dd.basis.length Dd.eps.length := by
  unfold edgeCode
  rw [mc_append, mc_append, mc_map_rowAdd, mc_map_rowAdd, Nat.zero_add, Nat.add_zero, mc_flatMap,
    sum_map_one _ _ (fun p => mc_kern u p), List.length_zip, List.length_range]

theorem mc_edgeCodeAt (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (w : Role .complex 100) (v : Vertex .complex 100) :
    mc (edgeCodeAt cdat w v) = CCoreCountsAux.ecnt cdat w v := by
  unfold edgeCodeAt CCoreCountsAux.ecnt
  cases edgeInto w v with
  | none => rfl
  | some e => exact mc_edgeCode (cdat e) (roleIdxN w)

/-- **Calls of the node code**: the role sums of the gate edges and the sink edges. -/
theorem mc_nodeCode (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) :
    mc (nodeCode cdat) =
      ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, ∑ w : Role .complex 100,
        CCoreCountsAux.gcnt cdat j ι r w +
        ∑ w : Role .complex 100, CCoreCountsAux.ecnt cdat w (.sink w) := by
  rw [nodeCode, mc_append, mc_append, mc_append, mc_map_phase, mc_flatMap_phase3, Nat.zero_add, Nat.add_zero]
  refine congrArg₂ HAdd.hAdd ?_ ?_
  · rw [mc_flatMap, CCoreCountsAux.stage_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mc_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    rw [mc_flatMap, ← Fin.sum_univ_def]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [mc_append, mc_gate, Nat.add_zero, mc_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    unfold CCoreCountsAux.gcnt
    cases gateAt j ι r w with
    | none => rfl
    | some g => exact mc_edgeCodeAt cdat w _
  · rw [mc_flatMap, Finset.sum_map_toList]
    exact Finset.sum_congr rfl (fun w _ => mc_edgeCodeAt cdat w _)

end NodeCodeAux

open NodeCodeAux in
/-- **(M5) Exact child count of the node code**: given the complex-network certificate and valid complex
edge data, `nodeCode cdat` makes exactly `s_c` child calls (with multiplicity; one per residual
basis vector of every edge, inverse kernels included), by the certificate total
`Σ_e dim residual = s_c`. -/
theorem nodeChildCount_holds (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) :
    NodeChildCountStmt cdat := by
  intro hcert hV
  show mc (nodeCode cdat) = tripleSc 100
  rw [mc_nodeCode]
  have hb : ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, ∑ w : Role .complex 100,
      CCoreCountsAux.gcnt cdat j ι r w +
      ∑ w : Role .complex 100, CCoreCountsAux.ecnt cdat w (.sink w) =
      ∑ w : Role .complex 100,
        ((edges w).map fun e => min (cdat e).basis.length (cdat e).eps.length).sum :=
    CCoreCountsAux.nodeEdgeSchedule_sum (fun _ e => min (cdat e).basis.length (cdat e).eps.length)
  rw [hb, ← hcert.count]
  exact Finset.sum_congr rfl (fun w _ =>
    congrArg List.sum (List.map_congr_left (fun e he => CCoreCountsAux.edge_calls_eq cdat hV w e he)))

end SubNLogN.Machine.CCore
