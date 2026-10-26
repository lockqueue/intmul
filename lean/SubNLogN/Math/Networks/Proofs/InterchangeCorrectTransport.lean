import SubNLogN.Math.Networks.Proofs.InterchangeCorrectShear
import SubNLogN.Math.Networks.Proofs.InterchangeCorrectRoles
import SubNLogN.Math.Networks.AppCFun

/-!
# Proposition A.7 (`prop:transfer11`) correctness, part T: transport of the role operations of a node to role states

For a node in class `c` (`NodeHyp`), the physical role operations of `bitNodeOps` act on the role
state (`roleState`, `InterchangeCorrectRoles.lean`) as the events of the serialized framed network (`NodeEvent.run`,
`AppCFun.lean`) with edge operators `bitEdgeOps (q^b)`:
* `roleState_edgeOpsB`: the Lemma A.6 (`lem:transfer-shear`) shear program of the edge of `w` entering `v` (by `run_shearOps`, part C)
  acts as `NodeEvent.edge w v`;
* `roleState_gateOpB`: the gate at `(j, ι, r)` acts as `NodeEvent.row j ι r` (pointwise on aligned
  records);
* `roleState_relabel`: `relabel rhoPerm` acts as `s ↦ s ∘ ρ`;
and none of them changes an address outside `c`.
-/

namespace SubNLogN.Math.Networks

open Model

namespace InterchangeCorrect

variable {L : Layout}

/-! ### Transport of role operations -/

/-! ### Helpers (sub-namespace `TransportAux`) -/

namespace TransportAux

/-- A row of the scalar network commutes with evaluation of array-valued states at a point. -/
theorem rowUpd_apply {κ : Kind} {h : ℕ} {R X M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (half : R) (j : Stage) (ι : Fix h) (op : Op) (ε : R) (s : Role κ h → (X → M))
    (w : Role κ h) (z : X) :
    rowUpd κ half j ι op ε s w z = rowUpd κ half j ι op ε (fun w' => s w' z) w := by
  have hside : ∀ S, sideVal κ half j ι s S z = sideVal κ half j ι (fun w' => s w' z) S := by
    intro S
    simp only [sideVal, Finset.sum_apply, Pi.smul_apply]
  have hgather : ∀ c, gatherVal j ι s c z = gatherVal j ι (fun w' => s w' z) c := by
    intro c
    cases c <;> simp only [gatherVal, Finset.sum_apply]
  have hscatter : ∀ S, scatterVal κ half j ι s S z =
      scatterVal κ half j ι (fun w' => s w' z) S := by
    intro S
    cases κ <;> simp only [scatterVal, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply]
  cases op <;> cases w <;> simp only [rowUpd, ite_apply, Pi.add_apply, Pi.smul_apply, hgather] <;>
    split <;> rename_i heq <;> simp only [heq, Pi.add_apply, Pi.smul_apply, hside, hscatter]

/-- Reindexing a matrix along an equivalence commutes with `mulVec` (generic finite types). -/
theorem mulVec_reindex_map {α ι S : Type*} [Fintype α] [Fintype ι] [CommRing S] (e : α ≃ ι)
    (M : Matrix α α ℚ) (f : ℚ → S) (u : α → S) (i : ι) :
    ((Matrix.reindex e e M).map f).mulVec (fun j => u (e.symm j)) i =
      ((M.map f).mulVec u) (e.symm i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun p => f (M (e.symm i) p) * u p)

/-- The role address of role `k'` lies in the role class of `k` iff `k' = k`. -/
theorem roleAddr_mem_sub_iff {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c)
    (k k' : Fin Wb) (H D : Fin mH → ZMod (q ^ b)) (y : L.Addr) :
    (c.sub Wb Wb_pos k).mem (roleAddr c (q ^ b) h₀ d₀ b k' H D y) ↔ k' = k := by
  rw [mem_sub_iff, roleIdx_roleAddr hN]
  exact ⟨fun h => h.2, fun h => ⟨roleAddr_mem_class hN k' H D y, h⟩⟩

end TransportAux

open TransportAux

/-- The Lemma A.6 (`lem:transfer-shear`) shear program of the edge of `w` entering `v` acts on role states as the event `edge w v`. -/
theorem roleState_edgeOpsB {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c)
    (hq : q.Prime) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    {Child β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β))
    (childOf : Fin mH → Fin mH → Child)
    (hchild : ∀ (k : Fin Wb) (i j : Fin mH) (A : L.Addr → β), crun (childOf i j) (c.sub Wb Wb_pos k) A =
      (Step.swapBlocks (h₀ + i.val * b) (d₀ + j.val * b) b : Step L β).runIn (c.sub Wb Wb_pos k) A)
    (w : Role .bit 100) (v : Vertex .bit 100) (A : L.Addr → β) :
    roleState c (q ^ b) h₀ d₀ b ((edgeOpsB (L := L) (β := β) (q ^ b) h₀ d₀ b fac childOf w v).foldl
        (fun A o => o.run crun c Wb_pos A) A) =
      (NodeEvent.edge w v).run .bit (0 : ZMod 2) (bitEdgeOps (q ^ b)) (roleState c (q ^ b) h₀ d₀ b A) ∧
    ∀ x, ¬ c.mem x → (edgeOpsB (L := L) (β := β) (q ^ b) h₀ d₀ b fac childOf w v).foldl
        (fun A o => o.run crun c Wb_pos A) A x = A x := by
  rcases hE : edgeInto w v with _ | e
  · have hops : edgeOpsB (L := L) (β := β) (q ^ b) h₀ d₀ b fac childOf w v = [] := by
      simp only [edgeOpsB, hE]
    rw [hops]
    refine ⟨?_, fun x _ => rfl⟩
    simp only [List.foldl_nil, NodeEvent.run, hE]
    exact (Function.update_eq_self _ _).symm
  · have he : e ∈ edges w := List.mem_of_find?_eq_some hE
    have hF := hfac w e he
    have hops : edgeOpsB (L := L) (β := β) (q ^ b) h₀ d₀ b fac childOf w v =
        shearOps (q ^ b) h₀ d₀ b (roleIdxB w) (fac (edgeMatFin e)) childOf := by
      simp only [edgeOpsB, hE]
    rw [hops, run_shearOps hN.two hq Wb_pos crun c hN.row (roleIdxB w) childOf (hchild _)
      (edgeMatFin e) _ hF]
    refine ⟨?_, fun x hx => ?_⟩
    · funext w' z
      by_cases hw : w' = w
      · rw [hw]
        simp only [NodeEvent.run, hE, Function.update_self]
        simp only [roleState, bitEdgeOps, shearArr, cpull]
        rw [if_pos (roleAddr_mem hN (roleIdxB w) _ _ _), (coords_roleAddr hN _ _ _ _).1,
          (coords_roleAddr hN _ _ _ _).2, setCoords_H_roleAddr hN]
        refine congrArg (fun H' => A (roleAddr c (q ^ b) h₀ d₀ b (roleIdxB w) H'
          (fun i => z.2.1 (cubeEquiv.symm i)) z.2.2)) ?_
        funext i
        simp only [Pi.sub_apply, edgeMatFin]
        rw [mulVec_reindex_map]
      · simp only [NodeEvent.run, hE, Function.update_of_ne hw]
        simp only [roleState, cpull]
        rw [if_neg (fun hm => hw (roleIdxB.injective
          ((roleAddr_mem_sub_iff hN (roleIdxB w) (roleIdxB w') _ _ _).1 hm)))]
    · simp only [cpull]
      rw [if_neg (fun hsub => hx ((mem_sub_iff c _ x).1 hsub).1)]

/-- A gate acts on role states as its row (pointwise). -/
theorem roleState_gateOpB {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c)
    {Child β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (j : Stage) (ι : Fix 100) (r : Fin 8)
    (A : L.Addr → β) :
    roleState c (q ^ b) h₀ d₀ b ((gateOpB j ι r : RoleOp L β Wb Child).run crun c Wb_pos A) =
      (NodeEvent.row j ι r).run .bit (0 : ZMod 2) (bitEdgeOps (q ^ b))
        (roleState c (q ^ b) h₀ d₀ b A) ∧
    ∀ x, ¬ c.mem x → (gateOpB j ι r : RoleOp L β Wb Child).run crun c Wb_pos A x = A x := by
  refine ⟨?_, fun x hx => ?_⟩
  · funext w z
    simp only [NodeEvent.run]
    rw [rowUpd_apply]
    simp only [roleState, gateOpB, RoleOp.run, gateRun]
    rw [if_pos (roleAddr_mem_class hN (roleIdxB w) _ _ _), roleIdx_roleAddr hN,
      Equiv.symm_apply_apply]
    simp only [aligned_roleAddr hN]
  · simp only [gateOpB, RoleOp.run, gateRun]
    rw [if_neg hx]

/-- The relabelling `rhoPerm`: role `w` receives the stream of role `ρ w`. -/
theorem roleState_relabel {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c)
    {Child β : Type} (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (A : L.Addr → β) :
    roleState c (q ^ b) h₀ d₀ b ((RoleOp.relabel rhoPerm : RoleOp L β Wb Child).run crun c Wb_pos A) =
      (fun w => roleState c (q ^ b) h₀ d₀ b A w.rho) ∧
    ∀ x, ¬ c.mem x → (RoleOp.relabel rhoPerm : RoleOp L β Wb Child).run crun c Wb_pos A x = A x := by
  refine ⟨?_, fun x hx => ?_⟩
  · funext w z
    have hrho : rhoPerm.symm (roleIdxB w) = roleIdxB w.rho := by
      simp only [rhoPerm, Equiv.symm_trans_apply, Equiv.symm_apply_apply]
      rfl
    simp only [roleState, RoleOp.run, relabelRun]
    rw [if_pos (roleAddr_mem_class hN (roleIdxB w) _ _ _), roleIdx_roleAddr hN, hrho,
      aligned_roleAddr hN]
  · simp only [RoleOp.run, relabelRun]
    rw [if_neg hx]

end InterchangeCorrect

end SubNLogN.Math.Networks
