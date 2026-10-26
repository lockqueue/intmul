import SubNLogN.Math.Networks.Proofs.InterchangeCorrectTransport
import SubNLogN.Math.Networks.Proofs.Serial

/-!
# Proposition A.7 (`prop:transfer11`) correctness, part N: the network node realizes `H ← H + D`

Transport of the role operations of `bitNodeOps` to role states (`roleState`, `InterchangeCorrectRoles.lean`):
* the Lemma A.6 (`lem:transfer-shear`) shear program of the edge of `w` entering `v` (`edgeOpsB`) acts as the event
  `NodeEvent.edge w v` with edge operators `bitEdgeOps (q^b)` (by `run_shearOps`, part C);
* a gate (`gateOpB j ι r`) acts as the event `NodeEvent.row j ι r` (pointwise on aligned records);
* the relabelling `rhoPerm` acts as `s ↦ s ∘ ρ`;
* nothing outside `c` changes.
So the node minus its relabel acts on role states as `runEvents … (nodeEvents .bit 100)`, which is
`framedNet` (`serialEqFramed_holds`, `Proofs/Serial.lean`), and `BitArrayCorollaryStmt`
(`BitNetCert.array_corollary`) with the relabelling gives the pull `H ← H − D`: the node realizes
`H ← H + D` on every role.
-/

namespace SubNLogN.Math.Networks

open Model

namespace InterchangeCorrect

variable {L : Layout}

/-! ### The node -/

/-- `bitNodeOps` without its final relabelling. -/
noncomputable def nodeMainOps {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {Child : Type}
    (R h₀ d₀ b : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (childOf : Fin mH → Fin mH → Child) : List (RoleOp L β Wb Child) :=
  ([Stage.one, .two, .three].flatMap fun j => (Finset.univ : Finset (Fix 100)).toList.flatMap fun ι =>
    (List.finRange 8).flatMap fun r =>
      ((Finset.univ : Finset (Role .bit 100)).toList.flatMap fun w =>
        match gateAt j ι r w with
        | some g => edgeOpsB R h₀ d₀ b fac childOf w (.gate g)
        | none => []) ++ [gateOpB j ι r]) ++
  ((Finset.univ : Finset (Role .bit 100)).toList.flatMap fun w =>
    edgeOpsB R h₀ d₀ b fac childOf w (.sink w))

theorem bitNodeOps_eq {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {Child : Type}
    (R h₀ d₀ b : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (childOf : Fin mH → Fin mH → Child) :
    bitNodeOps (L := L) (β := β) R h₀ d₀ b fac childOf =
      nodeMainOps R h₀ d₀ b fac childOf ++ [.relabel rhoPerm] := rfl

/-- The physical role operations of one event of the serialized network. -/
noncomputable def evOps {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {Child : Type}
    (R h₀ d₀ b : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (childOf : Fin mH → Fin mH → Child) : NodeEvent .bit 100 → List (RoleOp L β Wb Child)
  | .edge w v => edgeOpsB R h₀ d₀ b fac childOf w v
  | .row j ι r => [gateOpB j ι r]

theorem flatMap_filterMap_edge {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {Child : Type}
    (R h₀ d₀ b : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (childOf : Fin mH → Fin mH → Child) (j : Stage) (ι : Fix 100) (r : Fin 8)
    (l : List (Role .bit 100)) :
    (l.filterMap fun w => (gateAt j ι r w).map fun g => NodeEvent.edge w (.gate g)).flatMap
        (evOps (L := L) (β := β) R h₀ d₀ b fac childOf) =
      l.flatMap fun w => match gateAt j ι r w with
        | some g => edgeOpsB R h₀ d₀ b fac childOf w (.gate g)
        | none => [] := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    rw [List.filterMap_cons, List.flatMap_cons]
    cases h : gateAt j ι r w with
    | none =>
      simp only [Option.map_none, List.nil_append]
      exact ih
    | some g =>
      simp only [Option.map_some, List.flatMap_cons]
      rw [ih]
      rfl

/-- `nodeMainOps` is the event list `nodeEvents` with every event replaced by its operations. -/
theorem nodeMainOps_eq_flatMap {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {Child : Type}
    (R h₀ d₀ b : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (childOf : Fin mH → Fin mH → Child) :
    nodeMainOps (L := L) (β := β) R h₀ d₀ b fac childOf =
      (nodeEvents .bit 100).flatMap (evOps R h₀ d₀ b fac childOf) := by
  unfold nodeMainOps nodeEvents
  simp only [List.flatMap_append, List.flatMap_map, List.flatMap_assoc, flatMap_filterMap_edge,
    List.flatMap_singleton, evOps]

/-- Transport along any event list. -/
theorem roleState_events {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c)
    (hq : q.Prime) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    {Child β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (childOf : Fin mH → Fin mH → Child)
    (hchild : ∀ (k : Fin Wb) (i j : Fin mH) (A : L.Addr → β), crun (childOf i j) (c.sub Wb Wb_pos k) A =
      (Step.swapBlocks (h₀ + i.val * b) (d₀ + j.val * b) b : Step L β).runIn (c.sub Wb Wb_pos k) A)
    (evs : List (NodeEvent .bit 100)) (A : L.Addr → β) :
    roleState c (q ^ b) h₀ d₀ b ((evs.flatMap (evOps (L := L) (β := β) (q ^ b) h₀ d₀ b fac
        childOf)).foldl (fun A o => o.run crun c Wb_pos A) A) =
      runEvents .bit (0 : ZMod 2) (bitEdgeOps (q ^ b)) evs (roleState c (q ^ b) h₀ d₀ b A) ∧
    ∀ x, ¬ c.mem x → (evs.flatMap (evOps (L := L) (β := β) (q ^ b) h₀ d₀ b fac childOf)).foldl
        (fun A o => o.run crun c Wb_pos A) A x = A x := by
  induction evs generalizing A with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | cons ev rest ih =>
    rw [List.flatMap_cons, List.foldl_append]
    have hev : roleState c (q ^ b) h₀ d₀ b ((evOps (L := L) (β := β) (q ^ b) h₀ d₀ b fac
          childOf ev).foldl (fun A o => o.run crun c Wb_pos A) A) =
          ev.run .bit (0 : ZMod 2) (bitEdgeOps (q ^ b)) (roleState c (q ^ b) h₀ d₀ b A) ∧
        ∀ x, ¬ c.mem x → (evOps (L := L) (β := β) (q ^ b) h₀ d₀ b fac childOf ev).foldl
          (fun A o => o.run crun c Wb_pos A) A x = A x := by
      cases ev with
      | edge w v => exact roleState_edgeOpsB hN hq fac hfac crun childOf hchild w v A
      | row j ι r =>
        simp only [evOps, List.foldl_cons, List.foldl_nil]
        exact roleState_gateOpB hN crun j ι r A
    obtain ⟨h1, h2⟩ := ih ((evOps (L := L) (β := β) (q ^ b) h₀ d₀ b fac childOf ev).foldl
      (fun A o => o.run crun c Wb_pos A) A)
    refine ⟨?_, fun x hx => (h2 x hx).trans (hev.2 x hx)⟩
    rw [h1, hev.1]
    rfl

/-- The node without relabel acts on role states as the serialized framed network. -/
theorem roleState_nodeMain {q h₀ d₀ b : ℕ} {c : RowClass L} (hN : NodeHyp L q h₀ d₀ b c)
    (hq : q.Prime) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    {Child β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (childOf : Fin mH → Fin mH → Child)
    (hchild : ∀ (k : Fin Wb) (i j : Fin mH) (A : L.Addr → β), crun (childOf i j) (c.sub Wb Wb_pos k) A =
      (Step.swapBlocks (h₀ + i.val * b) (d₀ + j.val * b) b : Step L β).runIn (c.sub Wb Wb_pos k) A)
    (A : L.Addr → β) :
    roleState c (q ^ b) h₀ d₀ b ((nodeMainOps (L := L) (β := β) (q ^ b) h₀ d₀ b fac childOf).foldl
        (fun A o => o.run crun c Wb_pos A) A) =
      runEvents .bit (0 : ZMod 2) (bitEdgeOps (q ^ b)) (nodeEvents .bit 100)
        (roleState c (q ^ b) h₀ d₀ b A) ∧
    ∀ x, ¬ c.mem x → (nodeMainOps (L := L) (β := β) (q ^ b) h₀ d₀ b fac childOf).foldl
        (fun A o => o.run crun c Wb_pos A) A x = A x := by
  rw [nodeMainOps_eq_flatMap]
  exact roleState_events hN hq fac hfac crun childOf hchild (nodeEvents .bit 100) A

/-- **The node realizes `H ← H + D`** on every role (pull `H ← H − D`), for arbitrary data. -/
theorem run_node (hcert : BitNetCert) {q h₀ d₀ b : ℕ} {c : RowClass L}
    (hN : NodeHyp L q h₀ d₀ b c) (hq : q.Prime)
    (hfr : ∀ (v : Vertex .bit 100) (i j : Cube 100), QIntegral q (matB v i j))
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e))
    {Child β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (childOf : Fin mH → Fin mH → Child)
    (hchild : ∀ (k : Fin Wb) (i j : Fin mH) (A : L.Addr → β), crun (childOf i j) (c.sub Wb Wb_pos k) A =
      (Step.swapBlocks (h₀ + i.val * b) (d₀ + j.val * b) b : Step L β).runIn (c.sub Wb Wb_pos k) A)
    (A : L.Addr → β) :
    (bitNodeOps (L := L) (β := β) (q ^ b) h₀ d₀ b fac childOf).foldl
        (fun A o => o.run crun c Wb_pos A) A =
      cpull c.mem (fun x => setCoords L (q ^ b) h₀ b x
        (coords L (q ^ b) h₀ b x - coords L (q ^ b) d₀ b x)) A := by
  rw [bitNodeOps_eq, List.foldl_append, List.foldl_cons, List.foldl_nil]
  obtain ⟨hm1, hm2⟩ := roleState_nodeMain hN hq fac hfac crun childOf hchild A
  obtain ⟨hr1, hr2⟩ := roleState_relabel hN crun
    ((nodeMainOps (L := L) (β := β) (q ^ b) h₀ d₀ b fac childOf).foldl
      (fun A o => o.run crun c Wb_pos A) A)
  apply eq_of_roleState hN
  · intro x hx
    rw [hr2 x hx, hm2 x hx]
    simp [cpull, hx]
  · rw [hr1, hm1, serialEqFramed_holds 100 .bit (0 : ZMod 2) (bitEdgeOps (q ^ b))
      (roleState c (q ^ b) h₀ d₀ b A)]
    funext w z
    rw [hcert.array_corollary q b hq hfr (roleState c (q ^ b) h₀ d₀ b A) w z]
    simp only [roleState, cpull, if_pos (roleAddr_mem_class hN _ _ _ _)]
    rw [(coords_roleAddr hN _ _ _ _).1, (coords_roleAddr hN _ _ _ _).2, setCoords_H_roleAddr hN]
    rfl

end InterchangeCorrect

end SubNLogN.Math.Networks
