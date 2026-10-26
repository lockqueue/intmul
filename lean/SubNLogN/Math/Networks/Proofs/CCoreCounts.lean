import SubNLogN.Math.Networks.AppCCounts
import SubNLogN.Math.Networks.Proofs.CCoreWF
import SubNLogN.Math.Networks.Proofs.H2Final

/-!
# Child counts of the Lemma A.10 (`lem:transfer-phase`) core procedure

Statements in `SubNLogN/Math/Networks/AppCCounts.lean`. Helpers live in
`SubNLogN.Math.Networks.CCoreCountsAux`.

* `callCount_of_count`: with valid complex edge data, one node level of `cCoreProc` performs
  `Σ_w Σ_{e ∈ edges w} dim (residual e)` child calls, so exactly `s_c` given the certificate total
  (`ComplexNetCert.count`).
* `nonCallBound`: one node level has at most `E` non-call operations (`CCoreNonCallBoundStmt`), for
  the explicit constant `E = nodeBound = nodeBoundOf |Addr 100| |Fix 100| |Role .complex 100|`,
  `nodeBoundOf nA nF nR = nA + 3 (nF (8 (nR edgeOpsBound + 1))) + nR edgeOpsBound + 3 nA + 1`.
* Public names of the bridge (used by the machine-level cost proofs): `cxNodeEdgeSchedule` (the edges of a
  node in event order), `cxNodeEdgeSchedule_perm` (it is a `List.Perm` of all `(w, e)`,
  `e ∈ edges w`), `cxNodeEdgeSchedule_sum` (weighted form), `cxNodeOps_callCount_edges` (the calls
  of `cxNodeOps` are `Σ_w Σ_{e ∈ edges w} min |basis e| |eps e|`).

## The multiplicity-preserving bridge
`coreEdgeOps` makes exactly one child call per element of `(range |basis|).zip eps`
(`cc_coreEdgeOps`; an inverse kernel `(−i)^f Z C Z` is still one call), i.e. `|basis| = dim` calls
for valid data. `cxNodeOps` runs, for every `(j, ι, r)` and every role `w` touched at that time, the
edge of `w` entering its gate, and then every sink edge. For a fixed role `w` the gates of `touch w`
have pairwise distinct keys `(stage, inv, time)` (`touch_keys_nodup`), so summing over all keys
`(j, ι, r)` visits each gate of `touch w` once (`sum_find_eq`); the heads of `edges w` are
`touch w` followed by the sink, each the head of exactly one edge (`sum_heads`). Hence the calls of
role `w` are `Σ_{e ∈ edges w} |basis e|`.
-/

namespace SubNLogN.Math.Networks

open Model

namespace CCoreCountsAux

/-! ## Counting calls in lists of role operations -/

section Lists

variable {L : Layout} {β : Type} {W : ℕ} {Ch : Type}

/-- The number of child calls in a list of role operations. -/
def cc (l : List (RoleOp L β W Ch)) : ℕ := (l.filter RoleOp.isCall).length

theorem cc_nil : cc ([] : List (RoleOp L β W Ch)) = 0 := rfl

theorem cc_cons (o : RoleOp L β W Ch) (l : List (RoleOp L β W Ch)) :
    cc (o :: l) = (if o.isCall then 1 else 0) + cc l := by
  unfold cc
  rw [List.filter_cons]
  split_ifs <;> simp [Nat.add_comm]

theorem cc_append (l₁ l₂ : List (RoleOp L β W Ch)) : cc (l₁ ++ l₂) = cc l₁ + cc l₂ := by
  unfold cc
  rw [List.filter_append, List.length_append]

theorem cc_flatMap {α : Type*} (l : List α) (f : α → List (RoleOp L β W Ch)) :
    cc (l.flatMap f) = (l.map fun a => cc (f a)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, cc_append, ih, List.map_cons, List.sum_cons]

theorem cc_map_prim {α : Type*} (l : List α) (kf : α → Fin W) (sf : α → Step L β) :
    cc (l.map fun a => (RoleOp.prim (Child := Ch) (kf a) (sf a))) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, cc_cons, ih]
    rfl

theorem cc_map_prim' (l : List (Step L β)) (k : Fin W) :
    cc (l.map (RoleOp.prim (Child := Ch) k)) = 0 :=
  cc_map_prim l (fun _ => k) id

theorem sum_map_one {α : Type*} (l : List α) (g : α → ℕ) (h : ∀ a ∈ l, g a = 1) :
    (l.map g).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb)), List.length_cons, Nat.add_comm]

theorem sum_map_zero {α : Type*} (l : List α) (g : α → ℕ) (h : ∀ a ∈ l, g a = 0) :
    (l.map g).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem sum_map_le {α : Type*} (l : List α) (g : α → ℕ) (c : ℕ) (h : ∀ a ∈ l, g a ≤ c) :
    (l.map g).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, add_mul, one_mul]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

end Lists

/-! ## Reindexing sums over keys and over edge heads -/

section Reindex

/-- Summing over all keys `k` the value at the element of `G` found with key `k` visits every
element of `G` once, if the keys of `G` are distinct. -/
theorem sum_find_eq {α K : Type*} [Fintype K] [DecidableEq K] (G : List α) (κ : α → K)
    (q : K → α → Bool) (hq : ∀ k a, q k a = true ↔ κ a = k) (hG : (G.map κ).Nodup)
    (F : α → ℕ) : ∑ k : K, (G.find? (q k)).elim 0 F = (G.map F).sum := by
  induction G with
  | nil => simp
  | cons g G ih =>
    rw [List.map_cons, List.nodup_cons] at hG
    obtain ⟨hg, hG'⟩ := hG
    have key : ∀ k, ((g :: G).find? (q k)).elim 0 F =
        (G.find? (q k)).elim 0 F + (if κ g = k then F g else 0) := by
      intro k
      rw [List.find?_cons]
      by_cases hk : κ g = k
      · have hqk : q k g = true := (hq k g).mpr hk
        have hnone : G.find? (q k) = none := by
          rw [List.find?_eq_none]
          intro x hx hqx
          apply hg
          rw [List.mem_map]
          exact ⟨x, hx, by rw [(hq k x).mp hqx, hk]⟩
        rw [hqk, hnone, if_pos hk]
        exact (Nat.zero_add (F g)).symm
      · have hqk : q k g = false := by
          cases h : q k g
          · rfl
          · exact absurd ((hq k g).mp h) hk
        rw [hqk, if_neg hk, Nat.add_zero]
    rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_add_distrib, ih hG',
      Finset.sum_ite_eq, if_pos (Finset.mem_univ _), List.map_cons, List.sum_cons, Nat.add_comm]

/-- Over the heads `T` of the edges `(v0 :: T).zip T` (distinct heads), the value at the edge
found with head `v` sums to the total over all edges. -/
theorem sum_heads {V : Type*} (p : V → V × V → Bool) (hp : ∀ v e, p v e = true ↔ e.2 = v)
    (bl : V × V → ℕ) : ∀ (v0 : V) (T : List V), T.Nodup →
      (T.map fun v => (((v0 :: T).zip T).find? (p v)).elim 0 bl).sum =
        (((v0 :: T).zip T).map bl).sum
  | _, [], _ => rfl
  | v0, t :: T, hT => by
    rw [List.nodup_cons] at hT
    obtain ⟨ht, hT'⟩ := hT
    have h1 : ((v0, t) :: (t :: T).zip T).find? (p t) = some (v0, t) := by
      rw [List.find?_cons, (hp t (v0, t)).mpr rfl]
    have h2 : ∀ v ∈ T, ((v0, t) :: (t :: T).zip T).find? (p v) = ((t :: T).zip T).find? (p v) := by
      intro v hv
      have hne : p v (v0, t) = false := by
        cases h : p v (v0, t)
        · rfl
        · have h' := (hp v (v0, t)).mp h
          simp only at h'
          exact absurd (h' ▸ hv) ht
      rw [List.find?_cons, hne]
    have h3 : (T.map fun v => (((v0, t) :: (t :: T).zip T).find? (p v)).elim 0 bl) =
        (T.map fun v => (((t :: T).zip T).find? (p v)).elim 0 bl) :=
      List.map_congr_left (fun v hv => by rw [h2 v hv])
    rw [List.zip_cons_cons, List.map_cons, List.sum_cons, h1, h3, sum_heads p hp bl t T hT',
      List.map_cons, List.sum_cons]
    rfl

end Reindex

/-! ## Calls of the node operations -/

section Node

variable {A K D S rr : ℕ} {Ch : Type}

theorem isCall_prim {L : Layout} {β : Type} {W : ℕ} (k : Fin W) (s : Step L β) :
    (RoleOp.prim (Child := Ch) k s).isCall = false := rfl

theorem isCall_call {L : Layout} {β : Type} {W : ℕ} (k : Fin W) (c : Ch) :
    (RoleOp.call (L := L) (β := β) k c).isCall = true := rfl

theorem isCall_relabel {L : Layout} {β : Type} {W : ℕ} (π : Equiv.Perm (Fin W)) :
    (RoleOp.relabel (L := L) (β := β) (Child := Ch) π).isCall = false := rfl

theorem isCall_gateOpC (j : Stage) (ι : Fix 100) (r : Fin 8) :
    (gateOpC (A := A) (K := K) (D := D) (S := S) (rr := rr) (Child := Ch) j ι r).isCall = false :=
  rfl

theorem cc_map_prim0 {L : Layout} {β : Type} {W : ℕ} (p : ProcK L β 0) (k : Fin W) :
    cc (List.map (RoleOp.prim (Child := Ch) k) p) = 0 :=
  cc_map_prim' p k

/-- One child call per element of `(range |basis|).zip eps` (an inverse kernel is also one call). -/
theorem cc_coreEdgeOps (ρ f j0 : ℕ) (Dd : CxEdgeData) (childOf : ℕ → Ch) (k : Fin Wc) :
    cc (coreEdgeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 Dd childOf k) =
      min Dd.basis.length Dd.eps.length := by
  simp only [coreEdgeOps, cc_append, cc_flatMap, cc_map_prim0]
  simp [apply_ite cc, cc_cons, cc_nil, isCall_prim, isCall_call]

/-- The calls of the edge of `w` entering `v`. -/
noncomputable def ecnt (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (w : Role .complex 100) (v : Vertex .complex 100) : ℕ :=
  (edgeInto w v).elim 0 fun e => min (cdat e).basis.length (cdat e).eps.length

theorem cc_coreEdgeOpsAt (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (childOf : ℕ → Ch)
    (w : Role .complex 100) (v : Vertex .complex 100) :
    cc (coreEdgeOpsAt (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf w v) =
      ecnt cdat w v := by
  unfold coreEdgeOpsAt ecnt
  cases edgeInto w v with
  | none => rfl
  | some e => exact cc_coreEdgeOps ρ f j0 (cdat e) childOf (roleIdxC w)

/-- The calls at gate time `(j, ι, r)` on role `w`. -/
noncomputable def gcnt (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (j : Stage) (ι : Fix 100) (r : Fin 8) (w : Role .complex 100) : ℕ :=
  (gateAt j ι r w).elim 0 fun g => ecnt cdat w (.gate g)

theorem stage_sum (F : Stage → ℕ) : ([Stage.one, .two, .three].map F).sum = ∑ j, F j := by
  have hu : (Finset.univ : Finset Stage) = {Stage.one, Stage.two, Stage.three} := rfl
  rw [hu, Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  simp

/-- **Calls of one node**: the role sums of the gate edges and the sink edge. -/
theorem cc_cxNodeOps (ρ f j0 : ℕ) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (childOf : ℕ → Ch) :
    cc (cxNodeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf) =
      ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, ∑ w : Role .complex 100, gcnt cdat j ι r w +
        ∑ w : Role .complex 100, ecnt cdat w (.sink w) := by
  unfold cxNodeOps
  simp only [cc_append, cc_flatMap, cc_map_prim, cc_cons, cc_nil, isCall_prim, isCall_relabel,
    isCall_gateOpC, Bool.false_eq_true, ↓reduceIte, add_zero, zero_add, cc_coreEdgeOpsAt,
    Finset.sum_map_toList, ← Fin.sum_univ_def, stage_sum, Finset.sum_const_zero]
  refine Nat.add_right_cancel_iff.mpr ?_
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun ι _ =>
    Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun w _ => ?_))))
  unfold gcnt
  cases gateAt j ι r w with
  | none => rfl
  | some g => exact cc_coreEdgeOpsAt ρ f j0 cdat childOf w _

end Node

/-! ## The bridge: gate times and edge heads of one role -/

section Bridge

/-- The key `(stage, invocation, time)` of a gate. -/
def gkey (g : Gate 100) : Stage × (Fix 100 × Fin 8) := (g.stage, (g.inv, g.time))

/-- The gates touching a role have pairwise distinct `(stage, time)`. -/
theorem touch_stage_time_nodup (w : Role .complex 100) :
    ((touch w).map fun g => (g.stage, g.time)).Nodup := by
  cases w with
  | X a =>
    have h : ((touch (Role.X a : Role .complex 100)).map fun g => (g.stage, g.time)) =
        [(Stage.one, (2 : Fin 8)), (Stage.one, 3), (Stage.one, 6), (Stage.one, 7),
         (Stage.two, 2), (Stage.two, 3), (Stage.two, 6), (Stage.two, 7),
         (Stage.three, 2), (Stage.three, 3), (Stage.three, 6), (Stage.three, 7)] := rfl
    rw [h]
    decide
  | Y a =>
    have h : ((touch (Role.Y a : Role .complex 100)).map fun g => (g.stage, g.time)) =
        [(Stage.one, (0 : Fin 8)), (Stage.one, 1), (Stage.one, 4), (Stage.one, 5),
         (Stage.two, 0), (Stage.two, 1), (Stage.two, 4), (Stage.two, 5),
         (Stage.three, 0), (Stage.three, 1), (Stage.three, 4), (Stage.three, 5)] := rfl
    rw [h]
    decide
  | side j ι p =>
    apply List.Nodup.of_map Prod.snd
    have h : (((touch (Role.side j ι p : Role .complex 100)).map fun g => (g.stage, g.time)).map
        Prod.snd) = [(0 : Fin 8), 2, 5, 7] := rfl
    rw [h]
    decide
  | center j ι c =>
    apply List.Nodup.of_map Prod.snd
    have h : (((touch (Role.center j ι c : Role .complex 100)).map fun g => (g.stage, g.time)).map
        Prod.snd) = [(1 : Fin 8), 3, 4, 6] := rfl
    rw [h]
    decide

theorem touch_keys_nodup (w : Role .complex 100) : ((touch w).map gkey).Nodup := by
  have h := touch_stage_time_nodup w
  have heq : ((touch w).map gkey).map (fun k => (k.1, k.2.2)) =
      (touch w).map fun g => (g.stage, g.time) := by
    rw [List.map_map]
    rfl
  exact List.Nodup.of_map (fun k => (k.1, k.2.2)) (by rw [heq]; exact h)

/-- Summing over all gate times `(j, ι, r)` the weight of the gate of `w` at that time visits each
gate of `touch w` exactly once. -/
theorem role_gates_gen (G : Gate 100 → ℕ) (w : Role .complex 100) :
    ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, (gateAt j ι r w).elim 0 G = ((touch w).map G).sum := by
  have hgate : ∀ (j : Stage) (ι : Fix 100) (r : Fin 8), gateAt j ι r w =
      (touch w).find? (fun g => decide (g.stage = j ∧ g.inv = ι ∧ g.time = r)) := by
    intro j ι r
    unfold gateAt
    exact congrArg (fun p => List.find? p (touch w)) (funext fun g => decide_eq_decide.mpr Iff.rfl)
  rw [← sum_find_eq (touch w) gkey
    (fun k g => decide (g.stage = k.1 ∧ g.inv = k.2.1 ∧ g.time = k.2.2)) ?_ (touch_keys_nodup w) G]
  · rw [Fintype.sum_prod_type (α₁ := Stage) (α₂ := Fix 100 × Fin 8)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type (α₁ := Fix 100) (α₂ := Fin 8)]
    refine Finset.sum_congr rfl (fun ι _ => Finset.sum_congr rfl (fun r _ => ?_))
    rw [hgate j ι r]
  · intro k g
    simp [gkey, Prod.ext_iff]

/-- The edges of `w` entering its gates, then the edge entering its sink, are exactly `edges w`,
each once (any weights `F`). -/
theorem role_edges_gen (F : Vertex .complex 100 × Vertex .complex 100 → ℕ) (w : Role .complex 100) :
    ((touch w).map fun g => (edgeInto w (.gate g)).elim 0 F).sum + (edgeInto w (.sink w)).elim 0 F =
      ((edges w).map F).sum := by
  set T : List (Vertex .complex 100) := (touch w).map Vertex.gate ++ [Vertex.sink w] with hTdef
  have hedges : edges w = (Vertex.source w :: T).zip T := rfl
  have htouch : (touch w).Nodup := List.Nodup.of_map gkey (touch_keys_nodup w)
  have hT : T.Nodup := by
    refine List.Nodup.append (htouch.map (fun a b h => Vertex.gate.inj h)) (List.nodup_singleton _)
      ?_
    intro x hx hx'
    rw [List.mem_singleton] at hx'
    subst hx'
    obtain ⟨g, -, hg⟩ := List.mem_map.1 hx
    cases hg
  have hv : ∀ v, (edgeInto w v).elim 0 F = (((Vertex.source w :: T).zip T).find?
      (fun e => @decide (e.2 = v) (Classical.propDecidable _))).elim 0 F := by
    intro v
    unfold edgeInto
    rw [hedges]
  have hp : ∀ (v : Vertex .complex 100) (e : Vertex .complex 100 × Vertex .complex 100),
      @decide (e.2 = v) (Classical.propDecidable _) = true ↔ e.2 = v :=
    fun v e => @decide_eq_true_iff (e.2 = v) (Classical.propDecidable _)
  have h1 := sum_heads (fun v e => @decide (e.2 = v) (Classical.propDecidable _)) hp F
    (Vertex.source w) T hT
  have h2 : ((touch w).map fun g => (edgeInto w (.gate g)).elim 0 F).sum +
      (edgeInto w (.sink w)).elim 0 F = (T.map fun v => (edgeInto w v).elim 0 F).sum := by
    rw [hTdef, List.map_append, List.sum_append, List.map_map]
    simp [Function.comp_def]
  rw [h2, List.map_congr_left (fun v _ => hv v), h1, ← hedges]

/-- **The multiplicity-preserving bridge (weighted form).** For every weight
`F w e` on the edges of the roles, summing the weight of the edge entering the gate of `w` at every
gate time `(j, ι, r)` (the order of the events of a network node), plus the weight of the edge
entering the sink of every role, gives the total weight of all edges `Σ_w Σ_{e ∈ edges w} F w e`. -/
theorem nodeEdgeSchedule_sum
    (F : Role .complex 100 → Vertex .complex 100 × Vertex .complex 100 → ℕ) :
    ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, ∑ w : Role .complex 100,
        (gateAt j ι r w).elim 0 (fun g => (edgeInto w (.gate g)).elim 0 (F w)) +
      ∑ w : Role .complex 100, (edgeInto w (.sink w)).elim 0 (F w) =
      ∑ w : Role .complex 100, ((edges w).map (F w)).sum := by
  have hswap : ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, ∑ w : Role .complex 100,
      (gateAt j ι r w).elim 0 (fun g => (edgeInto w (.gate g)).elim 0 (F w)) =
      ∑ w : Role .complex 100, ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8,
        (gateAt j ι r w).elim 0 (fun g => (edgeInto w (.gate g)).elim 0 (F w)) := by
    calc _ = ∑ j : Stage, ∑ ι : Fix 100, ∑ w : Role .complex 100, ∑ r : Fin 8,
          (gateAt j ι r w).elim 0 (fun g => (edgeInto w (.gate g)).elim 0 (F w)) :=
          Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun ι _ => Finset.sum_comm))
      _ = ∑ j : Stage, ∑ w : Role .complex 100, ∑ ι : Fix 100, ∑ r : Fin 8,
          (gateAt j ι r w).elim 0 (fun g => (edgeInto w (.gate g)).elim 0 (F w)) :=
          Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [role_gates_gen, role_edges_gen]

/-! ## The bridge as a permutation of lists -/

/-- The edges visited by one network node in event order: at every gate time `(j, ι, r)` (stage,
invocation, time) and for every role `w` touched then, the edge of `w` entering that gate; then the
edge entering the sink of every role (`cxNodeOps` runs the operations of exactly these edges, in
this order). -/
noncomputable def nodeEdgeSchedule :
    List (Role .complex 100 × (Vertex .complex 100 × Vertex .complex 100)) :=
  ([Stage.one, .two, .three].flatMap fun j => (Finset.univ : Finset (Fix 100)).toList.flatMap
    fun ι => (List.finRange 8).flatMap fun r =>
      (Finset.univ : Finset (Role .complex 100)).toList.flatMap fun w =>
        (gateAt j ι r w).elim [] fun g => (edgeInto w (.gate g)).toList.map fun e => (w, e)) ++
  (Finset.univ : Finset (Role .complex 100)).toList.flatMap fun w =>
    (edgeInto w (.sink w)).toList.map fun e => (w, e)

theorem count_map_eq {α β : Type*} [DecidableEq β] (a : β) (g : α → β) (l : List α) :
    List.count a (l.map g) = (l.map fun x => if g x = a then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.count_cons, ih, List.map_cons, List.sum_cons]
    by_cases h : g x = a
    · simp [h, Nat.add_comm]
    · simp [h]

theorem count_elim_list {T α : Type*} [DecidableEq T] (a : T) (o : Option α) (f : α → List T) :
    List.count a (o.elim [] f) = o.elim 0 (fun x => List.count a (f x)) := by
  cases o <;> rfl

theorem sum_toList_map {α : Type*} (o : Option α) (F : α → ℕ) :
    (o.toList.map F).sum = o.elim 0 F := by
  cases o <;> simp

/-- **The multiplicity-preserving bridge (permutation form).** The edges
visited by a network node in event order (`nodeEdgeSchedule`) are a permutation of the edges
`edges w` of all roles `w`, each tagged with its role. -/
theorem nodeEdgeSchedule_perm :
    nodeEdgeSchedule.Perm ((Finset.univ : Finset (Role .complex 100)).toList.flatMap
      fun w => (edges w).map fun e => (w, e)) := by
  classical
  rw [@List.perm_iff_count _ instBEqOfDecidableEq]
  intro a
  have key := nodeEdgeSchedule_sum (fun w e => if (w, e) = a then 1 else 0)
  beta_reduce at key
  unfold nodeEdgeSchedule
  simp only [List.count_append, List.count_flatMap, Function.comp_def, count_elim_list,
    count_map_eq, sum_toList_map, Finset.sum_map_toList, ← Fin.sum_univ_def,
    stage_sum]
  with_reducible exact key

end Bridge

/-! ## Dimensions of residuals -/

/-- An orthonormal basis of `E` has `dim E` vectors. -/
theorem isONB_length_eq {E : Submodule (ZMod 2) (Pt 100)} {B : List (Pt 100)} (hB : IsONB E B) :
    B.length = Module.finrank (ZMod 2) E := by
  have hli := CCoreWFAux.isONB_linearIndependent hB
  have h := linearIndependent_iff_card_eq_finrank_span.mp hli
  rw [Fintype.card_fin] at h
  rw [h]
  obtain ⟨-, -, hspan⟩ := hB
  have hrange : Set.range (fun i : Fin B.length => B.get i) = {v | v ∈ B} := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact List.mem_iff_get.mpr ⟨i, rfl⟩
    · intro hv
      exact List.mem_iff_get.mp hv
  rw [hrange, Set.finrank, hspan]

theorem edge_calls_eq (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hV : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) (w : Role .complex 100)
    (e : Vertex .complex 100 × Vertex .complex 100) (he : e ∈ edges w) :
    min (cdat e).basis.length (cdat e).eps.length = Module.finrank (ZMod 2) (residC e) := by
  obtain ⟨hONB, heps, -⟩ := hV w e he
  rw [heps, List.length_map, min_self]
  exact isONB_length_eq hONB

/-! ## The child count -/

theorem callCount_node {L : Layout} {β : Type} (k W : ℕ) (hW : 0 < W)
    (ops : List (RoleOp L β W (ProcK L β k))) :
    ProcK.callCount k [Model.Op.node W hW ops] = cc ops := rfl

/-- **Child count of one node level**, given the certificate total `Σ_e dim residual = s_c`. -/
theorem callCount_of_count
    (hcount : ∑ w : Role .complex 100,
      ((edges w).map fun e => Module.finrank (ZMod 2) (residC e)).sum = tripleSc 100) :
    CCoreCallCountStmt := by
  intro A K D S rr ρ kLeaf cdat hV k j0 hleaf
  rw [CCoreWFAux.cCoreProc_succ_of_not_lt hleaf]
  refine (callCount_node k Wc Wc_pos _).trans ?_
  rw [cc_cxNodeOps]
  have hb : ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, ∑ w : Role .complex 100, gcnt cdat j ι r w +
      ∑ w : Role .complex 100, ecnt cdat w (.sink w) =
      ∑ w : Role .complex 100,
        ((edges w).map fun e => min (cdat e).basis.length (cdat e).eps.length).sum :=
    nodeEdgeSchedule_sum (fun _ e => min (cdat e).basis.length (cdat e).eps.length)
  rw [hb, ← hcount]
  exact Finset.sum_congr rfl (fun w _ =>
    congrArg List.sum (List.map_congr_left (fun e he => edge_calls_eq cdat hV w e he)))

end CCoreCountsAux

/-! ## The non-call bound -/

namespace CCoreCountsAux

theorem len_flatMap_le {α γ : Type*} (l : List α) (f : α → List γ) (c : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ c) : (l.flatMap f).length ≤ l.length * c := by
  rw [List.length_flatMap]
  exact sum_map_le _ _ c h

theorem len_lineSteps {Ly : Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3) (op : Bool × ℤ × ℕ) :
    (lineSteps (Ly := Ly) (β := β) L K ρ f C op).length ≤ 3 := by
  simp only [lineSteps]
  split_ifs <;> simp

theorem len_topBitSteps {Ly : Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3) :
    (topBitSteps (Ly := Ly) (β := β) L K ρ f C).length ≤ 3 := by
  simp only [topBitSteps]
  split_ifs <;> simp

theorem len_packed {Ly : Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3) :
    (@id (List (Step Ly β)) (packedAddProc (Ly := Ly) (β := β) L K ρ f C)).length ≤ 28 := by
  show (eightOps.flatMap (lineSteps (Ly := Ly) (β := β) L K ρ f C) ++ [repairStep L K ρ f C] ++
    topBitSteps L K ρ f C).length ≤ 28
  rw [List.length_append, List.length_append, List.length_singleton]
  have h1 := len_flatMap_le eightOps (lineSteps (Ly := Ly) (β := β) L K ρ f C) 3
    (fun op _ => len_lineSteps L K ρ f C op)
  have h2 : eightOps.length = 8 := rfl
  have h3 := len_topBitSteps (Ly := Ly) (β := β) L K ρ f C
  omega

theorem len_map_prim0 {L : Layout} {β : Type} {W : ℕ} {Ch : Type} (p : ProcK L β 0) (k : Fin W) :
    (List.map (RoleOp.prim (Child := Ch) k) p).length = (@id (List (Step L β)) p).length :=
  List.length_map ..

/-- A bound on the operations of one edge with valid data. -/
def edgeOpsBound : ℕ :=
  (mH * (mH - 1) + 3 * mH) * 28 + mH * 4 + (mH * (mH - 1) + 3 * mH) * 28

theorem len_coreEdgeOps {A K D S rr : ℕ} {Ch : Type} (ρ f j0 : ℕ) (Dd : CxEdgeData)
    (childOf : ℕ → Ch) (k : Fin Wc) (e : Vertex .complex 100 × Vertex .complex 100)
    (hV : Dd.Valid e) :
    (coreEdgeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 Dd childOf k).length ≤
      edgeOpsBound := by
  obtain ⟨hONB, -, -, hInv, hM, -⟩ := hV
  have hB := CCoreWFAux.isONB_length_le hONB
  unfold edgeOpsBound
  simp only [coreEdgeOps, List.length_append]
  refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
  · refine le_trans (len_flatMap_le _ _ 28 (fun p _ => ?_)) (Nat.mul_le_mul_right 28 hInv)
    rw [len_map_prim0]
    exact len_packed _ _ _ _ _
  · refine le_trans (len_flatMap_le _ _ 4 (fun p _ => ?_)) (Nat.mul_le_mul_right 4 (le_trans ?_ hB))
    · split_ifs <;> simp
    · rw [List.length_zip, List.length_range]
      exact min_le_left _ _
  · refine le_trans (len_flatMap_le _ _ 28 (fun p _ => ?_)) (Nat.mul_le_mul_right 28 hM)
    rw [len_map_prim0]
    exact len_packed _ _ _ _ _

theorem len_coreEdgeOpsAt {A K D S rr : ℕ} {Ch : Type} (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hV : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) (childOf : ℕ → Ch)
    (w : Role .complex 100) (v : Vertex .complex 100) :
    (coreEdgeOpsAt (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf w v).length ≤
      edgeOpsBound := by
  unfold coreEdgeOpsAt
  cases h : edgeInto w v with
  | none => exact Nat.zero_le _
  | some e => exact len_coreEdgeOps ρ f j0 (cdat e) childOf (roleIdxC w) e (hV w e (FI.edgeInto_mem h))

/-- The node bound as a function of the cardinalities `nA = |Addr 100|`, `nF = |Fix 100|`,
`nR = |Role .complex 100|`: `nA + 3 (nF (8 (nR E + 1))) + nR E + 3 nA + 1` with `E = edgeOpsBound`
(the factors `3` and `8` are written as the lengths of the stage list and of `List.finRange 8`, as
they arise from `cxNodeOps`). -/
def nodeBoundOf (nA nF nR : ℕ) : ℕ :=
  nA + [Stage.one, Stage.two, Stage.three].length * (nF * ((List.finRange 8).length *
    (nR * edgeOpsBound + 1))) + nR * edgeOpsBound + nA * 3 + 1

/-- The explicit bound on the operations of one node: `nodeBoundOf |Addr 100| |Fix 100| |Role|`,
the cardinalities written as the lengths of the enumerations `Finset.univ.toList` that `cxNodeOps`
runs over (equal to `Fintype.card` by `Finset.length_toList` and `Finset.card_univ`). The proof
below only rewrites with the equation lemmas of `nodeBound`/`nodeBoundOf`, so the kernel never has
to evaluate these closed arithmetic expressions. -/
noncomputable def nodeBound : ℕ :=
  nodeBoundOf (Finset.univ : Finset (Addr 100)).toList.length
    (Finset.univ : Finset (Fix 100)).toList.length
    (Finset.univ : Finset (Role .complex 100)).toList.length

theorem len_cxNodeOps {A K D S rr : ℕ} {Ch : Type} (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hV : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) (childOf : ℕ → Ch) :
    (cxNodeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf).length ≤
      nodeBound := by
  unfold cxNodeOps
  rw [nodeBound, nodeBoundOf]
  rw [List.length_append, List.length_append, List.length_append, List.length_append]
  refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) ?_) ?_
  · exact Nat.le_of_eq (List.length_map _)
  · refine len_flatMap_le _ _ _ (fun j _ => ?_)
    refine len_flatMap_le _ _ _ (fun ι _ => ?_)
    refine len_flatMap_le _ _ _ (fun r _ => ?_)
    rw [List.length_append, List.length_singleton]
    refine Nat.add_le_add_right ?_ 1
    refine len_flatMap_le _ _ _ (fun w _ => ?_)
    cases gateAt j ι r w with
    | none => exact Nat.zero_le _
    | some g => exact len_coreEdgeOpsAt ρ f j0 cdat hV childOf w _
  · exact len_flatMap_le _ _ edgeOpsBound
      (fun w _ => len_coreEdgeOpsAt ρ f j0 cdat hV childOf w _)
  · exact len_flatMap_le _ _ 3 (fun a _ => Nat.le_of_eq rfl)
  · exact Nat.le_of_eq rfl

theorem nonCallCount_node {L : Layout} {β : Type} (k W : ℕ) (hW : 0 < W)
    (ops : List (RoleOp L β W (ProcK L β k))) :
    ProcK.nonCallCount k [Model.Op.node W hW ops] = (ops.filter fun o => !o.isCall).length := rfl

/-- **Non-call operations of one node level** are at most `nodeBound`. -/
theorem nonCallBound : CCoreNonCallBoundStmt := by
  refine ⟨nodeBound, ?_⟩
  intro A K D S rr ρ kLeaf cdat hV k j0 hleaf
  rw [CCoreWFAux.cCoreProc_succ_of_not_lt hleaf]
  refine (nonCallCount_node k Wc Wc_pos _).trans_le ?_
  exact le_trans (List.length_filter_le _ _) (len_cxNodeOps ρ (mH ^ k) j0 cdat hV _)

end CCoreCountsAux

/-- **Lemma A.10 (`lem:transfer-phase`) child count** (`CCoreCallCountStmt`): with valid complex edge data, one node
level of `cCoreProc` performs exactly `s_c = tripleSc 100` child calls: one per residual basis
vector of every edge (inverse kernels included), and `Σ_e dim residual = s_c` by the complex
certificate `complexNetCert_holds`. -/
theorem cCoreCallCount_holds : CCoreCallCountStmt :=
  CCoreCountsAux.callCount_of_count complexNetCert_holds.count

/-- **Lemma A.10 (`lem:transfer-phase`) non-call operations** (`CCoreNonCallBoundStmt`): one node level of `cCoreProc` has at most
`CCoreCountsAux.nodeBound` non-call operations, a constant independent of the shape, `k` and `j0`. -/
theorem cCoreNonCallBound_holds : CCoreNonCallBoundStmt :=
  CCoreCountsAux.nonCallBound

/-! ## Public names for the edge-schedule bridge -/

/-- **Edge schedule of one complex network node**. The edges visited by one node of
`cxNodeOps`, in event order, each tagged with its role: for every gate time `(j, ι, r)` (stage,
invocation, time) and every role `w` touched then, the edge of `w` entering that gate; then, for
every role, the edge entering its sink. `cxNodeOps` runs `coreEdgeOpsAt` on exactly these edges in
this order (formally: `cc_cxNodeOps` together with `cxNodeEdgeSchedule_sum`, packaged as
`cxNodeOps_callCount_edges`). -/
noncomputable def cxNodeEdgeSchedule :
    List (Role .complex 100 × (Vertex .complex 100 × Vertex .complex 100)) :=
  CCoreCountsAux.nodeEdgeSchedule

/-- **Event schedule ↔ edges, permutation form.** `cxNodeEdgeSchedule` is a
permutation of the list of all edges `e ∈ edges w` of all roles `w` (tagged `(w, e)`): every edge of
every role is visited exactly once by the event schedule of a network node. -/
theorem cxNodeEdgeSchedule_perm :
    cxNodeEdgeSchedule.Perm ((Finset.univ : Finset (Role .complex 100)).toList.flatMap
      fun w => (edges w).map fun e => (w, e)) :=
  CCoreCountsAux.nodeEdgeSchedule_perm

/-- **Event schedule ↔ edges, weighted form.** For any weights `F w e`, the total
weight over the gate events `(j, ι, r, w)` of a node (the edge of `w` entering its gate at that
time) plus the sink edges equals `Σ_w Σ_{e ∈ edges w} F w e`. -/
theorem cxNodeEdgeSchedule_sum
    (F : Role .complex 100 → Vertex .complex 100 × Vertex .complex 100 → ℕ) :
    ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, ∑ w : Role .complex 100,
        (gateAt j ι r w).elim 0 (fun g => (edgeInto w (.gate g)).elim 0 (F w)) +
      ∑ w : Role .complex 100, (edgeInto w (.sink w)).elim 0 (F w) =
      ∑ w : Role .complex 100, ((edges w).map (F w)).sum :=
  CCoreCountsAux.nodeEdgeSchedule_sum F

/-- **Child calls of one network node, edge by edge.** The operations of `cxNodeOps` with
`RoleOp.isCall` number `Σ_w Σ_{e ∈ edges w} min |basis e| |eps e|`, i.e. one per element of
`(range |basis|).zip eps` in `coreEdgeOps` of every edge (inverse kernels included). No validity
hypothesis is needed; for valid data the summand is `dim (residC e)` (`edge_calls_eq`). -/
theorem cxNodeOps_callCount_edges {A K D S rr : ℕ} {Ch : Type} (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (childOf : ℕ → Ch) :
    ((cxNodeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf).filter
        RoleOp.isCall).length =
      ∑ w : Role .complex 100,
        ((edges w).map fun e => min (cdat e).basis.length (cdat e).eps.length).sum :=
  (CCoreCountsAux.cc_cxNodeOps ρ f j0 cdat childOf).trans
    (CCoreCountsAux.nodeEdgeSchedule_sum fun _ e => min (cdat e).basis.length (cdat e).eps.length)

end SubNLogN.Math.Networks
