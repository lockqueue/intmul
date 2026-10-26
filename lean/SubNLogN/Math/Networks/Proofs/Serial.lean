import SubNLogN.Math.Networks.AppCFun

/-!
# Serialization of the framed network

Proves `serialEqFramed_holds : SerialEqFramedStmt h` for every `h` (statement in `AppCFun.lean`):
for both networks, any coefficient ring and module (in `Type`) and ARBITRARY edge operators `E`,
executing the event list `nodeEvents` sequentially equals the stage-parallel `framedNet`. No
hypothesis is used. All helpers live in the namespace `SerialAux`.

## Proof plan
* Locality. A role `w` belongs to invocation `(j, ι)` iff `invOf j w = some ι`.
  - The row of `(j, ι)` changes only roles of `(j, ι)` (`rowUpd_eq_of_invOf_ne`). On those roles it
    reads only roles of `(j, ι)` (`rowUpd_congr`).
  - The incoming edges at `(j, ι, r)` act only on wires with a gate at `(j, ι, r)`, which are roles
    of `(j, ι)` (`invOf_of_gateAt`), and they act pointwise.
  - Hence `framedInvocation j ι` has the same support and locality
    (`framedInvocation_eq_of_invOf_ne`, `framedInvocation_congr`).
* Edge events. A list of edge events on distinct roles acts pointwise
  (`runEvents_filterMap_edge`). The edge events at `(j, ι, r)` give `preEdges E j ι r`
  (`runEvents_gate`); the sink events give the sink step of `framedNet` (`runEvents_sink`).
* Invocations. The events of `(j, ι)` give `framedInvocation j ι` (`runEvents_inv`).
* Stages. Running the invocations of a stage one after the other, each once, in the order of
  `Finset.univ.toList`, equals the parallel `framedStage` (`foldl_local_eq`, `runEvents_stage`).
-/

namespace SubNLogN.Math.Networks

namespace SerialAux

variable {h : ℕ} {κ : Kind}

/-! ### Membership of roles in invocations -/

theorem fix_mk (j : Stage) (ι : Fix h) (S : Tri h) : (Addr.mk j ι S).fix j = ι := by
  cases j <;> rfl

theorem invOf_srcRole (j : Stage) (ι : Fix h) (T : Tri h) :
    invOf j (srcRole (κ := κ) j ι T) = some ι := by
  unfold srcRole
  split <;> simp [invOf, fix_mk]

theorem invOf_side (j : Stage) (ι : Fix h) (p : SideIdx κ h) :
    invOf j (Role.side j ι p) = some ι := by
  simp [invOf]

theorem invOf_center (j : Stage) (ι : Fix h) (c : Center κ h) :
    invOf j (Role.center j ι c) = some ι := by
  simp [invOf]

theorem invOf_of_tgtTriple {j : Stage} {ι : Fix h} {w : Role κ h} {S : Tri h}
    (hS : tgtTriple? j ι w = some S) : invOf j w = some ι := by
  cases w with
  | X a =>
    simp only [tgtTriple?, Option.ite_none_right_eq_some, Option.some.injEq] at hS
    simp [invOf, hS.1.2]
  | Y a =>
    simp only [tgtTriple?, Option.ite_none_right_eq_some, Option.some.injEq] at hS
    simp [invOf, hS.1.2]
  | side _ _ _ => simp [tgtTriple?] at hS
  | center _ _ _ => simp [tgtTriple?] at hS

theorem touch_invOf (w : Role κ h) : ∀ g ∈ touch w, invOf g.stage w = some g.inv := by
  cases w with
  | X a => simp [touch, invOf, Gate.stage, Gate.inv]
  | Y a => simp [touch, invOf, Gate.stage, Gate.inv]
  | side j ι p => simp [touch, invOf, Gate.stage, Gate.inv]
  | center j ι c => simp [touch, invOf, Gate.stage, Gate.inv]

/-- A wire with a gate at `(j, ι, r)` is a role of invocation `(j, ι)`. -/
theorem invOf_of_gateAt {j : Stage} {ι : Fix h} {r : Fin 8} {w : Role κ h} {g : Gate h}
    (hg : gateAt j ι r w = some g) : invOf j w = some ι := by
  unfold gateAt at hg
  have hm := List.mem_of_find?_eq_some hg
  have hp := List.find?_some hg
  simp only [decide_eq_true_eq] at hp
  obtain ⟨hs, hi, -⟩ := hp
  subst hs hi
  exact touch_invOf w g hm

/-! ### Rows: support and locality -/

section Rows

variable {Rg M : Type*} [CommRing Rg] [AddCommGroup M] [Module Rg M]

/-- The row of `(j, ι)` changes only roles of `(j, ι)`. -/
theorem rowUpd_eq_of_invOf_ne (half : Rg) (j : Stage) (ι : Fix h) (op : Op) (ε : Rg)
    (s : Role κ h → M) (w : Role κ h) (hw : invOf j w ≠ some ι) :
    rowUpd κ half j ι op ε s w = s w := by
  cases op with
  | V =>
    cases w with
    | side j' ι' p =>
      simp only [rowUpd]
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact hw (invOf_side _ _ _)
    | X a => rfl
    | Y a => rfl
    | center j' ι' c => rfl
  | G =>
    cases w with
    | center j' ι' c =>
      simp only [rowUpd]
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact hw (invOf_center _ _ _)
    | X a => rfl
    | Y a => rfl
    | side j' ι' p => rfl
  | J =>
    simp only [rowUpd]
    cases hS : tgtTriple? j ι w with
    | none => rfl
    | some S => exact absurd (invOf_of_tgtTriple hS) hw
  | R =>
    simp only [rowUpd]
    cases hS : tgtTriple? j ι w with
    | none => rfl
    | some S => exact absurd (invOf_of_tgtTriple hS) hw

theorem gatherVal_congr (j : Stage) (ι : Fix h) {s s' : Role κ h → M}
    (hss : ∀ w, invOf j w = some ι → s w = s' w) (c : Center κ h) :
    gatherVal j ι s c = gatherVal j ι s' c := by
  have hsrc : ∀ T, s (srcRole j ι T) = s' (srcRole j ι T) :=
    fun T => hss _ (invOf_srcRole j ι T)
  cases c <;> simp only [gatherVal, hsrc]

theorem sideVal_congr (half : Rg) (j : Stage) (ι : Fix h) {s s' : Role κ h → M}
    (hss : ∀ w, invOf j w = some ι → s w = s' w) (S : Tri h) :
    sideVal κ half j ι s S = sideVal κ half j ι s' S := by
  have hside : ∀ p, s (Role.side j ι p) = s' (Role.side j ι p) :=
    fun p => hss _ (invOf_side j ι p)
  simp only [sideVal, hside]

theorem scatterVal_congr (half : Rg) (j : Stage) (ι : Fix h) {s s' : Role κ h → M}
    (hss : ∀ w, invOf j w = some ι → s w = s' w) (S : Tri h) :
    scatterVal κ half j ι s S = scatterVal κ half j ι s' S := by
  have hcen : ∀ c, s (Role.center j ι c) = s' (Role.center j ι c) :=
    fun c => hss _ (invOf_center j ι c)
  cases κ <;> simp only [scatterVal, hcen]

/-- On the roles of `(j, ι)` the row of `(j, ι)` reads only roles of `(j, ι)`. -/
theorem rowUpd_congr (half : Rg) (j : Stage) (ι : Fix h) (op : Op) (ε : Rg)
    {s s' : Role κ h → M} (hss : ∀ w, invOf j w = some ι → s w = s' w)
    (w : Role κ h) (hw : invOf j w = some ι) :
    rowUpd κ half j ι op ε s w = rowUpd κ half j ι op ε s' w := by
  have hw' := hss w hw
  have hsrc : ∀ T, s (srcRole j ι T) = s' (srcRole j ι T) :=
    fun T => hss _ (invOf_srcRole j ι T)
  cases op with
  | V =>
    cases w with
    | side j' ι' p => simp only [rowUpd, hw', hsrc]
    | X a => exact hw'
    | Y a => exact hw'
    | center j' ι' c => exact hw'
  | G =>
    cases w with
    | center j' ι' c => simp only [rowUpd, hw', gatherVal_congr j ι hss]
    | X a => exact hw'
    | Y a => exact hw'
    | side j' ι' p => exact hw'
  | J => simp only [rowUpd, hw', sideVal_congr half j ι hss]
  | R => simp only [rowUpd, hw', scatterVal_congr half j ι hss]

end Rows

/-! ### Edges and framed invocations: support and locality -/

/-- The value written by the edge event of `w` entering `v` (the edge operator, if the edge
exists). -/
noncomputable def edgeVal {A : Type*} (E : EdgeOps κ h A) (w : Role κ h) (v : Vertex κ h)
    (x : A) : A :=
  match edgeInto w v with
  | some e => E w e x
  | none => x

section Generic

variable {A : Type*}

theorem preEdges_eq_of_invOf_ne (E : EdgeOps κ h A) (j : Stage) (ι : Fix h) (r : Fin 8)
    (s : Role κ h → A) (w : Role κ h) (hw : invOf j w ≠ some ι) :
    preEdges E j ι r s w = s w := by
  simp only [preEdges]
  cases hg : gateAt j ι r w with
  | none => rfl
  | some g => exact absurd (invOf_of_gateAt hg) hw

theorem preEdges_congr (E : EdgeOps κ h A) (j : Stage) (ι : Fix h) (r : Fin 8)
    {s s' : Role κ h → A} (w : Role κ h) (hw : s w = s' w) :
    preEdges E j ι r s w = preEdges E j ι r s' w := by
  simp only [preEdges, hw]

/-- Sequential execution of maps `G · ι` acting on the disjoint role classes
`{w | invOf j w = some ι}`, along a duplicate-free list of invocations, is the parallel map. -/
theorem foldl_local_eq (j : Stage) (G : (Role κ h → A) → Fix h → (Role κ h → A))
    (hsupp : ∀ s ι w, invOf j w ≠ some ι → G s ι w = s w)
    (hloc : ∀ s s' ι, (∀ w, invOf j w = some ι → s w = s' w) →
      ∀ w, invOf j w = some ι → G s ι w = G s' ι w) :
    ∀ (L : List (Fix h)), L.Nodup → ∀ (s : Role κ h → A) (w : Role κ h),
      L.foldl G s w = match invOf j w with
        | some ι => if ι ∈ L then G s ι w else s w
        | none => s w := by
  intro L
  induction L with
  | nil =>
    intro _ s w
    cases invOf j w <;> simp
  | cons ι₀ L ih =>
    intro hnd s w
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons, ih hnd.2]
    cases hw : invOf j w with
    | none => exact hsupp s ι₀ w (by simp [hw])
    | some ι =>
      dsimp only
      by_cases hιL : ι ∈ L
      · have hne : ι ≠ ι₀ := fun e => hnd.1 (e ▸ hιL)
        rw [if_pos hιL, if_pos (List.mem_cons_of_mem _ hιL)]
        refine hloc (G s ι₀) s ι (fun w' hw' => hsupp s ι₀ w' ?_) w hw
        rw [hw']
        exact fun e => hne (Option.some.inj e)
      · rw [if_neg hιL]
        by_cases he : ι = ι₀
        · subst he
          rw [if_pos List.mem_cons_self]
        · rw [if_neg (show ι ∉ ι₀ :: L by simp [he, hιL])]
          exact hsupp s ι₀ w (by rw [hw]; exact fun e => he (Option.some.inj e))

end Generic

section Framed

variable {Rg A : Type*} [CommRing Rg] [AddCommGroup A] [Module Rg A]

theorem foldl_step_eq_of_invOf_ne (half : Rg) (E : EdgeOps κ h A) (j : Stage) (ι : Fix h)
    (rs : List (Fin 8)) (s : Role κ h → A) (w : Role κ h) (hw : invOf j w ≠ some ι) :
    rs.foldl (fun s r => rowUpd κ half j ι (rowOp j r) ((rowSign j r : ℤ) : Rg)
      (preEdges E j ι r s)) s w = s w := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldl_cons, ih, rowUpd_eq_of_invOf_ne half j ι _ _ _ w hw,
      preEdges_eq_of_invOf_ne E j ι r s w hw]

theorem foldl_step_congr (half : Rg) (E : EdgeOps κ h A) (j : Stage) (ι : Fix h)
    (rs : List (Fin 8)) {s s' : Role κ h → A} (hss : ∀ w, invOf j w = some ι → s w = s' w) :
    ∀ w, invOf j w = some ι →
      rs.foldl (fun s r => rowUpd κ half j ι (rowOp j r) ((rowSign j r : ℤ) : Rg)
        (preEdges E j ι r s)) s w =
      rs.foldl (fun s r => rowUpd κ half j ι (rowOp j r) ((rowSign j r : ℤ) : Rg)
        (preEdges E j ι r s)) s' w := by
  induction rs generalizing s s' with
  | nil => exact hss
  | cons r rs ih =>
    apply ih
    intro w hw
    exact rowUpd_congr half j ι _ _ (fun w' hw' => preEdges_congr E j ι r w' (hss w' hw')) w hw

/-- A framed invocation changes only its own roles. -/
theorem framedInvocation_eq_of_invOf_ne (half : Rg) (E : EdgeOps κ h A) (j : Stage)
    (ι : Fix h) (s : Role κ h → A) (w : Role κ h) (hw : invOf j w ≠ some ι) :
    framedInvocation κ half E j ι s w = s w :=
  foldl_step_eq_of_invOf_ne half E j ι _ s w hw

/-- On its own roles a framed invocation reads only its own roles. -/
theorem framedInvocation_congr (half : Rg) (E : EdgeOps κ h A) (j : Stage) (ι : Fix h)
    {s s' : Role κ h → A} (hss : ∀ w, invOf j w = some ι → s w = s' w) (w : Role κ h)
    (hw : invOf j w = some ι) :
    framedInvocation κ half E j ι s w = framedInvocation κ half E j ι s' w :=
  foldl_step_congr half E j ι _ hss w hw

end Framed

/-! ### Running event lists -/

section Events

variable {Rg A : Type*} [CommRing Rg] [AddCommGroup A] [Module Rg A]

theorem runEvents_cons (half : Rg) (E : EdgeOps κ h A) (ev : NodeEvent κ h)
    (evs : List (NodeEvent κ h)) (s : Role κ h → A) :
    runEvents κ half E (ev :: evs) s = runEvents κ half E evs (ev.run κ half E s) := rfl

theorem runEvents_append (half : Rg) (E : EdgeOps κ h A) (l₁ l₂ : List (NodeEvent κ h))
    (s : Role κ h → A) :
    runEvents κ half E (l₁ ++ l₂) s = runEvents κ half E l₂ (runEvents κ half E l₁ s) := by
  unfold runEvents
  rw [List.foldl_append]

theorem runEvents_flatMap {α : Type*} (half : Rg) (E : EdgeOps κ h A) (l : List α)
    (f : α → List (NodeEvent κ h)) (s : Role κ h → A) :
    runEvents κ half E (l.flatMap f) s = l.foldl (fun s a => runEvents κ half E (f a) s) s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, runEvents_append, List.foldl_cons, ih]

theorem run_edge (half : Rg) (E : EdgeOps κ h A) (w : Role κ h) (v : Vertex κ h)
    (s : Role κ h → A) :
    (NodeEvent.edge w v).run κ half E s = Function.update s w (edgeVal E w v (s w)) := rfl

/-- Edge events on distinct roles act pointwise. -/
theorem runEvents_filterMap_edge {β : Type*} (half : Rg) (E : EdgeOps κ h A)
    (og : Role κ h → Option β) (vtx : Role κ h → β → Vertex κ h) :
    ∀ (L : List (Role κ h)), L.Nodup → ∀ (s : Role κ h → A),
      runEvents κ half E (L.filterMap fun w => (og w).map fun b => NodeEvent.edge w (vtx w b)) s =
        fun w => if w ∈ L then
          (match og w with
           | some b => edgeVal E w (vtx w b) (s w)
           | none => s w)
          else s w := by
  intro L
  induction L with
  | nil =>
    intro _ s
    funext w
    simp [runEvents]
  | cons w₀ L ih =>
    intro hnd s
    rw [List.nodup_cons] at hnd
    cases hog : og w₀ with
    | none =>
      have hl : (w₀ :: L).filterMap (fun w => (og w).map fun b => NodeEvent.edge w (vtx w b)) =
          L.filterMap (fun w => (og w).map fun b => NodeEvent.edge w (vtx w b)) :=
        List.filterMap_cons_none (by simp [hog])
      rw [hl, ih hnd.2 s]
      funext w
      by_cases hw : w = w₀
      · subst hw
        simp [hog, hnd.1]
      · simp [hw]
    | some b =>
      have hl : (w₀ :: L).filterMap (fun w => (og w).map fun b => NodeEvent.edge w (vtx w b)) =
          NodeEvent.edge w₀ (vtx w₀ b) ::
            L.filterMap (fun w => (og w).map fun b => NodeEvent.edge w (vtx w b)) :=
        List.filterMap_cons_some (by simp [hog])
      rw [hl, runEvents_cons, ih hnd.2, run_edge]
      funext w
      by_cases hw : w = w₀
      · subst hw
        simp [hog, hnd.1]
      · simp [hw]

/-- The edge events at `(j, ι, r)` give `preEdges E j ι r`. -/
theorem runEvents_gate (half : Rg) (E : EdgeOps κ h A) (j : Stage) (ι : Fix h) (r : Fin 8)
    (s : Role κ h → A) :
    runEvents κ half E ((Finset.univ : Finset (Role κ h)).toList.filterMap fun w =>
        (gateAt j ι r w).map fun g => NodeEvent.edge w (.gate g)) s = preEdges E j ι r s := by
  rw [runEvents_filterMap_edge half E (gateAt j ι r) (fun _ g => Vertex.gate g) _
    (Finset.nodup_toList _) s]
  funext w
  simp only [Finset.mem_toList, Finset.mem_univ, if_true, preEdges]
  cases gateAt j ι r w <;> rfl

/-- The final sink events give the sink step of `framedNet`. -/
theorem runEvents_sink (half : Rg) (E : EdgeOps κ h A) (t : Role κ h → A) :
    runEvents κ half E ((Finset.univ : Finset (Role κ h)).toList.map fun w =>
        NodeEvent.edge w (.sink w)) t = fun w => edgeVal E w (.sink w) (t w) := by
  have hl : ((Finset.univ : Finset (Role κ h)).toList.map fun w => NodeEvent.edge w (.sink w)) =
      (Finset.univ : Finset (Role κ h)).toList.filterMap fun w =>
        (some () : Option Unit).map fun _ => NodeEvent.edge w (.sink w) := by
    simp [List.filterMap_eq_map']
  rw [hl, runEvents_filterMap_edge half E (fun _ => (some () : Option Unit))
    (fun w _ => Vertex.sink w) _ (Finset.nodup_toList _) t]
  funext w
  simp

/-- The events of invocation `(j, ι)` give `framedInvocation j ι`. -/
theorem runEvents_inv (half : Rg) (E : EdgeOps κ h A) (j : Stage) (ι : Fix h)
    (s : Role κ h → A) :
    runEvents κ half E ((List.finRange 8).flatMap fun r =>
      ((Finset.univ : Finset (Role κ h)).toList.filterMap fun w =>
        (gateAt j ι r w).map fun g => NodeEvent.edge w (.gate g)) ++ [NodeEvent.row j ι r]) s =
      framedInvocation κ half E j ι s := by
  rw [runEvents_flatMap]
  simp only [runEvents_append, runEvents_gate]
  rfl

/-- The events of stage `j` (invocations one after the other) give the parallel `framedStage`. -/
theorem runEvents_stage (half : Rg) (E : EdgeOps κ h A) (j : Stage) (s : Role κ h → A) :
    runEvents κ half E ((Finset.univ : Finset (Fix h)).toList.flatMap fun ι =>
      (List.finRange 8).flatMap fun r =>
        ((Finset.univ : Finset (Role κ h)).toList.filterMap fun w =>
          (gateAt j ι r w).map fun g => NodeEvent.edge w (.gate g)) ++ [NodeEvent.row j ι r]) s =
      framedStage κ half E j s := by
  rw [runEvents_flatMap]
  simp only [runEvents_inv]
  funext w
  rw [foldl_local_eq j (fun s ι => framedInvocation κ half E j ι s)
    (fun s ι w hw => framedInvocation_eq_of_invOf_ne half E j ι s w hw)
    (fun s s' ι hss w hw => framedInvocation_congr half E j ι hss w hw) _
    (Finset.nodup_toList _) s w]
  cases hw : invOf j w <;> simp [framedStage, hw]

end Events

end SerialAux

open SerialAux in
/-- Serialization: for every `h`, both networks, any coefficient ring and module
(in `Type`) and arbitrary edge operators, executing `nodeEvents` sequentially equals `framedNet`. -/
theorem serialEqFramed_holds (h : ℕ) : SerialEqFramedStmt h := by
  intro κ Rg Ar _ _ _ half E s
  unfold nodeEvents
  rw [runEvents_append, runEvents_flatMap]
  simp only [List.foldl_cons, List.foldl_nil, runEvents_stage, runEvents_sink]
  funext w
  rfl

end SubNLogN.Math.Networks
