import SubNLogN.Math.Networks.Proofs.LayerGuardCore

/-!
# Charge of one complex-network node of the Lemma A.10 (`lem:transfer-phase`) core (helper for `Prop71GuardStmt`)

`chg_cxNodeOps_le`: the sequential charge (`RoleOp.chg cs2 gateCharge cc`) of the role operations
`cxNodeOps` of one node is at most `gateSumOf gateCharge + 13 * Wc * mH * Bk` when every child
charges at most `Bk`. Here `gateSumOf c` is one charge `c` per gate row `(j, ι, r)` (a list sum
over the `3 · |Fix 100| · 8` rows), and `13 · W_c · m · Bk` bounds the child charges (each wire
meets at most `12` gate rows and has one sink edge, and each edge has at most `m` children since a
valid residual basis has at most `m` vectors). Masks, phases, row additions (address moves) and
the relabelling charge `0`.

To keep kernel elaboration
small, `cxNodeOps` is split into its five parts by a `rfl` equation and each part is bounded
separately; child charges are a generic `cc` with `cc (childOf t) ≤ Bk`. All counting is done
for abstract lists / index types and instantiated by application; no definition whose body is
closed arithmetic over `Wc` or `Fintype.card (Fix 100)` is ever unfolded (that would make the
kernel evaluate `Finset.univ`).
-/

namespace SubNLogN.Math.Networks.LayerGuardCount

open SubNLogN.Math.Networks SubNLogN.Math.Networks.Model SubNLogN.Math.Walsh
  SubNLogN.Math.Networks.LayerGuardRun SubNLogN.Math.Networks.LayerGuardSteps
  SubNLogN.Math.Networks.LayerGuardCore

/-! ## Sums over lists -/

theorem sum_map_append {γ : Type} (f : γ → ℕ) (l₁ l₂ : List γ) :
    ((l₁ ++ l₂).map f).sum = (l₁.map f).sum + (l₂.map f).sum := by
  simp [List.map_append, List.sum_append]

theorem sum_map_flatMap {α γ : Type} (f : γ → ℕ) (l : List α) (F : α → List γ) :
    ((l.flatMap F).map f).sum = (l.map fun x => ((F x).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem sum_map_eq_zero {α : Type} (l : List α) (F : α → ℕ) (h : ∀ x ∈ l, F x = 0) :
    (l.map F).sum = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a (List.mem_cons_self), ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem sum_map_le_length_mul {α : Type} (l : List α) (F : α → ℕ) (B : ℕ) (h : ∀ x ∈ l, F x ≤ B) :
    (l.map F).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a (List.mem_cons_self)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    rw [Nat.succ_mul]
    omega

/-! ## Every role meets at most twelve gate times -/

theorem touch_length_le {κ : Kind} (w : Role κ 100) : (touch w).length ≤ 12 := by
  cases w <;> simp [touch]

theorem gateAt_some {κ : Kind} {j : Stage} {ι : Fix 100} {r : Fin 8} {w : Role κ 100}
    {g : Gate 100} (h : gateAt j ι r w = some g) :
    g ∈ touch w ∧ g.stage = j ∧ g.inv = ι ∧ g.time = r := by
  unfold gateAt at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

/-! ## Gate rows -/

/-- Indicator bound for the edges of `w` before the row `(j, ι, r)`. -/
noncomputable def ind (Bk : ℕ) (j : Stage) (ι : Fix 100) (r : Fin 8) (w : Role .complex 100) : ℕ :=
  if (gateAt j ι r w).isSome then mH * Bk else 0

/-- Scalar work of one node: one gate charge `c` per row `(j, ι, r)`, as the list sum over the
rows (kept as a list sum, so that no closed cardinality arithmetic is ever unfolded). -/
noncomputable def gateSumOf (c : ℕ) : ℕ :=
  ([Stage.one, .two, .three].map fun _ => ((Finset.univ : Finset (Fix 100)).toList.map fun _ =>
    ((List.finRange 8).map fun _ => c).sum).sum).sum

theorem gateSumOf_eq (c : ℕ) : gateSumOf c =
    ([Stage.one, .two, .three].map fun _ => ((Finset.univ : Finset (Fix 100)).toList.map fun _ =>
      ((List.finRange 8).map fun _ => c).sum).sum).sum := rfl

/-! ## Generic list counting (no concrete `Finset.univ` is ever unfolded)

All counting is done for abstract lists and index types and then instantiated syntactically. -/

theorem sum_map_le_sum_map {α : Type} (l : List α) (f g : α → ℕ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem a hx))

theorem sum_map_congr {α : Type} (l : List α) {f g : α → ℕ} (h : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem sum_map_add_const {α : Type} (l : List α) (f : α → ℕ) (c : ℕ) :
    (l.map fun x => f x + c).sum = (l.map f).sum + l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

theorem sum_map_const' {α : Type} (l : List α) (c : ℕ) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

theorem sum_map_add' {α : Type} (l : List α) (f g : α → ℕ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem sum_map_comm {α β : Type} (l₁ : List α) (l₂ : List β) (f : α → β → ℕ) :
    (l₁.map fun a => (l₂.map fun b => f a b).sum).sum =
      (l₂.map fun b => (l₁.map fun a => f a b).sum).sum := by
  induction l₁ with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact (sum_map_eq_zero _ _ fun _ _ => rfl).symm
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    exact (sum_map_add' l₂ (fun b => f a b) (fun b => (l.map fun a => f a b).sum)).symm

theorem sum_swap4 {J I R Wt : Type} (LS : List J) (LF : List I) (LR : List R) (LW : List Wt)
    (H : J → I → R → Wt → ℕ) :
    (LS.map fun j => (LF.map fun ι => (LR.map fun r => (LW.map fun w => H j ι r w).sum).sum).sum).sum =
      (LW.map fun w => (LS.map fun j => (LF.map fun ι => (LR.map fun r => H j ι r w).sum).sum).sum).sum := by
  have e1 : ∀ j, (LF.map fun ι => (LR.map fun r => (LW.map fun w => H j ι r w).sum).sum).sum =
      (LW.map fun w => (LF.map fun ι => (LR.map fun r => H j ι r w).sum).sum).sum := by
    intro j
    have e2 : ∀ ι, (LR.map fun r => (LW.map fun w => H j ι r w).sum).sum =
        (LW.map fun w => (LR.map fun r => H j ι r w).sum).sum := fun ι =>
      sum_map_comm LR LW (fun r w => H j ι r w)
    rw [sum_map_congr LF fun ι _ => e2 ι]
    exact sum_map_comm LF LW (fun ι w => (LR.map fun r => H j ι r w).sum)
  rw [sum_map_congr LS fun j _ => e1 j]
  exact sum_map_comm LS LW (fun j w => (LF.map fun ι => (LR.map fun r => H j ι r w).sum).sum)

/-- An injective `Option`-valued map on a duplicate-free list `L` with values in `l` takes at most
`l.length` values `some _`; so the indicator sum is at most `l.length * c`. -/
theorem sum_ite_isSome_list_le {T G : Type} [DecidableEq G] (F : T → Option G) (c : ℕ) :
    ∀ (L : List T) (l : List G), L.Nodup → (∀ t ∈ L, ∀ g, F t = some g → g ∈ l) →
      (∀ t ∈ L, ∀ t' ∈ L, ∀ g, F t = some g → F t' = some g → t = t') →
      (L.map fun t => if (F t).isSome then c else 0).sum ≤ l.length * c := by
  intro L
  induction L with
  | nil => intro l _ _ _; simp
  | cons a L ih =>
    intro l hnd hmem hinj
    have ha : a ∉ L := (List.nodup_cons.mp hnd).1
    have hL : L.Nodup := (List.nodup_cons.mp hnd).2
    have hmemL : ∀ t ∈ L, ∀ g, F t = some g → g ∈ l := fun t ht g hg =>
      hmem t (List.mem_cons_of_mem _ ht) g hg
    have hinjL : ∀ t ∈ L, ∀ t' ∈ L, ∀ g, F t = some g → F t' = some g → t = t' :=
      fun t ht t' ht' g h1 h2 => hinj t (List.mem_cons_of_mem _ ht) t' (List.mem_cons_of_mem _ ht') g h1 h2
    simp only [List.map_cons, List.sum_cons]
    cases hFa : F a with
    | none =>
      show 0 + _ ≤ _
      rw [Nat.zero_add]
      exact ih l hL hmemL hinjL
    | some g =>
      have hg : g ∈ l := hmem a List.mem_cons_self g hFa
      have hmem' : ∀ t ∈ L, ∀ g', F t = some g' → g' ∈ l.erase g := by
        intro t ht g' hg'
        have hne : g' ≠ g := by
          intro heq
          rw [heq] at hg'
          exact ha ((hinj t (List.mem_cons_of_mem _ ht) a List.mem_cons_self g hg' hFa) ▸ ht)
        exact (List.mem_erase_of_ne hne).mpr (hmemL t ht g' hg')
      have key := ih (l.erase g) hL hmem' hinjL
      have hlen : (l.erase g).length + 1 = l.length := by
        rw [List.length_erase_of_mem hg]
        have := List.length_pos_of_mem hg
        omega
      calc c + (L.map fun t => if (F t).isSome then c else 0).sum
          ≤ c + (l.erase g).length * c := Nat.add_le_add_left key c
        _ = ((l.erase g).length + 1) * c := by ring
        _ = l.length * c := by rw [hlen]

theorem nodup_triples {J I R : Type} (LS : List J) (LF : List I) (LR : List R) (hS : LS.Nodup)
    (hF : LF.Nodup) (hR : LR.Nodup) :
    (LS.flatMap fun j => LF.flatMap fun ι => LR.map fun r => (j, ι, r)).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun j _ => ?_, hS.pairwise_of_forall_ne fun j _ j' _ hjj' => ?_⟩
  · refine List.nodup_flatMap.mpr ⟨fun ι _ => ?_, hF.pairwise_of_forall_ne fun ι _ ι' _ hιι' => ?_⟩
    · exact hR.map fun r r' h => congrArg (fun t : J × I × R => t.2.2) h
    · intro x hx hx'
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      obtain ⟨r', -, h⟩ := List.mem_map.mp hx'
      exact hιι' (congrArg (fun t : J × I × R => t.2.1) h).symm
  · intro x hx hx'
    obtain ⟨ι, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ι', -, hx'⟩ := List.mem_flatMap.mp hx'
    obtain ⟨r', -, h⟩ := List.mem_map.mp hx'
    exact hjj' (congrArg (fun t : J × I × R => t.1) h).symm

theorem sum_map_map' {α β : Type} (l : List α) (f : α → β) (g : β → ℕ) :
    ((l.map f).map g).sum = (l.map fun x => g (f x)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]

theorem sum_triples {J I R : Type} (LS : List J) (LF : List I) (LR : List R) (h : J → I → R → ℕ) :
    (LS.map fun j => (LF.map fun ι => (LR.map fun r => h j ι r).sum).sum).sum =
      ((LS.flatMap fun j => LF.flatMap fun ι => LR.map fun r => (j, ι, r)).map
        fun t => h t.1 t.2.1 t.2.2).sum := by
  rw [sum_map_flatMap]
  refine sum_map_congr _ fun j _ => ?_
  rw [sum_map_flatMap]
  refine sum_map_congr _ fun ι _ => ?_
  exact (sum_map_map' LR (fun r => (j, ι, r)) fun t => h t.1 t.2.1 t.2.2).symm

/-- Double counting of gate rows per wire, for abstract index lists. -/
theorem ind_list_gen {J I R Wt Gt : Type} [DecidableEq Gt] (LS : List J) (LF : List I) (LR : List R)
    (LW : List Wt) (hS : LS.Nodup) (hF : LF.Nodup) (hR : LR.Nodup) (c B : ℕ)
    (gA : J → I → R → Wt → Option Gt) (tch : Wt → List Gt) (htch : ∀ w, (tch w).length ≤ B)
    (hmem : ∀ j ι r w g, gA j ι r w = some g → g ∈ tch w)
    (hinj : ∀ j ι r j' ι' r' w g, gA j ι r w = some g → gA j' ι' r' w = some g →
      j = j' ∧ ι = ι' ∧ r = r') :
    (LS.map fun j => (LF.map fun ι => (LR.map fun r => (LW.map fun w =>
      if (gA j ι r w).isSome then c else 0).sum).sum).sum).sum ≤ LW.length * (B * c) := by
  have hw : ∀ w, (LS.map fun j => (LF.map fun ι => (LR.map fun r =>
      if (gA j ι r w).isSome then c else 0).sum).sum).sum ≤ B * c := by
    intro w
    rw [sum_triples]
    refine le_trans (sum_ite_isSome_list_le (fun t => gA t.1 t.2.1 t.2.2 w) c _ (tch w)
      (nodup_triples LS LF LR hS hF hR) (fun t _ g hg => hmem _ _ _ w g hg) ?_)
      (Nat.mul_le_mul_right c (htch w))
    rintro ⟨j, ι, r⟩ - ⟨j', ι', r'⟩ - g hg hg'
    obtain ⟨h1, h2, h3⟩ := hinj j ι r j' ι' r' w g hg hg'
    rw [h1, h2, h3]
  rw [sum_swap4]
  exact le_trans (sum_map_le_sum_map _ _ (fun _ => B * c) fun w _ => hw w)
    (le_of_eq (sum_map_const' LW _))

/-- The gate-row sum for abstract index lists. -/
theorem gpart_list {J I R Wt : Type} (LS : List J) (LF : List I) (LR : List R) (LW : List Wt)
    (G T : ℕ) (F ind' : J → I → R → Wt → ℕ) (hF : ∀ j ι r w, F j ι r w ≤ ind' j ι r w)
    (hT : (LS.map fun j => (LF.map fun ι => (LR.map fun r =>
      (LW.map fun w => ind' j ι r w).sum).sum).sum).sum ≤ T) :
    (LS.map fun j => (LF.map fun ι => (LR.map fun r =>
      (LW.map fun w => F j ι r w).sum + G).sum).sum).sum ≤
      (LS.map fun _ => (LF.map fun _ => (LR.map fun _ => G).sum).sum).sum + T := by
  have hmono : (LS.map fun j => (LF.map fun ι => (LR.map fun r =>
        (LW.map fun w => F j ι r w).sum).sum).sum).sum ≤
      (LS.map fun j => (LF.map fun ι => (LR.map fun r =>
        (LW.map fun w => ind' j ι r w).sum).sum).sum).sum :=
    sum_map_le_sum_map _ _ _ fun j _ => sum_map_le_sum_map _ _ _ fun ι _ =>
      sum_map_le_sum_map _ _ _ fun r _ => sum_map_le_sum_map _ _ _ fun w _ => hF j ι r w
  have hsplit : (LS.map fun j => (LF.map fun ι => (LR.map fun r =>
        (LW.map fun w => F j ι r w).sum + G).sum).sum).sum =
      (LS.map fun j => (LF.map fun ι => (LR.map fun r =>
        (LW.map fun w => F j ι r w).sum).sum).sum).sum +
        (LS.map fun _ => (LF.map fun _ => (LR.map fun _ => G).sum).sum).sum := by
    simp only [sum_map_add']
  rw [hsplit]
  omega

theorem ind_list_le (Bk : ℕ) :
    ([Stage.one, .two, .three].map fun j => ((Finset.univ : Finset (Fix 100)).toList.map fun ι =>
      ((List.finRange 8).map fun r => ((Finset.univ : Finset (Role .complex 100)).toList.map
        fun w => ind Bk j ι r w).sum).sum).sum).sum ≤ Wc * (12 * (mH * Bk)) := by
  have h := ind_list_gen [Stage.one, .two, .three] (Finset.univ : Finset (Fix 100)).toList
    (List.finRange 8) (Finset.univ : Finset (Role .complex 100)).toList (by decide)
    (Finset.nodup_toList _) (List.nodup_finRange 8) (mH * Bk) 12
    (fun j ι r w => gateAt j ι r w) (fun w => touch w) (fun w => touch_length_le w)
    (fun j ι r w g hg => (gateAt_some hg).1)
    (fun j ι r j' ι' r' w g hg hg' => ⟨(gateAt_some hg).2.1.symm.trans (gateAt_some hg').2.1,
      (gateAt_some hg).2.2.1.symm.trans (gateAt_some hg').2.2.1,
      (gateAt_some hg).2.2.2.symm.trans (gateAt_some hg').2.2.2⟩)
  rw [Finset.length_toList, Finset.card_univ] at h
  exact h

theorem gpart_le (Bk : ℕ) (F : Stage → Fix 100 → Fin 8 → Role .complex 100 → ℕ)
    (hF : ∀ j ι r w, F j ι r w ≤ ind Bk j ι r w) :
    ([Stage.one, .two, .three].map fun j => ((Finset.univ : Finset (Fix 100)).toList.map fun ι =>
      ((List.finRange 8).map fun r => ((Finset.univ : Finset (Role .complex 100)).toList.map
        fun w => F j ι r w).sum + gateCharge).sum).sum).sum
      ≤ gateSumOf gateCharge + Wc * (12 * (mH * Bk)) := by
  rw [gateSumOf_eq]
  exact gpart_list [Stage.one, .two, .three] (Finset.univ : Finset (Fix 100)).toList
    (List.finRange 8) (Finset.univ : Finset (Role .complex 100)).toList gateCharge _ F (ind Bk) hF
    (ind_list_le Bk)


/-- Pure arithmetic for the node total (all variables, so no closed term is evaluated). -/
theorem arith_node (E W M B : ℕ) : E + W * (12 * (M * B)) + W * (M * B) = E + 13 * W * M * B := by
  ring

/-- Assembly of the node total from the part bounds (all variables, so no closed term is
evaluated): masks and corrections `0`, gate rows `≤ E + W·12·M·B`, sink edges `≤ W·M·B`,
relabelling `0`. -/
theorem node_total (E W M B g s r : ℕ) (hg : g ≤ E + W * (12 * (M * B))) (hs : s ≤ W * (M * B))
    (hr : r = 0) : 0 + g + s + 0 + r ≤ E + 13 * W * M * B := by
  subst hr
  calc 0 + g + s + 0 + 0 = g + s := by omega
    _ ≤ E + W * (12 * (M * B)) + W * (M * B) := Nat.add_le_add hg hs
    _ = E + 13 * W * M * B := arith_node E W M B

/-! ## Edge operations -/

section Node

variable {A K D S rr : ℕ} {Child : Type}

theorem chg_coreEdgeOps_le (cc : Child → ℕ) (ρ f j0 : ℕ) (Dd : CxEdgeData) (childOf : ℕ → Child)
    (kk : Fin Wc) (Bk : ℕ) (hch : ∀ t, cc (childOf t) ≤ Bk) :
    ((coreEdgeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 Dd childOf kk).map
      (RoleOp.chg cs2 gateCharge cc)).sum ≤ Dd.basis.length * Bk := by
  have key : ∀ x y z n : ℕ, x = 0 → z = 0 → y ≤ n * Bk → x + y + z ≤ n * Bk := by
    intros; omega
  unfold coreEdgeOps
  simp only [sum_map_append, sum_map_flatMap]
  apply key
  · refine sum_map_eq_zero _ _ fun p _ => sum_map_eq_zero _ _ fun ro hro => ?_
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hro
    exact cs2_of_isMove (isMove_packed _ _ _ _ _ s hs)
  · refine sum_map_eq_zero _ _ fun p _ => sum_map_eq_zero _ _ fun ro hro => ?_
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hro
    exact cs2_of_isMove (isMove_packed _ _ _ _ _ s hs)
  · refine le_trans (sum_map_le_length_mul _ _ Bk fun p _ => ?_) ?_
    · split_ifs
      · simpa [RoleOp.chg] using hch p.1
      · simpa [RoleOp.chg, cs2, zSlot] using hch p.1
    · refine Nat.mul_le_mul_right _ ?_
      simp only [List.length_zip, List.length_range]
      exact min_le_left _ _

theorem chg_coreEdgeOpsAt_le (cc : Child → ℕ) (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) (childOf : ℕ → Child)
    (w : Role .complex 100) (v : Vertex .complex 100) (Bk : ℕ) (hch : ∀ t, cc (childOf t) ≤ Bk) :
    ((coreEdgeOpsAt (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf w v).map
      (RoleOp.chg cs2 gateCharge cc)).sum ≤ mH * Bk := by
  unfold coreEdgeOpsAt
  split
  · next e he =>
    have he' : e ∈ edges w := List.mem_of_find?_eq_some he
    calc _ ≤ (cdat e).basis.length * Bk := chg_coreEdgeOps_le cc ρ f j0 (cdat e) childOf _ Bk hch
      _ ≤ mH * Bk := Nat.mul_le_mul_right _ (valid_basis_length_le (hval w e he'))
  · simp

/-! ## The five parts of a node -/

/-- Source masks on the `X` roles. -/
noncomputable def partX (ρ f j0 : ℕ) : List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child) :=
  (Finset.univ : Finset (Addr 100)).toList.map fun a => .prim (roleIdxC (.X a)) (zMask ρ f j0 a)

/-- Gate rows with the incoming edges of the touched wires. -/
noncomputable def partG (ρ f j0 : ℕ) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (childOf : ℕ → Child) : List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child) :=
  [Stage.one, .two, .three].flatMap fun j => (Finset.univ : Finset (Fix 100)).toList.flatMap fun ι =>
    (List.finRange 8).flatMap fun r =>
      ((Finset.univ : Finset (Role .complex 100)).toList.flatMap fun w =>
        match gateAt j ι r w with
        | some g => coreEdgeOpsAt ρ f j0 cdat childOf w (.gate g)
        | none => []) ++ [gateOpC j ι r]

/-- Sink edges. -/
noncomputable def partSink (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (childOf : ℕ → Child) :
    List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child) :=
  (Finset.univ : Finset (Role .complex 100)).toList.flatMap fun w =>
    coreEdgeOpsAt ρ f j0 cdat childOf w (.sink w)

/-- Sink corrections. -/
noncomputable def partCorr (ρ f j0 : ℕ) : List (RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child) :=
  (Finset.univ : Finset (Addr 100)).toList.flatMap fun a =>
    [.prim (roleIdxC (.Y a)) (zMask ρ f j0 a),
     .prim (roleIdxC (.Y a)) (.recMap fun v => (Complex.I ^ (27 * f)) • v),
     .prim (roleIdxC (.X a)) (.recMap fun v => (-1 : ℂ) • v)]

theorem cxNodeOps_eq (ρ f j0 : ℕ) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (childOf : ℕ → Child) :
    cxNodeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf =
      partX ρ f j0 ++ partG ρ f j0 cdat childOf ++ partSink ρ f j0 cdat childOf ++ partCorr ρ f j0 ++
        [.relabel rhoPermC] := by
  -- unfold both sides first, so that `rfl` compares identical terms (a bare `rfl` may whnf
  -- `List.append` and evaluate `Finset.univ` of `Addr 100`)
  unfold cxNodeOps partX partG partSink partCorr
  rfl

theorem sum_partX (cc : Child → ℕ) (ρ f j0 : ℕ) :
    ((partX (A := A) (K := K) (D := D) (S := S) (rr := rr) (Child := Child) ρ f j0).map
      (RoleOp.chg cs2 gateCharge cc)).sum = 0 := by
  unfold partX
  refine sum_map_eq_zero _ _ fun x hx => ?_
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
  rfl

theorem sum_partCorr (cc : Child → ℕ) (ρ f j0 : ℕ) :
    ((partCorr (A := A) (K := K) (D := D) (S := S) (rr := rr) (Child := Child) ρ f j0).map
      (RoleOp.chg cs2 gateCharge cc)).sum = 0 := by
  unfold partCorr
  refine sum_map_eq_zero _ _ fun x hx => ?_
  obtain ⟨a, -, hx⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> rfl

theorem sum_partSink_le (cc : Child → ℕ) (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) (childOf : ℕ → Child)
    (Bk : ℕ) (hch : ∀ t, cc (childOf t) ≤ Bk) :
    ((partSink (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf).map
      (RoleOp.chg cs2 gateCharge cc)).sum ≤ Wc * (mH * Bk) := by
  unfold partSink
  rw [sum_map_flatMap, Finset.sum_map_toList]
  refine le_trans (Finset.sum_le_sum fun w _ =>
    chg_coreEdgeOpsAt_le cc ρ f j0 cdat hval childOf w (.sink w) Bk hch) ?_
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem sum_partG_le (cc : Child → ℕ) (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) (childOf : ℕ → Child)
    (Bk : ℕ) (hch : ∀ t, cc (childOf t) ≤ Bk) :
    ((partG (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf).map
      (RoleOp.chg cs2 gateCharge cc)).sum ≤ gateSumOf gateCharge + Wc * (12 * (mH * Bk)) := by
  unfold partG
  simp only [sum_map_flatMap, sum_map_append, List.map_singleton, List.sum_singleton]
  refine gpart_le Bk _ fun j ι r w => ?_
  unfold ind
  rcases hg : gateAt j ι r w with _ | g
  · simp
  · simpa using chg_coreEdgeOpsAt_le (A := A) (K := K) (D := D) (S := S) (rr := rr) cc ρ f j0 cdat
      hval childOf w (.gate g) Bk hch

/-- Charge of one node, for any child charges `cc` bounded by `Bk`. -/
theorem chg_cxNodeOps_le_gen (cc : Child → ℕ) (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) (childOf : ℕ → Child)
    (Bk : ℕ) (hch : ∀ t, cc (childOf t) ≤ Bk) :
    ((cxNodeOps (A := A) (K := K) (D := D) (S := S) (rr := rr) ρ f j0 cdat childOf).map
      (RoleOp.chg cs2 gateCharge cc)).sum ≤ gateSumOf gateCharge + 13 * Wc * mH * Bk := by
  rw [cxNodeOps_eq, sum_map_append, sum_map_append, sum_map_append, sum_map_append, sum_partX,
    sum_partCorr]
  have hG := sum_partG_le (A := A) (K := K) (D := D) (S := S) (rr := rr) cc ρ f j0 cdat hval
    childOf Bk hch
  have hS := sum_partSink_le (A := A) (K := K) (D := D) (S := S) (rr := rr) cc ρ f j0 cdat hval
    childOf Bk hch
  have hR : ([(RoleOp.relabel rhoPermC : RoleOp (layerLayout A K D S) (Fin rr → ℂ) Wc Child)].map
      (RoleOp.chg cs2 gateCharge cc)).sum = 0 := rfl
  exact node_total (gateSumOf gateCharge) Wc mH Bk _ _ _ hG hS hR

end Node

/-- **Charge of one complex-network node** of the Lemma A.10 (`lem:transfer-phase`) core: with children
of charge at most `Bk`, the node charges at most `gateSumOf gateCharge + 13 * Wc * mH * Bk`. -/
theorem chg_cxNodeOps_le {A₂ K D₂ S rr k : ℕ} (ρ f j0 : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (childOf : ℕ → ProcK (layerLayout A₂ K D₂ S) (Fin rr → ℂ) k) (Bk : ℕ)
    (hch : ∀ t, chargeK cs2 gateCharge k (childOf t) ≤ Bk) :
    ((cxNodeOps (A := A₂) (K := K) (D := D₂) (S := S) (rr := rr) ρ f j0 cdat childOf).map
      (RoleOp.chg cs2 gateCharge (chargeK cs2 gateCharge k))).sum ≤
        gateSumOf gateCharge + 13 * Wc * mH * Bk :=
  chg_cxNodeOps_le_gen (chargeK cs2 gateCharge k) ρ f j0 cdat hval childOf Bk hch

end SubNLogN.Math.Networks.LayerGuardCount
