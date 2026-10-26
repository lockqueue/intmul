import SubNLogN.Math.Networks.AppCSafe
import SubNLogN.Math.Networks.Proofs.InterchangeWFProof

/-!
# Class safety of the explicit Proposition A.7 (`prop:transfer11`) procedure (`InterchangeProcClassSafeStmt`)

`interchangeProcClassSafe_holds : InterchangeProcClassSafeStmt` (`AppCSafe.lean`):
under `InterchangeHyps`, `interchangeProc q fac k h₀ d₀` run in class `c` is class safe
(`ProcK.ClassSafe`, recursively, children in their role sub-classes).

Proof (helpers in `SubNLogN.Math.Networks.InterchangeSafeAux`):
* membership in a row class depends only on the row field, so a pull map that fixes the row field
  preserves every class with that row field (`preservesClass_of_row`); role sub-classes
  `c.sub W hW k` have the same row field as `c`;
* every primitive of `interchangeProc` is an `Elem.pair` of the fields `h₀`, `d₀` (depth `0`) or an
  `Elem.shift`/`Elem.unit` of a coordinate block of the `H` or `D` chunk; all these fields lie after the
  row field (`c.row < h₀ ≤ d₀`), so the pulls fix the row field;
* a node needs a complete role split: `c.μ · W_b ∣ r_row` follows from `c.μ · W_b^{k+1} ∣ r_row`;
  the children run in `c.sub W_b k'`, whose modulus `c.μ · W_b` gives `(c.μ · W_b) · W_b^k ∣ r_row`;
* gates and relabellings are class safe by definition.
The induction on `k` carries the class-dependent hypotheses `SafeHyps` (row field before both chunks,
divisibility), which the children inherit. Membership facts are obtained by rewriting (no named binder
of a membership in a `Finset` built from `univ`).

Pitfall: never check a term (`exact`, `refine`, `apply`, even a placeholder proof) against a goal
`ProcK.ClassSafe (k+1) (interchangeProc …) c`: the implicit-lambda check `whnf`s the expected type,
which unfolds `List.Forall` and evaluates the concrete list (maximum recursion). The depth-`k+1` step
therefore first generalizes the procedure to a variable `p` (with `hp : interchangeProc … = p`).
-/

namespace SubNLogN.Math.Networks

open Model

namespace InterchangeSafeAux

open InterchangeWFAux

/-! ### Row fields and pulls -/

theorem sub_row {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W) :
    (c.sub W hW k).row = c.row := rfl

theorem sub_mu {L : Layout} (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W) :
    (c.sub W hW k).μ = c.μ * W := rfl

/-- A pull map fixing the row field preserves the class. -/
theorem preservesClass_of_row {L : Layout} (c : RowClass L) (f : L.Addr → L.Addr)
    (hf : ∀ x, f x c.row = x c.row) : PreservesClass c f := by
  intro x
  unfold RowClass.mem
  rw [hf x]

/-- `blockSet t₀ t₁` does not change fields before `t₀`. -/
theorem blockSet_before {L : Layout} {t₀ t₁ : ℕ} (x : L.Addr) (v : ℕ) (i : Fin L.n)
    (hi : i.val < t₀) : L.blockSet t₀ t₁ x v i = x i := by
  unfold Layout.blockSet
  rw [if_neg (fun h => by unfold inBlock at h; omega)]

theorem safe_shift {L : Layout} {β : Type} (c : RowClass L) {t₀ t₁ : ℕ} (off : L.Addr → ℕ)
    (h : c.row.val < t₀) : Step.ClassSafe (β := β) c (.elem (.shift t₀ t₁ off)) :=
  preservesClass_of_row c _ (fun x => blockSet_before x _ c.row h)

theorem safe_unit {L : Layout} {β : Type} (c : RowClass L) {t₀ t₁ u u' : ℕ}
    (h : c.row.val < t₀) : Step.ClassSafe (β := β) c (.elem (.unit t₀ t₁ u u' : Elem L)) :=
  preservesClass_of_row c _ (fun x => blockSet_before x _ c.row h)

theorem safe_pair {L : Layout} {β : Type} (c : RowClass L) (i j : Fin L.n)
    (g : Equiv.Perm (Fin (L.r i) × Fin (L.r j))) (hi : c.row ≠ i) (hj : c.row ≠ j) :
    Step.ClassSafe (β := β) c (.elem (.pair i j g)) :=
  preservesClass_of_row c _ (fun x => by
    show Function.update (Function.update x i (g.symm (x i, x j)).1) j (g.symm (x i, x j)).2 c.row =
      x c.row
    rw [Function.update_of_ne hj, Function.update_of_ne hi])

/-! ### Step lists -/

theorem safe_lowerSteps {L : Layout} {β : Type} (c : RowClass L) {R t₀ b : ℕ}
    (E : Matrix (Fin mH) (Fin mH) ℚ) (ht : c.row.val < t₀) :
    ∀ s ∈ lowerSteps (L := L) (β := β) R t₀ b E, Step.ClassSafe c s := by
  intro s hs
  obtain ⟨i, -, hs⟩ := List.mem_flatMap.1 hs
  have hb : c.row.val < (blk t₀ b i).1 := lt_of_lt_of_le ht (blk_fst_ge t₀ b i)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact safe_unit c hb
  · exact safe_shift c _ hb

theorem safe_subHSteps {L : Layout} {β : Type} (c : RowClass L) {R h₀ d₀ b : ℕ}
    (hD : c.row.val < d₀) : ∀ s ∈ subHSteps (L := L) (β := β) R h₀ d₀ b, Step.ClassSafe c s := by
  intro s hs
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
  exact safe_shift c _ (lt_of_lt_of_le hD (blk_fst_ge d₀ b i))

theorem safe_hMinusDSteps {L : Layout} {β : Type} (c : RowClass L) {R h₀ d₀ b : ℕ}
    (hD : c.row.val < d₀) :
    ∀ s ∈ hMinusDSteps (L := L) (β := β) R h₀ d₀ b, Step.ClassSafe c s := by
  intro s hs
  obtain ⟨i, -, hs⟩ := List.mem_flatMap.1 hs
  have hb : c.row.val < (blk d₀ b i).1 := lt_of_lt_of_le hD (blk_fst_ge d₀ b i)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact safe_unit c hb
  · exact safe_shift c _ hb

/-! ### Role operations of a node -/

theorem safe_prim {L : Layout} {β : Type} {W : ℕ} {Child : Type} {csafe : Child → RowClass L → Prop}
    {c : RowClass L} {hW : 0 < W} (kk : Fin W) {s : Step L β}
    (hs : Step.ClassSafe (c.sub W hW kk) s) : RoleOp.ClassSafe csafe c hW (.prim kk s) :=
  hs

/-- The Lemma A.6 (`lem:transfer-shear`) shear program of one edge on role `kk`: all its primitives act on blocks after the row field,
its children are class safe in the role sub-class. -/
theorem safe_shearOps {L : Layout} {β : Type} {W : ℕ} {Child : Type}
    {csafe : Child → RowClass L → Prop} {c : RowClass L} {hW : 0 < W} {R h₀ d₀ b : ℕ}
    (hH : c.row.val < h₀) (hD : c.row.val < d₀) (F : FacData)
    {childOf : Fin mH → Fin mH → Child} (kk : Fin W)
    (hch : ∀ i j, csafe (childOf i j) (c.sub W hW kk)) :
    ∀ o ∈ shearOps (L := L) (β := β) R h₀ d₀ b kk F childOf, RoleOp.ClassSafe csafe c hW o := by
  have hH' : (c.sub W hW kk).row.val < h₀ := by rw [sub_row]; exact hH
  have hD' : (c.sub W hW kk).row.val < d₀ := by rw [sub_row]; exact hD
  have hlow : ∀ (t₀ : ℕ) (E : Matrix (Fin mH) (Fin mH) ℚ), (c.sub W hW kk).row.val < t₀ →
      ∀ o ∈ (lowerSteps (L := L) (β := β) R t₀ b E).map (RoleOp.prim (Child := Child) kk),
        RoleOp.ClassSafe csafe c hW o := by
    intro t₀ E ht o ho
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ho
    exact safe_prim kk (safe_lowerSteps _ E ht s hs)
  intro o ho
  unfold shearOps at ho
  simp only [List.mem_append] at ho
  rcases ho with (((ho | ho) | ho) | ho) | ho
  · exact hlow d₀ F.E₂ hD' o ho
  · exact hlow h₀ F.E₁' hH' o ho
  · obtain ⟨p, -, ho⟩ := List.mem_flatMap.1 ho
    have hb : (c.sub W hW kk).row.val < (blk d₀ b p.2).1 :=
      lt_of_lt_of_le hD' (blk_fst_ge d₀ b p.2)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact safe_prim kk (safe_shift _ _ hb)
    · exact hch p.1 p.2
    · exact safe_prim kk (safe_unit _ hb)
    · exact safe_prim kk (safe_shift _ _ hb)
  · exact hlow h₀ F.E₁ hH' o ho
  · exact hlow d₀ F.E₂' hD' o ho

theorem safe_edgeOpsB {L : Layout} {β : Type} {Child : Type} {csafe : Child → RowClass L → Prop}
    {c : RowClass L} {R h₀ d₀ b : ℕ} (hH : c.row.val < h₀) (hD : c.row.val < d₀)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) {childOf : Fin mH → Fin mH → Child}
    (hch : ∀ (kk : Fin Wb) i j, csafe (childOf i j) (c.sub Wb Wb_pos kk))
    (w : Role .bit 100) (v : Vertex .bit 100) :
    ∀ o ∈ edgeOpsB (L := L) (β := β) R h₀ d₀ b fac childOf w v,
      RoleOp.ClassSafe csafe c Wb_pos o := by
  intro o ho
  unfold edgeOpsB at ho
  cases he : edgeInto w v with
  | none =>
    rw [he] at ho
    simp at ho
  | some e =>
    rw [he] at ho
    exact safe_shearOps hH hD _ (roleIdxB w) (hch (roleIdxB w)) o ho

theorem safe_gateOpB {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {Child : Type}
    {csafe : Child → RowClass L → Prop} (c : RowClass L) (j : Stage) (ι : Fix 100) (r : Fin 8) :
    RoleOp.ClassSafe csafe c Wb_pos (gateOpB (L := L) (β := β) (Child := Child) j ι r) :=
  trivial

/-- All role operations of a bit-network node are class safe, given class-safe edge programs. -/
theorem safe_bitNodeOps {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {Child : Type}
    {csafe : Child → RowClass L → Prop} {c : RowClass L} {R h₀ d₀ b : ℕ}
    {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData} {childOf : Fin mH → Fin mH → Child}
    (hedge : ∀ (w : Role .bit 100) (v : Vertex .bit 100),
      ∀ o ∈ edgeOpsB (L := L) (β := β) R h₀ d₀ b fac childOf w v,
        RoleOp.ClassSafe csafe c Wb_pos o) :
    ∀ o ∈ bitNodeOps (L := L) (β := β) R h₀ d₀ b fac childOf, RoleOp.ClassSafe csafe c Wb_pos o := by
  intro o ho
  unfold bitNodeOps at ho
  rcases List.mem_append.1 ho with ho | ho
  · rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨j, -, ho⟩ := List.mem_flatMap.1 ho
      obtain ⟨ι, -, ho⟩ := List.mem_flatMap.1 ho
      obtain ⟨r, -, ho⟩ := List.mem_flatMap.1 ho
      rcases List.mem_append.1 ho with ho | ho
      · obtain ⟨w, -, ho⟩ := List.mem_flatMap.1 ho
        cases hg : gateAt j ι r w with
        | none =>
          rw [hg] at ho
          simp at ho
        | some g =>
          rw [hg] at ho
          exact hedge w (.gate g) o ho
      · rw [List.mem_singleton] at ho
        subst ho
        exact safe_gateOpB c j ι r
    · obtain ⟨w, -, ho⟩ := List.mem_flatMap.1 ho
      exact hedge w (.sink w) o ho
  · rw [List.mem_singleton] at ho
    subst ho
    trivial

/-! ### The induction on the depth -/

/-- Class-dependent hypotheses of the induction (inherited by the children of a node). -/
structure SafeHyps (L : Layout) (k h₀ d₀ : ℕ) (c : RowClass L) : Prop where
  rowH : c.row.val < h₀
  rowD : c.row.val < d₀
  div : c.μ * Wb ^ k ∣ L.r c.row

theorem procSafe_zero {L : Layout} {β : Type} {p : List (Step L β)} {c : RowClass L}
    (h : ∀ s ∈ p, Step.ClassSafe c s) : ProcK.ClassSafe 0 p c := by
  show List.Forall (fun s => Step.ClassSafe c s) p
  exact List.forall_iff_forall_mem.2 h

theorem opSafe_node {L : Layout} {β : Type} {Child : Type} {csafe : Child → RowClass L → Prop}
    {c : RowClass L} {W : ℕ} {hW : 0 < W} {ops : List (RoleOp L β W Child)}
    (hc : CompleteRoles c W) (h : ∀ o ∈ ops, RoleOp.ClassSafe csafe c hW o) :
    Op.ClassSafe csafe c (Model.Op.node W hW ops) :=
  ⟨hc, h⟩

/-- `ProcK.ClassSafe` at depth `d + 1` from the membership form (stated for a variable procedure
`p : ProcK L β (d + 1)`). -/
theorem procSafe_succ' {L : Layout} {β : Type} {d : ℕ} {p : ProcK L β (d + 1)} {c : RowClass L}
    (h : ∀ o ∈ @id (List (Model.Op L β (ProcK L β d))) p, Op.ClassSafe (ProcK.ClassSafe d) c o) :
    ProcK.ClassSafe (d + 1) p c := by
  show List.Forall (fun o => Op.ClassSafe (ProcK.ClassSafe d) c o) p
  exact List.forall_iff_forall_mem.2 h

/-- Membership in a procedure equal to `A ++ [x] ++ B`, the appends being taken at type
`ProcK L β (d + 1)` (as in `interchangeProc_succ`, so that the equation is matched syntactically). -/
theorem mem_of_eq_append {L : Layout} {β : Type} {d : ℕ} {p : ProcK L β (d + 1)}
    {A B : List (Model.Op L β (ProcK L β d))} {x : Model.Op L β (ProcK L β d)}
    (hp : p = (A ++ [x] ++ B : ProcK L β (d + 1))) {o : Model.Op L β (ProcK L β d)}
    (ho : o ∈ @id (List (Model.Op L β (ProcK L β d))) p) : o ∈ A ∨ o = x ∨ o ∈ B := by
  rw [hp] at ho
  simp only [id, List.mem_append, List.mem_singleton] at ho
  rcases ho with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- Depth `0`: one digit interchange of the fields `h₀`, `d₀`, both after the row field. -/
theorem safe_zero {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) {h₀ d₀ : ℕ} {c : RowClass L}
    (H : SafeHyps L 0 h₀ d₀ c) :
    ProcK.ClassSafe 0 (interchangeProc (L := L) (β := β) q fac 0 h₀ d₀) c := by
  refine procSafe_zero (fun s hs => ?_)
  rw [interchangeProc_zero (L := L) (β := β) q fac h₀ d₀] at hs
  split_ifs at hs with hh
  · rw [List.mem_singleton] at hs
    subst hs
    refine safe_pair c _ _ _ (fun h => ?_) (fun h => ?_)
    · have := congrArg Fin.val h
      simp only at this
      have := H.rowH
      omega
    · have := congrArg Fin.val h
      simp only at this
      have := H.rowD
      omega
  · simp at hs

/-- The induction: `interchangeProc q fac k h₀ d₀` is class safe in `c` under `SafeHyps`. -/
theorem safe_main {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k : ℕ) :
    ∀ (h₀ d₀ : ℕ) (c : RowClass L), SafeHyps L k h₀ d₀ c →
      ProcK.ClassSafe k (interchangeProc (L := L) (β := β) q fac k h₀ d₀) c := by
  induction k with
  | zero => exact fun h₀ d₀ c H => safe_zero q fac H
  | succ k ih =>
    intro h₀ d₀ c H
    have hcomp : CompleteRoles c Wb :=
      ⟨Wb_pos, dvd_trans (Nat.mul_dvd_mul_left c.μ (dvd_pow_self Wb (Nat.succ_ne_zero k))) H.div⟩
    have hch : ∀ (kk : Fin Wb) (i j : Fin mH),
        ProcK.ClassSafe k (interchangeProc (L := L) (β := β) q fac k
          (h₀ + i.val * mH ^ k) (d₀ + j.val * mH ^ k)) (c.sub Wb Wb_pos kk) := by
      intro kk i j
      refine ih _ _ _ ⟨?_, ?_, ?_⟩
      · rw [sub_row]
        have := H.rowH
        omega
      · rw [sub_row]
        have := H.rowD
        omega
      · rw [sub_row, sub_mu, Nat.mul_assoc, ← pow_succ']
        exact H.div
    -- Generalize the procedure first. Checking a term against the expected type
    -- `ProcK.ClassSafe (k+1) (interchangeProc …) c` makes Lean `whnf` that type (implicit-lambda
    -- check `whnfForall`; `apply` likewise counts arrows with `forallMetaTelescopeReducing`), i.e.
    -- unfold it to `List.Forall _ (interchangeProc …)` and evaluate the concrete list down to
    -- `List.finRange mH` (maximum recursion). With a variable `p` that `whnf` is stuck at once.
    generalize hp : interchangeProc (L := L) (β := β) q fac (k + 1) h₀ d₀ = p
    refine procSafe_succ' (fun o ho => ?_)
    rcases mem_of_eq_append (hp.symm.trans (interchangeProc_succ (L := L) (β := β) q fac k h₀ d₀))
      ho with ho | ho | ho
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ho
      exact safe_subHSteps c H.rowD s hs
    · rw [ho]
      exact opSafe_node hcomp (safe_bitNodeOps (fun w v =>
        safe_edgeOpsB (csafe := ProcK.ClassSafe k) H.rowH H.rowD fac hch w v))
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ho
      exact safe_hMinusDSteps c H.rowD s hs

end InterchangeSafeAux

/-- **Class safety of Proposition A.7 (`prop:transfer11`)** (`InterchangeProcClassSafeStmt`, `AppCSafe.lean`): under
`InterchangeHyps`, every primitive of `interchangeProc q fac k h₀ d₀` run in class `c` (or in a role
sub-class of a node) has a pull map preserving its class (all pulls change only fields of the two
chunks, after the row field), every node has a complete role split, recursively in the children. -/
theorem interchangeProcClassSafe_holds : InterchangeProcClassSafeStmt := by
  intro L β _ _ q fac k h₀ d₀ c H
  refine InterchangeSafeAux.safe_main q fac k h₀ d₀ c
    ⟨H.2.2.2.2.2.2.2.1, ?_, H.2.2.2.2.2.2.2.2⟩
  have h1 := H.2.2.2.2.2.1
  have h2 := H.2.2.2.2.2.2.2.1
  omega

end SubNLogN.Math.Networks
