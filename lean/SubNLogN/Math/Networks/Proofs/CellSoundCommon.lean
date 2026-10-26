import SubNLogN.Math.Networks.CellCalc

/-!
# Cell soundness, common part: name-level description of the network labels

Support for [OAI26] Lemma 6 (`Labels.lean`), `Lemma6OnbStmt` (`PhaseFrames.lean`) and the
cell-soundness contracts (`CellCalc.lean`).

* `trLabel nm L` instantiates a name-level label `L : Cell.ALabel`: the name `i` at coordinate `k`
  becomes the triple `nm k i`.
* `roleNames w`: the data roles `X a`, `Y a` name `a_k` at coordinate `k`; a side wire `A_{ST}` of
  stage `j` names `S` (name `0`) and `T` (name `1`) at the varying coordinate of `j` and the fixed
  triples of its invocation elsewhere; a central wire names the fixed triples of its invocation.
* `vlabels_eq`: along the vertex list of every role the labels are the instantiated name-level
  labels `Cell.classLabels (classOf w)` (proved by `rfl`).
* `vlabel_single`: every vertex label (also of gates touched by no role) is an instantiated
  name-level label that mentions only the name `0`.
* Name-level facts about the finitely many class edges (`classEdges_ok`, `classEdges_one`,
  `classEdges_inc_*`, `center_dec`), checked by `decide +kernel`.
* List bookkeeping: sums over the edges of a role as sums over the class edges.
-/

namespace SubNLogN.Math.Networks.WP6b

open Cell

variable {h : ℕ}

/-! ### Translation of name-level labels -/

/-- Instantiate a name-level token, `nm i` being the triple named `i`. -/
def trTok (nm : Fin 2 → Tri h) : ATok → Tok h
  | .zero => .zero
  | .full => .full
  | .line i => .line (nm i)
  | .perp i => .perp (nm i)
  | .perp2 => .perp2 (nm 0) (nm 1)

/-- Instantiate a name-level pure tensor coordinatewise. -/
def trSummand (nm : Fin 3 → Fin 2 → Tri h) (σ : ATok × ATok × ATok) : Summand h :=
  (trTok (nm 0) σ.1, trTok (nm 1) σ.2.1, trTok (nm 2) σ.2.2)

/-- Instantiate a name-level label. -/
def trLabel (nm : Fin 3 → Fin 2 → Tri h) (L : ALabel) : SymLabel h := L.map (trSummand nm)

/-- The coordinate varied at stage `j`. -/
def stageCoord : Stage → Fin 3
  | .one => 0
  | .two => 1
  | .three => 2

/-- Names of an invocation `ι` of stage `j`: `t` at the varying coordinate, the fixed triples of `ι`
at the other two coordinates. -/
def stageNames (j : Stage) (ι : Fix h) (t : Fin 2 → Tri h) : Fin 3 → Fin 2 → Tri h :=
  match j with
  | .one => ![t, fun _ => ι.1, fun _ => ι.2]
  | .two => ![fun _ => ι.1, t, fun _ => ι.2]
  | .three => ![fun _ => ι.1, fun _ => ι.2, t]

/-- The name assignment of a role. -/
def roleNames {κ : Kind} : Role κ h → Fin 3 → Fin 2 → Tri h
  | .X a => ![fun _ => a.1, fun _ => a.2.1, fun _ => a.2.2]
  | .Y a => ![fun _ => a.1, fun _ => a.2.1, fun _ => a.2.2]
  | .side j ι p => stageNames j ι ![p.1.1, p.1.2]
  | .center j ι _ => stageNames j ι (fun _ => ι.1)

theorem stageNames_coord (j : Stage) (ι : Fix h) (t : Fin 2 → Tri h) :
    stageNames j ι t (stageCoord j) = t := by
  cases j <;> rfl

theorem trLabel_aSide (j : Stage) (ι : Fix h) (r : Fin 8) (t : Fin 2 → Tri h) (i : Fin 2) :
    trLabel (stageNames j ι t) (aSide j r i) = gateLabel (.side j ι r (t i)) := by
  simp only [aSide, gateLabel]
  split_ifs <;> cases j <;> rfl

theorem trLabel_aCenter (j : Stage) (ι : Fix h) (r : Fin 8) (t : Fin 2 → Tri h) :
    trLabel (stageNames j ι t) (aCenter j r) = gateLabel (.center j ι r) := by
  simp only [aCenter, gateLabel]
  split_ifs <;> cases j <;> rfl

/-- The labels along the vertex list of a role are the instantiated class labels. -/
theorem vlabels_eq {κ : Kind} (w : Role κ h) :
    (vertices w).map vlabel = (classLabels (classOf w)).map (trLabel (roleNames w)) := by
  cases w with
  | X a => rfl
  | Y a => rfl
  | side j ι p => cases j <;> rfl
  | center j ι c => cases j <;> rfl

/-! ### Name-level checks (by `decide +kernel` on the finitely many class edges) -/

/-- Consecutive pairs of class labels: the name-level edges of a class. -/
def classEdges (c : RClass) : List (ALabel × ALabel) := (classLabels c).zip (classLabels c).tail

/-- Names mentioned by a name-level edge, per coordinate (as in `Cell.edgeDim`). -/
abbrev eR (e : ALabel × ALabel) : Fin 3 → List (Fin 2) := coordNames [e.1, e.2]

/-- Cells of the tail of a name-level edge. -/
abbrev cT (e : ALabel × ALabel) : List (Atom × Atom × Atom) := cells (eR e) e.1

/-- Cells of the head of a name-level edge. -/
abbrev cH (e : ALabel × ALabel) : List (Atom × Atom × Atom) := cells (eR e) e.2

/-- Name-level edge facts: duplicate-free cell lists and nested cell sets. -/
def EdgeOK (e : ALabel × ALabel) : Prop :=
  (cT e).Nodup ∧ (cH e).Nodup ∧ ((∀ x ∈ cT e, x ∈ cH e) ∨ (∀ x ∈ cH e, x ∈ cT e))

instance (e : ALabel × ALabel) : Decidable (EdgeOK e) := by unfold EdgeOK; infer_instance

/-- Where the name `1` may occur: only at the varying coordinate of a side class. -/
def oneOK : RClass → Fin 3 → Bool
  | .side j, k => decide (k = stageCoord j)
  | _, _ => false

theorem classEdges_ok (c : RClass) : ∀ e ∈ classEdges c, EdgeOK e := by
  cases c with
  | X => decide +kernel
  | Y => decide +kernel
  | side j => cases j <;> decide +kernel
  | center j => cases j <;> decide +kernel

theorem classEdges_one (c : RClass) :
    ∀ e ∈ classEdges c, ∀ k : Fin 3, (1 : Fin 2) ∈ eR e k → oneOK c k = true := by
  cases c with
  | X => decide +kernel
  | Y => decide +kernel
  | side j => cases j <;> decide +kernel
  | center j => cases j <;> decide +kernel

theorem classEdges_inc_X : ∀ e ∈ classEdges .X, ∀ x ∈ cT e, x ∈ cH e := by decide +kernel

theorem classEdges_inc_Y : ∀ e ∈ classEdges .Y, ∀ x ∈ cT e, x ∈ cH e := by decide +kernel

theorem classEdges_inc_side (j : Stage) : ∀ e ∈ classEdges (.side j), ∀ x ∈ cT e, x ∈ cH e := by
  cases j <;> decide +kernel

theorem classEdges_center (j : Stage) :
    classEdges (.center j) = [(([] : ALabel), aCenter j 1), (aCenter j 1, aCenter j 3),
      (aCenter j 3, aCenter j 4), (aCenter j 4, aCenter j 6), (aCenter j 6, [(.full, .full, .full)])] :=
  rfl

/-- The centre edges other than `3 → 4` are increasing at the name level. -/
theorem center_inc (j : Stage) :
    ∀ e ∈ [(([] : ALabel), aCenter j 1), (aCenter j 1, aCenter j 3), (aCenter j 4, aCenter j 6),
      (aCenter j 6, [(.full, .full, .full)])], ∀ x ∈ cT e, x ∈ cH e := by
  cases j <;> decide +kernel

/-- The centre edge `3 → 4` is decreasing at the name level and loses dimension `100`. -/
theorem center_dec (j : Stage) :
    (∀ x ∈ cH (aCenter j 3, aCenter j 4), x ∈ cT (aCenter j 3, aCenter j 4)) ∧
    ((cT (aCenter j 3, aCenter j 4)).map (cellDim 100 (eR (aCenter j 3, aCenter j 4)))).sum =
      ((cH (aCenter j 3, aCenter j 4)).map (cellDim 100 (eR (aCenter j 3, aCenter j 4)))).sum + 100 := by
  cases j <;> decide +kernel

theorem aSide_free (j : Stage) (r : Fin 8) : ∀ k : Fin 3, (1 : Fin 2) ∉ coordNames [aSide j r 0] k := by
  revert r; cases j <;> decide +kernel

theorem aCenter_free (j : Stage) (r : Fin 8) : ∀ k : Fin 3, (1 : Fin 2) ∉ coordNames [aCenter j r] k := by
  revert r; cases j <;> decide +kernel

/-- Every vertex label (also of gates touched by no role) is an instantiated name-level label that
mentions only the name `0`. -/
theorem vlabel_single {κ : Kind} (v : Vertex κ h) :
    ∃ (AL : ALabel) (nm : Fin 3 → Fin 2 → Tri h), vlabel v = trLabel nm AL ∧
      ∀ k : Fin 3, (1 : Fin 2) ∉ coordNames [AL] k := by
  cases v with
  | source w =>
    cases w with
    | X a => exact ⟨[(.line 0, .line 0, .line 0)], ![fun _ => a.1, fun _ => a.2.1, fun _ => a.2.2], rfl,
        by decide⟩
    | Y a => exact ⟨[], fun _ _ => a.1, rfl, by decide⟩
    | side j ι p => exact ⟨[], fun _ _ => ι.1, rfl, by decide⟩
    | center j ι c => exact ⟨[], fun _ _ => ι.1, rfl, by decide⟩
  | gate g =>
    cases g with
    | side j ι r t =>
      exact ⟨aSide j r 0, stageNames j ι (fun _ => t), (trLabel_aSide j ι r (fun _ => t) 0).symm,
        aSide_free j r⟩
    | center j ι r =>
      exact ⟨aCenter j r, stageNames j ι (fun _ => ι.1), (trLabel_aCenter j ι r (fun _ => ι.1)).symm,
        aCenter_free j r⟩
  | sink w =>
    cases w with
    | X a => exact ⟨[(.full, .full, .full)], fun _ _ => a.1, rfl, by decide⟩
    | Y a =>
      exact ⟨[(.perp 0, .full, .full), (.line 0, .perp 0, .full), (.line 0, .line 0, .perp 0)],
        ![fun _ => a.1, fun _ => a.2.1, fun _ => a.2.2], rfl, by decide⟩
    | side j ι p => exact ⟨[(.full, .full, .full)], fun _ _ => ι.1, rfl, by decide⟩
    | center j ι c => exact ⟨[(.full, .full, .full)], fun _ _ => ι.1, rfl, by decide⟩

/-- On a class edge of a role, the names `0` and `1` can both be mentioned at a coordinate only for
a side wire, at its varying coordinate, where they denote neighbouring triples. -/
theorem roleNames_one {κ : Kind} (w : Role κ h) {e : ALabel × ALabel} (he : e ∈ classEdges (classOf w))
    (k : Fin 3) (hk : (1 : Fin 2) ∈ eR e k) : Nbr κ (roleNames w k 0) (roleNames w k 1) := by
  have h1 := classEdges_one _ e he k hk
  cases w with
  | X a => simp [classOf, oneOK] at h1
  | Y a => simp [classOf, oneOK] at h1
  | side j ι p =>
    simp only [classOf, oneOK, decide_eq_true_eq] at h1
    subst h1
    simp only [roleNames, stageNames_coord]
    exact p.2
  | center j ι c => simp [classOf, oneOK] at h1

/-! ### List bookkeeping -/

theorem zip_tail_map {α β : Type*} (f : α → β) (l : List α) :
    (l.map f).zip (l.map f).tail = (l.zip l.tail).map (Prod.map f f) := by
  rw [← List.map_tail, List.zip_map]

/-- A sum over the edges of a role of a function of the two end labels equals the corresponding sum
over the class edges. -/
theorem sum_edges_labels {κ : Kind} {M : Type*} [AddCommMonoid M] (w : Role κ h)
    (G : SymLabel h → SymLabel h → M) :
    ((edges w).map fun e => G (vlabel e.1) (vlabel e.2)).sum =
      ((classEdges (classOf w)).map fun e =>
        G (trLabel (roleNames w) e.1) (trLabel (roleNames w) e.2)).sum := by
  have h1 : (edges w).map (fun e => G (vlabel e.1) (vlabel e.2)) =
      (((vertices w).map vlabel).zip ((vertices w).map vlabel).tail).map (fun e => G e.1 e.2) := by
    rw [zip_tail_map, List.map_map]; rfl
  rw [h1, vlabels_eq, zip_tail_map, List.map_map]; rfl

/-- The end labels of an edge of a role are those of a class edge. -/
theorem mem_edges_labels {κ : Kind} (w : Role κ h) {e : Vertex κ h × Vertex κ h} (he : e ∈ edges w) :
    ∃ e' ∈ classEdges (classOf w), vlabel e.1 = trLabel (roleNames w) e'.1 ∧
      vlabel e.2 = trLabel (roleNames w) e'.2 := by
  have h1 : (vlabel e.1, vlabel e.2) ∈
      (classEdges (classOf w)).map (Prod.map (trLabel (roleNames w)) (trLabel (roleNames w))) := by
    rw [classEdges, ← zip_tail_map, ← vlabels_eq, zip_tail_map]
    exact List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨e', he', hee⟩ := List.mem_map.1 h1
  exact ⟨e', he', (congrArg Prod.fst hee).symm, (congrArg Prod.snd hee).symm⟩

/-- The edges of a central wire. -/
theorem edges_center {κ : Kind} (j : Stage) (ι : Fix h) (c : Center κ h) :
    edges (Role.center j ι c) =
      [(.source (.center j ι c), .gate (.center j ι 1)), (.gate (.center j ι 1), .gate (.center j ι 3)),
        (.gate (.center j ι 3), .gate (.center j ι 4)), (.gate (.center j ι 4), .gate (.center j ι 6)),
        (.gate (.center j ι 6), .sink (.center j ι c))] :=
  rfl

/-- The sign of the source frame of a class (`−1` on `X`), as in `Cell.classRankSum`. -/
def s0 : RClass → ℤ
  | .X => -1
  | _ => 1

theorem sum_zipIdx_succ {α : Type*} (l : List α) (n : ℕ) (f : α → ℤ → ℕ) (a b : ℤ) :
    ((l.zipIdx (n + 1)).map fun e => f e.1 (if e.2 = 0 then a else b)).sum =
      (l.map fun x => f x b).sum := by
  induction l generalizing n with
  | nil => rfl
  | cons x l ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, Nat.add_one_ne_zero, if_false]
    rw [ih]

theorem classRankSum_eq (c : RClass) :
    classRankSum h c = ((classEdges c).zipIdx.map fun e =>
      edgeRank h (if e.2 = 0 then s0 c else 1) 1 e.1.1 e.1.2).sum := by
  cases c <;> rfl

/-- The vertex list of a role: its source, then a nonempty list of non-source vertices. -/
theorem vertices_cons {κ : Kind} (w : Role κ h) :
    ∃ v1 vs, vertices w = .source w :: v1 :: vs ∧ ∀ v ∈ v1 :: vs, ∀ u, v ≠ .source u := by
  have hne : (touch w).map Vertex.gate ++ [Vertex.sink w] ≠ [] := by simp
  obtain ⟨v1, vs, hv⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨v1, vs, ?_, ?_⟩
  · show [Vertex.source w] ++ ((touch w).map Vertex.gate ++ [Vertex.sink w]) = _
    rw [hv]; rfl
  · rw [← hv]
    intro v hv' u
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hv'
    rcases hv' with ⟨g, _, rfl⟩ | rfl <;> simp

end SubNLogN.Math.Networks.WP6b
