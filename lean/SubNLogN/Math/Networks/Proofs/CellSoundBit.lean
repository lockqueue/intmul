import SubNLogN.Math.Networks.Proofs.CellSoundRoles
import SubNLogN.Math.Networks.GeneralH

/-!
# Cell soundness for the bit network (key step of B4, [OAI26, §3.4, Prop. 7])

`SoundBitGenStmt h` (`GeneralH.lean`, every `h ≠ 9`) and its specialization `Cell.SoundBitStmt`
(`CellCalc.lean`, `h = 100`): along every role `w`, the rational ranks of the edge matrices
`A_e = M_head − M_tail` sum to the name-level class sum `Cell.classRankSum h (classOf w)`.
No hypotheses beyond `h ≠ 9`.

Proof. Write `P_U = projAlong β3 (labelSub β U)` (`β = betaB h`, `β3 = betaB3 h`). At gates and
sinks the frame is `M_v = P_{lab v}`; at the source it is `s₀ · P_{lab}` with `s₀ = −1` on `X`
(`M = −P_{U_a}`) and `s₀ = 1` elsewhere (there `lab = 0` and `P_0 = 0`). Hence the first edge of a
role has matrix `P_V − s₀ P_U`, every later edge `P_V − 1 · P_U`. Along the role the labels are the
instantiated class labels (`vlabels_eq`), so by `edge_rank` (cell calculus, `AGeom` of `ℚ` with
`I − J/9`, valid for `h ≠ 9`) the rank of the `i`-th edge is
`edgeRank h (if i = 0 then s₀ else 1) 1` of the `i`-th class edge: the summands of
`Cell.classRankSum` (`classRankSum_eq`, `sum_zipIdx_succ`).
-/

namespace SubNLogN.Math.Networks.WP6b

open Cell CellLib Module

variable {h : ℕ}

/-- `rank_ℚ (P_V − s · P_U)` for bit labels `U, V`. -/
noncomputable def rkB (h : ℕ) (s : ℤ) (U V : SymLabel h) : ℕ :=
  finrank ℚ (LinearMap.range (projAlong (betaB3 h) (labelSub (betaB h) V) -
    (s : ℚ) • projAlong (betaB3 h) (labelSub (betaB h) U)))

/-- At gates and sinks the bit frame is the projection onto the vertex label. -/
theorem frameB_of_ne_source {v : Vertex .bit h} (hv : ∀ u, v ≠ .source u) :
    frameB v = projAlong (betaB3 h) (labelSub (betaB h) (vlabel v)) := by
  cases v with
  | source u => exact absurd rfl (hv u)
  | gate g => rfl
  | sink u => rfl

/-- The source frame is `s₀ · P_{lab}` (`s₀ = −1` on `X`; elsewhere the label is `0`). -/
theorem frameB_source (w : Role .bit h) :
    frameB (.source w) =
      ((s0 (classOf w) : ℤ) : ℚ) • projAlong (betaB3 h) (labelSub (betaB h) (vlabel (.source w))) := by
  cases w with
  | X a =>
    show -projAlong (betaB3 h) (labelSub (betaB h) (labU a)) =
      ((-1 : ℤ) : ℚ) • projAlong (betaB3 h) (labelSub (betaB h) (labU a))
    module
  | Y a =>
    show (0 : Module.End ℚ (Cube h → ℚ)) =
      ((1 : ℤ) : ℚ) • projAlong (betaB3 h) (labelSub (betaB h) [])
    rw [show labelSub (betaB h) ([] : SymLabel h) = ⊥ from rfl, projAlong_bot, smul_zero]
  | side j ι p =>
    show (0 : Module.End ℚ (Cube h → ℚ)) =
      ((1 : ℤ) : ℚ) • projAlong (betaB3 h) (labelSub (betaB h) [])
    rw [show labelSub (betaB h) ([] : SymLabel h) = ⊥ from rfl, projAlong_bot, smul_zero]
  | center j ι c =>
    show (0 : Module.End ℚ (Cube h → ℚ)) =
      ((1 : ℤ) : ℚ) • projAlong (betaB3 h) (labelSub (betaB h) [])
    rw [show labelSub (betaB h) ([] : SymLabel h) = ⊥ from rfl, projAlong_bot, smul_zero]

/-- The first edge of a role: `rank (P_V − s₀ P_U)`. -/
theorem rkB_first (w : Role .bit h) {v : Vertex .bit h} (hv : ∀ u, v ≠ .source u) :
    rankQ (edgeMatB ((.source w, v) : Vertex .bit h × Vertex .bit h)) =
      rkB h (s0 (classOf w)) (vlabel (.source w)) (vlabel v) := by
  show finrank ℚ (LinearMap.range (frameB v - frameB (.source w))) = _
  rw [frameB_of_ne_source hv, frameB_source]
  rfl

/-- A later edge of a role: `rank (P_V − P_U)`. -/
theorem rkB_mid {u v : Vertex .bit h} (hu : ∀ x, u ≠ .source x) (hv : ∀ x, v ≠ .source x) :
    rankQ (edgeMatB ((u, v) : Vertex .bit h × Vertex .bit h)) = rkB h 1 (vlabel u) (vlabel v) := by
  show finrank ℚ (LinearMap.range (frameB v - frameB u)) = _
  rw [frameB_of_ne_source hu, frameB_of_ne_source hv]
  unfold rkB
  rw [Int.cast_one, one_smul]

/-- Transport of a sum over consecutive pairs along a map. -/
theorem sum_zip_tail_map {α γ : Type*} (f : α → γ) (F : γ → γ → ℕ) (l : List α) :
    ((l.zip l.tail).map fun e => F (f e.1) (f e.2)).sum =
      (((l.map f).zip (l.map f).tail).map fun e => F e.1 e.2).sum := by
  rw [zip_tail_map, List.map_map]
  rfl

/-- **Per-role bit soundness**: for a label field with `AGeom` (here `ℚ`, `I − J/9`, `h ≠ 9`), the
ranks of the edge matrices along a role sum to `Cell.classRankSum h (classOf w)`. -/
theorem role_rank_sum (hG : AGeom (betaB h) (betaB3 h)) (w : Role .bit h) :
    ((edges w).map fun e => rankQ (edgeMatB e)).sum = classRankSum h (classOf w) := by
  obtain ⟨v1, vs, hvert, hns⟩ := vertices_cons w
  have hlab : (classLabels (classOf w)).map (trLabel (roleNames w)) =
      vlabel (.source w) :: vlabel v1 :: vs.map vlabel := by
    rw [← vlabels_eq w, hvert, List.map_cons, List.map_cons]
  obtain ⟨L0, l', hcl, hL0, hl'⟩ := List.map_eq_cons_iff.1 hlab
  obtain ⟨L1, Ls, rfl, hL1, hLs⟩ := List.map_eq_cons_iff.1 hl'
  have hce : classEdges (classOf w) = (L0, L1) :: (L1 :: Ls).zip Ls := by
    simp only [classEdges, hcl, List.tail_cons, List.zip_cons_cons]
  have hedges : edges w = (.source w, v1) :: (v1 :: vs).zip vs := by
    simp only [edges, hvert, List.tail_cons, List.zip_cons_cons]
  have hgood : ∀ e ∈ classEdges (classOf w), GoodAll (betaB h) (roleNames w) (eR e) :=
    fun e he => goodAll_role (fun _ _ hST => betaB_nbr hST) w he
  -- the first edge
  have hfirst : rankQ (edgeMatB ((.source w, v1) : Vertex .bit h × Vertex .bit h)) =
      edgeRank h (s0 (classOf w)) 1 L0 L1 := by
    have he : (L0, L1) ∈ classEdges (classOf w) := by
      rw [hce]
      exact List.mem_cons_self
    have key : rkB h (s0 (classOf w)) (trLabel (roleNames w) L0) (trLabel (roleNames w) L1) =
        edgeRank h (s0 (classOf w)) 1 L0 L1 :=
      edge_rank hG (hgood _ he) (classEdges_ok _ _ he) (s0 (classOf w))
    rw [hL0, hL1] at key
    rw [← key]
    exact rkB_first w (hns v1 List.mem_cons_self)
  -- the later edges
  have hmap : (v1 :: vs).map vlabel = (L1 :: Ls).map (trLabel (roleNames w)) := by
    rw [List.map_cons, List.map_cons, hL1, hLs]
  have htail : (((v1 :: vs).zip vs).map fun e => rankQ (edgeMatB e)).sum =
      (((L1 :: Ls).zip Ls).map fun e => edgeRank h 1 1 e.1 e.2).sum := by
    calc (((v1 :: vs).zip vs).map fun e => rankQ (edgeMatB e)).sum
        = (((v1 :: vs).zip (v1 :: vs).tail).map fun e =>
            rkB h 1 (vlabel e.1) (vlabel e.2)).sum := by
          congr 1
          apply List.map_congr_left
          rintro ⟨x, y⟩ he
          have hm := List.of_mem_zip he
          exact rkB_mid (hns x hm.1) (hns y (List.mem_cons_of_mem _ hm.2))
      _ = ((((v1 :: vs).map vlabel).zip ((v1 :: vs).map vlabel).tail).map fun e =>
            rkB h 1 e.1 e.2).sum := sum_zip_tail_map vlabel (rkB h 1) (v1 :: vs)
      _ = ((((L1 :: Ls).map (trLabel (roleNames w))).zip
            ((L1 :: Ls).map (trLabel (roleNames w))).tail).map fun e => rkB h 1 e.1 e.2).sum := by
          rw [hmap]
      _ = (((L1 :: Ls).zip (L1 :: Ls).tail).map fun e =>
            rkB h 1 (trLabel (roleNames w) e.1) (trLabel (roleNames w) e.2)).sum :=
          (sum_zip_tail_map (trLabel (roleNames w)) (rkB h 1) (L1 :: Ls)).symm
      _ = (((L1 :: Ls).zip Ls).map fun e => edgeRank h 1 1 e.1 e.2).sum := by
          congr 1
          apply List.map_congr_left
          intro e he
          have he' : e ∈ classEdges (classOf w) := by
            rw [hce]
            exact List.mem_cons_of_mem _ he
          exact edge_rank hG (hgood _ he') (classEdges_ok _ _ he') 1
  calc ((edges w).map fun e => rankQ (edgeMatB e)).sum
      = rankQ (edgeMatB ((.source w, v1) : Vertex .bit h × Vertex .bit h)) +
          (((v1 :: vs).zip vs).map fun e => rankQ (edgeMatB e)).sum := by
        rw [hedges, List.map_cons, List.sum_cons]
    _ = edgeRank h (s0 (classOf w)) 1 L0 L1 +
          (((L1 :: Ls).zip Ls).map fun e => edgeRank h 1 1 e.1 e.2).sum := by
        rw [hfirst, htail]
    _ = classRankSum h (classOf w) := by
        rw [classRankSum_eq, hce, List.zipIdx_cons, List.map_cons, List.sum_cons,
          sum_zipIdx_succ ((L1 :: Ls).zip Ls) 0 (fun x s => edgeRank h s 1 x.1 x.2)
            (s0 (classOf w)) 1]
        simp

end SubNLogN.Math.Networks.WP6b

namespace SubNLogN.Math.Networks

/-- Cell soundness of the bit network for every `h ≠ 9` (`SoundBitGenStmt`). -/
theorem soundBitGen_holds (h : ℕ) (h9 : h ≠ 9) : SoundBitGenStmt h := fun w =>
  WP6b.role_rank_sum (WP6b.agBit (by exact_mod_cast h9)) w

/-- CONTRACT `Cell.SoundBitStmt` (cell soundness, bit network, `h = 100`). -/
theorem Cell.soundBit_holds : Cell.SoundBitStmt := soundBitGen_holds 100 (by norm_num)

end SubNLogN.Math.Networks
