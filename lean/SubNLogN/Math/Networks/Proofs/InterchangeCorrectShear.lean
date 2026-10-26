import SubNLogN.Math.Networks.Proofs.InterchangeCorrectSteps
import SubNLogN.Math.Networks.Proofs.C4Specialize

/-!
# Proposition A.7 (`prop:transfer11`) correctness, part C: the Lemma A.6 (`lem:transfer-shear`) shear program `shearOps` at the block level

On role stream `k` of a node in class `c`, the Lemma A.6 (`lem:transfer-shear`) shear program `shearOps (q^b) h₀ d₀ b k F childOf`
(`AppCProc.lean`) for factorization data `F` valid for `M` (`FacData.Valid q M`) acts by the pull
`H ← H − (M mod q^b) D`, i.e. it realizes the shear `H ← H + M D`, provided every child call
`childOf i j` interchanges the coordinate blocks `H_i` and `D_j` (the induction hypothesis of Proposition A.7 (`prop:transfer11`)).
Pieces: `lowerSteps` (part B2), one pivot (`D_j ← D_j + H_i`, child interchange, `D_j ← H_i − D_j`
gives the pull `H_i ← H_i − D_j`), all pivots (pull `H ← H − Π D`, rows distinct), and the
factorization `M ≡ E₁ Π E₂ (mod q^b)` with `E₁ E₁' ≡ 1`, `E₂ E₂' ≡ 1`.
-/

namespace SubNLogN.Math.Networks

open Model

namespace InterchangeCorrect

variable {L : Layout}

/-- Role primitives `.prim k s` run the steps in the role class `c.sub W k`. -/
theorem run_prims {W : ℕ} (hW : 0 < W) {Child β : Type}
    (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L) (k : Fin W)
    (l : List (Step L β)) (A : L.Addr → β) :
    (l.map (RoleOp.prim k)).foldl (fun A o => o.run crun c hW A) A =
      l.foldl (fun A s => s.runIn (c.sub W hW k) A) A := by
  rw [List.foldl_map]
  rfl

/-! ### Both chunks at once -/

/-- Overwrite both chunks (`H` at `h₀`, `D` at `d₀`). -/
def setHD (L : Layout) (Q h₀ d₀ b : ℕ) (x : L.Addr) (H D : Fin mH → ZMod Q) : L.Addr :=
  setCoords L Q d₀ b (setCoords L Q h₀ b x H) D

theorem coordsH_setHD {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (x : L.Addr)
    (H D : Fin mH → ZMod (q ^ b)) :
    coords L (q ^ b) h₀ b (setHD L (q ^ b) h₀ d₀ b x H D) = H := by
  unfold setHD
  rw [coords_setCoords_D hT, coords_setCoords hT.H]

theorem coordsD_setHD {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (x : L.Addr)
    (H D : Fin mH → ZMod (q ^ b)) :
    coords L (q ^ b) d₀ b (setHD L (q ^ b) h₀ d₀ b x H D) = D := by
  unfold setHD
  rw [coords_setCoords hT.D]

theorem setCoordsD_setHD {q h₀ d₀ b : ℕ} (x : L.Addr) (H D D' : Fin mH → ZMod (q ^ b)) :
    setCoords L (q ^ b) d₀ b (setHD L (q ^ b) h₀ d₀ b x H D) D' = setHD L (q ^ b) h₀ d₀ b x H D' := by
  unfold setHD
  rw [setCoords_setCoords]

theorem setCoordsH_setHD {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (x : L.Addr)
    (H D H' : Fin mH → ZMod (q ^ b)) :
    setCoords L (q ^ b) h₀ b (setHD L (q ^ b) h₀ d₀ b x H D) H' = setHD L (q ^ b) h₀ d₀ b x H' D := by
  unfold setHD
  rw [← setCoords_comm hT, setCoords_setCoords]

theorem setHD_self {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (x : L.Addr) :
    setHD L (q ^ b) h₀ d₀ b x (coords L (q ^ b) h₀ b x) (coords L (q ^ b) d₀ b x) = x := by
  unfold setHD
  rw [setCoords_coords hT.H, setCoords_coords hT.D]

/-- `setCoords` of `H` alone, in `setHD` form. -/
theorem setCoordsH_eq_setHD {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (x : L.Addr)
    (H' : Fin mH → ZMod (q ^ b)) :
    setCoords L (q ^ b) h₀ b x H' = setHD L (q ^ b) h₀ d₀ b x H' (coords L (q ^ b) d₀ b x) := by
  conv_lhs => rw [← setHD_self hT x]
  rw [setCoordsH_setHD hT]

/-- `setCoords` of `D` alone, in `setHD` form. -/
theorem setCoordsD_eq_setHD {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (x : L.Addr)
    (D' : Fin mH → ZMod (q ^ b)) :
    setCoords L (q ^ b) d₀ b x D' = setHD L (q ^ b) h₀ d₀ b x (coords L (q ^ b) h₀ b x) D' := by
  conv_lhs => rw [← setHD_self hT x]
  rw [setCoordsD_setHD]

theorem mem_setHD {Q h₀ d₀ b : ℕ} (c : RowClass L) (hc : c.row.val < h₀) (hcd : c.row.val < d₀)
    (x : L.Addr) (H D : Fin mH → ZMod Q) : c.mem (setHD L Q h₀ d₀ b x H D) ↔ c.mem x := by
  unfold setHD
  rw [mem_setCoords c hcd, mem_setCoords c hc]

/-- Four class-restricted pulls compose (the later pulls preserve the class). -/
theorem cpull4 {β : Type} (P : L.Addr → Prop) [DecidablePred P] (p₁ p₂ p₃ p₄ : L.Addr → L.Addr)
    (h₂ : ∀ x, P x → P (p₂ x)) (h₃ : ∀ x, P x → P (p₃ x)) (h₄ : ∀ x, P x → P (p₄ x))
    (A : L.Addr → β) :
    cpull P p₄ (cpull P p₃ (cpull P p₂ (cpull P p₁ A))) = cpull P (p₁ ∘ p₂ ∘ p₃ ∘ p₄) A := by
  rw [cpull_cpull P p₁ p₂ h₂, cpull_cpull P (p₁ ∘ p₂) p₃ h₃,
    cpull_cpull P ((p₁ ∘ p₂) ∘ p₃) p₄ h₄]
  rfl

/-- Five class-restricted pulls compose (the later pulls preserve the class). -/
theorem cpull5 {β : Type} (P : L.Addr → Prop) [DecidablePred P]
    (p₁ p₂ p₃ p₄ p₅ : L.Addr → L.Addr) (h₂ : ∀ x, P x → P (p₂ x)) (h₃ : ∀ x, P x → P (p₃ x))
    (h₄ : ∀ x, P x → P (p₄ x)) (h₅ : ∀ x, P x → P (p₅ x)) (A : L.Addr → β) :
    cpull P p₅ (cpull P p₄ (cpull P p₃ (cpull P p₂ (cpull P p₁ A)))) =
      cpull P (p₁ ∘ p₂ ∘ p₃ ∘ p₄ ∘ p₅) A := by
  rw [cpull_cpull P p₁ p₂ h₂, cpull_cpull P (p₁ ∘ p₂) p₃ h₃,
    cpull_cpull P ((p₁ ∘ p₂) ∘ p₃) p₄ h₄, cpull_cpull P (((p₁ ∘ p₂) ∘ p₃) ∘ p₄) p₅ h₅]
  rfl

theorem cast_pow_sub_one {q : ℕ} (hq : 0 < q) (b : ℕ) :
    (((q ^ b - 1 : ℕ)) : ZMod (q ^ b)) = -1 := by
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), ZMod.natCast_self, Nat.cast_one, zero_sub]

theorem setCoords_setCoords_eq_setHD {Q h₀ d₀ b : ℕ} (x : L.Addr) (U V : Fin mH → ZMod Q) :
    setCoords L Q d₀ b (setCoords L Q h₀ b x U) V = setHD L Q h₀ d₀ b x U V := rfl

theorem setHD_setHD {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (x : L.Addr)
    (H D H' D' : Fin mH → ZMod (q ^ b)) :
    setHD L (q ^ b) h₀ d₀ b (setHD L (q ^ b) h₀ d₀ b x H D) H' D' = setHD L (q ^ b) h₀ d₀ b x H' D' := by
  show setCoords L (q ^ b) d₀ b (setCoords L (q ^ b) h₀ b (setHD L (q ^ b) h₀ d₀ b x H D) H') D' = _
  rw [setCoordsH_setHD hT, setCoordsD_setHD]

/-- The pull of the pivot shift `D_j ← D_j + H_i`. -/
theorem shiftDH_pull {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (i j : Fin mH) :
    (Elem.shift (blk d₀ b j).1 (blk d₀ b j).2
        (fun x => L.blockVal (blk h₀ b i).1 (blk h₀ b i).2 x)).pull =
      fun x => setHD L (q ^ b) h₀ d₀ b x (coords L (q ^ b) h₀ b x)
        (Function.update (coords L (q ^ b) d₀ b x) j
          (coords L (q ^ b) d₀ b x j - coords L (q ^ b) h₀ b x i)) := by
  funext x
  rw [shift_pull hT.D, setCoordsD_eq_setHD hT]
  rfl

/-- The pull of the unit `D_j ← −D_j`. -/
theorem unitD_pull {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (hq : 0 < q) (j : Fin mH) :
    (Elem.unit (blk d₀ b j).1 (blk d₀ b j).2 (q ^ b - 1) (q ^ b - 1)).pull =
      fun x => setHD L (q ^ b) h₀ d₀ b x (coords L (q ^ b) h₀ b x)
        (Function.update (coords L (q ^ b) d₀ b x) j (-coords L (q ^ b) d₀ b x j)) := by
  funext x
  rw [unit_pull hT.D, setCoordsD_eq_setHD hT, cast_pow_sub_one hq, neg_one_mul]

/-- The four role operations of one pivot `(i, j)` of `shearOps`. -/
def pivotOps {W : ℕ} {Child β : Type} (R h₀ d₀ b : ℕ) (k : Fin W)
    (childOf : Fin mH → Fin mH → Child) (p : Fin mH × Fin mH) : List (RoleOp L β W Child) :=
  [.prim k (.elem (.shift (blk d₀ b p.2).1 (blk d₀ b p.2).2
      (fun x => L.blockVal (blk h₀ b p.1).1 (blk h₀ b p.1).2 x))),
   .call k (childOf p.1 p.2),
   .prim k (.elem (.unit (blk d₀ b p.2).1 (blk d₀ b p.2).2 (R - 1) (R - 1))),
   .prim k (.elem (.shift (blk d₀ b p.2).1 (blk d₀ b p.2).2
      (fun x => L.blockVal (blk h₀ b p.1).1 (blk h₀ b p.1).2 x)))]

theorem shearOps_eq {W : ℕ} {Child β : Type} (R h₀ d₀ b : ℕ) (k : Fin W) (F : FacData)
    (childOf : Fin mH → Fin mH → Child) :
    shearOps (L := L) (β := β) R h₀ d₀ b k F childOf =
      (lowerSteps R d₀ b F.E₂).map (.prim k) ++ (lowerSteps R h₀ b F.E₁').map (.prim k) ++
        F.piv.flatMap (pivotOps R h₀ d₀ b k childOf) ++
        (lowerSteps R h₀ b F.E₁).map (.prim k) ++ (lowerSteps R d₀ b F.E₂').map (.prim k) := rfl

/-- One pivot acts by the pull `H_i ← H_i − D_j` on role `k` (child = interchange of `H_i`, `D_j`). -/
theorem run_pivotOps {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (hq : q.Prime) {W : ℕ} (hW : 0 < W)
    {Child β : Type} (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L)
    (hc : c.row.val < h₀) (k : Fin W) (childOf : Fin mH → Fin mH → Child)
    (hchild : ∀ (i j : Fin mH) (A : L.Addr → β), crun (childOf i j) (c.sub W hW k) A =
      (Step.swapBlocks (h₀ + i.val * b) (d₀ + j.val * b) b : Step L β).runIn (c.sub W hW k) A)
    (p : Fin mH × Fin mH) (A : L.Addr → β) :
    (pivotOps (L := L) (β := β) (q ^ b) h₀ d₀ b k childOf p).foldl (fun A o => o.run crun c hW A) A =
      cpull (c.sub W hW k).mem (fun x => setCoords L (q ^ b) h₀ b x
        (Function.update (coords L (q ^ b) h₀ b x) p.1
          (coords L (q ^ b) h₀ b x p.1 - coords L (q ^ b) d₀ b x p.2))) A := by
  obtain ⟨i, j⟩ := p
  have hcd : c.row.val < d₀ := lt_of_lt_of_le hc (le_trans (Nat.le_add_right _ _) hT.HD)
  have hc' : (c.sub W hW k).row.val < h₀ := hc
  have hcd' : (c.sub W hW k).row.val < d₀ := hcd
  have hmem : ∀ (y : L.Addr) (H D : Fin mH → ZMod (q ^ b)),
      (c.sub W hW k).mem y → (c.sub W hW k).mem (setHD L (q ^ b) h₀ d₀ b y H D) :=
    fun y H D hy => (mem_setHD (c.sub W hW k) hc' hcd' y H D).2 hy
  simp only [pivotOps, List.foldl_cons, List.foldl_nil, RoleOp.run, hchild, runIn_elem,
    swapBlocks_blk_runIn hT, shiftDH_pull hT, unitD_pull hT hq.pos]
  refine (cpull4 _ _ _ _ _ (fun x hx => ?_) (fun x hx => hmem _ _ _ hx)
    (fun x hx => hmem _ _ _ hx) A).trans ?_
  · exact (mem_setCoords (c.sub W hW k) hcd' _ _).2 ((mem_setCoords (c.sub W hW k) hc' _ _).2 hx)
  apply cpull_congr
  intro x _
  simp only [Function.comp]
  conv_lhs => rw [← setHD_self hT x]
  simp only [setCoords_setCoords_eq_setHD, coordsH_setHD hT, coordsD_setHD hT, setHD_setHD hT,
    Function.update_self, Function.update_idem, neg_sub, sub_sub_cancel, Function.update_eq_self]
  rw [setCoordsH_eq_setHD hT]

/-- All pivots (distinct rows) act by the pull `H ← H − Π D`. -/
theorem run_pivots {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (hq : q.Prime) {W : ℕ} (hW : 0 < W)
    {Child β : Type} (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)) (c : RowClass L)
    (hc : c.row.val < h₀) (k : Fin W) (childOf : Fin mH → Fin mH → Child)
    (hchild : ∀ (i j : Fin mH) (A : L.Addr → β), crun (childOf i j) (c.sub W hW k) A =
      (Step.swapBlocks (h₀ + i.val * b) (d₀ + j.val * b) b : Step L β).runIn (c.sub W hW k) A)
    (piv : List (Fin mH × Fin mH)) (hrows : (piv.map Prod.fst).Nodup) (A : L.Addr → β) :
    (piv.flatMap (pivotOps (L := L) (β := β) (q ^ b) h₀ d₀ b k childOf)).foldl
        (fun A o => o.run crun c hW A) A =
      cpull (c.sub W hW k).mem (fun x => setCoords L (q ^ b) h₀ b x
        (coords L (q ^ b) h₀ b x -
          (Matrix.of fun i j => if (i, j) ∈ piv then (1 : ZMod (q ^ b)) else 0).mulVec
            (coords L (q ^ b) d₀ b x))) A := by
  induction piv generalizing A with
  | nil =>
    simp only [List.flatMap_nil, List.foldl_nil]
    symm
    rw [cpull_congr _ (p' := id) (fun x _ => ?_), cpull_id]
    have h0 : (Matrix.of fun i j => if (i, j) ∈ ([] : List (Fin mH × Fin mH)) then
        (1 : ZMod (q ^ b)) else 0).mulVec (coords L (q ^ b) d₀ b x) = 0 := by
      funext i
      simp [Matrix.mulVec, dotProduct]
    rw [h0, sub_zero, setCoords_coords hT.H]
    rfl
  | cons p rest ih =>
    have hc' : (c.sub W hW k).row.val < h₀ := hc
    rw [List.map_cons, List.nodup_cons] at hrows
    rw [List.flatMap_cons, List.foldl_append,
      run_pivotOps hT hq hW crun c hc k childOf hchild p A, ih hrows.2,
      cpull_cpull (c.sub W hW k).mem _ _ (fun x hx => (mem_setCoords (c.sub W hW k) hc' _ _).2 hx)]
    apply cpull_congr
    intro x _
    simp only [Function.comp]
    rw [setCoordsH_eq_setHD hT x, coordsH_setHD hT, coordsD_setHD hT, setCoordsH_setHD hT,
      setCoordsH_eq_setHD hT x]
    refine congrArg (fun U => setHD L (q ^ b) h₀ d₀ b x U (coords L (q ^ b) d₀ b x)) ?_
    funext i'
    obtain ⟨i, j⟩ := p
    have hnot : ∀ j' : Fin mH, (i, j') ∉ rest := fun j' hmem =>
      hrows.1 (List.mem_map.2 ⟨(i, j'), hmem, rfl⟩)
    by_cases hi : i' = i
    · subst hi
      rw [Function.update_self]
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, List.mem_cons,
        Prod.mk.injEq, true_and, hnot, or_false, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, if_false, sub_zero]
    · rw [Function.update_of_ne hi]
      have hne : ∀ j' : Fin mH, ((i', j') = (i, j) ∨ (i', j') ∈ rest) ↔ (i', j') ∈ rest :=
        fun j' => ⟨fun h => h.elim (fun h' => absurd (Prod.mk.inj h').1 hi) id, Or.inr⟩
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, List.mem_cons, hne]

/-- A one-sided inverse of a square rational matrix is two-sided (stated for a generic size, so
that no instance is synthesized at the concrete size `mH`). -/
theorem ic_mul_comm_of_eq_one {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ} (h : A * B = 1) :
    B * A = 1 :=
  mul_eq_one_comm.mp h

/-- Valid factorization data reduce modulo `q^b` (`RatModMatrixMul`, `q`-integrality). -/
theorem facData_mod {q : ℕ} (hq : q.Prime) (b : ℕ) {M : Matrix (Fin mH) (Fin mH) ℚ} {F : FacData}
    (hF : F.Valid q M) :
    M.map (ratMod (q ^ b)) = F.E₁.map (ratMod (q ^ b)) *
        (Matrix.of fun i j => if (i, j) ∈ F.piv then (1 : ZMod (q ^ b)) else 0) *
        F.E₂.map (ratMod (q ^ b)) ∧
      F.E₁.map (ratMod (q ^ b)) * F.E₁'.map (ratMod (q ^ b)) = 1 ∧
      F.E₁'.map (ratMod (q ^ b)) * F.E₁.map (ratMod (q ^ b)) = 1 ∧
      F.E₂.map (ratMod (q ^ b)) * F.E₂'.map (ratMod (q ^ b)) = 1 ∧
      F.E₂'.map (ratMod (q ^ b)) * F.E₂.map (ratMod (q ^ b)) = 1 := by
  obtain ⟨_, _, _, _, h1, h2, _, _, _, hA, hQI, _⟩ := hF
  have hmul := ratModMatrixMul_holds mH q b hq
  have hE₁ : ∀ i j, QIntegral q (F.E₁ i j) := fun i j => (hQI i j).1
  have hE₁' : ∀ i j, QIntegral q (F.E₁' i j) := fun i j => (hQI i j).2.1
  have hE₂ : ∀ i j, QIntegral q (F.E₂ i j) := fun i j => (hQI i j).2.2.1
  have hE₂' : ∀ i j, QIntegral q (F.E₂' i j) := fun i j => (hQI i j).2.2.2
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin mH) (Fin mH) ℚ,
      P = Matrix.of fun i j => if (i, j) ∈ F.piv then (1 : ℚ) else 0 := ⟨_, rfl⟩
  rw [← hPdef] at hA
  have hP : ∀ i j, QIntegral q (P i j) := by
    intro i j
    rw [hPdef, Matrix.of_apply]
    split_ifs
    · exact C4SpecAux.qIntegral_one hq
    · exact C4SpecAux.qIntegral_zero hq
  have hone : (1 : Matrix (Fin mH) (Fin mH) ℚ).map (ratMod (q ^ b)) = 1 :=
    Matrix.map_one _ (C4SpecAux.ratMod_zero _) (C4SpecAux.ratMod_one _)
  have hPmod : P.map (ratMod (q ^ b)) =
      Matrix.of fun i j => if (i, j) ∈ F.piv then (1 : ZMod (q ^ b)) else 0 := by
    ext i j
    rw [Matrix.map_apply, hPdef, Matrix.of_apply, Matrix.of_apply]
    split_ifs
    · exact C4SpecAux.ratMod_one _
    · exact C4SpecAux.ratMod_zero _
  have h1' : F.E₁' * F.E₁ = 1 := ic_mul_comm_of_eq_one h1
  have h2' : F.E₂' * F.E₂ = 1 := ic_mul_comm_of_eq_one h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hA, hmul (F.E₁ * P) F.E₂ (C4SpecAux.qIntegral_mul_apply hq F.E₁ P hE₁ hP) hE₂,
      hmul F.E₁ P hE₁ hP, hPmod]
  · rw [← hmul F.E₁ F.E₁' hE₁ hE₁', h1, hone]
  · rw [← hmul F.E₁' F.E₁ hE₁' hE₁, h1', hone]
  · rw [← hmul F.E₂ F.E₂' hE₂ hE₂', h2, hone]
  · rw [← hmul F.E₂' F.E₂ hE₂' hE₂, h2', hone]

/-- **Lemma A.6 (`lem:transfer-shear`) at the block level.** On role `k`, `shearOps` for data valid for `M` acts by the pull
`H ← H − (M mod q^b) D` (it realizes `H ← H + M D`), given that the child calls interchange
coordinate blocks. -/
theorem run_shearOps {q h₀ d₀ b : ℕ} (hT : TwoChunks L q h₀ d₀ b) (hq : q.Prime) {W : ℕ}
    (hW : 0 < W) {Child β : Type} (crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β))
    (c : RowClass L) (hc : c.row.val < h₀) (k : Fin W) (childOf : Fin mH → Fin mH → Child)
    (hchild : ∀ (i j : Fin mH) (A : L.Addr → β), crun (childOf i j) (c.sub W hW k) A =
      (Step.swapBlocks (h₀ + i.val * b) (d₀ + j.val * b) b : Step L β).runIn (c.sub W hW k) A)
    (M : Matrix (Fin mH) (Fin mH) ℚ) (F : FacData) (hF : F.Valid q M) (A : L.Addr → β) :
    (shearOps (L := L) (β := β) (q ^ b) h₀ d₀ b k F childOf).foldl
        (fun A o => o.run crun c hW A) A =
      cpull (c.sub W hW k).mem (fun x => setCoords L (q ^ b) h₀ b x
        (coords L (q ^ b) h₀ b x - (M.map (ratMod (q ^ b))).mulVec (coords L (q ^ b) d₀ b x))) A := by
  have hcd : c.row.val < d₀ := lt_of_lt_of_le hc (le_trans (Nat.le_add_right _ _) hT.HD)
  obtain ⟨hAmod, h11', h1'1, h22', h2'2⟩ := facData_mod hq b hF
  obtain ⟨hL1, hL1', hL2, hL2', h1, h2, hnd1, _, _, _, hQI, hdiag⟩ := hF
  have h1' : F.E₁' * F.E₁ = 1 := ic_mul_comm_of_eq_one h1
  have h2' : F.E₂' * F.E₂ = 1 := ic_mul_comm_of_eq_one h2
  have hc' : (c.sub W hW k).row.val < h₀ := hc
  have hcd' : (c.sub W hW k).row.val < d₀ := hcd
  rw [shearOps_eq, List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_append,
    run_prims, run_prims, run_prims, run_prims,
    run_lowerSteps hT.D hq (c.sub W hW k) hcd' F.E₂ F.E₂' hL2 h2
      (fun i j => ⟨(hQI i j).2.2.1, (hQI i j).2.2.2⟩) (fun i => (hdiag i).2.2.1),
    run_lowerSteps hT.H hq (c.sub W hW k) hc' F.E₁' F.E₁ hL1' h1'
      (fun i j => ⟨(hQI i j).2.1, (hQI i j).1⟩) (fun i => (hdiag i).2.1),
    run_pivots hT hq hW crun c hc k childOf hchild F.piv hnd1,
    run_lowerSteps hT.H hq (c.sub W hW k) hc' F.E₁ F.E₁' hL1 h1
      (fun i j => ⟨(hQI i j).1, (hQI i j).2.1⟩) (fun i => (hdiag i).1),
    run_lowerSteps hT.D hq (c.sub W hW k) hcd' F.E₂' F.E₂ hL2' h2'
      (fun i j => ⟨(hQI i j).2.2.2, (hQI i j).2.2.1⟩) (fun i => (hdiag i).2.2.2)]
  refine (cpull5 _ _ _ _ _ _ (fun x hx => (mem_setCoords _ hc' _ _).2 hx)
    (fun x hx => (mem_setCoords _ hc' _ _).2 hx) (fun x hx => (mem_setCoords _ hc' _ _).2 hx)
    (fun x hx => (mem_setCoords _ hcd' _ _).2 hx) A).trans ?_
  apply cpull_congr
  intro x _
  simp only [Function.comp]
  conv_lhs => rw [← setHD_self hT x]
  simp only [setCoordsH_setHD hT, setCoordsD_setHD, coordsH_setHD hT, coordsD_setHD hT]
  rw [setCoordsH_eq_setHD hT, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h11', Matrix.one_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hAmod, Matrix.mulVec_mulVec,
    h2'2, Matrix.one_mulVec]

end InterchangeCorrect

end SubNLogN.Math.Networks
