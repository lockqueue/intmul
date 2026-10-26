import SubNLogN.Math.Networks.Proofs.InterchangeCorrectNode

/-!
# Proposition A.7 (`prop:transfer11`) correctness: `InterchangeProcCorrectStmt`

`interchangeProc q fac k h₀ d₀` run in class `c` is the block interchange `swapBlocks h₀ d₀ (m^k)`.
Induction on `k` (generalizing `h₀ d₀ c A`):
* `k = 0`: one digit-pair swap (`Elem.pair` with `finSwapPerm`, both ranges `q`);
* `k + 1` (`b = m^k`, coordinates in `ZMod (q^b)`): `subHSteps` (pull `D ← D + H`), the node
  (pull `H ← H − D`; `run_node`, whose child calls are the induction hypothesis on the role classes
  `c.sub W_b k'`), `hMinusDSteps` (pull `D ← H − D`); the composite pull is `(H, D) ↦ (D, H)`,
  which is `swapBlocks h₀ d₀ (m · b)` (`swapBlocks_chunk_runIn`).
The network facts enter only through `BitNetCert` (array corollary, in `run_node`); the Lemma A.6 (`lem:transfer-shear`) shear facts are
re-proved at the block level (`run_shearOps`), so `ShearFacts` is not used.

File layout (all under `Networks/Proofs/`): `InterchangeCorrectRadix` (mixed-radix blocks),
`InterchangeCorrectCoords` and `InterchangeCorrectSteps` (chunk coordinates, primitive steps),
`InterchangeCorrectShear` (Lemma A.6 (`lem:transfer-shear`) at block level), `Serial` (serialization of the framed network),
`InterchangeCorrectRoles`, `InterchangeCorrectTransport`, `InterchangeCorrectNode` (roles, transport, node), this file (induction).
-/

namespace SubNLogN.Math.Networks

open Model

namespace InterchangeCorrect

variable {L : Layout}

/-- Three class-restricted pulls compose (the later pulls preserve the class). -/
theorem cpull3 {β : Type} (P : L.Addr → Prop) [DecidablePred P] (p₁ p₂ p₃ : L.Addr → L.Addr)
    (h₂ : ∀ x, P x → P (p₂ x)) (h₃ : ∀ x, P x → P (p₃ x)) (A : L.Addr → β) :
    cpull P p₃ (cpull P p₂ (cpull P p₁ A)) = cpull P (p₁ ∘ p₂ ∘ p₃) A := by
  rw [cpull_cpull P p₁ p₂ h₂, cpull_cpull P (p₁ ∘ p₂) p₃ h₃]
  rfl

private theorem ic_place_single {t : ℕ} (ht : t < L.n) : L.place (t + 1) ⟨t, ht⟩ = 1 := by
  unfold Layout.place
  apply Finset.prod_eq_one
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exfalso
  have h1 : t < j.val := hj.1
  have h2 : j.val < t + 1 := hj.2
  omega

private theorem ic_blockVal_single {t : ℕ} (ht : t < L.n) (x : L.Addr) :
    L.blockVal t (t + 1) x = (x ⟨t, ht⟩).val := by
  unfold Layout.blockVal
  rw [Finset.sum_eq_single ⟨t, ht⟩]
  · rw [ic_place_single ht, mul_one]
  · intro j hj hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inBlock] at hj
    exact absurd (Fin.ext (show j.val = t by omega)) hne
  · intro h
    exfalso
    exact h (by simp [inBlock])

private theorem ic_blockSet_single_self {t : ℕ} (ht : t < L.n) (x : L.Addr) (v : ℕ) :
    (L.blockSet t (t + 1) x v ⟨t, ht⟩).val = v % L.r ⟨t, ht⟩ := by
  simp only [Layout.blockSet]
  rw [if_pos (show inBlock t (t + 1) (⟨t, ht⟩ : Fin L.n) from ⟨le_refl _, Nat.lt_succ_self _⟩)]
  simp only [ic_place_single ht, Nat.div_one]

/-- Row field of a role class (generic `W`: never unfold `Wb` in a defeq check). -/
theorem ic_sub_row (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W) :
    (c.sub W hW k).row = c.row := rfl

/-- Modulus of a role class (generic `W`). -/
theorem ic_sub_mu (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W) :
    (c.sub W hW k).μ = c.μ * W := rfl

/-- The hypotheses at depth `k + 1` give the node hypotheses with block width `b = m^k`. -/
theorem nodeHyp_of_hyps {q : ℕ} {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData} {k h₀ d₀ : ℕ}
    {c : RowClass L} (hyp : InterchangeHyps L q fac (k + 1) h₀ d₀ c) :
    NodeHyp L q h₀ d₀ (mH ^ k) c := by
  obtain ⟨_, _, _, _, hrad, hHD, hDn, hrow, hdiv⟩ := hyp
  have e : mH * mH ^ k = mH ^ (k + 1) := (pow_succ' mH k).symm
  have hb : 0 < mH ^ k := pow_pos (by norm_num) k
  refine ⟨⟨⟨hb, by omega, fun j h1 h2 => hrad j (Or.inl ⟨h1, by omega⟩)⟩,
    ⟨hb, by omega, fun j h1 h2 => hrad j (Or.inr ⟨h1, by omega⟩)⟩, by omega⟩, hrow, ?_⟩
  exact dvd_trans (Nat.mul_dvd_mul_left c.μ (dvd_pow_self Wb (by omega : k + 1 ≠ 0))) hdiv

/-- The hypotheses at depth `k + 1` give those of every child call (role class `c.sub W_b k'`). -/
theorem hyps_child {q : ℕ} {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData} {k h₀ d₀ : ℕ}
    {c : RowClass L} (hyp : InterchangeHyps L q fac (k + 1) h₀ d₀ c) (k' : Fin Wb) (i j : Fin mH) :
    InterchangeHyps L q fac k (h₀ + i.val * mH ^ k) (d₀ + j.val * mH ^ k) (c.sub Wb Wb_pos k') := by
  obtain ⟨hq, hq2, hfr, hfac, hrad, hHD, hDn, hrow, hdiv⟩ := hyp
  have e : mH * mH ^ k = mH ^ (k + 1) := (pow_succ' mH k).symm
  have hi : i.val * mH ^ k + mH ^ k ≤ mH * mH ^ k := by
    have := Nat.mul_le_mul_right (mH ^ k) (Nat.succ_le_of_lt i.isLt)
    rwa [Nat.succ_mul] at this
  have hj : j.val * mH ^ k + mH ^ k ≤ mH * mH ^ k := by
    have := Nat.mul_le_mul_right (mH ^ k) (Nat.succ_le_of_lt j.isLt)
    rwa [Nat.succ_mul] at this
  refine ⟨hq, hq2, hfr, hfac, ?_, by omega, by omega, ?_, ?_⟩
  · intro i' hi'
    apply hrad i'
    rcases hi' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · rw [ic_sub_row]
    omega
  · rw [ic_sub_mu, ic_sub_row, mul_assoc, ← pow_succ']
    exact hdiv

/-- Depth `0`: one digit interchange. -/
theorem run_depth0 {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {q : ℕ}
    {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData} {h₀ d₀ : ℕ} {c : RowClass L}
    (hyp : InterchangeHyps L q fac 0 h₀ d₀ c) (A : L.Addr → β) :
    ProcK.run 0 (interchangeProc (L := L) (β := β) q fac 0 h₀ d₀) c A =
      (Step.swapBlocks h₀ d₀ (mH ^ 0) : Step L β).runIn c A := by
  obtain ⟨_, _, _, _, hrad, hHD, hDn, _, _⟩ := hyp
  simp only [pow_zero] at hrad hHD hDn ⊢
  have hh : h₀ < L.n := by omega
  have hd : d₀ < L.n := by omega
  have hrh : L.r ⟨h₀, hh⟩ = q := hrad ⟨h₀, hh⟩ (Or.inl ⟨le_refl _, by simp⟩)
  have hrd : L.r ⟨d₀, hd⟩ = q := hrad ⟨d₀, hd⟩ (Or.inr ⟨le_refl _, by simp⟩)
  have hab : L.r ⟨h₀, hh⟩ = L.r ⟨d₀, hd⟩ := hrh.trans hrd.symm
  have hproc : interchangeProc (L := L) (β := β) q fac 0 h₀ d₀ =
      [.elem (.pair ⟨h₀, hh⟩ ⟨d₀, hd⟩ (finSwapPerm _ _))] := by
    simp only [interchangeProc]
    exact dif_pos ⟨hh, hd⟩
  rw [hproc]
  show Step.runIn c (.elem (.pair ⟨h₀, hh⟩ ⟨d₀, hd⟩ (finSwapPerm _ _))) A = _
  funext x
  simp only [Step.runIn]
  split_ifs with hx
  · simp only [Step.run, Function.comp]
    congr 1
    funext j
    apply Fin.ext
    simp only [Elem.pull, finSwapPerm, dif_pos hab, Equiv.coe_fn_symm_mk]
    by_cases h1 : j = ⟨d₀, hd⟩
    · subst h1
      rw [Function.update_self, Fin.val_cast, ic_blockSet_single_self hd, ic_blockVal_single hh,
        hrd]
      rw [Nat.mod_eq_of_lt (by rw [← hrh]; exact (x ⟨h₀, hh⟩).isLt)]
    · by_cases h2 : j = ⟨h₀, hh⟩
      · subst h2
        rw [Function.update_of_ne h1, Function.update_self, Fin.val_cast,
          blockSet_apply_of_not _ _ _ (by simp only; omega), ic_blockSet_single_self hh,
          ic_blockVal_single hd, hrh]
        rw [Nat.mod_eq_of_lt (by rw [← hrd]; exact (x ⟨d₀, hd⟩).isLt)]
      · have h1' : j.val ≠ d₀ := fun h => h1 (Fin.ext h)
        have h2' : j.val ≠ h₀ := fun h => h2 (Fin.ext h)
        rw [Function.update_of_ne h1, Function.update_of_ne h2,
          blockSet_apply_of_not _ _ _ (by omega), blockSet_apply_of_not _ _ _ (by omega)]
  · rfl

/-- Depth `k + 1`, given that the child calls are block interchanges. -/
theorem run_succ (hcert : BitNetCert) {β : Type} [AddCommGroup β] [Module (ZMod 2) β] {q : ℕ}
    {fac : Matrix (Fin mH) (Fin mH) ℚ → FacData} {k h₀ d₀ : ℕ} {c : RowClass L}
    (hyp : InterchangeHyps L q fac (k + 1) h₀ d₀ c)
    (hchild : ∀ (k' : Fin Wb) (i j : Fin mH) (A : L.Addr → β),
      ProcK.run k (interchangeProc (L := L) (β := β) q fac k (h₀ + i.val * mH ^ k)
          (d₀ + j.val * mH ^ k)) (c.sub Wb Wb_pos k') A =
        (Step.swapBlocks (h₀ + i.val * mH ^ k) (d₀ + j.val * mH ^ k) (mH ^ k) : Step L β).runIn
          (c.sub Wb Wb_pos k') A)
    (A : L.Addr → β) :
    ProcK.run (k + 1) (interchangeProc (L := L) (β := β) q fac (k + 1) h₀ d₀) c A =
      (Step.swapBlocks h₀ d₀ (mH ^ (k + 1)) : Step L β).runIn c A := by
  have hN := nodeHyp_of_hyps hyp
  obtain ⟨hq, -, hfr, hfac, -, -, -, hrow, -⟩ := hyp
  have hT := hN.two
  have hrowd : c.row.val < d₀ := lt_of_lt_of_le hrow (le_trans (Nat.le_add_right _ _) hT.HD)
  have e : mH ^ (k + 1) = mH * mH ^ k := pow_succ' mH k
  have hproc : ProcK.run (k + 1) (interchangeProc (L := L) (β := β) q fac (k + 1) h₀ d₀) c A =
      (hMinusDSteps (L := L) (β := β) (q ^ mH ^ k) h₀ d₀ (mH ^ k)).foldl (fun A s => s.runIn c A)
        ((bitNodeOps (L := L) (β := β) (q ^ mH ^ k) h₀ d₀ (mH ^ k) fac
            (fun i j => interchangeProc (L := L) (β := β) q fac k (h₀ + i.val * mH ^ k)
              (d₀ + j.val * mH ^ k))).foldl
          (fun A o => o.run (ProcK.run k) c Wb_pos A)
          ((subHSteps (L := L) (β := β) (q ^ mH ^ k) h₀ d₀ (mH ^ k)).foldl
            (fun A s => s.runIn c A) A)) := by
    show List.foldl (fun A o => Model.Op.run (ProcK.run k) c o A) A
        ((subHSteps (L := L) (β := β) (q ^ mH ^ k) h₀ d₀ (mH ^ k)).map Model.Op.prim ++
          [Model.Op.node Wb Wb_pos (bitNodeOps (L := L) (β := β) (q ^ mH ^ k) h₀ d₀ (mH ^ k) fac
            (fun i j => interchangeProc (L := L) (β := β) q fac k (h₀ + i.val * mH ^ k)
              (d₀ + j.val * mH ^ k)))] ++
          (hMinusDSteps (L := L) (β := β) (q ^ mH ^ k) h₀ d₀ (mH ^ k)).map Model.Op.prim) = _
    rw [List.foldl_append, List.foldl_append, List.foldl_map, List.foldl_map, List.foldl_cons,
      List.foldl_nil]
    rfl
  rw [hproc, run_subHSteps hT c hrow, run_node hcert hN hq hfr fac hfac (ProcK.run k) _ hchild,
    run_hMinusDSteps hT c hrow, e, swapBlocks_chunk_runIn hT c]
  refine (cpull3 c.mem _ _ _ (fun x hx => (mem_setCoords c hrow _ _).2 hx)
    (fun x hx => (mem_setCoords c hrowd _ _).2 hx) A).trans ?_
  apply cpull_congr
  intro x _
  simp only [Function.comp]
  rw [coords_setCoords_D hT, coords_setCoords hT.D, sub_sub_cancel, coords_setCoords hT.H,
    coords_setCoords_H hT, coords_setCoords hT.D, sub_add_cancel, ← setCoords_comm hT,
    setCoords_setCoords]

end InterchangeCorrect

/-- **Proposition A.7 (`prop:transfer11`) correctness**: under `BitNetCert`,
`interchangeProc q fac k h₀ d₀` run in class `c` is `swapBlocks h₀ d₀ (m^k)` on `c`, for every
payload `β` (an `𝔽₂`-module) and arbitrary data, whenever `InterchangeHyps` holds. (`ShearFacts` is
not needed: the Lemma A.6 (`lem:transfer-shear`) shear facts are re-proved at the block level.) -/
theorem interchangeProcCorrect_holds : InterchangeProcCorrectStmt := by
  intro hcert _hshear L β _ _ q fac k
  induction k with
  | zero =>
    intro h₀ d₀ c hyp A
    exact InterchangeCorrect.run_depth0 hyp A
  | succ k ih =>
    intro h₀ d₀ c hyp A
    exact InterchangeCorrect.run_succ hcert hyp
      (fun k' i j A' => ih _ _ _ (InterchangeCorrect.hyps_child hyp k' i j) A') A

end SubNLogN.Math.Networks
