/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.RoundsProg
import SubNLogN.Machine.Calculus.Adapters

/-!
# K4 rounds driver, step lemmas (`Machine/FFT/RoundsRuns.lean`)

**Scope (honest summary).** Exact `Runs` facts for the steps of the rounds driver
(`Machine/FFT/RoundsProg.lean`), from the part contracts and the arithmetic kernels' specs taken as
hypotheses (no `sorry`): driver states `st`, the part calls `runs_prefixK`, `runs_chunkK`,
`runs_twK`, the kernel calls, the setup and the loop body.
-/

namespace SubNLogN.Machine.FFT.RoundsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
  SubNLogN.Machine.FFTKit SubNLogN.Math.Walsh SubNLogN.Math.Common WP.W9comp

/-! ## Part specifications (the bodies of the part contracts) -/

/-- The body of `PrefixRoundStmt` for a program `Pr` with constants `J`, `C`. -/
def PrefixSpec {E R : Type} [Fintype E] [DecidableEq E] (J C : ℕ)
    (Pr : Prog (KLoc (Fin 4) E) (fun _ => Sym) R) : Prop :=
  ∀ (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
    (rest hrest crest : List Sym) (S : KLoc (Fin 4) E → List Sym),
    KClean S → MidShapeOK q ℓ K w a → v < ℓ → ¬ IsChunkRound ℓ K v → ArrOnDiskGrid q z →
    BlkTerm rest → TermOK crest →
    S (.inl 0) = carrSyms w (encCube q z) ++ rest →
    S (.inl 1) = midHdr q ℓ K w a ++ hrest →
    S (.inl 3) = natSyms v ++ crest →
    Runs Pr S
      (Function.update S (.inl 0)
        (carrSyms w (encCube q (truncArr q (hT (roundSet ℓ K a v) z))) ++ rest))
      (fun _ => True)
      (C * ((D + 1) * cvolCube (addrBits a) (2 ^ ℓ) (w + D) +
        2 ^ addrBits a * (w + addrBits a + 1) ^ J + (midHdr q ℓ K w a).length))

/-- The body of `ChunkRoundStmt Band lam'`. -/
def ChunkSpec {E R : Type} [Fintype E] [DecidableEq E] (Band : LayerRT → Prop) (lam' : ℝ)
    (J C : ℕ) (Pr : Prog (KLoc (Fin 4) E) (fun _ => Sym) R) : Prop :=
  ∀ (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
    (rest hrest crest : List Sym) (S : KLoc (Fin 4) E → List Sym),
    KClean S → MidShapeOK q ℓ K w a → IsChunkRound ℓ K v →
    roundJ0 ℓ K a v + D * K ≤ addrBits a →
    Band (layerRT q (D + 1) (2 ^ ℓ) w K (roundJ0 ℓ K a v) D
      (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)) →
    ArrOnDiskGrid q z → BlkTerm rest → TermOK crest →
    S (.inl 0) = carrSyms w (encCube q z) ++ rest →
    S (.inl 1) = midHdr q ℓ K w a ++ hrest →
    S (.inl 3) = natSyms v ++ crest →
    Runs Pr S
      (Function.update S (.inl 0)
        (carrSyms w (encCube q (truncArr q (hT (slicePos (addrBits a) K (roundJ0 ℓ K a v) D
          (roundRho ℓ K v)) z))) ++ rest))
      (fun _ => True)
      (C * (layerCost lam' (layerRT q (D + 1) (2 ^ ℓ) w K (roundJ0 ℓ K a v) D
          (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)) +
        (w + addrBits a + 1) ^ J + (midHdr q ℓ K w a).length))

/-- The body of `TwiddlePassStmt`. -/
def TwSpec {E R : Type} [Fintype E] [DecidableEq E] (J C : ℕ)
    (Pr : Prog (KLoc (Fin 4) E) (fun _ => Sym) R) : Prop :=
  ∀ (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
    (rest hrest trest crest : List Sym) (S : KLoc (Fin 4) E → List Sym),
    KClean S → MidShapeOK q ℓ K w a → v < ℓ → TabOK q ℓ θt → ArrOnDiskGrid q z →
    BlkTerm rest → TermOK crest →
    S (.inl 0) = carrSyms w (encCube q z) ++ rest →
    S (.inl 1) = midHdr q ℓ K w a ++ hrest →
    S (.inl 2) = tabSyms w q ℓ θt ++ trest →
    S (.inl 3) = natSyms v ++ crest →
    Runs Pr S
      (Function.update S (.inl 0)
        (carrSyms w (encCube q (truncArr q (diagArr (fun x => θt (2 * twJ ℓ K a v x)) z))) ++
          rest))
      (fun _ => True)
      (C * (2 ^ addrBits a * 2 ^ ℓ * mulW (2 * w + 1) + cvolCube (addrBits a) (2 ^ ℓ) w +
        2 ^ addrBits a * (w + addrBits a + 1) ^ J + (midHdr q ℓ K w a).length))

/-! ## Driver states -/

section Own

variable {EP EC ET : Type}

@[simp] theorem own_inj {i j : Fin 10} : (own i : RK EP EC ET) = own j ↔ i = j := by
  simp [own]

@[simp] theorem own_ne_inl (i : Fin 10) (n : Fin 3) : (own i : RK EP EC ET) ≠ .inl n := by
  simp [own]

@[simp] theorem inl_ne_own (i : Fin 10) (n : Fin 3) : (.inl n : RK EP EC ET) ≠ own i := by
  simp [own]

@[simp] theorem own_ne_inr_inr (i : Fin 10) (x : EP ⊕ (EC ⊕ ET)) :
    (own i : RK EP EC ET) ≠ .inr (.inr x) := by simp [own]

@[simp] theorem inr_inr_ne_own (i : Fin 10) (x : EP ⊕ (EC ⊕ ET)) :
    (.inr (.inr x) : RK EP EC ET) ≠ own i := by simp [own]

theorem fCp_injective : Function.Injective (fCp : Fin 2 → RK EP EC ET) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fCp]
theorem fDec_injective : Function.Injective (fDec : Fin 1 → RK EP EC ET) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fDec]
theorem fCmp_injective : Function.Injective (fCmp : Fin 2 → RK EP EC ET) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fCmp]
theorem fDm_injective : Function.Injective (fDm : Fin 4 → RK EP EC ET) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fDm]

theorem fCp_ne (i : Fin 2) (j : Fin 6) : (fCp i : RK EP EC ET) ≠ own ⟨4 + j, by omega⟩ := by
  fin_cases i <;> simp [fCp, Fin.ext_iff] <;> omega
theorem fDec_ne (i : Fin 1) (j : Fin 6) : (fDec i : RK EP EC ET) ≠ own ⟨4 + j, by omega⟩ := by
  fin_cases i <;> simp [fDec, Fin.ext_iff] <;> omega
theorem fCmp_ne (i : Fin 2) (j : Fin 6) : (fCmp i : RK EP EC ET) ≠ own ⟨4 + j, by omega⟩ := by
  fin_cases i <;> simp [fCmp, Fin.ext_iff] <;> omega
theorem fDm_ne (i : Fin 4) (j : Fin 6) : (fDm i : RK EP EC ET) ≠ own ⟨4 + j, by omega⟩ := by
  fin_cases i <;> simp [fDm, Fin.ext_iff] <;> omega

end Own

section States

variable {EP EC ET : Type} [DecidableEq EP] [DecidableEq EC] [DecidableEq ET]

instance decEqPCT : DecidableEq (EP ⊕ (EC ⊕ ET)) := instDecidableEqSum
instance decEqRE : DecidableEq (RE EP EC ET) := instDecidableEqSum
instance decEqRK : DecidableEq (RK EP EC ET) := instDecidableEqSum

/-- A general driver state: the initial stacks `S₀` with the array and the own stacks `0..3`
replaced. -/
def sx (S₀ : RK EP EC ET → List Sym) (A v0 v1 v2 v3 : List Sym) : RK EP EC ET → List Sym :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update S₀ (.inl 0) A) (own 0) v0) (own 1) v1) (own 2) v2) (own 3) v3

/-- A loop state: array `A`, round index stack `vv`, `b₀` stack `bb`, temporaries empty. -/
def st (S₀ : RK EP EC ET → List Sym) (A vv bb : List Sym) : RK EP EC ET → List Sym :=
  sx S₀ A vv bb [] []

section SxLemmas

variable (S₀ : RK EP EC ET → List Sym) (A v0 v1 v2 v3 : List Sym)

@[simp] theorem sx_arr : sx S₀ A v0 v1 v2 v3 (.inl 0) = A := by simp [sx]
@[simp] theorem sx_own0 : sx S₀ A v0 v1 v2 v3 (own 0) = v0 := by simp [sx]
@[simp] theorem sx_own1 : sx S₀ A v0 v1 v2 v3 (own 1) = v1 := by simp [sx]
@[simp] theorem sx_own2 : sx S₀ A v0 v1 v2 v3 (own 2) = v2 := by simp [sx]
@[simp] theorem sx_own3 : sx S₀ A v0 v1 v2 v3 (own 3) = v3 := by simp [sx]
@[simp] theorem sx_inl1 : sx S₀ A v0 v1 v2 v3 (.inl 1) = S₀ (.inl 1) := by simp [sx]
@[simp] theorem sx_inl2 : sx S₀ A v0 v1 v2 v3 (.inl 2) = S₀ (.inl 2) := by simp [sx]
@[simp] theorem sx_inr_inr (x : EP ⊕ (EC ⊕ ET)) :
    sx S₀ A v0 v1 v2 v3 (.inr (.inr x)) = S₀ (.inr (.inr x)) := by simp [sx]

theorem sx_upd_arr (A' : List Sym) :
    Function.update (sx S₀ A v0 v1 v2 v3) (.inl 0) A' = sx S₀ A' v0 v1 v2 v3 := by
  funext k; simp only [sx, Function.update_apply]; split_ifs <;> simp_all
theorem sx_upd0 (w0 : List Sym) :
    Function.update (sx S₀ A v0 v1 v2 v3) (own 0) w0 = sx S₀ A w0 v1 v2 v3 := by
  funext k; simp only [sx, Function.update_apply]; split_ifs <;> simp_all
theorem sx_upd1 (w1 : List Sym) :
    Function.update (sx S₀ A v0 v1 v2 v3) (own 1) w1 = sx S₀ A v0 w1 v2 v3 := by
  funext k; simp only [sx, Function.update_apply]; split_ifs <;> simp_all
theorem sx_upd2 (w2 : List Sym) :
    Function.update (sx S₀ A v0 v1 v2 v3) (own 2) w2 = sx S₀ A v0 v1 w2 v3 := by
  funext k; simp only [sx, Function.update_apply]; split_ifs <;> simp_all
theorem sx_upd3 (w3 : List Sym) :
    Function.update (sx S₀ A v0 v1 v2 v3) (own 3) w3 = sx S₀ A v0 v1 v2 w3 := by
  funext k; simp only [sx, Function.update_apply]; split_ifs <;> simp_all

end SxLemmas

theorem sx_self {S₀ : RK EP EC ET → List Sym} (hcl : KClean S₀) :
    sx S₀ (S₀ (.inl 0)) [] [] [] [] = S₀ := by
  funext k
  simp only [sx, Function.update_apply]
  split_ifs with h3 h2 h1 h0 ha <;> subst_vars <;> first | rfl | exact (hcl _).symm

/-- The final state: every own stack empty again. -/
theorem sx_final {S₀ : RK EP EC ET → List Sym} (hcl : KClean S₀) (A : List Sym) :
    sx S₀ A [] [] [] [] = Function.update S₀ (.inl 0) A := by
  rw [← sx_upd_arr S₀ (S₀ (.inl 0)) [] [] [] [] A, sx_self hcl]

variable (S₀ : RK EP EC ET → List Sym) (A vv bb : List Sym)

@[simp] theorem st_arr : st S₀ A vv bb (.inl 0) = A := by simp [st]
@[simp] theorem st_own0 : st S₀ A vv bb (own 0) = vv := by simp [st]
@[simp] theorem st_own1 : st S₀ A vv bb (own 1) = bb := by simp [st]
@[simp] theorem st_inl1 : st S₀ A vv bb (.inl 1) = S₀ (.inl 1) := by simp [st]
@[simp] theorem st_inl2 : st S₀ A vv bb (.inl 2) = S₀ (.inl 2) := by simp [st]
@[simp] theorem st_inr_inr (x : EP ⊕ (EC ⊕ ET)) :
    st S₀ A vv bb (.inr (.inr x)) = S₀ (.inr (.inr x)) := by simp [st]

theorem update_st_arr (A' : List Sym) :
    Function.update (st S₀ A vv bb) (.inl 0) A' = st S₀ A' vv bb := sx_upd_arr _ _ _ _ _ _ _

theorem update_st_own0 (vv' : List Sym) :
    Function.update (st S₀ A vv bb) (own 0) vv' = st S₀ A vv' bb := sx_upd0 _ _ _ _ _ _ _

theorem update_st_own1 (bb' : List Sym) :
    Function.update (st S₀ A vv bb) (own 1) bb' = st S₀ A vv bb' := sx_upd1 _ _ _ _ _ _ _

end States

/-! ## Calls of the parts -/

section Calls

variable {EP EC ET Rcp Rdec Rcmp Rdm RP RC RT : Type} [Fintype EP] [DecidableEq EP]
  [Fintype EC] [DecidableEq EC] [Fintype ET] [DecidableEq ET]

omit [Fintype EP] [Fintype EC] [Fintype ET] in
theorem kclean_part {Ei : Type} (j : Ei → EP ⊕ (EC ⊕ ET)) {S₀ : RK EP EC ET → List Sym}
    (hcl : KClean S₀) (A vv bb : List Sym) : KClean (st S₀ A vv bb ∘ partEmb j) := by
  intro e
  simp only [Function.comp, partEmb_inr, st_inr_inr]
  exact hcl _

theorem runs_prefixK {JP CP : ℕ} {PP : Prog (KLoc (Fin 4) EP) (fun _ => Sym) RP}
    (hsP : PrefixSpec JP CP PP) {S₀ : RK EP EC ET → List Sym} (hcl : KClean S₀)
    {q ℓ K w D v : ℕ} {a : Fin D → ℕ} {y : RArr (Cube (addrBits a)) (2 ^ ℓ)}
    {rest hrest : List Sym} (bb : List Sym) (hshape : MidShapeOK q ℓ K w a) (hv : v < ℓ)
    (hnc : ¬ IsChunkRound ℓ K v) (hy : ArrOnDiskGrid q y) (hrestT : BlkTerm rest)
    (h1 : S₀ (.inl 1) = midHdr q ℓ K w a ++ hrest) :
    Runs (prefixK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RC := RC) (RT := RT)
        (EC := EC) (ET := ET) PP)
      (st S₀ (carrSyms w (encCube q y) ++ rest) (natSyms v) bb)
      (st S₀ (carrSyms w (encCube q (truncArr q (hT (roundSet ℓ K a v) y))) ++ rest)
        (natSyms v) bb)
      (fun _ => True)
      (CP * ((D + 1) * cvolCube (addrBits a) (2 ^ ℓ) (w + D) +
        2 ^ addrBits a * (w + addrBits a + 1) ^ JP + (midHdr q ℓ K w a).length)) := by
  have h := hsP q ℓ K w D v a y rest hrest []
    (st S₀ (carrSyms w (encCube q y) ++ rest) (natSyms v) bb ∘ partEmb injP)
    (kclean_part injP hcl _ _ _) hshape hv hnc hy hrestT TermOK.nil
    (by simp) (by simp [h1]) (by simp)
  have h2 := runs_callInj_update (partEmb_injective injP_injective)
    (lP (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RC := RC) (RT := RT)) h
  rw [partEmb_arr, update_st_arr] at h2
  exact h2

theorem runs_chunkK {Band : LayerRT → Prop} {lam' : ℝ} {JC CC : ℕ}
    {PC : Prog (KLoc (Fin 4) EC) (fun _ => Sym) RC}
    (hsC : ChunkSpec Band lam' JC CC PC) {S₀ : RK EP EC ET → List Sym} (hcl : KClean S₀)
    {q ℓ K w D v : ℕ} {a : Fin D → ℕ} {y : RArr (Cube (addrBits a)) (2 ^ ℓ)}
    {rest hrest : List Sym} (bb : List Sym) (hshape : MidShapeOK q ℓ K w a)
    (hband : ChunkCallsBand Band q ℓ K w a) (hch : IsChunkRound ℓ K v)
    (hy : ArrOnDiskGrid q y) (hrestT : BlkTerm rest)
    (h1 : S₀ (.inl 1) = midHdr q ℓ K w a ++ hrest) :
    Runs (chunkK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RT := RT)
        (EP := EP) (ET := ET) PC)
      (st S₀ (carrSyms w (encCube q y) ++ rest) (natSyms v) bb)
      (st S₀ (carrSyms w (encCube q (truncArr q (hT (roundSet ℓ K a v) y))) ++ rest)
        (natSyms v) bb)
      (fun _ => True)
      (CC * (layerCost lam' (layerRT q (D + 1) (2 ^ ℓ) w K (roundJ0 ℓ K a v) D
          (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)) +
        (w + addrBits a + 1) ^ JC + (midHdr q ℓ K w a).length)) := by
  obtain ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hw⟩ := hshape
  obtain ⟨hfit, hset⟩ := roundSet_chunk hℓ2 hK1 hKℓ ha hch
  have hb := hband (roundJ0 ℓ K a v) (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)
    (by omega) (Nat.mod_lt _ (by omega))
  have h := hsC q ℓ K w D v a y rest hrest []
    (st S₀ (carrSyms w (encCube q y) ++ rest) (natSyms v) bb ∘ partEmb injC)
    (kclean_part injC hcl _ _ _) ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hw⟩ hch hfit hb hy hrestT
    TermOK.nil (by simp) (by simp [h1]) (by simp)
  have h2 := runs_callInj_update (partEmb_injective injC_injective)
    (lC (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RT := RT)) h
  rw [partEmb_arr, update_st_arr, ← hset] at h2
  exact h2

theorem runs_twK {JT CT : ℕ} {PT : Prog (KLoc (Fin 4) ET) (fun _ => Sym) RT}
    (hsT : TwSpec JT CT PT) {S₀ : RK EP EC ET → List Sym} (hcl : KClean S₀)
    {q ℓ K w D v : ℕ} {a : Fin D → ℕ} {θt : ℕ → ℂ} {y : RArr (Cube (addrBits a)) (2 ^ ℓ)}
    {rest hrest trest : List Sym} (bb : List Sym) (hshape : MidShapeOK q ℓ K w a) (hv : v < ℓ)
    (htab : TabOK q ℓ θt) (hy : ArrOnDiskGrid q y) (hrestT : BlkTerm rest)
    (h1 : S₀ (.inl 1) = midHdr q ℓ K w a ++ hrest) (h2 : S₀ (.inl 2) = tabSyms w q ℓ θt ++ trest) :
    Runs (twK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC)
        (EP := EP) (EC := EC) PT)
      (st S₀ (carrSyms w (encCube q y) ++ rest) (natSyms v) bb)
      (st S₀ (carrSyms w (encCube q (truncArr q (diagArr (twPhase ℓ K a θt v) y))) ++ rest)
        (natSyms v) bb)
      (fun _ => True)
      (CT * (2 ^ addrBits a * 2 ^ ℓ * mulW (2 * w + 1) + cvolCube (addrBits a) (2 ^ ℓ) w +
        2 ^ addrBits a * (w + addrBits a + 1) ^ JT + (midHdr q ℓ K w a).length)) := by
  have h := hsT q ℓ K w D v a θt y rest hrest trest []
    (st S₀ (carrSyms w (encCube q y) ++ rest) (natSyms v) bb ∘ partEmb injT)
    (kclean_part injT hcl _ _ _) hshape hv htab hy hrestT TermOK.nil
    (by simp) (by simp [h1]) (by simp [h2]) (by simp)
  have h3 := runs_callInj_update (partEmb_injective injT_injective)
    (lT (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC)) h
  rw [partEmb_arr, update_st_arr] at h3
  exact h3

end Calls

/-! ## Calls of the arithmetic kernels and the header programs -/

section Kernels

variable {EP EC ET Rcp Rdec Rcmp Rdm RP RC RT : Type} [DecidableEq EP] [DecidableEq EC]
  [DecidableEq ET]

theorem runs_hdrK {P : SProg (RK EP EC ET)} {B B' : RK EP EC ET → List Sym} {T : ℕ}
    (h : Runs P B B' (fun _ => True) T) :
    Runs (hdrK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC)
      (RT := RT) P) B B' (fun _ => True) T :=
  runs_callInj (ι := id) Function.injective_id lO h (fun k hk => absurd rfl (hk k))

theorem runs_drainK (i : Fin 10) (B : RK EP EC ET → List Sym) :
    Runs (drainK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC)
      (RT := RT) i) B (Function.update B (own i) []) (fun _ => True)
      (2 * (B (own i)).length + 3) :=
  runs_callInj (ι := id) Function.injective_id lB (runs_drainProg (own i) B)
    (fun k hk => absurd rfl (hk k))

theorem runs_peekV (B : RK EP EC ET → List Sym) :
    Runs (peekV (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC)
      (RT := RT)) B B (fun s => lO.get s = (B (own 0)).head?) 1 := by
  rintro ⟨v, stk⟩ hs
  change stk = B at hs
  subst hs
  exact ⟨_, 1, Eval.peek [] (own 0) _ v stk, ⟨rfl, lO.get_set _ _⟩, le_rfl⟩

theorem runs_cpK {mcp Ccp : ℕ} (hmcp : mcp ≤ 6) {Pcp : Prog (Loc 2 mcp) (fun _ => Sym) Rcp}
    (hsp : ∀ (a : ℕ) (rx : List Sym) (S : Loc 2 mcp → List Sym), TermOK rx →
      S (.inl 0) = natSyms a ++ rx →
      Runs Pcp S (Function.update S (.inl 1) (natSyms a ++ S (.inl 1))) (fun _ => True)
        (Ccp * (bitLen a + 1)))
    (B : RK EP EC ET → List Sym) (a : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hB : B (own 2) = natSyms a ++ rx) :
    Runs (callInj (kEmb hmcp fCp)
        (lcp (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC) (RT := RT)) Pcp)
      B (Function.update B (own 0) (natSyms a ++ B (own 0))) (fun _ => True)
      (Ccp * (bitLen a + 1)) := by
  have h := hsp a rx (B ∘ kEmb hmcp fCp) hrx (by simpa [kEmb, fCp] using hB)
  have h2 := runs_callInj_update (kEmb_injective hmcp fCp_injective fCp_ne)
    (lcp (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC) (RT := RT)) h
  simpa [kEmb, fCp] using h2

theorem runs_decK {mdec Cdec : ℕ} (hmdec : mdec ≤ 6) {Pdec : Prog (Loc 1 mdec) (fun _ => Sym) Rdec}
    (hsp : ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 mdec → List Sym), TermOK rx →
      S (.inl 0) = natSyms (a + 1) ++ rx →
      Runs Pdec S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
        (Cdec * (TMFw.zerosLead (Computability.encodeNat (a + 1)) + 1)))
    (B : RK EP EC ET → List Sym) (a : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hB : B (own 0) = natSyms (a + 1) ++ rx) :
    Runs (decK (Rcp := Rcp) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC) (RT := RT) hmdec Pdec)
      B (Function.update B (own 0) (natSyms a ++ rx)) (fun _ => True)
      (Cdec * (TMFw.zerosLead (Computability.encodeNat (a + 1)) + 1)) := by
  have h := hsp a rx (B ∘ kEmb hmdec fDec) hrx (by simpa [kEmb, fDec] using hB)
  have h2 := runs_callInj_update (kEmb_injective hmdec fDec_injective fDec_ne)
    (ldec (Rcp := Rcp) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC) (RT := RT)) h
  exact h2

theorem runs_cmpK {mcmp Ccmp : ℕ} (hmcmp : mcmp ≤ 6) {Pcmp : Prog (Loc 2 mcmp) (fun _ => Sym) Rcmp}
    {obs : Rcmp → Ordering} (hcl : Pcmp.Closed)
    (hsp : ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 2 mcmp → List Sym), TermOK rx → TermOK ry →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
      Runs Pcmp S S (fun r => obs r = Lib.ordOf a b) (Ccmp * (bitLen a + bitLen b + 1)))
    (B : RK EP EC ET → List Sym) (a b : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hBa : B (own 0) = natSyms a ++ rx) (hBb : B (own 1) = natSyms b ++ ry) :
    Runs (cmpK (Rcp := Rcp) (Rdec := Rdec) (Rdm := Rdm) (RP := RP) (RC := RC) (RT := RT) hmcmp Pcmp)
      B B (fun s => obs (lcmp.get s) = Lib.ordOf a b) (Ccmp * (bitLen a + bitLen b + 1)) := by
  have h := hsp a b rx ry (B ∘ kEmb hmcmp fCmp) hrx hry (by simpa [kEmb, fCmp] using hBa)
    (by simpa [kEmb, fCmp] using hBb)
  exact RunsIn.iff_runs.mp (RunsIn.of_callInj_reg (kEmb_injective hmcmp fCmp_injective fCmp_ne)
    (lcmp (Rcp := Rcp) (Rdec := Rdec) (Rdm := Rdm) (RP := RP) (RC := RC) (RT := RT)) hcl h
    (fun _ _ => rfl) [])

theorem runs_dmK {mdm Cdm : ℕ} (hmdm : mdm ≤ 6) {Pdm : Prog (Loc 4 mdm) (fun _ => Sym) Rdm}
    (hcl : Pdm.Closed)
    (hsp : ∀ (a b : ℕ) (ra rb : List Sym) (S : Loc 4 mdm → List Sym), 0 < b → TermOK ra →
      TermOK rb → S (.inl 0) = natSyms a ++ ra → S (.inl 1) = natSyms b ++ rb →
      Runs Pdm S (Function.update (Function.update S (.inl 2) (natSyms (a / b) ++ S (.inl 2)))
          (.inl 3) (natSyms (a % b) ++ S (.inl 3))) (fun _ => True)
        (Cdm * (bitLen a * bitLen b + bitLen a + bitLen b + 1)))
    (B : RK EP EC ET → List Sym) (a b : ℕ) (ra rb : List Sym) (hb : 0 < b) (hra : TermOK ra)
    (hrb : TermOK rb) (hBa : B (own 0) = natSyms a ++ ra) (hBb : B (own 2) = natSyms b ++ rb) :
    Runs (callInj (kEmb hmdm fDm)
        (ldm (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (RP := RP) (RC := RC) (RT := RT)) Pdm)
      B (Function.update (Function.update B (own 3) (natSyms (a / b) ++ B (own 3)))
          (own 1) (natSyms (a % b) ++ B (own 1))) (fun _ => True)
      (Cdm * (bitLen a * bitLen b + bitLen a + bitLen b + 1)) := by
  have h := hsp a b ra rb (B ∘ kEmb hmdm fDm) hb hra hrb (by simpa [kEmb, fDm] using hBa)
    (by simpa [kEmb, fDm] using hBb)
  have h2 := RunsIn.iff_runs.mp (RunsIn.callInj_upd2 (kEmb_injective hmdm fDm_injective fDm_ne)
    (ldm (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (RP := RP) (RC := RC) (RT := RT)) hcl B
    (.inl 2) (.inl 3) _ _ h [])
  simpa [kEmb, fDm] using h2

end Kernels

/-! ## The setup -/

theorem hdrSyms_cons' (f : ℕ) (fs : List ℕ) :
    hdrSyms (f :: fs) = natSyms f ++ Sym.mark :: hdrSyms fs := by
  simp [hdrSyms]

theorem hdrSyms_append' (fs gs : List ℕ) : hdrSyms (fs ++ gs) = hdrSyms fs ++ hdrSyms gs := by
  simp [hdrSyms]

theorem midHdr_split {D : ℕ} (q ℓ K w : ℕ) (a : Fin D → ℕ) :
    midHdr q ℓ K w a = hdrSyms [q, D, ℓ, K] ++ hdrSyms ([w] ++ List.ofFn a) := by
  rw [midHdr, ← hdrSyms_append']
  rfl

/-- Cost of the setup (copy four header fields, drop three, copy, decrement, divide, two drains). -/
def setupCost (Ccp Cdec Cdm q D ℓ K : ℕ) : ℕ :=
  (([q, D, ℓ, K].map fun f => 13 * bitLen f + 20).sum + 2) + ((2 * bitLen q + 5) +
    ((2 * bitLen D + 5) + (Ccp * (bitLen ℓ + 1) + ((2 * bitLen ℓ + 5) +
    (Cdec * (TMFw.zerosLead (Computability.encodeNat (ℓ - 1 + 1)) + 1) +
    (Cdm * (bitLen (ℓ - 1) * bitLen K + bitLen (ℓ - 1) + bitLen K + 1) +
    ((2 * (bitLen K + 1) + 3) + (2 * bitLen ((ℓ - 1) / K) + 3))))))))

section Setup

variable {EP EC ET Rcp Rdec Rcmp Rdm RP RC RT : Type} [DecidableEq EP] [DecidableEq EC]
  [DecidableEq ET]

theorem runs_setup {mcp mdec mdm Ccp Cdec Cdm : ℕ} (hmcp : mcp ≤ 6) (hmdec : mdec ≤ 6)
    (hmdm : mdm ≤ 6) {Pcp : Prog (Loc 2 mcp) (fun _ => Sym) Rcp}
    {Pdec : Prog (Loc 1 mdec) (fun _ => Sym) Rdec} {Pdm : Prog (Loc 4 mdm) (fun _ => Sym) Rdm}
    (hsCp : ∀ (a : ℕ) (rx : List Sym) (S : Loc 2 mcp → List Sym), TermOK rx →
      S (.inl 0) = natSyms a ++ rx →
      Runs Pcp S (Function.update S (.inl 1) (natSyms a ++ S (.inl 1))) (fun _ => True)
        (Ccp * (bitLen a + 1)))
    (hsDec : ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 mdec → List Sym), TermOK rx →
      S (.inl 0) = natSyms (a + 1) ++ rx →
      Runs Pdec S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
        (Cdec * (TMFw.zerosLead (Computability.encodeNat (a + 1)) + 1)))
    (hclDm : Pdm.Closed)
    (hsDm : ∀ (a b : ℕ) (ra rb : List Sym) (S : Loc 4 mdm → List Sym), 0 < b → TermOK ra →
      TermOK rb → S (.inl 0) = natSyms a ++ ra → S (.inl 1) = natSyms b ++ rb →
      Runs Pdm S (Function.update (Function.update S (.inl 2) (natSyms (a / b) ++ S (.inl 2)))
          (.inl 3) (natSyms (a % b) ++ S (.inl 3))) (fun _ => True)
        (Cdm * (bitLen a * bitLen b + bitLen a + bitLen b + 1)))
    {S₀ : RK EP EC ET → List Sym} (hcl : KClean S₀) {q ℓ K w D : ℕ} {a : Fin D → ℕ}
    {hrest : List Sym} (hshape : MidShapeOK q ℓ K w a)
    (h1 : S₀ (.inl 1) = midHdr q ℓ K w a ++ hrest) :
    Runs (setupProg (Rcmp := Rcmp) (RP := RP) (RC := RC) (RT := RT) hmcp hmdec hmdm Pcp Pdec Pdm)
      S₀ (st S₀ (S₀ (.inl 0)) (natSyms (ℓ - 1)) (natSyms ((ℓ - 1) % K))) (fun _ => True)
      (setupCost Ccp Cdec Cdm q D ℓ K) := by
  obtain ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hw⟩ := hshape
  have hH : S₀ (.inl 1) = hdrSyms [q, D, ℓ, K] ++ (hdrSyms ([w] ++ List.ofFn a) ++ hrest) := by
    rw [h1, midHdr_split, List.append_assoc]
  have hmark : TermOK (Sym.mark :: hdrSyms [K]) := TermOK.cons rfl _
  -- 1. copy `[q, D, ℓ, K]` to `own 2`
  have r1 := runs_copyHdr (K := RK EP EC ET) (src := .inl 1) (dst := own 2) (t := own 3)
    (by simp) (by simp) (by simp) [q, D, ℓ, K] _ (sx S₀ (S₀ (.inl 0)) [] [] [] [])
    (by rw [sx_inl1]; exact hH) (by rw [sx_own3]; exact TermOK.nil)
  rw [sx_own2, List.append_nil, sx_upd2, sx_self hcl] at r1
  -- 2-3. drop `q`, `D`
  have r2 := runs_dropField (own 2) q (hdrSyms [D, ℓ, K])
    (sx S₀ (S₀ (.inl 0)) [] [] (hdrSyms [q, D, ℓ, K]) []) (by rw [sx_own2, hdrSyms_cons'])
  rw [sx_upd2] at r2
  have r3 := runs_dropField (own 2) D (hdrSyms [ℓ, K])
    (sx S₀ (S₀ (.inl 0)) [] [] (hdrSyms [D, ℓ, K]) []) (by rw [sx_own2, hdrSyms_cons'])
  rw [sx_upd2] at r3
  -- 4. copy `ℓ` to `own 0`
  have r4 := runs_cpK (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC) (RT := RT)
    hmcp hsCp (sx S₀ (S₀ (.inl 0)) [] [] (hdrSyms [ℓ, K]) []) ℓ _ hmark
    (by rw [sx_own2, hdrSyms_cons'])
  rw [sx_own0, List.append_nil, sx_upd0] at r4
  -- 5. drop `ℓ`
  have r5 := runs_dropField (own 2) ℓ (hdrSyms [K])
    (sx S₀ (S₀ (.inl 0)) (natSyms ℓ) [] (hdrSyms [ℓ, K]) []) (by rw [sx_own2, hdrSyms_cons'])
  rw [sx_upd2] at r5
  -- 6. decrement: `ℓ - 1`
  have hℓ1 : ℓ = ℓ - 1 + 1 := by omega
  have r6 := runs_decK (Rcp := Rcp) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC) (RT := RT)
    hmdec hsDec (sx S₀ (S₀ (.inl 0)) (natSyms ℓ) [] (hdrSyms [K]) []) (ℓ - 1) [] TermOK.nil
    (by rw [sx_own0, List.append_nil, ← hℓ1])
  rw [List.append_nil, sx_upd0] at r6
  -- 7. divide by `K`
  have r7 := runs_dmK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (RP := RP) (RC := RC) (RT := RT)
    hmdm hclDm hsDm (sx S₀ (S₀ (.inl 0)) (natSyms (ℓ - 1)) [] (hdrSyms [K]) []) (ℓ - 1) K []
    [Sym.mark] (by omega) TermOK.nil (TermOK.cons rfl _) (by rw [sx_own0, List.append_nil])
    (by rw [sx_own2]; simp [hdrSyms])
  rw [sx_own3, sx_own1, List.append_nil, List.append_nil, sx_upd3, sx_upd1] at r7
  -- 8-9. drain the temporaries
  have r8 := runs_drainK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP)
    (RC := RC) (RT := RT) 2 (sx S₀ (S₀ (.inl 0)) (natSyms (ℓ - 1)) (natSyms ((ℓ - 1) % K))
      (hdrSyms [K]) (natSyms ((ℓ - 1) / K)))
  rw [sx_own2, sx_upd2] at r8
  have r9 := runs_drainK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP)
    (RC := RC) (RT := RT) 3 (sx S₀ (S₀ (.inl 0)) (natSyms (ℓ - 1)) (natSyms ((ℓ - 1) % K))
      [] (natSyms ((ℓ - 1) / K)))
  rw [sx_own3, sx_upd3] at r9
  have hK2 : (hdrSyms [K]).length = bitLen K + 1 := by simp [hdrSyms, length_natSyms]
  rw [hK2] at r8
  rw [length_natSyms] at r9
  exact runs_seq (runs_hdrK r1) (runs_seq (runs_hdrK r2) (runs_seq (runs_hdrK r3)
    (runs_seq r4 (runs_seq (runs_hdrK r5) (runs_seq r6 (runs_seq r7 (runs_seq r8 r9)))))))

end Setup

/-! ## The loop body -/

theorem natSyms_zero : natSyms 0 = [] := by
  first | rfl | decide | simp [natSyms, Computability.encodeNat, Computability.encodeNum]

theorem isSome_head?_natSyms (n : ℕ) : ((natSyms n).head?).isSome = decide (n ≠ 0) := by
  rcases n with _ | n
  · simp [natSyms_zero]
  · have h : 0 < (natSyms (n + 1)).length := by
      rw [length_natSyms, bitLen, IntMulTM.length_encodeNat]
      exact Nat.size_pos.2 (Nat.succ_pos n)
    cases hc : natSyms (n + 1) with
    | nil => rw [hc] at h; simp at h
    | cons x l => simp

/-- The layer cost of a chunk round is uniform in the round (the record count is `2^{m₀}`). -/
noncomputable def lcU (lam' : ℝ) (D ℓ w m : ℕ) : ℕ :=
  (2 * 2 ^ m * 2 ^ ℓ * w) * ⌈((D + 1 : ℕ) : ℝ) ^ lam'⌉₊ + 2 * 2 ^ m * 2 ^ ℓ * w + 1

theorem layerCost_layerRT {lam' : ℝ} {q D ℓ K w j₀ nS ρ m : ℕ} (hm : j₀ + D * K + nS = m) :
    layerCost lam' (layerRT q (D + 1) (2 ^ ℓ) w K j₀ D nS ρ) = lcU lam' D ℓ w m := by
  have hM : 2 ^ j₀ * 2 ^ nS * 2 ^ (K * D) = 2 ^ m := by
    rw [← pow_add, ← pow_add, ← hm]
    congr 1
    ring
  simp only [layerCost, LayerRT.vol, LayerRT.M, layerRT, lcU, hM]

theorem runs_seq_ite_t' {K σ : Type} [DecidableEq K] {P p q : Prog K (fun _ => Sym) σ}
    {c : σ → Bool} {S1 S2 S3 : K → List Sym} {Q : σ → Prop} {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q T1)
    (hc : ∀ v, Q v → c v = true) (h2 : Runs p S2 S3 (fun _ => True) T2) :
    Runs (.seq P (.ite c p q)) S1 S3 (fun _ => True) (T1 + (T2 + 1)) := by
  rintro ⟨v, stk⟩ hs
  obtain ⟨⟨v1, s1⟩, t1, e1, ⟨hs1, hq⟩, ht1⟩ := h1 ⟨v, stk⟩ hs
  obtain ⟨s', t2, e2, hq2, ht2⟩ := h2 ⟨v1, s1⟩ hs1
  exact ⟨s', t1 + (t2 + 1), Eval.seq e1 (Eval.ite_true (hc v1 hq) e2), hq2, by omega⟩

theorem runs_seq_ite_f' {K σ : Type} [DecidableEq K] {P p q : Prog K (fun _ => Sym) σ}
    {c : σ → Bool} {S1 S2 S3 : K → List Sym} {Q : σ → Prop} {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q T1)
    (hc : ∀ v, Q v → c v = false) (h2 : Runs q S2 S3 (fun _ => True) T2) :
    Runs (.seq P (.ite c p q)) S1 S3 (fun _ => True) (T1 + (T2 + 1)) := by
  rintro ⟨v, stk⟩ hs
  obtain ⟨⟨v1, s1⟩, t1, e1, ⟨hs1, hq⟩, ht1⟩ := h1 ⟨v, stk⟩ hs
  obtain ⟨s', t2, e2, hq2, ht2⟩ := h2 ⟨v1, s1⟩ hs1
  exact ⟨s', t1 + (t2 + 1), Eval.seq e1 (Eval.ite_false (hc v1 hq) e2), hq2, by omega⟩

end SubNLogN.Machine.FFT.RoundsAux
