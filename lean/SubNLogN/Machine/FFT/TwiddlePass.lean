/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.TwiddleFacts
import SubNLogN.Machine.FFT.TwiddleHdr
import SubNLogN.Machine.FFT.TwiddleAddrDefs

/-!
# K4-TWIDDLE part (E2): the twiddle pass (`Machine/FFT/TwiddlePass.lean`)

**Scope (honest summary).** Proves `twiddlePass_holds : TwiddlePassStmt`
(`Machine/Contracts/FFT.lean`) from three named contracts taken as hypotheses:
`MulBigContract`, `CMulTruncBcastStmt` (the broadcast complex multiplication, AR4b) and
`TwiddleAddrStmt` (the per-record table index, `Machine/FFT/TwiddleAddrDefs.lean`). No `sorry`.

The kernel (`twProg`, `Par = Unit`, everything runtime-uniform):
1. `hdrPhase`: copy `q` and three copies of `w` out of the header (fields in front of `w` are
   parked and restored, cost `≤ 27·|midHdr|`);
2. `selPhase`: for every record `x` (index `n`): move it aside, compute `2·J(x)` **once** by the
   address routine (`TwiddleAddrStmt`), select the table entry `θ̃_{2J(x)}` by **one table scan**
   (`selEntry`), increment `n`; this builds the per-record phase array;
3. one call of `CMulTruncBcastStmt`: every coefficient of record `x` times `θ̃_{2J(x)}` (exact
   product, then `Q_q`), written back onto the array stack;
4. drop the parameter copies.
The value is `truncArr q (diagArr (fun x => θt (2·twJ ℓ K a v x)) z)` by `encCube_twiddle`
(`Machine/FFT/TwiddleMath.lean`); the cost bound uses `J := J_A + 1` and
`C := 100 + 6·C_C + C_A`.
-/

namespace SubNLogN.Machine.FFT

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine SubNLogN.Machine.FFT.DIF
  SubNLogN.Math.Walsh SubNLogN.Math.Common

namespace TwiddleAux

/-- Private stacks of the twiddle pass: 15 own stacks, then the private stacks of the address
routine and of the multiplier. -/
abbrev TwE (EA EC : Type) : Type := Fin 15 ⊕ (EA ⊕ EC)

/-- Own private stack `i` of the twiddle pass. -/
abbrev sc {EA EC : Type} (i : Fin 15) : KLoc (Fin 4) (TwE EA EC) := .inr (.inl i)

/-- Embedding of the address routine: header, round index, record counter `sc 1`, destination
`sc 5`, private stacks. -/
def ιA {EA EC : Type} : KLoc (Fin 4) EA → KLoc (Fin 4) (TwE EA EC) :=
  Sum.elim ![.inl 1, .inl 3, sc 1, sc 5] fun e => .inr (.inr (.inl e))

/-- Embedding of the multiplier: records `sc 8`, phases `sc 9`, output = the array stack, widths
`sc 12`, `sc 13`, `sc 14`, shift `sc 11`, private stacks. -/
def ιC {EA EC : Type} : KLoc (Fin 7) EC → KLoc (Fin 4) (TwE EA EC) :=
  Sum.elim ![sc 8, sc 9, .inl 0, sc 12, sc 13, sc 14, sc 11] fun e => .inr (.inr (.inr e))

theorem ιA_injective {EA EC : Type} :
    Function.Injective (ιA : KLoc (Fin 4) EA → KLoc (Fin 4) (TwE EA EC)) := by
  refine Function.Injective.sumElim ?_ (fun e e' h => by simpa using h) ?_
  · intro x y h
    fin_cases x <;> fin_cases y <;> simp_all
  · intro x e
    fin_cases x <;> simp

theorem ιC_injective {EA EC : Type} :
    Function.Injective (ιC : KLoc (Fin 7) EC → KLoc (Fin 4) (TwE EA EC)) := by
  refine Function.Injective.sumElim ?_ (fun e e' h => by simpa using h) ?_
  · intro x y h
    fin_cases x <;> fin_cases y <;> simp_all
  · intro x e
    fin_cases x <;> simp

/-- Register lens of the own routines. -/
abbrev lW (RA RC : Type) : Lens (Option Sym × (RA × RC)) (Option Sym) := Lens.fst _ _

/-- **The twiddle pass program** (see the module docstring). Stacks: `.inl 0` array, `.inl 1`
header, `.inl 2` table, `.inl 3` round index; `sc 0` moved records, `sc 1` record counter,
`sc 2` phases (reversed), `sc 3`/`sc 4` table side stacks, `sc 5`/`sc 6` table index and copy,
`sc 7` temporary, `sc 8` records, `sc 9` phases, `sc 10` parked header fields, `sc 11` `q`,
`sc 12`-`sc 14` `w`. -/
def twProg {EA EC RA RC : Type} (PA : Prog (KLoc (Fin 4) EA) (fun _ => Sym) RA)
    (PC : Prog (KLoc (Fin 7) EC) (fun _ => Sym) RC) :
    Prog (KLoc (Fin 4) (TwE EA EC)) (fun _ => Sym) (Option Sym × (RA × RC)) :=
  .seq (hdrPhase (lW RA RC) (.inl 1) (sc 10) (sc 7) (sc 11) (sc 12) (sc 13) (sc 14))
  (.seq (selPhase (lW RA RC) (callInj ιA (lsnd (Lens.fst RA RC)) PA) (.inl 0) (sc 0) (sc 1)
      (sc 2) (.inl 2) (sc 3) (sc 4) (sc 5) (sc 6) (sc 7) (sc 8) (sc 9))
  (.seq (callInj ιC (lsnd (Lens.snd RA RC)) PC)
  (.seq (drain (lW RA RC) (sc 12)) (.seq (drain (lW RA RC) (sc 13))
    (.seq (drain (lW RA RC) (sc 14)) (drain (lW RA RC) (sc 11)))))))

theorem closed_twProg {EA EC RA RC : Type} {PA : Prog (KLoc (Fin 4) EA) (fun _ => Sym) RA}
    {PC : Prog (KLoc (Fin 7) EC) (fun _ => Sym) RC} (hPA : PA.Closed) (hPC : PC.Closed) :
    (twProg PA PC).Closed :=
  ⟨closed_hdrPhase _ _ _ _ _ _ _ _,
    closed_selPhase _ (closed_callInj _ _ hPA) _ _ _ _ _ _ _ _ _ _ _ _,
    closed_callInj _ _ hPC, closed_drain _ _, closed_drain _ _, closed_drain _ _,
    closed_drain _ _⟩

theorem blkTerm_nil' : BlkTerm ([] : List Sym) := fun _ h => by cases h

end TwiddleAux

namespace TwiddleAux

/-- The final stacks of the twiddle pass. -/
theorem tw_final {EA EC : Type} [DecidableEq EA] [DecidableEq EC]
    (S : KLoc (Fin 4) (TwE EA EC) → List Sym) (hClean : KClean S) (q w : ℕ)
    (rest V0 vsA phsA : List Sym) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update S
            (sc 11) (natSyms q)) (sc 12) (natSyms w)) (sc 13) (natSyms w)) (sc 14) (natSyms w))
          (.inl 0) rest) (sc 8) vsA) (sc 9) phsA)
        (sc 8) []) (sc 9) []) (.inl 0) (V0 ++ rest))
      (sc 12) []) (sc 13) []) (sc 14) []) (sc 11) [] =
    Function.update S (.inl 0) (V0 ++ rest) := by
  have h' : ∀ i : Fin 15, S (sc i) = [] := fun i => hClean _
  funext x
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end TwiddleAux

open TwiddleAux in
/-- **K4-TWIDDLE: the twiddle pass contract.** `TwiddlePassStmt` holds, given the named
contracts `MulBigContract`, `CMulTruncBcastStmt` (AR4b) and `TwiddleAddrStmt` (the per-record
table index). Exponent `J := J_A + 1`, constant `C := 100 + 6·C_C + C_A`. -/
theorem twiddlePass_holds (hMul : MulBigContract) (hCM : CMulTruncBcastStmt)
    (hAddr : TwiddleAddrStmt) : TwiddlePassStmt := by
  obtain ⟨JA, CA, hA⟩ := hAddr
  obtain ⟨CC, hC⟩ := hCM hMul
  obtain ⟨EA, iFA, iDA, RA, PA, hRA, hRA', hPA, hspecA⟩ := hA ()
  obtain ⟨EC, iFC, iDC, RC, PC, hRC, hRC', hPC, hspecC⟩ := hC ()
  refine ⟨JA + 1, 100 + 6 * CC + CA, fun _ => ⟨TwE EA EC, inferInstance, inferInstance,
    Option Sym × (RA × RC), twProg PA PC, inferInstance, ⟨(none, hRA'.some, hRC'.some)⟩,
    closed_twProg hPA hPC, ?_⟩⟩
  intro q ℓ K w D v a θt z rest hrest trest crest S hClean hShape hv hTab hz hrestB hcrest
    hS0 hS1 hS2 hS3
  obtain ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hqw⟩ := id hShape
  have hK0 : 0 < K := by omega
  have hw1 : 1 ≤ w := by omega
  have hsc : ∀ i : Fin 15, S (sc i) = [] := fun i => hClean _
  -- data
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = twPhasesN q ℓ K a v θt := ⟨_, rfl⟩
  obtain ⟨vs, hvs⟩ : ∃ vs, vs = (encCube q z).map (crecBits w) := ⟨_, rfl⟩
  obtain ⟨phs, hphs⟩ : ∃ phs, phs = (bcastArr θ).map (crecBits w) := ⟨_, rfl⟩
  obtain ⟨tab, htab⟩ : ∃ tab, tab = (tabRecs q ℓ θt).map (crecBits w) := ⟨_, rfl⟩
  have hlenvs : vs.length = 2 ^ addrBits a := by rw [hvs, List.length_map, length_encCube']
  have hlenθ : θ.length = 2 ^ addrBits a := by rw [hθ, length_twPhasesN]
  have hlenphs : phs.length = vs.length := by
    rw [hphs, hlenvs, List.length_map, bcastArr, List.length_map, hlenθ]
  have hlentab : tab.length = 2 * 2 ^ ℓ := by rw [htab, length_tab]
  have hvsu : ∀ p ∈ vs, p.length = 2 * 2 ^ ℓ * w := by rw [hvs]; exact length_mem_vs q w z
  have htabu : ∀ p ∈ tab, p.length = 2 * w := by rw [htab]; exact length_mem_tab w q ℓ θt
  have hJ : ∀ i, i < vs.length → 2 * IntForms.twJNat ℓ K a v i < tab.length := by
    intro i _
    rw [hlentab]
    have := IntForms.twJNat_lt ℓ K a v i
    omega
  have hsel : ∀ i (hi : i < vs.length),
      phs[i]'(by omega) = tab[2 * IntForms.twJNat ℓ K a v i]'(hJ i hi) := by
    intro i hi
    subst hphs htab hθ
    exact phs_getElem q ℓ K w a v θt i _ _
  -- 1. the header: `q` on `sc 11`, `w` on `sc 12`, `sc 13`, `sc 14`
  obtain ⟨S1, hS1d⟩ : ∃ S1, S1 = Function.update (Function.update (Function.update
      (Function.update S (sc 11) (natSyms q)) (sc 12) (natSyms w)) (sc 13) (natSyms w)) (sc 14)
      (natSyms w) := ⟨_, rfl⟩
  have e1 : Runs (hdrPhase (lW RA RC) (.inl 1) (sc 10) (sc 7) (sc 11) (sc 12) (sc 13) (sc 14))
      S S1 (fun _ => True) (27 * (midHdr q ℓ K w a).length) := by
    have h := runs_hdrPhase (lW RA RC) (HDR := .inl 1) (PK := sc 10) (TC := sc 7) (QS := sc 11)
      (W1 := sc 12) (W2 := sc 13) (W3 := sc 14) (by simp +decide) S q ℓ K w a hrest hS1
      (hsc 10) (hsc 7)
    rw [hsc 11, hsc 12, hsc 13, hsc 14] at h
    simp only [List.append_nil] at h
    rw [hS1d]
    exact h
  have hS1x : ∀ x, x ≠ sc 11 → x ≠ sc 12 → x ≠ sc 13 → x ≠ sc 14 → S1 x = S x := by
    intro x h1 h2 h3 h4
    rw [hS1d, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
      Function.update_of_ne h1]
  have hS1s : ∀ i : Fin 15, i ≠ 11 → i ≠ 12 → i ≠ 13 → i ≠ 14 → S1 (sc i) = [] := by
    intro i h1 h2 h3 h4
    rw [hS1x (sc i) (by simpa using h1) (by simpa using h2) (by simpa using h3) (by simpa using h4)]
    exact hsc i
  -- 2. the selection phase (one address call and one table scan per record)
  obtain ⟨S2, hS2d⟩ : ∃ S2, S2 = Function.update (Function.update (Function.update S1 (.inl 0)
      rest) (sc 8) (arrSyms vs)) (sc 9) (arrSyms phs) := ⟨_, rfl⟩
  have hcl1 : ∀ i (hi : i < vs.length), KClean
      (selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i ∘ (ιA (EC := EC))) := by
    intro i _ e
    show selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i (.inr (.inr (.inl e))) = []
    rw [show selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i (.inr (.inr (.inl e))) =
        S1 (.inr (.inr (.inl e))) from upd4_o (by simp) (by simp) (by simp) (by simp),
      hS1x (.inr (.inr (.inl e))) (by simp) (by simp) (by simp) (by simp)]
    exact hClean _
  have e2 : Runs (selPhase (lW RA RC) (callInj ιA (lsnd (Lens.fst RA RC)) PA) (.inl 0) (sc 0)
      (sc 1) (sc 2) (.inl 2) (sc 3) (sc 4) (sc 5) (sc 6) (sc 7) (sc 8) (sc 9)) S1 S2
      (fun _ => True) (vs.length * (selRecCost (2 * 2 ^ ℓ * w) (CA * (w + addrBits a + 1) ^ JA)
        tab.length (2 * w) vs.length + 2) + 2 + (3 * bitLen vs.length + 2 +
        (4 * (arrSyms vs).length + 2 + (4 * (arrSyms phs).length + 2)))) := by
    rw [hS2d]
    refine runs_selPhase (lW RA RC) (by simp +decide) (by simp +decide) (by simp +decide)
      (by simp +decide) (by simp +decide) (by simp +decide) (by simp +decide) (by simp +decide)
      (by simp +decide) (by simp +decide) _ S1 vs phs tab (2 * w) (2 * 2 ^ ℓ * w) rest trest
      (fun i => 2 * IntForms.twJNat ℓ K a v i) (CA * (w + addrBits a + 1) ^ JA) hvsu htabu
      hlenphs hJ hsel hrestB ?_ (hS1s 0 (by decide) (by decide) (by decide) (by decide))
      (hS1s 1 (by decide) (by decide) (by decide) (by decide))
      (hS1s 2 (by decide) (by decide) (by decide) (by decide)) ?_
      (hS1s 3 (by decide) (by decide) (by decide) (by decide))
      (hS1s 4 (by decide) (by decide) (by decide) (by decide))
      (hS1s 5 (by decide) (by decide) (by decide) (by decide))
      (hS1s 6 (by decide) (by decide) (by decide) (by decide))
      (hS1s 7 (by decide) (by decide) (by decide) (by decide))
      (hS1s 8 (by decide) (by decide) (by decide) (by decide))
      (hS1s 9 (by decide) (by decide) (by decide) (by decide)) ?_
    · rw [hS1x (.inl 0) (by simp) (by simp) (by simp) (by simp), hS0, hvs]
      rfl
    · rw [hS1x (.inl 2) (by simp) (by simp) (by simp) (by simp), hS2, htab]
      rfl
    · intro i hi
      have hi' : i < 2 ^ addrBits a := by rw [← hlenvs]; exact hi
      have hX0 : (selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i ∘ ιA) (.inl 0) =
          midHdr q ℓ K w a ++ hrest := by
        show selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i (.inl 1) = _
        rw [show selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i (.inl 1) = S1 (.inl 1)
            from upd4_o (by simp) (by simp) (by simp) (by simp),
          hS1x (.inl 1) (by simp) (by simp) (by simp) (by simp), hS1]
      have hX1 : (selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i ∘ ιA) (.inl 1) =
          natSyms v ++ crest := by
        show selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i (.inl 3) = _
        rw [show selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i (.inl 3) = S1 (.inl 3)
            from upd4_o (by simp) (by simp) (by simp) (by simp),
          hS1x (.inl 3) (by simp) (by simp) (by simp) (by simp), hS3]
      have hX2 : (selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i ∘ ιA) (.inl 2) =
          natSyms i ++ [] := by
        show selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i (sc 1) = _
        rw [List.append_nil]
        exact upd4_3 (by simp +decide)
      have hX5 : (selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i ∘ ιA) (.inl 3) = [] := by
        show selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i (sc 5) = []
        rw [show selMid S1 (.inl 0) (sc 0) (sc 1) (sc 2) vs phs rest i (sc 5) = S1 (sc 5)
            from upd4_o (by simp +decide) (by simp +decide) (by simp +decide) (by simp +decide)]
        exact hS1s 5 (by decide) (by decide) (by decide) (by decide)
      have h := hspecA q ℓ K w D v i a hrest crest [] _ (hcl1 i hi) hShape hv hi' hcrest
        TermOK.nil hX0 hX1 hX2
      rw [hX5, List.append_nil, ← Function.update_comp_eq_of_injective _ ιA_injective] at h
      refine runs_callInj ιA_injective _ h ?_
      intro k hk
      exact Function.update_of_ne (fun h' => hk (.inl 3) h'.symm) _ _
  -- 3. the broadcast multiplication, written back onto the array stack
  have hS2x : ∀ x, x ≠ .inl 0 → x ≠ sc 8 → x ≠ sc 9 → S2 x = S1 x := by
    intro x h1 h2 h3
    rw [hS2d, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  have hfit1 : CArrFits w (encCube q z) := CnotBatchRed.cArrFits_encCube hz hqw
  have hfit2 : CArrFits w (bcastArr θ) := by
    rw [hθ]; exact cArrFits_bcast q ℓ K w a v θt hTab hqw
  have hcm : cmulTruncBcast q (encCube q z) θ =
      encCube q (truncArr q (diagArr (fun x => θt (2 * twJ ℓ K a v x)) z)) := by
    rw [hθ]; exact cmul_eq q ℓ K a hK0 ha v θt z hz hTab
  have hfit3 : CArrFits w (cmulTruncBcast q (encCube q z) θ) := by
    rw [hcm]
    exact CnotBatchRed.cArrFits_encCube (arrOnDiskGrid_twiddle q ℓ K a v θt z hz hTab) hqw
  have hlenzθ : (encCube q z).length = θ.length := by rw [length_encCube', hlenθ]
  have hcl : KClean (S2 ∘ (ιC (EA := EA))) := by
    intro e
    show S2 (.inr (.inr (.inr e))) = []
    rw [hS2x (.inr (.inr (.inr e))) (by simp) (by simp) (by simp),
      hS1x (.inr (.inr (.inr e))) (by simp) (by simp) (by simp) (by simp)]
    exact hClean _
  have hC0 : (S2 ∘ ιC) (.inl 0) = carrSyms w (encCube q z) ++ [] := by
    show S2 (sc 8) = _
    rw [hS2d, Function.update_of_ne
      (show (sc 8 : KLoc (Fin 4) (TwE EA EC)) ≠ sc 9 by simp +decide), Function.update_self,
      List.append_nil, hvs]
    rfl
  have hC1 : (S2 ∘ ιC) (.inl 1) = carrSyms w (bcastArr θ) ++ [] := by
    show S2 (sc 9) = _
    rw [hS2d, Function.update_self, List.append_nil, hphs]
    rfl
  have hC3 : (S2 ∘ ιC) (.inl 3) = natSyms w ++ [] := by
    show S2 (sc 12) = _
    rw [hS2x (sc 12) (by simp) (by simp +decide) (by simp +decide), hS1d]
    simp +decide
  have hC4 : (S2 ∘ ιC) (.inl 4) = natSyms w ++ [] := by
    show S2 (sc 13) = _
    rw [hS2x (sc 13) (by simp) (by simp +decide) (by simp +decide), hS1d]
    simp +decide
  have hC5 : (S2 ∘ ιC) (.inl 5) = natSyms w ++ [] := by
    show S2 (sc 14) = _
    rw [hS2x (sc 14) (by simp) (by simp +decide) (by simp +decide), hS1d]
    simp +decide
  have hC6 : (S2 ∘ ιC) (.inl 6) = natSyms q ++ [] := by
    show S2 (sc 11) = _
    rw [hS2x (sc 11) (by simp) (by simp +decide) (by simp +decide), hS1d]
    simp +decide
  have hCrun := hspecC w w w q (encCube q z) θ [] [] [] [] [] [] (S2 ∘ ιC) hcl hw1 hw1 hw1 hfit1
    hfit2 hlenzθ hfit3 blkTerm_nil' blkTerm_nil' TermOK.nil TermOK.nil TermOK.nil TermOK.nil
    hC0 hC1 hC3 hC4 hC5 hC6
  obtain ⟨S3, hS3d⟩ : ∃ S3, S3 = Function.update (Function.update (Function.update S2
      (ιC (EA := EA) (.inl 0)) []) (ιC (EA := EA) (.inl 1)) []) (ιC (EA := EA) (.inl 2))
      (carrSyms w (cmulTruncBcast q (encCube q z) θ) ++ rest) := ⟨_, rfl⟩
  have hS3e : S3 = Function.update (Function.update (Function.update S2 (sc 8) []) (sc 9) [])
      (.inl 0) (carrSyms w (cmulTruncBcast q (encCube q z) θ) ++ rest) := hS3d
  have hcomp : S3 ∘ ιC = Function.update (Function.update (Function.update (S2 ∘ ιC) (.inl 0)
      []) (.inl 1) []) (.inl 2)
      (carrSyms w (cmulTruncBcast q (encCube q z) θ) ++ (S2 ∘ ιC) (.inl 2)) := by
    have h2 : (S2 ∘ (ιC (EA := EA))) (.inl 2) = rest := by
      show S2 (.inl 0) = rest
      rw [hS2d, Function.update_of_ne
        (show (Sum.inl 0 : KLoc (Fin 4) (TwE EA EC)) ≠ sc 9 by simp), Function.update_of_ne
        (show (Sum.inl 0 : KLoc (Fin 4) (TwE EA EC)) ≠ sc 8 by simp), Function.update_self]
    rw [h2, hS3d, Function.update_comp_eq_of_injective _ ιC_injective,
      Function.update_comp_eq_of_injective _ ιC_injective,
      Function.update_comp_eq_of_injective _ ιC_injective]
  rw [← hcomp] at hCrun
  have e3 := runs_callInj ιC_injective (lsnd (α := Option Sym) (Lens.snd RA RC)) hCrun
    (fun k hk => by
    rw [hS3d, Function.update_of_ne (fun h => hk (.inl 2) h.symm),
      Function.update_of_ne (fun h => hk (.inl 1) h.symm),
      Function.update_of_ne (fun h => hk (.inl 0) h.symm)])
  -- 4. drop the parameter copies
  have e4 := runs_drain (lW RA RC) (sc 12) S3
  rw [show S3 (sc 12) = natSyms w by simp +decide [hS3e, hS2d, hS1d],
    length_natSyms] at e4
  have e5 := runs_drain (lW RA RC) (sc 13) (Function.update S3 (sc 12) [])
  rw [show Function.update S3 (sc 12) [] (sc 13) = natSyms w by
    simp +decide [hS3e, hS2d, hS1d], length_natSyms] at e5
  have e6 := runs_drain (lW RA RC) (sc 14)
    (Function.update (Function.update S3 (sc 12) []) (sc 13) [])
  rw [show Function.update (Function.update S3 (sc 12) []) (sc 13) [] (sc 14) = natSyms w by
    simp +decide [hS3e, hS2d, hS1d], length_natSyms] at e6
  have e7 := runs_drain (lW RA RC) (sc 11)
    (Function.update (Function.update (Function.update S3 (sc 12) []) (sc 13) []) (sc 14) [])
  rw [show Function.update (Function.update (Function.update S3 (sc 12) []) (sc 13) []) (sc 14) []
    (sc 11) = natSyms q by simp +decide [hS3e, hS2d, hS1d],
    length_natSyms] at e7
  -- 5. assemble
  refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 (runs_seq' e3 (runs_seq' e4
    (runs_seq' e5 (runs_seq' e6 e7)))))) (fun _ _ => trivial) ?_) ?_
  · apply twTotal_le CA CC _ _ _ _ _ _ _ _ le_rfl
    · rw [hlenvs, hlentab,
        show (arrSyms vs).length = cvolCube (addrBits a) (2 ^ ℓ) w by
          rw [hvs]; exact cvol_encCube' q w z,
        show (arrSyms phs).length = 2 ^ addrBits a * (2 * w + 1) by
          rw [hphs, ← hlenθ]; exact cvol_bcast w θ]
      exact selPhaseCost_le CA JA q ℓ w (addrBits a) hq8 hℓq hqw hℓ2
    · rw [ncoef_encCube, cvol_encCube', cvol_bcast, hlenθ]
      exact cmulCost_le CC q w ℓ (addrBits a) hq8 hqw
    · exact drainCost_le q w ℓ (addrBits a) hq8 hqw hℓ2
  · rw [← hcm, hS3e, hS2d, hS1d]
    exact tw_final S hClean q w rest _ _ _

end SubNLogN.Machine.FFT
