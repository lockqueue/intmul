/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixKit
import SubNLogN.Machine.FFT.PrefixParamSpec
import SubNLogN.Machine.FFT.PrefixPassSpec

/-!
# K4-PREFIX, stack layout and sub-kernel calls (`Machine/FFT/PrefixLayout.lean`)

Layout of the prefix-round kernel (`PrefixRoundStmt`, `Contracts/FFT.lean:239`):
* named stacks `nD` (data, `.inl 0`), `nH` (header, `.inl 1`), `nV` (round index, `.inl 3`);
* private stacks `ps d`, `d : PS`;
* the scratch of the three sub-kernels: the parameter phase (`PrefixParamStmt`), one butterfly
  pass (`PrefixPassStmt`), and the truncation (`TruncShiftStmt`, `Contracts/Arith.lean`).

The sub-kernels enter as definitional copies of their contract bodies (`ParamSpec`, `PassSpec`,
`TrSpec`), with `Runs` lemmas for their calls along injective embeddings (`runs_callInj`).
All proved, no `sorry`.
-/

namespace SubNLogN.Machine.FFT.PrefixAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine.FFT.DIF SubNLogN.Math.Walsh

/-- The kernel's own private stacks. -/
inductive PS
  | H | HA | G | GA | NP | E1 | E2 | E3 | T | WB1 | WB2 | WS | ONE | ZS | TMP | AUX
  deriving DecidableEq

instance : Fintype PS :=
  Fintype.ofList [.H, .HA, .G, .GA, .NP, .E1, .E2, .E3, .T, .WB1, .WB2, .WS, .ONE, .ZS, .TMP,
    .AUX] (by intro x; cases x <;> simp)

/-- The full layout: named stacks (`Fin 4`), the kernel's stacks, and the scratch of the
parameter kernel (`Er`), of the pass kernel (`Ep`) and of the truncation kernel (`Et`). -/
abbrev KP (Er Ep Et : Type) : Type := KLoc (Fin 4) (PS ⊕ (Er ⊕ (Ep ⊕ Et)))

section Layout

variable {Er Ep Et : Type}

/-- A kernel stack. -/
def ps (d : PS) : KP Er Ep Et := .inr (.inl d)

/-- The data stack, the header stack and the round-index stack. -/
def nD : KP Er Ep Et := .inl 0
def nH : KP Er Ep Et := .inl 1
def nV : KP Er Ep Et := .inl 3

/-- Parameter kernel: `0 ↦ nH`, `1 ↦ nV`, `2 ↦ H`, `3 ↦ G`, `4 ↦ WB1`, `5 ↦ WS`. -/
def ιr : KLoc (Fin 6) Er → KP Er Ep Et
  | .inl i => ![nH, nV, ps .H, ps .G, ps .WB1, ps .WS] i
  | .inr e => .inr (.inr (.inl e))

/-- Pass kernel: `0 ↦ E1`, `1 ↦ H`, `2 ↦ WB1`. -/
def ιp : KLoc (Fin 3) Ep → KP Er Ep Et
  | .inl i => ![ps .E1, ps .H, ps .WB1] i
  | .inr e => .inr (.inr (.inr (.inl e)))

/-- Truncation kernel, widening `w → W`: `0 ↦ nD`, `1 ↦ E1`, `2 ↦ WS`, `3 ↦ WB1`, `4 ↦ ZS`. -/
def ιtW : KLoc (Fin 5) Et → KP Er Ep Et
  | .inl i => ![nD, ps .E1, ps .WS, ps .WB1, ps .ZS] i
  | .inr e => .inr (.inr (.inr (.inr e)))

/-- Truncation kernel, one halving at width `W`: `0 ↦ E1`, `1 ↦ E2`, `2 ↦ WB1`, `3 ↦ WB2`,
`4 ↦ ONE`. -/
def ιt1 : KLoc (Fin 5) Et → KP Er Ep Et
  | .inl i => ![ps .E1, ps .E2, ps .WB1, ps .WB2, ps .ONE] i
  | .inr e => .inr (.inr (.inr (.inr e)))

/-- Truncation kernel, narrowing `W → w`: `0 ↦ E1`, `1 ↦ nD`, `2 ↦ WB1`, `3 ↦ WS`, `4 ↦ ZS`. -/
def ιtF : KLoc (Fin 5) Et → KP Er Ep Et
  | .inl i => ![ps .E1, nD, ps .WB1, ps .WS, ps .ZS] i
  | .inr e => .inr (.inr (.inr (.inr e)))

theorem ιr_injective : Function.Injective (ιr : KLoc (Fin 6) Er → KP Er Ep Et) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [ιr, ps, nH, nV]
  · fin_cases i <;> simp [ιr, ps, nH, nV] at h
  · fin_cases j <;> simp [ιr, ps, nH, nV] at h
  · simp only [ιr, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem ιp_injective : Function.Injective (ιp : KLoc (Fin 3) Ep → KP Er Ep Et) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [ιp, ps]
  · fin_cases i <;> simp [ιp, ps] at h
  · fin_cases j <;> simp [ιp, ps] at h
  · simp only [ιp, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem ιtW_injective : Function.Injective (ιtW : KLoc (Fin 5) Et → KP Er Ep Et) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [ιtW, ps, nD]
  · fin_cases i <;> simp [ιtW, ps, nD] at h
  · fin_cases j <;> simp [ιtW, ps, nD] at h
  · simp only [ιtW, Sum.inr.injEq] at h
    rw [h]

theorem ιt1_injective : Function.Injective (ιt1 : KLoc (Fin 5) Et → KP Er Ep Et) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [ιt1, ps]
  · fin_cases i <;> simp [ιt1, ps] at h
  · fin_cases j <;> simp [ιt1, ps] at h
  · simp only [ιt1, Sum.inr.injEq] at h
    rw [h]

theorem ιtF_injective : Function.Injective (ιtF : KLoc (Fin 5) Et → KP Er Ep Et) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [ιtF, ps, nD]
  · fin_cases i <;> simp [ιtF, ps, nD] at h
  · fin_cases j <;> simp [ιtF, ps, nD] at h
  · simp only [ιtF, Sum.inr.injEq] at h
    rw [h]

@[simp] theorem ps_inj {a b : PS} : (ps a : KP Er Ep Et) = ps b ↔ a = b := by simp [ps]
@[simp] theorem ps_ne_nD (d : PS) : (ps d : KP Er Ep Et) ≠ nD := by simp [ps, nD]
@[simp] theorem nD_ne_ps (d : PS) : (nD : KP Er Ep Et) ≠ ps d := by simp [ps, nD]
@[simp] theorem ps_ne_nH (d : PS) : (ps d : KP Er Ep Et) ≠ nH := by simp [ps, nH]
@[simp] theorem nH_ne_ps (d : PS) : (nH : KP Er Ep Et) ≠ ps d := by simp [ps, nH]
@[simp] theorem ps_ne_nV (d : PS) : (ps d : KP Er Ep Et) ≠ nV := by simp [ps, nV]
@[simp] theorem nV_ne_ps (d : PS) : (nV : KP Er Ep Et) ≠ ps d := by simp [ps, nV]
@[simp] theorem nD_ne_nH : (nD : KP Er Ep Et) ≠ nH := by simp [nD, nH]
@[simp] theorem nH_ne_nD : (nH : KP Er Ep Et) ≠ nD := by simp [nD, nH]
@[simp] theorem nD_ne_nV : (nD : KP Er Ep Et) ≠ nV := by simp [nD, nV]
@[simp] theorem nV_ne_nD : (nV : KP Er Ep Et) ≠ nD := by simp [nD, nV]
@[simp] theorem nH_ne_nV : (nH : KP Er Ep Et) ≠ nV := by simp [nH, nV]
@[simp] theorem nV_ne_nH : (nV : KP Er Ep Et) ≠ nH := by simp [nH, nV]

end Layout

/-! ## The sub-kernels as hypotheses on given programs -/

/-- The `spec` body of `PrefixParamStmt` (for a fixed exponent `J`), for a given program. -/
def ParamSpec (Er : Type) [DecidableEq Er] (R : Type) (C J : ℕ)
    (P : Prog (KLoc (Fin 6) Er) (fun _ => Sym) R) : Prop :=
  ∀ (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (hrest crest : List Sym)
    (S : KLoc (Fin 6) Er → List Sym),
    KClean S → MidShapeOK q ℓ K w a → v < ℓ → ¬ IsChunkRound ℓ K v → TermOK crest →
    S (.inl 0) = midHdr q ℓ K w a ++ hrest →
    S (.inl 1) = natSyms v ++ crest →
    Runs P S
      (Function.update (Function.update (Function.update (Function.update S
        (.inl 2) (List.replicate (2 ^ (D * pfY ℓ K v)) .mark ++ S (.inl 2)))
        (.inl 3) (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark ++ S (.inl 3)))
        (.inl 4) (natSyms (w + D) ++ S (.inl 4)))
        (.inl 5) (natSyms w ++ S (.inl 5)))
      (fun _ => True)
      (C * (2 ^ addrBits a * (w + addrBits a + 1) ^ J + (midHdr q ℓ K w a).length))

/-- The `spec` body of `PrefixPassStmt`, for a given program. -/
def PassSpec (Ep : Type) [DecidableEq Ep] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 3) Ep) (fun _ => Sym) R) : Prop :=
  ∀ (W h M r : ℕ) (B : List (List CInt)) (rest r2 : List Sym) (S : KLoc (Fin 3) Ep → List Sym),
    KClean S → 1 ≤ W → 1 ≤ h → B.length = 2 * h * M → (∀ row ∈ B, row.length = r) →
    CArrFits W B → CArrFits W (bpass h M B) → BlkTerm rest → TermOK r2 →
    S (.inl 0) = carrSyms W B ++ rest →
    S (.inl 1) = List.replicate h .mark →
    S (.inl 2) = natSyms W ++ r2 →
    Runs P S (Function.update S (.inl 0) (carrSyms W (bpass h M B) ++ rest))
      (fun _ => True) (C * (cvol W B + W + 1))

/-- The `spec` body of `TruncShiftStmt` (`Contracts/Arith.lean`), for a given program. -/
def TrSpec (Et : Type) [DecidableEq Et] (R : Type) (C : ℕ)
    (P : Prog (KLoc (Fin 5) Et) (fun _ => Sym) R) : Prop :=
  ∀ (w1 w2 s : ℕ) (v : List (List CInt)) (rest r2 r3 r4 : List Sym)
    (S : KLoc (Fin 5) Et → List Sym),
    1 ≤ w1 → 1 ≤ w2 → CArrFits w1 v → CArrFits w2 (mapC (truncShiftC s) v) →
    BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 →
    S (.inl 0) = carrSyms w1 v ++ rest → S (.inl 2) = natSyms w1 ++ r2 →
    S (.inl 3) = natSyms w2 ++ r3 → S (.inl 4) = natSyms s ++ r4 →
    Runs P S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (carrSyms w2 (mapC (truncShiftC s) v) ++ S (.inl 1)))
      (fun _ => True) (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1))

theorem natSyms_zero : natSyms 0 = [] := rfl

theorem blkTerm_nil : BlkTerm ([] : List Sym) := fun _ h => by simp at h

section Calls

variable {Er Ep Et : Type} [DecidableEq Er] [DecidableEq Ep] [DecidableEq Et] {σ Rr Rp Rt : Type}

theorem runs_paramCall (lr : Lens σ Rr) {Cr J : ℕ} {Pr : Prog (KLoc (Fin 6) Er) (fun _ => Sym) Rr}
    (hP : ParamSpec Er Rr Cr J Pr) (B : KP Er Ep Et → List Sym)
    (hclean : ∀ e : Er, B (.inr (.inr (.inl e))) = [])
    (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (hrest crest : List Sym)
    (hshape : MidShapeOK q ℓ K w a) (hv : v < ℓ) (hnc : ¬ IsChunkRound ℓ K v)
    (hcrest : TermOK crest)
    (hH : B nH = midHdr q ℓ K w a ++ hrest) (hV : B nV = natSyms v ++ crest) :
    Runs (callInj ιr lr Pr) B
      (Function.update (Function.update (Function.update (Function.update B
        (ps .H) (List.replicate (2 ^ (D * pfY ℓ K v)) .mark ++ B (ps .H)))
        (ps .G) (List.replicate (if v + 1 = ℓ then 0 else 2 ^ D - 1) .mark ++ B (ps .G)))
        (ps .WB1) (natSyms (w + D) ++ B (ps .WB1)))
        (ps .WS) (natSyms w ++ B (ps .WS)))
      (fun _ => True)
      (Cr * (2 ^ addrBits a * (w + addrBits a + 1) ^ J + (midHdr q ℓ K w a).length)) := by
  have h := hP q ℓ K w D v a hrest crest (B ∘ ιr) (fun e => by simp [ιr, hclean]) hshape hv hnc
    hcrest (by simp [ιr, hH]) (by simp [ιr, hV])
  refine runs_callInj ιr_injective lr (Q := fun _ => True) ?_ ?_
  · refine runs_congr h ?_
    funext x
    rcases x with (i | e)
    · fin_cases i <;> simp [ιr, ps, nH, nV, Function.update_apply]
    · simp [ιr, ps, Function.update_apply]
  · intro k hk
    have h1 : k ≠ ps .H := fun h => hk (.inl 2) (by simp [ιr, h])
    have h2 : k ≠ ps .G := fun h => hk (.inl 3) (by simp [ιr, h])
    have h3 : k ≠ ps .WB1 := fun h => hk (.inl 4) (by simp [ιr, h])
    have h4 : k ≠ ps .WS := fun h => hk (.inl 5) (by simp [ιr, h])
    simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4]

theorem runs_passCall (lp : Lens σ Rp) {Cp : ℕ} {Pp : Prog (KLoc (Fin 3) Ep) (fun _ => Sym) Rp}
    (hP : PassSpec Ep Rp Cp Pp) (B : KP Er Ep Et → List Sym)
    (hclean : ∀ e : Ep, B (.inr (.inr (.inr (.inl e)))) = [])
    (W h M r : ℕ) (B0 : List (List CInt)) (hW : 1 ≤ W) (hh : 1 ≤ h)
    (hlen : B0.length = 2 * h * M) (hrow : ∀ row ∈ B0, row.length = r)
    (hfit : CArrFits W B0) (hfit' : CArrFits W (bpass h M B0))
    (hE : B (ps .E1) = carrSyms W B0) (hH : B (ps .H) = List.replicate h .mark)
    (hWB : B (ps .WB1) = natSyms W) :
    Runs (callInj ιp lp Pp) B (Function.update B (ps .E1) (carrSyms W (bpass h M B0)))
      (fun _ => True) (Cp * (cvol W B0 + W + 1)) := by
  have h := hP W h M r B0 [] [] (B ∘ ιp) (fun e => by simp [ιp, hclean]) hW hh hlen hrow hfit
    hfit' blkTerm_nil TermOK.nil (by simp [ιp, hE]) (by simp [ιp, hH]) (by simp [ιp, hWB])
  refine runs_callInj ιp_injective lp (Q := fun _ => True) ?_ ?_
  · refine runs_congr h ?_
    funext x
    rcases x with (i | e)
    · fin_cases i <;> simp [ιp, ps, Function.update_apply]
    · simp [ιp, ps, Function.update_apply]
  · intro k hk
    have h1 : k ≠ ps .E1 := fun h => hk (.inl 0) (by simp [ιp, h])
    simp only [Function.update_of_ne h1]

theorem runs_trW (lt : Lens σ Rt) {Ct : ℕ} {Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt}
    (hP : TrSpec Et Rt Ct Pt) (B : KP Er Ep Et → List Sym) (w W : ℕ) (v : List (List CInt))
    (rest : List Sym) (hw : 1 ≤ w) (hW : 1 ≤ W) (hfit : CArrFits w v)
    (hfit' : CArrFits W (mapC (truncShiftC 0) v)) (hrest : BlkTerm rest)
    (hD : B nD = carrSyms w v ++ rest) (hWS : B (ps .WS) = natSyms w)
    (hWB : B (ps .WB1) = natSyms W) (hZ : B (ps .ZS) = []) :
    Runs (callInj ιtW lt Pt) B
      (Function.update (Function.update B nD rest) (ps .E1)
        (carrSyms W (mapC (truncShiftC 0) v) ++ B (ps .E1)))
      (fun _ => True) (Ct * (cvol w v + cvol W v + w + W + bitLen 0 + 1)) := by
  have h := hP w W 0 v rest [] [] [] (B ∘ ιtW) hw hW hfit hfit' hrest TermOK.nil TermOK.nil
    TermOK.nil (by simp [ιtW, hD]) (by simp [ιtW, hWS]) (by simp [ιtW, hWB])
    (by simp [ιtW, hZ, natSyms_zero])
  refine runs_callInj ιtW_injective lt (Q := fun _ => True) ?_ ?_
  · refine runs_congr h ?_
    funext x
    rcases x with (i | e)
    · fin_cases i <;> simp [ιtW, ps, nD, Function.update_apply]
    · simp [ιtW, ps, nD, Function.update_apply]
  · intro k hk
    have h1 : k ≠ nD := fun h => hk (.inl 0) (by simp [ιtW, h])
    have h2 : k ≠ ps .E1 := fun h => hk (.inl 1) (by simp [ιtW, h])
    simp only [Function.update_of_ne h1, Function.update_of_ne h2]

theorem runs_tr1 (lt : Lens σ Rt) {Ct : ℕ} {Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt}
    (hP : TrSpec Et Rt Ct Pt) (B : KP Er Ep Et → List Sym) (W : ℕ) (v : List (List CInt))
    (hW : 1 ≤ W) (hfit : CArrFits W v) (hfit' : CArrFits W (mapC (truncShiftC 1) v))
    (hE : B (ps .E1) = carrSyms W v) (hWB1 : B (ps .WB1) = natSyms W)
    (hWB2 : B (ps .WB2) = natSyms W) (hONE : B (ps .ONE) = natSyms 1) :
    Runs (callInj ιt1 lt Pt) B
      (Function.update (Function.update B (ps .E1) []) (ps .E2)
        (carrSyms W (mapC (truncShiftC 1) v) ++ B (ps .E2)))
      (fun _ => True) (Ct * (cvol W v + cvol W v + W + W + bitLen 1 + 1)) := by
  have h := hP W W 1 v [] [] [] [] (B ∘ ιt1) hW hW hfit hfit' blkTerm_nil TermOK.nil TermOK.nil
    TermOK.nil (by simp [ιt1, hE]) (by simp [ιt1, hWB1]) (by simp [ιt1, hWB2])
    (by simp [ιt1, hONE])
  refine runs_callInj ιt1_injective lt (Q := fun _ => True) ?_ ?_
  · refine runs_congr h ?_
    funext x
    rcases x with (i | e)
    · fin_cases i <;> simp [ιt1, ps, Function.update_apply]
    · simp [ιt1, ps, Function.update_apply]
  · intro k hk
    have h1 : k ≠ ps .E1 := fun h => hk (.inl 0) (by simp [ιt1, h])
    have h2 : k ≠ ps .E2 := fun h => hk (.inl 1) (by simp [ιt1, h])
    simp only [Function.update_of_ne h1, Function.update_of_ne h2]

theorem runs_trF (lt : Lens σ Rt) {Ct : ℕ} {Pt : Prog (KLoc (Fin 5) Et) (fun _ => Sym) Rt}
    (hP : TrSpec Et Rt Ct Pt) (B : KP Er Ep Et → List Sym) (W w : ℕ) (v : List (List CInt))
    (hW : 1 ≤ W) (hw : 1 ≤ w) (hfit : CArrFits W v) (hfit' : CArrFits w (mapC (truncShiftC 0) v))
    (hE : B (ps .E1) = carrSyms W v) (hWB1 : B (ps .WB1) = natSyms W)
    (hWS : B (ps .WS) = natSyms w) (hZ : B (ps .ZS) = []) :
    Runs (callInj ιtF lt Pt) B
      (Function.update (Function.update B (ps .E1) []) nD
        (carrSyms w (mapC (truncShiftC 0) v) ++ B nD))
      (fun _ => True) (Ct * (cvol W v + cvol w v + W + w + bitLen 0 + 1)) := by
  have h := hP W w 0 v [] [] [] [] (B ∘ ιtF) hW hw hfit hfit' blkTerm_nil TermOK.nil TermOK.nil
    TermOK.nil (by simp [ιtF, hE]) (by simp [ιtF, hWB1]) (by simp [ιtF, hWS])
    (by simp [ιtF, hZ, natSyms_zero])
  refine runs_callInj ιtF_injective lt (Q := fun _ => True) ?_ ?_
  · refine runs_congr h ?_
    funext x
    rcases x with (i | e)
    · fin_cases i <;> simp [ιtF, ps, nD, Function.update_apply]
    · simp [ιtF, ps, nD, Function.update_apply]
  · intro k hk
    have h1 : k ≠ ps .E1 := fun h => hk (.inl 0) (by simp [ιtF, h])
    have h2 : k ≠ nD := fun h => hk (.inl 1) (by simp [ιtF, h])
    simp only [Function.update_of_ne h1, Function.update_of_ne h2]

end Calls

end SubNLogN.Machine.FFT.PrefixAux
