/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseKind

/-!
# C-core phase leaf: the `zSlot`/`zMask` path (`CCore/LeafPhaseMask.lean`)

**Scope (honest summary).** Exact runs, everything proved (relative to the sub-kernel specs passed
as arguments):
* `ι9 ns j`, `runs_maskCall`: a `MaskSelStmt` kernel (`LeafPhaseMaskDefs.lean`) on the work layout;
* `maskMid u P₂ Pm`: move role `u`'s array to `X`, copy it to `X2`, `X2 ↦ Xn = ×i²` (`RotIPowStmt`,
  `e = 2`), select record-wise between `X` and `Xn` into `Y` (`MaskSelStmt`), move `Y` back;
  `safe_maskMid`.
-/

namespace SubNLogN.Machine.CCore.LeafScalarAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus Computability
open SubNLogN.Math.Common SubNLogN.Math.Walsh SubNLogN.Math.Networks SubNLogN.Machine.Layer.DrvPreK

variable {Er : Type}

/-- The `Fin 9` sub-kernel layout at the scratch stacks `ns`, private scratch through `j`. -/
def ι9 {Er' : Type} (ns : Fin 9 → PS) (j : Er' → Er) : KLoc (Fin 9) Er' → Lw Er
  | .inl i => wS (ns i)
  | .inr e => .inr (j e)

/-- The stacks of the `MaskSelStmt` call: `X, Xn, Y` and the counters `K, D, S, j0, k, ρ`. -/
def nsM : Fin 9 → PS := ![.X, .Xn, .Y, .cK, .cDD, .cS, .cJ, .cKk, .cRho]

theorem nsM_injective : Function.Injective nsM := by decide

theorem ι9_injective {Er' : Type} {ns : Fin 9 → PS} (hns : Function.Injective ns) {j : Er' → Er}
    (hj : Function.Injective j) : Function.Injective (ι9 (Er := Er) ns j) := by
  rintro (i | e) (i' | e') h
  · simp only [ι9, wS, Sum.inl.injEq, Option.some.injEq] at h
    rw [hns h]
  · simp [ι9] at h
  · simp [ι9] at h
  · simp only [ι9, Sum.inr.injEq] at h
    rw [hj h]

variable [DecidableEq Er]

/-- **A `MaskSelStmt` call** on the work layout. -/
theorem runs_maskCall {Er' Rr Rr' : Type} [DecidableEq Er'] (lr : Lens (σ Rr) Rr')
    {ss : Finset (Fin mn)} {C : ℕ} {P : Prog (KLoc (Fin 9) Er') (fun _ => Sym) Rr'}
    (hspec : ∀ (K D S j0 k ρ : ℕ) (v vn : List (List Bool))
      (rx rxn r3 r4 r5 r6 r7 r8 : List Sym) (St : KLoc (Fin 9) Er' → List Sym),
      KClean St → 1 ≤ k → ρ < K → j0 + mn ^ k ≤ D → 1 ≤ S → v.length = vn.length →
      BlkTerm rx → BlkTerm rxn →
      TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 → TermOK r7 → TermOK r8 →
      St (.inl 0) = arrSyms v ++ rx → St (.inl 1) = arrSyms vn ++ rxn →
      St (.inl 3) = natSyms K ++ r3 → St (.inl 4) = natSyms D ++ r4 →
      St (.inl 5) = natSyms S ++ r5 → St (.inl 6) = natSyms j0 ++ r6 →
      St (.inl 7) = natSyms k ++ r7 → St (.inl 8) = natSyms ρ ++ r8 →
      Runs P St
        (Function.update (Function.update (Function.update St (.inl 0) rx) (.inl 1) rxn) (.inl 2)
          (arrSyms (selRecs (selBit ss K D S j0 (mn ^ (k - 1)) ρ) v vn) ++ St (.inl 2)))
        (fun _ => True) (C * (vol v + vol vn + 2 ^ (K * D) + S + D + 1)))
    {j : Er' → Er} (hj : Function.Injective j) (d : List Sym) (sc : PS → List Sym)
    (er : Er → List Sym) (her : ∀ e, er (j e) = []) (t : CCoreRT) (hk : 1 ≤ t.k)
    (hρ : t.ρ < t.K) (hjD : t.j0 + mn ^ t.k ≤ t.D) (hS : 1 ≤ t.S)
    (v vn : List (List Bool)) (hlen : v.length = vn.length)
    (hX : sc .X = arrSyms v ++ [Sym.mark]) (hXn : sc .Xn = arrSyms vn ++ [Sym.mark])
    (hY : sc .Y = [Sym.mark]) (hK : sc .cK = natSyms t.K ++ [Sym.mark])
    (hD : sc .cDD = natSyms t.D ++ [Sym.mark]) (hSc : sc .cS = natSyms t.S ++ [Sym.mark])
    (hJ : sc .cJ = natSyms t.j0 ++ [Sym.mark]) (hKk : sc .cKk = natSyms t.k ++ [Sym.mark])
    (hR : sc .cRho = natSyms t.ρ ++ [Sym.mark]) :
    Runs (callInj (ι9 nsM j) lr P) (wst d sc er)
      (wst d (Function.update (Function.update (Function.update sc .X [Sym.mark]) .Xn [Sym.mark]) .Y
        (arrSyms (selRecs (selBit ss t.K t.D t.S t.j0 (mn ^ (t.k - 1)) t.ρ) v vn) ++ [Sym.mark])) er)
      (fun _ => True) (C * (vol v + vol vn + 2 ^ (t.K * t.D) + t.S + t.D + 1)) := by
  have tm : TermOK [Sym.mark] := TermOK.cons rfl _
  refine runs_callInj (Q := fun _ => True) (ι9_injective nsM_injective hj) lr ?_ ?_
  · have h := hspec t.K t.D t.S t.j0 t.k t.ρ v vn [Sym.mark] [Sym.mark] [Sym.mark] [Sym.mark]
      [Sym.mark] [Sym.mark] [Sym.mark] [Sym.mark] (wst d sc er ∘ ι9 nsM j)
      (fun e => by simp [ι9, her]) hk hρ hjD hS hlen blkTerm_mark blkTerm_mark tm tm tm tm tm tm
      (by simp [ι9, nsM, hX]) (by simp [ι9, nsM, hXn]) (by simp [ι9, nsM, hK])
      (by simp [ι9, nsM, hD]) (by simp [ι9, nsM, hSc]) (by simp [ι9, nsM, hJ])
      (by simp [ι9, nsM, hKk]) (by simp [ι9, nsM, hR])
    refine WP.W9comp.runs_congr h ?_
    funext x
    rcases x with i | x
    · fin_cases i <;> simp [ι9, nsM, Function.update_apply, hY]
    · simp [ι9, Function.update_apply]
  · intro k hk
    rcases k with (_ | q) | x
    · rfl
    · simp only [wst, Function.update_apply]
      have hq0 : q ≠ .X := fun h => hk (.inl 0) (by simp [ι9, nsM, h])
      have hq1 : q ≠ .Xn := fun h => hk (.inl 1) (by simp [ι9, nsM, h])
      have hq2 : q ≠ .Y := fun h => hk (.inl 2) (by simp [ι9, nsM, h])
      simp [hq0, hq1, hq2]
    · rfl

/-! ## The middle of the mask path -/

section MaskMid

variable {E2 Em R2 Rm : Type} [DecidableEq E2] [DecidableEq Em]

/-- Lens to the `RotIPowStmt` registers. -/
def lRot (R2 Rm : Type) : Lens (σ (R2 × Rm)) R2 := (lR (R2 × Rm)).comp (Lens.fst R2 Rm)

/-- Lens to the `MaskSelStmt` registers. -/
def lMs (R2 Rm : Type) : Lens (σ (R2 × Rm)) Rm := (lR (R2 × Rm)).comp (Lens.snd R2 Rm)

/-- Scratch part of the mask path: copy `X` to `X2`, `Xn ← ×i²(X2)`, `Y ← select(X, Xn)`. -/
def coreM (P2 : Prog (KLoc (Fin 3) E2) (fun _ => Sym) R2)
    (Pm : Prog (KLoc (Fin 9) Em) (fun _ => Sym) Rm) :
    Prog (Lw (E2 ⊕ Em)) (fun _ => Sym) (σ (R2 × Rm)) :=
  .seq ((passC Sym.mark (wS .X) (wS .Tm) (wS .X2)).liftRegs (lO _))
    (.seq (callInj (ι3 .X2 .Xn .cW Sum.inl) (lRot R2 Rm) P2)
      (callInj (ι9 nsM Sum.inr) (lMs R2 Rm) Pm))

/-- Move in, `coreM`, move out. -/
def maskMid (u : Fin Wn) (P2 : Prog (KLoc (Fin 3) E2) (fun _ => Sym) R2)
    (Pm : Prog (KLoc (Fin 9) Em) (fun _ => Sym) Rm) :
    Prog (BL (E2 ⊕ Em)) (fun _ => Sym) (σ (R2 × Rm)) :=
  .seq (mvIn _ u) (.seq (callInj ιw (lid _) (coreM P2 Pm)) (mvOut _ u))

theorem closed_maskMid (u : Fin Wn) {P2 : Prog (KLoc (Fin 3) E2) (fun _ => Sym) R2}
    {Pm : Prog (KLoc (Fin 9) Em) (fun _ => Sym) Rm} (h2 : P2.Closed) (hm : Pm.Closed) :
    (maskMid u P2 Pm).Closed :=
  ⟨closed_mvIn _ _, closed_callInj _ _ ⟨WP.W9comp.closed_liftRegs _ (closed_passC _ _ _ _),
    closed_callInj _ _ h2, closed_callInj _ _ hm⟩, closed_mvOut _ _⟩

theorem safe_maskMid {C2 Cm : ℕ} {ss : Finset (Fin mn)}
    {P2 : Prog (KLoc (Fin 3) E2) (fun _ => Sym) R2} {Pm : Prog (KLoc (Fin 9) Em) (fun _ => Sym) Rm}
    (hspec2 : ∀ (w : ℕ) (v : List (List CInt)) (rest r2 : List Sym)
      (S : KLoc (Fin 3) E2 → List Sym),
      1 ≤ w → CArrFits w v → CArrFits w (mapC (rotIPowC 2) v) → BlkTerm rest → TermOK r2 →
      S (.inl 0) = carrSyms w v ++ rest → S (.inl 2) = natSyms w ++ r2 →
      Runs P2 S
        (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (carrSyms w (mapC (rotIPowC 2) v) ++ S (.inl 1)))
        (fun _ => True) (C2 * (cvol w v + w + 1)))
    (hspecm : ∀ (K D S j0 k ρ : ℕ) (v vn : List (List Bool))
      (rx rxn r3 r4 r5 r6 r7 r8 : List Sym) (St : KLoc (Fin 9) Em → List Sym),
      KClean St → 1 ≤ k → ρ < K → j0 + mn ^ k ≤ D → 1 ≤ S → v.length = vn.length →
      BlkTerm rx → BlkTerm rxn →
      TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 → TermOK r7 → TermOK r8 →
      St (.inl 0) = arrSyms v ++ rx → St (.inl 1) = arrSyms vn ++ rxn →
      St (.inl 3) = natSyms K ++ r3 → St (.inl 4) = natSyms D ++ r4 →
      St (.inl 5) = natSyms S ++ r5 → St (.inl 6) = natSyms j0 ++ r6 →
      St (.inl 7) = natSyms k ++ r7 → St (.inl 8) = natSyms ρ ++ r8 →
      Runs Pm St
        (Function.update (Function.update (Function.update St (.inl 0) rx) (.inl 1) rxn) (.inl 2)
          (arrSyms (selRecs (selBit ss K D S j0 (mn ^ (k - 1)) ρ) v vn) ++ St (.inl 2)))
        (fun _ => True) (Cm * (vol v + vol vn + 2 ^ (K * D) + S + D + 1)))
    (h2 : P2.Closed) (hm : Pm.Closed) (u : Fin Wn) (t : CCoreRT) (hk : 1 ≤ t.k)
    (hρ : t.ρ < t.K) (hjD : t.j0 + mn ^ t.k ≤ t.D) (hS : 1 ≤ t.S) (v : List (List CInt))
    (S0 : BL (E2 ⊕ Em) → List Sym) (hcl : ∀ e, S0 (.inr (.inr e)) = []) (sc : PS → List Sym)
    (hu : S0 (roleL u) = carrSyms t.wg v ++ [Sym.mark])
    (hX : sc .X = [Sym.mark]) (hY : sc .Y = [Sym.mark]) (hT : sc .Tm = [Sym.mark])
    (hX2 : sc .X2 = [Sym.mark]) (hXn : sc .Xn = [Sym.mark]) (hW : sc .cW = natSyms t.wg)
    (hK : sc .cK = natSyms t.K ++ [Sym.mark]) (hD : sc .cDD = natSyms t.D ++ [Sym.mark])
    (hSc : sc .cS = natSyms t.S ++ [Sym.mark]) (hJ : sc .cJ = natSyms t.j0 ++ [Sym.mark])
    (hKk : sc .cKk = natSyms t.k ++ [Sym.mark]) (hR : sc .cRho = natSyms t.ρ ++ [Sym.mark])
    (hf1 : CArrFits t.wg v) (hf2 : CArrFits t.wg (mapC (rotIPowC 2) v)) :
    SafeRunsIn ccoreFramed [] (maskMid u P2 Pm) (stv S0 sc)
      (stv (Function.update S0 (roleL u)
        (arrSyms (selRecs (selBit ss t.K t.D t.S t.j0 (mn ^ (t.k - 1)) t.ρ)
          (v.map (crecBits t.wg)) ((mapC (rotIPowC 2) v).map (crecBits t.wg))) ++ [Sym.mark])) sc)
      (fun _ => True)
      (8 * cvol t.wg v + 4 + (9 * cvol t.wg v + 4 + C2 * (cvol t.wg v + t.wg + 1) +
        Cm * (cvol t.wg v + cvol t.wg v + 2 ^ (t.K * t.D) + t.S + t.D + 1)) +
        (8 * (arrSyms (selRecs (selBit ss t.K t.D t.S t.j0 (mn ^ (t.k - 1)) t.ρ)
          (v.map (crecBits t.wg)) ((mapC (rotIPowC 2) v).map (crecBits t.wg)))).length + 4)) := by
  set sel := selRecs (selBit ss t.K t.D t.S t.j0 (mn ^ (t.k - 1)) t.ρ)
    (v.map (crecBits t.wg)) ((mapC (rotIPowC 2) v).map (crecBits t.wg)) with hsel
  have hmk : ∀ x : List (List Bool), Sym.mark ∉ arrSyms x := mark_not_mem_arrSyms'
  have hw : 1 ≤ t.wg := by simp [CCoreRT.wg]
  have s2 := safe_mvIn (Er := E2 ⊕ Em) (R2 × Rm) u S0 sc (carrSyms t.wg v) (hmk _) hu hT hX
  set S1 := Function.update S0 (roleL u) [Sym.mark] with hS1
  have hS1cl : ∀ e, S1 (.inr (.inr e)) = [] := fun e => by
    rw [hS1, Function.update_of_ne (by simp)]; exact hcl e
  -- the scratch program
  set sc1 := Function.update sc .X (carrSyms t.wg v ++ [Sym.mark])
  have ra := WP.W0m.runs_liftRegs (lO (R2 × Rm)) (runs_passC (src := wS (Er := E2 ⊕ Em) .X)
    (tmp := wS .Tm) (dst := wS .X2) (by simp) (by simp) (by simp) (carrSyms t.wg v) [] []
    (hmk _) (wst (S1 descL) sc1 (fun e => S1 (.inr (.inr e)))) (by simp [sc1])
    (by simp [sc1, hT]))
  rw [update_wst_S] at ra
  set sc1a := Function.update sc1 .X2 (carrSyms t.wg v ++ wst (S1 descL) sc1
    (fun e => S1 (.inr (.inr e))) (wS .X2))
  have rb := runs_rotCall (lRot R2 Rm) hspec2 (a := .X2) (b := .Xn) (c := .cW) (by decide)
    (by decide) (by decide) Sum.inl_injective (S1 descL) sc1a (fun e => S1 (.inr (.inr e)))
    t.wg v hw hf1 hf2 (by simp [sc1a, sc1, hX2]) (by simp [sc1a, sc1, hXn])
    (by simp [sc1a, sc1, hW])
  set sc1b := Function.update (Function.update sc1a .X2 [Sym.mark]) .Xn
    (carrSyms t.wg (mapC (rotIPowC 2) v) ++ [Sym.mark])
  have rc := runs_maskCall (lMs R2 Rm) hspecm Sum.inr_injective (S1 descL) sc1b
    (fun e => S1 (.inr (.inr e))) (fun e => hS1cl (.inr e)) t hk hρ hjD hS
    (v.map (crecBits t.wg)) ((mapC (rotIPowC 2) v).map (crecBits t.wg)) (by simp [mapC])
    (by simp [sc1b, sc1a, sc1, carrSyms]) (by simp [sc1b, carrSyms]) (by simp [sc1b, sc1a, sc1, hY])
    (by simp [sc1b, sc1a, sc1, hK]) (by simp [sc1b, sc1a, sc1, hD]) (by simp [sc1b, sc1a, sc1, hSc])
    (by simp [sc1b, sc1a, sc1, hJ]) (by simp [sc1b, sc1a, sc1, hKk]) (by simp [sc1b, sc1a, sc1, hR])
  set sc3 := Function.update (Function.update (Function.update sc1b .X [Sym.mark]) .Xn [Sym.mark]) .Y
    (arrSyms sel ++ [Sym.mark])
  have s3 := safe_callW (Rr := R2 × Rm)
    (P := coreM P2 Pm) ⟨WP.W9comp.closed_liftRegs _ (closed_passC _ _ _ _), closed_callInj _ _ h2,
      closed_callInj _ _ hm⟩ S1 sc1 sc3
    (WP.W9comp.runs_mono (WP.W9comp.runs_seq ra (WP.W9comp.runs_seq rb rc)) (fun _ _ => trivial)
      le_rfl)
  have s4 := safe_mvOut (Er := E2 ⊕ Em) (R2 × Rm) u S1 sc3 (arrSyms sel) (hmk _) (by simp [hS1])
    (by simp [sc3, sc1b, sc1a, sc1, hT]) (by simp [sc3])
  replace s4 := SafeRunsIn.congr s4 (S₂ := stv (Function.update S0 (roleL u)
    (arrSyms sel ++ [Sym.mark])) sc) (by
      rw [hS1, Function.update_idem]
      congr 1
      funext q
      by_cases hq1 : q = .X
      · subst hq1; simp [sc3, sc1b, sc1a, sc1, hX]
      · by_cases hq2 : q = .Xn
        · subst hq2; simp [sc3, hXn]
        · by_cases hq3 : q = .Y
          · subst hq3; simp [hY]
          · by_cases hq4 : q = .X2
            · subst hq4; simp [sc3, sc1b, hX2]
            · simp [sc3, sc1b, sc1a, sc1, Function.update_apply, hq1, hq2, hq3, hq4]) le_rfl
  refine SafeRunsIn.mono (SafeRunsIn.seq s2 (SafeRunsIn.seq s3 s4)) (fun _ _ => trivial) ?_
  have hv1 : vol (v.map (crecBits t.wg)) = cvol t.wg v := rfl
  have hv2 : vol ((mapC (rotIPowC 2) v).map (crecBits t.wg)) = cvol t.wg v := cvol_mapC t.wg _ v
  simp only [hv1, hv2, cvol]
  omega

end MaskMid

end SubNLogN.Machine.CCore.LeafScalarAux
