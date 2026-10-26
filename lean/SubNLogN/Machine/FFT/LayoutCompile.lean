/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.Layout

/-!
# K4.3a (`Machine/FFT/LayoutCompile.lean`): the layout compiler from its two parts

**Scope (honest summary).** `layoutCompile_of_parts` proves `LayoutCompileStmt sel`
(`Machine/FFT/Layout.lean`) from two smaller contracts stated here:
* `PermHdrGenStmt`: from the middle header `midHdr q ℓ K w a` (restored) push the descriptor header
  `permHdr q (D+1) (2^ℓ) w K m₀` of Theorem 5.8;
* `LayoutMapGenStmt sel`: from the middle header push the runtime map
  `permSyms (layoutMap sel ℓ K a)` (Lemma 6.3, `lem:walsh-layout`; closed forms `layoutLList`, `layoutUList` of
  `Math/Walsh/IntForms/Address.lean`).
Both cost `C·((w + m₀ + 1)^J + |midHdr|)`. The two parts run one after the other on disjoint
private scratch (`callInj`). No `sorry`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Machine.FFTKit

/-- **[CONTRACT] K4.3b, the descriptor header of Theorem 5.8 from the middle header.**
Named stacks (`Fin 2`): `0` the header `midHdr q ℓ K w a` (restored), `1` receives
`permHdr q (D+1) (2^ℓ) w K m₀` on top of its previous content. Hypotheses: `MidShapeOK`.
Cost `C·((w + m₀ + 1)^J + |midHdr|)`. -/
def PermHdrGenStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest phrest : List Sym)
      (S : KLoc (Fin 2) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a →
      S (.inl 0) = midHdr q ℓ K w a ++ hrest → S (.inl 1) = phrest →
      Runs Pr S
        (Function.update S (.inl 1) (permHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) ++ phrest))
        (fun _ => True) (C * ((w + addrBits a + 1) ^ J + (midHdr q ℓ K w a).length))

/-- **[CONTRACT] K4.3c, the runtime map of `L` or `U` from the middle header** (Lemma 6.3,
`lem:walsh-layout`). Named stacks (`Fin 2`): `0` the header `midHdr q ℓ K w a` (restored), `1` receives
`permSyms (layoutMap sel ℓ K a) = hdrSyms [π 0, …, π (m₀-1)]` on top of its previous content.
Hypotheses: `MidShapeOK`. Cost `C·((w + m₀ + 1)^J + |midHdr|)`. -/
def LayoutMapGenStmt (sel : LayoutSel) : Prop :=
  ∃ J : ℕ, KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest prest : List Sym)
      (S : KLoc (Fin 2) E → List Sym),
      KClean S → MidShapeOK q ℓ K w a →
      S (.inl 0) = midHdr q ℓ K w a ++ hrest → S (.inl 1) = prest →
      Runs Pr S (Function.update S (.inl 1) (permSyms (layoutMap sel ℓ K a) ++ prest))
        (fun _ => True) (C * ((w + addrBits a + 1) ^ J + (midHdr q ℓ K w a).length))

namespace FFT.LayoutCompileAux

section Composite

variable {EH EM RH RM : Type}

/-- Embedding of the header part (header ↦ header, destination ↦ descriptor-header stack). -/
def hEmb : KLoc (Fin 2) EH → KLoc (Fin 3) (EH ⊕ EM)
  | .inl i => if (i : ℕ) = 0 then .inl 0 else .inl 1
  | .inr e => .inr (.inl e)

/-- Embedding of the map part (header ↦ header, destination ↦ map stack). -/
def mEmb : KLoc (Fin 2) EM → KLoc (Fin 3) (EH ⊕ EM)
  | .inl i => if (i : ℕ) = 0 then .inl 0 else .inl 2
  | .inr e => .inr (.inr e)

@[simp] theorem hEmb_0 : hEmb (EH := EH) (EM := EM) (.inl 0) = .inl 0 := by simp [hEmb]
@[simp] theorem hEmb_1 : hEmb (EH := EH) (EM := EM) (.inl 1) = .inl 1 := by simp [hEmb]
@[simp] theorem hEmb_inr (e : EH) : hEmb (EM := EM) (.inr e) = .inr (.inl e) := rfl
@[simp] theorem mEmb_0 : mEmb (EH := EH) (EM := EM) (.inl 0) = .inl 0 := by simp [mEmb]
@[simp] theorem mEmb_1 : mEmb (EH := EH) (EM := EM) (.inl 1) = .inl 2 := by simp [mEmb]
@[simp] theorem mEmb_inr (e : EM) : mEmb (EH := EH) (.inr e) = .inr (.inr e) := rfl

theorem hEmb_injective : Function.Injective (hEmb (EH := EH) (EM := EM)) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [hEmb]
  · fin_cases i <;> simp [hEmb] at h
  · fin_cases i' <;> simp [hEmb] at h
  · simp only [hEmb, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem mEmb_injective : Function.Injective (mEmb (EH := EH) (EM := EM)) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [mEmb]
  · fin_cases i <;> simp [mEmb] at h
  · fin_cases i' <;> simp [mEmb] at h
  · simp only [mEmb, Sum.inr.injEq] at h
    rw [h]

def lnsH : Lens (RH × RM) RH := Lens.fst _ _
def lnsM : Lens (RH × RM) RM := Lens.snd _ _

/-- The compiler: header part, then map part. -/
def compProg (PH : Prog (KLoc (Fin 2) EH) (fun _ => Sym) RH)
    (PM : Prog (KLoc (Fin 2) EM) (fun _ => Sym) RM) :
    Prog (KLoc (Fin 3) (EH ⊕ EM)) (fun _ => Sym) (RH × RM) :=
  .seq (callInj hEmb lnsH PH) (callInj mEmb lnsM PM)

theorem closed_compProg {PH : Prog (KLoc (Fin 2) EH) (fun _ => Sym) RH}
    {PM : Prog (KLoc (Fin 2) EM) (fun _ => Sym) RM} (hH : PH.Closed) (hM : PM.Closed) :
    (compProg PH PM).Closed :=
  WP.W9comp.closed_seq (closed_callInj _ _ hH) (closed_callInj _ _ hM)

end Composite

theorem compCost_bound {JH JM CH CM B H : ℕ} (hB : 1 ≤ B) :
    CH * (B ^ JH + H) + CM * (B ^ JM + H) ≤ (CH + CM) * (B ^ (JH + JM) + H) := by
  have h1 : B ^ JH ≤ B ^ (JH + JM) := Nat.pow_le_pow_right hB (by omega)
  have h2 : B ^ JM ≤ B ^ (JH + JM) := Nat.pow_le_pow_right hB (by omega)
  have e1 : CH * (B ^ JH + H) ≤ CH * (B ^ (JH + JM) + H) := Nat.mul_le_mul_left _ (by omega)
  have e2 : CM * (B ^ JM + H) ≤ CM * (B ^ (JH + JM) + H) := Nat.mul_le_mul_left _ (by omega)
  have e3 : (CH + CM) * (B ^ (JH + JM) + H) =
      CH * (B ^ (JH + JM) + H) + CM * (B ^ (JH + JM) + H) := by ring
  omega

end FFT.LayoutCompileAux

open FFT.LayoutCompileAux

/-- **The layout compiler from its parts**: the descriptor header (`PermHdrGenStmt`), then the
map (`LayoutMapGenStmt sel`). -/
theorem layoutCompile_of_parts (sel : LayoutSel) (hH : PermHdrGenStmt)
    (hM : LayoutMapGenStmt sel) : LayoutCompileStmt sel := by
  obtain ⟨JH, CH, hH⟩ := hH
  obtain ⟨JM, CM, hM⟩ := hM
  obtain ⟨EH, iFH, iDH, RH, PH, iRH, iNH, hcH, hsH⟩ := hH ()
  obtain ⟨EM, iFM, iDM, RM, PM, iRM, iNM, hcM, hsM⟩ := hM ()
  let iFH₁ : Fintype EH := iFH
  let iDH₁ : DecidableEq EH := iDH
  let iFM₁ : Fintype EM := iFM
  let iDM₁ : DecidableEq EM := iDM
  have iRH₁ : Finite RH := iRH
  have iNH₁ : Nonempty RH := iNH
  have iRM₁ : Finite RM := iRM
  have iNM₁ : Nonempty RM := iNM
  refine ⟨JH + JM, CH + CM, fun _ => ?_⟩
  refine ⟨EH ⊕ EM, inferInstance, inferInstance, RH × RM, compProg PH PM, inferInstance,
    inferInstance, closed_compProg hcH hcM, ?_⟩
  intro q ℓ K w D a hrest phrest prest S hcl hshape h0 h1 h2
  let hinst : DecidableEq (KLoc (Fin 3) (EH ⊕ EM)) := inferInstance
  have hcl' : ∀ e, S (.inr e) = [] := hcl
  obtain ⟨S1, hS1⟩ : ∃ S', S' = Function.update S (.inl 1)
      (permHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) ++ phrest) := ⟨_, rfl⟩
  have hr1 : Runs (callInj hEmb (@lnsH RH RM) PH) S S1 (fun _ => True)
      (CH * ((w + addrBits a + 1) ^ JH + (midHdr q ℓ K w a).length)) := by
    have hP := hsH q ℓ K w D a hrest phrest (S ∘ hEmb) (fun e => hcl' _) hshape
      (by simpa using h0) (by simpa using h1)
    have h := runs_callInj_update hEmb_injective (@lnsH RH RM) hP
    rw [hEmb_1] at h
    rw [hS1]
    exact h
  have hr2 : Runs (callInj mEmb (@lnsM RH RM) PM) S1
      (Function.update S1 (.inl 2) (permSyms (layoutMap sel ℓ K a) ++ prest)) (fun _ => True)
      (CM * ((w + addrBits a + 1) ^ JM + (midHdr q ℓ K w a).length)) := by
    have hP := hsM q ℓ K w D a hrest prest (S1 ∘ mEmb) (fun e => by simp [hS1, hcl'])
      hshape (by simp [hS1, h0]) (by simp [hS1, h2])
    have h := runs_callInj_update mEmb_injective (@lnsM RH RM) hP
    rw [mEmb_1] at h
    exact h
  have hall := WP.W9comp.runs_seq hr1 hr2
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial)
    (compCost_bound (by omega))
  rw [hS1]

end SubNLogN.Machine
