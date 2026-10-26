/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.SolLoop
import SubNLogN.Machine.Tables.SetupStmt
import SubNLogN.Machine.Tables.Header

/-!
# K6 (`Machine/Tables/MainSpec.lean`): the table generator on the host

**Scope (honest summary).** The host program `mainProg` = setup; tap phase; `rAx := d-1`;
solver loop; cleanup, built from the programs provided by the contract statements `SetupStmt`
and `TapPhaseStmt` (explicit hypotheses), and its exact specification `HT.mainProg_spec`: from a
clean scratch with the header on `par`, push `tapTabSyms` onto `tapTab` and `solTabSyms` onto
`solTab` for `tabOf ω P t` (`SubNLogN/Machine/Contracts/Tables.lean:77`), all else restored, with
the sum of the phase costs.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt SubNLogN.Math.Common

theorem parSt_inl (B : TL → List Sym) (b : BrPar) (i : Fin 3) (v : List Sym) :
    parSt (Function.update B (.inl i) v) b = Function.update (parSt B b) (.inl i) v := by
  funext g
  by_cases hg : g = Sum.inl i
  · subst hg
    simp [parSt, Function.update_apply]
  · simp only [parSt, Function.update_apply, hg, if_false]

theorem solTabSyms_tabOf {d : ℕ} (wT ω P : ℕ) (t : Fin d → ℕ) :
    solTabSyms wT P t (tabOf ω P t) = (deconvOrder d).flatMap fun i =>
      carrSyms wT (solRecsN ω P (t i) (prefixProd t i)) ++ [Sym.mark] := by
  unfold solTabSyms
  congr 1
  funext i
  rw [solBlock_tabOf]

theorem hdr_getElem_eight (b : BrPar) (h : 8 < b.hdr.length) : b.hdr[8] = b.d := by
  simp [BrPar.hdr]

theorem hdr_length_gt (b : BrPar) : 8 < b.hdr.length := by
  simp [BrPar.hdr]

section Main

variable (I : TB)

/-- The table generator on the host. -/
def mainProg (setupP tapP cleanP : TP I) : TP I :=
  setupP.seq (tapP.seq ((tnat I x40 8).seq ((fetchProg I x40 x41 rAx).seq ((tdc I rAx).seq
    ((tcd I rAx (solAxisBody I)).seq cleanP)))))

theorem mainProg_closed {setupP tapP cleanP : TP I} (h1 : setupP.Closed) (h2 : tapP.Closed)
    (h3 : cleanP.Closed) : (mainProg I setupP tapP cleanP).Closed :=
  ⟨h1, h2, pushBits_closed _ _, fetchProg_closed I _ _ _, callI_closed _ _ _ _,
    tcd_closed I _ _ (solAxisBody_closed I), h3⟩

end Main

theorem tapScratch_ne {j : Fin 61} (hj : TapScratch (j : ℕ)) (k : Fin 61)
    (hk : ¬ TapScratch (k : ℕ)) : (Sum.inr j : TL) ≠ Sum.inr k := by
  intro h
  have : j = k := Sum.inr.inj h
  subst this
  exact hk hj

theorem parSt_inr_of_ge (B : TL → List Sym) (b : BrPar) (j : Fin 61) (hj : 40 ≤ (j : ℕ)) :
    parSt B b (.inr j) = B (.inr j) := by
  simp (disch := exact inr_ne_of_ge _ (by decide) hj) only [parSt, Function.update_of_ne]

theorem parSt_inr_scratch (B : TL → List Sym) (b : BrPar) (j : Fin 61) (hj : TapScratch (j : ℕ)) :
    parSt B b (.inr j) = B (.inr j) := by
  simp (disch := exact tapScratch_ne hj _ (by unfold TapScratch; decide)) only [parSt,
    Function.update_of_ne]

section MainSpec

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The table generator on the host**, from the phase specifications (the conclusions of
`SetupStmt` and `TapPhaseStmt` for the given programs). -/
theorem HT.mainProg_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    {setupP tapP cleanP : TP I} {costS costT : BrPar → ℕ}
    (hsS : ∀ (b : BrPar) (rpar : List Sym) (B : TL → List Sym), 2 ≤ b.d → ShapeOK b.t →
      B sPar = hdrSyms b.hdr ++ rpar → (∀ j : Fin 61, B (.inr j) = []) →
      HT [] B setupP (parSt B b) (costS b))
    (hcS : ∀ (b : BrPar) (B : TL → List Sym), 2 ≤ b.d → ShapeOK b.t →
      (∀ j : Fin 61, B (.inr j) = []) → HT [] (parSt B b) cleanP B (costS b))
    (htS : ∀ (b : BrPar) (rpar : List Sym) (B : TL → List Sym),
      2 ≤ b.d → ShapeOK b.t → 1 ≤ b.ω → 1 ≤ b.wT →
      (∀ i ∈ spreadOrder b.d, CArrFits b.wT (tapBlock b.t b.P (tabOf b.ω b.P b.t) i)) →
      B sPar = hdrSyms b.hdr ++ rpar →
      B rP = natSyms b.P → B rW = natSyms b.ω → B rB = natSyms (tapPrec b.P) →
      B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec b.P))).1 →
      B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec b.P))).1 →
      B rPW = intSyms ((2 ^ b.wT : ℕ) : ℤ) → B rPW1 = intSyms ((2 ^ (b.wT + 1) : ℕ) : ℤ) →
      B rSH = hdrSyms (lowerShape b.t 1) → B rA = natSyms (prefixProd b.t 1) →
      (∀ j : Fin 61, TapScratch j → B (.inr j) = []) →
      HT [] B tapP
        (Function.update (Function.update (Function.update B sTap
          (tapTabSyms b.wT b.P b.t (tabOf b.ω b.P b.t) ++ B sTap))
          rSH (hdrSyms (lowerShape b.t b.d))) rA (natSyms (prefixProd b.t b.d)))
        (costT b))
    (b : BrPar) (rpar : List Sym) (B : TL → List Sym)
    (hd : 2 ≤ b.d) (hS : ShapeOK b.t) (hω : 1 ≤ b.ω) (hw : 1 ≤ b.wT)
    (hfit : TablesFit b.wT b.P b.t (tabOf b.ω b.P b.t))
    (hpar : B sPar = hdrSyms b.hdr ++ rpar) (hcl : ∀ j : Fin 61, B (.inr j) = []) :
    HT [] B (mainProg I setupP tapP cleanP)
      (Function.update (Function.update B sTap
        (tapTabSyms b.wT b.P b.t (tabOf b.ω b.P b.t) ++ B sTap))
        sSol (solTabSyms b.wT b.P b.t (tabOf b.ω b.P b.t) ++ B sSol))
      (costS b + (costT b + (bitLen 8 + 1 + (fetchCost C (hdrSyms b.hdr).length +
        (C * (bitLen (b.d - 1 + 1) + 1) + (solLoopCost C KM b.wT b.t b.ω b.P + costS b)))))) := by
  have hd1 : b.d - 1 + 1 = b.d := by omega
  have hfitS : ∀ i ∈ deconvOrder b.d,
      CArrFits b.wT (solRecsN b.ω b.P (b.t i) (prefixProd b.t i)) := by
    intro i hi
    have := hfit.2 i hi
    rwa [solBlock_tabOf] at this
  have hpS : parSt B b sTap = B sTap := by
    simp (disch := decide) only [parSt, Function.update_of_ne]
  have hpSol : parSt B b sSol = B sSol := by
    simp (disch := decide) only [parSt, Function.update_of_ne]
  have h40 : B x40 = [] := hcl 40
  have h41 : B x41 = [] := hcl 41
  have h21 : B rAx = [] := hcl 21
  have hpar1 : parSt B b sPar = hdrSyms b.hdr ++ rpar := by
    simp (disch := decide) only [parSt, Function.update_of_ne, hpar]
  refine (HT.seq (hsS b rpar B hd hS hpar hcl)
    (HT.seq (htS b rpar (parSt B b) hd hS hω hw hfit.1 hpar1
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
      (fun j hj => by rw [parSt_inr_scratch B b j hj]; exact hcl j))
    (HT.seq (HT.tnat_spec x40 8 _ [])
    (HT.seq (HT.fetch_spec hI x40 x41 rAx (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ b.hdr 8 (hdr_length_gt b) [] rpar TermOK.nil
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne, parSt, h40])
      (by simp (disch := decide) only [Function.update_of_ne, hpar1])
      (by simp (disch := decide) only [Function.update_of_ne, parSt, h41]) [])
    (HT.seq ((HT.tdc_spec hI rAx _ (b.d - 1) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne,
          hdr_getElem_eight b (hdr_length_gt b), hd1, parSt, h21]) []).of_eq
      (by
        funext g
        by_cases g0 : g = rAx
        · subst g0; simp (disch := decide) only [solPhSt, Function.update_of_ne,
            Function.update_self]
        by_cases g1 : g = sSol
        · subst g1
          simp (disch := decide) only [solPhSt, Function.update_of_ne, Function.update_self]
          rw [List.drop_eq_nil_of_le (by rw [length_deconvOrder']), List.flatMap_nil,
            List.nil_append]
        by_cases g2 : g = rA
        · subst g2; simp (disch := decide) only [solPhSt, Function.update_of_ne,
            Function.update_self, hd1]
        by_cases g3 : g = rSH
        · subst g3; simp (disch := decide) only [solPhSt, Function.update_of_ne,
            Function.update_self, hd1]
        by_cases g4 : g = x40
        · subst g4; simp (disch := decide) only [solPhSt, Function.update_of_ne,
            Function.update_self, parSt, h40]
        simp only [solPhSt, Function.update_of_ne g0, Function.update_of_ne g1,
          Function.update_of_ne g2, Function.update_of_ne g3, Function.update_of_ne g4]) le_rfl :
      HT [] _ _ (solPhSt (Function.update (parSt B b) sTap
        (tapTabSyms b.wT b.P b.t (tabOf b.ω b.P b.t) ++ parSt B b sTap)) b.t b.ω b.P b.wT
        (b.d - 1)) _)
    (HT.seq ((HT.solLoop_spec hI hMul (Function.update (parSt B b) sTap
        (tapTabSyms b.wT b.P b.t (tabOf b.ω b.P b.t) ++ parSt B b sTap)) b.t b.ω b.P b.wT hS hω hw
        hfitS
        (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
        (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
        (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
        (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
        (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
        (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
        (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
        (by simp (disch := decide) only [parSt, Function.update_of_ne, Function.update_self])
        (by simp (disch := decide) only [parSt, Function.update_of_ne]; exact hcl 15)
        (by simp (disch := decide) only [parSt, Function.update_of_ne]; exact hcl 17)
        (by simp (disch := decide) only [parSt, Function.update_of_ne]; exact hcl 18)
        (by simp (disch := decide) only [parSt, Function.update_of_ne]; exact hcl 19)
        (by simp (disch := decide) only [parSt, Function.update_of_ne]; exact hcl 20)
        (by simp (disch := decide) only [parSt, Function.update_of_ne]; exact hcl 27)
        (fun j hj => by
          rw [Function.update_of_ne Sum.inr_ne_inl, parSt_inr_of_ge B b j hj]
          exact hcl j) []).of_eq
      (by
        rw [parSt_inl, parSt_inl]
        funext g
        by_cases g0 : g = rAx
        · subst g0
          simp (disch := decide) only [solPhSt, Function.update_of_ne, Function.update_self,
            parSt, h21, natSyms_zero', List.append_nil]
        by_cases g1 : g = sSol
        · subst g1
          simp (disch := decide) only [solPhSt, Function.update_of_ne, Function.update_self,
            List.drop_zero, hpSol]
          rw [solTabSyms_tabOf]
        by_cases g2 : g = sTap
        · subst g2
          simp (disch := decide) only [solPhSt, Function.update_of_ne, Function.update_self,
            hpS]
        by_cases g3 : g = rA
        · subst g3
          simp (disch := decide) only [solPhSt, parSt, Function.update_of_ne,
            Function.update_self, Nat.zero_add]
        by_cases g4 : g = rSH
        · subst g4
          simp (disch := decide) only [solPhSt, parSt, Function.update_of_ne,
            Function.update_self, Nat.zero_add]
        simp only [solPhSt, Function.update_of_ne g0, Function.update_of_ne g1,
          Function.update_of_ne g2, Function.update_of_ne g3, Function.update_of_ne g4]) le_rfl :
      HT [] _ _ (parSt (Function.update (Function.update B sTap
        (tapTabSyms b.wT b.P b.t (tabOf b.ω b.P b.t) ++ B sTap))
        sSol (solTabSyms b.wT b.P b.t (tabOf b.ω b.P b.t) ++ B sSol)) b) _)
      (hcS b _ hd hS (fun j => by
        rw [Function.update_of_ne Sum.inr_ne_inl, Function.update_of_ne Sum.inr_ne_inl]
        exact hcl j))))))))

end MainSpec

end SubNLogN.Machine.Tables
