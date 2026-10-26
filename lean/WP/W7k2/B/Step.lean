import WP.W7k2.B.Post
import WP.W7k2.B.LState
import WP.W7k2.B.StepCost

/-!
# WP.W7k2.B.Step — the step part of a step level, blocks

* `VB B p K`: the fifteen level values of the step level `(p, K)` pushed on their stacks above `B`
  (`sK1 … sLN`, in the order `cvA`, `cvB`, `cvC`, `cvD` push them).
* `cvAll = cvA; cvB; cvC; cvD`: `B → VB B p K` (`cvAll_spec`).
* `dropVals`: `VB B p K → B` (`dropVals_spec`).
* `advance`: the level registers move to the child level (`bdc vL`, `vpI := pSub`, `vp := pChild`,
  `vK := K − K/2`).
* `stepPart = cvAll; postSeg; preSeg; advance; dropVals` (correctness in `B/Step2.lean`).
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-- The fifteen level values of the step level `(p, K)`, pushed on their stacks above `B`. -/
def VB (B : BL → List Sym) (p K : ℕ) : BL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update B
    sK1 (natSyms (K / 2) ++ B sK1))
    sK2 (natSyms (K - K / 2) ++ B sK2))
    sPW (natSyms (pWork p K) ++ B sPW))
    sPC (natSyms (pChild p K) ++ B sPC))
    sPS (natSyms (2 * pChild p K) ++ B sPS))
    sT1 (natSyms (2 ^ (K / 2)) ++ B sT1))
    sR (natSyms (2 ^ (K - K / 2)) ++ B sR))
    sR2 (natSyms (2 * 2 ^ (K - K / 2)) ++ B sR2))
    sN1 (natSyms (2 * (2 * pChild p K) + 1) ++ B sN1))
    sW (natSyms (effectiveFilterWidth (2 * pChild p K) (2 ^ (K - K / 2))) ++ B sW))
    sNB (natSyms (kroneckerSpreadNumBlocks (2 * pChild p K) (2 ^ (K - K / 2))) ++ B sNB))
    sH (natSyms (3 * (2 * pChild p K) + 2) ++ B sH))
    sTPc (natSyms (W7.tapPrec (2 * pChild p K)) ++ B sTPc))
    sPI (intSyms (computablePiScaledWithCost (W7.tapPrec (2 * pChild p K))).1 ++ B sPI))
    sLN (intSyms (computableLog2ScaledWithCost (W7.tapPrec (2 * pChild p K))).1 ++ B sLN)

/-- All level values. -/
def cvAll (I : BI) : BP I := (cvA I).seq <| (cvB I).seq <| (cvC I).seq (cvD I)

/-- Move the level registers to the child level. -/
def advance (I : BI) : BP I :=
  (bdc I vL).seq <| (bset I sPS vpI).seq <| (bset I sPC vp).seq (bset I sK2 vK)

/-- Drop the level values (last pushed first). -/
def dropVals (I : BI) : BP I :=
  (bdrI I sLN).seq <| (bdrI I sPI).seq <| (bdr I sTPc).seq <| (bdr I sH).seq <| (bdr I sNB).seq <|
  (bdr I sW).seq <| (bdr I sN1).seq <| (bdr I sR2).seq <| (bdr I sR).seq <| (bdr I sT1).seq <|
  (bdr I sPS).seq <| (bdr I sPC).seq <| (bdr I sPW).seq <| (bdr I sK2).seq (bdr I sK1)

/-- The step part of a step level: values, post segment onto `TR`, pre segment staged on `STG`,
registers to the child level, drop the values. -/
def stepPart (I : BI) : BP I :=
  (cvAll I).seq <| (postSeg I).seq <| (preSeg I).seq <| (advance I).seq (dropVals I)

theorem cvAll_closed (I : BI) : (cvAll I).Closed :=
  ⟨cvA_closed I, cvB_closed I, cvC_closed I, cvD_closed I⟩

theorem advance_closed (I : BI) : (advance I).Closed :=
  ⟨callI_closed _ _ _ _, bset_closed _ _ _, bset_closed _ _ _, bset_closed _ _ _⟩

theorem dropVals_closed (I : BI) : (dropVals I).Closed :=
  ⟨bdrI_closed _ _, bdrI_closed _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

/-- Popping the top update of a chain whose lower part already holds the value. -/
theorem upd_upd_self {f : BL → List Sym} {x : BL} {v w : List Sym} (h : f x = w) :
    Function.update (Function.update f x v) x w = f := by
  rw [Function.update_idem, ← h, Function.update_eq_self]

theorem stepPart_closed (I : BI) : (stepPart I).Closed :=
  ⟨cvAll_closed I, postSeg_closed I, preSeg_closed I, advance_closed I, dropVals_closed I⟩

section Step

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem cvAll_spec (hI : I.Spec Mul C) (KM : ℕ) (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (p K Q : ℕ) (B : BL → List Sym) (ρ : List (BP I)) (hvp : NatAt B vp p) (hvK : NatAt B vK K)
    (hK1 : TermOK (B sK1)) (hK2 : TermOK (B sK2)) (hPW : TermOK (B sPW)) (hPC : TermOK (B sPC))
    (hPS : TermOK (B sPS)) (hT1 : TermOK (B sT1)) (hR : TermOK (B sR)) (hR2 : TermOK (B sR2))
    (hN1 : TermOK (B sN1)) (hW : TermOK (B sW)) (hNB : TermOK (B sNB)) (hH : TermOK (B sH))
    (hTP : TermOK (B sTPc)) (h0 : TermOK (B y0)) (h1 : TermOK (B y1)) (h2 : TermOK (B y2))
    (h3 : TermOK (B y3)) (hQ : 128 * (pWork p K + 1) ≤ Q) :
    HT ρ B (cvAll I) (VB B p K)
      (5 * (C * Q) + (12 * (C * Q) + 8) + (C * (Q * Q) + 20 * (C * Q) + 6) +
        (2 * (C * Q ^ 4) + 2 * (C * (KM * Q ^ 2)) + 30 * (C * Q) + 100)) := by
  obtain ⟨rp, hrp, ep⟩ := hvp
  obtain ⟨rK, hrK, eK⟩ := hvK
  have hw : pWork p K = p + K + 6 := rfl
  have hc : pChild p K = p + 2 * K + 12 := by unfold pChild pWork; omega
  refine (HT.seq (cvA_spec hI K Q B ρ ⟨rK, hrK, eK⟩ hK1 hK2 (by omega)) <|
    HT.seq (cvB_spec hI p K Q _ ρ ⟨rp, hrp, by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, ep]⟩ ⟨rK, hrK, by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, eK]⟩ (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h0])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h1]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hPW]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hPC]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hPS]) (by omega)) <|
    HT.seq (cvC_spec hI (K / 2) (K - K / 2) (2 * pChild p K) Q _ ρ ⟨B sK1, hK1, by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]⟩
      ⟨B sK2, hK2, by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]⟩ ⟨B sPS, hPS, by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]⟩ (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hT1]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hR]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hR2])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hN1]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hW]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hNB]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h0]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h1]) (by omega)) <|
    cvD_spec hI (2 * pChild p K) Q KM hMul _ ρ ⟨B sPS, hPS, by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]⟩ (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h0])
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h1]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h2]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, h3]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hH]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne, hTP])
      (by omega)).of_eq ?_ (by omega)
  simp only [VB]
  simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]

/-- Cost of `dropVals` (the last summand of `stepCostE`). -/
def dropCost (C p K : ℕ) : ℕ :=
  C * (bitLen (K / 2) + 1) + C * (bitLen (K - K / 2) + 1) + C * (bitLen (pWork p K) + 1) +
    C * (bitLen (pChild p K) + 1) + C * (bitLen (2 * pChild p K) + 1) +
    C * (bitLen (2 ^ (K / 2)) + 1) + C * (bitLen (2 ^ (K - K / 2)) + 1) +
    C * (bitLen (2 * 2 ^ (K - K / 2)) + 1) + C * (bitLen (2 * (2 * pChild p K) + 1) + 1) +
    C * (bitLen (effectiveFilterWidth (2 * pChild p K) (2 ^ (K - K / 2))) + 1) +
    C * (bitLen (kroneckerSpreadNumBlocks (2 * pChild p K) (2 ^ (K - K / 2))) + 1) +
    C * (bitLen (3 * (2 * pChild p K) + 2) + 1) + C * (bitLen (W7.tapPrec (2 * pChild p K)) + 1) +
    (1 + C * (bitLen (computablePiScaledWithCost (W7.tapPrec (2 * pChild p K))).1.natAbs + 1)) +
    (1 + C * (bitLen (computableLog2ScaledWithCost (W7.tapPrec (2 * pChild p K))).1.natAbs + 1))

theorem dropVals_spec (hI : I.Spec Mul C) (p K : ℕ) (B : BL → List Sym) (ρ : List (BP I))
    (hK1 : TermOK (B sK1)) (hK2 : TermOK (B sK2)) (hPW : TermOK (B sPW)) (hPC : TermOK (B sPC))
    (hPS : TermOK (B sPS)) (hT1 : TermOK (B sT1)) (hR : TermOK (B sR)) (hR2 : TermOK (B sR2))
    (hN1 : TermOK (B sN1)) (hW : TermOK (B sW)) (hNB : TermOK (B sNB)) (hH : TermOK (B sH))
    (hTP : TermOK (B sTPc)) (hPI : TermOK (B sPI)) (hLN : TermOK (B sLN)) :
    HT ρ (VB B p K) (dropVals I) B (dropCost C p K) := by
  refine (HT.seq ((HT.bdrI hI sLN _ (computableLog2ScaledWithCost (W7.tapPrec (2 * pChild p K))).1
      (B sLN) hLN (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]) ρ).of_eq (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdrI hI sPI _ (computablePiScaledWithCost (W7.tapPrec (2 * pChild p K))).1
      (B sPI) hPI (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdr hI sTPc _ (W7.tapPrec (2 * pChild p K)) (B sTPc) hTP (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq
      (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdr hI sH _ (3 * (2 * pChild p K) + 2) (B sH) hH (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq
      (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdr hI sNB _ (kroneckerSpreadNumBlocks (2 * pChild p K) (2 ^ (K - K / 2))) (B sNB)
      hNB (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdr hI sW _ (effectiveFilterWidth (2 * pChild p K) (2 ^ (K - K / 2))) (B sW) hW
      (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdr hI sN1 _ (2 * (2 * pChild p K) + 1) (B sN1) hN1 (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq
      (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdr hI sR2 _ (2 * 2 ^ (K - K / 2)) (B sR2) hR2 (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq
      (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdr hI sR _ (2 ^ (K - K / 2)) (B sR) hR (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq
      (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdr hI sT1 _ (2 ^ (K / 2)) (B sT1) hT1 (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq
      (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdr hI sPS _ (2 * pChild p K) (B sPS) hPS (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq
      (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdr hI sPC _ (pChild p K) (B sPC) hPC (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq
      (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdr hI sPW _ (pWork p K) (B sPW) hPW (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq
      (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    HT.seq ((HT.bdr hI sK2 _ (K - K / 2) (B sK2) hK2 (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq
      (upd_upd_self (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne])) le_rfl) <|
    (HT.bdr hI sK1 _ (K / 2) (B sK1) hK1 (by simp (config := { failIfUnchanged := false }) (disch := decide) only [Function.update_self,
      Function.update_of_ne]) ρ).of_eq (upd_upd_self rfl) le_rfl).mono
    (by unfold dropCost; omega)

end Step

#assert_std_axioms cvAll_closed advance_closed dropVals_closed upd_upd_self stepPart_closed
  cvAll_spec dropVals_spec

end WP.W7k2
