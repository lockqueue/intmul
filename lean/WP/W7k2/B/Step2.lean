import WP.W7k2.B.Step

/-!
# WP.W7k2.B.Step2 — the step part of a step level, correctness

* `VB_upd`: an update outside the value stacks commutes with `VB`; `LS_TR`, `LS_STG`, `LS_adv`:
  updates of the level state.
* `postPhase_spec`, `prePhase_spec`, `advance_spec`: the phases of `stepPart` on `VB (LS …)`.
* `stepPart_spec`: from the level state `LS S (Lc+1) p K pIn blk tr` of a step level, `stepPart`
  reaches the child's level state, with `postSegC p K` on `TR` and `preSegC pIn p K` staged
  (reversed) on `STG`, within `stepCostE C KM p K pIn (Lc+1)` (`B/StepCost.lean`).
-/

set_option linter.unusedSimpArgs false

namespace WP.W7k2

open TMFw TMFw.Contracts IntMul

/-- The stacks of the level values. -/
def vbSlots : List BL := [sK1, sK2, sPW, sPC, sPS, sT1, sR, sR2, sN1, sW, sNB, sH, sTPc, sPI, sLN]

theorem VB_upd (B : BL → List Sym) (p K : ℕ) (x : BL) (w : List Sym)
    (hx : inNamed vbSlots x = false) :
    Function.update (VB B p K) x w = VB (Function.update B x w) p K := by
  have hm : x ∉ vbSlots := fun hm => by
    rw [inNamed_iff.mpr hm] at hx
    exact absurd hx (by decide)
  have k1 : sK1 ≠ x := fun e => hm (by simp [vbSlots, e])
  have k2 : sK2 ≠ x := fun e => hm (by simp [vbSlots, e])
  have k3 : sPW ≠ x := fun e => hm (by simp [vbSlots, e])
  have k4 : sPC ≠ x := fun e => hm (by simp [vbSlots, e])
  have k5 : sPS ≠ x := fun e => hm (by simp [vbSlots, e])
  have k6 : sT1 ≠ x := fun e => hm (by simp [vbSlots, e])
  have k7 : sR ≠ x := fun e => hm (by simp [vbSlots, e])
  have k8 : sR2 ≠ x := fun e => hm (by simp [vbSlots, e])
  have k9 : sN1 ≠ x := fun e => hm (by simp [vbSlots, e])
  have k10 : sW ≠ x := fun e => hm (by simp [vbSlots, e])
  have k11 : sNB ≠ x := fun e => hm (by simp [vbSlots, e])
  have k12 : sH ≠ x := fun e => hm (by simp [vbSlots, e])
  have k13 : sTPc ≠ x := fun e => hm (by simp [vbSlots, e])
  have k14 : sPI ≠ x := fun e => hm (by simp [vbSlots, e])
  have k15 : sLN ≠ x := fun e => hm (by simp [vbSlots, e])
  simp only [VB, Function.update_comm k1, Function.update_comm k2, Function.update_comm k3,
    Function.update_comm k4, Function.update_comm k5, Function.update_comm k6,
    Function.update_comm k7, Function.update_comm k8, Function.update_comm k9,
    Function.update_comm k10, Function.update_comm k11, Function.update_comm k12,
    Function.update_comm k13, Function.update_comm k14, Function.update_comm k15,
    Function.update_of_ne k1, Function.update_of_ne k2, Function.update_of_ne k3,
    Function.update_of_ne k4, Function.update_of_ne k5, Function.update_of_ne k6,
    Function.update_of_ne k7, Function.update_of_ne k8, Function.update_of_ne k9,
    Function.update_of_ne k10, Function.update_of_ne k11, Function.update_of_ne k12,
    Function.update_of_ne k13, Function.update_of_ne k14, Function.update_of_ne k15]

theorem LS_TR (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr w : List Sym) :
    Function.update (LS S Lc p K pIn blk tr) sTR w = LS S Lc p K pIn blk w := by
  simp only [LS]
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]

theorem LS_STG (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr blk' : List Sym) :
    Function.update (LS S Lc p K pIn blk tr) sSTG (blk' ++ Sym.mark :: S sSTG) =
      LS S Lc p K pIn blk' tr := by
  simp only [LS, Function.update_idem]

theorem LS_adv (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr : List Sym) (p' K' pIn' : ℕ) :
    Function.update (Function.update (Function.update (Function.update
      (LS S (Lc + 1) p K pIn blk tr) vL (natSyms Lc ++ Sym.mark :: S vL))
      vpI (natSyms pIn' ++ Sym.mark :: S vpI)) vp (natSyms p' ++ Sym.mark :: S vp))
      vK (natSyms K' ++ Sym.mark :: S vK) = LS S Lc p' K' pIn' blk tr := by
  simp only [LS]
  simp (disch := first | decide | simp (config := { failIfUnchanged := false })
      (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne]) only [upd_swap,
      Function.update_idem, upd_eq_self_of, Function.update_self, Function.update_of_ne,
      List.append_assoc, List.cons_append, List.nil_append]

theorem VB_TR (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr w : List Sym) :
    Function.update (VB (LS S Lc p K pIn blk tr) p K) sTR (w ++ VB (LS S Lc p K pIn blk tr) p K sTR) =
      VB (LS S Lc p K pIn blk (w ++ tr)) p K := by
  rw [show VB (LS S Lc p K pIn blk tr) p K sTR = tr by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor], VB_upd _ p K sTR _ (by decide), LS_TR]

theorem VB_STG (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr w : List Sym) :
    Function.update (VB (LS S Lc p K pIn blk tr) p K) sSTG
        (w ++ VB (LS S Lc p K pIn blk tr) p K sSTG) =
      VB (LS S Lc p K pIn (w ++ blk) tr) p K := by
  rw [show VB (LS S Lc p K pIn blk tr) p K sSTG = blk ++ Sym.mark :: S sSTG by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor],
    VB_upd _ p K sSTG _ (by decide), ← List.append_assoc, LS_STG]

section Step2

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem advance_spec (hI : I.Spec Mul C) (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr : List Sym)
    (ρ : List (BP I)) :
    HT ρ (VB (LS S (Lc + 1) p K pIn blk tr) p K) (advance I)
      (VB (LS S Lc (pChild p K) (K - K / 2) (2 * pChild p K) blk tr) p K)
      (C * (bitLen (Lc + 1) + 1) + (C * (bitLen pIn + 1) + C * (bitLen (2 * pChild p K) + 1)) +
        (C * (bitLen p + 1) + C * (bitLen (pChild p K) + 1)) +
        (C * (bitLen K + 1) + C * (bitLen (K - K / 2) + 1))) := by
  refine (HT.seq ((HT.bdc hI vL _ Lc (Sym.mark :: S vL) (termOK_mark _) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]) ρ).of_eq
      (VB_upd _ p K vL _ (by decide)) le_rfl) <|
    HT.seq ((HT.bset hI sPS vpI (by decide) _ (2 * pChild p K) pIn (Sym.mark :: S sPS)
      (Sym.mark :: S vpI) (termOK_mark _) (termOK_mark _) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]) ρ).of_eq
      (VB_upd _ p K vpI _ (by decide)) le_rfl) <|
    HT.seq ((HT.bset hI sPC vp (by decide) _ (pChild p K) p (Sym.mark :: S sPC)
      (Sym.mark :: S vp) (termOK_mark _) (termOK_mark _) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]) ρ).of_eq
      (VB_upd _ p K vp _ (by decide)) le_rfl) <|
    (HT.bset hI sK2 vK (by decide) _ (K - K / 2) K (Sym.mark :: S sK2)
      (Sym.mark :: S vK) (termOK_mark _) (termOK_mark _) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]) ρ).of_eq
      (VB_upd _ p K vK _ (by decide)) le_rfl).of_eq (by rw [LS_adv]) (by omega)

theorem postPhase_spec (hI : I.Spec Mul C) (S : BL → List Sym) (Lc p K pIn : ℕ)
    (blk tr : List Sym) (Q : ℕ) (ρ : List (BP I)) (hQ : 128 * (pWork p K + 1) ≤ Q)
    (hdiv : ∀ u2 < 2 ^ (K - K / 2), 0 < IntMulTM.Contracts.W8.columnDivisor (2 ^ (K - K / 2)) u2
      (c0V (pWork p K) (2 * pChild p K) (2 ^ (K - K / 2)) u2)
      (c1V (pWork p K) (2 * pChild p K) (2 ^ (K - K / 2)) u2)) :
    HT ρ (VB (LS S Lc p K pIn blk tr) p K) (postSeg I)
      (VB (LS S Lc p K pIn blk (postSegC p K ++ tr)) p K)
      (2 ^ (K - K / 2) * (C * Q ^ 4 + C * (Q * Q) + 12 * (C * Q) + 11) + 2 * (C * Q) +
        fieldsCost C [p, 2 * pChild p K, 2 ^ (K / 2), 2 ^ (K - K / 2), K / 2, K - K / 2,
          pChild p K, 3 * (2 * pChild p K) + 2] + 4) := by
  have hw : pWork p K = p + K + 6 := rfl
  have hc : pChild p K = p + 2 * K + 12 := by unfold pChild pWork; omega
  have b2 : bitLen (2 ^ (K - K / 2)) = K - K / 2 + 1 := bitLen_two_pow _
  exact (postSeg_spec hI p (pWork p K) (2 * pChild p K) (pChild p K)
    (3 * (2 * pChild p K) + 2) (K / 2) (K - K / 2) Q (VB (LS S Lc p K pIn blk tr) p K)
    (by omega) ⟨Sym.mark :: S vp, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩
    ⟨Sym.mark :: S sPW, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩ ⟨Sym.mark :: S sPC, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩
    ⟨Sym.mark :: S sPS, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩ ⟨Sym.mark :: S sT1, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩
    ⟨Sym.mark :: S sR, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩ ⟨Sym.mark :: S sK1, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩
    ⟨Sym.mark :: S sK2, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩ ⟨Sym.mark :: S sH, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) hdiv
    (by omega) (by omega) (by omega) ρ).of_eq (VB_TR _ _ _ _ _ _ _ _) le_rfl

theorem prePhase_spec (hI : I.Spec Mul C) (S : BL → List Sym) (Lc p K pIn : ℕ)
    (blk tr : List Sym) (Q : ℕ) (ρ : List (BP I)) (hQ : 128 * (pWork p K + 1) ≤ Q) :
    HT ρ (VB (LS S Lc p K pIn blk tr) p K) (preSeg I)
      (VB (LS S Lc p K pIn ((preSegC pIn p K).reverse ++ blk) tr) p K)
      (2 * (2 ^ (K - K / 2) * (C * Q ^ 4 + 2 * (C * Q) + 1)) +
        2 ^ (K / 2) * ((2 * (2 * pChild p K) +
          effectiveFilterWidth (2 * pChild p K) (2 ^ (K - K / 2))) *
            (C * Q ^ 4 + 15 * (C * Q) + 6) +
          effectiveFilterWidth (2 * pChild p K) (2 ^ (K - K / 2)) * (9 * (C * Q) + 7) +
          4 * (C * Q) + 3) +
        6 * (C * Q) + fieldsCost C [p, 2 * pChild p K, 2 * pChild p K, 2 ^ (K / 2),
          2 ^ (K - K / 2), K / 2, K - K / 2, effectiveFilterWidth (2 * pChild p K) (2 ^ (K - K / 2)),
          kroneckerSpreadNumBlocks (2 * pChild p K) (2 ^ (K - K / 2)), pChild p K, pIn] +
        3 * (preSegC pIn p K).length + 11) := by
  have hw : pWork p K = p + K + 6 := rfl
  have hc : pChild p K = p + 2 * K + 12 := by unfold pChild pWork; omega
  have b1 : bitLen (2 ^ (K / 2)) = K / 2 + 1 := bitLen_two_pow _
  have b3 : bitLen (2 * 2 ^ (K - K / 2)) = K - K / 2 + 1 + 1 := by
    rw [← pow_succ']; exact bitLen_two_pow _
  have b4 : bitLen (2 * (2 * pChild p K) + 1) ≤ 2 * (2 * pChild p K) + 1 := bitLen_le_self _
  exact (preSeg_spec hI pIn p (pWork p K) (2 * pChild p K) (pChild p K) (K / 2) (K - K / 2) Q
    (VB (LS S Lc p K pIn blk tr) p K)
    ⟨⟨Sym.mark :: S sPW, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩, ⟨Sym.mark :: S sPS, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩,
      ⟨Sym.mark :: S sT1, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩, ⟨Sym.mark :: S sW, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩,
      ⟨Sym.mark :: S sN1, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩, ⟨Sym.mark :: S sPI, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩,
      ⟨Sym.mark :: S sLN, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩⟩
    ⟨Sym.mark :: S vp, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩ ⟨Sym.mark :: S vpI, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩
    ⟨Sym.mark :: S sPC, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩ ⟨Sym.mark :: S sR, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩
    ⟨Sym.mark :: S sR2, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩ ⟨Sym.mark :: S sK1, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩
    ⟨Sym.mark :: S sK2, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩ ⟨Sym.mark :: S sNB, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [VB, LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by omega) (by omega) (by omega) (by omega)
    (by omega) ρ).of_eq (VB_STG _ _ _ _ _ _ _ _) le_rfl

/-- **The step part of a step level.** -/
theorem stepPart_spec (hI : I.Spec Mul C) (KM : ℕ) (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (S : BL → List Sym) (Lc p K pIn : ℕ) (blk tr : List Sym) (ρ : List (BP I))
    (hdiv : ∀ u2 < 2 ^ (K - K / 2), 0 < IntMulTM.Contracts.W8.columnDivisor (2 ^ (K - K / 2)) u2
      (c0V (pWork p K) (2 * pChild p K) (2 ^ (K - K / 2)) u2)
      (c1V (pWork p K) (2 * pChild p K) (2 ^ (K - K / 2)) u2)) :
    HT ρ (LS S (Lc + 1) p K pIn blk tr) (stepPart I)
      (LS S Lc (pChild p K) (K - K / 2) (2 * pChild p K) ((preSegC pIn p K).reverse ++ blk)
        (postSegC p K ++ tr))
      (stepCostE C KM p K pIn (Lc + 1)) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 128 * (pWork p K + 1) := ⟨_, rfl⟩
  have e1 := cvAll_spec hI KM hMul p K Q (LS S (Lc + 1) p K pIn blk tr) ρ
    ⟨Sym.mark :: S vp, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩ ⟨Sym.mark :: S vK, termOK_mark _, by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor]⟩
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by omega)
  have e2 := postPhase_spec hI S (Lc + 1) p K pIn blk tr Q ρ (by omega) hdiv
  have e3 := prePhase_spec (C := C) hI S (Lc + 1) p K pIn blk (postSegC p K ++ tr) Q ρ (by omega)
  have e4 := advance_spec hI S Lc p K pIn ((preSegC pIn p K).reverse ++ blk) (postSegC p K ++ tr) ρ
  have e5 := dropVals_spec hI p K (LS S Lc (pChild p K) (K - K / 2) (2 * pChild p K)
    ((preSegC pIn p K).reverse ++ blk) (postSegC p K ++ tr)) ρ
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
    (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark]) (by simp (config := { failIfUnchanged := false }) (disch := decide) only [LS, FS,
      Function.update_self, Function.update_of_ne, Bf_floor, Bf_nofloor, termOK_mark])
  refine (HT.seq e1 (HT.seq e2 (HT.seq e3 (HT.seq e4 e5)))).mono ?_
  simp only [stepCostE, dropCost]
  rw [← hQ]
  omega

end Step2

#assert_std_axioms VB_upd LS_TR LS_STG LS_adv VB_TR VB_STG advance_spec postPhase_spec
  prePhase_spec stepPart_spec

end WP.W7k2
