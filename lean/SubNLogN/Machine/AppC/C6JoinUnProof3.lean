/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6JoinUnProof2

/-!
# Lemma A.8 unjoin: the contract (`Machine/AppC/C6JoinUnProof3.lean`)

Part 3: `SubNLogN.Machine.c6Unjoin_holds (q) (hq : 2 ≤ q) : C6UnjoinStmt q`. The program is
`progUJ q P1` (`C6JoinUnProof2.lean`) with `P1` the proved K1 right-move kernel
(`K1Digit.k1MoveDigitMix_holds q true`): the setup `t = c6T q e`, `ℓ = e - t`, `N1 = G·q^ℓ`,
`N2 = B·q^ℓ` (`runs_setupUJ`), `t` right moves (`runs_loopUJ`), the cleanup (`runs_cleanJ`); the
composite address map is `c6UJInv` by `c6UJInv_eq_ujComp` (`C6JoinPure.lean`). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

namespace AppC.C6JoinUnAux

open AppC.C6JoinAux NatArith

/-- A uniform bound on the cost of `N2 := N2·q` during the loop. -/
def mqUJ (q e B : ℕ) : ℕ :=
  114 * (bitLen (q ^ e * B) + bitLen q + 2) ^ 2 + 9 * bitLen (q ^ e * B * q)

theorem mulConst_le_mq {q e l j B : ℕ} (hq : 1 ≤ q) (hle : l + j ≤ e) :
    mulConstCost (q ^ (l + j) * B) q ≤ mqUJ q e B := by
  have h1 : q ^ (l + j) * B ≤ q ^ e * B := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq hle)
  have h2 := bitLen_mono'' h1
  have h3 := bitLen_mono'' (Nat.mul_le_mul_right q h1)
  have h4 := mulConstCost_le (c := q) h2
  unfold mqUJ
  omega

/-! ## Cost bounds against the budget `Λ = q^(2e)·G·B` -/

theorem ujΛ_ge {q e G B : ℕ} (hG : 1 ≤ G) (hB : 1 ≤ B) :
    q ^ (2 * e) ≤ q ^ (2 * e) * G * B :=
  calc q ^ (2 * e) = q ^ (2 * e) * 1 * 1 := by ring
    _ ≤ q ^ (2 * e) * G * B := Nat.mul_le_mul (Nat.mul_le_mul_left _ hG) hB

theorem ujCostT_le {q e G B : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) (hte : c6T q e ≤ e) :
    costT q e ≤ (8 * tC q + 42) * (q ^ (2 * e) * G * B) := by
  have h1 := tCost_le hq e
  have h2 := cube_le_four_pow e
  have h3 := four_pow_le hq e
  have hΛ := ujΛ_ge (q := q) (e := e) hG hB
  have h4 := succ_le_budget (e := e) hq hG hB
  have h5 := bitLen_le_self' e
  have h6 := bitLen_le_self' (c6T q e)
  have h7 : tC q * (e + 1) ^ 3 ≤ 8 * tC q * (q ^ (2 * e) * G * B) := by
    calc tC q * (e + 1) ^ 3 ≤ tC q * (8 * 4 ^ e) := Nat.mul_le_mul_left _ h2
      _ ≤ tC q * (8 * q ^ (2 * e)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ ≤ tC q * (8 * (q ^ (2 * e) * G * B)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hΛ)
      _ = 8 * tC q * (q ^ (2 * e) * G * B) := by ring
  unfold costT
  linarith

theorem ujCostP_le {q e G B a n : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) (he : 1 ≤ e)
    (hn : n ≤ e) (hba : bitLen a ≤ bitLen G + bitLen B) (haΛ : a ≤ q ^ (2 * e) * G * B) :
    costP q a n ≤ (102400 * (2 * bitLen q + 4) ^ 2 + 15) * (q ^ (2 * e) * G * B) := by
  have hL1 : bitLen (a * q ^ n) ≤ bitLen a + (n * bitLen q + 1) :=
    (bitLen_mul_le' a (q ^ n)).trans (Nat.add_le_add_left (bitLen_pow_le' q n) _)
  have h2 : n * bitLen q ≤ e * bitLen q := Nat.mul_le_mul_right _ hn
  have h3 : bitLen q ≤ e * bitLen q := Nat.le_mul_of_pos_left _ (by omega)
  have hL : bitLen (a * q ^ n) + bitLen q + 2 ≤ 2 * e * bitLen q + bitLen G + bitLen B + 3 := by
    nlinarith
  have hm := master_le hq hG hB hn hL
  have h4 := bitLen_le_self' a
  have h5 := succ_le_budget (e := e) hq hG hB
  unfold costP powCost
  nlinarith

theorem ujMq_le {q e G B t : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) (he : 1 ≤ e)
    (ht : t ≤ e) : t * mqUJ q e B ≤ 62976 * (2 * bitLen q + 4) ^ 2 * (q ^ (2 * e) * G * B) := by
  have hL1 : bitLen (q ^ e * B) ≤ (e * bitLen q + 1) + bitLen B :=
    (bitLen_mul_le' (q ^ e) B).trans (Nat.add_le_add_right (bitLen_pow_le' q e) _)
  have h3 : bitLen q ≤ e * bitLen q := Nat.le_mul_of_pos_left _ (by omega)
  have hG0 := Nat.zero_le (bitLen G)
  have hL : bitLen (q ^ e * B) + bitLen q + 2 ≤ 2 * e * bitLen q + bitLen G + bitLen B + 3 := by
    nlinarith
  have hm := master_le hq hG hB ht hL
  have hq2 : bitLen (q ^ e * B * q) ≤ bitLen (q ^ e * B) + bitLen q := bitLen_mul_le' _ _
  have hsq : bitLen (q ^ e * B) + bitLen q + 2 ≤ (bitLen (q ^ e * B) + bitLen q + 2) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  have hb : bitLen (q ^ e * B * q) ≤ (bitLen (q ^ e * B) + bitLen q + 2) ^ 2 :=
    le_trans (by omega) hsq
  have h4 : t * mqUJ q e B ≤ (t + 1) * (123 * (bitLen (q ^ e * B) + bitLen q + 2) ^ 2) := by
    unfold mqUJ
    have h5 := Nat.mul_le_mul_left t hb
    have h6 := Nat.zero_le ((bitLen (q ^ e * B) + bitLen q + 2) ^ 2)
    nlinarith
  calc t * mqUJ q e B ≤ (t + 1) * (123 * (bitLen (q ^ e * B) + bitLen q + 2) ^ 2) := h4
    _ = 123 * ((t + 1) * (bitLen (q ^ e * B) + bitLen q + 2) ^ 2) := by ring
    _ ≤ 123 * (512 * (2 * bitLen q + 3 + 1) ^ 2 * (q ^ (2 * e) * G * B)) :=
        Nat.mul_le_mul_left _ hm
    _ = 62976 * (2 * bitLen q + 4) ^ 2 * (q ^ (2 * e) * G * B) := by ring

theorem ujClean_le {q e G B t l : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) (htl : t + l = e) :
    2 * bitLen (q ^ (l + t) * B) + 2 + (2 * bitLen (G * q ^ l) + 2 + (2 * bitLen l + 2 +
      (2 * bitLen t + 2))) ≤ 16 * (q ^ (2 * e) * G * B) := by
  have hΛ := ujΛ_ge (q := q) (e := e) hG hB
  have he2 : q ^ e ≤ q ^ (2 * e) := Nat.pow_le_pow_right (by omega) (by omega)
  have hl2 : q ^ l ≤ q ^ (2 * e) := Nat.pow_le_pow_right (by omega) (by omega)
  have hqe : 1 ≤ q ^ (2 * e) := Nat.one_le_pow _ _ (by omega)
  have a1 : q ^ (l + t) * B ≤ q ^ (2 * e) * G * B := by
    rw [show l + t = e by omega]
    calc q ^ e * B ≤ q ^ (2 * e) * B := Nat.mul_le_mul_right _ he2
      _ ≤ q ^ (2 * e) * G * B := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
  have a2 : G * q ^ l ≤ q ^ (2 * e) * G * B := by
    calc G * q ^ l ≤ G * q ^ (2 * e) := Nat.mul_le_mul_left _ hl2
      _ = q ^ (2 * e) * G * 1 := by ring
      _ ≤ q ^ (2 * e) * G * B := Nat.mul_le_mul_left _ hB
  have a3 := bitLen_le_self' (q ^ (l + t) * B)
  have a4 := bitLen_le_self' (G * q ^ l)
  have a5 := bitLen_le_self' l
  have a6 := bitLen_le_self' t
  have a7 : e ≤ q ^ (2 * e) * G * B := by
    have := succ_le_budget (e := e) hq hG hB
    omega
  omega

/-- The budget factor of the unjoin cost. -/
def ujK (q : ℕ) : ℕ :=
  (8 * tC q + 42) + 2 * (102400 * (2 * bitLen q + 4) ^ 2 + 15) + 62976 * (2 * bitLen q + 4) ^ 2 + 57

/-- The cost constant of the unjoin kernel (`C1`: the K1 kernel's constant). -/
def ujC (q C1 : ℕ) : ℕ := C1 + 13 + ujK q

theorem c6Unjoin_main (q : ℕ) (hq : 2 ≤ q) : C6UnjoinStmt q := by
  obtain ⟨C1, hK⟩ := K1Digit.k1MoveDigitMix_holds q true
  obtain ⟨E1, _, _, R1, P1, hR1a, hR1b, hP1, hs1⟩ := hK ()
  have hs1' : KerSpec q C1 P1 := fun N0 N1 N2 v rest r2 r3 S h1 h2 h3 h4 h5 h6 h7 =>
    hs1 N0 N1 N2 v rest r2 r3 S h1 h2 h3 h4 h5 h6 h7
  refine ⟨ujC q C1, fun _ => ⟨EJ E1, inferInstance, inferInstance, RJ R1, progUJ q P1,
    inferInstance, inferInstance, closed_progUJ q hP1, ?_⟩⟩
  intro A e G B w v rest r1 r2 r3 r4 S he hA hG hB hv hw hrest hr1 hr2 hr3 hr4 h0 h1 h2 h3 h4
  obtain ⟨ht1, hte⟩ := AppC.C6Aux.c6T_lt hq he
  have hsetup := runs_setupUJ (R1 := R1) hq e G B r1 r2 r3 S hr1 hr2 hr3 hte.le h1 h2 h3
  generalize ht : c6T q e = t at hsetup hte ht1 hv ⊢
  generalize hl : e - t = l at hsetup hv ⊢
  have htl : t + l = e := by omega
  have e0 : stA S t l (G * q ^ l) .N2 (B * q ^ l) = stUJ S q t l G B v rest 0 := by
    have hy0 : q ^ (l + 0) * B = B * q ^ l := by ring
    have hc0 : ujComp q l G B 0 = fun y => y := rfl
    simp only [stUJ, hy0, hc0, permByInv_id_uj]
    symm
    rw [Function.update_eq_self_iff]
    simp [stA, Function.update_apply, h0]
  have hM : ∀ j, j < t → C1 * (vol (permByInv (ujComp q l G B j) v) + 1) +
      6 * vol (permByInv (ujComp q l G B (j + 1)) v) + 7 + mulConstCost (q ^ (l + j) * B) q ≤
      C1 * (vol v + 1) + 6 * vol v + 7 + mqUJ q e B := fun j hj => by
    have a1 := AppC.C6BitMoveAux.vol_permByInv_le hw (ujComp q l G B j)
    have a2 := AppC.C6BitMoveAux.vol_permByInv_le hw (ujComp q l G B (j + 1))
    have a3 := mulConst_le_mq (q := q) (e := e) (l := l) (j := j) (B := B) (by omega) (by omega)
    have a4 := Nat.mul_le_mul_left C1 (Nat.add_le_add_right a1 1)
    omega
  have hloop := runs_loopUJ hs1' S A t l G B v rest hv hrest _ hM
  have hclean := runs_cleanJ (R1 := R1) (Y := .N2) (by decide) (by decide) (by decide) t l
    (G * q ^ l) (q ^ (l + t) * B) S (arrSyms (permByInv (ujComp q l G B t) v) ++ rest)
  have hall := WP.W9comp.runs_seq (WP.W9comp.runs_congr hsetup e0)
    (WP.W9comp.runs_seq hloop hclean)
  have hfin : permByInv (ujComp q l G B t) v = permByInv (c6UJInv (q ^ t) (q ^ l) G B) v := by
    refine AppC.C6Aux.permByInv_congr v (fun y hy => ?_)
    have := c6UJInv_eq_ujComp (q := q) (e := e) (t := t) (A := A) (G := G) (B := B) (y := y)
      (by omega) (by rw [hl, ← hv]; exact hy)
    rw [hl] at this
    exact this.symm
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall (by rw [hfin])) (fun _ h => h) ?_
  have hq1 : 1 ≤ q := by omega
  have he1 : 1 ≤ e := by omega
  have hte' : c6T q e ≤ e := by rw [ht]; exact hte.le
  have hqe : 1 ≤ q ^ (2 * e) := Nat.one_le_pow _ _ (by omega)
  have hGΛ : G ≤ q ^ (2 * e) * G * B :=
    calc G = 1 * G * 1 := by ring
      _ ≤ q ^ (2 * e) * G * B := Nat.mul_le_mul (Nat.mul_le_mul_right _ hqe) hB
  have hBΛ : B ≤ q ^ (2 * e) * G * B :=
    calc B = 1 * 1 * B := by ring
      _ ≤ q ^ (2 * e) * G * B := Nat.mul_le_mul (Nat.mul_le_mul hqe hG) le_rfl
  have hcT := ujCostT_le hq hG hB hte'
  have hcP1 := ujCostP_le (a := G) (n := l) hq hG hB he1 (by omega) (by omega) hGΛ
  have hcP2 := ujCostP_le (a := B) (n := l) hq hG hB he1 (by omega) (by omega) hBΛ
  have hmq := ujMq_le (t := t) hq hG hB he1 hte.le
  have hcl := ujClean_le (t := t) (l := l) hq hG hB htl
  have hΛ1 := succ_le_budget (e := e) hq hG hB
  have hover : 16 * t + 13 * bitLen t + 12 ≤ 41 * (q ^ (2 * e) * G * B) := by
    have := bitLen_le_self' t
    omega
  have hlenΛ : v.length = A * (q ^ (2 * e) * G * B) := by rw [hv, ← htl]; ring
  have hvol : vol v = v.length * (w + 1) := AppC.C6Aux.vol_eq_of_width hw
  have hΛV : q ^ (2 * e) * G * B ≤ vol v := by
    rw [hvol, hlenΛ]
    calc q ^ (2 * e) * G * B ≤ A * (q ^ (2 * e) * G * B) := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ A * (q ^ (2 * e) * G * B) * (w + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have htV : t ≤ vol v := by omega
  have hV1 : 1 ≤ vol v := by omega
  have hC1 : C1 * t ≤ C1 * vol v := Nat.mul_le_mul_left _ htV
  have htVt : t ≤ vol v * t := Nat.le_mul_of_pos_left _ hV1
  have hP1 := Nat.mul_le_mul_left (8 * tC q + 42) hΛV
  have hP2 := Nat.mul_le_mul_left (102400 * (2 * bitLen q + 4) ^ 2 + 15) hΛV
  have hP3 := Nat.mul_le_mul_left (62976 * (2 * bitLen q + 4) ^ 2) hΛV
  have key : ∀ X : ℕ, X ≤ (C1 + 13) * (vol v * (t + 1)) + ujK q * vol v →
      X ≤ ujC q C1 * (vol v * (t + 1) + 1) := fun X hX => by
    have k1 : vol v ≤ vol v * (t + 1) + 1 := by nlinarith
    have k2 := Nat.mul_le_mul_left (ujK q) k1
    have k3 : (C1 + 13) * (vol v * (t + 1)) ≤ (C1 + 13) * (vol v * (t + 1) + 1) :=
      Nat.mul_le_mul_left _ (Nat.le_succ _)
    calc X ≤ (C1 + 13) * (vol v * (t + 1)) + ujK q * vol v := hX
      _ ≤ (C1 + 13) * (vol v * (t + 1) + 1) + ujK q * (vol v * (t + 1) + 1) :=
          Nat.add_le_add k3 k2
      _ = ujC q C1 * (vol v * (t + 1) + 1) := by unfold ujC; ring
  apply key
  unfold ujK
  linarith

end AppC.C6JoinUnAux

/-- **`C6UnjoinStmt q` holds for every `q ≥ 2`** (`Machine/AppC/C6QLeaves.lean`). -/
theorem c6Unjoin_holds (q : ℕ) (hq : 2 ≤ q) : C6UnjoinStmt q :=
  AppC.C6JoinUnAux.c6Unjoin_main q hq

end SubNLogN.Machine
