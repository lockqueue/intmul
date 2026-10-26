/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6RowCost
import SubNLogN.Machine.AppC.C6TArith
import SubNLogN.Machine.AppC.C6PiecesMath

/-!
# Lemma A.8 row padding: the cost bound of the counter kernel (`Machine/AppC/C6RowCtrCostProof.lean`)

Proves `ctrCost_holds (hq : 2 ≤ q) (CT CW CD) : CtrCostStmt q CT CW CD` (statement in
`C6RowCost.lean`). With `N = R·Z` (`R = c6R q e`, `Z = c6Zq q e G B`): every value inside
`ctrCost` is `≤ 2N` (`W ≤ R`, `R' < 2R`, `Z ≤ N`), so all bit lengths are `≤ E = bitLen N + 2`;
`N ≥ q^e ≥ 2^e` gives `e + 1 ≤ E`. Hence every term is `≤ c·E³` (`powCost` via
`C6JoinAux.powCost_le`, `mulCost ≤ 800·E³`), and `E³ ≤ 48·N` (`x³ ≤ 6·2^x`, `2^{bitLen N} ≤ 2N`). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Proved (no `sorry`).** Constant `48 · cc9_K q CT CW CD`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

namespace AppC.C6RowAux

open NatArith

/-! ## Arithmetic helpers -/

theorem cc9_bls (n : ℕ) : bitLen n ≤ n := NatArith.bitLen_le_of_lt' Nat.lt_two_pow_self

theorem cc9_bl {x N : ℕ} (hx : x ≤ 2 * N) : bitLen x ≤ bitLen N + 1 :=
  NatArith.bitLen_le_of_lt' (by
    have h := NatArith.lt_two_pow_bitLen N
    rw [pow_succ]
    omega)

theorem cc9_E3_le {N : ℕ} (hN : 1 ≤ N) : (bitLen N + 2) ^ 3 ≤ 48 * N := by
  have h1 := C6Aux.cube_le_pow (bitLen N + 2)
  have h2 := C6Aux.two_pow_bitLen_le hN
  have h3 : 2 ^ (bitLen N + 2) = 4 * 2 ^ bitLen N := by rw [pow_add]; ring
  omega

theorem cc9_mulCost_le {a b E : ℕ} (ha : bitLen a ≤ E) (hb : bitLen b ≤ E) (hE : 1 ≤ E) :
    mulCost a b ≤ 800 * E ^ 3 := by
  unfold mulCost
  have h1 : bitLen a + 1 ≤ 2 * E := by omega
  have h2 : bitLen a + bitLen b + 2 ≤ 4 * E := by omega
  have h3 : (bitLen a + 1) * (bitLen a + bitLen b + 2) ≤ (2 * E) * (4 * E) := Nat.mul_le_mul h1 h2
  have h4 : E ^ 2 ≤ E ^ 3 := Nat.pow_le_pow_right hE (by norm_num)
  have h5 : (2 * E) * (4 * E) = 8 * E ^ 2 := by ring
  have h6 : 100 * (bitLen a + 1) * (bitLen a + bitLen b + 2) =
      100 * ((bitLen a + 1) * (bitLen a + bitLen b + 2)) := by ring
  rw [h6]
  omega

/-! ## The cost in abstract variables -/

/-- `ctrCost` with `t = c6T q e`, `R = q^{2t}`, `W = W_b^k` abstracted. -/
def cc9_cost (q CT CW CD e t R W G B : ℕ) : ℕ :=
  (1 + (CT * (e + 1) ^ 3 + (1 + CW * (e + 1) ^ 3))) +
  ((1 + ((bitLen 1 + 1) + powCost (q ^ 2) 1 t)) +
  (costRp CD R W +
  (costZ q e t G B +
  (costK R (G * q ^ (e - t) * q ^ (e - t) * B) (W * ((R + W - 1) / W)) +
    costDrop (G * q ^ (e - t) * q ^ (e - t) * B) (W * ((R + W - 1) / W)) R W t))))

theorem cc9_cost_eq (q CT CW CD e G B : ℕ) :
    ctrCost q CT CW CD e G B =
      cc9_cost q CT CW CD e (c6T q e) (q ^ (2 * c6T q e)) (tripleWb 100 ^ c6K e) G B := rfl

/-- The `E³` coefficient. -/
def cc9_K (q CT CW CD : ℕ) : ℕ :=
  CT + CW + 4 * CD + 200 * (bitLen (q ^ 2) + 3) ^ 2 + 400 * (bitLen q + 3) ^ 2 + 5000

theorem cc9_cost_le {q CT CW CD e t R W G B E : ℕ} (hE1 : 1 ≤ E) (he : e + 1 ≤ E) (ht : t ≤ e)
    (hRq : bitLen ((q ^ 2) ^ t) ≤ E) (hR : bitLen R ≤ E) (hW : bitLen W ≤ E)
    (hRW : bitLen (R + W) ≤ E) (hRW1 : bitLen (R + W - 1) ≤ E)
    (hQ : bitLen ((R + W - 1) / W) ≤ E) (hrem : bitLen ((R + W - 1) % W) ≤ E)
    (hRp : bitLen (W * ((R + W - 1) / W)) ≤ E) (hRpR : bitLen (W * ((R + W - 1) / W) - R) ≤ E)
    (hZ : bitLen (G * q ^ (e - t) * q ^ (e - t) * B) ≤ E) (hG : bitLen G ≤ E) (hB : bitLen B ≤ E)
    (hGl : bitLen (G * q ^ (e - t)) ≤ E) (hGll : bitLen (G * q ^ (e - t) * q ^ (e - t)) ≤ E) :
    cc9_cost q CT CW CD e t R W G B ≤ cc9_K q CT CW CD * E ^ 3 := by
  have hE3 : E ≤ E ^ 3 := by
    calc E = E ^ 1 := (pow_one E).symm
      _ ≤ E ^ 3 := Nat.pow_le_pow_right hE1 (by norm_num)
  have hE2 : E * E ≤ E ^ 3 := by
    calc E * E = E ^ 2 := (sq E).symm
      _ ≤ E ^ 3 := Nat.pow_le_pow_right hE1 (by norm_num)
  have h1E : 1 ≤ E ^ 3 := Nat.one_le_pow _ _ hE1
  have hb1 : bitLen 1 ≤ 1 := cc9_bls 1
  have hbe : bitLen e ≤ E := (cc9_bls e).trans (by omega)
  have hbt : bitLen t ≤ E := (cc9_bls t).trans (by omega)
  have hbl : bitLen (e - t) ≤ E := (cc9_bls _).trans (by omega)
  have hq2E : bitLen (q ^ 2) ≤ bitLen (q ^ 2) * E := Nat.le_mul_of_pos_right _ (by omega)
  have hqE : bitLen q ≤ bitLen q * E := Nat.le_mul_of_pos_right _ (by omega)
  have hp1 : powCost (q ^ 2) 1 t ≤ 200 * ((bitLen (q ^ 2) + 3) ^ 2 * E ^ 3) + E ^ 3 :=
    (C6JoinAux.powCost_le (c := q ^ 2) (a := 1) (n := t) (E := E) (α := 1)
      (β := bitLen (q ^ 2) + 3) hE1 (by omega) (by rw [one_mul, add_mul]; omega)).trans
      (le_of_eq (by ring))
  have hp2 : powCost q G (e - t) ≤ 200 * ((bitLen q + 3) ^ 2 * E ^ 3) + E ^ 3 :=
    (C6JoinAux.powCost_le (c := q) (a := G) (n := e - t) (E := E) (α := 1)
      (β := bitLen q + 3) hE1 (by omega) (by rw [add_mul]; omega)).trans (le_of_eq (by ring))
  have hp3 : powCost q (G * q ^ (e - t)) (e - t) ≤ 200 * ((bitLen q + 3) ^ 2 * E ^ 3) + E ^ 3 :=
    (C6JoinAux.powCost_le (c := q) (a := G * q ^ (e - t)) (n := e - t) (E := E) (α := 1)
      (β := bitLen q + 3) hE1 (by omega) (by rw [add_mul]; omega)).trans (le_of_eq (by ring))
  have hm1 := cc9_mulCost_le hW hQ hE1
  have hm2 := cc9_mulCost_le hGll hB hE1
  have hm3 := cc9_mulCost_le hR hZ hE1
  have hm4 := cc9_mulCost_le hRpR hZ hE1
  have hcd : CD * (bitLen (R + W - 1) * bitLen W + bitLen (R + W - 1) + bitLen W + 1) ≤
      4 * (CD * E ^ 3) := by
    have h1 : bitLen (R + W - 1) * bitLen W ≤ E * E := Nat.mul_le_mul hRW1 hW
    have h2 : bitLen (R + W - 1) * bitLen W + bitLen (R + W - 1) + bitLen W + 1 ≤ 4 * E ^ 3 := by
      omega
    calc CD * (bitLen (R + W - 1) * bitLen W + bitLen (R + W - 1) + bitLen W + 1)
        ≤ CD * (4 * E ^ 3) := Nat.mul_le_mul_left _ h2
      _ = 4 * (CD * E ^ 3) := by ring
  have hct : CT * (e + 1) ^ 3 ≤ CT * E ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he 3)
  have hcw : CW * (e + 1) ^ 3 ≤ CW * E ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he 3)
  have hK : cc9_K q CT CW CD * E ^ 3 = CT * E ^ 3 + CW * E ^ 3 + 4 * (CD * E ^ 3) +
      200 * ((bitLen (q ^ 2) + 3) ^ 2 * E ^ 3) + 400 * ((bitLen q + 3) ^ 2 * E ^ 3) +
      5000 * E ^ 3 := by
    unfold cc9_K; ring
  unfold cc9_cost costRp costA costC costZ costK costDrop
  rw [hK]
  omega

/-! ## The bound -/

/-- **The cost bound of the counter kernel** (`2 ≤ q`), constant `48 · cc9_K q CT CW CD`. -/
theorem ctrCost_holds {q : ℕ} (hq : 2 ≤ q) (CT CW CD : ℕ) : CtrCostStmt q CT CW CD := by
  refine ⟨48 * cc9_K q CT CW CD, fun e G B he hG hB => ?_⟩
  have hT := C6Aux.c6T_lt hq he
  have hZ1 : 1 ≤ c6Zq q e G B := one_le_c6Zq hq hG hB
  have hR1 : 1 ≤ q ^ (2 * c6T q e) := Nat.one_le_pow _ _ (by omega)
  have hl1 : 1 ≤ q ^ (e - c6T q e) := Nat.one_le_pow _ _ (by omega)
  have hW1 : 1 ≤ tripleWb 100 ^ c6K e := Nat.one_le_pow _ _ (by decide)
  have hWR : tripleWb 100 ^ c6K e ≤ q ^ (2 * c6T q e) := C6Aux.c6Wk_le_c6R hq
  have hRp : tripleWb 100 ^ c6K e * ((q ^ (2 * c6T q e) + tripleWb 100 ^ c6K e - 1) /
      tripleWb 100 ^ c6K e) < 2 * q ^ (2 * c6T q e) := C6Aux.c6Rp_lt hq
  have hZv : G * q ^ (e - c6T q e) * q ^ (e - c6T q e) * B = c6Zq q e G B := by
    unfold c6Zq; ring
  have hGl_le : G * q ^ (e - c6T q e) ≤ c6Zq q e G B := by
    rw [← hZv]
    calc G * q ^ (e - c6T q e) ≤ G * q ^ (e - c6T q e) * q ^ (e - c6T q e) :=
          Nat.le_mul_of_pos_right _ hl1
      _ ≤ G * q ^ (e - c6T q e) * q ^ (e - c6T q e) * B := Nat.le_mul_of_pos_right _ hB
  have hGll_le : G * q ^ (e - c6T q e) * q ^ (e - c6T q e) ≤ c6Zq q e G B := by
    rw [← hZv]; exact Nat.le_mul_of_pos_right _ hB
  have hG_le : G ≤ c6Zq q e G B := (Nat.le_mul_of_pos_right _ hl1).trans hGl_le
  have hB_le : B ≤ c6Zq q e G B := by
    rw [← hZv]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos hG hl1) hl1)
  obtain ⟨N, hN⟩ : ∃ N, N = c6R q e * c6Zq q e G B := ⟨_, rfl⟩
  rw [← hN]
  have hRN : q ^ (2 * c6T q e) ≤ N := by
    rw [hN]; exact Nat.le_mul_of_pos_right _ hZ1
  have hZN : c6Zq q e G B ≤ N := by
    rw [hN]; exact Nat.le_mul_of_pos_left _ hR1
  have hN1 : 1 ≤ N := le_trans hR1 hRN
  have hNe : 2 ^ e ≤ N := by
    have h1 : 2 ^ e ≤ q ^ e := Nat.pow_le_pow_left hq e
    have h2 : q ^ e ≤ q ^ (2 * c6T q e) * q ^ (e - c6T q e) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : q ^ (e - c6T q e) ≤ c6Zq q e G B :=
      (Nat.le_mul_of_pos_left _ hG).trans hGl_le
    have h4 : q ^ (2 * c6T q e) * q ^ (e - c6T q e) ≤ N := by
      rw [hN]; exact Nat.mul_le_mul_left _ h3
    omega
  have hbN : e + 1 ≤ bitLen N := by
    by_contra hc
    have h1 := NatArith.lt_two_pow_bitLen N
    have h2 : 2 ^ bitLen N ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have bl : ∀ x, x ≤ 2 * N → bitLen x ≤ bitLen N + 2 := fun x hx => (cc9_bl hx).trans (by omega)
  have hle := cc9_cost_le (q := q) (CT := CT) (CW := CW) (CD := CD) (e := e) (t := c6T q e)
    (R := q ^ (2 * c6T q e)) (W := tripleWb 100 ^ c6K e) (G := G) (B := B) (E := bitLen N + 2)
    (by omega) (by omega) hT.2.le
    (bl _ (by rw [← pow_mul]; omega))
    (bl _ (by omega)) (bl _ (by omega)) (bl _ (by omega)) (bl _ (by omega))
    (bl _ ((Nat.div_le_self _ _).trans (by omega)))
    (bl _ ((Nat.mod_lt _ (by omega)).le.trans (by omega)))
    (bl _ (by omega)) (bl _ ((Nat.sub_le _ _).trans (by omega)))
    (bl _ (by rw [hZv]; omega)) (bl _ (by omega)) (bl _ (by omega)) (bl _ (by omega))
    (bl _ (by omega))
  calc ctrCost q CT CW CD e G B
      = cc9_cost q CT CW CD e (c6T q e) (q ^ (2 * c6T q e)) (tripleWb 100 ^ c6K e) G B :=
        cc9_cost_eq q CT CW CD e G B
    _ ≤ cc9_K q CT CW CD * (bitLen N + 2) ^ 3 := hle
    _ ≤ cc9_K q CT CW CD * (48 * N) := Nat.mul_le_mul_left _ (cc9_E3_le hN1)
    _ = 48 * cc9_K q CT CW CD * N := by ring

end AppC.C6RowAux

end SubNLogN.Machine
