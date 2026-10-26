/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6PiecesLeaves
import SubNLogN.Machine.AppC.C5StreamArith

/-!
# Lemma A.8 piece-loop kernels, shared part (`Machine/AppC/C6PcBase.lean`)

Shared definitions and lemmas of the three level-E counter kernels `C6PcTestStmt`,
`C6PcArgsStmt`, `C6PcAdvStmt` (`C6PiecesLeaves.lean`): the scratch type `PE`, bit-length bounds
for the counters of a piece (`c6PJ`, `c6PL`, `c6Rp`, `q^o`, `c6PG`, `c6PB`). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Proved (no `sorry`).** Pure lemmas only.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

namespace AppC.C6PcAux

open NatArith

/-- Scratch stacks of the piece-loop kernels. -/
abbrev PE : Type := Fin 24

/-- Scratch stack `i`. -/
abbrev sv {N : Type} (i : Fin 24) : KLoc N PE := .inr i

/-! ## Bit lengths -/

theorem bitLen_le_of_lt_pow {q n c : ℕ} (hc : c < q ^ n) : bitLen c ≤ n * bitLen q :=
  NatArith.bitLen_le_of_lt' (lt_of_lt_of_le hc (by
    calc q ^ n ≤ (2 ^ bitLen q) ^ n := Nat.pow_le_pow_left (NatArith.lt_two_pow_bitLen q).le n
      _ = 2 ^ (n * bitLen q) := by rw [← pow_mul, mul_comm]))

theorem bitLen_pow_le {q : ℕ} (hq : 2 ≤ q) (n : ℕ) : bitLen (q ^ n) ≤ (n + 1) * bitLen q :=
  bitLen_le_of_lt_pow (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self n))

theorem bitLen_le_self'' (n : ℕ) : bitLen n ≤ n :=
  NatArith.bitLen_le_of_lt' Nat.lt_two_pow_self

theorem bitLen_tripleM : bitLen (tripleM 100) ≤ 20 :=
  NatArith.bitLen_le_of_lt' (by norm_num [tripleM])

theorem two_le_tripleM : 2 ≤ tripleM 100 := by norm_num [tripleM]

/-! ## The counters of a piece -/

theorem c6PL_le {q e o : ℕ} (ho : o < e - c6T q e) : c6PL q e o ≤ e - c6T q e - o := by
  unfold c6PL c6PJ
  exact Nat.pow_log_le_self _ (by omega)

theorem c6PJ_lt {q e o : ℕ} : c6PJ q e o < c6PL q e o := by
  unfold c6PL
  calc c6PJ q e o < 2 ^ c6PJ q e o := Nat.lt_two_pow_self
    _ ≤ tripleM 100 ^ c6PJ q e o := Nat.pow_le_pow_left two_le_tripleM _

theorem bitLen_c6Rp_le {q e : ℕ} (hq : 2 ≤ q) (he : 35 ≤ e) :
    bitLen (c6Rp q e) ≤ (2 * e + 2) * bitLen q := by
  have ht := (SubNLogN.Machine.AppC.C6Aux.c6T_lt hq he).2
  have h1 := C6Aux.c6Rp_lt (e := e) hq
  have h2 : 2 * c6R q e ≤ q ^ (2 * e + 2) := by
    unfold c6R
    calc 2 * q ^ (2 * c6T q e) ≤ q * q ^ (2 * c6T q e) := Nat.mul_le_mul_right _ hq
      _ = q ^ (2 * c6T q e + 1) := by ring
      _ ≤ q ^ (2 * e + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  exact bitLen_le_of_lt_pow (lt_of_lt_of_le h1 h2)

theorem bitLen_c6PG_le {q e G o : ℕ} (hq : 2 ≤ q) (ho : o < e - c6T q e) :
    bitLen (c6PG q e G o) ≤ 2 * (e + 1) * bitLen q + bitLen G := by
  unfold c6PG
  have h1 := NatArith.bitLen_mul_le' (q ^ (e - c6T q e - o - c6PL q e o) * G) (q ^ o)
  have h2 := NatArith.bitLen_mul_le' (q ^ (e - c6T q e - o - c6PL q e o)) G
  have h3 := bitLen_pow_le hq (e - c6T q e - o - c6PL q e o)
  have h4 := bitLen_pow_le hq o
  have h5 : (e - c6T q e - o - c6PL q e o + 1) * bitLen q ≤ (e + 1) * bitLen q :=
    Nat.mul_le_mul_right _ (by omega)
  have h6 : (o + 1) * bitLen q ≤ (e + 1) * bitLen q := Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem bitLen_c6PB_le {q e B o : ℕ} (hq : 2 ≤ q) :
    bitLen (c6PB q e B o) ≤ (e + 1) * bitLen q + bitLen B := by
  unfold c6PB
  have h2 := NatArith.bitLen_mul_le' (q ^ (e - c6T q e - o - c6PL q e o)) B
  have h3 := bitLen_pow_le hq (e - c6T q e - o - c6PL q e o)
  have h5 : (e - c6T q e - o - c6PL q e o + 1) * bitLen q ≤ (e + 1) * bitLen q :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem bitLen_qpow_le {q e o : ℕ} (hq : 2 ≤ q) (ho : o ≤ e) :
    bitLen (q ^ o) ≤ (e + 1) * bitLen q :=
  (bitLen_pow_le hq o).trans (Nat.mul_le_mul_right _ (by omega))

end AppC.C6PcAux

end SubNLogN.Machine
