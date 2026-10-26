/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.LiftPure

/-!
# `SubNLogN.Machine.Walsh.Cnot1Pure`: index arithmetic of one controlled flip (pure)

Paper: Lemma 5.4 (`lem:cnot`: `CNOT` moves the record at `x` to the address with
`x_t ↦ x_t ⊕ x_c`) and Lemma A.4(1) (`lem:transfer-streams`: a fixed permutation of a digit pair
costs `O(V)`).

**Scope (honest summary).** Pure lemmas, all proved (no `sorry`):
* `cnotPP`: the digit-pair permutation `(a, b) ↦ (a, b + a)` of `Fin 2 × Fin 2` (an involution);
* `testBit_setDigit_two`: the bits of `setDigit 2 k i d x` (`Contracts/Streams.lean:87`);
* `cubeOfNat_pairPermAddr`: for `y < 2^m`, the address map
  `pairPermAddr 2 m c t cnotPP.symm` of `K1PairPermStmt` is `cnotAddr [(c, t)]` read through
  `cubeOfNat` (`Contracts/Walsh.lean:71`), and stays below `2^m`;
* `permByInv_cnot`: hence `K1PairPermStmt`'s output order on the records of `encCube P z` is the
  record order of `encCube P (cnotArr [(c, t)] z)`;
* `length_carrSyms_encCube`: the stack volume of a cube array is `cvolCube m r w`.
-/

namespace SubNLogN.Machine.WalshCnot1

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Walsh

/-- The digit-pair permutation of a controlled flip, `(a, b) ↦ (a, b + a)` on `Fin 2 × Fin 2`
(first digit the control, second the target); it is an involution. -/
def cnotPP : Equiv.Perm (Fin 2 × Fin 2) where
  toFun p := (p.1, p.2 + p.1)
  invFun p := (p.1, p.2 + p.1)
  left_inv := by intro p; revert p; decide
  right_inv := by intro p; revert p; decide

/-! ## Bits of `setDigit 2` -/

theorem testBit_two_mul_add_zero (H d : ℕ) (hd : d < 2) :
    (2 * H + d).testBit 0 = decide (d = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, pow_zero, Nat.div_one, decide_eq_decide]
  omega

theorem testBit_two_mul_add_succ (H d n : ℕ) (hd : d < 2) :
    (2 * H + d).testBit (n + 1) = H.testBit n := by
  rw [Nat.testBit_succ]
  congr 1
  omega

/-- **Bits of `setDigit 2 k i d x`**: bit `k - 1 - i` becomes `d`, every other bit is kept. -/
theorem testBit_setDigit_two (k i d x j : ℕ) (hd : d < 2) :
    (setDigit 2 k i d x).testBit j = if j = k - 1 - i then decide (d = 1) else x.testBit j := by
  set e := k - 1 - i with he
  set Q := x / 2 ^ e with hQ
  set R := x % 2 ^ e with hR
  have hx : x = 2 ^ e * Q + R := (Nat.div_add_mod x (2 ^ e)).symm
  have hQ2 : Q = 2 * (Q / 2) + Q % 2 := (Nat.div_add_mod Q 2).symm
  have hRlt : R < 2 ^ e := Nat.mod_lt _ (pow_pos (by norm_num) e)
  have hb : Q % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hs : setDigit 2 k i d x = 2 ^ e * (2 * (Q / 2) + d) + R := by
    unfold setDigit digitAt
    rw [← he, ← hQ]
    have e1 : 2 ^ e * (2 * (Q / 2) + d) = 2 * (2 ^ e * (Q / 2)) + d * 2 ^ e := by ring
    have e2 : x = 2 * (2 ^ e * (Q / 2)) + Q % 2 * 2 ^ e + R := by
      conv_lhs => rw [hx, hQ2]
      ring
    rw [e1]
    omega
  have hx' : x = 2 ^ e * (2 * (Q / 2) + Q % 2) + R := by rw [← hQ2]; exact hx
  rw [hs, Nat.testBit_two_pow_mul_add _ hRlt]
  conv_rhs => rw [hx', Nat.testBit_two_pow_mul_add _ hRlt]
  rcases Nat.lt_trichotomy j e with hj | hj | hj
  · rw [if_pos hj, if_neg (by omega), if_pos hj]
  · subst hj
    rw [if_neg (lt_irrefl _), if_pos rfl, Nat.sub_self, testBit_two_mul_add_zero _ _ hd]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    obtain ⟨n, hn⟩ : ∃ n, j - e = n + 1 := ⟨j - e - 1, by omega⟩
    rw [hn, testBit_two_mul_add_succ _ _ _ hd, testBit_two_mul_add_succ _ _ _ hb]

/-! ## The controlled flip on indices -/

theorem digitAt_two_lt (k i x : ℕ) : digitAt 2 k i x < 2 := Nat.mod_lt _ (by norm_num)

theorem testBit_eq_digitAt (k i x : ℕ) :
    x.testBit (k - 1 - i) = decide (digitAt 2 k i x = 1) :=
  Nat.testBit_eq_decide_div_mod_eq

theorem setDigit_two_self (k i x : ℕ) : setDigit 2 k i (digitAt 2 k i x) x = x := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_setDigit_two _ _ _ _ _ (digitAt_two_lt k i x)]
  split_ifs with h
  · rw [h, testBit_eq_digitAt]
  · rfl

/-- `pairPermAddr 2 m c t cnotPP.symm` replaces the target digit by `target ⊕ control`. -/
theorem pairPermAddr_cnot (m c t y : ℕ) :
    pairPermAddr 2 m c t cnotPP.symm y =
      setDigit 2 m t ((digitAt 2 m t y + digitAt 2 m c y) % 2) y := by
  simp only [pairPermAddr, cnotPP, Equiv.coe_fn_symm_mk, Fin.val_add, digitFin]
  rw [setDigit_two_self]

/-- **The controlled flip on indices.** For `y < 2^m`, the address map of
`K1PairPermStmt 2 cnotPP` (digits `c`, `t`) stays below `2^m` and, read through `cubeOfNat`, is
`cnotAddr [(c, t)]`. -/
theorem cubeOfNat_pairPermAddr (m : ℕ) (c t : Fin m) (y : ℕ) (hy : y < 2 ^ m) :
    pairPermAddr 2 m c t cnotPP.symm y < 2 ^ m ∧
      cubeOfNat m (pairPermAddr 2 m c t cnotPP.symm y) = cnotAddr [(c, t)] (cubeOfNat m y) := by
  rw [pairPermAddr_cnot]
  have hdt : digitAt 2 m t y < 2 := digitAt_two_lt _ _ _
  have hdc : digitAt 2 m c y < 2 := digitAt_two_lt _ _ _
  have hd : (digitAt 2 m t y + digitAt 2 m c y) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hc : (c : ℕ) < m := c.isLt
  have ht : (t : ℕ) < m := t.isLt
  have hbits := fun j => testBit_setDigit_two m t _ y j hd
  constructor
  · apply Nat.lt_pow_two_of_testBit
    intro j hj
    rw [hbits, if_neg (by omega)]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hj))
  · funext p
    simp only [cubeOfNat, cnotAddr, List.any_cons, List.any_nil, Bool.or_false]
    rw [hbits]
    by_cases hp : p = t
    · have htt : decide (t = t) = true := decide_eq_true rfl
      rw [if_pos (by rw [hp]), hp, htt, Bool.true_and, testBit_eq_digitAt, testBit_eq_digitAt]
      rcases (by omega : digitAt 2 m t y = 0 ∨ digitAt 2 m t y = 1) with h1 | h1 <;>
      rcases (by omega : digitAt 2 m c y = 0 ∨ digitAt 2 m c y = 1) with h2 | h2 <;>
      simp [h1, h2]
    · have hpt : (p : ℕ) ≠ t := fun h => hp (Fin.ext h)
      have hp' : (p : ℕ) < m := p.isLt
      rw [if_neg (by omega)]
      have htp : decide (t = p) = false := by simp [Ne.symm hp]
      rw [htp, Bool.false_and, Bool.xor_false]

theorem sum_range_const (n a : ℕ) : ((List.range n).map fun _ => a).sum = n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring

/-- The stack volume of a cube array is `cvolCube m r w = 2^m·(2rw + 1)`. -/
theorem length_carrSyms_encCube (P w m r : ℕ) (z : RArr (Cube m) r) :
    (carrSyms w (encCube P z)).length = cvolCube m r w := by
  rw [← cvol, WalshLift.cvol_eq_sum]
  simp only [encCube, encArr, cubeAddrs, List.map_map, Function.comp_def, List.length_map,
    List.length_finRange]
  rw [sum_range_const, cvolCube]
  ring

/-- **`K1PairPermStmt`'s output order is the controlled flip.** On the records of
`encCube P z`, the permutation `permByInv (pairPermAddr 2 m c t cnotPP.symm)` gives the records of
`encCube P (cnotArr [(c, t)] z)`. -/
theorem permByInv_cnot (P w m r : ℕ) (c t : Fin m) (z : RArr (Cube m) r) :
    permByInv (pairPermAddr 2 m c t cnotPP.symm) ((encCube P z).map (crecBits w)) =
      (encCube P (cnotArr [(c, t)] z)).map (crecBits w) := by
  simp only [permByInv, encCube, encArr, cubeAddrs, List.map_map, List.length_map,
    List.length_range]
  apply List.map_congr_left
  intro y hy
  rw [List.mem_range] at hy
  obtain ⟨hlt, heq⟩ := cubeOfNat_pairPermAddr m c t y hy
  rw [List.getD_eq_getElem _ _ (by simp [hlt])]
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, heq, cnotArr]

end SubNLogN.Machine.WalshCnot1
