import WP.W9c.RowCostLem

/-!
# WP.W9c.RowCostAD — phases A and D of the row driver's cost

`rowCostAD_holds : RowCostAD` with `K = 50`. Phases A and D only read and copy parameters, so
every term of `costA` and `costD` is `C·(bit length + 1)` (or a constant); each bit length is at
most `spreadRowBound`:
* header fields (`pSub, m1, r, log r, W, stride`) are entries of `preTapeFields`, so their bit
  lengths are `≤ |hdrSyms …| ≤ hdrLen ≤ S`; quotients/remainders of `m1`, `zl, zr ≤ r`,
  `outLen ≤ 2W`, `|taps| ≤ W` reduce to these;
* the Kronecker pack has `≤ w + (s−1+1)·|taps| ≤ (W+1)·(s+w+p_in+2) ≤ nb·(…) ≤ S` bits
  (`bitLen_pack_le`, `nb ≥ 1`).
After distributing `C·(x + y + 1)` the sum is a linear combination of `C·a ≤ C·S` facts.
-/

namespace WP.W9c

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- **Phases A and D of the row cost.** -/
theorem rowCostAD_holds : RowCostAD := by
  refine ⟨50, fun C Mul h w taps hD hT hTW => ?_⟩
  unfold costA costD
  obtain ⟨-, hr, hmt1, hmt⟩ := hD
  have hrlog : h.r = 2 ^ natLog2Fuel h.r h.r := hr
  have hr2 : 2 ≤ h.r := by
    rw [hr]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h.mr := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hTW' : taps.length ≤ effectiveFilterWidth h.m1 h.r := hTW
  have hzlr := zl_add_zr h.m1 h.r hrlog (by omega)
  have hnb : 0 < kroneckerSpreadNumBlocks h.m1 h.r := by
    have hW1 : 1 ≤ effectiveFilterWidth h.m1 h.r := by
      simp only [effectiveFilterWidth]
      omega
    simp only [kroneckerSpreadNumBlocks]
    exact Nat.div_pos (by omega) (by omega)
  set F := (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length with hF
  set S := spreadRowBound Mul w h with hSdef
  set Wd := effectiveFilterWidth h.m1 h.r with hWd
  set s := strideOf h.pSub with hs
  set nb := kroneckerSpreadNumBlocks h.m1 h.r with hnbd
  have hWmin : Wd = min (2 * h.m1 + 1) h.r := rfl
  have hW1 : 1 ≤ Wd := by omega
  -- the bound `S`
  have hS : S = nb * (2 * Mul ((Wd + 1) * (s + w)) + (Wd + 1) * (s + w + h.p_in + 2) +
      Wd * eb w) + (h.r + Wd) * eb w + (F + bitLen h.p_in + 2) + 1 := rfl
  have hY : 2 * Mul ((Wd + 1) * (s + w)) + (Wd + 1) * (s + w + h.p_in + 2) + Wd * eb w ≤
      nb * (2 * Mul ((Wd + 1) * (s + w)) + (Wd + 1) * (s + w + h.p_in + 2) + Wd * eb w) :=
    Nat.le_mul_of_pos_left _ hnb
  have hZ : h.r + Wd ≤ (h.r + Wd) * eb w := Nat.le_mul_of_pos_right _ (by unfold eb; omega)
  have hS1 : F + bitLen h.p_in + 3 ≤ S := by rw [hS]; omega
  have hS2 : h.r ≤ S := by rw [hS]; omega
  have hX : (Wd + 1) * (s + w + h.p_in + 2) ≤ S := by rw [hS]; omega
  -- the Kronecker pack
  have hpk := bitLen_pack_le (s - 1 + 1) w (by omega) taps hT
  have h2 : (s - 1 + 1) * taps.length ≤ (s + 1) * Wd := Nat.mul_le_mul (by omega) hTW'
  have e3 : (Wd + 1) * (s + w + h.p_in + 2) =
      (s + 1) * Wd + w + (Wd * w + Wd * h.p_in + Wd + s + h.p_in + 2) := by ring
  have hpack : bitLen (packSignedKronecker ((2 ^ (s - 1 + 1) : ℕ) : ℤ) taps).natAbs ≤ S := by
    omega
  -- header fields and derived quantities
  have hpS : bitLen h.pSub ≤ F := bitLen_le_pre _ _ _ _ _ (by simp [preTapeFields])
  have hm1 : bitLen h.m1 ≤ F := bitLen_le_pre _ _ _ _ _ (by simp [preTapeFields])
  have hrF : bitLen h.r ≤ F := bitLen_le_pre _ _ _ _ _ (by simp [preTapeFields])
  have hlr : bitLen (natLog2Fuel h.r h.r) ≤ F := bitLen_le_pre _ _ _ _ _ (by simp [preTapeFields])
  have hWF : bitLen Wd ≤ F := bitLen_le_pre _ _ _ _ _ (by simp [preTapeFields, hWd])
  have hsF : bitLen s ≤ F := bitLen_le_pre _ _ _ _ _ (by simp [preTapeFields, hs])
  have hones : ones (Computability.encodeNat s) ≤ bitLen s := ones_le_length _
  have hdiv : bitLen (h.m1 / 2 ^ natLog2Fuel h.r h.r) ≤ bitLen h.m1 :=
    bitLen_mono (Nat.div_le_self _ _)
  have hmod : bitLen (h.m1 % 2 ^ natLog2Fuel h.r h.r) ≤ bitLen h.m1 := bitLen_mono (Nat.mod_le _ _)
  have hs11 : bitLen (s - 1 + 1) ≤ bitLen s + 1 := by
    rw [← bitLen_double_add_one]
    exact bitLen_mono (by omega)
  have hzl : bitLen (zlOf h.r (lowOf h.m1 h.r)) ≤ bitLen h.r := bitLen_mono (by omega)
  have hzr : bitLen (zrOf h.r (lowOf h.m1 h.r)) ≤ bitLen h.r := bitLen_mono (by omega)
  have hol : bitLen (outLenOf Wd taps) ≤ bitLen Wd + 1 := by
    rw [← bitLen_double_add_one]
    exact bitLen_mono (by unfold outLenOf; split_ifs <;> omega)
  have hTl : bitLen taps.length ≤ bitLen Wd := bitLen_mono hTW'
  have h2b : bitLen 2 = 2 := by simpa using bitLen_two_pow 1
  -- products with `C`
  have hCS : ∀ {a : ℕ}, a ≤ S → C * a ≤ C * S := fun ha => Nat.mul_le_mul_left C ha
  have c1 := hCS (a := F) (by omega)
  have c2 := hCS (a := bitLen h.p_in) (by omega)
  have c3 := hCS (a := ones (Computability.encodeNat s)) (by omega)
  have c4 := hCS (a := bitLen h.m1) (by omega)
  have c5 := hCS (a := min (natLog2Fuel h.r h.r) (bitLen h.m1)) (by omega)
  have c6 := hCS (a := bitLen (natLog2Fuel h.r h.r)) (by omega)
  have c7 := hCS (a := bitLen (h.m1 / 2 ^ natLog2Fuel h.r h.r)) (by omega)
  have c8 := hCS (a := bitLen h.r) (by omega)
  have c9 := hCS (a := bitLen (h.m1 % 2 ^ natLog2Fuel h.r h.r)) (by omega)
  have c10 := hCS hpack
  have c11 := hCS (a := bitLen (s - 1 + 1)) (by omega)
  have c12 := hCS (a := bitLen h.pSub) (by omega)
  have c13 := hCS (a := bitLen Wd) (by omega)
  have c14 := hCS (a := bitLen (zlOf h.r (lowOf h.m1 h.r))) (by omega)
  have c15 := hCS (a := bitLen (zrOf h.r (lowOf h.m1 h.r))) (by omega)
  have c16 := hCS (a := bitLen (outLenOf Wd taps)) (by omega)
  have c17 := hCS (a := bitLen taps.length) (by omega)
  have c18 := hCS (a := bitLen 2) (by omega)
  have c19 : C ≤ C * S := Nat.le_mul_of_pos_right C (by omega)
  have eK : 50 * (C + 1) * S = 50 * (C * S) + 50 * S := by ring
  rw [eK]
  simp only [Nat.mul_add, Nat.mul_one]
  omega

#assert_std_axioms rowCostAD_holds

end WP.W9c
