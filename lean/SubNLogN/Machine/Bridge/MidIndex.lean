/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.FFT
import SubNLogN.Machine.Contracts.RecordsTensor
import SubNLogN.Math.Walsh.Proofs.DirectFFTExact
import SubNLogN.Math.Walsh.IntForms.Address

/-!
# K5 middle glue, index part (`Bridge/MidIndex.lean`): the cube record order is `encFreq` order

The Walsh middle (`WalshMiddleMachineGenStmt`, `Contracts/FFT.lean`) stores a tensor
`U : Idx (fftShape a ℓ) → ℂ` as the cube array `ofTensor a ℓ U`: record `x` (in `cubeAddrs`
order) holds the last-axis line `k ↦ U (tensorIdx a ℓ x k)`. The bridge
(`MidMachineStmt`, `Contracts/Bridge.lean`) stores one-coefficient records in natural
frequency order `idxAddrsFreq`. This file proves that the two orders agree after flattening
(`cubeAddrs_flatMap_tensorIdx`), the index fact behind the regroup glue of
Section 6 (`sec:direct-fft`, natural axis order with the last axis contiguous, records = last-axis lines,
axis `0` most significant).

**Scope (honest summary).** Pure index lemmas, no machine content, no hypotheses.
-/

namespace SubNLogN.Machine.BridgeRed

open SubNLogN.Math.Common SubNLogN.Math.Walsh SubNLogN.Machine
open scoped BigOperators

variable {D : ℕ}

/-- The exponent sum of the record axes after axis `i`. -/
def sufExp (a : Fin D → ℕ) (i : Fin D) : ℕ :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin D => i < l), a l

theorem axisOffset_add_sufExp (a : Fin D → ℕ) (i : Fin D) :
    axisOffset a i + a i + sufExp a i = addrBits a := by
  unfold axisOffset sufExp addrBits
  rw [List.sum_take_ofFn, List.sum_ofFn, Finset.sum_filter, Finset.sum_filter]
  have hsplit : ∀ j : Fin D, a j = ((if (j : ℕ) < i then a j else 0) +
      (if j = i then a j else 0)) + (if i < j then a j else 0) := by
    intro j
    rcases lt_trichotomy (j : ℕ) (i : ℕ) with h | h | h
    · have h1 : j ≠ i := fun e => by rw [e] at h; exact lt_irrefl _ h
      have h2 : ¬ i < j := fun e => absurd (Fin.lt_def.mp e) (by omega)
      simp [h, h1, h2]
    · have e : j = i := Fin.ext h
      subst e
      simp
    · have h1 : j ≠ i := fun e => by rw [e] at h; exact lt_irrefl _ h
      have h2 : i < j := Fin.lt_def.mpr h
      have h3 : ¬ (j : ℕ) < i := by omega
      simp [h1, h2, h3]
  conv_rhs => rw [Finset.sum_congr rfl (fun j _ => hsplit j)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem totalLen_fftShape (a : Fin D → ℕ) (ℓ : ℕ) :
    totalLen (fftShape a ℓ) = 2 ^ addrBits a * 2 ^ ℓ := by
  unfold totalLen fftShape
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_castSucc, pow_add,
    DirectFFTExactProof.fftExp_last]
  congr 2
  unfold addrBits
  rw [List.sum_ofFn]
  exact Finset.sum_congr rfl fun i _ => DirectFFTExactProof.fftExp_castSucc a ℓ i

theorem suffixProd_fftShape_last (a : Fin D → ℕ) (ℓ : ℕ) :
    suffixProd (fftShape a ℓ) (Fin.last D) = 1 := by
  unfold suffixProd
  rw [Finset.prod_eq_one]
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
  exact absurd (Fin.le_last l) (not_le.mpr hl)

theorem suffixProd_fftShape_castSucc (a : Fin D → ℕ) (ℓ : ℕ) (i : Fin D) :
    suffixProd (fftShape a ℓ) (Fin.castSucc i) = 2 ^ sufExp a i * 2 ^ ℓ := by
  unfold suffixProd fftShape sufExp
  rw [Finset.prod_pow_eq_pow_sum, ← pow_add, Finset.sum_filter, Finset.sum_filter,
    Fin.sum_univ_castSucc]
  congr 1
  have hl : Fin.castSucc i < Fin.last D := Fin.castSucc_lt_last i
  rw [if_pos hl, DirectFFTExactProof.fftExp_last]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [DirectFFTExactProof.fftExp_castSucc]
  simp only [Fin.castSucc_lt_castSucc_iff]

theorem cubeBit_cubeOfNat' (m X p : ℕ) :
    cubeBit (cubeOfNat m X) p = (decide (p < m) && X.testBit (m - 1 - p)) := by
  by_cases h : p < m
  · rw [DirectFFTExactProof.cubeBit_lt _ h]
    simp [h, cubeOfNat]
  · simp [cubeBit, h]

theorem axisVal_cubeOfNat (a : Fin D → ℕ) (X : ℕ) (i : Fin D) :
    axisVal a (cubeOfNat (addrBits a) X) i = X / 2 ^ sufExp a i % 2 ^ a i := by
  have hm := axisOffset_add_sufExp a i
  apply Nat.eq_of_testBit_eq
  intro v
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hv : v < a i
  · rw [DirectFFTExactProof.testBit_axisVal a _ i hv, cubeBit_cubeOfNat']
    unfold origPos
    have hp : axisOffset a i + (a i - 1 - v) < addrBits a := by omega
    have he : addrBits a - 1 - (axisOffset a i + (a i - 1 - v)) = v + sufExp a i := by omega
    simp [hp, he, hv]
  · have hlt : axisVal a (cubeOfNat (addrBits a) X) i < 2 ^ v :=
      lt_of_lt_of_le (DirectFFTExactProof.axisVal_lt a _ i)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow hlt]
    simp [hv]

/-- **Digits of a cube coefficient**: the coefficient `k` of record `cubeOfNat m X` is the tensor
index with natural-frequency rank `X·2^ℓ + k`. -/
theorem tensorIdx_cubeOfNat (a : Fin D → ℕ) (ℓ : ℕ) (X : ℕ) (k : Fin (2 ^ ℓ))
    (n : Fin (totalLen (fftShape a ℓ))) (hn : (n : ℕ) = X * 2 ^ ℓ + k) :
    tensorIdx a ℓ (cubeOfNat (addrBits a) X) k = (encFreq (fftShape a ℓ)).symm n := by
  funext i
  apply Fin.ext
  rw [encFreq_symm_apply]
  induction i using Fin.lastCases with
  | last =>
    rw [DirectFFTExactProof.tensorIdx_last_val, suffixProd_fftShape_last, Nat.div_one,
      DirectFFTExactProof.fftShape_last, hn, mul_comm X, Nat.mul_add_mod,
      Nat.mod_eq_of_lt k.isLt]
  | cast i =>
    rw [DirectFFTExactProof.tensorIdx_castSucc_val, suffixProd_fftShape_castSucc,
      DirectFFTExactProof.fftShape_castSucc, axisVal_cubeOfNat, hn]
    congr 1
    rw [mul_comm (2 ^ sufExp a i), ← Nat.div_div_eq_div_mul]
    congr 1
    rw [mul_comm X, Nat.mul_add_div (Nat.two_pow_pos ℓ), Nat.div_eq_of_lt k.isLt, add_zero]

/-- **The cube record order flattens to natural frequency order** (Section 6 (`sec:direct-fft`)): the
coefficients of the records of `cubeAddrs`, record by record, are the tensor indices in the
order `idxAddrsFreq` (last axis contiguous, axis `0` most significant). -/
theorem cubeAddrs_flatMap_tensorIdx (a : Fin D → ℕ) (ℓ : ℕ) :
    (cubeAddrs (addrBits a)).flatMap (fun x => (List.finRange (2 ^ ℓ)).map (tensorIdx a ℓ x)) =
      idxAddrsFreq (fftShape a ℓ) := by
  have hT := totalLen_fftShape a ℓ
  have hr : List.range (2 ^ addrBits a) = (List.finRange (2 ^ addrBits a)).map Fin.val := by
    apply List.ext_getElem <;> simp
  have hL : (cubeAddrs (addrBits a)).flatMap
      (fun x => (List.finRange (2 ^ ℓ)).map (tensorIdx a ℓ x)) =
      List.flatten (List.ofFn fun X : Fin (2 ^ addrBits a) =>
        List.ofFn fun k : Fin (2 ^ ℓ) => tensorIdx a ℓ (cubeOfNat (addrBits a) X) k) := by
    unfold cubeAddrs
    rw [List.flatMap_map, hr, List.flatMap_map, List.flatMap_def, List.ofFn_eq_map]
    congr 1
    refine List.map_congr_left fun X _ => ?_
    rw [List.ofFn_eq_map]
  rw [hL]
  unfold idxAddrsFreq
  rw [← List.ofFn_eq_map, List.ofFn_congr hT, List.ofFn_mul]
  congr 1
  refine congrArg List.ofFn (funext fun X => congrArg List.ofFn (funext fun k => ?_))
  exact tensorIdx_cubeOfNat a ℓ X k _ rfl

end SubNLogN.Machine.BridgeRed
