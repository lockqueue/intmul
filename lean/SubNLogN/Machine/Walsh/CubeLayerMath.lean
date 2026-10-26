/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Walsh

/-!
# K3.0 value glue (`Machine/Walsh/CubeLayerMath.lean`): the cube order is the layer order

**Scope (honest summary).** Pure value-level lemmas, all proved (no `sorry`), in the namespace
`SubNLogN.Machine.WalshCubeAux`. Fix a slice shape `[2^{j₀}] × [2^K]^D × [2^{nS}]` of the
complete `m`-bit cube, `j₀ + DK + nS = m` (Definition 5.6, `def:walsh-positional`).
* `layerAddrOfIndex_eq_cubeToAddr`: for every `i` the layer address with lexicographic index `i`
  (`layerAddrOfIndex`, `Contracts/Records.lean`; the record order of Proposition A.11,
  `prop:prop14-param`) is the reading `cubeToAddr` (`Math/Walsh/Cube.lean`) of the cube address with
  index `i` (`cubeOfNat`, `Contracts/Walsh.lean`).
* `encLayer_eq_encCube`: hence every layer array `y` on the slice shape is stored exactly as the
  cube array `y ∘ cubeToAddr`.
* `encCube_eq_encLayer`, `encLayer_layerH_eq`: the input and the output of a layer call on the
  slice (input `z' = z ∘ addrToCube`, output `Q_P(H z')`) are stored exactly as the cube arrays `z`
  and `Q_P(H_T z)`, `T = slicePos m K j₀ D ρ` (via `layerH_cubeToAddr_eq_hT`, `Math/Walsh/Cube.lean`).
-/

namespace SubNLogN.Machine.WalshCubeAux

open TMFw TMFw.Contracts SubNLogN.Math.Walsh SubNLogN.Math.Common SubNLogN.Machine

/-- `K·D = K·(D-1-j) + j·K + K` for `j < D`. -/
theorem chunk_split {K D j : ℕ} (hj : j < D) : K * D = K * (D - 1 - j) + j * K + K := by
  have e : D = (D - 1 - j) + j + 1 := by omega
  conv_lhs => rw [e]
  ring

/-- **The lexicographic layer index is the cube index**: for `j₀ + DK + nS = m` and every `i`,
`layerAddrOfIndex (2^{j₀}) K D (2^{nS}) i = cubeToAddr K j₀ D nS (cubeOfNat m i)` (both sides read
only the bits `< m` of `i`). -/
theorem layerAddrOfIndex_eq_cubeToAddr {K j₀ D nS m : ℕ} (hm : j₀ + D * K + nS = m)
    (hA : 0 < 2 ^ j₀) (hS : 0 < 2 ^ nS) (i : ℕ) :
    layerAddrOfIndex (2 ^ j₀) K D (2 ^ nS) hA hS i = cubeToAddr K j₀ D nS (cubeOfNat m i) := by
  have hKD : K * D = D * K := Nat.mul_comm K D
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- the prefix
    apply Fin.ext
    simp only [layerAddrOfIndex, cubeToAddr, toFinPow]
    rw [Nat.mod_eq_of_lt (bitsValMSB_lt _ _)]
    apply Nat.eq_of_testBit_eq
    intro t
    rw [Nat.testBit_mod_two_pow, ← pow_add, Nat.testBit_div_two_pow, testBit_bitsValMSB]
    by_cases ht : t < j₀
    · rw [if_pos ht, decide_eq_true ht, Bool.true_and, cubeBit_of_lt _ (by omega)]
      simp only [cubeOfNat]
      congr 1
      omega
    · rw [if_neg ht, decide_eq_false ht, Bool.false_and]
  · -- the chunks
    funext j k
    simp only [layerAddrOfIndex, cubeToAddr]
    have hj := j.isLt
    have hk := k.isLt
    have hsplit := chunk_split (K := K) hj
    rw [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and, Nat.testBit_div_two_pow,
      Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    have hlt : (k : ℕ) + K * (D - 1 - (j : ℕ)) < K * D := by omega
    rw [decide_eq_true hlt, Bool.true_and, cubeBit_of_lt _ (by omega)]
    simp only [cubeOfNat]
    congr 1
    omega
  · -- the suffix
    apply Fin.ext
    simp only [layerAddrOfIndex, cubeToAddr, toFinPow]
    rw [Nat.mod_eq_of_lt (bitsValMSB_lt _ _)]
    apply Nat.eq_of_testBit_eq
    intro t
    rw [Nat.testBit_mod_two_pow, testBit_bitsValMSB]
    by_cases ht : t < nS
    · rw [if_pos ht, decide_eq_true ht, Bool.true_and, cubeBit_of_lt _ (by omega)]
      simp only [cubeOfNat]
      congr 1
      omega
    · rw [if_neg ht, decide_eq_false ht, Bool.false_and]

/-- The number of records of a slice shape: `2^{j₀}·2^{KD}·2^{nS} = 2^m`. -/
theorem card_slice_shape {K j₀ D nS m : ℕ} (hm : j₀ + D * K + nS = m) :
    2 ^ j₀ * 2 ^ (K * D) * 2 ^ nS = 2 ^ m := by
  rw [← pow_add, ← pow_add, ← hm, Nat.mul_comm K D]

/-- **A layer array on a slice shape is stored as a cube array**: `encLayer P y` is
`encCube P (y ∘ cubeToAddr)`. -/
theorem encLayer_eq_encCube {r K j₀ D nS m : ℕ} (hm : j₀ + D * K + nS = m)
    (hA : 0 < 2 ^ j₀) (hS : 0 < 2 ^ nS) (P : ℕ) (y : RArr (LayerAddr (2 ^ j₀) K D (2 ^ nS)) r) :
    encLayer hA hS P y = encCube P (fun x : Cube m => y (cubeToAddr K j₀ D nS x)) := by
  unfold encLayer encCube encArr layerAddrs cubeAddrs
  rw [List.map_map, List.map_map, card_slice_shape hm]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  rw [layerAddrOfIndex_eq_cubeToAddr hm hA hS i]

/-- The input of a slice call: the cube array `z` is stored as the layer array
`z ∘ addrToCube`. -/
theorem encCube_eq_encLayer {r K j₀ D nS m : ℕ} (hm : j₀ + D * K + nS = m)
    (hA : 0 < 2 ^ j₀) (hS : 0 < 2 ^ nS) (P : ℕ) (z : RArr (Cube m) r) :
    encCube P z = encLayer hA hS P (fun a => z (addrToCube K j₀ D nS m a)) := by
  rw [encLayer_eq_encCube hm]
  simp only [addrToCube_cubeToAddr hm]

/-- The output of a slice call: `Q_P(H z')`, `z' = z ∘ addrToCube`, is stored as the cube array
`Q_P(H_T z)`, `T = slicePos m K j₀ D ρ`. -/
theorem encLayer_layerH_eq {r K j₀ D nS m : ℕ} (hm : j₀ + D * K + nS = m)
    (hA : 0 < 2 ^ j₀) (hS : 0 < 2 ^ nS) (P : ℕ) (ρ : Fin K) (z : RArr (Cube m) r) :
    encLayer hA hS P (truncArr P (layerH ρ (fun a => z (addrToCube K j₀ D nS m a)))) =
      encCube P (truncArr P (hT (slicePos m K j₀ D ρ) z)) := by
  rw [encLayer_eq_encCube hm]
  congr 1
  funext x k
  simp only [truncArr]
  rw [layerH_cubeToAddr_eq_hT ρ hm z x k]

end SubNLogN.Machine.WalshCubeAux
