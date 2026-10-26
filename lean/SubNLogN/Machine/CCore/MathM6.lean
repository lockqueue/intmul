/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelMathDefs

/-!
# C-core skeleton, leaf (M6a): encodings are `O(V_g)` (`CCore/MathM6.lean`)

Proves the encoding-size leaf of `CCore/SkelMathDefs.lean`, for every `p : LayerParams` (no
admissibility hypothesis is needed), with cutoff `P₀ = 0`:

* `encLen_holds p : EncLenStmt p`. The `io` encoding `Enc t hA hS z` has exactly
  `M · (2 w_g r + 1)` symbols (`M` records of `r` coefficients, each coefficient two `w_g`-bit
  two's-complement fields, one `sep` per record; `M6Aux.enc_length_m6`). Since `r ≥ 1` (from the
  `r`-band `2^{a_r P/d} ≤ r`), `M ≥ 1` (`A, S ≥ 1`) and `w_g = P + 2Δ + 3 ≥ 3`, this gives
  `|Enc| + 1 ≤ 4 M r w_g = 2 V_g`.

(The header leaf `HdrLenStmt` is proved in `CCore/LeafSplitAux.lean`.)
-/

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common

namespace M6Aux

/-! ## Lengths of the `io` encoding -/

theorem coefBits_length_m6 (w : ℕ) (c : CInt) : (coefBits w c).length = 2 * w := by
  simp only [coefBits, twosBits, bitsLE, List.length_append, List.length_map, List.length_range]
  ring

theorem crecBits_length_m6 (w : ℕ) (cs : List CInt) :
    (crecBits w cs).length = 2 * w * cs.length := by
  induction cs with
  | nil => simp [crecBits]
  | cons c cs ih =>
    have e : crecBits w (c :: cs) = coefBits w c ++ crecBits w cs := by simp [crecBits]
    rw [e, List.length_append, ih, coefBits_length_m6, List.length_cons]
    ring

theorem carrSyms_length_m6 (w r : ℕ) (v : List (List CInt)) (hv : ∀ cs ∈ v, cs.length = r) :
    (carrSyms w v).length = v.length * (2 * w * r + 1) := by
  induction v with
  | nil => simp [carrSyms, arrSyms, blk]
  | cons cs v ih =>
    have h1 : cs.length = r := hv cs (by simp)
    have h2 := ih (fun c hc => hv c (List.mem_cons_of_mem _ hc))
    have e : carrSyms w (cs :: v) = recSyms (crecBits w cs) ++ carrSyms w v := by
      simp [carrSyms, arrSyms, blk]
    rw [e, List.length_append, h2]
    simp only [recSyms, List.length_append, List.length_map, crecBits_length_m6, h1,
      List.length_cons, List.length_nil]
    ring

theorem encArr_rows_m6 {α : Type} {r : ℕ} (F : ℕ) (addrs : List α) (z : α → Fin r → ℂ) :
    ∀ cs ∈ encArr F addrs z, cs.length = r := by
  intro cs hcs
  simp only [encArr, List.mem_map] at hcs
  obtain ⟨x, -, rfl⟩ := hcs
  simp

theorem encArr_length_m6 {α : Type} {r : ℕ} (F : ℕ) (addrs : List α) (z : α → Fin r → ℂ) :
    (encArr F addrs z).length = addrs.length := by
  simp [encArr]

theorem layerAddrs_length_m6 (A K D S : ℕ) (hA : 0 < A) (hS : 0 < S) :
    (layerAddrs A K D S hA hS).length = A * 2 ^ (K * D) * S := by
  simp [layerAddrs]

/-- The `io` encoding has exactly `M · (2 w_g r + 1)` symbols. -/
theorem enc_length_m6 (t : CCoreRT) (hA : 0 < t.A) (hS : 0 < t.S)
    (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) :
    (Enc t hA hS z).length = t.M * (2 * t.wg * t.r + 1) := by
  unfold Enc
  rw [carrSyms_length_m6 t.wg t.r _ (encArr_rows_m6 _ _ _), encArr_length_m6,
    layerAddrs_length_m6]
  unfold CCoreRT.M
  ring

/-- `M ≥ 1` for a complete shape. -/
theorem one_le_M_m6 {t : CCoreRT} (hA : 1 ≤ t.A) (hS : 1 ≤ t.S) : 1 ≤ t.M := by
  unfold CCoreRT.M
  calc 1 = 1 * 1 * 1 := rfl
    _ ≤ t.A * t.S * 2 ^ (t.K * t.D) := Nat.mul_le_mul (Nat.mul_le_mul hA hS) Nat.one_le_two_pow

end M6Aux

/-- **(M6a) Encodings are `O(V_g)`** (`EncLenStmt`), with cutoff `0`:
`|Enc t z| + 1 = M (2 w_g r + 1) + 1 ≤ 4 M r w_g = 2 V_g`. -/
theorem encLen_holds (p : LayerParams) : EncLenStmt p := by
  refine ⟨0, fun t hA hS z hb => ?_⟩
  obtain ⟨-, -, -, har, -, -, -, hA1, hS1, -, -, -, -, -⟩ := hb
  have hr0 : (0 : ℝ) < t.r := lt_of_lt_of_le (Real.rpow_pos_of_pos two_pos _) har
  have hr1 : 1 ≤ t.r := by have := Nat.cast_pos.mp hr0; omega
  have hM1 : 1 ≤ t.M := M6Aux.one_le_M_m6 hA1 hS1
  have hw : 3 ≤ t.wg := by unfold CCoreRT.wg; omega
  have hX : t.M * 1 * 3 ≤ t.M * t.r * t.wg := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hr1) hw
  rw [M6Aux.enc_length_m6]
  unfold CCoreRT.volG
  nlinarith

end SubNLogN.Machine.CCore
