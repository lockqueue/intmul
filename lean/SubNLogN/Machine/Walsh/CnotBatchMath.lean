/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Walsh
import SubNLogN.Math.Walsh.Exact

/-!
# K3-PERM (`Machine/Walsh/CnotBatchMath.lean`): value facts for the CNOT-batch composite

**Scope (honest summary).** Pure value-level lemmas used by the machine composite of
Proposition 5.5 (`Machine/Walsh/CnotBatch.lean`); all proved, no machine programs here.
* Encodings: on the `P`-grid the stored numerators at precision `P + δ` are those at `P` times
  `2^δ` (`encCube_lift`, the value form of the lift/lowering of Lemma 5.3 and Proposition 5.5); a disk array
  on the `P`-grid fits `w` bits when `P + 2 ≤ w` (`cArrFits_encCube`); the stack volume of a cube
  array is `cvolCube` (`cvol_encCube`).
* Exact rounds (Lemma 5.2, `lem:walsh-exact`, `gadget_round`): a layer call `Q_{P'}(H_Sel ·)` on a disk array
  on the `Q`-grid with `Q + D ≤ P'` is exact (`layer_round`).
-/

namespace SubNLogN.Machine.CnotBatchRed

open TMFw TMFw.Contracts SubNLogN.Math.Walsh SubNLogN.Math.Common SubNLogN.Machine

/-! ## Encodings at two precisions -/

/-- On the `P`-grid, `gridInt P` returns the exact numerators. -/
theorem gridInt_of_onGridR {P : ℕ} {x : ℝ} {a : ℤ} (hx : x = (a : ℝ) * gridUnit P) (δ : ℕ) :
    round (x * 2 ^ (P + δ)) = a * 2 ^ δ := by
  have h : x * 2 ^ (P + δ) = ((a * 2 ^ δ : ℤ) : ℝ) := by
    rw [hx, gridUnit, pow_add]
    push_cast
    field_simp
  rw [h, round_intCast]

/-- On the `P`-grid the numerators at precision `P + δ` are those at `P` times `2^δ`. -/
theorem gridInt_lift {P : ℕ} (δ : ℕ) {v : ℂ} (hv : OnGrid P v) :
    gridInt (P + δ) v = liftC δ (gridInt P v) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hv
  have h0a := gridInt_of_onGridR ha 0
  have h0b := gridInt_of_onGridR hb 0
  simp only [Nat.add_zero, pow_zero, mul_one] at h0a h0b
  simp only [gridInt, liftC, h0a, h0b, gridInt_of_onGridR ha δ, gridInt_of_onGridR hb δ]

/-- **Value form of the lift** (Lemma 5.3, `lem:walsh-lift`): for a `P`-grid array,
`encCube (P + δ) z = mapC (liftC δ) (encCube P z)`. -/
theorem encCube_lift {m r P : ℕ} (δ : ℕ) {z : RArr (Cube m) r} (hz : ArrOnGrid P z) :
    encCube (P + δ) z = mapC (liftC δ) (encCube P z) := by
  simp only [encCube, encArr, mapC, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply, List.map_map]
  apply List.map_congr_left
  intro k _
  exact gridInt_lift δ (hz x k)

/-- A disk array on the `P`-grid fits `w`-bit two's-complement fields when `P + 2 ≤ w`. -/
theorem cArrFits_encCube {m r P w : ℕ} {z : RArr (Cube m) r} (hz : ArrOnDiskGrid P z)
    (hw : P + 2 ≤ w) : CArrFits w (encCube P z) := by
  intro cs hcs c hc
  simp only [encCube, encArr, List.mem_map] at hcs
  obtain ⟨x, -, rfl⟩ := hcs
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hn⟩ := hz x k
  have h0a := gridInt_of_onGridR ha 0
  have h0b := gridInt_of_onGridR hb 0
  simp only [Nat.add_zero, pow_zero, mul_one] at h0a h0b
  have hP : (2 : ℝ) ^ P ≤ 2 ^ (w - 1 - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hw1 : (2 : ℝ) ^ (w - 1 - 1) * 2 = 2 ^ (w - 1) := by
    rw [← pow_succ]; congr 1; omega
  have key : ∀ (y : ℝ) (n : ℤ), y = (n : ℝ) * gridUnit P → |y| ≤ 1 → FitsTwos w n := by
    intro y n hy hy1
    have hu : (0 : ℝ) < gridUnit P := gridUnit_pos P
    have hn : |(n : ℝ)| ≤ 2 ^ P := by
      have h1 : |(n : ℝ)| * gridUnit P ≤ 1 := by
        rw [← abs_of_pos hu, ← abs_mul, ← hy]; exact hy1
      have h2 : gridUnit P * 2 ^ P = 1 := by rw [gridUnit]; field_simp
      calc |(n : ℝ)| = |(n : ℝ)| * gridUnit P * 2 ^ P := by rw [mul_assoc, h2, mul_one]
        _ ≤ 1 * 2 ^ P := by gcongr
        _ = 2 ^ P := one_mul _
    have hlt : |(n : ℝ)| < 2 ^ (w - 1) := by
      have : (0 : ℝ) < 2 ^ (w - 1 - 1) := by positivity
      linarith
    rw [abs_lt] at hlt
    constructor
    · have : (-(2 ^ (w - 1) : ℤ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : (n : ℝ) < ((2 ^ (w - 1) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  simp only [gridInt, h0a, h0b]
  exact ⟨key _ a ha ((Complex.abs_re_le_norm _).trans hn),
    key _ b hb ((Complex.abs_im_le_norm _).trans hn)⟩

/-- Payload length of a complex record. -/
theorem length_crecBits' (w : ℕ) (cs : List CInt) : (crecBits w cs).length = 2 * w * cs.length := by
  simp only [crecBits, coefBits, twosBits, bitsLE, List.length_flatMap, List.length_append,
    List.length_map, List.length_range]
  rw [List.map_const', List.sum_replicate, smul_eq_mul]
  ring

/-- Stack length of a complex record array. -/
theorem length_carrSyms' (w : ℕ) (v : List (List CInt)) :
    (carrSyms w v).length = (v.map fun cs => 2 * w * cs.length + 1).sum := by
  induction v with
  | nil => simp [carrSyms, arrSyms, blk]
  | cons cs v ih =>
    simp only [carrSyms, arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append,
      List.sum_cons] at ih ⊢
    rw [ih, recSyms, List.length_append, List.length_map, length_crecBits', List.length_singleton]

/-- The stack volume of a cube array is `cvolCube m r W = 2^m·(2rW + 1)`. -/
theorem cvol_encCube {m r : ℕ} (W F : ℕ) (z : RArr (Cube m) r) :
    cvol W (encCube F z) = cvolCube m r W := by
  rw [cvol, length_carrSyms', encCube, encArr, List.map_map]
  simp only [Function.comp_def, List.length_map, List.length_finRange]
  rw [List.map_const', List.sum_replicate, smul_eq_mul, cubeAddrs, List.length_map,
    List.length_range, cvolCube]
  ring

/-! ## Exact rounds -/

/-- **One exact layer round** (Lemma 5.2, `lem:walsh-exact`; `gadget_round`): on a disk array on the `Q`-grid
with `Q + D ≤ P'`, the truncated layer `Q_{P'}(H_Sel y)` equals `H_Sel y`, a disk array on the
`(Q + D)`-grid (`Sel` the slice positions). -/
theorem layer_round {m r : ℕ} {K j₀ D nS ρ : ℕ} (hρ : ρ < K) (hm : j₀ + D * K + nS = m)
    {Q P' : ℕ} (hQ : Q + D ≤ P') {y : RArr (Cube m) r} (hy : ArrOnDiskGrid Q y) :
    truncArr P' (hT (slicePos m K j₀ D ρ) y) = hT (slicePos m K j₀ D ρ) y ∧
      ArrOnDiskGrid (Q + D) (hT (slicePos m K j₀ D ρ) y) := by
  have hcard : (slicePos m K j₀ D ρ).card = D := card_slicePos ⟨ρ, hρ⟩ (by omega)
  have h := arrOnDiskGrid_hT (slicePos m K j₀ D ρ) hy
  rw [hcard] at h
  exact ⟨truncArr_eq_self (fun x k => (h x k).1.mono hQ), h⟩

/-- `CZ` has values `±1`. -/
theorem czSign_unit {m : ℕ} (pairs : List (Fin m × Fin m)) (x : Cube m) :
    czSign pairs x = 1 ∨ czSign pairs x = -1 ∨ czSign pairs x = Complex.I ∨
      czSign pairs x = -Complex.I := by
  unfold czSign
  rcases neg_one_pow_eq_or ℂ (pairs.countP (fun p => x p.1 && x p.2)) with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end SubNLogN.Machine.CnotBatchRed
