/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafRowAddValue

/-!
# C-core leaf 9 (Lemma A.9 row addition): call parameters (`CCore/LeafRowAddC7.lean`)

For a row addition `p₁ ← p₁ + p₂` (`p₁ ≠ p₂`; third slot `z = thirdSlot p₁ p₂`) at a node with
`f = m^(k-1)`, the compact role array is a Lemma A.9 (`lem:transfer13`) rectangle (`C7PackedXorStmt`,
`Contracts/AppC.lean`; `C7`/`c7` are earlier-draft names for Lemma A.9, kept for identifier stability)
`[N0] × [2^L] × [N1] × [2^L] × [N2] × [2^L] × [N3]` with `L = fK`. Its three chunk slots are the slot
blocks `j0 + s f, …, j0 + s f + f - 1` for `s ∈ {p₁, p₂, z}`, sorted by position (`lo < mid < hi`).
Name `0 = x` is slot `p₂`, name `1 = y` is slot `p₁`, name `2 = z` is the third slot.

## Proved here (complete proofs)
* `c7Stride_rk`: the stride of the rectangle slot of name `n` is `S · 2^{K(D - (j0 + s f) - f)}`.
* `packedXorAddr_rowAdd`: with `σ = c7Sigma p₁ p₂`, `packedXorAddr (fK) K ρ f N1 N2 N3 σ` is the
  stride-form map `pxa` of `LeafRowAddValue.lean`.
* `c7_shape`: the record count `A'·2^{KD}·S` is `N0·2^L·N1·2^L·N2·2^L·N3`.
-/

namespace SubNLogN.Machine.CCore.LeafRowAddAux

open TMFw TMFw.Contracts SubNLogN.Math.Walsh SubNLogN.Math.Common SubNLogN.Math.Networks
open SubNLogN.Machine

/-- Slot of chunk name `n` (`0 = x = p₂`, `1 = y = p₁`, `2 = z`). -/
def nameSlot (p₁ p₂ : ℕ) (n : Fin 3) : ℕ :=
  if n.val = 0 then p₂ else if n.val = 1 then p₁ else thirdSlot p₁ p₂

/-- Smallest, largest and middle of the three slots. -/
def loS (p₁ p₂ : ℕ) : ℕ := min (min p₁ p₂) (thirdSlot p₁ p₂)
/-- Largest of the three slots. -/
def hiS (p₁ p₂ : ℕ) : ℕ := max (max p₁ p₂) (thirdSlot p₁ p₂)
/-- Middle of the three slots. -/
def midS (p₁ p₂ : ℕ) : ℕ := p₁ + p₂ + thirdSlot p₁ p₂ - loS p₁ p₂ - hiS p₁ p₂

/-- Rectangle position (Lemma A.9 slot, `0` most significant) of chunk name `n`. -/
def rk (p₁ p₂ : ℕ) (n : Fin 3) : Fin 3 :=
  if nameSlot p₁ p₂ n = loS p₁ p₂ then 0 else if nameSlot p₁ p₂ n = hiS p₁ p₂ then 2 else 1

theorem nameSlot_injective {p₁ p₂ : ℕ} (hp : p₁ ≠ p₂) : Function.Injective (nameSlot p₁ p₂) := by
  obtain ⟨h3i, h3j, -⟩ := thirdSlot_ne p₁ p₂
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  unfold nameSlot at h
  apply Fin.ext
  split_ifs at h <;> omega

/-- Facts about the sorted slots. -/
theorem slots_sorted {p₁ p₂ : ℕ} (hp : p₁ ≠ p₂) :
    loS p₁ p₂ < midS p₁ p₂ ∧ midS p₁ p₂ < hiS p₁ p₂ ∧
    (∀ n, nameSlot p₁ p₂ n = loS p₁ p₂ ∨ nameSlot p₁ p₂ n = midS p₁ p₂ ∨
      nameSlot p₁ p₂ n = hiS p₁ p₂) ∧
    hiS p₁ p₂ ≤ max (max p₁ p₂) (thirdSlot p₁ p₂) := by
  obtain ⟨h3i, h3j, -⟩ := thirdSlot_ne p₁ p₂
  refine ⟨?_, ?_, ?_, le_rfl⟩
  · simp only [loS, midS, hiS]; omega
  · simp only [loS, midS, hiS]; omega
  · intro n
    have hn := n.isLt
    unfold nameSlot
    split_ifs <;> simp only [loS, midS, hiS] <;> omega

theorem rk_lo {p₁ p₂ : ℕ} {n : Fin 3} (h : nameSlot p₁ p₂ n = loS p₁ p₂) : rk p₁ p₂ n = 0 := by
  rw [rk, if_pos h]

theorem rk_hi {p₁ p₂ : ℕ} (hp : p₁ ≠ p₂) {n : Fin 3} (h : nameSlot p₁ p₂ n = hiS p₁ p₂) :
    rk p₁ p₂ n = 2 := by
  obtain ⟨hlm, hmh, -, -⟩ := slots_sorted hp
  rw [rk, if_neg (by rw [h]; omega), if_pos h]

theorem rk_mid {p₁ p₂ : ℕ} (hp : p₁ ≠ p₂) {n : Fin 3} (h : nameSlot p₁ p₂ n = midS p₁ p₂) :
    rk p₁ p₂ n = 1 := by
  obtain ⟨hlm, hmh, -, -⟩ := slots_sorted hp
  rw [rk, if_neg (by rw [h]; omega), if_neg (by rw [h]; omega)]

theorem rk_injective {p₁ p₂ : ℕ} (hp : p₁ ≠ p₂) : Function.Injective (rk p₁ p₂) := by
  intro a b h
  apply nameSlot_injective hp
  obtain ⟨hlm, hmh, hn, -⟩ := slots_sorted hp
  rcases hn a with ha | ha | ha <;> rcases hn b with hb | hb | hb
  · rw [ha, hb]
  · rw [rk_lo ha, rk_mid hp hb] at h; exact absurd h (by decide)
  · rw [rk_lo ha, rk_hi hp hb] at h; exact absurd h (by decide)
  · rw [rk_mid hp ha, rk_lo hb] at h; exact absurd h (by decide)
  · rw [ha, hb]
  · rw [rk_mid hp ha, rk_hi hp hb] at h; exact absurd h (by decide)
  · rw [rk_hi hp ha, rk_lo hb] at h; exact absurd h (by decide)
  · rw [rk_hi hp ha, rk_mid hp hb] at h; exact absurd h (by decide)
  · rw [ha, hb]

/-- The chunk-name arrangement of the Lemma A.9 call: slot `j` holds name `c7Sigma p₁ p₂ j`. -/
noncomputable def c7Sigma (p₁ p₂ : ℕ) : Equiv.Perm (Fin 3) :=
  if hp : p₁ ≠ p₂ then
    (Equiv.ofBijective (rk p₁ p₂) (Finite.injective_iff_bijective.mp (rk_injective hp))).symm
  else 1

theorem c7Sigma_symm {p₁ p₂ : ℕ} (hp : p₁ ≠ p₂) (n : Fin 3) :
    (c7Sigma p₁ p₂).symm n = rk p₁ p₂ n := by
  simp only [c7Sigma, dif_pos hp, Equiv.symm_symm, Equiv.ofBijective_apply]

/-- `N1 = 2^{K((j0 + mid f) - (j0 + lo f) - f)}`. -/
def c7N1 (K f j0 p₁ p₂ : ℕ) : ℕ := 2 ^ (K * ((j0 + midS p₁ p₂ * f) - (j0 + loS p₁ p₂ * f) - f))
/-- `N2 = 2^{K((j0 + hi f) - (j0 + mid f) - f)}`. -/
def c7N2 (K f j0 p₁ p₂ : ℕ) : ℕ := 2 ^ (K * ((j0 + hiS p₁ p₂ * f) - (j0 + midS p₁ p₂ * f) - f))
/-- `N3 = S·2^{K(D - (j0 + hi f) - f)}`. -/
def c7N3 (K D S f j0 p₁ p₂ : ℕ) : ℕ := S * 2 ^ (K * (D - (j0 + hiS p₁ p₂ * f) - f))
/-- `N0 = A'·2^{K(j0 + lo f)}` (implied by the length). -/
def c7N0 (A K f j0 p₁ p₂ : ℕ) : ℕ := A * 2 ^ (K * (j0 + loS p₁ p₂ * f))


/-- Chunk arithmetic: consecutive sorted slot blocks do not overlap. -/
theorem slot_gap {f a b : ℕ} (hab : a < b) (j0 : ℕ) : j0 + a * f + f ≤ j0 + b * f := by
  have := Nat.mul_le_mul_right f (Nat.succ_le_of_lt hab)
  rw [Nat.succ_mul] at this
  omega

theorem pow_mul_pow_eq {K a b c : ℕ} (h : a + b = c) : 2 ^ (K * a) * 2 ^ (K * b) = 2 ^ (K * c) := by
  rw [← pow_add, ← Nat.mul_add, h]

/-- **Strides of the Lemma A.9 rectangle.** The rectangle slot of name `n` has stride
`S·2^{K(D - (j0 + s f) - f)}`, `s = nameSlot p₁ p₂ n`. -/
theorem c7Stride_rk {K D S f j0 p₁ p₂ : ℕ} (hp : p₁ ≠ p₂)
    (hfit : j0 + hiS p₁ p₂ * f + f ≤ D) (n : Fin 3) :
    c7Stride (f * K) (c7N1 K f j0 p₁ p₂) (c7N2 K f j0 p₁ p₂) (c7N3 K D S f j0 p₁ p₂)
        (rk p₁ p₂ n) = S * 2 ^ (K * (D - (j0 + nameSlot p₁ p₂ n * f) - f)) := by
  obtain ⟨hlm, hmh, hn, -⟩ := slots_sorted hp
  have g1 := slot_gap (f := f) hlm j0
  have g2 := slot_gap (f := f) hmh j0
  have hfK : 2 ^ (f * K) = 2 ^ (K * f) := by rw [Nat.mul_comm]
  by_cases h0 : nameSlot p₁ p₂ n = loS p₁ p₂
  · rw [rk_lo h0, h0]
    simp only [c7Stride, c7N1, c7N2, c7N3, Fin.isValue, Fin.val_zero, if_true, hfK]
    calc S * 2 ^ (K * (D - (j0 + hiS p₁ p₂ * f) - f)) * 2 ^ (K * f) *
          2 ^ (K * (j0 + hiS p₁ p₂ * f - (j0 + midS p₁ p₂ * f) - f)) * 2 ^ (K * f) *
          2 ^ (K * (j0 + midS p₁ p₂ * f - (j0 + loS p₁ p₂ * f) - f))
        = S * (2 ^ (K * (D - (j0 + hiS p₁ p₂ * f) - f)) * 2 ^ (K * f) *
          2 ^ (K * (j0 + hiS p₁ p₂ * f - (j0 + midS p₁ p₂ * f) - f)) * 2 ^ (K * f) *
          2 ^ (K * (j0 + midS p₁ p₂ * f - (j0 + loS p₁ p₂ * f) - f))) := by ring
      _ = S * 2 ^ (K * (D - (j0 + loS p₁ p₂ * f) - f)) := by
        rw [pow_mul_pow_eq rfl, pow_mul_pow_eq rfl, pow_mul_pow_eq rfl, pow_mul_pow_eq]
        omega
  · by_cases h2 : nameSlot p₁ p₂ n = hiS p₁ p₂
    · rw [rk_hi hp h2, h2]
      simp [c7Stride, c7N3]
    · have hm : nameSlot p₁ p₂ n = midS p₁ p₂ := by
        rcases hn n with h | h | h
        · exact absurd h h0
        · exact h
        · exact absurd h h2
      rw [rk_mid hp hm, hm]
      simp only [c7Stride, c7N2, c7N3, Fin.isValue, Fin.val_one, one_ne_zero, if_false, if_true,
        hfK]
      calc S * 2 ^ (K * (D - (j0 + hiS p₁ p₂ * f) - f)) * 2 ^ (K * f) *
            2 ^ (K * (j0 + hiS p₁ p₂ * f - (j0 + midS p₁ p₂ * f) - f))
          = S * (2 ^ (K * (D - (j0 + hiS p₁ p₂ * f) - f)) * 2 ^ (K * f) *
            2 ^ (K * (j0 + hiS p₁ p₂ * f - (j0 + midS p₁ p₂ * f) - f))) := by ring
        _ = S * 2 ^ (K * (D - (j0 + midS p₁ p₂ * f) - f)) := by
          rw [pow_mul_pow_eq rfl, pow_mul_pow_eq]
          omega

/-- **The Lemma A.9 address map of the call is the stride-form map.** -/
theorem packedXorAddr_rowAdd {K D S f j0 ρ p₁ p₂ : ℕ} (hp : p₁ ≠ p₂)
    (hfit : j0 + hiS p₁ p₂ * f + f ≤ D) :
    packedXorAddr (f * K) K ρ f (c7N1 K f j0 p₁ p₂) (c7N2 K f j0 p₁ p₂)
        (c7N3 K D S f j0 p₁ p₂) (c7Sigma p₁ p₂) =
      pxa (f * K) K ρ f (S * 2 ^ (K * (D - (j0 + p₂ * f) - f)))
        (S * 2 ^ (K * (D - (j0 + p₁ * f) - f))) := by
  apply packedXorAddr_eq_pxa
  · rw [c7Sigma_symm hp, c7Stride_rk hp hfit]; rfl
  · rw [c7Sigma_symm hp, c7Stride_rk hp hfit]; rfl

/-- **Shape of the Lemma A.9 rectangle.** -/
theorem c7_shape {A K D S f j0 p₁ p₂ : ℕ} (hp : p₁ ≠ p₂)
    (hfit : j0 + hiS p₁ p₂ * f + f ≤ D) :
    A * 2 ^ (K * D) * S = c7N0 A K f j0 p₁ p₂ * 2 ^ (f * K) * c7N1 K f j0 p₁ p₂ * 2 ^ (f * K) *
      c7N2 K f j0 p₁ p₂ * 2 ^ (f * K) * c7N3 K D S f j0 p₁ p₂ := by
  obtain ⟨hlm, hmh, -, -⟩ := slots_sorted hp
  have g1 := slot_gap (f := f) hlm j0
  have g2 := slot_gap (f := f) hmh j0
  have hfK : 2 ^ (f * K) = 2 ^ (K * f) := by rw [Nat.mul_comm]
  simp only [c7N0, c7N1, c7N2, c7N3, hfK]
  calc A * 2 ^ (K * D) * S = A * S * 2 ^ (K * D) := by ring
    _ = A * S * (2 ^ (K * (j0 + loS p₁ p₂ * f)) * 2 ^ (K * f) *
          2 ^ (K * (j0 + midS p₁ p₂ * f - (j0 + loS p₁ p₂ * f) - f)) * 2 ^ (K * f) *
          2 ^ (K * (j0 + hiS p₁ p₂ * f - (j0 + midS p₁ p₂ * f) - f)) * 2 ^ (K * f) *
          2 ^ (K * (D - (j0 + hiS p₁ p₂ * f) - f))) := by
        rw [pow_mul_pow_eq rfl, pow_mul_pow_eq rfl, pow_mul_pow_eq rfl, pow_mul_pow_eq rfl,
          pow_mul_pow_eq rfl, pow_mul_pow_eq]
        omega
    _ = _ := by ring

end SubNLogN.Machine.CCore.LeafRowAddAux
