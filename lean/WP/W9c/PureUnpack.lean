import Contracts.W9.Pre
import WP.W7k2.Arith

/-!
# WP.W9c.PureUnpack — streamed balanced-digit unpack and the Kronecker pack width (pure)

Pure mathematical lemmas for streamed balanced-digit unpacking. Helper lemmas are `private`, so
importing this module adds only `udStep`, `udig` and the four theorems to `WP.W9c`.

* (A) `unpack_eq_udig`: the snapshot's `unpackSignedKronecker` at half-radix `H = 2^(k-1)` equals the
  streamed digits `udig`. Route: the generalized statement over `(M, c)` with `c ≤ 1`, where one step
  (`udStep_spec`) writes the value as `digit + 2H·rest` with `digit ∈ [-H, H)`; then the snapshot's
  `extractSignedSlot_add_mul` / `shiftSignedSlot_add_mul`.
* (B) `udStep_carry_le`, (C) `udig_natAbs_le`: carry in `{0,1}`, digits of magnitude `≤ 2^(k-1)`.
* (D) `bitLen_pack_le`: `|pack f| ≤ (2^B - 1)(2^(k·|f|) - 1) < 2^(B + k·|f|)`, by induction.
-/

namespace WP.W9c
open IntMul TMFw.Contracts

/-- One streamed balanced digit: magnitude `M` (the rest of |P|), carry `c ∈ {0,1}`, slot width
`k ≥ 1` (radix `2^k`, half `2^(k-1)`). `neg` is the sign of the packed product. -/
def udStep (neg : Bool) (k M c : ℕ) : ℤ × ℕ :=
  let t := M % 2 ^ k + c
  if neg then (if 2 ^ (k - 1) < t then (((2 ^ k - t : ℕ) : ℤ), 1) else (-(t : ℤ), 0))
  else (if 2 ^ (k - 1) ≤ t then ((t : ℤ) - ((2 ^ k : ℕ) : ℤ), 1) else ((t : ℤ), 0))

/-- `n` streamed digits, LSB first. -/
def udig (neg : Bool) (k : ℕ) : ℕ → ℕ → ℕ → List ℤ
  | 0, _, _ => []
  | n + 1, M, c => (udStep neg k M c).1 :: udig neg k n (M / 2 ^ k) (udStep neg k M c).2

private theorem two_pow_succ_pred (k : ℕ) (hk : 1 ≤ k) : 2 ^ k = 2 * 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, Nat.mul_comm]

/-- One step: the digit lies in `[-H, H)` and the value is `digit + 2H·rest`, `H = 2^(k-1)`. -/
private theorem udStep_spec (neg : Bool) (k M c : ℕ) (hk : 1 ≤ k) (hc : c ≤ 1) :
    -((2 ^ (k - 1) : ℕ) : ℤ) ≤ (udStep neg k M c).1 ∧
      (udStep neg k M c).1 < ((2 ^ (k - 1) : ℕ) : ℤ) ∧
      (if neg then -((M + c : ℕ) : ℤ) else ((M + c : ℕ) : ℤ)) =
        (udStep neg k M c).1 + 2 * ((2 ^ (k - 1) : ℕ) : ℤ) *
          (if neg then -((M / 2 ^ k + (udStep neg k M c).2 : ℕ) : ℤ)
            else ((M / 2 ^ k + (udStep neg k M c).2 : ℕ) : ℤ)) := by
  have h2 := two_pow_succ_pred k hk
  have hM := Nat.div_add_mod M (2 ^ k)
  have hr := Nat.mod_lt M (Nat.two_pow_pos k)
  have hh : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  unfold udStep
  dsimp only
  generalize 2 ^ (k - 1) = h at *
  rw [h2] at hM hr ⊢
  generalize M / (2 * h) = q at *
  generalize M % (2 * h) = r at *
  have hMz : (M : ℤ) = 2 * (h : ℤ) * (q : ℤ) + (r : ℤ) := by exact_mod_cast hM.symm
  have hsub : ((2 * h - (r + c) : ℕ) : ℤ) = 2 * (h : ℤ) - ((r : ℤ) + (c : ℤ)) := by omega
  rw [hsub]
  split_ifs <;> refine ⟨by push_cast; omega, by push_cast; omega, ?_⟩ <;> push_cast <;>
    first | linear_combination hMz | linear_combination (-1 : ℤ) * hMz

/-- The generalized unpack: value `±(M + c)` with carry `c ≤ 1`. -/
private theorem unpack_gen (k : ℕ) (hk : 1 ≤ k) (neg : Bool) : ∀ (n M c : ℕ), c ≤ 1 →
    unpackSignedKronecker ((2 ^ (k - 1) : ℕ) : ℤ) n
      (if neg then -((M + c : ℕ) : ℤ) else ((M + c : ℕ) : ℤ)) = udig neg k n M c
  | 0, _, _, _ => rfl
  | n + 1, M, c, hc => by
    obtain ⟨hlo, hhi, hV⟩ := udStep_spec neg k M c hk hc
    have hpos : (0 : ℤ) < ((2 ^ (k - 1) : ℕ) : ℤ) := by
      have := Nat.two_pow_pos (k - 1)
      omega
    have hc' : (udStep neg k M c).2 ≤ 1 := by
      unfold udStep
      dsimp only
      split_ifs <;> simp
    simp only [unpackSignedKronecker, udig]
    rw [hV, extractSignedSlot_add_mul _ _ _ hpos hlo hhi, shiftSignedSlot_add_mul _ _ _ hpos hlo hhi,
      unpack_gen k hk neg n (M / 2 ^ k) (udStep neg k M c).2 hc']

/-- (A) The streamed digits are the snapshot's unpack (radix `2·H`, `H = 2^(k-1)`). -/
theorem unpack_eq_udig (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (P : ℤ) :
    unpackSignedKronecker ((2 ^ (k - 1) : ℕ) : ℤ) n P = udig (decide (P < 0)) k n P.natAbs 0 := by
  have h := unpack_gen k hk (decide (P < 0)) n P.natAbs 0 (Nat.zero_le _)
  have hP : (if decide (P < 0) then -((P.natAbs + 0 : ℕ) : ℤ) else ((P.natAbs + 0 : ℕ) : ℤ)) = P := by
    by_cases hneg : P < 0
    · have h1 := Int.natAbs_of_nonneg (show 0 ≤ -P by omega)
      rw [Int.natAbs_neg] at h1
      simp only [hneg, decide_true, if_true, Nat.add_zero]
      omega
    · have h1 := Int.natAbs_of_nonneg (show 0 ≤ P by omega)
      simp only [hneg, decide_false, Bool.false_eq_true, if_false, Nat.add_zero]
      omega
  rw [hP] at h
  exact h

/-- (B) carry stays in {0,1}. -/
theorem udStep_carry_le (neg : Bool) (k M c : ℕ) (hk : 1 ≤ k) (hc : c ≤ 1) :
    (udStep neg k M c).2 ≤ 1 := by
  have _ := hk
  have _ := hc
  unfold udStep
  dsimp only
  split_ifs <;> simp

/-- (C) every digit has magnitude ≤ 2^(k-1). -/
theorem udig_natAbs_le (neg : Bool) (k : ℕ) (hk : 1 ≤ k) :
    ∀ (n M c : ℕ), c ≤ 1 → ∀ d ∈ udig neg k n M c, d.natAbs ≤ 2 ^ (k - 1)
  | 0, _, _, _ => by simp [udig]
  | n + 1, M, c, hc => by
    intro d hd
    simp only [udig, List.mem_cons] at hd
    rcases hd with rfl | hd
    · obtain ⟨hlo, hhi, -⟩ := udStep_spec neg k M c hk hc
      rcases Int.natAbs_eq (udStep neg k M c).1 with h | h <;> omega
    · exact udig_natAbs_le neg k hk n (M / 2 ^ k) (udStep neg k M c).2
        (udStep_carry_le neg k M c hk hc) d hd

/-- `|pack f| ≤ (2^B - 1)(2^(k·|f|) - 1)` for entries of magnitude `< 2^B`. -/
private theorem pack_abs_le (k B : ℕ) (hk : 1 ≤ k) : ∀ f : List ℤ, (∀ x ∈ f, x.natAbs < 2 ^ B) →
    |packSignedKronecker (((2 ^ k : ℕ) : ℤ)) f| ≤ ((2 : ℤ) ^ B - 1) * ((2 : ℤ) ^ (k * f.length) - 1)
  | [], _ => by simp [packSignedKronecker]
  | c :: f, hf => by
    have hc : c.natAbs < 2 ^ B := hf c (by simp)
    have ih := pack_abs_le k B hk f (fun x hx => hf x (by simp [hx]))
    have hcz : |c| ≤ (2 : ℤ) ^ B - 1 := by
      have h1 : ((c.natAbs : ℕ) : ℤ) < ((2 ^ B : ℕ) : ℤ) := by exact_mod_cast hc
      rw [Int.natCast_natAbs] at h1
      push_cast at h1
      omega
    have hA : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
    have hK : (2 : ℤ) ≤ 2 ^ k := by
      have : (2 : ℤ) ^ 1 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
      simpa using this
    have hcast : (((2 ^ k : ℕ) : ℤ)) = (2 : ℤ) ^ k := by push_cast; ring
    rw [hcast] at ih ⊢
    simp only [packSignedKronecker, List.length_cons]
    rw [show k * (f.length + 1) = k * f.length + k by ring, pow_add]
    calc |c + 2 ^ k * packSignedKronecker (2 ^ k) f|
        ≤ |c| + |2 ^ k * packSignedKronecker (2 ^ k) f| := abs_add_le _ _
      _ = |c| + 2 ^ k * |packSignedKronecker (2 ^ k) f| := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ k)]
      _ ≤ (2 ^ B - 1) + 2 ^ k * ((2 ^ B - 1) * (2 ^ (k * f.length) - 1)) :=
          add_le_add hcz (mul_le_mul_of_nonneg_left ih (by positivity))
      _ ≤ (2 ^ B - 1) * (2 ^ (k * f.length) * 2 ^ k - 1) := by
          have key : (2 ^ B - 1) * (2 ^ (k * f.length) * 2 ^ k - 1) -
              ((2 ^ B - 1) + 2 ^ k * ((2 ^ B - 1) * (2 ^ (k * f.length) - 1))) =
              ((2 : ℤ) ^ B - 1) * (2 ^ k - 2) := by ring
          have hnn : (0 : ℤ) ≤ ((2 : ℤ) ^ B - 1) * (2 ^ k - 2) :=
            mul_nonneg (by linarith) (by linarith)
          linarith

/-- (D) width of a signed Kronecker pack. -/
theorem bitLen_pack_le (k B : ℕ) (hk : 1 ≤ k) (f : List ℤ) (hf : ∀ x ∈ f, bitLen x.natAbs ≤ B) :
    bitLen (packSignedKronecker (((2 ^ k : ℕ) : ℤ)) f).natAbs ≤ B + k * f.length := by
  have hf' : ∀ x ∈ f, x.natAbs < 2 ^ B := fun x hx =>
    (WP.W7k2.bitLen_le_iff B x.natAbs).1 (hf x hx)
  have h := pack_abs_le k B hk f hf'
  apply (WP.W7k2.bitLen_le_iff _ _).2
  have hA : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
  have hG : (1 : ℤ) ≤ 2 ^ (k * f.length) := one_le_pow₀ (by norm_num)
  have hlt : |packSignedKronecker (((2 ^ k : ℕ) : ℤ)) f| < (2 : ℤ) ^ (B + k * f.length) := by
    rw [pow_add]
    have e : ((2 : ℤ) ^ B - 1) * ((2 : ℤ) ^ (k * f.length) - 1) =
        2 ^ B * 2 ^ (k * f.length) - 2 ^ B - 2 ^ (k * f.length) + 1 := by ring
    linarith
  have h2 : ((packSignedKronecker (((2 ^ k : ℕ) : ℤ)) f).natAbs : ℤ) <
      ((2 ^ (B + k * f.length) : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    push_cast
    exact hlt
  exact_mod_cast h2

#assert_std_axioms unpack_eq_udig udStep_carry_le udig_natAbs_le bitLen_pack_le
end WP.W9c
