/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.LiftPure
import SubNLogN.Machine.Contracts.Arith

/-!
# `SubNLogN.Machine.Walsh.CnotScanBits`: bit-level arithmetic of the CNOT-batch scans (pure)

Paper: Lemma 5.1 (`lem:walsh-select`, the gadget's scalar
`2^s [2(1-i)]^{q_sel}`, "a fourth-root phase, at most one multiplication by `1 - i` and one binary
shift"), eqs. (`eq:walsh-SU`) and (`eq:walsh-CZ`) (the diagonals `S_U`, `CZ`), and Proposition 5.5 (`×2^s`).

**Scope (honest summary).** Pure lemmas, all proved (no `sorry`). Every scan multiplies each
coefficient `n = (a, b)` of a record by a Gaussian integer `2^e · i^k · (1 - i)^μ`; on `W`-bit
two's-complement fields this is computed field by field:
* `LForm` (`LForm.bitFn`, `LForm.val`) and `sgnFn`: linear forms `L ∈ {a, b, a + b, a - b, b - a}`
  and sign `σ = ±1` for the parts `σ·L(a, b)` of `i^k (1-i)^μ (a + bi)` (`gfacZ`, `fieldSpec`, `cmulC_gfacZ` in `Walsh/CnotScanEngine.lean`);
* `rip2`: a two-stage ripple (`L` by a linear bit function of `K1/Twos.lean`, then an optional
  negation); `rip2_twosBits`: on `twosBits W a`, `twosBits W b` it gives `twosBits W (σ·L(a, b))`;
* `twosBits_shift`: `twosBits W (v·2^e) = replicate e' false ++ (twosBits W v).take (W - e')`,
  `e' = min e W` (a pure bit identity, no guard);
* `rip2_take`: the ripple of a prefix is the prefix of the ripple.
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.K1

/-! ## Linear bit functions -/

/-- Copy the first operand. -/
def copyABit (a _b c : Bool) : Bool × Bool := (a, c)

/-- Copy the second operand. -/
def copyBBit (_a b c : Bool) : Bool × Bool := (b, c)

/-- `b - a` (full subtractor with swapped operands). -/
def subBABit (a b c : Bool) : Bool × Bool := subBit b a c

/-- The identity second stage. -/
def idBit (a _b c : Bool) : Bool × Bool := (a, c)

theorem linBit_copyA : LinBit copyABit 1 0 0 := by
  intro a b c; cases a <;> cases b <;> cases c <;> simp [copyABit]

theorem linBit_copyB : LinBit copyBBit 0 1 0 := by
  intro a b c; cases a <;> cases b <;> cases c <;> simp [copyBBit]

theorem linBit_subBA : LinBit subBABit (-1) 1 (-1) := by
  intro a b c; cases a <;> cases b <;> cases c <;> simp [subBABit, subBit]

theorem linBit_id : LinBit idBit 1 0 0 := by
  intro a b c; cases a <;> cases b <;> cases c <;> simp [idBit]

/-- The five linear forms of a scan field. -/
inductive LForm : Type
  | a | b | apb | amb | bma
  deriving DecidableEq

/-- The stage-1 bit function of a linear form. -/
def LForm.bitFn : LForm → Bool → Bool → Bool → Bool × Bool
  | .a => copyABit
  | .b => copyBBit
  | .apb => addBit
  | .amb => subBit
  | .bma => subBABit

/-- The value of a linear form. -/
def LForm.val : LForm → ℤ → ℤ → ℤ
  | .a, x, _ => x
  | .b, _, y => y
  | .apb, x, y => x + y
  | .amb, x, y => x - y
  | .bma, x, y => y - x

theorem LForm.ripOut (L : LForm) (W : ℕ) (x y : ℤ) :
    K1.ripOut L.bitFn false (twosBits W x) (twosBits W y) = twosBits W (L.val x y) := by
  cases L
  · rw [show LForm.bitFn .a = copyABit from rfl, ripOut_twosBits linBit_copyA]; simp [LForm.val]
  · rw [show LForm.bitFn .b = copyBBit from rfl, ripOut_twosBits linBit_copyB]; simp [LForm.val]
  · exact ripOut_add W x y
  · exact ripOut_sub W x y
  · rw [show LForm.bitFn .bma = subBABit from rfl, ripOut_twosBits linBit_subBA]
    congr 1; simp [LForm.val]; ring

/-- The stage-2 bit function: identity (`σ = +1`) or negation (`σ = -1`). -/
def sgnFn (neg : Bool) : Bool → Bool → Bool → Bool × Bool := if neg then negBit else idBit

theorem ripOut_sgn (neg : Bool) (W : ℕ) (t : ℤ) :
    K1.ripOut (sgnFn neg) false (twosBits W t) (twosBits W t) =
      twosBits W (if neg then -t else t) := by
  cases neg
  · simp only [sgnFn, Bool.false_eq_true, if_false]
    rw [ripOut_twosBits linBit_id]
    simp
  · simp only [sgnFn, if_true]
    exact ripOut_neg W t t

/-! ## The two-stage ripple -/

/-- Two-stage ripple: stage 1 `f1` on `(a_i, b_i)` with carry `c1`, then stage 2 `f2` on the
stage-1 bit with carry `c2`. -/
def rip2 (f1 f2 : Bool → Bool → Bool → Bool × Bool) :
    Bool → Bool → List Bool → List Bool → List Bool
  | c1, c2, x :: xs, y :: ys =>
    (f2 (f1 x y c1).1 (f1 x y c1).1 c2).1 ::
      rip2 f1 f2 (f1 x y c1).2 (f2 (f1 x y c1).1 (f1 x y c1).1 c2).2 xs ys
  | _, _, _, _ => []

theorem rip2_eq (f1 f2 : Bool → Bool → Bool → Bool × Bool) :
    ∀ (c1 c2 : Bool) (xs ys : List Bool),
      rip2 f1 f2 c1 c2 xs ys = K1.ripOut f2 c2 (K1.ripOut f1 c1 xs ys) (K1.ripOut f1 c1 xs ys)
  | _, _, [], _ => rfl
  | _, _, _ :: _, [] => rfl
  | c1, c2, x :: xs, y :: ys => by
    simp only [rip2, ripOut_cons]
    rw [rip2_eq f1 f2 _ _ xs ys]

theorem rip2_take (f1 f2 : Bool → Bool → Bool → Bool × Bool) :
    ∀ (n : ℕ) (c1 c2 : Bool) (xs ys : List Bool),
      rip2 f1 f2 c1 c2 (xs.take n) (ys.take n) = (rip2 f1 f2 c1 c2 xs ys).take n
  | 0, _, _, _, _ => by simp [rip2]
  | n + 1, _, _, [], _ => by simp [rip2]
  | n + 1, _, _, _ :: _, [] => by simp [rip2]
  | n + 1, c1, c2, x :: xs, y :: ys => by
    simp only [List.take_succ_cons, rip2, List.take_succ_cons]
    rw [rip2_take f1 f2 n]

theorem length_rip2 (f1 f2 : Bool → Bool → Bool → Bool × Bool) :
    ∀ (c1 c2 : Bool) (xs ys : List Bool), xs.length = ys.length →
      (rip2 f1 f2 c1 c2 xs ys).length = xs.length
  | _, _, [], _, _ => rfl
  | _, _, _ :: _, [], h => by simp at h
  | c1, c2, x :: xs, y :: ys, h => by
    simp only [rip2, List.length_cons]
    rw [length_rip2 f1 f2 _ _ xs ys (by simpa using h)]

/-- **The two-stage ripple on two's-complement fields**: `twosBits W (σ·L(x, y))`. -/
theorem rip2_twosBits (L : LForm) (neg : Bool) (W : ℕ) (x y : ℤ) :
    rip2 L.bitFn (sgnFn neg) false false (twosBits W x) (twosBits W y) =
      twosBits W (if neg then -L.val x y else L.val x y) := by
  rw [rip2_eq, L.ripOut, ripOut_sgn]

/-! ## Shifts -/

theorem twosBits_take (n k : ℕ) (z : ℤ) : (twosBits (n + k) z).take n = twosBits n z := by
  simp only [twosBits, bitsLE]
  rw [← List.map_take, List.take_range, Nat.min_eq_left (by omega)]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have h1 : (z % 2 ^ (n + k)).toNat.testBit i = (z % 2 ^ n).toNat.testBit i := by
    have hA : (0 : ℤ) ≤ z % 2 ^ (n + k) := Int.emod_nonneg _ (by positivity)
    have hB : (0 : ℤ) ≤ z % 2 ^ n := Int.emod_nonneg _ (by positivity)
    have hmod : (z % 2 ^ (n + k)).toNat % 2 ^ n = (z % 2 ^ n).toNat := by
      have h := Int.emod_emod_of_dvd z (pow_dvd_pow (2 : ℤ) (Nat.le_add_right n k))
      zify [hA, hB]
      rw [Int.toNat_of_nonneg hA, Int.toNat_of_nonneg hB]
      rw [h]
    rw [← hmod, Nat.testBit_mod_two_pow]
    simp [hi]
  exact h1

/-- **Exact binary shift of a field** (no guard): the bits of `v·2^e` are `e' = min e W` zeros,
then the first `W - e'` bits of `v`. -/
theorem twosBits_shift (W e : ℕ) (v : ℤ) :
    twosBits W (v * 2 ^ e) =
      List.replicate (min e W) false ++ (twosBits W v).take (W - min e W) := by
  by_cases h : e ≤ W
  · rw [Nat.min_eq_left h]
    obtain ⟨n, rfl⟩ : ∃ n, W = n + e := ⟨W - e, by omega⟩
    rw [WalshLift.twosBits_mul_two_pow n v e, show n + e - e = n by omega, twosBits_take]
  · push_neg at h
    rw [Nat.min_eq_right h.le, Nat.sub_self, List.take_zero, List.append_nil]
    have hz : (v * 2 ^ e) % 2 ^ W = 0 := by
      have : (2 : ℤ) ^ W ∣ v * 2 ^ e :=
        Dvd.dvd.mul_left (pow_dvd_pow 2 h.le) v
      exact Int.emod_eq_zero_of_dvd this
    simp only [twosBits, bitsLE, hz, Int.toNat_zero, Nat.zero_testBit]
    simp

end SubNLogN.Machine.WalshScanAux
