import IntMulTM.Framework.Bits
import IntMulTM.Framework.AxiomGuard
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# WP.W7k1.IsqrtSpec — digit-by-digit (restoring) integer square root on bit lists

The functional model of the `W7_isqrt` machine kernel. Bit lists are LSB first (`bitsVal`).

* `subBits r t br`: bit-serial subtraction `r − t − br` over the bits of `r` (missing bits of `t`
  are `0`): the difference bits and the final borrow (`subBits_spec`).
* `sqStep b1 b0 (R, Q)`: one digit step. Bring in the bit pair (`R := 4R + 2b1 + b0`), then
  subtract `T = 4Q + 1` if that does not borrow: `Q := 2Q + 1`; otherwise keep `R` and
  `Q := 2Q`.
* `sqRun xs st`: the digit steps over an MSB-first list, two bits at a time.
* `padMSB a`: the MSB-first bits of `a`, padded with one high zero to even length.

Main theorem `sqRun_padMSB`: `(sqRun (padMSB a) ([], [])).2 = encodeNat (Nat.sqrt a)`.
The invariant `SqInv` (`sqStep_inv`, `sqRun_inv`) also gives the lengths the cost proof needs.
-/

namespace WP.W7k1

open TMFw Computability

/-! ## Bit-list facts -/

theorem toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

theorem bitsVal_lt : ∀ l : List Bool, bitsVal l < 2 ^ l.length
  | [] => by simp
  | b :: l => by
    have := bitsVal_lt l
    have := toNat_le_one b
    simp only [bitsVal_cons, List.length_cons, pow_succ]
    omega

theorem bitsVal_append : ∀ l m : List Bool, bitsVal (l ++ m) = bitsVal l + 2 ^ l.length * bitsVal m
  | [], m => by simp
  | b :: l, m => by
    simp only [List.cons_append, bitsVal_cons, bitsVal_append l m, List.length_cons, pow_succ]
    ring

theorem bitsVal_headD_tail (ts : List Bool) :
    bitsVal ts = bitsVal ts.tail + bitsVal ts.tail + (ts.headD false).toNat := by
  cases ts <;> rfl

theorem length_encodeNat_le : ∀ (j n : ℕ), n < 2 ^ j → (encodeNat n).length ≤ j
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this
    simp [encodeNat_zero]
  | j + 1, n, h => by
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [two_mul, encodeNat_add]
      split_ifs
      · simp
      · have := length_encodeNat_le j k (by rw [pow_succ] at h; omega)
        simp only [List.length_cons]
        omega
    · have := length_encodeNat_le j k (by rw [pow_succ] at h; omega)
      rw [two_mul, encodeNat_add_add_one, List.length_cons]
      omega

/-- The MSB of a positive number's encoding is `1`. -/
theorem encodeNat_reverse_head : ∀ n : ℕ, 0 < n → ∃ l, (encodeNat n).reverse = true :: l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · have hk : 0 < k := by omega
      have hne : encodeNat k ≠ [] := fun h => by
        rw [encodeNat_eq_nil_iff] at h
        omega
      obtain ⟨l, hl⟩ := ih k (by omega) hk
      rw [two_mul, encodeNat_add, if_neg hne, List.reverse_cons, hl]
      exact ⟨l ++ [false], rfl⟩
    · rw [two_mul, encodeNat_add_add_one, List.reverse_cons]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact ⟨[], by rw [encodeNat_zero]; rfl⟩
      · obtain ⟨l, hl⟩ := ih k (by omega) hk
        rw [hl]
        exact ⟨l ++ [true], rfl⟩

/-! ## Bit-serial subtraction -/

/-- Difference bit of `r − t − br`. -/
def dBit (r t br : Bool) : Bool := xor (xor r t) br

/-- Borrow out of `r − t − br`. -/
def bOut (r t br : Bool) : Bool := (!r && t) || (!r && br) || (t && br)

theorem dBit_bOut (r t br : Bool) :
    (dBit r t br).toNat + t.toNat + br.toNat = r.toNat + 2 * (bOut r t br).toNat := by
  cases r <;> cases t <;> cases br <;> rfl

/-- Bit-serial subtraction `r − t − br`, LSB first, over the bits of `r`; missing bits of `t` are
`0`. Returns the difference bits and the final borrow. -/
def subBits : List Bool → List Bool → Bool → List Bool × Bool
  | [], _, br => ([], br)
  | r :: rs, ts, br =>
    (dBit r (ts.headD false) br :: (subBits rs ts.tail (bOut r (ts.headD false) br)).1,
      (subBits rs ts.tail (bOut r (ts.headD false) br)).2)

theorem length_subBits : ∀ (rs ts : List Bool) (br : Bool),
    (subBits rs ts br).1.length = rs.length
  | [], _, _ => rfl
  | r :: rs, ts, br => by
    simp only [subBits, List.length_cons, length_subBits rs]

theorem subBits_spec : ∀ (rs ts : List Bool) (br : Bool), ts.length ≤ rs.length →
    bitsVal (subBits rs ts br).1 + bitsVal ts + br.toNat =
      bitsVal rs + 2 ^ rs.length * (subBits rs ts br).2.toNat
  | [], ts, br, h => by
    have : ts = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
    subst this
    simp [subBits]
  | r :: rs, ts, br, h => by
    have h' : ts.tail.length ≤ rs.length := by
      rw [List.length_tail]
      simp only [List.length_cons] at h
      omega
    have ih := subBits_spec rs ts.tail (bOut r (ts.headD false) br) h'
    have hb := dBit_bOut r (ts.headD false) br
    simp only [subBits, bitsVal_cons, List.length_cons]
    rw [bitsVal_headD_tail ts, pow_succ', Nat.mul_assoc]
    generalize 2 ^ rs.length * (subBits rs ts.tail (bOut r (ts.headD false) br)).2.toNat = PB
      at ih ⊢
    omega

/-! ## Digit steps -/

/-- One digit step of the restoring square root. State `(R, Q)` = remainder and root bits. -/
def sqStep (b1 b0 : Bool) (st : List Bool × List Bool) : List Bool × List Bool :=
  if (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).2 then
    (b0 :: b1 :: st.1, false :: st.2)
  else
    ((subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).1, true :: st.2)

/-- The digit steps over an MSB-first bit list, two bits at a time. -/
def sqRun : List Bool → List Bool × List Bool → List Bool × List Bool
  | b1 :: b0 :: rest, st => sqRun rest (sqStep b1 b0 st)
  | _, st => st

/-- Invariant after `j` digit steps over a prefix of value `v`. -/
def SqInv (v j : ℕ) (st : List Bool × List Bool) : Prop :=
  st.2 = encodeNat (Nat.sqrt v) ∧ bitsVal st.1 = v - Nat.sqrt v * Nat.sqrt v ∧
    st.1.length = 2 * j ∧ v < 4 ^ j

theorem sqInv_zero : SqInv 0 0 ([], []) :=
  ⟨by simp [encodeNat_zero], by simp, rfl, by simp⟩

/-- The arithmetic of one digit step. -/
theorem sqrt_step_math (v p : ℕ) (hp : p < 4) :
    (4 * Nat.sqrt v + 1 ≤ 4 * (v - Nat.sqrt v * Nat.sqrt v) + p →
      Nat.sqrt (4 * v + p) = 2 * Nat.sqrt v + 1) ∧
    (4 * (v - Nat.sqrt v * Nat.sqrt v) + p < 4 * Nat.sqrt v + 1 →
      Nat.sqrt (4 * v + p) = 2 * Nat.sqrt v) := by
  have h1 := Nat.sqrt_le v
  have h2 := Nat.succ_le_succ_sqrt v
  generalize Nat.sqrt v = q at h1 h2 ⊢
  have e1 : (2 * q + 1) * (2 * q + 1) = 4 * (q * q) + 4 * q + 1 := by ring
  have e2 : (2 * q + 1 + 1) * (2 * q + 1 + 1) = 4 * (q * q) + 8 * q + 4 := by ring
  have e3 : 2 * q * (2 * q) = 4 * (q * q) := by ring
  have e4 : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by ring
  rw [e4] at h2
  constructor
  · intro h
    symm
    rw [Nat.eq_sqrt, e1, e2]
    omega
  · intro h
    symm
    rw [Nat.eq_sqrt, e3, e1]
    omega

/-- The subtrahend `4q + 1` fits: `|T| ≤ |R|` at every step. -/
theorem sqInv_len (v j : ℕ) (st : List Bool × List Bool) (h : SqInv v j st) :
    st.2.length ≤ j := by
  obtain ⟨hQ, -, -, hv⟩ := h
  rw [hQ]
  apply length_encodeNat_le
  have h1 := Nat.sqrt_le v
  generalize Nat.sqrt v = q at h1 ⊢
  rw [show (4 : ℕ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num] at hv
  by_contra hq
  have hq' : 2 ^ j ≤ q := Nat.not_lt.mp hq
  have := Nat.mul_le_mul hq' hq'
  omega

theorem sqStep_inv (v j : ℕ) (st : List Bool × List Bool) (b1 b0 : Bool) (h : SqInv v j st)
    (hpos : 0 < 4 * v + (2 * b1.toNat + b0.toNat)) :
    SqInv (4 * v + (2 * b1.toNat + b0.toNat)) (j + 1) (sqStep b1 b0 st) := by
  have hTj := sqInv_len v j st h
  obtain ⟨hQ, hR, hlen, hv⟩ := h
  have hb1 := toNat_le_one b1
  have hb0 := toNat_le_one b0
  have hmath := sqrt_step_math v (2 * b1.toNat + b0.toNat) (by omega)
  have h1 := Nat.sqrt_le v
  have hRv : bitsVal (b0 :: b1 :: st.1) = 4 * bitsVal st.1 + (2 * b1.toNat + b0.toNat) := by
    simp only [bitsVal_cons]
    omega
  have hTv : bitsVal (true :: false :: st.2) = 4 * Nat.sqrt v + 1 := by
    simp only [bitsVal_cons, hQ, bitsVal_encodeNat, Bool.toNat_true, Bool.toNat_false]
    omega
  have hTlen : (true :: false :: st.2).length ≤ (b0 :: b1 :: st.1).length := by
    simp only [List.length_cons]
    omega
  have hspec := subBits_spec _ _ false hTlen
  have hDlen := length_subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false
  have hDlt := bitsVal_lt (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).1
  rw [hDlen] at hDlt
  rw [hRv, hTv] at hspec
  simp only [List.length_cons, hlen] at hDlt hspec
  have hv4 : 4 * v + (2 * b1.toNat + b0.toNat) < 4 ^ (j + 1) := by
    rw [pow_succ]
    omega
  unfold sqStep
  split_ifs with hbo
  · -- borrow: keep `R`, append a `0` root bit
    rw [hbo] at hspec
    simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.add_zero] at hspec
    have hlt : 4 * (v - Nat.sqrt v * Nat.sqrt v) + (2 * b1.toNat + b0.toNat) <
        4 * Nat.sqrt v + 1 := by
      rw [← hR]
      omega
    have hsq := hmath.2 hlt
    have hq0 : Nat.sqrt v ≠ 0 := by
      intro h0
      rw [h0] at hlt
      have : v = 0 := by
        have := Nat.sqrt_eq_zero.mp h0
        exact this
      subst this
      omega
    have hne : encodeNat (Nat.sqrt v) ≠ [] := fun h => hq0 ((encodeNat_eq_nil_iff _).mp h)
    refine ⟨?_, ?_, ?_, hv4⟩
    · show false :: st.2 = _
      rw [hsq, two_mul, encodeNat_add, if_neg hne, hQ]
    · show bitsVal (b0 :: b1 :: st.1) = _
      rw [hRv, hsq, hR]
      have e : 2 * Nat.sqrt v * (2 * Nat.sqrt v) = 4 * (Nat.sqrt v * Nat.sqrt v) := by ring
      rw [e]
      omega
    · show (b0 :: b1 :: st.1).length = _
      simp only [List.length_cons, hlen]
      omega
  · -- no borrow: take the difference, append a `1` root bit
    have hbo' : (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).2 = false := by
      simpa using hbo
    rw [hbo'] at hspec
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hspec
    have hge : 4 * Nat.sqrt v + 1 ≤ 4 * (v - Nat.sqrt v * Nat.sqrt v) +
        (2 * b1.toNat + b0.toNat) := by
      rw [← hR]
      omega
    have hsq := hmath.1 hge
    refine ⟨?_, ?_, ?_, hv4⟩
    · show true :: st.2 = _
      rw [hsq, two_mul, encodeNat_add_add_one, hQ]
    · show bitsVal (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).1 = _
      rw [hsq]
      have e : (2 * Nat.sqrt v + 1) * (2 * Nat.sqrt v + 1) =
          4 * (Nat.sqrt v * Nat.sqrt v) + 4 * Nat.sqrt v + 1 := by ring
      rw [e]
      rw [hR] at hspec
      omega
    · show (subBits (b0 :: b1 :: st.1) (true :: false :: st.2) false).1.length = _
      rw [length_subBits]
      simp only [List.length_cons, hlen]
      omega

theorem sqRun_inv : ∀ (xs : List Bool) (v j : ℕ) (st : List Bool × List Bool),
    SqInv v j st → xs.length % 2 = 0 →
    (∀ b1 b0 rest, xs = b1 :: b0 :: rest → 0 < 4 * v + (2 * b1.toNat + b0.toNat)) →
    SqInv (v * 4 ^ (xs.length / 2) + bitsVal xs.reverse) (j + xs.length / 2) (sqRun xs st)
  | [], v, j, st, h, _, _ => by simpa [sqRun] using h
  | [_], _, _, _, _, hl, _ => by simp at hl
  | b1 :: b0 :: rest, v, j, st, h, hl, hpos => by
    have hl' : rest.length % 2 = 0 := by
      simp only [List.length_cons] at hl
      omega
    have hv' := hpos b1 b0 rest rfl
    have h1 := sqStep_inv v j st b1 b0 h hv'
    have ih := sqRun_inv rest _ (j + 1) _ h1 hl' (fun b1' b0' rest' _ => by omega)
    have hidx : j + (b1 :: b0 :: rest).length / 2 = j + 1 + rest.length / 2 := by
      simp only [List.length_cons]
      omega
    have hval : v * 4 ^ ((b1 :: b0 :: rest).length / 2) + bitsVal (b1 :: b0 :: rest).reverse =
        (4 * v + (2 * b1.toNat + b0.toNat)) * 4 ^ (rest.length / 2) + bitsVal rest.reverse := by
      obtain ⟨k, hk⟩ : ∃ k, rest.length = 2 * k := ⟨rest.length / 2, by omega⟩
      have e1 : (b1 :: b0 :: rest).length / 2 = k + 1 := by
        simp only [List.length_cons]
        omega
      have e2 : rest.length / 2 = k := by omega
      have e3 : (b1 :: b0 :: rest).reverse = rest.reverse ++ [b0, b1] := by simp
      rw [e1, e2, e3, bitsVal_append, List.length_reverse, hk, pow_mul]
      simp only [bitsVal_cons, bitsVal_nil]
      norm_num
      ring
    rw [hidx, hval]
    exact ih

/-! ## The square root of a number -/

/-- MSB-first bits of `a`, padded with one high zero to even length. -/
def padMSB (a : ℕ) : List Bool :=
  if (encodeNat a).length % 2 = 0 then (encodeNat a).reverse else false :: (encodeNat a).reverse

theorem padMSB_length_even (a : ℕ) : (padMSB a).length % 2 = 0 := by
  unfold padMSB
  split_ifs with h
  · rw [List.length_reverse]
    exact h
  · rw [List.length_cons, List.length_reverse]
    omega

theorem padMSB_length (a : ℕ) : (padMSB a).length ≤ (encodeNat a).length + 1 := by
  unfold padMSB
  split_ifs <;> simp

theorem bitsVal_padMSB (a : ℕ) : bitsVal (padMSB a).reverse = a := by
  unfold padMSB
  split_ifs
  · rw [List.reverse_reverse, bitsVal_encodeNat]
  · rw [List.reverse_cons, List.reverse_reverse, bitsVal_append, bitsVal_encodeNat]
    simp

theorem padMSB_pos (a : ℕ) :
    ∀ b1 b0 rest, padMSB a = b1 :: b0 :: rest → 0 < 4 * 0 + (2 * b1.toNat + b0.toNat) := by
  intro b1 b0 rest h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [padMSB, encodeNat_zero] at h
  · obtain ⟨l, hl⟩ := encodeNat_reverse_head a ha
    unfold padMSB at h
    rw [hl] at h
    split_ifs at h
    · cases h
      simp
    · obtain ⟨-, rfl, -⟩ : b1 = false ∧ b0 = true ∧ rest = l := by
        simp only [List.cons.injEq] at h
        exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
      simp

/-- **The digit steps compute `Nat.sqrt`** (canonically encoded). -/
theorem sqRun_padMSB_inv (a : ℕ) :
    SqInv a ((padMSB a).length / 2) (sqRun (padMSB a) ([], [])) := by
  have h := sqRun_inv (padMSB a) 0 0 ([], []) sqInv_zero (padMSB_length_even a) (padMSB_pos a)
  rw [bitsVal_padMSB, Nat.zero_mul, Nat.zero_add, Nat.zero_add] at h
  exact h

theorem sqRun_padMSB (a : ℕ) : (sqRun (padMSB a) ([], [])).2 = encodeNat (Nat.sqrt a) :=
  (sqRun_padMSB_inv a).1

#assert_std_axioms bitsVal_lt bitsVal_append length_encodeNat_le encodeNat_reverse_head
  subBits_spec length_subBits sqrt_step_math sqInv_len sqStep_inv sqRun_inv padMSB_length_even
  padMSB_length bitsVal_padMSB padMSB_pos sqRun_padMSB_inv sqRun_padMSB

end WP.W7k1
