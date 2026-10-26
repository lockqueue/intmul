import Contracts.Machine.W3
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# WP.W5.Arith — bit lengths and the pure Toom-3 algebra (no machine)

* `bitLen` facts: `bitLen_le_iff : bitLen n ≤ m ↔ n < 2^m` and its corollaries (sums, products,
  shifts, quotients), plus the LSB-first decomposition `encodeNat_pos`.
* `toomVal A B k`: the value the machine's Toom-3 step computes from `A = |a|`, `B = |b|` and the
  split position `k`, written with exactly the machine's operations (parts by `%`/`/`, Bodrato
  evaluation at `0, 1, -1, -2, ∞`, interpolation with exact `/3`, `/2`, `/2`, Horner recomposition
  through `natAbs` and `2^k` shifts). `toomVal_eq : toomVal A B k = A * B` for **every** `k`.
* `sgnFix a b v`: the sign correction; `sgnFix_natAbs_mul : sgnFix a b (|a|·|b|) = a·b`.
* Size facts for the recursion measure: every evaluation point has bit length `≤ k + 3` when the
  parts are below `2^k` (`evals_bitLen`, `part_lt2`).
-/

namespace WP.W5

open TMFw TMFw.Contracts Computability

/-! ## Bit lengths -/

theorem bitLen_zero : bitLen 0 = 0 := by simp [bitLen, encodeNat_zero]

/-- LSB-first decomposition of a positive number. -/
theorem encodeNat_pos (n : ℕ) (hn : 0 < n) :
    encodeNat n = decide (n % 2 = 1) :: encodeNat (n / 2) := by
  obtain ⟨q, h | h⟩ := Nat.even_or_odd' n
  · subst h
    have hq : 0 < q := by omega
    have hne : encodeNat q ≠ [] := by rw [Ne, encodeNat_eq_nil_iff]; omega
    have h2 : 2 * q / 2 = q := by omega
    rw [two_mul, encodeNat_add, if_neg hne, ← two_mul, h2]
    simp
  · subst h
    have h1 : (2 * q + 1) % 2 = 1 := by omega
    have h2 : (2 * q + 1) / 2 = q := by omega
    rw [two_mul, encodeNat_add_add_one, ← two_mul, h2, h1]
    simp

theorem bitLen_pos (n : ℕ) (hn : 0 < n) : bitLen n = bitLen (n / 2) + 1 := by
  simp only [bitLen, encodeNat_pos n hn, List.length_cons]

theorem bitLen_le_iff : ∀ (m n : ℕ), bitLen n ≤ m ↔ n < 2 ^ m := by
  intro m
  induction m with
  | zero =>
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [bitLen_zero]
    · rw [bitLen_pos n hn, pow_zero]
      constructor <;> intro h <;> omega
  | succ m ih =>
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [bitLen_zero]
    · rw [bitLen_pos n hn, Nat.add_le_add_iff_right, ih, pow_succ]
      omega

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := (bitLen_le_iff _ n).1 le_rfl

theorem bitLen_le_of_lt {n m : ℕ} (h : n < 2 ^ m) : bitLen n ≤ m := (bitLen_le_iff m n).2 h

theorem bitLen_mono {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b :=
  bitLen_le_of_lt (lt_of_le_of_lt h (lt_two_pow_bitLen b))

theorem bitLen_add_le (a b : ℕ) : bitLen (a + b) ≤ max (bitLen a) (bitLen b) + 1 := by
  apply bitLen_le_of_lt
  have ha := lt_two_pow_bitLen a
  have hb := lt_two_pow_bitLen b
  have h1 : 2 ^ bitLen a ≤ 2 ^ max (bitLen a) (bitLen b) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have h2 : 2 ^ bitLen b ≤ 2 ^ max (bitLen a) (bitLen b) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  rw [pow_succ]
  omega

theorem bitLen_mul_le (a b : ℕ) : bitLen (a * b) ≤ bitLen a + bitLen b := by
  apply bitLen_le_of_lt
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_le (lt_two_pow_bitLen a) (le_of_lt (lt_two_pow_bitLen b))
    (Nat.two_pow_pos _)

theorem bitLen_mul_pow_le (a c : ℕ) : bitLen (a * 2 ^ c) ≤ bitLen a + c := by
  apply bitLen_le_of_lt
  rw [pow_add]
  exact Nat.mul_lt_mul_of_pos_right (lt_two_pow_bitLen a) (Nat.two_pow_pos _)

theorem bitLen_div_le (a d : ℕ) : bitLen (a / d) ≤ bitLen a := bitLen_mono (Nat.div_le_self a d)

theorem bitLen_mod_le (a d : ℕ) : bitLen (a % d) ≤ bitLen a := bitLen_mono (Nat.mod_le a d)

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := bitLen_le_of_lt Nat.lt_two_pow_self

/-- `n / 8^i = 0` iff the bit length is at most `3i`. -/
theorem div_pow8_eq_zero_iff (n i : ℕ) : n / 8 ^ i = 0 ↔ bitLen n ≤ 3 * i := by
  rw [bitLen_le_iff, Nat.div_eq_zero_iff_lt (Nat.pos_of_ne_zero (by positivity)), pow_mul]
  norm_num

/-! ### Integers -/

theorem bitLen_natAbs_add_le (a b : ℤ) :
    bitLen (a + b).natAbs ≤ max (bitLen a.natAbs) (bitLen b.natAbs) + 1 :=
  le_trans (bitLen_mono (Int.natAbs_add_le a b)) (bitLen_add_le _ _)

theorem bitLen_natAbs_sub_le (a b : ℤ) :
    bitLen (a - b).natAbs ≤ max (bitLen a.natAbs) (bitLen b.natAbs) + 1 :=
  le_trans (bitLen_mono (Int.natAbs_sub_le a b)) (bitLen_add_le _ _)

theorem bitLen_natAbs_mul_le (a b : ℤ) :
    bitLen (a * b).natAbs ≤ bitLen a.natAbs + bitLen b.natAbs := by
  rw [Int.natAbs_mul]
  exact bitLen_mul_le _ _

theorem bitLen_natAbs_neg (a : ℤ) : bitLen (-a).natAbs = bitLen a.natAbs := by
  rw [Int.natAbs_neg]

/-- Bit length of a `SmallOp` result (divisions exact). -/
theorem bitLen_smallOp_le (op : SmallOp) (z : ℤ) (h : op.ok z) :
    bitLen (op.apply z).natAbs ≤ bitLen z.natAbs + 2 := by
  cases op with
  | mul2 =>
    show bitLen (2 * z).natAbs ≤ _
    have e : (2 * z).natAbs = 2 * z.natAbs := by rw [Int.natAbs_mul]; rfl
    rw [e]
    apply bitLen_le_of_lt
    have := lt_two_pow_bitLen z.natAbs
    have h4 : 2 ^ (bitLen z.natAbs + 2) = 2 ^ bitLen z.natAbs * 4 := by rw [pow_add]; norm_num
    rw [h4]
    omega
  | mul3 =>
    show bitLen (3 * z).natAbs ≤ _
    have e : (3 * z).natAbs = 3 * z.natAbs := by rw [Int.natAbs_mul]; rfl
    rw [e]
    apply bitLen_le_of_lt
    have := lt_two_pow_bitLen z.natAbs
    have h4 : 2 ^ (bitLen z.natAbs + 2) = 2 ^ bitLen z.natAbs * 4 := by rw [pow_add]; norm_num
    rw [h4]
    omega
  | div2 =>
    show bitLen (z / 2).natAbs ≤ _
    have h2 : (2 : ℤ) ∣ z := h
    rw [Int.natAbs_ediv_of_dvd h2]
    exact le_trans (bitLen_div_le _ _) (by omega)
  | div3 =>
    show bitLen (z / 3).natAbs ≤ _
    have h3 : (3 : ℤ) ∣ z := h
    rw [Int.natAbs_ediv_of_dvd h3]
    exact le_trans (bitLen_div_le _ _) (by omega)

/-! ## Sign correction -/

/-- Negate `v` iff exactly one of `a`, `b` is negative. -/
def sgnFix (a b v : ℤ) : ℤ := if decide (a < 0) = decide (b < 0) then v else -v

theorem sgnFix_natAbs_mul (a b : ℤ) :
    sgnFix a b ((a.natAbs : ℤ) * (b.natAbs : ℤ)) = a * b := by
  unfold sgnFix
  rcases lt_or_ge a 0 with ha | ha <;> rcases lt_or_ge b 0 with hb | hb
  · rw [if_pos (by simp [ha, hb]), Int.ofNat_natAbs_of_nonpos ha.le,
      Int.ofNat_natAbs_of_nonpos hb.le]
    ring
  · have hb' : ¬ b < 0 := not_lt.2 hb
    rw [if_neg (by simp [ha, hb']), Int.ofNat_natAbs_of_nonpos ha.le, Int.natAbs_of_nonneg hb]
    ring
  · have ha' : ¬ a < 0 := not_lt.2 ha
    rw [if_neg (by simp [ha', hb]), Int.natAbs_of_nonneg ha, Int.ofNat_natAbs_of_nonpos hb.le]
    ring
  · have ha' : ¬ a < 0 := not_lt.2 ha
    have hb' : ¬ b < 0 := not_lt.2 hb
    rw [if_pos (by simp [ha', hb']), Int.natAbs_of_nonneg ha, Int.natAbs_of_nonneg hb]

/-! ## The Toom-3 value -/

/-- Parts of `A` at split position `k`: low, middle, high. -/
def part0 (A k : ℕ) : ℤ := ((A % 2 ^ k : ℕ) : ℤ)
/-- Middle part. -/
def part1 (A k : ℕ) : ℤ := ((A / 2 ^ k % 2 ^ k : ℕ) : ℤ)
/-- High part. -/
def part2 (A k : ℕ) : ℤ := ((A / 2 ^ k / 2 ^ k : ℕ) : ℤ)

/-- Evaluation at `1`, in the machine's operation order. -/
def ev1 (x0 x1 x2 : ℤ) : ℤ := (x0 + x2) + x1
/-- Evaluation at `-1`. -/
def evm1 (x0 x1 x2 : ℤ) : ℤ := (x0 + x2) - x1
/-- Evaluation at `-2`. -/
def evm2 (x0 x1 x2 : ℤ) : ℤ := SmallOp.apply .mul2 (((x0 + x2) - x1) + x2) - x0

/-- Interpolation and recomposition from the five point products, in the machine's order. -/
def recomp (k : ℕ) (r0 r1 rm1 rm2 rinf : ℤ) : ℤ :=
  let r3 := SmallOp.apply .div3 (rm2 - r1)
  let r1' := SmallOp.apply .div2 (r1 - rm1)
  let r2 := rm1 - r0
  let h := SmallOp.apply .div2 (r2 - r3)
  let t := SmallOp.apply .mul2 rinf
  let r3' := h + t
  let u := r2 + r1'
  let r2' := u - rinf
  let r1'' := r1' - r3'
  let acc1 := ((rinf.natAbs * 2 ^ k : ℕ) : ℤ) + r3'
  let acc2 := ((acc1.natAbs * 2 ^ k : ℕ) : ℤ) + r2'
  let acc3 := ((acc2.natAbs * 2 ^ k : ℕ) : ℤ) + r1''
  ((acc3.natAbs * 2 ^ k : ℕ) : ℤ) + r0

/-- **The machine's Toom-3 value** for magnitudes `A`, `B` and split position `k`. -/
def toomVal (A B k : ℕ) : ℤ :=
  recomp k (part0 A k * part0 B k)
    (ev1 (part0 A k) (part1 A k) (part2 A k) * ev1 (part0 B k) (part1 B k) (part2 B k))
    (evm1 (part0 A k) (part1 A k) (part2 A k) * evm1 (part0 B k) (part1 B k) (part2 B k))
    (evm2 (part0 A k) (part1 A k) (part2 A k) * evm2 (part0 B k) (part1 B k) (part2 B k))
    (part2 A k * part2 B k)

/-- `recomp` in closed form, from the three interpolation identities and nonnegativity. -/
theorem recomp_val (k : ℕ) (r0 r1 rm1 rm2 rinf c1 c2 c3 : ℤ)
    (e3 : rm2 - r1 = 3 * (-c1 + c2 - 3 * c3 + 5 * rinf))
    (e2 : r1 - rm1 = 2 * (c1 + c3))
    (er2 : rm1 - r0 = -c1 + c2 - c3 + rinf)
    (n4 : 0 ≤ rinf) (n3 : 0 ≤ c3) (n2 : 0 ≤ c2) (n1 : 0 ≤ c1) :
    recomp k r0 r1 rm1 rm2 rinf = (((rinf * 2 ^ k + c3) * 2 ^ k + c2) * 2 ^ k + c1) * 2 ^ k + r0 := by
  simp only [recomp]
  have q3 : SmallOp.apply .div3 (rm2 - r1) = -c1 + c2 - 3 * c3 + 5 * rinf := by
    show (rm2 - r1) / 3 = _
    rw [e3, Int.mul_ediv_cancel_left _ (by norm_num)]
  have q1 : SmallOp.apply .div2 (r1 - rm1) = c1 + c3 := by
    show (r1 - rm1) / 2 = _
    rw [e2, Int.mul_ediv_cancel_left _ (by norm_num)]
  rw [q3, q1]
  have qh : SmallOp.apply .div2 (rm1 - r0 - (-c1 + c2 - 3 * c3 + 5 * rinf)) = c3 - 2 * rinf := by
    show (rm1 - r0 - _) / 2 = _
    rw [er2, show -c1 + c2 - c3 + rinf - (-c1 + c2 - 3 * c3 + 5 * rinf) = 2 * (c3 - 2 * rinf) by
      ring, Int.mul_ediv_cancel_left _ (by norm_num)]
  have ht : SmallOp.apply .mul2 rinf = 2 * rinf := rfl
  rw [qh, ht]
  have e1 : c3 - 2 * rinf + 2 * rinf = c3 := by ring
  have e2' : rm1 - r0 + (c1 + c3) - rinf = c2 := by rw [er2]; ring
  have e3' : c1 + c3 - c3 = c1 := by ring
  rw [e1, e2', e3']
  have hP : (0 : ℤ) ≤ 2 ^ k := by positivity
  have hcast : ∀ z : ℤ, 0 ≤ z → (((z.natAbs * 2 ^ k : ℕ) : ℤ)) = z * 2 ^ k := by
    intro z hz
    push_cast
    rw [abs_of_nonneg hz]
  have h1 : 0 ≤ rinf * 2 ^ k + c3 := add_nonneg (mul_nonneg n4 hP) n3
  have h2 : 0 ≤ (rinf * 2 ^ k + c3) * 2 ^ k + c2 := add_nonneg (mul_nonneg h1 hP) n2
  have h3 : 0 ≤ ((rinf * 2 ^ k + c3) * 2 ^ k + c2) * 2 ^ k + c1 := add_nonneg (mul_nonneg h2 hP) n1
  rw [hcast rinf n4, hcast _ h1, hcast _ h2, hcast _ h3]

/-- **Toom-3 correctness** (pure): for nonnegative parts, `recomp` returns the product of the two
recomposed polynomials at `2^k`. -/
theorem recomp_eq (k : ℕ) (a0 a1 a2 b0 b1 b2 : ℤ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) :
    recomp k (a0 * b0) (ev1 a0 a1 a2 * ev1 b0 b1 b2) (evm1 a0 a1 a2 * evm1 b0 b1 b2)
      (evm2 a0 a1 a2 * evm2 b0 b1 b2) (a2 * b2) =
      (a0 + a1 * 2 ^ k + a2 * (2 ^ k * 2 ^ k)) * (b0 + b1 * 2 ^ k + b2 * (2 ^ k * 2 ^ k)) := by
  rw [recomp_val k _ _ _ _ _ (a0 * b1 + a1 * b0) (a0 * b2 + a1 * b1 + a2 * b0) (a1 * b2 + a2 * b1)
    (by simp only [evm2, ev1, SmallOp.apply]; ring) (by simp only [evm1, ev1]; ring)
    (by simp only [evm1]; ring) (mul_nonneg ha2 hb2)
    (add_nonneg (mul_nonneg ha1 hb2) (mul_nonneg ha2 hb1))
    (add_nonneg (add_nonneg (mul_nonneg ha0 hb2) (mul_nonneg ha1 hb1)) (mul_nonneg ha2 hb0))
    (add_nonneg (mul_nonneg ha0 hb1) (mul_nonneg ha1 hb0))]
  ring

theorem part_nonneg0 (A k : ℕ) : 0 ≤ part0 A k := Int.natCast_nonneg _
theorem part_nonneg1 (A k : ℕ) : 0 ≤ part1 A k := Int.natCast_nonneg _
theorem part_nonneg2 (A k : ℕ) : 0 ≤ part2 A k := Int.natCast_nonneg _

theorem parts_recompose (A k : ℕ) :
    part0 A k + part1 A k * 2 ^ k + part2 A k * (2 ^ k * 2 ^ k) = (A : ℤ) := by
  have h1 := Nat.mod_add_div A (2 ^ k)
  have h2 := Nat.mod_add_div (A / 2 ^ k) (2 ^ k)
  have e : A = A % 2 ^ k + 2 ^ k * (A / 2 ^ k % 2 ^ k + 2 ^ k * (A / 2 ^ k / 2 ^ k)) := by
    rw [h2, h1]
  have e' : (A : ℤ) = ((A % 2 ^ k : ℕ) : ℤ) + 2 ^ k * (((A / 2 ^ k % 2 ^ k : ℕ) : ℤ) +
      2 ^ k * ((A / 2 ^ k / 2 ^ k : ℕ) : ℤ)) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) e
    rw [this]
    push_cast
    ring
  simp only [part0, part1, part2]
  rw [e']
  ring

/-- **`toomVal` is the product**, for every split position `k`. -/
theorem toomVal_eq (A B k : ℕ) : toomVal A B k = (A : ℤ) * (B : ℤ) := by
  unfold toomVal
  rw [recomp_eq k _ _ _ _ _ _ (part_nonneg0 A k) (part_nonneg1 A k) (part_nonneg2 A k)
    (part_nonneg0 B k) (part_nonneg1 B k) (part_nonneg2 B k), parts_recompose, parts_recompose]

/-- The three interpolation obligations (exact `/3`, `/2`, `/2`), for any integer parts. -/
theorem interp_dvd (a0 a1 a2 b0 b1 b2 : ℤ) :
    (3 : ℤ) ∣ (evm2 a0 a1 a2 * evm2 b0 b1 b2 - ev1 a0 a1 a2 * ev1 b0 b1 b2) ∧
    (2 : ℤ) ∣ (ev1 a0 a1 a2 * ev1 b0 b1 b2 - evm1 a0 a1 a2 * evm1 b0 b1 b2) ∧
    (2 : ℤ) ∣ ((evm1 a0 a1 a2 * evm1 b0 b1 b2 - a0 * b0) -
      SmallOp.apply .div3 (evm2 a0 a1 a2 * evm2 b0 b1 b2 - ev1 a0 a1 a2 * ev1 b0 b1 b2)) := by
  have e3 : evm2 a0 a1 a2 * evm2 b0 b1 b2 - ev1 a0 a1 a2 * ev1 b0 b1 b2 =
      3 * (-(a0 * b1 + a1 * b0) + (a0 * b2 + a1 * b1 + a2 * b0) - 3 * (a1 * b2 + a2 * b1) +
        5 * (a2 * b2)) := by
    simp only [evm2, ev1, SmallOp.apply]; ring
  have e2 : ev1 a0 a1 a2 * ev1 b0 b1 b2 - evm1 a0 a1 a2 * evm1 b0 b1 b2 =
      2 * ((a0 * b1 + a1 * b0) + (a1 * b2 + a2 * b1)) := by
    simp only [evm1, ev1]; ring
  refine ⟨⟨_, e3⟩, ⟨_, e2⟩, ?_⟩
  have hq : SmallOp.apply .div3 (evm2 a0 a1 a2 * evm2 b0 b1 b2 - ev1 a0 a1 a2 * ev1 b0 b1 b2) =
      -(a0 * b1 + a1 * b0) + (a0 * b2 + a1 * b1 + a2 * b0) - 3 * (a1 * b2 + a2 * b1) +
        5 * (a2 * b2) := by
    show (_ - _) / 3 = _
    rw [e3, Int.mul_ediv_cancel_left _ (by norm_num)]
  rw [hq]
  refine ⟨(a1 * b2 + a2 * b1) - 2 * (a2 * b2), ?_⟩
  simp only [evm1]
  ring

/-! ## Sizes of the evaluation points -/

theorem part_lt0 (A k : ℕ) : (part0 A k).natAbs < 2 ^ k := by
  simp only [part0, Int.natAbs_natCast]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem part_lt1 (A k : ℕ) : (part1 A k).natAbs < 2 ^ k := by
  simp only [part1, Int.natAbs_natCast]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem part_lt2 (A k : ℕ) (hA : A < 2 ^ (3 * k)) : (part2 A k).natAbs < 2 ^ k := by
  simp only [part2, Int.natAbs_natCast]
  rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity)]
  calc A < 2 ^ (3 * k) := hA
    _ = 2 ^ k * (2 ^ k * 2 ^ k) := by
      rw [show 3 * k = k + (k + k) by ring, pow_add, pow_add]

/-- **Evaluation points are small**: with parts below `2^k`, every point value has bit length
`≤ k + 3`. -/
theorem evals_bitLen (x0 x1 x2 : ℤ) (k : ℕ) (h0 : 0 ≤ x0) (h1 : 0 ≤ x1) (h2 : 0 ≤ x2)
    (l0 : x0.natAbs < 2 ^ k) (l1 : x1.natAbs < 2 ^ k) (l2 : x2.natAbs < 2 ^ k) :
    bitLen x0.natAbs ≤ k + 3 ∧ bitLen (ev1 x0 x1 x2).natAbs ≤ k + 3 ∧
      bitLen (evm1 x0 x1 x2).natAbs ≤ k + 3 ∧ bitLen (evm2 x0 x1 x2).natAbs ≤ k + 3 ∧
      bitLen x2.natAbs ≤ k + 3 := by
  have l0' : x0 < 2 ^ k := lt_of_le_of_lt Int.le_natAbs (by exact_mod_cast l0)
  have l1' : x1 < 2 ^ k := lt_of_le_of_lt Int.le_natAbs (by exact_mod_cast l1)
  have l2' : x2 < 2 ^ k := lt_of_le_of_lt Int.le_natAbs (by exact_mod_cast l2)
  have key : ∀ z : ℤ, -(8 * 2 ^ k) < z → z < 8 * 2 ^ k → bitLen z.natAbs ≤ k + 3 := by
    intro z hl hu
    apply bitLen_le_of_lt
    have hz : (z.natAbs : ℤ) < 8 * 2 ^ k := by
      rcases le_or_gt 0 z with hz | hz
      · rw [Int.natAbs_of_nonneg hz]; exact hu
      · rw [Int.ofNat_natAbs_of_nonpos hz.le]; linarith
    have h8 : (2 : ℤ) ^ (k + 3) = 8 * 2 ^ k := by rw [pow_add]; ring
    have h8' : ((2 ^ (k + 3) : ℕ) : ℤ) = 8 * 2 ^ k := by push_cast; rw [h8]
    have hz' : (z.natAbs : ℤ) < ((2 ^ (k + 3) : ℕ) : ℤ) := by rw [h8']; exact hz
    exact_mod_cast hz'
  have hpos : (0 : ℤ) < 2 ^ k := by positivity
  refine ⟨key _ (by linarith) (by linarith), key _ ?_ ?_, key _ ?_ ?_, key _ ?_ ?_,
    key _ (by linarith) (by linarith)⟩ <;>
    simp only [ev1, evm1, evm2, SmallOp.apply] <;> linarith

#assert_std_axioms bitLen_le_iff bitLen_add_le bitLen_mul_le bitLen_mul_pow_le bitLen_smallOp_le
  encodeNat_pos div_pow8_eq_zero_iff sgnFix_natAbs_mul toomVal_eq interp_dvd evals_bitLen part_lt2

end WP.W5
