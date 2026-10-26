import Contracts.W8
import Contracts.Machine.Common
import IntMulTM.Framework.Lib.Counter

/-!
# WP.W9e.Arith — the arithmetic behind the machine rescale

The POST rescales (`Y`: `pChild → pSub`, output: `pSub → p`) are `gRescale`, which W8 proved to be
a shift (`W8.gRescale_shift`): a left shift by `p_out − p_in`, or the round-half-up right shift
`divRoundPow2 · (p_in − p_out)`. The machine works on sign-magnitude numbers (`intSyms`), so the
right shift is computed from the magnitude `a = |z|` as

* `q = a / 2^(d−1)` and `L = a mod 2^(d−1)` (one W3 `splitAt`),
* magnitude `rtMag z d = q/2 + q%2` if `z ≥ 0` or `L ≠ 0`, else `q/2` (`divRoundPow2_eq`),
* sign of `z`, except that a zero result is `pos` (`intSyms_signed`).

Also: small `natSyms`/`bitLen` facts (as in `WP.W6a.Basic`, re-proved here).
-/

namespace WP.W9e

open IntMul TMFw TMFw.Contracts Computability

/-! ## `natSyms` and `bitLen` -/

theorem natSyms_zero : natSyms 0 = [] := by
  simp [natSyms, encodeNat_zero]

theorem bitLen_zero : bitLen 0 = 0 := by
  simp [bitLen, encodeNat_zero]

theorem natSyms_add_add_one (r : ℕ) : natSyms (r + r + 1) = .bit true :: natSyms r := by
  simp [natSyms, encodeNat_add_add_one]

theorem natSyms_add_self (r : ℕ) (h : r ≠ 0) : natSyms (r + r) = .bit false :: natSyms r := by
  simp only [natSyms]
  rw [encodeNat_add, if_neg (by rw [encodeNat_eq_nil_iff]; exact h)]
  rfl

theorem bitLen_add_add_one (n : ℕ) : bitLen (n + n + 1) = bitLen n + 1 := by
  simp [bitLen, encodeNat_add_add_one]

theorem bitLen_add_self_le (n : ℕ) : bitLen (n + n) ≤ bitLen n + 1 := by
  unfold bitLen
  rw [encodeNat_add]
  split_ifs <;> simp

theorem bitLen_le_of_lt_two_pow {n k : ℕ} (h : n < 2 ^ k) : bitLen n ≤ k := by
  induction k generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    subst hn
    simp [bitLen_zero]
  | succ k ih =>
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [pow_succ] at h
      have h1 := ih (n := j) (by omega)
      have h2 := bitLen_add_self_le j
      rw [two_mul]
      omega
    · rw [pow_succ] at h
      have h1 := ih (n := j) (by omega)
      rw [two_mul, bitLen_add_add_one]
      omega

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n :=
  bitLen_le_of_lt_two_pow (Nat.lt_two_pow_self)

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · by_cases hk : k = 0
      · subst hk
        simp [bitLen_zero]
      · have := ih k (by omega)
        unfold bitLen
        rw [two_mul, encodeNat_add, if_neg (by rw [encodeNat_eq_nil_iff]; exact hk),
          List.length_cons, pow_succ]
        unfold bitLen at this
        omega
    · have := ih k (by omega)
      rw [two_mul, bitLen_add_add_one, pow_succ]
      omega

theorem bitLen_mono {m n : ℕ} (h : m ≤ n) : bitLen m ≤ bitLen n :=
  bitLen_le_of_lt_two_pow (lt_of_le_of_lt h (lt_two_pow_bitLen n))

/-- A nonzero number pops its lowest bit. -/
theorem natSyms_pos (q : ℕ) (hq : 0 < q) :
    natSyms q = .bit (decide (q % 2 = 1)) :: natSyms (q / 2) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' q
  · have hk : k ≠ 0 := by omega
    have h1 : 2 * k % 2 = 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    rw [h1, h2, two_mul, natSyms_add_self k hk]
    rfl
  · have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    rw [h1, h2, two_mul, natSyms_add_add_one]
    rfl

theorem bitLen_div_two_le (q : ℕ) : bitLen (q / 2) ≤ bitLen q := bitLen_mono (Nat.div_le_self _ _)

/-! ## Signed encodings -/

theorem sgnSym_eq_pos {z : ℤ} (h : 0 ≤ z) : sgnSym z = .pos := by
  simp [sgnSym, not_lt.2 h]

theorem sgnSym_eq_neg {z : ℤ} (h : z < 0) : sgnSym z = .neg := by
  simp [sgnSym, h]

/-- The machine's sign fix-up: the sign of `z`, except that `0` is `pos`. -/
theorem intSyms_signed (z : ℤ) (mag : ℕ) :
    intSyms (if z < 0 then -(mag : ℤ) else (mag : ℤ)) =
      (if mag = 0 then Sym.pos else sgnSym z) :: natSyms mag := by
  unfold intSyms
  by_cases hz : z < 0
  · rw [if_pos hz]
    by_cases hm : mag = 0
    · subst hm
      simp [sgnSym]
    · rw [if_neg hm, sgnSym_eq_neg hz, sgnSym_eq_neg (by omega)]
      simp
  · rw [if_neg hz]
    by_cases hm : mag = 0
    · subst hm
      simp [sgnSym]
    · rw [if_neg hm, sgnSym_eq_pos (by omega), sgnSym_eq_pos (by omega)]
      simp

/-- A left shift keeps the sign. -/
theorem intSyms_mul_pow (z : ℤ) (d : ℕ) :
    intSyms (z * ((2 ^ d : ℕ) : ℤ)) = sgnSym z :: natSyms (z.natAbs * 2 ^ d) := by
  have hp : (0 : ℤ) < ((2 ^ d : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos d
  unfold intSyms
  congr 1
  · unfold sgnSym
    by_cases hz : z < 0
    · rw [if_pos hz, if_pos (Int.mul_neg_of_neg_of_pos hz hp)]
    · rw [if_neg hz, if_neg (not_lt.2 (Int.mul_nonneg (not_lt.1 hz) (le_of_lt hp)))]
  · rw [Int.natAbs_mul, Int.natAbs_natCast]

/-! ## The round-half-up right shift -/

theorem ediv_eq_of_bounds {A B Q : ℤ} (hB : 0 < B) (h1 : B * Q ≤ A) (h2 : A < B * Q + B) :
    A / B = Q :=
  ((Int.ediv_emod_unique hB).2 ⟨(by ring : (A - B * Q) + B * Q = A), by linarith,
    by linarith⟩).1

theorem rt_nonneg (P L k b : ℤ) (hP : 0 < P) (hL0 : 0 ≤ L) (hL : L < P) (hb : b = 0 ∨ b = 1) :
    ((2 * k + b) * P + L + P) / (2 * P) = k + b := by
  apply ediv_eq_of_bounds (by linarith)
  · rcases hb with rfl | rfl <;> nlinarith
  · rcases hb with rfl | rfl <;> nlinarith

theorem rt_neg (P L k b : ℤ) (hP : 0 < P) (hL0 : 0 ≤ L) (hL : L < P) (hb : b = 0 ∨ b = 1) :
    (-((2 * k + b) * P + L) + P) / (2 * P) = -(k + if L = 0 then 0 else b) := by
  apply ediv_eq_of_bounds (by linarith)
  · by_cases hL' : L = 0
    · rw [if_pos hL']
      rcases hb with rfl | rfl <;> nlinarith
    · rw [if_neg hL']
      rcases hb with rfl | rfl <;> nlinarith
  · by_cases hL' : L = 0
    · rw [if_pos hL']
      rcases hb with rfl | rfl <;> nlinarith
    · rw [if_neg hL']
      have : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL')
      rcases hb with rfl | rfl <;> nlinarith

/-- Magnitude of `divRoundPow2 z d` (`d ≥ 1`), from `q = |z| / 2^(d−1)` and the dropped low part. -/
def rtMag (z : ℤ) (d : ℕ) : ℕ :=
  if 0 ≤ z ∨ z.natAbs % 2 ^ (d - 1) ≠ 0 then
    z.natAbs / 2 ^ (d - 1) / 2 + z.natAbs / 2 ^ (d - 1) % 2
  else z.natAbs / 2 ^ (d - 1) / 2

/-- **The machine's right shift.** For `d ≥ 1`, `divRoundPow2 z d` has magnitude `rtMag z d` and
the sign of `z`. -/
theorem divRoundPow2_eq (z : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    divRoundPow2 z d = if z < 0 then -((rtMag z d : ℕ) : ℤ) else ((rtMag z d : ℕ) : ℤ) := by
  unfold divRoundPow2
  rw [if_neg (by omega)]
  have hPpos : 0 < 2 ^ (d - 1) := Nat.two_pow_pos _
  have h2d : ((2 ^ d : ℕ) : ℤ) = 2 * ((2 ^ (d - 1) : ℕ) : ℤ) := by
    have : 2 ^ d = 2 * 2 ^ (d - 1) := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    rw [this]
    push_cast
    ring
  rw [h2d]
  have hdm := Nat.div_add_mod z.natAbs (2 ^ (d - 1))
  have hq := Nat.div_add_mod (z.natAbs / 2 ^ (d - 1)) 2
  have hL := Nat.mod_lt z.natAbs hPpos
  have hb : z.natAbs / 2 ^ (d - 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  -- the magnitude as an integer, in the shape of `rt_nonneg` / `rt_neg`
  have ha : (z.natAbs : ℤ) =
      (2 * ((z.natAbs / 2 ^ (d - 1) / 2 : ℕ) : ℤ) + ((z.natAbs / 2 ^ (d - 1) % 2 : ℕ) : ℤ)) *
        ((2 ^ (d - 1) : ℕ) : ℤ) + ((z.natAbs % 2 ^ (d - 1) : ℕ) : ℤ) := by
    have e1 : (z.natAbs : ℤ) = ((2 ^ (d - 1) : ℕ) : ℤ) * ((z.natAbs / 2 ^ (d - 1) : ℕ) : ℤ) +
        ((z.natAbs % 2 ^ (d - 1) : ℕ) : ℤ) := by exact_mod_cast hdm.symm
    have e2 : ((z.natAbs / 2 ^ (d - 1) : ℕ) : ℤ) = 2 * ((z.natAbs / 2 ^ (d - 1) / 2 : ℕ) : ℤ) +
        ((z.natAbs / 2 ^ (d - 1) % 2 : ℕ) : ℤ) := by exact_mod_cast hq.symm
    rw [e1, e2]
    ring
  have hbb : ((z.natAbs / 2 ^ (d - 1) % 2 : ℕ) : ℤ) = 0 ∨
      ((z.natAbs / 2 ^ (d - 1) % 2 : ℕ) : ℤ) = 1 := by omega
  have hPz : (0 : ℤ) < ((2 ^ (d - 1) : ℕ) : ℤ) := by exact_mod_cast hPpos
  have hLz : ((z.natAbs % 2 ^ (d - 1) : ℕ) : ℤ) < ((2 ^ (d - 1) : ℕ) : ℤ) := by exact_mod_cast hL
  have hL0 : (0 : ℤ) ≤ ((z.natAbs % 2 ^ (d - 1) : ℕ) : ℤ) := by positivity
  unfold rtMag
  by_cases hz : z < 0
  · rw [if_pos hz]
    have hzn : z = -(z.natAbs : ℤ) := by omega
    have hnn : ¬ (0 ≤ z) := by omega
    conv_lhs => rw [hzn]
    rw [ha, rt_neg _ _ _ _ hPz hL0 hLz hbb]
    split_ifs <;> omega
  · rw [if_neg hz]
    have hzn : z = (z.natAbs : ℤ) := by omega
    rw [if_pos (Or.inl (by omega))]
    conv_lhs => rw [hzn]
    rw [ha, rt_nonneg _ _ _ _ hPz hL0 hLz hbb]
    push_cast
    ring

theorem rtMag_le (z : ℤ) (d : ℕ) : rtMag z d ≤ z.natAbs := by
  unfold rtMag
  have h1 := Nat.div_le_self z.natAbs (2 ^ (d - 1))
  split_ifs <;> omega

/-! ## The coordinate rescale -/

/-- `gRescale p_in p_out` on one coordinate (`W8.gRescale_shift`). -/
def rscZ (pi po : ℕ) (z : ℤ) : ℤ :=
  if pi ≤ po then z * ((2 ^ (po - pi) : ℕ) : ℤ) else divRoundPow2 z (pi - po)

theorem gRescale_eq_rscZ (pi po : ℕ) (zz : ℤ × ℤ) :
    gRescale pi po zz = (rscZ pi po zz.1, rscZ pi po zz.2) := by
  rw [IntMulTM.Contracts.W8.gRescale_shift]
  unfold rscZ
  split_ifs <;> rfl

#assert_std_axioms natSyms_zero bitLen_zero natSyms_add_add_one natSyms_add_self bitLen_add_add_one
  bitLen_add_self_le bitLen_le_of_lt_two_pow bitLen_le_self lt_two_pow_bitLen bitLen_mono
  natSyms_pos bitLen_div_two_le sgnSym_eq_pos sgnSym_eq_neg intSyms_signed intSyms_mul_pow
  ediv_eq_of_bounds rt_nonneg rt_neg divRoundPow2_eq rtMag_le gRescale_eq_rscZ

end WP.W9e
