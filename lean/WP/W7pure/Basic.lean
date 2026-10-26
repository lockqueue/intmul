import Contracts.W7.Schedule
import IntMulTM.SpecFacts

/-!
# WP.W7pure.Basic — `bitLen` and list-length helpers for the W7 pure obligations

Shared by `WP.W7pure.TapeSize`, `WP.W7pure.EntryWidths` and `WP.W7pure.TapeBound`:
* `bitLen = Nat.size` (spec fact `IntMulTM.length_encodeNat`), hence `n < 2^w → bitLen n ≤ w` and
  `bitLen n ≤ n`;
* conversions from the snapshot's width predicates (`FitsSignedScalarWord`, `0 ≤ x ≤ 2^m`) and from
  W6b's reciprocal `⌊2^H / d⌋` (`d > 0`) to `bitLen` bounds;
* lengths of flattened maps (`length_flatten_map_le`), of headers (`length_header_le`) and of the leaf
  stage sum `Σ_{s<K} (2^(s+1)·c + 1) ≤ 2^(K+1)·c + K - 2c` (`length_stages_le`).
-/

namespace WP.W7pure

open TMFw.Contracts

/-! ## `bitLen` -/

/-- `bitLen` is `Nat.size`. -/
theorem bitLen_eq_size (n : ℕ) : bitLen n = Nat.size n :=
  IntMulTM.length_encodeNat n

theorem bitLen_le_of_lt {n w : ℕ} (h : n < 2 ^ w) : bitLen n ≤ w := by
  rw [bitLen_eq_size]
  exact Nat.size_le.2 h

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n :=
  bitLen_le_of_lt Nat.lt_two_pow_self

theorem bitLen_le_of_le_two_pow {n m : ℕ} (h : n ≤ 2 ^ m) : bitLen n ≤ m + 1 :=
  bitLen_le_of_lt (lt_of_le_of_lt h (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self m)))

/-- A snapshot signed word of width `w` (`|z| < 2^(w-1)`) has a magnitude of at most `w` bits. -/
theorem bitLen_natAbs_le_of_fits {w : ℕ} {z : ℤ} (h : IntMul.FitsSignedScalarWord w z) :
    bitLen z.natAbs ≤ w := by
  unfold IntMul.FitsSignedScalarWord at h
  rw [Int.abs_eq_natAbs] at h
  have h1 : z.natAbs < 2 ^ (w - 1) := by exact_mod_cast h
  exact bitLen_le_of_lt (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (Nat.sub_le w 1)))

/-- `0 ≤ x ≤ 2^m` gives `bitLen |x| ≤ m + 1`. -/
theorem bitLen_natAbs_le_of_nonneg_le {x : ℤ} {m : ℕ} (h0 : 0 ≤ x) (h1 : x ≤ (2 : ℤ) ^ m) :
    bitLen x.natAbs ≤ m + 1 := by
  apply bitLen_le_of_le_two_pow
  have h2 : ((x.natAbs : ℕ) : ℤ) ≤ ((2 ^ m : ℕ) : ℤ) := by
    rw [Int.natAbs_of_nonneg h0]
    push_cast
    exact h1
  exact_mod_cast h2

/-- W6b's per-column reciprocal `μ = ⌊2^H / d⌋` with `d > 0` satisfies `0 ≤ μ ≤ 2^H`, so it has at
most `H + 1` bits. -/
theorem bitLen_colRecip_le (H r u2 : ℕ) (a c : ℤ)
    (hd : 0 < IntMulTM.Contracts.W8.columnDivisor r u2 a c) :
    bitLen (W7.colRecip H r u2 a c).natAbs ≤ H + 1 := by
  unfold W7.colRecip
  have hN : (0 : ℤ) ≤ ((2 ^ H : ℕ) : ℤ) := by positivity
  have h0 : 0 ≤ ((2 ^ H : ℕ) : ℤ) / IntMulTM.Contracts.W8.columnDivisor r u2 a c :=
    Int.ediv_nonneg hN hd.le
  have h1 : ((2 ^ H : ℕ) : ℤ) / IntMulTM.Contracts.W8.columnDivisor r u2 a c ≤ ((2 ^ H : ℕ) : ℤ) :=
    Int.ediv_le_self _ hN
  apply bitLen_le_of_le_two_pow
  have h2 : (((((2 ^ H : ℕ) : ℤ) / IntMulTM.Contracts.W8.columnDivisor r u2 a c).natAbs : ℕ) : ℤ) ≤
      ((2 ^ H : ℕ) : ℤ) := by
    rw [Int.natAbs_of_nonneg h0]
    exact h1
  exact_mod_cast h2

/-! ## Lengths of lists -/

/-- A termwise length bound for a flattened map. -/
theorem length_flatten_map_le {α β : Type} (l : List α) (f : α → List β) (c : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ c) : (l.map f).flatten.length ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

/-- The same over `List.range n`. -/
theorem length_flatten_map_range_le {β : Type} (n : ℕ) (f : ℕ → List β) (c : ℕ)
    (h : ∀ i < n, (f i).length ≤ c) : ((List.range n).map f).flatten.length ≤ n * c := by
  have h1 := length_flatten_map_le (List.range n) f c (fun i hi => h i (List.mem_range.1 hi))
  rw [List.length_range] at h1
  exact h1

/-- One header field costs `bitLen v + 1` symbols. -/
theorem length_header_cons (v : ℕ) (fs : List ℕ) :
    (W7.header (v :: fs)).length = bitLen v + 1 + (W7.header fs).length := by
  simp only [W7.header, W7.field, List.map_cons, List.flatten_cons, List.length_append,
    length_natSyms, List.length_singleton]
  omega

/-- A header is at most `Σ fields + #fields + 1` symbols long (`bitLen v ≤ v`). -/
theorem length_header_le (fs : List ℕ) : (W7.header fs).length ≤ fs.sum + fs.length + 1 := by
  induction fs with
  | nil => simp [W7.header]
  | cons v fs ih =>
    rw [length_header_cons]
    have h1 := bitLen_le_self v
    simp only [List.sum_cons, List.length_cons]
    omega

/-- **Leaf stage sum.** If stage `s < K` has length at most `2^(s+1)·c + 1`, the `K` stages together
have length at most `2^(K+1)·c + K - 2c` (stated without subtraction). -/
theorem length_stages_le {β : Type} (K c : ℕ) (f : ℕ → List β)
    (h : ∀ s < K, (f s).length ≤ 2 ^ (s + 1) * c + 1) :
    ((List.range K).map f).flatten.length + 2 * c ≤ 2 ^ (K + 1) * c + K := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h1 := ih (fun s hs => h s (by omega))
    have h2 := h K (by omega)
    have hr : List.range (K + 1) = List.range K ++ [K] := List.range_succ
    rw [hr, List.map_append, List.flatten_append, List.length_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    have e : 2 ^ (K + 1 + 1) * c = 2 ^ (K + 1) * c + 2 ^ (K + 1) * c := by ring
    omega

#assert_std_axioms bitLen_eq_size bitLen_le_of_lt bitLen_le_self bitLen_le_of_le_two_pow
  bitLen_natAbs_le_of_fits bitLen_natAbs_le_of_nonneg_le bitLen_colRecip_le length_flatten_map_le
  length_flatten_map_range_le length_header_cons length_header_le length_stages_le

end WP.W7pure
