/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostPass2
import SubNLogN.Machine.K1.Twos

/-!
# K5-PP scan math (`Bridge/PrePostScanMath.lean`): what the two passes compute

**Scope (honest summary).** Pure lemmas, no programs, no `sorry`:
* `twosBits_eq_map'`: the bits of a field are `zb z k` (two's-complement bit `k`);
* `flagPairs_twosBits`: the pass-1 tag pairs are `(zb a k, [a mod 2^k ≠ 0])`;
* `p2outs_range` (the core): pass 2 or-s position `k` of the thermometer with `[2^k < |a|]`;
* `p2fieldT_thermo`, `p2recT_thermo`, `foldl_p2recT_thermo`: on thermometers
  `thermo w m` (`m` ones at the low positions, most significant position first) a field `a`
  turns `m` into `max m ⌈log₂ |a|⌉` (`Nat.clog 2 |a|`).
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts SubNLogN.Machine

/-! ## Bits -/

/-- Bit `i` of the two's-complement expansion of `z`. -/
def zb (z : ℤ) (i : ℕ) : Bool := decide (z / 2 ^ i % 2 = 1)

theorem zb_succ (z : ℤ) (i : ℕ) : zb z (i + 1) = zb (z / 2) i := by
  unfold zb
  rw [Int.ediv_ediv_of_nonneg (by norm_num : (0 : ℤ) ≤ 2), ← pow_succ']

theorem twosBits_eq_map' : ∀ (w : ℕ) (z : ℤ), twosBits w z = (List.range w).map (zb z)
  | 0, _ => rfl
  | w + 1, z => by
    rw [K1.twosBits_succ, twosBits_eq_map' w (z / 2), List.range_succ_eq_map, List.map_cons,
      List.map_map]
    congr 1
    · simp [zb]
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, zb_succ]

/-- `z mod 2^(k+1) ≠ 0` iff `z mod 2^k ≠ 0` or bit `k` is set. -/
theorem emod_two_pow_succ_ne (z : ℤ) (k : ℕ) :
    z % 2 ^ (k + 1) ≠ 0 ↔ (z % 2 ^ k ≠ 0 ∨ z / 2 ^ k % 2 = 1) := by
  have hP : (0 : ℤ) < 2 ^ k := by positivity
  set P : ℤ := 2 ^ k with hPd
  have h2 : (2 : ℤ) ^ (k + 1) = P * 2 := by rw [pow_succ]
  set q := z / P with hq
  set r := z % P with hr
  have hz : z = P * q + r := (Int.mul_ediv_add_emod z P).symm
  have hr0 : 0 ≤ r := Int.emod_nonneg z hP.ne'
  have hrP : r < P := Int.emod_lt_of_pos z hP
  have hq2 : 0 ≤ q % 2 ∧ q % 2 < 2 := ⟨Int.emod_nonneg q (by norm_num), Int.emod_lt_of_pos q (by norm_num)⟩
  have hq' : q = 2 * (q / 2) + q % 2 := (Int.mul_ediv_add_emod q 2).symm
  have hmod : z % 2 ^ (k + 1) = P * (q % 2) + r := by
    rw [h2]
    have e : z = P * (q % 2) + r + (P * 2) * (q / 2) := by
      calc z = P * q + r := hz
        _ = P * (2 * (q / 2) + q % 2) + r := by rw [← hq']
        _ = P * (q % 2) + r + (P * 2) * (q / 2) := by ring
    rw [e, Int.add_mul_emod_self_left]
    apply Int.emod_eq_of_lt
    · rcases Int.emod_two_eq_zero_or_one q with h | h <;> rw [h] <;> nlinarith
    · rcases Int.emod_two_eq_zero_or_one q with h | h <;> rw [h] <;> nlinarith
  rw [hmod]
  rcases Int.emod_two_eq_zero_or_one q with h' | h'
  · rw [h', mul_zero, zero_add]
    constructor
    · intro h
      exact Or.inl h
    · rintro (h | h)
      · exact h
      · omega
  · rw [h', mul_one]
    constructor
    · intro _
      exact Or.inr rfl
    · intro _
      omega

theorem any_range_zb (z : ℤ) : ∀ n : ℕ, (List.range n).any (zb z) = decide (z % 2 ^ n ≠ 0)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.any_append, any_range_zb z n]
    simp only [List.any_cons, List.any_nil, Bool.or_false, zb]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact (emod_two_pow_succ_ne z n).symm

theorem flagPairs_append_single : ∀ (f : Bool) (l : List Bool) (b : Bool),
    flagPairs f (l ++ [b]) = flagPairs f l ++ [(b, f || l.any id)]
  | f, [], b => by simp [flagPairs]
  | f, x :: l, b => by
    simp only [List.cons_append, flagPairs, flagPairs_append_single (f || x) l b, List.any_cons,
      id, Bool.or_assoc]

theorem flagPairs_range (z : ℤ) : ∀ n : ℕ,
    flagPairs false ((List.range n).map (zb z)) =
      (List.range n).map fun k => (zb z k, decide (z % 2 ^ k ≠ 0))
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_singleton, flagPairs_append_single,
      flagPairs_range z n, List.map_append, List.map_singleton, Bool.false_or, List.any_map]
    congr 2
    rw [← any_range_zb z n]
    rfl

theorem flagPairs_twosBits (w : ℕ) (a : ℤ) :
    flagPairs false (twosBits w a) = (List.range w).map fun k => (zb a k, decide (a % 2 ^ k ≠ 0)) := by
  rw [twosBits_eq_map', flagPairs_range]

/-! ## Pass 2: the update bits -/

/-- The running flag of pass 2 before position `n - 1` is processed. -/
def snAt (a : ℤ) (n : ℕ) : Bool := if a < 0 then decide (a < -2 ^ n) else decide (2 ^ n ≤ a)

theorem p2_step (a : ℤ) (n : ℕ) :
    p2u (decide (a < 0)) (snAt a (n + 1)) (zb a n) (decide (a % 2 ^ n ≠ 0)) =
        decide ((2 : ℤ) ^ n < |a|) ∧
      p2sn (decide (a < 0)) (snAt a (n + 1)) (zb a n) = snAt a n := by
  unfold p2u p2sn snAt zb
  have h2 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  rw [h2]
  have hP : (0 : ℤ) < 2 ^ n := by positivity
  set P : ℤ := 2 ^ n with hPd
  set q := a / P with hq
  set r := a % P with hr
  have hz : a = P * q + r := (Int.mul_ediv_add_emod a P).symm
  have hr0 : 0 ≤ r := Int.emod_nonneg a hP.ne'
  have hrP : r < P := Int.emod_lt_of_pos a hP
  have c1 : ∀ c : ℤ, (a < c * P ↔ q < c) := fun c => (Int.ediv_lt_iff_lt_mul hP).symm
  have c2 : ∀ c : ℤ, (c * P ≤ a ↔ c ≤ q) := fun c => (Int.le_ediv_iff_mul_le hP).symm
  rcases lt_or_ge a 0 with ha | ha
  · have hq0 : q < 0 := (c1 0).1 (by simpa using ha)
    have e1 : (a < -(2 * P)) ↔ q < -2 := by
      rw [show -(2 * P) = (-2) * P by ring]; exact c1 (-2)
    have e2 : (a < -P) ↔ q < -1 := by
      rw [show -P = (-1) * P by ring]; exact c1 (-1)
    have e3 : (P < |a|) ↔ q < -1 := by
      rw [abs_of_neg ha, ← e2]; constructor <;> intro h <;> linarith
    simp only [ha, decide_true, if_true, e1, e2, e3]
    constructor <;>
    · by_cases hA : q < -2 <;> by_cases hB : q % 2 = 1 <;> simp [hA, hB] <;> omega
  · have hq0 : 0 ≤ q := (c2 0).1 (by simpa using ha)
    have e1 : (2 * P ≤ a) ↔ 2 ≤ q := c2 2
    have e2 : (P ≤ a) ↔ 1 ≤ q := by rw [show P = 1 * P by ring]; exact c2 1
    have e3 : (P < |a|) ↔ (2 ≤ q ∨ (q = 1 ∧ r ≠ 0)) := by
      rw [abs_of_nonneg ha]
      constructor
      · intro h
        by_contra hc
        rw [not_or, not_and_or, not_not] at hc
        rcases lt_or_ge q 1 with hq1 | hq1
        · have : P * q ≤ 0 := by nlinarith
          linarith
        · have hq2 : q < 2 := by omega
          have hq1' : q = 1 := by omega
          rcases hc.2 with h3 | h3
          · exact h3 hq1'
          · rw [hz, hq1', h3] at h
            linarith
      · rintro (h | ⟨h1, h2⟩)
        · nlinarith
        · rw [hz, h1]
          have : 0 < r := lt_of_le_of_ne hr0 (Ne.symm h2)
          linarith
    have hnot : ¬ a < 0 := not_lt.mpr ha
    simp only [hnot, decide_false, if_false, e1, e2, e3]
    constructor <;>
    · by_cases hA : 2 ≤ q <;> by_cases hB : q % 2 = 1 <;> by_cases hC : r = 0 <;>
        simp [hA, hB, hC] <;> omega

theorem p2outs_range (a : ℤ) (τ : ℕ → Bool) : ∀ n : ℕ,
    p2outs (decide (a < 0)) (snAt a n)
        ((List.range n).reverse.map fun k => (zb a k, decide (a % 2 ^ k ≠ 0)))
        ((List.range n).reverse.map τ) =
      (List.range n).reverse.map fun k => τ k || decide ((2 : ℤ) ^ k < |a|)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, List.map_cons, List.map_cons]
    simp only [p2outs]
    rw [(p2_step a n).2, p2outs_range a τ n, (p2_step a n).1]

/-! ## Thermometers -/

/-- The thermometer of `m` on `w` positions, most significant position first: position `k` is
`[k < m]`. -/
def thermo (w m : ℕ) : List Bool := (List.range w).reverse.map fun k => decide (k < m)

theorem length_thermo (w m : ℕ) : (thermo w m).length = w := by simp [thermo]

theorem zb_top_of_fits {w : ℕ} {a : ℤ} (ha : FitsTwos w a) :
    zb a (w - 1) = decide (a < 0) := by
  obtain ⟨h1, h2⟩ := ha
  have hP : (0 : ℤ) < 2 ^ (w - 1) := by positivity
  unfold zb
  rcases lt_or_ge a 0 with hn | hn
  · have hlo : -1 ≤ a / 2 ^ (w - 1) := (Int.le_ediv_iff_mul_le hP).2 (by linarith)
    have hhi : a / 2 ^ (w - 1) < 0 := (Int.ediv_lt_iff_lt_mul hP).2 (by linarith)
    have : a / 2 ^ (w - 1) = -1 := by omega
    simp [this, hn]
  · have : a / 2 ^ (w - 1) = 0 := Int.ediv_eq_zero_of_lt hn h2
    simp [this, not_lt.mpr hn]

/-! ## Fields and records on thermometers -/

theorem snAt_fits {w : ℕ} {a : ℤ} (ha : FitsTwos w a) : snAt a w = false := by
  obtain ⟨h1, h2⟩ := ha
  have hp : (2 : ℤ) ^ (w - 1) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) (Nat.sub_le w 1)
  unfold snAt
  split_ifs with h
  · simp only [decide_eq_false_iff_not, not_lt]; linarith
  · simp only [decide_eq_false_iff_not, not_le]; linarith

theorem two_pow_lt_abs_iff (k : ℕ) (a : ℤ) :
    (2 : ℤ) ^ k < |a| ↔ k < Nat.clog 2 a.natAbs := by
  rw [Nat.lt_clog_iff_pow_lt (by norm_num), Int.abs_eq_natAbs]
  exact_mod_cast Iff.rfl

theorem p2fieldT_thermo {w : ℕ} (hw : 1 ≤ w) {a : ℤ} (ha : FitsTwos w a) (m : ℕ) :
    p2fieldT (twosBits w a) (thermo w m) = thermo w (max m (Nat.clog 2 a.natAbs)) := by
  unfold p2fieldT thermo
  rw [flagPairs_twosBits, ← List.map_reverse]
  have hng : ngOf ((List.range w).reverse.map fun k => (zb a k, decide (a % 2 ^ k ≠ 0))) =
      decide (a < 0) := by
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append, List.map_cons, ngOf,
      List.head?_cons, Option.map_some, Option.getD_some]
    have := zb_top_of_fits ha
    simpa using this
  rw [hng, ← snAt_fits ha, p2outs_range]
  apply List.map_congr_left
  intro k _
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, lt_max_iff, two_pow_lt_abs_iff]

/-- One record's update of the maximum. -/
def cmax (m : ℕ) (c : CInt) : ℕ := max (max m (Nat.clog 2 c.2.natAbs)) (Nat.clog 2 c.1.natAbs)

theorem p2recT_thermo {w : ℕ} (hw : 1 ≤ w) {c : CInt} (h1 : FitsTwos w c.1) (h2 : FitsTwos w c.2)
    (m : ℕ) : p2recT w (thermo w m) c = thermo w (cmax m c) := by
  unfold p2recT cmax
  rw [p2fieldT_thermo hw h2, p2fieldT_thermo hw h1]

theorem foldl_p2recT_thermo {w : ℕ} (hw : 1 ≤ w) :
    ∀ (cs : List CInt), (∀ c ∈ cs, FitsTwos w c.1 ∧ FitsTwos w c.2) → ∀ m : ℕ,
      cs.foldl (p2recT w) (thermo w m) = thermo w (cs.foldl cmax m)
  | [], _, _ => rfl
  | c :: cs, h, m => by
    rw [List.foldl_cons, List.foldl_cons, p2recT_thermo hw (h c (by simp)).1 (h c (by simp)).2]
    exact foldl_p2recT_thermo hw cs (fun c' hc' => h c' (by simp [hc'])) _

theorem count_true_thermo (m : ℕ) : ∀ w, (thermo w m).count true = min m w
  | 0 => by simp [thermo]
  | w + 1 => by
    have ih := count_true_thermo m w
    unfold thermo at ih ⊢
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, List.count_cons, ih]
    by_cases h : w < m <;> simp [h] <;> omega

end SubNLogN.Machine.BridgePP
