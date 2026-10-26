import SubNLogN.Math.Networks.AppCShear

/-!
# Proof of `PackedAgreeStmt` (Lemma A.9 (`lem:transfer13`) carry containment)

We prove `packedAgree_holds : PackedAgreeStmt` (statement in `AppCShear.lean`): for `K ≥ 6`, `L = fK`,
`ρ < K` and chunks `x, y, z < 2^L` in the good set `packedGood` (all used guard values of `y` and `z`
lie in `[10, 2^{K-1} - 11]`), the composite `packedS0` of the eight packed cyclic shifts equals the
ideal selected-bit XOR `packedT0`, and `packedT0` preserves the good set
(Lemma A.9 (`lem:transfer13`), [OAI26, §5.2, Lemma 13]). No hypotheses beyond those of the
statement are used.

## Plan
* `seg K ρ v i = ⌊v / 2^(ρ+iK)⌋ mod 2^K` is segment `i` (bits `ρ+iK, …, ρ+iK+K-1`) of `v`, and
  `rebuild K ρ n low high s = low + Σ_{i<n} 2^(ρ+iK) s_i + 2^(ρ+nK) high`. Every `v` is the rebuild
  of its own parts (`rebuild_self`); the parts of a rebuild with `low < 2^ρ` and all `s_i < 2^K` are
  `low`, `s`, `high` (`rebuild_spec`, by peeling the top segment). Hence `eq_of_parts`: two numbers
  with the same low part, segments and high part are equal.
* `core_line`: adding `Σ_{i<n} 2^(ρ+iK) d_i` (`d_i ∈ ℤ`) to `tgt < 2^L` and reducing mod `2^L`
  changes segment `i` to `seg tgt i + d_i` and nothing else, provided every `seg tgt i + d_i` lies in
  `[0, 2^K)`: no carry or borrow leaves a segment, and the high part is unchanged, so no wrap.
* `line_spec`: one `packedLine` acts on every segment pair `(seg y i, seg z i)` as one scalar step
  `sStep` (the body of the fold in `runEight`) with control `bitAt x (ρ+iK)`, provided all used
  segments of `y` and `z` lie in `[1, 2^K-2]`; the tested bit of the other chunk is the low bit of
  its segment.
* `fold_spec`: induction over a list of lines with signs `±1`; each scalar step moves each coordinate
  by at most one (`sStep_disp`), so `len(ops) ≤ seg ≤ 2^K-1-len(ops)` suffices.
* The good set gives `8 ≤ seg` and `seg + 8 < 2^K` for every used segment (`guardVal = seg / 2`;
  in fact `20 ≤ seg ≤ 2^K-21`, but eight lines only need the weaker bound). The scalar
  spec (`runEight_ctrl`: flip the low bit of `u` iff `c = 1`, restore `w`), `Nat.xor_mod_two_pow` and
  `Nat.xor_div_two_pow` identify the result of the eight lines with `packedT0`, and `T₀` changes no
  guard bit. The degenerate case `f = 0` (so `L = 0`) is checked directly.
-/

namespace SubNLogN.Math.Networks

namespace PackedAgreeAux

/-! ### Segment representation -/

/-- Segment `i` of `v`: its `K` bits starting at position `ρ + iK`. -/
def seg (K ρ v i : ℕ) : ℕ := v / 2 ^ (ρ + i * K) % 2 ^ K

/-- Reassemble a number from its low part (meant to be `< 2^ρ`), `n` segments `s 0, …, s (n-1)`
(meant to be `< 2^K`), and its high part (the value from bit `ρ + nK` on). -/
def rebuild (K ρ n low high : ℕ) (s : ℕ → ℕ) : ℕ :=
  low + ∑ i ∈ Finset.range n, 2 ^ (ρ + i * K) * s i + 2 ^ (ρ + n * K) * high

/-- Peeling the top segment: `n + 1` segments are `n` segments with the top one moved into the
high part. -/
lemma rebuild_succ (K ρ n low high : ℕ) (s : ℕ → ℕ) :
    rebuild K ρ (n + 1) low high s = rebuild K ρ n low (s n + 2 ^ K * high) s := by
  unfold rebuild
  rw [Finset.sum_range_succ, show ρ + (n + 1) * K = ρ + n * K + K by ring, pow_add]
  ring

/-- The parts of a rebuild (with `low < 2^ρ` and `s i < 2^K` for `i < n`) are `low`, `s`, `high`. -/
lemma rebuild_spec (K ρ : ℕ) : ∀ (n low high : ℕ) (s : ℕ → ℕ), low < 2 ^ ρ →
    (∀ i < n, s i < 2 ^ K) →
    rebuild K ρ n low high s % 2 ^ ρ = low ∧
      rebuild K ρ n low high s / 2 ^ (ρ + n * K) = high ∧
      ∀ i < n, seg K ρ (rebuild K ρ n low high s) i = s i
  | 0, low, high, s, hlow, _ => by
    simp only [rebuild, Finset.range_zero, Finset.sum_empty, add_zero, zero_mul]
    refine ⟨?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
    · rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlow, zero_add]
  | n + 1, low, high, s, hlow, hs => by
    obtain ⟨h1, h2, h3⟩ :=
      rebuild_spec K ρ n low (s n + 2 ^ K * high) s hlow (fun i hi => hs i (by omega))
    have hsn : s n < 2 ^ K := hs n (by omega)
    rw [rebuild_succ]
    refine ⟨h1, ?_, ?_⟩
    · rw [show ρ + (n + 1) * K = ρ + n * K + K by ring, pow_add, ← Nat.div_div_eq_div_mul, h2,
        Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hsn, zero_add]
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi | hi
      · exact h3 i hi
      · subst hi
        rw [seg, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsn]

/-- Every number is the rebuild of its own low part, segments and high part. -/
lemma rebuild_self (K ρ v : ℕ) : ∀ n,
    rebuild K ρ n (v % 2 ^ ρ) (v / 2 ^ (ρ + n * K)) (seg K ρ v) = v
  | 0 => by
    simp only [rebuild, Finset.range_zero, Finset.sum_empty, add_zero, zero_mul]
    exact Nat.mod_add_div v (2 ^ ρ)
  | n + 1 => by
    rw [rebuild_succ]
    have h : seg K ρ v n + 2 ^ K * (v / 2 ^ (ρ + (n + 1) * K)) = v / 2 ^ (ρ + n * K) := by
      have e : v / 2 ^ (ρ + (n + 1) * K) = v / 2 ^ (ρ + n * K) / 2 ^ K := by
        rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; ring
      rw [seg, e, Nat.mod_add_div]
    rw [h]
    exact rebuild_self K ρ v n

lemma rebuild_congr {K ρ n low high : ℕ} {s s' : ℕ → ℕ} (h : ∀ i < n, s i = s' i) :
    rebuild K ρ n low high s = rebuild K ρ n low high s' := by
  unfold rebuild
  rw [Finset.sum_congr rfl (g := fun i => 2 ^ (ρ + i * K) * s' i)
    (fun i hi => by rw [h i (Finset.mem_range.mp hi)])]

/-- Extensionality: equal low parts, segments `i < n` and high parts give equal numbers. -/
lemma eq_of_parts {K ρ n v v' : ℕ} (h1 : v % 2 ^ ρ = v' % 2 ^ ρ)
    (h2 : v / 2 ^ (ρ + n * K) = v' / 2 ^ (ρ + n * K)) (h3 : ∀ i < n, seg K ρ v i = seg K ρ v' i) :
    v = v' := by
  calc v = rebuild K ρ n (v % 2 ^ ρ) (v / 2 ^ (ρ + n * K)) (seg K ρ v) :=
        (rebuild_self K ρ v n).symm
    _ = rebuild K ρ n (v' % 2 ^ ρ) (v' / 2 ^ (ρ + n * K)) (seg K ρ v') := by
        rw [h1, h2]; exact rebuild_congr h3
    _ = v' := rebuild_self K ρ v' n

/-! ### One packed addition with segment-confined increments -/

/-- **No carry leaves a segment.** If `tgt < 2^L`, `ρ + nK ≤ L`, and every `seg tgt i + d i`
(`i < n`) lies in `[0, 2^K)`, then `((tgt + Σ_{i<n} 2^(ρ+iK) d_i) mod 2^L)` is a natural number
below `2^L` with the same low part and high part as `tgt` and with segments `seg tgt i + d i`. -/
lemma core_line {K ρ n L : ℕ} (hJ : ρ + n * K ≤ L) {tgt : ℕ} (htgt : tgt < 2 ^ L) (d : ℕ → ℤ)
    (hd : ∀ i < n, 0 ≤ (seg K ρ tgt i : ℤ) + d i ∧ (seg K ρ tgt i : ℤ) + d i < 2 ^ K) :
    ∃ new : ℕ,
      (((tgt : ℤ) + ∑ i ∈ Finset.range n, (2 : ℤ) ^ (ρ + i * K) * d i) % (2 : ℤ) ^ L).toNat = new ∧
      new < 2 ^ L ∧ new % 2 ^ ρ = tgt % 2 ^ ρ ∧
      new / 2 ^ (ρ + n * K) = tgt / 2 ^ (ρ + n * K) ∧
      ∀ i < n, (seg K ρ new i : ℤ) = seg K ρ tgt i + d i := by
  obtain ⟨s', hs'⟩ : ∃ s' : ℕ → ℕ, ∀ i < n, ((s' i : ℕ) : ℤ) = (seg K ρ tgt i : ℤ) + d i :=
    ⟨fun i => ((seg K ρ tgt i : ℤ) + d i).toNat, fun i hi => Int.toNat_of_nonneg (hd i hi).1⟩
  have hs'lt : ∀ i < n, s' i < 2 ^ K := by
    intro i hi
    have h := (hd i hi).2
    rw [← hs' i hi] at h
    exact_mod_cast h
  obtain ⟨hN1, hN2, hN3⟩ := rebuild_spec K ρ n (tgt % 2 ^ ρ) (tgt / 2 ^ (ρ + n * K)) s'
    (Nat.mod_lt _ (by positivity)) hs'lt
  have hcast : ((rebuild K ρ n (tgt % 2 ^ ρ) (tgt / 2 ^ (ρ + n * K)) s' : ℕ) : ℤ) =
      (tgt : ℤ) + ∑ i ∈ Finset.range n, (2 : ℤ) ^ (ρ + i * K) * d i := by
    have h0 : ((rebuild K ρ n (tgt % 2 ^ ρ) (tgt / 2 ^ (ρ + n * K)) (seg K ρ tgt) : ℕ) : ℤ) =
        (tgt : ℤ) := by
      rw [rebuild_self]
    rw [← h0]
    simp only [rebuild]
    push_cast
    have hsum : ∑ i ∈ Finset.range n, (2 : ℤ) ^ (ρ + i * K) * ((s' i : ℕ) : ℤ) =
        ∑ i ∈ Finset.range n, (2 : ℤ) ^ (ρ + i * K) * ((seg K ρ tgt i : ℕ) : ℤ) +
          ∑ i ∈ Finset.range n, (2 : ℤ) ^ (ρ + i * K) * d i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [← mul_add, hs' i (Finset.mem_range.mp hi)]
    linear_combination hsum
  have hpow : 2 ^ L = 2 ^ (ρ + n * K) * 2 ^ (L - (ρ + n * K)) := by
    rw [← pow_add]; congr 1; omega
  have hNlt : rebuild K ρ n (tgt % 2 ^ ρ) (tgt / 2 ^ (ρ + n * K)) s' < 2 ^ L := by
    have htop : tgt / 2 ^ (ρ + n * K) < 2 ^ (L - (ρ + n * K)) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc tgt < 2 ^ L := htgt
        _ = 2 ^ (L - (ρ + n * K)) * 2 ^ (ρ + n * K) := by rw [hpow, mul_comm]
    rw [← hN2, Nat.div_lt_iff_lt_mul (by positivity)] at htop
    calc _ < 2 ^ (L - (ρ + n * K)) * 2 ^ (ρ + n * K) := htop
      _ = 2 ^ L := by rw [hpow, mul_comm]
  refine ⟨rebuild K ρ n (tgt % 2 ^ ρ) (tgt / 2 ^ (ρ + n * K)) s', ?_, hNlt, hN1, hN2,
    fun i hi => by rw [hN3 i hi, hs' i hi]⟩
  rw [← hcast, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hNlt), Int.toNat_natCast]

/-! ### Bits and the scalar program -/

lemma bitAt_le_one (v j : ℕ) : bitAt v j ≤ 1 := by
  unfold bitAt
  have := Nat.mod_lt (v / 2 ^ j) (show 2 > 0 by norm_num)
  omega

lemma bitAt_cast (v j : ℕ) : (bitAt v j : ℤ) = 0 ∨ (bitAt v j : ℤ) = 1 := by
  have := bitAt_le_one v j
  omega

/-- Bit `ρ + iK` of `v` is the low bit of segment `i`. -/
lemma bitAt_eq_seg_mod {K : ℕ} (hK : 1 ≤ K) (ρ v i : ℕ) :
    bitAt v (ρ + i * K) = seg K ρ v i % 2 := by
  unfold bitAt seg
  rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]

/-- One scalar step of the eight-operation program: the body of the fold in `runEight`. -/
def sStep (c : ℤ) (p : ℤ × ℤ) (op : Bool × ℤ × ℕ) : ℤ × ℤ :=
  if op.1 then (p.1 + op.2.1 * c * (if p.2 % 2 = op.2.2 then 1 else 0), p.2)
  else (p.1, p.2 + op.2.1 * c * (if p.1 % 2 = op.2.2 then 1 else 0))

lemma runEight_eq (c : ℤ) (uw : ℤ × ℤ) : runEight c uw = eightOps.foldl (sStep c) uw := rfl

/-- The scalar program (local copy of the content of `RunEightSpecStmt`, in the form used here):
with control `c ∈ {0,1}` it maps `(u, w)` to `(u + c (1 - 2 (u mod 2)), w)`. -/
lemma runEight_ctrl (c u w : ℤ) (hc : c = 0 ∨ c = 1) :
    runEight c (u, w) = (u + c * (1 - 2 * (u % 2)), w) := by
  rcases hc with rfl | rfl
  · simp [runEight, eightOps]
  · have key : runEight 1 (u, w) = (u + 1 - 2 * (u % 2), w) := by
      have h1 : ∀ x : ℤ, (x + 1) % 2 = 1 - x % 2 := fun x => by omega
      have h3 : ∀ x : ℤ, (x + -1) % 2 = 1 - x % 2 := fun x => by omega
      rcases Int.emod_two_eq_zero_or_one u with hu | hu <;>
      rcases Int.emod_two_eq_zero_or_one w with hw | hw <;>
      simp [runEight, eightOps, hu, hw, h1, h3] <;> omega
    rw [key]
    congr 1
    ring

/-- Each scalar step with control `c ∈ {0,1}` and sign `±1` moves each coordinate by at most one. -/
lemma sStep_disp {c : ℤ} (hc : c = 0 ∨ c = 1) (p : ℤ × ℤ) {op : Bool × ℤ × ℕ}
    (hε : op.2.1 = 1 ∨ op.2.1 = -1) :
    p.1 - 1 ≤ (sStep c p op).1 ∧ (sStep c p op).1 ≤ p.1 + 1 ∧
      p.2 - 1 ≤ (sStep c p op).2 ∧ (sStep c p op).2 ≤ p.2 + 1 := by
  obtain ⟨t, e, q⟩ := op
  obtain ⟨u, w⟩ := p
  simp only at hε
  unfold sStep
  rcases hc with rfl | rfl <;> rcases hε with rfl | rfl <;> cases t <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> omega

/-! ### One packed line acts segmentwise -/

/-- The indicator summand of a packed line is the scalar step's increment. -/
lemma ind_eq {K : ℕ} (hK : 1 ≤ K) (ρ x o i q : ℕ) (e : ℤ) :
    e * (if bitAt x (ρ + i * K) = 1 ∧ bitAt o (ρ + i * K) = q then (1 : ℤ) else 0) =
      e * (bitAt x (ρ + i * K) : ℤ) * (if (seg K ρ o i : ℤ) % 2 = (q : ℤ) then 1 else 0) := by
  rw [bitAt_eq_seg_mod hK ρ o i]
  have hb := bitAt_le_one x (ρ + i * K)
  have hiff : ((seg K ρ o i : ℤ) % 2 = (q : ℤ)) ↔ (seg K ρ o i % 2 = q) := by
    constructor <;> intro h <;> omega
  by_cases h1 : bitAt x (ρ + i * K) = 1
  · by_cases h2 : seg K ρ o i % 2 = q
    · rw [if_pos ⟨h1, h2⟩, if_pos (hiff.mpr h2), h1]; push_cast; ring
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 (hiff.mp h))]; ring
  · have h0 : bitAt x (ρ + i * K) = 0 := by omega
    rw [if_neg (fun h => h1 h.1), h0]; push_cast; ring

/-- `Y` agrees with `y` below bit `ρ` and from bit `ρ + nK` on, and `Y < 2^L`. -/
def SameFrame (K ρ L n y Y : ℕ) : Prop :=
  Y < 2 ^ L ∧ Y % 2 ^ ρ = y % 2 ^ ρ ∧ Y / 2 ^ (ρ + n * K) = y / 2 ^ (ρ + n * K)

lemma SameFrame.refl {K ρ L n y : ℕ} (hy : y < 2 ^ L) : SameFrame K ρ L n y y := ⟨hy, rfl, rfl⟩

lemma SameFrame.trans {K ρ L n y Y Y' : ℕ} (h : SameFrame K ρ L n y Y)
    (h' : SameFrame K ρ L n Y Y') : SameFrame K ρ L n y Y' :=
  ⟨h'.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

/-- **One packed line.** If all used segments of `y` and `z` lie in `[1, 2^K - 2]`, the packed line
`op` (sign `±1`) keeps `x`, keeps the frames of `y` and `z`, and acts on each segment pair
`(seg y i, seg z i)` as the scalar step `sStep` with control `bitAt x (ρ + iK)`. -/
lemma line_spec {K ρ L f : ℕ} (hK : 1 ≤ K) (hJ : ρ + (f - 1) * K ≤ L) (op : Bool × ℤ × ℕ)
    (hε : op.2.1 = 1 ∨ op.2.1 = -1) (x y z : ℕ) (hy : y < 2 ^ L) (hz : z < 2 ^ L)
    (hb : ∀ i < f - 1, 1 ≤ seg K ρ y i ∧ seg K ρ y i + 2 ≤ 2 ^ K ∧
      1 ≤ seg K ρ z i ∧ seg K ρ z i + 2 ≤ 2 ^ K) :
    ∃ y' z', packedLine L K ρ f op (x, y, z) = (x, y', z') ∧
      SameFrame K ρ L (f - 1) y y' ∧ SameFrame K ρ L (f - 1) z z' ∧
      ∀ i < f - 1, ((seg K ρ y' i : ℤ), (seg K ρ z' i : ℤ)) =
        sStep (bitAt x (ρ + i * K)) ((seg K ρ y i : ℤ), (seg K ρ z i : ℤ)) op := by
  obtain ⟨t, e, q⟩ := op
  simp only at hε
  have hd : ∀ (o tgt : ℕ), (∀ i < f - 1, 1 ≤ seg K ρ tgt i ∧ seg K ρ tgt i + 2 ≤ 2 ^ K) →
      ∀ i < f - 1, 0 ≤ (seg K ρ tgt i : ℤ) + e * (bitAt x (ρ + i * K) : ℤ) *
          (if (seg K ρ o i : ℤ) % 2 = (q : ℤ) then 1 else 0) ∧
        (seg K ρ tgt i : ℤ) + e * (bitAt x (ρ + i * K) : ℤ) *
          (if (seg K ρ o i : ℤ) % 2 = (q : ℤ) then 1 else 0) < 2 ^ K := by
    intro o tgt hb' i hi
    obtain ⟨h1, h2⟩ := hb' i hi
    have hc := bitAt_le_one x (ρ + i * K)
    have h2' : ((seg K ρ tgt i : ℕ) : ℤ) + 2 ≤ (2 : ℤ) ^ K := by exact_mod_cast h2
    rcases hε with rfl | rfl <;> split_ifs <;> constructor <;> omega
  have hoff : ∀ o : ℕ, (e * ∑ i ∈ Finset.range (f - 1), (2 : ℤ) ^ (ρ + i * K) *
      (if bitAt x (ρ + i * K) = 1 ∧ bitAt o (ρ + i * K) = q then 1 else 0)) =
      ∑ i ∈ Finset.range (f - 1), (2 : ℤ) ^ (ρ + i * K) * (e * (bitAt x (ρ + i * K) : ℤ) *
          (if (seg K ρ o i : ℤ) % 2 = (q : ℤ) then 1 else 0)) := by
    intro o
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← ind_eq hK ρ x o i q e]
    ring
  cases t
  · -- target `z`, tested chunk `y`
    obtain ⟨new, hnew, hlt, hlow, hhigh, hseg⟩ :=
      core_line hJ hz _ (hd y z (fun i hi => ⟨(hb i hi).2.2.1, (hb i hi).2.2.2⟩))
    refine ⟨y, new, ?_, SameFrame.refl hy, ⟨hlt, hlow, hhigh⟩, fun i hi => ?_⟩
    · simp only [packedLine, Bool.false_eq_true, ↓reduceIte]
      rw [hoff y, hnew]
    · simp only [sStep, Bool.false_eq_true, ↓reduceIte, hseg i hi]
  · -- target `y`, tested chunk `z`
    obtain ⟨new, hnew, hlt, hlow, hhigh, hseg⟩ :=
      core_line hJ hy _ (hd z y (fun i hi => ⟨(hb i hi).1, (hb i hi).2.1⟩))
    refine ⟨new, z, ?_, ⟨hlt, hlow, hhigh⟩, SameFrame.refl hz, fun i hi => ?_⟩
    · simp only [packedLine, ↓reduceIte]
      rw [hoff z, hnew]
    · simp only [sStep, ↓reduceIte, hseg i hi]

/-- **A sequence of packed lines** with signs `±1` acts segmentwise as the scalar program, provided
every used segment of `y` and `z` starts in `[len ops, 2^K - 1 - len ops]`. -/
lemma fold_spec {K ρ L f : ℕ} (hK : 1 ≤ K) (hJ : ρ + (f - 1) * K ≤ L) (x : ℕ) :
    ∀ (ops : List (Bool × ℤ × ℕ)), (∀ op ∈ ops, op.2.1 = 1 ∨ op.2.1 = -1) →
    ∀ y z : ℕ, y < 2 ^ L → z < 2 ^ L →
    (∀ i < f - 1, ops.length ≤ seg K ρ y i ∧ seg K ρ y i + ops.length < 2 ^ K ∧
      ops.length ≤ seg K ρ z i ∧ seg K ρ z i + ops.length < 2 ^ K) →
    ∃ Y Z, ops.foldl (fun p op => packedLine L K ρ f op p) (x, y, z) = (x, Y, Z) ∧
      SameFrame K ρ L (f - 1) y Y ∧ SameFrame K ρ L (f - 1) z Z ∧
      ∀ i < f - 1, ((seg K ρ Y i : ℤ), (seg K ρ Z i : ℤ)) =
        ops.foldl (sStep (bitAt x (ρ + i * K))) ((seg K ρ y i : ℤ), (seg K ρ z i : ℤ))
  | [], _, y, z, hy, hz, _ =>
    ⟨y, z, rfl, SameFrame.refl hy, SameFrame.refl hz, fun _ _ => rfl⟩
  | op :: rest, hops, y, z, hy, hz, hb => by
    have hε := hops op (by simp)
    have hb1 : ∀ i < f - 1, 1 ≤ seg K ρ y i ∧ seg K ρ y i + 2 ≤ 2 ^ K ∧
        1 ≤ seg K ρ z i ∧ seg K ρ z i + 2 ≤ 2 ^ K := by
      intro i hi
      have h0 := hb i hi
      simp only [List.length_cons] at h0
      omega
    obtain ⟨y1, z1, hp, hfy, hfz, hseg⟩ := line_spec hK hJ op hε x y z hy hz hb1
    have hb' : ∀ i < f - 1, rest.length ≤ seg K ρ y1 i ∧ seg K ρ y1 i + rest.length < 2 ^ K ∧
        rest.length ≤ seg K ρ z1 i ∧ seg K ρ z1 i + rest.length < 2 ^ K := by
      intro i hi
      have h0 := hb i hi
      simp only [List.length_cons] at h0
      have hd := sStep_disp (bitAt_cast x (ρ + i * K)) ((seg K ρ y i : ℤ), (seg K ρ z i : ℤ)) hε
      rw [← hseg i hi] at hd
      simp only at hd
      omega
    obtain ⟨Y, Z, hfold, hfY, hfZ, hsegY⟩ :=
      fold_spec hK hJ x rest (fun o ho => hops o (by simp [ho])) y1 z1 hfy.1 hfz.1 hb'
    refine ⟨Y, Z, ?_, hfy.trans hfY, hfz.trans hfZ, fun i hi => ?_⟩
    · simp only [List.foldl_cons]
      rw [hp]
      exact hfold
    · rw [List.foldl_cons, hsegY i hi, hseg i hi]

/-! ### Selected-bit XOR and guards -/

lemma seg_xor (K ρ a b i : ℕ) : seg K ρ (a ^^^ b) i = seg K ρ a i ^^^ seg K ρ b i := by
  unfold seg
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]

/-- XOR with a bit `c ≤ 1` flips the low bit iff `c = 1` and keeps the quotient by two. -/
lemma xor_bit (s c : ℕ) (hc : c ≤ 1) :
    ((s ^^^ c : ℕ) : ℤ) = (s : ℤ) + (c : ℤ) * (1 - 2 * ((s : ℤ) % 2)) ∧ (s ^^^ c) / 2 = s / 2 := by
  have hdiv : (s ^^^ c) / 2 = s / 2 := by
    rw [Nat.xor_div_two, show c / 2 = 0 by omega, Nat.xor_zero]
  refine ⟨?_, hdiv⟩
  have hmod : (s ^^^ c) % 2 = s % 2 ^^^ c % 2 := by
    have h := Nat.xor_mod_two_pow (a := s) (b := c) (n := 1)
    rw [pow_one] at h
    exact h
  have h1 := Nat.div_add_mod (s ^^^ c) 2
  have h2 := Nat.div_add_mod s 2
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · simp
  · rcases Nat.mod_two_eq_zero_or_one s with hs | hs
    · have h3 : (s ^^^ 1) % 2 = 1 := by simp [hmod, hs]
      omega
    · have h3 : (s ^^^ 1) % 2 = 0 := by simp [hmod, hs]
      omega

lemma two_pow_eq {K : ℕ} (hK : 1 ≤ K) : 2 ^ K = 2 * 2 ^ (K - 1) := by
  rw [← pow_succ']; congr 1; omega

/-- The guard value of segment `i` is the segment without its selected (low) bit. -/
lemma guardVal_eq {K : ℕ} (hK : 1 ≤ K) (ρ i v : ℕ) : guardVal K ρ i v = seg K ρ v i / 2 := by
  unfold guardVal seg
  rw [two_pow_eq hK, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← pow_succ]

/-- Good guards give `8 ≤ seg` and `seg + 8 < 2^K` (the segment in fact lies in `[20, 2^K - 21]`;
only this weaker bound, enough for eight lines, is proved). -/
lemma seg_bounds_of_guard {K : ℕ} (hK : 1 ≤ K) (ρ i v : ℕ) (h1 : 10 ≤ guardVal K ρ i v)
    (h2 : guardVal K ρ i v + 11 ≤ 2 ^ (K - 1)) : 8 ≤ seg K ρ v i ∧ seg K ρ v i + 8 < 2 ^ K := by
  rw [guardVal_eq hK] at h1 h2
  have := two_pow_eq hK
  omega

/-- The XOR mask of `T₀`: bit `ρ + iK` of `x` at position `ρ + iK`, for `i < n`. -/
def maskOf (K ρ n x : ℕ) : ℕ := ∑ i ∈ Finset.range n, 2 ^ (ρ + i * K) * bitAt x (ρ + i * K)

lemma mask_parts {K : ℕ} (hK : 1 ≤ K) (ρ n x : ℕ) :
    maskOf K ρ n x % 2 ^ ρ = 0 ∧ maskOf K ρ n x / 2 ^ (ρ + n * K) = 0 ∧
      ∀ i < n, seg K ρ (maskOf K ρ n x) i = bitAt x (ρ + i * K) := by
  have hm : maskOf K ρ n x = rebuild K ρ n 0 0 (fun i => bitAt x (ρ + i * K)) := by
    simp [maskOf, rebuild]
  rw [hm]
  have h2K : 2 ≤ 2 ^ K := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
  exact rebuild_spec K ρ n 0 0 _ (by positivity)
    (fun i _ => lt_of_le_of_lt (bitAt_le_one _ _) (by omega))

end PackedAgreeAux

open PackedAgreeAux in
/-- **Lemma A.9 (`lem:transfer13`) agreement off `B`** ([OAI26, §5.2, Lemma 13]). For
`K ≥ 6`, `L = fK`, `ρ < K` and chunks `x, y, z < 2^L` whose used guards (segments `i < f - 1` of `y`
and `z`) lie in `[10, 2^{K-1} - 11]`, the eight packed shifts `packedS0` equal the ideal selected-bit
XOR `packedT0`, and `packedT0` preserves the good set. -/
theorem packedAgree_holds : PackedAgreeStmt := by
  intro L K ρ f hK hL hρ xyz hx hy hz hgood
  obtain ⟨x, y, z⟩ := xyz
  simp only at hx hy hz
  have hK1 : 1 ≤ K := by omega
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · -- `f = 0`: then `L = 0`, all chunks vanish, and no segment is used
    rw [zero_mul] at hL
    subst hL
    simp only [pow_zero, Nat.lt_one_iff] at hx hy hz
    subst hx hy hz
    refine ⟨?_, fun i hi => absurd hi (by omega)⟩
    simp [packedS0, packedT0, packedLine, eightOps]
  · have hJ : ρ + (f - 1) * K ≤ L := by
      obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
      rw [hL, Nat.add_sub_cancel, add_mul, one_mul]
      omega
    have hb : ∀ i < f - 1, eightOps.length ≤ seg K ρ y i ∧
        seg K ρ y i + eightOps.length < 2 ^ K ∧
        eightOps.length ≤ seg K ρ z i ∧ seg K ρ z i + eightOps.length < 2 ^ K := by
      intro i hi
      obtain ⟨g1, g2, g3, g4⟩ := hgood i hi
      have hy' := seg_bounds_of_guard hK1 ρ i y g1 g2
      have hz' := seg_bounds_of_guard hK1 ρ i z g3 g4
      have hlen : eightOps.length = 8 := rfl
      rw [hlen]
      exact ⟨hy'.1, hy'.2, hz'.1, hz'.2⟩
    have hεops : ∀ op ∈ eightOps, op.2.1 = 1 ∨ op.2.1 = -1 := by
      decide
    obtain ⟨Y, Z, hfold, hfY, hfZ, hsegYZ⟩ := fold_spec hK1 hJ x eightOps hεops y z hy hz hb
    have hseg : ∀ i < f - 1, (seg K ρ Y i : ℤ) = seg K ρ y i +
        (bitAt x (ρ + i * K) : ℤ) * (1 - 2 * ((seg K ρ y i : ℤ) % 2)) ∧
        seg K ρ Z i = seg K ρ z i := by
      intro i hi
      have h := hsegYZ i hi
      rw [← runEight_eq, runEight_ctrl _ _ _ (bitAt_cast x (ρ + i * K)), Prod.mk.injEq] at h
      exact ⟨h.1, by exact_mod_cast h.2⟩
    obtain ⟨hm1, hm2, hm3⟩ := mask_parts hK1 ρ (f - 1) x
    have hZ : Z = z := eq_of_parts hfZ.2.1 hfZ.2.2 (fun i hi => (hseg i hi).2)
    have hY : Y = y ^^^ maskOf K ρ (f - 1) x := by
      refine eq_of_parts (K := K) (ρ := ρ) (n := f - 1) ?_ ?_ ?_
      · rw [hfY.2.1, Nat.xor_mod_two_pow, hm1, Nat.xor_zero]
      · rw [hfY.2.2, Nat.xor_div_two_pow, hm2, Nat.xor_zero]
      · intro i hi
        rw [seg_xor, hm3 i hi]
        have h1 := (xor_bit (seg K ρ y i) (bitAt x (ρ + i * K)) (bitAt_le_one _ _)).1
        have h2 := (hseg i hi).1
        exact_mod_cast h2.trans h1.symm
    refine ⟨?_, ?_⟩
    · show eightOps.foldl (fun p op => packedLine L K ρ f op p) (x, y, z) =
        (x, y ^^^ maskOf K ρ (f - 1) x, z)
      rw [hfold, hY, hZ]
    · intro i hi
      obtain ⟨g1, g2, g3, g4⟩ := hgood i hi
      have hg : guardVal K ρ i (y ^^^ maskOf K ρ (f - 1) x) = guardVal K ρ i y := by
        rw [guardVal_eq hK1, guardVal_eq hK1, seg_xor, hm3 i hi,
          (xor_bit _ _ (bitAt_le_one _ _)).2]
      show 10 ≤ guardVal K ρ i (y ^^^ maskOf K ρ (f - 1) x) ∧
        guardVal K ρ i (y ^^^ maskOf K ρ (f - 1) x) + 11 ≤ 2 ^ (K - 1) ∧
        10 ≤ guardVal K ρ i z ∧ guardVal K ρ i z + 11 ≤ 2 ^ (K - 1)
      rw [hg]
      exact ⟨g1, g2, g3, g4⟩

end SubNLogN.Math.Networks
