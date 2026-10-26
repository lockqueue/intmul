/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.PrefixDefs
import SubNLogN.Math.Walsh.IntForms
import SubNLogN.Machine.Arith.Value
import SubNLogN.Math.Walsh.IntForms.Address
import SubNLogN.Math.Walsh.Identities

/-!
# K4-PREFIX, value-level facts (`Machine/FFT/PrefixMath.lean`)

Pure mathematics for `PrefixRoundStmt` (`Contracts/FFT.lean:239`; Theorem 6.5, `thm:direct-fft`,
Section 6.4). There is no machine in this file.
* `roundSet_eq_posBlock` (M1): for a prefix round, `roundSet ℓ K a v` is the position block
  `[pfS, pfS + pfN)`. This uses the layout `𝒫 ‖ 𝒞` (`Math/Walsh/Layout.lean`): slots `(i, ℓ-1)` with
  `a_i = ℓ` come first, then for `v' = b₀-1, …, 0` the `D` slots `(i, v')`.
* `encCube_truncArr_hT_posBlock` (M2): `Q_q(H_T z)` on a position block `T = [s, s + n)` is `n`
  exact butterfly passes on the index bits `m-s-n, …, m-s-1` (`bflyIter`), then one truncation by
  `2^n` (`gridIntC_truncC_hT`, `Math/Walsh/IntForms.lean`).
* `fits_bflyIter` (M3): the exact passes fit `W ≥ q + j + 2` bits.
* `truncShift_iter` (M4): `n` truncations by `2` are one truncation by `2^n`.

Helpers (namespace `SubNLogN.Machine.FFT.PrefixAux.Math`):
* (M4) `tdiv_tdiv_of_nonneg`: truncation toward zero composes.
* (M3) `CBound`: each pass at most doubles the largest numerator (`cbound_bpass`).
* (M2) `arrOf F` is the stored array of numerators `F`. One pass on index bit `b` of `arrOf F` is
  `arrOf` of the butterfly `bflyF` at position `m-1-b` (`bpass_arrOf`). The signed sums `hTNum`
  satisfy `hTNum {p} = bflyF p` (`hTNum_singleton`) and
  `hTNum {p} ∘ hTNum T = hTNum (insert p T)` (`hTNum_insert`). The latter comes from
  `hT {p} ∘ hT T = hT (insert p T)` (`kerOp_comp`) and the injectivity of `gridValC`. So
  `bflyIter` computes `hTNum` of a position block (`bflyIter_arrOf`).
* (M1) the position of a long slot `(i, ℓ-1)` is its index among the long axes
  (`newPos_long_idx`); short slots use `IntForms.newPos_short`.
-/

namespace SubNLogN.Machine.FFT.PrefixAux

open TMFw TMFw.Contracts SubNLogN.Math.Walsh SubNLogN.Math.Common

namespace Math

open SubNLogN.Math.Common.GridInt SubNLogN.Math.Walsh.IntForms

/-! ### (M4) Truncation toward zero composes -/

theorem tdiv_tdiv_of_nonneg (z a b : ℤ) (ha : 0 ≤ a) : (z.tdiv a).tdiv b = z.tdiv (a * b) := by
  rcases le_or_gt 0 z with hz | hz
  · rw [Int.tdiv_eq_ediv_of_nonneg hz, Int.tdiv_eq_ediv_of_nonneg (Int.ediv_nonneg hz ha),
      Int.tdiv_eq_ediv_of_nonneg hz, Int.ediv_ediv_of_nonneg ha]
  · obtain ⟨w, rfl⟩ : ∃ w, z = -w := ⟨-z, by ring⟩
    have hw : 0 ≤ w := by omega
    rw [Int.neg_tdiv, Int.neg_tdiv, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg hw,
      Int.tdiv_eq_ediv_of_nonneg (Int.ediv_nonneg hw ha), Int.tdiv_eq_ediv_of_nonneg hw,
      Int.ediv_ediv_of_nonneg ha]

theorem tdivPow_one_comp (z : ℤ) (n : ℕ) : tdivPow (tdivPow z n) 1 = tdivPow z (n + 1) := by
  unfold tdivPow
  rw [tdiv_tdiv_of_nonneg z (2 ^ n) (2 ^ 1) (by positivity), ← pow_add]

theorem truncShiftC_zero_fun : truncShiftC 0 = id := by
  funext c
  simp [truncShiftC, tdivPow]

theorem truncShiftC_one_comp (n : ℕ) (c : CInt) :
    truncShiftC 1 (truncShiftC n c) = truncShiftC (n + 1) c := by
  simp only [truncShiftC, tdivPow_one_comp]

theorem mapC_truncShiftC_zero (B : List (List CInt)) : mapC (truncShiftC 0) B = B := by
  simp [mapC, truncShiftC_zero_fun]

theorem mapC_mapC (f g : CInt → CInt) (B : List (List CInt)) :
    mapC f (mapC g B) = mapC (f ∘ g) B := by
  simp [mapC, List.map_map]

theorem iter_truncShiftC_one (n : ℕ) (B : List (List CInt)) :
    (mapC (truncShiftC 1))^[n] B = mapC (truncShiftC n) B := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, mapC_truncShiftC_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, mapC_mapC]
    congr 1
    funext c
    exact truncShiftC_one_comp n c

/-! ### (M3) Each exact pass at most doubles the numerators -/

/-- Every component of every coefficient has absolute value at most `c`. -/
def CBound (c : ℤ) (v : List (List CInt)) : Prop :=
  ∀ cs ∈ v, ∀ x ∈ cs, |x.1| ≤ c ∧ |x.2| ≤ c

theorem mem_zipWith_imp {α β γ : Type} {f : α → β → γ} :
    ∀ {l₁ : List α} {l₂ : List β} {x : γ}, x ∈ List.zipWith f l₁ l₂ →
      ∃ a ∈ l₁, ∃ b ∈ l₂, x = f a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l₁, b :: l₂, x, h => by
    rw [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, by simp, b, by simp, rfl⟩
    · obtain ⟨a', ha', b', hb', rfl⟩ := mem_zipWith_imp h
      exact ⟨a', List.mem_cons_of_mem _ ha', b', List.mem_cons_of_mem _ hb', rfl⟩

theorem mem_bev {α : Type} {h M : ℕ} {B : List α} {x : α} (hx : x ∈ bev h M B) : x ∈ B := by
  unfold bev at hx
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.1 hx
  exact List.mem_of_mem_drop (List.mem_of_mem_take hj)

theorem mem_bod {α : Type} {h M : ℕ} {B : List α} {x : α} (hx : x ∈ bod h M B) : x ∈ B := by
  unfold bod at hx
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.1 hx
  exact List.mem_of_mem_drop (List.mem_of_mem_take hj)

theorem mem_bint {α : Type} {h M : ℕ} {X Y : List α} {x : α} (hx : x ∈ bint h M X Y) :
    x ∈ X ∨ x ∈ Y := by
  unfold bint at hx
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.1 hx
  rcases List.mem_append.1 hj with h1 | h1
  · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take h1))
  · exact Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h1))

theorem abs_add_sub_le {a b c : ℤ} (ha : |a| ≤ c) (hb : |b| ≤ c) :
    |a + b| ≤ 2 * c ∧ |a - b| ≤ 2 * c := by
  obtain ⟨ha1, ha2⟩ := abs_le.1 ha
  obtain ⟨hb1, hb2⟩ := abs_le.1 hb
  exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

theorem cbound_zipC {c : ℤ} {f : CInt → CInt → CInt}
    (hf : ∀ a b : CInt, |a.1| ≤ c → |a.2| ≤ c → |b.1| ≤ c → |b.2| ≤ c →
      |(f a b).1| ≤ 2 * c ∧ |(f a b).2| ≤ 2 * c)
    {U V : List (List CInt)} (hU : CBound c U) (hV : CBound c V) : CBound (2 * c) (zipC f U V) := by
  intro cs hcs x hx
  unfold zipC at hcs
  obtain ⟨us, hus, vs, hvs, rfl⟩ := mem_zipWith_imp hcs
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_zipWith_imp hx
  exact hf a b (hU us hus a ha).1 (hU us hus a ha).2 (hV vs hvs b hb).1 (hV vs hvs b hb).2

theorem cbound_bpass {c : ℤ} {h M : ℕ} {B : List (List CInt)} (hB : CBound c B) :
    CBound (2 * c) (bpass h M B) := by
  have hev : CBound c (bev h M B) := fun cs hcs => hB cs (mem_bev hcs)
  have hod : CBound c (bod h M B) := fun cs hcs => hB cs (mem_bod hcs)
  have hadd : CBound (2 * c) (zipC caddC (bev h M B) (bod h M B)) :=
    cbound_zipC (fun a b h1 h2 h3 h4 => ⟨(abs_add_sub_le h1 h3).1, (abs_add_sub_le h2 h4).1⟩)
      hev hod
  have hsub : CBound (2 * c) (zipC csubC (bev h M B) (bod h M B)) :=
    cbound_zipC (fun a b h1 h2 h3 h4 => ⟨(abs_add_sub_le h1 h3).2, (abs_add_sub_le h2 h4).2⟩)
      hev hod
  intro cs hcs
  unfold bpass at hcs
  rcases mem_bint hcs with h1 | h1
  · exact hadd cs h1
  · exact hsub cs h1

theorem cbound_bflyIter {c : ℤ} (m L : ℕ) {B : List (List CInt)} (hB : CBound c B) :
    ∀ j, CBound (2 ^ j * c) (bflyIter m L j B)
  | 0 => by
    show CBound (2 ^ 0 * c) B
    rw [pow_zero, one_mul]
    exact hB
  | j + 1 => by
    show CBound (2 ^ (j + 1) * c) (bpass _ _ (bflyIter m L j B))
    rw [show (2 : ℤ) ^ (j + 1) * c = 2 * (2 ^ j * c) by ring]
    exact cbound_bpass (cbound_bflyIter m L hB j)

theorem cbound_encCube {m r q : ℕ} {z : RArr (Cube m) r} (hz : ArrOnDiskGrid q z) :
    CBound (2 ^ q) (encCube q z) := by
  intro cs hcs x hx
  unfold encCube encArr at hcs
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 hcs
  obtain ⟨k, _, rfl⟩ := List.mem_map.1 hx
  exact abs_gridIntC_le_of_onDiskGrid (hz y k)

theorem fitsTwos_of_abs_le_pow {W e : ℕ} {a : ℤ} (ha : |a| ≤ 2 ^ e) (hW : e + 2 ≤ W) :
    FitsTwos W a := by
  have h1 : (2 : ℤ) ^ e < 2 ^ (W - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  obtain ⟨h2, h3⟩ := abs_le.1 ha
  unfold FitsTwos
  exact ⟨by linarith, by linarith⟩

/-! ### (M2) List-level form of one pass -/

theorem take_drop_range_map {β : Type} (g : ℕ → β) {N a h : ℕ} (hle : a + h ≤ N) :
    (((List.range N).map g).drop a).take h = (List.range h).map (fun t => g (a + t)) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range]
    omega
  · intro t h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]

theorem flatMap_range_blocks {β : Type} {h : ℕ} (hh : 0 < h) (φ : ℕ → ℕ → β) :
    ∀ M : ℕ, (List.range M).flatMap (fun j => (List.range h).map (φ j)) =
      (List.range (M * h)).map (fun i => φ (i / h) (i % h))
  | 0 => by simp
  | M + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_blocks hh φ M, List.flatMap_singleton,
      show (M + 1) * h = M * h + h by ring, List.range_add, List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    have e1 : (M * h + t) / h = M := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hh, Nat.div_eq_of_lt ht, Nat.zero_add]
    have e2 : (M * h + t) % h = t := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
    simp only [Function.comp_apply, e1, e2]

theorem map_range_append {β : Type} (h : ℕ) (α γ : ℕ → β) :
    (List.range h).map α ++ (List.range h).map γ =
      (List.range (2 * h)).map (fun u => if u < h then α u else γ (u - h)) := by
  rw [two_mul, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro u hu
    rw [List.mem_range] at hu
    simp [hu]
  · apply List.map_congr_left
    intro u _
    simp

theorem zipC_map_range {N : ℕ} (f : CInt → CInt → CInt) (ξ η : ℕ → List CInt) :
    zipC f ((List.range N).map ξ) ((List.range N).map η) =
      (List.range N).map (fun i => List.zipWith f (ξ i) (η i)) := by
  unfold zipC
  rw [List.zipWith_map, List.zipWith_self]

theorem bint_range {h M : ℕ} (hh : 0 < h) (ξ η : ℕ → List CInt) :
    bint h M ((List.range (M * h)).map ξ) ((List.range (M * h)).map η) =
      (List.range (M * (2 * h))).map (fun i =>
        if i % (2 * h) < h then ξ (i / (2 * h) * h + i % (2 * h))
        else η (i / (2 * h) * h + (i % (2 * h) - h))) := by
  unfold bint
  rw [List.flatMap_congr (g := fun j => (List.range (2 * h)).map (fun u =>
      if u < h then ξ (j * h + u) else η (j * h + (u - h)))) ?_]
  · exact flatMap_range_blocks (by omega)
      (fun j u => if u < h then ξ (j * h + u) else η (j * h + (u - h))) M
  · intro j hj
    rw [List.mem_range] at hj
    have hle : j * h + h ≤ M * h := by
      have := Nat.mul_le_mul_right h (show j + 1 ≤ M by omega)
      linarith
    rw [take_drop_range_map ξ hle, take_drop_range_map η hle, map_range_append]

/-- One pass on a record array given as `(range (2hM)).map g`: with `i = 2h·j + u`, `u < 2h`, the
record at `i` is `g(2hj + u) + g(2hj + h + u)` for `u < h`, and
`g(2hj + (u-h)) - g(2hj + h + (u-h))` otherwise. -/
theorem bpass_range {h M : ℕ} (hh : 0 < h) (g : ℕ → List CInt) :
    bpass h M ((List.range (2 * h * M)).map g) =
      (List.range (2 * h * M)).map (fun i =>
        if i % (2 * h) < h then
          List.zipWith caddC (g (2 * h * (i / (2 * h)) + i % (2 * h)))
            (g (2 * h * (i / (2 * h)) + h + i % (2 * h)))
        else
          List.zipWith csubC (g (2 * h * (i / (2 * h)) + (i % (2 * h) - h)))
            (g (2 * h * (i / (2 * h)) + h + (i % (2 * h) - h)))) := by
  have hev : bev h M ((List.range (2 * h * M)).map g) =
      (List.range (M * h)).map (fun i => g (2 * (i / h) * h + i % h)) := by
    unfold bev
    rw [List.flatMap_congr (g := fun j => (List.range h).map (fun t => g (2 * j * h + t))) ?_]
    · exact flatMap_range_blocks hh (fun j t => g (2 * j * h + t)) M
    · intro j hj
      rw [List.mem_range] at hj
      have hle : 2 * j * h + h ≤ 2 * h * M := by
        have := Nat.mul_le_mul_right h (show 2 * j + 1 ≤ 2 * M by omega)
        linarith
      rw [take_drop_range_map g hle]
  have hod : bod h M ((List.range (2 * h * M)).map g) =
      (List.range (M * h)).map (fun i => g (2 * (i / h) * h + h + i % h)) := by
    unfold bod
    rw [List.flatMap_congr (g := fun j => (List.range h).map (fun t => g (2 * j * h + h + t))) ?_]
    · exact flatMap_range_blocks hh (fun j t => g (2 * j * h + h + t)) M
    · intro j hj
      rw [List.mem_range] at hj
      have hle : 2 * j * h + h + h ≤ 2 * h * M := by
        have := Nat.mul_le_mul_right h (show 2 * j + 2 ≤ 2 * M by omega)
        linarith
      rw [take_drop_range_map g hle]
  unfold bpass
  rw [hev, hod, zipC_map_range, zipC_map_range, bint_range hh,
    show M * (2 * h) = 2 * h * M by ring]
  apply List.map_congr_left
  intro i _
  have hu2 : i % (2 * h) < 2 * h := Nat.mod_lt _ (by omega)
  generalize i / (2 * h) = j
  generalize i % (2 * h) = u at hu2 ⊢
  by_cases hlt : u < h
  · rw [if_pos hlt, if_pos hlt]
    have e1 : (j * h + u) / h = j := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hh, Nat.div_eq_of_lt hlt, Nat.zero_add]
    have e2 : (j * h + u) % h = u := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    have e3 : 2 * j * h = 2 * h * j := by ring
    simp only [e1, e2, e3]
  · rw [if_neg hlt, if_neg hlt]
    have hlt' : u - h < h := by omega
    have e1 : (j * h + (u - h)) / h = j := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hh, Nat.div_eq_of_lt hlt', Nat.zero_add]
    have e2 : (j * h + (u - h)) % h = u - h := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt']
    have e3 : 2 * j * h = 2 * h * j := by ring
    simp only [e1, e2, e3]

/-! ### (M2) Bits of the paired indices -/

theorem testBit_low {b j u : ℕ} (hu : u < 2 ^ b) : (2 * 2 ^ b * j + u).testBit b = false := by
  have e : 2 * 2 ^ b * j + u = 2 ^ (b + 1) * j + u := by rw [pow_succ]; ring
  have h2 : u < 2 ^ (b + 1) := by rw [pow_succ]; omega
  rw [e, Nat.testBit_two_pow_mul_add j h2 b, if_pos (Nat.lt_add_one b)]
  exact Nat.testBit_lt_two_pow hu

theorem testBit_up {b j u : ℕ} (hu : u < 2 ^ b) (c : ℕ) :
    (2 * 2 ^ b * j + 2 ^ b + u).testBit c =
      if c = b then true else (2 * 2 ^ b * j + u).testBit c := by
  have e1 : 2 * 2 ^ b * j + 2 ^ b + u = 2 ^ (b + 1) * j + (2 ^ b * 1 + u) := by
    rw [pow_succ]; ring
  have e2 : 2 * 2 ^ b * j + u = 2 ^ (b + 1) * j + u := by rw [pow_succ]; ring
  have h1 : 2 ^ b * 1 + u < 2 ^ (b + 1) := by rw [pow_succ]; omega
  have h2 : u < 2 ^ (b + 1) := by rw [pow_succ]; omega
  rw [e1, e2, Nat.testBit_two_pow_mul_add j h1, Nat.testBit_two_pow_mul_add j h2,
    Nat.testBit_two_pow_mul_add 1 hu]
  by_cases hcb : c = b
  · rw [if_pos hcb, hcb, if_pos (Nat.lt_add_one b), if_neg (Nat.lt_irrefl b), Nat.sub_self]
    decide
  · rw [if_neg hcb]
    by_cases hc : c < b
    · rw [if_pos (show c < b + 1 by omega), if_pos hc, if_pos (show c < b + 1 by omega)]
    · rw [if_neg (show ¬ c < b + 1 by omega), if_neg (show ¬ c < b + 1 by omega)]

theorem cube_low {m b : ℕ} (hb : b < m) (j : ℕ) {u : ℕ} (hu : u < 2 ^ b) :
    cubeOfNat m (2 * 2 ^ b * j + u) ⟨m - 1 - b, by omega⟩ = false := by
  show (2 * 2 ^ b * j + u).testBit (m - 1 - (m - 1 - b)) = false
  rw [show m - 1 - (m - 1 - b) = b by omega]
  exact testBit_low hu

theorem cube_up {m b : ℕ} (hb : b < m) (j : ℕ) {u : ℕ} (hu : u < 2 ^ b) :
    cubeOfNat m (2 * 2 ^ b * j + 2 ^ b + u) =
      Function.update (cubeOfNat m (2 * 2 ^ b * j + u)) ⟨m - 1 - b, by omega⟩ true := by
  funext q
  by_cases hq : q = ⟨m - 1 - b, by omega⟩
  · subst hq
    rw [Function.update_self]
    show (2 * 2 ^ b * j + 2 ^ b + u).testBit (m - 1 - (m - 1 - b)) = true
    rw [show m - 1 - (m - 1 - b) = b by omega, testBit_up hu, if_pos rfl]
  · rw [Function.update_of_ne hq]
    show (2 * 2 ^ b * j + 2 ^ b + u).testBit (m - 1 - (q : ℕ)) =
      (2 * 2 ^ b * j + u).testBit (m - 1 - (q : ℕ))
    have hqb : m - 1 - (q : ℕ) ≠ b := by
      intro h
      apply hq
      apply Fin.ext
      show (q : ℕ) = m - 1 - b
      have := q.isLt
      omega
    rw [testBit_up hu, if_neg hqb]

/-! ### (M2) Passes on stored cube arrays -/

/-- The stored array of numerators `F`, records in increasing index order. -/
def arrOf {m r : ℕ} (F : Cube m → Fin r → CInt) : List (List CInt) :=
  (List.range (2 ^ m)).map fun i => (List.finRange r).map (F (cubeOfNat m i))

theorem encCube_eq_arrOf {m r : ℕ} (q : ℕ) (z : RArr (Cube m) r) :
    encCube q z = arrOf (fun y k => gridIntC q (z y k)) := by
  unfold encCube encArr cubeAddrs arrOf
  rw [List.map_map]
  rfl

theorem mapC_arrOf {m r : ℕ} (f : CInt → CInt) (F : Cube m → Fin r → CInt) :
    mapC f (arrOf F) = arrOf (fun y k => f (F y k)) := by
  unfold mapC arrOf
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, List.map_map]
  rfl

/-- The exact butterfly at position `p` on numerators: `A + B` at the address with `x_p = 0`,
`A - B` at the address with `x_p = 1` (`A`, `B` the records at `x_p = 0`, `x_p = 1`). -/
def bflyF {m r : ℕ} (p : Fin m) (F : Cube m → Fin r → CInt) (x : Cube m) (k : Fin r) : CInt :=
  if x p then csubC (F (Function.update x p false) k) (F x k)
  else caddC (F x k) (F (Function.update x p true) k)

theorem update_false_of {m : ℕ} {y : Cube m} {p : Fin m} (h : y p = false) :
    Function.update y p false = y := by
  rw [← h]
  exact Function.update_eq_self p y

/-- One exact pass on index bit `b` is the butterfly at position `m-1-b`. -/
theorem bpass_arrOf {m r b M : ℕ} (hb : b < m) (hM : 2 * 2 ^ b * M = 2 ^ m)
    (F : Cube m → Fin r → CInt) :
    bpass (2 ^ b) M (arrOf F) = arrOf (bflyF ⟨m - 1 - b, by omega⟩ F) := by
  unfold arrOf
  rw [← hM, bpass_range (Nat.two_pow_pos b)]
  apply List.map_congr_left
  intro i _
  have hdm := Nat.div_add_mod i (2 * 2 ^ b)
  have hu2 : i % (2 * 2 ^ b) < 2 * 2 ^ b := Nat.mod_lt _ (by positivity)
  generalize i / (2 * 2 ^ b) = j at hdm ⊢
  generalize i % (2 * 2 ^ b) = u at hdm hu2 ⊢
  rw [← hdm]
  by_cases hlt : u < 2 ^ b
  · rw [if_pos hlt, cube_up hb j hlt, List.zipWith_map, List.zipWith_self]
    apply List.map_congr_left
    intro k _
    simp [bflyF, cube_low hb j hlt]
  · rw [if_neg hlt]
    have hlt' : u - 2 ^ b < 2 ^ b := by omega
    have hi : 2 * 2 ^ b * j + u = 2 * 2 ^ b * j + 2 ^ b + (u - 2 ^ b) := by omega
    rw [hi, cube_up hb j hlt', List.zipWith_map, List.zipWith_self]
    apply List.map_congr_left
    intro k _
    have hy := update_false_of (cube_low hb j hlt')
    simp [bflyF, Function.update_idem, hy]

/-! ### (M2) Signed sums `hTNum`: one position, empty set, composition -/

theorem hTNum_empty {m r : ℕ} (F : Cube m → Fin r → CInt) : hTNum ∅ F = F := by
  funext x k
  have hfilt : Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ (∅ : Finset (Fin m)) → y j = x j) =
      {x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      not_false_eq_true, forall_const, Finset.mem_singleton]
    exact ⟨fun h => funext h, fun h j => h ▸ rfl⟩
  unfold hTNum
  rw [hfilt, Finset.sum_singleton, Finset.sum_singleton]
  simp

theorem hTNum_singleton {m r : ℕ} (p : Fin m) (F : Cube m → Fin r → CInt) (x : Cube m)
    (k : Fin r) : hTNum {p} F x k = bflyF p F x k := by
  have hfilt : Finset.univ.filter (fun y : Cube m => ∀ j, j ∉ ({p} : Finset (Fin m)) → y j = x j) =
      {Function.update x p true, Function.update x p false} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Finset.mem_insert]
    constructor
    · intro hy
      cases hyp : y p
      · right
        funext j
        by_cases hj : j = p
        · subst hj; rw [Function.update_self, hyp]
        · rw [Function.update_of_ne hj, hy j hj]
      · left
        funext j
        by_cases hj : j = p
        · subst hj; rw [Function.update_self, hyp]
        · rw [Function.update_of_ne hj, hy j hj]
    · rintro (rfl | rfl) j hj
      · exact Function.update_of_ne hj _ _
      · exact Function.update_of_ne hj _ _
  have hne : Function.update x p true ≠ Function.update x p false := by
    intro h
    have := congrFun h p
    simp at this
  unfold hTNum bflyF
  rw [hfilt, Finset.sum_pair hne, Finset.sum_pair hne]
  cases hxp : x p
  · have hx := update_false_of hxp
    simp [Finset.filter_singleton, hxp, hx, caddC]
    constructor <;> ring
  · have hx : Function.update x p true = x := by
      rw [← hxp]
      exact Function.update_eq_self p x
    simp [Finset.filter_singleton, hxp, hx, csubC]
    constructor <;> ring

theorem hT_insert_comp {m r : ℕ} {p : Fin m} {T : Finset (Fin m)} (hp : p ∉ T)
    (z : RArr (Cube m) r) : hT {p} (hT T z) = hT (insert p T) z := by
  rw [hT_eq_kerOp, hT_eq_kerOp, hT_eq_kerOp, kerOp_comp]
  congr 1
  funext j
  unfold hKer
  by_cases hj : j = p
  · subst hj
    simp [hp]
  · simp [hj]

theorem hTNum_insert {m r : ℕ} {p : Fin m} {T : Finset (Fin m)} (hp : p ∉ T)
    (F : Cube m → Fin r → CInt) : hTNum {p} (hTNum T F) = hTNum (insert p T) F := by
  funext x k
  apply gridValC_injective (T.card + 1)
  have h1 := hT_gridValC T.card {p} (hTNum T F) x k
  have h2 : (fun y i => gridValC T.card (hTNum T F y i)) = hT T (fun y i => gridValC 0 (F y i)) := by
    funext y i
    rw [hT_gridValC 0 T F y i, Nat.zero_add]
  have h3 := hT_gridValC 0 (insert p T) F x k
  rw [Finset.card_singleton] at h1
  rw [Finset.card_insert_of_notMem hp, Nat.zero_add] at h3
  rw [← h1, ← h3, h2, hT_insert_comp hp]

/-! ### (M2) Position blocks and the iterated passes -/

theorem posBlock_zero (m s : ℕ) : posBlock m s 0 = ∅ := by
  ext p
  simp only [posBlock, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, not_and, not_lt, Nat.add_zero]
  intro h
  exact h

theorem card_posBlock {m s n : ℕ} (h : s + n ≤ m) : (posBlock m s n).card = n := by
  have e : (posBlock m s n).map Fin.valEmbedding = Finset.Ico s (s + n) := by
    ext x
    simp only [posBlock, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, Nat.card_Ico]
  omega

theorem notMem_posBlock {m s n : ℕ} (p : Fin m) (hp : (p : ℕ) = s) :
    p ∉ posBlock m (s + 1) n := by
  simp only [posBlock, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt]
  intro h
  omega

theorem insert_posBlock {m s n : ℕ} (p : Fin m) (hp : (p : ℕ) = s) :
    insert p (posBlock m (s + 1) n) = posBlock m s (n + 1) := by
  ext q
  simp only [posBlock, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    by_cases hq : (q : ℕ) = s
    · left
      exact Fin.ext (by omega)
    · right
      exact ⟨by omega, by omega⟩

/-- `j` exact passes on the index bits `L, …, L + j - 1` compute the signed sums `hTNum` over
the position block `[s, s + j)`, `s = m - L - j`. -/
theorem bflyIter_arrOf {m r : ℕ} (L : ℕ) (F : Cube m → Fin r → CInt) :
    ∀ j s, s + j + L = m → bflyIter m L j (arrOf F) = arrOf (hTNum (posBlock m s j) F)
  | 0, s, _ => by
    rw [posBlock_zero, hTNum_empty]
    rfl
  | j + 1, s, hs => by
    have ih := bflyIter_arrOf L F j (s + 1) (by omega)
    have hb : L + j < m := by omega
    have hM : 2 * 2 ^ (L + j) * 2 ^ (m - L - j - 1) = 2 ^ m := by
      rw [← pow_succ', ← pow_add]
      congr 1
      omega
    have hp : ((⟨m - 1 - (L + j), by omega⟩ : Fin m) : ℕ) = s := by
      show m - 1 - (L + j) = s
      omega
    have hfun : bflyF ⟨m - 1 - (L + j), by omega⟩ (hTNum (posBlock m (s + 1) j) F) =
        hTNum {⟨m - 1 - (L + j), by omega⟩} (hTNum (posBlock m (s + 1) j) F) := by
      funext x k
      exact (hTNum_singleton _ _ x k).symm
    show bpass (2 ^ (L + j)) (2 ^ (m - L - j - 1)) (bflyIter m L j (arrOf F)) = _
    rw [ih, bpass_arrOf hb hM, hfun, hTNum_insert (notMem_posBlock _ hp),
      insert_posBlock _ hp]

/-! ### (M1) Positions of the long slots -/

theorem newPos_long_idx {D : ℕ} (ℓ K : ℕ) (a : Fin D → ℕ) (i : Fin D) (hi : a i = ℓ) :
    newPos ℓ K a (i, ℓ - 1) =
      ((List.finRange D).filter (fun i' => decide (a i' = ℓ))).idxOf i := by
  have hmemL : (i, ℓ - 1) ∈
      ((List.finRange D).filter (fun i' => decide (a i' = ℓ))).map (fun i' => (i', ℓ - 1)) :=
    List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_finRange i, by simpa using hi⟩, rfl⟩
  have hmemP : (i, ℓ - 1) ∈ prefixSlots ℓ K a := by
    rw [LayoutPermAux.prefixSlots_eq]
    exact List.mem_append_left _ hmemL
  have hinj : Function.Injective (fun i' : Fin D => (i', ℓ - 1)) := fun x y h => (Prod.mk.inj h).1
  rw [newPos, newSlots, List.idxOf_append_of_mem hmemP, LayoutPermAux.prefixSlots_eq,
    List.idxOf_append_of_mem hmemL, IntForms.idxOf_map_inj hinj]

end Math

/-- **(M1)** For a prefix round (`v < ℓ`, not a chunk round), `roundSet` is a position block. -/
theorem roundSet_eq_posBlock {D : ℕ} (q ℓ K w v : ℕ) (a : Fin D → ℕ)
    (hshape : MidShapeOK q ℓ K w a) (hv : v < ℓ) (hnc : ¬ IsChunkRound ℓ K v) :
    roundSet ℓ K a v = posBlock (addrBits a) (pfS ℓ K a v) (pfN ℓ K a v) := by
  obtain ⟨_, _, hℓ, _, hK1, _, ha, _⟩ := hshape
  ext p
  simp only [roundSet, posBlock, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold pfS pfN
  by_cases hvl : v + 1 = ℓ
  · rw [if_pos hvl, if_pos hvl]
    obtain rfl : v = ℓ - 1 := by omega
    have hlong : ∀ i : Fin D, ℓ - 1 < a i ↔ a i = ℓ := fun i => by rcases ha i with h | h <;> omega
    constructor
    · rintro ⟨i, hi, hpi⟩
      have hai := (hlong i).1 hi
      rw [Math.newPos_long_idx ℓ K a i hai] at hpi
      have hmem : i ∈ (List.finRange D).filter (fun i' => decide (a i' = ℓ)) :=
        List.mem_filter.2 ⟨List.mem_finRange i, by simpa using hai⟩
      have hlt := List.idxOf_lt_length_of_mem hmem
      refine ⟨Nat.zero_le _, ?_⟩
      show (p : ℕ) < 0 + ((List.finRange D).filter (fun i' => decide (a i' = ℓ))).length
      omega
    · rintro ⟨-, hp⟩
      have hlen : (p : ℕ) < ((List.finRange D).filter (fun i' => decide (a i' = ℓ))).length := by
        have hp' : (p : ℕ) < 0 + LayoutPermAux.nLong ℓ a := hp
        unfold LayoutPermAux.nLong at hp'
        omega
      have hmem := List.getElem_mem hlen
      have hai : a ((List.finRange D).filter (fun i' => decide (a i' = ℓ)))[(p : ℕ)] = ℓ := by
        have := (List.mem_filter.1 hmem).2
        simpa using this
      refine ⟨_, (hlong _).2 hai, ?_⟩
      rw [Math.newPos_long_idx ℓ K a _ hai]
      exact List.Nodup.idxOf_getElem ((List.nodup_finRange D).filter _) _ hlen
  · rw [if_neg hvl, if_neg hvl]
    have hv2 : v + 2 ≤ ℓ := by omega
    have hvb : v < layoutB0 ℓ K := by
      by_contra hcon
      exact hnc ⟨by omega, by omega, hv2⟩
    have hall : ∀ i : Fin D, v < a i := fun i => by rcases ha i with h | h <;> omega
    have hpos : ∀ i : Fin D, newPos ℓ K a (i, v) =
        LayoutPermAux.nLong ℓ a + (layoutB0 ℓ K - 1 - v) * D + i := fun i => by
      rw [IntForms.newPos_short ℓ K a i v hvb, IntForms.nLong_eq_longCount]
    simp only [hpos]
    constructor
    · rintro ⟨i, _, hi⟩
      have := i.isLt
      exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨(p : ℕ) - (LayoutPermAux.nLong ℓ a + (layoutB0 ℓ K - 1 - v) * D), by omega⟩,
        hall _, ?_⟩
      show LayoutPermAux.nLong ℓ a + (layoutB0 ℓ K - 1 - v) * D +
        ((p : ℕ) - (LayoutPermAux.nLong ℓ a + (layoutB0 ℓ K - 1 - v) * D)) = p
      omega

/-- **(M2)** `Q_q(H_T z)` for a position block `T = [s, s + n)`: exact butterfly passes on the
index bits `m-s-n, …, m-s-1`, then one truncation toward zero by `2^n`. -/
theorem encCube_truncArr_hT_posBlock {m r : ℕ} (q s n : ℕ) (hsn : s + n ≤ m)
    (z : RArr (Cube m) r) (hz : ArrOnGrid q z) :
    encCube q (truncArr q (hT (posBlock m s n) z)) =
      mapC (truncShiftC n) (bflyIter m (m - s - n) n (encCube q z)) := by
  have hcard : (posBlock m s n).card = n := Math.card_posBlock hsn
  have hiter := Math.bflyIter_arrOf (m - s - n) (fun y k => SubNLogN.Math.Common.GridInt.gridIntC q (z y k)) n s (by omega)
  rw [Math.encCube_eq_arrOf, Math.encCube_eq_arrOf, hiter, Math.mapC_arrOf]
  congr 1
  funext y k
  show SubNLogN.Math.Common.GridInt.gridIntC q (truncC q (hT (posBlock m s n) z y k)) = _
  rw [IntForms.gridIntC_truncC_hT (posBlock m s n) hz, hcard]
  rfl

/-- **(M3)** After `j` exact passes the numerators of a disk-grid array fit `W ≥ q + j + 2` bits. -/
theorem fits_bflyIter {m r : ℕ} (q L j W : ℕ) (hLj : L + j ≤ m) (hW : q + j + 2 ≤ W)
    (z : RArr (Cube m) r) (hz : ArrOnDiskGrid q z) :
    CArrFits W (bflyIter m L j (encCube q z)) := by
  have hB := Math.cbound_bflyIter m L (Math.cbound_encCube hz) j
  intro cs hcs c hc
  obtain ⟨h1, h2⟩ := hB cs hcs c hc
  rw [← pow_add] at h1 h2
  exact ⟨Math.fitsTwos_of_abs_le_pow h1 (by omega), Math.fitsTwos_of_abs_le_pow h2 (by omega)⟩

/-- **(M4)** `n` truncations by `2`, then the identity truncation `2^0`, are one truncation by `2^n`
(truncation toward zero composes). -/
theorem truncShift_iter (n : ℕ) (B : List (List CInt)) :
    mapC (truncShiftC 0) ((mapC (truncShiftC 1))^[n] B) = mapC (truncShiftC n) B := by
  rw [Math.iter_truncShiftC_one, Math.mapC_truncShiftC_zero]

end SubNLogN.Machine.FFT.PrefixAux
