/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPhaseDefs
import SubNLogN.Machine.Arith.Field

/-!
# Layer driver phase scan, pure core (`Machine/Layer/DrvPhaseScanMath.lean`)

**Scope (honest summary).** Machine-free facts behind the kernel of `DrvPhaseScanStmt`
(`Machine/Layer/DrvPhaseDefs.lean:63`); everything is proved (no `sorry`).
* `sadd k1 k2 c xs ys`: the bit-serial signed adder `k1·X + k2·Y` with an integer carry;
  `sadd_twosBits`: on two's-complement fields it computes `twosBits w (c + k1·x + k2·y)`;
  `sadd_snoc`/`scarry_snoc`: one more step; `scarry_range`: the carry stays in `[-2, 1]`.
* `extBit`: reading a `w`-bit field with sign extension; `map_extBit`: the first `n` read bits are
  `twosBits n z` (`FitsTwos w z`), for every `n` (extension and truncation).
* `kRe`, `kIm`, `gEO`: the coefficients of `z ↦ i^e·z` (times `1 - i` if `o`), `gEO_eq`.
* `selStep`, `selRun`, `selRun_count`: the counter scan of the selected bits (`selCount`).
-/

namespace SubNLogN.Machine.Layer.DrvPhaseScanAux

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-! ## The signed two-input bit-serial adder -/

/-- The column sum `c + k1·x + k2·y` of one adder step. -/
def sstep (k1 k2 c : ℤ) (x y : Bool) : ℤ := c + k1 * (x.toNat : ℤ) + k2 * (y.toNat : ℤ)

/-- Output bits of the signed adder `k1·X + k2·Y` from carry `c` (LSB-first lists). -/
def sadd (k1 k2 : ℤ) : ℤ → List Bool → List Bool → List Bool
  | c, x :: xs, y :: ys =>
    decide (sstep k1 k2 c x y % 2 = 1) :: sadd k1 k2 (sstep k1 k2 c x y / 2) xs ys
  | _, _, _ => []

/-- The carry of the signed adder after the two lists. -/
def scarry (k1 k2 : ℤ) : ℤ → List Bool → List Bool → ℤ
  | c, x :: xs, y :: ys => scarry k1 k2 (sstep k1 k2 c x y / 2) xs ys
  | c, _, _ => c

theorem sadd_snoc (k1 k2 : ℤ) : ∀ (c : ℤ) (xs ys : List Bool) (x y : Bool),
    xs.length = ys.length →
    sadd k1 k2 c (xs ++ [x]) (ys ++ [y]) =
      sadd k1 k2 c xs ys ++ [decide (sstep k1 k2 (scarry k1 k2 c xs ys) x y % 2 = 1)]
  | c, [], [], x, y, _ => by simp [sadd, scarry] <;> rfl
  | _, [], _ :: _, _, _, h => by simp at h
  | _, _ :: _, [], _, _, h => by simp at h
  | c, a :: xs, b :: ys, x, y, h => by
    simp only [List.cons_append, sadd, scarry]
    rw [sadd_snoc k1 k2 _ xs ys x y (by simpa using h)]
    simp <;> rfl

theorem scarry_snoc (k1 k2 : ℤ) : ∀ (c : ℤ) (xs ys : List Bool) (x y : Bool),
    xs.length = ys.length →
    scarry k1 k2 c (xs ++ [x]) (ys ++ [y]) = sstep k1 k2 (scarry k1 k2 c xs ys) x y / 2
  | c, [], [], x, y, _ => by simp [scarry]
  | _, [], _ :: _, _, _, h => by simp at h
  | _, _ :: _, [], _, _, h => by simp at h
  | c, a :: xs, b :: ys, x, y, h => by
    simp only [List.cons_append, scarry]
    exact scarry_snoc k1 k2 _ xs ys x y (by simpa using h)

/-- **The signed adder on two's-complement fields.** -/
theorem sadd_twosBits (k1 k2 : ℤ) : ∀ (w : ℕ) (c x y : ℤ),
    sadd k1 k2 c (twosBits w x) (twosBits w y) = twosBits w (c + k1 * x + k2 * y)
  | 0, _, _, _ => rfl
  | w + 1, c, x, y => by
    rw [K1.twosBits_succ w x, K1.twosBits_succ w y, K1.twosBits_succ w]
    simp only [sadd]
    have hx : x = 2 * (x / 2) + ((decide (x % 2 = 1)).toNat : ℤ) := by
      rw [← K1.emod_two_eq_toNat]; omega
    have hy : y = 2 * (y / 2) + ((decide (y % 2 = 1)).toNat : ℤ) := by
      rw [← K1.emod_two_eq_toNat]; omega
    generalize decide (x % 2 = 1) = a at hx ⊢
    generalize decide (y % 2 = 1) = b at hy ⊢
    have key : c + k1 * x + k2 * y =
        2 * (k1 * (x / 2)) + 2 * (k2 * (y / 2)) + sstep k1 k2 c a b := by
      unfold sstep; linear_combination k1 * hx + k2 * hy
    rw [sadd_twosBits k1 k2 w, key]
    generalize k1 * (x / 2) = P
    generalize k2 * (y / 2) = Q
    generalize sstep k1 k2 c a b = s
    simp only [List.cons.injEq]
    constructor
    · simp only [decide_eq_decide]; omega
    · congr 1; omega

/-- With coefficients in `{-1, 0, 1}`, the carry stays in `[-2, 1]`. -/
theorem sstep_div_range {k1 k2 c : ℤ} (h1 : -1 ≤ k1 ∧ k1 ≤ 1) (h2 : -1 ≤ k2 ∧ k2 ≤ 1)
    (hc : -2 ≤ c ∧ c ≤ 1) (x y : Bool) :
    -2 ≤ sstep k1 k2 c x y / 2 ∧ sstep k1 k2 c x y / 2 ≤ 1 := by
  unfold sstep
  have hx : (x.toNat : ℤ) = 0 ∨ (x.toNat : ℤ) = 1 := by cases x <;> simp
  have hy : (y.toNat : ℤ) = 0 ∨ (y.toNat : ℤ) = 1 := by cases y <;> simp
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> omega

theorem scarry_range {k1 k2 : ℤ} (h1 : -1 ≤ k1 ∧ k1 ≤ 1) (h2 : -1 ≤ k2 ∧ k2 ≤ 1) :
    ∀ (c : ℤ) (xs ys : List Bool), -2 ≤ c ∧ c ≤ 1 →
      -2 ≤ scarry k1 k2 c xs ys ∧ scarry k1 k2 c xs ys ≤ 1
  | c, x :: xs, y :: ys, hc => by
    simp only [scarry]
    exact scarry_range h1 h2 _ xs ys (sstep_div_range h1 h2 hc x y)
  | c, [], _, hc => by simpa [scarry] using hc
  | c, _ :: _, [], hc => by simpa [scarry] using hc

/-! ## Reading a field with sign extension -/

/-- Bit `j` of a `w`-bit field read with sign extension (past the field: the sign). -/
def extBit (w : ℕ) (z : ℤ) (j : ℕ) : Bool := (twosBits w z).getD j (decide (z < 0))

theorem map_range_getD (L : List Bool) (d : Bool) :
    ∀ n, (List.range n).map (fun j => L.getD j d) = (L ++ List.replicate n d).take n := by
  intro n
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    rw [List.getD_eq_getElem?_getD]
    by_cases hi : i < L.length
    · rw [List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_append_left hi]
    · rw [List.getElem?_eq_none (by omega), Option.getD_none,
        List.getElem_append_right (by omega), List.getElem_replicate]

/-- **Sign extension and truncation**: reading `n` bits of a `w`-bit field gives the `n`-bit
field of the same value. -/
theorem map_extBit {w : ℕ} {z : ℤ} (hw : 1 ≤ w) (hz : FitsTwos w z) (n : ℕ) :
    (List.range n).map (extBit w z) = twosBits n z := by
  unfold extBit
  rw [map_range_getD]
  by_cases hn : n ≤ w
  · rw [List.take_append_of_le_length (by rw [K1.length_twosBits]; exact hn),
      Arith.twosBits_take n w hn]
  · obtain ⟨k, rfl⟩ : ∃ k, n = w + k := ⟨n - w, by omega⟩
    rw [Arith.twosBits_ext w k z _ (Arith.ediv_pow_w_of_fits hz hw),
      List.take_append, K1.length_twosBits, List.take_of_length_le (by rw [K1.length_twosBits]; omega),
      show w + k - w = k by omega, List.take_replicate, min_eq_left (by omega)]

/-! ## The coefficients of the phase map -/

/-- Coefficients `(k_re, k_im)` of the real part of `i^e·(a + bi)`, times `1 - i` if `o`. -/
def kRe (e : ℕ) (o : Bool) : ℤ × ℤ :=
  if o then
    (if e % 4 = 0 then (1, 1) else if e % 4 = 1 then (1, -1) else if e % 4 = 2 then (-1, -1)
      else (-1, 1))
  else
    (if e % 4 = 0 then (1, 0) else if e % 4 = 1 then (0, -1) else if e % 4 = 2 then (-1, 0)
      else (0, 1))

/-- Coefficients of the imaginary part. -/
def kIm (e : ℕ) (o : Bool) : ℤ × ℤ :=
  if o then
    (if e % 4 = 0 then (-1, 1) else if e % 4 = 1 then (1, 1) else if e % 4 = 2 then (1, -1)
      else (-1, -1))
  else
    (if e % 4 = 0 then (0, 1) else if e % 4 = 1 then (1, 0) else if e % 4 = 2 then (0, -1)
      else (-1, 0))

/-- The coefficient map of one record: `z ↦ i^e·z`, then times `1 - i` if `o`. -/
def gEO (e : ℕ) (o : Bool) (z : CInt) : CInt := if o then omiC (rotC e z) else rotC e z

theorem gEO_eq (e : ℕ) (o : Bool) (z : CInt) :
    gEO e o z = ((kRe e o).1 * z.1 + (kRe e o).2 * z.2,
      (kIm e o).1 * z.1 + (kIm e o).2 * z.2) := by
  obtain ⟨a, b⟩ := z
  have h4 : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
  unfold gEO kRe kIm rotC omiC
  generalize e % 4 = r at h4 ⊢
  interval_cases r <;> cases o <;> refine Prod.ext ?_ ?_ <;> simp <;> ring

theorem kRe_range (e : ℕ) (o : Bool) :
    (-1 ≤ (kRe e o).1 ∧ (kRe e o).1 ≤ 1) ∧ (-1 ≤ (kRe e o).2 ∧ (kRe e o).2 ≤ 1) := by
  unfold kRe
  split_ifs <;> simp

theorem kIm_range (e : ℕ) (o : Bool) :
    (-1 ≤ (kIm e o).1 ∧ (kIm e o).1 ≤ 1) ∧ (-1 ≤ (kIm e o).2 ∧ (kIm e o).2 ≤ 1) := by
  unfold kIm
  split_ifs <;> simp

theorem rotC_mod (e : ℕ) (z : CInt) : rotC (e % 4) z = rotC e z := by
  simp [rotC]

theorem gEO_mod (e : ℕ) (o : Bool) (z : CInt) : gEO (e % 4) o z = gEO e o z := by
  simp [gEO, rotC_mod]

/-- `phaseRec` is `gEO` of the record's exponent, coefficient by coefficient. -/
theorem phaseRec_eq (S K ρ D c o x : ℕ) (cs : List CInt) :
    phaseRec S K ρ D c o x cs = cs.map (gEO (selCount S K ρ D x + c) (decide (o = 1))) := by
  unfold phaseRec gEO
  by_cases h : o = 1 <;> simp [h]

/-! ## The selected-bit scan -/

/-- One step of the selected-bit scan over the bits of `y` (LSB first). The state `(T, J, n)`:
`T` positions until the next selected one, `J` selected positions left, `n` the count. -/
def selStep (K : ℕ) (st : ℕ × ℕ × ℕ) (b : Bool) : ℕ × ℕ × ℕ :=
  if st.1 = 0 then (K - 1, st.2.1 - 1, if 0 < st.2.1 ∧ b = true then st.2.2 + 1 else st.2.2)
  else (st.1 - 1, st.2.1, st.2.2)

/-- The scan over a bit list. -/
def selRun (K : ℕ) (st : ℕ × ℕ × ℕ) (bs : List Bool) : ℕ × ℕ × ℕ := bs.foldl (selStep K) st

theorem length_filter_eq_sum (p : ℕ → Bool) :
    ∀ l : List ℕ, (l.filter p).length = (l.map fun j => (p j).toNat).sum
  | [] => rfl
  | a :: l => by
    by_cases h : p a = true
    · simp [h, length_filter_eq_sum p l]; ring
    · simp [h, length_filter_eq_sum p l]

/-- **Scan count.** From `(T, J, n)`, the scan adds the number of `j < J` with bit `T + K·j`
set. -/
theorem selRun_count (K : ℕ) (hK : 1 ≤ K) : ∀ (bs : List Bool) (T J n : ℕ),
    (selRun K (T, J, n) bs).2.2 =
      n + ((List.range J).map fun j => (bs.getD (T + K * j) false).toNat).sum
  | [], T, J, n => by
    simp [selRun]
  | b :: bs, T, J, n => by
    have hrun : selRun K (T, J, n) (b :: bs) = selRun K (selStep K (T, J, n) b) bs := rfl
    rw [hrun]
    by_cases hT : T = 0
    · subst hT
      have hs : selStep K (0, J, n) b =
          (K - 1, J - 1, if 0 < J ∧ b = true then n + 1 else n) := by
        simp [selStep]
      rw [hs, selRun_count K hK bs]
      rcases Nat.eq_zero_or_pos J with hJ | hJ
      · subst hJ; simp
      · obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
        rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
        have hfun : ((fun j => ((b :: bs).getD (0 + K * j) false).toNat) ∘ Nat.succ) =
            fun j => (bs.getD (K - 1 + K * j) false).toNat := by
          funext j
          simp only [Function.comp_apply, Nat.zero_add]
          rw [show K * (j + 1) = (K - 1 + K * j) + 1 by
            rw [Nat.mul_succ]; omega]
          rfl
        rw [hfun]
        simp only [Nat.zero_add, Nat.mul_zero, List.getD_cons_zero, Nat.add_sub_cancel]
        cases b <;> simp <;> ring
    · have hs : selStep K (T, J, n) b = (T - 1, J, n) := by
        simp [selStep, hT]
      rw [hs, selRun_count K hK bs]
      congr 2
      refine List.map_congr_left (fun j _ => ?_)
      rw [show T + K * j = (T - 1 + K * j) + 1 by omega]
      rfl

/-- Bits of `encodeNat`: `getD` is `testBit`. -/
theorem encodeNat_getD : ∀ (n i : ℕ), (encodeNat n).getD i false = n.testBit i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [encodeNat_zero]
      · have hne : encodeNat m ≠ [] := fun h => by
          rw [encodeNat_eq_nil_iff] at h; omega
        rw [show 2 * m = m + m by ring, encodeNat_add, if_neg hne]
        rcases i with _ | i
        · simp [Nat.testBit_zero]; omega
        · rw [List.getD_cons_succ, ih m (by omega) i, ← Nat.testBit_div_two]
          congr 1; omega
    · rw [show 2 * m + 1 = m + m + 1 by ring, encodeNat_add_add_one]
      rcases i with _ | i
      · simp [Nat.testBit_zero]; omega
      · rw [List.getD_cons_succ, ih m (by omega) i, ← Nat.testBit_div_two]
        congr 1; omega

/-- **The scan computes `selCount`.** On the bits of `y = x / S`, from `(ρ, D, n)`, the scan
ends with count `n + selCount S K ρ D x`. -/
theorem selRun_selCount (S K ρ D x n : ℕ) (hK : 1 ≤ K) :
    (selRun K (ρ, D, n) (encodeNat (x / S))).2.2 = n + selCount S K ρ D x := by
  rw [selRun_count K hK, selCount, length_filter_eq_sum]
  congr 2
  refine List.map_congr_left (fun j _ => ?_)
  rw [encodeNat_getD]

end SubNLogN.Machine.Layer.DrvPhaseScanAux
