import WP.W9c.PureSpec

/-!
# WP.W9c.PureGlueB — the machine's block digits are the snapshot's block products
(split 4: `GlueChunks`)

* `chunks_eq`: with enough fuel, `chunks W n x` is the list of the `⌈|x|/W⌉` windows
  `(x.drop (b·W)).take W`.
* `pack_window`: the snapshot's zero-padded quantized block `blockF … b` and the machine's
  (unpadded) quantized window have the same signed Kronecker pack (trailing zeros pack to `0`).
* With `k = s - 1 + 1` the radix `2^k` is the snapshot's `2·2^(s-1)`, and `outLenOf W taps` is the
  snapshot's output length (the block has length `W ≥ 1`).
-/

namespace WP.W9c

open TMFw TMFw.Contracts IntMul

theorem cnt_drop (W m : ℕ) (hW : 1 ≤ W) (hm : 1 ≤ m) :
    (m - W + W - 1) / W + 1 = (m + W - 1) / W := by
  by_cases hmW : W ≤ m
  · have e1 : m - W + W - 1 = m - 1 := by omega
    have e2 : m + W - 1 = m - 1 + W := by omega
    rw [e1, e2, Nat.add_div_right _ (by omega)]
  · have e1 : m - W + W - 1 = W - 1 := by omega
    rw [e1, Nat.div_eq_of_lt (by omega)]
    symm
    exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- `chunks` with enough fuel: the windows of `x`. -/
theorem chunks_eq (W : ℕ) (hW : 1 ≤ W) : ∀ (n : ℕ) (x : List ℤ), (x.length + W - 1) / W ≤ n →
    chunks W n x = (List.range ((x.length + W - 1) / W)).map fun b => (x.drop (b * W)).take W
  | 0, x, hc => by
    have hx : x.length = 0 := by
      by_contra hne
      have : 1 ≤ (x.length + W - 1) / W :=
        (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      omega
    rw [List.length_eq_zero_iff.mp hx]
    simp [chunks, Nat.div_eq_of_lt (show W - 1 < W by omega)]
  | n + 1, [], _ => by
    simp [chunks, Nat.div_eq_of_lt (show W - 1 < W by omega)]
  | n + 1, v :: vs, hc => by
    have hlen : 1 ≤ (v :: vs).length := by simp
    have hcd := cnt_drop W (v :: vs).length hW hlen
    have hc' : (((v :: vs).drop W).length + W - 1) / W ≤ n := by
      rw [List.length_drop]
      omega
    have ih := chunks_eq W hW n ((v :: vs).drop W) hc'
    rw [List.length_drop] at ih
    rw [← hcd, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [chunks]
    rw [ih]
    simp only [Nat.zero_mul, List.drop_zero, List.cons.injEq, true_and]
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp, Nat.succ_eq_add_one, List.drop_drop]
    congr 2
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- The zero-padded window and the unpadded window have the same pack. -/
theorem pack_window (M : ℤ) (f : ℤ → ℤ) (x : List ℤ) : ∀ (n o : ℕ),
    packSignedKronecker M ((List.range n).map fun a =>
        if o + a < x.length then f (x.getD (o + a) 0) else 0) =
      packSignedKronecker M (((x.drop o).take n).map f)
  | 0, o => by simp [packSignedKronecker]
  | n + 1, o => by
    have ih := pack_window M f x n (o + 1)
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have hfun : ((fun a => if o + a < x.length then f (x.getD (o + a) 0) else 0) ∘ Nat.succ) =
        fun a => if o + 1 + a < x.length then f (x.getD (o + 1 + a) 0) else 0 := by
      funext a
      simp only [Function.comp, Nat.succ_eq_add_one, show o + (a + 1) = o + 1 + a by omega]
    rw [hfun]
    by_cases ho : o < x.length
    · rw [List.drop_eq_getElem_cons ho, List.take_succ_cons, List.map_cons]
      simp only [packSignedKronecker, Nat.add_zero, if_pos ho]
      rw [ih, List.getD_eq_getElem _ _ ho]
    · have hd : x.drop o = [] := List.drop_eq_nil_of_le (by omega)
      have hd' : x.drop (o + 1) = [] := List.drop_eq_nil_of_le (by omega)
      rw [hd'] at ih
      rw [hd]
      simp only [packSignedKronecker, Nat.add_zero, if_neg ho, List.take_nil, List.map_nil] at ih ⊢
      rw [ih]
      ring

/-- **GlueChunks.** -/
theorem glueChunks_holds : GlueChunks := by
  intro s p_in q m1 r taps x hr hx _
  have hW1 : 1 ≤ Wf m1 r := by
    show 1 ≤ min (2 * m1 + 1) r
    omega
  have hNB : NB m1 r = (x.length + Wf m1 r - 1) / Wf m1 r := by
    rw [hx]
    rfl
  have hfuel : (x.length + Wf m1 r - 1) / Wf m1 r ≤ x.length := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    have : x.length ≤ x.length * Wf m1 r := Nat.le_mul_of_pos_right _ (by omega)
    have hcomm := Nat.mul_comm x.length (Wf m1 r)
    omega
  unfold passDigits
  rw [chunks_eq (Wf m1 r) hW1 x.length x hfuel, ← hNB, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  have hk : s - 1 + 1 - 1 = s - 1 := Nat.add_sub_cancel _ _
  have h2 : ((2 ^ (s - 1 + 1) : ℕ) : ℤ) = 2 * ((2 ^ (s - 1) : ℕ) : ℤ) := by
    push_cast
    ring
  have hlen : (blockF p_in q m1 r x b).length = Wf m1 r := by simp [blockF]
  have hne : blockF p_in q m1 r x b ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
    omega
  have hblk : blockF p_in q m1 r x b = (List.range (Wf m1 r)).map fun a =>
      if b * Wf m1 r + a < x.length then gQuantizeCoordToScale p_in q (x.getD (b * Wf m1 r + a) 0)
      else 0 := by
    rw [hx]
    rfl
  have hpack : packSignedKronecker ((2 ^ (s - 1 + 1) : ℕ) : ℤ) (blockF p_in q m1 r x b) =
      packSignedKronecker ((2 ^ (s - 1 + 1) : ℕ) : ℤ)
        (((x.drop (b * Wf m1 r)).take (Wf m1 r)).map (gQuantizeCoordToScale p_in q)) := by
    rw [hblk]
    exact pack_window _ _ x (Wf m1 r) (b * Wf m1 r)
  show unpackSignedKronecker ((2 ^ (s - 1 + 1 - 1) : ℕ) : ℤ) (outLenOf (Wf m1 r) taps)
      (packSignedKronecker ((2 ^ (s - 1 + 1) : ℕ) : ℤ)
          (((x.drop (b * Wf m1 r)).take (Wf m1 r)).map (gQuantizeCoordToScale p_in q)) *
        packSignedKronecker ((2 ^ (s - 1 + 1) : ℕ) : ℤ) taps) =
    unpackSignedKronecker ((2 ^ (s - 1) : ℕ) : ℤ)
      (if blockF p_in q m1 r x b = [] then 0 else if taps = [] then (blockF p_in q m1 r x b).length
        else (blockF p_in q m1 r x b).length + taps.length - 1)
      (packSignedKronecker (2 * ((2 ^ (s - 1) : ℕ) : ℤ)) (blockF p_in q m1 r x b) *
        packSignedKronecker (2 * ((2 ^ (s - 1) : ℕ) : ℤ)) taps)
  rw [hk, if_neg hne, hlen, ← h2, hpack]
  rfl

#assert_std_axioms cnt_drop chunks_eq pack_window glueChunks_holds

end WP.W9c
