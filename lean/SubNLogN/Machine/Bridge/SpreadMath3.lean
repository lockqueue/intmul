/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadMath2
import SubNLogN.Machine.Bridge.SpreadParts

/-!
# K5 spreading, pure lemmas III (`Bridge/SpreadMath3.lean`)

The extended line and the value bounds of the line primitive. Everything is proved.

* `ccF_window`: on the extended line `X ++ take (W-1) X` with the reversed tap record, output
  `W - 1 + m` of the linear convolution is the windowed cyclic sum of `lineOut`;
* `lineOut_eq`: `lineOut` is the rotation of the overlap-add outputs `lineConv` (drop `W - 1`);
* `fits_ccF`: the convolution values fit the slot (`s`-bit two's complement);
* `ccF_add_pend`: a block value plus the pending tail is the convolution of the extended prefix.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine Computability
open scoped BigOperators

/-! ## The extended line -/

theorem getD_ext_line (X : List CInt) (t W i : ℕ) (hX : X.length = t) (hWt : W ≤ t + 1)
    (hi : i < t + (W - 1)) :
    (X ++ X.take (W - 1)).getD i 0 = X.getD (i % t) 0 := by
  by_cases h : i < t
  · rw [Nat.mod_eq_of_lt h, List.getD_append _ _ _ _ (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega), hX]
    have hmod : i % t = i - t := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos (by omega)]

theorem getD_reverse_W (F : List CInt) (W c : ℕ) (hF : F.length = W) (hc : c < W) :
    F.reverse.getD (W - 1 - c) 0 = F.getD c 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega), hF,
    show W - 1 - (W - 1 - c) = c by omega]

/-- **Window identity of the extended line.** -/
theorem ccF_window (X F : List CInt) (t W m : ℕ) (hX : X.length = t) (hF : F.length = W)
    (hW : 1 ≤ W) (hWt : W ≤ t) (hm : m < t) :
    ccF (X ++ X.take (W - 1)) F.reverse (W - 1 + m) =
      ∑ c ∈ Finset.range W, cmulC (X.getD ((m + c) % t) 0) (F.getD c 0) := by
  unfold ccF
  rw [show W - 1 + m + 1 = m + W by omega, Finset.sum_range_add]
  have h1 : ∑ i ∈ Finset.range m, cmulC ((X ++ X.take (W - 1)).getD i 0)
      (F.reverse.getD (W - 1 + m - i) 0) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [List.getD_eq_default F.reverse 0 (by simp [hF]; omega), cmulC_zero_right]
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun c hc => ?_
  simp only [Finset.mem_range] at hc
  rw [getD_ext_line X t W (m + c) hX (by omega) (by omega),
    show W - 1 + m - (m + c) = W - 1 - c by omega,
    getD_reverse_W F W c hF hc]

/-- The `t + W - 1` overlap-add outputs of a line (extended line, reversed tap record). -/
def lineConv (t W : ℕ) (X F : List CInt) : List CInt :=
  (List.range (t + W - 1)).map (ccF (X ++ X.take (W - 1)) F.reverse)

theorem length_lineConv (t W : ℕ) (X F : List CInt) : (lineConv t W X F).length = t + W - 1 := by
  simp [lineConv]

/-- **Rotation**: `lineOut` is the last `a₀` outputs of `lineConv` followed by the `t - a₀`
outputs after the first `W - 1`, each rounded. -/
theorem lineOut_eq (q t W a0 : ℕ) (X F : List CInt) (hX : X.length = t) (hF : F.length = W)
    (hW : 1 ≤ W) (hWt : W ≤ t) (ha0 : a0 ≤ t) :
    lineOut q t W a0 X F =
      (((lineConv t W X F).drop (W - 1 + (t - a0))) ++
        (((lineConv t W X F).drop (W - 1)).take (t - a0))).map (roundHalfUpShiftC q) := by
  apply List.ext_getElem
  · simp only [lineOut, List.length_map, List.length_range, List.length_append, List.length_drop,
      List.length_take, length_lineConv]
    omega
  · intro a h1 h2
    have ha : a < t := by simpa [lineOut] using h1
    simp only [lineOut, List.getElem_map, List.getElem_range]
    congr 1
    rw [List.getElem_append]
    split_ifs with hlt
    · simp only [List.length_drop, length_lineConv] at hlt
      simp only [lineConv, List.getElem_drop, List.getElem_map, List.getElem_range]
      rw [show W - 1 + (t - a0) + a = W - 1 + (t - a0 + a) by omega,
        ccF_window X F t W _ hX hF hW hWt (by omega)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [show a + (t - a0) + c = t - a0 + a + c by omega]
    · simp only [List.length_drop, length_lineConv, not_lt] at hlt
      simp only [lineConv, List.getElem_take, List.getElem_drop, List.getElem_map,
        List.getElem_range, List.length_drop, List.length_map, List.length_range]
      rw [show W - 1 + (a - (t + W - 1 - (W - 1 + (t - a0)))) = W - 1 + (a - a0) by omega,
        ccF_window X F t W _ hX hF hW hWt (by omega)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [show a + (t - a0) + c = (a - a0 + c) + t by omega, Nat.add_mod_right]

/-! ## Value bounds -/

theorem abs_le_of_fits {w : ℕ} {z : ℤ} (h : FitsTwos w z) : |z| ≤ 2 ^ (w - 1) := by
  unfold FitsTwos at h
  rw [abs_le]
  constructor <;> omega

theorem cmulC_abs_le {wI wT : ℕ} (x y : CInt) (hx : FitsTwos wI x.1 ∧ FitsTwos wI x.2)
    (hy : FitsTwos wT y.1 ∧ FitsTwos wT y.2) :
    |(cmulC x y).1| ≤ 2 * (2 ^ (wI - 1) * 2 ^ (wT - 1)) ∧
      |(cmulC x y).2| ≤ 2 * (2 ^ (wI - 1) * 2 ^ (wT - 1)) := by
  have a1 := abs_le_of_fits hx.1
  have a2 := abs_le_of_fits hx.2
  have b1 := abs_le_of_fits hy.1
  have b2 := abs_le_of_fits hy.2
  have p11 : |x.1 * y.1| ≤ 2 ^ (wI - 1) * 2 ^ (wT - 1) := by
    rw [abs_mul]; exact mul_le_mul a1 b1 (abs_nonneg _) (by positivity)
  have p22 : |x.2 * y.2| ≤ 2 ^ (wI - 1) * 2 ^ (wT - 1) := by
    rw [abs_mul]; exact mul_le_mul a2 b2 (abs_nonneg _) (by positivity)
  have p12 : |x.1 * y.2| ≤ 2 ^ (wI - 1) * 2 ^ (wT - 1) := by
    rw [abs_mul]; exact mul_le_mul a1 b2 (abs_nonneg _) (by positivity)
  have p21 : |x.2 * y.1| ≤ 2 ^ (wI - 1) * 2 ^ (wT - 1) := by
    rw [abs_mul]; exact mul_le_mul a2 b1 (abs_nonneg _) (by positivity)
  constructor
  · show |x.1 * y.1 - x.2 * y.2| ≤ _
    calc _ ≤ |x.1 * y.1| + |x.2 * y.2| := abs_sub _ _
      _ ≤ _ := by linarith
  · show |x.1 * y.2 + x.2 * y.1| ≤ _
    calc _ ≤ |x.1 * y.2| + |x.2 * y.1| := abs_add_le _ _
      _ ≤ _ := by linarith

theorem sum_window_le_int (n L : ℕ) (M : ℤ) (hM0 : 0 ≤ M) (g : ℕ → ℤ)
    (h0 : ∀ i, L ≤ n - i → g i = 0) (hM : ∀ i, g i ≤ M) :
    ∑ i ∈ Finset.range (n + 1), g i ≤ L * M := by
  rw [← Finset.sum_filter_of_ne (p := fun i => n - i < L) (fun i _ hi => by
    by_contra h; exact hi (h0 i (by omega)))]
  calc _ ≤ ∑ _i ∈ (Finset.range (n + 1)).filter (fun i => n - i < L), M :=
        Finset.sum_le_sum fun i _ => hM i
    _ = (_ : ℕ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ L * M := mul_le_mul_of_nonneg_right (by exact_mod_cast card_window_le n L) hM0

/-- **Slot fit**: every convolution value fits `s`-bit two's complement when
`|G| · 2^{wI+wT-1} < 2^{s-1}`. -/
theorem fits_ccF {wI wT s : ℕ} (E G : List CInt) (n : ℕ)
    (hE : ∀ x ∈ E, FitsTwos wI x.1 ∧ FitsTwos wI x.2)
    (hG : ∀ y ∈ G, FitsTwos wT y.1 ∧ FitsTwos wT y.2)
    (hs : (G.length : ℤ) * (2 * (2 ^ (wI - 1) * 2 ^ (wT - 1))) < 2 ^ (s - 1)) :
    FitsTwos s (ccF E G n).1 ∧ FitsTwos s (ccF E G n).2 := by
  have key : ∀ (f : CInt → ℤ), (∀ x y : CInt, (FitsTwos wI x.1 ∧ FitsTwos wI x.2) →
      (FitsTwos wT y.1 ∧ FitsTwos wT y.2) → |f (cmulC x y)| ≤ 2 * (2 ^ (wI - 1) * 2 ^ (wT - 1))) →
      (∀ a b : CInt, f (a + b) = f a + f b) → f 0 = 0 →
      (∀ (S : Finset ℕ) (g : ℕ → CInt), f (∑ i ∈ S, g i) = ∑ i ∈ S, f (g i)) →
      FitsTwos s (f (ccF E G n)) := by
    intro f hf _ hf0 hsum
    unfold ccF
    rw [hsum]
    have hb : |∑ i ∈ Finset.range (n + 1), f (cmulC (E.getD i 0) (G.getD (n - i) 0))| ≤
        (G.length : ℤ) * (2 * (2 ^ (wI - 1) * 2 ^ (wT - 1))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_window_le_int n G.length _ (by positivity)
        _ (fun i hi => ?_) (fun i => hf _ _ (fits_getD hE i) (fits_getD hG (n - i))))
      rw [List.getD_eq_default G 0 (by omega), cmulC_zero_right, hf0, abs_zero]
    unfold FitsTwos
    rw [abs_le] at hb
    constructor <;> linarith [hb.1, hb.2]
  refine ⟨key Prod.fst (fun x y hx hy => (cmulC_abs_le x y hx hy).1) (fun _ _ => rfl) rfl
    (fun S g => Prod.fst_sum), key Prod.snd (fun x y hx hy => (cmulC_abs_le x y hx hy).2)
    (fun _ _ => rfl) rfl (fun S g => Prod.snd_sum)⟩

/-- A block value plus the pending tail of the prefix is the convolution of the extended prefix. -/
theorem ccF_add_pend (Epre B G : List CInt) (n : ℕ) (hn : n < B.length + G.length - 1) :
    ccF B G n + (pend Epre G).getD n 0 = ccF (Epre ++ B) G (Epre.length + n) := by
  have h := congrArg (fun l => l[n]?) (blockV_pend Epre B G)
  simp only [blockV, List.getElem?_map, List.getElem?_range hn, Option.map_some] at h
  exact Option.some.inj h

end SubNLogN.Machine.Bridge.SpreadAux
