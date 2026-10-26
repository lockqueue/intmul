import Contracts.W9.Pre
import Contracts.W8
import WP.W9s.SpecDefs
import WP.W9s.SpecLemmas

/-!
# WP.W9s.SpecMath — pure spec math for the synthetic FFT (W9s piece [a])

`synL` is the list-level reference of the machine's recursive DIT synthetic FFT: rows with
delimiters, even/odd dealing, a rotation, then entrywise butterflies. This file proves:

* `synL_eq`: `synL` is the snapshot's `computableSyntheticFFTRadix2` (`Δ = 2·c1`);
* `synL_length`, `synL_rows`: shape;
* `synL_width`: magnitudes never grow;
* `out_eq`: the `W9_synFFT` contract output in terms of `synL`.

Key negacyclic-shift lemma: for `s < r`,
`computableNegacyclicDirect r s f` is `rotL s` with the first `s` entries negated, and at `s + r`
the signs are flipped (`SM.negDirect_getD_lt`, `SM.negDirect_getD_add`). Helper lemmas live in
`WP.W9s.SM` (list/array lemmas in `WP.W9s.SpecLemmas`).
-/

namespace WP.W9s

open IntMul IntMul.LevelSync TMFw.Contracts TMFw.Contracts.W9

attribute [local instance 10000] instZeroIntElementary

namespace SM

/-! ## Bit lengths and the rounding halving -/

theorem encodeNat_pos (n : ℕ) (hn : 0 < n) :
    Computability.encodeNat n = decide (n % 2 = 1) :: Computability.encodeNat (n / 2) := by
  obtain ⟨q, h | h⟩ := Nat.even_or_odd' n
  · subst h
    have hq : 0 < q := by omega
    have hne : Computability.encodeNat q ≠ [] := by
      rw [Ne, TMFw.encodeNat_eq_nil_iff]; omega
    have h2 : 2 * q / 2 = q := by omega
    rw [two_mul, TMFw.encodeNat_add, if_neg hne, ← two_mul, h2]
    simp
  · subst h
    have h1 : (2 * q + 1) % 2 = 1 := by omega
    have h2 : (2 * q + 1) / 2 = q := by omega
    rw [two_mul, TMFw.encodeNat_add_add_one, ← two_mul, h2, h1]
    simp

theorem bitLen_zero : bitLen 0 = 0 := by simp [bitLen, TMFw.encodeNat_zero]

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

theorem divRoundPow2_one (z : ℤ) : divRoundPow2 z 1 = (z + 1) / 2 := by
  simp [divRoundPow2]

theorem natAbs_round_lt {x y : ℤ} {M : ℕ} (hx : x.natAbs < M) (hy : y.natAbs < M) :
    ((x + y + 1) / 2).natAbs < M ∧ ((x - y + 1) / 2).natAbs < M := by
  have h1 := Int.natAbs_eq x
  have h2 := Int.natAbs_eq y
  have h3 := Int.natAbs_eq ((x + y + 1) / 2)
  have h4 := Int.natAbs_eq ((x - y + 1) / 2)
  constructor <;> omega

/-- `|⌊(a ± b + 1)/2⌋| ≤ max |a| |b|`: a rounding butterfly keeps the width. -/
theorem bfly_width {w : ℕ} {a g : ℤ × ℤ} (b : Bool) (ha : EntryW w a) (hg : EntryW w g) :
    EntryW w (bfly b a g) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hg1, hg2⟩ := hg
  rw [bitLen_le_iff] at ha1 ha2 hg1 hg2
  have r1 := natAbs_round_lt ha1 hg1
  have r2 := natAbs_round_lt ha2 hg2
  cases b
  · show EntryW w (divRoundPow2 (a.1 + g.1) 1, divRoundPow2 (a.2 + g.2) 1)
    refine ⟨?_, ?_⟩ <;> simp only [divRoundPow2_one, bitLen_le_iff]
    · exact r1.1
    · exact r2.1
  · show EntryW w (divRoundPow2 (a.1 - g.1) 1, divRoundPow2 (a.2 - g.2) 1)
    refine ⟨?_, ?_⟩ <;> simp only [divRoundPow2_one, bitLen_le_iff]
    · exact r1.2
    · exact r2.2

#assert_std_axioms encodeNat_pos bitLen_zero bitLen_pos bitLen_le_iff divRoundPow2_one
  natAbs_round_lt bfly_width

/-! ## The combine step -/

theorem shift_lt {c1 k u r : ℕ} (hc : 2 * c1 * 2 ^ k = r) (hu : u < 2 ^ k) (hr : 0 < r) :
    2 * c1 * u < r := by
  have hc1 : 0 < 2 * c1 := by
    rcases Nat.eq_zero_or_pos (2 * c1) with h | h
    · rw [h, Nat.zero_mul] at hc; omega
    · exact h
  rw [← hc]
  exact (Nat.mul_lt_mul_left hc1).2 hu

theorem syn_size (V r k c1 : ℕ) (P : Array (Array (ℤ × ℤ))) :
    (computableSyntheticFFTRadix2 V r k c1 P).size = 2 ^ k :=
  (computableSyntheticFFTRadix2_size V r k c1 P).1

theorem syn_row (V r k c1 : ℕ) (P : Array (Array (ℤ × ℤ))) (i : ℕ) (hi : i < 2 ^ k) :
    ((computableSyntheticFFTRadix2 V r k c1 P).getD i #[]).size = r := by
  have hs := computableSyntheticFFTRadix2_size V r k c1 P
  have hi' : i < (computableSyntheticFFTRadix2 V r k c1 P).size := by rw [hs.1]; exact hi
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some]
  exact hs.2 ⟨i, hi'⟩

/-- The combine step of `computableSyntheticFFTRadix2` at level `k + 1` (rows `v1 < 2^k` add the
shifted odd half, the other rows subtract it) is `combL (2·c1)`. -/
theorem combine_eq (r k c1 : ℕ) (Y0 Y1 : Array (Array (ℤ × ℤ))) (h0 : Y0.size = 2 ^ k)
    (hr0 : ∀ i, i < 2 ^ k → (Y0.getD i #[]).size = r)
    (hr1 : ∀ i, i < 2 ^ k → (Y1.getD i #[]).size = r) (hc : 2 * c1 * 2 ^ k = r) :
    (Array.ofFn (fun v1 : Fin (2 ^ (k + 1)) =>
      Array.ofFn (fun k2 : Fin r =>
        (divRoundPow2 (((Y0.getD (v1.val % 2 ^ k) #[]).getD k2.val (0, 0)).1 +
            ((computableNegacyclicDirect r (2 * c1 * v1.val)
              (Y1.getD (v1.val % 2 ^ k) #[])).getD k2.val (0, 0)).1) 1,
          divRoundPow2 (((Y0.getD (v1.val % 2 ^ k) #[]).getD k2.val (0, 0)).2 +
            ((computableNegacyclicDirect r (2 * c1 * v1.val)
              (Y1.getD (v1.val % 2 ^ k) #[])).getD k2.val (0, 0)).2) 1)))).toList.map
        Array.toList =
      combL (2 * c1) (Y0.toList.map Array.toList) (Y1.toList.map Array.toList) := by
  have hY0 : (Y0.toList.map Array.toList).length = 2 ^ k := by
    rw [List.length_map, Array.length_toList, h0]
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
  apply list_ext_getD ([] : List (ℤ × ℤ))
  · rw [combL_length, hY0, List.length_map, Array.length_toList, Array.size_ofFn, hpow]
  · intro n hn
    have hn' : n < 2 ^ (k + 1) := by
      rw [List.length_map, Array.length_toList, Array.size_ofFn] at hn; exact hn
    have hn2 : n < 2 * (Y0.toList.map Array.toList).length := by rw [hY0, ← hpow]; exact hn'
    rw [getD_map_toList, getD_ofFn_arr _ n hn',
      getD_combL (2 * c1) (Y0.toList.map Array.toList) (Y1.toList.map Array.toList) n hn2, hY0]
    try dsimp only
    simp only [getD_map_toList]
    by_cases hlt : n < 2 ^ k
    · rw [if_pos hlt, Nat.mod_eq_of_lt hlt]
      apply row_eq r (2 * c1 * n) (2 * c1 * n) false _ _ (hr0 n hlt) (hr1 n hlt)
      intro k2 hk2
      have hs : 2 * c1 * n < r := shift_lt hc hlt (by omega)
      rw [negDirect_getD_lt r (2 * c1 * n) _ (hr1 n hlt) hs k2 hk2]
      by_cases h : k2 < 2 * c1 * n <;> simp [h]
    · have hge : 2 ^ k ≤ n := by omega
      have hu : n - 2 ^ k < 2 ^ k := by omega
      have hmod : n % 2 ^ k = n - 2 ^ k := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hu]
      have e : 2 * c1 * n = 2 * c1 * (n - 2 ^ k) + r := by
        rw [← hc, ← Nat.mul_add, Nat.sub_add_cancel hge]
      rw [if_neg hlt, hmod, e]
      apply row_eq r _ (2 * c1 * (n - 2 ^ k)) true _ _ (hr0 _ hu) (hr1 _ hu)
      intro k2 hk2
      have hs : 2 * c1 * (n - 2 ^ k) < r := shift_lt hc hu (by omega)
      rw [negDirect_getD_add r _ _ (hr1 _ hu) hs k2 hk2]
      by_cases h : k2 < 2 * c1 * (n - 2 ^ k) <;> simp [h]

#assert_std_axioms shift_lt syn_size syn_row combine_eq

end SM

/-! ## `synL` is the snapshot's synthetic FFT -/

theorem synL_eq (V r : ℕ) : ∀ (k c1 : ℕ) (P : Array (Array (ℤ × ℤ))),
    P.size = 2 ^ k → (∀ row ∈ P.toList, row.size = r) → c1 * 2 ^ k = r →
    (computableSyntheticFFTRadix2 V r k c1 P).toList.map Array.toList =
      synL (2 * c1) k (P.toList.map Array.toList)
  | 0, c1, P, hP, hrow, _ => by
    have hP1 : P.size = 1 := by rw [hP, pow_zero]
    have h0 : (P.getD 0 #[]).size = r := hrow _ (SM.getD_mem_toList P 0 (by omega) #[])
    rw [computableSyntheticFFTRadix2, synL]
    apply SM.list_ext_getD ([] : List (ℤ × ℤ))
    · rw [List.length_map, List.length_map, Array.length_toList, Array.length_toList,
        Array.size_ofFn, hP1]
    · intro n hn
      have hn0 : n = 0 := by
        rw [List.length_map, Array.length_toList, Array.size_ofFn] at hn; omega
      subst hn0
      rw [SM.getD_map_toList, SM.getD_map_toList, SM.getD_ofFn_arr _ 0 Nat.zero_lt_one]
      exact SM.ofFn_getD_toList _ r h0 (0, 0)
  | k + 1, c1, P, hP, hrow, hc => by
    have hc' : 2 * c1 * 2 ^ k = r := by rw [← hc, pow_succ]; ring
    have hP2 : P.size = 2 * 2 ^ k := by rw [hP, pow_succ]; omega
    have hErow : ∀ row ∈ (Array.ofFn (fun j1 : Fin (2 ^ k) => P.getD (2 * j1.val) #[])).toList,
        row.size = r := by
      intro row hr
      rw [SM.toList_evens P (2 ^ k) hP2] at hr
      exact hrow row (SM.mem_evensL _ hr)
    have hOrow : ∀ row ∈ (Array.ofFn (fun j1 : Fin (2 ^ k) =>
        P.getD (2 * j1.val + 1) #[])).toList, row.size = r := by
      intro row hr
      rw [SM.toList_odds P (2 ^ k) hP2] at hr
      exact hrow row (SM.mem_oddsL _ hr)
    have ih0 := synL_eq V r k (2 * c1) _ Array.size_ofFn hErow hc'
    have ih1 := synL_eq V r k (2 * c1) _ Array.size_ofFn hOrow hc'
    rw [computableSyntheticFFTRadix2, synL, SM.evensL_map, SM.oddsL_map,
      ← SM.toList_evens P (2 ^ k) hP2, ← SM.toList_odds P (2 ^ k) hP2, ← ih0, ← ih1]
    exact SM.combine_eq r k c1 _ _ (SM.syn_size _ _ _ _ _) (SM.syn_row _ _ _ _ _)
      (SM.syn_row _ _ _ _ _) hc'

#assert_std_axioms synL_eq

namespace SM

/-! ## Shape and width of `synL` -/

theorem synL_length_aux : ∀ (k Δ : ℕ) (X : List (List (ℤ × ℤ))), X.length = 2 ^ k →
    (synL Δ k X).length = 2 ^ k
  | 0, _, _, hX => hX
  | k + 1, Δ, X, hX => by
    have hE : (evensL X).length = 2 ^ k := by rw [evensL_length, hX, pow_succ]; omega
    rw [synL, combL_length, synL_length_aux k (2 * Δ) (evensL X) hE, pow_succ]
    omega

theorem synL_rows_aux (r : ℕ) : ∀ (k Δ : ℕ) (X : List (List (ℤ × ℤ))), X.length = 2 ^ k →
    (∀ row ∈ X, row.length = r) → ∀ row ∈ synL Δ k X, row.length = r
  | 0, _, _, _, hr => hr
  | k + 1, Δ, X, hX, hr => by
    have hE : (evensL X).length = 2 ^ k := by rw [evensL_length, hX, pow_succ]; omega
    have hO : (oddsL X).length = 2 ^ k := by rw [oddsL_length, hX, pow_succ]; omega
    have h0 := synL_rows_aux r k (2 * Δ) (evensL X) hE (fun row h => hr row (mem_evensL X h))
    have h1 := synL_rows_aux r k (2 * Δ) (oddsL X) hO (fun row h => hr row (mem_oddsL X h))
    have l0 := synL_length_aux k (2 * Δ) (evensL X) hE
    have l1 := synL_length_aux k (2 * Δ) (oddsL X) hO
    intro row hrow
    rw [synL] at hrow
    obtain ⟨u, hu, b, rfl⟩ := mem_combL hrow
    have hu1 : u < (synL (2 * Δ) k (oddsL X)).length := by rw [l1]; rw [l0] at hu; exact hu
    have ha := h0 _ (getD_mem_of_lt [] _ u hu)
    have hg := h1 _ (getD_mem_of_lt [] _ u hu1)
    exact zipB_rows ha (by rw [rotL_length]; exact hg)

theorem synL_width_aux (w : ℕ) : ∀ (k Δ : ℕ) (X : List (List (ℤ × ℤ))),
    (∀ row ∈ X, ∀ z ∈ row, EntryW w z) → ∀ row ∈ synL Δ k X, ∀ z ∈ row, EntryW w z
  | 0, _, _, hX => hX
  | k + 1, Δ, X, hX => by
    have h0 := synL_width_aux w k (2 * Δ) (evensL X) (fun row h => hX row (mem_evensL X h))
    have h1 := synL_width_aux w k (2 * Δ) (oddsL X) (fun row h => hX row (mem_oddsL X h))
    intro row hrow z hz
    rw [synL] at hrow
    obtain ⟨u, -, b, rfl⟩ := mem_combL hrow
    obtain ⟨b', a, g, ha, hg, rfl⟩ := mem_zipB b _ _ _ hz
    obtain ⟨ra, hra, hza⟩ := mem_getD _ u a ha
    obtain ⟨rg, hrg, hzg⟩ := mem_getD _ u g (mem_rotL hg)
    exact bfly_width b' (h0 ra hra a hza) (h1 rg hrg g hzg)

#assert_std_axioms synL_length_aux synL_rows_aux synL_width_aux

end SM

theorem synL_length (Δ : ℕ) : ∀ (k : ℕ) (X : List (List (ℤ × ℤ))),
    X.length = 2 ^ k → (synL Δ k X).length = 2 ^ k :=
  fun k X hX => SM.synL_length_aux k Δ X hX

theorem synL_rows (Δ r : ℕ) : ∀ (k : ℕ) (X : List (List (ℤ × ℤ))),
    X.length = 2 ^ k → (∀ row ∈ X, row.length = r) → ∀ row ∈ synL Δ k X, row.length = r :=
  fun k X hX hr => SM.synL_rows_aux r k Δ X hX hr

theorem synL_width (w Δ : ℕ) : ∀ (k : ℕ) (X : List (List (ℤ × ℤ))),
    (∀ row ∈ X, ∀ z ∈ row, EntryW w z) → ∀ row ∈ synL Δ k X, ∀ z ∈ row, EntryW w z :=
  fun k X hX => SM.synL_width_aux w k Δ X hX

#assert_std_axioms synL_length synL_rows synL_width

namespace SM

/-! ## `w9Q` is the identity (`gRescale q q = id`) -/

theorem read2D_of_lt (A : Array (Array (ℤ × ℤ))) (i j : ℕ) (hi : i < A.size)
    (hj : j < A[i].size) : read2D A i j = A[i][j] := by
  unfold read2D
  rw [dif_pos hi]
  try dsimp only
  rw [dif_pos hj]

theorem mat_ext (A B : Array (Array (ℤ × ℤ))) (n1 n2 : ℕ) (hA : A.size = n1)
    (hB : B.size = n1) (hrA : ∀ i, i < n1 → (A.getD i #[]).size = n2)
    (hrB : ∀ i, i < n1 → (B.getD i #[]).size = n2)
    (h : ∀ i j, i < n1 → j < n2 → read2D A i j = read2D B i j) : A = B := by
  apply Array.ext
  · rw [hA, hB]
  · intro i hiA hiB
    have hi : i < n1 := by omega
    have hsA : A[i].size = n2 := by
      have := hrA i hi
      rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hiA, Option.getD_some] at this
    have hsB : B[i].size = n2 := by
      have := hrB i hi
      rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hiB, Option.getD_some] at this
    apply Array.ext
    · rw [hsA, hsB]
    · intro j hjA hjB
      have hj : j < n2 := by omega
      have := h i j hi hj
      rwa [read2D_of_lt A i j hiA hjA, read2D_of_lt B i j hiB hjB] at this

theorem w9Q_id (pSub t1 r : ℕ) (syn : Array (Array (ℤ × ℤ))) (hs : syn.size = t1)
    (hr : ∀ i, i < t1 → (syn.getD i #[]).size = r) : w9Q pSub t1 r syn = syn := by
  unfold w9Q
  simp only [IntMulTM.Contracts.W8.gRescale_self]
  apply mat_ext _ _ t1 r (runScan2DWithSteps_fst_size _ _ _) hs
    (fun i hi => runScan2DWithSteps_row_size _ _ _ i hi) hr
  intro i j hi hj
  exact read2D_runScan2DWithSteps_of_lt t1 r _ hi hj

#assert_std_axioms read2D_of_lt mat_ext w9Q_id

end SM

/-- The `W9_synFFT` output (`w9Q ∘ w9Syn`) in terms of `synL`. -/
theorem out_eq (h : PreHdr) (Pm : Array (Array (ℤ × ℤ))) (hD : PreDims h) (hs : Pm.size = h.t1)
    (hr : ∀ row ∈ Pm.toList, row.size = h.r) :
    matSyms (w9Q h.pSub h.t1 h.r (w9Syn h.t1 h.r Pm)) =
      blkE (synL (2 * (h.r / h.t1)) h.mt1 (Pm.toList.map Array.toList)).flatten := by
  obtain ⟨ht, hr', _, h2⟩ := hD
  have hdiv : h.r / h.t1 * 2 ^ h.mt1 = h.r := by
    rw [← ht]
    exact Nat.div_mul_cancel (by rw [ht, hr']; exact pow_dvd_pow 2 h2)
  have hsz : Pm.size = 2 ^ h.mt1 := by rw [hs]; exact ht
  have heq := synL_eq h.t1 h.r h.mt1 (h.r / h.t1) Pm hsz hr hdiv
  have hsyn : w9Syn h.t1 h.r Pm =
      computableSyntheticFFTRadix2 h.t1 h.r h.mt1 (h.r / h.t1) Pm := rfl
  have hsz' : (w9Syn h.t1 h.r Pm).size = h.t1 := by rw [hsyn, SM.syn_size]; exact ht.symm
  have hrow' : ∀ i, i < h.t1 → ((w9Syn h.t1 h.r Pm).getD i #[]).size = h.r := by
    intro i hi
    rw [hsyn]
    exact SM.syn_row _ _ _ _ _ i (by rw [← ht]; exact hi)
  rw [SM.w9Q_id h.pSub h.t1 h.r _ hsz' hrow', hsyn, ← heq]
  rfl

#assert_std_axioms synL_eq synL_length synL_rows synL_width out_eq

end WP.W9s
