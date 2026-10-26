/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadIface

/-!
# K5 spreading, pure lemmas II (`Bridge/SpreadMath2.lean`)

Value-level facts used by the block step of the line primitive. Everything is proved.

* streams: `encodeNat_drop`, `bitsVal_bitsLE`, `sval_encodeNat`, `bitsVal_twosBits`;
* digits of a packed number: `pack_div_pow`, `pack_digit`;
* the eight signed partial products of a complex product (`rePairs`, `imPairs`):
  `ccF_re_eq`, `ccF_im_eq`;
* the slot value of the lockstep adder: `slotL`, `slot_gen`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine Computability
open scoped BigOperators

/-! ## Streams -/

theorem encodeNat_drop : ∀ (s z : ℕ), (encodeNat z).drop s = encodeNat (z / 2 ^ s)
  | 0, z => by simp
  | s + 1, z => by
    rw [← List.drop_tail, (encodeNat_head_tail z).2, encodeNat_drop s (z / 2),
      Nat.div_div_eq_div_mul, ← pow_succ']

theorem bitsVal_bitsLE : ∀ (s d : ℕ), bitsVal (bitsLE s d) = d % 2 ^ s
  | 0, d => by simp [bitsLE, Nat.mod_one]
  | s + 1, d => by
    rw [K1.bitsLE_succ, bitsVal_cons, bitsVal_bitsLE s (d / 2), pow_succ', Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one d with h | h <;> simp [Nat.testBit_zero, h] <;> omega

theorem sval_encodeNat (σ : Bool) (s z : ℕ) :
    sval s (σ, encodeNat z) = (if σ then 1 else -1) * ((z % 2 ^ s : ℕ) : ℤ) := by
  unfold sval
  rw [padTake_encodeNat, bitsVal_bitsLE]

theorem padTake_append_of_length {s : ℕ} (A B : List Bool) (h : A.length = s) :
    padTake (A ++ B) s = A := by
  unfold padTake
  rw [List.append_assoc, List.take_left' h]

theorem bitsVal_twosBits (s : ℕ) (z : ℤ) : (bitsVal (twosBits s z) : ℤ) = z % 2 ^ s := by
  have hp : (0 : ℤ) < 2 ^ s := by positivity
  have h0 : 0 ≤ z % 2 ^ s := Int.emod_nonneg z hp.ne'
  have h1 : z % 2 ^ s < 2 ^ s := Int.emod_lt_of_pos z hp
  have h2 : (z % 2 ^ s).toNat < 2 ^ s := by
    have h3 : ((z % 2 ^ s).toNat : ℤ) < ((2 ^ s : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0]; exact_mod_cast h1
    exact_mod_cast h3
  unfold twosBits
  rw [bitsVal_bitsLE, Nat.mod_eq_of_lt h2, Int.toNat_of_nonneg h0]

theorem twosBits_congr {s : ℕ} {a b : ℤ} (h : a % 2 ^ s = b % 2 ^ s) :
    twosBits s a = twosBits s b := by
  unfold twosBits
  rw [h]

/-! ## Digits of a packed number -/

theorem pack_div_pow (s : ℕ) : ∀ (l : List ℕ) (n : ℕ), (∀ d ∈ l, d < 2 ^ s) →
    pack s l / 2 ^ (s * n) = pack s (l.drop n)
  | l, 0, _ => by simp
  | [], n + 1, _ => by simp [pack]
  | d :: l, n + 1, h => by
    have hd : d < 2 ^ s := h d (by simp)
    rw [List.drop_succ_cons, ← pack_div_pow s l n (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      show s * (n + 1) = s + s * n by ring, pow_add, ← Nat.div_div_eq_div_mul, pack,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hd, zero_add]

theorem pack_mod_pow (s : ℕ) (l : List ℕ) (h : ∀ d ∈ l, d < 2 ^ s) :
    pack s l % 2 ^ s = l.headD 0 := by
  cases l with
  | nil => simp [pack]
  | cons d l =>
    rw [pack, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h d (by simp))]
    rfl

theorem headD_drop (l : List ℕ) (n : ℕ) : (l.drop n).headD 0 = l.getD n 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases hl : l.drop n with
  | nil =>
    have hlen : l.length ≤ n := by
      have := congrArg List.length hl
      simp at this
      omega
    simp [List.getElem?_eq_none hlen]
  | cons a t =>
    have : l[n]? = some a := by rw [← List.head?_drop, hl]; rfl
    simp [this]

/-- Digit `n` of a packed list whose entries fit the slot. -/
theorem pack_digit (s : ℕ) (l : List ℕ) (h : ∀ d ∈ l, d < 2 ^ s) (n : ℕ) :
    pack s l / 2 ^ (s * n) % 2 ^ s = l.getD n 0 := by
  rw [pack_div_pow s l n h, pack_mod_pow s _ (fun d hd => h d (List.mem_of_mem_drop hd)),
    headD_drop]

/-! ## The eight signed partial products -/

/-- Part pairs `(data part, filter part)` of the real component in slot-source order (sources
`0-3` positive, `4-7` negative): `Re(x·y) = x_re y_re - x_im y_im`. -/
def rePairs : Fin 8 → Fin 4 × Fin 4 :=
  ![(0, 0), (1, 1), (2, 3), (3, 2), (0, 1), (1, 0), (2, 2), (3, 3)]

/-- Part pairs of the imaginary component: `Im(x·y) = x_re y_im + x_im y_re`. -/
def imPairs : Fin 8 → Fin 4 × Fin 4 :=
  ![(0, 2), (1, 3), (2, 0), (3, 1), (0, 3), (1, 2), (2, 1), (3, 0)]

/-- The sign of slot source `j` as an integer. -/
def sgnZ (j : Fin 9) : ℤ := if slotSign j then 1 else -1

theorem cpart_zero (w : ℕ) (k : Fin 4) : cpart w k 0 = 0 := by
  fin_cases k <;> simp [cpart, lowPart, sgnPart]

theorem re_split_aux (x1 x2 y1 y2 : ℤ) (p1 n1 p2 n2 q1 m1 q2 m2 : ℕ) (h1 : x1 = p1 - n1)
    (h2 : x2 = p2 - n2) (h3 : y1 = q1 - m1) (h4 : y2 = q2 - m2) :
    x1 * y1 - x2 * y2 = ((p1 * q1 : ℕ) : ℤ) + ((n1 * m1 : ℕ) : ℤ) + ((p2 * m2 : ℕ) : ℤ) +
      ((n2 * q2 : ℕ) : ℤ) - ((p1 * m1 : ℕ) : ℤ) - ((n1 * q1 : ℕ) : ℤ) - ((p2 * q2 : ℕ) : ℤ) -
      ((n2 * m2 : ℕ) : ℤ) := by
  subst h1 h2 h3 h4; push_cast; ring

theorem im_split_aux (x1 x2 y1 y2 : ℤ) (p1 n1 p2 n2 q1 m1 q2 m2 : ℕ) (h1 : x1 = p1 - n1)
    (h2 : x2 = p2 - n2) (h3 : y1 = q1 - m1) (h4 : y2 = q2 - m2) :
    x1 * y2 + x2 * y1 = ((p1 * q2 : ℕ) : ℤ) + ((n1 * m2 : ℕ) : ℤ) + ((p2 * q1 : ℕ) : ℤ) +
      ((n2 * m1 : ℕ) : ℤ) - ((p1 * m2 : ℕ) : ℤ) - ((n1 * q2 : ℕ) : ℤ) - ((p2 * m1 : ℕ) : ℤ) -
      ((n2 * q1 : ℕ) : ℤ) := by
  subst h1 h2 h3 h4; push_cast; ring

theorem cmulC_re_split {wI wT : ℕ} (x y : CInt) (hx1 : FitsTwos wI x.1) (hx2 : FitsTwos wI x.2)
    (hy1 : FitsTwos wT y.1) (hy2 : FitsTwos wT y.2) :
    (cmulC x y).1 = ∑ j : Fin 8, sgnZ j.castSucc *
      ((cpart wI (rePairs j).1 x * cpart wT (rePairs j).2 y : ℕ) : ℤ) := by
  rw [show (cmulC x y).1 = x.1 * y.1 - x.2 * y.2 from rfl,
    re_split_aux _ _ _ _ _ _ _ _ _ _ _ _ (split_eq hx1) (split_eq hx2) (split_eq hy1)
      (split_eq hy2)]
  simp [Fin.sum_univ_eight, rePairs, cpart, sgnZ, slotSign]
  ring

theorem cmulC_im_split {wI wT : ℕ} (x y : CInt) (hx1 : FitsTwos wI x.1) (hx2 : FitsTwos wI x.2)
    (hy1 : FitsTwos wT y.1) (hy2 : FitsTwos wT y.2) :
    (cmulC x y).2 = ∑ j : Fin 8, sgnZ j.castSucc *
      ((cpart wI (imPairs j).1 x * cpart wT (imPairs j).2 y : ℕ) : ℤ) := by
  rw [show (cmulC x y).2 = x.1 * y.2 + x.2 * y.1 from rfl,
    im_split_aux _ _ _ _ _ _ _ _ _ _ _ _ (split_eq hx1) (split_eq hx2) (split_eq hy1)
      (split_eq hy2)]
  simp [Fin.sum_univ_eight, imPairs, cpart, sgnZ, slotSign]
  ring

theorem fits_getD {w : ℕ} {l : List CInt} (h : ∀ x ∈ l, FitsTwos w x.1 ∧ FitsTwos w x.2)
    (i : ℕ) : FitsTwos w (l.getD i 0).1 ∧ FitsTwos w (l.getD i 0).2 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none =>
    have hp : (0 : ℤ) < 2 ^ (w - 1) := by positivity
    exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  | some x => simpa using h x (List.mem_of_getElem? hi)

theorem getD_map_cpart (w : ℕ) (k : Fin 4) (l : List CInt) (i : ℕ) :
    (l.map (cpart w k)).getD i 0 = cpart w k (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [cpart_zero]

theorem ccF_re_eq {wI wT : ℕ} (B G : List CInt) (n : ℕ)
    (hB : ∀ x ∈ B, FitsTwos wI x.1 ∧ FitsTwos wI x.2)
    (hG : ∀ y ∈ G, FitsTwos wT y.1 ∧ FitsTwos wT y.2) :
    (ccF B G n).1 = ∑ j : Fin 8, sgnZ j.castSucc *
      ((convL (B.map (cpart wI (rePairs j).1)) (G.map (cpart wT (rePairs j).2))).getD n 0 : ℤ) := by
  unfold ccF
  rw [Prod.fst_sum]
  simp only [convL_getD, getD_map_cpart, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact cmulC_re_split _ _ (fits_getD hB i).1 (fits_getD hB i).2 (fits_getD hG (n - i)).1
    (fits_getD hG (n - i)).2

theorem ccF_im_eq {wI wT : ℕ} (B G : List CInt) (n : ℕ)
    (hB : ∀ x ∈ B, FitsTwos wI x.1 ∧ FitsTwos wI x.2)
    (hG : ∀ y ∈ G, FitsTwos wT y.1 ∧ FitsTwos wT y.2) :
    (ccF B G n).2 = ∑ j : Fin 8, sgnZ j.castSucc *
      ((convL (B.map (cpart wI (imPairs j).1)) (G.map (cpart wT (imPairs j).2))).getD n 0 : ℤ) := by
  unfold ccF
  rw [Prod.snd_sum]
  simp only [convL_getD, getD_map_cpart, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact cmulC_im_split _ _ (fits_getD hB i).1 (fits_getD hB i).2 (fits_getD hG (n - i)).1
    (fits_getD hG (n - i)).2

/-! ## The slot value of the lockstep adder -/

/-- The packed product of the part pair `p` of a block `B` and a filter `G`. -/
def zP (s wI wT : ℕ) (B G : List CInt) (p : Fin 4 × Fin 4) : ℕ :=
  pack s (B.map (cpart wI p.1)) * pack s (G.map (cpart wT p.2))

/-- The bit stream of a list of tail values (one `s`-bit two's complement field each). -/
def tailBits (s : ℕ) (f : CInt → ℤ) (T : List CInt) : List Bool :=
  (T.map fun x => twosBits s (f x)).flatten

/-- The nine slot-pass streams at slot `n`: the eight product streams (after `n` slots) and the
tail stream (after `n` fields). -/
def slotL (s wI wT n : ℕ) (B G T : List CInt) (pairs : Fin 8 → Fin 4 × Fin 4) (f : CInt → ℤ) :
    Fin 9 → List Bool :=
  fun j => if h : (j : ℕ) < 8 then encodeNat (zP s wI wT B G (pairs ⟨j, h⟩) / 2 ^ (s * n))
    else tailBits s f (T.drop n)

theorem bitsVal_replicate_false : ∀ s : ℕ, bitsVal (List.replicate s false) = 0
  | 0 => rfl
  | s + 1 => by rw [List.replicate_succ, bitsVal_cons, bitsVal_replicate_false s]; rfl

theorem tail_sval (s : ℕ) (f : CInt → ℤ) (hf : f 0 = 0) (T : List CInt) (n : ℕ) :
    sval s (true, tailBits s f (T.drop n)) % 2 ^ s = f (T.getD n 0) % 2 ^ s := by
  unfold sval
  simp only [if_true, one_mul]
  by_cases hn : n < T.length
  · rw [List.drop_eq_getElem_cons hn, tailBits, List.map_cons, List.flatten_cons,
      padTake_append_of_length _ _ (K1.length_twosBits _ _), bitsVal_twosBits, Int.emod_emod,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
  · have hn' : T.length ≤ n := by omega
    rw [List.drop_eq_nil_of_le hn', List.getD_eq_default _ _ hn', hf]
    simp [tailBits, padTake, bitsVal_replicate_false]

/-- **Slot value**: the lockstep adder on the nine slot streams outputs the `s`-bit two's
complement of the signed digit sum plus the tail value. -/
theorem slot_gen {s wI wT : ℕ} (B G T : List CInt) (n : ℕ) (pairs : Fin 8 → Fin 4 × Fin 4)
    (f : CInt → ℤ) (hf : f 0 = 0) (V : ℤ)
    (hdig : ∀ j : Fin 8, ∀ d ∈ convL (B.map (cpart wI (pairs j).1)) (G.map (cpart wT (pairs j).2)),
      d < 2 ^ s)
    (hV : V = ∑ j : Fin 8, sgnZ j.castSucc *
      ((convL (B.map (cpart wI (pairs j).1)) (G.map (cpart wT (pairs j).2))).getD n 0 : ℤ)) :
    serialRun s 0 (slotSrcs (slotL s wI wT n B G T pairs f)) =
      twosBits s (V + f (T.getD n 0)) := by
  rw [serialRun_correct, zero_add]
  apply twosBits_congr
  rw [slotSrcs, List.map_map, ← Fin.sum_univ_def, Fin.sum_univ_castSucc]
  have hj : ∀ j : Fin 8,
      (sval s ∘ fun j => (slotSign j, slotL s wI wT n B G T pairs f j)) j.castSucc =
      sgnZ j.castSucc *
        ((convL (B.map (cpart wI (pairs j).1)) (G.map (cpart wT (pairs j).2))).getD n 0 : ℤ) := by
    intro j
    simp only [Function.comp, slotL, Fin.val_castSucc, j.isLt, dif_pos, Fin.eta]
    rw [sval_encodeNat, zP, pack_mul, pack_digit _ _ (hdig j)]
    rfl
  have hl : (sval s ∘ fun j => (slotSign j, slotL s wI wT n B G T pairs f j)) (Fin.last 8) =
      sval s (true, tailBits s f (T.drop n)) := by
    simp [slotL, slotSign]
  rw [Finset.sum_congr rfl (fun j _ => hj j), ← hV, hl, Int.add_emod, tail_sval s f hf T n,
    ← Int.add_emod]

theorem cpart_le (w : ℕ) (k : Fin 4) (x : CInt) : cpart w k x ≤ 2 ^ (w - 1) := by
  fin_cases k <;> simp [cpart]
  · exact (lowPart_lt _ _).le
  · exact sgnPart_le _ _
  · exact (lowPart_lt _ _).le
  · exact sgnPart_le _ _

theorem card_window_le (n L : ℕ) :
    ((Finset.range (n + 1)).filter (fun i => n - i < L)).card ≤ L := by
  calc ((Finset.range (n + 1)).filter (fun i => n - i < L)).card
      ≤ ((Finset.range L).image (fun c => n - c)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        simp only [Finset.mem_image, Finset.mem_range]
        exact ⟨n - i, hi.2, by omega⟩
    _ ≤ (Finset.range L).card := Finset.card_image_le
    _ = L := Finset.card_range L

/-- A convolution-type sum with at most `L` nonzero terms, each `≤ M`. -/
theorem sum_window_le (n L M : ℕ) (g : ℕ → ℕ) (h0 : ∀ i, L ≤ n - i → g i = 0)
    (hM : ∀ i, g i ≤ M) : ∑ i ∈ Finset.range (n + 1), g i ≤ L * M := by
  rw [← Finset.sum_filter_of_ne (p := fun i => n - i < L) (fun i _ hi => by
    by_contra h; exact hi (h0 i (by omega)))]
  calc _ ≤ ∑ _i ∈ (Finset.range (n + 1)).filter (fun i => n - i < L), M :=
        Finset.sum_le_sum fun i _ => hM i
    _ = _ * M := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ L * M := Nat.mul_le_mul_right _ (card_window_le n L)

/-- The packed partial products have no inter-slot carry. -/
theorem convL_cpart_lt {s wI wT : ℕ} (B G : List CInt) (a b : Fin 4)
    (hlen : G.length * (2 ^ (wI - 1) * 2 ^ (wT - 1)) < 2 ^ s) :
    ∀ d ∈ convL (B.map (cpart wI a)) (G.map (cpart wT b)), d < 2 ^ s := by
  intro d hd
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hd
  rw [← List.getD_eq_getElem _ 0 hn, convL_getD]
  refine lt_of_le_of_lt (sum_window_le n G.length _ _ (fun i hi => ?_) (fun i => ?_)) hlen
  · rw [List.getD_eq_default (G.map (cpart wT b)) 0 (by simp; omega), mul_zero]
  · rw [getD_map_cpart, getD_map_cpart]
    exact Nat.mul_le_mul (cpart_le _ _ _) (cpart_le _ _ _)

