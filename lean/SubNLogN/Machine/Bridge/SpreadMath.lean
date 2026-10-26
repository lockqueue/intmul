/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Bridge
import SubNLogN.Machine.Arith.Value
import SubNLogN.Machine.K1.Twos
import SubNLogN.Machine.Arith.Pure

/-!
# K5 spreading, pure core (`Bridge/SpreadMath.lean`)

Pure (machine-free) facts behind the line primitive of `SpreadLinesStmt`
(`SubNLogN/Machine/Contracts/Bridge.lean`). Everything is proved (no `sorry`).

* **Slot packing** `pack s ds = ∑ dⱼ 2^{s j}` of natural coefficient lists and the Kronecker
  identity `pack s a * pack s b = pack s (convL a b)` (`pack_mul`), with the linear convolution
  `convL`; slot extraction `bitsLE (s·n) (pack s ds) = ds.flatMap (bitsLE s)` when every
  coefficient is `< 2^s` (`bitsLE_pack`); reading a canonical `natSyms` with zero padding
  (`padTake_encodeNat`).
* **Sign split without negation**: a `w`-bit two's complement `z` is `lowPart w z - sgnPart w z`
  with `lowPart` its low `w-1` bits and `sgnPart = [z<0]·2^{w-1}` (`split_eq`, `twosBits_split`).
* **Bit-serial signed summation** of several streams (`serialRun`, `serialRun_correct`).

All helpers live in `SubNLogN.Machine.Bridge.SpreadAux`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine Computability
open scoped BigOperators

/-! ## Slot packing and linear convolution -/

/-- Slot packing in radix `2^s`: `pack s [d₀, d₁, …] = d₀ + 2^s (d₁ + 2^s (…))`. -/
def pack (s : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: l => d + 2 ^ s * pack s l

/-- Linear convolution of coefficient lists (length `|a| + |b| - 1`). -/
def convL (a b : List ℕ) : List ℕ :=
  (List.range (a.length + b.length - 1)).map fun n =>
    ∑ i ∈ Finset.range (n + 1), a.getD i 0 * b.getD (n - i) 0

/-- The polynomial `∑ dⱼ Xʲ` of a coefficient list. -/
noncomputable def toPoly : List ℕ → Polynomial ℕ
  | [] => 0
  | d :: l => Polynomial.C d + Polynomial.X * toPoly l

theorem toPoly_coeff : ∀ (l : List ℕ) (n : ℕ), (toPoly l).coeff n = l.getD n 0
  | [], n => by simp [toPoly]
  | d :: l, 0 => by simp [toPoly]
  | d :: l, n + 1 => by
    simp only [toPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul,
      toPoly_coeff l n, List.getD_cons_succ]
    simp

theorem pack_eq_eval (s : ℕ) : ∀ l : List ℕ, pack s l = (toPoly l).eval (2 ^ s)
  | [] => by simp [pack, toPoly]
  | d :: l => by simp [pack, toPoly, pack_eq_eval s l]

theorem convL_length (a b : List ℕ) : (convL a b).length = a.length + b.length - 1 := by
  simp [convL]

theorem convL_getD (a b : List ℕ) (n : ℕ) :
    (convL a b).getD n 0 = ∑ i ∈ Finset.range (n + 1), a.getD i 0 * b.getD (n - i) 0 := by
  by_cases hn : n < a.length + b.length - 1
  · rw [List.getD_eq_getElem?_getD]
    simp [convL, hn]
  · have hlen : (convL a b).length ≤ n := by rw [convL_length]; omega
    rw [List.getD_eq_default (convL a b) 0 hlen]
    symm
    refine Finset.sum_eq_zero fun i hi => ?_
    by_cases ha : i < a.length
    · have hb : b.length ≤ n - i := by simp at hi; omega
      rw [List.getD_eq_default b 0 hb, mul_zero]
    · have ha' : a.length ≤ i := by omega
      rw [List.getD_eq_default a 0 ha', zero_mul]

theorem toPoly_mul (a b : List ℕ) : toPoly a * toPoly b = toPoly (convL a b) := by
  ext n
  rw [Polynomial.coeff_mul, toPoly_coeff, convL_getD,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [toPoly_coeff]

/-- **Kronecker identity**: the product of two packings is the packing of the linear convolution. -/
theorem pack_mul (s : ℕ) (a b : List ℕ) : pack s a * pack s b = pack s (convL a b) := by
  rw [pack_eq_eval, pack_eq_eval, pack_eq_eval, ← Polynomial.eval_mul, toPoly_mul]

/-! ## Slot extraction -/

theorem bitsLE_append (a b d : ℕ) : bitsLE (a + b) d = bitsLE a d ++ bitsLE b (d / 2 ^ a) := by
  induction a generalizing d with
  | zero => simp
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, K1.bitsLE_succ, K1.bitsLE_succ, ih, pow_succ,
      Nat.div_div_eq_div_mul, mul_comm 2 (2 ^ a)]
    rfl

theorem bitsLE_pack (s : ℕ) : ∀ l : List ℕ, (∀ d ∈ l, d < 2 ^ s) →
    bitsLE (s * l.length) (pack s l) = l.flatMap (bitsLE s)
  | [], _ => by simp [pack]
  | d :: l, h => by
    have hd : d < 2 ^ s := h d (by simp)
    have hl := bitsLE_pack s l fun x hx => h x (by simp [hx])
    have hpos : 0 < 2 ^ s := by positivity
    rw [List.length_cons, show s * (l.length + 1) = s + s * l.length by ring, bitsLE_append,
      List.flatMap_cons, ← hl]
    congr 1
    · rw [← K1.bitsLE_mod, pack, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    · congr 1
      rw [pack, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hd, zero_add]

theorem pack_lt (s : ℕ) : ∀ l : List ℕ, (∀ d ∈ l, d < 2 ^ s) → pack s l < 2 ^ (s * l.length)
  | [], _ => by simp [pack]
  | d :: l, h => by
    have hd : d < 2 ^ s := h d (by simp)
    have hl := pack_lt s l fun x hx => h x (by simp [hx])
    rw [List.length_cons, show s * (l.length + 1) = s + s * l.length by ring, pow_add, pack]
    calc d + 2 ^ s * pack s l < 2 ^ s + 2 ^ s * pack s l := by omega
      _ = 2 ^ s * (pack s l + 1) := by ring
      _ ≤ 2 ^ s * 2 ^ (s * l.length) := Nat.mul_le_mul_left _ hl

/-- Read `k` bits of a list, padding with zeros (the machine's read of an exhausted stream). -/
def padTake (L : List Bool) (k : ℕ) : List Bool := (L ++ List.replicate k false).take k

theorem padTake_succ (L : List Bool) (k : ℕ) :
    padTake L (k + 1) = L.headD false :: padTake L.tail k := by
  cases L with
  | nil =>
    simp only [padTake, List.nil_append, List.replicate_succ, List.take_succ_cons, List.headD,
      List.tail_nil]
  | cons b L =>
    simp only [padTake, List.cons_append, List.take_succ_cons, List.headD_cons, List.tail_cons]
    congr 1
    rw [List.take_append, List.take_append, List.take_replicate, List.take_replicate]
    congr 2
    omega

theorem encodeNat_head_tail (n : ℕ) : (encodeNat n).headD false = n.testBit 0 ∧
    (encodeNat n).tail = encodeNat (n / 2) := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [show 2 * m = m + m by ring, encodeNat_add]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [encodeNat_zero]
    · have hne : encodeNat m ≠ [] := fun h => by
        rw [encodeNat_eq_nil_iff] at h; omega
      rw [if_neg hne]
      refine ⟨?_, ?_⟩
      · simp [Nat.testBit_zero]
        omega
      · simp only [List.tail_cons]
        congr 1
        omega
  · rw [show 2 * m + 1 = m + m + 1 by ring, encodeNat_add_add_one]
    refine ⟨?_, ?_⟩
    · simp [Nat.testBit_zero]
      omega
    · simp only [List.tail_cons]
      congr 1
      omega

/-- Reading `k` bits of a canonical number with zero padding gives its low `k` bits. -/
theorem padTake_encodeNat : ∀ (k n : ℕ), padTake (encodeNat n) k = bitsLE k n
  | 0, n => by simp [padTake]
  | k + 1, n => by
    rw [padTake_succ, K1.bitsLE_succ, (encodeNat_head_tail n).1, (encodeNat_head_tail n).2,
      padTake_encodeNat k (n / 2)]

/-! ## Sign split without negation -/

/-- The low `w-1` bits of a `w`-bit two's complement field, as an unsigned number. -/
def lowPart (w : ℕ) (z : ℤ) : ℕ := (z % 2 ^ (w - 1)).toNat

/-- The sign part `[z < 0]·2^{w-1}` of a `w`-bit two's complement field. -/
def sgnPart (w : ℕ) (z : ℤ) : ℕ := if z < 0 then 2 ^ (w - 1) else 0

theorem lowPart_lt (w : ℕ) (z : ℤ) : lowPart w z < 2 ^ (w - 1) := by
  have h : (0 : ℤ) < 2 ^ (w - 1) := by positivity
  have h1 := Int.emod_nonneg z h.ne'
  have h2 := Int.emod_lt_of_pos z h
  unfold lowPart
  have : ((z % 2 ^ (w - 1)).toNat : ℤ) < ((2 ^ (w - 1) : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h1]; push_cast; exact h2
  exact_mod_cast this

theorem sgnPart_le (w : ℕ) (z : ℤ) : sgnPart w z ≤ 2 ^ (w - 1) := by
  unfold sgnPart
  split_ifs <;> simp

theorem ediv_pow_pred_of_fits {w : ℕ} {z : ℤ} (hz : FitsTwos w z) :
    z / 2 ^ (w - 1) = if z < 0 then -1 else 0 := by
  obtain ⟨h1, h2⟩ := hz
  have hp : (0 : ℤ) < 2 ^ (w - 1) := by positivity
  split_ifs with hneg
  · exact ((Int.ediv_emod_unique hp).mpr
      ⟨(by ring : z + 2 ^ (w - 1) + 2 ^ (w - 1) * (-1) = z), by omega, by omega⟩).1
  · exact ((Int.ediv_emod_unique hp).mpr ⟨(by ring : z + 2 ^ (w - 1) * 0 = z), by omega, by omega⟩).1

/-- `z = lowPart - sgnPart` for a `w`-bit two's complement `z`. -/
theorem split_eq {w : ℕ} {z : ℤ} (hz : FitsTwos w z) :
    z = (lowPart w z : ℤ) - (sgnPart w z : ℤ) := by
  have hp : (0 : ℤ) < 2 ^ (w - 1) := by positivity
  have hd := Int.emod_add_mul_ediv z (2 ^ (w - 1))
  rw [ediv_pow_pred_of_fits hz] at hd
  unfold lowPart sgnPart
  rw [Int.toNat_of_nonneg (Int.emod_nonneg z hp.ne')]
  split_ifs at hd ⊢ with hneg
  · push_cast; linarith
  · push_cast; linarith

theorem bitsLE_lt (a b d : ℕ) (hd : d < 2 ^ a) :
    bitsLE (a + b) d = bitsLE a d ++ List.replicate b false := by
  rw [bitsLE_append, Nat.div_eq_of_lt hd]
  congr 1
  induction b with
  | zero => rfl
  | succ b ih => rw [K1.bitsLE_succ, List.replicate_succ, ← ih]; rfl

/-- The bits of a `w`-bit two's complement field: the low part's `w-1` bits, then the sign. -/
theorem twosBits_split {w : ℕ} {z : ℤ} (hw : 1 ≤ w) (hz : FitsTwos w z) :
    twosBits w z = bitsLE (w - 1) (lowPart w z) ++ [decide (z < 0)] := by
  have hw' : w = (w - 1) + 1 := by omega
  conv_lhs => rw [hw', Arith.twosBits_add]
  rw [ediv_pow_pred_of_fits hz]
  congr 1
  split_ifs with hneg
  · simp only [hneg, decide_true]; rfl
  · simp only [hneg, decide_false]; rfl

/-- The `s`-bit slot of the unsigned low part. -/
theorem bitsLE_lowPart {w s : ℕ} (z : ℤ) (hws : w ≤ s) (hw : 1 ≤ w) :
    bitsLE s (lowPart w z) = bitsLE (w - 1) (lowPart w z) ++ false ::
      List.replicate (s - w) false := by
  rw [show s = (w - 1) + (s - w + 1) by omega, bitsLE_lt _ _ _ (lowPart_lt w z)]
  rw [show w - 1 + (s - w + 1) - w = s - w by omega]
  rfl

/-- The `s`-bit slot of the sign part. -/
theorem bitsLE_sgnPart {w s : ℕ} (z : ℤ) (hws : w ≤ s) (hw : 1 ≤ w) :
    bitsLE s (sgnPart w z) = List.replicate (w - 1) false ++ decide (z < 0) ::
      List.replicate (s - w) false := by
  have hs : s = (w - 1) + (s - w + 1) := by omega
  conv_lhs => rw [hs, bitsLE_append]
  have hlow : sgnPart w z % 2 ^ (w - 1) = 0 := by
    unfold sgnPart; split_ifs <;> simp
  rw [← K1.bitsLE_mod (w - 1) (sgnPart w z), hlow]
  congr 1
  · induction (w - 1) with
    | zero => rfl
    | succ n ih => rw [K1.bitsLE_succ, List.replicate_succ, Nat.zero_div, ← ih]; rfl
  · have hq : sgnPart w z / 2 ^ (w - 1) = if z < 0 then 1 else 0 := by
      unfold sgnPart; split_ifs <;> simp
    rw [hq, K1.bitsLE_succ]
    congr 1
    · split_ifs with h <;> simp [h]
    · rw [show (if z < 0 then 1 else 0) / 2 = 0 by split_ifs <;> rfl]
      induction (s - w) with
      | zero => rfl
      | succ n ih => rw [K1.bitsLE_succ, List.replicate_succ, Nat.zero_div, ← ih]; rfl

/-! ## Bit-serial signed summation -/

/-- `±b` for a stream with sign `σ` (`true` = `+`). -/
def sgnBit (σ b : Bool) : ℤ := if b then (if σ then 1 else -1) else 0

/-- The signed head contributions of a family of streams (an exhausted stream contributes `0`). -/
def headSum (srcs : List (Bool × List Bool)) : ℤ :=
  (srcs.map fun p => sgnBit p.1 (p.2.headD false)).sum

/-- Advance every stream by one bit. -/
def tails (srcs : List (Bool × List Bool)) : List (Bool × List Bool) :=
  srcs.map fun p => (p.1, p.2.tail)

/-- `j` steps of the lockstep adder from carry `c`: the output bits. -/
def serialRun : ℕ → ℤ → List (Bool × List Bool) → List Bool
  | 0, _, _ => []
  | j + 1, c, srcs =>
    decide ((c + headSum srcs) % 2 = 1) :: serialRun j ((c + headSum srcs) / 2) (tails srcs)

/-- The signed value of the first `j` bits of a stream. -/
def sval (j : ℕ) (p : Bool × List Bool) : ℤ :=
  (if p.1 then 1 else -1) * (bitsVal (padTake p.2 j) : ℤ)

theorem sval_succ (j : ℕ) (p : Bool × List Bool) :
    sval (j + 1) p = sgnBit p.1 (p.2.headD false) + 2 * sval j (p.1, p.2.tail) := by
  unfold sval sgnBit
  rw [padTake_succ, bitsVal_cons]
  rcases p with ⟨σ, L⟩
  cases σ <;> cases (L.headD false) <;>
    simp only [Bool.toNat_false, Bool.toNat_true, ite_true, ite_false, Bool.false_eq_true,
      Nat.cast_zero, Nat.cast_one, Nat.cast_add] <;> ring

theorem sum_sval_succ (j : ℕ) (srcs : List (Bool × List Bool)) :
    (srcs.map (sval (j + 1))).sum = headSum srcs + 2 * ((tails srcs).map (sval j)).sum := by
  induction srcs with
  | nil => simp [headSum, tails]
  | cons p srcs ih =>
    simp only [List.map_cons, List.sum_cons, headSum, tails] at ih ⊢
    rw [sval_succ, ih]
    ring

/-- **Bit-serial signed summation**: `j` steps from carry `c` output the `j`-bit two's
complement of `c + ∑ ±(value of the first j bits of each stream)`. -/
theorem serialRun_correct : ∀ (j : ℕ) (c : ℤ) (srcs : List (Bool × List Bool)),
    serialRun j c srcs = twosBits j (c + (srcs.map (sval j)).sum)
  | 0, c, srcs => by simp [serialRun]
  | j + 1, c, srcs => by
    rw [serialRun, K1.twosBits_succ, sum_sval_succ, serialRun_correct j]
    set S := ((tails srcs).map (sval j)).sum
    set h := headSum srcs
    congr 1
    · congr 1
      apply propext
      omega
    · congr 1
      omega

/-! ## Linear convolution of complex integer lists and overlap-add -/

/-- The linear convolution of complex integer lists, as a function of the index. -/
def ccF (E G : List CInt) (n : ℕ) : CInt :=
  ∑ i ∈ Finset.range (n + 1), cmulC (E.getD i 0) (G.getD (n - i) 0)

theorem cmulC_zero_left (b : CInt) : cmulC 0 b = 0 := by
  simp [cmulC]

theorem cmulC_zero_right (a : CInt) : cmulC a 0 = 0 := by
  simp [cmulC]

theorem ccF_eq_zero_of_le {E G : List CInt} {n : ℕ} (h : E.length + G.length ≤ n + 1) :
    ccF E G n = 0 := by
  unfold ccF
  refine Finset.sum_eq_zero fun i hi => ?_
  by_cases hi' : i < E.length
  · have hG : G.length ≤ n - i := by simp at hi; omega
    rw [List.getD_eq_default G 0 hG, cmulC_zero_right]
  · have hE : E.length ≤ i := by omega
    rw [List.getD_eq_default E 0 hE, cmulC_zero_left]

theorem getD_append_split (E B : List CInt) (i : ℕ) :
    (E ++ B).getD i 0 = if i < E.length then E.getD i 0 else B.getD (i - E.length) 0 := by
  split_ifs with h
  · exact List.getD_append _ _ _ _ h
  · exact List.getD_append_right _ _ _ _ (by omega)

/-- Convolution of a concatenation: the second part enters shifted by the first part's length. -/
theorem ccF_append (E B G : List CInt) (n : ℕ) :
    ccF (E ++ B) G n = ccF E G n + (if E.length ≤ n then ccF B G (n - E.length) else 0) := by
  split_ifs with hp
  · unfold ccF
    rw [← Finset.sum_range_add_sum_Ico _ (show E.length ≤ n + 1 by omega),
      ← Finset.sum_range_add_sum_Ico (fun i => cmulC (E.getD i 0) (G.getD (n - i) 0))
        (show E.length ≤ n + 1 by omega)]
    have hz : ∑ i ∈ Finset.Ico E.length (n + 1), cmulC (E.getD i 0) (G.getD (n - i) 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hE : E.length ≤ i := by simp at hi; omega
      rw [List.getD_eq_default E 0 hE, cmulC_zero_left]
    rw [hz, add_zero]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [getD_append_split, if_pos (by simpa using hi)]
    · rw [Finset.sum_Ico_eq_sum_range, show n + 1 - E.length = n - E.length + 1 by omega]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [getD_append_split, if_neg (by omega), show E.length + i - E.length = i by omega,
        show n - (E.length + i) = n - E.length - i by omega]
  · rw [add_zero]
    unfold ccF
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [getD_append_split, if_pos (by simp at hi; omega)]

/-- The pending tail after a prefix `E`: the next `W - 1` convolution values. -/
def pend (E G : List CInt) : List CInt :=
  (List.range (G.length - 1)).map fun r => ccF E G (E.length + r)

/-- One overlap-add block step: the block's convolution plus the old tail. -/
def blockV (B G T : List CInt) : List CInt :=
  (List.range (B.length + G.length - 1)).map fun n => ccF B G n + T.getD n 0

theorem blockV_pend (Epre B G : List CInt) :
    blockV B G (pend Epre G) =
      (List.range (B.length + G.length - 1)).map fun n => ccF (Epre ++ B) G (Epre.length + n) := by
  unfold blockV
  refine List.map_congr_left fun n hn => ?_
  rw [ccF_append, if_pos (by omega), show Epre.length + n - Epre.length = n by omega, add_comm]
  congr 1
  by_cases hr : n < G.length - 1
  · rw [pend, List.getD_eq_getElem?_getD]
    simp [hr]
  · rw [List.getD_eq_default _ 0 (by simp [pend]; omega), ccF_eq_zero_of_le (by omega)]

/-- The overlap-add run over a list of blocks, from tail `T`: the emitted values and the final
tail. -/
def oaRun (G : List CInt) : List (List CInt) → List CInt → List CInt × List CInt
  | [], T => ([], T)
  | B :: Bs, T =>
    ((blockV B G T).take B.length ++ (oaRun G Bs ((blockV B G T).drop B.length)).1,
      (oaRun G Bs ((blockV B G T).drop B.length)).2)

/-- **Overlap-add is linear convolution**: from the pending tail of a prefix, the run over blocks
emits the convolution values at the positions of the blocks and ends with the pending tail of
the extended prefix. -/
theorem oaRun_correct (G : List CInt) (hG : 1 ≤ G.length) :
    ∀ (Bs : List (List CInt)) (Epre : List CInt),
      oaRun G Bs (pend Epre G) =
        ((List.range Bs.flatten.length).map fun n => ccF (Epre ++ Bs.flatten) G (Epre.length + n),
          pend (Epre ++ Bs.flatten) G)
  | [], Epre => by simp [oaRun]
  | B :: Bs, Epre => by
    have ih := oaRun_correct G hG Bs (Epre ++ B)
    have hdrop : (blockV B G (pend Epre G)).drop B.length = pend (Epre ++ B) G := by
      rw [blockV_pend]
      apply List.ext_getElem
      · simp [pend]; omega
      · intro n h1 h2
        simp only [List.getElem_drop, List.getElem_map, List.getElem_range, pend, List.length_append]
        congr 1
        ring
    simp only [oaRun]
    rw [hdrop, ih, List.flatten_cons, List.append_assoc]
    refine Prod.ext ?_ rfl
    simp only
    rw [blockV_pend]
    apply List.ext_getElem
    · simp; omega
    · intro n h1 h2
      simp only [List.length_append, List.length_range, List.getElem_append, List.getElem_take,
        List.getElem_map, List.getElem_range, List.length_take, List.length_map]
      split_ifs with hn
      · rw [← List.append_assoc, ccF_append (Epre ++ B), if_neg (by simp; omega), add_zero]
      · congr 1
        simp at hn
        omega

end SubNLogN.Machine.Bridge.SpreadAux
