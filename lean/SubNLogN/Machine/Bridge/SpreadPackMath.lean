/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadIface

/-!
# K5 spreading, Kronecker packing: pure facts (`Bridge/SpreadPackMath.lean`)

**Scope (honest summary).** Pure lemmas (all proved) behind `PackDataStmt` and `PackFilterStmt`
(`Bridge/SpreadIface.lean`):
* `trimPush f P acc`: the bits `P` (most significant first) are pushed onto `acc` from the first
  `1` on (`f`: a `1` was already seen); `trimPush_append`, `trimPush_single`;
* `trimPush_bitsLE`: trimming the `N`-bit field of `n < 2^N`, most significant bit first, gives
  the canonical `encodeNat n` (the content of `natSyms n`);
* the slot of a part, most significant bit first: `revSlot_low` (`re⁺`, `im⁺`) and
  `revSlot_sgn` (`re⁻`, `im⁻`), from `twosBits_split`;
* `trimPush_pack`: emitting the slots of the coefficients `L` in order (each most significant bit
  first) and trimming gives `encodeNat (pack s (L.reverse.map (cpart w k)))`.
-/

namespace SubNLogN.Machine.Bridge.SpreadPackAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith
  SubNLogN.Machine.Bridge.SpreadAux Computability

/-- Trimmed push, most significant bit first: a bit goes onto `acc` once a `1` has been seen
(`f`: already seen). -/
def trimPush : Bool → List Bool → List Bool → List Bool
  | _, [], acc => acc
  | f, b :: P, acc => if f || b then trimPush true P (b :: acc) else trimPush false P acc

theorem trimPush_true : ∀ (P acc : List Bool), trimPush true P acc = P.reverse ++ acc
  | [], _ => rfl
  | b :: P, acc => by
    simp only [trimPush, Bool.true_or, if_true]
    rw [trimPush_true P (b :: acc), List.reverse_cons, List.append_assoc, List.singleton_append]

theorem trimPush_append : ∀ (f : Bool) (P Q acc : List Bool),
    trimPush f (P ++ Q) acc = trimPush (f || P.any id) Q (trimPush f P acc)
  | f, [], Q, acc => by simp [trimPush]
  | f, b :: P, Q, acc => by
    have ih1 := trimPush_append true P Q (b :: acc)
    have ih2 := trimPush_append false P Q acc
    cases f <;> cases b <;> simp [trimPush, ih1, ih2]

theorem trimPush_single (f b : Bool) (acc : List Bool) :
    trimPush f [b] acc = if f || b then b :: acc else acc := by
  cases f <;> cases b <;> rfl

theorem any_bitsLE : ∀ (N k : ℕ), k < 2 ^ N → (bitsLE N k).any id = decide (k ≠ 0)
  | 0, k, h => by
    have : k = 0 := by simpa using h
    subst this
    rfl
  | N + 1, k, h => by
    have h2 : k / 2 < 2 ^ N := by rw [pow_succ] at h; omega
    rw [K1.bitsLE_succ, List.any_cons, any_bitsLE N (k / 2) h2, Bool.eq_iff_iff]
    simp [Nat.testBit_zero]
    omega

theorem encodeNat_cons {n : ℕ} (hn : n ≠ 0) :
    encodeNat n = n.testBit 0 :: encodeNat (n / 2) := by
  have hne : encodeNat n ≠ [] := by
    intro h
    apply hn
    rw [← Computability.decode_encodeNat n, h]
    rfl
  obtain ⟨b, L, hL⟩ := List.exists_cons_of_ne_nil hne
  have ht := encodeNat_head_tail n
  rw [hL] at ht ⊢
  simp only [List.headD_cons, List.tail_cons] at ht
  rw [ht.1, ht.2]

/-- **Trimming a fixed-width field** (most significant bit first) gives the canonical code. -/
theorem trimPush_bitsLE : ∀ (N n : ℕ), n < 2 ^ N → ∀ acc : List Bool,
    trimPush false (bitsLE N n).reverse acc = encodeNat n ++ acc
  | 0, n, h, acc => by
    have : n = 0 := by simpa using h
    subst this
    simp [trimPush, bitsLE, TMFw.encodeNat_zero]
  | N + 1, n, h, acc => by
    have h2 : n / 2 < 2 ^ N := by rw [pow_succ] at h; omega
    rw [K1.bitsLE_succ, List.reverse_cons, trimPush_append, trimPush_bitsLE N (n / 2) h2,
      trimPush_single, Bool.false_or, List.any_reverse, any_bitsLE N (n / 2) h2]
    by_cases hn2 : n / 2 = 0
    · rw [hn2, TMFw.encodeNat_zero, List.nil_append]
      have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with rfl | rfl
      · simp [TMFw.encodeNat_zero]
      · simp
        rfl
    · have hn : n ≠ 0 := by omega
      rw [encodeNat_cons hn]
      simp [hn2]

theorem bitsLE_zero' (n : ℕ) : bitsLE n 0 = List.replicate n false := by
  simp [bitsLE]

theorem bitsLE_two_pow : ∀ n : ℕ, bitsLE n (2 ^ n) = List.replicate n false
  | 0 => rfl
  | n + 1 => by
    rw [K1.bitsLE_succ, Nat.testBit_two_pow_of_ne (by omega : n + 1 ≠ 0),
      show 2 ^ (n + 1) / 2 = 2 ^ n by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)],
      bitsLE_two_pow n, List.replicate_succ]

theorem bitsLE_lowPart {w s : ℕ} (hw : 1 ≤ w) (hws : w ≤ s) (z : ℤ) :
    bitsLE s (lowPart w z) =
      bitsLE (w - 1) (lowPart w z) ++ false :: List.replicate (s - w) false := by
  have e : s = (w - 1) + (s - w + 1) := by omega
  conv_lhs => rw [e]
  rw [bitsLE_append, Nat.div_eq_of_lt (lowPart_lt w z), bitsLE_zero', List.replicate_succ]

theorem bitsLE_sgnPart {w s : ℕ} (hw : 1 ≤ w) (hws : w ≤ s) (z : ℤ) :
    bitsLE s (sgnPart w z) =
      List.replicate (w - 1) false ++ decide (z < 0) :: List.replicate (s - w) false := by
  have e : s = (w - 1) + (s - w + 1) := by omega
  conv_lhs => rw [e]
  rw [bitsLE_append]
  unfold sgnPart
  split_ifs with h
  · have h1 : 2 ^ (w - 1) / 2 ^ (w - 1) = 1 := Nat.div_self (Nat.two_pow_pos _)
    rw [bitsLE_two_pow, h1, K1.bitsLE_succ, show (1 : ℕ) / 2 = 0 from rfl, bitsLE_zero',
      decide_eq_true h]
    rfl
  · rw [Nat.zero_div, bitsLE_zero', bitsLE_zero', List.replicate_succ, decide_eq_false h]

/-- The `⁺` slot (low bits), most significant bit first. -/
def slotP (s w : ℕ) (lows : List Bool) : List Bool :=
  List.replicate (s - w) false ++ false :: lows.reverse

/-- The `⁻` slot (sign bit), most significant bit first. -/
def slotM (s w : ℕ) (sgn : Bool) : List Bool :=
  List.replicate (s - w) false ++ sgn :: List.replicate (w - 1) false

theorem revSlot_low {w s : ℕ} (hw : 1 ≤ w) (hws : w ≤ s) (z : ℤ) :
    (bitsLE s (lowPart w z)).reverse = slotP s w (bitsLE (w - 1) (lowPart w z)) := by
  rw [bitsLE_lowPart hw hws, slotP]
  simp [List.reverse_append, List.reverse_replicate]

theorem revSlot_sgn {w s : ℕ} (hw : 1 ≤ w) (hws : w ≤ s) (z : ℤ) :
    (bitsLE s (sgnPart w z)).reverse = slotM s w (decide (z < 0)) := by
  rw [bitsLE_sgnPart hw hws, slotM]
  simp [List.reverse_append, List.reverse_replicate]

theorem cpart_lt {w s : ℕ} (hw : 1 ≤ w) (hws : w ≤ s) (k : Fin 4) (x : CInt) :
    cpart w k x < 2 ^ s := by
  have h1 : 2 ^ (w - 1) < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hl : ∀ z, lowPart w z < 2 ^ s := fun z => lt_trans (lowPart_lt w z) h1
  have hs : ∀ z, sgnPart w z < 2 ^ s := by
    intro z
    unfold sgnPart
    split_ifs
    · exact h1
    · exact Nat.two_pow_pos s
  fin_cases k
  exacts [hl x.1, hs x.1, hl x.2, hs x.2]

theorem pack_lt (s : ℕ) : ∀ l : List ℕ, (∀ d ∈ l, d < 2 ^ s) → pack s l < 2 ^ (s * l.length)
  | [], _ => by simp [pack]
  | d :: l, h => by
    have hd := h d List.mem_cons_self
    have ih := pack_lt s l (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))
    have h1 : 2 ^ s * (pack s l + 1) ≤ 2 ^ s * 2 ^ (s * l.length) := Nat.mul_le_mul_left _ ih
    have h2 : 2 ^ s * (pack s l + 1) = 2 ^ s * pack s l + 2 ^ s := by ring
    simp only [pack, List.length_cons]
    rw [Nat.mul_succ, pow_add, Nat.mul_comm (2 ^ (s * l.length)) (2 ^ s)]
    omega

/-- **Packing by trimmed emission.** Emitting, for the coefficients `L` in order, the slot of part
`k` most significant bit first, and trimming, gives `encodeNat (pack s (L.reverse.map (cpart w k)))`. -/
theorem trimPush_pack {w s : ℕ} (hw : 1 ≤ w) (hws : w ≤ s) (k : Fin 4) (L : List CInt) :
    trimPush false (L.flatMap fun x => (bitsLE s (cpart w k x)).reverse) [] =
      encodeNat (pack s (L.reverse.map (cpart w k))) := by
  have hlt : ∀ d ∈ L.reverse.map (cpart w k), d < 2 ^ s := by
    intro d hd
    simp only [List.mem_map] at hd
    obtain ⟨x, -, rfl⟩ := hd
    exact cpart_lt hw hws k x
  have hE : L.flatMap (fun x => (bitsLE s (cpart w k x)).reverse) =
      (bitsLE (s * (L.reverse.map (cpart w k)).length) (pack s (L.reverse.map (cpart w k)))).reverse := by
    rw [bitsLE_pack s _ hlt, List.flatMap_map, List.reverse_flatMap, List.reverse_reverse]
    rfl
  rw [hE, trimPush_bitsLE _ _ (pack_lt s _ hlt), List.append_nil]

end SubNLogN.Machine.Bridge.SpreadPackAux
