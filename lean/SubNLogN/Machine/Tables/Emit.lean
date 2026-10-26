/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.DropSegs
import SubNLogN.Machine.Contracts.Streams

/-!
# K6 (`Machine/Tables/Emit.lean`): pushing a `w`-bit two's-complement field

**Scope (honest summary).** Infrastructure only. `emitField` pushes the field `twosBits w z`
(`SubNLogN/Machine/Contracts/Streams.lean:76`) of a signed number `z` (`intSyms z` on a stack,
kept) onto a destination, least significant bit on top, for `FitsTwos w z` and `1 ≤ w`:
one signed addition `z + 2^w` (`z ≥ 0`) or `z + 2^(w+1)` (`z < 0`) gives the natural number
`v + 2^w` with `v = z mod 2^w`, whose canonical bits are `bitsLE w v ++ [true]`
(`encodeNat_add_two_pow`); two block moves reverse it twice and drop the leading `1`.
Cost `C·(|z| + w + 3) + 6w + 20`, linear in the field width (no binary counter).
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine

/-! ## Bit lists -/

theorem bitsLE_succ' (w d : ℕ) : bitsLE (w + 1) d = d.testBit 0 :: bitsLE w (d / 2) := by
  simp only [bitsLE, List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
    Nat.testBit_succ]

theorem length_bitsLE' (w d : ℕ) : (bitsLE w d).length = w := by simp [bitsLE]

theorem bitsVal_append : ∀ l₁ l₂ : List Bool,
    bitsVal (l₁ ++ l₂) = bitsVal l₁ + 2 ^ l₁.length * bitsVal l₂
  | [], l₂ => by simp
  | b :: l₁, l₂ => by
    simp only [List.cons_append, bitsVal_cons, bitsVal_append l₁ l₂, List.length_cons, pow_succ]
    ring

theorem normBits_append_true : ∀ l : List Bool, normBits (l ++ [true]) = l ++ [true]
  | [] => by simp [normBits]
  | b :: l => by
    simp only [List.cons_append, normBits, normBits_append_true l]
    simp

theorem bitsVal_bitsLE_lt : ∀ (w d : ℕ), d < 2 ^ w → bitsVal (bitsLE w d) = d
  | 0, d, h => by simp at h; subst h; rfl
  | w + 1, d, h => by
    rw [bitsLE_succ', bitsVal_cons, bitsVal_bitsLE_lt w (d / 2) (by rw [pow_succ] at h; omega)]
    have h1 := Nat.div_add_mod d 2
    have h2 : (d.testBit 0).toNat = d % 2 := by
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one d with h | h <;> simp [h]
    omega

theorem encodeNat_add_two_pow {w v : ℕ} (h : v < 2 ^ w) :
    Computability.encodeNat (v + 2 ^ w) = bitsLE w v ++ [true] := by
  have hv : bitsVal (bitsLE w v ++ [true]) = v + 2 ^ w := by
    rw [bitsVal_append, bitsVal_bitsLE_lt w v h]
    simp [bitsLE]
  rw [← hv, encodeNat_bitsVal, normBits_append_true]

theorem natSyms_add_two_pow {w v : ℕ} (h : v < 2 ^ w) :
    natSyms (v + 2 ^ w) = (bitsLE w v).map Sym.bit ++ [Sym.bit true] := by
  simp [natSyms, encodeNat_add_two_pow h]

/-- The natural number stored by `twosBits w z`. -/
def twosVal (w : ℕ) (z : ℤ) : ℕ := (z % (2 ^ w : ℤ)).toNat

theorem twosBits_eq (w : ℕ) (z : ℤ) : twosBits w z = bitsLE w (twosVal w z) := rfl

theorem twosVal_lt (w : ℕ) (z : ℤ) : twosVal w z < 2 ^ w := by
  unfold twosVal
  have h1 := Int.emod_nonneg z (by positivity : (2 ^ w : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos z (by positivity : (0 : ℤ) < 2 ^ w)
  have : ((z % (2 ^ w : ℤ)).toNat : ℤ) < 2 ^ w := by rw [Int.toNat_of_nonneg h1]; exact h2
  exact_mod_cast this

/-- The signed sum computed by `emitField`. -/
theorem twosVal_add_pos {w : ℕ} {z : ℤ} (hz : FitsTwos w z) (h0 : 0 ≤ z) :
    z + 2 ^ w = ((twosVal w z + 2 ^ w : ℕ) : ℤ) := by
  have hw : (2 : ℤ) ^ (w - 1) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) (Nat.sub_le w 1)
  have hz2 : z < 2 ^ w := lt_of_lt_of_le hz.2 hw
  unfold twosVal
  rw [Int.emod_eq_of_lt h0 hz2]
  push_cast
  rw [Int.toNat_of_nonneg h0]

theorem twosVal_add_neg {w : ℕ} {z : ℤ} (hz : FitsTwos w z) (h0 : z < 0) :
    z + 2 ^ (w + 1) = ((twosVal w z + 2 ^ w : ℕ) : ℤ) := by
  have hw : (2 : ℤ) ^ (w - 1) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) (Nat.sub_le w 1)
  have hz1 : -(2 : ℤ) ^ w ≤ z := le_trans (neg_le_neg hw) hz.1
  have hm : z % (2 ^ w : ℤ) = z + 2 ^ w := by
    have h1 : 0 ≤ z + 2 ^ w := by linarith
    have h2 : z + 2 ^ w < 2 ^ w := by linarith
    have h3 := Int.emod_eq_of_lt h1 h2
    rw [Int.add_emod_right] at h3
    exact h3
  unfold twosVal
  rw [hm]
  push_cast
  rw [Int.toNat_of_nonneg (by linarith), pow_succ]
  ring

/-! ## Peek, then branch -/

section Peek

variable {I : TB}

/-- Peek the top of `k` into the symbol register. -/
def peekR (I : TB) (k : TL) : TP I := .peek k (fun v o => I.lS.set v o)

theorem HT.peekBranch_spec (k : TL) (B B' : TL → List Sym) (x : Sym) (rest : List Sym)
    (hk : B k = x :: rest) (f : Option Sym → Bool) (p q : TP I) {T₁ T₂ : ℕ} (ρ : List (TP I))
    (hp : f (some x) = true → HT ρ B p B' T₁) (hq : f (some x) = false → HT ρ B q B' T₂) :
    HT ρ B ((peekR I k).seq (.ite (fun v => f (I.lS.get v)) p q)) B' (1 + (max T₁ T₂ + 1)) := by
  have h1 : Triple ρ (fun s => s.stk = B) (peekR I k)
      (fun s => s.stk = B ∧ I.lS.get s.var = some x) 1 := by
    rintro ⟨v, S⟩ hS
    change S = B at hS
    subst hS
    refine ⟨_, 1, Eval.peek ρ k (fun v o => I.lS.set v o) v S, ⟨rfl, ?_⟩, le_rfl⟩
    show I.lS.get (I.lS.set v (S k).head?) = some x
    rw [I.lS.get_set, hk]
    rfl
  refine Triple.seq h1 (Triple.ite ?_ ?_)
  · rintro s ⟨⟨hsB, hsx⟩, hc⟩
    have hfo : f (some x) = true := by rw [← hsx]; exact hc
    exact (hp hfo).mono (le_max_left _ _) s hsB
  · rintro s ⟨⟨hsB, hsx⟩, hc⟩
    have hfo : f (some x) = false := by rw [← hsx]; exact hc
    exact (hq hfo).mono (le_max_right _ _) s hsB

end Peek

/-! ## The field emitter -/

/-- Push `twosBits w z` (LSB on top) onto `D`, reading `intSyms z` from `Z` (kept), with
`intSyms (2^w)` on `PW`, `intSyms (2^(w+1))` on `PW1`, and empty temporaries `V`, `T`. -/
def emitField (I : TB) (Z PW PW1 V T D : TL) : TP I :=
  ((peekR I Z).seq (Prog.ite (fun v => decide (I.lS.get v = some Sym.neg)) (tai I Z PW1 V)
    (tai I Z PW V))).seq ((tpop I V).seq ((moveAll I V T).seq ((tpop I T).seq (moveAll I T D))))

theorem emitField_closed (I : TB) (Z PW PW1 V T D : TL) : (emitField I Z PW PW1 V T D).Closed :=
  ⟨⟨trivial, ⟨callI_closed _ _ _ _, callI_closed _ _ _ _⟩⟩, ⟨trivial, ⟨moveAll_closed I _ _,
    ⟨trivial, moveAll_closed I _ _⟩⟩⟩⟩

/-- Cost bound of `emitField`. -/
def emitCost (C w zb : ℕ) : ℕ := C * (zb + w + 3) + 6 * w + 20

theorem sgnSym_neg_iff (z : ℤ) : sgnSym z = Sym.neg ↔ z < 0 := by
  unfold sgnSym
  split_ifs with h
  · simp [h]
  · simp [h]

section EmitSpec

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.emitField_spec (hI : I.Spec Mul C) (Z PW PW1 V T D : TL)
    (hnd : [Z, PW, PW1, V, T, D].Nodup) (B : TL → List Sym) (w : ℕ) (z : ℤ)
    (rz r1 r2 : List Sym) (hw : 1 ≤ w) (hz : FitsTwos w z) (hrz : TermOK rz) (hr1 : TermOK r1)
    (hr2 : TermOK r2) (hZ : B Z = intSyms z ++ rz) (hP1 : B PW = intSyms (2 ^ w : ℕ) ++ r1)
    (hP2 : B PW1 = intSyms (2 ^ (w + 1) : ℕ) ++ r2) (hV : B V = []) (hT : B T = [])
    (ρ : List (TP I)) :
    HT ρ B (emitField I Z PW PW1 V T D)
      (Function.update B D ((twosBits w z).map Sym.bit ++ B D))
      (emitCost C w (bitLen z.natAbs)) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hZP, hZP1, hZV, hZT, hZD⟩, ⟨hPP1, hPV, hPT, hPD⟩, ⟨hP1V, hP1T, hP1D⟩, ⟨hVT, hVD⟩,
    hTD⟩ := hnd
  set v := twosVal w z with hv
  have hvlt : v < 2 ^ w := twosVal_lt w z
  -- after the addition: `V = pos :: natSyms (v + 2^w)`
  set B1 := Function.update B V (intSyms ((v + 2 ^ w : ℕ) : ℤ) ++ []) with hB1
  have hadd : HT ρ B ((peekR I Z).seq (.ite (fun v => decide (I.lS.get v = some Sym.neg))
      (tai I Z PW1 V) (tai I Z PW V))) B1 (1 + (max (C * (bitLen z.natAbs + (w + 2) + 1))
        (C * (bitLen z.natAbs + (w + 2) + 1)) + 1)) := by
    have hZ' : B Z = sgnSym z :: (natSyms z.natAbs ++ rz) := by rw [hZ]; rfl
    refine HT.peekBranch_spec Z B B1 (sgnSym z) _ hZ' (fun o => decide (o = some Sym.neg))
      (tai I Z PW1 V) (tai I Z PW V) ρ (fun h => ?_) (fun h => ?_)
    · have hneg : z < 0 := (sgnSym_neg_iff z).mp (by simpa using h)
      have e := HT.tai_spec hI Z PW1 V (by simp [hZP1, hZV, hP1V]) B z _ rz r2 hrz hr2 hZ hP2 ρ
      rw [hV] at e
      refine e.of_eq ?_ ?_
      · have h' : z + ((2 ^ (w + 1) : ℕ) : ℤ) = ((v + 2 ^ w : ℕ) : ℤ) := by
          have := twosVal_add_neg hz hneg
          rw [hv]; push_cast at this ⊢; linarith
        rw [hB1, h']
      · have : bitLen (((2 : ℕ) ^ (w + 1) : ℕ) : ℤ).natAbs ≤ w + 2 := by
          rw [Int.natAbs_natCast, bitLen_two_pow]
        exact Nat.mul_le_mul_left _ (by omega)
    · have hpos : 0 ≤ z := by
        by_contra hc
        exact absurd ((sgnSym_neg_iff z).mpr (by omega)) (by simpa using h)
      have e := HT.tai_spec hI Z PW V (by simp [hZP, hZV, hPV]) B z _ rz r1 hrz hr1 hZ hP1 ρ
      rw [hV] at e
      refine e.of_eq ?_ ?_
      · have h' : z + ((2 ^ w : ℕ) : ℤ) = ((v + 2 ^ w : ℕ) : ℤ) := by
          have := twosVal_add_pos hz hpos
          rw [hv]; push_cast at this ⊢; linarith
        rw [hB1, h']
      · have : bitLen (((2 : ℕ) ^ w : ℕ) : ℤ).natAbs ≤ w + 2 := by
          rw [Int.natAbs_natCast, bitLen_two_pow]; omega
        exact Nat.mul_le_mul_left _ (by omega)
  -- pop the sign
  have hB1V : B1 V = Sym.pos :: natSyms (v + 2 ^ w) := by
    rw [hB1, Function.update_self, intSyms_natCast, List.append_nil]
  have s2 := HT.tpop_spec V B1 Sym.pos _ hB1V ρ
  set B2 := Function.update B1 V (natSyms (v + 2 ^ w)) with hB2
  have hB2V : B2 V = (bitsLE w v).map Sym.bit ++ [Sym.bit true] := by
    rw [hB2, Function.update_self, natSyms_add_two_pow hvlt]
  have s3 := HT.moveAll_spec V T hVT ρ _ B2 hB2V
  set B3 := Function.update (Function.update B2 V []) T
    (((bitsLE w v).map Sym.bit ++ [Sym.bit true]).reverse ++ B2 T) with hB3
  have hB3T : B3 T = Sym.bit true :: (((bitsLE w v).map Sym.bit).reverse ++ []) := by
    rw [hB3, Function.update_self, hB2, Function.update_of_ne (Ne.symm hVT), hB1,
      Function.update_of_ne (Ne.symm hVT), hT]
    simp
  have s4 := HT.tpop_spec T B3 (Sym.bit true) _ hB3T ρ
  set B4 := Function.update B3 T (((bitsLE w v).map Sym.bit).reverse ++ []) with hB4
  have s5 := HT.moveAll_spec T D hTD ρ _ B4 (by rw [hB4, Function.update_self])
  refine (HT.seq hadd (HT.seq s2 (HT.seq s3 (HT.seq s4 s5)))).of_eq ?_ ?_
  · rw [hB4, hB3, hB2, hB1]
    funext g
    by_cases hgD : g = D
    · rw [hgD]
      simp [Function.update_of_ne (Ne.symm hTD), Function.update_of_ne (Ne.symm hVD), twosBits_eq, ← hv]
    by_cases hgT : g = T
    · rw [hgT]
      simp [Function.update_of_ne hTD, hT]
    by_cases hgV : g = V
    · rw [hgV]
      simp [Function.update_of_ne hVD, Function.update_of_ne hVT, hV]
    simp [Function.update_of_ne hgD, Function.update_of_ne hgT, Function.update_of_ne hgV]
  · have hc : C * (bitLen z.natAbs + (w + 2) + 1) = C * (bitLen z.natAbs + w + 3) := by ring
    simp only [List.length_append, List.length_reverse, List.length_map, List.length_cons,
      List.length_nil, length_bitsLE', max_self, hc]
    unfold emitCost
    omega

end EmitSpec

end SubNLogN.Machine.Tables
