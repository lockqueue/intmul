/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.Pow
import SubNLogN.Machine.Tables.Roles

/-!
# K6 (`Machine/Tables/Frag.lean`): small arithmetic fragments of the table generator

**Scope (honest summary).** Host fragments with exact final states and costs: `natMul`
(natural product through the signed multiplier instance), `lenProg` (count the bits of a number),
`pow2Int` (`intSyms 2^e`), `clogProg` (`bitLen (n-1)`, which is `Nat.clog 2 n` for `n ≥ 1`),
and the identity `lg n = bitLen (n-1)` for `n ≥ 2` (`lg` of `SubNLogN/Math/Common/DFT.lean:24`).
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine

/-! ## `lg` as a bit length -/

theorem clog_two_eq_bitLen {n : ℕ} (hn : 1 ≤ n) : Nat.clog 2 n = bitLen (n - 1) := by
  have key : ∀ k, Nat.clog 2 n ≤ k ↔ bitLen (n - 1) ≤ k := by
    intro k
    rw [Nat.clog_le_iff_le_pow (by norm_num), bitLen_le_iff]
    omega
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

theorem lg_eq_bitLen {n : ℕ} (hn : 2 ≤ n) : SubNLogN.Math.Common.lg n = bitLen (n - 1) := by
  unfold SubNLogN.Math.Common.lg
  rw [clog_two_eq_bitLen (by omega)]
  have : 1 ≤ bitLen (n - 1) := by
    by_contra h
    have h0 : bitLen (n - 1) ≤ 0 := by omega
    rw [bitLen_le_iff] at h0
    omega
  omega

section Defs

variable (I : TB)

/-- Push `natSyms (x·y)` onto `Z` (through the signed multiplier; `X`, `Y` restored). -/
def natMul (X Y Z : TL) : TP I :=
  (tpush I X .pos).seq ((tpush I Y .pos).seq ((tmu I X Y Z).seq ((tpop I X).seq
    ((tpop I Y).seq (tpop I Z)))))

/-- Count the bits of `X` (consumed) onto the counter `Y`. -/
def lenProg (X Y : TL) : TP I := bitLoop I X (tic I Y) (tic I Y)

/-- `X := intSyms 2^e` (`e` on `E`). -/
def pow2Int (X E : TL) : TP I := (tnat I X 1).seq ((tsv I X E).seq (tpush I X .pos))

/-- `Y := natSyms (bitLen (n-1))` for `n` on `X` (temporary `T`). -/
def clogProg (X T Y : TL) : TP I := (tcp I X T).seq ((tdc I T).seq (lenProg I T Y))

theorem natMul_closed (X Y Z : TL) : (natMul I X Y Z).Closed :=
  ⟨trivial, ⟨trivial, ⟨callI_closed _ _ _ _, ⟨trivial, ⟨trivial, trivial⟩⟩⟩⟩⟩

theorem lenProg_closed (X Y : TL) : (lenProg I X Y).Closed :=
  bitLoop_closed I _ _ _ (callI_closed _ _ _ _) (callI_closed _ _ _ _)

theorem pow2Int_closed (X E : TL) : (pow2Int I X E).Closed :=
  ⟨pushBits_closed _ _, ⟨callI_closed _ _ _ _, trivial⟩⟩

theorem clogProg_closed (X T Y : TL) : (clogProg I X T Y).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, lenProg_closed I _ _⟩⟩

end Defs

section Specs

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.natMul_spec (hI : I.Spec Mul C) (X Y Z : TL) (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (B : TL → List Sym) (w x y : ℕ) (rx ry : List Sym) (hwx : bitLen x ≤ w) (hwy : bitLen y ≤ w)
    (hrx : TermOK rx) (hry : TermOK ry) (hX : B X = natSyms x ++ rx) (hY : B Y = natSyms y ++ ry)
    (ρ : List (TP I)) :
    HT ρ B (natMul I X Y Z) (Function.update B Z (natSyms (x * y) ++ B Z)) (C * Mul w + C + 5) := by
  have hYX := Ne.symm hXY; have hZX := Ne.symm hXZ; have hZY := Ne.symm hYZ
  refine (HT.seq (HT.tpush_spec X .pos B ρ)
    (HT.seq (HT.tpush_spec Y .pos _ ρ)
    (HT.seq (HT.tmu_spec hI X Y Z (by simp [hXY, hXZ, hYZ]) _ w (x : ℤ) (y : ℤ) rx ry
      (by rw [Int.natAbs_natCast]; exact hwx) (by rw [Int.natAbs_natCast]; exact hwy) hrx hry
      (by rw [Function.update_of_ne hXY, Function.update_self, hX, intSyms_natCast'])
      (by rw [Function.update_self, Function.update_of_ne hYX, hY, intSyms_natCast']) ρ)
    (HT.seq (HT.tpop_spec X _ Sym.pos (natSyms x ++ rx)
      (by simp (disch := assumption) only [Function.update_of_ne, Function.update_self, hX]) ρ)
    (HT.seq (HT.tpop_spec Y _ Sym.pos (natSyms y ++ ry)
      (by simp (disch := assumption) only [Function.update_of_ne, Function.update_self, hY]) ρ)
    (HT.tpop_spec Z _ Sym.pos (natSyms (x * y) ++ B Z)
      (by
        simp (disch := assumption) only [Function.update_of_ne, Function.update_self]
        rw [← Nat.cast_mul, intSyms_natCast]; rfl) ρ)))))).of_eq ?_ ?_
  · funext g
    by_cases gZ : g = Z
    · subst gZ; simp (disch := assumption) only [Function.update_of_ne, Function.update_self]
    by_cases gY : g = Y
    · subst gY; simp (disch := assumption) only [Function.update_of_ne, Function.update_self, hY]
    by_cases gX : g = X
    · subst gX; simp (disch := assumption) only [Function.update_of_ne, Function.update_self, hX]
    simp only [Function.update_of_ne gX, Function.update_of_ne gY, Function.update_of_ne gZ]
  · omega

/-- The bit-counting states: `k` bits consumed and counted. -/
def lenSt (B : TL → List Sym) (X Y : TL) (bs : List Bool) (k : ℕ) : TL → List Sym :=
  Function.update (Function.update B X ((bs.drop k).map Sym.bit)) Y (natSyms k ++ [])

theorem HT.lenProg_spec (hI : I.Spec Mul C) (X Y : TL) (hXY : X ≠ Y) (B : TL → List Sym)
    (m : ℕ) (hX : B X = natSyms m) (hY : B Y = []) (ρ : List (TP I)) :
    HT ρ B (lenProg I X Y) (Function.update (Function.update B X []) Y (natSyms (bitLen m)))
      (bitLen m * (C * (bitLen m + 1) + 3) + 2) := by
  have hYX := Ne.symm hXY
  have hlen : (Computability.encodeNat m).length = bitLen m := rfl
  have hloop := HT.bitLoop_spec X (Computability.encodeNat m) (lenSt B X Y (Computability.encodeNat m))
    (fun k _ => by simp only [lenSt, Function.update_of_ne hXY, Function.update_self])
    (tic I Y) (tic I Y) (C * (bitLen m + 1)) ρ
    (fun k hk _ => (HT.tic_spec hI Y _ k [] TermOK.nil
      (by simp only [lenSt, Function.update_of_ne hYX, Function.update_self]) ρ).of_eq
      (by
        funext g
        by_cases gY : g = Y
        · subst gY; simp only [lenSt, Function.update_self]
        by_cases gX : g = X
        · subst gX; simp only [lenSt, Function.update_of_ne gY, Function.update_self]
        simp only [lenSt, Function.update_of_ne gX, Function.update_of_ne gY])
      (Nat.mul_le_mul_left C (Nat.add_le_add_right (le_trans (bitLen_le_self k) (by omega)) 1)))
    (fun k hk _ => (HT.tic_spec hI Y _ k [] TermOK.nil
      (by simp only [lenSt, Function.update_of_ne hYX, Function.update_self]) ρ).of_eq
      (by
        funext g
        by_cases gY : g = Y
        · subst gY; simp only [lenSt, Function.update_self]
        by_cases gX : g = X
        · subst gX; simp only [lenSt, Function.update_of_ne gY, Function.update_self]
        simp only [lenSt, Function.update_of_ne gX, Function.update_of_ne gY])
      (Nat.mul_le_mul_left C (Nat.add_le_add_right (le_trans (bitLen_le_self k) (by omega)) 1)))
  have e0 : lenSt B X Y (Computability.encodeNat m) 0 = B := by
    have hz : natSyms 0 = [] := rfl
    funext g
    by_cases gY : g = Y
    · subst gY; simp only [lenSt, Function.update_self, hz, List.append_nil, hY]
    by_cases gX : g = X
    · subst gX; simp only [lenSt, Function.update_of_ne gY, Function.update_self, List.drop_zero,
        hX]; rfl
    simp only [lenSt, Function.update_of_ne gX, Function.update_of_ne gY]
  rw [e0] at hloop
  refine hloop.of_eq ?_ (by rw [hlen])
  funext g
  by_cases gY : g = Y
  · subst gY; simp only [lenSt, Function.update_self, List.append_nil, hlen]
  by_cases gX : g = X
  · subst gX; simp only [lenSt, Function.update_of_ne gY, Function.update_self,
      List.drop_length, List.map_nil]
  simp only [lenSt, Function.update_of_ne gX, Function.update_of_ne gY]

theorem HT.pow2Int_spec (hI : I.Spec Mul C) (X E : TL) (hXE : X ≠ E) (B : TL → List Sym)
    (e : ℕ) (re : List Sym) (hre : TermOK re) (hX : B X = []) (hE : B E = natSyms e ++ re)
    (ρ : List (TP I)) :
    HT ρ B (pow2Int I X E) (Function.update B X (intSyms ((2 ^ e : ℕ) : ℤ)))
      (C * (e + bitLen e + 1) + 3) := by
  refine (HT.seq (HT.tnat_spec X 1 B ρ)
    (HT.seq (HT.tsv_spec hI X E (by simp [hXE]) _ 1 e [] re TermOK.nil hre
      (by rw [Function.update_self, hX]) (by rw [Function.update_of_ne (Ne.symm hXE), hE]) ρ)
      (HT.tpush_spec X .pos _ ρ))).of_eq ?_ ?_
  · simp only [Function.update_self, Function.update_idem, one_mul, List.append_nil,
      intSyms_natCast]
  · have : bitLen 1 ≤ 1 := bitLen_le_self 1
    omega

theorem HT.clogProg_spec (hI : I.Spec Mul C) (X T Y : TL) (hXT : X ≠ T) (hXY : X ≠ Y)
    (hTY : T ≠ Y) (B : TL → List Sym) (n : ℕ) (rx : List Sym) (hrx : TermOK rx) (hn : 1 ≤ n)
    (hX : B X = natSyms n ++ rx) (hT : B T = []) (hY : B Y = []) (ρ : List (TP I)) :
    HT ρ B (clogProg I X T Y) (Function.update B Y (natSyms (bitLen (n - 1))))
      (C * (bitLen n + 1) + (C * (bitLen n + 1) +
        (bitLen (n - 1) * (C * (bitLen (n - 1) + 1) + 3) + 2))) := by
  obtain ⟨v, rfl⟩ : ∃ v, n = v + 1 := ⟨n - 1, by omega⟩
  have hTX := Ne.symm hXT; have hYX := Ne.symm hXY; have hYT := Ne.symm hTY
  simp only [Nat.add_sub_cancel]
  refine (HT.seq (HT.tcp_spec hI X T (by simp [hXT]) B (v + 1) rx hrx hX ρ)
    (HT.seq (HT.tdc_spec hI T _ v [] TermOK.nil (by rw [Function.update_self, hT]) ρ)
    (HT.lenProg_spec hI T Y hTY _ v (by rw [Function.update_self, List.append_nil])
      (by rw [Function.update_of_ne hYT, Function.update_of_ne hYT, hY]) ρ))).of_eq ?_ le_rfl
  funext g
  by_cases gY : g = Y
  · subst gY; simp only [Function.update_self]
  by_cases gT : g = T
  · subst gT; simp only [Function.update_of_ne gY, Function.update_self, hT]
  simp only [Function.update_of_ne gY, Function.update_of_ne gT]

end Specs

end SubNLogN.Machine.Tables
