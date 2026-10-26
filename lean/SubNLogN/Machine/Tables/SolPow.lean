/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.SolGam

/-!
# K6 (`Machine/Tables/SolPow.lean`): solver entries, part 3 — the closure `γ̂`

**Scope (honest summary).** The powering steps `sqStep` (`X ↦ ⌊X²/2^Q⌋`) and `mulStep`
(`X ↦ ⌊X·â/2^q⌋`) on `x48`, the bit loop over the bits of `A` (most significant first), and the
fragment `solGam` (`x54 := intSyms γ̂`, `γ̂ = rhuDiv (2^(Q+q)) (2^Q - powTruncInt Q q â A)`).
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt

section Steps

variable (I : TB)

/-- `X ↦ ⌊X²/2^Q⌋` on `x48` (temporaries `x51`, `x52`). -/
def sqStep : TP I :=
  (copyPos I x48 x51).seq ((tmu I x48 x51 x52).seq ((intDrop I x51).seq ((intDrop I x48).seq
    ((shrPos I x52 rQ).seq (tmvInt I x52 x48)))))

/-- `X ↦ ⌊X·â/2^q⌋` on `x48` (`â` on `x47`; temporary `x52`). -/
def mulStep : TP I :=
  (tmu I x48 x47 x52).seq ((intDrop I x48).seq ((shrPos I x52 rq).seq (tmvInt I x52 x48)))

theorem sqStep_closed : (sqStep I).Closed :=
  ⟨copyPos_closed I _ _, ⟨callI_closed _ _ _ _, ⟨intDrop_closed I _, ⟨intDrop_closed I _,
    ⟨shrPos_closed I _ _, tmvInt_closed I _ _⟩⟩⟩⟩⟩

theorem mulStep_closed : (mulStep I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨intDrop_closed I _, ⟨shrPos_closed I _ _, tmvInt_closed I _ _⟩⟩⟩

variable {I} {Mul : ℕ → ℕ} {C : ℕ}

/-- Uniform cost bound of one powering step at width `W` (`|X|, |X²|, |â| ≤ W` bits). -/
def stepCost (C W : ℕ) (Mul : ℕ → ℕ) : ℕ := 2 * (C * Mul W + C) + 12 * C * (W + 2) + 30

theorem HT.sqStep_spec (hI : I.Spec Mul C) (B : TL → List Sym) (X Q W : ℕ)
    (hXW : bitLen X ≤ W) (hX2W : bitLen (X * X) ≤ W) (hQW : bitLen Q ≤ W)
    (h48 : B x48 = intSyms (X : ℤ)) (hQ : B rQ = natSyms Q) (h51 : B x51 = []) (h52 : B x52 = [])
    (ρ : List (TP I)) :
    HT ρ B (sqStep I) (Function.update B x48 (intSyms ((X * X / 2 ^ Q : ℕ) : ℤ)))
      (stepCost C W Mul) := by
  have hX' : bitLen (X : ℤ).natAbs ≤ W := by rw [Int.natAbs_natCast]; exact hXW
  refine (HT.seq (HT.copyPos_spec hI x48 x51 (by decide) B X [] TermOK.nil
      (by rw [h48, List.append_nil]) ρ)
    (HT.seq (HT.tmu_spec hI x48 x51 x52 (by decide) _ W (X : ℤ) (X : ℤ) [] [] hX' hX'
      TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, h48, List.append_nil])
      (by simp (disch := decide) only [Function.update_self, h51, List.append_nil]) ρ)
    (HT.seq (HT.intDrop_spec hI x51 _ (X : ℤ) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h51,
        List.append_nil]) ρ)
    (HT.seq (HT.intDrop_spec hI x48 _ (X : ℤ) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, h48, List.append_nil]) ρ)
    (HT.seq (HT.shrPos_spec hI x52 rQ (by decide) _ (X * X) Q [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h52,
        List.append_nil, Nat.cast_mul])
      (by simp (disch := decide) only [Function.update_of_ne, hQ, List.append_nil]) ρ)
      (HT.tmvInt_spec hI x52 x48 (by decide) _ ((X * X / 2 ^ Q : ℕ) : ℤ) [] TermOK.nil
        (by simp (disch := decide) only [Function.update_self]) ρ)))))).of_eq ?_ ?_
  · simp (disch := first | decide | simp (config := { failIfUnchanged := false }) (disch := decide)
      only [ValEq.eq_1, Function.update_self, Function.update_of_ne, h51, h52]) only [tupd_swap,
      Function.update_idem, tupd_eq_self_of, Function.update_self, Function.update_of_ne, h51,
      h52, List.append_nil, List.nil_append]
  · have e1 : bitLen ((X * X / 2 ^ Q : ℕ) : ℤ).natAbs ≤ W := by
      rw [Int.natAbs_natCast]; exact le_trans (bitLen_mono (Nat.div_le_self _ _)) hX2W
    have e2 : min Q (bitLen (X * X)) ≤ W := le_trans (min_le_right _ _) hX2W
    have e3 : bitLen ((X : ℤ) * (X : ℤ)).natAbs ≤ W := by
      rw [← Nat.cast_mul, Int.natAbs_natCast]; exact hX2W
    unfold stepCost
    nlinarith

theorem HT.mulStep_spec (hI : I.Spec Mul C) (B : TL → List Sym) (X a q W : ℕ)
    (hXW : bitLen X ≤ W) (haW : bitLen a ≤ W) (hXaW : bitLen (X * a) ≤ W) (hqW : bitLen q ≤ W)
    (h48 : B x48 = intSyms (X : ℤ)) (h47 : B x47 = intSyms (a : ℤ)) (hq : B rq = natSyms q)
    (h52 : B x52 = []) (ρ : List (TP I)) :
    HT ρ B (mulStep I) (Function.update B x48 (intSyms ((X * a / 2 ^ q : ℕ) : ℤ)))
      (stepCost C W Mul) := by
  have hX' : bitLen (X : ℤ).natAbs ≤ W := by rw [Int.natAbs_natCast]; exact hXW
  have ha' : bitLen (a : ℤ).natAbs ≤ W := by rw [Int.natAbs_natCast]; exact haW
  refine (HT.seq (HT.tmu_spec hI x48 x47 x52 (by decide) B W (X : ℤ) (a : ℤ) [] [] hX' ha'
      TermOK.nil TermOK.nil (by rw [h48, List.append_nil]) (by rw [h47, List.append_nil]) ρ)
    (HT.seq (HT.intDrop_spec hI x48 _ (X : ℤ) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, h48, List.append_nil]) ρ)
    (HT.seq (HT.shrPos_spec hI x52 rq (by decide) _ (X * a) q [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h52,
        List.append_nil, Nat.cast_mul])
      (by simp (disch := decide) only [Function.update_of_ne, hq, List.append_nil]) ρ)
      (HT.tmvInt_spec hI x52 x48 (by decide) _ ((X * a / 2 ^ q : ℕ) : ℤ) [] TermOK.nil
        (by simp (disch := decide) only [Function.update_self]) ρ)))).of_eq ?_ ?_
  · simp (disch := first | decide | simp (config := { failIfUnchanged := false }) (disch := decide)
      only [ValEq.eq_1, Function.update_self, Function.update_of_ne, h52]) only [tupd_swap,
      Function.update_idem, tupd_eq_self_of, Function.update_self, Function.update_of_ne, h52,
      List.append_nil, List.nil_append]
  · have e1 : bitLen ((X * a / 2 ^ q : ℕ) : ℤ).natAbs ≤ W := by
      rw [Int.natAbs_natCast]; exact le_trans (bitLen_mono (Nat.div_le_self _ _)) hXaW
    have e2 : min q (bitLen (X * a)) ≤ W := le_trans (min_le_right _ _) hXaW
    unfold stepCost
    nlinarith

end Steps

/-! ## The closure fragment -/

section Gam

variable (I : TB)

/-- `x48 := intSyms 2^Q`, `x50 := bits of A, most significant first` (temporary `x49`). -/
def gamInit : TP I :=
  (tnat I x48 1).seq ((tsv I x48 rQ).seq ((tpush I x48 .pos).seq ((tcp I rA x49).seq
    (moveAll I x49 x50))))

/-- `x54 := intSyms γ̂` from `x47 = intSyms â` (temporaries `x48 … x53`, `x57`, `x58`). -/
def solGam : TP I :=
  (gamInit I).seq ((bitLoop I x50 ((sqStep I).seq (mulStep I)) (sqStep I)).seq
    ((tsi I rPQ x48 x53).seq ((intDrop I x48).seq ((rhuDivProg I rPQq x53 x54 x57 x58).seq
      (intDrop I x53)))))

theorem gamInit_closed : (gamInit I).Closed :=
  ⟨pushBits_closed _ _, ⟨callI_closed _ _ _ _, ⟨trivial, ⟨callI_closed _ _ _ _,
    moveAll_closed I _ _⟩⟩⟩⟩

theorem solGam_closed : (solGam I).Closed :=
  ⟨gamInit_closed I, ⟨bitLoop_closed I _ _ _ ⟨sqStep_closed I, mulStep_closed I⟩ (sqStep_closed I),
    ⟨callI_closed _ _ _ _, ⟨intDrop_closed I _, ⟨rhuDivProg_closed I _ _ _ _ _,
      intDrop_closed I _⟩⟩⟩⟩⟩

variable {I} {Mul : ℕ → ℕ} {C : ℕ}

/-- The bit loop states of `solGam`. -/
def gamSt (B : TL → List Sym) (Q q a : ℕ) (bs : List Bool) (k : ℕ) : TL → List Sym :=
  Function.update (Function.update B x48
    (intSyms ((powFoldN Q q a (bs.take k) (2 ^ Q) : ℕ) : ℤ))) x50 ((bs.drop k).map Sym.bit)

theorem powFoldN_take_succ (Q q a : ℕ) (bs : List Bool) (k : ℕ) (hk : k < bs.length) :
    powFoldN Q q a (bs.take (k + 1)) (2 ^ Q) = powStepN Q q a bs[k] (powFoldN Q q a (bs.take k) (2 ^ Q)) := by
  simp only [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    powFoldN_append_single]

theorem bitLen_le_of_le_two_pow {x k : ℕ} (h : x ≤ 2 ^ k) : bitLen x ≤ k + 1 :=
  bitLen_le_of_lt (lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (by omega)))

/-- Cost of `solGam` at width `W` for `A` (`|A|` bits). -/
def gamCost (C W A Q q : ℕ) (Mul : ℕ → ℕ) : ℕ :=
  (bitLen 1 + 1 + C * (Q + bitLen Q + 1) + 1 + C * (bitLen A + 1) + (3 * bitLen A + 2)) +
    (bitLen A * (2 * stepCost C W Mul + 3) + 2) + C * (W + W + 1) + (1 + C * (W + 1)) +
    (4 * C * (W + 2) ^ 2 + 10) + (1 + C * (W + 1))

theorem HT.solGam_spec (hI : I.Spec Mul C) (B : TL → List Sym) (a A Q q : ℕ) (ha : a ≤ 2 ^ q)
    (h47 : B x47 = intSyms (a : ℤ)) (hA : B rA = natSyms A) (hQ : B rQ = natSyms Q)
    (hq : B rq = natSyms q) (hPQ : B rPQ = intSyms ((2 ^ Q : ℕ) : ℤ))
    (hPQq : B rPQq = intSyms ((2 ^ (Q + q) : ℕ) : ℤ))
    (h48 : B x48 = []) (h49 : B x49 = []) (h50 : B x50 = []) (h51 : B x51 = []) (h52 : B x52 = [])
    (h53 : B x53 = []) (h54 : B x54 = []) (h57 : B x57 = []) (h58 : B x58 = [])
    (ρ : List (TP I)) :
    HT ρ B (solGam I)
      (Function.update B x54 (intSyms (rhuDiv (2 ^ (Q + q)) (2 ^ Q - powTruncInt Q q a A))))
      (gamCost C (2 * Q + q + 2) A Q q Mul) := by
  set bs := (Computability.encodeNat A).reverse with hbs
  have hNA : bs.length = bitLen A := by rw [hbs, List.length_reverse]; rfl
  set W := 2 * Q + q + 2 with hW
  have hQW : bitLen Q ≤ W := le_trans (bitLen_le_self Q) (by omega)
  have hqW : bitLen q ≤ W := le_trans (bitLen_le_self q) (by omega)
  -- initialisation
  have hinit : HT ρ B (gamInit I) (gamSt B Q q a bs 0)
      (bitLen 1 + 1 + C * (Q + bitLen Q + 1) + 1 + C * (bitLen A + 1) + (3 * bitLen A + 2)) := by
    refine (HT.seq (HT.tnat_spec x48 1 B ρ)
      (HT.seq (HT.tsv_spec hI x48 rQ (by decide) _ 1 Q [] [] TermOK.nil TermOK.nil
        (by simp (disch := decide) only [Function.update_self, h48, List.append_nil])
        (by simp (disch := decide) only [Function.update_of_ne, hQ, List.append_nil]) ρ)
      (HT.seq (HT.tpush_spec x48 .pos _ ρ)
      (HT.seq (HT.tcp_spec hI rA x49 (by decide) _ A [] TermOK.nil
        (by simp (disch := decide) only [Function.update_of_ne, hA, List.append_nil]) ρ)
        (HT.moveAll_spec x49 x50 (by decide) ρ (natSyms A ++ []) _
          (by simp (disch := decide) only [Function.update_self, Function.update_of_ne,
            h49])))))).of_eq ?_ ?_
    · funext g
      unfold gamSt
      by_cases g50 : g = x50
      · subst g50
        simp (disch := decide) [Function.update_of_ne, natSyms, List.map_reverse, h50, hbs]
      by_cases g49 : g = x49
      · subst g49
        simp (disch := decide) [Function.update_of_ne, h49]
      by_cases g48 : g = x48
      · subst g48
        simp (disch := decide) only [Function.update_of_ne, Function.update_self, powFoldN,
          List.take_zero, List.foldl_nil, one_mul, List.append_nil, intSyms_natCast]
      simp [Function.update_of_ne g48, Function.update_of_ne g49, Function.update_of_ne g50]
    · (try simp only [length_natSyms, List.append_nil, List.length_append, List.length_nil])
      omega
  -- the bit loop
  have hstep : ∀ k (hk : k < bs.length), ∀ b, bs[k] = b →
      HT ρ (Function.update (gamSt B Q q a bs k) x50 ((bs.drop (k + 1)).map Sym.bit))
        (if b then (sqStep I).seq (mulStep I) else sqStep I) (gamSt B Q q a bs (k + 1))
        (2 * stepCost C W Mul) := by
    intro k hk b hb
    obtain ⟨X, hX⟩ : ∃ X, powFoldN Q q a (bs.take k) (2 ^ Q) = X := ⟨_, rfl⟩
    have hXle : X ≤ 2 ^ Q := by rw [← hX]; exact powFoldN_le ha _ _ le_rfl
    have hXW : bitLen X ≤ W := le_trans (bitLen_le_of_le_two_pow hXle) (by omega)
    have hX2 : X * X ≤ 2 ^ (2 * Q) := by rw [two_mul, pow_add]; exact Nat.mul_le_mul hXle hXle
    have hX2W : bitLen (X * X) ≤ W := le_trans (bitLen_le_of_le_two_pow hX2) (by omega)
    have hY : X * X / 2 ^ Q ≤ 2 ^ Q := powStepN_le (b := false) ha hXle
    have hYW : bitLen (X * X / 2 ^ Q) ≤ W := le_trans (bitLen_le_of_le_two_pow hY) (by omega)
    have haW : bitLen a ≤ W := le_trans (bitLen_le_of_le_two_pow ha) (by omega)
    have hYa : X * X / 2 ^ Q * a ≤ 2 ^ (Q + q) := by rw [pow_add]; exact Nat.mul_le_mul hY ha
    have hYaW : bitLen (X * X / 2 ^ Q * a) ≤ W := le_trans (bitLen_le_of_le_two_pow hYa) (by omega)
    have hpre48 : (Function.update (gamSt B Q q a bs k) x50 ((bs.drop (k + 1)).map Sym.bit)) x48 =
        intSyms (X : ℤ) := by
      simp (disch := decide) only [gamSt, Function.update_of_ne, Function.update_self, hX]
    have hsq := HT.sqStep_spec hI _ X Q W hXW hX2W hQW hpre48
      (by simp (disch := decide) only [gamSt, Function.update_of_ne, hQ])
      (by simp (disch := decide) only [gamSt, Function.update_of_ne, h51])
      (by simp (disch := decide) only [gamSt, Function.update_of_ne, h52]) ρ
    have hnext := powFoldN_take_succ Q q a bs k hk
    rw [hX] at hnext
    cases b
    · simp only [Bool.false_eq_true, if_false]
      refine hsq.of_eq ?_ (by omega)
      rw [gamSt, gamSt, hnext, hb]
      simp only [powStepN, Bool.false_eq_true, if_false, ↓reduceIte, hX]
      simp (disch := first | decide | simp (config := { failIfUnchanged := false })
        (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne])
        only [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
        Function.update_of_ne]
    · simp only [if_true]
      refine (HT.seq hsq (HT.mulStep_spec hI _ (X * X / 2 ^ Q) a q W hYW haW hYaW hqW
        (by simp (disch := decide) only [Function.update_self])
        (by simp (disch := decide) only [gamSt, Function.update_of_ne, h47])
        (by simp (disch := decide) only [gamSt, Function.update_of_ne, hq])
        (by simp (disch := decide) only [gamSt, Function.update_of_ne, h52]) ρ)).of_eq ?_
        (by omega)
      rw [gamSt, gamSt, hnext, hb]
      simp only [powStepN, if_true, ↓reduceIte, hX]
      simp (disch := first | decide | simp (config := { failIfUnchanged := false })
        (disch := decide) only [ValEq.eq_1, Function.update_self, Function.update_of_ne])
        only [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
        Function.update_of_ne]
  have hloop := HT.bitLoop_spec x50 bs (gamSt B Q q a bs)
    (fun k _ => by simp only [gamSt, Function.update_self]) ((sqStep I).seq (mulStep I))
    (sqStep I) (2 * stepCost C W Mul) ρ
    (fun k hk hb => by have := hstep k hk true hb; simpa using this)
    (fun k hk hb => by have := hstep k hk false hb; simpa using this)
  -- the final value
  have hfin : gamSt B Q q a bs bs.length =
      Function.update (Function.update B x48 (intSyms ((powFoldN Q q a bs (2 ^ Q) : ℕ) : ℤ)))
        x50 [] := by
    simp only [gamSt, List.take_length, List.drop_length, List.map_nil]
  rw [hfin] at hloop
  have hpow : ((powFoldN Q q a bs (2 ^ Q) : ℕ) : ℤ) = powTruncInt Q q a A := by
    rw [hbs]; exact powFoldN_eq Q q a A
  have hXle : powFoldN Q q a bs (2 ^ Q) ≤ 2 ^ Q := powFoldN_le ha _ _ le_rfl
  generalize powFoldN Q q a bs (2 ^ Q) = X at hloop hpow hXle
  have hXW : bitLen ((X : ℤ)).natAbs ≤ W := by
    rw [Int.natAbs_natCast]; exact le_trans (bitLen_le_of_le_two_pow hXle) (by omega)
  have hd0 : (0 : ℤ) ≤ ((2 ^ Q : ℕ) : ℤ) - (X : ℤ) := by
    have : (X : ℤ) ≤ ((2 ^ Q : ℕ) : ℤ) := by exact_mod_cast hXle
    linarith
  have hdle : ((2 ^ Q : ℕ) : ℤ) - (X : ℤ) ≤ (2 : ℤ) ^ Q := by
    have : (0 : ℤ) ≤ (X : ℤ) := Int.natCast_nonneg X
    push_cast; linarith
  have hdW : bitLen (((2 ^ Q : ℕ) : ℤ) - (X : ℤ)).natAbs ≤ W :=
    le_trans (bitLen_natAbs_le_of_le hd0 hdle) (by omega)
  have hPQW : bitLen (((2 ^ Q : ℕ) : ℤ)).natAbs ≤ W := by
    rw [Int.natAbs_natCast, bitLen_two_pow]; omega
  have hPQqW : bitLen (((2 ^ (Q + q) : ℕ) : ℤ)).natAbs ≤ W := by
    rw [Int.natAbs_natCast, bitLen_two_pow]; omega
  refine (HT.seq hinit (HT.seq hloop (HT.seq (HT.tsi_spec hI rPQ x48 x53 (by decide) _
      ((2 ^ Q : ℕ) : ℤ) (X : ℤ) [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hPQ, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ)
    (HT.seq (HT.intDrop_spec hI x48 _ (X : ℤ) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ)
    (HT.seq (HT.rhuDivProg_spec hI rPQq x53 x54 x57 x58 (by decide) _ ((2 ^ (Q + q) : ℕ) : ℤ)
      (((2 ^ Q : ℕ) : ℤ) - (X : ℤ)) [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hPQq, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h53,
        List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, h57])
      (by simp (disch := decide) only [Function.update_of_ne, h58]) ρ)
    (HT.intDrop_spec hI x53 _ (((2 ^ Q : ℕ) : ℤ) - (X : ℤ)) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h53,
        List.append_nil]) ρ)))))).of_eq ?_ ?_
  · funext g
    by_cases g54 : g = x54
    · subst g54
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, h54,
        List.append_nil]
      rw [← hpow]; push_cast; rfl
    by_cases g53 : g = x53
    · subst g53
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, h53]
    by_cases g48 : g = x48
    · subst g48
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, h48]
    by_cases g50 : g = x50
    · subst g50
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, h50]
    simp only [Function.update_of_ne g54, Function.update_of_ne g53, Function.update_of_ne g48,
      Function.update_of_ne g50]
  · unfold gamCost
    rw [hNA]
    have e1 := Nat.mul_le_mul_left C (Nat.add_le_add_right (Nat.add_le_add hPQW hXW) 1)
    have e2 := Nat.mul_le_mul_left C (Nat.add_le_add_right hXW 1)
    have e3 := rdCost_le (C := C) hPQqW hdW
    have e4 := Nat.mul_le_mul_left C (Nat.add_le_add_right hdW 1)
    omega

end Gam

end SubNLogN.Machine.Tables
