/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.TapEntry

/-!
# K6 (`Machine/Tables/TapRec.lean`): the tap record, `tapRec_holds : TapRecStmt`

**Scope (honest summary).** Proves the contract fragment `TapRecStmt` (`TapEntryStmt.lean`). The
program `recProg` runs as follows:
* it computes on the scratch temporaries `B + P`, `2^(2B - P)`, `Kc = (P + 2t(P+1))·A` and the window
  data `|win|`, `c0` (`c0 = 0` if `2P+1 ≤ t`, else `P`);
* it pushes the record end `sep` onto `tapTab`;
* for `i = |win|-1, …, 0` it pushes the coefficient of offset `e_i = (tapWin t P)[i]` with
  `entryProg` (`TapEntry.lean`), at the residue class `cm = (i + c0) mod t = ((e_i + P) mod t)`;
* it drops the temporaries.

`tapRec_holds` takes `K = 1000`. It applies `HT.recProg_spec` with the widths `W = 2V` and `U = V`,
where `V = ω + 4P + 2·size(2tA) + 100` (the size side conditions are `rec_bounds`), and bounds the
resulting cost `recCost` by `K·(C+1)·(KM+1)·tapRecCost` (`recCost_le`).

Helpers are in the namespace `SubNLogN.Machine.Tables.TapAux`; the public theorem `tapRec_holds`
is in `SubNLogN.Machine.Tables`.
-/

namespace SubNLogN.Machine.Tables.TapAux

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Machine.Tables SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt

/-! ## The window -/

/-- Number of stored offsets. -/
def Nw (t P : ℕ) : ℕ := if 2 * P + 1 ≤ t then 2 * P + 1 else t

/-- Residue offset of the window: entry `i` has class `(i + c0) mod t`. -/
def c0w (t P : ℕ) : ℕ := if 2 * P + 1 ≤ t then 0 else P

theorem tapWin_length (t P : ℕ) : (tapWin t P).length = Nw t P := by
  unfold tapWin Nw
  split_ifs <;> simp

/-- The `n`-th stored offset. -/
def winE (t P n : ℕ) : ℤ := if 2 * P + 1 ≤ t then (n : ℤ) - P else (n : ℤ)

theorem tapWin_getElem {t P i : ℕ} (hi : i < (tapWin t P).length) :
    (tapWin t P)[i] = winE t P i := by
  unfold winE
  split_ifs with h
  · simp [tapWin, h, ← List.map_eq_flatMap]
  · simp [tapWin, h, ← List.map_eq_flatMap]

theorem cm_win {t P : ℕ} (_ht : 1 ≤ t) (i : ℕ) (hi : i < (tapWin t P).length) :
    ((((tapWin t P)[i]) + (P : ℤ)) % (t : ℤ)).toNat = (i + c0w t P) % t := by
  have hlen := tapWin_length t P
  rw [tapWin_getElem hi]
  unfold Nw at hlen
  unfold winE c0w
  split_ifs with h
  · rw [sub_add_cancel]
    have hit : i < t := by
      rw [if_pos h] at hlen
      omega
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hit), Int.toNat_natCast,
      Nat.add_zero, Nat.mod_eq_of_lt hit]
  · have : ((i : ℤ) + P) % (t : ℤ) = (((i + P) % t : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [this, Int.toNat_natCast]

theorem tapInt_win {ω P t A a : ℕ} (ht : 1 ≤ t) (ha : a < A) (i : ℕ)
    (hi : i < (tapWin t P).length) :
    tapInt ω P t A a ((tapWin t P)[i]) =
      (TMFw.Contracts.divRoundRatInt (sumFrom ω P t A a ((i + c0w t P) % t) 0).1
          ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ),
        TMFw.Contracts.divRoundRatInt (sumFrom ω P t A a ((i + c0w t P) % t) 0).2
          ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)) := by
  rw [tapInt_eq_divRound, tapNum_eq_sumFrom ht ha, cm_win ht i hi]

theorem ordOf_ne_gt_iff (u v : ℕ) : Lib.ordOf u v ≠ Ordering.gt ↔ u ≤ v := by
  unfold Lib.ordOf
  by_cases h1 : u < v
  · simp [h1]
    omega
  · by_cases h2 : u = v
    · simp [h2]
    · simp [h1, h2]
      omega

/-! ## Setup of the record machine -/

section SetupProgs

variable (I : TB)

/-- `xBP := B + P`, `xTS := 2^(2B - P)`. -/
def setupA : TP I :=
  (tad I rB rP xBP).seq ((tcp I rB y1).seq ((tad I rB y1 y2).seq ((tdr I y1).seq
    ((tsb I y2 rP y3).seq ((tdr I y2).seq ((tic I xTS).seq ((tsv I xTS y3).seq (tdr I y3))))))))

theorem setupA_closed : (setupA I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
    ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
      callI_closed _ _ _ _⟩⟩⟩⟩⟩⟩⟩⟩

/-- `y4 := 2t·(P+1)`. -/
def setupB1 : TP I :=
  (tcp I rP y1).seq ((tic I y1).seq ((tcp I rT y2).seq ((tad I rT y2 y3).seq ((tdr I y2).seq
  ((tpush I y1 .pos).seq ((tpush I y3 .pos).seq ((tmu I y3 y1 y4).seq ((intDrop I y1).seq
  ((intDrop I y3).seq (tpop I y4))))))))))

theorem setupB1_closed : (setupB1 I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
    ⟨callI_closed _ _ _ _, ⟨trivial, ⟨trivial, ⟨callI_closed _ _ _ _, ⟨intDrop_closed I _,
      ⟨intDrop_closed I _, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `xKC := (P + y4)·A` (`y4` dropped). -/
def setupB2 : TP I :=
  (tad I rP y4 y5).seq ((tdr I y4).seq ((tpush I y5 .pos).seq ((tcp I rA y6).seq
  ((tpush I y6 .pos).seq ((tmu I y5 y6 xKC).seq ((intDrop I y5).seq ((intDrop I y6).seq
  (tpop I xKC))))))))

theorem setupB2_closed : (setupB2 I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨trivial, ⟨callI_closed _ _ _ _, ⟨trivial,
    ⟨callI_closed _ _ _ _, ⟨intDrop_closed I _, ⟨intDrop_closed I _, trivial⟩⟩⟩⟩⟩⟩⟩⟩

/-- `xN := |win|`, `xC0 := c0`. -/
def setupC : TP I :=
  (tcp I rP y1).seq ((tad I rP y1 y2).seq ((tdr I y1).seq ((tic I y2).seq
    (((tcm I y2 rT).seq (.ite (fun s => decide (I.cm.obs (I.lcm.get s) ≠ Ordering.gt))
      (tcp I y2 xN) ((tcp I rT xN).seq (tcp I rP xC0)))).seq (tdr I y2)))))

theorem setupC_closed : (setupC I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
    ⟨⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, callI_closed _ _ _ _⟩⟩⟩,
      callI_closed _ _ _ _⟩⟩⟩⟩⟩

end SetupProgs

section SetupSpecs

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.setupA_spec (hI : I.Spec Mul C) (B : TL → List Sym) (P : ℕ)
    (hB : B rB = natSyms (tapPrec P)) (hP : B rP = natSyms P)
    (hBP : B xBP = []) (hTS : B xTS = []) (h1 : B y1 = []) (h2 : B y2 = []) (h3 : B y3 = [])
    (W : ℕ) (hW : 2 * tapPrec P + P + 1 ≤ W) (ρ : List (TP I)) :
    HT ρ B (setupA I)
      (Function.update (Function.update B xBP (natSyms (tapPrec P + P))) xTS
        (natSyms (2 ^ (2 * tapPrec P - P))))
      (9 * (C * (2 * W + 1))) := by
  have hle : P ≤ tapPrec P + tapPrec P := by have := le_tapPrec P; omega
  refine (HT.seq (HT.tad' hI rB rP xBP (by decide) B (tapPrec P) P hB hP hBP ρ)
    (HT.seq (HT.tcp' hI rB y1 (by decide) _ (tapPrec P) (by simp [hB]) (by simp [h1]) ρ)
    (HT.seq (HT.tad' hI rB y1 y2 (by decide) _ (tapPrec P) (tapPrec P) (by simp [hB]) (by simp)
      (by simp [h2]) ρ)
    (HT.seq (HT.tdr' hI y1 _ (tapPrec P) (by simp) ρ)
    (HT.seq (HT.tsb' hI y2 rP y3 (by decide) _ (tapPrec P + tapPrec P) P hle (by simp)
      (by simp [hP]) (by simp [h3]) ρ)
    (HT.seq (HT.tdr' hI y2 _ (tapPrec P + tapPrec P) (by simp) ρ)
    (HT.seq (HT.tic' hI xTS _ 0 (by simp [hTS, natSyms_zero]) ρ)
    (HT.seq (HT.tsv_spec hI xTS y3 (by decide) _ (0 + 1) (tapPrec P + tapPrec P - P) [] []
      TermOK.nil TermOK.nil (by simp) (by simp) ρ)
      (HT.tdr' hI y3 _ (tapPrec P + tapPrec P - P) (by simp) ρ))))))))).of_eq ?_ ?_
  · have e : (0 + 1) * 2 ^ (tapPrec P + tapPrec P - P) = 2 ^ (2 * tapPrec P - P) := by
      rw [two_mul, zero_add, one_mul]
    funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · have b1 : bitLen (tapPrec P) ≤ W := (bitLen_le_self _).trans (by omega)
    have b2 : bitLen P ≤ W := (bitLen_le_self _).trans (by omega)
    have b3 : bitLen (tapPrec P + tapPrec P) ≤ W := (bitLen_le_self _).trans (by omega)
    have b4 : bitLen (tapPrec P + tapPrec P - P) ≤ W := (bitLen_le_self _).trans (by omega)
    have b5 : bitLen 0 ≤ W := (bitLen_le_self _).trans (by omega)
    have c1 : C * (bitLen (tapPrec P) + bitLen P + 1) ≤ C * (2 * W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c2 : C * (bitLen (tapPrec P) + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c3 : C * (bitLen (tapPrec P) + bitLen (tapPrec P) + 1) ≤ C * (2 * W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c4 : C * (bitLen (tapPrec P + tapPrec P) + bitLen P + 1) ≤ C * (2 * W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c5 : C * (bitLen (tapPrec P + tapPrec P) + 1) ≤ C * (2 * W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c6 : C * (bitLen 0 + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c7 : C * (tapPrec P + tapPrec P - P + bitLen (tapPrec P + tapPrec P - P) + 1) ≤
        C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c8 : C * (bitLen (tapPrec P + tapPrec P - P) + 1) ≤ C * (2 * W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    linarith

end SetupSpecs

section SetupSpecs2

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.setupB1_spec (hI : I.Spec Mul C) (B : TL → List Sym) (P t : ℕ)
    (hP : B rP = natSyms P) (hT : B rT = natSyms t)
    (h1 : B y1 = []) (h2 : B y2 = []) (h3 : B y3 = []) (h4 : B y4 = [])
    (W : ℕ) (hW1 : bitLen ((t + t) * (P + 1)) ≤ W) (hW2 : bitLen (t + t) ≤ W)
    (hW3 : bitLen (P + 1) ≤ W) (ρ : List (TP I)) :
    HT ρ B (setupB1 I) (Function.update B y4 (natSyms ((t + t) * (P + 1))))
      (C * Mul W + 12 * (C * (2 * W + 1)) + 6) := by
  have bP : bitLen P ≤ W := (bitLen_mono (by omega)).trans hW3
  have bt : bitLen t ≤ W := (bitLen_mono (by omega)).trans hW2
  refine (HT.seq (HT.tcp' hI rP y1 (by decide) B P hP h1 ρ)
    (HT.seq (HT.tic' hI y1 _ P (by simp) ρ)
    (HT.seq (HT.tcp' hI rT y2 (by decide) _ t (by simp [hT]) (by simp [h2]) ρ)
    (HT.seq (HT.tad' hI rT y2 y3 (by decide) _ t t (by simp [hT]) (by simp) (by simp [h3]) ρ)
    (HT.seq (HT.tdr' hI y2 _ t (by simp) ρ)
    (HT.seq (HT.tpush' y1 .pos _ (natSyms (P + 1)) (by simp) ρ)
    (HT.seq (HT.tpush' y3 .pos _ (natSyms (t + t)) (by simp) ρ)
    (HT.seq (HT.tmu' hI y3 y1 y4 (by decide) _ W ((t + t : ℕ) : ℤ) ((P + 1 : ℕ) : ℤ) [] []
      (by rw [Int.natAbs_natCast]; exact hW2) (by rw [Int.natAbs_natCast]; exact hW3)
      TermOK.nil TermOK.nil
      (by rw [intSyms_natCast]; simp (disch := decide) only [Function.update_of_ne,
        Function.update_self, List.append_nil])
      (by rw [intSyms_natCast]; simp (disch := decide) only [Function.update_of_ne,
        Function.update_self, List.append_nil])
      (by simp [h4]) ρ)
    (HT.seq (HT.intDrop' hI y1 _ ((P + 1 : ℕ) : ℤ)
      (by rw [intSyms_natCast]; simp (disch := decide) only [Function.update_of_ne,
        Function.update_self]) ρ)
    (HT.seq (HT.intDrop' hI y3 _ ((t + t : ℕ) : ℤ)
      (by rw [intSyms_natCast]; simp (disch := decide) only [Function.update_of_ne,
        Function.update_self]) ρ)
      (HT.tpop_spec y4 _ .pos (natSyms ((t + t) * (P + 1)))
        (by simp (disch := decide) only [Function.update_of_ne, Function.update_self];
            exact intSyms_mul_natCast _ _) ρ))))))))))).of_eq ?_ ?_
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simp only [Int.natAbs_natCast]
    have c1 : C * (bitLen P + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c2 : C * (bitLen t + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c3 : C * (bitLen t + bitLen t + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c4 : C * (bitLen (P + 1) + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c5 : C * (bitLen (t + t) + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c6 : C ≤ C * (2 * W + 1) := Nat.le_mul_of_pos_right _ (by omega)
    linarith

theorem HT.setupB2_spec (hI : I.Spec Mul C) (B : TL → List Sym) (P t A : ℕ)
    (hP : B rP = natSyms P) (hA : B rA = natSyms A)
    (h4 : B y4 = natSyms ((t + t) * (P + 1))) (h5 : B y5 = []) (h6 : B y6 = [])
    (hK : B xKC = []) (W : ℕ) (hWK : bitLen (kcN P t A) ≤ W)
    (hW1 : bitLen (P + (t + t) * (P + 1)) ≤ W) (hW2 : bitLen A ≤ W)
    (hW3 : bitLen ((t + t) * (P + 1)) ≤ W) (ρ : List (TP I)) :
    HT ρ B (setupB2 I) (Function.update (Function.update B y4 []) xKC (natSyms (kcN P t A)))
      (C * Mul W + 10 * (C * (2 * W + 1)) + 6) := by
  have bP : bitLen P ≤ W := (bitLen_mono (by omega)).trans hW1
  have hkc : (P + (t + t) * (P + 1)) * A = kcN P t A := by unfold kcN; ring
  refine (HT.seq (HT.tad' hI rP y4 y5 (by decide) B P ((t + t) * (P + 1)) hP h4 h5 ρ)
    (HT.seq (HT.tdr' hI y4 _ ((t + t) * (P + 1)) (by simp [h4]) ρ)
    (HT.seq (HT.tpush' y5 .pos _ (natSyms (P + (t + t) * (P + 1))) (by simp) ρ)
    (HT.seq (HT.tcp' hI rA y6 (by decide) _ A (by simp [hA]) (by simp [h6]) ρ)
    (HT.seq (HT.tpush' y6 .pos _ (natSyms A) (by simp) ρ)
    (HT.seq (HT.tmu' hI y5 y6 xKC (by decide) _ W ((P + (t + t) * (P + 1) : ℕ) : ℤ) (A : ℤ) [] []
      (by rw [Int.natAbs_natCast]; exact hW1) (by rw [Int.natAbs_natCast]; exact hW2)
      TermOK.nil TermOK.nil
      (by rw [intSyms_natCast]; simp (disch := decide) only [Function.update_of_ne,
        Function.update_self, List.append_nil])
      (by rw [intSyms_natCast]; simp (disch := decide) only [Function.update_of_ne,
        Function.update_self, List.append_nil])
      (by simp [hK]) ρ)
    (HT.seq (HT.intDrop' hI y5 _ ((P + (t + t) * (P + 1) : ℕ) : ℤ)
      (by rw [intSyms_natCast]; simp (disch := decide) only [Function.update_of_ne,
        Function.update_self]) ρ)
    (HT.seq (HT.intDrop' hI y6 _ (A : ℤ)
      (by rw [intSyms_natCast]; simp (disch := decide) only [Function.update_of_ne,
        Function.update_self]) ρ)
      (HT.tpop_spec xKC _ .pos (natSyms ((P + (t + t) * (P + 1)) * A))
        (by simp (disch := decide) only [Function.update_of_ne, Function.update_self];
            exact intSyms_mul_natCast _ _) ρ))))))))).of_eq ?_ ?_
  · rw [← hkc]
    funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simp only [Int.natAbs_natCast]
    have c1 : C * (bitLen P + bitLen ((t + t) * (P + 1)) + 1) ≤ C * (2 * W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c2 : C * (bitLen ((t + t) * (P + 1)) + 1) ≤ C * (2 * W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c3 : C * (bitLen A + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c4 : C * (bitLen (P + (t + t) * (P + 1)) + 1) ≤ C * (2 * W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c6 : C ≤ C * (2 * W + 1) := Nat.le_mul_of_pos_right _ (by omega)
    linarith

theorem HT.setupC_spec (hI : I.Spec Mul C) (B : TL → List Sym) (P t : ℕ)
    (hP : B rP = natSyms P) (hT : B rT = natSyms t)
    (h1 : B y1 = []) (h2 : B y2 = []) (hN : B xN = []) (hC0 : B xC0 = [])
    (W : ℕ) (hWP : bitLen (2 * P + 1) ≤ W) (hWt : bitLen t ≤ W) (ρ : List (TP I)) :
    HT ρ B (setupC I)
      (Function.update (Function.update B xN (natSyms (Nw t P))) xC0 (natSyms (c0w t P)))
      (10 * (C * (2 * W + 1)) + 4) := by
  have bP : bitLen P ≤ W := (bitLen_mono (by omega)).trans hWP
  have bPP : bitLen (P + P) ≤ W := (bitLen_mono (by omega)).trans hWP
  have bPP1 : bitLen (P + P + 1) ≤ W := (bitLen_mono (by omega)).trans hWP
  have hite : HT ρ (Function.update (Function.update (Function.update (Function.update B y1
      (natSyms P)) y2 (natSyms (P + P))) y1 []) y2 (natSyms (P + P + 1)))
      ((tcm I y2 rT).seq (.ite (fun s => decide (I.cm.obs (I.lcm.get s) ≠ Ordering.gt))
        (tcp I y2 xN) ((tcp I rT xN).seq (tcp I rP xC0))))
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update B y1 (natSyms P)) y2 (natSyms (P + P))) y1 []) y2
          (natSyms (P + P + 1))) xN (natSyms (Nw t P))) xC0 (natSyms (c0w t P)))
      (C * (bitLen (P + P + 1) + bitLen t + 1) + (max (C * (W + 1)) (2 * (C * (W + 1))) + 1)) := by
    refine HT.tcmIte_spec hI y2 rT (by decide) _ _ (P + P + 1) t [] [] TermOK.nil TermOK.nil
      (by simp) (by simp [hT]) (fun o => decide (o ≠ Ordering.gt)) _ _ ρ (fun h => ?_)
      (fun h => ?_)
    · have hc : P + P + 1 ≤ t := (ordOf_ne_gt_iff _ _).mp (by simpa using h)
      have hc' : 2 * P + 1 ≤ t := by omega
      have eN : Nw t P = P + P + 1 := by rw [Nw, if_pos hc']; omega
      have eC : c0w t P = 0 := by rw [c0w, if_pos hc']
      rw [eN, eC]
      refine (HT.tcp' hI y2 xN (by decide) _ (P + P + 1) (by simp) (by simp [hN]) ρ).of_eq ?_
        (Nat.mul_le_mul_left _ (by omega))
      funext x
      simp only [Function.update_apply]
      split_ifs <;> simp_all [natSyms_zero]
    · have hc : ¬ P + P + 1 ≤ t := fun hc => by
        have h' := (ordOf_ne_gt_iff _ _).mpr hc
        simp [h'] at h
      have hc' : ¬ 2 * P + 1 ≤ t := by omega
      have eN : Nw t P = t := by rw [Nw, if_neg hc']
      have eC : c0w t P = P := by rw [c0w, if_neg hc']
      rw [eN, eC]
      refine (HT.seq (HT.tcp' hI rT xN (by decide) _ t (by simp [hT]) (by simp [hN]) ρ)
        (HT.tcp' hI rP xC0 (by decide) _ P (by simp [hP]) (by simp [hC0]) ρ)).of_eq rfl ?_
      · have c1 : C * (bitLen t + 1) ≤ C * (W + 1) := Nat.mul_le_mul_left _ (by omega)
        have c2 : C * (bitLen P + 1) ≤ C * (W + 1) := Nat.mul_le_mul_left _ (by omega)
        omega
  refine (HT.seq (HT.tcp' hI rP y1 (by decide) B P hP h1 ρ)
    (HT.seq (HT.tad' hI rP y1 y2 (by decide) _ P P (by simp [hP]) (by simp) (by simp [h2]) ρ)
    (HT.seq (HT.tdr' hI y1 _ P (by simp) ρ)
    (HT.seq (HT.tic' hI y2 _ (P + P) (by simp) ρ)
    (HT.seq hite (HT.tdr' hI y2 _ (P + P + 1) (by simp) ρ)))))).of_eq ?_ ?_
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · have c1 : C * (bitLen P + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c2 : C * (bitLen P + bitLen P + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c3 : C * (bitLen (P + P) + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c4 : C * (bitLen (P + P + 1) + bitLen t + 1) ≤ C * (2 * W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have c5 : C * (bitLen (P + P + 1) + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c6 : C * (W + 1) ≤ C * (2 * W + 1) := Nat.mul_le_mul_left _ (by omega)
    have hmax : max (C * (W + 1)) (2 * (C * (W + 1))) = 2 * (C * (W + 1)) :=
      max_eq_right (by omega)
    rw [hmax]
    linarith

end SetupSpecs2

/-! ## The entry loop -/

section RecProgs

variable (I : TB)

/-- Entry `i` (counter value on `xN`): `xCM := (i + c0) mod t`, then `entryProg`. -/
def recBody : TP I :=
  (tad I xN xC0 y1).seq ((tdm I y1 rT y2 xCM).seq ((tdr I y2).seq ((tdr I y1).seq
    ((entryProg I).seq (tdr I xCM)))))

theorem recBody_closed : (recBody I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
    ⟨entryProg_closed I, callI_closed _ _ _ _⟩⟩⟩⟩⟩

/-- Setup: the temporaries, then the record end `sep` on `tapTab`. -/
def setupAll : TP I :=
  (setupA I).seq ((setupB1 I).seq ((setupB2 I).seq ((setupC I).seq (tpush I sTap .sep))))

theorem setupAll_closed : (setupAll I).Closed :=
  ⟨setupA_closed I, ⟨setupB1_closed I, ⟨setupB2_closed I, ⟨setupC_closed I, trivial⟩⟩⟩⟩

/-- Cleanup: drop the temporaries `xC0, xKC, xBP, xTS`. -/
def cleanProg : TP I := (tdr I xC0).seq ((tdr I xKC).seq ((tdr I xBP).seq (tdr I xTS)))

theorem cleanProg_closed : (cleanProg I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, callI_closed _ _ _ _⟩⟩⟩

/-- **The tap-record machine**: setup, the countdown loop over the window, cleanup. -/
def recProg : TP I := (setupAll I).seq ((tcd I xN (recBody I)).seq (cleanProg I))

theorem recProg_closed : (recProg I).Closed :=
  ⟨setupAll_closed I, ⟨tcd_closed I _ _ (recBody_closed I), cleanProg_closed I⟩⟩

/-- Cost bound of one loop iteration. -/
def recBodyCost (C : ℕ) (Mul : ℕ → ℕ) (P wT W U : ℕ) : ℕ :=
  entryCost C Mul P wT W U + 5 * (C * (W + 1) ^ 2)

/-- Cost bound of the setup. -/
def setupCost (C : ℕ) (Mul : ℕ → ℕ) (W : ℕ) : ℕ :=
  9 * (C * (2 * W + 1)) + ((C * Mul W + 12 * (C * (2 * W + 1)) + 6) +
    ((C * Mul W + 10 * (C * (2 * W + 1)) + 6) + ((10 * (C * (2 * W + 1)) + 4) + 1)))

end RecProgs

section RecSpecs

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.recBody_spec (hI : I.Spec Mul C) (S : TL → List Sym) (ω P t A a wT i c0 : ℕ)
    (hω : 1 ≤ ω) (ht : 1 ≤ t) (ha : a < A) (hw : 1 ≤ wT)
    (hfit1 : FitsTwos wT (TMFw.Contracts.divRoundRatInt (sumFrom ω P t A a ((i + c0) % t) 0).1
      ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)))
    (hfit2 : FitsTwos wT (TMFw.Contracts.divRoundRatInt (sumFrom ω P t A a ((i + c0) % t) 0).2
      ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ)))
    (hN : S xN = natSyms i) (hC0 : S xC0 = natSyms c0)
    (hP : S rP = natSyms P) (hT : S rT = natSyms t)
    (hA : S rA = natSyms A) (hab : S ra = natSyms a)
    (hK : S xKC = natSyms (kcN P t A)) (hD : S rDen = natSyms (2 * t * A))
    (hB : S rB = natSyms (tapPrec P)) (hBP : S xBP = natSyms (tapPrec P + P))
    (hW : S rW = natSyms ω)
    (hPi : S rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hLn : S rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hTS : S xTS = natSyms (2 ^ (2 * tapPrec P - P)))
    (hPW : S rPW = intSyms ((2 ^ wT : ℕ) : ℤ)) (hPW1 : S rPW1 = intSyms ((2 ^ (wT + 1) : ℕ) : ℤ))
    (hCM : S xCM = []) (hAR : S xAR = []) (hAI : S xAI = []) (hM : S xM = [])
    (h1 : S y1 = []) (h2 : S y2 = []) (h3 : S y3 = []) (h4 : S y4 = []) (h5 : S y5 = [])
    (h6 : S y6 = []) (h7 : S y7 = []) (h8 : S y8 = []) (h9 : S y9 = []) (h10 : S y10 = [])
    (h11 : S y11 = []) (h12 : S y12 = [])
    (W U : ℕ) (hWK : bitLen (kcN P t A) ≤ W) (hWD : bitLen (2 * t * A) ≤ W)
    (hU1 : tapPrec P + bitLen (2 * t * A) + 1 ≤ U) (hU2 : ω + tapPrec P + bitLen A + 1 ≤ U)
    (hU3 : bitLen (tapPrec P + P) ≤ U) (hWP : bitLen (2 * P + 1) ≤ W) (hWt : bitLen t ≤ W)
    (hWi : bitLen (i + c0) ≤ W) (ρ : List (TP I)) :
    HT ρ S (recBody I)
      (Function.update S sTap
        ((coefBits wT (TMFw.Contracts.divRoundRatInt (sumFrom ω P t A a ((i + c0) % t) 0).1
            ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ),
          TMFw.Contracts.divRoundRatInt (sumFrom ω P t A a ((i + c0) % t) 0).2
            ((2 ^ (2 * tapPrec P - P) : ℕ) : ℤ))).map Sym.bit ++ S sTap))
      (recBodyCost C Mul P wT W U) := by
  have ht0 : 0 < t := by omega
  have hcm : (i + c0) % t < t := Nat.mod_lt _ ht0
  have hcmW : bitLen ((i + c0) % t) ≤ W := (bitLen_mono hcm.le).trans hWt
  have hqW : bitLen ((i + c0) / t) ≤ W := (bitLen_mono (Nat.div_le_self _ _)).trans hWi
  have hiW : bitLen i ≤ W := (bitLen_mono (by omega)).trans hWi
  have hcW : bitLen c0 ≤ W := (bitLen_mono (by omega)).trans hWi
  refine (HT.seq (HT.tad' hI xN xC0 y1 (by decide) S i c0 hN hC0 h1 ρ)
    (HT.seq (HT.tdm' hI y1 rT y2 xCM (by decide) _ (i + c0) t ht0 (by simp) (by simp [hT])
      (by simp [h2]) (by simp [hCM]) ρ)
    (HT.seq (HT.tdr' hI y2 _ ((i + c0) / t) (by simp) ρ)
    (HT.seq (HT.tdr' hI y1 _ (i + c0) (by simp) ρ)
    (HT.seq (HT.entryProg_spec hI _ ω P t A a ((i + c0) % t) wT hω ht ha hcm hw hfit1 hfit2
      (by simp [hP]) (by simp [hT]) (by simp) (by simp [hA]) (by simp [hab]) (by simp [hK])
      (by simp [hD]) (by simp [hB]) (by simp [hBP]) (by simp [hW]) (by simp [hPi])
      (by simp [hLn]) (by simp [hTS]) (by simp [hPW]) (by simp [hPW1]) (by simp [hAR])
      (by simp [hAI]) (by simp [hM]) (by simp [h1]) (by simp [h2]) (by simp [h3]) (by simp [h4])
      (by simp [h5]) (by simp [h6]) (by simp [h7]) (by simp [h8]) (by simp [h9]) (by simp [h10])
      (by simp [h11]) (by simp [h12]) W U hWK hWD hU1 hU2 hU3 hWP hWt ρ)
      (HT.tdr' hI xCM _ ((i + c0) % t) (by simp) ρ)))))).of_eq ?_ ?_
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · unfold recBodyCost
    have hsq : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hsq2 : 2 * W + 1 ≤ (W + 1) ^ 2 := by
      have e : (W + 1) ^ 2 = W * W + (2 * W + 1) := by ring
      rw [e]
      exact Nat.le_add_left _ _
    have c1 : C * (bitLen i + bitLen c0 + 1) ≤ C * (W + 1) ^ 2 := Nat.mul_le_mul_left _ (by omega)
    have c2 : C * (bitLen (i + c0) * bitLen t + bitLen (i + c0) + bitLen t + 1) ≤
        C * (W + 1) ^ 2 := by
      apply Nat.mul_le_mul_left
      have e : bitLen (i + c0) * bitLen t + bitLen (i + c0) + bitLen t + 1 =
          (bitLen (i + c0) + 1) * (bitLen t + 1) := by ring
      rw [e, sq]
      exact Nat.mul_le_mul (by omega) (by omega)
    have c3 : C * (bitLen ((i + c0) / t) + 1) ≤ C * (W + 1) ^ 2 := Nat.mul_le_mul_left _ (by omega)
    have c4 : C * (bitLen (i + c0) + 1) ≤ C * (W + 1) ^ 2 := Nat.mul_le_mul_left _ (by omega)
    have c5 : C * (bitLen ((i + c0) % t) + 1) ≤ C * (W + 1) ^ 2 := Nat.mul_le_mul_left _ (by omega)
    linarith

end RecSpecs

/-! ## The record machine -/

section RecState

/-- The bits of the stored coefficient of offset `e`. -/
noncomputable def entBits (ω P wT t A a : ℕ) (e : ℤ) : List Sym :=
  (coefBits wT (tapInt ω P t A a e)).map Sym.bit

/-- The setup values on the temporaries `xBP, xTS, xKC, xC0`. -/
def recU (B : TL → List Sym) (P t A : ℕ) : TL → List Sym :=
  Function.update (Function.update (Function.update (Function.update B xBP
    (natSyms (tapPrec P + P))) xTS (natSyms (2 ^ (2 * tapPrec P - P)))) xKC
    (natSyms (kcN P t A))) xC0 (natSyms (c0w t P))

/-- Record-loop state: setup values, counter `i` on `xN`, entries `≥ i` pushed on `tapTab`. -/
noncomputable def recSt (B : TL → List Sym) (ω P wT t A a i : ℕ) : TL → List Sym :=
  Function.update (Function.update (recU B P t A) xN (natSyms i)) sTap
    (((tapWin t P).drop i).flatMap (entBits ω P wT t A a) ++ Sym.sep :: B sTap)

theorem drop_Nw (t P : ℕ) : (tapWin t P).drop (Nw t P) = [] := by
  rw [← tapWin_length, List.drop_length]

theorem c0w_le (t P : ℕ) : c0w t P ≤ P := by
  unfold c0w
  split_ifs <;> omega

theorem i_add_c0w_le {t P i : ℕ} (hi : i < Nw t P) : i + c0w t P ≤ t + 3 * P + 1 := by
  unfold Nw at hi
  unfold c0w
  split_ifs at hi ⊢ <;> omega

theorem setup_state_eq (B : TL → List Sym) (P t A : ℕ) (v l : List Sym) (h4 : B y4 = []) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update B xBP (natSyms (tapPrec P + P)))
        xTS (natSyms (2 ^ (2 * tapPrec P - P)))) y4 v) y4 []) xKC (natSyms (kcN P t A)))
      xN (natSyms (Nw t P))) xC0 (natSyms (c0w t P))) sTap l =
    Function.update (Function.update (recU B P t A) xN (natSyms (Nw t P))) sTap l := by
  unfold recU
  funext x
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem loop_state_eq (U : TL → List Sym) (n1 n2 L1 L2 : List Sym) :
    Function.update (Function.update (Function.update (Function.update U xN n1) sTap L1) xN
      (n2 ++ [])) sTap (L2 ++ Function.update (Function.update (Function.update U xN n1) sTap L1)
        xN (n2 ++ []) sTap) =
    Function.update (Function.update U xN n2) sTap (L2 ++ L1) := by
  funext x
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem clean_state_eq (B : TL → List Sym) (P t A : ℕ) (L : List Sym)
    (h40 : B xTS = []) (h41 : B xKC = []) (h42 : B xBP = []) (h43 : B xC0 = [])
    (h44 : B xN = []) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (recU B P t A) xN (natSyms 0)) sTap L) xC0 []) xKC []) xBP []) xTS [] =
    Function.update B sTap L := by
  unfold recU
  funext x
  simp only [Function.update_apply]
  split_ifs <;> simp_all [natSyms_zero]

theorem recSyms_eq (ω P wT t A a : ℕ) (l : List Sym) :
    recSyms (crecBits wT ((tapWin t P).map (tapInt ω P t A a))) ++ l =
      (tapWin t P).flatMap (entBits ω P wT t A a) ++ Sym.sep :: l := by
  simp [recSyms, crecBits, List.map_flatMap, List.flatMap_map]
  rfl

end RecState

section RecSetup

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.setupAll_spec (hI : I.Spec Mul C) (B : TL → List Sym) (ω P wT t A a : ℕ)
    (ht : 1 ≤ t) (ha : a < A)
    (hP : B rP = natSyms P) (hB : B rB = natSyms (tapPrec P)) (hT : B rT = natSyms t)
    (hA : B rA = natSyms A)
    (e40 : B xTS = []) (e41 : B xKC = []) (e42 : B xBP = []) (e43 : B xC0 = [])
    (e44 : B xN = []) (e49 : B y1 = []) (e50 : B y2 = []) (e51 : B y3 = []) (e52 : B y4 = [])
    (e53 : B y5 = []) (e54 : B y6 = [])
    (W : ℕ) (hWA : 2 * tapPrec P + P + 1 ≤ W) (hWK : bitLen (kcN P t A) ≤ W)
    (hWt : bitLen (t + 3 * P + 1) ≤ W) (ρ : List (TP I)) :
    HT ρ B (setupAll I) (recSt B ω P wT t A a (Nw t P)) (setupCost C Mul W) := by
  have hA1 : 0 < A := by omega
  have hkc1 : (t + t) * (P + 1) ≤ kcN P t A := by
    unfold kcN
    calc (t + t) * (P + 1) = 2 * t * (P + 1) := by ring
      _ ≤ P + 2 * t * (P + 1) := Nat.le_add_left _ _
      _ ≤ (P + 2 * t * (P + 1)) * A := Nat.le_mul_of_pos_right _ hA1
  have hkc2 : P + (t + t) * (P + 1) ≤ kcN P t A := by
    unfold kcN
    calc P + (t + t) * (P + 1) = P + 2 * t * (P + 1) := by ring
      _ ≤ (P + 2 * t * (P + 1)) * A := Nat.le_mul_of_pos_right _ hA1
  have hkc3 : A ≤ kcN P t A := by
    unfold kcN
    have hpos : 0 < 2 * t * (P + 1) :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
    exact Nat.le_mul_of_pos_left _ (by omega)
  have bW1 : bitLen ((t + t) * (P + 1)) ≤ W := (bitLen_mono hkc1).trans hWK
  have bW2 : bitLen (t + t) ≤ W := (bitLen_mono ((Nat.le_mul_of_pos_right _ (by omega)).trans
    hkc1)).trans hWK
  have bW3 : bitLen (P + 1) ≤ W :=
    (bitLen_mono ((Nat.le_mul_of_pos_left _ (by omega)).trans hkc1)).trans hWK
  have bW4 : bitLen (P + (t + t) * (P + 1)) ≤ W := (bitLen_mono hkc2).trans hWK
  have bW5 : bitLen A ≤ W := (bitLen_mono hkc3).trans hWK
  have bW6 : bitLen (2 * P + 1) ≤ W := (bitLen_mono (by omega)).trans hWt
  have bW7 : bitLen t ≤ W := (bitLen_mono (by omega)).trans hWt
  refine (HT.seq (HT.setupA_spec hI B P hB hP e42 e40 e49 e50 e51 W hWA ρ)
    (HT.seq (HT.setupB1_spec hI _ P t (by simp [hP]) (by simp [hT]) (by simp [e49])
      (by simp [e50]) (by simp [e51]) (by simp [e52]) W bW1 bW2 bW3 ρ)
    (HT.seq (HT.setupB2_spec hI _ P t A (by simp [hP]) (by simp [hA]) (by simp)
      (by simp [e53]) (by simp [e54]) (by simp [e41]) W hWK bW4 bW5 bW1 ρ)
    (HT.seq (HT.setupC_spec hI _ P t (by simp [hP]) (by simp [hT]) (by simp [e49])
      (by simp [e50]) (by simp [e44]) (by simp [e43]) W bW6 bW7 ρ)
      (HT.tpush' sTap .sep _ (B sTap) (by simp) ρ))))).of_eq ?_ le_rfl
  simp only [recSt, drop_Nw, List.flatMap_nil, List.nil_append]
  exact setup_state_eq B P t A _ _ e52

end RecSetup

section RecLoop

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.recLoop_spec (hI : I.Spec Mul C) (B : TL → List Sym) (ω P wT t A a : ℕ)
    (hω : 1 ≤ ω) (hw : 1 ≤ wT) (ht : 1 ≤ t) (ha : a < A)
    (hfit : ∀ e ∈ tapWin t P, FitsTwos wT (tapInt ω P t A a e).1 ∧
      FitsTwos wT (tapInt ω P t A a e).2)
    (hP : B rP = natSyms P) (hW : B rW = natSyms ω) (hB : B rB = natSyms (tapPrec P))
    (hPi : B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hLn : B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hPW : B rPW = intSyms ((2 ^ wT : ℕ) : ℤ)) (hPW1 : B rPW1 = intSyms ((2 ^ (wT + 1) : ℕ) : ℤ))
    (hT : B rT = natSyms t) (hA : B rA = natSyms A) (hD : B rDen = natSyms (2 * t * A))
    (hab : B ra = natSyms a)
    (e45 : B xCM = []) (e46 : B xAR = []) (e47 : B xAI = []) (e48 : B xM = [])
    (e49 : B y1 = []) (e50 : B y2 = []) (e51 : B y3 = []) (e52 : B y4 = []) (e53 : B y5 = [])
    (e54 : B y6 = []) (e55 : B y7 = []) (e56 : B y8 = []) (e57 : B y9 = []) (e58 : B y10 = [])
    (e59 : B y11 = []) (e60 : B y12 = [])
    (W U : ℕ) (hWK : bitLen (kcN P t A) ≤ W) (hWD : bitLen (2 * t * A) ≤ W)
    (hWt : bitLen (t + 3 * P + 1) ≤ W)
    (hU1 : tapPrec P + bitLen (2 * t * A) + 1 ≤ U) (hU2 : ω + tapPrec P + bitLen A + 1 ≤ U)
    (hU3 : bitLen (tapPrec P + P) ≤ U) (ρ : List (TP I)) :
    HT ρ (recSt B ω P wT t A a (Nw t P)) (tcd I xN (recBody I)) (recSt B ω P wT t A a 0)
      (C + loopCost (fun i => C * (bitLen (i + 1) + 1) + recBodyCost C Mul P wT W U + C)
        (Nw t P)) := by
  have bW6 : bitLen (2 * P + 1) ≤ W := (bitLen_mono (by omega)).trans hWt
  have bW7 : bitLen t ≤ W := (bitLen_mono (by omega)).trans hWt
  refine HT.tcd_spec hI xN [] TermOK.nil (recSt B ω P wT t A a) (fun i => by simp [recSt])
    (recBody I) (Nw t P) (fun _ => recBodyCost C Mul P wT W U) ρ (fun i hi => ?_)
  have hi' : i < (tapWin t P).length := by rw [tapWin_length]; exact hi
  have hent := tapInt_win (ω := ω) (P := P) (t := t) (A := A) (a := a) ht ha i hi'
  have hf := hfit _ (List.getElem_mem hi')
  rw [hent] at hf
  have hWi : bitLen (i + c0w t P) ≤ W := (bitLen_mono (i_add_c0w_le hi)).trans hWt
  have hb := HT.recBody_spec hI (Function.update (recSt B ω P wT t A a (i + 1)) xN
    (natSyms i ++ [])) ω P t A a wT i (c0w t P) hω ht ha hw hf.1 hf.2 (by simp)
    (by simp [recSt, recU]) (by simp [recSt, recU, hP]) (by simp [recSt, recU, hT])
    (by simp [recSt, recU, hA]) (by simp [recSt, recU, hab]) (by simp [recSt, recU])
    (by simp [recSt, recU, hD]) (by simp [recSt, recU, hB]) (by simp [recSt, recU])
    (by simp [recSt, recU, hW]) (by simp [recSt, recU, hPi]) (by simp [recSt, recU, hLn])
    (by simp [recSt, recU]) (by simp [recSt, recU, hPW]) (by simp [recSt, recU, hPW1])
    (by simp [recSt, recU, e45]) (by simp [recSt, recU, e46]) (by simp [recSt, recU, e47])
    (by simp [recSt, recU, e48]) (by simp [recSt, recU, e49]) (by simp [recSt, recU, e50])
    (by simp [recSt, recU, e51]) (by simp [recSt, recU, e52]) (by simp [recSt, recU, e53])
    (by simp [recSt, recU, e54]) (by simp [recSt, recU, e55]) (by simp [recSt, recU, e56])
    (by simp [recSt, recU, e57]) (by simp [recSt, recU, e58]) (by simp [recSt, recU, e59])
    (by simp [recSt, recU, e60]) W U hWK hWD hU1 hU2 hU3 bW6 bW7 hWi ρ
  refine hb.of_eq ?_ le_rfl
  rw [← hent]
  have hdrop : (tapWin t P).drop i = (tapWin t P)[i] :: (tapWin t P).drop (i + 1) :=
    List.drop_eq_getElem_cons hi'
  have e : recSt B ω P wT t A a i = Function.update (Function.update (recU B P t A) xN
      (natSyms i)) sTap (entBits ω P wT t A a (tapWin t P)[i] ++
        (((tapWin t P).drop (i + 1)).flatMap (entBits ω P wT t A a) ++ Sym.sep :: B sTap)) := by
    rw [recSt, hdrop, List.flatMap_cons, List.append_assoc]
  rw [e]
  exact loop_state_eq (recU B P t A) (natSyms (i + 1)) (natSyms i) _ _

end RecLoop

section RecClean

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.cleanProg_spec (hI : I.Spec Mul C) (B : TL → List Sym) (ω P wT t A a : ℕ)
    (e40 : B xTS = []) (e41 : B xKC = []) (e42 : B xBP = []) (e43 : B xC0 = [])
    (e44 : B xN = []) (W : ℕ) (hWA : 2 * tapPrec P + P + 1 ≤ W)
    (hWK : bitLen (kcN P t A) ≤ W) (ρ : List (TP I)) :
    HT ρ (recSt B ω P wT t A a 0) (cleanProg I)
      (Function.update B sTap
        (recSyms (crecBits wT ((tapWin t P).map (tapInt ω P t A a))) ++ B sTap))
      (4 * (C * (W + 1))) := by
  refine (HT.seq (HT.tdr' hI xC0 _ (c0w t P) (by simp [recSt, recU]) ρ)
    (HT.seq (HT.tdr' hI xKC _ (kcN P t A) (by simp [recSt, recU]) ρ)
    (HT.seq (HT.tdr' hI xBP _ (tapPrec P + P) (by simp [recSt, recU]) ρ)
      (HT.tdr' hI xTS _ (2 ^ (2 * tapPrec P - P)) (by simp [recSt, recU]) ρ)))).of_eq ?_ ?_
  · rw [recSyms_eq]
    simp only [recSt, List.drop_zero]
    exact clean_state_eq B P t A _ e40 e41 e42 e43 e44
  · have b1 : bitLen (c0w t P) ≤ W := (bitLen_le_self _).trans ((c0w_le t P).trans (by omega))
    have b2 : bitLen (tapPrec P + P) ≤ W := (bitLen_le_self _).trans (by omega)
    have b3 : bitLen (2 ^ (2 * tapPrec P - P)) ≤ W := by
      rw [bitLen_two_pow]
      omega
    have c1 : C * (bitLen (c0w t P) + 1) ≤ C * (W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c2 : C * (bitLen (kcN P t A) + 1) ≤ C * (W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c3 : C * (bitLen (tapPrec P + P) + 1) ≤ C * (W + 1) := Nat.mul_le_mul_left _ (by omega)
    have c4 : C * (bitLen (2 ^ (2 * tapPrec P - P)) + 1) ≤ C * (W + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    linarith

end RecClean

section RecMain

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

/-- Cost bound of the record machine. -/
def recCost (C : ℕ) (Mul : ℕ → ℕ) (P wT t W U : ℕ) : ℕ :=
  setupCost C Mul W + ((C + (Nw t P * (C * (W + 1) + recBodyCost C Mul P wT W U + C + 1) + 1)) +
    4 * (C * (W + 1)))

theorem HT.recProg_spec (hI : I.Spec Mul C) (B : TL → List Sym) (ω P wT t A a : ℕ)
    (hω : 1 ≤ ω) (hw : 1 ≤ wT) (ht : 1 ≤ t) (ha : a < A)
    (hfit : ∀ e ∈ tapWin t P, FitsTwos wT (tapInt ω P t A a e).1 ∧
      FitsTwos wT (tapInt ω P t A a e).2)
    (hP : B rP = natSyms P) (hW : B rW = natSyms ω) (hB : B rB = natSyms (tapPrec P))
    (hPi : B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hLn : B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec P))).1)
    (hPW : B rPW = intSyms ((2 ^ wT : ℕ) : ℤ)) (hPW1 : B rPW1 = intSyms ((2 ^ (wT + 1) : ℕ) : ℤ))
    (hT : B rT = natSyms t) (hA : B rA = natSyms A) (hD : B rDen = natSyms (2 * t * A))
    (hab : B ra = natSyms a) (htmp : ∀ j : Fin 61, 40 ≤ (j : ℕ) → B (.inr j) = [])
    (W U : ℕ) (hWA : 2 * tapPrec P + P + 1 ≤ W) (hWK : bitLen (kcN P t A) ≤ W)
    (hWD : bitLen (2 * t * A) ≤ W) (hWt : bitLen (t + 3 * P + 1) ≤ W)
    (hU1 : tapPrec P + bitLen (2 * t * A) + 1 ≤ U) (hU2 : ω + tapPrec P + bitLen A + 1 ≤ U)
    (hU3 : bitLen (tapPrec P + P) ≤ U) (ρ : List (TP I)) :
    HT ρ B (recProg I)
      (Function.update B sTap
        (recSyms (crecBits wT ((tapWin t P).map (tapInt ω P t A a))) ++ B sTap))
      (recCost C Mul P wT t W U) := by
  have e40 : B xTS = [] := htmp ⟨40, by decide⟩ (by decide)
  have e41 : B xKC = [] := htmp ⟨41, by decide⟩ (by decide)
  have e42 : B xBP = [] := htmp ⟨42, by decide⟩ (by decide)
  have e43 : B xC0 = [] := htmp ⟨43, by decide⟩ (by decide)
  have e44 : B xN = [] := htmp ⟨44, by decide⟩ (by decide)
  have e45 : B xCM = [] := htmp ⟨45, by decide⟩ (by decide)
  have e46 : B xAR = [] := htmp ⟨46, by decide⟩ (by decide)
  have e47 : B xAI = [] := htmp ⟨47, by decide⟩ (by decide)
  have e48 : B xM = [] := htmp ⟨48, by decide⟩ (by decide)
  have e49 : B y1 = [] := htmp ⟨49, by decide⟩ (by decide)
  have e50 : B y2 = [] := htmp ⟨50, by decide⟩ (by decide)
  have e51 : B y3 = [] := htmp ⟨51, by decide⟩ (by decide)
  have e52 : B y4 = [] := htmp ⟨52, by decide⟩ (by decide)
  have e53 : B y5 = [] := htmp ⟨53, by decide⟩ (by decide)
  have e54 : B y6 = [] := htmp ⟨54, by decide⟩ (by decide)
  have e55 : B y7 = [] := htmp ⟨55, by decide⟩ (by decide)
  have e56 : B y8 = [] := htmp ⟨56, by decide⟩ (by decide)
  have e57 : B y9 = [] := htmp ⟨57, by decide⟩ (by decide)
  have e58 : B y10 = [] := htmp ⟨58, by decide⟩ (by decide)
  have e59 : B y11 = [] := htmp ⟨59, by decide⟩ (by decide)
  have e60 : B y12 = [] := htmp ⟨60, by decide⟩ (by decide)
  refine (HT.seq (HT.setupAll_spec hI B ω P wT t A a ht ha hP hB hT hA e40 e41 e42 e43 e44
      e49 e50 e51 e52 e53 e54 W hWA hWK hWt ρ)
    (HT.seq (HT.recLoop_spec hI B ω P wT t A a hω hw ht ha hfit hP hW hB hPi hLn hPW hPW1 hT hA
      hD hab e45 e46 e47 e48 e49 e50 e51 e52 e53 e54 e55 e56 e57 e58 e59 e60 W U hWK hWD hWt
      hU1 hU2 hU3 ρ)
      (HT.cleanProg_spec hI B ω P wT t A a e40 e41 e42 e43 e44 W hWA hWK ρ))).mono ?_
  unfold recCost
  have hl := loopCost_le_unif (fun i => C * (bitLen (i + 1) + 1) + recBodyCost C Mul P wT W U + C)
    (C * (W + 1) + recBodyCost C Mul P wT W U + C) (Nw t P)
    (fun k hk => by
      have hk' : bitLen (k + 1) ≤ W := by
        have : k + 1 ≤ t + 3 * P + 1 := by unfold Nw at hk; split_ifs at hk <;> omega
        exact (bitLen_mono this).trans hWt
      exact Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_left C (by omega : bitLen (k + 1) + 1 ≤ W + 1)) _) _)
  linarith

end RecMain


/-! ## Cost arithmetic -/

section CostArith

theorem v4_facts {V : ℕ} (hV : 1 ≤ V) : V ≤ V ^ 4 ∧ V ^ 2 ≤ V ^ 4 ∧ 1 ≤ V ^ 4 ∧ V ^ 4 ≤ V ^ 5 :=
  ⟨Nat.le_self_pow (by norm_num) V, Nat.pow_le_pow_right hV (by norm_num),
    Nat.one_le_pow _ _ hV, Nat.pow_le_pow_right hV (by norm_num)⟩

theorem sq9_le {V : ℕ} (hV : 1 ≤ V) : (2 * V + 1) ^ 2 ≤ 9 * V ^ 4 := by
  obtain ⟨h1, h2, h3, -⟩ := v4_facts hV
  have h5 : (2 * V + 1) ^ 2 = 4 * V ^ 2 + 4 * V + 1 := by ring
  rw [h5]
  linarith

theorem sq4_le {V n : ℕ} (hV : 1 ≤ V) (hn : n ≤ V) : (n + 1) ^ 2 ≤ 4 * V ^ 4 := by
  have h : (n + 1) ^ 2 ≤ (2 * V) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  obtain ⟨-, h2, -, -⟩ := v4_facts hV
  have e : (2 * V) ^ 2 = 4 * V ^ 2 := by ring
  linarith

theorem C_le_X (C KM : ℕ) : C ≤ (C + 1) * (KM + 1) :=
  Nat.le_trans (Nat.le_succ C) (Nat.le_mul_of_pos_right _ (Nat.succ_pos KM))

theorem one_le_X0 (C KM : ℕ) : 1 ≤ (C + 1) * (KM + 1) :=
  Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)

theorem mulX_le {C KM n c V : ℕ} (h : n ≤ c * V ^ 4) :
    C * n ≤ c * ((C + 1) * (KM + 1) * V ^ 4) := by
  calc C * n ≤ C * (c * V ^ 4) := Nat.mul_le_mul_left C h
    _ ≤ (C + 1) * (KM + 1) * (c * V ^ 4) := Nat.mul_le_mul_right _ (C_le_X C KM)
    _ = c * ((C + 1) * (KM + 1) * V ^ 4) := by ring

theorem mulKM_le {C KM n c V : ℕ} {Mul : ℕ → ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (h : (n + 1) ^ 2 ≤ c * V ^ 4) : C * Mul n ≤ c * ((C + 1) * (KM + 1) * V ^ 4) := by
  calc C * Mul n ≤ C * (KM * (n + 1) ^ 2) := Nat.mul_le_mul_left C (hMul n)
    _ = (C * KM) * (n + 1) ^ 2 := by ring
    _ ≤ ((C + 1) * (KM + 1)) * (c * V ^ 4) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)) h
    _ = c * ((C + 1) * (KM + 1) * V ^ 4) := by ring

theorem one_le_X {C KM V : ℕ} (hV : 1 ≤ V) : 1 ≤ (C + 1) * (KM + 1) * V ^ 4 :=
  Nat.mul_pos (one_le_X0 C KM) (Nat.one_le_pow _ _ hV)

theorem V4_le_X {C KM V : ℕ} : V ^ 4 ≤ (C + 1) * (KM + 1) * V ^ 4 :=
  Nat.le_mul_of_pos_left _ (one_le_X0 C KM)

theorem sampleCost_le {C KM : ℕ} {Mul : ℕ → ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    {V w V' : ℕ} (hV : 1 ≤ V) (hw : w ≤ V) (hV' : V' ≤ 2 * V) :
    sampleCost C Mul (2 * V) V w V' ≤ 262 * ((C + 1) * (KM + 1) * V ^ 4) := by
  obtain ⟨a1, a2, a3, -⟩ := v4_facts hV
  have f1 : C * Mul (2 * V) ≤ 9 * ((C + 1) * (KM + 1) * V ^ 4) := mulKM_le hMul (sq9_le hV)
  have f2 : C * (2 * V + 1) ^ 2 ≤ 9 * ((C + 1) * (KM + 1) * V ^ 4) := mulX_le (sq9_le hV)
  have f3 : C * V ^ 4 ≤ 1 * ((C + 1) * (KM + 1) * V ^ 4) := mulX_le (by omega)
  have f4 : C * (2 * V + 1) ≤ 3 * ((C + 1) * (KM + 1) * V ^ 4) := mulX_le (by omega)
  have f5 : C * Mul w ≤ 4 * ((C + 1) * (KM + 1) * V ^ 4) := mulKM_le hMul (sq4_le hV hw)
  have f6 : C * (V' + 1) ≤ 3 * ((C + 1) * (KM + 1) * V ^ 4) := mulX_le (by omega)
  have f9 : C * (w + 1) ≤ 2 * ((C + 1) * (KM + 1) * V ^ 4) := mulX_le (by omega)
  have f7 : V' ≤ 2 * ((C + 1) * (KM + 1) * V ^ 4) := by
    have := V4_le_X (C := C) (KM := KM) (V := V)
    omega
  have f8 := one_le_X (C := C) (KM := KM) hV
  unfold sampleCost
  linarith

theorem bodyCost_le {C KM : ℕ} {Mul : ℕ → ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    {V w V' : ℕ} (hV : 1 ≤ V) (hw : w ≤ V) (hV' : V' ≤ 2 * V) :
    bodyCost C Mul (2 * V) V w V' ≤ 301 * ((C + 1) * (KM + 1) * V ^ 4) := by
  have h1 := sampleCost_le (C := C) hMul hV hw hV'
  have f2 : C * (2 * V + 1) ^ 2 ≤ 9 * ((C + 1) * (KM + 1) * V ^ 4) := mulX_le (sq9_le hV)
  have f8 := one_le_X (C := C) (KM := KM) hV
  unfold bodyCost
  linarith

theorem entryCost_le {C KM : ℕ} {Mul : ℕ → ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    {P wT V : ℕ} (hV : 1 ≤ V) (hw : tapPrec P + 4 ≤ V) (hA : accW P ≤ 2 * V) :
    entryCost C Mul P wT (2 * V) V ≤
      410 * ((C + 1) * (KM + 1) * ((2 * P + 1) * V ^ 5 + wT + 1)) := by
  obtain ⟨a1, a2, a3, a4⟩ := v4_facts hV
  have hb := bodyCost_le (C := C) hMul hV hw hA
  have hC := C_le_X C KM
  have hX1 := one_le_X0 C KM
  have hY : (C + 1) * (KM + 1) * V ^ 4 ≤ (C + 1) * (KM + 1) * ((2 * P + 1) * V ^ 5) :=
    Nat.mul_le_mul_left _ (le_trans a4 (Nat.le_mul_of_pos_left _ (by omega)))
  have f1 : C * (2 * (2 * V) + 1) ≤ 5 * ((C + 1) * (KM + 1) * V ^ 4) := mulX_le (by omega)
  have f2 : C * (2 * V + 1) ≤ 3 * ((C + 1) * (KM + 1) * V ^ 4) := mulX_le (by omega)
  have f3 : C * (accW P + 1) ^ 2 ≤ 9 * ((C + 1) * (KM + 1) * V ^ 4) := by
    have : (accW P + 1) ^ 2 ≤ (2 * V + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    exact mulX_le (this.trans (sq9_le hV))
  have f4 : C * accW P ≤ 2 * ((C + 1) * (KM + 1) * V ^ 4) := mulX_le (by omega)
  have f5 : C * wT ≤ (C + 1) * (KM + 1) * wT := Nat.mul_le_mul_right _ hC
  have f6 : wT ≤ (C + 1) * (KM + 1) * wT := Nat.le_mul_of_pos_left _ hX1
  have hX4 := one_le_X (C := C) (KM := KM) hV
  have hCV : C ≤ (C + 1) * (KM + 1) * V ^ 4 := le_trans hC (Nat.le_mul_of_pos_right _ (by omega))
  have hin : C * (2 * V + 1) + bodyCost C Mul (2 * V) V (tapPrec P + 4) (accW P) + C + 1 ≤
      306 * ((C + 1) * (KM + 1) * V ^ 4) := by
    linarith
  have hmain : (2 * P + 1) * (C * (2 * V + 1) + bodyCost C Mul (2 * V) V (tapPrec P + 4) (accW P)
      + C + 1) ≤ 306 * ((C + 1) * (KM + 1) * ((2 * P + 1) * V ^ 5)) := by
    calc (2 * P + 1) * (C * (2 * V + 1) + bodyCost C Mul (2 * V) V (tapPrec P + 4) (accW P)
          + C + 1)
        ≤ (2 * P + 1) * (306 * ((C + 1) * (KM + 1) * V ^ 4)) := Nat.mul_le_mul_left _ hin
      _ = 306 * ((C + 1) * (KM + 1) * ((2 * P + 1) * V ^ 4)) := by ring
      _ ≤ 306 * ((C + 1) * (KM + 1) * ((2 * P + 1) * V ^ 5)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ a4))
  unfold entryCost
  linarith

theorem recCost_le {C KM : ℕ} {Mul : ℕ → ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    {P wT t V : ℕ} (hV : 1 ≤ V) (hw : tapPrec P + 4 ≤ V) (hA : accW P ≤ 2 * V)
    (hN : 1 ≤ Nw t P) :
    recCost C Mul P wT t (2 * V) V ≤
      1000 * (C + 1) * (KM + 1) * (Nw t P * ((2 * P + 1) * V ^ 5 + wT + 1)) := by
  obtain ⟨a1, a2, a3, a4⟩ := v4_facts hV
  have he := entryCost_le (C := C) (wT := wT) hMul hV hw hA
  have hC := C_le_X C KM
  have hX1 := one_le_X0 C KM
  have hX4 := one_le_X (C := C) (KM := KM) hV
  have hE5 : V ^ 4 ≤ (2 * P + 1) * V ^ 5 + wT + 1 := by
    have : V ^ 5 ≤ (2 * P + 1) * V ^ 5 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hYE : (C + 1) * (KM + 1) * V ^ 4 ≤
      (C + 1) * (KM + 1) * ((2 * P + 1) * V ^ 5 + wT + 1) :=
    Nat.mul_le_mul_left _ hE5
  have hCE : C ≤ (C + 1) * (KM + 1) * ((2 * P + 1) * V ^ 5 + wT + 1) :=
    le_trans hC (Nat.le_mul_of_pos_right _ (by omega))
  have hXE : 1 ≤ (C + 1) * (KM + 1) * ((2 * P + 1) * V ^ 5 + wT + 1) := le_trans hX4 hYE
  have g1 : C * (2 * (2 * V) + 1) ≤ 5 * ((C + 1) * (KM + 1) * V ^ 4) := mulX_le (by omega)
  have g2 : C * Mul (2 * V) ≤ 9 * ((C + 1) * (KM + 1) * V ^ 4) := mulKM_le hMul (sq9_le hV)
  have g3 : C * (2 * V + 1) ≤ 3 * ((C + 1) * (KM + 1) * V ^ 4) := mulX_le (by omega)
  have g4 : C * (2 * V + 1) ^ 2 ≤ 9 * ((C + 1) * (KM + 1) * V ^ 4) := mulX_le (sq9_le hV)
  have inner : C * (2 * V + 1) + recBodyCost C Mul P wT (2 * V) V + C + 1 ≤
      460 * ((C + 1) * (KM + 1) * ((2 * P + 1) * V ^ 5 + wT + 1)) := by
    unfold recBodyCost
    linarith
  have hloop : Nw t P * (C * (2 * V + 1) + recBodyCost C Mul P wT (2 * V) V + C + 1) ≤
      Nw t P * (460 * ((C + 1) * (KM + 1) * ((2 * P + 1) * V ^ 5 + wT + 1))) :=
    Nat.mul_le_mul_left _ inner
  have hNXE : (C + 1) * (KM + 1) * ((2 * P + 1) * V ^ 5 + wT + 1) ≤
      Nw t P * ((C + 1) * (KM + 1) * ((2 * P + 1) * V ^ 5 + wT + 1)) :=
    Nat.le_mul_of_pos_left _ hN
  unfold recCost setupCost
  linarith

end CostArith

/-! ## Size bounds for the instantiation `W = 2V`, `U = V` -/

section Bounds

theorem tapPrec_le (P : ℕ) : tapPrec P ≤ 2 * P + 21 := by
  have hp := Nat.lt_two_pow_self (n := P)
  have e : 2 ^ (P + 1) = 2 ^ P * 2 := pow_succ 2 P
  have h2 : 2 * P + 2 ≤ 2 ^ (P + 1) := by omega
  have h : SubNLogN.Math.Common.lg (2 * P + 2) ≤ P + 1 := by
    unfold SubNLogN.Math.Common.lg
    exact max_le (Nat.clog_le_of_le_pow h2) (by omega)
  unfold tapPrec tapGuard
  omega

theorem rec_bounds (ω P t A : ℕ) (ht : 1 ≤ t) (hA : 0 < A) (V : ℕ)
    (hV : V = ω + 4 * P + 2 * Nat.size (2 * t * A) + 100) :
    2 * tapPrec P + P + 1 ≤ 2 * V ∧ bitLen (kcN P t A) ≤ 2 * V ∧ bitLen (2 * t * A) ≤ 2 * V ∧
    bitLen (t + 3 * P + 1) ≤ 2 * V ∧ tapPrec P + bitLen (2 * t * A) + 1 ≤ V ∧
    ω + tapPrec P + bitLen A + 1 ≤ V ∧ bitLen (tapPrec P + P) ≤ V ∧ 1 ≤ V ∧
    tapPrec P + 4 ≤ V ∧ accW P ≤ 2 * V := by
  have hTP := tapPrec_le P
  have hS : bitLen (2 * t * A) ≤ Nat.size (2 * t * A) := bitLen_le_of_lt (Nat.lt_size_self _)
  have hAle : A ≤ 2 * t * A := Nat.le_mul_of_pos_left A (by omega)
  have htle : t ≤ 2 * t * A :=
    le_trans (Nat.le_mul_of_pos_left t (by norm_num)) (Nat.le_mul_of_pos_right _ hA)
  have hbA : bitLen A ≤ Nat.size (2 * t * A) := (bitLen_mono hAle).trans hS
  have hbt : bitLen t ≤ Nat.size (2 * t * A) := (bitLen_mono htle).trans hS
  have hp := Nat.lt_two_pow_self (n := P)
  have e1 : 2 ^ (P + 1) = 2 ^ P * 2 := pow_succ 2 P
  have e2 : 2 ^ (P + 2) = 2 ^ P * 4 := by rw [pow_add]; norm_num
  have hP1 : bitLen (2 * P + 1) ≤ P + 1 := bitLen_le_of_lt (by omega)
  have hP3 : bitLen (3 * P + 1) ≤ P + 2 := bitLen_le_of_lt (by omega)
  have hkc : kcN P t A ≤ (2 * P + 1) * (2 * t * A) := by
    unfold kcN
    have h1 : P * A ≤ t * P * A := Nat.mul_le_mul_right A (Nat.le_mul_of_pos_left P (by omega))
    have h2 : 0 ≤ t * P * A := Nat.zero_le _
    linarith
  have hm1 := bitLen_mul_le (2 * P + 1) (2 * t * A)
  have hbk : bitLen (kcN P t A) ≤ P + 1 + Nat.size (2 * t * A) :=
    (bitLen_mono hkc).trans (by omega)
  have hbt3 : bitLen (t + 3 * P + 1) ≤ Nat.size (2 * t * A) + P + 3 := by
    have e : t + 3 * P + 1 = t + (3 * P + 1) := by omega
    rw [e]
    have h := bitLen_add_le t (3 * P + 1)
    have hm : max (bitLen t) (bitLen (3 * P + 1)) ≤ bitLen t + bitLen (3 * P + 1) :=
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    omega
  have hbTP : bitLen (tapPrec P + P) ≤ tapPrec P + P := bitLen_le_self _
  have haccW : accW P ≤ 5 * P + 47 := by unfold accW; omega
  subst hV
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega⟩

theorem one_le_Nw {t P : ℕ} (ht : 1 ≤ t) : 1 ≤ Nw t P := by
  unfold Nw
  split_ifs <;> omega

end Bounds

end SubNLogN.Machine.Tables.TapAux

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms

/-- **`TapRecStmt` holds**, with `K = 1000` and the program `TapAux.recProg I` (instantiated with
the widths `W = 2V`, `U = V`, `V = ω + 4P + 2·size(2tA) + 100`). -/
theorem tapRec_holds : TapRecStmt := by
  refine ⟨1000, fun I Mul C KM hI hMul => ⟨TapAux.recProg I, TapAux.recProg_closed I, ?_⟩⟩
  intro B ω P wT t A a hω hw ht ha hfit hP hW hB hPi hLn hPW hPW1 hT hA hD hab htmp
  obtain ⟨V, hV⟩ : ∃ V, V = ω + 4 * P + 2 * Nat.size (2 * t * A) + 100 := ⟨_, rfl⟩
  obtain ⟨hWA, hWK, hWD, hWt, hU1, hU2, hU3, hV1, hwV, haV⟩ :=
    TapAux.rec_bounds ω P t A ht (by omega) V hV
  refine (TapAux.HT.recProg_spec hI B ω P wT t A a hω hw ht ha hfit hP hW hB hPi hLn hPW hPW1
    hT hA hD hab htmp (2 * V) V hWA hWK hWD hWt hU1 hU2 hU3 []).mono ?_
  unfold tapRecCost
  rw [TapAux.tapWin_length, ← hV]
  exact TapAux.recCost_le hMul hV1 hwV haV (TapAux.one_le_Nw ht)

end SubNLogN.Machine.Tables
