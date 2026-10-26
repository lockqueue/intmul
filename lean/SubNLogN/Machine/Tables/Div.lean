/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.Emit
import SubNLogN.Math.Common.GridInt

/-!
# K6 (`Machine/Tables/Div.lean`): signed helpers and half-up division

**Scope (honest summary).** Infrastructure only:
* `intDrop` (pop a signed number, `HT.intDrop_spec`) and `maxZero` (`z ↦ max 0 z` in place,
  `HT.maxZero_spec`), with closedness lemmas `intDrop_closed` and `maxZero_closed`;
* `rhuDivProg` (`HT.rhuDivProg_spec`, cost `rdCost`): push `intSyms (rhuDiv n d)` for any signed
  `n, d`, where `rhuDiv n d = ⌊n/d + 1/2⌋` (`0` for `d = 0`; `SubNLogN/Math/Common/GridInt.lean`),
  by W6a's `divRoundRatInt` on `|d|` with `n` or `-n` (`rhuDiv_eq_divRound_pos`, `rhuDiv_eq_divRound_neg`).
  (The bit-list loop `bitLoop` / `HT.bitLoop_spec` lives in `Tables/Pow.lean`.)
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Common.GridInt

/-! ## Pure facts about `rhuDiv` -/

theorem rhuDiv_eq_divRound_pos (n : ℤ) (d : ℕ) (hd : 0 < d) :
    rhuDiv n d = divRoundRatInt n d := by
  unfold rhuDiv divRoundRatInt
  rw [if_pos (by positivity), if_pos (by exact_mod_cast hd)]

theorem rhuDiv_zero (n : ℤ) : rhuDiv n 0 = 0 := by
  unfold rhuDiv
  simp

theorem rhuDiv_eq_divRound_neg (n : ℤ) (d : ℕ) (hd : 0 < d) :
    rhuDiv n (-(d : ℤ)) = divRoundRatInt (0 - n) d := by
  unfold rhuDiv divRoundRatInt
  rw [if_neg (by omega), if_pos (by exact_mod_cast hd)]
  congr 1 <;> ring

theorem intSyms_neg_nat {d : ℕ} (hd : 0 < d) : intSyms (-(d : ℤ)) = Sym.neg :: natSyms d := by
  simp [intSyms, sgnSym, hd]

theorem intSyms_eq_cons (z : ℤ) : intSyms z = sgnSym z :: natSyms z.natAbs := rfl

/-! ## Small signed fragments -/

section Small

variable (I : TB)

/-- Pop a signed number. -/
def intDrop (X : TL) : TP I := (tpop I X).seq (tdr I X)

/-- `z ↦ max 0 z` in place. -/
def maxZero (X : TL) : TP I :=
  (popR' I.lS X).seq (Prog.ite (fun v => decide (I.lS.get v = some Sym.neg))
    ((tdr I X).seq (tpush I X .pos)) (tpush I X .pos))

theorem intDrop_closed (X : TL) : (intDrop I X).Closed := ⟨trivial, callI_closed _ _ _ _⟩

theorem maxZero_closed (X : TL) : (maxZero I X).Closed :=
  ⟨trivial, ⟨⟨callI_closed _ _ _ _, trivial⟩, trivial⟩⟩

variable {I} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.intDrop_spec (hI : I.Spec Mul C) (X : TL) (B : TL → List Sym) (z : ℤ) (r : List Sym)
    (hr : TermOK r) (hB : B X = intSyms z ++ r) (ρ : List (TP I)) :
    HT ρ B (intDrop I X) (Function.update B X r) (1 + C * (bitLen z.natAbs + 1)) := by
  have hB' : B X = sgnSym z :: (natSyms z.natAbs ++ r) := by rw [hB]; rfl
  refine (HT.seq (HT.tpop_spec X B _ _ hB' ρ)
    (HT.tdr_spec hI X _ z.natAbs r hr (by rw [Function.update_self]) ρ)).of_eq ?_ le_rfl
  rw [Function.update_idem]

theorem HT.maxZero_spec (hI : I.Spec Mul C) (X : TL) (B : TL → List Sym) (z : ℤ) (r : List Sym)
    (hr : TermOK r) (hB : B X = intSyms z ++ r) (ρ : List (TP I)) :
    HT ρ B (maxZero I X) (Function.update B X (intSyms (max 0 z) ++ r))
      (1 + (C * (bitLen z.natAbs + 1) + 1 + 1)) := by
  have hB' : B X = sgnSym z :: (natSyms z.natAbs ++ r) := by rw [hB]; rfl
  refine (HT.popBranch I.lS X B _ (sgnSym z) _ hB' (fun o => decide (o = some Sym.neg)) _ _ ρ
    (T₁ := C * (bitLen z.natAbs + 1) + 1) (T₂ := 1) (fun h => ?_) (fun h => ?_)).mono ?_
  · have hneg : z < 0 := (sgnSym_neg_iff z).mp (by simpa using h)
    refine (HT.seq (HT.tdr_spec hI X _ z.natAbs r hr (by rw [Function.update_self]) ρ)
      (HT.tpush_spec X .pos _ ρ)).of_eq ?_ le_rfl
    rw [Function.update_idem, Function.update_idem, Function.update_self, max_eq_left hneg.le]
    rfl
  · have hpos : 0 ≤ z := by
      by_contra hc
      exact absurd ((sgnSym_neg_iff z).mpr (by omega)) (by simpa using h)
    refine (HT.tpush_spec X .pos _ ρ).of_eq ?_ le_rfl
    rw [Function.update_idem, Function.update_self, max_eq_right hpos, intSyms_eq_cons,
      show sgnSym z = Sym.pos from by unfold sgnSym; simp [not_lt.mpr hpos]]
    rfl
  · simp

end Small

/-! ## Half-up division of signed numbers -/

section Div

variable (I : TB)

/-- Push `intSyms (rhuDiv n d)` onto `Z` (`X = intSyms n`, `Y = intSyms d`, both restored), using
the empty temporaries `Tz`, `Tn`. -/
def rhuDivProg (X Y Z Tz Tn : TL) : TP I :=
  (popR' I.lS Y).seq (Prog.ite (fun v => decide (I.lS.get v = some Sym.neg))
    ((tpush I Tz .pos).seq ((tsi I Tz X Tn).seq ((tdv I Tn Y Z).seq ((intDrop I Tn).seq
      ((tpop I Tz).seq (tpush I Y .neg))))))
    (((tiz I Y).seq (Prog.ite (fun v => I.iz.obs (I.liz.get v)) (tpush I Z .pos)
      (tdv I X Y Z))).seq (tpush I Y .pos)))

theorem rhuDivProg_closed (X Y Z Tz Tn : TL) : (rhuDivProg I X Y Z Tz Tn).Closed :=
  ⟨trivial, ⟨⟨trivial, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨intDrop_closed I _,
    ⟨trivial, trivial⟩⟩⟩⟩⟩, ⟨⟨callI_closed _ _ _ _, ⟨trivial, callI_closed _ _ _ _⟩⟩, trivial⟩⟩⟩

/-- Cost bound of `rhuDivProg` (`nb = |n|`, `db = |d|` in bits). -/
def rdCost (C nb db : ℕ) : ℕ := C * (nb * db + nb + db + 1) + 2 * C * (nb + 2) + 2 * C + 10

variable {I} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.rhuDivProg_spec (hI : I.Spec Mul C) (X Y Z Tz Tn : TL)
    (hnd : [X, Y, Z, Tz, Tn].Nodup) (B : TL → List Sym) (n d : ℤ) (rx ry : List Sym)
    (hrx : TermOK rx) (hry : TermOK ry) (hX : B X = intSyms n ++ rx) (hY : B Y = intSyms d ++ ry)
    (hTz : B Tz = []) (hTn : B Tn = []) (ρ : List (TP I)) :
    HT ρ B (rhuDivProg I X Y Z Tz Tn) (Function.update B Z (intSyms (rhuDiv n d) ++ B Z))
      (rdCost C (bitLen n.natAbs) (bitLen d.natAbs)) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hXY, hXZ, hXz, hXn⟩, ⟨hYZ, hYz, hYn⟩, ⟨hZz, hZn⟩, hzn⟩ := hnd
  have hYX := Ne.symm hXY; have hZX := Ne.symm hXZ; have hzX := Ne.symm hXz
  have hnX := Ne.symm hXn; have hZY := Ne.symm hYZ; have hzY := Ne.symm hYz
  have hnY := Ne.symm hYn; have hzZ := Ne.symm hZz; have hnZ := Ne.symm hZn
  have hnz := Ne.symm hzn
  have hY' : B Y = sgnSym d :: (natSyms d.natAbs ++ ry) := by rw [hY]; rfl
  set nb := bitLen n.natAbs with hnb
  set db := bitLen d.natAbs with hdb
  refine (HT.popBranch I.lS Y B _ (sgnSym d) _ hY' (fun o => decide (o = some Sym.neg)) _ _ ρ
    (T₁ := C * (nb * db + nb + db + 1) + 2 * C * (nb + 2) + 4)
    (T₂ := C + (C * (nb * db + nb + db + 1) + 1) + 1 + 1) (fun h => ?_) (fun h => ?_)).mono ?_
  · -- d < 0
    have hneg : d < 0 := (sgnSym_neg_iff d).mp (by simpa using h)
    obtain ⟨m, hm0, hdm⟩ : ∃ m : ℕ, 0 < m ∧ d = -(m : ℤ) := ⟨d.natAbs, by omega, by omega⟩
    have hdm' : d.natAbs = m := by rw [hdm]; simp
    rw [hdm'] at hdb ⊢
    refine (HT.seq (HT.tpush_spec Tz .pos _ ρ)
      (HT.seq (HT.tsi_spec hI Tz X Tn (by simp [hzX, hzn, hXn]) _ 0 n [] rx TermOK.nil hrx
        (by simp [Function.update_apply, hzY, hTz, intSyms_zero])
        (by simp [Function.update_apply, hXz, hXY, hX]) ρ)
      (HT.seq (HT.tdv_spec hI Tn Y Z (by simp [hnY, hnZ, hYZ]) _ (0 - n) m [] ry hm0 TermOK.nil
        hry (by simp [Function.update_apply, hnz, hnY, hTn])
        (by simp [Function.update_apply, hYn, hYz]) ρ)
      (HT.seq (HT.intDrop_spec hI Tn _ (0 - n) [] TermOK.nil
        (by simp [Function.update_apply, hnZ, hnz, hnY, hTn]) ρ)
      (HT.seq (HT.tpop_spec Tz _ Sym.pos []
        (by simp [Function.update_apply, hzn, hzZ, hzY, hTz]) ρ)
        (HT.tpush_spec Y .neg _ ρ)))))).of_eq ?_ ?_
    · rw [hdm, rhuDiv_eq_divRound_neg n m hm0]
      funext g
      by_cases hgY : g = Y
      · subst hgY
        simp [Function.update_apply, hYz, hYn, hYZ, hY, hdm, intSyms_neg_nat hm0]
      by_cases hgz : g = Tz
      · subst hgz
        simp [Function.update_apply, hzY, hzn, hzZ, hTz]
      by_cases hgn : g = Tn
      · subst hgn
        simp [Function.update_apply, hnY, hnz, hnZ, hTn]
      by_cases hgZ : g = Z
      · subst hgZ
        simp [Function.update_apply, hZY, hZn, hZz]
      simp [Function.update_apply, hgY, hgz, hgn, hgZ]
    · have h0 : bitLen (0 : ℤ).natAbs = 0 := by decide
      have h1 : (0 - n).natAbs = n.natAbs := by omega
      rw [h0, h1, ← hnb, ← hdb]
      nlinarith
  · -- d ≥ 0
    have hpos : 0 ≤ d := by
      by_contra hc
      exact absurd ((sgnSym_neg_iff d).mpr (by omega)) (by simpa using h)
    obtain ⟨m, hdm⟩ : ∃ m : ℕ, d = (m : ℤ) := ⟨d.natAbs, by omega⟩
    have hdm' : d.natAbs = m := by rw [hdm]; simp
    rw [hdm'] at hdb ⊢
    have hsg : sgnSym d = Sym.pos := by unfold sgnSym; simp [not_lt.mpr hpos]
    have hb : HT ρ (Function.update B Y (natSyms m ++ ry))
        ((tiz I Y).seq (Prog.ite (fun v => I.iz.obs (I.liz.get v)) (tpush I Z .pos)
          (tdv I X Y Z)))
        (Function.update (Function.update B Y (natSyms m ++ ry)) Z (intSyms (rhuDiv n d) ++ B Z))
        (C + (max 1 (C * (nb * db + nb + db + 1)) + 1)) := by
      refine HT.tizIte_spec hI Y _ _ m ry hry (by simp) (tpush I Z .pos) (tdv I X Y Z) ρ
        (fun h0 => ?_) (fun h0 => ?_)
      · subst h0
        refine (HT.tpush_spec Z .pos _ ρ).of_eq ?_ le_rfl
        rw [hdm, Nat.cast_zero, rhuDiv_zero, intSyms_zero, Function.update_of_ne hZY]
        rfl
      · refine (HT.tdv_spec hI X Y Z (by simp [hXY, hXZ, hYZ]) _ n m rx ry (by omega) hrx hry
          (by simp [Function.update_apply, hXY, hX]) (by simp) ρ).of_eq ?_ (by rw [hnb, hdb])
        rw [hdm, rhuDiv_eq_divRound_pos n m (by omega), Function.update_of_ne hZY]
    refine (HT.seq hb (HT.tpush_spec Y .pos _ ρ)).of_eq ?_ ?_
    · funext g
      by_cases hgY : g = Y
      · subst hgY
        simp [Function.update_apply, hYZ, hY, hdm, intSyms_natCast]
      by_cases hgZ : g = Z
      · subst hgZ
        simp [Function.update_apply, hZY]
      simp [Function.update_apply, hgY, hgZ]
    · have : max 1 (C * (nb * db + nb + db + 1)) ≤ C * (nb * db + nb + db + 1) + 1 :=
        max_le (by omega) (by omega)
      omega
  · have hC : C ≤ 2 * C * (nb + 2) := by nlinarith
    have := max_le (show C * (nb * db + nb + db + 1) + 2 * C * (nb + 2) + 4 ≤
        C * (nb * db + nb + db + 1) + 2 * C * (nb + 2) + 4 by omega)
      (show C + (C * (nb * db + nb + db + 1) + 1) + 1 + 1 ≤
        C * (nb * db + nb + db + 1) + 2 * C * (nb + 2) + 4 by omega)
    unfold rdCost
    omega

end Div

end SubNLogN.Machine.Tables
