/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.Pow
import SubNLogN.Machine.Tables.SolMath
import SubNLogN.Machine.Tables.Roles

/-!
# K6 (`Machine/Tables/SolCoef.lean`): solver entries, part 1 — the oriented coefficients

**Scope (honest summary).** Signed-number move `tmvInt` (`HT.tmvInt_spec`) and the orientation
fragment `solOrient` (`HT.solOrient_spec`: from `x41 = 2u` and `x42 = intSyms c0 ++ intSyms c1`,
store the oriented numerators `ĉ_max`, `ĉ_min` on `x43`, `x44` according to `2u < t`; combined with
`W7_c0c1` (`Contracts/W7/Kernels.lean:152`) in `solCoeffs2` / `HT.solCoeffs2_spec` of `SolGam.lean`).
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms

/-- Move a signed number from `X` to `Y` (W7k2's `moveInt` with the bundle's instances). -/
def tmvInt (I : TB) (X Y : TL) : TP I := moveInt I.cp I.dr I.lS I.lcp I.ldr X Y t0

theorem tmvInt_closed (I : TB) (X Y : TL) : (tmvInt I X Y).Closed := moveInt_closed _ _ _ _ _ _ _ _

theorem HT.tmvInt_spec {I : TB} {Mul : ℕ → ℕ} {C : ℕ} (hI : I.Spec Mul C) (X Y : TL) (hXY : X ≠ Y)
    (B : TL → List Sym) (z : ℤ) (rx : List Sym) (hrx : TermOK rx) (hB : B X = intSyms z ++ rx)
    (ρ : List (TP I)) :
    HT ρ B (tmvInt I X Y) (Function.update (Function.update B Y (intSyms z ++ B Y)) X rx)
      (C * (bitLen z.natAbs + 1) + C * (bitLen z.natAbs + 1) + 3) :=
  HT.moveInt hI.cp hI.dr I.lS I.lcp I.ldr X Y t0 hXY (by decide) B z rx hrx hB ρ

/-! ## Part 1: the oriented coefficients -/

/-- Orientation: from `x42 = intSyms c0 ++ intSyms c1`, put `ĉ_max` on `x43` and `ĉ_min` on `x44`
(test `2u < t` with `x41 = 2u`). -/
def solOrient (I : TB) : TP I :=
  (tcm I x41 rT).seq (Prog.ite (fun s => decide (I.cm.obs (I.lcm.get s) = .lt))
    ((tmvInt I x42 x43).seq (tmvInt I x42 x44)) ((tmvInt I x42 x44).seq (tmvInt I x42 x43)))

theorem solOrient_closed (I : TB) : (solOrient I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨⟨tmvInt_closed _ _ _, tmvInt_closed _ _ _⟩,
    ⟨tmvInt_closed _ _ _, tmvInt_closed _ _ _⟩⟩⟩

section Orient

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.solOrient_spec (hI : I.Spec Mul C) (S : TL → List Sym) (u t : ℕ) (c0 c1 : ℤ)
    (h41 : S x41 = natSyms (u + u)) (hT : S rT = natSyms t)
    (h42 : S x42 = intSyms c0 ++ intSyms c1) (h43 : S x43 = []) (h44 : S x44 = [])
    (ρ : List (TP I)) :
    HT ρ S (solOrient I)
      (Function.update (Function.update (Function.update S x42 []) x43
        (intSyms (if 2 * u < t then c0 else c1))) x44 (intSyms (if 2 * u < t then c1 else c0)))
      (C * (bitLen (u + u) + bitLen t + 1) +
        (2 * (C * (bitLen c0.natAbs + bitLen c1.natAbs + 2)) + 6 + 1)) := by
  have hc : C * (bitLen c0.natAbs + 1) + C * (bitLen c0.natAbs + 1) + 3 +
      (C * (bitLen c1.natAbs + 1) + C * (bitLen c1.natAbs + 1) + 3) ≤
      2 * (C * (bitLen c0.natAbs + bitLen c1.natAbs + 2)) + 6 := by nlinarith
  refine HT.tcmIte_spec hI x41 rT (by decide) S _ (u + u) t [] [] TermOK.nil TermOK.nil
    (by rw [h41, List.append_nil]) (by rw [hT, List.append_nil]) (fun o => decide (o = .lt))
    _ _ ρ (T₁ := 2 * (C * (bitLen c0.natAbs + bitLen c1.natAbs + 2)) + 6)
    (T₂ := 2 * (C * (bitLen c0.natAbs + bitLen c1.natAbs + 2)) + 6) (fun h => ?_) (fun h => ?_)
    |>.mono (by simp)
  · have hlt : 2 * u < t := by
      have := h; simp only [decide_eq_true_eq] at this
      unfold Lib.ordOf at this; split_ifs at this with h1 <;> first | omega | simp at this
    refine (HT.seq (HT.tmvInt_spec hI x42 x43 (by decide) S c0 (intSyms c1) (termOK_intSyms c1 [] |>
      fun h => by simpa using h) h42 ρ)
      (HT.tmvInt_spec hI x42 x44 (by decide) _ c1 [] TermOK.nil
        (by simp (disch := decide) only [Function.update_self, List.append_nil]) ρ)).of_eq ?_ hc
    rw [if_pos hlt, if_pos hlt]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false }) (disch := decide)
      only [ValEq.eq_1, Function.update_self, Function.update_of_ne, h43, h44]) only [tupd_swap,
      Function.update_idem, tupd_eq_self_of, Function.update_self, Function.update_of_ne, h43, h44,
      List.append_nil]
  · have hlt : ¬ 2 * u < t := by
      intro hc'
      have : Lib.ordOf (u + u) t = .lt := by unfold Lib.ordOf; rw [if_pos (by omega)]
      rw [this] at h; simp at h
    refine (HT.seq (HT.tmvInt_spec hI x42 x44 (by decide) S c0 (intSyms c1) (termOK_intSyms c1 [] |>
      fun h => by simpa using h) h42 ρ)
      (HT.tmvInt_spec hI x42 x43 (by decide) _ c1 [] TermOK.nil
        (by simp (disch := decide) only [Function.update_self, List.append_nil]) ρ)).of_eq ?_
      (by nlinarith)
    rw [if_neg hlt, if_neg hlt]
    simp (disch := first | decide | simp (config := { failIfUnchanged := false }) (disch := decide)
      only [ValEq.eq_1, Function.update_self, Function.update_of_ne, h43, h44]) only [tupd_swap,
      Function.update_idem, tupd_eq_self_of, Function.update_self, Function.update_of_ne, h43, h44,
      List.append_nil]

end Orient

end SubNLogN.Machine.Tables
