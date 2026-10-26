/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.SolBlock
import SubNLogN.Machine.Tables.Frag

/-!
# K6 (`Machine/Tables/SolAxis.lean`): the closure precision on the machine

**Scope (honest summary).** The fragment `qProg` computing
`Q = closurePrec q A t = q + lg A + 2·lg(4t) + 10` (`SubNLogN/Math/Bridge/Components.lean`,
Lemma 4.6 (`lem:bridge-C`)(v) and Theorem 4.7 (`thm:bridge-precision`)) from `q`, `A ≥ 2`, `t ≥ 1` (via `lg n = bitLen (n-1)` for `n ≥ 2`),
with exact final state and the cost bound `qCost C W` for any `W` bounding the inputs.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt SubNLogN.Math.Common

section Defs

variable (I : TB)

/-- `rQ := closurePrec q A t` (`q` on `rq`, `A` on `rA`, `t` on `rT`; temporaries
`x40 … x47`). -/
def qProg : TP I :=
  (clogProg I rA x41 x40).seq ((tcp I rT x42).seq ((tnat I x43 2).seq ((tsv I x42 x43).seq
    ((tdr I x43).seq ((clogProg I x42 x45 x44).seq ((tdr I x42).seq
    ((tad I rq x40 x46).seq ((tad I x46 x44 x47).seq ((tad I x47 x44 x45).seq
    ((tnat I x43 10).seq ((tad I x45 x43 rQ).seq ((tdr I x43).seq ((tdr I x45).seq
    ((tdr I x47).seq ((tdr I x46).seq ((tdr I x44).seq (tdr I x40)))))))))))))))))

theorem qProg_closed : (qProg I).Closed :=
  ⟨clogProg_closed I _ _ _, callI_closed _ _ _ _, pushBits_closed _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, clogProg_closed I _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    pushBits_closed _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

end Defs

/-- Cost bound of `qProg` at input width `W`. -/
def qCost (C W : ℕ) : ℕ := 2 * (W * (C * (W + 1) + 3)) + 40 * (C * (5 * W)) + 40 * C + 40

section Specs

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

set_option maxHeartbeats 1000000 in
theorem HT.qProg_spec (hI : I.Spec Mul C) (B : TL → List Sym) (q A t W : ℕ)
    (hA2 : 2 ≤ A) (ht1 : 1 ≤ t) (hqW : q ≤ W) (hAW : bitLen A ≤ W) (htW : bitLen t + 3 ≤ W)
    (hq : B rq = natSyms q) (hA : B rA = natSyms A) (hT : B rT = natSyms t) (hQ0 : B rQ = [])
    (h40 : B x40 = []) (h41 : B x41 = []) (h42 : B x42 = []) (h43 : B x43 = [])
    (h44 : B x44 = []) (h45 : B x45 = []) (h46 : B x46 = []) (h47 : B x47 = [])
    (ρ : List (TP I)) :
    HT ρ B (qProg I) (Function.update B rQ (natSyms (closurePrec q A t))) (qCost C W) := by
  have hQv : q + bitLen (A - 1) + bitLen (t * 2 ^ 2 - 1) + bitLen (t * 2 ^ 2 - 1) + 10 =
      closurePrec q A t := by
    unfold closurePrec
    rw [lg_eq_bitLen hA2, lg_eq_bitLen (by omega : 2 ≤ 4 * t), show t * 2 ^ 2 = 4 * t by ring]
    ring
  refine (HT.seq (HT.clogProg_spec hI rA x41 x40 (by decide) (by decide) (by decide) B A []
      TermOK.nil (by omega) (by rw [hA, List.append_nil]) h41 h40 ρ)
    (HT.seq (HT.tcp_spec hI rT x42 (by decide) _ t [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hT, List.append_nil]) ρ)
    (HT.seq (HT.tnat_spec x43 2 _ ρ)
    (HT.seq (HT.tsv_spec hI x42 x43 (by decide) _ t 2 [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h42])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h43]) ρ)
    (HT.seq (HT.tdr_spec hI x43 _ 2 [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h43]) ρ)
    (HT.seq (HT.clogProg_spec hI x42 x45 x44 (by decide) (by decide) (by decide) _ (t * 2 ^ 2) []
      TermOK.nil (Nat.mul_pos (by omega) (by positivity))
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [Function.update_of_ne, h45])
      (by simp (disch := decide) only [Function.update_of_ne, h44]) ρ)
    (HT.seq (HT.tdr_spec hI x42 _ (t * 2 ^ 2) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self]) ρ)
    (HT.seq (HT.tad_spec hI rq x40 x46 (by decide) _ q (bitLen (A - 1)) [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hq, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ)
    (HT.seq (HT.tad_spec hI x46 x44 x47 (by decide) _ (q + bitLen (A - 1))
      (bitLen (t * 2 ^ 2 - 1)) [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h46])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ)
    (HT.seq (HT.tad_spec hI x47 x44 x45 (by decide) _ (q + bitLen (A - 1) + bitLen (t * 2 ^ 2 - 1))
      (bitLen (t * 2 ^ 2 - 1)) [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h47])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ)
    (HT.seq (HT.tnat_spec x43 10 _ ρ)
    (HT.seq (HT.tad_spec hI x45 x43 rQ (by decide) _
      (q + bitLen (A - 1) + bitLen (t * 2 ^ 2 - 1) + bitLen (t * 2 ^ 2 - 1)) 10 [] []
      TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h45])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h43]) ρ)
    (HT.seq (HT.tdr_spec hI x43 _ 10 [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h43]) ρ)
    (HT.seq (HT.tdr_spec hI x45 _
      (q + bitLen (A - 1) + bitLen (t * 2 ^ 2 - 1) + bitLen (t * 2 ^ 2 - 1)) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h45]) ρ)
    (HT.seq (HT.tdr_spec hI x47 _ (q + bitLen (A - 1) + bitLen (t * 2 ^ 2 - 1)) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h47]) ρ)
    (HT.seq (HT.tdr_spec hI x46 _ (q + bitLen (A - 1)) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h46]) ρ)
    (HT.seq (HT.tdr_spec hI x44 _ (bitLen (t * 2 ^ 2 - 1)) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ)
    (HT.tdr_spec hI x40 _ (bitLen (A - 1)) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ)))))))))))))))))).of_eq ?_ ?_
  · funext g
    by_cases g0 : g = rQ
    · subst g0
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, hQ0,
        List.append_nil]
      rw [hQv]
    by_cases g1 : g = x40
    · subst g1; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h40]
    by_cases g2 : g = x41
    · subst g2; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h41]
    by_cases g3 : g = x42
    · subst g3; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h42]
    by_cases g4 : g = x43
    · subst g4; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h43]
    by_cases g5 : g = x44
    · subst g5; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h44]
    by_cases g6 : g = x45
    · subst g6; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h45]
    by_cases g7 : g = x46
    · subst g7; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h46]
    by_cases g8 : g = x47
    · subst g8; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h47]
    simp only [Function.update_of_ne g0, Function.update_of_ne g1, Function.update_of_ne g2,
      Function.update_of_ne g3, Function.update_of_ne g4, Function.update_of_ne g5,
      Function.update_of_ne g6, Function.update_of_ne g7, Function.update_of_ne g8]
  · have vA : bitLen (A - 1) ≤ W := le_trans (bitLen_mono (Nat.sub_le A 1)) hAW
    have v4 : bitLen (t * 2 ^ 2) ≤ W := by
      have := bitLen_mul_le t (2 ^ 2)
      have h4 : bitLen (2 ^ 2) = 2 + 1 := bitLen_two_pow 2
      omega
    have v4' : bitLen (t * 2 ^ 2 - 1) ≤ W := le_trans (bitLen_mono (Nat.sub_le _ 1)) v4
    have vS1 : bitLen (q + bitLen (A - 1)) ≤ 5 * W := le_trans (bitLen_le_self _) (by omega)
    have vS2 : bitLen (q + bitLen (A - 1) + bitLen (t * 2 ^ 2 - 1)) ≤ 5 * W :=
      le_trans (bitLen_le_self _) (by omega)
    have vS3 : bitLen (q + bitLen (A - 1) + bitLen (t * 2 ^ 2 - 1) +
        bitLen (t * 2 ^ 2 - 1)) ≤ 5 * W := le_trans (bitLen_le_self _) (by omega)
    have v2 : bitLen 2 ≤ 2 := bitLen_le_self 2
    have v10 : bitLen 10 ≤ 10 := bitLen_le_self 10
    have vq : bitLen q ≤ W := le_trans (bitLen_le_self q) hqW
    have vbA : bitLen (bitLen (A - 1)) ≤ W := le_trans (bitLen_le_self _) vA
    have vb4 : bitLen (bitLen (t * 2 ^ 2 - 1)) ≤ W := le_trans (bitLen_le_self _) v4'
    have pA : bitLen (A - 1) * (C * (bitLen (A - 1) + 1) + 3) ≤ W * (C * (W + 1) + 3) :=
      Nat.mul_le_mul vA (Nat.add_le_add_right (Nat.mul_le_mul_left C (Nat.add_le_add_right vA 1)) 3)
    have p4 : bitLen (t * 2 ^ 2 - 1) * (C * (bitLen (t * 2 ^ 2 - 1) + 1) + 3) ≤
        W * (C * (W + 1) + 3) :=
      Nat.mul_le_mul v4' (Nat.add_le_add_right (Nat.mul_le_mul_left C
        (Nat.add_le_add_right v4' 1)) 3)
    have cA := Nat.mul_le_mul_left C (show bitLen A ≤ 5 * W by omega)
    have ct := Nat.mul_le_mul_left C (show bitLen t ≤ 5 * W by omega)
    have c4 := Nat.mul_le_mul_left C (show bitLen (t * 2 ^ 2) ≤ 5 * W by omega)
    have cq := Nat.mul_le_mul_left C (show bitLen q ≤ 5 * W by omega)
    have cbA := Nat.mul_le_mul_left C (show bitLen (bitLen (A - 1)) ≤ 5 * W by omega)
    have cb4 := Nat.mul_le_mul_left C (show bitLen (bitLen (t * 2 ^ 2 - 1)) ≤ 5 * W by omega)
    have cS1 := Nat.mul_le_mul_left C vS1
    have cS2 := Nat.mul_le_mul_left C vS2
    have cS3 := Nat.mul_le_mul_left C vS3
    have c2 := Nat.mul_le_mul_left C (show bitLen 2 ≤ 5 * W by omega)
    have c10 := Nat.mul_le_mul_left C (show bitLen 10 ≤ 5 * W by omega)
    have c2' := Nat.mul_le_mul_left C (show 2 ≤ 5 * W by omega)
    unfold qCost
    linarith [Nat.zero_le (C * W)]

end Specs

end SubNLogN.Machine.Tables
