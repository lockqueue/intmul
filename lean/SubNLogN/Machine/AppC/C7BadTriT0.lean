/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7BadTriLine

/-!
# Lemma A.9 extraction: `T₀` on the machine (`Machine/AppC/C7BadTriT0.lean`)

The ideal selected-bit XOR `T₀` of the bad-record triple transform (`c7BadTri`, `C7BadTri.lean`)
as one addition and one subtraction of line sums (`packedT0_eq`, `xor_mask_eq`,
`C7ExtractMath.lean`): `y := y + lsum K ρ x y false N - lsum K ρ x y true N`. Both line sums
(`btLsum_runs`, `C7BadTriLine.lean`) read a copy `YC` of `y`, so `y` may be updated in between.
Used by `btTri` (`C7BadTriMain.lean`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine.AppC.C7BadTriAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine.AppC.C7ExtractAux SubNLogN.Machine.Calculus

section Progs

variable (xk : XKit BTLoc)

/-- `T₀`: `y := y + lsum x y false - lsum x y true`; both line sums read a copy `YC` of `y`. -/
def btT0 : Prog BTLoc (fun _ => Sym) xk.R :=
  .seq (btInitCopy xk bY bYC bCT)
  (.seq (btLsum xk bYC false)
  (.seq (addTo xk bY bOFF bT0 bT1 bT2 bT3)
  (.seq (dropFW xk bOFF)
  (.seq (btLsum xk bYC true)
  (.seq (subFrom xk bY bOFF bT0 bT1 bT2 bT3)
  (.seq (dropFW xk bOFF) (dropFW xk bYC)))))))

theorem closed_btT0 : (btT0 xk).Closed :=
  ⟨closed_btInitCopy xk _ _ _, closed_btLsum xk _ _, closed_addTo xk _ _ _ _ _ _,
    closed_dropFW xk _, closed_btLsum xk _ _, closed_subFrom xk _ _ _ _ _ _, closed_dropFW xk _,
    closed_dropFW xk _⟩

end Progs

/-- **`T₀` on the machine**: `y := y + lsum K ρ x y false N - lsum K ρ x y true N`. -/
theorem btT0_runs (xk : XKit BTLoc) (K ρ N L x y : ℕ) (rx ry r3 r4 r6 : List Sym)
    (S : BTLoc → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hr3 : TermOK r3)
    (hr4 : TermOK r4) (hr6 : TermOK r6)
    (hSx : S bX = natSyms x ++ rx) (hSy : S bY = natSyms y ++ ry)
    (hS3 : S bPK = natSyms (2 ^ K) ++ r3) (hS4 : S bPr = natSyms (2 ^ ρ) ++ r4)
    (hS6 : S bF1 = natSyms N ++ r6) (hK : 1 ≤ K) (hNL : ρ + N * K < L) (hx : x < 2 ^ L)
    (hy : y < 2 ^ L) :
    Runs (btT0 xk) S
      (Function.update S bY (natSyms (y + lsum K ρ x y false N - lsum K ρ x y true N) ++ ry))
      (fun _ => True) (30 * opCost xk (L + 1) * (N + 1)) := by
  have hW := btOpCost_ge xk (L + 1)
  have hNK : N ≤ N * K := Nat.le_mul_of_pos_right N hK
  have hLp : L < 2 ^ L := Nat.lt_two_pow_self
  have hL1 : 2 ^ (L + 1) = 2 ^ L + 2 ^ L := by rw [pow_succ]; ring
  have hpow : 2 ^ (ρ + N * K) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hNL.le
  have hA := lsum_lt K ρ x y false hK N
  have hB := lsum_lt K ρ x y true hK N
  have hle := (xor_mask_eq K ρ x y hK N).2
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq
    (runs_btInitCopy xk (src := bY) (k := bYC) (tmp := bCT) (by decide) (by decide) (by decide)
      y (L + 1) ry (S bYC) S hry hSy rfl (btBitLen_le (by omega)))
    (WP.W9comp.runs_seq
    (btLsum_runs xk bYC (by decide) (by decide) (by decide) false K ρ N (L + 1) x y rx
      (Sym.mark :: S bYC) r3 r4 r6 _ hrx (termOK_mark _) hr3 hr4 hr6
      (by simp +decide [hSx]) (by simp)
      (by simp +decide [hS3])
      (by simp +decide [hS4])
      (by simp +decide [hS6]) hK (by omega) (by omega) (by omega)
      (by omega))
    (WP.W9comp.runs_seq
    (runs_addTo xk (k := bY) (b := bOFF) (t := bT0) (t1 := bT1) (t2 := bT2) (t3 := bT3)
      (by decide) y (lsum K ρ x y false N) (L + 1) ry (Sym.mark :: S bOFF) _ hry (termOK_mark _)
      (by simp +decide [hSy]) (by simp +decide)
      (btBitLen_le (by omega)) (btBitLen_le (by omega)) (btBitLen_le (by omega)))
    (WP.W9comp.runs_seq
    (runs_dropFW xk bOFF (lsum K ρ x y false N) Sym.mark (S bOFF) _ rfl
      (by simp +decide))
    (WP.W9comp.runs_seq
    (btLsum_runs xk bYC (by decide) (by decide) (by decide) true K ρ N (L + 1) x y rx
      (Sym.mark :: S bYC) r3 r4 r6 _ hrx (termOK_mark _) hr3 hr4 hr6
      (by simp +decide [hSx]) (by simp +decide)
      (by simp +decide [hS3])
      (by simp +decide [hS4])
      (by simp +decide [hS6]) hK (by omega) (by omega) (by omega)
      (by omega))
    (WP.W9comp.runs_seq
    (runs_subFrom xk (k := bY) (b := bOFF) (t := bT0) (t1 := bT1) (t2 := bT2) (t3 := bT3)
      (by decide) (y + lsum K ρ x y false N) (lsum K ρ x y true N) (L + 1) ry
      (Sym.mark :: S bOFF) _ hry (termOK_mark _) hle
      (by simp +decide) (by simp +decide)
      (btBitLen_le (by omega)) (btBitLen_le (by omega)))
    (WP.W9comp.runs_seq
    (runs_dropFW xk bOFF (lsum K ρ x y true N) Sym.mark (S bOFF) _ rfl
      (by simp +decide))
    (runs_dropFW xk bYC y Sym.mark (S bYC) _ rfl
      (by simp +decide))))))))) ?_) (fun _ _ => trivial) ?_
  · funext k
    rcases k with j | j <;> fin_cases j <;> simp +decide
  · have e6 : 12 * opCost xk (L + 1) * (N + 1) = 12 * (opCost xk (L + 1) * (N + 1)) := by ring
    have e5 : 30 * opCost xk (L + 1) * (N + 1) = 30 * (opCost xk (L + 1) * (N + 1)) := by ring
    have e7 : opCost xk (L + 1) ≤ opCost xk (L + 1) * (N + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have e8 := btBitLen_le (show lsum K ρ x y false N < 2 ^ L by omega)
    have e9 := btBitLen_le (show lsum K ρ x y true N < 2 ^ L by omega)
    have e10 := btBitLen_le hy
    omega

end SubNLogN.Machine.AppC.C7BadTriAux
