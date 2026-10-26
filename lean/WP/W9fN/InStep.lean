import WP.W9fN.Lay8
import WP.W9fN.StepCost
import WP.W9fN.FinishSpec
import WP.W9fW.Builders

/-!
# WP.W9fN.InStep — one iteration of the Nyquist core's zPart loop

Host state after `n` steps (`Xn`, `SInv`): `IN` holds the unread inputs `Y[n+1..]`, `ZS` holds the
zPart array `Z_n = W8.zPartNyqBarrett q H μ a Ys n` (last entry on top, above a `mark`), the
variables satisfy `Prm` (divisor = multiplier = `a`), `Z = Z_n[n]`, and the step's input widths
`βstep H`. The body pops `Y[n+1]` into `Y1, Y2`, runs the compiled `pStepP` (one reciprocal step),
and pushes the new `Z` onto `ZS` (`inBody_step`, cost `bodyCost C Mul H`).
-/

namespace WP.W9fN

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fN.IL IntMul IntMulTM.Contracts

/-! ## Arrays and blocks -/

theorem blkE_cons' (y : ℤ × ℤ) (ys : List (ℤ × ℤ)) : blkE (y :: ys) = entrySyms y ++ blkE ys := by
  simp [blkE, blk]

theorem drop_read1D (Ys : Array (ℤ × ℤ)) (n : ℕ) (h : n < Ys.size) :
    Ys.toList.drop n = read1D Ys n :: Ys.toList.drop (n + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  congr 1
  simp [read1D, h]

theorem read1D_mem (Ys : Array (ℤ × ℤ)) (n : ℕ) (h : n < Ys.size) : read1D Ys n ∈ Ys.toList := by
  simp [read1D, h]

theorem read1D_push_size (arr : Array (ℤ × ℤ)) (x : ℤ × ℤ) : read1D (arr.push x) arr.size = x := by
  simp [read1D]

theorem zp_succ (q H : ℕ) (μ a : ℤ) (Ys : Array (ℤ × ℤ)) (n : ℕ) :
    W8.zPartNyqBarrett q H μ a Ys (n + 1) = (W8.zPartNyqBarrett q H μ a Ys n).push
      (W8.recStepBarrett q H μ a a (read1D Ys (n + 1)) (read1D (W8.zPartNyqBarrett q H μ a Ys n) n)) :=
  rfl

theorem zp_last (q H : ℕ) (μ a : ℤ) (Ys : Array (ℤ × ℤ)) (n : ℕ) :
    read1D (W8.zPartNyqBarrett q H μ a Ys (n + 1)) (n + 1) =
      W8.recStepBarrett q H μ a a (read1D Ys (n + 1)) (read1D (W8.zPartNyqBarrett q H μ a Ys n) n) := by
  have hs := WP.W9f.zPartNyqBarrett_size q H μ a Ys n
  have key : ∀ (arr : Array (ℤ × ℤ)) (x : ℤ × ℤ) (m : ℕ), arr.size = m → read1D (arr.push x) m = x := by
    intro arr x m h
    subst h
    exact read1D_push_size arr x
  rw [zp_succ]
  exact key _ _ _ hs

theorem zp_rev_succ (q H : ℕ) (μ a : ℤ) (Ys : Array (ℤ × ℤ)) (n : ℕ) :
    (W8.zPartNyqBarrett q H μ a Ys (n + 1)).toList.reverse =
      W8.recStepBarrett q H μ a a (read1D Ys (n + 1)) (read1D (W8.zPartNyqBarrett q H μ a Ys n) n) ::
        (W8.zPartNyqBarrett q H μ a Ys n).toList.reverse := by
  rw [zp_succ, Array.toList_push, List.reverse_append]
  rfl

/-! ## The loop state -/

/-- Invariant on the variables after `n` steps. -/
structure SInv (q H : ℕ) (μ a : ℤ) (Ys : Array (ℤ × ℤ)) (n : ℕ) (env : V → ℤ) : Prop where
  prm : Prm env q H μ a a
  z : (env .Z1, env .Z2) = read1D (W8.zPartNyqBarrett q H μ a Ys n) n
  w : ∀ v, bitLen (env v).natAbs ≤ βstep H v

/-- Non-variable stacks after `n` steps (`Zn` = the zPart array after `n` steps). -/
def Xn (S : HK → List Sym) (Ys : Array (ℤ × ℤ)) (rIn : List Sym) (Zn : Array (ℤ × ℤ)) (n : ℕ) :
    HK → List Sym :=
  Function.update (Function.update S kIN (blkE (Ys.toList.drop (n + 1)) ++ rIn)) kZS
    (blkE Zn.toList.reverse ++ Sym.mark :: S kZS)

/-- The compiled reciprocal step on the host. -/
def stepC (I : Op → OpImpl) : Prog HK (fun _ => Sym) (GReg I) := (pStepP.compile I).mapStk LN.emb

/-- Loop body: pop `Y[n+1]`, one zPart step, push the new `Z` onto `ZS`. -/
def inBody (I : Op → OpImpl) : Prog HK (fun _ => Sym) (GReg I) :=
  .seq (hM I (popEntry kIN (vL .Y1) (vL .Y2) kTMP))
    (.seq (stepC I) (hM I (pushEntry (vL .Z1) (vL .Z2) kZS kTMP)))

/-- Cost bound of one iteration. -/
def bodyCost (C : ℕ) (Mul : ℕ → ℕ) (H : ℕ) : ℕ :=
  (22 * H + 46) + (10 * (C * Mul (WP.W9f.solW H) + C + 20 * WP.W9f.solW H + 43) +
    24 * (C * (2 * WP.W9f.solW H + 1) + 20 * WP.W9f.solW H + 43)) + (14 * H + 40)

theorem kIN_ne_kZS : kIN ≠ kZS := by simp [kIN, kZS]
theorem kIN_ne_kTMP : kIN ≠ kTMP := by simp [kIN, kTMP]
theorem kZS_ne_kTMP : kZS ≠ kTMP := by
  simp only [kZS, kTMP, ne_eq, Sum.inr.injEq]
  decide

theorem bitLen_le_of_abs {x : ℤ} {H : ℕ} (h : |x| ≤ ((2 ^ H : ℕ) : ℤ)) : bitLen x.natAbs ≤ H + 1 :=
  WP.W9fW.bitLen_natAbs_le_succ h

#assert_std_axioms blkE_cons' drop_read1D read1D_mem read1D_push_size zp_succ zp_last zp_rev_succ
  kIN_ne_kZS kIN_ne_kTMP kZS_ne_kTMP bitLen_le_of_abs

end WP.W9fN
