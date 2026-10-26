import WP.W7k3t.Else
import WP.W7k3t.DenY

/-!
# WP.W7k3t.Top — the tap kernel program

Host `Loc 8 16` (the contract's: named `0..4` = `p_work, pSub, t1, j1, s`, `5` = `πZ`, `6` = `lnZ`,
`7` = dst; 16 scratch stacks). `dst += tapV p_work pSub t1 j1 s πN lnN` (`= tapC …`, `Decomp`):

| scratch | value |
|---|---|
| 0 | `numT` (`NUMT`), then signed |
| 1 | `numTheta = πN·numT` (`mul`, sign popped) |
| 2 | `numY = numTheta²` (`NSQ`) |
| 3 | `denY` (`DENY`) |
| 4 | `B + 2 = pSub + 4` (`AFF 1 4`) |
| 5 | `(B+2)·denY` (`NMUL`) |

then `cmpNat` against `numY`: `≤` pushes `intSyms 0`, else the branch `ELSE` (`telse`); cleanup.
-/

-- The uniform operand-read / normalisation simp sets are used verbatim at every step; single steps
-- may need only part of them.
set_option linter.unusedSimpArgs false

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

instance : Big 8 16 := ⟨by decide⟩

theorem intSyms_zero_tap : intSyms 0 = [Sym.pos] := by
  simp [intSyms, sgnSym, natSyms, encodeNat_zero]

/-- Operand widths of the setup phase (both branches). -/
structure TopW (W p_work pSub t1 j1 s πN lnN : ℕ) : Prop where
  hW : 43 * pSub + 61 ≤ W
  hpw : bitLen p_work ≤ W
  ht : bitLen t1 ≤ W
  hj : bitLen j1 ≤ W
  hs : bitLen s ≤ W
  hd : bitLen (((s : ℤ) - (pSub : ℤ)) * (t1 : ℤ)).natAbs ≤ W
  hnt : bitLen (numTV pSub t1 j1 s) ≤ W
  hpi : bitLen πN ≤ W
  hth : bitLen (πN * numTV pSub t1 j1 s) ≤ W
  hny : bitLen (πN * numTV pSub t1 j1 s * (πN * numTV pSub t1 j1 s)) ≤ W
  h4p : bitLen (4 * p_work) ≤ W
  hln : bitLen lnN ≤ W
  h4pl : bitLen (4 * p_work * lnN) ≤ W
  htt : bitLen (t1 * t1) ≤ W
  h4plt : bitLen (4 * p_work * lnN * (t1 * t1)) ≤ W
  hdy : bitLen (denYV p_work pSub t1 lnN) ≤ W
  hth4 : bitLen ((pSub + 4) * denYV p_work pSub t1 lnN) ≤ W

/-- The test and the two branches. -/
def topBranch (I : TI) : Prog (Loc 8 16) (fun _ => Sym) I.R :=
  (tcm I (.inr 5) (.inr 2)).seq (.ite (fun v => decide (I.cm.obs (I.lcm.get v) ≠ .gt))
    (pushS (.inl 7) .pos) (telse I (.inl 1) (.inl 2) (.inr 2) (.inr 3) (.inl 7)))

theorem topBranch_closed (I : TI) : (topBranch I).Closed :=
  ⟨callI_closed _ _ _ _, trivial, telse_closed _ _ _ _ _ _⟩

theorem topBranch_spec {I : TI} {U : ℕ} (hI : I.Ok U) (B : Loc 8 16 → List Sym)
    (pSub t1 NY DY TH : ℕ) (r1 r2 rN rD rT : List Sym) (h1 : TermOK r1) (h2 : TermOK r2)
    (hrN : TermOK rN) (hrD : TermOK rD) (hrT : TermOK rT) (e1 : B (.inl 1) = natSyms pSub ++ r1)
    (e2 : B (.inl 2) = natSyms t1 ++ r2) (eN : B (.inr 2) = natSyms NY ++ rN)
    (eD : B (.inr 3) = natSyms DY ++ rD) (eT : B (.inr 5) = natSyms TH ++ rT) {W : ℕ}
    (hT : bitLen TH ≤ W) (hN : bitLen NY ≤ W) (he : ¬ TH ≤ NY → ElseW W pSub t1 NY DY) :
    HT [] B (topBranch I)
      (Function.update B (.inl 7)
        (intSyms (if TH ≤ NY then 0 else elseV pSub t1 NY DY) ++ B (.inl 7)))
      (2 * ((17 * pSub + 23) * (160 * uc U W)) + 803 * uc U W) := by
  have h1u : 1 ≤ uc U W := uc_one hI.one
  refine (tcm_ite_ht hI (.inr 5) (.inr 2) (by decide) B _ TH NY rT rN hrT hrN eT eN hT hN
    (fun o => decide (o ≠ .gt)) _ _ [] (T₁ := uc U W)
    (T₂ := 2 * ((17 * pSub + 23) * (160 * uc U W)) + 800 * uc U W) (fun h => ?_)
    (fun h => ?_)).mono ?_
  · have hle : TH ≤ NY := (ordOf_ne_gt_iff _ _).mp (of_decide_eq_true h)
    refine (push_ht hI (.inl 7) .pos B (W := W) []).of_eq ?_ le_rfl
    rw [if_pos hle, intSyms_zero_tap]
    rfl
  · have hgt : ¬ TH ≤ NY := fun hle =>
      absurd ((ordOf_ne_gt_iff _ _).mpr hle) (of_decide_eq_false h)
    refine (telse_ht hI (.inl 1) (.inl 2) (.inr 2) (.inr 3) (.inl 7) (by decide) B pSub t1 NY DY
      r1 r2 rN rD h1 h2 hrN hrD e1 e2 eN eD (he hgt) []).of_eq ?_ le_rfl
    rw [if_neg hgt]
  · have hm : max (uc U W) (2 * ((17 * pSub + 23) * (160 * uc U W)) + 800 * uc U W) =
        2 * ((17 * pSub + 23) * (160 * uc U W)) + 800 * uc U W := max_eq_right (by omega)
    rw [hm]
    omega

/-- **The tap kernel program.** -/
def topProg (I : TI) : Prog (Loc 8 16) (fun _ => Sym) I.R :=
  (pushS (.inr 0) .mark).seq <| (tnumt I (.inl 1) (.inl 2) (.inl 3) (.inl 4) (.inr 0)).seq <|
  (pushS (.inr 0) .pos).seq <|
  (pushS (.inr 1) .mark).seq <| (tmu I (.inl 5) (.inr 0) (.inr 1)).seq <| (popS (.inr 1)).seq <|
  (pushS (.inr 2) .mark).seq <| (tnsq I (.inr 1) (.inr 2)).seq <|
  (pushS (.inr 3) .mark).seq <| (tdeny I (.inl 0) (.inl 1) (.inl 2) (.inl 6) (.inr 3)).seq <|
  (pushS (.inr 4) .mark).seq <| (taff I 1 4 (.inl 1) (.inr 4)).seq <|
  (pushS (.inr 5) .mark).seq <| (tnmul I (.inr 4) (.inr 3) (.inr 5)).seq <|
  (topBranch I).seq <|
  (tdr I (.inr 5)).seq <| (popS (.inr 5)).seq <|
  (tdr I (.inr 4)).seq <| (popS (.inr 4)).seq <|
  (tdr I (.inr 3)).seq <| (popS (.inr 3)).seq <|
  (tdr I (.inr 2)).seq <| (popS (.inr 2)).seq <|
  (tdr I (.inr 1)).seq <| (popS (.inr 1)).seq <|
  (popS (.inr 0)).seq <| (tdr I (.inr 0)).seq <| popS (.inr 0)

theorem tnumt_closed' (I : TI) (p t j s z : Loc 8 16) : (tnumt I p t j s z).Closed :=
  tsub_closed _ _ _ _

theorem tdeny_closed' (I : TI) (pw ps t ln z : Loc 8 16) : (tdeny I pw ps t ln z).Closed :=
  tsub_closed _ _ _ _

theorem topProg_closed (I : TI) : (topProg I).Closed :=
  ⟨trivial, tnumt_closed' _ _ _ _ _ _, trivial, trivial, callI_closed _ _ _ _, trivial, trivial,
    tnsq_closed _ _ _, trivial, tdeny_closed' _ _ _ _ _ _, trivial, taff_closed _ _ _ _ _, trivial,
    tnmul_closed _ _ _ _, topBranch_closed _, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _,
    trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _,
    trivial, trivial, callI_closed _ _ _ _, trivial⟩

#assert_std_axioms intSyms_zero_tap topBranch_closed topBranch_spec tnumt_closed' tdeny_closed' topProg_closed

end WP.W7k3t
