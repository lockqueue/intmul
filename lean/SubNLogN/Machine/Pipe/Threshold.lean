/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.Dispatch
import IntMulTM.Framework.Lib.CompareEval

/-!
# K7 (`Machine/Pipe/Threshold.lean`): the cutoff test kernel

The pipeline's guard is a cutoff `c ≤ K0` on the second field `K0` of the root header
`C0 = hdrSyms [b, K0, k1, k2] ++ r0`. This file builds a closed program on `BLoc 4` that keeps every
stack and leaves `decide (c ≤ K0)` in a register, for any constant `c`, and proves it (0 `sorry`):
* `pushList k l` pushes the symbols of `l` (so that `l` lies on top, in order); `runs_pushList`;
* `thresholdProg c`: guard `X`; move `b` from `C0` to `X` (`rewindTo`); push `natSyms c` (guarded)
  on `T`; compare `K0` with `c` (`Lib.cmpNum`); drop `c`; push the mark back on `C0` and move `b`
  back (`rewindTo`);
* `ThresholdTestStmt` and `thresholdTest_holds`; `walshTest_of_threshold` instantiates
  `WalshTestStmt` (`Dispatch.lean`) for the guard `fun _ K0 => decide (c ≤ K0)`.
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN SubNLogN.S5 Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMulTM
  IntMulTM.Contracts

/-! ## Pushing a list of symbols -/

/-- Push the symbols of `l` onto `k`, deepest first, so that `l` ends up on top in order. -/
def pushList {K : Type} (k : K) : List Sym → SProg K
  | [] => skip
  | s :: l => .seq (pushList k l) (pushC k s)

theorem closed_pushList {K : Type} (k : K) : ∀ l : List Sym, (pushList k l).Closed
  | [] => by simp [Prog.Closed, pushList, skip, Prog.FreeBelow]
  | s :: l => ⟨closed_pushList k l, by simp [pushC, Prog.FreeBelow]⟩

theorem runs_pushList {K : Type} [DecidableEq K] (k : K) :
    ∀ (l : List Sym) (S : K → List Sym),
      Runs (pushList k l) S (Function.update S k (l ++ S k)) (fun _ => True) (l.length + 1)
  | [], S => by
    refine Runs.of_eval fun v => ⟨v, 1, (Eval.load (Γ := fun _ => Sym) [] id v S).of_eq ?_ rfl,
      trivial, le_refl _⟩
    simp
  | s :: l, S => by
    have h := WP.W9comp.runs_seq (runs_pushList k l S)
      (WP.W9mp.runs_pushC k s (Function.update S k (l ++ S k)))
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h ?_) (fun _ _ => trivial) ?_
    · rw [Function.update_self, Function.update_idem]
      rfl
    · simp

/-! ## The program -/

/-- Scratch stacks of the cutoff test on `BLoc 4`. -/
def thX : BLoc 4 := .inr 0
/-- See `thX`. -/
def thT : BLoc 4 := .inr 1
/-- See `thX`. -/
def thU : BLoc 4 := .inr 2
/-- See `thX`. -/
def thV : BLoc 4 := .inr 3

/-- Head: guard `X`, move `b` from `C0` to `X`, push the guarded constant on `T`. -/
def thHead (c : ℕ) : SProg (BLoc 4) :=
  .seq (pushC thX .mark) <|
  .seq (WP.W9comp.rewindTo (.inl .C0) thX .mark) <|
  .seq (pushC thT .mark) (pushList thT (natSyms c))

/-- Tail: drop the constant, push the mark back on `C0`, move `b` back from `X`. -/
def thTail : SProg (BLoc 4) :=
  .seq (WP.W9mp.dropTo thT .mark) <|
  .seq (pushC (.inl .C0) .mark) (WP.W9comp.rewindTo thX (.inl .C0) .mark)

/-- **The cutoff test** for the constant `c`: compare `K0` (second field of `C0`) with `c`. -/
def thresholdProg (c : ℕ) : Prog (BLoc 4) (fun _ => Sym) CReg :=
  .seq ((thHead c).liftRegs L1) (.seq (cmpNum (.inl .C0) thT thU thV) (thTail.liftRegs L1))

/-- The flag: `cmpNum` left `ordOf K0 c`, and `c ≤ K0` iff it is not `.lt`. -/
def thFlag (v : CReg) : Bool := decide (v.2.2 ≠ Ordering.lt)

theorem closed_thresholdProg (c : ℕ) : (thresholdProg c).Closed := by
  have hh : (thHead c).Closed := ⟨by simp [pushC, Prog.FreeBelow],
    ⟨by simp [WP.W9comp.rewindTo, WP.W9comp.rewindBody, popR, pushR, Prog.FreeBelow],
      ⟨by simp [pushC, Prog.FreeBelow], closed_pushList _ _⟩⟩⟩
  have ht : thTail.Closed := ⟨WP.W9mp.closed_dropTo _ _, ⟨by simp [pushC, Prog.FreeBelow],
    by simp [WP.W9comp.rewindTo, WP.W9comp.rewindBody, popR, pushR, Prog.FreeBelow]⟩⟩
  refine ⟨WP.W9comp.closed_liftRegs _ hh, ⟨?_, WP.W9comp.closed_liftRegs _ ht⟩⟩
  simp [cmpNum, cmpBody, pushC, popR, pushR, restoreR, moveBits, moveBitsBody, skip,
    Prog.FreeBelow, WP.W9comp.freeBelow_liftRegs]

/-! ## Correctness -/

theorem ordOf_ne_lt_iff (a c : ℕ) : ordOf a c ≠ Ordering.lt ↔ c ≤ a := by
  unfold ordOf
  constructor
  · intro h
    by_contra hlt
    exact h (if_pos (by omega))
  · intro h
    rw [if_neg (by omega)]
    split_ifs <;> simp

theorem thresholdProg_runs (c b K0 k1 k2 : ℕ) (r0 : List Sym) (σ : BLoc 4 → List Sym)
    (hC0 : σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0) :
    Runs (thresholdProg c) σ σ (fun v => thFlag v = decide (c ≤ K0))
      (25 * (bitLen c + bitLen b + 1)) := by
  have dXC : (thX : BLoc 4) ≠ .inl .C0 := by decide
  have dTC : (thT : BLoc 4) ≠ .inl .C0 := by decide
  have dTX : (thT : BLoc 4) ≠ thX := by decide
  have dUC : (thU : BLoc 4) ≠ .inl .C0 := by decide
  have dVC : (thV : BLoc 4) ≠ .inl .C0 := by decide
  have dTU : (thT : BLoc 4) ≠ thU := by decide
  have dTV : (thT : BLoc 4) ≠ thV := by decide
  have dUV : (thU : BLoc 4) ≠ thV := by decide
  set ra : List Sym := Sym.mark :: (hdrSyms [k1, k2] ++ r0) with hra_def
  set restC : List Sym := natSyms K0 ++ ra with hrestC
  have hC0' : σ (.inl .C0) = natSyms b ++ Sym.mark :: restC := by
    rw [hC0]; simp [WP.W9mp.hdrSyms_cons, restC, ra]
  -- head
  set S1 := Function.update σ thX (Sym.mark :: σ thX) with hS1
  have h1 := WP.W9mp.runs_pushC thX Sym.mark σ
  have hS1C : S1 (.inl .C0) = natSyms b ++ Sym.mark :: restC := by
    rw [hS1, Function.update_of_ne dXC.symm]; exact hC0'
  set S2 := Function.update (Function.update S1 (.inl .C0) restC) thX
    ((natSyms b).reverse ++ S1 thX) with hS2
  have h2 := WP.W9mp.runs_rewindTo dXC.symm Sym.mark (natSyms b) restC S1
    (WP.W9mp.mark_not_mem_natSyms b) hS1C
  set S3 := Function.update S2 thT (Sym.mark :: S2 thT) with hS3
  have h3 := WP.W9mp.runs_pushC thT Sym.mark S2
  set S4 := Function.update S3 thT (natSyms c ++ S3 thT) with hS4
  have h4 := runs_pushList thT (natSyms c) S3
  have hHead := WP.W9comp.runs_seq h1 (WP.W9comp.runs_seq h2 (WP.W9comp.runs_seq h3 h4))
  -- facts about `S4`
  have h4C : S4 (.inl .C0) = natSyms K0 ++ ra := by
    simp [hS4, hS3, hS2, Function.update_of_ne dTC.symm, Function.update_of_ne dXC.symm, restC]
  have h4T : S4 thT = natSyms c ++ Sym.mark :: σ thT := by
    simp [hS4, hS3, hS2, hS1, Function.update_of_ne dTX, Function.update_of_ne dTC]
  have h4X : S4 thX = (natSyms b).reverse ++ Sym.mark :: σ thX := by
    simp [hS4, hS3, hS2, hS1, Function.update_of_ne dTX.symm]
  -- compare
  have hra : TermOK ra := WP.W9mp.termOK_mark _
  have hrb : TermOK (Sym.mark :: σ thT) := WP.W9mp.termOK_mark _
  have hC : Triple [] (fun s => s.stk = S4) (cmpNum (.inl .C0) thT thU thV)
      (fun s => s.stk = S4 ∧ s.var.2.2 = ordOf K0 c)
      (12 * min (encodeNat K0).length (encodeNat c).length + 15) := by
    rintro ⟨v, stk⟩ hs
    change stk = S4 at hs
    subst hs
    exact cmpNum_triple dTC.symm dUC.symm dVC.symm dTU dTV dUV v K0 c ra (Sym.mark :: σ thT) _ hra
      hrb h4C h4T _ rfl
  -- tail
  have hpop : S4 thT = hdrSyms [c] ++ σ thT := by rw [h4T]; simp [hdrSyms]
  set S6 := Function.update S4 thT (σ thT) with hS6
  have h6 := WP.W9mp.runs_popHdr thT c (σ thT) S4 hpop
  set S7 := Function.update S6 (.inl .C0) (Sym.mark :: S6 (.inl .C0)) with hS7
  have h7 := WP.W9mp.runs_pushC (.inl .C0) Sym.mark S6
  have h7X : S7 thX = (natSyms b).reverse ++ Sym.mark :: σ thX := by
    simp [hS7, hS6, Function.update_of_ne dXC, Function.update_of_ne dTX.symm, h4X]
  set S8 := Function.update (Function.update S7 thX (σ thX)) (.inl .C0)
    ((natSyms b).reverse.reverse ++ S7 (.inl .C0)) with hS8
  have h8 := WP.W9mp.runs_rewindTo dXC Sym.mark (natSyms b).reverse (σ thX) S7
    (by simpa using WP.W9mp.mark_not_mem_natSyms b) h7X
  have hTail := WP.W9comp.runs_seq h6 (WP.W9comp.runs_seq h7 h8)
  have hS8σ : S8 = σ := by
    funext k
    by_cases hk : k = .inl .C0
    · subst hk
      simp [hS8, hS7, hS6, Function.update_of_ne dTC.symm, h4C, hC0', restC]
    · by_cases hx : k = thX
      · subst hx
        simp [hS8, Function.update_of_ne dXC]
      · by_cases ht : k = thT
        · subst ht
          simp [hS8, hS7, hS6, Function.update_of_ne dTX, Function.update_of_ne dTC]
        · simp [hS8, hS7, hS6, hS4, hS3, hS2, hS1, Function.update_of_ne hk,
            Function.update_of_ne hx, Function.update_of_ne ht]
  -- assemble
  have hH := WP.W9mp.runs_liftRegs L1 hHead
  have hT := Triple.liftRegs L1 hTail (fun v : CReg => v.2.2 = ordOf K0 c) (fun _ _ hv => hv)
  have hec : (encodeNat c).length = bitLen c := by rw [← length_natSyms]; simp [natSyms]
  refine (Triple.seq (hH.post fun _ h => h.1) (Triple.seq hC hT)).conseq (fun _ h => h) ?_ ?_
  · rintro s ⟨⟨hs, -⟩, hv⟩
    refine ⟨hs.trans hS8σ, ?_⟩
    show decide (s.var.2.2 ≠ Ordering.lt) = decide (c ≤ K0)
    rw [hv]
    exact decide_eq_decide.2 (ordOf_ne_lt_iff K0 c)
  · have hmin : min (encodeNat K0).length (encodeNat c).length ≤ bitLen c :=
      (min_le_right _ _).trans hec.le
    simp only [List.length_reverse, length_natSyms]
    nlinarith [hmin]

/-! ## The statement -/

/-- **Cutoff test (`ThresholdTestStmt`).** There is a constant `C` such that for every constant `c`
there is a closed program on `BLoc mt` (`mt ≤ 64`) over a finite nonempty register type, with a
Boolean read-out `flag`, that for every `σ` with `C0 = hdrSyms [b, K0, k1, k2] ++ r0` keeps every
stack and sets `flag = decide (c ≤ K0)`, within `C · (bitLen c + bitLen b + 1)` steps. -/
def ThresholdTestStmt : Prop :=
  ∃ C : ℕ, ∀ c : ℕ, ∃ (mt : ℕ) (Rt : Type) (Pt : Prog (BLoc mt) (fun _ => Sym) Rt)
    (flag : Rt → Bool),
    mt ≤ 64 ∧ Finite Rt ∧ Nonempty Rt ∧ Pt.Closed ∧
    ∀ (b K0 k1 k2 : ℕ) (r0 : List Sym) (σ : BLoc mt → List Sym),
      σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 →
      Runs Pt σ σ (fun v => flag v = decide (c ≤ K0)) (C * (bitLen c + bitLen b + 1))

/-- **The cutoff test holds (`thresholdTest_holds`, 0 `sorry`)**, with `C = 25`. -/
theorem thresholdTest_holds : ThresholdTestStmt :=
  ⟨25, fun c => ⟨4, CReg, thresholdProg c, thFlag, by norm_num, inferInstance, inferInstance,
    closed_thresholdProg c, fun b K0 k1 k2 r0 σ hC0 => thresholdProg_runs c b K0 k1 k2 r0 σ hC0⟩⟩

/-- **The Walsh test for a cutoff guard (`walshTest_of_threshold`, 0 `sorry`):** for every constant
`c`, `WalshTestStmt (fun _ K0 => decide (c ≤ K0)) (fun n _ => 25 * (bitLen c + bitLen (W8.hB n) + 1))`. -/
theorem walshTest_of_threshold (c : ℕ) :
    WalshTestStmt (fun _ K0 => decide (c ≤ K0)) (fun n _ => 25 * (bitLen c + bitLen (W8.hB n) + 1)) :=
  ⟨4, CReg, thresholdProg c, thFlag, by norm_num, inferInstance, inferInstance,
    closed_thresholdProg c, fun n _ _ _ σ _ _ _ k1 k2 r0 hP =>
      thresholdProg_runs c (W8.hB n) (W8.hK0 n) k1 k2 r0 σ hP.2.2.2.2.2.2.2.2.2.2⟩

end SubNLogN.Machine.Pipe
