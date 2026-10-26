/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.MulBig.Contract
import SubNLogN.Machine.MulBig.Stages

/-!
# `mulBig` (K0.4): the program on `MBLoc = Fin 3 ⊕ GW` and its exact run

`mulBigProg` runs, on the named stacks `X = .inl 0`, `Y = .inl 1`, `Z = .inl 2` and the 76 scratch
stacks `.inr w` (`w : WP.Top.GW`):
1. `copyBlock X oa`, `copyBlock Y ob` (temporary `xs 0`; `X`, `Y` are restored);
2. the IntMul pipeline stages of `SubNLogN.Machine.MulBig.Stages` on the scratch region
   (parameters, W7 tables, tape conversion, glue, W9), each renamed by `Sum.inr`;
3. `copyBlock oa Z` (the product is pushed on `Z`);
4. `clearList` of all 76 scratch stacks.

Registers: `MRegs Ra Rd R7 Rc R9 = Option Sym × WP.W0m.Regs Ra Rd × R7 × Rc × R9`; each stage reaches
its own component through a lens.

**`mulBigProg_runs`**: for all `x y` there is a W7 hierarchy `cSpec` (with `Joint (operandBits x y)
cSpec`) such that for all rests `rx ry rz` (`TermOK rx`, `TermOK ry`) the program maps
`mbSt (natSyms x ++ rx) (natSyms y ++ ry) rz (fun _ => [])` exactly to
`mbSt (natSyms x ++ rx) (natSyms y ++ ry) (natSyms (x * y) ++ rz) (fun _ => [])`, within the sum
`mbCost …` of the stage costs. `spec_of_runs` turns such a family into `SpecMulBig`.
-/

namespace SubNLogN.Machine.MulBig

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts

/-! ## States on `MBLoc` -/

/-- `MBLoc` stacks with `X`, `Y`, `Z` on the named stacks and `G` on the scratch stacks. -/
def mbSt (X Y Z : List Sym) (G : WP.Top.GW → List Sym) : MBLoc → List Sym
  | .inl i => if i.val = 0 then X else if i.val = 1 then Y else Z
  | .inr w => G w

theorem mbSt_update_inr (X Y Z : List Sym) (G : WP.Top.GW → List Sym) (w : WP.Top.GW)
    (v : List Sym) :
    Function.update (mbSt X Y Z G) (.inr w) v = mbSt X Y Z (Function.update G w v) := by
  funext k
  rcases k with i | w'
  · simp [mbSt]
  · by_cases h : w' = w
    · subst h
      simp [mbSt]
    · simp [mbSt, h]

theorem mbSt_update_inl2 (X Y Z : List Sym) (G : WP.Top.GW → List Sym) (v : List Sym) :
    Function.update (mbSt X Y Z G) (.inl 2) v = mbSt X Y v G := by
  funext k
  rcases k with i | w
  · fin_cases i <;> simp [mbSt]
  · simp [mbSt]

/-- Every `MBLoc` state is an `mbSt`. -/
theorem eq_mbSt {σ : MBLoc → List Sym} {G : WP.Top.GW → List Sym} (hG : ∀ w, σ (.inr w) = G w) :
    σ = mbSt (σ (.inl 0)) (σ (.inl 1)) (σ (.inl 2)) G := by
  funext k
  rcases k with i | w
  · fin_cases i <;> rfl
  · exact hG w

/-- A `Runs` on the scratch region `GW`, renamed by `Sum.inr`: the named stacks are untouched. -/
theorem runs_inr {R : Type} {P : Prog WP.Top.GW (fun _ => Sym) R} {G G' : WP.Top.GW → List Sym}
    {Q : R → Prop} {T : ℕ} (h : Runs P G G' Q T) (X Y Z : List Sym) :
    Runs (P.mapStk (Sum.inr : WP.Top.GW → MBLoc)) (mbSt X Y Z G) (mbSt X Y Z G') Q T :=
  WP.W0m.runs_embed Sum.inr_injective h _ _ (fun _ => rfl) (fun _ => rfl) (fun k hk => by
    rcases k with i | w
    · rfl
    · exact absurd rfl (hk w))

/-! ## Copy-in, copy-out, cleanup -/

/-- Copy `X`'s number onto the empty scratch stack `oa`; `X` is restored. -/
theorem runs_copyX (x : ℕ) (rx Y Z : List Sym) (G : WP.Top.GW → List Sym) (hrx : TermOK rx)
    (hG : G .oa = []) :
    Runs (copyBlock (.inl 0) (.inr .oa) (.inr (.xs 0)) : SProg MBLoc)
      (mbSt (natSyms x ++ rx) Y Z G)
      (mbSt (natSyms x ++ rx) Y Z (Function.update G .oa (natSyms x))) (fun _ => True)
      (7 * bitLen x + 7) := by
  refine Runs.of_eval fun v => ⟨some .mark, 7 * bitLen x + 7, ?_, trivial, le_rfl⟩
  refine (copyBlock_eval (K := MBLoc) (src := .inl 0) (dst := .inr .oa) (tmp := .inr (.xs 0))
    (by decide) (by decide) (by decide) [] v (encodeNat x) rx (mbSt (natSyms x ++ rx) Y Z G) hrx
    rfl).of_eq ?_ rfl
  have e : (encodeNat x).map Sym.bit ++ mbSt (natSyms x ++ rx) Y Z G (.inr .oa) = natSyms x := by
    simp [mbSt, hG, natSyms]
  rw [mbSt_update_inr, e]

/-- Copy `Y`'s number onto the empty scratch stack `ob`; `Y` is restored. -/
theorem runs_copyY (y : ℕ) (X ry Z : List Sym) (G : WP.Top.GW → List Sym) (hry : TermOK ry)
    (hG : G .ob = []) :
    Runs (copyBlock (.inl 1) (.inr .ob) (.inr (.xs 0)) : SProg MBLoc)
      (mbSt X (natSyms y ++ ry) Z G)
      (mbSt X (natSyms y ++ ry) Z (Function.update G .ob (natSyms y))) (fun _ => True)
      (7 * bitLen y + 7) := by
  refine Runs.of_eval fun v => ⟨some .mark, 7 * bitLen y + 7, ?_, trivial, le_rfl⟩
  refine (copyBlock_eval (K := MBLoc) (src := .inl 1) (dst := .inr .ob) (tmp := .inr (.xs 0))
    (by decide) (by decide) (by decide) [] v (encodeNat y) ry (mbSt X (natSyms y ++ ry) Z G) hry
    rfl).of_eq ?_ rfl
  have e : (encodeNat y).map Sym.bit ++ mbSt X (natSyms y ++ ry) Z G (.inr .ob) = natSyms y := by
    simp [mbSt, hG, natSyms]
  rw [mbSt_update_inr, e]

/-- Copy the product from `oa` onto `Z` (pushed on `Z`'s old content). -/
theorem runs_copyZ (v : ℕ) (X Y Z : List Sym) (G : WP.Top.GW → List Sym) (hG : G .oa = natSyms v) :
    Runs (copyBlock (.inr .oa) (.inl 2) (.inr (.xs 0)) : SProg MBLoc) (mbSt X Y Z G)
      (mbSt X Y (natSyms v ++ Z) G) (fun _ => True) (7 * bitLen v + 7) := by
  refine Runs.of_eval fun r => ⟨some .mark, 7 * bitLen v + 7, ?_, trivial, le_rfl⟩
  refine (copyBlock_eval (K := MBLoc) (src := .inr .oa) (dst := .inl 2) (tmp := .inr (.xs 0))
    (by decide) (by decide) (by decide) [] r (encodeNat v) [] (mbSt X Y Z G) TermOK.nil
    (by simp [mbSt, hG, natSyms])).of_eq ?_ rfl
  rw [mbSt_update_inl2]
  rfl

/-- Empty all 76 scratch stacks, whatever they hold. -/
theorem runs_clear (X Y Z : List Sym) (G : WP.Top.GW → List Sym) :
    Runs (WP.Top.clearList (WP.Top.allGW.map Sum.inr) : SProg MBLoc) (mbSt X Y Z G)
      (mbSt X Y Z (fun _ => [])) (fun _ => True) (2 * WP.Top.totalSize G + 2 * 76 + 1) := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, ht, e⟩ := WP.Top.clearList_eval ([] : List (SProg MBLoc))
    (WP.Top.allGW.map Sum.inr) v (mbSt X Y Z G)
  refine ⟨v', t, e.of_eq ?_ rfl, trivial, ?_⟩
  · congr 1
    funext k
    rcases k with i | w
    · have hi : (Sum.inl i : MBLoc) ∉ WP.Top.allGW.map Sum.inr := by
        intro h
        obtain ⟨w, -, hw⟩ := List.mem_map.mp h
        cases hw
      rw [if_neg hi]
      rfl
    · have hw : (Sum.inr w : MBLoc) ∈ WP.Top.allGW.map Sum.inr :=
        List.mem_map_of_mem (WP.Top.mem_allGW w)
      rw [if_pos hw]
      rfl
  · have e2 : ((WP.Top.allGW.map (Sum.inr : WP.Top.GW → MBLoc)).map
        fun k => 2 * (mbSt X Y Z G k).length + 2).sum = 2 * WP.Top.totalSize G + 2 * 76 := by
      rw [List.map_map]
      have h := WP.Top.sum_map_two_mul_add_two WP.Top.allGW (fun w => (G w).length)
      rw [WP.Top.length_allGW] at h
      exact h
    omega

#assert_std_axioms mbSt_update_inr mbSt_update_inl2 eq_mbSt runs_inr runs_copyX runs_copyY
  runs_copyZ runs_clear

/-! ## Registers and the program -/

/-- Registers of `mulBigProg`: the library macros' symbol register, the parameter stage's registers
(`WP.W0m.Regs Ra Rd`), and the private registers of the W7, TapeConv and W9 instances. -/
abbrev MRegs (Ra Rd R7 Rc R9 : Type) := Option Sym × WP.W0m.Regs Ra Rd × R7 × Rc × R9

/-- Lens: the symbol register. -/
def lSym (Ra Rd R7 Rc R9 : Type) : Lens (MRegs Ra Rd R7 Rc R9) (Option Sym) := Lens.fst _ _
/-- Lens: the parameter stage's registers. -/
def lPar (Ra Rd R7 Rc R9 : Type) : Lens (MRegs Ra Rd R7 Rc R9) (WP.W0m.Regs Ra Rd) :=
  (Lens.snd _ _).comp (Lens.fst _ _)
/-- Lens: the table builder's registers. -/
def lTab (Ra Rd R7 Rc R9 : Type) : Lens (MRegs Ra Rd R7 Rc R9) R7 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
/-- Lens: the tape converter's registers. -/
def lConv (Ra Rd R7 Rc R9 : Type) : Lens (MRegs Ra Rd R7 Rc R9) Rc :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
/-- Lens: the multiplier's (W9) registers. -/
def lMul (Ra Rd R7 Rc R9 : Type) : Lens (MRegs Ra Rd R7 Rc R9) R9 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _)))

/-- **The `mulBig` program**, from the stage programs: the W3 adder `Padd` and the W6a divider
`Pdiv` (inside the parameter stage), the W7 builder `P7`, the tape converter `Pc` and the W9
multiplier `P9`. -/
def mulBigProg {ma md m7 mc m9 : ℕ} {Ra Rd R7 Rc R9 : Type}
    (Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra) (hma : ma ≤ 6)
    (Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd) (hmd : md ≤ 6)
    (P7 : Prog (Loc 4 m7) (fun _ => Sym) R7) (hm7 : m7 ≤ 32)
    (Pc : Prog (Loc 1 mc) (fun _ => Sym) Rc) (hmc : mc ≤ 75)
    (P9 : Prog (BLoc m9) (fun _ => Sym) R9) (hm9 : m9 ≤ 64) :
    Prog MBLoc (fun _ => Sym) (MRegs Ra Rd R7 Rc R9) :=
  .seq ((copyBlock (.inl 0) (.inr .oa) (.inr (.xs 0)) : SProg MBLoc).liftRegs
      (lSym Ra Rd R7 Rc R9))
  (.seq ((copyBlock (.inl 1) (.inr .ob) (.inr (.xs 0)) : SProg MBLoc).liftRegs
      (lSym Ra Rd R7 Rc R9))
  (.seq ((((paramProg Padd hma Pdiv hmd).mapStk WP.Top.ι0).mapStk Sum.inr).liftRegs
      (lPar Ra Rd R7 Rc R9))
  (.seq (((P7.mapStk (WP.Top.ι7 hm7)).mapStk Sum.inr).liftRegs (lTab Ra Rd R7 Rc R9))
  (.seq (((Pc.mapStk (WP.Top.ιc hmc)).mapStk Sum.inr).liftRegs (lConv Ra Rd R7 Rc R9))
  (.seq ((WP.Top.glueProg.mapStk Sum.inr).liftRegs (lSym Ra Rd R7 Rc R9))
  (.seq (((P9.mapStk (WP.Top.ι9 hm9)).mapStk Sum.inr).liftRegs (lMul Ra Rd R7 Rc R9))
  (.seq ((copyBlock (.inr .oa) (.inl 2) (.inr (.xs 0)) : SProg MBLoc).liftRegs
      (lSym Ra Rd R7 Rc R9))
    ((WP.Top.clearList (WP.Top.allGW.map Sum.inr) : SProg MBLoc).liftRegs (lSym Ra Rd R7 Rc R9)))))))))

theorem glueProg_closed : WP.Top.glueProg.Closed := by
  have h1 := WP.Top.copyBlock_closed WP.Top.GW.pk (WP.Top.GW.c 0) (WP.Top.GW.xs 0)
  have h2 := WP.Top.copyBlock_closed WP.Top.GW.pK0 (WP.Top.GW.c 0) (WP.Top.GW.xs 0)
  have h3 := WP.Top.copyBlock_closed WP.Top.GW.pb (WP.Top.GW.c 0) (WP.Top.GW.xs 0)
  unfold Prog.Closed at h1 h2 h3 ⊢
  simp only [WP.Top.glueProg, Prog.FreeBelow, pushC, h1, h2, h3, and_self]

/-- `mulBigProg` is closed when the stage programs are. -/
theorem mulBigProg_closed {ma md m7 mc m9 : ℕ} {Ra Rd R7 Rc R9 : Type}
    {Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra} (hma : ma ≤ 6)
    {Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd} (hmd : md ≤ 6)
    {P7 : Prog (Loc 4 m7) (fun _ => Sym) R7} (hm7 : m7 ≤ 32)
    {Pc : Prog (Loc 1 mc) (fun _ => Sym) Rc} (hmc : mc ≤ 75)
    {P9 : Prog (BLoc m9) (fun _ => Sym) R9} (hm9 : m9 ≤ 64)
    (hPa : Padd.Closed) (hPd : Pdiv.Closed) (h7 : P7.Closed) (hc : Pc.Closed) (h9 : P9.Closed) :
    (mulBigProg Padd hma Pdiv hmd P7 hm7 Pc hmc P9 hm9).Closed := by
  have hp := paramProg_closed hma hmd hPa hPd
  have hcx := WP.Top.copyBlock_closed (K := MBLoc) (.inl 0) (.inr .oa) (.inr (.xs 0))
  have hcy := WP.Top.copyBlock_closed (K := MBLoc) (.inl 1) (.inr .ob) (.inr (.xs 0))
  have hcz := WP.Top.copyBlock_closed (K := MBLoc) (.inr .oa) (.inl 2) (.inr (.xs 0))
  have hcl := WP.Top.clearList_closed (WP.Top.allGW.map (Sum.inr : WP.Top.GW → MBLoc))
  have hg := glueProg_closed
  unfold Prog.Closed at hp hcx hcy hcz hcl hg h7 hc h9 ⊢
  simp only [mulBigProg, Prog.FreeBelow, WP.W0m.freeBelow_liftRegs, WP.W0m.freeBelow_mapStk]
  exact ⟨hcx, hcy, hp, h7, hc, hg, h9, hcz, hcl⟩

/-! ## The exact run -/

/-- The sum of the stage costs of one run (right-nested, in program order). -/
def mbCost (Ca Cd C7 Cc C9 : ℕ) (Mul : ℕ → ℕ) (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ) (x y : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) : ℕ :=
  (7 * bitLen x + 7) + ((7 * bitLen y + 7) + (WP.W0m.workCost Ca Cd x y +
    (WP.Top.tabCost C7 (operandBits x y) cSpec + (WP.Top.convCost Cc cSpec +
    (WP.Top.glueCost (operandBits x y) + (WP.Top.w9Cost C9 Mul wdF wdI wR (operandBits x y) cSpec +
    ((7 * bitLen (x * y) + 7) +
      (2 * WP.Top.totalSize (WP.Top.w9Out (operandBits x y) x y cSpec (x * y)) + 2 * 76 + 1))))))))

/-- **The exact run of `mulBigProg`.** For all operands there is a W7 hierarchy `cSpec` such that,
for all rests, the program maps the entry stacks exactly to the exit stacks within `mbCost`. -/
theorem mulBigProg_runs {ma md m7 mc m9 Ca Cd C7 Cc C9 : ℕ} {Ra Rd R7 Rc R9 : Type}
    {Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra} {Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd}
    {P7 : Prog (Loc 4 m7) (fun _ => Sym) R7} {Pc : Prog (Loc 1 mc) (fun _ => Sym) Rc}
    {P9 : Prog (BLoc m9) (fun _ => Sym) R9} {Mul : ℕ → ℕ} {wdF wdI : ℕ → ℕ → ℕ} {wR : ℕ → ℕ}
    (hA : WP.W0m.AddSpec Padd Ca) (hD : WP.W0m.DivSpec Pdiv Cd) (hma : ma ≤ 6) (hmd : md ≤ 6)
    (h7 : WP.Top.W7Spec P7 C7) (hm7 : m7 ≤ 32) (hc : WP.Top.ConvSpec Pc Cc) (hmc : mc ≤ 75)
    (h9 : WP.Top.W9Spec Mul P9 C9) (hm9 : m9 ≤ 64) (hroot : WP.Top.W9RootOK wdF wdI wR)
    (x y : ℕ) :
    ∃ cSpec, WP.Top.Joint (operandBits x y) cSpec ∧
      ∀ rx ry rz : List Sym, TermOK rx → TermOK ry →
        Runs (mulBigProg Padd hma Pdiv hmd P7 hm7 Pc hmc P9 hm9)
          (mbSt (natSyms x ++ rx) (natSyms y ++ ry) rz (fun _ => []))
          (mbSt (natSyms x ++ rx) (natSyms y ++ ry) (natSyms (x * y) ++ rz) (fun _ => []))
          (fun _ => True) (mbCost Ca Cd C7 Cc C9 Mul wdF wdI wR x y cSpec) := by
  obtain ⟨cSpec, hj, h2⟩ := stTab_runs hm7 h7 (operandBits x y) x y
  refine ⟨cSpec, hj, fun rx ry rz hrx hry => ?_⟩
  set X := natSyms x ++ rx with hX
  set Y := natSyms y ++ ry with hY
  have e1 := WP.W0m.runs_liftRegs (lSym Ra Rd R7 Rc R9)
    (runs_copyX x rx Y rz (fun _ => []) hrx rfl)
  have e2 := WP.W0m.runs_liftRegs (lSym Ra Rd R7 Rc R9)
    (runs_copyY y X ry rz (Function.update (fun _ => []) .oa (natSyms x)) hry (by simp))
  have e3 := WP.W0m.runs_liftRegs (lPar Ra Rd R7 Rc R9)
    (runs_inr (stParam_runs hA hD hma hmd x y) X Y rz)
  have e4 := WP.W0m.runs_liftRegs (lTab Ra Rd R7 Rc R9) (runs_inr h2 X Y rz)
  have e5 := WP.W0m.runs_liftRegs (lConv Ra Rd R7 Rc R9)
    (runs_inr (stConv_runs hmc hc _ x y cSpec hj) X Y rz)
  have e6 := WP.W0m.runs_liftRegs (lSym Ra Rd R7 Rc R9)
    (runs_inr (stGlue_runs (operandBits x y) x y cSpec) X Y rz)
  have e7 := WP.W0m.runs_liftRegs (lMul Ra Rd R7 Rc R9)
    (runs_inr (stW9_runs hm9 h9 hroot x y cSpec hj) X Y rz)
  have e8 := WP.W0m.runs_liftRegs (lSym Ra Rd R7 Rc R9)
    (runs_copyZ (x * y) X Y rz (WP.Top.w9Out (operandBits x y) x y cSpec (x * y))
      (by simp [WP.Top.w9Out]))
  have e9 := WP.W0m.runs_liftRegs (lSym Ra Rd R7 Rc R9)
    (runs_clear X Y (natSyms (x * y) ++ rz) (WP.Top.w9Out (operandBits x y) x y cSpec (x * y)))
  exact WP.W0m.runs_mono (WP.W0m.runs_seq e1 (WP.W0m.runs_seq e2 (WP.W0m.runs_seq e3
    (WP.W0m.runs_seq e4 (WP.W0m.runs_seq e5 (WP.W0m.runs_seq e6 (WP.W0m.runs_seq e7
      (WP.W0m.runs_seq e8 e9))))))))
    (fun _ _ => trivial) le_rfl

/-- A family of exact runs from `mbSt` entry stacks is a `SpecMulBig` instance. -/
theorem spec_of_runs {R : Type} {P : Prog MBLoc (fun _ => Sym) R} {C : ℕ}
    (h : ∀ (x y : ℕ) (rx ry rz : List Sym), TermOK rx → TermOK ry →
      Runs P (mbSt (natSyms x ++ rx) (natSyms y ++ ry) rz (fun _ => []))
        (mbSt (natSyms x ++ rx) (natSyms y ++ ry) (natSyms (x * y) ++ rz) (fun _ => []))
        (fun _ => True) (C * mulBigBound x y)) :
    SpecMulBig P C := by
  intro x y rx ry rz σ hrx hry hX hY hZ hG
  have e : σ = mbSt (natSyms x ++ rx) (natSyms y ++ ry) rz (fun _ => []) := by
    rw [eq_mbSt (G := fun _ => []) hG, hX, hY, hZ]
  subst e
  rw [mbSt_update_inl2]
  exact h x y rx ry rz hrx hry

#assert_std_axioms glueProg_closed mulBigProg_closed mulBigProg_runs spec_of_runs

end SubNLogN.Machine.MulBig
