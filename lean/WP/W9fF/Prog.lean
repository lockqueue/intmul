import WP.W9fF.HostOps
import WP.W9fF.StepEv
import WP.W9fF.Bnd
import WP.W9fF.Comb
import WP.W9fF.InitCost

/-!
# WP.W9fF.Prog — the forward-core program and its state predicates

Program (`mainProg I`, over `HK` with IntLang's registers `GReg I`):
1. `setupP`: create the 31 variables (value 0, guarded), guard PZ and PH, load `q, H, μ, a, c`,
   run `pSetA; pSetB; pSetC` (constants `S2 = q+2`, `ONE`, `SS = 2^(q+2)`, `HALF = 2^(q+1)`);
2. `startP`: pop `Y[0]` into `Y01, Y02`; `pInit`; push zPart[0], zHom[0] onto PZ, PH;
3. `whileEnt I inL (body1 I)`: pop `Y[n+1]`, `pStepF`, push zPart[n+1], zHom[n+1];
4. `slc I pBnd` (boundary value `Z0` into `W1, W2`);
5. `whileEnt I pzL (body2 I)`: pop zPart[u], zHom[u], `pComb`, push the output entry onto OUT;
6. `teardownP`: drop the guards of PZ, PH and all variables.

State predicates: `ColOK` (the contract's hypotheses), `AllW`, `J1` (loop 1), `J2` (loop 2),
`HS S J i o pz ph` (some `env` with `J env` and host stacks `hs S env i o pz ph`), and
`hs_triple` (exact-stack steps give `HS` triples).
-/

namespace WP.W9fF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fF.IL WP.W9f IntMul IntMulTM.Contracts

section Progs

variable (I : Op → OpImpl)

/-- Loop 1 body. -/
def body1 : Prog HK (fun _ => Sym) (GReg I) :=
  .seq (hM I (popEntry inL (vLoc .Y1) (vLoc .Y2) tmpL))
    (.seq (slc I pStepF) (.seq (hM I (pushEntry (vLoc .Z1) (vLoc .Z2) pzL tmpL))
      (hM I (pushEntry (vLoc .G1) (vLoc .G2) phL tmpL))))

/-- Loop 2 body. -/
def body2 : Prog HK (fun _ => Sym) (GReg I) :=
  .seq (hM I (popEntry pzL (vLoc .Z1) (vLoc .Z2) tmpL))
    (.seq (hM I (popEntry phL (vLoc .G1) (vLoc .G2) tmpL))
      (.seq (slc I pComb) (hM I (pushEntry (vLoc .T7) (vLoc .T8) outL tmpL))))

/-- Setup. -/
def setupP : Prog HK (fun _ => Sym) (GReg I) :=
  .seq (hM I (lay.initVars V.all)) (.seq (hM I (pushC pzL .mark)) (.seq (hM I (pushC phL .mark))
    (.seq (hM I (loadNat qL (vLoc .S2) tmpL)) (.seq (hM I (loadNat hL (vLoc .HV) tmpL))
    (.seq (hM I (loadNat muL (vLoc .MU) tmpL)) (.seq (hM I (loadInt aL (vLoc .DA) tmpL))
    (.seq (hM I (loadInt cL (vLoc .MC) tmpL))
    (.seq (slc I pSetA) (.seq (slc I pSetB) (slc I pSetC))))))))))

/-- First entry and initial recurrence state. -/
def startP : Prog HK (fun _ => Sym) (GReg I) :=
  .seq (hM I (popEntry inL (vLoc .Y01) (vLoc .Y02) tmpL)) (.seq (slc I pInit)
    (.seq (hM I (pushEntry (vLoc .Z1) (vLoc .Z2) pzL tmpL))
      (hM I (pushEntry (vLoc .G1) (vLoc .G2) phL tmpL))))

/-- Teardown. -/
def teardownP : Prog HK (fun _ => Sym) (GReg I) :=
  .seq (hM I (popR pzL)) (.seq (hM I (popR phL)) (hM I (lay.dropVars V.all)))

/-- **The forward core.** -/
def mainProg : Prog HK (fun _ => Sym) (GReg I) :=
  .seq (.seq (setupP I) (startP I)) (.seq (whileEnt I inL (body1 I))
    (.seq (.seq (slc I pBnd) (whileEnt I pzL (body2 I))) (teardownP I)))

end Progs

/-! ## State predicates -/

/-- The contract's hypotheses on one column. -/
structure ColOK (q H μ : ℕ) (a c : ℤ) (Ys : Array (ℤ × ℤ)) : Prop where
  size : 2 ≤ Ys.size
  qH : q + 2 ≤ H
  apos : 0 < a
  mu : (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a
  aw : bitLen a.natAbs ≤ H
  cw : bitLen c.natAbs ≤ H
  yw : ArrW H Ys
  zb : W8.zPartFwdBound q H a c Ys (Ys.size - 1)
  hb : W8.zHomFwdBound q H a c (Ys.size - 1)
  ow : ArrW H (W8.solveFwdBarrett q H Ys.size μ a c Ys)

/-- Every variable fits the declared product width. -/
def AllW (H : ℕ) (env : V → ℤ) : Prop := ∀ v, bitLen (env v).natAbs ≤ solW H

/-- Loop-1 invariant on the variables after `k` recurrence steps. -/
def J1 (q H μ : ℕ) (a c : ℤ) (Ys : Array (ℤ × ℤ)) (k : ℕ) (env : V → ℤ) : Prop :=
  Prm env q H (μ : ℤ) a c ∧ env .Y01 = (read1D Ys 0).1 ∧ env .Y02 = (read1D Ys 0).2 ∧
    env .Z1 = (zpE q H μ a c Ys k).1 ∧ env .Z2 = (zpE q H μ a c Ys k).2 ∧
    env .G1 = (zhE q H μ a c k).1 ∧ env .G2 = (zhE q H μ a c k).2 ∧ AllW H env

/-- Loop-2 invariant on the variables. -/
def J2 (q H μ : ℕ) (a c : ℤ) (Ys : Array (ℤ × ℤ)) (env : V → ℤ) : Prop :=
  Prm env q H (μ : ℤ) a c ∧ env .W1 = (z0E q H Ys.size μ a c Ys).1 ∧
    env .W2 = (z0E q H Ys.size μ a c Ys).2 ∧ AllW H env

/-- Host stacks `hs S env i o pz ph` for some `env` with `J env`. -/
def HS (S : HK → List Sym) (J : (V → ℤ) → Prop) (i o pz ph : List Sym) (St : HK → List Sym) :
    Prop :=
  ∃ env, J env ∧ St = hs S env i o pz ph

/-- Exact-stack steps give `HS` triples. -/
theorem hs_triple (I : Op → OpImpl) {prog : Prog HK (fun _ => Sym) (GReg I)} {S : HK → List Sym}
    {J J' : (V → ℤ) → Prop} {i o pz ph i' o' pz' ph' : List Sym} {T : ℕ}
    (h : ∀ env, J env → ∃ env', J' env' ∧
      RunsS prog (hs S env i o pz ph) (hs S env' i' o' pz' ph') T) :
    Triple [] (fun s => HS S J i o pz ph s.stk) prog (fun s => HS S J' i' o' pz' ph' s.stk) T := by
  rintro s ⟨env, hJ, hs0⟩
  obtain ⟨env', hJ', hr⟩ := h env hJ
  obtain ⟨s', t, e, hs', ht⟩ := hr s hs0
  exact ⟨s', t, e, ⟨env', hJ', hs'⟩, ht⟩

theorem hM_noRec (I : Op → OpImpl) (p : SProg HK) (h : noRec p = true) : (hM I p).Closed :=
  hM_closed I p (fb_of_noRec p 0 h)

/-- **The program is closed** when the op implementations are. -/
theorem mainProg_closed (I : Op → OpImpl) (hI : ∀ o, (I o).P.Closed) : (mainProg I).Closed := by
  have sl := slc_closed I hI
  refine ⟨⟨⟨hM_noRec I _ rfl, hM_noRec I _ rfl, hM_noRec I _ rfl, hM_noRec I _ rfl,
    hM_noRec I _ rfl, hM_noRec I _ rfl, hM_noRec I _ rfl, hM_noRec I _ rfl, sl _, sl _, sl _⟩,
    hM_noRec I _ rfl, sl _, hM_noRec I _ rfl, hM_noRec I _ rfl⟩,
    whileEnt_closed I _ _ ⟨hM_noRec I _ rfl, sl _, hM_noRec I _ rfl, hM_noRec I _ rfl⟩,
    ⟨sl _, whileEnt_closed I _ _ ⟨hM_noRec I _ rfl, hM_noRec I _ rfl, sl _, hM_noRec I _ rfl⟩⟩,
    hM_noRec I _ rfl, hM_noRec I _ rfl, hM_noRec I _ rfl⟩

#assert_std_axioms hs_triple hM_noRec mainProg_closed

end WP.W9fF
