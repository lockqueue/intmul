import WP.W0m.Stage

/-!
# WP.W0m.Main — the W0m contract and its proof (W3 adder and W6a divider as hypotheses)

`W0m_inputStage`: there are a finite nonempty register type `σ` and a constant `C` such that, for
every machine work-stack type `W` and injective `ι : Stk → W`, a closed program over the
production layout has the following behaviour:
* it starts from `inputStk (encNatPair.encode (a, b))`;
* it ends with input and output stacks empty, `work (ι x) = outW a b x`, and every other work stack
  empty;
* it takes at most `C·(L + 1) + C·(Λ + 1)²` steps, with `L` the input length and
  `Λ = lam a b = O(log L)`.

The hypotheses `W3_addNat` and `W6a_divModNat` are discharged by the integrator once W3 and W6a are
proved.
-/

namespace WP.W0m

open Computability TMFw TMFw.Lib TMFw.Contracts IntMulTM

theorem workProg_closed {ma md : ℕ} {Ra Rd : Type} {Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra}
    {Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd} (hma : ma ≤ 6) (hmd : md ≤ 6)
    (hPa : Padd.Closed) (hPd : Pdiv.Closed) : (workProg Padd hma Pdiv hmd : WProg Ra Rd).Closed := by
  unfold Prog.Closed at hPa hPd ⊢
  simp [workProg, phA, phB, phC, phD, phE, phF, phG, phH, sym, cmpW, addW, divW, Prog.FreeBelow,
    freeBelow_liftRegs, freeBelow_mapStk, hPa, hPd, moveBits, moveBitsBody, countBits, cntLoop,
    cntBody, copyBlock, moveBlock, moveBitsDup, dupBody, dropNat, dropLoop, inc, incFix, scanLoop,
    scanBody, dec, decFix, zeroTest, pushC, pushR, popR, peekR, restoreR, Lib.skip, cmpNum, cmpBody]

/-- **W0m contract** (input stage over the production layout). -/
def W0m_inputStage : Prop :=
  ∃ (σ : Type) (_ : Finite σ) (_ : Nonempty σ) (C : ℕ),
    ∀ (W : Type) [DecidableEq W] (ι : Stk → W), Function.Injective ι →
      ∃ P : Prog (StackId W) (StackId.Γ encNatPair.Γ) σ, P.Closed ∧ ∀ a b : ℕ,
        Triple [] (fun s => s.stk = inputStk (encNatPair.encode (a, b))) P
          (fun s => s.stk .input = [] ∧ s.stk .output = [] ∧
            (∀ x, s.stk (.work (ι x)) = outW a b x) ∧ ∀ w, (∀ x, ι x ≠ w) → s.stk (.work w) = [])
          (C * ((encNatPair.encode (a, b)).length + 1) + C * ((lam a b + 1) * (lam a b + 1)))

theorem lam_ge_three (a b : ℕ) : 3 ≤ lam a b := by
  unfold lam
  rw [bitLen_eq_size]
  exact Nat.lt_size.mpr (by rw [show (2 : ℕ) ^ 2 = 4 from rfl]; unfold inLen; omega)

/-- **Main theorem of W0m.** -/
theorem W0m_inputStage_holds (hadd : W3_addNat) (hdiv : W6a_divModNat) : W0m_inputStage := by
  obtain ⟨Ca, ma, Ra, Padd, hma, hfa, hna, hcla, hA⟩ := addSpec_of_W3 hadd
  obtain ⟨Cd, md, Rd, Pdiv, hmd, hfd, hnd, hcld, hD⟩ := divSpec_of_W6a hdiv
  have hma6 : ma ≤ 6 := by omega
  refine ⟨Option Sym × Regs Ra Rd, inferInstance, inferInstance, 400 + Ca + Cd,
    fun W _ ι hι => ⟨inputStage ι (workProg Padd hma6 Pdiv hmd),
      inputStage_closed ι (workProg_closed hma6 hmd hcla hcld), fun a b => ?_⟩⟩
  refine Triple.cost_mono
    (inputStage_triple hι (fun a b => workProg_runs hA hD hma6 hmd a b) a b) ?_
  have hL : (encNatPair.encode (a, b)).length = inLen a b := by
    rw [encNatPair_encode_length]
    rfl
  rw [hL]
  have h3 := lam_ge_three a b
  unfold workCost
  set Λ := lam a b with hΛ
  set X := (Λ + 1) * (Λ + 1) with hX
  have hsq : X = Λ * Λ + 2 * Λ + 1 := by rw [hX, sq_succ]
  have h3Λ : 3 * Λ ≤ Λ * Λ := Nat.mul_le_mul_right Λ h3
  have hX1 : 4 * Λ + 2 ≤ X := by omega
  have hCa : Ca * (4 * Λ + 2) ≤ Ca * X := Nat.mul_le_mul_left Ca hX1
  have hd1 : (400 + Ca + Cd) * (inLen a b + 1) =
      400 * (inLen a b + 1) + Ca * (inLen a b + 1) + Cd * (inLen a b + 1) := by
    rw [Nat.add_mul, Nat.add_mul]
  have hd2 : (400 + Ca + Cd) * X = 400 * X + Ca * X + Cd * X := by rw [Nat.add_mul, Nat.add_mul]
  rw [hd1, hd2]
  unfold inLen
  omega

#assert_std_axioms workProg_closed lam_ge_three W0m_inputStage_holds

end WP.W0m
