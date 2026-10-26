/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulTear
import SubNLogN.Machine.Arith.CMulCost

/-!
# AR4, products: the kernel runs (`Arith/CMulRuns.lean`)

**Scope (honest summary).** `cmulKernel_runs`: exact final stacks and the cost bound of the product
kernel, from any multiplier instance `SpecMulBig Pm Cm`. Everything is proved (no `sorry`).
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-! ## The kernel -/

set_option maxHeartbeats 1000000 in
/-- The coefficient contract of `coefProg Pm` relative to the stacks after the setup. -/
theorem cmul_hspec {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ}
    (hPm : SpecMulBig Pm Cm) {w1 w2 w3 s : ℕ} (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (S : CK → List Sym) (hKC : KClean S) :
    CoefSpecC (coefProg Pm) w1 w2 w3 s (coefBound Cm w1 w2 w3) (setupSt w1 w2 w3 s S) := by
  intro a c Lz Lθ v S' ha1 ha2 hc1 hc2 hfr hz hθ
  have hne : ∀ c' : CS, c' ≠ .T → S' (cs c') = setupSt w1 w2 w3 s S (cs c') := fun c' hc' =>
    hfr _ (by simp) (by simp) (by intro h; exact hc' (by cases h; rfl))
  have hR1 : S' (cs .R1) = List.replicate w1 .mark := by
    rw [hne .R1 (by decide)]; simp [setupSt]
  have hRt : S' (cs .Rt) = List.replicate w2 .mark := by
    rw [hne .Rt (by decide)]; simp [setupSt]
  have hRW : S' (cs .RW) = List.replicate (2 * max w1 w2 + 1) .mark := by
    rw [hne .RW (by decide)]; simp [setupSt]
  have hRs : S' (cs .Rs) = List.replicate (min s (2 * max w1 w2 + 1)) .mark := by
    rw [hne .Rs (by decide)]; simp [setupSt]
  have hRh : S' (cs .Rh) =
      List.replicate (2 * max w1 w2 + 1 - min s (2 * max w1 w2 + 1)) .mark := by
    rw [hne .Rh (by decide)]; simp [setupSt]
  have hR2 : S' (cs .R2) = List.replicate w3 .mark := by
    rw [hne .R2 (by decide)]; simp [setupSt]
  have hWk : ∀ c', isWork c' = true → S' (cs c') = [] := fun c' hc' => by
    rw [hne c' (by intro h; subst h; simp [isWork] at hc')]
    exact setupSt_work hKC c' hc'
  have hG : ∀ g, S' (.inr (.inr g)) = [] := fun g => by
    rw [hfr _ (by simp) (by simp) (by simp)]; simp [setupSt, hKC (.inr g)]
  exact coefProg_eval hPm hw1 hw2 rfl (by omega) a c ha1 ha2 hc1 hc2 Lz Lθ v S' hWk hG hR1 hRt
    hRW hRs hRh hR2 hz hθ

set_option maxHeartbeats 1000000 in
/-- The record loop and the teardown, from the stacks after the setup. -/
theorem cmul_loopTear {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ}
    (hPm : SpecMulBig Pm Cm) (w1 w2 w3 s : ℕ) (z θ : List (List CInt)) (rz rθ : List Sym)
    (S : CK → List Sym) (hKC : KClean S) (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2) (hz1 : CArrFits w1 z)
    (hθ1 : CArrFits w2 θ) (hal : CAligned z θ) (hrz : BlkTerm rz)
    (h0 : S (.inl 0) = carrSyms w1 z ++ rz) (h1 : S (.inl 1) = carrSyms w2 θ ++ rθ)
    (v : AReg × Rm) (hv : v.1.o = (setupSt w1 w2 w3 s S (.inl 0)).head?) :
    ∃ (v' : AReg × Rm) (t : ℕ),
      Eval [] (.seq (recLoopC (coefProg Pm)) (cmulTeardown.liftRegs (Lens.fst AReg Rm)))
        ⟨v, setupSt w1 w2 w3 s S⟩
        ⟨v', Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (.inl 2)
          (carrSyms w3 (zipC (cmulTruncC s) z θ) ++ S (.inl 2))⟩ t ∧
      t ≤ ncoef z * (coefBound Cm w1 w2 w3 + 1) + 6 * z.length + 1 +
        (3 * cvol w3 z + 15 * (w1 + w2) + 3 * w3 + 20) := by
  obtain ⟨v3, t3, e3, ht3⟩ := recLoopC_eval hw1 (cmul_hspec (w3 := w3) (s := s) hPm hw1 hw2 S hKC) z θ rz rθ v
    (setupSt w1 w2 w3 s S) hal hz1 hθ1 hrz (fun k _ _ _ => rfl) (by simp [setupSt, h0])
    (by simp [setupSt, h1]) hv
  obtain ⟨v4, e4⟩ := cmulTeardown_eval w1 w2 w3 s (carrSyms w3 (zipC (cmulTruncC s) z θ)) rz rθ
    (mark_not_mem_carrSyms _ _) v3.1 S hKC
  have e4' := Eval.liftRegs (Lens.fst AReg Rm) e4 v3 rfl
  have hzs := zipC_shape (cmulTruncC s) hal
  have hlen : (carrSyms w3 (zipC (cmulTruncC s) z θ)).length = cvol w3 z := by
    show cvol w3 (zipC (cmulTruncC s) z θ) = cvol w3 z
    rw [cvol_eq, cvol_eq, hzs.1, hzs.2]
  refine ⟨_, _, Eval.seq e3 e4', ?_⟩
  rw [hlen]
  exact Nat.add_le_add ht3 (tear_cost_le w1 w2 w3 s (cvol w3 z))

set_option maxHeartbeats 1000000 in
/-- **The product kernel**, exact final stacks and bounded cost. -/
theorem cmulKernel_runs {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ}
    (hPm : SpecMulBig Pm Cm) (w1 w2 w3 s : ℕ) (z θ : List (List CInt))
    (rz rθ r3 r4 r5 r6 : List Sym) (S : CK → List Sym) (hKC : KClean S) (hw1 : 1 ≤ w1)
    (hw2 : 1 ≤ w2) (hz1 : CArrFits w1 z) (hθ1 : CArrFits w2 θ) (hal : CAligned z θ)
    (hrz : BlkTerm rz) (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5) (hr6 : TermOK r6)
    (h0 : S (.inl 0) = carrSyms w1 z ++ rz) (h1 : S (.inl 1) = carrSyms w2 θ ++ rθ)
    (h3 : S (.inl 3) = natSyms w1 ++ r3) (h4 : S (.inl 4) = natSyms w2 ++ r4)
    (h5 : S (.inl 5) = natSyms w3 ++ r5) (h6 : S (.inl 6) = natSyms s ++ r6) :
    Runs (cmulKernel Pm) S
      (Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (.inl 2)
        (carrSyms w3 (zipC (cmulTruncC s) z θ) ++ S (.inl 2)))
      (fun _ => True)
      ((4 * Cm + 1000) * (ncoef z * mulW (w1 + w2 + 1) + cvol w1 z + cvol w2 θ + cvol w3 z +
        (ncoef z + 1) * (bitLen s + 1) + w1 + w2 + w3)) := by
  apply Runs.of_eval
  intro v0
  obtain ⟨v1, t1, e1, ht1⟩ := cmulSetup_eval w1 w2 w3 s r3 r4 r5 r6 v0.1 S hKC hr3 hr4 hr5 hr6
    h3 h4 h5 h6
  have e1' := Eval.liftRegs (Lens.fst AReg Rm) e1 v0 rfl
  have e2 := Eval.liftRegs (Lens.fst AReg Rm) (eval_peekO (.inl 0) v1 (setupSt w1 w2 w3 s S))
    ((Lens.fst AReg Rm).set v0 v1) rfl
  obtain ⟨v4, t4, e4, ht4⟩ := cmul_loopTear hPm w1 w2 w3 s z θ rz rθ S hKC hw1 hw2 hz1 hθ1 hal
    hrz h0 h1 ((Lens.fst AReg Rm).set ((Lens.fst AReg Rm).set v0 v1)
      { v1 with o := (setupSt w1 w2 w3 s S (.inl 0)).head? }) rfl
  refine ⟨v4, _, Eval.seq e1' (Eval.seq e2 e4), trivial, ?_⟩
  have hal' := aligned_shape hal
  exact cmul_cost_le Cm w1 w2 w3 s (ncoef z) z.length t1 t4 (cvol w1 z) (cvol w2 θ) (cvol w3 z)
    ht1 ht4 (cvol_eq w1 z) (by rw [cvol_eq, hal'.1, hal'.2]) (cvol_eq w3 z)

end SubNLogN.Machine.Arith
