/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Arith.CMulBRec
import SubNLogN.Machine.Arith.CMulKC
import SubNLogN.Machine.Arith.CMulCost

/-!
# AR4b: the broadcast product kernel runs; `CMulTruncBcastStmt` (`Arith/CMulBRuns.lean`)

**Scope (honest summary).** `cmulBKernel_runs` (exact final stacks, bounded cost) and
`cmulTruncBcast_holds : CMulTruncBcastStmt` (`Machine/Contracts/Arith.lean`, AR4b;
Section 6.3 (`sec:direct-fft-twiddle`), Theorem 6.5 (`thm:direct-fft`)). Everything is proved (no `sorry`); the multiplier enters only through
the premise `MulBigContract`; the kernel constant is `4·Cm + 1000`. The statement's hypotheses
`1 ≤ w3`, `BlkTerm rθ`, `CArrFits w3 (cmulTruncBcast s z θ)` are not needed by the proof.
-/

namespace SubNLogN.Machine.Arith

open TMFw TMFw.Contracts SubNLogN.Machine Computability

theorem cmulB_cost_le (Cm w1 w2 w3 s n L t1 t4 c1 c2 c3 : ℕ)
    (ht1 : t1 ≤ 300 * (w1 + w2 + w3 + bitLen s) + 300)
    (ht4 : t4 ≤ n * (14 * w2 + 7 + coefBound Cm w1 w2 w3 + 1) + L * (30 * w2 + 31) + 1 +
      (3 * c3 + 15 * (w1 + w2) + 3 * w3 + 20))
    (hc1 : c1 = L + 2 * w1 * n) (hc2 : c2 = L + 2 * w2 * L) (hc3 : c3 = L + 2 * w3 * n) :
    t1 + (1 + t4) ≤ (4 * Cm + 1000) * (n * mulW (w1 + w2 + 1) + c1 + c2 + c3 +
      (n + 1) * (w2 + bitLen s + 1) + w1 + w2 + w3) := by
  have hkey : n * (14 * w2 + 7 + coefBound Cm w1 w2 w3 + 1) =
      4 * (Cm * (n * mulW (w1 + w2 + 1))) + 400 * (n * w1) + 414 * (n * w2) +
        400 * (n * w3) + 408 * n := by
    unfold coefBound; ring
  have hD : (n + 1) * (w2 + bitLen s + 1) = n * w2 + n * bitLen s + n + w2 + bitLen s + 1 := by
    ring
  have hL : L * (30 * w2 + 31) = 30 * (L * w2) + 31 * L := by ring
  have hc1' : c1 = L + 2 * (n * w1) := by rw [hc1]; ring
  have hc2' : c2 = L + 2 * (L * w2) := by rw [hc2]; ring
  have hc3' : c3 = L + 2 * (n * w3) := by rw [hc3]; ring
  have hexp : (4 * Cm + 1000) * (n * mulW (w1 + w2 + 1) + c1 + c2 + c3 +
      (n + 1) * (w2 + bitLen s + 1) + w1 + w2 + w3) =
      4 * (Cm * (n * mulW (w1 + w2 + 1) + c1 + c2 + c3 + (n + 1) * (w2 + bitLen s + 1) + w1 +
        w2 + w3)) + 1000 * (n * mulW (w1 + w2 + 1) + c1 + c2 + c3 +
        (n + 1) * (w2 + bitLen s + 1) + w1 + w2 + w3) := by ring
  have hXm : Cm * (n * mulW (w1 + w2 + 1)) ≤ Cm * (n * mulW (w1 + w2 + 1) + c1 + c2 + c3 +
      (n + 1) * (w2 + bitLen s + 1) + w1 + w2 + w3) := Nat.mul_le_mul_left _ (by omega)
  rw [hexp]
  rw [hkey, hL] at ht4
  generalize Cm * (n * mulW (w1 + w2 + 1) + c1 + c2 + c3 + (n + 1) * (w2 + bitLen s + 1) + w1 +
    w2 + w3) = A1 at hXm ⊢
  generalize Cm * (n * mulW (w1 + w2 + 1)) = A2 at hXm ht4
  generalize n * mulW (w1 + w2 + 1) = E at hXm ⊢
  generalize (n + 1) * (w2 + bitLen s + 1) = D at hD ⊢
  generalize n * bitLen s = F at hD
  generalize n * w1 = B1 at hc1' ht4
  generalize n * w2 = B2 at hD ht4
  generalize n * w3 = B3 at hc3' ht4
  generalize L * w2 = G at hc2' ht4
  subst hc1' hc2' hc3' hD
  linarith

theorem bcastArr_shape (θ : List CInt) :
    (bcastArr θ).length = θ.length ∧ ncoef (bcastArr θ) = θ.length := by
  induction θ with
  | nil => simp [bcastArr, ncoef]
  | cons t θ ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [bcastArr, ncoef, List.map_cons, List.length_cons, List.sum_cons] at h1 h2 ⊢
    refine ⟨by rw [h1], ?_⟩
    rw [h2]
    simp only [List.length_nil, List.length_singleton]
    omega

theorem cmulTruncBcast_shape (s : ℕ) : ∀ {z : List (List CInt)} {θ : List CInt},
    z.length = θ.length →
      (cmulTruncBcast s z θ).length = z.length ∧ ncoef (cmulTruncBcast s z θ) = ncoef z
  | [], [], _ => by simp [cmulTruncBcast, ncoef]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: z, t :: θ, h => by
    obtain ⟨h1, h2⟩ := cmulTruncBcast_shape s (z := z) (θ := θ) (by simpa using h)
    simp only [cmulTruncBcast, ncoef, List.zipWith_cons_cons, List.length_cons, List.map_cons,
      List.sum_cons, List.length_map] at h1 h2 ⊢
    exact ⟨by rw [h1], by rw [h2]⟩

theorem phaseIn_closed : phaseIn.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, phaseIn, drainBits, dbLoop, peekQ, peekO, drop1,
    Prog.liftRegs, Lib.copyBlock, Lib.moveBlock, Lib.moveBitsDup, Lib.dupBody, Lib.pushC,
    Lib.popR, Lib.pushR, Lib.moveBits, Lib.moveBitsBody, Lib.restoreR, Lib.skip]

theorem phaseOut_closed : phaseOut.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, phaseOut, drainBits, dbLoop, peekQ, peekO, drop1, pushS,
    recTail]

theorem copyWB_closed :
    ((Lib.copyBlock (cs .WB) (.inl 1 : CK) (cs .CT)).liftRegs lensO).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, Prog.liftRegs, Lib.copyBlock, Lib.moveBlock,
    Lib.moveBitsDup, Lib.dupBody, Lib.pushC, Lib.popR, Lib.pushR, Lib.moveBits,
    Lib.moveBitsBody, Lib.restoreR, Lib.skip]

theorem cmulBKernel_closed {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} (hcl : Pm.Closed) :
    (cmulBKernel Pm).Closed := by
  have hS := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) cmulSetup_closed
  have hO := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) (p := peekO (K := CK) (.inl 0))
    (by simp [Prog.Closed, Prog.FreeBelow, peekO])
  have hI := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) phaseIn_closed
  have hOut := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) phaseOut_closed
  have hC := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) copyWB_closed
  have hA := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) absAll_closed
  have hP := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) postAll_closed
  have hT := WP.W9comp.closed_liftRegs (Lens.fst AReg Rm) cmulTeardown_closed
  have hM1 := closed_callInj (mbι .Ma .Mc .P1) (Lens.snd AReg Rm) hcl
  have hM2 := closed_callInj (mbι .Mb .Md .P2) (Lens.snd AReg Rm) hcl
  have hM3 := closed_callInj (mbι .Ma .Md .P3) (Lens.snd AReg Rm) hcl
  have hM4 := closed_callInj (mbι .Mb .Mc .P4) (Lens.snd AReg Rm) hcl
  simp only [Prog.Closed] at hS hO hI hOut hC hA hP hT hM1 hM2 hM3 hM4 ⊢
  simp only [cmulBKernel, recLoopB, recBodyB, coefLoop, cpB, coefProg, mulAll, Prog.FreeBelow,
    hS, hO, hI, hOut, hC, hA, hP, hT, hM1, hM2, hM3, hM4, and_self]

/-! ## The broadcast kernel -/

set_option maxHeartbeats 1000000 in
/-- The coefficient contract of `cpB Pm`, for every phase, relative to the stacks after the setup
with the phase in the buffer. -/
theorem cmulB_hcp {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ}
    (hPm : SpecMulBig Pm Cm) {w1 w2 w3 s : ℕ} (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (S : CK → List Sym) (hKC : KClean S) :
    ∀ (t : CInt), FitsTwos w2 t.1 → FitsTwos w2 t.2 → ∀ S1 : CK → List Sym,
      (∀ k, k ≠ .inl 0 → k ≠ .inl 1 → k ≠ cs .T → k ≠ cs .WB →
        S1 k = setupSt w1 w2 w3 s S k) →
      S1 (cs .WB) = (coefBits w2 t).map Sym.bit →
      CoefSpecB (cpB Pm) w1 w3 (fun a => cmulTruncC s a t)
        (14 * w2 + 7 + coefBound Cm w1 w2 w3) S1 := by
  intro t ht1 ht2 S1 hfr hWB
  have hne : ∀ c' : CS, c' ≠ .T → c' ≠ .WB → S1 (cs c') = setupSt w1 w2 w3 s S (cs c') :=
    fun c' h1 h2 => hfr _ (by simp) (by simp) (by intro h; exact h1 (by cases h; rfl))
      (by intro h; exact h2 (by cases h; rfl))
  have hR1 : S1 (cs .R1) = List.replicate w1 .mark := by
    rw [hne .R1 (by decide) (by decide)]; simp [setupSt]
  have hRt : S1 (cs .Rt) = List.replicate w2 .mark := by
    rw [hne .Rt (by decide) (by decide)]; simp [setupSt]
  have hRW : S1 (cs .RW) = List.replicate (2 * max w1 w2 + 1) .mark := by
    rw [hne .RW (by decide) (by decide)]; simp [setupSt]
  have hRs : S1 (cs .Rs) = List.replicate (min s (2 * max w1 w2 + 1)) .mark := by
    rw [hne .Rs (by decide) (by decide)]; simp [setupSt]
  have hRh : S1 (cs .Rh) =
      List.replicate (2 * max w1 w2 + 1 - min s (2 * max w1 w2 + 1)) .mark := by
    rw [hne .Rh (by decide) (by decide)]; simp [setupSt]
  have hR2 : S1 (cs .R2) = List.replicate w3 .mark := by
    rw [hne .R2 (by decide) (by decide)]; simp [setupSt]
  have hWk : ∀ c', isWork c' = true → S1 (cs c') = [] := fun c' hc' => by
    rw [hne c' (by intro h; subst h; simp [isWork] at hc')
      (by intro h; subst h; simp [isWork] at hc')]
    exact setupSt_work hKC c' hc'
  have hG : ∀ g, S1 (.inr (.inr g)) = [] := fun g => by
    rw [hfr _ (by simp) (by simp) (by simp) (by simp)]; simp [setupSt, hKC (.inr g)]
  exact cpB_spec hPm hw1 hw2 rfl (by omega) t ht1 ht2 S1 hWk hG hR1 hRt hRW hRs hRh hR2 hWB

set_option maxHeartbeats 1000000 in
/-- The record loop and the teardown of the broadcast kernel, from the stacks after the setup. -/
theorem cmulB_loopTear {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ}
    (hPm : SpecMulBig Pm Cm) (w1 w2 w3 s : ℕ) (z : List (List CInt)) (θ : List CInt)
    (rz rθ : List Sym) (S : CK → List Sym) (hKC : KClean S) (hw1 : 1 ≤ w1) (hw2 : 1 ≤ w2)
    (hz1 : CArrFits w1 z) (hθ1 : CArrFits w2 (bcastArr θ)) (hlen : z.length = θ.length)
    (hrz : BlkTerm rz) (h0 : S (.inl 0) = carrSyms w1 z ++ rz)
    (h1 : S (.inl 1) = carrSyms w2 (bcastArr θ) ++ rθ)
    (v : AReg × Rm) (hv : v.1.o = (setupSt w1 w2 w3 s S (.inl 0)).head?) :
    ∃ (v' : AReg × Rm) (t : ℕ),
      Eval [] (.seq (recLoopB Pm) (cmulTeardown.liftRegs (Lens.fst AReg Rm)))
        ⟨v, setupSt w1 w2 w3 s S⟩
        ⟨v', Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (.inl 2)
          (carrSyms w3 (cmulTruncBcast s z θ) ++ S (.inl 2))⟩ t ∧
      t ≤ ncoef z * (14 * w2 + 7 + coefBound Cm w1 w2 w3 + 1) + z.length * (30 * w2 + 31) + 1 +
        (3 * cvol w3 z + 15 * (w1 + w2) + 3 * w3 + 20) := by
  obtain ⟨v3, t3, e3, ht3⟩ := recLoopB_eval hw1 hw2 (cmulB_hcp (w3 := w3) (s := s) hPm hw1 hw2 S hKC)
    (by simp [setupSt, hKC (.inl .WB)]) (by simp [setupSt, hKC (.inl .CT)]) z θ rz rθ v
    (setupSt w1 w2 w3 s S) hlen hz1 hθ1 hrz (fun k _ _ _ => rfl) (by simp [setupSt, h0])
    (by simp [setupSt, h1]) hv
  obtain ⟨v4, e4⟩ := cmulTeardown_eval w1 w2 w3 s (carrSyms w3 (cmulTruncBcast s z θ)) rz rθ
    (mark_not_mem_carrSyms _ _) v3.1 S hKC
  have e4' := Eval.liftRegs (Lens.fst AReg Rm) e4 v3 rfl
  have hsh := cmulTruncBcast_shape s hlen
  have hlen' : (carrSyms w3 (cmulTruncBcast s z θ)).length = cvol w3 z := by
    show cvol w3 (cmulTruncBcast s z θ) = cvol w3 z
    rw [cvol_eq, cvol_eq, hsh.1, hsh.2]
  refine ⟨_, _, Eval.seq e3 e4', ?_⟩
  rw [hlen']
  exact Nat.add_le_add ht3 (tear_cost_le w1 w2 w3 s (cvol w3 z))

set_option maxHeartbeats 1000000 in
/-- **The broadcast product kernel**, exact final stacks and bounded cost. -/
theorem cmulBKernel_runs {Rm : Type} {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ}
    (hPm : SpecMulBig Pm Cm) (w1 w2 w3 s : ℕ) (z : List (List CInt)) (θ : List CInt)
    (rz rθ r3 r4 r5 r6 : List Sym) (S : CK → List Sym) (hKC : KClean S) (hw1 : 1 ≤ w1)
    (hw2 : 1 ≤ w2) (hz1 : CArrFits w1 z) (hθ1 : CArrFits w2 (bcastArr θ))
    (hlen : z.length = θ.length) (hrz : BlkTerm rz) (hr3 : TermOK r3) (hr4 : TermOK r4)
    (hr5 : TermOK r5) (hr6 : TermOK r6)
    (h0 : S (.inl 0) = carrSyms w1 z ++ rz) (h1 : S (.inl 1) = carrSyms w2 (bcastArr θ) ++ rθ)
    (h3 : S (.inl 3) = natSyms w1 ++ r3) (h4 : S (.inl 4) = natSyms w2 ++ r4)
    (h5 : S (.inl 5) = natSyms w3 ++ r5) (h6 : S (.inl 6) = natSyms s ++ r6) :
    Runs (cmulBKernel Pm) S
      (Function.update (Function.update (Function.update S (.inl 0) rz) (.inl 1) rθ) (.inl 2)
        (carrSyms w3 (cmulTruncBcast s z θ) ++ S (.inl 2)))
      (fun _ => True)
      ((4 * Cm + 1000) * (ncoef z * mulW (w1 + w2 + 1) + cvol w1 z + cvol w2 (bcastArr θ) +
        cvol w3 z + (ncoef z + 1) * (w2 + bitLen s + 1) + w1 + w2 + w3)) := by
  apply Runs.of_eval
  intro v0
  obtain ⟨v1, t1, e1, ht1⟩ := cmulSetup_eval w1 w2 w3 s r3 r4 r5 r6 v0.1 S hKC hr3 hr4 hr5 hr6
    h3 h4 h5 h6
  have e1' := Eval.liftRegs (Lens.fst AReg Rm) e1 v0 rfl
  have e2 := Eval.liftRegs (Lens.fst AReg Rm) (eval_peekO (.inl 0) v1 (setupSt w1 w2 w3 s S))
    ((Lens.fst AReg Rm).set v0 v1) rfl
  obtain ⟨v4, t4, e4, ht4⟩ := cmulB_loopTear hPm w1 w2 w3 s z θ rz rθ S hKC hw1 hw2 hz1 hθ1 hlen
    hrz h0 h1 ((Lens.fst AReg Rm).set ((Lens.fst AReg Rm).set v0 v1)
      { v1 with o := (setupSt w1 w2 w3 s S (.inl 0)).head? }) rfl
  refine ⟨v4, _, Eval.seq e1' (Eval.seq e2 e4), trivial, ?_⟩
  have hb := bcastArr_shape θ
  exact cmulB_cost_le Cm w1 w2 w3 s (ncoef z) z.length t1 t4 (cvol w1 z) (cvol w2 (bcastArr θ))
    (cvol w3 z) ht1 ht4 (cvol_eq w1 z) (by rw [cvol_eq, hb.1, hb.2, hlen]) (cvol_eq w3 z)

/-! ## The contract -/

/-- **`CMulTruncBcastStmt` holds** (`Machine/Contracts/Arith.lean`, AR4b; Section 6.3 (`sec:direct-fft-twiddle`), Theorem 6.5 (`thm:direct-fft`)):
given any multiplier satisfying `MulBigContract`, the broadcast kernel `cmulBKernel` maps `z`
(width `w1`) and one phase per record `θ` (width `w2`) to `cmulTruncBcast s z θ` (width `w3`),
with cost `(4·Cm + 1000)·(M·mulW (w1 + w2 + 1) + V_z + V_θ + V_out + (M + 1)·(w2 + bitLen s + 1)
+ w1 + w2 + w3)`. The hypotheses `1 ≤ w3`, `BlkTerm rθ` and `CArrFits w3 (cmulTruncBcast s z θ)`
of the statement are not needed by the proof. -/
theorem cmulTruncBcast_holds : CMulTruncBcastStmt := by
  intro hMB
  obtain ⟨Cm, Rm, Pm, hfin, hne, hcl, hspec⟩ := hMB
  haveI := hfin
  haveI := hne
  refine ⟨4 * Cm + 1000, fun _ => ⟨CS ⊕ WP.Top.GW, inferInstance, inferInstance, AReg × Rm,
    cmulBKernel Pm, inferInstance, inferInstance, cmulBKernel_closed hcl, ?_⟩⟩
  intro w1 w2 w3 s z θ rz rθ r3 r4 r5 r6 S hKC hw1 hw2 _ hz1 hθ1 hlen _ hrz _ hr3 hr4 hr5 hr6 h0
    h1 h3 h4 h5 h6
  exact cmulBKernel_runs hspec w1 w2 w3 s z θ rz rθ r3 r4 r5 r6 S hKC hw1 hw2 hz1 hθ1 hlen hrz
    hr3 hr4 hr5 hr6 h0 h1 h3 h4 h5 h6

end SubNLogN.Machine.Arith
