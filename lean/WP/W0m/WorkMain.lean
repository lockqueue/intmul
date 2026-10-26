import WP.W0m.PhasesB

/-!
# WP.W0m.WorkMain — the whole work program: exact final stacks and cost

`workProg_runs`: from `S0 a b` (the copied-in input on `inp`, everything else empty), the work
program reaches exactly `outW a b`. With `n = operandBits a b`, that state holds:
* `oa = a`, `ob = b`, `nn = n`;
* `bb = sB n`, `kk = sK n`, `k0 = sK0 n`, `lf = sL n`, `p0 = sP0 n`;
* every other stack empty.

The cost is at most `workCost Ca Cd a b`: linear in the operand lengths, plus `O(Λ²)` with
`Λ = bitLen (18·(L+1)) = O(log L)`. Here `Ca`, `Cd` are the adder and divider contract constants.
-/

namespace WP.W0m

open Computability TMFw TMFw.Lib TMFw.Contracts

/-- Initial work stacks: the copied-in input on `inp`. -/
def S0 (a b : ℕ) : Stk → List Sym := Function.update (fun _ => []) .inp (inputSyms a b)

/-- Final work stacks. -/
def outW (a b : ℕ) : Stk → List Sym := fun x =>
  match x with
  | .oa => natSyms a
  | .ob => natSyms b
  | .nn => natSyms (IntMulTM.operandBits a b)
  | .bb => natSyms (sB (IntMulTM.operandBits a b))
  | .kk => natSyms (sK (IntMulTM.operandBits a b))
  | .k0 => natSyms (sK0 (IntMulTM.operandBits a b))
  | .lf => natSyms (sL (IntMulTM.operandBits a b))
  | .p0 => natSyms (sP0 (IntMulTM.operandBits a b))
  | _ => []

/-- Input length `|encNatPair (a, b)| = |bits a| + |bits b| + 1`. -/
def inLen (a b : ℕ) : ℕ := bitLen a + bitLen b + 1

/-- Common bound on the bit lengths of all schedule values. -/
def lam (a b : ℕ) : ℕ := bitLen (18 * (inLen a b + 1))

/-- Cost bound of the work program. -/
def workCost (Ca Cd a b : ℕ) : ℕ :=
  27 * (bitLen a + bitLen b) + 300 * lam a b + 400 + Cd * ((lam a b + 1) * (lam a b + 1)) +
    Ca * (4 * lam a b + 2)

theorem workProg_runs {ma md Ca Cd : ℕ} {Ra Rd : Type} {Padd : Prog (Loc 3 ma) (fun _ => Sym) Ra}
    {Pdiv : Prog (Loc 4 md) (fun _ => Sym) Rd} (hA : AddSpec Padd Ca) (hD : DivSpec Pdiv Cd)
    (hma : ma ≤ 6) (hmd : md ≤ 6) (a b : ℕ) :
    Runs (workProg Padd hma Pdiv hmd) (S0 a b) (outW a b) (fun _ => True) (workCost Ca Cd a b) := by
  set n := IntMulTM.operandBits a b with hn
  set Λ := lam a b with hΛ
  -- value bounds
  have hn1 : 1 ≤ n := operandBits_pos a b
  have hn0 : n ≠ 0 := by omega
  have hnL : n ≤ inLen a b := by
    rw [hn, operandBits_eq]
    unfold inLen
    omega
  have hmono : ∀ v, v ≤ 18 * (inLen a b + 1) → bitLen v ≤ Λ := fun v hv => bitLen_mono hv
  have hla : bitLen (bitLen a) ≤ Λ := hmono _ (by unfold inLen; omega)
  have hlb : bitLen (bitLen b) ≤ Λ := hmono _ (by unfold inLen; omega)
  have hbn : bitLen n ≤ Λ := hmono _ (by omega)
  have hsB : bitLen (sB n) ≤ Λ := hmono _ (by have := sB_le hn1; omega)
  have hsK : bitLen (sK n) ≤ Λ := hmono _ (by have := sK_le n; omega)
  have hsK0 : bitLen (sK0 n) ≤ Λ := hmono _ (by have := sK0_le n; omega)
  have hsum : bitLen (sB n + sK0 n + 3) ≤ Λ :=
    hmono _ (by have := sB_le hn1; have := sK0_le n; omega)
  -- phase A
  have pA := phA_runs (Ra := Ra) (Rd := Rd) (S0 a b) a b (by simp [S0]) (by simp [S0])
    (by simp [S0])
  set S1 := Function.update (Function.update (Function.update (S0 a b) .inp []) .ob (natSyms b))
    .oa (natSyms a) with hS1
  -- phase B
  have pB := phB_runs (Ra := Ra) (Rd := Rd) S1 a b (by simp [hS1]) (by simp [hS1])
    (by simp [hS1, S0]) (by simp [hS1, S0])
  set S2 := Function.update (Function.update S1 .la (natSyms (bitLen a))) .lb (natSyms (bitLen b))
    with hS2
  -- phase C
  have pC := phC_runs (Ra := Ra) (Rd := Rd) S2 (bitLen a) (bitLen b) (by simp [hS2])
    (by simp [hS2]) (by simp [hS2, hS1, S0]) Λ hla hlb
  set S3 := Function.update (Function.update (Function.update S2 .nn (natSyms n)) .la []) .lb []
    with hS3
  have pC' : Runs (phC : WProg Ra Rd) S2 S3 (fun _ => True) (40 * Λ + 50) := runs_post pC rfl le_rfl
  -- phase D
  have pD := phD_runs (Ra := Ra) (Rd := Rd) S3 n hn0 (by simp [hS3])
    (by simp [hS3, hS2, hS1, S0]) Λ hbn
  set S4 := Function.update S3 .bb (natSyms (sB n)) with hS4
  -- phase E
  have pE := phE_runs (Ra := Ra) hD hmd S4 n (sB n) (by have := sB_pos n; omega) (by simp [hS4, hS3])
    (by simp [hS4]) (by simp [hS4, hS3, hS2, hS1, S0]) (by simp [hS4, hS3, hS2, hS1, S0]) Λ hbn hsB
  set S5 := Function.update S4 .kk (natSyms (sK n)) with hS5
  have pE' : Runs (phE Pdiv hmd : WProg Ra Rd) S4 S5 (fun _ => True)
      (Cd * ((Λ + 1) * (Λ + 1)) + 8 * Λ + 14) := runs_post pE rfl le_rfl
  -- phase F
  have pF := phF_runs (Ra := Ra) (Rd := Rd) S5 (sK n) (by simp [hS5])
    (by simp [hS5, hS4, hS3, hS2, hS1, S0]) (by simp [hS5, hS4, hS3, hS2, hS1, S0]) Λ hsK
  set S6 := Function.update S5 .k0 (natSyms (sK0 n)) with hS6
  have pF' : Runs (phF : WProg Ra Rd) S5 S6 (fun _ => True) (100 * Λ + 150) :=
    runs_post pF (by rw [hS6, sK0_eq]) le_rfl
  -- phase G
  have pG := phG_runs (Ra := Ra) (Rd := Rd) S6 (sK0 n) (sK0_ge n) (by simp [hS6])
    (by simp [hS6, hS5, hS4, hS3, hS2, hS1, S0]) (by simp [hS6, hS5, hS4, hS3, hS2, hS1, S0]) Λ hsK0
  set S7 := Function.update S6 .lf (natSyms (sL n)) with hS7
  have pG' : Runs (phG : WProg Ra Rd) S6 S7 (fun _ => True) (60 * Λ + 50) :=
    runs_post pG (by rw [hS7, sL_eq, Nat.add_sub_cancel]) le_rfl
  -- phase H
  have pH := phH_runs (Rd := Rd) hA hma S7 (sB n) (sK0 n) (by simp [hS7, hS6, hS5, hS4])
    (by simp [hS7, hS6]) (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, S0])
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, S0]) (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, S0])
    Λ hsum
  -- compose
  refine runs_post (runs_seq pA (runs_seq pB (runs_seq pC' (runs_seq pD (runs_seq pE'
    (runs_seq pF' (runs_seq pG' pH))))))) ?_ ?_
  · funext x
    cases x <;> simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, S0, outW, sP0, hn]
  · simp only [workCost, ← hΛ]
    omega

#assert_std_axioms workProg_runs

end WP.W0m
