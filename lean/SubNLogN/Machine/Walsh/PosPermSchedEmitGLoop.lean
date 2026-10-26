/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedEmitLoopDefs
import SubNLogN.Machine.Walsh.PosPermSchedEmitBlk

/-!
# Schedule compiler emitter, the group and slice loops (`PosPermSchedEmitGLoop.lean`)

Proof of the reduction `gLoop_of : RhoBodyStmt → GLoopStmt` (`PosPermSchedEmitLoopDefs.lean`):
* `runs_rhoLoop`: the `ρ` loop of one group (counter `rc`), from `RhoBodyStmt`;
* `runs_gBody`: one group (`gSetup_holds`, the `ρ` loop, the clears, `g := g + 1`);
* `gLoop_of`: the group loop (counter `gc`).
The accumulator after the first `j` slices of a group is `accR`, after the first `i` groups `accG`
(`finRange_take_flatMap_succ`, `range_flatMap_succ` of `PosPermSchedEmitMath.lean`).

**Scope (honest summary).** Proved: `gLoop_of`; its only hypothesis is `RhoBodyStmt`.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.EmitGL

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.Walsh.PosPermSchedAux SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

/-- A run with both endpoints rewritten. -/
theorem runs_congr' {P : SProg Stk} {S1 S1' S2 S2' : Stk → List Sym} {T T' : ℕ}
    (h : Runs P S1 S2 (fun _ => True) T) (e1 : S1 = S1') (e2 : S2 = S2') (hT : T ≤ T') :
    Runs P S1' S2' (fun _ => True) T' := by
  subst e1
  exact runs_weak h e2 hT

/-- Equal valuations and accumulators give equal states. -/
theorem st_congr2 {S₀ : Stk → List Sym} {w₁ w₂ : RegN → ℕ} {a₁ a₂ bt : List Sym}
    (h : ∀ r, w₁ r = w₂ r) (ha : a₁ = a₂) : st S₀ w₁ a₁ bt = st S₀ w₂ a₂ bt := by
  rw [funext h, ha]

/-- The accumulator after the first `j` slices of group `g`. -/
def accR {m : ℕ} (d K g : ℕ) (P : List (Fin m × Fin m)) (A : List Sym) (j : ℕ) : List Sym :=
  (schedSyms (((List.finRange K).take j).flatMap fun ρ => sliceCmds m d K g ρ P)).reverse ++ A

theorem accR_zero {m : ℕ} (d K g : ℕ) (P : List (Fin m × Fin m)) (A : List Sym) :
    accR d K g P A 0 = A := by
  simp [accR, PSIO.schedSyms_nil]

theorem accR_succ {m : ℕ} (d K g : ℕ) (P : List (Fin m × Fin m)) (A : List Sym) {j : ℕ}
    (hj : j < K) :
    accR d K g P A (j + 1) =
      (schedSyms (sliceCmds m d K g ⟨j, hj⟩ P)).reverse ++ accR d K g P A j := by
  simp only [accR, finRange_take_flatMap_succ _ hj, PSIO.schedSyms_append_reverse,
    List.append_assoc]

theorem accR_K {m : ℕ} (d K g : ℕ) (P : List (Fin m × Fin m)) (A : List Sym) :
    accR d K g P A K =
      (schedSyms ((List.finRange K).flatMap fun ρ => sliceCmds m d K g ρ P)).reverse ++ A := by
  simp only [accR, finRange_take_self]

/-- The accumulator after the first `i` groups. -/
def accG {m : ℕ} (d K : ℕ) (P : List (Fin m × Fin m)) (A : List Sym) (i : ℕ) : List Sym :=
  (schedSyms ((List.range i).flatMap fun g =>
    (List.finRange K).flatMap fun ρ => sliceCmds m d K g ρ P)).reverse ++ A

theorem accG_zero {m : ℕ} (d K : ℕ) (P : List (Fin m × Fin m)) (A : List Sym) :
    accG d K P A 0 = A := by
  simp [accG, PSIO.schedSyms_nil]

theorem accG_succ {m : ℕ} (d K : ℕ) (P : List (Fin m × Fin m)) (A : List Sym) (i : ℕ) :
    accG d K P A (i + 1) =
      (schedSyms ((List.finRange K).flatMap fun ρ => sliceCmds m d K i ρ P)).reverse ++
        accG d K P A i := by
  simp only [accG, range_flatMap_succ, PSIO.schedSyms_append_reverse, List.append_assoc]

/-! ## The `ρ` loop of one group -/

theorem runs_rhoLoop (hR : RhoBodyStmt) (S₀ : Stk → List Sym) (IT : RawN)
    (hIT : IT = .I0T ∨ IT = .I1T) (m d K g : ℕ) (I : Fin m → Fin m) (stA : Bool)
    (w0 : RegN → ℕ) (A : List Sym) (V : ℕ)
    (hT : S₀ (rs IT) = utab (finVals I)) (hU : S₀ (rs .U) = []) (hB1 : S₀ (rs .B1) = [])
    (hm : w0 .m = m) (hK : w0 .K = K) (hj0 : w0 .j0 = groupStart K d g)
    (hD : w0 .D = groupSize m K d g)
    (hq4 : w0 .q4 = groupStart K d g + groupSize m K d g * K)
    (hnS : w0 .nS = m - groupStart K d g - groupSize m K d g * K)
    (hz : ∀ q : RegN, (q = .hi ∨ q = .cnt ∨ q = .x ∨ q = .y ∨ q = .f ∨ q = .c ∨ q = .t ∨
      q = .e0 ∨ q = .e1 ∨ q = .q7 ∨ q = .q8 ∨ q = .v ∨ q = .fnd ∨ q = .b) → w0 q = 0)
    (hV1 : 1 ≤ V) (hmV : m ≤ V) (hKV : K ≤ V) (hL : (utab (finVals I)).length ≤ V)
    (hj0V : w0 .j0 ≤ V) (hq4V : w0 .q4 ≤ V) (hDV : w0 .D ≤ V) (hnSV : w0 .nS ≤ V)
    (hmm : (m + 1) * (2 * m + 2) ≤ V) :
    Runs (loopR .rc (rhoBody IT stA))
      (st S₀ (Function.update (Function.update w0 .rho 0) .rc K) A [])
      (st S₀ (Function.update (Function.update w0 .rho K) .rc 0)
        (accR d K g (stPairs stA I) A K) [])
      (fun _ => True) (K * ((m + 2) * (50 * opW V) + 3) + 2) := by
  have h := runs_loopR S₀ .rc rfl (fun ρ => Function.update w0 .rho ρ)
    (fun ρ => accR d K g (stPairs stA I) A ρ) (fun _ => []) ((m + 2) * (50 * opW V)) K
    (fun ρ hρ => runs_congr'
      (hR S₀ IT hIT m d K g I stA (Function.update w0 .rc (K - 1 - ρ))
        (accR d K g (stPairs stA I) A ρ) V ρ hρ hT hU hB1 hm hK hj0 hD hq4 hnS hV1 hmV hKV hL
        hj0V hq4V hDV hnSV hmm)
      (st_congr (fun r => by
        cases r <;> first | rfl | exact (hz _ (by decide)).symm))
      (st_congr2 (fun r => by
        cases r <;> first | rfl | exact (hz _ (by decide)).symm)
        (accR_succ d K g (stPairs stA I) A hρ).symm)
      le_rfl)
  simp only [accR_zero] at h
  exact h

/-! ## One group -/

theorem runs_gBody (hR : RhoBodyStmt) (S₀ : Stk → List Sym) (IT : RawN)
    (hIT : IT = .I0T ∨ IT = .I1T) (m d K : ℕ) (I : Fin m → Fin m) (stA : Bool)
    (u : RegN → ℕ) (A : List Sym) (V i : ℕ)
    (hT : S₀ (rs IT) = utab (finVals I)) (hU : S₀ (rs .U) = []) (hB1 : S₀ (rs .B1) = [])
    (hd : 1 ≤ d) (hK : 1 ≤ K) (hum : u .m = m) (hud : u .d = d) (huK : u .K = K)
    (huJ : u .J = numChunks m K) (hug : u .g = i) (hi : i < numGroups m K d)
    (hz : ∀ q : RegN, q ≠ .m → q ≠ .d → q ≠ .K → q ≠ .J → q ≠ .G → q ≠ .JK → q ≠ .g →
      q ≠ .gc → u q = 0)
    (hV : 2 * (m + d + K + 1) ^ 3 ≤ V) (hL : (utab (finVals I)).length ≤ V) :
    Runs (gBody IT stA) (st S₀ u A [])
      (st S₀ (Function.update u .g (i + 1))
        ((schedSyms ((List.finRange K).flatMap fun ρ =>
          sliceCmds m d K i ρ (stPairs stA I))).reverse ++ A) [])
      (fun _ => True) (38 * opW V + (K * ((m + 2) * (50 * opW V) + 3) + 2)) := by
  have hz' : ∀ q : RegN, (q ≠ .m ∧ q ≠ .d ∧ q ≠ .K ∧ q ≠ .J ∧ q ≠ .G ∧ q ≠ .JK ∧ q ≠ .g ∧
      q ≠ .gc) → u q = 0 := fun q h =>
    hz q h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2
  -- arithmetic
  obtain ⟨N, hN⟩ : ∃ N, N = m + d + K + 1 := ⟨_, rfl⟩
  rw [← hN] at hV
  have hN1 : 1 ≤ N := by omega
  have hNle : N ≤ N * N := by have := Nat.mul_le_mul (le_refl N) hN1; omega
  have hNNle : N * N ≤ N * (N * N) := Nat.mul_le_mul (le_refl N) hNle
  have hV3 : 2 * (N * (N * N)) ≤ V := by
    have e : N ^ 3 = N * (N * N) := by ring
    omega
  have hV1 : 1 ≤ V := by omega
  have hmV : m ≤ V := by omega
  have hdV : d ≤ V := by omega
  have hKV : K ≤ V := by omega
  have hJm : numChunks m K ≤ m := Nat.div_le_self m K
  have hJK : numChunks m K * K ≤ m := Nat.div_mul_le_self m K
  have hid : i * d < numChunks m K := (PosPermAux.lt_numGroups_iff hd).1 hi
  have hGle : numGroups m K d ≤ m + d := by
    unfold numGroups
    have := Nat.div_le_self (numChunks m K + d - 1) d
    omega
  have hidK : i * d * K ≤ numChunks m K * K := Nat.mul_le_mul (le_of_lt hid) (le_refl K)
  have hDd : min d (numChunks m K - i * d) ≤ d := min_le_left _ _
  have hDJ : min d (numChunks m K - i * d) ≤ numChunks m K - i * d := min_le_right _ _
  have hq4m : i * d * K + min d (numChunks m K - i * d) * K ≤ m := by
    have h1 : (i * d + min d (numChunks m K - i * d)) * K ≤ numChunks m K * K :=
      Nat.mul_le_mul (by omega) (le_refl K)
    have e : (i * d + min d (numChunks m K - i * d)) * K =
        i * d * K + min d (numChunks m K - i * d) * K := by ring
    omega
  have hdK : d * K ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
  have hmm : (m + 1) * (2 * m + 2) ≤ V := by
    have h1 : (m + 1) * (m + 1) ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
    have e : (m + 1) * (2 * m + 2) = 2 * ((m + 1) * (m + 1)) := by ring
    omega
  have hj0V : u .g * u .d * u .K ≤ V := by rw [hug, hud, huK]; omega
  have hDV : min (u .d) (u .J - u .g * u .d) ≤ V := by rw [hug, hud, huJ]; omega
  have hDKV : min (u .d) (u .J - u .g * u .d) * u .K ≤ V := by
    rw [hug, hud, huJ, huK]; omega
  have hq4V : u .g * u .d * u .K + min (u .d) (u .J - u .g * u .d) * u .K ≤ V := by
    rw [hug, hud, huJ, huK]; omega
  have hnSV : u .m - u .g * u .d * u .K - min (u .d) (u .J - u .g * u .d) * u .K ≤ V := by
    rw [hum]; omega
  -- the steps
  have hS := gSetup_holds S₀ u A V (hz' .q2 (by decide)) (hz' .q3 (by decide))
    (hz' .q5 (by decide)) (hz' .f (by decide)) (hz' .j0 (by decide)) (hz' .D (by decide))
    (hz' .DK (by decide)) (hz' .q4 (by decide)) (hz' .nS (by decide)) (by omega) (by omega)
    hV1 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hug, hud, huK]; omega)
  have hC := runs_copyR0 S₀ (gVals u) A [] (V := V) .K .rc (show u .K ≤ V by omega)
    (hz' .rc (by decide))
  have hLp := runs_rhoLoop hR S₀ IT hIT m d K i I stA (gVals u) A V hT hU hB1 hum huK
    (by show u .g * u .d * u .K = i * d * K; rw [hug, hud, huK])
    (by show min (u .d) (u .J - u .g * u .d) = min d (numChunks m K - i * d); rw [hud, huJ, hug])
    (by
      show u .g * u .d * u .K + min (u .d) (u .J - u .g * u .d) * u .K =
        i * d * K + min d (numChunks m K - i * d) * K
      rw [hug, hud, huK, huJ])
    (by
      show u .m - u .g * u .d * u .K - min (u .d) (u .J - u .g * u .d) * u .K =
        m - i * d * K - min d (numChunks m K - i * d) * K
      rw [hum, hug, hud, huK, huJ])
    (fun q hq => by
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> exact hz' _ (by decide))
    hV1 hmV hKV hL hj0V hq4V hDV hnSV hmm
  refine runs_weak (runs_seq' hS (runs_seq' (runs_congr' hC rfl
      (st_congr (fun r => by cases r <;> first | rfl | exact huK | exact hz' _ (by decide)))
      le_rfl)
    (runs_seq' hLp
    (runs_seq' (runs_clr S₀ _ _ [] .rho hKV)
    (runs_seq' (runs_clr S₀ _ _ [] .j0 hj0V)
    (runs_seq' (runs_clr S₀ _ _ [] .D hDV)
    (runs_seq' (runs_clr S₀ _ _ [] .DK hDKV)
    (runs_seq' (runs_clr S₀ _ _ [] .q4 hq4V)
    (runs_seq' (runs_clr S₀ _ _ [] .nS hnSV)
      (runs_inc (V := V) S₀ _ _ [] .g) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
      le_rfl) le_rfl)
    (st_congr2 (fun r => by
      cases r <;> first | rfl | exact congrArg (· + 1) hug | exact (hz' _ (by decide)).symm)
      (accR_K d K i (stPairs stA I) A))
    (by omega)

end SubNLogN.Machine.Walsh.PosPermSchedAux.EmitGL

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.Walsh.PosPermSchedAux.EmitGL

/-- **[PROVED] All groups of a stage from one slice** (`GLoopStmt` from `RhoBodyStmt`,
`PosPermSchedEmitLoopDefs.lean`). -/
theorem gLoop_of (hR : RhoBodyStmt) : GLoopStmt := by
  intro S₀ IT hIT m d K I stA v acc V hT hU hB1 hd hK hvm hvd hvK hvJ hvG hv0 hV hL
  have hv0' : ∀ q : RegN, (q ≠ .m ∧ q ≠ .d ∧ q ≠ .K ∧ q ≠ .J ∧ q ≠ .G ∧ q ≠ .JK) → v q = 0 :=
    fun q h => hv0 q h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  have hN3 : m + d + K + 1 ≤ (m + d + K + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hGle : numGroups m K d ≤ m + d := by
    unfold numGroups
    have := Nat.div_le_self (numChunks m K + d - 1) d
    have := Nat.div_le_self m K
    unfold numChunks at *
    omega
  have hnV : numGroups m K d ≤ V := by omega
  have hloop := runs_loopR S₀ .gc rfl (fun i => Function.update v .g i)
    (fun i => accG d K (stPairs stA I) acc i) (fun _ => [])
    (38 * opW V + (K * ((m + 2) * (50 * opW V) + 3) + 2)) (numGroups m K d)
    (fun i hi => runs_congr'
      (runs_gBody hR S₀ IT hIT m d K I stA
        (Function.update (Function.update v .g i) .gc (numGroups m K d - 1 - i))
        (accG d K (stPairs stA I) acc i) V i hT hU hB1 hd hK hvm hvd hvK hvJ rfl hi
        (fun q h1 h2 h3 h4 h5 h6 h7 h8 => by
          rw [Function.update_of_ne h8, Function.update_of_ne h7]
          exact hv0 q h1 h2 h3 h4 h5 h6)
        hV hL)
      rfl
      (st_congr2 (fun r => by cases r <;> rfl) (accG_succ d K (stPairs stA I) acc i).symm)
      le_rfl)
  simp only [accG_zero] at hloop
  have hc := runs_copyR0 S₀ v acc [] (V := V) .G .gc (by omega) (hv0' .gc (by decide))
  refine runs_weak (runs_seq' (runs_congr' hc rfl (st_congr (fun r => by
      cases r <;> first | rfl | exact hvG | exact hv0' _ (by decide))) le_rfl)
    (runs_seq' hloop (runs_clr S₀ _ _ [] .g hnV) le_rfl) le_rfl)
    (st_congr2 (fun r => by cases r <;> first | rfl | exact (hv0' _ (by decide)).symm) rfl) ?_
  have hW := one_le_opW V
  generalize opW V = W at hW ⊢
  have hA : 38 * W + (K * ((m + 2) * (50 * W) + 3) + 2) + 3 ≤ (K + 1) * ((m + 2) * (60 * W)) := by
    have e1 : K * ((m + 2) * (50 * W) + 3) = 50 * (K * ((m + 2) * W)) + 3 * K := by ring
    have e2 : (K + 1) * ((m + 2) * (60 * W)) =
        60 * (K * ((m + 2) * W)) + 60 * ((m + 2) * W) := by ring
    have h5 : 1 * 1 ≤ (m + 2) * W := Nat.mul_le_mul (by omega) hW
    have h3 : K * 1 ≤ K * ((m + 2) * W) := Nat.mul_le_mul (le_refl K) (by omega)
    have h4 : 2 * W ≤ (m + 2) * W := Nat.mul_le_mul (by omega) (le_refl W)
    rw [e1, e2]
    omega
  have hB : numGroups m K d * (38 * W + (K * ((m + 2) * (50 * W) + 3) + 2) + 3) ≤
      (m + d + K + 2) * ((m + d + K + 2) * ((m + d + K + 2) * (60 * W))) :=
    Nat.mul_le_mul (by omega)
      (le_trans hA (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (le_refl _))))
  have e3 : (m + d + K + 2) ^ 3 * (100 * W) =
      100 * ((m + d + K + 2) * ((m + d + K + 2) * ((m + d + K + 2) * W))) := by ring
  have e4 : (m + d + K + 2) * ((m + d + K + 2) * ((m + d + K + 2) * (60 * W))) =
      60 * ((m + d + K + 2) * ((m + d + K + 2) * ((m + d + K + 2) * W))) := by ring
  have h6 : 1 * (1 * (1 * W)) ≤ (m + d + K + 2) * ((m + d + K + 2) * ((m + d + K + 2) * W)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (le_refl W)))
  rw [e3]
  omega

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit
