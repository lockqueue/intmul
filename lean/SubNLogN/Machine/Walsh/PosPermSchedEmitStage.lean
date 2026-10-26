/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedEmitStageDefs

/-!
# Schedule compiler emitter, the stage assembly (`PosPermSchedEmitStage.lean`)

`stageProg_of (hG : GLoopStmt) (hL : LeftPassStmt) : StageProgStmt`: the stage emitter
`stageProgE` (`PosPermSchedEmitStageDefs.lean`) satisfies `StageEmitSpec` with `C = 10^7` and
`k = 9`, given the slice-loop contract `GLoopStmt` and the leftover-pass contract `LeftPassStmt`.

Proof: the entry stacks are the emitter state `st S (vInit m d K) A []` (`st_vInit`). `setup` (nine
generic programs) reaches `st S (vS m d K) A []`, with `J = numChunks m K`, `G = numGroups m K d` and
`JK = J·K` (`runs_setup`). `gLoop` and `lLoop` then append the slice commands and the leftover single
flips (`hG`, `hL`, with `V = 2 (m+d+K+1)^3`), and the teardown clears `J, G, JK`. The accumulator
matches `stageCmds` by `stage_eq`, `leftPairs_stage` and `schedSyms_append_reverse`. The cost bound is
`stage_cost_le`.

**Scope (honest summary).** A reduction: `StageProgStmt` from the contracts `GLoopStmt` and
`LeftPassStmt` (the latter is proved as `leftPass_holds`, `PosPermSchedEmitLeft.lean`). It adds no
new contract.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.Emit

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.Walsh.PosPermSchedAux.PSIO

namespace StageT1

/-- The registers after `setup`: `m, d, K`, `J = numChunks m K`, `G = numGroups m K d`,
`JK = J·K`, all others `0`. -/
def vS (m d K : ℕ) : RegN → ℕ := fun r =>
  match r with
  | .m => m
  | .d => d
  | .K => K
  | .J => numChunks m K
  | .G => numGroups m K d
  | .JK => numChunks m K * K
  | _ => 0

/-- The slice commands of a stage (the effect of `gLoop`, `GLoopStmt`). -/
def sliceL (m d K : ℕ) (stA : Bool) (I : Fin m → Fin m) : List (PosCmd m K) :=
  (List.range (numGroups m K d)).flatMap fun g =>
    (List.finRange K).flatMap fun ρ => sliceCmds m d K g ρ (stPairs stA I)

/-- The leftover single flips of a stage (the effect of `lLoop`, `LeftPassStmt`). -/
def leftL (m K : ℕ) (stA : Bool) (I : Fin m → Fin m) : List (PosCmd m K) :=
  ((List.finRange m).filterMap (fun x => (pairOf stA I x).filter (leftQ K))).map
    (fun p => (PosCmd.one p.1 p.2 : PosCmd m K))

/-- The entry stacks of a stage are the emitter state `st S (vInit m d K) A []`. -/
theorem st_vInit (S : Stk → List Sym) (m d K : ℕ) (A : List Sym)
    (hm : S (rg .m) = una m) (hd : S (rg .d) = una d) (hK : S (rg .K) = una K)
    (hA : S (rs .ACC) = A) (hz : ∀ q, q ≠ .m → q ≠ .d → q ≠ .K → S (rg q) = [])
    (hBT : S (rs .BT) = []) : st S (vInit m d K) A [] = S := by
  funext k
  rcases k with i | w | q
  · rfl
  · cases w <;> first | rfl | exact hA.symm | exact hBT.symm
  · by_cases h1 : q = .m
    · subst h1
      exact hm.symm
    by_cases h2 : q = .d
    · subst h2
      exact hd.symm
    by_cases h3 : q = .K
    · subst h3
      exact hK.symm
    rw [hz q h1 h2 h3]
    cases q <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3

theorem utabLen_le (l : List ℕ) (B : ℕ) (h : ∀ a ∈ l, a + 1 ≤ B) :
    (utab l).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [utab_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    simp only [List.length_append, length_una, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem utabFin_le {m : ℕ} (I : Fin m → Fin m) : (utab (finVals I)).length ≤ m * m := by
  have h := utabLen_le (finVals I) m (fun a ha => by
    simp only [finVals, List.mem_ofFn] at ha
    obtain ⟨p, rfl⟩ := ha
    exact (I p).isLt)
  have hl : (finVals I).length = m := by simp [finVals]
  rwa [hl] at h

section Setup

variable (S : Stk → List Sym) {V : ℕ}

/-- **The stage setup**: `J := m / K`, `G := (J + d - 1) / d`, `JK := J·K` (nine programs). -/
theorem runs_setup (m d K : ℕ) (A : List Sym) (hd : 1 ≤ d) (hK : 1 ≤ K) (hmV : m ≤ V)
    (hdV : d ≤ V) (hKV : K ≤ V) (hq2V : m / K + d - 1 ≤ V) :
    Runs setup (st S (vInit m d K) A []) (st S (vS m d K) A []) (fun _ => True) (9 * opW V) := by
  have hW := one_le_opW V
  have hJV : m / K ≤ V := le_trans (Nat.div_le_self m K) hmV
  have hrV : m % K ≤ V := le_trans (Nat.mod_le m K) hmV
  have hr2V : (m / K + d - 1) % d ≤ V := le_trans (Nat.mod_le _ d) hq2V
  refine runs_weak (runs_seq' (runs_dmR0 S (vInit m d K) A [] .m .K .J .v hmV hKV
      (by show 0 < K; omega) rfl rfl)
    (runs_seq' (runs_clr S _ A [] .v (by exact hrV))
    (runs_seq' (runs_copyR0 S _ A [] .J .q2 (by exact hJV) (by rfl))
    (runs_seq' (runs_copyR S _ A [] .d .q2 (by exact hdV))
    (runs_seq' (runs_dec (V := V) S _ A [] .q2)
    (runs_seq' (runs_dmR0 S _ A [] .q2 .d .G .v (by exact hq2V) (by exact hdV)
        (by show 0 < d; omega) (by rfl) (by rfl))
    (runs_seq' (runs_clr S _ A [] .v (by exact hr2V))
    (runs_seq' (runs_clr S _ A [] .q2 (by exact hq2V))
      (runs_mulR0 S _ A [] .J .K .JK (by exact hJV) (by exact hKV) (by rfl))
      le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
    (st_congr fun r => by cases r <;> rfl) (by omega)

end Setup

/-- The cost of the stage, for `V = 2 (m+d+K+1)^3`, is at most `10^7 (m+d+K+1)^9`. -/
theorem stage_cost_le (m d K : ℕ) :
    9 * opW (2 * (m + d + K + 1) ^ 3) + ((m + d + K + 2) ^ 3 * (100 * opW (2 * (m + d + K + 1) ^ 3)) +
      ((m + 1) * (100 * opW (2 * (m + d + K + 1) ^ 3)) + (opW (2 * (m + d + K + 1) ^ 3) +
        (opW (2 * (m + d + K + 1) ^ 3) + opW (2 * (m + d + K + 1) ^ 3))))) ≤
      10000000 * (m + d + K + 1) ^ 9 := by
  obtain ⟨N, hN⟩ : ∃ N, N = m + d + K + 1 := ⟨_, rfl⟩
  have hP : m + d + K + 2 = N + 1 := by omega
  rw [hP, ← hN]
  have hmN : m + 1 ≤ N := by omega
  have h3 : 1 ≤ N ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hW1 : opW (2 * N ^ 3) ≤ 9000 * N ^ 6 := by
    unfold opW
    have h1 : 2 * N ^ 3 + 1 ≤ 3 * N ^ 3 := by omega
    have h2 : (2 * N ^ 3 + 1) ^ 2 ≤ (3 * N ^ 3) ^ 2 := Nat.pow_le_pow_left h1 2
    have h4 : (3 * N ^ 3) ^ 2 = 9 * N ^ 6 := by ring
    omega
  generalize opW (2 * N ^ 3) = W at hW1 ⊢
  have hP3 : (N + 1) ^ 3 ≤ 8 * N ^ 3 := by
    have h5 : N + 1 ≤ 2 * N := by omega
    calc (N + 1) ^ 3 ≤ (2 * N) ^ 3 := Nat.pow_le_pow_left h5 3
      _ = 8 * N ^ 3 := by ring
  have hN3 : N ≤ N ^ 3 := Nat.le_self_pow (by norm_num) N
  have e1 : (N + 1) ^ 3 * (100 * W) ≤ 8 * N ^ 3 * (100 * W) := Nat.mul_le_mul_right _ hP3
  have e2 : (m + 1) * (100 * W) ≤ N ^ 3 * (100 * W) :=
    Nat.mul_le_mul_right _ (le_trans hmN hN3)
  have e3 : W ≤ N ^ 3 * W := by
    calc W = 1 * W := (Nat.one_mul W).symm
      _ ≤ N ^ 3 * W := Nat.mul_le_mul_right _ h3
  have e4 : N ^ 3 * W ≤ N ^ 3 * (9000 * N ^ 6) := Nat.mul_le_mul_left _ hW1
  have r1 : 8 * N ^ 3 * (100 * W) = 800 * (N ^ 3 * W) := by ring
  have r2 : N ^ 3 * (100 * W) = 100 * (N ^ 3 * W) := by ring
  have r3 : N ^ 3 * (9000 * N ^ 6) = 9000 * N ^ 9 := by ring
  omega

end StageT1

open StageT1 in
/-- **The stage emitter `stageProgE` meets `StageEmitSpec`** (constants `C = 10^7`, `k = 9`),
given the slice-loop contract `GLoopStmt` and the leftover-pass contract `LeftPassStmt`. -/
theorem stageProg_of (hG : GLoopStmt) (hL : LeftPassStmt) : StageProgStmt := by
  unfold StageProgStmt
  refine ⟨stageProgE, closed_stageProgE, ?_⟩
  unfold StageEmitSpec
  refine ⟨10000000, 9, ?_⟩
  intro IT hIT stA m d K I S A hd hK hT hm hdd hKK hA hz hBT hU hB1 _hB2 _hB3 _hB4
  obtain ⟨V, hVdef⟩ : ∃ V, V = 2 * (m + d + K + 1) ^ 3 := ⟨_, rfl⟩
  have hN3 : m + d + K + 1 ≤ V := by
    have h := Nat.le_self_pow (n := 3) (by norm_num) (m + d + K + 1)
    omega
  have hLm : (utab (finVals I)).length ≤ V := by
    have h1 := utabFin_le I
    have h2 : m * m ≤ (m + d + K + 1) ^ 3 := by
      calc m * m ≤ (m + d + K + 1) * (m + d + K + 1) := Nat.mul_le_mul (by omega) (by omega)
        _ = (m + d + K + 1) ^ 2 := (sq _).symm
        _ ≤ (m + d + K + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have hJV : m / K ≤ V := by have := Nat.div_le_self m K; omega
  have hJKV : m / K * K ≤ V := by have := Nat.div_mul_le_self m K; omega
  have hq2V : m / K + d - 1 ≤ V := by have := Nat.div_le_self m K; omega
  have hGV : (m / K + d - 1) / d ≤ V := by have := Nat.div_le_self (m / K + d - 1) d; omega
  have hS := st_vInit S m d K A hm hdd hKK hA hz hBT
  rw [← hS, st_upd_acc]
  have s1 := runs_setup S m d K A hd hK (by omega : m ≤ V) (by omega : d ≤ V) (by omega : K ≤ V)
    hq2V
  have s2 : Runs (gLoop IT stA) (st S (vS m d K) A [])
      (st S (vS m d K) ((schedSyms (sliceL m d K stA I)).reverse ++ A) []) (fun _ => True)
      ((m + d + K + 2) ^ 3 * (100 * opW V)) :=
    hG S IT hIT m d K I stA (vS m d K) A V hT hU hB1 hd hK rfl rfl rfl rfl rfl
      (fun q h1 h2 h3 h4 h5 h6 => by
        cases q <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2 |
          exact absurd rfl h3 | exact absurd rfl h4 | exact absurd rfl h5 | exact absurd rfl h6)
      (by omega) hLm
  have hlz : ∀ X : List Sym, st S (lz (vS m d K)) X [] = st S (vS m d K) X [] :=
    fun X => st_congr fun r => by cases r <;> rfl
  have s3 : Runs (lLoop IT stA) (st S (vS m d K) ((schedSyms (sliceL m d K stA I)).reverse ++ A) [])
      (st S (vS m d K) ((schedSyms (leftL m K stA I)).reverse ++
        ((schedSyms (sliceL m d K stA I)).reverse ++ A)) []) (fun _ => True)
      ((m + 1) * (100 * opW V)) := by
    have h := hL S IT hIT m I stA (vS m d K) ((schedSyms (sliceL m d K stA I)).reverse ++ A) V
      hT hU hB1 rfl (by show 0 < K; omega) rfl (by omega) (by omega) hLm (by exact hJKV)
    simp only [hlz] at h
    exact h
  have hacc : (schedSyms (stageCmds m d K (if stA then stageA I else stageB I))).reverse ++ A =
      (schedSyms (leftL m K stA I)).reverse ++ ((schedSyms (sliceL m d K stA I)).reverse ++ A) := by
    rw [stage_eq, stageCmds, schedSyms_append_reverse, leftPairs_stage, List.append_assoc]
    all_goals rfl
  rw [hacc]
  refine runs_weak (runs_seq' s1 (runs_seq' s2 (runs_seq' s3
    (runs_seq' (runs_clr S _ _ [] .J (by exact hJV))
      (runs_seq' (runs_clr S _ _ [] .G (by exact hGV))
        (runs_clr S _ _ [] .JK (by exact hJKV)) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl)
    (st_congr fun r => by cases r <;> rfl) ?_
  subst hVdef
  exact stage_cost_le m d K

end SubNLogN.Machine.Walsh.PosPermSchedAux.Emit
