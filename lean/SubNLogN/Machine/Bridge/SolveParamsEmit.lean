/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveParamsStage
import SubNLogN.Machine.Bridge.Kit
import IntMulTM.Framework.Lib.Counter
import IntMulTM.SpecFacts

/-!
# SOL-PARAM-ROWS (4): replication loop

`emitLoop Yk Ak`: copy the record on `Yk` onto `Ak` once per unit of the `natSyms` counter on
`kCC` (counting down to `0`, `BridgeRed.runs_counted_loop`); `runs_emitLoop` gives the exact final
stacks and an explicit cost.

All proved; helpers in `SubNLogN.Machine.Bridge.SolveParamsAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveParamsAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine Computability
open WP.W9comp (runs_seq runs_mono runs_congr)

theorem loopCost_le_mul' (B : ℕ → ℕ) (M : ℕ) :
    ∀ N, (∀ n, n < N → B n ≤ M) → loopCost B N ≤ N * (M + 1) + 1
  | 0, _ => by simp [loopCost]
  | N + 1, h => by
    have ih := loopCost_le_mul' B M N (fun n hn => h n (by omega))
    have h2 := h N (by omega)
    simp only [loopCost]
    nlinarith

theorem bitLen_mono'' {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat, IntMulTM.length_encodeNat]
  exact Nat.size_le_size h

theorem natSyms_eq_map (n : ℕ) : natSyms n = (encodeNat n).map Sym.bit := rfl

/-- One replication step: copy the record, decrement the counter. -/
def emitCore (Yk Ak : SK) : BProg SK := .seq (L (SolveAux.copyRec Yk Ak kTP)) (L (dec kCC kTQ))

/-- Replicate the record on `Yk` onto `Ak`, counter `kCC`. -/
def emitLoop (Yk Ak : SK) : BProg SK :=
  .seq (BridgeRed.peekTop kCC)
    (.loop BridgeRed.topIsBit (.seq (emitCore Yk Ak) (BridgeRed.peekTop kCC)))

theorem runs_emitLoop (Yk Ak : SK)
    (hYA : (Yk = kY0 ∧ Ak = kA0) ∨ (Yk = kY1 ∧ Ak = kA1) ∨ (Yk = kY2 ∧ Ak = kA2))
    (bs : List Bool) (restY : List Sym) (N : ℕ) (S : SK → List Sym)
    (hY : S Yk = recSyms bs ++ restY) (hCC : S kCC = natSyms N) :
    Runs (emitLoop Yk Ak) S
      (Function.update (Function.update S kCC []) Ak
        (SolveAux.recsOf (List.replicate N bs) ++ S Ak))
      (fun _ => True) (N * (7 * bs.length + 6 * bitLen N + 20) + 2) := by
  have a1 : Yk ≠ Ak := by rcases hYA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have a2 : Yk ≠ kTP := by rcases hYA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have a3 : Ak ≠ kTP := by rcases hYA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have a4 : Yk ≠ kCC := by rcases hYA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have a5 : Ak ≠ kCC := by rcases hYA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  let B : ℕ → SK → List Sym := fun n =>
    Function.update (Function.update S kCC (natSyms n)) Ak
      (SolveAux.recsOf (List.replicate (N - n) bs) ++ S Ak)
  let T : ℕ → ℕ := fun n => (7 * bs.length + 8) + (6 * zerosLead (encodeNat (n + 1)) + 8)
  have hk : ∀ n, n ≤ N → B n kCC = natSyms n := by
    intro n _
    simp [B, Function.update_apply, a5.symm]
  have hstep : ∀ n, n + 1 ≤ N → Runs (emitCore Yk Ak) (B (n + 1)) (B n) (fun _ => True) (T n) := by
    intro n hn
    have hYB : B (n + 1) Yk = recSyms bs ++ restY := by
      simp [B, Function.update_apply, a1, a4, hY]
    have h1 := runs_L (K := SK) fun v =>
      ⟨_, SolveAux.copyRec_eval a1 a2 a3 v bs restY (B (n + 1)) hYB⟩
    have hCCB : Function.update (B (n + 1)) Ak (recSyms bs ++ B (n + 1) Ak) kCC =
        (encodeNat (n + 1)).map Sym.bit ++ [] := by
      simp [B, Function.update_apply, a5.symm, natSyms_eq_map]
    have h2 := runs_L (K := SK) fun v =>
      ⟨_, dec_eval (k := kCC) (t := kTQ) (by decide) [] v n []
        (Function.update (B (n + 1)) Ak (recSyms bs ++ B (n + 1) Ak)) termOK_nil hCCB⟩
    refine runs_congr (runs_seq h1 h2) ?_
    funext k
    by_cases k1 : k = Ak
    · subst k1
      have hNn : N - n = (N - (n + 1)) + 1 := by omega
      simp [B, Function.update_apply, a5, hNn, List.replicate_succ, SolveAux.recsOf_cons]
    by_cases k2 : k = kCC
    · subst k2
      simp [B, Function.update_apply, a5.symm, natSyms_eq_map]
    simp [B, Function.update_apply, k1, k2]
  have hL := BridgeRed.runs_counted_loop kCC (emitCore Yk Ak) B N T hk hstep
  have hBN : B N = S := by
    funext k
    by_cases k1 : k = Ak
    · subst k1; simp [B, Function.update_apply, a5]
    by_cases k2 : k = kCC
    · subst k2; simp [B, Function.update_apply, a5.symm, hCC]
    simp [B, Function.update_apply, k1, k2]
  have hB0 : B 0 = Function.update (Function.update S kCC []) Ak
      (SolveAux.recsOf (List.replicate N bs) ++ S Ak) := by
    simp [B, natSyms_eq_map, encodeNat_zero]
  rw [hBN, hB0] at hL
  refine runs_mono hL (fun _ _ => trivial) ?_
  have hT : ∀ n, n < N → T n + 1 ≤ 7 * bs.length + 6 * bitLen N + 17 := by
    intro n hn
    have hz : zerosLead (encodeNat (n + 1)) ≤ bitLen N :=
      le_trans (zerosLead_le_length _) (bitLen_mono'' (by omega))
    simp only [T]
    omega
  have hc := loopCost_le_mul' (fun n => T n + 1) _ N hT
  nlinarith

end SubNLogN.Machine.Bridge.SolveParamsAux
