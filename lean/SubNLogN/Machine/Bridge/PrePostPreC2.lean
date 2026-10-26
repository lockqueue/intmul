/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostPost
import SubNLogN.Machine.Bridge.PreScaleVal

/-!
# K5 pre-scaling: the `⌊(lg D + 1)/2⌋` block (`Bridge/PrePostPreC2.lean`)

`c2Block NK NC U` turns `natSyms k` on `NK` into `natSyms (max ((k+1)/2) 1)` on `NC` (for
`k = Σ_{i≥1} lg t_i` this is `⌊(lg D + 1)/2⌋` of `preScaleExp`, Section 4.4 (`sec:bridge-alg`), step (1), since
`lg D = max k 1`): copy, increment, drop the lowest bit (`(natSyms m).tail = natSyms (m/2)`), and
increment once more if the result is `0`.

**Scope (honest summary).** Proved, no `sorry`: `runs_popR'`, `runs_skip'`, `runs_c2Block`.
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability

section C2

variable {K : Type}

/-- `NC := max ((NK + 1) / 2) 1`. -/
def c2Block (NK NC U : K) : SProg K :=
  .seq (copyBlock NK NC U) (.seq (inc NC U) (.seq (popR NC)
    (.seq (peekR NC) (.ite optIsBit skip (inc NC U)))))

theorem closed_c2Block (NK NC U : K) : (c2Block NK NC U).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, c2Block, copyBlock, moveBlock, moveBits, moveBitsBody,
    moveBitsDup, dupBody, restoreR, popR, pushR, pushC, skip, inc, incFix, scanLoop, scanBody,
    peekR]

variable [DecidableEq K]

theorem runs_popR' {k : K} (a : Sym) (L : List Sym) (S : K → List Sym) (hS : S k = a :: L) :
    Runs (popR k) S (Function.update S k L) (fun _ => True) 1 := by
  refine Runs.of_eval fun v => ⟨some a, 1, ?_, trivial, le_refl _⟩
  refine (Eval.pop [] k (fun _ o => o) v S).of_eq ?_ rfl
  rw [hS]
  rfl

theorem runs_skip' (S : K → List Sym) : Runs (skip : SProg K) S S (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, skip_eval [] _, trivial, le_refl _⟩

theorem natSyms_succ_ne_nil (k : ℕ) : natSyms (k + 1) ≠ [] := by
  unfold natSyms
  rw [ne_eq, List.map_eq_nil_iff, encodeNat_eq_nil_iff]
  omega

theorem runs_c2Block {NK NC U : K} (h1 : NK ≠ NC) (h2 : NK ≠ U) (h3 : NC ≠ U) (k : ℕ)
    (RK : List Sym) (S : K → List Sym) (hRK : TermOK RK) (hK : S NK = natSyms k ++ RK)
    (hC : S NC = []) :
    Runs (c2Block NK NC U) S (Function.update S NC (natSyms (max ((k + 1) / 2) 1) ++ []))
      (fun _ => True) (20 * bitLen k + 40) := by
  have hbk : (encodeNat k).length = bitLen k := rfl
  have hb0 : bitLen 0 = 0 := by simp [bitLen, encodeNat_zero]
  have r1 := runs_copyBlock h1 h2 h3 (encodeNat k) RK S hRK hK
  rw [hC] at r1
  have r2 := runs_inc h3 k [] (Function.update S NC ((encodeNat k).map Sym.bit ++ []))
    TermOK.nil (by rw [Function.update_self]; rfl)
  rw [Function.update_idem] at r2
  obtain ⟨a, L, haL⟩ : ∃ a L, natSyms (k + 1) = a :: L := by
    rcases h : natSyms (k + 1) with _ | ⟨a, L⟩
    · exact absurd h (natSyms_succ_ne_nil k)
    · exact ⟨a, L, rfl⟩
  have hL : L = natSyms ((k + 1) / 2) ++ [] := by
    rw [List.append_nil, ← BridgePSH.natSyms_tail, haL]
    rfl
  have r3 := runs_popR' (k := NC) a L (Function.update S NC (natSyms (k + 1) ++ []))
    (by rw [Function.update_self, haL, List.append_nil])
  rw [Function.update_idem, hL] at r3
  set S3 := Function.update S NC (natSyms ((k + 1) / 2) ++ []) with hS3
  have hb3 : optIsBit (S3 NC).head? = decide ((k + 1) / 2 ≠ 0) := by
    rw [hS3, Function.update_self]
    exact optIsBit_natSyms _ TermOK.nil
  have r4 := runs_peekR NC S3
  rcases Nat.eq_zero_or_pos ((k + 1) / 2) with h0 | hpos
  · -- `(k+1)/2 = 0`: increment
    have hS3' : S3 NC = natSyms 0 ++ [] := by rw [hS3, Function.update_self, h0]
    have r5 := runs_inc h3 0 [] S3 TermOK.nil hS3'
    rw [hS3, Function.update_idem] at r5
    have hite := runs_seq_ite (c := optIsBit) (b := false) (A := skip) (A' := inc NC U)
      (WP.W9comp.runs_mono r4 (fun r hr => by rw [hr, hb3, h0]; rfl) le_rfl)
      (fun h => absurd h (by decide)) (fun _ => r5)
    have hmax : max ((k + 1) / 2) 1 = 0 + 1 := by omega
    rw [hmax]
    refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
      (WP.W9comp.runs_seq r3 hite))) (fun _ _ => trivial) ?_
    omega
  · -- `(k+1)/2 ≥ 1`: skip
    have r5 := runs_skip' S3
    have hite := runs_seq_ite (c := optIsBit) (b := true) (A := skip) (A' := inc NC U)
      (WP.W9comp.runs_mono r4 (fun r hr => by
        rw [hr, hb3]; exact decide_eq_true (by omega)) le_rfl)
      (fun _ => r5) (fun h => absurd h (by decide))
    have hmax : max ((k + 1) / 2) 1 = (k + 1) / 2 := by omega
    rw [hmax]
    refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
      (WP.W9comp.runs_seq r3 hite))) (fun _ _ => trivial) ?_
    omega

end C2

end SubNLogN.Machine.BridgePP
