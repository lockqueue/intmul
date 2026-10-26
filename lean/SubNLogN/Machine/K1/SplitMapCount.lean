/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.SplitMapMove

/-!
# K1/K5 shared kit, part 3 (`K1/SplitMapCount.lean`): binary countdown loops

**Scope (honest summary).** Proved generic rules (no contract is proved here):
* `cdLoop cnt tmp mv`: while the binary counter on `cnt` is nonzero, decrement it (`TMFw.Lib.dec`)
  and run `mv`; `loopM_cdLoop`.
* `cdMove ns cnt tmp mv`: copy the counter `N` on `ns` (restored) to `cnt` above a `mark`, run
  `mv` exactly `N` times, drop the `mark`; `runsM_cdMove`.
* Cost: `incSeqCost 6 8 N + Σ c + 2N + 7·bitLen N + 12`, where `incSeqCost 6 8 N ≤ 14·N` is the
  amortized decrement cost (`TMFw.incSeqCost_le`), via `zerosLead (encodeNat (n+1)) =
  ones (encodeNat n)`. This is the amortized counter and local countdown device of Lemma A.4 (`lem:transfer-streams`).
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

theorem zerosLead_incBits : ∀ L : List Bool, zerosLead (incBits L) = ones L
  | [] => rfl
  | true :: l => by simp [incBits, zerosLead, ones, zerosLead_incBits l]
  | false :: l => by simp [incBits, zerosLead, ones]

theorem zerosLead_encodeNat_succ (n : ℕ) : zerosLead (encodeNat (n + 1)) = ones (encodeNat n) := by
  rw [encodeNat_succ, zerosLead_incBits]

theorem csum_shift (c : ℕ → ℕ) : ∀ (n0 len : ℕ), csum (fun i => c (i + 1)) n0 len = csum c (n0 + 1) len
  | _, 0 => rfl
  | n0, len + 1 => by
    simp only [csum]
    rw [csum_shift c (n0 + 1) len]

theorem natSyms_succ_head (n : ℕ) (R : List Sym) :
    testO Sym.isBit (natSyms (n + 1) ++ R).head? = true := by
  obtain ⟨b, l, h⟩ : ∃ b l, encodeNat (n + 1) = b :: l := by
    cases h : encodeNat (n + 1) with
    | nil => exact absurd ((encodeNat_eq_nil_iff _).1 h) (Nat.succ_ne_zero n)
    | cons b l => exact ⟨b, l, rfl⟩
  simp [natSyms, h, testO]

theorem testO_isBit_of_termOK {R : List Sym} (hR : TermOK R) : testO Sym.isBit R.head? = false := by
  cases R with
  | nil => rfl
  | cons x R => simpa [testO] using hR x rfl

section Countdown

variable {K M : Type}

/-- Countdown loop: while the counter on `cnt` is nonzero, decrement it and run `mv`. -/
def cdLoop (cnt tmp : K) (mv : KP K M) : KP K M :=
  whileTop cnt Sym.isBit (.seq (lift (Lib.dec cnt tmp)) mv)

/-- Copy the counter on `ns` to `cnt` above a `mark`, run `mv` that many times, drop the `mark`. -/
def cdMove (ns cnt tmp : K) (mv : KP K M) : KP K M :=
  .seq (lift (Lib.pushC cnt .mark)) (.seq (lift (Lib.copyBlock ns cnt tmp))
    (.seq (cdLoop cnt tmp mv) (lift (Lib.popR cnt))))

theorem closed_cdLoop (cnt tmp : K) {mv : KP K M} (h : mv.Closed) : (cdLoop cnt tmp mv).Closed := by
  refine closed_whileTop _ _ ⟨closed_lift ?_, h⟩
  simp [Prog.Closed, Prog.FreeBelow, Lib.dec, Lib.pushC, Lib.popR, Lib.scanLoop, Lib.scanBody,
    Lib.decFix, Lib.peekR, Lib.skip, Lib.moveBits, Lib.moveBitsBody, Lib.pushR]

theorem closed_cdMove (ns cnt tmp : K) {mv : KP K M} (h : mv.Closed) :
    (cdMove ns cnt tmp mv).Closed := by
  refine ⟨closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC]), closed_lift ?_,
    closed_cdLoop cnt tmp h, closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.popR])⟩
  simp [Prog.Closed, Prog.FreeBelow, Lib.copyBlock, Lib.pushC, Lib.moveBlock, Lib.moveBits,
    Lib.moveBitsBody, Lib.restoreR, Lib.moveBitsDup, Lib.dupBody, Lib.pushR, Lib.popR, Lib.skip]

variable [DecidableEq K]

theorem loopM_cdLoop {cnt tmp : K} (hct : cnt ≠ tmp) (mv : KP K M) (R : List Sym) (hR : TermOK R) :
    ∀ (n : ℕ) (m : ℕ → M) (S : ℕ → K → List Sym) (c : ℕ → ℕ),
      (∀ i < n, ∀ X, RunsM mv (m i) (Function.update (S i) cnt X) (m (i + 1))
        (Function.update (S (i + 1)) cnt X) (c i)) →
      LoopM cnt Sym.isBit (.seq (lift (Lib.dec cnt tmp)) mv) (m 0)
        (Function.update (S 0) cnt (natSyms n ++ R)) (m n) (Function.update (S n) cnt R)
        (incSeqCost 6 8 n + csum c 0 n + 2 * n + 1)
  | 0, m, S, c, _ => by
    refine (LoopM.stop ?_).mono ?_
    · simp only [Function.update_self]
      simpa [natSyms, encodeNat_zero] using testO_isBit_of_termOK hR
    · simp [incSeqCost, csum]
  | n + 1, m, S, c, hmv => by
    have hdec : RunsM (lift (M := M) (Lib.dec cnt tmp)) (m 0)
        (Function.update (S 0) cnt (natSyms (n + 1) ++ R)) (m 0)
        (Function.update (S 0) cnt (natSyms n ++ R))
        (6 * zerosLead (encodeNat (n + 1)) + 8) := by
      refine RunsM.ofLib (fun o => ⟨some Sym.mark, _, le_rfl, ?_⟩) (m 0)
      have e := Lib.dec_eval hct [] o n R (Function.update (S 0) cnt (natSyms (n + 1) ++ R)) hR
        (by rw [Function.update_self]; rfl)
      rw [Function.update_idem] at e
      exact e
    have h1 := hdec.seq (hmv 0 (Nat.succ_pos n) (natSyms n ++ R))
    have ih := loopM_cdLoop hct mv R hR n (fun i => m (i + 1)) (fun i => S (i + 1))
      (fun i => c (i + 1)) (fun i hi X => hmv (i + 1) (by omega) X)
    have hc : testO Sym.isBit ((Function.update (S 0) cnt (natSyms (n + 1) ++ R)) cnt).head? =
        true := by
      rw [Function.update_self]
      exact natSyms_succ_head n R
    refine (LoopM.step hc h1 ih).mono ?_
    rw [zerosLead_encodeNat_succ, csum_shift]
    simp only [incSeqCost, csum]
    omega

/-- **Countdown move.** `mv` runs `N` times (step `i` from state `i` to `i + 1`, framing `cnt`),
where `N` is the counter on `ns` (restored). -/
theorem runsM_cdMove {ns cnt tmp : K} (hnc : ns ≠ cnt) (hnt : ns ≠ tmp) (hct : cnt ≠ tmp)
    (mv : KP K M) (N : ℕ) (Rn C0 : List Sym) (hRn : TermOK Rn) (m : ℕ → M)
    (S : ℕ → K → List Sym) (c : ℕ → ℕ) (hns : S 0 ns = natSyms N ++ Rn) (hcnt0 : S 0 cnt = C0)
    (hcntN : S N cnt = C0)
    (hmv : ∀ i < N, ∀ X, RunsM mv (m i) (Function.update (S i) cnt X) (m (i + 1))
      (Function.update (S (i + 1)) cnt X) (c i)) :
    RunsM (cdMove ns cnt tmp mv) (m 0) (S 0) (m N) (S N)
      (incSeqCost 6 8 N + csum c 0 N + 2 * N + 7 * bitLen N + 12) := by
  have h1 := RunsM.push (M := M) cnt Sym.mark (m 0) (S 0)
  rw [hcnt0] at h1
  have h2 : RunsM (lift (M := M) (Lib.copyBlock ns cnt tmp)) (m 0)
      (Function.update (S 0) cnt (Sym.mark :: C0)) (m 0)
      (Function.update (S 0) cnt (natSyms N ++ Sym.mark :: C0)) (7 * bitLen N + 7) := by
    refine RunsM.ofLib (fun o => ⟨some Sym.mark, _, le_rfl, ?_⟩) (m 0)
    have e := Lib.copyBlock_eval hnc hnt hct [] o (encodeNat N) Rn
      (Function.update (S 0) cnt (Sym.mark :: C0)) hRn
      (by rw [Function.update_of_ne hnc]; exact hns)
    rw [Function.update_idem, Function.update_self] at e
    exact e
  have h3 := runsM_whileTop' (loopM_cdLoop hct mv (Sym.mark :: C0) (TermOK.cons rfl _) N m S c hmv)
  have h4 := RunsM.pop (M := M) cnt Sym.mark C0 (m N) (Function.update (S N) cnt (Sym.mark :: C0))
    (Function.update_self _ _ _)
  refine RunsM.of_eq (h1.seq (h2.seq (h3.seq h4))) rfl rfl rfl ?_ ?_
  · rw [Function.update_idem, ← hcntN, Function.update_eq_self]
  · omega

end Countdown

end SubNLogN.Machine.K1.SMM
