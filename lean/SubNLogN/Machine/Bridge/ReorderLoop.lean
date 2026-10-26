/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.ReorderStep

/-!
# K5 reorder (3): the loop, the cost bound and the contract

The reorder machine `ReorderAux.reorderProg P6` (`ReorderStep.lean`) runs `initR`, then the
loop `peek M; while bit (stepR P6; peek M)`, then `finR`. (`c6`/`C6` is a historical name from an earlier draft for Lemma A.8 (`lem:transfer12`), kept for stability.) This file proves:
* `runs_loopR`: the loop runs from the state `stR S b v rarr 0` before step `0` to the state
  `stR S b v rarr ⌊d/2⌋` (`runs_cond_loop`, the family indexed by the number of remaining steps),
  from the step statement `StepRStmt` (`runs_stepR` of `ReorderStep.lean`, a hypothesis here);
* `runs_reorderProg`: the whole machine, from the input order `idxAddrsIn` (`= arrStep d 0`) to
  natural order (`= arrStep d ⌊d/2⌋`, `ExposeAddr.arrOrder_arrStep_zero/_half`);
* `reorder_cost_le`: the cost is within `(C6 + cS + 100) · reorderCost (bridgeX τ) b`; every
  step's Lemma A.8 (`lem:transfer12`) factor `u^τ` with `u = max(log₂ t_{d-1-s}, log₂ t_s) ∈ {ℓ-1, ℓ}` is
  `≤ ⌈ℓ^τ⌉₊` for every sign of `τ` (`ceil_rpow_le`);
* `reorder_of_c6_of_step`: `ReorderStmt (bridgeX τ)` from `C6InterchangeStmt τ`, its premise, and
  the step statement; `reorder_of_c6`: the same with `runs_stepR` from `ReorderStep.lean` (no extra
  hypothesis).
-/

namespace SubNLogN.Machine.Bridge.ReorderLoopAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability
open SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Machine.BridgeExp
open SubNLogN.Machine.Bridge.ReorderAux

/-- The interchange factor of one step is within `⌈ℓ^τ⌉₊`, for `1 ≤ u ≤ ℓ` and every sign of `τ`. -/
theorem ceil_rpow_le (V u ℓ : ℕ) (τ : ℝ) (hu1 : 1 ≤ u) (hul : u ≤ ℓ) :
    ⌈(V : ℝ) * (u : ℝ) ^ τ⌉₊ ≤ V * bridgeX τ ℓ := by
  apply Nat.ceil_le.2
  push_cast
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  unfold bridgeX
  rcases le_or_gt 0 τ with hτ | hτ
  · exact le_trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hul) hτ)
      (Nat.le_ceil _)
  · have h1 : (u : ℝ) ^ τ ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hu1) hτ.le
    have hℓ : (0 : ℝ) < ℓ := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hu1.trans hul))
    have h2 : 0 < ⌈(ℓ : ℝ) ^ τ⌉₊ := Nat.ceil_pos.2 (Real.rpow_pos_of_pos hℓ τ)
    have h3 : (1 : ℝ) ≤ (⌈(ℓ : ℝ) ^ τ⌉₊ : ℝ) := Nat.one_le_cast.2 h2
    linarith

section Loop

variable {E6 R6 : Type} [DecidableEq E6]

/-- **The step statement** (`runs_stepR`, `ReorderStep.lean`): one step `stepR P6` runs from the state before
step `s` to the state before step `s + 1`, at cost `cS·setup` plus the interchange cost of the step. -/
def StepRStmt (τ : ℝ) (C6 cS : ℕ) (P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6) : Prop :=
  ∀ (b : BrPar) (k ℓ : ℕ), BalancedShape b.t k ℓ → ShapeOK b.t → 1 ≤ b.wI →
    ∀ (v : Idx b.t → CInt) (rarr rpar : List Sym), BlkTerm rarr →
    ∀ (S : RL E6 → List Sym), KClean S → S (kN .par) = hdrSyms b.hdr ++ rpar →
    ∀ s : ℕ, s < b.d - 1 - s →
      Runs (stepR P6) (stR S b v rarr s) (stR S b v rarr (s + 1)) (fun _ => True)
        (cS * b.setup + C6 * (⌈(vol1 b.R b.wI : ℝ) *
          ((max (aN b.t (b.d - 1 - s)) (aN b.t s) : ℕ) : ℝ) ^ τ⌉₊ + 1))

theorem step_cost_le (τ : ℝ) (b : BrPar) {k ℓ : ℕ} (hbal : BalancedShape b.t k ℓ)
    (C6 cS s : ℕ) (hs : s < b.d - 1 - s) :
    cS * b.setup + C6 * (⌈(vol1 b.R b.wI : ℝ) *
        ((max (aN b.t (b.d - 1 - s)) (aN b.t s) : ℕ) : ℝ) ^ τ⌉₊ + 1) ≤
      cS * b.setup + C6 * (vol1 b.R b.wI * bridgeX τ ℓ + 1) := by
  have hd : 2 ≤ b.d := hbal.1
  have hℓ : 2 ≤ ℓ := hbal.2.2.1
  have h1 := aN_bal (m := b.d - 1 - s) hbal (by omega)
  have h2 := aN_bal (m := s) hbal (by omega)
  have hu1 : 1 ≤ max (aN b.t (b.d - 1 - s)) (aN b.t s) := le_max_of_le_left (by omega)
  have hul : max (aN b.t (b.d - 1 - s)) (aN b.t s) ≤ ℓ := max_le (by omega) (by omega)
  have := ceil_rpow_le (vol1 b.R b.wI) _ ℓ τ hu1 hul
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right this 1)) _

/-- **The reorder loop**: `⌊d/2⌋` steps, from `stR … 0` to `stR … ⌊d/2⌋`. -/
theorem runs_loopR (τ : ℝ) {C6 cS : ℕ} {P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6}
    (hstep : StepRStmt τ C6 cS P6) (b : BrPar) {k ℓ : ℕ} (hbal : BalancedShape b.t k ℓ)
    (ht : ShapeOK b.t) (hwI : 1 ≤ b.wI) (v : Idx b.t → CInt) (rarr rpar : List Sym)
    (hrarr : BlkTerm rarr) (S : RL E6 → List Sym) (hcl : KClean S)
    (hpar : S (kN .par) = hdrSyms b.hdr ++ rpar) :
    Runs (.seq (BridgeRed.peekTop (rs .M)) (.loop BridgeRed.topIsBit
        (.seq (stepR P6) (BridgeRed.peekTop (rs .M)))))
      (stR S b v rarr 0) (stR S b v rarr (b.d / 2)) (fun _ => True)
      (1 + loopCost (fun _ => cS * b.setup + C6 * (vol1 b.R b.wI * bridgeX τ ℓ + 1) + 1)
        (b.d / 2)) := by
  have hd2 : 2 ≤ b.d := hbal.1
  have h := runs_cond_loop (σ' := R6) (rs .M : RL E6) BridgeRed.topIsBit (stepR P6)
    (fun n => stR S b v rarr (b.d / 2 - n)) (b.d / 2)
    (fun _ => cS * b.setup + C6 * (vol1 b.R b.wI * bridgeX τ ℓ + 1))
    (fun n w hn => by
      simp only [stR, Function.update_of_ne (show (rs .M : RL E6) ≠ rs .W by simp),
        Function.update_self]
      rw [BridgeRed.topIsBit_natSyms, decide_eq_decide]
      omega)
    (fun n hn => by
      have hs : b.d / 2 - (n + 1) < b.d - 1 - (b.d / 2 - (n + 1)) := by omega
      have e : b.d / 2 - n = b.d / 2 - (n + 1) + 1 := by omega
      show Runs (stepR P6) (stR S b v rarr (b.d / 2 - (n + 1))) (stR S b v rarr (b.d / 2 - n))
        (fun _ => True) (cS * b.setup + C6 * (vol1 b.R b.wI * bridgeX τ ℓ + 1))
      rw [e]
      exact WP.W9comp.runs_mono (hstep b k ℓ hbal ht hwI v rarr rpar hrarr S hcl hpar _ hs)
        (fun _ _ => trivial) (step_cost_le τ b hbal C6 cS _ hs))
  simp only [Nat.sub_self, Nat.sub_zero] at h
  exact h

/-- The final cleanup drops `Nc` and `W`. -/
theorem runs_finR (b : BrPar) (v : Idx b.t → CInt) (rarr : List Sym) (S : RL E6 → List Sym)
    (s : ℕ) :
    Runs (lift (σ' := R6) (finR (E6 := E6))) (stR S b v rarr s)
      (Function.update (Function.update (stR S b v rarr s) (rs .Nc) []) (rs .W) [])
      (fun _ => True) (2 * bitLen s + 2 + (2 * bitLen (2 * b.wI) + 2)) := by
  have r1 := WP.W9mp.runs_popHdr (rs .Nc : RL E6) s [] (stR S b v rarr s)
    (by simp [stR, hdrSyms_cons', hdrSyms_nil])
  have r2 := WP.W9mp.runs_popHdr (rs .W : RL E6) (2 * b.wI) []
    (Function.update (stR S b v rarr s) (rs .Nc) [])
    (by simp [stR, hdrSyms_cons', hdrSyms_nil])
  exact runs_lift (WP.W9comp.runs_seq r1 r2)

/-- **The reorder machine runs** (from the step statement): the records in input order
`idxAddrsIn` become the records in natural order `idxAddrsFreq`. -/
theorem runs_reorderProg (τ : ℝ) {C6 cS : ℕ} {P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6}
    (hstep : StepRStmt τ C6 cS P6) (b : BrPar) {k ℓ : ℕ} (hbal : BalancedShape b.t k ℓ)
    (ht : ShapeOK b.t) (hwI : 1 ≤ b.wI) (v : Idx b.t → CInt) (rarr rpar : List Sym)
    (hrarr : BlkTerm rarr) (S : RL E6 → List Sym) (hcl : KClean S)
    (harr : S (kW .arr) = carrSyms b.wI (recsAt (idxAddrsIn b.t) v) ++ rarr)
    (hpar : S (kN .par) = hdrSyms b.hdr ++ rpar) :
    Runs (reorderProg P6) S
      (Function.update S (kW .arr) (carrSyms b.wI (recsAt (idxAddrsFreq b.t) v) ++ rarr))
      (fun _ => True)
      ((b.d + 1) * (cS * b.setup + C6 * (vol1 b.R b.wI * bridgeX τ ℓ + 1)) +
        100 * (b.d + 1) * b.setup) := by
  have hcl' : ∀ e, S (.inr e) = [] := hcl
  have hd2 : 2 ≤ b.d := hbal.1
  have r1 := runs_initR (E6 := E6) (R6 := R6) b hwI rpar S (hcl' _) (hcl' _) (hcl' _) (hcl' _)
    hpar
  have h0 : Function.update (Function.update (Function.update S (rs .W)
        (natSyms (2 * b.wI) ++ [Sym.mark])) (rs .M) (natSyms (b.d - 1))) (rs .Nc) [Sym.mark] =
      stR S b v rarr 0 := by
    funext x
    by_cases x1 : x = kW .arr
    · subst x1
      simp [stR, harr, arrOrder_arrStep_zero]
    by_cases x2 : x = rs .Nc
    · subst x2
      simp [stR, natSyms_zero_x]
    by_cases x3 : x = rs .M
    · subst x3
      simp [stR]
    by_cases x4 : x = rs .W
    · subst x4
      simp [stR]
    simp [stR, x1, x2, x3, x4]
  rw [h0] at r1
  have r2 := runs_loopR τ hstep b hbal ht hwI v rarr rpar hrarr S hcl hpar
  have r3 := runs_finR (R6 := R6) b v rarr S (b.d / 2)
  have hfin : Function.update (Function.update (stR S b v rarr (b.d / 2)) (rs .Nc) []) (rs .W)
      [] = Function.update S (kW .arr) (carrSyms b.wI (recsAt (idxAddrsFreq b.t) v) ++ rarr) := by
    funext x
    by_cases x1 : x = kW .arr
    · subst x1
      simp [stR, arrOrder_arrStep_half]
    by_cases x2 : x = rs .Nc
    · subst x2
      simp [hcl']
    by_cases x3 : x = rs .M
    · subst x3
      simp [stR, show b.d - 1 - 2 * (b.d / 2) = 0 by omega, natSyms_zero_x, hcl']
    by_cases x4 : x = rs .W
    · subst x4
      simp [hcl']
    simp [stR, x1, x2, x3, x4]
  have hall := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 r3)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall hfin) (fun _ _ => trivial) ?_
  have hH : b.d + 9 ≤ (hdrSyms b.hdr).length := by
    have h1 := length_le_hdrSyms b.hdr
    have h2 : b.hdr.length = 9 + b.d := by
      simp [BrPar.hdr] <;> omega
    omega
  have hset : (hdrSyms b.hdr).length + 1 ≤ b.setup := by
    unfold BrPar.setup
    exact Nat.le_self_pow (by norm_num) _
  have hwIH : bitLen (2 * b.wI) ≤ (hdrSyms b.hdr).length := by
    have h1 : bitLen b.wI + 1 ≤ (hdrSyms b.hdr).length :=
      bitLen_le_hdrSyms (by simp [BrPar.hdr])
    have h2 : bitLen (2 * b.wI) = bitLen b.wI + 1 := by
      rw [← length_natSyms_x, ← length_natSyms_x, natSyms_two_mul hwI, List.length_cons]
    omega
  have hdl : bitLen (b.d / 2) ≤ (hdrSyms b.hdr).length :=
    le_trans (bitLen_le_self_x _) (by omega)
  have hloop := loopCost_le_mul
    (fun _ => cS * b.setup + C6 * (vol1 b.R b.wI * bridgeX τ ℓ + 1) + 1)
    (cS * b.setup + C6 * (vol1 b.R b.wI * bridgeX τ ℓ + 1) + 1) (b.d / 2) (fun _ _ => le_rfl)
  generalize cS * b.setup + C6 * (vol1 b.R b.wI * bridgeX τ ℓ + 1) = Q at hloop ⊢
  have h1 := Nat.mul_le_mul_right (Q + 1 + 1) (show b.d / 2 ≤ b.d + 1 by omega)
  nlinarith [hloop, h1, hset, hH, hwIH, hdl, Nat.zero_le (b.d * b.setup), Nat.zero_le (b.d * Q)]

end Loop

/-- The cost of `runs_reorderProg` is within `(C6 + cS + 100) · reorderCost (bridgeX τ) b`. -/
theorem reorder_cost_le (τ : ℝ) (b : BrPar) (C6 cS ℓ : ℕ) (hℓ : axisBits b.t = ℓ) :
    (b.d + 1) * (cS * b.setup + C6 * (vol1 b.R b.wI * bridgeX τ ℓ + 1)) +
        100 * (b.d + 1) * b.setup ≤
      (C6 + cS + 100) * reorderCost (bridgeX τ) b := by
  unfold reorderCost exposeCost
  rw [hℓ]
  have hs : 1 ≤ b.setup := by
    unfold BrPar.setup
    exact Nat.one_le_pow _ _ (by omega)
  have hA1 : b.setup ≤ (bridgeX τ ℓ + 1) * vol1 b.R b.wI + b.setup := Nat.le_add_left _ _
  have hA2 : vol1 b.R b.wI * bridgeX τ ℓ + 1 ≤ (bridgeX τ ℓ + 1) * vol1 b.R b.wI + b.setup := by
    nlinarith
  have hinner : cS * b.setup + C6 * (vol1 b.R b.wI * bridgeX τ ℓ + 1) + 100 * b.setup ≤
      (C6 + cS + 100) * ((bridgeX τ ℓ + 1) * vol1 b.R b.wI + b.setup) := by
    have e1 := Nat.mul_le_mul_left cS hA1
    have e2 := Nat.mul_le_mul_left C6 hA2
    have e3 := Nat.mul_le_mul_left 100 hA1
    nlinarith [e1, e2, e3]
  calc (b.d + 1) * (cS * b.setup + C6 * (vol1 b.R b.wI * bridgeX τ ℓ + 1)) +
        100 * (b.d + 1) * b.setup
      = (b.d + 1) * (cS * b.setup + C6 * (vol1 b.R b.wI * bridgeX τ ℓ + 1) +
          100 * b.setup) := by ring
    _ ≤ (b.d + 1) * ((C6 + cS + 100) * ((bridgeX τ ℓ + 1) * vol1 b.R b.wI + b.setup)) :=
        Nat.mul_le_mul_left _ hinner
    _ = (C6 + cS + 100) * ((b.d + 1) * ((bridgeX τ ℓ + 1) * vol1 b.R b.wI + b.setup)) := by
        ring

/-- **`ReorderStmt (bridgeX τ)` from Lemma A.8 (`lem:transfer12`) and the step statement** (`StepRStmt` for every
interchange program `P6`, i.e. `runs_stepR`, with step constant `cS`). Program `reorderProg P6`, constant
`C6 + cS + 100`. -/
theorem reorder_of_c6_of_step (τ : ℝ)
    (hτ : (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ)
    (hC6 : C6InterchangeStmt τ) (cS : ℕ)
    (hstepR : ∀ (E6 R6 : Type) [DecidableEq E6] (C6 : ℕ)
      (P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6),
      C6Spec τ E6 R6 C6 P6 → StepRStmt τ C6 cS P6) :
    ReorderStmt (bridgeX τ) := by
  obtain ⟨C6, h⟩ := hC6 hτ
  obtain ⟨E6, _, _, R6, P6, _, _, hcl6, spec⟩ := h ()
  refine ⟨C6 + cS + 100, fun _ => ⟨RS ⊕ E6, inferInstance, inferInstance, Option Sym × R6,
    reorderProg P6, inferInstance, inferInstance, closed_reorderProg hcl6, ?_⟩⟩
  intro b v rarr rpar S hcl _ ht hbal hwI _ hrarr harr hpar
  obtain ⟨k, ℓ, hb⟩ := hbal
  exact WP.W9comp.runs_mono
    (runs_reorderProg τ (hstepR E6 R6 C6 P6 spec) b hb ht hwI v rarr rpar hrarr S hcl harr hpar)
    (fun _ _ => trivial) (reorder_cost_le τ b C6 cS ℓ (axisBits_bal hb))

end SubNLogN.Machine.Bridge.ReorderLoopAux

namespace SubNLogN.Machine

open SubNLogN.Machine.Bridge.ReorderAux SubNLogN.Machine.Bridge.ReorderLoopAux

/-- **[K5] Reorder to tensor order from Lemma A.8 (`lem:transfer12`)** (`ReorderStmt`, Lemma 4.8 (bridge Lemma D): `⌊d/2⌋` direct exchanges)
at the pipe's interchange factor `bridgeX τ`: from the interchange `C6InterchangeStmt τ` and
its premise `s_b/W_b < m^τ`. Program `ReorderAux.reorderProg P6` (`ReorderStep.lean`), step lemma
`ReorderAux.runs_stepR` (step constant `300`), constant `C6 + 400`. -/
theorem reorder_of_c6 (τ : ℝ) (hτ : (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ)
    (hC6 : C6InterchangeStmt τ) : ReorderStmt (bridgeX τ) := by
  refine reorder_of_c6_of_step τ hτ hC6 300 ?_
  intro E6 R6 _ C6 P6 h6
  unfold StepRStmt
  intro b k ℓ hb ht hwI v rarr rpar hrarr S hcl hpar s hs
  exact runs_stepR τ h6 b hb ht hwI v rarr rpar hrarr S hcl hpar s hs

end SubNLogN.Machine
