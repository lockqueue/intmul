/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelP0
import SubNLogN.Machine.CCore.LeafPhaseMaskSelCostDefs
import SubNLogN.Machine.CCore.LeafPhaseMaskSelVal

/-!
# C-core phase leaf, record-wise sign selection: phase-0 toolkit (`LeafPhaseMaskSelP0Kit.lean`)

**Scope (honest summary).** Helper lemmas for the correctness proof of phase 0 of the
`MaskSelStmt` kernel (all proved): evaluation lemmas for `p0m`, `Runs` wrappers on `msSt` states
(`runs_msSt_*`), `msSt_ext`, `length_maskMSB`, `length_membList`, `slots_eq`, and `runs_p0body`
(one chunk: decrement `R`, then emit). It also states, without proving them, two named statements:
* `Phase0BStmt`: correctness of phase 0, part B (`phase0B`);
* `Phase0Stmt`: correctness of phase 0 (`phase0 ss`), in the form used by `maskSel_of`.
-/

namespace SubNLogN.Machine.CCore.PhaseMaskAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP Computability

section P0m

variable (tss x fu r j tmp msk : List Sym)

@[simp] theorem p0m_Tss : p0m tss x fu r j tmp msk .Tss = tss := rfl
@[simp] theorem p0m_X : p0m tss x fu r j tmp msk .X = x := rfl
@[simp] theorem p0m_Fu : p0m tss x fu r j tmp msk .Fu = fu := rfl
@[simp] theorem p0m_R : p0m tss x fu r j tmp msk .R = r := rfl
@[simp] theorem p0m_J : p0m tss x fu r j tmp msk .J = j := rfl
@[simp] theorem p0m_Tmp : p0m tss x fu r j tmp msk .Tmp = tmp := rfl
@[simp] theorem p0m_Msk : p0m tss x fu r j tmp msk .Msk = msk := rfl
@[simp] theorem p0m_C : p0m tss x fu r j tmp msk .C = [] := rfl
@[simp] theorem p0m_C2 : p0m tss x fu r j tmp msk .C2 = [] := rfl
@[simp] theorem p0m_U : p0m tss x fu r j tmp msk .U = [] := rfl
@[simp] theorem p0m_Fu2 : p0m tss x fu r j tmp msk .Fu2 = [] := rfl
@[simp] theorem p0m_Tb : p0m tss x fu r j tmp msk .Tb = [] := rfl
@[simp] theorem p0m_Tb2 : p0m tss x fu r j tmp msk .Tb2 = [] := rfl
@[simp] theorem p0m_Gu : p0m tss x fu r j tmp msk .Gu = [] := rfl
@[simp] theorem p0m_Sc : p0m tss x fu r j tmp msk .Sc = [] := rfl
@[simp] theorem p0m_Su : p0m tss x fu r j tmp msk .Su = [] := rfl
@[simp] theorem p0m_Out : p0m tss x fu r j tmp msk .Out = [] := rfl

end P0m

/-- `natSyms` is a bit block. -/
theorem natSyms_eq_map_m (n : ℕ) : natSyms n = (encodeNat n).map Sym.bit := rfl

theorem bitLen_le_self_m (n : ℕ) : bitLen n ≤ n :=
  TMFw.W3s.bitLen_le_of_lt Nat.lt_two_pow_self

/-- Change the initial stacks of a `Runs` fact along an equality. -/
theorem runs_congr_start {K' σ : Type} [DecidableEq K'] {P : Prog K' (fun _ => Sym) σ}
    {S S0 S' : K' → List Sym} {Q : σ → Prop} {T : ℕ} (h : Runs P S S' Q T) (he : S = S0) :
    Runs P S0 S' Q T := he ▸ h

/-! ## `Runs` wrappers on `msSt` states -/

section Wrap

variable {St : ML → List Sym} {m : MSc → List Sym}

theorem runs_msSt_cb {src : ML} {e e2 : MSc} (h1 : src ≠ sc e) (h2 : src ≠ sc e2) (h3 : e ≠ e2)
    (blk : List Bool) (rest : List Sym) (hrest : TermOK rest)
    (hsrc : msSt St m src = blk.map Sym.bit ++ rest) :
    Runs (msLift (copyBlock src (sc e) (sc e2))) (msSt St m)
      (msSt St (Function.update m e (blk.map Sym.bit ++ m e))) (fun _ => True)
      (7 * blk.length + 7) := by
  have h := runs_liftRegs lensPO (runs_copyBlock h1 h2 (by simpa using h3) blk rest (msSt St m)
    hrest hsrc)
  rw [update_msSt_inr] at h
  exact h

theorem runs_msSt_dec {e : MSc} (hne : e ≠ .U) (n : ℕ) (rest : List Sym) (hrest : TermOK rest)
    (hm : m e = natSyms n ++ rest) :
    Runs (msLift (decIfPos (sc e) (sc .U))) (msSt St m)
      (msSt St (Function.update m e (natSyms (n - 1) ++ rest))) (fun _ => True)
      (8 * bitLen n + 10) := by
  have h := runs_liftRegs lensPO (runs_decIfPos (k := sc e) (t := sc .U) (by simpa using hne) n
    rest (msSt St m) hrest hm)
  rw [update_msSt_inr] at h
  exact h

theorem runs_msSt_push (e : MSc) (x : Sym) :
    Runs (msLift (pushC (sc e) x)) (msSt St m) (msSt St (Function.update m e (x :: m e)))
      (fun _ => True) 1 := by
  have h := runs_liftRegs lensPO (runs_pushC (sc e) x (msSt St m))
  rw [update_msSt_inr] at h
  exact h

theorem runs_msSt_mb {e e' : MSc} (hne : e ≠ e') (es : List Bool) (rest : List Sym)
    (hrest : TermOK rest) (hm : m e = es.map Sym.bit ++ rest) :
    Runs (msLift (moveBlock (sc e) (sc e'))) (msSt St m)
      (msSt St (Function.update (Function.update m e rest) e' (es.reverse.map Sym.bit ++ m e')))
      (fun _ => True) (3 * es.length + 4) := by
  have h := runs_liftRegs lensPO (runs_moveBlock (src := sc e) (dst := sc e') (by simpa using hne)
    es rest (msSt St m) hrest hm)
  rw [update_msSt_inr, update_msSt_inr] at h
  exact h

theorem runs_msSt_drop (e : MSc) (bs : List Bool) (rest : List Sym) (hrest : TermOK rest)
    (hm : m e = bs.map Sym.bit ++ rest) :
    Runs (msDropBits (sc e)) (msSt St m) (msSt St (Function.update m e rest)) (fun _ => True)
      (3 * bs.length + 2) := by
  have h := runs_msDropBits (k := sc e) bs rest (msSt St m) hrest hm
  rw [update_msSt_inr] at h
  exact h

theorem runs_msSt_emit (b : Bool) (x ρ : ℕ) (r8 : List Sym) (h8 : TermOK r8)
    (hS8 : St (nm 8) = natSyms ρ ++ r8) (hX : m .X = natSyms x ++ []) (hC : m .C = []) :
    Runs (p0Emit b) (msSt St m)
      (msSt St (Function.update m .Tmp (List.replicate ρ (Sym.bit false) ++ Sym.bit b ::
        (List.replicate x (Sym.bit false) ++ m .Tmp)))) (fun _ => True) (30 * (x + ρ) + 30) := by
  have h := runs_msEmitP (X := sc .X) (Rho := nm 8) (C := sc .C) (C2 := sc .C2) (U := sc .U)
    (Tmp := sc .Tmp) b (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) x ρ [] r8 TermOK.nil h8 (msSt St m) hX hS8 hC
  rw [update_msSt_inr] at h
  exact h

theorem runs_msSt_dec0 {e : MSc} (hne : e ≠ .U) (n : ℕ) (hm : m e = natSyms n) :
    Runs (msLift (decIfPos (sc e) (sc .U))) (msSt St m)
      (msSt St (Function.update m e (natSyms (n - 1)))) (fun _ => True) (8 * bitLen n + 10) := by
  have h := runs_msSt_dec (St := St) (m := m) hne n [] TermOK.nil (by rw [hm, List.append_nil])
  rw [List.append_nil] at h
  exact h

theorem runs_msSt_cb0 {src : ML} {e e2 : MSc} (h1 : src ≠ sc e) (h2 : src ≠ sc e2) (h3 : e ≠ e2)
    (n : ℕ) (rest : List Sym) (hrest : TermOK rest)
    (hsrc : msSt St m src = natSyms n ++ rest) (he : m e = []) :
    Runs (msLift (copyBlock src (sc e) (sc e2))) (msSt St m)
      (msSt St (Function.update m e (natSyms n))) (fun _ => True) (7 * bitLen n + 7) := by
  have h := runs_msSt_cb (St := St) (m := m) h1 h2 h3 (encodeNat n) rest hrest hsrc
  rw [he, List.append_nil] at h
  exact h

end Wrap

/-! ## Phase 0: helpers for part B -/

theorem msSt_ext {St : ML → List Sym} {m m' : MSc → List Sym} (h : ∀ e, m e = m' e) :
    msSt St m = msSt St m' := by
  rw [show m = m' from funext h]

theorem length_maskMSB (K ρ : ℕ) (hρ : ρ < K) (mem : List Bool) :
    (maskMSB K ρ mem).length = K * mem.length := by
  induction mem with
  | nil => simp [maskMSB]
  | cons b mem ih =>
    simp only [maskMSB, List.flatMap_cons, List.length_append, List.length_replicate,
      List.length_cons] at ih ⊢
    rw [ih]
    have : K - 1 - ρ + (ρ + 1) = K := by omega
    nlinarith

theorem length_membList (ss : Finset (Fin mn)) (j0 f D : ℕ) (h : j0 + mn * f ≤ D) :
    (membList ss j0 f D).length = D :=
  MaskSelValAux.length_membList ss j0 f D h

/-- The slot part of the membership list. -/
theorem slots_eq (ss : Finset (Fin mn)) (f : ℕ) :
    (slotBools ss).flatMap (fun b => List.replicate f b) =
      (List.finRange mn).flatMap (fun s => List.replicate f (decide (s ∈ ss))) := by
  simp [slotBools, List.flatMap_map]

/-- One chunk of the chunk loops: decrement `R`, emit the chunk `b`. -/
theorem runs_p0body {St : ML → List Sym} (b : Bool) (K ρ : ℕ) (hρ : ρ < K) (r8 : List Sym)
    (h8 : TermOK r8) (hS8 : St (nm 8) = natSyms ρ ++ r8) (n : ℕ) (m : MSc → List Sym)
    (hX : m .X = natSyms (K - 1 - ρ)) (hC : m .C = []) (hR : m .R = natSyms n) :
    Runs (.seq p0DecR (p0Emit b)) (msSt St m)
      (msSt St (Function.update (Function.update m .R (natSyms (n - 1))) .Tmp
        (List.replicate ρ (Sym.bit false) ++ Sym.bit b ::
          (List.replicate (K - 1 - ρ) (Sym.bit false) ++ m .Tmp))))
      (fun _ => True) (8 * n + 30 * K + 40) := by
  have d1 := runs_msSt_dec (St := St) (m := m) (e := .R) (by decide) n [] TermOK.nil
    (by rw [hR, List.append_nil])
  rw [List.append_nil] at d1
  have d2 := runs_msSt_emit (St := St) (m := Function.update m .R (natSyms (n - 1))) b
    (K - 1 - ρ) ρ r8 h8 hS8 (by simp [hX]) (by simp [hC])
  have e : Function.update m .R (natSyms (n - 1)) .Tmp = m .Tmp := by simp
  rw [e] at d2
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq d1 d2) (fun _ _ => trivial) ?_
  have := bitLen_le_self_m n
  omega

/-! ## The named statements -/

/-- The cost bound of phase 0, part B (`phase0B`). -/
def cost0B (K D j0 k : ℕ) : ℕ :=
  (7 * D + 7) + (7 * j0 + 7) + (j0 * (8 * D + 30 * K + 40 + 8 * j0 + 13) + 2) +
    (mn * (mn ^ (k - 1) * (8 * D + 30 * K + 44) + 3 * mn ^ (k - 1) + 6 + 4) + 2) +
    (D * (30 * K + 30 + 8 * D + 13) + 2) + (3 * (K * D) + 4) + (3 * K + 2) +
    (3 * mn ^ (k - 1) + 2)

/-- **[CONTRACT] Phase 0, part B.** From the slot table `slotBools ss` on `Tss`, `X = K - 1 - ρ`,
`Fu = 0^{m^{k-1}}` (all other scratch stacks empty) and the counters `D, j0, ρ` on the named
stacks `4, 6, 8`, `phase0B` leaves exactly the mask bits
`maskMSB K ρ (membList ss j0 (m^(k-1)) D)` on `Msk` (all other scratch stacks empty, named
stacks unchanged), within `cost0B K D j0 k` steps. -/
def Phase0BStmt : Prop :=
  ∀ (ss : Finset (Fin mn)) (K D j0 k ρ : ℕ) (r4 r6 r8 : List Sym) (St : ML → List Sym),
    1 ≤ k → ρ < K → j0 + mn ^ k ≤ D → TermOK r4 → TermOK r6 → TermOK r8 →
    St (nm 4) = natSyms D ++ r4 → St (nm 6) = natSyms j0 ++ r6 →
    St (nm 8) = natSyms ρ ++ r8 →
    Runs phase0B
      (msSt St (p0m ((slotBools ss).map Sym.bit) (natSyms (K - 1 - ρ))
        (List.replicate (mn ^ (k - 1)) (Sym.bit false)) [] [] [] []))
      (msSt St (p0m [] [] [] [] [] []
        ((maskMSB K ρ (membList ss j0 (mn ^ (k - 1)) D)).map Sym.bit)))
      (fun _ => True) (cost0B K D j0 k)

/-- **[CONTRACT] Phase 0.** From empty scratch stacks and the counters `K, D, j0, k, ρ` on the
named stacks `3, 4, 6, 7, 8`, `phase0 ss` leaves exactly the mask bits
`maskMSB K ρ (membList ss j0 (m^(k-1)) D)` on `Msk` (all other scratch stacks empty, named
stacks unchanged), within `cost0 K D j0 k ρ` steps. -/
def Phase0Stmt : Prop :=
  ∀ (ss : Finset (Fin mn)) (K D j0 k ρ : ℕ) (r3 r4 r6 r7 r8 : List Sym) (St : ML → List Sym),
    1 ≤ k → ρ < K → j0 + mn ^ k ≤ D →
    TermOK r3 → TermOK r4 → TermOK r6 → TermOK r7 → TermOK r8 →
    St (nm 3) = natSyms K ++ r3 → St (nm 4) = natSyms D ++ r4 → St (nm 6) = natSyms j0 ++ r6 →
    St (nm 7) = natSyms k ++ r7 → St (nm 8) = natSyms ρ ++ r8 →
    Runs (phase0 ss) (msSt St (p0m [] [] [] [] [] [] []))
      (msSt St (p0m [] [] [] [] [] []
        ((maskMSB K ρ (membList ss j0 (mn ^ (k - 1)) D)).map Sym.bit)))
      (fun _ => True) (cost0 K D j0 k ρ)

end SubNLogN.Machine.CCore.PhaseMaskAux
