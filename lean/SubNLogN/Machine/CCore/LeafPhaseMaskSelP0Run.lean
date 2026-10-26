/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelP0Kit

/-!
# C-core phase leaf, record-wise sign selection: correctness of phase 0 (`LeafPhaseMaskSelP0Run.lean`)

**Scope (honest summary).**
* `runs_phase0A'` (proved): phase 0, part A, leaves the slot table on `Tss`, `X = K - 1 - ρ` and
  `Fu = 0^{m^{k-1}}`, all other scratch stacks empty, named stacks unchanged, within `cost0A`.
* `phase0_of` (proved): `Phase0BStmt → Phase0Stmt`, i.e. correctness of phase 0 conditional on
  its part B (the named statement `Phase0BStmt` of `LeafPhaseMaskSelP0Kit.lean`).
-/

namespace SubNLogN.Machine.CCore.PhaseMaskAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP Computability

/-- The cost bound of phase 0, part A. -/
def cost0A (K k ρ : ℕ) : ℕ :=
  (mn + 1) + (7 * K + 7) + (8 * K + 10) + (7 * ρ + 7) + (ρ * (8 * K + 10 + 8 * ρ + 13) + 2) +
    1 + (7 * k + 7) + (8 * k + 10) + ((k - 1) * (8 * mn ^ (k - 1) + 6 + 8 * (k - 1) + 13) + 2)

theorem cost0_eq (K D j0 k ρ : ℕ) : cost0 K D j0 k ρ = cost0A K k ρ + cost0B K D j0 k := by
  unfold cost0 cost0A cost0B
  ring

/-! ## Phase 0, part A: the counters `X = K - 1 - ρ` and `Fu = 0^f` -/

theorem runs_phase0A' (l : List Sym) (hl : l.length = mn) (K k ρ : ℕ) (r3 r7 r8 : List Sym)
    (St : ML → List Sym) (hk : 1 ≤ k) (h3 : TermOK r3) (h7 : TermOK r7) (h8 : TermOK r8)
    (hS3 : St (nm 3) = natSyms K ++ r3) (hS7 : St (nm 7) = natSyms k ++ r7)
    (hS8 : St (nm 8) = natSyms ρ ++ r8) :
    Runs (phase0A' l)
      (msSt St (p0m [] [] [] [] [] [] []))
      (msSt St (p0m l (natSyms (K - 1 - ρ)) (List.replicate (mn ^ (k - 1)) (Sym.bit false))
        [] [] [] []))
      (fun _ => True) (cost0A K k ρ) := by
  -- 1. the slot table
  have r1 : Runs (msPushAll (sc .Tss) l) (msSt St (p0m [] [] [] [] [] [] []))
      (msSt St (p0m l [] [] [] [] [] [])) (fun _ => True) (mn + 1) := by
    have h := runs_msPushAll (sc .Tss) l (msSt St (p0m [] [] [] [] [] [] []))
    rw [update_msSt_inr] at h
    simp only [msSt_inr, p0m_Tss, List.append_nil, upd_p0m_Tss, hl] at h
    exact h
  -- 2. `X := K`
  have r2 := runs_msSt_cb0 (St := St) (m := p0m l [] [] [] [] [] []) (src := nm 3) (e := .X)
    (e2 := .C2) (by decide) (by decide) (by decide) K r3 h3 hS3 rfl
  rw [upd_p0m_X] at r2
  -- 3. `X := K - 1`
  have r3' := runs_msSt_dec0 (St := St) (m := p0m l (natSyms K) [] [] [] [] []) (e := .X)
    (by decide) K rfl
  rw [upd_p0m_X] at r3'
  -- 4. `J := ρ`
  have r4 := runs_msSt_cb0 (St := St) (m := p0m l (natSyms (K - 1)) [] [] [] [] [])
    (src := nm 8) (e := .J) (e2 := .C2) (by decide) (by decide) (by decide) ρ r8 h8 hS8 rfl
  rw [upd_p0m_J] at r4
  -- 5. `ρ` decrements of `X`
  have r5 := runs_msCd (C := sc .J) (U := sc .U) (by decide) (msLift (decIfPos (sc .X) (sc .U))) []
    TermOK.nil (fun j => msSt St (p0m l (natSyms (K - 1 - j)) [] [] [] [] []))
    (8 * bitLen K + 10) (fun j m => by
      rw [update_msSt_inr, update_msSt_inr, upd_p0m_J, upd_p0m_J]
      have h := runs_msSt_dec0 (St := St) (m := p0m l (natSyms (K - 1 - j)) [] []
        (natSyms m ++ []) [] []) (e := .X) (by decide) (K - 1 - j) rfl
      rw [upd_p0m_X, show K - 1 - j - 1 = K - 1 - (j + 1) by omega] at h
      exact WP.W9comp.runs_mono h (fun _ _ => trivial)
        (by have := TMFw.W3s.bitLen_mono (show K - 1 - j ≤ K by omega); omega)) ρ
  rw [update_msSt_inr, update_msSt_inr, upd_p0m_J, upd_p0m_J] at r5
  have r5' : Runs (msCd (sc .J) (sc .U) (msLift (decIfPos (sc .X) (sc .U))))
      (msSt St (p0m l (natSyms (K - 1)) [] [] (natSyms ρ) [] []))
      (msSt St (p0m l (natSyms (K - 1 - ρ)) [] [] [] [] [])) (fun _ => True)
      (ρ * (8 * bitLen K + 10 + 8 * bitLen ρ + 13) + 2) :=
    runs_congr_start r5 (by simp only [Nat.sub_zero, List.append_nil])
  -- 6. `Fu := [0]`
  have r6 := runs_msSt_push (St := St) (m := p0m l (natSyms (K - 1 - ρ)) [] [] [] [] [])
    .Fu (Sym.bit false)
  simp only [p0m_Fu, upd_p0m_Fu] at r6
  -- 7. `J := k`
  have r7' := runs_msSt_cb0 (St := St)
    (m := p0m l (natSyms (K - 1 - ρ)) [Sym.bit false] [] [] [] [])
    (src := nm 7) (e := .J) (e2 := .C2) (by decide) (by decide) (by decide) k r7 h7 hS7 rfl
  rw [upd_p0m_J] at r7'
  -- 8. `J := k - 1`
  have r8' := runs_msSt_dec0 (St := St)
    (m := p0m l (natSyms (K - 1 - ρ)) [Sym.bit false] [] (natSyms k) [] [])
    (e := .J) (by decide) k rfl
  rw [upd_p0m_J] at r8'
  -- 9. `k - 1` multiplications of `Fu` by `m`
  have r9 := runs_msCdT (C := sc .J) (U := sc .U) (by decide) (msMulM (sc .Fu) (sc .Fu2)) []
    TermOK.nil (fun j => msSt St (p0m l (natSyms (K - 1 - ρ))
      (List.replicate (mn ^ j) (Sym.bit false)) [] [] [] [])) (k - 1)
    (8 * mn ^ (k - 1) + 6) (fun j hj => by
      rw [update_msSt_inr, update_msSt_inr, upd_p0m_J, upd_p0m_J]
      have h := runs_msMulM (Fu := sc .Fu) (Fu2 := sc .Fu2) (by decide) (mn ^ j) [] TermOK.nil
        (msSt St (p0m l (natSyms (K - 1 - ρ)) (List.replicate (mn ^ j) (Sym.bit false))
          [] (natSyms (k - 1 - (j + 1)) ++ []) [] [])) (by simp) (by simp)
      rw [update_msSt_inr, upd_p0m_Fu, ← pow_succ] at h
      simp only [List.append_nil] at h ⊢
      refine WP.W9comp.runs_mono h (fun _ _ => trivial) ?_
      have e1 : mn ^ (j + 1) ≤ mn ^ (k - 1) :=
        Nat.pow_le_pow_right (by norm_num [mn, tripleM]) (by omega)
      have e2 : mn ^ j ≤ mn ^ (j + 1) := Nat.pow_le_pow_right (by norm_num [mn, tripleM]) (by omega)
      linarith)
  rw [update_msSt_inr, update_msSt_inr, upd_p0m_J, upd_p0m_J] at r9
  have r9' : Runs (msCd (sc .J) (sc .U) (msMulM (sc .Fu) (sc .Fu2)))
      (msSt St (p0m l (natSyms (K - 1 - ρ)) [Sym.bit false] [] (natSyms (k - 1)) [] []))
      (msSt St (p0m l (natSyms (K - 1 - ρ)) (List.replicate (mn ^ (k - 1)) (Sym.bit false))
        [] [] [] [])) (fun _ => True)
      ((k - 1) * (8 * mn ^ (k - 1) + 6 + 8 * bitLen (k - 1) + 13) + 2) :=
    runs_congr_start r9 (by simp only [pow_zero, List.replicate_one, List.append_nil])
  -- compose
  have hK := bitLen_le_self_m K
  have hr := bitLen_le_self_m ρ
  have hk' := bitLen_le_self_m k
  have hk1 := bitLen_le_self_m (k - 1)
  have m1 : ρ * bitLen K ≤ ρ * K := Nat.mul_le_mul_left _ hK
  have m2 : ρ * bitLen ρ ≤ ρ * ρ := Nat.mul_le_mul_left _ hr
  have m3 : (k - 1) * bitLen (k - 1) ≤ (k - 1) * (k - 1) := Nat.mul_le_mul_left _ hk1
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3' (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5'
    (WP.W9comp.runs_seq r6 (WP.W9comp.runs_seq r7' (WP.W9comp.runs_seq r8' r9'))))))))
    (fun _ _ => trivial) ?_
  unfold cost0A
  nlinarith

/-- **Phase 0 from its part B** (`Phase0BStmt → Phase0Stmt`). -/
theorem phase0_of (hB : Phase0BStmt) : Phase0Stmt := by
  intro ss K D j0 k ρ r3 r4 r6 r7 r8 St hk hρ hD h3 h4 h6 h7 h8 hS3 hS4 hS6 hS7 hS8
  have hlen : ((slotBools ss).map Sym.bit).length = mn := by
    rw [List.length_map, slotBools, List.length_map, List.length_finRange]
  have a := runs_phase0A' ((slotBools ss).map Sym.bit) hlen K k ρ r3 r7 r8 St hk h3 h7 h8 hS3 hS7
    hS8
  have b := hB ss K D j0 k ρ r4 r6 r8 St hk hρ hD h4 h6 h8 hS4 hS6 hS8
  rw [cost0_eq]
  exact WP.W9comp.runs_seq a b

end SubNLogN.Machine.CCore.PhaseMaskAux
