/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7LinesMain
import SubNLogN.Machine.AppC.C5StreamArith
import WP.W3s.Concat
import WP.W9mp.Glue

/-!
# Lemma A.9 lines, the counter kernel (`Machine/AppC/C7LinesSetup.lean`)

Proves `C7LinesSetupStmt` (stated in `C7LinesMain.lean`): from the counters `K, f, N1, N2`, push
`natSyms (f·K)` onto three stacks and `natSyms (N1·2^{f·K}·N2)` onto a fourth. Built from the
mark-floored `NatArith` library (`AppC/C5StreamArith.lean`: `mulN`, `copyN`, `pushMark`, `dropF`)
and the proved shift `TMFw.W3s.W3_shlVar_holds`:
`P1 ← f·K` (on a `mark` floor), copied three times; `P2 ← N1` (on a `mark` floor), shifted by
`P1`; `G ← P2·N2`; drop `P2` and `P1` with their floors. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

**Results (0 `sorry`).** `c7LinesSetup_holds : C7LinesSetupStmt`, and the wrapper
`c7Lines_holds (hC6 : C6InterchangeStmt τ) (hOff : ∀ ε par xF, K4OffsetCtlParStmt (lineOff ε par xF) J) :
C7LinesStmt τ σ`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

namespace AppC.C7LinesSetupAux

open NatArith

/-- Private stacks of the counter kernel: `0` = `P1` (for `L`), `1` = `P2` (for `N1·2^L`), `2..5` the
multiplication temporaries, `6` the copy temporary; then the shift kernel's scratch. -/
abbrev SE (ms : ℕ) : Type := Fin 7 ⊕ Fin ms

/-- Private stack `i`. -/
def pv {ms : ℕ} (i : Fin 7) : KLoc (Fin 8) (SE ms) := .inr (.inl i)

/-- Stack map of the shift kernel: the number on `P2`, the counter on `P1`. -/
def ιsh {ms : ℕ} : Loc 2 ms → KLoc (Fin 8) (SE ms)
  | .inl i => if i = 0 then pv 1 else pv 0
  | .inr j => .inr (.inr j)

theorem ιsh_injective {ms : ℕ} : Function.Injective (ιsh (ms := ms)) := by
  rintro (i | j) (i' | j') h
  · fin_cases i <;> fin_cases i' <;> simp_all [ιsh, pv]
  · fin_cases i <;> simp [ιsh, pv] at h
  · fin_cases i' <;> simp [ιsh, pv] at h
  · simp only [ιsh, Sum.inr.injEq] at h
    rw [h]

/-- **The counter program.** -/
def setupProg {ms : ℕ} {Rsh : Type} (Psh : Prog (Loc 2 ms) (fun _ => Sym) Rsh) :
    Prog (KLoc (Fin 8) (SE ms)) (fun _ => Sym) (Reg × Rsh) :=
  .seq ((pushMark (pv 0)).liftRegs (Lens.fst _ _))
  (.seq ((mulN (.inl 1) (.inl 0) (pv 0) (pv 2) (pv 3) (pv 4) (pv 5)).liftRegs (Lens.fst _ _))
  (.seq ((copyN (pv 0) (.inl 4) (pv 6)).liftRegs (Lens.fst _ _))
  (.seq ((copyN (pv 0) (.inl 5) (pv 6)).liftRegs (Lens.fst _ _))
  (.seq ((copyN (pv 0) (.inl 6) (pv 6)).liftRegs (Lens.fst _ _))
  (.seq ((pushMark (pv 1)).liftRegs (Lens.fst _ _))
  (.seq ((copyN (.inl 2) (pv 1) (pv 6)).liftRegs (Lens.fst _ _))
  (.seq (callInj ιsh (Lens.snd _ _) Psh)
  (.seq ((mulN (pv 1) (.inl 3) (.inl 7) (pv 2) (pv 3) (pv 4) (pv 5)).liftRegs (Lens.fst _ _))
  (.seq ((dropF (pv 1)).liftRegs (Lens.fst _ _))
    ((dropF (pv 0)).liftRegs (Lens.fst _ _)))))))))))

theorem closed_setupProg {ms : ℕ} {Rsh : Type} {Psh : Prog (Loc 2 ms) (fun _ => Sym) Rsh}
    (h : Psh.Closed) : (setupProg Psh).Closed :=
  ⟨WP.W9comp.closed_liftRegs _ (closed_pushMark _),
    WP.W9comp.closed_liftRegs _ (closed_mulN _ _ _ _ _ _ _),
    WP.W9comp.closed_liftRegs _ (closed_copyN _ _ _),
    WP.W9comp.closed_liftRegs _ (closed_copyN _ _ _),
    WP.W9comp.closed_liftRegs _ (closed_copyN _ _ _),
    WP.W9comp.closed_liftRegs _ (closed_pushMark _),
    WP.W9comp.closed_liftRegs _ (closed_copyN _ _ _),
    closed_callInj _ _ h,
    WP.W9comp.closed_liftRegs _ (closed_mulN _ _ _ _ _ _ _),
    WP.W9comp.closed_liftRegs _ (closed_dropF _),
    WP.W9comp.closed_liftRegs _ (closed_dropF _)⟩

/-! ## The run -/

section Run

variable {ms : ℕ} {Rsh : Type} {Psh : Prog (Loc 2 ms) (fun _ => Sym) Rsh}

/-- The counter program runs as specified (cost given step by step). -/
theorem setup_runs {Csh : ℕ}
    (hsh : ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 ms → List Sym), TermOK rx → TermOK rc →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
      Runs Psh S (Function.update S (.inl 0) (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
        (Csh * (c + bitLen c + 1)))
    (K f N1 N2 : ℕ) (r0 r1 r2 r3 : List Sym) (S : KLoc (Fin 8) (SE ms) → List Sym)
    (hr0 : TermOK r0) (hr1 : TermOK r1) (hr2 : TermOK r2) (hr3 : TermOK r3)
    (hS0 : S (.inl 0) = natSyms K ++ r0) (hS1 : S (.inl 1) = natSyms f ++ r1)
    (hS2 : S (.inl 2) = natSyms N1 ++ r2) (hS3 : S (.inl 3) = natSyms N2 ++ r3) :
    Runs (setupProg Psh) S
      (Function.update (Function.update (Function.update (Function.update S
        (.inl 4) (natSyms (f * K) ++ S (.inl 4))) (.inl 5) (natSyms (f * K) ++ S (.inl 5)))
        (.inl 6) (natSyms (f * K) ++ S (.inl 6)))
        (.inl 7) (natSyms (N1 * 2 ^ (f * K) * N2) ++ S (.inl 7)))
      (fun _ => True)
      (1 + (mulCost f K + ((7 * bitLen (f * K) + 7) + ((7 * bitLen (f * K) + 7) +
        ((7 * bitLen (f * K) + 7) + (1 + ((7 * bitLen N1 + 7) +
        (Csh * (f * K + bitLen (f * K) + 1) + (mulCost (N1 * 2 ^ (f * K)) N2 +
        ((2 * bitLen (N1 * 2 ^ (f * K)) + 2) + (2 * bitLen (f * K) + 2))))))))))) := by
  have hmk : ∀ x, TermOK (Sym.mark :: x) := termOK_mark
  -- 1. floor on `P1`
  have e1 := WP.W9mp.runs_liftRegs (Lens.fst Reg Rsh) (runs_pushMark (pv 0) S)
  set s1 := Function.update S (pv 0) (Sym.mark :: S (pv 0)) with hs1
  -- 2. `P1 ← f·K`
  have e2 := WP.W9mp.runs_liftRegs (Lens.fst Reg Rsh)
    (runs_mulN (x := .inl 1) (y := .inl 0) (z := pv 0) (A := pv 2) (Bs := pv 3) (Acc := pv 4)
      (T := pv 5) (by simp [pv]) f K r1 r0 s1 hr1 hr0 (by simp [hs1, pv, hS1])
      (by simp [hs1, pv, hS0]))
  have h1P : s1 (pv 0) = Sym.mark :: S (pv 0) := by simp [hs1]
  rw [h1P] at e2
  set s2 := Function.update s1 (pv 0) (natSyms (f * K) ++ Sym.mark :: S (pv 0)) with hs2
  have h2P : s2 (pv 0) = natSyms (f * K) ++ Sym.mark :: S (pv 0) := by simp [hs2]
  have h2P' : s2 (.inr (.inl 0)) = natSyms (f * K) ++ Sym.mark :: S (.inr (.inl 0)) := h2P
  -- 3. three copies of `L`
  have e3 := WP.W9mp.runs_liftRegs (Lens.fst Reg Rsh)
    (runs_copyN (src := pv 0) (dst := .inl 4) (tmp := pv 6) (by simp [pv]) (by simp [pv])
      (by simp [pv]) (f * K) (Sym.mark :: S (pv 0)) s2 (hmk _) h2P)
  have h2L1 : s2 (.inl 4) = S (.inl 4) := by simp [hs2, hs1, pv]
  rw [h2L1] at e3
  set s3 := Function.update s2 (.inl 4) (natSyms (f * K) ++ S (.inl 4)) with hs3
  have e4 := WP.W9mp.runs_liftRegs (Lens.fst Reg Rsh)
    (runs_copyN (src := pv 0) (dst := .inl 5) (tmp := pv 6) (by simp [pv]) (by simp [pv])
      (by simp [pv]) (f * K) (Sym.mark :: S (pv 0)) s3 (hmk _) (by simp [hs3, h2P', pv]))
  have h3L2 : s3 (.inl 5) = S (.inl 5) := by simp [hs3, hs2, hs1, pv]
  rw [h3L2] at e4
  set s4 := Function.update s3 (.inl 5) (natSyms (f * K) ++ S (.inl 5)) with hs4
  have e5 := WP.W9mp.runs_liftRegs (Lens.fst Reg Rsh)
    (runs_copyN (src := pv 0) (dst := .inl 6) (tmp := pv 6) (by simp [pv]) (by simp [pv])
      (by simp [pv]) (f * K) (Sym.mark :: S (pv 0)) s4 (hmk _) (by simp [hs4, hs3, h2P', pv]))
  have h4L3 : s4 (.inl 6) = S (.inl 6) := by simp [hs4, hs3, hs2, hs1, pv]
  rw [h4L3] at e5
  set s5 := Function.update s4 (.inl 6) (natSyms (f * K) ++ S (.inl 6)) with hs5
  -- 4. floor on `P2`, `P2 ← N1`
  have e6 := WP.W9mp.runs_liftRegs (Lens.fst Reg Rsh) (runs_pushMark (pv 1) s5)
  have h5P2 : s5 (pv 1) = S (pv 1) := by simp [hs5, hs4, hs3, hs2, hs1, pv]
  rw [h5P2] at e6
  set s6 := Function.update s5 (pv 1) (Sym.mark :: S (pv 1)) with hs6
  have e7 := WP.W9mp.runs_liftRegs (Lens.fst Reg Rsh)
    (runs_copyN (src := .inl 2) (dst := pv 1) (tmp := pv 6) (by simp [pv]) (by simp [pv])
      (by simp [pv]) N1 r2 s6 hr2 (by simp [hs6, hs5, hs4, hs3, hs2, hs1, pv, hS2]))
  have h6P2 : s6 (pv 1) = Sym.mark :: S (pv 1) := by simp [hs6]
  rw [h6P2] at e7
  set s7 := Function.update s6 (pv 1) (natSyms N1 ++ Sym.mark :: S (pv 1)) with hs7
  -- 5. `P2 ← N1·2^L`
  have e8' := hsh N1 (f * K) (Sym.mark :: S (pv 1)) (Sym.mark :: S (pv 0)) (s7 ∘ ιsh) (hmk _)
    (hmk _) (by show s7 (pv 1) = _; simp [hs7])
    (by show s7 (pv 0) = _; simp [hs7, hs6, hs5, hs4, hs3, h2P', pv])
  have e8 := AppC.C7LinesAux.runs_call_upd1 (ιsh_injective (ms := ms)) (Lens.snd Reg Rsh)
    (.inl 0) _ e8'
  set s8 := Function.update s7 (pv 1) (natSyms (N1 * 2 ^ (f * K)) ++ Sym.mark :: S (pv 1))
    with hs8
  have e8s : Runs (callInj ιsh (Lens.snd Reg Rsh) Psh) s7 s8 (fun _ => True)
      (Csh * (f * K + bitLen (f * K) + 1)) := e8
  -- 6. `G ← P2·N2`
  have e9 := WP.W9mp.runs_liftRegs (Lens.fst Reg Rsh)
    (runs_mulN (x := pv 1) (y := .inl 3) (z := .inl 7) (A := pv 2) (Bs := pv 3) (Acc := pv 4)
      (T := pv 5) (by simp [pv]) (N1 * 2 ^ (f * K)) N2 (Sym.mark :: S (pv 1)) r3 s8 (hmk _) hr3
      (by simp [hs8]) (by simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, pv, hS3]))
  have h8G : s8 (.inl 7) = S (.inl 7) := by simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, pv]
  rw [h8G] at e9
  set s9 := Function.update s8 (.inl 7) (natSyms (N1 * 2 ^ (f * K) * N2) ++ S (.inl 7)) with hs9
  -- 7. drop `P2` and `P1` with their floors
  have e10 := WP.W9mp.runs_liftRegs (Lens.fst Reg Rsh)
    (runs_dropF (pv 1) (N1 * 2 ^ (f * K)) Sym.mark (S (pv 1)) s9 rfl (by simp [hs9, hs8, pv]))
  set s10 := Function.update s9 (pv 1) (S (pv 1)) with hs10
  have e11 := WP.W9mp.runs_liftRegs (Lens.fst Reg Rsh)
    (runs_dropF (pv 0) (f * K) Sym.mark (S (pv 0)) s10 rfl
      (by simp [hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, h2P', pv]))
  have X := WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq e2 (WP.W9comp.runs_seq e3
    (WP.W9comp.runs_seq e4 (WP.W9comp.runs_seq e5 (WP.W9comp.runs_seq e6
    (WP.W9comp.runs_seq e7 (WP.W9comp.runs_seq e8s (WP.W9comp.runs_seq e9
    (WP.W9comp.runs_seq e10 e11)))))))))
  refine WP.W9comp.runs_congr X ?_
  funext x
  rcases x with i | i | j
  · fin_cases i <;> simp [hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, pv]
  · fin_cases i <;> simp [hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, pv]
  · simp [hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, pv]

end Run

/-! ## Cost -/

/-- The counter kernel's cost is at most `(1100 + 3·C_sh)·X²`, `X = fK + |K| + |f| + |N1| + |N2| + 1`. -/
theorem setup_cost_le' (Csh K f N1 N2 : ℕ) :
    1 + (mulCost f K + ((7 * bitLen (f * K) + 7) + ((7 * bitLen (f * K) + 7) +
      ((7 * bitLen (f * K) + 7) + (1 + ((7 * bitLen N1 + 7) +
      (Csh * (f * K + bitLen (f * K) + 1) + (mulCost (N1 * 2 ^ (f * K)) N2 +
      ((2 * bitLen (N1 * 2 ^ (f * K)) + 2) + (2 * bitLen (f * K) + 2)))))))))) ≤
    (1100 + 3 * Csh) * (f * K + bitLen K + bitLen f + bitLen N1 + bitLen N2 + 1) ^ 2 := by
  set X := f * K + bitLen K + bitLen f + bitLen N1 + bitLen N2 + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hL : bitLen (f * K) ≤ f * K := AppC.C7LinesAux.bitLen_le_self' _
  have hB : bitLen (N1 * 2 ^ (f * K)) ≤ bitLen N1 + f * K := bitLen_mul_two_pow_le N1 (f * K)
  have hLX : bitLen (f * K) ≤ X := by omega
  have hN1X : bitLen N1 ≤ X := by omega
  have hBX : bitLen (N1 * 2 ^ (f * K)) ≤ X := by omega
  have hm1 : mulCost f K ≤ 200 * X ^ 2 := by
    unfold mulCost
    have h1 : bitLen f + 1 ≤ X := by omega
    have h2 : bitLen f + bitLen K + 2 ≤ 2 * X := by omega
    calc 100 * (bitLen f + 1) * (bitLen f + bitLen K + 2) ≤ 100 * X * (2 * X) := by gcongr
      _ = 200 * X ^ 2 := by ring
  have hm2 : mulCost (N1 * 2 ^ (f * K)) N2 ≤ 800 * X ^ 2 := by
    unfold mulCost
    have h1 : bitLen (N1 * 2 ^ (f * K)) + 1 ≤ 2 * X := by omega
    have h2 : bitLen (N1 * 2 ^ (f * K)) + bitLen N2 + 2 ≤ 4 * X := by omega
    calc 100 * (bitLen (N1 * 2 ^ (f * K)) + 1) * (bitLen (N1 * 2 ^ (f * K)) + bitLen N2 + 2)
        ≤ 100 * (2 * X) * (4 * X) := by gcongr
      _ = 800 * X ^ 2 := by ring
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hc : Csh * (f * K + bitLen (f * K) + 1) ≤ 3 * Csh * X ^ 2 := by
    have : f * K + bitLen (f * K) + 1 ≤ 3 * X ^ 2 := by omega
    calc Csh * (f * K + bitLen (f * K) + 1) ≤ Csh * (3 * X ^ 2) := Nat.mul_le_mul_left _ this
      _ = 3 * Csh * X ^ 2 := by ring
  nlinarith

end AppC.C7LinesSetupAux

open AppC.C7LinesSetupAux

/-- **The counter kernel of the Lemma A.9 lines** (`c7LinesSetup_holds`, 0 `sorry`): `C7LinesSetupStmt`,
from `NatArith` (`mulN`, `copyN`, `pushMark`, `dropF`) and `TMFw.W3s.W3_shlVar_holds`. -/
theorem c7LinesSetup_holds : C7LinesSetupStmt := by
  obtain ⟨Csh, hCsh⟩ := TMFw.W3s.W3_shlVar_holds
  obtain ⟨ms, Rsh, obs, Psh, hms, hRf, hRn, hcl, hsh⟩ := hCsh ()
  refine ⟨1100 + 3 * Csh, fun _ => ⟨SE ms, inferInstance, inferInstance, NatArith.Reg × Rsh,
    setupProg Psh, inferInstance, inferInstance, closed_setupProg hcl, ?_⟩⟩
  intro K f N1 N2 r0 r1 r2 r3 S hr0 hr1 hr2 hr3 hS0 hS1 hS2 hS3
  exact WP.W9comp.runs_mono
    (setup_runs hsh K f N1 N2 r0 r1 r2 r3 S hr0 hr1 hr2 hr3 hS0 hS1 hS2 hS3)
    (fun _ _ => trivial) (setup_cost_le' Csh K f N1 N2)

/-- **Lemma A.9 phase 1, the eight packed lines, from its two remaining leaves** (`c7Lines_holds`,
0 `sorry`): the Lemma A.8 interchange `C6InterchangeStmt τ` and the Lemma A.9 offset routines
`K4OffsetCtlParStmt (lineOff ε par xF) J` for `ε = ±1`, `par ≤ 1`. -/
theorem c7Lines_holds (τ : ℝ) (σ : Equiv.Perm (Fin 3)) (J : ℕ) (hC6 : C6InterchangeStmt τ)
    (hOff : ∀ (ε : ℤ) (par : ℕ) (xF : Bool), (ε = 1 ∨ ε = -1) → par ≤ 1 →
      K4OffsetCtlParStmt (AppC.C7LinesAux.lineOff ε par xF) J) :
    C7LinesStmt τ σ :=
  c7Lines_of τ σ J hC6 hOff c7LinesSetup_holds

end SubNLogN.Machine
