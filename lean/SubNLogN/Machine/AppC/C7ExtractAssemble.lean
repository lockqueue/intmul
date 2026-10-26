/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7ExtractRecC
import SubNLogN.Machine.AppC.C7ExtractSetup
import SubNLogN.Machine.AppC.C7ExtractAssembleKit
import SubNLogN.Machine.AppC.C7ExtractAssembleCost

/-!
# Lemma A.9 extraction, assembly (`Machine/AppC/C7ExtractAssemble.lean`)

**Scope.** Proves `SubNLogN.Machine.c7Extract_of_parts`: `C7ExtractStmt σ`
(`Machine/AppC/C7RepairDefs.lean`; Lemma A.9 (`lem:transfer13`)) from three
component contracts, which enter as explicit hypotheses:
* `C7BadTriStmt` (`C7BadTri.lean`), the triple sub-kernel;
* `C7XSetupStmt` and `C7XCostStmt` (`C7ExtractSetup.lean`), the setup phase and the pure cost
  inequality.
Nothing else is assumed (no `sorry`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

The kernel is `setup ; countdown (record body) ; cleanup` (`topP`) on the layout `XK E'`, over the
kit `natKit` extended by the registers of the triple kernel (`kitExt`, `C7ExtractAssembleKit.lean`).
* The main loop (`runs_loop`) uses the state family `stF n`: the buffer `T` holds the reversed first
  `n` records above `sep`, the skeleton `H` holds the hole segments of records `n, …, M-1` above
  `tag 15`, and the bank `Bk` holds the bank segments above `tag 14`. The per-record body is
  `runs_recBody` (`C7ExtractRecC.lean`). The triple kernel is `tri`, and its `TriSpec` comes from
  `runs_tri`.
* `cleanupP` (`runs_cleanupP`) pops the two delimiters and drops the constants.
-/

namespace SubNLogN.Machine.AppC.C7XAux2

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.Calculus
  SubNLogN.Machine.AppC.C7ExtractAux SubNLogN.Machine.AppC.C7Aux
  SubNLogN.Machine.AppC.C7RepairAux.Math SubNLogN.Math.Networks SubNLogN.Machine.AppC.Corr
  SubNLogN.Machine.AppC.C7RadixAux

section Loop

variable {E' : Type} [DecidableEq E']

/-- Main-loop state with counter `n` (records `n, …, M-1` done), before the counter update. -/
def stF (S : XK E' → List Sym) (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3))
    (w : List (List Bool)) (rest : List Sym) (n : ℕ) : XK E' → List Sym :=
  Function.update (Function.update (Function.update (setupSt S K ρ f w rest)
    (wk .T) ((SubNLogN.Machine.arrSyms (w.take n)).reverse ++ Sym.sep :: S (wk .T)))
    sH (((List.range w.length).drop n).flatMap (hseg K ρ f N1 N2 N3 σ w) ++
      Sym.tag 15 :: S sH))
    sB (((List.range w.length).drop n).flatMap (bseg K ρ f N1 N2 N3 σ (Nat.size w.length) w) ++
      Sym.tag 14 :: S sB)

/-- Seven updates of `T, H, Bk, cM` collapse to four. -/
theorem upd7 (S0 : XK E' → List Sym) (t1 h1 b1 c t2 h2 b2 : List Sym) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update S0 (wk .T) t1) sH h1) sB b1) (wk .cM) c) (wk .T) t2)
      sH h2) sB b2 =
    Function.update (Function.update (Function.update (Function.update S0 (wk .T) t2) sH h2)
      sB b2) (wk .cM) c := by
  funext k
  simp only [Function.update_apply]
  by_cases h1 : k = sB
  · subst h1; simp
  · by_cases h2 : k = sH
    · subst h2; simp
    · by_cases h3 : k = wk .T
      · subst h3; simp
      · by_cases h4 : k = wk .cM
        · subst h4; simp
        · simp [h1, h2, h3, h4]

theorem stF_start (S : XK E' → List Sym) (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3))
    (w : List (List Bool)) (rest : List Sym) :
    Function.update (stF S K ρ f N1 N2 N3 σ w rest w.length) (wk .cM)
      (natSyms w.length ++ Sym.mark :: S (wk .cM)) = setupSt S K ρ f w rest := by
  have hd : (List.range w.length).drop w.length = [] := List.drop_of_length_le (by simp)
  have e1 : (SubNLogN.Machine.arrSyms (w.take w.length)).reverse ++ Sym.sep :: S (wk .T) =
      setupSt S K ρ f w rest (wk .T) := by
    rw [List.take_length]; simp [setupSt, Function.update_apply]
  have e2 : ((List.range w.length).drop w.length).flatMap (hseg K ρ f N1 N2 N3 σ w) ++
      Sym.tag 15 :: S sH = setupSt S K ρ f w rest sH := by
    rw [hd]; simp [setupSt, Function.update_apply]
  have e3 : ((List.range w.length).drop w.length).flatMap
      (bseg K ρ f N1 N2 N3 σ (Nat.size w.length) w) ++ Sym.tag 14 :: S sB =
      setupSt S K ρ f w rest sB := by
    rw [hd]; simp [setupSt, Function.update_apply]
  have e4 : natSyms w.length ++ Sym.mark :: S (wk .cM) = setupSt S K ρ f w rest (wk .cM) := by
    simp [setupSt, Function.update_apply]
  unfold stF
  rw [e1, e2, e3, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self, e4,
    Function.update_eq_self]

/-- The record count `M = c7M …` dominates `2^{fK}`, `N1`, `N2`, `N3`. -/
theorem c7M_ge (K f N0 N1 N2 N3 : ℕ) (hN0 : 1 ≤ N0) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2)
    (hN3 : 1 ≤ N3) :
    2 ^ (f * K) ≤ c7M K f N0 N1 N2 N3 ∧ N1 ≤ c7M K f N0 N1 N2 N3 ∧
      N2 ≤ c7M K f N0 N1 N2 N3 ∧ N3 ≤ c7M K f N0 N1 N2 N3 := by
  have hP : 0 < 2 ^ (f * K) := Nat.two_pow_pos _
  unfold c7M
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc 2 ^ (f * K) ≤ N0 * 2 ^ (f * K) := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ N0 * 2 ^ (f * K) * N1 := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) := Nat.le_mul_of_pos_right _ hP
      _ ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) :=
          Nat.le_mul_of_pos_right _ hP
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  · calc N1 ≤ N0 * 2 ^ (f * K) * N1 := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hP)
      _ ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) := Nat.le_mul_of_pos_right _ hP
      _ ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) :=
          Nat.le_mul_of_pos_right _ hP
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  · calc N2 ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 :=
          Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hP)
            (by omega)) hP)
      _ ≤ N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) :=
          Nat.le_mul_of_pos_right _ hP
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  · exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos
      (Nat.mul_pos (by omega) hP) (by omega)) hP) (by omega)) hP)

set_option maxHeartbeats 4000000 in
/-- **The main loop**: from the setup state, the countdown over the `M` records leaves the buffer
`T` at `sep`, the skeleton with all hole segments, the bank with all bank segments, and the
counter at its floor. -/
theorem runs_loop (xk : XKit (XK E')) (σ : Equiv.Perm (Fin 3))
    (tri : Prog (XK E') (fun _ => Sym) xk.R) (Ct K ρ f N0 N1 N2 N3 R : ℕ)
    (w : List (List Bool)) (rest r1 r2 r3 r4 r5 r6 : List Sym) (S : XK E' → List Sym)
    (htri : TriSpec xk tri Ct K ρ f)
    (hK : 6 ≤ K) (hρ : ρ < K) (hf : 1 ≤ f) (hN0 : 1 ≤ N0) (hN1 : 1 ≤ N1) (hN2 : 1 ≤ N2)
    (hN3 : 1 ≤ N3) (hw : w.length = c7M K f N0 N1 N2 N3) (hwR : ∀ p ∈ w, p.length = R)
    (hr1 : TermOK r1) (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4) (hr5 : TermOK r5)
    (hr6 : TermOK r6)
    (hS1 : S sK = natSyms K ++ r1) (hS2 : S sRho = natSyms ρ ++ r2)
    (hS3 : S sF = natSyms f ++ r3) (hS4 : S sN1 = natSyms N1 ++ r4)
    (hS5 : S sN2 = natSyms N2 ++ r5) (hS6 : S sN3 = natSyms N3 ++ r6) :
    Runs (countdown xk.lw (wk .cM) (wk .u5) (recBody xk σ tri)) (setupSt S K ρ f w rest)
      (Function.update (stF S K ρ f N1 N2 N3 σ w rest 0) (wk .cM) (Sym.mark :: S (wk .cM)))
      (fun _ => True)
      (countdownCost (fun _ => recCost xk (Nat.size w.length + 2) f (f * K) Ct R
        (Nat.size w.length)) w.length) := by
  obtain ⟨hM2, hM1, hM2', hM3⟩ := c7M_ge K f N0 N1 N2 N3 hN0 hN1 hN2 hN3
  rw [← hw] at hM2 hM1 hM2' hM3
  have hA : f * K < Nat.size w.length := Nat.lt_size.mpr hM2
  have hMA : w.length < 2 ^ Nat.size w.length := Nat.lt_size_self _
  have hAnb : 2 ^ Nat.size w.length ≤ 2 ^ (Nat.size w.length + 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAA : 2 ^ Nat.size w.length + 2 ^ Nat.size w.length ≤ 2 ^ (Nat.size w.length + 2) := by
    rw [pow_succ, pow_succ]; omega
  have hbody : ∀ n, n < w.length →
      RunsIn [] (recBody xk σ tri)
        (Function.update (stF S K ρ f N1 N2 N3 σ w rest (n + 1)) (wk .cM)
          (natSyms (n + 1) ++ Sym.mark :: S (wk .cM)))
        (Function.update (stF S K ρ f N1 N2 N3 σ w rest n) (wk .cM)
          (natSyms (n + 1) ++ Sym.mark :: S (wk .cM)))
        (fun _ => True)
        (recCost xk (Nat.size w.length + 2) f (f * K) Ct R (Nat.size w.length)) := by
    intro n hn
    have hmem : w[n] ∈ w := List.getElem_mem hn
    have hlen : w[n].length = R := hwR _ hmem
    have hd : c7Dest K ρ f N1 N2 N3 σ n < 2 ^ Nat.size w.length := by
      have := dest_lt K ρ f N0 N1 N2 N3 σ (by omega) hρ hf (by omega) (by omega) (by omega)
        (n := n) (by rw [← hw]; exact hn)
      rw [← hw] at this
      omega
    have hb := runs_recBody xk σ tri Ct K ρ f N1 N2 N3 (Nat.size w.length)
      (Nat.size w.length + 2) n w[n]
      ((SubNLogN.Machine.arrSyms (w.take n)).reverse ++ Sym.sep :: S (wk .T))
      (Sym.mark :: S (wk .cM))
      (Function.update (stF S K ρ f N1 N2 N3 σ w rest (n + 1)) (wk .cM)
        (natSyms (n + 1) ++ Sym.mark :: S (wk .cM)))
      htri hK hρ hf hN1 hN2 hN3 (by omega) (by omega) (by omega) (by omega) (by omega) hd hAA
      ⟨r1, hr1, by simp [stF, setupSt, Function.update_apply, hS1]⟩
      ⟨r2, hr2, by simp [stF, setupSt, Function.update_apply, hS2]⟩
      ⟨r3, hr3, by simp [stF, setupSt, Function.update_apply, hS3]⟩
      ⟨r4, hr4, by simp [stF, setupSt, Function.update_apply, hS4]⟩
      ⟨r5, hr5, by simp [stF, setupSt, Function.update_apply, hS5]⟩
      ⟨r6, hr6, by simp [stF, setupSt, Function.update_apply, hS6]⟩
      ⟨Sym.mark :: S (wk .cL), termOK_mark _, by simp [stF, setupSt, Function.update_apply]⟩
      ⟨Sym.mark :: S (wk .c2L), termOK_mark _, by simp [stF, setupSt, Function.update_apply]⟩
      ⟨Sym.mark :: S (wk .c2K), termOK_mark _, by simp [stF, setupSt, Function.update_apply]⟩
      ⟨Sym.mark :: S (wk .c2K1), termOK_mark _, by simp [stF, setupSt, Function.update_apply]⟩
      ⟨Sym.mark :: S (wk .c2r), termOK_mark _, by simp [stF, setupSt, Function.update_apply]⟩
      ⟨Sym.mark :: S (wk .c2r1), termOK_mark _, by simp [stF, setupSt, Function.update_apply]⟩
      ⟨Sym.mark :: S (wk .cF1), termOK_mark _, by simp [stF, setupSt, Function.update_apply]⟩
      ⟨Sym.mark :: S (wk .c10), termOK_mark _, by simp [stF, setupSt, Function.update_apply]⟩
      ⟨Sym.mark :: S (wk .c11), termOK_mark _, by simp [stF, setupSt, Function.update_apply]⟩
      ⟨Sym.mark :: S (wk .c1), termOK_mark _, by simp [stF, setupSt, Function.update_apply]⟩
      ⟨Sym.mark :: S (wk .c2A), termOK_mark _, by simp [stF, setupSt, Function.update_apply]⟩
      (termOK_mark _) (Function.update_self _ _ _)
      (by
        rw [show (Function.update (stF S K ρ f N1 N2 N3 σ w rest (n + 1)) (wk .cM)
            (natSyms (n + 1) ++ Sym.mark :: S (wk .cM))) (wk .T) =
            (SubNLogN.Machine.arrSyms (w.take (n + 1))).reverse ++ Sym.sep :: S (wk .T) by
          simp [stF, Function.update_apply], rev_arr_take_succ w n hn]
        rfl)
      (rev_arr_sep (w.take n) (S (wk .T)))
    rw [hlen] at hb
    refine WP.W9comp.runs_congr hb ?_
    have eH : (Function.update (stF S K ρ f N1 N2 N3 σ w rest (n + 1)) (wk .cM)
        (natSyms (n + 1) ++ Sym.mark :: S (wk .cM))) sH =
        ((List.range w.length).drop (n + 1)).flatMap (hseg K ρ f N1 N2 N3 σ w) ++
          Sym.tag 15 :: S sH := by
      simp [stF, Function.update_apply]
    have eB : (Function.update (stF S K ρ f N1 N2 N3 σ w rest (n + 1)) (wk .cM)
        (natSyms (n + 1) ++ Sym.mark :: S (wk .cM))) sB =
        ((List.range w.length).drop (n + 1)).flatMap
          (bseg K ρ f N1 N2 N3 σ (Nat.size w.length) w) ++ Sym.tag 14 :: S sB := by
      simp [stF, Function.update_apply]
    have v1 : (if badB K ρ f N1 N2 N3 σ n then [Sym.tag 8] else SubNLogN.Machine.recSyms w[n]) ++
        (((List.range w.length).drop (n + 1)).flatMap (hseg K ρ f N1 N2 N3 σ w) ++
          Sym.tag 15 :: S sH) =
        ((List.range w.length).drop n).flatMap (hseg K ρ f N1 N2 N3 σ w) ++
          Sym.tag 15 :: S sH := by
      rw [flatMap_drop_succ _ _ _ hn, List.append_assoc]
      congr 1
      simp only [hseg, List.getD_eq_getElem _ _ hn]
    have v2 : (if badB K ρ f N1 N2 N3 σ n then
          keyedSyms (bitsLE (Nat.size w.length) (c7Dest K ρ f N1 N2 N3 σ n), w[n]) else []) ++
        (((List.range w.length).drop (n + 1)).flatMap
          (bseg K ρ f N1 N2 N3 σ (Nat.size w.length) w) ++ Sym.tag 14 :: S sB) =
        ((List.range w.length).drop n).flatMap (bseg K ρ f N1 N2 N3 σ (Nat.size w.length) w) ++
          Sym.tag 14 :: S sB := by
      rw [flatMap_drop_succ _ _ _ hn, List.append_assoc]
      congr 1
      simp only [bseg, List.getD_eq_getElem _ _ hn]
    rw [eH, eB, v1, v2]
    unfold stF
    exact upd7 _ _ _ _ _ _ _ _
  have h := runsIn_countdown (ρ := []) xk.lw (c := wk .cM) (t := wk .u5) (by simp)
    (body := recBody xk σ tri) w.length (Sym.mark :: S (wk .cM)) (termOK_mark _)
    (stF S K ρ f N1 N2 N3 σ w rest)
    (fun _ => recCost xk (Nat.size w.length + 2) f (f * K) Ct R (Nat.size w.length)) hbody
  rw [stF_start] at h
  exact WP.W9comp.runs_mono (RunsIn.iff_runs.mp h) (fun _ _ => trivial) le_rfl

end Loop

/-! ## The assembled kernel -/

/-- The kit of the assembled kernel: `natKit` with the triple kernel's registers. -/
def xkE (E' R' : Type) [DecidableEq E'] (hf : Finite R') (hn : Nonempty R') : XKit (XK E') :=
  kitExt (natKit (XK E')) R' hf hn

/-- The assembled program: setup, the countdown over the records, cleanup. -/
def topP {E' : Type} [DecidableEq E'] (xk : XKit (XK E')) (σ : Equiv.Perm (Fin 3))
    (Ps tri : Prog (XK E') (fun _ => Sym) xk.R) : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq Ps (.seq (countdown xk.lw (wk .cM) (wk .u5) (recBody xk σ tri)) (cleanupP xk))

end SubNLogN.Machine.AppC.C7XAux2

namespace SubNLogN.Machine

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.Calculus
  SubNLogN.Machine.AppC.C7ExtractAux SubNLogN.Machine.AppC.C7XAux2 SubNLogN.Machine.AppC.C7Aux
  SubNLogN.Machine.AppC.C7RepairAux SubNLogN.Machine.AppC.C7RepairAux.Math

set_option maxHeartbeats 8000000 in
/-- **Lemma A.9 extraction from its parts** (`C7ExtractStmt σ`, `Machine/AppC/C7RepairDefs.lean`;
Lemma A.9 (`lem:transfer13`)). The three component contracts enter as explicit
hypotheses: the triple sub-kernel `C7BadTriStmt`, the setup phase `C7XSetupStmt`, and the cost
inequality `C7XCostStmt`. The constant is the `Cf` of `C7XCostStmt` at kit constant `110` and
triple constant `Ct`. -/
theorem c7Extract_of_parts (σ : Equiv.Perm (Fin 3)) (hTri : C7BadTriStmt)
    (hSet : C7XSetupStmt) (hCost : C7XCostStmt) : C7ExtractStmt σ := by
  obtain ⟨Ct, hT⟩ := hTri
  obtain ⟨Cf, hCf⟩ := hCost 110 Ct
  refine ⟨Cf, fun _ => ?_⟩
  obtain ⟨E', hFE, hDE, R', Pt, hRf, hRn, hPc, hPt⟩ := hT ()
  obtain ⟨Ps, hPsc, hPs⟩ := hSet E' (xkE E' R' hRf hRn)
  refine ⟨XW ⊕ E', inferInstance, inferInstance, (xkE E' R' hRf hRn).R,
    topP (xkE E' R' hRf hRn) σ Ps (tri (natKit (XK E')) R' hRf hRn Pt),
    (xkE E' R' hRf hRn).finR, (xkE E' R' hRf hRn).neR,
    ⟨hPsc, closed_countdown _ _ _ (closed_recBody (xkE E' R' hRf hRn) σ
      (tri_closed (natKit (XK E')) R' hRf hRn hPc)), closed_cleanupP _⟩, ?_⟩
  intro K ρ f N0 N1 N2 N3 R w rest r1 r2 r3 r4 r5 r6 r7 S hK hρ hf hN0 hN1 hN2 hN3 hR hw hwR
    hrest hr1 hr2 hr3 hr4 hr5 hr6 hr7 hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS7
  have h1 := hPs K ρ f N0 N1 N2 N3 R w rest r1 r2 r3 r4 r5 r6 r7 S hK hρ hf hN0 hN1 hN2 hN3 hR hw
    hwR hrest hr1 hr2 hr3 hr4 hr5 hr6 hr7 hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS7
  have htri : TriSpec (xkE E' R' hRf hRn) (tri (natKit (XK E')) R' hRf hRn Pt) Ct K ρ f :=
    runs_tri (natKit (XK E')) R' hRf hRn Pt Ct hPt K ρ f hK hρ hf
  have h2 := runs_loop (xkE E' R' hRf hRn) σ (tri (natKit (XK E')) R' hRf hRn Pt) Ct K ρ f N0 N1
    N2 N3 R w rest r1 r2 r3 r4 r5 r6 S htri hK hρ hf hN0 hN1 hN2 hN3 hw hwR hr1 hr2 hr3 hr4 hr5 hr6
    hS1 hS2 hS3 hS4 hS5 hS6
  have h3 := runs_cleanupP (xkE E' R' hRf hRn)
    (Function.update (stF S K ρ f N1 N2 N3 σ w rest 0) (wk .cM) (Sym.mark :: S (wk .cM)))
    (vc1 := 1) (vc10 := 10) (vc11 := 11) (vcL := f * K) (vc2L := 2 ^ (f * K)) (vc2K := 2 ^ K)
    (vc2K1 := 2 ^ (K - 1)) (vc2r := 2 ^ ρ) (vc2r1 := 2 ^ (ρ + 1)) (vcF1 := f - 1)
    (vc2A := 2 ^ Nat.size w.length) (vcA := Nat.size w.length)
    (rcM := S (wk .cM)) (rT := S (wk .T)) (rc1 := S (wk .c1)) (rc10 := S (wk .c10))
    (rc11 := S (wk .c11)) (rcL := S (wk .cL)) (rc2L := S (wk .c2L)) (rc2K := S (wk .c2K))
    (rc2K1 := S (wk .c2K1)) (rc2r := S (wk .c2r)) (rc2r1 := S (wk .c2r1)) (rcF1 := S (wk .cF1))
    (rc2A := S (wk .c2A)) (rcA := S (wk .cA))
    (by simp [Function.update_apply])
    (by
      have ha0 : SubNLogN.Machine.arrSyms ([] : List (List Bool)) = [] := rfl
      simp [stF, setupSt, Function.update_apply, ha0])
    (by simp [stF, setupSt, Function.update_apply])
    (by simp [stF, setupSt, Function.update_apply])
    (by simp [stF, setupSt, Function.update_apply])
    (by simp [stF, setupSt, Function.update_apply])
    (by simp [stF, setupSt, Function.update_apply])
    (by simp [stF, setupSt, Function.update_apply])
    (by simp [stF, setupSt, Function.update_apply])
    (by simp [stF, setupSt, Function.update_apply])
    (by simp [stF, setupSt, Function.update_apply])
    (by simp [stF, setupSt, Function.update_apply])
    (by simp [stF, setupSt, Function.update_apply])
    (by simp [stF, setupSt, Function.update_apply])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h1
    (WP.W9comp.runs_seq h2 h3)) ?_) (fun _ _ => trivial)
    (AppC.C7XCostAux.c7x_cost_le (xkE E' R' hRf hRn) rfl Ct Cf K ρ f N0 N1 N2 N3 R w hCf hK hρ
      hf hN0 hN1 hN2 hN3 hR hw hwR)
  funext k
  rcases k with (k | k) | (x | e)
  · fin_cases k <;> simp [stF, setupSt, Function.update_apply, sArr, sK, sRho, sF, sN1, sN2,
      sN3, sR]
  · fin_cases k <;> simp [stF, setupSt, Function.update_apply, holeSyms_holes, bankSyms_bank,
      c7KeyWidth, sH, sB, sAc]
  · cases x <;> simp [stF, setupSt, Function.update_apply]
  · simp [stF, setupSt, Function.update_apply]

end SubNLogN.Machine
