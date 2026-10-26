/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6JoinMove

/-!
# Lemma A.8 join/unjoin: shared phases (`Machine/AppC/C6JoinCommon.lean`)

The setup and cleanup phases shared by the high join (`C6JoinHigh.lean`) and the unjoin, on the
layout `KJ E1` of `C6JoinMove.lean`. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

* `preT q`: `t := c6T q e` on `tS` (the threshold kernel), `ℓ := e - t` on `lS` (`runs_preT`).
* `mkPowJ q src Y ns`: `Y := a·q^n` (`runs_mkPowJ`).
* `setupJ q xs Y = preT; N1 := G·q^(n at xs); Y := B·q^ℓ`. It lands in `stA S t ℓ n1 Y y`
  (`runs_setupHJ`: `xs = 1`, `n1 = G·q^e`, `Y = PB`; `runs_setupUJ`: `xs = lS`, `n1 = G·q^ℓ`,
  `Y = N2`).
* `cleanJ Y`: drop the counters on `Y, N1, lS, tS` (`runs_cleanJ`); `stA_upd` replaces the
  counter on `Y`.

All helpers are in `SubNLogN.Machine.AppC.C6JoinAux`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

namespace AppC.C6JoinAux

open NatArith

/-- A `Runs` fact through a register lens (trivial register postcondition). -/
theorem runs_lift {K σ τ : Type} [DecidableEq K] (l : Lens σ τ) {P : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ} (h : Runs P S S' Q T) :
    Runs (P.liftRegs l) S S' (fun _ => True) T := by
  have h2 : Runs (P.liftRegs l) S S' (fun v => Q (l.get v)) T :=
    RunsIn.liftRegs l (RunsIn.iff_runs.2 h)
  exact WP.W9comp.runs_mono h2 (fun _ _ => trivial) le_rfl

section Programs

variable {E1 : Type} {R1 : Type}

/-- `t := c6T q e` on `tS` and `ℓ := e - t` on `lS` (each above a `mark`). -/
def preT (q : ℕ) : Prog (KJ E1) (fun _ => Sym) (RJ R1) :=
  .seq ((pushMark (jp .tS)).liftRegs (lN R1)) (.seq (callInj (ιT E1) (lN R1) (tKerP q))
    ((mkSub (.inl 1) (jp .tS) (jp .lS) (jp .Q) (jp .Td) (jp .A)).liftRegs (lN R1)))

/-- `Y := a·q^n` above a `mark` (`a` copied from `src`, `n` read from `ns`). -/
def mkPowJ (q : ℕ) (src : KJ E1) (Y : PS) (ns : KJ E1) : Prog (KJ E1) (fun _ => Sym) (RJ R1) :=
  (mkPow q src (jp Y) ns (jp .Kc2) (jp .Tm) (jp .Q) (jp .Td) (jp .A) (jp .Bs) (jp .Acc)).liftRegs
    (lN R1)

/-- The setup: `preT`, then `N1 := G·q^n` (`n` read from `xs`), `Y := B·q^ℓ`. -/
def setupJ (q : ℕ) (xs : KJ E1) (Y : PS) : Prog (KJ E1) (fun _ => Sym) (RJ R1) :=
  .seq (preT q) (.seq (mkPowJ q (.inl 2) .N1 xs) (mkPowJ q (.inl 3) Y (jp .lS)))

/-- Drop the counter on `Y`, then those on `N1`, `lS`, `tS` (with their floors). -/
def cleanJ (Y : PS) : Prog (KJ E1) (fun _ => Sym) (RJ R1) :=
  (Prog.seq (dropF (jp Y)) (.seq (dropF (jp .N1)) (.seq (dropF (jp .lS)) (dropF (jp .tS))))).liftRegs
    (lN R1)

theorem closed_preT (q : ℕ) : (preT (E1 := E1) (R1 := R1) q).Closed :=
  ⟨WP.W9comp.closed_liftRegs _ (closed_pushMark _), closed_callInj _ _ (closed_tKerP q),
    WP.W9comp.closed_liftRegs _ (closed_mkSub _ _ _ _ _ _)⟩

theorem closed_mkPowJ (q : ℕ) (src : KJ E1) (Y : PS) (ns : KJ E1) :
    (mkPowJ (R1 := R1) q src Y ns).Closed :=
  WP.W9comp.closed_liftRegs _ (closed_mkPow _ _ _ _ _ _ _ _ _ _ _)

theorem closed_setupJ (q : ℕ) (xs : KJ E1) (Y : PS) : (setupJ (R1 := R1) q xs Y).Closed :=
  ⟨closed_preT q, closed_mkPowJ _ _ _ _, closed_mkPowJ _ _ _ _⟩

theorem closed_cleanJ (Y : PS) : (cleanJ (E1 := E1) (R1 := R1) Y).Closed :=
  WP.W9comp.closed_liftRegs _ ⟨closed_dropF _, closed_dropF _, closed_dropF _, closed_dropF _⟩

end Programs

section Runs

variable {E1 : Type} [DecidableEq E1] {R1 : Type}

/-- The stacks after the setup: `t` on `tS`, `ℓ` on `lS`, `n1` on `N1`, `y` on `Y` (each above a
`mark`). -/
def stA (S : KJ E1 → List Sym) (t l n1 : ℕ) (Y : PS) (y : ℕ) : KJ E1 → List Sym :=
  Function.update (Function.update (Function.update (Function.update S (jp .tS)
    (natSyms t ++ Sym.mark :: S (jp .tS))) (jp .lS) (natSyms l ++ Sym.mark :: S (jp .lS)))
    (jp .N1) (natSyms n1 ++ Sym.mark :: S (jp .N1))) (jp Y) (natSyms y ++ Sym.mark :: S (jp Y))

/-- Replacing the counter on `Y` (the array stack being overridden). -/
theorem stA_upd (S : KJ E1 → List Sym) (t l n1 : ℕ) (Y : PS) (y y' : ℕ) (arr : List Sym) :
    Function.update (Function.update (stA S t l n1 Y y) (.inl 0) arr) (jp Y)
      (natSyms y' ++ Sym.mark :: S (jp Y)) = Function.update (stA S t l n1 Y y') (.inl 0) arr := by
  rw [Function.update_comm (inl_ne_jp Y 0)]
  simp only [stA, Function.update_idem]

/-- `preT`: `t` on `tS`, `ℓ = e - t` on `lS`. -/
theorem runs_preT {q : ℕ} (hq : 2 ≤ q) (e : ℕ) (r1 : List Sym) (S : KJ E1 → List Sym)
    (hr1 : TermOK r1) (he : c6T q e ≤ e) (hS1 : S (.inl 1) = natSyms e ++ r1) :
    Runs (preT (E1 := E1) (R1 := R1) q) S
      (Function.update (Function.update S (jp .tS) (natSyms (c6T q e) ++ Sym.mark :: S (jp .tS)))
        (jp .lS) (natSyms (e - c6T q e) ++ Sym.mark :: S (jp .lS))) (fun _ => True)
      (1 + (tCost q e + (1 + 20 * (bitLen e + bitLen (c6T q e) + 1)))) := by
  have a1 : Runs ((pushMark (jp .tS)).liftRegs (lN R1)) S
      (Function.update S (jp .tS) (Sym.mark :: S (jp .tS))) (fun _ => True) 1 :=
    runs_lift _ (runs_pushMark _ S)
  have a2 := runs_callT (R1 := R1) hq e r1 (Function.update S (jp .tS) (Sym.mark :: S (jp .tS)))
    hr1 (by rw [Function.update_of_ne (inl_ne_jp _ _)]; exact hS1)
  rw [Function.update_self, Function.update_idem] at a2
  have a3 := runs_lift (lN R1) (runs_mkSub (K := KJ E1) (x := .inl 1) (y := jp .tS)
    (z := jp .lS) (t1 := jp .Q) (t2 := jp .Td) (t3 := jp .A) (by simp) e (c6T q e) r1
    (Sym.mark :: S (jp .tS))
    (Function.update S (jp .tS) (natSyms (c6T q e) ++ Sym.mark :: S (jp .tS))) hr1
    (termOK_mark _) he (by rw [Function.update_of_ne (inl_ne_jp _ _)]; exact hS1)
    (Function.update_self _ _ _))
  rw [Function.update_of_ne (show (jp .lS : KJ E1) ≠ jp .tS by simp)] at a3
  exact WP.W9comp.runs_seq a1 (WP.W9comp.runs_seq a2 a3)

/-- `mkPowJ`: `Y := a·q^n` above a `mark`. -/
theorem runs_mkPowJ {q : ℕ} (hq : 1 ≤ q) {src ns : KJ E1} {Y : PS}
    (hnd : [jp Y, ns, jp .Kc2, jp .Tm, jp .Q, jp .Td, jp .A, jp .Bs, jp .Acc].Nodup)
    (hsY : src ≠ jp Y) (hsQ : src ≠ jp .Q) (a n : ℕ) (ra rn : List Sym) (S : KJ E1 → List Sym)
    (hra : TermOK ra) (hrn : TermOK rn) (hsrc : S src = natSyms a ++ ra)
    (hns : S ns = natSyms n ++ rn) :
    Runs (mkPowJ (R1 := R1) q src Y ns) S
      (Function.update S (jp Y) (natSyms (a * q ^ n) ++ Sym.mark :: S (jp Y))) (fun _ => True)
      (1 + ((7 * bitLen a + 7) + powCost q a n)) :=
  runs_lift _ (runs_mkPow hnd hsY hsQ hq a n ra rn S hra hrn hsrc hns)

/-- Cost of `preT`. -/
def costT (q e : ℕ) : ℕ := 1 + (tCost q e + (1 + 20 * (bitLen e + bitLen (c6T q e) + 1)))

/-- Cost of `mkPowJ` (`Y := a·q^n`). -/
def costP (q a n : ℕ) : ℕ := 1 + ((7 * bitLen a + 7) + powCost q a n)

/-- **Setup of the high join**: `N1 := G·q^e`, `PB := B·q^ℓ`. -/
theorem runs_setupHJ {q : ℕ} (hq : 2 ≤ q) (e G B : ℕ) (r1 r2 r3 : List Sym)
    (S : KJ E1 → List Sym) (hr1 : TermOK r1) (hr2 : TermOK r2) (hr3 : TermOK r3)
    (he : c6T q e ≤ e) (hS1 : S (.inl 1) = natSyms e ++ r1) (hS2 : S (.inl 2) = natSyms G ++ r2)
    (hS3 : S (.inl 3) = natSyms B ++ r3) :
    Runs (setupJ (R1 := R1) q (.inl 1) .PB) S
      (stA S (c6T q e) (e - c6T q e) (G * q ^ e) .PB (B * q ^ (e - c6T q e))) (fun _ => True)
      (costT q e + (costP q G e + costP q B (e - c6T q e))) := by
  have hq1 : 1 ≤ q := by omega
  have b1 := runs_preT (R1 := R1) hq e r1 S hr1 he hS1
  set S2 : KJ E1 → List Sym := Function.update (Function.update S (jp .tS)
    (natSyms (c6T q e) ++ Sym.mark :: S (jp .tS))) (jp .lS)
    (natSyms (e - c6T q e) ++ Sym.mark :: S (jp .lS)) with hS2def
  have b2 := runs_mkPowJ (R1 := R1) (q := q) hq1 (src := .inl 2) (ns := .inl 1) (Y := .N1)
    (by simp) (by simp) (by simp) G e r2 r1 S2 hr2 hr1 (by simp [hS2def, hS2])
    (by simp [hS2def, hS1])
  rw [show S2 (jp .N1) = S (jp .N1) by simp [hS2def]] at b2
  set S3 : KJ E1 → List Sym :=
    Function.update S2 (jp .N1) (natSyms (G * q ^ e) ++ Sym.mark :: S (jp .N1)) with hS3def
  have b3 := runs_mkPowJ (R1 := R1) (q := q) hq1 (src := .inl 3) (ns := jp .lS) (Y := .PB)
    (by simp) (by simp) (by simp) B (e - c6T q e) r3 (Sym.mark :: S (jp .lS)) S3 hr3
    (termOK_mark _) (by simp [hS3def, hS2def, hS3]) (by simp [hS3def, hS2def])
  rw [show S3 (jp .PB) = S (jp .PB) by simp [hS3def, hS2def]] at b3
  exact WP.W9comp.runs_seq b1 (WP.W9comp.runs_seq b2 b3)

/-- **Setup of the unjoin**: `N1 := G·q^ℓ`, `N2 := B·q^ℓ`. -/
theorem runs_setupUJ {q : ℕ} (hq : 2 ≤ q) (e G B : ℕ) (r1 r2 r3 : List Sym)
    (S : KJ E1 → List Sym) (hr1 : TermOK r1) (hr2 : TermOK r2) (hr3 : TermOK r3)
    (he : c6T q e ≤ e) (hS1 : S (.inl 1) = natSyms e ++ r1) (hS2 : S (.inl 2) = natSyms G ++ r2)
    (hS3 : S (.inl 3) = natSyms B ++ r3) :
    Runs (setupJ (R1 := R1) q (jp .lS) .N2) S
      (stA S (c6T q e) (e - c6T q e) (G * q ^ (e - c6T q e)) .N2 (B * q ^ (e - c6T q e)))
      (fun _ => True)
      (costT q e + (costP q G (e - c6T q e) + costP q B (e - c6T q e))) := by
  have hq1 : 1 ≤ q := by omega
  have b1 := runs_preT (R1 := R1) hq e r1 S hr1 he hS1
  set S2 : KJ E1 → List Sym := Function.update (Function.update S (jp .tS)
    (natSyms (c6T q e) ++ Sym.mark :: S (jp .tS))) (jp .lS)
    (natSyms (e - c6T q e) ++ Sym.mark :: S (jp .lS)) with hS2def
  have b2 := runs_mkPowJ (R1 := R1) (q := q) hq1 (src := .inl 2) (ns := jp .lS) (Y := .N1)
    (by simp) (by simp) (by simp) G (e - c6T q e) r2 (Sym.mark :: S (jp .lS)) S2 hr2
    (termOK_mark _) (by simp [hS2def, hS2]) (by simp [hS2def])
  rw [show S2 (jp .N1) = S (jp .N1) by simp [hS2def]] at b2
  set S3 : KJ E1 → List Sym := Function.update S2 (jp .N1)
    (natSyms (G * q ^ (e - c6T q e)) ++ Sym.mark :: S (jp .N1)) with hS3def
  have b3 := runs_mkPowJ (R1 := R1) (q := q) hq1 (src := .inl 3) (ns := jp .lS) (Y := .N2)
    (by simp) (by simp) (by simp) B (e - c6T q e) r3 (Sym.mark :: S (jp .lS)) S3 hr3
    (termOK_mark _) (by simp [hS3def, hS2def, hS3]) (by simp [hS3def, hS2def])
  rw [show S3 (jp .N2) = S (jp .N2) by simp [hS3def, hS2def]] at b3
  exact WP.W9comp.runs_seq b1 (WP.W9comp.runs_seq b2 b3)

/-- **Cleanup**: drop the counters on `Y, N1, lS, tS` (any values) with their floors. -/
theorem runs_cleanJ {Y : PS} (h1 : Y ≠ .N1) (h2 : Y ≠ .lS) (h3 : Y ≠ .tS) (t l n1 y : ℕ)
    (S : KJ E1 → List Sym) (arr : List Sym) :
    Runs (cleanJ (R1 := R1) Y) (Function.update (stA S t l n1 Y y) (.inl 0) arr)
      (Function.update S (.inl 0) arr) (fun _ => True)
      ((2 * bitLen y + 2) + ((2 * bitLen n1 + 2) + ((2 * bitLen l + 2) + (2 * bitLen t + 2)))) := by
  refine runs_lift (Q := fun _ => True) (lN R1) ?_
  set S0 : KJ E1 → List Sym := Function.update (stA S t l n1 Y y) (.inl 0) arr with hS0
  have d1 := runs_dropF (jp Y) y Sym.mark (S (jp Y)) S0 rfl (by simp [hS0, stA])
  have d2 := runs_dropF (jp .N1) n1 Sym.mark (S (jp .N1)) (Function.update S0 (jp Y) (S (jp Y)))
    rfl (by simp [hS0, stA, Ne.symm h1])
  have d3 := runs_dropF (jp .lS) l Sym.mark (S (jp .lS))
    (Function.update (Function.update S0 (jp Y) (S (jp Y))) (jp .N1) (S (jp .N1))) rfl
    (by simp [hS0, stA, Ne.symm h2])
  have d4 := runs_dropF (jp .tS) t Sym.mark (S (jp .tS))
    (Function.update (Function.update (Function.update S0 (jp Y) (S (jp Y))) (jp .N1)
      (S (jp .N1))) (jp .lS) (S (jp .lS))) rfl (by simp [hS0, stA, Ne.symm h3])
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq d1 (WP.W9comp.runs_seq d2
    (WP.W9comp.runs_seq d3 d4))) ?_
  funext k
  simp only [hS0, stA, Function.update_apply]
  split_ifs <;> simp_all

end Runs

end AppC.C6JoinAux

end SubNLogN.Machine
