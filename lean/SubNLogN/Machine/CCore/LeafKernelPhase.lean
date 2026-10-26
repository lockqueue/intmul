/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafKernelProg

/-!
# C-core leaf kernel: the phases as `Runs` facts (`CCore/LeafKernelPhase.lean`)

Exact `Runs` facts for the phases of `innerP` (`CCore/LeafKernelProg.lean`) on the inner layout,
from a base state `B` whose named private stacks are empty.
* `runs_phaseH`: the eight header fields `P, Δ, K, D, S, j0, k, ρ` land on their stacks (`stH`).
-/

namespace SubNLogN.Machine.CCore.LeafKernelAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability
open SubNLogN.Machine.Layer

/-! ## Generic plumbing -/

section Helpers

variable {K σ τ : Type} [DecidableEq K]

/-- A component's `Runs` through a register lens. -/
theorem runs_lift (l : Lens σ τ) {p : Prog K (fun _ => Sym) τ} {S S' : K → List Sym}
    {Q : τ → Prop} {T : ℕ} (h : Runs p S S' Q T) :
    Runs (p.liftRegs l) S S' (fun v => Q (l.get v)) T :=
  RunsIn.iff_runs.1 (RunsIn.liftRegs l (RunsIn.iff_runs.2 h))

end Helpers

section Plumbing

variable {L K σ R : Type} [DecidableEq L] [DecidableEq K]

/-- `callInj` of a kernel that updates one stack. -/
theorem runs_inj_upd1 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {Q : R → Prop} {T : ℕ} (B : K → List Sym) (x : L)
    (v : List Sym) (h : Runs P (B ∘ ι) (Function.update (B ∘ ι) x v) Q T) :
    Runs (callInj ι l P) B (Function.update B (ι x) v) (fun _ => True) T :=
  runs_callInj hι l (by rw [Function.update_comp_eq_of_injective B hι x v]; exact h)
    (fun k hk => Function.update_of_ne (Ne.symm (hk x)) _ _)

end Plumbing

/-! ## Phase H -/

section PhaseH

variable {Ec : Type} [DecidableEq Ec] {m1 m2 m3 : ℕ} {Rc R1 R2 R3 : Type}

omit [DecidableEq Ec] in
theorem sc_ne {i j : Fin NS} (h : i ≠ j) : (sc i : LI Ec m1 m2 m3) ≠ sc j :=
  fun e => h (Sum.inl_injective (Sum.inr_injective e))

theorem runs_takeF (X : Fin NS) (hXH : X ≠ iH) (hXT : X ≠ iT0) (f : ℕ) (fs : List ℕ)
    (tl : List Sym) (S : LI Ec m1 m2 m3 → List Sym)
    (hS : S (sc iH) = W9.hdrSyms (f :: fs) ++ tl) :
    Runs (takeF (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3) X) S
      (Function.update (Function.update S (sc X) (natSyms f ++ S (sc X))) (sc iH)
        (W9.hdrSyms fs ++ tl)) (fun _ => True) (7 * bitLen f + 7 + (2 * bitLen f + 5)) := by
  have hS' : S (sc iH) = natSyms f ++ Sym.mark :: (W9.hdrSyms fs ++ tl) := by
    rw [hS, HdrAux.hdrSyms_cons]
    simp
  have hHX : (sc iH : LI Ec m1 m2 m3) ≠ sc X := sc_ne (Ne.symm hXH)
  have hHT : (sc iH : LI Ec m1 m2 m3) ≠ sc iT0 := sc_ne (by decide)
  have hXT' : (sc X : LI Ec m1 m2 m3) ≠ sc iT0 := sc_ne hXT
  exact WP.W9comp.runs_seq
    (runs_lift lR (NatArith.runs_copyN hHX hHT hXT' f _ S (NatArith.termOK_mark _) hS'))
    (runs_lift lW (runs_dropField (sc iH) f (W9.hdrSyms fs ++ tl) _
      (by rw [Function.update_of_ne hHX]; exact hS')))

theorem runs_skipF (f : ℕ) (fs : List ℕ) (tl : List Sym) (S : LI Ec m1 m2 m3 → List Sym)
    (hS : S (sc iH) = W9.hdrSyms (f :: fs) ++ tl) :
    Runs (skipF (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3)) S
      (Function.update S (sc iH) (W9.hdrSyms fs ++ tl)) (fun _ => True) (2 * bitLen f + 5) :=
  runs_lift lW (runs_dropField (sc iH) f (W9.hdrSyms fs ++ tl) S
    (by rw [hS, HdrAux.hdrSyms_cons]; simp))

/-- The state after phase H: the eight extracted fields on their stacks. -/
def stH (B : LI Ec m1 m2 m3 → List Sym) (fP fΔ fK fD fS fj fk fρ : ℕ) :
    LI Ec m1 m2 m3 → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update B (sc iP) (natSyms fP)) (sc iDl)
      (natSyms fΔ)) (sc iK) (natSyms fK)) (sc iD) (natSyms fD)) (sc iS) (natSyms fS)) (sc ij)
      (natSyms fj)) (sc ik) (natSyms fk)) (sc iRo) (natSyms fρ)

/-- **Phase H.** From a state whose descriptor starts with the header and whose named private
stacks are empty, the eight needed fields land on their stacks; everything else is unchanged. -/
theorem runs_phaseH (B : LI Ec m1 m2 m3 → List Sym) (fP fd fr fΔ fA fR fK fD fS fj fk fρ : ℕ)
    (tdesc : List Sym)
    (hdesc : B dsI = W9.hdrSyms [fP, fd, fr, fΔ, fA, fR, fK, fD, fS, fj, fk, fρ] ++ tdesc)
    (hsc : ∀ i, B (sc i) = []) :
    Runs (phaseH (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3)) B (stH B fP fΔ fK fD fS fj fk fρ)
      (fun _ => True)
      (40 * ((W9.hdrSyms [fP, fd, fr, fΔ, fA, fR, fK, fD, fS, fj, fk, fρ]).length + 1)) := by
  have hdH : (dsI : LI Ec m1 m2 m3) ≠ sc iH := by simp
  have hdT : (dsI : LI Ec m1 m2 m3) ≠ sc iT0 := by simp
  have hHT : (sc iH : LI Ec m1 m2 m3) ≠ sc iT0 := sc_ne (by decide)
  have h0 := runs_lift (lW (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3))
    (runs_copyHdr hdH hdT hHT [fP, fd, fr, fΔ, fA, fR, fK, fD, fS, fj, fk, fρ] tdesc B hdesc
      (by rw [hsc]; exact TermOK.nil))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq h0
    (WP.W9comp.runs_seq (runs_takeF iP (by decide) (by decide) fP
      [fd, fr, fΔ, fA, fR, fK, fD, fS, fj, fk, fρ] (B (sc iH)) _ (Function.update_self _ _ _))
    (WP.W9comp.runs_seq (runs_skipF fd [fr, fΔ, fA, fR, fK, fD, fS, fj, fk, fρ] (B (sc iH)) _
      (Function.update_self _ _ _))
    (WP.W9comp.runs_seq (runs_skipF fr [fΔ, fA, fR, fK, fD, fS, fj, fk, fρ] (B (sc iH)) _
      (Function.update_self _ _ _))
    (WP.W9comp.runs_seq (runs_takeF iDl (by decide) (by decide) fΔ [fA, fR, fK, fD, fS, fj, fk, fρ]
      (B (sc iH)) _ (Function.update_self _ _ _))
    (WP.W9comp.runs_seq (runs_skipF fA [fR, fK, fD, fS, fj, fk, fρ] (B (sc iH)) _
      (Function.update_self _ _ _))
    (WP.W9comp.runs_seq (runs_skipF fR [fK, fD, fS, fj, fk, fρ] (B (sc iH)) _
      (Function.update_self _ _ _))
    (WP.W9comp.runs_seq (runs_takeF iK (by decide) (by decide) fK [fD, fS, fj, fk, fρ]
      (B (sc iH)) _ (Function.update_self _ _ _))
    (WP.W9comp.runs_seq (runs_takeF iD (by decide) (by decide) fD [fS, fj, fk, fρ]
      (B (sc iH)) _ (Function.update_self _ _ _))
    (WP.W9comp.runs_seq (runs_takeF iS (by decide) (by decide) fS [fj, fk, fρ]
      (B (sc iH)) _ (Function.update_self _ _ _))
    (WP.W9comp.runs_seq (runs_takeF ij (by decide) (by decide) fj [fk, fρ]
      (B (sc iH)) _ (Function.update_self _ _ _))
    (WP.W9comp.runs_seq (runs_takeF ik (by decide) (by decide) fk [fρ]
      (B (sc iH)) _ (Function.update_self _ _ _))
      (runs_takeF iRo (by decide) (by decide) fρ [] (B (sc iH)) _
        (Function.update_self _ _ _)))))))))))))) ?_) (fun _ _ => trivial) ?_
  · funext x
    rcases x with i | i | e
    · simp [stH]
    · fin_cases i <;> simp [stH, Function.update_apply, hsc, HdrAux.hdrSyms_nil]
    · simp [stH]
  · simp only [HdrAux.length_hdrSyms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

end PhaseH

/-! ## Phase A: the arithmetic steps -/

section StepsA

variable {Ec : Type} [DecidableEq Ec] {m1 m2 m3 : ℕ} {Rc R1 R2 R3 : Type}

omit [DecidableEq Ec] in
theorem sc_injective : Function.Injective (sc : Fin NS → LI Ec m1 m2 m3) :=
  fun _ _ e => Sum.inl_injective (Sum.inr_injective e)

omit [DecidableEq Ec] in
theorem nodup_sc {l : List (Fin NS)} (h : l.Nodup) :
    (l.map (sc : Fin NS → LI Ec m1 m2 m3)).Nodup :=
  h.map sc_injective

theorem runs_addP {x y z : Fin NS} (h : [x, y, z, iT1, iT2, iT3].Nodup) (a b : ℕ)
    (S : LI Ec m1 m2 m3 → List Sym) (hx : S (sc x) = natSyms a) (hy : S (sc y) = natSyms b) :
    Runs (addP (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3) x y z) S
      (Function.update S (sc z) (natSyms (a + b) ++ S (sc z))) (fun _ => True)
      (20 * (bitLen a + bitLen b + 1)) :=
  runs_lift lR (NatArith.runs_addN (nodup_sc h) a b [] [] S TermOK.nil TermOK.nil
    (by rw [hx, List.append_nil]) (by rw [hy, List.append_nil]))

theorem runs_subP {x y z : Fin NS} (h : [x, y, z, iT1, iT2, iT3].Nodup) (a b : ℕ) (hab : b ≤ a)
    (S : LI Ec m1 m2 m3 → List Sym) (hx : S (sc x) = natSyms a) (hy : S (sc y) = natSyms b) :
    Runs (subP (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3) x y z) S
      (Function.update S (sc z) (natSyms (a - b) ++ S (sc z))) (fun _ => True)
      (20 * (bitLen a + bitLen b + 1)) :=
  runs_lift lR (NatArith.runs_subN (nodup_sc h) a b [] [] S TermOK.nil TermOK.nil hab
    (by rw [hx, List.append_nil]) (by rw [hy, List.append_nil]))

theorem runs_dropP (x : Fin NS) (a : ℕ) (S : LI Ec m1 m2 m3 → List Sym)
    (hx : S (sc x) = natSyms a) :
    Runs (dropP (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3) x) S (Function.update S (sc x) [])
      (fun _ => True) (2 * bitLen a + 4) :=
  runs_lift lR (NatArith.runs_dropN (sc x) a [] S TermOK.nil (by rw [hx, List.append_nil]))

theorem runs_pushP (x : Fin NS) (c : ℕ) (S : LI Ec m1 m2 m3 → List Sym) :
    Runs (pushP (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3) x c) S
      (Function.update S (sc x) (natSyms c ++ S (sc x))) (fun _ => True) (bitLen c + 1) :=
  runs_lift lR (NatArith.runs_pushNat (sc x) c S)

theorem one_le_mn : 1 ≤ mn := by norm_num [mn, tripleM]

theorem runs_powP (S : LI Ec m1 m2 m3 → List Sym) (fk : ℕ) (hCt : S (sc iCt) = natSyms 1)
    (hk : S (sc ik) = natSyms fk) :
    Runs (powP (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3)) S
      (Function.update S (sc iCt) (natSyms (1 * mn ^ fk) ++ [])) (fun _ => True)
      (NatArith.powCost mn 1 fk) :=
  runs_lift lR (NatArith.runs_powMulN (nodup_sc (l := [iCt, ik, iT1, iT2, iT3, iT4, iT5, iT6, iT7])
    (by decide)) mn one_le_mn 1 fk [] [] S TermOK.nil TermOK.nil (by rw [hCt, List.append_nil])
    (by rw [hk, List.append_nil]))

theorem runs_mulP (S : LI Ec m1 m2 m3 → List Sym) (a b : ℕ) (hK : S (sc iK) = natSyms a)
    (hY : S (sc iY3) = natSyms b) :
    Runs (mulP (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3)) S
      (Function.update S (sc iY4) (natSyms (a * b) ++ S (sc iY4))) (fun _ => True)
      (NatArith.mulCost a b) :=
  runs_lift lR (NatArith.runs_mulN (nodup_sc (l := [iK, iY3, iY4, iT1, iT2, iT3, iT4])
    (by decide)) a b [] [] S TermOK.nil TermOK.nil (by rw [hK, List.append_nil])
    (by rw [hY, List.append_nil]))

theorem runs_copySP (S : LI Ec m1 m2 m3 → List Sym) (a : ℕ) (hS : S (sc iS) = natSyms a) :
    Runs (copySP (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3)) S
      (Function.update S (sc iW) (natSyms a ++ S (sc iW))) (fun _ => True) (7 * bitLen a + 7) :=
  runs_lift lR (NatArith.runs_copyN (sc_ne (by decide)) (sc_ne (by decide)) (sc_ne (by decide))
    a [] S TermOK.nil (by rw [hS, List.append_nil]))

/-- W3 `decNat` on the named stack `N`. -/
theorem runs_decP {P3 : Prog (Loc 1 m3) (fun _ => Sym) R3} {C3 : ℕ}
    (hd : ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m3 → List Sym), TermOK rx →
      S (.inl 0) = natSyms (a + 1) ++ rx →
      Runs P3 S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
        (C3 * (zerosLead (encodeNat (a + 1)) + 1)))
    (N : Fin NS) (S : LI Ec m1 m2 m3 → List Sym) (a : ℕ) (hN : S (sc N) = natSyms (a + 1)) :
    Runs (callInj (ι3 Ec m1 m2 m3 N) (l3 (Rc := Rc) (R1 := R1) (R2 := R2)) P3) S
      (Function.update S (sc N) (natSyms a ++ [])) (fun _ => True)
      (C3 * (zerosLead (encodeNat (a + 1)) + 1)) :=
  runs_inj_upd1 (ι3_inj Ec m1 m2 m3 N) l3 S (.inl 0) (natSyms a ++ [])
    (hd a [] _ TermOK.nil (by show S (sc N) = _; rw [hN, List.append_nil]))

/-- W3 `shlVar`: `W ↦ W·2^X0`. -/
theorem runs_shlP {P1 : Prog (Loc 2 m1) (fun _ => Sym) R1} {C1 : ℕ}
    (hs : ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 m1 → List Sym), TermOK rx → TermOK rc →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
      Runs P1 S (Function.update S (.inl 0) (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
        (C1 * (c + bitLen c + 1)))
    (S : LI Ec m1 m2 m3 → List Sym) (a c : ℕ) (hW : S (sc iW) = natSyms a)
    (hX : S (sc iX0) = natSyms c) :
    Runs (callInj (ι1 Ec m1 m2 m3) (l1 (Rc := Rc) (R2 := R2) (R3 := R3)) P1) S
      (Function.update S (sc iW) (natSyms (a * 2 ^ c) ++ [])) (fun _ => True)
      (C1 * (c + bitLen c + 1)) :=
  runs_inj_upd1 (ι1_inj Ec m1 m2 m3) l1 S (.inl 0) (natSyms (a * 2 ^ c) ++ [])
    (hs a c [] [] _ TermOK.nil TermOK.nil (by show S (sc iW) = _; rw [hW, List.append_nil])
      (by show S (sc iX0) = _; rw [hX, List.append_nil]))

/-- W3 `shrVar`: `W ↦ W / 2^K`. -/
theorem runs_shrP {P2 : Prog (Loc 2 m2) (fun _ => Sym) R2} {C2 : ℕ}
    (hs : ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 m2 → List Sym), TermOK rx → TermOK rc →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
      Runs P2 S (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx)) (fun _ => True)
        (C2 * (min c (bitLen a) + bitLen c + 1)))
    (S : LI Ec m1 m2 m3 → List Sym) (a c : ℕ) (hW : S (sc iW) = natSyms a)
    (hK : S (sc iK) = natSyms c) :
    Runs (callInj (ι2 Ec m1 m2 m3) (l2 (Rc := Rc) (R1 := R1) (R3 := R3)) P2) S
      (Function.update S (sc iW) (natSyms (a / 2 ^ c) ++ [])) (fun _ => True)
      (C2 * (min c (bitLen a) + bitLen c + 1)) :=
  runs_inj_upd1 (ι2_inj Ec m1 m2 m3) l2 S (.inl 0) (natSyms (a / 2 ^ c) ++ [])
    (hs a c [] [] _ TermOK.nil TermOK.nil (by show S (sc iW) = _; rw [hW, List.append_nil])
      (by show S (sc iK) = _; rw [hK, List.append_nil]))

end StepsA

/-! ## Phase A: the step groups -/

section GroupsA

variable {Ec : Type} [DecidableEq Ec] {m1 m2 m3 : ℕ} {Rc R1 R2 R3 : Type}

theorem runs_stepA1 (S : LI Ec m1 m2 m3 → List Sym) (fP fΔ : ℕ) (hP : S (sc iP) = natSyms fP)
    (hΔ : S (sc iDl) = natSyms fΔ) (hC3 : S (sc iC3) = []) (hY1 : S (sc iY1) = [])
    (hY2 : S (sc iY2) = []) (hWg : S (sc iWg) = []) :
    Runs (stepA1 (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3)) S
      (Function.update (Function.update (Function.update (Function.update S (sc iC3) (natSyms 3))
        (sc iY1) (natSyms (fP + fΔ))) (sc iY2) (natSyms (fΔ + 3))) (sc iWg)
        (natSyms (fP + fΔ + (fΔ + 3)))) (fun _ => True)
      (bitLen 3 + 1 + (20 * (bitLen fP + bitLen fΔ + 1) + (20 * (bitLen fΔ + bitLen 3 + 1) +
        20 * (bitLen (fP + fΔ) + bitLen (fΔ + 3) + 1)))) := by
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq (runs_pushP iC3 3 S)
    (WP.W9comp.runs_seq (runs_addP (by decide) fP fΔ _ (by simp [hP])
      (by simp [hΔ]))
    (WP.W9comp.runs_seq (runs_addP (by decide) fΔ 3 _ (by simp [hΔ])
      (by simp [hC3]))
      (runs_addP (by decide) (fP + fΔ) (fΔ + 3) _ (by simp [hY1])
        (by simp [hY2]))))) ?_
  simp [hC3, hY1, hY2, hWg]

theorem runs_stepA2 (S : LI Ec m1 m2 m3 → List Sym) (fk : ℕ) (hk : S (sc ik) = natSyms fk)
    (hCt : S (sc iCt) = []) :
    Runs (stepA2 (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3)) S
      (Function.update S (sc iCt) (natSyms (1 * mn ^ fk))) (fun _ => True)
      (bitLen 1 + 1 + NatArith.powCost mn 1 fk) := by
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq (runs_pushP iCt 1 S)
    (runs_powP _ fk (by simp [hCt]) (by simp [hk]))) ?_
  rw [Function.update_idem, List.append_nil]

theorem runs_stepA3 {P3 : Prog (Loc 1 m3) (fun _ => Sym) R3} {C3 : ℕ}
    (hd : ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m3 → List Sym), TermOK rx →
      S (.inl 0) = natSyms (a + 1) ++ rx →
      Runs P3 S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
        (C3 * (zerosLead (encodeNat (a + 1)) + 1)))
    (S : LI Ec m1 m2 m3 → List Sym) (fK fD fj fρ : ℕ) (hlt : fj < fD)
    (hK : S (sc iK) = natSyms fK) (hD : S (sc iD) = natSyms fD) (hj : S (sc ij) = natSyms fj)
    (hρ : S (sc iRo) = natSyms fρ) (hY3 : S (sc iY3) = []) (hY4 : S (sc iY4) = [])
    (hX0 : S (sc iX0) = []) :
    Runs (stepA3 (Rc := Rc) (R1 := R1) (R2 := R2) P3) S
      (Function.update (Function.update (Function.update S (sc iY3) (natSyms (fD - fj - 1)))
        (sc iY4) (natSyms (fK * (fD - fj - 1)))) (sc iX0) (natSyms (fρ + fK * (fD - fj - 1))))
      (fun _ => True)
      (20 * (bitLen fD + bitLen fj + 1) + (C3 * (zerosLead (encodeNat (fD - fj - 1 + 1)) + 1) +
        (NatArith.mulCost fK (fD - fj - 1) + 20 * (bitLen fρ + bitLen (fK * (fD - fj - 1)) + 1)))) := by
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq (runs_subP (by decide) fD fj hlt.le S hD hj)
    (WP.W9comp.runs_seq (runs_decP hd iY3 _ (fD - fj - 1)
      (by rw [show fD - fj - 1 + 1 = fD - fj by omega]; simp [hY3]))
    (WP.W9comp.runs_seq (runs_mulP _ fK (fD - fj - 1) (by simp [hK])
      (by simp))
      (runs_addP (by decide) fρ (fK * (fD - fj - 1)) _ (by simp [hρ])
        (by simp [hY4]))))) ?_
  simp [hY3, hY4, hX0]

theorem runs_stepA4 {P1 : Prog (Loc 2 m1) (fun _ => Sym) R1} {C1 : ℕ}
    (hs : ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 m1 → List Sym), TermOK rx → TermOK rc →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
      Runs P1 S (Function.update S (.inl 0) (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
        (C1 * (c + bitLen c + 1)))
    (S : LI Ec m1 m2 m3 → List Sym) (fS x0 : ℕ) (hS : S (sc iS) = natSyms fS)
    (hX : S (sc iX0) = natSyms x0) (hW : S (sc iW) = []) :
    Runs (stepA4 (Rc := Rc) (R2 := R2) (R3 := R3) P1) S
      (Function.update S (sc iW) (natSyms (fS * 2 ^ x0))) (fun _ => True)
      (7 * bitLen fS + 7 + C1 * (x0 + bitLen x0 + 1)) := by
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq (runs_copySP S fS hS)
    (runs_shlP hs _ fS x0 (by simp [hW]) (by simp [hX]))) ?_
  rw [Function.update_idem, List.append_nil]

theorem runs_dropsA (S : LI Ec m1 m2 m3 → List Sym)
    (aP aΔ aD aS aj ak aρ a3 a1 a2 ay3 ay4 ax0 : ℕ)
    (hP : S (sc iP) = natSyms aP) (hΔ : S (sc iDl) = natSyms aΔ) (hD : S (sc iD) = natSyms aD)
    (hS : S (sc iS) = natSyms aS) (hj : S (sc ij) = natSyms aj) (hk : S (sc ik) = natSyms ak)
    (hρ : S (sc iRo) = natSyms aρ) (h3 : S (sc iC3) = natSyms a3) (h1 : S (sc iY1) = natSyms a1)
    (h2 : S (sc iY2) = natSyms a2) (hy3 : S (sc iY3) = natSyms ay3)
    (hy4 : S (sc iY4) = natSyms ay4) (hx0 : S (sc iX0) = natSyms ax0) :
    Runs (dropsA (Rc := Rc) (R1 := R1) (R2 := R2) (R3 := R3)) S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update S (sc iP) []) (sc iDl) []) (sc iD) [])
        (sc iS) []) (sc ij) []) (sc ik) []) (sc iRo) []) (sc iC3) []) (sc iY1) []) (sc iY2) [])
        (sc iY3) []) (sc iY4) []) (sc iX0) [])
      (fun _ => True)
      (2 * bitLen aP + 4 + (2 * bitLen aΔ + 4 + (2 * bitLen aD + 4 + (2 * bitLen aS + 4 +
        (2 * bitLen aj + 4 + (2 * bitLen ak + 4 + (2 * bitLen aρ + 4 + (2 * bitLen a3 + 4 +
        (2 * bitLen a1 + 4 + (2 * bitLen a2 + 4 + (2 * bitLen ay3 + 4 + (2 * bitLen ay4 + 4 +
        (2 * bitLen ax0 + 4))))))))))))) :=
  WP.W9comp.runs_seq (runs_dropP iP aP S hP)
  (WP.W9comp.runs_seq (runs_dropP iDl aΔ _ (by simp [hΔ]))
  (WP.W9comp.runs_seq (runs_dropP iD aD _ (by simp [hD]))
  (WP.W9comp.runs_seq (runs_dropP iS aS _ (by simp [hS]))
  (WP.W9comp.runs_seq (runs_dropP ij aj _ (by simp [hj]))
  (WP.W9comp.runs_seq (runs_dropP ik ak _ (by simp [hk]))
  (WP.W9comp.runs_seq (runs_dropP iRo aρ _ (by simp [hρ]))
  (WP.W9comp.runs_seq (runs_dropP iC3 a3 _ (by simp [h3]))
  (WP.W9comp.runs_seq (runs_dropP iY1 a1 _ (by simp [h1]))
  (WP.W9comp.runs_seq (runs_dropP iY2 a2 _ (by simp [h2]))
  (WP.W9comp.runs_seq (runs_dropP iY3 ay3 _ (by simp [hy3]))
  (WP.W9comp.runs_seq (runs_dropP iY4 ay4 _ (by simp [hy4]))
    (runs_dropP iX0 ax0 _ (by simp [hx0])))))))))))))

end GroupsA

/-! ## Phase A -/

section PhaseA

variable {Ec : Type} [DecidableEq Ec] {m1 m2 m3 : ℕ} {Rc R1 R2 R3 : Type}

/-- The state after phase A: `K`, `w_g`, the counter `e` and `W` on their stacks. -/
def stA (B : LI Ec m1 m2 m3 → List Sym) (fK wg e W0 : ℕ) : LI Ec m1 m2 m3 → List Sym :=
  Function.update (Function.update (Function.update (Function.update B (sc iK) (natSyms fK))
    (sc iWg) (natSyms wg)) (sc iCt) (natSyms e)) (sc iW) (natSyms W0)

/-- Cost of the group `stepA1`. -/
def costA1 (fP fΔ : ℕ) : ℕ :=
  bitLen 3 + 1 + (20 * (bitLen fP + bitLen fΔ + 1) + (20 * (bitLen fΔ + bitLen 3 + 1) +
    20 * (bitLen (fP + fΔ) + bitLen (fΔ + 3) + 1)))

/-- Cost of the group `stepA2`. -/
def costA2 (fk : ℕ) : ℕ := bitLen 1 + 1 + NatArith.powCost mn 1 fk

/-- Cost of the group `stepA3`. -/
def costA3 (C3 fK fD fj fρ : ℕ) : ℕ :=
  20 * (bitLen fD + bitLen fj + 1) + (C3 * (zerosLead (encodeNat (fD - fj - 1 + 1)) + 1) +
    (NatArith.mulCost fK (fD - fj - 1) + 20 * (bitLen fρ + bitLen (fK * (fD - fj - 1)) + 1)))

/-- Cost of the group `stepA4`. -/
def costA4 (C1 fS x0 : ℕ) : ℕ := 7 * bitLen fS + 7 + C1 * (x0 + bitLen x0 + 1)

/-- Cost of `dropsA`. -/
def costDrops (aP aΔ aD aS aj ak aρ a3 a1 a2 ay3 ay4 ax0 : ℕ) : ℕ :=
  2 * bitLen aP + 4 + (2 * bitLen aΔ + 4 + (2 * bitLen aD + 4 + (2 * bitLen aS + 4 +
    (2 * bitLen aj + 4 + (2 * bitLen ak + 4 + (2 * bitLen aρ + 4 + (2 * bitLen a3 + 4 +
    (2 * bitLen a1 + 4 + (2 * bitLen a2 + 4 + (2 * bitLen ay3 + 4 + (2 * bitLen ay4 + 4 +
    (2 * bitLen ax0 + 4))))))))))))

/-- The cost of phase A. -/
def costA (C1 C3 fP fΔ fK fD fS fj fk fρ : ℕ) : ℕ :=
  costA1 fP fΔ + (costA2 fk + (costA3 C3 fK fD fj fρ + (costA4 C1 fS (fρ + fK * (fD - fj - 1)) +
    costDrops fP fΔ fD fS fj fk fρ 3 (fP + fΔ) (fΔ + 3) (fD - fj - 1) (fK * (fD - fj - 1))
      (fρ + fK * (fD - fj - 1)))))

/-- **Phase A**, from the state after phase H. -/
theorem runs_phaseA {P1 : Prog (Loc 2 m1) (fun _ => Sym) R1} {P3 : Prog (Loc 1 m3) (fun _ => Sym) R3}
    {C1 C3 : ℕ}
    (hs : ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 m1 → List Sym), TermOK rx → TermOK rc →
      S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
      Runs P1 S (Function.update S (.inl 0) (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
        (C1 * (c + bitLen c + 1)))
    (hd : ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 m3 → List Sym), TermOK rx →
      S (.inl 0) = natSyms (a + 1) ++ rx →
      Runs P3 S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
        (C3 * (zerosLead (encodeNat (a + 1)) + 1)))
    (B : LI Ec m1 m2 m3 → List Sym) (fP fΔ fK fD fS fj fk fρ : ℕ) (hlt : fj < fD)
    (hsc : ∀ i, B (sc i) = []) :
    Runs (phaseA (Ec := Ec) (m2 := m2) (Rc := Rc) (R2 := R2) P1 P3)
      (stH B fP fΔ fK fD fS fj fk fρ)
      (stA B fK (fP + fΔ + (fΔ + 3)) (1 * mn ^ fk) (fS * 2 ^ (fρ + fK * (fD - fj - 1))))
      (fun _ => True) (costA C1 C3 fP fΔ fK fD fS fj fk fρ) := by
  refine WP.W9comp.runs_congr (WP.W9comp.runs_seq
    (runs_stepA1 _ fP fΔ (by simp [stH]) (by simp [stH]) (by simp [stH, hsc])
      (by simp [stH, hsc]) (by simp [stH, hsc]) (by simp [stH, hsc]))
    (WP.W9comp.runs_seq (runs_stepA2 _ fk (by simp [stH]) (by simp [stH, hsc]))
    (WP.W9comp.runs_seq (runs_stepA3 hd _ fK fD fj fρ hlt (by simp [stH]) (by simp [stH])
      (by simp [stH]) (by simp [stH]) (by simp [stH, hsc]) (by simp [stH, hsc])
      (by simp [stH, hsc]))
    (WP.W9comp.runs_seq (runs_stepA4 hs _ fS (fρ + fK * (fD - fj - 1)) (by simp [stH])
      (by simp) (by simp [stH, hsc]))
      (runs_dropsA _ fP fΔ fD fS fj fk fρ 3 (fP + fΔ) (fΔ + 3) (fD - fj - 1) (fK * (fD - fj - 1))
        (fρ + fK * (fD - fj - 1)) (by simp [stH]) (by simp [stH]) (by simp [stH])
        (by simp [stH]) (by simp [stH]) (by simp [stH]) (by simp [stH]) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp)))))) ?_
  funext x
  rcases x with i | i | e
  · simp [stA, stH]
  · fin_cases i <;> simp +decide [stA, stH, Function.update_apply, hsc]
  · simp [stA, stH]

end PhaseA

end SubNLogN.Machine.CCore.LeafKernelAux
