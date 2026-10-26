/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7ExtractInst
import SubNLogN.Machine.AppC.C7ExtractRecB
import SubNLogN.Machine.AppC.C7BadTri

/-!
# Lemma A.9 extraction, assembly part 1: the kit with the triple kernel
(`Machine/AppC/C7ExtractAssembleKit.lean`)

**Scope.** Everything here is proved (no `sorry`). It supports
`c7Extract_of_parts` (`C7ExtractAssemble.lean`):
* `kitExt xk R'`: the arithmetic kit `xk` (`C7ExtractKit.lean`) with one more register component
  `R'`. Its programs are `xk`'s, lifted through `Lens.fst`, with the same specifications and the
  same constant.
* `triEmb`: the embedding of the stacks of the triple kernel `C7BadTriStmt` (`Fin 11` named, private
  `E'`) into the extraction layout `XK E'`. Here `0, 1, 2 ↦ nX, nY, nZ`; `3, 4, 5 ↦ K, ρ, f`;
  `6, …, 10 ↦ cL, c2L, c2K, c2r, cF1`; the private stacks go to the private part. It is injective
  (`triEmb_inj`).
* `runs_tri`: the triple kernel `Pt` called through `callInj triEmb (Lens.snd _ _)` updates
  `nX, nY, nZ` in place to `packedT0 ∘ packedS0inv`. Its hypothesis is exactly the
  `C7BadTriStmt` specification of `Pt`. Its conclusion is the body of `TriSpec`
  (`C7ExtractRecC.lean`). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine.AppC.C7XAux2

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.AppC.C7ExtractAux
  SubNLogN.Math.Networks SubNLogN.Machine.AppC.C7Aux

/-! ## The extended kit -/

section Ext

variable {K : Type} [DecidableEq K]

/-- The kit `xk` with an extra register component `R'` (programs lifted through `Lens.fst`). -/
def kitExt (xk : XKit K) (R' : Type) (hf : Finite R') (hn : Nonempty R') : XKit K where
  R := xk.R × R'
  finR := by have := xk.finR; infer_instance
  neR := by have := xk.neR; infer_instance
  lw := (Lens.fst _ _).comp xk.lw
  obs := fun v => xk.obs v.1
  c := xk.c
  add x y z t1 t2 t3 := (xk.add x y z t1 t2 t3).liftRegs (Lens.fst _ _)
  sub x y z t1 t2 t3 := (xk.sub x y z t1 t2 t3).liftRegs (Lens.fst _ _)
  mul x y z A Bs Acc T := (xk.mul x y z A Bs Acc T).liftRegs (Lens.fst _ _)
  cmp x y t1 t2 := (xk.cmp x y t1 t2).liftRegs (Lens.fst _ _)
  dm x y q r d0 d1 d2 := (xk.dm x y q r d0 d1 d2).liftRegs (Lens.fst _ _)
  add_closed x y z t1 t2 t3 := WP.W9comp.closed_liftRegs _ (xk.add_closed x y z t1 t2 t3)
  sub_closed x y z t1 t2 t3 := WP.W9comp.closed_liftRegs _ (xk.sub_closed x y z t1 t2 t3)
  mul_closed x y z A Bs Acc T := WP.W9comp.closed_liftRegs _ (xk.mul_closed x y z A Bs Acc T)
  cmp_closed x y t1 t2 := WP.W9comp.closed_liftRegs _ (xk.cmp_closed x y t1 t2)
  dm_closed x y q r d0 d1 d2 := WP.W9comp.closed_liftRegs _ (xk.dm_closed x y q r d0 d1 d2)
  add_spec h a b rx ry S hrx hry hx hy :=
    WP.W9comp.runs_mono (WP.W0m.runs_liftRegs (Lens.fst _ _)
      (xk.add_spec h a b rx ry S hrx hry hx hy)) (fun _ _ => trivial) le_rfl
  sub_spec h a b rx ry S hrx hry hab hx hy :=
    WP.W9comp.runs_mono (WP.W0m.runs_liftRegs (Lens.fst _ _)
      (xk.sub_spec h a b rx ry S hrx hry hab hx hy)) (fun _ _ => trivial) le_rfl
  mul_spec h a b rx ry S hrx hry hx hy :=
    WP.W9comp.runs_mono (WP.W0m.runs_liftRegs (Lens.fst _ _)
      (xk.mul_spec h a b rx ry S hrx hry hx hy)) (fun _ _ => trivial) le_rfl
  cmp_spec h a b rx ry S hrx hry hx hy :=
    WP.W0m.runs_liftRegs (Lens.fst _ _) (xk.cmp_spec h a b rx ry S hrx hry hx hy)
  dm_spec h a b rx ry S hb hrx hry hx hy :=
    WP.W9comp.runs_mono (WP.W0m.runs_liftRegs (Lens.fst _ _)
      (xk.dm_spec h a b rx ry S hb hrx hry hx hy)) (fun _ _ => trivial) le_rfl

@[simp] theorem kitExt_c (xk : XKit K) (R' : Type) (hf : Finite R') (hn : Nonempty R') :
    (kitExt xk R' hf hn).c = xk.c := rfl

end Ext

/-! ## The triple kernel inside the extraction layout -/

section Tri

variable {E' : Type} [DecidableEq E']

/-- Stacks of the triple kernel `C7BadTriStmt` inside the extraction layout. -/
def triEmb : KLoc (Fin 11) E' → XK E'
  | .inl i => ![wk .nX, wk .nY, wk .nZ, sK, sRho, sF, wk .cL, wk .c2L, wk .c2K, wk .c2r,
      wk .cF1] i
  | .inr e => .inr (.inr e)

theorem triEmb_inj : Function.Injective (triEmb (E' := E')) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [triEmb]
  · fin_cases i <;> simp_all [triEmb]
  · fin_cases j <;> simp_all [triEmb]
  · simp_all [triEmb]

/-- The triple kernel called on the extraction layout (registers in the second component). -/
def tri (xk : XKit (XK E')) (R' : Type) (hf : Finite R')
    (hn : Nonempty R') (Pt : Prog (KLoc (Fin 11) E') (fun _ => Sym) R') :
    Prog (XK E') (fun _ => Sym) (kitExt xk R' hf hn).R :=
  callInj triEmb (Lens.snd _ _) Pt

theorem tri_closed (xk : XKit (XK E')) (R' : Type) (hf : Finite R')
    (hn : Nonempty R') {Pt : Prog (KLoc (Fin 11) E') (fun _ => Sym) R'} (hP : Pt.Closed) :
    (tri xk R' hf hn Pt).Closed :=
  closed_callInj _ _ hP

/-- **The triple kernel on the extraction layout.** Given the `C7BadTriStmt` specification of
`Pt` (hypothesis `hPt`), and `6 ≤ K`, `ρ < K`, `1 ≤ f`, the call `tri` updates `nX, nY, nZ` in
place to the components of `packedT0 ∘ packedS0inv`; every other stack is unchanged. This is the
body of `TriSpec xk' (tri …) Ct K ρ f` (`C7ExtractRecC.lean`), with `NumAt` unfolded. -/
theorem runs_tri (xk : XKit (XK E')) (R' : Type) (hf : Finite R') (hn : Nonempty R')
    (Pt : Prog (KLoc (Fin 11) E') (fun _ => Sym) R') (Ct : ℕ)
    (hPt : ∀ (K ρ f x y z : ℕ) (rx ry rz r3 r4 r5 r6 r7 r8 r9 r10 : List Sym)
      (S : KLoc (Fin 11) E' → List Sym),
      6 ≤ K → ρ < K → 1 ≤ f → x < 2 ^ (f * K) → y < 2 ^ (f * K) → z < 2 ^ (f * K) →
      TermOK rx → TermOK ry → TermOK rz → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
      TermOK r7 → TermOK r8 → TermOK r9 → TermOK r10 →
      S (.inl 0) = natSyms x ++ rx → S (.inl 1) = natSyms y ++ ry →
      S (.inl 2) = natSyms z ++ rz → S (.inl 3) = natSyms K ++ r3 →
      S (.inl 4) = natSyms ρ ++ r4 → S (.inl 5) = natSyms f ++ r5 →
      S (.inl 6) = natSyms (f * K) ++ r6 → S (.inl 7) = natSyms (2 ^ (f * K)) ++ r7 →
      S (.inl 8) = natSyms (2 ^ K) ++ r8 → S (.inl 9) = natSyms (2 ^ ρ) ++ r9 →
      S (.inl 10) = natSyms (f - 1) ++ r10 →
      Runs Pt S
        (Function.update (Function.update (Function.update S (.inl 0)
            (natSyms (AppC.C7BadTriAux.c7BadTri K ρ f (x, y, z)).1 ++ rx))
          (.inl 1) (natSyms (AppC.C7BadTriAux.c7BadTri K ρ f (x, y, z)).2.1 ++ ry))
          (.inl 2) (natSyms (AppC.C7BadTriAux.c7BadTri K ρ f (x, y, z)).2.2 ++ rz))
        (fun _ => True) (Ct * (f * K + 1) ^ 3))
    (K ρ f : ℕ) (hK : 6 ≤ K) (hρ : ρ < K) (hf1 : 1 ≤ f) :
    ∀ (x y z : ℕ) (rx ry rz : List Sym) (S : XK E' → List Sym),
      x < 2 ^ (f * K) → y < 2 ^ (f * K) → z < 2 ^ (f * K) → TermOK rx → TermOK ry →
      TermOK rz → S (wk .nX) = natSyms x ++ rx → S (wk .nY) = natSyms y ++ ry →
      S (wk .nZ) = natSyms z ++ rz →
      (∃ r, TermOK r ∧ S sK = natSyms K ++ r) → (∃ r, TermOK r ∧ S sRho = natSyms ρ ++ r) →
      (∃ r, TermOK r ∧ S sF = natSyms f ++ r) →
      (∃ r, TermOK r ∧ S (wk .cL) = natSyms (f * K) ++ r) →
      (∃ r, TermOK r ∧ S (wk .c2L) = natSyms (2 ^ (f * K)) ++ r) →
      (∃ r, TermOK r ∧ S (wk .c2K) = natSyms (2 ^ K) ++ r) →
      (∃ r, TermOK r ∧ S (wk .c2r) = natSyms (2 ^ ρ) ++ r) →
      (∃ r, TermOK r ∧ S (wk .cF1) = natSyms (f - 1) ++ r) →
      Runs (tri xk R' hf hn Pt) S
        (Function.update (Function.update (Function.update S
          (wk .nX) (natSyms (packedT0 K ρ f (packedS0inv (f * K) K ρ f (x, y, z))).1 ++ rx))
          (wk .nY) (natSyms (packedT0 K ρ f (packedS0inv (f * K) K ρ f (x, y, z))).2.1 ++ ry))
          (wk .nZ) (natSyms (packedT0 K ρ f (packedS0inv (f * K) K ρ f (x, y, z))).2.2 ++ rz))
        (fun _ => True) (Ct * (f * K + 1) ^ 3) := by
  intro x y z rx ry rz S hx hy hz hrx hry hrz eX eY eZ ⟨r3, h3, e3⟩ ⟨r4, h4, e4⟩ ⟨r5, h5, e5⟩
    ⟨r6, h6, e6⟩ ⟨r7, h7, e7⟩ ⟨r8, h8, e8⟩ ⟨r9, h9, e9⟩ ⟨r10, h10, e10⟩
  have hP := hPt K ρ f x y z rx ry rz r3 r4 r5 r6 r7 r8 r9 r10 (S ∘ triEmb) hK hρ hf1 hx hy hz
    hrx hry hrz h3 h4 h5 h6 h7 h8 h9 h10 eX eY eZ e3 e4 e5 e6 e7 e8 e9 e10
  refine runs_callInj triEmb_inj (Lens.snd _ _) (Q := fun _ => True) ?_ ?_
  · have q0 : (wk .nX : XK E') = triEmb (.inl 0) := rfl
    have q1 : (wk .nY : XK E') = triEmb (.inl 1) := rfl
    have q2 : (wk .nZ : XK E') = triEmb (.inl 2) := rfl
    rw [q0, q1, q2, Function.update_comp_eq_of_injective _ triEmb_inj,
      Function.update_comp_eq_of_injective _ triEmb_inj,
      Function.update_comp_eq_of_injective _ triEmb_inj]
    exact hP
  · intro k hk
    have n0 : k ≠ wk .nX := fun h => hk (.inl 0) h.symm
    have n1 : k ≠ wk .nY := fun h => hk (.inl 1) h.symm
    have n2 : k ≠ wk .nZ := fun h => hk (.inl 2) h.symm
    rw [Function.update_of_ne n2, Function.update_of_ne n1, Function.update_of_ne n0]

end Tri

/-! ## The cleanup -/

section Clean

variable {E' : Type} [DecidableEq E']

/-- Cleanup of the extraction kernel: pop the floor of `cM` and the delimiter of `T`, drop the
constants with their floors. -/
def cleanupP (xk : XKit (XK E')) : Prog (XK E') (fun _ => Sym) xk.R :=
  .seq (popW xk (wk .cM)) (.seq (popW xk (wk .T)) (.seq (dropFW xk (wk .c1)) (.seq (dropFW xk (wk .c10)) (.seq (dropFW xk (wk .c11)) (.seq (dropFW xk (wk .cL)) (.seq (dropFW xk (wk .c2L)) (.seq (dropFW xk (wk .c2K)) (.seq (dropFW xk (wk .c2K1)) (.seq (dropFW xk (wk .c2r)) (.seq (dropFW xk (wk .c2r1)) (.seq (dropFW xk (wk .cF1)) (.seq (dropFW xk (wk .c2A)) (dropFW xk (wk .cA))))))))))))))

theorem closed_cleanupP (xk : XKit (XK E')) : (cleanupP xk).Closed := by
  unfold cleanupP
  refine ⟨closed_popW xk _, closed_popW xk _, closed_dropFW xk _, closed_dropFW xk _,
    closed_dropFW xk _, closed_dropFW xk _, closed_dropFW xk _, closed_dropFW xk _,
    closed_dropFW xk _, closed_dropFW xk _, closed_dropFW xk _, closed_dropFW xk _,
    closed_dropFW xk _, closed_dropFW xk _⟩

/-- **The cleanup**: from `cM = mark :: rcM`, `T = sep :: rT` and each constant
`natSyms v ++ mark :: r`, the cleanup leaves `rcM`, `rT` and the rests `r`. -/
theorem runs_cleanupP (xk : XKit (XK E')) (B : XK E' → List Sym)
    {vc1 vc10 vc11 vcL vc2L vc2K vc2K1 vc2r vc2r1 vcF1 vc2A vcA : ℕ}
    {rcM rT rc1 rc10 rc11 rcL rc2L rc2K rc2K1 rc2r rc2r1 rcF1 rc2A rcA : List Sym}
    (hcM : B (wk .cM) = Sym.mark :: rcM)
    (hT : B (wk .T) = Sym.sep :: rT)
    (hc1 : B (wk .c1) = natSyms vc1 ++ Sym.mark :: rc1)
    (hc10 : B (wk .c10) = natSyms vc10 ++ Sym.mark :: rc10)
    (hc11 : B (wk .c11) = natSyms vc11 ++ Sym.mark :: rc11)
    (hcL : B (wk .cL) = natSyms vcL ++ Sym.mark :: rcL)
    (hc2L : B (wk .c2L) = natSyms vc2L ++ Sym.mark :: rc2L)
    (hc2K : B (wk .c2K) = natSyms vc2K ++ Sym.mark :: rc2K)
    (hc2K1 : B (wk .c2K1) = natSyms vc2K1 ++ Sym.mark :: rc2K1)
    (hc2r : B (wk .c2r) = natSyms vc2r ++ Sym.mark :: rc2r)
    (hc2r1 : B (wk .c2r1) = natSyms vc2r1 ++ Sym.mark :: rc2r1)
    (hcF1 : B (wk .cF1) = natSyms vcF1 ++ Sym.mark :: rcF1)
    (hc2A : B (wk .c2A) = natSyms vc2A ++ Sym.mark :: rc2A)
    (hcA : B (wk .cA) = natSyms vcA ++ Sym.mark :: rcA)
    :
    Runs (cleanupP xk) B
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (B) (wk .cM) rcM) (wk .T) rT) (wk .c1) rc1) (wk .c10) rc10) (wk .c11) rc11) (wk .cL) rcL) (wk .c2L) rc2L) (wk .c2K) rc2K) (wk .c2K1) rc2K1) (wk .c2r) rc2r) (wk .c2r1) rc2r1) (wk .cF1) rcF1) (wk .c2A) rc2A) (wk .cA) rcA)
      (fun _ => True) (2 + (2 * bitLen vc1 + 2) + (2 * bitLen vc10 + 2) + (2 * bitLen vc11 + 2) + (2 * bitLen vcL + 2) + (2 * bitLen vc2L + 2) + (2 * bitLen vc2K + 2) + (2 * bitLen vc2K1 + 2) + (2 * bitLen vc2r + 2) + (2 * bitLen vc2r1 + 2) + (2 * bitLen vcF1 + 2) + (2 * bitLen vc2A + 2) + (2 * bitLen vcA + 2)) := by
  unfold cleanupP
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq (runs_popW_cons xk (wk .cM) _ Sym.mark rcM (by simp [Function.update_apply, hcM]))
    (WP.W9comp.runs_seq (runs_popW_cons xk (wk .T) _ Sym.sep rT (by simp [Function.update_apply, hT]))
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .c1) vc1 Sym.mark rc1 _ rfl (by simp [Function.update_apply, hc1]))
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .c10) vc10 Sym.mark rc10 _ rfl (by simp [Function.update_apply, hc10]))
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .c11) vc11 Sym.mark rc11 _ rfl (by simp [Function.update_apply, hc11]))
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .cL) vcL Sym.mark rcL _ rfl (by simp [Function.update_apply, hcL]))
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .c2L) vc2L Sym.mark rc2L _ rfl (by simp [Function.update_apply, hc2L]))
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .c2K) vc2K Sym.mark rc2K _ rfl (by simp [Function.update_apply, hc2K]))
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .c2K1) vc2K1 Sym.mark rc2K1 _ rfl (by simp [Function.update_apply, hc2K1]))
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .c2r) vc2r Sym.mark rc2r _ rfl (by simp [Function.update_apply, hc2r]))
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .c2r1) vc2r1 Sym.mark rc2r1 _ rfl (by simp [Function.update_apply, hc2r1]))
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .cF1) vcF1 Sym.mark rcF1 _ rfl (by simp [Function.update_apply, hcF1]))
    (WP.W9comp.runs_seq (runs_dropFW xk (wk .c2A) vc2A Sym.mark rc2A _ rfl (by simp [Function.update_apply, hc2A]))
    (runs_dropFW xk (wk .cA) vcA Sym.mark rcA _ rfl (by simp [Function.update_apply, hcA])))))))))))))))
    (fun _ h => h) (by omega)

end Clean

end SubNLogN.Machine.AppC.C7XAux2
