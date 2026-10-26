/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafSplitAux
import SubNLogN.Machine.Calculus.FramePassSafe
import SubNLogN.Machine.Calculus.SafeFootprint
import SubNLogN.Machine.Calculus.SafeFold
import SubNLogN.Machine.Calculus.Hdr

/-!
# C-core leaves 6-7 (split / collect), part 3: the row-size counter (`CCore/LeafSplitCtr.lean`)

Generic programs over any stack type `K` (registers `Option Sym`), all proved:
* `hdrKDS desc ht cS cD cK`: copy the descriptor fields `K, D, S` (fields 6, 7, 8 of a 12-field
  header on `desc`) onto `cK, cD, cS` as `natSyms f ++ [mark]`, through the temporary `ht`
  (`Calculus/Hdr.lean` field moves). Exact `Runs` fact `runs_hdrKDS`; it peeks/pops only `desc`
  and `ht` (`readsIn_hdrKDS`), hence is boundary safe when those two are unframed
  (`safe_hdrKDS`, by `SafeRunsIn.of_runs_readsIn`).
* `pushZeros cK cD cD2 tt cb`: with `natSyms K` on `cK` and `natSyms D` on `cD`, push `K·D` zero
  bits on `cb` (countdown over `cK`; each step copies `cD` to `cD2` by pass C and counts it down).
  Safe for every framed set (`safe_pushZeros`; certified passes of `Calculus/FramePassSafe.lean`).
Together they turn `natSyms S ++ [mark]` into `natSyms (2^(K·D)·S) ++ [mark]`
(`natSyms_two_pow_mul`): the row size `B` of the cyclic row split.
-/

namespace SubNLogN.Machine.CCore.LeafSplitAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
open Computability

/-- The identity register lens on `Option Sym`. -/
def idL : Lens (Option Sym) (Option Sym) where
  get := id
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

section Progs

variable {K : Type}

/-- Copy the header fields `K, D, S` (fields 6, 7, 8) of `desc` onto `cK, cD, cS` (each as
`natSyms f ++ [mark]` on top) through the temporary `ht`; `desc` and `ht` are restored. -/
def hdrKDS (desc ht cS cD cK : K) : SProg K :=
  .seq (forEachRange 9 (fun _ => moveFieldTo desc ht))
    (.seq (moveFieldBackCopy ht desc cS)
      (.seq (moveFieldBackCopy ht desc cD)
        (.seq (moveFieldBackCopy ht desc cK)
          (forEachRange 6 (fun _ => moveFieldBack ht desc)))))

/-- Push `K·D` zero bits on `cb` (`natSyms K` on `cK`, `natSyms D` on `cD`). -/
def pushZeros (cK cD cD2 tt cb : K) : SProg K :=
  countdown idL cK tt (.seq (passC .mark cD tt cD2) (countdown idL cD2 tt (pushC cb (.bit false))))

theorem closed_hdrKDS (desc ht cS cD cK : K) : (hdrKDS desc ht cS cD cK).Closed := by
  refine ⟨closed_forEachRange _ _ (fun _ _ => closed_moveFieldTo desc ht),
    closed_moveFieldBackCopy _ _ _, closed_moveFieldBackCopy _ _ _, closed_moveFieldBackCopy _ _ _,
    closed_forEachRange _ _ (fun _ _ => closed_moveFieldBack ht desc)⟩

theorem closed_pushZeros (cK cD cD2 tt cb : K) : (pushZeros cK cD cD2 tt cb).Closed := by
  refine closed_countdown _ _ _ ⟨closed_passC _ _ _ _, closed_countdown _ _ _ ?_⟩
  simp [Prog.Closed, Prog.FreeBelow, pushC]

end Progs

section Reads

variable {K : Type}

theorem readsIn_true : ∀ p : SProg K, ReadsIn (fun _ => True) p
  | .push _ _ => trivial
  | .peek _ _ => trivial
  | .pop _ _ => trivial
  | .load _ => trivial
  | .seq p q => ⟨readsIn_true p, readsIn_true q⟩
  | .ite _ p q => ⟨readsIn_true p, readsIn_true q⟩
  | .loop _ p => readsIn_true p
  | .fix b => readsIn_true b
  | .recur _ => trivial

theorem readsIn_moveBlock (A : K → Prop) (src dst : K) (h : A src) :
    ReadsIn A (moveBlock src dst) := by
  simp [ReadsIn, moveBlock, moveBits, moveBitsBody, restoreR, popR, pushR, skip, h]

theorem readsIn_hdrKDS (A : K → Prop) (desc ht cS cD cK : K) (hd : A desc) (ht' : A ht) :
    ReadsIn A (hdrKDS desc ht cS cD cK) := by
  refine ⟨readsIn_forEachProg A _ _ (fun _ _ => ?_), ?_, ?_, ?_,
    readsIn_forEachProg A _ _ (fun _ _ => ?_)⟩
  · simp [ReadsIn, moveFieldTo, moveBlock, moveBits, moveBitsBody, restoreR, popR, pushR, pushC,
      skip, hd]
  all_goals simp [ReadsIn, moveFieldBackCopy, moveFieldBack, copyBlock, moveBlock, moveBits,
      moveBitsBody, moveBitsDup, dupBody, restoreR, popR, pushR, pushC, skip, hd, ht']

end Reads

section Rules

variable {K : Type} [DecidableEq K]

theorem termOK_fieldRev_append (f : ℕ) (l : List Sym) : TermOK (fieldRev f ++ l) := by
  intro d hd
  simp only [fieldRev, List.cons_append, List.head?_cons, Option.some.injEq] at hd
  subst hd
  rfl

/-- **Copy the fields `K, D, S`**, exact. The descriptor `desc` holds a 12-field header (fields
`a₀…a₅, K, D, S, b₀, b₁, b₂`) above `tdesc`; the temporary `ht` holds a number terminator. Then
`cS`, `cD`, `cK` receive `natSyms f ++ [mark]` on top; `desc`, `ht` are restored. -/
theorem runs_hdrKDS {desc ht cS cD cK : K} (h1 : desc ≠ ht) (h2 : desc ≠ cS) (h3 : desc ≠ cD)
    (h4 : desc ≠ cK) (h5 : ht ≠ cS) (h6 : ht ≠ cD) (h7 : ht ≠ cK) (h8 : cS ≠ cD) (h9 : cS ≠ cK)
    (h10 : cD ≠ cK) (a0 a1 a2 a3 a4 a5 fK fD fS b0 b1 b2 : ℕ) (tdesc : List Sym)
    (S0 : K → List Sym)
    (hdesc : S0 desc = hdrSyms [a0, a1, a2, a3, a4, a5, fK, fD, fS, b0, b1, b2] ++ tdesc)
    (hht : TermOK (S0 ht)) :
    Runs (hdrKDS desc ht cS cD cK) S0
      (Function.update (Function.update (Function.update S0 cS
        (natSyms fS ++ Sym.mark :: S0 cS)) cD (natSyms fD ++ Sym.mark :: S0 cD))
        cK (natSyms fK ++ Sym.mark :: S0 cK))
      (fun _ => True)
      (13 * (hdrSyms [a0, a1, a2, a3, a4, a5, fK, fD, fS, b0, b1, b2]).length + 100) := by
  obtain ⟨X, hXdef⟩ : ∃ X : List Sym, X = hdrSyms [b0, b1, b2] ++ tdesc := ⟨_, rfl⟩
  obtain ⟨L6, hL6⟩ : ∃ L6 : List Sym, L6 = [a5, a4, a3, a2, a1, a0].flatMap fieldRev ++ S0 ht :=
    ⟨_, rfl⟩
  have hX : S0 desc = hdrSyms [a0, a1, a2, a3, a4, a5, fK, fD, fS] ++ X := by
    rw [hdesc, hXdef, ← List.append_assoc, ← HdrAux.hdrSyms_append]
    rfl
  have r1 := runs_moveFieldsTo h1 [a0, a1, a2, a3, a4, a5, fK, fD, fS] X S0 hX
  obtain ⟨S1, hS1⟩ : ∃ S1 : K → List Sym, S1 = Function.update (Function.update S0 desc X) ht
      (movedFields [a0, a1, a2, a3, a4, a5, fK, fD, fS] ++ S0 ht) := ⟨_, rfl⟩
  rw [← hS1] at r1
  have hS1ht : S1 ht = fieldRev fS ++ (fieldRev fD ++ (fieldRev fK ++ L6)) := by
    rw [hS1, Function.update_self, hL6]
    simp [movedFields]
  have hS1d : S1 desc = X := by rw [hS1, Function.update_of_ne h1, Function.update_self]
  have hS1o : ∀ k, k ≠ desc → k ≠ ht → S1 k = S0 k := by
    intro k hk1 hk2
    rw [hS1, Function.update_of_ne hk2, Function.update_of_ne hk1]
  have r2 := runs_moveFieldBackCopy h1.symm h5 h2 fS _ S1 (termOK_fieldRev_append _ _) hS1ht
  obtain ⟨S2, hS2⟩ : ∃ S2 : K → List Sym, S2 = Function.update (Function.update
      (Function.update S1 ht (fieldRev fD ++ (fieldRev fK ++ L6))) desc
      (natSyms fS ++ Sym.mark :: S1 desc)) cS (natSyms fS ++ Sym.mark :: S1 cS) := ⟨_, rfl⟩
  rw [← hS2] at r2
  have hS2ht : S2 ht = fieldRev fD ++ (fieldRev fK ++ L6) := by
    rw [hS2, Function.update_of_ne h5, Function.update_of_ne h1.symm, Function.update_self]
  have hS2d : S2 desc = natSyms fS ++ Sym.mark :: X := by
    rw [hS2, Function.update_of_ne h2, Function.update_self, hS1d]
  have hS2c : S2 cS = natSyms fS ++ Sym.mark :: S0 cS := by
    rw [hS2, Function.update_self, hS1o cS h2.symm h5.symm]
  have hS2o : ∀ k, k ≠ desc → k ≠ ht → k ≠ cS → S2 k = S0 k := by
    intro k hk1 hk2 hk3
    rw [hS2, Function.update_of_ne hk3, Function.update_of_ne hk1, Function.update_of_ne hk2,
      hS1o k hk1 hk2]
  have r3 := runs_moveFieldBackCopy h1.symm h6 h3 fD _ S2 (termOK_fieldRev_append _ _) hS2ht
  obtain ⟨S3, hS3⟩ : ∃ S3 : K → List Sym, S3 = Function.update (Function.update
      (Function.update S2 ht (fieldRev fK ++ L6)) desc (natSyms fD ++ Sym.mark :: S2 desc)) cD
      (natSyms fD ++ Sym.mark :: S2 cD) := ⟨_, rfl⟩
  rw [← hS3] at r3
  have hS3ht : S3 ht = fieldRev fK ++ L6 := by
    rw [hS3, Function.update_of_ne h6, Function.update_of_ne h1.symm, Function.update_self]
  have hS3d : S3 desc = natSyms fD ++ Sym.mark :: natSyms fS ++ Sym.mark :: X := by
    rw [hS3, Function.update_of_ne h3, Function.update_self, hS2d]
    simp
  have hS3c : S3 cS = natSyms fS ++ Sym.mark :: S0 cS := by
    rw [hS3, Function.update_of_ne h8, Function.update_of_ne h2.symm, Function.update_of_ne h5.symm,
      hS2c]
  have hS3D : S3 cD = natSyms fD ++ Sym.mark :: S0 cD := by
    rw [hS3, Function.update_self, hS2o cD h3.symm h6.symm h8.symm]
  have hS3o : ∀ k, k ≠ desc → k ≠ ht → k ≠ cS → k ≠ cD → S3 k = S0 k := by
    intro k hk1 hk2 hk3 hk4
    rw [hS3, Function.update_of_ne hk4, Function.update_of_ne hk1, Function.update_of_ne hk2,
      hS2o k hk1 hk2 hk3]
  have hL6ok : TermOK L6 := by
    rw [hL6]
    exact HdrAux.termOK_flatMap_fieldRev _ _ hht
  have r4 := runs_moveFieldBackCopy h1.symm h7 h4 fK _ S3 hL6ok hS3ht
  obtain ⟨S4, hS4⟩ : ∃ S4 : K → List Sym, S4 = Function.update (Function.update
      (Function.update S3 ht L6) desc (natSyms fK ++ Sym.mark :: S3 desc)) cK
      (natSyms fK ++ Sym.mark :: S3 cK) := ⟨_, rfl⟩
  rw [← hS4] at r4
  have hS4ht : S4 ht = [a5, a4, a3, a2, a1, a0].flatMap fieldRev ++ S0 ht := by
    rw [hS4, Function.update_of_ne h7, Function.update_of_ne h1.symm, Function.update_self, hL6]
  have hS4d : S4 desc = natSyms fK ++ Sym.mark :: natSyms fD ++ Sym.mark :: natSyms fS ++
      Sym.mark :: X := by
    rw [hS4, Function.update_of_ne h4, Function.update_self, hS3d]
    simp
  have hS4c : S4 cS = natSyms fS ++ Sym.mark :: S0 cS := by
    rw [hS4, Function.update_of_ne h9, Function.update_of_ne h2.symm, Function.update_of_ne h5.symm,
      hS3c]
  have hS4D : S4 cD = natSyms fD ++ Sym.mark :: S0 cD := by
    rw [hS4, Function.update_of_ne h10, Function.update_of_ne h3.symm,
      Function.update_of_ne h6.symm, hS3D]
  have hS4K : S4 cK = natSyms fK ++ Sym.mark :: S0 cK := by
    rw [hS4, Function.update_self, hS3o cK h4.symm h7.symm h9.symm h10.symm]
  have hS4o : ∀ k, k ≠ desc → k ≠ ht → k ≠ cS → k ≠ cD → k ≠ cK → S4 k = S0 k := by
    intro k hk1 hk2 hk3 hk4 hk5
    rw [hS4, Function.update_of_ne hk5, Function.update_of_ne hk1, Function.update_of_ne hk2,
      hS3o k hk1 hk2 hk3 hk4]
  have r5 := runs_moveFieldsBack h1.symm [a5, a4, a3, a2, a1, a0] (S0 ht) S4 hht hS4ht
  have hc := RunsIn.seq (RunsIn.iff_runs.mpr r1) (RunsIn.seq (RunsIn.iff_runs.mpr r2)
    (RunsIn.seq (RunsIn.iff_runs.mpr r3) (RunsIn.seq (RunsIn.iff_runs.mpr r4)
      (RunsIn.iff_runs.mpr r5))))
  refine RunsIn.iff_runs.mp (RunsIn.congr hc ?_ ?_)
  · funext k
    by_cases hk1 : k = desc
    · subst hk1
      rw [Function.update_self, Function.update_of_ne h4, Function.update_of_ne h3,
        Function.update_of_ne h2, hdesc, hS4d, hXdef]
      simp [hdrSyms]
    by_cases hk2 : k = ht
    · subst hk2
      rw [Function.update_of_ne (Ne.symm h1), Function.update_self, Function.update_of_ne h7,
        Function.update_of_ne h6, Function.update_of_ne h5]
    rw [Function.update_of_ne hk1, Function.update_of_ne hk2]
    by_cases hk5 : k = cK
    · subst hk5
      rw [Function.update_self, hS4K]
    by_cases hk4 : k = cD
    · subst hk4
      rw [Function.update_of_ne hk5, Function.update_self, hS4D]
    by_cases hk3 : k = cS
    · subst hk3
      rw [Function.update_of_ne hk5, Function.update_of_ne hk4, Function.update_self, hS4c]
    rw [Function.update_of_ne hk5, Function.update_of_ne hk4, Function.update_of_ne hk3,
      hS4o k hk1 hk2 hk3 hk4 hk5]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hdrSyms_length']
    omega

/-- **Copy the fields `K, D, S`**, boundary safe when `desc` and `ht` are unframed (it peeks and
pops only these two stacks). -/
theorem safe_hdrKDS {framed : K → Prop} {desc ht cS cD cK : K} (hfd : ¬ framed desc)
    (hft : ¬ framed ht) (h1 : desc ≠ ht) (h2 : desc ≠ cS) (h3 : desc ≠ cD)
    (h4 : desc ≠ cK) (h5 : ht ≠ cS) (h6 : ht ≠ cD) (h7 : ht ≠ cK) (h8 : cS ≠ cD) (h9 : cS ≠ cK)
    (h10 : cD ≠ cK) (a0 a1 a2 a3 a4 a5 fK fD fS b0 b1 b2 : ℕ) (tdesc : List Sym)
    (S0 : K → List Sym)
    (hdesc : S0 desc = hdrSyms [a0, a1, a2, a3, a4, a5, fK, fD, fS, b0, b1, b2] ++ tdesc)
    (hht : TermOK (S0 ht)) (ρ : List (SProg K)) :
    SafeRunsIn framed ρ (hdrKDS desc ht cS cD cK) S0
      (Function.update (Function.update (Function.update S0 cS
        (natSyms fS ++ Sym.mark :: S0 cS)) cD (natSyms fD ++ Sym.mark :: S0 cD))
        cK (natSyms fK ++ Sym.mark :: S0 cK))
      (fun _ => True)
      (13 * (hdrSyms [a0, a1, a2, a3, a4, a5, fK, fD, fS, b0, b1, b2]).length + 100) :=
  SafeRunsIn.of_runs_readsIn
    (runs_hdrKDS h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 a0 a1 a2 a3 a4 a5 fK fD fS b0 b1 b2 tdesc S0 hdesc
      hht) (closed_hdrKDS desc ht cS cD cK) (readsIn_hdrKDS _ desc ht cS cD cK hfd hft) ρ

end Rules

section Zeros

variable {K : Type} [DecidableEq K]

theorem SafeRunsIn.of_eq_init' {framed : K → Prop} {ρ : List (SProg K)} {P : SProg K}
    {S₁ S₂ S' : K → List Sym} {Q : Option Sym → Prop} {T : ℕ}
    (h : SafeRunsIn framed ρ P S₁ S' Q T) (e : S₁ = S₂) : SafeRunsIn framed ρ P S₂ S' Q T :=
  e ▸ h

theorem mark_not_mem_natSyms (n : ℕ) : Sym.mark ∉ natSyms n := by
  simp [natSyms]

theorem termOK_mark_cons (l : List Sym) : TermOK (Sym.mark :: l) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  rfl

/-- One outer step of `pushZeros`: copy `natSyms D` from `cD` to `cD2` and push `D` zero bits on
`cb` while counting `cD2` down. -/
theorem safe_zerosStep {cD cD2 tt cb : K} (h1 : cD ≠ cD2) (h2 : cD ≠ tt) (h3 : cD ≠ cb)
    (h4 : cD2 ≠ tt) (h5 : cD2 ≠ cb) (h6 : tt ≠ cb) (fD : ℕ) (cd cd2 tt0 : List Sym)
    (Sx : K → List Sym) (hD : Sx cD = natSyms fD ++ Sym.mark :: cd)
    (hD2 : Sx cD2 = Sym.mark :: cd2) (htt : Sx tt = Sym.mark :: tt0) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ
      (.seq (passC .mark cD tt cD2) (countdown idL cD2 tt (pushC cb (.bit false)))) Sx
      (Function.update Sx cb (List.replicate fD (Sym.bit false) ++ Sx cb)) (fun _ => True)
      (9 * bitLen fD + 4 + countdownCost (fun _ => 1) fD) := by
  have hc := safe_passC h2 h4.symm h1 (natSyms fD) cd tt0 (mark_not_mem_natSyms fD) Sx hD htt ρ
  rw [length_natSyms] at hc
  set ct : List Sym := Sym.mark :: cd2 with hct
  set st : ℕ → K → List Sym := fun m =>
    Function.update Sx cb (List.replicate (fD - m) (Sym.bit false) ++ Sx cb) with hst
  have hcd := safe_countdown (ρ := ρ) idL h4 (body := pushC cb (.bit false)) fD ct
    (termOK_mark_cons cd2) (by simp [hct]) st (fun _ => 1) (fun n hn => by
      refine (safe_pushC cb (.bit false) _ ρ).congr ?_ le_rfl
      funext k
      simp only [hst, Function.update_apply]
      split_ifs with hk1 hk2 hk2 <;> subst_vars <;> simp_all
      have e : fD - n = fD - (n + 1) + 1 := by omega
      rw [e, List.replicate_succ, List.cons_append])
  have hinit : Function.update (st fD) cD2 (natSyms fD ++ ct) =
      Function.update Sx cD2 (natSyms fD ++ Sx cD2) := by
    funext k
    simp only [hst, Function.update_apply, Nat.sub_self, List.replicate_zero, List.nil_append]
    split_ifs <;> subst_vars <;> simp_all
  have hfin : Function.update (st 0) cD2 ct =
      Function.update Sx cb (List.replicate fD (Sym.bit false) ++ Sx cb) := by
    funext k
    simp only [hst, Function.update_apply, Nat.sub_zero]
    split_ifs <;> subst_vars <;> simp_all
  rw [hinit, hfin] at hcd
  exact SafeRunsIn.mono (SafeRunsIn.seq hc hcd) (fun _ _ => trivial) le_rfl

/-- **`pushZeros`**, safe for every framed set: with `natSyms K` on `cK` (above a visible number
terminator `ck`), `natSyms D` on `cD` (above a `mark`), guards `mark` on `cD2` and `tt`, it pushes
`K·D` zero bits on `cb` and consumes the counter on `cK`; `cD`, `cD2`, `tt` are restored. -/
theorem safe_pushZeros {cK cD cD2 tt cb : K} (hKD : cK ≠ cD) (hKD2 : cK ≠ cD2) (hKt : cK ≠ tt)
    (hKb : cK ≠ cb) (h1 : cD ≠ cD2) (h2 : cD ≠ tt) (h3 : cD ≠ cb) (h4 : cD2 ≠ tt) (h5 : cD2 ≠ cb)
    (h6 : tt ≠ cb) (fK fD : ℕ) (ck cd cd2 tt0 : List Sym) (hck : TermOK ck) (hckne : ck ≠ [])
    (S0 : K → List Sym) (hK : S0 cK = natSyms fK ++ ck)
    (hD : S0 cD = natSyms fD ++ Sym.mark :: cd) (hD2 : S0 cD2 = Sym.mark :: cd2)
    (htt : S0 tt = Sym.mark :: tt0) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (pushZeros cK cD cD2 tt cb) S0
      (Function.update (Function.update S0 cK ck) cb
        (List.replicate (fK * fD) (Sym.bit false) ++ S0 cb))
      (fun _ => True)
      (countdownCost (fun _ => 9 * bitLen fD + 4 + countdownCost (fun _ => 1) fD) fK) := by
  obtain ⟨st, hst⟩ : ∃ st : ℕ → K → List Sym, st = fun n =>
      Function.update S0 cb (List.replicate ((fK - n) * fD) (Sym.bit false) ++ S0 cb) :=
    ⟨_, rfl⟩
  have hcd := safe_countdown (ρ := ρ) idL hKt
    (body := .seq (passC .mark cD tt cD2) (countdown idL cD2 tt (pushC cb (.bit false)))) fK ck
    hck hckne st (fun _ => 9 * bitLen fD + 4 + countdownCost (fun _ => 1) fD) (fun n hn => by
      have hx1 : (Function.update (st (n + 1)) cK (natSyms (n + 1) ++ ck)) cD =
          natSyms fD ++ Sym.mark :: cd := by
        rw [Function.update_of_ne hKD.symm, hst]
        dsimp only
        rw [Function.update_of_ne h3, hD]
      have hx2 : (Function.update (st (n + 1)) cK (natSyms (n + 1) ++ ck)) cD2 =
          Sym.mark :: cd2 := by
        rw [Function.update_of_ne hKD2.symm, hst]
        dsimp only
        rw [Function.update_of_ne h5, hD2]
      have hx3 : (Function.update (st (n + 1)) cK (natSyms (n + 1) ++ ck)) tt =
          Sym.mark :: tt0 := by
        rw [Function.update_of_ne hKt.symm, hst]
        dsimp only
        rw [Function.update_of_ne h6, htt]
      have hz := safe_zerosStep h1 h2 h3 h4 h5 h6 fD cd cd2 tt0
        (Function.update (st (n + 1)) cK (natSyms (n + 1) ++ ck)) hx1 hx2 hx3 ρ
      refine hz.congr ?_ le_rfl
      have e : (fK - n) * fD = fD + (fK - (n + 1)) * fD := by
        rw [show fK - n = (fK - (n + 1)) + 1 by omega, Nat.add_mul, one_mul, Nat.add_comm]
      funext k
      by_cases hk : k = cb
      · subst hk
        rw [Function.update_self, Function.update_of_ne hKb.symm, Function.update_of_ne hKb.symm,
          hst]
        simp only [Function.update_self]
        rw [e, List.replicate_add, List.append_assoc]
      · rw [Function.update_of_ne hk]
        by_cases hk' : k = cK
        · subst hk'
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hk', Function.update_of_ne hk', hst]
          dsimp only
          rw [Function.update_of_ne hk, Function.update_of_ne hk])
  have hinit : Function.update (st fK) cK (natSyms fK ++ ck) = S0 := by
    funext k
    rw [hst]
    simp only [Nat.sub_self, Nat.zero_mul, List.replicate_zero, List.nil_append,
      Function.update_eq_self]
    by_cases hk : k = cK
    · subst hk
      rw [Function.update_self, hK]
    · rw [Function.update_of_ne hk]
  have hfin : Function.update (st 0) cK ck = Function.update (Function.update S0 cK ck) cb
      (List.replicate (fK * fD) (Sym.bit false) ++ S0 cb) := by
    rw [hst]
    simp only [Nat.sub_zero]
    exact Function.update_comm hKb.symm _ _ _
  rw [hinit, hfin] at hcd
  exact SafeRunsIn.mono hcd (fun _ _ => trivial) le_rfl

/-- `countdown` cost bound for the zero pushing: at most `26·K·D + 22·K + 2`. -/
theorem pushZeros_cost_le (fK fD : ℕ) :
    countdownCost (fun _ => 9 * bitLen fD + 4 + countdownCost (fun _ => 1) fD) fK ≤
      26 * (fK * fD) + 22 * fK + 2 := by
  have hin : countdownCost (fun _ => 1) fD ≤ 17 * fD + 2 := by
    have := countdownCost_le (fun _ => 1) fD
    simp only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul,
      mul_one] at this
    omega
  have hb := bitLen_le_self' fD
  have hout := countdownCost_le (fun _ => 9 * bitLen fD + 4 + countdownCost (fun _ => 1) fD) fK
  simp only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul] at hout
  have : fK * (9 * bitLen fD + 4 + countdownCost (fun _ => 1) fD) ≤ fK * (26 * fD + 6) :=
    Nat.mul_le_mul_left _ (by omega)
  nlinarith

end Zeros

end SubNLogN.Machine.CCore.LeafSplitAux
