/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvPreProg

/-!
# Layer driver pre-phase, part 2: steps, halving, kernel loop, cleanup (`Machine/Layer/DrvPreSteps.lean`)

Step lemmas of the pre-phase program (`DrvPreProg.lean`); helpers in `SubNLogN.Machine.Layer.DrvPPAux`.
-/

namespace SubNLogN.Machine.Layer.DrvPPAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Walsh
open SubNLogN.Math.Networks (padR q0Of)

/-! ## Steps -/

section QSteps

variable {Epar Eshl Esc Eck Epad Edsc Rpar Rshl Rsc Rck Rpad Rdsc : Type}
variable [DecidableEq Epar] [DecidableEq Eshl] [DecidableEq Esc] [DecidableEq Eck]
  [DecidableEq Epad] [DecidableEq Edsc]

theorem step_pushQ (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (j : Fin 16) :
    Calculus.RunsIn [] (pushQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck)
      (Rpad := Rpad) (Rdsc := Rdsc) j)
      (qst S a dp pre) (qst S a dp (Function.update pre j (Sym.mark :: pre j))) (fun _ => True) 1 := by
  have h := WP.W9comp.runs_pushConst (σ := QReg Rpar Rshl Rsc Rck Rpad Rdsc) (qS j) Sym.mark
    (qst S a dp pre)
  have e : Function.update (qst S a dp pre) (qS j) (Sym.mark :: qst S a dp pre (qS j)) =
      qst S a dp (Function.update pre j (Sym.mark :: pre j)) := by
    rw [← qst_upd_qS]
    rfl
  rw [e] at h
  exact Calculus.RunsIn.iff_runs.2 h

theorem step_popQ (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (j : Fin 16) (d : Sym) (q : List Sym) (hj : pre j = d :: q) :
    Calculus.RunsIn [] (popQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck)
      (Rpad := Rpad) (Rdsc := Rdsc) j)
      (qst S a dp pre) (qst S a dp (Function.update pre j q)) (fun _ => True) 1 := by
  have h := DriverAux.runs_pop_of (σ := QReg Rpar Rshl Rsc Rck Rpad Rdsc) (qS j) (fun v _ => v)
    (qst S a dp pre)
  have e : Function.update (qst S a dp pre) (qS j) (qst S a dp pre (qS j)).tail =
      qst S a dp (Function.update pre j q) := by
    rw [← qst_upd_qS]
    show Function.update (qst S a dp pre) (qS j) (pre j ++ S (qS j)).tail = _
    rw [hj]
    rfl
  rw [e] at h
  exact Calculus.RunsIn.iff_runs.2 h

theorem step_dropQ (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (j : Fin 16) (n : ℕ) (fs : List ℕ) (q : List Sym)
    (hlen : fs.length = n + 1) (hj : pre j = hdrSyms fs ++ q) :
    Calculus.RunsIn [] (dropQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck)
      (Rpad := Rpad) (Rdsc := Rdsc) j n)
      (qst S a dp pre) (qst S a dp (Function.update pre j q)) (fun _ => True)
      (DriverAux.dropCost fs) := by
  have h := DriverAux.runs_dropHdr (qS j) n fs (q ++ S (qS j)) (qst S a dp pre) hlen
    (by show pre j ++ S (qS j) = _; rw [hj, List.append_assoc])
  rw [qst_upd_qS] at h
  exact Calculus.RunsIn.mono
    (Calculus.RunsIn.of_runs_liftRegs (mO Rpar Rshl Rsc Rck Rpad Rdsc) h
      (DriverAux.closed_dropHdr _ _) [])
    (fun _ _ => trivial) le_rfl

theorem step_passQ1 (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (v : List (List Bool)) (h11 : pre 11 = arrSyms v ++ [Sym.mark])
    (h13 : pre 13 = [Sym.mark]) :
    Calculus.RunsIn []
      ((Calculus.passR Sym.mark Sym.mark (qS 11) (qS 13) (qS 12)).liftRegs
        (mO Rpar Rshl Rsc Rck Rpad Rdsc))
      (qst S a dp pre)
      (qst S a dp (Function.update (Function.update pre 11 [Sym.mark]) 12
        (arrSyms v.reverse ++ pre 12)))
      (fun _ => True) (8 * (arrSyms v).length + 2) := by
  have h := Calculus.runs_passR (g := Sym.mark) (gt := Sym.mark)
    (src := (qS 11 : QLoc Epar Eshl Esc Eck Epad Edsc)) (tmp := qS 13) (dst := qS 12)
    (by simp [qS]) (by simp [qS]) (by simp [qS]) rfl (by simp) rfl v (S (qS 11)) (S (qS 13))
    (qst S a dp pre)
    (by show pre 11 ++ S (qS 11) = _; rw [h11, List.append_assoc]; rfl)
    (by show pre 13 ++ S (qS 13) = _; rw [h13]; rfl)
  have e : Function.update (Function.update (qst S a dp pre) (qS 11) (Sym.mark :: S (qS 11)))
      (qS 12) (arrSyms v.reverse ++ qst S a dp pre (qS 12)) =
      qst S a dp (Function.update (Function.update pre 11 [Sym.mark]) 12
        (arrSyms v.reverse ++ pre 12)) := by
    have e1 : Sym.mark :: S (qS 11) = [Sym.mark] ++ S (qS 11) := rfl
    have e2 : arrSyms v.reverse ++ qst S a dp pre (qS 12) =
        (arrSyms v.reverse ++ pre 12) ++ S (qS 12) := (List.append_assoc _ _ _).symm
    rw [e1, qst_upd_qS, e2, qst_upd_qS]
  rw [e] at h
  exact Calculus.RunsIn.mono
    (Calculus.RunsIn.of_runs_liftRegs (mO Rpar Rshl Rsc Rck Rpad Rdsc) h
      (Calculus.closed_passR _ _ _ _ _) [])
    (fun _ _ => trivial) le_rfl

theorem step_passQ2 (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (v : List (List Bool)) (h12 : pre 12 = arrSyms v ++ [Sym.mark])
    (h13 : pre 13 = [Sym.mark]) :
    Calculus.RunsIn []
      ((Calculus.passR Sym.mark Sym.mark (qS 12) (qS 13) qA).liftRegs
        (mO Rpar Rshl Rsc Rck Rpad Rdsc))
      (qst S a dp pre) (qst S (arrSyms v.reverse ++ a) dp (Function.update pre 12 [Sym.mark]))
      (fun _ => True) (8 * (arrSyms v).length + 2) := by
  have h := Calculus.runs_passR (g := Sym.mark) (gt := Sym.mark)
    (src := (qS 12 : QLoc Epar Eshl Esc Eck Epad Edsc)) (tmp := qS 13) (dst := qA)
    (by simp [qS]) (by simp [qS, qA]) (by simp [qS, qA]) rfl (by simp) rfl v (S (qS 12))
    (S (qS 13)) (qst S a dp pre)
    (by show pre 12 ++ S (qS 12) = _; rw [h12, List.append_assoc]; rfl)
    (by show pre 13 ++ S (qS 13) = _; rw [h13]; rfl)
  have e : Function.update (Function.update (qst S a dp pre) (qS 12) (Sym.mark :: S (qS 12))) qA
      (arrSyms v.reverse ++ qst S a dp pre qA) =
      qst S (arrSyms v.reverse ++ a) dp (Function.update pre 12 [Sym.mark]) := by
    have e1 : Sym.mark :: S (qS 12) = [Sym.mark] ++ S (qS 12) := rfl
    have e2 : qst S a dp pre qA = a := rfl
    rw [e1, qst_upd_qS, e2, qst_upd_qA]
  rw [e] at h
  exact Calculus.RunsIn.mono
    (Calculus.RunsIn.of_runs_liftRegs (mO Rpar Rshl Rsc Rck Rpad Rdsc) h
      (Calculus.closed_passR _ _ _ _ _) [])
    (fun _ _ => trivial) le_rfl

/-- A kernel working in place on own stack `11`. -/
theorem step_onX {L R : Type} [DecidableEq L] {ι : L → QLoc Epar Eshl Esc Eck Epad Edsc}
    (hι : Function.Injective ι) (l : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) R)
    {P : Prog L (fun _ => Sym) R} (hcl : P.Closed) {i0 : L} (hi0 : ι i0 = qS 11)
    (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (q : List Sym) {T : ℕ} {Q : R → Prop}
    (hP : Runs P (qst S a dp pre ∘ ι) (Function.update (qst S a dp pre ∘ ι) i0 (q ++ S (qS 11)))
      Q T) :
    Calculus.RunsIn [] (callInj ι l P) (qst S a dp pre) (qst S a dp (Function.update pre 11 q))
      (fun _ => True) T := by
  rw [← qst_upd_qS]
  refine Calculus.RunsIn.of_callInj hι l hcl (Q := Q) ?_ ?_ []
  · have e := Function.update_comp_eq_of_injective (qst S a dp pre) hι i0 (q ++ S (qS 11))
    rw [hi0] at e
    rw [e]
    exact hP
  · intro k hk
    exact Function.update_of_ne (fun h => hk i0 (hi0.trans h.symm)) _ _

/-- The exact left shift: array → own stack `11`. -/
theorem step_shl {R : Type} (l : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) R)
    {P : Prog (KLoc (Fin 5) Eshl) (fun _ => Sym) R} (hcl : P.Closed)
    (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (a' X : List Sym) {T : ℕ} {Q : R → Prop}
    (hP : Runs P (qst S a dp pre ∘ κShl) (Function.update (Function.update (qst S a dp pre ∘ κShl)
      (.inl 0) a') (.inl 1) (X ++ (qst S a dp pre ∘ κShl) (.inl 1))) Q T) :
    Calculus.RunsIn [] (callInj κShl l P) (qst S a dp pre)
      (qst S a' dp (Function.update pre 11 (X ++ pre 11))) (fun _ => True) T := by
  have h7 : X ++ qst S a dp pre (qS 11) = (X ++ pre 11) ++ S (qS 11) :=
    (List.append_assoc _ _ _).symm
  have e : Function.update (Function.update (qst S a dp pre) qA a') (qS 11)
      (X ++ qst S a dp pre (qS 11)) = qst S a' dp (Function.update pre 11 (X ++ pre 11)) := by
    rw [qst_upd_qA, h7, qst_upd_qS]
  rw [← e]
  refine Calculus.RunsIn.of_callInj κShl_injective l hcl (Q := Q) ?_ ?_ []
  · rw [show (qS 11 : QLoc Epar Eshl Esc Eck Epad Edsc) = κShl (.inl 1) from rfl,
      show (qA : QLoc Epar Eshl Esc Eck Epad Edsc) = κShl (.inl 0) from rfl,
      Function.update_comp_eq_of_injective _ κShl_injective,
      Function.update_comp_eq_of_injective _ κShl_injective]
    exact hP
  · intro k hk
    rw [Function.update_of_ne (show k ≠ qS 11 from fun h => hk (.inl 1) h.symm),
      Function.update_of_ne (show k ≠ qA from fun h => hk (.inl 0) h.symm)]

/-- The descriptor kernel. -/
theorem step_dsc {R : Type} (l : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) R)
    {P : Prog (KLoc (Fin 2) Edsc) (fun _ => Sym) R} (hcl : P.Closed)
    (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (Ds : List Sym) {T : ℕ} {Q : R → Prop}
    (hP : Runs P (qst S a dp pre ∘ κDsc)
      (Function.update (qst S a dp pre ∘ κDsc) (.inl 1) (Ds ++ (qst S a dp pre ∘ κDsc) (.inl 1)))
      Q T) :
    Calculus.RunsIn [] (callInj κDsc l P) (qst S a dp pre) (qst S a (Ds ++ dp) pre)
      (fun _ => True) T := by
  have e : Function.update (qst S a dp pre) qD (Ds ++ qst S a dp pre qD) = qst S a (Ds ++ dp) pre := by
    have e2 : Ds ++ qst S a dp pre qD = (Ds ++ dp) ++ S qD := (List.append_assoc _ _ _).symm
    rw [e2, qst_upd_qD]
  rw [← e]
  refine Calculus.RunsIn.of_callInj κDsc_injective l hcl (Q := Q) ?_ ?_ []
  · rw [show (qD : QLoc Epar Eshl Esc Eck Epad Edsc) = κDsc (.inl 1) from rfl,
      Function.update_comp_eq_of_injective _ κDsc_injective]
    exact hP
  · intro k hk
    exact Function.update_of_ne (show k ≠ qD from fun h => hk (.inl 1) h.symm) _ _

/-- The payload the parameter kernel pushes on its stack `i`. -/
noncomputable def payQ (t : LayerRT) (i : Fin 12) : List Sym :=
  drvPreParamsPost (E := Empty) t (fun _ => []) (.inl i)

theorem drvPreParamsPost_inl (t : LayerRT) {E : Type} (St : KLoc (Fin 12) E → List Sym)
    (i : Fin 12) : drvPreParamsPost t St (.inl i) = payQ t i ++ St (.inl i) := by
  fin_cases i <;> simp [payQ, drvPreParamsPost]

theorem payQ_zero (t : LayerRT) (i : Fin 12) (h : i.val = 0) : payQ t i = [] := by
  unfold payQ drvPreParamsPost
  simp [h]

/-- Own-stack prefixes after the parameter kernel. -/
noncomputable def parPreQ (t : LayerRT) (pre : Fin 16 → List Sym) (j : Fin 16) : List Sym :=
  (if h : j.val < 11 then payQ t ⟨j.val + 1, by omega⟩ else []) ++ pre j

theorem κPar_succ (k : ℕ) (hk : k < 11) :
    (κPar (.inl ⟨k + 1, by omega⟩) : QLoc Epar Eshl Esc Eck Epad Edsc) = qS ⟨k, by omega⟩ := by
  simp [κPar, qS]

/-- The parameter kernel. -/
theorem step_parQ {R : Type} (l : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) R)
    {P : Prog (KLoc (Fin 12) Epar) (fun _ => Sym) R} (hcl : P.Closed) (t : LayerRT)
    (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym) (pre : Fin 16 → List Sym)
    {T : ℕ} {Q : R → Prop}
    (hP : Runs P (qst S a dp pre ∘ κPar) (drvPreParamsPost t (qst S a dp pre ∘ κPar)) Q T) :
    Calculus.RunsIn [] (callInj κPar l P) (qst S a dp pre) (qst S a dp (parPreQ t pre))
      (fun _ => True) T := by
  refine Calculus.RunsIn.of_callInj κPar_injective l hcl (Q := Q) ?_ ?_ []
  · have e : qst S a dp (parPreQ t pre) ∘ κPar = drvPreParamsPost t (qst S a dp pre ∘ κPar) := by
      funext x
      rcases x with i | e
      · rw [drvPreParamsPost_inl]
        by_cases h0 : i.val = 0
        · rw [payQ_zero t i h0, List.nil_append]
          simp only [Function.comp_apply, κPar, dif_pos h0]
          rfl
        · obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by omega⟩
          have hk11 : k < 11 := by have := i.isLt; omega
          have hiq : i = ⟨k + 1, Nat.succ_lt_succ hk11⟩ := Fin.ext hk
          rw [Function.comp_apply, Function.comp_apply, hiq, κPar_succ k hk11]
          show parPreQ t pre ⟨k, _⟩ ++ S (qS ⟨k, _⟩) =
            payQ t ⟨k + 1, _⟩ ++ (pre ⟨k, _⟩ ++ S (qS ⟨k, _⟩))
          unfold parPreQ
          rw [dif_pos hk11, List.append_assoc]
      · rfl
    rw [e]
    exact hP
  · intro k hk
    rcases k with i | j | e
    · rfl
    · by_cases hj : j.val < 11
      · exact (hk (.inl ⟨j.val + 1, by omega⟩) (by rw [κPar_succ j.val hj]; rfl)).elim
      · show parPreQ t pre j ++ S (qS j) = pre j ++ S (qS j)
        unfold parPreQ
        rw [dif_neg hj, List.nil_append]
    · rfl

/-- Own-stack prefixes after the floors. -/
def gPreQ (pre : Fin 16 → List Sym) (j : Fin 16) : List Sym :=
  if j.val = 7 then pre j else Sym.mark :: pre j

theorem runs_guardsQ (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) :
    Calculus.RunsIn [] (guardsQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck)
      (Rpad := Rpad) (Rdsc := Rdsc)) (qst S a dp pre) (qst S a dp (gPreQ pre)) (fun _ => True) 15 := by
  have h := (step_pushQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
      (Rdsc := Rdsc) S a dp pre 0).seq
    ((step_pushQ S a dp _ 1).seq ((step_pushQ S a dp _ 2).seq ((step_pushQ S a dp _ 3).seq
    ((step_pushQ S a dp _ 4).seq ((step_pushQ S a dp _ 5).seq ((step_pushQ S a dp _ 6).seq
    ((step_pushQ S a dp _ 8).seq ((step_pushQ S a dp _ 9).seq ((step_pushQ S a dp _ 10).seq
    ((step_pushQ S a dp _ 11).seq ((step_pushQ S a dp _ 12).seq ((step_pushQ S a dp _ 13).seq
    ((step_pushQ S a dp _ 14).seq (step_pushQ S a dp _ 15))))))))))))))
  refine Calculus.RunsIn.congr h ?_ le_rfl
  congr 1
  funext j
  fin_cases j <;> simp [gPreQ, Function.update_apply]

/-- Decrement the loop counter (own stack `4`). -/
theorem step_decQ (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (n : ℕ) (h4 : pre 4 = natSyms (n + 1) ++ [Sym.mark]) :
    Calculus.RunsIn [] ((Lib.dec (qS 4) (qS 15)).liftRegs (mO Rpar Rshl Rsc Rck Rpad Rdsc))
      (qst S a dp pre) (qst S a dp (Function.update pre 4 (natSyms n ++ [Sym.mark])))
      (fun _ => True) (6 * zerosLead (Computability.encodeNat (n + 1)) + 8) := by
  have h := Calculus.FramePassRAux.runs_dec (c := (qS 4 : QLoc Epar Eshl Esc Eck Epad Edsc))
    (t := qS 15) (by simp [qS]) n (Sym.mark :: S (qS 4)) (qst S a dp pre) (termOK_mark _)
    (by show pre 4 ++ S (qS 4) = _; rw [h4, List.append_assoc]; rfl)
  have e : natSyms n ++ Sym.mark :: S (qS 4) = (natSyms n ++ [Sym.mark]) ++ S (qS 4) := by simp
  rw [e, qst_upd_qS] at h
  exact Calculus.RunsIn.mono
    (Calculus.RunsIn.of_runs_liftRegs (mO Rpar Rshl Rsc Rck Rpad Rdsc) h
      (Calculus.FramePassRAux.closed_dec _ _) [])
    (fun _ _ => trivial) le_rfl

end QSteps

/-! ## The halving and the kernel passes -/

section QLoop

variable {Epar Eshl Esc Eck Epad Edsc Rpar Rshl Rsc Rck Rpad Rdsc : Type}
variable [DecidableEq Epar] [DecidableEq Eshl] [DecidableEq Esc] [DecidableEq Eck]
  [DecidableEq Epad] [DecidableEq Edsc]

theorem natSyms_two_mul' {n : ℕ} (hn : 1 ≤ n) : natSyms (2 * n) = Sym.bit false :: natSyms n := by
  unfold natSyms
  rw [two_mul, TMFw.encodeNat_add, if_neg]
  · rfl
  · intro h
    rw [TMFw.encodeNat_eq_nil_iff] at h
    omega

theorem natSyms_two_pow_mul (K W : ℕ) (hW : 1 ≤ W) :
    natSyms (2 ^ K * W) = List.replicate K (Sym.bit false) ++ natSyms W := by
  induction K with
  | zero => simp
  | succ K ih =>
    have e : 2 ^ (K + 1) * W = 2 * (2 ^ K * W) := by ring
    rw [e, natSyms_two_mul' (Nat.mul_pos (Nat.two_pow_pos K) hW), ih, List.replicate_succ,
      List.cons_append]

/-- **Halving the bit weight**: own stack `5` goes from `natSyms (2^K·W')` to `natSyms W'`. -/
theorem runs_halve (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (K W' : ℕ) (hW' : 1 ≤ W')
    (h5 : pre 5 = natSyms (2 ^ K * W') ++ [Sym.mark]) (h6 : pre 6 = natSyms K ++ [Sym.mark])
    (h13 : pre 13 = [Sym.mark]) (h14 : pre 14 = [Sym.mark]) :
    Calculus.RunsIn [] (halveQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck)
      (Rpad := Rpad) (Rdsc := Rdsc)) (qst S a dp pre)
      (qst S a dp (Function.update pre 5 (natSyms W' ++ [Sym.mark]))) (fun _ => True)
      (9 * bitLen K + 4 + Calculus.countdownCost (fun _ => 1) K) := by
  have hc := FFT.DIF.runs_copyBits (mO Rpar Rshl Rsc Rck Rpad Rdsc)
    (src := (qS 6 : QLoc Epar Eshl Esc Eck Epad Edsc)) (dst := qS 14) (tmp := qS 13)
    (by simp [qS]) (by simp [qS]) (by simp [qS]) (qst S a dp pre) (Computability.encodeNat K)
    (Sym.mark :: S (qS 6))
    (by show pre 6 ++ S (qS 6) = _; rw [h6, List.append_assoc]; rfl)
    (termOK_mark _) (by show TermOK (pre 13 ++ S (qS 13)); rw [h13]; exact termOK_mark _)
  have e1 : (Computability.encodeNat K).map Sym.bit ++ qst S a dp pre (qS 14) =
      (natSyms K ++ [Sym.mark]) ++ S (qS 14) := by
    show natSyms K ++ (pre 14 ++ S (qS 14)) = _
    rw [h14, List.append_assoc]
  rw [e1, qst_upd_qS] at hc
  -- the countdown
  set st : ℕ → QLoc Epar Eshl Esc Eck Epad Edsc → List Sym := fun m =>
    qst S a dp (Function.update pre 5
      (List.replicate m (Sym.bit false) ++ natSyms W' ++ [Sym.mark])) with hst
  have hupd : ∀ m n : ℕ, Function.update (st m) (qS 14) (natSyms n ++ Sym.mark :: S (qS 14)) =
      qst S a dp (Function.update (Function.update pre 5
        (List.replicate m (Sym.bit false) ++ natSyms W' ++ [Sym.mark])) 14
        (natSyms n ++ [Sym.mark])) := by
    intro m n
    rw [hst]
    have e : natSyms n ++ Sym.mark :: S (qS 14) = (natSyms n ++ [Sym.mark]) ++ S (qS 14) := by
      simp
    rw [e, qst_upd_qS]
  have hcd := Calculus.runsIn_countdown (ρ := []) (mO Rpar Rshl Rsc Rck Rpad Rdsc)
    (c := (qS 14 : QLoc Epar Eshl Esc Eck Epad Edsc)) (t := qS 15) (by simp [qS])
    (body := popQ 5) K (Sym.mark :: S (qS 14)) (termOK_mark _) st (fun _ => 1)
    (fun m _ => by
      rw [hupd, hupd]
      have hp := step_popQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
        (Rdsc := Rdsc) S a dp (Function.update (Function.update pre 5
          (List.replicate (m + 1) (Sym.bit false) ++ natSyms W' ++ [Sym.mark])) 14
          (natSyms (m + 1) ++ [Sym.mark])) 5 (Sym.bit false)
        (List.replicate m (Sym.bit false) ++ natSyms W' ++ [Sym.mark])
        (by simp [Function.update_apply, List.replicate_succ])
      refine Calculus.RunsIn.congr hp ?_ le_rfl
      congr 1
      funext j
      fin_cases j <;> simp [Function.update_apply])
  have hs1 : qst S a dp (Function.update pre 14 (natSyms K ++ [Sym.mark])) =
      Function.update (st K) (qS 14) (natSyms K ++ Sym.mark :: S (qS 14)) := by
    rw [hupd]
    congr 1
    funext j
    fin_cases j <;> simp [Function.update_apply, h5, natSyms_two_pow_mul K W' hW']
  have hs2 : Function.update (st 0) (qS 14) (Sym.mark :: S (qS 14)) =
      qst S a dp (Function.update pre 5 (natSyms W' ++ [Sym.mark])) := by
    have e : Function.update (st 0) (qS 14) (Sym.mark :: S (qS 14)) =
        Function.update (st 0) (qS 14) (natSyms 0 ++ Sym.mark :: S (qS 14)) := rfl
    rw [e, hupd]
    congr 1
    funext j
    have hz : natSyms 0 = [] := rfl
    fin_cases j <;> simp [Function.update_apply, h14, hz]
  rw [← hs1, hs2] at hcd
  exact Calculus.RunsIn.mono (Calculus.RunsIn.seq (Calculus.RunsIn.iff_runs.2 hc) hcd)
    (fun _ _ => trivial) le_rfl

/-- The kernel pass's specification (the body of `DrvCKernelStmt`). -/
def CkSpec {E R : Type} [DecidableEq E] (C : ℕ) (Pr : Prog (KLoc (Fin 3) E) (fun _ => Sym) R) :
    Prop :=
  ∀ (W w : ℕ) (blks : List (List (List CInt))) (rest r1 r2 : List Sym)
    (S : KLoc (Fin 3) E → List Sym),
    1 ≤ W → 1 ≤ w → (∀ blk ∈ blks, CGateBlockOK W blk) →
    CArrFits w blks.flatten → CArrFits w (blks.map (cgateBlock W)).flatten →
    BlkTerm rest → TermOK r1 → TermOK r2 →
    S (.inl 0) = carrSyms w blks.flatten ++ rest → S (.inl 1) = natSyms W ++ r1 →
    S (.inl 2) = natSyms w ++ r2 →
    Runs Pr S
      (Function.update S (.inl 0) (carrSyms w (blks.map (cgateBlock W)).flatten ++ rest))
      (fun _ => True)
      (C * (cvol w blks.flatten + blks.flatten.length * (bitLen W + 1) + w + 1))

theorem blkTerm_mark (X : List Sym) : BlkTerm (Sym.mark :: X) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  exact ⟨rfl, by simp⟩

/-- One kernel pass on own stack `11` (bit weight on stack `5`, width on stack `1`). -/
theorem step_ckQ {R : Type} (l : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) R)
    {P : Prog (KLoc (Fin 3) Eck) (fun _ => Sym) R} (hcl : P.Closed) {Cck : ℕ}
    (hck : CkSpec Cck P) (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (W w : ℕ) (blks : List (List (List CInt))) (hW : 1 ≤ W)
    (hw : 1 ≤ w) (hok : ∀ blk ∈ blks, CGateBlockOK W blk) (hfin : CArrFits w blks.flatten)
    (hfout : CArrFits w (blks.map (cgateBlock W)).flatten)
    (h11 : pre 11 = carrSyms w blks.flatten ++ [Sym.mark]) (h5 : pre 5 = natSyms W ++ [Sym.mark])
    (h1 : pre 1 = natSyms w ++ [Sym.mark]) :
    Calculus.RunsIn [] (callInj κCk l P) (qst S a dp pre)
      (qst S a dp (Function.update pre 11 (carrSyms w (blks.map (cgateBlock W)).flatten ++
        [Sym.mark]))) (fun _ => True)
      (Cck * (cvol w blks.flatten + blks.flatten.length * (bitLen W + 1) + w + 1)) := by
  refine step_onX κCk_injective l hcl (i0 := .inl 0) rfl S a dp pre _ (Q := fun _ => True) ?_
  have h := hck W w blks (Sym.mark :: S (qS 11)) (Sym.mark :: S (qS 5)) (Sym.mark :: S (qS 1))
    (qst S a dp pre ∘ κCk) hW hw hok hfin hfout (blkTerm_mark _) (termOK_mark _) (termOK_mark _)
    (by show pre 11 ++ S (qS 11) = _; rw [h11, List.append_assoc]; rfl)
    (by show pre 5 ++ S (qS 5) = _; rw [h5, List.append_assoc]; rfl)
    (by show pre 1 ++ S (qS 1) = _; rw [h1, List.append_assoc]; rfl)
  have e : carrSyms w (blks.map (cgateBlock W)).flatten ++ Sym.mark :: S (qS 11) =
      (carrSyms w (blks.map (cgateBlock W)).flatten ++ [Sym.mark]) ++ S (qS 11) := by simp
  rw [e] at h
  exact h

/-- **The kernel loop**: `N` iterations of (halve the bit weight; kernel pass), from the lists
`Ls 1` (weight `Wk 0`) to `Ls (N + 1)` (weight `Wk N`). -/
theorem runs_loopQ {R : Type} (l : Lens (QReg Rpar Rshl Rsc Rck Rpad Rdsc) R)
    {P : Prog (KLoc (Fin 3) Eck) (fun _ => Sym) R} (hcl : P.Closed) {Cck : ℕ}
    (hck : CkSpec Cck P) (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (pre : Fin 16 → List Sym) (K w N : ℕ) (Ls : ℕ → List (List CInt))
    (Bs : ℕ → List (List (List CInt))) (Wk : ℕ → ℕ)
    (hB : ∀ k, k ≤ N → (Bs k).flatten = Ls k)
    (hB' : ∀ k, k ≤ N → ((Bs k).map (cgateBlock (Wk k))).flatten = Ls (k + 1))
    (hWk : ∀ k, k < N → Wk k = 2 ^ K * Wk (k + 1)) (hW1 : ∀ k, k ≤ N → 1 ≤ Wk k) (hw : 1 ≤ w)
    (hok : ∀ k, k ≤ N → ∀ blk ∈ Bs k, CGateBlockOK (Wk k) blk)
    (hfit : ∀ k, k ≤ N + 1 → CArrFits w (Ls k))
    (h4 : pre 4 = natSyms N ++ [Sym.mark]) (h5 : pre 5 = natSyms (Wk 0) ++ [Sym.mark])
    (h11 : pre 11 = carrSyms w (Ls 1) ++ [Sym.mark]) (h6 : pre 6 = natSyms K ++ [Sym.mark])
    (h1 : pre 1 = natSyms w ++ [Sym.mark]) (h13 : pre 13 = [Sym.mark])
    (h14 : pre 14 = [Sym.mark]) :
    Calculus.RunsIn [] (Calculus.countdown (mO Rpar Rshl Rsc Rck Rpad Rdsc) (qS 4) (qS 15)
        (.seq (halveQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
          (Rdsc := Rdsc)) (callInj κCk l P)))
      (qst S a dp pre)
      (qst S a dp (Function.update (Function.update (Function.update pre 5
        (natSyms (Wk N) ++ [Sym.mark])) 11 (carrSyms w (Ls (N + 1)) ++ [Sym.mark])) 4 [Sym.mark]))
      (fun _ => True)
      (Calculus.countdownCost (fun n => 9 * bitLen K + 4 + Calculus.countdownCost (fun _ => 1) K +
        Cck * (cvol w (Ls (N - n)) + (Ls (N - n)).length * (bitLen (Wk (N - n)) + 1) + w + 1)) N) := by
  set st : ℕ → QLoc Epar Eshl Esc Eck Epad Edsc → List Sym := fun n =>
    qst S a dp (Function.update (Function.update pre 5 (natSyms (Wk (N - n)) ++ [Sym.mark])) 11
      (carrSyms w (Ls (N - n + 1)) ++ [Sym.mark])) with hst
  have hupd : ∀ n m : ℕ, Function.update (st n) (qS 4) (natSyms m ++ Sym.mark :: S (qS 4)) =
      qst S a dp (Function.update (Function.update (Function.update pre 5
        (natSyms (Wk (N - n)) ++ [Sym.mark])) 11 (carrSyms w (Ls (N - n + 1)) ++ [Sym.mark])) 4
        (natSyms m ++ [Sym.mark])) := by
    intro n m
    rw [hst]
    have e : natSyms m ++ Sym.mark :: S (qS 4) = (natSyms m ++ [Sym.mark]) ++ S (qS 4) := by simp
    rw [e, qst_upd_qS]
  have hcd := Calculus.runsIn_countdown (ρ := []) (mO Rpar Rshl Rsc Rck Rpad Rdsc)
    (c := (qS 4 : QLoc Epar Eshl Esc Eck Epad Edsc)) (t := qS 15) (by simp [qS])
    (body := .seq (halveQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
      (Rdsc := Rdsc)) (callInj κCk l P)) N (Sym.mark :: S (qS 4)) (termOK_mark _) st
    (fun n => 9 * bitLen K + 4 + Calculus.countdownCost (fun _ => 1) K +
      Cck * (cvol w (Ls (N - n)) + (Ls (N - n)).length * (bitLen (Wk (N - n)) + 1) + w + 1))
    (fun n hn => by
      obtain ⟨m, hm⟩ : ∃ m, N - n = m + 1 := ⟨N - n - 1, by omega⟩
      have hm' : N - (n + 1) = m := by omega
      rw [hupd, hupd, hm, hm']
      have hh := runs_halve (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
        (Rdsc := Rdsc) S a dp (Function.update (Function.update (Function.update pre 5
          (natSyms (Wk m) ++ [Sym.mark])) 11 (carrSyms w (Ls (m + 1)) ++ [Sym.mark])) 4
          (natSyms (n + 1) ++ [Sym.mark])) K (Wk (m + 1)) (hW1 _ (by omega))
        (by simp [Function.update_apply, hWk m (by omega)]) (by simp [Function.update_apply, h6])
        (by simp [Function.update_apply, h13]) (by simp [Function.update_apply, h14])
      have hBm := hB (m + 1) (by omega)
      have hBm' := hB' (m + 1) (by omega)
      have hk := step_ckQ l hcl hck S a dp (Function.update (Function.update (Function.update
        (Function.update pre 5 (natSyms (Wk m) ++ [Sym.mark])) 11
        (carrSyms w (Ls (m + 1)) ++ [Sym.mark])) 4 (natSyms (n + 1) ++ [Sym.mark])) 5
        (natSyms (Wk (m + 1)) ++ [Sym.mark])) (Wk (m + 1)) w (Bs (m + 1)) (hW1 _ (by omega)) hw
        (hok (m + 1) (by omega)) (by rw [hBm]; exact hfit _ (by omega))
        (by rw [hBm']; exact hfit _ (by omega))
        (by simp [Function.update_apply, hBm]) (by simp [Function.update_apply])
        (by simp [Function.update_apply, h1])
      rw [hBm, hBm'] at hk
      refine Calculus.RunsIn.congr (Calculus.RunsIn.seq hh hk) ?_ (by omega)
      congr 1
      funext j
      fin_cases j <;> simp [Function.update_apply])
  have hs1 : qst S a dp pre = Function.update (st N) (qS 4) (natSyms N ++ Sym.mark :: S (qS 4)) := by
    rw [hupd]
    congr 1
    funext j
    fin_cases j <;> simp [Function.update_apply, h4, h5, h11]
  have hs2 : Function.update (st 0) (qS 4) (Sym.mark :: S (qS 4)) =
      qst S a dp (Function.update (Function.update (Function.update pre 5
        (natSyms (Wk N) ++ [Sym.mark])) 11 (carrSyms w (Ls (N + 1)) ++ [Sym.mark])) 4 [Sym.mark]) := by
    have e : Function.update (st 0) (qS 4) (Sym.mark :: S (qS 4)) =
        Function.update (st 0) (qS 4) (natSyms 0 ++ Sym.mark :: S (qS 4)) := rfl
    rw [e, hupd]
    simp [natSyms, TMFw.encodeNat_zero]
  rw [← hs1, hs2] at hcd
  exact Calculus.RunsIn.mono hcd (fun _ _ => trivial) le_rfl

end QLoop

/-! ## Specifications, prefixes, cleanup -/

section QSpecs

/-- The parameter kernel's specification (the body of `DrvPreParamsStmt`). -/
def ParSpecQ {E R : Type} [DecidableEq E] (J C : ℕ) (Pr : Prog (KLoc (Fin 12) E) (fun _ => Sym) R) :
    Prop :=
  ∀ (t : LayerRT) (hrest : List Sym) (S : KLoc (Fin 12) E → List Sym),
    t.ρ < t.K → 1 ≤ t.D → S (.inl 0) = t.hdr ++ hrest →
    Runs Pr S (drvPreParamsPost t S) (fun _ => True) (C * (t.hdr.length + t.D * t.K + 1) ^ J)

/-- The exact left shift's specification (the body of `ShlStmt`). -/
def ShlSpec {E R : Type} [DecidableEq E] (C : ℕ) (P : Prog (KLoc (Fin 5) E) (fun _ => Sym) R) :
    Prop :=
  ∀ (w1 w2 s : ℕ) (v : List (List CInt)) (rest r2 r3 r4 : List Sym)
    (S : KLoc (Fin 5) E → List Sym),
    1 ≤ w1 → 1 ≤ w2 → CArrFits w1 v → CArrFits w2 (mapC (shlC s) v) →
    BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 →
    S (.inl 0) = carrSyms w1 v ++ rest → S (.inl 2) = natSyms w1 ++ r2 →
    S (.inl 3) = natSyms w2 ++ r3 → S (.inl 4) = natSyms s ++ r4 →
    Runs P S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (carrSyms w2 (mapC (shlC s) v) ++ S (.inl 1)))
      (fun _ => True) (C * (cvol w1 v + cvol w2 v + w1 + w2 + bitLen s + 1))

/-- The padding's specification (the body of `DrvPadStmt`). -/
def PadSpec {E R : Type} [DecidableEq E] (C : ℕ) (Pr : Prog (KLoc (Fin 5) E) (fun _ => Sym) R) :
    Prop :=
  ∀ (N0 Npad r w : ℕ) (blks : List (List (List CInt))) (rest r1 r2 r3 r4 : List Sym)
    (S : KLoc (Fin 5) E → List Sym),
    1 ≤ N0 → 1 ≤ w → (∀ blk ∈ blks, blk.length = N0) → BlkTerm rest →
    TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 →
    S (.inl 0) = carrSyms w blks.flatten ++ rest → S (.inl 1) = natSyms N0 ++ r1 →
    S (.inl 2) = natSyms Npad ++ r2 → S (.inl 3) = natSyms r ++ r3 →
    S (.inl 4) = natSyms w ++ r4 →
    Runs Pr S
      (Function.update S (.inl 0) (carrSyms w (blks.map (padBlock Npad r)).flatten ++ rest))
      (fun _ => True)
      (C * (cvol w (blks.map (padBlock Npad r)).flatten +
        (blks.length + 1) * (bitLen N0 + bitLen Npad + bitLen r + bitLen w + 1)))

/-- The descriptor kernel's specification (the body of `DrvDescStmt`). -/
def DscSpec {E R : Type} [DecidableEq E] (J C : ℕ) (Pr : Prog (KLoc (Fin 2) E) (fun _ => Sym) R) :
    Prop :=
  ∀ (t : LayerRT) (hrest : List Sym) (S : KLoc (Fin 2) E → List Sym),
    S (.inl 0) = t.hdr ++ hrest →
    Runs Pr S (Function.update S (.inl 1) (drvDescSyms t ++ S (.inl 1))) (fun _ => True)
      (C * ((t.hdr.length + t.D * t.K + 1) ^ J + (drvDescSyms t).length))

/-- Own-stack prefixes after the floors and the parameter kernel. -/
noncomputable def preP (t : LayerRT) (j : Fin 16) : List Sym :=
  if j.val = 0 then natSyms t.w ++ [Sym.mark]
  else if j.val = 1 then natSyms (drvWg t) ++ [Sym.mark]
  else if j.val = 2 then natSyms (drvDelta t) ++ [Sym.mark]
  else if j.val = 3 then hdrSyms (preScHdr t) ++ [Sym.mark]
  else if j.val = 4 then natSyms (drvQ1 t) ++ [Sym.mark]
  else if j.val = 5 then natSyms (drvW0 t) ++ [Sym.mark]
  else if j.val = 6 then natSyms t.K ++ [Sym.mark]
  else if j.val = 7 then [drvRowsSym t]
  else if j.val = 8 then natSyms (drvKeep t) ++ [Sym.mark]
  else if j.val = 9 then natSyms (drvNpad t) ++ [Sym.mark]
  else if j.val = 10 then natSyms t.r ++ [Sym.mark]
  else [Sym.mark]

theorem preP_eq (t : LayerRT) : parPreQ t (gPreQ (fun _ => [])) = preP t := by
  funext j
  fin_cases j <;> simp [parPreQ, payQ, drvPreParamsPost, gPreQ, preP, preScHdr]

/-- Cost of the cleanup. -/
noncomputable def cleanQCost (t : LayerRT) (W : ℕ) : ℕ :=
  DriverAux.dropCost [t.w] + DriverAux.dropCost [drvWg t] + DriverAux.dropCost [drvDelta t] +
    DriverAux.dropCost (preScHdr t) + DriverAux.dropCost [W] + DriverAux.dropCost [t.K] +
    DriverAux.dropCost [drvKeep t] + DriverAux.dropCost [drvNpad t] + DriverAux.dropCost [t.r] + 9

end QSpecs

section QClean

variable {Epar Eshl Esc Eck Epad Edsc Rpar Rshl Rsc Rck Rpad Rdsc : Type}
variable [DecidableEq Epar] [DecidableEq Eshl] [DecidableEq Esc] [DecidableEq Eck]
  [DecidableEq Epad] [DecidableEq Edsc]

theorem runs_cleanQ (S : QLoc Epar Eshl Esc Eck Epad Edsc → List Sym) (a dp : List Sym)
    (t : LayerRT) (W : ℕ) :
    Calculus.RunsIn [] (cleanQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck)
      (Rpad := Rpad) (Rdsc := Rdsc))
      (qst S a dp (Function.update (Function.update (preP t) 4 [Sym.mark]) 5
        (natSyms W ++ [Sym.mark])))
      (qst S a dp (fun _ => [])) (fun _ => True) (cleanQCost t W) := by
  have h := (step_dropQ (Rpar := Rpar) (Rshl := Rshl) (Rsc := Rsc) (Rck := Rck) (Rpad := Rpad)
      (Rdsc := Rdsc) S a dp (Function.update (Function.update (preP t) 4 [Sym.mark]) 5
        (natSyms W ++ [Sym.mark])) 0 0 [t.w] [] rfl
      (by simp [Function.update_apply, preP, hdrSyms])).seq
    ((step_dropQ S a dp _ 1 0 [drvWg t] [] rfl (by simp [Function.update_apply, preP, hdrSyms])).seq
    ((step_dropQ S a dp _ 2 0 [drvDelta t] [] rfl
      (by simp [Function.update_apply, preP, hdrSyms])).seq
    ((step_dropQ S a dp _ 3 7 (preScHdr t) [Sym.mark] rfl
      (by simp [Function.update_apply, preP])).seq
    ((step_popQ S a dp _ 3 Sym.mark [] (by simp [Function.update_apply])).seq
    ((step_popQ S a dp _ 4 Sym.mark [] (by simp [Function.update_apply])).seq
    ((step_dropQ S a dp _ 5 0 [W] [] rfl (by simp [Function.update_apply, hdrSyms])).seq
    ((step_dropQ S a dp _ 6 0 [t.K] [] rfl (by simp [Function.update_apply, preP, hdrSyms])).seq
    ((step_popQ S a dp _ 7 (drvRowsSym t) [] (by simp [Function.update_apply, preP])).seq
    ((step_dropQ S a dp _ 8 0 [drvKeep t] [] rfl
      (by simp [Function.update_apply, preP, hdrSyms])).seq
    ((step_dropQ S a dp _ 9 0 [drvNpad t] [] rfl
      (by simp [Function.update_apply, preP, hdrSyms])).seq
    ((step_dropQ S a dp _ 10 0 [t.r] [] rfl (by simp [Function.update_apply, preP, hdrSyms])).seq
    ((step_popQ S a dp _ 11 Sym.mark [] (by simp [Function.update_apply, preP])).seq
    ((step_popQ S a dp _ 12 Sym.mark [] (by simp [Function.update_apply, preP])).seq
    ((step_popQ S a dp _ 13 Sym.mark [] (by simp [Function.update_apply, preP])).seq
    ((step_popQ S a dp _ 14 Sym.mark [] (by simp [Function.update_apply, preP])).seq
    (step_popQ S a dp _ 15 Sym.mark [] (by simp [Function.update_apply, preP])))))))))))))))))
  refine Calculus.RunsIn.congr h ?_ (by unfold cleanQCost; omega)
  congr 1
  funext j
  fin_cases j <;> simp [Function.update_apply]

end QClean

end SubNLogN.Machine.Layer.DrvPPAux
