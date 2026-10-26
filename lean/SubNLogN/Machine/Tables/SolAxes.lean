/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.SolAxis
import SubNLogN.Machine.Tables.TapRank

/-!
# K6 (`Machine/Tables/SolAxes.lean`): one solver axis

**Scope (honest summary).** List facts for the axis loops (`deconvOrder`, `lowerShape`,
`prefixProd` one step at a time) and the fragment `solAxisBody`: with the lower shape
`hdrSyms (t_i :: …)` on `rSH` and `A_{i+1} = A_i·t_i` on `rA`, it reads `t_i`, sets `rA := A_i`,
computes `2t_i`, `Q = closurePrec (P+2) A_i t_i`, `2^Q`, `2^(Q+q)`, pushes the solver block of
axis `i` (`solBlockProg`) and cleans up (popping `t_i` from `rSH`); exact final state, cost
`solAxisCost`.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt SubNLogN.Math.Common

/-! ## List facts -/

theorem deconvOrder_succ' (n : ℕ) :
    deconvOrder (n + 1) = (List.finRange n).map Fin.succ := by
  unfold deconvOrder
  rw [List.finRange_succ, List.filter_cons]
  simp only [Fin.val_zero, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte]
  rw [List.filter_eq_self]
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  simp

theorem length_deconvOrder' (d : ℕ) : (deconvOrder d).length = d - 1 := by
  cases d with
  | zero => simp [deconvOrder]
  | succ n => simp [deconvOrder_succ']

theorem deconvOrder_getElem (d k : ℕ) (hk : k < (deconvOrder d).length) :
    (deconvOrder d)[k] = ⟨k + 1, by rw [length_deconvOrder'] at hk; omega⟩ := by
  cases d with
  | zero => simp [deconvOrder] at hk
  | succ n =>
    have hk' : k < n := by rw [length_deconvOrder'] at hk; omega
    simp only [deconvOrder_succ', List.getElem_map, List.getElem_finRange]
    ext
    simp

theorem deconvOrder_drop (d k : ℕ) (hk : k + 1 < d) :
    (deconvOrder d).drop k = ⟨k + 1, hk⟩ :: (deconvOrder d).drop (k + 1) := by
  have hlen : k < (deconvOrder d).length := by rw [length_deconvOrder']; omega
  rw [List.drop_eq_getElem_cons hlen, deconvOrder_getElem d k hlen]

theorem lowerShape_succ {d : ℕ} (t : Fin d → ℕ) (k : ℕ) (hk : k < d) :
    lowerShape t (k + 1) = t ⟨k, hk⟩ :: lowerShape t k := by
  unfold lowerShape
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hk)]
  simp

theorem prefixProd_succ' {d : ℕ} (t : Fin d → ℕ) (j : ℕ) (hj : j < d) :
    prefixProd t (j + 1) = prefixProd t j * t ⟨j, hj⟩ := by
  unfold prefixProd
  have h : Finset.univ.filter (fun i : Fin d => (i : ℕ) < j + 1) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun i : Fin d => (i : ℕ) < j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [h, Finset.prod_insert (by simp), mul_comm]

section Body

variable (I : TB)

/-- First half of a solver axis: read `t_i`, `A_i := A_{i+1}/t_i`, `2t_i`, `Q`, `2^Q`, `2^(Q+q)`. -/
def solAxisPre : TP I :=
  (tcp I rSH rT).seq ((tdm I rA rT x40 x41).seq ((tdr I rA).seq ((tcp I x40 rA).seq
    ((tdr I x40).seq ((tcp I rT x42).seq ((tad I rT x42 r2t).seq ((tdr I x42).seq
    ((qProg I).seq ((pow2Int I rPQ rQ).seq ((tad I rQ rq x40).seq ((pow2Int I rPQq x40).seq
    (tdr I x40))))))))))))

/-- Second half: the solver block, then cleanup (popping `t_i` from `rSH`). -/
def solAxisPost : TP I :=
  (solBlockProg I).seq ((intDrop I rPQq).seq ((intDrop I rPQ).seq
    ((tdr I rQ).seq ((tdr I r2t).seq ((tdr I rT).seq (dropBlock I rSH))))))

/-- One solver axis (see the module docstring); temporaries `x40 … x60`. -/
def solAxisBody : TP I := (solAxisPre I).seq (solAxisPost I)

theorem solAxisPre_closed : (solAxisPre I).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    qProg_closed I, pow2Int_closed I _ _, callI_closed _ _ _ _, pow2Int_closed I _ _,
    callI_closed _ _ _ _⟩

theorem solAxisPost_closed : (solAxisPost I).Closed :=
  ⟨solBlockProg_closed I, intDrop_closed I _, intDrop_closed I _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, dropBlock_closed I _⟩

theorem solAxisBody_closed : (solAxisBody I).Closed :=
  ⟨solAxisPre_closed I, solAxisPost_closed I⟩

end Body

/-- Cost bound of one solver axis. -/
def solAxisCost (C KM U wT t : ℕ) : ℕ :=
  solBlockCost C KM U wT t + qCost C U + 40 * (C * (U * U + 4 * U + 1)) + 4 * U + 40

/-- The state between the two halves of a solver axis. -/
def solPreSt (B : TL → List Sym) (t A P : ℕ) : TL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update B rT (natSyms t)) rA (natSyms A)) r2t (natSyms (t + t)))
    rQ (natSyms (closurePrec (P + 2) A t))) rPQ (intSyms ((2 ^ closurePrec (P + 2) A t : ℕ) : ℤ)))
    rPQq (intSyms ((2 ^ (closurePrec (P + 2) A t + (P + 2)) : ℕ) : ℤ))

theorem cmono {C X Y : ℕ} (h : X ≤ Y) : C * X ≤ C * Y := Nat.mul_le_mul_left C h

theorem inr_ne_of_ge {j : Fin 61} (k : Fin 61) (hk : (k : ℕ) < 40) (hj : 40 ≤ (j : ℕ)) :
    (Sum.inr j : TL) ≠ Sum.inr k :=
  inr_ne_inr (by omega)

section BodySpec

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

set_option maxHeartbeats 4000000 in
theorem HT.solAxisPre_spec (hI : I.Spec Mul C) (B : TL → List Sym) (P t A U : ℕ) (L : List Sym)
    (ht2 : 2 ≤ t) (hA2 : 2 ≤ A) (hbt : bitLen t + 3 ≤ U) (hU2 : P + 2 ≤ U)
    (hU4 : bitLen A + 1 ≤ U) (hU5 : bitLen (A * t) + 1 ≤ U)
    (hQU : closurePrec (P + 2) A t + (P + 2) + 1 ≤ U)
    (hSH : B rSH = natSyms t ++ Sym.mark :: L) (hA : B rA = natSyms (A * t))
    (hq : B rq = natSyms (P + 2)) (hT0 : B rT = []) (h2t0 : B r2t = []) (hQ0 : B rQ = [])
    (hPQ0 : B rPQ = []) (hPQq0 : B rPQq = [])
    (htmp : ∀ j : Fin 61, 40 ≤ (j : ℕ) → B (.inr j) = []) (ρ : List (TP I)) :
    HT ρ B (solAxisPre I) (solPreSt B t A P) (12 * (C * (U * U + 4 * U + 1)) + qCost C U + 6) := by
  have h40 : B x40 = [] := htmp 40 (by decide)
  have h41 : B x41 = [] := htmp 41 (by decide)
  have h42 : B x42 = [] := htmp 42 (by decide)
  have h43 : B x43 = [] := htmp 43 (by decide)
  have h44 : B x44 = [] := htmp 44 (by decide)
  have h45 : B x45 = [] := htmp 45 (by decide)
  have h46 : B x46 = [] := htmp 46 (by decide)
  have h47 : B x47 = [] := htmp 47 (by decide)
  have ht0 : 0 < t := by omega
  have hdiv : A * t / t = A := Nat.mul_div_cancel A ht0
  have hmod : natSyms (A * t % t) = [] := by rw [Nat.mul_mod_left]; rfl
  have hbQ := bitLen_le_self (closurePrec (P + 2) A t)
  have hbQq := bitLen_le_self (closurePrec (P + 2) A t + (P + 2))
  have hbq := bitLen_le_self (P + 2)
  have hbtt : bitLen (t + t) ≤ bitLen t + 1 := by
    have := bitLen_add_le t t; simp only [max_self] at this; exact this
  refine (HT.seq ((HT.tcp_spec hI rSH rT (by decide) B t (Sym.mark :: L) (termOK_mark L) hSH
      ρ).mono (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)))
    (HT.seq ((HT.tdm_spec hI rA rT x40 x41 (by decide) _ (A * t) t [] [] ht0 TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hA, List.append_nil])
      (by simp (disch := decide) only [Function.update_self, hT0]) ρ).mono
      (cmono (C := C) (Y := U * U + 4 * U + 1)
        (by have hp : bitLen (A * t) * bitLen t ≤ U * U := Nat.mul_le_mul (by omega) (by omega)
            omega)))
    (HT.seq ((HT.tdr_spec hI rA _ (A * t) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hA, List.append_nil]) ρ).mono
      (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)))
    (HT.seq ((HT.tcp_spec hI x40 rA (by decide) _ A [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, hdiv, h40])
      ρ).mono (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)))
    (HT.seq ((HT.tdr_spec hI x40 _ A [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, hdiv, h40])
      ρ).mono (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)))
    (HT.seq ((HT.tcp_spec hI rT x42 (by decide) _ t [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, hT0]) ρ).mono
      (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)))
    (HT.seq ((HT.tad_spec hI rT x42 r2t (by decide) _ t t [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, hT0])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h42]) ρ).mono
      (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)))
    (HT.seq ((HT.tdr_spec hI x42 _ t [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h42]) ρ).mono
      (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)))
    (HT.seq (HT.qProg_spec hI _ (P + 2) A t U hA2 (by omega) hU2 (by omega) hbt
      (by simp (disch := decide) only [Function.update_of_ne, hq])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, hT0,
        List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hQ0])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, hmod, h41,
        List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [Function.update_of_ne, h43])
      (by simp (disch := decide) only [Function.update_of_ne, h44])
      (by simp (disch := decide) only [Function.update_of_ne, h45])
      (by simp (disch := decide) only [Function.update_of_ne, h46])
      (by simp (disch := decide) only [Function.update_of_ne, h47]) ρ)
    (HT.seq ((HT.pow2Int_spec hI rPQ rQ (by decide) _ (closurePrec (P + 2) A t) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hPQ0])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono
      (Nat.add_le_add_right (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)) 3))
    (HT.seq ((HT.tad_spec hI rQ rq x40 (by decide) _ (closurePrec (P + 2) A t) (P + 2) [] []
      TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hq, List.append_nil]) ρ).mono
      (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)))
    (HT.seq ((HT.pow2Int_spec hI rPQq x40 (by decide) _ (closurePrec (P + 2) A t + (P + 2)) []
      TermOK.nil (by simp (disch := decide) only [Function.update_of_ne, hPQq0])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self]) ρ).mono
      (Nat.add_le_add_right (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)) 3))
      ((HT.tdr_spec hI x40 _ (closurePrec (P + 2) A t + (P + 2)) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h40]) ρ).mono
      (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega))))))))))))))).of_eq ?_ ?_
  · funext g
    by_cases g1 : g = rT
    · subst g1; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, hT0, List.append_nil]
    by_cases g2 : g = rA
    · subst g2; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, List.append_nil]
    by_cases g3 : g = r2t
    · subst g3; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, h2t0, List.append_nil]
    by_cases g4 : g = rQ
    · subst g4; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self]
    by_cases g5 : g = rPQ
    · subst g5; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self]
    by_cases g6 : g = rPQq
    · subst g6; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self]
    by_cases g7 : g = x40
    · subst g7; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, h40]
    by_cases g8 : g = x41
    · subst g8; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, h41, hmod, List.append_nil]
    by_cases g9 : g = x42
    · subst g9; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, h42]
    simp only [solPreSt, Function.update_of_ne g1, Function.update_of_ne g2,
      Function.update_of_ne g3, Function.update_of_ne g4, Function.update_of_ne g5,
      Function.update_of_ne g6, Function.update_of_ne g7, Function.update_of_ne g8,
      Function.update_of_ne g9]
  · omega

set_option maxHeartbeats 4000000 in
theorem HT.solAxisPost_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (B : TL → List Sym) (ω P t A wT U : ℕ) (L : List Sym)
    (hω : 1 ≤ ω) (ht : Even t) (hw : 1 ≤ wT)
    (hU1 : ω + coeffPrec P + bitLen (2 * t) + 4 ≤ U) (hU2 : coeffPrec P + (P + 2) + 6 ≤ U)
    (hU3 : 2 * closurePrec (P + 2) A t + (P + 2) + 4 ≤ U) (hU4 : bitLen A + 1 ≤ U)
    (hfit : ∀ u < t, FitsTwos wT (muN ω P t u) ∧ FitsTwos wT (ahN ω P t u) ∧
      FitsTwos wT (gamN ω P t A u))
    (hSH : B rSH = natSyms t ++ Sym.mark :: L)
    (hW : B rW = natSyms ω) (hPC : B rPC = natSyms (coeffPrec P))
    (hNmu : B rNmu = intSyms ((2 ^ (coeffPrec P + 2 + (P + 2)) : ℕ) : ℤ))
    (hPq : B rPq = intSyms ((2 ^ (P + 2) : ℕ) : ℤ)) (hq : B rq = natSyms (P + 2))
    (hZ : B rZero = intSyms 0) (hPW : B rPW = intSyms ((2 ^ wT : ℕ) : ℤ))
    (hPW1 : B rPW1 = intSyms ((2 ^ (wT + 1) : ℕ) : ℤ))
    (hT0 : B rT = []) (h2t0 : B r2t = []) (hQ0 : B rQ = []) (hPQ0 : B rPQ = [])
    (hPQq0 : B rPQq = []) (hru : B ru = [])
    (htmp : ∀ j : Fin 61, 40 ≤ (j : ℕ) → B (.inr j) = []) (ρ : List (TP I)) :
    HT ρ (solPreSt B t A P) (solAxisPost I)
      (Function.update (Function.update (Function.update B rSH L) rA (natSyms A)) sSol
        (carrSyms wT (solRecsN ω P t A) ++ Sym.mark :: B sSol))
      (solBlockCost C KM U wT t + 5 * (C * (U * U + 4 * U + 1)) + 2 * U + 4) := by
  have hbt : bitLen t + 3 ≤ U := by
    have := bitLen_mono (show t ≤ 2 * t by omega); omega
  have hbtt : bitLen (t + t) ≤ bitLen t + 1 := by
    have := bitLen_add_le t t; simp only [max_self] at this; exact this
  have hbQ := bitLen_le_self (closurePrec (P + 2) A t)
  refine (HT.seq (HT.solBlockProg_spec hI hMul _ ω P t A wT U hω ht hw hU1 hU2 hU3 hU4 hfit
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, hru])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, hW])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, hPC])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, Function.update_self]
          try rw [two_mul])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, hNmu])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, hPq])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, hq])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, hZ])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, hPW])
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, hPW1])
      (fun j hj => by
        simp only [solPreSt]
        rw [Function.update_of_ne (inr_ne_of_ge 20 (by decide) hj),
          Function.update_of_ne (inr_ne_of_ge 19 (by decide) hj),
          Function.update_of_ne (inr_ne_of_ge 18 (by decide) hj),
          Function.update_of_ne (inr_ne_of_ge 17 (by decide) hj),
          Function.update_of_ne (inr_ne_of_ge 16 (by decide) hj),
          Function.update_of_ne (inr_ne_of_ge 15 (by decide) hj)]
        exact htmp j hj) ρ)
    (HT.seq ((HT.intDrop_spec hI rPQq _ ((2 ^ (closurePrec (P + 2) A t + (P + 2)) : ℕ) : ℤ) []
      TermOK.nil (by simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, List.append_nil]) ρ).mono
      (Nat.add_le_add_left (cmono (C := C) (Y := U * U + 4 * U + 1)
        (by rw [Int.natAbs_natCast, bitLen_two_pow]; omega)) 1))
    (HT.seq ((HT.intDrop_spec hI rPQ _ ((2 ^ closurePrec (P + 2) A t : ℕ) : ℤ) []
      TermOK.nil (by simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, List.append_nil]) ρ).mono
      (Nat.add_le_add_left (cmono (C := C) (Y := U * U + 4 * U + 1)
        (by rw [Int.natAbs_natCast, bitLen_two_pow]; omega)) 1))
    (HT.seq ((HT.tdr_spec hI rQ _ (closurePrec (P + 2) A t) [] TermOK.nil
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)))
    (HT.seq ((HT.tdr_spec hI r2t _ (t + t) [] TermOK.nil
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)))
    (HT.seq ((HT.tdr_spec hI rT _ t [] TermOK.nil
      (by simp (disch := decide) only [solPreSt, Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ).mono (cmono (C := C) (Y := U * U + 4 * U + 1) (by omega)))
      ((HT.dropBlock_spec rSH ρ (natSyms t) L (mark_not_mem_natSyms t) _
        (by simp (disch := decide) only [solPreSt, Function.update_of_ne, hSH])).mono
        (show 2 * (natSyms t).length + 2 ≤ 2 * U + 2 by rw [length_natSyms]; omega)))))))).of_eq
      ?_ ?_
  · funext g
    by_cases g0 : g = sSol
    · subst g0; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self]
    by_cases g1 : g = rSH
    · subst g1; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self]
    by_cases g2 : g = rA
    · subst g2; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self]
    by_cases g3 : g = rT
    · subst g3; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, hT0]
    by_cases g4 : g = r2t
    · subst g4; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, h2t0]
    by_cases g5 : g = rQ
    · subst g5; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, hQ0]
    by_cases g6 : g = rPQ
    · subst g6; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, hPQ0]
    by_cases g7 : g = rPQq
    · subst g7; simp (disch := decide) only [solPreSt, Function.update_of_ne,
        Function.update_self, hPQq0]
    simp only [solPreSt, Function.update_of_ne g0, Function.update_of_ne g1,
      Function.update_of_ne g2, Function.update_of_ne g3, Function.update_of_ne g4,
      Function.update_of_ne g5, Function.update_of_ne g6, Function.update_of_ne g7]
  · omega

/-- **One solver axis** `i` (`t = t_i`, `A = A_i`): from `rSH = hdrSyms (t_i :: …)` and
`rA = A_i·t_i`, push the solver block of axis `i` (`carrSyms wT (solRecsN …) ++ [mark]`) onto
`solTab`, pop `t_i` from `rSH` and leave `A_i` on `rA`; all other stacks restored. -/
theorem HT.solAxisBody_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (B : TL → List Sym) (ω P t A wT U : ℕ) (L : List Sym)
    (hω : 1 ≤ ω) (ht : Even t) (ht2 : 2 ≤ t) (hA2 : 2 ≤ A) (hw : 1 ≤ wT)
    (hU1 : ω + coeffPrec P + bitLen (2 * t) + 4 ≤ U) (hU2 : coeffPrec P + (P + 2) + 6 ≤ U)
    (hU3 : 2 * closurePrec (P + 2) A t + (P + 2) + 4 ≤ U) (hU4 : bitLen A + 1 ≤ U)
    (hU5 : bitLen (A * t) + 1 ≤ U)
    (hfit : ∀ u < t, FitsTwos wT (muN ω P t u) ∧ FitsTwos wT (ahN ω P t u) ∧
      FitsTwos wT (gamN ω P t A u))
    (hSH : B rSH = natSyms t ++ Sym.mark :: L) (hA : B rA = natSyms (A * t))
    (hW : B rW = natSyms ω) (hPC : B rPC = natSyms (coeffPrec P))
    (hNmu : B rNmu = intSyms ((2 ^ (coeffPrec P + 2 + (P + 2)) : ℕ) : ℤ))
    (hPq : B rPq = intSyms ((2 ^ (P + 2) : ℕ) : ℤ)) (hq : B rq = natSyms (P + 2))
    (hZ : B rZero = intSyms 0) (hPW : B rPW = intSyms ((2 ^ wT : ℕ) : ℤ))
    (hPW1 : B rPW1 = intSyms ((2 ^ (wT + 1) : ℕ) : ℤ))
    (hT0 : B rT = []) (h2t0 : B r2t = []) (hQ0 : B rQ = []) (hPQ0 : B rPQ = [])
    (hPQq0 : B rPQq = []) (hru : B ru = [])
    (htmp : ∀ j : Fin 61, 40 ≤ (j : ℕ) → B (.inr j) = []) (ρ : List (TP I)) :
    HT ρ B (solAxisBody I)
      (Function.update (Function.update (Function.update B rSH L) rA (natSyms A)) sSol
        (carrSyms wT (solRecsN ω P t A) ++ Sym.mark :: B sSol))
      (solAxisCost C KM U wT t) := by
  have hbt : bitLen t + 3 ≤ U := by
    have := bitLen_mono (show t ≤ 2 * t by omega); omega
  refine (HT.seq (HT.solAxisPre_spec hI B P t A U L ht2 hA2 hbt (by unfold coeffPrec at hU2; omega)
      hU4 hU5 (by omega) hSH hA hq hT0 h2t0 hQ0 hPQ0 hPQq0 htmp ρ)
    (HT.solAxisPost_spec hI hMul B ω P t A wT U L hω ht hw hU1 hU2 hU3 hU4 hfit hSH hW hPC hNmu
      hPq hq hZ hPW hPW1 hT0 h2t0 hQ0 hPQ0 hPQq0 hru htmp ρ)).of_eq rfl ?_
  unfold solAxisCost
  omega

end BodySpec

end SubNLogN.Machine.Tables
