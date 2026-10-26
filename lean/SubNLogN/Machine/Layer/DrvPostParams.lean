/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvParamsShared
import SubNLogN.Machine.Layer.DrvPostParamsScanCost

/-!
# Layer driver: the post-phase parameter kernel (`Machine/Layer/DrvPostParams.lean`)

**Scope (honest summary).** Proves `drvPostParams_holds : DrvPostParamsStmt`
(`Layer/DrvParamsDefs.lean:75`) with exponent `J = 3`. There are no hypotheses beyond the
statement's: no `KClean`, no bands on `t`. Everything is fully proved.

The kernel `DrvPostParamsAux.postProg` has registers `DrvArith.Reg2` and scratch stacks `Fin 64`.
It runs in six steps:
1. It copies the header fields `d, D, K, S` above `mark` floors on scratch stacks `0 … 3`
   (`DrvParamsAux.copyFieldN`).
2. `keepN` (`Layer/DrvParamsShared.lean`) pushes `natSyms (drvKeep t)` on `.inl 1`.
3. `npadN` (same file) pushes `natSyms (drvNpad t)` on `.inl 2`. The values `padR` and
   `2^{q₀K}` are computed only in the rows case `q₀ < D`.
4. `flagN` (this file) pushes the rows flag `drvRowsSym t` on `.inl 3`.
5. It drops the four copies.
6. `postScanN` (`Layer/DrvPostParamsScan.lean`) pushes the outputs of `.inl 4 … 7`.

Every scratch stack is restored, whatever its content at entry. `runs_postProg` states the exact
final stacks `drvPostParamsPost t S` and the cost `postCost t`. `postCost_le` bounds the cost by
`c·(|hdr| + D·K + 1)³`.
-/

namespace SubNLogN.Machine.Layer.DrvPostParamsAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability SubNLogN.Machine
  SubNLogN.Machine.NatArith SubNLogN.Machine.Layer.DrvArith SubNLogN.Machine.Layer.DrvParamsShared
open SubNLogN.Math.Networks (padR q0Of)

/-- Stack indices of the kernel: named stacks `Fin 8` (`0` the header, `1 … 7` the outputs) and
scratch stacks `Fin 64` (`0 … 3` the floored values `d, D, K, S`; `4, 5` copy temporaries; the
sub-kernels use `11 … 47` as work stacks and temporaries). -/
abbrev PK : Type := KLoc (Fin 8) (Fin 64)

/-- Stack map of `keepN`: `D, K, S ↦ .inr 1, 2, 3`, result on `.inl 1`. -/
def keepMap : Fin 16 → PK := fun i =>
  if i.val = 0 then .inr 1 else if i.val = 1 then .inr 2 else if i.val = 2 then .inr 3
  else if i.val = 3 then .inl 1 else .inr ⟨i.val + 8, by omega⟩

/-- Stack map of `npadN`: `d, D, K, S ↦ .inr 0 … 3`, result on `.inl 2`. -/
def npadMap : Fin 40 → PK := fun i =>
  if i.val = 0 then .inr 0 else if i.val = 1 then .inr 1 else if i.val = 2 then .inr 2
  else if i.val = 3 then .inr 3 else if i.val = 4 then .inl 2 else .inr ⟨i.val + 8, by omega⟩

/-- Stack map of `flagN`: `d, D ↦ .inr 0, 1`, result on `.inl 3`. -/
def rowsMap : Fin 20 → PK := fun i =>
  if i.val = 0 then .inr 0 else if i.val = 1 then .inr 1 else if i.val = 2 then .inl 3
  else .inr ⟨i.val + 8, by omega⟩

/-- Stack map of `postScanN`: header `.inl 0`, results on `.inl 4 … 7`. -/
def scanMap : Fin 40 → PK := fun i =>
  if i.val = 0 then .inl 0 else if i.val = 1 then .inl 4 else if i.val = 2 then .inl 5
  else if i.val = 3 then .inl 6 else if i.val = 4 then .inl 7 else .inr ⟨i.val + 8, by omega⟩

theorem keepMap_inj : Function.Injective keepMap := by decide
theorem npadMap_inj : Function.Injective npadMap := by decide
theorem rowsMap_inj : Function.Injective rowsMap := by decide
theorem scanMap_inj : Function.Injective scanMap := by decide

/-! ## The rows flag -/

section Flag

variable {K : Type}

/-- The stack map of `q0N` inside `flagN`. -/
def flQ0Map : Fin 16 → Fin 20 := fun i =>
  if i.val = 0 then 0 else if i.val = 1 then 3 else ⟨i.val + 4, by omega⟩

/-- **`flagN st`**: `d` on `st 0`, `D` on `st 1` (both restored) ↦ pushes the rows flag
`Sym.bit (decide (q0Of d < D))` on `st 2`; work stack `st 3`; temporaries `st 4 … st 19`. -/
noncomputable def flagN (st : Fin 20 → K) : Prog K (fun _ => Sym) Reg2 :=
  .seq (.seq ((Prog.seq (pushMark (st 3)) (q0N (st ∘ flQ0Map))).liftRegs lN)
    (.seq ((cmpN (st 3) (st 1) (st 4) (st 5)).liftRegs lN)
      (.ite (fun r => isLtR r.1) ((pushW (st 2) (.bit true)).liftRegs lN)
        ((pushW (st 2) (.bit false)).liftRegs lN))))
    ((dropF (st 3)).liftRegs lN)

/-- The cost of `flagN`. -/
noncomputable def flagCost (d D : ℕ) : ℕ :=
  (1 + q0Cost d) + ((12 * min (bitLen (q0Of d)) (bitLen D) + 15) + (1 + 1)) +
    (2 * bitLen (q0Of d) + 2)

theorem closed_flagN (st : Fin 20 → K) : (flagN st).Closed := by
  have hite : (Prog.ite (fun r : Reg2 => isLtR r.1) ((pushW (st 2) (.bit true)).liftRegs lN)
      ((pushW (st 2) (.bit false)).liftRegs lN)).Closed := by
    show Prog.FreeBelow 0 _ ∧ Prog.FreeBelow 0 _
    exact ⟨WP.W9comp.closed_liftRegs lN (closed_pushW _ _),
      WP.W9comp.closed_liftRegs lN (closed_pushW _ _)⟩
  exact WP.W9comp.closed_seq (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN
    (WP.W9comp.closed_seq (closed_pushMark _) (closed_q0N _)))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (closed_cmpN' _ _ _ _)) hite))
    (WP.W9comp.closed_liftRegs lN (closed_dropF _))

variable [DecidableEq K]

theorem runs_flagN {st : Fin 20 → K} (hst : Function.Injective st) (d D : ℕ)
    (rd rD : List Sym) (S : K → List Sym) (hrd : TermOK rd) (hrD : TermOK rD)
    (h0 : S (st 0) = natSyms d ++ rd) (h1 : S (st 1) = natSyms D ++ rD) :
    Runs (flagN st) S (Function.update S (st 2) (Sym.bit (decide (q0Of d < D)) :: S (st 2)))
      (fun _ => True) (flagCost d D) := by
  have hnd : ∀ l : List (Fin 20), l.Nodup → (l.map st).Nodup := fun l hl => hl.map hst
  obtain ⟨S1, hS1⟩ : ∃ T, T = fl S (st 3) (q0Of d) := ⟨_, rfl⟩
  obtain ⟨T1, hT1⟩ : ∃ T, T = Function.update S1 (st 2)
      (Sym.bit (decide (q0Of d < D)) :: S (st 2)) := ⟨_, rfl⟩
  have r1 : Runs (.seq (pushMark (st 3)) (q0N (st ∘ flQ0Map))) S S1 (fun _ => True)
      (1 + q0Cost d) := by
    rw [hS1]
    apply runs_fl
    have c := runs_q0N (hst.comp (by decide : Function.Injective flQ0Map)) d rd
      (Function.update S (st 3) (Sym.mark :: S (st 3))) hrd
      (by rw [show (st ∘ flQ0Map) 0 = st 0 from rfl, Function.update_of_ne (hst.ne (by decide)),
        h0])
    rw [show (st ∘ flQ0Map) 1 = st 3 from rfl, Function.update_self] at c
    exact c
  have rc : Runs ((cmpN (st 3) (st 1) (st 4) (st 5)).liftRegs lN) S1 S1
      (fun r => (lN.get r).2.2.2.2 = ordOf (q0Of d) D)
      (12 * min (bitLen (q0Of d)) (bitLen D) + 15) :=
    runs_liftRegs' lN (runs_cmpN (hnd [3, 1, 4, 5] (by decide)) (q0Of d) D
      (Sym.mark :: S (st 3)) rD S1 (termOK_mark _) hrD (by rw [hS1, fl_self])
      (by rw [hS1, fl_ne (hst.ne (by decide)), h1]))
  have e2 : S1 (st 2) = S (st 2) := by rw [hS1, fl_ne (hst.ne (by decide))]
  have rB : Runs (.seq ((cmpN (st 3) (st 1) (st 4) (st 5)).liftRegs lN)
      (.ite (fun r => isLtR r.1) ((pushW (st 2) (.bit true)).liftRegs lN)
        ((pushW (st 2) (.bit false)).liftRegs lN))) S1 T1 (fun _ => True)
      ((12 * min (bitLen (q0Of d)) (bitLen D) + 15) + (1 + 1)) := by
    by_cases h : q0Of d < D
    · refine runs_seq_ite_true rc (fun v hv => ?_) ?_
      · show decide _ = true
        rw [show v.1.2.2.2.2 = ordOf (q0Of d) D from hv, (npOrdOf_lt _ _).2 h]
        rfl
      · have c := DrvParamsAux.runs_lN (runs_pushW (st 2) (.bit true) S1)
        rw [e2] at c
        rw [hT1, decide_eq_true h]
        exact c
    · refine runs_seq_ite_false rc (fun v hv => ?_) ?_
      · show decide _ = false
        rw [show v.1.2.2.2.2 = ordOf (q0Of d) D from hv]
        exact decide_eq_false (fun h' => h ((npOrdOf_lt _ _).1 h'))
      · have c := DrvParamsAux.runs_lN (runs_pushW (st 2) (.bit false) S1)
        rw [e2] at c
        rw [hT1, decide_eq_false h]
        exact c
  have rd3 : Runs ((dropF (st 3)).liftRegs lN) T1
      (Function.update S (st 2) (Sym.bit (decide (q0Of d < D)) :: S (st 2))) (fun _ => True)
      (2 * bitLen (q0Of d) + 2) := by
    have c := runs_dropF (st 3) (q0Of d) Sym.mark (S (st 3)) T1 rfl
      (by rw [hT1, Function.update_of_ne (hst.ne (by decide)), hS1, fl_self])
    refine runs_liftRegs' lN (WP.W9comp.runs_congr c ?_)
    funext k
    rcases eq_or_ne k (st 2) with rfl | h2
    · simp +decide only [hT1, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
    rcases eq_or_ne k (st 3) with rfl | h3
    · simp +decide only [hT1, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
    simp only [hT1, hS1, fl, Function.update_apply, h2, h3, if_false]
  exact WP.W9comp.runs_seq (WP.W9comp.runs_seq (runs_liftRegs' lN r1) rB) rd3

end Flag

section FlagBound

open SubNLogN.Math.Networks (Wc)

/-- `flagCost` with `q0Cost d` and `q₀` as variables. -/
def flagGen (QC q D : ℕ) : ℕ :=
  (1 + QC) + ((12 * min (bitLen q) (bitLen D) + 15) + (1 + 1)) + (2 * bitLen q + 2)

theorem flagCost_eq (d D : ℕ) : flagCost d D = flagGen (q0Cost d) (q0Of d) D := rfl

theorem flagGen_le (c0 Q QC q d D : ℕ) (hQC : QC ≤ c0 * (bitLen d + 1) ^ 3)
    (hq : q ≤ Q * (bitLen d + 1)) :
    flagGen QC q D ≤ (c0 + 100 * (Q + 1)) * (bitLen d + bitLen D + 1) ^ 3 := by
  obtain ⟨B, hB⟩ : ∃ B, B = bitLen d + bitLen D + 1 := ⟨_, rfl⟩
  rw [← hB]
  have hB1 : 1 ≤ B := by omega
  obtain ⟨e1, e2, e3, e4⟩ := cube_facts hB1
  have hB3 : 1 ≤ B ^ 3 := le_trans hB1 e1
  have hbq : bitLen q ≤ Q * B := by
    have h1 := DrvParamsShared.bitLen_le_self' q
    have h2 : Q * (bitLen d + 1) ≤ Q * B := Nat.mul_le_mul_left Q (by omega)
    omega
  have hQB : Q * B ≤ Q * B ^ 3 := Nat.mul_le_mul_left Q e1
  have hqc : QC ≤ c0 * B ^ 3 :=
    le_trans hQC (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
  have hmin : min (bitLen q) (bitLen D) ≤ B := le_trans (min_le_right _ _) (by omega)
  have hR : (c0 + 100 * (Q + 1)) * B ^ 3 = c0 * B ^ 3 + 100 * (Q * B ^ 3) + 100 * B ^ 3 := by
    ring
  rw [hR]
  unfold flagGen
  omega

/-- `flagCost d D = O((|d| + |D| + 1)³)`. -/
theorem flagCost_le : ∃ c, ∀ d D, flagCost d D ≤ c * (bitLen d + bitLen D + 1) ^ 3 := by
  obtain ⟨c0, hc0⟩ := q0Cost_le
  obtain ⟨Q, hQ⟩ : ∃ Q, Nat.clog 2 Wc = Q := ⟨_, rfl⟩
  refine ⟨c0 + 100 * (Q + 1), fun d D => ?_⟩
  rw [flagCost_eq]
  exact flagGen_le c0 Q _ _ d D (hc0 d) (by subst hQ; exact q0Of_le d)

end FlagBound

/-- Copy of header field `i` above a floor on `w`. -/
def fldN (i : ℕ) (w : PK) : Prog PK (fun _ => Sym) Reg :=
  .seq (pushMark w) (DrvParamsAux.copyFieldN i (.inl 0) w (.inr 4) (.inr 5))

/-- The counts part: floored copies of `d, D, K, S`. -/
def countsA : Prog PK (fun _ => Sym) Reg :=
  .seq (.seq (.seq (fldN 1 (.inr 0)) (fldN 3 (.inr 1))) (fldN 6 (.inr 2))) (fldN 5 (.inr 3))

/-- Drop the floored copies. -/
def countsZ : Prog PK (fun _ => Sym) Reg :=
  .seq (.seq (.seq (dropF (.inr 3)) (dropF (.inr 2))) (dropF (.inr 1))) (dropF (.inr 0))

/-- **The post-phase parameter program.** -/
noncomputable def postProg : Prog PK (fun _ => Sym) Reg2 :=
  .seq (.seq (.seq (.seq (.seq (countsA.liftRegs lN) (keepN keepMap)) (npadN npadMap))
    (flagN rowsMap)) (countsZ.liftRegs lN)) (DrvParamsAux.postScanN scanMap)

theorem closed_postProg : postProg.Closed := by
  have hf : ∀ i w, (fldN i w).Closed := fun i w =>
    WP.W9comp.closed_seq (closed_pushMark _) (DrvParamsAux.closed_copyFieldN _ _ _ _ _)
  exact WP.W9comp.closed_seq (WP.W9comp.closed_seq (WP.W9comp.closed_seq (WP.W9comp.closed_seq
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (WP.W9comp.closed_seq
      (WP.W9comp.closed_seq (WP.W9comp.closed_seq (hf _ _) (hf _ _)) (hf _ _)) (hf _ _)))
      (closed_keepN _)) (closed_npadN _)) (closed_flagN _))
    (WP.W9comp.closed_liftRegs lN (WP.W9comp.closed_seq (WP.W9comp.closed_seq
      (WP.W9comp.closed_seq (closed_dropF _) (closed_dropF _)) (closed_dropF _))
      (closed_dropF _)))) (DrvParamsAux.closed_postScanN _)

/-- The header fields. -/
def flds (t : LayerRT) : List ℕ := [t.P, t.d, t.r, t.D, t.A, t.S, t.K, t.ρ + 1, t.w]

/-- The cost of `postProg`. -/
noncomputable def postCost (t : LayerRT) : ℕ :=
  (1 + DrvParamsAux.copyFieldCost (flds t)) + (1 + DrvParamsAux.copyFieldCost (flds t)) +
    (1 + DrvParamsAux.copyFieldCost (flds t)) + (1 + DrvParamsAux.copyFieldCost (flds t)) +
    keepCost t.D t.K t.S + npadCost t.d t.D t.K t.S + flagCost t.d t.D +
    ((2 * bitLen t.S + 2) + (2 * bitLen t.K + 2) + (2 * bitLen t.D + 2) + (2 * bitLen t.d + 2)) +
    DrvParamsAux.postScanCost t

theorem drvRowsSym_eq' (t : LayerRT) : drvRowsSym t = Sym.bit (decide (q0Of t.d < t.D)) := by
  by_cases h : q0Of t.d < t.D
  · rw [DrvParamsAux.drvRowsSym_of_rows h, decide_eq_true h]
  · rw [DrvParamsAux.drvRowsSym_of_not_rows h, decide_eq_false h]

/-- **The run of `postProg`**: exact final stacks `drvPostParamsPost t S`, cost `postCost t`. -/
theorem runs_postProg (t : LayerRT) (hrest : List Sym) (S : PK → List Sym)
    (h0 : S (.inl 0) = t.hdr ++ hrest) :
    Runs postProg S (drvPostParamsPost t S) (fun _ => True) (postCost t) := by
  have hh : S (.inl 0) = hdrSyms (flds t) ++ hrest := h0
  obtain ⟨S1, hS1⟩ : ∃ T, T = fl S (.inr 0) t.d := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ T, T = fl S1 (.inr 1) t.D := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ T, T = fl S2 (.inr 2) t.K := ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ T, T = fl S3 (.inr 3) t.S := ⟨_, rfl⟩
  obtain ⟨S5, hS5⟩ : ∃ T, T = Function.update S4 (.inl 1)
      (natSyms (2 ^ (t.K * t.D) * t.S) ++ S (.inl 1)) := ⟨_, rfl⟩
  obtain ⟨S6, hS6⟩ : ∃ T, T = Function.update S5 (.inl 2)
      (natSyms (npadVal t.d t.D t.K t.S) ++ S (.inl 2)) := ⟨_, rfl⟩
  obtain ⟨S7, hS7⟩ : ∃ T, T = Function.update S6 (.inl 3)
      (Sym.bit (decide (q0Of t.d < t.D)) :: S (.inl 3)) := ⟨_, rfl⟩
  obtain ⟨D1, hD1⟩ : ∃ T, T = Function.update S7 (.inr 3) (S (.inr 3)) := ⟨_, rfl⟩
  obtain ⟨D2, hD2⟩ : ∃ T, T = Function.update D1 (.inr 2) (S (.inr 2)) := ⟨_, rfl⟩
  obtain ⟨D3, hD3⟩ : ∃ T, T = Function.update D2 (.inr 1) (S (.inr 1)) := ⟨_, rfl⟩
  obtain ⟨D4, hD4⟩ : ∃ T, T = Function.update D3 (.inr 0) (S (.inr 0)) := ⟨_, rfl⟩
  -- the field copies
  have c1 : Runs (fldN 1 (.inr 0)) S S1 (fun _ => True)
      (1 + DrvParamsAux.copyFieldCost (flds t)) := by
    rw [hS1]
    apply runs_fl
    have c := DrvParamsAux.runs_copyFieldN (src := (.inl 0 : PK)) (dst := .inr 0) (pk := .inr 4)
      (tmp := .inr 5) (by decide) (flds t) 1 (by simp [flds]) hrest
      (Function.update S (.inr 0) (Sym.mark :: S (.inr 0)))
      (by rw [Function.update_of_ne (by decide)]; exact hh)
    rw [Function.update_self] at c
    exact c
  have c2 : Runs (fldN 3 (.inr 1)) S1 S2 (fun _ => True)
      (1 + DrvParamsAux.copyFieldCost (flds t)) := by
    rw [hS2]
    apply runs_fl
    have c := DrvParamsAux.runs_copyFieldN (src := (.inl 0 : PK)) (dst := .inr 1) (pk := .inr 4)
      (tmp := .inr 5) (by decide) (flds t) 3 (by simp [flds]) hrest
      (Function.update S1 (.inr 1) (Sym.mark :: S1 (.inr 1)))
      (by rw [Function.update_of_ne (by decide), hS1, fl_ne (by decide)]; exact hh)
    rw [Function.update_self] at c
    exact c
  have c3 : Runs (fldN 6 (.inr 2)) S2 S3 (fun _ => True)
      (1 + DrvParamsAux.copyFieldCost (flds t)) := by
    rw [hS3]
    apply runs_fl
    have c := DrvParamsAux.runs_copyFieldN (src := (.inl 0 : PK)) (dst := .inr 2) (pk := .inr 4)
      (tmp := .inr 5) (by decide) (flds t) 6 (by simp [flds]) hrest
      (Function.update S2 (.inr 2) (Sym.mark :: S2 (.inr 2)))
      (by rw [Function.update_of_ne (by decide), hS2, fl_ne (by decide), hS1, fl_ne (by decide)]
          exact hh)
    rw [Function.update_self] at c
    exact c
  have c4 : Runs (fldN 5 (.inr 3)) S3 S4 (fun _ => True)
      (1 + DrvParamsAux.copyFieldCost (flds t)) := by
    rw [hS4]
    apply runs_fl
    have c := DrvParamsAux.runs_copyFieldN (src := (.inl 0 : PK)) (dst := .inr 3) (pk := .inr 4)
      (tmp := .inr 5) (by decide) (flds t) 5 (by simp [flds]) hrest
      (Function.update S3 (.inr 3) (Sym.mark :: S3 (.inr 3)))
      (by rw [Function.update_of_ne (by decide), hS3, fl_ne (by decide), hS2, fl_ne (by decide),
            hS1, fl_ne (by decide)]
          exact hh)
    rw [Function.update_self] at c
    exact c
  -- keep, npad, rows
  have c5 : Runs (keepN keepMap) S4 S5 (fun _ => True) (keepCost t.D t.K t.S) := by
    have c := runs_keepN keepMap_inj t.D t.K t.S (Sym.mark :: S (.inr 1)) (Sym.mark :: S (.inr 2))
      (Sym.mark :: S (.inr 3)) S4 (termOK_mark _) (termOK_mark _) (termOK_mark _)
      (by simp +decide only [show keepMap 0 = .inr 1 from rfl, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false])
      (by simp +decide only [show keepMap 1 = .inr 2 from rfl, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false])
      (by simp +decide only [show keepMap 2 = .inr 3 from rfl, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false])
    have e : S4 (keepMap 3) = S (.inl 1) := by
      simp +decide only [show keepMap 3 = .inl 1 from rfl, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false]
    rw [e, show keepMap 3 = .inl 1 from rfl, ← hS5] at c
    exact c
  have c6 : Runs (npadN npadMap) S5 S6 (fun _ => True) (npadCost t.d t.D t.K t.S) := by
    have c := runs_npadN npadMap_inj t.d t.D t.K t.S (Sym.mark :: S (.inr 0))
      (Sym.mark :: S (.inr 1)) (Sym.mark :: S (.inr 2)) (Sym.mark :: S (.inr 3)) S5
      (termOK_mark _) (termOK_mark _) (termOK_mark _) (termOK_mark _)
      (by simp +decide only [show npadMap 0 = .inr 0 from rfl, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false])
      (by simp +decide only [show npadMap 1 = .inr 1 from rfl, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false])
      (by simp +decide only [show npadMap 2 = .inr 2 from rfl, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false])
      (by simp +decide only [show npadMap 3 = .inr 3 from rfl, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false])
    have e : S5 (npadMap 4) = S (.inl 2) := by
      simp +decide only [show npadMap 4 = .inl 2 from rfl, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false]
    rw [e, show npadMap 4 = .inl 2 from rfl, ← hS6] at c
    exact c
  have c7 : Runs (flagN rowsMap) S6 S7 (fun _ => True) (flagCost t.d t.D) := by
    have c := runs_flagN rowsMap_inj t.d t.D (Sym.mark :: S (.inr 0))
      (Sym.mark :: S (.inr 1)) S6 (termOK_mark _) (termOK_mark _)
      (by simp +decide only [show rowsMap 0 = .inr 0 from rfl, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false])
      (by simp +decide only [show rowsMap 1 = .inr 1 from rfl, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false])
    have e : S6 (rowsMap 2) = S (.inl 3) := by
      simp +decide only [show rowsMap 2 = .inl 3 from rfl, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false]
    rw [e, show rowsMap 2 = .inl 3 from rfl, ← hS7] at c
    exact c
  -- drop the floored copies
  have c8 : Runs (dropF (.inr 3 : PK)) S7 D1 (fun _ => True) (2 * bitLen t.S + 2) := by
    have c := runs_dropF (.inr 3 : PK) t.S Sym.mark (S (.inr 3)) S7 rfl
      (by simp +decide only [hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply,
        if_true, if_false])
    rw [← hD1] at c
    exact c
  have c9 : Runs (dropF (.inr 2 : PK)) D1 D2 (fun _ => True) (2 * bitLen t.K + 2) := by
    have c := runs_dropF (.inr 2 : PK) t.K Sym.mark (S (.inr 2)) D1 rfl
      (by simp +decide only [hD1, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply,
        if_true, if_false])
    rw [← hD2] at c
    exact c
  have c10 : Runs (dropF (.inr 1 : PK)) D2 D3 (fun _ => True) (2 * bitLen t.D + 2) := by
    have c := runs_dropF (.inr 1 : PK) t.D Sym.mark (S (.inr 1)) D2 rfl
      (by simp +decide only [hD2, hD1, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false])
    rw [← hD3] at c
    exact c
  have c11 : Runs (dropF (.inr 0 : PK)) D3 D4 (fun _ => True) (2 * bitLen t.d + 2) := by
    have c := runs_dropF (.inr 0 : PK) t.d Sym.mark (S (.inr 0)) D3 rfl
      (by simp +decide only [hD3, hD2, hD1, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false])
    rw [← hD4] at c
    exact c
  -- the scan
  have c12 := DrvParamsAux.runs_postScanN scanMap_inj t hrest D4
    (by simp +decide only [show scanMap 0 = .inl 0 from rfl, hD4, hD3, hD2, hD1, hS7, hS6, hS5,
      hS4, hS3, hS2, hS1, fl, Function.update_apply, if_true, if_false]; exact h0)
  rw [show scanMap 1 = .inl 4 from rfl, show scanMap 2 = .inl 5 from rfl,
    show scanMap 3 = .inl 6 from rfl, show scanMap 4 = .inl 7 from rfl] at c12
  -- composition
  have hA := runs_liftRegs' lN (WP.W9comp.runs_seq (WP.W9comp.runs_seq
    (WP.W9comp.runs_seq c1 c2) c3) c4)
  have hZ := runs_liftRegs' lN (WP.W9comp.runs_seq (WP.W9comp.runs_seq
    (WP.W9comp.runs_seq c8 c9) c10) c11)
  have hall := WP.W9comp.runs_seq (WP.W9comp.runs_seq (WP.W9comp.runs_seq
    (WP.W9comp.runs_seq (WP.W9comp.runs_seq hA c5) c6) c7) hZ) c12
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial)
    (le_of_eq (by unfold postCost; omega))
  funext l
  rcases l with i | e
  · fin_cases i <;>
      simp +decide only [hD4, hD3, hD2, hD1, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false, drvPostParamsPost, drvKeep, drvNpad_eq,
        drvRowsSym_eq'] <;>
      rfl
  · rcases eq_or_ne e 0 with rfl | he0
    · simp +decide only [hD4, hD3, hD2, hD1, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false, drvPostParamsPost]
    rcases eq_or_ne e 1 with rfl | he1
    · simp +decide only [hD4, hD3, hD2, hD1, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false, drvPostParamsPost]
    rcases eq_or_ne e 2 with rfl | he2
    · simp +decide only [hD4, hD3, hD2, hD1, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false, drvPostParamsPost]
    rcases eq_or_ne e 3 with rfl | he3
    · simp +decide only [hD4, hD3, hD2, hD1, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
        Function.update_apply, if_true, if_false, drvPostParamsPost]
    simp only [hD4, hD3, hD2, hD1, hS7, hS6, hS5, hS4, hS3, hS2, hS1, fl,
      Function.update_apply, Sum.inr.injEq, he0, he1, he2, he3, reduceCtorEq, if_false,
      drvPostParamsPost]

/-- `postCost` with every sub-cost and bit length as a variable. -/
def postGen (CF KC NC FC bS bK bD bd SC : ℕ) : ℕ :=
  (1 + CF) + (1 + CF) + (1 + CF) + (1 + CF) + KC + NC + FC +
    ((2 * bS + 2) + (2 * bK + 2) + (2 * bD + 2) + (2 * bd + 2)) + SC

theorem postCost_eq (t : LayerRT) : postCost t = postGen (DrvParamsAux.copyFieldCost (flds t))
    (keepCost t.D t.K t.S) (npadCost t.d t.D t.K t.S) (flagCost t.d t.D) (bitLen t.S)
    (bitLen t.K) (bitLen t.D) (bitLen t.d) (DrvParamsAux.postScanCost t) := rfl

theorem postGen_le (L DK CF KC NC FC bS bK bD bd SC ck cn cr cs : ℕ) (hCF : CF = 13 * L + 12)
    (hS : bS + 1 ≤ L) (hK : bK + 1 ≤ L) (hD : bD + 1 ≤ L) (hd : bd + 1 ≤ L)
    (hk : KC ≤ ck * (bS + bK + bD + DK + 1) ^ 3)
    (hn : NC ≤ cn * (bd + bS + bK + bD + DK + 1) ^ 3)
    (hr : FC ≤ cr * (bd + bD + 1) ^ 3) (hs : SC ≤ cs * (L + DK + 1) ^ 3) :
    postGen CF KC NC FC bS bK bD bd SC ≤
      (200 + 27 * ck + 64 * cn + 8 * cr + cs) * (L + DK + 1) ^ 3 := by
  obtain ⟨B, hB⟩ : ∃ B, B = L + DK + 1 := ⟨_, rfl⟩
  rw [← hB] at hs ⊢
  have hB1 : 1 ≤ B := by omega
  obtain ⟨e1, e2, e3, e4⟩ := cube_facts hB1
  have hB3 : 1 ≤ B ^ 3 := le_trans hB1 e1
  have hk' : KC ≤ 27 * ck * B ^ 3 := by
    calc KC ≤ ck * (bS + bK + bD + DK + 1) ^ 3 := hk
      _ ≤ ck * (3 * B) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
      _ = 27 * ck * B ^ 3 := by ring
  have hn' : NC ≤ 64 * cn * B ^ 3 := by
    calc NC ≤ cn * (bd + bS + bK + bD + DK + 1) ^ 3 := hn
      _ ≤ cn * (4 * B) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
      _ = 64 * cn * B ^ 3 := by ring
  have hr' : FC ≤ 8 * cr * B ^ 3 := by
    calc FC ≤ cr * (bd + bD + 1) ^ 3 := hr
      _ ≤ cr * (2 * B) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
      _ = 8 * cr * B ^ 3 := by ring
  have hR : (200 + 27 * ck + 64 * cn + 8 * cr + cs) * B ^ 3 =
      200 * B ^ 3 + 27 * ck * B ^ 3 + 64 * cn * B ^ 3 + 8 * cr * B ^ 3 + cs * B ^ 3 := by ring
  rw [hR]
  unfold postGen
  omega

/-- `postCost t = O((|hdr| + D·K + 1)³)`. -/
theorem postCost_le : ∃ c, ∀ t : LayerRT, postCost t ≤ c * (t.hdr.length + t.D * t.K + 1) ^ 3 := by
  obtain ⟨ck, hck⟩ := keepCost_le
  obtain ⟨cn, hcn⟩ := npadCost_le
  obtain ⟨cr, hcr⟩ := flagCost_le
  obtain ⟨cs, hcs⟩ := DrvParamsAux.postScanCost_le
  refine ⟨200 + 27 * ck + 64 * cn + 8 * cr + cs, fun t => ?_⟩
  rw [postCost_eq]
  exact postGen_le t.hdr.length (t.D * t.K) _ _ _ _ _ _ _ _ _ ck cn cr cs rfl
    (DrvParamsAux.bitLen_hdr_S t) (DrvParamsAux.bitLen_hdr_K t) (DrvParamsAux.bitLen_hdr_D t)
    (DrvParamsAux.bitLen_hdr_d t) (hck _ _ _) (hcn _ _ _ _) (hcr _ _) (hcs t)

end SubNLogN.Machine.Layer.DrvPostParamsAux

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability SubNLogN.Machine

/-- **`DrvPostParamsStmt` holds** (exponent `J = 3`, no hypotheses beyond the statement's).

The kernel `DrvPostParamsAux.postProg` copies the header fields `d, D, K, S` above floors on
scratch stacks, computes `drvKeep t = 2^{KD}·S` (`keepN`), `drvNpad t` (`npadN`; the
padding value `padR` and `2^{q₀K}` are computed only when `q₀ < D`), the rows flag
(`flagN`), drops the copies and runs the header scan `postScanN` for the outputs on stacks
`4 … 7`. Every scratch stack is restored (arbitrary content at entry). Cost
`postCost t ≤ c·(|hdr| + D·K + 1)³` (`postCost_le`). -/
theorem drvPostParams_holds : DrvPostParamsStmt := by
  obtain ⟨c, hc⟩ := DrvPostParamsAux.postCost_le
  refine ⟨3, c, fun _ => ⟨Fin 64, inferInstance, inferInstance, DrvArith.Reg2,
    DrvPostParamsAux.postProg, inferInstance, inferInstance, DrvPostParamsAux.closed_postProg,
    ?_⟩⟩
  intro t hrest S h0
  exact WP.W9comp.runs_mono (DrvPostParamsAux.runs_postProg t hrest S h0) (fun _ _ => trivial)
    (hc t)

end SubNLogN.Machine.Layer
