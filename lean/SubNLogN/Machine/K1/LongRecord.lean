/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.LongRecordBase
import WP.W3s.Math
import Mathlib.Tactic.Linarith

/-!
# K1, Lemma A.5 (`K1/LongRecord.lean`): the long-record address-dependent scan

**Result.** `c3LongRecordScan_holds α F J : C3LongRecordScanStmt α F J` for all `α F J`
(statement: `SubNLogN/Machine/Contracts/Streams.lean`; paper: Lemma A.5 (`lem:transfer-long-record`);
`c3`/`C3` is a historical name from an earlier draft for Lemma A.5, kept for identifier stability).
The statement is an implication: from an address routine (`C3AddrStmt α J`) and a payload
routine (`C3PayloadStmt F`) it builds the scan kernel. Nothing else is assumed: no `sorry`, no
extra hypothesis. The per-record length hypothesis `(bitLen M + |d| + 1)^J ≤ |p_x| + 1` is part of
the contract statement itself.

## Program design
Stacks `KLoc (Fin 3) (Ea ⊕ (Ef ⊕ Fin 5))`: named `0` source, `1` destination, `2` descriptor;
`Ea`/`Ef` are the routines' private scratch stacks; the own scratch stacks are `X` (record
counter), `Xt` (its temporary), `A` (address data), `T` (payload output), `U` (output staging).
Registers `Option Sym × (Ra × Rf)`: a work register and the routines' registers (lenses).
1. Push `mark` on `X` (counter `x = 0` above it) and on `U` (staging guard); peek the source.
2. While the source top is a record symbol (bit or `sep`), for record `x` with payload `p`:
   a. the address routine on `(X, descriptor, A)`: `A := recSyms (α d x) ++ A`;
   b. the payload routine on `(source, A, T)`: pops `recSyms p`, `T := recSyms (F a p) ++ T`;
   c. `dropBits A` drops the address record;
   d. `moveRec T U` (W4) moves the output record to `U`, reversed, so `U` holds the outputs
      in up orientation;
   e. `inc X Xt` sets `x := x + 1`; then peek the source.
3. `rewindTo U dst mark`: one reversing transfer puts the outputs, first record on top, onto the
   destination and drops the guard.
4. `dropBits X` drops the counter and its guard.
Every scratch stack ends with its initial content (restored convention).

## Cost accounting
For record `x` let `n = |p_x| + 1`. The hypothesis gives `(bitLen M + |d| + 1)^J ≤ n`, and
`bitLen x ≤ bitLen M`. Then:
* the address routine costs `≤ Ca·n`, and its output has `|α d x| + 1 ≤ Ca·n` (`runs_length_le`);
* the payload routine costs `≤ Cf·(|p| + |a| + 1) ≤ Cf(1+Ca)·n`, and `|F a p| + 1 ≤ Cf(1+Ca)·n`;
* `dropBits` and `moveRec` are linear in these outputs; the peek and the loop test cost `2`;
* the increment costs `6·ones (encodeNat x) + 9`, amortized `≤ 15` per record (`incSeqCost_le`).
The loop costs `≤ Kp·V + 16·M + 1` with `Kp = 3Ca + 4Cf(1+Ca) + 1`. The final transfer costs
`3·vol(out) + 2 ≤ 3Cf(1+Ca)·V + 2` and the counter drop `2·bitLen M + 2`. Since `M ≤ V`, the
total is `≤ C·(V + 1)` with `C = Kp + 3Cf(1+Ca) + 28` (`scanC`).
-/

namespace SubNLogN.Machine.K1

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## The premise specifications (bodies of `C3AddrStmt`, `C3PayloadStmt`) -/

/-- The spec in `C3AddrStmt α J` (`Contracts/Streams.lean`), for one program `P` with
constant `C`. -/
def AddrSpec (α : List Bool → ℕ → List Bool) (J : ℕ) {E R : Type} [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc (Fin 3) E) (fun _ => Sym) R) : Prop :=
  ∀ (x : ℕ) (d : List Bool) (r0 r1 : List Sym) (S : KLoc (Fin 3) E → List Sym), TermOK r0 →
    S (.inl 0) = natSyms x ++ r0 → S (.inl 1) = recSyms d ++ r1 →
    Runs P S (Function.update S (.inl 2) (recSyms (α d x) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen x + d.length + 1) ^ J)

/-- The spec in `C3PayloadStmt F` (`Contracts/Streams.lean`), for one program `P` with
constant `C`. -/
def PayloadSpec (F : List Bool → List Bool → List Bool) {E R : Type} [DecidableEq E] (C : ℕ)
    (P : Prog (KLoc (Fin 3) E) (fun _ => Sym) R) : Prop :=
  ∀ (p a : List Bool) (rest r1 : List Sym) (S : KLoc (Fin 3) E → List Sym),
    S (.inl 0) = recSyms p ++ rest → S (.inl 1) = recSyms a ++ r1 →
    Runs P S
      (Function.update (Function.update S (.inl 0) rest) (.inl 2)
        (recSyms (F a p) ++ S (.inl 2)))
      (fun _ => True) (C * (p.length + a.length + 1))

/-- The address record is no longer than the address routine's cost. -/
theorem addr_len_le {α : List Bool → ℕ → List Bool} {J : ℕ} {E R : Type} [DecidableEq E]
    {C : ℕ} {P : Prog (KLoc (Fin 3) E) (fun _ => Sym) R} (h : AddrSpec α J C P)
    (hR : Nonempty R) (x : ℕ) (d : List Bool) :
    (α d x).length + 1 ≤ C * (bitLen x + d.length + 1) ^ J := by
  let S : KLoc (Fin 3) E → List Sym :=
    Function.update (Function.update (fun _ => []) (.inl 0) (natSyms x)) (.inl 1) (recSyms d)
  have h0 : S (.inl 0) = natSyms x ++ [] := by simp [S]
  have h1 : S (.inl 1) = recSyms d ++ [] := by simp [S]
  have hr := runs_length_le hR (h x d [] [] S TermOK.nil h0 h1) (.inl 2)
  simpa [S, length_recSyms] using hr

/-- The payload output record is no longer than the payload routine's cost. -/
theorem payload_len_le {F : List Bool → List Bool → List Bool} {E R : Type} [DecidableEq E]
    {C : ℕ} {P : Prog (KLoc (Fin 3) E) (fun _ => Sym) R} (h : PayloadSpec F C P)
    (hR : Nonempty R) (p a : List Bool) :
    (F a p).length + 1 ≤ C * (p.length + a.length + 1) := by
  let S : KLoc (Fin 3) E → List Sym :=
    Function.update (Function.update (fun _ => []) (.inl 0) (recSyms p)) (.inl 1) (recSyms a)
  have h0 : S (.inl 0) = recSyms p ++ [] := by simp [S]
  have h1 : S (.inl 1) = recSyms a ++ [] := by simp [S]
  have hr := runs_length_le hR (h p a [] [] S h0 h1) (.inl 2)
  simpa [S, length_recSyms] using hr

/-! ## Layout -/

/-- Private scratch of the scan: the address routine's, the payload routine's, five own stacks. -/
abbrev ScanE (Ea Ef : Type) : Type := Ea ⊕ (Ef ⊕ Fin 5)

/-- Stacks of the scan kernel. -/
abbrev ScanL (Ea Ef : Type) : Type := KLoc (Fin 3) (ScanE Ea Ef)

/-- Registers of the scan: a work register, then the two routines' registers. -/
abbrev ScanR (Ra Rf : Type) : Type := Option Sym × (Ra × Rf)

section Layout

variable {Ea Ef : Type}

/-- Named stack `0`: the source array (consumed). -/
abbrev sSrc : ScanL Ea Ef := .inl 0
/-- Named stack `1`: the destination. -/
abbrev sDst : ScanL Ea Ef := .inl 1
/-- Named stack `2`: the descriptor record (restored). -/
abbrev sDesc : ScanL Ea Ef := .inl 2
/-- Own scratch: the record counter `x` (above a guard `mark`). -/
abbrev sX : ScanL Ea Ef := .inr (.inr (.inr 0))
/-- Own scratch: temporary of the counter increment. -/
abbrev sXt : ScanL Ea Ef := .inr (.inr (.inr 1))
/-- Own scratch: the address-data record. -/
abbrev sA : ScanL Ea Ef := .inr (.inr (.inr 2))
/-- Own scratch: the payload routine's output record. -/
abbrev sT : ScanL Ea Ef := .inr (.inr (.inr 3))
/-- Own scratch: the outputs in up orientation (above a guard `mark`). -/
abbrev sU : ScanL Ea Ef := .inr (.inr (.inr 4))

/-- The address routine's stacks inside the scan: `0 ↦ X`, `1 ↦` descriptor, `2 ↦ A`, its
scratch to `Ea`. -/
def embA : KLoc (Fin 3) Ea → ScanL Ea Ef
  | .inl i => if i = 0 then sX else if i = 1 then sDesc else sA
  | .inr e => .inr (.inl e)

/-- The payload routine's stacks inside the scan: `0 ↦` source, `1 ↦ A`, `2 ↦ T`, its scratch
to `Ef`. -/
def embF : KLoc (Fin 3) Ef → ScanL Ea Ef
  | .inl i => if i = 0 then sSrc else if i = 1 then sA else sT
  | .inr e => .inr (.inr (.inl e))

theorem embA_injective : Function.Injective (embA : KLoc (Fin 3) Ea → ScanL Ea Ef) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [embA]
  · fin_cases i <;> simp [embA] at h
  · fin_cases j <;> simp [embA] at h
  · simp only [embA, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem embF_injective : Function.Injective (embF : KLoc (Fin 3) Ef → ScanL Ea Ef) := by
  rintro (i | e) (j | e') h
  · fin_cases i <;> fin_cases j <;> simp_all [embF]
  · fin_cases i <;> simp [embF] at h
  · fin_cases j <;> simp [embF] at h
  · simp only [embF, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

end Layout

/-- Lens onto the work register. -/
def lO {Ra Rf : Type} : Lens (ScanR Ra Rf) (Option Sym) := Lens.fst _ _

/-- Lens onto the address routine's registers. -/
def lA {Ra Rf : Type} : Lens (ScanR Ra Rf) Ra := (Lens.snd _ _).comp (Lens.fst _ _)

/-- Lens onto the payload routine's registers. -/
def lF {Ra Rf : Type} : Lens (ScanR Ra Rf) Rf := (Lens.snd _ _).comp (Lens.snd _ _)

/-! ## The program -/

section Program

variable {Ea Ef Ra Rf : Type}

/-- A work-register program run inside the scan (through `lO`). -/
abbrev wk (p : SProg (ScanL Ea Ef)) : Prog (ScanL Ea Ef) (fun _ => Sym) (ScanR Ra Rf) :=
  p.liftRegs lO

/-- Loop body for one record: address routine, payload routine, drop the address record, stage
the output record on `U`, increment the counter, peek the source. -/
def c3Body (Pa : Prog (KLoc (Fin 3) Ea) (fun _ => Sym) Ra)
    (Pf : Prog (KLoc (Fin 3) Ef) (fun _ => Sym) Rf) :
    Prog (ScanL Ea Ef) (fun _ => Sym) (ScanR Ra Rf) :=
  .seq (callInj embA lA Pa) (.seq (callInj embF lF Pf) (.seq (wk (dropBits sA))
    (.seq (wk (moveRec sT sU)) (.seq (wk (inc sX sXt)) (wk (peekR sSrc))))))

/-- **The Lemma A.5 (`lem:transfer-long-record`) scan program (`c3Prog`).** -/
def c3Prog (Pa : Prog (KLoc (Fin 3) Ea) (fun _ => Sym) Ra)
    (Pf : Prog (KLoc (Fin 3) Ef) (fun _ => Sym) Rf) :
    Prog (ScanL Ea Ef) (fun _ => Sym) (ScanR Ra Rf) :=
  .seq (wk (pushC sX .mark)) (.seq (wk (pushC sU .mark)) (.seq (wk (peekR sSrc))
    (.seq (.loop (fun r => isRecTop r.1) (c3Body Pa Pf))
      (.seq (wk (WP.W9comp.rewindTo sU sDst .mark)) (wk (dropBits sX))))))

theorem closed_c3Prog {Pa : Prog (KLoc (Fin 3) Ea) (fun _ => Sym) Ra}
    {Pf : Prog (KLoc (Fin 3) Ef) (fun _ => Sym) Rf} (hPa : Pa.Closed) (hPf : Pf.Closed) :
    (c3Prog Pa Pf).Closed := by
  have hw : ∀ p : SProg (ScanL Ea Ef), p.Closed → (wk (Ra := Ra) (Rf := Rf) p).Closed :=
    fun p hp => WP.W9comp.closed_liftRegs lO hp
  have hpush : ∀ (k : ScanL Ea Ef) (x : Sym), (pushC k x).Closed := fun k x => by
    simp [Prog.Closed, Prog.FreeBelow, pushC]
  have hpeek : ∀ k : ScanL Ea Ef, (peekR k).Closed := fun k => by
    simp [Prog.Closed, Prog.FreeBelow, peekR]
  have hmove : (moveRec (sT : ScanL Ea Ef) sU).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, pushR, popR]
  have hinc : (inc (sX : ScanL Ea Ef) sXt).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, inc, incFix, scanLoop, Lib.scanBody, moveBits,
      moveBitsBody, pushC, popR, pushR, restoreR, skip]
  have hrew : (WP.W9comp.rewindTo (sU : ScanL Ea Ef) sDst .mark).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, WP.W9comp.rewindTo, WP.W9comp.rewindBody, pushR, popR]
  have hbody : (c3Body Pa Pf).Closed :=
    ⟨closed_callInj _ _ hPa, closed_callInj _ _ hPf, hw _ (closed_dropBits _), hw _ hmove,
      hw _ hinc, hw _ (hpeek _)⟩
  exact ⟨hw _ (hpush _ _), hw _ (hpush _ _), hw _ (hpeek _), hbody, hw _ hrew,
    hw _ (closed_dropBits _)⟩

end Program

/-! ## States of the scan -/

section States

variable {Ea Ef : Type}

/-- Extensionality over the scan's stacks, by cases (the routines' scratch families `Ea`, `Ef`
are handled uniformly, never enumerated). -/
theorem scanL_funext {f g : ScanL Ea Ef → List Sym}
    (h0 : f sSrc = g sSrc) (h1 : f sDst = g sDst) (h2 : f sDesc = g sDesc)
    (hX : f sX = g sX) (hXt : f sXt = g sXt) (hA : f sA = g sA) (hT : f sT = g sT)
    (hU : f sU = g sU) (hEa : ∀ e, f (.inr (.inl e)) = g (.inr (.inl e)))
    (hEf : ∀ e, f (.inr (.inr (.inl e))) = g (.inr (.inr (.inl e)))) : f = g := by
  funext k
  rcases k with i | e | e | i
  · fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · exact hEa e
  · exact hEf e
  · fin_cases i
    · exact hX
    · exact hXt
    · exact hA
    · exact hT
    · exact hU

variable [DecidableEq Ea] [DecidableEq Ef]

/-- The scan's stacks: source, `X`, `A`, `T`, `U` set; everything else as in `S0`. -/
def st5 (S0 : ScanL Ea Ef → List Sym) (src X A T U : List Sym) : ScanL Ea Ef → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update S0
    sSrc src) sX X) sA A) sT T) sU U

variable (S0 : ScanL Ea Ef → List Sym) (src X A T U : List Sym)

@[simp] theorem st5_src : st5 S0 src X A T U sSrc = src := by simp [st5]
@[simp] theorem st5_X : st5 S0 src X A T U sX = X := by simp [st5]
@[simp] theorem st5_A : st5 S0 src X A T U sA = A := by simp [st5]
@[simp] theorem st5_T : st5 S0 src X A T U sT = T := by simp [st5]
@[simp] theorem st5_U : st5 S0 src X A T U sU = U := by simp [st5]
@[simp] theorem st5_dst : st5 S0 src X A T U sDst = S0 sDst := by simp [st5]
@[simp] theorem st5_desc : st5 S0 src X A T U sDesc = S0 sDesc := by simp [st5]

@[simp] theorem st5_upd_src (src' : List Sym) :
    Function.update (st5 S0 src X A T U) sSrc src' = st5 S0 src' X A T U := by
  apply scanL_funext <;> intros <;> simp [st5]

@[simp] theorem st5_upd_X (X' : List Sym) :
    Function.update (st5 S0 src X A T U) sX X' = st5 S0 src X' A T U := by
  apply scanL_funext <;> intros <;> simp [st5]

@[simp] theorem st5_upd_A (A' : List Sym) :
    Function.update (st5 S0 src X A T U) sA A' = st5 S0 src X A' T U := by
  apply scanL_funext <;> intros <;> simp [st5]

@[simp] theorem st5_upd_T (T' : List Sym) :
    Function.update (st5 S0 src X A T U) sT T' = st5 S0 src X A T' U := by
  apply scanL_funext <;> intros <;> simp [st5]

@[simp] theorem st5_upd_U (U' : List Sym) :
    Function.update (st5 S0 src X A T U) sU U' = st5 S0 src X A T U' := by
  apply scanL_funext <;> intros <;> simp [st5]

/-- Loop state after `x` records: `vs` remain on the source, `X` holds the counter `x` above its
guard, `U` holds `acc` (the finished outputs, reversed) above its guard. -/
def c3St (rest : List Sym) (x : ℕ) (vs : List (List Bool)) (acc : List Sym) :
    ScanL Ea Ef → List Sym :=
  st5 S0 (arrSyms vs ++ rest) (natSyms x ++ Sym.mark :: S0 sX) (S0 sA) (S0 sT)
    (acc ++ Sym.mark :: S0 sU)

end States

/-! ## The two routine calls -/

section Calls

variable {Ea Ef Ra Rf : Type} [DecidableEq Ea] [DecidableEq Ef]

theorem runs_callA {α : List Bool → ℕ → List Bool} {J Ca : ℕ}
    {Pa : Prog (KLoc (Fin 3) Ea) (fun _ => Sym) Ra} (hA : AddrSpec α J Ca Pa)
    (B : ScanL Ea Ef → List Sym) (x : ℕ) (d : List Bool) (r0 r1 : List Sym) (hr0 : TermOK r0)
    (hX : B sX = natSyms x ++ r0) (hD : B sDesc = recSyms d ++ r1) :
    Runs (callInj embA (lA (Rf := Rf)) Pa) B (Function.update B sA (recSyms (α d x) ++ B sA))
      (fun _ => True) (Ca * (bitLen x + d.length + 1) ^ J) := by
  have he : (embA (.inl 2) : ScanL Ea Ef) = sA := by simp [embA]
  have hP := hA x d r0 r1 (B ∘ embA) hr0 (by simpa [embA] using hX) (by simpa [embA] using hD)
  refine runs_callInj (Q := fun _ => True) embA_injective lA ?_ ?_
  · rw [← he, Function.update_comp_eq_of_injective B embA_injective]
    exact hP
  · intro k hk
    refine Function.update_of_ne ?_ _ _
    rintro rfl
    exact hk (.inl 2) he

theorem runs_callF {F : List Bool → List Bool → List Bool} {Cf : ℕ}
    {Pf : Prog (KLoc (Fin 3) Ef) (fun _ => Sym) Rf} (hF : PayloadSpec F Cf Pf)
    (B : ScanL Ea Ef → List Sym) (p a : List Bool) (rest r1 : List Sym)
    (hS : B sSrc = recSyms p ++ rest) (hA : B sA = recSyms a ++ r1) :
    Runs (callInj embF (lF (Ra := Ra)) Pf) B
      (Function.update (Function.update B sSrc rest) sT (recSyms (F a p) ++ B sT))
      (fun _ => True) (Cf * (p.length + a.length + 1)) := by
  have h0 : (embF (.inl 0) : ScanL Ea Ef) = sSrc := by simp [embF]
  have h2 : (embF (.inl 2) : ScanL Ea Ef) = sT := by simp [embF]
  have hP := hF p a rest r1 (B ∘ embF) (by simpa [embF] using hS) (by simpa [embF] using hA)
  refine runs_callInj (Q := fun _ => True) embF_injective lF ?_ ?_
  · rw [← h0, ← h2, Function.update_comp_eq_of_injective _ embF_injective,
      Function.update_comp_eq_of_injective _ embF_injective]
    exact hP
  · intro k hk
    have hk0 : k ≠ sSrc := by
      rintro rfl
      exact hk (.inl 0) h0
    have hk2 : k ≠ sT := by
      rintro rfl
      exact hk (.inl 2) h2
    rw [Function.update_of_ne hk2, Function.update_of_ne hk0]

end Calls

/-! ## One loop iteration -/

/-- Per-record cost factor `Kp = 3·Ca + 4·Cf·(1+Ca) + 1`. -/
def scanKp (Ca Cf : ℕ) : ℕ := 3 * Ca + 4 * (Cf * (1 + Ca)) + 1

/-- The kernel's cost constant `C = Kp + 3·Cf·(1+Ca) + 28`. -/
def scanC (Ca Cf : ℕ) : ℕ := scanKp Ca Cf + 3 * (Cf * (1 + Ca)) + 28

section Step

variable {Ea Ef Ra Rf : Type} [DecidableEq Ea] [DecidableEq Ef]

/-- Record-level bounds from the routines' costs, under the per-record hypothesis `hpow`. -/
theorem rec_bounds {α : List Bool → ℕ → List Bool} {F : List Bool → List Bool → List Bool}
    {J Ca Cf : ℕ} {Pa : Prog (KLoc (Fin 3) Ea) (fun _ => Sym) Ra}
    {Pf : Prog (KLoc (Fin 3) Ef) (fun _ => Sym) Rf}
    (hA : AddrSpec α J Ca Pa) (hF : PayloadSpec F Cf Pf) (hRa : Nonempty Ra) (hRf : Nonempty Rf)
    (x : ℕ) (d p : List Bool) (hpow : (bitLen x + d.length + 1) ^ J ≤ p.length + 1) :
    Ca * (bitLen x + d.length + 1) ^ J ≤ Ca * (p.length + 1) ∧
    (α d x).length + 1 ≤ Ca * (p.length + 1) ∧
    Cf * (p.length + (α d x).length + 1) ≤ Cf * (1 + Ca) * (p.length + 1) ∧
    (F (α d x) p).length + 1 ≤ Cf * (1 + Ca) * (p.length + 1) := by
  have e1 : Ca * (bitLen x + d.length + 1) ^ J ≤ Ca * (p.length + 1) :=
    Nat.mul_le_mul_left _ hpow
  have e2 := (addr_len_le hA hRa x d).trans e1
  have e3 : Cf * (p.length + (α d x).length + 1) ≤ Cf * (1 + Ca) * (p.length + 1) := by
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    nlinarith [e2]
  exact ⟨e1, e2, e3, (payload_len_le hF hRf p (α d x)).trans e3⟩

/-- **One record.** The loop body takes the state after `x` records to the state after `x + 1`,
staging the output record `F (α d x) a` on `U`, within `Kp·(|a| + 1)` plus one increment. -/
theorem c3_step {α : List Bool → ℕ → List Bool} {F : List Bool → List Bool → List Bool}
    {J Ca Cf : ℕ} {Pa : Prog (KLoc (Fin 3) Ea) (fun _ => Sym) Ra}
    {Pf : Prog (KLoc (Fin 3) Ef) (fun _ => Sym) Rf}
    (hA : AddrSpec α J Ca Pa) (hF : PayloadSpec F Cf Pf) (hRa : Nonempty Ra) (hRf : Nonempty Rf)
    (S0 : ScanL Ea Ef → List Sym) (rest : List Sym) (d : List Bool) (r2 : List Sym)
    (hD : S0 sDesc = recSyms d ++ r2) (x : ℕ) (a : List Bool) (vs : List (List Bool))
    (acc : List Sym) (hpow : (bitLen x + d.length + 1) ^ J ≤ a.length + 1) :
    Triple []
      (fun s => s.stk = c3St S0 rest x (a :: vs) acc ∧
        s.var.1 = (arrSyms (a :: vs) ++ rest).head?)
      (c3Body Pa Pf)
      (fun s => s.stk = c3St S0 rest (x + 1) vs ((recSyms (F (α d x) a)).reverse ++ acc) ∧
        s.var.1 = (arrSyms vs ++ rest).head?)
      (scanKp Ca Cf * (a.length + 1) + (6 * ones (encodeNat x) + 9)) := by
  obtain ⟨e1, e2, e3, e4⟩ := rec_bounds hA hF hRa hRf x d a hpow
  have r1 : Runs (callInj embA (lA (Rf := Rf)) Pa) (c3St S0 rest x (a :: vs) acc)
      (st5 S0 (arrSyms (a :: vs) ++ rest) (natSyms x ++ Sym.mark :: S0 sX)
        (recSyms (α d x) ++ S0 sA) (S0 sT) (acc ++ Sym.mark :: S0 sU))
      (fun _ => True) (Ca * (bitLen x + d.length + 1) ^ J) :=
    WP.W9comp.runs_congr (runs_callA hA _ x d (Sym.mark :: S0 sX) r2 (TermOK.cons rfl _)
      (by simp [c3St]) (by simp [c3St, hD])) (by simp [c3St])
  have r2' : Runs (callInj embF (lF (Ra := Ra)) Pf)
      (st5 S0 (arrSyms (a :: vs) ++ rest) (natSyms x ++ Sym.mark :: S0 sX)
        (recSyms (α d x) ++ S0 sA) (S0 sT) (acc ++ Sym.mark :: S0 sU))
      (st5 S0 (arrSyms vs ++ rest) (natSyms x ++ Sym.mark :: S0 sX)
        (recSyms (α d x) ++ S0 sA) (recSyms (F (α d x) a) ++ S0 sT) (acc ++ Sym.mark :: S0 sU))
      (fun _ => True) (Cf * (a.length + (α d x).length + 1)) :=
    WP.W9comp.runs_congr (runs_callF hF _ a (α d x) (arrSyms vs ++ rest) (S0 sA)
      (by simp [arrSyms_cons]) (by simp)) (by simp)
  have r3 : Runs (wk (Ra := Ra) (Rf := Rf) (dropBits sA))
      (st5 S0 (arrSyms vs ++ rest) (natSyms x ++ Sym.mark :: S0 sX)
        (recSyms (α d x) ++ S0 sA) (recSyms (F (α d x) a) ++ S0 sT) (acc ++ Sym.mark :: S0 sU))
      (st5 S0 (arrSyms vs ++ rest) (natSyms x ++ Sym.mark :: S0 sX)
        (S0 sA) (recSyms (F (α d x) a) ++ S0 sT) (acc ++ Sym.mark :: S0 sU))
      (fun _ => True) (2 * (α d x).length + 2) :=
    WP.W9comp.runs_congr (runs_wk_dropBits lO sA (α d x) Sym.sep (S0 sA) _ rfl
      (by simp [recSyms])) (by simp)
  have hdat : ∀ y ∈ (F (α d x) a).map Sym.bit, isDataSym y = true := by
    intro y hy
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
    rfl
  have r4 : Runs (wk (Ra := Ra) (Rf := Rf) (moveRec sT sU))
      (st5 S0 (arrSyms vs ++ rest) (natSyms x ++ Sym.mark :: S0 sX)
        (S0 sA) (recSyms (F (α d x) a) ++ S0 sT) (acc ++ Sym.mark :: S0 sU))
      (st5 S0 (arrSyms vs ++ rest) (natSyms x ++ Sym.mark :: S0 sX)
        (S0 sA) (S0 sT) ((recSyms (F (α d x) a)).reverse ++ acc ++ Sym.mark :: S0 sU))
      (fun _ => True) (3 * ((F (α d x) a).map Sym.bit).length + 3) :=
    WP.W9comp.runs_congr (runs_wk_moveRec lO (src := sT) (dst := sU) (by simp)
      ((F (α d x) a).map Sym.bit) (S0 sT) _ hdat (by simp [recSyms])) (by simp [recSyms])
  have r5 : Runs (wk (Ra := Ra) (Rf := Rf) (inc sX sXt))
      (st5 S0 (arrSyms vs ++ rest) (natSyms x ++ Sym.mark :: S0 sX)
        (S0 sA) (S0 sT) ((recSyms (F (α d x) a)).reverse ++ acc ++ Sym.mark :: S0 sU))
      (c3St S0 rest (x + 1) vs ((recSyms (F (α d x) a)).reverse ++ acc))
      (fun _ => True) (6 * ones (encodeNat x) + 9) :=
    WP.W9comp.runs_congr (runs_wk_inc lO (k := sX) (t := sXt) (by simp) x (Sym.mark :: S0 sX) _
      (TermOK.cons rfl _) (by simp)) (by simp [c3St])
  have p6 := triple_peek_fst (τ := Ra × Rf) (sSrc : ScanL Ea Ef)
    (c3St S0 rest (x + 1) vs ((recSyms (F (α d x) a)).reverse ++ acc))
  have hall := runs_seq_triple r1 (runs_seq_triple r2' (runs_seq_triple r3
    (runs_seq_triple r4 (runs_seq_triple r5 p6))))
  refine Triple.conseq hall (fun s hs => hs.1) ?_ ?_
  · rintro s ⟨hs, hv⟩
    exact ⟨hs, by rw [hv]; simp [c3St]⟩
  · simp only [List.length_map, scanKp]
    nlinarith [e1, e2, e3, e4]

end Step

/-! ## Outputs -/

/-- The outputs of the records `vs`, the first one at index `x`. -/
def c3Outs (α : List Bool → ℕ → List Bool) (F : List Bool → List Bool → List Bool)
    (d : List Bool) : ℕ → List (List Bool) → List (List Bool)
  | _, [] => []
  | x, p :: vs => F (α d x) p :: c3Outs α F d (x + 1) vs

theorem c3Outs_eq (α : List Bool → ℕ → List Bool) (F : List Bool → List Bool → List Bool)
    (d : List Bool) : ∀ (vs : List (List Bool)) (x : ℕ),
      c3Outs α F d x vs = vs.mapIdx fun j p => F (α d (x + j)) p
  | [], _ => rfl
  | p :: vs, x => by
    simp only [List.mapIdx_cons, c3Outs, c3Outs_eq α F d vs (x + 1), Nat.add_zero]
    congr 2
    funext j q
    rw [Nat.add_assoc, Nat.add_comm 1 j]

theorem foldG_c3 (α : List Bool → ℕ → List Bool) (F : List Bool → List Bool → List Bool)
    (d : List Bool) : ∀ (vs : List (List Bool)) (x : ℕ) (acc : List Sym),
      foldG (fun x a acc => (recSyms (F (α d x) a)).reverse ++ acc) x vs acc =
        (arrSyms (c3Outs α F d x vs)).reverse ++ acc
  | [], _, _ => by simp [foldG, c3Outs, arrSyms_nil]
  | p :: vs, x, acc => by
    show foldG _ (x + 1) vs _ = _
    rw [foldG_c3 α F d vs (x + 1), c3Outs, arrSyms_cons, List.reverse_append, List.append_assoc]

section Whole

variable {Ea Ef Ra Rf : Type} [DecidableEq Ea] [DecidableEq Ef]

/-- The total output volume is linear in the input volume. -/
theorem vol_c3Outs_le {α : List Bool → ℕ → List Bool} {F : List Bool → List Bool → List Bool}
    {J Ca Cf : ℕ} {Pa : Prog (KLoc (Fin 3) Ea) (fun _ => Sym) Ra}
    {Pf : Prog (KLoc (Fin 3) Ef) (fun _ => Sym) Rf}
    (hA : AddrSpec α J Ca Pa) (hF : PayloadSpec F Cf Pf) (hRa : Nonempty Ra) (hRf : Nonempty Rf)
    (d : List Bool) (M : ℕ) : ∀ (vs : List (List Bool)) (x : ℕ), x + vs.length ≤ M →
      (∀ p ∈ vs, (bitLen M + d.length + 1) ^ J ≤ p.length + 1) →
      vol (c3Outs α F d x vs) ≤ Cf * (1 + Ca) * vol vs
  | [], _, _, _ => by simp [c3Outs, vol_nil]
  | p :: vs, x, hx, hp => by
    have hx' : x + 1 + vs.length ≤ M := by
      simp only [List.length_cons] at hx
      omega
    have hpow : (bitLen x + d.length + 1) ^ J ≤ p.length + 1 :=
      le_trans (Nat.pow_le_pow_left
        (by have := TMFw.W3s.bitLen_mono (show x ≤ M by omega); omega) J)
        (hp p List.mem_cons_self)
    obtain ⟨-, -, -, e4⟩ := rec_bounds hA hF hRa hRf x d p hpow
    have ih := vol_c3Outs_le hA hF hRa hRf d M vs (x + 1) hx'
      (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    rw [c3Outs, vol_cons, vol_cons, Nat.mul_add]
    nlinarith [e4, ih]

/-- **The whole scan.** From the stacks `S` (source `arrSyms v ++ rest`, descriptor
`recSyms d ++ r2`), `c3Prog` consumes the source and pushes the outputs `F (α d x) p_x`, first
record on top, onto the destination; every other stack is restored. Cost `scanC Ca Cf·(V + 1)`. -/
theorem c3_runs {α : List Bool → ℕ → List Bool} {F : List Bool → List Bool → List Bool}
    {J Ca Cf : ℕ} {Pa : Prog (KLoc (Fin 3) Ea) (fun _ => Sym) Ra}
    {Pf : Prog (KLoc (Fin 3) Ef) (fun _ => Sym) Rf}
    (hA : AddrSpec α J Ca Pa) (hF : PayloadSpec F Cf Pf) (hRa : Nonempty Ra) (hRf : Nonempty Rf)
    (d : List Bool) (v : List (List Bool)) (rest r2 : List Sym) (S : ScanL Ea Ef → List Sym)
    (hlen : ∀ x < v.length, (bitLen v.length + d.length + 1) ^ J ≤ (v.getD x []).length + 1)
    (hrest : BlkTerm rest) (hsrc : S (.inl 0) = arrSyms v ++ rest)
    (hdesc : S (.inl 2) = recSyms d ++ r2) :
    Runs (c3Prog Pa Pf) S
      (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (arrSyms (v.mapIdx fun x p => F (α d x) p) ++ S (.inl 1)))
      (fun _ => True) (scanC Ca Cf * (vol v + 1)) := by
  have hall : ∀ p ∈ v, (bitLen v.length + d.length + 1) ^ J ≤ p.length + 1 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have := hlen i hi
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
  -- set-up: the two guards, then peek
  have r1 := runs_wk_pushC (lO (Ra := Ra) (Rf := Rf)) (sX : ScanL Ea Ef) Sym.mark S
  have r2' := runs_wk_pushC (lO (Ra := Ra) (Rf := Rf)) (sU : ScanL Ea Ef) Sym.mark
    (Function.update S sX (Sym.mark :: S sX))
  have hS2 : Function.update (Function.update S sX (Sym.mark :: S sX)) sU
      (Sym.mark :: Function.update S sX (Sym.mark :: S sX) sU) = c3St S rest 0 v [] := by
    apply scanL_funext <;> intros <;> simp [c3St, st5, hsrc, natSyms, encodeNat_zero]
  rw [hS2] at r2'
  have p3 := triple_peek_fst (τ := Ra × Rf) (sSrc : ScanL Ea Ef) (c3St S rest 0 v [])
  -- the record loop
  have hloop := triple_loop_list (c := fun r : ScanR Ra Rf => isRecTop r.1)
    (body := c3Body Pa Pf)
    (fun x vs acc => c3St S rest x vs acc) (fun vs r => r.1 = (arrSyms vs ++ rest).head?)
    (fun x a acc => (recSyms (F (α d x) a)).reverse ++ acc)
    (fun x a => scanKp Ca Cf * (a.length + 1) + (6 * ones (encodeNat x) + 9))
    (fun x vs => x + vs.length = v.length ∧
      ∀ p ∈ vs, (bitLen v.length + d.length + 1) ^ J ≤ p.length + 1)
    (fun x a vs h => by
      have h1 := h.1
      simp only [List.length_cons] at h1
      exact ⟨by omega, fun p hp => h.2 p (List.mem_cons_of_mem _ hp)⟩)
    (fun r hr => by rw [hr]; exact isRecTop_nil hrest)
    (fun a vs r hr => by rw [hr]; exact isRecTop_cons a vs rest)
    (fun x a vs acc h => c3_step hA hF hRa hRf S rest d r2 hdesc x a vs acc (by
      have h1 := h.1
      simp only [List.length_cons] at h1
      exact le_trans (Nat.pow_le_pow_left
        (by have := TMFw.W3s.bitLen_mono (show x ≤ v.length by omega); omega) J)
        (h.2 a List.mem_cons_self)))
    v 0 [] ⟨by simp, hall⟩
  obtain ⟨accF, haccF⟩ : ∃ l, l = (arrSyms (c3Outs α F d 0 v)).reverse := ⟨_, rfl⟩
  have hfold : foldG (fun x a acc => (recSyms (F (α d x) a)).reverse ++ acc) 0 v [] = accF := by
    rw [foldG_c3, List.append_nil, haccF]
  -- the final transfer and the counter drop
  have hmark : Sym.mark ∉ accF := by
    intro h
    rw [haccF, List.mem_reverse] at h
    rcases mem_arrSyms h with h | ⟨b, h⟩ <;> cases h
  have r5 := WP.W9comp.runs_rewind (lO (Ra := Ra) (Rf := Rf)) (src := (sU : ScanL Ea Ef))
    (dst := sDst) (by simp) Sym.mark accF (S sU) (c3St S rest v.length [] accF) hmark
    (by simp [c3St])
  have r6 := runs_wk_dropBits (lO (Ra := Ra) (Rf := Rf)) (sX : ScanL Ea Ef) (encodeNat v.length)
    Sym.mark (S sX) (Function.update (Function.update (c3St S rest v.length [] accF) sU (S sU))
      sDst (accF.reverse ++ c3St S rest v.length [] accF sDst)) rfl (by simp [c3St, natSyms])
  have hout : accF.reverse = arrSyms (v.mapIdx fun x p => F (α d x) p) := by
    rw [haccF, List.reverse_reverse, c3Outs_eq]
    simp
  have hfin : Function.update (Function.update (Function.update (c3St S rest v.length [] accF)
      sU (S sU)) sDst (accF.reverse ++ c3St S rest v.length [] accF sDst)) sX (S sX) =
      Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (arrSyms (v.mapIdx fun x p => F (α d x) p) ++ S (.inl 1)) := by
    rw [hout]
    apply scanL_funext <;> intros <;> simp [c3St, st5, arrSyms_nil]
  have t3 : Triple [] (fun s => s.stk = c3St S rest 0 v [])
      (wk (Ra := Ra) (Rf := Rf) (peekR sSrc))
      (fun s => s.stk = c3St S rest 0 v [] ∧ s.var.1 = (arrSyms v ++ rest).head?) 1 :=
    Triple.post p3 fun s hs => ⟨hs.1, by rw [hs.2]; simp [c3St]⟩
  have t4 : Triple [] (fun s => s.stk = c3St S rest 0 v [] ∧
        s.var.1 = (arrSyms v ++ rest).head?)
      (.loop (fun r : ScanR Ra Rf => isRecTop r.1) (c3Body Pa Pf))
      (fun s => s.stk = c3St S rest v.length [] accF)
      (loopB (fun x a => scanKp Ca Cf * (a.length + 1) + (6 * ones (encodeNat x) + 9)) 0 v) :=
    Triple.post hloop fun s hs => by rw [hs, Nat.zero_add, hfold]
  have hfull := Triple.seq (Triple.post r1 fun _ hs => hs.1)
    (Triple.seq (Triple.post r2' fun _ hs => hs.1) (Triple.seq t3 (Triple.seq t4
      (Triple.seq (Triple.post r5 fun _ hs => hs.1) (WP.W9comp.runs_congr r6 hfin)))))
  refine Triple.cost_mono hfull ?_
  -- cost
  have hL := loopB_inc (scanKp Ca Cf) List.length v 0
  have hinc := incSeqCost_le 6 9 v.length
  have hvol := vol_c3Outs_le hA hF hRa hRf d v.length v 0 (by simp) hall
  have hbl : (encodeNat v.length).length ≤ v.length :=
    (TMFw.W3s.bitLen_le_iff v.length v.length).2 Nat.lt_two_pow_self
  have hMV := length_le_vol v
  have haccL : accF.length = vol (c3Outs α F d 0 v) := by
    rw [haccF, List.length_reverse]
    rfl
  have h0 : incSeqCost 6 9 0 = 0 := rfl
  rw [← vol_eq_sum, h0, Nat.add_zero, Nat.zero_add] at hL
  rw [haccL]
  unfold scanC
  nlinarith [hL, hinc, hvol, hbl, hMV]

end Whole

/-! ## The contract -/

/-- **Lemma A.5 (`lem:transfer-long-record`), long-record address-dependent scan, proved**
(`C3LongRecordScanStmt`, `Contracts/Streams.lean`). For every address map
`α`, payload map `F` and exponent `J`: given an address routine (`C3AddrStmt α J`) and a payload
routine (`C3PayloadStmt F`), the kernel `c3Prog` replaces the array `v` by
`v.mapIdx fun x p => F (α d x) p` (pushed on the destination, first record on top), restores the
descriptor and all scratch stacks, and costs at most `C·(V + 1)` with `C = scanC Ca Cf`
depending only on the routines' constants, provided `(bitLen M + |d| + 1)^J ≤ |p_x| + 1` for every
record (the hypothesis in the statement). -/
theorem c3LongRecordScan_holds (α : List Bool → ℕ → List Bool)
    (F : List Bool → List Bool → List Bool) (J : ℕ) : C3LongRecordScanStmt α F J := by
  intro hAddr hPay
  obtain ⟨Ca, hCa⟩ := hAddr
  obtain ⟨Cf, hCf⟩ := hPay
  obtain ⟨Ea, iEaF, iEaD, Ra, Pa, hRaF, hRaN, hPaC, hPaS⟩ := hCa ()
  obtain ⟨Ef, iEfF, iEfD, Rf, Pf, hRfF, hRfN, hPfC, hPfS⟩ := hCf ()
  refine ⟨scanC Ca Cf, fun _ => ⟨ScanE Ea Ef, inferInstance, inferInstance, ScanR Ra Rf,
    c3Prog Pa Pf, ?_, ?_, closed_c3Prog hPaC hPfC, ?_⟩⟩
  · have := hRaF
    have := hRfF
    infer_instance
  · obtain ⟨ra⟩ := hRaN
    obtain ⟨rf⟩ := hRfN
    exact ⟨(none, ra, rf)⟩
  · intro d v rest r2 S hlen hrest hsrc hdesc
    exact c3_runs hPaS hPfS hRaN hRfN d v rest r2 S hlen hrest hsrc hdesc

end SubNLogN.Machine.K1
