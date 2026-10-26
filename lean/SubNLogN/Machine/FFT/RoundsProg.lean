/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.RoundsBase
import SubNLogN.Machine.FFT.Kit
import SubNLogN.Machine.Calculus.Hdr
import SubNLogN.Machine.Calculus.Loops

/-!
# K4 rounds driver, layout and program (`Machine/FFT/RoundsProg.lean`)

**Scope (honest summary).** Definitions and closedness only (no contract is proved here; no
`sorry`): the stack layout, the registers and the program of the record-axis rounds driver used by
`roundsStmt_of_parts` (`Machine/FFT/RoundsMain.lean`).

* **Layout.** Named stacks `Fin 3` (`0` array, `1` header, `2` table). Private stacks
  `Fin 10 ⊕ (EP ⊕ (EC ⊕ ET))`: own stacks `own 0` (the round index `natSyms v`, which is stack `3`
  of every part), `own 1` (`natSyms b₀`, `b₀ = (ℓ-1) mod K`), `own 2`, `own 3` (temporaries),
  `own 4..9` (scratch of the arithmetic kernels, at most six each); then the scratch blocks of the prefix-round,
  chunk-round and twiddle parts.
* **Program.** `setup; round(ℓ-1); loop; drain(own 1)`:
  - `setup`: copy the first four header fields `[q, D, ℓ, K]` to `own 2`, drop `q, D`, copy `ℓ` to
    `own 0`, drop `ℓ`, decrement `own 0` (now `ℓ - 1`), divide by `K` (quotient to `own 3`,
    remainder `b₀` to `own 1`), drain `own 2`, `own 3`;
  - `round(ℓ-1)`: the prefix part, then the twiddle part (the top slot is a prefix round);
  - `loop`: while `own 0 ≠ 0`: decrement it (`v := v - 1`), compare `v` with `b₀`, run the chunk
    part if `v ≥ b₀` and the prefix part otherwise, then the twiddle part.
-/

namespace SubNLogN.Machine.FFT.RoundsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
  SubNLogN.Machine.FFTKit

/-! ## Layout -/

/-- Private stacks of the driver: ten own stacks, then the parts' scratch blocks. -/
abbrev RE (EP EC ET : Type) : Type := Fin 10 ⊕ (EP ⊕ (EC ⊕ ET))

/-- All stacks of the driver. -/
abbrev RK (EP EC ET : Type) : Type := KLoc (Fin 3) (RE EP EC ET)

section Layout

variable {EP EC ET : Type}

/-- The own private stack `i`. -/
def own (i : Fin 10) : RK EP EC ET := .inr (.inl i)

/-- Scratch injections of the three parts. -/
def injP : EP → EP ⊕ (EC ⊕ ET) := Sum.inl
/-- Scratch injection of the chunk part. -/
def injC : EC → EP ⊕ (EC ⊕ ET) := fun e => .inr (.inl e)
/-- Scratch injection of the twiddle part. -/
def injT : ET → EP ⊕ (EC ⊕ ET) := fun e => .inr (.inr e)

theorem injP_injective : Function.Injective (injP (EP := EP) (EC := EC) (ET := ET)) :=
  fun _ _ h => by simpa [injP] using h
theorem injC_injective : Function.Injective (injC (EP := EP) (EC := EC) (ET := ET)) :=
  fun _ _ h => by simpa [injC] using h
theorem injT_injective : Function.Injective (injT (EP := EP) (EC := EC) (ET := ET)) :=
  fun _ _ h => by simpa [injT] using h

/-- Embedding of a round part (named stacks `Fin 4`: array, header, table, round index). -/
def partEmb {Ei : Type} (j : Ei → EP ⊕ (EC ⊕ ET)) : KLoc (Fin 4) Ei → RK EP EC ET
  | .inl i => if (i : ℕ) = 0 then .inl 0 else if (i : ℕ) = 1 then .inl 1 else
      if (i : ℕ) = 2 then .inl 2 else own 0
  | .inr e => .inr (.inr (j e))

@[simp] theorem partEmb_arr {Ei : Type} (j : Ei → EP ⊕ (EC ⊕ ET)) :
    partEmb j (.inl 0) = .inl 0 := by simp [partEmb]
@[simp] theorem partEmb_hdr {Ei : Type} (j : Ei → EP ⊕ (EC ⊕ ET)) :
    partEmb j (.inl 1) = .inl 1 := by simp [partEmb]
@[simp] theorem partEmb_tab {Ei : Type} (j : Ei → EP ⊕ (EC ⊕ ET)) :
    partEmb j (.inl 2) = .inl 2 := by simp [partEmb]
@[simp] theorem partEmb_idx {Ei : Type} (j : Ei → EP ⊕ (EC ⊕ ET)) :
    partEmb j (.inl 3) = own 0 := by simp [partEmb]
@[simp] theorem partEmb_inr {Ei : Type} (j : Ei → EP ⊕ (EC ⊕ ET)) (e : Ei) :
    partEmb j (.inr e) = .inr (.inr (j e)) := rfl

theorem partEmb_injective {Ei : Type} {j : Ei → EP ⊕ (EC ⊕ ET)} (hj : Function.Injective j) :
    Function.Injective (partEmb j) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [partEmb, own]
  · fin_cases i <;> simp [partEmb, own] at h
  · fin_cases i' <;> simp [partEmb, own] at h
  · simp only [partEmb, Sum.inr.injEq] at h
    rw [hj h]

/-- Embedding of an arithmetic kernel: named stacks by `f`, its `m ≤ 6` scratch stacks onto
`own 4, …, own 9`. -/
def kEmb {n m : ℕ} (hm : m ≤ 6) (f : Fin n → RK EP EC ET) : Loc n m → RK EP EC ET
  | .inl i => f i
  | .inr j => own ⟨4 + j, by omega⟩

theorem kEmb_injective {n m : ℕ} (hm : m ≤ 6) {f : Fin n → RK EP EC ET}
    (hf : Function.Injective f) (hfs : ∀ i (j : Fin 6), f i ≠ own ⟨4 + j, by omega⟩) :
    Function.Injective (kEmb hm f) := by
  rintro (i | j) (i' | j') h
  · exact congrArg Sum.inl (hf h)
  · exact absurd h (hfs i ⟨j', by omega⟩)
  · exact absurd h.symm (hfs i' ⟨j, by omega⟩)
  · simp only [kEmb, own, Sum.inr.injEq, Sum.inl.injEq, Fin.mk.injEq] at h
    exact congrArg Sum.inr (Fin.ext (by omega))

end Layout

/-! ## Registers -/

/-- Registers of the driver: the `Option Sym` register of the header programs and the loop test,
the drain flag, the four arithmetic kernels' registers and the three parts' registers. -/
abbrev RR (Rcp Rdec Rcmp Rdm RP RC RT : Type) : Type :=
  Option Sym × (Bool × (Rcp × (Rdec × (Rcmp × (Rdm × (RP × (RC × RT)))))))

section Lenses

variable {Rcp Rdec Rcmp Rdm RP RC RT : Type}

/-- Lens onto the `Option Sym` register. -/
def lO : Lens (RR Rcp Rdec Rcmp Rdm RP RC RT) (Option Sym) := Lens.fst _ _
/-- Lens onto the drain flag. -/
def lB : Lens (RR Rcp Rdec Rcmp Rdm RP RC RT) Bool := (Lens.snd _ _).comp (Lens.fst _ _)
/-- Lens onto the copy kernel's registers. -/
def lcp : Lens (RR Rcp Rdec Rcmp Rdm RP RC RT) Rcp :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
/-- Lens onto the decrement kernel's registers. -/
def ldec : Lens (RR Rcp Rdec Rcmp Rdm RP RC RT) Rdec :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
/-- Lens onto the comparison kernel's registers. -/
def lcmp : Lens (RR Rcp Rdec Rcmp Rdm RP RC RT) Rcmp :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
/-- Lens onto the division kernel's registers. -/
def ldm : Lens (RR Rcp Rdec Rcmp Rdm RP RC RT) Rdm :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))
/-- Lens onto the prefix part's registers. -/
def lP : Lens (RR Rcp Rdec Rcmp Rdm RP RC RT) RP :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))
/-- Lens onto the chunk part's registers. -/
def lC : Lens (RR Rcp Rdec Rcmp Rdm RP RC RT) RC :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))))))
/-- Lens onto the twiddle part's registers. -/
def lT : Lens (RR Rcp Rdec Rcmp Rdm RP RC RT) RT :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _)))))))

end Lenses

/-! ## The program -/

section Program

variable {EP EC ET Rcp Rdec Rcmp Rdm RP RC RT : Type} {mcp mdec mcmp mdm : ℕ}

/-- Named stacks of the copy kernel: source `own 2`, destination `own 0`. -/
def fCp : Fin 2 → RK EP EC ET := ![own 2, own 0]
/-- Named stack of the decrement kernel: `own 0`. -/
def fDec : Fin 1 → RK EP EC ET := ![own 0]
/-- Named stacks of the comparison kernel: `own 0` (the round index), `own 1` (`b₀`). -/
def fCmp : Fin 2 → RK EP EC ET := ![own 0, own 1]
/-- Named stacks of the division kernel: dividend `own 0`, divisor `own 2`, quotient `own 3`,
remainder `own 1`. -/
def fDm : Fin 4 → RK EP EC ET := ![own 0, own 2, own 3, own 1]

/-- Driver programs. -/
abbrev RProg (EP EC ET Rcp Rdec Rcmp Rdm RP RC RT : Type) : Type :=
  Prog (RK EP EC ET) (fun _ => Sym) (RR Rcp Rdec Rcmp Rdm RP RC RT)

variable (hmcp : mcp ≤ 6) (hmdec : mdec ≤ 6) (hmcmp : mcmp ≤ 6) (hmdm : mdm ≤ 6)
  (Pcp : Prog (Loc 2 mcp) (fun _ => Sym) Rcp) (Pdec : Prog (Loc 1 mdec) (fun _ => Sym) Rdec)
  (Pcmp : Prog (Loc 2 mcmp) (fun _ => Sym) Rcmp) (Pdm : Prog (Loc 4 mdm) (fun _ => Sym) Rdm)
  (obsCmp : Rcmp → Ordering)
  (PP : Prog (KLoc (Fin 4) EP) (fun _ => Sym) RP) (PC : Prog (KLoc (Fin 4) EC) (fun _ => Sym) RC)
  (PT : Prog (KLoc (Fin 4) ET) (fun _ => Sym) RT)

/-- An `Option Sym` header program on the driver's stacks. -/
def hdrK (P : SProg (RK EP EC ET)) : RProg EP EC ET Rcp Rdec Rcmp Rdm RP RC RT := callInj id lO P

/-- Drain an own stack. -/
def drainK (i : Fin 10) : RProg EP EC ET Rcp Rdec Rcmp Rdm RP RC RT :=
  callInj id lB (drainProg (own i))

/-- The setup: `b₀ = (ℓ - 1) mod K` on `own 1`, `ℓ - 1` on `own 0`. -/
def setupProg : RProg EP EC ET Rcp Rdec Rcmp Rdm RP RC RT :=
  .seq (hdrK (copyHdr 4 (.inl 1) (own 2) (own 3)))
  (.seq (hdrK (dropField (own 2)))
  (.seq (hdrK (dropField (own 2)))
  (.seq (callInj (kEmb hmcp fCp) lcp Pcp)
  (.seq (hdrK (dropField (own 2)))
  (.seq (callInj (kEmb hmdec fDec) ldec Pdec)
  (.seq (callInj (kEmb hmdm fDm) ldm Pdm)
  (.seq (drainK 2) (drainK 3))))))))

/-- The prefix-round part. -/
def prefixK : RProg EP EC ET Rcp Rdec Rcmp Rdm RP RC RT := callInj (partEmb injP) lP PP
/-- The chunk-round part. -/
def chunkK : RProg EP EC ET Rcp Rdec Rcmp Rdm RP RC RT := callInj (partEmb injC) lC PC
/-- The twiddle part. -/
def twK : RProg EP EC ET Rcp Rdec Rcmp Rdm RP RC RT := callInj (partEmb injT) lT PT
/-- Decrement the round index. -/
def decK : RProg EP EC ET Rcp Rdec Rcmp Rdm RP RC RT := callInj (kEmb hmdec fDec) ldec Pdec
/-- Compare the round index with `b₀`. -/
def cmpK : RProg EP EC ET Rcp Rdec Rcmp Rdm RP RC RT := callInj (kEmb hmcmp fCmp) lcmp Pcmp
/-- Peek the round index (loop test: is it nonzero?). -/
def peekV : RProg EP EC ET Rcp Rdec Rcmp Rdm RP RC RT := .peek (own 0) (fun s o => lO.set s o)

/-- The chunk test after the comparison: `v ≥ b₀`. -/
def chunkTest (s : RR Rcp Rdec Rcmp Rdm RP RC RT) : Bool := obsCmp (lcmp.get s) != .lt

/-- The loop test after `peekV`: the round index is nonzero. -/
def loopTest (s : RR Rcp Rdec Rcmp Rdm RP RC RT) : Bool := (lO.get s).isSome

/-- One loop iteration: `v := v - 1`, the chunk or prefix part, the twiddle part, peek. -/
def bodyProg : RProg EP EC ET Rcp Rdec Rcmp Rdm RP RC RT :=
  .seq (.seq (.seq (decK hmdec Pdec) (cmpK hmcmp Pcmp))
      (.ite (chunkTest obsCmp) (chunkK PC) (prefixK PP)))
    (.seq (twK PT) peekV)

/-- The whole driver. -/
def mainProg : RProg EP EC ET Rcp Rdec Rcmp Rdm RP RC RT :=
  .seq (setupProg hmcp hmdec hmdm Pcp Pdec Pdm)
    (.seq (.seq (prefixK PP) (twK PT))
      (.seq (.seq peekV (.loop loopTest (bodyProg hmdec hmcmp Pdec Pcmp obsCmp PP PC PT)))
        (drainK 1)))

theorem closed_mainProg (hcp : Pcp.Closed) (hdec : Pdec.Closed) (hcmp : Pcmp.Closed)
    (hdm : Pdm.Closed) (hP : PP.Closed) (hC : PC.Closed) (hT : PT.Closed) :
    (mainProg hmcp hmdec hmcmp hmdm Pcp Pdec Pcmp Pdm obsCmp PP PC PT).Closed := by
  have hh : ∀ P : SProg (RK EP EC ET), P.Closed →
      (hdrK (Rcp := Rcp) (Rdec := Rdec) (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC)
        (RT := RT) P).Closed := fun P h => closed_callInj _ _ h
  have hd : ∀ i : Fin 10, (drainK (EP := EP) (EC := EC) (ET := ET) (Rcp := Rcp) (Rdec := Rdec)
      (Rcmp := Rcmp) (Rdm := Rdm) (RP := RP) (RC := RC) (RT := RT) i).Closed :=
    fun i => closed_callInj _ _ (closed_drainProg _)
  refine ⟨⟨hh _ (closed_copyHdr _ _ _ _), hh _ (closed_dropField _), hh _ (closed_dropField _),
    closed_callInj _ _ hcp, hh _ (closed_dropField _), closed_callInj _ _ hdec,
    closed_callInj _ _ hdm, hd 2, hd 3⟩, ⟨closed_callInj _ _ hP, closed_callInj _ _ hT⟩,
    ⟨trivial, ⟨⟨closed_callInj _ _ hdec, closed_callInj _ _ hcmp⟩, closed_callInj _ _ hC,
      closed_callInj _ _ hP⟩, closed_callInj _ _ hT, trivial⟩, hd 1⟩

end Program

end SubNLogN.Machine.FFT.RoundsAux
