/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6RowPure
import SubNLogN.Machine.AppC.C6RadixSetup

/-!
# Lemma A.8 row padding / unpadding kernels from a counter kernel (`Machine/AppC/C6RowPass.lean`)

`c6RowPad_of : 2 ≤ q → C6RowCtrSpec q → C6RowPadStmt q` and
`c6RowUnpad_of : 2 ≤ q → C6RowCtrSpec q → C6RowUnpadStmt q` (0 `sorry`; the counter kernel is a
hypothesis here, proved in `C6RowCtr.lean`). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

The kernel (layout `KLoc (Fin 5) (PS ⊕ Ec)`, registers `Option Sym × Rc`): push a `mark` on the two
private counter stacks `K1s`, `K2s`; the counter kernel pushes `K1 = R·Z` and `K2 = (R' − R)·Z` above
them; `toUnary` (`C6RadixSetup.lean`) reads `K1`, `K2` (and, for the padding, the width `w`) into
unary masters; the block pass of `C6RadixRow.lean` (`padPass`: `K1` records kept, `K2` zero records
emitted per block; `unpadPass`: `K1` kept, `K2` skipped) runs on the array in place; every master
and counter is dropped. The block passes are the row padding / unpadding by
`c6RowPad_eq_rowPadL`, `c6RowUnpad_eq_rowUnpadL` (`C6RowPure.lean`). Every cost term is linear in
the volume, the counter kernel costs `C·(R·Z)` and `R·Z ≤` the number of records.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Lib

namespace AppC.C6RowAux

open AppC.C6RadixAux AppC.C6Aux Calculus

/-! ## Layout -/

/-- Private stacks of the row kernels. -/
inductive PS where
  | K1s | K2s | mK1 | mK2 | mw | acc | c1 | c2 | cw | tmp | tb
  deriving DecidableEq

instance instFintypePS : Fintype PS :=
  Fintype.ofList [.K1s, .K2s, .mK1, .mK2, .mw, .acc, .c1, .c2, .cw, .tmp, .tb]
    (by intro x; cases x <;> decide)

/-- Scratch of the row kernels: private stacks, then the counter kernel's scratch. -/
abbrev PE (Ec : Type) : Type := PS ⊕ Ec

instance instDecEqPE {Ec : Type} [DecidableEq Ec] : DecidableEq (PE Ec) :=
  inferInstanceAs (DecidableEq (PS ⊕ Ec))

instance (priority := high) instDecEqKP {Ec : Type} [DecidableEq Ec] :
    DecidableEq (KLoc (Fin 5) (PE Ec)) :=
  @instDecidableEqSum (Fin 5) (PE Ec) _ instDecEqPE

instance instFintypePE {Ec : Type} [Fintype Ec] : Fintype (PE Ec) :=
  inferInstanceAs (Fintype (PS ⊕ Ec))

section Layout

variable {Ec : Type}

/-- A numeric code of a stack (named `0..4`, `K1s` `5`, `K2s` `6`, other private `7`, scratch
`100`). -/
def pcode : KLoc (Fin 5) (PE Ec) → ℕ
  | .inl i => i.val
  | .inr (.inl .K1s) => 5
  | .inr (.inl .K2s) => 6
  | .inr (.inl _) => 7
  | .inr (.inr _) => 100

/-- Stack map of the counter kernel: `e, G, B` (named `1, 2, 3`), then `K1s`, `K2s`. -/
def ιc : KLoc (Fin 5) Ec → KLoc (Fin 5) (PE Ec)
  | .inl i => ![.inl 1, .inl 2, .inl 3, .inr (.inl .K1s), .inr (.inl .K2s)] i
  | .inr x => .inr (.inr x)

theorem pcode_ιc (k : Fin 5) : pcode (ιc (Ec := Ec) (.inl k)) = (![1, 2, 3, 5, 6] k : ℕ) := by
  fin_cases k <;> rfl

theorem pcode_ιc_lt (k : Fin 5) : pcode (ιc (Ec := Ec) (.inl k)) < 7 := by
  rw [pcode_ιc]
  fin_cases k <;> decide

theorem ιc_injective : Function.Injective (ιc (Ec := Ec)) := by
  have hv : Function.Injective (fun k : Fin 5 => (![1, 2, 3, 5, 6] k : ℕ)) := by decide
  rintro (a | a) (b | b) h
  · have := congrArg pcode h
    rw [pcode_ιc, pcode_ιc] at this
    exact congrArg Sum.inl (hv this)
  · have h1 : pcode (ιc (Ec := Ec) (.inl a)) = 100 := congrArg pcode h
    have h2 := pcode_ιc_lt (Ec := Ec) a
    omega
  · have h1 : 100 = pcode (ιc (Ec := Ec) (.inl b)) := congrArg pcode h
    have h2 := pcode_ιc_lt (Ec := Ec) b
    omega
  · simp only [ιc, Sum.inr.injEq] at h
    rw [h]

end Layout

/-! ## Programs -/

section Progs

variable {Ec : Type}

/-- Push the floors of the two counter stacks. -/
def preP : SProg (KLoc (Fin 5) (PE Ec)) :=
  .seq (pushC (.inr (.inl .K1s)) .mark) (pushC (.inr (.inl .K2s)) .mark)

/-- After the counters: masters, the padding block pass, drops. -/
def padPost : SProg (KLoc (Fin 5) (PE Ec)) :=
  .seq (toUnary (.inr (.inl .K1s)) (.inr (.inl .mK1)) (.inr (.inl .tb)) (.inr (.inl .tmp)))
  (.seq (toUnary (.inr (.inl .K2s)) (.inr (.inl .mK2)) (.inr (.inl .tb)) (.inr (.inl .tmp)))
  (.seq (toUnary (.inl 4) (.inr (.inl .mw)) (.inr (.inl .tb)) (.inr (.inl .tmp)))
  (.seq (padPass (.inl 0) (.inr (.inl .acc)) (.inr (.inl .mK1)) (.inr (.inl .mK2)) (.inr (.inl .mw))
      (.inr (.inl .c1)) (.inr (.inl .c2)) (.inr (.inl .cw)) (.inr (.inl .tmp)))
  (.seq (dropU (.inr (.inl .mK1))) (.seq (dropU (.inr (.inl .mK2)))
  (.seq (dropU (.inr (.inl .mw))) (.seq (dropU (.inr (.inl .K1s))) (dropU (.inr (.inl .K2s))))))))))

/-- After the counters: masters, the unpadding block pass, drops. -/
def unpadPost : SProg (KLoc (Fin 5) (PE Ec)) :=
  .seq (toUnary (.inr (.inl .K1s)) (.inr (.inl .mK1)) (.inr (.inl .tb)) (.inr (.inl .tmp)))
  (.seq (toUnary (.inr (.inl .K2s)) (.inr (.inl .mK2)) (.inr (.inl .tb)) (.inr (.inl .tmp)))
  (.seq (unpadPass (.inl 0) (.inr (.inl .acc)) (.inr (.inl .mK1)) (.inr (.inl .mK2))
      (.inr (.inl .c1)) (.inr (.inl .c2)) (.inr (.inl .tmp)))
  (.seq (dropU (.inr (.inl .mK1))) (.seq (dropU (.inr (.inl .mK2)))
  (.seq (dropU (.inr (.inl .K1s))) (dropU (.inr (.inl .K2s))))))))

variable {Rc : Type}

/-- **The padding kernel.** -/
def padProg (Pc : Prog (KLoc (Fin 5) Ec) (fun _ => Sym) Rc) :
    Prog (KLoc (Fin 5) (PE Ec)) (fun _ => Sym) (Option Sym × Rc) :=
  .seq ((preP (Ec := Ec)).liftRegs (Lens.fst _ _)) (.seq (callInj ιc (Lens.snd _ _) Pc)
    ((padPost (Ec := Ec)).liftRegs (Lens.fst _ _)))

/-- **The unpadding kernel.** -/
def unpadProg (Pc : Prog (KLoc (Fin 5) Ec) (fun _ => Sym) Rc) :
    Prog (KLoc (Fin 5) (PE Ec)) (fun _ => Sym) (Option Sym × Rc) :=
  .seq ((preP (Ec := Ec)).liftRegs (Lens.fst _ _)) (.seq (callInj ιc (Lens.snd _ _) Pc)
    ((unpadPost (Ec := Ec)).liftRegs (Lens.fst _ _)))

end Progs

/-! ## Closedness -/

theorem fb_pushN {K : Type} (k : K) (x : Sym) :
    ∀ (j d : ℕ), (pushN k x j).FreeBelow d
  | 0, d => by simp [pushN, Prog.FreeBelow, skip]
  | j + 1, d => ⟨by simp [Prog.FreeBelow, pushC], fb_pushN k x j d⟩

section Closed

variable {Ec : Type}

theorem closed_preP : (preP (Ec := Ec)).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, preP, pushC]

theorem closed_padPost : (padPost (Ec := Ec)).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, padPost, toUnary, hornerLoop, hornerBody, mulU, addTop,
    moveBlock, moveBits, moveBitsBody, restoreR, padPass, padLoop, padBody, withCtr, copyBlock,
    moveBitsDup, dupBody, cloop, copyRec, emitZero, moveRecs, dropU, clearBits, pushC, popR, peekR,
    pushR, skip, fb_pushN]

theorem closed_unpadPost : (unpadPost (Ec := Ec)).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, unpadPost, toUnary, hornerLoop, hornerBody, mulU, addTop,
    moveBlock, moveBits, moveBitsBody, restoreR, unpadPass, unpadLoop, unpadBody, withCtr,
    copyBlock, moveBitsDup, dupBody, cloop, copyRec, skipRec, moveRecs, dropU, clearBits, pushC,
    popR, peekR, pushR, skip, fb_pushN]

variable {Rc : Type}

theorem closed_padProg {Pc : Prog (KLoc (Fin 5) Ec) (fun _ => Sym) Rc} (hcl : Pc.Closed) :
    (padProg Pc).Closed :=
  ⟨WP.W9comp.closed_liftRegs _ closed_preP, closed_callInj _ _ hcl,
    WP.W9comp.closed_liftRegs _ closed_padPost⟩

theorem closed_unpadProg {Pc : Prog (KLoc (Fin 5) Ec) (fun _ => Sym) Rc} (hcl : Pc.Closed) :
    (unpadProg Pc).Closed :=
  ⟨WP.W9comp.closed_liftRegs _ closed_preP, closed_callInj _ _ hcl,
    WP.W9comp.closed_liftRegs _ closed_unpadPost⟩

end Closed

/-! ## Runs of the pieces -/

/-- Drop a binary counter and its `mark` floor (`dropU` is `clearBits; popR`). -/
theorem runsIn_dropNat {K : Type} [DecidableEq K] (k : K) (n : ℕ) (X : List Sym)
    (S : K → List Sym) (hS : S k = natSyms n ++ Sym.mark :: X) :
    RunsIn [] (dropU k) S (Function.update S k X) (fun _ => True)
      (4 * bitLen n + 2 + 1) := by
  have h1 := runsIn_clearBits (ρ := []) k (Computability.encodeNat n)
    (C6RadixAux.termOK_mark X) S hS
  have h2 := runsIn_popR [] k (Function.update S k (Sym.mark :: X)) Sym.mark X
    (Function.update_self _ _ _)
  rw [Function.update_idem] at h2
  exact RunsIn.mono (RunsIn.seq h1 h2) (fun _ _ => trivial) le_rfl

/-- A kernel on an injective sub-layout that pushes on two of its stacks. -/
theorem rowCall_upd2 {L K σ R : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog L (fun _ => Sym) R}
    {B : K → List Sym} (x0 x1 : L) (w0 w1 : List Sym) {Q : R → Prop} {T : ℕ}
    (h : Runs P (B ∘ ι) (Function.update (Function.update (B ∘ ι) x0 w0) x1 w1) Q T) :
    Runs (callInj ι l P) B (Function.update (Function.update B (ι x0) w0) (ι x1) w1)
      (fun _ => True) T := by
  refine runs_callInj hι l (Q := Q) ?_ (fun k hk => ?_)
  · rw [Function.update_comp_eq_of_injective _ hι x1 w1,
      Function.update_comp_eq_of_injective B hι x0 w0]
    exact h
  · rw [Function.update_of_ne (fun h => hk x1 h.symm), Function.update_of_ne (fun h => hk x0 h.symm)]

theorem bitLen_le_self_row (n : ℕ) : bitLen n ≤ n := by
  rw [bitLen, IntMulTM.length_encodeNat]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

section Runs

variable {Ec : Type} [DecidableEq Ec]

theorem runs_preP (S : KLoc (Fin 5) (PE Ec) → List Sym) :
    RunsIn [] (preP (Ec := Ec)) S
      (Function.update (Function.update S (.inr (.inl .K1s)) (Sym.mark :: S (.inr (.inl .K1s))))
        (.inr (.inl .K2s)) (Sym.mark :: S (.inr (.inl .K2s)))) (fun _ => True) 2 := by
  have h1 := runsIn_pushC [] (.inr (.inl .K1s) : KLoc (Fin 5) (PE Ec)) Sym.mark S
  have h2 := runsIn_pushC [] (.inr (.inl .K2s) : KLoc (Fin 5) (PE Ec)) Sym.mark
    (Function.update S (.inr (.inl .K1s)) (Sym.mark :: S (.inr (.inl .K1s))))
  have e : Function.update S (.inr (.inl .K1s)) (Sym.mark :: S (.inr (.inl .K1s)))
      (.inr (.inl .K2s) : KLoc (Fin 5) (PE Ec)) = S (.inr (.inl .K2s)) := by simp
  rw [e] at h2
  exact RunsIn.seq h1 h2

theorem runs_padPost {A K1 K2 w : ℕ} {v : List (List Bool)} (hK1 : 0 < K1)
    (hv : v.length = A * K1) (hw : ∀ p ∈ v, p.length = w) {rest r4 X1 X2 : List Sym}
    (hrest : BlkTerm rest) (hr4 : TermOK r4) (S : KLoc (Fin 5) (PE Ec) → List Sym)
    (h0 : S (.inl 0) = arrSyms v ++ rest) (h4 : S (.inl 4) = natSyms w ++ r4)
    (hk1 : S (.inr (.inl .K1s)) = natSyms K1 ++ Sym.mark :: X1)
    (hk2 : S (.inr (.inl .K2s)) = natSyms K2 ++ Sym.mark :: X2) :
    RunsIn [] (padPost (Ec := Ec)) S
      (Function.update (Function.update (Function.update S (.inl 0)
        (arrSyms (rowPadL K1 K2 w A v) ++ rest)) (.inr (.inl .K1s)) X1) (.inr (.inl .K2s)) X2)
      (fun _ => True)
      ((27 * K1 + 9) + ((27 * K2 + 9) + ((27 * w + 9) +
        ((A * (K1 * (3 * w + 13) + K2 * (11 * w + 22) + 24) + 4 * vol (rowPadL K1 K2 w A v) + 6) +
        ((4 * K1 + 3) + ((4 * K2 + 3) + ((4 * w + 3) +
        ((4 * bitLen K1 + 2 + 1) + (4 * bitLen K2 + 2 + 1))))))))) := by
  have e1 := runsIn_toUnary (ρ := []) (src := (.inr (.inl .K1s) : KLoc (Fin 5) (PE Ec)))
    (dst := .inr (.inl .mK1)) (tb := .inr (.inl .tb)) (tmp := .inr (.inl .tmp))
    (by simp) (by simp) (by simp) (by simp) K1 (C6RadixAux.termOK_mark X1) S hk1
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update S (.inr (.inl .mK1))
      (ublk K1 ++ Sym.mark :: S (.inr (.inl .mK1))) := ⟨_, rfl⟩
  rw [← hS1] at e1
  have e2 := runsIn_toUnary (ρ := []) (src := (.inr (.inl .K2s) : KLoc (Fin 5) (PE Ec)))
    (dst := .inr (.inl .mK2)) (tb := .inr (.inl .tb)) (tmp := .inr (.inl .tmp))
    (by simp) (by simp) (by simp) (by simp) K2 (C6RadixAux.termOK_mark X2) S1
    (by rw [hS1]; simp [hk2])
  have l2 : S1 (.inr (.inl .mK2)) = S (.inr (.inl .mK2)) := by rw [hS1]; simp
  rw [l2] at e2
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S1 (.inr (.inl .mK2))
      (ublk K2 ++ Sym.mark :: S (.inr (.inl .mK2))) := ⟨_, rfl⟩
  rw [← hS2] at e2
  have e3 := runsIn_toUnary (ρ := []) (src := (.inl 4 : KLoc (Fin 5) (PE Ec)))
    (dst := .inr (.inl .mw)) (tb := .inr (.inl .tb)) (tmp := .inr (.inl .tmp))
    (by simp) (by simp) (by simp) (by simp) w hr4 S2
    (by rw [hS2, hS1]; simp [h4])
  have l3 : S2 (.inr (.inl .mw)) = S (.inr (.inl .mw)) := by rw [hS2, hS1]; simp
  rw [l3] at e3
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update S2 (.inr (.inl .mw))
      (ublk w ++ Sym.mark :: S (.inr (.inl .mw))) := ⟨_, rfl⟩
  rw [← hS3] at e3
  have e4 := runsIn_padPass (ρ := []) (src := (.inl 0 : KLoc (Fin 5) (PE Ec)))
    (acc := .inr (.inl .acc)) (mK1 := .inr (.inl .mK1)) (mK2 := .inr (.inl .mK2))
    (mw := .inr (.inl .mw)) (c1 := .inr (.inl .c1)) (c2 := .inr (.inl .c2))
    (cw := .inr (.inl .cw)) (tmp := .inr (.inl .tmp)) (by simp) K1 K2 w A hK1 v hv hw hrest
    (C6RadixAux.termOK_mark (S (.inr (.inl .mK1)))) (C6RadixAux.termOK_mark (S (.inr (.inl .mK2))))
    (C6RadixAux.termOK_mark (S (.inr (.inl .mw)))) S3
    (by rw [hS3, hS2, hS1]; simp [h0]) (by rw [hS3, hS2, hS1]; simp)
    (by rw [hS3, hS2, hS1]; simp) (by rw [hS3, hS2, hS1]; simp)
  obtain ⟨S4, hS4⟩ : ∃ S4, S4 = Function.update S3 (.inl 0)
      (arrSyms (rowPadL K1 K2 w A v) ++ rest) := ⟨_, rfl⟩
  rw [← hS4] at e4
  have e5 := runsIn_dropU (ρ := []) (.inr (.inl .mK1) : KLoc (Fin 5) (PE Ec)) K1
    (S (.inr (.inl .mK1))) S4 (by rw [hS4, hS3, hS2, hS1]; simp)
  obtain ⟨S5, hS5⟩ : ∃ S5, S5 = Function.update S4 (.inr (.inl .mK1))
      (S (.inr (.inl .mK1))) := ⟨_, rfl⟩
  rw [← hS5] at e5
  have e6 := runsIn_dropU (ρ := []) (.inr (.inl .mK2) : KLoc (Fin 5) (PE Ec)) K2
    (S (.inr (.inl .mK2))) S5 (by rw [hS5, hS4, hS3, hS2, hS1]; simp)
  obtain ⟨S6, hS6⟩ : ∃ S6, S6 = Function.update S5 (.inr (.inl .mK2))
      (S (.inr (.inl .mK2))) := ⟨_, rfl⟩
  rw [← hS6] at e6
  have e7 := runsIn_dropU (ρ := []) (.inr (.inl .mw) : KLoc (Fin 5) (PE Ec)) w
    (S (.inr (.inl .mw))) S6 (by rw [hS6, hS5, hS4, hS3, hS2, hS1]; simp)
  obtain ⟨S7, hS7⟩ : ∃ S7, S7 = Function.update S6 (.inr (.inl .mw))
      (S (.inr (.inl .mw))) := ⟨_, rfl⟩
  rw [← hS7] at e7
  have e8 := runsIn_dropNat (.inr (.inl .K1s) : KLoc (Fin 5) (PE Ec)) K1 X1 S7
    (by rw [hS7, hS6, hS5, hS4, hS3, hS2, hS1]; simp [hk1])
  obtain ⟨S8, hS8⟩ : ∃ S8, S8 = Function.update S7 (.inr (.inl .K1s)) X1 := ⟨_, rfl⟩
  rw [← hS8] at e8
  have e9 := runsIn_dropNat (.inr (.inl .K2s) : KLoc (Fin 5) (PE Ec)) K2 X2 S8
    (by rw [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]; simp [hk2])
  refine RunsIn.congr (RunsIn.seq e1 (RunsIn.seq e2 (RunsIn.seq e3 (RunsIn.seq e4
    (RunsIn.seq e5 (RunsIn.seq e6 (RunsIn.seq e7 (RunsIn.seq e8 e9)))))))) ?_ le_rfl
  rw [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]
  funext k
  rcases k with i | x | x
  · fin_cases i <;> simp
  · cases x <;> simp
  · simp

theorem runs_unpadPost {A K1 K2 w : ℕ} {v : List (List Bool)} (hK : 0 < K1 + K2)
    (hv : v.length = A * (K1 + K2)) (hw : ∀ p ∈ v, p.length = w) {rest X1 X2 : List Sym}
    (hrest : BlkTerm rest) (S : KLoc (Fin 5) (PE Ec) → List Sym)
    (h0 : S (.inl 0) = arrSyms v ++ rest)
    (hk1 : S (.inr (.inl .K1s)) = natSyms K1 ++ Sym.mark :: X1)
    (hk2 : S (.inr (.inl .K2s)) = natSyms K2 ++ Sym.mark :: X2) :
    RunsIn [] (unpadPost (Ec := Ec)) S
      (Function.update (Function.update (Function.update S (.inl 0)
        (arrSyms (rowUnpadL K1 K2 A v) ++ rest)) (.inr (.inl .K1s)) X1) (.inr (.inl .K2s)) X2)
      (fun _ => True)
      ((27 * K1 + 9) + ((27 * K2 + 9) +
        ((A * (K1 * (3 * w + 13) + K2 * (4 * w + 13) + 24) + 4 * vol (rowUnpadL K1 K2 A v) + 6) +
        ((4 * K1 + 3) + ((4 * K2 + 3) +
        ((4 * bitLen K1 + 2 + 1) + (4 * bitLen K2 + 2 + 1))))))) := by
  have e1 := runsIn_toUnary (ρ := []) (src := (.inr (.inl .K1s) : KLoc (Fin 5) (PE Ec)))
    (dst := .inr (.inl .mK1)) (tb := .inr (.inl .tb)) (tmp := .inr (.inl .tmp))
    (by simp) (by simp) (by simp) (by simp) K1 (C6RadixAux.termOK_mark X1) S hk1
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update S (.inr (.inl .mK1))
      (ublk K1 ++ Sym.mark :: S (.inr (.inl .mK1))) := ⟨_, rfl⟩
  rw [← hS1] at e1
  have e2 := runsIn_toUnary (ρ := []) (src := (.inr (.inl .K2s) : KLoc (Fin 5) (PE Ec)))
    (dst := .inr (.inl .mK2)) (tb := .inr (.inl .tb)) (tmp := .inr (.inl .tmp))
    (by simp) (by simp) (by simp) (by simp) K2 (C6RadixAux.termOK_mark X2) S1
    (by rw [hS1]; simp [hk2])
  have l2 : S1 (.inr (.inl .mK2)) = S (.inr (.inl .mK2)) := by rw [hS1]; simp
  rw [l2] at e2
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update S1 (.inr (.inl .mK2))
      (ublk K2 ++ Sym.mark :: S (.inr (.inl .mK2))) := ⟨_, rfl⟩
  rw [← hS2] at e2
  have e3 := runsIn_unpadPass (ρ := []) (src := (.inl 0 : KLoc (Fin 5) (PE Ec)))
    (acc := .inr (.inl .acc)) (mK1 := .inr (.inl .mK1)) (mK2 := .inr (.inl .mK2))
    (c1 := .inr (.inl .c1)) (c2 := .inr (.inl .c2)) (tmp := .inr (.inl .tmp)) (by simp)
    K1 K2 w A hK v hv hw hrest
    (C6RadixAux.termOK_mark (S (.inr (.inl .mK1)))) (C6RadixAux.termOK_mark (S (.inr (.inl .mK2)))) S2
    (by rw [hS2, hS1]; simp [h0]) (by rw [hS2, hS1]; simp) (by rw [hS2, hS1]; simp)
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update S2 (.inl 0)
      (arrSyms (rowUnpadL K1 K2 A v) ++ rest) := ⟨_, rfl⟩
  rw [← hS3] at e3
  have e4 := runsIn_dropU (ρ := []) (.inr (.inl .mK1) : KLoc (Fin 5) (PE Ec)) K1
    (S (.inr (.inl .mK1))) S3 (by rw [hS3, hS2, hS1]; simp)
  obtain ⟨S4, hS4⟩ : ∃ S4, S4 = Function.update S3 (.inr (.inl .mK1))
      (S (.inr (.inl .mK1))) := ⟨_, rfl⟩
  rw [← hS4] at e4
  have e5 := runsIn_dropU (ρ := []) (.inr (.inl .mK2) : KLoc (Fin 5) (PE Ec)) K2
    (S (.inr (.inl .mK2))) S4 (by rw [hS4, hS3, hS2, hS1]; simp)
  obtain ⟨S5, hS5⟩ : ∃ S5, S5 = Function.update S4 (.inr (.inl .mK2))
      (S (.inr (.inl .mK2))) := ⟨_, rfl⟩
  rw [← hS5] at e5
  have e6 := runsIn_dropNat (.inr (.inl .K1s) : KLoc (Fin 5) (PE Ec)) K1 X1 S5
    (by rw [hS5, hS4, hS3, hS2, hS1]; simp [hk1])
  obtain ⟨S6, hS6⟩ : ∃ S6, S6 = Function.update S5 (.inr (.inl .K1s)) X1 := ⟨_, rfl⟩
  rw [← hS6] at e6
  have e7 := runsIn_dropNat (.inr (.inl .K2s) : KLoc (Fin 5) (PE Ec)) K2 X2 S6
    (by rw [hS6, hS5, hS4, hS3, hS2, hS1]; simp [hk2])
  refine RunsIn.congr (RunsIn.seq e1 (RunsIn.seq e2 (RunsIn.seq e3 (RunsIn.seq e4
    (RunsIn.seq e5 (RunsIn.seq e6 e7)))))) ?_ le_rfl
  rw [hS6, hS5, hS4, hS3, hS2, hS1]
  funext k
  rcases k with i | x | x
  · fin_cases i <;> simp
  · cases x <;> simp
  · simp

end Runs

/-! ## Cost bounds -/

theorem pad_cost_le {A K1 K2 w V Cc b1 b2 : ℕ} (hA : 1 ≤ A) (hK1 : 1 ≤ K1)
    (hb1 : b1 ≤ K1) (hb2 : b2 ≤ K2) (hV : V = A * (K1 + K2) * (w + 1)) :
    2 + (Cc * K1 + ((27 * K1 + 9) + ((27 * K2 + 9) + ((27 * w + 9) +
        ((A * (K1 * (3 * w + 13) + K2 * (11 * w + 22) + 24) + 4 * V + 6) +
        ((4 * K1 + 3) + ((4 * K2 + 3) + ((4 * w + 3) +
        ((4 * b1 + 2 + 1) + (4 * b2 + 2 + 1)))))))))) ≤ (Cc + 200) * (V + 1) := by
  have hAK1 : K1 ≤ A * K1 := Nat.le_mul_of_pos_left K1 hA
  have hAK2 : K2 ≤ A * K2 := Nat.le_mul_of_pos_left K2 hA
  have hAA : A ≤ A * K1 := Nat.le_mul_of_pos_right A hK1
  have hw1 : w ≤ A * K1 * w := Nat.le_mul_of_pos_left w (Nat.mul_pos hA hK1)
  have eV : V = A * K1 * w + A * K2 * w + A * K1 + A * K2 := by rw [hV]; ring
  have hKV : K1 ≤ V := by rw [eV]; omega
  have hC : Cc * K1 ≤ Cc * V := Nat.mul_le_mul_left Cc hKV
  have e1 : A * (K1 * (3 * w + 13) + K2 * (11 * w + 22) + 24) =
      3 * (A * K1 * w) + 13 * (A * K1) + 11 * (A * K2 * w) + 22 * (A * K2) + 24 * A := by ring
  have e2 : (Cc + 200) * (V + 1) = Cc * V + Cc + 200 * V + 200 := by ring
  rw [e1, e2]
  omega

theorem unpad_cost_le {A K1 K2 w V VU Cc b1 b2 : ℕ} (hA : 1 ≤ A) (hK1 : 1 ≤ K1)
    (hb1 : b1 ≤ K1) (hb2 : b2 ≤ K2) (hV : V = A * (K1 + K2) * (w + 1)) (hVU : VU ≤ V) :
    2 + (Cc * K1 + ((27 * K1 + 9) + ((27 * K2 + 9) +
        ((A * (K1 * (3 * w + 13) + K2 * (4 * w + 13) + 24) + 4 * VU + 6) +
        ((4 * K1 + 3) + ((4 * K2 + 3) +
        ((4 * b1 + 2 + 1) + (4 * b2 + 2 + 1)))))))) ≤ (Cc + 200) * (V + 1) := by
  have hAK1 : K1 ≤ A * K1 := Nat.le_mul_of_pos_left K1 hA
  have hAK2 : K2 ≤ A * K2 := Nat.le_mul_of_pos_left K2 hA
  have hAA : A ≤ A * K1 := Nat.le_mul_of_pos_right A hK1
  have eV : V = A * K1 * w + A * K2 * w + A * K1 + A * K2 := by rw [hV]; ring
  have hKV : K1 ≤ V := by rw [eV]; omega
  have hC : Cc * K1 ≤ Cc * V := Nat.mul_le_mul_left Cc hKV
  have e1 : A * (K1 * (3 * w + 13) + K2 * (4 * w + 13) + 24) =
      3 * (A * K1 * w) + 13 * (A * K1) + 4 * (A * K2 * w) + 13 * (A * K2) + 24 * A := by ring
  have e2 : (Cc + 200) * (V + 1) = Cc * V + Cc + 200 * V + 200 := by ring
  rw [e1, e2]
  omega

theorem mem_of_mem_rowUnpadL {K1 K2 M : ℕ} {v : List (List Bool)} {p : List Bool}
    (h : p ∈ rowUnpadL K1 K2 M v) : p ∈ v := by
  unfold rowUnpadL at h
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp h
  exact List.mem_of_mem_drop (List.mem_of_mem_take hi)

/-! ## The contracts from the counter kernel -/

/-- **Row padding** (`C6RowPadStmt q`, for `2 ≤ q`) from the counter kernel. -/
theorem c6RowPad_of {q : ℕ} (hq : 2 ≤ q) (hC : C6RowCtrSpec q) : C6RowPadStmt q := by
  obtain ⟨Cc, hCc⟩ := hC
  obtain ⟨Ec, iEf, iEd, Rc, Pc, hRf, hRn, hcl, hs⟩ := hCc ()
  refine ⟨Cc + 200, fun _ => ⟨PE Ec, instFintypePE, instDecEqPE, Option Sym × Rc, padProg Pc,
    (by have := hRf; infer_instance), (by have := hRn; infer_instance), closed_padProg hcl, ?_⟩⟩
  intro A e G B w v rest r1 r2 r3 r4 S he hA hG hB hlen hw hrest hr1 hr2 hr3 hr4 hS0 hS1 hS2 hS3
    hS4
  have hZe : q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B = c6Zq q e G B := rfl
  rw [hZe] at hlen ⊢
  have hR0 : 0 < c6R q e := c6R_pos hq
  have hZ1 : 1 ≤ c6Zq q e G B := one_le_c6Zq hq hG hB
  have hRR : c6R q e ≤ c6Rp q e := c6R_le_c6Rp q e
  have hpos : 0 < c6R q e * c6Zq q e G B := Nat.mul_pos hR0 hZ1
  -- 1. the counter floors
  have X1 := WP.W0m.runs_liftRegs (Lens.fst (Option Sym) Rc)
    (RunsIn.iff_runs.mp (runs_preP (Ec := Ec) S))
  obtain ⟨S1, hS1d⟩ : ∃ S1, S1 = Function.update (Function.update S (.inr (.inl .K1s))
      (Sym.mark :: S (.inr (.inl .K1s)))) (.inr (.inl .K2s)) (Sym.mark :: S (.inr (.inl .K2s))) :=
    ⟨_, rfl⟩
  rw [← hS1d] at X1
  -- 2. the counters `K1 = R·Z`, `K2 = (R' − R)·Z`
  have c := hs e G B r1 r2 r3 (S1 ∘ ιc) he hG hB hr1 hr2 hr3
    (by show S1 (.inl 1) = _; rw [hS1d]; simp [hS1])
    (by show S1 (.inl 2) = _; rw [hS1d]; simp [hS2])
    (by show S1 (.inl 3) = _; rw [hS1d]; simp [hS3])
  have X2 := rowCall_upd2 ιc_injective (Lens.snd (Option Sym) Rc) (.inl 3) (.inl 4) _ _ c
  have a1 : S1 (.inr (.inl .K1s)) = Sym.mark :: S (.inr (.inl .K1s)) := by rw [hS1d]; simp
  have a2 : S1 (.inr (.inl .K2s)) = Sym.mark :: S (.inr (.inl .K2s)) := by rw [hS1d]; simp
  obtain ⟨S2, hS2d⟩ : ∃ S2, S2 = Function.update (Function.update S1 (.inr (.inl .K1s))
      (natSyms (c6R q e * c6Zq q e G B) ++ Sym.mark :: S (.inr (.inl .K1s)))) (.inr (.inl .K2s))
      (natSyms ((c6Rp q e - c6R q e) * c6Zq q e G B) ++ Sym.mark :: S (.inr (.inl .K2s))) :=
    ⟨_, rfl⟩
  have X2' : Runs (callInj ιc (Lens.snd (Option Sym) Rc) Pc) S1 S2 (fun _ => True)
      (Cc * (c6R q e * c6Zq q e G B)) := by
    refine WP.W9comp.runs_congr X2 ?_
    show Function.update (Function.update S1 (.inr (.inl .K1s))
      (natSyms (c6R q e * c6Zq q e G B) ++ S1 (.inr (.inl .K1s)))) (.inr (.inl .K2s))
      (natSyms ((c6Rp q e - c6R q e) * c6Zq q e G B) ++ S1 (.inr (.inl .K2s))) = S2
    rw [a1, a2, hS2d]
  -- 3. masters, the block pass, drops
  have hv : v.length = A * (c6R q e * c6Zq q e G B) := by rw [hlen, mul_assoc]
  have P3 := runs_padPost (Ec := Ec) (A := A) (K1 := c6R q e * c6Zq q e G B)
    (K2 := (c6Rp q e - c6R q e) * c6Zq q e G B) (w := w) (X1 := S (.inr (.inl .K1s)))
    (X2 := S (.inr (.inl .K2s))) hpos hv hw hrest hr4 S2
    (by rw [hS2d, hS1d]; simp [hS0]) (by rw [hS2d, hS1d]; simp [hS4])
    (by rw [hS2d]; simp) (by rw [hS2d]; simp)
  have X3 := WP.W0m.runs_liftRegs (Lens.fst (Option Sym) Rc) (RunsIn.iff_runs.mp P3)
  have hall := WP.W9comp.runs_seq X1 (WP.W9comp.runs_seq X2' X3)
  rw [← c6RowPad_eq_rowPadL hR0 hZ1 hRR hlen] at hall
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · rw [hS2d, hS1d]
    funext k
    rcases k with i | x | x
    · fin_cases i <;> simp
    · cases x <;> simp
    · simp
  · have hV : vol (c6RowPad (c6R q e) (c6Rp q e) (c6Zq q e G B) w v) =
        A * (c6R q e * c6Zq q e G B + (c6Rp q e - c6R q e) * c6Zq q e G B) * (w + 1) := by
      rw [vol_eq_of_width (width_c6RowPad hR0 hZ1 hlen hw), length_c6RowPad hpos hlen,
        ← Nat.add_mul, Nat.add_sub_cancel' hRR]
      ring
    exact pad_cost_le hA hpos (bitLen_le_self_row _) (bitLen_le_self_row _) hV

/-- **Row unpadding** (`C6RowUnpadStmt q`, for `2 ≤ q`) from the counter kernel. -/
theorem c6RowUnpad_of {q : ℕ} (hq : 2 ≤ q) (hC : C6RowCtrSpec q) : C6RowUnpadStmt q := by
  obtain ⟨Cc, hCc⟩ := hC
  obtain ⟨Ec, iEf, iEd, Rc, Pc, hRf, hRn, hcl, hs⟩ := hCc ()
  refine ⟨Cc + 200, fun _ => ⟨PE Ec, instFintypePE, instDecEqPE, Option Sym × Rc, unpadProg Pc,
    (by have := hRf; infer_instance), (by have := hRn; infer_instance), closed_unpadProg hcl,
    ?_⟩⟩
  intro A e G B w v rest r1 r2 r3 r4 S he hA hG hB hlen hw hrest hr1 hr2 hr3 hr4 hS0 hS1 hS2 hS3
    hS4
  have hZe : q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B = c6Zq q e G B := rfl
  rw [hZe] at hlen ⊢
  have hR0 : 0 < c6R q e := c6R_pos hq
  have hZ1 : 1 ≤ c6Zq q e G B := one_le_c6Zq hq hG hB
  have hRR : c6R q e ≤ c6Rp q e := c6R_le_c6Rp q e
  have hpos : 0 < c6R q e * c6Zq q e G B := Nat.mul_pos hR0 hZ1
  have X1 := WP.W0m.runs_liftRegs (Lens.fst (Option Sym) Rc)
    (RunsIn.iff_runs.mp (runs_preP (Ec := Ec) S))
  obtain ⟨S1, hS1d⟩ : ∃ S1, S1 = Function.update (Function.update S (.inr (.inl .K1s))
      (Sym.mark :: S (.inr (.inl .K1s)))) (.inr (.inl .K2s)) (Sym.mark :: S (.inr (.inl .K2s))) :=
    ⟨_, rfl⟩
  rw [← hS1d] at X1
  have c := hs e G B r1 r2 r3 (S1 ∘ ιc) he hG hB hr1 hr2 hr3
    (by show S1 (.inl 1) = _; rw [hS1d]; simp [hS1])
    (by show S1 (.inl 2) = _; rw [hS1d]; simp [hS2])
    (by show S1 (.inl 3) = _; rw [hS1d]; simp [hS3])
  have X2 := rowCall_upd2 ιc_injective (Lens.snd (Option Sym) Rc) (.inl 3) (.inl 4) _ _ c
  have a1 : S1 (.inr (.inl .K1s)) = Sym.mark :: S (.inr (.inl .K1s)) := by rw [hS1d]; simp
  have a2 : S1 (.inr (.inl .K2s)) = Sym.mark :: S (.inr (.inl .K2s)) := by rw [hS1d]; simp
  obtain ⟨S2, hS2d⟩ : ∃ S2, S2 = Function.update (Function.update S1 (.inr (.inl .K1s))
      (natSyms (c6R q e * c6Zq q e G B) ++ Sym.mark :: S (.inr (.inl .K1s)))) (.inr (.inl .K2s))
      (natSyms ((c6Rp q e - c6R q e) * c6Zq q e G B) ++ Sym.mark :: S (.inr (.inl .K2s))) :=
    ⟨_, rfl⟩
  have X2' : Runs (callInj ιc (Lens.snd (Option Sym) Rc) Pc) S1 S2 (fun _ => True)
      (Cc * (c6R q e * c6Zq q e G B)) := by
    refine WP.W9comp.runs_congr X2 ?_
    show Function.update (Function.update S1 (.inr (.inl .K1s))
      (natSyms (c6R q e * c6Zq q e G B) ++ S1 (.inr (.inl .K1s)))) (.inr (.inl .K2s))
      (natSyms ((c6Rp q e - c6R q e) * c6Zq q e G B) ++ S1 (.inr (.inl .K2s))) = S2
    rw [a1, a2, hS2d]
  have hK : c6R q e * c6Zq q e G B + (c6Rp q e - c6R q e) * c6Zq q e G B =
      c6Rp q e * c6Zq q e G B := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' hRR]
  have hv : v.length = A * (c6R q e * c6Zq q e G B + (c6Rp q e - c6R q e) * c6Zq q e G B) := by
    rw [hK, hlen, mul_assoc]
  have P3 := runs_unpadPost (Ec := Ec) (A := A) (K1 := c6R q e * c6Zq q e G B)
    (K2 := (c6Rp q e - c6R q e) * c6Zq q e G B) (w := w) (X1 := S (.inr (.inl .K1s)))
    (X2 := S (.inr (.inl .K2s))) (by omega) hv hw hrest S2
    (by rw [hS2d, hS1d]; simp [hS0]) (by rw [hS2d]; simp) (by rw [hS2d]; simp)
  have X3 := WP.W0m.runs_liftRegs (Lens.fst (Option Sym) Rc) (RunsIn.iff_runs.mp P3)
  have hall := WP.W9comp.runs_seq X1 (WP.W9comp.runs_seq X2' X3)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · rw [c6RowUnpad_eq_rowUnpadL hR0 hZ1 hRR hlen, hS2d, hS1d]
    funext k
    rcases k with i | x | x
    · fin_cases i <;> simp
    · cases x <;> simp
    · simp
  · have hV : vol v = A * (c6R q e * c6Zq q e G B + (c6Rp q e - c6R q e) * c6Zq q e G B) *
        (w + 1) := by
      rw [vol_eq_of_width hw, hv]
    have hu := le_of_eq hv.symm
    have hVU : vol (rowUnpadL (c6R q e * c6Zq q e G B) ((c6Rp q e - c6R q e) * c6Zq q e G B) A v)
        ≤ vol v := by
      rw [vol_eq_of_width (fun p hp => hw p (mem_of_mem_rowUnpadL hp)), length_rowUnpadL _ _ A v hu,
        hV]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
    exact unpad_cost_le hA hpos (bitLen_le_self_row _) (bitLen_le_self_row _) hV hVU

end AppC.C6RowAux

end SubNLogN.Machine
