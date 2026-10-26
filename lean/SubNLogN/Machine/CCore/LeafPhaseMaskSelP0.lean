/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafPhaseMaskSelEmit

/-!
# C-core phase leaf, record-wise sign selection: the stacks and phase 0 (`LeafPhaseMaskSelP0.lean`)

**Scope (honest summary).** The stack type `ML` of the kernel of `MaskSelStmt` (the 9 named stacks
and the scratch `MSc`), the state notation `msSt`, and phase 0 (`phase0`): from the counters
`K, D, j0, k, ρ` (named stacks `3, 4, 6, 7, 8`, restored) it leaves the mask bits
`maskMSB K ρ (membList ss j0 (m^(k-1)) D)` on the scratch stack `Msk`; every other scratch stack
is left empty (`phase0_of`, proved in `LeafPhaseMaskSelP0Run.lean`).
-/

namespace SubNLogN.Machine.CCore.PhaseMaskAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.BridgePP Computability

/-- Scratch stacks of the `MaskSelStmt` kernel. -/
inductive MSc where
  | Tss | X | C | C2 | U | Fu | Fu2 | R | J | Tmp | Msk | Tb | Tb2 | Gu | Sc | Su | Out
  deriving DecidableEq

instance : Fintype MSc :=
  Fintype.ofList [.Tss, .X, .C, .C2, .U, .Fu, .Fu2, .R, .J, .Tmp, .Msk, .Tb, .Tb2, .Gu, .Sc, .Su,
    .Out] (fun x => by cases x <;> simp)

/-- Stacks of the kernel. -/
abbrev ML : Type := KLoc (Fin 9) MSc

/-- Named stack `i`. -/
abbrev nm (i : Fin 9) : ML := .inl i
/-- Scratch stack `e`. -/
abbrev sc (e : MSc) : ML := .inr e

/-- A state from the named stacks of `St` and the scratch contents `m`. -/
def msSt (St : ML → List Sym) (m : MSc → List Sym) : ML → List Sym
  | .inl i => St (.inl i)
  | .inr e => m e

@[simp] theorem msSt_inl (St : ML → List Sym) (m : MSc → List Sym) (i : Fin 9) :
    msSt St m (.inl i) = St (.inl i) := rfl

@[simp] theorem msSt_inr (St : ML → List Sym) (m : MSc → List Sym) (e : MSc) :
    msSt St m (.inr e) = m e := rfl

theorem update_msSt_inr (St : ML → List Sym) (m : MSc → List Sym) (e : MSc) (l : List Sym) :
    Function.update (msSt St m) (.inr e) l = msSt St (Function.update m e l) := by
  funext k
  rcases k with i | e'
  · simp [Function.update_apply]
  · simp only [msSt_inr, Function.update_apply, Sum.inr.injEq]

theorem update_msSt_inl (St : ML → List Sym) (m : MSc → List Sym) (i : Fin 9) (l : List Sym) :
    Function.update (msSt St m) (.inl i) l = msSt (Function.update St (.inl i) l) m := by
  funext k
  rcases k with i' | e
  · simp only [msSt_inl, Function.update_apply]
  · simp [Function.update_apply]

theorem msSt_clean {St : ML → List Sym} (h : KClean St) : msSt St (fun _ => []) = St := by
  funext k
  rcases k with i | e
  · rfl
  · exact (h e).symm

/-- Scratch contents during phase 0 (all other scratch stacks empty). -/
def p0m (tss x fu r j tmp msk : List Sym) : MSc → List Sym
  | .Tss => tss
  | .X => x
  | .Fu => fu
  | .R => r
  | .J => j
  | .Tmp => tmp
  | .Msk => msk
  | _ => []

theorem p0m_nil : p0m [] [] [] [] [] [] [] = fun _ => [] := by
  funext e; cases e <;> rfl

theorem upd_p0m_Tss (tss x fu r j tmp msk l : List Sym) :
    Function.update (p0m tss x fu r j tmp msk) .Tss l = p0m l x fu r j tmp msk := by
  funext e; cases e <;> rfl
theorem upd_p0m_X (tss x fu r j tmp msk l : List Sym) :
    Function.update (p0m tss x fu r j tmp msk) .X l = p0m tss l fu r j tmp msk := by
  funext e; cases e <;> rfl
theorem upd_p0m_Fu (tss x fu r j tmp msk l : List Sym) :
    Function.update (p0m tss x fu r j tmp msk) .Fu l = p0m tss x l r j tmp msk := by
  funext e; cases e <;> rfl
theorem upd_p0m_R (tss x fu r j tmp msk l : List Sym) :
    Function.update (p0m tss x fu r j tmp msk) .R l = p0m tss x fu l j tmp msk := by
  funext e; cases e <;> rfl
theorem upd_p0m_J (tss x fu r j tmp msk l : List Sym) :
    Function.update (p0m tss x fu r j tmp msk) .J l = p0m tss x fu r l tmp msk := by
  funext e; cases e <;> rfl
theorem upd_p0m_Tmp (tss x fu r j tmp msk l : List Sym) :
    Function.update (p0m tss x fu r j tmp msk) .Tmp l = p0m tss x fu r j l msk := by
  funext e; cases e <;> rfl
theorem upd_p0m_Msk (tss x fu r j tmp msk l : List Sym) :
    Function.update (p0m tss x fu r j tmp msk) .Msk l = p0m tss x fu r j tmp l := by
  funext e; cases e <;> rfl
theorem upd_p0m_C (tss x fu r j tmp msk : List Sym) :
    Function.update (p0m tss x fu r j tmp msk) .C [] = p0m tss x fu r j tmp msk := by
  funext e; cases e <;> rfl
theorem upd_p0m_Fu2 (tss x fu r j tmp msk : List Sym) :
    Function.update (p0m tss x fu r j tmp msk) .Fu2 [] = p0m tss x fu r j tmp msk := by
  funext e; cases e <;> rfl

/-- The slot membership bits, slot `0` first. -/
def slotBools (ss : Finset (Fin mn)) : List Bool := (List.finRange mn).map fun s => decide (s ∈ ss)

/-- The contents of `Tmp` after emitting the chunks `mem` (forward): the mask bits, reversed. -/
def tmpOf (K ρ : ℕ) (mem : List Bool) : List Sym := (maskMSB K ρ mem).reverse.map Sym.bit

theorem tmpOf_nil (K ρ : ℕ) : tmpOf K ρ [] = [] := by simp [tmpOf, maskMSB]

theorem tmpOf_snoc (K ρ : ℕ) (mem : List Bool) (b : Bool) :
    tmpOf K ρ (mem ++ [b]) = List.replicate ρ (Sym.bit false) ++ Sym.bit b ::
      (List.replicate (K - 1 - ρ) (Sym.bit false) ++ tmpOf K ρ mem) := by
  simp [tmpOf, maskMSB, List.flatMap_append, List.reverse_append, List.map_replicate,
    List.reverse_replicate]

/-- One chunk emission of phase 0. -/
def p0Emit (b : Bool) : PProg ML := msEmitP b (sc .X) (nm 8) (sc .C) (sc .C2) (sc .U) (sc .Tmp)

/-- Decrement the remaining-chunk counter `R`. -/
def p0DecR : PProg ML := msLift (decIfPos (sc .R) (sc .U))

/-- Phase 0, part A, for a static table `l`: push `l` onto `Tss`, `X := K - 1 - ρ`,
`Fu := 0^{m^{k-1}}`. -/
def phase0A' (l : List Sym) : PProg ML :=
  .seq (msPushAll (sc .Tss) l)
  (.seq (msLift (copyBlock (nm 3) (sc .X) (sc .C2)))
  (.seq (msLift (decIfPos (sc .X) (sc .U)))
  (.seq (msLift (copyBlock (nm 8) (sc .J) (sc .C2)))
  (.seq (msCd (sc .J) (sc .U) (msLift (decIfPos (sc .X) (sc .U))))
  (.seq (msLift (pushC (sc .Fu) (Sym.bit false)))
  (.seq (msLift (copyBlock (nm 7) (sc .J) (sc .C2)))
  (.seq (msLift (decIfPos (sc .J) (sc .U)))
    (msCd (sc .J) (sc .U) (msMulM (sc .Fu) (sc .Fu2))))))))))

/-- Phase 0, part A: the slot table of `ss`. -/
def phase0A (ss : Finset (Fin mn)) : PProg ML := phase0A' ((slotBools ss).map Sym.bit)

/-- Phase 0, part B: the chunk loops, the reversal onto `Msk`, the clean-up. -/
def phase0B : PProg ML :=
  .seq (msLift (copyBlock (nm 4) (sc .R) (sc .C2)))
  (.seq (msLift (copyBlock (nm 6) (sc .J) (sc .C2)))
  (.seq (msCd (sc .J) (sc .U) (.seq p0DecR (p0Emit false)))
  (.seq (msB (sc .Tss) (msU (sc .Fu) (sc .Fu2) (.seq p0DecR (p0Emit true)))
      (msU (sc .Fu) (sc .Fu2) (.seq p0DecR (p0Emit false))))
  (.seq (msCd (sc .R) (sc .U) (p0Emit false))
  (.seq (msLift (moveBlock (sc .Tmp) (sc .Msk)))
  (.seq (msDropBits (sc .X)) (msDropBits (sc .Fu))))))))

/-- **Phase 0**: emit the mask bits `maskMSB K ρ (membList ss j0 f D)` onto `Msk`. -/
def phase0 (ss : Finset (Fin mn)) : PProg ML := .seq (phase0A ss) phase0B

theorem closed_phase0A' (l : List Sym) : (phase0A' l).Closed := by
  have hcb : ∀ a b c : ML, (msLift (copyBlock a b c)).Closed := fun a b c =>
    closed_msLift (closed_copyBlock' a b c)
  have hdec : ∀ a b : ML, (msLift (decIfPos a b)).Closed := fun a b =>
    closed_msLift (closed_decIfPos a b)
  have h9 := closed_msCd (sc .J) (sc .U) (closed_msMulM (sc .Fu) (sc .Fu2))
  have h8 := WP.W9comp.closed_seq (hdec (sc .J) (sc .U)) h9
  have h7 := WP.W9comp.closed_seq (hcb (nm 7) (sc .J) (sc .C2)) h8
  have h6 := WP.W9comp.closed_seq (closed_msLift (K := ML)
    (by simp [Prog.Closed, Prog.FreeBelow, pushC] : (pushC (sc .Fu) (Sym.bit false)).Closed)) h7
  have h5 := WP.W9comp.closed_seq (closed_msCd (sc .J) (sc .U) (hdec (sc .X) (sc .U))) h6
  have h4 := WP.W9comp.closed_seq (hcb (nm 8) (sc .J) (sc .C2)) h5
  have h3 := WP.W9comp.closed_seq (hdec (sc .X) (sc .U)) h4
  have h2 := WP.W9comp.closed_seq (hcb (nm 3) (sc .X) (sc .C2)) h3
  exact WP.W9comp.closed_seq (closed_msPushAll (sc .Tss) l) h2

theorem closed_phase0A (ss : Finset (Fin mn)) : (phase0A ss).Closed :=
  closed_phase0A' ((slotBools ss).map Sym.bit)

theorem closed_phase0B : phase0B.Closed := by
  have hE : ∀ b, (p0Emit b).Closed := fun b => closed_msEmitP b _ _ _ _ _ _
  have hD : p0DecR.Closed := closed_msLift (closed_decIfPos _ _)
  have hcb : ∀ a b c : ML, (msLift (copyBlock a b c)).Closed := fun a b c =>
    closed_msLift (closed_copyBlock' a b c)
  have g7 := WP.W9comp.closed_seq (closed_msDropBits (sc .X)) (closed_msDropBits (sc .Fu))
  have g6 := WP.W9comp.closed_seq (closed_msLift (closed_moveBlock' (sc .Tmp) (sc .Msk))) g7
  have g5 := WP.W9comp.closed_seq (closed_msCd (sc .R) (sc .U) (hE false)) g6
  have g4 := WP.W9comp.closed_seq (closed_msB (sc .Tss)
    (closed_msU (sc .Fu) (sc .Fu2) (WP.W9comp.closed_seq hD (hE true)))
    (closed_msU (sc .Fu) (sc .Fu2) (WP.W9comp.closed_seq hD (hE false)))) g5
  have g3 := WP.W9comp.closed_seq (closed_msCd (sc .J) (sc .U) (WP.W9comp.closed_seq hD (hE false))) g4
  have g2 := WP.W9comp.closed_seq (hcb (nm 6) (sc .J) (sc .C2)) g3
  exact WP.W9comp.closed_seq (hcb (nm 4) (sc .R) (sc .C2)) g2

theorem closed_phase0 (ss : Finset (Fin mn)) : (phase0 ss).Closed :=
  WP.W9comp.closed_seq (closed_phase0A ss) closed_phase0B

end SubNLogN.Machine.CCore.PhaseMaskAux
