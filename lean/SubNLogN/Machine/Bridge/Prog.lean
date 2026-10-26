/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.Cost

/-!
# K5 reduction (6): the assembled bridge program

`bridgeProg hm P1 … P10` is the bridge machine built from the part programs (1 pre-scale,
2 reorder, 3 expose, 4 restore, 5 spread lines, 6 solve, 7 output, 8 counter init, 9 middle,
10 counter decrement), on the stacks `KLoc BrN (BrW ⊕ BrEP E1 … E9)` and registers
`Option Sym × BrRR R1 … R10`: the skeleton `bridgeProgOf` with each part embedded by `callInj`
(`ιK`, `ιM`, `ιD` of `Kit.lean`) through the injections `jn1 … jn9`, `jnD` and the lenses
`ln1 … ln10`. One fixed program for all runtime parameters. All proved.
-/

namespace SubNLogN.Machine.BridgeRed

open TMFw TMFw.Contracts SubNLogN.Machine

/-- Scratch of the assembled bridge: the parts' scratch types and `Fin 4` for the counter
kernel. A plain `def` (not reducible), with explicit instances below: instance search over a
ten-fold nested sum is too expensive. -/
def BrEP (E1 E2 E3 E4 E5 E6 E7 E8 E9 : Type) : Type :=
  E1 ⊕ (E2 ⊕ (E3 ⊕ (E4 ⊕ (E5 ⊕ (E6 ⊕ (E7 ⊕ (E8 ⊕ (E9 ⊕ Fin 4))))))))

/-- Binary `DecidableEq` of a sum (a cheap instance problem). -/
def decEqSum2 {α β : Type} [DecidableEq α] [DecidableEq β] : DecidableEq (α ⊕ β) := inferInstance

/-- Binary `Fintype` of a sum. -/
def fintypeSum2 {α β : Type} [Fintype α] [Fintype β] : Fintype (α ⊕ β) := inferInstance

instance instDecidableEqBrEP {E1 E2 E3 E4 E5 E6 E7 E8 E9 : Type} [i1 : DecidableEq E1]
    [i2 : DecidableEq E2] [i3 : DecidableEq E3] [i4 : DecidableEq E4] [i5 : DecidableEq E5]
    [i6 : DecidableEq E6] [i7 : DecidableEq E7] [i8 : DecidableEq E8] [i9 : DecidableEq E9] :
    DecidableEq (BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9) :=
  @decEqSum2 _ _ i1 (@decEqSum2 _ _ i2 (@decEqSum2 _ _ i3 (@decEqSum2 _ _ i4 (@decEqSum2 _ _ i5
    (@decEqSum2 _ _ i6 (@decEqSum2 _ _ i7 (@decEqSum2 _ _ i8 (@decEqSum2 _ (Fin 4) i9
      inferInstance))))))))

instance instFintypeBrEP {E1 E2 E3 E4 E5 E6 E7 E8 E9 : Type} [i1 : Fintype E1]
    [i2 : Fintype E2] [i3 : Fintype E3] [i4 : Fintype E4] [i5 : Fintype E5]
    [i6 : Fintype E6] [i7 : Fintype E7] [i8 : Fintype E8] [i9 : Fintype E9] :
    Fintype (BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9) :=
  @fintypeSum2 _ _ i1 (@fintypeSum2 _ _ i2 (@fintypeSum2 _ _ i3 (@fintypeSum2 _ _ i4
    (@fintypeSum2 _ _ i5 (@fintypeSum2 _ _ i6 (@fintypeSum2 _ _ i7 (@fintypeSum2 _ _ i8
      (@fintypeSum2 _ (Fin 4) i9 inferInstance))))))))

/-- Registers of the assembled bridge (after the flag). -/
abbrev BrRR (R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 : Type) : Type :=
  R1 × (R2 × (R3 × (R4 × (R5 × (R6 × (R7 × (R8 × (R9 × R10))))))))

section Inj

variable {E1 E2 E3 E4 E5 E6 E7 E8 E9 : Type}

def jn1 : E1 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9 := fun e => Sum.inl e
def jn2 : E2 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9 := fun e => Sum.inr (Sum.inl e)
def jn3 : E3 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9 := fun e => Sum.inr (Sum.inr (Sum.inl e))
def jn4 : E4 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9 :=
  fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))
def jn5 : E5 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9 :=
  fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl e))))
def jn6 : E6 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9 :=
  fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))))
def jn7 : E7 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9 :=
  fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl e))))))
def jn8 : E8 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9 :=
  fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))))))
def jn9 : E9 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9 :=
  fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inl e))))))))
def jnD {m : ℕ} (h : m ≤ 4) : Fin m → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9 :=
  fun j => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Fin.castLE h j)))))))))

theorem jn1_injective : Function.Injective (jn1 : E1 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9) :=
  fun _ _ h => Sum.inl_injective h
theorem jn2_injective : Function.Injective (jn2 : E2 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9) :=
  fun _ _ h => Sum.inl_injective (Sum.inr_injective h)
theorem jn3_injective : Function.Injective (jn3 : E3 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9) :=
  fun _ _ h => Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))
theorem jn4_injective : Function.Injective (jn4 : E4 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9) :=
  fun _ _ h => Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h)))
theorem jn5_injective : Function.Injective (jn5 : E5 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9) :=
  fun _ _ h => Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective
    (Sum.inr_injective h))))
theorem jn6_injective : Function.Injective (jn6 : E6 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9) :=
  fun _ _ h => Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective
    (Sum.inr_injective (Sum.inr_injective h)))))
theorem jn7_injective : Function.Injective (jn7 : E7 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9) :=
  fun _ _ h => Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective
    (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h))))))
theorem jn8_injective : Function.Injective (jn8 : E8 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9) :=
  fun _ _ h => Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective
    (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h)))))))
theorem jn9_injective : Function.Injective (jn9 : E9 → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9) :=
  fun _ _ h => Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective
    (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective
      (Sum.inr_injective h))))))))
theorem jnD_injective {m : ℕ} (hm : m ≤ 4) :
    Function.Injective (jnD hm : Fin m → BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9) :=
  fun _ _ h => Fin.castLE_injective hm (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective
    (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective
      (Sum.inr_injective (Sum.inr_injective h)))))))))

end Inj

section Lens

variable {R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 : Type}

def ln1 : Lens (Option Sym × BrRR R1 R2 R3 R4 R5 R6 R7 R8 R9 R10) R1 :=
  (Lens.snd _ _).comp (Lens.fst _ _)
def ln2 : Lens (Option Sym × BrRR R1 R2 R3 R4 R5 R6 R7 R8 R9 R10) R2 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def ln3 : Lens (Option Sym × BrRR R1 R2 R3 R4 R5 R6 R7 R8 R9 R10) R3 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def ln4 : Lens (Option Sym × BrRR R1 R2 R3 R4 R5 R6 R7 R8 R9 R10) R4 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
def ln5 : Lens (Option Sym × BrRR R1 R2 R3 R4 R5 R6 R7 R8 R9 R10) R5 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))
def ln6 : Lens (Option Sym × BrRR R1 R2 R3 R4 R5 R6 R7 R8 R9 R10) R6 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))
def ln7 : Lens (Option Sym × BrRR R1 R2 R3 R4 R5 R6 R7 R8 R9 R10) R7 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))))))
def ln8 : Lens (Option Sym × BrRR R1 R2 R3 R4 R5 R6 R7 R8 R9 R10) R8 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
      (Lens.fst _ _))))))))
def ln9 : Lens (Option Sym × BrRR R1 R2 R3 R4 R5 R6 R7 R8 R9 R10) R9 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
      ((Lens.snd _ _).comp (Lens.fst _ _)))))))))
def ln10 : Lens (Option Sym × BrRR R1 R2 R3 R4 R5 R6 R7 R8 R9 R10) R10 :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
      ((Lens.snd _ _).comp (Lens.snd _ _)))))))))

end Lens

/-- **The assembled bridge program.** -/
def bridgeProg {E1 E2 E3 E4 E5 E6 E7 E8 E9 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 : Type} {m : ℕ}
    (hm : m ≤ 4) (P1 : Prog (KLoc BrK E1) (fun _ => Sym) R1)
    (P2 : Prog (KLoc BrK E2) (fun _ => Sym) R2) (P3 : Prog (KLoc BrK E3) (fun _ => Sym) R3)
    (P4 : Prog (KLoc BrK E4) (fun _ => Sym) R4) (P5 : Prog (KLoc BrK E5) (fun _ => Sym) R5)
    (P6 : Prog (KLoc BrK E6) (fun _ => Sym) R6) (P7 : Prog (KLoc BrK E7) (fun _ => Sym) R7)
    (P8 : Prog (KLoc BrK E8) (fun _ => Sym) R8) (P9 : Prog (KLoc (Fin 2) E9) (fun _ => Sym) R9)
    (P10 : Prog (Loc 1 m) (fun _ => Sym) R10) :
    Prog (KLoc BrN (BrW ⊕ BrEP E1 E2 E3 E4 E5 E6 E7 E8 E9)) (fun _ => Sym)
      (Option Sym × BrRR R1 R2 R3 R4 R5 R6 R7 R8 R9 R10) :=
  bridgeProgOf (.inr (.inl .ax)) (callInj (ιK jn1) ln1 P1) (callInj (ιK jn2) ln2 P2)
    (callInj (ιK jn8) ln8 P8) (callInj (ιK jn3) ln3 P3) (callInj (ιK jn5) ln5 P5)
    (callInj (ιK jn4) ln4 P4) (callInj (ιD (jnD hm)) ln10 P10) (callInj (ιM jn9) ln9 P9)
    (callInj (ιK jn6) ln6 P6) (callInj (ιK jn7) ln7 P7)

theorem closed_bridgeProg {E1 E2 E3 E4 E5 E6 E7 E8 E9 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 : Type}
    {m : ℕ} (hm : m ≤ 4) {P1 : Prog (KLoc BrK E1) (fun _ => Sym) R1}
    {P2 : Prog (KLoc BrK E2) (fun _ => Sym) R2} {P3 : Prog (KLoc BrK E3) (fun _ => Sym) R3}
    {P4 : Prog (KLoc BrK E4) (fun _ => Sym) R4} {P5 : Prog (KLoc BrK E5) (fun _ => Sym) R5}
    {P6 : Prog (KLoc BrK E6) (fun _ => Sym) R6} {P7 : Prog (KLoc BrK E7) (fun _ => Sym) R7}
    {P8 : Prog (KLoc BrK E8) (fun _ => Sym) R8} {P9 : Prog (KLoc (Fin 2) E9) (fun _ => Sym) R9}
    {P10 : Prog (Loc 1 m) (fun _ => Sym) R10} (h1 : P1.Closed) (h2 : P2.Closed)
    (h3 : P3.Closed) (h4 : P4.Closed) (h5 : P5.Closed) (h6 : P6.Closed) (h7 : P7.Closed)
    (h8 : P8.Closed) (h9 : P9.Closed) (h10 : P10.Closed) :
    (bridgeProg hm P1 P2 P3 P4 P5 P6 P7 P8 P9 P10).Closed :=
  closed_bridgeProgOf _ (closed_callInj _ _ h1) (closed_callInj _ _ h2) (closed_callInj _ _ h8)
    (closed_callInj _ _ h3) (closed_callInj _ _ h5) (closed_callInj _ _ h4)
    (closed_callInj _ _ h10) (closed_callInj _ _ h9) (closed_callInj _ _ h6)
    (closed_callInj _ _ h7)

end SubNLogN.Machine.BridgeRed
