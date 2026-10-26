/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelDefs

/-!
# C-core leaf 9 (Lemma A.9 row addition): the counter layout (`CCore/LeafRowAddCS.lean`)

The private layout `CS` of the packed-addition counter kernel: the descriptor `desc`, the seven
counter stacks `c i` (Lemma A.9 named stacks `1`–`7`: `K, ρ, f, N1, N2, N3, R`) and twenty work stacks `w i`.
`setC S vals` is `S` with counter stack `i` holding `natSyms (vals i)`.
-/

namespace SubNLogN.Machine.CCore.LeafRowAddAux

open TMFw TMFw.Contracts

/-- Stacks of the counter kernel. -/
inductive CS where
  | desc : CS
  | c : Fin 7 → CS
  | w : Fin 20 → CS
  deriving DecidableEq

namespace CS
abbrev wT : CS := .w 0
abbrev wC : CS := .w 1
abbrev t1 : CS := .w 2
abbrev t2 : CS := .w 3
abbrev t3 : CS := .w 4
abbrev mA : CS := .w 5
abbrev mB : CS := .w 6
abbrev mAcc : CS := .w 7
abbrev mT : CS := .w 8
abbrev mQ : CS := .w 9
abbrev mTd : CS := .w 10
abbrev pK : CS := .w 11
abbrev pt : CS := .w 12
abbrev x0 : CS := .w 13
abbrev x1 : CS := .w 14
abbrev x2 : CS := .w 15
abbrev x3 : CS := .w 16
abbrev x4 : CS := .w 17
abbrev x5 : CS := .w 18
abbrev x6 : CS := .w 19
end CS

/-- The state with counter stack `i` holding `natSyms (vals i)`. -/
def setC (S : CS → List Sym) (vals : Fin 7 → ℕ) : CS → List Sym
  | .c i => natSyms (vals i)
  | k => S k

end SubNLogN.Machine.CCore.LeafRowAddAux
