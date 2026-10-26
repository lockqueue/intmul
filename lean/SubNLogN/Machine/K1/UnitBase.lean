/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitMove

/-!
# K5, layout and fiber-level kit (`K1/UnitBase.lean`)

**Scope (honest summary).** The stack layout shared by the K5 kernels (`K5NegStmt`,
`K5UnitMulMixStmt`, `SubNLogN/Machine/Contracts/Streams.lean` §5) and generic proved lemmas:
* layout `L5 na nx = Fin 4 ⊕ (Fin 9 ⊕ (Fin na ⊕ Fin nx))`: named stacks (`0` source,
  `1` destination, `2` counter `b`, `3` counter `s`), nine single scratch stacks, and two
  families (`na` token counters, `nx` streams); state builder `mk5` with update/read lemmas;
* `unaryB` (`runsM_unaryB`) and `clearDep` (`runsM_clearDep`, imported from `K1/UnitMove.lean`):
  push `b` unary tokens onto the depth stack (countdown of `b`) and clear them again.
Paper: Fact 3.3(4) (`fact:oai-streams`) and Lemma A.4 (`lem:transfer-streams`); the depth
recursion realizes "the target fiber consists of `Q = q^b` consecutive suffix blocks".
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

/-- Private scratch of the K5 kernels: nine single stacks, `na` token counters, `nx` streams. -/
abbrev E5 (na nx : ℕ) : Type := Fin 9 ⊕ (Fin na ⊕ Fin nx)

/-- Stacks of the K5 kernels. -/
abbrev L5 (na nx : ℕ) : Type := KLoc (Fin 4) (E5 na nx)

/-- A K5 stack state from its four component families. -/
abbrev mk5 {na nx : ℕ} (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zs : Fin na → List Sym)
    (xs : Fin nx → List Sym) : L5 na nx → List Sym :=
  Sum.elim nm (Sum.elim sg (Sum.elim zs xs))

section Names

variable {na nx : ℕ}

abbrev SRC5 : L5 na nx := .inl 0
abbrev DST5 : L5 na nx := .inl 1
abbrev BC5 : L5 na nx := .inl 2
abbrev SC5 : L5 na nx := .inl 3
/-- Single scratch stack `j`: `0` accumulator, `1` depth, `2` counter, `3` temporary,
`4` negation store / fiber store, `5` second temporary, `6` concatenation, `7` middle array,
`8` second accumulator. -/
abbrev SG5 (j : Fin 9) : L5 na nx := .inr (.inl j)
abbrev ZS5 (j : Fin na) : L5 na nx := .inr (.inr (.inl j))
abbrev XS5 (j : Fin nx) : L5 na nx := .inr (.inr (.inr j))

abbrev ACC5 : L5 na nx := SG5 0
abbrev DEP5 : L5 na nx := SG5 1
abbrev CNT5 : L5 na nx := SG5 2
abbrev TMP5 : L5 na nx := SG5 3
abbrev NEG5 : L5 na nx := SG5 4
abbrev TMP25 : L5 na nx := SG5 5
abbrev CAT5 : L5 na nx := SG5 6
abbrev MID5 : L5 na nx := SG5 7
abbrev ACC25 : L5 na nx := SG5 8

theorem mk5_eta (S : L5 na nx → List Sym) :
    S = mk5 (fun i => S (.inl i)) (fun j => S (.inr (.inl j))) (fun j => S (.inr (.inr (.inl j))))
      (fun j => S (.inr (.inr (.inr j)))) := by
  funext k
  rcases k with i | j | j | j <;> rfl

theorem mk5_ext {nm nm' : Fin 4 → List Sym} {sg sg' : Fin 9 → List Sym}
    {zs zs' : Fin na → List Sym} {xs xs' : Fin nx → List Sym} (h1 : nm = nm') (h2 : sg = sg')
    (h3 : zs = zs') (h4 : xs = xs') : mk5 nm sg zs xs = mk5 nm' sg' zs' xs' := by
  subst h1 h2 h3 h4
  rfl

@[simp] theorem mk5_nm (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zs : Fin na → List Sym)
    (xs : Fin nx → List Sym) (i : Fin 4) : mk5 nm sg zs xs (.inl i) = nm i := rfl

@[simp] theorem mk5_sg (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zs : Fin na → List Sym)
    (xs : Fin nx → List Sym) (j : Fin 9) : mk5 nm sg zs xs (.inr (.inl j)) = sg j := rfl

@[simp] theorem mk5_zs (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zs : Fin na → List Sym)
    (xs : Fin nx → List Sym) (j : Fin na) : mk5 nm sg zs xs (.inr (.inr (.inl j))) = zs j := rfl

@[simp] theorem mk5_xs (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zs : Fin na → List Sym)
    (xs : Fin nx → List Sym) (j : Fin nx) : mk5 nm sg zs xs (.inr (.inr (.inr j))) = xs j := rfl

theorem upd5_nm (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zs : Fin na → List Sym)
    (xs : Fin nx → List Sym) (i : Fin 4) (x : List Sym) :
    Function.update (mk5 nm sg zs xs) (.inl i) x = mk5 (Function.update nm i x) sg zs xs := by
  show Function.update (Sum.elim nm (Sum.elim sg (Sum.elim zs xs))) (Sum.inl i) x = _
  rw [Sum.update_elim_inl]

theorem upd5_sg (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zs : Fin na → List Sym)
    (xs : Fin nx → List Sym) (j : Fin 9) (x : List Sym) :
    Function.update (mk5 nm sg zs xs) (.inr (.inl j)) x = mk5 nm (Function.update sg j x) zs xs := by
  show Function.update (Sum.elim nm (Sum.elim sg (Sum.elim zs xs))) (Sum.inr (Sum.inl j)) x = _
  rw [Sum.update_elim_inr, Sum.update_elim_inl]

theorem upd5_zs (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zs : Fin na → List Sym)
    (xs : Fin nx → List Sym) (j : Fin na) (x : List Sym) :
    Function.update (mk5 nm sg zs xs) (.inr (.inr (.inl j))) x =
      mk5 nm sg (Function.update zs j x) xs := by
  show Function.update (Sum.elim nm (Sum.elim sg (Sum.elim zs xs))) (Sum.inr (Sum.inr (Sum.inl j)))
    x = _
  rw [Sum.update_elim_inr, Sum.update_elim_inr, Sum.update_elim_inl]

theorem upd5_xs (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zs : Fin na → List Sym)
    (xs : Fin nx → List Sym) (j : Fin nx) (x : List Sym) :
    Function.update (mk5 nm sg zs xs) (.inr (.inr (.inr j))) x =
      mk5 nm sg zs (Function.update xs j x) := by
  show Function.update (Sum.elim nm (Sum.elim sg (Sum.elim zs xs))) (Sum.inr (Sum.inr (Sum.inr j)))
    x = _
  rw [Sum.update_elim_inr, Sum.update_elim_inr, Sum.update_elim_inr]

end Names

end SubNLogN.Machine.K1.SMM
