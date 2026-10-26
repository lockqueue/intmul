import WP.W9sq.Entry
import WP.W9sq.Loop

/-!
# WP.W9sq.Main1 — the entry loop over the whole stream

`stL Bi es q restS i` is the state after `i` entries: `S` holds the remaining entries `es.drop i`,
then `| $ restS`; `sO` holds the reversed outputs of `es.take i` above `Bi sO`. `loop_spec`: the
peek loop over `S` (stop at `symNode`) runs `entryP` once per entry, from `stL … 0` to
`stL … es.length`.
-/

namespace WP.W9sq

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- The state after `i` entries. -/
def stL (Bi : HL → List Sym) (es : List (ℤ × ℤ)) (q : ℕ) (restS : List Sym) (i : ℕ) :
    HL → List Sym :=
  Function.update (Function.update Bi hS
      (((es.drop i).map entrySyms).flatten ++ symNode :: symLevel :: restS))
    sO ((((es.take i).map fun e => entrySyms (sqE q e)).flatten).reverse ++ Bi sO)

theorem sgnSym_ne_symNode (z : ℤ) : sgnSym z ≠ symNode := by
  unfold sgnSym symNode
  split_ifs <;> decide

theorem stL_S (Bi : HL → List Sym) (es : List (ℤ × ℤ)) (q : ℕ) (restS : List Sym) (i : ℕ) :
    stL Bi es q restS i hS =
      ((es.drop i).map entrySyms).flatten ++ symNode :: symLevel :: restS := by
  unfold stL
  rw [Function.update_of_ne (by decide), Function.update_self]

theorem stL_O (Bi : HL → List Sym) (es : List (ℤ × ℤ)) (q : ℕ) (restS : List Sym) (i : ℕ) :
    stL Bi es q restS i sO =
      (((es.take i).map fun e => entrySyms (sqE q e)).flatten).reverse ++ Bi sO := by
  unfold stL
  rw [Function.update_self]

theorem stL_other (Bi : HL → List Sym) (es : List (ℤ × ℤ)) (q : ℕ) (restS : List Sym) (i : ℕ)
    (k : HL) (h1 : k ≠ hS) (h2 : k ≠ sO) : stL Bi es q restS i k = Bi k := by
  unfold stL
  rw [Function.update_of_ne h2, Function.update_of_ne h1]

theorem stL_succ (Bi : HL → List Sym) (es : List (ℤ × ℤ)) (q : ℕ) (restS : List Sym) (i : ℕ)
    (hi : i < es.length) :
    Function.update (Function.update (stL Bi es q restS i) hS
        (((es.drop (i + 1)).map entrySyms).flatten ++ symNode :: symLevel :: restS)) sO
      ((entrySyms (sqE q es[i])).reverse ++ stL Bi es q restS i sO) =
      stL Bi es q restS (i + 1) := by
  have ht : es.take (i + 1) = es.take i ++ [es[i]] := List.take_succ_eq_append_getElem hi
  funext k
  by_cases h1 : k = sO
  · subst h1
    rw [Function.update_self, stL_O, stL_O, ht, List.map_append, List.flatten_append,
      List.map_singleton, List.flatten_singleton, List.reverse_append, List.append_assoc]
  · by_cases h2 : k = hS
    · subst h2
      rw [Function.update_of_ne h1, Function.update_self, stL_S]
    · rw [Function.update_of_ne h1, Function.update_of_ne h2, stL_other _ _ _ _ _ _ h2 h1,
        stL_other _ _ _ _ _ _ h2 h1]

theorem loop_spec (J : SqI) {Mul : ℕ → ℕ} {C : ℕ} (hJ : SqI.Spec Mul J C) (Bi : HL → List Sym)
    (es : List (ℤ × ℤ)) (q wR : ℕ) (hq : 0 < q) (restS : List Sym)
    (hin : ∀ e ∈ es, EntryW wR e) (hout : ∀ e ∈ es, EntryW wR (sqE q e))
    (tX : TermOK (Bi sX)) (tX2 : TermOK (Bi sX2)) (tY : TermOK (Bi sY)) (tY2 : TermOK (Bi sY2))
    (tP1 : TermOK (Bi sP1)) (tP2 : TermOK (Bi sP2)) (tP3 : TermOK (Bi sP3))
    (tP4 : TermOK (Bi sP4)) (tD : TermOK (Bi sD)) (tE : TermOK (Bi sE)) (tR : TermOK (Bi sR))
    (tI : TermOK (Bi sI)) (rQ rH rH1 : List Sym) (hrQ : TermOK rQ) (hrH : TermOK rH)
    (hrH1 : TermOK rH1) (eQ : Bi sQ = natSyms q ++ rQ) (eH : Bi sH = natSyms (2 ^ (q - 1)) ++ rH)
    (eH1 : Bi sH1 = natSyms (2 ^ (q - 1) - 1) ++ rH1) :
    HT [] (stL Bi es q restS 0) (peekLoop J.lS hS symNode (entryP J))
      (stL Bi es q restS es.length) (1 + (es.length * (entB C Mul wR q + 1 + 1) + 1)) := by
  have hO : ∀ i (k : HL), k ≠ hS → k ≠ sO → stL Bi es q restS i k = Bi k :=
    fun i k h1 h2 => stL_other Bi es q restS i k h1 h2
  refine HT.peekLoop J.lS hS symNode (entryP J) (stL Bi es q restS) es.length (entB C Mul wR q)
    ?_ ?_ ?_
  · intro i hi
    rw [stL_S, List.drop_eq_getElem_cons hi, List.map_cons, List.flatten_cons]
    simp only [entrySyms, intSyms, List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
    exact sgnSym_ne_symNode _
  · rw [stL_S, List.drop_length]
    rfl
  · intro i hi
    have hmem : es[i] ∈ es := List.getElem_mem hi
    obtain ⟨hx, hy⟩ := hin _ hmem
    have hS0 : stL Bi es q restS i hS = entrySyms es[i] ++
        (((es.drop (i + 1)).map entrySyms).flatten ++ symNode :: symLevel :: restS) := by
      rw [stL_S, List.drop_eq_getElem_cons hi, List.map_cons, List.flatten_cons, List.append_assoc]
    refine (entry_spec J hJ (stL Bi es q restS i) wR q hq es[i].1 es[i].2 hx hy (hout _ hmem) _ hS0
      (by rw [hO i _ (by decide) (by decide)]; exact tX)
      (by rw [hO i _ (by decide) (by decide)]; exact tX2)
      (by rw [hO i _ (by decide) (by decide)]; exact tY)
      (by rw [hO i _ (by decide) (by decide)]; exact tY2)
      (by rw [hO i _ (by decide) (by decide)]; exact tP1)
      (by rw [hO i _ (by decide) (by decide)]; exact tP2)
      (by rw [hO i _ (by decide) (by decide)]; exact tP3)
      (by rw [hO i _ (by decide) (by decide)]; exact tP4)
      (by rw [hO i _ (by decide) (by decide)]; exact tD)
      (by rw [hO i _ (by decide) (by decide)]; exact tE)
      (by rw [hO i _ (by decide) (by decide)]; exact tR)
      (by rw [hO i _ (by decide) (by decide)]; exact tI)
      rQ rH rH1 hrQ hrH hrH1 (by rw [hO i _ (by decide) (by decide)]; exact eQ)
      (by rw [hO i _ (by decide) (by decide)]; exact eH)
      (by rw [hO i _ (by decide) (by decide)]; exact eH1)).of_eq ?_ le_rfl
    exact stL_succ Bi es q restS i hi

#assert_std_axioms sgnSym_ne_symNode stL_S stL_O stL_other stL_succ loop_spec

end WP.W9sq
