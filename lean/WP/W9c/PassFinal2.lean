import WP.W9c.PassFinal

/-!
# WP.W9c.PassFinal2 — rewind of the cyclic tape and the end of a pass
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

variable {σ : Type} (K : PKit σ) {Mul : ℕ → ℕ} {C : ℕ}

theorem length_intSyms (z : ℤ) : (intSyms z).length = bitLen z.natAbs + 1 := by
  simp [intSyms, length_natSyms]

/-- **Rewind**: all cells of the right stack `TR` move onto `OUT`, keeping their orientation. -/
theorem ht_rewind (lS : Lens σ (Option Sym)) (Bc : ℕ) (B : PL → List Sym) (tr out : List Sym)
    (ρ : List (HP 10 24 σ)) :
    ∀ (rest pre : List ℤ), (∀ c ∈ rest, bitLen c.natAbs ≤ Bc) →
    HT ρ (Function.update (Function.update B pTR (listSyms rest ++ Sym.mark :: tr)) pOUT
        (listSyms pre ++ out))
      (whileTop lS pTR isSgn (mvNum lS pTR pOUT pTT))
      (Function.update (Function.update B pTR (Sym.mark :: tr)) pOUT
        (listSyms (rest.reverse ++ pre) ++ out))
      (rest.length * (8 * (Bc + 1) + 12) + 2)
  | [], pre, _ => by
    refine (ht_whileTop_false lS pTR isSgn _ _ ?_).of_eq ?_ (by simp)
    · simp [listSyms_nil, isSgn, optT]
    · simp [listSyms_nil]
  | c :: rest, pre, hb => by
    set B0 := Function.update (Function.update B pTR (listSyms (c :: rest) ++ Sym.mark :: tr)) pOUT
      (listSyms pre ++ out) with hB0
    have hm := ht_mvNum (ρ := ρ) lS (src := pTR) (dst := pOUT) (tmp := pTT) (by decide)
      (by decide) (by decide) B0 c (listSyms rest ++ Sym.mark :: tr)
      (by simp [hB0, listSyms_cons])
    have ih := ht_rewind lS Bc B tr out ρ rest (c :: pre) (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    have hm' : HT ρ B0 (mvNum lS pTR pOUT pTT)
        (Function.update (Function.update B pTR (listSyms rest ++ Sym.mark :: tr)) pOUT
          (listSyms (c :: pre) ++ out)) (8 * (intSyms c).length + 10) := by
      refine hm.of_eq ?_ le_rfl
      funext j
      simp only [hB0, Function.update_apply, listSyms_cons, List.append_assoc, List.cons_append]
      split_ifs <;> simp_all
    refine (ht_whileTop_true lS pTR isSgn _ B0 _ _ ?_ hm' ih).of_eq ?_ ?_
    · simp only [hB0]
      rw [Function.update_of_ne (by decide), Function.update_self]
      exact isSgn_head_listSyms c rest _
    · simp [List.reverse_cons, List.append_assoc]
    · have := hb c (List.mem_cons_self ..)
      rw [length_intSyms]
      simp only [List.length_cons]
      nlinarith

#assert_std_axioms length_intSyms ht_rewind

end WP.W9c
