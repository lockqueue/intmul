import WP.W9c.BlockPackStep

/-!
# WP.W9c.BlockPackHorner — rebuild one chain's value from its chunks

`hornerP b` (`ht_horner`): the chunk stack of chain `b` holds the chunks (last on top, each followed
by `sep`) above a `mark`, the carry stack holds the final carry `c`. While the chunk stack's top is
not `mark`: `acc := chunk + acc·2^k` (`W3_concatAt`, cost independent of `acc`), pop the `sep`. Then
pop the `mark`. The accumulator ends as `hval (2^k) cs c` (`= packNat`, by `hval_chain`).
-/

namespace WP.W9c.BlockPack

open TMFw TMFw.Contracts WP.W7k2 Computability

section

variable (K : Kit)

/-- Horner pass of chain `b`. -/
def hornerP (b : Bool) : BProg 6 8 K.Reg :=
  (whileTopP K.lS1 (chT b) (fun x => !decide (x = Sym.mark))
    ((cCat K (chC b) kK (chT b)).seq (popS (chT b)))).seq (popS (chT b))

theorem hornerP_closed (b : Bool) : (hornerP K b).Closed :=
  ⟨whileTopP_closed _ _ _ ⟨callI_closed _ _ _ _, trivial⟩, trivial⟩

end

/-- Horner state of chain `b` with `n` chunks left. -/
def stH (r : HS) (b : Bool) (k : ℕ) (cs : List ℕ) (c : ℕ) (rC rT : List Sym) (n : ℕ) : HS :=
  (r.set (chC b) (natSyms (hval (2 ^ k) (cs.drop n) c) ++ rC)).set (chT b)
    (chunkSyms (cs.take n).reverse ++ Sym.mark :: rT)

theorem head_natSyms_sep_ne_mark (m : ℕ) (l : List Sym) :
    optP (fun x => !decide (x = Sym.mark)) (natSyms m ++ Sym.sep :: l).head? = true := by
  cases h : encodeNat m with
  | nil => simp [natSyms, h, optP]
  | cons b bs => simp [natSyms, h, optP]

theorem stH_chT (r : HS) (b : Bool) (k : ℕ) (cs : List ℕ) (c : ℕ) (rC rT : List Sym) (n : ℕ) :
    (stH r b k cs c rC rT n).f (chT b) = chunkSyms (cs.take n).reverse ++ Sym.mark :: rT := by
  unfold stH
  cases b <;> rfl

theorem stH_chT_succ (r : HS) (b : Bool) (k : ℕ) (cs : List ℕ) (c : ℕ) (rC rT : List Sym) (n : ℕ)
    (hn : n < cs.length) :
    (stH r b k cs c rC rT (n + 1)).f (chT b) =
      natSyms cs[n] ++ Sym.sep :: (chunkSyms (cs.take n).reverse ++ Sym.mark :: rT) := by
  rw [stH_chT, List.take_succ_eq_append_getElem hn, chunkSyms_snoc_rev, List.append_assoc,
    List.cons_append]

variable {K : Kit} {C : ℕ} {ρ : List (BProg 6 8 K.Reg)}

/-- **The Horner pass.** -/
theorem ht_horner (hK : K.OK C) (b : Bool) (r : HS) (k : ℕ) (cs : List ℕ) (c U' : ℕ)
    (rC rT rk : List Sym) (hrC : TermOK rC) (hrk : TermOK rk) (hk : r.k = natSyms k ++ rk)
    (hcs : ∀ x ∈ cs, x < 2 ^ k) (hU : 2 * k + 1 ≤ U') :
    HT ρ (stH r b k cs c rC rT cs.length).f (hornerP K b)
      ((r.set (chC b) (natSyms (hval (2 ^ k) cs c) ++ rC)).set (chT b) rT).f
      (cs.length * (C * U' + 3) + 3) := by
  have hloop := HT.whileTopP (ρ := ρ) K.lS1 (chT b) (fun x => !decide (x = Sym.mark))
    (fun n => (stH r b k cs c rC rT n).f) ((cCat K (chC b) kK (chT b)).seq (popS (chT b)))
    (fun _ => C * U' + 1) cs.length
    (fun n hn => by
      show optP _ ((stH r b k cs c rC rT (n + 1)).f (chT b)).head? = true
      rw [stH_chT_succ r b k cs c rC rT n hn]
      exact head_natSyms_sep_ne_mark _ _)
    (by
      show optP _ ((stH r b k cs c rC rT 0).f (chT b)).head? = false
      rw [stH_chT]
      rfl)
    (fun n hn => by
      have hx : (stH r b k cs c rC rT (n + 1)).f (chC b) =
          natSyms (hval (2 ^ k) (cs.drop (n + 1)) c) ++ rC := by
        unfold stH
        cases b <;> rfl
      have hc : (stH r b k cs c rC rT (n + 1)).f kK = natSyms k ++ rk := by
        unfold stH
        cases b <;> exact hk
      have s1 := ht_cat (ρ := ρ) hK (stH r b k cs c rC rT (n + 1)) (chC b) kK (chT b)
        (by cases b <;> decide) (hval (2 ^ k) (cs.drop (n + 1)) c) cs[n] k rC rk
        (Sym.sep :: (chunkSyms (cs.take n).reverse ++ Sym.mark :: rT)) hrC hrk (TermOK.cons rfl _)
        (hcs _ (List.getElem_mem hn)) hx hc (stH_chT_succ r b k cs c rC rT n hn)
      have s2 := ht_pop (ρ := ρ) (((stH r b k cs c rC rT (n + 1)).set (chC b)
          (natSyms (cs[n] + hval (2 ^ k) (cs.drop (n + 1)) c * 2 ^ k) ++ rC)).set (chT b)
          (Sym.sep :: (chunkSyms (cs.take n).reverse ++ Sym.mark :: rT))) (chT b) Sym.sep
        (chunkSyms (cs.take n).reverse ++ Sym.mark :: rT) (by cases b <;> rfl)
      have hv : hval (2 ^ k) (cs.drop n) c = cs[n] + hval (2 ^ k) (cs.drop (n + 1)) c * 2 ^ k := by
        rw [List.drop_eq_getElem_cons hn, hval_cons]
        ring
      refine (HT.seq s1 s2).of_eq ?_ ?_
      · show _ = (stH r b k cs c rC rT n).f
        unfold stH
        rw [hv]
        cases b <;> rfl
      · show C * (k + bitLen k + 1) + 1 ≤ C * U' + 1
        have bk := bitLen_le_self k
        have e := Nat.mul_le_mul_left C (show k + bitLen k + 1 ≤ U' by omega)
        omega)
  rw [loopCost_const] at hloop
  have hpop := ht_pop (ρ := ρ) (stH r b k cs c rC rT 0) (chT b) Sym.mark rT
    (by rw [stH_chT]; rfl)
  have e3 : cs.length * (C * U' + 1 + 1 + 1) = cs.length * (C * U' + 3) := by ring
  refine (HT.seq hloop hpop).of_eq ?_ (by omega)
  unfold stH
  cases b <;> rfl

#assert_std_axioms hornerP_closed head_natSyms_sep_ne_mark stH_chT stH_chT_succ ht_horner

end WP.W9c.BlockPack
