import WP.W9cS.Rows

/-!
# WP.W9cS.Loop — the row loop of the spread driver

`rowLoop e kerP = while (IN holds an entry) { rowWork e kerP; peek IN }`. For a list `Ls` of rows
`(row, out, filter-row symbols)` with `|row| = r > 0`: `IN` is consumed, the outputs are stacked on
`OUT` (reversed, first row deepest), the filter rows move from `TR` to `TL`.
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 TMFw.W4 Computability

variable {K R : Type}

/-- Loop body. -/
def rowBody (e : DS → K) (kerP : BProg K R) : BProg K R :=
  .seq (rowWork e kerP) (lf (peekR (e .IN)))

/-- The row loop. -/
def rowLoop (e : DS → K) (kerP : BProg K R) : BProg K R :=
  .loop (fun v => isRecR v.1) (rowBody e kerP)

theorem rowLoop_closed (e : DS → K) {kerP : BProg K R} (hk : kerP.Closed) :
    (rowLoop e kerP).Closed :=
  ⟨rowWork_closed e hk, lf_closed (by simp [Prog.Closed, Prog.FreeBelow, peekR])⟩

variable [DecidableEq K]

theorem rowLoop_spec {e : DS → K} (he : Function.Injective e) (kerP : BProg K R)
    (c0 c1 : List Sym) (Ck r Lr : ℕ) (hr : 0 < r) :
    ∀ (Ls : List (List (ℤ × ℤ) × List (ℤ × ℤ) × List Sym)) (S : K → List Sym)
      (IN0 restT Q0 T0 RS0 : List Sym),
      (∀ x ∈ Ls, x.1.length = r ∧ (blkE x.1).length ≤ Lr ∧ (blkE x.2.1).length ≤ Lr ∧
        KerOK e kerP c0 c1 Ck x) →
      S (e .IN) = blkE (Ls.flatMap (·.1)) ++ Sym.mark :: IN0 → S (e .W0) = [] →
      S (e .T) = Sym.mark :: T0 → S (e .Q) = Sym.mark :: Q0 →
      S (e .RS) = natSyms r ++ Sym.mark :: RS0 → S (e .TR) = Ls.flatMap (·.2.2) ++ restT →
      S (e .C0) = c0 → S (e .C1) = c1 →
      ∀ v : Option Sym × R, v.1 = (S (e .IN)).head? →
        ∃ v' t, Eval [] (rowLoop e kerP) ⟨v, S⟩
          ⟨v', Function.update (Function.update (Function.update (Function.update S (e .IN)
            (Sym.mark :: IN0)) (e .OUT) ((blkE (Ls.flatMap (·.2.1))).reverse ++ S (e .OUT)))
            (e .TR) restT) (e .TL) ((Ls.flatMap (·.2.2)).reverse ++ S (e .TL))⟩ t ∧
          t ≤ Ls.length * (Ck + 7 * bitLen r + 16 * r + 9 * Lr + 17) + 1
  | [], S, IN0, restT, _, _, _, _, hIN, _, _, _, _, hTR, _, _, v, hv => by
    have hIN' : S (e .IN) = Sym.mark :: IN0 := by simpa [blkE, blk] using hIN
    have hTR' : S (e .TR) = restT := by simpa using hTR
    refine ⟨v, 1, (Eval.loop_false ?_).of_eq ?_ rfl, by simp⟩
    · show isRecR v.1 = false
      rw [hv, hIN']
      rfl
    · congr 1
      funext k
      simp only [Function.update_apply, List.flatMap_nil, List.reverse_nil, List.nil_append,
        blkE_eq_flatten, List.map_nil, List.flatten_nil]
      split_ifs <;> simp_all [he.eq_iff]
  | x :: Ls, S, IN0, restT, Q0, T0, RS0, hLs, hIN, hW, hT, hQ, hRS, hTR, hC0, hC1, v, hv => by
    obtain ⟨hx1, hx2, hx3, hxk⟩ := hLs x (by simp)
    have hLs' : ∀ y ∈ Ls, y.1.length = r ∧ (blkE y.1).length ≤ Lr ∧ (blkE y.2.1).length ≤ Lr ∧
        KerOK e kerP c0 c1 Ck y := fun y hy => hLs y (List.mem_cons_of_mem x hy)
    have hIN' : S (e .IN) = blkE x.1 ++ (blkE (Ls.flatMap (·.1)) ++ Sym.mark :: IN0) := by
      rw [hIN, List.flatMap_cons, blkE_append, List.append_assoc]
    have hTR' : S (e .TR) = x.2.2 ++ (Ls.flatMap (·.2.2) ++ restT) := by
      rw [hTR, List.flatMap_cons, List.append_assoc]
    obtain ⟨v1, t1, e1, ht1⟩ := rowWork_spec he kerP c0 c1 Ck r x hx1 hxk _ _ Q0 T0 RS0 S hIN' hW
      hT hQ hRS hTR' hC0 hC1 v
    set S1 := Function.update (Function.update (Function.update (Function.update S (e .IN)
      (blkE (Ls.flatMap (·.1)) ++ Sym.mark :: IN0)) (e .OUT) ((blkE x.2.1).reverse ++ S (e .OUT)))
      (e .TR) (Ls.flatMap (·.2.2) ++ restT)) (e .TL) (x.2.2.reverse ++ S (e .TL)) with hS1
    have e2 := lf_peek (R := R) (e .IN) v1 S1
    obtain ⟨v2, t2, e3, ht2⟩ := rowLoop_spec he kerP c0 c1 Ck r Lr hr Ls S1 IN0 restT Q0 T0 RS0
      hLs' (by simp [hS1, he.eq_iff]) (by simp [hS1, he.eq_iff, hW]) (by simp [hS1, he.eq_iff, hT])
      (by simp [hS1, he.eq_iff, hQ]) (by simp [hS1, he.eq_iff, hRS]) (by simp [hS1, he.eq_iff])
      (by simp [hS1, he.eq_iff, hC0]) (by simp [hS1, he.eq_iff, hC1]) ((S1 (e .IN)).head?, v1.2)
      rfl
    obtain ⟨z, zs, hz⟩ : ∃ z zs, x.1 = z :: zs := by
      cases h : x.1 with
      | nil => rw [h] at hx1; simp at hx1; omega
      | cons z zs => exact ⟨z, zs, rfl⟩
    have hc : (fun v : Option Sym × R => isRecR v.1) v = true := by
      show isRecR v.1 = true
      rw [hv, hIN', hz, blkE_eq_flatten, List.map_cons, List.flatten_cons, List.append_assoc]
      exact isRecR_head_of_recOK (entrySyms_recOK z) _
    refine ⟨v2, _, (Eval.loop_true hc (Eval.seq e1 e2) e3).of_eq ?_ rfl, ?_⟩
    · congr 1
      funext k
      simp only [hS1, Function.update_apply, List.flatMap_cons, blkE_append, List.reverse_append,
        List.append_assoc]
      split_ifs <;> simp_all [he.eq_iff]
    · simp only [List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

#assert_std_axioms rowLoop_closed rowLoop_spec

end WP.W9c
