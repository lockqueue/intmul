import WP.W9g.Tape
import WP.W9g.Resc

/-!
# WP.W9g.Comb — the butterfly passes of one combine step

A combine at stage `s` (block halves `Y0`, `Y1` of length `h = 2^s` on `A`, `B`, first entry on
top, each above a `mark`) produces the `2h` output cells in two passes:
* pass 1, cell `u < h`: `cellV (q+2) Y0[u] Y1[u] tw[u]`; `Y0[u]`, `Y1[u]` are saved on `A2`, `B2`;
* pass 2, cell `h + u`: `cellV (q+2) Y0[u] Y1[u] tw[h+u]`.
Each cell (`cell1`) moves the operands to `A2`/`B2`, reads the next twiddle (`readTw`), runs the
butterfly kernel and drops the twiddle. Outputs are pushed onto `R`, so `R` holds them reversed.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-- The output cells of one pass. -/
def cells (q2 : ℕ) : List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ)
  | a :: as, b :: bs, c :: cs => cellV q2 a b c :: cells q2 as bs cs
  | _, _, _ => []

/-- Butterfly context: the shift counters and the terminated temporaries. -/
def BfCtx (q : ℕ) (σ : Stk → List Sym) : Prop :=
  (∃ rq, σ .Q2 = natSyms (q + 2) ++ rq ∧ TermOK rq) ∧
    (∃ r1, σ .ONE = natSyms 1 ++ r1 ∧ TermOK r1) ∧ ∀ k ∈ bfTemps, TermOK (σ k)

/-- Stacks the butterfly context depends on. -/
def bfCtxStk : List Stk := .Q2 :: .ONE :: bfTemps

theorem BfCtx.frame {q : ℕ} {σ σ' : Stk → List Sym} (h : BfCtx q σ)
    (hag : ∀ k ∈ bfCtxStk, σ' k = σ k) : BfCtx q σ' := by
  obtain ⟨⟨rq, hq, hrq⟩, ⟨r1, h1, hr1⟩, hT⟩ := h
  refine ⟨⟨rq, by rw [hag .Q2 (by decide), hq], hrq⟩, ⟨r1, by rw [hag .ONE (by decide), h1], hr1⟩,
    fun k hk => ?_⟩
  rw [hag k (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk))]
  exact hT k hk

/-- Cost bound of one cell. -/
def cellCost (CM CA CS CL CR : ℕ) (Mul : ℕ → ℕ) (w q : ℕ) : ℕ :=
  bflyCost CM CA CS CL CR Mul w q + 24 * eb w + 12

section Prog

variable (X : Prims)

/-- One cell: save the operands, read the twiddle, butterfly, drop the twiddle. -/
def cell1 : MProg Stk X.Reg :=
  (.seq (lm (emove .A .A2 .T1)) (.seq (lm (emove .B .B2 .T1)) (.seq readTw
    (.seq (bflyProg X) (lm (dropEntry .Om))))))

/-- One pass-2 cell: as `cell1`, then drop the saved operands. -/
def cell2 : MProg Stk X.Reg :=
  .seq (cell1 X) (.seq (lm (dropEntry .A2)) (lm (dropEntry .B2)))

/-- Pass 1: one `cell1` per entry of `A`. -/
def pass1 : MProg Stk X.Reg := whileTop .A (notSym .mark) (cell1 X)

/-- Pass 2: one `cell2` per entry of `A`. -/
def pass2 : MProg Stk X.Reg := whileTop .A (notSym .mark) (cell2 X)

theorem cell1_closed : (cell1 X).Closed :=
  ⟨lm_closed (emove_closed _ _ _), lm_closed (emove_closed _ _ _), readTw_closed,
    bflyProg_closed X, lm_closed (dropEntry_closed _)⟩

theorem cell2_closed : (cell2 X).Closed :=
  ⟨cell1_closed X, lm_closed (dropEntry_closed _), lm_closed (dropEntry_closed _)⟩

theorem pass1_closed : (pass1 X).Closed := whileTop_closed (cell1_closed X)

theorem pass2_closed : (pass2 X).Closed := whileTop_closed (cell2_closed X)

end Prog

/-- The state after one cell. -/
def cellSt (q : ℕ) (σ : Stk → List Sym) (y y1 ω : ℤ × ℤ) (rA rB rT : List Sym) : Stk → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update σ .A rA) .A2 (entrySyms y ++ σ .A2)) .B rB) .B2
    (entrySyms y1 ++ σ .B2)) .TR rT) .TL ((entrySyms ω).reverse ++ σ .TL)) .R
    (entrySyms (cellV (q + 2) y y1 ω) ++ σ .R)

/-- **One cell**, exact. -/
theorem cell1_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (w q : ℕ) (y y1 ω : ℤ × ℤ) (rA rB rT : List Sym)
    (σ : Stk → List Sym) (hctx : BfCtx q σ) (hA : σ .A = entrySyms y ++ rA)
    (hB : σ .B = entrySyms y1 ++ rB) (hTR : σ .TR = entrySyms ω ++ rT) (hw0 : EntryW w y)
    (hw1 : EntryW w y1) (hww : EntryW w ω) :
    RS [] (cell1 X) σ (cellSt q σ y y1 ω rA rB rT) (cellCost CM CA CS CL CR Mul w q) := by
  obtain ⟨⟨rq, hq, hrq⟩, ⟨r1, h1, hr1⟩, hT⟩ := hctx
  refine (((emove_rs (src := .A) (dst := .A2) (t := .T1) (by decide) (by decide) (by decide) y rA σ hA).seq
      ((emove_rs (src := .B) (dst := .B2) (t := .T1) (by decide) (by decide) (by decide) y1 rB _ (by exact hB)).seq
      ((readTw_rs ω rT _ (by exact hTR)).seq
      ((bfly_rs hok w q y.1 y.2 ω.1 ω.2 y1.1 y1.2 (σ .A2) (σ .B2) (σ .Om) rq r1 _ (by rfl) (by rfl) (by rfl) (by exact hq) hrq (by exact h1) hr1 (fun k hk => by simp only [bfTemps, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hT _ (by decide)) hw0.1 hw0.2 hww.1 hww.2 hw1.1 hw1.2).seq
      (dropEntry_rs .Om ω (σ .Om) _ (by rfl))))))).congr ?_ ?_
  · funext k
    cases k <;> rfl
  · have e0 := length_entrySyms_le hw0
    have e1 := length_entrySyms_le hw1
    have e2 := length_entrySyms_le hww
    unfold cellCost
    omega

/-- The state after pass 1. -/
def pass1St (q : ℕ) (σ : Stk → List Sym) (y0s y1s ws outs d0 d1 : List (ℤ × ℤ))
    (A0 B0 A20 B20 R0 TRr TLl : List Sym) : Stk → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update σ .A (.mark :: A0)) .B (.mark :: B0)) .TR TRr) .TL
    ((blkE ws).reverse ++ TLl)) .R (blkE (outs ++ cells (q + 2) y0s y1s ws).reverse ++ R0)) .A2
    (blkE (d0 ++ y0s).reverse ++ A20)) .B2 (blkE (d1 ++ y1s).reverse ++ B20)

theorem pass1_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (w q : ℕ) :
    ∀ (y0s y1s ws outs d0 d1 : List (ℤ × ℤ)) (A0 B0 A20 B20 R0 TRr TLl : List Sym)
      (σ : Stk → List Sym),
      y1s.length = y0s.length → ws.length = y0s.length →
      (∀ z ∈ y0s, EntryW w z) → (∀ z ∈ y1s, EntryW w z) → (∀ z ∈ ws, EntryW w z) →
      BfCtx q σ → σ .A = blkE y0s ++ .mark :: A0 → σ .B = blkE y1s ++ .mark :: B0 →
      σ .TR = blkE ws ++ TRr → σ .TL = TLl → σ .R = blkE outs.reverse ++ R0 →
      σ .A2 = blkE d0.reverse ++ A20 → σ .B2 = blkE d1.reverse ++ B20 →
      RS [] (pass1 X) σ (pass1St q σ y0s y1s ws outs d0 d1 A0 B0 A20 B20 R0 TRr TLl)
        (y0s.length * (cellCost CM CA CS CL CR Mul w q + 2) + 2)
  | [], y1s, ws, outs, d0, d1, A0, B0, A20, B20, R0, TRr, TLl, σ, h1, h2, _, _, _, _, hA, hB,
      hTR, hTL, hR, hA2, hB2 => by
    have e1 : y1s = [] := List.eq_nil_of_length_eq_zero h1
    have e2 : ws = [] := List.eq_nil_of_length_eq_zero h2
    subst e1 e2
    refine (whileTop_done ?_).congr ?_ (by simp)
    · rw [hA]
      exact notSym_self _ _
    · unfold pass1St
      simp only [cells, List.append_nil, blkE_nil, List.nil_append, List.reverse_nil] at hA hB hTR ⊢
      rw [← hA, ← hB, ← hTR, ← hTL, ← hR, ← hA2, ← hB2]
      simp only [Function.update_eq_self]
  | y :: ys, [], _, _, _, _, _, _, _, _, _, _, _, _, h1, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp at h1
  | y :: ys, _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, h2, _, _, _, _, _, _, _, _, _, _, _ => by
    simp at h2
  | y :: ys, y1 :: ys1, ω :: ws', outs, d0, d1, A0, B0, A20, B20, R0, TRr, TLl, σ, h1, h2, hw0,
      hw1, hww, hctx, hA, hB, hTR, hTL, hR, hA2, hB2 => by
    refine whileTop_step' ?_ (cell1_rs hok w q y y1 ω (blkE ys ++ .mark :: A0)
      (blkE ys1 ++ .mark :: B0) (blkE ws' ++ TRr) σ hctx
      (by rw [hA, blkE_cons, List.append_assoc]) (by rw [hB, blkE_cons, List.append_assoc])
      (by rw [hTR, blkE_cons, List.append_assoc]) (hw0 y (by simp)) (hw1 y1 (by simp))
      (hww ω (by simp)))
      ((pass1_rs hok w q ys ys1 ws' (outs ++ [cellV (q + 2) y y1 ω]) (d0 ++ [y]) (d1 ++ [y1]) A0 B0
        A20 B20 R0 TRr ((entrySyms ω).reverse ++ TLl) _ (by simpa using h1) (by simpa using h2)
        (fun z hz => hw0 z (by simp [hz])) (fun z hz => hw1 z (by simp [hz]))
        (fun z hz => hww z (by simp [hz]))
        (hctx.frame (fun k hk => by
          simp only [bfCtxStk, bfTemps, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl <;> rfl))
        (by rfl) (by rfl) (by rfl) (by unfold cellSt; rw [← hTL]; rfl)
        (by unfold cellSt; simp [hR, blkE_cons, List.reverse_append])
        (by unfold cellSt; simp [hA2, blkE_cons, List.reverse_append])
        (by unfold cellSt; simp [hB2, blkE_cons, List.reverse_append])).congr ?_ le_rfl) ?_
    · rw [hA, blkE_cons, List.append_assoc]
      exact notSym_entry mark_ok y _
    · have e1 : (outs ++ [cellV (q + 2) y y1 ω]) ++ cells (q + 2) ys ys1 ws' =
          outs ++ cells (q + 2) (y :: ys) (y1 :: ys1) (ω :: ws') := by simp [cells]
      have e2 : (d0 ++ [y]) ++ ys = d0 ++ y :: ys := by simp
      have e3 : (d1 ++ [y1]) ++ ys1 = d1 ++ y1 :: ys1 := by simp
      have e4 : (blkE ws').reverse ++ ((entrySyms ω).reverse ++ TLl) =
          (blkE (ω :: ws')).reverse ++ TLl := by simp [blkE_cons, List.reverse_append]
      unfold pass1St
      rw [e1, e2, e3, e4]
      funext k
      cases k <;> rfl
    · simp only [List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- The state after pass 2. -/
def pass2St (q : ℕ) (σ : Stk → List Sym) (y0s y1s ws outs : List (ℤ × ℤ))
    (A0 B0 R0 TRr TLl : List Sym) : Stk → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update σ .A
    (.mark :: A0)) .B (.mark :: B0)) .TR TRr) .TL ((blkE ws).reverse ++ TLl)) .R
    (blkE (outs ++ cells (q + 2) y0s y1s ws).reverse ++ R0)

theorem pass2_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (w q : ℕ) :
    ∀ (y0s y1s ws outs : List (ℤ × ℤ)) (A0 B0 R0 TRr TLl : List Sym) (σ : Stk → List Sym),
      y1s.length = y0s.length → ws.length = y0s.length →
      (∀ z ∈ y0s, EntryW w z) → (∀ z ∈ y1s, EntryW w z) → (∀ z ∈ ws, EntryW w z) →
      BfCtx q σ → σ .A = blkE y0s ++ .mark :: A0 → σ .B = blkE y1s ++ .mark :: B0 →
      σ .TR = blkE ws ++ TRr → σ .TL = TLl → σ .R = blkE outs.reverse ++ R0 →
      RS [] (pass2 X) σ (pass2St q σ y0s y1s ws outs A0 B0 R0 TRr TLl)
        (y0s.length * (cellCost CM CA CS CL CR Mul w q + 4 * eb w + 2) + 2)
  | [], y1s, ws, outs, A0, B0, R0, TRr, TLl, σ, h1, h2, _, _, _, _, hA, hB, hTR, hTL, hR => by
    have e1 : y1s = [] := List.eq_nil_of_length_eq_zero h1
    have e2 : ws = [] := List.eq_nil_of_length_eq_zero h2
    subst e1 e2
    refine (whileTop_done ?_).congr ?_ (by simp)
    · rw [hA]
      exact notSym_self _ _
    · unfold pass2St
      simp only [cells, List.append_nil, blkE_nil, List.nil_append, List.reverse_nil] at hA hB hTR ⊢
      rw [← hA, ← hB, ← hTR, ← hTL, ← hR]
      simp only [Function.update_eq_self]
  | y :: ys, [], _, _, _, _, _, _, _, _, h1, _, _, _, _, _, _, _, _, _, _ => by simp at h1
  | y :: ys, _ :: _, [], _, _, _, _, _, _, _, _, h2, _, _, _, _, _, _, _, _, _ => by simp at h2
  | y :: ys, y1 :: ys1, ω :: ws', outs, A0, B0, R0, TRr, TLl, σ, h1, h2, hw0, hw1, hww, hctx, hA,
      hB, hTR, hTL, hR => by
    have c1 := cell1_rs hok w q y y1 ω (blkE ys ++ .mark :: A0) (blkE ys1 ++ .mark :: B0)
      (blkE ws' ++ TRr) σ hctx (by rw [hA, blkE_cons, List.append_assoc])
      (by rw [hB, blkE_cons, List.append_assoc]) (by rw [hTR, blkE_cons, List.append_assoc])
      (hw0 y (by simp)) (hw1 y1 (by simp)) (hww ω (by simp))
    have c2 := dropEntry_rs (τ := X.Reg) .A2 y (σ .A2) (cellSt q σ y y1 ω (blkE ys ++ .mark :: A0)
      (blkE ys1 ++ .mark :: B0) (blkE ws' ++ TRr)) (by rfl)
    have c3 := dropEntry_rs (τ := X.Reg) .B2 y1 (σ .B2)
      (Function.update (cellSt q σ y y1 ω (blkE ys ++ .mark :: A0) (blkE ys1 ++ .mark :: B0)
        (blkE ws' ++ TRr)) .A2 (σ .A2)) (by rfl)
    refine whileTop_step' ?_ (c1.seq (c2.seq c3))
      ((pass2_rs hok w q ys ys1 ws' (outs ++ [cellV (q + 2) y y1 ω]) A0 B0 R0 TRr
        ((entrySyms ω).reverse ++ TLl) _ (by simpa using h1) (by simpa using h2)
        (fun z hz => hw0 z (by simp [hz])) (fun z hz => hw1 z (by simp [hz]))
        (fun z hz => hww z (by simp [hz]))
        (hctx.frame (fun k hk => by
          simp only [bfCtxStk, bfTemps, List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl <;> rfl))
        (by rfl) (by rfl) (by rfl) (by unfold cellSt; rw [← hTL]; rfl)
        (by unfold cellSt; simp [hR, blkE_cons, List.reverse_append])).congr ?_ le_rfl) ?_
    · rw [hA, blkE_cons, List.append_assoc]
      exact notSym_entry mark_ok y _
    · have e1 : (outs ++ [cellV (q + 2) y y1 ω]) ++ cells (q + 2) ys ys1 ws' =
          outs ++ cells (q + 2) (y :: ys) (y1 :: ys1) (ω :: ws') := by simp [cells]
      have e4 : (blkE ws').reverse ++ ((entrySyms ω).reverse ++ TLl) =
          (blkE (ω :: ws')).reverse ++ TLl := by simp [blkE_cons, List.reverse_append]
      unfold pass2St
      rw [e1, e4]
      funext k
      cases k <;> rfl
    · have e0 := length_entrySyms_le (hw0 y (by simp))
      have e1 := length_entrySyms_le (hw1 y1 (by simp))
      simp only [List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

#assert_std_axioms BfCtx.frame cell1_closed cell2_closed pass1_closed pass2_closed cell1_rs
  pass1_rs pass2_rs

end WP.W9g
