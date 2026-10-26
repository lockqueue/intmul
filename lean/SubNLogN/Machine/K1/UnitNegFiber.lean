/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitNegProg

/-!
# K5-neg, one fiber (`K1/UnitNegFiber.lean`)

**Scope (honest summary).** Proved exact-stack specification of one negated fiber
(`runsM_negFiber`): `q^b` blocks of `s` records are read (block `0` to the accumulator, the others
to the negation store, by the unary-depth recursion `recProg`), then the store is unloaded block by
block (`loopM_unloadNeg`), each block restored to its internal order. The accumulator receives the
fiber's output `negFib (q^b) s w` (block `0`, then blocks `q^b - 1, …, 1`), reversed. Cost at most
`110·vol` of the fiber. [OAI26, §2.1, proof of Lemma 4]; paper: Lemma A.4 (`lem:transfer-streams`).
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

theorem termOK_revBlocks (bs : List (List (List Bool))) (X : List Sym) (hX : TermOK X) :
    TermOK (bs.flatMap (fun b => (arrSyms b).reverse) ++ X) := by
  induction bs with
  | nil => simpa using hX
  | cons b bs ih =>
    rw [List.flatMap_cons, List.append_assoc, arrSyms_reverse_eq]
    exact termOK_revRecs _ _ ih

theorem length_le_vol (l : List (List Bool)) : l.length ≤ vol l := by
  induction l with
  | nil => simp
  | cons p l ih => rw [vol_cons, List.length_cons]; omega

theorem vol_drop_le (l : List (List Bool)) (n : ℕ) : vol (l.drop n) ≤ vol l := by
  conv_rhs => rw [← List.take_append_drop n l]
  rw [vol_append]
  omega

theorem csum_vol_blk (w : List (List Bool)) (s : ℕ) :
    ∀ (n0 len : ℕ), csum (fun n => vol ((w.drop (n * s)).take s)) n0 len =
      vol ((w.drop (n0 * s)).take (len * s))
  | _, 0 => by simp [csum]
  | n0, len + 1 => by
    simp only [csum]
    rw [csum_vol_blk w s (n0 + 1) len]
    have e1 : (len + 1) * s = s + len * s := by ring
    have e2 : (n0 + 1) * s = n0 * s + s := by ring
    rw [e1, e2, List.take_add, vol_append, List.drop_drop]

theorem vol_revBlocks (s Q : ℕ) (w : List (List Bool)) :
    vol ((List.range (Q - 1)).reverse.flatMap fun i => blkOf s w (i + 1)) =
      vol ((w.take (Q * s)).drop s) := by
  rw [take_drop_blocks]
  simp only [List.flatMap, vol_flatten, List.map_map, List.map_reverse, List.sum_reverse]

section Fiber

variable (nm : Fin 4 → List Sym) (zs xs : Fin 0 → List Sym) (s : ℕ) (r3 : List Sym)

theorem loopM_unloadNeg (hs : 1 ≤ s) (hr3 : TermOK r3) (hnm3 : nm 3 = natSyms s ++ r3) (m : Bool)
    (neg0 : List Sym) :
    ∀ (bs : List (List (List Bool))) (sg : Fin 9 → List Sym), (∀ b ∈ bs, b.length = s) →
      sg 4 = bs.flatMap (fun b => (arrSyms b).reverse) ++ Sym.mark :: neg0 →
      LoopM NEG5 isSepS unloadBlk m (mk5 nm sg zs xs) m
        (mk5 nm (Function.update (Function.update sg 4 (Sym.mark :: neg0)) 0
          ((arrSyms bs.flatten).reverse ++ sg 0)) zs xs)
        (6 * vol bs.flatten + bs.length * (26 * s + 17) + 1)
  | [], sg, _, hneg => by
    refine (LoopM.congr (LoopM.stop ?_) ?_).mono (by simp)
    · rw [mk5_sg, hneg]
      rfl
    · refine mk5_ext rfl ?_ rfl rfl
      funext j
      fin_cases j <;> simp [Function.update_apply, hneg]
  | b :: bs, sg, hbs, hneg => by
    have hb := hbs b List.mem_cons_self
    have hRn := termOK_revBlocks bs (Sym.mark :: neg0) (TermOK.cons rfl _)
    have h1 := runsM_unloadBlk nm zs xs s r3 m sg b hb _ hRn hr3 hnm3
      (by rw [hneg, List.flatMap_cons, List.append_assoc])
    have ih := loopM_unloadNeg hs hr3 hnm3 m neg0 bs
      (Function.update (Function.update sg 4 (bs.flatMap (fun b => (arrSyms b).reverse) ++
        Sym.mark :: neg0)) 0 ((arrSyms b).reverse ++ sg 0))
      (fun b' h => hbs b' (List.mem_cons_of_mem _ h)) (by simp [Function.update_apply])
    have hc : testO isSepS ((mk5 nm sg zs xs) NEG5).head? = true := by
      rw [mk5_sg, hneg, List.flatMap_cons, arrSyms_reverse_eq]
      obtain ⟨p, ps, hp⟩ : ∃ p ps, b.reverse = p :: ps := by
        cases h : b.reverse with
        | nil =>
          have := congrArg List.length h
          rw [List.length_reverse, List.length_nil] at this
          omega
        | cons p ps => exact ⟨p, ps, rfl⟩
      rw [hp, List.flatMap_cons, recSyms_reverse]
      rfl
    refine ((LoopM.step hc h1 ih).congr ?_).mono ?_
    · refine mk5_ext rfl ?_ rfl rfl
      funext j
      fin_cases j <;> simp [Function.update_apply, arrSyms_append, List.flatten_cons]
    · unfold unloadCost
      rw [List.flatten_cons, vol_append, List.length_cons]
      nlinarith

theorem blkOf_length (s : ℕ) (w : List (List Bool)) (t : ℕ) (h : (t + 1) * s ≤ w.length) :
    (blkOf s w t).length = s := by
  simp only [blkOf, List.length_take, List.length_drop]
  rw [Nat.succ_mul] at h
  omega

/-- **One negated fiber.** -/
theorem runsM_negFiber (q : ℕ) (hq : 2 ≤ q) (b : ℕ) (hs : 1 ≤ s) (hr3 : TermOK r3)
    (w : List (List Bool)) (R : List Sym) (hw : q ^ b * s ≤ w.length) (sg : Fin 9 → List Sym)
    (D : List Sym) (hD : D.head? ≠ some tok) (hnm0 : nm 0 = arrSyms w ++ R)
    (hnm3 : nm 3 = natSyms s ++ r3) (hsg1 : sg 1 = List.replicate b tok ++ D) (m : Bool) :
    RunsM (negFiber q) m (mk5 nm sg zs xs) false
      (mk5 (Function.update nm 0 (arrSyms (w.drop (q ^ b * s)) ++ R))
        (Function.update sg 0 ((arrSyms (negFib (q ^ b) s w)).reverse ++ sg 0)) zs xs)
      (110 * vol (w.take (q ^ b * s))) := by
  have hQ1 : 1 ≤ q ^ b := Nat.one_le_pow _ _ (by omega)
  have h1 := RunsM.load (K := L5 0 0) (fun _ => true) m (mk5 nm sg zs xs)
  have h2 := RunsM.push (M := Bool) NEG5 Sym.mark true (mk5 nm sg zs xs)
  rw [upd5_sg, mk5_sg] at h2
  have hrec := runsM_recProg q DEP5 negAct closed_negAct D hD (q ^ b) (fun n => decide (n = 0))
    (negSt nm (Function.update sg 1 D) zs xs s w R (sg 0) (sg 4))
    (fun n => negActCost s ((w.drop (n * s)).take s))
    (fun n _ => by
      simp only [negSt, mk5_sg]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self])
    (fun n hn => by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · have h := runsM_negAct_first nm (Function.update sg 1 D) zs xs s w R (sg 0) (sg 4) r3 hr3
          (le_trans (Nat.le_mul_of_pos_left s hQ1) hw) hnm3
        exact RunsM.of_eq h rfl rfl rfl rfl (by simp)
      · have hw' : (n + 1) * s ≤ w.length :=
          le_trans (Nat.mul_le_mul_right s (by omega)) hw
        have h := runsM_negAct_rest nm (Function.update sg 1 D) zs xs s w R (sg 0) (sg 4) r3 n hpos
          hr3 hw' hnm3
        exact RunsM.of_eq h (decide_eq_false (by omega)).symm rfl
          (decide_eq_false (by omega)).symm rfl le_rfl)
    b 0 (Or.inl hq) (by omega)
  have e0 : Function.update (negSt nm (Function.update sg 1 D) zs xs s w R (sg 0) (sg 4) 0) DEP5
      (List.replicate b tok ++ D) = mk5 nm (Function.update sg 4 (Sym.mark :: sg 4)) zs xs := by
    simp only [negSt, upd5_sg, Nat.zero_mul, List.drop_zero, List.take_zero, List.drop_nil,
      arrSyms_nil, List.reverse_nil, List.nil_append, Nat.min_def]
    refine mk5_ext ?_ ?_ rfl rfl
    · rw [← hnm0, Function.update_eq_self]
    · funext j
      fin_cases j <;> simp [Function.update_apply, hsg1]
  -- the store after the recursion
  have hbsl : ∀ blk ∈ (List.range (q ^ b - 1)).reverse.map (fun i => blkOf s w (i + 1)),
      blk.length = s := by
    intro blk hblk
    simp only [List.mem_map, List.mem_reverse, List.mem_range] at hblk
    obtain ⟨i, hi, rfl⟩ := hblk
    exact blkOf_length s w (i + 1) (le_trans (Nat.mul_le_mul_right s (by omega)) hw)
  have hneg : (Function.update (Function.update (Function.update (Function.update sg 1 D) 0
      ((arrSyms (w.take (min (q ^ b) 1 * s))).reverse ++ sg 0)) 4
      ((arrSyms ((w.take (q ^ b * s)).drop s)).reverse ++ Sym.mark :: sg 4)) 1
      (List.replicate b tok ++ D)) 4 =
      ((List.range (q ^ b - 1)).reverse.map (fun i => blkOf s w (i + 1))).flatMap
        (fun blk => (arrSyms blk).reverse) ++ Sym.mark :: sg 4 := by
    rw [Function.update_of_ne (by decide), Function.update_self, take_drop_blocks,
      rev_arrSyms_flatMap, List.flatMap_map]
  have hnmQ3 : (Function.update nm 0 (arrSyms (w.drop (q ^ b * s)) ++ R)) 3 = natSyms s ++ r3 := by
    rw [Function.update_of_ne (by decide)]
    exact hnm3
  have hun := runsM_whileTop' (loopM_unloadNeg
    (Function.update nm 0 (arrSyms (w.drop (q ^ b * s)) ++ R)) zs xs s r3 hs hr3 hnmQ3 false (sg 4)
    _ _ hbsl hneg)
  have hrec2 : RunsM (recProg q DEP5 negAct) true
      (mk5 nm (Function.update sg 4 (Sym.mark :: sg 4)) zs xs) false
      (mk5 (Function.update nm 0 (arrSyms (w.drop (q ^ b * s)) ++ R))
        (Function.update (Function.update (Function.update (Function.update sg 1 D) 0
          ((arrSyms (w.take (min (q ^ b) 1 * s))).reverse ++ sg 0)) 4
          ((arrSyms ((w.take (q ^ b * s)).drop s)).reverse ++ Sym.mark :: sg 4)) 1
          (List.replicate b tok ++ D)) zs xs)
      (csum (fun n => negActCost s ((w.drop (n * s)).take s)) 0 (q ^ b) + 11 * q ^ b) :=
    RunsM.of_eq hrec rfl e0 (decide_eq_false (by omega))
      (by simp only [Nat.zero_add, negSt, upd5_sg]) le_rfl
  refine RunsM.of_eq (h1.seq (h2.seq (hrec2.seq (hun.seq
    (RunsM.pop (M := Bool) NEG5 Sym.mark (sg 4) false _ ?_))))) rfl rfl rfl ?_ ?_
  · simp [Function.update_apply]
  · rw [upd5_sg]
    refine mk5_ext rfl ?_ rfl rfl
    have hmin : min (q ^ b) 1 = 1 := by omega
    funext j
    fin_cases j <;> simp [Function.update_apply, hsg1, hmin, negFib, blkOf, arrSyms_append,
      List.flatMap]
  · -- cost
    have hcs : csum (fun n => negActCost s ((w.drop (n * s)).take s)) 0 (q ^ b) =
        3 * vol (w.take (q ^ b * s)) + q ^ b * (23 * s + 14) := by
      simp only [negActCost]
      rw [csum_add_fun, csum_add_fun, csum_mul, csum_vol_blk, csum_const, csum_const,
        Nat.zero_mul, List.drop_zero]
      ring
    have hvb : vol ((List.range (q ^ b - 1)).reverse.map (fun i => blkOf s w (i + 1))).flatten ≤
        vol (w.take (q ^ b * s)) := by
      rw [← List.flatMap, vol_revBlocks]
      exact vol_drop_le _ _
    have hbl : ((List.range (q ^ b - 1)).reverse.map (fun i => blkOf s w (i + 1))).length ≤
        q ^ b := by simp
    have hV : q ^ b * s ≤ vol (w.take (q ^ b * s)) := by
      have := length_le_vol (w.take (q ^ b * s))
      rw [List.length_take] at this
      omega
    have hQs : q ^ b ≤ q ^ b * s := Nat.le_mul_of_pos_right _ hs
    have hbl2 : ((List.range (q ^ b - 1)).reverse.map (fun i => blkOf s w (i + 1))).length *
        (26 * s + 17) ≤ 26 * (q ^ b * s) + 17 * q ^ b := by
      calc _ ≤ q ^ b * (26 * s + 17) := Nat.mul_le_mul_right _ hbl
        _ = 26 * (q ^ b * s) + 17 * q ^ b := by ring
    have hQ2 : q ^ b * (23 * s + 14) = 23 * (q ^ b * s) + 14 * q ^ b := by ring
    rw [hcs]
    omega

end Fiber

end SubNLogN.Machine.K1.SMM
