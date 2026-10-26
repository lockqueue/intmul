/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.DistributeCore
import IntMulTM.Framework.Lib.Counter

/-!
# K1-dist block core (`K1/DistributeBlkCore.lean`): moving a row of `s` records

**Scope (honest summary).** Generic helpers for the block versions of the K2 kernels (a *row* is a
block of `s` consecutive records, `s` a runtime parameter held as a binary counter `natSyms s` on a
parameter stack). Everything here is fully proved:
* `rowMove src dst cnt T tmp`: push a `mark` on `T`, copy the counter `s` from `cnt` onto `T`
  (`TMFw.Lib.copyBlock`), then `s` times: W4's `moveRec src dst` and `TMFw.Lib.dec T tmp`; finally
  drop the `mark`. Exact evaluation `rowMove_eval`: the first `s` records of `src` move (each
  reversed, the last on top) onto `dst`; `cnt`, `T`, `tmp` are restored. Cost
  `3·vol (row) + incSeqCost 6 10 s + 7·bitLen s + 11`, where the decrement costs are amortized by
  `TMFw.incSeqCost_le` (`incSeqCost 6 10 s ≤ 16·s`).
* `zerosLead_encodeNat_succ`: the trailing zeros of `n + 1` are the trailing ones of `n` (this is
  what makes a count-down as cheap as a count-up).
-/

namespace SubNLogN.Machine.K2

open TMFw TMFw.Contracts TMFw.Lib Computability

theorem zerosLead_incBits : ∀ L : List Bool, zerosLead (incBits L) = ones L
  | [] => rfl
  | true :: L => by simp [incBits, zerosLead, ones, zerosLead_incBits L]
  | false :: L => by simp [incBits, zerosLead, ones]

theorem zerosLead_encodeNat_succ (n : ℕ) : zerosLead (encodeNat (n + 1)) = ones (encodeNat n) := by
  rw [encodeNat_succ, zerosLead_incBits]

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n :=
  WP.W9comp.bitLen_le_of_lt_two_pow (Nat.lt_two_pow_self)

section Progs

variable {K : Type}

/-- Body of the row loop: move one record, decrement the counter, test it. -/
def rowBody (src dst T tmp : K) : SProg K := .seq (moveRec src dst) (.seq (dec T tmp) (zeroTest T))

/-- Row loop: while the counter on `T` is nonzero. -/
def rowLoop (src dst T tmp : K) : SProg K := .loop optIsBit (rowBody src dst T tmp)

/-- **Move one row of `s` records** from `src` to `dst`; `s` is read from the counter stack `cnt`;
`T`, `tmp` are temporaries (restored). -/
def rowMove (src dst cnt T tmp : K) : SProg K :=
  .seq (pushC T .mark) (.seq (copyBlock cnt T tmp) (.seq (zeroTest T)
    (.seq (rowLoop src dst T tmp) (popR T))))

theorem closed_rowMove (src dst cnt T tmp : K) : (rowMove src dst cnt T tmp).Closed := by
  simp [rowMove, rowLoop, rowBody, Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, dec,
    copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody, restoreR, scanLoop,
    scanBody, decFix, zeroTest, pushC, peekR, popR, pushR, skip]

variable [DecidableEq K]

/-- **The row loop, exact.** With counter `j` on `T` (above a terminator `TR`) and at least `j`
records on `src`, the loop moves the first `j` records onto `dst` (each reversed) and leaves the
counter `0`. Cost `3·vol (u.take j) + incSeqCost 6 10 j + 1`. -/
theorem rowLoop_eval {src dst T tmp : K} (h1 : src ≠ dst) (h2 : src ≠ T) (h3 : dst ≠ T)
    (h4 : T ≠ tmp) (TR : List Sym) (hTR : TermOK TR) (R : List Sym) :
    ∀ (j : ℕ) (u : List (List Bool)) (S : K → List Sym), j ≤ u.length →
      S src = arrSyms u ++ R → S T = natSyms j ++ TR →
      Eval [] (rowLoop src dst T tmp) ⟨(S T).head?, S⟩
        ⟨TR.head?, Function.update (Function.update (Function.update S src
          (arrSyms (u.drop j) ++ R)) dst ((arrSyms (u.take j)).reverse ++ S dst)) T TR⟩
        (3 * vol (u.take j) + incSeqCost 6 10 j + 1)
  | 0, u, S, _, hsrc, hT => by
    have hT' : S T = TR := by simpa [natSyms, encodeNat_zero] using hT
    refine (Eval.loop_false ?_).of_eq ?_ ?_
    · rw [hT']
      exact optIsBit_head?_of_termOK hTR
    · rw [hT']
      congr 1
      rw [List.drop_zero, List.take_zero, arrSyms_nil, List.reverse_nil, List.nil_append, ← hsrc,
        Function.update_eq_self, Function.update_eq_self, ← hT', Function.update_eq_self]
    · simp [vol_nil, incSeqCost]
  | j + 1, u, S, hj, hsrc, hT => by
    obtain ⟨p, u', rfl⟩ : ∃ p u', u = p :: u' := by
      cases u with
      | nil => simp at hj
      | cons p u' => exact ⟨p, u', rfl⟩
    have hj' : j ≤ u'.length := by simp at hj; omega
    -- moveRec
    have e1 := moveRec_eval h1 (S T).head? (p.map Sym.bit) (arrSyms u' ++ R) S (bits_data p)
      (by rw [hsrc, arrSyms_cons, List.append_assoc, recSyms_append])
    set S1 := Function.update (Function.update S src (arrSyms u' ++ R)) dst
      (Sym.sep :: ((p.map Sym.bit).reverse ++ S dst)) with hS1
    have hS1T : S1 T = (encodeNat (j + 1)).map Sym.bit ++ TR := by
      rw [hS1, Function.update_of_ne (Ne.symm h3), Function.update_of_ne (Ne.symm h2), hT]
      rfl
    -- dec
    have e2 := dec_eval h4 [] (some Sym.sep) j TR S1 hTR hS1T
    set S2 := Function.update S1 T ((encodeNat j).map Sym.bit ++ TR) with hS2
    -- zeroTest
    have e3 := peekR_eval T (some Sym.mark) S2
    have hS2src : S2 src = arrSyms u' ++ R := by
      rw [hS2, Function.update_of_ne h2, hS1, Function.update_of_ne h1, Function.update_self]
    have hS2T : S2 T = natSyms j ++ TR := by rw [hS2, Function.update_self]; rfl
    have ih := rowLoop_eval h1 h2 h3 h4 TR hTR R j u' S2 hj' hS2src hS2T
    have htest : optIsBit (S T).head? = true := by
      rw [hT]
      obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat (j + 1) = b :: l := by
        cases h : encodeNat (j + 1) with
        | nil => exact absurd ((encodeNat_eq_nil_iff _).1 h) (by omega)
        | cons b l => exact ⟨b, l, rfl⟩
      simp [natSyms, hbl]
    refine (Eval.loop_true htest (Eval.seq e1 (Eval.seq e2 e3)) ih).of_eq ?_ ?_
    · congr 1
      have hS2dst : S2 dst = (recSyms p).reverse ++ S dst := by
        rw [hS2, Function.update_of_ne h3, hS1, Function.update_self, reverse_recSyms,
          List.cons_append]
      funext k
      rw [hS2dst]
      simp only [hS2, hS1, Function.update_apply, List.drop_succ_cons, List.take_succ_cons,
        arrSyms_cons, List.reverse_append, List.append_assoc]
      split_ifs <;> simp_all
    · rw [List.take_succ_cons, vol_cons, incSeqCost, ← zerosLead_encodeNat_succ]
      simp only [List.length_map]
      omega

end Progs

end SubNLogN.Machine.K2

namespace SubNLogN.Machine.K2

open TMFw TMFw.Contracts TMFw.Lib Computability

section RowMove

variable {K : Type} [DecidableEq K]

/-- **`rowMove`, exact.** With `s ≤ |u|` records on `src` and the counter `s` on `cnt`, the first
`s` records of `src` move onto `dst` (each reversed, the last on top); `cnt`, `T`, `tmp` are
restored. Cost `3·vol (u.take s) + incSeqCost 6 10 s + 7·bitLen s + 11`. -/
theorem rowMove_eval {src dst cnt T tmp : K} (h1 : src ≠ dst) (h2 : src ≠ T) (h3 : dst ≠ T)
    (h4 : T ≠ tmp) (h5 : cnt ≠ T) (h6 : cnt ≠ tmp) (x : Option Sym) (s : ℕ) (rc : List Sym)
    (hrc : TermOK rc) (u : List (List Bool)) (R : List Sym) (S : K → List Sym)
    (hs : s ≤ u.length) (hsrc : S src = arrSyms u ++ R) (hcnt : S cnt = natSyms s ++ rc) :
    Eval [] (rowMove src dst cnt T tmp) ⟨x, S⟩
      ⟨some Sym.mark, Function.update (Function.update S src (arrSyms (u.drop s) ++ R)) dst
        ((arrSyms (u.take s)).reverse ++ S dst)⟩
      (3 * vol (u.take s) + incSeqCost 6 10 s + 7 * bitLen s + 11) := by
  have e0 := pushC_eval T Sym.mark x S
  set S1 := Function.update S T (Sym.mark :: S T) with hS1
  have e1 := copyBlock_eval h5 h6 h4 [] x (encodeNat s) rc S1 hrc
    (by rw [hS1, Function.update_of_ne h5]; exact hcnt)
  set S2 := Function.update S1 T ((encodeNat s).map Sym.bit ++ S1 T) with hS2
  have e2 := peekR_eval T (some Sym.mark) S2
  have hS2src : S2 src = arrSyms u ++ R := by
    rw [hS2, Function.update_of_ne h2, hS1, Function.update_of_ne h2]
    exact hsrc
  have hS2T : S2 T = natSyms s ++ (Sym.mark :: S T) := by
    rw [hS2, Function.update_self, hS1, Function.update_self]
    rfl
  have e3 := rowLoop_eval h1 h2 h3 h4 (Sym.mark :: S T) (TermOK.cons (by rfl) _) R s u S2 hs
    hS2src hS2T
  set S3 := Function.update (Function.update (Function.update S2 src (arrSyms (u.drop s) ++ R))
    dst ((arrSyms (u.take s)).reverse ++ S2 dst)) T (Sym.mark :: S T) with hS3
  have e4 : Eval [] (popR T) ⟨(Sym.mark :: S T).head?, S3⟩
      ⟨some Sym.mark, Function.update S3 T (S T)⟩ 1 := by
    refine (popR_eval T _ S3).of_eq ?_ rfl
    rw [hS3, Function.update_self]
    rfl
  refine (Eval.seq e0 (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4)))).of_eq ?_ ?_
  · congr 1
    funext k
    simp only [hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [bitLen]
    omega

/-- The `rowMove` cost bound used by the kernels: `3·vol + 23·s + 11`. -/
theorem rowMove_cost_le (s : ℕ) (u : List (List Bool)) :
    3 * vol (u.take s) + incSeqCost 6 10 s + 7 * bitLen s + 11 ≤ 3 * vol (u.take s) + 23 * s + 11 := by
  have h1 := incSeqCost_le 6 10 s
  have h2 := bitLen_le_self s
  omega

/-- **Guarded row move**: if a record is on top of `src`, move one row; otherwise nothing. -/
def growMove (src dst cnt T tmp : K) : SProg K :=
  .seq (peekR src) (.ite isRecR (rowMove src dst cnt T tmp) skip)

theorem growMove_eval_skip {src dst cnt T tmp : K} (x : Option Sym) (S : K → List Sym)
    (h : isRecR (S src).head? = false) :
    Eval [] (growMove src dst cnt T tmp) ⟨x, S⟩ ⟨(S src).head?, S⟩ 3 :=
  (Eval.seq (peekR_eval src x S)
    (Eval.ite_false (p := rowMove src dst cnt T tmp) h (skip_eval [] _))).of_eq rfl rfl

theorem growMove_eval_row {src dst cnt T tmp : K} (h1 : src ≠ dst) (h2 : src ≠ T) (h3 : dst ≠ T)
    (h4 : T ≠ tmp) (h5 : cnt ≠ T) (h6 : cnt ≠ tmp) (x : Option Sym) (s : ℕ) (rc : List Sym)
    (hrc : TermOK rc) (u : List (List Bool)) (hu : u ≠ []) (R : List Sym) (S : K → List Sym)
    (hs : s ≤ u.length) (hsrc : S src = arrSyms u ++ R) (hcnt : S cnt = natSyms s ++ rc) :
    Eval [] (growMove src dst cnt T tmp) ⟨x, S⟩
      ⟨some Sym.mark, Function.update (Function.update S src (arrSyms (u.drop s) ++ R)) dst
        ((arrSyms (u.take s)).reverse ++ S dst)⟩
      (3 * vol (u.take s) + incSeqCost 6 10 s + 7 * bitLen s + 13) := by
  have htest : isRecR (S src).head? = true := by
    obtain ⟨p, u', rfl⟩ := List.exists_cons_of_ne_nil hu
    rw [hsrc]
    exact isRecR_head_cons _ _ _
  refine (Eval.seq (peekR_eval src x S)
    (Eval.ite_true htest (rowMove_eval h1 h2 h3 h4 h5 h6 _ s rc hrc u R S hs hsrc hcnt))).of_eq
    rfl ?_
  omega

end RowMove

theorem closed_growMove {K : Type} (src dst cnt T tmp : K) :
    (growMove src dst cnt T tmp).Closed :=
  ⟨by simp [Prog.FreeBelow, peekR], closed_rowMove src dst cnt T tmp,
    by simp [Prog.FreeBelow, skip]⟩

end SubNLogN.Machine.K2

namespace SubNLogN.Machine.K2

open TMFw TMFw.Contracts TMFw.Lib

/-! ## `roleBlocks` and `mergeBlocks` -/

theorem roleBlocks_nil {α : Type} (W w s : ℕ) : roleBlocks W w s ([] : List α) = [] := by
  simp [roleBlocks]

/-- **Dealing record `x`**: class `w` gains record `x` iff its row `x / s` has class `w`. -/
theorem roleBlocks_take_succ {α : Type} (W w s x : ℕ) (v : List α) :
    roleBlocks W w s (v.take (x + 1)) =
      roleBlocks W w s (v.take x) ++ (if x / s % W = w then v[x]?.toList else []) := by
  by_cases hm : x < v.length
  · have h1 : (v.take (x + 1)).length = x + 1 := by simp; omega
    have h2 : (v.take x).length = x := by simp; omega
    unfold roleBlocks
    rw [h1, h2, List.range_succ, List.filterMap_append]
    congr 1
    · apply List.filterMap_congr
      intro y hy
      have hy' : y < x := List.mem_range.mp hy
      simp [hy', show y < x + 1 by omega]
    · by_cases hk : x / s % W = w <;> simp [hk, List.getElem?_eq_getElem hm]
  · have h1 : v.take (x + 1) = v := List.take_of_length_le (by omega)
    have h2 : v.take x = v := List.take_of_length_le (by omega)
    rw [h1, h2, List.getElem?_eq_none (by omega)]
    simp

/-- **Dealing row `m`** (records `[m·s, m·s + j)`, `j ≤ s`): class `w` gains them iff
`m % W = w`. -/
theorem roleBlocks_take_row {α : Type} (W w s m : ℕ) (v : List α) :
    ∀ j, j ≤ s → roleBlocks W w s (v.take (m * s + j)) =
      roleBlocks W w s (v.take (m * s)) ++ (if m % W = w then (v.drop (m * s)).take j else [])
  | 0, _ => by simp
  | j + 1, hj => by
    rw [← Nat.add_assoc, roleBlocks_take_succ, roleBlocks_take_row W w s m v j (by omega)]
    have hs : 0 < s := by omega
    have hdiv : (m * s + j) / s = m := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    rw [hdiv, List.take_add_one, List.getElem?_drop]
    split_ifs <;> simp

theorem vol_roleBlocks_le (W w s : ℕ) (v : List (List Bool)) :
    vol (roleBlocks W w s v) ≤ vol v := by
  have key : ∀ m, vol (roleBlocks W w s (v.take m)) ≤ vol (v.take m) := by
    intro m
    induction m with
    | zero => simp [roleBlocks_nil, vol_nil]
    | succ m ih =>
      rw [roleBlocks_take_succ, List.take_add_one, vol_append, vol_append]
      split_ifs <;> simp [vol_nil] <;> omega
  have := key v.length
  rwa [List.take_length] at this

theorem mergeBlocks_zero {α : Type} (W : ℕ) (ord : Fin W → Fin W) (s : ℕ) (us : Fin W → List α) :
    mergeBlocks W ord 0 s us = [] := by
  simp [mergeBlocks]

theorem mergeBlocks_s_zero {α : Type} (W : ℕ) (ord : Fin W → Fin W) (g : ℕ)
    (us : Fin W → List α) : mergeBlocks W ord g 0 us = [] := by
  simp [mergeBlocks]

/-- **One block-merge round**: round `0` emits the first rows (`take s`) in class order; the
remaining rounds merge the rest (`drop s`). -/
theorem mergeBlocks_succ {α : Type} (W : ℕ) (ord : Fin W → Fin W) (g s : ℕ)
    (us : Fin W → List α) :
    mergeBlocks W ord (g + 1) s us =
      (List.finRange W).flatMap (fun c => (us (ord c)).take s) ++
        mergeBlocks W ord g s (fun r => (us r).drop s) := by
  unfold mergeBlocks
  rw [List.range_succ_eq_map, List.flatMap_cons]
  congr 1
  · simp
  · rw [List.flatMap_map]
    congr 1
    funext t
    congr 1
    funext c
    rw [List.drop_drop, Nat.succ_mul, Nat.add_comm (t * s) s]

theorem vol_flatMap {β : Type} (l : List β) (f : β → List (List Bool)) :
    vol (l.flatMap f) = (l.map fun b => vol (f b)).sum := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.flatMap_cons, vol_append, ih, List.map_cons, List.sum_cons]

theorem vol_take_add_drop (s : ℕ) (u : List (List Bool)) :
    vol (u.take s) + vol (u.drop s) = vol u := by
  rw [← vol_append, List.take_append_drop]

/-- **Volume of a block merge**: the total volume of the streams. -/
theorem vol_mergeBlocks {W : ℕ} (ord : Equiv.Perm (Fin W)) (s : ℕ) :
    ∀ (g : ℕ) (us : Fin W → List (List Bool)), (∀ r, (us r).length = g * s) →
      vol (mergeBlocks W ord g s us) = ∑ r, vol (us r)
  | 0, us, h => by
    rw [mergeBlocks_zero]
    have : ∀ r, us r = [] := fun r => List.eq_nil_of_length_eq_zero (by rw [h r]; simp)
    simp [this, vol_nil]
  | g + 1, us, h => by
    have hd : ∀ r, ((us r).drop s).length = g * s := fun r => by
      rw [List.length_drop, h r, Nat.succ_mul, Nat.add_sub_cancel]
    rw [mergeBlocks_succ, vol_append, vol_mergeBlocks ord s g _ hd, vol_flatMap, sum_finRange,
      show (∑ c : Fin W, vol ((us (ord c)).take s)) = ∑ r : Fin W, vol ((us r).take s) from
        Equiv.sum_comp ord (fun r => vol ((us r).take s)), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => vol_take_add_drop s (us r))

end SubNLogN.Machine.K2
