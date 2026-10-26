/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Streams
import SubNLogN.Machine.Contracts.Family
import Mathlib.Algebra.BigOperators.Fin

/-!
# K1-dist core (`K1/DistributeCore.lean`): record-stream helpers for the K2 kernels

**Scope (honest summary).** Generic helpers for `K1/Distribute.lean` (the proofs of
`K2DistributeStmt` and `K2MergeStmt`; paper: Fact 3.3(3) (`fact:oai-streams`) and
Lemma A.4(4) (`lem:transfer-streams`)). Everything here is fully proved:
* `isRecR`: register test "a record symbol (a payload bit or the record end `sep`) is on top".
  `isRecR_of_blkTerm`: it is `false` on the head of a `BlkTerm` rest; `isRecR_head_cons`: it is
  `true` on the head of a nonempty array.
* Algebra of `arrSyms` / `vol` (`arrSyms_cons`, `arrSyms_append`, `vol_cons`, `vol_append`,
  `length_le_vol`, `vol_drop_anti`, ...), `roleRows_take_succ` (dealing one more row), and
  `mergeRows_succ` (one more merge round), `vol_mergeRows`, `vol_roleRows_le`.
* `gmove src dst`: guarded record move (peek; if a record is on top, W4's `moveRec`, which pushes
  the record reversed; otherwise nothing). Exact evaluations `gmove_eval_rec`, `gmove_eval_skip`.
* `dropArr src`: delete the array on top of `src` (used when `W = 0`); `dropArr_eval`.
* `runs_forEachFin_pot`: `runs_forEachFin` with a telescoping (potential) cost bound.
-/

namespace SubNLogN.Machine.K2

open TMFw TMFw.Contracts TMFw.Lib

/-! ## Record symbols -/

/-- Register test: the register holds a record symbol (a payload bit or the record end `sep`). -/
def isRecR : Option Sym → Bool
  | some (.bit _) => true
  | some .sep => true
  | _ => false

theorem isRecR_of_blkTerm {rest : List Sym} (h : BlkTerm rest) : isRecR rest.head? = false := by
  cases rest with
  | nil => rfl
  | cons d l =>
    obtain ⟨h1, h2⟩ := h d rfl
    cases d <;> simp_all [isRecR, isDataSym]

theorem recSyms_append (p : List Bool) (R : List Sym) :
    recSyms p ++ R = p.map Sym.bit ++ Sym.sep :: R := by
  simp [recSyms]

theorem reverse_recSyms (p : List Bool) :
    (recSyms p).reverse = Sym.sep :: (p.map Sym.bit).reverse := by
  simp [recSyms]

theorem arrSyms_nil : arrSyms ([] : List (List Bool)) = [] := rfl

theorem arrSyms_cons (p : List Bool) (v : List (List Bool)) :
    arrSyms (p :: v) = recSyms p ++ arrSyms v := by
  simp [arrSyms, blk]

theorem arrSyms_append (u v : List (List Bool)) : arrSyms (u ++ v) = arrSyms u ++ arrSyms v := by
  simp [arrSyms, blk]

theorem arrSyms_singleton (p : List Bool) : arrSyms [p] = recSyms p := by
  simp [arrSyms, blk]

theorem vol_nil : vol ([] : List (List Bool)) = 0 := rfl

theorem vol_cons (p : List Bool) (v : List (List Bool)) : vol (p :: v) = p.length + 1 + vol v := by
  simp [vol, arrSyms_cons, recSyms]
  omega

theorem vol_append (u v : List (List Bool)) : vol (u ++ v) = vol u + vol v := by
  simp [vol, arrSyms_append]

theorem length_le_vol : ∀ v : List (List Bool), v.length ≤ vol v
  | [] => le_rfl
  | p :: v => by
    rw [vol_cons, List.length_cons]
    have := length_le_vol v
    omega

theorem isRecR_head_cons (p : List Bool) (v : List (List Bool)) (rest : List Sym) :
    isRecR ((arrSyms (p :: v) ++ rest).head?) = true := by
  rw [arrSyms_cons]
  cases p <;> simp [recSyms, isRecR]

theorem mem_arrSyms {v : List (List Bool)} {x : Sym} (hx : x ∈ arrSyms v) :
    isRecR (some x) = true := by
  induction v with
  | nil => simp [arrSyms_nil] at hx
  | cons p v ih =>
    rw [arrSyms_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [recSyms, List.mem_append, List.mem_map, List.mem_singleton] at hx
      rcases hx with ⟨b, _, rfl⟩ | rfl <;> rfl
    · exact ih hx

theorem mark_not_mem_reverse_arrSyms (v : List (List Bool)) :
    Sym.mark ∉ (arrSyms v).reverse := by
  rw [List.mem_reverse]
  intro h
  have := mem_arrSyms h
  simp [isRecR] at this

theorem bits_data (p : List Bool) : ∀ y ∈ p.map Sym.bit, isDataSym y = true := by
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨_, _, rfl⟩ := hy
  rfl

/-! ## Volumes of suffixes -/

theorem vol_drop_le_vol (l : List (List Bool)) (k : ℕ) : vol (l.drop k) ≤ vol l := by
  conv_rhs => rw [← List.take_append_drop k l]
  rw [vol_append]
  omega

theorem vol_drop_anti (v : List (List Bool)) {m n : ℕ} (h : m ≤ n) :
    vol (v.drop n) ≤ vol (v.drop m) := by
  have : v.drop n = (v.drop m).drop (n - m) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [this]
  exact vol_drop_le_vol _ _

theorem vol_drop_eq_of_lt (v : List (List Bool)) {m : ℕ} (h : m < v.length) :
    vol (v.drop m) = v[m].length + 1 + vol (v.drop (m + 1)) := by
  rw [List.drop_eq_getElem_cons h, vol_cons]

theorem vol_eq_sum (l : List (List Bool)) : vol l = (l.map fun p => p.length + 1).sum := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [vol_cons, ih, List.map_cons, List.sum_cons]

/-- A sum over `List.finRange n` is the `Finset` sum over `Fin n`. -/
theorem sum_finRange {M : Type} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) :
    ((List.finRange n).map f).sum = ∑ i, f i :=
  (Fin.sum_univ_def f).symm

/-! ## `roleRows`: dealing one more row -/

theorem roleRows_nil {α : Type} (W k : ℕ) : roleRows W k ([] : List α) = [] := by
  simp [roleRows]

/-- **Dealing row `m`.** Among the first `m + 1` rows, class `k` gains row `m` iff `m % W = k`. -/
theorem roleRows_take_succ {α : Type} (W k m : ℕ) (v : List α) :
    roleRows W k (v.take (m + 1)) =
      roleRows W k (v.take m) ++ (if m % W = k then v[m]?.toList else []) := by
  by_cases hm : m < v.length
  · have h1 : (v.take (m + 1)).length = m + 1 := by simp; omega
    have h2 : (v.take m).length = m := by simp; omega
    unfold roleRows
    rw [h1, h2, List.range_succ, List.filterMap_append]
    congr 1
    · apply List.filterMap_congr
      intro x hx
      have hx' : x < m := List.mem_range.mp hx
      simp [hx', show x < m + 1 by omega]
    · by_cases hk : m % W = k <;> simp [hk, List.getElem?_eq_getElem hm]
  · have h1 : v.take (m + 1) = v := List.take_of_length_le (by omega)
    have h2 : v.take m = v := List.take_of_length_le (by omega)
    rw [h1, h2, List.getElem?_eq_none (by omega)]
    simp

theorem vol_roleRows_take_le (W k : ℕ) (v : List (List Bool)) :
    ∀ m, vol (roleRows W k (v.take m)) ≤ vol (v.take m)
  | 0 => by simp [roleRows_nil, vol_nil]
  | m + 1 => by
    rw [roleRows_take_succ, List.take_add_one, vol_append, vol_append]
    have ih := vol_roleRows_take_le W k v m
    split_ifs <;> simp [vol_nil] <;> omega

/-- A class of rows is no larger than the whole array. -/
theorem vol_roleRows_le (W k : ℕ) (v : List (List Bool)) : vol (roleRows W k v) ≤ vol v := by
  have := vol_roleRows_take_le W k v v.length
  rwa [List.take_length] at this

/-! ## `mergeRows`: one more round -/

theorem mergeRows_zero {α : Type} (W : ℕ) (ord : Fin W → Fin W) (us : Fin W → List α) :
    mergeRows W ord 0 us = [] := by
  simp [mergeRows]

/-- **One merge round.** With every stream nonempty, round `0` emits the stream heads in the class
order, and the remaining rounds merge the tails. -/
theorem mergeRows_succ {α : Type} (W : ℕ) (ord : Fin W → Fin W) (g : ℕ) (a : Fin W → α)
    (b : Fin W → List α) :
    mergeRows W ord (g + 1) (fun r => a r :: b r) =
      (List.finRange W).map (fun c => a (ord c)) ++ mergeRows W ord g b := by
  unfold mergeRows
  rw [List.range_succ_eq_map, List.flatMap_cons]
  congr 1
  · simp
  · simp [List.flatMap_map]

/-- Split equal-length nonempty streams into heads and tails. -/
theorem exists_cons_fun {W : ℕ} {α : Type} {g : ℕ} (us : Fin W → List α)
    (h : ∀ r, (us r).length = g + 1) :
    ∃ (a : Fin W → α) (b : Fin W → List α), us = (fun r => a r :: b r) ∧ ∀ r, (b r).length = g := by
  have hne : ∀ r, us r ≠ [] := fun r hr => by
    have := h r
    rw [hr] at this
    simp at this
  refine ⟨fun r => (us r).head (hne r), fun r => (us r).tail, ?_, fun r => ?_⟩
  · funext r
    exact (List.cons_head_tail (hne r)).symm
  · rw [List.length_tail, h r]
    rfl

/-- **Volume of a merge**: the merged array has the total volume of the streams. -/
theorem vol_mergeRows {W : ℕ} (ord : Equiv.Perm (Fin W)) :
    ∀ (g : ℕ) (us : Fin W → List (List Bool)), (∀ r, (us r).length = g) →
      vol (mergeRows W ord g us) = ∑ r, vol (us r)
  | 0, us, h => by
    rw [mergeRows_zero]
    have : ∀ r, us r = [] := fun r => List.eq_nil_of_length_eq_zero (h r)
    simp [this, vol_nil]
  | g + 1, us, h => by
    obtain ⟨a, b, rfl, hb⟩ := exists_cons_fun us h
    rw [mergeRows_succ, vol_append, vol_mergeRows ord g b hb, vol_eq_sum, List.map_map,
      sum_finRange]
    have e : ∑ c : Fin W, ((fun p : List Bool => p.length + 1) ∘ fun c => a (ord c)) c =
        ∑ r : Fin W, ((a r).length + 1) :=
      Equiv.sum_comp ord (fun r => (a r).length + 1)
    rw [e, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => (vol_cons _ _).symm)

/-! ## Guarded record move and array deletion -/

section Progs

variable {K : Type}

/-- **Guarded record move** `gmove src dst`: peek `src`; if a record symbol is on top, move the
top record onto `dst` with W4's `moveRec` (which pushes it reversed, `sep` on top); otherwise do
nothing. -/
def gmove (src dst : K) : SProg K := .seq (peekR src) (.ite isRecR (moveRec src dst) skip)

/-- Loop body of `dropArr`: pop one symbol, peek the next. -/
def dropBody (src : K) : SProg K := .seq (popR src) (peekR src)

/-- Delete the array on top of `src` (its `BlkTerm` rest stays). -/
def dropArr (src : K) : SProg K := .seq (peekR src) (.loop isRecR (dropBody src))

theorem closed_gmove (src dst : K) : (gmove src dst).Closed := by
  simp [gmove, Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, peekR, popR, pushR, skip]

theorem closed_dropArr (src : K) : (dropArr src).Closed := by
  simp [dropArr, dropBody, Prog.Closed, Prog.FreeBelow, peekR, popR]

variable [DecidableEq K]

theorem peekR_eval (k : K) (x : Option Sym) (S : K → List Sym) :
    Eval [] (peekR k) ⟨x, S⟩ ⟨(S k).head?, S⟩ 1 :=
  Eval.peek _ _ _ _ _

theorem pushC_eval (k : K) (c : Sym) (x : Option Sym) (S : K → List Sym) :
    Eval [] (pushC k c) ⟨x, S⟩ ⟨x, Function.update S k (c :: S k)⟩ 1 :=
  Eval.push _ _ _ _ _

theorem popR_eval (k : K) (x : Option Sym) (S : K → List Sym) :
    Eval [] (popR k) ⟨x, S⟩ ⟨(S k).head?, Function.update S k (S k).tail⟩ 1 :=
  Eval.pop _ _ _ _ _

/-- `gmove`, record on top: the record moves (reversed) onto `dst`; cost `3·|p| + 5`. -/
theorem gmove_eval_rec {src dst : K} (hne : src ≠ dst) (x : Option Sym) (p : List Bool)
    (R : List Sym) (S : K → List Sym) (hS : S src = recSyms p ++ R) :
    Eval [] (gmove src dst) ⟨x, S⟩
      ⟨some Sym.sep, Function.update (Function.update S src R) dst ((recSyms p).reverse ++ S dst)⟩
      (3 * p.length + 5) := by
  have hpk := peekR_eval src x S
  have htest : isRecR (S src).head? = true := by
    rw [hS]
    cases p <;> simp [recSyms, isRecR]
  have hmv := moveRec_eval hne (S src).head? (p.map Sym.bit) R S (bits_data p)
    (by rw [hS, recSyms_append])
  refine (Eval.seq hpk (Eval.ite_true htest hmv)).of_eq ?_ ?_
  · rw [reverse_recSyms, List.cons_append]
  · simp only [List.length_map]
    omega

/-- `gmove`, no record on top: nothing changes; cost `3`. -/
theorem gmove_eval_skip {src dst : K} (x : Option Sym) (S : K → List Sym)
    (h : isRecR (S src).head? = false) :
    Eval [] (gmove src dst) ⟨x, S⟩ ⟨(S src).head?, S⟩ 3 :=
  (Eval.seq (peekR_eval src x S) (Eval.ite_false (p := moveRec src dst) h (skip_eval [] _))).of_eq
    rfl rfl

theorem dropArr_loop_eval {src : K} (rest : List Sym) (hrest : isRecR rest.head? = false) :
    ∀ (L : List Sym) (S : K → List Sym), (∀ y ∈ L, isRecR (some y) = true) → S src = L ++ rest →
      Eval [] (.loop isRecR (dropBody src)) ⟨(L ++ rest).head?, S⟩
        ⟨rest.head?, Function.update S src rest⟩ (3 * L.length + 1)
  | [], S, _, hS => by
    refine (Eval.loop_false hrest).of_eq ?_ rfl
    rw [List.nil_append] at hS
    rw [← hS, Function.update_eq_self]
    rfl
  | y :: L, S, hL, hS => by
    have hy : isRecR (some y) = true := hL y (by simp)
    have hL' : ∀ z ∈ L, isRecR (some z) = true := fun z hz => hL z (by simp [hz])
    have hpop : Eval [] (popR src) ⟨some y, S⟩ ⟨some y, Function.update S src (L ++ rest)⟩ 1 := by
      refine (Eval.pop [] src (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS]
      rfl
    have hpk : Eval [] (peekR src) ⟨some y, Function.update S src (L ++ rest)⟩
        ⟨(L ++ rest).head?, Function.update S src (L ++ rest)⟩ 1 := by
      refine (peekR_eval src (some y) _).of_eq ?_ rfl
      rw [Function.update_self]
    have ih := dropArr_loop_eval (src := src) rest hrest L (Function.update S src (L ++ rest)) hL'
      (Function.update_self _ _ _)
    refine (Eval.loop_true hy (Eval.seq hpop hpk) ih).of_eq ?_ ?_
    · rw [Function.update_idem]
    · simp only [List.length_cons]
      omega

/-- **`dropArr`, exact**: the array on top of `src` is deleted; cost `3·V + 2`. -/
theorem dropArr_eval {src : K} (x : Option Sym) (v : List (List Bool)) (rest : List Sym)
    (S : K → List Sym) (hrest : BlkTerm rest) (hS : S src = arrSyms v ++ rest) :
    Eval [] (dropArr src) ⟨x, S⟩ ⟨rest.head?, Function.update S src rest⟩ (3 * vol v + 2) := by
  have hpk : Eval [] (peekR src) ⟨x, S⟩ ⟨(arrSyms v ++ rest).head?, S⟩ 1 := by
    refine (peekR_eval src x S).of_eq ?_ rfl
    rw [hS]
  have hl := dropArr_loop_eval rest (isRecR_of_blkTerm hrest) (arrSyms v) S
    (fun y hy => mem_arrSyms hy) hS
  refine (Eval.seq hpk hl).of_eq rfl ?_
  simp only [vol]
  omega

end Progs

/-! ## `forEachFin` with a telescoping cost -/

theorem sum_range_telescope (c : ℕ) (Φ : ℕ → ℕ) (hΦ : ∀ i, Φ (i + 1) ≤ Φ i) :
    ∀ n, ((List.range n).map fun i => c + (Φ i - Φ (i + 1))).sum = n * c + (Φ 0 - Φ n) ∧
      Φ n ≤ Φ 0
  | 0 => by simp
  | n + 1 => by
    obtain ⟨ih, hle⟩ := sum_range_telescope c Φ hΦ n
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    have := hΦ n
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    constructor
    · rw [Nat.succ_mul]
      omega
    · omega

/-- **`runs_forEachFin` with a potential.** If step `i` runs within `c + (Φ i - Φ (i + 1))` for a
non-increasing `Φ`, the whole loop runs within `n·c + (Φ 0 - Φ n) + 1`. -/
theorem runs_forEachFin_pot {K σ : Type} [DecidableEq K] (n : ℕ)
    (f : Fin n → Prog K (fun _ => Sym) σ) (S : ℕ → K → List Sym) (Φ : ℕ → ℕ) (c : ℕ)
    (hΦ : ∀ i, Φ (i + 1) ≤ Φ i)
    (h : ∀ i : Fin n, Runs (f i) (S i) (S (i + 1)) (fun _ => True) (c + (Φ i - Φ (i + 1)))) :
    Runs (forEachFin n f) (S 0) (S n) (fun _ => True) (n * c + (Φ 0 - Φ n) + 1) := by
  have hr := runs_forEachFin n f (fun i => c + (Φ i - Φ (i + 1))) S h
  have hsum : ((List.finRange n).map fun i : Fin n => c + (Φ i - Φ (i + 1))).sum =
      n * c + (Φ 0 - Φ n) := by
    have e : ((List.finRange n).map fun i : Fin n => c + (Φ i - Φ (i + 1))) =
        (List.range n).map fun i => c + (Φ i - Φ (i + 1)) := by
      rw [← List.map_coe_finRange_eq_range, List.map_map]
      rfl
    rw [e]
    exact (sum_range_telescope c Φ hΦ n).1
  rw [hsum] at hr
  exact hr

end SubNLogN.Machine.K2
