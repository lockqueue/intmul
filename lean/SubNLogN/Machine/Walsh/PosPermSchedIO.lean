/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedBase
import SubNLogN.Machine.Walsh.PosPermSchedIOList

/-!
# Schedule compiler IO, emission (`Machine/Walsh/PosPermSchedIO.lean`)

Generic IO programs (any stack type `K`, `SProg K`) of the runtime schedule compiler
(`PosPermSchedStmt`, `PosPermLeaf.lean`), with exact `Runs` rules:

* `tbl`: the π table format (`una a ++ [sep]` per entry, entry `0` on top);
* `moveAll src dst`: move a whole stack, `dst := src.reverse ++ dst`, `src := []`;
* `emitField x q tmp acc`: the unary register `x = una n` is consumed and the accumulator gains
  `natSyms n ++ [mark]` (`acc` holds the reverse of the emitted text, so this emits the text
  `(natSyms n ++ [mark]).reverse`: a mark, then the bits most significant first). The bits are
  produced by repeated halving (`halveStep`, least significant first) onto the scratch stack
  `tmp`, then moved (reversed) onto `acc`. Cost `7 (n + 1)^2`.

**Scope (honest summary).** Definitions and proved rules; no contract is proved here.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.PSIO

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine Computability
open SubNLogN.Machine.Walsh.PosPermSchedAux

/-- The π table format: entry `a` is `una a ++ [sep]`, the first entry on top. -/
def tbl (l : List ℕ) : List Sym := l.flatMap fun a => una a ++ [Sym.sep]

/-! ## Pure lemmas on `natSyms` (bits of `n / 2 ^ i`) -/

theorem natSyms_zero : natSyms 0 = [] := by
  simp [natSyms, encodeNat_zero]

theorem natSyms_eq_nil_iff (m : ℕ) : natSyms m = [] ↔ m = 0 := by
  simp [natSyms, encodeNat_eq_nil_iff]

theorem natSyms_div_two (m : ℕ) : natSyms (m / 2) = (natSyms m).tail := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [natSyms_zero]
  · rw [natSyms_halve m (by omega), List.tail_cons]

theorem natSyms_div_pow (n i : ℕ) : natSyms (n / 2 ^ i) = (natSyms n).drop i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, ← Nat.div_div_eq_div_mul, natSyms_div_two, ih, List.tail_drop]

theorem div_pow_ne_zero_iff (n i : ℕ) : n / 2 ^ i ≠ 0 ↔ i < (natSyms n).length := by
  rw [Ne, ← natSyms_eq_nil_iff, natSyms_div_pow, ← List.length_eq_zero_iff, List.length_drop]
  omega

theorem natSyms_getElem (n i : ℕ) (hi : i < (natSyms n).length) :
    (natSyms n)[i] = Sym.bit (decide (n / 2 ^ i % 2 = 1)) := by
  have h1 := natSyms_div_pow n i
  rw [natSyms_halve _ ((div_pow_ne_zero_iff n i).2 hi), List.drop_eq_getElem_cons hi] at h1
  exact (List.cons.inj h1).1.symm

theorem take_succ_reverse_natSyms (n i : ℕ) (hi : i < (natSyms n).length) :
    ((natSyms n).take (i + 1)).reverse =
      Sym.bit (decide (n / 2 ^ i % 2 = 1)) :: ((natSyms n).take i).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, natSyms_getElem n i hi]
  simp

theorem natSyms_length_le (n : ℕ) : (natSyms n).length ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [natSyms_zero]
    · rw [natSyms_halve n (by omega), List.length_cons]
      have := ih (n / 2) (by omega)
      omega

/-- The arithmetic of the `emitField` cost bound. -/
theorem emit_cost_le (n N : ℕ) (hN : N ≤ n) :
    1 + (N * (6 * n + 9 + 2) + 2 + (N * 4 + 2)) ≤ 7 * (n + 1) ^ 2 := by
  have h1 : N * (6 * n + 9 + 2) ≤ n * (6 * n + 9 + 2) := Nat.mul_le_mul_right _ hN
  have h2 : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have h3 : n * (6 * n + 9 + 2) = 6 * (n * n) + 11 * n := by ring
  have h4 : n ≤ n * n + 1 := by nlinarith
  rw [h2]
  omega

section Generic

variable {K : Type} [DecidableEq K]

/-! ## Three distinguished registers -/

/-- The state `S` with stacks `x`, `q`, `t` overwritten by `a`, `b`, `c`. -/
def upd3 (S : K → List Sym) (x q t : K) (a b c : List Sym) : K → List Sym :=
  Function.update (Function.update (Function.update S x a) q b) t c

section Upd3

variable {S : K → List Sym} {x q t : K} {a b c : List Sym}

theorem upd3_x (hxq : x ≠ q) (hxt : x ≠ t) (a' : List Sym) :
    Function.update (upd3 S x q t a b c) x a' = upd3 S x q t a' b c := by
  funext k
  simp only [upd3, Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

theorem upd3_q (hqt : q ≠ t) (b' : List Sym) :
    Function.update (upd3 S x q t a b c) q b' = upd3 S x q t a b' c := by
  funext k
  simp only [upd3, Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

theorem upd3_t (c' : List Sym) :
    Function.update (upd3 S x q t a b c) t c' = upd3 S x q t a b c' := by
  unfold upd3
  rw [Function.update_idem]

theorem upd3_app_x (hxq : x ≠ q) (hxt : x ≠ t) : upd3 S x q t a b c x = a := by
  unfold upd3
  rw [Function.update_of_ne hxt, Function.update_of_ne hxq, Function.update_self]

theorem upd3_app_q (hqt : q ≠ t) : upd3 S x q t a b c q = b := by
  unfold upd3
  rw [Function.update_of_ne hqt, Function.update_self]

theorem upd3_app_t : upd3 S x q t a b c t = c := by
  unfold upd3
  rw [Function.update_self]

theorem upd3_congr {a' b' c' : List Sym} (ha : a = a') (hb : b = b') (hc : c = c') :
    upd3 S x q t a b c = upd3 S x q t a' b' c' := by
  subst ha hb hc
  rfl

end Upd3

/-! ## Branch on a peeked top -/

/-- Peek `k` and branch on the peeked symbol. -/
theorem runs_peekIte {k : K} {c : Option Sym → Bool} {p q : SProg K} {S S' : K → List Sym}
    {T : ℕ} (hp : c (S k).head? = true → Runs p S S' (fun _ => True) T)
    (hq : c (S k).head? = false → Runs q S S' (fun _ => True) T) :
    Runs (.seq (peekR k) (.ite c p q)) S S' (fun _ => True) (T + 2) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ := runs_peekR k S s hs
  cases hc : c (S k).head?
  · obtain ⟨s2, t2, e2, hq2, ht2⟩ := hq hc s1 hs1
    exact ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_false (by rw [hv1]; exact hc) e2), hq2,
      by omega⟩
  · obtain ⟨s2, t2, e2, hq2, ht2⟩ := hp hc s1 hs1
    exact ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_true (by rw [hv1]; exact hc) e2), hq2,
      by omega⟩

/-! ## Moving a whole stack -/

/-- Move all of `src` onto `dst` (reversing it). -/
def moveAll (src dst : K) : SProg K := whileNE src (mv src dst)

omit [DecidableEq K] in
theorem closed_moveAll (src dst : K) : (moveAll src dst).Closed := by
  simp [moveAll, whileNE, whileTop, mv, popR, pushR, peekR, Prog.Closed, Prog.FreeBelow]

theorem runs_moveAll {src dst : K} (hne : src ≠ dst) (S : K → List Sym) :
    Runs (moveAll src dst) S
      (Function.update (Function.update S src []) dst ((S src).reverse ++ S dst))
      (fun _ => True) ((S src).length * 4 + 2) := by
  have h := runs_whileNE (k := src) (p := mv src dst)
    (fun i => Function.update (Function.update S src ((S src).drop i)) dst
      (((S src).take i).reverse ++ S dst)) 2 (S src).length
    (fun i hi => by
      simp only [Function.update_of_ne hne, Function.update_self]
      intro h0
      rw [List.drop_eq_nil_iff] at h0
      omega)
    (by simp [Function.update_of_ne hne])
    (fun i hi => by
      have hdrop : (S src).drop i = (S src)[i] :: (S src).drop (i + 1) :=
        List.drop_eq_getElem_cons hi
      have h1 := runs_mv hne (Function.update (Function.update S src ((S src).drop i)) dst
        (((S src).take i).reverse ++ S dst)) (S src)[i] ((S src).drop (i + 1))
        (by rw [Function.update_of_ne hne, Function.update_self, hdrop])
      have hv : (S src)[i] :: (((S src).take i).reverse ++ S dst) =
          ((S src).take (i + 1)).reverse ++ S dst := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
          List.reverse_append, List.reverse_singleton, List.singleton_append, List.cons_append]
      refine runs_weak h1 ?_ le_rfl
      rw [upd4 hne, Function.update_self, hv])
  have h0 : Function.update (Function.update S src ((S src).drop 0)) dst
      (((S src).take 0).reverse ++ S dst) = S := by
    simp only [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append,
      Function.update_eq_self]
  rw [h0] at h
  simp only [List.drop_length, List.take_length] at h
  exact h

/-! ## Halving a unary register -/

/-- Inner loop body: pop a token; if another one follows, pop it too and count it in `q`;
otherwise (odd) turn the top `bit false` of `tmp` into `bit true`. -/
def halveBody (x q tmp : K) : SProg K :=
  .seq (popR x) (.seq (peekR x) (.ite isSomeB (.seq (popR x) (incR q))
    (.seq (popR tmp) (pushC tmp (Sym.bit true)))))

/-- One halving step: `x := x / 2` (via `q`), `bit (x % 2)` pushed on `tmp`. -/
def halveStep (x q tmp : K) : SProg K :=
  .seq (pushC tmp (Sym.bit false)) (.seq (whileNE x (halveBody x q tmp)) (moveU q x))

/-- **Field emission**: consume `x = una n`; the accumulator gains `natSyms n ++ [mark]`. -/
def emitField (x q tmp acc : K) : SProg K :=
  .seq (pushC acc Sym.mark) (.seq (whileNE x (halveStep x q tmp)) (moveAll tmp acc))

omit [DecidableEq K] in
theorem closed_halveStep (x q tmp : K) : (halveStep x q tmp).Closed := by
  simp [halveStep, halveBody, moveU, incR, whileNE, whileTop, popR, peekR, pushC,
    Prog.Closed, Prog.FreeBelow]

omit [DecidableEq K] in
theorem closed_emitField (x q tmp acc : K) : (emitField x q tmp acc).Closed := by
  simp [emitField, halveStep, halveBody, moveAll, moveU, incR, whileNE, whileTop, mv, popR,
    pushR, peekR, pushC, Prog.Closed, Prog.FreeBelow]

/-- Inner-loop state of `halveStep` after `j` iterations (value `v`; `tmp = bit false :: t`
at the start, its top turned into `bit true` by the last iteration when `v` is odd). -/
def halveSt (S : K → List Sym) (x q tmp : K) (v : ℕ) (t : List Sym) (j : ℕ) : K → List Sym :=
  upd3 S x q tmp (una (v - 2 * j)) (una (min j (v / 2)))
    ((if v < 2 * j then Sym.bit true else Sym.bit false) :: t)

theorem runs_halveBody {x q tmp : K} (hxq : x ≠ q) (hxt : x ≠ tmp) (hqt : q ≠ tmp)
    (S : K → List Sym) (v : ℕ) (t : List Sym) (j : ℕ) (hj : j < (v + 1) / 2) :
    Runs (halveBody x q tmp) (halveSt S x q tmp v t j) (halveSt S x q tmp v t (j + 1))
      (fun _ => True) 5 := by
  have hx : halveSt S x q tmp v t j x = una (v - 2 * j) := upd3_app_x hxq hxt
  have hq : halveSt S x q tmp v t j q = una (min j (v / 2)) := upd3_app_q hqt
  have hpop := runs_true (runs_popR x (halveSt S x q tmp v t j))
  rw [hx, tail_una] at hpop
  have hS1x : Function.update (halveSt S x q tmp v t j) x (una (v - 2 * j - 1)) x =
      una (v - 2 * j - 1) := Function.update_self _ _ _
  unfold halveBody
  refine runs_seq' (T2 := 2 + 2) hpop ?_ (by omega)
  rcases Nat.lt_or_ge (v - 2 * j) 2 with hlt | hge
  · -- the last token (`v = 2 j + 1`): mark the bit as odd
    have h0 : v - 2 * j - 1 = 0 := by omega
    refine runs_peekIte (fun hc => ?_) (fun _ => ?_)
    · exfalso
      rw [hS1x, h0] at hc
      simp [isSomeB] at hc
    · have ht : Function.update (halveSt S x q tmp v t j) x (una (v - 2 * j - 1)) tmp =
          Sym.bit false :: t := by
        rw [Function.update_of_ne (Ne.symm hxt), halveSt, upd3_app_t,
          if_neg (show ¬ v < 2 * j by omega)]
      have p1 := runs_true (runs_popR tmp
        (Function.update (halveSt S x q tmp v t j) x (una (v - 2 * j - 1))))
      rw [ht, List.tail_cons] at p1
      have p2 := runs_pushC tmp (Sym.bit true) (Function.update
        (Function.update (halveSt S x q tmp v t j) x (una (v - 2 * j - 1))) tmp t)
      rw [Function.update_self, Function.update_idem] at p2
      refine runs_seq' p1 (runs_weak p2 ?_ le_rfl) (by omega)
      unfold halveSt
      rw [upd3_x hxq hxt, upd3_t]
      exact upd3_congr (by congr 1 <;> omega) (by congr 1 <;> omega)
        (by rw [if_pos (show v < 2 * (j + 1) by omega)])
  · -- two tokens: pop the second one and count it in `q`
    have hpos : v - 2 * j - 1 = (v - 2 * j - 2) + 1 := by omega
    refine runs_peekIte (fun _ => ?_) (fun hc => ?_)
    · have p1 := runs_true (runs_popR x
        (Function.update (halveSt S x q tmp v t j) x (una (v - 2 * j - 1))))
      rw [Function.update_self, tail_una, Function.update_idem] at p1
      have p2 := runs_incR q (Function.update (halveSt S x q tmp v t j) x
        (una (v - 2 * j - 1 - 1))) (min j (v / 2))
        (by rw [Function.update_of_ne (Ne.symm hxq), hq])
      refine runs_seq' p1 (runs_weak p2 ?_ le_rfl) (by omega)
      unfold halveSt
      rw [upd3_x hxq hxt, upd3_q hqt]
      exact upd3_congr (by congr 1 <;> omega) (by congr 1 <;> omega)
        (by rw [if_neg (show ¬ v < 2 * j by omega), if_neg (show ¬ v < 2 * (j + 1) by omega)])
    · exfalso
      rw [hS1x, hpos, una_succ] at hc
      simp [isSomeB] at hc

/-- **Halving step.** `x = una v` becomes `una (v / 2)`; `bit (v % 2 = 1)` is pushed on `tmp`;
`q` is empty before and after. -/
theorem runs_halveStep {x q tmp : K} (hxq : x ≠ q) (hxt : x ≠ tmp) (hqt : q ≠ tmp)
    (S : K → List Sym) (v : ℕ) (hx : S x = una v) (hq : S q = []) :
    Runs (halveStep x q tmp) S
      (Function.update (Function.update S x (una (v / 2))) tmp
        (Sym.bit (decide (v % 2 = 1)) :: S tmp)) (fun _ => True) (6 * v + 9) := by
  have h1 := runs_pushC tmp (Sym.bit false) S
  have h0 : halveSt S x q tmp v (S tmp) 0 = Function.update S tmp (Sym.bit false :: S tmp) := by
    funext k
    simp only [halveSt, upd3, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  have hloop := runs_whileNE (k := x) (p := halveBody x q tmp) (halveSt S x q tmp v (S tmp)) 5
    ((v + 1) / 2)
    (fun i hi => by rw [halveSt, upd3_app_x hxq hxt]; exact una_ne_nil (by omega))
    (by rw [halveSt, upd3_app_x hxq hxt, show v - 2 * ((v + 1) / 2) = 0 by omega, una_zero])
    (fun i hi => runs_halveBody hxq hxt hqt S v (S tmp) i hi)
  rw [h0] at hloop
  have hmv := runs_moveU (Ne.symm hxq) (halveSt S x q tmp v (S tmp) ((v + 1) / 2)) (v / 2) 0
    (by rw [halveSt, upd3_app_q hqt]; congr 1 <;> omega)
    (by rw [halveSt, upd3_app_x hxq hxt, show v - 2 * ((v + 1) / 2) = 0 by omega])
  unfold halveStep
  refine runs_seq' h1 (runs_seq' hloop (runs_weak hmv ?_ le_rfl) le_rfl) (by omega)
  have eB : (if v < 2 * ((v + 1) / 2) then Sym.bit true else Sym.bit false) =
      Sym.bit (decide (v % 2 = 1)) := by
    by_cases h : v % 2 = 1
    · rw [if_pos (show v < 2 * ((v + 1) / 2) by omega), decide_eq_true h]
    · rw [if_neg (show ¬ v < 2 * ((v + 1) / 2) by omega), decide_eq_false h]
  unfold halveSt
  rw [eB, Nat.zero_add]
  funext k
  simp only [upd3, Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

/-- Outer-loop state of `emitField` after `i` halvings. -/
def emitSt (S : K → List Sym) (x tmp acc : K) (n i : ℕ) : K → List Sym :=
  Function.update (Function.update (Function.update S acc (Sym.mark :: S acc)) x
    (una (n / 2 ^ i))) tmp ((natSyms n).take i).reverse

/-- **Field emission.** The register `x = una n` is consumed (`x := []`), the accumulator gains
`natSyms n ++ [mark]`; the scratch stacks `q`, `tmp` are empty before and after. -/
theorem runs_emitField {x q tmp acc : K} (hxq : x ≠ q) (hxt : x ≠ tmp) (hxa : x ≠ acc)
    (hqt : q ≠ tmp) (hqa : q ≠ acc) (hta : tmp ≠ acc) (S : K → List Sym) (n : ℕ)
    (hx : S x = una n) (hq : S q = []) (ht : S tmp = []) :
    Runs (emitField x q tmp acc) S
      (Function.update (Function.update S x []) acc (natSyms n ++ Sym.mark :: S acc))
      (fun _ => True) (7 * (n + 1) ^ 2) := by
  have h1 := runs_pushC acc Sym.mark S
  have hz : n / 2 ^ (natSyms n).length = 0 := by
    by_contra h
    exact lt_irrefl _ ((div_pow_ne_zero_iff n _).1 h)
  have e0 : emitSt S x tmp acc n 0 = Function.update S acc (Sym.mark :: S acc) := by
    funext k
    simp only [emitSt, Function.update_apply, pow_zero, Nat.div_one, List.take_zero,
      List.reverse_nil]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  have hloop := runs_whileNE (k := x) (p := halveStep x q tmp) (emitSt S x tmp acc n)
    (6 * n + 9) (natSyms n).length
    (fun i hi => by
      rw [emitSt, Function.update_of_ne hxt, Function.update_self]
      exact una_ne_nil ((div_pow_ne_zero_iff n i).2 hi))
    (by rw [emitSt, Function.update_of_ne hxt, Function.update_self, hz, una_zero])
    (fun i hi => by
      have hxi : emitSt S x tmp acc n i x = una (n / 2 ^ i) := by
        rw [emitSt, Function.update_of_ne hxt, Function.update_self]
      have hqi : emitSt S x tmp acc n i q = [] := by
        rw [emitSt, Function.update_of_ne hqt, Function.update_of_ne hxq.symm,
          Function.update_of_ne hqa, hq]
      have hti : emitSt S x tmp acc n i tmp = ((natSyms n).take i).reverse := by
        rw [emitSt, Function.update_self]
      have hs := runs_halveStep hxq hxt hqt (emitSt S x tmp acc n i) (n / 2 ^ i) hxi hqi
      refine runs_weak hs ?_ (by have := Nat.div_le_self n (2 ^ i); omega)
      rw [hti, ← take_succ_reverse_natSyms n i hi, Nat.div_div_eq_div_mul, ← pow_succ]
      unfold emitSt
      rw [upd4 hxt])
  rw [e0] at hloop
  have hNx : (natSyms n).take (natSyms n).length = natSyms n := List.take_length
  have hmv := runs_moveAll hta (emitSt S x tmp acc n (natSyms n).length)
  have htN : emitSt S x tmp acc n (natSyms n).length tmp = (natSyms n).reverse := by
    rw [emitSt, Function.update_self, hNx]
  have haN : emitSt S x tmp acc n (natSyms n).length acc = Sym.mark :: S acc := by
    rw [emitSt, Function.update_of_ne hta.symm, Function.update_of_ne hxa.symm,
      Function.update_self]
  rw [htN, haN, List.reverse_reverse, List.length_reverse] at hmv
  unfold emitField
  refine runs_seq' h1 (runs_seq' hloop (runs_weak hmv ?_ le_rfl) le_rfl)
    (emit_cost_le n _ (natSyms_length_le n))
  funext k
  simp only [emitSt, Function.update_apply, hz, una_zero]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

end Generic

end SubNLogN.Machine.Walsh.PosPermSchedAux.PSIO
