/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedIO
import SubNLogN.Machine.Walsh.PosPermSchedTbl

/-!
# Schedule compiler IO, decoding (`Machine/Walsh/PosPermSchedIODec.lean`)

Generic decoding programs (any stack type `K`, `SProg K`) of the runtime schedule compiler
(`PosPermSchedStmt`, `PosPermLeaf.lean`), with exact `Runs` rules. A field is
`natSyms v ++ [mark]` (bits least significant first, then a mark):

* `skipFld src bk`: move one field from `src` onto the backup stack `bk` (cost `4 |bits| + 4`);
* `decFld src bk dst pw t`: the same move, and the unary register `dst` gains `v`; the bits are
  weighted by a power-of-two register `pw` (doubled after each bit). Cost `22 (v + 1)^2`.

Every popped symbol is pushed on the backup stack, so the source can be restored exactly by
`moveAll bk src` (`PosPermSchedIO.lean`).

**Scope (honest summary).** Definitions and proved rules; no contract is proved here.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.PSIO

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine Computability
open SubNLogN.Machine.Walsh.PosPermSchedAux

/-- Register test: the peeked symbol is a bit. -/
def isBitB : Option Sym → Bool
  | some (Sym.bit _) => true
  | _ => false

/-- Register test: the peeked symbol is the bit `1`. -/
def isOneB : Option Sym → Bool
  | some (Sym.bit true) => true
  | _ => false

/-! ## Pure lemmas -/

theorem two_pow_le_of_lt (v i : ℕ) (hi : i < (natSyms v).length) : 2 ^ i ≤ v := by
  have h := (div_pow_ne_zero_iff v i).2 hi
  have h2 : 0 < v / 2 ^ i := Nat.pos_of_ne_zero h
  rw [Nat.div_pos_iff] at h2
  exact h2.2

theorem two_pow_le (v i : ℕ) (hi : i ≤ (natSyms v).length) : 2 ^ i ≤ 2 * v + 1 := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · have h := two_pow_le_of_lt v (i - 1) (by omega)
    have e : 2 ^ i = 2 * 2 ^ (i - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega

theorem mod_two_pow_succ' (v i : ℕ) :
    v % 2 ^ (i + 1) = v % 2 ^ i + (if decide (v / 2 ^ i % 2 = 1) then 2 ^ i else 0) := by
  rw [Nat.mod_pow_succ]
  by_cases h : v / 2 ^ i % 2 = 1
  · simp [h]
  · have h0 : v / 2 ^ i % 2 = 0 := by omega
    simp [h0]

theorem mod_two_pow_length (v : ℕ) : v % 2 ^ (natSyms v).length = v := by
  apply Nat.mod_eq_of_lt
  have hz : v / 2 ^ (natSyms v).length = 0 := by
    by_contra h
    exact lt_irrefl _ ((div_pow_ne_zero_iff v _).1 h)
  rw [Nat.div_eq_zero_iff] at hz
  rcases hz with h | h
  · exact absurd h (pow_pos (by norm_num : (0 : ℕ) < 2) _).ne'
  · exact h

theorem rev_field (v : ℕ) (X : List Sym) :
    (natSyms v ++ [Sym.mark]).reverse ++ X = Sym.mark :: ((natSyms v).reverse ++ X) := by
  simp

/-- The arithmetic of the `decFld` cost bound. -/
theorem dec_cost_le (v L : ℕ) (hL : L ≤ v) (h2 : 2 ^ L ≤ 2 * v + 1) :
    1 + (L * (v * 19 + 14 + 2) + 2 + (2 + (2 ^ L * 3 + 2))) ≤ 22 * (v + 1) ^ 2 := by
  have h1 : L * (v * 19 + 14 + 2) ≤ v * (v * 19 + 14 + 2) := Nat.mul_le_mul_right _ hL
  have h3 : v * (v * 19 + 14 + 2) = 19 * (v * v) + 16 * v := by ring
  have h4 : (v + 1) ^ 2 = v * v + 2 * v + 1 := by ring
  rw [h3] at h1
  rw [h4]
  omega

section Generic

variable {K : Type} [DecidableEq K]

/-- Four updates overridden by four updates of the same stacks. -/
theorem upd_override4 {S : K → List Sym} {a b c d : K} (A B C D A' B' C' D' : List Sym) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update S a A) b B) c C) d D)
      a A') b B') c C') d D' =
    Function.update (Function.update (Function.update (Function.update S a A') b B') c C')
      d D' := by
  funext k
  simp only [Function.update_apply]
  split_ifs <;> rfl

/-! ## Doubling a unary register -/

/-- `pw := 2 pw` via the empty scratch `t`. -/
def dblU (pw t : K) : SProg K := .seq (moveU pw t) (forDown t (.seq (incR pw) (incR pw)))

omit [DecidableEq K] in
theorem closed_dblU (pw t : K) : (dblU pw t).Closed := by
  simp [dblU, moveU, forDown, incR, whileNE, whileTop, popR, peekR, pushC, Prog.Closed,
    Prog.FreeBelow]

theorem runs_dblU {pw t : K} (hne : pw ≠ t) (S : K → List Sym) (a : ℕ) (hp : S pw = una a)
    (ht : S t = []) :
    Runs (dblU pw t) S (Function.update S pw (una (2 * a))) (fun _ => True) (a * 9 + 4) := by
  have h1 := runs_moveU hne S a 0 hp ht
  have h2 := runs_forDown (c := t) (p := .seq (incR pw) (incR pw))
    (fun i => Function.update S pw (una (2 * i))) 2 a
    (fun i _ => by
      have i1 := runs_incR pw (Function.update (Function.update S pw (una (2 * i))) t
        (una (a - 1 - i))) (2 * i) (by rw [Function.update_of_ne hne, Function.update_self])
      have i2 := runs_incR pw (Function.update (Function.update (Function.update S pw
        (una (2 * i))) t (una (a - 1 - i))) pw (una (2 * i + 1))) (2 * i + 1)
        (by rw [Function.update_self])
      have e : 2 * i + 1 + 1 = 2 * (i + 1) := by ring
      rw [e] at i2
      refine runs_seq' i1 (runs_weak i2 ?_ le_rfl) le_rfl
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all))
  have e1 : Function.update (Function.update S pw []) t (una (0 + a)) =
      Function.update (Function.update S pw (una (2 * 0))) t (una a) := by
    rw [Nat.zero_add, Nat.mul_zero, una_zero]
  have e2 : Function.update (Function.update S pw (una (2 * a))) t [] =
      Function.update S pw (una (2 * a)) := by
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  rw [e1] at h1
  rw [e2] at h2
  exact runs_seq' h1 h2 (by omega)

/-! ## One bit -/

/-- One bit of a field: move it to the backup `bk`; if it is a one, `dst := dst + pw`;
then `pw := 2 pw`. -/
def decBit (src bk dst pw t : K) : SProg K :=
  .seq (.seq (peekR src) (.ite isOneB (.seq (mv src bk) (copyU pw dst t)) (mv src bk)))
    (dblU pw t)

theorem runs_decBit {src bk dst pw t : K} (hnd : [src, bk, dst, pw, t].Nodup)
    (S : K → List Sym) (b : Bool) (L : List Sym) (e p : ℕ) (hs : S src = Sym.bit b :: L)
    (hd : S dst = una e) (hp : S pw = una p) (ht : S t = []) :
    Runs (decBit src bk dst pw t) S
      (Function.update (Function.update (Function.update (Function.update S src L) bk
        (Sym.bit b :: S bk)) dst (una (e + if b then p else 0))) pw (una (2 * p)))
      (fun _ => True) (p * 19 + 14) := by
  have hd' : src ≠ bk ∧ src ≠ dst ∧ src ≠ pw ∧ src ≠ t ∧ bk ≠ dst ∧ bk ≠ pw ∧ bk ≠ t ∧
      dst ≠ pw ∧ dst ≠ t ∧ pw ≠ t := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
    tauto
  obtain ⟨h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ := hd'
  have hmv := runs_mv h12 S (Sym.bit b) L hs
  have e1 : Function.update (Function.update S src L) bk (Sym.bit b :: S bk) pw = una p := by
    rw [Function.update_of_ne h24.symm, Function.update_of_ne h14.symm, hp]
  have e2 : Function.update (Function.update S src L) bk (Sym.bit b :: S bk) dst = una e := by
    rw [Function.update_of_ne h23.symm, Function.update_of_ne h13.symm, hd]
  have e3 : Function.update (Function.update S src L) bk (Sym.bit b :: S bk) t = [] := by
    rw [Function.update_of_ne h25.symm, Function.update_of_ne h15.symm, ht]
  have hbr : Runs (.seq (peekR src) (.ite isOneB (.seq (mv src bk) (copyU pw dst t))
      (mv src bk))) S (Function.update (Function.update (Function.update S src L) bk
        (Sym.bit b :: S bk)) dst (una (e + if b then p else 0))) (fun _ => True)
      (p * 10 + 8 + 2) := by
    cases b with
    | true =>
      refine runs_peekIte (fun _ => ?_) (fun hc => ?_)
      · have hcp := runs_copyU h34.symm h45 h35 _ p e e1 e2 e3
        exact runs_seq' hmv (runs_weak hcp (by rw [if_pos rfl]) le_rfl) (by omega)
      · rw [hs] at hc
        exact absurd hc (by simp [isOneB])
    | false =>
      refine runs_peekIte (fun hc => ?_) (fun _ => ?_)
      · rw [hs] at hc
        exact absurd hc (by simp [isOneB])
      · refine runs_weak hmv ?_ (by omega)
        rw [if_neg Bool.false_ne_true, Nat.add_zero, ← e2, Function.update_eq_self]
  have hdb := runs_dblU h45 (Function.update (Function.update (Function.update S src L) bk
    (Sym.bit b :: S bk)) dst (una (e + if b then p else 0))) p
    (by rw [Function.update_of_ne h34.symm, e1]) (by rw [Function.update_of_ne h35.symm, e3])
  unfold decBit
  exact runs_seq' hbr hdb (by omega)

/-! ## Skipping a field -/

/-- Move one field (bits, then its mark) from `src` onto the backup `bk`. -/
def skipFld (src bk : K) : SProg K := .seq (whileTop src isBitB (mv src bk)) (mv src bk)

omit [DecidableEq K] in
theorem closed_skipFld (src bk : K) : (skipFld src bk).Closed := by
  simp [skipFld, whileTop, mv, popR, pushR, peekR, Prog.Closed, Prog.FreeBelow]

theorem runs_skipFld {src bk : K} (hne : src ≠ bk) (S : K → List Sym) (v : ℕ) (R : List Sym)
    (hs : S src = natSyms v ++ Sym.mark :: R) :
    Runs (skipFld src bk) S (Function.update (Function.update S src R) bk
      ((natSyms v ++ [Sym.mark]).reverse ++ S bk)) (fun _ => True)
      ((natSyms v).length * 4 + 4) := by
  have hloop := runs_whileTop (k := src) (c := isBitB) (p := mv src bk)
    (fun i => Function.update (Function.update S src ((natSyms v).drop i ++ Sym.mark :: R)) bk
      (((natSyms v).take i).reverse ++ S bk)) 2 (natSyms v).length
    (fun i hi => by
      rw [Function.update_of_ne hne, Function.update_self, List.drop_eq_getElem_cons hi,
        natSyms_getElem v i hi]
      rfl)
    (by
      rw [Function.update_of_ne hne, Function.update_self, List.drop_length, List.nil_append]
      rfl)
    (fun i hi => by
      have hm := runs_mv hne (Function.update (Function.update S src
        ((natSyms v).drop i ++ Sym.mark :: R)) bk (((natSyms v).take i).reverse ++ S bk))
        (natSyms v)[i] ((natSyms v).drop (i + 1) ++ Sym.mark :: R)
        (by rw [Function.update_of_ne hne, Function.update_self, List.drop_eq_getElem_cons hi,
          List.cons_append])
      refine runs_weak hm ?_ le_rfl
      rw [upd4 hne, Function.update_self, List.take_add_one, List.getElem?_eq_getElem hi,
        Option.toList_some, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.cons_append])
  have e0 : Function.update (Function.update S src ((natSyms v).drop 0 ++ Sym.mark :: R)) bk
      (((natSyms v).take 0).reverse ++ S bk) = S := by
    rw [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append, ← hs,
      Function.update_eq_self, Function.update_eq_self]
  rw [e0, List.drop_length, List.take_length, List.nil_append] at hloop
  have hm := runs_mv hne (Function.update (Function.update S src (Sym.mark :: R)) bk
    ((natSyms v).reverse ++ S bk)) Sym.mark R
    (by rw [Function.update_of_ne hne, Function.update_self])
  unfold skipFld
  refine runs_seq' hloop (runs_weak hm ?_ le_rfl) (by omega)
  rw [upd4 hne, Function.update_self, rev_field]

/-! ## Decoding a field into a unary register -/

/-- Decode one field from `src` (moved onto the backup `bk`), adding its value to `dst`;
`pw` (power of two) and `t` are scratch, empty before and after. -/
def decFld (src bk dst pw t : K) : SProg K :=
  .seq (incR pw) (.seq (whileTop src isBitB (decBit src bk dst pw t))
    (.seq (mv src bk) (clearU pw)))

omit [DecidableEq K] in
theorem closed_decFld (src bk dst pw t : K) : (decFld src bk dst pw t).Closed := by
  simp [decFld, decBit, dblU, copyU, moveU, forDown, clearU, incR, whileNE, whileTop, mv,
    popR, pushR, peekR, pushC, Prog.Closed, Prog.FreeBelow]

/-- Loop state of `decFld` after `i` bits. -/
def decSt (S : K → List Sym) (src bk dst pw : K) (v : ℕ) (R : List Sym) (e i : ℕ) :
    K → List Sym :=
  Function.update (Function.update (Function.update (Function.update S src
    ((natSyms v).drop i ++ Sym.mark :: R)) bk (((natSyms v).take i).reverse ++ S bk)) dst
    (una (e + v % 2 ^ i))) pw (una (2 ^ i))

/-- **Field decoding.** The field `natSyms v ++ [mark]` on top of `src` is moved onto `bk`
(reversed), and `v` is added to the unary register `dst`. -/
theorem runs_decFld {src bk dst pw t : K} (hnd : [src, bk, dst, pw, t].Nodup)
    (S : K → List Sym) (v e : ℕ) (R : List Sym) (hs : S src = natSyms v ++ Sym.mark :: R)
    (hd : S dst = una e) (hp : S pw = []) (ht : S t = []) :
    Runs (decFld src bk dst pw t) S
      (Function.update (Function.update (Function.update S src R) bk
        ((natSyms v ++ [Sym.mark]).reverse ++ S bk)) dst (una (e + v)))
      (fun _ => True) (22 * (v + 1) ^ 2) := by
  have hd' : src ≠ bk ∧ src ≠ dst ∧ src ≠ pw ∧ src ≠ t ∧ bk ≠ dst ∧ bk ≠ pw ∧ bk ≠ t ∧
      dst ≠ pw ∧ dst ≠ t ∧ pw ≠ t := by
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      List.nodup_nil] at hnd'
    tauto
  obtain ⟨h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ := hd'
  have dsrc : ∀ i, decSt S src bk dst pw v R e i src = (natSyms v).drop i ++ Sym.mark :: R := by
    intro i
    rw [decSt, Function.update_of_ne h14, Function.update_of_ne h13, Function.update_of_ne h12,
      Function.update_self]
  have dbk : ∀ i, decSt S src bk dst pw v R e i bk = ((natSyms v).take i).reverse ++ S bk := by
    intro i
    rw [decSt, Function.update_of_ne h24, Function.update_of_ne h23, Function.update_self]
  have ddst : ∀ i, decSt S src bk dst pw v R e i dst = una (e + v % 2 ^ i) := by
    intro i
    rw [decSt, Function.update_of_ne h34, Function.update_self]
  have dpw : ∀ i, decSt S src bk dst pw v R e i pw = una (2 ^ i) := by
    intro i
    rw [decSt, Function.update_self]
  have dt : ∀ i, decSt S src bk dst pw v R e i t = [] := by
    intro i
    rw [decSt, Function.update_of_ne h45.symm, Function.update_of_ne h35.symm,
      Function.update_of_ne h25.symm, Function.update_of_ne h15.symm, ht]
  have h1 := runs_incR pw S 0 hp
  have e0 : decSt S src bk dst pw v R e 0 = Function.update S pw (una (0 + 1)) := by
    funext k
    simp only [decSt, Function.update_apply, List.drop_zero, List.take_zero, List.reverse_nil,
      List.nil_append, pow_zero, Nat.mod_one, Nat.add_zero, Nat.zero_add]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  have hloop := runs_whileTop (k := src) (c := isBitB) (p := decBit src bk dst pw t)
    (decSt S src bk dst pw v R e) (v * 19 + 14) (natSyms v).length
    (fun i hi => by
      rw [dsrc, List.drop_eq_getElem_cons hi, natSyms_getElem v i hi]
      rfl)
    (by
      rw [dsrc, List.drop_length, List.nil_append]
      rfl)
    (fun i hi => by
      have hb := runs_decBit hnd (decSt S src bk dst pw v R e i) (decide (v / 2 ^ i % 2 = 1))
        ((natSyms v).drop (i + 1) ++ Sym.mark :: R) (e + v % 2 ^ i) (2 ^ i)
        (by rw [dsrc, List.drop_eq_getElem_cons hi, natSyms_getElem v i hi, List.cons_append])
        (ddst i) (dpw i) (dt i)
      refine runs_weak hb ?_ (by have := two_pow_le_of_lt v i hi; omega)
      have eb : Sym.bit (decide (v / 2 ^ i % 2 = 1)) :: (((natSyms v).take i).reverse ++ S bk) =
          ((natSyms v).take (i + 1)).reverse ++ S bk := by
        rw [take_succ_reverse_natSyms v i hi]
        rfl
      have ed : e + v % 2 ^ i + (if decide (v / 2 ^ i % 2 = 1) then 2 ^ i else 0) =
          e + v % 2 ^ (i + 1) := by
        rw [mod_two_pow_succ', Nat.add_assoc]
      rw [dbk, eb, ed, ← pow_succ']
      unfold decSt
      exact upd_override4 _ _ _ _ _ _ _ _)
  rw [e0] at hloop
  have hm := runs_mv h12 (decSt S src bk dst pw v R e (natSyms v).length) Sym.mark R
    (by rw [dsrc, List.drop_length, List.nil_append])
  have hc := runs_clearU pw (Function.update (Function.update
    (decSt S src bk dst pw v R e (natSyms v).length) src R) bk
    (Sym.mark :: decSt S src bk dst pw v R e (natSyms v).length bk)) (2 ^ (natSyms v).length)
    (by rw [Function.update_of_ne h24.symm, Function.update_of_ne h14.symm, dpw])
  unfold decFld
  refine runs_seq' h1 (runs_seq' hloop (runs_seq' hm (runs_weak hc ?_ le_rfl) le_rfl) le_rfl)
    (dec_cost_le v _ (natSyms_length_le v) (two_pow_le v _ le_rfl))
  rw [dbk, List.take_length, rev_field]
  funext k
  simp only [decSt, Function.update_apply, mod_two_pow_length]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

/-! ## The header `permHdr P d r w k m` -/

theorem hdr_step (f : ℕ) (fs : List ℕ) (X : List Sym) :
    hdrSyms (f :: fs) ++ X = natSyms f ++ Sym.mark :: (hdrSyms fs ++ X) := by
  rw [hdrSyms_cons, List.append_assoc, List.cons_append]

theorem bk_step (f : ℕ) (fs : List ℕ) :
    (natSyms f ++ [Sym.mark]).reverse ++ (hdrSyms fs).reverse =
      (hdrSyms (fs ++ [f])).reverse := by
  rw [hdrSyms_append, hdrSyms_cons, hdrSyms_nil]
  simp only [List.reverse_append]

omit [DecidableEq K] in
theorem nodup5 {a b c d e : K} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : a ≠ e)
    (h5 : b ≠ c) (h6 : b ≠ d) (h7 : b ≠ e) (h8 : c ≠ d) (h9 : c ≠ e) (h10 : d ≠ e) :
    [a, b, c, d, e].Nodup := by
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- Canonical state of the header decoder: `h`, `bk` and three unary registers overwritten. -/
def hst (S : K → List Sym) (h bk dR KR mR : K) (hv bkv : List Sym) (a b c : ℕ) :
    K → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update S h hv)
    bk bkv) dR (una a)) KR (una b)) mR (una c)

/-- **Header decoder.** Skip `P`; decode `d` into `dR`; skip `r`, `w`; decode `k` into `KR` and
`m` into `mR`; every symbol goes to the backup `bk`, which is finally moved back onto `h`. -/
def decHdr (h bk dR KR mR pw t : K) : SProg K :=
  .seq (skipFld h bk) (.seq (decFld h bk dR pw t) (.seq (skipFld h bk) (.seq (skipFld h bk)
    (.seq (decFld h bk KR pw t) (.seq (decFld h bk mR pw t) (moveAll bk h))))))

omit [DecidableEq K] in
theorem closed_decHdr (h bk dR KR mR pw t : K) : (decHdr h bk dR KR mR pw t).Closed := by
  simp [decHdr, skipFld, decFld, decBit, dblU, copyU, moveU, moveAll, forDown, clearU, incR,
    whileNE, whileTop, mv, popR, pushR, peekR, pushC, Prog.Closed, Prog.FreeBelow]

section HstGlue

variable {S : K → List Sym} {h bk dR KR mR : K}

theorem hst_init (hnd : [h, bk, dR, KR, mR].Nodup) (hd : S dR = []) (hK : S KR = [])
    (hm : S mR = []) (hv bkv : List Sym) :
    Function.update (Function.update S h hv) bk bkv = hst S h bk dR KR mR hv bkv 0 0 0 := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
  unfold hst
  funext x
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

theorem hst_skip (hnd : [h, bk, dR, KR, mR].Nodup) (hv bkv hv' bkv' : List Sym) (a b c : ℕ) :
    Function.update (Function.update (hst S h bk dR KR mR hv bkv a b c) h hv') bk bkv' =
      hst S h bk dR KR mR hv' bkv' a b c := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
  unfold hst
  funext x
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

theorem hst_dR (hnd : [h, bk, dR, KR, mR].Nodup) (hv bkv hv' bkv' : List Sym) (a b c a' : ℕ) :
    Function.update (Function.update (Function.update (hst S h bk dR KR mR hv bkv a b c) h hv')
      bk bkv') dR (una a') = hst S h bk dR KR mR hv' bkv' a' b c := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
  unfold hst
  funext x
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

theorem hst_KR (hnd : [h, bk, dR, KR, mR].Nodup) (hv bkv hv' bkv' : List Sym) (a b c b' : ℕ) :
    Function.update (Function.update (Function.update (hst S h bk dR KR mR hv bkv a b c) h hv')
      bk bkv') KR (una b') = hst S h bk dR KR mR hv' bkv' a b' c := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
  unfold hst
  funext x
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

theorem hst_mR (hnd : [h, bk, dR, KR, mR].Nodup) (hv bkv hv' bkv' : List Sym) (a b c c' : ℕ) :
    Function.update (Function.update (Function.update (hst S h bk dR KR mR hv bkv a b c) h hv')
      bk bkv') mR (una c') = hst S h bk dR KR mR hv' bkv' a b c' := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
  unfold hst
  funext x
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

theorem hst_final (hnd : [h, bk, dR, KR, mR].Nodup) (hb : S bk = []) (hv bkv : List Sym)
    (a b c : ℕ) :
    Function.update (Function.update (hst S h bk dR KR mR hv bkv a b c) bk []) h (S h) =
      Function.update (Function.update (Function.update S dR (una a)) KR (una b)) mR
        (una c) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
  unfold hst
  funext x
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

end HstGlue

/-- **Header decoding.** From `h = permHdr P d r w k m ++ hrest` and empty `bk`, `dR`, `KR`,
`mR`, `pw`, `t`: the registers become `una d`, `una k`, `una m`; everything else (in particular
`h`) is restored exactly. -/
theorem runs_decHdr {h bk dR KR mR pw t : K} (hnd : [h, bk, dR, KR, mR, pw, t].Nodup)
    (S : K → List Sym) (P d r w k m : ℕ) (hrest : List Sym)
    (hh : S h = permHdr P d r w k m ++ hrest) (hb : S bk = []) (hd : S dR = [])
    (hK : S KR = []) (hm : S mR = []) (hp : S pw = []) (ht : S t = []) :
    Runs (decHdr h bk dR KR mR pw t) S
      (Function.update (Function.update (Function.update S dR (una d)) KR (una k)) mR (una m))
      (fun _ => True)
      (22 * ((d + 1) ^ 2 + (k + 1) ^ 2 + (m + 1) ^ 2) + 8 * (permHdr P d r w k m).length +
        14) := by
  have hd' : h ≠ bk ∧ h ≠ dR ∧ h ≠ KR ∧ h ≠ mR ∧ h ≠ pw ∧ h ≠ t ∧ bk ≠ dR ∧ bk ≠ KR ∧
      bk ≠ mR ∧ bk ≠ pw ∧ bk ≠ t ∧ dR ≠ KR ∧ dR ≠ mR ∧ dR ≠ pw ∧ dR ≠ t ∧ KR ≠ mR ∧ KR ≠ pw ∧
      KR ≠ t ∧ mR ≠ pw ∧ mR ≠ t ∧ pw ≠ t := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
    tauto
  obtain ⟨a1, a2, a3, a4, a5, a6, b2, b3, b4, b5, b6, c3, c4, c5, c6, d4, d5, d6, e5, e6, f6⟩ :=
    hd'
  have hs_h : ∀ hv bkv a b c, hst S h bk dR KR mR hv bkv a b c h = hv := by
    intro hv bkv a b c
    rw [hst, Function.update_of_ne a4, Function.update_of_ne a3, Function.update_of_ne a2,
      Function.update_of_ne a1, Function.update_self]
  have hs_bk : ∀ hv bkv a b c, hst S h bk dR KR mR hv bkv a b c bk = bkv := by
    intro hv bkv a b c
    rw [hst, Function.update_of_ne b4, Function.update_of_ne b3, Function.update_of_ne b2,
      Function.update_self]
  have hs_dR : ∀ hv bkv a b c, hst S h bk dR KR mR hv bkv a b c dR = una a := by
    intro hv bkv a b c
    rw [hst, Function.update_of_ne c4, Function.update_of_ne c3, Function.update_self]
  have hs_KR : ∀ hv bkv a b c, hst S h bk dR KR mR hv bkv a b c KR = una b := by
    intro hv bkv a b c
    rw [hst, Function.update_of_ne d4, Function.update_self]
  have hs_mR : ∀ hv bkv a b c, hst S h bk dR KR mR hv bkv a b c mR = una c := by
    intro hv bkv a b c
    rw [hst, Function.update_self]
  have hs_pw : ∀ hv bkv a b c, hst S h bk dR KR mR hv bkv a b c pw = [] := by
    intro hv bkv a b c
    rw [hst, Function.update_of_ne e5.symm, Function.update_of_ne d5.symm,
      Function.update_of_ne c5.symm, Function.update_of_ne b5.symm,
      Function.update_of_ne a5.symm, hp]
  have hs_t : ∀ hv bkv a b c, hst S h bk dR KR mR hv bkv a b c t = [] := by
    intro hv bkv a b c
    rw [hst, Function.update_of_ne e6.symm, Function.update_of_ne d6.symm,
      Function.update_of_ne c6.symm, Function.update_of_ne b6.symm,
      Function.update_of_ne a6.symm, ht]
  have hnd5 : [h, bk, dR, KR, mR].Nodup := nodup5 a1 a2 a3 a4 b2 b3 b4 c3 c4 d4
  -- the seven steps
  have s1 := runs_skipFld a1 S P (hdrSyms [d, r, w, k, m] ++ hrest) (by rw [hh, permHdr, hdr_step])
  have e1 : (natSyms P ++ [Sym.mark]).reverse ++ S bk = (hdrSyms [P]).reverse := by
    rw [hb, List.append_nil, hdrSyms_cons, hdrSyms_nil]
  rw [e1, hst_init hnd5 hd hK hm] at s1
  have s2 := runs_decFld (nodup5 a1 a2 a5 a6 b2 b5 b6 c5 c6 f6)
    (hst S h bk dR KR mR (hdrSyms [d, r, w, k, m] ++ hrest) (hdrSyms [P]).reverse 0 0 0) d 0
    (hdrSyms [r, w, k, m] ++ hrest) (by rw [hs_h, hdr_step]) (hs_dR _ _ _ _ _) (hs_pw _ _ _ _ _)
    (hs_t _ _ _ _ _)
  rw [hs_bk, bk_step, Nat.zero_add, hst_dR hnd5] at s2
  have s3 := runs_skipFld a1
    (hst S h bk dR KR mR (hdrSyms [r, w, k, m] ++ hrest) (hdrSyms ([P] ++ [d])).reverse d 0 0) r
    (hdrSyms [w, k, m] ++ hrest) (by rw [hs_h, hdr_step])
  rw [hs_bk, bk_step, hst_skip hnd5] at s3
  have s4 := runs_skipFld a1
    (hst S h bk dR KR mR (hdrSyms [w, k, m] ++ hrest) (hdrSyms ([P] ++ [d] ++ [r])).reverse d 0 0)
    w (hdrSyms [k, m] ++ hrest) (by rw [hs_h, hdr_step])
  rw [hs_bk, bk_step, hst_skip hnd5] at s4
  have s5 := runs_decFld (nodup5 a1 a3 a5 a6 b3 b5 b6 d5 d6 f6)
    (hst S h bk dR KR mR (hdrSyms [k, m] ++ hrest) (hdrSyms ([P] ++ [d] ++ [r] ++ [w])).reverse
      d 0 0) k 0 (hdrSyms [m] ++ hrest) (by rw [hs_h, hdr_step]) (hs_KR _ _ _ _ _)
    (hs_pw _ _ _ _ _) (hs_t _ _ _ _ _)
  rw [hs_bk, bk_step, Nat.zero_add, hst_KR hnd5] at s5
  have s6 := runs_decFld (nodup5 a1 a4 a5 a6 b4 b5 b6 e5 e6 f6)
    (hst S h bk dR KR mR (hdrSyms [m] ++ hrest)
      (hdrSyms ([P] ++ [d] ++ [r] ++ [w] ++ [k])).reverse d k 0) m 0 hrest
    (by rw [hs_h, hdr_step, hdrSyms_nil, List.nil_append]) (hs_mR _ _ _ _ _) (hs_pw _ _ _ _ _)
    (hs_t _ _ _ _ _)
  rw [hs_bk, bk_step, Nat.zero_add, hst_mR hnd5] at s6
  have s7 := runs_moveAll a1.symm (hst S h bk dR KR mR hrest
    (hdrSyms ([P] ++ [d] ++ [r] ++ [w] ++ [k] ++ [m])).reverse d k m)
  have e7 : hdrSyms ([P] ++ [d] ++ [r] ++ [w] ++ [k] ++ [m]) ++ hrest = S h := by
    rw [hh]
    rfl
  rw [hs_bk, hs_h, List.reverse_reverse, List.length_reverse, e7, hst_final hnd5 hb] at s7
  have hlen : (permHdr P d r w k m).length = (natSyms P).length + (natSyms d).length +
      (natSyms r).length + (natSyms w).length + (natSyms k).length + (natSyms m).length + 6 := by
    simp only [permHdr, hdrSyms, List.flatMap_cons, List.flatMap_nil, List.length_append,
      List.length_cons, List.length_nil]
    omega
  have hlen' : (hdrSyms ([P] ++ [d] ++ [r] ++ [w] ++ [k] ++ [m])).length =
      (permHdr P d r w k m).length := rfl
  unfold decHdr
  refine runs_seq' s1 (runs_seq' s2 (runs_seq' s3 (runs_seq' s4
    (runs_seq' s5 (runs_seq' s6 s7 le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) ?_
  rw [hlen']
  omega

/-! ## The π table -/

theorem utab_length_le (l : List ℕ) (B : ℕ) (hB : ∀ a ∈ l, a ≤ B) :
    (utab l).length ≤ l.length * (B + 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [utab_cons, List.length_append, length_una, List.length_cons, List.length_cons, add_mul,
      one_mul]
    have h1 := hB a (by simp)
    have h2 := ih (fun x hx => hB x (by simp [hx]))
    omega

theorem utab_rev_step (l : List ℕ) (a : ℕ) :
    Sym.sep :: (una a ++ (utab l).reverse) = (utab (l ++ [a])).reverse := by
  rw [utab_append, utab_cons, utab_nil, List.reverse_append]
  simp [reverse_una]

/-- Loop state of the table decoder after `i` entries (the counter excluded). -/
def tF (S : K → List Sym) (pi bk Trev : K) (l : List ℕ) (prest : List Sym) (i : ℕ) :
    K → List Sym :=
  Function.update (Function.update (Function.update S pi (hdrSyms (l.drop i) ++ prest)) bk
    (hdrSyms (l.take i)).reverse) Trev (utab (l.take i)).reverse

/-- **Table decoder.** `c := n` (copy of the register `nR`); `n` times: decode a field of `pi`
into `u` (backup `bk`), push `una u ++ [sep]` reversed on `Trev`; then `T := utab l ++ T` and
`pi` is restored from `bk`. -/
def decTbl (pi bk nR T u c Trev pw t : K) : SProg K :=
  .seq (copyU nR c t) (.seq (forDown c (.seq (decFld pi bk u pw t)
    (.seq (moveAll u Trev) (pushC Trev Sym.sep)))) (.seq (moveAll Trev T) (moveAll bk pi)))

omit [DecidableEq K] in
theorem closed_decTbl (pi bk nR T u c Trev pw t : K) :
    (decTbl pi bk nR T u c Trev pw t).Closed := by
  simp [decTbl, decFld, decBit, dblU, copyU, moveU, moveAll, forDown, clearU, incR,
    whileNE, whileTop, mv, popR, pushR, peekR, pushC, Prog.Closed, Prog.FreeBelow]

section TblGlue

variable {S : K → List Sym} {pi bk Trev c : K}

theorem tF_zero (h12 : pi ≠ bk) (h13 : pi ≠ Trev) (h23 : bk ≠ Trev) (l : List ℕ)
    (prest : List Sym) (hpi : S pi = hdrSyms l ++ prest) (hb : S bk = []) (hr : S Trev = []) :
    tF S pi bk Trev l prest 0 = S := by
  unfold tF
  funext x
  simp only [Function.update_apply, List.drop_zero, List.take_zero, hdrSyms_nil, utab_nil,
    List.reverse_nil]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

theorem tbl_glue {u : K} {l : List ℕ} {prest : List Sym} {i : ℕ}
    (hnd : [pi, bk, Trev, c, u].Nodup) (hu : S u = []) (C R' B' U V V' : List Sym) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (tF S pi bk Trev l prest i) c C) pi R') bk B') u U) u [])
      Trev V) Trev V' =
    Function.update (Function.update (Function.update (Function.update S pi R') bk B') Trev V')
      c C := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
  unfold tF
  funext x
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

theorem tbl_final {T : K} {l : List ℕ} {prest : List Sym} {i : ℕ}
    (hnd : [pi, bk, Trev, c, T].Nodup) (hb : S bk = []) (hr : S Trev = []) (hc : S c = [])
    (X : List Sym) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (tF S pi bk Trev l prest i) c []) Trev []) T X) bk []) pi (S pi) =
      Function.update S T X := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
  unfold tF
  funext x
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

end TblGlue

/-- The arithmetic of the `decTbl` cost bound. -/
theorem tbl_cost_le (n B U H : ℕ) (hU : U ≤ n * (B + 1)) :
    n * 10 + 6 + (n * (22 * (B + 1) ^ 2 + 4 * B + 3 + 3) + 2 + (U * 4 + 2 + (H * 4 + 2))) ≤
      n * (22 * (B + 1) ^ 2 + 8 * B + 20) + 4 * H + 12 := by
  have e1 : n * (22 * (B + 1) ^ 2 + 4 * B + 3 + 3) =
      22 * (n * (B + 1) ^ 2) + 4 * (n * B) + 6 * n := by ring
  have e2 : n * (22 * (B + 1) ^ 2 + 8 * B + 20) = 22 * (n * (B + 1) ^ 2) + 8 * (n * B) + 20 * n := by
    ring
  have e3 : n * (B + 1) = n * B + n := by ring
  rw [e1, e2]
  rw [e3] at hU
  omega

/-- **Table decoding.** From `pi = hdrSyms l ++ prest` (entries `≤ B`), `nR = una l.length` and
empty scratch: `T := utab l ++ T`; everything else (in particular `pi`, `nR`) is restored. -/
theorem runs_decTbl {pi bk nR T u c Trev pw t : K}
    (hnd : [pi, bk, nR, T, u, c, Trev, pw, t].Nodup) (S : K → List Sym) (l : List ℕ) (B : ℕ)
    (hB : ∀ a ∈ l, a ≤ B) (prest : List Sym) (hpi : S pi = hdrSyms l ++ prest)
    (hn : S nR = una l.length) (hb : S bk = []) (hu : S u = []) (hc : S c = [])
    (hr : S Trev = []) (hp : S pw = []) (ht : S t = []) :
    Runs (decTbl pi bk nR T u c Trev pw t) S (Function.update S T (utab l ++ S T))
      (fun _ => True)
      (l.length * (22 * (B + 1) ^ 2 + 8 * B + 20) + 4 * (hdrSyms l).length + 12) := by
  have hd' : pi ≠ bk ∧ pi ≠ nR ∧ pi ≠ T ∧ pi ≠ u ∧ pi ≠ c ∧ pi ≠ Trev ∧ pi ≠ pw ∧ pi ≠ t ∧
      bk ≠ nR ∧ bk ≠ T ∧ bk ≠ u ∧ bk ≠ c ∧ bk ≠ Trev ∧ bk ≠ pw ∧ bk ≠ t ∧
      nR ≠ T ∧ nR ≠ u ∧ nR ≠ c ∧ nR ≠ Trev ∧ nR ≠ pw ∧ nR ≠ t ∧
      T ≠ u ∧ T ≠ c ∧ T ≠ Trev ∧ T ≠ pw ∧ T ≠ t ∧ u ≠ c ∧ u ≠ Trev ∧ u ≠ pw ∧ u ≠ t ∧
      c ≠ Trev ∧ c ≠ pw ∧ c ≠ t ∧ Trev ≠ pw ∧ Trev ≠ t ∧ pw ≠ t := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
    tauto
  obtain ⟨n12, n13, n14, n15, n16, n17, n18, n19, n23, n24, n25, n26, n27, n28, n29,
    n34, n35, n36, n37, n38, n39, n45, n46, n47, n48, n49, n56, n57, n58, n59,
    n67, n68, n69, n78, n79, n89⟩ := hd'
  have hnd5 : [pi, bk, Trev, c, u].Nodup :=
    nodup5 n12 n17 n16 n15 n27 n26 n25 n67.symm n57.symm n56.symm
  have hnd5' : [pi, bk, Trev, c, T].Nodup :=
    nodup5 n12 n17 n16 n14 n27 n26 n24 n67.symm n47.symm n46.symm
  have h0 := runs_copyU n36 n39 n69 S l.length 0 hn hc ht
  rw [Nat.zero_add] at h0
  have hf := runs_forDown (c := c)
    (p := .seq (decFld pi bk u pw t) (.seq (moveAll u Trev) (pushC Trev Sym.sep)))
    (tF S pi bk Trev l prest) (22 * (B + 1) ^ 2 + 4 * B + 3) l.length (fun i hi => by
      have hil : i < l.length := hi
      have Gpi : Function.update (tF S pi bk Trev l prest i) c (una (l.length - 1 - i)) pi =
          hdrSyms (l.drop i) ++ prest := by
        rw [Function.update_of_ne n16, tF, Function.update_of_ne n17, Function.update_of_ne n12,
          Function.update_self]
      have Gbk : Function.update (tF S pi bk Trev l prest i) c (una (l.length - 1 - i)) bk =
          (hdrSyms (l.take i)).reverse := by
        rw [Function.update_of_ne n26, tF, Function.update_of_ne n27, Function.update_self]
      have GTr : Function.update (tF S pi bk Trev l prest i) c (una (l.length - 1 - i)) Trev =
          (utab (l.take i)).reverse := by
        rw [Function.update_of_ne n67.symm, tF, Function.update_self]
      have Gu : Function.update (tF S pi bk Trev l prest i) c (una (l.length - 1 - i)) u =
          una 0 := by
        rw [Function.update_of_ne n56, tF, Function.update_of_ne n57,
          Function.update_of_ne n25.symm, Function.update_of_ne n15.symm, hu, una_zero]
      have Gpw : Function.update (tF S pi bk Trev l prest i) c (una (l.length - 1 - i)) pw =
          [] := by
        rw [Function.update_of_ne n68.symm, tF, Function.update_of_ne n78.symm,
          Function.update_of_ne n28.symm, Function.update_of_ne n18.symm, hp]
      have Gt : Function.update (tF S pi bk Trev l prest i) c (una (l.length - 1 - i)) t =
          [] := by
        rw [Function.update_of_ne n69.symm, tF, Function.update_of_ne n79.symm,
          Function.update_of_ne n29.symm, Function.update_of_ne n19.symm, ht]
      have b1 := runs_decFld (nodup5 n12 n15 n18 n19 n25 n28 n29 n58 n59 n89)
        (Function.update (tF S pi bk Trev l prest i) c (una (l.length - 1 - i))) l[i] 0
        (hdrSyms (l.drop (i + 1)) ++ prest)
        (by rw [Gpi, List.drop_eq_getElem_cons hil, hdr_step]) Gu Gpw Gt
      rw [Gbk, Nat.zero_add, bk_step, ← List.take_succ_eq_append_getElem hil] at b1
      have b2 := runs_moveAll n57 (Function.update (Function.update (Function.update
        (Function.update (tF S pi bk Trev l prest i) c (una (l.length - 1 - i))) pi
        (hdrSyms (l.drop (i + 1)) ++ prest)) bk (hdrSyms (l.take (i + 1))).reverse) u (una l[i]))
      rw [Function.update_self, Function.update_of_ne n57.symm, Function.update_of_ne n27.symm,
        Function.update_of_ne n17.symm, GTr, reverse_una, length_una] at b2
      have b3 := runs_pushC Trev Sym.sep (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (tF S pi bk Trev l prest i) c
        (una (l.length - 1 - i))) pi (hdrSyms (l.drop (i + 1)) ++ prest)) bk
        (hdrSyms (l.take (i + 1))).reverse) u (una l[i])) u []) Trev
        (una l[i] ++ (utab (l.take i)).reverse))
      rw [Function.update_self, utab_rev_step, ← List.take_succ_eq_append_getElem hil] at b3
      have hli : l[i] ≤ B := hB _ (by simp)
      have hsq : (l[i] + 1) ^ 2 ≤ (B + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      exact runs_seq' b1 (runs_seq' b2 (runs_weak b3 (tbl_glue hnd5 hu _ _ _ _ _ _) le_rfl)
        le_rfl) (by omega))
  rw [tF_zero n12 n17 n27 l prest hpi hb hr] at hf
  have yTr : Function.update (tF S pi bk Trev l prest l.length) c [] Trev = (utab l).reverse := by
    rw [Function.update_of_ne n67.symm, tF, Function.update_self, List.take_length]
  have yT : Function.update (tF S pi bk Trev l prest l.length) c [] T = S T := by
    rw [Function.update_of_ne n46, tF, Function.update_of_ne n47, Function.update_of_ne n24.symm,
      Function.update_of_ne n14.symm]
  have m1 := runs_moveAll n47.symm (Function.update (tF S pi bk Trev l prest l.length) c [])
  rw [yTr, yT, List.reverse_reverse, List.length_reverse] at m1
  have zbk : Function.update (Function.update (Function.update (tF S pi bk Trev l prest l.length)
      c []) Trev []) T (utab l ++ S T) bk = (hdrSyms l).reverse := by
    rw [Function.update_of_ne n24, Function.update_of_ne n27, Function.update_of_ne n26, tF,
      Function.update_of_ne n27, Function.update_self, List.take_length]
  have zpi : Function.update (Function.update (Function.update (tF S pi bk Trev l prest l.length)
      c []) Trev []) T (utab l ++ S T) pi = prest := by
    rw [Function.update_of_ne n14, Function.update_of_ne n17, Function.update_of_ne n16, tF,
      Function.update_of_ne n17, Function.update_of_ne n12, Function.update_self,
      List.drop_length, hdrSyms_nil, List.nil_append]
  have m2 := runs_moveAll n12.symm (Function.update (Function.update (Function.update
    (tF S pi bk Trev l prest l.length) c []) Trev []) T (utab l ++ S T))
  rw [zbk, zpi, List.reverse_reverse, List.length_reverse, ← hpi, tbl_final hnd5' hb hr hc] at m2
  unfold decTbl
  exact runs_seq' h0 (runs_seq' hf (runs_seq' m1 m2 le_rfl) le_rfl)
    (tbl_cost_le _ _ _ _ (utab_length_le l B hB))

/-- **π-table decoding** (`runs_decTbl` for `l = [π 0, …, π (m-1)]`, `B = m`). -/
theorem runs_decPi {pi bk nR T u c Trev pw t : K}
    (hnd : [pi, bk, nR, T, u, c, Trev, pw, t].Nodup) (S : K → List Sym) {m : ℕ}
    (π : Fin m → Fin m) (prest : List Sym) (hpi : S pi = permSyms π ++ prest)
    (hn : S nR = una m) (hb : S bk = []) (hu : S u = []) (hc : S c = []) (hr : S Trev = [])
    (hp : S pw = []) (ht : S t = []) :
    Runs (decTbl pi bk nR T u c Trev pw t) S
      (Function.update S T (utab (List.ofFn fun p => (π p : ℕ)) ++ S T)) (fun _ => True)
      (m * (22 * (m + 1) ^ 2 + 8 * m + 20) + 4 * (permSyms π).length + 12) := by
  have h := runs_decTbl hnd S (List.ofFn fun p => (π p : ℕ)) m
    (fun a ha => by
      obtain ⟨p, rfl⟩ := List.mem_ofFn.1 ha
      exact (π p).isLt.le)
    prest hpi (by rw [List.length_ofFn]; exact hn) hb hu hc hr hp ht
  rw [List.length_ofFn] at h
  exact h

end Generic

end SubNLogN.Machine.Walsh.PosPermSchedAux.PSIO
