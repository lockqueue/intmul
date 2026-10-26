/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedOps

/-!
# Schedule compiler, part 3 (`Machine/Walsh/PosPermSchedTbl.lean`): unary tables

A table of naturals `[a₀, a₁, …]` on one stack is `utab l = una a₀ ++ sep :: una a₁ ++ sep :: …`
(entry `0` on top). Programs and exact `Runs` rules:
* `drainTo src dst` (move every symbol; reverses), `moveToks`/`copyToks` (move the leading tokens),
  `skipEntry` (move one entry with its separator);
* `lookup T U i o lc tmp`: `o := o + l[i]` (the table is restored);
* `pushEntry T v`: `T := una v ++ sep :: T`, `v := 0`; `popEntry T v`: `v := v + head`, drop it.

**Scope (honest summary).** Definitions and proved rules only; no contract is proved here.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

open TMFw TMFw.Lib TMFw.Contracts

/-- One table entry. -/
def ent (a : ℕ) : List Sym := una a ++ [Sym.sep]

/-- A table of naturals, entry `0` on top. -/
def utab (l : List ℕ) : List Sym := l.flatMap ent

@[simp] theorem utab_nil : utab [] = [] := rfl

theorem utab_cons (a : ℕ) (l : List ℕ) : utab (a :: l) = una a ++ Sym.sep :: utab l := by
  simp [utab, ent]

theorem utab_append (l₁ l₂ : List ℕ) : utab (l₁ ++ l₂) = utab l₁ ++ utab l₂ := by
  simp [utab]

theorem reverse_una (n : ℕ) : (una n).reverse = una n := List.reverse_replicate

theorem tail_una_append (n : ℕ) (L : List Sym) : (una (n + 1) ++ L).tail = una n ++ L := rfl

/-- Register test: the register holds the token. -/
def isTokB (r : Option Sym) : Bool := decide (r = some tok)

section Tbl

variable {K : Type} [DecidableEq K]

/-! ## Moving symbols -/

/-- Move every symbol of `src` onto `dst`. -/
def drainTo (src dst : K) : SProg K := whileNE src (mv src dst)

theorem runs_drainTo {src dst : K} (hne : src ≠ dst) (S : K → List Sym) :
    Runs (drainTo src dst) S
      (Function.update (Function.update S src []) dst ((S src).reverse ++ S dst))
      (fun _ => True) ((S src).length * 4 + 2) := by
  have h := runs_whileNE (k := src) (p := mv src dst)
    (fun i => Function.update (Function.update S src ((S src).drop i))
      dst (((S src).take i).reverse ++ S dst)) 2 (S src).length
    (fun i hi => by
      rw [Function.update_of_ne hne, Function.update_self]
      intro h
      have := congrArg List.length h
      simp at this
      omega)
    (by rw [Function.update_of_ne hne, Function.update_self, List.drop_length])
    (fun i hi => by
      have hget : (S src).drop i = (S src)[i] :: (S src).drop (i + 1) :=
        List.drop_eq_getElem_cons hi
      have hm := runs_mv hne (Function.update (Function.update S src ((S src).drop i))
        dst (((S src).take i).reverse ++ S dst)) (S src)[i] ((S src).drop (i + 1))
        (by rw [Function.update_of_ne hne, Function.update_self, hget])
      refine runs_weak hm ?_ le_rfl
      rw [List.take_succ_eq_append_getElem hi, List.reverse_append]
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all))
  have e0 : Function.update (Function.update S src ((S src).drop 0)) dst
      (((S src).take 0).reverse ++ S dst) = S := by
    simp
  rw [e0, List.take_length, List.drop_length] at h
  exact runs_weak h rfl (by omega)

/-- Move the leading tokens of `src` onto `dst`. -/
def moveToks (src dst : K) : SProg K := whileTop src isTokB (mv src dst)

theorem runs_moveToks {src dst : K} (hne : src ≠ dst) (S : K → List Sym) (a : ℕ)
    (R : List Sym) (hR : R.head? ≠ some tok) (hS : S src = una a ++ R) :
    Runs (moveToks src dst) S
      (Function.update (Function.update S src R) dst (una a ++ S dst))
      (fun _ => True) (a * 4 + 2) := by
  have h := runs_whileTop (k := src) (c := isTokB) (p := mv src dst)
    (fun i => Function.update (Function.update S src (una (a - i) ++ R)) dst (una i ++ S dst))
    2 a
    (fun i hi => by
      rw [Function.update_of_ne hne, Function.update_self]
      obtain ⟨j, hj⟩ : ∃ j, a - i = j + 1 := ⟨a - i - 1, by omega⟩
      rw [hj]
      rfl)
    (by
      rw [Function.update_of_ne hne, Function.update_self, Nat.sub_self, una_zero,
        List.nil_append]
      simp only [isTokB, decide_eq_false_iff_not]
      exact hR)
    (fun i hi => by
      obtain ⟨j, hj⟩ : ∃ j, a - i = j + 1 := ⟨a - i - 1, by omega⟩
      have hm := runs_mv hne (Function.update (Function.update S src (una (a - i) ++ R)) dst
        (una i ++ S dst)) tok (una j ++ R)
        (by rw [Function.update_of_ne hne, Function.update_self, hj]; rfl)
      refine runs_weak hm ?_ le_rfl
      have e1 : a - (i + 1) = j := by omega
      rw [e1]
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all) <;> rfl)
  have e0 : Function.update (Function.update S src (una (a - 0) ++ R)) dst (una 0 ++ S dst) =
      S := by
    rw [Nat.sub_zero, ← hS, una_zero, List.nil_append, Function.update_eq_self,
      Function.update_eq_self]
  rw [e0, Nat.sub_self, una_zero, List.nil_append] at h
  exact h

/-- Move the leading tokens of `src` onto `dst`, counting them into the register `o`. -/
def copyToks (src dst o : K) : SProg K := whileTop src isTokB (.seq (mv src dst) (incR o))

theorem runs_copyToks {src dst o : K} (h1 : src ≠ dst) (h2 : src ≠ o) (h3 : dst ≠ o)
    (S : K → List Sym) (a c : ℕ) (R : List Sym) (hR : R.head? ≠ some tok)
    (hS : S src = una a ++ R) (ho : S o = una c) :
    Runs (copyToks src dst o) S
      (Function.update (Function.update (Function.update S src R) dst (una a ++ S dst)) o
        (una (c + a))) (fun _ => True) (a * 5 + 2) := by
  have h := runs_whileTop (k := src) (c := isTokB) (p := .seq (mv src dst) (incR o))
    (fun i => Function.update (Function.update (Function.update S src (una (a - i) ++ R)) dst
      (una i ++ S dst)) o (una (c + i))) 3 a
    (fun i hi => by
      rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self]
      obtain ⟨j, hj⟩ : ∃ j, a - i = j + 1 := ⟨a - i - 1, by omega⟩
      rw [hj]
      rfl)
    (by
      rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self, Nat.sub_self,
        una_zero, List.nil_append]
      simp only [isTokB, decide_eq_false_iff_not]
      exact hR)
    (fun i hi => by
      obtain ⟨j, hj⟩ : ∃ j, a - i = j + 1 := ⟨a - i - 1, by omega⟩
      have hm := runs_mv h1 (Function.update (Function.update (Function.update S src
        (una (a - i) ++ R)) dst (una i ++ S dst)) o (una (c + i))) tok (una j ++ R)
        (by rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self, hj]; rfl)
      have hi2 := runs_incR o (Function.update (Function.update (Function.update (Function.update
        (Function.update S src (una (a - i) ++ R)) dst (una i ++ S dst)) o (una (c + i))) src
        (una j ++ R)) dst (tok :: (Function.update (Function.update (Function.update S src
        (una (a - i) ++ R)) dst (una i ++ S dst)) o (una (c + i))) dst)) (c + i)
        (by rw [Function.update_of_ne h3.symm, Function.update_of_ne h2.symm,
          Function.update_self])
      refine runs_seq' hm (runs_weak hi2 ?_ le_rfl) le_rfl
      have e1 : a - (i + 1) = j := by omega
      rw [e1]
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all) <;> rfl)
  have e0 : Function.update (Function.update (Function.update S src (una (a - 0) ++ R)) dst
      (una 0 ++ S dst)) o (una (c + 0)) = S := by
    rw [Nat.sub_zero, ← hS, una_zero, List.nil_append, Nat.add_zero, ← ho,
      Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  rw [e0, Nat.sub_self, una_zero, List.nil_append] at h
  exact h

/-! ## Entries -/

/-- Move one entry (tokens and separator) of `src` onto `dst`. -/
def skipEntry (src dst : K) : SProg K := .seq (moveToks src dst) (mv src dst)

theorem runs_skipEntry {src dst : K} (hne : src ≠ dst) (S : K → List Sym) (a : ℕ)
    (R : List Sym) (hS : S src = una a ++ Sym.sep :: R) :
    Runs (skipEntry src dst) S
      (Function.update (Function.update S src R) dst (Sym.sep :: una a ++ S dst))
      (fun _ => True) (a * 4 + 4) := by
  have h1 := runs_moveToks hne S a (Sym.sep :: R) (by simp) hS
  have h2 := runs_mv hne (Function.update (Function.update S src (Sym.sep :: R)) dst
    (una a ++ S dst)) Sym.sep R (by rw [Function.update_of_ne hne, Function.update_self])
  refine runs_seq' h1 (runs_weak h2 ?_ le_rfl) (by omega)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

/-- `T := una v ++ sep :: T`, `v := 0`. -/
def pushEntry (T v : K) : SProg K := .seq (pushC T Sym.sep) (forDown v (pushC T tok))

theorem runs_pushEntry {T v : K} (hne : T ≠ v) (S : K → List Sym) (a : ℕ) (hv : S v = una a) :
    Runs (pushEntry T v) S
      (Function.update (Function.update S T (una a ++ Sym.sep :: S T)) v [])
      (fun _ => True) (a * 4 + 3) := by
  have h1 := runs_pushC T Sym.sep S
  have h2 := runs_forDown (c := v) (p := pushC T tok)
    (fun i => Function.update S T (una i ++ Sym.sep :: S T)) 1 a (fun i _ => by
      have hp := runs_pushC T tok (Function.update (Function.update S T (una i ++ Sym.sep :: S T))
        v (una (a - 1 - i)))
      refine runs_weak hp ?_ le_rfl
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all) <;> rfl)
  have e0 : Function.update (Function.update S T (una 0 ++ Sym.sep :: S T)) v (una a) =
      Function.update S T (Sym.sep :: S T) := by
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  rw [e0] at h2
  exact runs_seq' h1 h2 (by omega)

/-- `v := v + (head entry of T)` and drop that entry. -/
def popEntry (T v : K) : SProg K := .seq (whileTop T isTokB (.seq (popR T) (incR v))) (popR T)

theorem runs_popEntry {T v : K} (hne : T ≠ v) (S : K → List Sym) (a c : ℕ) (R : List Sym)
    (hT : S T = una a ++ Sym.sep :: R) (hv : S v = una c) :
    Runs (popEntry T v) S (Function.update (Function.update S T R) v (una (c + a)))
      (fun _ => True) (a * 4 + 3) := by
  have h := runs_whileTop (k := T) (c := isTokB) (p := .seq (popR T) (incR v))
    (fun i => Function.update (Function.update S T (una (a - i) ++ Sym.sep :: R)) v
      (una (c + i))) 2 a
    (fun i hi => by
      rw [Function.update_of_ne hne, Function.update_self]
      obtain ⟨j, hj⟩ : ∃ j, a - i = j + 1 := ⟨a - i - 1, by omega⟩
      rw [hj]
      rfl)
    (by
      rw [Function.update_of_ne hne, Function.update_self, Nat.sub_self, una_zero,
        List.nil_append]
      rfl)
    (fun i hi => by
      obtain ⟨j, hj⟩ : ∃ j, a - i = j + 1 := ⟨a - i - 1, by omega⟩
      have e1 : a - (i + 1) = j := by omega
      rw [hj, e1]
      have hp := runs_popR T (Function.update (Function.update S T (una (j + 1) ++ Sym.sep :: R))
        v (una (c + i)))
      rw [Function.update_of_ne hne, Function.update_self, tail_una_append] at hp
      have hi2 := runs_incR v (Function.update (Function.update (Function.update S T
        (una (j + 1) ++ Sym.sep :: R)) v (una (c + i))) T (una j ++ Sym.sep :: R)) (c + i)
        (by rw [Function.update_of_ne hne.symm, Function.update_self])
      refine runs_seq' (runs_true hp) (runs_weak hi2 ?_ le_rfl) le_rfl
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all) <;> rfl)
  have e0 : Function.update (Function.update S T (una (a - 0) ++ Sym.sep :: R)) v
      (una (c + 0)) = S := by
    rw [Nat.sub_zero, Nat.add_zero, ← hT, ← hv, Function.update_eq_self, Function.update_eq_self]
  rw [e0, Nat.sub_self, una_zero, List.nil_append] at h
  have h2 := runs_popR T (Function.update (Function.update S T (Sym.sep :: R)) v (una (c + a)))
  rw [Function.update_of_ne hne, Function.update_self] at h2
  refine runs_seq' h (runs_weak (runs_true h2) ?_ le_rfl) (by omega)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

/-! ## Lookup -/

/-- `o := o + l[i]` for the table `T = utab l` (restored); `U lc tmp` empty before and after. -/
def lookup (T U i o lc tmp : K) : SProg K :=
  .seq (copyU i lc tmp) (.seq (forDown lc (skipEntry T U)) (.seq (copyToks T U o) (drainTo U T)))

theorem una_le_utab_length (l : List ℕ) (j : ℕ) (hj : j < l.length) : l[j] ≤ (utab l).length := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    rw [utab_cons]
    cases j with
    | zero => simp
    | succ j =>
      have := ih j (by simpa using hj)
      simp only [List.getElem_cons_succ, List.length_append, length_una, List.length_cons]
      omega

theorem runs_lookup {T U i o lc tmp : K} (hnd : [T, U, i, o, lc, tmp].Nodup) (S : K → List Sym)
    (l : List ℕ) (j c : ℕ) (hj : j < l.length) (hT : S T = utab l) (hi : S i = una j)
    (ho : S o = una c) (hU : S U = []) (hlc : S lc = []) (htmp : S tmp = []) :
    Runs (lookup T U i o lc tmp) S (Function.update S o (una (c + l[j])))
      (fun _ => True) ((j + 1) * ((utab l).length + 1) * 30) := by
  have hd : T ≠ U ∧ T ≠ i ∧ T ≠ o ∧ T ≠ lc ∧ T ≠ tmp ∧ U ≠ i ∧ U ≠ o ∧ U ≠ lc ∧ U ≠ tmp ∧
      i ≠ o ∧ i ≠ lc ∧ i ≠ tmp ∧ o ≠ lc ∧ o ≠ tmp ∧ lc ≠ tmp := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil] at hnd
    tauto
  obtain ⟨hTU, hTi, hTo, hTl, hTt, hUi, hUo, hUl, hUt, hio, hil, hit, hol, hot, hlt⟩ := hd
  set L := (utab l).length with hL
  have c1 := runs_copyU hil hit hlt S j 0 hi hlc htmp
  have c2 := runs_forDown (c := lc) (p := skipEntry T U)
    (fun k => Function.update (Function.update S T (utab (l.drop k))) U
      ((utab (l.take k)).reverse)) (L * 4 + 4) j (fun k hk => by
      have hkl : k < l.length := by omega
      have hdrop : utab (l.drop k) = una l[k] ++ Sym.sep :: utab (l.drop (k + 1)) := by
        rw [List.drop_eq_getElem_cons hkl, utab_cons]
      have hs := runs_skipEntry hTU (Function.update (Function.update (Function.update S T
        (utab (l.drop k))) U ((utab (l.take k)).reverse)) lc (una (j - 1 - k))) l[k]
        (utab (l.drop (k + 1))) (by
          rw [Function.update_of_ne hTl, Function.update_of_ne hTU, Function.update_self, hdrop])
      refine runs_weak hs ?_ (by have := una_le_utab_length l k hkl; omega)
      have htake : (utab (l.take (k + 1))).reverse =
          Sym.sep :: una l[k] ++ (utab (l.take k)).reverse := by
        rw [List.take_succ_eq_append_getElem hkl, utab_append, utab_cons, utab_nil,
          List.reverse_append]
        simp [reverse_una]
      rw [htake]
      funext x
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all))
  have e2 : Function.update (Function.update (Function.update S T (utab (l.drop 0))) U
      ((utab (l.take 0)).reverse)) lc (una j) = Function.update S lc (una (0 + j)) := by
    funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  rw [e2] at c2
  have hdropj : utab (l.drop j) = una l[j] ++ Sym.sep :: utab (l.drop (j + 1)) := by
    rw [List.drop_eq_getElem_cons hj, utab_cons]
  have c3 := runs_copyToks hTU hTo hUo (Function.update (Function.update (Function.update S T
    (utab (l.drop j))) U ((utab (l.take j)).reverse)) lc []) l[j] c
    (Sym.sep :: utab (l.drop (j + 1))) (by simp)
    (by rw [Function.update_of_ne hTl, Function.update_of_ne hTU, Function.update_self, hdropj])
    (by rw [Function.update_of_ne hol, Function.update_of_ne hUo.symm,
      Function.update_of_ne hTo.symm, ho])
  have c4 := runs_drainTo hTU.symm (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update S T (utab (l.drop j))) U
    ((utab (l.take j)).reverse)) lc []) T (Sym.sep :: utab (l.drop (j + 1)))) U
    (una l[j] ++ (Function.update (Function.update (Function.update S T (utab (l.drop j))) U
    ((utab (l.take j)).reverse)) lc []) U)) o (una (c + l[j])))
  have hfin : (utab (l.take j)) ++ (una l[j] ++ Sym.sep :: utab (l.drop (j + 1))) = utab l := by
    rw [← hdropj, ← utab_append, List.take_append_drop]
  refine runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_weak c4 ?_ le_rfl) le_rfl) le_rfl) ?_
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all [reverse_una])
  · have hlj := una_le_utab_length l j hj
    have hU : ((Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S T (utab (l.drop j))) U ((utab (l.take j)).reverse)) lc
        []) T (Sym.sep :: utab (l.drop (j + 1)))) U (una l[j] ++ (Function.update
        (Function.update (Function.update S T (utab (l.drop j))) U ((utab (l.take j)).reverse))
        lc []) U)) o (una (c + l[j]))) U).length ≤ L := by
      simp only [Function.update_of_ne hUo, Function.update_self, Function.update_of_ne hUl,
        List.length_append, length_una, List.length_reverse]
      have := congrArg List.length hfin
      simp only [List.length_append, length_una, List.length_cons] at this
      omega
    have e1 : (j + 1) * (L + 1) * 30 = j * L * 30 + j * 30 + L * 30 + 30 := by ring
    have e2 : j * (L * 4 + 4 + 3) = j * L * 4 + j * 7 := by ring
    omega

end Tbl

end SubNLogN.Machine.Walsh.PosPermSchedAux
