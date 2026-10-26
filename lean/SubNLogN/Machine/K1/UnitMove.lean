/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.SplitMapTop

/-!
# K5 kit: generic block moves (`K1/UnitMove.lean`)

**Scope (honest summary).** Generic proved rules (any stack type `K`), no contract:
* `runsM_cdMvRec`: a block of `N` records (`N` = the counter on `ns`) moves from `src` to `dst`
  (records arrive reversed, block orientation flips);
* `runsM_cdMvRev`: a block of `N` reversed records moves from `src` to `dst`, restoring the
  records' order;
* `runsM_unaryB`: the depth stack receives `b` unary tokens above a `mark`;
  `runsM_clearDep`: they are removed again;
* `RunsM.ite_pos` / `RunsM.ite_neg`: register tests.
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

section Generic

variable {K M : Type} [DecidableEq K]

theorem RunsM.ite_pos {c : Option Sym × M → Bool} {p p' : KP K M} {m m' : M}
    {S S' : K → List Sym} {T : ℕ} (hc : ∀ o, c (o, m) = true) (h : RunsM p m S m' S' T) :
    RunsM (.ite c p p') m S m' S' (T + 1) := by
  intro o
  obtain ⟨o', t, ht, e⟩ := h o
  exact ⟨o', t + 1, by omega, Eval.ite_true (hc o) e⟩

theorem RunsM.ite_neg {c : Option Sym × M → Bool} {p p' : KP K M} {m m' : M}
    {S S' : K → List Sym} {T : ℕ} (hc : ∀ o, c (o, m) = false) (h : RunsM p' m S m' S' T) :
    RunsM (.ite c p p') m S m' S' (T + 1) := by
  intro o
  obtain ⟨o', t, ht, e⟩ := h o
  exact ⟨o', t + 1, by omega, Eval.ite_false (hc o) e⟩

/-- **Block move.** `N` records (`N` = the counter on `ns`) move from `src` to `dst`. -/
theorem runsM_cdMvRec {ns cnt tmp src dst : K} (hnc : ns ≠ cnt) (hnt : ns ≠ tmp)
    (hct : cnt ≠ tmp) (hsd : src ≠ dst) (hsc : src ≠ cnt) (hdc : dst ≠ cnt) (_hns : ns ≠ src)
    (_hnd : ns ≠ dst) (N : ℕ) (Rn : List Sym) (hRn : TermOK Rn) (w : List (List Bool)) (R : List Sym)
    (hw : N ≤ w.length) (m : M) (S : K → List Sym) (hsrc : S src = arrSyms w ++ R)
    (hN : S ns = natSyms N ++ Rn) :
    RunsM (cdMove ns cnt tmp (mvRec src dst)) m S m
      (Function.update (Function.update S src (arrSyms (w.drop N) ++ R)) dst
        ((arrSyms (w.take N)).reverse ++ S dst))
      (incSeqCost 6 8 N + 3 * vol (w.take N) + 2 * N + 7 * bitLen N + 12) := by
  set St : ℕ → K → List Sym := fun i => Function.update (Function.update S src
    (arrSyms (w.drop i) ++ R)) dst ((arrSyms (w.take i)).reverse ++ S dst) with hSt
  have hSt0 : St 0 = S := by
    rw [hSt]
    simp only [List.drop_zero, List.take_zero, arrSyms_nil, List.reverse_nil, List.nil_append]
    rw [← hsrc, Function.update_eq_self, Function.update_eq_self]
  have key := runsM_cdMove (M := M) hnc hnt hct (mvRec src dst) N Rn (S cnt) hRn (fun _ => m) St
    (fun i => 3 * ((w.getD i []).length + 1))
    (by rw [hSt0]; exact hN) (by rw [hSt0])
    (by rw [hSt]; simp only []; rw [Function.update_of_ne hdc.symm, Function.update_of_ne hsc.symm])
    ?_
  · rw [hSt0] at key
    refine RunsM.of_eq key rfl rfl rfl (by rw [hSt]) ?_
    rw [csum_mul, csum_vol w 0 N (by omega), List.drop_zero]
  · intro i hi X
    have hdrop : w.drop i = w[i] :: w.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
    have hs : (Function.update (St i) cnt X) src =
        recSyms w[i] ++ (arrSyms (w.drop (i + 1)) ++ R) := by
      rw [Function.update_of_ne hsc, hSt]
      simp only []
      rw [Function.update_of_ne hsd, Function.update_self, hdrop, arrSyms_cons, List.append_assoc]
    have h := runsM_mvRec (M := M) hsd w[i] (arrSyms (w.drop (i + 1)) ++ R) m
      (Function.update (St i) cnt X) hs
    refine RunsM.of_eq h rfl rfl rfl ?_ ?_
    · have e : (arrSyms (List.take (i + 1) w)).reverse =
          (recSyms w[i]).reverse ++ (arrSyms (List.take i w)).reverse := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
          arrSyms_append, arrSyms_cons, arrSyms_nil, List.append_nil, List.reverse_append]
      rw [hSt]
      simp only []
      rw [e]
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    · rw [List.getD_eq_getElem _ _ (by omega)]
      omega

theorem csum_add_fun (f g : ℕ → ℕ) :
    ∀ (n0 len : ℕ), csum (fun i => f i + g i) n0 len = csum f n0 len + csum g n0 len
  | _, 0 => rfl
  | n0, len + 1 => by
    simp only [csum]
    rw [csum_add_fun f g (n0 + 1) len]
    omega

theorem termOK_revRecs (l : List (List Bool)) (R : List Sym) (hR : TermOK R) :
    TermOK (l.flatMap (fun p => (recSyms p).reverse) ++ R) := by
  cases l with
  | nil => simpa using hR
  | cons p l =>
    rw [List.flatMap_cons, recSyms_reverse, List.cons_append, List.cons_append]
    exact TermOK.cons rfl _

/-- **Reversed block move.** The reversed records `u` (first element on top) move from `src` to
`dst`, each restored to its order; `dst` receives `arrSyms u.reverse`. -/
theorem runsM_cdMvRev {ns cnt tmp src dst : K} (hnc : ns ≠ cnt) (hnt : ns ≠ tmp)
    (hct : cnt ≠ tmp) (hsd : src ≠ dst) (hsc : src ≠ cnt) (hdc : dst ≠ cnt)
    (Rn : List Sym) (hRn : TermOK Rn) (u : List (List Bool)) (R : List Sym) (hR : TermOK R)
    (m : M) (S : K → List Sym) (hsrc : S src = u.flatMap (fun p => (recSyms p).reverse) ++ R)
    (hN : S ns = natSyms u.length ++ Rn) :
    RunsM (cdMove ns cnt tmp (mvRev src dst)) m S m
      (Function.update (Function.update S src R) dst (arrSyms u.reverse ++ S dst))
      (incSeqCost 6 8 u.length + 3 * vol u + 5 * u.length + 7 * bitLen u.length + 12) := by
  set St : ℕ → K → List Sym := fun i => Function.update (Function.update S src
    ((u.drop i).flatMap (fun p => (recSyms p).reverse) ++ R)) dst
    (arrSyms (u.take i).reverse ++ S dst) with hSt
  have hSt0 : St 0 = S := by
    rw [hSt]
    simp only [List.drop_zero, List.take_zero, List.reverse_nil, arrSyms_nil, List.nil_append]
    rw [← hsrc, Function.update_eq_self, Function.update_eq_self]
  have key := runsM_cdMove (M := M) hnc hnt hct (mvRev src dst) u.length Rn (S cnt) hRn
    (fun _ => m) St (fun i => 3 * ((u.getD i []).length + 1) + 3)
    (by rw [hSt0]; exact hN) (by rw [hSt0])
    (by rw [hSt]; simp only []; rw [Function.update_of_ne hdc.symm, Function.update_of_ne hsc.symm])
    ?_
  · rw [hSt0] at key
    refine RunsM.of_eq key rfl rfl rfl ?_ ?_
    · rw [hSt]
      simp only [List.drop_length, List.flatMap_nil, List.nil_append, List.take_length]
    · rw [csum_add_fun, csum_mul, csum_vol u 0 u.length (by omega), csum_const, List.drop_zero,
        List.take_length]
      omega
  · intro i hi X
    have hdrop : u.drop i = u[i] :: u.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
    have hs : (Function.update (St i) cnt X) src = (recSyms u[i]).reverse ++
        ((u.drop (i + 1)).flatMap (fun p => (recSyms p).reverse) ++ R) := by
      rw [Function.update_of_ne hsc, hSt]
      simp only []
      rw [Function.update_of_ne hsd, Function.update_self, hdrop, List.flatMap_cons,
        List.append_assoc]
    have h := runsM_mvRev (M := M) hsd u[i]
      ((u.drop (i + 1)).flatMap (fun p => (recSyms p).reverse) ++ R)
      (termOK_revRecs _ R hR) m (Function.update (St i) cnt X) hs
    refine RunsM.of_eq h rfl rfl rfl ?_ ?_
    · have e : arrSyms (List.take (i + 1) u).reverse = recSyms u[i] ++ arrSyms (List.take i u).reverse := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
          List.reverse_append, List.reverse_singleton, List.singleton_append, arrSyms_cons]
      rw [hSt]
      simp only []
      rw [e]
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    · rw [List.getD_eq_getElem _ _ (by omega)]
      omega

/-- Push `b` unary tokens (above a `mark`) on the depth stack `dk`. -/
def unaryB (bc cnt tmp dk : K) : KP K M :=
  .seq (lift (Lib.pushC dk .mark)) (cdMove bc cnt tmp (lift (Lib.pushC dk tok)))

/-- Remove the depth tokens and their `mark`. -/
def clearDep (dk : K) : KP K M :=
  .seq (whileTop dk isTokS (lift (Lib.popR dk))) (lift (Lib.popR dk))

theorem runsM_unaryB {bc cnt tmp dk : K} (hbc : bc ≠ cnt) (hbt : bc ≠ tmp) (hct : cnt ≠ tmp)
    (hdc : dk ≠ cnt) (hbd : bc ≠ dk) (b : ℕ) (Rb : List Sym) (hRb : TermOK Rb) (m : M)
    (S : K → List Sym) (hb : S bc = natSyms b ++ Rb) :
    RunsM (unaryB bc cnt tmp dk) m S m
      (Function.update S dk (List.replicate b tok ++ Sym.mark :: S dk))
      (incSeqCost 6 8 b + 3 * b + 7 * bitLen b + 13) := by
  have h1 := RunsM.push (M := M) dk Sym.mark m S
  set St : ℕ → K → List Sym := fun i =>
    Function.update S dk (List.replicate i tok ++ Sym.mark :: S dk) with hSt
  have key := runsM_cdMove (M := M) hbc hbt hct (lift (Lib.pushC dk tok)) b Rb (S cnt) hRb
    (fun _ => m) St (fun _ => 1)
    (by rw [hSt]; simp only []; rw [Function.update_of_ne hbd]; exact hb)
    (by rw [hSt]; simp only []; rw [Function.update_of_ne hdc.symm])
    (by rw [hSt]; simp only []; rw [Function.update_of_ne hdc.symm])
    ?_
  · have e0 : St 0 = Function.update S dk (Sym.mark :: S dk) := by rw [hSt]; simp
    rw [e0] at key
    refine RunsM.of_eq (h1.seq key) rfl rfl rfl (by rw [hSt]) ?_
    rw [csum_const]
    omega
  · intro i _ X
    have h := RunsM.push (M := M) dk tok m (Function.update (St i) cnt X)
    refine RunsM.of_eq h rfl rfl rfl ?_ le_rfl
    rw [hSt]
    simp only []
    funext k
    simp only [Function.update_apply, List.replicate_succ]
    split_ifs <;> simp_all

theorem loopM_clearDep (dk : K) (D : List Sym) (m : M) (S : K → List Sym) :
    ∀ e : ℕ, LoopM dk isTokS (lift (Lib.popR dk)) m
      (Function.update S dk (List.replicate e tok ++ Sym.mark :: D)) m
      (Function.update S dk (Sym.mark :: D)) (3 * e + 1)
  | 0 => (LoopM.stop (by simp [testO, isTokS, tok])).mono (by simp)
  | e + 1 => by
    have h := RunsM.pop (M := M) dk tok (List.replicate e tok ++ Sym.mark :: D) m
      (Function.update S dk (List.replicate (e + 1) tok ++ Sym.mark :: D))
      (by simp [List.replicate_succ])
    rw [Function.update_idem] at h
    refine (LoopM.step (by simp [testO, isTokS, List.replicate_succ]) h
      (loopM_clearDep dk D m S e)).mono (by omega)

theorem runsM_clearDep (dk : K) (e : ℕ) (D : List Sym) (m : M) (S : K → List Sym)
    (hS : S dk = List.replicate e tok ++ Sym.mark :: D) :
    RunsM (clearDep dk) m S m (Function.update S dk D) (3 * e + 3) := by
  have h1 := runsM_whileTop' (loopM_clearDep dk D m S e)
  have h2 := RunsM.pop (M := M) dk Sym.mark D m (Function.update S dk (Sym.mark :: D))
    (Function.update_self _ _ _)
  rw [Function.update_idem] at h2
  have e0 : Function.update S dk (List.replicate e tok ++ Sym.mark :: D) = S := by
    rw [← hS, Function.update_eq_self]
  rw [e0] at h1
  exact (h1.seq h2).mono (by omega)

end Generic

end SubNLogN.Machine.K1.SMM
