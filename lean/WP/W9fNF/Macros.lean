import WP.W6a.Basic

/-!
# WP.W9fNF.Macros — symbol-level stack macros for the Nyquist finish

Generic over the stack type `K`, one `Option Sym` register, exact final states:

| macro | effect | cost |
|---|---|---|
| `stageA e src t` | move `d ++ [e]` from `src` onto `t` (reversed); no `e` in `d` | `3·|d| + 5` |
| `stageB t dst` | move `l` from `t` onto `dst` (reversed) down to a `mark`, pop it | `4·|l| + 3` |
| `moveOne src dst t` | move one record `d ++ [sep]` keeping its order (W9fM) | `7·|d| + 13` |
| `peel src t` | `pushC t mark; stageA sep2 src t` (expose the second coordinate) | `3·|d| + 6` |
| `dropInt k` | pop `intSyms z` | `3·|z| + 3` |
| `moveInt src dst t` | move `intSyms z` keeping its order | `7·|z| + 14` |
| `replInt src dst t` | `dropInt dst; moveInt src dst t` | `3·|y| + 7·|z| + 17` |
| `dropUntil e k` | pop `d ++ [e]`; no `e` in `d` | `3·|d| + 3` |
-/

namespace WP.W9fNF

open TMFw TMFw.Lib TMFw.Contracts Computability WP.W6a

section Macros

variable {K : Type} [DecidableEq K]

/-! ## Stage A: move up to and including a stop symbol -/

/-- Loop of stage A. -/
def stageALoop (e : Sym) (src t : K) : SProg K :=
  .loop (fun r => !decide (r = some e)) (.seq (popR src) (pushR t))

/-- Stage A: move symbols from `src` onto `t` up to and including the first `e`. -/
def stageA (e : Sym) (src t : K) : SProg K := .seq (.load fun _ => none) (stageALoop e src t)

theorem stageALoop_eval (e : Sym) {src t : K} (hst : src ≠ t) (ρ : List (SProg K)) :
    ∀ (d rest : List Sym) (S : K → List Sym) (cur : Option Sym),
      (∀ x ∈ d, x ≠ e) → cur ≠ some e → S src = d ++ e :: rest →
      Eval ρ (stageALoop e src t) ⟨cur, S⟩
        ⟨some e, Function.update (Function.update S src rest) t ((d ++ [e]).reverse ++ S t)⟩
        (3 * d.length + 4)
  | [], rest, S, cur, _, hcur, hS => by
    have e1 : Eval ρ (popR src) ⟨cur, S⟩ ⟨some e, Function.update S src rest⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) cur S).of_eq ?_ rfl
      rw [hS]
      rfl
    have e2 : Eval ρ (pushR t) ⟨some e, Function.update S src rest⟩
        ⟨some e, Function.update (Function.update S src rest) t (([] ++ [e]).reverse ++ S t)⟩ 1 := by
      refine (Eval.push ρ t (fun r => r.getD .sep) (some e) _).of_eq ?_ rfl
      rw [Function.update_of_ne (Ne.symm hst)]
      rfl
    exact (Eval.loop_true (by simp [hcur]) (Eval.seq e1 e2) (Eval.loop_false (by simp))).of_eq
      rfl rfl
  | x :: d, rest, S, cur, hd, hcur, hS => by
    have hx : x ≠ e := hd x (List.mem_cons_self ..)
    have e1 : Eval ρ (popR src) ⟨cur, S⟩
        ⟨some x, Function.update S src (d ++ e :: rest)⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) cur S).of_eq ?_ rfl
      rw [hS]
      rfl
    have e2 : Eval ρ (pushR t) ⟨some x, Function.update S src (d ++ e :: rest)⟩
        ⟨some x, Function.update (Function.update S src (d ++ e :: rest)) t (x :: S t)⟩ 1 := by
      refine (Eval.push ρ t (fun r => r.getD .sep) (some x) _).of_eq ?_ rfl
      rw [Function.update_of_ne (Ne.symm hst)]
      rfl
    have ih := stageALoop_eval e hst ρ d rest
      (Function.update (Function.update S src (d ++ e :: rest)) t (x :: S t)) (some x)
      (fun y hy => hd y (List.mem_cons_of_mem _ hy)) (by simpa using hx)
      (by rw [Function.update_of_ne hst, Function.update_self])
    refine (Eval.loop_true (by simp [hcur]) (Eval.seq e1 e2) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply, List.cons_append, List.reverse_cons, List.append_assoc]
    split_ifs <;> simp_all

theorem stageA_eval (e : Sym) {src t : K} (hst : src ≠ t) (ρ : List (SProg K)) (v : Option Sym)
    (d rest : List Sym) (S : K → List Sym) (hd : ∀ x ∈ d, x ≠ e) (hS : S src = d ++ e :: rest) :
    Eval ρ (stageA e src t) ⟨v, S⟩
      ⟨some e, Function.update (Function.update S src rest) t ((d ++ [e]).reverse ++ S t)⟩
      (3 * d.length + 5) :=
  (Eval.seq (Eval.load ρ (fun _ => none) v S)
    (stageALoop_eval e hst ρ d rest S none hd (by simp) hS)).of_eq rfl (by omega)

/-! ## Stage B: move back down to a `mark`, then pop it -/

/-- Loop of stage B. -/
def stageBLoop (t dst : K) : SProg K :=
  .loop (fun r => !decide (r = some Sym.mark)) (.seq (popR t) (.seq (pushR dst) (peekR t)))

/-- Stage B: move symbols from `t` onto `dst` down to a `mark`, then pop the mark. -/
def stageB (t dst : K) : SProg K := .seq (peekR t) (.seq (stageBLoop t dst) (popR t))

theorem stageBLoop_eval {t dst : K} (htd : t ≠ dst) (ρ : List (SProg K)) (t0 : List Sym) :
    ∀ (l : List Sym) (S : K → List Sym), (∀ x ∈ l, x ≠ Sym.mark) →
      S t = l ++ Sym.mark :: t0 →
      Eval ρ (stageBLoop t dst) ⟨(l ++ Sym.mark :: t0).head?, S⟩
        ⟨some Sym.mark, Function.update (Function.update S t (Sym.mark :: t0)) dst
          (l.reverse ++ S dst)⟩ (4 * l.length + 1)
  | [], S, _, hS => by
    have hS' : S t = Sym.mark :: t0 := hS
    refine (Eval.loop_false (by simp)).of_eq ?_ rfl
    show (⟨some Sym.mark, S⟩ : SSt K) = _
    rw [List.reverse_nil, List.nil_append, ← hS', Function.update_eq_self, Function.update_eq_self]
  | x :: l, S, hl, hS => by
    have hx : x ≠ Sym.mark := hl x (List.mem_cons_self ..)
    have e1 : Eval ρ (popR t) ⟨((x :: l) ++ Sym.mark :: t0).head?, S⟩
        ⟨some x, Function.update S t (l ++ Sym.mark :: t0)⟩ 1 := by
      refine (Eval.pop ρ t (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS]
      rfl
    have e2 : Eval ρ (pushR dst) ⟨some x, Function.update S t (l ++ Sym.mark :: t0)⟩
        ⟨some x, Function.update (Function.update S t (l ++ Sym.mark :: t0)) dst (x :: S dst)⟩ 1 := by
      refine (Eval.push ρ dst (fun r => r.getD .sep) (some x) _).of_eq ?_ rfl
      rw [Function.update_of_ne (Ne.symm htd)]
      rfl
    have e3 : Eval ρ (peekR t)
        ⟨some x, Function.update (Function.update S t (l ++ Sym.mark :: t0)) dst (x :: S dst)⟩
        ⟨(l ++ Sym.mark :: t0).head?,
          Function.update (Function.update S t (l ++ Sym.mark :: t0)) dst (x :: S dst)⟩ 1 := by
      refine (Eval.peek ρ t (fun _ o => o) _ _).of_eq ?_ rfl
      rw [Function.update_of_ne htd, Function.update_self]
    have ih := stageBLoop_eval htd ρ t0 l
      (Function.update (Function.update S t (l ++ Sym.mark :: t0)) dst (x :: S dst))
      (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      (by rw [Function.update_of_ne htd, Function.update_self])
    refine (Eval.loop_true (by simp [hx]) (Eval.seq e1 (Eval.seq e2 e3)) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all

theorem stageB_eval {t dst : K} (htd : t ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (l t0 : List Sym) (S : K → List Sym) (hl : ∀ x ∈ l, x ≠ Sym.mark)
    (hS : S t = l ++ Sym.mark :: t0) :
    Eval ρ (stageB t dst) ⟨v, S⟩
      ⟨some Sym.mark, Function.update (Function.update S t t0) dst (l.reverse ++ S dst)⟩
      (4 * l.length + 3) := by
  have e1 : Eval ρ (peekR t) ⟨v, S⟩ ⟨(l ++ Sym.mark :: t0).head?, S⟩ 1 :=
    (Eval.peek ρ t (fun _ o => o) v S).of_eq (by rw [hS]) rfl
  have e2 := stageBLoop_eval htd ρ t0 l S hl hS
  have e3 : Eval ρ (popR t)
      ⟨some Sym.mark, Function.update (Function.update S t (Sym.mark :: t0)) dst (l.reverse ++ S dst)⟩
      ⟨some Sym.mark, Function.update (Function.update (Function.update S t (Sym.mark :: t0)) dst
        (l.reverse ++ S dst)) t t0⟩ 1 := by
    refine (Eval.pop ρ t (fun _ o => o) _ _).of_eq ?_ rfl
    rw [Function.update_of_ne htd, Function.update_self]
    rfl
  refine (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end Macros

#assert_std_axioms stageALoop_eval stageA_eval stageBLoop_eval stageB_eval

end WP.W9fNF
