/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.SafeTransport
import SubNLogN.Machine.Calculus.Park

/-!
# Framed procedure calculus (`Calculus/SafePark.lean`): boundary-safe parking

The extensional `Runs` facts for
`park`/`unpark` in `Calculus/Park.lean`. They take a `FrameTail` below the parked block, so the
`mark` that stops the scan may lie *below* the visible content. In the stack-bottom case
(`rest = []`) the scan even pops an empty stack. Neither situation is boundary-safe.

This file proves the **same programs** boundary-safe (`SafeEval` / `SafeRunsIn`, for **every**
framed set) under the **owned-delimiter convention**:
* `park r p` needs `S r = es ++ mark :: rest`, so the delimiter `mark` belongs to the visible
  content of `r`. The scan pops the delimiter and `restoreR` pushes it back; this temporary
  removal happens while the visible content is non-empty. `rest` is arbitrary visible content.
  Tails below it come from `SafeRunsIn.frame_tail` (`Calculus/SafeTransport.lean`).
* `unpark p r` needs `S p = es.reverse ++ mark :: pt`, where the `mark` was pushed by the matching
  `park`.
* `unprotect k` needs `S k = mark :: tl`. `protect` only pushes.
* `safeRunsIn_parkCall` and `safeRunsIn_protectCall` are the call rules of `Park.lean` in safe
  form, with the same costs. The child sees the parent's delimiter on `r`. A child framed on
  `r` with empty visible content gets that delimiter as part of its tail (`frame_tail`), so it
  never reads it.

In all these runs every `pop` finds the popped stack non-empty in the visible state, which is why
the results hold for any `framed`. The excluded case (no delimiter in the visible content) is
exactly the unsafe one. The popping `Runs` rules of `Park.lean` stay available for legacy use only.
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

/-- Rewriting the final state and the cost of a safe run. -/
theorem SafeEval.of_eq_cost {K σ : Type} [DecidableEq K] {framed : K → Prop}
    {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ}
    {s s₁ s₂ : St K (fun _ => Sym) σ} {t t₂ : ℕ} (h : SafeEval framed ρ p s s₁ t) (e : s₁ = s₂)
    (et : t = t₂) : SafeEval framed ρ p s s₂ t₂ := by
  subst e
  subst et
  exact h

section SafeMacros

variable {K : Type} [DecidableEq K]

/-- The scanning loop of `moveToMark`, safe: the delimiter is in the visible content. -/
theorem safeEval_moveToMark_loop (framed : K → Prop) {src dst : K} (hne : src ≠ dst)
    (ρ : List (SProg K)) :
    ∀ (es rest : List Sym) (S : K → List Sym), MarkFree es →
      S src = (es ++ Sym.mark :: rest).tail →
      SafeEval framed ρ (.loop notMarkR (moveBitsBody src dst))
        ⟨(es ++ Sym.mark :: rest).head?, S⟩
        ⟨some Sym.mark, Function.update (Function.update S src rest) dst (es.reverse ++ S dst)⟩
        (3 * es.length + 1)
  | [], rest, S, _, hS => by
    have hc : notMarkR (some Sym.mark) = false := by simp [notMarkR]
    refine (SafeEval.loop_false (framed := framed) (ρ := ρ) (p := moveBitsBody src dst)
      (s := ⟨some Sym.mark, S⟩) hc).of_eq_cost ?_ rfl
    have hS' : S src = rest := hS
    show (⟨some Sym.mark, S⟩ : SSt K) = ⟨some Sym.mark, Function.update
      (Function.update S src rest) dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | e :: es, rest, S, hes, hS => by
    have he : e ≠ Sym.mark := hes e List.mem_cons_self
    have hes' : MarkFree es := fun d hd => hes d (List.mem_cons_of_mem e hd)
    have hS' : S src = es ++ Sym.mark :: rest := hS
    have hpush : SafeEval framed ρ (pushR dst) ⟨some e, S⟩
        ⟨some e, Function.update S dst (e :: S dst)⟩ 1 :=
      (SafeEval.push ρ dst (fun r => r.getD .sep) (some e) S).of_eq_cost rfl rfl
    have hsrc : Function.update S dst (e :: S dst) src = es ++ Sym.mark :: rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hnn : framed src → Function.update S dst (e :: S dst) src ≠ [] := by
      intro _
      rw [hsrc]
      simp
    have hpop : SafeEval framed ρ (popR src) ⟨some e, Function.update S dst (e :: S dst)⟩
        ⟨(es ++ Sym.mark :: rest).head?, Function.update (Function.update S dst (e :: S dst))
          src (es ++ Sym.mark :: rest).tail⟩ 1 := by
      refine (SafeEval.pop ρ src (fun _ o => o) _ _ hnn).of_eq_cost ?_ rfl
      rw [hsrc]
    have ih := safeEval_moveToMark_loop framed hne ρ es rest
      (Function.update (Function.update S dst (e :: S dst)) src (es ++ Sym.mark :: rest).tail) hes'
      (Function.update_self _ _ _)
    have hc : notMarkR (some e) = true := by simp [notMarkR, he]
    refine (SafeEval.loop_true hc (SafeEval.seq hpush hpop) ih).of_eq_cost ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **moveToMark**, safe and exact, when the stopping `mark` is visible:
`src = es ++ mark :: rest` becomes `src = rest`, and the register ends at `some mark`. -/
theorem safeEval_moveToMark (framed : K → Prop) {src dst : K} (hne : src ≠ dst)
    (ρ : List (SProg K)) (v : Option Sym) (es rest : List Sym) (S : K → List Sym)
    (hes : MarkFree es) (hS : S src = es ++ Sym.mark :: rest) :
    SafeEval framed ρ (moveToMark src dst) ⟨v, S⟩
      ⟨some Sym.mark, Function.update (Function.update S src rest) dst (es.reverse ++ S dst)⟩
      (3 * es.length + 2) := by
  have hnn : framed src → S src ≠ [] := by
    intro _
    rw [hS]
    simp
  have h1 : SafeEval framed ρ (popR src) ⟨v, S⟩
      ⟨(es ++ Sym.mark :: rest).head?, Function.update S src (es ++ Sym.mark :: rest).tail⟩ 1 := by
    refine (SafeEval.pop ρ src (fun _ o => o) v S hnn).of_eq_cost ?_ rfl
    rw [hS]
  have h2 := safeEval_moveToMark_loop framed hne ρ es rest
    (Function.update S src (es ++ Sym.mark :: rest).tail) hes (Function.update_self _ _ _)
  refine (SafeEval.seq h1 h2).of_eq_cost ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- `restoreR` with a `mark` in the register pushes it back (no read). -/
theorem safeEval_restoreR_mark (framed : K → Prop) (ρ : List (SProg K)) (k : K)
    (S : K → List Sym) :
    SafeEval framed ρ (restoreR k) ⟨some Sym.mark, S⟩
      ⟨some Sym.mark, Function.update S k (Sym.mark :: S k)⟩ 2 := by
  have h := SafeEval.push (framed := framed) ρ k (fun r => r.getD .sep) (some Sym.mark) S
  exact SafeEval.ite_true (c := fun r => r.isSome) (q := skip) (by rfl) h

/-- **park**, safe and exact (owned delimiter): `r = es ++ mark :: rest` becomes `r = mark :: rest`
(the delimiter is popped and pushed back), and `es` lands reversed on `p` above a new `mark`. -/
theorem safeEval_park (framed : K → Prop) {r p : K} (hrp : r ≠ p) (ρ : List (SProg K))
    (v : Option Sym) (es rest : List Sym) (S : K → List Sym) (hes : MarkFree es)
    (hS : S r = es ++ Sym.mark :: rest) :
    SafeEval framed ρ (park r p) ⟨v, S⟩
      ⟨some Sym.mark, Function.update (Function.update S r (Sym.mark :: rest)) p
        (es.reverse ++ Sym.mark :: S p)⟩
      (3 * es.length + 5) := by
  have e0 : SafeEval framed ρ (pushC p .mark) ⟨v, S⟩ ⟨v, Function.update S p (.mark :: S p)⟩ 1 := by
    have h := SafeEval.push (framed := framed) ρ p (fun _ => Sym.mark) v S
    exact h
  have e1 := safeEval_moveToMark framed hrp ρ v es rest (Function.update S p (.mark :: S p)) hes
    (by rw [Function.update_of_ne hrp]; exact hS)
  have e2 := safeEval_restoreR_mark framed ρ r
    (Function.update (Function.update (Function.update S p (.mark :: S p)) r rest) p
      (es.reverse ++ Function.update S p (.mark :: S p) p))
  refine (SafeEval.seq e0 (SafeEval.seq e1 e2)).of_eq_cost ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- **unpark**, safe and exact: `p = es.reverse ++ mark :: pt` becomes `p = pt` (the `mark` pushed
by the matching `park` is consumed) and `es` goes back on `r`. -/
theorem safeEval_unpark (framed : K → Prop) {p r : K} (hpr : p ≠ r) (ρ : List (SProg K))
    (v : Option Sym) (es pt : List Sym) (S : K → List Sym) (hes : MarkFree es)
    (hS : S p = es.reverse ++ Sym.mark :: pt) :
    SafeEval framed ρ (unpark p r) ⟨v, S⟩
      ⟨some Sym.mark, Function.update (Function.update S p pt) r (es ++ S r)⟩
      (3 * es.length + 2) := by
  have h := safeEval_moveToMark framed hpr ρ v es.reverse pt S hes.reverse hS
  refine h.of_eq_cost ?_ (by rw [List.length_reverse])
  rw [List.reverse_reverse]

/-- **protect**, safe (push only). -/
theorem safeEval_protect (framed : K → Prop) (ρ : List (SProg K)) (k : K) (v : Option Sym)
    (S : K → List Sym) :
    SafeEval framed ρ (protect k) ⟨v, S⟩ ⟨v, Function.update S k (Sym.mark :: S k)⟩ 1 := by
  have h := SafeEval.push (framed := framed) ρ k (fun _ => Sym.mark) v S
  exact h

/-- **unprotect**, safe: pops the visible top `mark`. -/
theorem safeEval_unprotect (framed : K → Prop) (ρ : List (SProg K)) (k : K) (v : Option Sym)
    (S : K → List Sym) (tl : List Sym) (hS : S k = Sym.mark :: tl) :
    SafeEval framed ρ (unprotect k) ⟨v, S⟩ ⟨some Sym.mark, Function.update S k tl⟩ 1 := by
  have hnn : framed k → S k ≠ [] := by
    intro _
    rw [hS]
    simp
  refine (SafeEval.pop ρ k (fun _ o => o) v S hnn).of_eq_cost ?_ rfl
  rw [hS]
  rfl

/-! ### `SafeRunsIn` forms (any environment, any framed set) -/

theorem safeRunsIn_park (framed : K → Prop) {r p : K} (hrp : r ≠ p) (ρ : List (SProg K))
    (es rest : List Sym) (S : K → List Sym) (hes : MarkFree es)
    (hS : S r = es ++ Sym.mark :: rest) :
    SafeRunsIn framed ρ (park r p) S
      (Function.update (Function.update S r (Sym.mark :: rest)) p (es.reverse ++ Sym.mark :: S p))
      (fun _ => True) (3 * es.length + 5) :=
  fun v => ⟨_, _, safeEval_park framed hrp ρ v es rest S hes hS, trivial, le_rfl⟩

theorem safeRunsIn_unpark (framed : K → Prop) {p r : K} (hpr : p ≠ r) (ρ : List (SProg K))
    (es pt : List Sym) (S : K → List Sym) (hes : MarkFree es)
    (hS : S p = es.reverse ++ Sym.mark :: pt) :
    SafeRunsIn framed ρ (unpark p r) S (Function.update (Function.update S p pt) r (es ++ S r))
      (fun _ => True) (3 * es.length + 2) :=
  fun v => ⟨_, _, safeEval_unpark framed hpr ρ v es pt S hes hS, trivial, le_rfl⟩

theorem safeRunsIn_protect (framed : K → Prop) (ρ : List (SProg K)) (k : K) (S : K → List Sym) :
    SafeRunsIn framed ρ (protect k) S (Function.update S k (Sym.mark :: S k)) (fun _ => True) 1 :=
  fun v => ⟨_, _, safeEval_protect framed ρ k v S, trivial, le_rfl⟩

theorem safeRunsIn_unprotect (framed : K → Prop) (ρ : List (SProg K)) (k : K) (S : K → List Sym)
    (tl : List Sym) (hS : S k = Sym.mark :: tl) :
    SafeRunsIn framed ρ (unprotect k) S (Function.update S k tl) (fun _ => True) 1 :=
  fun v => ⟨_, _, safeEval_unprotect framed ρ k v S tl hS, trivial, le_rfl⟩

end SafeMacros

/-! ### Safe call rules -/

section SafeCalls

variable {K σ : Type} [DecidableEq K]

/-- **The safe parking rule** (owned delimiter). The parent's stack `r` holds a mark-free block
`es` above its own visible delimiter: `S r = es ++ mark :: rest`. The child runs with
`r = mark :: rest` and with the parking stack holding `mark :: es.reverse ++ mark :: (old p)`. It
may change `r` arbitrarily but must leave `p` as it found it. Afterwards the parked call puts `es`
back on top of whatever the child left on `r` and restores the old content of `p`; every other
stack is as the child left it. The run is boundary-safe for the given `framed` set, as soon as
the child's run is. The overhead is `6·|es| + 9`, as in `runsIn_parkCall`. -/
theorem safeRunsIn_parkCall (framed : K → Prop) {ρ : List (Prog K (fun _ => Sym) σ)}
    (l : Lens σ (Option Sym)) {r p : K} (hrp : r ≠ p) {child : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (es rest : List Sym) (hes : MarkFree es)
    (hSr : S r = es ++ Sym.mark :: rest)
    (hchild : SafeRunsIn framed ρ child
      (Function.update (Function.update S r (Sym.mark :: rest)) p
        (Sym.mark :: (es.reverse ++ Sym.mark :: S p))) S' Q T)
    (hp' : S' p = Sym.mark :: (es.reverse ++ Sym.mark :: S p)) :
    SafeRunsIn framed ρ (parkCall l r p child) S
      (Function.update (Function.update S' p (S p)) r (es ++ S' r)) (fun _ => True)
      (T + 6 * es.length + 9) := by
  have e1 := SafeRunsIn.liftRegs l (closed_park r p)
    (safeRunsIn_park framed hrp [] es rest S hes hSr) ρ
  set S1 := Function.update (Function.update S r (Sym.mark :: rest)) p
    (es.reverse ++ Sym.mark :: S p) with hS1
  have e2 := SafeRunsIn.liftRegs l (closed_protect p) (safeRunsIn_protect framed [] p S1) ρ
  have hS2 : Function.update S1 p (Sym.mark :: S1 p) =
      Function.update (Function.update S r (Sym.mark :: rest)) p
        (Sym.mark :: (es.reverse ++ Sym.mark :: S p)) := by
    rw [hS1, Function.update_self, Function.update_idem]
  rw [hS2] at e2
  have e4 := SafeRunsIn.liftRegs l (closed_unprotect p)
    (safeRunsIn_unprotect framed [] p S' _ hp') ρ
  have e5 := SafeRunsIn.liftRegs l (closed_unpark p r)
    (safeRunsIn_unpark framed (Ne.symm hrp) [] es (S p)
      (Function.update S' p (es.reverse ++ Sym.mark :: S p)) hes (Function.update_self _ _ _)) ρ
  have hfin : Function.update (Function.update (Function.update S' p
      (es.reverse ++ Sym.mark :: S p)) p (S p)) r
      (es ++ Function.update S' p (es.reverse ++ Sym.mark :: S p) r) =
      Function.update (Function.update S' p (S p)) r (es ++ S' r) := by
    rw [Function.update_idem, Function.update_of_ne hrp]
  rw [hfin] at e5
  refine SafeRunsIn.mono
    (SafeRunsIn.seq e1 (SafeRunsIn.seq e2 (SafeRunsIn.seq hchild (SafeRunsIn.seq e4 e5))))
    (fun _ _ => trivial) ?_
  omega

/-- **The safe protection rule.** The child runs with a visible `mark` on top of `k` and must
leave that stack as it found it; the old content of `k` is restored. Overhead `2`. -/
theorem safeRunsIn_protectCall (framed : K → Prop) {ρ : List (Prog K (fun _ => Sym) σ)}
    (l : Lens σ (Option Sym)) (k : K) {child : Prog K (fun _ => Sym) σ} {S S' : K → List Sym}
    {Q : σ → Prop} {T : ℕ}
    (hchild : SafeRunsIn framed ρ child (Function.update S k (Sym.mark :: S k)) S' Q T)
    (hk' : S' k = Sym.mark :: S k) :
    SafeRunsIn framed ρ (protectCall l k child) S (Function.update S' k (S k)) (fun _ => True)
      (T + 2) := by
  have e1 := SafeRunsIn.liftRegs l (closed_protect k) (safeRunsIn_protect framed [] k S) ρ
  have e3 := SafeRunsIn.liftRegs l (closed_unprotect k)
    (safeRunsIn_unprotect framed [] k S' (S k) hk') ρ
  refine SafeRunsIn.mono (SafeRunsIn.seq e1 (SafeRunsIn.seq hchild e3)) (fun _ _ => trivial) ?_
  omega

end SafeCalls

#assert_std_axioms SafeEval.of_eq_cost safeEval_moveToMark_loop safeEval_moveToMark
  safeEval_restoreR_mark safeEval_park safeEval_unpark safeEval_protect safeEval_unprotect
  safeRunsIn_park safeRunsIn_unpark safeRunsIn_protect safeRunsIn_unprotect safeRunsIn_parkCall
  safeRunsIn_protectCall

end SubNLogN.Machine.Calculus
