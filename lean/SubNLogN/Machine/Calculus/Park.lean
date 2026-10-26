/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Basic

/-!
# Framed procedure calculus, layer 2 (`Calculus/Park.lean`): parking and protection

The depth-first parking discipline of Proposition A.7 (`prop:transfer11`),
Section A.2 (`sec:transfer-power`): before a child call the parent moves its live data away from the stacks the child uses,
so the child finds them in a frame-tail state, and it moves the data back after the return. A call
never scans an ancestor's parked data.

Programs (one `Option Sym` register, `SProg`):
* `moveToMark src dst`: move the block above the first `mark` of `src` onto `dst` (reversed); the
  `mark` (or `none` at the bottom) goes to the register. Cost `3·|block| + 2` (`moveToMark_eval`).
* `park r p`: push a `mark` on the parking stack `p`, move the mark-free block above `r`'s frame
  tail onto `p`, restore `r`'s frame mark. `r` is left in its frame-tail state. Cost `3·|block| + 5`.
* `unpark p r`: move the block above `p`'s top `mark` back onto `r` (original order) and drop that
  `mark`. Cost `3·|block| + 2`.
* `protect k` / `unprotect k`: push / pop one `mark` (cost 1). After `protect k` the old content of
  `k` is a frame tail.

**Operational boundary note.** `moveToMark`, `park` and `unpark` pop the stopping `mark`
(or reach the bottom) and, for `park`, push it back. Their lemmas are exact for every tail in the
class `FrameTail` (they are `FramedRunsIn` facts for that class), but these programs are not
boundary-safe in the sense of `SafeEval` (`Calculus/Frame.lean`) on the scanned stack; for
`SafeEval`-based framing use the peek-based passes of `Calculus/FramePass.lean`. A block must be
`MarkFree`, so these programs can never be applied to `hdrSyms` (which has a `mark` after every
field).

Composition lemmas (any environment `ρ`, the child may be `recur 0`):
* `runsIn_parkCall`: `park r p ; protect p ; child ; unprotect p ; unpark p r` runs the child with
  `r` in its frame-tail state and `p = mark :: (parked block) ++ mark :: (old p)` (a frame tail), and
  restores both; the overhead is `6·|block| + 9`, independent of the tails.
* `runsIn_protectCall`: `protect k ; child ; unprotect k`, overhead `2`.
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

section Programs

variable {K : Type}

/-- Loop guard: the register holds a symbol other than `mark`. -/
def notMarkR (r : Option Sym) : Bool :=
  match r with
  | some d => !decide (d = Sym.mark)
  | none => false

/-- Move the block above the first `mark` of `src` onto `dst` (reversed); the `mark` (or `none`)
goes to the register. -/
def moveToMark (src dst : K) : SProg K := .seq (popR src) (.loop notMarkR (moveBitsBody src dst))

/-- **Park** the mark-free block above `r`'s frame tail on `p`, above a new `mark`. -/
def park (r p : K) : SProg K := .seq (pushC p .mark) (.seq (moveToMark r p) (restoreR r))

/-- **Unpark**: move the block above `p`'s top `mark` back onto `r`; drop that `mark`. -/
def unpark (p r : K) : SProg K := moveToMark p r

/-- **Protect** `k`: push a `mark`, so that the old content of `k` becomes a frame tail. -/
def protect (k : K) : SProg K := pushC k .mark

/-- **Unprotect** `k`: pop the top `mark`. -/
def unprotect (k : K) : SProg K := popR k

theorem closed_moveToMark (src dst : K) : (moveToMark src dst).Closed := by
  simp [Prog.Closed, moveToMark, Prog.FreeBelow, moveBitsBody, pushR, popR]

theorem closed_park (r p : K) : (park r p).Closed := by
  simp [Prog.Closed, park, moveToMark, Prog.FreeBelow, moveBitsBody, pushR, popR, pushC, restoreR,
    Lib.skip]

theorem closed_unpark (p r : K) : (unpark p r).Closed := closed_moveToMark p r

theorem closed_protect (k : K) : (protect k).Closed := by
  simp [Prog.Closed, protect, Prog.FreeBelow, pushC]

theorem closed_unprotect (k : K) : (unprotect k).Closed := by
  simp [Prog.Closed, unprotect, Prog.FreeBelow, popR]

end Programs

section Eval

variable {K : Type} [DecidableEq K]

theorem notMarkR_head?_of_frameTail {rest : List Sym} (h : FrameTail rest) :
    notMarkR rest.head? = false := by
  rcases h with rfl | h
  · rfl
  · rw [h]
    simp [notMarkR]

theorem moveToMark_loop_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) :
    ∀ (es rest : List Sym) (S : K → List Sym), MarkFree es → FrameTail rest →
      S src = (es ++ rest).tail →
      Eval ρ (.loop notMarkR (moveBitsBody src dst)) ⟨(es ++ rest).head?, S⟩
        ⟨rest.head?, Function.update (Function.update S src rest.tail) dst (es.reverse ++ S dst)⟩
        (3 * es.length + 1)
  | [], rest, S, _, hrest, hS => by
    refine (Eval.loop_false (notMarkR_head?_of_frameTail hrest)).of_eq ?_ rfl
    have hS' : S src = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update (Function.update S src rest.tail)
      dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | e :: es, rest, S, hes, hrest, hS => by
    have he : e ≠ Sym.mark := hes e List.mem_cons_self
    have hes' : MarkFree es := fun d hd => hes d (List.mem_cons_of_mem e hd)
    have hS' : S src = es ++ rest := hS
    have hpush : Eval ρ (pushR dst) ⟨some e, S⟩ ⟨some e, Function.update S dst (e :: S dst)⟩ 1 :=
      (Eval.push ρ dst (fun r => r.getD .sep) (some e) S).of_eq rfl rfl
    have hsrc : Function.update S dst (e :: S dst) src = es ++ rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval ρ (popR src) ⟨some e, Function.update S dst (e :: S dst)⟩
        ⟨(es ++ rest).head?, Function.update (Function.update S dst (e :: S dst))
          src (es ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := moveToMark_loop_eval hne ρ es rest
      (Function.update (Function.update S dst (e :: S dst)) src (es ++ rest).tail) hes' hrest
      (Function.update_self _ _ _)
    have hc : notMarkR (some e) = true := by simp [notMarkR, he]
    refine (Eval.loop_true hc (Eval.seq hpush hpop) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **moveToMark**, exact. -/
theorem moveToMark_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (es rest : List Sym) (S : K → List Sym) (hes : MarkFree es) (hrest : FrameTail rest)
    (hS : S src = es ++ rest) :
    Eval ρ (moveToMark src dst) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S src rest.tail) dst (es.reverse ++ S dst)⟩
      (3 * es.length + 2) := by
  have h1 : Eval ρ (popR src) ⟨v, S⟩
      ⟨(es ++ rest).head?, Function.update S src (es ++ rest).tail⟩ 1 := by
    refine (Eval.pop ρ src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := moveToMark_loop_eval hne ρ es rest (Function.update S src (es ++ rest).tail) hes hrest
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- **park**, exact: `r = es ++ rest` (mark-free `es`, frame tail `rest`) becomes `r = rest`, and
`es` lands reversed on `p` above a new `mark`. -/
theorem park_eval {r p : K} (hrp : r ≠ p) (ρ : List (SProg K)) (v : Option Sym)
    (es rest : List Sym) (S : K → List Sym) (hes : MarkFree es) (hrest : FrameTail rest)
    (hS : S r = es ++ rest) :
    Eval ρ (park r p) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S r rest) p (es.reverse ++ Sym.mark :: S p)⟩
      (3 * es.length + 5) := by
  have e0 : Eval ρ (pushC p .mark) ⟨v, S⟩ ⟨v, Function.update S p (.mark :: S p)⟩ 1 :=
    Eval.push ρ p (fun _ => .mark) v S
  have e1 := moveToMark_eval hrp ρ v es rest (Function.update S p (.mark :: S p)) hes hrest
    (by rw [Function.update_of_ne hrp]; exact hS)
  have e2 := restoreR_eval ρ r rest
    (Function.update (Function.update (Function.update S p (.mark :: S p)) r rest.tail) p
      (es.reverse ++ Function.update S p (.mark :: S p) p))
    (by rw [Function.update_of_ne hrp, Function.update_self])
  refine (Eval.seq e0 (Eval.seq e1 e2)).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- **unpark**, exact: `p = es.reverse ++ mark :: pt` gives `p = pt` and `es` back on `r`. -/
theorem unpark_eval {p r : K} (hpr : p ≠ r) (ρ : List (SProg K)) (v : Option Sym)
    (es pt : List Sym) (S : K → List Sym) (hes : MarkFree es)
    (hS : S p = es.reverse ++ Sym.mark :: pt) :
    Eval ρ (unpark p r) ⟨v, S⟩
      ⟨some .mark, Function.update (Function.update S p pt) r (es ++ S r)⟩ (3 * es.length + 2) := by
  have h := moveToMark_eval hpr ρ v es.reverse (Sym.mark :: pt) S hes.reverse (FrameTail.mark pt) hS
  refine h.of_eq ?_ (by rw [List.length_reverse])
  rw [List.reverse_reverse]
  rfl

end Eval

/-! ## `Runs` forms -/

section RunsForms

variable {K : Type} [DecidableEq K]

theorem runs_park {r p : K} (hrp : r ≠ p) (es rest : List Sym) (S : K → List Sym)
    (hes : MarkFree es) (hrest : FrameTail rest) (hS : S r = es ++ rest) :
    Runs (park r p) S
      (Function.update (Function.update S r rest) p (es.reverse ++ Sym.mark :: S p))
      (fun _ => True) (3 * es.length + 5) :=
  Runs.of_eval fun v => ⟨_, _, park_eval hrp [] v es rest S hes hrest hS, trivial, le_rfl⟩

theorem runs_unpark {p r : K} (hpr : p ≠ r) (es pt : List Sym) (S : K → List Sym)
    (hes : MarkFree es) (hS : S p = es.reverse ++ Sym.mark :: pt) :
    Runs (unpark p r) S (Function.update (Function.update S p pt) r (es ++ S r)) (fun _ => True)
      (3 * es.length + 2) :=
  Runs.of_eval fun v => ⟨_, _, unpark_eval hpr [] v es pt S hes hS, trivial, le_rfl⟩

theorem runs_protect (k : K) (S : K → List Sym) :
    Runs (protect k) S (Function.update S k (Sym.mark :: S k)) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, by
    have h := Eval.push ([] : List (SProg K)) k (fun _ => Sym.mark) v S
    exact h, trivial, le_rfl⟩

theorem runs_unprotect (k : K) (S : K → List Sym) (tl : List Sym) (hS : S k = Sym.mark :: tl) :
    Runs (unprotect k) S (Function.update S k tl) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨some Sym.mark, 1, by
    have h := Eval.pop ([] : List (SProg K)) k (fun _ o => o) v S
    rw [hS] at h
    exact h, trivial, le_rfl⟩

end RunsForms

/-! ## Calls with parking and protection -/

section Calls

variable {K σ : Type} [DecidableEq K]

/-- **Call with parking**: `park r p ; protect p ; child ; unprotect p ; unpark p r`, the macros
reaching the symbol register through the lens `l`. -/
def parkCall (l : Lens σ (Option Sym)) (r p : K) (child : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq ((park r p).liftRegs l) (.seq ((protect p).liftRegs l) (.seq child
    (.seq ((unprotect p).liftRegs l) ((unpark p r).liftRegs l))))

/-- **Call with protection**: `protect k ; child ; unprotect k`. -/
def protectCall (l : Lens σ (Option Sym)) (k : K) (child : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq ((protect k).liftRegs l) (.seq child ((unprotect k).liftRegs l))

omit [DecidableEq K] in
theorem closed_parkCall (l : Lens σ (Option Sym)) (r p : K) {child : Prog K (fun _ => Sym) σ}
    (hc : child.Closed) : (parkCall l r p child).Closed :=
  ⟨WP.W9comp.closed_liftRegs l (closed_park r p),
    WP.W9comp.closed_liftRegs l (closed_protect p), hc,
    WP.W9comp.closed_liftRegs l (closed_unprotect p), WP.W9comp.closed_liftRegs l (closed_unpark p r)⟩

omit [DecidableEq K] in
theorem closed_protectCall (l : Lens σ (Option Sym)) (k : K) {child : Prog K (fun _ => Sym) σ}
    (hc : child.Closed) : (protectCall l k child).Closed :=
  ⟨WP.W9comp.closed_liftRegs l (closed_protect k), hc,
    WP.W9comp.closed_liftRegs l (closed_unprotect k)⟩

/-- **The parking rule.** The parent's stack `r` holds a mark-free block `es` above its frame tail
`rest`. The child runs with `r = rest` and with the parking stack holding
`mark :: es.reverse ++ mark :: (old p)` (both frame tails); it may change `r` arbitrarily (for
example push its result on it) but must leave `p` as it found it. Then the parked call puts `es`
back on top of whatever the child left on `r` and restores the old content of `p`; every other stack
is as the child left it. The overhead `6·|es| + 9` does not depend on any tail. -/
theorem runsIn_parkCall {ρ : List (Prog K (fun _ => Sym) σ)} (l : Lens σ (Option Sym)) {r p : K}
    (hrp : r ≠ p) {child : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (es rest : List Sym) (hes : MarkFree es) (hrest : FrameTail rest) (hSr : S r = es ++ rest)
    (hchild : RunsIn ρ child
      (Function.update (Function.update S r rest) p (Sym.mark :: (es.reverse ++ Sym.mark :: S p)))
      S' Q T)
    (hp' : S' p = Sym.mark :: (es.reverse ++ Sym.mark :: S p)) :
    RunsIn ρ (parkCall l r p child) S (Function.update (Function.update S' p (S p)) r (es ++ S' r))
      (fun _ => True) (T + 6 * es.length + 9) := by
  have e1 := RunsIn.of_runs_liftRegs l (runs_park hrp es rest S hes hrest hSr) (closed_park r p) ρ
  set S1 := Function.update (Function.update S r rest) p (es.reverse ++ Sym.mark :: S p) with hS1
  have e2 := RunsIn.of_runs_liftRegs l (runs_protect p S1) (closed_protect p) ρ
  have hS2 : Function.update S1 p (Sym.mark :: S1 p) =
      Function.update (Function.update S r rest) p (Sym.mark :: (es.reverse ++ Sym.mark :: S p)) := by
    rw [hS1, Function.update_self, Function.update_idem]
  rw [hS2] at e2
  have e4 := RunsIn.of_runs_liftRegs l (runs_unprotect p S' _ hp') (closed_unprotect p) ρ
  have e5 := RunsIn.of_runs_liftRegs l
    (runs_unpark (Ne.symm hrp) es (S p) (Function.update S' p (es.reverse ++ Sym.mark :: S p)) hes
      (Function.update_self _ _ _))
    (closed_unpark p r) ρ
  have hfin : Function.update (Function.update (Function.update S' p (es.reverse ++ Sym.mark :: S p))
      p (S p)) r (es ++ Function.update S' p (es.reverse ++ Sym.mark :: S p) r) =
      Function.update (Function.update S' p (S p)) r (es ++ S' r) := by
    rw [Function.update_idem, Function.update_of_ne hrp]
  rw [hfin] at e5
  refine RunsIn.mono (RunsIn.seq e1 (RunsIn.seq e2 (RunsIn.seq hchild (RunsIn.seq e4 e5))))
    (fun _ _ => trivial) ?_
  omega

/-- **The protection rule.** The child runs with a `mark` on top of `k` (so the old content of `k`
is a frame tail for it) and must leave that `mark` stack as it found it; the old content of `k` is
restored after the call. The overhead is `2`. -/
theorem runsIn_protectCall {ρ : List (Prog K (fun _ => Sym) σ)} (l : Lens σ (Option Sym)) (k : K)
    {child : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hchild : RunsIn ρ child (Function.update S k (Sym.mark :: S k)) S' Q T)
    (hk' : S' k = Sym.mark :: S k) :
    RunsIn ρ (protectCall l k child) S (Function.update S' k (S k)) (fun _ => True) (T + 2) := by
  have e1 := RunsIn.of_runs_liftRegs l (runs_protect k S) (closed_protect k) ρ
  have e3 := RunsIn.of_runs_liftRegs l (runs_unprotect k S' (S k) hk') (closed_unprotect k) ρ
  refine RunsIn.mono (RunsIn.seq e1 (RunsIn.seq hchild e3)) (fun _ _ => trivial) ?_
  omega

end Calls

#assert_std_axioms closed_moveToMark closed_park closed_unpark closed_protect closed_unprotect
  moveToMark_eval park_eval unpark_eval runs_park runs_unpark runs_protect runs_unprotect
  closed_parkCall closed_protectCall runsIn_parkCall runsIn_protectCall

end SubNLogN.Machine.Calculus
