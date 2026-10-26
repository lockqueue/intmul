/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Frame

/-!
# Framed procedure calculus: the elementary framing passes (`Calculus/FramePass.lean`)

Direct `Prog` programs over one `Option Sym` register for guarded tape-transfer passes, with
a delimiter (guard) symbol `g` that ends the current segment. Each pass stops when it peeks the
guard and never pops it.

* `passM g src dst` (Pass M, move a segment reversing it): cost exactly `4n + 2`.
* `passF g src d₁ d₂` (Pass F, fork a segment to two destinations, both reversed): `5n + 2`.
* `passE g src` (Pass E, erase the segment): `3n + 2`.
* `passS g src tmp dst` (Pass S, orientation-preserving transfer via a guarded temporary):
  `8n + 4`.
* `passC g src tmp dst` (Pass C, orientation-preserving copy, source restored): `9n + 4`.

Each comes as an exact `Runs` fact for **arbitrary** stacks (`runs_passM`, …; the guard and the
content below it are arbitrary) and as a protected-tail judgment for **all** tails on all stacks
(`framed_passM`, …, class `fun _ _ => True`, any environment). The latter is the extensional
`FramedRunsIn` (no `SafeEval` access certificate is proved here; see `Calculus/Frame.lean`).
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

section Programs

variable {K : Type}

/-- Loop guard of the passes: the register holds something other than `some g`. -/
def notG (g : Sym) (r : Option Sym) : Bool := decide (r ≠ some g)

/-- Body of Pass M: move one symbol from `src` to `dst`, then look at the next one. -/
def passMBody (src dst : K) : SProg K := .seq (popR src) (.seq (pushR dst) (peekR src))

/-- **Pass M**: move the segment of `src` above the guard `g` onto `dst` (reversed). -/
def passM (g : Sym) (src dst : K) : SProg K := .seq (peekR src) (.loop (notG g) (passMBody src dst))

/-- Body of Pass F: move one symbol from `src` to both `d₁` and `d₂`. -/
def passFBody (src d₁ d₂ : K) : SProg K :=
  .seq (popR src) (.seq (pushR d₁) (.seq (pushR d₂) (peekR src)))

/-- **Pass F**: fork the segment of `src` above the guard `g` onto `d₁` and `d₂` (both reversed). -/
def passF (g : Sym) (src d₁ d₂ : K) : SProg K :=
  .seq (peekR src) (.loop (notG g) (passFBody src d₁ d₂))

/-- Body of Pass E: drop one symbol of `src`. -/
def passEBody (src : K) : SProg K := .seq (popR src) (peekR src)

/-- **Pass E**: erase the segment of `src` above the guard `g`. -/
def passE (g : Sym) (src : K) : SProg K := .seq (peekR src) (.loop (notG g) (passEBody src))

/-- **Pass S**: transfer the segment of `src` above `g` onto `dst` in the same orientation, through
`tmp` (whose top is a guard `g`). -/
def passS (g : Sym) (src tmp dst : K) : SProg K := .seq (passM g src tmp) (passM g tmp dst)

/-- **Pass C**: copy the segment of `src` above `g` onto `dst` in the same orientation, restoring
`src`, through `tmp` (whose top is a guard `g`). -/
def passC (g : Sym) (src tmp dst : K) : SProg K := .seq (passM g src tmp) (passF g tmp src dst)

theorem closed_passM (g : Sym) (src dst : K) : (passM g src dst).Closed := by
  simp [passM, passMBody, popR, pushR, peekR, Prog.Closed, Prog.FreeBelow]

theorem closed_passF (g : Sym) (src d₁ d₂ : K) : (passF g src d₁ d₂).Closed := by
  simp [passF, passFBody, popR, pushR, peekR, Prog.Closed, Prog.FreeBelow]

theorem closed_passE (g : Sym) (src : K) : (passE g src).Closed := by
  simp [passE, passEBody, popR, peekR, Prog.Closed, Prog.FreeBelow]

theorem closed_passS (g : Sym) (src tmp dst : K) : (passS g src tmp dst).Closed :=
  ⟨closed_passM g src tmp, closed_passM g tmp dst⟩

theorem closed_passC (g : Sym) (src tmp dst : K) : (passC g src tmp dst).Closed :=
  ⟨closed_passM g src tmp, closed_passF g tmp src dst⟩

end Programs

section Eval

variable {K : Type} [DecidableEq K]

theorem notG_self (g : Sym) : notG g (some g) = false := by simp [notG]

theorem notG_of_ne {g x : Sym} (h : x ≠ g) : notG g (some x) = true := by simp [notG, h]

/-- The loop of Pass M, exact. -/
theorem passM_loop_eval {g : Sym} {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) :
    ∀ (xs ts : List Sym) (S : K → List Sym), g ∉ xs → S src = xs ++ g :: ts →
      Eval ρ (.loop (notG g) (passMBody src dst)) ⟨(xs ++ g :: ts).head?, S⟩
        ⟨some g, Function.update (Function.update S src (g :: ts)) dst (xs.reverse ++ S dst)⟩
        (4 * xs.length + 1)
  | [], ts, S, _, hS => by
    refine (Eval.loop_false (notG_self g)).of_eq ?_ rfl
    have hS' : S src = g :: ts := hS
    show (⟨some g, S⟩ : SSt K) = ⟨some g, Function.update (Function.update S src (g :: ts))
      dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: xs, ts, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self)
    have hg' : g ∉ xs := fun h => hg (List.mem_cons_of_mem x h)
    have hS' : S src = x :: (xs ++ g :: ts) := hS
    have hpop : Eval ρ (popR src) ⟨some x, S⟩
        ⟨some x, Function.update S src (xs ++ g :: ts)⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) (some x) S).of_eq ?_ rfl
      simp only [hS', List.head?_cons, List.tail_cons]
    have hpush : Eval ρ (pushR dst) ⟨some x, Function.update S src (xs ++ g :: ts)⟩
        ⟨some x, Function.update (Function.update S src (xs ++ g :: ts)) dst (x :: S dst)⟩ 1 := by
      refine (Eval.push ρ dst (fun r => r.getD .sep) (some x) _).of_eq ?_ rfl
      simp only [Function.update_of_ne hne.symm, Option.getD_some]
    have hsrc1 : (Function.update (Function.update S src (xs ++ g :: ts)) dst (x :: S dst)) src =
        xs ++ g :: ts := by
      rw [Function.update_of_ne hne, Function.update_self]
    have hpeek : Eval ρ (peekR src)
        ⟨some x, Function.update (Function.update S src (xs ++ g :: ts)) dst (x :: S dst)⟩
        ⟨(xs ++ g :: ts).head?,
          Function.update (Function.update S src (xs ++ g :: ts)) dst (x :: S dst)⟩ 1 := by
      refine (Eval.peek ρ src (fun _ o => o) (some x) _).of_eq ?_ rfl
      simp only [hsrc1]
    have ih := passM_loop_eval hne ρ xs ts _ hg' hsrc1
    refine (Eval.loop_true (notG_of_ne hx) (Eval.seq hpop (Eval.seq hpush hpeek)) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **Pass M**, exact: cost `4n + 2`. -/
theorem passM_eval {g : Sym} {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (xs ts : List Sym) (S : K → List Sym) (hg : g ∉ xs) (hS : S src = xs ++ g :: ts) :
    Eval ρ (passM g src dst) ⟨v, S⟩
      ⟨some g, Function.update (Function.update S src (g :: ts)) dst (xs.reverse ++ S dst)⟩
      (4 * xs.length + 2) := by
  have h1 : Eval ρ (peekR src) ⟨v, S⟩ ⟨(xs ++ g :: ts).head?, S⟩ 1 := by
    refine (Eval.peek ρ src (fun _ o => o) v S).of_eq ?_ rfl
    simp only [hS]
  exact (Eval.seq h1 (passM_loop_eval hne ρ xs ts S hg hS)).of_eq rfl (by omega)

/-- The loop of Pass F, exact. -/
theorem passF_loop_eval {g : Sym} {src d₁ d₂ : K} (h1 : src ≠ d₁) (h2 : src ≠ d₂) (h12 : d₁ ≠ d₂)
    (ρ : List (SProg K)) :
    ∀ (xs ts : List Sym) (S : K → List Sym), g ∉ xs → S src = xs ++ g :: ts →
      Eval ρ (.loop (notG g) (passFBody src d₁ d₂)) ⟨(xs ++ g :: ts).head?, S⟩
        ⟨some g, Function.update (Function.update (Function.update S src (g :: ts))
          d₁ (xs.reverse ++ S d₁)) d₂ (xs.reverse ++ S d₂)⟩
        (5 * xs.length + 1)
  | [], ts, S, _, hS => by
    refine (Eval.loop_false (notG_self g)).of_eq ?_ rfl
    have hS' : S src = g :: ts := hS
    show (⟨some g, S⟩ : SSt K) = ⟨some g, Function.update (Function.update
      (Function.update S src (g :: ts)) d₁ ([].reverse ++ S d₁)) d₂ ([].reverse ++ S d₂)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self,
      List.nil_append, Function.update_eq_self]
  | x :: xs, ts, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self)
    have hg' : g ∉ xs := fun h => hg (List.mem_cons_of_mem x h)
    have hS' : S src = x :: (xs ++ g :: ts) := hS
    have hpop : Eval ρ (popR src) ⟨some x, S⟩
        ⟨some x, Function.update S src (xs ++ g :: ts)⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) (some x) S).of_eq ?_ rfl
      simp only [hS', List.head?_cons, List.tail_cons]
    have hpush1 : Eval ρ (pushR d₁) ⟨some x, Function.update S src (xs ++ g :: ts)⟩
        ⟨some x, Function.update (Function.update S src (xs ++ g :: ts)) d₁ (x :: S d₁)⟩ 1 := by
      refine (Eval.push ρ d₁ (fun r => r.getD .sep) (some x) _).of_eq ?_ rfl
      simp only [Function.update_of_ne h1.symm, Option.getD_some]
    have hpush2 : Eval ρ (pushR d₂)
        ⟨some x, Function.update (Function.update S src (xs ++ g :: ts)) d₁ (x :: S d₁)⟩
        ⟨some x, Function.update (Function.update (Function.update S src (xs ++ g :: ts))
          d₁ (x :: S d₁)) d₂ (x :: S d₂)⟩ 1 := by
      refine (Eval.push ρ d₂ (fun r => r.getD .sep) (some x) _).of_eq ?_ rfl
      simp only [Function.update_of_ne h12.symm, Function.update_of_ne h2.symm, Option.getD_some]
    have hsrc1 : (Function.update (Function.update (Function.update S src (xs ++ g :: ts))
        d₁ (x :: S d₁)) d₂ (x :: S d₂)) src = xs ++ g :: ts := by
      rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self]
    have hpeek : Eval ρ (peekR src)
        ⟨some x, Function.update (Function.update (Function.update S src (xs ++ g :: ts))
          d₁ (x :: S d₁)) d₂ (x :: S d₂)⟩
        ⟨(xs ++ g :: ts).head?, Function.update (Function.update
          (Function.update S src (xs ++ g :: ts)) d₁ (x :: S d₁)) d₂ (x :: S d₂)⟩ 1 := by
      refine (Eval.peek ρ src (fun _ o => o) (some x) _).of_eq ?_ rfl
      simp only [hsrc1]
    have ih := passF_loop_eval h1 h2 h12 ρ xs ts _ hg' hsrc1
    refine (Eval.loop_true (notG_of_ne hx)
      (Eval.seq hpop (Eval.seq hpush1 (Eval.seq hpush2 hpeek))) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **Pass F**, exact: cost `5n + 2`. -/
theorem passF_eval {g : Sym} {src d₁ d₂ : K} (h1 : src ≠ d₁) (h2 : src ≠ d₂) (h12 : d₁ ≠ d₂)
    (ρ : List (SProg K)) (v : Option Sym) (xs ts : List Sym) (S : K → List Sym) (hg : g ∉ xs)
    (hS : S src = xs ++ g :: ts) :
    Eval ρ (passF g src d₁ d₂) ⟨v, S⟩
      ⟨some g, Function.update (Function.update (Function.update S src (g :: ts))
        d₁ (xs.reverse ++ S d₁)) d₂ (xs.reverse ++ S d₂)⟩
      (5 * xs.length + 2) := by
  have h0 : Eval ρ (peekR src) ⟨v, S⟩ ⟨(xs ++ g :: ts).head?, S⟩ 1 := by
    refine (Eval.peek ρ src (fun _ o => o) v S).of_eq ?_ rfl
    simp only [hS]
  exact (Eval.seq h0 (passF_loop_eval h1 h2 h12 ρ xs ts S hg hS)).of_eq rfl (by omega)

/-- The loop of Pass E, exact. -/
theorem passE_loop_eval {g : Sym} {src : K} (ρ : List (SProg K)) :
    ∀ (xs ts : List Sym) (S : K → List Sym), g ∉ xs → S src = xs ++ g :: ts →
      Eval ρ (.loop (notG g) (passEBody src)) ⟨(xs ++ g :: ts).head?, S⟩
        ⟨some g, Function.update S src (g :: ts)⟩ (3 * xs.length + 1)
  | [], ts, S, _, hS => by
    refine (Eval.loop_false (notG_self g)).of_eq ?_ rfl
    have hS' : S src = g :: ts := hS
    show (⟨some g, S⟩ : SSt K) = ⟨some g, Function.update S src (g :: ts)⟩
    rw [← hS', Function.update_eq_self]
  | x :: xs, ts, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self)
    have hg' : g ∉ xs := fun h => hg (List.mem_cons_of_mem x h)
    have hS' : S src = x :: (xs ++ g :: ts) := hS
    have hpop : Eval ρ (popR src) ⟨some x, S⟩
        ⟨some x, Function.update S src (xs ++ g :: ts)⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) (some x) S).of_eq ?_ rfl
      simp only [hS', List.head?_cons, List.tail_cons]
    have hsrc1 : (Function.update S src (xs ++ g :: ts)) src = xs ++ g :: ts :=
      Function.update_self _ _ _
    have hpeek : Eval ρ (peekR src) ⟨some x, Function.update S src (xs ++ g :: ts)⟩
        ⟨(xs ++ g :: ts).head?, Function.update S src (xs ++ g :: ts)⟩ 1 := by
      refine (Eval.peek ρ src (fun _ o => o) (some x) _).of_eq ?_ rfl
      simp only [hsrc1]
    have ih := passE_loop_eval ρ xs ts _ hg' hsrc1
    refine (Eval.loop_true (notG_of_ne hx) (Eval.seq hpop hpeek) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **Pass E**, exact: cost `3n + 2`. -/
theorem passE_eval {g : Sym} {src : K} (ρ : List (SProg K)) (v : Option Sym) (xs ts : List Sym)
    (S : K → List Sym) (hg : g ∉ xs) (hS : S src = xs ++ g :: ts) :
    Eval ρ (passE g src) ⟨v, S⟩ ⟨some g, Function.update S src (g :: ts)⟩ (3 * xs.length + 2) := by
  have h0 : Eval ρ (peekR src) ⟨v, S⟩ ⟨(xs ++ g :: ts).head?, S⟩ 1 := by
    refine (Eval.peek ρ src (fun _ o => o) v S).of_eq ?_ rfl
    simp only [hS]
  exact (Eval.seq h0 (passE_loop_eval ρ xs ts S hg hS)).of_eq rfl (by omega)

/-! ## `Runs` forms: arbitrary stacks, arbitrary content below the guard -/

theorem runs_passM {g : Sym} {src dst : K} (hne : src ≠ dst) (xs ts : List Sym) (hg : g ∉ xs)
    (S : K → List Sym) (hS : S src = xs ++ g :: ts) :
    Runs (passM g src dst) S
      (Function.update (Function.update S src (g :: ts)) dst (xs.reverse ++ S dst))
      (fun r => r = some g) (4 * xs.length + 2) :=
  Runs.of_eval fun v => ⟨some g, _, passM_eval hne [] v xs ts S hg hS, rfl, le_rfl⟩

theorem runs_passF {g : Sym} {src d₁ d₂ : K} (h1 : src ≠ d₁) (h2 : src ≠ d₂) (h12 : d₁ ≠ d₂)
    (xs ts : List Sym) (hg : g ∉ xs) (S : K → List Sym) (hS : S src = xs ++ g :: ts) :
    Runs (passF g src d₁ d₂) S
      (Function.update (Function.update (Function.update S src (g :: ts))
        d₁ (xs.reverse ++ S d₁)) d₂ (xs.reverse ++ S d₂))
      (fun r => r = some g) (5 * xs.length + 2) :=
  Runs.of_eval fun v => ⟨some g, _, passF_eval h1 h2 h12 [] v xs ts S hg hS, rfl, le_rfl⟩

theorem runs_passE {g : Sym} {src : K} (xs ts : List Sym) (hg : g ∉ xs) (S : K → List Sym)
    (hS : S src = xs ++ g :: ts) :
    Runs (passE g src) S (Function.update S src (g :: ts)) (fun r => r = some g)
      (3 * xs.length + 2) :=
  Runs.of_eval fun v => ⟨some g, _, passE_eval [] v xs ts S hg hS, rfl, le_rfl⟩

/-- **Pass S**: `src = xs ++ g :: ts` and `tmp = g :: tt` give `src = g :: ts`,
`dst = xs ++ dst` (same orientation), `tmp` unchanged; cost `8n + 4`. -/
theorem runs_passS {g : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst) (h3 : src ≠ dst)
    (xs ts tt : List Sym) (hg : g ∉ xs) (S : K → List Sym) (hS : S src = xs ++ g :: ts)
    (hT : S tmp = g :: tt) :
    Runs (passS g src tmp dst) S
      (Function.update (Function.update S src (g :: ts)) dst (xs ++ S dst))
      (fun r => r = some g) (8 * xs.length + 4) := by
  have hA := runs_passM h1 xs ts hg S hS
  have hT1 : (Function.update (Function.update S src (g :: ts)) tmp (xs.reverse ++ S tmp)) tmp =
      xs.reverse ++ g :: tt := by
    rw [Function.update_self, hT]
  have hg' : g ∉ xs.reverse := by rwa [List.mem_reverse]
  have hB := runs_passM h2 xs.reverse tt hg' _ hT1
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.seq (RunsIn.iff_runs.mpr hA)
    (RunsIn.iff_runs.mpr hB)) ?_ (by simp only [List.length_reverse]; omega))
  funext k
  simp only [Function.update_apply, List.reverse_reverse]
  split_ifs <;> simp_all

/-- **Pass C**: `src = xs ++ g :: ts` and `tmp = g :: tt` give `dst = xs ++ dst` (same
orientation), `src` and `tmp` restored; cost `9n + 4`. -/
theorem runs_passC {g : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst) (h3 : src ≠ dst)
    (xs ts tt : List Sym) (hg : g ∉ xs) (S : K → List Sym) (hS : S src = xs ++ g :: ts)
    (hT : S tmp = g :: tt) :
    Runs (passC g src tmp dst) S (Function.update S dst (xs ++ S dst))
      (fun r => r = some g) (9 * xs.length + 4) := by
  have hA := runs_passM h1 xs ts hg S hS
  have hT1 : (Function.update (Function.update S src (g :: ts)) tmp (xs.reverse ++ S tmp)) tmp =
      xs.reverse ++ g :: tt := by
    rw [Function.update_self, hT]
  have hg' : g ∉ xs.reverse := by rwa [List.mem_reverse]
  have hB := runs_passF h1.symm h2 h3 xs.reverse tt hg' _ hT1
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.seq (RunsIn.iff_runs.mpr hA)
    (RunsIn.iff_runs.mpr hB)) ?_ (by simp only [List.length_reverse]; omega))
  funext k
  simp only [Function.update_apply, List.reverse_reverse]
  split_ifs <;> simp_all

/-! ## Protected-tail forms: every tail on every stack, any environment -/

theorem framed_passM {g : Sym} {src dst : K} (hne : src ≠ dst) (xs : List Sym) (hg : g ∉ xs)
    (S : K → List Sym) (hS : S src = xs ++ [g]) (ρ : List (SProg K)) :
    FramedRunsIn (fun _ _ => True) ρ (passM g src dst) S
      (Function.update (Function.update S src [g]) dst (xs.reverse ++ S dst))
      (fun r => r = some g) (4 * xs.length + 2) := by
  refine FramedRunsIn.of_runs (closed_passM g src dst) (fun τ _ => ?_) ρ
  have h := runs_passM hne xs (τ src) hg (appendTail S τ) (by simp [hS])
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.iff_runs.mpr h) ?_ le_rfl)
  funext k
  simp only [appendTail_apply, Function.update_apply]
  split_ifs <;> simp_all

theorem framed_passF {g : Sym} {src d₁ d₂ : K} (h1 : src ≠ d₁) (h2 : src ≠ d₂) (h12 : d₁ ≠ d₂)
    (xs : List Sym) (hg : g ∉ xs) (S : K → List Sym) (hS : S src = xs ++ [g])
    (ρ : List (SProg K)) :
    FramedRunsIn (fun _ _ => True) ρ (passF g src d₁ d₂) S
      (Function.update (Function.update (Function.update S src [g])
        d₁ (xs.reverse ++ S d₁)) d₂ (xs.reverse ++ S d₂))
      (fun r => r = some g) (5 * xs.length + 2) := by
  refine FramedRunsIn.of_runs (closed_passF g src d₁ d₂) (fun τ _ => ?_) ρ
  have h := runs_passF h1 h2 h12 xs (τ src) hg (appendTail S τ) (by simp [hS])
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.iff_runs.mpr h) ?_ le_rfl)
  funext k
  simp only [appendTail_apply, Function.update_apply]
  split_ifs <;> simp_all

theorem framed_passE {g : Sym} {src : K} (xs : List Sym) (hg : g ∉ xs) (S : K → List Sym)
    (hS : S src = xs ++ [g]) (ρ : List (SProg K)) :
    FramedRunsIn (fun _ _ => True) ρ (passE g src) S (Function.update S src [g])
      (fun r => r = some g) (3 * xs.length + 2) := by
  refine FramedRunsIn.of_runs (closed_passE g src) (fun τ _ => ?_) ρ
  have h := runs_passE (src := src) xs (τ src) hg (appendTail S τ) (by simp [hS])
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.iff_runs.mpr h) ?_ le_rfl)
  funext k
  simp only [appendTail_apply, Function.update_apply]
  split_ifs <;> simp_all

theorem framed_passS {g : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst) (h3 : src ≠ dst)
    (xs : List Sym) (hg : g ∉ xs) (S : K → List Sym) (hS : S src = xs ++ [g]) (hT : S tmp = [g])
    (ρ : List (SProg K)) :
    FramedRunsIn (fun _ _ => True) ρ (passS g src tmp dst) S
      (Function.update (Function.update S src [g]) dst (xs ++ S dst))
      (fun r => r = some g) (8 * xs.length + 4) := by
  refine FramedRunsIn.of_runs (closed_passS g src tmp dst) (fun τ _ => ?_) ρ
  have h := runs_passS h1 h2 h3 xs (τ src) (τ tmp) hg (appendTail S τ) (by simp [hS])
    (by simp [hT])
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.iff_runs.mpr h) ?_ le_rfl)
  funext k
  simp only [appendTail_apply, Function.update_apply]
  split_ifs <;> simp_all

theorem framed_passC {g : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst) (h3 : src ≠ dst)
    (xs : List Sym) (hg : g ∉ xs) (S : K → List Sym) (hS : S src = xs ++ [g]) (hT : S tmp = [g])
    (ρ : List (SProg K)) :
    FramedRunsIn (fun _ _ => True) ρ (passC g src tmp dst) S (Function.update S dst (xs ++ S dst))
      (fun r => r = some g) (9 * xs.length + 4) := by
  refine FramedRunsIn.of_runs (closed_passC g src tmp dst) (fun τ _ => ?_) ρ
  have h := runs_passC h1 h2 h3 xs (τ src) (τ tmp) hg (appendTail S τ) (by simp [hS])
    (by simp [hT])
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.iff_runs.mpr h) ?_ le_rfl)
  funext k
  simp only [appendTail_apply, Function.update_apply]
  split_ifs <;> simp_all

end Eval

/-! ## Single steps with protected tails -/

section Prim

variable {K : Type} [DecidableEq K]

/-- `pushC k a` with every tail on every stack: cost `1`. -/
theorem framed_pushC (k : K) (a : Sym) (S : K → List Sym) (ρ : List (SProg K)) :
    FramedRunsIn (fun _ _ => True) ρ (pushC k a) S (Function.update S k (a :: S k))
      (fun _ => True) 1 := by
  refine FramedRunsIn.of_runs (by simp [pushC, Prog.Closed, Prog.FreeBelow]) (fun τ _ => ?_) ρ
  refine Runs.of_eval fun v => ⟨v, 1, ?_, trivial, le_rfl⟩
  refine (Eval.push [] k (fun _ => a) v (appendTail S τ)).of_eq ?_ rfl
  rw [appendTail_update]
  rfl

/-- `popR k` on a non-empty local segment, with every tail on every stack: cost `1`. -/
theorem framed_popR (k : K) (a : Sym) (l : List Sym) (S : K → List Sym) (hS : S k = a :: l)
    (ρ : List (SProg K)) :
    FramedRunsIn (fun _ _ => True) ρ (popR k) S (Function.update S k l) (fun r => r = some a) 1 := by
  refine FramedRunsIn.of_runs (by simp [popR, Prog.Closed, Prog.FreeBelow]) (fun τ _ => ?_) ρ
  refine Runs.of_eval fun v => ⟨some a, 1, ?_, rfl, le_rfl⟩
  refine (Eval.pop [] k (fun _ o => o) v (appendTail S τ)).of_eq ?_ rfl
  rw [appendTail_update]
  simp [hS]

/-- `peekR k` on a non-empty local segment, with every tail on every stack: cost `1`. -/
theorem framed_peekR (k : K) (a : Sym) (l : List Sym) (S : K → List Sym) (hS : S k = a :: l)
    (ρ : List (SProg K)) :
    FramedRunsIn (fun _ _ => True) ρ (peekR k) S S (fun r => r = some a) 1 := by
  refine FramedRunsIn.of_runs (by simp [peekR, Prog.Closed, Prog.FreeBelow]) (fun τ _ => ?_) ρ
  refine Runs.of_eval fun v => ⟨some a, 1, ?_, rfl, le_rfl⟩
  refine (Eval.peek [] k (fun _ o => o) v (appendTail S τ)).of_eq ?_ rfl
  simp [hS]

end Prim

#assert_std_axioms passM_eval passF_eval passE_eval runs_passM runs_passF runs_passE runs_passS
  runs_passC framed_passM framed_passF framed_passE framed_passS framed_passC framed_pushC
  framed_popR framed_peekR

end SubNLogN.Machine.Calculus
