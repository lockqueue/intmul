/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.FramePassR
import SubNLogN.Machine.Calculus.SafePark

/-!
# Framed procedure calculus (`Calculus/FramePassSafe.lean`): boundary-safe certificates for the passes

The pass programs of `Calculus/FramePass.lean`
and `Calculus/FramePassR.lean` are boundary-safe for the framed set `fun _ => True` (every stack
framed): every `peek` and `pop` of these programs happens on a stack whose visible content is
non-empty, because each scan stops at a visible guard. Hence (`SafeRunsIn.mono_framed`) they are
safe for **every** framed set, and with `SafeRunsIn.frame_tail` they run unchanged above any
protected tails. Costs are those of the `Eval`/`Runs` facts.

* exact safe evaluations `safe_passM_eval`, `safe_passF_eval`, `safe_passE_eval` (proof clones of
  the `FramePass.lean` ones with the read premises added);
* `SafeRunsIn` forms `safe_passM`, `safe_passF`, `safe_passE`, `safe_passS`, `safe_passC`;
* safe primitives `safe_pushC`, `safe_popR`, `safe_peekR`;
* Pass R: `safe_passRBody`, `safe_passR` (record-order reversal, cost `8·|arrSyms v| + 2`).
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

section SafePasses

variable {K : Type} [DecidableEq K]

/-! ## Safe primitives -/

theorem safe_pushC (k : K) (a : Sym) (S : K → List Sym) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (pushC k a) S (Function.update S k (a :: S k)) (fun _ => True) 1 :=
  fun v => ⟨v, 1, SafeEval.push ρ k (fun _ => a) v S, trivial, le_rfl⟩

theorem safe_popR (k : K) (a : Sym) (xs : List Sym) (S : K → List Sym) (hS : S k = a :: xs)
    (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (popR k) S (Function.update S k xs) (fun r => r = some a) 1 :=
  fun v => ⟨some a, 1, (SafeEval.pop ρ k (fun _ o => o) v S (fun _ => by simp [hS])).of_eq_cost
    (by simp only [hS, List.head?_cons, List.tail_cons]) rfl, rfl, le_rfl⟩

theorem safe_peekR (k : K) (a : Sym) (xs : List Sym) (S : K → List Sym) (hS : S k = a :: xs)
    (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (peekR k) S S (fun r => r = some a) 1 :=
  fun v => ⟨some a, 1, (SafeEval.peek ρ k (fun _ o => o) v S (fun _ => by simp [hS])).of_eq_cost
    (by simp only [hS, List.head?_cons]) rfl, rfl, le_rfl⟩

/-! ## Pass M -/

theorem safe_passM_loop_eval {g : Sym} {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) :
    ∀ (xs ts : List Sym) (S : K → List Sym), g ∉ xs → S src = xs ++ g :: ts →
      SafeEval (fun _ => True) ρ (.loop (notG g) (passMBody src dst)) ⟨(xs ++ g :: ts).head?, S⟩
        ⟨some g, Function.update (Function.update S src (g :: ts)) dst (xs.reverse ++ S dst)⟩
        (4 * xs.length + 1)
  | [], ts, S, _, hS => by
    refine (SafeEval.loop_false (framed := fun _ => True) (ρ := ρ) (p := passMBody src dst)
      (s := ⟨some g, S⟩) (notG_self g)).of_eq_cost ?_ rfl
    have hS' : S src = g :: ts := hS
    show (⟨some g, S⟩ : SSt K) = ⟨some g, Function.update (Function.update S src (g :: ts))
      dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: xs, ts, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self)
    have hg' : g ∉ xs := fun h => hg (List.mem_cons_of_mem x h)
    have hS' : S src = x :: (xs ++ g :: ts) := hS
    have hpop : SafeEval (fun _ => True) ρ (popR src) ⟨some x, S⟩
        ⟨some x, Function.update S src (xs ++ g :: ts)⟩ 1 := by
      refine (SafeEval.pop ρ src (fun _ o => o) (some x) S (fun _ => by simp [hS'])).of_eq_cost
        ?_ rfl
      simp only [hS', List.head?_cons, List.tail_cons]
    have hpush : SafeEval (fun _ => True) ρ (pushR dst) ⟨some x, Function.update S src (xs ++ g :: ts)⟩
        ⟨some x, Function.update (Function.update S src (xs ++ g :: ts)) dst (x :: S dst)⟩ 1 := by
      refine (SafeEval.push ρ dst (fun r => r.getD .sep) (some x) _).of_eq_cost ?_ rfl
      simp only [Function.update_of_ne hne.symm, Option.getD_some]
    have hsrc1 : (Function.update (Function.update S src (xs ++ g :: ts)) dst (x :: S dst)) src =
        xs ++ g :: ts := by
      rw [Function.update_of_ne hne, Function.update_self]
    have hpeek : SafeEval (fun _ => True) ρ (peekR src)
        ⟨some x, Function.update (Function.update S src (xs ++ g :: ts)) dst (x :: S dst)⟩
        ⟨(xs ++ g :: ts).head?,
          Function.update (Function.update S src (xs ++ g :: ts)) dst (x :: S dst)⟩ 1 := by
      refine (SafeEval.peek ρ src (fun _ o => o) (some x) _
        (fun _ => by rw [hsrc1]; simp)).of_eq_cost ?_ rfl
      simp only [hsrc1]
    have ih := safe_passM_loop_eval hne ρ xs ts _ hg' hsrc1
    refine (SafeEval.loop_true (notG_of_ne hx) (SafeEval.seq hpop (SafeEval.seq hpush hpeek))
      ih).of_eq_cost ?_ (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **Pass M**, safe and exact. -/
theorem safe_passM_eval {g : Sym} {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K))
    (v : Option Sym) (xs ts : List Sym) (S : K → List Sym) (hg : g ∉ xs)
    (hS : S src = xs ++ g :: ts) :
    SafeEval (fun _ => True) ρ (passM g src dst) ⟨v, S⟩
      ⟨some g, Function.update (Function.update S src (g :: ts)) dst (xs.reverse ++ S dst)⟩
      (4 * xs.length + 2) := by
  have h1 : SafeEval (fun _ => True) ρ (peekR src) ⟨v, S⟩ ⟨(xs ++ g :: ts).head?, S⟩ 1 := by
    refine (SafeEval.peek ρ src (fun _ o => o) v S (fun _ => by rw [hS]; simp)).of_eq_cost ?_ rfl
    simp only [hS]
  exact (SafeEval.seq h1 (safe_passM_loop_eval hne ρ xs ts S hg hS)).of_eq_cost rfl (by omega)

theorem safe_passM {g : Sym} {src dst : K} (hne : src ≠ dst) (xs ts : List Sym) (hg : g ∉ xs)
    (S : K → List Sym) (hS : S src = xs ++ g :: ts) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passM g src dst) S
      (Function.update (Function.update S src (g :: ts)) dst (xs.reverse ++ S dst))
      (fun r => r = some g) (4 * xs.length + 2) :=
  fun v => ⟨some g, 4 * xs.length + 2, safe_passM_eval hne ρ v xs ts S hg hS, rfl, le_rfl⟩

/-! ## Pass F -/

theorem safe_passF_loop_eval {g : Sym} {src d₁ d₂ : K} (h1 : src ≠ d₁) (h2 : src ≠ d₂)
    (h12 : d₁ ≠ d₂) (ρ : List (SProg K)) :
    ∀ (xs ts : List Sym) (S : K → List Sym), g ∉ xs → S src = xs ++ g :: ts →
      SafeEval (fun _ => True) ρ (.loop (notG g) (passFBody src d₁ d₂)) ⟨(xs ++ g :: ts).head?, S⟩
        ⟨some g, Function.update (Function.update (Function.update S src (g :: ts))
          d₁ (xs.reverse ++ S d₁)) d₂ (xs.reverse ++ S d₂)⟩
        (5 * xs.length + 1)
  | [], ts, S, _, hS => by
    refine (SafeEval.loop_false (framed := fun _ => True) (ρ := ρ) (p := passFBody src d₁ d₂)
      (s := ⟨some g, S⟩) (notG_self g)).of_eq_cost ?_ rfl
    have hS' : S src = g :: ts := hS
    show (⟨some g, S⟩ : SSt K) = ⟨some g, Function.update (Function.update
      (Function.update S src (g :: ts)) d₁ ([].reverse ++ S d₁)) d₂ ([].reverse ++ S d₂)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self,
      List.nil_append, Function.update_eq_self]
  | x :: xs, ts, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self)
    have hg' : g ∉ xs := fun h => hg (List.mem_cons_of_mem x h)
    have hS' : S src = x :: (xs ++ g :: ts) := hS
    have hpop : SafeEval (fun _ => True) ρ (popR src) ⟨some x, S⟩
        ⟨some x, Function.update S src (xs ++ g :: ts)⟩ 1 := by
      refine (SafeEval.pop ρ src (fun _ o => o) (some x) S (fun _ => by simp [hS'])).of_eq_cost
        ?_ rfl
      simp only [hS', List.head?_cons, List.tail_cons]
    have hpush1 : SafeEval (fun _ => True) ρ (pushR d₁)
        ⟨some x, Function.update S src (xs ++ g :: ts)⟩
        ⟨some x, Function.update (Function.update S src (xs ++ g :: ts)) d₁ (x :: S d₁)⟩ 1 := by
      refine (SafeEval.push ρ d₁ (fun r => r.getD .sep) (some x) _).of_eq_cost ?_ rfl
      simp only [Function.update_of_ne h1.symm, Option.getD_some]
    have hpush2 : SafeEval (fun _ => True) ρ (pushR d₂)
        ⟨some x, Function.update (Function.update S src (xs ++ g :: ts)) d₁ (x :: S d₁)⟩
        ⟨some x, Function.update (Function.update (Function.update S src (xs ++ g :: ts))
          d₁ (x :: S d₁)) d₂ (x :: S d₂)⟩ 1 := by
      refine (SafeEval.push ρ d₂ (fun r => r.getD .sep) (some x) _).of_eq_cost ?_ rfl
      simp only [Function.update_of_ne h12.symm, Function.update_of_ne h2.symm, Option.getD_some]
    have hsrc1 : (Function.update (Function.update (Function.update S src (xs ++ g :: ts))
        d₁ (x :: S d₁)) d₂ (x :: S d₂)) src = xs ++ g :: ts := by
      rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self]
    have hpeek : SafeEval (fun _ => True) ρ (peekR src)
        ⟨some x, Function.update (Function.update (Function.update S src (xs ++ g :: ts))
          d₁ (x :: S d₁)) d₂ (x :: S d₂)⟩
        ⟨(xs ++ g :: ts).head?, Function.update (Function.update
          (Function.update S src (xs ++ g :: ts)) d₁ (x :: S d₁)) d₂ (x :: S d₂)⟩ 1 := by
      refine (SafeEval.peek ρ src (fun _ o => o) (some x) _
        (fun _ => by rw [hsrc1]; simp)).of_eq_cost ?_ rfl
      simp only [hsrc1]
    have ih := safe_passF_loop_eval h1 h2 h12 ρ xs ts _ hg' hsrc1
    refine (SafeEval.loop_true (notG_of_ne hx)
      (SafeEval.seq hpop (SafeEval.seq hpush1 (SafeEval.seq hpush2 hpeek))) ih).of_eq_cost ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **Pass F**, safe and exact. -/
theorem safe_passF_eval {g : Sym} {src d₁ d₂ : K} (h1 : src ≠ d₁) (h2 : src ≠ d₂) (h12 : d₁ ≠ d₂)
    (ρ : List (SProg K)) (v : Option Sym) (xs ts : List Sym) (S : K → List Sym) (hg : g ∉ xs)
    (hS : S src = xs ++ g :: ts) :
    SafeEval (fun _ => True) ρ (passF g src d₁ d₂) ⟨v, S⟩
      ⟨some g, Function.update (Function.update (Function.update S src (g :: ts))
        d₁ (xs.reverse ++ S d₁)) d₂ (xs.reverse ++ S d₂)⟩
      (5 * xs.length + 2) := by
  have h0 : SafeEval (fun _ => True) ρ (peekR src) ⟨v, S⟩ ⟨(xs ++ g :: ts).head?, S⟩ 1 := by
    refine (SafeEval.peek ρ src (fun _ o => o) v S (fun _ => by rw [hS]; simp)).of_eq_cost ?_ rfl
    simp only [hS]
  exact (SafeEval.seq h0 (safe_passF_loop_eval h1 h2 h12 ρ xs ts S hg hS)).of_eq_cost rfl
    (by omega)

theorem safe_passF {g : Sym} {src d₁ d₂ : K} (h1 : src ≠ d₁) (h2 : src ≠ d₂) (h12 : d₁ ≠ d₂)
    (xs ts : List Sym) (hg : g ∉ xs) (S : K → List Sym) (hS : S src = xs ++ g :: ts)
    (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passF g src d₁ d₂) S
      (Function.update (Function.update (Function.update S src (g :: ts))
        d₁ (xs.reverse ++ S d₁)) d₂ (xs.reverse ++ S d₂))
      (fun r => r = some g) (5 * xs.length + 2) :=
  fun v => ⟨some g, 5 * xs.length + 2, safe_passF_eval h1 h2 h12 ρ v xs ts S hg hS, rfl, le_rfl⟩

/-! ## Pass E -/

theorem safe_passE_loop_eval {g : Sym} {src : K} (ρ : List (SProg K)) :
    ∀ (xs ts : List Sym) (S : K → List Sym), g ∉ xs → S src = xs ++ g :: ts →
      SafeEval (fun _ => True) ρ (.loop (notG g) (passEBody src)) ⟨(xs ++ g :: ts).head?, S⟩
        ⟨some g, Function.update S src (g :: ts)⟩ (3 * xs.length + 1)
  | [], ts, S, _, hS => by
    refine (SafeEval.loop_false (framed := fun _ => True) (ρ := ρ) (p := passEBody src)
      (s := ⟨some g, S⟩) (notG_self g)).of_eq_cost ?_ rfl
    have hS' : S src = g :: ts := hS
    show (⟨some g, S⟩ : SSt K) = ⟨some g, Function.update S src (g :: ts)⟩
    rw [← hS', Function.update_eq_self]
  | x :: xs, ts, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self)
    have hg' : g ∉ xs := fun h => hg (List.mem_cons_of_mem x h)
    have hS' : S src = x :: (xs ++ g :: ts) := hS
    have hpop : SafeEval (fun _ => True) ρ (popR src) ⟨some x, S⟩
        ⟨some x, Function.update S src (xs ++ g :: ts)⟩ 1 := by
      refine (SafeEval.pop ρ src (fun _ o => o) (some x) S (fun _ => by simp [hS'])).of_eq_cost
        ?_ rfl
      simp only [hS', List.head?_cons, List.tail_cons]
    have hsrc1 : (Function.update S src (xs ++ g :: ts)) src = xs ++ g :: ts :=
      Function.update_self _ _ _
    have hpeek : SafeEval (fun _ => True) ρ (peekR src) ⟨some x, Function.update S src (xs ++ g :: ts)⟩
        ⟨(xs ++ g :: ts).head?, Function.update S src (xs ++ g :: ts)⟩ 1 := by
      refine (SafeEval.peek ρ src (fun _ o => o) (some x) _
        (fun _ => by rw [hsrc1]; simp)).of_eq_cost ?_ rfl
      simp only [hsrc1]
    have ih := safe_passE_loop_eval ρ xs ts _ hg' hsrc1
    refine (SafeEval.loop_true (notG_of_ne hx) (SafeEval.seq hpop hpeek) ih).of_eq_cost ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **Pass E**, safe and exact. -/
theorem safe_passE_eval {g : Sym} {src : K} (ρ : List (SProg K)) (v : Option Sym)
    (xs ts : List Sym) (S : K → List Sym) (hg : g ∉ xs) (hS : S src = xs ++ g :: ts) :
    SafeEval (fun _ => True) ρ (passE g src) ⟨v, S⟩ ⟨some g, Function.update S src (g :: ts)⟩
      (3 * xs.length + 2) := by
  have h0 : SafeEval (fun _ => True) ρ (peekR src) ⟨v, S⟩ ⟨(xs ++ g :: ts).head?, S⟩ 1 := by
    refine (SafeEval.peek ρ src (fun _ o => o) v S (fun _ => by rw [hS]; simp)).of_eq_cost ?_ rfl
    simp only [hS]
  exact (SafeEval.seq h0 (safe_passE_loop_eval ρ xs ts S hg hS)).of_eq_cost rfl (by omega)

theorem safe_passE {g : Sym} {src : K} (xs ts : List Sym) (hg : g ∉ xs) (S : K → List Sym)
    (hS : S src = xs ++ g :: ts) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passE g src) S (Function.update S src (g :: ts))
      (fun r => r = some g) (3 * xs.length + 2) :=
  fun v => ⟨some g, 3 * xs.length + 2, safe_passE_eval ρ v xs ts S hg hS, rfl, le_rfl⟩

/-! ## Passes S and C -/

theorem safe_passS {g : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst) (h3 : src ≠ dst)
    (xs ts tt : List Sym) (hg : g ∉ xs) (S : K → List Sym) (hS : S src = xs ++ g :: ts)
    (hT : S tmp = g :: tt) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passS g src tmp dst) S
      (Function.update (Function.update S src (g :: ts)) dst (xs ++ S dst))
      (fun r => r = some g) (8 * xs.length + 4) := by
  have hA := safe_passM h1 xs ts hg S hS ρ
  have hT1 : (Function.update (Function.update S src (g :: ts)) tmp (xs.reverse ++ S tmp)) tmp =
      xs.reverse ++ g :: tt := by
    rw [Function.update_self, hT]
  have hg' : g ∉ xs.reverse := by rwa [List.mem_reverse]
  have hB := safe_passM h2 xs.reverse tt hg' _ hT1 ρ
  refine SafeRunsIn.congr (SafeRunsIn.seq hA hB) ?_ (by simp only [List.length_reverse]; omega)
  funext k
  simp only [List.reverse_reverse, Function.update_apply]
  split_ifs <;> simp_all

theorem safe_passC {g : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst) (h3 : src ≠ dst)
    (xs ts tt : List Sym) (hg : g ∉ xs) (S : K → List Sym) (hS : S src = xs ++ g :: ts)
    (hT : S tmp = g :: tt) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passC g src tmp dst) S (Function.update S dst (xs ++ S dst))
      (fun r => r = some g) (9 * xs.length + 4) := by
  have hA := safe_passM h1 xs ts hg S hS ρ
  have hT1 : (Function.update (Function.update S src (g :: ts)) tmp (xs.reverse ++ S tmp)) tmp =
      xs.reverse ++ g :: tt := by
    rw [Function.update_self, hT]
  have hg' : g ∉ xs.reverse := by rwa [List.mem_reverse]
  have hB := safe_passF (Ne.symm h1) h2 h3 xs.reverse tt hg' _ hT1 ρ
  refine SafeRunsIn.congr (SafeRunsIn.seq hA hB) ?_ (by simp only [List.length_reverse]; omega)
  funext k
  simp only [List.reverse_reverse, Function.update_apply]
  split_ifs <;> simp_all

/-! ## Pass R -/

/-- Peek with a known head, safe. -/
theorem safe_peekR_head (k : K) (S : K → List Sym) (hne : S k ≠ []) (x : Option Sym)
    (hx : (S k).head? = x) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (peekR k) S S (fun r => r = x) 1 :=
  fun v => ⟨(S k).head?, 1, SafeEval.peek ρ k (fun _ o => o) v S (fun _ => hne), hx, le_rfl⟩

/-- **One record of Pass R**, safe and exact (as `runs_passRBody`; the rest of `src` must be
non-empty, e.g. it contains the guard). -/
theorem safe_passRBody {gt : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (hgt : gt.isBit = false) (p : List Bool) (rest tt : List Sym)
    (S : K → List Sym) (hS : S src = SubNLogN.Machine.recSyms p ++ rest)
    (hT : S tmp = gt :: tt) (hrest : rest ≠ []) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passRBody gt src tmp dst) S
      (Function.update (Function.update S src rest) dst (SubNLogN.Machine.recSyms p ++ S dst))
      (fun r => r = rest.head?) (8 * p.length + 7) := by
  have hA := safe_passM h1 (p.map Sym.bit) rest (FramePassRAux.sep_not_mem_bits p) S
    (by rw [hS]; simp [SubNLogN.Machine.recSyms]) ρ
  refine SafeRunsIn.congr (SafeRunsIn.seq hA
    (SafeRunsIn.seq (SafeRunsIn.mono (safe_popR src Sym.sep rest _ ?_ ρ) (fun _ _ => trivial) le_rfl)
    (SafeRunsIn.seq (safe_pushC dst Sym.sep _ ρ)
    (SafeRunsIn.seq (SafeRunsIn.mono (safe_passM h2 (p.map Sym.bit).reverse tt ?_ _ ?_ ρ)
        (fun _ _ => trivial) le_rfl)
      (safe_peekR_head src _ ?_ rest.head? ?_ ρ))))) ?_ ?_
  · rw [Function.update_of_ne h1, Function.update_self]
  · rw [List.mem_reverse]
    exact FramePassRAux.not_mem_bits_of_isBit hgt p
  · rw [Function.update_of_ne h2, Function.update_of_ne (Ne.symm h1), Function.update_self, hT]
  · rw [Function.update_of_ne h3, Function.update_of_ne h1, Function.update_of_ne h3,
      Function.update_self]
    exact hrest
  · rw [Function.update_of_ne h3, Function.update_of_ne h1, Function.update_of_ne h3,
      Function.update_self]
  · funext k
    simp only [SubNLogN.Machine.recSyms, List.reverse_reverse, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [List.length_reverse, List.length_map]
    omega

/-- The loop of Pass R, safe (exact stacks, cost bound). -/
theorem safe_passR_loop {g gt : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (hg : g.isBit = false) (hgs : g ≠ Sym.sep) (hgt : gt.isBit = false)
    (tt : List Sym) (ρ : List (SProg K)) :
    ∀ (v : List (List Bool)) (ts : List Sym) (S : K → List Sym),
      S src = SubNLogN.Machine.arrSyms v ++ g :: ts → S tmp = gt :: tt →
      ∃ t, t ≤ 8 * (SubNLogN.Machine.arrSyms v).length + 1 ∧
        SafeEval (fun _ => True) ρ (.loop (notG g) (passRBody gt src tmp dst))
          ⟨(SubNLogN.Machine.arrSyms v ++ g :: ts).head?, S⟩
          ⟨some g, Function.update (Function.update S src (g :: ts)) dst
            (SubNLogN.Machine.arrSyms v.reverse ++ S dst)⟩ t
  | [], ts, S, hS, _ => by
    have hS' : S src = g :: ts := by simpa [FramePassRAux.arrSyms_nil] using hS
    refine ⟨1, by simp [FramePassRAux.arrSyms_nil], ?_⟩
    refine (SafeEval.loop_false (framed := fun _ => True) (ρ := ρ) (p := passRBody gt src tmp dst)
      (s := ⟨(SubNLogN.Machine.arrSyms [] ++ g :: ts).head?, S⟩)
      (by simp [FramePassRAux.arrSyms_nil, notG])).of_eq_cost ?_ rfl
    simp only [FramePassRAux.arrSyms_nil, List.nil_append, List.reverse_nil, List.head?_cons]
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | p :: v, ts, S, hS, hT => by
    have hS1 : S src = SubNLogN.Machine.recSyms p ++ (SubNLogN.Machine.arrSyms v ++ g :: ts) := by
      rw [hS, FramePassRAux.arrSyms_cons, List.append_assoc]
    obtain ⟨v1, t1, e1, hq1, ht1⟩ := safe_passRBody h1 h2 h3 hgt p
      (SubNLogN.Machine.arrSyms v ++ g :: ts) tt S hS1 hT (by simp) ρ
      (SubNLogN.Machine.arrSyms (p :: v) ++ g :: ts).head?
    obtain ⟨t2, ht2, e2⟩ := safe_passR_loop h1 h2 h3 hg hgs hgt tt ρ v ts
      (Function.update (Function.update S src (SubNLogN.Machine.arrSyms v ++ g :: ts)) dst
        (SubNLogN.Machine.recSyms p ++ S dst))
      (by rw [Function.update_of_ne h3, Function.update_self])
      (by rw [Function.update_of_ne h2, Function.update_of_ne (Ne.symm h1), hT])
    have hc : notG g (SubNLogN.Machine.arrSyms (p :: v) ++ g :: ts).head? = true := by
      rw [FramePassRAux.arrSyms_cons]
      cases p with
      | nil => simp [SubNLogN.Machine.recSyms, notG, Ne.symm hgs]
      | cons b p =>
        simp only [SubNLogN.Machine.recSyms, List.map_cons, List.cons_append, List.head?_cons,
          notG, ne_eq, Option.some.injEq, decide_eq_true_eq]
        intro h
        rw [← h] at hg
        simp [Sym.isBit] at hg
    subst hq1
    refine ⟨t1 + t2 + 1, ?_, (SafeEval.loop_true hc e1 e2).of_eq_cost ?_ rfl⟩
    · rw [FramePassRAux.arrSyms_cons, List.length_append, FramePassRAux.length_recSyms]
      omega
    · congr 1
      funext k
      simp only [List.reverse_cons, FramePassRAux.arrSyms_append, FramePassRAux.arrSyms_cons,
        FramePassRAux.arrSyms_nil, List.append_nil, List.append_assoc, Function.update_apply]
      split_ifs <;> simp_all

/-- **Pass R**, safe and exact (as `runs_passR`): boundary-safe for every framed set. -/
theorem safe_passR {g gt : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (hg : g.isBit = false) (hgs : g ≠ Sym.sep) (hgt : gt.isBit = false)
    (v : List (List Bool)) (ts tt : List Sym) (S : K → List Sym)
    (hS : S src = SubNLogN.Machine.arrSyms v ++ g :: ts) (hT : S tmp = gt :: tt)
    (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (passR g gt src tmp dst) S
      (Function.update (Function.update S src (g :: ts)) dst
        (SubNLogN.Machine.arrSyms v.reverse ++ S dst))
      (fun r => r = some g) (8 * (SubNLogN.Machine.arrSyms v).length + 2) := by
  intro r
  obtain ⟨t, ht, e⟩ := safe_passR_loop h1 h2 h3 hg hgs hgt tt ρ v ts S hS hT
  have e0 : SafeEval (fun _ => True) ρ (peekR src) ⟨r, S⟩
      ⟨(SubNLogN.Machine.arrSyms v ++ g :: ts).head?, S⟩ 1 := by
    refine (SafeEval.peek ρ src (fun _ o => o) r S (fun _ => by rw [hS]; simp)).of_eq_cost ?_ rfl
    simp only [hS]
  exact ⟨some g, 1 + t, SafeEval.seq e0 e, rfl, by omega⟩

end SafePasses

#assert_std_axioms safe_pushC safe_popR safe_peekR safe_passM_loop_eval safe_passM_eval safe_passM
  safe_passF_loop_eval safe_passF_eval safe_passF safe_passE_loop_eval safe_passE_eval safe_passE
  safe_passS safe_passC safe_peekR_head safe_passRBody safe_passR_loop safe_passR

/-! ## The binary countdown counter, safe -/

section SafeCounter

variable {K : Type} [DecidableEq K]

open Computability

/-- The loop of `moveBits`, safe when the terminator is visible (`rest ≠ []`). -/
theorem safe_moveBits_loop_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) :
    ∀ (es : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest → rest ≠ [] →
      S src = (es.map Sym.bit ++ rest).tail →
      SafeEval (fun _ => True) ρ (.loop optIsBit (moveBitsBody src dst))
        ⟨(es.map Sym.bit ++ rest).head?, S⟩
        ⟨rest.head?, Function.update (Function.update S src rest.tail) dst
          (es.reverse.map Sym.bit ++ S dst)⟩ (3 * es.length + 1)
  | [], rest, S, hrest, _, hS => by
    refine (SafeEval.loop_false (framed := fun _ => True) (ρ := ρ) (p := moveBitsBody src dst)
      (s := ⟨rest.head?, S⟩) (optIsBit_head?_of_termOK hrest)).of_eq_cost ?_ rfl
    have hS' : S src = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update (Function.update S src rest.tail)
      dst ([] ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.nil_append, Function.update_eq_self]
  | e :: es, rest, S, hrest, hrne, hS => by
    have hS' : S src = es.map Sym.bit ++ rest := hS
    have hpush : SafeEval (fun _ => True) ρ (pushR dst) ⟨some (.bit e), S⟩
        ⟨some (.bit e), Function.update S dst (.bit e :: S dst)⟩ 1 :=
      (SafeEval.push ρ dst (fun r => r.getD .sep) (some (.bit e)) S).of_eq_cost rfl rfl
    have hsrc : Function.update S dst (.bit e :: S dst) src = es.map Sym.bit ++ rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : SafeEval (fun _ => True) ρ (popR src)
        ⟨some (.bit e), Function.update S dst (.bit e :: S dst)⟩
        ⟨(es.map Sym.bit ++ rest).head?, Function.update (Function.update S dst (.bit e :: S dst))
          src (es.map Sym.bit ++ rest).tail⟩ 1 := by
      refine (SafeEval.pop ρ src (fun _ o => o) _ _ (fun _ => by rw [hsrc]; simp [hrne])).of_eq_cost
        ?_ rfl
      rw [hsrc]
    have ih := safe_moveBits_loop_eval hne ρ es rest
      (Function.update (Function.update S dst (.bit e :: S dst)) src (es.map Sym.bit ++ rest).tail)
      hrest hrne (Function.update_self _ _ _)
    refine (SafeEval.loop_true (by rfl) (SafeEval.seq hpush hpop) ih).of_eq_cost ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **moveBits**, safe when the terminator is visible. -/
theorem safe_moveBits_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (es : List Bool) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest) (hrne : rest ≠ [])
    (hS : S src = es.map Sym.bit ++ rest) :
    SafeEval (fun _ => True) ρ (moveBits src dst) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S src rest.tail) dst
        (es.reverse.map Sym.bit ++ S dst)⟩ (3 * es.length + 2) := by
  have h1 : SafeEval (fun _ => True) ρ (popR src) ⟨v, S⟩
      ⟨(es.map Sym.bit ++ rest).head?, Function.update S src (es.map Sym.bit ++ rest).tail⟩ 1 := by
    refine (SafeEval.pop ρ src (fun _ o => o) v S (fun _ => by rw [hS]; simp [hrne])).of_eq_cost
      ?_ rfl
    rw [hS]
  have h2 := safe_moveBits_loop_eval hne ρ es rest
    (Function.update S src (es.map Sym.bit ++ rest).tail) hrest hrne (Function.update_self _ _ _)
  refine (SafeEval.seq h1 h2).of_eq_cost ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- The carry/borrow scan of `Lib.inc`/`Lib.dec`, safe when the terminator is visible. -/
theorem safe_scan_eval {k t : K} (hkt : k ≠ t) (b c : Bool) (ρ : List (SProg K)) :
    ∀ (L : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest → rest ≠ [] →
      S k = (L.map Sym.bit ++ rest).tail →
      SafeEval (fun _ => True) ρ (scanLoop b c k t) ⟨(L.map Sym.bit ++ rest).head?, S⟩
        ⟨((dropRun b L).map Sym.bit ++ rest).head?,
          Function.update (Function.update S k ((dropRun b L).map Sym.bit ++ rest).tail) t
            (List.replicate (runLen b L) (Sym.bit c) ++ S t)⟩ (3 * runLen b L + 1)
  | [], rest, S, hrest, _, hS => by
    refine (SafeEval.loop_false (framed := fun _ => True) (ρ := ρ) (p := scanBody k t c)
      (s := ⟨rest.head?, S⟩) (isBitR_head?_of_termOK b hrest)).of_eq_cost ?_ rfl
    have hS' : S k = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) =
      ⟨rest.head?, Function.update (Function.update S k rest.tail) t ([] ++ S t)⟩
    rw [← hS', Function.update_eq_self, List.nil_append, Function.update_eq_self]
  | x :: L, rest, S, hrest, hrne, hS => by
    have hS' : S k = L.map Sym.bit ++ rest := hS
    by_cases hx : x = b
    · subst hx
      have hpush : SafeEval (fun _ => True) ρ (pushC t (.bit c)) ⟨some (.bit x), S⟩
          ⟨some (.bit x), Function.update S t (.bit c :: S t)⟩ 1 :=
        SafeEval.push ρ t (fun _ => .bit c) (some (.bit x)) S
      have hk : Function.update S t (.bit c :: S t) k = L.map Sym.bit ++ rest := by
        rw [Function.update_of_ne hkt]
        exact hS'
      have hpop : SafeEval (fun _ => True) ρ (popR k)
          ⟨some (.bit x), Function.update S t (.bit c :: S t)⟩
          ⟨(L.map Sym.bit ++ rest).head?, Function.update (Function.update S t (.bit c :: S t)) k
            (L.map Sym.bit ++ rest).tail⟩ 1 := by
        refine (SafeEval.pop ρ k (fun _ o => o) _ _ (fun _ => by rw [hk]; simp [hrne])).of_eq_cost
          ?_ rfl
        rw [hk]
      have ih := safe_scan_eval hkt x c ρ L rest
        (Function.update (Function.update S t (.bit c :: S t)) k (L.map Sym.bit ++ rest).tail)
        hrest hrne (Function.update_self _ _ _)
      have hd : dropRun x (x :: L) = dropRun x L := by simp [dropRun]
      have hr : runLen x (x :: L) = runLen x L + 1 := by simp [runLen]
      rw [hd, hr]
      refine (SafeEval.loop_true (by simp [isBitR]) (SafeEval.seq hpush hpop) ih).of_eq_cost ?_
        (by omega)
      congr 1
      funext j
      simp only [Function.update_apply]
      split_ifs <;> simp_all [List.replicate_succ']
    · have hd : dropRun b (x :: L) = x :: L := by simp [dropRun, hx]
      have hr : runLen b (x :: L) = 0 := by simp [runLen, hx]
      rw [hd, hr]
      refine (SafeEval.loop_false (framed := fun _ => True) (ρ := ρ) (p := scanBody k t c)
        (s := ⟨((x :: L).map Sym.bit ++ rest).head?, S⟩) (by simp [isBitR, hx])).of_eq_cost ?_ rfl
      show (⟨((x :: L).map Sym.bit ++ rest).head?, S⟩ : SSt K) =
        ⟨((x :: L).map Sym.bit ++ rest).head?, Function.update (Function.update S k
          ((x :: L).map Sym.bit ++ rest).tail) t ([] ++ S t)⟩
      rw [← hS, Function.update_eq_self, List.nil_append, Function.update_eq_self]

/-- The fix-up step of `Lib.dec`, safe when the terminator is visible. -/
theorem safe_decFix_eval {k : K} (ρ : List (SProg K)) (r₀ : Option Sym) (M : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest) (hrne : rest ≠ [])
    (hS : S k = M.map Sym.bit ++ rest) :
    SafeEval (fun _ => True) ρ (decFix k) ⟨r₀, S⟩
      ⟨(M.map Sym.bit ++ rest).head?,
        Function.update S k ((if M = [] then [] else false :: M).map Sym.bit ++ rest)⟩ 3 := by
  have e1 : SafeEval (fun _ => True) ρ (peekR k) ⟨r₀, S⟩ ⟨(M.map Sym.bit ++ rest).head?, S⟩ 1 := by
    refine (SafeEval.peek ρ k (fun _ o => o) r₀ S (fun _ => by rw [hS]; simp [hrne])).of_eq_cost
      ?_ rfl
    rw [hS]
  cases M with
  | nil =>
    have e2 : SafeEval (fun _ => True) ρ (.ite optIsBit (pushC k (.bit false)) skip)
        ⟨([].map Sym.bit ++ rest).head?, S⟩ ⟨([].map Sym.bit ++ rest).head?, S⟩ 2 :=
      SafeEval.ite_false (optIsBit_head?_of_termOK hrest)
        (SafeEval.load ρ id ([].map Sym.bit ++ rest).head? S)
    refine (SafeEval.seq e1 e2).of_eq_cost ?_ rfl
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update S k ([] ++ rest)⟩
    rw [List.nil_append, ← (show S k = rest from hS), Function.update_eq_self]
  | cons m M' =>
    have e2 : SafeEval (fun _ => True) ρ (.ite optIsBit (pushC k (.bit false)) skip)
        ⟨((m :: M').map Sym.bit ++ rest).head?, S⟩
        ⟨((m :: M').map Sym.bit ++ rest).head?, Function.update S k (.bit false :: S k)⟩ 2 :=
      SafeEval.ite_true (by rfl) (SafeEval.push ρ k (fun _ => .bit false) _ S)
    refine (SafeEval.seq e1 e2).of_eq_cost ?_ rfl
    simp only [List.cons_ne_nil, if_false, hS]
    rfl

/-- **`Lib.dec`**, safe and exact when the terminator is visible (`rest ≠ []`):
`encodeNat (n+1) ↦ encodeNat n`, cost `6·zerosLead + 8`. -/
theorem safe_dec_eval {k t : K} (hkt : k ≠ t) (ρ : List (SProg K)) (v : Option Sym) (n : ℕ)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest) (hrne : rest ≠ [])
    (hS : S k = (encodeNat (n + 1)).map Sym.bit ++ rest) :
    SafeEval (fun _ => True) ρ (dec k t) ⟨v, S⟩
      ⟨some .mark, Function.update S k ((encodeNat n).map Sym.bit ++ rest)⟩
      (6 * zerosLead (encodeNat (n + 1)) + 8) := by
  set L := encodeNat (n + 1) with hL
  obtain ⟨M, hM⟩ := dropRun_false_encodeNat_succ n
  rw [← hL] at hM
  have e0 : SafeEval (fun _ => True) ρ (pushC t .mark) ⟨v, S⟩
      ⟨v, Function.update S t (.mark :: S t)⟩ 1 :=
    SafeEval.push ρ t (fun _ => .mark) v S
  set S1 := Function.update S t (.mark :: S t) with hS1
  have hS1k : S1 k = L.map Sym.bit ++ rest := by rw [hS1, Function.update_of_ne hkt]; exact hS
  have e1 : SafeEval (fun _ => True) ρ (popR k) ⟨v, S1⟩
      ⟨(L.map Sym.bit ++ rest).head?, Function.update S1 k (L.map Sym.bit ++ rest).tail⟩ 1 := by
    refine (SafeEval.pop ρ k (fun _ o => o) v S1 (fun _ => by rw [hS1k]; simp [hrne])).of_eq_cost
      ?_ rfl
    rw [hS1k]
  have e2 := safe_scan_eval hkt false true ρ L rest
    (Function.update S1 k (L.map Sym.bit ++ rest).tail) hrest hrne (Function.update_self _ _ _)
  rw [hM] at e2
  set S3 := Function.update (Function.update (Function.update S1 k (L.map Sym.bit ++ rest).tail) k
    ((true :: M).map Sym.bit ++ rest).tail) t (List.replicate (runLen false L) (Sym.bit true) ++
      Function.update S1 k (L.map Sym.bit ++ rest).tail t) with hS3
  have e3 := safe_decFix_eval (k := k) ρ ((true :: M).map Sym.bit ++ rest).head? M rest S3 hrest
    hrne (by rw [hS3, Function.update_of_ne hkt, Function.update_self]; rfl)
  set S4 := Function.update S3 k ((if M = [] then [] else false :: M).map Sym.bit ++ rest)
    with hS4
  have hS4t : S4 t = (List.replicate (runLen false L) true).map Sym.bit ++ (.mark :: S t) := by
    rw [hS4, Function.update_of_ne (Ne.symm hkt), hS3, Function.update_self,
      Function.update_of_ne (Ne.symm hkt), hS1, Function.update_self, List.map_replicate]
  have e4 := safe_moveBits_eval (Ne.symm hkt) ρ (M.map Sym.bit ++ rest).head?
    (List.replicate (runLen false L) true)
    (.mark :: S t) S4 (TermOK.cons (by rfl) _) (by simp) hS4t
  refine (SafeEval.seq e0 (SafeEval.seq e1 (SafeEval.seq e2 (SafeEval.seq e3 e4)))).of_eq_cost ?_ ?_
  · congr 1
    have hdec : encodeNat n = List.replicate (runLen false L) true ++
        (if M = [] then [] else false :: M) := by
      rw [← decBits_encodeNat_succ, ← hL, decBits_eq_run L M hM]
    funext j
    simp only [hS4, hS3, hS1, Function.update_apply, List.tail_cons,
      List.reverse_replicate, hdec]
    split_ifs <;> simp_all [List.map_replicate]
  · rw [List.length_replicate, ← runLen_false_eq_zerosLead]
    omega

theorem safe_dec {c t : K} (hct : c ≠ t) (n : ℕ) (ct : List Sym) (S : K → List Sym)
    (hct' : TermOK ct) (hctne : ct ≠ []) (hS : S c = natSyms (n + 1) ++ ct) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (dec c t) S (Function.update S c (natSyms n ++ ct))
      (fun _ => True) (6 * zerosLead (encodeNat (n + 1)) + 8) :=
  fun v => ⟨_, _, safe_dec_eval hct ρ v n ct S hct' hctne hS, trivial, le_rfl⟩

theorem safe_zeroTest (c : K) (n : ℕ) (ct : List Sym) (S : K → List Sym) (hct : TermOK ct)
    (hctne : ct ≠ []) (hS : S c = natSyms n ++ ct) (ρ : List (SProg K)) :
    SafeRunsIn (fun _ => True) ρ (zeroTest c) S S (fun r => optIsBit r = decide (0 < n)) 1 := by
  intro v
  obtain ⟨r, hr, e⟩ := zeroTest_eval ρ v n ct S hct hS
  refine ⟨r, 1, ?_, ?_, le_rfl⟩
  · have e' := SafeEval.peek (framed := fun _ => True) ρ c (fun _ o => o) v S
      (fun _ => by rw [hS]; simp [hctne])
    have hr' : r = (S c).head? := by
      cases e
      rfl
    rw [hr']
    exact e'
  · show optIsBit r = decide (0 < n)
    rw [hr]
    cases n <;> simp

end SafeCounter

/-- **Countdown**, boundary-safe for every framed set (`SafeRunsIn (fun _ => True)`, any
environment), when the counter terminator is visible (`ct ≠ []`) and the body is safe; as
`runsIn_countdown`. -/
theorem safe_countdown {K σ : Type} [DecidableEq K] {ρ : List (Prog K (fun _ => Sym) σ)}
    (l : Lens σ (Option Sym)) {c t : K} (hct : c ≠ t) {body : Prog K (fun _ => Sym) σ} (N : ℕ)
    (ct : List Sym) (hctm : TermOK ct) (hctne : ct ≠ []) (st : ℕ → K → List Sym) (B : ℕ → ℕ)
    (hbody : ∀ n, n < N →
      SafeRunsIn (fun _ => True) ρ body (Function.update (st (n + 1)) c (natSyms (n + 1) ++ ct))
        (Function.update (st n) c (natSyms (n + 1) ++ ct)) (fun _ => True) (B n)) :
    SafeRunsIn (fun _ => True) ρ (countdown l c t body)
      (Function.update (st N) c (natSyms N ++ ct)) (Function.update (st 0) c ct)
      (fun v => optIsBit (l.get v) = false) (countdownCost B N) := by
  have h0 : SafeRunsIn (fun _ => True) ρ ((zeroTest c).liftRegs l)
      (Function.update (st N) c (natSyms N ++ ct)) (Function.update (st N) c (natSyms N ++ ct))
      (fun v => optIsBit (l.get v) = decide (0 < N)) 1 :=
    SafeRunsIn.liftRegs l (FramePassRAux.closed_zeroTest c)
      (safe_zeroTest c N ct _ hctm hctne (Function.update_self _ _ _) []) ρ
  have hstep : ∀ n, n < N →
      SafeRunsIn (fun _ => True) ρ (.seq body (.seq ((dec c t).liftRegs l) ((zeroTest c).liftRegs l)))
        (Function.update (st (n + 1)) c (natSyms (n + 1) ++ ct))
        (Function.update (st n) c (natSyms n ++ ct))
        (fun v => optIsBit (l.get v) = decide (0 < n))
        (B n + 6 * zerosLead (Computability.encodeNat (n + 1)) + 9) := by
    intro n hn
    have hd := SafeRunsIn.liftRegs l (FramePassRAux.closed_dec c t)
      (safe_dec hct n ct (Function.update (st n) c (natSyms (n + 1) ++ ct)) hctm hctne
        (Function.update_self _ _ _) []) ρ
    rw [Function.update_idem] at hd
    have hz := SafeRunsIn.liftRegs l (FramePassRAux.closed_zeroTest c)
      (safe_zeroTest c n ct (Function.update (st n) c (natSyms n ++ ct)) hctm hctne
        (Function.update_self _ _ _) []) ρ
    exact SafeRunsIn.mono (SafeRunsIn.seq (hbody n hn) (SafeRunsIn.seq hd hz)) (fun _ h => h)
      (by omega)
  have key := SafeRunsIn.seq_loop (st := fun n => Function.update (st n) c (natSyms n ++ ct))
    h0 hstep
  refine SafeRunsIn.congr key ?_ (by simp [countdownCost])
  simp [natSyms, encodeNat_zero]

#assert_std_axioms safe_moveBits_loop_eval safe_moveBits_eval safe_scan_eval safe_decFix_eval
  safe_dec_eval safe_dec safe_zeroTest safe_countdown

end SubNLogN.Machine.Calculus
