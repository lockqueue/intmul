/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.FramePass
import SubNLogN.Machine.Calculus.Guard
import SubNLogN.Machine.Contracts.Streams
import WP.W9b.Macros

/-!
# Framed procedure calculus: Pass R and the binary countdown counter (`Calculus/FramePassR.lean`)

Record-order reversal and binary countdown passes, in the conventions of
`Calculus/FramePass.lean` (one `Option Sym` register; exact `Runs` facts for arbitrary stacks, and
protected-tail `FramedRunsIn` forms for all tails on all stacks, class `fun _ _ => True`).

* **Pass R** `passR g gt src tmp dst`: reverse the record order of the block `arrSyms v` of raw bit
  records on `src` (above the guard `g`, which is neither a bit nor `sep`) onto `dst`, preserving
  each record's symbol order, through `tmp` (whose top is a non-bit guard `gt`). Per record: Pass M
  of the payload to `tmp` stopping at `sep`, pop the `sep`, push `sep` on `dst`, Pass M of the
  payload from `tmp` to `dst` stopping at `gt`, peek. Result `arrSyms v.reverse ++ (old dst)`;
  cost exactly `8·|arrSyms v| + 2` (`8ℓ + 8` per record of `ℓ` payload bits, plus
  the initial peek and the final test): `runs_passR`, `framed_passR`.
* **Countdown** `countdown l c t body`: with the canonical LSB-first counter `natSyms N` on `c`
  (above a number terminator), run `body` for the counter values `N, N-1, …, 1`, decrementing with
  `Lib.dec` (temporary `t`) and testing with `Lib.zeroTest` (the finite `isZero` flag is the
  register's `optIsBit`). It leaves its counter segment empty (`natSyms 0 = []`, local reset).
  Exact cost `Σ_{n=1}^{N} B n + decSum N + 2N + 2`, and `decSum N ≤ 14N`, so the cost is at most
  `Σ B n + 16N + 2` (`runsIn_countdown`, `countdownCost_le`), using the exact `Lib.dec` cost
  `6t + 8` (`t` = trailing zeros) amortized over the `N`
  decrements. `framed_countdown` is the protected-tail form.
-/

namespace SubNLogN.Machine.Calculus

open Computability TMFw TMFw.Contracts TMFw.Lib

/-! ## Pass R -/

section PassRPrograms

variable {K : Type}

/-- Body of Pass R: move one record from `src` to `dst` (symbol order preserved) through `tmp`,
then peek the next symbol of `src`. -/
def passRBody (gt : Sym) (src tmp dst : K) : SProg K :=
  .seq (passM Sym.sep src tmp) (.seq (popR src) (.seq (pushC dst Sym.sep)
    (.seq (passM gt tmp dst) (peekR src))))

/-- **Pass R**: reverse the record order of the block of records on `src` above the guard `g`, onto
`dst`, each record's symbol order preserved, through `tmp` (top guard `gt`). -/
def passR (g gt : Sym) (src tmp dst : K) : SProg K :=
  .seq (peekR src) (.loop (notG g) (passRBody gt src tmp dst))

theorem closed_passRBody (gt : Sym) (src tmp dst : K) : (passRBody gt src tmp dst).Closed := by
  simp [passRBody, passM, passMBody, popR, pushR, pushC, peekR, Prog.Closed, Prog.FreeBelow]

theorem closed_passR (g gt : Sym) (src tmp dst : K) : (passR g gt src tmp dst).Closed := by
  simp [passR, passRBody, passM, passMBody, popR, pushR, pushC, peekR, Prog.Closed,
    Prog.FreeBelow]

end PassRPrograms

section PassREval

variable {K : Type} [DecidableEq K]

namespace FramePassRAux

theorem sep_not_mem_bits (p : List Bool) : Sym.sep ∉ p.map Sym.bit := by
  intro h
  obtain ⟨b, -, hb⟩ := List.mem_map.1 h
  exact Sym.noConfusion hb

theorem not_mem_bits_of_isBit {g : Sym} (hg : g.isBit = false) (xs : List Bool) :
    g ∉ xs.map Sym.bit := by
  intro h
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 h
  simp [Sym.isBit] at hg

theorem runs_peekR_eq (k : K) (S : K → List Sym) (x : Option Sym) (hx : (S k).head? = x) :
    Runs (peekR k) S S (fun r => r = x) 1 :=
  Runs.of_eval fun v => ⟨(S k).head?, 1, by
    have h := Eval.peek ([] : List (SProg K)) k (fun _ o => o) v S
    exact h, hx, le_rfl⟩

theorem arrSyms_cons (p : List Bool) (v : List (List Bool)) :
    SubNLogN.Machine.arrSyms (p :: v) = SubNLogN.Machine.recSyms p ++ SubNLogN.Machine.arrSyms v := by
  simp [SubNLogN.Machine.arrSyms, blk]

theorem arrSyms_nil : SubNLogN.Machine.arrSyms [] = [] := by
  simp [SubNLogN.Machine.arrSyms, blk]

theorem arrSyms_append (v w : List (List Bool)) :
    SubNLogN.Machine.arrSyms (v ++ w) = SubNLogN.Machine.arrSyms v ++ SubNLogN.Machine.arrSyms w := by
  simp [SubNLogN.Machine.arrSyms, blk]

theorem length_recSyms (p : List Bool) : (SubNLogN.Machine.recSyms p).length = p.length + 1 := by
  simp [SubNLogN.Machine.recSyms]

end FramePassRAux

/-- **One record of Pass R**, exact stacks: the record `recSyms p` on top of `src` goes on top of
`dst` (same symbol order); `tmp` (top guard `gt`) is restored; the register holds the next symbol
of `src`. Cost `8·|p| + 7`. -/
theorem runs_passRBody {gt : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (hgt : gt.isBit = false) (p : List Bool) (rest tt : List Sym)
    (S : K → List Sym) (hS : S src = SubNLogN.Machine.recSyms p ++ rest)
    (hT : S tmp = gt :: tt) :
    Runs (passRBody gt src tmp dst) S
      (Function.update (Function.update S src rest) dst (SubNLogN.Machine.recSyms p ++ S dst))
      (fun r => r = rest.head?) (8 * p.length + 7) := by
  have hA := runs_passM h1 (p.map Sym.bit) rest (FramePassRAux.sep_not_mem_bits p) S
    (by rw [hS]; simp [SubNLogN.Machine.recSyms])
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.seq (RunsIn.iff_runs.mpr hA)
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_popR src _ Sym.sep rest ?_))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_pushC dst Sym.sep _))
    (RunsIn.seq (RunsIn.iff_runs.mpr (runs_passM h2 (p.map Sym.bit).reverse tt ?_ _ ?_))
      (RunsIn.iff_runs.mpr (FramePassRAux.runs_peekR_eq src _ rest.head? ?_)))))) ?_ ?_)
  · rw [Function.update_of_ne h1, Function.update_self]
  · rw [List.mem_reverse]
    exact FramePassRAux.not_mem_bits_of_isBit hgt p
  · rw [Function.update_of_ne h2, Function.update_of_ne (Ne.symm h1), Function.update_self, hT]
  · rw [Function.update_of_ne h3, Function.update_of_ne h1, Function.update_of_ne h3,
      Function.update_self]
  · funext k
    simp only [SubNLogN.Machine.recSyms, List.reverse_reverse, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [List.length_reverse, List.length_map]
    omega

/-- The loop of Pass R (exact stacks, cost bound). -/
theorem passR_loop {g gt : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (hg : g.isBit = false) (hgs : g ≠ Sym.sep) (hgt : gt.isBit = false)
    (tt : List Sym) :
    ∀ (v : List (List Bool)) (ts : List Sym) (S : K → List Sym),
      S src = SubNLogN.Machine.arrSyms v ++ g :: ts → S tmp = gt :: tt →
      ∃ t, t ≤ 8 * (SubNLogN.Machine.arrSyms v).length + 1 ∧
        Eval [] (.loop (notG g) (passRBody gt src tmp dst))
          ⟨(SubNLogN.Machine.arrSyms v ++ g :: ts).head?, S⟩
          ⟨some g, Function.update (Function.update S src (g :: ts)) dst
            (SubNLogN.Machine.arrSyms v.reverse ++ S dst)⟩ t
  | [], ts, S, hS, _ => by
    have hS' : S src = g :: ts := by simpa [FramePassRAux.arrSyms_nil] using hS
    refine ⟨1, by simp [FramePassRAux.arrSyms_nil], ?_⟩
    refine (Eval.loop_false (by simp [FramePassRAux.arrSyms_nil, notG])).of_eq ?_ rfl
    simp only [FramePassRAux.arrSyms_nil, List.nil_append, List.reverse_nil]
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | p :: v, ts, S, hS, hT => by
    have hS1 : S src = SubNLogN.Machine.recSyms p ++ (SubNLogN.Machine.arrSyms v ++ g :: ts) := by
      rw [hS, FramePassRAux.arrSyms_cons, List.append_assoc]
    obtain ⟨s1, t1, e1, ⟨hs1, hq1⟩, ht1⟩ := runs_passRBody h1 h2 h3 hgt p
      (SubNLogN.Machine.arrSyms v ++ g :: ts) tt S hS1 hT
      ⟨(SubNLogN.Machine.arrSyms (p :: v) ++ g :: ts).head?, S⟩ rfl
    obtain ⟨t2, ht2, e2⟩ := passR_loop h1 h2 h3 hg hgs hgt tt v ts
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
    obtain ⟨var1, stk1⟩ := s1
    simp only at hs1 hq1
    subst hs1 hq1
    refine ⟨t1 + t2 + 1, ?_, (Eval.loop_true hc e1 e2).of_eq ?_ rfl⟩
    · rw [FramePassRAux.arrSyms_cons, List.length_append, FramePassRAux.length_recSyms]
      omega
    · congr 1
      funext k
      simp only [List.reverse_cons, FramePassRAux.arrSyms_append, FramePassRAux.arrSyms_cons, FramePassRAux.arrSyms_nil, List.append_nil,
        List.append_assoc, Function.update_apply]
      split_ifs <;> simp_all

/-- **Pass R**, exact: the block `arrSyms v` of raw bit records on `src` (above the guard `g`,
neither a bit nor `sep`; arbitrary content `ts` below) lands on `dst` as
`arrSyms v.reverse` (record order reversed, every record's symbol order preserved); `src` keeps
`g :: ts`; `tmp` (top guard `gt`, not a bit) is restored; the register holds `g`. Cost
`8·|arrSyms v| + 2`. -/
theorem runs_passR {g gt : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (hg : g.isBit = false) (hgs : g ≠ Sym.sep) (hgt : gt.isBit = false)
    (v : List (List Bool)) (ts tt : List Sym) (S : K → List Sym)
    (hS : S src = SubNLogN.Machine.arrSyms v ++ g :: ts) (hT : S tmp = gt :: tt) :
    Runs (passR g gt src tmp dst) S
      (Function.update (Function.update S src (g :: ts)) dst
        (SubNLogN.Machine.arrSyms v.reverse ++ S dst))
      (fun r => r = some g) (8 * (SubNLogN.Machine.arrSyms v).length + 2) :=
  Runs.of_eval fun r => by
    obtain ⟨t, ht, e⟩ := passR_loop h1 h2 h3 hg hgs hgt tt v ts S hS hT
    have e0 : Eval [] (peekR src) ⟨r, S⟩ ⟨(SubNLogN.Machine.arrSyms v ++ g :: ts).head?, S⟩ 1 := by
      refine (Eval.peek [] src (fun _ o => o) r S).of_eq ?_ rfl
      simp only [hS]
    exact ⟨some g, 1 + t, Eval.seq e0 e, rfl, by omega⟩

/-- **Pass R with protected tails**: guard local (`src = arrSyms v ++ [g]`, `tmp = [gt]`), every
tail on every stack, any environment. -/
theorem framed_passR {g gt : Sym} {src tmp dst : K} (h1 : src ≠ tmp) (h2 : tmp ≠ dst)
    (h3 : src ≠ dst) (hg : g.isBit = false) (hgs : g ≠ Sym.sep) (hgt : gt.isBit = false)
    (v : List (List Bool)) (S : K → List Sym) (hS : S src = SubNLogN.Machine.arrSyms v ++ [g])
    (hT : S tmp = [gt]) (ρ : List (SProg K)) :
    FramedRunsIn (fun _ _ => True) ρ (passR g gt src tmp dst) S
      (Function.update (Function.update S src [g]) dst
        (SubNLogN.Machine.arrSyms v.reverse ++ S dst))
      (fun r => r = some g) (8 * (SubNLogN.Machine.arrSyms v).length + 2) := by
  refine FramedRunsIn.of_runs (closed_passR g gt src tmp dst) (fun τ _ => ?_) ρ
  have h := runs_passR h1 h2 h3 hg hgs hgt v (τ src) (τ tmp) (appendTail S τ) (by simp [hS])
    (by simp [hT])
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.iff_runs.mpr h) ?_ le_rfl)
  funext k
  simp only [appendTail_apply, Function.update_apply]
  split_ifs <;> simp_all

end PassREval

/-! ## The binary countdown counter -/

section CountdownPrograms

variable {K σ : Type}

/-- **Countdown**: with the counter `natSyms N` on `c`, run `body` for the counter values
`N, N-1, …, 1`: zero test; while the counter is nonzero: `body ; dec c t ; zero test`. The counter
operations reach the symbol register through the lens `l`. -/
def countdown (l : Lens σ (Option Sym)) (c t : K) (body : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq ((zeroTest c).liftRegs l)
    (.loop (fun v => optIsBit (l.get v))
      (.seq body (.seq ((dec c t).liftRegs l) ((zeroTest c).liftRegs l))))

/-- The cost of `countdown` with body costs `B n` (counter value `n + 1`). -/
def countdownCost (B : ℕ → ℕ) (N : ℕ) : ℕ :=
  1 + loopCost (fun n => B n + 6 * zerosLead (encodeNat (n + 1)) + 9) N

namespace FramePassRAux

theorem closed_zeroTest (c : K) : (zeroTest c).Closed := by
  simp [Prog.Closed, zeroTest, peekR, Prog.FreeBelow]

theorem closed_dec (c t : K) : (dec c t).Closed := by
  simp [Prog.Closed, dec, decFix, scanLoop, scanBody, moveBits, moveBitsBody, pushC, popR,
    pushR, peekR, Prog.FreeBelow, Lib.skip]

end FramePassRAux

theorem closed_countdown (l : Lens σ (Option Sym)) (c t : K) {body : Prog K (fun _ => Sym) σ}
    (hb : body.Closed) : (countdown l c t body).Closed :=
  ⟨WP.W9comp.closed_liftRegs l (FramePassRAux.closed_zeroTest c), hb,
    WP.W9comp.closed_liftRegs l (FramePassRAux.closed_dec c t),
    WP.W9comp.closed_liftRegs l (FramePassRAux.closed_zeroTest c)⟩

/-- **Countdown cost**, exact form: `Σ_{n<N} B n + decSum N + 2N + 2` (`decSum N` is the total
cost of the decrements `N → … → 0`). -/
theorem countdownCost_eq (B : ℕ → ℕ) :
    ∀ N, countdownCost B N = ((List.range N).map B).sum + WP.W9b.decSum N + 2 * N + 2
  | 0 => by simp [countdownCost, loopCost, WP.W9b.decSum]
  | N + 1 => by
    have ih := countdownCost_eq B N
    simp only [countdownCost, loopCost] at ih ⊢
    rw [List.range_succ, List.map_append, List.sum_append, WP.W9b.decSum]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-- **Countdown cost**, bound: `Σ_{n<N} B n + 16N + 2` (amortized: `decSum N ≤ 14N`). -/
theorem countdownCost_le (B : ℕ → ℕ) (N : ℕ) :
    countdownCost B N ≤ ((List.range N).map B).sum + 16 * N + 2 := by
  rw [countdownCost_eq]
  have := WP.W9b.decSum_le N
  omega

end CountdownPrograms

section CountdownRules

variable {K σ : Type} [DecidableEq K]

namespace FramePassRAux

theorem runs_zeroTest (c : K) (n : ℕ) (ct : List Sym) (S : K → List Sym) (hct : TermOK ct)
    (hS : S c = natSyms n ++ ct) :
    Runs (zeroTest c) S S (fun r => optIsBit r = decide (0 < n)) 1 :=
  Runs.of_eval fun v => by
    obtain ⟨r, hr, e⟩ := zeroTest_eval [] v n ct S hct hS
    refine ⟨r, 1, e, ?_, le_rfl⟩
    rw [hr]
    cases n <;> simp

theorem runs_dec {c t : K} (hct : c ≠ t) (n : ℕ) (ct : List Sym) (S : K → List Sym)
    (hct' : TermOK ct) (hS : S c = natSyms (n + 1) ++ ct) :
    Runs (dec c t) S (Function.update S c (natSyms n ++ ct)) (fun _ => True)
      (6 * zerosLead (encodeNat (n + 1)) + 8) :=
  Runs.of_eval fun v => ⟨_, _, dec_eval hct [] v n ct S hct' hS, trivial, le_rfl⟩

end FramePassRAux

/-- **Countdown**, exact stacks, any environment. The counter `natSyms N` sits on `c` above a
number terminator `ct`; when the counter holds `n + 1` (`n < N`), the body takes the other stacks
from `st (n + 1)` to `st n` (leaving `c` alone) within `B n`. Then `countdown` ends with the other
stacks `st 0` and the counter segment empty (`c = ct`), the register's `optIsBit` false (the
`isZero` flag), within `countdownCost B N`. -/
theorem runsIn_countdown {ρ : List (Prog K (fun _ => Sym) σ)} (l : Lens σ (Option Sym)) {c t : K}
    (hct : c ≠ t) {body : Prog K (fun _ => Sym) σ} (N : ℕ) (ct : List Sym) (hctm : TermOK ct)
    (st : ℕ → K → List Sym) (B : ℕ → ℕ)
    (hbody : ∀ n, n < N →
      RunsIn ρ body (Function.update (st (n + 1)) c (natSyms (n + 1) ++ ct))
        (Function.update (st n) c (natSyms (n + 1) ++ ct)) (fun _ => True) (B n)) :
    RunsIn ρ (countdown l c t body) (Function.update (st N) c (natSyms N ++ ct))
      (Function.update (st 0) c ct) (fun v => optIsBit (l.get v) = false) (countdownCost B N) := by
  have h0 : RunsIn ρ ((zeroTest c).liftRegs l) (Function.update (st N) c (natSyms N ++ ct))
      (Function.update (st N) c (natSyms N ++ ct)) (fun v => optIsBit (l.get v) = decide (0 < N))
      1 :=
    RunsIn.of_runs_liftRegs l (FramePassRAux.runs_zeroTest c N ct _ hctm
      (Function.update_self _ _ _)) (FramePassRAux.closed_zeroTest c) ρ
  have hstep : ∀ n, n < N →
      RunsIn ρ (.seq body (.seq ((dec c t).liftRegs l) ((zeroTest c).liftRegs l)))
        (Function.update (st (n + 1)) c (natSyms (n + 1) ++ ct))
        (Function.update (st n) c (natSyms n ++ ct))
        (fun v => optIsBit (l.get v) = decide (0 < n))
        (B n + 6 * zerosLead (encodeNat (n + 1)) + 9) := by
    intro n hn
    have hd := RunsIn.of_runs_liftRegs l (FramePassRAux.runs_dec hct n ct
      (Function.update (st n) c (natSyms (n + 1) ++ ct)) hctm (Function.update_self _ _ _))
      (FramePassRAux.closed_dec c t) ρ
    rw [Function.update_idem] at hd
    have hz := RunsIn.of_runs_liftRegs l (FramePassRAux.runs_zeroTest c n ct
      (Function.update (st n) c (natSyms n ++ ct)) hctm (Function.update_self _ _ _))
      (FramePassRAux.closed_zeroTest c) ρ
    exact RunsIn.mono (RunsIn.seq (hbody n hn) (RunsIn.seq hd hz)) (fun _ h => h) (by omega)
  have key := RunsIn.seq_loop (st := fun n => Function.update (st n) c (natSyms n ++ ct)) h0 hstep
  refine RunsIn.congr key ?_ (by simp [countdownCost])
  simp [natSyms, encodeNat_zero]

/-- **Countdown with protected tails**: the counter terminator is local (`c = natSyms N ++ d :: ct`
with `d` not a bit), every tail on every stack, any environment; the body is given in the same
protected-tail form. -/
theorem framed_countdown {ρ : List (Prog K (fun _ => Sym) σ)} (l : Lens σ (Option Sym)) {c t : K}
    (hct : c ≠ t) {body : Prog K (fun _ => Sym) σ} (N : ℕ) (d : Sym) (hd : d.isBit = false)
    (ct : List Sym) (st : ℕ → K → List Sym) (B : ℕ → ℕ)
    (hbody : ∀ n, n < N →
      FramedRunsIn (fun _ _ => True) ρ body
        (Function.update (st (n + 1)) c (natSyms (n + 1) ++ d :: ct))
        (Function.update (st n) c (natSyms (n + 1) ++ d :: ct)) (fun _ => True) (B n)) :
    FramedRunsIn (fun _ _ => True) ρ (countdown l c t body)
      (Function.update (st N) c (natSyms N ++ d :: ct)) (Function.update (st 0) c (d :: ct))
      (fun v => optIsBit (l.get v) = false) (countdownCost B N) := by
  have hzf : ∀ (n : ℕ) (S : K → List Sym), S c = natSyms n ++ d :: ct →
      FramedRunsIn (fun _ _ => True) ρ ((zeroTest c).liftRegs l) S S
        (fun v => optIsBit (l.get v) = decide (0 < n)) 1 := by
    intro n S hS
    refine FramedRunsIn.of_runs (WP.W9comp.closed_liftRegs l (FramePassRAux.closed_zeroTest c))
      (fun τ _ => ?_) ρ
    exact WP.W0m.runs_liftRegs l (FramePassRAux.runs_zeroTest c n (d :: ct ++ τ c)
      (appendTail S τ) (TermOK.cons hd _) (by simp [hS]))
  have hdf : ∀ (n : ℕ) (S : K → List Sym), S c = natSyms (n + 1) ++ d :: ct →
      FramedRunsIn (fun _ _ => True) ρ ((dec c t).liftRegs l) S
        (Function.update S c (natSyms n ++ d :: ct)) (fun _ => True)
        (6 * zerosLead (encodeNat (n + 1)) + 8) := by
    intro n S hS
    refine FramedRunsIn.of_runs (WP.W9comp.closed_liftRegs l (FramePassRAux.closed_dec c t))
      (fun τ _ => ?_) ρ
    have h := WP.W0m.runs_liftRegs l (FramePassRAux.runs_dec hct n (d :: ct ++ τ c)
      (appendTail S τ) (TermOK.cons hd _) (by simp [hS]))
    rw [appendTail_update]
    simpa using h
  have h0 := hzf N (Function.update (st N) c (natSyms N ++ d :: ct)) (Function.update_self _ _ _)
  have hstep : ∀ n, n < N →
      FramedRunsIn (fun _ _ => True) ρ
        (.seq body (.seq ((dec c t).liftRegs l) ((zeroTest c).liftRegs l)))
        (Function.update (st (n + 1)) c (natSyms (n + 1) ++ d :: ct))
        (Function.update (st n) c (natSyms n ++ d :: ct))
        (fun v => optIsBit (l.get v) = decide (0 < n))
        (B n + 6 * zerosLead (encodeNat (n + 1)) + 9) := by
    intro n hn
    have hd' := hdf n (Function.update (st n) c (natSyms (n + 1) ++ d :: ct))
      (Function.update_self _ _ _)
    rw [Function.update_idem] at hd'
    have hz := hzf n (Function.update (st n) c (natSyms n ++ d :: ct)) (Function.update_self _ _ _)
    exact FramedRunsIn.mono (FramedRunsIn.seq (hbody n hn) (FramedRunsIn.seq hd' hz))
      (fun _ h => h) (by omega)
  have key := FramedRunsIn.seq_loop
    (st := fun n => Function.update (st n) c (natSyms n ++ d :: ct)) h0 hstep
  refine FramedRunsIn.congr key ?_ (by simp [countdownCost])
  simp [natSyms, encodeNat_zero]

end CountdownRules

#assert_std_axioms closed_passRBody closed_passR FramePassRAux.runs_peekR_eq FramePassRAux.arrSyms_cons FramePassRAux.arrSyms_nil
  FramePassRAux.arrSyms_append runs_passRBody passR_loop runs_passR framed_passR closed_countdown
  countdownCost_eq countdownCost_le runsIn_countdown framed_countdown

end SubNLogN.Machine.Calculus
