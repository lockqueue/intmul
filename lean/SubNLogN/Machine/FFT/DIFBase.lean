/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Arith

/-!
# K4-DIF base (`Machine/FFT/DIFBase.lean`): atoms, the peek-loop rule, stack moves

**Scope (honest summary).** Generic, algorithm-free machine lemmas used by the record DIF kernel
(`RecordDIFStmt`, `Contracts/FFT.lean`). Everything is proved (no `sorry`). Programs are over an
arbitrary stack type `K` and register type `σ` with a lens `lO : Lens σ (Option Sym)` (the one
register field the moves use); embedded sub-kernels keep their own register fields.

* Atoms `peekO`, `popO`, `pushK`, `mv` (pop one symbol and push it elsewhere), `dupmv`, with
  exact `Runs` lemmas.
* `ploop k c body` = `peek k; while c(reg) do (body; peek k)`. **Peek-loop rule** `runs_ploop`:
  if the stacks visit `St 0, …, St N`, the head of stack `k` passes the test exactly before the
  last state, and every iteration is a `Runs` from `St i` to `St (i+1)` (any register), then the
  loop runs from `St 0` to `St N` within `∑ (B i + 2) + 2` steps. Every loop of the kernel is an
  instance, so no loop needs its own `Eval` induction.
* `movePrefix` (move a prefix whose symbols pass a test; one `mv` per symbol, `4·|L| + 2`),
  `dupPrefix` (the same onto two stacks), `rmove` (move exactly `|ruler|` symbols, a unary ruler of
  `mark`s; `10·n + 4`), `rmoveN` (`k` ruled moves), `halveTo` (`n ↦ ⌊n/2⌋` marks), `dbl1`
  (`n ↦ 2n + 1` marks), `copyBits` (copy a bit block through a temporary stack).

Design of the whole kernel (plan; files `DIFBase`, `DIFPass`, `DIFMath`, `DIFLevel`, `DIF`):
* Data: `carrSyms w B` with records = blocks. Level `s` (`0 ≤ s < ℓ`) acts on the *blocked*
  array `B_s` (`2^{m₀+s}` records of `2^{ℓ-s}` coefficients); its half `h = 2^{ℓ-s-1}`.
* Per level: split every block into its two halves (unary ruler of `h` coefficient units, each a
  ruled move of `2w` bits), `HalfSumDiffStmt` on the halves, gather the stage table
  `[θ̃_{2^{s+1} j}]_{j<h}` once (Section 6.4, `sec:direct-fft-thm`) and replicate it once per block,
  `CMulTruncStmt` (difference × phase, then `Q_q`), interleave the two result arrays record by
  record: this is `B_{s+1}`.
* Bit reversal: `ℓ` passes, each dealing records into two streams and merging pairs by
  coefficient interleaving (unit `2w` bits); after `t` passes record `g` holds a bit-reversed
  aligned chunk of `2^t` coefficients (a shrinking/growing-block construction rather than a
  repeated whole-record unshuffle).
* Orientation: the working array lives reversed on a private stack between passes
  (`(arrSyms v).reverse`); every pass reads one orientation and writes the other, so no extra
  rewinds are needed except one at entry and one at exit.
* Uniformity: `Par = Unit`, all counters are unary mark stacks or binary `natSyms`
  stacks, all iteration is `Prog.loop`.
-/

namespace SubNLogN.Machine.FFT.DIF

open TMFw TMFw.Contracts WP.W9comp

/-! ## Atoms -/

section Atoms

variable {K σ : Type} (lO : Lens σ (Option Sym))

/-- Peek stack `k` into the register field. -/
def peekO (k : K) : Prog K (fun _ => Sym) σ := .peek k (fun v o => lO.set v o)

/-- Pop stack `k` into the register field. -/
def popO (k : K) : Prog K (fun _ => Sym) σ := .pop k (fun v o => lO.set v o)

/-- Push the register field (default `sep`) onto stack `k`. -/
def pushO (k : K) : Prog K (fun _ => Sym) σ := .push k (fun v => (lO.get v).getD .sep)

/-- Push a constant onto stack `k`. -/
def pushK (k : K) (x : Sym) : Prog K (fun _ => Sym) σ := .push k (fun _ => x)

/-- Do nothing (1 step). -/
def skipP : Prog K (fun _ => Sym) σ := .load id

/-- Move one symbol from `src` to `dst`. -/
def mv (src dst : K) : Prog K (fun _ => Sym) σ := .seq (popO lO src) (pushO lO dst)

/-- Move one symbol from `src` onto both `a` and `b`. -/
def dupmv (src a b : K) : Prog K (fun _ => Sym) σ :=
  .seq (popO lO src) (.seq (pushO lO a) (pushO lO b))

/-- The peek loop: `peek k; while c reg do (body; peek k)`. -/
def ploop (k : K) (c : Option Sym → Bool) (body : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq (peekO lO k) (.loop (fun v => c (lO.get v)) (.seq body (peekO lO k)))

theorem closed_peekO (k : K) : (peekO lO k).Closed := by
  simp [peekO, Prog.Closed, Prog.FreeBelow]
theorem closed_popO (k : K) : (popO lO k).Closed := by
  simp [popO, Prog.Closed, Prog.FreeBelow]
theorem closed_pushK (k : K) (x : Sym) : (pushK (σ := σ) k x).Closed := by
  simp [pushK, Prog.Closed, Prog.FreeBelow]
theorem closed_skipP : (skipP : Prog K (fun _ => Sym) σ).Closed := by
  simp [skipP, Prog.Closed, Prog.FreeBelow]
theorem closed_mv (src dst : K) : (mv lO src dst).Closed := by
  simp [mv, popO, pushO, Prog.Closed, Prog.FreeBelow]
theorem closed_dupmv (src a b : K) : (dupmv lO src a b).Closed := by
  simp [dupmv, popO, pushO, Prog.Closed, Prog.FreeBelow]
theorem closed_ploop (k : K) (c : Option Sym → Bool) {body : Prog K (fun _ => Sym) σ}
    (h : body.Closed) : (ploop lO k c body).Closed := by
  simp only [ploop, peekO, Prog.Closed, Prog.FreeBelow, true_and, and_true]
  exact h

end Atoms

/-! ## Runs of the atoms -/

section RunsAtoms

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

theorem runs_peekO (k : K) (S : K → List Sym) :
    Runs (peekO lO k) S S (fun v => lO.get v = (S k).head?) 1 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.peek [] k _ v stk, ⟨rfl, lO.get_set _ _⟩, le_rfl⟩

theorem runs_popO (k : K) (S : K → List Sym) :
    Runs (popO lO k) S (Function.update S k (S k).tail) (fun v => lO.get v = (S k).head?) 1 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.pop [] k _ v stk, ⟨rfl, lO.get_set _ _⟩, le_rfl⟩

theorem runs_pushK (k : K) (x : Sym) (S : K → List Sym) :
    Runs (pushK (σ := σ) k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.push [] k _ v stk, ⟨rfl, trivial⟩, le_rfl⟩

theorem runs_skipP (S : K → List Sym) :
    Runs (skipP : Prog K (fun _ => Sym) σ) S S (fun _ => True) 1 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.load [] id v stk, ⟨rfl, trivial⟩, le_rfl⟩

theorem runs_mv {src dst : K} (hne : src ≠ dst) (S : K → List Sym) {x : Sym} {l : List Sym}
    (h : S src = x :: l) :
    Runs (mv lO src dst) S (Function.update (Function.update S src l) dst (x :: S dst))
      (fun v => lO.get v = some x) 2 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  have e1 := Eval.pop [] src (fun v o => lO.set v o) v stk
  have e2 := Eval.push [] dst (fun v => (lO.get v).getD .sep) (lO.set v (stk src).head?)
    (Function.update stk src (stk src).tail)
  refine ⟨_, 2, Eval.seq e1 e2, ⟨?_, ?_⟩, le_rfl⟩
  · simp only [h, List.tail_cons, List.head?_cons, lO.get_set, Option.getD_some,
      Function.update_of_ne (Ne.symm hne)]
  · simp only [lO.get_set, h, List.head?_cons]

theorem runs_dupmv {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (S : K → List Sym) {x : Sym} {l : List Sym} (h : S src = x :: l) :
    Runs (dupmv lO src a b) S
      (Function.update (Function.update (Function.update S src l) a (x :: S a)) b (x :: S b))
      (fun v => lO.get v = some x) 3 := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  have e1 := Eval.pop [] src (fun v o => lO.set v o) v stk
  have e2 := Eval.push [] a (fun v => (lO.get v).getD .sep) (lO.set v (stk src).head?)
    (Function.update stk src (stk src).tail)
  have e3 := Eval.push [] b (fun v => (lO.get v).getD .sep) (lO.set v (stk src).head?)
    (Function.update (Function.update stk src (stk src).tail) a
      ((lO.get (lO.set v (stk src).head?)).getD .sep ::
        Function.update stk src (stk src).tail a))
  refine ⟨_, 3, Eval.seq e1 (Eval.seq e2 e3), ⟨?_, ?_⟩, le_rfl⟩
  · simp only [h, List.tail_cons, List.head?_cons, lO.get_set, Option.getD_some,
      Function.update_of_ne (Ne.symm hsa), Function.update_of_ne (Ne.symm hsb),
      Function.update_of_ne (Ne.symm hab)]
  · simp only [lO.get_set, h, List.head?_cons]

end RunsAtoms

/-! ## The peek-loop rule -/

section PLoop

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

theorem ploop_loop_eval (k : K) (c : Option Sym → Bool) (body : Prog K (fun _ => Sym) σ) :
    ∀ (N : ℕ) (St : ℕ → K → List Sym) (B : ℕ → ℕ),
      (∀ i, i ≤ N → c ((St i) k).head? = decide (i < N)) →
      (∀ i, i < N → Runs body (St i) (St (i + 1)) (fun _ => True) (B i)) →
      ∀ v : σ, lO.get v = ((St 0) k).head? →
        ∃ v' t, Eval [] (.loop (fun v => c (lO.get v)) (.seq body (peekO lO k)))
          ⟨v, St 0⟩ ⟨v', St N⟩ t ∧ t ≤ (∑ i ∈ Finset.range N, (B i + 2)) + 1
  | 0, St, B, htest, _, v, hv => by
    refine ⟨v, 1, Eval.loop_false ?_, by simp⟩
    show c (lO.get v) = false
    rw [hv, htest 0 le_rfl]
    simp
  | N + 1, St, B, htest, hbody, v, hv => by
    obtain ⟨⟨v1, s1⟩, t1, e1, ⟨hs1, -⟩, ht1⟩ := hbody 0 (Nat.succ_pos N) ⟨v, St 0⟩ rfl
    change s1 = St (0 + 1) at hs1
    subst hs1
    have e2 := Eval.peek [] k (fun v o => lO.set v o) v1 (St (0 + 1))
    obtain ⟨v', t, e3, ht⟩ := ploop_loop_eval k c body N (fun i => St (i + 1))
      (fun i => B (i + 1))
      (fun i hi => by
        show c ((St (i + 1)) k).head? = decide (i < N)
        rw [htest (i + 1) (by omega)]
        simp)
      (fun i hi => hbody (i + 1) (by omega)) (lO.set v1 ((St (0 + 1)) k).head?)
      (lO.get_set _ _)
    refine ⟨v', t1 + 1 + t + 1, Eval.loop_true ?_ (Eval.seq e1 e2) e3, ?_⟩
    · show c (lO.get v) = true
      rw [hv, htest 0 (by omega)]
      simp
    · rw [Finset.sum_range_succ']
      omega

/-- **Peek-loop rule.** -/
theorem runs_ploop (k : K) (c : Option Sym → Bool) (body : Prog K (fun _ => Sym) σ)
    (N : ℕ) (St : ℕ → K → List Sym) (B : ℕ → ℕ)
    (htest : ∀ i, i ≤ N → c ((St i) k).head? = decide (i < N))
    (hbody : ∀ i, i < N → Runs body (St i) (St (i + 1)) (fun _ => True) (B i)) :
    Runs (ploop lO k c body) (St 0) (St N) (fun _ => True)
      ((∑ i ∈ Finset.range N, (B i + 2)) + 2) := by
  rintro ⟨v, stk⟩ hs
  change stk = St 0 at hs
  subst hs
  have e0 := Eval.peek [] k (fun v o => lO.set v o) v (St 0)
  obtain ⟨v', t, e, ht⟩ := ploop_loop_eval lO k c body N St B htest hbody
    (lO.set v ((St 0) k).head?) (lO.get_set _ _)
  exact ⟨⟨v', St N⟩, 1 + t, Eval.seq e0 e, ⟨rfl, trivial⟩, by omega⟩

/-- **Peek-loop rule**, uniform iteration bound. -/
theorem runs_ploop_const (k : K) (c : Option Sym → Bool) (body : Prog K (fun _ => Sym) σ)
    (N : ℕ) (St : ℕ → K → List Sym) (B : ℕ)
    (htest : ∀ i, i ≤ N → c ((St i) k).head? = decide (i < N))
    (hbody : ∀ i, i < N → Runs body (St i) (St (i + 1)) (fun _ => True) B) :
    Runs (ploop lO k c body) (St 0) (St N) (fun _ => True) (N * (B + 2) + 2) := by
  have h := runs_ploop lO k c body N St (fun _ => B) htest hbody
  simpa [Finset.sum_const, Finset.card_range] using h

end PLoop

/-! ## Prefix moves -/

section Moves

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- Move the longest prefix of `src` passing `c` onto `dst`, one symbol at a time. -/
def movePrefix (src dst : K) (c : Option Sym → Bool) : Prog K (fun _ => Sym) σ :=
  ploop lO src c (mv lO src dst)

omit [DecidableEq K] in
theorem closed_movePrefix (src dst : K) (c : Option Sym → Bool) :
    (movePrefix lO src dst c).Closed :=
  closed_ploop lO src c (closed_mv lO src dst)

theorem runs_movePrefix {src dst : K} (hne : src ≠ dst) (c : Option Sym → Bool)
    (S : K → List Sym) (L R : List Sym) (hS : S src = L ++ R)
    (hL : ∀ x ∈ L, c (some x) = true) (hR : c R.head? = false) :
    Runs (movePrefix lO src dst c) S
      (Function.update (Function.update S src R) dst (L.reverse ++ S dst)) (fun _ => True)
      (4 * L.length + 2) := by
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update S src (L.drop i ++ R)) dst ((L.take i).reverse ++ S dst)
  have h0 : St 0 = S := by
    funext j
    simp only [St, Function.update_apply]
    split_ifs <;> simp_all
  have hN : St L.length =
      Function.update (Function.update S src R) dst (L.reverse ++ S dst) := by
    simp only [St, List.drop_length, List.nil_append, List.take_length]
  have h := runs_ploop_const lO src c (mv lO src dst) L.length St 2 ?_ ?_
  · rw [h0, hN] at h
    exact runs_mono h (fun _ _ => trivial) (by omega)
  · intro i hi
    have hsrc : St i src = L.drop i ++ R := by
      simp only [St, Function.update_of_ne hne, Function.update_self]
    rw [hsrc]
    rcases Nat.lt_or_ge i L.length with hlt | hge
    · rw [List.drop_eq_getElem_cons hlt]
      simp [hL _ (List.getElem_mem hlt), hlt]
    · have hi' : i = L.length := le_antisymm hi hge
      subst hi'
      simp [hR]
  · intro i hi
    have hx : St i src = L[i] :: (L.drop (i + 1) ++ R) := by
      simp only [St, Function.update_of_ne hne, Function.update_self]
      rw [List.drop_eq_getElem_cons hi]
      rfl
    refine runs_congr (runs_mono (runs_mv lO hne (St i) hx) (fun _ _ => trivial) le_rfl) ?_
    have ht : (L.take (i + 1)).reverse = L[i] :: (L.take i).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      simp
    funext j
    simp only [St, Function.update_apply, ht]
    split_ifs <;> simp_all

/-- Move the longest prefix of `src` passing `c` onto both `a` and `b`. -/
def dupPrefix (src a b : K) (c : Option Sym → Bool) : Prog K (fun _ => Sym) σ :=
  ploop lO src c (dupmv lO src a b)

omit [DecidableEq K] in
theorem closed_dupPrefix (src a b : K) (c : Option Sym → Bool) :
    (dupPrefix lO src a b c).Closed :=
  closed_ploop lO src c (closed_dupmv lO src a b)

theorem runs_dupPrefix {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (c : Option Sym → Bool)
    (S : K → List Sym) (L R : List Sym) (hS : S src = L ++ R)
    (hL : ∀ x ∈ L, c (some x) = true) (hR : c R.head? = false) :
    Runs (dupPrefix lO src a b c) S
      (Function.update (Function.update (Function.update S src R) a (L.reverse ++ S a)) b
        (L.reverse ++ S b)) (fun _ => True)
      (5 * L.length + 2) := by
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (Function.update S src (L.drop i ++ R)) a
      ((L.take i).reverse ++ S a)) b ((L.take i).reverse ++ S b)
  have h0 : St 0 = S := by
    funext j
    simp only [St, Function.update_apply]
    split_ifs <;> simp_all
  have hN : St L.length = Function.update (Function.update (Function.update S src R) a
      (L.reverse ++ S a)) b (L.reverse ++ S b) := by
    simp only [St, List.drop_length, List.nil_append, List.take_length]
  have hsrc : ∀ i, St i src = L.drop i ++ R := fun i => by
    simp only [St, Function.update_of_ne hsa, Function.update_of_ne hsb, Function.update_self]
  have h := runs_ploop_const lO src c (dupmv lO src a b) L.length St 3 ?_ ?_
  · rw [h0, hN] at h
    exact runs_mono h (fun _ _ => trivial) (by omega)
  · intro i hi
    rw [hsrc]
    rcases Nat.lt_or_ge i L.length with hlt | hge
    · rw [List.drop_eq_getElem_cons hlt]
      simp [hL _ (List.getElem_mem hlt), hlt]
    · have hi' : i = L.length := le_antisymm hi hge
      subst hi'
      simp [hR]
  · intro i hi
    have hx : St i src = L[i] :: (L.drop (i + 1) ++ R) := by
      rw [hsrc, List.drop_eq_getElem_cons hi]
      rfl
    refine runs_congr (runs_mono (runs_dupmv lO hsa hsb hab (St i) hx) (fun _ _ => trivial)
      le_rfl) ?_
    have ht : (L.take (i + 1)).reverse = L[i] :: (L.take i).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      simp
    funext j
    simp only [St, Function.update_apply, ht]
    split_ifs <;> simp_all

end Moves

/-! ## Small helpers -/

theorem isSome_head?_replicate (n : ℕ) (x : Sym) :
    ((List.replicate n x).head?).isSome = decide (0 < n) := by
  cases n <;> simp

section Helpers

variable {K σ : Type} [DecidableEq K]

theorem runs_seq_ite_t {P p q : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {S1 S2 S3 : K → List Sym} {Q : σ → Prop} {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q T1)
    (hc : ∀ v, Q v → c v = true) (h2 : Runs p S2 S3 (fun _ => True) T2) :
    Runs (.seq P (.ite c p q)) S1 S3 (fun _ => True) (T1 + (T2 + 1)) := by
  rintro ⟨v, stk⟩ hs
  obtain ⟨⟨v1, s1⟩, t1, e1, ⟨hs1, hq⟩, ht1⟩ := h1 ⟨v, stk⟩ hs
  obtain ⟨s', t2, e2, hq2, ht2⟩ := h2 ⟨v1, s1⟩ hs1
  exact ⟨s', t1 + (t2 + 1), Eval.seq e1 (Eval.ite_true (hc v1 hq) e2), hq2, by omega⟩

theorem runs_seq_ite_f {P p q : Prog K (fun _ => Sym) σ} {c : σ → Bool}
    {S1 S2 S3 : K → List Sym} {Q : σ → Prop} {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q T1)
    (hc : ∀ v, Q v → c v = false) (h2 : Runs q S2 S3 (fun _ => True) T2) :
    Runs (.seq P (.ite c p q)) S1 S3 (fun _ => True) (T1 + (T2 + 1)) := by
  rintro ⟨v, stk⟩ hs
  obtain ⟨⟨v1, s1⟩, t1, e1, ⟨hs1, hq⟩, ht1⟩ := h1 ⟨v, stk⟩ hs
  obtain ⟨s', t2, e2, hq2, ht2⟩ := h2 ⟨v1, s1⟩ hs1
  exact ⟨s', t1 + (t2 + 1), Eval.seq e1 (Eval.ite_false (hc v1 hq) e2), hq2, by omega⟩

/-- Sequencing, forgetting the first register post-condition. -/
theorem runs_seq' {P Q : Prog K (fun _ => Sym) σ} {S1 S2 S3 : K → List Sym} {Q1 Q2 : σ → Prop}
    {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q1 T1) (h2 : Runs Q S2 S3 Q2 T2) :
    Runs (.seq P Q) S1 S3 (fun _ => True) (T1 + T2) :=
  runs_mono (runs_seq h1 h2) (fun _ _ => trivial) le_rfl

end Helpers

/-! ## Ruled moves and mark counters -/

section Ruled

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- One ruled step: consume a ruler mark (parked on `A`), then move one symbol. -/
def rstep (src dst R A : K) : Prog K (fun _ => Sym) σ :=
  .seq (popO lO R) (.seq (pushK A .mark) (mv lO src dst))

/-- Ruled move: move exactly `|R|` symbols from `src` to `dst` (`R` a stack of `mark`s, parked
on `A` and restored). -/
def rmove (src dst R A : K) : Prog K (fun _ => Sym) σ :=
  .seq (ploop lO R Option.isSome (rstep lO src dst R A)) (movePrefix lO A R Option.isSome)

omit [DecidableEq K] in
theorem closed_rmove (src dst R A : K) : (rmove lO src dst R A).Closed := by
  refine ⟨closed_ploop lO R _ ?_, closed_movePrefix lO A R _⟩
  exact ⟨closed_popO lO R, closed_pushK A .mark, closed_mv lO src dst⟩

theorem runs_rmove {src dst R A : K} (h1 : src ≠ dst) (h2 : src ≠ R) (h3 : src ≠ A)
    (h4 : dst ≠ R) (h5 : dst ≠ A) (h6 : R ≠ A) (S : K → List Sym) (L srest : List Sym)
    (hR : S R = List.replicate L.length .mark) (hA : S A = []) (hS : S src = L ++ srest) :
    Runs (rmove lO src dst R A) S
      (Function.update (Function.update S src srest) dst (L.reverse ++ S dst)) (fun _ => True)
      (10 * L.length + 4) := by
  let n := L.length
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (Function.update (Function.update S R
      (List.replicate (n - i) .mark)) A (List.replicate i .mark)) src (L.drop i ++ srest)) dst
      ((L.take i).reverse ++ S dst)
  have hStR : ∀ i, St i R = List.replicate (n - i) .mark := fun i => by
    simp only [St, Function.update_of_ne (Ne.symm h4), Function.update_of_ne (Ne.symm h2),
      Function.update_of_ne h6, Function.update_self]
  have hStA : ∀ i, St i A = List.replicate i .mark := fun i => by
    simp only [St, Function.update_of_ne (Ne.symm h5), Function.update_of_ne (Ne.symm h3),
      Function.update_self]
  have hStsrc : ∀ i, St i src = L.drop i ++ srest := fun i => by
    simp only [St, Function.update_of_ne h1, Function.update_self]
  have h0 : St 0 = S := by
    funext j
    simp only [St, Function.update_apply]
    split_ifs <;> simp_all [n, List.replicate_succ]
  have hloop := runs_ploop_const lO R Option.isSome (rstep lO src dst R A) n St 4 ?_ ?_
  · rw [h0] at hloop
    have hA' : St n A = List.replicate n .mark ++ [] := by rw [hStA, List.append_nil]
    have hrest := runs_movePrefix lO h6.symm Option.isSome (St n) (List.replicate n .mark) []
      hA' (by simp) rfl
    refine runs_congr (runs_mono (runs_seq hloop hrest) (fun _ _ => trivial) ?_) ?_
    · simp only [List.length_replicate, n]
      omega
    · funext j
      simp only [St, Function.update_apply]
      split_ifs <;> simp_all [n, List.replicate_succ]
  · intro i hi
    rw [hStR, isSome_head?_replicate]
    exact decide_eq_decide.mpr (by omega)
  · intro i hi
    have hd : L.drop i = L[i] :: L.drop (i + 1) := List.drop_eq_getElem_cons hi
    have ht : (L.take (i + 1)).reverse = L[i] :: (L.take i).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      simp
    have hrep : List.replicate (n - i) Sym.mark = Sym.mark :: List.replicate (n - (i + 1)) .mark := by
      rw [show n - i = (n - (i + 1)) + 1 by omega, List.replicate_succ]
    have e1 := runs_popO lO R (St i)
    have e2 := runs_pushK (σ := σ) A .mark (Function.update (St i) R (St i R).tail)
    have hx : Function.update (Function.update (St i) R (St i R).tail) A
        (Sym.mark :: Function.update (St i) R (St i R).tail A) src =
        L[i] :: (L.drop (i + 1) ++ srest) := by
      rw [Function.update_of_ne h3, Function.update_of_ne h2, hStsrc, hd]
      rfl
    have e3 := runs_mv lO h1 _ hx
    refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 e3)) (fun _ _ => trivial) le_rfl) ?_
    funext j
    simp only [St, Function.update_apply, ht]
    split_ifs <;> simp_all [n, List.replicate_succ]

/-- `k` ruled moves: move `k·|R|` symbols, where `k = |H|` (marks parked on `HA`, restored). -/
def rmoveN (src dst H HA R A : K) : Prog K (fun _ => Sym) σ :=
  .seq (ploop lO H Option.isSome (.seq (popO lO H) (.seq (pushK HA .mark) (rmove lO src dst R A))))
    (movePrefix lO HA H Option.isSome)

omit [DecidableEq K] in
theorem closed_rmoveN (src dst H HA R A : K) : (rmoveN lO src dst H HA R A).Closed := by
  refine ⟨closed_ploop lO H _ ?_, closed_movePrefix lO HA H _⟩
  exact ⟨closed_popO lO H, closed_pushK HA .mark, closed_rmove lO src dst R A⟩

theorem runs_rmoveN {src dst H HA R A : K} (h1 : src ≠ dst) (h2 : src ≠ H) (h3 : src ≠ HA)
    (h4 : src ≠ R) (h5 : src ≠ A) (h6 : dst ≠ H) (h7 : dst ≠ HA) (h8 : dst ≠ R) (h9 : dst ≠ A)
    (h10 : H ≠ HA) (h11 : H ≠ R) (h12 : H ≠ A) (h13 : HA ≠ R) (h14 : HA ≠ A) (h15 : R ≠ A)
    (S : K → List Sym) (k n : ℕ) (L srest : List Sym)
    (hH : S H = List.replicate k .mark) (hHA : S HA = []) (hR : S R = List.replicate n .mark)
    (hA : S A = []) (hS : S src = L ++ srest) (hL : L.length = k * n) :
    Runs (rmoveN lO src dst H HA R A) S
      (Function.update (Function.update S src srest) dst (L.reverse ++ S dst)) (fun _ => True)
      (k * (10 * n + 8) + 4 * k + 4) := by
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (Function.update (Function.update S H
      (List.replicate (k - i) .mark)) HA (List.replicate i .mark)) src (L.drop (i * n) ++ srest))
      dst ((L.take (i * n)).reverse ++ S dst)
  have hStH : ∀ i, St i H = List.replicate (k - i) .mark := fun i => by
    simp only [St, Function.update_of_ne (Ne.symm h6), Function.update_of_ne (Ne.symm h2),
      Function.update_of_ne h10, Function.update_self]
  have hStHA : ∀ i, St i HA = List.replicate i .mark := fun i => by
    simp only [St, Function.update_of_ne (Ne.symm h7), Function.update_of_ne (Ne.symm h3),
      Function.update_self]
  have hStsrc : ∀ i, St i src = L.drop (i * n) ++ srest := fun i => by
    simp only [St, Function.update_of_ne h1, Function.update_self]
  have h0 : St 0 = S := by
    funext j
    simp only [St, Function.update_apply]
    split_ifs <;> simp_all
  have hloop := runs_ploop_const lO H Option.isSome
    (.seq (popO lO H) (.seq (pushK HA .mark) (rmove lO src dst R A))) k St (10 * n + 6) ?_ ?_
  · rw [h0] at hloop
    have hHA' : St k HA = List.replicate k .mark ++ [] := by rw [hStHA, List.append_nil]
    have hrest := runs_movePrefix lO h10.symm Option.isSome (St k) (List.replicate k .mark) []
      hHA' (by simp) rfl
    have hkn : L.drop (k * n) = [] := List.drop_of_length_le (by omega)
    have hkn' : L.take (k * n) = L := List.take_of_length_le (by omega)
    refine runs_congr (runs_mono (runs_seq hloop hrest) (fun _ _ => trivial) ?_) ?_
    · simp only [List.length_replicate]
      nlinarith
    · funext j
      simp only [St, Function.update_apply, hkn, hkn']
      split_ifs <;> simp_all
  · intro i hi
    rw [hStH, isSome_head?_replicate]
    exact decide_eq_decide.mpr (by omega)
  · intro i hi
    have hrep : List.replicate (k - i) Sym.mark = Sym.mark :: List.replicate (k - (i + 1)) .mark := by
      rw [show k - i = (k - (i + 1)) + 1 by omega, List.replicate_succ]
    have e1 := runs_popO lO H (St i)
    have e2 := runs_pushK (σ := σ) HA .mark (Function.update (St i) H (St i H).tail)
    set S2 := Function.update (Function.update (St i) H (St i H).tail) HA
        (Sym.mark :: Function.update (St i) H (St i H).tail HA) with hS2
    have hlen : ((L.drop (i * n)).take n).length = n := by
      rw [List.length_take, List.length_drop]
      have : (i + 1) * n ≤ k * n := Nat.mul_le_mul_right n hi
      rw [Nat.add_mul, one_mul] at this
      omega
    have hS2src : S2 src = (L.drop (i * n)).take n ++ ((L.drop (i * n)).drop n ++ srest) := by
      rw [hS2, Function.update_of_ne h3, Function.update_of_ne h2, hStsrc, ← List.append_assoc,
        List.take_append_drop]
    have hS2R : S2 R = List.replicate ((L.drop (i * n)).take n).length .mark := by
      rw [hlen, hS2, Function.update_of_ne h13.symm, Function.update_of_ne h11.symm]
      simp only [St, Function.update_of_ne (Ne.symm h8), Function.update_of_ne (Ne.symm h4),
        Function.update_of_ne h13.symm, Function.update_of_ne h11.symm, hR]
    have hS2A : S2 A = [] := by
      rw [hS2, Function.update_of_ne h14.symm, Function.update_of_ne h12.symm]
      simp only [St, Function.update_of_ne (Ne.symm h9), Function.update_of_ne (Ne.symm h5),
        Function.update_of_ne h14.symm, Function.update_of_ne h12.symm, hA]
    have e3 := runs_rmove lO h1 h4 h5 h8 h9 h15 S2 _ _ hS2R hS2A hS2src
    rw [hlen] at e3
    have hdrop : (L.drop (i * n)).drop n = L.drop ((i + 1) * n) := by
      rw [List.drop_drop, Nat.add_mul, one_mul]
    have htake : ((L.drop (i * n)).take n).reverse ++ (L.take (i * n)).reverse =
        (L.take ((i + 1) * n)).reverse := by
      rw [← List.reverse_append, Nat.add_mul, one_mul, List.take_add]
    refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 e3)) (fun _ _ => trivial)
      (by omega)) ?_
    funext j
    simp only [hS2, St, Function.update_apply, hdrop]
    split_ifs <;> simp_all [← htake, List.replicate_succ]

/-- Halve a mark counter: `src` (`n` marks) is emptied and `⌊n/2⌋` marks are pushed on `dst`. -/
def halveTo (src dst : K) : Prog K (fun _ => Sym) σ :=
  ploop lO src Option.isSome (.seq (popO lO src) (.seq (popO lO src)
    (.ite (fun v => (lO.get v).isSome) (pushK dst .mark) skipP)))

omit [DecidableEq K] in
theorem closed_halveTo (src dst : K) : (halveTo lO src dst).Closed := by
  refine closed_ploop lO src _ ⟨closed_popO lO src, closed_popO lO src, ?_, ?_⟩
  · exact closed_pushK dst .mark
  · exact closed_skipP

theorem runs_halveTo {src dst : K} (hne : src ≠ dst) (S : K → List Sym) (n : ℕ)
    (hS : S src = List.replicate n .mark) :
    Runs (halveTo lO src dst) S
      (Function.update (Function.update S src []) dst (List.replicate (n / 2) .mark ++ S dst))
      (fun _ => True) (3 * n + 5) := by
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update S src (List.replicate (n - 2 * i) .mark)) dst
      (List.replicate (min i (n / 2)) .mark ++ S dst)
  have hStsrc : ∀ i, St i src = List.replicate (n - 2 * i) .mark := fun i => by
    simp only [St, Function.update_of_ne hne, Function.update_self]
  have hStdst : ∀ i, St i dst = List.replicate (min i (n / 2)) .mark ++ S dst := fun i => by
    simp only [St, Function.update_self]
  have h0 : St 0 = S := by
    funext j
    simp only [St, Function.update_apply]
    split_ifs <;> simp_all
  have hloop := runs_ploop_const lO src Option.isSome (.seq (popO lO src) (.seq (popO lO src)
    (.ite (fun v => (lO.get v).isSome) (pushK dst .mark) skipP))) ((n + 1) / 2) St 4 ?_ ?_
  · rw [h0] at hloop
    refine runs_congr (runs_mono hloop (fun _ _ => trivial) (by omega)) ?_
    have e1 : n - 2 * ((n + 1) / 2) = 0 := by omega
    have e2 : min ((n + 1) / 2) (n / 2) = n / 2 := by omega
    funext j
    simp only [St, Function.update_apply, e1, e2, List.replicate_zero]
  · intro i hi
    rw [hStsrc, isSome_head?_replicate]
    exact decide_eq_decide.mpr (by omega)
  · intro i hi
    have e1 := runs_popO lO src (St i)
    set S1 := Function.update (St i) src (St i src).tail with hS1
    have e2 := runs_popO lO src S1
    set S2 := Function.update S1 src (S1 src).tail with hS2
    have hS1src : S1 src = List.replicate (n - 2 * i - 1) .mark := by
      rw [hS1, Function.update_self, hStsrc, List.tail_replicate]
    rcases Nat.lt_or_ge (2 * i + 1) n with hlt | hge
    · -- two marks available: push one
      have e3 := runs_pushK (σ := σ) dst .mark S2
      have hc : ∀ v, lO.get v = (S1 src).head? → (lO.get v).isSome = true := by
        intro v hv
        rw [hv, hS1src, show n - 2 * i - 1 = (n - 2 * i - 2) + 1 by omega, List.replicate_succ]
        rfl
      refine runs_congr (runs_mono (runs_seq' e1 (runs_seq_ite_t e2 hc e3))
        (fun _ _ => trivial) le_rfl) ?_
      have hm : min (i + 1) (n / 2) = min i (n / 2) + 1 := by omega
      funext j
      simp only [hS2, hS1, St, Function.update_apply, hm, List.replicate_succ]
      split_ifs <;> simp_all [List.tail_replicate, Nat.sub_sub, Nat.mul_add]
    · -- one mark left: skip
      have e3 := runs_skipP (σ := σ) S2
      have hc : ∀ v, lO.get v = (S1 src).head? → (lO.get v).isSome = false := by
        intro v hv
        rw [hv, hS1src, show n - 2 * i - 1 = 0 by omega]
        rfl
      refine runs_congr (runs_mono (runs_seq' e1 (runs_seq_ite_f e2 hc e3))
        (fun _ _ => trivial) le_rfl) ?_
      have hm : min (i + 1) (n / 2) = min i (n / 2) := by omega
      have hz : n - 2 * (i + 1) = 0 := by omega
      have hz' : n - 2 * i - 1 = 0 := by omega
      funext j
      simp only [hS2, hS1, St, Function.update_apply, hm, hz]
      split_ifs <;> simp_all [List.tail_replicate, hz']

/-- `src` (`n` marks) becomes `2n + 1` marks (via `aux`). -/
def dbl1 (src aux : K) : Prog K (fun _ => Sym) σ :=
  .seq (ploop lO src Option.isSome (.seq (popO lO src) (.seq (pushK aux .mark) (pushK aux .mark))))
    (.seq (pushK aux .mark) (movePrefix lO aux src Option.isSome))

omit [DecidableEq K] in
theorem closed_dbl1 (src aux : K) : (dbl1 lO src aux).Closed := by
  refine ⟨closed_ploop lO src _ ⟨closed_popO lO src, closed_pushK aux .mark,
    closed_pushK aux .mark⟩, closed_pushK aux .mark, closed_movePrefix lO aux src _⟩

theorem runs_dbl1 {src aux : K} (hne : src ≠ aux) (S : K → List Sym) (n : ℕ)
    (hS : S src = List.replicate n .mark) (ha : S aux = []) :
    Runs (dbl1 lO src aux) S (Function.update S src (List.replicate (2 * n + 1) .mark))
      (fun _ => True) (13 * n + 9) := by
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update S src (List.replicate (n - i) .mark)) aux
      (List.replicate (2 * i) .mark)
  have hStsrc : ∀ i, St i src = List.replicate (n - i) .mark := fun i => by
    simp only [St, Function.update_of_ne hne, Function.update_self]
  have h0 : St 0 = S := by
    funext j
    simp only [St, Function.update_apply]
    split_ifs <;> simp_all
  have hloop := runs_ploop_const lO src Option.isSome
    (.seq (popO lO src) (.seq (pushK aux .mark) (pushK aux .mark))) n St 3 ?_ ?_
  · rw [h0] at hloop
    have e2 := runs_pushK (σ := σ) aux .mark (St n)
    have haux : Function.update (St n) aux (Sym.mark :: St n aux) aux =
        List.replicate (2 * n + 1) .mark ++ [] := by
      simp only [St, Function.update_self, List.append_nil, List.replicate_succ]
    have e3 := runs_movePrefix lO hne.symm Option.isSome _ _ [] haux (by simp) rfl
    refine runs_congr (runs_mono (runs_seq hloop (runs_seq' e2 e3)) (fun _ _ => trivial)
      (by simp only [List.length_replicate]; omega)) ?_
    funext j
    simp only [St, Function.update_apply]
    split_ifs <;> simp_all
  · intro i hi
    rw [hStsrc, isSome_head?_replicate]
    exact decide_eq_decide.mpr (by omega)
  · intro i hi
    have e1 := runs_popO lO src (St i)
    set S1 := Function.update (St i) src (St i src).tail with hS1
    have e2 := runs_pushK (σ := σ) aux .mark S1
    have e3 := runs_pushK (σ := σ) aux .mark (Function.update S1 aux (Sym.mark :: S1 aux))
    refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 e3)) (fun _ _ => trivial)
      le_rfl) ?_
    have hm : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    funext j
    simp only [hS1, St, Function.update_apply, hm, List.replicate_succ]
    split_ifs <;> simp_all [List.tail_replicate, Nat.sub_sub]

/-- Empty stack `k`. -/
def drain (k : K) : Prog K (fun _ => Sym) σ := ploop lO k Option.isSome (popO lO k)

omit [DecidableEq K] in
theorem closed_drain (k : K) : (drain lO k).Closed := closed_ploop lO k _ (closed_popO lO k)

theorem runs_drain (k : K) (S : K → List Sym) :
    Runs (drain lO k) S (Function.update S k []) (fun _ => True) (3 * (S k).length + 2) := by
  let St : ℕ → K → List Sym := fun i => Function.update S k ((S k).drop i)
  have h0 : St 0 = S := by simp [St]
  have hloop := runs_ploop_const lO k Option.isSome (popO lO k) (S k).length St 1 ?_ ?_
  · rw [h0] at hloop
    refine runs_congr (runs_mono hloop (fun _ _ => trivial) (by omega)) ?_
    simp [St]
  · intro i hi
    simp only [St, Function.update_self]
    rcases Nat.lt_or_ge i (S k).length with hlt | hge
    · rw [List.drop_eq_getElem_cons hlt]
      simp [hlt]
    · rw [List.drop_of_length_le hge]
      simp
      omega
  · intro i hi
    refine runs_congr (runs_mono (runs_popO lO k (St i)) (fun _ _ => trivial) le_rfl) ?_
    simp only [St, Function.update_self, Function.update_idem, List.tail_drop]

/-- Copy the bit block on top of `src` onto `dst` (same order) through `tmp`. -/
def copyBits (src dst tmp : K) : Prog K (fun _ => Sym) σ :=
  .seq (movePrefix lO src tmp optIsBit) (dupPrefix lO tmp src dst optIsBit)

omit [DecidableEq K] in
theorem closed_copyBits (src dst tmp : K) : (copyBits lO src dst tmp).Closed :=
  ⟨closed_movePrefix lO src tmp _, closed_dupPrefix lO tmp src dst _⟩

theorem runs_copyBits {src dst tmp : K} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (S : K → List Sym) (p : List Bool) (R : List Sym) (hS : S src = p.map Sym.bit ++ R)
    (hR : TermOK R) (ht : TermOK (S tmp)) :
    Runs (copyBits lO src dst tmp) S (Function.update S dst (p.map Sym.bit ++ S dst))
      (fun _ => True) (9 * p.length + 4) := by
  have hbits : ∀ x ∈ p.map Sym.bit, optIsBit (some x) = true := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
    rfl
  have e1 := runs_movePrefix lO h2 optIsBit S (p.map Sym.bit) R hS hbits
    (optIsBit_head?_of_termOK hR)
  set S1 := Function.update (Function.update S src R) tmp ((p.map Sym.bit).reverse ++ S tmp)
    with hS1
  have hS1t : S1 tmp = (p.map Sym.bit).reverse ++ S tmp := by rw [hS1, Function.update_self]
  have e2 := runs_dupPrefix lO h2.symm h3.symm h1 optIsBit S1 _ _ hS1t
    (fun x hx => hbits x (List.mem_reverse.1 hx)) (optIsBit_head?_of_termOK ht)
  refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial)
    (by simp only [List.length_reverse, List.length_map]; omega)) ?_
  funext j
  simp only [hS1, Function.update_apply, List.reverse_reverse]
  split_ifs <;> simp_all

end Ruled


/-! ## Canonical update chains -/

section Upd

variable {K : Type} [DecidableEq K]

/-- Four stack updates in a fixed order (a canonical state of a pass). -/
def upd4 (S : K → List Sym) (k1 k2 k3 k4 : K) (v1 v2 v3 v4 : List Sym) : K → List Sym :=
  Function.update (Function.update (Function.update (Function.update S k1 v1) k2 v2) k3 v3) k4 v4

variable {S : K → List Sym} {k1 k2 k3 k4 : K} {v1 v2 v3 v4 : List Sym}

theorem upd4_1 (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h14 : k1 ≠ k4) :
    upd4 S k1 k2 k3 k4 v1 v2 v3 v4 k1 = v1 := by
  simp only [upd4, Function.update_of_ne h14, Function.update_of_ne h13,
    Function.update_of_ne h12, Function.update_self]

theorem upd4_2 (h23 : k2 ≠ k3) (h24 : k2 ≠ k4) : upd4 S k1 k2 k3 k4 v1 v2 v3 v4 k2 = v2 := by
  simp only [upd4, Function.update_of_ne h24, Function.update_of_ne h23, Function.update_self]

theorem upd4_3 (h34 : k3 ≠ k4) : upd4 S k1 k2 k3 k4 v1 v2 v3 v4 k3 = v3 := by
  simp only [upd4, Function.update_of_ne h34, Function.update_self]

theorem upd4_4 : upd4 S k1 k2 k3 k4 v1 v2 v3 v4 k4 = v4 := by
  simp only [upd4, Function.update_self]

theorem upd4_o {x : K} (h1 : x ≠ k1) (h2 : x ≠ k2) (h3 : x ≠ k3) (h4 : x ≠ k4) :
    upd4 S k1 k2 k3 k4 v1 v2 v3 v4 x = S x := by
  simp only [upd4, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
    Function.update_of_ne h1]

theorem upd4_set1 (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h14 : k1 ≠ k4) (v : List Sym) :
    Function.update (upd4 S k1 k2 k3 k4 v1 v2 v3 v4) k1 v = upd4 S k1 k2 k3 k4 v v2 v3 v4 := by
  unfold upd4
  rw [Function.update_comm h14.symm, Function.update_comm h13.symm, Function.update_comm h12.symm,
    Function.update_idem]

theorem upd4_set2 (h23 : k2 ≠ k3) (h24 : k2 ≠ k4) (v : List Sym) :
    Function.update (upd4 S k1 k2 k3 k4 v1 v2 v3 v4) k2 v = upd4 S k1 k2 k3 k4 v1 v v3 v4 := by
  unfold upd4
  rw [Function.update_comm h24.symm, Function.update_comm h23.symm, Function.update_idem]

theorem upd4_set3 (h34 : k3 ≠ k4) (v : List Sym) :
    Function.update (upd4 S k1 k2 k3 k4 v1 v2 v3 v4) k3 v = upd4 S k1 k2 k3 k4 v1 v2 v v4 := by
  unfold upd4
  rw [Function.update_comm h34.symm, Function.update_idem]

theorem upd4_set4 (v : List Sym) :
    Function.update (upd4 S k1 k2 k3 k4 v1 v2 v3 v4) k4 v = upd4 S k1 k2 k3 k4 v1 v2 v3 v := by
  unfold upd4
  rw [Function.update_idem]

theorem upd4_self : upd4 S k1 k2 k3 k4 (S k1) (S k2) (S k3) (S k4) = S := by
  unfold upd4
  simp only [Function.update_eq_self]


/-- Five stack updates in a fixed order. -/
def upd5 (S : K → List Sym) (k1 k2 k3 k4 k5 : K) (v1 v2 v3 v4 v5 : List Sym) : K → List Sym :=
  Function.update (upd4 S k1 k2 k3 k4 v1 v2 v3 v4) k5 v5

variable {k5 : K} {v5 : List Sym}

theorem upd5_1 (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h14 : k1 ≠ k4) (h15 : k1 ≠ k5) :
    upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v4 v5 k1 = v1 := by
  rw [upd5, Function.update_of_ne h15, upd4_1 h12 h13 h14]

theorem upd5_2 (h23 : k2 ≠ k3) (h24 : k2 ≠ k4) (h25 : k2 ≠ k5) :
    upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v4 v5 k2 = v2 := by
  rw [upd5, Function.update_of_ne h25, upd4_2 h23 h24]

theorem upd5_3 (h34 : k3 ≠ k4) (h35 : k3 ≠ k5) :
    upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v4 v5 k3 = v3 := by
  rw [upd5, Function.update_of_ne h35, upd4_3 h34]

theorem upd5_4 (h45 : k4 ≠ k5) : upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v4 v5 k4 = v4 := by
  rw [upd5, Function.update_of_ne h45, upd4_4]

theorem upd5_5 : upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v4 v5 k5 = v5 := by
  rw [upd5, Function.update_self]

theorem upd5_o {x : K} (h1 : x ≠ k1) (h2 : x ≠ k2) (h3 : x ≠ k3) (h4 : x ≠ k4) (h5 : x ≠ k5) :
    upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v4 v5 x = S x := by
  rw [upd5, Function.update_of_ne h5, upd4_o h1 h2 h3 h4]

theorem upd5_set1 (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h14 : k1 ≠ k4) (h15 : k1 ≠ k5) (v : List Sym) :
    Function.update (upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v4 v5) k1 v =
      upd5 S k1 k2 k3 k4 k5 v v2 v3 v4 v5 := by
  rw [upd5, upd5, Function.update_comm h15.symm, upd4_set1 h12 h13 h14]

theorem upd5_set2 (h23 : k2 ≠ k3) (h24 : k2 ≠ k4) (h25 : k2 ≠ k5) (v : List Sym) :
    Function.update (upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v4 v5) k2 v =
      upd5 S k1 k2 k3 k4 k5 v1 v v3 v4 v5 := by
  rw [upd5, upd5, Function.update_comm h25.symm, upd4_set2 h23 h24]

theorem upd5_set3 (h34 : k3 ≠ k4) (h35 : k3 ≠ k5) (v : List Sym) :
    Function.update (upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v4 v5) k3 v =
      upd5 S k1 k2 k3 k4 k5 v1 v2 v v4 v5 := by
  rw [upd5, upd5, Function.update_comm h35.symm, upd4_set3 h34]

theorem upd5_set4 (h45 : k4 ≠ k5) (v : List Sym) :
    Function.update (upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v4 v5) k4 v =
      upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v v5 := by
  rw [upd5, upd5, Function.update_comm h45.symm, upd4_set4]

theorem upd5_set5 (v : List Sym) :
    Function.update (upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v4 v5) k5 v =
      upd5 S k1 k2 k3 k4 k5 v1 v2 v3 v4 v := by
  rw [upd5, upd5, Function.update_idem]

theorem upd5_self : upd5 S k1 k2 k3 k4 k5 (S k1) (S k2) (S k3) (S k4) (S k5) = S := by
  rw [upd5, upd4_self, Function.update_eq_self]

end Upd

/-! ## List combinators -/

/-- Interleave: `[a₀, b₀, a₁, b₁, …]` (stops at the shorter list). -/
def inter {α : Type} : List α → List α → List α
  | a :: as, b :: bs => a :: b :: inter as bs
  | _, _ => []

/-- Entries at even positions. -/
def evens {α : Type} : List α → List α
  | a :: _ :: t => a :: evens t
  | _ => []

/-- Entries at odd positions. -/
def odds {α : Type} : List α → List α
  | _ :: b :: t => b :: odds t
  | _ => []

theorem length_inter {α : Type} :
    ∀ (as bs : List α), as.length = bs.length → (inter as bs).length = 2 * as.length
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [inter, List.length_cons]
    rw [length_inter as bs (by simpa using h)]
    ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem inter_append_pair {α : Type} :
    ∀ (as bs : List α) (a b : α), as.length = bs.length →
      inter (as ++ [a]) (bs ++ [b]) = inter as bs ++ [a, b]
  | [], [], a, b, _ => rfl
  | x :: as, y :: bs, a, b, h => by
    simp only [List.cons_append, inter]
    rw [inter_append_pair as bs a b (by simpa using h)]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem evens_inter {α : Type} :
    ∀ (as bs : List α), as.length = bs.length → evens (inter as bs) = as
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [inter, evens]
    rw [evens_inter as bs (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem odds_inter {α : Type} :
    ∀ (as bs : List α), as.length = bs.length → odds (inter as bs) = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [inter, odds]
    rw [odds_inter as bs (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

end SubNLogN.Machine.FFT.DIF
