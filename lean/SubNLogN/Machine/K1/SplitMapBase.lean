/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Streams
import WP.W3s.Math

/-!
# K1/K5 shared kit (`K1/SplitMapBase.lean`): exact-state specs, peek loops, unary-depth recursion

**Scope (honest summary).** Generic, algorithm-free program builders and their proved rules,
shared by the K1c proof (`K1SplitMapMergeStmt`, files `K1/SplitMap*.lean`) and the K5 proof
(`K5UnitMulStmt`, files `K1/Unit*.lean`). No contract is proved in this file.

## Plan of the two proofs (paper: Fact 3.3 (`fact:oai-streams`), Lemma A.4 (`lem:transfer-streams`))

**K1c, split / pointwise map / merge** (Lemma A.4(3) (`lem:transfer-streams`)). The array has `q^k`
records; digit `i` splits it into `q^i` *superblocks* of `q` *blocks* of `L = q^m` records,
`m = k-1-i`; the `q` blocks of a superblock are the `q` aligned streams.
* Setup (only for `q ≥ 2`): the depth stack receives `m` unary tokens (binary counters `k`, `i`
  are decremented to zero; cost `O(k·bitLen k)`, absorbed since `V ≥ q^k ≥ 2^k`).
* Per superblock: (split) block `c` is moved to stream stack `c` by the unary-depth recursion
  `recProg` (exactly `q^m` record moves, overhead `≤ 11·q^m` steps); (map) aligned record
  tuples are popped from the `q` streams (which hold the blocks reversed), each `digitWidth A`-bit
  digit tuple is read into a finite register buffer, `g` is applied, and the output digits are
  pushed on `q` output stacks, which then hold the output blocks in `.down` orientation; (merge)
  the output stacks are rewound in order `0..q-1` onto an accumulator (orientation `.up`).
* End: the accumulator is rewound onto the destination (orientation `.down`).
* `q = 1`: one record; no counters are read (their length is not bounded by `V`).
* Cost: every symbol is moved a bounded number of times; per record and per digit tuple the
  overhead is `O(q·digitWidth A)`, a constant of the contract. Total `C·(V + 1)`.

**K5, unit multiplication** (Lemma A.4 (`lem:transfer-streams`): intervals of `x ↦ ax - kQ`, merging by
the cyclic residue pattern; inverse by the reversed schedule; a rational unit is an integer
multiplication composed with an inverse one). For `q ≥ 2` and nonempty input: unary `b` on the
depth stack; `Q mod a`, `Q mod d` in registers. Pass A (multiply by `a`) per fiber: move the
fiber while counting the residue classes in unary; cut into `a` intervals by the counts; merge by
the residue pattern. Pass D (divide by `d`) per fiber: distribute by the residue pattern;
concatenate. `q ≤ 1` and the empty input are the identity (no counter is read).

## Contents
* `KP K M`: programs with registers `Option Sym × M`; `lift` runs a `TMFw.Lib` macro on the first
  component. `RunsM P m S m' S' T`: exact stacks and exact state `M`, any `Option Sym` slot.
* `whileTop k c body` (peek loop) with `runsM_whileTop`.
* `recProg q dk act` (unary-depth recursion: `q^e` runs of `act` when the depth stack `dk` holds
  `e` tokens) with `runsM_recProg`; cost `Σ c + 11·q^e`.
* `dispatch sel ps n` (case split on a register value) with `eval_dispatch`.
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts

/-! ## Register layout, lifting, closedness -/

/-- Kernel programs over stacks `K`: alphabet `Sym`, registers `Option Sym × M`. -/
abbrev KP (K M : Type) := Prog K (fun _ => Sym) (Option Sym × M)

/-- Run a library macro (registers `Option Sym`) on the first register component. -/
def lift {K M : Type} (p : Lib.SProg K) : KP K M := p.liftRegs (Lens.fst _ _)

theorem closed_lift {K M : Type} {p : Lib.SProg K} (hp : p.Closed) : (lift (M := M) p).Closed :=
  WP.W9comp.closed_liftRegs _ hp

/-- `FreeBelow` is monotone in the bound. -/
theorem freeBelow_mono {K : Type} {Γ : K → Type} {σ : Type} :
    ∀ (p : Prog K Γ σ) {d d' : ℕ}, d ≤ d' → p.FreeBelow d → p.FreeBelow d'
  | .push _ _, _, _, _, _ => trivial
  | .peek _ _, _, _, _, _ => trivial
  | .pop _ _, _, _, _, _ => trivial
  | .load _, _, _, _, _ => trivial
  | .seq p q, _, _, h, hp => ⟨freeBelow_mono p h hp.1, freeBelow_mono q h hp.2⟩
  | .ite _ p q, _, _, h, hp => ⟨freeBelow_mono p h hp.1, freeBelow_mono q h hp.2⟩
  | .loop _ p, _, _, h, hp => freeBelow_mono p h hp
  | .fix b, _, _, h, hp => freeBelow_mono b (Nat.add_le_add_right h 1) hp
  | .recur _, _, _, h, hp => lt_of_lt_of_le hp h

/-! ## Programs (no `DecidableEq` needed) -/

section Progs

variable {K M : Type}

/-- Peek the top of stack `k` into the `Option Sym` slot. -/
def peekO (k : K) : KP K M := .peek k (fun r o => (o, r.2))

/-- Test an optional symbol with `c` (`false` at the stack bottom). -/
def testO (c : Sym → Bool) : Option Sym → Bool
  | some x => c x
  | none => false

/-- `whileTop k c body`: while the top of `k` satisfies `c`, run `body`. -/
def whileTop (k : K) (c : Sym → Bool) (body : KP K M) : KP K M :=
  .seq (peekO k) (.loop (fun r => testO c r.1) (.seq body (peekO k)))

/-- `rep p n`: `p` repeated `n` times, then one `skip`. -/
def rep (p : KP K M) : ℕ → KP K M
  | 0 => Lib.skip
  | n + 1 => .seq p (rep p n)

/-- The unary depth token. -/
def tok : Sym := .bit true

/-- Is the `Option Sym` slot the depth token? -/
def isTokO (r : Option Sym × M) : Bool := decide (r.1 = some tok)

/-- Body of the unary-depth recursion: if the depth stack `dk` shows a token, pop it, call the
procedure `q` times and push the token back; otherwise run `act` once. -/
def recBody (q : ℕ) (dk : K) (act : KP K M) : KP K M :=
  .seq (peekO dk) (.ite isTokO
    (.seq (.pop dk fun r _ => r) (.seq (rep (.recur 0) q) (.push dk fun _ => tok))) act)

/-- **Unary-depth recursion**: with `e` tokens on `dk`, `act` runs `q^e` times. -/
def recProg (q : ℕ) (dk : K) (act : KP K M) : KP K M := .fix (recBody q dk act)

/-- Case split on a register value: run `ps j` when `sel r = j < n`. -/
def dispatch (sel : Option Sym × M → ℕ) (ps : ℕ → KP K M) : ℕ → KP K M
  | 0 => Lib.skip
  | n + 1 => .ite (fun r => decide (sel r = n)) (ps n) (dispatch sel ps n)

theorem closed_whileTop (k : K) (c : Sym → Bool) {body : KP K M} (h : body.Closed) :
    (whileTop k c body).Closed :=
  ⟨trivial, h, trivial⟩

theorem closed_recProg (q : ℕ) (dk : K) {act : KP K M} (h : act.Closed) :
    (recProg q dk act).Closed := by
  refine ⟨trivial, ⟨trivial, ?_, trivial⟩, freeBelow_mono act (Nat.zero_le 1) h⟩
  induction q with
  | zero => trivial
  | succ n ih => exact ⟨Nat.zero_lt_one, ih⟩

theorem closed_dispatch (sel : Option Sym × M → ℕ) {ps : ℕ → KP K M} (h : ∀ j, (ps j).Closed) :
    ∀ n, (dispatch sel ps n).Closed
  | 0 => trivial
  | n + 1 => ⟨h n, closed_dispatch sel h n⟩

end Progs

/-! ## Exact-state specifications -/

section RunsM

variable {K M : Type} [DecidableEq K]

/-- From stacks `S` and state `m` (any `Option Sym` slot), `P` reaches stacks `S'` and state
`m'` within `T` steps. -/
def RunsM (P : KP K M) (m : M) (S : K → List Sym) (m' : M) (S' : K → List Sym) (T : ℕ) :
    Prop :=
  ∀ o : Option Sym, ∃ o' t, t ≤ T ∧ Eval [] P ⟨(o, m), S⟩ ⟨(o', m'), S'⟩ t

theorem RunsM.seq {P Q : KP K M} {m1 m2 m3 : M} {S1 S2 S3 : K → List Sym} {T1 T2 : ℕ}
    (h1 : RunsM P m1 S1 m2 S2 T1) (h2 : RunsM Q m2 S2 m3 S3 T2) :
    RunsM (.seq P Q) m1 S1 m3 S3 (T1 + T2) := by
  intro o
  obtain ⟨o1, t1, ht1, e1⟩ := h1 o
  obtain ⟨o2, t2, ht2, e2⟩ := h2 o1
  exact ⟨o2, t1 + t2, Nat.add_le_add ht1 ht2, Eval.seq e1 e2⟩

theorem RunsM.mono {P : KP K M} {m m' : M} {S S' : K → List Sym} {T T' : ℕ}
    (h : RunsM P m S m' S' T) (hT : T ≤ T') : RunsM P m S m' S' T' := by
  intro o
  obtain ⟨o', t, ht, e⟩ := h o
  exact ⟨o', t, ht.trans hT, e⟩

theorem RunsM.congr {P : KP K M} {m m' : M} {S S' S'' : K → List Sym} {T : ℕ}
    (h : RunsM P m S m' S' T) (hS : S' = S'') : RunsM P m S m' S'' T := hS ▸ h

/-- A library macro, given by evaluations from every register, keeps the state `m`. -/
theorem RunsM.ofLib {p : Lib.SProg K} {S S' : K → List Sym} {T : ℕ}
    (h : ∀ o : Option Sym, ∃ o' t, t ≤ T ∧ Eval [] p ⟨o, S⟩ ⟨o', S'⟩ t) (m : M) :
    RunsM (lift p) m S m S' T := by
  intro o
  obtain ⟨o', t, ht, e⟩ := h o
  exact ⟨o', t, ht, Eval.liftRegs (Lens.fst _ _) e (o, m) rfl⟩

theorem RunsM.load (f : M → M) (m : M) (S : K → List Sym) :
    RunsM (.load fun r => (r.1, f r.2)) m S (f m) S 1 :=
  fun o => ⟨o, 1, le_rfl, Eval.load _ _ _ _⟩

theorem RunsM.push (k : K) (x : Sym) (m : M) (S : K → List Sym) :
    RunsM (lift (Lib.pushC k x)) m S m (Function.update S k (x :: S k)) 1 :=
  RunsM.ofLib (fun o => ⟨o, 1, le_rfl, Eval.push _ _ _ _ _⟩) m

theorem RunsM.pop (k : K) (x : Sym) (L : List Sym) (m : M) (S : K → List Sym)
    (hS : S k = x :: L) : RunsM (lift (Lib.popR k)) m S m (Function.update S k L) 1 := by
  refine RunsM.ofLib (fun o => ⟨some x, 1, le_rfl, ?_⟩) m
  have e := Eval.pop [] k (fun (_ : Option Sym) o => o) o S
  rw [hS] at e
  exact e

theorem RunsM.skip (m : M) (S : K → List Sym) : RunsM (Lib.skip : KP K M) m S m S 1 :=
  fun o => ⟨o, 1, le_rfl, Lib.skip_eval _ _⟩

/-- **Initialization.** A `RunsM` spec from state `m0`, preceded by a register load of `m0`, is a
`Runs` spec (any initial register). -/
theorem runs_of_runsM {P : KP K M} {m0 m' : M} {S S' : K → List Sym} {T : ℕ}
    (h : RunsM P m0 S m' S' T) :
    Runs (.seq (.load fun r => (r.1, m0)) P) S S' (fun _ => True) (T + 1) := by
  intro s hs
  obtain ⟨⟨o, m⟩, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨o', t, ht, e⟩ := h o
  exact ⟨⟨(o', m'), S'⟩, 1 + t, Eval.seq (Eval.load _ _ _ _) e, ⟨rfl, trivial⟩, by omega⟩

/-! ## Peek loops -/

theorem eval_loopTop (k : K) (c : Sym → Bool) (body : KP K M) :
    ∀ (n : ℕ) (m : ℕ → M) (S : ℕ → K → List Sym) (T : ℕ → ℕ),
      (∀ i < n, testO c (S i k).head? = true ∧
        RunsM body (m i) (S i) (m (i + 1)) (S (i + 1)) (T i)) →
      testO c (S n k).head? = false →
      ∃ t, t ≤ (∑ i ∈ Finset.range n, (T i + 2)) + 1 ∧
        Eval [] (.loop (fun r => testO c r.1) (.seq body (peekO k)))
          ⟨((S 0 k).head?, m 0), S 0⟩ ⟨((S n k).head?, m n), S n⟩ t := by
  intro n
  induction n with
  | zero =>
    intro m S T _ hstop
    exact ⟨1, by simp, Eval.loop_false hstop⟩
  | succ n ih =>
    intro m S T hstep hstop
    obtain ⟨hc0, hb0⟩ := hstep 0 (Nat.succ_pos n)
    obtain ⟨o1, t0, ht0, e0⟩ := hb0 ((S 0 k).head?)
    have ep : Eval [] (peekO (M := M) k) ⟨(o1, m 1), S 1⟩ ⟨((S 1 k).head?, m 1), S 1⟩ 1 :=
      Eval.peek _ _ _ _ _
    obtain ⟨t, ht, e⟩ := ih (fun i => m (i + 1)) (fun i => S (i + 1)) (fun i => T (i + 1))
      (fun i hi => hstep (i + 1) (by omega)) hstop
    refine ⟨t0 + 1 + t + 1, ?_, Eval.loop_true hc0 (Eval.seq e0 ep) e⟩
    rw [Finset.sum_range_succ']
    omega

/-- **Peek-loop rule.** Iteration `i` runs `body` from `(m i, S i)` to `(m (i+1), S (i+1))`
while the top of `k` satisfies `c`; at `n` it does not. Cost `Σ (T i + 2) + 2`. -/
theorem runsM_whileTop (k : K) (c : Sym → Bool) (body : KP K M) (n : ℕ) (m : ℕ → M)
    (S : ℕ → K → List Sym) (T : ℕ → ℕ)
    (hstep : ∀ i < n, testO c (S i k).head? = true ∧
      RunsM body (m i) (S i) (m (i + 1)) (S (i + 1)) (T i))
    (hstop : testO c (S n k).head? = false) :
    RunsM (whileTop k c body) (m 0) (S 0) (m n) (S n)
      ((∑ i ∈ Finset.range n, (T i + 2)) + 2) := by
  intro o
  obtain ⟨t, ht, e⟩ := eval_loopTop k c body n m S T hstep hstop
  exact ⟨_, 1 + t, by omega, Eval.seq (Eval.peek _ _ _ _ _) e⟩

/-! ## Cost sums and the recursion overhead -/

/-- `csum c n0 len = c n0 + c (n0+1) + … + c (n0+len-1)`. -/
def csum (c : ℕ → ℕ) (n0 : ℕ) : ℕ → ℕ
  | 0 => 0
  | len + 1 => c n0 + csum c (n0 + 1) len

theorem csum_add (c : ℕ → ℕ) : ∀ (a n0 b : ℕ), csum c n0 (a + b) = csum c n0 a + csum c (n0 + a) b
  | 0, n0, b => by simp [csum]
  | a + 1, n0, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega, csum, csum, csum_add c a (n0 + 1) b,
      show n0 + 1 + a = n0 + (a + 1) by omega]
    omega

theorem csum_mono {c c' : ℕ → ℕ} (h : ∀ n, c n ≤ c' n) : ∀ (n0 len : ℕ), csum c n0 len ≤ csum c' n0 len
  | _, 0 => le_rfl
  | n0, len + 1 => Nat.add_le_add (h n0) (csum_mono h (n0 + 1) len)

theorem csum_const (b : ℕ) : ∀ (n0 len : ℕ), csum (fun _ => b) n0 len = b * len
  | _, 0 => by simp [csum]
  | n0, len + 1 => by rw [csum, csum_const b (n0 + 1) len, Nat.mul_succ]; omega

/-- Overhead of `recBody` at depth `e` (beyond the runs of `act`). -/
def recE (q : ℕ) : ℕ → ℕ
  | 0 => 2
  | e + 1 => q * (recE q e + 2) + 5

theorem recE_le (q : ℕ) (hq : 2 ≤ q) : ∀ e, recE q e + 9 ≤ 11 * q ^ e
  | 0 => by simp [recE]
  | e + 1 => by
    have ih := recE_le q hq e
    have h1 : q * (recE q e + 9) ≤ q * (11 * q ^ e) := Nat.mul_le_mul_left q ih
    have h2 : q * (recE q e + 2) + 7 * q = q * (recE q e + 9) := by ring
    have h3 : q * (11 * q ^ e) = 11 * q ^ (e + 1) := by ring
    rw [recE]
    omega

/-! ## The unary-depth recursion -/

section Rec

variable (q : ℕ) (dk : K) (act : KP K M)

theorem eval_rep_recur (D : List Sym) (N : ℕ) (m : ℕ → M) (S : ℕ → K → List Sym) (c : ℕ → ℕ)
    (e : ℕ)
    (ih : ∀ n0, n0 + q ^ e ≤ N → ∀ o : Option Sym, ∃ o' t, t ≤ csum c n0 (q ^ e) + recE q e ∧
      Eval [recBody q dk act] (recBody q dk act)
        ⟨(o, m n0), Function.update (S n0) dk (List.replicate e tok ++ D)⟩
        ⟨(o', m (n0 + q ^ e)), Function.update (S (n0 + q ^ e)) dk (List.replicate e tok ++ D)⟩
        t) :
    ∀ (j n1 : ℕ), n1 + j * q ^ e ≤ N → ∀ o : Option Sym, ∃ o' t,
      t ≤ csum c n1 (j * q ^ e) + j * (recE q e + 2) + 1 ∧
      Eval [recBody q dk act] (rep (.recur 0) j)
        ⟨(o, m n1), Function.update (S n1) dk (List.replicate e tok ++ D)⟩
        ⟨(o', m (n1 + j * q ^ e)),
          Function.update (S (n1 + j * q ^ e)) dk (List.replicate e tok ++ D)⟩ t
  | 0, n1, _, o => by
    simp only [Nat.zero_mul, Nat.add_zero]
    exact ⟨o, 1, by simp [csum], Lib.skip_eval _ _⟩
  | j + 1, n1, hN, o => by
    obtain ⟨o1, t1, ht1, e1⟩ := ih n1 (by rw [Nat.succ_mul] at hN; omega) o
    have hN' : (n1 + q ^ e) + j * q ^ e ≤ N := by rw [Nat.succ_mul] at hN; omega
    obtain ⟨o2, t2, ht2, e2⟩ := eval_rep_recur D N m S c e ih j (n1 + q ^ e) hN' o1
    have hidx : n1 + q ^ e + j * q ^ e = n1 + (j + 1) * q ^ e := by rw [Nat.succ_mul]; omega
    rw [hidx] at e2
    refine ⟨o2, (t1 + 2) + t2, ?_, Eval.seq (Eval.recur (n := 0) rfl e1) e2⟩
    have hc := csum_add c (q ^ e) n1 (j * q ^ e)
    rw [show q ^ e + j * q ^ e = (j + 1) * q ^ e by rw [Nat.succ_mul]; omega] at hc
    rw [hc, Nat.succ_mul]
    omega

theorem eval_recBody (hact : act.Closed) (D : List Sym) (hD : D.head? ≠ some tok) (N : ℕ)
    (m : ℕ → M) (S : ℕ → K → List Sym) (c : ℕ → ℕ)
    (hdk : ∀ n ≤ N, S n dk = D)
    (hstep : ∀ n < N, RunsM act (m n) (S n) (m (n + 1)) (S (n + 1)) (c n)) :
    ∀ (e n0 : ℕ), n0 + q ^ e ≤ N → ∀ o : Option Sym, ∃ o' t, t ≤ csum c n0 (q ^ e) + recE q e ∧
      Eval [recBody q dk act] (recBody q dk act)
        ⟨(o, m n0), Function.update (S n0) dk (List.replicate e tok ++ D)⟩
        ⟨(o', m (n0 + q ^ e)), Function.update (S (n0 + q ^ e)) dk (List.replicate e tok ++ D)⟩
        t
  | 0, n0, hN, o => by
    simp only [pow_zero] at hN ⊢
    have h0 : Function.update (S n0) dk (List.replicate 0 tok ++ D) = S n0 := by
      rw [List.replicate_zero, List.nil_append, ← hdk n0 (by omega), Function.update_eq_self]
    have h1 : Function.update (S (n0 + 1)) dk (List.replicate 0 tok ++ D) = S (n0 + 1) := by
      rw [List.replicate_zero, List.nil_append, ← hdk (n0 + 1) hN, Function.update_eq_self]
    rw [h0, h1]
    obtain ⟨o', t, ht, e⟩ := hstep n0 (by omega) ((S n0 dk).head?)
    have ep : Eval [recBody q dk act] (peekO (M := M) dk) ⟨(o, m n0), S n0⟩
        ⟨((S n0 dk).head?, m n0), S n0⟩ 1 := Eval.peek _ _ _ _ _
    have hc : isTokO ((S n0 dk).head?, m n0) = false := by
      rw [hdk n0 (by omega)]
      simpa [isTokO] using hD
    refine ⟨o', 1 + (t + 1), ?_, Eval.seq ep (Eval.ite_false hc (e.env_irrel hact _))⟩
    simp only [csum, recE]
    omega
  | e + 1, n0, hN, o => by
    have hpow : q ^ (e + 1) = q * q ^ e := by rw [pow_succ, Nat.mul_comm]
    rw [hpow] at hN ⊢
    have hdk0 : Function.update (S n0) dk (List.replicate (e + 1) tok ++ D) dk =
        tok :: (List.replicate e tok ++ D) := by
      rw [Function.update_self, List.replicate_succ, List.cons_append]
    have ep : Eval [recBody q dk act] (peekO (M := M) dk)
        ⟨(o, m n0), Function.update (S n0) dk (List.replicate (e + 1) tok ++ D)⟩
        ⟨(some tok, m n0), Function.update (S n0) dk (List.replicate (e + 1) tok ++ D)⟩ 1 := by
      refine (Eval.peek _ _ _ _ _).of_eq ?_ rfl
      rw [hdk0]
      rfl
    have epop : Eval [recBody q dk act] (.pop dk fun r _ => r)
        ⟨(some tok, m n0), Function.update (S n0) dk (List.replicate (e + 1) tok ++ D)⟩
        ⟨(some tok, m n0), Function.update (S n0) dk (List.replicate e tok ++ D)⟩ 1 := by
      refine (Eval.pop _ _ _ _ _).of_eq ?_ rfl
      rw [hdk0, Function.update_idem]
      rfl
    obtain ⟨o2, t2, ht2, e2⟩ := eval_rep_recur q dk act D N m S c e
      (eval_recBody hact D hD N m S c hdk hstep e) q n0 hN (some tok)
    have epush : Eval [recBody q dk act] (.push dk fun _ => tok)
        ⟨(o2, m (n0 + q * q ^ e)),
          Function.update (S (n0 + q * q ^ e)) dk (List.replicate e tok ++ D)⟩
        ⟨(o2, m (n0 + q * q ^ e)),
          Function.update (S (n0 + q * q ^ e)) dk (List.replicate (e + 1) tok ++ D)⟩ 1 := by
      refine (Eval.push _ _ _ _ _).of_eq ?_ rfl
      rw [Function.update_self, Function.update_idem]
      simp [List.replicate_succ]
    refine ⟨o2, 1 + ((1 + (t2 + 1)) + 1), ?_,
      Eval.seq ep (Eval.ite_true rfl (Eval.seq epop (Eval.seq e2 epush)))⟩
    simp only [recE]
    omega

/-- **Unary-depth recursion rule.** Let `act` (closed) run from `(m n, S n)` to
`(m (n+1), S (n+1))` within `c n` for `n < N`, never touching the depth stack `dk` (`S n dk = D`,
whose top is not a token). With `e` tokens on `dk`, `recProg q dk act` performs the `q^e` steps
starting at `n0` (`n0 + q^e ≤ N`), within `Σ c + 11·q^e`, and restores `dk`. -/
theorem runsM_recProg (hact : act.Closed) (D : List Sym) (hD : D.head? ≠ some tok)
    (N : ℕ) (m : ℕ → M) (S : ℕ → K → List Sym) (c : ℕ → ℕ)
    (hdk : ∀ n ≤ N, S n dk = D)
    (hstep : ∀ n < N, RunsM act (m n) (S n) (m (n + 1)) (S (n + 1)) (c n))
    (e n0 : ℕ) (hq : 2 ≤ q ∨ e = 0) (hN : n0 + q ^ e ≤ N) :
    RunsM (recProg q dk act) (m n0) (Function.update (S n0) dk (List.replicate e tok ++ D))
      (m (n0 + q ^ e)) (Function.update (S (n0 + q ^ e)) dk (List.replicate e tok ++ D))
      (csum c n0 (q ^ e) + 11 * q ^ e) := by
  intro o
  obtain ⟨o', t, ht, ev⟩ := eval_recBody q dk act hact D hD N m S c hdk hstep e n0 hN o
  have hE : recE q e + 2 ≤ 11 * q ^ e := by
    rcases hq with hq | rfl
    · have := recE_le q hq e
      omega
    · simp [recE]
  exact ⟨o', t + 2, by omega, Eval.fix ev⟩

end Rec

/-! ## Dispatch -/

theorem eval_dispatch (sel : Option Sym × M → ℕ) (ps : ℕ → KP K M) {ρ : List (KP K M)}
    {v : Option Sym × M} {S : K → List Sym} {s' : St K (fun _ => Sym) (Option Sym × M)} {t j : ℕ}
    (hj : sel v = j) (h : Eval ρ (ps j) ⟨v, S⟩ s' t) :
    ∀ n, j < n → Eval ρ (dispatch sel ps n) ⟨v, S⟩ s' (t + (n - j))
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    by_cases hjn : j = n
    · subst hjn
      exact (Eval.ite_true (by simp [hj]) h).of_eq rfl (by omega)
    · have ih := eval_dispatch sel ps hj h n (by omega)
      exact (Eval.ite_false (by simpa [hj] using hjn) ih).of_eq rfl (by omega)

end RunsM

end SubNLogN.Machine.K1.SMM
