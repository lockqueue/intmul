/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Loops
import SubNLogN.Machine.K1.LongRecordBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lemma A.8 radix padding, part 1 (`Machine/AppC/C6RadixBase.lean`): unary counters

Support for `C6RadixPadStmt` / `C6RadixUnpadStmt` (`Machine/AppC/C6Leaves.lean`). All programs here
are `SProg K` (register `Option Sym`) over an arbitrary stack type `K`, and all facts are exact-stack
`RunsIn` facts (`Machine/Calculus/Basic.lean`), proved from the exact evaluations of the stream
library (`IntMulTM/Framework/Lib/Basic.lean`) and the counted-loop rule `RunsIn.seq_loop`. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Unary counters.** A counter with value `n` is the bit block `ublk n` (`n` copies of `bit true`)
on top of a stack whose remaining content is a valid terminator (`TermOK`, usually a `mark` pushed
on the arbitrary initial content of a private stack). Copying is `copyBlock`, decrementing is one
pop, the zero test is one peek.

* `cloop c body`: repeat `body` while the counter on `c` is nonempty, decrementing first
  (`runsIn_cloopL` for an arbitrary bit block, `runsIn_cloop` for `ublk n`).
* `withCtr m c tmp body`: copy the counter on `m` to a fresh counter on `c` and run `cloop`
  (`runsIn_withCtr`); `c` and `tmp` are restored.
* `mulU j P tmp`: multiply the counter on `P` by the constant `j` (`runsIn_mulU`).
* `popIfBit`, `clearBits` (`runsIn_popIfBit`, `runsIn_clearBits`).

Helpers live in `SubNLogN.Machine.AppC.C6RadixAux`.
-/

namespace SubNLogN.Machine.AppC.C6RadixAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine.Calculus

/-! ## Unary blocks -/

/-- A unary block: `n` copies of `bit true`. -/
def ublk (n : ℕ) : List Sym := (List.replicate n true).map Sym.bit

theorem ublk_zero : ublk 0 = [] := rfl

theorem ublk_succ (n : ℕ) : ublk (n + 1) = Sym.bit true :: ublk n := by
  simp [ublk, List.replicate_succ]

theorem ublk_add (a b : ℕ) : ublk (a + b) = ublk a ++ ublk b := by
  unfold ublk
  rw [List.replicate_add, List.map_append]

theorem length_ublk (n : ℕ) : (ublk n).length = n := by simp [ublk]

theorem ublk_drop (n i : ℕ) : ((List.replicate n true).drop i).map Sym.bit = ublk (n - i) := by
  simp [ublk, List.drop_replicate]

theorem head?_ublk_append {n : ℕ} {rest : List Sym} (hrest : TermOK rest) :
    optIsBit (ublk n ++ rest).head? = decide (0 < n) := by
  cases n with
  | zero =>
    rw [ublk_zero, List.nil_append]
    simpa using optIsBit_head?_of_termOK hrest
  | succ n => simp [ublk_succ]

theorem termOK_mark (X : List Sym) : TermOK (Sym.mark :: X) := by
  intro d hd
  simp only [List.head?_cons, Option.some.injEq] at hd
  subst hd
  rfl

variable {K : Type} [DecidableEq K]

/-! ## `RunsIn` from exact evaluations; atoms -/

theorem runsIn_of_eval {ρ : List (SProg K)} {P : SProg K} {S S' : K → List Sym}
    {Q : Option Sym → Prop} {T : ℕ}
    (h : ∀ v, ∃ v' t, Eval ρ P ⟨v, S⟩ ⟨v', S'⟩ t ∧ Q v' ∧ t ≤ T) : RunsIn ρ P S S' Q T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨v', t, e, hq, ht⟩ := h v
  exact ⟨⟨v', S'⟩, t, e, ⟨rfl, hq⟩, ht⟩

theorem runsIn_pushC (ρ : List (SProg K)) (k : K) (x : Sym) (S : K → List Sym) :
    RunsIn ρ (pushC k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  runsIn_of_eval fun v => ⟨v, 1, Eval.push ρ k (fun _ => x) v S, trivial, le_rfl⟩

theorem runsIn_popR (ρ : List (SProg K)) (k : K) (S : K → List Sym) (x : Sym) (l : List Sym)
    (h : S k = x :: l) :
    RunsIn ρ (popR k) S (Function.update S k l) (fun v => v = some x) 1 :=
  runsIn_of_eval fun v => ⟨some x, 1, (Eval.pop ρ k (fun _ o => o) v S).of_eq (by simp [h]) rfl,
    rfl, le_rfl⟩

theorem runsIn_peekR (ρ : List (SProg K)) (k : K) (S : K → List Sym) :
    RunsIn ρ (peekR k) S S (fun v => v = (S k).head?) 1 :=
  runsIn_of_eval fun v => ⟨(S k).head?, 1, Eval.peek ρ k (fun _ o => o) v S, rfl, le_rfl⟩

theorem runsIn_skip (ρ : List (SProg K)) (S : K → List Sym) :
    RunsIn ρ (skip : SProg K) S S (fun _ => True) 1 :=
  runsIn_of_eval fun v => ⟨v, 1, skip_eval ρ ⟨v, S⟩, trivial, le_rfl⟩

theorem runsIn_copyBlock {ρ : List (SProg K)} {src dst tmp : K} (hsd : src ≠ dst)
    (hst : src ≠ tmp) (hdt : dst ≠ tmp) (blk : List Bool) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S src = blk.map Sym.bit ++ rest) :
    RunsIn ρ (copyBlock src dst tmp) S (Function.update S dst (blk.map Sym.bit ++ S dst))
      (fun _ => True) (7 * blk.length + 7) :=
  runsIn_of_eval fun v => ⟨_, _, copyBlock_eval hsd hst hdt ρ v blk rest S hrest hS, trivial, le_rfl⟩

theorem runsIn_moveBlock {ρ : List (SProg K)} {src dst : K} (hne : src ≠ dst) (es : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = es.map Sym.bit ++ rest) :
    RunsIn ρ (moveBlock src dst) S
      (Function.update (Function.update S src rest) dst (es.reverse.map Sym.bit ++ S dst))
      (fun _ => True) (3 * es.length + 4) :=
  runsIn_of_eval fun v => ⟨_, _, moveBlock_eval hne ρ v es rest S hrest hS, trivial, le_rfl⟩

/-- Copy a unary counter. -/
theorem runsIn_copyU {ρ : List (SProg K)} {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp)
    (hdt : dst ≠ tmp) (n : ℕ) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = ublk n ++ rest) :
    RunsIn ρ (copyBlock src dst tmp) S (Function.update S dst (ublk n ++ S dst))
      (fun _ => True) (7 * n + 7) := by
  have h := runsIn_copyBlock (ρ := ρ) hsd hst hdt (List.replicate n true) rest S hrest hS
  rw [List.length_replicate] at h
  exact h

/-! ## Counter loops -/

/-- Repeat `body` while the counter (bit block) on `c` is nonempty, popping one bit first. -/
def cloop (c : K) (body : SProg K) : SProg K :=
  .seq (peekR c) (.loop optIsBit (.seq (popR c) (.seq body (peekR c))))

/-- **Counter loop over an arbitrary bit block** `bs` on `c` (above a terminator `rest`). Iteration
`i` runs `body` from data state `F i` to `F (i + 1)`, with the counter holding `bs.drop (i+1)`. -/
theorem runsIn_cloopL {ρ : List (SProg K)} {c : K} {body : SProg K} (bs : List Bool)
    {rest : List Sym} (hrest : TermOK rest) (F : ℕ → K → List Sym) (Tb : ℕ → ℕ)
    (hbody : ∀ i, i < bs.length →
      RunsIn ρ body (Function.update (F i) c ((bs.drop (i + 1)).map Sym.bit ++ rest))
        (Function.update (F (i + 1)) c ((bs.drop (i + 1)).map Sym.bit ++ rest)) (fun _ => True)
        (Tb i)) :
    RunsIn ρ (cloop c body) (Function.update (F 0) c (bs.map Sym.bit ++ rest))
      (Function.update (F bs.length) c rest) (fun v => optIsBit v = false)
      (1 + loopCost (fun m => Tb (bs.length - (m + 1)) + 2) bs.length) := by
  set L := bs.length with hL
  have h := RunsIn.seq_loop (ρ := ρ) (P₀ := peekR c) (p := .seq (popR c) (.seq body (peekR c)))
    (c := optIsBit) (st := fun m => Function.update (F (L - m)) c ((bs.drop (L - m)).map Sym.bit ++ rest))
    (S := Function.update (F 0) c (bs.map Sym.bit ++ rest))
    (B := fun m => Tb (L - (m + 1)) + 2) (N := L) (T₀ := 1) ?h0 ?hstep
  · refine RunsIn.congr h ?_ le_rfl
    simp [hL]
  · -- setup: peek
    have hp := runsIn_peekR ρ c (Function.update (F 0) c (bs.map Sym.bit ++ rest))
    refine (RunsIn.mono (RunsIn.congr hp ?_ le_rfl) ?_ le_rfl)
    · simp
    · intro v hv
      rw [hv, Function.update_self]
      cases bs with
      | nil => simpa [hL] using optIsBit_head?_of_termOK hrest
      | cons b l => simp [hL]
  · -- one iteration
    intro m hm
    have hdrop : bs.drop (L - (m + 1)) = bs[L - (m + 1)]'(by omega) :: bs.drop (L - m) := by
      rw [List.drop_eq_getElem_cons (by omega)]
      congr 2
      omega
    have hpop := runsIn_popR ρ c
      (Function.update (F (L - (m + 1))) c ((bs.drop (L - (m + 1))).map Sym.bit ++ rest))
      (Sym.bit (bs[L - (m + 1)]'(by omega))) ((bs.drop (L - m)).map Sym.bit ++ rest)
      (by rw [Function.update_self, hdrop]; rfl)
    rw [Function.update_idem] at hpop
    have hb := hbody (L - (m + 1)) (by omega)
    have e1 : L - (m + 1) + 1 = L - m := by omega
    rw [e1] at hb
    have hpk := runsIn_peekR ρ c
      (Function.update (F (L - m)) c ((bs.drop (L - m)).map Sym.bit ++ rest))
    have hall := RunsIn.seq hpop (RunsIn.seq hb hpk)
    refine RunsIn.mono hall ?_ (by omega)
    intro v hv
    rw [hv, Function.update_self]
    by_cases hm0 : m = 0
    · subst hm0
      have : bs.drop L = [] := List.drop_of_length_le (le_of_eq hL.symm)
      simp only [Nat.sub_zero, this, List.map_nil, List.nil_append, lt_self_iff_false,
        decide_false]
      exact optIsBit_head?_of_termOK hrest
    · have hlt : L - m < L := by omega
      rw [List.drop_eq_getElem_cons hlt]
      simp only [List.map_cons, List.cons_append, List.head?_cons, optIsBit_some_bit]
      exact (decide_eq_true (by omega)).symm

/-- **Counter loop over a unary counter** `ublk n`. -/
theorem runsIn_cloop {ρ : List (SProg K)} {c : K} {body : SProg K} (n : ℕ) {rest : List Sym}
    (hrest : TermOK rest) (F : ℕ → K → List Sym) (Tb : ℕ → ℕ)
    (hbody : ∀ i, i < n →
      RunsIn ρ body (Function.update (F i) c (ublk (n - (i + 1)) ++ rest))
        (Function.update (F (i + 1)) c (ublk (n - (i + 1)) ++ rest)) (fun _ => True) (Tb i)) :
    RunsIn ρ (cloop c body) (Function.update (F 0) c (ublk n ++ rest))
      (Function.update (F n) c rest) (fun v => optIsBit v = false)
      (1 + loopCost (fun m => Tb (n - (m + 1)) + 2) n) := by
  have h := runsIn_cloopL (ρ := ρ) (c := c) (body := body) (List.replicate n true) hrest F Tb
    (fun i hi => by
      rw [ublk_drop]
      exact hbody i (by simpa using hi))
  simpa [ublk] using h

/-! ## Copying a counter and looping over the copy -/

/-- Copy the counter on `m` to a fresh counter on `c` (above a `mark`) and loop over it; `c` and
`tmp` are restored. -/
def withCtr (m c tmp : K) (body : SProg K) : SProg K :=
  .seq (pushC c .mark) (.seq (copyBlock m c tmp) (.seq (cloop c body) (popR c)))

theorem runsIn_withCtr {ρ : List (SProg K)} {m c tmp : K} (hmc : m ≠ c) (hmt : m ≠ tmp)
    (hct : c ≠ tmp) {body : SProg K} (n : ℕ) {Tm : List Sym} (hTm : TermOK Tm)
    (F : ℕ → K → List Sym) (hFm : F 0 m = ublk n ++ Tm) (hF0 : F 0 c = F n c) (Tb : ℕ → ℕ)
    (hbody : ∀ i, i < n →
      RunsIn ρ body (Function.update (F i) c (ublk (n - (i + 1)) ++ Sym.mark :: F 0 c))
        (Function.update (F (i + 1)) c (ublk (n - (i + 1)) ++ Sym.mark :: F 0 c))
        (fun _ => True) (Tb i)) :
    RunsIn ρ (withCtr m c tmp body) (F 0) (F n) (fun _ => True)
      (7 * n + 10 + loopCost (fun j => Tb (n - (j + 1)) + 2) n) := by
  have h1 := runsIn_pushC ρ c Sym.mark (F 0)
  have h2 := runsIn_copyU (ρ := ρ) hmc hmt hct n Tm (Function.update (F 0) c (Sym.mark :: F 0 c))
    hTm (by rw [Function.update_of_ne hmc]; exact hFm)
  rw [Function.update_self, Function.update_idem] at h2
  have h3 := runsIn_cloop (ρ := ρ) (c := c) (body := body) n (termOK_mark (F 0 c)) F Tb hbody
  have h4 := runsIn_popR ρ c (Function.update (F n) c (Sym.mark :: F 0 c)) Sym.mark (F 0 c)
    (by rw [Function.update_self])
  rw [Function.update_idem] at h4
  have hall := RunsIn.seq h1 (RunsIn.seq h2 (RunsIn.seq h3 h4))
  have e : Function.update (F n) c (F 0 c) = F n := by rw [hF0, Function.update_eq_self]
  exact RunsIn.mono (RunsIn.congr hall e le_rfl) (fun _ _ => trivial) (by omega)

/-! ## Pushing constants; multiplying a counter by a constant -/

/-- Push `j` copies of `x` on `k`. -/
def pushN (k : K) (x : Sym) : ℕ → SProg K
  | 0 => skip
  | j + 1 => .seq (pushC k x) (pushN k x j)

theorem runsIn_pushN (ρ : List (SProg K)) (k : K) (x : Sym) :
    ∀ (j : ℕ) (S : K → List Sym),
      RunsIn ρ (pushN k x j) S (Function.update S k (List.replicate j x ++ S k)) (fun _ => True)
        (j + 1)
  | 0, S => by
    refine RunsIn.congr (runsIn_skip ρ S) ?_ le_rfl
    simp
  | j + 1, S => by
    have h1 := runsIn_pushC ρ k x S
    have h2 := runsIn_pushN ρ k x j (Function.update S k (x :: S k))
    rw [Function.update_self, Function.update_idem] at h2
    refine RunsIn.mono (RunsIn.congr (RunsIn.seq h1 h2) ?_ le_rfl) (fun _ _ => trivial)
      (by omega)
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]

theorem replicate_bit_true (j : ℕ) : List.replicate j (Sym.bit true) = ublk j := by
  simp [ublk]

/-- Multiply the unary counter on `P` by the constant `j` (using `tmp`, restored). -/
def mulU (j : ℕ) (P tmp : K) : SProg K :=
  .seq (pushC tmp .mark)
    (.seq (moveBlock P tmp) (.seq (cloop tmp (pushN P (.bit true) j)) (popR tmp)))

theorem runsIn_mulU {ρ : List (SProg K)} (j : ℕ) {P tmp : K} (hPt : P ≠ tmp) (a : ℕ)
    {T : List Sym} (hT : TermOK T) (S : K → List Sym) (hS : S P = ublk a ++ T) :
    RunsIn ρ (mulU j P tmp) S (Function.update S P (ublk (j * a) ++ T)) (fun _ => True)
      ((j + 7) * a + 8) := by
  have h1 := runsIn_pushC ρ tmp Sym.mark S
  have h2 := runsIn_moveBlock (ρ := ρ) hPt (List.replicate a true) T
    (Function.update S tmp (Sym.mark :: S tmp)) hT (by rw [Function.update_of_ne hPt]; exact hS)
  have e2 : Function.update (Function.update (Function.update S tmp (Sym.mark :: S tmp)) P T) tmp
      ((List.replicate a true).reverse.map Sym.bit ++
        Function.update S tmp (Sym.mark :: S tmp) tmp) =
      Function.update (Function.update S P (ublk (j * 0) ++ T)) tmp
        (ublk a ++ Sym.mark :: S tmp) := by
    funext x
    simp only [Function.update_apply, List.reverse_replicate, Nat.mul_zero, ublk_zero,
      List.nil_append]
    split_ifs <;> simp_all [ublk]
  rw [e2] at h2
  have h3 := runsIn_cloop (ρ := ρ) (c := tmp) (body := pushN P (.bit true) j) a
    (termOK_mark (S tmp)) (fun i => Function.update S P (ublk (j * i) ++ T)) (fun _ => j + 1)
    (fun i _ => by
      have h := runsIn_pushN ρ P (.bit true) j
        (Function.update (Function.update S P (ublk (j * i) ++ T)) tmp
          (ublk (a - (i + 1)) ++ Sym.mark :: S tmp))
      refine RunsIn.congr h ?_ le_rfl
      have e : ublk j ++ (ublk (j * i) ++ T) = ublk (j + j * i) ++ T := by
        rw [← List.append_assoc, ← ublk_add]
      have e' : ublk j ++ (ublk (j * i) ++ T) = ublk (j * i + j) ++ T := by
        rw [← List.append_assoc, ← ublk_add, Nat.add_comm]
      funext x
      simp only [Function.update_apply]
      split_ifs with h1 h2 <;> simp_all [replicate_bit_true, Nat.mul_succ])
  have h4 := runsIn_popR ρ tmp
    (Function.update (Function.update S P (ublk (j * a) ++ T)) tmp (Sym.mark :: S tmp))
    Sym.mark (S tmp) (by rw [Function.update_self])
  have e4 : Function.update (Function.update (Function.update S P (ublk (j * a) ++ T)) tmp
      (Sym.mark :: S tmp)) tmp (S tmp) = Function.update S P (ublk (j * a) ++ T) := by
    funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  rw [e4] at h4
  have hall := RunsIn.seq h1 (RunsIn.seq h2 (RunsIn.seq h3 h4))
  refine RunsIn.mono hall (fun _ _ => trivial) ?_
  rw [loopCost_const]
  simp only [List.length_replicate]
  apply le_of_eq
  ring

/-! ## Conditional pop, clearing a bit block -/

/-- Pop the top of `k` if it is a bit. -/
def popIfBit (k : K) : SProg K := .seq (peekR k) (.ite optIsBit (popR k) skip)

theorem runsIn_popIfBit {ρ : List (SProg K)} (k : K) (j : ℕ) {T : List Sym} (hT : TermOK T)
    (S : K → List Sym) (hS : S k = ublk j ++ T) :
    RunsIn ρ (popIfBit k) S (Function.update S k (ublk (j - 1) ++ T)) (fun _ => True) 3 := by
  cases j with
  | zero =>
    have hp := runsIn_peekR ρ k S
    have hS' : S k = T := by rw [hS, ublk_zero, List.nil_append]
    have hf : RunsIn ρ (peekR k) S S (fun v => optIsBit v = false) 1 := by
      refine RunsIn.mono hp (fun v hv => ?_) le_rfl
      rw [hv, hS']
      exact optIsBit_head?_of_termOK hT
    have h := RunsIn.ite_false (Pt := popR k) hf (runsIn_skip ρ S)
    refine RunsIn.congr h ?_ le_rfl
    rw [Nat.zero_sub, ublk_zero, List.nil_append, ← hS', Function.update_eq_self]
  | succ j =>
    have hp := runsIn_peekR ρ k S
    have hf : RunsIn ρ (peekR k) S S (fun v => optIsBit v = true) 1 := by
      refine RunsIn.mono hp (fun v hv => ?_) le_rfl
      rw [hv, hS, ublk_succ]
      rfl
    have hpop := runsIn_popR ρ k S (Sym.bit true) (ublk j ++ T) (by rw [hS, ublk_succ]; rfl)
    have h := RunsIn.ite_true (Pf := skip) hf hpop
    refine RunsIn.mono (RunsIn.congr h ?_ le_rfl) (fun _ _ => trivial) le_rfl
    rw [Nat.add_sub_cancel]

/-- Pop the bit block on top of `k` (the terminator below it stays). -/
def clearBits (k : K) : SProg K := cloop k skip

theorem runsIn_clearBits {ρ : List (SProg K)} (k : K) (es : List Bool) {rest : List Sym}
    (hrest : TermOK rest) (S : K → List Sym) (hS : S k = es.map Sym.bit ++ rest) :
    RunsIn ρ (clearBits k) S (Function.update S k rest) (fun _ => True) (4 * es.length + 2) := by
  have h := runsIn_cloopL (ρ := ρ) (c := k) (body := skip) es hrest (fun _ => S) (fun _ => 1)
    (fun i _ => runsIn_skip ρ _)
  rw [← hS, Function.update_eq_self] at h
  refine RunsIn.mono h (fun _ _ => trivial) ?_
  rw [loopCost_const]
  omega

