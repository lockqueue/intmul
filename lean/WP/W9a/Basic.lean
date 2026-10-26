import Contracts.W9.Common
import Contracts.W9.Sweep
import IntMulTM.Framework.Lib.Counter

/-!
# WP.W9a.Basic — generic macros and facts for the W9 combinators

* Register lifts: `liftQ` runs a one-symbol-register macro (`SProg`) inside registers
  `R × Option Sym`, `liftK` runs a component with registers `R` there (`liftQ_eval`, `liftK_eval`).
* Closedness of lifted and renamed programs.
* Macros over `SProg K` with exact evaluation lemmas:
  * `moveUntil src dst stop`: move symbols until the popped one satisfies `stop` (it stays in the
    register);
  * `dropUntil src stop`: the same without pushing;
  * `countLoop Kc t body`: run `body` once per unit of a binary counter on `Kc` (decrementing it
    first). The decrements are charged with the amortised `incSeqCost`, so `n` iterations cost
    `O(n)` plus the body costs.
* `sumTo` algebra and the upward indexed loop rule `Triple.loop_up`.
* Symbol facts: entries contain no layout tag and no `mark`; streams start with a node symbol.
* `outer` frame lemmas.
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Closedness -/

theorem freeBelow_liftRegs {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ) :
    ∀ (p : Prog K Γ τ) (d : ℕ), (p.liftRegs l).FreeBelow d ↔ p.FreeBelow d
  | .push _ _, _ => Iff.rfl
  | .peek _ _, _ => Iff.rfl
  | .pop _ _, _ => Iff.rfl
  | .load _, _ => Iff.rfl
  | .seq p q, d => and_congr (freeBelow_liftRegs l p d) (freeBelow_liftRegs l q d)
  | .ite _ p q, d => and_congr (freeBelow_liftRegs l p d) (freeBelow_liftRegs l q d)
  | .loop _ p, d => freeBelow_liftRegs l p d
  | .fix b, d => freeBelow_liftRegs l b (d + 1)
  | .recur _, _ => Iff.rfl

theorem freeBelow_mapStk {K K' A σ : Type} (ι : K → K') :
    ∀ (p : Prog K (fun _ => A) σ) (d : ℕ), (p.mapStk ι).FreeBelow d ↔ p.FreeBelow d
  | .push _ _, _ => Iff.rfl
  | .peek _ _, _ => Iff.rfl
  | .pop _ _, _ => Iff.rfl
  | .load _, _ => Iff.rfl
  | .seq p q, d => and_congr (freeBelow_mapStk ι p d) (freeBelow_mapStk ι q d)
  | .ite _ p q, d => and_congr (freeBelow_mapStk ι p d) (freeBelow_mapStk ι q d)
  | .loop _ p, d => freeBelow_mapStk ι p d
  | .fix b, d => freeBelow_mapStk ι b (d + 1)
  | .recur _, _ => Iff.rfl

theorem closed_liftRegs {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ) {p : Prog K Γ τ}
    (h : p.Closed) : (p.liftRegs l).Closed :=
  (freeBelow_liftRegs l p 0).2 h

theorem closed_mapStk {K K' A σ : Type} (ι : K → K') {p : Prog K (fun _ => A) σ}
    (h : p.Closed) : (p.mapStk ι).Closed :=
  (freeBelow_mapStk ι p 0).2 h

section ClosedRules

variable {K : Type} {Γ : K → Type} {σ : Type}

theorem closed_seq {p q : Prog K Γ σ} (hp : p.Closed) (hq : q.Closed) : (Prog.seq p q).Closed :=
  ⟨hp, hq⟩

theorem closed_ite {c : σ → Bool} {p q : Prog K Γ σ} (hp : p.Closed) (hq : q.Closed) :
    (Prog.ite c p q).Closed :=
  ⟨hp, hq⟩

theorem closed_loop {c : σ → Bool} {p : Prog K Γ σ} (hp : p.Closed) : (Prog.loop c p).Closed := hp

theorem closed_push (k : K) (f : σ → Γ k) : (Prog.push k f).Closed := trivial

theorem closed_peek (k : K) (f : σ → Option (Γ k) → σ) : (Prog.peek k f).Closed := trivial

theorem closed_pop (k : K) (f : σ → Option (Γ k) → σ) : (Prog.pop k f).Closed := trivial

theorem closed_load (f : σ → σ) : (Prog.load (K := K) (Γ := Γ) f).Closed := trivial

end ClosedRules

/-! ## Register lifts -/

section Lifts

variable {K : Type} {R : Type}

/-- A one-symbol-register macro run inside registers `R × Option Sym` (second component). -/
def liftQ (p : SProg K) : Prog K (fun _ => Sym) (R × Option Sym) :=
  p.liftRegs (Lens.snd R (Option Sym))

/-- A component with registers `R` run inside registers `R × Option Sym` (first component). -/
def liftK (κ : Prog K (fun _ => Sym) R) : Prog K (fun _ => Sym) (R × Option Sym) :=
  κ.liftRegs (Lens.fst R (Option Sym))

theorem closed_liftQ {p : SProg K} (h : p.Closed) : (liftQ (R := R) p).Closed :=
  closed_liftRegs _ h

theorem closed_liftK {κ : Prog K (fun _ => Sym) R} (h : κ.Closed) : (liftK κ).Closed :=
  closed_liftRegs _ h

variable [DecidableEq K]

theorem liftQ_eval {p : SProg K} {S S' : K → List Sym} {r r' : Option Sym} {t : ℕ}
    (h : Eval [] p ⟨r, S⟩ ⟨r', S'⟩ t) (v : R × Option Sym) (hv : v.2 = r) :
    Eval [] (liftQ p) ⟨v, S⟩ ⟨(v.1, r'), S'⟩ t :=
  Eval.liftRegs (Lens.snd R (Option Sym)) h v hv

theorem liftK_eval {κ : Prog K (fun _ => Sym) R} {s s' : St K (fun _ => Sym) R} {t : ℕ}
    (h : Eval [] κ s s' t) (q : Option Sym) :
    Eval [] (liftK κ) ⟨(s.var, q), s.stk⟩ ⟨(s'.var, q), s'.stk⟩ t :=
  Eval.liftRegs (Lens.fst R (Option Sym)) h (s.var, q) rfl

end Lifts

/-! ## Register tests -/

/-- Is the register the symbol `x`? -/
def isSym (x : Sym) (r : Option Sym) : Bool := decide (r = some x)

/-- Is the register empty (the popped stack was empty)? -/
def isNoneR (r : Option Sym) : Bool := r.isNone

theorem isSym_some_self (x : Sym) : isSym x (some x) = true := by simp [isSym]

theorem isSym_some_of_ne {x y : Sym} (h : y ≠ x) : isSym x (some y) = false := by
  simp [isSym, h]

/-! ## Macros over `SProg K` -/

section Macros

variable {K : Type}

/-- Move symbols from `src` to `dst` until the popped symbol satisfies `stop`; that symbol (or
`none` at the bottom) stays in the register. -/
def moveUntil (src dst : K) (stop : Option Sym → Bool) : SProg K :=
  .seq (popR src) (.loop (fun r => !stop r) (.seq (pushR dst) (popR src)))

/-- Pop symbols from `src` until the popped symbol satisfies `stop`. -/
def dropUntil (src : K) (stop : Option Sym → Bool) : SProg K :=
  .seq (popR src) (.loop (fun r => !stop r) (popR src))

/-- Move one symbol from `src` to `dst`. -/
def moveSym (src dst : K) : SProg K := .seq (popR src) (pushR dst)

/-- Move a chunk terminated by `x`, terminator included. -/
def moveChunk (src dst : K) (x : Sym) : SProg K := .seq (moveUntil src dst (isSym x)) (pushR dst)

/-- Counted loop: while the counter on `Kc` is nonzero, decrement it (temporary `t`) and run
`body`. -/
def countLoop (Kc t : K) (body : SProg K) : SProg K :=
  .seq (zeroTest Kc) (.loop optIsBit (.seq (dec Kc t) (.seq body (zeroTest Kc))))

theorem closed_popR (k : K) : (popR k).Closed := trivial
theorem closed_pushR (k : K) : (pushR k).Closed := trivial
theorem closed_peekR (k : K) : (peekR k).Closed := trivial
theorem closed_pushC (k : K) (x : Sym) : (pushC k x).Closed := trivial
theorem closed_skip : (skip : SProg K).Closed := trivial

theorem closed_moveUntil (src dst : K) (stop : Option Sym → Bool) :
    (moveUntil src dst stop).Closed :=
  ⟨trivial, ⟨trivial, trivial⟩⟩

theorem closed_dropUntil (src : K) (stop : Option Sym → Bool) : (dropUntil src stop).Closed :=
  ⟨trivial, trivial⟩

theorem closed_moveSym (src dst : K) : (moveSym src dst).Closed := ⟨trivial, trivial⟩

theorem closed_moveChunk (src dst : K) (x : Sym) : (moveChunk src dst x).Closed :=
  ⟨closed_moveUntil _ _ _, trivial⟩

theorem closed_moveBits (src dst : K) : (moveBits src dst).Closed := ⟨trivial, ⟨trivial, trivial⟩⟩

theorem closed_moveBlock (src dst : K) : (moveBlock src dst).Closed :=
  ⟨closed_moveBits _ _, ⟨trivial, trivial⟩⟩

theorem closed_moveBitsDup (src a b : K) : (moveBitsDup src a b).Closed :=
  ⟨trivial, ⟨trivial, ⟨trivial, trivial⟩⟩⟩

theorem closed_copyBlock (src dst tmp : K) : (copyBlock src dst tmp).Closed :=
  ⟨trivial, ⟨closed_moveBlock _ _, closed_moveBitsDup _ _ _⟩⟩

theorem closed_dec (k t : K) : (dec k t).Closed :=
  ⟨trivial, ⟨trivial, ⟨⟨trivial, trivial⟩, ⟨⟨trivial, ⟨trivial, trivial⟩⟩,
    closed_moveBits _ _⟩⟩⟩⟩

theorem closed_countLoop (Kc t : K) {body : SProg K} (hb : body.Closed) :
    (countLoop Kc t body).Closed :=
  ⟨trivial, ⟨closed_dec _ _, ⟨hb, trivial⟩⟩⟩

variable [DecidableEq K]

theorem moveUntil_loop_eval {src dst : K} (hne : src ≠ dst) (stop : Option Sym → Bool) :
    ∀ (d rest : List Sym) (S : K → List Sym), (∀ x ∈ d, stop (some x) = false) →
      stop rest.head? = true → S src = (d ++ rest).tail →
      Eval [] (.loop (fun r => !stop r) (.seq (pushR dst) (popR src))) ⟨(d ++ rest).head?, S⟩
        ⟨rest.head?, Function.update (Function.update S src rest.tail) dst (d.reverse ++ S dst)⟩
        (3 * d.length + 1)
  | [], rest, S, _, hstop, hS => by
    refine (Eval.loop_false (by show (!stop rest.head?) = false; simp [hstop])).of_eq ?_ rfl
    have hS' : S src = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update (Function.update S src rest.tail)
      dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: d, rest, S, hd, hstop, hS => by
    have hx : stop (some x) = false := hd x (List.mem_cons_self ..)
    have hd' : ∀ y ∈ d, stop (some y) = false := fun y hy => hd y (List.mem_cons_of_mem _ hy)
    have hS' : S src = d ++ rest := hS
    have hpush : Eval [] (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      Eval.push _ _ _ _ _
    have hsrc : Function.update S dst (x :: S dst) src = d ++ rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval [] (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨(d ++ rest).head?, Function.update (Function.update S dst (x :: S dst)) src
          (d ++ rest).tail⟩ 1 := by
      refine (Eval.pop [] src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := moveUntil_loop_eval hne stop d rest
      (Function.update (Function.update S dst (x :: S dst)) src (d ++ rest).tail) hd' hstop
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by show (!stop (some x)) = true; simp [hx]) (Eval.seq hpush hpop)
      ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- **moveUntil**, exact. -/
theorem moveUntil_eval {src dst : K} (hne : src ≠ dst) (stop : Option Sym → Bool) (v : Option Sym)
    (d rest : List Sym) (S : K → List Sym) (hd : ∀ x ∈ d, stop (some x) = false)
    (hstop : stop rest.head? = true) (hS : S src = d ++ rest) :
    Eval [] (moveUntil src dst stop) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S src rest.tail) dst (d.reverse ++ S dst)⟩
      (3 * d.length + 2) := by
  have h1 : Eval [] (popR src) ⟨v, S⟩
      ⟨(d ++ rest).head?, Function.update S src (d ++ rest).tail⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := moveUntil_loop_eval hne stop d rest (Function.update S src (d ++ rest).tail) hd hstop
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem dropUntil_loop_eval {src : K} (stop : Option Sym → Bool) :
    ∀ (d rest : List Sym) (S : K → List Sym), (∀ x ∈ d, stop (some x) = false) →
      stop rest.head? = true → S src = (d ++ rest).tail →
      Eval [] (.loop (fun r => !stop r) (popR src)) ⟨(d ++ rest).head?, S⟩
        ⟨rest.head?, Function.update S src rest.tail⟩ (2 * d.length + 1)
  | [], rest, S, _, hstop, hS => by
    refine (Eval.loop_false (by show (!stop rest.head?) = false; simp [hstop])).of_eq ?_ rfl
    have hS' : S src = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update S src rest.tail⟩
    rw [← hS', Function.update_eq_self]
  | x :: d, rest, S, hd, hstop, hS => by
    have hx : stop (some x) = false := hd x (List.mem_cons_self ..)
    have hd' : ∀ y ∈ d, stop (some y) = false := fun y hy => hd y (List.mem_cons_of_mem _ hy)
    have hS' : S src = d ++ rest := hS
    have hpop : Eval [] (popR src) ⟨some x, S⟩
        ⟨(d ++ rest).head?, Function.update S src (d ++ rest).tail⟩ 1 := by
      refine (Eval.pop [] src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hS']
    have ih := dropUntil_loop_eval stop d rest (Function.update S src (d ++ rest).tail) hd' hstop
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by show (!stop (some x)) = true; simp [hx]) hpop ih).of_eq ?_ ?_
    · rw [Function.update_idem]
    · simp only [List.length_cons]
      omega

/-- **dropUntil**, exact. -/
theorem dropUntil_eval {src : K} (stop : Option Sym → Bool) (v : Option Sym) (d rest : List Sym)
    (S : K → List Sym) (hd : ∀ x ∈ d, stop (some x) = false) (hstop : stop rest.head? = true)
    (hS : S src = d ++ rest) :
    Eval [] (dropUntil src stop) ⟨v, S⟩ ⟨rest.head?, Function.update S src rest.tail⟩
      (2 * d.length + 2) := by
  have h1 : Eval [] (popR src) ⟨v, S⟩
      ⟨(d ++ rest).head?, Function.update S src (d ++ rest).tail⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := dropUntil_loop_eval stop d rest (Function.update S src (d ++ rest).tail) hd hstop
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  rw [Function.update_idem]

/-- **moveSym**, exact. -/
theorem moveSym_eval {src dst : K} (hne : src ≠ dst) (v : Option Sym) (x : Sym) (rest : List Sym)
    (S : K → List Sym) (hS : S src = x :: rest) :
    Eval [] (moveSym src dst) ⟨v, S⟩
      ⟨some x, Function.update (Function.update S src rest) dst (x :: S dst)⟩ 2 := by
  have h1 : Eval [] (popR src) ⟨v, S⟩ ⟨some x, Function.update S src rest⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
    rfl
  have h2 : Eval [] (pushR dst) ⟨some x, Function.update S src rest⟩
      ⟨some x, Function.update (Function.update S src rest) dst
        (x :: Function.update S src rest dst)⟩ 1 :=
    Eval.push _ _ _ _ _
  refine (Eval.seq h1 h2).of_eq ?_ rfl
  rw [Function.update_of_ne (Ne.symm hne)]

/-- **moveChunk**, exact: the chunk `d` and its terminator `x` are moved (reversed). -/
theorem moveChunk_eval {src dst : K} (hne : src ≠ dst) (x : Sym) (v : Option Sym)
    (d rest : List Sym) (S : K → List Sym) (hd : x ∉ d) (hS : S src = d ++ x :: rest) :
    Eval [] (moveChunk src dst x) ⟨v, S⟩
      ⟨some x, Function.update (Function.update S src rest) dst
        ((d ++ [x]).reverse ++ S dst)⟩ (3 * d.length + 3) := by
  have h1 := moveUntil_eval hne (isSym x) v d (x :: rest) S
    (fun y hy => isSym_some_of_ne (fun e => hd (e ▸ hy))) (isSym_some_self x) hS
  have h2 : Eval [] (pushR dst) ⟨some x, Function.update (Function.update S src rest) dst
        (d.reverse ++ S dst)⟩
      ⟨some x, Function.update (Function.update (Function.update S src rest) dst
        (d.reverse ++ S dst)) dst (x :: (Function.update (Function.update S src rest) dst
        (d.reverse ++ S dst)) dst)⟩ 1 :=
    Eval.push _ _ _ _ _
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  rw [Function.update_self, Function.update_idem, List.reverse_append]
  rfl

/-! ### Counted loops -/

theorem zerosLead_incBits : ∀ L : List Bool, zerosLead (incBits L) = ones L
  | [] => rfl
  | true :: L => by simp [incBits, zerosLead, ones, zerosLead_incBits L]
  | false :: _ => rfl

theorem zerosLead_encodeNat_succ (n : ℕ) : zerosLead (encodeNat (n + 1)) = ones (encodeNat n) := by
  rw [encodeNat_succ, zerosLead_incBits]

theorem countLoop_loop_eval {α : Type} {Kc t : K} (hKt : Kc ≠ t) (body : SProg K)
    (P : List α → (K → List Sym) → Prop) (rK : List Sym) (hrK : TermOK rK) (cost : α → ℕ)
    (hK : ∀ ys S, P ys S → S Kc = natSyms ys.length ++ rK)
    (hbody : ∀ y ys S v, P (y :: ys) S → ∃ v' S', Eval [] body
      ⟨v, Function.update S Kc (natSyms ys.length ++ rK)⟩ ⟨v', S'⟩ (cost y) ∧ P ys S') :
    ∀ (ys : List α) (S : K → List Sym) (v : Option Sym), P ys S →
      optIsBit v = !decide (ys.length = 0) →
      ∃ v' S', Eval [] (.loop optIsBit (.seq (dec Kc t) (.seq body (zeroTest Kc))))
        ⟨v, S⟩ ⟨v', S'⟩ (incSeqCost 6 10 ys.length + (ys.map cost).sum + 1) ∧ P [] S'
  | [], S, v, hP, hv => by
    refine ⟨v, S, (Eval.loop_false (by simpa using hv)).of_eq rfl ?_, hP⟩
    simp [incSeqCost]
  | y :: ys, S, v, hP, hv => by
    have hSK : S Kc = (encodeNat (ys.length + 1)).map Sym.bit ++ rK := hK _ _ hP
    have e1 := dec_eval hKt [] v ys.length rK S hrK hSK
    obtain ⟨v2, S2, e2, hP2⟩ := hbody y ys S (some .mark) hP
    obtain ⟨r, hr, e3⟩ := zeroTest_eval (k := Kc) [] v2 ys.length rK S2 hrK (hK ys S2 hP2)
    obtain ⟨v4, S4, e4, hP4⟩ := countLoop_loop_eval hKt body P rK hrK cost hK hbody ys S2 r hP2 hr
    refine ⟨v4, S4, (Eval.loop_true (by simpa using hv) (Eval.seq e1 (Eval.seq e2 e3)) e4).of_eq
      rfl ?_, hP4⟩
    rw [zerosLead_encodeNat_succ]
    simp only [List.length_cons, incSeqCost, List.map_cons, List.sum_cons]
    omega

/-- **countLoop**, Hoare form over the list of remaining items. Each iteration decrements the
counter (amortised in `incSeqCost`) and runs `body` on the next item. -/
theorem countLoop_eval {α : Type} {Kc t : K} (hKt : Kc ≠ t) (body : SProg K)
    (P : List α → (K → List Sym) → Prop) (rK : List Sym) (hrK : TermOK rK) (cost : α → ℕ)
    (hK : ∀ ys S, P ys S → S Kc = natSyms ys.length ++ rK)
    (hbody : ∀ y ys S v, P (y :: ys) S → ∃ v' S', Eval [] body
      ⟨v, Function.update S Kc (natSyms ys.length ++ rK)⟩ ⟨v', S'⟩ (cost y) ∧ P ys S')
    (ys : List α) (S : K → List Sym) (v : Option Sym) (hP : P ys S) :
    ∃ v' S', Eval [] (countLoop Kc t body) ⟨v, S⟩ ⟨v', S'⟩
      (incSeqCost 6 10 ys.length + (ys.map cost).sum + 2) ∧ P [] S' := by
  obtain ⟨r, hr, e1⟩ := zeroTest_eval (k := Kc) [] v ys.length rK S hrK (hK ys S hP)
  obtain ⟨v', S', e2, hP'⟩ := countLoop_loop_eval hKt body P rK hrK cost hK hbody ys S r hP hr
  exact ⟨v', S', (Eval.seq e1 e2).of_eq rfl (by omega), hP'⟩

end Macros

/-! ## `sumTo` algebra -/

theorem sumTo_zero (f : ℕ → ℕ) : sumTo 0 f = 0 := rfl

theorem sumTo_succ (n : ℕ) (f : ℕ → ℕ) : sumTo (n + 1) f = sumTo n f + f n := by
  simp [sumTo, List.range_succ]

theorem sumTo_succ' (f : ℕ → ℕ) : ∀ n, sumTo (n + 1) f = f 0 + sumTo n (fun i => f (i + 1))
  | 0 => by simp [sumTo_succ, sumTo_zero]
  | n + 1 => by
    rw [sumTo_succ, sumTo_succ' f n, sumTo_succ]
    omega

theorem sumTo_congr (f g : ℕ → ℕ) : ∀ n, (∀ i < n, f i = g i) → sumTo n f = sumTo n g
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumTo_succ, sumTo_succ, sumTo_congr f g n (fun i hi => h i (by omega)), h n (by omega)]

theorem sumTo_le (f g : ℕ → ℕ) : ∀ n, (∀ i < n, f i ≤ g i) → sumTo n f ≤ sumTo n g
  | 0, _ => le_rfl
  | n + 1, h => by
    rw [sumTo_succ, sumTo_succ]
    have := sumTo_le f g n (fun i hi => h i (by omega))
    have := h n (by omega)
    omega

theorem sumTo_add (f g : ℕ → ℕ) : ∀ n, sumTo n (fun i => f i + g i) = sumTo n f + sumTo n g
  | 0 => rfl
  | n + 1 => by
    rw [sumTo_succ, sumTo_succ, sumTo_succ, sumTo_add f g n]
    omega

theorem sumTo_mul_left (a : ℕ) (f : ℕ → ℕ) : ∀ n, sumTo n (fun i => a * f i) = a * sumTo n f
  | 0 => by simp [sumTo_zero]
  | n + 1 => by
    rw [sumTo_succ, sumTo_succ, sumTo_mul_left a f n, Nat.mul_add]

theorem sumTo_const (a : ℕ) : ∀ n, sumTo n (fun _ => a) = n * a
  | 0 => by simp [sumTo_zero]
  | n + 1 => by
    rw [sumTo_succ, sumTo_const a n, Nat.succ_mul]

theorem sumTo_length_flatMap {β : Type} (f : ℕ → List β) :
    ∀ n, sumTo n (fun i => (f i).length) = ((List.range n).flatMap f).length
  | 0 => rfl
  | n + 1 => by
    rw [sumTo_succ, sumTo_length_flatMap f n, List.range_succ, List.flatMap_append,
      List.length_append]
    simp

/-! ## Indexed loops -/

/-- **Upward indexed loop**: invariant `I i` with `i` = iterations done; the iteration from `i`
costs `B i`. -/
theorem Triple.loop_up {K : Type} {Γ : K → Type} {σ : Type} [DecidableEq K]
    {ρ : List (Prog K Γ σ)} {c : σ → Bool} {p : Prog K Γ σ} {I : ℕ → St K Γ σ → Prop}
    {B : ℕ → ℕ} (M : ℕ)
    (hstep : ∀ i < M, Triple ρ (I i) p (I (i + 1)) (B i))
    (hcont : ∀ i < M, ∀ s, I i s → c s.var = true)
    (hstop : ∀ s, I M s → c s.var = false) :
    Triple ρ (I 0) (.loop c p) (I M) (sumTo M B + M + 1) := by
  have key : ∀ k i, i + k = M →
      Triple ρ (I i) (.loop c p) (I M) (sumTo k (fun j => B (i + j)) + k + 1) := by
    intro k
    induction k with
    | zero =>
      intro i hi s hs
      have hiM : i = M := by omega
      rw [hiM] at hs
      exact ⟨s, 1, Eval.loop_false (hstop s hs), hs, by simp [sumTo_zero]⟩
    | succ k ih =>
      intro i hi s hs
      obtain ⟨s₁, t₁, e₁, h₁, ht₁⟩ := hstep i (by omega) s hs
      obtain ⟨s₂, t₂, e₂, h₂, ht₂⟩ := ih (i + 1) (by omega) s₁ h₁
      refine ⟨s₂, t₁ + t₂ + 1, Eval.loop_true (hcont i (by omega) s hs) e₁ e₂, h₂, ?_⟩
      have hsum : sumTo (k + 1) (fun j => B (i + j)) = B i + sumTo k (fun j => B (i + 1 + j)) := by
        rw [sumTo_succ']
        exact congrArg₂ (· + ·) rfl (sumTo_congr _ _ k (fun j _ => by
          show B (i + (j + 1)) = B (i + 1 + j)
          rw [show i + (j + 1) = i + 1 + j by omega]))
      rw [hsum]
      omega
  have h := key M 0 (by omega)
  rwa [sumTo_congr (fun j => B (0 + j)) B M (fun j _ => by
    show B (0 + j) = B j
    rw [Nat.zero_add])] at h

/-! ## Symbol facts -/

/-- Layout tags. -/
def isTagSym : Sym → Bool
  | .tag _ => true
  | _ => false

/-- Entry symbols are neither layout tags nor the macro guard `mark`. -/
def EntrySym (x : Sym) : Prop := isTagSym x = false ∧ x ≠ Sym.mark

theorem entrySym_intSyms (z : ℤ) : ∀ x ∈ intSyms z, EntrySym x := by
  intro x hx
  simp only [intSyms, natSyms, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨b, -, rfl⟩
  · unfold sgnSym
    split
    · exact ⟨rfl, by decide⟩
    · exact ⟨rfl, by decide⟩
  · exact ⟨rfl, fun h => by cases h⟩

theorem entrySym_entrySyms (z : ℤ × ℤ) : ∀ x ∈ entrySyms z, EntrySym x := by
  intro x hx
  unfold entrySyms at hx
  rw [List.mem_append, List.mem_cons, List.mem_append, List.mem_singleton] at hx
  rcases hx with h | h | h | h
  · exact entrySym_intSyms _ x h
  · subst h
    exact ⟨rfl, by decide⟩
  · exact entrySym_intSyms _ x h
  · subst h
    exact ⟨rfl, by decide⟩

theorem entrySym_blkE (v : List (ℤ × ℤ)) : ∀ x ∈ blkE v, EntrySym x := by
  intro x hx
  simp only [blkE, blk, List.mem_flatten, List.mem_map] at hx
  obtain ⟨l, ⟨z, -, rfl⟩, hxl⟩ := hx
  exact entrySym_entrySyms z x hxl

theorem tag_not_mem_blkE (t : Fin 16) (v : List (ℤ × ℤ)) : Sym.tag t ∉ blkE v :=
  fun h => by have := (entrySym_blkE v _ h).1; simp [isTagSym] at this

theorem mark_not_mem_blkE (v : List (ℤ × ℤ)) : Sym.mark ∉ blkE v :=
  fun h => (entrySym_blkE v _ h).2 rfl

theorem tag_not_mem_entrySyms (t : Fin 16) (z : ℤ × ℤ) : Sym.tag t ∉ entrySyms z :=
  fun h => by have := (entrySym_entrySyms z _ h).1; simp [isTagSym] at this

/-! ## Streams and groups -/

theorem blkE_nil : blkE [] = [] := rfl

theorem blkE_cons (z : ℤ × ℤ) (v : List (ℤ × ℤ)) : blkE (z :: v) = entrySyms z ++ blkE v := rfl

theorem blkE_append (a b : List (ℤ × ℤ)) : blkE (a ++ b) = blkE a ++ blkE b := by
  simp [blkE, blk]

theorem groupSyms_nil : groupSyms [] = [] := rfl

theorem groupSyms_cons (y : Array (ℤ × ℤ)) (grp : List (Array (ℤ × ℤ))) :
    groupSyms (y :: grp) = blkE y.toList ++ groupSyms grp := by
  simp [groupSyms, List.flatMap_cons, blkE_append]

theorem groupSyms_append (a b : List (Array (ℤ × ℤ))) :
    groupSyms (a ++ b) = groupSyms a ++ groupSyms b := by
  simp [groupSyms, List.flatMap_append, blkE_append]

theorem groupSyms_eq_flatMap :
    ∀ grp : List (Array (ℤ × ℤ)), groupSyms grp = grp.flatMap (fun y => blkE y.toList)
  | [] => rfl
  | y :: grp => by rw [groupSyms_cons, groupSyms_eq_flatMap grp, List.flatMap_cons]

theorem nodeSyms_ne_nil (x : Array (ℤ × ℤ)) : nodeSyms x ≠ [] := by simp [nodeSyms]

theorem symLevel_not_mem_nodeSyms (x : Array (ℤ × ℤ)) : symLevel ∉ nodeSyms x := by
  intro h
  rw [nodeSyms, List.mem_append, List.mem_singleton] at h
  rcases h with h | h
  · exact tag_not_mem_blkE 1 _ h
  · exact absurd h (by decide)

theorem symLevel_not_mem_flatMap_nodeSyms (xs : List (Array (ℤ × ℤ))) :
    symLevel ∉ xs.flatMap nodeSyms := by
  intro h
  obtain ⟨x, -, hx⟩ := List.mem_flatMap.1 h
  exact symLevel_not_mem_nodeSyms x hx

/-- A nonempty stream does not start with `$`. -/
theorem head_ne_level (x : Array (ℤ × ℤ)) (l : List Sym) :
    (nodeSyms x ++ l).head? ≠ some symLevel := by
  intro h
  obtain ⟨a, as, has⟩ := List.exists_cons_of_ne_nil (nodeSyms_ne_nil x)
  rw [has, List.cons_append, List.head?_cons, Option.some.injEq] at h
  apply symLevel_not_mem_nodeSyms x
  rw [has, h]
  exact List.mem_cons_self ..

theorem length_flatMap_nodeSyms :
    ∀ xs : List (Array (ℤ × ℤ)), (xs.flatMap nodeSyms).length = (groupSyms xs).length + xs.length
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, groupSyms_cons, List.length_append, List.length_append,
      length_flatMap_nodeSyms xs, nodeSyms, List.length_append, List.length_cons]
    simp only [List.length_nil, List.length_cons]
    omega

theorem length_streamSyms (xs : List (Array (ℤ × ℤ))) :
    (streamSyms xs).length = (groupSyms xs).length + xs.length + 1 := by
  rw [streamSyms, List.length_append, length_flatMap_nodeSyms]
  rfl

/-- The groups of a stream, concatenated, are its prefix of `M` groups. -/
theorem flatMap_groupAt (g : ℕ) (xs : List (Array (ℤ × ℤ))) :
    ∀ M, (List.range M).flatMap (groupAt g xs) = xs.take (M * g)
  | 0 => by simp
  | M + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_groupAt g xs M, List.flatMap_singleton,
      groupAt, Nat.succ_mul, List.take_add]

theorem sumTo_groupSyms (g M : ℕ) (xs : List (Array (ℤ × ℤ))) (hlen : xs.length = g * M) :
    sumTo M (fun i => (groupSyms (groupAt g xs i)).length) = (groupSyms xs).length := by
  have h1 : ∀ n, sumTo n (fun i => (groupSyms (groupAt g xs i)).length) =
      (groupSyms ((List.range n).flatMap (groupAt g xs))).length := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [sumTo_succ, ih, List.range_succ, List.flatMap_append, groupSyms_append,
        List.length_append, List.flatMap_singleton]
  rw [h1, flatMap_groupAt, List.take_of_length_le (by rw [hlen, Nat.mul_comm])]

/-- After `i` groups, the rest of the stream starts with group `i`. -/
theorem drop_groupAt (g i : ℕ) (xs : List (Array (ℤ × ℤ))) :
    xs.drop (i * g) = groupAt g xs i ++ xs.drop ((i + 1) * g) := by
  rw [groupAt, Nat.succ_mul, ← List.drop_drop, List.take_append_drop]

theorem length_groupAt (g M i : ℕ) (xs : List (Array (ℤ × ℤ))) (hlen : xs.length = g * M)
    (hi : i < M) : (groupAt g xs i).length = g := by
  rw [groupAt, List.length_take, List.length_drop, hlen]
  have : (i + 1) * g ≤ g * M := by
    rw [Nat.mul_comm g M]
    exact Nat.mul_le_mul_right g hi
  rw [Nat.succ_mul] at this
  omega

theorem drop_all (g M : ℕ) (xs : List (Array (ℤ × ℤ))) (hlen : xs.length = g * M) :
    xs.drop (M * g) = [] :=
  List.drop_of_length_le (by rw [hlen, Nat.mul_comm])

/-! ## `outer` frame lemmas -/

section Outer

variable {m : ℕ}

theorem outer_update_inr (σ : BLoc m → List Sym) (j : Fin m) (x : List Sym) :
    outer (Function.update σ (.inr j) x) = outer σ := by
  funext k
  simp only [outer]
  split_ifs
  · rfl
  · rw [Function.update_of_ne (by simp)]

theorem outer_update_S (σ : BLoc m → List Sym) (x : List Sym) :
    outer (Function.update σ (.inl .S) x) = outer σ := by
  funext k
  simp only [outer]
  split_ifs with h
  · rfl
  · have hk : k ≠ .S := fun e => h (Or.inl e)
    rw [Function.update_of_ne (fun e => hk (Sum.inl_injective e))]

theorem outer_update_W0 (σ : BLoc m → List Sym) (x : List Sym) :
    outer (Function.update σ (.inl .W0) x) = outer σ := by
  funext k
  simp only [outer]
  split_ifs with h
  · rfl
  · have hk : k ≠ .W0 := fun e => h (Or.inr e)
    rw [Function.update_of_ne (fun e => hk (Sum.inl_injective e))]

theorem outer_update_inl (σ : BLoc m → List Sym) (k : LB) (hS : k ≠ .S) (hW : k ≠ .W0)
    (x : List Sym) : outer (Function.update σ (.inl k) x) = Function.update (outer σ) k x := by
  funext k'
  simp only [outer]
  by_cases hk : k' = k
  · subst hk
    rw [if_neg (by tauto), Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hk, Function.update_of_ne (fun e => hk (Sum.inl_injective e))]
    rfl

end Outer

#assert_std_axioms freeBelow_liftRegs freeBelow_mapStk closed_liftRegs closed_mapStk liftQ_eval
  liftK_eval moveUntil_loop_eval moveUntil_eval dropUntil_loop_eval dropUntil_eval moveSym_eval
  moveChunk_eval zerosLead_incBits zerosLead_encodeNat_succ countLoop_loop_eval countLoop_eval
  sumTo_succ sumTo_succ' sumTo_congr sumTo_le sumTo_add sumTo_mul_left sumTo_const
  sumTo_length_flatMap Triple.loop_up entrySym_blkE tag_not_mem_blkE mark_not_mem_blkE
  groupSyms_cons groupSyms_append groupSyms_eq_flatMap head_ne_level length_flatMap_nodeSyms
  length_streamSyms flatMap_groupAt sumTo_groupSyms drop_groupAt length_groupAt drop_all
  outer_update_inr outer_update_S outer_update_W0 outer_update_inl

end WP.W9a
