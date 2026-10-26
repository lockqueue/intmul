import Contracts.Machine.W4
import IntMulTM.Framework.Lib.Counter

/-!
# WP.W4o.Basic — registers, atoms and small loops for the odd-stride router

Programs of this package run over registers `Reg = Option Sym × Option Sym × Bool` (main symbol
`a`, second symbol `b`, carry `c`). Every lemma is an exact `Eval` statement, generic in the
environment `ρ`, so it can be used inside the recursive router (`fix` / `recur`).

| program | effect | cost |
|---|---|---|
| `mvBits src dst` | `dst += blk.reverse`; the terminator is popped into `a` | `3·|blk| + 2` |
| `dropNum k` | pop a bit block and its (non-bit) terminator | `2·|blk| + 2` |
| `moveAll src dst` | move record symbols until a non-record symbol (which stays) | `4·|l| + 2` |
-/

namespace TMFw.W4o

open TMFw TMFw.Lib TMFw.Contracts

/-- Registers: main symbol `a`, second symbol `b`, carry `c`. -/
abbrev Reg := Option Sym × Option Sym × Bool

/-- Programs of this package. -/
abbrev RProg (K : Type) := Prog K (fun _ => Sym) Reg

/-- States of this package. -/
abbrev RSt (K : Type) := St K (fun _ => Sym) Reg

section Defs

variable {K : Type}

/-- Pop `k` into `a`. -/
def popA (k : K) : RProg K := .pop k (fun r o => (o, r.2))

/-- Peek `k` into `a`. -/
def peekA (k : K) : RProg K := .peek k (fun r o => (o, r.2))

/-- Peek `k` into `b`. -/
def peekB (k : K) : RProg K := .peek k (fun r o => (r.1, o, r.2.2))

/-- Push `a` (default `sep`). -/
def pushA (k : K) : RProg K := .push k (fun r => r.1.getD .sep)

/-- Push `b` (default `sep`). -/
def pushB (k : K) : RProg K := .push k (fun r => r.2.1.getD .sep)

/-- Push a constant. -/
def pushK (k : K) (x : Sym) : RProg K := .push k (fun _ => x)

/-- Pop and discard (registers unchanged). -/
def dropT (k : K) : RProg K := .pop k (fun r _ => r)

/-- Do nothing (1 step). -/
def skipR : RProg K := .load id

/-- Record symbols: payload or record end. -/
def isRecSym (x : Sym) : Bool := isDataSym x || decide (x = Sym.sep)

/-- Is the register a record symbol? -/
def isRecO : Option Sym → Bool
  | some x => isRecSym x
  | none => false

/-- `a` is a bit. -/
def bitA (r : Reg) : Bool := optIsBit r.1

/-- `b` is a bit. -/
def bitB (r : Reg) : Bool := optIsBit r.2.1

/-- `a` is a payload symbol. -/
def dataA (r : Reg) : Bool := isDataR r.1

/-- `a` is a record symbol. -/
def recA (r : Reg) : Bool := isRecO r.1

/-- Move the top bit block of `src` onto `dst` (reversed); the terminator is popped into `a`. -/
def mvBits (src dst : K) : RProg K :=
  .seq (popA src) (.loop bitA (.seq (pushA dst) (popA src)))

/-- Pop a bit block and its terminator. -/
def dropNum (k : K) : RProg K := .seq (popA k) (.loop bitA (popA k))

/-- Move record symbols from `src` to `dst` until a non-record symbol (not consumed). -/
def moveAll (src dst : K) : RProg K :=
  .seq (peekA src) (.loop recA (.seq (pushA dst) (.seq (dropT src) (peekA src))))

end Defs

theorem isRecO_head?_of_blkTerm {rest : List Sym} (h : BlkTerm rest) : isRecO rest.head? = false := by
  cases rest with
  | nil => rfl
  | cons d l =>
    obtain ⟨h1, h2⟩ := h d rfl
    simp [isRecO, isRecSym, h1, h2]

theorem isRecSym_of_data {x : Sym} (h : isDataSym x = true) : isRecSym x = true := by
  simp [isRecSym, h]

theorem isRecSym_sep : isRecSym Sym.sep = true := rfl

theorem isRecSym_mark : isRecSym Sym.mark = false := rfl

section Atoms

variable {K : Type} [DecidableEq K]

theorem eval_popA' (ρ : List (RProg K)) (k : K) (r : Reg) (S : K → List Sym) :
    Eval ρ (popA k) ⟨r, S⟩ ⟨((S k).head?, r.2), Function.update S k (S k).tail⟩ 1 :=
  Eval.pop ρ k _ r S

theorem eval_popA (ρ : List (RProg K)) (k : K) (r : Reg) (S : K → List Sym) (x : Sym)
    (L : List Sym) (hS : S k = x :: L) :
    Eval ρ (popA k) ⟨r, S⟩ ⟨(some x, r.2), Function.update S k L⟩ 1 :=
  (Eval.pop ρ k _ r S).of_eq (by simp only [hS, List.head?_cons, List.tail_cons]) rfl

theorem eval_dropT (ρ : List (RProg K)) (k : K) (r : Reg) (S : K → List Sym) (x : Sym)
    (L : List Sym) (hS : S k = x :: L) :
    Eval ρ (dropT k) ⟨r, S⟩ ⟨r, Function.update S k L⟩ 1 :=
  (Eval.pop ρ k _ r S).of_eq (by simp only [hS, List.tail_cons]) rfl

theorem eval_peekA (ρ : List (RProg K)) (k : K) (r : Reg) (S : K → List Sym) :
    Eval ρ (peekA k) ⟨r, S⟩ ⟨((S k).head?, r.2), S⟩ 1 :=
  Eval.peek ρ k _ r S

theorem eval_peekB (ρ : List (RProg K)) (k : K) (r : Reg) (S : K → List Sym) :
    Eval ρ (peekB k) ⟨r, S⟩ ⟨(r.1, (S k).head?, r.2.2), S⟩ 1 :=
  Eval.peek ρ k _ r S

theorem eval_pushA (ρ : List (RProg K)) (k : K) (x : Sym) (r2 : Option Sym × Bool)
    (S : K → List Sym) :
    Eval ρ (pushA k) ⟨(some x, r2), S⟩ ⟨(some x, r2), Function.update S k (x :: S k)⟩ 1 :=
  Eval.push ρ k _ _ S

theorem eval_pushB (ρ : List (RProg K)) (k : K) (a : Option Sym) (y : Sym) (c : Bool)
    (S : K → List Sym) :
    Eval ρ (pushB k) ⟨(a, some y, c), S⟩ ⟨(a, some y, c), Function.update S k (y :: S k)⟩ 1 :=
  Eval.push ρ k _ _ S

theorem eval_pushK (ρ : List (RProg K)) (k : K) (x : Sym) (r : Reg) (S : K → List Sym) :
    Eval ρ (pushK k x) ⟨r, S⟩ ⟨r, Function.update S k (x :: S k)⟩ 1 :=
  Eval.push ρ k _ r S

theorem eval_skipR (ρ : List (RProg K)) (s : RSt K) : Eval ρ skipR s s 1 := by
  cases s
  exact Eval.load ρ id _ _

end Atoms

section Loops

variable {K : Type} [DecidableEq K]

theorem mvBits_loop {src dst : K} (hne : src ≠ dst) (ρ : List (RProg K))
    (r2 : Option Sym × Bool) :
    ∀ (es : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S src = (es.map Sym.bit ++ rest).tail →
      Eval ρ (.loop bitA (.seq (pushA dst) (popA src))) ⟨((es.map Sym.bit ++ rest).head?, r2), S⟩
        ⟨(rest.head?, r2), Function.update (Function.update S src rest.tail) dst
          (es.reverse.map Sym.bit ++ S dst)⟩ (3 * es.length + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    have hS' : S src = rest.tail := hS
    show (⟨(rest.head?, r2), S⟩ : RSt K) = ⟨(rest.head?, r2), Function.update
      (Function.update S src rest.tail) dst (([] : List Bool).reverse.map Sym.bit ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.map_nil, List.nil_append,
      Function.update_eq_self]
  | e :: es, rest, S, hrest, hS => by
    have hS' : S src = es.map Sym.bit ++ rest := hS
    have hpush := eval_pushA ρ dst (Sym.bit e) r2 S
    have hsrc : Function.update S dst (Sym.bit e :: S dst) src = es.map Sym.bit ++ rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop := eval_popA' ρ src (some (Sym.bit e), r2)
      (Function.update S dst (Sym.bit e :: S dst))
    rw [hsrc] at hpop
    have ih := mvBits_loop hne ρ r2 es rest
      (Function.update (Function.update S dst (Sym.bit e :: S dst)) src
        (es.map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) (Eval.seq hpush hpop) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **mvBits**, exact. -/
theorem mvBits_eval {src dst : K} (hne : src ≠ dst) (ρ : List (RProg K)) (r : Reg)
    (es : List Bool) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = es.map Sym.bit ++ rest) :
    Eval ρ (mvBits src dst) ⟨r, S⟩
      ⟨(rest.head?, r.2), Function.update (Function.update S src rest.tail) dst
        (es.reverse.map Sym.bit ++ S dst)⟩ (3 * es.length + 2) := by
  have h1 := eval_popA' ρ src r S
  rw [hS] at h1
  have h2 := mvBits_loop hne ρ r.2 es rest
    (Function.update S src (es.map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem dropNum_loop {k : K} (ρ : List (RProg K)) (r2 : Option Sym × Bool) :
    ∀ (es : List Bool) (x : Sym) (R : List Sym) (S : K → List Sym), x.isBit = false →
      S k = (es.map Sym.bit ++ x :: R).tail →
      Eval ρ (.loop bitA (popA k)) ⟨((es.map Sym.bit ++ x :: R).head?, r2), S⟩
        ⟨(some x, r2), Function.update S k R⟩ (2 * es.length + 1)
  | [], x, R, S, hx, hS => by
    have hS' : S k = R := hS
    refine (Eval.loop_false (optIsBit_head?_of_termOK (TermOK.cons hx R))).of_eq ?_ rfl
    show (⟨(some x, r2), S⟩ : RSt K) = ⟨(some x, r2), Function.update S k R⟩
    rw [← hS', Function.update_eq_self]
  | e :: es, x, R, S, hx, hS => by
    have hS' : S k = es.map Sym.bit ++ x :: R := hS
    have hpop := eval_popA' ρ k (some (Sym.bit e), r2) S
    rw [hS'] at hpop
    have ih := dropNum_loop ρ r2 es x R (Function.update S k (es.map Sym.bit ++ x :: R).tail) hx
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) hpop ih).of_eq ?_ (by simp only [List.length_cons]; omega)
    rw [Function.update_idem]

/-- **dropNum**, exact. -/
theorem dropNum_eval {k : K} (ρ : List (RProg K)) (r : Reg) (es : List Bool) (x : Sym)
    (R : List Sym) (S : K → List Sym) (hx : x.isBit = false)
    (hS : S k = es.map Sym.bit ++ x :: R) :
    Eval ρ (dropNum k) ⟨r, S⟩ ⟨(some x, r.2), Function.update S k R⟩ (2 * es.length + 2) := by
  have h1 := eval_popA' ρ k r S
  rw [hS] at h1
  have h2 := dropNum_loop ρ r.2 es x R (Function.update S k (es.map Sym.bit ++ x :: R).tail) hx
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  rw [Function.update_idem]

theorem moveAll_loop {src dst : K} (hne : src ≠ dst) (ρ : List (RProg K))
    (r2 : Option Sym × Bool) (R : List Sym) (hR : isRecO R.head? = false) :
    ∀ (l : List Sym) (S : K → List Sym), (∀ x ∈ l, isRecSym x = true) → S src = l ++ R →
      Eval ρ (.loop recA (.seq (pushA dst) (.seq (dropT src) (peekA src))))
        ⟨((l ++ R).head?, r2), S⟩
        ⟨(R.head?, r2), Function.update (Function.update S src R) dst (l.reverse ++ S dst)⟩
        (4 * l.length + 1)
  | [], S, _, hS => by
    refine (Eval.loop_false hR).of_eq ?_ rfl
    have hS' : S src = R := hS
    show (⟨(R.head?, r2), S⟩ : RSt K) = ⟨(R.head?, r2), Function.update
      (Function.update S src R) dst (([] : List Sym).reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append,
      Function.update_eq_self]
  | x :: l, S, hl, hS => by
    have hx : isRecSym x = true := hl x (List.mem_cons_self ..)
    have hpush := eval_pushA ρ dst x r2 S
    have hsrc : Function.update S dst (x :: S dst) src = x :: (l ++ R) := by
      rw [Function.update_of_ne hne]
      exact hS
    have hdrop := eval_dropT ρ src (some x, r2) (Function.update S dst (x :: S dst)) x (l ++ R)
      hsrc
    have hpeek := eval_peekA ρ src (some x, r2)
      (Function.update (Function.update S dst (x :: S dst)) src (l ++ R))
    rw [Function.update_self] at hpeek
    have ih := moveAll_loop hne ρ r2 R hR l
      (Function.update (Function.update S dst (x :: S dst)) src (l ++ R))
      (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (Function.update_self _ _ _)
    refine (Eval.loop_true hx (Eval.seq hpush (Eval.seq hdrop hpeek)) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- **moveAll**, exact. -/
theorem moveAll_eval {src dst : K} (hne : src ≠ dst) (ρ : List (RProg K)) (r : Reg)
    (l R : List Sym) (S : K → List Sym) (hl : ∀ x ∈ l, isRecSym x = true)
    (hR : isRecO R.head? = false) (hS : S src = l ++ R) :
    Eval ρ (moveAll src dst) ⟨r, S⟩
      ⟨(R.head?, r.2), Function.update (Function.update S src R) dst (l.reverse ++ S dst)⟩
      (4 * l.length + 2) := by
  have h1 := eval_peekA ρ src r S
  rw [hS] at h1
  exact (Eval.seq h1 (moveAll_loop hne ρ r.2 R hR l S hl hS)).of_eq rfl (by omega)

end Loops

#assert_std_axioms isRecO_head?_of_blkTerm isRecSym_of_data eval_popA eval_dropT eval_pushA
  eval_pushB eval_pushK eval_skipR mvBits_eval dropNum_eval moveAll_eval

end TMFw.W4o
