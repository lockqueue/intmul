import IntMulTM.SpecFacts
import SubNLogN.Machine.Pipe.Names

/-!
# Input-guard kernel, part 1: generic stack routines and Horner conversion

Helpers (namespace `SubNLogN.Machine.Pipe.GuardAux`) for the input-guard kernel
`SubNLogN.Machine.Pipe.guard_holds : GuardStmt` (proved in `SubNLogN/Machine/Pipe/Guard.lean`).

* Generic routines on any stack index type `K` (programs `SProg K` with register `Option Sym`):
  `moveAll` (move a whole stack, reversing it), `clearM` (empty a stack), `moveDbl` / `moveDup`
  (move a stack of marks while doubling / duplicating it), `copyAll` (copy a stack of marks via a
  temporary stack), each with an exact `Eval` lemma (final state and exact cost).
* Horner conversion of an MSB-first binary field into a unary count (`horner`, `horner_eval`),
  with the cost bound `hcost_le`.
-/

namespace SubNLogN.Machine.Pipe.GuardAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

/-- The register holds a symbol. -/
def isSomeB (v : Option Sym) : Bool := v.isSome

/-- The register holds the bit `1`. -/
def isTrueBit (v : Option Sym) : Bool := decide (v = some (Sym.bit true))

variable {K : Type}

/-- Loop body of `moveAll`: move one symbol, peek the next one. -/
def moveAllBody (src dst : K) : SProg K := .seq (popR src) (.seq (pushR dst) (peekR src))

/-- Move every symbol of `src` onto `dst` (reversing the order). -/
def moveAll (src dst : K) : SProg K := .seq (peekR src) (.loop isSomeB (moveAllBody src dst))

/-- Loop body of `clearM`. -/
def clearBody (k : K) : SProg K := .seq (popR k) (peekR k)

/-- Pop `k` until it is empty. -/
def clearM (k : K) : SProg K := .seq (peekR k) (.loop isSomeB (clearBody k))

/-- Loop body of `moveDbl`: pop one symbol, push two marks. -/
def moveDblBody (src dst : K) : SProg K :=
  .seq (popR src) (.seq (pushC dst .mark) (.seq (pushC dst .mark) (peekR src)))

/-- Pop every symbol of `src`, pushing two marks on `dst` for each. -/
def moveDbl (src dst : K) : SProg K := .seq (peekR src) (.loop isSomeB (moveDblBody src dst))

/-- Loop body of `moveDup`. -/
def moveDupBody (src a b : K) : SProg K :=
  .seq (popR src) (.seq (pushR a) (.seq (pushR b) (peekR src)))

/-- Move every symbol of `src` onto both `a` and `b`. -/
def moveDup (src a b : K) : SProg K := .seq (peekR src) (.loop isSomeB (moveDupBody src a b))

/-- Copy `src` onto `dst` through `tmp` (`src` restored). -/
def copyAll (src dst tmp : K) : SProg K := .seq (moveDup src dst tmp) (moveAll tmp src)

variable [DecidableEq K]

theorem moveAll_loop_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) :
    ∀ (l : List Sym) (S : K → List Sym), S src = l →
      Eval ρ (.loop isSomeB (moveAllBody src dst)) ⟨l.head?, S⟩
        ⟨none, Function.update (Function.update S src []) dst (l.reverse ++ S dst)⟩
        (4 * l.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    congr 1
    funext k
    by_cases h1 : k = dst
    · subst h1; simp [Function.update_of_ne hne.symm]
    · by_cases h2 : k = src
      · subst h2; simp [Function.update_of_ne h1, hS]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  | a :: l, S, hS => by
    set S1 := Function.update S src l with hS1
    set S2 := Function.update S1 dst (a :: S1 dst) with hS2
    have e1 : Eval ρ (popR src) ⟨(a :: l).head?, S⟩ ⟨some a, S1⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS]; rfl
    have e2 : Eval ρ (pushR dst) ⟨some a, S1⟩ ⟨some a, S2⟩ 1 :=
      Eval.push ρ dst (fun r => r.getD .sep) (some a) S1
    have hS2s : S2 src = l := by
      rw [hS2, Function.update_of_ne hne, hS1, Function.update_self]
    have e3 : Eval ρ (peekR src) ⟨some a, S2⟩ ⟨l.head?, S2⟩ 1 := by
      refine (Eval.peek ρ src (fun _ o => o) _ S2).of_eq ?_ rfl
      rw [hS2s]
    have ih := moveAll_loop_eval hne ρ l S2 hS2s
    refine (Eval.loop_true (by rfl) (Eval.seq e1 (Eval.seq e2 e3)) ih).of_eq ?_
      (by simp only [List.length_cons]; ring)
    congr 1
    funext k
    by_cases h1 : k = dst
    · subst h1
      simp [hS2, hS1, Function.update_of_ne hne.symm]
    · by_cases h2 : k = src
      · subst h2; simp [Function.update_of_ne h1]
      · simp [hS2, hS1, Function.update_of_ne h1, Function.update_of_ne h2]

theorem moveAll_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (l : List Sym) (S : K → List Sym) (hS : S src = l) :
    Eval ρ (moveAll src dst) ⟨v, S⟩
      ⟨none, Function.update (Function.update S src []) dst (l.reverse ++ S dst)⟩
      (4 * l.length + 2) := by
  have e0 : Eval ρ (peekR src) ⟨v, S⟩ ⟨l.head?, S⟩ 1 := by
    refine (Eval.peek ρ src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  exact (Eval.seq e0 (moveAll_loop_eval hne ρ l S hS)).of_eq rfl (by ring)

theorem clearM_loop_eval {k : K} (ρ : List (SProg K)) :
    ∀ (l : List Sym) (S : K → List Sym), S k = l →
      Eval ρ (.loop isSomeB (clearBody k)) ⟨l.head?, S⟩ ⟨none, Function.update S k []⟩
        (3 * l.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    congr 1
    rw [← hS, Function.update_eq_self]
  | a :: l, S, hS => by
    set S1 := Function.update S k l with hS1
    have e1 : Eval ρ (popR k) ⟨(a :: l).head?, S⟩ ⟨some a, S1⟩ 1 := by
      refine (Eval.pop ρ k (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS]; rfl
    have hS1k : S1 k = l := by rw [hS1, Function.update_self]
    have e2 : Eval ρ (peekR k) ⟨some a, S1⟩ ⟨l.head?, S1⟩ 1 := by
      refine (Eval.peek ρ k (fun _ o => o) _ S1).of_eq ?_ rfl
      rw [hS1k]
    have ih := clearM_loop_eval ρ l S1 hS1k
    refine (Eval.loop_true (by rfl) (Eval.seq e1 e2) ih).of_eq ?_
      (by simp only [List.length_cons]; ring)
    rw [hS1, Function.update_idem]

theorem clearM_eval {k : K} (ρ : List (SProg K)) (v : Option Sym) (l : List Sym)
    (S : K → List Sym) (hS : S k = l) :
    Eval ρ (clearM k) ⟨v, S⟩ ⟨none, Function.update S k []⟩ (3 * l.length + 2) := by
  have e0 : Eval ρ (peekR k) ⟨v, S⟩ ⟨l.head?, S⟩ 1 := by
    refine (Eval.peek ρ k (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  exact (Eval.seq e0 (clearM_loop_eval ρ l S hS)).of_eq rfl (by ring)

theorem moveDbl_loop_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) :
    ∀ (l : List Sym) (S : K → List Sym), S src = l →
      Eval ρ (.loop isSomeB (moveDblBody src dst)) ⟨l.head?, S⟩
        ⟨none, Function.update (Function.update S src []) dst
          (List.replicate (2 * l.length) Sym.mark ++ S dst)⟩ (5 * l.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    congr 1
    funext k
    by_cases h1 : k = dst
    · subst h1; simp [Function.update_of_ne hne.symm]
    · by_cases h2 : k = src
      · subst h2; simp [Function.update_of_ne h1, hS]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  | a :: l, S, hS => by
    set S1 := Function.update S src l with hS1
    set S2 := Function.update S1 dst (Sym.mark :: S1 dst) with hS2
    set S3 := Function.update S2 dst (Sym.mark :: S2 dst) with hS3
    have e1 : Eval ρ (popR src) ⟨(a :: l).head?, S⟩ ⟨some a, S1⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS]; rfl
    have e2 : Eval ρ (pushC dst .mark) ⟨some a, S1⟩ ⟨some a, S2⟩ 1 :=
      Eval.push ρ dst (fun _ => .mark) (some a) S1
    have e3 : Eval ρ (pushC dst .mark) ⟨some a, S2⟩ ⟨some a, S3⟩ 1 :=
      Eval.push ρ dst (fun _ => .mark) (some a) S2
    have hS3s : S3 src = l := by
      rw [hS3, Function.update_of_ne hne, hS2, Function.update_of_ne hne, hS1,
        Function.update_self]
    have e4 : Eval ρ (peekR src) ⟨some a, S3⟩ ⟨l.head?, S3⟩ 1 := by
      refine (Eval.peek ρ src (fun _ o => o) _ S3).of_eq ?_ rfl
      rw [hS3s]
    have ih := moveDbl_loop_eval hne ρ l S3 hS3s
    refine (Eval.loop_true (by rfl) (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) ih).of_eq ?_
      (by simp only [List.length_cons]; ring)
    congr 1
    funext k
    by_cases h1 : k = dst
    · subst h1
      simp only [Function.update_self, hS3, hS2, hS1, Function.update_of_ne hne.symm,
        List.length_cons]
      rw [show 2 * (l.length + 1) = 2 * l.length + 1 + 1 by ring, List.replicate_succ',
        List.replicate_succ']
      simp
    · by_cases h2 : k = src
      · subst h2; simp [Function.update_of_ne h1]
      · simp [hS3, hS2, hS1, Function.update_of_ne h1, Function.update_of_ne h2]

theorem moveDbl_eval {src dst : K} (hne : src ≠ dst) (ρ : List (SProg K)) (v : Option Sym)
    (l : List Sym) (S : K → List Sym) (hS : S src = l) :
    Eval ρ (moveDbl src dst) ⟨v, S⟩
      ⟨none, Function.update (Function.update S src []) dst
        (List.replicate (2 * l.length) Sym.mark ++ S dst)⟩ (5 * l.length + 2) := by
  have e0 : Eval ρ (peekR src) ⟨v, S⟩ ⟨l.head?, S⟩ 1 := by
    refine (Eval.peek ρ src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  exact (Eval.seq e0 (moveDbl_loop_eval hne ρ l S hS)).of_eq rfl (by ring)

end SubNLogN.Machine.Pipe.GuardAux

namespace SubNLogN.Machine.Pipe.GuardAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine

variable {K : Type} [DecidableEq K]

theorem moveDup_loop_eval {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (ρ : List (SProg K)) :
    ∀ (l : List Sym) (S : K → List Sym), S src = l →
      Eval ρ (.loop isSomeB (moveDupBody src a b)) ⟨l.head?, S⟩
        ⟨none, Function.update (Function.update (Function.update S src []) a (l.reverse ++ S a))
          b (l.reverse ++ S b)⟩ (5 * l.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    congr 1
    funext k
    by_cases h1 : k = b
    · subst h1; simp
    · by_cases h2 : k = a
      · subst h2; simp [Function.update_of_ne h1]
      · by_cases h3 : k = src
        · subst h3; simp [Function.update_of_ne h1, Function.update_of_ne h2, hS]
        · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  | x :: l, S, hS => by
    set S1 := Function.update S src l with hS1
    set S2 := Function.update S1 a (x :: S1 a) with hS2
    set S3 := Function.update S2 b (x :: S2 b) with hS3
    have e1 : Eval ρ (popR src) ⟨(x :: l).head?, S⟩ ⟨some x, S1⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS]; rfl
    have e2 : Eval ρ (pushR a) ⟨some x, S1⟩ ⟨some x, S2⟩ 1 :=
      Eval.push ρ a (fun r => r.getD .sep) (some x) S1
    have e3 : Eval ρ (pushR b) ⟨some x, S2⟩ ⟨some x, S3⟩ 1 :=
      Eval.push ρ b (fun r => r.getD .sep) (some x) S2
    have hS3s : S3 src = l := by
      rw [hS3, Function.update_of_ne hsb, hS2, Function.update_of_ne hsa, hS1,
        Function.update_self]
    have e4 : Eval ρ (peekR src) ⟨some x, S3⟩ ⟨l.head?, S3⟩ 1 := by
      refine (Eval.peek ρ src (fun _ o => o) _ S3).of_eq ?_ rfl
      rw [hS3s]
    have ih := moveDup_loop_eval hsa hsb hab ρ l S3 hS3s
    refine (Eval.loop_true (by rfl) (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) ih).of_eq ?_
      (by simp only [List.length_cons]; ring)
    congr 1
    funext k
    by_cases h1 : k = b
    · subst h1
      simp [hS3, hS2, hS1, Function.update_of_ne hab.symm, Function.update_of_ne hsb.symm]
    · by_cases h2 : k = a
      · subst h2
        simp [Function.update_of_ne h1, hS3, hS2, hS1, Function.update_of_ne hsa.symm]
      · by_cases h3 : k = src
        · subst h3; simp [Function.update_of_ne h1, Function.update_of_ne h2]
        · simp [hS3, hS2, hS1, Function.update_of_ne h1, Function.update_of_ne h2,
            Function.update_of_ne h3]

theorem moveDup_eval {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (ρ : List (SProg K)) (v : Option Sym) (l : List Sym) (S : K → List Sym) (hS : S src = l) :
    Eval ρ (moveDup src a b) ⟨v, S⟩
      ⟨none, Function.update (Function.update (Function.update S src []) a (l.reverse ++ S a))
        b (l.reverse ++ S b)⟩ (5 * l.length + 2) := by
  have e0 : Eval ρ (peekR src) ⟨v, S⟩ ⟨l.head?, S⟩ 1 := by
    refine (Eval.peek ρ src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  exact (Eval.seq e0 (moveDup_loop_eval hsa hsb hab ρ l S hS)).of_eq rfl (by ring)

/-- **copyAll**: `dst := l.reverse ++ dst`, `src` restored, `tmp` (empty) stays empty. -/
theorem copyAll_eval {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (ρ : List (SProg K)) (v : Option Sym) (l : List Sym) (S : K → List Sym) (hS : S src = l)
    (hT : S tmp = []) :
    Eval ρ (copyAll src dst tmp) ⟨v, S⟩
      ⟨none, Function.update S dst (l.reverse ++ S dst)⟩ (9 * l.length + 4) := by
  have e1 := moveDup_eval hsd hst hdt ρ v l S hS
  set S1 := Function.update (Function.update (Function.update S src []) dst (l.reverse ++ S dst))
    tmp (l.reverse ++ S tmp) with hS1
  have hS1t : S1 tmp = l.reverse := by rw [hS1, Function.update_self, hT, List.append_nil]
  have e2 := moveAll_eval hst.symm ρ none l.reverse S1 hS1t
  refine (Eval.seq e1 e2).of_eq ?_ (by simp only [List.length_reverse]; ring)
  congr 1
  funext k
  by_cases h1 : k = src
  · subst h1
    simp [hS1, Function.update_of_ne hsd, Function.update_of_ne hst, hS]
  · by_cases h2 : k = tmp
    · subst h2
      simp [Function.update_of_ne (Ne.symm hst), Function.update_of_ne hdt.symm, hT]
    · by_cases h3 : k = dst
      · subst h3; simp [hS1, Function.update_of_ne h1, Function.update_of_ne h2]
      · simp [hS1, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]

/-! ## Horner conversion (binary, MSB first, to unary) -/

/-- Horner value: `hval a [m₁, …, m_k] = (…(2a + m₁)…)·2 + m_k`. -/
def hval : ℕ → List Bool → ℕ
  | a, [] => a
  | a, m :: ms => hval (2 * a + m.toNat) ms

/-- Step count of the Horner loop. -/
def hcost : ℕ → List Bool → ℕ
  | _, [] => 1
  | a, m :: ms => 13 * a + 4 * m.toNat + 9 + hcost (2 * a + m.toNat) ms

theorem hval_append (a : ℕ) (l : List Bool) (m : Bool) :
    hval a (l ++ [m]) = 2 * hval a l + m.toNat := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => exact ih _

theorem hval_reverse (a : ℕ) (es : List Bool) :
    hval a es.reverse = a * 2 ^ es.length + bitsVal es := by
  induction es with
  | nil => simp [hval]
  | cons e es ih =>
    rw [List.reverse_cons, hval_append, ih, bitsVal_cons, List.length_cons, pow_succ]
    ring

theorem hval_encodeNat (n : ℕ) : hval 0 (encodeNat n).reverse = n := by
  rw [hval_reverse, bitsVal_encodeNat]; ring

theorem hcost_le : ∀ (a : ℕ) (ms : List Bool),
    hcost a ms + 13 * a ≤ 13 * hval a ms + 13 * ms.length + 1
  | a, [] => by simp only [hcost, hval, List.length_nil]; omega
  | a, m :: ms => by
    have ih := hcost_le (2 * a + m.toNat) ms
    have hm : m.toNat ≤ 1 := Bool.toNat_le m
    simp only [hcost, hval, List.length_cons]
    omega

/-- Loop body of `horner`: push the bit back on `src`, `acc := 2·acc + bit` (through `acc2`),
pop the next bit of `h`. -/
def hornerBody (src acc acc2 h : K) : SProg K :=
  .seq (pushR src) (.seq (.ite isTrueBit (pushC acc2 .mark) skip)
    (.seq (moveDbl acc acc2) (.seq (moveAll acc2 acc) (popR h))))

/-- Horner conversion of the bits on `h` (MSB on top) into `acc`, pushing the bits back on `src`. -/
def horner (src acc acc2 h : K) : SProg K :=
  .seq (popR h) (.loop optIsBit (hornerBody src acc acc2 h))


theorem isTrueBit_ite_eval {acc2 : K} (ρ : List (SProg K)) (m : Bool) (S : K → List Sym)
    (h0 : S acc2 = []) :
    Eval ρ (.ite isTrueBit (pushC acc2 .mark) skip) ⟨some (Sym.bit m), S⟩
      ⟨some (Sym.bit m), Function.update S acc2 (List.replicate m.toNat Sym.mark)⟩ 2 := by
  cases m with
  | true =>
    refine (Eval.ite_true (by rfl) (Eval.push ρ acc2 (fun _ => .mark) _ S)).of_eq ?_ rfl
    rw [h0]; rfl
  | false =>
    refine (Eval.ite_false (by rfl) (skip_eval ρ _)).of_eq ?_ rfl
    show (⟨some (Sym.bit false), S⟩ : SSt K) = ⟨some (Sym.bit false), Function.update S acc2 []⟩
    rw [← h0, Function.update_eq_self]

theorem horner_loop_eval {src acc acc2 h : K} (h1 : src ≠ acc) (h2 : src ≠ acc2) (h3 : src ≠ h)
    (h4 : acc ≠ acc2) (h5 : acc ≠ h) (h6 : acc2 ≠ h) (ρ : List (SProg K)) :
    ∀ (ms : List Bool) (a : ℕ) (S : K → List Sym), S h = (ms.map Sym.bit).tail →
      S acc = List.replicate a Sym.mark → S acc2 = [] →
      Eval ρ (.loop optIsBit (hornerBody src acc acc2 h)) ⟨(ms.map Sym.bit).head?, S⟩
        ⟨none, Function.update (Function.update (Function.update S h []) src
          ((ms.reverse.map Sym.bit) ++ S src)) acc (List.replicate (hval a ms) Sym.mark)⟩
        (hcost a ms)
  | [], a, S, hSh, hSa, _ => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    congr 1
    funext k
    by_cases hk1 : k = acc
    · subst hk1; simp [hval, hSa]
    · by_cases hk2 : k = src
      · subst hk2; simp [Function.update_of_ne hk1]
      · by_cases hk3 : k = h
        · subst hk3
          simp only [Function.update_of_ne hk1, Function.update_of_ne hk2, Function.update_self]
          simpa using hSh
        · simp [Function.update_of_ne hk1, Function.update_of_ne hk2, Function.update_of_ne hk3]
  | m :: ms, a, S, hSh, hSa, hS2 => by
    set S1 := Function.update S src (Sym.bit m :: S src) with hS1
    have e1 : Eval ρ (pushR src) ⟨some (Sym.bit m), S⟩ ⟨some (Sym.bit m), S1⟩ 1 :=
      Eval.push ρ src (fun r => r.getD .sep) (some (Sym.bit m)) S
    have hS1c2 : S1 acc2 = [] := by rw [hS1, Function.update_of_ne h2.symm, hS2]
    have e2 := isTrueBit_ite_eval ρ m S1 hS1c2
    set S2 := Function.update S1 acc2 (List.replicate m.toNat Sym.mark) with hS2'
    have hS2a : S2 acc = List.replicate a Sym.mark := by
      rw [hS2', Function.update_of_ne h4, hS1, Function.update_of_ne h1.symm, hSa]
    have e3 := moveDbl_eval h4 ρ (some (Sym.bit m)) _ S2 hS2a
    rw [List.length_replicate] at e3
    set S3 := Function.update (Function.update S2 acc []) acc2
      (List.replicate (2 * a) Sym.mark ++ S2 acc2) with hS3
    have hS3c2 : S3 acc2 = List.replicate (2 * a + m.toNat) Sym.mark := by
      rw [hS3, Function.update_self, hS2', Function.update_self, List.replicate_add]
    have e4 := moveAll_eval h4.symm ρ none _ S3 hS3c2
    rw [List.length_replicate, List.reverse_replicate] at e4
    set S4 := Function.update (Function.update S3 acc2 []) acc
      (List.replicate (2 * a + m.toNat) Sym.mark ++ S3 acc) with hS4
    have hS4h : S4 h = ms.map Sym.bit := by
      rw [hS4, Function.update_of_ne h5.symm, Function.update_of_ne h6.symm, hS3,
        Function.update_of_ne h6.symm, Function.update_of_ne h5.symm, hS2',
        Function.update_of_ne h6.symm, hS1, Function.update_of_ne h3.symm]
      simpa using hSh
    have e5 : Eval ρ (popR h) ⟨none, S4⟩
        ⟨(ms.map Sym.bit).head?, Function.update S4 h (ms.map Sym.bit).tail⟩ 1 := by
      refine (Eval.pop ρ h (fun _ o => o) none S4).of_eq ?_ rfl
      rw [hS4h]
    set S5 := Function.update S4 h (ms.map Sym.bit).tail with hS5
    have hS3a : S3 acc = [] := by
      rw [hS3, Function.update_of_ne h4, Function.update_self]
    have hS5h : S5 h = (ms.map Sym.bit).tail := by rw [hS5, Function.update_self]
    have hS5a : S5 acc = List.replicate (2 * a + m.toNat) Sym.mark := by
      rw [hS5, Function.update_of_ne h5, hS4, Function.update_self, hS3a, List.append_nil]
    have hS5c2 : S5 acc2 = [] := by
      rw [hS5, Function.update_of_ne h6, hS4, Function.update_of_ne h4.symm, Function.update_self]
    have ih := horner_loop_eval h1 h2 h3 h4 h5 h6 ρ ms (2 * a + m.toNat) S5 hS5h hS5a hS5c2
    have hbody := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))
    refine (Eval.loop_true (by rfl) hbody ih).of_eq ?_ (by simp only [hcost]; ring)
    congr 1
    funext k
    by_cases hk1 : k = acc
    · subst hk1; simp [hval]
    · by_cases hk2 : k = src
      · subst hk2
        simp [Function.update_of_ne hk1, hS5, hS4, hS3, hS2', hS1, Function.update_of_ne h1,
          Function.update_of_ne h2, Function.update_of_ne h3]
      · by_cases hk3 : k = h
        · subst hk3; simp [Function.update_of_ne hk1, Function.update_of_ne hk2]
        · by_cases hk4 : k = acc2
          · subst hk4
            simp [Function.update_of_ne hk1, Function.update_of_ne hk2, Function.update_of_ne hk3,
              hS5, hS4, Function.update_of_ne h4.symm, hS2]
          · simp [Function.update_of_ne hk1, Function.update_of_ne hk2, Function.update_of_ne hk3,
              hS5, hS4, hS3, hS2', hS1, Function.update_of_ne hk4]

theorem horner_eval {src acc acc2 h : K} (h1 : src ≠ acc) (h2 : src ≠ acc2) (h3 : src ≠ h)
    (h4 : acc ≠ acc2) (h5 : acc ≠ h) (h6 : acc2 ≠ h) (ρ : List (SProg K)) (v : Option Sym)
    (ms : List Bool) (a : ℕ) (S : K → List Sym) (hSh : S h = ms.map Sym.bit)
    (hSa : S acc = List.replicate a Sym.mark) (hS2 : S acc2 = []) :
    Eval ρ (horner src acc acc2 h) ⟨v, S⟩
      ⟨none, Function.update (Function.update (Function.update S h []) src
        ((ms.reverse.map Sym.bit) ++ S src)) acc (List.replicate (hval a ms) Sym.mark)⟩
      (hcost a ms + 1) := by
  have e0 : Eval ρ (popR h) ⟨v, S⟩
      ⟨(ms.map Sym.bit).head?, Function.update S h (ms.map Sym.bit).tail⟩ 1 := by
    refine (Eval.pop ρ h (fun _ o => o) v S).of_eq ?_ rfl
    rw [hSh]
  have ih := horner_loop_eval h1 h2 h3 h4 h5 h6 ρ ms a (Function.update S h (ms.map Sym.bit).tail)
    (Function.update_self _ _ _) (by rw [Function.update_of_ne h5]; exact hSa)
    (by rw [Function.update_of_ne h6]; exact hS2)
  refine (Eval.seq e0 ih).of_eq ?_ (by ring)
  congr 1
  funext k
  by_cases hk1 : k = acc
  · subst hk1; simp
  · by_cases hk2 : k = src
    · subst hk2; simp [Function.update_of_ne hk1, Function.update_of_ne h3]
    · by_cases hk3 : k = h
      · subst hk3; simp [Function.update_of_ne hk1, Function.update_of_ne hk2]
      · simp [Function.update_of_ne hk1, Function.update_of_ne hk2, Function.update_of_ne hk3]

end SubNLogN.Machine.Pipe.GuardAux
