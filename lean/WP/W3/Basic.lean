import Contracts.Machine.W3

/-!
# WP.W3.Basic — shared helpers for the unsigned W3 implementations

* `noRec` / `closed_of_noRec`: closedness of `recur`-free programs, by `decide`.
* `bitsVal_eq_head_tail`, `optBit_head?_map`: bit-list facts for the ripple loops.
* Macros over one `Option Sym` register, with exact `Eval` lemmas:
  `dropBits` (pop a bit block and its terminator), `dropNum` (pop a number, keep the terminator),
  `skipZeros` / `emitNorm` (MSB-first bits on a temporary → canonical LSB-first number on another
  stack).
-/

namespace WP.W3

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Closedness -/

section NoRec

variable {K : Type} {Γ : K → Type} {σ : Type}

/-- `p` contains no `recur`. -/
def noRec : Prog K Γ σ → Bool
  | .seq p q => noRec p && noRec q
  | .ite _ p q => noRec p && noRec q
  | .loop _ p => noRec p
  | .fix b => noRec b
  | .recur _ => false
  | _ => true

theorem freeBelow_of_noRec : ∀ (p : Prog K Γ σ) (d : ℕ), noRec p = true → p.FreeBelow d
  | .push _ _, _, _ => by simp [Prog.FreeBelow]
  | .peek _ _, _, _ => by simp [Prog.FreeBelow]
  | .pop _ _, _, _ => by simp [Prog.FreeBelow]
  | .load _, _, _ => by simp [Prog.FreeBelow]
  | .seq p q, d, h => by
    simp only [noRec, Bool.and_eq_true] at h
    exact ⟨freeBelow_of_noRec p d h.1, freeBelow_of_noRec q d h.2⟩
  | .ite _ p q, d, h => by
    simp only [noRec, Bool.and_eq_true] at h
    exact ⟨freeBelow_of_noRec p d h.1, freeBelow_of_noRec q d h.2⟩
  | .loop _ p, d, h => freeBelow_of_noRec p d h
  | .fix b, d, h => freeBelow_of_noRec b (d + 1) h
  | .recur _, _, h => by simp [noRec] at h

/-- A `recur`-free program is closed. -/
theorem closed_of_noRec {p : Prog K Γ σ} (h : noRec p = true) : p.Closed :=
  freeBelow_of_noRec p 0 h

end NoRec

/-! ## Bit lists -/

theorem bitsVal_eq_head_tail (A : List Bool) :
    bitsVal A = 2 * bitsVal A.tail + (A.headD false).toNat := by
  cases A with
  | nil => rfl
  | cons a A =>
    simp only [bitsVal_cons, List.tail_cons, List.headD_cons]
    omega

theorem optBit_head?_map {ra : List Sym} (hra : TermOK ra) :
    ∀ A : List Bool, optBit (A.map Sym.bit ++ ra).head? = A.headD false
  | [] => by
    cases ra with
    | nil => rfl
    | cons d l =>
      have := hra d rfl
      cases d <;> simp_all [optBit]
  | _ :: _ => rfl

/-! ## Macros -/

variable {K : Type}

/-- Pop the bit block on top of `k` and its terminator (into the register). -/
def dropBits (k : K) : SProg K := .seq (popR k) (.loop optIsBit (popR k))

/-- Pop the number on top of `k`, keeping its terminator. -/
def dropNum (k : K) : SProg K := .seq (dropBits k) (restoreR k)

/-- Pop the zero bits on top of `t`. -/
def skipZeros (t : K) : SProg K := .loop isZeroBit (popR t)

/-- `t` holds MSB-first bits above a terminator: skip the high zeros, move the rest onto `d`
(LSB on top), and pop the terminator into the register. -/
def emitNorm (t d : K) : SProg K :=
  .seq (popR t) (.seq (skipZeros t) (.loop optIsBit (moveBitsBody t d)))


variable [DecidableEq K]

theorem dropBits_loop_eval (k : K) (ρ : List (SProg K)) :
    ∀ (L : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S k = (L.map Sym.bit ++ rest).tail →
      Eval ρ (.loop optIsBit (popR k)) ⟨(L.map Sym.bit ++ rest).head?, S⟩
        ⟨rest.head?, Function.update S k rest.tail⟩ (2 * L.length + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    have hS' : S k = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update S k rest.tail⟩
    rw [← hS', Function.update_eq_self]
  | b :: L, rest, S, hrest, hS => by
    have hS' : S k = L.map Sym.bit ++ rest := hS
    have hpop : Eval ρ (popR k) ⟨some (.bit b), S⟩
        ⟨(L.map Sym.bit ++ rest).head?, Function.update S k (L.map Sym.bit ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ k (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS']
    have ih := dropBits_loop_eval k ρ L rest (Function.update S k (L.map Sym.bit ++ rest).tail)
      hrest (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) hpop ih).of_eq ?_ (by simp only [List.length_cons]; omega)
    rw [Function.update_idem]

/-- **dropBits**, exact: the block and its terminator are popped. -/
theorem dropBits_eval {k : K} (ρ : List (SProg K)) (v : Option Sym) (L : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = L.map Sym.bit ++ rest) :
    Eval ρ (dropBits k) ⟨v, S⟩ ⟨rest.head?, Function.update S k rest.tail⟩ (2 * L.length + 2) := by
  have h1 : Eval ρ (popR k) ⟨v, S⟩
      ⟨(L.map Sym.bit ++ rest).head?, Function.update S k (L.map Sym.bit ++ rest).tail⟩ 1 := by
    refine (Eval.pop ρ k (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := dropBits_loop_eval k ρ L rest (Function.update S k (L.map Sym.bit ++ rest).tail) hrest
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  rw [Function.update_idem]

/-- **dropNum**, exact: the block is popped, the terminator stays. -/
theorem dropNum_eval {k : K} (ρ : List (SProg K)) (v : Option Sym) (L : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = L.map Sym.bit ++ rest) :
    Eval ρ (dropNum k) ⟨v, S⟩ ⟨rest.head?, Function.update S k rest⟩ (2 * L.length + 4) := by
  have h1 := dropBits_eval ρ v L rest S hrest hS
  have h2 := restoreR_eval ρ k rest (Function.update S k rest.tail) (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  rw [Function.update_idem]

theorem skipZeros_eval (t : K) (ρ : List (SProg K)) :
    ∀ (ds : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S t = (ds.map Sym.bit ++ rest).tail →
      Eval ρ (skipZeros t) ⟨(ds.map Sym.bit ++ rest).head?, S⟩
        ⟨((ds.dropWhile (fun b => !b)).map Sym.bit ++ rest).head?,
          Function.update S t ((ds.dropWhile (fun b => !b)).map Sym.bit ++ rest).tail⟩
        (2 * (ds.length - (ds.dropWhile (fun b => !b)).length) + 1)
  | [], rest, S, hrest, hS => by
    have hz : isZeroBit rest.head? = false := by
      cases rest with
      | nil => rfl
      | cons d l =>
        have := hrest d rfl
        cases d <;> simp_all [isZeroBit]
    refine (Eval.loop_false hz).of_eq ?_ (by simp)
    have hS' : S t = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update S t rest.tail⟩
    rw [← hS', Function.update_eq_self]
  | false :: ds, rest, S, hrest, hS => by
    have hS' : S t = ds.map Sym.bit ++ rest := hS
    have hpop : Eval ρ (popR t) ⟨some (.bit false), S⟩
        ⟨(ds.map Sym.bit ++ rest).head?, Function.update S t (ds.map Sym.bit ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ t (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS']
    have ih := skipZeros_eval t ρ ds rest (Function.update S t (ds.map Sym.bit ++ rest).tail) hrest
      (Function.update_self _ _ _)
    have hlen := length_dropWhile_le' (fun b => !b) ds
    have hd : (false :: ds).dropWhile (fun b => !b) = ds.dropWhile (fun b => !b) := rfl
    rw [hd]
    refine (Eval.loop_true (by rfl) hpop ih).of_eq ?_ ?_
    · rw [Function.update_idem]
    · simp only [List.length_cons]
      omega
  | true :: ds, rest, S, hrest, hS => by
    have hd : (true :: ds).dropWhile (fun b => !b) = true :: ds := rfl
    rw [hd]
    refine (Eval.loop_false (by rfl)).of_eq ?_ (by simp)
    have hS' : S t = ((true :: ds).map Sym.bit ++ rest).tail := hS
    rw [← hS', Function.update_eq_self]

/-- **emitNorm**, exact: `d` receives the canonical number whose MSB-first bits are `ds`. -/
theorem emitNorm_eval {t d : K} (htd : t ≠ d) (ρ : List (SProg K)) (v : Option Sym)
    (ds : List Bool) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S t = ds.map Sym.bit ++ rest) :
    Eval ρ (emitNorm t d) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S t rest.tail) d
        ((encodeNat (bitsVal ds.reverse)).map Sym.bit ++ S d)⟩
      (2 * ds.length + (ds.dropWhile (fun b => !b)).length + 3) := by
  have h1 : Eval ρ (popR t) ⟨v, S⟩
      ⟨(ds.map Sym.bit ++ rest).head?, Function.update S t (ds.map Sym.bit ++ rest).tail⟩ 1 := by
    refine (Eval.pop ρ t (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := skipZeros_eval t ρ ds rest (Function.update S t (ds.map Sym.bit ++ rest).tail) hrest
    (Function.update_self _ _ _)
  have h3 := moveBits_loop_eval htd ρ (ds.dropWhile (fun b => !b)) rest
    (Function.update (Function.update S t (ds.map Sym.bit ++ rest).tail) t
      ((ds.dropWhile (fun b => !b)).map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
  have hlen := length_dropWhile_le' (fun b => !b) ds
  refine (Eval.seq h1 (Eval.seq h2 h3)).of_eq ?_ (by omega)
  rw [← reverse_dropWhile_eq_encodeNat, List.map_reverse]
  simp only [Function.update_idem, Function.update_of_ne (Ne.symm htd)]

#assert_std_axioms closed_of_noRec bitsVal_eq_head_tail optBit_head?_map dropBits_eval
  dropNum_eval skipZeros_eval emitNorm_eval

end WP.W3
