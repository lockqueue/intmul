import Contracts.Machine.W3

/-!
# WP.W3s.Macros — small stack macros (generic in the stack type `K`)

| macro | effect (pre: `S k = blk.map bit ++ rest`, `TermOK rest`) | cost |
|---|---|---|
| `dropBits k` | `k := rest.tail` (terminator popped into the register) | `2·|blk| + 2` |
| `dropZeros k` | `k := (dropRun false blk).map bit ++ rest` (leading `0`s popped) | `2·runLen false blk + 4` |

Plus list facts used by the loops (`optIsBit_head?_bits`, `runLen_le_length`, …).
-/

namespace TMFw.W3s

open TMFw TMFw.Lib TMFw.Contracts Computability

variable {K : Type}

/-- Pop while the register holds a bit. -/
def dropLoop (k : K) : SProg K := .loop optIsBit (popR k)

/-- Pop the top bit block of `k` and its terminator (the terminator goes to the register). -/
def dropBits (k : K) : SProg K := .seq (popR k) (dropLoop k)

/-- Pop the leading `0`s of the top bit block of `k`. -/
def dropZeros (k : K) : SProg K :=
  .seq (popR k) (.seq (.loop (isBitR false) (popR k)) (restoreR k))

/-! ## List facts -/

theorem optIsBit_head?_bits (l : List Bool) {rest : List Sym} (h : TermOK rest) :
    optIsBit (l.map Sym.bit ++ rest).head? = !decide (l = []) := by
  cases l with
  | nil => simpa using optIsBit_head?_of_termOK h
  | cons b l => simp [optIsBit]

theorem runLen_le_length (b : Bool) : ∀ l : List Bool, runLen b l ≤ l.length
  | [] => le_rfl
  | x :: l => by
    have := runLen_le_length b l
    by_cases hx : x = b
    · simp only [runLen, hx, if_true, List.length_cons]
      omega
    · simp only [runLen, hx, if_false, List.length_cons]
      omega

theorem length_dropRun_le (b : Bool) : ∀ l : List Bool, (dropRun b l).length ≤ l.length
  | [] => le_rfl
  | x :: l => by
    have := length_dropRun_le b l
    by_cases hx : x = b
    · simp only [dropRun, hx, if_true, List.length_cons]
      omega
    · simp only [dropRun, hx, if_false, List.length_cons]
      omega

variable [DecidableEq K]

/-- Three updates only depend on the base function outside the updated points. -/
theorem upd3_congr {S S' : K → List Sym} {a b c : K}
    (h : ∀ j, j ≠ a → j ≠ b → j ≠ c → S j = S' j) (A B C : List Sym) :
    Function.update (Function.update (Function.update S a A) b B) c C =
      Function.update (Function.update (Function.update S' a A) b B) c C := by
  funext j
  simp only [Function.update_apply]
  split_ifs with h1 h2 h3
  · rfl
  · rfl
  · rfl
  · exact h j h3 h2 h1

/-! ## dropBits -/

theorem dropLoop_eval {k : K} (ρ : List (SProg K)) :
    ∀ (es : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S k = (es.map Sym.bit ++ rest).tail →
      Eval ρ (dropLoop k) ⟨(es.map Sym.bit ++ rest).head?, S⟩
        ⟨rest.head?, Function.update S k rest.tail⟩ (2 * es.length + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    have hS' : S k = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update S k rest.tail⟩
    rw [← hS', Function.update_eq_self]
  | e :: es, rest, S, hrest, hS => by
    have hS' : S k = es.map Sym.bit ++ rest := hS
    have hpop : Eval ρ (popR k) ⟨some (.bit e), S⟩
        ⟨(es.map Sym.bit ++ rest).head?, Function.update S k (es.map Sym.bit ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ k (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hS']
    have ih := dropLoop_eval ρ es rest (Function.update S k (es.map Sym.bit ++ rest).tail) hrest
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) hpop ih).of_eq ?_ ?_
    · rw [Function.update_idem]
    · simp only [List.length_cons]
      omega

/-- **dropBits**, exact: pop the bit block and its terminator. -/
theorem dropBits_eval {k : K} (ρ : List (SProg K)) (v : Option Sym) (es : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest) (hS : S k = es.map Sym.bit ++ rest) :
    Eval ρ (dropBits k) ⟨v, S⟩ ⟨rest.head?, Function.update S k rest.tail⟩ (2 * es.length + 2) := by
  have h1 : Eval ρ (popR k) ⟨v, S⟩
      ⟨(es.map Sym.bit ++ rest).head?, Function.update S k (es.map Sym.bit ++ rest).tail⟩ 1 := by
    refine (Eval.pop ρ k (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := dropLoop_eval ρ es rest (Function.update S k (es.map Sym.bit ++ rest).tail) hrest
    (Function.update_self _ _ _)
  rw [Function.update_idem] at h2
  exact (Eval.seq h1 h2).of_eq rfl (by omega)

/-! ## dropZeros -/

theorem zeroLoop_eval {k : K} (ρ : List (SProg K)) :
    ∀ (es : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S k = (es.map Sym.bit ++ rest).tail →
      Eval ρ (.loop (isBitR false) (popR k)) ⟨(es.map Sym.bit ++ rest).head?, S⟩
        ⟨((dropRun false es).map Sym.bit ++ rest).head?,
          Function.update S k ((dropRun false es).map Sym.bit ++ rest).tail⟩
        (2 * runLen false es + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (isBitR_head?_of_termOK false hrest)).of_eq ?_ rfl
    have hS' : S k = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update S k rest.tail⟩
    rw [← hS', Function.update_eq_self]
  | false :: es, rest, S, hrest, hS => by
    have hS' : S k = es.map Sym.bit ++ rest := hS
    have hpop : Eval ρ (popR k) ⟨some (.bit false), S⟩
        ⟨(es.map Sym.bit ++ rest).head?, Function.update S k (es.map Sym.bit ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ k (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hS']
    have ih := zeroLoop_eval ρ es rest (Function.update S k (es.map Sym.bit ++ rest).tail) hrest
      (Function.update_self _ _ _)
    rw [Function.update_idem] at ih
    have hd : dropRun false (false :: es) = dropRun false es := by simp [dropRun]
    have hr : runLen false (false :: es) = runLen false es + 1 := by simp [runLen]
    rw [hd, hr]
    exact (Eval.loop_true (by simp [isBitR]) hpop ih).of_eq rfl (by omega)
  | true :: es, rest, S, hrest, hS => by
    have hd : dropRun false (true :: es) = true :: es := by simp [dropRun]
    have hr : runLen false (true :: es) = 0 := by simp [runLen]
    rw [hd, hr]
    refine (Eval.loop_false (by simp [isBitR])).of_eq ?_ rfl
    show (⟨((true :: es).map Sym.bit ++ rest).head?, S⟩ : SSt K) =
      ⟨((true :: es).map Sym.bit ++ rest).head?,
        Function.update S k ((true :: es).map Sym.bit ++ rest).tail⟩
    rw [← hS, Function.update_eq_self]

/-- **dropZeros**, exact: pop the leading zeros of the top bit block. -/
theorem dropZeros_eval {k : K} (ρ : List (SProg K)) (v : Option Sym) (es : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest) (hS : S k = es.map Sym.bit ++ rest) :
    Eval ρ (dropZeros k) ⟨v, S⟩
      ⟨((dropRun false es).map Sym.bit ++ rest).head?,
        Function.update S k ((dropRun false es).map Sym.bit ++ rest)⟩ (2 * runLen false es + 4) := by
  have h1 : Eval ρ (popR k) ⟨v, S⟩
      ⟨(es.map Sym.bit ++ rest).head?, Function.update S k (es.map Sym.bit ++ rest).tail⟩ 1 := by
    refine (Eval.pop ρ k (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := zeroLoop_eval ρ es rest (Function.update S k (es.map Sym.bit ++ rest).tail) hrest
    (Function.update_self _ _ _)
  rw [Function.update_idem] at h2
  have h3 := restoreR_eval ρ k ((dropRun false es).map Sym.bit ++ rest)
    (Function.update S k ((dropRun false es).map Sym.bit ++ rest).tail) (Function.update_self _ _ _)
  rw [Function.update_idem] at h3
  exact (Eval.seq h1 (Eval.seq h2 h3)).of_eq rfl (by omega)

#assert_std_axioms optIsBit_head?_bits runLen_le_length length_dropRun_le upd3_congr dropLoop_eval
  dropBits_eval zeroLoop_eval dropZeros_eval

end TMFw.W3s
