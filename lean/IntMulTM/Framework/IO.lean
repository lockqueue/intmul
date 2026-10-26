import IntMulTM.Framework.Layout
import IntMulTM.Framework.Bits

/-!
# IntMulTM.Framework.IO — copy-in and copy-out (the only code touching `input` / `output`)

Registers: one `Option Sym` (lift into a larger register file with `Prog.liftRegs`).

* `copyIn tr w` : move the whole input stack onto work stack `w`, translating symbols by
  `tr : A → Sym` (reverses the order: for `encodeNat` input, the work stack then holds the
  number MSB-first, most significant bit on top). Exact cost `3 * |input| + 2`.
* `copyOut w` : work stack `w` holds `ds.map Sym.bit ++ rest` (MSB-first bits `ds`; `rest` empty
  or starting with a non-bit symbol); skip high zeros and emit the bits onto `output`. Result on
  `output`: exactly `encodeNat (bitsVal ds.reverse)` (LSB first, normalized, `0 ↦ []`).
  Exact cost `2 * |ds| + |ds.dropWhile (!·)| + 3 ≤ 3 * |ds| + 3`.
-/

namespace TMFw

open Turing

theorem length_dropWhile_le' {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.dropWhile p).length ≤ l.length
  | [] => Nat.le_refl _
  | x :: l => by
    by_cases h : p x = true
    · have e : (x :: l).dropWhile p = l.dropWhile p := by simp [h]
      rw [e]
      exact Nat.le_succ_of_le (length_dropWhile_le' p l)
    · have e : (x :: l).dropWhile p = x :: l := by simp [h]
      rw [e]

section IO

variable {W A : Type}

/-- Programs over the production layout with one `Option Sym` register. -/
abbrev IOProg (W A : Type) := Prog (StackId W) (StackId.Γ A) (Option Sym)

/-- Pop the input stack into the register, translated by `tr`. -/
def popIn (tr : A → Sym) : IOProg W A := .pop .input (fun _ o => o.map tr)

/-- Pop work stack `w` into the register. -/
def popW (w : W) : IOProg W A := .pop (.work w) (fun _ o => o)

/-- The copy-in loop body: push the register onto `w`, pop the next input symbol. -/
def copyInBody (tr : A → Sym) (w : W) : IOProg W A :=
  .seq (.push (.work w) (fun r => r.getD .sep)) (popIn tr)

/-- Copy-in. -/
def copyIn (tr : A → Sym) (w : W) : IOProg W A :=
  .seq (popIn tr) (.loop (fun r => r.isSome) (copyInBody tr w))

/-- Is the register the bit `0`? -/
def isZeroBit : Option Sym → Bool
  | some (.bit false) => true
  | _ => false

/-- The copy-out emit body: push the register's bit onto `output`, pop the next work symbol. -/
def copyOutBody (w : W) : IOProg W A := .seq (.push .output optBit) (popW w)

/-- Copy-out. -/
def copyOut (w : W) : IOProg W A :=
  .seq (popW w) (.seq (.loop isZeroBit (popW w)) (.loop optIsBit (copyOutBody w)))

variable [DecidableEq W]

/-! ### copy-in -/

theorem copyIn_loop_eval (tr : A → Sym) (w : W) (ρ : List (IOProg W A)) :
    ∀ (rem : List A) (S : ∀ k : StackId W, List (StackId.Γ A k)), S .input = rem.tail →
      Eval ρ (.loop (fun r => r.isSome) (copyInBody tr w)) ⟨rem.head?.map tr, S⟩
        ⟨none, Function.update (Function.update S .input []) (.work w)
          ((rem.map tr).reverse ++ S (.work w))⟩ (3 * rem.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    have h1 : Function.update S .input [] = S := by
      rw [Function.update_eq_self_iff]
      exact hS.symm
    congr 1
    rw [h1]
    exact (Function.update_eq_self _ _).symm
  | a :: rem, S, hS => by
    have hpush : Eval ρ (.push (.work w) (fun r => r.getD .sep)) ⟨some (tr a), S⟩
        ⟨some (tr a), Function.update S (.work w) (tr a :: S (.work w))⟩ 1 :=
      (Eval.push ρ (.work w) (fun r => r.getD .sep) (some (tr a)) S).of_eq rfl rfl
    have hin : Function.update S (.work w) (tr a :: S (.work w)) .input = rem := by
      rw [upd_work_input]
      exact hS
    have hpop : Eval ρ (popIn tr) ⟨some (tr a), Function.update S (.work w) (tr a :: S (.work w))⟩
        ⟨rem.head?.map tr, Function.update (Function.update S (.work w) (tr a :: S (.work w)))
          .input rem.tail⟩ 1 := by
      refine (Eval.pop ρ .input (fun _ o => o.map tr) _ _).of_eq ?_ rfl
      rw [hin]
    have ih := copyIn_loop_eval tr w ρ rem
      (Function.update (Function.update S (.work w) (tr a :: S (.work w))) .input rem.tail)
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) (Eval.seq hpush hpop) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    apply StackId.stk_ext
    · simp
    · simp
    · intro w'
      by_cases hw : w' = w
      · subst hw
        simp
      · simp [hw]

/-- **copy-in**, exact. -/
theorem copyIn_eval (tr : A → Sym) (w : W) (ρ : List (IOProg W A)) (v : Option Sym)
    (S : ∀ k : StackId W, List (StackId.Γ A k)) :
    Eval ρ (copyIn tr w) ⟨v, S⟩
      ⟨none, Function.update (Function.update S .input []) (.work w)
        (((S .input).map tr).reverse ++ S (.work w))⟩ (3 * (S .input).length + 2) := by
  have h1 : Eval ρ (popIn tr) ⟨v, S⟩
      ⟨(S .input).head?.map tr, Function.update S .input (S .input).tail⟩ 1 :=
    Eval.pop ρ .input (fun _ o => o.map tr) v S
  have h2 := copyIn_loop_eval tr w ρ (S .input) (Function.update S .input (S .input).tail)
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  apply StackId.stk_ext
  · simp
  · simp
  · intro w'
    by_cases hw : w' = w
    · subst hw
      simp
    · simp [hw]

/-! ### copy-out -/

theorem copyOut_skip_eval (w : W) (ρ : List (IOProg W A)) :
    ∀ (ds : List Bool) (rest : List Sym) (S : ∀ k : StackId W, List (StackId.Γ A k)),
      TermOK rest → S (.work w) = (ds.map Sym.bit ++ rest).tail →
      Eval ρ (.loop isZeroBit (popW w)) ⟨(ds.map Sym.bit ++ rest).head?, S⟩
        ⟨((ds.dropWhile (fun b => !b)).map Sym.bit ++ rest).head?,
          Function.update S (.work w) ((ds.dropWhile (fun b => !b)).map Sym.bit ++ rest).tail⟩
        (2 * (ds.length - (ds.dropWhile (fun b => !b)).length) + 1)
  | [], rest, S, hrest, hS => by
    have hz : isZeroBit rest.head? = false := by
      cases rest with
      | nil => rfl
      | cons d l =>
        have := hrest d rfl
        cases d <;> simp_all [isZeroBit]
    refine (Eval.loop_false hz).of_eq ?_ (by simp)
    have hS' : S (.work w) = rest.tail := hS
    show (⟨rest.head?, S⟩ : St (StackId W) (StackId.Γ A) (Option Sym)) =
      ⟨rest.head?, Function.update S (.work w) rest.tail⟩
    rw [← hS', Function.update_eq_self]
  | false :: ds, rest, S, hrest, hS => by
    have hS' : S (.work w) = ds.map Sym.bit ++ rest := hS
    have hpop : Eval ρ (popW w) ⟨some (.bit false), S⟩
        ⟨(ds.map Sym.bit ++ rest).head?,
          Function.update S (.work w) (ds.map Sym.bit ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ (.work w) (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS']
    have ih := copyOut_skip_eval w ρ ds rest
      (Function.update S (.work w) (ds.map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
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
    have hS' : S (.work w) = ((true :: ds).map Sym.bit ++ rest).tail := hS
    rw [← hS', Function.update_eq_self]

theorem copyOut_emit_eval (w : W) (ρ : List (IOProg W A)) :
    ∀ (es : List Bool) (rest : List Sym) (S : ∀ k : StackId W, List (StackId.Γ A k)),
      TermOK rest → S (.work w) = (es.map Sym.bit ++ rest).tail →
      Eval ρ (.loop optIsBit (copyOutBody w))
        ⟨(es.map Sym.bit ++ rest).head?, S⟩
        ⟨rest.head?, Function.update (Function.update S (.work w) rest.tail) .output
          (es.reverse ++ S .output)⟩ (3 * es.length + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    have hS' : S (.work w) = rest.tail := hS
    show (⟨rest.head?, S⟩ : St (StackId W) (StackId.Γ A) (Option Sym)) =
      ⟨rest.head?, Function.update (Function.update S (.work w) rest.tail) .output
        ([] ++ S .output)⟩
    rw [← hS', Function.update_eq_self, List.nil_append, Function.update_eq_self]
  | e :: es, rest, S, hrest, hS => by
    have hS' : S (.work w) = es.map Sym.bit ++ rest := hS
    have hpush : Eval ρ (.push .output optBit) ⟨some (.bit e), S⟩
        ⟨some (.bit e), Function.update S .output (e :: S .output)⟩ 1 :=
      (Eval.push ρ .output optBit (some (.bit e)) S).of_eq rfl rfl
    have hw : Function.update S .output (e :: S .output) (.work w) = es.map Sym.bit ++ rest := by
      rw [upd_output_work]
      exact hS'
    have hpop : Eval ρ (popW w) ⟨some (.bit e), Function.update S .output (e :: S .output)⟩
        ⟨(es.map Sym.bit ++ rest).head?,
          Function.update (Function.update S .output (e :: S .output)) (.work w)
            (es.map Sym.bit ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ (.work w) (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hw]
    have ih := copyOut_emit_eval w ρ es rest
      (Function.update (Function.update S .output (e :: S .output)) (.work w)
        (es.map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) (Eval.seq hpush hpop) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    apply StackId.stk_ext
    · simp
    · simp
    · intro w'
      by_cases hw' : w' = w
      · subst hw'
        simp
      · simp [hw']

/-- **copy-out**, exact. -/
theorem copyOut_eval (w : W) (ρ : List (IOProg W A)) (v : Option Sym) (ds : List Bool)
    (rest : List Sym) (S : ∀ k : StackId W, List (StackId.Γ A k)) (hrest : TermOK rest)
    (hS : S (.work w) = ds.map Sym.bit ++ rest) :
    Eval ρ (copyOut w) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S (.work w) rest.tail) .output
        ((ds.dropWhile (fun b => !b)).reverse ++ S .output)⟩
      (2 * ds.length + (ds.dropWhile (fun b => !b)).length + 3) := by
  have h1 : Eval ρ (popW w) ⟨v, S⟩
      ⟨(ds.map Sym.bit ++ rest).head?, Function.update S (.work w) (ds.map Sym.bit ++ rest).tail⟩
      1 := by
    refine (Eval.pop ρ (.work w) (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := copyOut_skip_eval w ρ ds rest
    (Function.update S (.work w) (ds.map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
  have h3 := copyOut_emit_eval w ρ (ds.dropWhile (fun b => !b)) rest
    (Function.update (Function.update S (.work w) (ds.map Sym.bit ++ rest).tail) (.work w)
      ((ds.dropWhile (fun b => !b)).map Sym.bit ++ rest).tail) hrest
    (Function.update_self _ _ _)
  have hlen := length_dropWhile_le' (fun b => !b) ds
  refine (Eval.seq h1 (Eval.seq h2 h3)).of_eq ?_ (by omega)
  congr 1
  apply StackId.stk_ext
  · simp
  · simp
  · intro w'
    by_cases hw : w' = w
    · subst hw
      simp
    · simp [hw]

/-- **copy-out produces exactly `encodeNat`**, in at most `3 * |ds| + 3` steps. -/
theorem copyOut_eval_encodeNat (w : W) (ρ : List (IOProg W A)) (v : Option Sym) (ds : List Bool)
    (rest : List Sym) (S : ∀ k : StackId W, List (StackId.Γ A k)) (hrest : TermOK rest)
    (hS : S (.work w) = ds.map Sym.bit ++ rest) :
    ∃ t, t ≤ 3 * ds.length + 3 ∧ Eval ρ (copyOut w) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update S (.work w) rest.tail) .output
        (Computability.encodeNat (bitsVal ds.reverse) ++ S .output)⟩ t := by
  refine ⟨_, ?_, (copyOut_eval w ρ v ds rest S hrest hS).of_eq ?_ rfl⟩
  · have := length_dropWhile_le' (fun b => !b) ds
    omega
  · rw [reverse_dropWhile_eq_encodeNat]

end IO

end TMFw
