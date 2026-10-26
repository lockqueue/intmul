/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Layout
import IntMulTM.Framework.Lib.Basic

/-!
# K3-PERM (`Machine/Walsh/PosPermGlue.lean`): stack primitives of the schedule interpreter

**Scope (honest summary).** Small fixed stack programs (`SProg K`: stacks `K`, one `Option Sym`
register) with exact evaluation lemmas, all proved:
* `moveUntil stop src dst`: move the symbols of `src` above the first `stop` onto `dst` (reversed)
  and pop the `stop` (`moveUntil_eval`, cost `3·|blk| + 2`).
* `dupAll src a b`: empty `src`, pushing every symbol onto both `a` and `b`, so that `a`, `b`
  receive the reversed content (`dupAll_eval`, cost `4·|L| + 2`).
* `fieldMoves src tmp n`: move the first `n` fields of an `hdrSyms` header from `src` onto `tmp`
  (reversed) (`fieldMoves_eval`).
* `copyHdr n src dst tmp`: copy the first `n` fields of a header on `src` onto `dst`, `src`
  restored, using the empty stack `tmp` (`copyHdr_eval`).
-/

namespace SubNLogN.Machine.PosPermRed

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib Computability

section Glue

variable {K : Type} [DecidableEq K]

/-! ### `moveUntil` -/

/-- Loop test of `moveUntil`: the register holds a symbol other than `stop`. -/
def contTest (stop : Sym) : Option Sym → Bool
  | some x => decide (x ≠ stop)
  | none => false

/-- Move the symbols of `src` above the first `stop` onto `dst` (reversed), popping the `stop`. -/
def moveUntil (stop : Sym) (src dst : K) : SProg K :=
  .seq (popR src) (.loop (contTest stop) (moveBitsBody src dst))

theorem moveUntil_loop_eval {src dst : K} (hne : src ≠ dst) (stop : Sym) (ρ : List (SProg K)) :
    ∀ (blk rest : List Sym) (S : K → List Sym), stop ∉ blk →
      S src = (blk ++ stop :: rest).tail →
      Eval ρ (.loop (contTest stop) (moveBitsBody src dst)) ⟨(blk ++ stop :: rest).head?, S⟩
        ⟨some stop, Function.update (Function.update S src rest) dst (blk.reverse ++ S dst)⟩
        (3 * blk.length + 1)
  | [], rest, S, _, hS => by
    have hS' : S src = rest := by simpa using hS
    refine (Eval.loop_false (by simp [contTest])).of_eq ?_ rfl
    show (⟨some stop, S⟩ : SSt K) = _
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: blk, rest, S, hstop, hS => by
    have hx : x ≠ stop := fun h => hstop (h ▸ List.mem_cons_self)
    have hstop' : stop ∉ blk := fun h => hstop (List.mem_cons_of_mem _ h)
    have hS' : S src = blk ++ stop :: rest := hS
    have hpush : Eval ρ (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      (Eval.push ρ dst (fun r => r.getD .sep) (some x) S).of_eq rfl rfl
    have hsrc : Function.update S dst (x :: S dst) src = blk ++ stop :: rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval ρ (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨(blk ++ stop :: rest).head?, Function.update (Function.update S dst (x :: S dst))
          src (blk ++ stop :: rest).tail⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := moveUntil_loop_eval hne stop ρ blk rest
      (Function.update (Function.update S dst (x :: S dst)) src (blk ++ stop :: rest).tail)
      hstop' (Function.update_self _ _ _)
    refine (Eval.loop_true (by simp [contTest, hx]) (Eval.seq hpush hpop) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all

/-- **`moveUntil`, exact.** -/
theorem moveUntil_eval {src dst : K} (hne : src ≠ dst) (stop : Sym) (ρ : List (SProg K))
    (v : Option Sym) (blk rest : List Sym) (S : K → List Sym) (hstop : stop ∉ blk)
    (hS : S src = blk ++ stop :: rest) :
    Eval ρ (moveUntil stop src dst) ⟨v, S⟩
      ⟨some stop, Function.update (Function.update S src rest) dst (blk.reverse ++ S dst)⟩
      (3 * blk.length + 2) := by
  have h1 : Eval ρ (popR src) ⟨v, S⟩
      ⟨(blk ++ stop :: rest).head?, Function.update S src (blk ++ stop :: rest).tail⟩ 1 := by
    refine (Eval.pop ρ src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := moveUntil_loop_eval hne stop ρ blk rest
    (Function.update S src (blk ++ stop :: rest).tail) hstop (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### `dupAll` -/

/-- Body of `dupAll`: push the register onto `a` and `b`, then pop `src`. -/
def dupBody2 (src a b : K) : SProg K := .seq (pushR a) (.seq (pushR b) (popR src))

/-- Empty `src`, pushing each symbol onto `a` and `b`. -/
def dupAll (src a b : K) : SProg K := .seq (popR src) (.loop (fun r => r.isSome) (dupBody2 src a b))

theorem dupAll_loop_eval {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (ρ : List (SProg K)) :
    ∀ (L : List Sym) (S : K → List Sym), S src = L.tail →
      Eval ρ (.loop (fun r => r.isSome) (dupBody2 src a b)) ⟨L.head?, S⟩
        ⟨none, Function.update (Function.update (Function.update S src []) a (L.reverse ++ S a)) b
          (L.reverse ++ S b)⟩ (4 * L.length + 1)
  | [], S, hS => by
    have hS' : S src = [] := hS
    refine (Eval.loop_false rfl).of_eq ?_ rfl
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | x :: L, S, hS => by
    have hS' : S src = L := hS
    have hpa : Eval ρ (pushR a) ⟨some x, S⟩ ⟨some x, Function.update S a (x :: S a)⟩ 1 :=
      (Eval.push ρ a (fun r => r.getD .sep) (some x) S).of_eq rfl rfl
    have hpb : Eval ρ (pushR b) ⟨some x, Function.update S a (x :: S a)⟩
        ⟨some x, Function.update (Function.update S a (x :: S a)) b
          (x :: Function.update S a (x :: S a) b)⟩ 1 :=
      (Eval.push ρ b (fun r => r.getD .sep) (some x) _).of_eq rfl rfl
    set S2 := Function.update (Function.update S a (x :: S a)) b
      (x :: Function.update S a (x :: S a) b) with hS2
    have hsrc : S2 src = L := by
      rw [hS2, Function.update_of_ne hsb, Function.update_of_ne hsa]
      exact hS'
    have hpop : Eval ρ (popR src) ⟨some x, S2⟩ ⟨L.head?, Function.update S2 src L.tail⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := dupAll_loop_eval hsa hsb hab ρ L (Function.update S2 src L.tail)
      (Function.update_self _ _ _)
    refine (Eval.loop_true rfl (Eval.seq hpa (Eval.seq hpb hpop)) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [hS2, Function.update_apply, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    split_ifs <;> simp_all

/-- **`dupAll`, exact**: `src` (content `L`) becomes empty, `a` and `b` receive `L.reverse`. -/
theorem dupAll_eval {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (ρ : List (SProg K)) (v : Option Sym) (S : K → List Sym) :
    Eval ρ (dupAll src a b) ⟨v, S⟩
      ⟨none, Function.update (Function.update (Function.update S src []) a ((S src).reverse ++ S a))
        b ((S src).reverse ++ S b)⟩ (4 * (S src).length + 2) := by
  have h1 : Eval ρ (popR src) ⟨v, S⟩ ⟨(S src).head?, Function.update S src (S src).tail⟩ 1 :=
    Eval.pop ρ src (fun _ o => o) v S
  have h2 := dupAll_loop_eval hsa hsb hab ρ (S src) (Function.update S src (S src).tail)
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### Moving and copying header fields -/

/-- Move one header field (`natSyms n ++ [mark]`) from `src` onto `tmp` (reversed). -/
def fieldMove (src tmp : K) : SProg K := .seq (moveBits src tmp) (pushR tmp)

/-- Move the first `n` header fields from `src` onto `tmp` (reversed). -/
def fieldMoves (src tmp : K) : ℕ → SProg K
  | 0 => skip
  | n + 1 => .seq (fieldMove src tmp) (fieldMoves src tmp n)

theorem fieldMove_eval {src tmp : K} (hne : src ≠ tmp) (ρ : List (SProg K)) (v : Option Sym)
    (f : ℕ) (rest : List Sym) (S : K → List Sym) (hS : S src = natSyms f ++ Sym.mark :: rest) :
    Eval ρ (fieldMove src tmp) ⟨v, S⟩
      ⟨some Sym.mark, Function.update (Function.update S src rest) tmp
        ((natSyms f ++ [Sym.mark]).reverse ++ S tmp)⟩ (3 * bitLen f + 3) := by
  have h1 := moveBits_eval hne ρ v (encodeNat f) (Sym.mark :: rest) S
    (fun d h => by simp at h; subst h; rfl) hS
  have h2 : Eval ρ (pushR tmp) ⟨some Sym.mark, Function.update (Function.update S src rest) tmp
        ((encodeNat f).reverse.map Sym.bit ++ S tmp)⟩
      ⟨some Sym.mark, Function.update (Function.update (Function.update S src rest) tmp
        ((encodeNat f).reverse.map Sym.bit ++ S tmp)) tmp
        (Sym.mark :: Function.update (Function.update S src rest) tmp
          ((encodeNat f).reverse.map Sym.bit ++ S tmp) tmp)⟩ 1 :=
    Eval.push ρ tmp (fun r => r.getD .sep) _ _
  refine (Eval.seq h1 h2).of_eq ?_ (by simp [bitLen])
  congr 1
  funext k
  simp only [Function.update_apply, natSyms, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.map_reverse]
  split_ifs <;> simp_all

/-- Cost of moving the fields `fs`. -/
def fieldsCost (fs : List ℕ) : ℕ := (fs.map fun f => 3 * bitLen f + 3).sum + 1

theorem fieldMoves_eval {src tmp : K} (hne : src ≠ tmp) (ρ : List (SProg K)) :
    ∀ (fs : List ℕ) (v : Option Sym) (rest : List Sym) (S : K → List Sym),
      S src = hdrSyms fs ++ rest →
      ∃ v', Eval ρ (fieldMoves src tmp fs.length) ⟨v, S⟩
        ⟨v', Function.update (Function.update S src rest) tmp ((hdrSyms fs).reverse ++ S tmp)⟩
        (fieldsCost fs)
  | [], v, rest, S, hS => by
    refine ⟨v, (skip_eval ρ _).of_eq ?_ (by simp [fieldsCost])⟩
    have hS' : S src = rest := by simpa [hdrSyms] using hS
    congr 1
    rw [← hS', Function.update_eq_self]
    simp [hdrSyms]
  | f :: fs, v, rest, S, hS => by
    have hS' : S src = natSyms f ++ Sym.mark :: (hdrSyms fs ++ rest) := by
      rw [hS]; simp [hdrSyms]
    have h1 := fieldMove_eval hne ρ v f (hdrSyms fs ++ rest) S hS'
    obtain ⟨v', h2⟩ := fieldMoves_eval hne ρ fs (some Sym.mark) rest
      (Function.update (Function.update S src (hdrSyms fs ++ rest)) tmp
        ((natSyms f ++ [Sym.mark]).reverse ++ S tmp))
      (by rw [Function.update_of_ne hne, Function.update_self])
    refine ⟨v', (Eval.seq h1 h2).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [Function.update_apply, hdrSyms, List.flatMap_cons, List.reverse_append,
        List.append_assoc]
      split_ifs <;> simp_all
    · simp only [fieldsCost, List.map_cons, List.sum_cons]
      omega

/-- Copy the first `n` header fields of `src` onto `dst` (`src` restored) via the stack `tmp`. -/
def copyHdr (n : ℕ) (src dst tmp : K) : SProg K := .seq (fieldMoves src tmp n) (dupAll tmp src dst)

/-- **`copyHdr`, exact**: if `src` holds `hdrSyms fs ++ rest` and `tmp` is empty, then `dst`
receives `hdrSyms fs` on top and every other stack is restored. -/
theorem copyHdr_eval {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (ρ : List (SProg K)) (v : Option Sym) (fs : List ℕ) (rest : List Sym) (S : K → List Sym)
    (hS : S src = hdrSyms fs ++ rest) (hT : S tmp = []) :
    ∃ v', Eval ρ (copyHdr fs.length src dst tmp) ⟨v, S⟩
      ⟨v', Function.update S dst (hdrSyms fs ++ S dst)⟩
      (fieldsCost fs + (4 * (hdrSyms fs).length + 2)) := by
  obtain ⟨v1, h1⟩ := fieldMoves_eval hst ρ fs v rest S hS
  have h2 := dupAll_eval (Ne.symm hst) (Ne.symm hdt) hsd ρ v1
    (Function.update (Function.update S src rest) tmp ((hdrSyms fs).reverse ++ S tmp))
  refine ⟨none, (Eval.seq h1 h2).of_eq ?_ ?_⟩
  · congr 1
    funext k
    simp only [Function.update_apply, hT, List.append_nil]
    split_ifs <;> simp_all
  · simp [hT]

end Glue

end SubNLogN.Machine.PosPermRed
