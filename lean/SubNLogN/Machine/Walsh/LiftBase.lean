/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.Twos
import IntMulTM.Framework.Lib.Counter

/-!
# `SubNLogN.Machine.Walsh.LiftBase`: unary counters on clean stacks (K3-LIFT, part 1)

Paper: Lemma 5.3 (`lem:walsh-lift`: append `8d`
fractional zero bits to every numerator and use width `w_* = w + 8d`) and Proposition 5.5 (`prop:cnot-batch`,
the exact lowering). The kernels are in `Walsh/Lift.lean`; this file has the generic stack loops
they use.

## Plan of the lift / lower kernels (`LiftBase`, `LiftLoop`, `Lift`)
* **Data.** The array `carrSyms W v` is a list of records; a record is `2·|cs|` two's-complement
  fields of `W` bits (LSB first), then `sep`. A lifted field is
  `twosBits (w + δ) (a·2^δ) = replicate δ false ++ twosBits w a`, so
  * lift = per field: emit `δ` zeros, then copy `w` bits;
  * lower = per field: drop `δ` bits, then copy `w` bits.
  No sign extension is needed: the width grows by exactly the number of appended low bits.
* **Template.** The runtime header `hdrSyms [w, δ]` is converted once into two unary counters on
  clean scratch stacks, `tz = uSym^δ` and `tc = uSym^w` (binary-to-unary by MSB-first doubling,
  `toUnary`; cost `O(w + δ + 1)`); the header is restored.
* **Field pass.** One field = walk `tz` (`δ` steps: push a `0`, resp. pop and drop an input bit),
  then walk `tc` (`w` steps: move an input bit to the output buffer); each walk moves the units to
  the scratch `u` and back (`drain`). Cost `7δ + 8w + 8`, exactly.
* **Record pass.** While the input head is a bit or `sep`: the field loop (while the head is a
  bit), then the record end. The output goes reversed onto the scratch `o` (guard `mark` at its
  bottom) and is rewound onto the array stack at the end (`rewindTo`), which restores the order.
  Then `tz`, `tc` are cleared, so every scratch stack ends empty (`KClean`).
* **Cost.** `≤ 50·(cvol (w + δ) v + w + δ + 1)`, using `1 ≤ w`.

**Scope (honest summary).** This file: the generic loops `drain`, `drain2`, `dbl`, `clear`,
`toUnary` with exact (resp. bounded) evaluation lemmas, the value lemma `accBits_reverse`, and
local copies of five small encoding lemmas of `K1/AddSub.lean` (`arrSyms_cons`, ...).
No contract is proved here.
-/

namespace SubNLogN.Machine.WalshLift

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine Computability

/-- The unit symbol of the unary counters. -/
def uSym : Sym := .sep2

/-- Loop test: the register holds a symbol (the last pop found a nonempty stack). -/
def isSomeR (r : Option Sym) : Bool := r.isSome

/-- Most-significant-bit-first value of a bit list, from the accumulator `a`. -/
def accBits (a : ℕ) (bs : List Bool) : ℕ := bs.foldl (fun a b => 2 * a + b.toNat) a

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n :=
  WP.W9comp.bitLen_le_of_lt_two_pow Nat.lt_two_pow_self

theorem accBits_reverse : ∀ l : List Bool, accBits 0 l.reverse = bitsVal l
  | [] => rfl
  | b :: l => by
    have ih := accBits_reverse l
    simp only [accBits] at ih ⊢
    rw [List.reverse_cons, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, bitsVal_cons]
    ring

theorem accBits_encodeNat (n : ℕ) : accBits 0 (encodeNat n).reverse = n := by
  rw [accBits_reverse, bitsVal_encodeNat]

/-! ## Record encodings (local copies, so that this file does not depend on `K1/AddSub.lean`) -/

theorem arrSyms_nil : arrSyms [] = [] := rfl

theorem arrSyms_cons (p : List Bool) (v : List (List Bool)) :
    arrSyms (p :: v) = recSyms p ++ arrSyms v := rfl

theorem recSyms_append (p : List Bool) (L : List Sym) :
    recSyms p ++ L = p.map Sym.bit ++ Sym.sep :: L := by
  simp [recSyms]

theorem reverse_recSyms (p : List Bool) :
    (recSyms p).reverse = Sym.sep :: p.reverse.map Sym.bit := by
  simp [recSyms, List.map_reverse]

theorem mark_not_mem_arrSyms : ∀ v : List (List Bool), Sym.mark ∉ arrSyms v
  | [] => by simp [arrSyms_nil]
  | p :: v => by
    rw [arrSyms_cons]
    have ih := mark_not_mem_arrSyms v
    simp [recSyms, ih]

theorem replicate_two_mul_succ (n : ℕ) (a : Sym) (l : List Sym) :
    List.replicate (2 * (n + 1)) a ++ l = List.replicate (2 * n) a ++ (a :: a :: l) := by
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.replicate_succ', List.replicate_succ']
  simp

section Progs

variable {K : Type}

/-- Loop body of `drain`. -/
def drainBody (src dst : K) : SProg K := .seq (pushR dst) (popR src)

/-- Move all of `src` onto `dst` (reversed). -/
def drain (src dst : K) : SProg K := .seq (popR src) (.loop isSomeR (drainBody src dst))

/-- Loop body of `drain2`. -/
def drain2Body (src dst : K) : SProg K :=
  .seq (pushC dst uSym) (.seq (pushC dst uSym) (popR src))

/-- Empty `src`, pushing two units onto `dst` per symbol. -/
def drain2 (src dst : K) : SProg K := .seq (popR src) (.loop isSomeR (drain2Body src dst))

/-- Double the unary counter `k` (which holds nothing else), using the empty scratch `u`. -/
def dbl (k u : K) : SProg K := .seq (drain k u) (drain2 u k)

/-- Empty the stack `k`. -/
def clear (k : K) : SProg K := .seq (popR k) (.loop isSomeR (popR k))

/-- One step of the binary-to-unary conversion (most significant bit first): restore the bit on
`h`, double `dst`, read the bit back and add it. -/
def u2Body (src dst h u : K) : SProg K :=
  .seq (pushR h) (.seq (dbl dst u) (.seq (peekR h)
    (.seq (.ite (isBitR true) (pushC dst uSym) skip) (popR src))))

/-- Binary-to-unary conversion: `src` holds bits, most significant on top, and nothing else. They
are moved back onto `h` (reversed), and `dst` receives their value in unary. -/
def toUnary (src dst h u : K) : SProg K := .seq (popR src) (.loop optIsBit (u2Body src dst h u))

theorem closed_drain (src dst : K) : (drain src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, drain, drainBody, pushR, popR]

theorem closed_clear (k : K) : (clear k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, clear, popR]

theorem closed_toUnary (src dst h u : K) : (toUnary src dst h u).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, toUnary, u2Body, dbl, drain, drainBody, drain2, drain2Body,
    pushR, popR, peekR, pushC, skip]

end Progs

/-! ## Evaluation -/

section Eval

variable {K : Type} [DecidableEq K]

theorem eval_pushR_some (k : K) (x : Sym) (S : K → List Sym) :
    Eval [] (pushR k) ⟨some x, S⟩ ⟨some x, Function.update S k (x :: S k)⟩ 1 := by
  unfold pushR
  exact Eval.push [] k (fun r : Option Sym => r.getD Sym.sep) (some x) S

theorem eval_pushC (k : K) (x : Sym) (v : Option Sym) (S : K → List Sym) :
    Eval [] (pushC k x) ⟨v, S⟩ ⟨v, Function.update S k (x :: S k)⟩ 1 := by
  unfold pushC
  exact Eval.push [] k (fun _ : Option Sym => x) v S

theorem eval_popR (k : K) (v : Option Sym) (L : List Sym) (S : K → List Sym) (hS : S k = L) :
    Eval [] (popR k) ⟨v, S⟩ ⟨L.head?, Function.update S k L.tail⟩ 1 := by
  refine (Eval.pop [] k (fun _ o => o) v S).of_eq ?_ rfl
  rw [hS]

theorem eval_peekR (k : K) (v : Option Sym) (L : List Sym) (S : K → List Sym) (hS : S k = L) :
    Eval [] (peekR k) ⟨v, S⟩ ⟨L.head?, S⟩ 1 := by
  refine (Eval.peek [] k (fun _ o => o) v S).of_eq ?_ rfl
  rw [hS]

theorem drain_loop_eval {src dst : K} (hne : src ≠ dst) :
    ∀ (L : List Sym) (S : K → List Sym), S src = L.tail →
      Eval [] (.loop isSomeR (drainBody src dst)) ⟨L.head?, S⟩
        ⟨none, Function.update (Function.update S src []) dst (L.reverse ++ S dst)⟩
        (3 * L.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    have hS' : S src = [] := hS
    have e : Function.update (Function.update S src []) dst (([] : List Sym).reverse ++ S dst) =
        S := by
      funext k
      simp only [Function.update_apply, List.reverse_nil, List.nil_append]
      split_ifs <;> simp_all
    rw [e]
    rfl
  | x :: L, S, hS => by
    have hS' : S src = L := hS
    have hpop := eval_popR src (some x) L (Function.update S dst (x :: S dst))
      (by rw [Function.update_of_ne hne, hS'])
    have ih := drain_loop_eval hne L
      (Function.update (Function.update S dst (x :: S dst)) src L.tail) (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) (Eval.seq (eval_pushR_some dst x S) hpop) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- **`drain`**, exact: `src` (holding `L`) is emptied onto `dst`, reversed. -/
theorem drain_eval {src dst : K} (hne : src ≠ dst) (v : Option Sym) (L : List Sym)
    (S : K → List Sym) (hS : S src = L) :
    Eval [] (drain src dst) ⟨v, S⟩
      ⟨none, Function.update (Function.update S src []) dst (L.reverse ++ S dst)⟩
      (3 * L.length + 2) := by
  have h1 := eval_popR src v L S hS
  have h2 := drain_loop_eval hne L (Function.update S src L.tail) (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem drain2_loop_eval {src dst : K} (hne : src ≠ dst) :
    ∀ (L : List Sym) (S : K → List Sym), S src = L.tail →
      Eval [] (.loop isSomeR (drain2Body src dst)) ⟨L.head?, S⟩
        ⟨none, Function.update (Function.update S src []) dst
          (List.replicate (2 * L.length) uSym ++ S dst)⟩ (4 * L.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    have hS' : S src = [] := hS
    have e : Function.update (Function.update S src []) dst
        (List.replicate (2 * ([] : List Sym).length) uSym ++ S dst) = S := by
      funext k
      simp only [Function.update_apply, List.length_nil, Nat.mul_zero, List.replicate_zero,
        List.nil_append]
      split_ifs <;> simp_all
    rw [e]
    rfl
  | x :: L, S, hS => by
    have hS' : S src = L := hS
    set S2 := Function.update (Function.update S dst (uSym :: S dst)) dst
      (uSym :: Function.update S dst (uSym :: S dst) dst) with hS2
    have hpop := eval_popR src (some x) L S2
      (by rw [hS2, Function.update_of_ne hne, Function.update_of_ne hne, hS'])
    have ih := drain2_loop_eval hne L (Function.update S2 src L.tail) (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl)
      (Eval.seq (eval_pushC dst uSym _ S) (Eval.seq (eval_pushC dst uSym _ _) hpop)) ih).of_eq
      ?_ ?_
    · congr 1
      funext k
      simp only [hS2, Function.update_apply, List.length_cons, replicate_two_mul_succ]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- **`drain2`**, exact: `src` (holding `L`) is emptied; `dst` receives `2·|L|` units. -/
theorem drain2_eval {src dst : K} (hne : src ≠ dst) (v : Option Sym) (L : List Sym)
    (S : K → List Sym) (hS : S src = L) :
    Eval [] (drain2 src dst) ⟨v, S⟩
      ⟨none, Function.update (Function.update S src []) dst
        (List.replicate (2 * L.length) uSym ++ S dst)⟩ (4 * L.length + 2) := by
  have h1 := eval_popR src v L S hS
  have h2 := drain2_loop_eval hne L (Function.update S src L.tail) (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- **`dbl`**, exact: a unary counter `a` on `k` (alone on its stack) becomes `2a`; the scratch
`u` starts and ends empty. -/
theorem dbl_eval {k u : K} (hne : k ≠ u) (v : Option Sym) (a : ℕ) (S : K → List Sym)
    (hK : S k = List.replicate a uSym) (hU : S u = []) :
    Eval [] (dbl k u) ⟨v, S⟩ ⟨none, Function.update S k (List.replicate (2 * a) uSym)⟩
      (7 * a + 4) := by
  have h1 := drain_eval hne v _ S hK
  have h2 := drain2_eval hne.symm none (List.replicate a uSym)
    (Function.update (Function.update S k []) u ((List.replicate a uSym).reverse ++ S u))
    (by rw [Function.update_self, hU, List.append_nil, List.reverse_replicate])
  refine (Eval.seq h1 h2).of_eq ?_ (by simp only [List.length_replicate]; omega)
  congr 1
  funext j
  simp only [Function.update_apply, List.length_replicate]
  split_ifs <;> simp_all

theorem clear_loop_eval (k : K) :
    ∀ (L : List Sym) (S : K → List Sym), S k = L.tail →
      Eval [] (.loop isSomeR (popR k)) ⟨L.head?, S⟩ ⟨none, Function.update S k []⟩
        (2 * L.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    have hS' : S k = [] := hS
    have e : Function.update S k [] = S := by rw [← hS', Function.update_eq_self]
    rw [e]
    rfl
  | x :: L, S, hS => by
    have hpop := eval_popR k (some x) L S hS
    have ih := clear_loop_eval k L (Function.update S k L.tail) (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) hpop ih).of_eq ?_ ?_
    · rw [Function.update_idem]
    · simp only [List.length_cons]
      omega

/-- **`clear`**, exact. -/
theorem clear_eval (k : K) (v : Option Sym) (L : List Sym) (S : K → List Sym) (hS : S k = L) :
    Eval [] (clear k) ⟨v, S⟩ ⟨none, Function.update S k []⟩ (2 * L.length + 2) := by
  have h1 := eval_popR k v L S hS
  have h2 := clear_loop_eval k L (Function.update S k L.tail) (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  rw [Function.update_idem]

theorem ite_add_bit_eval (dst : K) (b : Bool) (a : ℕ) (S : K → List Sym)
    (hD : S dst = List.replicate (2 * a) uSym) :
    Eval [] (.ite (isBitR true) (pushC dst uSym) skip) ⟨some (.bit b), S⟩
      ⟨some (.bit b), Function.update S dst (List.replicate (2 * a + b.toNat) uSym)⟩ 2 := by
  cases b
  · refine (Eval.ite_false (by simp [isBitR]) (skip_eval [] _)).of_eq ?_ rfl
    rw [Bool.toNat_false, Nat.add_zero, ← hD, Function.update_eq_self]
  · refine (Eval.ite_true (by simp [isBitR]) (eval_pushC dst uSym _ S)).of_eq ?_ rfl
    rw [hD, Bool.toNat_true, List.replicate_succ]

theorem u2Body_eval {src dst h u : K} (hsd : src ≠ dst) (hsh : src ≠ h)
    (hdh : dst ≠ h) (hdu : dst ≠ u) (hhu : h ≠ u) (b : Bool) (a : ℕ) (L : List Sym)
    (S : K → List Sym) (hS : S src = L) (hD : S dst = List.replicate a uSym) (hU : S u = []) :
    Eval [] (u2Body src dst h u) ⟨some (.bit b), S⟩
      ⟨L.head?, Function.update (Function.update (Function.update S h (.bit b :: S h)) dst
        (List.replicate (2 * a + b.toNat) uSym)) src L.tail⟩ (7 * a + 9) := by
  set S1 := Function.update S h (.bit b :: S h) with hS1
  have e1 := eval_pushR_some h (.bit b) S
  have e2 := dbl_eval hdu (some (.bit b)) a S1
    (by rw [hS1, Function.update_of_ne hdh, hD]) (by rw [hS1, Function.update_of_ne hhu.symm, hU])
  set S2 := Function.update S1 dst (List.replicate (2 * a) uSym) with hS2
  have e3 := eval_peekR h none (.bit b :: S h) S2
    (by rw [hS2, Function.update_of_ne hdh.symm, hS1, Function.update_self])
  have e4 := ite_add_bit_eval dst b a S2 (by rw [hS2, Function.update_self])
  have e5 := eval_popR src (some (.bit b)) L
    (Function.update S2 dst (List.replicate (2 * a + b.toNat) uSym))
    (by rw [Function.update_of_ne hsd, hS2, Function.update_of_ne hsd, hS1,
      Function.update_of_ne hsh, hS])
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [hS2, hS1, Function.update_apply]
  split_ifs <;> simp_all

theorem toUnary_loop_eval {src dst h u : K} (hsd : src ≠ dst) (hsh : src ≠ h) (hsu : src ≠ u)
    (hdh : dst ≠ h) (hdu : dst ≠ u) (hhu : h ≠ u) :
    ∀ (bs : List Bool) (a : ℕ) (S : K → List Sym), S src = (bs.map Sym.bit).tail →
      S dst = List.replicate a uSym → S u = [] →
      ∃ t, Eval [] (.loop optIsBit (u2Body src dst h u)) ⟨(bs.map Sym.bit).head?, S⟩
        ⟨none, Function.update (Function.update (Function.update S src []) dst
          (List.replicate (accBits a bs) uSym)) h (bs.reverse.map Sym.bit ++ S h)⟩ t ∧
        t + 7 * a ≤ 7 * accBits a bs + 10 * bs.length + 1
  | [], a, S, hS, hD, _ => by
    have hS' : S src = [] := hS
    refine ⟨1, (Eval.loop_false (by rfl)).of_eq ?_ rfl, by
      simp only [accBits, List.foldl_nil, List.length_nil]; omega⟩
    have e : Function.update (Function.update (Function.update S src []) dst
        (List.replicate (accBits a []) uSym)) h (([] : List Bool).reverse.map Sym.bit ++ S h) =
        S := by
      funext k
      simp only [Function.update_apply, accBits, List.foldl_nil, List.reverse_nil, List.map_nil,
        List.nil_append]
      split_ifs <;> simp_all
    rw [e]
    rfl
  | b :: bs, a, S, hS, hD, hU => by
    have hS' : S src = bs.map Sym.bit := hS
    have e1 := u2Body_eval hsd hsh hdh hdu hhu b a _ S hS' hD hU
    obtain ⟨t, e2, ht⟩ := toUnary_loop_eval hsd hsh hsu hdh hdu hhu bs (2 * a + b.toNat)
      (Function.update (Function.update (Function.update S h (.bit b :: S h)) dst
        (List.replicate (2 * a + b.toNat) uSym)) src (bs.map Sym.bit).tail)
      (Function.update_self _ _ _)
      (by rw [Function.update_of_ne hsd.symm, Function.update_self])
      (by rw [Function.update_of_ne hsu.symm, Function.update_of_ne hdu.symm,
        Function.update_of_ne hhu.symm, hU])
    refine ⟨7 * a + 9 + t + 1, (Eval.loop_true (by rfl) e1 e2).of_eq ?_ rfl, ?_⟩
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.singleton_append, accBits, List.foldl_cons]
      split_ifs <;> simp_all
    · simp only [accBits, List.foldl_cons, List.length_cons] at ht ⊢
      omega

/-- **`toUnary`**: the bits `bs` (most significant on top, alone on `src`) are moved back onto
`h` (reversed), and `dst` (holding `uSym^a`, alone) receives `uSym^(accBits a bs)`. The
scratch `u` starts and ends empty. Cost bound `7·accBits a bs + 10·|bs| + 2 - 7a`. -/
theorem toUnary_eval {src dst h u : K} (hsd : src ≠ dst) (hsh : src ≠ h) (hsu : src ≠ u)
    (hdh : dst ≠ h) (hdu : dst ≠ u) (hhu : h ≠ u) (v : Option Sym) (bs : List Bool) (a : ℕ)
    (S : K → List Sym) (hS : S src = bs.map Sym.bit) (hD : S dst = List.replicate a uSym)
    (hU : S u = []) :
    ∃ t, Eval [] (toUnary src dst h u) ⟨v, S⟩
      ⟨none, Function.update (Function.update (Function.update S src []) dst
        (List.replicate (accBits a bs) uSym)) h (bs.reverse.map Sym.bit ++ S h)⟩ t ∧
      t + 7 * a ≤ 7 * accBits a bs + 10 * bs.length + 2 := by
  have h1 := eval_popR src v _ S hS
  obtain ⟨t, h2, ht⟩ := toUnary_loop_eval hsd hsh hsu hdh hdu hhu bs a
    (Function.update S src (bs.map Sym.bit).tail) (Function.update_self _ _ _)
    (by rw [Function.update_of_ne hsd.symm, hD]) (by rw [Function.update_of_ne hsu.symm, hU])
  refine ⟨1 + t, (Eval.seq h1 h2).of_eq ?_ rfl, by omega⟩
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end Eval

end SubNLogN.Machine.WalshLift
