import Contracts.Machine.Common
import IntMulTM.Framework.Lib.Counter
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# WP.TapeConv.Prims — stacks, registers and loop primitives of the table-tape converter

The converter runs on four stacks `CS = tr | x | y | z`:
* `tr` holds the table tape (W7's encoding on entry, W9's on exit);
* `x` accumulates the converted tape, reversed, above the guard `gX = tag 7`;
* `y`, `z` hold a copy of `pSub` (for the stride `3·pSub`) or of the leaf's `K` (stage counter).

Registers `CR = Option Sym × Fin 3`: the last symbol read and the carry of the `×3` transducer.
States are written `mk4 tr x y z`.

`Ev ρ p S S' t`: from **every** register value, `p` maps the stacks `S` to `S'` within `t` steps
(environment `ρ`). `Ev.seq` composes without side conditions; register-dependent control flow is
handled inside the primitive lemmas.

The `×3` arithmetic (`m3o`, `m3c`, `m3run`, `flushBits`, `m3_result`) has the same definitions as
WP.W3b.Arith; it is re-proved here so that this package depends only on the framework and contracts.
-/

namespace WP.TapeConv

open TMFw TMFw.Contracts Computability

/-! ## Stacks, registers, states -/

/-- The converter's stacks: the table stack and three scratch stacks. -/
inductive CS
  | tr
  | x
  | y
  | z
  deriving DecidableEq, Repr

instance : Fintype CS where
  elems := {.tr, .x, .y, .z}
  complete k := by cases k <;> simp

/-- Registers: the symbol slot and the carry of `×3`. -/
abbrev CR : Type := Option Sym × Fin 3

/-- Converter programs. -/
abbrev CP : Type := Prog CS (fun _ => Sym) CR

/-- A stack assignment given by its four stacks. -/
def mk4 (a b c d : List Sym) : CS → List Sym
  | .tr => a
  | .x => b
  | .y => c
  | .z => d

theorem mk4_eta (S : CS → List Sym) : mk4 (S .tr) (S .x) (S .y) (S .z) = S := by
  funext k
  cases k <;> rfl

theorem upd_tr (a b c d l : List Sym) : Function.update (mk4 a b c d) .tr l = mk4 l b c d := by
  funext k
  cases k <;> simp [mk4]

theorem upd_x (a b c d l : List Sym) : Function.update (mk4 a b c d) .x l = mk4 a l c d := by
  funext k
  cases k <;> simp [mk4]

theorem upd_y (a b c d l : List Sym) : Function.update (mk4 a b c d) .y l = mk4 a b l d := by
  funext k
  cases k <;> simp [mk4]

theorem upd_z (a b c d l : List Sym) : Function.update (mk4 a b c d) .z l = mk4 a b c l := by
  funext k
  cases k <;> simp [mk4]

/-! ## Atoms -/

/-- Pop `k` into the symbol slot. -/
def popS (k : CS) : CP := .pop k fun v o => (o, v.2)

/-- Peek `k` into the symbol slot. -/
def peekS (k : CS) : CP := .peek k fun v o => (o, v.2)

/-- Push the symbol slot onto `k` (default `sep`). -/
def pushS (k : CS) : CP := .push k fun v => v.1.getD .sep

/-- Push a constant onto `k`. -/
def pushK (k : CS) (s : Sym) : CP := .push k fun _ => s

/-- Do nothing (one step). -/
def skipP : CP := .load id

/-- The symbol slot holds a bit. -/
def isB (v : CR) : Bool := optIsBit v.1

/-- The symbol slot holds `s`. -/
def isS (s : Sym) (v : CR) : Bool := decide (v.1 = some s)

/-- The symbol slot does not hold `s`. -/
def notS (s : Sym) (v : CR) : Bool := !decide (v.1 = some s)

theorem popT_eval (ρ : List CP) (v : CR) (A X Y Z : List Sym) :
    Eval ρ (popS .tr) ⟨v, mk4 A X Y Z⟩ ⟨(A.head?, v.2), mk4 A.tail X Y Z⟩ 1 := by
  have e := Eval.pop ρ CS.tr (fun (v : CR) o => (o, v.2)) v (mk4 A X Y Z)
  rw [upd_tr] at e
  exact e

theorem popX_eval (ρ : List CP) (v : CR) (T A Y Z : List Sym) :
    Eval ρ (popS .x) ⟨v, mk4 T A Y Z⟩ ⟨(A.head?, v.2), mk4 T A.tail Y Z⟩ 1 := by
  have e := Eval.pop ρ CS.x (fun (v : CR) o => (o, v.2)) v (mk4 T A Y Z)
  rw [upd_x] at e
  exact e

theorem popY_eval (ρ : List CP) (v : CR) (T X A Z : List Sym) :
    Eval ρ (popS .y) ⟨v, mk4 T X A Z⟩ ⟨(A.head?, v.2), mk4 T X A.tail Z⟩ 1 := by
  have e := Eval.pop ρ CS.y (fun (v : CR) o => (o, v.2)) v (mk4 T X A Z)
  rw [upd_y] at e
  exact e

theorem popZ_eval (ρ : List CP) (v : CR) (T X Y A : List Sym) :
    Eval ρ (popS .z) ⟨v, mk4 T X Y A⟩ ⟨(A.head?, v.2), mk4 T X Y A.tail⟩ 1 := by
  have e := Eval.pop ρ CS.z (fun (v : CR) o => (o, v.2)) v (mk4 T X Y A)
  rw [upd_z] at e
  exact e

theorem peekT_eval (ρ : List CP) (v : CR) (A X Y Z : List Sym) :
    Eval ρ (peekS .tr) ⟨v, mk4 A X Y Z⟩ ⟨(A.head?, v.2), mk4 A X Y Z⟩ 1 :=
  Eval.peek ρ CS.tr (fun (v : CR) o => (o, v.2)) v (mk4 A X Y Z)

theorem peekZ_eval (ρ : List CP) (v : CR) (T X Y A : List Sym) :
    Eval ρ (peekS .z) ⟨v, mk4 T X Y A⟩ ⟨(A.head?, v.2), mk4 T X Y A⟩ 1 :=
  Eval.peek ρ CS.z (fun (v : CR) o => (o, v.2)) v (mk4 T X Y A)

theorem pushKX_eval (ρ : List CP) (s : Sym) (v : CR) (T X Y Z : List Sym) :
    Eval ρ (pushK .x s) ⟨v, mk4 T X Y Z⟩ ⟨v, mk4 T (s :: X) Y Z⟩ 1 := by
  have e := Eval.push ρ CS.x (fun (_ : CR) => s) v (mk4 T X Y Z)
  rw [upd_x] at e
  exact e

theorem pushKY_eval (ρ : List CP) (s : Sym) (v : CR) (T X Y Z : List Sym) :
    Eval ρ (pushK .y s) ⟨v, mk4 T X Y Z⟩ ⟨v, mk4 T X (s :: Y) Z⟩ 1 := by
  have e := Eval.push ρ CS.y (fun (_ : CR) => s) v (mk4 T X Y Z)
  rw [upd_y] at e
  exact e

theorem pushKZ_eval (ρ : List CP) (s : Sym) (v : CR) (T X Y Z : List Sym) :
    Eval ρ (pushK .z s) ⟨v, mk4 T X Y Z⟩ ⟨v, mk4 T X Y (s :: Z)⟩ 1 := by
  have e := Eval.push ρ CS.z (fun (_ : CR) => s) v (mk4 T X Y Z)
  rw [upd_z] at e
  exact e

theorem pushSX_eval (ρ : List CP) (a : Sym) (c : Fin 3) (T X Y Z : List Sym) :
    Eval ρ (pushS .x) ⟨(some a, c), mk4 T X Y Z⟩ ⟨(some a, c), mk4 T (a :: X) Y Z⟩ 1 := by
  have e := Eval.push ρ CS.x (fun (v : CR) => v.1.getD .sep) (some a, c) (mk4 T X Y Z)
  rw [upd_x] at e
  exact e

theorem pushSY_eval (ρ : List CP) (a : Sym) (c : Fin 3) (T X Y Z : List Sym) :
    Eval ρ (pushS .y) ⟨(some a, c), mk4 T X Y Z⟩ ⟨(some a, c), mk4 T X (a :: Y) Z⟩ 1 := by
  have e := Eval.push ρ CS.y (fun (v : CR) => v.1.getD .sep) (some a, c) (mk4 T X Y Z)
  rw [upd_y] at e
  exact e

theorem pushSZ_eval (ρ : List CP) (a : Sym) (c : Fin 3) (T X Y Z : List Sym) :
    Eval ρ (pushS .z) ⟨(some a, c), mk4 T X Y Z⟩ ⟨(some a, c), mk4 T X Y (a :: Z)⟩ 1 := by
  have e := Eval.push ρ CS.z (fun (v : CR) => v.1.getD .sep) (some a, c) (mk4 T X Y Z)
  rw [upd_z] at e
  exact e

theorem pushST_eval (ρ : List CP) (a : Sym) (c : Fin 3) (T X Y Z : List Sym) :
    Eval ρ (pushS .tr) ⟨(some a, c), mk4 T X Y Z⟩ ⟨(some a, c), mk4 (a :: T) X Y Z⟩ 1 := by
  have e := Eval.push ρ CS.tr (fun (v : CR) => v.1.getD .sep) (some a, c) (mk4 T X Y Z)
  rw [upd_tr] at e
  exact e

theorem skip_eval (ρ : List CP) (v : CR) (S : CS → List Sym) : Eval ρ skipP ⟨v, S⟩ ⟨v, S⟩ 1 :=
  Eval.load ρ id v S

/-! ## Bit loops -/

/-- While the symbol slot is a bit: push it onto `dst`, pop the next symbol of `src`. -/
def copyLoop (src dst : CS) : CP := .loop isB (.seq (pushS dst) (popS src))

/-- While the symbol slot is a bit: pop the next symbol of `src`. -/
def dropLoop (src : CS) : CP := .loop isB (popS src)

/-- While the symbol slot is a bit: push it onto `a` and `b`, pop the next symbol of `src`. -/
def dupLoop (src a b : CS) : CP := .loop isB (.seq (pushS a) (.seq (pushS b) (popS src)))

theorem copyTX_eval (ρ : List CP) (c : Fin 3) :
    ∀ (es : List Bool) (rest X Y Z : List Sym), TermOK rest →
      Eval ρ (copyLoop .tr .x)
        ⟨((es.map Sym.bit ++ rest).head?, c), mk4 (es.map Sym.bit ++ rest).tail X Y Z⟩
        ⟨(rest.head?, c), mk4 rest.tail (es.reverse.map Sym.bit ++ X) Y Z⟩ (3 * es.length + 1)
  | [], rest, X, Y, Z, hrest => Eval.loop_false (optIsBit_head?_of_termOK hrest)
  | e :: es, rest, X, Y, Z, hrest => by
    have h1 := pushSX_eval ρ (.bit e) c (es.map Sym.bit ++ rest) X Y Z
    have h2 := popT_eval ρ (some (.bit e), c) (es.map Sym.bit ++ rest) (.bit e :: X) Y Z
    have ih := copyTX_eval ρ c es rest (.bit e :: X) Y Z hrest
    refine (Eval.loop_true (by rfl) (Eval.seq h1 h2) ih).of_eq ?_ ?_
    · simp
    · simp only [List.length_cons]
      omega

theorem copyYZ_eval (ρ : List CP) (c : Fin 3) :
    ∀ (es : List Bool) (rest T X Z : List Sym), TermOK rest →
      Eval ρ (copyLoop .y .z)
        ⟨((es.map Sym.bit ++ rest).head?, c), mk4 T X (es.map Sym.bit ++ rest).tail Z⟩
        ⟨(rest.head?, c), mk4 T X rest.tail (es.reverse.map Sym.bit ++ Z)⟩ (3 * es.length + 1)
  | [], rest, T, X, Z, hrest => Eval.loop_false (optIsBit_head?_of_termOK hrest)
  | e :: es, rest, T, X, Z, hrest => by
    have h1 := pushSZ_eval ρ (.bit e) c T X (es.map Sym.bit ++ rest) Z
    have h2 := popY_eval ρ (some (.bit e), c) T X (es.map Sym.bit ++ rest) (.bit e :: Z)
    have ih := copyYZ_eval ρ c es rest T X (.bit e :: Z) hrest
    refine (Eval.loop_true (by rfl) (Eval.seq h1 h2) ih).of_eq ?_ ?_
    · simp
    · simp only [List.length_cons]
      omega

theorem dropT_eval (ρ : List CP) (c : Fin 3) :
    ∀ (es : List Bool) (rest X Y Z : List Sym), TermOK rest →
      Eval ρ (dropLoop .tr)
        ⟨((es.map Sym.bit ++ rest).head?, c), mk4 (es.map Sym.bit ++ rest).tail X Y Z⟩
        ⟨(rest.head?, c), mk4 rest.tail X Y Z⟩ (2 * es.length + 1)
  | [], rest, X, Y, Z, hrest => Eval.loop_false (optIsBit_head?_of_termOK hrest)
  | e :: es, rest, X, Y, Z, hrest => by
    have h2 := popT_eval ρ (some (.bit e), c) (es.map Sym.bit ++ rest) X Y Z
    have ih := dropT_eval ρ c es rest X Y Z hrest
    refine (Eval.loop_true (by rfl) h2 ih).of_eq rfl ?_
    simp only [List.length_cons]
    omega

theorem dupTXY_eval (ρ : List CP) (c : Fin 3) :
    ∀ (es : List Bool) (rest X Y Z : List Sym), TermOK rest →
      Eval ρ (dupLoop .tr .x .y)
        ⟨((es.map Sym.bit ++ rest).head?, c), mk4 (es.map Sym.bit ++ rest).tail X Y Z⟩
        ⟨(rest.head?, c), mk4 rest.tail (es.reverse.map Sym.bit ++ X) (es.reverse.map Sym.bit ++ Y) Z⟩
        (4 * es.length + 1)
  | [], rest, X, Y, Z, hrest => Eval.loop_false (optIsBit_head?_of_termOK hrest)
  | e :: es, rest, X, Y, Z, hrest => by
    have h1 := pushSX_eval ρ (.bit e) c (es.map Sym.bit ++ rest) X Y Z
    have h2 := pushSY_eval ρ (.bit e) c (es.map Sym.bit ++ rest) (.bit e :: X) Y Z
    have h3 := popT_eval ρ (some (.bit e), c) (es.map Sym.bit ++ rest) (.bit e :: X) (.bit e :: Y) Z
    have ih := dupTXY_eval ρ c es rest (.bit e :: X) (.bit e :: Y) Z hrest
    refine (Eval.loop_true (by rfl) (Eval.seq h1 (Eval.seq h2 h3)) ih).of_eq ?_ ?_
    · simp
    · simp only [List.length_cons]
      omega

/-- The guard below the converted tape on `x` (W9's `symGuard`; it occurs in no tape). -/
abbrev gX : Sym := .tag 7

/-- While the symbol slot is not the guard: push it onto `tr`, pop the next symbol of `x`. -/
def backLoop : CP := .loop (notS gX) (.seq (pushS .tr) (popS .x))

theorem back_eval (ρ : List CP) (c : Fin 3) :
    ∀ (l T X0 Y Z : List Sym), (∀ s ∈ l, s ≠ gX) →
      Eval ρ backLoop ⟨((l ++ gX :: X0).head?, c), mk4 T (l ++ gX :: X0).tail Y Z⟩
        ⟨(some gX, c), mk4 (l.reverse ++ T) X0 Y Z⟩ (3 * l.length + 1)
  | [], T, X0, Y, Z, _ => Eval.loop_false (by rfl)
  | a :: l, T, X0, Y, Z, hl => by
    have ha : a ≠ gX := hl a (by simp)
    have h1 := pushST_eval ρ a c T (l ++ gX :: X0) Y Z
    have h2 := popX_eval ρ (some a, c) (a :: T) (l ++ gX :: X0) Y Z
    have ih := back_eval ρ c l (a :: T) X0 Y Z (fun s hs => hl s (by simp [hs]))
    refine (Eval.loop_true ?_ (Eval.seq h1 h2) ih).of_eq ?_ ?_
    · simp [notS, ha]
    · simp
    · simp only [List.length_cons]
      omega

/-! ## `×3`, LSB first (same definitions as WP.W3b.Arith) -/

theorem bitsVal_append : ∀ L M : List Bool,
    bitsVal (L ++ M) = bitsVal L + 2 ^ L.length * bitsVal M
  | [], M => by simp
  | b :: L, M => by
    rw [List.cons_append, bitsVal_cons, bitsVal_append L M, bitsVal_cons, List.length_cons,
      pow_succ]
    ring

theorem normBits_append_true : ∀ M : List Bool, normBits (M ++ [true]) = M ++ [true]
  | [] => by simp [normBits]
  | b :: M => by
    rw [List.cons_append, normBits, normBits_append_true M]
    simp

theorem normBits_tail {b : Bool} {L : List Bool} (h : normBits (b :: L) = b :: L) :
    normBits L = L := by
  have h2 : (if b = false ∧ normBits L = [] then [] else b :: normBits L) = b :: L := h
  split at h2
  · exact absurd h2 (List.cons_ne_nil _ _).symm
  · exact (List.cons.inj h2).2

/-- `3·b + c`. -/
def m3s (c : Fin 3) (b : Bool) : ℕ := 3 * b.toNat + c.val

/-- Output bit of one `×3` step. -/
def m3o (c : Fin 3) (b : Bool) : Bool := decide (m3s c b % 2 = 1)

/-- Carry out of one `×3` step. -/
def m3c (c : Fin 3) (b : Bool) : Fin 3 :=
  ⟨m3s c b / 2, by have := c.isLt; have := Bool.toNat_le b; unfold m3s; omega⟩

theorem m3_id (c : Fin 3) (b : Bool) :
    3 * b.toNat + c.val = 2 * (m3c c b).val + (m3o c b).toNat := by
  revert c b
  decide

/-- Run `×3` over an LSB-first bit list: output bits and final carry. -/
def m3run : Fin 3 → List Bool → List Bool × Fin 3
  | c, [] => ([], c)
  | c, b :: l => (m3o c b :: (m3run (m3c c b) l).1, (m3run (m3c c b) l).2)

/-- The flushed carry, LSB first. -/
def flushBits (c : Fin 3) : List Bool :=
  if c.val = 0 then [] else if c.val = 1 then [true] else [false, true]

theorem bitsVal_flushBits (c : Fin 3) : bitsVal (flushBits c) = c.val := by
  revert c
  decide

theorem flushBits_length (c : Fin 3) : (flushBits c).length ≤ 2 := by
  revert c
  decide

theorem m3run_length : ∀ (c : Fin 3) (l : List Bool), (m3run c l).1.length = l.length
  | _, [] => rfl
  | c, b :: l => by simp [m3run, m3run_length (m3c c b) l]

theorem m3run_val : ∀ (c : Fin 3) (l : List Bool),
    bitsVal (m3run c l).1 + 2 ^ l.length * (m3run c l).2.val = 3 * bitsVal l + c.val
  | c, [] => by simp [m3run]
  | c, b :: l => by
    have ih := m3run_val (m3c c b) l
    have hid := m3_id c b
    simp only [m3run, bitsVal_cons, List.length_cons, pow_succ]
    linear_combination 2 * ih + hid.symm

theorem m3run_carry_pos : ∀ (L : List Bool) (c : Fin 3), normBits L = L → L ≠ [] →
    1 ≤ (m3run c L).2.val
  | [], _, _, h => absurd rfl h
  | [b], c, hn, _ => by
    cases b
    · simp [normBits] at hn
    · simp only [m3run, m3c, m3s, Bool.toNat_true]
      omega
  | b :: b' :: L, c, hn, _ => by
    simp only [m3run]
    exact m3run_carry_pos (b' :: L) (m3c c b) (normBits_tail hn) (List.cons_ne_nil _ _)

/-- **`×3` result**: output plus flushed carry is the canonical encoding of `3a`. -/
theorem m3_result (a : ℕ) :
    (m3run 0 (encodeNat a)).1 ++ flushBits (m3run 0 (encodeNat a)).2 = encodeNat (3 * a) := by
  have hval := m3run_val 0 (encodeNat a)
  have hlen := m3run_length 0 (encodeNat a)
  have hb : bitsVal ((m3run 0 (encodeNat a)).1 ++ flushBits (m3run 0 (encodeNat a)).2) =
      3 * a := by
    rw [bitsVal_append, bitsVal_flushBits, hlen, hval, bitsVal_encodeNat]
    simp
  have hn : normBits ((m3run 0 (encodeNat a)).1 ++ flushBits (m3run 0 (encodeNat a)).2) =
      (m3run 0 (encodeNat a)).1 ++ flushBits (m3run 0 (encodeNat a)).2 := by
    by_cases ha : a = 0
    · subst ha
      simp [encodeNat_zero, m3run, flushBits, normBits]
    · have hne : encodeNat a ≠ [] := fun h => ha ((encodeNat_eq_nil_iff a).1 h)
      have hpos := m3run_carry_pos (encodeNat a) 0 (normBits_encodeNat a) hne
      have hlt := (m3run 0 (encodeNat a)).2.isLt
      simp only [flushBits]
      rw [if_neg (show ¬ (m3run 0 (encodeNat a)).2.val = 0 by omega)]
      split_ifs
      · exact normBits_append_true _
      · rw [show (m3run 0 (encodeNat a)).1 ++ [false, true] =
          ((m3run 0 (encodeNat a)).1 ++ [false]) ++ [true] by simp]
        exact normBits_append_true _
  rw [← hb, encodeNat_bitsVal, hn]

/-- `bitLen (3·n) ≤ bitLen n + 2`. -/
theorem bitLen_mul3_le (n : ℕ) : bitLen (3 * n) ≤ bitLen n + 2 := by
  have h := congrArg List.length (m3_result n)
  rw [List.length_append, m3run_length] at h
  have h2 := flushBits_length (m3run 0 (encodeNat n)).2
  unfold bitLen
  omega

/-- The `×3` transducer from `z` to `x`: emit the output bit, pop the next bit with the new carry. -/
def m3Loop : CP :=
  .loop isB (.seq (.push .x fun v => .bit (m3o v.2 (optBit v.1)))
    (.pop .z fun v o => (o, m3c v.2 (optBit v.1))))

theorem m3_eval (ρ : List CP) :
    ∀ (es : List Bool) (c : Fin 3) (rest T X Y : List Sym), TermOK rest →
      Eval ρ m3Loop ⟨((es.map Sym.bit ++ rest).head?, c), mk4 T X Y (es.map Sym.bit ++ rest).tail⟩
        ⟨(rest.head?, (m3run c es).2),
          mk4 T ((m3run c es).1.reverse.map Sym.bit ++ X) Y rest.tail⟩ (3 * es.length + 1)
  | [], c, rest, T, X, Y, hrest => Eval.loop_false (optIsBit_head?_of_termOK hrest)
  | e :: es, c, rest, T, X, Y, hrest => by
    have h1 : Eval ρ (.push .x fun (v : CR) => Sym.bit (m3o v.2 (optBit v.1)))
        ⟨(some (.bit e), c), mk4 T X Y (es.map Sym.bit ++ rest)⟩
        ⟨(some (.bit e), c), mk4 T (.bit (m3o c e) :: X) Y (es.map Sym.bit ++ rest)⟩ 1 := by
      have e1 := Eval.push ρ CS.x (fun (v : CR) => Sym.bit (m3o v.2 (optBit v.1)))
        (some (.bit e), c) (mk4 T X Y (es.map Sym.bit ++ rest))
      rw [upd_x] at e1
      exact e1
    have h2 : Eval ρ (.pop .z fun (v : CR) o => (o, m3c v.2 (optBit v.1)))
        ⟨(some (.bit e), c), mk4 T (.bit (m3o c e) :: X) Y (es.map Sym.bit ++ rest)⟩
        ⟨((es.map Sym.bit ++ rest).head?, m3c c e),
          mk4 T (.bit (m3o c e) :: X) Y (es.map Sym.bit ++ rest).tail⟩ 1 := by
      have e2 := Eval.pop ρ CS.z (fun (v : CR) o => (o, m3c v.2 (optBit v.1)))
        (some (.bit e), c) (mk4 T (.bit (m3o c e) :: X) Y (es.map Sym.bit ++ rest))
      rw [upd_z] at e2
      exact e2
    have ih := m3_eval ρ es (m3c c e) rest T (.bit (m3o c e) :: X) Y hrest
    refine (Eval.loop_true (by rfl) (Eval.seq h1 h2) ih).of_eq ?_ ?_
    · simp [m3run]
    · simp only [List.length_cons]
      omega

/-- Push the flushed carry bits onto `x` (LSB first, so they end up after the output bits). -/
def flushP : CP :=
  .seq (.ite (fun v => decide (v.2.val = 2)) (pushK .x (.bit false)) skipP)
    (.ite (fun v => decide (v.2.val ≠ 0)) (pushK .x (.bit true)) skipP)

theorem flush_eval (ρ : List CP) (r : Option Sym) (c : Fin 3) (T X Y Z : List Sym) :
    Eval ρ flushP ⟨(r, c), mk4 T X Y Z⟩
      ⟨(r, c), mk4 T ((flushBits c).reverse.map Sym.bit ++ X) Y Z⟩ 4 := by
  rcases c with ⟨_ | _ | _ | n, hc⟩
  · exact (Eval.seq (Eval.ite_false (by rfl) (skip_eval ρ _ _))
      (Eval.ite_false (by rfl) (skip_eval ρ _ _))).of_eq (by simp [flushBits]) rfl
  · exact (Eval.seq (Eval.ite_false (by rfl) (skip_eval ρ _ _))
      (Eval.ite_true (by rfl) (pushKX_eval ρ _ _ T X Y Z))).of_eq (by simp [flushBits]) rfl
  · exact (Eval.seq (Eval.ite_true (by rfl) (pushKX_eval ρ _ _ T X Y Z))
      (Eval.ite_true (by rfl) (pushKX_eval ρ _ _ T _ Y Z))).of_eq (by simp [flushBits]) rfl
  · omega

/-! ## Bit lengths -/

theorem length_incBits : ∀ L : List Bool, (incBits L).length ≤ L.length + 1
  | [] => by simp [incBits]
  | true :: L => by
    have := length_incBits L
    simp only [incBits, List.length_cons]
    omega
  | false :: L => by simp [incBits]

theorem bitLen_le_self : ∀ n : ℕ, bitLen n ≤ n
  | 0 => by simp [bitLen, encodeNat_zero]
  | n + 1 => by
    have h := bitLen_le_self n
    have h2 := length_incBits (encodeNat n)
    unfold bitLen at *
    rw [encodeNat_succ]
    omega

theorem encodeNat_succ_cons (n : ℕ) : ∃ b l, encodeNat (n + 1) = b :: l := by
  cases h : encodeNat (n + 1) with
  | nil => exact absurd ((encodeNat_eq_nil_iff _).1 h) (by omega)
  | cons b l => exact ⟨b, l, rfl⟩

/-! ## Register-agnostic runs -/

/-- From every register value, `p` maps the stacks `S` to `S'` within `t` steps (environment `ρ`). -/
def Ev (ρ : List CP) (p : CP) (S S' : CS → List Sym) (t : ℕ) : Prop :=
  ∀ v : CR, ∃ v' : CR, ∃ t', t' ≤ t ∧ Eval ρ p ⟨v, S⟩ ⟨v', S'⟩ t'

theorem Ev.seq {ρ : List CP} {p q : CP} {S S₁ S₂ : CS → List Sym} {t₁ t₂ : ℕ}
    (h₁ : Ev ρ p S S₁ t₁) (h₂ : Ev ρ q S₁ S₂ t₂) : Ev ρ (.seq p q) S S₂ (t₁ + t₂) := by
  intro v
  obtain ⟨v₁, u₁, hu₁, e₁⟩ := h₁ v
  obtain ⟨v₂, u₂, hu₂, e₂⟩ := h₂ v₁
  exact ⟨v₂, u₁ + u₂, by omega, Eval.seq e₁ e₂⟩

theorem Ev.mono {ρ : List CP} {p : CP} {S S' : CS → List Sym} {t t' : ℕ} (h : Ev ρ p S S' t)
    (ht : t ≤ t') : Ev ρ p S S' t' := by
  intro v
  obtain ⟨v', u, hu, e⟩ := h v
  exact ⟨v', u, by omega, e⟩

theorem Ev.of_eq {ρ : List CP} {p : CP} {S S₁ S₂ : CS → List Sym} {t : ℕ} (h : Ev ρ p S S₁ t)
    (hS : S₁ = S₂) : Ev ρ p S S₂ t := hS ▸ h

theorem ev_popT (ρ : List CP) (a : Sym) (A X Y Z : List Sym) :
    Ev ρ (popS .tr) (mk4 (a :: A) X Y Z) (mk4 A X Y Z) 1 :=
  fun v => ⟨(some a, v.2), 1, le_rfl, popT_eval ρ v (a :: A) X Y Z⟩

theorem ev_pushKX (ρ : List CP) (s : Sym) (T X Y Z : List Sym) :
    Ev ρ (pushK .x s) (mk4 T X Y Z) (mk4 T (s :: X) Y Z) 1 :=
  fun v => ⟨v, 1, le_rfl, pushKX_eval ρ s v T X Y Z⟩

theorem ev_pushKY (ρ : List CP) (s : Sym) (T X Y Z : List Sym) :
    Ev ρ (pushK .y s) (mk4 T X Y Z) (mk4 T X (s :: Y) Z) 1 :=
  fun v => ⟨v, 1, le_rfl, pushKY_eval ρ s v T X Y Z⟩

theorem ev_pushKZ (ρ : List CP) (s : Sym) (T X Y Z : List Sym) :
    Ev ρ (pushK .z s) (mk4 T X Y Z) (mk4 T X Y (s :: Z)) 1 :=
  fun v => ⟨v, 1, le_rfl, pushKZ_eval ρ s v T X Y Z⟩

/-- Accumulator form of a push onto `x`: `x = A.reverse ++ X0` becomes `(A ++ [s]).reverse ++ X0`. -/
theorem ev_pushAcc (ρ : List CP) (s : Sym) (T A X0 Y Z : List Sym) :
    Ev ρ (pushK .x s) (mk4 T (A.reverse ++ X0) Y Z) (mk4 T ((A ++ [s]).reverse ++ X0) Y Z) 1 :=
  (ev_pushKX ρ s T (A.reverse ++ X0) Y Z).of_eq (by simp)

/-! ## Closedness -/

theorem freeBelow_mapStk {K K' A σ : Type} (ι : K → K') :
    ∀ (p : Prog K (fun _ => A) σ) (d : ℕ), (p.mapStk ι).FreeBelow d ↔ p.FreeBelow d
  | .push _ _, _ => Iff.rfl
  | .peek _ _, _ => Iff.rfl
  | .pop _ _, _ => Iff.rfl
  | .load _, _ => Iff.rfl
  | .seq p q, d => by
    simp only [Prog.mapStk, Prog.FreeBelow, freeBelow_mapStk ι p d, freeBelow_mapStk ι q d]
  | .ite _ p q, d => by
    simp only [Prog.mapStk, Prog.FreeBelow, freeBelow_mapStk ι p d, freeBelow_mapStk ι q d]
  | .loop _ p, d => by simp only [Prog.mapStk, Prog.FreeBelow, freeBelow_mapStk ι p d]
  | .fix b, d => by simp only [Prog.mapStk, Prog.FreeBelow, freeBelow_mapStk ι b (d + 1)]
  | .recur _, _ => Iff.rfl

#assert_std_axioms mk4_eta upd_tr upd_x upd_y upd_z copyTX_eval copyYZ_eval dropT_eval
  dupTXY_eval back_eval m3_result bitLen_mul3_le m3_eval flush_eval bitLen_le_self Ev.seq
  ev_pushAcc freeBelow_mapStk

end WP.TapeConv
