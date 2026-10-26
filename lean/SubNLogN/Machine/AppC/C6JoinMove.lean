/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6TArith
import SubNLogN.Machine.AppC.C6JoinPure
import SubNLogN.Machine.AppC.C6BitMove

/-!
# Lemma A.8 join/unjoin: machine part 1 (`Machine/AppC/C6JoinMove.lean`): layout, the in-place move,
counter helpers, the cost budget

Shared by `C6JoinHigh.lean` (`C6HighJoinStmt`) and the unjoin files `C6JoinUnProof*.lean`
(`C6UnjoinStmt`, a separate package).

* Layout `KJ E1 = KLoc (Fin 5) (E1 ⊕ (TS ⊕ PS))`: the named stacks of the leaf contracts
  (`0` the array, `1`-`4` the counters `e, G, B, w`), the K1 kernel's scratch `E1`, the threshold
  kernel's scratch `TS` (`C6TArith.lean`) and the private stacks `PS`. Registers
  `RJ R1 = R1 × NatArith.Reg`.
* `moveJ P1`: the K1 kernel `K1MoveDigitMixStmt` (source: the array, destination: the private stack
  `D`, counters on `N1`, `N2`), then the move back onto the array stack (`C6BitMoveAux.movePG`).
  Proved: `runs_moveJ`.
* `mkPow`, `mkSub` (generic stack type, `NatArith.Reg`): `Y := a·q^n`, `z := a - b`, above a fresh
  `mark`. Proved: `runs_mkPow`, `runs_mkSub`; the threshold kernel in this layout, `runs_callT`.
* The cost budget `Λ = q^(2e)·G·B`: `master_le`, `(n + 1)·L² ≤ 512·(2·|q| + c + 1)²·Λ` whenever
  `n ≤ e` and `L ≤ 2e·|q| + |G| + |B| + c` (`|x| = bitLen x`).

All helpers are in `SubNLogN.Machine.AppC.C6JoinAux`. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

namespace AppC.C6JoinAux

open NatArith

/-! ## Layout -/

/-- Private stacks of the joining kernels. -/
inductive PS where
  | D | T | N1 | N2 | Kc | Kt | tS | lS | PB | Kc2 | Q | Td | A | Bs | Acc | Tm
  deriving DecidableEq

instance : Fintype PS where
  elems := {.D, .T, .N1, .N2, .Kc, .Kt, .tS, .lS, .PB, .Kc2, .Q, .Td, .A, .Bs, .Acc, .Tm}
  complete := fun x => by cases x <;> simp

/-- Scratch of the joining kernels: the K1 kernel's `E1`, the threshold kernel's `TS`, and `PS`. -/
abbrev EJ (E1 : Type) : Type := E1 ⊕ (TS ⊕ PS)

/-- Layout of the joining kernels. -/
abbrev KJ (E1 : Type) : Type := KLoc (Fin 5) (EJ E1)

/-- Registers of the joining kernels: the K1 kernel's and the `NatArith` registers. -/
abbrev RJ (R1 : Type) : Type := R1 × NatArith.Reg

/-- The private stack `x`. -/
def jp {E1 : Type} (x : PS) : KJ E1 := .inr (.inr (.inr x))

@[simp] theorem jp_inj {E1 : Type} (x y : PS) : (jp x : KJ E1) = jp y ↔ x = y := by simp [jp]

@[simp] theorem jp_ne_inl {E1 : Type} (x : PS) (i : Fin 5) : (jp x : KJ E1) ≠ .inl i := by
  simp [jp]

@[simp] theorem inl_ne_jp {E1 : Type} (x : PS) (i : Fin 5) : (.inl i : KJ E1) ≠ jp x := by
  simp [jp]

@[simp] theorem jp_ne_ts {E1 : Type} (x : PS) (y : TS) : (jp x : KJ E1) ≠ .inr (.inr (.inl y)) := by
  simp [jp]

@[simp] theorem jp_ne_e1 {E1 : Type} (x : PS) (y : E1) : (jp x : KJ E1) ≠ .inr (.inl y) := by
  simp [jp]

section Layout

variable (E1 : Type)

/-- The K1 kernel: source `0 ↦ 0` (the array), destination `1 ↦ D`, counters `2 ↦ N1`,
`3 ↦ N2`, scratch `E1`. -/
def ιK : KLoc (Fin 4) E1 → KJ E1 :=
  Sum.elim ![.inl 0, jp .D, jp .N1, jp .N2] fun e => .inr (.inl e)

/-- The threshold kernel: `0 ↦ 1` (the counter `e`), `1 ↦ tS`, scratch `TS`. -/
def ιT : KT → KJ E1 :=
  Sum.elim ![.inl 1, jp .tS] fun x => .inr (.inr (.inl x))

theorem ιK_inj : Function.Injective (ιK E1) := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [jp]
  · intro a b h
    simpa using h
  · intro i e
    fin_cases i <;> simp [jp]

theorem ιT_inj : Function.Injective (ιT E1) := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [jp]
  · intro a b h
    simpa using h
  · intro i x
    fin_cases i <;> simp [jp]

end Layout

section Lenses

variable (R1 : Type)

/-- The K1 kernel's registers. -/
def lK : Lens (RJ R1) R1 := Lens.fst _ _

/-- The `NatArith` registers. -/
def lN : Lens (RJ R1) NatArith.Reg := Lens.snd _ _

/-- The work register (loop counters, peeks, rewinds). -/
def lWJ : Lens (RJ R1) (Option Sym) := (Lens.snd _ _).comp NatArith.lW

end Lenses

/-! ## The in-place move -/

section Move

variable {E1 : Type} [DecidableEq E1] {R1 : Type}

/-- **One digit move in place**: the K1 kernel from the array (stack `0`) into `D`, then the move
back onto stack `0` through `T` (`C6BitMoveAux.movePG`). -/
def moveJ (P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1) : Prog (KJ E1) (fun _ => Sym) (RJ R1) :=
  C6BitMoveAux.movePG (lWJ R1) (callInj (ιK E1) (lK R1) P1) (.inl 0) (jp .D) (jp .T)

omit [DecidableEq E1] in
theorem closed_moveJ {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1} (hP1 : P1.Closed) :
    (moveJ P1).Closed :=
  C6BitMoveAux.closed_movePG _ (closed_callInj _ _ hP1) _ _ _

/-- `moveJ`: if the kernel maps `arrSyms v` to `arrSyms w` (counters `N1`, `N2` on `N1`, `N2`),
the array stack ends with `arrSyms w ++ rest`; every other stack is unchanged. -/
theorem runs_moveJ {P1 : Prog (KLoc (Fin 4) E1) (fun _ => Sym) R1} {T1 : ℕ}
    (S : KJ E1 → List Sym) (v w : List (List Bool)) (rest r2 r3 : List Sym) (N1 N2 : ℕ)
    (hK : ∀ S' : KLoc (Fin 4) E1 → List Sym, S' (.inl 0) = arrSyms v ++ rest →
      S' (.inl 2) = natSyms N1 ++ r2 → S' (.inl 3) = natSyms N2 ++ r3 →
      Runs P1 S' (Function.update (Function.update S' (.inl 0) rest) (.inl 1)
        (arrSyms w ++ S' (.inl 1))) (fun _ => True) T1)
    (hS0 : S (.inl 0) = arrSyms v ++ rest) (hN1 : S (jp .N1) = natSyms N1 ++ r2)
    (hN2 : S (jp .N2) = natSyms N2 ++ r3) :
    Runs (moveJ P1) S (Function.update S (.inl 0) (arrSyms w ++ rest)) (fun _ => True)
      (1 + (T1 + (1 + ((3 * (arrSyms w).length + 2) + (3 * (arrSyms w).reverse.length + 2))))) := by
  have h0D : (Sum.inl 0 : KJ E1) ≠ jp .D := inl_ne_jp _ _
  have h0T : (Sum.inl 0 : KJ E1) ≠ jp .T := inl_ne_jp _ _
  have hDT : (jp .D : KJ E1) ≠ jp .T := by simp
  have h1D : (jp .N1 : KJ E1) ≠ jp .D := by simp
  have h2D : (jp .N2 : KJ E1) ≠ jp .D := by simp
  refine C6BitMoveAux.runs_movePG (lWJ R1) h0D h0T hDT S (arrSyms w) rest
    (C6BitMoveAux.mark_not_mem_arrSyms w) ?_
  exact C6BitMoveAux.runs_inj_upd2 (ιK_inj E1) (lK R1) _ (.inl 0) (.inl 1) rest _
    (hK _ (by change Function.update S (jp .D) _ (.inl 0) = _
              rw [Function.update_of_ne h0D]; exact hS0)
      (by change Function.update S (jp .D) _ (jp .N1) = _
          rw [Function.update_of_ne h1D]; exact hN1)
      (by change Function.update S (jp .D) _ (jp .N2) = _
          rw [Function.update_of_ne h2D]; exact hN2))

/-- The threshold kernel inside the joining layout: `natSyms (c6T q e)` is pushed on `tS`. -/
theorem runs_callT {q : ℕ} (hq : 2 ≤ q) (e : ℕ) (r1 : List Sym) (S : KJ E1 → List Sym)
    (hr1 : TermOK r1) (hS1 : S (.inl 1) = natSyms e ++ r1) :
    Runs (callInj (ιT E1) (lN R1) (tKerP q)) S
      (Function.update S (jp .tS) (natSyms (c6T q e) ++ S (jp .tS))) (fun _ => True)
      (tCost q e) :=
  C6BitMoveAux.runs_inj_upd1 (ιT_inj E1) (lN R1) S (.inl 1) _
    (runs_tKerP hq e r1 (S ∘ ιT E1) hr1 hS1)

end Move

/-! ## Counter helpers -/

section Arith

variable {K : Type} [DecidableEq K]

/-- `Y := a·q^n` above a fresh `mark` (`a` copied from `src`, `n` read from `ns`). -/
def mkPow (q : ℕ) (src Y ns Kc2 Tm Q Td A Bs Acc : K) : Prog K (fun _ => Sym) NatArith.Reg :=
  .seq (pushMark Y) (.seq (copyN src Y Q) (powMulN Y q ns Kc2 Tm Q Td A Bs Acc))

omit [DecidableEq K] in
theorem closed_mkPow (q : ℕ) (src Y ns Kc2 Tm Q Td A Bs Acc : K) :
    (mkPow q src Y ns Kc2 Tm Q Td A Bs Acc).Closed :=
  ⟨closed_pushMark _, closed_copyN _ _ _, closed_powMulN _ _ _ _ _ _ _ _ _ _⟩

theorem runs_mkPow {src Y ns Kc2 Tm Q Td A Bs Acc : K}
    (hnd : [Y, ns, Kc2, Tm, Q, Td, A, Bs, Acc].Nodup) (hsY : src ≠ Y) (hsQ : src ≠ Q)
    {q : ℕ} (hq : 1 ≤ q) (a n : ℕ) (ra rn : List Sym) (S : K → List Sym) (hra : TermOK ra)
    (hrn : TermOK rn) (hsrc : S src = natSyms a ++ ra) (hns : S ns = natSyms n ++ rn) :
    Runs (mkPow q src Y ns Kc2 Tm Q Td A Bs Acc) S
      (Function.update S Y (natSyms (a * q ^ n) ++ Sym.mark :: S Y)) (fun _ => True)
      (1 + ((7 * bitLen a + 7) + powCost q a n)) := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hYn, -, -, hYQ, -, -, -, -⟩, -⟩ := hnd'
  have r1 := runs_pushMark Y S
  have r2 := runs_copyN hsY hsQ hYQ a ra (Function.update S Y (Sym.mark :: S Y)) hra
    (by rw [Function.update_of_ne hsY]; exact hsrc)
  rw [Function.update_self, Function.update_idem] at r2
  have r3 := runs_powMulN hnd q hq a n (Sym.mark :: S Y) rn
    (Function.update S Y (natSyms a ++ Sym.mark :: S Y)) (termOK_mark _) hrn
    (Function.update_self _ _ _) (by rw [Function.update_of_ne (Ne.symm hYn)]; exact hns)
  rw [Function.update_idem] at r3
  exact WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 r3)

/-- `z := a - b` above a fresh `mark` (`a` on `x`, `b` on `y`). -/
def mkSub (x y z t1 t2 t3 : K) : Prog K (fun _ => Sym) NatArith.Reg :=
  .seq (pushMark z) (subN x y z t1 t2 t3)

omit [DecidableEq K] in
theorem closed_mkSub (x y z t1 t2 t3 : K) : (mkSub x y z t1 t2 t3).Closed :=
  ⟨closed_pushMark _, closed_subN _ _ _ _ _ _⟩

theorem runs_mkSub {x y z t1 t2 t3 : K} (h : [x, y, z, t1, t2, t3].Nodup) (a b : ℕ)
    (rx ry : List Sym) (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hab : b ≤ a)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) :
    Runs (mkSub x y z t1 t2 t3) S (Function.update S z (natSyms (a - b) ++ Sym.mark :: S z))
      (fun _ => True) (1 + 20 * (bitLen a + bitLen b + 1)) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h'
  obtain ⟨⟨-, hxz, -, -, -⟩, ⟨hyz, -, -, -⟩, -⟩ := h'
  have r1 := runs_pushMark z S
  have r2 := runs_subN h a b rx ry (Function.update S z (Sym.mark :: S z)) hrx hry hab
    (by rw [Function.update_of_ne hxz]; exact hx) (by rw [Function.update_of_ne hyz]; exact hy)
  rw [Function.update_self, Function.update_idem] at r2
  exact WP.W9comp.runs_seq r1 r2

end Arith

/-! ## The cost budget `Λ = q^(2e)·G·B` -/

theorem bitLen_eq_size (x : ℕ) : bitLen x = Nat.size x := by
  rw [bitLen, IntMulTM.length_encodeNat]

theorem sq_le_two_pow' : ∀ k : ℕ, (k + 1) ^ 2 ≤ 2 ^ (k + 2)
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | k + 3 => by
    have ih := sq_le_two_pow' (k + 2)
    have e1 : 2 ^ (k + 3 + 2) = 2 * 2 ^ (k + 2 + 2) := by ring
    have h2 : (k + 3 + 1) ^ 2 ≤ 2 * (k + 2 + 1) ^ 2 :=
      Nat.le.intro (show (k + 3 + 1) ^ 2 + (k ^ 2 + 4 * k + 2) = 2 * (k + 2 + 1) ^ 2 by ring)
    rw [e1]
    exact h2.trans (Nat.mul_le_mul_left 2 ih)

theorem cube_le_four_pow : ∀ e : ℕ, (e + 1) ^ 3 ≤ 8 * 4 ^ e
  | 0 => by norm_num
  | 1 => by norm_num
  | e + 2 => by
    have ih := cube_le_four_pow (e + 1)
    have e1 : 4 ^ (e + 2) = 4 * 4 ^ (e + 1) := by ring
    rw [e1]
    nlinarith [ih, Nat.zero_le (e ^ 3), Nat.zero_le (e ^ 2)]

theorem sq_bitLen_succ_le {x : ℕ} (hx : 1 ≤ x) : (bitLen x + 1) ^ 2 ≤ 8 * x := by
  rw [bitLen_eq_size]
  have hs : 1 ≤ Nat.size x := Nat.size_pos.2 hx
  have hlow : 2 ^ (Nat.size x - 1) ≤ x := by
    by_contra h
    have := Nat.size_le.2 (not_le.1 h)
    omega
  have h1 := sq_le_two_pow' (Nat.size x)
  have h2 : 2 ^ (Nat.size x + 2) = 8 * 2 ^ (Nat.size x - 1) := by
    rw [show Nat.size x + 2 = (Nat.size x - 1) + 3 by omega, pow_add]
    ring
  calc (Nat.size x + 1) ^ 2 ≤ 2 ^ (Nat.size x + 2) := h1
    _ = 8 * 2 ^ (Nat.size x - 1) := h2
    _ ≤ 8 * x := Nat.mul_le_mul_left 8 hlow

theorem four_pow_le {q : ℕ} (hq : 2 ≤ q) (e : ℕ) : 4 ^ e ≤ q ^ (2 * e) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by nlinarith) e

/-- **The cost budget.** For `n ≤ e` and `L ≤ 2e·|q| + |G| + |B| + c`:
`(n + 1)·L² ≤ 512·(2|q| + c + 1)²·q^(2e)·G·B`. -/
theorem master_le {q e G B n L c : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) (hn : n ≤ e)
    (hL : L ≤ 2 * e * bitLen q + bitLen G + bitLen B + c) :
    (n + 1) * L ^ 2 ≤ 512 * (2 * bitLen q + c + 1) ^ 2 * (q ^ (2 * e) * G * B) := by
  obtain ⟨a, ha⟩ : ∃ a, a = 2 * e * bitLen q + c := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = bitLen G := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = bitLen B := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = 2 * bitLen q + c + 1 := ⟨_, rfl⟩
  have hLa : L ≤ a + g + b := by omega
  have h1 : L ≤ (a + 1) * (g + 1) * (b + 1) := by
    have e1 : (a + 1) * (g + 1) * (b + 1) =
        a * g * b + a * g + a * b + g * b + a + g + b + 1 := by ring
    omega
  have h2 : L ^ 2 ≤ (a + 1) ^ 2 * (g + 1) ^ 2 * (b + 1) ^ 2 := by
    calc L ^ 2 ≤ ((a + 1) * (g + 1) * (b + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = (a + 1) ^ 2 * (g + 1) ^ 2 * (b + 1) ^ 2 := by ring
  have h3 : a + 1 ≤ k * (e + 1) := by
    have e1 : k * (e + 1) = 2 * e * bitLen q + 2 * bitLen q + c * e + c + e + 1 := by
      rw [hk]; ring
    omega
  have h4 : (n + 1) * (a + 1) ^ 2 ≤ k ^ 2 * (e + 1) ^ 3 :=
    calc (n + 1) * (a + 1) ^ 2 ≤ (e + 1) * (k * (e + 1)) ^ 2 :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left h3 2)
      _ = k ^ 2 * (e + 1) ^ 3 := by ring
  have h5 : (e + 1) ^ 3 ≤ 8 * q ^ (2 * e) :=
    (cube_le_four_pow e).trans (Nat.mul_le_mul_left 8 (four_pow_le hq e))
  have hgG : (g + 1) ^ 2 ≤ 8 * G := by rw [hg]; exact sq_bitLen_succ_le hG
  have hbB : (b + 1) ^ 2 ≤ 8 * B := by rw [hb]; exact sq_bitLen_succ_le hB
  calc (n + 1) * L ^ 2 ≤ (n + 1) * ((a + 1) ^ 2 * (g + 1) ^ 2 * (b + 1) ^ 2) :=
        Nat.mul_le_mul_left _ h2
    _ = (n + 1) * (a + 1) ^ 2 * (g + 1) ^ 2 * (b + 1) ^ 2 := by ring
    _ ≤ (k ^ 2 * (8 * q ^ (2 * e))) * (8 * G) * (8 * B) :=
        Nat.mul_le_mul (Nat.mul_le_mul (h4.trans (Nat.mul_le_mul_left _ h5)) hgG) hbB
    _ = 512 * (2 * bitLen q + c + 1) ^ 2 * (q ^ (2 * e) * G * B) := by rw [hk]; ring

/-- `e + 1 ≤ Λ`-type bound: `e + 1 ≤ q^(2e)·G·B`. -/
theorem succ_le_budget {q e G B : ℕ} (hq : 2 ≤ q) (hG : 1 ≤ G) (hB : 1 ≤ B) :
    e + 1 ≤ q ^ (2 * e) * G * B := by
  have h1 : e + 1 ≤ 2 ^ e := Nat.lt_two_pow_self
  have h2 : 2 ^ e ≤ 4 ^ e := Nat.pow_le_pow_left (by norm_num) e
  have h3 := four_pow_le hq e
  have h4 : q ^ (2 * e) ≤ q ^ (2 * e) * G * B := by
    calc q ^ (2 * e) = q ^ (2 * e) * 1 * 1 := by ring
      _ ≤ q ^ (2 * e) * G * B := Nat.mul_le_mul (Nat.mul_le_mul_left _ hG) hB
  omega

end AppC.C6JoinAux

end SubNLogN.Machine
