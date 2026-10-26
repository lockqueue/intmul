/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7RepairDefs
import SubNLogN.Machine.K1.LongRecordBase
import WP.W3.Basic
import WP.W3s.Math
import IntMulTM.Framework.Lib.CompareEval

/-!
# Lemma A.9 extraction, part 1: arithmetic kit and in-place number routines
(`Machine/AppC/C7ExtractKit.lean`)

Support file for `C7ExtractStmt` (`Machine/AppC/C7RepairDefs.lean`;
Lemma A.9 (`lem:transfer13`)). The extraction kernel works with natural numbers in
the canonical `natSyms` encoding (LSB on top) on private scratch stacks whose initial content is
arbitrary (restored convention). Every number lives above a *floor* (a `mark`), so that `TermOK`
holds below it.

* `XKit K`: an **arithmetic kit** over stacks `K`: a finite register type `R` with a one-symbol
  work register (`lw`) and a comparison observation (`obs`), and closed programs for
  `z += a + b`, `z += a - b`, `z += a * b`, a comparison, and `q += a / b, r += a % b`, each with an
  exact `Runs` specification (all other stacks unchanged, temporaries restored, arbitrary content
  allowed on them) and one uniform cost constant `c`. The kit is instantiated at the end of the
  development (`C7ExtractInst.lean`) from the shared `NatArith` library and the W3/W6a programs.
* Lifted one-symbol pieces (`pushW`, `popW`, `peekW`, `skipW`) and the stream library calls
  `copyW` (`Lib.copyBlock`), `dropW` (`WP.W3.dropNum`), `dropFW` (`K1.dropBits`).
* **In-place routines** with a temporary floor: `addTo` (`k := k + b`), `subFrom` (`k := k - b`),
  `mulBy` (`k := k * b`), `divBy` (`k := k / b`), `modBy` (`k := k % b`), each with an exact
  `Runs` fact and the uniform cost bound `opCost xk n` when all numbers involved have at most `n`
  bits.

Everything here is proved (no `sorry`); nothing depends on the Lemma A.9 data. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine.AppC.C7ExtractAux

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## The arithmetic kit -/

/-- **Arithmetic kit** over the stacks `K`: programs with exact `Runs` specifications. Operands
are `natSyms` blocks above `TermOK` tails and are restored; results are pushed on the destination's
old content; the listed temporaries may hold anything and are restored. -/
structure XKit (K : Type) [DecidableEq K] : Type 1 where
  /-- Register type. -/
  R : Type
  finR : Finite R
  neR : Nonempty R
  /-- The one-symbol work register. -/
  lw : Lens R (Option Sym)
  /-- The comparison observation. -/
  obs : R → Ordering
  /-- Uniform cost constant. -/
  c : ℕ
  /-- `z += a + b` (operands `x, y`; temporaries `t1 t2 t3`). -/
  add : K → K → K → K → K → K → Prog K (fun _ => Sym) R
  /-- `z += a - b` for `b ≤ a`. -/
  sub : K → K → K → K → K → K → Prog K (fun _ => Sym) R
  /-- `z += a * b` (temporaries `A Bs Acc T`). -/
  mul : K → K → K → K → K → K → K → Prog K (fun _ => Sym) R
  /-- Compare `a` and `b` (temporaries `t1 t2`); the result is `obs`. -/
  cmp : K → K → K → K → Prog K (fun _ => Sym) R
  /-- `q += a / b`, `r += a % b` for `0 < b` (temporaries `d0 d1 d2`). -/
  dm : K → K → K → K → K → K → K → Prog K (fun _ => Sym) R
  add_closed : ∀ x y z t1 t2 t3, (add x y z t1 t2 t3).Closed
  sub_closed : ∀ x y z t1 t2 t3, (sub x y z t1 t2 t3).Closed
  mul_closed : ∀ x y z A Bs Acc T, (mul x y z A Bs Acc T).Closed
  cmp_closed : ∀ x y t1 t2, (cmp x y t1 t2).Closed
  dm_closed : ∀ x y q r d0 d1 d2, (dm x y q r d0 d1 d2).Closed
  add_spec : ∀ {x y z t1 t2 t3 : K}, [x, y, z, t1, t2, t3].Nodup → ∀ (a b : ℕ)
    (rx ry : List Sym) (S : K → List Sym), TermOK rx → TermOK ry → S x = natSyms a ++ rx →
    S y = natSyms b ++ ry →
    Runs (add x y z t1 t2 t3) S (Function.update S z (natSyms (a + b) ++ S z)) (fun _ => True)
      (c * (bitLen a + bitLen b + 1))
  sub_spec : ∀ {x y z t1 t2 t3 : K}, [x, y, z, t1, t2, t3].Nodup → ∀ (a b : ℕ)
    (rx ry : List Sym) (S : K → List Sym), TermOK rx → TermOK ry → b ≤ a →
    S x = natSyms a ++ rx → S y = natSyms b ++ ry →
    Runs (sub x y z t1 t2 t3) S (Function.update S z (natSyms (a - b) ++ S z)) (fun _ => True)
      (c * (bitLen a + bitLen b + 1))
  mul_spec : ∀ {x y z A Bs Acc T : K}, [x, y, z, A, Bs, Acc, T].Nodup → ∀ (a b : ℕ)
    (rx ry : List Sym) (S : K → List Sym), TermOK rx → TermOK ry → S x = natSyms a ++ rx →
    S y = natSyms b ++ ry →
    Runs (mul x y z A Bs Acc T) S (Function.update S z (natSyms (a * b) ++ S z))
      (fun _ => True) (c * ((bitLen a + 1) * (bitLen a + bitLen b + 2)))
  cmp_spec : ∀ {x y t1 t2 : K}, [x, y, t1, t2].Nodup → ∀ (a b : ℕ) (rx ry : List Sym)
    (S : K → List Sym), TermOK rx → TermOK ry → S x = natSyms a ++ rx → S y = natSyms b ++ ry →
    Runs (cmp x y t1 t2) S S (fun v => obs v = Lib.ordOf a b) (c * (bitLen a + bitLen b + 1))
  dm_spec : ∀ {x y q r d0 d1 d2 : K}, [x, y, q, r, d0, d1, d2].Nodup → ∀ (a b : ℕ)
    (rx ry : List Sym) (S : K → List Sym), 0 < b → TermOK rx → TermOK ry →
    S x = natSyms a ++ rx → S y = natSyms b ++ ry →
    Runs (dm x y q r d0 d1 d2) S
      (Function.update (Function.update S q (natSyms (a / b) ++ S q)) r
        (natSyms (a % b) ++ S r))
      (fun _ => True) (c * (bitLen a * bitLen b + bitLen a + bitLen b + 1))

/-! ## Lifted one-symbol pieces and stream calls -/

section Prims

variable {K : Type} [DecidableEq K] (xk : XKit K)

/-- Push the constant `s` on `k`. -/
def pushW (k : K) (s : Sym) : Prog K (fun _ => Sym) xk.R := (pushC k s).liftRegs xk.lw
/-- Pop the top of `k` into the work register. -/
def popW (k : K) : Prog K (fun _ => Sym) xk.R := (popR k).liftRegs xk.lw
/-- Peek the top of `k` into the work register. -/
def peekW (k : K) : Prog K (fun _ => Sym) xk.R := (peekR k).liftRegs xk.lw
/-- Do nothing (one step). -/
def skipW : Prog K (fun _ => Sym) xk.R := .load id
/-- Copy the bit block on top of `src` onto `dst` (`tmp` restored). -/
def copyW (src dst tmp : K) : Prog K (fun _ => Sym) xk.R :=
  (copyBlock src dst tmp).liftRegs xk.lw
/-- Pop the number on top of `k`, keeping its terminator. -/
def dropW (k : K) : Prog K (fun _ => Sym) xk.R := (WP.W3.dropNum k).liftRegs xk.lw
/-- Pop the number on top of `k` together with the non-bit symbol (floor) below it. -/
def dropFW (k : K) : Prog K (fun _ => Sym) xk.R :=
  (SubNLogN.Machine.K1.dropBits k).liftRegs xk.lw

theorem closed_pushW (k : K) (s : Sym) : (pushW xk k s).Closed :=
  WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, pushC])
theorem closed_popW (k : K) : (popW xk k).Closed :=
  WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, popR])
theorem closed_peekW (k : K) : (peekW xk k).Closed :=
  WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, peekR])
theorem closed_skipW : (skipW xk : Prog K (fun _ => Sym) xk.R).Closed := by
  simp [skipW, Prog.Closed, Prog.FreeBelow]
theorem closed_copyW (src dst tmp : K) : (copyW xk src dst tmp).Closed :=
  WP.W9comp.closed_liftRegs _ (WP.W3.closed_of_noRec rfl)
theorem closed_dropW (k : K) : (dropW xk k).Closed :=
  WP.W9comp.closed_liftRegs _ (WP.W3.closed_of_noRec rfl)
theorem closed_dropFW (k : K) : (dropFW xk k).Closed :=
  WP.W9comp.closed_liftRegs _ (WP.W3.closed_of_noRec rfl)

theorem runs_pushW (k : K) (s : Sym) (S : K → List Sym) :
    Runs (pushW xk k s) S (Function.update S k (s :: S k)) (fun _ => True) 1 :=
  SubNLogN.Machine.K1.runs_wk_pushC xk.lw k s S

theorem runs_popW (k : K) (S : K → List Sym) :
    Runs (popW xk k) S (Function.update S k (S k).tail) (fun _ => True) 1 :=
  SubNLogN.Machine.K1.runs_wk_popR xk.lw k S

theorem runs_popW_cons (k : K) (S : K → List Sym) (a : Sym) (l : List Sym) (hS : S k = a :: l) :
    Runs (popW xk k) S (Function.update S k l) (fun _ => True) 1 := by
  have h := runs_popW xk k S
  rw [hS, List.tail_cons] at h
  exact h

/-- The peek, with its register postcondition (`RunsIn []` form, for `ite`). -/
theorem runsIn_peekW (k : K) (S : K → List Sym) :
    SubNLogN.Machine.Calculus.RunsIn [] (peekW xk k) S S (fun v => xk.lw.get v = (S k).head?) 1 :=
  SubNLogN.Machine.K1.triple_peek_lens xk.lw k S

theorem runs_skipW (S : K → List Sym) :
    Runs (skipW xk : Prog K (fun _ => Sym) xk.R) S S (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, Eval.load [] id v S, trivial, le_rfl⟩

theorem runs_copyW {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (a : ℕ) (rx : List Sym) (S : K → List Sym) (hrx : TermOK rx)
    (hS : S src = natSyms a ++ rx) :
    Runs (copyW xk src dst tmp) S (Function.update S dst (natSyms a ++ S dst)) (fun _ => True)
      (7 * bitLen a + 7) :=
  SubNLogN.Machine.K1.runs_liftRegs_of_eval xk.lw fun v =>
    ⟨some .mark, _, copyBlock_eval hsd hst hdt [] v (encodeNat a) rx S hrx hS, le_rfl⟩

theorem runs_dropW (k : K) (a : ℕ) (rx : List Sym) (S : K → List Sym) (hrx : TermOK rx)
    (hS : S k = natSyms a ++ rx) :
    Runs (dropW xk k) S (Function.update S k rx) (fun _ => True) (2 * bitLen a + 4) :=
  SubNLogN.Machine.K1.runs_liftRegs_of_eval xk.lw fun v =>
    ⟨_, _, WP.W3.dropNum_eval [] v (encodeNat a) rx S hrx hS, le_rfl⟩

theorem runs_dropFW (k : K) (a : ℕ) (t : Sym) (rest : List Sym) (S : K → List Sym)
    (ht : t.isBit = false) (hS : S k = natSyms a ++ t :: rest) :
    Runs (dropFW xk k) S (Function.update S k rest) (fun _ => True) (2 * bitLen a + 2) :=
  SubNLogN.Machine.K1.runs_wk_dropBits xk.lw k (encodeNat a) t rest S ht hS

end Prims

theorem termOK_mark (L : List Sym) : TermOK (Sym.mark :: L) := TermOK.cons rfl _

/-! ## In-place routines -/

section InPlace

variable {K : Type} [DecidableEq K] (xk : XKit K)

/-- Uniform cost bound of one in-place routine on numbers of at most `n` bits. -/
def opCost (n : ℕ) : ℕ := (2 * xk.c + 40) * (n + 1) ^ 2

theorem le_opCost (n A : ℕ) (h : A ≤ 2 * xk.c * (n + 1) ^ 2 + 40 * (n + 1)) :
    A ≤ opCost xk n := by
  unfold opCost
  have : 40 * (n + 1) ≤ 40 * (n + 1) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
  nlinarith

theorem c_lin_le (n a b : ℕ) (ha : a ≤ n) (hb : b ≤ n) :
    xk.c * (a + b + 1) ≤ 2 * xk.c * (n + 1) ^ 2 := by
  have h1 : a + b + 1 ≤ 2 * (n + 1) ^ 2 := by nlinarith
  calc xk.c * (a + b + 1) ≤ xk.c * (2 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ h1
    _ = 2 * xk.c * (n + 1) ^ 2 := by ring

theorem c_mul_le (n a b : ℕ) (ha : a ≤ n) (hb : b ≤ n) :
    xk.c * ((a + 1) * (a + b + 2)) ≤ 2 * xk.c * (n + 1) ^ 2 := by
  have h1 : (a + 1) * (a + b + 2) ≤ 2 * (n + 1) ^ 2 := by nlinarith
  calc xk.c * ((a + 1) * (a + b + 2)) ≤ xk.c * (2 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ h1
    _ = 2 * xk.c * (n + 1) ^ 2 := by ring

theorem c_dm_le (n a b : ℕ) (ha : a ≤ n) (hb : b ≤ n) :
    xk.c * (a * b + a + b + 1) ≤ 2 * xk.c * (n + 1) ^ 2 := by
  have h1 : a * b + a + b + 1 ≤ 2 * (n + 1) ^ 2 := by nlinarith
  calc xk.c * (a * b + a + b + 1) ≤ xk.c * (2 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ h1
    _ = 2 * xk.c * (n + 1) ^ 2 := by ring

/-- `k := k + b` (floor and result on `t`; temporaries `t1 t2 t3`). -/
def addTo (k b t t1 t2 t3 : K) : Prog K (fun _ => Sym) xk.R :=
  .seq (pushW xk t .mark) (.seq (xk.add k b t t1 t2 t3) (.seq (dropW xk k)
    (.seq (copyW xk t k t1) (dropFW xk t))))

/-- `k := k - b` for `b ≤ k`. -/
def subFrom (k b t t1 t2 t3 : K) : Prog K (fun _ => Sym) xk.R :=
  .seq (pushW xk t .mark) (.seq (xk.sub k b t t1 t2 t3) (.seq (dropW xk k)
    (.seq (copyW xk t k t1) (dropFW xk t))))

/-- `k := k * b` (temporaries `A Bs Acc T`). -/
def mulBy (k b t A Bs Acc T : K) : Prog K (fun _ => Sym) xk.R :=
  .seq (pushW xk t .mark) (.seq (xk.mul k b t A Bs Acc T) (.seq (dropW xk k)
    (.seq (copyW xk t k A) (dropFW xk t))))

/-- `k := k / b` (quotient on `t`, remainder on `j`, both floored; temporaries `d0 d1 d2`). -/
def divBy (k b t j d0 d1 d2 : K) : Prog K (fun _ => Sym) xk.R :=
  .seq (pushW xk t .mark) (.seq (pushW xk j .mark) (.seq (xk.dm k b t j d0 d1 d2)
    (.seq (dropFW xk j) (.seq (dropW xk k) (.seq (copyW xk t k d0) (dropFW xk t))))))

/-- `k := k % b`. -/
def modBy (k b t j d0 d1 d2 : K) : Prog K (fun _ => Sym) xk.R :=
  .seq (pushW xk t .mark) (.seq (pushW xk j .mark) (.seq (xk.dm k b t j d0 d1 d2)
    (.seq (dropFW xk t) (.seq (dropW xk k) (.seq (copyW xk j k d0) (dropFW xk j))))))

theorem closed_addTo (k b t t1 t2 t3 : K) : (addTo xk k b t t1 t2 t3).Closed :=
  ⟨closed_pushW xk _ _, xk.add_closed _ _ _ _ _ _, closed_dropW xk _, closed_copyW xk _ _ _,
    closed_dropFW xk _⟩
theorem closed_subFrom (k b t t1 t2 t3 : K) : (subFrom xk k b t t1 t2 t3).Closed :=
  ⟨closed_pushW xk _ _, xk.sub_closed _ _ _ _ _ _, closed_dropW xk _, closed_copyW xk _ _ _,
    closed_dropFW xk _⟩
theorem closed_mulBy (k b t A Bs Acc T : K) : (mulBy xk k b t A Bs Acc T).Closed :=
  ⟨closed_pushW xk _ _, xk.mul_closed _ _ _ _ _ _ _, closed_dropW xk _, closed_copyW xk _ _ _,
    closed_dropFW xk _⟩
theorem closed_divBy (k b t j d0 d1 d2 : K) : (divBy xk k b t j d0 d1 d2).Closed :=
  ⟨closed_pushW xk _ _, closed_pushW xk _ _, xk.dm_closed _ _ _ _ _ _ _, closed_dropFW xk _,
    closed_dropW xk _, closed_copyW xk _ _ _, closed_dropFW xk _⟩
theorem closed_modBy (k b t j d0 d1 d2 : K) : (modBy xk k b t j d0 d1 d2).Closed :=
  ⟨closed_pushW xk _ _, closed_pushW xk _ _, xk.dm_closed _ _ _ _ _ _ _, closed_dropFW xk _,
    closed_dropW xk _, closed_copyW xk _ _ _, closed_dropFW xk _⟩

theorem runs_addTo {k b t t1 t2 t3 : K} (h : [k, b, t, t1, t2, t3].Nodup) (x y n : ℕ)
    (rk rb : List Sym) (S : K → List Sym) (hrk : TermOK rk) (hrb : TermOK rb)
    (hk : S k = natSyms x ++ rk) (hb : S b = natSyms y ++ rb)
    (hx : bitLen x ≤ n) (hy : bitLen y ≤ n) (hs : bitLen (x + y) ≤ n) :
    Runs (addTo xk k b t t1 t2 t3) S (Function.update S k (natSyms (x + y) ++ rk))
      (fun _ => True) (opCost xk n) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hkb, hkt, hk1, -, -⟩, ⟨hbt, -, -, -⟩, ⟨ht1, -, -⟩, -, -⟩ := h'
  have X := WP.W9comp.runs_seq (runs_pushW xk t .mark S)
    (WP.W9comp.runs_seq (xk.add_spec h x y rk rb _ hrk hrb
      (by simp [Function.update_apply, hkt, hk]) (by simp [Function.update_apply, hbt, hb]))
    (WP.W9comp.runs_seq (runs_dropW xk k x rk _ hrk (by simp [Function.update_apply, hkt, hk]))
    (WP.W9comp.runs_seq (runs_copyW xk (Ne.symm hkt) ht1 hk1 (x + y) (Sym.mark :: S t) _
      (termOK_mark _) (by simp [Function.update_apply, Ne.symm hkt]))
      (runs_dropFW xk t (x + y) .mark (S t) _ rfl
        (by simp [Function.update_apply, Ne.symm hkt])))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext j
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · have e1 := c_lin_le xk n _ _ hx hy
    refine le_opCost xk n _ ?_
    linarith

theorem runs_subFrom {k b t t1 t2 t3 : K} (h : [k, b, t, t1, t2, t3].Nodup) (x y n : ℕ)
    (rk rb : List Sym) (S : K → List Sym) (hrk : TermOK rk) (hrb : TermOK rb) (hyx : y ≤ x)
    (hk : S k = natSyms x ++ rk) (hb : S b = natSyms y ++ rb)
    (hx : bitLen x ≤ n) (hy : bitLen y ≤ n) :
    Runs (subFrom xk k b t t1 t2 t3) S (Function.update S k (natSyms (x - y) ++ rk))
      (fun _ => True) (opCost xk n) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hkb, hkt, hk1, -, -⟩, ⟨hbt, -, -, -⟩, ⟨ht1, -, -⟩, -, -⟩ := h'
  have hs : bitLen (x - y) ≤ n := le_trans (TMFw.W3s.bitLen_mono (Nat.sub_le x y)) hx
  have X := WP.W9comp.runs_seq (runs_pushW xk t .mark S)
    (WP.W9comp.runs_seq (xk.sub_spec h x y rk rb _ hrk hrb hyx
      (by simp [Function.update_apply, hkt, hk]) (by simp [Function.update_apply, hbt, hb]))
    (WP.W9comp.runs_seq (runs_dropW xk k x rk _ hrk (by simp [Function.update_apply, hkt, hk]))
    (WP.W9comp.runs_seq (runs_copyW xk (Ne.symm hkt) ht1 hk1 (x - y) (Sym.mark :: S t) _
      (termOK_mark _) (by simp [Function.update_apply, Ne.symm hkt]))
      (runs_dropFW xk t (x - y) .mark (S t) _ rfl
        (by simp [Function.update_apply, Ne.symm hkt])))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext j
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · have e1 := c_lin_le xk n _ _ hx hy
    refine le_opCost xk n _ ?_
    linarith

theorem runs_mulBy {k b t A Bs Acc T : K} (h : [k, b, t, A, Bs, Acc, T].Nodup) (x y n : ℕ)
    (rk rb : List Sym) (S : K → List Sym) (hrk : TermOK rk) (hrb : TermOK rb)
    (hk : S k = natSyms x ++ rk) (hb : S b = natSyms y ++ rb)
    (hx : bitLen x ≤ n) (hy : bitLen y ≤ n) (hs : bitLen (x * y) ≤ n) :
    Runs (mulBy xk k b t A Bs Acc T) S (Function.update S k (natSyms (x * y) ++ rk))
      (fun _ => True) (opCost xk n) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hkb, hkt, hkA, -, -, -⟩, ⟨hbt, -, -, -, -⟩, ⟨htA, -, -, -⟩, -, -, -⟩ := h'
  have X := WP.W9comp.runs_seq (runs_pushW xk t .mark S)
    (WP.W9comp.runs_seq (xk.mul_spec h x y rk rb _ hrk hrb
      (by simp [Function.update_apply, hkt, hk]) (by simp [Function.update_apply, hbt, hb]))
    (WP.W9comp.runs_seq (runs_dropW xk k x rk _ hrk (by simp [Function.update_apply, hkt, hk]))
    (WP.W9comp.runs_seq (runs_copyW xk (Ne.symm hkt) htA hkA (x * y) (Sym.mark :: S t) _
      (termOK_mark _) (by simp [Function.update_apply, Ne.symm hkt]))
      (runs_dropFW xk t (x * y) .mark (S t) _ rfl
        (by simp [Function.update_apply, Ne.symm hkt])))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext j
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · have e1 := c_mul_le xk n _ _ hx hy
    refine le_opCost xk n _ ?_
    linarith

theorem runs_divBy {k b t j d0 d1 d2 : K} (h : [k, b, t, j, d0, d1, d2].Nodup) (x y n : ℕ)
    (rk rb : List Sym) (S : K → List Sym) (hrk : TermOK rk) (hrb : TermOK rb) (hy0 : 0 < y)
    (hk : S k = natSyms x ++ rk) (hb : S b = natSyms y ++ rb)
    (hx : bitLen x ≤ n) (hy : bitLen y ≤ n) :
    Runs (divBy xk k b t j d0 d1 d2) S (Function.update S k (natSyms (x / y) ++ rk))
      (fun _ => True) (opCost xk n) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hkb, hkt, hkj, hk0, -, -⟩, ⟨hbt, hbj, -, -, -⟩, ⟨htj, ht0, -, -⟩, -, -, -⟩ := h'
  have hq : bitLen (x / y) ≤ n := le_trans (TMFw.W3s.bitLen_mono (Nat.div_le_self x y)) hx
  have hr : bitLen (x % y) ≤ n := le_trans (TMFw.W3s.bitLen_mono (Nat.mod_le x y)) hx
  have X := WP.W9comp.runs_seq (runs_pushW xk t .mark S)
    (WP.W9comp.runs_seq (runs_pushW xk j .mark _)
    (WP.W9comp.runs_seq (xk.dm_spec h x y rk rb _ hy0 hrk hrb
      (by simp [Function.update_apply, hkt, hkj, hk])
      (by simp [Function.update_apply, hbt, hbj, hb]))
    (WP.W9comp.runs_seq (runs_dropFW xk j (x % y) .mark (S j) _ rfl
      (by simp [Function.update_apply, htj, Ne.symm htj]))
    (WP.W9comp.runs_seq (runs_dropW xk k x rk _ hrk
      (by simp [Function.update_apply, hkt, hkj, hk]))
    (WP.W9comp.runs_seq (runs_copyW xk (Ne.symm hkt) ht0 hk0 (x / y) (Sym.mark :: S t) _
      (termOK_mark _) (by simp [Function.update_apply, Ne.symm hkt, htj]))
      (runs_dropFW xk t (x / y) .mark (S t) _ rfl
        (by simp [Function.update_apply, Ne.symm hkt, htj])))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · have e1 := c_dm_le xk n _ _ hx hy
    refine le_opCost xk n _ ?_
    linarith

theorem runs_modBy {k b t j d0 d1 d2 : K} (h : [k, b, t, j, d0, d1, d2].Nodup) (x y n : ℕ)
    (rk rb : List Sym) (S : K → List Sym) (hrk : TermOK rk) (hrb : TermOK rb) (hy0 : 0 < y)
    (hk : S k = natSyms x ++ rk) (hb : S b = natSyms y ++ rb)
    (hx : bitLen x ≤ n) (hy : bitLen y ≤ n) :
    Runs (modBy xk k b t j d0 d1 d2) S (Function.update S k (natSyms (x % y) ++ rk))
      (fun _ => True) (opCost xk n) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hkb, hkt, hkj, hk0, -, -⟩, ⟨hbt, hbj, -, -, -⟩, ⟨htj, -, -, -⟩, ⟨hj0, -, -⟩, -, -⟩ := h'
  have hq : bitLen (x / y) ≤ n := le_trans (TMFw.W3s.bitLen_mono (Nat.div_le_self x y)) hx
  have hr : bitLen (x % y) ≤ n := le_trans (TMFw.W3s.bitLen_mono (Nat.mod_le x y)) hx
  have X := WP.W9comp.runs_seq (runs_pushW xk t .mark S)
    (WP.W9comp.runs_seq (runs_pushW xk j .mark _)
    (WP.W9comp.runs_seq (xk.dm_spec h x y rk rb _ hy0 hrk hrb
      (by simp [Function.update_apply, hkt, hkj, hk])
      (by simp [Function.update_apply, hbt, hbj, hb]))
    (WP.W9comp.runs_seq (runs_dropFW xk t (x / y) .mark (S t) _ rfl
      (by simp [Function.update_apply, htj, Ne.symm htj]))
    (WP.W9comp.runs_seq (runs_dropW xk k x rk _ hrk
      (by simp [Function.update_apply, hkt, hkj, hk]))
    (WP.W9comp.runs_seq (runs_copyW xk (Ne.symm hkj) hj0 hk0 (x % y) (Sym.mark :: S j) _
      (termOK_mark _) (by simp [Function.update_apply, Ne.symm hkj, Ne.symm htj]))
      (runs_dropFW xk j (x % y) .mark (S j) _ rfl
        (by simp [Function.update_apply, Ne.symm hkj, Ne.symm htj])))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · have e1 := c_dm_le xk n _ _ hx hy
    refine le_opCost xk n _ ?_
    linarith

end InPlace

end SubNLogN.Machine.AppC.C7ExtractAux
