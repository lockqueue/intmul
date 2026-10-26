/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.Div
import SubNLogN.Math.Bridge.IntForms.Solver

/-!
# K6 (`Machine/Tables/Pow.lean`): the bit loop and truncated binary powering

**Scope (honest summary).** Infrastructure and one pure lemma:
* `bitLoop`: pop the bits of a list (most significant first in our use) one by one and run one of
  two bodies per bit (`HT.bitLoop_spec`);
* `powFoldN_eq`: square-and-multiply over the bits of `L`, most significant first, starting from
  `2^Q`, with a truncation (floor division by `2^Q`, resp. `2^p`) after every product, is
  `powTruncInt Q p a L` (`SubNLogN/Math/Bridge/IntForms/Solver.lean`; Lemma 4.6 (`lem:bridge-C`)
  (bridge Lemma C)(v)) for a natural base `a`. Each square is computed once.
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Common.GridInt
  SubNLogN.Math.Bridge.IntForms

/-! ## Truncated powering over the bits -/

/-- One step: square and truncate by `2^Q`, then (bit `1`) multiply by `a` and truncate by `2^p`. -/
def powStepN (Q p a : ℕ) (b : Bool) (X : ℕ) : ℕ :=
  if b then X * X / 2 ^ Q * a / 2 ^ p else X * X / 2 ^ Q

/-- Fold of `powStepN` over a bit list. -/
def powFoldN (Q p a : ℕ) (bs : List Bool) (X : ℕ) : ℕ := bs.foldl (fun X b => powStepN Q p a b X) X

theorem tdivShift_natCast (z : ℕ) (s : ℕ) : tdivShift (z : ℤ) s = ((z / 2 ^ s : ℕ) : ℤ) := by
  unfold tdivShift
  rw [Int.tdiv_eq_ediv_of_nonneg (by positivity)]
  push_cast
  rfl

theorem powFoldN_append_single (Q p a : ℕ) (l : List Bool) (b : Bool) (X : ℕ) :
    powFoldN Q p a (l ++ [b]) X = powStepN Q p a b (powFoldN Q p a l X) := by
  simp [powFoldN, List.foldl_append]

theorem powFoldN_eq (Q p a : ℕ) : ∀ L : ℕ,
    ((powFoldN Q p a (Computability.encodeNat L).reverse (2 ^ Q) : ℕ) : ℤ) =
      powTruncInt Q p (a : ℤ) L := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    rw [powTruncInt]
    by_cases h0 : L = 0
    · subst h0
      rw [dif_pos rfl, encodeNat_zero]
      simp [powFoldN]
    · rw [dif_neg h0]
      have hm : L / 2 < L := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by norm_num)
      have ihm := ih (L / 2) hm
      obtain ⟨m, hL | hL⟩ := Nat.even_or_odd' L
      · -- L = 2m, m > 0
        have hm0 : m ≠ 0 := by omega
        have henc : Computability.encodeNat L = false :: Computability.encodeNat m := by
          rw [hL, two_mul, encodeNat_add, if_neg (by rw [encodeNat_eq_nil_iff]; exact hm0)]
        have hdiv : L / 2 = m := by omega
        rw [hdiv] at ihm ⊢
        rw [if_pos (by omega), henc, List.reverse_cons, powFoldN_append_single, ← ihm]
        simp only [powStepN, Bool.false_eq_true, if_false]
        rw [← Int.natCast_mul, tdivShift_natCast]
      · -- L = 2m + 1
        have henc : Computability.encodeNat L = true :: Computability.encodeNat m := by
          rw [hL, two_mul, encodeNat_add_add_one]
        have hdiv : L / 2 = m := by omega
        rw [hdiv] at ihm ⊢
        rw [if_neg (by omega), henc, List.reverse_cons, powFoldN_append_single, ← ihm]
        simp only [powStepN, if_true]
        rw [← Int.natCast_mul, tdivShift_natCast, ← Int.natCast_mul, tdivShift_natCast]

/-! ## The bit loop -/

section BitLoop

variable (I : TB)

/-- Pop the bits of `X` one by one; for each, run `p` (bit `1`) or `q` (bit `0`). -/
def bitLoop (X : TL) (p q : TP I) : TP I :=
  (popR' I.lS X).seq (Prog.loop (fun v => (I.lS.get v).isSome)
    ((Prog.ite (fun v => decide (I.lS.get v = some (Sym.bit true))) p q).seq (popR' I.lS X)))

theorem bitLoop_closed (X : TL) (p q : TP I) (hp : p.Closed) (hq : q.Closed) :
    (bitLoop I X p q).Closed := ⟨trivial, ⟨⟨hp, hq⟩, trivial⟩⟩

variable {I}

theorem HT.bitLoop_spec (X : TL) (bs : List Bool) (St : ℕ → TL → List Sym)
    (hX : ∀ k, k ≤ bs.length → St k X = (bs.drop k).map Sym.bit) (p q : TP I) (cb : ℕ)
    (ρ : List (TP I))
    (hp : ∀ k (h : k < bs.length), bs[k] = true →
      HT ρ (Function.update (St k) X ((bs.drop (k + 1)).map Sym.bit)) p (St (k + 1)) cb)
    (hq : ∀ k (h : k < bs.length), bs[k] = false →
      HT ρ (Function.update (St k) X ((bs.drop (k + 1)).map Sym.bit)) q (St (k + 1)) cb) :
    HT ρ (St 0) (bitLoop I X p q) (St bs.length) (bs.length * (cb + 3) + 2) := by
  unfold HT bitLoop
  set N := bs.length with hN
  -- invariant with `m` iterations remaining
  have hloop := Triple.loop (ρ := ρ) (c := fun v => (I.lS.get v).isSome)
    (p := (Prog.ite (fun v => decide (I.lS.get v = some (Sym.bit true))) p q).seq
      (popR' I.lS X))
    (I := fun m s => m ≤ N ∧ s.stk = Function.update (St (N - m)) X
      ((bs.drop (N - m + 1)).map Sym.bit) ∧ I.lS.get s.var = (bs.map Sym.bit)[N - m]?)
    (B := fun _ => cb + 2) ?_ ?_ ?_ N
  · refine Triple.cost_mono (Triple.seq (R := fun s => N ≤ N ∧ s.stk = Function.update
      (St (N - N)) X ((bs.drop (N - N + 1)).map Sym.bit) ∧
      I.lS.get s.var = (bs.map Sym.bit)[N - N]?) (T₁ := 1)
      (T₂ := loopCost (fun _ => cb + 2) N) ?_ ?_) ?_
    · rintro ⟨v, S⟩ hS
      change S = St 0 at hS
      subst hS
      refine ⟨_, 1, Eval.pop ρ X (fun v o => I.lS.set v o) v (St 0), ⟨le_rfl, ?_, ?_⟩, le_rfl⟩
      · show Function.update (St 0) X (St 0 X).tail = _
        rw [Nat.sub_self, hX 0 (Nat.zero_le _)]
        simp [List.drop_one, List.map_tail]
      · show I.lS.get (I.lS.set v (St 0 X).head?) = _
        rw [I.lS.get_set, Nat.sub_self, hX 0 (Nat.zero_le _)]
        simp [List.head?_map, List.head?_eq_getElem?]
    · refine Triple.conseq hloop (fun s hs => hs) (fun s hs => ?_) le_rfl
      rw [hs.2.1, Nat.sub_zero, List.drop_of_length_le (by omega), List.map_nil]
      exact Function.update_eq_self_iff.mpr (by rw [hX N le_rfl, List.drop_length]; rfl)
    · rw [loopCost_const]
      have : N * (cb + 2 + 1) = N * (cb + 3) := by ring
      omega
  · intro n
    rintro ⟨v, S⟩ ⟨hn, hS, hv⟩
    simp only at hS hv
    subst hS
    have hk : N - (n + 1) < N := by omega
    have hk1 : N - (n + 1) + 1 = N - n := by omega
    have hv' : I.lS.get v = some (Sym.bit bs[N - (n + 1)]) := by
      rw [hv, List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
    have hite : Triple ρ (fun s => s.stk = Function.update (St (N - (n + 1))) X
          ((bs.drop (N - (n + 1) + 1)).map Sym.bit) ∧
          I.lS.get s.var = some (Sym.bit bs[N - (n + 1)]))
        (Prog.ite (fun v => decide (I.lS.get v = some (Sym.bit true))) p q)
        (fun s => s.stk = St (N - (n + 1) + 1)) (cb + 1) := by
      refine Triple.ite ?_ ?_
      · intro s ⟨⟨hs1, hs2⟩, hc⟩
        have hb : bs[N - (n + 1)] = true := by
          rw [hs2] at hc; simpa using hc
        exact hp _ hk hb s hs1
      · intro s ⟨⟨hs1, hs2⟩, hc⟩
        have hb : bs[N - (n + 1)] = false := by
          rw [hs2] at hc; simpa using hc
        exact hq _ hk hb s hs1
    obtain ⟨s1, t1, e1, hs1, ht1⟩ := hite ⟨v, _⟩ ⟨rfl, hv'⟩
    have hX1 : St (N - (n + 1) + 1) X = (bs.drop (N - n)).map Sym.bit := by
      rw [hX _ (by omega), hk1]
    refine ⟨_, t1 + 1, Eval.seq e1 (Eval.pop ρ X (fun v o => I.lS.set v o) s1.var s1.stk),
      ⟨by omega, ?_, ?_⟩, by omega⟩
    · show Function.update s1.stk X (s1.stk X).tail = _
      rw [hs1, hX1, ← hk1]
      congr 1
      rw [← List.map_tail, List.tail_drop, hk1]
    · show I.lS.get (I.lS.set s1.var (s1.stk X).head?) = _
      rw [I.lS.get_set, hs1, hX1, List.head?_map, List.head?_drop, List.getElem?_map]
  · intro n s hs
    obtain ⟨hn, -, hv⟩ := hs
    have hk : N - (n + 1) < N := by omega
    rw [hv, List.getElem?_map, List.getElem?_eq_getElem hk]
    rfl
  · intro s hs
    obtain ⟨-, -, hv⟩ := hs
    rw [hv, Nat.sub_zero, List.getElem?_eq_none (by simp [hN])]
    rfl

end BitLoop

end SubNLogN.Machine.Tables
