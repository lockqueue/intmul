/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostHdr

/-!
# K5-PP composition helpers (`Bridge/PrePostCall.lean`)

* `runs_callInjQ`: `runs_callInj` (`Contracts/Layout.lean`) keeping the component's register
  postcondition through the lens (needed to branch on a comparison result).
* `runs_call0/1/2`: embedded components whose effect is zero, one or two `Function.update`s.
* `runs_seq_ite`: a component that decides a Boolean test, followed by `ite`.
* `locMap`: the stack map of an `MContract` component (`Loc n m`).
* `bitLen` facts: `bitLen_add_le`, `bitLen_le_self'`.

**Scope (honest summary).** Proved, no `sorry`.
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine Computability

section Call

variable {L K σ R : Type} [DecidableEq L] [DecidableEq K]

/-- `runs_callInj` keeping the register postcondition. -/
theorem runs_callInjQ {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) :
    Runs (callInj ι l P) B B' (fun v => Q (l.get v)) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = B at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', hq⟩, ht⟩ := hP ⟨l.get v, stk ∘ ι⟩ rfl
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι stk (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      exact (h1 x).trans (congrFun hs' x)
    · simp only [not_exists] at hk
      rw [h2 _ hk, hout k hk]
  subst hT'
  refine ⟨⟨l.set v s'.var, T'⟩, t, Eval.liftRegs l e' v rfl, ⟨rfl, ?_⟩, ht⟩
  show Q (l.get (l.set v s'.var))
  rw [l.get_set]
  exact hq

theorem runs_call0 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {B : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (B ∘ ι) Q T) :
    Runs (callInj ι l P) B B (fun v => Q (l.get v)) T :=
  runs_callInjQ hι l hP (fun _ _ => rfl)

theorem runs_call1 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {B : K → List Sym} {k : L} {w : List Sym} {Q : R → Prop}
    {T : ℕ} (hP : Runs P (B ∘ ι) (Function.update (B ∘ ι) k w) Q T) :
    Runs (callInj ι l P) B (Function.update B (ι k) w) (fun v => Q (l.get v)) T := by
  refine runs_callInjQ hι l ?_ ?_
  · rw [Function.update_comp_eq_of_injective B hι]
    exact hP
  · intro k' hk'
    rw [Function.update_of_ne (fun h => hk' k h.symm)]

theorem runs_call2 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {B : K → List Sym} {k1 k2 : L} {w1 w2 : List Sym}
    {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (Function.update (Function.update (B ∘ ι) k1 w1) k2 w2) Q T) :
    Runs (callInj ι l P) B (Function.update (Function.update B (ι k1) w1) (ι k2) w2)
      (fun v => Q (l.get v)) T := by
  refine runs_callInjQ hι l ?_ ?_
  · rw [Function.update_comp_eq_of_injective _ hι, Function.update_comp_eq_of_injective B hι]
    exact hP
  · intro k' hk'
    rw [Function.update_of_ne (fun h => hk' k2 h.symm),
      Function.update_of_ne (fun h => hk' k1 h.symm)]

end Call

section Ite

variable {K σ : Type} [DecidableEq K]

/-- A component deciding the Boolean `c = b`, followed by `ite c`. -/
theorem runs_seq_ite {P A A' : Prog K (fun _ => Sym) σ} {c : σ → Bool} {S S1 S2 : K → List Sym}
    {b : Bool} {Q : σ → Prop} {T1 T2 : ℕ} (h1 : Runs P S S1 (fun v => c v = b) T1)
    (hA : b = true → Runs A S1 S2 Q T2) (hA' : b = false → Runs A' S1 S2 Q T2) :
    Runs (.seq P (.ite c A A')) S S2 Q (T1 + (T2 + 1)) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hc⟩, ht1⟩ := h1 s hs
  cases b
  · obtain ⟨s2, t2, e2, hq2, ht2⟩ := hA' rfl s1 hs1
    exact ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_false hc e2), hq2, by omega⟩
  · obtain ⟨s2, t2, e2, hq2, ht2⟩ := hA rfl s1 hs1
    exact ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_true hc e2), hq2, by omega⟩

end Ite

/-- Stack map of an `MContract` component: named stacks by `names`, scratch by `scr`. -/
def locMap {K : Type} {n m : ℕ} (names : Fin n → K) (scr : Fin m → K) : Loc n m → K :=
  Sum.elim names scr

theorem locMap_injective {K : Type} {n m : ℕ} {names : Fin n → K} {scr : Fin m → K}
    (h1 : Function.Injective names) (h2 : Function.Injective scr)
    (h3 : ∀ i j, names i ≠ scr j) : Function.Injective (locMap names scr) := by
  rintro (a | a) (b | b) h <;> simp only [locMap, Sum.elim_inl, Sum.elim_inr] at h
  · rw [h1 h]
  · exact absurd h (h3 a b)
  · exact absurd h.symm (h3 b a)
  · rw [h2 h]

/-! ## Bit lengths -/

theorem bitLen_le_iff' (n k : ℕ) : bitLen n ≤ k ↔ n < 2 ^ k := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := (bitLen_le_iff' n _).1 le_rfl

theorem bitLen_add_le (a b : ℕ) : bitLen (a + b) ≤ bitLen a + bitLen b + 1 := by
  rw [bitLen_le_iff']
  have ha := lt_two_pow_bitLen a
  have hb := lt_two_pow_bitLen b
  have h1 : 2 ^ bitLen a ≤ 2 ^ (bitLen a + bitLen b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ bitLen b ≤ 2 ^ (bitLen a + bitLen b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

theorem bitLen_le_self' (n : ℕ) : bitLen n ≤ n := length_encodeNat_le n

end SubNLogN.Machine.BridgePP
