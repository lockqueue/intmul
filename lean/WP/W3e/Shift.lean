import WP.W3e.Basic

/-!
# WP.W3e.Shift — `W3_shlConst` and `W3_shrConst` on the machine

Both programs work in place on the operand stack `X0 = .inl 0` (no scratch stacks, one
`Option Sym` register). The shift amount `k` is the compile-time parameter, so the programs are
unrolled `k` times. LSB is on top.

| program | algorithm | exact cost | contract bound |
|---|---|---|---|
| `shlProg k` | peek; if the top is a bit (`a ≠ 0`), push `k` zero bits, else nothing | `k + 3` (`a ≠ 0`), `3` (`a = 0`) | `3·(k+1)` |
| `shrProg k` | `k` times: peek; if the top is a bit, pop it | `3k + 1` | `3·(k+1)` |

The zero test keeps the results canonical: `0·2^k = 0` stays `[]` (no zero bits are pushed on an
empty block), and a right shift stops at the terminator (`a / 2^k = 0` once the block is empty).
-/

namespace WP.W3e

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Programs -/

/-- Push `k` zero bits onto `X0`. -/
def pushZeros : ℕ → SProg (Loc 1 0)
  | 0 => skip
  | k + 1 => .seq (pushZeros k) (pushC X0 (.bit false))

/-- **`shlConst k`**: `a ↦ a·2^k`. -/
def shlProg (k : ℕ) : SProg (Loc 1 0) := .seq (peekR X0) (.ite optIsBit (pushZeros k) skip)

/-- One conditional pop: drop the top bit if there is one. -/
def popStep : SProg (Loc 1 0) := .seq (peekR X0) (.ite optIsBit (popR X0) skip)

/-- **`shrConst k`**: `a ↦ a / 2^k` (`k` conditional pops). -/
def shrProg : ℕ → SProg (Loc 1 0)
  | 0 => skip
  | k + 1 => .seq popStep (shrProg k)

theorem pushZeros_closed : ∀ k, (pushZeros k).Closed
  | 0 => trivial
  | k + 1 => ⟨pushZeros_closed k, trivial⟩

theorem shlProg_closed (k : ℕ) : (shlProg k).Closed := ⟨trivial, pushZeros_closed k, trivial⟩

theorem popStep_closed : popStep.Closed := ⟨trivial, trivial, trivial⟩

theorem shrProg_closed : ∀ k, (shrProg k).Closed
  | 0 => trivial
  | k + 1 => ⟨popStep_closed, shrProg_closed k⟩

/-! ## Shift left -/

theorem pushZeros_eval (ρ : List (SProg (Loc 1 0))) :
    ∀ (k : ℕ) (v : Option Sym) (S : Loc 1 0 → List Sym),
      Eval ρ (pushZeros k) ⟨v, S⟩
        ⟨v, Function.update S X0 (List.replicate k (Sym.bit false) ++ S X0)⟩ (k + 1)
  | 0, v, S => eval_stk (skip_eval ρ _)
      (by rw [List.replicate_zero, List.nil_append, Function.update_eq_self])
  | k + 1, v, S => by
    have e1 := pushZeros_eval ρ k v S
    have e2 := eval_push_eq ρ X0 (fun _ => Sym.bit false) v
      (Function.update S X0 (List.replicate k (Sym.bit false) ++ S X0)) (.bit false)
      (List.replicate k (Sym.bit false) ++ S X0) rfl (Function.update_self ..)
    refine (Eval.seq e1 e2).of_eq ?_ rfl
    rw [Function.update_idem, List.replicate_succ, List.cons_append]

/-- **Exact run of `shlProg k`.** -/
theorem shlProg_eval (k a : ℕ) (rx : List Sym) (hrx : TermOK rx) (S : Loc 1 0 → List Sym)
    (hS : S X0 = natSyms a ++ rx) (v : Option Sym) :
    ∃ v' t, Eval [] (shlProg k) ⟨v, S⟩
      ⟨v', Function.update S X0 (natSyms (a * 2 ^ k) ++ rx)⟩ t ∧ t ≤ 3 * (k + 1) := by
  have e1 := eval_peek_eq [] X0 (fun _ o => o) v S (natSyms a ++ rx).head? (by rw [hS])
  have hb := optIsBit_head_natSyms a hrx
  by_cases ha : a = 0
  · subst ha
    have hc : optIsBit (natSyms 0 ++ rx).head? = false := by rw [hb]; rfl
    refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.ite_false hc (skip_eval [] _))) ?_, by omega⟩
    rw [Nat.zero_mul, ← hS, Function.update_eq_self]
  · have hc : optIsBit (natSyms a ++ rx).head? = true := by rw [hb]; simp [ha]
    refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.ite_true hc (pushZeros_eval [] k _ S))) ?_,
      by omega⟩
    rw [hS, natSyms_mul_two_pow ha k, List.append_assoc]

/-- **`W3_shlConst` holds** (no hypotheses; `C = 3`, no scratch stacks). -/
theorem W3_shlConst_holds : W3_shlConst := by
  refine ⟨3, fun k => ⟨0, Option Sym, fun _ => (), shlProg k, Nat.zero_le _, inferInstance,
    ⟨none⟩, shlProg_closed k, ?_⟩⟩
  intro a rx S hrx hS
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := shlProg_eval k a rx hrx S hS v
  exact ⟨v', t, e, trivial, ht⟩

/-! ## Shift right -/

/-- One conditional pop halves the operand. -/
theorem popStep_eval (a : ℕ) (rx : List Sym) (hrx : TermOK rx) (S : Loc 1 0 → List Sym)
    (hS : S X0 = natSyms a ++ rx) (v : Option Sym) :
    ∃ v', Eval [] popStep ⟨v, S⟩ ⟨v', Function.update S X0 (natSyms (a / 2) ++ rx)⟩ 3 := by
  have e1 := eval_peek_eq [] X0 (fun _ o => o) v S (natSyms a ++ rx).head? (by rw [hS])
  have hb := optIsBit_head_natSyms a hrx
  by_cases ha : a = 0
  · subst ha
    have hc : optIsBit (natSyms 0 ++ rx).head? = false := by rw [hb]; rfl
    refine ⟨_, eval_stk (Eval.seq e1 (Eval.ite_false hc (skip_eval [] _))) ?_⟩
    rw [Nat.zero_div, ← hS, Function.update_eq_self]
  · obtain ⟨b, hbits⟩ := natSyms_half ha
    have hc : optIsBit (natSyms a ++ rx).head? = true := by rw [hb]; simp [ha]
    have e2 := eval_pop_eq [] X0 (fun _ o => o) (natSyms a ++ rx).head? S (.bit b)
      (natSyms (a / 2) ++ rx) (by rw [hS, hbits, List.cons_append])
    exact ⟨_, Eval.seq e1 (Eval.ite_true hc e2)⟩

/-- **Exact run of `shrProg k`**: `3k + 1` steps. -/
theorem shrProg_eval (rx : List Sym) (hrx : TermOK rx) :
    ∀ (k a : ℕ) (S : Loc 1 0 → List Sym), S X0 = natSyms a ++ rx → ∀ v : Option Sym,
      ∃ v', Eval [] (shrProg k) ⟨v, S⟩
        ⟨v', Function.update S X0 (natSyms (a / 2 ^ k) ++ rx)⟩ (3 * k + 1)
  | 0, a, S, hS, v => ⟨v, eval_stk (skip_eval [] _)
      (by rw [pow_zero, Nat.div_one, ← hS, Function.update_eq_self])⟩
  | k + 1, a, S, hS, v => by
    obtain ⟨v1, e1⟩ := popStep_eval a rx hrx S hS v
    obtain ⟨v2, e2⟩ := shrProg_eval rx hrx k (a / 2)
      (Function.update S X0 (natSyms (a / 2) ++ rx)) (Function.update_self ..) v1
    refine ⟨v2, (Eval.seq e1 e2).of_eq ?_ (by omega)⟩
    rw [Function.update_idem, Nat.div_div_eq_div_mul, ← pow_succ']

/-- **`W3_shrConst` holds** (no hypotheses; `C = 3`, no scratch stacks). -/
theorem W3_shrConst_holds : W3_shrConst := by
  refine ⟨3, fun k => ⟨0, Option Sym, fun _ => (), shrProg k, Nat.zero_le _, inferInstance,
    ⟨none⟩, shrProg_closed k, ?_⟩⟩
  intro a rx S hrx hS
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', e⟩ := shrProg_eval rx hrx k a S hS v
  exact ⟨v', _, e, trivial, by omega⟩

#assert_std_axioms pushZeros_closed shlProg_closed popStep_closed shrProg_closed pushZeros_eval
  shlProg_eval W3_shlConst_holds popStep_eval shrProg_eval W3_shrConst_holds

end WP.W3e
