import Contracts.Machine.W3
import IntMulTM.Framework.Lib.Basic

/-!
# WP.W3e.Basic — evaluation atoms and bit-list facts for the constant shifts

* `eval_stk`, `eval_peek_eq`, `eval_pop_eq`, `eval_push_eq`: the framework's `Eval` atoms with the
  final state given explicitly.
* `optIsBit_head_natSyms`: the top of `natSyms n ++ rx` (`TermOK rx`) is a bit iff `n ≠ 0`.
* `natSyms_mul_two_pow`: for `n ≠ 0`, `natSyms (n·2^k)` is `natSyms n` with `k` zero bits on top
  (LSB first).
* `natSyms_half`: for `n ≠ 0`, `natSyms n` is one bit on top of `natSyms (n / 2)`.
-/

namespace WP.W3e

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- The operand stack of both shifts. -/
abbrev X0 : Loc 1 0 := .inl 0

/-! ## Evaluation atoms with explicit final states -/

section Atoms

variable {K σ : Type} [DecidableEq K]

/-- Rewrite only the final stacks of an evaluation. -/
theorem eval_stk {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ}
    {s : St K (fun _ => Sym) σ} {v : σ} {S₁ S₂ : K → List Sym} {t : ℕ}
    (h : Eval ρ p s ⟨v, S₁⟩ t) (hS : S₁ = S₂) : Eval ρ p s ⟨v, S₂⟩ t := by
  subst hS
  exact h

theorem eval_pop_eq (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ)
    (v : σ) (S : K → List Sym) (x : Sym) (L : List Sym) (hS : S k = x :: L) :
    Eval ρ (.pop k f) ⟨v, S⟩ ⟨f v (some x), Function.update S k L⟩ 1 :=
  (Eval.pop ρ k f v S).of_eq (by simp only [hS, List.head?_cons, List.tail_cons]) rfl

theorem eval_peek_eq (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ)
    (v : σ) (S : K → List Sym) (o : Option Sym) (ho : (S k).head? = o) :
    Eval ρ (.peek k f) ⟨v, S⟩ ⟨f v o, S⟩ 1 :=
  (Eval.peek ρ k f v S).of_eq (by rw [ho]) rfl

theorem eval_push_eq (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Sym) (v : σ)
    (S : K → List Sym) (x : Sym) (L : List Sym) (hx : f v = x) (hL : S k = L) :
    Eval ρ (.push k f) ⟨v, S⟩ ⟨v, Function.update S k (x :: L)⟩ 1 :=
  (Eval.push ρ k f v S).of_eq (by rw [hx, hL]) rfl

end Atoms

/-! ## Bit-list facts -/

/-- The top of `natSyms n ++ rx` is a bit iff `n ≠ 0`. -/
theorem optIsBit_head_natSyms (n : ℕ) {rx : List Sym} (hrx : TermOK rx) :
    optIsBit (natSyms n ++ rx).head? = !decide (n = 0) := by
  cases h : encodeNat n with
  | nil =>
    have hn : n = 0 := (encodeNat_eq_nil_iff n).1 h
    subst hn
    simp [natSyms, h, optIsBit_head?_of_termOK hrx]
  | cons b l =>
    have hn : n ≠ 0 := fun hn => by rw [hn, encodeNat_zero] at h; cases h
    simp [natSyms, h, hn]

theorem natSyms_dbl (n : ℕ) (hn : n ≠ 0) : natSyms (n + n) = .bit false :: natSyms n := by
  have hne : encodeNat n ≠ [] := fun h => hn ((encodeNat_eq_nil_iff n).1 h)
  simp only [natSyms, encodeNat_add, if_neg hne, List.map_cons]

theorem natSyms_dbl_one (n : ℕ) : natSyms (n + n + 1) = .bit true :: natSyms n := by
  simp only [natSyms, encodeNat_add_add_one, List.map_cons]

/-- **Shift left**: `k` zero bits on top of `natSyms n`, for `n ≠ 0`. -/
theorem natSyms_mul_two_pow {n : ℕ} (hn : n ≠ 0) :
    ∀ k, natSyms (n * 2 ^ k) = List.replicate k (Sym.bit false) ++ natSyms n
  | 0 => by rw [pow_zero, Nat.mul_one, List.replicate_zero, List.nil_append]
  | k + 1 => by
    have h0 : n * 2 ^ k ≠ 0 := Nat.mul_ne_zero hn (pow_ne_zero k (by decide))
    rw [show n * 2 ^ (k + 1) = n * 2 ^ k + n * 2 ^ k by rw [pow_succ, ← Nat.mul_assoc, Nat.mul_two],
      natSyms_dbl _ h0, natSyms_mul_two_pow hn k, List.replicate_succ, List.cons_append]

/-- **Halving**: for `n ≠ 0`, the low bit is on top of `natSyms (n / 2)`. -/
theorem natSyms_half {n : ℕ} (hn : n ≠ 0) : ∃ b, natSyms n = .bit b :: natSyms (n / 2) := by
  obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' n
  · refine ⟨false, ?_⟩
    have hq : q ≠ 0 := by omega
    rw [two_mul, natSyms_dbl q hq, show (q + q) / 2 = q by omega]
  · refine ⟨true, ?_⟩
    rw [two_mul, natSyms_dbl_one, show (q + q + 1) / 2 = q by omega]

#assert_std_axioms eval_stk eval_pop_eq eval_peek_eq eval_push_eq optIsBit_head_natSyms natSyms_dbl
  natSyms_dbl_one natSyms_mul_two_pow natSyms_half

end WP.W3e
