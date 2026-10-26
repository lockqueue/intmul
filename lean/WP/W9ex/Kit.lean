import IntMulTM.Framework.Lib.Counter
import Contracts.Machine.Common

/-!
# WP.W9ex.Kit — exact-stack triples for `SProg` and the small macros of the extract kernel

`XT B p B' T`: from stacks `B` (any register) the program `p` reaches stacks exactly `B'` within
`T` steps; `XT.runs` turns it into the contracts' `Runs`. Rules: sequencing, weakening, the
framework macros (`pushC`, `popR`, `moveBits`, `copyBlock`, `inc`) and new macros:
* `skipPast k g`: pop `k` up to and including the first `g`;
* `dropBit k`: pop the top of `k` if it is a bit (`natSyms n ↦ natSyms (n / 2)`); `dropBits k j`;
* `rewindTo src dst g`: move `src` onto `dst` (reversing) down to the first `g`, drop `g`
  (same program as `WP.W9comp.rewindTo`);
* `popBranch`: pop, then branch on the popped symbol;
* `cntLoop c t body`: `while c ≠ 0 do (dec c; body)`, zero test before every iteration.
-/

namespace WP.W9ex

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Bit lengths -/

theorem natSyms_zero : natSyms 0 = [] := by
  simp [natSyms, encodeNat_zero]

theorem natSyms_succ_eq (n : ℕ) : natSyms (n + 1) = (incBits (encodeNat n)).map Sym.bit := by
  rw [natSyms, encodeNat_succ]

theorem natSyms_cons {n : ℕ} (hn : n ≠ 0) : ∃ b, natSyms n = Sym.bit b :: natSyms (n / 2) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hk : k ≠ 0 := by omega
    have hne : encodeNat k ≠ [] := fun h => hk ((encodeNat_eq_nil_iff k).1 h)
    refine ⟨false, ?_⟩
    rw [show 2 * k / 2 = k by omega, natSyms, natSyms, two_mul, encodeNat_add, if_neg hne]
    rfl
  · refine ⟨true, ?_⟩
    rw [show (2 * k + 1) / 2 = k by omega, natSyms, natSyms, two_mul, encodeNat_add_add_one]
    rfl

theorem bitLen_zero : bitLen 0 = 0 := by
  simp [bitLen, encodeNat_zero]

theorem bitLen_eq (n : ℕ) : bitLen n = if n = 0 then 0 else bitLen (n / 2) + 1 := by
  split_ifs with h
  · subst h
    exact bitLen_zero
  · obtain ⟨b, hb⟩ := natSyms_cons h
    have := congrArg List.length hb
    simp only [length_natSyms, List.length_cons] at this
    exact this

theorem bitLen_mono (n : ℕ) : ∀ m, m ≤ n → bitLen m ≤ bitLen n := by
  refine Nat.strong_induction_on n ?_
  intro n ih m hmn
  rw [bitLen_eq m, bitLen_eq n]
  by_cases hm : m = 0
  · rw [if_pos hm]
    exact Nat.zero_le _
  · have hn : n ≠ 0 := by omega
    rw [if_neg hm, if_neg hn]
    have := ih (n / 2) (by omega) (m / 2) (by omega)
    omega

theorem bitLen_le_of_lt_two_pow (k : ℕ) : ∀ n, n < 2 ^ k → bitLen n ≤ k := by
  induction k with
  | zero =>
    intro n hn
    have h0 : n = 0 := by simpa using hn
    subst h0
    rw [bitLen_zero]
  | succ k ih =>
    intro n hn
    rw [bitLen_eq n]
    by_cases h0 : n = 0
    · rw [if_pos h0]
      exact Nat.zero_le _
    · rw [if_neg h0]
      have := ih (n / 2) (by rw [pow_succ] at hn; omega)
      omega

/-! ## Exact-stack triples -/

section XT

variable {K : Type} [DecidableEq K]

/-- From stacks `B` (any register), reach stacks exactly `B'` within `T` steps. -/
def XT (B : K → List Sym) (p : SProg K) (B' : K → List Sym) (T : ℕ) : Prop :=
  ∀ v : Option Sym, ∃ v' t, Eval [] p ⟨v, B⟩ ⟨v', B'⟩ t ∧ t ≤ T

theorem XT.seq {B B₁ B₂ : K → List Sym} {p q : SProg K} {T₁ T₂ : ℕ} (h₁ : XT B p B₁ T₁)
    (h₂ : XT B₁ q B₂ T₂) : XT B (.seq p q) B₂ (T₁ + T₂) := by
  intro v
  obtain ⟨v₁, t₁, e₁, ht₁⟩ := h₁ v
  obtain ⟨v₂, t₂, e₂, ht₂⟩ := h₂ v₁
  exact ⟨v₂, t₁ + t₂, Eval.seq e₁ e₂, Nat.add_le_add ht₁ ht₂⟩

theorem XT.mono {B B' : K → List Sym} {p : SProg K} {T T' : ℕ} (h : XT B p B' T)
    (hT : T ≤ T') : XT B p B' T' := by
  intro v
  obtain ⟨v', t, e, ht⟩ := h v
  exact ⟨v', t, e, le_trans ht hT⟩

theorem XT.congr {B B₁ B₂ : K → List Sym} {p : SProg K} {T : ℕ} (h : XT B p B₁ T)
    (hB : B₁ = B₂) : XT B p B₂ T := hB ▸ h

theorem XT.runs {B B' : K → List Sym} {p : SProg K} {T : ℕ} (h : XT B p B' T) :
    Runs p B B' (fun _ => True) T :=
  Runs.of_eval fun v => by
    obtain ⟨v', t, e, ht⟩ := h v
    exact ⟨v', t, e, trivial, ht⟩

theorem xt_pushC (k : K) (x : Sym) (B : K → List Sym) :
    XT B (pushC k x) (Function.update B k (x :: B k)) 1 := fun v =>
  ⟨v, 1, Eval.push _ _ _ _ _, le_rfl⟩

theorem xt_popR {k : K} {B : K → List Sym} {x : Sym} {rest : List Sym} (hk : B k = x :: rest) :
    XT B (popR k) (Function.update B k rest) 1 := by
  intro v
  have e : Eval [] (popR k) ⟨v, B⟩ ⟨some x, Function.update B k rest⟩ 1 := by
    refine (Eval.pop [] k (fun _ o => o) v B).of_eq ?_ rfl
    rw [hk]
    rfl
  exact ⟨_, _, e, le_rfl⟩

theorem xt_moveBits {src dst : K} (hne : src ≠ dst) {B : K → List Sym} (es : List Bool)
    {rest : List Sym} (hrest : TermOK rest) (hS : B src = es.map Sym.bit ++ rest) :
    XT B (moveBits src dst) (Function.update (Function.update B src rest.tail) dst
      (es.reverse.map Sym.bit ++ B dst)) (3 * es.length + 2) := fun v =>
  ⟨_, _, moveBits_eval hne [] v es rest B hrest hS, le_rfl⟩

theorem xt_copyBlock {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    {B : K → List Sym} (blk : List Bool) {rest : List Sym} (hrest : TermOK rest)
    (hS : B src = blk.map Sym.bit ++ rest) :
    XT B (copyBlock src dst tmp) (Function.update B dst (blk.map Sym.bit ++ B dst))
      (7 * blk.length + 7) := fun v =>
  ⟨_, _, copyBlock_eval hsd hst hdt [] v blk rest B hrest hS, le_rfl⟩

theorem xt_inc {k t : K} (hkt : k ≠ t) {B : K → List Sym} (n : ℕ) {rest : List Sym}
    (hrest : TermOK rest) (hS : B k = natSyms n ++ rest) :
    XT B (inc k t) (Function.update B k (natSyms (n + 1) ++ rest)) (6 * bitLen n + 9) := by
  intro v
  obtain ⟨c, hc, e⟩ := inc_eval hkt [] v (encodeNat n) rest B hrest hS
  refine ⟨some .mark, c, e.of_eq ?_ rfl, ?_⟩
  · rw [natSyms_succ_eq]
  · have := ones_le_length (encodeNat n)
    unfold bitLen
    omega

end XT

#assert_std_axioms natSyms_zero natSyms_succ_eq natSyms_cons bitLen_zero bitLen_eq bitLen_mono
  bitLen_le_of_lt_two_pow XT.seq XT.mono XT.congr XT.runs xt_pushC xt_popR xt_moveBits
  xt_copyBlock xt_inc

end WP.W9ex
