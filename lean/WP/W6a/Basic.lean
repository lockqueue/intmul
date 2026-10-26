import Contracts.Machine.W3
import Contracts.Machine.W6a

/-!
# WP.W6a.Basic — helpers for the long-division work package

* `call ι l P`: run a contract program `P` (local stacks `Loc n m`, registers `R`) inside a bigger
  program, renaming its stacks along an injection `ι` and its registers along a lens `l`.
  `call_eval` / `call_eval_upd` turn the contract's `Runs` into an evaluation of the big program in
  which every stack outside the image of `ι` and every register outside the lens is unchanged.
* `Prog.Closed` is preserved by `liftRegs` and `mapStk`, hence by `call` (`closed_call`).
* `dropBits k`: pop the bit block on top of stack `k`, keeping its terminator (cost `3·|blk| + 2`).
* Generic exact atoms `eval_push'`, `eval_pop'`, `eval_peek'` with the final state given up to
  equality, and `liftFst` (an `SProg` run inside registers `Option Sym × τ`).
* Bit lengths: `lt_two_pow_bitLen`, `bitLen_le_of_lt_two_pow`, `bitLen_mono`.
* Canonical doubling: `natSyms (r + r + 1) = bit 1 :: natSyms r`, and `natSyms (r + r) =
  bit 0 :: natSyms r` for `r ≠ 0`.
* One quotient-bit step of schoolbook division (`div_step`), and `notLt_ordOf`.
-/

namespace WP.W6a

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Embedding contract programs -/

/-- Run the contract program `P` inside a program over stacks `K` and registers `σ`: its stacks are
renamed along `ι`, its registers live behind the lens `l`. -/
def call {n m : ℕ} {K σ R : Type} (ι : Loc n m → K) (l : Lens σ R)
    (P : Prog (Loc n m) (fun _ => Sym) R) : Prog K (fun _ => Sym) σ :=
  (P.mapStk ι).liftRegs l

/-- A contract's `Runs`, read through an injective stack embedding and a register lens. -/
theorem call_eval {n m : ℕ} {K σ R : Type} [DecidableEq K] {ι : Loc n m → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog (Loc n m) (fun _ => Sym) R}
    {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (h : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) (v : σ) :
    ∃ w t, Eval [] (call ι l P) ⟨v, B⟩ ⟨l.set v w, B'⟩ t ∧ Q w ∧ t ≤ T := by
  obtain ⟨s', t, e, ⟨hs', hq⟩, ht⟩ := h ⟨l.get v, B ∘ ι⟩ rfl
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι B (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      rw [h1 x, hs']
      rfl
    · push_neg at hk
      rw [h2 k hk, hout k hk]
  subst hT'
  exact ⟨s'.var, t, Eval.liftRegs l e' v rfl, hq, ht⟩

/-- `call_eval` for a contract whose final stacks update one named stack. -/
theorem call_eval_upd {n m : ℕ} {K σ R : Type} [DecidableEq K] {ι : Loc n m → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog (Loc n m) (fun _ => Sym) R}
    {B : K → List Sym} (i : Loc n m) (x : List Sym) {Q : R → Prop} {T : ℕ}
    (h : Runs P (B ∘ ι) (Function.update (B ∘ ι) i x) Q T) (v : σ) :
    ∃ w t, Eval [] (call ι l P) ⟨v, B⟩ ⟨l.set v w, Function.update B (ι i) x⟩ t ∧ Q w ∧
      t ≤ T := by
  refine call_eval hι l ?_ ?_ v
  · rw [Function.update_comp_eq_of_injective B hι i x]
    exact h
  · intro k hk
    exact Function.update_of_ne (fun e => hk i e.symm) _ _

/-! ## Closedness -/

theorem freeBelow_liftRegs {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ) :
    ∀ (p : Prog K Γ τ) (d : ℕ), (p.liftRegs l).FreeBelow d ↔ p.FreeBelow d
  | .push _ _, _ => Iff.rfl
  | .peek _ _, _ => Iff.rfl
  | .pop _ _, _ => Iff.rfl
  | .load _, _ => Iff.rfl
  | .seq p q, d => and_congr (freeBelow_liftRegs l p d) (freeBelow_liftRegs l q d)
  | .ite _ p q, d => and_congr (freeBelow_liftRegs l p d) (freeBelow_liftRegs l q d)
  | .loop _ p, d => freeBelow_liftRegs l p d
  | .fix b, d => freeBelow_liftRegs l b (d + 1)
  | .recur _, _ => Iff.rfl

theorem freeBelow_mapStk {K K' A σ : Type} (ι : K → K') :
    ∀ (p : Prog K (fun _ => A) σ) (d : ℕ), (p.mapStk ι).FreeBelow d ↔ p.FreeBelow d
  | .push _ _, _ => Iff.rfl
  | .peek _ _, _ => Iff.rfl
  | .pop _ _, _ => Iff.rfl
  | .load _, _ => Iff.rfl
  | .seq p q, d => and_congr (freeBelow_mapStk ι p d) (freeBelow_mapStk ι q d)
  | .ite _ p q, d => and_congr (freeBelow_mapStk ι p d) (freeBelow_mapStk ι q d)
  | .loop _ p, d => freeBelow_mapStk ι p d
  | .fix b, d => freeBelow_mapStk ι b (d + 1)
  | .recur _, _ => Iff.rfl

theorem closed_liftRegs {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ) {p : Prog K Γ τ}
    (h : p.Closed) : (p.liftRegs l).Closed :=
  (freeBelow_liftRegs l p 0).2 h

theorem closed_call {n m : ℕ} {K σ R : Type} (ι : Loc n m → K) (l : Lens σ R)
    {P : Prog (Loc n m) (fun _ => Sym) R} (h : P.Closed) : (call ι l P).Closed :=
  (freeBelow_liftRegs l _ 0).2 ((freeBelow_mapStk ι P 0).2 h)

/-! ## Exact atoms with the final state up to equality -/

section Atoms

variable {K σ : Type} [DecidableEq K]

theorem eval_push' (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Sym) (v : σ)
    (S S' : K → List Sym) (h : Function.update S k (f v :: S k) = S') :
    Eval ρ (.push k f) ⟨v, S⟩ ⟨v, S'⟩ 1 :=
  (Eval.push ρ k f v S).of_eq (by rw [h]) rfl

theorem eval_pop' (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ) (v : σ)
    (S S' : K → List Sym) (x : Sym) (tl : List Sym) (hk : S k = x :: tl)
    (h : Function.update S k tl = S') :
    Eval ρ (.pop k f) ⟨v, S⟩ ⟨f v (some x), S'⟩ 1 := by
  have e := Eval.pop ρ k f v S
  rw [hk] at e
  exact e.of_eq (by rw [← h]; rfl) rfl

theorem eval_peek' (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ) (v : σ)
    (S : K → List Sym) (o : Option Sym) (hk : (S k).head? = o) :
    Eval ρ (.peek k f) ⟨v, S⟩ ⟨f v o, S⟩ 1 :=
  (Eval.peek ρ k f v S).of_eq (by rw [hk]) rfl

/-- An `SProg` (one `Option Sym` register) run inside registers `Option Sym × τ`. -/
theorem liftFst {τ : Type} {p : SProg K} {S S' : K → List Sym} {r r' : Option Sym} {t : ℕ}
    (h : Eval [] p ⟨r, S⟩ ⟨r', S'⟩ t) (v : Option Sym × τ) (hv : v.1 = r) :
    Eval [] (p.liftRegs (Lens.fst _ _)) ⟨v, S⟩ ⟨(r', v.2), S'⟩ t := by
  subst hv
  exact Eval.liftRegs (Lens.fst _ _) h v rfl

end Atoms

/-! ## Dropping a bit block -/

/-- Loop body of `dropBits`: pop, then look at the next symbol. -/
def dropBody {K : Type} (k : K) : SProg K := .seq (.pop k fun r _ => r) (peekR k)

/-- Pop the bit block on top of `k`; its terminator stays on `k` and ends up in the register. -/
def dropBits {K : Type} (k : K) : SProg K := .seq (peekR k) (.loop optIsBit (dropBody k))

theorem dropBits_loop_eval {K : Type} [DecidableEq K] (k : K) (ρ : List (SProg K)) :
    ∀ (es : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S k = es.map Sym.bit ++ rest →
      Eval ρ (.loop optIsBit (dropBody k)) ⟨(es.map Sym.bit ++ rest).head?, S⟩
        ⟨rest.head?, Function.update S k rest⟩ (3 * es.length + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    simp only [List.map_nil, List.nil_append] at hS ⊢
    rw [← hS, Function.update_eq_self]
  | e :: es, rest, S, hrest, hS => by
    have h1 : Eval ρ (.pop k fun r _ => r) ⟨((e :: es).map Sym.bit ++ rest).head?, S⟩
        ⟨some (.bit e), Function.update S k (es.map Sym.bit ++ rest)⟩ 1 :=
      eval_pop' ρ k _ _ S _ (.bit e) (es.map Sym.bit ++ rest) hS rfl
    have h2 : Eval ρ (peekR k) ⟨some (.bit e), Function.update S k (es.map Sym.bit ++ rest)⟩
        ⟨(es.map Sym.bit ++ rest).head?, Function.update S k (es.map Sym.bit ++ rest)⟩ 1 :=
      eval_peek' ρ k _ _ _ _ (by rw [Function.update_self])
    have ih := dropBits_loop_eval k ρ es rest (Function.update S k (es.map Sym.bit ++ rest)) hrest
      (Function.update_self _ _ _)
    rw [Function.update_idem] at ih
    exact (Eval.loop_true (by rfl) (Eval.seq h1 h2) ih).of_eq rfl
      (by simp only [List.length_cons]; omega)

/-- **dropBits**, exact. -/
theorem dropBits_eval {K : Type} [DecidableEq K] (k : K) (ρ : List (SProg K)) (v : Option Sym)
    (es : List Bool) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = es.map Sym.bit ++ rest) :
    Eval ρ (dropBits k) ⟨v, S⟩ ⟨rest.head?, Function.update S k rest⟩ (3 * es.length + 2) :=
  (Eval.seq (eval_peek' ρ k (fun _ o => o) v S _ (by rw [hS]))
    (dropBits_loop_eval k ρ es rest S hrest hS)).of_eq rfl (by omega)

theorem closed_dropBits {K : Type} (k : K) : (dropBits k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, dropBits, dropBody, peekR]

/-! ## Bit lengths -/

theorem natSyms_zero : natSyms 0 = [] := by
  simp [natSyms, encodeNat_zero]

theorem bitLen_zero : bitLen 0 = 0 := by
  simp [bitLen, encodeNat_zero]

theorem natSyms_add_add_one (r : ℕ) : natSyms (r + r + 1) = .bit true :: natSyms r := by
  simp [natSyms, encodeNat_add_add_one]

theorem natSyms_add_self (r : ℕ) (h : r ≠ 0) : natSyms (r + r) = .bit false :: natSyms r := by
  simp only [natSyms]
  rw [encodeNat_add, if_neg (by rw [encodeNat_eq_nil_iff]; exact h)]
  rfl

theorem bitLen_add_add_one (n : ℕ) : bitLen (n + n + 1) = bitLen n + 1 := by
  simp [bitLen, encodeNat_add_add_one]

theorem bitLen_add_self_le (n : ℕ) : bitLen (n + n) ≤ bitLen n + 1 := by
  unfold bitLen
  rw [encodeNat_add]
  split_ifs <;> simp

theorem bitLen_add_self (n : ℕ) (h : n ≠ 0) : bitLen (n + n) = bitLen n + 1 := by
  unfold bitLen
  rw [encodeNat_add, if_neg (by rw [encodeNat_eq_nil_iff]; exact h)]
  simp

theorem lt_two_pow_bitLen (n : ℕ) : n < 2 ^ bitLen n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · by_cases hk : k = 0
    · subst hk
      simp [bitLen_zero]
    · rw [two_mul, bitLen_add_self k hk, pow_succ]
      have := ih k (by omega)
      omega
  · rw [two_mul, bitLen_add_add_one, pow_succ]
    have := ih k (by omega)
    omega

theorem bitLen_le_of_lt_two_pow {n k : ℕ} (h : n < 2 ^ k) : bitLen n ≤ k := by
  induction k generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    subst hn
    simp [bitLen_zero]
  | succ k ih =>
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [pow_succ] at h
      have h1 := ih (n := j) (by omega)
      have h2 := bitLen_add_self_le j
      rw [two_mul]
      omega
    · rw [pow_succ] at h
      have h1 := ih (n := j) (by omega)
      rw [two_mul, bitLen_add_add_one]
      omega

theorem bitLen_mono {m n : ℕ} (h : m ≤ n) : bitLen m ≤ bitLen n :=
  bitLen_le_of_lt_two_pow (lt_of_le_of_lt h (lt_two_pow_bitLen n))

/-- A number below `2·b` has at most one bit more than `b`. -/
theorem bitLen_lt_two_mul {x b : ℕ} (h : x < b + b) : bitLen x ≤ bitLen b + 1 := by
  refine bitLen_le_of_lt_two_pow ?_
  have := lt_two_pow_bitLen b
  rw [pow_succ]
  omega

/-! ## Schoolbook division: one quotient bit -/

/-- Appending the bit `c` to the dividend `h`: with `r = h % b` and `x = 2r + c`, the new quotient
is `2·(h / b) + [b ≤ x]` and the new remainder `x - [b ≤ x]·b`. -/
theorem div_step {h b c : ℕ} (hb : 0 < b) (hc : c ≤ 1) :
    (h + h + c) / b =
        (if b ≤ h % b + h % b + c then h / b + h / b + 1 else h / b + h / b) ∧
      (h + h + c) % b =
        (if b ≤ h % b + h % b + c then h % b + h % b + c - b else h % b + h % b + c) := by
  have h1 := Nat.mod_add_div h b
  have h2 := Nat.mod_lt h hb
  split_ifs with hge
  · refine (Nat.div_mod_unique hb).2 ⟨?_, by omega⟩
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  · refine (Nat.div_mod_unique hb).2 ⟨?_, by omega⟩
    rw [Nat.mul_add]
    omega

/-! ## Ordering test -/

/-- `false` exactly on `lt`. -/
def notLt : Ordering → Bool
  | .lt => false
  | _ => true

theorem notLt_ordOf (x y : ℕ) : notLt (ordOf x y) = decide (y ≤ x) := by
  by_cases h : x < y
  · rw [show ordOf x y = .lt from if_pos h, decide_eq_false (by omega)]
    rfl
  · rw [decide_eq_true (by omega)]
    unfold ordOf
    rw [if_neg h]
    split_ifs <;> rfl

#assert_std_axioms call_eval call_eval_upd freeBelow_liftRegs freeBelow_mapStk closed_liftRegs
  closed_call eval_push' eval_pop' eval_peek' liftFst dropBits_loop_eval dropBits_eval
  closed_dropBits natSyms_zero bitLen_zero natSyms_add_add_one natSyms_add_self bitLen_add_add_one
  bitLen_add_self_le bitLen_add_self lt_two_pow_bitLen bitLen_le_of_lt_two_pow bitLen_mono
  bitLen_lt_two_mul div_step notLt_ordOf

end WP.W6a
