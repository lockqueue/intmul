import Contracts.Machine.W6a

/-!
# WP.W9fDiv.Prog — signed rounding division for the W9f column solvers

`z += divRoundRatInt a b`, for a signed numerator `a` (stack `.inl 0`) and a **signed** denominator
`b` (stack `.inl 1`); both are restored. The result is `0` when `b ≤ 0`, as in the snapshot's
`divRoundRatInt`.

**Program** `w9Prog Pr`, where `Pr` is a `W6a_divRound` program (natural denominator, at most 6
scratch stacks):

1. pop the sign symbol of `b` into a register; stack `.inl 1` now holds `|b|`;
2. peek its top: a bit iff `|b| ≠ 0`;
3. if the sign is `pos` and `|b| ≠ 0` (that is, `b > 0`), run `Pr` on `(a, |b|, z)`; otherwise push
   `pos` onto `z` (`intSyms 0 = [pos]`);
4. push the sign symbol back onto `.inl 1`.

`Pr` runs on the named stacks in place, and on the six scratch stacks through `fin6`.

**Standalone.** As W9f asked, this package depends only on the frozen contracts and the snapshot. The
contract-embedding helpers below (`call`, `call_eval_upd`, …) are therefore local copies of those in
`WP.W6a.Basic`.
-/

namespace WP.W9fDiv

open TMFw TMFw.Contracts Computability

/-! ## Embedding a contract program (copied from `WP.W6a.Basic`) -/

/-- Run the contract program `P` inside a program over stacks `K` and registers `σ`. -/
def call {n m : ℕ} {K σ R : Type} (ι : Loc n m → K) (l : Lens σ R)
    (P : Prog (Loc n m) (fun _ => Sym) R) : Prog K (fun _ => Sym) σ :=
  (P.mapStk ι).liftRegs l

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

theorem closed_call {n m : ℕ} {K σ R : Type} (ι : Loc n m → K) (l : Lens σ R)
    {P : Prog (Loc n m) (fun _ => Sym) R} (h : P.Closed) : (call ι l P).Closed :=
  (freeBelow_liftRegs l _ 0).2 ((freeBelow_mapStk ι P 0).2 h)

/-! ## Exact atoms with the final state up to equality (copied from `WP.W6a.Basic`) -/

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

end Atoms

/-! ## Stacks, registers, program -/

/-- Local stacks: named `a` (`.inl 0`), `b` (`.inl 1`), `z` (`.inl 2`); six scratch stacks, used
only by the embedded `divRound` program. -/
abbrev FStk := Loc 3 6

/-- Registers: current symbol, sign symbol of `b`, registers of the `divRound` program. -/
abbrev FReg (R : Type) := Option Sym × Option Sym × R

/-- Lens on the registers of the `divRound` program. -/
def Ldr (R : Type) : Lens (FReg R) R where
  get v := v.2.2
  set v w := (v.1, v.2.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Fold a scratch index into `Fin 6` (the identity on `Fin m` for `m ≤ 6`). -/
def fin6 {m : ℕ} (j : Fin m) : Fin 6 := ⟨j.val % 6, Nat.mod_lt _ (by decide)⟩

/-- Stack embedding of the `divRound` program: named stacks in place, scratch through `fin6`. -/
def drStk {m : ℕ} (x : Loc 3 m) : FStk := Sum.map id fin6 x

theorem drStk_injective {m : ℕ} (hm : m ≤ 6) : Function.Injective (drStk (m := m)) := by
  intro x y h
  rcases x with i | j <;> rcases y with i' | j'
  · simpa [drStk] using h
  · simp [drStk] at h
  · simp [drStk] at h
  · simp only [drStk, Sum.map_inr, Sum.inr.injEq] at h
    have hv := congrArg Fin.val h
    simp only [fin6] at hv
    have hj := j.isLt
    have hj' := j'.isLt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    exact congrArg Sum.inr (Fin.ext hv)

variable {R : Type}

/-- **Signed rounding division** `z += divRoundRatInt a b` (`0` when `b ≤ 0`), from a `divRound`
program `Pr` with a natural denominator. -/
def w9Prog {m : ℕ} (Pr : Prog (Loc 3 m) (fun _ => Sym) R) : Prog FStk (fun _ => Sym) (FReg R) :=
  .seq (.pop (.inl 1) fun v o => (v.1, o, v.2.2))
    (.seq (.peek (.inl 1) fun v o => (o, v.2))
      (.seq (.ite (fun v => decide (v.2.1 = some .pos) && optIsBit v.1)
          (call drStk (Ldr R) Pr) (.push (.inl 2) fun _ => .pos))
        (.push (.inl 1) fun v => v.2.1.getD .sep)))

theorem w9Prog_closed {m : ℕ} (Pr : Prog (Loc 3 m) (fun _ => Sym) R) (h : Pr.Closed) :
    (w9Prog Pr).Closed := by
  have h1 : (call drStk (Ldr R) Pr).FreeBelow 0 := closed_call drStk (Ldr R) h
  simp only [Prog.Closed]
  simp [Prog.FreeBelow, w9Prog, h1]

#assert_std_axioms call_eval call_eval_upd freeBelow_liftRegs freeBelow_mapStk closed_call
  eval_push' eval_pop' eval_peek' drStk_injective w9Prog_closed

end WP.W9fDiv
