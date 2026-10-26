import Contracts.W9.Common
import IntMulTM.Framework.Compose
import IntMulTM.Framework.Lib.Basic

/-!
# WP.W9comp.Kit — composing W9 stage programs

The W9 composites (`W9_preNode_of_phases`, `W9_postNode_of_phases`) run phase programs that come
from `BContract`s. Each phase has its own scratch count `mᵢ` and register type `Rᵢ`. This file
provides:
* `emb h`: the stack embedding `BLoc m → BLoc m'`, identity on the named stacks `LB` and
  `Fin.castLE` on scratch. `upd_comp_emb` moves `Function.update` on a named stack across it.
* `callB h l P`: run `P` inside the composite (stacks along `emb h`, registers through the lens `l`).
  `runs_callB` turns a phase's `Runs` into a composite `Runs`; `closed_callB` keeps closedness.
* `runs_seq`, `runs_mono`: sequencing and weakening.
* `pushConst`, `runs_pushConst`: push a constant (the rewind guard).
* `rewindTo src dst g`: move symbols from `src` to `dst` down to the first `g`, then drop `g`.
  `rewindTo_eval` is the exact evaluation; `runs_rewind` is the lifted `Runs`.
* Width monotonicity (`EntryW.mono`, `ArrW.mono`, `MatW.mono`), row sizes from `getD`
  (`rows_of_getD`), and bit lengths (`bitLen_le_of_lt_two_pow`).
-/

namespace WP.W9comp

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Embedding phase programs -/

/-- Stack embedding of a phase with `m` scratch stacks into a composite with `m'`. -/
def emb {m m' : ℕ} (h : m ≤ m') : BLoc m → BLoc m'
  | .inl k => .inl k
  | .inr j => .inr (Fin.castLE h j)

@[simp] theorem emb_inl {m m' : ℕ} (h : m ≤ m') (k : LB) : emb h (.inl k) = .inl k := rfl

theorem emb_injective {m m' : ℕ} (h : m ≤ m') : Function.Injective (emb h) := by
  rintro (a | a) (b | b) hab
  · simpa [emb] using hab
  · simp [emb] at hab
  · simp [emb] at hab
  · simp only [emb, Sum.inr.injEq] at hab
    exact congrArg Sum.inr (Fin.castLE_injective h hab)

/-- `Function.update` on a named stack commutes with the embedding. -/
theorem upd_comp_emb {m m' : ℕ} (h : m ≤ m') (B : BLoc m' → List Sym) (k : LB) (v : List Sym) :
    Function.update (B ∘ emb h) (.inl k) v = (Function.update B (.inl k) v) ∘ emb h :=
  (Function.update_comp_eq_of_injective B (emb_injective h) (.inl k) v).symm

/-- Run a phase program inside the composite. -/
def callB {m m' : ℕ} {σ R : Type} (h : m ≤ m') (l : Lens σ R)
    (P : Prog (BLoc m) (fun _ => Sym) R) : Prog (BLoc m') (fun _ => Sym) σ :=
  (P.mapStk (emb h)).liftRegs l

/-- Lens into the tail of a register pair (composite register files are right-nested products). -/
def lsnd {α β γ : Type} (l : Lens β γ) : Lens (α × β) γ := (Lens.snd α β).comp l

/-- **A phase's `Runs` inside the composite.** The big post-state must agree with the big
pre-state on every scratch stack (phases only update named stacks). -/
theorem runs_callB {m m' : ℕ} {σ R : Type} (h : m ≤ m') (l : Lens σ R)
    {P : Prog (BLoc m) (fun _ => Sym) R} {B B' : BLoc m' → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ emb h) (B' ∘ emb h) Q T) (hout : ∀ j : Fin m', B' (.inr j) = B (.inr j)) :
    Runs (callB h l P) B B' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = B at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := hP ⟨l.get v, stk ∘ emb h⟩ rfl
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk (emb_injective h) stk (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    rcases k with k | j
    · exact (h1 (.inl k)).trans (congrFun hs' (.inl k))
    · by_cases hj : ∃ x, emb h x = .inr j
      · obtain ⟨x, hx⟩ := hj
        rw [← hx]
        exact (h1 x).trans (congrFun hs' x)
      · push_neg at hj
        rw [h2 _ hj, hout j]
  subst hT'
  exact ⟨⟨l.set v s'.var, T'⟩, t, Eval.liftRegs l e' v rfl, ⟨rfl, trivial⟩, ht⟩

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

theorem closed_callB {m m' : ℕ} {σ R : Type} (h : m ≤ m') (l : Lens σ R)
    {P : Prog (BLoc m) (fun _ => Sym) R} (hP : P.Closed) : (callB h l P).Closed :=
  (freeBelow_liftRegs l _ 0).2 ((freeBelow_mapStk (emb h) P 0).2 hP)

theorem closed_seq {K : Type} {Γ : K → Type} {σ : Type} {p q : Prog K Γ σ} (hp : p.Closed)
    (hq : q.Closed) : (Prog.seq p q).Closed :=
  ⟨hp, hq⟩

/-! ## Sequencing -/

section Seq

variable {K σ : Type} [DecidableEq K]

theorem runs_seq {P Q : Prog K (fun _ => Sym) σ} {S1 S2 S3 : K → List Sym} {Q1 Q2 : σ → Prop}
    {T1 T2 : ℕ} (h1 : Runs P S1 S2 Q1 T1) (h2 : Runs Q S2 S3 Q2 T2) :
    Runs (.seq P Q) S1 S3 Q2 (T1 + T2) :=
  Triple.seq (Triple.post h1 fun _ hs => hs.1) h2

theorem runs_mono {P : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q Q' : σ → Prop}
    {T T' : ℕ} (h : Runs P S S' Q T) (hQ : ∀ v, Q v → Q' v) (hT : T ≤ T') : Runs P S S' Q' T' :=
  Triple.cost_mono (Triple.post h fun _ hs => ⟨hs.1, hQ _ hs.2⟩) hT

theorem runs_congr {P : Prog K (fun _ => Sym) σ} {S S' S'' : K → List Sym} {Q : σ → Prop}
    {T : ℕ} (h : Runs P S S' Q T) (he : S' = S'') : Runs P S S'' Q T := he ▸ h

/-- Push a constant (any register type). -/
def pushConst (k : K) (x : Sym) : Prog K (fun _ => Sym) σ := .push k (fun _ => x)

theorem runs_pushConst (k : K) (x : Sym) (S : K → List Sym) :
    Runs (pushConst (σ := σ) k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  exact ⟨_, 1, Eval.push _ _ _ _ _, ⟨rfl, trivial⟩, le_refl _⟩

omit [DecidableEq K] in
theorem closed_pushConst (k : K) (x : Sym) : (pushConst (σ := σ) k x).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, pushConst]

end Seq

/-! ## Guard rewind -/

/-- Loop test of `rewindTo`: the register holds a symbol other than `g`. -/
def notG (g : Sym) : Option Sym → Bool
  | some x => !(decide (x = g))
  | none => false

/-- Loop body of `rewindTo`: push the register onto `dst`, pop `src`. -/
def rewindBody {K : Type} (src dst : K) : SProg K := .seq (pushR dst) (popR src)

/-- Move symbols from `src` to `dst` down to the first `g`, which is popped and dropped. -/
def rewindTo {K : Type} (src dst : K) (g : Sym) : SProg K :=
  .seq (popR src) (.loop (notG g) (rewindBody src dst))

section Rewind

variable {K : Type} [DecidableEq K]

theorem rewind_loop_eval {src dst : K} (hne : src ≠ dst) (g : Sym) :
    ∀ (L rest : List Sym) (S : K → List Sym), g ∉ L → S src = (L ++ g :: rest).tail →
      Eval [] (.loop (notG g) (rewindBody src dst)) ⟨(L ++ g :: rest).head?, S⟩
        ⟨some g, Function.update (Function.update S src rest) dst (L.reverse ++ S dst)⟩
        (3 * L.length + 1)
  | [], rest, S, _, hS => by
    refine (Eval.loop_false (by simp [notG])).of_eq ?_ rfl
    have hS' : S src = rest := hS
    show (⟨some g, S⟩ : SSt K) =
      ⟨some g, Function.update (Function.update S src rest) dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: L, rest, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self ..)
    have hg' : g ∉ L := fun h => hg (List.mem_cons_of_mem _ h)
    have hS' : S src = L ++ g :: rest := hS
    have hpush : Eval [] (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      Eval.push _ _ _ _ _
    have hsrc : Function.update S dst (x :: S dst) src = L ++ g :: rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval [] (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨(L ++ g :: rest).head?, Function.update (Function.update S dst (x :: S dst))
          src (L ++ g :: rest).tail⟩ 1 := by
      refine (Eval.pop [] src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := rewind_loop_eval hne g L rest
      (Function.update (Function.update S dst (x :: S dst)) src (L ++ g :: rest).tail) hg'
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by simp [notG, hx]) (Eval.seq hpush hpop) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- **rewindTo**, exact. -/
theorem rewindTo_eval {src dst : K} (hne : src ≠ dst) (g : Sym) (v : Option Sym)
    (L rest : List Sym) (S : K → List Sym) (hg : g ∉ L) (hS : S src = L ++ g :: rest) :
    Eval [] (rewindTo src dst g) ⟨v, S⟩
      ⟨some g, Function.update (Function.update S src rest) dst (L.reverse ++ S dst)⟩
      (3 * L.length + 2) := by
  have h1 : Eval [] (popR src) ⟨v, S⟩
      ⟨(L ++ g :: rest).head?, Function.update S src (L ++ g :: rest).tail⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := rewind_loop_eval hne g L rest (Function.update S src (L ++ g :: rest).tail) hg
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- `rewindTo` through a register lens, as `Runs`. -/
theorem runs_rewind {σ : Type} (l : Lens σ (Option Sym)) {src dst : K} (hne : src ≠ dst)
    (g : Sym) (L rest : List Sym) (S : K → List Sym) (hg : g ∉ L) (hS : S src = L ++ g :: rest) :
    Runs ((rewindTo src dst g).liftRegs l) S
      (Function.update (Function.update S src rest) dst (L.reverse ++ S dst)) (fun _ => True)
      (3 * L.length + 2) := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  exact ⟨_, _, Eval.liftRegs l (rewindTo_eval hne g (l.get v) L rest stk hg hS) v rfl,
    ⟨rfl, trivial⟩, le_refl _⟩

omit [DecidableEq K] in
theorem closed_rewind {σ : Type} (l : Lens σ (Option Sym)) (src dst : K) (g : Sym) :
    ((rewindTo src dst g).liftRegs l).Closed :=
  closed_liftRegs l (by simp [Prog.Closed, Prog.FreeBelow, rewindTo, rewindBody, pushR, popR])

end Rewind

/-! ## Widths, rows, bit lengths -/

theorem EntryW.mono {w w' : ℕ} (h : w ≤ w') {z : ℤ × ℤ} (hz : EntryW w z) : EntryW w' z :=
  ⟨hz.1.trans h, hz.2.trans h⟩

theorem ArrW.mono {w w' : ℕ} (h : w ≤ w') {x : Array (ℤ × ℤ)} (hx : ArrW w x) : ArrW w' x :=
  fun z hz => EntryW.mono h (hx z hz)

theorem MatW.mono {w w' : ℕ} (h : w ≤ w') {M : Array (Array (ℤ × ℤ))} (hM : MatW w M) :
    MatW w' M :=
  fun row hr => ArrW.mono h (hM row hr)

/-- Row sizes in the contracts' `∀ row ∈ M.toList` form, from the `getD` form. -/
theorem rows_of_getD {α : Type} {M : Array (Array α)} {n : ℕ}
    (h : ∀ i < M.size, (M.getD i #[]).size = n) : ∀ row ∈ M.toList, row.size = n := by
  intro row hrow
  rw [Array.mem_toList_iff] at hrow
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hrow
  have := h i hi
  simpa [Array.getD, hi] using this

theorem bitLen_zero' : bitLen 0 = 0 := by
  simp [bitLen, encodeNat_zero]

theorem bitLen_add_add_one' (n : ℕ) : bitLen (n + n + 1) = bitLen n + 1 := by
  simp [bitLen, encodeNat_add_add_one]

theorem bitLen_add_self_le' (n : ℕ) : bitLen (n + n) ≤ bitLen n + 1 := by
  unfold bitLen
  rw [encodeNat_add]
  split_ifs <;> simp

theorem bitLen_le_of_lt_two_pow {n k : ℕ} (h : n < 2 ^ k) : bitLen n ≤ k := by
  induction k generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    subst hn
    simp [bitLen_zero']
  | succ k ih =>
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [pow_succ] at h
      have h1 := ih (n := j) (by omega)
      have h2 := bitLen_add_self_le' j
      rw [two_mul]
      omega
    · rw [pow_succ] at h
      have h1 := ih (n := j) (by omega)
      rw [two_mul, bitLen_add_add_one']
      omega

#assert_std_axioms emb_injective upd_comp_emb runs_callB closed_callB closed_seq runs_seq runs_mono
  runs_congr runs_pushConst closed_pushConst rewind_loop_eval rewindTo_eval runs_rewind
  closed_rewind EntryW.mono ArrW.mono MatW.mono rows_of_getD bitLen_le_of_lt_two_pow
  freeBelow_liftRegs freeBelow_mapStk closed_liftRegs bitLen_zero' bitLen_add_add_one'
  bitLen_add_self_le'

end WP.W9comp
