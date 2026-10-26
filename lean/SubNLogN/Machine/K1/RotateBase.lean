/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.LongRecordBase
import SubNLogN.Machine.Contracts.Family
import WP.W3b.DecAmortised
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Choose.Bounds
import WP.W3s.Math

/-!
# K1 support for K4 (`K1/RotateBase.lean`): a `q^ℓ`-fold enumerator and a counted loop

**Scope (honest summary).** Generic, algorithm-free program builders with proved rules (no
`sorry`), used by the controlled rotation (`K1/Rotate.lean`):
* `enumProg l q L leaf`: runs `leaf` exactly `q^ℓ` times, where `ℓ` is a unary counter (`ℓ` bits
  `true` above a terminator) on the stack `L`. It is a recursive procedure (`fix`/`recur`): if
  `ℓ > 0`, decrement the counter, recurse `q` times, increment it again; else run `leaf`. Rule
  `runs_enum` (exact stacks, cost `enumE q T ℓ k + 2`); bound `enumE_le`
  (`O(Σ leaf costs + q^ℓ)` for `q ≥ 2`). The only runtime quantity is the stack counter `ℓ`;
  `q` is a compile-time constant (the number of recursive calls in the program text).
* `cntLoop l K t act`: `act` repeated `n` times, `n` a binary counter on `K` that is decremented
  to `0`. Rule `runs_cntLoop`; the decrements are amortized with `TMFw.W3b.dec_sum`
  (`WP/W3b/DecAmortised.lean`).
* Parameter-driven loops: `nLoop` (`n` read from a counter stack, restored; `runs_nLoop`),
  `mkUnary` (push the unary counter `b`; `runs_mkUnary`), `powLoop` (`leaf` repeated `q^b`
  times; `runs_powLoop`).
* Arithmetic: `pow_le_two_pow` (`(b+1)^J ≤ J!·2^J·2^b`), `bitLen_le_self'`, window sums
  `wsum` (`wsum_add`, `wsum_mul`), `listSum_range`.
-/

namespace SubNLogN.Machine.K1.Rot

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Closedness helpers -/

/-- `FreeBelow` is monotone in the depth. -/
theorem freeBelow_mono {K : Type} {Γ : K → Type} {σ : Type} :
    ∀ (p : Prog K Γ σ) {d d' : ℕ}, d ≤ d' → p.FreeBelow d → p.FreeBelow d'
  | .push _ _, _, _, _, _ => trivial
  | .peek _ _, _, _, _, _ => trivial
  | .pop _ _, _, _, _, _ => trivial
  | .load _, _, _, _, _ => trivial
  | .seq p q, _, _, h, hpq => ⟨freeBelow_mono p h hpq.1, freeBelow_mono q h hpq.2⟩
  | .ite _ p q, _, _, h, hpq => ⟨freeBelow_mono p h hpq.1, freeBelow_mono q h hpq.2⟩
  | .loop _ p, _, _, h, hp => freeBelow_mono p h hp
  | .fix b, _, _, h, hb => freeBelow_mono b (Nat.succ_le_succ h) hb
  | .recur _, _, _, h, hn => Nat.lt_of_lt_of_le hn h

theorem freeBelow_of_closed {K : Type} {Γ : K → Type} {σ : Type} {p : Prog K Γ σ}
    (h : p.Closed) (d : ℕ) : p.FreeBelow d :=
  freeBelow_mono p (Nat.zero_le d) h

/-! ## Sums over windows -/

/-- `Σ_{j < m} w (k + j)`. -/
def wsum (w : ℕ → ℕ) (k m : ℕ) : ℕ := ((List.range m).map fun j => w (k + j)).sum

theorem wsum_add (w : ℕ → ℕ) (k a b : ℕ) : wsum w k (a + b) = wsum w k a + wsum w (k + a) b := by
  simp only [wsum, List.range_add, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, Nat.add_assoc]

theorem wsum_mul (w : ℕ → ℕ) (k m : ℕ) :
    ∀ q, ((List.range q).map fun i => wsum w (k + i * m) m).sum = wsum w k (q * m)
  | 0 => by simp [wsum]
  | q + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, wsum_mul w k m q, Nat.succ_mul,
      wsum_add]
    simp

theorem listSum_range (f : ℕ → ℕ) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, listSum_range f n,
      Finset.sum_range_succ]
    simp

/-! ## The `q^ℓ`-fold enumerator -/

section Enum

variable {K σ : Type}

/-- Unary depth counter: `ℓ` bits `true`. -/
def unary (ℓ : ℕ) : List Sym := List.replicate ℓ (Sym.bit true)

/-- Body of the enumerator: if the unary counter on `L` is nonzero, decrement it, recurse `q`
times, increment it again; otherwise run `leaf`. -/
def enumBody (l : Lens σ (Option Sym)) (q : ℕ) (L : K) (leaf : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq ((peekR L).liftRegs l)
    (.ite (fun r => optIsBit (l.get r))
      (.seq ((popR L).liftRegs l)
        (.seq (forEachProg (List.range q) fun _ => .recur 0) ((pushC L (.bit true)).liftRegs l)))
      leaf)

/-- **The enumerator**: `leaf` is run `q^ℓ` times, `ℓ` = the unary counter on `L`. -/
def enumProg (l : Lens σ (Option Sym)) (q : ℕ) (L : K) (leaf : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .fix (enumBody l q L leaf)

theorem closed_enumProg (l : Lens σ (Option Sym)) (q : ℕ) (L : K)
    {leaf : Prog K (fun _ => Sym) σ} (h : leaf.Closed) : (enumProg l q L leaf).Closed := by
  have hf : ∀ m : List ℕ,
      (forEachProg m fun _ => (Prog.recur 0 : Prog K (fun _ => Sym) σ)).FreeBelow 1 := by
    intro m
    induction m with
    | nil => exact trivial
    | cons a m ih => exact ⟨Nat.zero_lt_one, ih⟩
  exact ⟨trivial, ⟨trivial, hf _, trivial⟩, freeBelow_of_closed h 1⟩

/-- Cost of the enumerator body: `T k` for leaf `k`, plus `2` per body, `2` per call and `5`
per inner node. -/
def enumE (q : ℕ) (T : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, k => T k + 2
  | ℓ + 1, k => ((List.range q).map fun i => enumE q T ℓ (k + i * q ^ ℓ) + 2).sum + 5

theorem closed_peekR_lift (l : Lens σ (Option Sym)) (k : K) : ((peekR k).liftRegs l).Closed :=
  WP.W9comp.closed_liftRegs l (by simp [Prog.Closed, Prog.FreeBelow, peekR])

theorem closed_popR_lift (l : Lens σ (Option Sym)) (k : K) : ((popR k).liftRegs l).Closed :=
  WP.W9comp.closed_liftRegs l (by simp [Prog.Closed, Prog.FreeBelow, popR])

theorem closed_pushC_lift (l : Lens σ (Option Sym)) (k : K) (x : Sym) :
    ((pushC k x).liftRegs l).Closed :=
  WP.W9comp.closed_liftRegs l (by simp [Prog.Closed, Prog.FreeBelow, pushC])

variable [DecidableEq K]

/-- **Enumerator rule.** `St k` are the stacks after `k` leaves (their `L` entry is overridden by
the counter). If leaf `k` runs from `St k` to `St (k + 1)` (counter `0`, i.e. `L = L0`) within
`T k`, for every `k < N`, then the enumerator with counter `ℓ` runs the leaves `k, …,
k + q^ℓ - 1`, from `St k` to `St (k + q^ℓ)`, restoring the counter, within `enumE q T ℓ k + 2`. -/
theorem runs_enum (l : Lens σ (Option Sym)) (q : ℕ) (L : K) (leaf : Prog K (fun _ => Sym) σ)
    (hleafC : leaf.Closed) (St : ℕ → K → List Sym) (L0 : List Sym) (hL0 : TermOK L0) (N : ℕ)
    (Tl : ℕ → ℕ)
    (hleaf : ∀ k, k < N → Runs leaf (Function.update (St k) L L0)
      (Function.update (St (k + 1)) L L0) (fun _ => True) (Tl k)) :
    ∀ ℓ k, k + q ^ ℓ ≤ N →
      Runs (enumProg l q L leaf) (Function.update (St k) L (unary ℓ ++ L0))
        (Function.update (St (k + q ^ ℓ)) L (unary ℓ ++ L0)) (fun _ => True)
        (enumE q Tl ℓ k + 2) := by
  intro ℓ k hk
  have key := Triple.fix (ρ := []) (b := enumBody l q L leaf) (X := ℕ × ℕ)
    (P := fun x s => s.stk = Function.update (St x.2) L (unary x.1 ++ L0) ∧ x.2 + q ^ x.1 ≤ N)
    (Q := fun x s => s.stk = Function.update (St (x.2 + q ^ x.1)) L (unary x.1 ++ L0) ∧ True)
    (T := fun x => enumE q Tl x.1 x.2) (fun x => x.1) ?_ (ℓ, k)
  · exact key.pre fun s hs => ⟨hs, hk⟩
  rintro ⟨ℓ, k⟩ IH
  suffices H : k + q ^ ℓ ≤ N → Triple [enumBody l q L leaf]
      (fun s => s.stk = Function.update (St k) L (unary ℓ ++ L0)) (enumBody l q L leaf)
      (fun s => s.stk = Function.update (St (k + q ^ ℓ)) L (unary ℓ ++ L0) ∧ True)
      (enumE q Tl ℓ k) from fun s hs => H hs.2 s hs.1
  intro hkN
  have hpk := (triple_peek_lens l L (Function.update (St k) L (unary ℓ ++ L0))).env_irrel
    (closed_peekR_lift l L) [enumBody l q L leaf]
  simp only [Function.update_self] at hpk
  cases ℓ with
  | zero =>
    have hlf := (hleaf k (by simpa using hkN)).env hleafC [enumBody l q L leaf]
    have hite : Triple [enumBody l q L leaf]
        (fun s => s.stk = Function.update (St k) L (unary 0 ++ L0) ∧
          l.get s.var = (unary 0 ++ L0).head?)
        (.ite (fun r => optIsBit (l.get r))
          (.seq ((popR L).liftRegs l)
            (.seq (forEachProg (List.range q) fun _ => .recur 0)
              ((pushC L (.bit true)).liftRegs l))) leaf)
        (fun s => s.stk = Function.update (St (k + q ^ 0)) L (unary 0 ++ L0) ∧ True)
        (Tl k + 1) := by
      refine Triple.ite ?_ ?_
      · rintro s ⟨⟨-, hv⟩, hc⟩
        exfalso
        simp only [hv, unary, List.replicate_zero, List.nil_append,
          optIsBit_head?_of_termOK hL0] at hc
        exact Bool.false_ne_true hc
      · refine Triple.conseq hlf (fun s hs => ?_) (fun s hs => ⟨?_, trivial⟩) le_rfl
        · rw [hs.1.1]
          simp [unary]
        · rw [hs.1]
          simp [unary]
    refine Triple.conseq (Triple.seq hpk hite) (fun s hs => hs) (fun s hs => hs) ?_
    simp only [enumE]
    omega
  | succ ℓ =>
    have hlt : ∀ i, i < q → k + i * q ^ ℓ + q ^ ℓ ≤ N := by
      intro i hi
      have h1 : (i + 1) * q ^ ℓ ≤ q * q ^ ℓ := Nat.mul_le_mul_right _ hi
      have h2 : q ^ (ℓ + 1) = q * q ^ ℓ := by rw [pow_succ, Nat.mul_comm]
      have : k + q ^ (ℓ + 1) ≤ N := hkN
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    have hpop : Triple [enumBody l q L leaf]
        (fun s => s.stk = Function.update (St k) L (unary (ℓ + 1) ++ L0)) ((popR L).liftRegs l)
        (fun s => s.stk = Function.update (St (k + 0 * q ^ ℓ)) L (unary ℓ ++ L0)) 1 := by
      refine Triple.post ((runs_wk_popR l L _).env (closed_popR_lift l L) _) fun s hs => ?_
      rw [hs.1, Function.update_idem, Function.update_self]
      simp [unary, List.replicate_succ]
    have hfor := triple_forEachProg (ρ := [enumBody l q L leaf])
      (fun _ => (Prog.recur 0 : Prog K (fun _ => Sym) σ))
      (fun i => enumE q Tl ℓ (k + i * q ^ ℓ) + 2) (List.range q)
      (fun i s => s.stk = Function.update (St (k + i * q ^ ℓ)) L (unary ℓ ++ L0))
      (fun i hi => by
        simp only [List.length_range] at hi
        simp only [List.getElem_range]
        refine Triple.conseq (IH (ℓ, k + i * q ^ ℓ) (Nat.lt_succ_self ℓ))
          (fun s hs => ⟨hs, hlt i hi⟩) (fun s hs => ?_) le_rfl
        rw [hs.1]
        congr 2
        rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc])
    simp only [List.length_range] at hfor
    have hpush : Triple [enumBody l q L leaf]
        (fun s => s.stk = Function.update (St (k + q * q ^ ℓ)) L (unary ℓ ++ L0))
        ((pushC L (.bit true)).liftRegs l)
        (fun s => s.stk = Function.update (St (k + q ^ (ℓ + 1))) L (unary (ℓ + 1) ++ L0) ∧ True)
        1 := by
      refine Triple.post ((runs_wk_pushC l L (.bit true) _).env (closed_pushC_lift l L _) _)
        fun s hs => ⟨?_, trivial⟩
      rw [hs.1, Function.update_idem, Function.update_self, pow_succ, Nat.mul_comm (q ^ ℓ) q]
      simp [unary, List.replicate_succ]
    have hite : Triple [enumBody l q L leaf]
        (fun s => s.stk = Function.update (St k) L (unary (ℓ + 1) ++ L0) ∧
          l.get s.var = (unary (ℓ + 1) ++ L0).head?)
        (.ite (fun r => optIsBit (l.get r))
          (.seq ((popR L).liftRegs l)
            (.seq (forEachProg (List.range q) fun _ => .recur 0)
              ((pushC L (.bit true)).liftRegs l))) leaf)
        (fun s => s.stk = Function.update (St (k + q ^ (ℓ + 1))) L (unary (ℓ + 1) ++ L0) ∧ True)
        (1 + ((((List.range q).map fun i => enumE q Tl ℓ (k + i * q ^ ℓ) + 2).sum + 1) + 1) + 1) := by
      refine Triple.ite ?_ ?_
      · exact Triple.pre (Triple.seq hpop (Triple.seq hfor hpush)) fun s hs => hs.1.1
      · rintro s ⟨⟨-, hv⟩, hc⟩
        exfalso
        simp only [hv, unary, List.replicate_succ, List.cons_append, List.head?_cons,
          optIsBit_some_bit] at hc
        exact absurd hc (by decide)
    refine Triple.conseq (Triple.seq hpk hite) (fun s hs => hs) (fun s hs => hs) ?_
    simp only [enumE]
    omega

end Enum

/-! ## Cost bound of the enumerator -/

/-- **Enumerator cost.** If leaf `k` costs at most `A·w k + c` for `k < N`, the enumerator body
over the leaves `k, …, k + q^ℓ - 1` (`k + q^ℓ ≤ N`) costs at most `A·Σ w + 2D·q^ℓ - D` with
`D = 2q + 5 + c`. -/
theorem enumE_le (q : ℕ) (hq : 2 ≤ q) (Tl w : ℕ → ℕ) (A c N : ℕ)
    (hT : ∀ k, k < N → Tl k ≤ A * w k + c) :
    ∀ ℓ k, k + q ^ ℓ ≤ N → enumE q Tl ℓ k + (2 * q + 5 + c) ≤
      A * wsum w k (q ^ ℓ) + 2 * (2 * q + 5 + c) * q ^ ℓ
  | 0, k, hk => by
    have := hT k (by simpa using hk)
    simp only [enumE, pow_zero, wsum, List.range_one, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, Nat.mul_one]
    omega
  | ℓ + 1, k, hk => by
    have hk' : ∀ i, i < q → k + i * q ^ ℓ + q ^ ℓ ≤ N := by
      intro i hi
      have h1 : (i + 1) * q ^ ℓ ≤ q * q ^ ℓ := Nat.mul_le_mul_right _ hi
      have h2 : q ^ (ℓ + 1) = q * q ^ ℓ := by rw [pow_succ, Nat.mul_comm]
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    have ih : ∀ i, i < q → enumE q Tl ℓ (k + i * q ^ ℓ) + (2 * q + 5 + c) ≤
        A * wsum w (k + i * q ^ ℓ) (q ^ ℓ) + 2 * (2 * q + 5 + c) * q ^ ℓ :=
      fun i hi => enumE_le q hq Tl w A c N hT ℓ (k + i * q ^ ℓ) (hk' i hi)
    have hsum : ∑ i ∈ Finset.range q, (enumE q Tl ℓ (k + i * q ^ ℓ) + (2 * q + 5 + c)) ≤
        ∑ i ∈ Finset.range q, (A * wsum w (k + i * q ^ ℓ) (q ^ ℓ) +
          2 * (2 * q + 5 + c) * q ^ ℓ) :=
      Finset.sum_le_sum fun i hi => ih i (Finset.mem_range.1 hi)
    have e1 : ∑ i ∈ Finset.range q, (enumE q Tl ℓ (k + i * q ^ ℓ) + (2 * q + 5 + c)) =
        (∑ i ∈ Finset.range q, enumE q Tl ℓ (k + i * q ^ ℓ)) + q * (2 * q + 5 + c) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    have e2 : ∑ i ∈ Finset.range q, (A * wsum w (k + i * q ^ ℓ) (q ^ ℓ) +
          2 * (2 * q + 5 + c) * q ^ ℓ) =
        A * (∑ i ∈ Finset.range q, wsum w (k + i * q ^ ℓ) (q ^ ℓ)) +
          q * (2 * (2 * q + 5 + c) * q ^ ℓ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
        Finset.mul_sum]
    rw [e1, e2] at hsum
    have hw := wsum_mul w k (q ^ ℓ) q
    rw [listSum_range] at hw
    rw [hw] at hsum
    have hqD : 2 * (2 * q + 5 + c) ≤ q * (2 * q + 5 + c) := Nat.mul_le_mul_right _ hq
    simp only [enumE]
    rw [listSum_range, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      pow_succ, Nat.mul_comm (q ^ ℓ) q]
    nlinarith [hsum, hqD]

/-- `(b + 1)^J ≤ J!·2^J·2^b`: polynomial work in `b` is absorbed by `2^b` (`≤ q^b` records). -/
theorem pow_le_two_pow (J b : ℕ) : (b + 1) ^ J ≤ J.factorial * 2 ^ J * 2 ^ b := by
  have h1 := Nat.pow_sub_le_descFactorial (b + J) J
  rw [show b + J + 1 - J = b + 1 by omega, Nat.descFactorial_eq_factorial_mul_choose] at h1
  have h2 : (b + J).choose J ≤ 2 ^ (b + J) := Nat.choose_le_two_pow _ _
  calc (b + 1) ^ J ≤ J.factorial * (b + J).choose J := h1
    _ ≤ J.factorial * 2 ^ (b + J) := Nat.mul_le_mul_left _ h2
    _ = J.factorial * 2 ^ J * 2 ^ b := by rw [pow_add]; ring

/-- `bitLen n ≤ n`. -/
theorem bitLen_le_self' (n : ℕ) : bitLen n ≤ n :=
  (TMFw.W3s.bitLen_le_iff n n).2 Nat.lt_two_pow_self

/-! ## Counted loops -/

section Cnt

variable {K σ : Type}

/-- **Counted loop**: `act` runs `n` times, `n` the binary counter on `Kc`, which is decremented
to `0` (`t` is the decrement's temporary). -/
def cntLoop (l : Lens σ (Option Sym)) (Kc t : K) (act : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq ((peekR Kc).liftRegs l)
    (.loop (fun r => optIsBit (l.get r))
      (.seq ((dec Kc t).liftRegs l) (.seq act ((peekR Kc).liftRegs l))))

theorem closed_dec_lift (l : Lens σ (Option Sym)) (k t : K) : ((dec k t).liftRegs l).Closed :=
  WP.W9comp.closed_liftRegs l (by
    simp [Prog.Closed, Prog.FreeBelow, dec, decFix, scanLoop, Lib.scanBody, moveBits,
      moveBitsBody, pushC, popR, pushR, peekR, skip])

theorem closed_cntLoop (l : Lens σ (Option Sym)) (Kc t : K) {act : Prog K (fun _ => Sym) σ}
    (h : act.Closed) : (cntLoop l Kc t act).Closed :=
  ⟨closed_peekR_lift l Kc, closed_dec_lift l Kc t, h, closed_peekR_lift l Kc⟩

theorem loopB_replicate {α : Type} (B : ℕ → α → ℕ) (a : α) :
    ∀ m x, loopB B x (List.replicate m a) = ((List.range m).map fun j => B (x + j) a + 1).sum + 1
  | 0, x => by simp [loopB]
  | m + 1, x => by
    rw [List.replicate_succ, loopB, loopB_replicate B a m (x + 1), List.range_succ_eq_map,
      List.map_cons, List.sum_cons, List.map_map]
    have : ∀ j, x + 1 + j = x + (j + 1) := fun j => by omega
    simp only [Function.comp_def, Nat.add_zero, Nat.succ_eq_add_one, this]
    omega

variable [DecidableEq K]

/-- **Counted-loop rule.** `St j`: the stacks after `j` actions (their `Kc` entry is overridden by
the counter, above `R0`). Action `j` runs with the counter already decremented to `n - (j + 1)`.
Cost: the actions plus `16·n + 6·bitLen n + 2` (amortized decrements, `TMFw.W3b.dec_sum`). -/
theorem runs_cntLoop (l : Lens σ (Option Sym)) {Kc t : K} (hKt : Kc ≠ t)
    (act : Prog K (fun _ => Sym) σ) (St : ℕ → K → List Sym) (R0 : List Sym) (hR0 : TermOK R0)
    (n : ℕ) (Ta : ℕ → ℕ)
    (hact : ∀ j, j < n → Runs act (Function.update (St j) Kc (natSyms (n - (j + 1)) ++ R0))
      (Function.update (St (j + 1)) Kc (natSyms (n - (j + 1)) ++ R0)) (fun _ => True) (Ta j)) :
    Runs (cntLoop l Kc t act) (Function.update (St 0) Kc (natSyms n ++ R0))
      (Function.update (St n) Kc R0) (fun _ => True)
      (((List.range n).map Ta).sum + 16 * n + 6 * bitLen n + 2) := by
  have hloop := triple_loop_list (c := fun r => optIsBit (l.get r))
    (body := .seq ((dec Kc t).liftRegs l) (.seq act ((peekR Kc).liftRegs l)))
    (fun x vs (_ : Unit) => Function.update (St x) Kc (natSyms vs.length ++ R0))
    (fun vs r => l.get r = (natSyms vs.length ++ R0).head?)
    (fun _ (_ : Unit) _ => ())
    (fun x _ => 6 * zerosLead (encodeNat (n - x)) + 8 + (Ta x + 1))
    (fun x vs => x + vs.length = n)
    (fun x a vs h => by simp only [List.length_cons] at h; omega)
    (fun r hr => by
      rw [hr]
      simp only [List.length_nil, natSyms, encodeNat_zero, List.map_nil, List.nil_append]
      exact optIsBit_head?_of_termOK hR0)
    (fun a vs r hr => by
      rw [hr]
      obtain ⟨b, L, hbL⟩ : ∃ b L, encodeNat (vs.length + 1) = b :: L := by
        cases h : encodeNat (vs.length + 1) with
        | nil => exact absurd ((encodeNat_eq_nil_iff _).1 h) (Nat.succ_ne_zero _)
        | cons b L => exact ⟨b, L, rfl⟩
      simp [natSyms, hbL])
    (fun x a vs _ hok => by
      have hn : n - x = vs.length + 1 := by simp only [List.length_cons] at hok; omega
      have hn' : n - (x + 1) = vs.length := by simp only [List.length_cons] at hok; omega
      have r1 := runs_wk_dec l hKt vs.length R0
        (Function.update (St x) Kc (natSyms (a :: vs).length ++ R0)) hR0 (by simp)
      rw [Function.update_idem] at r1
      have r2 := hact x (by simp only [List.length_cons] at hok; omega)
      rw [hn'] at r2
      have p3 := triple_peek_lens l Kc (Function.update (St (x + 1)) Kc (natSyms vs.length ++ R0))
      refine Triple.conseq (runs_seq_triple r1 (runs_seq_triple r2 p3)) (fun s hs => hs.1)
        (fun s hs => ⟨hs.1, by rw [hs.2]; simp⟩) ?_
      rw [hn])
    (List.replicate n ()) 0 () (by simp)
  have p0 := triple_peek_lens l Kc (Function.update (St 0) Kc (natSyms n ++ R0))
  have p0' : Triple [] (fun s => s.stk = Function.update (St 0) Kc (natSyms n ++ R0))
      ((peekR Kc).liftRegs l)
      (fun s => s.stk = Function.update (St 0) Kc (natSyms (List.replicate n ()).length ++ R0) ∧
        l.get s.var = (natSyms (List.replicate n ()).length ++ R0).head?) 1 :=
    Triple.post p0 fun s hs => ⟨by rw [hs.1, List.length_replicate],
      by rw [hs.2, List.length_replicate]; simp⟩
  refine Triple.conseq (Triple.seq p0' hloop) (fun s hs => hs)
    (fun s hs => ⟨?_, trivial⟩) ?_
  · rw [hs]
    simp [natSyms, encodeNat_zero]
  · rw [loopB_replicate]
    have hd := TMFw.W3b.dec_sum n n le_rfl
    have hz := TMFw.W3b.zerosCount_le_length (encodeNat n)
    simp only [listSum_range, Nat.zero_add, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, smul_eq_mul, Nat.sub_self] at hd ⊢
    rw [← Finset.mul_sum]
    have hb : (encodeNat n).length = bitLen n := rfl
    omega

end Cnt

/-! ## Loops driven by parameter counters -/

section Param

variable {K σ : Type}

/-- `act` repeated `n` times, `n` read from the binary counter on `ns` (restored): `Kc` is the
working counter (pushed above a guard, removed at the end), `t` a temporary. -/
def nLoop (l : Lens σ (Option Sym)) (ns Kc t : K) (act : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq ((pushC Kc .mark).liftRegs l) (.seq ((copyBlock ns Kc t).liftRegs l)
    (.seq (cntLoop l Kc t act) ((dropBits Kc).liftRegs l)))

/-- Push the unary counter `b` (read from the binary counter on `bs`) on `L`, above a guard. -/
def mkUnary (l : Lens σ (Option Sym)) (bs L Kc t : K) : Prog K (fun _ => Sym) σ :=
  .seq ((pushC L .mark).liftRegs l) (nLoop l bs Kc t ((pushC L (.bit true)).liftRegs l))

/-- `leaf` repeated `q^b` times, `b` read from the binary counter on `bs` (restored); `L` holds
the unary depth counter during the enumeration. -/
def powLoop (l : Lens σ (Option Sym)) (q : ℕ) (bs L Kc t : K) (leaf : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq (mkUnary l bs L Kc t) (.seq (enumProg l q L leaf) ((dropBits L).liftRegs l))

theorem closed_copyBlock_lift (l : Lens σ (Option Sym)) (a b t : K) :
    ((copyBlock a b t).liftRegs l).Closed :=
  WP.W9comp.closed_liftRegs l (by
    simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
      dupBody, restoreR, pushC, popR, pushR, skip])

theorem closed_dropBits_lift (l : Lens σ (Option Sym)) (k : K) :
    ((dropBits k).liftRegs l).Closed :=
  WP.W9comp.closed_liftRegs l (closed_dropBits k)

theorem closed_nLoop (l : Lens σ (Option Sym)) (ns Kc t : K) {act : Prog K (fun _ => Sym) σ}
    (h : act.Closed) : (nLoop l ns Kc t act).Closed :=
  ⟨closed_pushC_lift l Kc _, closed_copyBlock_lift l ns Kc t, closed_cntLoop l Kc t h,
    closed_dropBits_lift l Kc⟩

theorem closed_powLoop (l : Lens σ (Option Sym)) (q : ℕ) (bs L Kc t : K)
    {leaf : Prog K (fun _ => Sym) σ} (h : leaf.Closed) : (powLoop l q bs L Kc t leaf).Closed :=
  ⟨⟨closed_pushC_lift l L _, closed_nLoop l bs Kc t (closed_pushC_lift l L _)⟩,
    closed_enumProg l q L h, closed_dropBits_lift l L⟩

variable [DecidableEq K]

/-- **`nLoop` rule.** `St j`: the stacks after `j` actions (`Kc` overridden by the counter during
the loop); the counter `n` is read from `ns` in `St 0`. -/
theorem runs_nLoop (l : Lens σ (Option Sym)) {ns Kc t : K} (hnK : ns ≠ Kc) (hnt : ns ≠ t)
    (hKt : Kc ≠ t) (act : Prog K (fun _ => Sym) σ) (St : ℕ → K → List Sym) (n : ℕ)
    (rn : List Sym) (hrn : TermOK rn) (hns : St 0 ns = natSyms n ++ rn)
    (hKc : St n Kc = St 0 Kc) (Ta : ℕ → ℕ)
    (hact : ∀ j, j < n →
      Runs act (Function.update (St j) Kc (natSyms (n - (j + 1)) ++ Sym.mark :: St 0 Kc))
        (Function.update (St (j + 1)) Kc (natSyms (n - (j + 1)) ++ Sym.mark :: St 0 Kc))
        (fun _ => True) (Ta j)) :
    Runs (nLoop l ns Kc t act) (St 0) (St n) (fun _ => True)
      (((List.range n).map Ta).sum + 16 * n + 13 * bitLen n + 12) := by
  have r1 := runs_wk_pushC l Kc Sym.mark (St 0)
  have r2 : Runs ((copyBlock ns Kc t).liftRegs l)
      (Function.update (St 0) Kc (Sym.mark :: St 0 Kc))
      (Function.update (St 0) Kc (natSyms n ++ Sym.mark :: St 0 Kc)) (fun _ => True)
      (7 * bitLen n + 7) := by
    refine runs_liftRegs_of_eval l fun v => ⟨some .mark, _, ?_, le_rfl⟩
    have e := copyBlock_eval hnK hnt hKt [] v (encodeNat n) rn
      (Function.update (St 0) Kc (Sym.mark :: St 0 Kc)) hrn
      (by rw [Function.update_of_ne hnK]; exact hns)
    rw [Function.update_idem, Function.update_self] at e
    exact e
  have r3 := runs_cntLoop l hKt act St (Sym.mark :: St 0 Kc) (TermOK.cons rfl _) n Ta hact
  have r4 := runs_wk_dropBits l Kc [] Sym.mark (St 0 Kc)
    (Function.update (St n) Kc (Sym.mark :: St 0 Kc)) rfl (by simp)
  have r4' := WP.W9comp.runs_congr r4
    (by rw [Function.update_idem, ← hKc, Function.update_eq_self])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 r4'))) (fun _ h => h) ?_
  simp only [List.length_nil]
  omega

/-- **`mkUnary` rule**: pushes the unary counter `b` (above a guard) on `L`. -/
theorem runs_mkUnary (l : Lens σ (Option Sym)) {bs L Kc t : K} (hbK : bs ≠ Kc) (hbt : bs ≠ t)
    (hKt : Kc ≠ t) (hLK : L ≠ Kc) (hLb : L ≠ bs) (S : K → List Sym) (b : ℕ) (rb : List Sym)
    (hrb : TermOK rb) (hbS : S bs = natSyms b ++ rb) :
    Runs (mkUnary l bs L Kc t) S (Function.update S L (unary b ++ Sym.mark :: S L))
      (fun _ => True) (17 * b + 13 * bitLen b + 13) := by
  have r1 : Runs ((pushC L .mark).liftRegs l) S
      (Function.update S L (unary 0 ++ Sym.mark :: S L)) (fun _ => True) 1 :=
    runs_wk_pushC l L Sym.mark S
  have r2 := runs_nLoop l hbK hbt hKt ((pushC L (.bit true)).liftRegs l)
    (fun j => Function.update S L (unary j ++ Sym.mark :: S L)) b rb hrb
    (by
      show Function.update S L (unary 0 ++ Sym.mark :: S L) bs = natSyms b ++ rb
      rw [Function.update_of_ne (Ne.symm hLb)]
      exact hbS)
    (by
      show Function.update S L (unary b ++ Sym.mark :: S L) Kc =
        Function.update S L (unary 0 ++ Sym.mark :: S L) Kc
      rw [Function.update_of_ne (Ne.symm hLK), Function.update_of_ne (Ne.symm hLK)])
    (fun _ => 1)
    (fun j _ => by
      refine WP.W9comp.runs_congr (runs_wk_pushC l L (.bit true) _) ?_
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all [unary, List.replicate_succ])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 r2) (fun _ h => h) ?_
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul, Nat.mul_one]
  omega

/-- **`powLoop` rule.** `St k`: the stacks after `k` leaves (`L` overridden during the
enumeration); `b` is read from `bs` in `St 0`. Leaf `k` runs from `St k` to `St (k + 1)`. -/
theorem runs_powLoop (l : Lens σ (Option Sym)) (q : ℕ) {bs L Kc t : K} (hbK : bs ≠ Kc)
    (hbt : bs ≠ t) (hKt : Kc ≠ t) (hLK : L ≠ Kc) (hLb : L ≠ bs) (leaf : Prog K (fun _ => Sym) σ)
    (hleafC : leaf.Closed) (St : ℕ → K → List Sym) (b : ℕ) (rb : List Sym) (hrb : TermOK rb)
    (hbS : St 0 bs = natSyms b ++ rb) (hL : St (q ^ b) L = St 0 L) (Tl : ℕ → ℕ)
    (hleaf : ∀ k, k < q ^ b → Runs leaf (Function.update (St k) L (Sym.mark :: St 0 L))
      (Function.update (St (k + 1)) L (Sym.mark :: St 0 L)) (fun _ => True) (Tl k)) :
    Runs (powLoop l q bs L Kc t leaf) (St 0) (St (q ^ b)) (fun _ => True)
      (enumE q Tl b 0 + 19 * b + 13 * bitLen b + 17) := by
  have r1 := runs_mkUnary l hbK hbt hKt hLK hLb (St 0) b rb hrb hbS
  have r2 := runs_enum l q L leaf hleafC St (Sym.mark :: St 0 L) (TermOK.cons rfl _) (q ^ b) Tl
    hleaf b 0 (by simp)
  rw [Nat.zero_add] at r2
  have r3 := runs_wk_dropBits l L (List.replicate b true) Sym.mark (St 0 L)
    (Function.update (St (q ^ b)) L (unary b ++ Sym.mark :: St 0 L)) rfl
    (by simp [unary, List.map_replicate])
  have r3' := WP.W9comp.runs_congr r3
    (by rw [Function.update_idem, ← hL, Function.update_eq_self])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 r3'))
    (fun _ h => h) ?_
  simp only [List.length_replicate]
  omega

end Param

end SubNLogN.Machine.K1.Rot
