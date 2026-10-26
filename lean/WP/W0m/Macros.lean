import WP.W0m.Sched
import IntMulTM.Framework.Lib.Counter

/-!
# WP.W0m.Macros — two new library macros with exact `Eval` lemmas

* `dropNat k`: pop the number on top of `k`, keeping its terminator. Cost `2·|blk| + 4`.
* `countBits src t tm c ct`: add the bit length of the top block of `src` to the binary counter on
  `c`. `src` and the scratch stacks `t`, `tm`, `ct` are restored. Cost
  `≤ 7·|blk| + cntCost v |blk| + 10`, where `v` is the counter's initial value. The increments are
  amortised: `cntCost v m ≤ 17·m + 6·popcount (encodeNat v)` (`cntCost_le`), so counting from `0`
  costs `≤ 24·|blk| + 10`.
-/

namespace WP.W0m

open Computability TMFw TMFw.Lib TMFw.Contracts

variable {K : Type}

/-- Pop while the register holds a bit. -/
def dropLoop (k : K) : SProg K := .loop optIsBit (popR k)

/-- Drop the number on top of `k`, keeping its terminator. -/
def dropNat (k : K) : SProg K := .seq (popR k) (.seq (dropLoop k) (restoreR k))

/-- Counting loop body: increment the counter `c` (temporary `ct`), pop the next symbol of `t`. -/
def cntBody (t c ct : K) : SProg K := .seq (inc c ct) (popR t)

/-- Counting loop: while the register holds a bit. -/
def cntLoop (t c ct : K) : SProg K := .loop optIsBit (cntBody t c ct)

/-- Add the bit length of the top block of `src` to the counter on `c`. Guard `t` with a mark, copy
the block onto `t`, then pop it bit by bit while incrementing `c`; the mark ends the loop. -/
def countBits (src t tm c ct : K) : SProg K :=
  .seq (pushC t .mark) (.seq (copyBlock src t tm) (.seq (popR t) (cntLoop t c ct)))

/-- Cost bound of the counting loop: from counter value `v`, over `m` bits. -/
def cntCost : ℕ → ℕ → ℕ
  | _, 0 => 0
  | v, m + 1 => 6 * ones (encodeNat v) + 11 + cntCost (v + 1) m

/-- Amortised increments (potential `6 · popcount`). -/
theorem cntCost_le : ∀ (m v : ℕ),
    cntCost v m + 6 * popcount (encodeNat (v + m)) ≤ 17 * m + 6 * popcount (encodeNat v)
  | 0, v => by simp [cntCost]
  | m + 1, v => by
    have ih := cntCost_le m (v + 1)
    have hid := ones_add_popcount_incBits (encodeNat v)
    rw [← encodeNat_succ] at hid
    rw [show v + (m + 1) = v + 1 + m by omega]
    simp only [cntCost]
    omega

theorem cntCost_zero_le (m : ℕ) : cntCost 0 m ≤ 17 * m := by
  have h := cntCost_le m 0
  rw [encodeNat_zero] at h
  simp only [popcount] at h
  omega

variable [DecidableEq K]

theorem dropLoop_eval {k : K} (ρ : List (SProg K)) :
    ∀ (es : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S k = (es.map Sym.bit ++ rest).tail →
      Eval ρ (dropLoop k) ⟨(es.map Sym.bit ++ rest).head?, S⟩
        ⟨rest.head?, Function.update S k rest.tail⟩ (2 * es.length + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    have hS' : S k = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt K) = ⟨rest.head?, Function.update S k rest.tail⟩
    rw [← hS', Function.update_eq_self]
  | e :: es, rest, S, hrest, hS => by
    have hS' : S k = es.map Sym.bit ++ rest := hS
    have hpop : Eval ρ (popR k) ⟨some (.bit e), S⟩
        ⟨(es.map Sym.bit ++ rest).head?, Function.update S k (es.map Sym.bit ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ k (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hS']
    have ih := dropLoop_eval ρ es rest (Function.update S k (es.map Sym.bit ++ rest).tail) hrest
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) hpop ih).of_eq ?_ ?_
    · rw [Function.update_idem]
    · simp only [List.length_cons]
      omega

/-- **dropNat**, exact. -/
theorem dropNat_eval {k : K} (ρ : List (SProg K)) (v : Option Sym) (es : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest) (hS : S k = es.map Sym.bit ++ rest) :
    Eval ρ (dropNat k) ⟨v, S⟩ ⟨rest.head?, Function.update S k rest⟩ (2 * es.length + 4) := by
  have h1 : Eval ρ (popR k) ⟨v, S⟩
      ⟨(es.map Sym.bit ++ rest).head?, Function.update S k (es.map Sym.bit ++ rest).tail⟩ 1 := by
    refine (Eval.pop ρ k (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := dropLoop_eval ρ es rest (Function.update S k (es.map Sym.bit ++ rest).tail) hrest
    (Function.update_self _ _ _)
  rw [Function.update_idem] at h2
  have h3 := restoreR_eval ρ k rest (Function.update S k rest.tail) (Function.update_self _ _ _)
  rw [Function.update_idem] at h3
  exact (Eval.seq h1 (Eval.seq h2 h3)).of_eq rfl (by omega)

theorem cntLoop_eval {t c ct : K} (htc : t ≠ c) (htct : t ≠ ct) (hcct : c ≠ ct)
    (ρ : List (SProg K)) (rc Z : List Sym) (hrc : TermOK rc) :
    ∀ (es : List Bool) (v : ℕ) (S : K → List Sym),
      S t = (es.map Sym.bit ++ Sym.mark :: Z).tail → S c = natSyms v ++ rc →
      ∃ cost, cost ≤ cntCost v es.length + 1 ∧
        Eval ρ (cntLoop t c ct) ⟨(es.map Sym.bit ++ Sym.mark :: Z).head?, S⟩
          ⟨some Sym.mark, Function.update (Function.update S t Z) c
            (natSyms (v + es.length) ++ rc)⟩ cost
  | [], v, S, hS, hc => by
    refine ⟨1, by simp [cntCost], (Eval.loop_false (by rfl)).of_eq ?_ rfl⟩
    have hS' : S t = Z := hS
    show (⟨some Sym.mark, S⟩ : SSt K) = _
    rw [← hS', Function.update_eq_self, List.length_nil, Nat.add_zero, ← hc,
      Function.update_eq_self]
  | e :: es, v, S, hS, hc => by
    have hS' : S t = es.map Sym.bit ++ Sym.mark :: Z := hS
    obtain ⟨ci, hci, ei⟩ := inc_eval (k := c) (t := ct) hcct ρ (some (.bit e)) (encodeNat v) rc S
      hrc hc
    rw [← encodeNat_succ] at ei
    set S1 := Function.update S c ((encodeNat (v + 1)).map Sym.bit ++ rc) with hS1
    have hS1t : S1 t = es.map Sym.bit ++ Sym.mark :: Z := by
      rw [hS1, Function.update_of_ne htc, hS']
    have ep : Eval ρ (popR t) ⟨some .mark, S1⟩
        ⟨(es.map Sym.bit ++ Sym.mark :: Z).head?,
          Function.update S1 t (es.map Sym.bit ++ Sym.mark :: Z).tail⟩ 1 := by
      refine (Eval.pop ρ t (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hS1t]
    obtain ⟨cr, hcr, er⟩ := cntLoop_eval htc htct hcct ρ rc Z hrc es (v + 1)
      (Function.update S1 t (es.map Sym.bit ++ Sym.mark :: Z).tail) (Function.update_self _ _ _)
      (by rw [Function.update_of_ne (Ne.symm htc), hS1, Function.update_self]; rfl)
    have hlen : v + (e :: es).length = v + 1 + es.length := by
      simp only [List.length_cons]
      omega
    rw [hlen]
    refine ⟨ci + 1 + cr + 1, ?_, (Eval.loop_true (by rfl) (Eval.seq ei ep) er).of_eq ?_ rfl⟩
    · simp only [List.length_cons, cntCost]
      omega
    · congr 1
      funext x
      simp only [hS1, Function.update_apply]
      split_ifs <;> simp_all

/-- **countBits**, exact stacks: only the counter changes. -/
theorem countBits_eval {src t tm c ct : K} (hst : src ≠ t) (hstm : src ≠ tm) (httm : t ≠ tm)
    (htc : t ≠ c) (htct : t ≠ ct) (hcct : c ≠ ct) (ρ : List (SProg K)) (r : Option Sym)
    (blk : List Bool) (rest : List Sym) (v : ℕ) (rc : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hrc : TermOK rc) (hS : S src = blk.map Sym.bit ++ rest)
    (hc : S c = natSyms v ++ rc) :
    ∃ cost, cost ≤ 7 * blk.length + cntCost v blk.length + 10 ∧
      Eval ρ (countBits src t tm c ct) ⟨r, S⟩
        ⟨some Sym.mark, Function.update S c (natSyms (v + blk.length) ++ rc)⟩ cost := by
  set S1 := Function.update S t (Sym.mark :: S t) with hS1
  have e1 : Eval ρ (pushC t .mark) ⟨r, S⟩ ⟨r, S1⟩ 1 := Eval.push ρ t (fun _ => .mark) r S
  have hS1src : S1 src = blk.map Sym.bit ++ rest := by
    rw [hS1, Function.update_of_ne hst, hS]
  have e2 := copyBlock_eval hst hstm httm ρ r blk rest S1 hrest hS1src
  set S2 := Function.update S1 t (blk.map Sym.bit ++ S1 t) with hS2
  have hS2t : S2 t = blk.map Sym.bit ++ Sym.mark :: S t := by
    rw [hS2, Function.update_self, hS1, Function.update_self]
  have e3 : Eval ρ (popR t) ⟨some .mark, S2⟩
      ⟨(blk.map Sym.bit ++ Sym.mark :: S t).head?,
        Function.update S2 t (blk.map Sym.bit ++ Sym.mark :: S t).tail⟩ 1 := by
    refine (Eval.pop ρ t (fun _ o => o) _ _).of_eq ?_ rfl
    rw [hS2t]
  obtain ⟨cl, hcl, e4⟩ := cntLoop_eval htc htct hcct ρ rc (S t) hrc blk v
    (Function.update S2 t (blk.map Sym.bit ++ Sym.mark :: S t).tail) (Function.update_self _ _ _)
    (by rw [Function.update_of_ne (Ne.symm htc), hS2, Function.update_of_ne (Ne.symm htc), hS1,
      Function.update_of_ne (Ne.symm htc), hc])
  refine ⟨1 + (7 * blk.length + 7 + (1 + cl)), by omega,
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ rfl⟩
  congr 1
  funext x
  simp only [hS2, hS1, Function.update_apply]
  split_ifs <;> simp_all

#assert_std_axioms cntCost_le cntCost_zero_le dropLoop_eval dropNat_eval cntLoop_eval countBits_eval

end WP.W0m
