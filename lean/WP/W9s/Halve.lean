import WP.W7k2.Ops

/-!
# WP.W9s.Halve — in-place rounding halving of a signed number (W9s piece [b])

`halveRound I k dflt`, in place on host stack `k`:
`intSyms x ++ rest ↦ intSyms (divRoundPow2 x 1) ++ rest`, with `divRoundPow2 x 1 = ⌊(x+1)/2⌋`.
Let `m = |x|`, LSB on top.

1. Pop the sign into register 1, peek the magnitude's top into register 2.
2. If it is not a bit (`m = 0`, so `x = 0`), push `pos` back.
3. Otherwise pop the low bit into register 2, then:
   * `x < 0`: the result is `−(m/2)`. Peek: if a bit follows (`m/2 ≠ 0`) push `neg`, else `pos`.
   * `x > 0`: the result is `m/2 + (m mod 2)`. If the low bit was `1`, increment with the `incNat`
     instance (`callI`, registers through `incLens`). Then push `pos`.

Every branch pushes a constant sign, so no register is read after the `incNat` call. Cost: at most
`7 + C·(ones (enc (m/2)) + 1) ≤ (C + 20)·(|m| + 1)`.
-/

namespace WP.W9s

open TMFw TMFw.Contracts WP.W7k2 Computability
open IntMul (divRoundPow2)

/-- Body of `W3_incNat` for one extracted instance (`exists_inst`, verbatim). -/
def SpecInc (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a + 1) ++ rx)) (fun _ => True)
      (C * (ones (encodeNat a) + 1))

/-- Registers of `halveRound`: two symbol registers, then the `incNat` instance's registers. -/
abbrev HReg (I : Inst 1 4 Unit) : Type := Option Sym × Option Sym × I.R

namespace Halve

/-- Lens to the `incNat` instance's registers. -/
def incLens (I : Inst 1 4 Unit) : Lens (HReg I) I.R := (Lens.snd _ _).comp (Lens.snd _ _)

/-- Store a symbol in register 1. -/
def setR1 (I : Inst 1 4 Unit) (v : HReg I) (o : Option Sym) : HReg I := (o, v.2.1, v.2.2)

/-- Store a symbol in register 2. -/
def setR2 (I : Inst 1 4 Unit) (v : HReg I) (o : Option Sym) : HReg I := (v.1, o, v.2.2)

end Halve

open Halve

/-- In place on host stack `k`: `intSyms x ++ rest ↦ intSyms (divRoundPow2 x 1) ++ rest`.
`dflt` is the default host stack of `callI`. -/
def halveRound {a b : ℕ} (I : Inst 1 4 Unit) (k dflt : Loc a b) :
    Prog (Loc a b) (fun _ => Sym) (HReg I) :=
  .seq (.pop k (setR1 I)) <| .seq (.peek k (setR2 I)) <|
    .ite (fun v => optIsBit v.2.1)
      (.seq (.pop k (setR2 I)) <|
        .ite (fun v => decide (v.1 = some .neg))
          (.seq (.peek k (setR2 I)) (.ite (fun v => optIsBit v.2.1) (pushS k .neg) (pushS k .pos)))
          (.seq (.ite (fun v => optBit v.2.1) (callI I [k] dflt (incLens I)) Lib.skip)
            (pushS k .pos)))
      (pushS k .pos)

theorem halveRound_closed {a b : ℕ} (I : Inst 1 4 Unit) (k dflt : Loc a b) :
    (halveRound I k dflt).Closed :=
  ⟨trivial, trivial,
    ⟨trivial, ⟨trivial, trivial, trivial⟩, ⟨callI_closed _ _ _ _, trivial⟩, trivial⟩, trivial⟩

/-! ## Evaluation atoms and number facts (helpers, namespace `WP.W9s.Halve`) -/

namespace Halve

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

/-- For `n ≠ 0`, the low bit (`n % 2 = 1`) is on top of `natSyms (n / 2)`. -/
theorem natSyms_low (n : ℕ) (hn : n ≠ 0) :
    natSyms n = .bit (decide (n % 2 = 1)) :: natSyms (n / 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have e : n = n / 2 + n / 2 := by omega
    rw [show decide (n % 2 = 1) = false by simp [h]]
    calc natSyms n = natSyms (n / 2 + n / 2) := congrArg natSyms e
      _ = _ := natSyms_dbl _ (by omega)
  · have e : n = n / 2 + n / 2 + 1 := by omega
    rw [show decide (n % 2 = 1) = true by simp [h]]
    calc natSyms n = natSyms (n / 2 + n / 2 + 1) := congrArg natSyms e
      _ = _ := natSyms_dbl_one _

theorem intSyms_neg_natCast (q : ℕ) :
    intSyms (-(q : ℤ)) = (if q = 0 then Sym.pos else Sym.neg) :: natSyms q := by
  unfold intSyms sgnSym
  rw [Int.natAbs_neg, Int.natAbs_natCast]
  by_cases hq : q = 0
  · subst hq
    simp
  · rw [if_neg hq, if_pos (show -(q : ℤ) < 0 by omega)]

theorem divRoundPow2_one (x : ℤ) : divRoundPow2 x 1 = (x + 1) / 2 := by
  unfold divRoundPow2
  norm_num

/-- `incNat` on host stack `k` through the lens `l`. -/
theorem HT.incAt {a b : ℕ} {σ : Type} {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecInc I C)
    (l : Lens σ I.R) (k dflt : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym)
    (n : ℕ) (rx : List Sym) (hrx : TermOK rx) (hB : B k = natSyms n ++ rx)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [k] dflt l) (Function.update B k (natSyms (n + 1) ++ rx))
      (C * (ones (encodeNat n) + 1)) :=
  HT.callI_upd I [k] dflt (List.nodup_singleton k) rfl hcap l B (.inl 0) _ (hI n rx _ hrx hB) ρ

/-! ## Correctness and cost -/

/-- **Exact run of `halveRound`** from any registers. -/
theorem halveRound_eval {a b : ℕ} {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecInc I C)
    (k dflt : Loc a b) (hcap : 4 + 1 ≤ a + b) (S : Loc a b → List Sym) (x : ℤ)
    (rest : List Sym) (hrest : TermOK rest) (hS : S k = intSyms x ++ rest)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) (HReg I))) (v : HReg I) :
    ∃ v' t, Eval ρ (halveRound I k dflt) ⟨v, S⟩
      ⟨v', Function.update S k (intSyms (divRoundPow2 x 1) ++ rest)⟩ t ∧
      t ≤ (C + 20) * (bitLen x.natAbs + 1) := by
  obtain ⟨r1, r2, r3⟩ := v
  obtain ⟨m, hm⟩ : ∃ m, m = x.natAbs := ⟨_, rfl⟩
  rw [← hm]
  have hS' : S k = sgnSym x :: (natSyms m ++ rest) := by rw [hS, hm]; rfl
  have hval := divRoundPow2_one x
  have hb1 := optIsBit_head_natSyms m hrest
  have hmul : (C + 20) * (bitLen m + 1) = C * (bitLen m + 1) + 20 * (bitLen m + 1) :=
    Nat.add_mul _ _ _
  have e1 : Eval ρ (.pop k (setR1 I)) ⟨(r1, r2, r3), S⟩
      ⟨(some (sgnSym x), r2, r3), Function.update S k (natSyms m ++ rest)⟩ 1 :=
    eval_pop_eq ρ k (setR1 I) (r1, r2, r3) S (sgnSym x) (natSyms m ++ rest) hS'
  have e2 : Eval ρ (.peek k (setR2 I))
      ⟨(some (sgnSym x), r2, r3), Function.update S k (natSyms m ++ rest)⟩
      ⟨(some (sgnSym x), (natSyms m ++ rest).head?, r3),
        Function.update S k (natSyms m ++ rest)⟩ 1 :=
    eval_peek_eq ρ k (setR2 I) _ _ _ (by rw [Function.update_self])
  by_cases hm0 : m = 0
  · -- `x = 0`: push `pos` back
    have hx0 : x = 0 := Int.natAbs_eq_zero.mp (hm ▸ hm0)
    have hq : divRoundPow2 x 1 = ((0 : ℕ) : ℤ) := by rw [hval, hx0]; rfl
    have hc1 : optIsBit (natSyms m ++ rest).head? = false := by rw [hb1, hm0]; rfl
    have e3 := eval_push_eq ρ k (fun _ => Sym.pos)
      (some (sgnSym x), (natSyms m ++ rest).head?, r3) (Function.update S k (natSyms m ++ rest))
      .pos (natSyms m ++ rest) rfl (by rw [Function.update_self])
    refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.ite_false hc1 e3))) ?_, by omega⟩
    rw [Function.update_idem, hq, intSyms_natCast, hm0, List.cons_append]
  · have hbits := natSyms_low m hm0
    have hc1 : optIsBit (natSyms m ++ rest).head? = true := by rw [hb1]; simp [hm0]
    have hlen : bitLen m = bitLen (m / 2) + 1 := by
      rw [← length_natSyms, ← length_natSyms, hbits, List.length_cons]
    have e4 : Eval ρ (.pop k (setR2 I))
        ⟨(some (sgnSym x), (natSyms m ++ rest).head?, r3), Function.update S k (natSyms m ++ rest)⟩
        ⟨(some (sgnSym x), some (.bit (decide (m % 2 = 1))), r3),
          Function.update (Function.update S k (natSyms m ++ rest)) k (natSyms (m / 2) ++ rest)⟩
        1 :=
      eval_pop_eq ρ k (setR2 I) _ _ (.bit (decide (m % 2 = 1))) (natSyms (m / 2) ++ rest)
        (by rw [Function.update_self, hbits, List.cons_append])
    by_cases hneg : x < 0
    · -- `x < 0`: the result is `−(m/2)`
      have hsgn : sgnSym x = .neg := if_pos hneg
      have hc2 : decide (some (sgnSym x) = some Sym.neg) = true := by rw [hsgn]; rfl
      have hxm : (m : ℤ) = -x := by rw [hm]; exact Int.ofNat_natAbs_of_nonpos hneg.le
      have hq : divRoundPow2 x 1 = -((m / 2 : ℕ) : ℤ) := by rw [hval]; omega
      have e5 : Eval ρ (.peek k (setR2 I))
          ⟨(some (sgnSym x), some (.bit (decide (m % 2 = 1))), r3),
            Function.update (Function.update S k (natSyms m ++ rest)) k (natSyms (m / 2) ++ rest)⟩
          ⟨(some (sgnSym x), (natSyms (m / 2) ++ rest).head?, r3),
            Function.update (Function.update S k (natSyms m ++ rest)) k (natSyms (m / 2) ++ rest)⟩
          1 :=
        eval_peek_eq ρ k (setR2 I) _ _ _ (by rw [Function.update_self])
      have hb3 := optIsBit_head_natSyms (m / 2) hrest
      by_cases hq0 : m / 2 = 0
      · have hc3 : optIsBit (natSyms (m / 2) ++ rest).head? = false := by rw [hb3, hq0]; rfl
        have e6 := eval_push_eq ρ k (fun _ => Sym.pos)
          (some (sgnSym x), (natSyms (m / 2) ++ rest).head?, r3)
          (Function.update (Function.update S k (natSyms m ++ rest)) k (natSyms (m / 2) ++ rest))
          .pos (natSyms (m / 2) ++ rest) rfl (by rw [Function.update_self])
        refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.ite_true hc1 (Eval.seq e4
          (Eval.ite_true hc2 (Eval.seq e5 (Eval.ite_false hc3 e6))))))) ?_, by omega⟩
        rw [Function.update_idem, Function.update_idem, hq, intSyms_neg_natCast, if_pos hq0,
          List.cons_append]
      · have hc3 : optIsBit (natSyms (m / 2) ++ rest).head? = true := by rw [hb3]; simp [hq0]
        have e6 := eval_push_eq ρ k (fun _ => Sym.neg)
          (some (sgnSym x), (natSyms (m / 2) ++ rest).head?, r3)
          (Function.update (Function.update S k (natSyms m ++ rest)) k (natSyms (m / 2) ++ rest))
          .neg (natSyms (m / 2) ++ rest) rfl (by rw [Function.update_self])
        refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.ite_true hc1 (Eval.seq e4
          (Eval.ite_true hc2 (Eval.seq e5 (Eval.ite_true hc3 e6))))))) ?_, by omega⟩
        rw [Function.update_idem, Function.update_idem, hq, intSyms_neg_natCast, if_neg hq0,
          List.cons_append]
    · -- `x > 0`: the result is `m/2 + (m mod 2)`
      have hsgn : sgnSym x = .pos := if_neg hneg
      have hc2 : decide (some (sgnSym x) = some Sym.neg) = false := by rw [hsgn]; rfl
      have hxm : (m : ℤ) = x := by rw [hm]; exact Int.natAbs_of_nonneg (by omega)
      by_cases hodd : m % 2 = 1
      · have hq : divRoundPow2 x 1 = ((m / 2 + 1 : ℕ) : ℤ) := by rw [hval]; omega
        have hc4 : optBit (some (Sym.bit (decide (m % 2 = 1)))) = true := by simp [hodd]
        obtain ⟨s3, t3, e6, hs3, ht3⟩ := HT.incAt hI (incLens I) k dflt hcap
          (Function.update (Function.update S k (natSyms m ++ rest)) k (natSyms (m / 2) ++ rest))
          (m / 2) rest hrest (by rw [Function.update_self]) ρ
          ⟨(some (sgnSym x), some (.bit (decide (m % 2 = 1))), r3),
            Function.update (Function.update S k (natSyms m ++ rest)) k (natSyms (m / 2) ++ rest)⟩
          rfl
        have e7 := eval_push_eq ρ k (fun _ => Sym.pos) s3.var s3.stk .pos
          (natSyms (m / 2 + 1) ++ rest) rfl (by rw [hs3, Function.update_self])
        refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.ite_true hc1 (Eval.seq e4
          (Eval.ite_false hc2 (Eval.seq (Eval.ite_true hc4 e6) e7)))))) ?_, ?_⟩
        · rw [hs3, Function.update_idem, Function.update_idem, Function.update_idem, hq,
            intSyms_natCast, List.cons_append]
        · have hones : ones (encodeNat (m / 2)) ≤ bitLen (m / 2) := ones_le_length _
          have h3 : C * (ones (encodeNat (m / 2)) + 1) ≤ C * (bitLen m + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
      · have hq : divRoundPow2 x 1 = ((m / 2 : ℕ) : ℤ) := by rw [hval]; omega
        have hc4 : optBit (some (Sym.bit (decide (m % 2 = 1)))) = false := by simp [hodd]
        have e7 := eval_push_eq ρ k (fun _ => Sym.pos)
          (some (sgnSym x), some (.bit (decide (m % 2 = 1))), r3)
          (Function.update (Function.update S k (natSyms m ++ rest)) k (natSyms (m / 2) ++ rest))
          .pos (natSyms (m / 2) ++ rest) rfl (by rw [Function.update_self])
        refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 (Eval.ite_true hc1 (Eval.seq e4
          (Eval.ite_false hc2 (Eval.seq (Eval.ite_false hc4 (Lib.skip_eval ρ _)) e7)))))) ?_,
          by omega⟩
        rw [Function.update_idem, Function.update_idem, hq, intSyms_natCast, List.cons_append]

end Halve

/-- **Rounding halving, in place** (W9s piece [b]). -/
theorem HT.halveRound {a b : ℕ} {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecInc I C)
    (k dflt : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (x : ℤ) (rest : List Sym)
    (hrest : TermOK rest) (hB : B k = intSyms x ++ rest)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) (HReg I))) :
    HT ρ B (halveRound I k dflt) (Function.update B k (intSyms (divRoundPow2 x 1) ++ rest))
      ((C + 20) * (bitLen x.natAbs + 1)) := by
  intro s hs
  obtain ⟨v, S⟩ := s
  change S = B at hs
  rw [hs]
  obtain ⟨v', t, e, ht⟩ := Halve.halveRound_eval hI k dflt hcap B x rest hrest hB ρ v
  exact ⟨_, t, e, rfl, ht⟩

#assert_std_axioms halveRound_closed Halve.eval_stk Halve.eval_pop_eq Halve.eval_peek_eq
  Halve.eval_push_eq Halve.optIsBit_head_natSyms Halve.natSyms_dbl Halve.natSyms_dbl_one
  Halve.natSyms_low Halve.intSyms_neg_natCast Halve.divRoundPow2_one Halve.HT.incAt
  Halve.halveRound_eval HT.halveRound

end WP.W9s
