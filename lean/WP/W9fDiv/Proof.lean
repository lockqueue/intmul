import WP.W9fDiv.Prog

/-!
# WP.W9fDiv.Proof — the W9fDiv statement from `W6a_divRound`

* `w9Prog_spec`: let `Pr` be any `W6a_divRound` program with constant `C`. Then `w9Prog Pr` computes
  `z += divRoundRatInt a b` for signed `a, b`, restores `a` and `b`, and takes at most
  `(C + 5)·(|a|·|b| + |a| + |b| + 1)` steps.
* `W9fDivCore_of_divRound : W6a_divRound → W9fDivCore`. Here `W9fDivCore` is the W9fDiv statement
  with the restated `TMFw.Contracts.divRoundRatInt`. `WP.W9fDiv.Spec` bridges it to the snapshot's
  `IntMul.divRoundRatInt`, definitionally.
-/

namespace WP.W9fDiv

open TMFw TMFw.Contracts Computability

/-- The body of `W6a_divRound` for one program `Pr` with cost constant `C`. -/
def DRSpec {m : ℕ} {R : Type} (C : ℕ) (Pr : Prog (Loc 3 m) (fun _ => Sym) R) : Prop :=
  ∀ (num : ℤ) (den : ℕ) (ra rb : List Sym) (S : Loc 3 m → List Sym), 0 < den →
    TermOK ra → TermOK rb → S (.inl 0) = intSyms num ++ ra → S (.inl 1) = natSyms den ++ rb →
    Runs Pr S (Function.update S (.inl 2) (intSyms (divRoundRatInt num den) ++ S (.inl 2)))
      (fun _ => True)
      (C * (bitLen num.natAbs * bitLen den + bitLen num.natAbs + bitLen den + 1))

/-- The W9fDiv statement with the restated `divRoundRatInt` of `Contracts.Machine.W6a`. -/
def W9fDivCore : Prop :=
  MContract Unit 3 16 Unit fun _ m _ C _ P =>
    ∀ (a b : ℤ) (ra rb : List Sym) (S : Loc 3 m → List Sym), TermOK ra → TermOK rb →
      TermOK (S (.inl 2)) → S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
      Runs P S (Function.update S (.inl 2) (intSyms (divRoundRatInt a b) ++ S (.inl 2)))
        (fun _ => True)
        (C * (bitLen a.natAbs * bitLen b.natAbs + bitLen a.natAbs + bitLen b.natAbs + 1))

theorem divRoundRatInt_of_nonpos (a b : ℤ) (hb : b ≤ 0) : divRoundRatInt a b = 0 := by
  unfold divRoundRatInt
  rw [if_neg (not_lt.mpr hb)]

theorem intSyms_zero : intSyms 0 = [Sym.pos] := by
  simp [intSyms, sgnSym, natSyms, encodeNat_zero]

theorem headBit_natSyms (n : ℕ) (rest : List Sym) (hrest : TermOK rest) :
    optIsBit (natSyms n ++ rest).head? = !decide (n = 0) := by
  by_cases hn : n = 0
  · subst hn
    rw [natSyms, encodeNat_zero, List.map_nil, List.nil_append, optIsBit_head?_of_termOK hrest]
    rfl
  · obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat n = b :: l := by
      cases h : encodeNat n with
      | nil => exact absurd ((encodeNat_eq_nil_iff n).1 h) hn
      | cons b l => exact ⟨b, l, rfl⟩
    rw [natSyms, hbl, decide_eq_false hn]
    rfl

/-- Restoring `b`'s stack after the middle step, which only changed `z`. -/
theorem upd_restore (S : FStk → List Sym) (X Z : List Sym) :
    Function.update (Function.update (Function.update S (.inl 1) X) (.inl 2) Z) (.inl 1)
      (S (.inl 1)) = Function.update S (.inl 2) Z := by
  rw [Function.update_comm (by decide : (.inl 2 : FStk) ≠ .inl 1), Function.update_idem,
    Function.update_eq_self]

section Spec

variable {m : ℕ} {R : Type}

theorem w9Prog_spec {C : ℕ} {Pr : Prog (Loc 3 m) (fun _ => Sym) R} (hm : m ≤ 6)
    (hspec : DRSpec C Pr) (a b : ℤ) (ra rb : List Sym) (S : FStk → List Sym) (hra : TermOK ra)
    (hrb : TermOK rb) (hA : S (.inl 0) = intSyms a ++ ra) (hB : S (.inl 1) = intSyms b ++ rb) :
    Runs (w9Prog Pr) S (Function.update S (.inl 2) (intSyms (divRoundRatInt a b) ++ S (.inl 2)))
      (fun _ => True)
      ((C + 5) * (bitLen a.natAbs * bitLen b.natAbs + bitLen a.natAbs + bitLen b.natAbs + 1)) := by
  refine Runs.of_eval fun v => ?_
  -- 1. pop the sign of `b`
  have e1 : Eval [] (.pop (.inl 1) fun v o => (v.1, o, v.2.2) : Prog FStk (fun _ => Sym) (FReg R))
      ⟨v, S⟩ ⟨(v.1, some (sgnSym b), v.2.2), Function.update S (.inl 1) (natSyms b.natAbs ++ rb)⟩
      1 :=
    eval_pop' [] (.inl 1 : FStk) _ v S _ (sgnSym b) (natSyms b.natAbs ++ rb) hB rfl
  -- 2. look at the top of `|b|`
  have e2 : Eval [] (.peek (.inl 1) fun v o => (o, v.2) : Prog FStk (fun _ => Sym) (FReg R))
      ⟨(v.1, some (sgnSym b), v.2.2), Function.update S (.inl 1) (natSyms b.natAbs ++ rb)⟩
      ⟨((natSyms b.natAbs ++ rb).head?, some (sgnSym b), v.2.2),
        Function.update S (.inl 1) (natSyms b.natAbs ++ rb)⟩ 1 :=
    eval_peek' [] (.inl 1 : FStk) _ _ _ _ (by rw [Function.update_self])
  have hhead := headBit_natSyms b.natAbs rb hrb
  -- 4. push the sign of `b` back (both branches end in the same way)
  have e4 : ∀ (w : FReg R) (Z : List Sym), w.2.1 = some (sgnSym b) →
      Eval [] (.push (.inl 1) fun v => v.2.1.getD .sep : Prog FStk (fun _ => Sym) (FReg R))
        ⟨w, Function.update (Function.update S (.inl 1) (natSyms b.natAbs ++ rb)) (.inl 2) Z⟩
        ⟨w, Function.update S (.inl 2) Z⟩ 1 := by
    intro w Z hw
    refine eval_push' [] (.inl 1 : FStk) _ _ _ _ ?_
    show Function.update (Function.update (Function.update S (.inl 1) (natSyms b.natAbs ++ rb))
      (.inl 2) Z) (.inl 1) (w.2.1.getD .sep :: (natSyms b.natAbs ++ rb)) = _
    rw [hw]
    show Function.update (Function.update (Function.update S (.inl 1) (natSyms b.natAbs ++ rb))
      (.inl 2) Z) (.inl 1) (intSyms b ++ rb) = _
    rw [← hB, upd_restore]
  by_cases hpos : 0 < b
  · -- `b > 0`: run `divRound` with denominator `|b|`
    have hd : 0 < b.natAbs := Int.natAbs_pos.mpr hpos.ne'
    have hcast : ((b.natAbs : ℕ) : ℤ) = b := Int.natAbs_of_nonneg hpos.le
    have hR := hspec a b.natAbs ra rb
      (Function.update S (.inl 1) (natSyms b.natAbs ++ rb) ∘ drStk) hd hra hrb
      (by
        show Function.update S (.inl 1) (natSyms b.natAbs ++ rb) (.inl 0) = _
        rw [Function.update_of_ne (show (.inl 0 : FStk) ≠ .inl 1 by decide)]
        exact hA)
      (by
        show Function.update S (.inl 1) (natSyms b.natAbs ++ rb) (.inl 1) = _
        rw [Function.update_self])
    obtain ⟨w, t3, e3, -, ht3⟩ := call_eval_upd
      (B := Function.update S (.inl 1) (natSyms b.natAbs ++ rb)) (drStk_injective hm) (Ldr R)
      (.inl 2) _ hR ((natSyms b.natAbs ++ rb).head?, some (sgnSym b), v.2.2)
    rw [hcast] at e3
    have e3' : Eval [] (call drStk (Ldr R) Pr)
        ⟨((natSyms b.natAbs ++ rb).head?, some (sgnSym b), v.2.2),
          Function.update S (.inl 1) (natSyms b.natAbs ++ rb)⟩
        ⟨(Ldr R).set ((natSyms b.natAbs ++ rb).head?, some (sgnSym b), v.2.2) w,
          Function.update (Function.update S (.inl 1) (natSyms b.natAbs ++ rb)) (.inl 2)
            (intSyms (divRoundRatInt a b) ++ S (.inl 2))⟩ t3 := e3
    have hc : (decide (some (sgnSym b) = some Sym.pos) &&
        optIsBit (natSyms b.natAbs ++ rb).head?) = true := by
      have hs : sgnSym b = .pos := by unfold sgnSym; rw [if_neg (by omega)]
      rw [hhead, hs]
      simp [hpos.ne']
    refine ⟨_, _, Eval.seq e1 (Eval.seq e2 (Eval.seq (Eval.ite_true hc e3')
      (e4 _ _ rfl))), trivial, ?_⟩
    rw [Nat.add_mul]
    omega
  · -- `b ≤ 0`: the result is `0`
    have hb0 : divRoundRatInt a b = 0 := divRoundRatInt_of_nonpos a b (not_lt.mp hpos)
    have hc : (decide (some (sgnSym b) = some Sym.pos) &&
        optIsBit (natSyms b.natAbs ++ rb).head?) = false := by
      rw [hhead]
      by_cases hneg : b < 0
      · have hs : sgnSym b = .neg := by unfold sgnSym; rw [if_pos hneg]
        rw [hs]
        simp
      · have h0 : b = 0 := by omega
        subst h0
        simp
    have e3 : Eval [] (.push (.inl 2) fun _ => Sym.pos : Prog FStk (fun _ => Sym) (FReg R))
        ⟨((natSyms b.natAbs ++ rb).head?, some (sgnSym b), v.2.2),
          Function.update S (.inl 1) (natSyms b.natAbs ++ rb)⟩
        ⟨((natSyms b.natAbs ++ rb).head?, some (sgnSym b), v.2.2),
          Function.update (Function.update S (.inl 1) (natSyms b.natAbs ++ rb)) (.inl 2)
            (intSyms (divRoundRatInt a b) ++ S (.inl 2))⟩ 1 := by
      refine eval_push' [] (.inl 2 : FStk) _ _ _ _ ?_
      rw [hb0, intSyms_zero]
      rfl
    refine ⟨_, _, Eval.seq e1 (Eval.seq e2 (Eval.seq (Eval.ite_false hc e3)
      (e4 _ _ rfl))), trivial, ?_⟩
    rw [Nat.add_mul]
    omega

end Spec

/-- **W9fDiv** (restated `divRoundRatInt`), from `W6a_divRound`. -/
theorem W9fDivCore_of_divRound (h : W6a_divRound) : W9fDivCore := by
  obtain ⟨Cr, hCr⟩ := h
  obtain ⟨m, R, _, Pr, hm, hfin, hne, hcl, hspec⟩ := hCr ()
  refine ⟨Cr + 5, fun _ => ⟨6, FReg R, fun _ => (), w9Prog Pr, by decide, ?_, ?_,
    w9Prog_closed Pr hcl, ?_⟩⟩
  · haveI := hfin
    infer_instance
  · obtain ⟨r⟩ := hne
    exact ⟨(none, none, r)⟩
  · intro a b ra rb S hra hrb _ hA hB
    exact w9Prog_spec hm hspec a b ra rb S hra hrb hA hB

#assert_std_axioms divRoundRatInt_of_nonpos intSyms_zero headBit_natSyms upd_restore w9Prog_spec
  W9fDivCore_of_divRound

end WP.W9fDiv
