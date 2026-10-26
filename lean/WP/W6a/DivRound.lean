import WP.W6a.DivRoundProg

/-!
# WP.W6a.DivRound — `W6a_divRound` from `W3_subNat`

The pieces of `divRoundProg` are evaluated on `rst`-states (`rPrologue_eval` … `rEpilogue_eval`).
`divRound_eval_rst` composes them, and `RoundMath.intSyms_divRound` identifies the output with
`intSyms (divRoundRatInt num den)`.

Cost: `divMod` costs `(2·Cs + 70)·(|n|·|den| + |n| + |den| + 1)`. Everything else is linear,
at most `16·|n| + 15·|den| + 61`. Hence the constant is `2·Cs + 140`.

**`W6a_divRound_holds : W3_subNat → W6a_divRound`**, and `W6a_holds` for both contracts.
-/

namespace WP.W6a

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- `call_eval` for a contract whose final stacks update two named stacks. -/
theorem call_eval_upd2 {n m : ℕ} {K σ R : Type} [DecidableEq K] {ι : Loc n m → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog (Loc n m) (fun _ => Sym) R}
    {B : K → List Sym} (i j : Loc n m) (x y : List Sym) {Q : R → Prop} {T : ℕ}
    (h : Runs P (B ∘ ι) (Function.update (Function.update (B ∘ ι) i x) j y) Q T) (v : σ) :
    ∃ w t, Eval [] (call ι l P) ⟨v, B⟩
      ⟨l.set v w, Function.update (Function.update B (ι i) x) (ι j) y⟩ t ∧ Q w ∧ t ≤ T := by
  refine call_eval hι l ?_ ?_ v
  · rw [Function.update_comp_eq_of_injective _ hι j y,
      Function.update_comp_eq_of_injective B hι i x]
    exact h
  · intro k hk
    rw [Function.update_of_ne (fun e => hk j e.symm), Function.update_of_ne (fun e => hk i e.symm)]

theorem optIsBit_natSyms_head (M : ℕ) (rest : List Sym) (hrest : TermOK rest) :
    optIsBit (natSyms M ++ rest).head? = !decide (M = 0) := by
  by_cases hM : M = 0
  · subst hM
    rw [natSyms_zero, List.nil_append, optIsBit_head?_of_termOK hrest]
    rfl
  · obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat M = b :: l := by
      cases h : encodeNat M with
      | nil => exact absurd ((encodeNat_eq_nil_iff M).1 h) hM
      | cons b l => exact ⟨b, l, rfl⟩
    rw [natSyms, hbl, decide_eq_false hM]
    rfl

theorem bitLen_succ_le (n : ℕ) : bitLen (n + 1) ≤ bitLen n + 1 :=
  bitLen_le_of_lt_two_pow (by have := lt_two_pow_bitLen n; rw [pow_succ]; omega)

section Pieces

variable {m : ℕ} {R : Type}

theorem rPrologue_eval (z : ℤ) (ra dC oC yC mC w1 w2 : List Sym) (v : RReg R) :
    Eval [] (rPrologue (R := R)) ⟨v, rst (intSyms z ++ ra) dC oC yC mC w1 w2⟩
      ⟨(v.1, some (sgnSym z), v.2.2),
        rst (natSyms z.natAbs ++ ra) dC oC (.mark :: yC) (.mark :: mC) w1 w2⟩ 3 := by
  have e1 : Eval [] (.pop rN fun v o => (v.1, o, v.2.2) : Prog DRStk (fun _ => Sym) (RReg R))
      ⟨v, rst (intSyms z ++ ra) dC oC yC mC w1 w2⟩
      ⟨(v.1, some (sgnSym z), v.2.2), rst (natSyms z.natAbs ++ ra) dC oC yC mC w1 w2⟩ 1 :=
    eval_pop' [] rN _ v _ _ (sgnSym z) (natSyms z.natAbs ++ ra) rfl (rst_upd_N ..)
  have e2 : Eval [] (.push rY fun _ => .mark : Prog DRStk (fun _ => Sym) (RReg R))
      ⟨(v.1, some (sgnSym z), v.2.2), rst (natSyms z.natAbs ++ ra) dC oC yC mC w1 w2⟩
      ⟨(v.1, some (sgnSym z), v.2.2),
        rst (natSyms z.natAbs ++ ra) dC oC (.mark :: yC) mC w1 w2⟩ 1 :=
    eval_push' [] rY _ _ _ _ (rst_upd_Y ..)
  have e3 : Eval [] (.push rM fun _ => .mark : Prog DRStk (fun _ => Sym) (RReg R))
      ⟨(v.1, some (sgnSym z), v.2.2),
        rst (natSyms z.natAbs ++ ra) dC oC (.mark :: yC) mC w1 w2⟩
      ⟨(v.1, some (sgnSym z), v.2.2),
        rst (natSyms z.natAbs ++ ra) dC oC (.mark :: yC) (.mark :: mC) w1 w2⟩ 1 :=
    eval_push' [] rM _ _ _ _ (rst_upd_M ..)
  exact Eval.seq e1 (Eval.seq e2 e3)

theorem rDivMod_eval {Cs : ℕ} {Ps : Prog (Loc 3 m) (fun _ => Sym) R} (hm : m ≤ 4)
    (hspec : SubSpec Cs Ps) (n den : ℕ) (hd : 0 < den) (ra rb oC yC mC w1 w2 : List Sym)
    (hra : TermOK ra) (hrb : TermOK rb) (v : RReg R) :
    ∃ w t, Eval [] (call dmStk (Ldm R) (divModProg Ps))
      ⟨v, rst (natSyms n ++ ra) (natSyms den ++ rb) oC yC mC w1 w2⟩
      ⟨(Ldm R).set v w, rst (natSyms n ++ ra) (natSyms den ++ rb) oC (natSyms (n / den) ++ yC)
        (natSyms (n % den) ++ mC) w1 w2⟩ t ∧
      t ≤ (2 * Cs + 70) * (bitLen n * bitLen den + bitLen n + bitLen den + 1) := by
  obtain ⟨w, t, e, -, ht⟩ := call_eval_upd2
    (B := rst (natSyms n ++ ra) (natSyms den ++ rb) oC yC mC w1 w2) dmStk_injective (Ldm R) sQ sR
    _ _ (divModProg_spec hm hspec n den ra rb
      (rst (natSyms n ++ ra) (natSyms den ++ rb) oC yC mC w1 w2 ∘ dmStk) hd hra hrb rfl rfl) v
  refine ⟨w, t, e.of_eq ?_ rfl, ht⟩
  show (⟨(Ldm R).set v w, Function.update (Function.update
    (rst (natSyms n ++ ra) (natSyms den ++ rb) oC yC mC w1 w2) rY (natSyms (n / den) ++ yC))
    rM (natSyms (n % den) ++ mC)⟩ : St DRStk (fun _ => Sym) (RReg R)) = _
  rw [rst_upd_Y, rst_upd_M]

theorem rDouble_eval (nC dC oC yC rest w1 w2 : List Sym) (hrest : TermOK rest) (x : ℕ)
    (v : RReg R) :
    ∃ v', Eval [] (rDouble (R := R)) ⟨v, rst nC dC oC yC (natSyms x ++ rest) w1 w2⟩
      ⟨v', rst nC dC oC yC (natSyms (x + x) ++ rest) w1 w2⟩ 3 ∧ v'.2 = v.2 := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨(rest.head?, v.2), Eval.seq (eval_peek' [] rM _ v _ rest.head? (by simp [natSyms_zero]))
      (Eval.ite_false (optIsBit_head?_of_termOK hrest) (skip_eval _ _)), rfl⟩
  · obtain ⟨d, l, hdl⟩ : ∃ d l, natSyms x = .bit d :: l := by
      unfold natSyms
      cases h : encodeNat x with
      | nil => exact absurd ((encodeNat_eq_nil_iff x).1 h) hx
      | cons d l => exact ⟨d, l.map Sym.bit, rfl⟩
    refine ⟨(some (.bit d), v.2),
      Eval.seq (eval_peek' [] rM _ v _ (some (.bit d)) (by simp [hdl]))
        (Eval.ite_true (by rfl) (eval_push' [] rM _ _ _ _ ?_)), rfl⟩
    rw [rst_upd_M, natSyms_add_self x hx]
    rfl

theorem rCmp_eval (nC oC yC rb rx w1 w2 : List Sym) (hrb : TermOK rb) (hrx : TermOK rx)
    (x den : ℕ) (v : RReg R) :
    Eval [] (rCmp (R := R)) ⟨v, rst nC (natSyms den ++ rb) oC yC (natSyms x ++ rx) w1 w2⟩
      ⟨(v.1, v.2.1, (some .mark, some .mark, ordOf x den), v.2.2.2),
        rst nC (natSyms den ++ rb) oC yC (natSyms x ++ rx) w1 w2⟩
      (12 * min (bitLen x) (bitLen den) + 15) := by
  have e := cmpNum_eval (k₁ := rM) (k₂ := rD) (t₁ := rY) (t₂ := rO) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) v.2.2.1 (encodeNat x) (encodeNat den) rx rb
    (rst nC (natSyms den ++ rb) oC yC (natSyms x ++ rx) w1 w2) hrx hrb rfl rfl
  rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat x) (normBits_encodeNat den), bitsVal_encodeNat,
    bitsVal_encodeNat] at e
  exact Eval.liftRegs (Lcmp2 R) e v rfl

theorem rRound_eval (nC dC oC rest mC w1 w2 : List Sym) (hrest : TermOK rest) (q : ℕ)
    (v : RReg R) (sg : Option Sym) (o : Ordering) (hsg : v.2.1 = sg) (ho : v.2.2.1.2.2 = o) :
    ∃ v' t, Eval [] (rRound (R := R)) ⟨v, rst nC dC oC (natSyms q ++ rest) mC w1 w2⟩
      ⟨v', rst nC dC oC (natSyms (q + if roundUp sg o then 1 else 0) ++ rest) mC w1 w2⟩ t ∧
      v'.2 = v.2 ∧ t ≤ 6 * bitLen q + 10 := by
  cases hr : roundUp sg o with
  | true =>
    obtain ⟨c, hc, e⟩ := inc_eval (k := rY) (t := rM) (by decide) [] v.1 (encodeNat q) rest
      (rst nC dC oC (natSyms q ++ rest) mC w1 w2) hrest rfl
    rw [← encodeNat_succ, rst_upd_Y] at e
    refine ⟨_, _, Eval.ite_true (by show roundUp v.2.1 v.2.2.1.2.2 = true; rw [hsg, ho]; exact hr)
      (liftFst e v rfl), rfl, ?_⟩
    have := ones_le_length (encodeNat q)
    change c + 1 ≤ 6 * (encodeNat q).length + 10
    omega
  | false =>
    exact ⟨v, 2, Eval.ite_false (by show roundUp v.2.1 v.2.2.1.2.2 = false; rw [hsg, ho]; exact hr)
      (skip_eval _ _), rfl, by omega⟩

theorem rOut_eval (nC dC oC rest mC w1 w2 : List Sym) (hrest : TermOK rest) (M : ℕ)
    (v : RReg R) (sg : Sym) (hsg : v.2.1 = some sg) :
    ∃ v' t, Eval [] (rOut (R := R)) ⟨v, rst nC dC oC (natSyms M ++ rest) mC w1 w2⟩
      ⟨v', rst nC dC ((if sg = .neg ∧ M ≠ 0 then Sym.neg else Sym.pos) :: (natSyms M ++ oC))
        (natSyms M ++ rest) mC w1 w2⟩ t ∧ v'.2 = v.2 ∧ t ≤ 7 * bitLen M + 10 := by
  have e1 : Eval [] (rCur (R := R) (copyBlock rY rO rM))
      ⟨v, rst nC dC oC (natSyms M ++ rest) mC w1 w2⟩
      ⟨(some .mark, v.2), rst nC dC (natSyms M ++ oC) (natSyms M ++ rest) mC w1 w2⟩
      (7 * bitLen M + 7) := by
    have e := copyBlock_eval (src := rY) (dst := rO) (tmp := rM) (by decide) (by decide)
      (by decide) [] v.1 (encodeNat M) rest (rst nC dC oC (natSyms M ++ rest) mC w1 w2) hrest rfl
    rw [rst_upd_O] at e
    exact liftFst e v rfl
  have e2 := eval_peek' [] rY (fun v o => (o, v.2)) ((some .mark, v.2) : RReg R)
    (rst nC dC (natSyms M ++ oC) (natSyms M ++ rest) mC w1 w2) (natSyms M ++ rest).head? rfl
  have hb := optIsBit_natSyms_head M rest hrest
  by_cases hc : sg = .neg ∧ M ≠ 0
  · rw [if_pos hc]
    have hcond : (decide (v.2.1 = some Sym.neg) && optIsBit (natSyms M ++ rest).head?) = true := by
      rw [hb, hsg, hc.1]
      simp [hc.2]
    have e3 : Eval [] (.push rO fun _ => .neg : Prog DRStk (fun _ => Sym) (RReg R))
        ⟨((natSyms M ++ rest).head?, v.2), rst nC dC (natSyms M ++ oC) (natSyms M ++ rest) mC w1 w2⟩
        ⟨((natSyms M ++ rest).head?, v.2),
          rst nC dC (Sym.neg :: (natSyms M ++ oC)) (natSyms M ++ rest) mC w1 w2⟩ 1 :=
      eval_push' [] rO _ _ _ _ (rst_upd_O ..)
    exact ⟨_, _, Eval.seq e1 (Eval.seq e2 (Eval.ite_true hcond e3)), rfl, by omega⟩
  · rw [if_neg hc]
    have hcond : (decide (v.2.1 = some Sym.neg) && optIsBit (natSyms M ++ rest).head?) = false := by
      rw [hb, hsg]
      by_cases hs : sg = .neg
      · have hM : M = 0 := by
          by_contra hM
          exact hc ⟨hs, hM⟩
        simp [hM]
      · simp [hs]
    have e3 : Eval [] (.push rO fun _ => .pos : Prog DRStk (fun _ => Sym) (RReg R))
        ⟨((natSyms M ++ rest).head?, v.2), rst nC dC (natSyms M ++ oC) (natSyms M ++ rest) mC w1 w2⟩
        ⟨((natSyms M ++ rest).head?, v.2),
          rst nC dC (Sym.pos :: (natSyms M ++ oC)) (natSyms M ++ rest) mC w1 w2⟩ 1 :=
      eval_push' [] rO _ _ _ _ (rst_upd_O ..)
    exact ⟨_, _, Eval.seq e1 (Eval.seq e2 (Eval.ite_false hcond e3)), rfl, by omega⟩

theorem rEpilogue_eval (z : ℤ) (ra dC oC yC mC w1 w2 : List Sym) (M x : ℕ) (v : RReg R)
    (hv : v.2.1 = some (sgnSym z)) :
    ∃ v' t, Eval [] (rEpilogue (R := R))
      ⟨v, rst (natSyms z.natAbs ++ ra) dC oC (natSyms M ++ .mark :: yC)
        (natSyms x ++ .mark :: mC) w1 w2⟩
      ⟨v', rst (intSyms z ++ ra) dC oC yC mC w1 w2⟩ t ∧ t ≤ 3 * bitLen M + 3 * bitLen x + 7 := by
  have e1 : Eval [] (rCur (R := R) (dropBits rY))
      ⟨v, rst (natSyms z.natAbs ++ ra) dC oC (natSyms M ++ .mark :: yC)
        (natSyms x ++ .mark :: mC) w1 w2⟩
      ⟨(some .mark, v.2), rst (natSyms z.natAbs ++ ra) dC oC (.mark :: yC)
        (natSyms x ++ .mark :: mC) w1 w2⟩ (3 * bitLen M + 2) := by
    have e := dropBits_eval rY [] v.1 (encodeNat M) (.mark :: yC)
      (rst (natSyms z.natAbs ++ ra) dC oC (natSyms M ++ .mark :: yC) (natSyms x ++ .mark :: mC)
        w1 w2) (TermOK.cons rfl _) rfl
    rw [rst_upd_Y] at e
    exact liftFst e v rfl
  have e2 : Eval [] (.pop rY fun v _ => v : Prog DRStk (fun _ => Sym) (RReg R))
      ⟨(some .mark, v.2), rst (natSyms z.natAbs ++ ra) dC oC (.mark :: yC)
        (natSyms x ++ .mark :: mC) w1 w2⟩
      ⟨(some .mark, v.2), rst (natSyms z.natAbs ++ ra) dC oC yC
        (natSyms x ++ .mark :: mC) w1 w2⟩ 1 :=
    eval_pop' [] rY _ _ _ _ .mark yC rfl (rst_upd_Y ..)
  have e3 : Eval [] (rCur (R := R) (dropBits rM))
      ⟨(some .mark, v.2), rst (natSyms z.natAbs ++ ra) dC oC yC (natSyms x ++ .mark :: mC) w1 w2⟩
      ⟨(some .mark, v.2), rst (natSyms z.natAbs ++ ra) dC oC yC (.mark :: mC) w1 w2⟩
      (3 * bitLen x + 2) := by
    have e := dropBits_eval rM [] (some .mark) (encodeNat x) (.mark :: mC)
      (rst (natSyms z.natAbs ++ ra) dC oC yC (natSyms x ++ .mark :: mC) w1 w2)
      (TermOK.cons rfl _) rfl
    rw [rst_upd_M] at e
    exact liftFst e (some .mark, v.2) rfl
  have e4 : Eval [] (.pop rM fun v _ => v : Prog DRStk (fun _ => Sym) (RReg R))
      ⟨(some .mark, v.2), rst (natSyms z.natAbs ++ ra) dC oC yC (.mark :: mC) w1 w2⟩
      ⟨(some .mark, v.2), rst (natSyms z.natAbs ++ ra) dC oC yC mC w1 w2⟩ 1 :=
    eval_pop' [] rM _ _ _ _ .mark mC rfl (rst_upd_M ..)
  have e5 : Eval [] (.push rN fun v => v.2.1.getD .sep : Prog DRStk (fun _ => Sym) (RReg R))
      ⟨(some .mark, v.2), rst (natSyms z.natAbs ++ ra) dC oC yC mC w1 w2⟩
      ⟨(some .mark, v.2), rst (intSyms z ++ ra) dC oC yC mC w1 w2⟩ 1 := by
    refine eval_push' [] rN _ _ _ _ ?_
    rw [rst_upd_N]
    show rst (v.2.1.getD .sep :: (natSyms z.natAbs ++ ra)) dC oC yC mC w1 w2 = _
    rw [hv]
    rfl
  exact ⟨_, _, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5))), by omega⟩

end Pieces

section Main

variable {m : ℕ} {R : Type}

/-- The whole program on `rst`-states. -/
theorem divRound_eval_rst {Cs : ℕ} {Ps : Prog (Loc 3 m) (fun _ => Sym) R} (hm : m ≤ 4)
    (hspec : SubSpec Cs Ps) (num : ℤ) (den : ℕ) (hd : 0 < den)
    (ra rb oC yC mC w1 w2 : List Sym) (hra : TermOK ra) (hrb : TermOK rb) (v : RReg R) :
    ∃ v' t, Eval [] (divRoundProg Ps)
      ⟨v, rst (intSyms num ++ ra) (natSyms den ++ rb) oC yC mC w1 w2⟩
      ⟨v', rst (intSyms num ++ ra) (natSyms den ++ rb) (intSyms (divRoundRatInt num den) ++ oC)
        yC mC w1 w2⟩ t ∧
      t ≤ (2 * Cs + 140) *
        (bitLen num.natAbs * bitLen den + bitLen num.natAbs + bitLen den + 1) := by
  rw [intSyms_divRound num den hd]
  have e1 := rPrologue_eval (R := R) num ra (natSyms den ++ rb) oC yC mC w1 w2 v
  obtain ⟨w, t2, e2, ht2⟩ := rDivMod_eval hm hspec num.natAbs den hd ra rb oC (.mark :: yC)
    (.mark :: mC) w1 w2 hra hrb (v.1, some (sgnSym num), v.2.2)
  obtain ⟨v3, e3, hv3⟩ := rDouble_eval (R := R) (natSyms num.natAbs ++ ra) (natSyms den ++ rb) oC
    (natSyms (num.natAbs / den) ++ .mark :: yC) (.mark :: mC) w1 w2 (TermOK.cons rfl _)
    (num.natAbs % den) ((Ldm R).set (v.1, some (sgnSym num), v.2.2) w)
  have e4 := rCmp_eval (R := R) (natSyms num.natAbs ++ ra) oC
    (natSyms (num.natAbs / den) ++ .mark :: yC) rb (.mark :: mC) w1 w2 hrb (TermOK.cons rfl _)
    (num.natAbs % den + num.natAbs % den) den v3
  have hsg4 : v3.2.1 = some (sgnSym num) := congrArg Prod.fst hv3
  obtain ⟨v5, t5, e5, hv5, ht5⟩ := rRound_eval (R := R) (natSyms num.natAbs ++ ra)
    (natSyms den ++ rb) oC (.mark :: yC)
    (natSyms (num.natAbs % den + num.natAbs % den) ++ .mark :: mC) w1 w2 (TermOK.cons rfl _)
    (num.natAbs / den)
    ((v3.1, v3.2.1, (some .mark, some .mark, ordOf (num.natAbs % den + num.natAbs % den) den),
      v3.2.2.2) : RReg R)
    (some (sgnSym num)) (ordOf (num.natAbs % den + num.natAbs % den) den) hsg4 rfl
  obtain ⟨v6, t6, e6, hv6, ht6⟩ := rOut_eval (R := R) (natSyms num.natAbs ++ ra)
    (natSyms den ++ rb) oC (.mark :: yC)
    (natSyms (num.natAbs % den + num.natAbs % den) ++ .mark :: mC) w1 w2 (TermOK.cons rfl _)
    (num.natAbs / den + if roundUp (some (sgnSym num))
      (ordOf (num.natAbs % den + num.natAbs % den) den) then 1 else 0)
    v5 (sgnSym num) (by rw [hv5]; exact hsg4)
  obtain ⟨v7, t7, e7, ht7⟩ := rEpilogue_eval (R := R) num ra (natSyms den ++ rb)
    ((if sgnSym num = .neg ∧ (num.natAbs / den + if roundUp (some (sgnSym num))
        (ordOf (num.natAbs % den + num.natAbs % den) den) then 1 else 0) ≠ 0
      then Sym.neg else Sym.pos) ::
      (natSyms (num.natAbs / den + if roundUp (some (sgnSym num))
        (ordOf (num.natAbs % den + num.natAbs % den) den) then 1 else 0) ++ oC))
    yC mC w1 w2
    (num.natAbs / den + if roundUp (some (sgnSym num))
      (ordOf (num.natAbs % den + num.natAbs % den) den) then 1 else 0)
    (num.natAbs % den + num.natAbs % den) v6 (by rw [hv6, hv5]; exact hsg4)
  refine ⟨v7, _, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 e7))))), ?_⟩
  -- cost
  have hq : bitLen (num.natAbs / den) ≤ bitLen num.natAbs := bitLen_mono (Nat.div_le_self _ _)
  have hM : bitLen (num.natAbs / den + if roundUp (some (sgnSym num))
      (ordOf (num.natAbs % den + num.natAbs % den) den) then 1 else 0) ≤ bitLen num.natAbs + 1 := by
    have h1 : (num.natAbs / den + if roundUp (some (sgnSym num))
        (ordOf (num.natAbs % den + num.natAbs % den) den) then 1 else 0) ≤ num.natAbs / den + 1 := by
      split_ifs <;> omega
    have := bitLen_succ_le (num.natAbs / den)
    have := bitLen_mono h1
    omega
  have hr : bitLen (num.natAbs % den + num.natAbs % den) ≤ bitLen den + 1 :=
    bitLen_lt_two_mul (by have := Nat.mod_lt num.natAbs hd; omega)
  have hmin : min (bitLen (num.natAbs % den + num.natAbs % den)) (bitLen den) ≤ bitLen den :=
    Nat.min_le_right _ _
  have hexp : (2 * Cs + 140) *
      (bitLen num.natAbs * bitLen den + bitLen num.natAbs + bitLen den + 1) =
      (2 * Cs + 70) * (bitLen num.natAbs * bitLen den + bitLen num.natAbs + bitLen den + 1) +
        70 * (bitLen num.natAbs * bitLen den + bitLen num.natAbs + bitLen den + 1) := by
    ring
  omega

/-- **The `divRound` contract body** for `divRoundProg Ps`. -/
theorem divRoundProg_spec {Cs : ℕ} {Ps : Prog (Loc 3 m) (fun _ => Sym) R} (hm : m ≤ 4)
    (hspec : SubSpec Cs Ps) (num : ℤ) (den : ℕ) (ra rb : List Sym) (S : DRStk → List Sym)
    (hd : 0 < den) (hra : TermOK ra) (hrb : TermOK rb) (hN : S rN = intSyms num ++ ra)
    (hD : S rD = natSyms den ++ rb) :
    Runs (divRoundProg Ps) S (Function.update S rO (intSyms (divRoundRatInt num den) ++ S rO))
      (fun _ => True)
      ((2 * Cs + 140) * (bitLen num.natAbs * bitLen den + bitLen num.natAbs + bitLen den + 1)) := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := divRound_eval_rst hm hspec num den hd ra rb (S rO) (S rY) (S rM)
    (S rW1) (S rW2) hra hrb v
  rw [← hN, ← hD, rst_eta] at e
  exact ⟨v', t, by rw [upd_O]; exact e, trivial, ht⟩

end Main

/-- **W6a.divRound**, from the subtraction contract of W3. -/
theorem W6a_divRound_holds (hsub : W3_subNat) : W6a_divRound := by
  obtain ⟨Cs, hCs⟩ := hsub
  obtain ⟨m, R, _, Ps, hm, hfin, hne, hcl, hspec⟩ := hCs ()
  refine ⟨2 * Cs + 140, fun _ => ⟨4, RReg R, fun _ => (), divRoundProg Ps, by decide, ?_, ?_,
    divRoundProg_closed Ps hcl, ?_⟩⟩
  · haveI := hfin
    infer_instance
  · obtain ⟨r⟩ := hne
    exact ⟨(none, none, (none, none, .eq), (none, false, (none, none, .eq), r))⟩
  · intro num den ra rb S hd hra hrb hN hD
    exact divRoundProg_spec hm hspec num den ra rb S hd hra hrb hN hD

/-- **W6a**: both long-division contracts, from `W3_subNat`. -/
theorem W6a_holds (hsub : W3_subNat) : W6a_divModNat ∧ W6a_divRound :=
  ⟨W6a_divModNat_holds hsub, W6a_divRound_holds hsub⟩

#assert_std_axioms call_eval_upd2 optIsBit_natSyms_head bitLen_succ_le rPrologue_eval
  rDivMod_eval rDouble_eval rCmp_eval rRound_eval rOut_eval rEpilogue_eval divRound_eval_rst
  divRoundProg_spec W6a_divRound_holds W6a_holds

end WP.W6a
