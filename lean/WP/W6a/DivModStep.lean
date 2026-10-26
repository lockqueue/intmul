import WP.W6a.DivModProg
import Mathlib.Tactic.Ring

/-!
# WP.W6a.DivModStep — one iteration of the long-division loop

`body_eval`: from the loop invariant `invSt S aBits q r (bit c :: tl)` (quotient so far `q`,
remainder `r < b`), one iteration reaches `invSt S (bit c :: aBits) q' r' tl`, where
`(q', r') = if b ≤ 2r + c then (2q + 1, 2r + c − b) else (2q, 2r + c)`. It takes at most
`(2·Cs + 50)·(|b| + 1)` steps, where `Cs` is the cost constant of the subtractor `Ps`.

The pieces (`stepIn_eval`, `cmpXB_eval`, `sub_eval`, `geBranch_eval`, `ltBranch_eval`) are exact
or bounded evaluations on `st`-states. The library macros (`dropBits`, `copyBlock`, `moveBlock`)
are lifted onto the current-symbol register by `liftFst`.
-/

namespace WP.W6a

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- The specification part of `W3_subNat`, for one program `P` with cost constant `C`. -/
def SubSpec {m : ℕ} {R : Type} (C : ℕ) (P : Prog (Loc 3 m) (fun _ => Sym) R) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry → b ≤ a →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Stacks of the loop invariant: `A` holds `aBits`, `Q` the quotient so far `q`, `T` the
remaining dividend bits `tl` (MSB on top) over a mark, `X` the remainder `r` over a mark, and `Z`
a mark. `B` and `R` are as in `S`. -/
def invSt (S : DStk → List Sym) (aBits : List Sym) (q r : ℕ) (tl : List Sym) :
    DStk → List Sym :=
  st aBits (S sB) (natSyms q ++ S sQ) (S sR) (tl ++ .mark :: S sT) (natSyms r ++ .mark :: S sX)
    (.mark :: S sZ)

section Steps

variable {m : ℕ} {R : Type}

/-! ### Library macros on `st`-states -/

theorem dropX_eval (aC bC qC rC tC zC rest : List Sym) (hrest : TermOK rest) (x : ℕ)
    (v : DReg R) :
    Eval [] (liftCur (R := R) (dropBits sX)) ⟨v, st aC bC qC rC tC (natSyms x ++ rest) zC⟩
      ⟨(rest.head?, v.2), st aC bC qC rC tC rest zC⟩ (3 * bitLen x + 2) := by
  have e := dropBits_eval sX [] v.1 (encodeNat x) rest
    (st aC bC qC rC tC (natSyms x ++ rest) zC) hrest rfl
  rw [st_upd_X] at e
  exact liftFst e v rfl

theorem dropZ_eval (aC bC qC rC tC xC rest : List Sym) (hrest : TermOK rest) (z : ℕ)
    (v : DReg R) :
    Eval [] (liftCur (R := R) (dropBits sZ)) ⟨v, st aC bC qC rC tC xC (natSyms z ++ rest)⟩
      ⟨(rest.head?, v.2), st aC bC qC rC tC xC rest⟩ (3 * bitLen z + 2) := by
  have e := dropBits_eval sZ [] v.1 (encodeNat z) rest
    (st aC bC qC rC tC xC (natSyms z ++ rest)) hrest rfl
  rw [st_upd_Z] at e
  exact liftFst e v rfl

theorem copyZX_eval (aC bC qC rC tC xC rest : List Sym) (hrest : TermOK rest) (z : ℕ)
    (v : DReg R) :
    Eval [] (liftCur (R := R) (copyBlock sZ sX sT)) ⟨v, st aC bC qC rC tC xC (natSyms z ++ rest)⟩
      ⟨(some .mark, v.2), st aC bC qC rC tC (natSyms z ++ xC) (natSyms z ++ rest)⟩
      (7 * bitLen z + 7) := by
  have e := copyBlock_eval (src := sZ) (dst := sX) (tmp := sT) (by decide) (by decide)
    (by decide) [] v.1 (encodeNat z) rest (st aC bC qC rC tC xC (natSyms z ++ rest)) hrest rfl
  rw [st_upd_X] at e
  exact liftFst e v rfl

theorem copyXR_eval (aC bC qC rC tC zC rest : List Sym) (hrest : TermOK rest) (x : ℕ)
    (v : DReg R) :
    Eval [] (liftCur (R := R) (copyBlock sX sR sT)) ⟨v, st aC bC qC rC tC (natSyms x ++ rest) zC⟩
      ⟨(some .mark, v.2), st aC bC qC (natSyms x ++ rC) tC (natSyms x ++ rest) zC⟩
      (7 * bitLen x + 7) := by
  have e := copyBlock_eval (src := sX) (dst := sR) (tmp := sT) (by decide) (by decide)
    (by decide) [] v.1 (encodeNat x) rest (st aC bC qC rC tC (natSyms x ++ rest) zC) hrest rfl
  rw [st_upd_R] at e
  exact liftFst e v rfl

theorem moveAT_eval (bC qC rC tC xC zC ra : List Sym) (hra : TermOK ra) (a : ℕ) (v : DReg R) :
    Eval [] (liftCur (R := R) (moveBlock sA sT)) ⟨v, st (natSyms a ++ ra) bC qC rC tC xC zC⟩
      ⟨(ra.head?, v.2), st ra bC qC rC ((encodeNat a).reverse.map Sym.bit ++ tC) xC zC⟩
      (3 * bitLen a + 4) := by
  have e := moveBlock_eval (src := sA) (dst := sT) (by decide) [] v.1 (encodeNat a) ra
    (st (natSyms a ++ ra) bC qC rC tC xC zC) hra rfl
  rw [st_upd_A, st_upd_T] at e
  exact liftFst e v rfl

/-! ### The pieces of the loop body -/

theorem stepIn_eval (aC bC qC rC tC zC rx : List Sym) (hrx : TermOK rx) (xr : ℕ) (c : Bool)
    (v : DReg R) :
    ∃ v' t, Eval [] (stepIn (R := R))
      ⟨v, st aC bC qC rC (.bit c :: tC) (natSyms xr ++ rx) zC⟩
      ⟨v', st (.bit c :: aC) bC qC rC tC (natSyms (xr + xr + c.toNat) ++ rx) zC⟩ t ∧
      v'.2 = v.2 ∧ t ≤ 6 := by
  have e1 : Eval [] (popCur (R := R) sT)
      ⟨v, st aC bC qC rC (.bit c :: tC) (natSyms xr ++ rx) zC⟩
      ⟨(some (.bit c), v.2), st aC bC qC rC tC (natSyms xr ++ rx) zC⟩ 1 :=
    eval_pop' [] sT _ v _ _ (.bit c) tC rfl (st_upd_T ..)
  have e2 : Eval [] (pushCur (R := R) sA)
      ⟨(some (.bit c), v.2), st aC bC qC rC tC (natSyms xr ++ rx) zC⟩
      ⟨(some (.bit c), v.2), st (.bit c :: aC) bC qC rC tC (natSyms xr ++ rx) zC⟩ 1 :=
    eval_push' [] sA _ _ _ _ (st_upd_A ..)
  cases c with
  | true =>
    have e3 : Eval [] (dblAdd (R := R))
        ⟨(some (.bit true), v.2), st (.bit true :: aC) bC qC rC tC (natSyms xr ++ rx) zC⟩
        ⟨(some (.bit true), v.2),
          st (.bit true :: aC) bC qC rC tC (natSyms (xr + xr + 1) ++ rx) zC⟩ 2 :=
      Eval.ite_true (by rfl)
        (eval_push' [] sX _ _ _ _ (by rw [st_upd_X, natSyms_add_add_one]; rfl))
    exact ⟨_, _, Eval.seq e1 (Eval.seq e2 e3), rfl, by omega⟩
  | false =>
    by_cases hx : xr = 0
    · subst hx
      have e3 : Eval [] (dblAdd (R := R))
          ⟨(some (.bit false), v.2), st (.bit false :: aC) bC qC rC tC (natSyms 0 ++ rx) zC⟩
          ⟨(rx.head?, v.2), st (.bit false :: aC) bC qC rC tC (natSyms 0 ++ rx) zC⟩ 4 := by
        refine Eval.ite_false (by rfl) (Eval.seq (eval_peek' [] sX _ _ _ rx.head? ?_)
          (Eval.ite_false ?_ (skip_eval _ _)))
        · simp [natSyms_zero]
        · exact optIsBit_head?_of_termOK hrx
      exact ⟨_, _, Eval.seq e1 (Eval.seq e2 e3), rfl, by omega⟩
    · obtain ⟨d, l, hdl⟩ : ∃ d l, natSyms xr = .bit d :: l := by
        unfold natSyms
        cases h : encodeNat xr with
        | nil => exact absurd ((encodeNat_eq_nil_iff xr).1 h) hx
        | cons d l => exact ⟨d, l.map Sym.bit, rfl⟩
      have e3 : Eval [] (dblAdd (R := R))
          ⟨(some (.bit false), v.2), st (.bit false :: aC) bC qC rC tC (natSyms xr ++ rx) zC⟩
          ⟨(some (.bit d), v.2),
            st (.bit false :: aC) bC qC rC tC (natSyms (xr + xr) ++ rx) zC⟩ 4 := by
        refine Eval.ite_false (by rfl) (Eval.seq (eval_peek' [] sX _ _ _ (some (.bit d)) ?_)
          (Eval.ite_true (by rfl) (eval_push' [] sX _ _ _ _ ?_)))
        · simp [hdl]
        · rw [st_upd_X, natSyms_add_self xr hx]; rfl
      exact ⟨_, _, Eval.seq e1 (Eval.seq e2 e3), rfl, by omega⟩

theorem cmpXB_eval (aC qC rC tC zC rb rx : List Sym) (hrb : TermOK rb) (hrx : TermOK rx)
    (x b : ℕ) (v : DReg R) :
    Eval [] (cmpXB (R := R)) ⟨v, st aC (natSyms b ++ rb) qC rC tC (natSyms x ++ rx) zC⟩
      ⟨(v.1, v.2.1, (some .mark, some .mark, ordOf x b), v.2.2.2),
        st aC (natSyms b ++ rb) qC rC tC (natSyms x ++ rx) zC⟩
      (12 * min (bitLen x) (bitLen b) + 15) := by
  have e := cmpNum_eval (k₁ := sX) (k₂ := sB) (t₁ := sZ) (t₂ := sR) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) v.2.2.1 (encodeNat x) (encodeNat b) rx rb
    (st aC (natSyms b ++ rb) qC rC tC (natSyms x ++ rx) zC) hrx hrb rfl rfl
  rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat x) (normBits_encodeNat b), bitsVal_encodeNat,
    bitsVal_encodeNat] at e
  exact Eval.liftRegs (Lcmp R) e v rfl

theorem sub_eval {Cs : ℕ} {Ps : Prog (Loc 3 m) (fun _ => Sym) R} (hm : m ≤ 4)
    (hspec : SubSpec Cs Ps) (aC qC rC tC zC rb rx : List Sym) (hrb : TermOK rb)
    (hrx : TermOK rx) (x b : ℕ) (hge : b ≤ x) (v : DReg R) :
    ∃ w t, Eval [] (call subStk (Lsub R) Ps)
      ⟨v, st aC (natSyms b ++ rb) qC rC tC (natSyms x ++ rx) zC⟩
      ⟨(Lsub R).set v w, st aC (natSyms b ++ rb) qC rC tC (natSyms x ++ rx)
        (natSyms (x - b) ++ zC)⟩ t ∧
      t ≤ Cs * (bitLen x + bitLen b + 1) := by
  obtain ⟨w, t, e, -, ht⟩ := call_eval_upd
    (B := st aC (natSyms b ++ rb) qC rC tC (natSyms x ++ rx) zC) (subStk_injective hm) (Lsub R)
    (.inl 2) _ (hspec x b rx rb (st aC (natSyms b ++ rb) qC rC tC (natSyms x ++ rx) zC ∘ subStk)
      hrx hrb hge rfl rfl) v
  refine ⟨w, t, e.of_eq ?_ rfl, ht⟩
  show (⟨(Lsub R).set v w, Function.update (st aC (natSyms b ++ rb) qC rC tC (natSyms x ++ rx) zC)
    sZ (natSyms (x - b) ++ zC)⟩ : St DStk (fun _ => Sym) (DReg R)) = _
  rw [st_upd_Z]

theorem geBranch_eval {Cs : ℕ} {Ps : Prog (Loc 3 m) (fun _ => Sym) R} (hm : m ≤ 4)
    (hspec : SubSpec Cs Ps) (aC qC rC tC rb sx sz : List Sym) (hrb : TermOK rb) (x b : ℕ)
    (hge : b ≤ x) (v : DReg R) :
    ∃ v' t, Eval [] (geBranch Ps)
      ⟨v, st aC (natSyms b ++ rb) qC rC tC (natSyms x ++ .mark :: sx) (.mark :: sz)⟩
      ⟨v', st aC (natSyms b ++ rb) (.bit true :: qC) rC tC (natSyms (x - b) ++ .mark :: sx)
        (.mark :: sz)⟩ t ∧
      v'.2.1 = true ∧ t ≤ Cs * (bitLen x + bitLen b + 1) + 13 * bitLen x + 13 := by
  obtain ⟨w, t1, e1, ht1⟩ := sub_eval hm hspec aC qC rC tC (.mark :: sz) rb (.mark :: sx) hrb
    (TermOK.cons rfl _) x b hge v
  have e2 := dropX_eval (R := R) aC (natSyms b ++ rb) qC rC tC (natSyms (x - b) ++ .mark :: sz)
    (.mark :: sx) (TermOK.cons rfl _) x ((Lsub R).set v w)
  have e3 := copyZX_eval (R := R) aC (natSyms b ++ rb) qC rC tC (.mark :: sx) (.mark :: sz)
    (TermOK.cons rfl _) (x - b) (some .mark, ((Lsub R).set v w).2)
  have e4 := dropZ_eval (R := R) aC (natSyms b ++ rb) qC rC tC (natSyms (x - b) ++ .mark :: sx)
    (.mark :: sz) (TermOK.cons rfl _) (x - b) (some .mark, ((Lsub R).set v w).2)
  have e5 : Eval [] (pushSym (R := R) sQ (.bit true))
      ⟨(some .mark, ((Lsub R).set v w).2),
        st aC (natSyms b ++ rb) qC rC tC (natSyms (x - b) ++ .mark :: sx) (.mark :: sz)⟩
      ⟨(some .mark, ((Lsub R).set v w).2),
        st aC (natSyms b ++ rb) (.bit true :: qC) rC tC (natSyms (x - b) ++ .mark :: sx)
          (.mark :: sz)⟩ 1 :=
    eval_push' [] sQ _ _ _ _ (st_upd_Q ..)
  have e6 := Eval.load [] (fun v : DReg R => (v.1, true, v.2.2))
    (some .mark, ((Lsub R).set v w).2)
    (st aC (natSyms b ++ rb) (.bit true :: qC) rC tC (natSyms (x - b) ++ .mark :: sx)
      (.mark :: sz))
  refine ⟨_, _, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6)))), rfl, ?_⟩
  have := bitLen_mono (Nat.sub_le x b)
  omega

theorem ltBranch_eval (aC bC rC tC xC zC qC : List Sym) (q : ℕ) (v : DReg R)
    (hv : v.2.1 = decide (q ≠ 0)) :
    Eval [] (ltBranch (R := R)) ⟨v, st aC bC (natSyms q ++ qC) rC tC xC zC⟩
      ⟨v, st aC bC (natSyms (q + q) ++ qC) rC tC xC zC⟩ 2 := by
  by_cases hq : q = 0
  · subst hq
    have hv' : v.2.1 = false := by simpa using hv
    exact Eval.ite_false hv' (skip_eval _ _)
  · have hv' : v.2.1 = true := by simpa [hq] using hv
    refine Eval.ite_true hv' (eval_push' [] sQ _ _ _ _ ?_)
    rw [st_upd_Q, natSyms_add_self q hq]; rfl

/-! ### One iteration -/

theorem body_eval {Cs : ℕ} {Ps : Prog (Loc 3 m) (fun _ => Sym) R} (hm : m ≤ 4)
    (hspec : SubSpec Cs Ps) (S : DStk → List Sym) (rb : List Sym) (hrb : TermOK rb) (b : ℕ)
    (hB : S sB = natSyms b ++ rb) (aBits tl : List Sym) (c : Bool) (q r : ℕ) (hr : r < b)
    (v : DReg R) (hv : v.2.1 = decide (q ≠ 0)) :
    ∃ v' t, Eval [] (body Ps) ⟨v, invSt S aBits q r (.bit c :: tl)⟩
      ⟨v', invSt S (.bit c :: aBits)
        (if b ≤ r + r + c.toNat then q + q + 1 else q + q)
        (if b ≤ r + r + c.toNat then r + r + c.toNat - b else r + r + c.toNat) tl⟩ t ∧
      v'.1 = (tl ++ Sym.mark :: S sT).head? ∧
      v'.2.1 = decide ((if b ≤ r + r + c.toNat then q + q + 1 else q + q) ≠ 0) ∧
      t ≤ (2 * Cs + 50) * (bitLen b + 1) := by
  simp only [invSt, hB]
  obtain ⟨v1, t1, e1, hv1, ht1⟩ := stepIn_eval (R := R) aBits (natSyms b ++ rb)
    (natSyms q ++ S sQ) (S sR) (tl ++ .mark :: S sT) (.mark :: S sZ) (.mark :: S sX)
    (TermOK.cons rfl _) r c v
  have e2 := cmpXB_eval (R := R) (.bit c :: aBits) (natSyms q ++ S sQ) (S sR)
    (tl ++ .mark :: S sT) (.mark :: S sZ) rb (.mark :: S sX) hrb (TermOK.cons rfl _)
    (r + r + c.toNat) b v1
  have hc1 : c.toNat ≤ 1 := Bool.toNat_le c
  have hx2 : bitLen (r + r + c.toNat) ≤ bitLen b + 1 := bitLen_lt_two_mul (by omega)
  have hmin : min (bitLen (r + r + c.toNat)) (bitLen b) ≤ bitLen b := Nat.min_le_right _ _
  have hexp : (2 * Cs + 50) * (bitLen b + 1) = Cs * (2 * bitLen b + 2) + 50 * bitLen b + 50 := by
    ring
  by_cases hge : b ≤ r + r + c.toNat
  · rw [if_pos hge, if_pos hge, natSyms_add_add_one]
    obtain ⟨v3, t3, e3, hv3, ht3⟩ := geBranch_eval hm hspec (.bit c :: aBits) (natSyms q ++ S sQ)
      (S sR) (tl ++ .mark :: S sT) rb (S sX) (S sZ) hrb (r + r + c.toNat) b hge
      (v1.1, v1.2.1, (some .mark, some .mark, ordOf (r + r + c.toNat) b), v1.2.2.2)
    have hc3 : notLt (ordOf (r + r + c.toNat) b) = true := by
      rw [notLt_ordOf]
      exact decide_eq_true hge
    have e4 := eval_peek' [] sT (fun v o => (o, v.2)) v3
      (st (.bit c :: aBits) (natSyms b ++ rb) (.bit true :: (natSyms q ++ S sQ)) (S sR)
        (tl ++ .mark :: S sT) (natSyms (r + r + c.toNat - b) ++ .mark :: S sX) (.mark :: S sZ))
      (tl ++ .mark :: S sT).head? rfl
    refine ⟨_, _, Eval.seq e1 (Eval.seq e2 (Eval.seq (Eval.ite_true hc3 e3) e4)), rfl, ?_, ?_⟩
    · show v3.2.1 = _
      rw [hv3]
      simp
    · have hmul : Cs * (bitLen (r + r + c.toNat) + bitLen b + 1) ≤ Cs * (2 * bitLen b + 2) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  · rw [if_neg hge, if_neg hge]
    have hc3 : notLt (ordOf (r + r + c.toNat) b) = false := by
      rw [notLt_ordOf]
      exact decide_eq_false hge
    have e3 := ltBranch_eval (R := R) (.bit c :: aBits) (natSyms b ++ rb) (S sR)
      (tl ++ .mark :: S sT) (natSyms (r + r + c.toNat) ++ .mark :: S sX) (.mark :: S sZ) (S sQ) q
      (v1.1, v1.2.1, (some .mark, some .mark, ordOf (r + r + c.toNat) b), v1.2.2.2)
      (by show v1.2.1 = _; rw [hv1]; exact hv)
    have e4 := eval_peek' [] sT (fun v o => (o, v.2))
      ((v1.1, v1.2.1, (some .mark, some .mark, ordOf (r + r + c.toNat) b), v1.2.2.2) : DReg R)
      (st (.bit c :: aBits) (natSyms b ++ rb) (natSyms (q + q) ++ S sQ) (S sR)
        (tl ++ .mark :: S sT) (natSyms (r + r + c.toNat) ++ .mark :: S sX) (.mark :: S sZ))
      (tl ++ .mark :: S sT).head? rfl
    refine ⟨_, _, Eval.seq e1 (Eval.seq e2 (Eval.seq (Eval.ite_false hc3 e3) e4)), rfl, ?_, ?_⟩
    · show v1.2.1 = _
      rw [hv1, hv]
      exact decide_eq_decide.mpr (by omega)
    · omega

end Steps

#assert_std_axioms dropX_eval dropZ_eval copyZX_eval copyXR_eval moveAT_eval stepIn_eval
  cmpXB_eval sub_eval geBranch_eval ltBranch_eval body_eval

end WP.W6a
