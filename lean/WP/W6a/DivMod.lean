import WP.W6a.DivModStep

/-!
# WP.W6a.DivMod — `W6a_divModNat` from `W3_subNat`

* `loop_eval`: the main loop consumes the remaining MSB-first dividend bits `s`. Its invariant
  `loopSt` keeps the quotient `h / b` on `Q` and the remainder `h % b` on `X`, where `h` is the
  value of the processed prefix (`div_step`). Cost `|s|·(K + 1) + 1` with
  `K = (2·Cs + 50)·(|b| + 1)`.
* `divModProg_spec`: the contract's `Runs` for `divModProg Ps`, with cost
  `(2·Cs + 70)·(|a|·|b| + |a| + |b| + 1)`.
* **`W6a_divModNat_holds : W3_subNat → W6a_divModNat`** (the `W3_subNat` sub-kernel contract
  is a hypothesis).
-/

namespace WP.W6a

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- Stacks of the main loop after the MSB-first prefix `p` of the dividend has been processed
(value `h = bitsVal p.reverse`); the bits `s` remain. -/
def loopSt (S : DStk → List Sym) (ra : List Sym) (b : ℕ) (p s : List Bool) : DStk → List Sym :=
  invSt S (p.reverse.map Sym.bit ++ ra) (bitsVal p.reverse / b) (bitsVal p.reverse % b)
    (s.map Sym.bit)

section Loop

variable {m : ℕ} {R : Type}

theorem loop_eval {Cs : ℕ} {Ps : Prog (Loc 3 m) (fun _ => Sym) R} (hm : m ≤ 4)
    (hspec : SubSpec Cs Ps) (S : DStk → List Sym) (ra rb : List Sym) (hrb : TermOK rb) (b : ℕ)
    (hb : 0 < b) (hB : S sB = natSyms b ++ rb) :
    ∀ (s p : List Bool) (v : DReg R), v.1 = (s.map Sym.bit ++ Sym.mark :: S sT).head? →
      v.2.1 = decide (bitsVal p.reverse / b ≠ 0) →
      ∃ v' t, Eval [] (.loop (fun v => optIsBit v.1) (body Ps)) ⟨v, loopSt S ra b p s⟩
        ⟨v', loopSt S ra b (p ++ s) []⟩ t ∧
        t ≤ s.length * ((2 * Cs + 50) * (bitLen b + 1) + 1) + 1
  | [], p, v, hv1, _ => by
    refine ⟨v, 1, (Eval.loop_false ?_).of_eq (by rw [List.append_nil]) rfl, by simp⟩
    show optIsBit v.1 = false
    rw [hv1]; rfl
  | c :: s, p, v, hv1, hv2 => by
    have hr : bitsVal p.reverse % b < b := Nat.mod_lt _ hb
    obtain ⟨v1, t1, e1, hv1', hv2', ht1⟩ := body_eval hm hspec S rb hrb b hB
      (p.reverse.map Sym.bit ++ ra) (s.map Sym.bit) c (bitsVal p.reverse / b)
      (bitsVal p.reverse % b) hr v hv2
    have hrev : (p ++ [c]).reverse = c :: p.reverse := by simp
    obtain ⟨hdiv, hmod⟩ := div_step (h := bitsVal p.reverse) hb (Bool.toNat_le c)
    have hst : loopSt S ra b (p ++ [c]) s = invSt S (.bit c :: (p.reverse.map Sym.bit ++ ra))
        (if b ≤ bitsVal p.reverse % b + bitsVal p.reverse % b + c.toNat then
          bitsVal p.reverse / b + bitsVal p.reverse / b + 1 else
          bitsVal p.reverse / b + bitsVal p.reverse / b)
        (if b ≤ bitsVal p.reverse % b + bitsVal p.reverse % b + c.toNat then
          bitsVal p.reverse % b + bitsVal p.reverse % b + c.toNat - b else
          bitsVal p.reverse % b + bitsVal p.reverse % b + c.toNat)
        (s.map Sym.bit) := by
      rw [loopSt, hrev, bitsVal_cons, hdiv, hmod]; rfl
    rw [← hst] at e1
    have hv2'' : v1.2.1 = decide (bitsVal (p ++ [c]).reverse / b ≠ 0) := by
      rw [hv2', hrev, bitsVal_cons, hdiv]
    obtain ⟨v2, t2, e2, ht2⟩ := loop_eval hm hspec S ra rb hrb b hb hB s (p ++ [c]) v1 hv1' hv2''
    refine ⟨v2, t1 + t2 + 1, (Eval.loop_true ?_ e1 e2).of_eq ?_ rfl, ?_⟩
    · show optIsBit v.1 = true
      rw [hv1]; rfl
    · rw [List.append_assoc, List.singleton_append]
    · rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- The whole program on `st`-states. -/
theorem divMod_eval_st {Cs : ℕ} {Ps : Prog (Loc 3 m) (fun _ => Sym) R} (hm : m ≤ 4)
    (hspec : SubSpec Cs Ps) (a b : ℕ) (hb : 0 < b) (ra rb qC rC tC xC zC : List Sym)
    (hra : TermOK ra) (hrb : TermOK rb) (v : DReg R) :
    ∃ v' t, Eval [] (divModProg Ps)
      ⟨v, st (natSyms a ++ ra) (natSyms b ++ rb) qC rC tC xC zC⟩
      ⟨v', st (natSyms a ++ ra) (natSyms b ++ rb) (natSyms (a / b) ++ qC)
        (natSyms (a % b) ++ rC) tC xC zC⟩ t ∧
      t ≤ (2 * Cs + 70) * (bitLen a * bitLen b + bitLen a + bitLen b + 1) := by
  -- setup: marks, flag, move the dividend to `T`, look at its top
  have e1 : Eval [] (pushSym (R := R) sT .mark)
      ⟨v, st (natSyms a ++ ra) (natSyms b ++ rb) qC rC tC xC zC⟩
      ⟨v, st (natSyms a ++ ra) (natSyms b ++ rb) qC rC (.mark :: tC) xC zC⟩ 1 :=
    eval_push' [] sT _ _ _ _ (st_upd_T ..)
  have e2 : Eval [] (pushSym (R := R) sX .mark)
      ⟨v, st (natSyms a ++ ra) (natSyms b ++ rb) qC rC (.mark :: tC) xC zC⟩
      ⟨v, st (natSyms a ++ ra) (natSyms b ++ rb) qC rC (.mark :: tC) (.mark :: xC) zC⟩ 1 :=
    eval_push' [] sX _ _ _ _ (st_upd_X ..)
  have e3 : Eval [] (pushSym (R := R) sZ .mark)
      ⟨v, st (natSyms a ++ ra) (natSyms b ++ rb) qC rC (.mark :: tC) (.mark :: xC) zC⟩
      ⟨v, st (natSyms a ++ ra) (natSyms b ++ rb) qC rC (.mark :: tC) (.mark :: xC)
        (.mark :: zC)⟩ 1 :=
    eval_push' [] sZ _ _ _ _ (st_upd_Z ..)
  have e4 := Eval.load [] (fun v : DReg R => (v.1, false, v.2.2)) v
    (st (natSyms a ++ ra) (natSyms b ++ rb) qC rC (.mark :: tC) (.mark :: xC) (.mark :: zC))
  have e5 := moveAT_eval (R := R) (natSyms b ++ rb) qC rC (.mark :: tC) (.mark :: xC)
    (.mark :: zC) ra hra a (v.1, false, v.2.2)
  have e6 := eval_peek' [] sT (fun v o => (o, v.2)) (ra.head?, false, v.2.2)
    (st ra (natSyms b ++ rb) qC rC ((encodeNat a).reverse.map Sym.bit ++ .mark :: tC)
      (.mark :: xC) (.mark :: zC))
    ((encodeNat a).reverse.map Sym.bit ++ .mark :: tC).head? rfl
  -- the main loop
  have hL0 : loopSt (st (natSyms a ++ ra) (natSyms b ++ rb) qC rC tC xC zC) ra b []
      (encodeNat a).reverse =
      st ra (natSyms b ++ rb) qC rC ((encodeNat a).reverse.map Sym.bit ++ .mark :: tC)
        (.mark :: xC) (.mark :: zC) := by
    simp [loopSt, invSt, natSyms_zero]
  have hL1 : loopSt (st (natSyms a ++ ra) (natSyms b ++ rb) qC rC tC xC zC) ra b
      ([] ++ (encodeNat a).reverse) [] =
      st (natSyms a ++ ra) (natSyms b ++ rb) (natSyms (a / b) ++ qC) rC (.mark :: tC)
        (natSyms (a % b) ++ .mark :: xC) (.mark :: zC) := by
    simp [loopSt, invSt, bitsVal_encodeNat, natSyms]
  obtain ⟨v7, t7, e7, ht7⟩ := loop_eval hm hspec
    (st (natSyms a ++ ra) (natSyms b ++ rb) qC rC tC xC zC) ra rb hrb b hb rfl
    (encodeNat a).reverse [] (((encodeNat a).reverse.map Sym.bit ++ .mark :: tC).head?, false,
      v.2.2) rfl (by simp)
  rw [hL0, hL1] at e7
  -- teardown: drop the marks of `T` and `Z`, copy the remainder to `R`, clear `X`
  have e8 : Eval [] (popDrop (R := R) sT)
      ⟨v7, st (natSyms a ++ ra) (natSyms b ++ rb) (natSyms (a / b) ++ qC) rC (.mark :: tC)
        (natSyms (a % b) ++ .mark :: xC) (.mark :: zC)⟩
      ⟨v7, st (natSyms a ++ ra) (natSyms b ++ rb) (natSyms (a / b) ++ qC) rC tC
        (natSyms (a % b) ++ .mark :: xC) (.mark :: zC)⟩ 1 :=
    eval_pop' [] sT _ _ _ _ .mark tC rfl (st_upd_T ..)
  have e9 : Eval [] (popDrop (R := R) sZ)
      ⟨v7, st (natSyms a ++ ra) (natSyms b ++ rb) (natSyms (a / b) ++ qC) rC tC
        (natSyms (a % b) ++ .mark :: xC) (.mark :: zC)⟩
      ⟨v7, st (natSyms a ++ ra) (natSyms b ++ rb) (natSyms (a / b) ++ qC) rC tC
        (natSyms (a % b) ++ .mark :: xC) zC⟩ 1 :=
    eval_pop' [] sZ _ _ _ _ .mark zC rfl (st_upd_Z ..)
  have e10 := copyXR_eval (R := R) (natSyms a ++ ra) (natSyms b ++ rb) (natSyms (a / b) ++ qC)
    rC tC zC (.mark :: xC) (TermOK.cons rfl _) (a % b) v7
  have e11 := dropX_eval (R := R) (natSyms a ++ ra) (natSyms b ++ rb) (natSyms (a / b) ++ qC)
    (natSyms (a % b) ++ rC) tC zC (.mark :: xC) (TermOK.cons rfl _) (a % b) (some .mark, v7.2)
  have e12 : Eval [] (popDrop (R := R) sX)
      ⟨(some .mark, v7.2), st (natSyms a ++ ra) (natSyms b ++ rb) (natSyms (a / b) ++ qC)
        (natSyms (a % b) ++ rC) tC (.mark :: xC) zC⟩
      ⟨(some .mark, v7.2), st (natSyms a ++ ra) (natSyms b ++ rb) (natSyms (a / b) ++ qC)
        (natSyms (a % b) ++ rC) tC xC zC⟩ 1 :=
    eval_pop' [] sX _ _ _ _ .mark xC rfl (st_upd_X ..)
  refine ⟨_, _, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 (Eval.seq e10 (Eval.seq e11 e12)))))))))), ?_⟩
  -- cost
  simp only [List.length_reverse] at ht7
  change t7 ≤ bitLen a * ((2 * Cs + 50) * (bitLen b + 1) + 1) + 1 at ht7
  have hr : bitLen (a % b) ≤ bitLen b := bitLen_mono (Nat.le_of_lt (Nat.mod_lt a hb))
  have hK : bitLen a * ((2 * Cs + 50) * (bitLen b + 1) + 1) + 3 * bitLen a + 10 * bitLen b + 22 ≤
      (2 * Cs + 70) * (bitLen a * bitLen b + bitLen a + bitLen b + 1) := by
    ring_nf
    omega
  omega

/-- **The `divMod` contract body** for `divModProg Ps`. -/
theorem divModProg_spec {Cs : ℕ} {Ps : Prog (Loc 3 m) (fun _ => Sym) R} (hm : m ≤ 4)
    (hspec : SubSpec Cs Ps) (a b : ℕ) (ra rb : List Sym) (S : DStk → List Sym) (hb : 0 < b)
    (hra : TermOK ra) (hrb : TermOK rb) (hA : S sA = natSyms a ++ ra)
    (hB : S sB = natSyms b ++ rb) :
    Runs (divModProg Ps) S
      (Function.update (Function.update S sQ (natSyms (a / b) ++ S sQ)) sR
        (natSyms (a % b) ++ S sR)) (fun _ => True)
      ((2 * Cs + 70) * (bitLen a * bitLen b + bitLen a + bitLen b + 1)) := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := divMod_eval_st hm hspec a b hb ra rb (S sQ) (S sR) (S sT) (S sX)
    (S sZ) hra hrb v
  rw [← hA, ← hB, st_eta] at e
  exact ⟨v', t, by rw [upd_QR]; exact e, trivial, ht⟩

end Loop

/-- **W6a.divMod**, from the subtraction contract of W3. -/
theorem W6a_divModNat_holds (hsub : W3_subNat) : W6a_divModNat := by
  obtain ⟨Cs, hCs⟩ := hsub
  obtain ⟨m, R, _, Ps, hm, hfin, hne, hcl, hspec⟩ := hCs ()
  refine ⟨2 * Cs + 70, fun _ => ⟨3, DReg R, fun _ => (), divModProg Ps, by decide, ?_, ?_,
    divModProg_closed Ps hcl, ?_⟩⟩
  · haveI := hfin
    infer_instance
  · obtain ⟨r⟩ := hne
    exact ⟨(none, false, (none, none, .eq), r)⟩
  · intro a b ra rb S hb hra hrb hA hB
    exact divModProg_spec hm hspec a b ra rb S hb hra hrb hA hB

#assert_std_axioms loop_eval divMod_eval_st divModProg_spec W6a_divModNat_holds

end WP.W6a
