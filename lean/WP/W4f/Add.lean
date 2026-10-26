import WP.W4f.Prog

/-!
# WP.W4f.Add — the in-place addition `s := (s + u2) mod 2^|s|`

* `readU_eval`: read the next bit of `u2` (a non-bit reads as `0`, nothing is popped).
* `addLoop_eval`: the bit-serial pass over the residual `s`; it pops `s`, pushes the sum bits
  (`addBits s u c`, reversed) on `kT`, and moves the `min(|s|, |u|)` bits of `u2` it read onto `kV`.
* `addPhase_eval`: the whole phase; only `kS` changes (to `addBits s u false`).
-/

namespace WP.W4f

open TMFw TMFw.Lib TMFw.Contracts

variable {K : Type} [DecidableEq K]

theorem drop_tail_eq (u : List Bool) (n : ℕ) : u.tail.drop n = u.drop (n + 1) := by
  cases u <;> simp

theorem take_tail_rev (u : List Bool) (n : ℕ) (l : List Sym) :
    (u.tail.take n).reverse.map Sym.bit ++ ((u.take 1).map Sym.bit ++ l) =
      (u.take (n + 1)).reverse.map Sym.bit ++ l := by
  cases u <;> simp

theorem take_drop_map (u : List Bool) (n : ℕ) (l : List Sym) :
    (u.take n).map Sym.bit ++ ((u.drop n).map Sym.bit ++ l) = u.map Sym.bit ++ l := by
  rw [← List.append_assoc, ← List.map_append, List.take_append_drop]

theorem readU_eval {kU kV : K} (hUV : kU ≠ kV) (r1 : List Sym) (hr1 : TermOK r1) (u : List Bool)
    (v : Reg) (S : K → List Sym) (hU : S kU = u.map Sym.bit ++ r1) :
    ∃ t, t ≤ 4 ∧ Eval [] (readU kU kV) ⟨v, S⟩
      ⟨((u.map Sym.bit ++ r1).head?, v.2), Function.update (Function.update S kU
        (u.tail.map Sym.bit ++ r1)) kV ((u.take 1).map Sym.bit ++ S kV)⟩ t := by
  have e1 := pk_eval kU v S _ hU
  cases u with
  | nil =>
    have hU' : S kU = r1 := hU
    have hfin : Function.update (Function.update S kU (([] : List Bool).tail.map Sym.bit ++ r1))
        kV ((([] : List Bool).take 1).map Sym.bit ++ S kV) = S := by
      simp only [List.tail_nil, List.take_nil, List.map_nil, List.nil_append]
      rw [← hU', Function.update_eq_self, Function.update_eq_self]
    exact ⟨3, by omega, (Eval.seq e1 (Eval.ite_false (symBit_termOK hr1 _) (skip_eval [] _))).of_eq
      (st_eq rfl hfin.symm) rfl⟩
  | cons x u' =>
    have hU' : S kU = Sym.bit x :: (u'.map Sym.bit ++ r1) := hU
    have e2 := pp_eval kU (((x :: u').map Sym.bit ++ r1).head?, v.2) S _ _ hU'
    have e3 := pr_eval kV (Sym.bit x) v.2 (Function.update S kU (u'.map Sym.bit ++ r1))
    have hfin : Function.update (Function.update S kU (u'.map Sym.bit ++ r1)) kV
        (Sym.bit x :: Function.update S kU (u'.map Sym.bit ++ r1) kV) =
        Function.update (Function.update S kU ((x :: u').tail.map Sym.bit ++ r1)) kV
          (((x :: u').take 1).map Sym.bit ++ S kV) := by
      rw [Function.update_of_ne (Ne.symm hUV)]
      rfl
    exact ⟨4, le_refl _, (Eval.seq e1 (Eval.ite_true (by rfl) (Eval.seq e2 e3))).of_eq
      (st_eq rfl hfin) rfl⟩

theorem addLoop_eval {kS kU kV kT : K} (hSU : kS ≠ kU) (hSV : kS ≠ kV) (hST : kS ≠ kT)
    (hUV : kU ≠ kV) (hUT : kU ≠ kT) (hVT : kV ≠ kT) (restS r1 : List Sym) (hrS : TermOK restS)
    (hr1 : TermOK r1) :
    ∀ (s u : List Bool) (a c : Bool) (S : K → List Sym),
      S kS = s.map Sym.bit ++ restS → S kU = u.map Sym.bit ++ r1 →
      ∃ v' t, t ≤ 9 * s.length + 1 ∧
        Eval [] (addLoop kS kU kV kT) ⟨((s.map Sym.bit ++ restS).head?, a, c), S⟩
          ⟨v', Function.update (Function.update (Function.update (Function.update S
            kS restS) kU ((u.drop s.length).map Sym.bit ++ r1))
            kV ((u.take s.length).reverse.map Sym.bit ++ S kV))
            kT ((addBits s u c).reverse.map Sym.bit ++ S kT)⟩ t
  | [], u, a, c, S, hS, hU => by
    have hS' : S kS = restS := hS
    have hfin : Function.update (Function.update (Function.update (Function.update S
        kS restS) kU ((u.drop ([] : List Bool).length).map Sym.bit ++ r1))
        kV ((u.take ([] : List Bool).length).reverse.map Sym.bit ++ S kV))
        kT ((addBits [] u c).reverse.map Sym.bit ++ S kT) = S := by
      simp only [List.length_nil, List.drop_zero, List.take_zero, List.reverse_nil, List.map_nil,
        List.nil_append, addBits]
      rw [← hS', ← hU, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self,
        Function.update_eq_self]
    exact ⟨_, 1, by omega,
      (Eval.loop_false (symBit_termOK hrS _)).of_eq (st_eq rfl hfin.symm) rfl⟩
  | b :: s, u, a, c, S, hS, hU => by
    have hS' : S kS = Sym.bit b :: (s.map Sym.bit ++ restS) := hS
    obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update S kS (s.map Sym.bit ++ restS) := ⟨_, rfl⟩
    have e1 : Eval [] (popA kS) ⟨(((b :: s).map Sym.bit ++ restS).head?, a, c), S⟩
        ⟨(((b :: s).map Sym.bit ++ restS).head?, b, c), S1⟩ 1 :=
      (popA_eval kS _ a c b S _ hS').of_eq (st_eq rfl hS1.symm) rfl
    have hU1 : S1 kU = u.map Sym.bit ++ r1 := by
      rw [hS1, Function.update_of_ne (Ne.symm hSU)]
      exact hU
    obtain ⟨t2, ht2, e2⟩ := readU_eval hUV r1 hr1 u
      (((b :: s).map Sym.bit ++ restS).head?, b, c) S1 hU1
    obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update (Function.update (Function.update S1 kU
        (u.tail.map Sym.bit ++ r1)) kV ((u.take 1).map Sym.bit ++ S1 kV)) kT
        (Sym.bit (xor3 b (u.headD false) c) :: S1 kT) := ⟨_, rfl⟩
    have e3 : Eval [] (pushSum kT) ⟨((u.map Sym.bit ++ r1).head?, b, c),
        Function.update (Function.update S1 kU (u.tail.map Sym.bit ++ r1)) kV
          ((u.take 1).map Sym.bit ++ S1 kV)⟩ ⟨((u.map Sym.bit ++ r1).head?, b, c), S3⟩ 1 := by
      refine (pushSum_eval kT _ b c _).of_eq (st_eq rfl ?_) rfl
      rw [hS3, optBit_headU hr1, Function.update_of_ne (Ne.symm hVT),
        Function.update_of_ne (Ne.symm hUT)]
    have e4 := setC_eval (K := K) ((u.map Sym.bit ++ r1).head?) b c S3
    have h3S : S3 kS = s.map Sym.bit ++ restS := by
      rw [hS3, Function.update_of_ne hST, Function.update_of_ne hSV, Function.update_of_ne hSU,
        hS1, Function.update_self]
    have h3U : S3 kU = u.tail.map Sym.bit ++ r1 := by
      rw [hS3, Function.update_of_ne hUT, Function.update_of_ne hUV, Function.update_self]
    have e5 := pk_eval kS ((u.map Sym.bit ++ r1).head?, b,
      maj3 b (optBit (u.map Sym.bit ++ r1).head?) c) S3 _ h3S
    obtain ⟨v', t, ht, ih⟩ := addLoop_eval hSU hSV hST hUV hUT hVT restS r1 hrS hr1 s u.tail b
      (maj3 b (optBit (u.map Sym.bit ++ r1).head?) c) S3 h3S h3U
    have hfin : Function.update (Function.update (Function.update (Function.update S3
        kS restS) kU ((u.tail.drop s.length).map Sym.bit ++ r1))
        kV ((u.tail.take s.length).reverse.map Sym.bit ++ S3 kV))
        kT ((addBits s u.tail (maj3 b (optBit (u.map Sym.bit ++ r1).head?) c)).reverse.map
          Sym.bit ++ S3 kT) =
        Function.update (Function.update (Function.update (Function.update S
        kS restS) kU ((u.drop (b :: s).length).map Sym.bit ++ r1))
        kV ((u.take (b :: s).length).reverse.map Sym.bit ++ S kV))
        kT ((addBits (b :: s) u c).reverse.map Sym.bit ++ S kT) := by
      have hl : (b :: s).length = s.length + 1 := rfl
      rw [hl, optBit_headU hr1]
      funext j
      by_cases h1 : j = kT
      · rw [h1]
        simp only [Function.update_self, hS3, hS1, Function.update_of_ne (Ne.symm hST), addBits,
          List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.cons_append, List.nil_append]
      by_cases h2 : j = kV
      · rw [h2]
        simp only [Function.update_self, Function.update_of_ne hVT, hS3, hS1,
          Function.update_of_ne (Ne.symm hSV)]
        exact take_tail_rev u s.length (S kV)
      by_cases h3 : j = kU
      · rw [h3]
        simp only [Function.update_self, Function.update_of_ne hUT, Function.update_of_ne hUV,
          drop_tail_eq]
      by_cases h4 : j = kS
      · rw [h4]
        simp only [Function.update_self, Function.update_of_ne hST, Function.update_of_ne hSV,
          Function.update_of_ne hSU]
      · simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
          Function.update_of_ne h4, hS3, hS1]
    refine ⟨v', 1 + (t2 + (1 + (1 + 1))) + t + 1, ?_, (Eval.loop_true (by rfl)
      (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))) ih).of_eq (st_eq rfl hfin) rfl⟩
    simp only [List.length_cons]
    omega

theorem addPhase_eval {kS kU kV kT : K} (hSU : kS ≠ kU) (hSV : kS ≠ kV) (hST : kS ≠ kT)
    (hUV : kU ≠ kV) (hUT : kU ≠ kT) (hVT : kV ≠ kT) (s u : List Bool) (v : Reg)
    (S : K → List Sym) (S0 T0 V0 r1 : List Sym) (hr1 : TermOK r1)
    (hS : S kS = s.map Sym.bit ++ Sym.mark :: S0) (hU : S kU = u.map Sym.bit ++ r1)
    (hT : S kT = Sym.mark :: T0) (hV : S kV = Sym.mark :: V0) :
    ∃ v' t, t ≤ 15 * s.length + 12 ∧ Eval [] (addPhase kS kU kV kT) ⟨v, S⟩
      ⟨v', Function.update S kS ((addBits s u false).map Sym.bit ++ Sym.mark :: S0)⟩ t := by
  obtain ⟨o, a, c⟩ := v
  have e1 := clrC_eval (K := K) o a c S
  have e2 := pk_eval kS (o, a, false) S _ hS
  obtain ⟨v3, t3, ht3, e3⟩ := addLoop_eval hSU hSV hST hUV hUT hVT (Sym.mark :: S0) r1
    (TermOK.cons rfl _) hr1 s u a false S hS hU
  obtain ⟨S3, hS3⟩ : ∃ S3, S3 = Function.update (Function.update (Function.update
      (Function.update S kS (Sym.mark :: S0)) kU ((u.drop s.length).map Sym.bit ++ r1))
      kV ((u.take s.length).reverse.map Sym.bit ++ S kV))
      kT ((addBits s u false).reverse.map Sym.bit ++ S kT) := ⟨_, rfl⟩
  have e3' := e3.of_eq (st_eq rfl hS3.symm) rfl
  have h3T : S3 kT = (addBits s u false).reverse.map Sym.bit ++ Sym.mark :: T0 := by
    rw [hS3, Function.update_self, hT]
  have m4 := moveBlock_eval (Ne.symm hST) [] v3.1 (addBits s u false).reverse (Sym.mark :: T0) S3
    (TermOK.cons rfl _) h3T
  obtain ⟨S4, hS4⟩ : ∃ S4, S4 = Function.update (Function.update S3 kT (Sym.mark :: T0)) kS
      ((addBits s u false).reverse.reverse.map Sym.bit ++ S3 kS) := ⟨_, rfl⟩
  have e4 := (lift_eval m4 v3 rfl).of_eq (st_eq rfl hS4.symm) rfl
  have h4V : S4 kV = (u.take s.length).reverse.map Sym.bit ++ Sym.mark :: V0 := by
    rw [hS4, Function.update_of_ne (Ne.symm hSV), Function.update_of_ne hVT, hS3,
      Function.update_of_ne hVT, Function.update_self, hV]
  have m5 := moveBlock_eval (Ne.symm hUV) [] (Sym.mark :: T0).head? (u.take s.length).reverse
    (Sym.mark :: V0) S4 (TermOK.cons rfl _) h4V
  have e5 := lift_eval m5 ((Sym.mark :: T0).head?, v3.2) rfl
  have hfin : Function.update (Function.update S4 kV (Sym.mark :: V0)) kU
      ((u.take s.length).reverse.reverse.map Sym.bit ++ S4 kU) =
      Function.update S kS ((addBits s u false).map Sym.bit ++ Sym.mark :: S0) := by
    funext j
    by_cases h1 : j = kU
    · rw [h1]
      simp only [Function.update_self, Function.update_of_ne (Ne.symm hSU),
        Function.update_of_ne hUT, Function.update_of_ne hUV, hS4, hS3, List.reverse_reverse]
      rw [hU, take_drop_map]
    by_cases h2 : j = kV
    · rw [h2]
      simp only [Function.update_self, Function.update_of_ne (Ne.symm hUV),
        Function.update_of_ne (Ne.symm hSV)]
      exact hV.symm
    by_cases h3 : j = kS
    · rw [h3]
      simp only [Function.update_self, Function.update_of_ne hSU, Function.update_of_ne hSV,
        Function.update_of_ne hST, hS4, hS3, List.reverse_reverse]
    by_cases h4 : j = kT
    · rw [h4]
      simp only [Function.update_self, Function.update_of_ne hUT.symm,
        Function.update_of_ne hVT.symm, Function.update_of_ne hST.symm, hS4]
      exact hT.symm
    · simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
        Function.update_of_ne h4, hS4, hS3]
  refine ⟨_, 1 + (1 + (t3 + ((3 * (addBits s u false).reverse.length + 4) +
    (3 * (u.take s.length).reverse.length + 4)))), ?_,
    (Eval.seq e1 (Eval.seq e2 (Eval.seq e3' (Eval.seq e4 e5)))).of_eq (st_eq rfl hfin) rfl⟩
  have l1 : (addBits s u false).reverse.length = s.length := by
    rw [List.length_reverse, length_addBits]
  have l2 : (u.take s.length).reverse.length ≤ s.length := by
    rw [List.length_reverse]
    exact List.length_take_le _ _
  omega

#assert_std_axioms drop_tail_eq take_tail_rev take_drop_map readU_eval addLoop_eval addPhase_eval

end WP.W4f
