import WP.Inst.W3

/-!
# WP.Inst.W3Ok — the W3 contracts, proved with exactly the `WP.Inst.W3` definitions

`<c>.ok : W3_<c>` takes as witnesses `<c>.prog`, `<c>.r0` and `<c>.closed`; the scratch count, register type
and observation are given literally and agree with `<c>.m`, `<c>.R` and `<c>.obs` by `rfl`. The proofs are
those of the original contract theorems (`Contracts.Machine.W3`, `WP.W3`, `TMFw.W3s`, `WP.W3e`), with the
program replaced by the instance definition. So the programs that consumers run are the verified ones.
-/

namespace WP.Inst

open TMFw TMFw.Lib TMFw.Contracts Computability

theorem copyNat.ok : W3_copyNat := by
  refine ⟨7, fun _ => ⟨1, Option Sym, fun _ => (), copyNat.prog, by decide, inferInstance,
    ⟨copyNat.r0⟩, copyNat.closed, ?_⟩⟩
  intro a rx S hrx hx
  refine Runs.of_eval fun v => ?_
  have e := copyBlock_eval (src := .inl 0) (dst := .inl 1) (tmp := .inr 0) (by decide) (by decide)
    (by decide) [] v (encodeNat a) rx S hrx hx
  refine ⟨some .mark, _, e, trivial, ?_⟩
  simp only [bitLen]
  omega

theorem cmpNat.ok : W3_cmpNat := by
  refine ⟨15, fun _ => ⟨2, CReg, fun v => v.2.2, cmpNat.prog, by decide, inferInstance,
    ⟨cmpNat.r0⟩, cmpNat.closed, ?_⟩⟩
  intro a b rx ry S hrx hry hx hy
  refine Runs.of_eval fun v => ?_
  have e := cmpNum_eval (k₁ := .inl 0) (k₂ := .inl 1) (t₁ := .inr 0) (t₂ := .inr 1) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) v (encodeNat a) (encodeNat b)
    rx ry S hrx hry hx hy
  refine ⟨_, _, e, ?_, ?_⟩
  · show cmpAll .eq (encodeNat a) (encodeNat b) = ordOf a b
    rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat a) (normBits_encodeNat b), bitsVal_encodeNat,
      bitsVal_encodeNat]
  · simp only [bitLen]
    omega

theorem isZeroNat.ok : W3_isZeroNat := by
  refine ⟨1, fun _ => ⟨0, Option Sym, fun r => !optIsBit r, isZeroNat.prog, Nat.zero_le _,
    inferInstance, ⟨isZeroNat.r0⟩, isZeroNat.closed, ?_⟩⟩
  intro a rx S hrx hx
  refine Runs.of_eval fun v => ?_
  obtain ⟨r, hr, e⟩ := zeroTest_eval (k := .inl 0) [] v a rx S hrx hx
  exact ⟨r, 1, e, by simp [hr], le_refl _⟩

theorem incNat.ok : W3_incNat := by
  refine ⟨9, fun _ => ⟨1, Option Sym, fun _ => (), incNat.prog, by decide, inferInstance,
    ⟨incNat.r0⟩, incNat.closed, ?_⟩⟩
  intro a rx S hrx hx
  refine Runs.of_eval fun v => ?_
  obtain ⟨c, hc, e⟩ := inc_eval (k := .inl 0) (t := .inr 0) (by decide) [] v (encodeNat a) rx S
    hrx hx
  refine ⟨some .mark, c, ?_, trivial, by omega⟩
  rw [natSyms, encodeNat_succ]
  exact e

theorem decNat.ok : W3_decNat := by
  refine ⟨8, fun _ => ⟨1, Option Sym, fun _ => (), decNat.prog, by decide, inferInstance,
    ⟨decNat.r0⟩, decNat.closed, ?_⟩⟩
  intro a rx S hrx hx
  refine Runs.of_eval fun v => ?_
  have e := dec_eval (k := .inl 0) (t := .inr 0) (by decide) [] v a rx S hrx hx
  exact ⟨some .mark, _, e, trivial, by omega⟩

theorem natToInt.ok : W3_natToInt := by
  refine ⟨1, fun _ => ⟨0, Option Sym, fun _ => (), natToInt.prog, Nat.zero_le _,
    inferInstance, ⟨natToInt.r0⟩, natToInt.closed, ?_⟩⟩
  intro a rx S hrx hx
  refine Runs.of_eval fun v => ⟨v, 1, ?_, trivial, le_refl _⟩
  have e : Eval [] (pushC (.inl 0 : Loc 1 0) .pos) ⟨v, S⟩
      ⟨v, Function.update S (.inl 0) (Sym.pos :: S (.inl 0))⟩ 1 := Eval.push _ _ _ _ _
  refine e.of_eq ?_ rfl
  rw [intSyms_natCast, hx, List.cons_append]

theorem splitSign.ok : W3_splitSign := by
  refine ⟨1, fun _ => ⟨0, Option Sym, fun r => decide (r = some Sym.neg), splitSign.prog,
    Nat.zero_le _, inferInstance, ⟨splitSign.r0⟩, splitSign.closed, ?_⟩⟩
  intro z rx S hrx hx
  refine Runs.of_eval fun v => ⟨some (sgnSym z), 1, ?_, ?_, le_refl _⟩
  · have e : Eval [] (popR (.inl 0 : Loc 1 0)) ⟨v, S⟩
        ⟨(S (.inl 0)).head?, Function.update S (.inl 0) (S (.inl 0)).tail⟩ 1 := Eval.pop _ _ _ _ _
    refine e.of_eq ?_ rfl
    simp [hx, intSyms]
  · by_cases h : z < 0 <;> simp [sgnSym, h]

open WP.W3 in
theorem addNat.ok : W3_addNat := by
  refine ⟨20, fun _ => ⟨3, AReg, fun _ => (), addNat.prog, by decide, inferInstance,
    ⟨addNat.r0⟩, addNat.closed, ?_⟩⟩
  intro a b rx ry S hrx hry hx hy
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := addSubProg_eval addBit (encodeNat a) (encodeNat b) rx ry hrx hry S hx
    hy v
  have h0 : false.toNat = 0 := rfl
  have hval : bitsVal (rip addBit (max (encodeNat a).length (encodeNat b).length) false
      (encodeNat a) (encodeNat b)) = a + b := by
    rw [bitsVal_rip_add (max (encodeNat a).length (encodeNat b).length) false (encodeNat a)
      (encodeNat b) (le_max_left _ _) (le_max_right _ _), bitsVal_encodeNat, bitsVal_encodeNat,
      h0, Nat.add_zero]
  rw [hval] at e
  refine ⟨v', t, e, trivial, ?_⟩
  simp only [bitLen]
  omega

open WP.W3 in
theorem subNat.ok : W3_subNat := by
  refine ⟨20, fun _ => ⟨3, AReg, fun _ => (), subNat.prog, by decide, inferInstance,
    ⟨subNat.r0⟩, subNat.closed, ?_⟩⟩
  intro a b rx ry S hrx hry hab hx hy
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := addSubProg_eval subBit (encodeNat a) (encodeNat b) rx ry hrx hry S hx
    hy v
  have hle : bitsVal (encodeNat b) ≤ bitsVal (encodeNat a) := by
    rw [bitsVal_encodeNat, bitsVal_encodeNat]
    exact hab
  have hval : bitsVal (rip subBit (max (encodeNat a).length (encodeNat b).length) false
      (encodeNat a) (encodeNat b)) = a - b := by
    rw [bitsVal_rip_sub (max (encodeNat a).length (encodeNat b).length) (encodeNat a)
      (encodeNat b) (le_max_left _ _) (le_max_right _ _) hle, bitsVal_encodeNat,
      bitsVal_encodeNat]
  rw [hval] at e
  refine ⟨v', t, e, trivial, ?_⟩
  simp only [bitLen]
  omega

open WP.W3 in
theorem dropNat.ok : W3_dropNat := by
  refine ⟨4, fun _ => ⟨0, Option Sym, fun _ => (), dropNat.prog, Nat.zero_le _,
    inferInstance, ⟨dropNat.r0⟩, dropNat.closed, ?_⟩⟩
  intro a rx S hrx hx
  refine Runs.of_eval fun v =>
    ⟨rx.head?, _, dropNum_eval [] v (encodeNat a) rx S hrx hx, trivial, ?_⟩
  simp only [bitLen]
  omega

open WP.W3 in
theorem normNat.ok : W3_normNat := by
  refine ⟨8, fun _ => ⟨1, Option Sym, fun _ => (), normNat.prog, by decide, inferInstance,
    ⟨normNat.r0⟩, normNat.closed, ?_⟩⟩
  intro l rx S hrx hx
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := normProg_eval l rx hrx S hx v
  exact ⟨v', t, e, trivial, by omega⟩

open TMFw.W3s TMFw.W3b in
theorem splitAt.ok : W3_splitAt := by
  refine ⟨30, fun _ => ⟨3, Option Sym, fun _ => (), splitAt.prog, by decide, inferInstance,
    ⟨splitAt.r0⟩, splitAt.closed, ?_⟩⟩
  intro a n rx rc S hrx hrc hx hc
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := splitCore_eval (x := .inl 0) (c := .inl 1) (y := .inl 2) (kc := .inr 1)
    (u := .inr 2) (t := .inr 0) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) [] v a n rx
    rc hrx hrc S hx hc
  exact ⟨v', t, e, trivial, ht⟩

open TMFw.W3s TMFw.W3b in
theorem concatAt.ok : W3_concatAt := by
  refine ⟨30, fun _ => ⟨3, Option Sym, fun _ => (), concatAt.prog, by decide, inferInstance,
    ⟨concatAt.r0⟩, concatAt.closed, ?_⟩⟩
  intro hi lo n rx rc ry S hrx hrc hry hlo hx hc hy
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := concatCore_eval (x := .inl 0) (c := .inl 1) (y := .inl 2)
    (kc := .inr 1) (u := .inr 2) (t := .inr 0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    [] v hi lo n rx rc ry hrx hrc hry hlo S hx hc hy
  exact ⟨v', t, e, trivial, ht⟩

open WP.W3e in
theorem shlConst.ok : W3_shlConst := by
  refine ⟨3, fun k => ⟨0, Option Sym, fun _ => (), shlConst.prog k, Nat.zero_le _, inferInstance,
    ⟨shlConst.r0⟩, shlConst.closed k, ?_⟩⟩
  intro a rx S hrx hS
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := shlProg_eval k a rx hrx S hS v
  exact ⟨v', t, e, trivial, ht⟩

open WP.W3e in
theorem shrConst.ok : W3_shrConst := by
  refine ⟨3, fun k => ⟨0, Option Sym, fun _ => (), shrConst.prog k, Nat.zero_le _, inferInstance,
    ⟨shrConst.r0⟩, shrConst.closed k, ?_⟩⟩
  intro a rx S hrx hS
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', e⟩ := shrProg_eval rx hrx k a S hS v
  exact ⟨v', _, e, trivial, by omega⟩

open TMFw.W3s TMFw.W3b in
theorem shrVar.ok : W3_shrVar := by
  refine ⟨33, fun _ => ⟨4, Option Sym, fun _ => (), shrVar.prog, le_refl _, inferInstance,
    ⟨shrVar.r0⟩, shrVar.closed, ?_⟩⟩
  intro a n rx rc S hrx hrc hx hc
  refine Runs.of_eval fun v => ?_
  have e1 : Eval [] (pushC (.inr 3 : Loc 2 4) .mark) ⟨v, S⟩
      ⟨v, Function.update S (.inr 3) (.mark :: S (.inr 3))⟩ 1 :=
    eval_push_eq [] (.inr 3 : Loc 2 4) (fun _ => Sym.mark) v S Sym.mark (S (.inr 3)) rfl rfl
  set S1 := Function.update S (.inr 3) (Sym.mark :: S (.inr 3)) with hS1
  have hx1 : S1 (.inl 0) = natSyms a ++ rx := by
    rw [hS1, Function.update_of_ne (by decide), hx]
  have hc1 : S1 (.inl 1) = natSyms n ++ rc := by
    rw [hS1, Function.update_of_ne (by decide), hc]
  obtain ⟨v2, t2, e2, ht2⟩ := splitCore_eval (x := .inl 0) (c := .inl 1) (y := .inr 3)
    (kc := .inr 1) (u := .inr 2) (t := .inr 0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    [] v a n rx rc hrx hrc S1 hx1 hc1
  set S2 := Function.update (Function.update S1 (.inl 0) (natSyms (a / 2 ^ n) ++ rx)) (.inr 3)
    (natSyms (a % 2 ^ n) ++ S1 (.inr 3)) with hS2
  have hS2w : S2 (.inr 3) = (encodeNat (a % 2 ^ n)).map Sym.bit ++ (Sym.mark :: S (.inr 3)) := by
    rw [hS2, Function.update_self, hS1, Function.update_self]
    rfl
  have e3 := dropBits_eval [] v2 (encodeNat (a % 2 ^ n)) (Sym.mark :: S (.inr 3)) S2
    (TermOK.cons rfl _) hS2w
  refine ⟨(Sym.mark :: S (.inr 3)).head?, _, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl, trivial,
    ?_⟩
  · congr 1
    funext j
    simp only [hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · have hb := bitLen_mod_le a n
    simp only [bitLen] at hb ht2 ⊢
    omega

open TMFw.W3s TMFw.W3b in
theorem shlVar.ok : W3_shlVar := by
  refine ⟨32, fun _ => ⟨4, Option Sym, fun _ => (), shlVar.prog, le_refl _, inferInstance,
    ⟨shlVar.r0⟩, shlVar.closed, ?_⟩⟩
  intro a n rx rc S hrx hrc hx hc
  refine Runs.of_eval fun v => ?_
  have e1 : Eval [] (pushC (.inr 3 : Loc 2 4) .mark) ⟨v, S⟩
      ⟨v, Function.update S (.inr 3) (.mark :: S (.inr 3))⟩ 1 :=
    eval_push_eq [] (.inr 3 : Loc 2 4) (fun _ => Sym.mark) v S Sym.mark (S (.inr 3)) rfl rfl
  set S1 := Function.update S (.inr 3) (Sym.mark :: S (.inr 3)) with hS1
  have hx1 : S1 (.inl 0) = natSyms a ++ rx := by
    rw [hS1, Function.update_of_ne (by decide), hx]
  have hc1 : S1 (.inl 1) = natSyms n ++ rc := by
    rw [hS1, Function.update_of_ne (by decide), hc]
  have hw1 : S1 (.inr 3) = natSyms 0 ++ (Sym.mark :: S (.inr 3)) := by
    rw [hS1, Function.update_self, natSyms_zero, List.nil_append]
  obtain ⟨v2, t2, e2, ht2⟩ := concatCore_eval (x := .inl 0) (c := .inl 1) (y := .inr 3)
    (kc := .inr 1) (u := .inr 2) (t := .inr 0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    [] v a 0 n rx rc (Sym.mark :: S (.inr 3)) hrx hrc (TermOK.cons rfl _) (Nat.two_pow_pos n) S1
    hx1 hc1 hw1
  set S2 := Function.update (Function.update S1 (.inl 0) (natSyms (0 + a * 2 ^ n) ++ rx)) (.inr 3)
    (Sym.mark :: S (.inr 3)) with hS2
  have e3 := eval_pop_eq [] (.inr 3 : Loc 2 4) (fun _ o => o) v2 S2 Sym.mark (S (.inr 3))
    (by rw [hS2, Function.update_self])
  refine ⟨some Sym.mark, _, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl, trivial, ?_⟩
  · congr 1
    funext j
    simp only [hS2, hS1, Nat.zero_add, Function.update_apply]
    split_ifs <;> simp_all
  · omega

end WP.Inst
