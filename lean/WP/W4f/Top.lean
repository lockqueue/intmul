import WP.W4f.Main
import WP.W4f.Phases2

/-!
# WP.W4f.Top — the contract `W4_oddStrideFactor`

`oddProg` runs `oddProgG` on the contract's stacks (`.inl 0` = `k`, `.inl 1` = `u2`, `.inl 2` =
destination; scratch `.inr 0..3` = `S, T, V, Y`). `oddProg_eval`: exact final stacks, cost
`≤ 40·(k+1)²` (`bitLen u2` is not even needed: only the low `≤ k` bits of `u2` are read).
`W4_oddStrideFactor_holds`: the contract, with `C = 40`, `m = 4`, registers `Reg`.
-/

namespace WP.W4f

open TMFw TMFw.Lib TMFw.Contracts Computability

/-- The program on the contract's stacks. -/
def oddProg : Prog (Loc 3 4) (fun _ => Sym) Reg :=
  oddProgG (.inl 0) (.inl 1) (.inl 2) (.inr 0) (.inr 1) (.inr 2) (.inr 3)

theorem oddProg_eval (k u2 : ℕ) (r0 r1 : List Sym) (hr0 : TermOK r0) (hr1 : TermOK r1)
    (v : Reg) (S : Loc 3 4 → List Sym) (hK : S (.inl 0) = natSyms k ++ r0)
    (hU : S (.inl 1) = natSyms u2 ++ r1) :
    ∃ v' t, t ≤ 40 * ((k + 1) * (k + 1)) ∧ Eval [] oddProg ⟨v, S⟩
      ⟨v', Function.update S (.inl 2)
        (natSyms (computableOddStrideFactor k u2) ++ S (.inl 2))⟩ t := by
  have hKU : (Sum.inl 0 : Loc 3 4) ≠ Sum.inl 1 := by decide
  have hKD : (Sum.inl 0 : Loc 3 4) ≠ Sum.inl 2 := by decide
  have hKS : (Sum.inl 0 : Loc 3 4) ≠ Sum.inr 0 := by decide
  have hKT : (Sum.inl 0 : Loc 3 4) ≠ Sum.inr 1 := by decide
  have hKV : (Sum.inl 0 : Loc 3 4) ≠ Sum.inr 2 := by decide
  have hKY : (Sum.inl 0 : Loc 3 4) ≠ Sum.inr 3 := by decide
  have hUD : (Sum.inl 1 : Loc 3 4) ≠ Sum.inl 2 := by decide
  have hUS : (Sum.inl 1 : Loc 3 4) ≠ Sum.inr 0 := by decide
  have hUT : (Sum.inl 1 : Loc 3 4) ≠ Sum.inr 1 := by decide
  have hUV : (Sum.inl 1 : Loc 3 4) ≠ Sum.inr 2 := by decide
  have hUY : (Sum.inl 1 : Loc 3 4) ≠ Sum.inr 3 := by decide
  have hDS : (Sum.inl 2 : Loc 3 4) ≠ Sum.inr 0 := by decide
  have hDT : (Sum.inl 2 : Loc 3 4) ≠ Sum.inr 1 := by decide
  have hDV : (Sum.inl 2 : Loc 3 4) ≠ Sum.inr 2 := by decide
  have hDY : (Sum.inl 2 : Loc 3 4) ≠ Sum.inr 3 := by decide
  have hST : (Sum.inr 0 : Loc 3 4) ≠ Sum.inr 1 := by decide
  have hSV : (Sum.inr 0 : Loc 3 4) ≠ Sum.inr 2 := by decide
  have hSY : (Sum.inr 0 : Loc 3 4) ≠ Sum.inr 3 := by decide
  have hTV : (Sum.inr 1 : Loc 3 4) ≠ Sum.inr 2 := by decide
  have hTY : (Sum.inr 1 : Loc 3 4) ≠ Sum.inr 3 := by decide
  have hVY : (Sum.inr 2 : Loc 3 4) ≠ Sum.inr 3 := by decide
  obtain ⟨o, a, c⟩ := v
  by_cases hk : k = 0
  · -- `k = 0`: the factor is `1`
    subst hk
    rw [natSyms_zero, List.nil_append] at hK
    have e0 := pk_eval (Sum.inl 0 : Loc 3 4) (o, a, c) S r0 hK
    have hfin : Function.update S (Sum.inl 2) (Sym.bit true :: S (Sum.inl 2)) =
        Function.update S (Sum.inl 2)
          (natSyms (computableOddStrideFactor 0 u2) ++ S (Sum.inl 2)) := by
      have hf : computableOddStrideFactor 0 u2 = 1 := by simp [computableOddStrideFactor]
      rw [hf, natSyms, encodeNat_one]
      rfl
    exact ⟨_, 1 + (1 + 1), by omega,
      (Eval.seq e0 (Eval.ite_false (symBit_termOK hr0 _)
        (pc_eval (Sum.inl 2 : Loc 3 4) (Sym.bit true) _ S))).of_eq (st_eq rfl hfin) rfl⟩
  · -- `k ≥ 1`: the lift
    have e0 := pk_eval (Sum.inl 0 : Loc 3 4) (o, a, c) S _ hK
    obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat k = b :: l := by
      cases h : encodeNat k with
      | nil => exact absurd ((encodeNat_eq_nil_iff k).1 h) hk
      | cons b l => exact ⟨b, l, rfl⟩
    have hkb : symBit ((natSyms k ++ r0).head?, a, c) = true := by
      rw [natSyms, hbl]
      rfl
    -- setup
    obtain ⟨t1, ht1, e1⟩ := setup_eval hKS hKT hKV hKY hST hSV hSY hTV hTY hVY k r0 hr0
      ((natSyms k ++ r0).head?, a, c) S hK
    obtain ⟨S1, hS1⟩ : ∃ S1, S1 = Function.update (Function.update (Function.update
        (Function.update S (Sum.inr 0) (Sym.mark :: S (Sum.inr 0))) (Sum.inr 3)
        (Sym.mark :: S (Sum.inr 3))) (Sum.inr 1) (natSyms k ++ Sym.mark :: S (Sum.inr 1)))
        (Sum.inr 2) (Sym.mark :: S (Sum.inr 2)) := ⟨_, rfl⟩
    have e1' := e1.of_eq (st_eq rfl hS1.symm) rfl
    have h1T : S1 (Sum.inr 1) = natSyms k ++ Sym.mark :: S (Sum.inr 1) := by
      simp only [hS1, Function.update_self, Function.update_of_ne hTV]
    -- unary expansion `s := 1^k`
    obtain ⟨⟨o2, a2, c2⟩, t2, ht2, e2⟩ := initLoop_eval hST hSV hTV (S (Sum.inr 1)) k k a c S1
      le_rfl h1T
    obtain ⟨S2, hS2⟩ : ∃ S2, S2 = Function.update (Function.update S1 (Sum.inr 1)
        (Sym.mark :: S (Sum.inr 1))) (Sum.inr 0)
        ((List.replicate k true).map Sym.bit ++ S1 (Sum.inr 0)) := ⟨_, rfl⟩
    have e2' := e2.of_eq (st_eq rfl hS2.symm) rfl
    have h2S : S2 (Sum.inr 0) = (List.replicate k true).map Sym.bit ++
        Sym.mark :: S (Sum.inr 0) := by
      simp only [hS2, hS1, Function.update_self, Function.update_of_ne hSV,
        Function.update_of_ne hST, Function.update_of_ne hSY]
    have h2U : S2 (Sum.inl 1) = natSyms u2 ++ r1 := by
      simp only [hS2, hS1, Function.update_of_ne hUS, Function.update_of_ne hUT,
        Function.update_of_ne hUV, Function.update_of_ne hUY, hU]
    have h2T : S2 (Sum.inr 1) = Sym.mark :: S (Sum.inr 1) := by
      simp only [hS2, Function.update_self, Function.update_of_ne hST.symm]
    have h2V : S2 (Sum.inr 2) = Sym.mark :: S (Sum.inr 2) := by
      simp only [hS2, hS1, Function.update_self, Function.update_of_ne hSV.symm,
        Function.update_of_ne hTV.symm]
    have e3 := pk_eval (Sum.inr 0 : Loc 3 4) (o2, a2, c2) S2 _ h2S
    -- the lifting loop
    obtain ⟨h, v4, t4, hh, hdvd, ht4, e4⟩ := mainLoop_eval hUS.symm hSV hST hSY hUV hUT hUY
      hTV.symm hVY hTY u2 (S (Sum.inr 0)) (S (Sum.inr 1)) (S (Sum.inr 2)) r1 hr1 k
      (List.replicate k true) a2 c2 S2 (by simp) h2S h2U h2T h2V
    obtain ⟨S4, hS4⟩ : ∃ S4, S4 = Function.update (Function.update S2 (Sum.inr 0)
        (Sym.mark :: S (Sum.inr 0))) (Sum.inr 3) (h.reverse.map Sym.bit ++ S2 (Sum.inr 3)) :=
      ⟨_, rfl⟩
    have e4' := e4.of_eq (st_eq rfl hS4.symm) rfl
    have h4S : S4 (Sum.inr 0) = Sym.mark :: S (Sum.inr 0) := by
      simp only [hS4, Function.update_self, Function.update_of_ne hSY]
    have h4T : S4 (Sum.inr 1) = Sym.mark :: S (Sum.inr 1) := by
      simp only [hS4, Function.update_of_ne hTY, Function.update_of_ne hST.symm, h2T]
    have h4V : S4 (Sum.inr 2) = Sym.mark :: S (Sum.inr 2) := by
      simp only [hS4, Function.update_of_ne hVY, Function.update_of_ne hSV.symm, h2V]
    have h4Y : S4 (Sum.inr 3) = h.reverse.map Sym.bit ++ Sym.mark :: S (Sum.inr 3) := by
      simp only [hS4, hS2, hS1, Function.update_self, Function.update_of_ne hSY.symm,
        Function.update_of_ne hTY.symm, Function.update_of_ne hVY.symm]
    -- cleanup and output
    obtain ⟨v5, t5, ht5, e5⟩ := cleanup_eval hDS hDT hDV hDY hST hSV hSY hTV hTY hVY h
      (S (Sum.inr 0)) (S (Sum.inr 1)) (S (Sum.inr 2)) (S (Sum.inr 3)) v4 S4 h4S h4T h4V h4Y
    have hw := hensel_correct k u2 hk h hh hdvd
    have hfin : Function.update (Function.update (Function.update (Function.update
        (Function.update S4 (Sum.inr 0) (S (Sum.inr 0))) (Sum.inr 1) (S (Sum.inr 1)))
        (Sum.inr 2) (S (Sum.inr 2))) (Sum.inr 3) (S (Sum.inr 3))) (Sum.inl 2)
        ((encodeNat (bitsVal h)).map Sym.bit ++ S4 (Sum.inl 2)) =
        Function.update S (Sum.inl 2)
          (natSyms (computableOddStrideFactor k u2) ++ S (Sum.inl 2)) := by
      funext j
      by_cases hjD : j = Sum.inl 2
      · rw [hjD]
        simp only [Function.update_self, hS4, hS2, hS1, Function.update_of_ne hDS,
          Function.update_of_ne hDT, Function.update_of_ne hDV, Function.update_of_ne hDY, hw,
          natSyms]
      by_cases hjY : j = Sum.inr 3
      · rw [hjY]
        simp only [Function.update_self, Function.update_of_ne hDY.symm]
      by_cases hjV : j = Sum.inr 2
      · rw [hjV]
        simp only [Function.update_self, Function.update_of_ne hVY,
          Function.update_of_ne hDV.symm]
      by_cases hjT : j = Sum.inr 1
      · rw [hjT]
        simp only [Function.update_self, Function.update_of_ne hTY, Function.update_of_ne hTV,
          Function.update_of_ne hDT.symm]
      by_cases hjS : j = Sum.inr 0
      · rw [hjS]
        simp only [Function.update_self, Function.update_of_ne hSY, Function.update_of_ne hSV,
          Function.update_of_ne hST, Function.update_of_ne hDS.symm]
      · simp only [Function.update_of_ne hjD, Function.update_of_ne hjY,
          Function.update_of_ne hjV, Function.update_of_ne hjT, Function.update_of_ne hjS, hS4,
          hS2, hS1]
    refine ⟨v5, 1 + (t1 + (t2 + (1 + (t4 + t5))) + 1), ?_,
      (Eval.seq e0 (Eval.ite_true hkb (Eval.seq e1' (Eval.seq e2' (Eval.seq e3
        (Eval.seq e4' e5)))))).of_eq (st_eq rfl hfin) rfl⟩
    have hb : bitLen k ≤ k := length_encodeNat_le k
    have hsq : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    have hkk : k * (6 * k + 12) = 6 * (k * k) + 12 * k := by ring
    omega

/-- **W4.oddStrideFactor** holds (no hypotheses): `C = 40`, four scratch stacks. -/
theorem W4_oddStrideFactor_holds : W4_oddStrideFactor := by
  refine ⟨40, fun _ => ⟨4, Reg, fun _ => (), oddProg, le_refl _, inferInstance,
    ⟨(none, false, false)⟩, oddProgG_closed _ _ _ _ _ _ _, ?_⟩⟩
  intro k u2 r0 r1 S hr0 hr1 hK hU
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, ht, e⟩ := oddProg_eval k u2 r0 r1 hr0 hr1 v S hK hU
  refine ⟨v', t, e, trivial, ?_⟩
  have hsq : (k + 1) ^ 2 = (k + 1) * (k + 1) := by ring
  rw [hsq]
  exact le_trans ht (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))

#assert_std_axioms oddProg_eval W4_oddStrideFactor_holds

end WP.W4f
