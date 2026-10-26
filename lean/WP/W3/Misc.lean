import WP.W3.AddLoop

/-!
# WP.W3.Misc — `W3_dropNat_holds`, `W3_normNat_holds`, re-exports of the seed instances

* `dropNat`: `dropNum x` (pop the block and the terminator, push the terminator back);
  cost `2·|a| + 4`, `C = 4`, no scratch.
* `normNat`: guard `t`, `moveBlock x t` (MSB-first bits on `t`), `emitNorm t x` (skip high zeros,
  canonical number back on `x`, mark consumed); cost `≤ 6·|l| + 8`, `C = 8`, one scratch stack.
* `W3_copyNat_holds`, `W3_cmpNat_holds`, `W3_isZeroNat_holds`, `W3_incNat_holds`,
  `W3_decNat_holds`, `W3_natToInt_holds`, `W3_splitSign_holds`: the instances proved in
  `Contracts.Machine.W3`, re-exported under the W3 names.
-/

namespace WP.W3

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## drop -/

/-- **drop** (in place): pop the number on `x`, keep its terminator; cost `4·(|a| + 1)`. -/
theorem W3_dropNat_holds : W3_dropNat := by
  refine ⟨4, fun _ => ⟨0, Option Sym, fun _ => (), dropNum (.inl 0), Nat.zero_le _,
    inferInstance, ⟨none⟩, closed_of_noRec rfl, ?_⟩⟩
  intro a rx S hrx hx
  refine Runs.of_eval fun v =>
    ⟨rx.head?, _, dropNum_eval [] v (encodeNat a) rx S hrx hx, trivial, ?_⟩
  simp only [bitLen]
  omega

/-! ## normalize -/

theorem stk_ext11 {S T : Loc 1 1 → List Sym} (hx : S (.inl 0) = T (.inl 0))
    (ht : S (.inr 0) = T (.inr 0)) : S = T := by
  funext k
  rcases k with ⟨_ | n, hn⟩ | ⟨_ | n, hn⟩
  · exact hx
  · omega
  · exact ht
  · omega

/-- Normalize the bit block on `.inl 0` in place, using the scratch stack `.inr 0`. -/
def normProg : SProg (Loc 1 1) :=
  .seq (pushC (.inr 0) .mark) (.seq (moveBlock (.inl 0) (.inr 0)) (emitNorm (.inr 0) (.inl 0)))

theorem normProg_eval (l : List Bool) (rx : List Sym) (hrx : TermOK rx) (S : Loc 1 1 → List Sym)
    (hx : S (.inl 0) = l.map Sym.bit ++ rx) (v : Option Sym) :
    ∃ v' t, Eval [] normProg ⟨v, S⟩
      ⟨v', Function.update S (.inl 0) (natSyms (bitsVal l) ++ rx)⟩ t ∧ t ≤ 6 * l.length + 8 := by
  have e1 := eval_push_eq [] (.inr 0 : Loc 1 1) (fun _ => Sym.mark) v S .mark (S (.inr 0)) rfl rfl
  set S1 := Function.update S (.inr 0) (.mark :: S (.inr 0)) with hS1
  have e2 := moveBlock_eval (src := (.inl 0 : Loc 1 1)) (dst := .inr 0) (by decide) [] v l rx S1
    hrx (by simp [hS1, hx])
  set S2 := Function.update (Function.update S1 (.inl 0) rx) (.inr 0)
    (l.reverse.map Sym.bit ++ S1 (.inr 0)) with hS2
  have e3 := emitNorm_eval (t := (.inr 0 : Loc 1 1)) (d := .inl 0) (by decide) [] rx.head?
    l.reverse (.mark :: S (.inr 0)) S2 (TermOK.cons rfl _) (by simp [hS2, hS1])
  refine ⟨_, _, eval_stk (Eval.seq e1 (Eval.seq e2 e3)) ?_, ?_⟩
  · apply stk_ext11 <;> simp [hS2, hS1, natSyms]
  · have hlen := length_dropWhile_le' (fun b => !b) l.reverse
    simp only [List.length_reverse] at hlen ⊢
    omega

/-- **normalize** (in place): bit block `l` ↦ `natSyms (bitsVal l)`; cost `8·(|l| + 1)`. -/
theorem W3_normNat_holds : W3_normNat := by
  refine ⟨8, fun _ => ⟨1, Option Sym, fun _ => (), normProg, by decide, inferInstance, ⟨none⟩,
    closed_of_noRec rfl, ?_⟩⟩
  intro l rx S hrx hx
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := normProg_eval l rx hrx S hx v
  exact ⟨v', t, e, trivial, by omega⟩

/-! ## Re-exports of the seed instances -/

theorem W3_copyNat_holds : W3_copyNat := w3_copyNat

theorem W3_cmpNat_holds : W3_cmpNat := w3_cmpNat

theorem W3_isZeroNat_holds : W3_isZeroNat := w3_isZeroNat

theorem W3_incNat_holds : W3_incNat := w3_incNat

theorem W3_decNat_holds : W3_decNat := w3_decNat

theorem W3_natToInt_holds : W3_natToInt := w3_natToInt

theorem W3_splitSign_holds : W3_splitSign := w3_splitSign

#assert_std_axioms W3_dropNat_holds normProg_eval W3_normNat_holds W3_copyNat_holds
  W3_cmpNat_holds W3_isZeroNat_holds W3_incNat_holds W3_decNat_holds W3_natToInt_holds
  W3_splitSign_holds

end WP.W3
