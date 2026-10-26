/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadBlockA

/-!
# K5 spreading: the AR pre-stage setup (`Bridge/SpreadStageAR.lean`)

* `stagePre` and `stagePre_eval`: build the five product rulers `pr 0 … pr 4` (`mulRuler_step` on
  `mulRuler`, temporaries `X 0`, `X 7`) and skip the tap-table blocks before the axis block onto
  `TT` (walk over `ru skip`, temporary `X 3`, body `mvBlockM`), within cost `stagePreCost`.
  (The companion post-stage cleanup `stagePost_eval` restoring the tap table, moving `Out` onto
  `arr`, and clearing all rulers is proved in `Bridge/SpreadStageAR2.lean`.)

Stated on arbitrary stacks `S` with explicit final states. Everything is proved.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

variable {Esu : Type} [DecidableEq Esu]

/-- Product rulers and the tap-table skip. -/
def stagePre : AProg (SK Esu) :=
  .seq (mulRuler (sp (.ru .Wm1)) (sp (.X 0)) (sp (.ru .recw)) (sp (.X 7)) (sp (.pr 0)))
  (.seq (mulRuler (sp (.ru .t)) (sp (.X 0)) (sp (.ru .recw)) (sp (.X 7)) (sp (.pr 1)))
  (.seq (mulRuler (sp (.ru .a0)) (sp (.X 0)) (sp (.ru .recw)) (sp (.X 7)) (sp (.pr 2)))
  (.seq (mulRuler (sp (.ru .ta)) (sp (.X 0)) (sp (.ru .recw)) (sp (.X 7)) (sp (.pr 3)))
  (.seq (mulRuler (sp (.ru .Wm1)) (sp (.X 0)) (sp (.ru .s)) (sp (.X 7)) (sp (.pr 4)))
  (.seq (walk (sp (.ru .skip)) (sp (.X 3)) (mvBlockM (kN .tapTab) (sp .TT)))
    (moveMarks (sp (.X 3)) (sp (.ru .skip))))))))

/-- Cost bound of `stagePre`. -/
def stagePreCost (nW nr nt na nta ns nk L : ℕ) : ℕ :=
  (nW * (9 * nr + 8) + 4 * nW + 4) + (nt * (9 * nr + 8) + 4 * nt + 4) +
    (na * (9 * nr + 8) + 4 * na + 4) + (nta * (9 * nr + 8) + 4 * nta + 4) +
    (nW * (9 * ns + 8) + 4 * nW + 4) + (nk * (3 * L + 5 + 4) + 2) + (4 * nk + 2)

/-- One product ruler on top of an empty stack. -/
theorem mulRuler_step (R1 R2 X1 X2 D : SpS) (h1 : R1 ≠ X1) (h2 : R1 ≠ R2) (h3 : R1 ≠ X2)
    (h4 : R1 ≠ D) (h5 : X1 ≠ R2) (h6 : X1 ≠ X2) (h7 : X1 ≠ D) (h8 : R2 ≠ X2) (h9 : R2 ≠ D)
    (h10 : X2 ≠ D) (n1 n2 : ℕ) (S : SK Esu → List Sym) (v : AReg)
    (hX1 : S (sp X1) = []) (hX2 : S (sp X2) = []) (hR1 : S (sp R1) = List.replicate n1 .mark)
    (hR2 : S (sp R2) = List.replicate n2 .mark) (hD : S (sp D) = []) :
    ∃ v', Eval [] (mulRuler (sp R1) (sp X1) (sp R2) (sp X2) (sp D)) ⟨v, S⟩
      ⟨v', Function.update S (sp D) (List.replicate (n1 * n2) .mark)⟩
      (n1 * (9 * n2 + 8) + 4 * n1 + 4) := by
  have inj := sp_injective (Esu := Esu)
  obtain ⟨v', e⟩ := mulRuler_eval (fun h => h1 (inj h)) (fun h => h2 (inj h)) (fun h => h3 (inj h))
    (fun h => h4 (inj h)) (fun h => h5 (inj h)) (fun h => h6 (inj h)) (fun h => h7 (inj h))
    (fun h => h8 (inj h)) (fun h => h9 (inj h)) (fun h => h10 (inj h)) n1 n2 [] [] S (by simp)
    (by simp) (by rw [hX1]; simp) (by rw [hX2]; simp) (by rw [hR1, List.append_nil])
    (by rw [hR2, List.append_nil]) v
  rw [hD, List.append_nil] at e
  exact ⟨v', e⟩

theorem stagePre_eval (nW nr nt na nta ns nk : ℕ) (blks : List (List Sym)) (rest : List Sym)
    (S : SK Esu → List Sym) (v : AReg)
    (hWm1 : S (sp (.ru .Wm1)) = List.replicate nW .mark)
    (hrecw : S (sp (.ru .recw)) = List.replicate nr .mark)
    (ht : S (sp (.ru .t)) = List.replicate nt .mark)
    (ha0 : S (sp (.ru .a0)) = List.replicate na .mark)
    (hta : S (sp (.ru .ta)) = List.replicate nta .mark)
    (hs : S (sp (.ru .s)) = List.replicate ns .mark)
    (hskip : S (sp (.ru .skip)) = List.replicate nk .mark)
    (hpr : ∀ k, S (sp (.pr k)) = []) (hX0 : S (sp (.X 0)) = []) (hX7 : S (sp (.X 7)) = [])
    (hX3 : S (sp (.X 3)) = []) (hTT : S (sp .TT) = [])
    (htap : S (kN .tapTab) = blks.flatMap (· ++ [.mark]) ++ rest) (hlen : blks.length = nk)
    (hmk : ∀ b ∈ blks, ∀ x ∈ b, x ≠ .mark) :
    ∃ v' c, Eval [] stagePre ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S (sp (.pr 0)) (List.replicate (nW * nr) .mark))
          (sp (.pr 1)) (List.replicate (nt * nr) .mark))
          (sp (.pr 2)) (List.replicate (na * nr) .mark))
          (sp (.pr 3)) (List.replicate (nta * nr) .mark))
          (sp (.pr 4)) (List.replicate (nW * ns) .mark))
          (kN .tapTab) rest) (sp .TT) (blks.flatMap (· ++ [.mark])).reverse⟩ c ∧
      c ≤ stagePreCost nW nr nt na nta ns nk (blks.flatMap (· ++ [.mark])).length := by
  -- the five product rulers
  obtain ⟨v1, e1⟩ := mulRuler_step (Esu := Esu) (.ru .Wm1) (.ru .recw) (.X 0) (.X 7) (.pr 0)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) nW nr S v hX0 hX7 hWm1 hrecw (hpr 0)
  set S1 := Function.update S (sp (.pr 0)) (List.replicate (nW * nr) .mark) with hS1
  obtain ⟨v2, e2⟩ := mulRuler_step (Esu := Esu) (.ru .t) (.ru .recw) (.X 0) (.X 7) (.pr 1)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) nt nr S1 v1 (by simp [hS1, Function.update_apply, hX0])
    (by simp [hS1, Function.update_apply, hX7]) (by simp [hS1, Function.update_apply, ht])
    (by simp [hS1, Function.update_apply, hrecw]) (by simp [hS1, Function.update_apply, hpr])
  set S2 := Function.update S1 (sp (.pr 1)) (List.replicate (nt * nr) .mark) with hS2
  obtain ⟨v3, e3⟩ := mulRuler_step (Esu := Esu) (.ru .a0) (.ru .recw) (.X 0) (.X 7) (.pr 2)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) na nr S2 v2 (by simp [hS2, hS1, Function.update_apply, hX0])
    (by simp [hS2, hS1, Function.update_apply, hX7]) (by simp [hS2, hS1, Function.update_apply, ha0])
    (by simp [hS2, hS1, Function.update_apply, hrecw])
    (by simp [hS2, hS1, Function.update_apply, hpr])
  set S3 := Function.update S2 (sp (.pr 2)) (List.replicate (na * nr) .mark) with hS3
  obtain ⟨v4, e4⟩ := mulRuler_step (Esu := Esu) (.ru .ta) (.ru .recw) (.X 0) (.X 7) (.pr 3)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) nta nr S3 v3 (by simp [hS3, hS2, hS1, Function.update_apply, hX0])
    (by simp [hS3, hS2, hS1, Function.update_apply, hX7])
    (by simp [hS3, hS2, hS1, Function.update_apply, hta])
    (by simp [hS3, hS2, hS1, Function.update_apply, hrecw])
    (by simp [hS3, hS2, hS1, Function.update_apply, hpr])
  set S4 := Function.update S3 (sp (.pr 3)) (List.replicate (nta * nr) .mark) with hS4
  obtain ⟨v5, e5⟩ := mulRuler_step (Esu := Esu) (.ru .Wm1) (.ru .s) (.X 0) (.X 7) (.pr 4)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) nW ns S4 v4 (by simp [hS4, hS3, hS2, hS1, Function.update_apply, hX0])
    (by simp [hS4, hS3, hS2, hS1, Function.update_apply, hX7])
    (by simp [hS4, hS3, hS2, hS1, Function.update_apply, hWm1])
    (by simp [hS4, hS3, hS2, hS1, Function.update_apply, hs])
    (by simp [hS4, hS3, hS2, hS1, Function.update_apply, hpr])
  set S5 := Function.update S4 (sp (.pr 4)) (List.replicate (nW * ns) .mark) with hS5
  have l5 : ∀ k, k ≠ sp (.pr 0) → k ≠ sp (.pr 1) → k ≠ sp (.pr 2) → k ≠ sp (.pr 3) →
      k ≠ sp (.pr 4) → S5 k = S k := by
    intro k a b c d e
    simp [hS5, hS4, hS3, hS2, hS1, Function.update_of_ne, a, b, c, d, e]
  -- the tap skip
  set P := blks.flatMap (· ++ [Sym.mark]) with hP
  let Sf : ℕ → SK Esu → List Sym := fun j => Function.update (Function.update (Function.update
    (Function.update S5 (sp (.ru .skip)) (List.replicate (nk - j) .mark)) (sp (.X 3))
      (List.replicate j .mark)) (kN .tapTab) ((blks.drop j).flatMap (· ++ [Sym.mark]) ++ rest))
    (sp .TT) ((blks.take j).flatMap (· ++ [Sym.mark])).reverse
  have hSR : ∀ j ≤ nk, Sf j (sp (.ru .skip)) = List.replicate (nk - j) .mark ++ [] := by
    intro j _; simp [Sf, Function.update_apply]
  have h0 : Sf 0 = S5 := by
    funext k
    simp only [Sf, Function.update_apply, Nat.sub_zero, List.replicate_zero, List.drop_zero,
      List.take_zero, List.flatMap_nil, List.reverse_nil]
    split_ifs with a b c d
    · rw [a, l5 _ (by simp) (by simp) (by simp) (by simp) (by simp), hTT]
    · rw [b, l5 _ (by simp) (by simp) (by simp) (by simp) (by simp), htap]
    · rw [c, l5 _ (by simp) (by simp) (by simp) (by simp) (by simp), hX3]
    · rw [d, l5 _ (by simp) (by simp) (by simp) (by simp) (by simp), hskip]
    · rfl
  obtain ⟨v6, c6, e6, hc6⟩ := walk_eval_bounded (R := sp (.ru .skip)) (X := sp (.X 3)) (by simp)
    (mvBlockM (kN .tapTab) (sp .TT)) nk [] (by simp) Sf hSR (3 * P.length + 5)
    (fun j hj u => by
      clear h0 hSR
      have hj' : j < blks.length := by omega
      have hdrop : blks.drop j = blks[j] :: blks.drop (j + 1) := List.drop_eq_getElem_cons hj'
      set S' := Function.update (Function.update (Sf j) (sp (.ru .skip))
          (List.replicate (nk - j - 1) .mark ++ [])) (sp (.X 3)) (.mark :: Sf j (sp (.X 3)))
        with hS'
      have hsrc : S' (kN .tapTab) = blks[j] ++ .mark ::
          ((blks.drop (j + 1)).flatMap (· ++ [Sym.mark]) ++ rest) := by
        rw [hS', Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
        show Function.update _ (sp .TT) _ (kN .tapTab) = _
        rw [Function.update_of_ne (by simp), Function.update_self, hdrop, List.flatMap_cons]
        simp [List.append_assoc]
      have hdst : S' (sp .TT) = ((blks.take j).flatMap (· ++ [Sym.mark])).reverse := by
        rw [hS', Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
        show Function.update _ (sp .TT) _ (sp .TT) = _
        rw [Function.update_self]
      obtain ⟨w, e⟩ := mvBlockM_eval (src := kN .tapTab) (dst := sp .TT) (by simp) blks[j]
        ((blks.drop (j + 1)).flatMap (· ++ [Sym.mark]) ++ rest) u S'
        (hmk _ (List.getElem_mem hj')) hsrc
      rw [hdst] at e
      refine ⟨w, _, e.of_eq ?_ rfl, ?_⟩
      · congr 1
        have htk : (blks.take (j + 1)).flatMap (· ++ [Sym.mark]) =
            (blks.take j).flatMap (· ++ [Sym.mark]) ++ (blks[j] ++ [Sym.mark]) := by
          rw [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
            List.flatMap_append, List.flatMap_singleton]
        funext k
        rw [hS']
        simp only [Sf, Function.update_apply]
        clear hS1 hS2 hS3 hS4 hS5 l5 hsrc hdst hS' e
        split_ifs <;> simp_all [htk, List.replicate_succ, List.reverse_append, Nat.sub_sub,
          List.append_assoc]
      · have hmem := List.getElem_mem hj'
        have h1 : (blks[j] ++ [Sym.mark]).length ≤ P.length := by
          rw [hP, List.length_flatMap]
          exact List.le_sum_of_mem (List.mem_map_of_mem (f := fun b => (b ++ [Sym.mark]).length)
            hmem)
        simp at h1
        omega) v5
  rw [h0] at e6
  have e7 := moveMarks_eval (X := sp (.X 3)) (R := sp (.ru .skip)) (by simp) nk [] v6 (Sf nk)
    (by simp) (by simp [Sf, Function.update_apply])
  refine ⟨{ v6 with r := ([] : List Sym).head? }, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3
    (Eval.seq e4 (Eval.seq e5 (Eval.seq e6 e7)))))).of_eq ?_ rfl, ?_⟩
  · congr 1
    funext k
    clear e1 e2 e3 e4 e5 e6 e7 h0 hSR
    subst hlen
    by_cases h1 : k = sp (.ru .skip)
    · subst h1
      simp only [Function.update_self, Function.update_of_ne (show sp (Esu := Esu) (.ru .skip) ≠
        sp .TT by simp), Function.update_of_ne (show sp (Esu := Esu) (.ru .skip) ≠ kN .tapTab by
        simp)]
      rw [l5 _ (by simp) (by simp) (by simp) (by simp) (by simp), hskip]
      simp [Sf]
    by_cases h2 : k = sp (.X 3)
    · subst h2
      rw [Function.update_of_ne (show sp (Esu := Esu) (.X 3) ≠ sp (.ru .skip) by simp),
        Function.update_self, Function.update_of_ne (show sp (Esu := Esu) (.X 3) ≠ sp .TT by simp),
        Function.update_of_ne (show sp (Esu := Esu) (.X 3) ≠ kN .tapTab by simp),
        l5 _ (by simp) (by simp) (by simp) (by simp) (by simp), hX3]
    by_cases h3 : k = kN .tapTab
    · subst h3
      rw [Function.update_of_ne (show kN (E := SpS ⊕ Esu) .tapTab ≠ sp (.ru .skip) by simp),
        Function.update_of_ne (show kN (E := SpS ⊕ Esu) .tapTab ≠ sp (.X 3) by simp),
        Function.update_of_ne (show kN (E := SpS ⊕ Esu) .tapTab ≠ sp .TT by simp),
        Function.update_self]
      simp [Sf]
    by_cases h4 : k = sp .TT
    · subst h4
      rw [Function.update_of_ne (show sp (Esu := Esu) .TT ≠ sp (.ru .skip) by simp),
        Function.update_of_ne (show sp (Esu := Esu) .TT ≠ sp (.X 3) by simp),
        Function.update_self]
      simp [Sf, hP]
    rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h4,
      Function.update_of_ne h3]
    simp only [Sf, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4]
  · unfold stagePreCost
    omega

end SubNLogN.Machine.Bridge.SpreadAux
