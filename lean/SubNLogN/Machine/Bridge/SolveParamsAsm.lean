/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveParamsMain
import SubNLogN.Machine.Bridge.SolveParamsNav

/-!
# SOL-PARAM-ROWS (8): the body after the header parse

`bodyB` runs after the header parse, in this order:
1. navigate to block `i` (`navLoop`);
2. skip the first half if `h = 1` (`halfLoop`);
3. run the digit loop (`mainLoop`) and the drains onto `sMU, sNA, sGM`;
4. put the block's records back and restore the skipped blocks (`restLoop`);
5. clear the five header-derived stacks.

`runs_bodyB` gives the exact final stacks and the explicit cost `bodyCost`.

All proved; helpers in `SubNLogN.Machine.Bridge.SolveParamsAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveParamsAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine Computability
open WP.W9comp (runs_seq runs_mono runs_congr)

theorem recsOf_take_drop (l : List (List Bool)) (n : ℕ) (t : List Sym) :
    SolveAux.recsOf (l.take n) ++ (SolveAux.recsOf (l.drop n) ++ t) = SolveAux.recsOf l ++ t := by
  rw [← List.append_assoc, ← SolveAux.recsOf_append, List.take_append_drop]

/-- The body after the header parse. -/
def bodyB : BProg SK :=
  .seq (L (copyBlock kCX kCD kTP)) (.seq navLoop (.seq halfLoop
  (.seq (L (copyBlock kCT kCD kTP)) (.seq mainLoop (.seq drains
  (.seq (L (SolveAux.drainRecs kZR sTab kTP)) (.seq (L (copyBlock kCX kCD kTP)) (.seq restLoop
  (.seq (clearBits kRU) (.seq (clearBits kRX) (.seq (clearBits kCX) (.seq (clearBits kCT)
    (clearBits kCU)))))))))))))

/-- The cost of `bodyB`. -/
def bodyCost (w N H U u0 : ℕ) (bl : List (List (List Bool))) (rl : List (List Bool)) : ℕ :=
  (7 * bitLen N + 7) + (1 + loopCost (fun n => navStepCost (bl.getD (N - (n + 1)) []) n + 1) N) +
  (H * (6 * (6 * w) + 6 * bitLen H + 20) + 7 * bitLen H + 50) + (7 * bitLen H + 7) +
  (1 + loopCost (fun n => digitCost w U n + 1) H) + 3 * (H * U * (12 * w + 24) + 2) +
  (SolveAux.drainCost (rl.take (u0 + H)).reverse + 1) + (7 * bitLen N + 7) +
  (1 + loopCost (fun n => navStepCost (bl.getD n []).reverse n + 1) N) +
  ((3 * w + 2) + (3 * (w + 1) + 2) + (3 * bitLen N + 2) + (3 * bitLen H + 2) + (3 * bitLen U + 2))

theorem runs_bodyB (w : ℕ) (hw : 1 ≤ w) (bl : List (List (List Bool))) (N : ℕ)
    (hN : N < bl.length) (hbl : ∀ rs ∈ bl, ∀ bs ∈ rs, bs.length = 6 * w)
    (tl U H h : ℕ) (hh : h ≤ 1) (hH : 2 * H ≤ tl) (μf xf γf : ℕ → ℤ)
    (hfit : ∀ u, u < tl → FitsTwos w (μf u) ∧ FitsTwos w (xf u) ∧ FitsTwos w (γf u))
    (hrl : bl[N] = recList w tl μf xf γf) (rsol rh : List Sym) (hrh : TermOK rh)
    (S : SK → List Sym) (c : ∀ e : Fin 25, S (.inr e) = [])
    (hTab : S sTab = tabSyms bl ++ rsol) (hHalf : S sHalf = natSyms h ++ rh) :
    Runs bodyB
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        kRU (ruler w)) kRX (ruler (w + 1))) kCX (natSyms N)) kCT (natSyms H)) kCU (natSyms U))
      (Function.update (Function.update (Function.update S
        sMU (SolveAux.recsOf (rowRecs w U (h * H) H μf) ++ S sMU))
        sNA (SolveAux.recsOf (rowRecs w U (h * H) H (fun u => -xf u)) ++ S sNA))
        sGM (SolveAux.recsOf (rowRecs w U (h * H) H γf) ++ S sGM))
      (fun _ => True) (bodyCost w N H U (h * H) bl (recList w tl μf xf γf)) := by
  have cRU : S kRU = [] := c 2
  have cRX : S kRX = [] := c 3
  have cRV : S kRV = [] := c 4
  have cTP : S kTP = [] := c 5
  have cCX : S kCX = [] := c 7
  have cCT : S kCT = [] := c 8
  have cCU : S kCU = [] := c 9
  have cCC : S kCC = [] := c 10
  have cCD : S kCD = [] := c 11
  have cZB : S kZB = [] := c 12
  have cZR : S kZR = [] := c 13
  have cW : S kW = [] := c 14
  have cYT : S kYT = [] := c 15
  have cYT2 : S kYT2 = [] := c 16
  have cJ : S kJ = [] := c 17
  have cY0 : S kY0 = [] := c 18
  have cY1 : S kY1 = [] := c 19
  have cY2 : S kY2 = [] := c 20
  have cA0 : S kA0 = [] := c 21
  have cA1 : S kA1 = [] := c 22
  have cA2 : S kA2 = [] := c 23
  have cCY : S kCY = [] := c 24
  have hne : ∀ rs ∈ bl, ∀ bs ∈ rs, bs ≠ [] := fun rs hrs bs hbs h0 => by
    have := hbl rs hrs bs hbs
    rw [h0, List.length_nil] at this
    omega
  have hlenrl : (recList w tl μf xf γf).length = tl := by simp [recList]
  have hℓ : ∀ bs ∈ recList w tl μf xf γf, bs.length = 6 * w := by
    intro bs hbs
    simp only [recList, List.mem_map] at hbs
    obtain ⟨u, _, rfl⟩ := hbs
    exact length_recBits w _ _ _
  have hsplit : tabSyms (bl.drop N) =
      SolveAux.recsOf (recList w tl μf xf γf) ++ Sym.mark :: tabSyms (bl.drop (N + 1)) := by
    rw [List.drop_eq_getElem_cons hN, tabSyms_cons, hrl]
  have hu0H : h * H + H ≤ tl := by
    rcases (show h = 0 ∨ h = 1 by omega) with rfl | rfl <;> omega
  have hneR : ∀ bs ∈ ((recList w tl μf xf γf).take (h * H + H)).reverse, bs ≠ [] := by
    intro bs hbs h0
    have := hℓ bs (List.mem_of_mem_take (List.mem_reverse.mp hbs))
    rw [h0, List.length_nil] at this
    omega
  refine runs_mono (runs_congr (runs_seq
    (runs_L_copyBlock (src := kCX) (dst := kCD) (tmp := kTP) (by decide) (by decide) (by decide)
      (encodeNat N) [] _ termOK_nil (by simp [Function.update_apply, natSyms_eq_map]))
    (runs_seq (runs_navLoop bl hne rsol N hN.le _ (by simp [Function.update_apply, hTab])
      (by simp [Function.update_apply, cZB]) (by simp [Function.update_apply, cTP])
      (by simp [Function.update_apply, cCD, natSyms_eq_map]))
    (runs_seq (runs_halfLoop (recList w tl μf xf γf) (6 * w) hℓ
      (Sym.mark :: (tabSyms (bl.drop (N + 1)) ++ rsol)) H h hh (by omega) rh hrh _
      (by simp [Function.update_apply, hsplit]) (by simp [Function.update_apply, cZR])
      (by simp [Function.update_apply, cTP]) (by simp [Function.update_apply])
      (by simp [Function.update_apply, cCY]) (by simp [Function.update_apply])
      (by simp [Function.update_apply, hHalf]))
    (runs_seq (runs_L_copyBlock (src := kCT) (dst := kCD) (tmp := kTP) (by decide) (by decide)
      (by decide) (encodeNat H) [] _ termOK_nil (by simp [Function.update_apply, natSyms_eq_map]))
    (runs_seq (runs_mainLoop w hw tl U (h * H) H μf xf γf hfit hu0H
      (Sym.mark :: (tabSyms (bl.drop (N + 1)) ++ rsol)) _
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
      (by simp [Function.update_apply, cRV]) (by simp [Function.update_apply, cTP])
      (by simp [Function.update_apply, cYT]) (by simp [Function.update_apply, cYT2])
      (by simp [Function.update_apply, cW]) (by simp [Function.update_apply, cJ])
      (by simp [Function.update_apply, cY0]) (by simp [Function.update_apply, cY1])
      (by simp [Function.update_apply, cY2]) (by simp [Function.update_apply])
      (by simp [Function.update_apply, cCC]) (by simp [Function.update_apply, natSyms_eq_map])
      (by simp [Function.update_apply, cA0]) (by simp [Function.update_apply, cA1])
      (by simp [Function.update_apply, cA2]))
    (runs_seq (runs_drains w U (h * H) H μf (fun u => -xf u) γf _
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
      (by simp [Function.update_apply]) (by simp [Function.update_apply, cTP]))
    (runs_seq (runs_L (K := SK) fun v => ⟨_, SolveAux.drainRecs_eval (A := kZR) (B := sTab)
      (tmp := kTP) (by decide) (by decide) (by decide) v
      ((recList w tl μf xf γf).take (h * H + H)).reverse [] _ hneR
      (by simp [Function.update_apply]) termOK_nil
      (by simpa [Function.update_apply, cTP] using termOK_nil)⟩)
    (runs_seq (runs_L_copyBlock (src := kCX) (dst := kCD) (tmp := kTP) (by decide) (by decide)
      (by decide) (encodeNat N) [] _ termOK_nil (by simp [Function.update_apply, natSyms_eq_map]))
    (runs_seq (runs_restLoop bl hne rsol N hN.le _
      (by simp [Function.update_apply, recsOf_take_drop, hsplit])
      (by simp [Function.update_apply]) (by simp [Function.update_apply, cTP])
      (by simp [Function.update_apply, natSyms_eq_map]))
    (runs_seq (runs_clearBits kRU (List.replicate w false) [] termOK_nil _
      (by simp [Function.update_apply, ruler_eq]))
    (runs_seq (runs_clearBits kRX (List.replicate (w + 1) false) [] termOK_nil _
      (by simp [Function.update_apply, ruler_eq]))
    (runs_seq (runs_clearBits kCX (encodeNat N) [] termOK_nil _
      (by simp [Function.update_apply, natSyms_eq_map]))
    (runs_seq (runs_clearBits kCT (encodeNat H) [] termOK_nil _
      (by simp [Function.update_apply, natSyms_eq_map]))
      (runs_clearBits kCU (encodeNat U) [] termOK_nil _
        (by simp [Function.update_apply, natSyms_eq_map]))))))))))))))) ?_)
    (fun _ _ => trivial) ?_
  · funext k
    by_cases k1 : k = sTab
    · subst k1; simp [Function.update_apply, hTab]
    by_cases k2 : k = sMU
    · subst k2; simp [Function.update_apply]
    by_cases k3 : k = sNA
    · subst k3; simp [Function.update_apply]
    by_cases k4 : k = sGM
    · subst k4; simp [Function.update_apply]
    by_cases k5 : k = kRU
    · subst k5; simp [Function.update_apply, cRU]
    by_cases k6 : k = kRX
    · subst k6; simp [Function.update_apply, cRX]
    by_cases k7 : k = kCX
    · subst k7; simp [Function.update_apply, cCX]
    by_cases k8 : k = kCT
    · subst k8; simp [Function.update_apply, cCT]
    by_cases k9 : k = kCU
    · subst k9; simp [Function.update_apply, cCU]
    by_cases k10 : k = kCD
    · subst k10; simp [Function.update_apply, cCD]
    by_cases k11 : k = kZB
    · subst k11; simp [Function.update_apply, cZB]
    by_cases k12 : k = kZR
    · subst k12; simp [Function.update_apply, cZR]
    by_cases k13 : k = kA0
    · subst k13; simp [Function.update_apply, cA0]
    by_cases k14 : k = kA1
    · subst k14; simp [Function.update_apply, cA1]
    by_cases k15 : k = kA2
    · subst k15; simp [Function.update_apply, cA2]
    simp [Function.update_apply, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15]
  · simp only [bodyCost, bitLen, List.length_replicate]
    omega

end SubNLogN.Machine.Bridge.SolveParamsAux
