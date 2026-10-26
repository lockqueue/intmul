/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveParamsDigit

/-!
# SOL-PARAM-ROWS (6): the digit loop and the output drains

`mainLoop`: `digitBody` counted by `kCD` over the `H` digits `u0, …, u0 + H - 1` of the half. The
block's records (`recList`) move from the table onto `kZR`, and each digit's three output records
are replicated `U` times onto `kA0, kA1, kA2` (newest first, `accRev`). `drains`: move the
accumulated records onto `sMU, sNA, sGM`, which restores their order. `runs_mainLoop` and
`runs_drains` give the exact final stacks and explicit costs.

All proved; helpers in `SubNLogN.Machine.Bridge.SolveParamsAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveParamsAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine Computability
open WP.W9comp (runs_seq runs_mono runs_congr)

/-! ## Lists -/

/-- The record payloads of a block: `recBits w (μf u) (xf u) (γf u)` for `u < tl`. -/
def recList (w tl : ℕ) (μf xf γf : ℕ → ℤ) : List (List Bool) :=
  (List.range tl).map fun u => recBits w (μf u) (xf u) (γf u)

theorem recList_drop {w tl : ℕ} {μf xf γf : ℕ → ℤ} {u v : ℕ} (hu : u < tl) (hv : v = u + 1) :
    (recList w tl μf xf γf).drop u =
      recBits w (μf u) (xf u) (γf u) :: (recList w tl μf xf γf).drop v := by
  subst hv
  rw [List.drop_eq_getElem_cons (by simp [recList, hu])]
  simp [recList]

theorem recList_take {w tl : ℕ} {μf xf γf : ℕ → ℤ} {u v : ℕ} (hu : u < tl) (hv : v = u + 1) :
    ((recList w tl μf xf γf).take v).reverse =
      recBits w (μf u) (xf u) (γf u) :: ((recList w tl μf xf γf).take u).reverse := by
  subst hv
  rw [List.take_succ_eq_append_getElem (by simp [recList, hu])]
  simp [recList]

/-- The output records of the digits `j' < j` (newest first), each replicated `U` times. -/
def accRev (w U u0 : ℕ) (g : ℕ → ℤ) (j : ℕ) : List (List Bool) :=
  (List.range j).reverse.flatMap fun j' => List.replicate U (crecBits (w + 1) [(g (u0 + j'), 0)])

theorem accRev_succ (w U u0 : ℕ) (g : ℕ → ℤ) (j : ℕ) :
    accRev w U u0 g (j + 1) =
      List.replicate U (crecBits (w + 1) [(g (u0 + j), 0)]) ++ accRev w U u0 g j := by
  rw [accRev, List.range_succ, List.reverse_append]
  simp [accRev]

theorem accRev_reverse (w U u0 : ℕ) (g : ℕ → ℤ) (j : ℕ) :
    (accRev w U u0 g j).reverse =
      (List.range j).flatMap fun j' => List.replicate U (crecBits (w + 1) [(g (u0 + j'), 0)]) := by
  induction j with
  | zero => simp [accRev]
  | succ j ih =>
    rw [accRev_succ, List.reverse_append, ih, List.reverse_replicate, List.range_succ,
      List.flatMap_append]
    simp

theorem length_accRev (w U u0 : ℕ) (g : ℕ → ℤ) (j : ℕ) : (accRev w U u0 g j).length = j * U := by
  induction j with
  | zero => simp [accRev]
  | succ j ih => rw [accRev_succ, List.length_append, ih, List.length_replicate]; ring

theorem length_mem_accRev {w U u0 : ℕ} {g : ℕ → ℤ} {j : ℕ} :
    ∀ bs ∈ accRev w U u0 g j, bs.length = 2 * (w + 1) := by
  intro bs hbs
  simp only [accRev, List.mem_flatMap, List.mem_replicate] at hbs
  obtain ⟨j', _, _, rfl⟩ := hbs
  exact length_crecBits_one _ _

theorem accRev_ne_nil {w U u0 : ℕ} {g : ℕ → ℤ} {j : ℕ} : ∀ bs ∈ accRev w U u0 g j, bs ≠ [] := by
  intro bs hbs h
  have h2 := length_mem_accRev bs hbs
  rw [h, List.length_nil] at h2
  omega

theorem sum_drain_const (ℓ : ℕ) : ∀ bss : List (List Bool), (∀ bs ∈ bss, bs.length = ℓ) →
    (bss.map fun bs => 6 * bs.length + 12).sum = bss.length * (6 * ℓ + 12)
  | [], _ => by simp
  | bs :: bss, h => by
    rw [List.map_cons, List.sum_cons, h bs List.mem_cons_self,
      sum_drain_const ℓ bss (fun b hb => h b (List.mem_cons_of_mem _ hb)), List.length_cons]
    ring

theorem drainCost_accRev (w U u0 : ℕ) (g : ℕ → ℤ) (j : ℕ) :
    SolveAux.drainCost (accRev w U u0 g j) = j * U * (12 * w + 24) + 1 := by
  rw [SolveAux.drainCost, sum_drain_const (2 * (w + 1)) _ length_mem_accRev, length_accRev]
  ring

/-! ## The digit loop -/

/-- The digit loop: `digitBody` counted by `kCD`. -/
def mainLoop : BProg SK :=
  .seq (BridgeRed.peekTop kCD) (.loop BridgeRed.topIsBit (.seq digitBody (BridgeRed.peekTop kCD)))

theorem accRev_succ' (w U u0 : ℕ) (g : ℕ → ℤ) {j j' : ℕ} (hj : j' = j + 1) :
    accRev w U u0 g j' =
      List.replicate U (crecBits (w + 1) [(g (u0 + j), 0)]) ++ accRev w U u0 g j := by
  subst hj; exact accRev_succ w U u0 g j

theorem runs_mainLoop (w : ℕ) (hw : 1 ≤ w) (tl U u0 H : ℕ) (μf xf γf : ℕ → ℤ)
    (hfit : ∀ u, u < tl → FitsTwos w (μf u) ∧ FitsTwos w (xf u) ∧ FitsTwos w (γf u))
    (hH : u0 + H ≤ tl) (tail : List Sym) (S : SK → List Sym)
    (hTab : S sTab = SolveAux.recsOf ((recList w tl μf xf γf).drop u0) ++ tail)
    (hZR : S kZR = SolveAux.recsOf ((recList w tl μf xf γf).take u0).reverse)
    (hRU : S kRU = ruler w) (hRX : S kRX = ruler (w + 1)) (hRV : S kRV = []) (hTP : S kTP = [])
    (hYT : S kYT = []) (hYT2 : S kYT2 = []) (hW : S kW = []) (hJ : S kJ = [])
    (hY0 : S kY0 = []) (hY1 : S kY1 = []) (hY2 : S kY2 = [])
    (hCU : S kCU = natSyms U) (hCC : S kCC = []) (hCD : S kCD = natSyms H)
    (hA0 : S kA0 = []) (hA1 : S kA1 = []) (hA2 : S kA2 = []) :
    Runs mainLoop S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S sTab (SolveAux.recsOf ((recList w tl μf xf γf).drop (u0 + H)) ++ tail))
        kZR (SolveAux.recsOf ((recList w tl μf xf γf).take (u0 + H)).reverse))
        kA0 (SolveAux.recsOf (accRev w U u0 μf H)))
        kA1 (SolveAux.recsOf (accRev w U u0 (fun u => -xf u) H)))
        kA2 (SolveAux.recsOf (accRev w U u0 γf H)))
        kCD [])
      (fun _ => True) (1 + loopCost (fun n => digitCost w U n + 1) H) := by
  let B : ℕ → SK → List Sym := fun n =>
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update S sTab
        (SolveAux.recsOf ((recList w tl μf xf γf).drop (u0 + (H - n))) ++ tail))
      kZR (SolveAux.recsOf ((recList w tl μf xf γf).take (u0 + (H - n))).reverse))
      kA0 (SolveAux.recsOf (accRev w U u0 μf (H - n))))
      kA1 (SolveAux.recsOf (accRev w U u0 (fun u => -xf u) (H - n))))
      kA2 (SolveAux.recsOf (accRev w U u0 γf (H - n))))
      kCD (natSyms n)
  have hk : ∀ n, n ≤ H → B n kCD = natSyms n := by
    intro n _
    simp [B]
  have hstep : ∀ n, n + 1 ≤ H →
      Runs digitBody (B (n + 1)) (B n) (fun _ => True) (digitCost w U n) := by
    intro n hn
    have hu : u0 + (H - (n + 1)) < tl := by omega
    have hv : u0 + (H - n) = u0 + (H - (n + 1)) + 1 := by omega
    have hj : H - n = H - (n + 1) + 1 := by omega
    obtain ⟨f1, f2, f3⟩ := hfit _ hu
    have hd := recList_drop (w := w) (μf := μf) (xf := xf) (γf := γf) hu hv
    have ht := recList_take (w := w) (μf := μf) (xf := xf) (γf := γf) hu hv
    have a0 := accRev_succ' w U u0 μf hj
    have a1 := accRev_succ' w U u0 (fun u => -xf u) hj
    have a2 := accRev_succ' w U u0 γf hj
    refine runs_congr (runs_digitBody w hw _ _ _ f1 f2 f3 U n
      (SolveAux.recsOf ((recList w tl μf xf γf).drop (u0 + (H - n))) ++ tail) (B (n + 1))
      (by simp [B, hd]) (by simp [B, hRU]) (by simp [B, hRX]) (by simp [B, hRV])
      (by simp [B, hTP]) (by simp [B, hYT]) (by simp [B, hYT2]) (by simp [B, hW])
      (by simp [B, hJ]) (by simp [B, hY0]) (by simp [B, hY1]) (by simp [B, hY2])
      (by simp [B, hCU]) (by simp [B, hCC]) (by simp [B])) ?_
    funext k
    by_cases k1 : k = sTab
    · subst k1; simp [B]
    by_cases k2 : k = kZR
    · subst k2; simp [B, ht]
    by_cases k3 : k = kA0
    · subst k3; simp [B, a0, SolveAux.recsOf_append]
    by_cases k4 : k = kA1
    · subst k4; simp [B, a1, SolveAux.recsOf_append]
    by_cases k5 : k = kA2
    · subst k5; simp [B, a2, SolveAux.recsOf_append]
    by_cases k6 : k = kCD
    · subst k6; simp [B]
    simp [B, Function.update_apply, k1, k2, k3, k4, k5, k6]
  have hL := BridgeRed.runs_counted_loop kCD digitBody B H (fun n => digitCost w U n) hk hstep
  have hBH : B H = S := by
    funext k
    by_cases k1 : k = sTab
    · subst k1; simp [B, hTab]
    by_cases k2 : k = kZR
    · subst k2; simp [B, hZR]
    by_cases k3 : k = kA0
    · subst k3; simp [B, hA0, accRev]
    by_cases k4 : k = kA1
    · subst k4; simp [B, hA1, accRev]
    by_cases k5 : k = kA2
    · subst k5; simp [B, hA2, accRev]
    by_cases k6 : k = kCD
    · subst k6; simp [B, hCD]
    simp [B, Function.update_apply, k1, k2, k3, k4, k5, k6]
  have hB0 : B 0 = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update S sTab
        (SolveAux.recsOf ((recList w tl μf xf γf).drop (u0 + H)) ++ tail))
      kZR (SolveAux.recsOf ((recList w tl μf xf γf).take (u0 + H)).reverse))
      kA0 (SolveAux.recsOf (accRev w U u0 μf H)))
      kA1 (SolveAux.recsOf (accRev w U u0 (fun u => -xf u) H)))
      kA2 (SolveAux.recsOf (accRev w U u0 γf H))) kCD [] := by
    simp [B, natSyms_eq_map, encodeNat_zero]
  rw [hBH, hB0] at hL
  exact hL

/-! ## Draining the accumulators -/

/-- Move the accumulated records onto the output stacks (restoring their order). -/
def drains : BProg SK :=
  .seq (L (SolveAux.drainRecs kA0 sMU kTP)) (.seq (L (SolveAux.drainRecs kA1 sNA kTP))
    (L (SolveAux.drainRecs kA2 sGM kTP)))

/-- The records of an output row: `U` copies of the record of each digit `u0 + j`, `j < H`. -/
def rowRecs (w U u0 H : ℕ) (g : ℕ → ℤ) : List (List Bool) :=
  (List.range H).flatMap fun j => List.replicate U (crecBits (w + 1) [(g (u0 + j), 0)])

theorem runs_drains (w U u0 H : ℕ) (g0 g1 g2 : ℕ → ℤ) (S : SK → List Sym)
    (hA0 : S kA0 = SolveAux.recsOf (accRev w U u0 g0 H))
    (hA1 : S kA1 = SolveAux.recsOf (accRev w U u0 g1 H))
    (hA2 : S kA2 = SolveAux.recsOf (accRev w U u0 g2 H)) (hTP : S kTP = []) :
    Runs drains S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S kA0 []) kA1 []) kA2 [])
        sMU (SolveAux.recsOf (rowRecs w U u0 H g0) ++ S sMU))
        sNA (SolveAux.recsOf (rowRecs w U u0 H g1) ++ S sNA))
        sGM (SolveAux.recsOf (rowRecs w U u0 H g2) ++ S sGM))
      (fun _ => True) (3 * (H * U * (12 * w + 24) + 2)) := by
  refine runs_mono (runs_congr (runs_seq
    (runs_L (K := SK) fun v => ⟨_, SolveAux.drainRecs_eval (A := kA0) (B := sMU) (tmp := kTP)
      (by decide) (by decide) (by decide) v (accRev w U u0 g0 H) [] S accRev_ne_nil
      (by rw [hA0, List.append_nil]) termOK_nil (by rw [hTP]; exact termOK_nil)⟩)
    (runs_seq (runs_L (K := SK) fun v => ⟨_, SolveAux.drainRecs_eval (A := kA1) (B := sNA)
      (tmp := kTP) (by decide) (by decide) (by decide) v (accRev w U u0 g1 H) [] _ accRev_ne_nil
      (by simp [Function.update_apply, hA1]) termOK_nil
      (by simpa [Function.update_apply, hTP] using termOK_nil)⟩)
    (runs_L (K := SK) fun v => ⟨_, SolveAux.drainRecs_eval (A := kA2) (B := sGM) (tmp := kTP)
      (by decide) (by decide) (by decide) v (accRev w U u0 g2 H) [] _ accRev_ne_nil
      (by simp [Function.update_apply, hA2]) termOK_nil
      (by simpa [Function.update_apply, hTP] using termOK_nil)⟩))) ?_)
    (fun _ _ => trivial) (by simp only [drainCost_accRev]; omega)
  funext k
  by_cases k1 : k = kA0
  · subst k1; simp [Function.update_apply]
  by_cases k2 : k = kA1
  · subst k2; simp [Function.update_apply]
  by_cases k3 : k = kA2
  · subst k3; simp [Function.update_apply]
  by_cases k4 : k = sMU
  · subst k4; simp [Function.update_apply, accRev_reverse, rowRecs]
  by_cases k5 : k = sNA
  · subst k5; simp [Function.update_apply, accRev_reverse, rowRecs]
  by_cases k6 : k = sGM
  · subst k6; simp [Function.update_apply, accRev_reverse, rowRecs]
  simp [Function.update_apply, k1, k2, k3, k4, k5, k6]

end SubNLogN.Machine.Bridge.SolveParamsAux
