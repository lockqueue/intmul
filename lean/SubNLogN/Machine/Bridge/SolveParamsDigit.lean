/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveParamsEmit

/-!
# SOL-PARAM-ROWS (5): one digit of the half

`digitSplit`: move the digit's solver record `[μ̂, â, γ̂]` from the table to `kZR`, copy it to `kW`
and stage the three output records `(μ̂, 0)`, `(-â, 0)`, `(γ̂, 0)` at width `wT + 1` on
`kY0, kY1, kY2`. `emitOne`: replicate a staged record `U` times onto its accumulator.
`digitBody`: both, then decrement the digit counter `kCD`.

All proved; helpers in `SubNLogN.Machine.Bridge.SolveParamsAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveParamsAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine Computability
open WP.W9comp (runs_seq runs_mono runs_congr)

theorem runs_popB (k : SK) (x : Sym) (L' : List Sym) (S : SK → List Sym) (hS : S k = x :: L') :
    Runs (popB k) S (Function.update S k L') (fun _ => True) 1 := by
  refine Runs.of_eval fun v => ⟨(some x, v.2), 1, ?_, trivial, le_refl _⟩
  have := Eval.pop [] k (fun (v : BReg) o => (o, v.2)) v S
  rw [hS] at this
  exact this

/-- The six fields of a solver record. -/
def recBits (w : ℕ) (μ x γ : ℤ) : List Bool :=
  twosBits w μ ++ twosBits w 0 ++ twosBits w x ++ twosBits w 0 ++ twosBits w γ ++ twosBits w 0

theorem length_recBits (w : ℕ) (μ x γ : ℤ) : (recBits w μ x γ).length = 6 * w := by
  simp [recBits, K1.length_twosBits]; ring

/-- Move the digit record and stage its three output records. -/
def digitSplit : BProg SK :=
  .seq (L (SolveAux.moveRec sTab kZR kTP))
  (.seq (L (SolveAux.copyRec kZR kW kTP))
  (.seq (pushCB kJ .sep)
  (.seq (stageId kY0)
  (.seq (stageNeg kY1)
  (.seq (stageId kY2)
  (.seq (popB kW)
    (L (SolveAux.eraseRec kJ))))))))

theorem runs_digitSplit (w : ℕ) (hw : 1 ≤ w) (μ x γ : ℤ) (hμ : FitsTwos w μ) (hx : FitsTwos w x)
    (hγ : FitsTwos w γ) (tabRest : List Sym) (S : SK → List Sym)
    (hTab : S sTab = recSyms (recBits w μ x γ) ++ tabRest)
    (hRU : S kRU = ruler w) (hRX : S kRX = ruler (w + 1)) (hRV : S kRV = []) (hTP : S kTP = [])
    (hYT : S kYT = []) (hYT2 : S kYT2 = []) (hW : S kW = []) (hJ : S kJ = [])
    (hY0 : S kY0 = []) (hY1 : S kY1 = []) (hY2 : S kY2 = []) :
    Runs digitSplit S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        sTab tabRest) kZR (recSyms (recBits w μ x γ) ++ S kZR))
        kY0 (recSyms (crecBits (w + 1) [(μ, 0)])))
        kY1 (recSyms (crecBits (w + 1) [(-x, 0)])))
        kY2 (recSyms (crecBits (w + 1) [(γ, 0)])))
      (fun _ => True) (200 * w + 200) := by
  have hlen := length_recBits w μ x γ
  set bs := recBits w μ x γ with hbs
  refine runs_mono (runs_congr (runs_seq
    (runs_L (K := SK) fun v => ⟨_, SolveAux.moveRec_eval (src := sTab) (dst := kZR) (tmp := kTP)
      (by decide) (by decide) (by decide) v bs tabRest S hTab (by rw [hTP]; exact termOK_nil)⟩)
    (runs_seq (runs_L (K := SK) fun v => ⟨_, SolveAux.copyRec_eval (src := kZR) (dst := kW)
      (tmp := kTP) (by decide) (by decide) (by decide) v bs (S kZR) _
      (by simp [Function.update_apply])⟩)
    (runs_seq (runs_pushCB kJ Sym.sep _)
    (runs_seq (runs_stageId kY0 (Or.inl rfl) w hw μ hμ
      ((twosBits w x ++ twosBits w 0 ++ twosBits w γ ++ twosBits w 0).map Sym.bit ++ [Sym.sep]) _
      (by simp [Function.update_apply, hRU]) (by simp [Function.update_apply, hRX])
      (by simp [Function.update_apply, hRV]) (by simp [Function.update_apply, hYT])
      (by simp [Function.update_apply, hW, hbs, recBits, recSyms]))
    (runs_seq (runs_stageNeg kY1 (Or.inr (Or.inl rfl)) w hw x hx
      ((twosBits w γ ++ twosBits w 0).map Sym.bit ++ [Sym.sep]) _
      (by simp [Function.update_apply, hRU]) (by simp [Function.update_apply, hRX])
      (by simp [Function.update_apply, hRV]) (by simp [Function.update_apply, hYT])
      (by simp [Function.update_apply, hYT2])
      (by simp [Function.update_apply]))
    (runs_seq (runs_stageId kY2 (Or.inr (Or.inr rfl)) w hw γ hγ [Sym.sep] _
      (by simp [Function.update_apply, hRU]) (by simp [Function.update_apply, hRX])
      (by simp [Function.update_apply, hRV]) (by simp [Function.update_apply, hYT])
      (by simp [Function.update_apply]))
    (runs_seq (runs_popB kW Sym.sep [] _ (by simp [Function.update_apply]))
      (runs_L (K := SK) fun v => ⟨_, SolveAux.eraseRec_eval kJ v
        (List.replicate w false ++ List.replicate w false ++ List.replicate w false) [] _
        (by simp [Function.update_apply, hJ, ruler_eq, recSyms]
            simp only [← List.append_assoc, List.replicate_append_replicate, Nat.add_assoc])⟩))))))))
    ?_) (fun _ _ => trivial) (by simp [hlen, K1.length_twosBits]; omega)
  funext k
  by_cases k1 : k = sTab
  · subst k1; simp [Function.update_apply]
  by_cases k2 : k = kZR
  · subst k2; simp [Function.update_apply]
  by_cases k3 : k = kW
  · subst k3; simp [Function.update_apply, hW]
  by_cases k4 : k = kJ
  · subst k4; simp [Function.update_apply, hJ]
  by_cases k5 : k = kY0
  · subst k5; simp [Function.update_apply, hY0]
  by_cases k6 : k = kY1
  · subst k6; simp [Function.update_apply, hY1]
  by_cases k7 : k = kY2
  · subst k7; simp [Function.update_apply, hY2]
  simp [Function.update_apply, k1, k2, k3, k4, k5, k6, k7]

/-! ## Replicating a staged record -/

/-- Cost of `emitOne` for `U` copies of a record of `len` bits. -/
def emitCost (U len : ℕ) : ℕ := U * (7 * len + 6 * bitLen U + 20) + 7 * bitLen U + 2 * len + 11

/-- Replicate the staged record on `Yk` onto `Ak`, `U` times (`U` copied from `kCU` to the
counter `kCC`), then erase the staged record. -/
def emitOne (Yk Ak : SK) : BProg SK :=
  .seq (L (copyBlock kCU kCC kTP)) (.seq (emitLoop Yk Ak) (L (SolveAux.eraseRec Yk)))

theorem runs_emitOne (Yk Ak : SK)
    (hYA : (Yk = kY0 ∧ Ak = kA0) ∨ (Yk = kY1 ∧ Ak = kA1) ∨ (Yk = kY2 ∧ Ak = kA2))
    (bs : List Bool) (U : ℕ) (S : SK → List Sym)
    (hY : S Yk = recSyms bs) (hCU : S kCU = natSyms U) (hCC : S kCC = []) :
    Runs (emitOne Yk Ak) S
      (Function.update (Function.update S Yk []) Ak
        (SolveAux.recsOf (List.replicate U bs) ++ S Ak))
      (fun _ => True) (emitCost U bs.length) := by
  have a1 : Yk ≠ Ak := by rcases hYA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have a4 : Yk ≠ kCC := by rcases hYA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have a5 : Ak ≠ kCC := by rcases hYA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  refine runs_mono (runs_congr (runs_seq
    (runs_L_copyBlock (src := kCU) (dst := kCC) (tmp := kTP) (by decide) (by decide) (by decide)
      (encodeNat U) [] S termOK_nil (by rw [hCU, natSyms_eq_map, List.append_nil]))
    (runs_seq (runs_emitLoop Yk Ak hYA bs [] U _
        (by simp [Function.update_apply, a4, hY])
        (by simp [Function.update_apply, hCC, natSyms_eq_map]))
      (runs_L (K := SK) fun v => ⟨_, SolveAux.eraseRec_eval Yk v bs [] _
        (by simp [Function.update_apply, a1, a4, hY])⟩))) ?_)
    (fun _ _ => trivial) (by simp only [emitCost, bitLen]; omega)
  funext k
  by_cases k1 : k = Yk
  · subst k1; simp [Function.update_apply, a1, a4]
  by_cases k2 : k = Ak
  · subst k2; simp [Function.update_apply, a1.symm, a5, k1]
  by_cases k3 : k = kCC
  · subst k3; simp [Function.update_apply, a4.symm, a5.symm, hCC]
  simp [Function.update_apply, k1, k2, k3]

/-! ## One digit -/

theorem length_crecBits_one (w : ℕ) (g : ℤ) : (crecBits w [(g, 0)]).length = 2 * w := by
  simp [crecBits_one, K1.length_twosBits]; ring

/-- One digit of the half: split the record, replicate the three staged records `U` times onto
`kA0, kA1, kA2`, decrement the digit counter `kCD`. -/
def digitBody : BProg SK :=
  .seq digitSplit (.seq (emitOne kY0 kA0) (.seq (emitOne kY1 kA1) (.seq (emitOne kY2 kA2)
    (L (dec kCD kTQ)))))

/-- Cost bound of `digitBody`. -/
def digitCost (w U n : ℕ) : ℕ :=
  200 * w + 200 + 3 * emitCost U (2 * (w + 1)) + (6 * bitLen (n + 1) + 8)

theorem runs_digitBody (w : ℕ) (hw : 1 ≤ w) (μ x γ : ℤ) (hμ : FitsTwos w μ) (hx : FitsTwos w x)
    (hγ : FitsTwos w γ) (U n : ℕ) (tabRest : List Sym) (S : SK → List Sym)
    (hTab : S sTab = recSyms (recBits w μ x γ) ++ tabRest)
    (hRU : S kRU = ruler w) (hRX : S kRX = ruler (w + 1)) (hRV : S kRV = []) (hTP : S kTP = [])
    (hYT : S kYT = []) (hYT2 : S kYT2 = []) (hW : S kW = []) (hJ : S kJ = [])
    (hY0 : S kY0 = []) (hY1 : S kY1 = []) (hY2 : S kY2 = [])
    (hCU : S kCU = natSyms U) (hCC : S kCC = []) (hCD : S kCD = natSyms (n + 1)) :
    Runs digitBody S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update S sTab tabRest) kZR (recSyms (recBits w μ x γ) ++ S kZR))
        kA0 (SolveAux.recsOf (List.replicate U (crecBits (w + 1) [(μ, 0)])) ++ S kA0))
        kA1 (SolveAux.recsOf (List.replicate U (crecBits (w + 1) [(-x, 0)])) ++ S kA1))
        kA2 (SolveAux.recsOf (List.replicate U (crecBits (w + 1) [(γ, 0)])) ++ S kA2))
        kCD (natSyms n))
      (fun _ => True) (digitCost w U n) := by
  refine runs_mono (runs_congr (runs_seq
    (runs_digitSplit w hw μ x γ hμ hx hγ tabRest S hTab hRU hRX hRV hTP hYT hYT2 hW hJ hY0 hY1 hY2)
    (runs_seq (runs_emitOne kY0 kA0 (Or.inl ⟨rfl, rfl⟩) (crecBits (w + 1) [(μ, 0)]) U _
        (by simp [Function.update_apply]) (by simp [Function.update_apply, hCU])
        (by simp [Function.update_apply, hCC]))
    (runs_seq (runs_emitOne kY1 kA1 (Or.inr (Or.inl ⟨rfl, rfl⟩)) (crecBits (w + 1) [(-x, 0)]) U _
        (by simp [Function.update_apply]) (by simp [Function.update_apply, hCU])
        (by simp [Function.update_apply, hCC]))
    (runs_seq (runs_emitOne kY2 kA2 (Or.inr (Or.inr ⟨rfl, rfl⟩)) (crecBits (w + 1) [(γ, 0)]) U _
        (by simp [Function.update_apply]) (by simp [Function.update_apply, hCU])
        (by simp [Function.update_apply, hCC]))
      (runs_L (K := SK) fun v => ⟨_, dec_eval (k := kCD) (t := kTQ) (by decide) [] v n [] _
        termOK_nil (by simp [Function.update_apply, hCD, natSyms_eq_map])⟩))))) ?_)
    (fun _ _ => trivial) ?_
  · funext k
    by_cases k1 : k = sTab
    · subst k1; simp [Function.update_apply]
    by_cases k2 : k = kZR
    · subst k2; simp [Function.update_apply]
    by_cases k3 : k = kA0
    · subst k3; simp [Function.update_apply]
    by_cases k4 : k = kA1
    · subst k4; simp [Function.update_apply]
    by_cases k5 : k = kA2
    · subst k5; simp [Function.update_apply]
    by_cases k6 : k = kCD
    · subst k6; simp [Function.update_apply, natSyms_eq_map]
    by_cases k7 : k = kY0
    · subst k7; simp [Function.update_apply, hY0]
    by_cases k8 : k = kY1
    · subst k8; simp [Function.update_apply, hY1]
    by_cases k9 : k = kY2
    · subst k9; simp [Function.update_apply, hY2]
    simp [Function.update_apply, k1, k2, k3, k4, k5, k6, k7, k8, k9]
  · have hz : zerosLead (encodeNat (n + 1)) ≤ bitLen (n + 1) := zerosLead_le_length _
    simp only [digitCost, length_crecBits_one]
    omega

end SubNLogN.Machine.Bridge.SolveParamsAux
