/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvArith
import SubNLogN.Machine.Layer.DrvArithBounds
import SubNLogN.Machine.Layer.DrvCostKit
import SubNLogN.Machine.Layer.DrvParamsDefs

/-!
# Layer driver: shared parameter kernels (`Machine/Layer/DrvParamsShared.lean`)

Generic machine programs (any stack type `K`, stacks given by an injective map `st`, register file
`DrvArith.Reg2`), shared by the post- and pre-phase parameter kernels, each with an exact `Runs`
specification (every stack other than the destination is restored; temporaries may hold arbitrary
content) and an explicit cost with a cubic bound:
* `keepN`: from `D`, `K`, `S` pushes `natSyms (2^(K·D)·S)` (`runs_keepN`, `keepCost_le`);
* `npadN`: from `d`, `D`, `K`, `S` pushes `natSyms (npadVal d D K S)`, the padding record count
  `drvNpad` (`drvNpad_eq`), with the rows test `q₀ < D` inside (`runs_npadN`, `npadCost_le`).
-/

namespace SubNLogN.Machine.Layer.DrvParamsShared

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.Layer.DrvArith
open SubNLogN.Math.Networks (padR q0Of Wc Wc_pos mH)

/-! ## `keepN` -/

section Keep

variable {K : Type}

/-- **`keepN st`**: `st 0 = D`, `st 1 = K`, `st 2 = S` (restored) ↦ `natSyms (S·2^(K·D))` pushed on
`st 3`; work stacks `st 4` (`K·D`), `st 5`; temporaries `st 6 … st 12`. -/
def keepN (st : Fin 16 → K) : Prog K (fun _ => Sym) Reg2 :=
  (Prog.seq (.seq (.seq (.seq (.seq (pushMark (st 4))
    (mulN (st 1) (st 0) (st 4) (st 6) (st 7) (st 8) (st 9)))
    (.seq (pushMark (st 5)) (.seq (copyN (st 2) (st 5) (st 6))
      (powMulN (st 5) 2 (st 4) (st 6) (st 7) (st 8) (st 9) (st 10) (st 11) (st 12)))))
    (copyN (st 5) (st 3) (st 6))) (dropF (st 5))) (dropF (st 4))).liftRegs lN

/-- The cost of `keepN`. -/
def keepCost (D Kv Sv : ℕ) : ℕ :=
  (1 + mulCost Kv D) + (1 + ((7 * bitLen Sv + 7) + powCost 2 Sv (Kv * D))) +
    (7 * bitLen (Sv * 2 ^ (Kv * D)) + 7) + (2 * bitLen (Sv * 2 ^ (Kv * D)) + 2) +
    (2 * bitLen (Kv * D) + 2)

variable [DecidableEq K]

/-- **`keepN`**: pushes `natSyms (2^(K·D)·S)` on `st 3`; every other stack restored. -/
theorem runs_keepN {st : Fin 16 → K} (hst : Function.Injective st) (D Kv Sv : ℕ)
    (rD rK rS : List Sym) (S : K → List Sym) (hrD : TermOK rD) (hrK : TermOK rK)
    (hrS : TermOK rS) (h0 : S (st 0) = natSyms D ++ rD) (h1 : S (st 1) = natSyms Kv ++ rK)
    (h2 : S (st 2) = natSyms Sv ++ rS) :
    Runs (keepN st) S (Function.update S (st 3) (natSyms (2 ^ (Kv * D) * Sv) ++ S (st 3)))
      (fun _ => True) (keepCost D Kv Sv) := by
  have hnd : ∀ l : List (Fin 16), l.Nodup → (l.map st).Nodup := fun l hl => hl.map hst
  obtain ⟨S1, hS1⟩ : ∃ T, T = fl S (st 4) (Kv * D) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ T, T = fl S1 (st 5) (Sv * 2 ^ (Kv * D)) := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ T, T = Function.update S2 (st 3)
      (natSyms (Sv * 2 ^ (Kv * D)) ++ S (st 3)) := ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ T, T = Function.update S3 (st 5) (S (st 5)) := ⟨_, rfl⟩
  obtain ⟨S5, hS5⟩ : ∃ T, T = Function.update S4 (st 4) (S (st 4)) := ⟨_, rfl⟩
  have r1 : Runs (.seq (pushMark (st 4)) (mulN (st 1) (st 0) (st 4) (st 6) (st 7) (st 8) (st 9)))
      S S1 (fun _ => True) (1 + mulCost Kv D) := by
    rw [hS1]
    apply runs_fl
    have c := runs_mulN (x := st 1) (y := st 0) (z := st 4) (A := st 6) (Bs := st 7)
      (Acc := st 8) (T := st 9) (hnd [1, 0, 4, 6, 7, 8, 9] (by decide)) Kv D rK rD
      (Function.update S (st 4) (Sym.mark :: S (st 4))) hrK hrD
      (by rw [Function.update_of_ne (hst.ne (by decide)), h1])
      (by rw [Function.update_of_ne (hst.ne (by decide)), h0])
    rw [Function.update_self] at c
    exact c
  have r2 : Runs (.seq (pushMark (st 5)) (.seq (copyN (st 2) (st 5) (st 6))
      (powMulN (st 5) 2 (st 4) (st 6) (st 7) (st 8) (st 9) (st 10) (st 11) (st 12)))) S1 S2
      (fun _ => True) (1 + ((7 * bitLen Sv + 7) + powCost 2 Sv (Kv * D))) := by
    rw [hS2]
    apply runs_fl
    have c1 := runs_copyN (src := st 2) (dst := st 5) (tmp := st 6) (hst.ne (by decide))
      (hst.ne (by decide)) (hst.ne (by decide)) Sv rS
      (Function.update S1 (st 5) (Sym.mark :: S1 (st 5))) hrS
      (by simp +decide only [hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
          exact h2)
    have c2 := runs_powMulN (k := st 5) (ns := st 4) (Kc := st 6) (t := st 7) (Q := st 8)
      (Tdst := st 9) (A := st 10) (Bs := st 11) (Acc := st 12)
      (hnd [5, 4, 6, 7, 8, 9, 10, 11, 12] (by decide)) 2 (by norm_num) Sv (Kv * D)
      (Sym.mark :: S1 (st 5)) (Sym.mark :: S (st 4))
      (Function.update (Function.update S1 (st 5) (Sym.mark :: S1 (st 5))) (st 5)
        (natSyms Sv ++ Function.update S1 (st 5) (Sym.mark :: S1 (st 5)) (st 5)))
      (termOK_mark _) (termOK_mark _)
      (by rw [Function.update_self, Function.update_self])
      (by simp +decide only [hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false])
    refine WP.W9comp.runs_congr (WP.W9comp.runs_seq c1 c2) ?_
    rw [Function.update_idem]
  have r3 : Runs (copyN (st 5) (st 3) (st 6)) S2 S3 (fun _ => True)
      (7 * bitLen (Sv * 2 ^ (Kv * D)) + 7) := by
    have c := runs_copyN (src := st 5) (dst := st 3) (tmp := st 6) (hst.ne (by decide))
      (hst.ne (by decide)) (hst.ne (by decide)) (Sv * 2 ^ (Kv * D)) (Sym.mark :: S1 (st 5)) S2
      (termOK_mark _)
      (by simp +decide only [hS2, fl, Function.update_apply, hst.eq_iff, if_true, if_false])
    have e : S2 (st 3) = S (st 3) := by
      simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
    rw [e] at c
    rw [hS3]
    exact c
  have r4 : Runs (dropF (st 5)) S3 S4 (fun _ => True) (2 * bitLen (Sv * 2 ^ (Kv * D)) + 2) := by
    have c := runs_dropF (st 5) (Sv * 2 ^ (Kv * D)) Sym.mark (S (st 5)) S3 rfl
      (by simp +decide only [hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
        if_false])
    rw [hS4]
    exact c
  have r5 : Runs (dropF (st 4)) S4 S5 (fun _ => True) (2 * bitLen (Kv * D) + 2) := by
    have c := runs_dropF (st 4) (Kv * D) Sym.mark (S (st 4)) S4 rfl
      (by simp +decide only [hS4, hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
        if_false])
    rw [hS5]
    exact c
  have hall := runs_liftRegs' lN (WP.W9comp.runs_seq (WP.W9comp.runs_seq (WP.W9comp.runs_seq
    (WP.W9comp.runs_seq r1 r2) r3) r4) r5)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) (le_of_eq rfl)
  funext k
  rcases eq_or_ne k (st 3) with rfl | h3
  · simp +decide only [hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
      if_false]
    rw [Nat.mul_comm Sv]
  rcases eq_or_ne k (st 4) with rfl | h4
  · simp +decide only [hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
      if_false]
  rcases eq_or_ne k (st 5) with rfl | h5
  · simp +decide only [hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
      if_false]
  simp only [hS5, hS4, hS3, hS2, hS1, fl, Function.update_apply, h3, h4, h5, if_false]

end Keep

/-! ## `npadN` -/

section Npad

variable {K : Type}

/-- The padding record count: `(padR − 2^{q₀K})·2^{K(D−q₀)}·S` if `q₀ < D`, else `0`. -/
noncomputable def npadVal (d D K S : ℕ) : ℕ :=
  if q0Of d < D then (padR d K - 2 ^ (q0Of d * K)) * (2 ^ (K * (D - q0Of d)) * S) else 0

theorem npadR_ge (d K : ℕ) : 2 ^ (q0Of d * K) ≤ padR d K := by
  unfold padR
  have hW : 0 < Wc ^ SubNLogN.Math.Networks.k0Of d := pow_pos Wc_pos _
  have h1 := Nat.div_add_mod (2 ^ (q0Of d * K) + Wc ^ SubNLogN.Math.Networks.k0Of d - 1)
    (Wc ^ SubNLogN.Math.Networks.k0Of d)
  have h2 := Nat.mod_lt (2 ^ (q0Of d * K) + Wc ^ SubNLogN.Math.Networks.k0Of d - 1) hW
  omega

theorem drvNpad_eq (t : LayerRT) : drvNpad t = npadVal t.d t.D t.K t.S := by
  unfold drvNpad npadVal DrvRows SubNLogN.Math.Networks.useRows
  by_cases h : q0Of t.d < t.D
  · rw [if_pos ⟨h, lt_of_lt_of_le (Nat.two_pow_pos _) (npadR_ge _ _)⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

theorem npOrdOf_lt (a b : ℕ) : ordOf a b = Ordering.lt ↔ a < b := by
  unfold ordOf
  split_ifs with h1 h2 <;> simp_all

/-- The stack map of `padRN` inside `npadN`. -/
def npPadMap : Fin 32 → Fin 40 := fun i =>
  if i.val = 0 then 0 else if i.val = 1 then 2 else if i.val = 2 then 6 else if i.val = 3 then 7
  else ⟨i.val + 8, by omega⟩

/-- The stack map of `q0N` inside `npadN`. -/
def npQ0Map : Fin 16 → Fin 40 := fun i =>
  if i.val = 0 then 0 else if i.val = 1 then 5 else ⟨i.val + 10, by omega⟩

/-- The arithmetic part of the rows branch (work stacks `st 8 … st 11`, temporaries from
`st 12`). -/
def npadRowsB (st : Fin 40 → K) : Prog K (fun _ => Sym) Reg :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq
    (.seq (pushMark (st 8)) (subN (st 6) (st 7) (st 8) (st 12) (st 13) (st 14)))
    (.seq (pushMark (st 9)) (subN (st 1) (st 5) (st 9) (st 12) (st 13) (st 14))))
    (.seq (pushMark (st 10)) (mulN (st 2) (st 9) (st 10) (st 12) (st 13) (st 14) (st 15))))
    (.seq (pushMark (st 11)) (.seq (copyN (st 3) (st 11) (st 12))
      (powMulN (st 11) 2 (st 10) (st 12) (st 13) (st 14) (st 15) (st 16) (st 17) (st 18)))))
    (mulN (st 8) (st 11) (st 4) (st 12) (st 13) (st 14) (st 15)))
    (dropF (st 11))) (dropF (st 10))) (dropF (st 9))) (dropF (st 8))) (dropF (st 7)))
    (dropF (st 6))

/-- The rows branch of `npadN` (`q₀ < D`). -/
noncomputable def npadRows (st : Fin 40 → K) : Prog K (fun _ => Sym) Reg2 :=
  .seq (.seq ((Prog.seq (pushMark (st 6)) (pushMark (st 7))).liftRegs lN) (padRN (st ∘ npPadMap)))
    ((npadRowsB st).liftRegs lN)

/-- **`npadN st`**: `st 0 = d`, `st 1 = D`, `st 2 = K`, `st 3 = S` (restored) ↦
`natSyms (npadVal d D K S)` pushed on `st 4`; work stacks `st 5 … st 11`; temporaries `st 12 …`. -/
noncomputable def npadN (st : Fin 40 → K) : Prog K (fun _ => Sym) Reg2 :=
  .seq (.seq ((Prog.seq (pushMark (st 5)) (q0N (st ∘ npQ0Map))).liftRegs lN)
    (.seq ((cmpN (st 5) (st 1) (st 12) (st 13)).liftRegs lN)
      (.ite (fun r => isLtR r.1) (npadRows st) skip)))
    ((dropF (st 5)).liftRegs lN)

/-- The cost of the rows branch. -/
noncomputable def npRowsCost (d D Kv Sv : ℕ) : ℕ :=
  (1 + 1) + padRCost d Kv +
  ((1 + 20 * (bitLen (padR d Kv) + bitLen (2 ^ (q0Of d * Kv)) + 1)) +
  (1 + 20 * (bitLen D + bitLen (q0Of d) + 1)) + (1 + mulCost Kv (D - q0Of d)) +
  (1 + ((7 * bitLen Sv + 7) + powCost 2 Sv (Kv * (D - q0Of d)))) +
  mulCost (padR d Kv - 2 ^ (q0Of d * Kv)) (Sv * 2 ^ (Kv * (D - q0Of d))) +
  (2 * bitLen (Sv * 2 ^ (Kv * (D - q0Of d))) + 2) + (2 * bitLen (Kv * (D - q0Of d)) + 2) +
  (2 * bitLen (D - q0Of d) + 2) + (2 * bitLen (padR d Kv - 2 ^ (q0Of d * Kv)) + 2) +
  (2 * bitLen (2 ^ (q0Of d * Kv)) + 2) + (2 * bitLen (padR d Kv) + 2))

/-- The cost of `npadN`. -/
noncomputable def npadCost (d D Kv Sv : ℕ) : ℕ :=
  (1 + q0Cost d) + ((12 * min (bitLen (q0Of d)) (bitLen D) + 15) +
    ((if q0Of d < D then npRowsCost d D Kv Sv else 1) + 1)) + (2 * bitLen (q0Of d) + 2)

variable [DecidableEq K]

theorem runs_npadRows {st : Fin 40 → K} (hst : Function.Injective st) (d D Kv Sv : ℕ)
    (rd rD rK rS : List Sym) (S : K → List Sym) (hrd : TermOK rd) (hrD : TermOK rD)
    (hrK : TermOK rK) (hrS : TermOK rS) (h0 : S (st 0) = natSyms d ++ rd)
    (h1 : S (st 1) = natSyms D ++ rD) (h2 : S (st 2) = natSyms Kv ++ rK)
    (h3 : S (st 3) = natSyms Sv ++ rS) (h : q0Of d < D) :
    Runs (npadRows st) (fl S (st 5) (q0Of d))
      (Function.update (fl S (st 5) (q0Of d)) (st 4) (natSyms (npadVal d D Kv Sv) ++ S (st 4)))
      (fun _ => True) (npRowsCost d D Kv Sv) := by
  have hnd : ∀ l : List (Fin 40), l.Nodup → (l.map st).Nodup := fun l hl => hl.map hst
  have hXP := npadR_ge d Kv
  obtain ⟨S1, hS1⟩ : ∃ T, T = fl S (st 5) (q0Of d) := ⟨_, rfl⟩
  rw [← hS1]
  obtain ⟨S2, hS2⟩ : ∃ T, T = Function.update (Function.update S1 (st 6) (Sym.mark :: S (st 6)))
      (st 7) (Sym.mark :: S (st 7)) := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ T, T = fl (fl S1 (st 6) (padR d Kv)) (st 7) (2 ^ (q0Of d * Kv)) :=
    ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ T, T = fl S3 (st 8) (padR d Kv - 2 ^ (q0Of d * Kv)) := ⟨_, rfl⟩
  obtain ⟨S5, hS5⟩ : ∃ T, T = fl S4 (st 9) (D - q0Of d) := ⟨_, rfl⟩
  obtain ⟨S6, hS6⟩ : ∃ T, T = fl S5 (st 10) (Kv * (D - q0Of d)) := ⟨_, rfl⟩
  obtain ⟨S7, hS7⟩ : ∃ T, T = fl S6 (st 11) (Sv * 2 ^ (Kv * (D - q0Of d))) := ⟨_, rfl⟩
  obtain ⟨S8, hS8⟩ : ∃ T, T = Function.update S7 (st 4)
      (natSyms ((padR d Kv - 2 ^ (q0Of d * Kv)) * (Sv * 2 ^ (Kv * (D - q0Of d)))) ++
        S (st 4)) := ⟨_, rfl⟩
  obtain ⟨D1, hD1⟩ : ∃ T, T = Function.update S8 (st 11) (S (st 11)) := ⟨_, rfl⟩
  obtain ⟨D2, hD2⟩ : ∃ T, T = Function.update D1 (st 10) (S (st 10)) := ⟨_, rfl⟩
  obtain ⟨D3, hD3⟩ : ∃ T, T = Function.update D2 (st 9) (S (st 9)) := ⟨_, rfl⟩
  obtain ⟨D4, hD4⟩ : ∃ T, T = Function.update D3 (st 8) (S (st 8)) := ⟨_, rfl⟩
  obtain ⟨D5, hD5⟩ : ∃ T, T = Function.update D4 (st 7) (S (st 7)) := ⟨_, rfl⟩
  obtain ⟨D6, hD6⟩ : ∃ T, T = Function.update D5 (st 6) (S (st 6)) := ⟨_, rfl⟩
  -- the floors of the padding values
  have p1 : Runs ((Prog.seq (pushMark (st 6)) (pushMark (st 7))).liftRegs lN) S1 S2
      (fun _ => True) (1 + 1) := by
    have c := WP.W9comp.runs_seq (runs_pushMark (st 6) S1)
      (runs_pushMark (st 7) (Function.update S1 (st 6) (Sym.mark :: S1 (st 6))))
    refine runs_liftRegs' lN (WP.W9comp.runs_congr c ?_)
    funext k
    simp +decide only [hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
  -- `padR`, `2^{q₀K}`
  have p2 : Runs (padRN (st ∘ npPadMap)) S2 S3 (fun _ => True) (padRCost d Kv) := by
    have c := runs_padRN (hst.comp (by decide : Function.Injective npPadMap)) d Kv rd rK S2 hrd hrK
      (by simp +decide only [show (st ∘ npPadMap) 0 = st 0 from rfl, hS2, hS1, fl,
            Function.update_apply, hst.eq_iff, if_true, if_false]
          exact h0)
      (by simp +decide only [show (st ∘ npPadMap) 1 = st 2 from rfl, hS2, hS1, fl,
            Function.update_apply, hst.eq_iff, if_true, if_false]
          exact h2)
    refine WP.W9comp.runs_congr c ?_
    rw [show (st ∘ npPadMap) 2 = st 6 from rfl, show (st ∘ npPadMap) 3 = st 7 from rfl]
    funext k
    rcases eq_or_ne k (st 6) with rfl | h6
    · simp +decide only [hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
    rcases eq_or_ne k (st 7) with rfl | h7
    · simp +decide only [hS3, hS2, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
    simp only [hS3, hS2, hS1, fl, Function.update_apply, h6, h7, if_false]
  -- `padR − 2^{q₀K}`
  have q1 : Runs (.seq (pushMark (st 8)) (subN (st 6) (st 7) (st 8) (st 12) (st 13) (st 14))) S3 S4
      (fun _ => True) (1 + 20 * (bitLen (padR d Kv) + bitLen (2 ^ (q0Of d * Kv)) + 1)) := by
    rw [hS4]
    apply runs_fl
    have c := runs_subN (x := st 6) (y := st 7) (z := st 8) (t1 := st 12) (t2 := st 13)
      (t3 := st 14) (hnd [6, 7, 8, 12, 13, 14] (by decide)) (padR d Kv) (2 ^ (q0Of d * Kv))
      (Sym.mark :: S (st 6)) (Sym.mark :: S (st 7))
      (Function.update S3 (st 8) (Sym.mark :: S3 (st 8))) (termOK_mark _) (termOK_mark _) hXP
      (by simp +decide only [hS3, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false])
      (by simp +decide only [hS3, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false])
    rw [Function.update_self] at c
    exact c
  -- `D − q₀`
  have q2 : Runs (.seq (pushMark (st 9)) (subN (st 1) (st 5) (st 9) (st 12) (st 13) (st 14))) S4 S5
      (fun _ => True) (1 + 20 * (bitLen D + bitLen (q0Of d) + 1)) := by
    rw [hS5]
    apply runs_fl
    have c := runs_subN (x := st 1) (y := st 5) (z := st 9) (t1 := st 12) (t2 := st 13)
      (t3 := st 14) (hnd [1, 5, 9, 12, 13, 14] (by decide)) D (q0Of d) rD (Sym.mark :: S (st 5))
      (Function.update S4 (st 9) (Sym.mark :: S4 (st 9))) hrD (termOK_mark _) (le_of_lt h)
      (by simp +decide only [hS4, hS3, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
            if_false]
          exact h1)
      (by simp +decide only [hS4, hS3, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
        if_false])
    rw [Function.update_self] at c
    exact c
  -- `K·(D − q₀)`
  have q3 : Runs (.seq (pushMark (st 10))
      (mulN (st 2) (st 9) (st 10) (st 12) (st 13) (st 14) (st 15))) S5 S6
      (fun _ => True) (1 + mulCost Kv (D - q0Of d)) := by
    rw [hS6]
    apply runs_fl
    have c := runs_mulN (x := st 2) (y := st 9) (z := st 10) (A := st 12) (Bs := st 13)
      (Acc := st 14) (T := st 15) (hnd [2, 9, 10, 12, 13, 14, 15] (by decide)) Kv (D - q0Of d)
      rK (Sym.mark :: S (st 9)) (Function.update S5 (st 10) (Sym.mark :: S5 (st 10))) hrK
      (termOK_mark _)
      (by simp +decide only [hS5, hS4, hS3, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
            if_false]
          exact h2)
      (by simp +decide only [hS5, hS4, hS3, hS1, fl, Function.update_apply, hst.eq_iff, if_true,
        if_false])
    rw [Function.update_self] at c
    exact c
  -- `S·2^{K(D−q₀)}`
  have q4 : Runs (.seq (pushMark (st 11)) (.seq (copyN (st 3) (st 11) (st 12))
      (powMulN (st 11) 2 (st 10) (st 12) (st 13) (st 14) (st 15) (st 16) (st 17) (st 18)))) S6 S7
      (fun _ => True) (1 + ((7 * bitLen Sv + 7) + powCost 2 Sv (Kv * (D - q0Of d)))) := by
    rw [hS7]
    apply runs_fl
    have c1 := runs_copyN (src := st 3) (dst := st 11) (tmp := st 12) (hst.ne (by decide))
      (hst.ne (by decide)) (hst.ne (by decide)) Sv rS
      (Function.update S6 (st 11) (Sym.mark :: S6 (st 11))) hrS
      (by simp +decide only [hS6, hS5, hS4, hS3, hS1, fl, Function.update_apply, hst.eq_iff,
            if_true, if_false]
          exact h3)
    have c2 := runs_powMulN (k := st 11) (ns := st 10) (Kc := st 12) (t := st 13) (Q := st 14)
      (Tdst := st 15) (A := st 16) (Bs := st 17) (Acc := st 18)
      (hnd [11, 10, 12, 13, 14, 15, 16, 17, 18] (by decide)) 2 (by norm_num) Sv
      (Kv * (D - q0Of d)) (Sym.mark :: S6 (st 11)) (Sym.mark :: S (st 10))
      (Function.update (Function.update S6 (st 11) (Sym.mark :: S6 (st 11))) (st 11)
        (natSyms Sv ++ Function.update S6 (st 11) (Sym.mark :: S6 (st 11)) (st 11)))
      (termOK_mark _) (termOK_mark _)
      (by rw [Function.update_self, Function.update_self])
      (by simp +decide only [hS6, hS5, hS4, hS3, hS1, fl, Function.update_apply, hst.eq_iff,
        if_true, if_false])
    refine WP.W9comp.runs_congr (WP.W9comp.runs_seq c1 c2) ?_
    rw [Function.update_idem]
  -- the product onto `st 4`
  have q5 : Runs (mulN (st 8) (st 11) (st 4) (st 12) (st 13) (st 14) (st 15)) S7 S8
      (fun _ => True) (mulCost (padR d Kv - 2 ^ (q0Of d * Kv)) (Sv * 2 ^ (Kv * (D - q0Of d)))) := by
    have c := runs_mulN (x := st 8) (y := st 11) (z := st 4) (A := st 12) (Bs := st 13)
      (Acc := st 14) (T := st 15) (hnd [8, 11, 4, 12, 13, 14, 15] (by decide))
      (padR d Kv - 2 ^ (q0Of d * Kv)) (Sv * 2 ^ (Kv * (D - q0Of d))) (Sym.mark :: S (st 8))
      (Sym.mark :: S (st 11)) S7 (termOK_mark _) (termOK_mark _)
      (by simp +decide only [hS7, hS6, hS5, hS4, hS3, hS1, fl, Function.update_apply, hst.eq_iff,
        if_true, if_false])
      (by simp +decide only [hS7, hS6, hS5, hS4, hS3, hS1, fl, Function.update_apply, hst.eq_iff,
        if_true, if_false])
    have e : S7 (st 4) = S (st 4) := by
      simp +decide only [hS7, hS6, hS5, hS4, hS3, hS1, fl, Function.update_apply, hst.eq_iff,
        if_true, if_false]
    rw [e, ← hS8] at c
    exact c
  -- drops
  have q6 : Runs (dropF (st 11)) S8 D1 (fun _ => True)
      (2 * bitLen (Sv * 2 ^ (Kv * (D - q0Of d))) + 2) := by
    have c := runs_dropF (st 11) (Sv * 2 ^ (Kv * (D - q0Of d))) Sym.mark (S (st 11)) S8 rfl
      (by simp +decide only [hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl, Function.update_apply,
        hst.eq_iff, if_true, if_false])
    rw [← hD1] at c
    exact c
  have q7 : Runs (dropF (st 10)) D1 D2 (fun _ => True) (2 * bitLen (Kv * (D - q0Of d)) + 2) := by
    have c := runs_dropF (st 10) (Kv * (D - q0Of d)) Sym.mark (S (st 10)) D1 rfl
      (by simp +decide only [hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl, Function.update_apply,
        hst.eq_iff, if_true, if_false])
    rw [← hD2] at c
    exact c
  have q8 : Runs (dropF (st 9)) D2 D3 (fun _ => True) (2 * bitLen (D - q0Of d) + 2) := by
    have c := runs_dropF (st 9) (D - q0Of d) Sym.mark (S (st 9)) D2 rfl
      (by simp +decide only [hD2, hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false])
    rw [← hD3] at c
    exact c
  have q9 : Runs (dropF (st 8)) D3 D4 (fun _ => True)
      (2 * bitLen (padR d Kv - 2 ^ (q0Of d * Kv)) + 2) := by
    have c := runs_dropF (st 8) (padR d Kv - 2 ^ (q0Of d * Kv)) Sym.mark (S (st 8)) D3 rfl
      (by simp +decide only [hD3, hD2, hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false])
    rw [← hD4] at c
    exact c
  have q10 : Runs (dropF (st 7)) D4 D5 (fun _ => True) (2 * bitLen (2 ^ (q0Of d * Kv)) + 2) := by
    have c := runs_dropF (st 7) (2 ^ (q0Of d * Kv)) Sym.mark (S (st 7)) D4 rfl
      (by simp +decide only [hD4, hD3, hD2, hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false])
    rw [← hD5] at c
    exact c
  have q11 : Runs (dropF (st 6)) D5 D6 (fun _ => True) (2 * bitLen (padR d Kv) + 2) := by
    have c := runs_dropF (st 6) (padR d Kv) Sym.mark (S (st 6)) D5 rfl
      (by simp +decide only [hD5, hD4, hD3, hD2, hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl,
        Function.update_apply, hst.eq_iff, if_true, if_false])
    rw [← hD6] at c
    exact c
  have hB := WP.W9comp.runs_seq (WP.W9comp.runs_seq (WP.W9comp.runs_seq (WP.W9comp.runs_seq
    (WP.W9comp.runs_seq (WP.W9comp.runs_seq (WP.W9comp.runs_seq (WP.W9comp.runs_seq
    (WP.W9comp.runs_seq (WP.W9comp.runs_seq q1 q2) q3) q4) q5) q6) q7) q8) q9) q10) q11
  have hall := WP.W9comp.runs_seq (WP.W9comp.runs_seq p1 p2) (runs_liftRegs' lN hB)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial)
    (by unfold npRowsCost; omega)
  have hv : npadVal d D Kv Sv =
      (padR d Kv - 2 ^ (q0Of d * Kv)) * (Sv * 2 ^ (Kv * (D - q0Of d))) := by
    rw [npadVal, if_pos h, Nat.mul_comm (2 ^ (Kv * (D - q0Of d))) Sv]
  rw [hv]
  funext k
  rcases eq_or_ne k (st 4) with rfl | h4
  · simp +decide only [hD6, hD5, hD4, hD3, hD2, hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false]
  rcases eq_or_ne k (st 6) with rfl | h6
  · simp +decide only [hD6, hD5, hD4, hD3, hD2, hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false]
  rcases eq_or_ne k (st 7) with rfl | h7
  · simp +decide only [hD6, hD5, hD4, hD3, hD2, hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false]
  rcases eq_or_ne k (st 8) with rfl | h8
  · simp +decide only [hD6, hD5, hD4, hD3, hD2, hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false]
  rcases eq_or_ne k (st 9) with rfl | h9
  · simp +decide only [hD6, hD5, hD4, hD3, hD2, hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false]
  rcases eq_or_ne k (st 10) with rfl | h10
  · simp +decide only [hD6, hD5, hD4, hD3, hD2, hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false]
  rcases eq_or_ne k (st 11) with rfl | h11
  · simp +decide only [hD6, hD5, hD4, hD3, hD2, hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl,
      Function.update_apply, hst.eq_iff, if_true, if_false]
  simp only [hD6, hD5, hD4, hD3, hD2, hD1, hS8, hS7, hS6, hS5, hS4, hS3, hS1, fl,
    Function.update_apply, h4, h6, h7, h8, h9, h10, h11, if_false]

/-- **`npadN`**: pushes `natSyms (npadVal d D K S)` on `st 4`; every other stack restored. -/
theorem runs_npadN {st : Fin 40 → K} (hst : Function.Injective st) (d D Kv Sv : ℕ)
    (rd rD rK rS : List Sym) (S : K → List Sym) (hrd : TermOK rd) (hrD : TermOK rD)
    (hrK : TermOK rK) (hrS : TermOK rS) (h0 : S (st 0) = natSyms d ++ rd)
    (h1 : S (st 1) = natSyms D ++ rD) (h2 : S (st 2) = natSyms Kv ++ rK)
    (h3 : S (st 3) = natSyms Sv ++ rS) :
    Runs (npadN st) S (Function.update S (st 4) (natSyms (npadVal d D Kv Sv) ++ S (st 4)))
      (fun _ => True) (npadCost d D Kv Sv) := by
  have hnd : ∀ l : List (Fin 40), l.Nodup → (l.map st).Nodup := fun l hl => hl.map hst
  obtain ⟨S1, hS1⟩ : ∃ T, T = fl S (st 5) (q0Of d) := ⟨_, rfl⟩
  obtain ⟨T1, hT1⟩ : ∃ T, T = Function.update S1 (st 4)
      (natSyms (npadVal d D Kv Sv) ++ S (st 4)) := ⟨_, rfl⟩
  have r1 : Runs (.seq (pushMark (st 5)) (q0N (st ∘ npQ0Map))) S S1 (fun _ => True)
      (1 + q0Cost d) := by
    rw [hS1]
    apply runs_fl
    have c := runs_q0N (hst.comp (by decide : Function.Injective npQ0Map)) d rd
      (Function.update S (st 5) (Sym.mark :: S (st 5))) hrd
      (by rw [show (st ∘ npQ0Map) 0 = st 0 from rfl, Function.update_of_ne (hst.ne (by decide)),
        h0])
    rw [show (st ∘ npQ0Map) 1 = st 5 from rfl, Function.update_self] at c
    exact c
  have rc : Runs ((cmpN (st 5) (st 1) (st 12) (st 13)).liftRegs lN) S1 S1
      (fun r => (lN.get r).2.2.2.2 = ordOf (q0Of d) D)
      (12 * min (bitLen (q0Of d)) (bitLen D) + 15) :=
    runs_liftRegs' lN (runs_cmpN (hnd [5, 1, 12, 13] (by decide)) (q0Of d) D
      (Sym.mark :: S (st 5)) rD S1 (termOK_mark _) hrD (by rw [hS1, fl_self])
      (by rw [hS1, fl_ne (hst.ne (by decide)), h1]))
  have rB : Runs (.seq ((cmpN (st 5) (st 1) (st 12) (st 13)).liftRegs lN)
      (.ite (fun r => isLtR r.1) (npadRows st) skip)) S1 T1 (fun _ => True)
      ((12 * min (bitLen (q0Of d)) (bitLen D) + 15) +
        ((if q0Of d < D then npRowsCost d D Kv Sv else 1) + 1)) := by
    by_cases h : q0Of d < D
    · rw [if_pos h]
      refine runs_seq_ite_true rc (fun v hv => ?_) ?_
      · show decide _ = true
        rw [show v.1.2.2.2.2 = ordOf (q0Of d) D from hv, (npOrdOf_lt _ _).2 h]
        rfl
      · rw [hT1, hS1]
        exact runs_npadRows hst d D Kv Sv rd rD rK rS S hrd hrD hrK hrS h0 h1 h2 h3 h
    · rw [if_neg h]
      refine runs_seq_ite_false rc (fun v hv => ?_) ?_
      · show decide _ = false
        rw [show v.1.2.2.2.2 = ordOf (q0Of d) D from hv]
        exact decide_eq_false (fun h' => h ((npOrdOf_lt _ _).1 h'))
      · have e0 : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]
        have e4 : S1 (st 4) = S (st 4) := by rw [hS1, fl_ne (hst.ne (by decide))]
        have hT : T1 = S1 := by
          rw [hT1, npadVal, if_neg h, e0, List.nil_append, ← e4, Function.update_eq_self]
        rw [hT]
        exact Runs.of_eval fun v => ⟨v, 1, skip_eval [] _, trivial, le_rfl⟩
  have rd5 : Runs ((dropF (st 5)).liftRegs lN) T1
      (Function.update S (st 4) (natSyms (npadVal d D Kv Sv) ++ S (st 4))) (fun _ => True)
      (2 * bitLen (q0Of d) + 2) := by
    have c := runs_dropF (st 5) (q0Of d) Sym.mark (S (st 5)) T1 rfl
      (by rw [hT1, Function.update_of_ne (hst.ne (by decide)), hS1, fl_self])
    refine runs_liftRegs' lN (WP.W9comp.runs_congr c ?_)
    funext k
    rcases eq_or_ne k (st 4) with rfl | h4
    · simp +decide only [hT1, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
    rcases eq_or_ne k (st 5) with rfl | h5
    · simp +decide only [hT1, hS1, fl, Function.update_apply, hst.eq_iff, if_true, if_false]
    simp only [hT1, hS1, fl, Function.update_apply, h4, h5, if_false]
  exact WP.W9comp.runs_seq (WP.W9comp.runs_seq (runs_liftRegs' lN r1) rB) rd5

end Npad

/-! ## Cost bounds -/

section Bounds

open SubNLogN.Math.Networks (k0Of)

theorem bitLen_le_self' (n : ℕ) : bitLen n ≤ n := bitLen_le_of_lt' Nat.lt_two_pow_self

theorem cube_facts {B : ℕ} (hB : 1 ≤ B) :
    B ≤ B ^ 3 ∧ B ^ 2 ≤ B ^ 3 ∧ (B + 1) ^ 2 ≤ 4 * B ^ 3 ∧ (2 * B + 1) ^ 3 ≤ 27 * B ^ 3 := by
  have h3 : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right hB (by norm_num)
  have h1 : B ≤ B ^ 3 := by
    calc B = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ 3 := Nat.pow_le_pow_right hB (by norm_num)
  refine ⟨h1, h3, ?_, ?_⟩
  · calc (B + 1) ^ 2 ≤ (2 * B) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * B ^ 2 := by ring
      _ ≤ 4 * B ^ 3 := Nat.mul_le_mul_left _ h3
  · calc (2 * B + 1) ^ 3 ≤ (3 * B) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 27 * B ^ 3 := by ring

theorem keepCost_le : ∃ c, ∀ D Kv Sv, keepCost D Kv Sv ≤
    c * (bitLen Sv + bitLen Kv + bitLen D + D * Kv + 1) ^ 3 := by
  refine ⟨100000, fun D Kv Sv => ?_⟩
  obtain ⟨B, hB⟩ : ∃ B, B = bitLen Sv + bitLen Kv + bitLen D + D * Kv + 1 := ⟨_, rfl⟩
  rw [← hB]
  have hB1 : 1 ≤ B := by omega
  have hKD : Kv * D ≤ B := by rw [Nat.mul_comm]; omega
  have hbS : bitLen (Sv * 2 ^ (Kv * D)) ≤ 2 * B := by
    have := bitLen_mul_two_pow_le Sv (Kv * D)
    omega
  have hbKD : bitLen (Kv * D) ≤ B := le_trans (bitLen_le_self' _) hKD
  have h2 : bitLen 2 ≤ 2 * B := le_trans BoundsAux.bl_two_le (by omega)
  have hm := DrvParamsAux.mulCost_le (a := Kv) (b := D) (X := B) (by omega) (by omega)
  have hp := DrvParamsAux.powCost_le (c := 2) (a := Sv) (n := Kv * D) (X := 2 * B) (by omega)
    hbS h2
  obtain ⟨e1, e2, e3, e4⟩ := cube_facts hB1
  unfold keepCost
  nlinarith

/-- `M·⌈X/M⌉ ≤ X + M` (generic form). -/
theorem mul_ceil_le (M X : ℕ) : M * ((X + M - 1) / M) ≤ X + M :=
  le_trans (Nat.mul_div_le _ _) (by omega)

/-- `padR ≤ 2^{q₀K} + W_c^{k₀}`. -/
theorem padR_le_sum (d K : ℕ) : padR d K ≤ 2 ^ (q0Of d * K) + Wc ^ k0Of d :=
  mul_ceil_le _ _

theorem bl_pow_gen (a W : ℕ) (h : bitLen a = W) (n : ℕ) : bitLen (a ^ n) ≤ n * W + 1 :=
  h ▸ BoundsAux.bl_pow_le a n

theorem k0Of_le_bitLen (d : ℕ) : k0Of d ≤ bitLen d := by
  unfold k0Of
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  exact le_trans (le_of_lt (lt_two_pow_bitLen d)) (Nat.pow_le_pow_left (by norm_num) _)

theorem bitLen_padR_le (d K W : ℕ) (hW : bitLen Wc = W) :
    bitLen (padR d K) ≤ q0Of d * K + bitLen d * W + 3 := by
  have h0 := le_trans (bitLen_mono'' (padR_le_sum d K)) (bitLen_add_le' _ _)
  have h1 := BoundsAux.bl_two_pow_le (q0Of d * K)
  have h2 := bl_pow_gen Wc W hW (k0Of d)
  have h3 := Nat.mul_le_mul_right W (k0Of_le_bitLen d)
  omega

/-- `npRowsCost` with the parameters `padRCost`, `padR`, `2^{q₀K}`, `q₀` as variables. -/
def npRowsGen (PC PR X q D Kv Sv : ℕ) : ℕ :=
  (1 + 1) + PC +
  ((1 + 20 * (bitLen PR + bitLen X + 1)) +
  (1 + 20 * (bitLen D + bitLen q + 1)) + (1 + mulCost Kv (D - q)) +
  (1 + ((7 * bitLen Sv + 7) + powCost 2 Sv (Kv * (D - q)))) +
  mulCost (PR - X) (Sv * 2 ^ (Kv * (D - q))) +
  (2 * bitLen (Sv * 2 ^ (Kv * (D - q))) + 2) + (2 * bitLen (Kv * (D - q)) + 2) +
  (2 * bitLen (D - q) + 2) + (2 * bitLen (PR - X) + 2) +
  (2 * bitLen X + 2) + (2 * bitLen PR + 2))

theorem npRowsCost_eq (d D Kv Sv : ℕ) : npRowsCost d D Kv Sv =
    npRowsGen (padRCost d Kv) (padR d Kv) (2 ^ (q0Of d * Kv)) (q0Of d) D Kv Sv := rfl

theorem npRowsGen_le (c1 W PC PR X q d D Kv Sv : ℕ) (h : q < D)
    (hPC : PC ≤ c1 * (bitLen d + q * Kv + bitLen Kv + 1) ^ 3)
    (hPR : bitLen PR ≤ q * Kv + bitLen d * W + 3) (hXb : bitLen X ≤ q * Kv + 1) :
    npRowsGen PC PR X q D Kv Sv ≤ (27 * c1 + 100000 * (W + 10) ^ 2) *
      (bitLen d + bitLen Sv + bitLen Kv + bitLen D + D * Kv + 1) ^ 3 := by
  obtain ⟨B, hB⟩ : ∃ B, B = bitLen d + bitLen Sv + bitLen Kv + bitLen D + D * Kv + 1 := ⟨_, rfl⟩
  rw [← hB]
  have hB1 : 1 ≤ B := by omega
  have hqK : q * Kv ≤ D * Kv := Nat.mul_le_mul_right Kv (le_of_lt h)
  have hKDq : Kv * (D - q) ≤ B := by
    have : Kv * (D - q) ≤ Kv * D := Nat.mul_le_mul_left Kv (Nat.sub_le _ _)
    rw [Nat.mul_comm Kv D] at this
    omega
  have hX : bitLen X ≤ B := by omega
  have hdW : bitLen d * W ≤ B * W := Nat.mul_le_mul_right W (by omega)
  have hP : bitLen PR ≤ B * W + 3 * B := by omega
  have hPX : bitLen (PR - X) ≤ B * W + 3 * B := le_trans (bitLen_mono'' (Nat.sub_le _ _)) hP
  have hSK : bitLen (Sv * 2 ^ (Kv * (D - q))) ≤ 2 * B := by
    have := bitLen_mul_two_pow_le Sv (Kv * (D - q))
    omega
  have hDq : bitLen (D - q) ≤ B := by
    have := bitLen_mono'' (Nat.sub_le D q)
    omega
  have hq : bitLen q ≤ B := by
    have := bitLen_mono'' (le_of_lt h)
    omega
  have hbKDq : bitLen (Kv * (D - q)) ≤ B := le_trans (bitLen_le_self' _) hKDq
  have h2 : bitLen 2 ≤ 2 * B := le_trans BoundsAux.bl_two_le (by omega)
  obtain ⟨e1, e2, e3, e4⟩ := cube_facts hB1
  obtain ⟨M, hM⟩ : ∃ M, M = (W + 10) ^ 2 * B ^ 3 := ⟨_, rfl⟩
  have hW1 : 1 ≤ (W + 10) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hB3M : B ^ 3 ≤ M := by
    rw [hM]
    calc B ^ 3 = 1 * B ^ 3 := (Nat.one_mul _).symm
      _ ≤ (W + 10) ^ 2 * B ^ 3 := Nat.mul_le_mul_right _ hW1
  have hBW : B * W + 3 * B ≤ M := by
    have h1 : W + 3 ≤ (W + 10) ^ 2 := by
      calc W + 3 ≤ (W + 10) * 1 := by omega
        _ ≤ (W + 10) * (W + 10) := Nat.mul_le_mul_left _ (by omega)
        _ = (W + 10) ^ 2 := (sq _).symm
    calc B * W + 3 * B = (W + 3) * B := by ring
      _ ≤ (W + 10) ^ 2 * B ^ 3 := Nat.mul_le_mul h1 e1
      _ = M := hM.symm
  have hpr : PC ≤ 27 * c1 * B ^ 3 := by
    have h2' : bitLen d + q * Kv + bitLen Kv + 1 ≤ 3 * B := by omega
    calc PC ≤ c1 * (3 * B) ^ 3 := le_trans hPC (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2' 3))
      _ = 27 * c1 * B ^ 3 := by ring
  have hm1 : mulCost Kv (D - q) ≤ 800 * B ^ 3 := by
    calc mulCost Kv (D - q) ≤ 200 * (B + 1) ^ 2 :=
          DrvParamsAux.mulCost_le (a := Kv) (b := D - q) (X := B) (by omega) hDq
      _ ≤ 200 * (4 * B ^ 3) := Nat.mul_le_mul_left _ e3
      _ = 800 * B ^ 3 := by ring
  have hp : powCost 2 Sv (Kv * (D - q)) ≤ 48600 * B ^ 3 := by
    calc powCost 2 Sv (Kv * (D - q)) ≤ 1800 * (2 * B + 1) ^ 3 :=
          DrvParamsAux.powCost_le (c := 2) (a := Sv) (n := Kv * (D - q)) (X := 2 * B)
            (by omega) hSK h2
      _ ≤ 1800 * (27 * B ^ 3) := Nat.mul_le_mul_left _ e4
      _ = 48600 * B ^ 3 := by ring
  have hm2 : mulCost (PR - X) (Sv * 2 ^ (Kv * (D - q))) ≤ 200 * M := by
    have hx : B * W + 3 * B + 1 ≤ (W + 10) * B := by
      have : (W + 10) * B = B * W + 3 * B + 7 * B := by ring
      omega
    calc mulCost (PR - X) (Sv * 2 ^ (Kv * (D - q))) ≤ 200 * (B * W + 3 * B + 1) ^ 2 :=
          DrvParamsAux.mulCost_le (a := PR - X) (b := Sv * 2 ^ (Kv * (D - q)))
            (X := B * W + 3 * B) hPX (by omega)
      _ ≤ 200 * ((W + 10) * B) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx 2)
      _ = 200 * ((W + 10) ^ 2 * B ^ 2) := by ring
      _ ≤ 200 * ((W + 10) ^ 2 * B ^ 3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e2)
      _ = 200 * M := by rw [hM]
  have hR : (27 * c1 + 100000 * (W + 10) ^ 2) * B ^ 3 = 27 * c1 * B ^ 3 + 100000 * M := by
    rw [hM]
    ring
  have hbD : bitLen D ≤ B := by omega
  have hbS : bitLen Sv ≤ B := by omega
  have hBM : B ≤ M := le_trans e1 hB3M
  have h1M : 1 ≤ M := le_trans hB1 hBM
  rw [hR]
  unfold npRowsGen
  linarith only [hpr, hm1, hp, hm2, hP, hPX, hX, hSK, hDq, hq, hbKDq, hBW, hB3M, hBM, h1M, hbD,
    hbS]

/-- The rows branch costs `O(B³)` (`B = |d| + |S| + |K| + |D| + D·K + 1`). -/
theorem npRowsCost_le (c1 W : ℕ) (hc1 : ∀ d K, padRCost d K ≤ c1 * (bitLen d + q0Of d * K +
    bitLen K + 1) ^ 3) (hW : bitLen Wc = W) (d D Kv Sv : ℕ) (h : q0Of d < D) :
    npRowsCost d D Kv Sv ≤ (27 * c1 + 100000 * (W + 10) ^ 2) *
      (bitLen d + bitLen Sv + bitLen Kv + bitLen D + D * Kv + 1) ^ 3 := by
  rw [npRowsCost_eq]
  exact npRowsGen_le c1 W _ _ _ _ d D Kv Sv h (hc1 d Kv) (bitLen_padR_le d Kv W hW)
    (BoundsAux.bl_two_pow_le _)

end Bounds

section Bounds2

/-- `npadCost` with `q0Cost d`, `q₀`, the rows cost as variables. -/
def npadGen (QC q R D : ℕ) : ℕ :=
  (1 + QC) + ((12 * min (bitLen q) (bitLen D) + 15) + ((if q < D then R else 1) + 1)) +
    (2 * bitLen q + 2)

theorem npadCost_eq (d D Kv Sv : ℕ) :
    npadCost d D Kv Sv = npadGen (q0Cost d) (q0Of d) (npRowsCost d D Kv Sv) D := rfl

theorem npadGen_le (c0 c1 W Q QC q R d D Kv Sv : ℕ) (hQC : QC ≤ c0 * (bitLen d + 1) ^ 3)
    (hq : q ≤ Q * (bitLen d + 1))
    (hR : q < D → R ≤ (27 * c1 + 100000 * (W + 10) ^ 2) *
      (bitLen d + bitLen Sv + bitLen Kv + bitLen D + D * Kv + 1) ^ 3) :
    npadGen QC q R D ≤ (c0 + 27 * c1 + 100000 * (W + 10) ^ 2 + 100 * (Q + 1)) *
      (bitLen d + bitLen Sv + bitLen Kv + bitLen D + D * Kv + 1) ^ 3 := by
  obtain ⟨B, hB⟩ : ∃ B, B = bitLen d + bitLen Sv + bitLen Kv + bitLen D + D * Kv + 1 := ⟨_, rfl⟩
  rw [← hB] at hR ⊢
  have hB1 : 1 ≤ B := by omega
  obtain ⟨e1, e2, e3, e4⟩ := cube_facts hB1
  have hbq : bitLen q ≤ Q * B := by
    have h1 := bitLen_le_self' q
    have h2 : Q * (bitLen d + 1) ≤ Q * B := Nat.mul_le_mul_left Q (by omega)
    omega
  have hQB : Q * B ≤ Q * B ^ 3 := Nat.mul_le_mul_left Q e1
  have hqc : QC ≤ c0 * B ^ 3 :=
    le_trans hQC (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
  have hmin : min (bitLen q) (bitLen D) ≤ B := le_trans (min_le_right _ _) (by omega)
  have hB3 : 1 ≤ B ^ 3 := le_trans hB1 e1
  have hW1 : 1 ≤ (W + 10) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hbr : (if q < D then R else 1) ≤ (27 * c1 + 100000 * (W + 10) ^ 2) * B ^ 3 := by
    split_ifs with h
    · exact hR h
    · nlinarith
  unfold npadGen
  nlinarith

theorem npadCost_le : ∃ c, ∀ d D Kv Sv, npadCost d D Kv Sv ≤
    c * (bitLen d + bitLen Sv + bitLen Kv + bitLen D + D * Kv + 1) ^ 3 := by
  obtain ⟨c0, hc0⟩ := q0Cost_le
  obtain ⟨c1, hc1⟩ := padRCost_le
  obtain ⟨W, hW⟩ : ∃ W, bitLen Wc = W := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Nat.clog 2 Wc = Q := ⟨_, rfl⟩
  refine ⟨c0 + 27 * c1 + 100000 * (W + 10) ^ 2 + 100 * (Q + 1), fun d D Kv Sv => ?_⟩
  rw [npadCost_eq]
  exact npadGen_le c0 c1 W Q _ _ _ d D Kv Sv (hc0 d) (by subst hQ; exact q0Of_le d)
    (fun h => npRowsCost_le c1 W hc1 hW d D Kv Sv h)

end Bounds2

/-! ## Closedness -/

section Closed

variable {K : Type}

theorem closed_keepN (st : Fin 16 → K) : (keepN st).Closed :=
  WP.W9comp.closed_liftRegs lN (WP.W9comp.closed_seq (WP.W9comp.closed_seq (WP.W9comp.closed_seq
    (WP.W9comp.closed_seq (WP.W9comp.closed_seq (closed_pushMark _) (closed_mulN _ _ _ _ _ _ _))
      (WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq (closed_copyN _ _ _)
        (closed_powMulN _ _ _ _ _ _ _ _ _ _))))
    (closed_copyN _ _ _)) (closed_dropF _)) (closed_dropF _))

theorem closed_npadRowsB (st : Fin 40 → K) : (npadRowsB st).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_seq (WP.W9comp.closed_seq (WP.W9comp.closed_seq
    (WP.W9comp.closed_seq (WP.W9comp.closed_seq (WP.W9comp.closed_seq (WP.W9comp.closed_seq
    (WP.W9comp.closed_seq (WP.W9comp.closed_seq
    (WP.W9comp.closed_seq (closed_pushMark _) (closed_subN _ _ _ _ _ _))
    (WP.W9comp.closed_seq (closed_pushMark _) (closed_subN _ _ _ _ _ _)))
    (WP.W9comp.closed_seq (closed_pushMark _) (closed_mulN _ _ _ _ _ _ _)))
    (WP.W9comp.closed_seq (closed_pushMark _) (WP.W9comp.closed_seq (closed_copyN _ _ _)
      (closed_powMulN _ _ _ _ _ _ _ _ _ _))))
    (closed_mulN _ _ _ _ _ _ _))
    (closed_dropF _)) (closed_dropF _)) (closed_dropF _)) (closed_dropF _)) (closed_dropF _))
    (closed_dropF _)

theorem closed_npadN (st : Fin 40 → K) : (npadN st).Closed := by
  have hrows : (npadRows st).Closed :=
    WP.W9comp.closed_seq (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN
      (WP.W9comp.closed_seq (closed_pushMark _) (closed_pushMark _))) (closed_padRN _))
      (WP.W9comp.closed_liftRegs lN (closed_npadRowsB st))
  have hskip : (skip : Prog K (fun _ => Sym) Reg2).Closed := by
    show Prog.FreeBelow 0 (Prog.load id)
    trivial
  have hite : (Prog.ite (fun r : Reg2 => isLtR r.1) (npadRows st) skip).Closed := by
    show Prog.FreeBelow 0 (npadRows st) ∧ Prog.FreeBelow 0 skip
    exact ⟨hrows, hskip⟩
  exact WP.W9comp.closed_seq (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN
    (WP.W9comp.closed_seq (closed_pushMark _) (closed_q0N _)))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lN (closed_cmpN' _ _ _ _)) hite))
    (WP.W9comp.closed_liftRegs lN (closed_dropF _))

end Closed

end SubNLogN.Machine.Layer.DrvParamsShared
