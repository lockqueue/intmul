/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafRowAddCtr
import SubNLogN.Machine.CCore.LeafRowAddCS

/-!
# C-core leaf 9 (Lemma A.9 row addition): the counter kernel (`CCore/LeafRowAddCtrK.lean`)

The Lemma A.9 call (`C7PackedXorStmt`) reads seven runtime counters `K, ρ, f, N1, N2, N3, R` as
`natSyms` on its named stacks `1`–`7`. This file computes them from the call descriptor
`t.hdr` (`hdrSyms [P, d, r, Δ, A, R, K, D, S, j0, k, ρ]`) on a small private layout `CS`:
`desc`, the seven counter stacks `c i`, and twenty work stacks. Every work stack and the
descriptor are restored. Arithmetic uses the shared `natSyms` library
(`AppC/C5StreamArith.lean`, `SubNLogN.Machine.NatArith`).
-/

namespace SubNLogN.Machine.CCore.LeafRowAddAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine SubNLogN.Machine.NatArith
open SubNLogN.Machine.Calculus

/-- The header fields of a call descriptor. -/
def hfs (t : CCoreRT) : List ℕ := [t.P, t.d, t.r, t.Δ, t.A, t.R, t.K, t.D, t.S, t.j0, t.k, t.ρ]

theorem hdr_eq (t : CCoreRT) : t.hdr = W9.hdrSyms (hfs t) := rfl

/-! ## The seven counter programs -/

/-- `c 0 := K`. -/
def ctrK : Prog CS (fun _ => Sym) Reg := copyField 6 .desc (.c 0) .wT .wC
/-- `c 1 := ρ`. -/
def ctrRho : Prog CS (fun _ => Sym) Reg := copyField 11 .desc (.c 1) .wT .wC
/-- `c 2 := f = m^(k-1)`. -/
def ctrF : Prog CS (fun _ => Sym) Reg :=
  .seq (copyField 10 .desc .x0 .wT .wC) (.seq (pushNat .x1 1) (.seq (subN .x0 .x1 .x2 .t1 .t2 .t3)
    (.seq (pushNat (.c 2) 1) (.seq (powMulN (.c 2) mn .x2 .pK .pt .mQ .mTd .mA .mB .mAcc)
      (.seq (dropN .x2) (.seq (dropN .x1) (dropN .x0)))))))

/-- The record width `R = 2·r·(P + 2Δ + 3)` on `c 6`. -/
def ctrR : Prog CS (fun _ => Sym) Reg :=
  .seq (copyField 0 .desc .x0 .wT .wC) (.seq (copyField 3 .desc .x1 .wT .wC) (.seq (dblN .x1)
    (.seq (addN .x0 .x1 .x2 .t1 .t2 .t3) (.seq (dropN .x1) (.seq (dropN .x0) (.seq (pushNat .x0 3)
      (.seq (addN .x2 .x0 .x1 .t1 .t2 .t3) (.seq (dropN .x0) (.seq (dropN .x2)
        (.seq (copyField 2 .desc .x0 .wT .wC) (.seq (mulN .x0 .x1 (.c 6) .mA .mB .mAcc .mT)
          (.seq (dblN (.c 6)) (.seq (dropN .x1) (dropN .x0))))))))))))))

/-- `c j := 2^(K·f·cst)` from `c 0 = K`, `c 2 = f`. -/
def ctrPow (j : Fin 7) (cst : ℕ) : Prog CS (fun _ => Sym) Reg :=
  .seq (copyN (.c 0) .x0 .wC) (.seq (copyN (.c 2) .x1 .wC) (.seq (mulN .x0 .x1 .x2 .mA .mB .mAcc .mT)
    (.seq (mulConstN .x2 cst .mQ .mTd .mA .mB .mAcc .mT) (.seq (pushNat (.c j) 1)
      (.seq (powMulN (.c j) 2 .x2 .pK .pt .mQ .mTd .mA .mB .mAcc)
        (.seq (dropN .x2) (.seq (dropN .x1) (dropN .x0))))))))

/-- `c 5 := N3 = S·2^(K·(D - (f·(hi+1) + j0)))` from `c 0 = K`, `c 2 = f`. -/
def ctrN3 (hi1 : ℕ) : Prog CS (fun _ => Sym) Reg :=
  .seq (copyN (.c 2) .x0 .wC) (.seq (mulConstN .x0 hi1 .mQ .mTd .mA .mB .mAcc .mT)
    (.seq (copyField 9 .desc .x1 .wT .wC) (.seq (addN .x0 .x1 .x2 .t1 .t2 .t3)
      (.seq (copyField 7 .desc .x3 .wT .wC) (.seq (subN .x3 .x2 .x4 .t1 .t2 .t3)
        (.seq (copyN (.c 0) .x5 .wC) (.seq (mulN .x5 .x4 .x6 .mA .mB .mAcc .mT)
          (.seq (copyField 8 .desc (.c 5) .wT .wC)
            (.seq (powMulN (.c 5) 2 .x6 .pK .pt .mQ .mTd .mA .mB .mAcc)
              (.seq (dropN .x6) (.seq (dropN .x5) (.seq (dropN .x4) (.seq (dropN .x3)
                (.seq (dropN .x2) (.seq (dropN .x1) (dropN .x0))))))))))))))))

/-! ## Exact costs -/

/-- Cost of `ctrK` and `ctrRho` (one field copy). -/
def costK (t : CCoreRT) : ℕ := 19 * t.hdr.length + 9

/-- Cost of `ctrF`. -/
def costF (t : CCoreRT) : ℕ :=
  (19 * t.hdr.length + 9) + ((bitLen 1 + 1) + (20 * (bitLen t.k + bitLen 1 + 1) +
    ((bitLen 1 + 1) + (powCost mn 1 (t.k - 1) + ((2 * bitLen (t.k - 1) + 4) +
      ((2 * bitLen 1 + 4) + (2 * bitLen t.k + 4)))))))

/-- Cost of `ctrR`. -/
def costR (t : CCoreRT) : ℕ :=
  (19 * t.hdr.length + 9) + ((19 * t.hdr.length + 9) + (3 +
    (20 * (bitLen t.P + bitLen (t.Δ + t.Δ) + 1) + ((2 * bitLen (t.Δ + t.Δ) + 4) +
      ((2 * bitLen t.P + 4) + ((bitLen 3 + 1) +
        (20 * (bitLen (t.P + (t.Δ + t.Δ)) + bitLen 3 + 1) + ((2 * bitLen 3 + 4) +
          ((2 * bitLen (t.P + (t.Δ + t.Δ)) + 4) + ((19 * t.hdr.length + 9) +
            (mulCost t.r (t.P + (t.Δ + t.Δ) + 3) + (3 +
              ((2 * bitLen (t.P + (t.Δ + t.Δ) + 3) + 4) + (2 * bitLen t.r + 4))))))))))))))

/-- Cost of `ctrPow j cst` with `K = Kv`, `f = fv`. -/
def costPow (cst Kv fv : ℕ) : ℕ :=
  (7 * bitLen Kv + 7) + ((7 * bitLen fv + 7) + (mulCost Kv fv + (mulConstCost (Kv * fv) cst +
    ((bitLen 1 + 1) + (powCost 2 1 (Kv * fv * cst) + ((2 * bitLen (Kv * fv * cst) + 4) +
      ((2 * bitLen fv + 4) + (2 * bitLen Kv + 4))))))))

/-- Cost of `ctrN3 hi1` with `K = Kv`, `f = fv`. -/
def costN3 (t : CCoreRT) (hi1 Kv fv : ℕ) : ℕ :=
  (7 * bitLen fv + 7) + (mulConstCost fv hi1 + ((19 * t.hdr.length + 9) +
    (20 * (bitLen (fv * hi1) + bitLen t.j0 + 1) + ((19 * t.hdr.length + 9) +
      (20 * (bitLen t.D + bitLen (fv * hi1 + t.j0) + 1) + ((7 * bitLen Kv + 7) +
        (mulCost Kv (t.D - (fv * hi1 + t.j0)) + ((19 * t.hdr.length + 9) +
          (powCost 2 t.S (Kv * (t.D - (fv * hi1 + t.j0))) +
            ((2 * bitLen (Kv * (t.D - (fv * hi1 + t.j0))) + 4) + ((2 * bitLen Kv + 4) +
              ((2 * bitLen (t.D - (fv * hi1 + t.j0)) + 4) + ((2 * bitLen t.D + 4) +
                ((2 * bitLen (fv * hi1 + t.j0) + 4) + ((2 * bitLen t.j0 + 4) +
                  (2 * bitLen (fv * hi1) + 4))))))))))))))))

/-! ## Exact runs -/

section Runs

variable (t : CCoreRT) (tdesc : List Sym)

theorem runs_ctrK (S : CS → List Sym) (hd : S .desc = t.hdr ++ tdesc) (hw : ∀ i, S (.w i) = []) :
    Runs ctrK S (Function.update S (.c 0) (natSyms t.K ++ S (.c 0))) (fun _ => True)
      (19 * t.hdr.length + 9) :=
  runs_copyField (by decide) (by decide) (by decide) (by decide) (by decide) 6 (hfs t)
    (by simp [hfs]) tdesc S hd (hw 0)

theorem runs_ctrRho (S : CS → List Sym) (hd : S .desc = t.hdr ++ tdesc)
    (hw : ∀ i, S (.w i) = []) :
    Runs ctrRho S (Function.update S (.c 1) (natSyms t.ρ ++ S (.c 1))) (fun _ => True)
      (19 * t.hdr.length + 9) :=
  runs_copyField (by decide) (by decide) (by decide) (by decide) (by decide) 11 (hfs t)
    (by simp [hfs]) tdesc S hd (hw 0)

/-- Uniform size parameter of the counter costs. -/
def ctrB (t : CCoreRT) : ℕ := t.hdr.length + t.K * t.D

theorem runs_ctrF (S : CS → List Sym) (hd : S .desc = t.hdr ++ tdesc) (hw : ∀ i, S (.w i) = [])
    (hc : S (.c 2) = []) (hk : 1 ≤ t.k) :
    Runs ctrF S (Function.update S (.c 2) (natSyms (mn ^ (t.k - 1)))) (fun _ => True)
      (costF t) := by
  have h := WP.W9comp.runs_seq (runs_copyField (d := CS.desc) (dst := CS.x0) (t := CS.wT)
    (tc := CS.wC) (by decide) (by decide) (by decide) (by decide) (by decide) 10 (hfs t)
    (by simp [hfs]) tdesc S hd (hw 0))
   (WP.W9comp.runs_seq (runs_pushNat CS.x1 1 _)
   (WP.W9comp.runs_seq (runs_subN (x := CS.x0) (y := CS.x1) (z := CS.x2) (t1 := CS.t1)
      (t2 := CS.t2) (t3 := CS.t3) (by decide) t.k 1 [] [] _ termOK_nil termOK_nil hk
      (by simp [Function.update_apply, hw, hfs]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_pushNat (CS.c 2) 1 _)
   (WP.W9comp.runs_seq (runs_powMulN (k := CS.c 2) (ns := CS.x2) (Kc := CS.pK) (t := CS.pt)
      (Q := CS.mQ) (Tdst := CS.mTd) (A := CS.mA) (Bs := CS.mB) (Acc := CS.mAcc) (by decide) mn
      (by norm_num [mn, tripleM]) 1 (t.k - 1) [] [] _ termOK_nil termOK_nil
      (by simp [Function.update_apply, hw, hc]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dropN CS.x2 (t.k - 1) [] _ termOK_nil (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dropN CS.x1 1 [] _ termOK_nil (by simp [Function.update_apply, hw]))
     (runs_dropN CS.x0 t.k [] _ termOK_nil (by simp [Function.update_apply, hw, hfs]))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h ?_) (fun _ _ => trivial) (le_of_eq rfl)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem runs_ctrR (S : CS → List Sym) (hd : S .desc = t.hdr ++ tdesc) (hw : ∀ i, S (.w i) = [])
    (hc : S (.c 6) = []) :
    Runs ctrR S (Function.update S (.c 6) (natSyms (2 * t.r * t.wg))) (fun _ => True)
      (costR t) := by
  have h := WP.W9comp.runs_seq (runs_copyField (d := CS.desc) (dst := CS.x0) (t := CS.wT)
    (tc := CS.wC) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (hfs t)
    (by simp [hfs]) tdesc S hd (hw 0))
   (WP.W9comp.runs_seq (runs_copyField (d := CS.desc) (dst := CS.x1) (t := CS.wT)
    (tc := CS.wC) (by decide) (by decide) (by decide) (by decide) (by decide) 3 (hfs t)
    (by simp [hfs]) tdesc _ (by simp [Function.update_apply, hd, hdr_eq]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dblN CS.x1 t.Δ [] _ termOK_nil (by simp [Function.update_apply, hw, hfs]))
   (WP.W9comp.runs_seq (runs_addN (x := CS.x0) (y := CS.x1) (z := CS.x2) (t1 := CS.t1)
      (t2 := CS.t2) (t3 := CS.t3) (by decide) t.P (t.Δ + t.Δ) [] [] _ termOK_nil termOK_nil
      (by simp [Function.update_apply, hw, hfs]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dropN CS.x1 (t.Δ + t.Δ) [] _ termOK_nil (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dropN CS.x0 t.P [] _ termOK_nil (by simp [Function.update_apply, hw, hfs]))
   (WP.W9comp.runs_seq (runs_pushNat CS.x0 3 _)
   (WP.W9comp.runs_seq (runs_addN (x := CS.x2) (y := CS.x0) (z := CS.x1) (t1 := CS.t1)
      (t2 := CS.t2) (t3 := CS.t3) (by decide) (t.P + (t.Δ + t.Δ)) 3 [] [] _ termOK_nil
      termOK_nil (by simp [Function.update_apply, hw]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dropN CS.x0 3 [] _ termOK_nil (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dropN CS.x2 (t.P + (t.Δ + t.Δ)) [] _ termOK_nil (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_copyField (d := CS.desc) (dst := CS.x0) (t := CS.wT)
    (tc := CS.wC) (by decide) (by decide) (by decide) (by decide) (by decide) 2 (hfs t)
    (by simp [hfs]) tdesc _ (by simp [Function.update_apply, hd, hdr_eq]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_mulN (x := CS.x0) (y := CS.x1) (z := CS.c 6) (A := CS.mA)
      (Bs := CS.mB) (Acc := CS.mAcc) (T := CS.mT) (by decide) t.r (t.P + (t.Δ + t.Δ) + 3)
      [] [] _ termOK_nil termOK_nil (by simp [Function.update_apply, hw, hfs]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dblN (CS.c 6) (t.r * (t.P + (t.Δ + t.Δ) + 3)) [] _ termOK_nil
      (by simp [Function.update_apply, hw, hc]))
   (WP.W9comp.runs_seq (runs_dropN CS.x1 (t.P + (t.Δ + t.Δ) + 3) [] _ termOK_nil
      (by simp [Function.update_apply, hw]))
     (runs_dropN CS.x0 t.r [] _ termOK_nil (by simp [Function.update_apply, hw, hfs])))))))))))))))
  have hv : t.r * (t.P + (t.Δ + t.Δ) + 3) + t.r * (t.P + (t.Δ + t.Δ) + 3) =
      2 * t.r * t.wg := by simp only [CCoreRT.wg]; ring
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h ?_) (fun _ _ => trivial) (le_of_eq rfl)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem runs_ctrPow (j : Fin 7) (hj0 : j ≠ 0) (hj2 : j ≠ 2) (cst Kv fv : ℕ)
    (S : CS → List Sym) (hw : ∀ i, S (.w i) = []) (h0 : S (.c 0) = natSyms Kv)
    (h2 : S (.c 2) = natSyms fv) (hc : S (.c j) = []) :
    Runs (ctrPow j cst) S (Function.update S (.c j) (natSyms (2 ^ (Kv * fv * cst))))
      (fun _ => True) (costPow cst Kv fv) := by
  have hj0' : CS.c j ≠ CS.c 0 := fun h => hj0 (CS.c.inj h)
  have hj2' : CS.c j ≠ CS.c 2 := fun h => hj2 (CS.c.inj h)
  have hnd : [CS.c j, CS.x2, CS.pK, CS.pt, CS.mQ, CS.mTd, CS.mA, CS.mB, CS.mAcc].Nodup := by
    simp [List.nodup_cons]
  have h := WP.W9comp.runs_seq (runs_copyN (src := CS.c 0) (dst := CS.x0) (tmp := CS.wC)
      (by decide) (by decide) (by decide) Kv [] S termOK_nil (by rw [h0, List.append_nil]))
   (WP.W9comp.runs_seq (runs_copyN (src := CS.c 2) (dst := CS.x1) (tmp := CS.wC)
      (by decide) (by decide) (by decide) fv [] _ termOK_nil (by simp [Function.update_apply, h2]))
   (WP.W9comp.runs_seq (runs_mulN (x := CS.x0) (y := CS.x1) (z := CS.x2) (A := CS.mA)
      (Bs := CS.mB) (Acc := CS.mAcc) (T := CS.mT) (by decide) Kv fv [] [] _ termOK_nil
      termOK_nil (by simp [Function.update_apply, hw]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_mulConstN (k := CS.x2) (Q := CS.mQ) (Tdst := CS.mTd) (A := CS.mA)
      (Bs := CS.mB) (Acc := CS.mAcc) (T := CS.mT) (by decide) cst (Kv * fv) [] _ termOK_nil
      (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_pushNat (CS.c j) 1 _)
   (WP.W9comp.runs_seq (runs_powMulN (k := CS.c j) (ns := CS.x2) (Kc := CS.pK) (t := CS.pt)
      (Q := CS.mQ) (Tdst := CS.mTd) (A := CS.mA) (Bs := CS.mB) (Acc := CS.mAcc) hnd 2
      (by norm_num) 1 (Kv * fv * cst) [] [] _ termOK_nil termOK_nil (by simp [Function.update_apply, hw, hc])
      (by simp [Function.update_apply, hw, hj0', hj2']))
   (WP.W9comp.runs_seq (runs_dropN CS.x2 (Kv * fv * cst) [] _ termOK_nil
      (by simp [Function.update_apply, hw, hj0', hj2']))
   (WP.W9comp.runs_seq (runs_dropN CS.x1 fv [] _ termOK_nil (by simp [Function.update_apply, hw]))
     (runs_dropN CS.x0 Kv [] _ termOK_nil (by simp [Function.update_apply, hw])))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h ?_) (fun _ _ => trivial) (le_of_eq rfl)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem runs_ctrN3 (hi1 Kv fv : ℕ) (S : CS → List Sym) (hd : S .desc = t.hdr ++ tdesc)
    (hw : ∀ i, S (.w i) = []) (h0 : S (.c 0) = natSyms Kv) (h2 : S (.c 2) = natSyms fv)
    (hc : S (.c 5) = []) (hle : fv * hi1 + t.j0 ≤ t.D) :
    Runs (ctrN3 hi1) S
      (Function.update S (.c 5) (natSyms (t.S * 2 ^ (Kv * (t.D - (fv * hi1 + t.j0))))))
      (fun _ => True) (costN3 t hi1 Kv fv) := by
  have h := WP.W9comp.runs_seq (runs_copyN (src := CS.c 2) (dst := CS.x0) (tmp := CS.wC)
      (by decide) (by decide) (by decide) fv [] S termOK_nil (by rw [h2, List.append_nil]))
   (WP.W9comp.runs_seq (runs_mulConstN (k := CS.x0) (Q := CS.mQ) (Tdst := CS.mTd) (A := CS.mA)
      (Bs := CS.mB) (Acc := CS.mAcc) (T := CS.mT) (by decide) hi1 fv [] _ termOK_nil
      (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_copyField (d := CS.desc) (dst := CS.x1) (t := CS.wT)
    (tc := CS.wC) (by decide) (by decide) (by decide) (by decide) (by decide) 9 (hfs t)
    (by simp [hfs]) tdesc _ (by simp [Function.update_apply, hd, hdr_eq]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_addN (x := CS.x0) (y := CS.x1) (z := CS.x2) (t1 := CS.t1)
      (t2 := CS.t2) (t3 := CS.t3) (by decide) (fv * hi1) t.j0 [] [] _ termOK_nil termOK_nil
      (by simp [Function.update_apply, hw]) (by simp [Function.update_apply, hw, hfs]))
   (WP.W9comp.runs_seq (runs_copyField (d := CS.desc) (dst := CS.x3) (t := CS.wT)
    (tc := CS.wC) (by decide) (by decide) (by decide) (by decide) (by decide) 7 (hfs t)
    (by simp [hfs]) tdesc _ (by simp [Function.update_apply, hd, hdr_eq]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_subN (x := CS.x3) (y := CS.x2) (z := CS.x4) (t1 := CS.t1)
      (t2 := CS.t2) (t3 := CS.t3) (by decide) t.D (fv * hi1 + t.j0) [] [] _ termOK_nil
      termOK_nil hle (by simp [Function.update_apply, hw, hfs]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_copyN (src := CS.c 0) (dst := CS.x5) (tmp := CS.wC)
      (by decide) (by decide) (by decide) Kv [] _ termOK_nil (by simp [Function.update_apply, h0]))
   (WP.W9comp.runs_seq (runs_mulN (x := CS.x5) (y := CS.x4) (z := CS.x6) (A := CS.mA)
      (Bs := CS.mB) (Acc := CS.mAcc) (T := CS.mT) (by decide) Kv (t.D - (fv * hi1 + t.j0))
      [] [] _ termOK_nil termOK_nil (by simp [Function.update_apply, hw]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_copyField (d := CS.desc) (dst := CS.c 5) (t := CS.wT)
    (tc := CS.wC) (by decide) (by decide) (by decide) (by decide) (by decide) 8 (hfs t)
    (by simp [hfs]) tdesc _ (by simp [Function.update_apply, hd, hdr_eq]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_powMulN (k := CS.c 5) (ns := CS.x6) (Kc := CS.pK) (t := CS.pt)
      (Q := CS.mQ) (Tdst := CS.mTd) (A := CS.mA) (Bs := CS.mB) (Acc := CS.mAcc) (by decide) 2
      (by norm_num) t.S (Kv * (t.D - (fv * hi1 + t.j0))) [] [] _ termOK_nil termOK_nil
      (by simp [Function.update_apply, hw, hc, hfs]) (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dropN CS.x6 (Kv * (t.D - (fv * hi1 + t.j0))) [] _ termOK_nil
      (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dropN CS.x5 Kv [] _ termOK_nil (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dropN CS.x4 (t.D - (fv * hi1 + t.j0)) [] _ termOK_nil
      (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dropN CS.x3 t.D [] _ termOK_nil (by simp [Function.update_apply, hw, hfs]))
   (WP.W9comp.runs_seq (runs_dropN CS.x2 (fv * hi1 + t.j0) [] _ termOK_nil (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_dropN CS.x1 t.j0 [] _ termOK_nil (by simp [Function.update_apply, hw, hfs]))
     (runs_dropN CS.x0 (fv * hi1) [] _ termOK_nil (by simp [Function.update_apply, hw])))))))))))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h ?_) (fun _ _ => trivial) (le_of_eq rfl)
  funext k
  cases k with
  | desc => simp [Function.update_apply]
  | c i => fin_cases i <;> simp [Function.update_apply, hc]
  | w i => fin_cases i <;> simp [Function.update_apply, hw]

/-- Clear the seven counter stacks. -/
def ctrClr : Prog CS (fun _ => Sym) Reg :=
  .seq (dropN (.c 0)) (.seq (dropN (.c 1)) (.seq (dropN (.c 2)) (.seq (dropN (.c 3))
    (.seq (dropN (.c 4)) (.seq (dropN (.c 5)) (dropN (.c 6)))))))

theorem runs_ctrClr (vals : Fin 7 → ℕ) (S : CS → List Sym) (hc : ∀ i, S (.c i) = []) :
    Runs ctrClr (setC S vals) S (fun _ => True)
      ((2 * bitLen (vals 0) + 4) + ((2 * bitLen (vals 1) + 4) + ((2 * bitLen (vals 2) + 4) +
        ((2 * bitLen (vals 3) + 4) + ((2 * bitLen (vals 4) + 4) + ((2 * bitLen (vals 5) + 4) +
          (2 * bitLen (vals 6) + 4))))))) := by
  have h := WP.W9comp.runs_seq (runs_dropN (CS.c 0) (vals 0) [] (setC S vals) termOK_nil
      (by simp [setC]))
   (WP.W9comp.runs_seq (runs_dropN (CS.c 1) (vals 1) [] _ termOK_nil
      (by simp [Function.update_apply, setC]))
   (WP.W9comp.runs_seq (runs_dropN (CS.c 2) (vals 2) [] _ termOK_nil
      (by simp [Function.update_apply, setC]))
   (WP.W9comp.runs_seq (runs_dropN (CS.c 3) (vals 3) [] _ termOK_nil
      (by simp [Function.update_apply, setC]))
   (WP.W9comp.runs_seq (runs_dropN (CS.c 4) (vals 4) [] _ termOK_nil
      (by simp [Function.update_apply, setC]))
   (WP.W9comp.runs_seq (runs_dropN (CS.c 5) (vals 5) [] _ termOK_nil
      (by simp [Function.update_apply, setC]))
     (runs_dropN (CS.c 6) (vals 6) [] _ termOK_nil
      (by simp [Function.update_apply, setC])))))))
  refine WP.W9comp.runs_congr h ?_
  funext k
  cases k with
  | desc => simp [Function.update_apply, setC]
  | c i => fin_cases i <;> simp [Function.update_apply, setC, hc]
  | w i => simp [Function.update_apply, setC]

end Runs


/-! ## The whole counter set-up -/

/-- All seven counters: `K, ρ, f, R`, then `N1, N2` (powers of two) and `N3`. -/
def ctrAll (p₁ p₂ : ℕ) : Prog CS (fun _ => Sym) Reg :=
  .seq ctrK (.seq ctrRho (.seq ctrF (.seq ctrR (.seq (ctrPow 3 (midS p₁ p₂ - loS p₁ p₂ - 1))
    (.seq (ctrPow 4 (hiS p₁ p₂ - midS p₁ p₂ - 1)) (ctrN3 (hiS p₁ p₂ + 1)))))))

/-- The counter values (Lemma A.9 named stacks `1`–`7`). -/
def ctrVals (t : CCoreRT) (p₁ p₂ : ℕ) : Fin 7 → ℕ :=
  ![t.K, t.ρ, mn ^ (t.k - 1),
    2 ^ (t.K * mn ^ (t.k - 1) * (midS p₁ p₂ - loS p₁ p₂ - 1)),
    2 ^ (t.K * mn ^ (t.k - 1) * (hiS p₁ p₂ - midS p₁ p₂ - 1)),
    t.S * 2 ^ (t.K * (t.D - (mn ^ (t.k - 1) * (hiS p₁ p₂ + 1) + t.j0))),
    2 * t.r * t.wg]

/-- Cost of `ctrAll`. -/
def costAll (t : CCoreRT) (p₁ p₂ : ℕ) : ℕ :=
  costK t + (costK t + (costF t + (costR t +
    (costPow (midS p₁ p₂ - loS p₁ p₂ - 1) t.K (mn ^ (t.k - 1)) +
      (costPow (hiS p₁ p₂ - midS p₁ p₂ - 1) t.K (mn ^ (t.k - 1)) +
        costN3 t (hiS p₁ p₂ + 1) t.K (mn ^ (t.k - 1)))))))

theorem runs_ctrAll (t : CCoreRT) (tdesc : List Sym) (p₁ p₂ : ℕ) (S : CS → List Sym)
    (hd : S .desc = t.hdr ++ tdesc) (hw : ∀ i, S (.w i) = []) (hc : ∀ i, S (.c i) = [])
    (hk : 1 ≤ t.k) (hle : mn ^ (t.k - 1) * (hiS p₁ p₂ + 1) + t.j0 ≤ t.D) :
    Runs (ctrAll p₁ p₂) S (setC S (ctrVals t p₁ p₂)) (fun _ => True) (costAll t p₁ p₂) := by
  have h := WP.W9comp.runs_seq (runs_ctrK t tdesc S hd hw)
   (WP.W9comp.runs_seq (runs_ctrRho t tdesc _ (by simp [Function.update_apply, hd])
      (by simp [Function.update_apply, hw]))
   (WP.W9comp.runs_seq (runs_ctrF t tdesc _ (by simp [Function.update_apply, hd])
      (by simp [Function.update_apply, hw]) (by simp [Function.update_apply, hc]) hk)
   (WP.W9comp.runs_seq (runs_ctrR t tdesc _ (by simp [Function.update_apply, hd])
      (by simp [Function.update_apply, hw]) (by simp [Function.update_apply, hc]))
   (WP.W9comp.runs_seq (runs_ctrPow 3 (by decide) (by decide) (midS p₁ p₂ - loS p₁ p₂ - 1) t.K
      (mn ^ (t.k - 1)) _ (by simp [Function.update_apply, hw])
      (by simp [Function.update_apply, hc]) (by simp [Function.update_apply, hc])
      (by simp [Function.update_apply, hc]))
   (WP.W9comp.runs_seq (runs_ctrPow 4 (by decide) (by decide) (hiS p₁ p₂ - midS p₁ p₂ - 1) t.K
      (mn ^ (t.k - 1)) _ (by simp [Function.update_apply, hw])
      (by simp [Function.update_apply, hc]) (by simp [Function.update_apply, hc])
      (by simp [Function.update_apply, hc]))
     (runs_ctrN3 t tdesc (hiS p₁ p₂ + 1) t.K (mn ^ (t.k - 1)) _
      (by simp [Function.update_apply, hd]) (by simp [Function.update_apply, hw])
      (by simp [Function.update_apply, hc]) (by simp [Function.update_apply, hc])
      (by simp [Function.update_apply, hc]) hle))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h ?_) (fun _ _ => trivial) (le_of_eq rfl)
  funext k
  cases k with
  | desc => simp [Function.update_apply, setC]
  | c i => fin_cases i <;> simp [Function.update_apply, setC, ctrVals, hc]
  | w i => simp [Function.update_apply, setC]


/-- Cost of `ctrClr`. -/
def costClr (vals : Fin 7 → ℕ) : ℕ :=
  (2 * bitLen (vals 0) + 4) + ((2 * bitLen (vals 1) + 4) + ((2 * bitLen (vals 2) + 4) +
    ((2 * bitLen (vals 3) + 4) + ((2 * bitLen (vals 4) + 4) + ((2 * bitLen (vals 5) + 4) +
      (2 * bitLen (vals 6) + 4))))))

theorem runs_ctrClr' (vals : Fin 7 → ℕ) (S : CS → List Sym) (hc : ∀ i, S (.c i) = []) :
    Runs ctrClr (setC S vals) S (fun _ => True) (costClr vals) :=
  runs_ctrClr vals S hc

/-! ## Closedness -/

theorem closed_ctrK : ctrK.Closed := closed_copyField _ _ _ _ _

theorem closed_ctrRho : ctrRho.Closed := closed_copyField _ _ _ _ _

theorem closed_ctrF : ctrF.Closed :=
  ⟨closed_copyField _ _ _ _ _, closed_pushNat _ _, closed_subN _ _ _ _ _ _, closed_pushNat _ _,
    closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_dropN _, closed_dropN _, closed_dropN _⟩

theorem closed_ctrR : ctrR.Closed :=
  ⟨closed_copyField _ _ _ _ _, closed_copyField _ _ _ _ _, closed_dblN _, closed_addN _ _ _ _ _ _,
    closed_dropN _, closed_dropN _, closed_pushNat _ _, closed_addN _ _ _ _ _ _, closed_dropN _,
    closed_dropN _, closed_copyField _ _ _ _ _, closed_mulN _ _ _ _ _ _ _, closed_dblN _,
    closed_dropN _, closed_dropN _⟩

theorem closed_ctrPow (j : Fin 7) (cst : ℕ) : (ctrPow j cst).Closed :=
  ⟨closed_copyN _ _ _, closed_copyN _ _ _, closed_mulN _ _ _ _ _ _ _,
    closed_mulConstN _ _ _ _ _ _ _ _, closed_pushNat _ _, closed_powMulN _ _ _ _ _ _ _ _ _ _,
    closed_dropN _, closed_dropN _, closed_dropN _⟩

theorem closed_ctrN3 (hi1 : ℕ) : (ctrN3 hi1).Closed :=
  ⟨closed_copyN _ _ _, closed_mulConstN _ _ _ _ _ _ _ _, closed_copyField _ _ _ _ _,
    closed_addN _ _ _ _ _ _, closed_copyField _ _ _ _ _, closed_subN _ _ _ _ _ _,
    closed_copyN _ _ _, closed_mulN _ _ _ _ _ _ _, closed_copyField _ _ _ _ _,
    closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_dropN _, closed_dropN _, closed_dropN _,
    closed_dropN _, closed_dropN _, closed_dropN _, closed_dropN _⟩

theorem closed_ctrAll (p₁ p₂ : ℕ) : (ctrAll p₁ p₂).Closed :=
  ⟨closed_ctrK, closed_ctrRho, closed_ctrF, closed_ctrR, closed_ctrPow _ _, closed_ctrPow _ _,
    closed_ctrN3 _⟩

theorem closed_ctrClr : ctrClr.Closed :=
  ⟨closed_dropN _, closed_dropN _, closed_dropN _, closed_dropN _, closed_dropN _, closed_dropN _,
    closed_dropN _⟩

end SubNLogN.Machine.CCore.LeafRowAddAux
