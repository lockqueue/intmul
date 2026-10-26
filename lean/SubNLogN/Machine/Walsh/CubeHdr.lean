/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CubeLayer
import SubNLogN.Machine.Walsh.CubeHdrKit

/-!
# K3.0a (`Machine/Walsh/CubeHdr.lean`): the slice-header builder

Paper: Proposition A.11 (`prop:prop14-param`, the layer header `Γ(P)Γ(d)Γ(r)Γ(D)Γ(A)Γ(S)Γ(K)Γ(ρ+1)Γ(w)`) and
Definition 5.6 (`def:walsh-positional`: the slice shape has `A = 2^{j₀}`, `S = 2^{nS}`).

**Scope (honest summary).** Proved (no `sorry`): `cubeHdr_holds : CubeHdrStmt`
(`Machine/Walsh/CubeLayer.lean`), and with it `cubeLayer_of_layerMachine :
LayerMachineGenStmt Band (layerCost lam') → CubeLayerStmt Band lam'` (no other hypothesis).
Helpers live in `SubNLogN.Machine.WalshCubeAux`.

## Plan
Stacks `KLoc (Fin 2) (Fin 14)`: `0` the slice header `[P, d, r, w, K, m, j₀, D, nS, ρ]`
(restored), `1` the target; scratch: `pk` (park), nine field stacks, `C` (counter), `kc, u, t`
(W3 scratch). All scratch is empty on entry and on exit.
1. Unpack (`runs_hdrUnpack`): move each field onto its own stack, bits reversed (`unpackField`;
   `m` is only parked), parking a reversed copy of the header on `pk`; `xfer pk 0` restores the
   header exactly. Cost `≤ 10·|sliceHdr|`.
2. Build bottom-up (`runs_hdrBuild`): `w`; `ρ` then `inc` (`ρ + 1`); `K`; `2^{nS}`, `2^{j₀}`
   (`pow2Field`, the proved W3 concatenation); `D`; `r`; `d`; `P`; each preceded by a `mark`.
   Cost `≤ 50(Σ|fields| + 10) + 36(j₀ + nS)`.
Total `≤ 60((w + m + 1) + |sliceHdr|)` since `j₀ + nS ≤ m`.
-/

namespace SubNLogN.Machine.WalshCubeAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability SubNLogN.Machine

theorem closed_inc' {K : Type} (k t : K) : (inc k t).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, inc, incFix, scanLoop, scanBody, pushC, popR, restoreR,
    pushR, skip, moveBits, moveBitsBody]

/-! ## Stacks and programs -/

/-- Stacks of the header builder: named `Fin 2`, scratch `Fin 14`. -/
abbrev HL : Type := KLoc (Fin 2) (Fin 14)

abbrev csSrc : HL := .inl 0
abbrev csDst : HL := .inl 1
abbrev csPK : HL := .inr 0
abbrev csFP : HL := .inr 1
abbrev csFd : HL := .inr 2
abbrev csFr : HL := .inr 3
abbrev csFw : HL := .inr 4
abbrev csFK : HL := .inr 5
abbrev csFj : HL := .inr 6
abbrev csFD : HL := .inr 7
abbrev csFn : HL := .inr 8
abbrev csFq : HL := .inr 9
abbrev csC : HL := .inr 10
abbrev csKc : HL := .inr 11
abbrev csU : HL := .inr 12
abbrev csT : HL := .inr 13

/-- Phase 1: unpack the ten fields (bits reversed; `m` parked only), then restore the header. -/
def hdrUnpackProg : SProg HL :=
  .seq (unpackField csSrc csFP csPK) (.seq (unpackField csSrc csFd csPK)
  (.seq (unpackField csSrc csFr csPK) (.seq (unpackField csSrc csFw csPK)
  (.seq (unpackField csSrc csFK csPK) (.seq (parkField csSrc csPK)
  (.seq (unpackField csSrc csFj csPK) (.seq (unpackField csSrc csFD csPK)
  (.seq (unpackField csSrc csFn csPK) (.seq (unpackField csSrc csFq csPK)
  (xfer csPK csSrc))))))))))

/-- Phase 2: build `[P, d, r, D, 2^{j₀}, 2^{nS}, K, ρ+1, w]` on the target, bottom-up. -/
def hdrBuildProg : SProg HL :=
  .seq (pushFieldRev csFw csDst) (.seq (pushFieldRev csFq csDst) (.seq (inc csDst csT)
  (.seq (pushFieldRev csFK csDst) (.seq (pow2Field csFn csDst csC csPK csKc csU csT)
  (.seq (pow2Field csFj csDst csC csPK csKc csU csT) (.seq (pushFieldRev csFD csDst)
  (.seq (pushFieldRev csFr csDst) (.seq (pushFieldRev csFd csDst)
  (pushFieldRev csFP csDst)))))))))

/-- **The slice-header builder.** -/
def cubeHdrProg : SProg HL := .seq hdrUnpackProg hdrBuildProg

theorem closed_cubeHdrProg : cubeHdrProg.Closed := by
  refine WP.W9comp.closed_seq ?_ ?_
  · exact WP.W9comp.closed_seq (closed_unpackField _ _ _) (WP.W9comp.closed_seq
      (closed_unpackField _ _ _) (WP.W9comp.closed_seq (closed_unpackField _ _ _)
      (WP.W9comp.closed_seq (closed_unpackField _ _ _) (WP.W9comp.closed_seq
      (closed_unpackField _ _ _) (WP.W9comp.closed_seq (closed_parkField _ _)
      (WP.W9comp.closed_seq (closed_unpackField _ _ _) (WP.W9comp.closed_seq
      (closed_unpackField _ _ _) (WP.W9comp.closed_seq (closed_unpackField _ _ _)
      (WP.W9comp.closed_seq (closed_unpackField _ _ _) (closed_xfer _ _))))))))))
  · exact WP.W9comp.closed_seq (closed_pushFieldRev _ _) (WP.W9comp.closed_seq
      (closed_pushFieldRev _ _) (WP.W9comp.closed_seq (closed_inc' _ _) (WP.W9comp.closed_seq
      (closed_pushFieldRev _ _) (WP.W9comp.closed_seq (closed_pow2Field _ _ _ _ _ _ _)
      (WP.W9comp.closed_seq (closed_pow2Field _ _ _ _ _ _ _) (WP.W9comp.closed_seq
      (closed_pushFieldRev _ _) (WP.W9comp.closed_seq (closed_pushFieldRev _ _)
      (WP.W9comp.closed_seq (closed_pushFieldRev _ _) (closed_pushFieldRev _ _)))))))))

/-- The stacks after phase 1: the input stacks, with the nine fields held reversed. -/
def restoredSt (S : HL → List Sym) (P d r w K j₀ D nS ρ : ℕ) : HL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update S
      csFP (natSyms P).reverse) csFd (natSyms d).reverse) csFr (natSyms r).reverse)
      csFw (natSyms w).reverse) csFK (natSyms K).reverse) csFj (natSyms j₀).reverse)
      csFD (natSyms D).reverse) csFn (natSyms nS).reverse) csFq (natSyms ρ).reverse

/-! ## Phase 1: unpack and restore -/

theorem hdrSyms_nil' : hdrSyms [] = [] := rfl

/-- **Phase 1**: from the input stacks (scratch empty, the slice header on `0`) to `restoredSt`,
within `10·|sliceHdr|` steps. -/
theorem runs_hdrUnpack (S : HL → List Sym) (hcl : ∀ e, S (.inr e) = [])
    (P d r w K m j₀ D nS ρ : ℕ) (hrest : List Sym)
    (h0 : S csSrc = sliceHdr P d r w K m j₀ D nS ρ ++ hrest) :
    Runs hdrUnpackProg S (restoredSt S P d r w K j₀ D nS ρ) (fun _ => True)
      (10 * (sliceHdr P d r w K m j₀ D nS ρ).length) := by
  have e0 : S csSrc = natSyms P ++ Sym.mark :: (hdrSyms [d, r, w, K, m, j₀, D, nS, ρ] ++ hrest) := by
    rw [h0, sliceHdr, hdrSyms_cons_append]
  -- 1. `P`
  obtain ⟨S1, hS1⟩ : ∃ S', S' = Function.update (Function.update (Function.update S csSrc
      (hdrSyms [d, r, w, K, m, j₀, D, nS, ρ] ++ hrest)) csFP (natSyms P).reverse) csPK
      (hdrSyms [P]).reverse := ⟨_, rfl⟩
  have r1 : Runs (unpackField csSrc csFP csPK) S S1 (fun _ => True) (4 * bitLen P + 3) := by
    rw [hS1]
    exact runs_unpackField' (by decide) (by decide) (by decide) P [] _ S e0 (hcl _) (hcl _)
  -- 2. `d`
  have e1 : S1 csSrc = natSyms d ++ Sym.mark :: (hdrSyms [r, w, K, m, j₀, D, nS, ρ] ++ hrest) := by
    rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, hdrSyms_cons_append]
  obtain ⟨S2, hS2⟩ : ∃ S', S' = Function.update (Function.update (Function.update S1 csSrc
      (hdrSyms [r, w, K, m, j₀, D, nS, ρ] ++ hrest)) csFd (natSyms d).reverse) csPK
      (hdrSyms [P, d]).reverse := ⟨_, rfl⟩
  have r2 : Runs (unpackField csSrc csFd csPK) S1 S2 (fun _ => True) (4 * bitLen d + 3) := by
    rw [hS2]
    exact runs_unpackField' (by decide) (by decide) (by decide) d [P] _ S1 e1
      (by simp +decide only [hS1, Function.update_apply, if_false, hcl])
      (by rw [hS1, Function.update_self])
  -- 3. `r`
  have e2 : S2 csSrc = natSyms r ++ Sym.mark :: (hdrSyms [w, K, m, j₀, D, nS, ρ] ++ hrest) := by
    rw [hS2, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, hdrSyms_cons_append]
  obtain ⟨S3, hS3⟩ : ∃ S', S' = Function.update (Function.update (Function.update S2 csSrc
      (hdrSyms [w, K, m, j₀, D, nS, ρ] ++ hrest)) csFr (natSyms r).reverse) csPK
      (hdrSyms [P, d, r]).reverse := ⟨_, rfl⟩
  have r3 : Runs (unpackField csSrc csFr csPK) S2 S3 (fun _ => True) (4 * bitLen r + 3) := by
    rw [hS3]
    exact runs_unpackField' (by decide) (by decide) (by decide) r [P, d] _ S2 e2
      (by simp +decide only [hS2, hS1, Function.update_apply, if_false, hcl])
      (by rw [hS2, Function.update_self])
  -- 4. `w`
  have e3 : S3 csSrc = natSyms w ++ Sym.mark :: (hdrSyms [K, m, j₀, D, nS, ρ] ++ hrest) := by
    rw [hS3, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, hdrSyms_cons_append]
  obtain ⟨S4, hS4⟩ : ∃ S', S' = Function.update (Function.update (Function.update S3 csSrc
      (hdrSyms [K, m, j₀, D, nS, ρ] ++ hrest)) csFw (natSyms w).reverse) csPK
      (hdrSyms [P, d, r, w]).reverse := ⟨_, rfl⟩
  have r4 : Runs (unpackField csSrc csFw csPK) S3 S4 (fun _ => True) (4 * bitLen w + 3) := by
    rw [hS4]
    exact runs_unpackField' (by decide) (by decide) (by decide) w [P, d, r] _ S3 e3
      (by simp +decide only [hS3, hS2, hS1, Function.update_apply, if_false, hcl])
      (by rw [hS3, Function.update_self])
  -- 5. `K`
  have e4 : S4 csSrc = natSyms K ++ Sym.mark :: (hdrSyms [m, j₀, D, nS, ρ] ++ hrest) := by
    rw [hS4, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, hdrSyms_cons_append]
  obtain ⟨S5, hS5⟩ : ∃ S', S' = Function.update (Function.update (Function.update S4 csSrc
      (hdrSyms [m, j₀, D, nS, ρ] ++ hrest)) csFK (natSyms K).reverse) csPK
      (hdrSyms [P, d, r, w, K]).reverse := ⟨_, rfl⟩
  have r5 : Runs (unpackField csSrc csFK csPK) S4 S5 (fun _ => True) (4 * bitLen K + 3) := by
    rw [hS5]
    exact runs_unpackField' (by decide) (by decide) (by decide) K [P, d, r, w] _ S4 e4
      (by simp +decide only [hS4, hS3, hS2, hS1, Function.update_apply, if_false, hcl])
      (by rw [hS4, Function.update_self])
  -- 6. `m` (parked only)
  have e5 : S5 csSrc = natSyms m ++ Sym.mark :: (hdrSyms [j₀, D, nS, ρ] ++ hrest) := by
    rw [hS5, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, hdrSyms_cons_append]
  obtain ⟨S6, hS6⟩ : ∃ S', S' = Function.update (Function.update S5 csSrc
      (hdrSyms [j₀, D, nS, ρ] ++ hrest)) csPK (hdrSyms [P, d, r, w, K, m]).reverse := ⟨_, rfl⟩
  have r6 : Runs (parkField csSrc csPK) S5 S6 (fun _ => True) (3 * bitLen m + 3) := by
    rw [hS6]
    exact runs_parkField' (by decide) m [P, d, r, w, K] _ S5 e5 (by rw [hS5, Function.update_self])
  -- 7. `j₀`
  have e6 : S6 csSrc = natSyms j₀ ++ Sym.mark :: (hdrSyms [D, nS, ρ] ++ hrest) := by
    rw [hS6, Function.update_of_ne (by decide), Function.update_self, hdrSyms_cons_append]
  obtain ⟨S7, hS7⟩ : ∃ S', S' = Function.update (Function.update (Function.update S6 csSrc
      (hdrSyms [D, nS, ρ] ++ hrest)) csFj (natSyms j₀).reverse) csPK
      (hdrSyms [P, d, r, w, K, m, j₀]).reverse := ⟨_, rfl⟩
  have r7 : Runs (unpackField csSrc csFj csPK) S6 S7 (fun _ => True) (4 * bitLen j₀ + 3) := by
    rw [hS7]
    exact runs_unpackField' (by decide) (by decide) (by decide) j₀ [P, d, r, w, K, m] _ S6 e6
      (by simp +decide only [hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply, if_false, hcl])
      (by rw [hS6, Function.update_self])
  -- 8. `D`
  have e7 : S7 csSrc = natSyms D ++ Sym.mark :: (hdrSyms [nS, ρ] ++ hrest) := by
    rw [hS7, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, hdrSyms_cons_append]
  obtain ⟨S8, hS8⟩ : ∃ S', S' = Function.update (Function.update (Function.update S7 csSrc
      (hdrSyms [nS, ρ] ++ hrest)) csFD (natSyms D).reverse) csPK
      (hdrSyms [P, d, r, w, K, m, j₀, D]).reverse := ⟨_, rfl⟩
  have r8 : Runs (unpackField csSrc csFD csPK) S7 S8 (fun _ => True) (4 * bitLen D + 3) := by
    rw [hS8]
    exact runs_unpackField' (by decide) (by decide) (by decide) D [P, d, r, w, K, m, j₀] _ S7 e7
      (by simp +decide only [hS7, hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply, if_false, hcl])
      (by rw [hS7, Function.update_self])
  -- 9. `nS`
  have e8 : S8 csSrc = natSyms nS ++ Sym.mark :: (hdrSyms [ρ] ++ hrest) := by
    rw [hS8, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, hdrSyms_cons_append]
  obtain ⟨S9, hS9⟩ : ∃ S', S' = Function.update (Function.update (Function.update S8 csSrc
      (hdrSyms [ρ] ++ hrest)) csFn (natSyms nS).reverse) csPK
      (hdrSyms [P, d, r, w, K, m, j₀, D, nS]).reverse := ⟨_, rfl⟩
  have r9 : Runs (unpackField csSrc csFn csPK) S8 S9 (fun _ => True) (4 * bitLen nS + 3) := by
    rw [hS9]
    exact runs_unpackField' (by decide) (by decide) (by decide) nS [P, d, r, w, K, m, j₀, D] _
      S8 e8
      (by simp +decide only [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply, if_false, hcl])
      (by rw [hS8, Function.update_self])
  -- 10. `ρ`
  have e9 : S9 csSrc = natSyms ρ ++ Sym.mark :: (hdrSyms [] ++ hrest) := by
    rw [hS9, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, hdrSyms_cons_append]
  obtain ⟨S10, hS10⟩ : ∃ S', S' = Function.update (Function.update (Function.update S9 csSrc
      (hdrSyms [] ++ hrest)) csFq (natSyms ρ).reverse) csPK
      (hdrSyms [P, d, r, w, K, m, j₀, D, nS, ρ]).reverse := ⟨_, rfl⟩
  have r10 : Runs (unpackField csSrc csFq csPK) S9 S10 (fun _ => True) (4 * bitLen ρ + 3) := by
    rw [hS10]
    exact runs_unpackField' (by decide) (by decide) (by decide) ρ [P, d, r, w, K, m, j₀, D, nS] _
      S9 e9
      (by simp +decide only [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply, if_false,
        hcl])
      (by rw [hS9, Function.update_self])
  -- 11. restore the header
  have r11 := runs_xfer' (src := csPK) (dst := csSrc) (by decide) S10
    (hdrSyms [P, d, r, w, K, m, j₀, D, nS, ρ]).reverse (hdrSyms [] ++ hrest)
    (by rw [hS10, Function.update_self])
    (by rw [hS10, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self])
  have hall := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6
    (WP.W9comp.runs_seq r7 (WP.W9comp.runs_seq r8 (WP.W9comp.runs_seq r9
    (WP.W9comp.runs_seq r10 r11)))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · -- the final stacks
    funext k
    rcases k with i | e
    · fin_cases i
      · simp +decide only [restoredSt, Function.update_apply, if_true, if_false,
          List.reverse_reverse, hdrSyms_nil', List.nil_append]
        exact h0.symm
      · simp +decide only [restoredSt, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1,
          Function.update_apply, if_false]
    · fin_cases e <;>
        simp +decide only [restoredSt, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1,
          Function.update_apply, if_true, if_false, hcl]
  · -- the cost
    simp only [List.length_reverse, sliceHdr, length_hdrSyms, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega

/-! ## Phase 2: build the layer header -/

/-- **Phase 2**: from `restoredSt` to the input stacks with `(layerRT …).hdr` pushed onto `1`. -/
theorem runs_hdrBuild (S : HL → List Sym) (hcl : ∀ e, S (.inr e) = []) (P d r w K j₀ D nS ρ : ℕ) :
    Runs hdrBuildProg (restoredSt S P d r w K j₀ D nS ρ)
      (Function.update S csDst ((layerRT P d r w K j₀ D nS ρ).hdr ++ S csDst)) (fun _ => True)
      (50 * (bitLen P + bitLen d + bitLen r + bitLen w + bitLen K + bitLen j₀ + bitLen D +
        bitLen nS + bitLen ρ + 10) + 36 * (j₀ + nS)) := by
  obtain ⟨T0, hT0⟩ : ∃ T, T = restoredSt S P d r w K j₀ D nS ρ := ⟨_, rfl⟩
  rw [← hT0]
  obtain ⟨H1, hH1⟩ : ∃ L : List Sym, L = natSyms w ++ Sym.mark :: S csDst := ⟨_, rfl⟩
  obtain ⟨H3, hH3⟩ : ∃ L : List Sym, L = natSyms (ρ + 1) ++ Sym.mark :: H1 := ⟨_, rfl⟩
  obtain ⟨H4, hH4⟩ : ∃ L : List Sym, L = natSyms K ++ Sym.mark :: H3 := ⟨_, rfl⟩
  obtain ⟨H5, hH5⟩ : ∃ L : List Sym, L = natSyms (2 ^ nS) ++ Sym.mark :: H4 := ⟨_, rfl⟩
  obtain ⟨H6, hH6⟩ : ∃ L : List Sym, L = natSyms (2 ^ j₀) ++ Sym.mark :: H5 := ⟨_, rfl⟩
  obtain ⟨H7, hH7⟩ : ∃ L : List Sym, L = natSyms D ++ Sym.mark :: H6 := ⟨_, rfl⟩
  obtain ⟨H8, hH8⟩ : ∃ L : List Sym, L = natSyms r ++ Sym.mark :: H7 := ⟨_, rfl⟩
  obtain ⟨H9, hH9⟩ : ∃ L : List Sym, L = natSyms d ++ Sym.mark :: H8 := ⟨_, rfl⟩
  obtain ⟨H10, hH10⟩ : ∃ L : List Sym, L = natSyms P ++ Sym.mark :: H9 := ⟨_, rfl⟩
  -- 1. `w`
  obtain ⟨T1, hT1⟩ : ∃ T, T = Function.update (Function.update T0 csFw []) csDst H1 := ⟨_, rfl⟩
  have r1 : Runs (pushFieldRev csFw csDst) T0 T1 (fun _ => True) (3 * bitLen w + 3) := by
    rw [hT1, hH1]
    exact runs_pushFieldRev' (by decide) w T0
      (by simp +decide only [hT0, restoredSt, Function.update_apply, if_true, if_false]) (S csDst)
      (by simp +decide only [hT0, restoredSt, Function.update_apply, if_false])
  -- 2. `ρ`
  obtain ⟨T2, hT2⟩ : ∃ T, T = Function.update (Function.update T1 csFq []) csDst
      (natSyms ρ ++ Sym.mark :: H1) := ⟨_, rfl⟩
  have r2 : Runs (pushFieldRev csFq csDst) T1 T2 (fun _ => True) (3 * bitLen ρ + 3) := by
    rw [hT2]
    exact runs_pushFieldRev' (by decide) ρ T1
      (by simp +decide only [hT1, hT0, restoredSt, Function.update_apply, if_true, if_false]) H1
      (by rw [hT1, Function.update_self])
  -- 3. `ρ + 1`
  obtain ⟨T3, hT3⟩ : ∃ T, T = Function.update T2 csDst H3 := ⟨_, rfl⟩
  have r3 : Runs (inc csDst csT) T2 T3 (fun _ => True) (6 * bitLen ρ + 9) := by
    rw [hT3, hH3]
    exact runs_inc (by decide) ρ (Sym.mark :: H1) T2 (TermOK.cons rfl _)
      (by rw [hT2, Function.update_self])
  -- 4. `K`
  obtain ⟨T4, hT4⟩ : ∃ T, T = Function.update (Function.update T3 csFK []) csDst H4 := ⟨_, rfl⟩
  have r4 : Runs (pushFieldRev csFK csDst) T3 T4 (fun _ => True) (3 * bitLen K + 3) := by
    rw [hT4, hH4]
    exact runs_pushFieldRev' (by decide) K T3
      (by simp +decide only [hT3, hT2, hT1, hT0, restoredSt, Function.update_apply, if_true, if_false]) H3
      (by rw [hT3, Function.update_self])
  -- 5. `2^{nS}`
  obtain ⟨T5, hT5⟩ : ∃ T, T = Function.update (Function.update T4 csFn []) csDst H5 := ⟨_, rfl⟩
  have r5 : Runs (pow2Field csFn csDst csC csPK csKc csU csT) T4 T5 (fun _ => True)
      (36 * (nS + bitLen nS + 1)) := by
    rw [hT5, hH5]
    exact runs_pow2Field (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) nS T4
      (by simp +decide only [hT4, hT3, hT2, hT1, hT0, restoredSt, Function.update_apply, if_true, if_false])
      (by simp +decide only [hT4, hT3, hT2, hT1, hT0, restoredSt, Function.update_apply, if_false, hcl])
      (by simp +decide only [hT4, hT3, hT2, hT1, hT0, restoredSt, Function.update_apply, if_false, hcl])
      H4 (by rw [hT4, Function.update_self])
  -- 6. `2^{j₀}`
  obtain ⟨T6, hT6⟩ : ∃ T, T = Function.update (Function.update T5 csFj []) csDst H6 := ⟨_, rfl⟩
  have r6 : Runs (pow2Field csFj csDst csC csPK csKc csU csT) T5 T6 (fun _ => True)
      (36 * (j₀ + bitLen j₀ + 1)) := by
    rw [hT6, hH6]
    exact runs_pow2Field (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) j₀ T5
      (by simp +decide only [hT5, hT4, hT3, hT2, hT1, hT0, restoredSt, Function.update_apply, if_true, if_false])
      (by simp +decide only [hT5, hT4, hT3, hT2, hT1, hT0, restoredSt, Function.update_apply, if_false, hcl])
      (by simp +decide only [hT5, hT4, hT3, hT2, hT1, hT0, restoredSt, Function.update_apply, if_false, hcl])
      H5 (by rw [hT5, Function.update_self])
  -- 7. `D`
  obtain ⟨T7, hT7⟩ : ∃ T, T = Function.update (Function.update T6 csFD []) csDst H7 := ⟨_, rfl⟩
  have r7 : Runs (pushFieldRev csFD csDst) T6 T7 (fun _ => True) (3 * bitLen D + 3) := by
    rw [hT7, hH7]
    exact runs_pushFieldRev' (by decide) D T6
      (by simp +decide only [hT6, hT5, hT4, hT3, hT2, hT1, hT0, restoredSt,
        Function.update_apply, if_true, if_false]) H6
      (by rw [hT6, Function.update_self])
  -- 8. `r`
  obtain ⟨T8, hT8⟩ : ∃ T, T = Function.update (Function.update T7 csFr []) csDst H8 := ⟨_, rfl⟩
  have r8 : Runs (pushFieldRev csFr csDst) T7 T8 (fun _ => True) (3 * bitLen r + 3) := by
    rw [hT8, hH8]
    exact runs_pushFieldRev' (by decide) r T7
      (by simp +decide only [hT7, hT6, hT5, hT4, hT3, hT2, hT1, hT0, restoredSt,
        Function.update_apply, if_true, if_false]) H7
      (by rw [hT7, Function.update_self])
  -- 9. `d`
  obtain ⟨T9, hT9⟩ : ∃ T, T = Function.update (Function.update T8 csFd []) csDst H9 := ⟨_, rfl⟩
  have r9 : Runs (pushFieldRev csFd csDst) T8 T9 (fun _ => True) (3 * bitLen d + 3) := by
    rw [hT9, hH9]
    exact runs_pushFieldRev' (by decide) d T8
      (by simp +decide only [hT8, hT7, hT6, hT5, hT4, hT3, hT2, hT1, hT0, restoredSt,
        Function.update_apply, if_true, if_false]) H8
      (by rw [hT8, Function.update_self])
  -- 10. `P`
  obtain ⟨T10, hT10⟩ : ∃ T, T = Function.update (Function.update T9 csFP []) csDst H10 :=
    ⟨_, rfl⟩
  have r10 : Runs (pushFieldRev csFP csDst) T9 T10 (fun _ => True) (3 * bitLen P + 3) := by
    rw [hT10, hH10]
    exact runs_pushFieldRev' (by decide) P T9
      (by simp +decide only [hT9, hT8, hT7, hT6, hT5, hT4, hT3, hT2, hT1, hT0, restoredSt,
        Function.update_apply, if_true, if_false]) H9
      (by rw [hT9, Function.update_self])
  have hall := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 (WP.W9comp.runs_seq r6
    (WP.W9comp.runs_seq r7 (WP.W9comp.runs_seq r8 (WP.W9comp.runs_seq r9 r10))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · -- the final stacks
    have hH : H10 = (layerRT P d r w K j₀ D nS ρ).hdr ++ S csDst := by
      rw [hH10, hH9, hH8, hH7, hH6, hH5, hH4, hH3, hH1]
      simp [LayerRT.hdr, layerRT, hdrSyms]
    funext k
    rcases k with i | e
    · fin_cases i
      · simp +decide only [hT10, hT9, hT8, hT7, hT6, hT5, hT4, hT3, hT2, hT1, hT0, restoredSt,
          Function.update_apply, if_false]
      · simp +decide only [hT10, Function.update_apply, if_true, if_false, hH]
    · fin_cases e <;>
        simp +decide only [hT10, hT9, hT8, hT7, hT6, hT5, hT4, hT3, hT2, hT1, hT0, restoredSt,
          Function.update_apply, if_true, if_false, hcl]
  · -- the cost
    omega

end SubNLogN.Machine.WalshCubeAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine.WalshCubeAux

/-- **K3.0a holds** (`CubeHdrStmt`, `Machine/Walsh/CubeLayer.lean`): the program `cubeHdrProg`
reads the slice header `[P, d, r, w, K, m, j₀, D, nS, ρ]` (restored) and pushes the layer header
`[P, d, r, D, 2^{j₀}, 2^{nS}, K, ρ + 1, w]` (Proposition A.11, `prop:prop14-param`), within
`60((w + m + 1) + |sliceHdr|)` steps (`J = 1`, `C = 60`), for every slice shape
`j₀ + DK + nS = m`. -/
theorem cubeHdr_holds : CubeHdrStmt := by
  refine ⟨1, 60, fun _ => ⟨Fin 14, inferInstance, inferInstance, Option Sym, cubeHdrProg,
    inferInstance, ⟨none⟩, closed_cubeHdrProg, ?_⟩⟩
  intro P d r w K m j₀ D nS ρ hrest S hcl hm h0
  have hcl' : ∀ e, S (.inr e) = [] := hcl
  have hU := runs_hdrUnpack S hcl' P d r w K m j₀ D nS ρ hrest h0
  have hB := runs_hdrBuild S hcl' P d r w K j₀ D nS ρ
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq hU hB) (fun _ _ => trivial) ?_
  have hl : (sliceHdr P d r w K m j₀ D nS ρ).length = (bitLen P + 1) + ((bitLen d + 1) +
      ((bitLen r + 1) + ((bitLen w + 1) + ((bitLen K + 1) + ((bitLen m + 1) + ((bitLen j₀ + 1) +
      ((bitLen D + 1) + ((bitLen nS + 1) + ((bitLen ρ + 1) + 0))))))))) := by
    simp only [sliceHdr, length_hdrSyms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hjn : j₀ + nS ≤ m := by omega
  rw [hl, pow_one]
  omega

/-- **K3.0 from the layer machine alone** (Proposition A.11 (`prop:prop14-param`), on the slice
shapes of Definition 5.6 (`def:walsh-positional`)): `cubeLayer_of_layer` with the proved header
builder `cubeHdr_holds`. There is no other hypothesis. -/
theorem cubeLayer_of_layerMachine {Band : LayerRT → Prop} {lam' : ℝ}
    (hL : LayerMachineGenStmt Band (layerCost lam')) : CubeLayerStmt Band lam' :=
  cubeLayer_of_layer hL cubeHdr_holds

end SubNLogN.Machine
