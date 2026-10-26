/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanIdx
import SubNLogN.Machine.Walsh.CnotScanUV

/-!
# `SubNLogN.Machine.Walsh.CnotScanSelPhaseK`: the unit routine of the scan `S_U`

Paper: Section 5.1 eq. (`eq:walsh-SU`) (`S_U` multiplies the record at `x` by
`i^{∑_{j ∈ U} x_j}`) and Lemma 5.1 (`lem:walsh-select`: `U = Sel ∖ T`, applied in one scan as a fourth-root
phase).

## Plan
`kRsp`: `k := 0`; walk the index `x` (LSB first, `Walsh/CnotScanIdx.lean`) and the `U`-vector
`uv` (K3-LIFT's `uvSyms`, aligned with `x`) in parallel, `k := k + 1` for every position where
both bits are set, parking the bits on `x2` and `tmp`; then drain both back. All stacks are
restored. Cost `12m + 7`.

**Scope (honest summary).** `kRsp` and `kRSpec_kRsp` (the engine's `KRSpec`), no `sorry`.
Helpers live in `SubNLogN.Machine.WalshScanSP`.
-/

namespace SubNLogN.Machine.WalshScanSP

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine WalshLift
  SubNLogN.Machine.WalshScanAux SubNLogN.Machine.WalshScanX

/-! ## Programs -/

/-- `k := k + 1` if the bits in `t` and `s` are both set. -/
def addPh : EProg SK :=
  .load fun r => { r with k := if optBit r.t && optBit r.s then r.k + 1 else r.k }

/-- One step: pop the next `uv` bit into `s`, count, park both bits, pop the next index bit. -/
def spStep : EProg SK :=
  .seq (popS (.inr .uv)) (.seq addPh (.seq (pushT (.inr .x2)) (.seq (pushS (.inr .tmp))
    (popT (.inr .x)))))

/-- The unit routine of the scan `S_U`. -/
def kRsp : EProg SK :=
  .seq (.load fun r => { r with k := 0 }) (.seq (popT (.inr .x)) (.seq (.loop tSome spStep)
    (.seq ((drain (.inr .x2) (.inr .x)).liftRegs lT) ((drain (.inr .tmp) (.inr .uv)).liftRegs lT))))

theorem closed_kRsp : kRsp.Closed := by
  have hd : ∀ a b : SK, ((drain a b).liftRegs lT).FreeBelow 0 :=
    fun a b => WP.W9comp.closed_liftRegs lT (closed_drain a b)
  simp [Prog.Closed, Prog.FreeBelow, kRsp, spStep, addPh, popT, popS, pushT, pushS, hd]

/-! ## The parallel walk -/

/-- The number of positions where both lists have a set bit. -/
def spCount : List Bool → List Bool → ℕ
  | b :: bs, u :: us => (if b && u then 1 else 0) + spCount bs us
  | _, _ => 0

theorem spLoop_eval : ∀ (bs us : List Bool) (X2 TMP : List Sym) (r : ER) (S : SK → List Sym),
    bs.length = us.length → r.t = (bs.map Sym.bit).head? →
    S (.inr .x) = (bs.map Sym.bit).tail → S (.inr .uv) = us.map Sym.bit →
    S (.inr .x2) = X2 → S (.inr .tmp) = TMP →
    ∃ r' : ER, Eval [] (.loop tSome spStep) ⟨r, S⟩
      ⟨r', Function.update (Function.update (Function.update (Function.update S
        (.inr .x) []) (.inr .uv) []) (.inr .x2) (bs.reverse.map Sym.bit ++ X2))
        (.inr .tmp) (us.reverse.map Sym.bit ++ TMP)⟩ (6 * bs.length + 1) ∧
      r'.k = r.k + fin4 (spCount bs us) ∧ r'.mu = r.mu
  | [], [], X2, TMP, r, S, _, ht, hx, huv, hx2, htmp => by
    have ht' : r.t = none := ht
    have hx' : S (.inr .x) = [] := hx
    have huv' : S (.inr .uv) = [] := huv
    refine ⟨r, (Eval.loop_false (by simp [tSome, ht'])).of_eq ?_ rfl,
      (add_fin4_zero r.k).symm, rfl⟩
    congr 1
    funext j
    simp only [Function.update_apply, List.reverse_nil, List.map_nil, List.nil_append]
    split_ifs <;> simp_all
  | [], _ :: _, _, _, _, _, h, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _, _, _, _, _ => by simp at h
  | b :: bs, u :: us, X2, TMP, r, S, hlen, ht, hx, huv, hx2, htmp => by
    have ht' : r.t = some (Sym.bit b) := ht
    have hx' : S (.inr .x) = bs.map Sym.bit := hx
    have huv' : S (.inr .uv) = Sym.bit u :: us.map Sym.bit := huv
    have e1 := eval_popS (.inr .uv) r (Sym.bit u :: us.map Sym.bit) S huv'
    set S1 := Function.update S (.inr .uv) (Sym.bit u :: us.map Sym.bit).tail with hS1
    set r1 : ER := { r with s := (Sym.bit u :: us.map Sym.bit).head? } with hr1
    set r2 : ER := { r1 with k := if b && u then r.k + 1 else r.k } with hr2
    have e2 : Eval [] addPh ⟨r1, S1⟩ ⟨r2, S1⟩ 1 := by
      refine (Eval.load [] (fun r : ER =>
        { r with k := if optBit r.t && optBit r.s then r.k + 1 else r.k }) r1 S1).of_eq ?_ rfl
      simp [hr2, hr1, ht']
    have e3 := eval_pushT (.inr .x2) r2 (Sym.bit b) (by simp [hr2, hr1, ht']) S1
    set S3 := Function.update S1 (.inr .x2) (Sym.bit b :: S1 (.inr .x2)) with hS3
    have e4 := eval_pushS (.inr .tmp) r2 (Sym.bit u) (by simp [hr2, hr1]) S3
    set S4 := Function.update S3 (.inr .tmp) (Sym.bit u :: S3 (.inr .tmp)) with hS4
    have e5 := eval_popT (.inr .x) r2 (bs.map Sym.bit) S4 (by simp [hS4, hS3, hS1, hx'])
    obtain ⟨r', e6, hk6, hmu6⟩ := spLoop_eval bs us (Sym.bit b :: X2) (Sym.bit u :: TMP)
      { r2 with t := (bs.map Sym.bit).head? }
      (Function.update S4 (.inr .x) (bs.map Sym.bit).tail) (by simpa using hlen) rfl
      (Function.update_self _ _ _) (by simp [hS4, hS3, hS1]) (by simp [hS4, hS3, hS1, hx2])
      (by simp [hS4, hS3, hS1, htmp])
    refine ⟨r', (Eval.loop_true (by simp [tSome, ht']) (Eval.seq e1 (Eval.seq e2 (Eval.seq e3
      (Eval.seq e4 e5)))) e6).of_eq ?_ (by simp only [List.length_cons]; omega), ?_, ?_⟩
    · clear e1 e2 e3 e4 e5 e6
      congr 1
      funext j
      by_cases h1 : j = .inr .x2
      · subst h1
        simp
      · by_cases h2 : j = .inr .tmp
        · subst h2
          simp
        · by_cases h3 : j = .inr .x
          · subst h3
            simp
          · by_cases h4 : j = .inr .uv
            · subst h4
              simp
            · simp [hS4, hS3, hS1, Function.update_of_ne h1, Function.update_of_ne h2,
                Function.update_of_ne h3, Function.update_of_ne h4]
    · rw [hk6]
      have h1 : (1 : Fin 4).val = 1 := rfl
      apply Fin.ext
      simp only [hr2, spCount, Fin.val_add, val_fin4]
      by_cases hbu : (b && u) = true
      · rw [if_pos hbu, if_pos hbu, Fin.val_add, h1]
        omega
      · rw [if_neg hbu, if_neg hbu]
        omega
    · rw [hmu6]

/-! ## The unit routine -/

/-- The `U`-vector as bits (position `m - 1` first, aligned with the index). -/
def uvBits (m : ℕ) (U : Finset (Fin m)) : List Bool :=
  (List.finRange m).reverse.map fun p => decide (p ∈ U)

theorem uvSyms_eq (m : ℕ) (U : Finset (Fin m)) : uvSyms m U = (uvBits m U).map Sym.bit := rfl

theorem length_uvBits (m : ℕ) (U : Finset (Fin m)) : (uvBits m U).length = m := by
  simp [uvBits]

/-- The unit exponent of record `i`: the number of positions of `U` set in its address,
mod `4`. -/
def spKfun (m : ℕ) (U : Finset (Fin m)) (i : ℕ) : Fin 4 :=
  fin4 (spCount (bitsLE m i) (uvBits m U))

/-- Static data of the scan `S_U` (not the array, the output buffer or the index). -/
def spStat (m : ℕ) (U : Finset (Fin m)) (S : SK → List Sym) : Prop :=
  S (.inr .uv) = uvSyms m U ∧ S (.inr .x2) = [] ∧ S (.inr .tmp) = []

theorem statFrame_spStat (m : ℕ) (U : Finset (Fin m)) : StatFrame (spStat m U) := by
  intro S S' hS ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_⟩ <;> rw [hS _ (by simp) (by simp) (by simp)] <;> assumption

theorem kRSpec_kRsp (m : ℕ) (U : Finset (Fin m)) :
    KRSpec kRsp (spKfun m U) (idxSyms m) (spStat m U) (12 * m + 7) := by
  intro i S r hx hst
  obtain ⟨huv, hx2, htmp⟩ := hst
  have e1 := Eval.load [] (fun r : ER => { r with k := 0 }) r S
  have e2 := eval_popT (.inr .x) { r with k := 0 } (idxSyms m i) S hx
  obtain ⟨r3, e3, hk3, hmu3⟩ := spLoop_eval (bitsLE m i) (uvBits m U) [] []
    { { r with k := 0 } with t := (idxSyms m i).head? }
    (Function.update S (.inr .x) (idxSyms m i).tail)
    (by simp [K1.length_bitsLE, length_uvBits]) rfl (Function.update_self _ _ _)
    (by simp [huv, uvSyms_eq]) (by simp [hx2]) (by simp [htmp])
  set S3 := Function.update (Function.update (Function.update (Function.update
    (Function.update S (.inr .x) (idxSyms m i).tail) (.inr .x) []) (.inr .uv) [])
    (.inr .x2) ((bitsLE m i).reverse.map Sym.bit ++ [])) (.inr .tmp)
    ((uvBits m U).reverse.map Sym.bit ++ []) with hS3
  have e4 := eval_drainE (src := (.inr .x2 : SK)) (dst := .inr .x) (by simp) r3
    ((bitsLE m i).reverse.map Sym.bit) S3 (by simp [hS3])
  set S4 := Function.update (Function.update S3 (.inr .x2) []) (.inr .x)
    (((bitsLE m i).reverse.map Sym.bit).reverse ++ S3 (.inr .x)) with hS4
  have e5 := eval_drainE (src := (.inr .tmp : SK)) (dst := .inr .uv) (by simp)
    { r3 with t := none } ((uvBits m U).reverse.map Sym.bit) S4 (by simp [hS4, hS3])
  refine ⟨{ { r3 with t := none } with t := none }, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3
    (Eval.seq e4 e5)))).of_eq ?_ rfl, ?_, ?_, ?_⟩
  · clear e1 e2 e3 e4 e5
    congr 1
    funext j
    by_cases h1 : j = .inr .x
    · subst h1
      simp [hS4, hS3, hx, idxSyms]
    · by_cases h2 : j = .inr .uv
      · subst h2
        simp [hS4, hS3, huv, uvSyms_eq]
      · by_cases h3 : j = .inr .x2
        · subst h3
          simp [hS4, hS3, hx2]
        · by_cases h4 : j = .inr .tmp
          · subst h4
            simp [hS4, hS3, htmp]
          · simp [hS4, hS3, Function.update_of_ne h1, Function.update_of_ne h2,
              Function.update_of_ne h3, Function.update_of_ne h4]
  · simp [hk3, spKfun]
  · simp [hmu3]
  · simp only [List.length_reverse, List.length_map, K1.length_bitsLE, length_uvBits]
    omega

end SubNLogN.Machine.WalshScanSP
