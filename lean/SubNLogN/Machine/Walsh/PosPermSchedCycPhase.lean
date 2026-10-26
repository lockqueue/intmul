/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedDefs

/-!
# Schedule compiler, part 8 (`Machine/Walsh/PosPermSchedCycPhase.lean`): the cycle phase

`cycPhase_of (ha : CycBaseStmt) (hb : CycIdxLenStmt) (hc : CycPushStmt) : CycPhaseStmt`.
The phase runs the three per-point programs for `x = m-1, …, 0` (counted loop on `xc`), so the
pushed entries leave `I0T = utab (finVals (invol0 π))` and `I1T = utab (finVals (invol1 π))` with
entry `0` on top. The identification with Lemma 5.7's definitions is `cycleBase_val`,
`cycleIdx_eq`, `cycleLen_eq'`, `invol0_val`, `invol1_val` (`PosPermSchedCycMath.lean`).

**Scope (honest summary).** Proves `cycPhase_of` (a reduction) and frame lemmas for `ScrClean`.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Walsh

/-! ## `ScrClean` frame lemmas -/

theorem scrClean_mono {S : Stk → List Sym} {k1 k2 : List RegN} (h : ScrClean S k1)
    (hsub : ∀ q ∈ k1, q ∈ k2) : ScrClean S k2 :=
  ⟨fun q hq => h.1 q (fun h1 => hq (hsub q h1)), h.2⟩

theorem scrClean_upd_reg {S : Stk → List Sym} {keep : List RegN} (h : ScrClean S keep)
    (q : RegN) (hq : q ∈ keep) (v : List Sym) : ScrClean (Function.update S (rg q) v) keep := by
  refine ⟨fun r hr => ?_, ?_⟩
  · have hrq : r ≠ q := fun e => hr (e ▸ hq)
    rw [Function.update_of_ne (by simpa using hrq)]
    exact h.1 r hr
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rw [Function.update_of_ne (by simp)]; assumption)

theorem scrClean_upd_nil {S : Stk → List Sym} {keep : List RegN} (h : ScrClean S keep)
    (q : RegN) : ScrClean (Function.update S (rg q) []) keep := by
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases hrq : r = q
    · subst hrq; exact Function.update_self _ _ _
    · rw [Function.update_of_ne (by simpa using hrq)]
      exact h.1 r hr
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rw [Function.update_of_ne (by simp)]; assumption)

theorem scrClean_upd_table {S : Stk → List Sym} {keep : List RegN} (h : ScrClean S keep)
    (w : RawN) (hw : w = .I0T ∨ w = .I1T) (v : List Sym) :
    ScrClean (Function.update S (rs w) v) keep := by
  refine ⟨fun r hr => ?_, ?_⟩
  · rw [Function.update_of_ne (by simp)]
    exact h.1 r hr
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.2
    rcases hw with rfl | rfl <;>
      (refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [Function.update_of_ne (by simp)]; assumption))

theorem findAcc_le (P : ℕ → Bool) (i : ℕ) : findAcc P i ≤ i := by
  unfold findAcc
  cases h : (List.range i).find? P with
  | none => exact Nat.zero_le _
  | some k =>
    have := List.mem_of_find?_eq_some h
    simp at this
    simp
    omega

theorem findAcc_lt (P : ℕ → Bool) (i : ℕ) (hi : 0 < i) : findAcc P i < i := by
  unfold findAcc
  cases h : (List.range i).find? P with
  | none => simpa using hi
  | some k =>
    have := List.mem_of_find?_eq_some h
    simp at this
    simpa using this

/-! ## The program -/

/-- The loop body for the point `x = xc` (the counter value). -/
def cycBody (Pa Pb Pc : SProg Stk) : SProg Stk :=
  .seq (copyU (rg .xc) (rg .x) (rg .tmp)) (.seq Pa (.seq Pb (.seq Pc
    (.seq (clearU (rg .b)) (.seq (clearU (rg .idx)) (.seq (clearU (rg .len))
      (clearU (rg .x))))))))

/-- The cycle phase: `x = m-1, …, 0`. -/
def cycProg (Pa Pb Pc : SProg Stk) : SProg Stk :=
  .seq (copyU (rg .m) (rg .xc) (rg .tmp)) (forDown (rg .xc) (cycBody Pa Pb Pc))

theorem table_step (L : List ℕ) (c : ℕ) (hc : c < L.length) :
    ent L[c] ++ utab (L.drop (c + 1)) = utab (L.drop c) := by
  rw [List.drop_eq_getElem_cons hc, utab_cons, ent]
  simp

theorem invol0_entry {m : ℕ} (π : Fin m → Fin m) (c : ℕ) (hc : c < m) :
    (finVals (invol0 π))[c]'(by rw [length_finVals]; exact hc) =
      (piN π)^[(findAcc (fun j => decide ((piN π)^[j] (piN π (baseAcc π c m)) =
        baseAcc π c m)) m + 1 - findAcc (fun j => decide ((piN π)^[j] (baseAcc π c m) = c)) m) %
        (findAcc (fun j => decide ((piN π)^[j] (piN π (baseAcc π c m)) = baseAcc π c m)) m + 1)]
        (baseAcc π c m) := by
  rw [getElem_finVals, invol0_val, cycleLen_eq', cycleIdx_eq, cycleBase_val]

theorem invol1_entry {m : ℕ} (π : Fin m → Fin m) (c : ℕ) (hc : c < m) :
    (finVals (invol1 π))[c]'(by rw [length_finVals]; exact hc) =
      (piN π)^[(findAcc (fun j => decide ((piN π)^[j] (piN π (baseAcc π c m)) =
        baseAcc π c m)) m + 1 + 1 -
        findAcc (fun j => decide ((piN π)^[j] (baseAcc π c m) = c)) m) %
        (findAcc (fun j => decide ((piN π)^[j] (piN π (baseAcc π c m)) = baseAcc π c m)) m + 1)]
        (baseAcc π c m) := by
  rw [getElem_finVals, invol1_val, cycleLen_eq', cycleIdx_eq, cycleBase_val]

theorem pow_mono_aux (m a b : ℕ) (h : a ≤ b) : (m + 1) ^ a ≤ (m + 1) ^ b :=
  Nat.pow_le_pow_right (Nat.succ_pos m) h

/-! ## The reduction -/

theorem cycPhase_of (ha : CycBaseStmt) (hb : CycIdxLenStmt) (hc : CycPushStmt) :
    CycPhaseStmt := by
  obtain ⟨Pa, hPa, Ca, ka, hA⟩ := ha
  obtain ⟨Pb, hPb, Cb, kb, hB⟩ := hb
  obtain ⟨Pc, hPc, Cc, kc, hC⟩ := hc
  refine ⟨cycProg Pa Pb Pc, ?_, Ca + Cb + Cc + 60, ka + kb + kc + 2, ?_⟩
  · simp only [Prog.Closed] at hPa hPb hPc
    simp [Prog.Closed, Prog.FreeBelow, cycProg, cycBody, copyU, forDown, whileNE, whileTop,
      clearU, incR, popR, peekR, pushC, hPa, hPb, hPc]
  intro m π S hPT hm hI0 hI1 hcl
  set L0 := finVals (invol0 π) with hL0
  set L1 := finVals (invol1 π) with hL1
  have hl0 : L0.length = m := length_finVals _
  have hl1 : L1.length = m := length_finVals _
  have hreg : ∀ q : RegN, q ≠ .m → q ≠ .d → q ≠ .K → S (rg q) = [] := fun q h1 h2 h3 =>
    hcl.1 q (by simp [h1, h2, h3])
  set P := (m + 1) ^ (ka + kb + kc + 1) with hP
  have hPa' : (m + 1) ^ ka ≤ P := pow_mono_aux m _ _ (by omega)
  have hPb' : (m + 1) ^ kb ≤ P := pow_mono_aux m _ _ (by omega)
  have hPc' : (m + 1) ^ kc ≤ P := pow_mono_aux m _ _ (by omega)
  have hP1 : m + 1 ≤ P := by
    have := pow_mono_aux m 1 (ka + kb + kc + 1) (by omega)
    simpa using this
  set Tb := (Ca + Cb + Cc + 30) * P with hTb
  let F : ℕ → Stk → List Sym := fun i => Function.update (Function.update S (rs .I0T)
    (utab (L0.drop (m - i)))) (rs .I1T) (utab (L1.drop (m - i)))
  have hF : ∀ i, F i = Function.update (Function.update S (rs .I0T)
      (utab (L0.drop (m - i)))) (rs .I1T) (utab (L1.drop (m - i))) := fun _ => rfl
  have hloop := runs_forDown (c := rg .xc) (p := cycBody Pa Pb Pc) F Tb m (fun i hi => by
    set c := m - 1 - i with hcdef
    have hcm : c < m := by omega
    set S0 := Function.update (F i) (rg .xc) (una c) with hS0
    have hcl0 : ScrClean S0 [.m, .xc, .x, .d, .K] :=
      scrClean_upd_reg (scrClean_upd_table (scrClean_upd_table (scrClean_mono hcl (by decide))
        .I0T (Or.inl rfl) _) .I1T (Or.inr rfl) _) .xc (by simp) _
    -- step 1: x := c
    have c1 := runs_copyU (src := rg .xc) (dst := rg .x) (tmp := rg .tmp) (by decide) (by decide)
      (by decide) S0 c 0 (by simp [hS0]) (by simp [hS0, hF, Function.update_apply, hreg])
      (by simp [hS0, hF, Function.update_apply, hreg])
    rw [Nat.zero_add] at c1
    set S1 := Function.update S0 (rg .x) (una c) with hS1
    have hcl1 : ScrClean S1 [.m, .xc, .x, .d, .K] := scrClean_upd_reg hcl0 .x (by simp) _
    -- step 2: b := base
    set bb := baseAcc π c m with hbb
    have hbbm : bb < m := baseAcc_lt π c m hcm
    have c2 := hA m π c S1 hcm (by simp [hS1, hS0, hF, Function.update_apply, hPT])
      (by simp [hS1, hS0, hF, Function.update_apply, hm]) (by simp [hS1]) hcl1
    set S2 := Function.update S1 (rg .b) (una bb) with hS2
    have hcl2 : ScrClean S2 [.m, .xc, .x, .b, .d, .K] :=
      scrClean_upd_reg (scrClean_mono hcl1 (by decide)) .b (by simp) _
    -- step 3: idx, len
    set I := findAcc (fun j => decide ((piN π)^[j] bb = c)) m with hI
    set N := findAcc (fun j => decide ((piN π)^[j] (piN π bb) = bb)) m + 1 with hN
    have hIm : I < m := findAcc_lt _ m (by omega)
    have hNm : N ≤ m := by have := findAcc_lt (fun j => decide ((piN π)^[j] (piN π bb) = bb)) m
                              (by omega); omega
    have c3 := hB m π c bb S2 hcm hbbm (by simp [hS2, hS1, hS0, hF, Function.update_apply, hPT])
      (by simp [hS2, hS1, hS0, hF, Function.update_apply, hm]) (by simp [hS2, hS1])
      (by simp [hS2]) hcl2
    set S3 := Function.update (Function.update S2 (rg .idx) (una I)) (rg .len) (una N) with hS3
    have hcl3 : ScrClean S3 [.m, .xc, .x, .b, .idx, .len, .d, .K] :=
      scrClean_upd_reg (scrClean_upd_reg (scrClean_mono hcl2 (by decide)) .idx (by simp) _) .len
        (by simp) _
    -- step 4: push
    have c4 := hC m π bb I N S3 hbbm (by omega) hNm hIm.le
      (by simp [hS3, hS2, hS1, hS0, hF, Function.update_apply, hPT])
      (by simp [hS3, hS2, hS1, hS0, hF, Function.update_apply, hm]) (by simp [hS3, hS2])
      (by simp [hS3]) (by simp [hS3]) hcl3
    have hT0 : S3 (rs .I0T) = utab (L0.drop (m - i)) := by
      simp [hS3, hS2, hS1, hS0, hF, Function.update_apply]
    have hT1 : S3 (rs .I1T) = utab (L1.drop (m - i)) := by
      simp [hS3, hS2, hS1, hS0, hF, Function.update_apply]
    rw [hT0, hT1] at c4
    set S4 := Function.update (Function.update S3 (rs .I0T) (ent ((piN π)^[(N - I) % N] bb) ++
      utab (L0.drop (m - i)))) (rs .I1T) (ent ((piN π)^[(N + 1 - I) % N] bb) ++
      utab (L1.drop (m - i))) with hS4
    -- steps 5-8: clears
    have d1 := runs_clearU (rg .b) S4 bb (by simp [hS4, hS3, hS2])
    have d2 := runs_clearU (rg .idx) (Function.update S4 (rg .b) []) I (by simp [hS4, hS3])
    have d3 := runs_clearU (rg .len) (Function.update (Function.update S4 (rg .b) []) (rg .idx) [])
      N (by simp [hS4, hS3])
    have d4 := runs_clearU (rg .x) (Function.update (Function.update (Function.update S4 (rg .b)
      []) (rg .idx) []) (rg .len) []) c (by simp [hS4, hS3, hS2, hS1])
    have e0 : ent ((piN π)^[(N - I) % N] bb) ++ utab (L0.drop (m - i)) =
        utab (L0.drop (m - (i + 1))) := by
      have h1 := table_step L0 c (by omega)
      have h2 : c + 1 = m - i := by omega
      have h3 : m - (i + 1) = c := by omega
      rw [h2] at h1
      rw [h3, ← h1]
      congr 2
      exact (invol0_entry π c hcm).symm
    have e1 : ent ((piN π)^[(N + 1 - I) % N] bb) ++ utab (L1.drop (m - i)) =
        utab (L1.drop (m - (i + 1))) := by
      have h1 := table_step L1 c (by omega)
      have h2 : c + 1 = m - i := by omega
      have h3 : m - (i + 1) = c := by omega
      rw [h2] at h1
      rw [h3, ← h1]
      congr 2
      exact (invol1_entry π c hcm).symm
    refine runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_seq' c4 (runs_seq' d1 (runs_seq' d2
      (runs_seq' d3 (runs_weak d4 ?_ le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) ?_
    · rw [hF, e0.symm, e1.symm]
      funext k
      rcases k with j | w | q
      · simp [hS4, hS3, hS2, hS1, hS0, hF, Function.update_apply]
      · cases w <;> simp [hS4, hS3, hS2, hS1, hS0, hF, Function.update_apply]
      · cases q <;> simp [hS4, hS3, hS2, hS1, hS0, hF, Function.update_apply, hreg]
    · have h1 : Ca * (m + 1) ^ ka ≤ Ca * P := Nat.mul_le_mul_left _ hPa'
      have h2 : Cb * (m + 1) ^ kb ≤ Cb * P := Nat.mul_le_mul_left _ hPb'
      have h3 : Cc * (m + 1) ^ kc ≤ Cc * P := Nat.mul_le_mul_left _ hPc'
      have h4 : (Ca + Cb + Cc + 30) * P = Ca * P + Cb * P + Cc * P + 30 * P := by ring
      omega)
  -- assemble
  have c0 := runs_copyU (src := rg .m) (dst := rg .xc) (tmp := rg .tmp) (by decide) (by decide)
    (by decide) S m 0 hm (by rw [hreg .xc (by decide) (by decide) (by decide)]; rfl)
    (hreg .tmp (by decide) (by decide) (by decide))
  have eF0 : Function.update (F 0) (rg .xc) (una m) = Function.update S (rg .xc) (una (0 + m)) := by
    have hd0 : L0.drop m = [] := by rw [List.drop_eq_nil_iff]; omega
    have hd1 : L1.drop m = [] := by rw [List.drop_eq_nil_iff]; omega
    rw [hF, Nat.sub_zero, hd0, hd1, utab_nil, Nat.zero_add]
    funext k
    rcases k with j | w | q
    · simp [Function.update_apply]
    · cases w <;> simp [Function.update_apply, hI0, hI1]
    · cases q <;> simp [Function.update_apply]
  have eFm : Function.update (F m) (rg .xc) [] = Function.update (Function.update S (rs .I0T)
      (utab L0)) (rs .I1T) (utab L1) := by
    rw [hF, Nat.sub_self, List.drop_zero, List.drop_zero]
    funext k
    rcases k with j | w | q
    · simp [Function.update_apply]
    · cases w <;> simp [Function.update_apply]
    · cases q <;> simp [Function.update_apply, hreg]
  rw [eF0, eFm] at hloop
  refine runs_seq' c0 hloop ?_
  have h4 : (Ca + Cb + Cc + 60) * (m + 1) ^ (ka + kb + kc + 2) =
      (Ca + Cb + Cc + 60) * P * (m + 1) := by
    rw [hP]; ring
  have h5 : m * (Tb + 3) ≤ (m + 1) * Tb + 3 * m := by
    have : m * (Tb + 3) = m * Tb + 3 * m := by ring
    have : m * Tb ≤ (m + 1) * Tb := Nat.mul_le_mul_right _ (by omega)
    omega
  have h6 : (m + 1) * Tb + 30 * (m + 1) ≤ (Ca + Cb + Cc + 60) * P * (m + 1) := by
    have : (Ca + Cb + Cc + 60) * P * (m + 1) = (m + 1) * Tb + (m + 1) * (30 * P) := by
      rw [hTb]; ring
    have : 30 * (m + 1) ≤ (m + 1) * (30 * P) := by
      have h30 : 30 ≤ 30 * P := Nat.le_mul_of_pos_right 30 (by omega)
      calc 30 * (m + 1) = (m + 1) * 30 := by ring
        _ ≤ (m + 1) * (30 * P) := Nat.mul_le_mul_left _ h30
    omega
  omega

end SubNLogN.Machine.Walsh.PosPermSchedAux
