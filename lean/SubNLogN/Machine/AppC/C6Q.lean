/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6QLeaves
import SubNLogN.Machine.AppC.C6Eq

/-!
# Lemma A.8 level C (`Machine/AppC/C6Q.lean`): the radix-`q` interchange of `e` digits

**Theorem** (`c6Q_of_parts`, fully proved): for `q ≥ 2`, `C6SmallTestStmt`, `C6SmallStmt q`,
`C6HighJoinStmt q`, `C6LowStmt q τ` and `C6UnjoinStmt q` give `C6QStmt q τ`
(Lemma A.8 (`lem:transfer12`), radix-`q` chunks). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Program** (`progC`) on `KLoc (Fin 5) (Et ⊕ Es ⊕ Eh ⊕ El ⊕ Eu)`: test `e ≤ 34`; if so the
small-width kernel (`e` digit-pair swaps); otherwise the high join, the low interchange across
the row field `[q^{2t}]` and the undo of the join.

**Correctness**: `hj_low_uj_identity` (`C6QLeaves.lean`) with `q^e = q^t·q^{e-t}` (`c6T_lt`).

**Cost**: the high/undo steps cost `O(V·(t+1))` and `t + 1 ≤ 35·e^τ` (`c6T_succ_le_rpow`);
`C = C_test + C_small + 35·C_hj + C_low + 35·C_uj + 1`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Machine.Calculus

namespace AppC.C6Aux

/-! ## The composite layout of level C -/

/-- Scratch of level C: test, small kernel, high join, low interchange, undo join. -/
abbrev EC (Et Es Eh El Eu : Type) : Type := Et ⊕ (Es ⊕ (Eh ⊕ (El ⊕ Eu)))

/-- Registers of level C. -/
abbrev RC (Rt Rs Rh Rl Ru : Type) : Type := Rt × (Rs × (Rh × (Rl × Ru)))

def ιCT (Et Es Eh El Eu : Type) : KLoc (Fin 1) Et → KLoc (Fin 5) (EC Et Es Eh El Eu) :=
  Sum.map (![1] : Fin 1 → Fin 5) Sum.inl

def ιCS (Et Es Eh El Eu : Type) : KLoc (Fin 5) Es → KLoc (Fin 5) (EC Et Es Eh El Eu) :=
  Sum.map id fun e => Sum.inr (Sum.inl e)

def ιCH (Et Es Eh El Eu : Type) : KLoc (Fin 5) Eh → KLoc (Fin 5) (EC Et Es Eh El Eu) :=
  Sum.map id fun e => Sum.inr (Sum.inr (Sum.inl e))

def ιCL (Et Es Eh El Eu : Type) : KLoc (Fin 5) El → KLoc (Fin 5) (EC Et Es Eh El Eu) :=
  Sum.map id fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))

def ιCU (Et Es Eh El Eu : Type) : KLoc (Fin 5) Eu → KLoc (Fin 5) (EC Et Es Eh El Eu) :=
  Sum.map id fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))

theorem ιCT_inj (Et Es Eh El Eu : Type) : Function.Injective (ιCT Et Es Eh El Eu) :=
  Sum.map_injective.2 ⟨by decide, Sum.inl_injective⟩

theorem ιCS_inj (Et Es Eh El Eu : Type) : Function.Injective (ιCS Et Es Eh El Eu) :=
  Sum.map_injective.2 ⟨Function.injective_id, fun a b h => by simpa using h⟩

theorem ιCH_inj (Et Es Eh El Eu : Type) : Function.Injective (ιCH Et Es Eh El Eu) :=
  Sum.map_injective.2 ⟨Function.injective_id, fun a b h => by simpa using h⟩

theorem ιCL_inj (Et Es Eh El Eu : Type) : Function.Injective (ιCL Et Es Eh El Eu) :=
  Sum.map_injective.2 ⟨Function.injective_id, fun a b h => by simpa using h⟩

theorem ιCU_inj (Et Es Eh El Eu : Type) : Function.Injective (ιCU Et Es Eh El Eu) :=
  Sum.map_injective.2 ⟨Function.injective_id, fun a b h => by simpa using h⟩

def lCT (Rt Rs Rh Rl Ru : Type) : Lens (RC Rt Rs Rh Rl Ru) Rt := Lens.fst _ _

def lCS (Rt Rs Rh Rl Ru : Type) : Lens (RC Rt Rs Rh Rl Ru) Rs :=
  (Lens.snd _ _).comp (Lens.fst _ _)

def lCH (Rt Rs Rh Rl Ru : Type) : Lens (RC Rt Rs Rh Rl Ru) Rh :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))

def lCL (Rt Rs Rh Rl Ru : Type) : Lens (RC Rt Rs Rh Rl Ru) Rl :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))

def lCU (Rt Rs Rh Rl Ru : Type) : Lens (RC Rt Rs Rh Rl Ru) Ru :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _)))

/-- **The level-C program**: test `e ≤ 34`; small kernel, or high join; low; undo join. -/
def progC {K σ : Type} (test small hj low uj : Prog K (fun _ => Sym) σ) (isSmall : σ → Bool) :
    Prog K (fun _ => Sym) σ :=
  .seq test (.ite isSmall small (.seq hj (.seq low uj)))

theorem closed_progC {K σ : Type} {test small hj low uj : Prog K (fun _ => Sym) σ}
    {isSmall : σ → Bool} (ht : test.Closed) (hs : small.Closed) (hh : hj.Closed)
    (hl : low.Closed) (hu : uj.Closed) : (progC test small hj low uj isSmall).Closed :=
  ⟨ht, hs, hh, hl, hu⟩

section Branches

variable {K σ : Type} [DecidableEq K] {test small hj low uj : Prog K (fun _ => Sym) σ}
  {isSmall : σ → Bool}

theorem runs_progC_small {S S' : K → List Sym} {Tt Ts : ℕ}
    (ht : Runs test S S (fun v => isSmall v = true) Tt) (hs : Runs small S S' (fun _ => True) Ts) :
    Runs (progC test small hj low uj isSmall) S S' (fun _ => True) (Tt + (Ts + 1)) :=
  RunsIn.iff_runs.1 (RunsIn.ite_true (RunsIn.iff_runs.2 ht) (RunsIn.iff_runs.2 hs))

theorem runs_progC_big {S S1 S2 S3 : K → List Sym} {Tt Th Tl Tu : ℕ}
    (ht : Runs test S S (fun v => isSmall v = false) Tt) (hh : Runs hj S S1 (fun _ => True) Th)
    (hl : Runs low S1 S2 (fun _ => True) Tl) (hu : Runs uj S2 S3 (fun _ => True) Tu) :
    Runs (progC test small hj low uj isSmall) S S3 (fun _ => True) (Tt + ((Th + (Tl + Tu)) + 1)) :=
  RunsIn.iff_runs.1 (RunsIn.ite_false (RunsIn.iff_runs.2 ht)
    (RunsIn.iff_runs.2 (runs_seq hh (runs_seq hl hu))))

end Branches

/-- The level-C costs fit `C·(X + 1)`, `C = Ct + Cs + 35·Ch + Clo + 35·Cu + 1`. -/
theorem costC_fit {Ct Cs Ch Clo Cu Tt Ts Th Tlo Tu X : ℕ} (hTt : Tt ≤ Ct * (X + 1))
    (hTs : Ts ≤ Cs * (X + 1)) (hTh : Th ≤ Ch * (35 * X + 1)) (hTlo : Tlo ≤ Clo * (X + 1))
    (hTu : Tu ≤ Cu * (35 * X + 1)) :
    Tt + (Ts + 1) ≤ (Ct + Cs + 35 * Ch + Clo + 35 * Cu + 1) * (X + 1) ∧
      Tt + ((Th + (Tlo + Tu)) + 1) ≤ (Ct + Cs + 35 * Ch + Clo + 35 * Cu + 1) * (X + 1) := by
  have h1 : Ch * (35 * X + 1) ≤ 35 * (Ch * (X + 1)) := by nlinarith
  have h2 : Cu * (35 * X + 1) ≤ 35 * (Cu * (X + 1)) := by nlinarith
  have e : (Ct + Cs + 35 * Ch + Clo + 35 * Cu + 1) * (X + 1) = Ct * (X + 1) + Cs * (X + 1) +
      35 * (Ch * (X + 1)) + Clo * (X + 1) + 35 * (Cu * (X + 1)) + (X + 1) := by ring
  refine ⟨by omega, by omega⟩

end AppC.C6Aux

open AppC.C6Aux in
/-- **Lemma A.8 level C** (Lemma A.8 (`lem:transfer12`), radix-`q` chunks): for `q ≥ 2`,
the small-width test and kernel, the high join, the low interchange and the undo of the join give
the radix-`q` interchange `C6QStmt q τ`. -/
theorem c6Q_of_parts {q : ℕ} {τ : ℝ} (hq : 2 ≤ q) (hT : C6SmallTestStmt) (hSm : C6SmallStmt q)
    (hHJ : C6HighJoinStmt q) (hLo : C6LowStmt q τ) (hUJ : C6UnjoinStmt q) : C6QStmt q τ := by
  intro hτ
  have hτ0 : 0 < τ := tau_pos hτ
  obtain ⟨Clo, hLo⟩ := hLo hτ
  obtain ⟨Ct, hT⟩ := hT
  obtain ⟨Cs, hSm⟩ := hSm
  obtain ⟨Ch, hHJ⟩ := hHJ
  obtain ⟨Cu, hUJ⟩ := hUJ
  obtain ⟨Et, _, _, Rt, Pt, hRt1, hRt2, hPt, obs, hsT⟩ := hT ()
  obtain ⟨Es, _, _, Rs, Ps, hRs1, hRs2, hPs, hsS⟩ := hSm ()
  obtain ⟨Eh, _, _, Rh, Ph, hRh1, hRh2, hPh, hsH⟩ := hHJ ()
  obtain ⟨El, _, _, Rl, Pl, hRl1, hRl2, hPl, hsL⟩ := hLo ()
  obtain ⟨Eu, _, _, Ru, Pu, hRu1, hRu2, hPu, hsU⟩ := hUJ ()
  have := hRt1; have := hRt2; have := hRs1; have := hRs2; have := hRh1; have := hRh2
  have := hRl1; have := hRl2; have := hRu1; have := hRu2
  refine ⟨Ct + Cs + 35 * Ch + Clo + 35 * Cu + 1, fun _ => ⟨EC Et Es Eh El Eu, inferInstance,
    inferInstance, RC Rt Rs Rh Rl Ru,
    progC (callInj (ιCT Et Es Eh El Eu) (lCT Rt Rs Rh Rl Ru) Pt)
      (callInj (ιCS Et Es Eh El Eu) (lCS Rt Rs Rh Rl Ru) Ps)
      (callInj (ιCH Et Es Eh El Eu) (lCH Rt Rs Rh Rl Ru) Ph)
      (callInj (ιCL Et Es Eh El Eu) (lCL Rt Rs Rh Rl Ru) Pl)
      (callInj (ιCU Et Es Eh El Eu) (lCU Rt Rs Rh Rl Ru) Pu) (fun x => obs x.1),
    inferInstance, inferInstance,
    closed_progC (closed_callInj _ _ hPt) (closed_callInj _ _ hPs) (closed_callInj _ _ hPh)
      (closed_callInj _ _ hPl) (closed_callInj _ _ hPu), ?_⟩⟩
  intro A e G B w v rest r1 r2 r3 r4 S he hA hG hB hlen hw hrest hr1 hr2 hr3 hr4 hS0 hS1 hS2 hS3
    hS4
  have hV : vol v = v.length * (w + 1) := vol_eq_of_width hw
  have hlenV : v.length ≤ vol v := by
    rw [hV]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos w)
  have hqe : e < q ^ e := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hq e)
  have hlen_ge : q ^ e ≤ v.length := by
    rw [hlen]
    calc q ^ e = 1 * q ^ e * 1 * 1 * 1 := by ring
      _ ≤ A * q ^ e * G * q ^ e * B := by
        gcongr
        exact Nat.one_le_pow _ _ (by omega)
  have hbl : bitLen e ≤ e := TMFw.W3s.bitLen_le_of_lt Nat.lt_two_pow_self
  have hX : vol v ≤ ⌈(vol v : ℝ) * (e : ℝ) ^ τ⌉₊ := le_ceil_pow hτ0 he
  have hTt : Ct * (bitLen e + 1) ≤ Ct * (⌈(vol v : ℝ) * (e : ℝ) ^ τ⌉₊ + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have htest := runs_callInj_reg (ιCT_inj Et Es Eh El Eu) (lCT Rt Rs Rh Rl Ru)
    (hsT e r1 (S ∘ ιCT Et Es Eh El Eu) hr1 hS1) (fun _ _ => rfl)
  rcases Nat.lt_or_ge e 35 with h34 | h35
  · -- small widths: `e` digit-pair swaps
    have ht : Runs (callInj (ιCT Et Es Eh El Eu) (lCT Rt Rs Rh Rl Ru) Pt) S S
        (fun x => obs x.1 = true) (Ct * (bitLen e + 1)) :=
      runs_mono htest (fun x hx => by
        have hx' : obs x.1 = decide (e ≤ 34) := hx
        rw [hx']; exact decide_eq_true (by omega)) le_rfl
    have hs := runs_callInj_upd1 (ιCS_inj Et Es Eh El Eu) (lCS Rt Rs Rh Rl Ru) S (.inl 0) _
      (hsS A e G B w v rest r1 r2 r3 r4 (S ∘ ιCS Et Es Eh El Eu) he (by omega) hA hG hB hlen hw
        hrest hr1 hr2 hr3 hr4 hS0 hS1 hS2 hS3 hS4)
    have hfit := (costC_fit (Cs := Cs) (Ch := Ch) (Clo := Clo) (Cu := Cu)
      (Ts := Cs * (vol v + 1)) (Th := 0) (Tlo := 0) (Tu := 0) hTt
      (Nat.mul_le_mul_left Cs (by omega : vol v + 1 ≤ ⌈(vol v : ℝ) * (e : ℝ) ^ τ⌉₊ + 1))
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)).1
    exact runs_mono (runs_progC_small ht hs) (fun _ _ => trivial) hfit
  · -- large widths: high join, low interchange, undo join
    obtain ⟨ht1, htl⟩ := c6T_lt hq h35
    have hqe' : q ^ e = q ^ c6T q e * q ^ (e - c6T q e) := by
      rw [← pow_add, Nat.add_sub_cancel' htl.le]
    have hlenT : v.length = A * q ^ c6T q e * q ^ (e - c6T q e) * G * q ^ c6T q e *
        q ^ (e - c6T q e) * B := by rw [hlen, hqe']; ring
    have ht : Runs (callInj (ιCT Et Es Eh El Eu) (lCT Rt Rs Rh Rl Ru) Pt) S S
        (fun x => obs x.1 = false) (Ct * (bitLen e + 1)) :=
      runs_mono htest (fun x hx => by
        have hx' : obs x.1 = decide (e ≤ 34) := hx
        rw [hx']; exact decide_eq_false (by omega)) le_rfl
    -- the high join
    have hrgH : ∀ y < v.length,
        c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B y < v.length := by
      intro y hy
      have hy' : y < A * q ^ c6T q e * q ^ c6T q e * q ^ (e - c6T q e) * G *
          q ^ (e - c6T q e) * B := by rw [hlenT] at hy; linarith
      calc c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B y < A * q ^ c6T q e *
            q ^ (e - c6T q e) * G * q ^ c6T q e * q ^ (e - c6T q e) * B := c6HJInv_lt hy'
        _ = v.length := hlenT.symm
    have hh := runs_callInj_upd1 (ιCH_inj Et Es Eh El Eu) (lCH Rt Rs Rh Rl Ru) S (.inl 0) _
      (hsH A e G B w v rest r1 r2 r3 r4 (S ∘ ιCH Et Es Eh El Eu) h35 hA hG hB hlen hw
        hrest hr1 hr2 hr3 hr4 hS0 hS1 hS2 hS3 hS4)
    have hlen₁ : (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v).length =
        A * q ^ (2 * c6T q e) * q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B := by
      rw [length_permByInv, hlenT, two_mul, pow_add]; ring
    have hw₁ : ∀ p ∈ permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v,
        p.length = w := fun p hp => hw p (mem_permByInv hrgH hp)
    have hvol₁ : vol (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v) = vol v := by
      rw [vol_eq_of_width hw₁, hV, length_permByInv]
    -- the low interchange
    have hrgL : ∀ y < v.length,
        swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B y < v.length := by
      intro y hy
      have e1 : v.length = A * q ^ c6T q e * q ^ c6T q e * q ^ (e - c6T q e) * G *
          q ^ (e - c6T q e) * B := by rw [hlenT]; ring
      rw [e1] at hy ⊢
      exact swapFieldsInv_lt hy
    have hLk := hsL A e G B w (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v)
      rest r1 r2 r3 r4
      (Function.update S (.inl 0) (arrSyms (permByInv (c6HJInv (q ^ c6T q e)
        (q ^ (e - c6T q e)) G B) v) ++ rest) ∘ ιCL Et Es Eh El Eu)
      h35 hA hG hB hlen₁ hw₁ hrest hr1 hr2 hr3 hr4 (Function.update_self _ _ _)
      (by show Function.update S (Sum.inl 0) _ (Sum.inl 1) = _
          rw [Function.update_of_ne (by simp)]; exact hS1)
      (by show Function.update S (Sum.inl 0) _ (Sum.inl 2) = _
          rw [Function.update_of_ne (by simp)]; exact hS2)
      (by show Function.update S (Sum.inl 0) _ (Sum.inl 3) = _
          rw [Function.update_of_ne (by simp)]; exact hS3)
      (by show Function.update S (Sum.inl 0) _ (Sum.inl 4) = _
          rw [Function.update_of_ne (by simp)]; exact hS4)
    have hl := runs_callInj_upd1 (ιCL_inj Et Es Eh El Eu) (lCL Rt Rs Rh Rl Ru) _ (.inl 0) _ hLk
    have hrgL₁ : ∀ y < (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v).length,
        swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B y <
          (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v).length := by
      rw [length_permByInv]; exact hrgL
    have hlen₂ : (permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
        (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v)).length =
        A * q ^ c6T q e * q ^ c6T q e * q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B := by
      rw [length_permByInv, length_permByInv, hlenT]; ring
    have hw₂ : ∀ p ∈ permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
        (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v), p.length = w :=
      fun p hp => hw₁ p (mem_permByInv hrgL₁ hp)
    have hvol₂ : vol (permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
        (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v)) = vol v := by
      rw [vol_eq_of_width hw₂, hV, length_permByInv, length_permByInv]
    -- undo the join
    have hUk := hsU A e G B w (permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
        (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v)) rest r1 r2 r3 r4
      (Function.update (Function.update S (.inl 0) (arrSyms (permByInv (c6HJInv (q ^ c6T q e)
        (q ^ (e - c6T q e)) G B) v) ++ rest)) (.inl 0)
        (arrSyms (permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
          (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v)) ++ rest) ∘
        ιCU Et Es Eh El Eu)
      h35 hA hG hB hlen₂ hw₂ hrest hr1 hr2 hr3 hr4 (Function.update_self _ _ _)
      (by show Function.update (Function.update S (Sum.inl 0) _) (Sum.inl 0) _ (Sum.inl 1) = _
          rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact hS1)
      (by show Function.update (Function.update S (Sum.inl 0) _) (Sum.inl 0) _ (Sum.inl 2) = _
          rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact hS2)
      (by show Function.update (Function.update S (Sum.inl 0) _) (Sum.inl 0) _ (Sum.inl 3) = _
          rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact hS3)
      (by show Function.update (Function.update S (Sum.inl 0) _) (Sum.inl 0) _ (Sum.inl 4) = _
          rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact hS4)
    have hu := runs_callInj_upd1 (ιCU_inj Et Es Eh El Eu) (lCU Rt Rs Rh Rl Ru) _ (.inl 0) _ hUk
    -- the functional identity
    have hrgU : ∀ y < v.length,
        c6UJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B y < v.length := by
      intro y hy
      rw [hlenT] at hy
      calc c6UJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B y < A * q ^ c6T q e * q ^ c6T q e *
            q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B := c6UJInv_lt hy
        _ = v.length := by rw [hlenT]; ring
    have hfun : permByInv (c6UJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B)
        (permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
          (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v)) =
        permByInv (swapFieldsInv (q ^ e) G (q ^ e) B) v := by
      rw [permByInv_comp _ _ v hrgL, permByInv_comp _ _ v hrgU]
      apply permByInv_congr
      intro y hy
      rw [hqe']
      apply hj_low_uj_identity
      rw [hlenT] at hy
      exact hy
    -- the cost
    have hVt : vol v * (c6T q e + 1) ≤ 35 * ⌈(vol v : ℝ) * (e : ℝ) ^ τ⌉₊ := by
      have h1 := c6T_succ_le_rpow hq hτ (by omega : 1 ≤ e)
      have h2 : ((vol v * (c6T q e + 1) : ℕ) : ℝ) ≤ 35 * ((vol v : ℝ) * (e : ℝ) ^ τ) := by
        have h3 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) (vol v))
        push_cast at h3 ⊢
        linarith
      have h4 : 35 * ((vol v : ℝ) * (e : ℝ) ^ τ) ≤
          ((35 * ⌈(vol v : ℝ) * (e : ℝ) ^ τ⌉₊ : ℕ) : ℝ) := by
        push_cast
        exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)
      exact_mod_cast h2.trans h4
    have hfit := (costC_fit (Cs := Cs) (Ts := 0) hTt (Nat.zero_le _)
      (Th := Ch * (vol v * (c6T q e + 1) + 1)) (Nat.mul_le_mul_left _ (by omega))
      (Tlo := Clo * (⌈(vol (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v) : ℝ) *
        (e : ℝ) ^ τ⌉₊ + 1)) (by rw [hvol₁])
      (Tu := Cu * (vol (permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
        (permByInv (c6HJInv (q ^ c6T q e) (q ^ (e - c6T q e)) G B) v)) * (c6T q e + 1) + 1))
      (by rw [hvol₂]; exact Nat.mul_le_mul_left _ (by omega))).2
    refine runs_congr (runs_progC_big ht hh hl hu) ?_ hfit
    show Function.update (Function.update (Function.update S (.inl 0) _) (.inl 0) _) (.inl 0) _ = _
    rw [Function.update_idem, Function.update_idem, hfun]

end SubNLogN.Machine
