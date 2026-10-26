/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6LowLeaves

/-!
# Lemma A.8 level D (`Machine/AppC/C6Low.lean`): the low interchange across the row field

**Theorem** (`c6Low_of_parts`, fully proved): for `q ≥ 2`, `C6RowPadStmt q`, `C6PiecesStmt q τ` and
`C6RowUnpadStmt q` give `C6LowStmt q τ` (Lemma A.8 (`lem:transfer12`),
row-padded low-digit interchange). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Program** (`progD`): pad the row field `[R]` to `[R']`; the pieces; unpad.
**Correctness**: `row_unpad_swap_pad`. **Cost**: the padded volume is `< 2V` (`c6Rp_lt`), so the
total is `≤ 2·(C_pad + C_pieces + C_unpad)·(⌈V·e^τ⌉₊ + 1)`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Machine.Calculus

namespace AppC.C6Aux

/-- Scratch of level D: row padding, pieces, row unpadding. -/
abbrev ED (Ep Epc Eu : Type) : Type := Ep ⊕ (Epc ⊕ Eu)

/-- Registers of level D. -/
abbrev RD (Rp Rpc Ru : Type) : Type := Rp × (Rpc × Ru)

def ιDP (Ep Epc Eu : Type) : KLoc (Fin 5) Ep → KLoc (Fin 5) (ED Ep Epc Eu) := Sum.map id Sum.inl

def ιDC (Ep Epc Eu : Type) : KLoc (Fin 5) Epc → KLoc (Fin 5) (ED Ep Epc Eu) :=
  Sum.map id fun e => Sum.inr (Sum.inl e)

def ιDU (Ep Epc Eu : Type) : KLoc (Fin 5) Eu → KLoc (Fin 5) (ED Ep Epc Eu) :=
  Sum.map id fun e => Sum.inr (Sum.inr e)

theorem ιDP_inj (Ep Epc Eu : Type) : Function.Injective (ιDP Ep Epc Eu) :=
  Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩

theorem ιDC_inj (Ep Epc Eu : Type) : Function.Injective (ιDC Ep Epc Eu) :=
  Sum.map_injective.2 ⟨Function.injective_id, fun a b h => by simpa using h⟩

theorem ιDU_inj (Ep Epc Eu : Type) : Function.Injective (ιDU Ep Epc Eu) :=
  Sum.map_injective.2 ⟨Function.injective_id, fun a b h => by simpa using h⟩

def lDP (Rp Rpc Ru : Type) : Lens (RD Rp Rpc Ru) Rp := Lens.fst _ _

def lDC (Rp Rpc Ru : Type) : Lens (RD Rp Rpc Ru) Rpc := (Lens.snd _ _).comp (Lens.fst _ _)

def lDU (Rp Rpc Ru : Type) : Lens (RD Rp Rpc Ru) Ru := (Lens.snd _ _).comp (Lens.snd _ _)

/-- **The level-D program**: row padding; pieces; row unpadding. -/
def progD {K σ : Type} (pad pieces unpad : Prog K (fun _ => Sym) σ) : Prog K (fun _ => Sym) σ :=
  .seq pad (.seq pieces unpad)

theorem closed_progD {K σ : Type} {pad pieces unpad : Prog K (fun _ => Sym) σ}
    (hp : pad.Closed) (hc : pieces.Closed) (hu : unpad.Closed) :
    (progD pad pieces unpad).Closed :=
  ⟨hp, hc, hu⟩

theorem costD_fit {Cp Cpc Cu Tp Tpc Tu X : ℕ} (hTp : Tp ≤ Cp * (2 * X + 1))
    (hTpc : Tpc ≤ Cpc * (2 * X + 1)) (hTu : Tu ≤ Cu * (2 * X + 1)) :
    Tp + (Tpc + Tu) ≤ 2 * (Cp + Cpc + Cu) * (X + 1) := by
  have h1 : Cp * (2 * X + 1) ≤ 2 * (Cp * (X + 1)) := by nlinarith
  have h2 : Cpc * (2 * X + 1) ≤ 2 * (Cpc * (X + 1)) := by nlinarith
  have h3 : Cu * (2 * X + 1) ≤ 2 * (Cu * (X + 1)) := by nlinarith
  have e : 2 * (Cp + Cpc + Cu) * (X + 1) =
      2 * (Cp * (X + 1)) + 2 * (Cpc * (X + 1)) + 2 * (Cu * (X + 1)) := by ring
  omega

end AppC.C6Aux

open AppC.C6Aux in
/-- **Lemma A.8 level D** (Lemma A.8 (`lem:transfer12`)): the row padding, the pieces and the row
unpadding give the low interchange across the row field, `C6LowStmt q τ`. -/
theorem c6Low_of_parts {q : ℕ} {τ : ℝ} (hq : 2 ≤ q) (hP : C6RowPadStmt q)
    (hPc : C6PiecesStmt q τ) (hU : C6RowUnpadStmt q) : C6LowStmt q τ := by
  intro hτ
  have hτ0 : 0 < τ := tau_pos hτ
  obtain ⟨Cpc, hPc⟩ := hPc hτ
  obtain ⟨Cp, hP⟩ := hP
  obtain ⟨Cu, hU⟩ := hU
  obtain ⟨Ep, _, _, Rp, Pp, hRp1, hRp2, hPp, hsP⟩ := hP ()
  obtain ⟨Epc, _, _, Rpc, Ppc, hRc1, hRc2, hPpc, hsC⟩ := hPc ()
  obtain ⟨Eu, _, _, Ru, Pu, hRu1, hRu2, hPu, hsU⟩ := hU ()
  have := hRp1; have := hRp2; have := hRc1; have := hRc2; have := hRu1; have := hRu2
  refine ⟨2 * (Cp + Cpc + Cu), fun _ => ⟨ED Ep Epc Eu, inferInstance, inferInstance,
    RD Rp Rpc Ru, progD (callInj (ιDP Ep Epc Eu) (lDP Rp Rpc Ru) Pp)
      (callInj (ιDC Ep Epc Eu) (lDC Rp Rpc Ru) Ppc) (callInj (ιDU Ep Epc Eu) (lDU Rp Rpc Ru) Pu),
    inferInstance, inferInstance,
    closed_progD (closed_callInj _ _ hPp) (closed_callInj _ _ hPpc) (closed_callInj _ _ hPu), ?_⟩⟩
  intro A e G B w v rest r1 r2 r3 r4 S he hA hG hB hlen hw hrest hr1 hr2 hr3 hr4 hS0 hS1 hS2 hS3
    hS4
  have hR1 : 1 ≤ c6R q e := c6R_pos hq
  have hRR : c6R q e ≤ c6Rp q e := c6R_le_c6Rp q e
  have hRp : c6Rp q e < 2 * c6R q e := c6Rp_lt hq
  have hql : 1 ≤ q ^ (e - c6T q e) := Nat.one_le_pow _ _ (by omega)
  have hZ : 1 ≤ q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hql hG) hql) hB
    simpa using this
  have hlen' : v.length = A * c6R q e * (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) := by
    rw [hlen]; unfold c6R; ring
  have hposRZ : 0 < c6R q e * (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) := by positivity
  -- step 1: row padding
  have hp := runs_callInj_upd1 (ιDP_inj Ep Epc Eu) (lDP Rp Rpc Ru) S (.inl 0) _
    (hsP A e G B w v rest r1 r2 r3 r4 (S ∘ ιDP Ep Epc Eu) he hA hG hB hlen' hw hrest hr1 hr2 hr3
      hr4 hS0 hS1 hS2 hS3 hS4)
  have hlenp := length_c6RowPad (R' := c6Rp q e) (w := w) hposRZ hlen'
  have hwp := width_c6RowPad (R' := c6Rp q e) hR1 hZ hlen' hw
  have hlenp' : (c6RowPad (c6R q e) (c6Rp q e) (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w
      v).length = A * c6Rp q e * q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B := by
    rw [hlenp]; ring
  -- step 2: the pieces
  have hcK := hsC A e G B w
    (c6RowPad (c6R q e) (c6Rp q e) (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v)
    rest r1 r2 r3 r4
    (Function.update S (.inl 0) (arrSyms (c6RowPad (c6R q e) (c6Rp q e)
      (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v) ++ rest) ∘ ιDC Ep Epc Eu)
    he hA hG hB hlenp' hwp hrest hr1 hr2 hr3 hr4 (Function.update_self _ _ _)
    (by show Function.update S (Sum.inl 0) _ (Sum.inl 1) = _
        rw [Function.update_of_ne (by simp)]; exact hS1)
    (by show Function.update S (Sum.inl 0) _ (Sum.inl 2) = _
        rw [Function.update_of_ne (by simp)]; exact hS2)
    (by show Function.update S (Sum.inl 0) _ (Sum.inl 3) = _
        rw [Function.update_of_ne (by simp)]; exact hS3)
    (by show Function.update S (Sum.inl 0) _ (Sum.inl 4) = _
        rw [Function.update_of_ne (by simp)]; exact hS4)
  have hc := runs_callInj_upd1 (ιDC_inj Ep Epc Eu) (lDC Rp Rpc Ru) _ (.inl 0) _ hcK
  -- the swapped padded array
  have hrg : ∀ y < (c6RowPad (c6R q e) (c6Rp q e)
      (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v).length,
      swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B y <
        (c6RowPad (c6R q e) (c6Rp q e)
          (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v).length := by
    intro y hy
    rw [hlenp'] at hy ⊢
    exact swapFieldsInv_lt (A := A * c6Rp q e) hy
  have hlenq : (permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
      (c6RowPad (c6R q e) (c6Rp q e) (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v)).length =
      A * c6Rp q e * (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) := by
    rw [length_permByInv, hlenp]
  have hwq : ∀ p ∈ permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
      (c6RowPad (c6R q e) (c6Rp q e) (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v),
      p.length = w := fun p hp => hwp p (mem_permByInv hrg hp)
  have hvolq : vol (permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
      (c6RowPad (c6R q e) (c6Rp q e) (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v)) =
      vol (c6RowPad (c6R q e) (c6Rp q e) (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v) := by
    rw [vol_eq_of_width hwq, vol_eq_of_width hwp, length_permByInv]
  -- step 3: row unpadding
  have huK := hsU A e G B w
    (permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
      (c6RowPad (c6R q e) (c6Rp q e) (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v))
    rest r1 r2 r3 r4
    (Function.update (Function.update S (.inl 0) (arrSyms (c6RowPad (c6R q e) (c6Rp q e)
      (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v) ++ rest)) (.inl 0)
      (arrSyms (permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
        (c6RowPad (c6R q e) (c6Rp q e) (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v)) ++
        rest) ∘ ιDU Ep Epc Eu)
    he hA hG hB hlenq hwq hrest hr1 hr2 hr3 hr4 (Function.update_self _ _ _)
    (by show Function.update (Function.update S (Sum.inl 0) _) (Sum.inl 0) _ (Sum.inl 1) = _
        rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact hS1)
    (by show Function.update (Function.update S (Sum.inl 0) _) (Sum.inl 0) _ (Sum.inl 2) = _
        rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact hS2)
    (by show Function.update (Function.update S (Sum.inl 0) _) (Sum.inl 0) _ (Sum.inl 3) = _
        rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact hS3)
    (by show Function.update (Function.update S (Sum.inl 0) _) (Sum.inl 0) _ (Sum.inl 4) = _
        rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact hS4)
  have hu := runs_callInj_upd1 (ιDU_inj Ep Epc Eu) (lDU Rp Rpc Ru) _ (.inl 0) _ huK
  -- the functional identity and the cost
  have hfun := row_unpad_swap_pad (w := w) v hR1 hRR hZ hlen'
  have hX : vol v ≤ ⌈(vol v : ℝ) * (e : ℝ) ^ τ⌉₊ := le_ceil_pow hτ0 (by omega)
  have hVp : vol (c6RowPad (c6R q e) (c6Rp q e)
      (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v) ≤ 2 * vol v := by
    rw [vol_eq_of_width hwp, hlenp, vol_eq_of_width hw, hlen']
    have h1 : c6Rp q e ≤ 2 * c6R q e := hRp.le
    calc A * c6Rp q e * (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) * (w + 1)
        ≤ A * (2 * c6R q e) * (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) * (w + 1) := by
          gcongr
      _ = 2 * (A * c6R q e * (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) * (w + 1)) := by
          ring
  have hTpc : ⌈(vol (c6RowPad (c6R q e) (c6Rp q e)
      (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v) : ℝ) * (e : ℝ) ^ τ⌉₊ ≤
      2 * ⌈(vol v : ℝ) * (e : ℝ) ^ τ⌉₊ := by
    apply Nat.ceil_le.mpr
    have h1 : (vol (c6RowPad (c6R q e) (c6Rp q e)
        (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v) : ℝ) * (e : ℝ) ^ τ ≤
        ((2 * vol v : ℕ) : ℝ) * (e : ℝ) ^ τ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hVp) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have h2 : ((2 * vol v : ℕ) : ℝ) * (e : ℝ) ^ τ ≤
        ((2 * ⌈(vol v : ℝ) * (e : ℝ) ^ τ⌉₊ : ℕ) : ℝ) := by
      push_cast
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)
    exact h1.trans h2
  have hfit := costD_fit (Cp := Cp) (Cpc := Cpc) (Cu := Cu)
    (X := ⌈(vol v : ℝ) * (e : ℝ) ^ τ⌉₊)
    (Tp := Cp * (vol (c6RowPad (c6R q e) (c6Rp q e)
      (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v) + 1))
    (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left _ (Nat.succ_le_succ hTpc))
    (Tu := Cu * (vol (permByInv (swapFieldsInv (q ^ (e - c6T q e)) G (q ^ (e - c6T q e)) B)
      (c6RowPad (c6R q e) (c6Rp q e) (q ^ (e - c6T q e) * G * q ^ (e - c6T q e) * B) w v)) + 1))
    (by rw [hvolq]; exact Nat.mul_le_mul_left _ (by omega))
  refine runs_congr (runs_seq hp (runs_seq hc hu)) ?_ hfit
  show Function.update (Function.update (Function.update S (.inl 0) _) (.inl 0) _) (.inl 0) _ = _
  rw [Function.update_idem, Function.update_idem, hfun]

end SubNLogN.Machine
