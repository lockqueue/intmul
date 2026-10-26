/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6Leaves
import SubNLogN.Machine.Calculus.Basic
import Contracts.Machine.W3
import WP.W3s.Math

/-!
# Lemma A.8 level A (`Machine/AppC/C6Top.lean`): unequal widths from equal widths

**Theorem** (`c6Interchange_of_eq`, fully proved): `C6EqStmt τ`, `C6BitMoveStmt true` and
`C6BitMoveStmt false` give `C6InterchangeStmt τ` (Lemma A.8 (`lem:transfer12`),
equal and unequal widths). (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

**Program** (`progA`) on `KLoc (Fin 6) (Ee ⊕ Er ⊕ El ⊕ Fin mc)`: compare the counters `u1, u2`
(the proved `w3_cmpNat`) and branch.
* `u1 = u2`: one equal-width interchange.
* `u1 = u2 + 1` (`(h0, H, G, D) → (h0, D, G, H) → (D, G, h0, H)`): equal-width interchange with
  prefix `2A` and width `u2`, then move the bit `h0` right across `[2^u2] × [G]`.
* `u2 = u1 + 1` (`(H, G, d0, D) → (d0, H, G, D) → (d0, D, G, H)`): move `d0` left across
  `[2^u1] × [G]`, then the equal-width interchange with prefix `2A` and width `u1`.
The kernels read their counters directly from the named stacks of Lemma A.8; no counter is computed.

**Cost**: `C = 2·C_cmp + C_eq + C_right + C_left + 2`, using `0 < τ` (from the premise, since
`s_b ≥ W_b`), `bitLen u ≤ u`, `u1 + u2 + 1 ≤ 2^{u1+u2} ≤ V` and `u ≤ max u1 u2`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Machine.Calculus

namespace AppC.C6Aux

/-! ## Index arithmetic for the unequal-width branches -/

theorem add_mul_lt {x0 x1 A N : ℕ} (h0 : x0 < A) (h1 : x1 < N) : x0 * N + x1 < A * N :=
  calc x0 * N + x1 < x0 * N + N := by omega
    _ = (x0 + 1) * N := by ring
    _ ≤ A * N := Nat.mul_le_mul_right N h0

/-- Mixed-radix decomposition of an index into four coordinates. -/
theorem decomp3 {y A N1 N2 N3 : ℕ} (hy : y < A * N1 * N2 * N3) :
    ∃ a x1 x2 x3, a < A ∧ x1 < N1 ∧ x2 < N2 ∧ x3 < N3 ∧
      y = ((a * N1 + x1) * N2 + x2) * N3 + x3 := by
  have h3 : 0 < N3 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have h2 : 0 < N2 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have h1 : 0 < N1 := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  refine ⟨y / N3 / N2 / N1, y / N3 / N2 % N1, y / N3 % N2, y % N3,
    ?_, Nat.mod_lt _ h1, Nat.mod_lt _ h2, Nat.mod_lt _ h3, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul h1, Nat.div_lt_iff_lt_mul h2, Nat.div_lt_iff_lt_mul h3]
    exact hy
  · have e1 := Nat.div_add_mod' y N3
    have e2 := Nat.div_add_mod' (y / N3) N2
    have e3 := Nat.div_add_mod' (y / N3 / N2) N1
    rw [e3, e2, e1]

theorem swapFieldsInv_lt {A Hh G Hd B y : ℕ} (hy : y < A * Hd * G * Hh * B) :
    swapFieldsInv Hh G Hd B y < A * Hh * G * Hd * B := by
  obtain ⟨a, d, g, h, z, ha, hd, hg, hh, hz, rfl⟩ := decomp5 hy
  rw [swapFieldsInv_coord hd hg hh hz]
  exact add_mul_lt (add_mul_lt (add_mul_lt (add_mul_lt ha hh) hg) hd) hz

theorem moveRightMixInv_lt {q N0 N1 N2 y : ℕ} (hy : y < N0 * N1 * q * N2) :
    moveRightMixInv q N1 N2 y < N0 * q * N1 * N2 := by
  obtain ⟨a, x1, d, x2, ha, hx1, hd, hx2, rfl⟩ := decomp3 hy
  rw [moveRightMixInv_coord hx1 hd hx2]
  exact add_mul_lt (add_mul_lt (add_mul_lt ha hd) hx1) hx2

/-- **Branch `u1 = u2 + 1`.** Equal-width interchange (prefix `2A`) followed by the right bit
move is the `(n+1, n)` interchange. -/
theorem gt_identity {A G B n y : ℕ} (hy : y < A * 2 ^ n * G * (2 * 2 ^ n) * B) :
    swapFieldsInv (2 ^ n) G (2 ^ n) B (moveRightMixInv 2 (2 ^ n * G) (2 ^ n * B) y) =
      swapFieldsInv (2 * 2 ^ n) G (2 ^ n) B y := by
  have hNpos : 0 < 2 ^ n := by positivity
  obtain ⟨a, d, g, H, z, ha, hd, hg, hH, hz, hy'⟩ := decomp5 hy
  have hb : H / 2 ^ n < 2 := (Nat.div_lt_iff_lt_mul hNpos).2 (by linarith)
  have hh : H % 2 ^ n < 2 ^ n := Nat.mod_lt _ hNpos
  have hHe : H = H / 2 ^ n * 2 ^ n + H % 2 ^ n := (Nat.div_add_mod' H (2 ^ n)).symm
  have lhs : swapFieldsInv (2 ^ n) G (2 ^ n) B (moveRightMixInv 2 (2 ^ n * G) (2 ^ n * B) y) =
      ((((a * 2 + H / 2 ^ n) * 2 ^ n + H % 2 ^ n) * G + g) * 2 ^ n + d) * B + z := by
    have e1 : y = ((a * (2 ^ n * G) + (d * G + g)) * 2 + H / 2 ^ n) * (2 ^ n * B) +
        (H % 2 ^ n * B + z) := by
      rw [hy']
      nth_rewrite 1 [hHe]
      ring
    rw [e1, moveRightMixInv_coord (add_mul_lt hd hg) hb (add_mul_lt hh hz)]
    have e2 : ((a * 2 + H / 2 ^ n) * (2 ^ n * G) + (d * G + g)) * (2 ^ n * B) +
        (H % 2 ^ n * B + z) =
        ((((a * 2 + H / 2 ^ n) * 2 ^ n + d) * G + g) * 2 ^ n + H % 2 ^ n) * B + z := by ring
    rw [e2, swapFieldsInv_coord hd hg hh hz]
  have rhs : swapFieldsInv (2 * 2 ^ n) G (2 ^ n) B y =
      (((a * (2 * 2 ^ n) + H) * G + g) * 2 ^ n + d) * B + z := by
    rw [hy', swapFieldsInv_coord hd hg hH hz]
  rw [lhs, rhs]
  conv_rhs => rw [hHe]
  ring

/-- **Branch `u2 = u1 + 1`.** The left bit move followed by the equal-width interchange (prefix
`2A`) is the `(n, n+1)` interchange. -/
theorem lt_identity {A G B n y : ℕ} (hy : y < A * (2 * 2 ^ n) * G * 2 ^ n * B) :
    moveLeftMixInv 2 (2 ^ n * G) (2 ^ n * B) (swapFieldsInv (2 ^ n) G (2 ^ n) B y) =
      swapFieldsInv (2 ^ n) G (2 * 2 ^ n) B y := by
  have hNpos : 0 < 2 ^ n := by positivity
  obtain ⟨a, D, g, h, z, ha, hD, hg, hh, hz, hy'⟩ := decomp5 hy
  have hb : D / 2 ^ n < 2 := (Nat.div_lt_iff_lt_mul hNpos).2 (by linarith)
  have hd : D % 2 ^ n < 2 ^ n := Nat.mod_lt _ hNpos
  have hDe : D = D / 2 ^ n * 2 ^ n + D % 2 ^ n := (Nat.div_add_mod' D (2 ^ n)).symm
  have lhs : moveLeftMixInv 2 (2 ^ n * G) (2 ^ n * B) (swapFieldsInv (2 ^ n) G (2 ^ n) B y) =
      ((a * (2 ^ n * G) + (h * G + g)) * 2 + D / 2 ^ n) * (2 ^ n * B) + (D % 2 ^ n * B + z) := by
    have e1 : y = ((((a * 2 + D / 2 ^ n) * 2 ^ n + D % 2 ^ n) * G + g) * 2 ^ n + h) * B + z := by
      rw [hy']
      nth_rewrite 1 [hDe]
      ring
    rw [e1, swapFieldsInv_coord hd hg hh hz]
    have e2 : ((((a * 2 + D / 2 ^ n) * 2 ^ n + h) * G + g) * 2 ^ n + D % 2 ^ n) * B + z =
        ((a * 2 + D / 2 ^ n) * (2 ^ n * G) + (h * G + g)) * (2 ^ n * B) +
          (D % 2 ^ n * B + z) := by ring
    rw [e2, moveLeftMixInv_coord (add_mul_lt hh hg) hb (add_mul_lt hd hz)]
  have rhs : swapFieldsInv (2 ^ n) G (2 * 2 ^ n) B y =
      (((a * 2 ^ n + h) * G + g) * (2 * 2 ^ n) + D) * B + z := by
    rw [hy', swapFieldsInv_coord hD hg hh hz]
  rw [lhs, rhs]
  conv_rhs => rw [hDe]
  ring

/-! ## The exponent is positive -/

/-- The premise `s_b/W_b < m^τ` forces `0 < τ`, because `W_b ≤ s_b`. -/
theorem tau_pos {τ : ℝ} (hτ : (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ) :
    0 < τ := by
  by_contra h0
  have h : τ ≤ 0 := not_lt.mp h0
  have hm : (1 : ℝ) ≤ (tripleM 100 : ℝ) := by exact_mod_cast (by decide : 1 ≤ tripleM 100)
  have h1 : (tripleM 100 : ℝ) ^ τ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm h
  have hW : (0 : ℝ) < (tripleWb 100 : ℝ) := by exact_mod_cast (by decide : 0 < tripleWb 100)
  have hWS : (tripleWb 100 : ℝ) ≤ (tripleSb 100 : ℝ) := by
    exact_mod_cast (by decide : tripleWb 100 ≤ tripleSb 100)
  have h2 : (1 : ℝ) ≤ (tripleSb 100 : ℝ) / tripleWb 100 := by
    rw [le_div_iff₀ hW, one_mul]
    exact hWS
  linarith

/-- Monotonicity of the Lemma A.8 cost in the width. -/
theorem ceil_pow_mono {V u M : ℕ} {τ : ℝ} (hτ : 0 < τ) (huM : u ≤ M) :
    ⌈(V : ℝ) * (u : ℝ) ^ τ⌉₊ ≤ ⌈(V : ℝ) * (M : ℝ) ^ τ⌉₊ := by
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg V)
  exact Real.rpow_le_rpow (Nat.cast_nonneg u) (by exact_mod_cast huM) hτ.le

/-- `V ≤ ⌈V·M^τ⌉₊` for `M ≥ 1`, `τ > 0`. -/
theorem le_ceil_pow {V M : ℕ} {τ : ℝ} (hτ : 0 < τ) (hM : 1 ≤ M) :
    V ≤ ⌈(V : ℝ) * (M : ℝ) ^ τ⌉₊ := by
  have h1 : (1 : ℝ) ≤ (M : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hM) hτ.le
  have h2 : (V : ℝ) ≤ (V : ℝ) * (M : ℝ) ^ τ := by
    nlinarith [Nat.cast_nonneg (α := ℝ) V]
  exact_mod_cast h2.trans (Nat.le_ceil _)

/-- The branch costs fit `C·(X + 1)` with `C = 2·Cc + Ce + Cr + Cl + 2`. -/
theorem cost_fit {Cc Ce Cr Cl Tc Te Tr Tl V X : ℕ} (hTc : Tc ≤ Cc * V) (hTe : Te ≤ Ce * (X + 1))
    (hTr : Tr ≤ Cr * (V + 1)) (hTl : Tl ≤ Cl * (V + 1)) (hVX : V ≤ X) :
    Tc + ((Tc + ((Te + Tr) + 1)) + 1) ≤ (2 * Cc + Ce + Cr + Cl + 2) * (X + 1) ∧
      Tc + ((Tc + ((Tl + Te) + 1)) + 1) ≤ (2 * Cc + Ce + Cr + Cl + 2) * (X + 1) ∧
      Tc + (Te + 1) ≤ (2 * Cc + Ce + Cr + Cl + 2) * (X + 1) := by
  have h1 : Cc * V ≤ Cc * (X + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : Cr * (V + 1) ≤ Cr * (X + 1) := Nat.mul_le_mul_left _ (by omega)
  have h3 : Cl * (V + 1) ≤ Cl * (X + 1) := Nat.mul_le_mul_left _ (by omega)
  have e : (2 * Cc + Ce + Cr + Cl + 2) * (X + 1) =
      2 * (Cc * (X + 1)) + Ce * (X + 1) + Cr * (X + 1) + Cl * (X + 1) + 2 * (X + 1) := by ring
  refine ⟨by omega, by omega, by omega⟩

end AppC.C6Aux

namespace AppC.C6Aux

theorem moveLeftMixInv_lt {q N0 N1 N2 y : ℕ} (hy : y < N0 * q * N1 * N2) :
    moveLeftMixInv q N1 N2 y < N0 * N1 * q * N2 := by
  obtain ⟨a, d, x1, x2, ha, hd, hx1, hx2, rfl⟩ := decomp3 hy
  rw [moveLeftMixInv_coord hx1 hd hx2]
  exact add_mul_lt (add_mul_lt (add_mul_lt ha hx1) hd) hx2

/-! ## Machine plumbing -/

section Plumbing

variable {L K σ R : Type} [DecidableEq L] [DecidableEq K]

/-- `callInj` keeping the register postcondition through the lens. -/
theorem runs_callInj_reg {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) :
    Runs (callInj ι l P) B B' (fun v => Q (l.get v)) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = B at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', hq⟩, ht⟩ := hP ⟨l.get v, stk ∘ ι⟩ rfl
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι stk (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      exact (h1 x).trans (congrFun hs' x)
    · simp only [not_exists] at hk
      rw [h2 _ hk, hout k hk]
  subst hT'
  refine ⟨⟨l.set v s'.var, T'⟩, t, Eval.liftRegs l e' v rfl, ⟨rfl, ?_⟩, ht⟩
  show Q (l.get (l.set v s'.var))
  rw [l.get_set]
  exact hq

/-- `callInj` of a kernel that updates one stack. -/
theorem runs_callInj_upd1 {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {Q : R → Prop} {T : ℕ} (B : K → List Sym) (x : L)
    (v : List Sym) (h : Runs P (B ∘ ι) (Function.update (B ∘ ι) x v) Q T) :
    Runs (callInj ι l P) B (Function.update B (ι x) v) (fun _ => True) T :=
  runs_callInj hι l (by rw [Function.update_comp_eq_of_injective B hι x v]; exact h)
    (fun k hk => Function.update_of_ne (Ne.symm (hk x)) _ _)

end Plumbing

/-! ## The composite layout of level A -/

/-- Scratch of level A: the equal-width kernel, the two bit moves, the comparator. -/
abbrev EA (Ee Er El : Type) (mc : ℕ) : Type := Ee ⊕ (Er ⊕ (El ⊕ Fin mc))

/-- Registers of level A. -/
abbrev RA (Re Rr Rl Rc : Type) : Type := Re × (Rr × (Rl × Rc))

def ιE1 (Ee Er El : Type) (mc : ℕ) : KLoc (Fin 5) Ee → KLoc (Fin 6) (EA Ee Er El mc) :=
  Sum.map (![0, 1, 3, 4, 5] : Fin 5 → Fin 6) Sum.inl

def ιE2 (Ee Er El : Type) (mc : ℕ) : KLoc (Fin 5) Ee → KLoc (Fin 6) (EA Ee Er El mc) :=
  Sum.map (![0, 2, 3, 4, 5] : Fin 5 → Fin 6) Sum.inl

def ιR (Ee Er El : Type) (mc : ℕ) : KLoc (Fin 4) Er → KLoc (Fin 6) (EA Ee Er El mc) :=
  Sum.map (![0, 2, 3, 4] : Fin 4 → Fin 6) fun e => Sum.inr (Sum.inl e)

def ιL (Ee Er El : Type) (mc : ℕ) : KLoc (Fin 4) El → KLoc (Fin 6) (EA Ee Er El mc) :=
  Sum.map (![0, 1, 3, 4] : Fin 4 → Fin 6) fun e => Sum.inr (Sum.inr (Sum.inl e))

def ιC (Ee Er El : Type) (mc : ℕ) : Loc 2 mc → KLoc (Fin 6) (EA Ee Er El mc) :=
  Sum.map (![1, 2] : Fin 2 → Fin 6) fun j => Sum.inr (Sum.inr (Sum.inr j))

theorem ιE1_inj (Ee Er El : Type) (mc : ℕ) : Function.Injective (ιE1 Ee Er El mc) :=
  Sum.map_injective.2 ⟨by decide, Sum.inl_injective⟩

theorem ιE2_inj (Ee Er El : Type) (mc : ℕ) : Function.Injective (ιE2 Ee Er El mc) :=
  Sum.map_injective.2 ⟨by decide, Sum.inl_injective⟩

theorem ιR_inj (Ee Er El : Type) (mc : ℕ) : Function.Injective (ιR Ee Er El mc) :=
  Sum.map_injective.2 ⟨by decide, fun a b h => by simpa using h⟩

theorem ιL_inj (Ee Er El : Type) (mc : ℕ) : Function.Injective (ιL Ee Er El mc) :=
  Sum.map_injective.2 ⟨by decide, fun a b h => by simpa using h⟩

theorem ιC_inj (Ee Er El : Type) (mc : ℕ) : Function.Injective (ιC Ee Er El mc) :=
  Sum.map_injective.2 ⟨by decide, fun a b h => by simpa using h⟩

def lE (Re Rr Rl Rc : Type) : Lens (RA Re Rr Rl Rc) Re := Lens.fst _ _

def lR (Re Rr Rl Rc : Type) : Lens (RA Re Rr Rl Rc) Rr := (Lens.snd _ _).comp (Lens.fst _ _)

def lL (Re Rr Rl Rc : Type) : Lens (RA Re Rr Rl Rc) Rl :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))

def lC (Re Rr Rl Rc : Type) : Lens (RA Re Rr Rl Rc) Rc :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))

/-- **The level-A program**: compare `u1, u2`; equal widths, or the two unequal-width branches. -/
def progA {K σ : Type} (cmp e1 e2 r l : Prog K (fun _ => Sym) σ) (isEq isGt : σ → Bool) :
    Prog K (fun _ => Sym) σ :=
  .seq cmp (.ite isEq e1 (.seq cmp (.ite isGt (.seq e2 r) (.seq l e1))))

theorem closed_progA {K σ : Type} {cmp e1 e2 r l : Prog K (fun _ => Sym) σ} {isEq isGt : σ → Bool}
    (hc : cmp.Closed) (h1 : e1.Closed) (h2 : e2.Closed) (hr : r.Closed) (hl : l.Closed) :
    (progA cmp e1 e2 r l isEq isGt).Closed :=
  ⟨hc, h1, hc, ⟨h2, hr⟩, ⟨hl, h1⟩⟩

/-- `Runs` weakening (via `RunsIn.mono`). -/
theorem runs_mono {K σ : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q Q' : σ → Prop} {T T' : ℕ} (h : Runs P S S' Q T)
    (hQ : ∀ v, Q v → Q' v) (hT : T ≤ T') : Runs P S S' Q' T' :=
  RunsIn.iff_runs.1 (RunsIn.mono (RunsIn.iff_runs.2 h) hQ hT)

/-- `Runs` with rewritten final stacks and weakened cost (via `RunsIn.congr`). -/
theorem runs_congr {K σ : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) σ}
    {S S₁ S₂ : K → List Sym} {Q : σ → Prop} {T T' : ℕ} (h : Runs P S S₁ Q T) (e : S₁ = S₂)
    (hT : T ≤ T') : Runs P S S₂ Q T' :=
  RunsIn.iff_runs.1 (RunsIn.congr (RunsIn.iff_runs.2 h) e hT)

section Branches

variable {K σ : Type} [DecidableEq K] {cmp e1 e2 r l : Prog K (fun _ => Sym) σ}
  {isEq isGt : σ → Bool}

theorem runs_progA_eq {S S' : K → List Sym} {Tc Te : ℕ}
    (hc : Runs cmp S S (fun v => isEq v = true) Tc) (he : Runs e1 S S' (fun _ => True) Te) :
    Runs (progA cmp e1 e2 r l isEq isGt) S S' (fun _ => True) (Tc + (Te + 1)) :=
  RunsIn.iff_runs.1 (RunsIn.ite_true (RunsIn.iff_runs.2 hc) (RunsIn.iff_runs.2 he))

theorem runs_progA_gt {S S1 S2 : K → List Sym} {Tc T2 Tr : ℕ}
    (hc1 : Runs cmp S S (fun v => isEq v = false) Tc)
    (hc2 : Runs cmp S S (fun v => isGt v = true) Tc)
    (h2 : Runs e2 S S1 (fun _ => True) T2) (hr : Runs r S1 S2 (fun _ => True) Tr) :
    Runs (progA cmp e1 e2 r l isEq isGt) S S2 (fun _ => True)
      (Tc + ((Tc + ((T2 + Tr) + 1)) + 1)) :=
  RunsIn.iff_runs.1 (RunsIn.ite_false (RunsIn.iff_runs.2 hc1) (RunsIn.ite_true
    (RunsIn.iff_runs.2 hc2) (RunsIn.seq (RunsIn.iff_runs.2 h2) (RunsIn.iff_runs.2 hr))))

theorem runs_progA_lt {S S1 S2 : K → List Sym} {Tc Tl T1 : ℕ}
    (hc1 : Runs cmp S S (fun v => isEq v = false) Tc)
    (hc2 : Runs cmp S S (fun v => isGt v = false) Tc)
    (hl : Runs l S S1 (fun _ => True) Tl) (h1 : Runs e1 S1 S2 (fun _ => True) T1) :
    Runs (progA cmp e1 e2 r l isEq isGt) S S2 (fun _ => True)
      (Tc + ((Tc + ((Tl + T1) + 1)) + 1)) :=
  RunsIn.iff_runs.1 (RunsIn.ite_false (RunsIn.iff_runs.2 hc1) (RunsIn.ite_false
    (RunsIn.iff_runs.2 hc2) (RunsIn.seq (RunsIn.iff_runs.2 hl) (RunsIn.iff_runs.2 h1))))

end Branches

end AppC.C6Aux

open AppC.C6Aux in
/-- **Lemma A.8 level A** (Lemma A.8 (`lem:transfer12`)): the
equal-width interchange `C6EqStmt τ` and the two single-bit moves give the Lemma A.8 contract
`C6InterchangeStmt τ` for all widths with `|u1 - u2| ≤ 1`. -/
theorem c6Interchange_of_eq {τ : ℝ} (hEq : C6EqStmt τ) (hR : C6BitMoveStmt true)
    (hL : C6BitMoveStmt false) : C6InterchangeStmt τ := by
  intro hτ
  have hτ0 : 0 < τ := tau_pos hτ
  obtain ⟨Ce, hEq⟩ := hEq hτ
  obtain ⟨Cr, hR⟩ := hR
  obtain ⟨Cl, hL⟩ := hL
  obtain ⟨Cc, hC⟩ := w3_cmpNat
  obtain ⟨Ee, _, _, Re, Pe, hRe1, hRe2, hPe, hsE⟩ := hEq ()
  obtain ⟨Er, _, _, Rr, Pr, hRr1, hRr2, hPr, hsR⟩ := hR ()
  obtain ⟨El, _, _, Rl, Pl, hRl1, hRl2, hPl, hsL⟩ := hL ()
  obtain ⟨mc, Rc, obs, Pc, -, hRc1, hRc2, hPc, hsC⟩ := hC ()
  have := hRe1; have := hRe2; have := hRr1; have := hRr2
  have := hRl1; have := hRl2; have := hRc1; have := hRc2
  refine ⟨2 * Cc + Ce + Cr + Cl + 2, fun _ => ⟨EA Ee Er El mc, inferInstance, inferInstance,
    RA Re Rr Rl Rc,
    progA (callInj (ιC Ee Er El mc) (lC Re Rr Rl Rc) Pc)
      (callInj (ιE1 Ee Er El mc) (lE Re Rr Rl Rc) Pe) (callInj (ιE2 Ee Er El mc) (lE Re Rr Rl Rc) Pe)
      (callInj (ιR Ee Er El mc) (lR Re Rr Rl Rc) Pr) (callInj (ιL Ee Er El mc) (lL Re Rr Rl Rc) Pl)
      (fun x => decide (obs x.2.2.2 = .eq)) (fun x => decide (obs x.2.2.2 = .gt)),
    inferInstance, inferInstance,
    closed_progA (closed_callInj _ _ hPc) (closed_callInj _ _ hPe) (closed_callInj _ _ hPe)
      (closed_callInj _ _ hPr) (closed_callInj _ _ hPl), ?_⟩⟩
  intro A u1 u2 G B w v rest r1 r2 r3 r4 r5 S hu1 hu2 h12 h21 hA hG hB hlen hw hrest hr1 hr2 hr3
    hr4 hr5 hS0 hS1 hS2 hS3 hS4 hS5
  -- common facts
  have hV : vol v = v.length * (w + 1) := vol_eq_of_width hw
  have hlenV : v.length ≤ vol v := by
    rw [hV]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos w)
  have hlen_ge : 2 ^ u1 * 2 ^ u2 ≤ v.length := by
    rw [hlen]
    calc 2 ^ u1 * 2 ^ u2 = 1 * 2 ^ u1 * 1 * 2 ^ u2 * 1 := by ring
      _ ≤ A * 2 ^ u1 * G * 2 ^ u2 * B := by gcongr
  have hpow : u1 + u2 + 1 ≤ 2 ^ u1 * 2 ^ u2 := by
    rw [← pow_add]; exact Nat.lt_two_pow_self
  have hbl1 : bitLen u1 ≤ u1 := TMFw.W3s.bitLen_le_of_lt Nat.lt_two_pow_self
  have hbl2 : bitLen u2 ≤ u2 := TMFw.W3s.bitLen_le_of_lt Nat.lt_two_pow_self
  have hTc : Cc * (bitLen u1 + bitLen u2 + 1) ≤ Cc * vol v :=
    Nat.mul_le_mul_left _ (by omega)
  have hM : 1 ≤ max u1 u2 := le_max_of_le_left hu1
  have hVX : vol v ≤ ⌈(vol v : ℝ) * ((max u1 u2 : ℕ) : ℝ) ^ τ⌉₊ := le_ceil_pow hτ0 hM
  have hcmp := runs_callInj_reg (ιC_inj Ee Er El mc) (lC Re Rr Rl Rc)
    (hsC u1 u2 r1 r2 (S ∘ ιC Ee Er El mc) hr1 hr2 hS1 hS2) (fun _ _ => rfl)
  rcases (by omega : u1 = u2 ∨ u1 = u2 + 1 ∨ u2 = u1 + 1) with h | h | h
  · -- equal widths: one interchange
    subst u2
    have hc : Runs (callInj (ιC Ee Er El mc) (lC Re Rr Rl Rc) Pc) S S
        (fun x => decide (obs x.2.2.2 = .eq) = true) (Cc * (bitLen u1 + bitLen u1 + 1)) :=
      runs_mono hcmp (fun x hx => by
        have hx' : obs x.2.2.2 = .eq := hx.trans (Lib.ordOf_self u1)
        rw [hx']; rfl) le_rfl
    have he := runs_callInj_upd1 (ιE1_inj Ee Er El mc) (lE Re Rr Rl Rc) S (.inl 0) _
      (hsE A u1 G B w v rest r1 r3 r4 r5 (S ∘ ιE1 Ee Er El mc) hu1 hA hG hB hlen hw hrest hr1 hr3
        hr4 hr5 hS0 hS1 hS3 hS4 hS5)
    have hfit := (cost_fit (Cl := Cl) (Cr := Cr) (Tr := 0) (Tl := 0) hTc
      (Te := Ce * (⌈(vol v : ℝ) * (u1 : ℝ) ^ τ⌉₊ + 1))
      (Nat.mul_le_mul_left _ (Nat.succ_le_succ (ceil_pow_mono hτ0 (le_max_left u1 u1))))
      (Nat.zero_le _) (Nat.zero_le _) hVX).2.2
    exact runs_mono (runs_progA_eq hc he) (fun _ _ => trivial) hfit
  · -- `u1 = u2 + 1`: interchange with prefix `2A`, then the right bit move
    subst u1
    have hord : Lib.ordOf (u2 + 1) u2 = .gt := by
      unfold Lib.ordOf; rw [if_neg (by omega), if_neg (by omega)]
    have hc1 : Runs (callInj (ιC Ee Er El mc) (lC Re Rr Rl Rc) Pc) S S
        (fun x => decide (obs x.2.2.2 = .eq) = false) (Cc * (bitLen (u2 + 1) + bitLen u2 + 1)) :=
      runs_mono hcmp (fun x hx => by
        have hx' : obs x.2.2.2 = .gt := hx.trans hord
        rw [hx']; rfl) le_rfl
    have hc2 : Runs (callInj (ιC Ee Er El mc) (lC Re Rr Rl Rc) Pc) S S
        (fun x => decide (obs x.2.2.2 = .gt) = true) (Cc * (bitLen (u2 + 1) + bitLen u2 + 1)) :=
      runs_mono hcmp (fun x hx => by
        have hx' : obs x.2.2.2 = .gt := hx.trans hord
        rw [hx']; rfl) le_rfl
    have hlen2 : v.length = 2 * A * 2 ^ u2 * G * 2 ^ u2 * B := by rw [hlen, pow_succ]; ring
    have hrg1 : ∀ y < v.length, swapFieldsInv (2 ^ u2) G (2 ^ u2) B y < v.length := by
      intro y hy
      rw [hlen2] at hy ⊢
      exact swapFieldsInv_lt hy
    have hlen₁ : (permByInv (swapFieldsInv (2 ^ u2) G (2 ^ u2) B) v).length =
        A * 2 * 2 ^ u2 * G * 2 ^ u2 * B := by
      rw [length_permByInv, hlen, pow_succ]; ring
    have hw₁ : ∀ p ∈ permByInv (swapFieldsInv (2 ^ u2) G (2 ^ u2) B) v, p.length = w :=
      fun p hp => hw p (mem_permByInv hrg1 hp)
    have hvol₁ : vol (permByInv (swapFieldsInv (2 ^ u2) G (2 ^ u2) B) v) = vol v := by
      rw [vol_eq_of_width hw₁, hV, length_permByInv]
    have he := runs_callInj_upd1 (ιE2_inj Ee Er El mc) (lE Re Rr Rl Rc) S (.inl 0) _
      (hsE (2 * A) u2 G B w v rest r2 r3 r4 r5 (S ∘ ιE2 Ee Er El mc) hu2 (by omega) hG hB hlen2 hw
        hrest hr2 hr3 hr4 hr5 hS0 hS2 hS3 hS4 hS5)
    have hRk : Runs Pr
        (Function.update S (.inl 0)
          (arrSyms (permByInv (swapFieldsInv (2 ^ u2) G (2 ^ u2) B) v) ++ rest) ∘ ιR Ee Er El mc)
        (Function.update (Function.update S (.inl 0)
          (arrSyms (permByInv (swapFieldsInv (2 ^ u2) G (2 ^ u2) B) v) ++ rest) ∘ ιR Ee Er El mc)
          (.inl 0) (arrSyms (permByInv (moveRightMixInv 2 (2 ^ u2 * G) (2 ^ u2 * B))
            (permByInv (swapFieldsInv (2 ^ u2) G (2 ^ u2) B) v)) ++ rest))
        (fun _ => True) (Cr * (vol (permByInv (swapFieldsInv (2 ^ u2) G (2 ^ u2) B) v) + 1)) :=
      hsR A u2 G B w _ rest r2 r3 r4 _ hlen₁ hw₁ hrest hr2 hr3 hr4 (Function.update_self _ _ _)
        (by show Function.update S (Sum.inl 0) _ (Sum.inl 2) = _
            rw [Function.update_of_ne (by simp)]; exact hS2)
        (by show Function.update S (Sum.inl 0) _ (Sum.inl 3) = _
            rw [Function.update_of_ne (by simp)]; exact hS3)
        (by show Function.update S (Sum.inl 0) _ (Sum.inl 4) = _
            rw [Function.update_of_ne (by simp)]; exact hS4)
    have hr := runs_callInj_upd1 (ιR_inj Ee Er El mc) (lR Re Rr Rl Rc) _ (.inl 0) _ hRk
    have hfun : permByInv (moveRightMixInv 2 (2 ^ u2 * G) (2 ^ u2 * B))
        (permByInv (swapFieldsInv (2 ^ u2) G (2 ^ u2) B) v) =
        permByInv (swapFieldsInv (2 ^ (u2 + 1)) G (2 ^ u2) B) v := by
      rw [permByInv_comp _ _ v (fun y hy => ?_)]
      · apply permByInv_congr
        intro y hy
        rw [pow_succ']
        apply gt_identity
        calc y < v.length := hy
          _ = A * 2 ^ u2 * G * (2 * 2 ^ u2) * B := by rw [hlen, pow_succ]; ring
      · have hy' : y < A * (2 ^ u2 * G) * 2 * (2 ^ u2 * B) := by
          calc y < v.length := hy
            _ = A * (2 ^ u2 * G) * 2 * (2 ^ u2 * B) := by rw [hlen, pow_succ]; ring
        calc moveRightMixInv 2 (2 ^ u2 * G) (2 ^ u2 * B) y < A * 2 * (2 ^ u2 * G) * (2 ^ u2 * B) :=
              moveRightMixInv_lt hy'
          _ = v.length := by rw [hlen, pow_succ]; ring
    have hfit := (cost_fit (Cl := Cl) (Tl := 0) hTc
      (Te := Ce * (⌈(vol v : ℝ) * (u2 : ℝ) ^ τ⌉₊ + 1))
      (Tr := Cr * (vol (permByInv (swapFieldsInv (2 ^ u2) G (2 ^ u2) B) v) + 1))
      (Nat.mul_le_mul_left _ (Nat.succ_le_succ (ceil_pow_mono hτ0 (le_max_right (u2 + 1) u2))))
      (by rw [hvol₁]) (Nat.zero_le _) hVX).1
    refine runs_congr (runs_progA_gt hc1 hc2 he hr) ?_ hfit
    show Function.update (Function.update S (.inl 0) _) (.inl 0) _ = _
    rw [Function.update_idem, hfun]
  · -- `u2 = u1 + 1`: the left bit move, then the interchange with prefix `2A`
    subst u2
    have hord : Lib.ordOf u1 (u1 + 1) = .lt := by
      unfold Lib.ordOf; rw [if_pos (by omega)]
    have hc1 : Runs (callInj (ιC Ee Er El mc) (lC Re Rr Rl Rc) Pc) S S
        (fun x => decide (obs x.2.2.2 = .eq) = false) (Cc * (bitLen u1 + bitLen (u1 + 1) + 1)) :=
      runs_mono hcmp (fun x hx => by
        have hx' : obs x.2.2.2 = .lt := hx.trans hord
        rw [hx']; rfl) le_rfl
    have hc2 : Runs (callInj (ιC Ee Er El mc) (lC Re Rr Rl Rc) Pc) S S
        (fun x => decide (obs x.2.2.2 = .gt) = false) (Cc * (bitLen u1 + bitLen (u1 + 1) + 1)) :=
      runs_mono hcmp (fun x hx => by
        have hx' : obs x.2.2.2 = .lt := hx.trans hord
        rw [hx']; rfl) le_rfl
    have hlenL : v.length = A * 2 * 2 ^ u1 * G * 2 ^ u1 * B := by rw [hlen, pow_succ]; ring
    have hrgL : ∀ y < v.length, moveLeftMixInv 2 (2 ^ u1 * G) (2 ^ u1 * B) y < v.length := by
      intro y hy
      have hy' : y < A * 2 * (2 ^ u1 * G) * (2 ^ u1 * B) := by
        calc y < v.length := hy
          _ = A * 2 * (2 ^ u1 * G) * (2 ^ u1 * B) := by rw [hlen, pow_succ]; ring
      calc moveLeftMixInv 2 (2 ^ u1 * G) (2 ^ u1 * B) y < A * (2 ^ u1 * G) * 2 * (2 ^ u1 * B) :=
            moveLeftMixInv_lt hy'
        _ = v.length := by rw [hlen, pow_succ]; ring
    have hLk : Runs Pl (S ∘ ιL Ee Er El mc)
        (Function.update (S ∘ ιL Ee Er El mc) (.inl 0)
          (arrSyms (permByInv (moveLeftMixInv 2 (2 ^ u1 * G) (2 ^ u1 * B)) v) ++ rest))
        (fun _ => True) (Cl * (vol v + 1)) :=
      hsL A u1 G B w v rest r1 r3 r4 (S ∘ ιL Ee Er El mc) hlenL hw hrest hr1 hr3 hr4 hS0 hS1 hS3 hS4
    have hl := runs_callInj_upd1 (ιL_inj Ee Er El mc) (lL Re Rr Rl Rc) S (.inl 0) _ hLk
    have hlen₁ : (permByInv (moveLeftMixInv 2 (2 ^ u1 * G) (2 ^ u1 * B)) v).length =
        2 * A * 2 ^ u1 * G * 2 ^ u1 * B := by
      rw [length_permByInv, hlen, pow_succ]; ring
    have hw₁ : ∀ p ∈ permByInv (moveLeftMixInv 2 (2 ^ u1 * G) (2 ^ u1 * B)) v, p.length = w :=
      fun p hp => hw p (mem_permByInv hrgL hp)
    have hvol₁ : vol (permByInv (moveLeftMixInv 2 (2 ^ u1 * G) (2 ^ u1 * B)) v) = vol v := by
      rw [vol_eq_of_width hw₁, hV, length_permByInv]
    have hEk := hsE (2 * A) u1 G B w (permByInv (moveLeftMixInv 2 (2 ^ u1 * G) (2 ^ u1 * B)) v)
      rest r1 r3 r4 r5
      (Function.update S (.inl 0)
        (arrSyms (permByInv (moveLeftMixInv 2 (2 ^ u1 * G) (2 ^ u1 * B)) v) ++ rest) ∘
        ιE1 Ee Er El mc)
      hu1 (by omega) hG hB hlen₁ hw₁ hrest hr1 hr3 hr4 hr5 (Function.update_self _ _ _)
      (by show Function.update S (Sum.inl 0) _ (Sum.inl 1) = _
          rw [Function.update_of_ne (by simp)]; exact hS1)
      (by show Function.update S (Sum.inl 0) _ (Sum.inl 3) = _
          rw [Function.update_of_ne (by simp)]; exact hS3)
      (by show Function.update S (Sum.inl 0) _ (Sum.inl 4) = _
          rw [Function.update_of_ne (by simp)]; exact hS4)
      (by show Function.update S (Sum.inl 0) _ (Sum.inl 5) = _
          rw [Function.update_of_ne (by simp)]; exact hS5)
    have he := runs_callInj_upd1 (ιE1_inj Ee Er El mc) (lE Re Rr Rl Rc) _ (.inl 0) _ hEk
    have hrgE : ∀ y < v.length, swapFieldsInv (2 ^ u1) G (2 ^ u1) B y < v.length := by
      intro y hy
      have e : v.length = 2 * A * 2 ^ u1 * G * 2 ^ u1 * B := by rw [hlen, pow_succ]; ring
      rw [e] at hy ⊢
      exact swapFieldsInv_lt hy
    have hfun : permByInv (swapFieldsInv (2 ^ u1) G (2 ^ u1) B)
        (permByInv (moveLeftMixInv 2 (2 ^ u1 * G) (2 ^ u1 * B)) v) =
        permByInv (swapFieldsInv (2 ^ u1) G (2 ^ (u1 + 1)) B) v := by
      rw [permByInv_comp _ _ v hrgE]
      apply permByInv_congr
      intro y hy
      rw [pow_succ']
      apply lt_identity
      calc y < v.length := hy
        _ = A * (2 * 2 ^ u1) * G * 2 ^ u1 * B := by rw [hlen, pow_succ]; ring
    have hfit := (cost_fit (Cr := Cr) (Tr := 0) hTc
      (Te := Ce * (⌈(vol (permByInv (moveLeftMixInv 2 (2 ^ u1 * G) (2 ^ u1 * B)) v) : ℝ) *
        (u1 : ℝ) ^ τ⌉₊ + 1))
      (Tl := Cl * (vol v + 1))
      (by rw [hvol₁]
          exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (ceil_pow_mono hτ0
            (le_max_left u1 (u1 + 1)))))
      (Nat.zero_le _) le_rfl hVX).2.1
    refine runs_congr (runs_progA_lt hc1 hc2 hl he) ?_ hfit
    show Function.update (Function.update S (.inl 0) _) (.inl 0) _ = _
    rw [Function.update_idem, hfun]

end SubNLogN.Machine
