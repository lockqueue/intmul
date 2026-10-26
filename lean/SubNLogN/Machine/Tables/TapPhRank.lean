/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.Frag
import SubNLogN.Machine.Tables.Header
import SubNLogN.Machine.Tables.TapRank

/-!
# K6 (`Machine/Tables/TapPhRank.lean`): the shift index of a tap record on the machine

**Scope (honest summary).** Part of the proof of `TapPhaseStmt` (`TapPhaseStmt.lean`). The
fragment `rankProg` computes `a = rankA L r` (`TapRank.lean`) onto `ra`, from the record rank `r`
on `ru`, the product `A = ∏ L` on `rA`, the field count `|L|` on `rI` and the lower shape
`hdrSyms L` on `rSH` (restored): it walks the fields of `rSH` (`rkStep`: one division of the
remaining product `M`, one division with remainder of the remaining rank `x`, one product, one
sum; the field is moved onto `x45`), then moves all fields back. Exact final state, cost
`rankCost C KM β` for any `β ≥ bitLen A`, `β ≥ |L|`. Pure facts on the fold (`rkSt`): the remaining
product is `∏ (L.drop k)`, `a + M ≤ A` (so every value is at most `A`), and `rankA L r < ∏ L`
for `r < ∏ L`. Helpers live in `SubNLogN.Machine.Tables.TapPhAux`.
-/

namespace SubNLogN.Machine.Tables.TapPhAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Machine.Tables
  SubNLogN.Math.Bridge SubNLogN.Math.Common

/-! ## The rank fold -/

/-- The fold state of `rankA L r` after the first `k` axis lengths. -/
def rkSt (L : List ℕ) (r k : ℕ) : ℕ × ℕ × ℕ :=
  (L.take k).foldl (fun st t => rankStep t st) (r, L.prod, 0)

theorem rkSt_zero (L : List ℕ) (r : ℕ) : rkSt L r 0 = (r, L.prod, 0) := by
  simp [rkSt]

theorem rkSt_succ (L : List ℕ) (r k : ℕ) (hk : k < L.length) :
    rkSt L r (k + 1) = rankStep L[k] (rkSt L r k) := by
  simp only [rkSt, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem rankA_eq_rkSt (L : List ℕ) (r : ℕ) : rankA L r = (rkSt L r L.length).2.2 := by
  simp [rankA, rkSt]

theorem rkSt_M (L : List ℕ) (r : ℕ) (hL : ∀ t ∈ L, 1 ≤ t) :
    ∀ k, k ≤ L.length → (rkSt L r k).2.1 = (L.drop k).prod
  | 0, _ => by simp [rkSt_zero]
  | k + 1, hk => by
    rw [rkSt_succ L r k (by omega)]
    show (rkSt L r k).2.1 / L[k] = _
    rw [rkSt_M L r hL k (by omega), List.drop_eq_getElem_cons (by omega), List.prod_cons]
    exact Nat.mul_div_cancel_left _ (hL _ (by simp))

theorem rankStep_inv (t x M a A : ℕ) (ht : 1 ≤ t) (hdvd : t ∣ M) (h : a + M ≤ A) :
    (rankStep t (x, M, a)).2.2 + (rankStep t (x, M, a)).2.1 ≤ A := by
  obtain ⟨q, rfl⟩ := hdvd
  show a + t * q / t * (x % t) + t * q / t ≤ A
  rw [Nat.mul_div_cancel_left q (by omega)]
  have hmod : x % t + 1 ≤ t := Nat.mod_lt _ (by omega)
  have h3 : q * (x % t) + q ≤ t * q := by
    have := Nat.mul_le_mul_left q hmod
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm q t] at this
    exact this
  omega

theorem rkSt_inv (L : List ℕ) (r : ℕ) (hL : ∀ t ∈ L, 1 ≤ t) :
    ∀ k, k ≤ L.length → (rkSt L r k).2.2 + (rkSt L r k).2.1 ≤ L.prod ∧ (rkSt L r k).1 ≤ r
  | 0, _ => by simp [rkSt_zero]
  | k + 1, hk => by
    obtain ⟨h1, h2⟩ := rkSt_inv L r hL k (by omega)
    have hM := rkSt_M L r hL k (by omega)
    have ht : 1 ≤ L[k] := hL _ (by simp)
    have hdvd : L[k] ∣ (rkSt L r k).2.1 := by
      rw [hM, List.drop_eq_getElem_cons (by omega), List.prod_cons]
      exact Dvd.intro _ rfl
    rw [rkSt_succ L r k (by omega)]
    generalize rkSt L r k = st at h1 h2 hdvd
    obtain ⟨x, M, a⟩ := st
    exact ⟨rankStep_inv _ x M a _ ht hdvd h1, le_trans (Nat.div_le_self _ _) h2⟩

theorem prod_pos_of (L : List ℕ) (hL : ∀ t ∈ L, 1 ≤ t) : 1 ≤ L.prod :=
  List.prod_pos (fun t ht => hL t ht)

theorem drop_prod_pos (L : List ℕ) (hL : ∀ t ∈ L, 1 ≤ t) (k : ℕ) : 1 ≤ (L.drop k).prod :=
  prod_pos_of _ (fun t ht => hL t (List.mem_of_mem_drop ht))

/-- The shift index is below the product: `rankA L r < ∏ L` for `r < ∏ L`. -/
theorem rankA_lt (L : List ℕ) (r : ℕ) (hL : ∀ t ∈ L, 1 ≤ t) : rankA L r < L.prod := by
  have h := (rkSt_inv L r hL L.length le_rfl).1
  rw [rkSt_M L r hL L.length le_rfl, List.drop_length, List.prod_nil] at h
  rw [rankA_eq_rkSt]
  omega

/-- Every value of step `k` of the fold is at most `∏ L` (for `r < ∏ L`). -/
theorem rkSt_step_le (L : List ℕ) (r : ℕ) (hL : ∀ t ∈ L, 1 ≤ t) (hr : r < L.prod) (k : ℕ)
    (hk : k < L.length) :
    (rkSt L r k).1 ≤ L.prod ∧ (rkSt L r k).2.1 ≤ L.prod ∧ L[k] ≤ L.prod ∧
      (rkSt L r k).2.2 + (rkSt L r k).2.1 / L[k] * ((rkSt L r k).1 % L[k]) ≤ L.prod := by
  obtain ⟨h1, h2⟩ := rkSt_inv L r hL k hk.le
  have h3 := (rkSt_inv L r hL (k + 1) hk).1
  rw [rkSt_succ L r k hk] at h3
  have hM := rkSt_M L r hL k hk.le
  have hMpos : 1 ≤ (rkSt L r k).2.1 := by rw [hM]; exact drop_prod_pos L hL k
  have hdvd : L[k] ∣ (rkSt L r k).2.1 := by
    rw [hM, List.drop_eq_getElem_cons hk, List.prod_cons]
    exact Dvd.intro _ rfl
  have htM : L[k] ≤ (rkSt L r k).2.1 := Nat.le_of_dvd (by omega) hdvd
  refine ⟨by omega, by omega, by omega, ?_⟩
  have e : (rankStep L[k] (rkSt L r k)).2.2 =
      (rkSt L r k).2.2 + (rkSt L r k).2.1 / L[k] * ((rkSt L r k).1 % L[k]) := rfl
  omega

/-! ## Lower shapes -/

theorem lowerShape_len {d : ℕ} (t : Fin d → ℕ) (i : ℕ) (hi : i ≤ d) :
    (lowerShape t i).length = i := by
  simp [lowerShape, hi]

theorem lowerShape_succ'' {d : ℕ} (t : Fin d → ℕ) (k : ℕ) (hk : k < d) :
    lowerShape t (k + 1) = t ⟨k, hk⟩ :: lowerShape t k := by
  unfold lowerShape
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hk)]
  simp

theorem prefixProd_succ'' {d : ℕ} (t : Fin d → ℕ) (j : ℕ) (hj : j < d) :
    prefixProd t (j + 1) = prefixProd t j * t ⟨j, hj⟩ := by
  unfold prefixProd
  have h : Finset.univ.filter (fun i : Fin d => (i : ℕ) < j + 1) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun i : Fin d => (i : ℕ) < j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [h, Finset.prod_insert (by simp), mul_comm]

theorem prefixProd_zero' {d : ℕ} (t : Fin d → ℕ) : prefixProd t 0 = 1 := by
  simp [prefixProd]

theorem lowerShape_prod {d : ℕ} (t : Fin d → ℕ) : ∀ i, i ≤ d → (lowerShape t i).prod = prefixProd t i
  | 0, _ => by simp [lowerShape, prefixProd_zero']
  | i + 1, hi => by
    rw [lowerShape_succ'' t i (by omega), List.prod_cons, lowerShape_prod t i (by omega),
      prefixProd_succ'' t i (by omega), Nat.mul_comm]

theorem lowerShape_ge {d : ℕ} (t : Fin d → ℕ) (h2 : ∀ j, 2 ≤ t j) (i : ℕ) :
    ∀ x ∈ lowerShape t i, 2 ≤ x := by
  intro x hx
  unfold lowerShape at hx
  rw [List.mem_reverse] at hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 (List.mem_of_mem_take hx)
  exact h2 j

/-- `2^|L| ≤ ∏ L` when every entry is at least `2`. -/
theorem two_pow_le_prod (L : List ℕ) (h : ∀ x ∈ L, 2 ≤ x) : 2 ^ L.length ≤ L.prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.length_cons, List.prod_cons, pow_succ]
    have ha := h a List.mem_cons_self
    have hL := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    calc 2 ^ L.length * 2 ≤ L.prod * a := Nat.mul_le_mul hL ha
      _ = a * L.prod := Nat.mul_comm _ _

/-- `|L| < bitLen (∏ L)` when every entry is at least `2`. -/
theorem length_lt_bitLen_prod (L : List ℕ) (h : ∀ x ∈ L, 2 ≤ x) : L.length < bitLen L.prod := by
  have h1 := WP.W7k2.bitLen_mono (two_pow_le_prod L h)
  rw [WP.W7k2.bitLen_two_pow] at h1
  omega

/-! ## Programs -/

section Defs

variable (I : TB)

/-- `X := Y`, `Y := []` (each holds exactly one natural number). -/
def mvNat (X Y : TL) : TP I := (tdr I X).seq ((tcp I Y X).seq (tdr I Y))

theorem mvNat_closed (X Y : TL) : (mvNat I X Y).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

/-- One step of the rank fold (field `t` on top of `rSH`; `x` on `x40`, `M` on `x41`, `a` on
`ra`): `x := x / t`, `M := M / t`, `a := a + (M / t)·(x % t)`; the field moves onto `x45`. -/
def rkStep : TP I :=
  (tcp I rSH x46).seq ((tdm I x41 x46 x47 x48).seq ((tdm I x40 x46 x49 x50).seq
    ((natMul I x47 x50 x51).seq ((tad I ra x51 x52).seq ((mvNat I ra x52).seq
    ((mvNat I x40 x49).seq ((mvNat I x41 x47).seq ((tdr I x46).seq ((tdr I x48).seq
    ((tdr I x50).seq ((tdr I x51).seq (moveThru I rSH x45))))))))))))

theorem rkStep_closed : (rkStep I).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, natMul_closed I _ _ _,
    callI_closed _ _ _ _, mvNat_closed I _ _, mvNat_closed I _ _, mvNat_closed I _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    moveThru_closed I _ _⟩

/-- The rank fragment: `ra := rankA L r` (see the module docstring). -/
def rankProg : TP I :=
  (tcp I ru x40).seq ((tcp I rA x41).seq ((tcp I rI x44).seq ((tcd I x44 (rkStep I)).seq
    ((moveAll I x45 rSH).seq ((tdr I x40).seq (tdr I x41))))))

theorem rankProg_closed : (rankProg I).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    tcd_closed I _ _ (rkStep_closed I), moveAll_closed I _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _⟩

end Defs

/-! ## Arithmetic helpers -/

theorem inr_ne' {a b : Fin 61} (h : (a : ℕ) ≠ b) : (Sum.inr a : TL) ≠ Sum.inr b :=
  fun e => h (congrArg Fin.val (Sum.inr.inj e))

theorem cmono' {C X Y : ℕ} (h : X ≤ Y) : C * X ≤ C * Y := Nat.mul_le_mul_left C h

theorem sq_le' {u v β : ℕ} (hu : u ≤ β) (hv : v ≤ β) : u * v + u + v + 1 ≤ (β + 1) ^ 2 := by
  have : u * v ≤ β * β := Nat.mul_le_mul hu hv
  nlinarith

theorem lin_le' {u β : ℕ} (hu : u ≤ β) : u + 1 ≤ (β + 1) ^ 2 := by nlinarith

theorem lin2_le' {u v β : ℕ} (hu : u ≤ β) (hv : v ≤ β) : u + v + 1 ≤ (β + 1) ^ 2 := by nlinarith

theorem hdrSyms_len_bound (l : List ℕ) (β : ℕ) (h : ∀ x ∈ l, bitLen x ≤ β) :
    (hdrSyms l).length ≤ l.length * (β + 1) := by
  induction l with
  | nil => simp [hdrSyms]
  | cons a l ih =>
    rw [length_hdrSyms_cons, List.length_cons, Nat.succ_mul]
    have ha := h a List.mem_cons_self
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem le_prod_of_mem' (L : List ℕ) (hL : ∀ t ∈ L, 1 ≤ t) {x : ℕ} (hx : x ∈ L) : x ≤ L.prod :=
  Nat.le_of_dvd (prod_pos_of L hL) (List.dvd_prod hx)

/-! ## Specifications -/

section Specs

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.mvNat_spec (hI : I.Spec Mul C) (X Y : TL) (hXY : X ≠ Y) (B : TL → List Sym) (u v : ℕ)
    (hX : B X = natSyms u) (hY : B Y = natSyms v) (ρ : List (TP I)) :
    HT ρ B (mvNat I X Y) (Function.update (Function.update B X (natSyms v)) Y [])
      (C * (bitLen u + 1) + C * (bitLen v + 1) + C * (bitLen v + 1)) := by
  have hYX : Y ≠ X := Ne.symm hXY
  refine (HT.seq (HT.tdr_spec hI X B u [] TermOK.nil (by rw [hX, List.append_nil]) ρ)
    (HT.seq (HT.tcp_spec hI Y X (by simp [hYX]) _ v [] TermOK.nil
      (by rw [Function.update_of_ne hYX, hY, List.append_nil]) ρ)
    (HT.tdr_spec hI Y _ v [] TermOK.nil
      (by rw [Function.update_of_ne hYX, Function.update_of_ne hYX, hY, List.append_nil])
      ρ))).of_eq ?_ (by omega)
  rw [Function.update_self, List.append_nil, Function.update_idem]

/-- Cost bound of one fold step. -/
def rkStepCost (C KM β : ℕ) : ℕ :=
  17 * (C * (β + 1) ^ 2) + C * (KM * (β + 1) ^ 2) + C + 3 * β + 8

set_option maxHeartbeats 4000000 in
/-- **One fold step.** Field `t` on top of `rSH`, `x` on `x40`, `M` on `x41`, `a` on `ra`, the
temporaries `x46 … x52` empty, all values at most `V` with `bitLen V ≤ β`. -/
theorem HT.rkStep_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (B : TL → List Sym) (x M a t V β : ℕ) (rest : List Sym) (ht : 1 ≤ t)
    (hxV : x ≤ V) (hMV : M ≤ V) (htV : t ≤ V) (haV : a + M / t * (x % t) ≤ V)
    (hβ : bitLen V ≤ β)
    (hSH : B rSH = natSyms t ++ Sym.mark :: rest) (h40 : B x40 = natSyms x)
    (h41 : B x41 = natSyms M) (ha : B ra = natSyms a)
    (h46 : B x46 = []) (h47 : B x47 = []) (h48 : B x48 = []) (h49 : B x49 = [])
    (h50 : B x50 = []) (h51 : B x51 = []) (h52 : B x52 = []) (ρ : List (TP I)) :
    HT ρ B (rkStep I)
      (Function.update (Function.update (Function.update (Function.update (Function.update B
        x40 (natSyms (x / t))) x41 (natSyms (M / t))) ra (natSyms (a + M / t * (x % t))))
        rSH rest) x45 ((natSyms t ++ [Sym.mark]).reverse ++ B x45))
      (rkStepCost C KM β) := by
  have hb : ∀ y, y ≤ V → bitLen y ≤ β := fun y hy => le_trans (WP.W7k2.bitLen_mono hy) hβ
  have bx := hb x hxV
  have bM := hb M hMV
  have bt := hb t htV
  have bMt := hb (M / t) (le_trans (Nat.div_le_self _ _) hMV)
  have bMm := hb (M % t) (le_trans (Nat.mod_lt _ (by omega)).le htV)
  have bxt := hb (x / t) (le_trans (Nat.div_le_self _ _) hxV)
  have bxm := hb (x % t) (le_trans (Nat.mod_lt _ (by omega)).le htV)
  have bp := hb (M / t * (x % t)) (by omega)
  have ba := hb a (by omega)
  have bap := hb (a + M / t * (x % t)) haV
  have hMul' : Mul β ≤ KM * (β + 1) ^ 2 := hMul β
  refine (HT.seq ((HT.tcp_spec hI rSH x46 (by decide) B t (Sym.mark :: rest) (termOK_mark rest)
      hSH ρ).mono (cmono' (lin_le' bt)))
    (HT.seq ((HT.tdm_spec hI x41 x46 x47 x48 (by decide) _ M t [] [] ht TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, h41, List.append_nil])
      (by simp (disch := decide) only [Function.update_self, h46]) ρ).mono
      (cmono' (sq_le' bM bt)))
    (HT.seq ((HT.tdm_spec hI x40 x46 x49 x50 (by decide) _ x t [] [] ht TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, h40, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h46]) ρ).mono
      (cmono' (sq_le' bx bt)))
    (HT.seq ((HT.natMul_spec hI x47 x50 x51 (by decide) (by decide) (by decide) _ β (M / t)
      (x % t) [] [] bMt bxm TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h47])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h50]) ρ).mono
      (show C * Mul β + C + 5 ≤ C * (KM * (β + 1) ^ 2) + C + 5 from
        Nat.add_le_add_right (Nat.add_le_add_right (cmono' hMul') C) 5))
    (HT.seq ((HT.tad_spec hI ra x51 x52 (by decide) _ a (M / t * (x % t)) [] [] TermOK.nil
      TermOK.nil (by simp (disch := decide) only [Function.update_of_ne, ha, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h51]) ρ).mono
      (cmono' (lin2_le' ba bp)))
    (HT.seq ((HT.mvNat_spec hI ra x52 (by decide) _ a (a + M / t * (x % t))
      (by simp (disch := decide) only [Function.update_of_ne, ha])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h52,
        List.append_nil]) ρ).mono (show _ ≤ 3 * (C * (β + 1) ^ 2) by
          have := cmono' (C := C) (lin_le' ba); have := cmono' (C := C) (lin_le' bap); omega))
    (HT.seq ((HT.mvNat_spec hI x40 x49 (by decide) _ x (x / t)
      (by simp (disch := decide) only [Function.update_of_ne, h40])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h49,
        List.append_nil]) ρ).mono (show _ ≤ 3 * (C * (β + 1) ^ 2) by
          have := cmono' (C := C) (lin_le' bx); have := cmono' (C := C) (lin_le' bxt); omega))
    (HT.seq ((HT.mvNat_spec hI x41 x47 (by decide) _ M (M / t)
      (by simp (disch := decide) only [Function.update_of_ne, h41])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h47,
        List.append_nil]) ρ).mono (show _ ≤ 3 * (C * (β + 1) ^ 2) by
          have := cmono' (C := C) (lin_le' bM); have := cmono' (C := C) (lin_le' bMt); omega))
    (HT.seq ((HT.tdr_spec hI x46 _ t [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h46,
        List.append_nil]) ρ).mono (cmono' (lin_le' bt)))
    (HT.seq ((HT.tdr_spec hI x48 _ (M % t) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h48,
        List.append_nil]) ρ).mono (cmono' (lin_le' bMm)))
    (HT.seq ((HT.tdr_spec hI x50 _ (x % t) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h50,
        List.append_nil]) ρ).mono (cmono' (lin_le' bxm)))
    (HT.seq ((HT.tdr_spec hI x51 _ (M / t * (x % t)) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h51,
        List.append_nil]) ρ).mono (cmono' (lin_le' bp)))
      ((HT.moveThru_spec rSH x45 (by decide) ρ (natSyms t) rest (mark_not_mem_natSyms t) _
        (by simp (disch := decide) only [Function.update_of_ne, hSH])).mono
        (show 3 * (natSyms t).length + 3 ≤ 3 * β + 3 by
          rw [length_natSyms]; omega)))))))))))))).of_eq ?_ ?_
  · funext g
    by_cases g1 : g = x40
    · subst g1; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
    by_cases g2 : g = x41
    · subst g2; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
    by_cases g3 : g = ra
    · subst g3; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
    by_cases g4 : g = rSH
    · subst g4; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
    by_cases g5 : g = x45
    · subst g5; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
    by_cases g6 : g = x46
    · subst g6; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h46]
    by_cases g7 : g = x47
    · subst g7; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h47]
    by_cases g8 : g = x48
    · subst g8; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h48]
    by_cases g9 : g = x49
    · subst g9; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h49]
    by_cases g10 : g = x50
    · subst g10; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h50]
    by_cases g11 : g = x51
    · subst g11; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h51]
    by_cases g12 : g = x52
    · subst g12; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h52]
    simp only [Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3,
      Function.update_of_ne g4, Function.update_of_ne g5, Function.update_of_ne g6,
      Function.update_of_ne g7, Function.update_of_ne g8, Function.update_of_ne g9,
      Function.update_of_ne g10, Function.update_of_ne g11, Function.update_of_ne g12]
  · unfold rkStepCost
    omega

/-! ## The rank loop -/

/-- The state of the rank loop after `k` steps (base state `B`). -/
def rkLS (B : TL → List Sym) (L : List ℕ) (r k : ℕ) : TL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update B
    x40 (natSyms (rkSt L r k).1)) x41 (natSyms (rkSt L r k).2.1)) ra
    (natSyms (rkSt L r k).2.2)) rSH (hdrSyms (L.drop k))) x45 (hdrSyms (L.take k)).reverse

/-- The countdown states of the rank loop: counter `c`, `n - c` steps done. -/
def rkCS (B : TL → List Sym) (L : List ℕ) (r n c : ℕ) : TL → List Sym :=
  Function.update (rkLS B L r (n - c)) x44 (natSyms c ++ [])

/-- Cost bound of the rank fragment. -/
def rankCost (C KM β : ℕ) : ℕ :=
  β * (rkStepCost C KM β + C * (β + 1) + C + 1) + 7 * (C * (β + 1)) + 3 * (β * (β + 1)) + 3

theorem hdrSyms_take_succ (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    (hdrSyms (L.take (k + 1))).reverse =
      (natSyms L[k] ++ [Sym.mark]).reverse ++ (hdrSyms (L.take k)).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, hdrSyms_append,
    List.reverse_append, hdrSyms_cons, hdrSyms_nil]

theorem hdrSyms_drop_eq (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    hdrSyms (L.drop k) = natSyms L[k] ++ Sym.mark :: hdrSyms (L.drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons hk, hdrSyms_cons]

theorem natSyms_zero'' : natSyms 0 = [] := rfl

set_option maxHeartbeats 4000000 in
/-- **The rank fragment.** From `ru = r`, `rA = ∏ L`, `rI = |L|`, `rSH = hdrSyms L` (`r < ∏ L`,
entries `≥ 1`) and empty `ra`, `x40`, `x41`, `x44 … x52`, push `rankA L r` onto `ra`; every other
stack is restored. -/
theorem HT.rankProg_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (B : TL → List Sym) (L : List ℕ) (r β : ℕ) (hL : ∀ t ∈ L, 1 ≤ t) (hr : r < L.prod)
    (hβA : bitLen L.prod ≤ β) (hβL : L.length ≤ β)
    (hru : B ru = natSyms r) (hA : B rA = natSyms L.prod) (hI' : B rI = natSyms L.length)
    (hSH : B rSH = hdrSyms L) (hra : B ra = [])
    (h40 : B x40 = []) (h41 : B x41 = []) (h44 : B x44 = []) (h45 : B x45 = [])
    (h46 : B x46 = []) (h47 : B x47 = []) (h48 : B x48 = []) (h49 : B x49 = [])
    (h50 : B x50 = []) (h51 : B x51 = []) (h52 : B x52 = []) (ρ : List (TP I)) :
    HT ρ B (rankProg I) (Function.update B ra (natSyms (rankA L r))) (rankCost C KM β) := by
  have hloop := HT.tcd_spec hI x44 [] TermOK.nil (rkCS B L r L.length)
    (fun c => by simp only [rkCS, Function.update_self]) (rkStep I) L.length
    (fun _ => rkStepCost C KM β) ρ (fun c hc => by
      have hk : L.length - (c + 1) < L.length := by omega
      obtain ⟨b1, b2, b3, b4⟩ := rkSt_step_le L r hL hr (L.length - (c + 1)) hk
      have hk1 : L.length - c = L.length - (c + 1) + 1 := by omega
      have e1 : (rkSt L r (L.length - c)).1 =
          (rkSt L r (L.length - (c + 1))).1 / L[L.length - (c + 1)] := by
        rw [hk1, rkSt_succ L r _ hk]; rfl
      have e2 : (rkSt L r (L.length - c)).2.1 =
          (rkSt L r (L.length - (c + 1))).2.1 / L[L.length - (c + 1)] := by
        rw [hk1, rkSt_succ L r _ hk]; rfl
      have e3 : (rkSt L r (L.length - c)).2.2 = (rkSt L r (L.length - (c + 1))).2.2 +
          (rkSt L r (L.length - (c + 1))).2.1 / L[L.length - (c + 1)] *
            ((rkSt L r (L.length - (c + 1))).1 % L[L.length - (c + 1)]) := by
        rw [hk1, rkSt_succ L r _ hk]; rfl
      have e4 : hdrSyms (L.drop (L.length - c)) =
          hdrSyms (L.drop (L.length - (c + 1) + 1)) := by rw [hk1]
      have e5 : (hdrSyms (L.take (L.length - c))).reverse =
          (natSyms L[L.length - (c + 1)] ++ [Sym.mark]).reverse ++
            (hdrSyms (L.take (L.length - (c + 1)))).reverse := by
        rw [hk1, hdrSyms_take_succ L _ hk]
      refine (HT.rkStep_spec hI hMul _ (rkSt L r (L.length - (c + 1))).1
        (rkSt L r (L.length - (c + 1))).2.1 (rkSt L r (L.length - (c + 1))).2.2
        L[L.length - (c + 1)] L.prod β (hdrSyms (L.drop (L.length - (c + 1) + 1)))
        (hL _ (by simp)) b1 b2 b3 b4 hβA
        (by simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          Function.update_self, hdrSyms_drop_eq L _ hk])
        (by simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          Function.update_self])
        (by simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          Function.update_self])
        (by simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          Function.update_self])
        (by simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          h46])
        (by simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          h47])
        (by simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          h48])
        (by simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          h49])
        (by simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          h50])
        (by simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          h51])
        (by simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          h52]) ρ).of_eq ?_ le_rfl
      funext g
      by_cases g1 : g = x40
      · subst g1
        simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          Function.update_self, e1]
      by_cases g2 : g = x41
      · subst g2
        simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          Function.update_self, e2]
      by_cases g3 : g = ra
      · subst g3
        simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          Function.update_self, e3]
      by_cases g4 : g = rSH
      · subst g4
        simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          Function.update_self, e4]
      by_cases g5 : g = x45
      · subst g5
        simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          Function.update_self, e5]
      by_cases g6 : g = x44
      · subst g6
        simp (disch := decide) only [rkCS, rkLS, Function.update_idem, Function.update_of_ne,
          Function.update_self]
      simp only [rkCS, rkLS, Function.update_of_ne g1, Function.update_of_ne g2,
        Function.update_of_ne g3, Function.update_of_ne g4, Function.update_of_ne g5,
        Function.update_of_ne g6])
  -- the start and the end of the loop
  have hstart : Function.update (Function.update (Function.update B x40 (natSyms r ++ B x40)) x41
      (natSyms L.prod ++ Function.update B x40 (natSyms r ++ B x40) x41)) x44
      (natSyms L.length ++ Function.update (Function.update B x40 (natSyms r ++ B x40)) x41
        (natSyms L.prod ++ Function.update B x40 (natSyms r ++ B x40) x41) x44) =
      rkCS B L r L.length L.length := by
    funext g
    by_cases g1 : g = x40
    · subst g1
      simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self,
        Nat.sub_self, rkSt_zero, h40, List.append_nil]
    by_cases g2 : g = x41
    · subst g2
      simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self,
        Nat.sub_self, rkSt_zero, h41, List.append_nil]
    by_cases g3 : g = x44
    · subst g3
      simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self, h44]
    by_cases g4 : g = ra
    · subst g4
      simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self,
        Nat.sub_self, rkSt_zero, hra, natSyms_zero'']
    by_cases g5 : g = rSH
    · subst g5
      simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self,
        Nat.sub_self, List.drop_zero, hSH]
    by_cases g6 : g = x45
    · subst g6
      simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self,
        Nat.sub_self, List.take_zero, hdrSyms_nil, List.reverse_nil, h45]
    simp only [rkCS, rkLS, Function.update_of_ne g1, Function.update_of_ne g2,
      Function.update_of_ne g3, Function.update_of_ne g4, Function.update_of_ne g5,
      Function.update_of_ne g6]
  -- bounds
  have hP1 : 1 ≤ L.prod := prod_pos_of L hL
  have hbr : bitLen r ≤ β := le_trans (WP.W7k2.bitLen_mono hr.le) hβA
  have hbn : bitLen L.length ≤ β := le_trans (WP.W7k2.bitLen_le_self _) hβL
  obtain ⟨hinv1, hinv2⟩ := rkSt_inv L r hL L.length le_rfl
  have hbx : bitLen (rkSt L r L.length).1 ≤ β :=
    le_trans (WP.W7k2.bitLen_mono (by omega : (rkSt L r L.length).1 ≤ L.prod)) hβA
  have hbM : bitLen (rkSt L r L.length).2.1 ≤ β :=
    le_trans (WP.W7k2.bitLen_mono (by omega : (rkSt L r L.length).2.1 ≤ L.prod)) hβA
  have hHL : (hdrSyms (L.take L.length)).length ≤ L.length * (β + 1) := by
    have h := hdrSyms_len_bound (L.take L.length) β (fun x hx =>
      le_trans (WP.W7k2.bitLen_mono (le_prod_of_mem' L hL (List.mem_of_mem_take hx))) hβA)
    have h2 : (L.take L.length).length ≤ L.length := List.length_take_le _ _
    exact le_trans h (Nat.mul_le_mul_right _ h2)
  have hloopc := loopCost_le_unif (fun c => C * (bitLen (c + 1) + 1) + rkStepCost C KM β + C)
    (C * (β + 1) + rkStepCost C KM β + C) L.length (fun c hc => by
      have : bitLen (c + 1) ≤ β := le_trans (WP.W7k2.bitLen_le_self _) (by omega)
      have := cmono' (C := C) (show bitLen (c + 1) + 1 ≤ β + 1 by omega)
      omega)
  have hl2 : L.length * (C * (β + 1) + rkStepCost C KM β + C + 1) ≤
      β * (rkStepCost C KM β + C * (β + 1) + C + 1) := by
    rw [show C * (β + 1) + rkStepCost C KM β + C + 1 = rkStepCost C KM β + C * (β + 1) + C + 1
      by ring]
    exact Nat.mul_le_mul_right _ hβL
  have hl3 : L.length * (β + 1) ≤ β * (β + 1) := Nat.mul_le_mul_right _ hβL
  have hC1 : C ≤ C * (β + 1) := Nat.le_mul_of_pos_right C (by omega)
  rw [← hstart] at hloop
  refine (HT.seq ((HT.tcp_spec hI ru x40 (by decide) B r [] TermOK.nil
      (by rw [hru, List.append_nil]) ρ).mono (cmono' (show bitLen r + 1 ≤ β + 1 by omega)))
    (HT.seq ((HT.tcp_spec hI rA x41 (by decide) _ L.prod [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hA, List.append_nil]) ρ).mono
      (cmono' (show bitLen L.prod + 1 ≤ β + 1 by omega)))
    (HT.seq ((HT.tcp_spec hI rI x44 (by decide) _ L.length [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hI', List.append_nil]) ρ).mono
      (cmono' (show bitLen L.length + 1 ≤ β + 1 by omega)))
    (HT.seq hloop
    (HT.seq (HT.moveAll_spec x45 rSH (by decide) ρ (hdrSyms (L.take L.length)).reverse _
      (by simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self,
        Nat.sub_zero]))
    (HT.seq ((HT.tdr_spec hI x40 _ (rkSt L r L.length).1 [] TermOK.nil
      (by simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self,
        Nat.sub_zero, List.append_nil]) ρ).mono
      (cmono' (show bitLen (rkSt L r L.length).1 + 1 ≤ β + 1 by omega)))
    ((HT.tdr_spec hI x41 _ (rkSt L r L.length).2.1 [] TermOK.nil
      (by simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self,
        Nat.sub_zero, List.append_nil]) ρ).mono
      (cmono' (show bitLen (rkSt L r L.length).2.1 + 1 ≤ β + 1 by omega))))))))).of_eq ?_ ?_
  · funext g
    by_cases g1 : g = ra
    · subst g1
      simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self,
        Nat.sub_zero, rankA_eq_rkSt]
    by_cases g2 : g = rSH
    · subst g2
      simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self,
        Nat.sub_zero, List.reverse_reverse]
      rw [← hdrSyms_append, List.take_append_drop, hSH]
    by_cases g3 : g = x45
    · subst g3
      simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self, h45]
    by_cases g4 : g = x40
    · subst g4
      simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self, h40]
    by_cases g5 : g = x41
    · subst g5
      simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self, h41]
    by_cases g6 : g = x44
    · subst g6
      simp (disch := decide) only [rkCS, rkLS, Function.update_of_ne, Function.update_self, h44,
        natSyms_zero'', List.append_nil]
    simp only [rkCS, rkLS, Function.update_of_ne g1, Function.update_of_ne g2,
      Function.update_of_ne g3, Function.update_of_ne g4, Function.update_of_ne g5,
      Function.update_of_ne g6]
  · rw [List.length_reverse]
    unfold rankCost
    omega

end Specs

end SubNLogN.Machine.Tables.TapPhAux
