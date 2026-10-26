/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.TapPhRank
import SubNLogN.Machine.Tables.TapPhBlockStmt
import IntMulTM.SpecFacts

/-!
# K6 (`Machine/Tables/TapPh.lean`): the tap phase from one tap block

**Scope (honest summary).** Proves `tapPhase_of_block : TapBlockStmt → TapPhaseStmt`
(`TapPhaseStmt.lean`, `TapPhBlockStmt.lean`); the block statement is an explicit hypothesis until
proved. The program `tapProg blk`: fetch `d` (header field `8`) onto the axis counter `rAx`,
decrement it, `rI := 1`; then `d - 1` times the axis body (axis `i` = the value of `rI`):
`axPre` fetches `t_i` (header field `i + 9`) onto `rT` and computes `rDen := 2·(t_i·A_i)`, the
block `blk` pushes the tap block of axis `i` and its `mark` onto `tapTab`, `axSuf` pushes `t_i`
onto the lower shape `rSH`, sets `rA := A_i·t_i`, `rI := i + 1` and drops `rT`, `rDen`; finally
`rI` is dropped. The axes run `1, …, d-1`, i.e. counter `c` handles `(spreadOrder d)[c] = d-1-c`.
Cost: the blocks give `Σ_i tapAxisCost b i = tapPart b + tapTabLen b`; the `d` header fetches and
the counter arithmetic are bounded by the setup budget `(|hdrSyms b.hdr| + 1)^3`.
-/

namespace SubNLogN.Machine.Tables.TapPhAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Machine.Tables
  SubNLogN.Math.Bridge SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common

/-! ## List facts -/

theorem deconvOrder_succ'' (n : ℕ) :
    deconvOrder (n + 1) = (List.finRange n).map Fin.succ := by
  unfold deconvOrder
  rw [List.finRange_succ, List.filter_cons]
  simp only [Fin.val_zero, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte]
  rw [List.filter_eq_self]
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  simp

theorem spreadOrder_eq_reverse (d : ℕ) : spreadOrder d = (deconvOrder d).reverse := by
  unfold spreadOrder deconvOrder
  rw [List.filter_reverse]

theorem length_spreadOrder' (d : ℕ) : (spreadOrder d).length = d - 1 := by
  cases d with
  | zero => simp [spreadOrder]
  | succ n => simp [spreadOrder_eq_reverse, deconvOrder_succ'']

/-- Counter `c` of the axis loop handles axis `d - 1 - c`. -/
theorem spreadOrder_getElem' (d c : ℕ) (hc : c < (spreadOrder d).length) :
    ((spreadOrder d)[c] : ℕ) = d - 1 - c := by
  cases d with
  | zero => simp [spreadOrder] at hc
  | succ n =>
    have hc' : c < n := by rw [length_spreadOrder'] at hc; omega
    simp only [spreadOrder_eq_reverse, deconvOrder_succ'', List.getElem_reverse,
      List.getElem_map, List.getElem_finRange, Fin.val_succ, Fin.val_cast, List.length_map,
      List.length_finRange]
    omega

theorem sum_range_getD (l : List ℕ) : ∑ c ∈ Finset.range l.length, l.getD c 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]
    omega

/-- The tap part plus the tap table length is the sum of the per-axis costs. -/
theorem tapPart_add_tapTabLen (b : BrPar) :
    tapPart b + tapTabLen b = ((spreadOrder b.d).map (tapAxisCost b)).sum := by
  unfold tapPart tapTabLen tapAxisCost
  rw [← List.sum_map_add]

/-! ## Header facts -/

theorem hdr_len (b : BrPar) : b.hdr.length = 9 + b.d := by
  simp [BrPar.hdr]
  omega

theorem hdr_get_d (b : BrPar) (h : 8 < b.hdr.length) : b.hdr[8] = b.d := by
  simp [BrPar.hdr]

theorem hdr_get_t (b : BrPar) (i : ℕ) (hi : i < b.d) (h : i + 9 < b.hdr.length) :
    b.hdr[i + 9] = b.t ⟨i, hi⟩ := by
  simp only [BrPar.hdr]
  rw [List.getElem_append_right (by simp)]
  simp

theorem d_le_hdrLen (b : BrPar) : b.d ≤ (hdrSyms b.hdr).length := by
  have := length_le_length_hdrSyms b.hdr
  rw [hdr_len] at this
  omega

/-! ## Programs -/

section Defs

variable (I : TB)

/-- Axis prologue: `rT := t_i` (header field `i + 9`, `i` on `rI`), `rDen := 2·(t_i·A_i)`. -/
def axPre : TP I :=
  (tnat I x40 9).seq ((tad I rI x40 x41).seq ((tdr I x40).seq ((fetchProg I x41 x40 rT).seq
    ((natMul I rT rA x40).seq ((tnat I x41 2).seq ((natMul I x41 x40 rDen).seq
    ((tdr I x40).seq (tdr I x41))))))))

/-- Axis epilogue: `rSH := t_i :: …`, `rA := A_i·t_i`, `rI := i + 1`, drop `rT`, `rDen`. -/
def axSuf : TP I :=
  (tpush I rSH .mark).seq ((tcp I rT rSH).seq ((natMul I rA rT x40).seq ((tdr I rA).seq
    ((tcp I x40 rA).seq ((tdr I x40).seq ((tic I rI).seq ((tdr I rT).seq (tdr I rDen))))))))

/-- One axis of the tap phase. -/
def axisBody (blk : TP I) : TP I := (axPre I).seq (blk.seq (axSuf I))

/-- The tap phase. -/
def tapProg (blk : TP I) : TP I :=
  (tnat I x40 8).seq ((fetchProg I x40 x41 rAx).seq ((tdc I rAx).seq ((tnat I rI 1).seq
    ((tcd I rAx (axisBody I blk)).seq (tdr I rI)))))

theorem axPre_closed : (axPre I).Closed :=
  ⟨pushBits_closed _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, fetchProg_closed I _ _ _,
    natMul_closed I _ _ _, pushBits_closed _ _, natMul_closed I _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _⟩

theorem axSuf_closed : (axSuf I).Closed :=
  ⟨trivial, callI_closed _ _ _ _, natMul_closed I _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _,
    callI_closed _ _ _ _⟩

theorem axisBody_closed {blk : TP I} (h : blk.Closed) : (axisBody I blk).Closed :=
  ⟨axPre_closed I, h, axSuf_closed I⟩

theorem tapProg_closed {blk : TP I} (h : blk.Closed) : (tapProg I blk).Closed :=
  ⟨pushBits_closed _ _, fetchProg_closed I _ _ _, callI_closed _ _ _ _, pushBits_closed _ _,
    tcd_closed I _ _ (axisBody_closed I h), callI_closed _ _ _ _⟩

end Defs

/-! ## The axis prologue and epilogue -/

/-- Cost of the axis prologue. -/
def axPreCost (C KM H W i : ℕ) : ℕ :=
  fetchCost C H + 2 * (C * (KM * (W + 1) ^ 2) + C + 5) + 4 * (C * (W + i + 11)) + 13

/-- Cost of the axis epilogue. -/
def axSufCost (C KM W i : ℕ) : ℕ :=
  C * (KM * (W + 1) ^ 2) + C + 5 + 7 * (C * (W + i + 1)) + 1

section Specs

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

set_option maxHeartbeats 4000000 in
theorem HT.axPre_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (B : TL → List Sym) (hs : List ℕ) (rpar : List Sym) (i t A W : ℕ) (hk : i + 9 < hs.length)
    (hti : hs[i + 9] = t) (hW : bitLen (2 * t * A) ≤ W) (ht1 : 1 ≤ t) (hA1 : 1 ≤ A)
    (hP : B sPar = hdrSyms hs ++ rpar) (hrI : B rI = natSyms i) (hA : B rA = natSyms A)
    (hT : B rT = []) (hD : B rDen = []) (h40 : B x40 = []) (h41 : B x41 = [])
    (ρ : List (TP I)) :
    HT ρ B (axPre I)
      (Function.update (Function.update B rT (natSyms t)) rDen (natSyms (2 * t * A)))
      (axPreCost C KM (hdrSyms hs).length W i) := by
  have hb : ∀ y, y ≤ 2 * t * A → bitLen y ≤ W := fun y hy =>
    le_trans (WP.W7k2.bitLen_mono hy) hW
  have htA : t * A ≤ 2 * t * A := by nlinarith
  have bt : bitLen t ≤ W := hb t (by nlinarith)
  have bA : bitLen A ≤ W := hb A (by nlinarith)
  have btA : bitLen (t * A) ≤ W := hb _ htA
  have b2 : bitLen 2 ≤ W := hb 2 (by nlinarith)
  have b9 : bitLen 9 ≤ 9 := WP.W7k2.bitLen_le_self 9
  have b2' : bitLen 2 ≤ 2 := WP.W7k2.bitLen_le_self 2
  have bi : bitLen i ≤ i := WP.W7k2.bitLen_le_self i
  have hMul' : Mul W ≤ KM * (W + 1) ^ 2 := hMul W
  refine (HT.seq (HT.tnat_spec x40 9 B ρ)
    (HT.seq ((HT.tad_spec hI rI x40 x41 (by decide) _ i 9 [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hrI, List.append_nil])
      (by simp (disch := decide) only [Function.update_self, h40]) ρ).mono
      (cmono' (show bitLen i + bitLen 9 + 1 ≤ W + i + 11 by omega)))
    (HT.seq ((HT.tdr_spec hI x40 _ 9 [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h40]) ρ).mono
      (cmono' (show bitLen 9 + 1 ≤ W + i + 11 by omega)))
    (HT.seq (HT.fetch_spec hI x41 x40 rT (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ hs (i + 9) hk [] rpar TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h41])
      (by simp (disch := decide) only [Function.update_of_ne, hP])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self]) ρ)
    (HT.seq ((HT.natMul_spec hI rT rA x40 (by decide) (by decide) (by decide) _ W t A [] [] bt bA
      TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, hti, hT])
      (by simp (disch := decide) only [Function.update_of_ne, hA, List.append_nil]) ρ).mono
      (show C * Mul W + C + 5 ≤ C * (KM * (W + 1) ^ 2) + C + 5 from
        Nat.add_le_add_right (Nat.add_le_add_right (cmono' hMul') C) 5))
    (HT.seq (HT.tnat_spec x41 2 _ ρ)
    (HT.seq ((HT.natMul_spec hI x41 x40 rDen (by decide) (by decide) (by decide) _ W 2 (t * A)
      [] [] b2 btA TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h41])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h40]) ρ).mono
      (show C * Mul W + C + 5 ≤ C * (KM * (W + 1) ^ 2) + C + 5 from
        Nat.add_le_add_right (Nat.add_le_add_right (cmono' hMul') C) 5))
    (HT.seq ((HT.tdr_spec hI x40 _ (t * A) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h40]) ρ).mono
      (cmono' (show bitLen (t * A) + 1 ≤ W + i + 11 by omega)))
    ((HT.tdr_spec hI x41 _ 2 [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h41]) ρ).mono
      (cmono' (show bitLen 2 + 1 ≤ W + i + 11 by omega))))))))))).of_eq ?_ ?_
  · funext g
    by_cases g1 : g = rT
    · subst g1
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, hti, hT,
        List.append_nil]
    by_cases g2 : g = rDen
    · subst g2
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, hD,
        List.append_nil, Nat.mul_assoc]
    by_cases g3 : g = x40
    · subst g3; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h40]
    by_cases g4 : g = x41
    · subst g4; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h41]
    simp only [Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3,
      Function.update_of_ne g4]
  · unfold axPreCost
    have : bitLen 9 + 1 ≤ 10 := by omega
    have : bitLen 2 + 1 ≤ 3 := by omega
    omega

set_option maxHeartbeats 4000000 in
theorem HT.axSuf_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    (B : TL → List Sym) (L : List ℕ) (i t A D W : ℕ)
    (hbt : bitLen t ≤ W) (hbA : bitLen A ≤ W) (hbAt : bitLen (A * t) ≤ W) (hbD : bitLen D ≤ W)
    (hT : B rT = natSyms t) (hD : B rDen = natSyms D) (hSH : B rSH = hdrSyms L)
    (hA : B rA = natSyms A) (hrI : B rI = natSyms i) (h40 : B x40 = []) (ρ : List (TP I)) :
    HT ρ B (axSuf I)
      (Function.update (Function.update (Function.update (Function.update (Function.update B
        rSH (hdrSyms (t :: L))) rA (natSyms (A * t))) rI (natSyms (i + 1))) rT []) rDen [])
      (axSufCost C KM W i) := by
  have bi : bitLen i ≤ i := WP.W7k2.bitLen_le_self i
  have hMul' : Mul W ≤ KM * (W + 1) ^ 2 := hMul W
  refine (HT.seq (HT.tpush_spec rSH .mark B ρ)
    (HT.seq ((HT.tcp_spec hI rT rSH (by decide) _ t [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hT, List.append_nil]) ρ).mono
      (cmono' (show bitLen t + 1 ≤ W + i + 1 by omega)))
    (HT.seq ((HT.natMul_spec hI rA rT x40 (by decide) (by decide) (by decide) _ W A t [] [] hbA
      hbt TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hA, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hT, List.append_nil]) ρ).mono
      (show C * Mul W + C + 5 ≤ C * (KM * (W + 1) ^ 2) + C + 5 from
        Nat.add_le_add_right (Nat.add_le_add_right (cmono' hMul') C) 5))
    (HT.seq ((HT.tdr_spec hI rA _ A [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hA, List.append_nil]) ρ).mono
      (cmono' (show bitLen A + 1 ≤ W + i + 1 by omega)))
    (HT.seq ((HT.tcp_spec hI x40 rA (by decide) _ (A * t) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h40]) ρ).mono
      (cmono' (show bitLen (A * t) + 1 ≤ W + i + 1 by omega)))
    (HT.seq ((HT.tdr_spec hI x40 _ (A * t) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h40]) ρ).mono
      (cmono' (show bitLen (A * t) + 1 ≤ W + i + 1 by omega)))
    (HT.seq ((HT.tic_spec hI rI _ i [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hrI, List.append_nil]) ρ).mono
      (cmono' (show bitLen i + 1 ≤ W + i + 1 by omega)))
    (HT.seq ((HT.tdr_spec hI rT _ t [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hT, List.append_nil]) ρ).mono
      (cmono' (show bitLen t + 1 ≤ W + i + 1 by omega)))
    ((HT.tdr_spec hI rDen _ D [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hD, List.append_nil]) ρ).mono
      (cmono' (show bitLen D + 1 ≤ W + i + 1 by omega))))))))))).of_eq ?_ ?_
  · funext g
    by_cases g1 : g = rSH
    · subst g1
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, hSH,
        hdrSyms_cons, List.append_nil]
    by_cases g2 : g = rA
    · subst g2
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, h40,
        List.append_nil]
    by_cases g3 : g = rI
    · subst g3
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, List.append_nil]
    by_cases g4 : g = rT
    · subst g4; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
    by_cases g5 : g = rDen
    · subst g5; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
    by_cases g6 : g = x40
    · subst g6; simp (disch := decide) only [Function.update_of_ne, Function.update_self, h40]
    simp only [Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3,
      Function.update_of_ne g4, Function.update_of_ne g5, Function.update_of_ne g6]
  · unfold axSufCost
    omega

end Specs

/-! ## One axis -/

/-- The body of `TapBlockStmt` for a fixed block program `blk` and constant `K`. -/
def BlkSpec (I : TB) (C KM K : ℕ) (blk : TP I) : Prop :=
  ∀ (b : BrPar) (i : Fin b.d) (B : TL → List Sym),
    ShapeOK b.t → 1 ≤ b.ω → 1 ≤ b.wT →
    CArrFits b.wT (tapBlock b.t b.P (tabOf b.ω b.P b.t) i) →
    B rP = natSyms b.P → B rW = natSyms b.ω → B rB = natSyms (tapPrec b.P) →
    B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec b.P))).1 →
    B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec b.P))).1 →
    B rPW = intSyms ((2 ^ b.wT : ℕ) : ℤ) → B rPW1 = intSyms ((2 ^ (b.wT + 1) : ℕ) : ℤ) →
    B rT = natSyms (b.t i) → B rA = natSyms (prefixProd b.t i) →
    B rDen = natSyms (2 * b.t i * prefixProd b.t i) → B rI = natSyms (i : ℕ) →
    B rSH = hdrSyms (lowerShape b.t i) → B ru = [] → B ra = [] →
    (∀ j : Fin 61, 40 ≤ (j : ℕ) → B (.inr j) = []) →
    HT [] B blk
      (Function.update B sTap
        (carrSyms b.wT (tapBlock b.t b.P (tabOf b.ω b.P b.t) i) ++ Sym.mark :: B sTap))
      (K * (C + 1) * (KM + 1) * tapAxisCost b i)

/-- Cost of one axis. -/
def axisCost (C KM KB H W i ax : ℕ) : ℕ :=
  axPreCost C KM H W i + (KB * (C + 1) * (KM + 1) * ax + axSufCost C KM W i)

theorem inr_ne_ge {j : Fin 61} (k : Fin 61) (hk : (k : ℕ) < 40) (hj : 40 ≤ (j : ℕ)) :
    (Sum.inr j : TL) ≠ Sum.inr k :=
  inr_ne' (by omega)

theorem prefixProd_pos' (b : BrPar) (hS : ShapeOK b.t) (i : ℕ) (hi : i ≤ b.d) :
    1 ≤ prefixProd b.t i := by
  rw [← lowerShape_prod b.t i hi]
  exact prod_pos_of _ (fun x hx => le_trans (by norm_num)
    (lowerShape_ge b.t (fun j => (hS j).1) i x hx))

theorem bitLen_eq_size' (n : ℕ) : bitLen n = Nat.size n := IntMulTM.length_encodeNat n

/-- `(bitLen (2·t_i·A_i) + 1)^2` is at most the axis cost (it is at most `tabUnit b i`). -/
theorem W_sq_le (b : BrPar) (hS : ShapeOK b.t) (i : ℕ) (hi : i < b.d) :
    (bitLen (2 * b.t ⟨i, hi⟩ * prefixProd b.t i) + 1) ^ 2 ≤ tapAxisCost b ⟨i, hi⟩ := by
  have hA := prefixProd_pos' b hS i hi.le
  have h1 : (bitLen (2 * b.t ⟨i, hi⟩ * prefixProd b.t i) + 1) ^ 2 ≤ tabUnit b ⟨i, hi⟩ := by
    unfold tabUnit
    rw [bitLen_eq_size']
    calc (Nat.size (2 * b.t ⟨i, hi⟩ * prefixProd b.t i) + 1) ^ 2
        ≤ (Nat.size (2 * b.t ⟨i, hi⟩ * prefixProd b.t i) + 1) ^ 5 :=
          Nat.pow_le_pow_right (by omega) (by norm_num)
      _ ≤ _ := Nat.pow_le_pow_left (by simp only [Fin.val_mk]; omega) 5
  have h2 : tabUnit b ⟨i, hi⟩ ≤ prefixProd b.t ↑(⟨i, hi⟩ : Fin b.d) *
      ((2 * b.P + 1) * (2 * b.P + 1) * tabUnit b ⟨i, hi⟩) := by
    have h3 : 1 ≤ prefixProd b.t ↑(⟨i, hi⟩ : Fin b.d) * ((2 * b.P + 1) * (2 * b.P + 1)) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    calc tabUnit b ⟨i, hi⟩ = 1 * tabUnit b ⟨i, hi⟩ := (one_mul _).symm
      _ ≤ (prefixProd b.t ↑(⟨i, hi⟩ : Fin b.d) * ((2 * b.P + 1) * (2 * b.P + 1))) *
          tabUnit b ⟨i, hi⟩ := Nat.mul_le_mul_right _ h3
      _ = _ := by ring
  unfold tapAxisCost
  omega

section AxisSpec

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

set_option maxHeartbeats 4000000 in
/-- **One axis** `i` (`1 ≤ i < d`): push the tap block of axis `i` and its `mark`, extend the lower
shape by `t_i`, `rA := A_{i+1}`, `rI := i + 1`; all other stacks restored. -/
theorem HT.axisBody_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    {blk : TP I} {KB : ℕ} (hblk : BlkSpec I C KM KB blk)
    (b : BrPar) (i : ℕ) (hi : i < b.d) (B : TL → List Sym) (rpar : List Sym)
    (hS : ShapeOK b.t) (hω : 1 ≤ b.ω) (hw : 1 ≤ b.wT)
    (hfit : CArrFits b.wT (tapBlock b.t b.P (tabOf b.ω b.P b.t) ⟨i, hi⟩))
    (hpar : B sPar = hdrSyms b.hdr ++ rpar)
    (hPr : B rP = natSyms b.P) (hWr : B rW = natSyms b.ω) (hBr : B rB = natSyms (tapPrec b.P))
    (hPi : B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec b.P))).1)
    (hLn : B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec b.P))).1)
    (hPW : B rPW = intSyms ((2 ^ b.wT : ℕ) : ℤ))
    (hPW1 : B rPW1 = intSyms ((2 ^ (b.wT + 1) : ℕ) : ℤ))
    (hrI : B rI = natSyms i) (hSH : B rSH = hdrSyms (lowerShape b.t i))
    (hA : B rA = natSyms (prefixProd b.t i)) (hT : B rT = []) (hD : B rDen = [])
    (hru : B ru = []) (hra : B ra = [])
    (htmp : ∀ j : Fin 61, 40 ≤ (j : ℕ) → B (.inr j) = []) :
    HT [] B (axisBody I blk)
      (Function.update (Function.update (Function.update (Function.update B sTap
        (carrSyms b.wT (tapBlock b.t b.P (tabOf b.ω b.P b.t) ⟨i, hi⟩) ++ Sym.mark :: B sTap))
        rSH (hdrSyms (lowerShape b.t (i + 1)))) rA (natSyms (prefixProd b.t (i + 1))))
        rI (natSyms (i + 1)))
      (axisCost C KM KB (hdrSyms b.hdr).length (bitLen (2 * b.t ⟨i, hi⟩ * prefixProd b.t i)) i
        (tapAxisCost b ⟨i, hi⟩)) := by
  have h40 : B x40 = [] := htmp 40 (by decide)
  have h41 : B x41 = [] := htmp 41 (by decide)
  have ht2 : 2 ≤ b.t ⟨i, hi⟩ := (hS ⟨i, hi⟩).1
  have hA1 : 1 ≤ prefixProd b.t i := prefixProd_pos' b hS i hi.le
  have hk : i + 9 < b.hdr.length := by rw [hdr_len]; omega
  have hb : ∀ y, y ≤ 2 * b.t ⟨i, hi⟩ * prefixProd b.t i →
      bitLen y ≤ bitLen (2 * b.t ⟨i, hi⟩ * prefixProd b.t i) := fun y hy => WP.W7k2.bitLen_mono hy
  have hbt : bitLen (b.t ⟨i, hi⟩) ≤ bitLen (2 * b.t ⟨i, hi⟩ * prefixProd b.t i) :=
    hb _ (by nlinarith)
  have hbA : bitLen (prefixProd b.t i) ≤ bitLen (2 * b.t ⟨i, hi⟩ * prefixProd b.t i) :=
    hb _ (by nlinarith)
  have hbAt : bitLen (prefixProd b.t i * b.t ⟨i, hi⟩) ≤
      bitLen (2 * b.t ⟨i, hi⟩ * prefixProd b.t i) := hb _ (by nlinarith)
  refine (HT.seq (HT.axPre_spec hI hMul B b.hdr rpar i (b.t ⟨i, hi⟩) (prefixProd b.t i)
      (bitLen (2 * b.t ⟨i, hi⟩ * prefixProd b.t i)) hk (hdr_get_t b i hi hk) le_rfl (by omega)
      hA1 hpar hrI hA hT hD h40 h41 [])
    (HT.seq (hblk b ⟨i, hi⟩ _ hS hω hw hfit
      (by simp (disch := decide) only [Function.update_of_ne, hPr])
      (by simp (disch := decide) only [Function.update_of_ne, hWr])
      (by simp (disch := decide) only [Function.update_of_ne, hBr])
      (by simp (disch := decide) only [Function.update_of_ne, hPi])
      (by simp (disch := decide) only [Function.update_of_ne, hLn])
      (by simp (disch := decide) only [Function.update_of_ne, hPW])
      (by simp (disch := decide) only [Function.update_of_ne, hPW1])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [Function.update_of_ne, hA])
      (by simp (disch := decide) only [Function.update_self])
      (by simp (disch := decide) only [Function.update_of_ne, hrI])
      (by simp (disch := decide) only [Function.update_of_ne, hSH])
      (by simp (disch := decide) only [Function.update_of_ne, hru])
      (by simp (disch := decide) only [Function.update_of_ne, hra])
      (fun j hj => by
        rw [Function.update_of_ne (inr_ne_ge 23 (by decide) hj),
          Function.update_of_ne (inr_ne_ge 15 (by decide) hj)]
        exact htmp j hj))
    (HT.axSuf_spec hI hMul _ (lowerShape b.t i) i (b.t ⟨i, hi⟩) (prefixProd b.t i)
      (2 * b.t ⟨i, hi⟩ * prefixProd b.t i) (bitLen (2 * b.t ⟨i, hi⟩ * prefixProd b.t i))
      hbt hbA hbAt le_rfl
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self])
      (by simp (disch := decide) only [Function.update_of_ne, hSH])
      (by simp (disch := decide) only [Function.update_of_ne, hA])
      (by simp (disch := decide) only [Function.update_of_ne, hrI])
      (by simp (disch := decide) only [Function.update_of_ne, h40]) []))).of_eq ?_ le_rfl
  funext g
  by_cases g1 : g = sTap
  · subst g1; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
  by_cases g2 : g = rSH
  · subst g2
    simp (disch := decide) only [Function.update_of_ne, Function.update_self,
      lowerShape_succ'' b.t i hi]
  by_cases g3 : g = rA
  · subst g3
    simp (disch := decide) only [Function.update_of_ne, Function.update_self,
      prefixProd_succ'' b.t i hi]
  by_cases g4 : g = rI
  · subst g4; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
  by_cases g5 : g = rT
  · subst g5; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hT]
  by_cases g6 : g = rDen
  · subst g6; simp (disch := decide) only [Function.update_of_ne, Function.update_self, hD]
  simp only [Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3,
    Function.update_of_ne g4, Function.update_of_ne g5, Function.update_of_ne g6]

end AxisSpec

/-! ## The axis loop -/

/-- The tap blocks (with marks) of the axes `(spreadOrder d).drop c`, i.e. `d-1-c, …, 1`. -/
noncomputable def tapRest (b : BrPar) (c : ℕ) : List Sym :=
  ((spreadOrder b.d).drop c).flatMap fun i =>
    carrSyms b.wT (tapBlock b.t b.P (tabOf b.ω b.P b.t) i) ++ [Sym.mark]

theorem tapRest_step (b : BrPar) (c : ℕ) (hc : c < (spreadOrder b.d).length) :
    tapRest b c = carrSyms b.wT (tapBlock b.t b.P (tabOf b.ω b.P b.t) (spreadOrder b.d)[c]) ++
      Sym.mark :: tapRest b (c + 1) := by
  unfold tapRest
  rw [List.drop_eq_getElem_cons hc, List.flatMap_cons, List.append_assoc]
  rfl

/-- The axis-loop states: counter `c`, the axes `1, …, d-1-c` done. -/
noncomputable def axSt (B : TL → List Sym) (b : BrPar) (c : ℕ) : TL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update B sTap
    (tapRest b c ++ B sTap)) rSH (hdrSyms (lowerShape b.t (b.d - c)))) rA
    (natSyms (prefixProd b.t (b.d - c)))) rI (natSyms (b.d - c))) rAx (natSyms c ++ [])

/-- Per-iteration cost bound of the axis loop (counter `c`). -/
def axLoopCost (C KM KB H : ℕ) (b : BrPar) (c : ℕ) : ℕ :=
  fetchCost C H + (KB + 160) * (C + 1) * (KM + 1) *
    ((spreadOrder b.d).map (tapAxisCost b)).getD c 0 + 11 * (C * H)

theorem axisCost_le (C KM KB H W i ax : ℕ) (hW : (W + 1) ^ 2 ≤ ax) (hiH : i ≤ H) :
    axisCost C KM KB H W i ax ≤
      fetchCost C H + (KB + 160) * (C + 1) * (KM + 1) * ax + 11 * (C * H) := by
  have hax1 : 1 ≤ ax := le_trans (Nat.one_le_pow _ _ (by omega)) hW
  have hX1 : ax ≤ (C + 1) * (KM + 1) * ax := Nat.le_mul_of_pos_left _ (by positivity)
  have hCX : C ≤ (C + 1) * (KM + 1) * ax := by
    have : C * 1 ≤ (C + 1) * (KM + 1) * ax :=
      le_of_le_of_eq (Nat.mul_le_mul (show C ≤ C + 1 by omega)
        (Nat.one_le_iff_ne_zero.2 (by positivity) : 1 ≤ (KM + 1) * ax)) (by ring)
    omega
  have hW1 : W ≤ (W + 1) ^ 2 := by nlinarith
  have e1 : C * (KM * (W + 1) ^ 2) ≤ (C + 1) * (KM + 1) * ax :=
    le_of_le_of_eq (Nat.mul_le_mul (show C ≤ C + 1 by omega)
      (Nat.mul_le_mul (show KM ≤ KM + 1 by omega) hW)) (by ring)
  have eCW : C * W ≤ (C + 1) * (KM + 1) * ax :=
    le_of_le_of_eq (Nat.mul_le_mul (show C ≤ C + 1 by omega)
      (le_trans (le_trans hW1 hW) (Nat.le_mul_of_pos_left ax (by omega) : ax ≤ (KM + 1) * ax)))
      (by ring)
  have eCi : C * i ≤ C * H := Nat.mul_le_mul_left C hiH
  have e2 : C * (W + i + 11) ≤ 12 * ((C + 1) * (KM + 1) * ax) + C * H := by
    have : C * (W + i + 11) = C * W + C * i + 11 * C := by ring
    omega
  have e3 : C * (W + i + 1) ≤ 2 * ((C + 1) * (KM + 1) * ax) + C * H := by
    have : C * (W + i + 1) = C * W + C * i + C := by ring
    omega
  have e4 : (KB + 160) * (C + 1) * (KM + 1) * ax =
      KB * (C + 1) * (KM + 1) * ax + 160 * ((C + 1) * (KM + 1) * ax) := by ring
  unfold axisCost axPreCost axSufCost
  omega

theorem natSyms_zero''' : natSyms 0 = [] := rfl

section LoopSpec

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

set_option maxHeartbeats 8000000 in
/-- **The axis loop**: from `axSt B b (d-1)` to `axSt B b 0`. -/
theorem HT.axLoop_spec (hI : I.Spec Mul C) {KM : ℕ} (hMul : ∀ w, Mul w ≤ KM * (w + 1) ^ 2)
    {blk : TP I} {KB : ℕ} (hblk : BlkSpec I C KM KB blk)
    (b : BrPar) (B : TL → List Sym) (rpar : List Sym)
    (hS : ShapeOK b.t) (hω : 1 ≤ b.ω) (hw : 1 ≤ b.wT)
    (hfit : ∀ i ∈ spreadOrder b.d, CArrFits b.wT (tapBlock b.t b.P (tabOf b.ω b.P b.t) i))
    (hpar : B sPar = hdrSyms b.hdr ++ rpar)
    (hPr : B rP = natSyms b.P) (hWr : B rW = natSyms b.ω) (hBr : B rB = natSyms (tapPrec b.P))
    (hPi : B rPi = intSyms (IntMul.computablePiScaledWithCost (W7.tapPrec (tapPrec b.P))).1)
    (hLn : B rLn = intSyms (IntMul.computableLog2ScaledWithCost (W7.tapPrec (tapPrec b.P))).1)
    (hPW : B rPW = intSyms ((2 ^ b.wT : ℕ) : ℤ))
    (hPW1 : B rPW1 = intSyms ((2 ^ (b.wT + 1) : ℕ) : ℤ))
    (hscr : ∀ j : Fin 61, TapScratch j → B (.inr j) = []) :
    HT [] (axSt B b (b.d - 1)) (tcd I rAx (axisBody I blk)) (axSt B b 0)
      (C + loopCost (fun c => C * (bitLen (c + 1) + 1) +
        axLoopCost C KM KB (hdrSyms b.hdr).length b c + C) (b.d - 1)) := by
  have hT0 : B rT = [] := hscr 15 (by unfold TapScratch; decide)
  have hD0 : B rDen = [] := hscr 23 (by unfold TapScratch; decide)
  have hu0 : B ru = [] := hscr 27 (by unfold TapScratch; decide)
  have ha0 : B ra = [] := hscr 28 (by unfold TapScratch; decide)
  refine HT.tcd_spec hI rAx [] TermOK.nil (axSt B b) (fun c => by
      simp only [axSt, Function.update_self]) (axisBody I blk) (b.d - 1)
    (axLoopCost C KM KB (hdrSyms b.hdr).length b) [] (fun c hc => ?_)
  have hlen : c < (spreadOrder b.d).length := by rw [length_spreadOrder']; omega
  have hi : b.d - (c + 1) < b.d := by omega
  have hsp : (spreadOrder b.d)[c] = ⟨b.d - (c + 1), hi⟩ :=
    Fin.ext (by rw [spreadOrder_getElem' b.d c hlen]; simp only [Fin.val_mk]; omega)
  have hmem : (⟨b.d - (c + 1), hi⟩ : Fin b.d) ∈ spreadOrder b.d := by
    rw [← hsp]; exact List.getElem_mem hlen
  have e1 : b.d - (c + 1) + 1 = b.d - c := by omega
  refine (HT.axisBody_spec hI hMul hblk b (b.d - (c + 1)) hi _ rpar hS hω hw (hfit _ hmem)
    (by simp (disch := decide) only [axSt, Function.update_of_ne, hpar])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, hPr])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, hWr])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, hBr])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, hPi])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, hLn])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, hPW])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, hPW1])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, hT0])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, hD0])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, hu0])
    (by simp (disch := decide) only [axSt, Function.update_of_ne, ha0])
    (fun j hj => by
      simp only [axSt]
      rw [Function.update_of_ne (inr_ne_ge 21 (by decide) hj),
        Function.update_of_ne (inr_ne_ge 21 (by decide) hj),
        Function.update_of_ne (inr_ne_ge 14 (by decide) hj),
        Function.update_of_ne (inr_ne_ge 16 (by decide) hj),
        Function.update_of_ne (inr_ne_ge 22 (by decide) hj),
        Function.update_of_ne (Sum.inr_ne_inl : (Sum.inr j : TL) ≠ Sum.inl 1)]
      exact hscr j (by unfold TapScratch; omega))).of_eq ?_ ?_
  · funext g
    by_cases g1 : g = sTap
    · subst g1
      simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self]
      rw [tapRest_step b c hlen, hsp, List.append_assoc, List.cons_append]
    by_cases g2 : g = rSH
    · subst g2
      simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self, e1]
    by_cases g3 : g = rA
    · subst g3
      simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self, e1]
    by_cases g4 : g = rI
    · subst g4
      simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self, e1]
    by_cases g5 : g = rAx
    · subst g5
      simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self]
    simp only [axSt, Function.update_of_ne g1, Function.update_of_ne g2,
      Function.update_of_ne g3, Function.update_of_ne g4, Function.update_of_ne g5]
  · have hW := W_sq_le b hS (b.d - (c + 1)) hi
    have hiH : b.d - (c + 1) ≤ (hdrSyms b.hdr).length := le_trans (by omega) (d_le_hdrLen b)
    have hg : ((spreadOrder b.d).map (tapAxisCost b)).getD c 0 =
        tapAxisCost b ⟨b.d - (c + 1), hi⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa using hlen), List.getElem_map, hsp]
    unfold axLoopCost
    rw [hg]
    exact axisCost_le _ _ _ _ _ _ _ hW hiH

end LoopSpec

/-! ## Cost arithmetic of the phase -/

theorem fetchCost_le (C H : ℕ) : fetchCost C H ≤ 12 * ((C + 1) * (H + 1) ^ 2) := by
  unfold fetchCost
  have h1 : C + 3 ≤ 3 * (C + 1) := by omega
  have h2 : (H + 2) ^ 2 ≤ 4 * (H + 1) ^ 2 :=
    le_of_le_of_eq (Nat.pow_le_pow_left (show H + 2 ≤ 2 * (H + 1) by omega) 2) (by ring)
  calc (C + 3) * (H + 2) ^ 2 ≤ (3 * (C + 1)) * (4 * (H + 1) ^ 2) := Nat.mul_le_mul h1 h2
    _ = 12 * ((C + 1) * (H + 1) ^ 2) := by ring

theorem sum_axLoop_le (C KM KB H : ℕ) (b : BrPar) (hdH : b.d ≤ H) :
    ∑ c ∈ Finset.range (b.d - 1), (C * (bitLen (c + 1) + 1) +
        axLoopCost C KM KB H b c + C + 1) ≤
      (b.d - 1) * (C * (H + 1) + fetchCost C H + 11 * (C * H) + C + 1) +
        (KB + 160) * (C + 1) * (KM + 1) * (tapPart b + tapTabLen b) := by
  have h1 : ∀ c ∈ Finset.range (b.d - 1), C * (bitLen (c + 1) + 1) +
      axLoopCost C KM KB H b c + C + 1 ≤
      (C * (H + 1) + fetchCost C H + 11 * (C * H) + C + 1) +
        (KB + 160) * (C + 1) * (KM + 1) * ((spreadOrder b.d).map (tapAxisCost b)).getD c 0 := by
    intro c hc
    have hc' := Finset.mem_range.1 hc
    have hb : bitLen (c + 1) ≤ H := le_trans (WP.W7k2.bitLen_le_self _) (by omega)
    have := cmono' (C := C) (show bitLen (c + 1) + 1 ≤ H + 1 by omega)
    unfold axLoopCost
    omega
  calc _ ≤ ∑ c ∈ Finset.range (b.d - 1), ((C * (H + 1) + fetchCost C H + 11 * (C * H) + C + 1) +
        (KB + 160) * (C + 1) * (KM + 1) * ((spreadOrder b.d).map (tapAxisCost b)).getD c 0) :=
        Finset.sum_le_sum h1
    _ = (b.d - 1) * (C * (H + 1) + fetchCost C H + 11 * (C * H) + C + 1) +
        (KB + 160) * (C + 1) * (KM + 1) *
          ∑ c ∈ Finset.range (b.d - 1), ((spreadOrder b.d).map (tapAxisCost b)).getD c 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
          Finset.mul_sum]
    _ = _ := by
        have hl : ((spreadOrder b.d).map (tapAxisCost b)).length = b.d - 1 := by
          rw [List.length_map, length_spreadOrder']
        rw [← hl, sum_range_getD, ← tapPart_add_tapTabLen]

end SubNLogN.Machine.Tables.TapPhAux

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common SubNLogN.Machine.Tables.TapPhAux

set_option maxHeartbeats 8000000 in
/-- **The tap phase from one tap block** (`TapPhaseStmt` from `TapBlockStmt`): the program
`tapProg blk` runs the axes `1, …, d-1`; constant `K = K_block + 220`. -/
theorem tapPhase_of_block (hBlk : TapBlockStmt) : TapPhaseStmt := by
  obtain ⟨KB, hKB⟩ := hBlk
  refine ⟨KB + 220, fun I Mul C KM hI hMul => ?_⟩
  obtain ⟨blk, hcl, hblk⟩ := hKB I Mul C KM hI hMul
  refine ⟨tapProg I blk, tapProg_closed I hcl, fun b rpar B hd2 hS hω hw hfit hpar hPr hWr hBr
    hPi hLn hPW hPW1 hSH hA hscr => ?_⟩
  have h40 : B x40 = [] := hscr 40 (by unfold TapScratch; decide)
  have h41 : B x41 = [] := hscr 41 (by unfold TapScratch; decide)
  have hAx0 : B rAx = [] := hscr 21 (by unfold TapScratch; decide)
  have hI0 : B rI = [] := hscr 14 (by unfold TapScratch; decide)
  have hk8 : 8 < b.hdr.length := by rw [hdr_len]; omega
  have hdH : b.d ≤ (hdrSyms b.hdr).length := d_le_hdrLen b
  have e1 : b.d - (b.d - 1) = 1 := by omega
  have hrest : tapRest b (b.d - 1) = [] := by
    unfold tapRest
    rw [List.drop_eq_nil_of_le (by rw [length_spreadOrder'])]
    rfl
  have hloop := HT.axLoop_spec hI hMul hblk b B rpar hS hω hw hfit hpar hPr hWr hBr hPi hLn hPW
    hPW1 hscr
  refine (HT.seq (HT.tnat_spec x40 8 B [])
    (HT.seq (HT.fetch_spec hI x40 x41 rAx (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ b.hdr 8 hk8 [] rpar TermOK.nil
      (by simp (disch := decide) only [Function.update_self, h40])
      (by simp (disch := decide) only [Function.update_of_ne, hpar])
      (by simp (disch := decide) only [Function.update_of_ne, h41]) [])
    (HT.seq (HT.tdc_spec hI rAx _ (b.d - 1) [] TermOK.nil
      (by
        simp (disch := decide) only [Function.update_of_ne, Function.update_self, hdr_get_d,
          hAx0]
        rw [Nat.sub_add_cancel (by omega)]) [])
    (HT.seq ((HT.tnat_spec rI 1 _ []).of_eq (by
        funext g
        by_cases g1 : g = sTap
        · subst g1
          simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self, hrest,
            List.nil_append]
        by_cases g2 : g = rSH
        · subst g2
          simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self, e1, hSH]
        by_cases g3 : g = rA
        · subst g3
          simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self, e1, hA]
        by_cases g4 : g = rI
        · subst g4
          simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self, e1, hI0,
            List.append_nil]
        by_cases g5 : g = rAx
        · subst g5
          simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self]
        by_cases g6 : g = x40
        · subst g6
          simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self, h40]
        simp only [axSt, Function.update_of_ne g1, Function.update_of_ne g2,
          Function.update_of_ne g3, Function.update_of_ne g4, Function.update_of_ne g5,
          Function.update_of_ne g6]) le_rfl)
    (HT.seq hloop
      (HT.tdr_spec hI rI _ b.d [] TermOK.nil
        (by simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self,
          Nat.sub_zero, List.append_nil]) [])))))).of_eq ?_ ?_
  · funext g
    by_cases g1 : g = sTap
    · subst g1
      simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self]
      rfl
    by_cases g2 : g = rSH
    · subst g2
      simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self,
        Nat.sub_zero]
    by_cases g3 : g = rA
    · subst g3
      simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self,
        Nat.sub_zero]
    by_cases g4 : g = rI
    · subst g4
      simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self, hI0]
    by_cases g5 : g = rAx
    · subst g5
      simp (disch := decide) only [axSt, Function.update_of_ne, Function.update_self, hAx0,
        natSyms_zero''', List.append_nil]
    simp only [axSt, Function.update_of_ne g1, Function.update_of_ne g2, Function.update_of_ne g3,
      Function.update_of_ne g4, Function.update_of_ne g5]
  · -- the cost
    rw [loopCost_eq_sum, show b.setup = ((hdrSyms b.hdr).length + 1) ^ 3 from rfl]
    have hsum := sum_axLoop_le C KM KB (hdrSyms b.hdr).length b hdH
    have hF := fetchCost_le C (hdrSyms b.hdr).length
    generalize (hdrSyms b.hdr).length = H at hdH hsum hF ⊢
    have hb8 : bitLen 8 ≤ 8 := WP.W7k2.bitLen_le_self 8
    have hb1 : bitLen 1 ≤ 1 := WP.W7k2.bitLen_le_self 1
    have hbd : bitLen b.d ≤ H := le_trans (WP.W7k2.bitLen_le_self _) hdH
    have hbd1 : bitLen (b.d - 1 + 1) ≤ H := by rw [Nat.sub_add_cancel (by omega)]; exact hbd
    have hS1 : (C + 1) * (H + 1) ≤ (C + 1) * (H + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (by nlinarith)
    have hS2 : (C + 1) * (H + 1) ^ 2 ≤ (C + 1) * (H + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num))
    have hS0 : 1 ≤ (C + 1) * (H + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    have a4 : C + 1 ≤ (C + 1) * (H + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hCd : C * (bitLen (b.d - 1 + 1) + 1) ≤ (C + 1) * (H + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hCd' : C * (bitLen b.d + 1) ≤ (C + 1) * (H + 1) := Nat.mul_le_mul (by omega) (by omega)
    have hX : C * (H + 1) + fetchCost C H + 11 * (C * H) + C + 1 ≤
        25 * ((C + 1) * (H + 1) ^ 2) := by
      have a1 : C * (H + 1) ≤ (C + 1) * (H + 1) := Nat.mul_le_mul_right _ (by omega)
      have a2 : C * H ≤ (C + 1) * (H + 1) := Nat.mul_le_mul (by omega) (by omega)
      have a3 : (C + 1) * (H + 1) ≤ (C + 1) * (H + 1) ^ 2 :=
        Nat.mul_le_mul_left _ (by nlinarith)
      omega
    have hnX : (b.d - 1) * (C * (H + 1) + fetchCost C H + 11 * (C * H) + C + 1) ≤
        25 * ((C + 1) * (H + 1) ^ 3) := by
      calc (b.d - 1) * (C * (H + 1) + fetchCost C H + 11 * (C * H) + C + 1)
          ≤ (H + 1) * (25 * ((C + 1) * (H + 1) ^ 2)) := Nat.mul_le_mul (by omega) hX
        _ = 25 * ((C + 1) * (H + 1) ^ 3) := by ring
    have hR : (KB + 220) * (C + 1) * (KM + 1) * (tapPart b + tapTabLen b + ((H + 1) ^ 3)) =
        (KB + 160) * (C + 1) * (KM + 1) * (tapPart b + tapTabLen b) +
          60 * ((C + 1) * (KM + 1) * (tapPart b + tapTabLen b)) +
          (KB + 220) * ((C + 1) * (KM + 1) * (H + 1) ^ 3) := by ring
    have h60 : 60 * ((C + 1) * (H + 1) ^ 3) ≤ (KB + 220) * ((C + 1) * (KM + 1) * (H + 1) ^ 3) := by
      have : (C + 1) * (H + 1) ^ 3 ≤ (C + 1) * (KM + 1) * (H + 1) ^ 3 := by
        rw [Nat.mul_right_comm]
        exact Nat.le_mul_of_pos_right _ (by omega)
      have h2 : 60 * ((C + 1) * (H + 1) ^ 3) ≤ 60 * ((C + 1) * (KM + 1) * (H + 1) ^ 3) :=
        Nat.mul_le_mul_left _ this
      have h3 : 60 * ((C + 1) * (KM + 1) * (H + 1) ^ 3) ≤
          (KB + 220) * ((C + 1) * (KM + 1) * (H + 1) ^ 3) := Nat.mul_le_mul_right _ (by omega)
      omega
    rw [hR]
    omega

end SubNLogN.Machine.Tables
