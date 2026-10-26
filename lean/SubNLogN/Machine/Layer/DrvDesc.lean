/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvDescDefs
import SubNLogN.Machine.Calculus.Hdr
import IntMulTM.SpecFacts

/-!
# Layer driver pre-phase: the descriptor kernel from its two parts (`Machine/Layer/DrvDesc.lean`)

**Scope (honest summary).** `drvDesc_of : DrvDescArithStmt → DrvDescPiecesStmt → DrvDescStmt`
(no `sorry`; the hypotheses are the two frozen sub-statements of `Machine/Layer/DrvDescDefs.lean`).

Program (one private stack `V` for the value record, plus the two kernels' scratch):
1. the value kernel (`DrvDescArithStmt`) reads the layer header and pushes the value record
   `hdrSyms (drvDescVals t)` onto `V`;
2. the pieces kernel (`DrvDescPiecesStmt`) reads the record on `V` (restored) and pushes
   `descOfVals …` onto the descriptor stack;
3. `dropHdr V 9` pops the record again.

Math (section 2): `descOfVals` of the record is `drvDescSyms t` (`vals_spec`; uses `padR > 0` and
`piecesOf 0 = []`), and the record has length `≤ (2⌈lg W_c⌉ + 6)·(|hdr| + D·K + 1)`
(`length_vals_le`; `⌈lg W_c⌉ = Nat.clog 2 Wc` stays symbolic and is never evaluated).
Helpers live in `SubNLogN.Machine.Layer.DrvDescAux`.
-/

namespace SubNLogN.Machine.Layer.DrvDescAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Layer
open SubNLogN.Math.Networks (q0Of padR piecesOf piecesAux useRows k0Of mH Wc)

/-! ## 1. Bit lengths -/

theorem bitLen_eq_size (n : ℕ) : bitLen n = Nat.size n := IntMulTM.length_encodeNat n

theorem bitLen_zero' : bitLen 0 = 0 := by rw [bitLen_eq_size, Nat.size_zero]

theorem bitLen_mono {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  rw [bitLen_eq_size, bitLen_eq_size]; exact Nat.size_le_size h

theorem bitLen_mul_le (a b : ℕ) : bitLen (a * b) ≤ bitLen a + bitLen b := by
  rw [bitLen_eq_size, bitLen_eq_size, bitLen_eq_size, Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem bitLen_le_of_le_pow {n k : ℕ} (h : n ≤ 2 ^ k) : bitLen n ≤ k + 1 := by
  rw [bitLen_eq_size, Nat.size_le, pow_succ]
  have := Nat.two_pow_pos k
  omega

theorem bitLen_two_mul_le (d : ℕ) : bitLen (2 * d) ≤ bitLen d + 1 := by
  rw [bitLen_eq_size, bitLen_eq_size, Nat.size_le, pow_succ]
  have := Nat.lt_size_self d
  omega

theorem clog_le_bitLen {b n : ℕ} (hb : 2 ≤ b) : Nat.clog b n ≤ bitLen n := by
  apply Nat.clog_le_of_le_pow
  have h1 : n < 2 ^ bitLen n := by rw [bitLen_eq_size]; exact Nat.lt_size_self n
  have h2 : 2 ^ bitLen n ≤ b ^ bitLen n := Nat.pow_le_pow_left hb _
  omega

theorem length_hdrSyms9 (a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℕ) :
    (hdrSyms [a1, a2, a3, a4, a5, a6, a7, a8, a9]).length =
      bitLen a1 + bitLen a2 + bitLen a3 + bitLen a4 + bitLen a5 + bitLen a6 + bitLen a7 +
        bitLen a8 + bitLen a9 + 9 := by
  rw [Calculus.HdrAux.length_hdrSyms]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- The cost of `dropHdr` is at most five times the header length. -/
theorem dropCost_le (fs : List ℕ) :
    (fs.map fun f => 2 * bitLen f + 5).sum ≤ 5 * (hdrSyms fs).length := by
  rw [Calculus.HdrAux.length_hdrSyms]
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

/-! ## 2. The value record: descriptors and size -/

/-- Abstract form of `q₀ ≤ ⌈lg W⌉·(bitLen d + 1)` (for any `W`). -/
theorem mul_clog_le_aux (W d : ℕ) :
    Nat.clog 2 W * Nat.clog mH (2 * d) ≤ Nat.clog 2 W * (bitLen d + 1) :=
  Nat.mul_le_mul_left _ ((clog_le_bitLen (by norm_num [mH])).trans (bitLen_two_mul_le d))

/-- `q₀ ≤ ⌈lg W_c⌉·(bitLen d + 1)` (`⌈lg W_c⌉` symbolic, never evaluated). -/
theorem q0Of_le (d : ℕ) : q0Of d ≤ Nat.clog 2 Wc * (bitLen d + 1) := mul_clog_le_aux Wc d

/-- Abstract form of `W^{k₀} ≤ 2^{q₀}` (for any `W`, so that `W_c` is never evaluated). -/
theorem pow_clog_le_aux (W d : ℕ) :
    W ^ Nat.clog mH d ≤ 2 ^ (Nat.clog 2 W * Nat.clog mH (2 * d)) := by
  have hW : W ≤ 2 ^ Nat.clog 2 W := Nat.le_pow_clog (by norm_num) _
  have hk : Nat.clog mH d ≤ Nat.clog mH (2 * d) := Nat.clog_mono_right _ (by omega)
  calc W ^ Nat.clog mH d ≤ (2 ^ Nat.clog 2 W) ^ Nat.clog mH d := Nat.pow_le_pow_left hW _
    _ = 2 ^ (Nat.clog 2 W * Nat.clog mH d) := (pow_mul 2 _ _).symm
    _ ≤ 2 ^ (Nat.clog 2 W * Nat.clog mH (2 * d)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hk)

/-- Abstract form of the `padR` bound. -/
theorem padR_le_aux (w q K : ℕ) (hw : w ≤ 2 ^ q) :
    w * ((2 ^ (q * K) + w - 1) / w) ≤ 2 ^ (q * K + q + 1) := by
  have h1 : w * ((2 ^ (q * K) + w - 1) / w) ≤ 2 ^ (q * K) + w - 1 := Nat.mul_div_le _ _
  have h2 : 2 ^ (q * K) ≤ 2 ^ (q * K + q) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ q ≤ 2 ^ (q * K + q) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (q * K + q + 1) = 2 * 2 ^ (q * K + q) := by rw [pow_succ]; ring
  generalize w * ((2 ^ (q * K) + w - 1) / w) = p at h1 ⊢
  generalize 2 ^ (q * K) = a at h1 h2
  generalize 2 ^ q = b at hw h3
  generalize 2 ^ (q * K + q) = c at h2 h3 h4
  omega

/-- `padR ≤ 2^{q₀K + q₀ + 1}` (any `K`). -/
theorem padR_le_pow (d K : ℕ) : padR d K ≤ 2 ^ (q0Of d * K + q0Of d + 1) := by
  unfold padR
  exact padR_le_aux _ _ K (pow_clog_le_aux Wc d)

theorem bitLen_padR_le (d K : ℕ) : bitLen (padR d K) ≤ q0Of d * K + q0Of d + 1 + 1 :=
  bitLen_le_of_le_pow (padR_le_pow d K)

/-- Abstract form of `padR > 0`. -/
theorem padR_pos_aux (w a : ℕ) (hw : 0 < w) (ha : 1 ≤ a) : 0 < w * ((a + w - 1) / w) :=
  Nat.mul_pos hw ((Nat.one_le_div_iff hw).2 (by omega))

theorem padR_pos' (d K : ℕ) : 0 < padR d K := by
  unfold padR
  exact padR_pos_aux _ _ (pow_pos SubNLogN.Math.Networks.Wc_pos _) Nat.one_le_two_pow

theorem piecesOf_zero : piecesOf 0 = [] := by
  unfold piecesOf
  rw [Nat.digits_zero]
  rfl

theorem drvPieces_rows {t : LayerRT} (h : DrvRows t) : drvPieces t = piecesOf (drvD' t) := by
  unfold drvPieces; rw [if_pos h]

theorem drvPieces_not_rows {t : LayerRT} (h : ¬ DrvRows t) : drvPieces t = [] := by
  unfold drvPieces; rw [if_neg h]

theorem drvCtx_hdr (t : LayerRT) (pc : ℕ × ℕ) :
    (drvCtx t 0 pc).hdr = hdrSyms [t.P, t.d, t.r, t.P, t.A * padR t.d t.K, padR t.d t.K, t.K,
      t.D - q0Of t.d, t.S, pc.2, pc.1, t.ρ] := rfl

/-- **The value record and the descriptors.** The record is `[P, d, r, a, R, K, e, S, ρ]` for some
`a, R, e`, and its piece descriptors `descOfVals …` are exactly `drvDescSyms t`: in the rows case
`a = A·padR`, `R = padR`, `e = D - q₀` and `drvPieces t = piecesOf (D - q₀)` (as `padR > 0`); otherwise
`a = R = e = 0`, `drvPieces t = []` and `piecesOf 0 = []`. -/
theorem vals_spec (t : LayerRT) : ∃ a R e : ℕ,
    drvDescVals t = [t.P, t.d, t.r, a, R, t.K, e, t.S, t.ρ] ∧
      descOfVals t.P t.d t.r a R t.K e t.S t.ρ = drvDescSyms t := by
  by_cases hq : q0Of t.d < t.D
  · refine ⟨t.A * padR t.d t.K, padR t.d t.K, t.D - q0Of t.d, ?_, ?_⟩
    · unfold drvDescVals; rw [if_pos hq]
    · have hr : DrvRows t := by
        show q0Of t.d < t.D ∧ 0 < padR t.d t.K
        exact ⟨hq, padR_pos' _ _⟩
      unfold descOfVals drvDescSyms
      rw [drvPieces_rows hr]
      simp only [drvCtx_hdr, drvD']
  · refine ⟨0, 0, 0, ?_, ?_⟩
    · unfold drvDescVals; rw [if_neg hq]
    · have hr : ¬ DrvRows t := fun h => hq h.1
      unfold descOfVals drvDescSyms
      rw [drvPieces_not_rows hr, piecesOf_zero]
      simp only [List.map_nil, List.flatten_nil]

/-- Abstract form of the size bound (all quantities are variables, so that no tactic ever sees
`q₀`, `padR` or `W_c`). -/
theorem vals_len_aux (c0 q R P d r D A S K ρ w : ℕ) (hq : q ≤ c0 * (bitLen d + 1))
    (hR : bitLen R ≤ q * K + q + 1 + 1) :
    (hdrSyms (if q < D then [P, d, r, A * R, R, K, D - q, S, ρ]
      else [P, d, r, 0, 0, K, 0, S, ρ])).length ≤
      (2 * c0 + 6) * ((hdrSyms [P, d, r, D, A, S, K, ρ + 1, w]).length + D * K + 1) := by
  rw [length_hdrSyms9 P d r D A S K (ρ + 1) w]
  have hρ : bitLen ρ ≤ bitLen (ρ + 1) := bitLen_mono (Nat.le_succ _)
  have hb0 := bitLen_zero'
  have hX : bitLen d + 1 ≤ bitLen P + bitLen d + bitLen r + bitLen D + bitLen A + bitLen S +
      bitLen K + bitLen (ρ + 1) + bitLen w + 9 + D * K + 1 := by omega
  have hcX := Nat.mul_le_mul_left c0 hX
  generalize hHdef : bitLen P + bitLen d + bitLen r + bitLen D + bitLen A + bitLen S +
      bitLen K + bitLen (ρ + 1) + bitLen w + 9 = H at hX hcX ⊢
  have e : (2 * c0 + 6) * (H + D * K + 1) =
      2 * (c0 * (H + D * K + 1)) + 6 * (H + D * K + 1) := by ring
  split_ifs with hqD
  · rw [length_hdrSyms9]
    have h1 := bitLen_mul_le A R
    have h3 : bitLen (D - q) ≤ bitLen D := bitLen_mono (Nat.sub_le _ _)
    have h4 : q * K ≤ D * K := Nat.mul_le_mul_right _ hqD.le
    omega
  · rw [length_hdrSyms9, hb0]
    omega

/-- **Size of the value record**: `≤ (2⌈lg W_c⌉ + 6)·(|hdr| + D·K + 1)`. In the rows case
`bitLen padR ≤ q₀K + q₀ + 2 ≤ DK + ⌈lg W_c⌉(bitLen d + 1) + 2` and `bitLen (A·padR) ≤ bitLen A +
bitLen padR` (`vals_len_aux`, instantiated). -/
theorem length_vals_le (t : LayerRT) :
    (hdrSyms (drvDescVals t)).length ≤
      (2 * Nat.clog 2 Wc + 6) * (t.hdr.length + t.D * t.K + 1) :=
  vals_len_aux (Nat.clog 2 Wc) (q0Of t.d) (padR t.d t.K) t.P t.d t.r t.D t.A t.S t.K t.ρ t.w
    (q0Of_le t.d) (bitLen_padR_le t.d t.K)

/-! ## 3. Layout and program -/

/-- Private stacks: the value-record stack `V`, the value kernel's and the pieces kernel's scratch. -/
abbrev DE (EA EP : Type) : Type := Unit ⊕ (EA ⊕ EP)

/-- The stacks of the descriptor program. -/
abbrev DK (EA EP : Type) : Type := KLoc (Fin 2) (DE EA EP)

/-- Registers: the value kernel's, the pieces kernel's, and one `Option Sym` for `dropHdr`. -/
abbrev DR (RA RP : Type) : Type := RA × (RP × Option Sym)

/-- Decidable equality of a sum from its summands, built explicitly. -/
abbrev decEqSumD {α β : Type} (ha : DecidableEq α) (hb : DecidableEq β) :
    DecidableEq (α ⊕ β) := by
  letI := ha
  letI := hb
  exact inferInstance

/-- `Fintype` of a sum from its summands, built explicitly. -/
abbrev fintypeSumD {α β : Type} (ha : Fintype α) (hb : Fintype β) : Fintype (α ⊕ β) := by
  letI := ha
  letI := hb
  exact inferInstance

section Layout

variable {EA EP : Type}

/-- The value-record stack `V`. -/
abbrev stV : DK EA EP := .inr (.inl ())

/-- Embedding of the value kernel (named: header `0 ↦ 0`, destination `1 ↦ V`). -/
def embA : KLoc (Fin 2) EA → DK EA EP
  | .inl i => if (i : ℕ) = 0 then .inl 0 else stV
  | .inr e => .inr (.inr (.inl e))

/-- Embedding of the pieces kernel (named: record `0 ↦ V`, destination `1 ↦ 1`). -/
def embP : KLoc (Fin 2) EP → DK EA EP
  | .inl i => if (i : ℕ) = 0 then stV else .inl 1
  | .inr e => .inr (.inr (.inr e))

theorem embA_injective : Function.Injective (embA (EA := EA) (EP := EP)) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [embA]
  · fin_cases i <;> simp [embA] at h
  · fin_cases i' <;> simp [embA] at h
  · simp only [embA, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem embP_injective : Function.Injective (embP (EA := EA) (EP := EP)) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [embP]
  · fin_cases i <;> simp [embP] at h
  · fin_cases i' <;> simp [embP] at h
  · simp only [embP, Sum.inr.injEq] at h
    rw [h]

end Layout

/-- `callInj` with one updated stack. -/
theorem runs_callInj_upd {L K σ R : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog L (fun _ => Sym) R} {B : K → List Sym}
    {x : L} {v : List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (Function.update (B ∘ ι) x v) Q T) :
    Runs (callInj ι l P) B (Function.update B (ι x) v) (fun _ => True) T := by
  refine runs_callInj (Q := Q) hι l ?_ ?_
  · rwa [Function.update_comp_eq_of_injective B hι x v]
  · intro k hk
    exact Function.update_of_ne (fun h => hk x h.symm) _ _

section Program

variable {EA EP RA RP : Type}

def lnA : Lens (DR RA RP) RA := Lens.fst _ _
def lnP : Lens (DR RA RP) RP := (Lens.snd _ _).comp (Lens.fst _ _)
def lnV : Lens (DR RA RP) (Option Sym) := (Lens.snd _ _).comp (Lens.snd _ _)

/-- **The descriptor program**: value kernel (header ↦ record on `V`), pieces kernel (record on
`V` ↦ descriptors), then pop the record from `V`. -/
def descProg (PA : Prog (KLoc (Fin 2) EA) (fun _ => Sym) RA)
    (PP : Prog (KLoc (Fin 2) EP) (fun _ => Sym) RP) :
    Prog (DK EA EP) (fun _ => Sym) (DR RA RP) :=
  .seq (callInj embA lnA PA)
    (.seq (callInj embP lnP PP) (callInj id lnV (Calculus.dropHdr (stV : DK EA EP) 9)))

theorem closed_descProg {PA : Prog (KLoc (Fin 2) EA) (fun _ => Sym) RA}
    {PP : Prog (KLoc (Fin 2) EP) (fun _ => Sym) RP} (hA : PA.Closed) (hP : PP.Closed) :
    (descProg PA PP).Closed :=
  WP.W9comp.closed_seq (closed_callInj _ _ hA)
    (WP.W9comp.closed_seq (closed_callInj _ _ hP) (closed_callInj _ _ (Calculus.closed_dropHdr _ _)))

end Program

/-! ## 4. Cost arithmetic -/

theorem cost_le {CA CP JA JP c X Lr Dc L : ℕ} (hX : 1 ≤ X) (hLr : Lr ≤ c * X)
    (hD : Dc ≤ 5 * Lr) :
    CA * X ^ JA + (CP * ((Lr + 1) ^ JP + L) + (Dc + 1)) ≤
      (CA + CP * (c + 1) ^ JP + 5 * c + 1) * (X ^ (JA + JP + 1) + L) := by
  have p1 : X ^ JA ≤ X ^ (JA + JP + 1) := Nat.pow_le_pow_right hX (by omega)
  have p2 : X ^ JP ≤ X ^ (JA + JP + 1) := Nat.pow_le_pow_right hX (by omega)
  have p3 : X ≤ X ^ (JA + JP + 1) := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ (JA + JP + 1) := Nat.pow_le_pow_right hX (by omega)
  have hM : 1 ≤ (c + 1) ^ JP := Nat.one_le_pow _ _ (by omega)
  have hL1 : Lr + 1 ≤ (c + 1) * X := by
    have : (c + 1) * X = c * X + X := by ring
    omega
  have hpow : (Lr + 1) ^ JP ≤ (c + 1) ^ JP * X ^ JP := by
    rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hL1 _
  generalize X ^ (JA + JP + 1) = XJ at p1 p2 p3 ⊢
  generalize (c + 1) ^ JP = M at hM hpow ⊢
  have q1 : CA * X ^ JA ≤ CA * XJ := Nat.mul_le_mul_left _ p1
  have q2 : CP * (Lr + 1) ^ JP ≤ CP * M * XJ := by
    calc CP * (Lr + 1) ^ JP ≤ CP * (M * X ^ JP) := Nat.mul_le_mul_left _ hpow
      _ ≤ CP * (M * XJ) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ p2)
      _ = CP * M * XJ := by ring
  have q3 : CP * L ≤ CP * M * L := by
    calc CP * L = CP * 1 * L := by ring
      _ ≤ CP * M * L := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hM)
  have h5 : 5 * Lr ≤ 5 * (c * X) := Nat.mul_le_mul_left _ hLr
  have h6 : c * X ≤ c * XJ := Nat.mul_le_mul_left _ p3
  have h7 : 1 ≤ XJ := le_trans hX p3
  have e1 : 5 * c * XJ = 5 * (c * XJ) := by ring
  have e2 : (CA + CP * M + 5 * c + 1) * (XJ + L) = CA * XJ + CP * M * XJ + 5 * c * XJ + XJ +
      (CA * L + CP * M * L + 5 * c * L + L) := by ring
  have e3 : CP * ((Lr + 1) ^ JP + L) = CP * (Lr + 1) ^ JP + CP * L := by ring
  omega

/-! ## 5. The contract -/

/-- **The descriptor program meets `DrvDescStmt`'s specification**, given the two parts'
specifications and a linear bound `c` on the value record. -/
theorem desc_contract {EA EP RA RP : Type} [iDA : DecidableEq EA] [iDP : DecidableEq EP]
    [Finite RA] [Nonempty RA] [Finite RP] [Nonempty RP]
    [iFE : Fintype (DE EA EP)] [iDE : DecidableEq (DE EA EP)] {JA CA JP CP c : ℕ}
    {PA : Prog (KLoc (Fin 2) EA) (fun _ => Sym) RA}
    {PP : Prog (KLoc (Fin 2) EP) (fun _ => Sym) RP}
    (hcA : PA.Closed) (hcP : PP.Closed)
    (hsA : ∀ (t : LayerRT) (hrest : List Sym) (S : KLoc (Fin 2) EA → List Sym),
      S (.inl 0) = t.hdr ++ hrest →
      Runs PA S (Function.update S (.inl 1) (hdrSyms (drvDescVals t) ++ S (.inl 1)))
        (fun _ => True) (CA * (t.hdr.length + t.D * t.K + 1) ^ JA))
    (hsP : ∀ (P d r a R K e S ρ : ℕ) (vrest : List Sym) (Sk : KLoc (Fin 2) EP → List Sym),
      Sk (.inl 0) = hdrSyms [P, d, r, a, R, K, e, S, ρ] ++ vrest →
      Runs PP Sk (Function.update Sk (.inl 1) (descOfVals P d r a R K e S ρ ++ Sk (.inl 1)))
        (fun _ => True)
        (CP * (((hdrSyms [P, d, r, a, R, K, e, S, ρ]).length + 1) ^ JP +
          (descOfVals P d r a R K e S ρ).length)))
    (hc : ∀ t : LayerRT,
      (hdrSyms (drvDescVals t)).length ≤ c * (t.hdr.length + t.D * t.K + 1)) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R : Type)
      (Pr : Prog (KLoc (Fin 2) E) (fun _ => Sym) R), Finite R ∧ Nonempty R ∧ Pr.Closed ∧
      ∀ (t : LayerRT) (hrest : List Sym) (S : KLoc (Fin 2) E → List Sym),
        S (.inl 0) = t.hdr ++ hrest →
        Runs Pr S (Function.update S (.inl 1) (drvDescSyms t ++ S (.inl 1)))
          (fun _ => True)
          ((CA + CP * (c + 1) ^ JP + 5 * c + 1) *
            ((t.hdr.length + t.D * t.K + 1) ^ (JA + JP + 1) + (drvDescSyms t).length)) := by
  refine ⟨DE EA EP, iFE, iDE, DR RA RP, descProg PA PP, inferInstance, inferInstance,
    closed_descProg hcA hcP, ?_⟩
  intro t hrest S h0
  obtain ⟨a, R, e, hv, hd⟩ := vals_spec t
  -- step 1: the value record onto `V`
  have hr1 : Runs (callInj embA (@lnA RA RP) PA) S
      (Function.update S stV (hdrSyms [t.P, t.d, t.r, a, R, t.K, e, t.S, t.ρ] ++ S stV))
      (fun _ => True) (CA * (t.hdr.length + t.D * t.K + 1) ^ JA) := by
    have hP := hsA t hrest (S ∘ embA) (by simpa [embA] using h0)
    rw [hv] at hP
    have h := runs_callInj_upd embA_injective (@lnA RA RP) hP
    refine WP.W9comp.runs_congr h ?_
    simp [embA]
  -- step 2: the descriptors onto `1`
  have hr2 : Runs (callInj embP (@lnP RA RP) PP)
      (Function.update S stV (hdrSyms [t.P, t.d, t.r, a, R, t.K, e, t.S, t.ρ] ++ S stV))
      (Function.update (Function.update S stV
        (hdrSyms [t.P, t.d, t.r, a, R, t.K, e, t.S, t.ρ] ++ S stV)) (.inl 1)
        (drvDescSyms t ++ S (.inl 1)))
      (fun _ => True)
      (CP * (((hdrSyms [t.P, t.d, t.r, a, R, t.K, e, t.S, t.ρ]).length + 1) ^ JP +
        (drvDescSyms t).length)) := by
    have hP := hsP t.P t.d t.r a R t.K e t.S t.ρ (S stV)
      (Function.update S stV (hdrSyms [t.P, t.d, t.r, a, R, t.K, e, t.S, t.ρ] ++ S stV) ∘ embP)
      (by simp [embP])
    rw [hd] at hP
    have h := runs_callInj_upd embP_injective (@lnP RA RP) hP
    refine WP.W9comp.runs_congr h ?_
    simp [embP]
  -- step 3: pop the record
  have hr3 := runs_callInj_upd (ι := id) Function.injective_id (@lnV RA RP)
    (Calculus.runs_dropHdr (stV : DK EA EP) [t.P, t.d, t.r, a, R, t.K, e, t.S, t.ρ] (S stV)
      ((Function.update (Function.update S stV
        (hdrSyms [t.P, t.d, t.r, a, R, t.K, e, t.S, t.ρ] ++ S stV)) (.inl 1)
        (drvDescSyms t ++ S (.inl 1))) ∘ id) (by simp))
  have hall := WP.W9comp.runs_seq hr1 (WP.W9comp.runs_seq hr2 hr3)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · funext k
    by_cases hk1 : k = .inl 1
    · subst hk1; simp
    · by_cases hkV : k = stV
      · subst hkV; simp
      · simp [Function.update_of_ne hk1, Function.update_of_ne hkV]
  · have hrec : (hdrSyms [t.P, t.d, t.r, a, R, t.K, e, t.S, t.ρ]).length ≤
        c * (t.hdr.length + t.D * t.K + 1) := by rw [← hv]; exact hc t
    exact cost_le (by omega) hrec (dropCost_le _)

end SubNLogN.Machine.Layer.DrvDescAux

namespace SubNLogN.Machine.Layer

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine DrvDescAux

/-- **The descriptor kernel from its two parts** (`DrvDescStmt`): the value kernel
(`DrvDescArithStmt`) pushes the value record onto a private stack, the pieces kernel
(`DrvDescPiecesStmt`) turns it into `drvDescSyms t` on the descriptor stack, and the record is
popped. `J = J_A + J_P + 1`, `C = C_A + C_P·(c + 1)^{J_P} + 5c + 1` with `c = 2⌈lg W_c⌉ + 6`. -/
theorem drvDesc_of (hA : DrvDescArithStmt) (hP : DrvDescPiecesStmt) : DrvDescStmt := by
  obtain ⟨JA, CA, hA⟩ := hA
  obtain ⟨JP, CP, hP⟩ := hP
  obtain ⟨EA, iFA, iDA, RA, PA, iRA, iNA, hcA, hsA⟩ := hA ()
  obtain ⟨EP, iFP, iDP, RP, PP, iRP, iNP, hcP, hsP⟩ := hP ()
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ∀ t : LayerRT,
      (hdrSyms (drvDescVals t)).length ≤ c * (t.hdr.length + t.D * t.K + 1) :=
    ⟨_, length_vals_le⟩
  exact ⟨JA + JP + 1, CA + CP * (c + 1) ^ JP + 5 * c + 1, fun _ =>
    desc_contract (iDA := iDA) (iDP := iDP)
      (iFE := fintypeSumD inferInstance (fintypeSumD iFA iFP))
      (iDE := decEqSumD inferInstance (decEqSumD iDA iDP)) hcA hcP hsA hsP hc⟩

end SubNLogN.Machine.Layer
