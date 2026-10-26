/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CubeLayerMath
import SubNLogN.Machine.FFT.Kit

/-!
# K3.0 (`Machine/Walsh/CubeLayer.lean`): a layer call on a slice of the cube, from the layer machine

Paper: Proposition A.11 (`prop:prop14-param`, including its runtime header) at the slice shapes of
Definition 5.6 (`def:walsh-positional`).

**Scope (honest summary).** Proved (no `sorry`):
`cubeLayer_of_layer : LayerMachineGenStmt Band (layerCost lam') → CubeHdrStmt → CubeLayerStmt Band lam'`.
`CubeHdrStmt` is the leaf contract of the header builder `sliceHdr ↦ LayerRT.hdr`, stated here and
taken as an explicit hypothesis; it is proved in `Machine/Walsh/CubeHdr.lean` (`cubeHdr_holds`),
where the hypothesis-free form `cubeLayer_of_layerMachine` is derived. Helpers live in
`SubNLogN.Machine.WalshCubeAux`.

## Plan (program and invariants)
Named stacks `0` (cube array), `1` (slice header); private stacks `Unit ⊕ (EH ⊕ EL)`: the layer
header stack `H` (empty on entry by `KClean`), the header builder's scratch `EH`, the layer's
scratch `EL`. Program:
1. header builder (`CubeHdrStmt`): reads the slice header on `1` (restored) and pushes
   `(layerRT P d r w K j₀ D nS ρ).hdr` onto the empty `H`;
2. the layer (`LayerMachineGenStmt`), embedded with array `↦ 0`, header `↦ H`, scratch `↦ EL`: by
   `encCube_eq_encLayer` the cube array *is* the layer array `z ∘ addrToCube` on the shape
   `[2^{j₀}] × [2^K]^D × [2^{nS}]`, and by `encLayer_layerH_eq` the output is the cube array
   `Q_P(H_T z)`, `T = slicePos m K j₀ D ρ` (`CubeLayerMath.lean`);
3. empty `H` (`drainProg`).
Cost: `C_H((w+m+1)^{J_H} + |sliceHdr|) + C_L·layerCost + 2|LayerRT.hdr| + 3`, and
`|LayerRT.hdr| ≤ |sliceHdr| + 2(w + m + 1)` (`length_layerHdr_le`, from `2^{j₀}`, `2^{nS}` having
`j₀ + 1`, `nS + 1` bits, `j₀ + nS ≤ m`, `ρ < K ≤ w + m`); total
`≤ (C_H + C_L + 15)(layerCost + (w+m+1)^{J_H+1} + |sliceHdr|)`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common

/-- **[LEAF CONTRACT] K3.0a, header builder of a slice layer call** (proved:
`cubeHdr_holds`, `Machine/Walsh/CubeHdr.lean`) (Proposition A.11 (`prop:prop14-param`): the
layer header `Γ(P)Γ(d)Γ(r)Γ(D)Γ(A)Γ(S)Γ(K)Γ(ρ+1)Γ(w)`, `LayerRT.hdr`; Definition 5.6
(`def:walsh-positional`): the slice shape has `A = 2^{j₀}`, `S = 2^{nS}`).
* Named stacks (`Fin 2`): `0` the slice header `sliceHdr P d r w K m j₀ D nS ρ` (restored; the
  header has ten fields, so nothing is assumed below it), `1` receives the layer header
  `(layerRT P d r w K j₀ D nS ρ).hdr` on top of its content.
* Every other stack is restored; private scratch clean on entry (`KClean`).
* Hypothesis: the slice shape `j₀ + DK + nS = m` (so `2^{j₀}`, `2^{nS}` have at most `m + 1` bits).
* Cost `C·((w + m + 1)^J + |sliceHdr|)`, `J` fixed before the runtime data. -/
def CubeHdrStmt : Prop :=
  ∃ J : ℕ, KContract (Fin 2) Unit fun _ E _ _ _ C Pr =>
    ∀ (P d r w K m j₀ D nS ρ : ℕ) (hrest : List Sym) (S : KLoc (Fin 2) E → List Sym),
      KClean S → j₀ + D * K + nS = m →
      S (.inl 0) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest →
      Runs Pr S
        (Function.update S (.inl 1) ((layerRT P d r w K j₀ D nS ρ).hdr ++ S (.inl 1)))
        (fun _ => True) (C * ((w + m + 1) ^ J + (sliceHdr P d r w K m j₀ D nS ρ).length))

end SubNLogN.Machine

namespace SubNLogN.Machine.WalshCubeAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
  SubNLogN.Machine SubNLogN.Machine.FFTKit

/-! ## 1. Header lengths -/

theorem length_hdrSyms (fs : List ℕ) :
    (hdrSyms fs).length = (fs.map fun n => bitLen n + 1).sum := by
  induction fs with
  | nil => simp [hdrSyms]
  | cons n fs ih =>
    simp only [hdrSyms, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih, length_natSyms, List.length_singleton]

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n :=
  WP.W9comp.bitLen_le_of_lt_two_pow (Nat.lt_two_pow_self)

theorem bitLen_two_pow_le (k : ℕ) : bitLen (2 ^ k) ≤ k + 1 :=
  WP.W9comp.bitLen_le_of_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))

/-- The layer header of a slice call is at most `2(w + m + 1)` longer than the slice header. -/
theorem length_layerHdr_le {P d r w K m j₀ D nS ρ : ℕ} (hm : j₀ + D * K + nS = m) (hρ : ρ < K)
    (hKw : K ≤ w + m) :
    (layerRT P d r w K j₀ D nS ρ).hdr.length ≤
      (sliceHdr P d r w K m j₀ D nS ρ).length + 2 * (w + m + 1) := by
  show (hdrSyms [P, d, r, D, 2 ^ j₀, 2 ^ nS, K, ρ + 1, w]).length ≤
    (hdrSyms [P, d, r, w, K, m, j₀, D, nS, ρ]).length + 2 * (w + m + 1)
  rw [length_hdrSyms, length_hdrSyms]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h1 := bitLen_two_pow_le j₀
  have h2 := bitLen_two_pow_le nS
  have h3 := bitLen_le_self (ρ + 1)
  omega

/-- The cost of the composite is at most a constant times the slice call's bound. -/
theorem cube_cost_bound {CH CL JH L Hs Ht w m : ℕ} (hHt : Ht ≤ Hs + 2 * (w + m + 1)) :
    CH * ((w + m + 1) ^ JH + Hs) + (CL * L + (2 * Ht + 3)) ≤
      (CH + CL + 15) * (L + (w + m + 1) ^ (JH + 1) + Hs) := by
  have hb : 1 ≤ w + m + 1 := by omega
  have hX : (w + m + 1) ^ JH ≤ (w + m + 1) ^ (JH + 1) := Nat.pow_le_pow_right hb (by omega)
  have hY : w + m + 1 ≤ (w + m + 1) ^ (JH + 1) := by
    calc w + m + 1 = (w + m + 1) ^ 1 := (pow_one _).symm
      _ ≤ (w + m + 1) ^ (JH + 1) := Nat.pow_le_pow_right hb (by omega)
  set Y := (w + m + 1) ^ (JH + 1) with hYdef
  set X := (w + m + 1) ^ JH with hXdef
  have e1 : CH * (X + Hs) ≤ CH * (L + Y + Hs) := Nat.mul_le_mul_left _ (by omega)
  have e2 : CL * L ≤ CL * (L + Y + Hs) := Nat.mul_le_mul_left _ (by omega)
  have e3 : 2 * Ht + 3 ≤ 15 * (L + Y + Hs) := by omega
  calc CH * (X + Hs) + (CL * L + (2 * Ht + 3))
      ≤ CH * (L + Y + Hs) + (CL * (L + Y + Hs) + 15 * (L + Y + Hs)) := by omega
    _ = (CH + CL + 15) * (L + Y + Hs) := by ring

/-! ## 2. The composite program -/

/-- Decidable equality of a sum from its summands, built explicitly (instance witnesses obtained
from contract existentials are passed by name). -/
abbrev decEqSum {α β : Type} (ha : DecidableEq α) (hb : DecidableEq β) : DecidableEq (α ⊕ β) := by
  letI := ha
  letI := hb
  exact inferInstance

/-- `Fintype` of a sum from its summands, built explicitly (as `decEqSum`). -/
abbrev fintypeSum {α β : Type} (ha : Fintype α) (hb : Fintype β) : Fintype (α ⊕ β) := by
  letI := ha
  letI := hb
  exact inferInstance

section Composite

variable {EH EL RH RL : Type}

/-- Private stacks of the composite: the layer header stack, then the two parts' scratch. -/
abbrev CubeE (EH EL : Type) : Type := Unit ⊕ (EH ⊕ EL)

/-- Registers of the composite: the drain flag, then the two parts' registers. -/
abbrev CubeR (RH RL : Type) : Type := Bool × (RH × RL)

/-- The private layer header stack `H`. -/
abbrev cubeHstk : KLoc (Fin 2) (CubeE EH EL) := .inr (.inl ())

/-- Embedding of the header builder: source `↦ 1`, target `↦ H`, scratch `↦ EH`. -/
def hdrEmb : KLoc (Fin 2) EH → KLoc (Fin 2) (CubeE EH EL)
  | .inl i => if (i : ℕ) = 0 then .inl 1 else .inr (.inl ())
  | .inr e => .inr (.inr (.inl e))

/-- Embedding of the layer: array `↦ 0`, header `↦ H`, scratch `↦ EL`. -/
def layEmb : KLoc (Fin 2) EL → KLoc (Fin 2) (CubeE EH EL)
  | .inl i => if (i : ℕ) = 0 then .inl 0 else .inr (.inl ())
  | .inr e => .inr (.inr (.inr e))

@[simp] theorem hdrEmb_src : hdrEmb (EH := EH) (EL := EL) (.inl 0) = .inl 1 := by simp [hdrEmb]
@[simp] theorem hdrEmb_dst : hdrEmb (EH := EH) (EL := EL) (.inl 1) = .inr (.inl ()) := by
  simp [hdrEmb]
@[simp] theorem hdrEmb_inr (e : EH) : hdrEmb (EL := EL) (.inr e) = .inr (.inr (.inl e)) := rfl
@[simp] theorem layEmb_arr : layEmb (EH := EH) (EL := EL) (.inl 0) = .inl 0 := by simp [layEmb]
@[simp] theorem layEmb_hdr : layEmb (EH := EH) (EL := EL) (.inl 1) = .inr (.inl ()) := by
  simp [layEmb]
@[simp] theorem layEmb_inr (e : EL) : layEmb (EH := EH) (.inr e) = .inr (.inr (.inr e)) := rfl

theorem hdrEmb_injective : Function.Injective (hdrEmb (EH := EH) (EL := EL)) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [hdrEmb]
  · fin_cases i <;> simp [hdrEmb] at h
  · fin_cases i' <;> simp [hdrEmb] at h
  · simp only [hdrEmb, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem layEmb_injective : Function.Injective (layEmb (EH := EH) (EL := EL)) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [layEmb]
  · fin_cases i <;> simp [layEmb] at h
  · fin_cases i' <;> simp [layEmb] at h
  · simp only [layEmb, Sum.inr.injEq] at h
    rw [h]

/-- Register lenses of the drain flag and the two parts. -/
def lnsB : Lens (CubeR RH RL) Bool := Lens.fst _ _
def lnsH : Lens (CubeR RH RL) RH := (Lens.snd _ _).comp (Lens.fst _ _)
def lnsL : Lens (CubeR RH RL) RL := (Lens.snd _ _).comp (Lens.snd _ _)

/-- **The composite program**: build the layer header on `H`; the layer; empty `H`. -/
def cubeProg (PH : Prog (KLoc (Fin 2) EH) (fun _ => Sym) RH)
    (PL : Prog (KLoc (Fin 2) EL) (fun _ => Sym) RL) :
    Prog (KLoc (Fin 2) (CubeE EH EL)) (fun _ => Sym) (CubeR RH RL) :=
  .seq (callInj hdrEmb lnsH PH)
    (.seq (callInj layEmb lnsL PL) (callInj id lnsB (drainProg cubeHstk)))

theorem closed_cubeProg {PH : Prog (KLoc (Fin 2) EH) (fun _ => Sym) RH}
    {PL : Prog (KLoc (Fin 2) EL) (fun _ => Sym) RL} (hH : PH.Closed) (hL : PL.Closed) :
    (cubeProg PH PL).Closed :=
  WP.W9comp.closed_seq (closed_callInj _ _ hH) (WP.W9comp.closed_seq (closed_callInj _ _ hL)
    (closed_callInj _ _ (closed_drainProg _)))

end Composite

/-! ## 3. The reduction -/

/-- **The composite meets the slice call's contract**, given the header builder's and the layer's
specifications (stated exactly as in `CubeHdrStmt` and `LayerMachineGenStmt`, for fixed programs
and constants). The scratch and register types are fixed with their instances;
`cubeLayer_of_layer` instantiates them with the parts' witnesses. -/
theorem cubeContract_of_parts {EH EL RH RL : Type}
    [iDH : DecidableEq EH] [iDL : DecidableEq EL]
    [iRH : Finite RH] [iNH : Nonempty RH] [iRL : Finite RL] [iNL : Nonempty RL]
    [iFE : Fintype (CubeE EH EL)] [iDE : DecidableEq (CubeE EH EL)]
    {Band : LayerRT → Prop} {lam' : ℝ} {JH CH CL : ℕ}
    {PH : Prog (KLoc (Fin 2) EH) (fun _ => Sym) RH} {PL : Prog (KLoc (Fin 2) EL) (fun _ => Sym) RL}
    (hcH : PH.Closed) (hcL : PL.Closed)
    (hsH : ∀ (P d r w K m j₀ D nS ρ : ℕ) (hrest : List Sym) (S : KLoc (Fin 2) EH → List Sym),
      KClean S → j₀ + D * K + nS = m →
      S (.inl 0) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest →
      Runs PH S
        (Function.update S (.inl 1) ((layerRT P d r w K j₀ D nS ρ).hdr ++ S (.inl 1)))
        (fun _ => True) (CH * ((w + m + 1) ^ JH + (sliceHdr P d r w K m j₀ D nS ρ).length)))
    (hsL : ∀ (t : LayerRT) (hA : 0 < t.A) (hS : 0 < t.S) (hρ : t.ρ < t.K)
      (z : RArr (LayerAddr t.A t.K t.D t.S) t.r) (rest hrest : List Sym)
      (S : KLoc (Fin 2) EL → List Sym),
      KClean S → Band t → t.P + 2 ≤ t.w → ArrOnDiskGrid t.P z → BlkTerm rest →
      S (.inl 0) = carrSyms t.w (encLayer hA hS t.P z) ++ rest →
      S (.inl 1) = t.hdr ++ hrest →
      Runs PL S
        (Function.update S (.inl 0)
          (carrSyms t.w (encLayer hA hS t.P (truncArr t.P (layerH ⟨t.ρ, hρ⟩ z))) ++ rest))
        (fun _ => True) (CL * layerCost lam' t)) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R : Type)
      (Pr : Prog (KLoc (Fin 2) E) (fun _ => Sym) R), Finite R ∧ Nonempty R ∧ Pr.Closed ∧
      ∀ (P d r w K m j₀ D nS ρ : ℕ) (z : RArr (Cube m) r) (rest hrest : List Sym)
        (S : KLoc (Fin 2) E → List Sym),
        KClean S → j₀ + D * K + nS = m → ρ < K → P + 2 ≤ w → d ≤ w + m → K ≤ w + m →
        Band (layerRT P d r w K j₀ D nS ρ) → ArrOnDiskGrid P z → BlkTerm rest →
        S (.inl 0) = carrSyms w (encCube P z) ++ rest →
        S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest →
        Runs Pr S
          (Function.update S (.inl 0)
            (carrSyms w (encCube P (truncArr P (hT (slicePos m K j₀ D ρ) z))) ++ rest))
          (fun _ => True)
          ((CH + CL + 15) * (layerCost lam' (layerRT P d r w K j₀ D nS ρ) +
            (w + m + 1) ^ (JH + 1) + (sliceHdr P d r w K m j₀ D nS ρ).length)) := by
  refine ⟨CubeE EH EL, iFE, iDE, CubeR RH RL, cubeProg PH PL, inferInstance, inferInstance,
    closed_cubeProg hcH hcL, ?_⟩
  intro P d r w K m j₀ D nS ρ z rest hrest S hcl hm hρ hw _hdw hKw hband hz hrestT h0 h1
  have hcl' : ∀ e, S (.inr e) = [] := hcl
  have hA : 0 < 2 ^ j₀ := Nat.two_pow_pos j₀
  have hS : 0 < 2 ^ nS := Nat.two_pow_pos nS
  have hne0 : (Sum.inl 0 : KLoc (Fin 2) (CubeE EH EL)) ≠ cubeHstk := by simp
  obtain ⟨S1, hS1⟩ : ∃ S', S' = Function.update S cubeHstk (layerRT P d r w K j₀ D nS ρ).hdr :=
    ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S', S' = Function.update S1 (.inl 0)
      (carrSyms w (encCube P (truncArr P (hT (slicePos m K j₀ D ρ) z))) ++ rest) := ⟨_, rfl⟩
  -- step 1: the layer header
  have hr1 : Runs (callInj hdrEmb (@lnsH RH RL) PH) S S1 (fun _ => True)
      (CH * ((w + m + 1) ^ JH + (sliceHdr P d r w K m j₀ D nS ρ).length)) := by
    have hP := hsH P d r w K m j₀ D nS ρ hrest (S ∘ hdrEmb) (fun e => hcl' _) hm
      (by simpa using h1)
    have h := runs_callInj_update hdrEmb_injective (@lnsH RH RL) hP
    refine WP.W9comp.runs_congr h ?_
    rw [hS1]
    simp [hcl']
  -- step 2: the layer, on the cube array read as the layer array `z ∘ addrToCube`
  have hr2 : Runs (callInj layEmb (@lnsL RH RL) PL) S1 S2 (fun _ => True)
      (CL * layerCost lam' (layerRT P d r w K j₀ D nS ρ)) := by
    have e0 : (S1 ∘ layEmb) (.inl 0) =
        carrSyms w (encLayer hA hS P (fun a => z (addrToCube K j₀ D nS m a))) ++ rest := by
      rw [Function.comp_apply, layEmb_arr, hS1, Function.update_of_ne hne0, h0,
        encCube_eq_encLayer hm hA hS P z]
    have e1 : (S1 ∘ layEmb) (.inl 1) = (layerRT P d r w K j₀ D nS ρ).hdr ++ [] := by
      rw [Function.comp_apply, layEmb_hdr, hS1, Function.update_self, List.append_nil]
    have hclL : KClean (S1 ∘ layEmb) := fun e => by
      show S1 (layEmb (.inr e)) = []
      rw [layEmb_inr, hS1, Function.update_of_ne (by simp), hcl']
    have hP := hsL (layerRT P d r w K j₀ D nS ρ) hA hS hρ
      (fun a => z (addrToCube K j₀ D nS m a)) rest [] (S1 ∘ layEmb) hclL hband hw
      (fun a k => hz _ k) hrestT e0 e1
    have h := runs_callInj_update layEmb_injective (@lnsL RH RL) hP
    refine WP.W9comp.runs_congr h ?_
    rw [hS2, layEmb_arr]
    congr 1
    exact congrArg (· ++ rest) (congrArg (carrSyms w) (encLayer_layerH_eq hm hA hS P ⟨ρ, hρ⟩ z))
  -- step 3: empty `H`
  have hr3 : Runs (callInj id (@lnsB RH RL) (drainProg cubeHstk)) S2
      (Function.update S2 cubeHstk []) (fun _ => True) (2 * (S2 cubeHstk).length + 3) :=
    runs_callInj_update (ι := id) Function.injective_id lnsB (runs_drainProg cubeHstk (S2 ∘ id))
  have hall := WP.W9comp.runs_seq hr1 (WP.W9comp.runs_seq hr2 hr3)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · -- the final stacks
    rw [hS2, hS1]
    funext k
    by_cases hk0 : k = .inl 0
    · subst hk0
      simp
    · by_cases hkH : k = cubeHstk
      · subst hkH
        simp [hcl']
      · simp [hk0, hkH]
  · -- the cost
    have hH : (S2 cubeHstk).length ≤
        (sliceHdr P d r w K m j₀ D nS ρ).length + 2 * (w + m + 1) := by
      rw [hS2, hS1, Function.update_of_ne hne0.symm, Function.update_self]
      exact length_layerHdr_le hm hρ hKw
    exact cube_cost_bound hH

end SubNLogN.Machine.WalshCubeAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Math.Walsh SubNLogN.Machine.WalshCubeAux

/-- **K3.0 from the layer machine** (Proposition A.11 (`prop:prop14-param`), on the slice shapes of
Definition 5.6 (`def:walsh-positional`)): the generic layer machine with cost `layerCost lam'`, plus
the header builder `CubeHdrStmt` (leaf; proved as `cubeHdr_holds`), give `CubeLayerStmt Band lam'` for the same
`Band`. The cube array is the layer array in place (`CubeLayerMath.lean`); there is no other
hypothesis. Constants: `J = J_H + 1`, `C = C_H + C_L + 15`. -/
theorem cubeLayer_of_layer {Band : LayerRT → Prop} {lam' : ℝ}
    (hL : LayerMachineGenStmt Band (layerCost lam')) (hH : CubeHdrStmt) :
    CubeLayerStmt Band lam' := by
  obtain ⟨JH, CH, hH'⟩ := hH
  obtain ⟨CL, hL'⟩ := hL
  obtain ⟨EH, iFH, iDH, RH, PH, iRH, iNH, hcH, hsH⟩ := hH' ()
  obtain ⟨EL, iFL, iDL, RL, PL, iRL, iNL, hcL, hsL⟩ := hL' ()
  exact ⟨JH + 1, CH + CL + 15, fun _ =>
    cubeContract_of_parts (iDH := iDH) (iDL := iDL) (iRH := iRH) (iNH := iNH) (iRL := iRL)
      (iNL := iNL) (iFE := fintypeSum inferInstance (fintypeSum iFH iFL))
      (iDE := decEqSum inferInstance (decEqSum iDH iDL)) hcH hcL hsH hsL⟩

end SubNLogN.Machine
