/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.ChunkTail
import SubNLogN.Machine.FFT.RoundsBase

/-!
# K4.5 (`Machine/FFT/ChunkMain.lean`): a chunk round is one layer call

**Scope (honest summary).** `chunkRound_of_cubeLayer : CubeLayerStmt Band lam' →
ChunkRoundStmt Band lam'` (no `sorry`; the only hypothesis is the layer call on a slice,
`CubeLayerStmt`, K3.0). The descriptor header comes from the proved `permHdrGen_holds`
(`Machine/FFT/LayoutHdr.lean`), the last four fields from the proved tail builder `tail_exists`
(`Machine/FFT/ChunkTail.lean`).

Program (private stacks `T`, `H`; Lemma 6.3, `lem:walsh-layout`, and Section 6.4):
1. `permHdr q (D+1) 2^ℓ w K m₀` onto `T` (`PermHdrGenStmt`);
2. the tail builder reads `D, ℓ` (header), `K, m₀` (from `T`, consumed) and `v`, and pushes
   `hdrSyms [j₀, D, nS, ρ]` onto `H`;
3. `permHdr …` again, onto `H`: now `H = sliceHdr q (D+1) 2^ℓ w K m₀ j₀ D nS ρ`;
4. the layer call on the slice (`CubeLayerStmt`) with the array and `H`: the array becomes
   `Q_q(H_T z)`, `T = slicePos m₀ K j₀ D ρ`;
5. empty `H`.
Cost `C·(layerCost + (w + m₀ + 1)^J + |midHdr|)` with `J = J_H + J_L + 4`.
-/

namespace SubNLogN.Machine.FFT.ChunkAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh
  SubNLogN.Math.Common SubNLogN.Machine.FFTKit

/-! ## 1. Layout -/

/-- Private stacks: `T`, `H`, the tail builder's scratch, the header generator's and the layer
call's scratch blocks. -/
abbrev ChE (EH EL : Type) : Type := Fin 2 ⊕ (Fin 13 ⊕ (EH ⊕ EL))

/-- The stacks of the chunk-round program. -/
abbrev ChK (EH EL : Type) : Type := KLoc (Fin 4) (ChE EH EL)

/-- Registers: the drain flag, the header generator's, the tail builder's and the layer call's. -/
abbrev ChR (RH RT RL : Type) : Type := Bool × (RH × (RT × RL))

section Layout

variable {EH EL : Type}

/-- The private stack `T` (descriptor header, consumed by the tail builder). -/
abbrev stT : ChK EH EL := .inr (.inl 0)
/-- The private stack `H` (the slice header). -/
abbrev stH : ChK EH EL := .inr (.inl 1)

/-- Embedding of the header generator (named: header, destination `dst`). -/
def embH (dst : ChK EH EL) : KLoc (Fin 2) EH → ChK EH EL
  | .inl i => if (i : ℕ) = 0 then .inl 1 else dst
  | .inr e => .inr (.inr (.inr (.inl e)))

/-- Embedding of the tail builder. -/
def embT : CL → ChK EH EL
  | .inl i => if (i : ℕ) = 0 then .inl 1 else if (i : ℕ) = 1 then .inl 3
      else if (i : ℕ) = 2 then stT else stH
  | .inr j => .inr (.inr (.inl j))

/-- Embedding of the layer call (named: array, slice header `H`). -/
def embL : KLoc (Fin 2) EL → ChK EH EL
  | .inl i => if (i : ℕ) = 0 then .inl 0 else stH
  | .inr e => .inr (.inr (.inr (.inr e)))

theorem embH_injective_T : Function.Injective (embH (stT : ChK EH EL)) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [embH]
  · fin_cases i <;> simp [embH] at h
  · fin_cases i' <;> simp [embH] at h
  · simp only [embH, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem embH_injective_H : Function.Injective (embH (stH : ChK EH EL)) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [embH]
  · fin_cases i <;> simp [embH] at h
  · fin_cases i' <;> simp [embH] at h
  · simp only [embH, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem embT_injective : Function.Injective (embT (EH := EH) (EL := EL)) := by
  rintro (i | j) (i' | j') h
  · fin_cases i <;> fin_cases i' <;> simp_all [embT]
  · fin_cases i <;> simp [embT] at h
  · fin_cases i' <;> simp [embT] at h
  · simp only [embT, Sum.inr.injEq, Sum.inl.injEq] at h
    rw [h]

theorem embL_injective : Function.Injective (embL (EH := EH) (EL := EL)) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [embL]
  · fin_cases i <;> simp [embL] at h
  · fin_cases i' <;> simp [embL] at h
  · simp only [embL, Sum.inr.injEq] at h
    rw [h]

end Layout

/-- `callInj` with two updated stacks. -/
theorem runs_callInj_update2 {L K σ R : Type} [DecidableEq L] [DecidableEq K] {ι : L → K}
    (hι : Function.Injective ι) (l : Lens σ R) {P : Prog L (fun _ => Sym) R} {B : K → List Sym}
    {x y : L} {vx vy : List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (Function.update (Function.update (B ∘ ι) x vx) y vy) Q T) :
    Runs (callInj ι l P) B (Function.update (Function.update B (ι x) vx) (ι y) vy)
      (fun _ => True) T := by
  refine runs_callInj (Q := Q) hι l ?_ ?_
  · rw [Function.update_comp_eq_of_injective _ hι y, Function.update_comp_eq_of_injective _ hι x]
    exact hP
  · intro k hk
    rw [Function.update_of_ne (fun h => hk y h.symm), Function.update_of_ne (fun h => hk x h.symm)]

/-! ## 2. Program -/

section Program

variable {EH EL RH RT RL : Type}

def lnB : Lens (ChR RH RT RL) Bool := Lens.fst _ _
def lnH : Lens (ChR RH RT RL) RH := (Lens.snd _ _).comp (Lens.fst _ _)
def lnT : Lens (ChR RH RT RL) RT := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lnL : Lens (ChR RH RT RL) RL := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))

/-- **The chunk-round program**: descriptor header onto `T`; tail onto `H` (consuming `T`);
descriptor header onto `H`; the layer call; empty `H`. -/
def chunkProg (PH : Prog (KLoc (Fin 2) EH) (fun _ => Sym) RH) (PT : Prog CL (fun _ => Sym) RT)
    (PL : Prog (KLoc (Fin 2) EL) (fun _ => Sym) RL) :
    Prog (ChK EH EL) (fun _ => Sym) (ChR RH RT RL) :=
  .seq (callInj (embH stT) lnH PH) (.seq (callInj embT lnT PT)
    (.seq (callInj (embH stH) lnH PH) (.seq (callInj embL lnL PL)
      (callInj id lnB (drainProg stH)))))

theorem closed_chunkProg {PH : Prog (KLoc (Fin 2) EH) (fun _ => Sym) RH}
    {PT : Prog CL (fun _ => Sym) RT} {PL : Prog (KLoc (Fin 2) EL) (fun _ => Sym) RL}
    (hH : PH.Closed) (hT : PT.Closed) (hL : PL.Closed) : (chunkProg PH PT PL).Closed :=
  WP.W9comp.closed_seq (closed_callInj _ _ hH) (WP.W9comp.closed_seq (closed_callInj _ _ hT)
    (WP.W9comp.closed_seq (closed_callInj _ _ hH) (WP.W9comp.closed_seq (closed_callInj _ _ hL)
      (closed_callInj _ _ (closed_drainProg _)))))

end Program

/-! ## 3. Header facts -/

theorem sliceHdr_eq (P d r w K m j₀ D nS ρ : ℕ) :
    sliceHdr P d r w K m j₀ D nS ρ = permHdr P d r w K m ++ hdrSyms [j₀, D, nS, ρ] := by
  simp [sliceHdr, permHdr, hdrSyms]

theorem length_sliceHdr_le {q D ℓ K w m j₀ nS ρ X : ℕ} (hq : q ≤ X) (hD : D + 1 ≤ X)
    (hℓ : ℓ + 1 ≤ X) (hw : w ≤ X) (hK : K ≤ X) (hm : m ≤ X) (hj : j₀ ≤ X) (hn : nS ≤ X)
    (hr : ρ ≤ X) :
    (sliceHdr q (D + 1) (2 ^ ℓ) w K m j₀ D nS ρ).length ≤ 10 * X + 10 := by
  rw [sliceHdr, RoundsAux.length_hdrSyms_eq]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h2 := FFT.LayoutAux.bitLen_two_pow_le ℓ
  have b1 := RoundsAux.bitLen_le_self q
  have b2 := RoundsAux.bitLen_le_self (D + 1)
  have b4 := RoundsAux.bitLen_le_self w
  have b5 := RoundsAux.bitLen_le_self K
  have b6 := RoundsAux.bitLen_le_self m
  have b7 := RoundsAux.bitLen_le_self j₀
  have b8 := RoundsAux.bitLen_le_self D
  have b9 := RoundsAux.bitLen_le_self nS
  have b10 := RoundsAux.bitLen_le_self ρ
  omega

/-! ## 4. The reduction -/

/-- Decidable equality of a sum from its summands, built explicitly (as in
`Machine/FFT/Middle.lean`: instance search on deeply nested sums is expensive). -/
abbrev decEqSumC {α β : Type} (ha : DecidableEq α) (hb : DecidableEq β) :
    DecidableEq (α ⊕ β) := by
  letI := ha
  letI := hb
  exact inferInstance

/-- `Fintype` of a sum from its summands, built explicitly. -/
abbrev fintypeSumC {α β : Type} (ha : Fintype α) (hb : Fintype β) : Fintype (α ⊕ β) := by
  letI := ha
  letI := hb
  exact inferInstance


theorem pow_le_pow_X {X a b : ℕ} (hX : 1 ≤ X) (h : a ≤ b) : X ^ a ≤ X ^ b :=
  Nat.pow_le_pow_right hX h

/-- **The chunk-round program meets the contract**, given the three parts' specifications. -/
theorem chunk_contract {EH EL RH RT RL : Type} [iDH : DecidableEq EH] [iDL : DecidableEq EL]
    [Finite RH] [Nonempty RH] [Finite RT] [Nonempty RT] [Finite RL] [Nonempty RL]
    [iFE : Fintype (ChE EH EL)] [iDE : DecidableEq (ChE EH EL)]
    {Band : LayerRT → Prop} {lam' : ℝ} {JH CH CT JL CLc : ℕ}
    {PH : Prog (KLoc (Fin 2) EH) (fun _ => Sym) RH} {PT : Prog CL (fun _ => Sym) RT}
    {PL : Prog (KLoc (Fin 2) EL) (fun _ => Sym) RL}
    (hcH : PH.Closed) (hcT : PT.Closed) (hcL : PL.Closed)
    (hsH : ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest phrest : List Sym)
      (S : KLoc (Fin 2) EH → List Sym),
      KClean S → MidShapeOK q ℓ K w a →
      S (.inl 0) = midHdr q ℓ K w a ++ hrest → S (.inl 1) = phrest →
      Runs PH S
        (Function.update S (.inl 1) (permHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) ++ phrest))
        (fun _ => True) (CH * ((w + addrBits a + 1) ^ JH + (midHdr q ℓ K w a).length)))
    (hsT : ∀ (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (hrest crest : List Sym) (S : CL → List Sym),
      (∀ j, S (.inr j) = []) → MidShapeOK q ℓ K w a → IsChunkRound ℓ K v → TermOK crest →
      S (.inl 0) = midHdr q ℓ K w a ++ hrest → S (.inl 1) = natSyms v ++ crest →
      S (.inl 2) = permHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) →
      Runs PT S (Function.update (Function.update S (.inl 2) []) (.inl 3)
          (hdrSyms [roundJ0 ℓ K a v, D, addrBits a - roundJ0 ℓ K a v - D * K, roundRho ℓ K v] ++
            S (.inl 3)))
        (fun _ => True) (CT * (w + addrBits a + 1) ^ 3))
    (hsL : ∀ (P d r w K m j₀ D nS ρ : ℕ) (z : RArr (Cube m) r) (rest hrest : List Sym)
      (S : KLoc (Fin 2) EL → List Sym),
      KClean S → j₀ + D * K + nS = m → ρ < K → P + 2 ≤ w → d ≤ w + m → K ≤ w + m →
      Band (layerRT P d r w K j₀ D nS ρ) → ArrOnDiskGrid P z → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube P z) ++ rest →
      S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest →
      Runs PL S
        (Function.update S (.inl 0)
          (carrSyms w (encCube P (truncArr P (hT (slicePos m K j₀ D ρ) z))) ++ rest))
        (fun _ => True)
        (CLc * (layerCost lam' (layerRT P d r w K j₀ D nS ρ) + (w + m + 1) ^ JL +
          (sliceHdr P d r w K m j₀ D nS ρ).length))) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R : Type)
      (Pr : Prog (KLoc (Fin 4) E) (fun _ => Sym) R), Finite R ∧ Nonempty R ∧ Pr.Closed ∧
      ∀ (q ℓ K w D v : ℕ) (a : Fin D → ℕ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
        (rest hrest crest : List Sym) (S : KLoc (Fin 4) E → List Sym),
        KClean S → MidShapeOK q ℓ K w a → IsChunkRound ℓ K v →
        roundJ0 ℓ K a v + D * K ≤ addrBits a →
        Band (layerRT q (D + 1) (2 ^ ℓ) w K (roundJ0 ℓ K a v) D
          (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)) →
        ArrOnDiskGrid q z → BlkTerm rest → TermOK crest →
        S (.inl 0) = carrSyms w (encCube q z) ++ rest →
        S (.inl 1) = midHdr q ℓ K w a ++ hrest →
        S (.inl 3) = natSyms v ++ crest →
        Runs Pr S
          (Function.update S (.inl 0)
            (carrSyms w (encCube q (truncArr q (hT (slicePos (addrBits a) K (roundJ0 ℓ K a v) D
              (roundRho ℓ K v)) z))) ++ rest))
          (fun _ => True)
          ((2 * CH + CT + 21 * CLc + 43) *
            (layerCost lam' (layerRT q (D + 1) (2 ^ ℓ) w K (roundJ0 ℓ K a v) D
              (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)) +
            (w + addrBits a + 1) ^ (JH + JL + 4) + (midHdr q ℓ K w a).length)) := by
  refine ⟨ChE EH EL, iFE, iDE, ChR RH RT RL, chunkProg PH PT PL, inferInstance, inferInstance,
    closed_chunkProg hcH hcT hcL, ?_⟩
  intro q ℓ K w D v a z rest hrest crest S hcl hsh hc hle hband hz hrestT hcr h0 h1 h3
  have hcl' : ∀ e, S (.inr e) = [] := hcl
  have hDm := le_addrBits_D hsh
  have hsh' := hsh
  obtain ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hw⟩ := hsh'
  have hK0 : 0 < K := by omega
  have hρK : roundRho ℓ K v < K := Nat.mod_lt _ hK0
  -- intermediate stacks
  obtain ⟨S1, hS1⟩ : ∃ S', S' = Function.update S stT
      (permHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) ++ []) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S', S' = Function.update (Function.update S1 stT []) stH
      (hdrSyms [roundJ0 ℓ K a v, D, addrBits a - roundJ0 ℓ K a v - D * K, roundRho ℓ K v] ++
        []) := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ S', S' = Function.update S2 stH
      (permHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) ++
        (hdrSyms [roundJ0 ℓ K a v, D, addrBits a - roundJ0 ℓ K a v - D * K, roundRho ℓ K v] ++
          [])) := ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ S', S' = Function.update S3 (.inl 0)
      (carrSyms w (encCube q (truncArr q (hT (slicePos (addrBits a) K (roundJ0 ℓ K a v) D
        (roundRho ℓ K v)) z))) ++ rest) := ⟨_, rfl⟩
  -- step 1: the descriptor header onto `T`
  have hr1 : Runs (callInj (embH stT) (@lnH RH RT RL) PH) S S1 (fun _ => True)
      (CH * ((w + addrBits a + 1) ^ JH + (midHdr q ℓ K w a).length)) := by
    have hP := hsH q ℓ K w D a hrest [] (S ∘ embH stT) (fun e => hcl' _) hsh
      (by simpa [embH] using h1) (by simp [embH, hcl'])
    have h := runs_callInj_update embH_injective_T (@lnH RH RT RL) hP
    refine WP.W9comp.runs_congr h ?_
    rw [hS1]
    simp [embH]
  -- step 2: the tail onto `H`
  have hr2 : Runs (callInj embT (@lnT RH RT RL) PT) S1 S2 (fun _ => True)
      (CT * (w + addrBits a + 1) ^ 3) := by
    have hP := hsT q ℓ K w D v a hrest crest (S1 ∘ embT)
      (fun j => by rw [hS1]; simp [embT, hcl']) hsh hc hcr
      (by rw [hS1]; simpa [embT] using h1) (by rw [hS1]; simpa [embT] using h3)
      (by rw [hS1]; simp [embT])
    have h := runs_callInj_update2 embT_injective (@lnT RH RT RL) hP
    refine WP.W9comp.runs_congr h ?_
    rw [hS2, hS1]
    simp [embT, hcl']
  -- step 3: the descriptor header onto `H`
  have hr3 : Runs (callInj (embH stH) (@lnH RH RT RL) PH) S2 S3 (fun _ => True)
      (CH * ((w + addrBits a + 1) ^ JH + (midHdr q ℓ K w a).length)) := by
    have hP := hsH q ℓ K w D a hrest
      (hdrSyms [roundJ0 ℓ K a v, D, addrBits a - roundJ0 ℓ K a v - D * K, roundRho ℓ K v] ++ [])
      (S2 ∘ embH stH) (fun e => by rw [hS2, hS1]; simp [embH, hcl']) hsh
      (by rw [hS2, hS1]; simpa [embH] using h1) (by rw [hS2]; simp [embH])
    have h := runs_callInj_update embH_injective_H (@lnH RH RT RL) hP
    refine WP.W9comp.runs_congr h ?_
    rw [hS3]
    simp [embH]
  -- step 4: the layer call
  have hH3 : S3 stH = sliceHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) (roundJ0 ℓ K a v) D
      (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v) ++ [] := by
    rw [hS3, sliceHdr_eq]
    simp
  have hr4 : Runs (callInj embL (@lnL RH RT RL) PL) S3 S4 (fun _ => True)
      (CLc * (layerCost lam' (layerRT q (D + 1) (2 ^ ℓ) w K (roundJ0 ℓ K a v) D
          (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)) + (w + addrBits a + 1) ^ JL +
        (sliceHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) (roundJ0 ℓ K a v) D
          (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)).length)) := by
    have hP := hsL q (D + 1) (2 ^ ℓ) w K (addrBits a) (roundJ0 ℓ K a v) D
      (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v) z rest [] (S3 ∘ embL)
      (fun e => by rw [hS3, hS2, hS1]; simp [embL, hcl']) (by omega) hρK (by omega) (by omega)
      (by omega) hband hz hrestT (by rw [hS3, hS2, hS1]; simpa [embL] using h0)
      (by simpa [embL] using hH3)
    have h := runs_callInj_update embL_injective (@lnL RH RT RL) hP
    refine WP.W9comp.runs_congr h ?_
    rw [hS4]
    simp [embL]
  -- step 5: empty `H`
  have hr5 : Runs (callInj id (@lnB RH RT RL) (drainProg stH)) S4
      (Function.update S4 stH []) (fun _ => True) (2 * (S4 stH).length + 3) :=
    runs_callInj_update (ι := id) Function.injective_id lnB (runs_drainProg stH (S4 ∘ id))
  have hall := WP.W9comp.runs_seq hr1 (WP.W9comp.runs_seq hr2 (WP.W9comp.runs_seq hr3
    (WP.W9comp.runs_seq hr4 hr5)))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · -- the final stacks
    rw [hS4, hS3, hS2, hS1]
    funext k
    by_cases hk0 : k = .inl 0
    · subst hk0
      simp
    · by_cases hkT : k = stT
      · subst hkT
        simp [hcl']
      · by_cases hkH : k = stH
        · subst hkH
          simp [hcl']
        · simp [hk0, hkT, hkH]
  · -- the cost
    have hH4 : (S4 stH).length = (sliceHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) (roundJ0 ℓ K a v) D
        (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)).length := by
      rw [hS4, Function.update_of_ne (by simp), hH3, List.append_nil]
    rw [hH4]
    have hX : 1 ≤ w + addrBits a + 1 := by omega
    have hS := length_sliceHdr_le (q := q) (D := D) (ℓ := ℓ) (K := K) (w := w) (m := addrBits a)
      (j₀ := roundJ0 ℓ K a v) (nS := addrBits a - roundJ0 ℓ K a v - D * K) (ρ := roundRho ℓ K v)
      (X := w + addrBits a + 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    generalize (sliceHdr q (D + 1) (2 ^ ℓ) w K (addrBits a) (roundJ0 ℓ K a v) D
      (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)).length = Sl at hS ⊢
    generalize layerCost lam' (layerRT q (D + 1) (2 ^ ℓ) w K (roundJ0 ℓ K a v) D
      (addrBits a - roundJ0 ℓ K a v - D * K) (roundRho ℓ K v)) = Lc
    generalize (midHdr q ℓ K w a).length = Hm
    generalize hXdef : w + addrBits a + 1 = X at hX hS ⊢
    have p1 : X ^ JH ≤ X ^ (JH + JL + 4) := pow_le_pow_X hX (by omega)
    have p2 : X ^ 3 ≤ X ^ (JH + JL + 4) := pow_le_pow_X hX (by omega)
    have p3 : X ^ JL ≤ X ^ (JH + JL + 4) := pow_le_pow_X hX (by omega)
    have p4 : X ≤ X ^ (JH + JL + 4) := by
      calc X = X ^ 1 := (pow_one X).symm
        _ ≤ X ^ (JH + JL + 4) := pow_le_pow_X hX (by omega)
    generalize X ^ (JH + JL + 4) = XJ at p1 p2 p3 p4 ⊢
    have q1 : CH * (X ^ JH + Hm) ≤ CH * (Lc + XJ + Hm) := Nat.mul_le_mul_left _ (by omega)
    have q2 : CT * X ^ 3 ≤ CT * (Lc + XJ + Hm) := Nat.mul_le_mul_left _ (by omega)
    have q3 : CLc * (Lc + X ^ JL + Sl) ≤ CLc * (21 * (Lc + XJ + Hm)) :=
      Nat.mul_le_mul_left _ (by omega)
    have e1 : CLc * (21 * (Lc + XJ + Hm)) = 21 * (CLc * (Lc + XJ + Hm)) := by ring
    have e2 : (2 * CH + CT + 21 * CLc + 43) * (Lc + XJ + Hm) = 2 * (CH * (Lc + XJ + Hm)) +
        CT * (Lc + XJ + Hm) + 21 * (CLc * (Lc + XJ + Hm)) + 43 * (Lc + XJ + Hm) := by ring
    omega

end SubNLogN.Machine.FFT.ChunkAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Math.Walsh SubNLogN.Machine.FFT.ChunkAux

/-- **K4.5, a chunk round is one layer call** (Theorem 6.5, `thm:direct-fft`, and Lemma 6.3): from the layer call
on a slice (`CubeLayerStmt`, K3.0), with the proved descriptor-header generator
(`permHdrGen_holds`) and the proved tail builder (`tail_exists`). -/
theorem chunkRound_of_cubeLayer {Band : LayerRT → Prop} {lam' : ℝ}
    (hL : CubeLayerStmt Band lam') : ChunkRoundStmt Band lam' := by
  obtain ⟨JL, CLc, hL⟩ := hL
  obtain ⟨JH, CH, hH⟩ := permHdrGen_holds
  obtain ⟨EL, iFL, iDL, RL, PL, iRL, iNL, hcL, hsL⟩ := hL ()
  obtain ⟨EH, iFH, iDH, RH, PH, iRH, iNH, hcH, hsH⟩ := hH ()
  obtain ⟨CT, RT, PT, iRT, iNT, hcT, hsT⟩ := tail_exists
  exact ⟨JH + JL + 4, 2 * CH + CT + 21 * CLc + 43, fun _ =>
    chunk_contract (iDH := iDH) (iDL := iDL)
      (iFE := fintypeSumC inferInstance (fintypeSumC inferInstance (fintypeSumC iFH iFL)))
      (iDE := decEqSumC inferInstance (decEqSumC inferInstance (decEqSumC iDH iDL)))
      hcH hcT hcL hsH hsT hsL⟩

end SubNLogN.Machine
