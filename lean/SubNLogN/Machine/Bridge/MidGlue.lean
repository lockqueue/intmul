/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Bridge
import SubNLogN.Machine.Bridge.MidIndex
import WP.W9comp.Kit

/-!
# K5 middle glue (`Bridge/MidGlue.lean`): the bridge's middle interface from the Walsh middle

The bridge machine (`BridgeMachineStmt`) calls the middle transform through `MidMachineStmt F`
(`Contracts/Bridge.lean`): one-coefficient records in natural frequency order
`idxAddrsFreq t`, in place. The Walsh middle (`WalshMiddleMachineGenStmt Band lam'`,
`Contracts/FFT.lean`, Corollary 6.6 (`cor:walsh-middle`)) works on the cube array
`ofTensor a ℓ U`: records of `r = 2^ℓ` coefficients (the last-axis lines). By
`cubeAddrs_flatMap_tensorIdx` (`MidIndex.lean`) the coefficients of the cube records, record by
record, are exactly the flat records in `idxAddrsFreq` order, so the glue is a pure change of
record boundaries on the stack:
* `MidGroupStmt`: delete every record end except every `r`-th one (`r = 2^ℓ`, `ℓ` read from the
  middle header);
* `MidUngroupStmt`: put a record end after every coefficient (`2w` bits, `w` read from the
  header).

**Program** (`midMachine_of_walsh`): `group ; walsh middle ; ungroup`, all three on the same two
named stacks (`0` the array, `1` the middle header `midHdr`), private scratch disjoint.

**The family** (`walshFam G Band lam' J`): index type and bridge parameters from `G`
(`WalshFamData`); shape `t = fftShape a ℓ`, `d = D + 1`; middle
`walshMiddle idealLayer (P+2) D ℓ K a` (`walshMid ρ p0 K0` at `G` = the `F_new` data);
header `[P+2, D, ℓ, K, wI] ++ a` (= `midHdr`); eligibility `MidShapeOK ∧ MidCallsBand Band` at
`q = P + 2`, width `wI`; cost `midCost lam' J D ℓ K wI m₀ + glueCost ℓ wI m₀`.

**Scope (honest summary).** Statements `MidGroupStmt`, `MidUngroupStmt` (glue kernels, proved
elsewhere), the family `walshFam`, and the proved reduction
`midMachine_of_walsh : WalshMiddleMachineGenStmt Band lam' → MidGroupStmt → MidUngroupStmt →
∃ J, ∀ G, MidMachineStmt (walshFam G Band lam' J)`. No other hypotheses.
-/

namespace SubNLogN.Machine.BridgeRed

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Common
  SubNLogN.Math.Walsh
open WP.W9comp (runs_seq runs_mono runs_congr closed_seq)

/-! ## Glue contracts -/

/-- One-coefficient records `[c]` of a coefficient list. -/
def singles (cs : List CInt) : List (List CInt) := cs.map fun c => [c]

/-- **[CONTRACT] Regroup glue** (flat records → `2^ℓ`-coefficient records, in place).
Named stacks (`Fin 2`): `0` the array, `1` the middle header `midHdr q ℓ K w a` (restored).
For records `ws` of exactly `2^ℓ` coefficients each, stack `0` goes from the one-coefficient
records of `ws.flatten` to the records `ws` (the coefficient bits are untouched; only record ends
are deleted). Cost `C·((ℓ+1)·(vol + 1) + |midHdr|)` with `vol = vol1 |ws.flatten| w` (e.g. `ℓ`
pair-merging passes). -/
def MidGroupStmt : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ _ C Pg =>
    ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (ws : List (List CInt)) (rest hrest : List Sym)
      (S : KLoc (Fin 2) E → List Sym),
      KClean S → (∀ x ∈ ws, x.length = 2 ^ ℓ) → BlkTerm rest →
      S (.inl 0) = carrSyms w (singles ws.flatten) ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      Runs Pg S (Function.update S (.inl 0) (carrSyms w ws ++ rest)) (fun _ => True)
        (C * ((ℓ + 1) * (vol1 ws.flatten.length w + 1) + (midHdr q ℓ K w a).length))

/-- **[CONTRACT] Ungroup glue** (records → one-coefficient records, in place).
Named stacks (`Fin 2`): `0` the array, `1` the middle header `midHdr q ℓ K w a` (restored).
For any records `ws` and `1 ≤ w`, stack `0` goes from the records `ws` to the one-coefficient
records of `ws.flatten` (a record end after every `2w`-bit coefficient, the old ends deleted).
Cost `C·(vol + |ws| + w + 1 + |midHdr|)`, `vol = vol1 |ws.flatten| w`. -/
def MidUngroupStmt : Prop :=
  KContract (Fin 2) Unit fun _ E _ _ _ C Pg =>
    ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (ws : List (List CInt)) (rest hrest : List Sym)
      (S : KLoc (Fin 2) E → List Sym),
      KClean S → 1 ≤ w → BlkTerm rest →
      S (.inl 0) = carrSyms w ws ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      Runs Pg S (Function.update S (.inl 0) (carrSyms w (singles ws.flatten) ++ rest))
        (fun _ => True)
        (C * (vol1 ws.flatten.length w + ws.length + w + 1 + (midHdr q ℓ K w a).length))

/-! ## The Walsh family -/

/-- Data of a bridge family whose middle is the Walsh middle: index type, the bridge parameters
other than the shape, and the direct-FFT shape data (`d = D + 1`, `t = fftShape a ℓ`, chunk
width `K`). -/
structure WalshFamData : Type 1 where
  /-- runtime index type -/
  Ix : Type
  /-- output precision -/
  p : Ix → ℕ
  /-- working precision (`q = P + 2`) -/
  P : Ix → ℕ
  /-- alias width -/
  ω : Ix → ℕ
  /-- internal record width (also the middle's width `w`) -/
  wI : Ix → ℕ
  /-- table entry width -/
  wT : Ix → ℕ
  /-- output record width -/
  wOut : Ix → ℕ
  /-- input precision -/
  pIn : Ix → ℕ
  /-- input record width -/
  wIn : Ix → ℕ
  /-- number of record axes -/
  D : Ix → ℕ
  /-- record-axis exponents -/
  a : (s : Ix) → Fin (D s) → ℕ
  /-- last-axis exponent (`r = 2^ℓ`) -/
  ℓ : Ix → ℕ
  /-- chunk width -/
  K : Ix → ℕ

/-- Explicit cost of the two glue kernels: `(ℓ + 2)·(vol + 1) + w + 2^{m₀}` with
`vol = vol1 (2^{m₀}·2^ℓ) w` (lower order than `midCost`, which contains `ℓ·cvolCube`). -/
def glueCost (ℓ w m : ℕ) : ℕ := (ℓ + 2) * (vol1 (2 ^ m * 2 ^ ℓ) w + 1) + w + 2 ^ m

/-- **The bridge family of the Walsh middle** (with WF's cost exponent `J`). -/
noncomputable def walshFam (G : WalshFamData) (Band : LayerRT → Prop) (lam' : ℝ) (J : ℕ) :
    BrFam where
  Ix := G.Ix
  par s := { p := G.p s, P := G.P s, ω := G.ω s, wI := G.wI s, wT := G.wT s, wOut := G.wOut s,
             pIn := G.pIn s, wIn := G.wIn s, d := G.D s + 1, t := fftShape (G.a s) (G.ℓ s) }
  run s := walshMiddle idealLayer (G.P s + 2) (G.D s) (G.ℓ s) (G.K s) (G.a s)
  mhdr s := [G.P s + 2, G.D s, G.ℓ s, G.K s, G.wI s] ++ List.ofFn (G.a s)
  MOK s := MidShapeOK (G.P s + 2) (G.ℓ s) (G.K s) (G.wI s) (G.a s) ∧
    MidCallsBand Band (G.P s + 2) (G.ℓ s) (G.K s) (G.wI s) (G.a s)
  Tmid s := midCost lam' J (G.D s) (G.ℓ s) (G.K s) (G.wI s) (addrBits (G.a s)) +
    glueCost (G.ℓ s) (G.wI s) (addrBits (G.a s))

/-! ## Data identities (via `cubeAddrs_flatMap_tensorIdx`) -/

section Data

variable {D : ℕ}

/-- The flat records of a tensor in natural frequency order are the one-coefficient records of the
flattened cube array. -/
theorem encT_eq_singles_encCube (q : ℕ) (a : Fin D → ℕ) (ℓ : ℕ) (U : Idx (fftShape a ℓ) → ℂ) :
    encT q (idxAddrsFreq (fftShape a ℓ)) U = singles (encCube q (ofTensor a ℓ U)).flatten := by
  rw [← cubeAddrs_flatMap_tensorIdx a ℓ]
  simp only [encT, recsAt, singles, encCube, encArr, ofTensor, ← List.flatMap_def,
    List.map_flatMap, List.map_map, Function.comp_def]

theorem length_encCube_rec (q : ℕ) (a : Fin D → ℕ) (ℓ : ℕ)
    (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) : ∀ x ∈ encCube q z, x.length = 2 ^ ℓ := by
  intro x hx
  simp only [encCube, encArr, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  simp

theorem length_encCube (q : ℕ) (a : Fin D → ℕ) (ℓ : ℕ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ)) :
    (encCube q z).length = 2 ^ addrBits a := by
  simp [encCube, encArr, cubeAddrs]

theorem length_flatten_encCube (q : ℕ) (a : Fin D → ℕ) (ℓ : ℕ) (U : Idx (fftShape a ℓ) → ℂ) :
    (encCube q (ofTensor a ℓ U)).flatten.length = 2 ^ addrBits a * 2 ^ ℓ := by
  have h2 : (encT q (idxAddrsFreq (fftShape a ℓ)) U).length = 2 ^ addrBits a * 2 ^ ℓ := by
    simp only [encT, recsAt, idxAddrsFreq, List.length_map, List.length_finRange]
    exact totalLen_fftShape a ℓ
  rw [encT_eq_singles_encCube, singles, List.length_map] at h2
  exact h2

end Data

/-! ## Embedding the three kernels -/

/-- Embedding of a kernel on `KLoc (Fin 2) Ek` into the composite `KLoc (Fin 2) EP`: named stacks
fixed, scratch through `inj`. -/
def ιF {Ek EP : Type} (inj : Ek → EP) : KLoc (Fin 2) Ek → KLoc (Fin 2) EP
  | .inl i => .inl i
  | .inr e => .inr (inj e)

theorem ιF_injective {Ek EP : Type} {inj : Ek → EP} (h : Function.Injective inj) :
    Function.Injective (ιF inj) := by
  rintro (a | a) (b | b) hab <;> simp_all [ιF, h.eq_iff]

theorem kClean_comp_ιF {Ek EP : Type} (inj : Ek → EP) {S : KLoc (Fin 2) EP → List Sym}
    (hS : KClean S) : KClean (S ∘ ιF inj) := fun e => hS (inj e)

theorem kClean_update_inl {E : Type} [DecidableEq E] {S : KLoc (Fin 2) E → List Sym}
    (hS : KClean S) (i : Fin 2) (v : List Sym) : KClean (Function.update S (.inl i) v) :=
  fun e => by
    rw [Function.update_of_ne (by simp)]
    exact hS e

/-- **Calling a kernel inside the composite** (in place on stack `0`). -/
theorem runs_partF {Ek EP Rk σ : Type} [DecidableEq Ek] [DecidableEq EP] {inj : Ek → EP}
    (hinj : Function.Injective inj) (l : Lens σ Rk) {P : Prog (KLoc (Fin 2) Ek) (fun _ => Sym) Rk}
    {S : KLoc (Fin 2) EP → List Sym} {v : List Sym} {Q : Rk → Prop} {T : ℕ}
    (h : Runs P (S ∘ ιF inj) (Function.update (S ∘ ιF inj) (.inl 0) v) Q T) :
    Runs (callInj (ιF inj) l P) S (Function.update S (.inl 0) v) (fun _ => True) T := by
  have hc : Function.update S (.inl 0) v ∘ ιF inj = Function.update (S ∘ ιF inj) (.inl 0) v :=
    Function.update_comp_eq_of_injective S (ιF_injective hinj) (.inl 0) v
  refine runs_callInj (ιF_injective hinj) l (by rw [hc]; exact h) ?_
  intro k hk
  rcases k with i | e
  · exact absurd rfl (hk (.inl i))
  · exact Function.update_of_ne (by simp) _ _

/-- Cost arithmetic of `midMachine_of_walsh`. -/
theorem glue_cost_aux (CG CW CU M H l w Mm x y z : ℕ) (hx : x = Mm * 2 ^ l)
    (hy : y = Mm * 2 ^ l) (hz : z = Mm) :
    CG * ((l + 1) * (vol1 x w + 1) + H) + (CW * (M + H) + CU * (vol1 y w + z + w + 1 + H)) ≤
      (CG + CW + CU) * (M + ((l + 2) * (vol1 (Mm * 2 ^ l) w + 1) + w + Mm) + H) := by
  rw [hx, hy, hz]
  generalize vol1 (Mm * 2 ^ l) w = V
  have e1 : (l + 1) * (V + 1) + H ≤ M + ((l + 2) * (V + 1) + w + Mm) + H := by nlinarith
  have e2 : M + H ≤ M + ((l + 2) * (V + 1) + w + Mm) + H := by omega
  have e3 : V + Mm + w + 1 + H ≤ M + ((l + 2) * (V + 1) + w + Mm) + H := by nlinarith
  calc CG * ((l + 1) * (V + 1) + H) + (CW * (M + H) + CU * (V + Mm + w + 1 + H))
      ≤ CG * (M + ((l + 2) * (V + 1) + w + Mm) + H) +
        (CW * (M + ((l + 2) * (V + 1) + w + Mm) + H) +
          CU * (M + ((l + 2) * (V + 1) + w + Mm) + H)) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e1)
          (Nat.add_le_add (Nat.mul_le_mul_left _ e2) (Nat.mul_le_mul_left _ e3))
    _ = (CG + CW + CU) * (M + ((l + 2) * (V + 1) + w + Mm) + H) := by ring

/-! ## The reduction -/

/-- **`MidMachineStmt` for the Walsh family** (Definition 4.5 (`def:middle-contract`),
realized by Corollary 6.6 (`cor:walsh-middle`)): from the Walsh middle and the two glue
kernels. Program `group ; middle ; ungroup`; `J` is the middle's cost exponent. The eligibility
`MOK` of `walshFam` supplies `MidShapeOK` and `MidCallsBand`; the disk condition of the middle
input follows from `‖U‖_∞ ≤ 1/8`. -/
theorem midMachine_of_walsh (Band : LayerRT → Prop) (lam' : ℝ)
    (hW : WalshMiddleMachineGenStmt Band lam') (hG : MidGroupStmt) (hU : MidUngroupStmt) :
    ∃ J, ∀ G : WalshFamData, MidMachineStmt (walshFam G Band lam' J) := by
  obtain ⟨J, CW, hW⟩ := hW
  obtain ⟨CG, hG⟩ := hG
  obtain ⟨CU, hU⟩ := hU
  obtain ⟨EW, _, _, RW, PW, _, _, hcW, sW⟩ := hW ()
  obtain ⟨EG, _, _, RG, PG, _, _, hcG, sG⟩ := hG ()
  obtain ⟨EU, _, _, RU, PU, _, _, hcU, sU⟩ := hU ()
  refine ⟨J, fun G => ⟨CG + CW + CU, fun _ => ⟨EG ⊕ EW ⊕ EU, inferInstance, inferInstance,
    RG × RW × RU,
    .seq (callInj (ιF (Sum.inl : EG → EG ⊕ EW ⊕ EU)) (Lens.fst RG (RW × RU)) PG)
      (.seq (callInj (ιF (fun e : EW => (Sum.inr (Sum.inl e) : EG ⊕ EW ⊕ EU)))
          ((Lens.snd RG (RW × RU)).comp (Lens.fst RW RU)) PW)
        (callInj (ιF (fun e : EU => (Sum.inr (Sum.inr e) : EG ⊕ EW ⊕ EU)))
          ((Lens.snd RG (RW × RU)).comp (Lens.snd RW RU)) PU)),
    inferInstance, inferInstance,
    closed_seq (closed_callInj _ _ hcG)
      (closed_seq (closed_callInj _ _ hcW) (closed_callInj _ _ hcU)), ?_⟩⟩⟩
  refine fun (s : G.Ix) (U : Idx (fftShape (G.a s) (G.ℓ s)) → ℂ) rest rh S hMOK hS hw hUg hUn _ _
    hrest hS0 hS1 => ?_
  obtain ⟨hshape, hband⟩ := hMOK
  have hinjG : Function.Injective (Sum.inl : EG → EG ⊕ EW ⊕ EU) := Sum.inl_injective
  have hinjW : Function.Injective (fun e : EW => (Sum.inr (Sum.inl e) : EG ⊕ EW ⊕ EU)) :=
    fun _ _ h => Sum.inl_injective (Sum.inr_injective h)
  have hinjU : Function.Injective (fun e : EU => (Sum.inr (Sum.inr e) : EG ⊕ EW ⊕ EU)) :=
    fun _ _ h => Sum.inr_injective (Sum.inr_injective h)
  have hS0' : S (.inl 0) = carrSyms (G.wI s)
      (singles (encCube (G.P s + 2) (ofTensor (G.a s) (G.ℓ s) U)).flatten) ++ rest := by
    rw [← encT_eq_singles_encCube]
    exact hS0
  have hS1' : S (.inl 1) = midHdr (G.P s + 2) (G.ℓ s) (G.K s) (G.wI s) (G.a s) ++ rh := hS1
  -- (1) group
  have r1 := runs_partF hinjG (Lens.fst RG (RW × RU))
    (sG (G.P s + 2) (G.ℓ s) (G.K s) (G.wI s) (G.D s) (G.a s)
      (encCube (G.P s + 2) (ofTensor (G.a s) (G.ℓ s) U)) rest rh
      (S ∘ ιF (Sum.inl : EG → EG ⊕ EW ⊕ EU)) (kClean_comp_ιF _ hS)
      (length_encCube_rec _ _ _ _) hrest hS0' hS1')
  -- (2) the Walsh middle
  have r2 := runs_partF hinjW ((Lens.snd RG (RW × RU)).comp (Lens.fst RW RU))
    (sW (G.P s + 2) (G.ℓ s) (G.K s) (G.wI s) (G.D s) (G.a s) U rest rh
      (Function.update S (.inl 0)
        (carrSyms (G.wI s) (encCube (G.P s + 2) (ofTensor (G.a s) (G.ℓ s) U)) ++ rest) ∘
        ιF (fun e : EW => (Sum.inr (Sum.inl e) : EG ⊕ EW ⊕ EU)))
      (kClean_comp_ιF _ (kClean_update_inl hS _ _)) hshape hband
      (fun j => ⟨hUg j, le_trans (norm_le_pi_norm U j) (le_trans hUn (by norm_num))⟩) hrest
      (by simp [ιF])
      (by
        simp only [Function.comp, ιF]
        rw [Function.update_of_ne (by simp)]
        exact hS1'))
  rw [Function.update_idem] at r2
  -- (3) ungroup
  have r3 := runs_partF hinjU ((Lens.snd RG (RW × RU)).comp (Lens.snd RW RU))
    (sU (G.P s + 2) (G.ℓ s) (G.K s) (G.wI s) (G.D s) (G.a s)
      (encCube (G.P s + 2) (ofTensor (G.a s) (G.ℓ s)
        (walshMiddle idealLayer (G.P s + 2) (G.D s) (G.ℓ s) (G.K s) (G.a s) U))) rest rh
      (Function.update S (.inl 0)
        (carrSyms (G.wI s) (encCube (G.P s + 2) (ofTensor (G.a s) (G.ℓ s)
          (walshMiddle idealLayer (G.P s + 2) (G.D s) (G.ℓ s) (G.K s) (G.a s) U))) ++ rest) ∘
        ιF (fun e : EU => (Sum.inr (Sum.inr e) : EG ⊕ EW ⊕ EU)))
      (kClean_comp_ιF _ (kClean_update_inl hS _ _)) hw hrest
      (by simp [ιF])
      (by
        simp only [Function.comp, ιF]
        rw [Function.update_of_ne (by simp)]
        exact hS1'))
  rw [Function.update_idem] at r3
  have h123 := runs_seq r1 (runs_seq r2 r3)
  refine runs_mono (runs_congr h123 ?_) (fun _ _ => trivial) ?_
  · show _ = Function.update S (.inl 0) (carrSyms (G.wI s)
      (encT (G.P s + 2) (idxAddrsFreq (fftShape (G.a s) (G.ℓ s)))
        (walshMiddle idealLayer (G.P s + 2) (G.D s) (G.ℓ s) (G.K s) (G.a s) U)) ++ rest)
    rw [encT_eq_singles_encCube]
  · exact glue_cost_aux CG CW CU _ _ (G.ℓ s) (G.wI s) (2 ^ addrBits (G.a s)) _ _ _
      (length_flatten_encCube _ _ _ _) (length_flatten_encCube _ _ _ _) (length_encCube _ _ _ _)

end SubNLogN.Machine.BridgeRed
