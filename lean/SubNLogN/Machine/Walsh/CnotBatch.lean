/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotBatchMath
import SubNLogN.Machine.Walsh.CnotLeaf

/-!
# K3-PERM (`Machine/Walsh/CnotBatch.lean`): Proposition 5.5 on the machine, from its parts

**Scope (honest summary).** A sequencing reduction: `cnotBatchMachine_of` proves
`CnotBatchMachineStmt Band lam'` (`Contracts/Walsh.lean`) from the layer call on a cube slice
(`CubeLayerStmt Band lam'`), the exact lift and lowering (`LiftMachineStmt`, `LowerMachineStmt`)
and the two leaf contracts stated below. The composite program and every step of its
correctness and cost proof are proved here.

## Leaf contracts (named hypotheses, stated in `Machine/Walsh/CnotLeaf.lean`)
* `CnotHdrStmt` — the header builder of a batch: from `sliceHdr P d r w K m j₀ D nS ρ` it writes
  the lift/lowering header `hdrSyms [w, 8d]` and the lifted slice header
  `sliceHdr (P+8d) d r (w+8d) K m j₀ D nS ρ` (Lemma 5.3, Proposition 5.5). Cost `C·(|sliceHdr| + 1)`.
* `CnotScanStmt mode` — one recordwise scan of the lifted array (`P_* = P + 8d`, `w_* = w + 8d`),
  reading the slice header and the pair list: `mode = selPhase` the diagonal `S_U` with
  `U = Sel ∖ T` (Section 5.1, eq. (`eq:walsh-SU`)); `mode = cz` the sign diagonal `CZ` (Section 5.2,
  eq. (`eq:walsh-CZ`), computed once per record, Proposition 5.5); `mode = selScalar` the scalar
  `2^s[2(1-i)]^{q_sel}` of Lemma 5.1 (`lem:walsh-select`, one scan); `mode = shift` the final `×2^s`
  (Proposition 5.5). Cost `C·(V_* + 2^m·((w + m + 1)^J + |pairsSyms|) + |sliceHdr|)`.

## The composite (Proposition 5.5, `prop:cnot-batch`)
`hdr; lift; G; CZ; G; shift; lower; drain(hA); drain(hB)` with the gadget
`G = S_U; layer; S_U; layer; S_U; layer; selScalar` (eq. (`eq:walsh-three-layer`)), six layer calls in all.
Layout `KLoc (Fin 3) (Fin 2 ⊕ X)`: named stacks array / slice header / pairs as in the contract,
private `hA` (`hdrSyms [w, 8d]`) and `hB` (lifted slice header), then the parts' private scratch.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common

/-! ## The composite's layout -/

namespace CnotBatchRed

open WP.W9comp (runs_seq runs_mono runs_congr lsnd)

/-! ## Generic helpers (as in `Machine/FFT/Kit.lean`, copied to keep this file self-contained) -/

section Drain

variable {K : Type} [DecidableEq K]

/-- Pop one symbol of stack `k`; the register records whether a symbol was popped. -/
def drainStep (k : K) : Prog K (fun _ => Sym) Bool := .pop k (fun _ o => o.isSome)

/-- Empty stack `k`: pop, and keep popping while the last pop found a symbol. -/
def drainProg (k : K) : Prog K (fun _ => Sym) Bool := .seq (drainStep k) (.loop id (drainStep k))

omit [DecidableEq K] in
theorem closed_drainProg (k : K) : (drainProg k).Closed := by
  simp [drainProg, drainStep, Prog.Closed, Prog.FreeBelow]

/-- The drain loop, entered after a successful pop. -/
theorem drain_loop_eval (k : K) : ∀ (L : List Sym) (S : K → List Sym), S k = L →
    Eval [] (.loop id (drainStep k)) ⟨true, S⟩ ⟨false, Function.update S k []⟩
      (2 * L.length + 3)
  | [], S, hS => by
    have h1 : Eval [] (drainStep k) ⟨true, S⟩ ⟨false, Function.update S k []⟩ 1 :=
      (Eval.pop [] k (fun _ o => o.isSome) true S).of_eq (by rw [hS]; rfl) rfl
    have h2 : Eval [] (.loop id (drainStep k)) ⟨false, Function.update S k []⟩
        ⟨false, Function.update S k []⟩ 1 := Eval.loop_false rfl
    exact (Eval.loop_true (c := id) rfl h1 h2).of_eq rfl (by simp)
  | x :: L, S, hS => by
    have h1 : Eval [] (drainStep k) ⟨true, S⟩ ⟨true, Function.update S k L⟩ 1 :=
      (Eval.pop [] k (fun _ o => o.isSome) true S).of_eq (by rw [hS]; rfl) rfl
    have ih := drain_loop_eval k L (Function.update S k L) (by simp)
    refine (Eval.loop_true (c := id) rfl h1 ih).of_eq ?_ ?_
    · simp [Function.update_idem]
    · simp only [List.length_cons]; ring

/-- **`drainProg` empties stack `k`** within `2·|S k| + 3` steps; every other stack is unchanged. -/
theorem runs_drainProg (k : K) (S : K → List Sym) :
    Runs (drainProg k) S (Function.update S k []) (fun _ => True) (2 * (S k).length + 3) := by
  apply Runs.of_eval
  intro v
  cases hS : S k with
  | nil =>
    refine ⟨false, 1 + 1, ?_, trivial, by simp⟩
    have h1 : Eval [] (drainStep k) ⟨v, S⟩ ⟨false, Function.update S k []⟩ 1 :=
      (Eval.pop [] k (fun _ o => o.isSome) v S).of_eq (by rw [hS]; rfl) rfl
    exact Eval.seq h1 (Eval.loop_false rfl)
  | cons x L =>
    refine ⟨false, 1 + (2 * L.length + 3), ?_, trivial, by simp only [List.length_cons]; omega⟩
    have h1 : Eval [] (drainStep k) ⟨v, S⟩ ⟨true, Function.update S k L⟩ 1 :=
      (Eval.pop [] k (fun _ o => o.isSome) v S).of_eq (by rw [hS]; rfl) rfl
    have h2 := drain_loop_eval k L (Function.update S k L) (by simp)
    exact (Eval.seq h1 h2).of_eq (by simp [Function.update_idem]) rfl

end Drain

section CallInj

variable {L K σ R : Type} [DecidableEq L] [DecidableEq K]

/-- **One-stack update along an injective embedding.** If the part `P` runs from `B ∘ ι` to
`B ∘ ι` with stack `x` replaced by `v`, then `callInj ι l P` runs from `B` to `B` with stack `ι x`
replaced by `v`, with the same cost. -/
theorem runs_callInj_update {ι : L → K} (hι : Function.Injective ι) (l : Lens σ R)
    {P : Prog L (fun _ => Sym) R} {B : K → List Sym} {x : L} {v : List Sym} {Q : R → Prop}
    {T : ℕ} (hP : Runs P (B ∘ ι) (Function.update (B ∘ ι) x v) Q T) :
    Runs (callInj ι l P) B (Function.update B (ι x) v) (fun _ => True) T := by
  refine runs_callInj (Q := Q) hι l ?_ ?_
  · rwa [Function.update_comp_eq_of_injective B hι x v]
  · intro k hk
    exact Function.update_of_ne (fun h => hk x h.symm) _ _

end CallInj

/-- Decidable equality of a sum from its summands, built explicitly (instance search on deeply
nested sums exceeds `synthInstance.maxSize`). -/
abbrev decEqSum {α β : Type} (ha : DecidableEq α) (hb : DecidableEq β) : DecidableEq (α ⊕ β) := by
  letI := ha
  letI := hb
  exact inferInstance

/-- `Fintype` of a sum from its summands, built explicitly. -/
abbrev fintypeSum {α β : Type} (ha : Fintype α) (hb : Fintype β) : Fintype (α ⊕ β) := by
  letI := ha
  letI := hb
  exact inferInstance

section Layout

variable {X : Type}

/-- Composite state: the initial stacks `S` with the array, `hA` and `hB` replaced. -/
def st [DecidableEq X] (S : KLoc (Fin 3) (Fin 2 ⊕ X) → List Sym) (a hA hB : List Sym) :
    KLoc (Fin 3) (Fin 2 ⊕ X) → List Sym :=
  Function.update (Function.update (Function.update S (.inl 0) a) (.inr (.inl 0)) hA)
    (.inr (.inl 1)) hB

/-- Embedding of a part with named stacks `N` (placed by `f`) and private scratch `Y` (placed by
`j` into the parts' block `X`). -/
def emb {N Y : Type} (f : N → KLoc (Fin 3) (Fin 2 ⊕ X)) (j : Y → X) :
    KLoc N Y → KLoc (Fin 3) (Fin 2 ⊕ X)
  | .inl i => f i
  | .inr e => .inr (.inr (j e))

theorem emb_injective {N Y : Type} {f : N → KLoc (Fin 3) (Fin 2 ⊕ X)} {j : Y → X}
    (hf : Function.Injective f) (hj : Function.Injective j)
    (hfj : ∀ i x, f i ≠ .inr (.inr x)) : Function.Injective (emb f j) := by
  rintro (i | e) (i' | e') h
  · exact congrArg Sum.inl (hf h)
  · exact absurd h (hfj i (j e'))
  · exact absurd h.symm (hfj i' (j e))
  · simp only [emb, Sum.inr.injEq] at h
    rw [hj h]

variable [DecidableEq X] (S : KLoc (Fin 3) (Fin 2 ⊕ X) → List Sym) (a hA hB : List Sym)

@[simp] theorem st_arr : st S a hA hB (.inl 0) = a := by simp [st]
@[simp] theorem st_hdr : st S a hA hB (.inl 1) = S (.inl 1) := by simp [st]
@[simp] theorem st_pairs : st S a hA hB (.inl 2) = S (.inl 2) := by simp [st]
@[simp] theorem st_hA : st S a hA hB (.inr (.inl 0)) = hA := by simp [st]
@[simp] theorem st_hB : st S a hA hB (.inr (.inl 1)) = hB := by simp [st]
@[simp] theorem st_inr (x : X) : st S a hA hB (.inr (.inr x)) = S (.inr (.inr x)) := by
  simp [st]

theorem st_upd_arr (a' : List Sym) :
    Function.update (st S a hA hB) (.inl 0) a' = st S a' hA hB := by
  funext k
  simp only [st, Function.update_apply]
  split_ifs <;> simp_all

theorem st_upd_hA (hA' : List Sym) :
    Function.update (st S a hA hB) (.inr (.inl 0)) hA' = st S a hA' hB := by
  funext k
  simp only [st, Function.update_apply]
  split_ifs <;> simp_all

theorem st_upd_hB (hB' : List Sym) :
    Function.update (st S a hA hB) (.inr (.inl 1)) hB' = st S a hA hB' := by
  funext k
  simp only [st, Function.update_apply]
  split_ifs <;> simp_all

theorem st_init (h0 : S (.inr (.inl 0)) = []) (h1 : S (.inr (.inl 1)) = []) :
    st S (S (.inl 0)) [] [] = S := by
  funext k
  simp only [st, Function.update_apply]
  split_ifs <;> simp_all

theorem st_final (h0 : S (.inr (.inl 0)) = []) (h1 : S (.inr (.inl 1)) = []) :
    st S a [] [] = Function.update S (.inl 0) a := by
  funext k
  simp only [st, Function.update_apply]
  split_ifs <;> simp_all

/-- Every part sees clean private scratch. -/
theorem kclean_emb (hS : KClean S) {N Y : Type} (f : N → KLoc (Fin 3) (Fin 2 ⊕ X)) (j : Y → X) :
    KClean (st S a hA hB ∘ emb f j) := fun e => by
  simp only [Function.comp_apply, emb, st_inr]
  exact hS (.inr (j e))

/-- **An array step**: a part that only replaces its array stack (placed at `.inl 0`). -/
theorem runs_arrStep {N Y σ R : Type} [DecidableEq N] [DecidableEq Y]
    {f : N → KLoc (Fin 3) (Fin 2 ⊕ X)} {j : Y → X} (hinj : Function.Injective (emb f j))
    {n0 : N} (h0 : f n0 = .inl 0) (l : Lens σ R) {P : Prog (KLoc N Y) (fun _ => Sym) R}
    {a' : List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (st S a hA hB ∘ emb f j)
      (Function.update (st S a hA hB ∘ emb f j) (.inl n0) a') Q T) :
    Runs (callInj (emb f j) l P) (st S a hA hB) (st S a' hA hB) (fun _ => True) T := by
  have h := runs_callInj_update hinj l hP
  rwa [show emb f j (.inl n0) = .inl 0 from h0, st_upd_arr] at h

/-- **The header step**: a part writing its named stacks `1, 2` placed at `hA`, `hB`. -/
theorem runs_hdrStep {Y σ R : Type} [DecidableEq Y]
    {f : Fin 3 → KLoc (Fin 3) (Fin 2 ⊕ X)} {j : Y → X} (hinj : Function.Injective (emb f j))
    (h1 : f 1 = .inr (.inl 0)) (h2 : f 2 = .inr (.inl 1)) (l : Lens σ R)
    {P : Prog (KLoc (Fin 3) Y) (fun _ => Sym) R} {vA vB : List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (st S a hA hB ∘ emb f j)
      (Function.update (Function.update (st S a hA hB ∘ emb f j) (.inl 1) vA) (.inl 2) vB) Q T) :
    Runs (callInj (emb f j) l P) (st S a hA hB) (st S a vA vB) (fun _ => True) T := by
  refine runs_callInj (Q := Q) hinj l ?_ ?_
  · have e : st S a vA vB =
        Function.update (Function.update (st S a hA hB) (emb f j (.inl 1)) vA)
          (emb f j (.inl 2)) vB := by
      rw [show emb f j (.inl 1) = .inr (.inl 0) from h1,
        show emb f j (.inl 2) = .inr (.inl 1) from h2, st_upd_hA, st_upd_hB]
    rw [e, Function.update_comp_eq_of_injective _ hinj, Function.update_comp_eq_of_injective _ hinj]
    exact hP
  · intro k hk
    have hk1 : k ≠ .inr (.inl 0) := fun h => hk (.inl 1) (by rw [h]; exact h1)
    have hk2 : k ≠ .inr (.inl 1) := fun h => hk (.inl 2) (by rw [h]; exact h2)
    simp only [st, Function.update_apply, hk1, hk2, if_false]

/-- **A drain step** on a private header stack. -/
theorem runs_drainStep {σ : Type} (l : Lens σ Bool) (k : KLoc (Fin 3) (Fin 2 ⊕ X))
    (B : KLoc (Fin 3) (Fin 2 ⊕ X) → List Sym) :
    Runs (callInj id l (drainProg k)) B (Function.update B k []) (fun _ => True)
      (2 * (B k).length + 3) := by
  have h := runs_drainProg k B
  exact runs_callInj_update Function.injective_id l (by simpa using h)

end Layout

/-! ## The parts' specifications (bodies of the contracts) -/

section Specs

/-- Body of `CubeLayerStmt` (for the part's `J`). -/
def LaySpec (Band : LayerRT → Prop) (lam' : ℝ) (J : ℕ) (E : Type) [DecidableEq E] (R : Type)
    (C : ℕ) (Pr : Prog (KLoc (Fin 2) E) (fun _ => Sym) R) : Prop :=
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
        (C * (layerCost lam' (layerRT P d r w K j₀ D nS ρ) + (w + m + 1) ^ J +
          (sliceHdr P d r w K m j₀ D nS ρ).length))

/-- Body of `LiftMachineStmt`. -/
def LiftSpec (E : Type) [DecidableEq E] (R : Type) (C : ℕ)
    (Pr : Prog (KLoc (Fin 2) E) (fun _ => Sym) R) : Prop :=
  ∀ (w δ : ℕ) (v : List (List CInt)) (rest hrest : List Sym) (S : KLoc (Fin 2) E → List Sym),
      KClean S → 1 ≤ w → CArrFits w v → BlkTerm rest →
      S (.inl 0) = carrSyms w v ++ rest → S (.inl 1) = hdrSyms [w, δ] ++ hrest →
      Runs Pr S (Function.update S (.inl 0) (carrSyms (w + δ) (mapC (liftC δ) v) ++ rest))
        (fun _ => True) (C * (cvol (w + δ) v + w + δ + 1))

/-- Body of `LowerMachineStmt`. -/
def LowSpec (E : Type) [DecidableEq E] (R : Type) (C : ℕ)
    (Pr : Prog (KLoc (Fin 2) E) (fun _ => Sym) R) : Prop :=
  ∀ (w δ : ℕ) (v : List (List CInt)) (rest hrest : List Sym) (S : KLoc (Fin 2) E → List Sym),
      KClean S → 1 ≤ w → CArrFits w v → BlkTerm rest →
      S (.inl 0) = carrSyms (w + δ) (mapC (liftC δ) v) ++ rest →
      S (.inl 1) = hdrSyms [w, δ] ++ hrest →
      Runs Pr S (Function.update S (.inl 0) (carrSyms w v ++ rest))
        (fun _ => True) (C * (cvol (w + δ) v + w + δ + 1))

/-- Body of `CnotHdrStmt`. -/
def HdrSpec (E : Type) [DecidableEq E] (R : Type) (C : ℕ)
    (Pr : Prog (KLoc (Fin 3) E) (fun _ => Sym) R) : Prop :=
  ∀ (P d r w K m j₀ D nS ρ : ℕ) (hrest : List Sym) (S : KLoc (Fin 3) E → List Sym),
      KClean S → S (.inl 0) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest →
      Runs Pr S
        (Function.update (Function.update S (.inl 1) (hdrSyms [w, 8 * d] ++ S (.inl 1)))
          (.inl 2) (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ ++ S (.inl 2)))
        (fun _ => True) (C * ((sliceHdr P d r w K m j₀ D nS ρ).length + 1))

/-- Body of `CnotScanStmt mode` (for the part's `J`). -/
def ScanSpec (mode : CnotScanMode) (J : ℕ) (E : Type) [DecidableEq E] (R : Type) (C : ℕ)
    (Pr : Prog (KLoc (Fin 3) E) (fun _ => Sym) R) : Prop :=
  ∀ (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m)) (y : RArr (Cube m) r)
      (rest hrest prest : List Sym) (S : KLoc (Fin 3) E → List Sym),
      KClean S → j₀ + D * K + nS = m → ρ < K → P + 2 ≤ w → d ≤ w + m → K ≤ w + m →
      CnotPairsValid pairs → ArrOnDiskGrid (P + 8 * d) y →
      ArrOnDiskGrid (P + 8 * d) (cnotScanMap K j₀ D ρ pairs mode y) → BlkTerm rest →
      S (.inl 0) = carrSyms (w + 8 * d) (encCube (P + 8 * d) y) ++ rest →
      S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest →
      S (.inl 2) = pairsSyms pairs ++ prest →
      Runs Pr S
        (Function.update S (.inl 0)
          (carrSyms (w + 8 * d) (encCube (P + 8 * d) (cnotScanMap K j₀ D ρ pairs mode y)) ++ rest))
        (fun _ => True)
        (C * (cvolCube m r (w + 8 * d) + 2 ^ m * ((w + m + 1) ^ J + (pairsSyms pairs).length) +
          (sliceHdr P d r w K m j₀ D nS ρ).length))

end Specs

/-! ## Named-stack placements -/

section Place

variable {X : Type}

/-- Header part: slice header (composite stack `1`), `hA`, `hB`. -/
def fH : Fin 3 → KLoc (Fin 3) (Fin 2 ⊕ X) := ![.inl 1, .inr (.inl 0), .inr (.inl 1)]
/-- Lift and lowering: array, `hA`. -/
def fA : Fin 2 → KLoc (Fin 3) (Fin 2 ⊕ X) := ![.inl 0, .inr (.inl 0)]
/-- Layer call: array, `hB`. -/
def fB : Fin 2 → KLoc (Fin 3) (Fin 2 ⊕ X) := ![.inl 0, .inr (.inl 1)]
/-- Scans: array, slice header, pairs. -/
def fS : Fin 3 → KLoc (Fin 3) (Fin 2 ⊕ X) := ![.inl 0, .inl 1, .inl 2]

theorem fH_inj : Function.Injective (fH (X := X)) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fH]
theorem fA_inj : Function.Injective (fA (X := X)) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fA]
theorem fB_inj : Function.Injective (fB (X := X)) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fB]
theorem fS_inj : Function.Injective (fS (X := X)) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fS]

theorem fH_ne (i : Fin 3) (x : X) : fH i ≠ .inr (.inr x) := by fin_cases i <;> simp [fH]
theorem fA_ne (i : Fin 2) (x : X) : fA i ≠ .inr (.inr x) := by fin_cases i <;> simp [fA]
theorem fB_ne (i : Fin 2) (x : X) : fB i ≠ .inr (.inr x) := by fin_cases i <;> simp [fB]
theorem fS_ne (i : Fin 3) (x : X) : fS i ≠ .inr (.inr x) := by fin_cases i <;> simp [fS]

end Place

section PlaceSimp

variable {X : Type}

@[simp] theorem fS_0 : fS (X := X) 0 = .inl 0 := rfl
@[simp] theorem fS_1 : fS (X := X) 1 = .inl 1 := rfl
@[simp] theorem fS_2 : fS (X := X) 2 = .inl 2 := rfl
@[simp] theorem fH_0 : fH (X := X) 0 = .inl 1 := rfl
@[simp] theorem fH_1 : fH (X := X) 1 = .inr (.inl 0) := rfl
@[simp] theorem fH_2 : fH (X := X) 2 = .inr (.inl 1) := rfl
@[simp] theorem fA_0 : fA (X := X) 0 = .inl 0 := rfl
@[simp] theorem fA_1 : fA (X := X) 1 = .inr (.inl 0) := rfl
@[simp] theorem fB_0 : fB (X := X) 0 = .inl 0 := rfl
@[simp] theorem fB_1 : fB (X := X) 1 = .inr (.inl 1) := rfl
@[simp] theorem emb_inl {N Y : Type} (f : N → KLoc (Fin 3) (Fin 2 ⊕ X)) (j : Y → X) (i : N) :
    emb f j (.inl i) = f i := rfl

end PlaceSimp

/-! ## One call of each part -/

section Steps

variable {X : Type} [DecidableEq X] {S : KLoc (Fin 3) (Fin 2 ⊕ X) → List Sym}

/-- A scan call (`CnotScanStmt mode`) on the lifted array. -/
theorem runs_scan {Ei Ri σ : Type} [DecidableEq Ei] {mode : CnotScanMode} {J C : ℕ}
    {Pi : Prog (KLoc (Fin 3) Ei) (fun _ => Sym) Ri} (hspec : ScanSpec mode J Ei Ri C Pi)
    {ji : Ei → X} (hji : Function.Injective ji) (li : Lens σ Ri) (hS : KClean S)
    {P d r w K m j₀ D nS ρ : ℕ} {pairs : List (Fin m × Fin m)} {rest hrest prest : List Sym}
    (hm : j₀ + D * K + nS = m) (hρ : ρ < K) (hw : P + 2 ≤ w) (hdw : d ≤ w + m)
    (hKw : K ≤ w + m) (hv : CnotPairsValid pairs) (hbt : BlkTerm rest)
    (hs1 : S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest)
    (hs2 : S (.inl 2) = pairsSyms pairs ++ prest) (hA hB : List Sym) {y : RArr (Cube m) r}
    (hy : ArrOnDiskGrid (P + 8 * d) y)
    (hy' : ArrOnDiskGrid (P + 8 * d) (cnotScanMap K j₀ D ρ pairs mode y)) :
    Runs (callInj (emb fS ji) li Pi)
      (st S (carrSyms (w + 8 * d) (encCube (P + 8 * d) y) ++ rest) hA hB)
      (st S (carrSyms (w + 8 * d) (encCube (P + 8 * d) (cnotScanMap K j₀ D ρ pairs mode y)) ++
        rest) hA hB)
      (fun _ => True)
      (C * (cvolCube m r (w + 8 * d) + 2 ^ m * ((w + m + 1) ^ J + (pairsSyms pairs).length) +
          (sliceHdr P d r w K m j₀ D nS ρ).length)) :=
  runs_arrStep S _ hA hB (emb_injective fS_inj hji fS_ne) (n0 := 0) rfl li
    (hspec P d r w K m j₀ D nS ρ pairs y rest hrest prest _ (kclean_emb S _ hA hB hS fS ji)
      hm hρ hw hdw hKw hv hy hy' hbt (by simp) (by simp [hs1]) (by simp [hs2]))

/-- A layer call (`CubeLayerStmt`) at the lifted precision, header in `hB`. -/
theorem runs_layer {EL RL σ : Type} [DecidableEq EL] {Band : LayerRT → Prop} {lam' : ℝ}
    {J C : ℕ} {PL : Prog (KLoc (Fin 2) EL) (fun _ => Sym) RL}
    (hspec : LaySpec Band lam' J EL RL C PL) {jL : EL → X} (hj : Function.Injective jL)
    (lL : Lens σ RL) (hS : KClean S) {P d r w K m j₀ D nS ρ : ℕ} {rest : List Sym}
    (hm : j₀ + D * K + nS = m) (hρ : ρ < K) (hw : P + 2 ≤ w) (hdw : d ≤ w + m)
    (hKw : K ≤ w + m) (hband : Band (sliceRT P d r w K j₀ D nS ρ)) (hbt : BlkTerm rest)
    (hA : List Sym) {y : RArr (Cube m) r} (hy : ArrOnDiskGrid (P + 8 * d) y) :
    Runs (callInj (emb fB jL) lL PL)
      (st S (carrSyms (w + 8 * d) (encCube (P + 8 * d) y) ++ rest) hA
        (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ))
      (st S (carrSyms (w + 8 * d)
          (encCube (P + 8 * d) (truncArr (P + 8 * d) (hT (slicePos m K j₀ D ρ) y))) ++ rest) hA
        (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ))
      (fun _ => True)
      (C * (layerCost lam' (sliceRT P d r w K j₀ D nS ρ) + (w + 8 * d + m + 1) ^ J +
          (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ).length)) :=
  runs_arrStep S _ hA _ (emb_injective fB_inj hj fB_ne) (n0 := 0) rfl lL
    (hspec (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ y rest [] _
      (kclean_emb S _ hA _ hS fB jL) hm hρ (by omega) (by omega) (by omega) hband hy hbt
      (by simp) (by simp))

/-- The lift (`LiftMachineStmt`) by `8d`, header in `hA`. -/
theorem runs_lift {ELi RLi σ : Type} [DecidableEq ELi] {C : ℕ}
    {PLi : Prog (KLoc (Fin 2) ELi) (fun _ => Sym) RLi} (hspec : LiftSpec ELi RLi C PLi)
    {jLi : ELi → X} (hj : Function.Injective jLi) (l : Lens σ RLi) (hS : KClean S)
    {P d w m r : ℕ} {z : RArr (Cube m) r} {rest : List Sym} (hw : P + 2 ≤ w)
    (hz : ArrOnDiskGrid P z) (hbt : BlkTerm rest) (hB : List Sym) :
    Runs (callInj (emb fA jLi) l PLi)
      (st S (carrSyms w (encCube P z) ++ rest) (hdrSyms [w, 8 * d]) hB)
      (st S (carrSyms (w + 8 * d) (encCube (P + 8 * d) z) ++ rest) (hdrSyms [w, 8 * d]) hB)
      (fun _ => True) (C * (cvolCube m r (w + 8 * d) + w + 8 * d + 1)) := by
  have h := runs_arrStep S (carrSyms w (encCube P z) ++ rest) (hdrSyms [w, 8 * d]) hB
    (emb_injective fA_inj hj fA_ne) (n0 := 0) rfl l
    (hspec w (8 * d) (encCube P z) rest [] _ (kclean_emb S _ _ hB hS fA jLi) (by omega)
      (cArrFits_encCube hz hw) hbt (by simp) (by simp))
  rw [← encCube_lift (8 * d) (fun x k => (hz x k).1), cvol_encCube] at h
  exact h

/-- The exact lowering (`LowerMachineStmt`) by `8d`, header in `hA`. -/
theorem runs_lower {ELo RLo σ : Type} [DecidableEq ELo] {C : ℕ}
    {PLo : Prog (KLoc (Fin 2) ELo) (fun _ => Sym) RLo} (hspec : LowSpec ELo RLo C PLo)
    {jLo : ELo → X} (hj : Function.Injective jLo) (l : Lens σ RLo) (hS : KClean S)
    {P d w m r : ℕ} {v : RArr (Cube m) r} {rest : List Sym} (hw : P + 2 ≤ w)
    (hv : ArrOnDiskGrid P v) (hbt : BlkTerm rest) (hB : List Sym) :
    Runs (callInj (emb fA jLo) l PLo)
      (st S (carrSyms (w + 8 * d) (encCube (P + 8 * d) v) ++ rest) (hdrSyms [w, 8 * d]) hB)
      (st S (carrSyms w (encCube P v) ++ rest) (hdrSyms [w, 8 * d]) hB)
      (fun _ => True) (C * (cvolCube m r (w + 8 * d) + w + 8 * d + 1)) := by
  have h := runs_arrStep S (carrSyms (w + 8 * d) (encCube (P + 8 * d) v) ++ rest)
    (hdrSyms [w, 8 * d]) hB (emb_injective fA_inj hj fA_ne) (n0 := 0) rfl l
    (hspec w (8 * d) (encCube P v) rest [] _ (kclean_emb S _ _ hB hS fA jLo) (by omega)
      (cArrFits_encCube hv hw) hbt
      (by simp [encCube_lift (8 * d) (fun x k => (hv x k).1)]) (by simp))
  rw [cvol_encCube] at h
  exact h

/-- The header builder (`CnotHdrStmt`): `hA`, `hB` receive the two derived headers. -/
theorem runs_hdr {EH RH σ : Type} [DecidableEq EH] {C : ℕ}
    {PH : Prog (KLoc (Fin 3) EH) (fun _ => Sym) RH} (hspec : HdrSpec EH RH C PH)
    {jH : EH → X} (hj : Function.Injective jH) (l : Lens σ RH) (hS : KClean S)
    {P d r w K m j₀ D nS ρ : ℕ} {hrest : List Sym}
    (hs1 : S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest) (a : List Sym) :
    Runs (callInj (emb fH jH) l PH) (st S a [] [])
      (st S a (hdrSyms [w, 8 * d]) (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ))
      (fun _ => True) (C * ((sliceHdr P d r w K m j₀ D nS ρ).length + 1)) := by
  refine runs_hdrStep S a [] [] (emb_injective fH_inj hj fH_ne) rfl rfl l (Q := fun _ => True) ?_
  have h := hspec P d r w K m j₀ D nS ρ hrest _ (kclean_emb S a [] [] hS fH jH) (by simp [hs1])
  simpa using h

end Steps

/-! ## The gadget (Lemma 5.1 executed, eq. (`eq:walsh-three-layer`)) -/

/-- The gadget's program shape: `S_U; layer; S_U; layer; S_U; layer; scalar`. -/
def gad {K : Type} {Γ : K → Type} {σ : Type} (cS cL cC : Prog K Γ σ) : Prog K Γ σ :=
  .seq cS (.seq cL (.seq cS (.seq cL (.seq cS (.seq cL cC)))))

theorem closed_gad {K : Type} {Γ : K → Type} {σ : Type} {cS cL cC : Prog K Γ σ}
    (h1 : cS.Closed) (h2 : cL.Closed) (h3 : cC.Closed) : (gad cS cL cC).Closed :=
  ⟨h1, h2, h1, h2, h1, h2, h3⟩

section Gadget

variable {X : Type} [DecidableEq X] {S : KLoc (Fin 3) (Fin 2 ⊕ X) → List Sym}

/-- **The gadget is exact on the machine** (Lemmas 5.1–5.2, `lem:walsh-select`, `lem:walsh-exact`): on a disk array on the
`Q`-grid with `Q + 3D ≤ P + 8d`, the seven calls return `H_T y` (`T = targets pairs`,
the three layer truncations discard only zeros, the scalar undoes the unwanted positions). -/
theorem runs_gad {EL RL E1 R1 E3 R3 σ : Type} [DecidableEq EL] [DecidableEq E1] [DecidableEq E3]
    {Band : LayerRT → Prop} {lam' : ℝ} {JL CL J1 C1 J3 C3 : ℕ}
    {PL : Prog (KLoc (Fin 2) EL) (fun _ => Sym) RL}
    {P1 : Prog (KLoc (Fin 3) E1) (fun _ => Sym) R1} {P3 : Prog (KLoc (Fin 3) E3) (fun _ => Sym) R3}
    (hL : LaySpec Band lam' JL EL RL CL PL) (h1 : ScanSpec .selPhase J1 E1 R1 C1 P1)
    (h3 : ScanSpec .selScalar J3 E3 R3 C3 P3)
    {jL : EL → X} {j1 : E1 → X} {j3 : E3 → X} (hjL : Function.Injective jL)
    (hj1 : Function.Injective j1) (hj3 : Function.Injective j3)
    (lL : Lens σ RL) (l1 : Lens σ R1) (l3 : Lens σ R3) (hS : KClean S)
    {P d r w K m j₀ D nS ρ : ℕ} {pairs : List (Fin m × Fin m)} {rest hrest prest : List Sym}
    (hm : j₀ + D * K + nS = m) (hρ : ρ < K) (hw : P + 2 ≤ w) (hdw : d ≤ w + m)
    (hKw : K ≤ w + m) (hv : CnotPairsValid pairs) (htgt : targets pairs ⊆ slicePos m K j₀ D ρ)
    (hband : Band (sliceRT P d r w K j₀ D nS ρ)) (hbt : BlkTerm rest)
    (hs1 : S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest)
    (hs2 : S (.inl 2) = pairsSyms pairs ++ prest) (hA : List Sym)
    {Q : ℕ} (hQ : Q + 3 * D ≤ P + 8 * d) {y : RArr (Cube m) r}
    (hy : ArrOnDiskGrid Q y) :
    Runs (gad (callInj (emb fS j1) l1 P1) (callInj (emb fB jL) lL PL) (callInj (emb fS j3) l3 P3))
      (st S (carrSyms (w + 8 * d) (encCube (P + 8 * d) y) ++ rest) hA
        (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ))
      (st S (carrSyms (w + 8 * d) (encCube (P + 8 * d) (hT (targets pairs) y)) ++ rest) hA
        (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ))
      (fun _ => True)
      (3 * (C1 * (cvolCube m r (w + 8 * d) + 2 ^ m * ((w + m + 1) ^ J1 + (pairsSyms pairs).length) +
          (sliceHdr P d r w K m j₀ D nS ρ).length)) +
        3 * (CL * (layerCost lam' (sliceRT P d r w K j₀ D nS ρ) + (w + 8 * d + m + 1) ^ JL +
          (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ).length)) +
        C3 * (cvolCube m r (w + 8 * d) + 2 ^ m * ((w + m + 1) ^ J3 + (pairsSyms pairs).length) +
          (sliceHdr P d r w K m j₀ D nS ρ).length)) := by
  have hcard : (slicePos m K j₀ D ρ).card = D := card_slicePos ⟨ρ, hρ⟩ (by omega)
  have hTcard : (targets pairs).card ≤ D := hcard ▸ Finset.card_le_card htgt
  have mono : ∀ {q : ℕ} {u : RArr (Cube m) r}, q ≤ P + 8 * d → ArrOnDiskGrid q u →
      ArrOnDiskGrid (P + 8 * d) u := fun hq hu => arrOnDiskGrid_mono hq hu
  -- values (exact rounds)
  have v1 := arrOnDiskGrid_sDiag (slicePos m K j₀ D ρ \ targets pairs) hy
  obtain ⟨e2, v2⟩ := layer_round hρ hm (P' := P + 8 * d) (by omega) v1
  have v3 := arrOnDiskGrid_sDiag (slicePos m K j₀ D ρ \ targets pairs) v2
  obtain ⟨e4, v4⟩ := layer_round hρ hm (P' := P + 8 * d) (by omega) v3
  have v5 := arrOnDiskGrid_sDiag (slicePos m K j₀ D ρ \ targets pairs) v4
  obtain ⟨e6, v6⟩ := layer_round hρ hm (P' := P + 8 * d) (by omega) v5
  have v7 : ArrOnDiskGrid (Q + (targets pairs).card) (hT (targets pairs) y) :=
    arrOnDiskGrid_hT _ hy
  have e7 := hT_eq_selScalar_three_layer (slicePos m K j₀ D ρ) (targets pairs) htgt y
  -- the seven calls
  have s1 := runs_scan h1 hj1 l1 hS hm hρ hw hdw hKw hv hbt hs1 hs2 hA
    (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ) (mono (by omega) hy) (mono (by omega) v1)
  have s2 := runs_layer hL hjL lL hS hm hρ hw hdw hKw hband hbt hA (mono (by omega) v1)
  rw [e2] at s2
  have s3 := runs_scan h1 hj1 l1 hS hm hρ hw hdw hKw hv hbt hs1 hs2 hA
    (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ) (mono (by omega) v2) (mono (by omega) v3)
  have s4 := runs_layer hL hjL lL hS hm hρ hw hdw hKw hband hbt hA (mono (by omega) v3)
  rw [e4] at s4
  have s5 := runs_scan h1 hj1 l1 hS hm hρ hw hdw hKw hv hbt hs1 hs2 hA
    (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ) (mono (by omega) v4) (mono (by omega) v5)
  have s6 := runs_layer hL hjL lL hS hm hρ hw hdw hKw hband hbt hA (mono (by omega) v5)
  rw [e6] at s6
  have v7' : ArrOnDiskGrid (P + 8 * d) (cnotScanMap K j₀ D ρ pairs .selScalar
      (hT (slicePos m K j₀ D ρ) (sDiag (slicePos m K j₀ D ρ \ targets pairs)
        (hT (slicePos m K j₀ D ρ) (sDiag (slicePos m K j₀ D ρ \ targets pairs)
          (hT (slicePos m K j₀ D ρ) (sDiag (slicePos m K j₀ D ρ \ targets pairs) y))))))) := by
    simp only [cnotScanMap]
    rw [← e7]
    exact mono (by omega) v7
  have s7 := runs_scan h3 hj3 l3 hS hm hρ hw hdw hKw hv hbt hs1 hs2 hA
    (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ) (mono (by omega) v6) v7'
  simp only [cnotScanMap] at s1 s3 s5 s7
  rw [← e7] at s7
  exact runs_mono (runs_seq s1 (runs_seq s2 (runs_seq s3 (runs_seq s4 (runs_seq s5
    (runs_seq s6 s7)))))) (fun _ _ => trivial) (le_of_eq (by ring))

end Gadget

/-! ## Sizes -/

theorem bitLen_le_self' (n : ℕ) : bitLen n ≤ n :=
  WP.W9comp.bitLen_le_of_lt_two_pow Nat.lt_two_pow_self

theorem length_hdrSyms_le (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) :
    (hdrSyms l).length ≤ l.length * (B + 1) := by
  induction l with
  | nil => simp [hdrSyms]
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hb := bitLen_le_self' a
    simp only [hdrSyms, List.flatMap_cons, List.length_append, length_natSyms,
      List.length_cons, List.length_nil] at hl ⊢
    rw [Nat.succ_mul]
    omega

/-- The pair list of a valid batch is short: `|pairsSyms pairs| ≤ (m + 1)²`. -/
theorem length_pairsSyms_le {m : ℕ} {pairs : List (Fin m × Fin m)} (hv : CnotPairsValid pairs) :
    (pairsSyms pairs).length ≤ (m + 1) ^ 2 := by
  have h2 : 2 * pairs.length ≤ m := by
    have := hv.length_le_card
    simpa [two_mul] using this
  have hb := length_hdrSyms_le (pairs.length :: pairs.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]) m
    (by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · obtain ⟨p, -, hp⟩ := List.mem_flatMap.1 hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact p.1.isLt.le
        · exact p.2.isLt.le)
  have hfl : ∀ ps : List (Fin m × Fin m),
      (ps.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]).length = 2 * ps.length := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
      omega
  have hlen : (pairs.length :: pairs.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]).length =
      2 * pairs.length + 1 := by
    simp only [List.length_cons, hfl]
  rw [hlen] at hb
  calc (pairsSyms pairs).length ≤ (2 * pairs.length + 1) * (m + 1) := hb
    _ ≤ (m + 1) * (m + 1) := Nat.mul_le_mul_right _ (by omega)
    _ = (m + 1) ^ 2 := by ring

/-! ## The composite program -/

section Composite

/-- The parts' private block. -/
abbrev PX (EH ELi ELo EL E1 E2 E3 E4 : Type) : Type :=
  ((EH ⊕ ELi) ⊕ (ELo ⊕ EL)) ⊕ ((E1 ⊕ E2) ⊕ (E3 ⊕ E4))

/-- Registers of the composite (`Bool` for the drains). -/
abbrev PR (RH RLi RLo RL R1 R2 R3 R4 : Type) : Type :=
  ((RH × RLi) × (RLo × RL)) × ((R1 × R2) × ((R3 × R4) × Bool))

/-- The composite's stacks. -/
abbrev CbLoc (EH ELi ELo EL E1 E2 E3 E4 : Type) : Type :=
  KLoc (Fin 3) (Fin 2 ⊕ PX EH ELi ELo EL E1 E2 E3 E4)

variable {EH ELi ELo EL E1 E2 E3 E4 RH RLi RLo RL R1 R2 R3 R4 : Type}

def jH : EH → PX EH ELi ELo EL E1 E2 E3 E4 := fun e => .inl (.inl (.inl e))
def jLi : ELi → PX EH ELi ELo EL E1 E2 E3 E4 := fun e => .inl (.inl (.inr e))
def jLo : ELo → PX EH ELi ELo EL E1 E2 E3 E4 := fun e => .inl (.inr (.inl e))
def jL : EL → PX EH ELi ELo EL E1 E2 E3 E4 := fun e => .inl (.inr (.inr e))
def j1 : E1 → PX EH ELi ELo EL E1 E2 E3 E4 := fun e => .inr (.inl (.inl e))
def j2 : E2 → PX EH ELi ELo EL E1 E2 E3 E4 := fun e => .inr (.inl (.inr e))
def j3 : E3 → PX EH ELi ELo EL E1 E2 E3 E4 := fun e => .inr (.inr (.inl e))
def j4 : E4 → PX EH ELi ELo EL E1 E2 E3 E4 := fun e => .inr (.inr (.inr e))

/-- Lens into the first component. -/
def lfst {α β γ : Type} (l : Lens α γ) : Lens (α × β) γ := (Lens.fst α β).comp l

def lH : Lens (PR RH RLi RLo RL R1 R2 R3 R4) RH := lfst (lfst (Lens.fst _ _))
def lLi : Lens (PR RH RLi RLo RL R1 R2 R3 R4) RLi := lfst (lfst (Lens.snd _ _))
def lLo : Lens (PR RH RLi RLo RL R1 R2 R3 R4) RLo := lfst (lsnd (Lens.fst _ _))
def lL : Lens (PR RH RLi RLo RL R1 R2 R3 R4) RL := lfst (lsnd (Lens.snd _ _))
def l1 : Lens (PR RH RLi RLo RL R1 R2 R3 R4) R1 := lsnd (lfst (Lens.fst _ _))
def l2 : Lens (PR RH RLi RLo RL R1 R2 R3 R4) R2 := lsnd (lfst (Lens.snd _ _))
def l3 : Lens (PR RH RLi RLo RL R1 R2 R3 R4) R3 := lsnd (lsnd (lfst (Lens.fst _ _)))
def l4 : Lens (PR RH RLi RLo RL R1 R2 R3 R4) R4 := lsnd (lsnd (lfst (Lens.snd _ _)))
def lD : Lens (PR RH RLi RLo RL R1 R2 R3 R4) Bool := lsnd (lsnd (Lens.snd _ _))

variable (PH : Prog (KLoc (Fin 3) EH) (fun _ => Sym) RH)
  (PLi : Prog (KLoc (Fin 2) ELi) (fun _ => Sym) RLi)
  (PLo : Prog (KLoc (Fin 2) ELo) (fun _ => Sym) RLo)
  (PL : Prog (KLoc (Fin 2) EL) (fun _ => Sym) RL) (P1 : Prog (KLoc (Fin 3) E1) (fun _ => Sym) R1)
  (P2 : Prog (KLoc (Fin 3) E2) (fun _ => Sym) R2) (P3 : Prog (KLoc (Fin 3) E3) (fun _ => Sym) R3)
  (P4 : Prog (KLoc (Fin 3) E4) (fun _ => Sym) R4)

/-- The gadget of the composite (`S_U` = part `1`, layer, scalar = part `3`). -/
def cbGad : Prog (CbLoc EH ELi ELo EL E1 E2 E3 E4) (fun _ => Sym) (PR RH RLi RLo RL R1 R2 R3 R4) :=
  gad (callInj (emb fS j1) l1 P1) (callInj (emb fB jL) lL PL) (callInj (emb fS j3) l3 P3)

/-- **The composite** (Proposition 5.5, `prop:cnot-batch`): header; lift; gadget; `CZ`; gadget; `×2^s`; lowering; drains. -/
def cbProg : Prog (CbLoc EH ELi ELo EL E1 E2 E3 E4) (fun _ => Sym) (PR RH RLi RLo RL R1 R2 R3 R4) :=
  .seq (callInj (emb fH jH) lH PH)
  (.seq (callInj (emb fA jLi) lLi PLi)
  (.seq (cbGad PL P1 P3)
  (.seq (callInj (emb fS j2) l2 P2)
  (.seq (cbGad PL P1 P3)
  (.seq (callInj (emb fS j4) l4 P4)
  (.seq (callInj (emb fA jLo) lLo PLo)
  (.seq (callInj id lD (drainProg (.inr (.inl 0))))
    (callInj id lD (drainProg (.inr (.inl 1)))))))))))

theorem closed_cbProg (hH : PH.Closed) (hLi : PLi.Closed) (hLo : PLo.Closed) (hL : PL.Closed)
    (h1 : P1.Closed) (h2 : P2.Closed) (h3 : P3.Closed) (h4 : P4.Closed) :
    (cbProg PH PLi PLo PL P1 P2 P3 P4).Closed := by
  have hg : (cbGad (EH := EH) (ELi := ELi) (ELo := ELo) (E2 := E2) (E4 := E4) (RH := RH)
      (RLi := RLi) (RLo := RLo) (R2 := R2) (R4 := R4) PL P1 P3).Closed :=
    closed_gad (closed_callInj _ _ h1) (closed_callInj _ _ hL) (closed_callInj _ _ h3)
  exact ⟨closed_callInj _ _ hH, closed_callInj _ _ hLi, hg, closed_callInj _ _ h2, hg,
    closed_callInj _ _ h4, closed_callInj _ _ hLo, closed_callInj _ _ (closed_drainProg _),
    closed_callInj _ _ (closed_drainProg _)⟩

end Composite

/-! ## Correctness and cost of the composite -/

/-- Cost of one gadget: three scans `S_U`, three layer calls, one scalar scan. -/
noncomputable def gadCost (lam' : ℝ) (JL J1 J3 CL C1 C3 P d r w K m j₀ D nS ρ np : ℕ) : ℕ :=
  3 * (C1 * (cvolCube m r (w + 8 * d) + 2 ^ m * ((w + m + 1) ^ J1 + np) +
      (sliceHdr P d r w K m j₀ D nS ρ).length)) +
    3 * (CL * (layerCost lam' (sliceRT P d r w K j₀ D nS ρ) + (w + 8 * d + m + 1) ^ JL +
      (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ).length)) +
    C3 * (cvolCube m r (w + 8 * d) + 2 ^ m * ((w + m + 1) ^ J3 + np) +
      (sliceHdr P d r w K m j₀ D nS ρ).length)

/-- Cost of the composite: the sum of its parts' bounds (two drains included). -/
noncomputable def cbCost (lam' : ℝ)
    (JL J1 J2 J3 J4 CH CLi CLo CL C1 C2 C3 C4 P d r w K m j₀ D nS ρ np : ℕ) : ℕ :=
  CH * ((sliceHdr P d r w K m j₀ D nS ρ).length + 1) +
  (CLi * (cvolCube m r (w + 8 * d) + w + 8 * d + 1) +
  (gadCost lam' JL J1 J3 CL C1 C3 P d r w K m j₀ D nS ρ np +
  (C2 * (cvolCube m r (w + 8 * d) + 2 ^ m * ((w + m + 1) ^ J2 + np) +
      (sliceHdr P d r w K m j₀ D nS ρ).length) +
  (gadCost lam' JL J1 J3 CL C1 C3 P d r w K m j₀ D nS ρ np +
  (C4 * (cvolCube m r (w + 8 * d) + 2 ^ m * ((w + m + 1) ^ J4 + np) +
      (sliceHdr P d r w K m j₀ D nS ρ).length) +
  (CLo * (cvolCube m r (w + 8 * d) + w + 8 * d + 1) +
  ((2 * (hdrSyms [w, 8 * d]).length + 3) +
    (2 * (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ).length + 3))))))))

section Correct

variable {EH ELi ELo EL E1 E2 E3 E4 RH RLi RLo RL R1 R2 R3 R4 : Type}
  [DecidableEq EH] [DecidableEq ELi] [DecidableEq ELo] [DecidableEq EL] [DecidableEq E1]
  [DecidableEq E2] [DecidableEq E3] [DecidableEq E4] [iX : DecidableEq (PX EH ELi ELo EL E1 E2 E3 E4)]

/-- **The composite performs the batch** (Proposition 5.5, `prop:cnot-batch`): from the contract's
input stacks it reaches exactly the contract's output stacks, within `cbCost`. -/
theorem cbProg_runs {Band : LayerRT → Prop} {lam' : ℝ}
    {JL J1 J2 J3 J4 CH CLi CLo CL C1 C2 C3 C4 : ℕ}
    {PH : Prog (KLoc (Fin 3) EH) (fun _ => Sym) RH}
    {PLi : Prog (KLoc (Fin 2) ELi) (fun _ => Sym) RLi}
    {PLo : Prog (KLoc (Fin 2) ELo) (fun _ => Sym) RLo}
    {PL : Prog (KLoc (Fin 2) EL) (fun _ => Sym) RL}
    {P1 : Prog (KLoc (Fin 3) E1) (fun _ => Sym) R1} {P2 : Prog (KLoc (Fin 3) E2) (fun _ => Sym) R2}
    {P3 : Prog (KLoc (Fin 3) E3) (fun _ => Sym) R3} {P4 : Prog (KLoc (Fin 3) E4) (fun _ => Sym) R4}
    (hH : HdrSpec EH RH CH PH) (hLi : LiftSpec ELi RLi CLi PLi) (hLo : LowSpec ELo RLo CLo PLo)
    (hL : LaySpec Band lam' JL EL RL CL PL) (h1 : ScanSpec .selPhase J1 E1 R1 C1 P1)
    (h2 : ScanSpec .cz J2 E2 R2 C2 P2) (h3 : ScanSpec .selScalar J3 E3 R3 C3 P3)
    (h4 : ScanSpec .shift J4 E4 R4 C4 P4)
    {P d r w K m j₀ D nS ρ : ℕ} {pairs : List (Fin m × Fin m)} {z : RArr (Cube m) r}
    {rest hrest prest : List Sym} {S : CbLoc EH ELi ELo EL E1 E2 E3 E4 → List Sym}
    (hS : KClean S) (hm : j₀ + D * K + nS = m) (hDd : D ≤ d) (hρ : ρ < K)
    (hw : P + 2 ≤ w) (hdw : d ≤ w + m) (hKw : K ≤ w + m) (hv : CnotPairsValid pairs)
    (htgt : targets pairs ⊆ slicePos m K j₀ D ρ) (hband : Band (sliceRT P d r w K j₀ D nS ρ))
    (hz : ArrOnDiskGrid P z) (hbt : BlkTerm rest)
    (hs0 : S (.inl 0) = carrSyms w (encCube P z) ++ rest)
    (hs1 : S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest)
    (hs2 : S (.inl 2) = pairsSyms pairs ++ prest) :
    Runs (cbProg PH PLi PLo PL P1 P2 P3 P4) S
      (Function.update S (.inl 0) (carrSyms w (encCube P (cnotArr pairs z)) ++ rest))
      (fun _ => True)
      (cbCost lam' JL J1 J2 J3 J4 CH CLi CLo CL C1 C2 C3 C4 P d r w K m j₀ D nS ρ
        (pairsSyms pairs).length) := by
  have hA0 : S (.inr (.inl 0)) = [] := hS (.inl 0)
  have hB0 : S (.inr (.inl 1)) = [] := hS (.inl 1)
  have hcard : (slicePos m K j₀ D ρ).card = D := card_slicePos ⟨ρ, hρ⟩ (by omega)
  have hTcard : (targets pairs).card ≤ D := hcard ▸ Finset.card_le_card htgt
  have mono : ∀ {q : ℕ} {u : RArr (Cube m) r}, q ≤ P + 8 * d → ArrOnDiskGrid q u →
      ArrOnDiskGrid (P + 8 * d) u := fun hq hu => arrOnDiskGrid_mono hq hu
  have hjH : Function.Injective (jH : EH → PX EH ELi ELo EL E1 E2 E3 E4) :=
    fun _ _ h => by simpa [jH] using h
  have hjLi : Function.Injective (jLi : ELi → PX EH ELi ELo EL E1 E2 E3 E4) :=
    fun _ _ h => by simpa [jLi] using h
  have hjLo : Function.Injective (jLo : ELo → PX EH ELi ELo EL E1 E2 E3 E4) :=
    fun _ _ h => by simpa [jLo] using h
  have hjL : Function.Injective (jL : EL → PX EH ELi ELo EL E1 E2 E3 E4) :=
    fun _ _ h => by simpa [jL] using h
  have hj1 : Function.Injective (j1 : E1 → PX EH ELi ELo EL E1 E2 E3 E4) :=
    fun _ _ h => by simpa [j1] using h
  have hj2 : Function.Injective (j2 : E2 → PX EH ELi ELo EL E1 E2 E3 E4) :=
    fun _ _ h => by simpa [j2] using h
  have hj3 : Function.Injective (j3 : E3 → PX EH ELi ELo EL E1 E2 E3 E4) :=
    fun _ _ h => by simpa [j3] using h
  have hj4 : Function.Injective (j4 : E4 → PX EH ELi ELo EL E1 E2 E3 E4) :=
    fun _ _ h => by simpa [j4] using h
  -- values (Lemmas 5.2, 5.4)
  have v1 : ArrOnDiskGrid (P + (targets pairs).card) (hT (targets pairs) z) :=
    arrOnDiskGrid_hT _ hz
  have v2 : ArrOnDiskGrid (P + (targets pairs).card)
      (diagArr (czSign pairs) (hT (targets pairs) z)) :=
    arrOnDiskGrid_diagArr _ (czSign_unit pairs) v1
  have v3 : ArrOnDiskGrid (P + (targets pairs).card + (targets pairs).card)
      (hT (targets pairs) (diagArr (czSign pairs) (hT (targets pairs) z))) :=
    arrOnDiskGrid_hT _ v2
  have ecnot := cnotArr_eq_hT_cz_hT pairs hv z
  have vc : ArrOnDiskGrid P (cnotArr pairs z) := fun y k => hz _ k
  -- the calls
  have c0 := runs_hdr hH hjH (lH : Lens (PR RH RLi RLo RL R1 R2 R3 R4) RH) hS hs1 (carrSyms w (encCube P z) ++ rest)
  have c1 := runs_lift (d := d) hLi hjLi (lLi : Lens (PR RH RLi RLo RL R1 R2 R3 R4) RLi) hS hw hz hbt
    (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ)
  have c2 := runs_gad hL h1 h3 hjL hj1 hj3 (lL : Lens (PR RH RLi RLo RL R1 R2 R3 R4) RL) (l1 : Lens (PR RH RLi RLo RL R1 R2 R3 R4) R1)
    (l3 : Lens (PR RH RLi RLo RL R1 R2 R3 R4) R3) hS hm hρ hw hdw hKw hv htgt hband hbt hs1 hs2
    (hdrSyms [w, 8 * d]) (Q := P) (by omega) hz
  have v2' : ArrOnDiskGrid (P + 8 * d)
      (cnotScanMap K j₀ D ρ pairs .cz (hT (targets pairs) z)) := by
    simp only [cnotScanMap]; exact mono (by omega) v2
  have c3 := runs_scan h2 hj2 (l2 : Lens (PR RH RLi RLo RL R1 R2 R3 R4) R2) hS hm hρ hw hdw hKw hv hbt hs1 hs2 (hdrSyms [w, 8 * d])
    (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ) (mono (by omega) v1) v2'
  simp only [cnotScanMap] at c3
  have c4 := runs_gad hL h1 h3 hjL hj1 hj3 (lL : Lens (PR RH RLi RLo RL R1 R2 R3 R4) RL) (l1 : Lens (PR RH RLi RLo RL R1 R2 R3 R4) R1)
    (l3 : Lens (PR RH RLi RLo RL R1 R2 R3 R4) R3) hS hm hρ hw hdw hKw hv htgt hband hbt hs1 hs2
    (hdrSyms [w, 8 * d]) (Q := P + (targets pairs).card) (by omega) v2
  have vc' : ArrOnDiskGrid (P + 8 * d) (cnotScanMap K j₀ D ρ pairs .shift
      (hT (targets pairs) (diagArr (czSign pairs) (hT (targets pairs) z)))) := by
    simp only [cnotScanMap]; rw [← ecnot]; exact mono (by omega) vc
  have c5 := runs_scan h4 hj4 (l4 : Lens (PR RH RLi RLo RL R1 R2 R3 R4) R4) hS hm hρ hw hdw hKw hv hbt hs1 hs2 (hdrSyms [w, 8 * d])
    (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ) (mono (by omega) v3) vc'
  simp only [cnotScanMap] at c5
  rw [← ecnot] at c5
  have c6 := runs_lower (d := d) hLo hjLo (lLo : Lens (PR RH RLi RLo RL R1 R2 R3 R4) RLo) hS hw vc hbt
    (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ)
  have c7 := runs_drainStep (lD : Lens (PR RH RLi RLo RL R1 R2 R3 R4) Bool) (.inr (.inl 0))
    (st S (carrSyms w (encCube P (cnotArr pairs z)) ++ rest) (hdrSyms [w, 8 * d])
      (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ))
  rw [st_upd_hA, st_hA] at c7
  have c8 := runs_drainStep (lD : Lens (PR RH RLi RLo RL R1 R2 R3 R4) Bool) (.inr (.inl 1))
    (st S (carrSyms w (encCube P (cnotArr pairs z)) ++ rest) []
      (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ))
  rw [st_upd_hB, st_hB] at c8
  have e0 : st S (carrSyms w (encCube P z) ++ rest) [] [] = S := by
    rw [← hs0]; exact st_init S hA0 hB0
  have hall := runs_seq c0 (runs_seq c1 (runs_seq c2 (runs_seq c3 (runs_seq c4 (runs_seq c5
    (runs_seq c6 (runs_seq c7 c8)))))))
  rw [e0, st_final S _ hA0 hB0] at hall
  refine runs_mono hall (fun _ _ => trivial) (le_of_eq ?_)
  unfold cbCost gadCost
  ring

end Correct

/-! ## The cost bound -/

/-- The composite's constant (fixed by the parts' constants and the layer exponent `J_L`). -/
def cbConst (JL CH CLi CLo CL C1 C2 C3 C4 : ℕ) : ℕ :=
  CH + 9 * CLi + 12 * C1 + 6 * (CL * (9 ^ JL + 20)) + 4 * C3 + 2 * C2 + 2 * C4 + 9 * CLo + 66

theorem length_hdrSyms' (l : List ℕ) :
    (hdrSyms l).length = (l.map fun n => bitLen n + 1).sum := by
  induction l with
  | nil => simp [hdrSyms]
  | cons a l ih =>
    simp only [hdrSyms, List.flatMap_cons, List.length_append, length_natSyms,
      List.length_singleton, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- **The parts' costs sum to at most `cbConst` times the contract's bound** (Proposition 5.5: six layer
calls, a constant number of scans, the header and per-record address work explicit). -/
theorem cbCost_le (lam' : ℝ)
    {JL J1 J2 J3 J4 CH CLi CLo CL C1 C2 C3 C4 P d r w K m j₀ D nS ρ np : ℕ}
    (hw : P + 2 ≤ w) (hdw : d ≤ w + m) (hnp : np ≤ (m + 1) ^ 2) :
    cbCost lam' JL J1 J2 J3 J4 CH CLi CLo CL C1 C2 C3 C4 P d r w K m j₀ D nS ρ np ≤
      cbConst JL CH CLi CLo CL C1 C2 C3 C4 *
        (layerCost lam' (sliceRT P d r w K j₀ D nS ρ) + cvolCube m r (w + 8 * d) +
          2 ^ m * (w + m + 1) ^ (JL + J1 + J2 + J3 + J4 + 2) +
          (sliceHdr P d r w K m j₀ D nS ρ).length) := by
  obtain ⟨J, hJ⟩ : ∃ x, x = JL + J1 + J2 + J3 + J4 + 2 := ⟨_, rfl⟩
  obtain ⟨LC, hLC⟩ : ∃ x, x = layerCost lam' (sliceRT P d r w K j₀ D nS ρ) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ x, x = cvolCube m r (w + 8 * d) := ⟨_, rfl⟩
  obtain ⟨sh, hsh⟩ : ∃ x, x = (sliceHdr P d r w K m j₀ D nS ρ).length := ⟨_, rfl⟩
  obtain ⟨sh', hsh'⟩ : ∃ x, x = (sliceHdr (P + 8 * d) d r (w + 8 * d) K m j₀ D nS ρ).length :=
    ⟨_, rfl⟩
  obtain ⟨hA, hhA⟩ : ∃ x, x = (hdrSyms [w, 8 * d]).length := ⟨_, rfl⟩
  obtain ⟨Pm, hPm⟩ : ∃ x, x = 2 ^ m * (w + m + 1) ^ J := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ x, x = LC + V + Pm + sh := ⟨_, rfl⟩
  have hBJ : ∀ k, k ≤ J → (w + m + 1) ^ k ≤ Pm := by
    intro k hk
    rw [hPm]
    calc (w + m + 1) ^ k ≤ (w + m + 1) ^ J := Nat.pow_le_pow_right (by omega) hk
      _ ≤ 2 ^ m * (w + m + 1) ^ J := Nat.le_mul_of_pos_left _ (by positivity)
  have hPmB : w + m + 1 ≤ Pm := by simpa using hBJ 1 (by omega)
  have hsc : ∀ k, k ≤ J → 2 ^ m * ((w + m + 1) ^ k + np) ≤ 2 * Pm := by
    intro k hk
    have h1 : (w + m + 1) ^ k ≤ (w + m + 1) ^ J := Nat.pow_le_pow_right (by omega) hk
    have h2 : np ≤ (w + m + 1) ^ J := le_trans hnp
      (le_trans (Nat.pow_le_pow_left (by omega) 2) (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [hPm]
    calc 2 ^ m * ((w + m + 1) ^ k + np) ≤ 2 ^ m * ((w + m + 1) ^ J + (w + m + 1) ^ J) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (2 ^ m * (w + m + 1) ^ J) := by ring
  have hlay : (w + 8 * d + m + 1) ^ JL ≤ 9 ^ JL * Pm := by
    calc (w + 8 * d + m + 1) ^ JL ≤ (9 * (w + m + 1)) ^ JL := Nat.pow_le_pow_left (by omega) _
      _ = 9 ^ JL * (w + m + 1) ^ JL := mul_pow _ _ _
      _ ≤ 9 ^ JL * Pm := Nat.mul_le_mul_left _ (hBJ JL (by omega))
  have hsh'le : sh' ≤ sh + 18 * Pm := by
    have h1 := bitLen_le_self' (P + 8 * d)
    have h2 := bitLen_le_self' (w + 8 * d)
    rw [hsh', hsh]
    simp only [sliceHdr, length_hdrSyms', List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  have hhAle : hA ≤ 11 * Pm := by
    have h1 := bitLen_le_self' w
    have h2 := bitLen_le_self' (8 * d)
    rw [hhA]
    simp only [length_hdrSyms', List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  unfold cbCost gadCost cbConst
  rw [← hJ, ← hLC, ← hV, ← hsh', ← hsh, ← hhA, ← hPm]
  have t1 : CH * (sh + 1) ≤ CH * M := Nat.mul_le_mul_left _ (by omega)
  have t2 : CLi * (V + w + 8 * d + 1) ≤ CLi * (9 * M) := Nat.mul_le_mul_left _ (by omega)
  have t8 : CLo * (V + w + 8 * d + 1) ≤ CLo * (9 * M) := Nat.mul_le_mul_left _ (by omega)
  have ts : ∀ (Ci k : ℕ), k ≤ J →
      Ci * (V + 2 ^ m * ((w + m + 1) ^ k + np) + sh) ≤ Ci * (2 * M) := by
    intro Ci k hk
    have := hsc k hk
    exact Nat.mul_le_mul_left _ (by omega)
  have t3 := ts C1 J1 (by omega)
  have t5 := ts C3 J3 (by omega)
  have t6 := ts C2 J2 (by omega)
  have t7 := ts C4 J4 (by omega)
  have t4 : CL * (LC + (w + 8 * d + m + 1) ^ JL + sh') ≤ CL * ((9 ^ JL + 20) * M) := by
    apply Nat.mul_le_mul_left
    have h9 : 9 ^ JL * Pm ≤ 9 ^ JL * M := Nat.mul_le_mul_left _ (by omega)
    have he : (9 ^ JL + 20) * M = 9 ^ JL * M + 20 * M := by ring
    omega
  have t9 : 2 * hA + 3 ≤ 25 * M := by omega
  have t10 : 2 * sh' + 3 ≤ 41 * M := by omega
  calc _ ≤ CH * M + (CLi * (9 * M) + ((3 * (C1 * (2 * M)) + 3 * (CL * ((9 ^ JL + 20) * M)) +
          C3 * (2 * M)) + (C2 * (2 * M) + ((3 * (C1 * (2 * M)) +
          3 * (CL * ((9 ^ JL + 20) * M)) + C3 * (2 * M)) + (C4 * (2 * M) +
          (CLo * (9 * M) + (25 * M + 41 * M))))))) := by omega
    _ = _ := by rw [hM]; ring

end CnotBatchRed

open CnotBatchRed in
/-- **Proposition 5.5 on the machine, from its parts** (`prop:cnot-batch`): the
layer call on a cube slice (`CubeLayerStmt`), the exact lift and lowering (`LiftMachineStmt`,
`LowerMachineStmt`), the header builder (`CnotHdrStmt`) and the four recordwise scans
(`CnotScanStmt`) give `CnotBatchMachineStmt`. The program is `cbProg`; exactness follows from
Lemmas 5.1, 5.2, 5.4 (`hT_eq_selScalar_three_layer`, `layer_round`,
`cnotArr_eq_hT_cz_hT`); the cost is `cbCost_le` with `J = J_L + J₁ + J₂ + J₃ + J₄ + 2`. -/
theorem cnotBatchMachine_of {Band : LayerRT → Prop} {lam' : ℝ}
    (hLay : CubeLayerStmt Band lam') (hLift : LiftMachineStmt) (hLow : LowerMachineStmt)
    (hHdr : CnotHdrStmt) (hScan : ∀ mode, CnotScanStmt mode) :
    CnotBatchMachineStmt Band lam' := by
  obtain ⟨JL, CL, hLay⟩ := hLay
  obtain ⟨EL, iLf, iLd, RL, PL, fRL, nRL, cPL, sPL⟩ := hLay ()
  obtain ⟨CLi, hLift⟩ := hLift
  obtain ⟨ELi, iLif, iLid, RLi, PLi, fRLi, nRLi, cPLi, sPLi⟩ := hLift ()
  obtain ⟨CLo, hLow⟩ := hLow
  obtain ⟨ELo, iLof, iLod, RLo, PLo, fRLo, nRLo, cPLo, sPLo⟩ := hLow ()
  obtain ⟨CH, hHdr⟩ := hHdr
  obtain ⟨EH, iHf, iHd, RH, PH, fRH, nRH, cPH, sPH⟩ := hHdr ()
  obtain ⟨J1, C1, h1⟩ := hScan .selPhase
  obtain ⟨E1, i1f, i1d, R1, P1, fR1, nR1, cP1, sP1⟩ := h1 ()
  obtain ⟨J2, C2, h2⟩ := hScan .cz
  obtain ⟨E2, i2f, i2d, R2, P2, fR2, nR2, cP2, sP2⟩ := h2 ()
  obtain ⟨J3, C3, h3⟩ := hScan .selScalar
  obtain ⟨E3, i3f, i3d, R3, P3, fR3, nR3, cP3, sP3⟩ := h3 ()
  obtain ⟨J4, C4, h4⟩ := hScan .shift
  obtain ⟨E4, i4f, i4d, R4, P4, fR4, nR4, cP4, sP4⟩ := h4 ()
  have sL : LaySpec Band lam' JL EL RL CL PL := sPL
  have sLi : LiftSpec ELi RLi CLi PLi := sPLi
  have sLo : LowSpec ELo RLo CLo PLo := sPLo
  have sH : HdrSpec EH RH CH PH := sPH
  have s1 : ScanSpec .selPhase J1 E1 R1 C1 P1 := sP1
  have s2 : ScanSpec .cz J2 E2 R2 C2 P2 := sP2
  have s3 : ScanSpec .selScalar J3 E3 R3 C3 P3 := sP3
  have s4 : ScanSpec .shift J4 E4 R4 C4 P4 := sP4
  let iDX : DecidableEq (PX EH ELi ELo EL E1 E2 E3 E4) :=
    decEqSum (decEqSum (decEqSum iHd iLid) (decEqSum iLod iLd))
      (decEqSum (decEqSum i1d i2d) (decEqSum i3d i4d))
  let iFX : Fintype (PX EH ELi ELo EL E1 E2 E3 E4) :=
    fintypeSum (fintypeSum (fintypeSum iHf iLif) (fintypeSum iLof iLf))
      (fintypeSum (fintypeSum i1f i2f) (fintypeSum i3f i4f))
  refine ⟨JL + J1 + J2 + J3 + J4 + 2, cbConst JL CH CLi CLo CL C1 C2 C3 C4, fun _ =>
    ⟨Fin 2 ⊕ PX EH ELi ELo EL E1 E2 E3 E4, fintypeSum inferInstance iFX,
      decEqSum inferInstance iDX,
      PR RH RLi RLo RL R1 R2 R3 R4, cbProg PH PLi PLo PL P1 P2 P3 P4, inferInstance,
      inferInstance, closed_cbProg PH PLi PLo PL P1 P2 P3 P4 cPH cPLi cPLo cPL cP1 cP2 cP3 cP4,
      ?_⟩⟩
  intro P d r w K m j₀ D nS ρ pairs z rest hrest prest S hS hm hD1 hDd hρ hw hdw hKw hv htgt
    hband hz hbt hs0 hs1 hs2
  exact WP.W9comp.runs_mono (cbProg_runs (iX := iDX) sH sLi sLo sL s1 s2 s3 s4 hS hm hDd hρ hw
    hdw hKw hv htgt hband hz hbt hs0 hs1 hs2) (fun _ _ => trivial)
    (cbCost_le lam' hw hdw (length_pairsSyms_le hv))

end SubNLogN.Machine
