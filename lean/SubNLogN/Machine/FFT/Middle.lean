/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.Kit
import SubNLogN.Machine.FFT.MiddleMath

/-!
# K4 reduction (`Machine/FFT/Middle.lean`): the Walsh middle machine from its parts

**Scope (honest summary).** `walshMiddleMachine_of_parts` (namespace `SubNLogN.Machine`) proves
the machine form of Corollary 6.6 (`WalshMiddleMachineGenStmt Band lam'`, `Contracts/FFT.lean`)
from the five part contracts `PhaseTableMachineStmt`, `RecordDIFStmt`,
`LayoutExecStmt Band lam' .L`, `RoundsStmt Band lam'`, `LayoutExecStmt Band lam' .U`, for every
`Band` and `lam'`. There is no other hypothesis: the value-level facts come from proved theorems
(via `Machine/FFT/MiddleMath.lean`). No `sorry`. The helpers (layout, lenses, `midProg`, cost
lemma `midCost_bound`, and the composite lemma `midContract_of_parts`) live in the namespace
`SubNLogN.Machine.FFT.MiddleAux`.

## Plan (program design, invariants, cost accounting)
Paper: proof of Theorem 6.5 (`thm:direct-fft`, Section 6.4), stages (i)–(iv) in this order, with
the master phase table of Lemma 6.1 (`lem:phase-table`) built once up front.
* **Layout.** Named stacks `Fin 2` (`0` the tensor array, in place; `1` the header, restored).
  Private stacks `Unit ⊕ (E_T ⊕ (E_D ⊕ (E_L ⊕ (E_R ⊕ E_U))))`: `midTab = .inr (.inl ())` holds the
  phase table; the five blocks are the parts' private scratch. A part with named stacks `Fin 3`
  (array, header, table) is embedded by `midEmb j` (array ↦ array, header ↦ header,
  table ↦ `midTab`, scratch `e ↦ .inr (.inr (j e))`) through `callInj`; registers
  `Bool × (R_T × (R_D × (R_L × (R_R × R_U))))` with product lenses (`Bool` for the drain).
* **Program.** `table; DIF; L; rounds; U; drain(midTab)`.
* **Invariant.** Every private stack is empty on entry (`KClean`). After the table step `midTab`
  holds `tabSyms w q ℓ θ̃` (`θ̃ = phaseTable q ℓ`); each later part only replaces the array; its
  private block is still empty when it is called (no other step writes it); the drain empties
  `midTab` again. Values: `z₀ = ofTensor a ℓ U`, `z₁ = lastAxisFFT q ℓ θ̃ z₀`, `z₂ = L z₁`,
  `z₃ = rounds z₂`, `z₄ = U z₃`; each is disk-grid (`MiddleMath`), and `z₄` is the encoded
  `walshMiddle idealLayer` output (`walshMiddle_ofTensor_eq`).
* **Cost.** Sum of the parts' bounds plus the drain (`2·|tabSyms| + 3`); `midCost_bound` shows
  the sum is at most `(C_T + C_D + 2C_L + C_R + 2C_U + 15)·midCost lam' J D ℓ K w m₀` with
  `J = J_T + J_D + J_L + J_R + J_U + 2` (`m₀/d + K + 1 ≤ 2ℓ` since `m₀ ≤ Dℓ`, `K ≤ ℓ - 1`).
-/

namespace SubNLogN.Machine.FFT.MiddleAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
  SubNLogN.Machine.FFTKit

/-! ## 1. Layout of the composite -/

section Layout

variable {Ei X : Type}

/-- Embedding of a middle-level part (named stacks `Fin 3`: array, header, table; private
scratch `Ei`) into the middle's layout `KLoc (Fin 2) (Unit ⊕ X)`. -/
def midEmb (j : Ei → X) : KLoc (Fin 3) Ei → KLoc (Fin 2) (Unit ⊕ X)
  | .inl i => if (i : ℕ) = 0 then .inl 0 else if (i : ℕ) = 1 then .inl 1 else .inr (.inl ())
  | .inr e => .inr (.inr (j e))

@[simp] theorem midEmb_arr (j : Ei → X) : midEmb j (.inl 0) = .inl 0 := by simp [midEmb]
@[simp] theorem midEmb_hdr (j : Ei → X) : midEmb j (.inl 1) = .inl 1 := by simp [midEmb]
@[simp] theorem midEmb_tab (j : Ei → X) : midEmb j (.inl 2) = .inr (.inl ()) := by
  simp [midEmb]
@[simp] theorem midEmb_inr (j : Ei → X) (e : Ei) : midEmb j (.inr e) = .inr (.inr (j e)) := rfl

theorem midEmb_injective {j : Ei → X} (hj : Function.Injective j) :
    Function.Injective (midEmb j) := by
  rintro (i | e) (i' | e') h
  · fin_cases i <;> fin_cases i' <;> simp_all [midEmb]
  · fin_cases i <;> simp [midEmb] at h
  · fin_cases i' <;> simp [midEmb] at h
  · simp only [midEmb, Sum.inr.injEq] at h
    rw [hj h]

end Layout

/-! ## 2. Stack lengths -/

theorem length_coefBits (w : ℕ) (c : CInt) : (coefBits w c).length = 2 * w := by
  simp [coefBits, twosBits, bitsLE]
  ring

theorem length_crecBits (w : ℕ) (cs : List CInt) :
    (crecBits w cs).length = 2 * w * cs.length := by
  induction cs with
  | nil => simp [crecBits]
  | cons c cs ih =>
    simp only [crecBits, List.flatMap_cons, List.length_append] at ih ⊢
    rw [length_coefBits, ih, List.length_cons]
    ring

theorem length_carrSyms (w : ℕ) (v : List (List CInt)) :
    (carrSyms w v).length = (v.map fun cs => 2 * w * cs.length + 1).sum := by
  induction v with
  | nil => simp [carrSyms, arrSyms, blk]
  | cons cs v ih =>
    simp only [carrSyms, arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append,
      List.sum_cons] at ih ⊢
    rw [ih, recSyms, List.length_append, List.length_map, length_crecBits, List.length_singleton]

theorem length_tabSyms (w q ℓ : ℕ) (θt : ℕ → ℂ) :
    (tabSyms w q ℓ θt).length = 2 * 2 ^ ℓ * (2 * w + 1) := by
  rw [tabSyms, length_carrSyms, tabRecs, List.map_map]
  have h : ((fun cs : List CInt => 2 * w * cs.length + 1) ∘ fun j => [gridInt q (θt j)]) =
      fun _ => 2 * w + 1 := by
    funext j
    simp
  rw [h, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]

/-! ## 3. Cost accounting -/

theorem cvolCube_mono {m r w w' : ℕ} (h : w ≤ w') : cvolCube m r w ≤ cvolCube m r w' :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ h) 1)

/-- **The parts' costs sum to at most a constant times the middle's bound** (Section 6.4: the
table, the last axis, the two positional maps with `m₀/d ≤ ℓ` and `K ≤ ℓ - 1`, the rounds).
`H` is the header length (charged once per part), `dr` the drain cost of the table stack. -/
theorem midCost_bound (lam' : ℝ) {JT JD JL JR JU CT CD CL CR CU D ℓ K w m H dr : ℕ}
    (hℓ : 2 ≤ ℓ) (hKℓ : K ≤ ℓ - 1) (hm : m ≤ D * ℓ) (hℓw : ℓ ≤ w)
    (hdr : dr ≤ 15 * (2 ^ ℓ * (w + 1))) :
    CT * (2 ^ ℓ * (w + 1) ^ JT + H) +
      (CD * (ℓ * 2 ^ m * 2 ^ ℓ * mulW (2 * w + 1) + (ℓ + 1) * cvolCube m (2 ^ ℓ) w +
          2 ^ ℓ * (w + 1) ^ JD + H) +
        (CL * (permCost lam' JL (D + 1) (2 ^ ℓ) w K m + H) +
          (CR * (roundsCost lam' JR D ℓ K w m + H) +
            (CU * (permCost lam' JU (D + 1) (2 ^ ℓ) w K m + H) + dr)))) ≤
      (CT + CD + 2 * CL + CR + 2 * CU + 15) *
        (midCost lam' (JT + JD + JL + JR + JU + 2) D ℓ K w m + H) := by
  set J := JT + JD + JL + JR + JU + 2 with hJ
  set Lc := ⌈((D + 1 : ℕ) : ℝ) ^ lam'⌉₊ with hLc
  set Vs := cvolCube m (2 ^ ℓ) (w + 8 * (D + 1)) with hVs
  set V := cvolCube m (2 ^ ℓ) w with hV
  set X := (D + 1) * K + ℓ * Lc + ℓ + 1 with hX
  set Mu := ℓ * 2 ^ m * 2 ^ ℓ * mulW (2 * w + 1) with hMu
  set Pm := 2 ^ m * (w + m + 1) ^ J with hPm
  set Pt := 2 ^ ℓ * (w + 1) ^ J with hPt
  set M := midCost lam' J D ℓ K w m with hMdef
  have hM : M = Vs * X + Mu + Pm + Pt := rfl
  have hVVs : V ≤ Vs := cvolCube_mono (by omega)
  have hw1 : 1 ≤ w + 1 := by omega
  have hwm1 : 1 ≤ w + m + 1 := by omega
  -- (a) the table
  have ha : 2 ^ ℓ * (w + 1) ^ JT ≤ M := by
    have : 2 ^ ℓ * (w + 1) ^ JT ≤ Pt :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hw1 (by omega))
    omega
  -- (b) the last axis
  have hb : ℓ * 2 ^ m * 2 ^ ℓ * mulW (2 * w + 1) + (ℓ + 1) * V + 2 ^ ℓ * (w + 1) ^ JD ≤ M := by
    have h1 : (ℓ + 1) * V ≤ Vs * X :=
      calc (ℓ + 1) * V ≤ X * Vs := Nat.mul_le_mul (by omega) hVVs
        _ = Vs * X := Nat.mul_comm _ _
    have h2 : 2 ^ ℓ * (w + 1) ^ JD ≤ Pt :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hw1 (by omega))
    omega
  -- (c) a positional map
  have hperm : ∀ J', J' + 1 ≤ J → permCost lam' J' (D + 1) (2 ^ ℓ) w K m ≤ 2 * M := by
    intro J' hJ'
    have hdiv : m / (D + 1) ≤ ℓ :=
      Nat.div_le_of_le_mul (le_trans hm (Nat.mul_le_mul_right _ (Nat.le_succ D)))
    have h1 : m / (D + 1) + K + 1 ≤ 2 * ℓ := by omega
    have h2 : ℓ * (2 ^ m * (w + m + 1) ^ J') ≤ Pm :=
      calc ℓ * (2 ^ m * (w + m + 1) ^ J') ≤ (w + m + 1) * (2 ^ m * (w + m + 1) ^ J') :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ m * (w + m + 1) ^ (J' + 1) := by ring
        _ ≤ Pm := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hwm1 hJ')
    have h3 : ℓ * (Vs * (Lc + 1)) ≤ Vs * X :=
      calc ℓ * (Vs * (Lc + 1)) = Vs * (ℓ * Lc + ℓ) := by ring
        _ ≤ Vs * X := Nat.mul_le_mul_left _ (by omega)
    calc permCost lam' J' (D + 1) (2 ^ ℓ) w K m
        = (m / (D + 1) + K + 1) * (Vs * (Lc + 1) + 2 ^ m * (w + m + 1) ^ J') := rfl
      _ ≤ (2 * ℓ) * (Vs * (Lc + 1) + 2 ^ m * (w + m + 1) ^ J') := Nat.mul_le_mul_right _ h1
      _ = 2 * (ℓ * (Vs * (Lc + 1)) + ℓ * (2 ^ m * (w + m + 1) ^ J')) := by ring
      _ ≤ 2 * (Vs * X + Pm) := Nat.mul_le_mul_left _ (Nat.add_le_add h3 h2)
      _ ≤ 2 * M := Nat.mul_le_mul_left _ (by omega)
  -- (d) the rounds
  have hd : roundsCost lam' JR D ℓ K w m ≤ M := by
    have h2 : 2 ^ m * (w + m + 1) ^ JR ≤ Pm :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hwm1 (by omega))
    have h3 : roundsCost lam' JR D ℓ K w m = Vs * X + Mu + 2 ^ m * (w + m + 1) ^ JR := rfl
    omega
  -- (e) the drain
  have he : dr ≤ 15 * (M + H) := by
    have h1 : 2 ^ ℓ * (w + 1) ≤ Pt :=
      calc 2 ^ ℓ * (w + 1) = 2 ^ ℓ * (w + 1) ^ 1 := by rw [pow_one]
        _ ≤ Pt := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hw1 (by omega))
    omega
  have hL := hperm JL (by omega)
  have hU := hperm JU (by omega)
  calc _ ≤ CT * (M + H) + (CD * (M + H) + (CL * (2 * (M + H)) + (CR * (M + H) +
        (CU * (2 * (M + H)) + 15 * (M + H))))) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
          (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
            (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
              (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
                (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) he))))
    _ = (CT + CD + 2 * CL + CR + 2 * CU + 15) * (M + H) := by ring

/-! ## 4. The composite program -/

/-- Decidable equality of a sum from its summands, built explicitly. (Instance search for
`DecidableEq` of a deeply nested sum exceeds `synthInstance.maxSize`: the solution size doubles
with each level; the middle's layout has six levels.) -/
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

variable {ET ED EL ER EU RT RD RL RR RU : Type}

/-- Private stacks of the middle: the table stack, then the five parts' scratch blocks. -/
abbrev MidE (ET ED EL ER EU : Type) : Type := Unit ⊕ (ET ⊕ (ED ⊕ (EL ⊕ (ER ⊕ EU))))

/-- Registers of the middle: the drain flag, then the five parts' registers. -/
abbrev MidR (RT RD RL RR RU : Type) : Type := Bool × (RT × (RD × (RL × (RR × RU))))

/-- The private table stack of the middle. -/
abbrev midTab : KLoc (Fin 2) (MidE ET ED EL ER EU) := .inr (.inl ())

/-- Scratch injections of the five parts. -/
def injT : ET → ET ⊕ (ED ⊕ (EL ⊕ (ER ⊕ EU))) := Sum.inl
def injD : ED → ET ⊕ (ED ⊕ (EL ⊕ (ER ⊕ EU))) := fun e => .inr (.inl e)
def injL : EL → ET ⊕ (ED ⊕ (EL ⊕ (ER ⊕ EU))) := fun e => .inr (.inr (.inl e))
def injR : ER → ET ⊕ (ED ⊕ (EL ⊕ (ER ⊕ EU))) := fun e => .inr (.inr (.inr (.inl e)))
def injU : EU → ET ⊕ (ED ⊕ (EL ⊕ (ER ⊕ EU))) := fun e => .inr (.inr (.inr (.inr e)))

theorem injT_injective : Function.Injective (injT (ET := ET) (ED := ED) (EL := EL) (ER := ER)
    (EU := EU)) := fun _ _ h => by simpa [injT] using h
theorem injD_injective : Function.Injective (injD (ET := ET) (ED := ED) (EL := EL) (ER := ER)
    (EU := EU)) := fun _ _ h => by simpa [injD] using h
theorem injL_injective : Function.Injective (injL (ET := ET) (ED := ED) (EL := EL) (ER := ER)
    (EU := EU)) := fun _ _ h => by simpa [injL] using h
theorem injR_injective : Function.Injective (injR (ET := ET) (ED := ED) (EL := EL) (ER := ER)
    (EU := EU)) := fun _ _ h => by simpa [injR] using h
theorem injU_injective : Function.Injective (injU (ET := ET) (ED := ED) (EL := EL) (ER := ER)
    (EU := EU)) := fun _ _ h => by simpa [injU] using h

/-- Register lenses of the drain flag and the five parts. -/
def lnsB : Lens (MidR RT RD RL RR RU) Bool := Lens.fst _ _
def lnsT : Lens (MidR RT RD RL RR RU) RT := (Lens.snd _ _).comp (Lens.fst _ _)
def lnsD : Lens (MidR RT RD RL RR RU) RD :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lnsL : Lens (MidR RT RD RL RR RU) RL :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lnsR : Lens (MidR RT RD RL RR RU) RR :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
def lnsU : Lens (MidR RT RD RL RR RU) RU :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.snd _ _))))

/-- **The middle program**: table; DIF; `L`; rounds; `U`; drain the table stack. -/
def midProg (PT : Prog (KLoc (Fin 3) ET) (fun _ => Sym) RT)
    (PD : Prog (KLoc (Fin 3) ED) (fun _ => Sym) RD) (PL : Prog (KLoc (Fin 3) EL) (fun _ => Sym) RL)
    (PR : Prog (KLoc (Fin 3) ER) (fun _ => Sym) RR) (PU : Prog (KLoc (Fin 3) EU) (fun _ => Sym) RU) :
    Prog (KLoc (Fin 2) (MidE ET ED EL ER EU)) (fun _ => Sym) (MidR RT RD RL RR RU) :=
  .seq (callInj (midEmb injT) lnsT PT) (.seq (callInj (midEmb injD) lnsD PD)
    (.seq (callInj (midEmb injL) lnsL PL) (.seq (callInj (midEmb injR) lnsR PR)
      (.seq (callInj (midEmb injU) lnsU PU) (callInj id lnsB (drainProg midTab))))))

theorem closed_midProg {PT : Prog (KLoc (Fin 3) ET) (fun _ => Sym) RT}
    {PD : Prog (KLoc (Fin 3) ED) (fun _ => Sym) RD} {PL : Prog (KLoc (Fin 3) EL) (fun _ => Sym) RL}
    {PR : Prog (KLoc (Fin 3) ER) (fun _ => Sym) RR} {PU : Prog (KLoc (Fin 3) EU) (fun _ => Sym) RU}
    (hT : PT.Closed) (hD : PD.Closed) (hL : PL.Closed) (hR : PR.Closed) (hU : PU.Closed) :
    (midProg PT PD PL PR PU).Closed :=
  WP.W9comp.closed_seq (closed_callInj _ _ hT) (WP.W9comp.closed_seq (closed_callInj _ _ hD)
    (WP.W9comp.closed_seq (closed_callInj _ _ hL) (WP.W9comp.closed_seq (closed_callInj _ _ hR)
      (WP.W9comp.closed_seq (closed_callInj _ _ hU) (closed_callInj _ _ (closed_drainProg _))))))

end Composite

/-! ## 5. The reduction -/

/-- **The middle program meets the middle's contract**, given the five parts' specifications
(stated exactly as in the part contracts, for fixed programs `PT, …, PU` and constants). All
scratch and register types are fixed here with their instances; `walshMiddleMachine_of_parts`
instantiates them with the parts' witnesses. -/
theorem midContract_of_parts {ET ED EL ER EU RT RD RL RR RU : Type}
    [iDT : DecidableEq ET] [iDD : DecidableEq ED] [iDL : DecidableEq EL] [iDR : DecidableEq ER]
    [iDU : DecidableEq EU]
    [iRT : Finite RT] [iNT : Nonempty RT] [iRD : Finite RD] [iND : Nonempty RD]
    [iRL : Finite RL] [iNL : Nonempty RL] [iRR : Finite RR] [iNR : Nonempty RR]
    [iRU : Finite RU] [iNU : Nonempty RU]
    [iFE : Fintype (MidE ET ED EL ER EU)] [iDE : DecidableEq (MidE ET ED EL ER EU)]
    {Band : LayerRT → Prop} {lam' : ℝ} {JT JD JL JR JU CT CD CL CR CU : ℕ}
    {PT : Prog (KLoc (Fin 3) ET) (fun _ => Sym) RT} {PD : Prog (KLoc (Fin 3) ED) (fun _ => Sym) RD}
    {PL : Prog (KLoc (Fin 3) EL) (fun _ => Sym) RL} {PR : Prog (KLoc (Fin 3) ER) (fun _ => Sym) RR}
    {PU : Prog (KLoc (Fin 3) EU) (fun _ => Sym) RU}
    (hcT : PT.Closed) (hcD : PD.Closed) (hcL : PL.Closed) (hcR : PR.Closed) (hcU : PU.Closed)
    (hsT : ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest : List Sym) (S : KLoc (Fin 3) ET → List Sym),
      KClean S → MidShapeOK q ℓ K w a →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      Runs PT S (Function.update S (.inl 2) (tabSyms w q ℓ (phaseTable q ℓ) ++ S (.inl 2)))
        (fun _ => True) (CT * (2 ^ ℓ * (w + 1) ^ JT + (midHdr q ℓ K w a).length)))
    (hsD : ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
      (rest hrest trest : List Sym) (S : KLoc (Fin 3) ED → List Sym),
      KClean S → MidShapeOK q ℓ K w a → TabOK q ℓ θt → ArrOnDiskGrid q z → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube q z) ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      S (.inl 2) = tabSyms w q ℓ θt ++ trest →
      Runs PD S
        (Function.update S (.inl 0) (carrSyms w (encCube q (lastAxisFFT q ℓ θt z)) ++ rest))
        (fun _ => True)
        (CD * (ℓ * 2 ^ addrBits a * 2 ^ ℓ * mulW (2 * w + 1) +
          (ℓ + 1) * cvolCube (addrBits a) (2 ^ ℓ) w + 2 ^ ℓ * (w + 1) ^ JD +
          (midHdr q ℓ K w a).length)))
    (hsL : ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
      (rest hrest : List Sym) (S : KLoc (Fin 3) EL → List Sym),
      KClean S → MidShapeOK q ℓ K w a → SliceCallsBand Band q (D + 1) (2 ^ ℓ) w K (addrBits a) →
      ArrOnDiskGrid q z → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube q z) ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      Runs PL S
        (Function.update S (.inl 0)
          (carrSyms w (encCube q (posPermArr (layoutMap .L ℓ K a) z)) ++ rest))
        (fun _ => True)
        (CL * (permCost lam' JL (D + 1) (2 ^ ℓ) w K (addrBits a) + (midHdr q ℓ K w a).length)))
    (hsR : ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (θt : ℕ → ℂ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
      (rest hrest trest : List Sym) (S : KLoc (Fin 3) ER → List Sym),
      KClean S → MidShapeOK q ℓ K w a → ChunkCallsBand Band q ℓ K w a → TabOK q ℓ θt →
      ArrOnDiskGrid q z → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube q z) ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      S (.inl 2) = tabSyms w q ℓ θt ++ trest →
      Runs PR S
        (Function.update S (.inl 0)
          (carrSyms w (encCube q (runProg idealLayer (2 ^ ℓ) (roundsProg q D ℓ K a θt) z)) ++
            rest))
        (fun _ => True) (CR * (roundsCost lam' JR D ℓ K w (addrBits a) + (midHdr q ℓ K w a).length)))
    (hsU : ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (z : RArr (Cube (addrBits a)) (2 ^ ℓ))
      (rest hrest : List Sym) (S : KLoc (Fin 3) EU → List Sym),
      KClean S → MidShapeOK q ℓ K w a → SliceCallsBand Band q (D + 1) (2 ^ ℓ) w K (addrBits a) →
      ArrOnDiskGrid q z → BlkTerm rest →
      S (.inl 0) = carrSyms w (encCube q z) ++ rest →
      S (.inl 1) = midHdr q ℓ K w a ++ hrest →
      Runs PU S
        (Function.update S (.inl 0)
          (carrSyms w (encCube q (posPermArr (layoutMap .U ℓ K a) z)) ++ rest))
        (fun _ => True)
        (CU * (permCost lam' JU (D + 1) (2 ^ ℓ) w K (addrBits a) + (midHdr q ℓ K w a).length))) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R : Type)
      (P : Prog (KLoc (Fin 2) E) (fun _ => Sym) R), Finite R ∧ Nonempty R ∧ P.Closed ∧
      ∀ (q ℓ K w D : ℕ) (a : Fin D → ℕ) (U : Idx (fftShape a ℓ) → ℂ) (rest hrest : List Sym)
        (S : KLoc (Fin 2) E → List Sym),
        KClean S → MidShapeOK q ℓ K w a → MidCallsBand Band q ℓ K w a →
        (∀ j, OnDiskGrid q (U j)) → BlkTerm rest →
        S (.inl 0) = carrSyms w (encCube q (ofTensor a ℓ U)) ++ rest →
        S (.inl 1) = midHdr q ℓ K w a ++ hrest →
        Runs P S
          (Function.update S (.inl 0)
            (carrSyms w (encCube q (ofTensor a ℓ (walshMiddle idealLayer q D ℓ K a U))) ++ rest))
          (fun _ => True)
          ((CT + CD + 2 * CL + CR + 2 * CU + 15) *
            (midCost lam' (JT + JD + JL + JR + JU + 2) D ℓ K w (addrBits a) +
              (midHdr q ℓ K w a).length)) := by
  refine ⟨MidE ET ED EL ER EU, iFE, iDE, MidR RT RD RL RR RU,
    midProg PT PD PL PR PU, inferInstance, inferInstance,
    closed_midProg hcT hcD hcL hcR hcU, ?_⟩
  intro q ℓ K w D a U rest hrest S hcl hshape hband hU hrestT h0 h1
  have hcl' : ∀ e, S (.inr e) = [] := hcl
  obtain ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hw⟩ := hshape
  -- the values
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = phaseTable q ℓ := ⟨_, rfl⟩
  obtain ⟨z0, hz0⟩ : ∃ z, z = ofTensor a ℓ U := ⟨_, rfl⟩
  obtain ⟨z1, hz1⟩ : ∃ z, z = lastAxisFFT q ℓ θ z0 := ⟨_, rfl⟩
  obtain ⟨z2, hz2⟩ : ∃ z, z = posPermArr (layoutL ℓ K a) z1 := ⟨_, rfl⟩
  obtain ⟨z3, hz3⟩ : ∃ z, z = runProg idealLayer (2 ^ ℓ) (roundsProg q D ℓ K a θ) z2 :=
    ⟨_, rfl⟩
  obtain ⟨z4, hz4⟩ : ∃ z, z = posPermArr (layoutU ℓ K a) z3 := ⟨_, rfl⟩
  have htab : TabOK q ℓ θ := by rw [hθ]; exact tabOK_phaseTable hq8 hℓq.le
  have hd0 : ArrOnDiskGrid q z0 := by rw [hz0]; exact ofTensor_diskGrid hU
  have hd1 : ArrOnDiskGrid q z1 := by
    rw [hz1, hθ]; exact lastAxisFFT_diskGrid hq8 hℓq.le (by omega) hd0
  have hd2 : ArrOnDiskGrid q z2 := by
    rw [hz2]; exact DirectFFTProof.posPermArr_onDiskGrid _ hd1
  have hd3 : ArrOnDiskGrid q z3 := by rw [hz3]; exact rounds_ideal_diskGrid htab z2 hd2
  have hfin : ofTensor a ℓ (walshMiddle idealLayer q D ℓ K a U) = z4 := by
    have h1' := hd1
    have h3' := hd3
    rw [hz1, hz0, hθ] at h1'
    rw [hz3, hz2, hz1, hz0, hθ] at h3'
    rw [hz4, hz3, hz2, hz1, hz0, hθ]
    exact walshMiddle_ofTensor_eq_parts hK1 hKℓ hℓ2 ha U h1' h3'
  have hshape : MidShapeOK q ℓ K w a := ⟨hq8, hD1, hℓ2, hℓq, hK1, hKℓ, ha, hw⟩
  -- the intermediate stacks
  obtain ⟨S1, hS1⟩ : ∃ S', S' = Function.update S midTab (tabSyms w q ℓ θ) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S', S' = Function.update S1 (.inl 0) (carrSyms w (encCube q z1) ++ rest) :=
    ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ S', S' = Function.update S2 (.inl 0) (carrSyms w (encCube q z2) ++ rest) :=
    ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ S', S' = Function.update S3 (.inl 0) (carrSyms w (encCube q z3) ++ rest) :=
    ⟨_, rfl⟩
  obtain ⟨S5, hS5⟩ : ∃ S', S' = Function.update S4 (.inl 0) (carrSyms w (encCube q z4) ++ rest) :=
    ⟨_, rfl⟩
  -- facts about the intermediate stacks
  have hS1i : ∀ x, S1 (.inr (.inr x)) = [] := by intro x; rw [hS1]; simp [hcl']
  have hS2i : ∀ x, S2 (.inr (.inr x)) = [] := by intro x; rw [hS2]; simp [hS1i]
  have hS3i : ∀ x, S3 (.inr (.inr x)) = [] := by intro x; rw [hS3]; simp [hS2i]
  have hS4i : ∀ x, S4 (.inr (.inr x)) = [] := by intro x; rw [hS4]; simp [hS3i]
  have hS1h : S1 (.inl 1) = midHdr q ℓ K w a ++ hrest := by rw [hS1]; simp [h1]
  have hS2h : S2 (.inl 1) = midHdr q ℓ K w a ++ hrest := by rw [hS2]; simp [hS1h]
  have hS3h : S3 (.inl 1) = midHdr q ℓ K w a ++ hrest := by rw [hS3]; simp [hS2h]
  have hS4h : S4 (.inl 1) = midHdr q ℓ K w a ++ hrest := by rw [hS4]; simp [hS3h]
  have hS1t : S1 midTab = tabSyms w q ℓ θ := by rw [hS1]; simp
  have hS2t : S2 midTab = tabSyms w q ℓ θ := by rw [hS2]; simp [hS1t]
  have hS3t : S3 midTab = tabSyms w q ℓ θ := by rw [hS3]; simp [hS2t]
  have hS4t : S4 midTab = tabSyms w q ℓ θ := by rw [hS4]; simp [hS3t]
  have hS5t : S5 midTab = tabSyms w q ℓ θ := by rw [hS5]; simp [hS4t]
  have hS1a : S1 (.inl 0) = carrSyms w (encCube q z0) ++ rest := by rw [hS1, hz0]; simp [h0]
  have hS2a : S2 (.inl 0) = carrSyms w (encCube q z1) ++ rest := by rw [hS2]; simp
  have hS3a : S3 (.inl 0) = carrSyms w (encCube q z2) ++ rest := by rw [hS3]; simp
  have hS4a : S4 (.inl 0) = carrSyms w (encCube q z3) ++ rest := by rw [hS4]; simp
  -- step 1: the phase table
  have hr1 : Runs (callInj (midEmb injT) (@lnsT RT RD RL RR RU) PT) S S1 (fun _ => True)
      (CT * (2 ^ ℓ * (w + 1) ^ JT + (midHdr q ℓ K w a).length)) := by
    have hP := hsT q ℓ K w D a hrest (S ∘ midEmb injT) (fun e => hcl' _) hshape
      (by simpa using h1)
    have h := runs_callInj_update (midEmb_injective injT_injective) (@lnsT RT RD RL RR RU) hP
    refine WP.W9comp.runs_congr h ?_
    rw [hS1, hθ]
    simp [hcl']
  -- step 2: the last axis
  have hr2 : Runs (callInj (midEmb injD) (@lnsD RT RD RL RR RU) PD) S1 S2 (fun _ => True)
      (CD * (ℓ * 2 ^ addrBits a * 2 ^ ℓ * mulW (2 * w + 1) +
        (ℓ + 1) * cvolCube (addrBits a) (2 ^ ℓ) w + 2 ^ ℓ * (w + 1) ^ JD +
        (midHdr q ℓ K w a).length)) := by
    have hP := hsD q ℓ K w D a θ z0 rest hrest [] (S1 ∘ midEmb injD) (fun e => hS1i _) hshape
      htab hd0 hrestT (by simpa using hS1a) (by simpa using hS1h) (by simpa using hS1t)
    have h := runs_callInj_update (midEmb_injective injD_injective) (@lnsD RT RD RL RR RU) hP
    rw [midEmb_arr, ← hz1] at h
    rw [hS2]
    exact h
  -- step 3: the layout `L`
  have hr3 : Runs (callInj (midEmb injL) (@lnsL RT RD RL RR RU) PL) S2 S3 (fun _ => True)
      (CL * (permCost lam' JL (D + 1) (2 ^ ℓ) w K (addrBits a) + (midHdr q ℓ K w a).length)) := by
    have hP := hsL q ℓ K w D a z1 rest hrest (S2 ∘ midEmb injL) (fun e => hS2i _) hshape hband.2
      hd1 hrestT (by simpa using hS2a) (by simpa using hS2h)
    have h := runs_callInj_update (midEmb_injective injL_injective) (@lnsL RT RD RL RR RU) hP
    rw [midEmb_arr] at h
    rw [hS3, hz2]
    exact h
  -- step 4: the rounds
  have hr4 : Runs (callInj (midEmb injR) (@lnsR RT RD RL RR RU) PR) S3 S4 (fun _ => True)
      (CR * (roundsCost lam' JR D ℓ K w (addrBits a) + (midHdr q ℓ K w a).length)) := by
    have hP := hsR q ℓ K w D a θ z2 rest hrest [] (S3 ∘ midEmb injR) (fun e => hS3i _) hshape
      hband.1 htab hd2 hrestT (by simpa using hS3a) (by simpa using hS3h)
      (by simpa using hS3t)
    have h := runs_callInj_update (midEmb_injective injR_injective) (@lnsR RT RD RL RR RU) hP
    rw [midEmb_arr, ← hz3] at h
    rw [hS4]
    exact h
  -- step 5: the restoration `U`
  have hr5 : Runs (callInj (midEmb injU) (@lnsU RT RD RL RR RU) PU) S4 S5 (fun _ => True)
      (CU * (permCost lam' JU (D + 1) (2 ^ ℓ) w K (addrBits a) + (midHdr q ℓ K w a).length)) := by
    have hP := hsU q ℓ K w D a z3 rest hrest (S4 ∘ midEmb injU) (fun e => hS4i _) hshape hband.2
      hd3 hrestT (by simpa using hS4a) (by simpa using hS4h)
    have h := runs_callInj_update (midEmb_injective injU_injective) (@lnsU RT RD RL RR RU) hP
    rw [midEmb_arr] at h
    rw [hS5, hz4]
    exact h
  -- step 6: empty the table stack
  have hr6 : Runs (callInj id (@lnsB RT RD RL RR RU) (drainProg midTab)) S5
      (Function.update S5 midTab [])
      (fun _ => True) (2 * (S5 midTab).length + 3) :=
    runs_callInj_update (ι := id) Function.injective_id lnsB (runs_drainProg midTab (S5 ∘ id))
  have hall := WP.W9comp.runs_seq hr1 (WP.W9comp.runs_seq hr2 (WP.W9comp.runs_seq hr3
    (WP.W9comp.runs_seq hr4 (WP.W9comp.runs_seq hr5 hr6))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · -- the final stacks
    rw [hfin, hS5, hS4, hS3, hS2, hS1]
    funext k
    by_cases hk0 : k = .inl 0
    · subst hk0
      simp
    · by_cases hkT : k = midTab
      · subst hkT
        simp [hcl']
      · simp [hk0, hkT]
  · -- the cost
    have hm : addrBits a ≤ D * ℓ := addrBits_le_mul (fun i => by rcases ha i with h | h <;> omega)
    have hdr : 2 * (S5 midTab).length + 3 ≤ 15 * (2 ^ ℓ * (w + 1)) := by
      rw [hS5t, length_tabSyms]
      have h2 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
      have e1 : 2 * (2 * 2 ^ ℓ * (2 * w + 1)) + 3 = 8 * (2 ^ ℓ * w) + 4 * 2 ^ ℓ + 3 := by ring
      have e2 : 15 * (2 ^ ℓ * (w + 1)) = 15 * (2 ^ ℓ * w) + 15 * 2 ^ ℓ := by ring
      omega
    exact midCost_bound lam' hℓ2 hKℓ hm (by omega) hdr

end SubNLogN.Machine.FFT.MiddleAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Math.Walsh SubNLogN.Machine.FFT.MiddleAux

/-- **Corollary 6.6 (`cor:walsh-middle`), machine form, from its parts** (Theorem 6.5, `thm:direct-fft`).
The phase table (Lemma 6.1), the last axis (stage (i)), the positional map `L` (stage (ii)), the
record-axis rounds (stage (iii)) and the restoration `U = (LB)^{-1}` (stage (iv)), run in this order
and followed by emptying the table stack, implement `walshMiddle idealLayer` on the encoded
tensor, within `C·(midCost + |midHdr|)`. There is no other hypothesis: the value-level facts are
proved in `Machine/FFT/MiddleMath.lean`. -/
theorem walshMiddleMachine_of_parts {Band : LayerRT → Prop} {lam' : ℝ}
    (hTab : PhaseTableMachineStmt) (hDIF : RecordDIFStmt) (hLx : LayoutExecStmt Band lam' .L)
    (hRx : RoundsStmt Band lam') (hUx : LayoutExecStmt Band lam' .U) :
    WalshMiddleMachineGenStmt Band lam' := by
  obtain ⟨JT, CT, hT⟩ := hTab
  obtain ⟨JD, CD, hD⟩ := hDIF
  obtain ⟨JL, CL, hL⟩ := hLx
  obtain ⟨JR, CR, hR⟩ := hRx
  obtain ⟨JU, CU, hU⟩ := hUx
  obtain ⟨ET, iFT, iDT, RT, PT, iRT, iNT, hcT, hsT⟩ := hT ()
  obtain ⟨ED, iFD, iDD, RD, PD, iRD, iND, hcD, hsD⟩ := hD ()
  obtain ⟨EL, iFL, iDL, RL, PL, iRL, iNL, hcL, hsL⟩ := hL ()
  obtain ⟨ER, iFR, iDR, RR, PR, iRR, iNR, hcR, hsR⟩ := hR ()
  obtain ⟨EU, iFU, iDU, RU, PU, iRU, iNU, hcU, hsU⟩ := hU ()
  exact ⟨JT + JD + JL + JR + JU + 2, CT + CD + 2 * CL + CR + 2 * CU + 15, fun _ =>
    midContract_of_parts (iDT := iDT) (iDD := iDD) (iDL := iDL) (iDR := iDR) (iDU := iDU)
      (iRT := iRT)
      (iNT := iNT) (iRD := iRD) (iND := iND) (iRL := iRL) (iNL := iNL) (iRR := iRR)
      (iNR := iNR) (iRU := iRU) (iNU := iNU)
      (iFE := fintypeSum inferInstance (fintypeSum iFT (fintypeSum iFD (fintypeSum iFL
        (fintypeSum iFR iFU)))))
      (iDE := decEqSum inferInstance (decEqSum iDT (decEqSum iDD (decEqSum iDL
        (decEqSum iDR iDU))))) hcT hcD hcL hcR hcU hsT hsD hsL hsR hsU⟩

end SubNLogN.Machine
