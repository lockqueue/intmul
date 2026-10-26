/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.S5.ExecutablePipeline
import SubNLogN.S5.HeadlineCost
import WP.Top.Current6
import WP.W7k2.B.Top
import WP.W7k3.StdChar
import WP.W7k3t.Tap
import WP.W7k3c.Final
import WP.W9mp.Main
import WP.W9sp.Main
import WP.W9sq.Theorem
import WP.W9ex.Extract
import WP.W9h.Gate
import WP.W11b.Final

/-!
# Component S5 (`TopDispatcher.lean`): 6-stage `WP.Top.topProg` reduction to a Stage-5 contract

Proves (0 `sorry`; this file contains no `sorry`) that the 6-stage top-level program
`WP.Top.topProg Pin P7 hm7 Pc hmc P9 hm9` on the 76-work-stack layout `WP.Top.GW` yields
`Headline_TM2_SubNLogN_46` once a Stage-5 program `P9` with a headline-shaped cost bound is
supplied. With `n = operandBits a b`:
1. **Stage 1** (`Pin`, from `W0m_inputStage_proved`, 0 `sorry`): parses
   `inputStk (IntMulTM.encNatPair.encode (a, b))` into `prodOf (prmState n a b)` in
   `≤ 580 * C0 * n` steps (`inCostN_le_linear`).
2. **Stage 2** (`tabStage P7 hm7`, from `W7_buildTables_proved`, 0 `sorry`): builds the table tape
   `W7.tape W7.snapshotSchedule.toTapeFormat cSpec` with `WP.Top.Joint n cSpec` in
   `O(√n · (log₂ n)^8) ≤ O(n)` steps (`sqP_le_linear`).
3. **Stage 3** (`convStage Pc hmc`, from `WP.Top.TapeConv_proved`, 0 `sorry`): converts the table
   tape into `tapeSyms cSpec` in `O(n)` steps.
4. **Stage 4** (`WP.Top.glueStage`, 0 `sorry`): produces `prodOf (w9In n a b cSpec)` in `O(n)` steps.
5. **Stage 5** (`w9Stage P9 hm9`): enters in this module only as a contract hypothesis, in one of
   the forms below (and is discharged via `W9SubNLogNSpecX` in `S5/TopObligation.lean`).
6. **Stage 6** (`WP.Top.outStage`, 0 `sorry`): reverses `natSyms (a * b)` on `.oa`, writes
   `outputStk (encodeNat (a * b))` and clears all 76 work stacks in `O(n)` steps
   (`out_le`, `poly_le_linear`).

**Stage-5 contracts.** In the primed versions the only cost hypothesis is `HeadlineCost g C N`
(`S5/HeadlineCost.lean`) on one free function `g`; no transform and no split into stages is
prescribed. The headline itself is proved via `S5/TopExtended.lean` from the more permissive
`W9SubNLogNSpecX` (Stage 5 may also use any finite number of extra work stacks), which
`W9SubNLogNSpec'` implies (`w9X_of_w9'`).
* `W9SubNLogNSpec'`: a closed `BLoc m9` program taking, for every `cSpec` with
  `WP.Top.Joint n cSpec`, the `w9In n a b cSpec` stacks to the same stacks with
  `.OA := natSyms (a * b)`, `.OB := []`, within `T9 a b cSpec` steps, where
  `T9 a b cSpec ≤ g n + C9 * (|tapeSyms cSpec| + 1)` for `n ≥ N9` (`headline_46_of_w9_subNLogN'`).
* `CoreWorkProgSpec'`: a core work-stack multiplier between Stage 1 and the output stage, in
  `≤ g n` steps for `n ≥ N` (`headline_46_of_core_workProg'`).
* `W9PipeSubNLogNSpec'`: Stage 5 assembled by `WP.W9mp.multProg` from the proved
  split/square/extract/reconstruct stages and a pipeline program `Pp` computing an arbitrary
  transform map `F` that satisfies the root-recovery invariant `RootOKSubNLogN F`
  (`w9SubNLogNSpec'_of_pipe'`). The Walsh-bridge multiplier is instantiated on the extended-stack
  `W9SubNLogNSpecX` path (`SubNLogN/Assembly/`, `S5/TopObligation.lean`).

The unprimed versions `W9SubNLogNSpec`, `CoreWorkProgSpec`, `W9PipeSubNLogNSpec` replace
`HeadlineCost g C N` by `Monotone c.total ∧ SubNLogNStageBounds c A N` for a 6-stage schedule `c`.
That is a stronger sufficient condition (every stage `≤ A * n * (log₂ n)^(14/15)`) which the
paper's algorithm does not meet; each unprimed contract implies its primed version
(`w9SubNLogNSpec'_of_w9SubNLogNSpec`, `coreWorkProgSpec'_of_coreWorkProgSpec`,
`w9PipeSubNLogNSpec'_of_w9PipeSubNLogNSpec`).

The headline theorems `headline_TM2_subNLogN_46` (and `_47`, `_56`, `headline_TM2_littleO_nlogn`)
and the proved witness `w9SubNLogNSpecX_holds` (assembled from `SubNLogN/Machine/` and
`SubNLogN/Assembly/`) live in `S5/TopObligation.lean`.
-/

namespace SubNLogN.S5

open SubNLogN Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  IntMulTM.Contracts.Top

/-- **Unconditional Proof of `W0m_inputStage` (0 `sorry`):**
Instantiates `WP.W0m.W0m_inputStage_holds` with the proved `WP.W3.W3_addNat_holds` and
`WP.W6a.W6a_divModNat_holds WP.W3.W3_subNat_holds`. -/
theorem W0m_inputStage_proved : WP.W0m.W0m_inputStage :=
  WP.W0m.W0m_inputStage_holds WP.W3.W3_addNat_holds
    (WP.W6a.W6a_divModNat_holds WP.W3.W3_subNat_holds)

/-- **Unconditional Proof of `W7_buildTables W7.snapshotSchedule` (0 `sorry`):**
Instantiates `WP.Top.W7_buildTables_of_leaves` with all proved W3, W5, W6a, and W7 leaf contracts. -/
theorem W7_buildTables_proved : W7_buildTables W7.snapshotSchedule :=
  WP.Top.W7_buildTables_of_leaves WP.Top.W3_all_holds
    (WP.W6a.W6a_holds WP.W3.W3_subNat_holds)
    (WP.W5.W5_toom3Mul_holds
      (TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
      (TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
      TMFw.W3b.W3_smallOpInt_holds TMFw.W3s.W3_splitAt_holds TMFw.W3s.W3_shlVar_holds)
    WP.W7k3.W7_stdChar_bind
    WP.W7k3t.W7_sincGaussianTap_bind
    WP.W7k3c.W7_c0c1_bind
    WP.W7k2.W7_buildTablesRef_holds

/-- `inCostN C0 n` is strictly linear (`≤ 580 * C0 * n`) for all `n ≥ 1`. -/
theorem inCostN_le_linear (C0 n : ℕ) (hn : 1 ≤ n) :
    WP.Top.inCostN C0 n ≤ 580 * C0 * n := by
  unfold WP.Top.inCostN
  have h1 : C0 * (2 * n + 2) ≤ C0 * (4 * n) := Nat.mul_le_mul_left C0 (by omega)
  have h2 : C0 * (288 * (n + 1)) ≤ C0 * (576 * n) := Nat.mul_le_mul_left C0 (by omega)
  calc C0 * (2 * n + 2) + C0 * (288 * (n + 1))
      ≤ C0 * (4 * n) + C0 * (576 * n) := Nat.add_le_add h1 h2
    _ = 580 * C0 * n := by ring

/-- **`sqP n = (√n + 1)(log₂ n + 1)^8` is strictly linear (`≤ 2^41 * n`) for all `n ≥ 2` (0 `sorry`).** -/
theorem sqP_le_linear (n : ℕ) (hn : 2 ≤ n) :
    WP.Top.sqP n ≤ 2 ^ 41 * n := by
  have hn0 : n ≠ 0 := by omega
  have h1 : Nat.log2 n + 1 < 2 ^ (Nat.log2 n / 16 + 5) := by
    have hq : Nat.log2 n / 16 < 2 ^ (Nat.log2 n / 16) := Nat.lt_two_pow_self
    have e : 2 ^ (Nat.log2 n / 16 + 5) = 32 * 2 ^ (Nat.log2 n / 16) := by rw [pow_add]; ring
    rw [e]; omega
  have h2 : (Nat.log2 n + 1) ^ 8 ≤ 2 ^ (Nat.log2 n / 2 + 40) := by
    have h := Nat.pow_lt_pow_left h1 (by omega : (8 : ℕ) ≠ 0)
    rw [← pow_mul] at h
    exact le_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))
  have h3 : 2 ^ (Nat.log2 n / 2) ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt]
    calc 2 ^ (Nat.log2 n / 2) * 2 ^ (Nat.log2 n / 2) = 2 ^ (Nat.log2 n / 2 + Nat.log2 n / 2) :=
          (pow_add _ _ _).symm
      _ ≤ 2 ^ Nat.log2 n := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := Nat.log2_self_le hn0
  have hs1 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hs2 : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have e40 : 2 ^ (Nat.log2 n / 2 + 40) = 2 ^ 40 * 2 ^ (Nat.log2 n / 2) := by rw [pow_add]; ring
  have h4 : (Nat.log2 n + 1) ^ 8 ≤ 2 ^ 40 * Nat.sqrt n :=
    h2.trans (by rw [e40]; exact Nat.mul_le_mul_left _ h3)
  unfold WP.Top.sqP
  calc (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 8
      ≤ (Nat.sqrt n + 1) * (2 ^ 40 * Nat.sqrt n) := Nat.mul_le_mul_left _ h4
    _ = 2 ^ 40 * (Nat.sqrt n * Nat.sqrt n + Nat.sqrt n) := by ring
    _ ≤ 2 ^ 40 * (n + n) := Nat.mul_le_mul_left _ (Nat.add_le_add hs1 hs2)
    _ = 2 ^ 41 * n := by ring

/-- **Linear bound for `α * sqP n + β * n + γ` (`poly_le_linear`, 0 `sorry`).** -/
theorem poly_le_linear (α β γ n : ℕ) (hn : 2 ≤ n) :
    α * WP.Top.sqP n + β * n + γ ≤ (α * 2 ^ 41 + β + γ) * n := by
  have hq := sqP_le_linear n hn
  have h1 : α * WP.Top.sqP n ≤ α * (2 ^ 41 * n) := Nat.mul_le_mul_left α hq
  have h3 : γ ≤ γ * n := Nat.le_mul_of_pos_right γ (by omega)
  calc α * WP.Top.sqP n + β * n + γ
      ≤ α * (2 ^ 41 * n) + β * n + γ * n := Nat.add_le_add (Nat.add_le_add h1 le_rfl) h3
    _ = (α * 2 ^ 41 + β + γ) * n := by ring

/-- `outCost (bitLen (a * b)) (J₀ * operandBits a b)` is strictly linear in `operandBits a b`. -/
theorem outCost_le_linear (J₀ a b : ℕ) :
    WP.Top.outCost (bitLen (a * b)) (J₀ * operandBits a b) ≤
      (2 * J₀ + 196) * operandBits a b := by
  have hn1 : 1 ≤ operandBits a b := WP.W0m.operandBits_pos a b
  have hbit : bitLen (a * b) ≤ 2 * operandBits a b := WP.Top.bitLen_mul_le a b
  unfold WP.Top.outCost
  rw [WP.Top.length_allGW]
  calc 12 * bitLen (a * b) + 2 * (J₀ * operandBits a b) + 2 * 76 + 20
      ≤ 12 * (2 * operandBits a b) + 2 * (J₀ * operandBits a b) + 172 * operandBits a b := by
        omega
    _ = (2 * J₀ + 196) * operandBits a b := by ring

/-- Global register tuple for the 3-stage top-level program:
`σi` for `W0m` input stage, `Rcore` for the core multiplier, `Option Sym` for `outStage`. -/
abbrev SubNLogNTopRegs (σi Rcore : Type) := σi × Rcore × Option Sym

def lensIn3 (σi Rcore : Type) : Lens (SubNLogNTopRegs σi Rcore) σi :=
  Lens.fst _ _

def lensCore3 (σi Rcore : Type) : Lens (SubNLogNTopRegs σi Rcore) Rcore :=
  (Lens.snd _ _).comp (Lens.fst _ _)

def lensOut3 (σi Rcore : Type) : Lens (SubNLogNTopRegs σi Rcore) (Option Sym) :=
  (Lens.snd _ _).comp (Lens.snd _ _)

/-- **3-Stage Top-Level Program (`subNLogNTopProg`):**
Composes Stage 1 (`Pin` from `W0m`), Stage 2 (`Pcore` lifted to `StackId WP.Top.GW`), and
Stage 3 (`WP.Top.outStage`). -/
def subNLogNTopProg {σi Rcore : Type}
    (Pin : Prog (StackId WP.Top.GW) (StackId.Γ IntMulTM.PairSym) σi)
    (Pcore : Prog WP.Top.GW (fun _ => Sym) Rcore) :
    Prog (StackId WP.Top.GW) (StackId.Γ IntMulTM.PairSym) (SubNLogNTopRegs σi Rcore) :=
  .seq (Pin.liftRegs (lensIn3 σi Rcore))
    (.seq ((Pcore.liftWork IntMulTM.PairSym).liftRegs (lensCore3 σi Rcore))
      (WP.Top.outStage.liftRegs (lensOut3 σi Rcore)))

/-- `subNLogNTopProg Pin Pcore` is `.Closed` whenever `Pin.Closed` and `Pcore.Closed` (0 `sorry`). -/
theorem subNLogNTopProg_closed {σi Rcore : Type}
    {Pin : Prog (StackId WP.Top.GW) (StackId.Γ IntMulTM.PairSym) σi}
    {Pcore : Prog WP.Top.GW (fun _ => Sym) Rcore}
    (hin : Pin.Closed) (hcore : Pcore.Closed) :
    (subNLogNTopProg Pin Pcore).Closed := by
  have hout := WP.Top.outStage_closed
  unfold Prog.Closed at hin hcore hout ⊢
  simp only [subNLogNTopProg, Prog.FreeBelow, WP.W0m.freeBelow_liftRegs,
    WP.W0m.freeBelow_liftWork]
  exact ⟨hin, hcore, hout⟩

/-- **Postcondition of the Core Work-Stack Multiplier (`CorePost`):**
Stack `.oa` holds `natSyms (a * b) ++ rest` with `TermOK rest`, and total symbol count across
all 76 work stacks in `WP.Top.GW` is at most `J`. -/
def CorePost (a b J : ℕ) (S : WP.Top.GW → List Sym) : Prop :=
  (∃ rest, TermOK rest ∧ S .oa = natSyms (a * b) ++ rest) ∧
  WP.Top.totalSize S ≤ J

/-- **End-to-End 3-Stage Hoare Triple (`subNLogNTopProg_triple`, 0 `sorry`):**
Composes `Pin` (`W0m`), `Pcore`, and `WP.Top.outStage` into a complete `Triple` from
`inputStk (IntMulTM.encNatPair.encode (a, b))` to `outputStk (encodeNat (a * b))`. -/
theorem subNLogNTopProg_triple {σi Rcore : Type}
    {Pin : Prog (StackId WP.Top.GW) (StackId.Γ IntMulTM.PairSym) σi}
    {Pcore : Prog WP.Top.GW (fun _ => Sym) Rcore}
    {Tin Tcore J : ℕ → ℕ → ℕ}
    (hin : ∀ a b, Triple []
      (fun s => s.stk = inputStk (IntMulTM.encNatPair.encode (a, b)))
      Pin (WP.Top.InPost a b) (Tin a b))
    (hcore : ∀ a b, Triple []
      (fun s : St WP.Top.GW (fun _ => Sym) Rcore =>
        s.stk = WP.Top.prmState (operandBits a b) a b)
      Pcore (fun s => CorePost a b (J a b) s.stk) (Tcore a b))
    (σ0 : SubNLogNTopRegs σi Rcore) (a b : ℕ) :
    Triple []
      (· = ⟨σ0, inputStk (IntMulTM.encNatPair.encode (a, b))⟩)
      (subNLogNTopProg Pin Pcore)
      (fun s => s.stk = outputStk (encodeNat (a * b)))
      (Tin a b + (Tcore a b + WP.Top.outCost (bitLen (a * b)) (J a b))) := by
  -- Stage 1: Pin
  have h1 : Triple []
      (· = ⟨σ0, inputStk (IntMulTM.encNatPair.encode (a, b))⟩)
      (Pin.liftRegs (lensIn3 σi Rcore))
      (fun s => s.stk = WP.Top.prodOf (WP.Top.prmState (operandBits a b) a b))
      (Tin a b) := by
    refine (Triple.liftRegs (lensIn3 σi Rcore) (hin a b) (fun _ => True)
      (fun _ _ _ => trivial)).conseq ?_ ?_ le_rfl
    · rintro s rfl; exact ⟨rfl, trivial⟩
    · rintro s ⟨⟨hi, ho, hw, hz⟩, -⟩
      exact WP.Top.afterIn_eq a b hi ho hw hz
  -- Stage 2: Pcore
  have hw2 := Triple.liftWork (A := IntMulTM.PairSym) (hcore a b)
    (fun s => s.stk .input = [] ∧ s.stk .output = [])
    (fun _ _ hs hi ho => ⟨hi.trans hs.1, ho.trans hs.2⟩)
  have h2 : Triple []
      (fun s : St (StackId WP.Top.GW) (StackId.Γ IntMulTM.PairSym) (SubNLogNTopRegs σi Rcore) =>
        s.stk = WP.Top.prodOf (WP.Top.prmState (operandBits a b) a b))
      ((Pcore.liftWork IntMulTM.PairSym).liftRegs (lensCore3 σi Rcore))
      (fun s => s.stk .input = [] ∧ s.stk .output = [] ∧
        (∃ rest, TermOK rest ∧ s.stk (.work .oa) = natSyms (a * b) ++ rest) ∧
        WP.Top.totalSize (fun w => s.stk (.work w)) ≤ J a b)
      (Tcore a b) := by
    refine (Triple.liftRegs (lensCore3 σi Rcore) hw2 (fun _ => True)
      (fun _ _ _ => trivial)).conseq ?_ ?_ le_rfl
    · intro s hs
      exact ⟨WP.Top.pre_of_prodOf hs, trivial⟩
    · rintro s ⟨⟨⟨hrest, hsz⟩, hi, ho⟩, -⟩
      exact ⟨hi, ho, hrest, hsz⟩
  -- Stage 3: outStage
  have h3 : Triple []
      (fun s : St (StackId WP.Top.GW) (StackId.Γ IntMulTM.PairSym) (SubNLogNTopRegs σi Rcore) =>
        s.stk .input = [] ∧ s.stk .output = [] ∧
        (∃ rest, TermOK rest ∧ s.stk (.work .oa) = natSyms (a * b) ++ rest) ∧
        WP.Top.totalSize (fun w => s.stk (.work w)) ≤ J a b)
      (WP.Top.outStage.liftRegs (lensOut3 σi Rcore))
      (fun s => s.stk = outputStk (encodeNat (a * b)))
      (WP.Top.outCost (bitLen (a * b)) (J a b)) := by
    refine (Triple.liftRegs (lensOut3 σi Rcore)
      (WP.Top.outStage_triple (a * b) (J a b)) (fun _ => True)
      (fun _ _ _ => trivial)).conseq ?_ ?_ le_rfl
    · intro s hs; exact ⟨hs, trivial⟩
    · rintro s ⟨hs, -⟩; exact hs
  exact Triple.seq h1 (Triple.seq h2 h3)

set_option linter.style.haveILetI false

/-- **Core work-stack multiplier contract, per-stage version (`CoreWorkProgSpec`):**
Existence of a closed work-stack program `Pcore : Prog WP.Top.GW (fun _ => Sym) Rcore` over a
finite nonempty register type `Rcore` that computes `CorePost a b (J₀ * operandBits a b)` from
`prmState (operandBits a b) a b` in `Tcore a b` steps, where for `N ≤ operandBits a b`,
`Tcore a b ≤ c.total (operandBits a b)` for a 6-stage schedule `c` with `Monotone c.total` and
`SubNLogNStageBounds c A N`. The per-stage bounds (every stage `≤ A * n * (log₂ n)^(14/15)`) are a
stronger sufficient condition that the paper's algorithm does not meet. This contract implies the
headline-shaped `CoreWorkProgSpec'` (`coreWorkProgSpec'_of_coreWorkProgSpec`). -/
def CoreWorkProgSpec : Prop :=
  ∃ (Rcore : Type) (_ : Finite Rcore) (_ : Nonempty Rcore)
    (Pcore : Prog WP.Top.GW (fun _ => Sym) Rcore)
    (Tcore : ℕ → ℕ → ℕ) (c : SubNLogNStageCosts) (A N J₀ : ℕ),
    Pcore.Closed ∧
    Monotone c.total ∧
    SubNLogNStageBounds c A N ∧
    (∀ a b : ℕ, Triple []
      (fun s : St WP.Top.GW (fun _ => Sym) Rcore =>
        s.stk = WP.Top.prmState (operandBits a b) a b)
      Pcore (fun s => CorePost a b (J₀ * operandBits a b) s.stk) (Tcore a b)) ∧
    (∀ a b : ℕ, N ≤ operandBits a b → Tcore a b ≤ c.total (operandBits a b))

/-- **Core work-stack multiplier contract, headline-shaped version (`CoreWorkProgSpec'`):**
Existence of a closed work-stack program `Pcore : Prog WP.Top.GW (fun _ => Sym) Rcore` over a
finite nonempty register type `Rcore` that computes `CorePost a b (J₀ * operandBits a b)` from
`prmState (operandBits a b) a b` in `Tcore a b` steps, where for `N ≤ operandBits a b`,
`Tcore a b ≤ g (operandBits a b)` for some function `g` with `HeadlineCost g C N`. No algorithm,
transform, or split of the cost into stages is prescribed. -/
def CoreWorkProgSpec' : Prop :=
  ∃ (Rcore : Type) (_ : Finite Rcore) (_ : Nonempty Rcore)
    (Pcore : Prog WP.Top.GW (fun _ => Sym) Rcore)
    (Tcore : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (C N J₀ : ℕ),
    Pcore.Closed ∧
    HeadlineCost g C N ∧
    (∀ a b : ℕ, Triple []
      (fun s : St WP.Top.GW (fun _ => Sym) Rcore =>
        s.stk = WP.Top.prmState (operandBits a b) a b)
      Pcore (fun s => CorePost a b (J₀ * operandBits a b) s.stk) (Tcore a b)) ∧
    (∀ a b : ℕ, N ≤ operandBits a b → Tcore a b ≤ g (operandBits a b))

/-- `CoreWorkProgSpec` implies `CoreWorkProgSpec'` (take `g = c.total`, by
`headlineCost_of_stageBounds`; 0 `sorry`). -/
theorem coreWorkProgSpec'_of_coreWorkProgSpec (h : CoreWorkProgSpec) : CoreWorkProgSpec' := by
  obtain ⟨Rcore, hfc, hnc, Pcore, Tcore, c, A, N, J₀, hclcore, hmono, hb, htrcore, hbound⟩ := h
  obtain ⟨C, hC⟩ := headlineCost_of_stageBounds c A N hmono hb
  exact ⟨Rcore, hfc, hnc, Pcore, Tcore, c.total, C, N, J₀, hclcore, hC, htrcore, hbound⟩

/-- **Assembly from `CoreWorkProgSpec'` (`headline_46_of_core_workProg'`, 0 `sorry`):**
Composes `Pin` (from `W0m_inputStage_proved`), `Pcore` (from `CoreWorkProgSpec'`), and
`WP.Top.outStage` (from `WP.Top.outStage_triple`), bounds the linear `W0m` and `outStage`
costs via `inCostN_le_linear` and `outCost_le_linear` (absorbed by `HeadlineCost.add_linear`),
applies `eventually_supCost_subNLogN` and `TMFw.acceptTM`, and transports along `pairSymEquiv`
to yield `Headline_TM2_SubNLogN_46`. -/
theorem headline_46_of_core_workProg' (hCore : CoreWorkProgSpec') :
    Headline_TM2_SubNLogN_46 := by
  obtain ⟨σi, hfi, hni, C0, hW0⟩ := W0m_inputStage_proved
  obtain ⟨Pin, hclin, hin⟩ := hW0 WP.Top.GW WP.Top.ι0 WP.Top.ι0_inj
  obtain ⟨Rcore, hfc, hnc, Pcore, Tcore, gc, Cg, N, J₀, hclcore, hgc, htrcore, hbound⟩ := hCore
  have _ := hfi
  have _ := hfc
  haveI : Fintype σi := Fintype.ofFinite σi
  haveI : Fintype Rcore := Fintype.ofFinite Rcore
  let Tin (a b : ℕ) : ℕ :=
    C0 * ((IntMulTM.encNatPair.encode (a, b)).length + 1) +
      C0 * ((WP.W0m.lam a b + 1) * (WP.W0m.lam a b + 1))
  let J (a b : ℕ) : ℕ := J₀ * operandBits a b
  let f (a b : ℕ) : ℕ := Tin a b + (Tcore a b + WP.Top.outCost (bitLen (a * b)) (J a b))
  let Klin : ℕ := 580 * C0 + (2 * J₀ + 196) + 1
  let g (n : ℕ) : ℕ := gc n + Klin * n
  have hgH : HeadlineCost g (2 * (Cg + (Klin + 1))) N := hgc.add_linear Klin
  have hfg : ∀ a b, N ≤ operandBits a b → f a b ≤ g (operandBits a b) := by
    intro a b hN
    have hn1 : 1 ≤ operandBits a b := WP.W0m.operandBits_pos a b
    have h1 : Tin a b ≤ 580 * C0 * operandBits a b :=
      le_trans (WP.Top.tin_le C0 a b) (inCostN_le_linear C0 (operandBits a b) hn1)
    have h2 : Tcore a b ≤ gc (operandBits a b) := hbound a b hN
    have h3 : WP.Top.outCost (bitLen (a * b)) (J a b) ≤ (2 * J₀ + 196) * operandBits a b :=
      outCost_le_linear J₀ a b
    dsimp only [f, g, Klin]
    calc Tin a b + (Tcore a b + WP.Top.outCost (bitLen (a * b)) (J a b))
        ≤ 580 * C0 * operandBits a b + (gc (operandBits a b) + (2 * J₀ + 196) * operandBits a b) :=
          Nat.add_le_add h1 (Nat.add_le_add h2 h3)
      _ ≤ gc (operandBits a b) + (580 * C0 + (2 * J₀ + 196) + 1) * operandBits a b := by
          have : 580 * C0 * operandBits a b + (gc (operandBits a b) + (2 * J₀ + 196) * operandBits a b) =
              gc (operandBits a b) + (580 * C0 + (2 * J₀ + 196)) * operandBits a b := by ring
          rw [this]
          exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  obtain ⟨C', N', hC', hSup⟩ :=
    eventually_supCost_subNLogN f g N (2 * (Cg + (Klin + 1))) hgH.1 hfg hgH.2.2.2
  let σ0 : SubNLogNTopRegs σi Rcore := (Classical.choice hni, Classical.choice hnc, none)
  let Ptop := subNLogNTopProg Pin Pcore
  have hEval : ∀ p : ℕ × ℕ, ∃ v t,
      Eval [] Ptop ⟨σ0, inputStk (IntMulTM.encNatPair.encode p)⟩
        ⟨v, outputStk (encodeNat (p.1 * p.2))⟩ t ∧
      t ≤ WP.Top.supCost f (IntMulTM.encNatPair.encode p).length := by
    intro p
    have htr := (subNLogNTopProg_triple hin htrcore σ0 p.1 p.2).cost_mono
      (WP.Top.le_supCost f (WP.Top.lt_two_pow_enc_left p.1 p.2) (WP.Top.lt_two_pow_enc_right p.1 p.2))
    obtain ⟨s', t, he, hq, ht⟩ := htr _ rfl
    refine ⟨s'.var, t, ?_, ht⟩
    rw [← hq]
    exact he
  exact transport_TM2_subNLogN
    ⟨TMFw.acceptTM IntMulTM.encNatPair (fun p => p.1 * p.2) Ptop σ0 (WP.Top.supCost f) hEval,
      TMFw.acceptTM_finite, C', N', hC', hSup⟩

/-- **Assembly from `CoreWorkProgSpec` (`headline_46_of_core_workProg`, 0 `sorry`):**
Corollary of `headline_46_of_core_workProg'` and `coreWorkProgSpec'_of_coreWorkProgSpec`. -/
theorem headline_46_of_core_workProg (hCore : CoreWorkProgSpec) :
    Headline_TM2_SubNLogN_46 :=
  headline_46_of_core_workProg' (coreWorkProgSpec'_of_coreWorkProgSpec hCore)

/-! ## 6-Stage `WP.Top.topProg` Reduction to Stage 5 (`W9SubNLogNSpec'`) -/

/-- **Stage 5 (`w9Stage P9 hm9`) lifted to `TopRegs` (`stage_w9_subNLogN`, 0 `sorry`):** -/
theorem stage_w9_subNLogN {σi R7 Rc R9 : Type} {m : ℕ} (hm : m ≤ 64)
    {P9 : Prog (BLoc m) (fun _ => Sym) R9} {T9 : ℕ}
    (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (hr : Runs P9
      (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm l))
      (Function.update
        (Function.update
          (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm l))
          (.inl .OA) (natSyms (a * b) ++ []))
        (.inl .OB) [])
      (fun _ => True) T9) :
    Triple []
      (fun s : St (StackId WP.Top.GW) (StackId.Γ IntMulTM.PairSym)
          (WP.Top.TopRegs σi R7 Rc R9) =>
        s.stk = WP.Top.prodOf (WP.Top.w9In (operandBits a b) a b cSpec))
      ((WP.Top.w9Stage P9 hm).liftRegs (WP.Top.l9 σi R7 Rc R9))
      (fun s => s.stk = WP.Top.prodOf (WP.Top.w9Out (operandBits a b) a b cSpec (a * b)))
      T9 := by
  have he := Runs.embed (WP.Top.ι9_inj hm) hr (WP.Top.w9In (operandBits a b) a b cSpec)
    (fun _ => rfl)
  have hw := Triple.liftWork (A := IntMulTM.PairSym) he
    (fun s => s.stk .input = [] ∧ s.stk .output = [])
    (fun _ _ hs hi ho => ⟨hi.trans hs.1, ho.trans hs.2⟩)
  refine (Triple.liftRegs (WP.Top.l9 σi R7 Rc R9) hw (fun _ => True)
    (fun _ _ _ => trivial)).conseq ?_ ?_ le_rfl
  · intro s hs
    exact ⟨WP.Top.pre_of_prodOf hs, trivial⟩
  · rintro s ⟨⟨⟨h1, h2, -⟩, hi, ho⟩, -⟩
    refine WP.Top.eq_prodOf hi ho (fun w => ?_)
    exact congrFun (WP.Top.afterW9_eq hm _ a b cSpec (a * b)
      (T := fun w => s.stk (.work w)) h1 h2) w

/-- **The 6-Stage Composed Triple (`top_subNLogN_triple`, 0 `sorry`):**
Composes Stages 1–6 (`Pin`, `tabStage P7`, `convStage Pc`, `glueStage`, `w9Stage P9`, `outStage`)
into a single Hoare triple for `WP.Top.topProg Pin P7 hm7 Pc hmc P9 hm9`. -/
theorem top_subNLogN_triple {σi R7 Rc R9 : Type} {m7 mc m9 : ℕ}
    (hm7 : m7 ≤ 32) (hmc : mc ≤ 75) (hm9 : m9 ≤ 64)
    {Pin : Prog (StackId WP.Top.GW) (StackId.Γ IntMulTM.PairSym) σi}
    {Tin : ℕ → ℕ → ℕ}
    (hin : ∀ a b, Triple []
      (fun s => s.stk = inputStk (IntMulTM.encNatPair.encode (a, b))) Pin (WP.Top.InPost a b)
      (Tin a b))
    {P7 : Prog (Loc 4 m7) (fun _ => Sym) R7} {C7 : ℕ} (h7 : WP.Top.W7Spec P7 C7)
    {Pc : Prog (Loc 1 mc) (fun _ => Sym) Rc} {Cc : ℕ} (hc : WP.Top.ConvSpec Pc Cc)
    {P9 : Prog (BLoc m9) (fun _ => Sym) R9}
    {T9 : ℕ → ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ}
    (h9 : ∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      WP.Top.Joint (operandBits a b) cSpec →
      Runs P9
        (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l))
        (Function.update
          (Function.update
            (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l))
            (.inl .OA) (natSyms (a * b) ++ []))
          (.inl .OB) [])
        (fun _ => True) (T9 a b cSpec))
    (σ0 : WP.Top.TopRegs σi R7 Rc R9) (a b : ℕ) :
    ∃ cSpec, WP.Top.Joint (operandBits a b) cSpec ∧
      Triple [] (· = ⟨σ0, inputStk (IntMulTM.encNatPair.encode (a, b))⟩)
        (WP.Top.topProg Pin P7 hm7 Pc hmc P9 hm9)
        (fun s => s.stk = outputStk (encodeNat (a * b)))
        (Tin a b + (WP.Top.tabCost C7 (operandBits a b) cSpec + (WP.Top.convCost Cc cSpec +
          (WP.Top.glueCost (operandBits a b) + (T9 a b cSpec +
            WP.Top.outCost (bitLen (a * b))
              (WP.Top.totalSize (WP.Top.w9Out (operandBits a b) a b cSpec (a * b)))))))) := by
  obtain ⟨cSpec, hj, h2⟩ :=
    WP.Top.stage_tab (σi := σi) (Rc := Rc) (R9 := R9) hm7 h7 (operandBits a b) a b
  refine ⟨cSpec, hj, ?_⟩
  exact Triple.seq (WP.Top.stage_in a b σ0 (hin a b))
    (Triple.seq h2
      (Triple.seq (WP.Top.stage_conv hmc hc _ a b cSpec hj)
        (Triple.seq (WP.Top.stage_glue _ a b cSpec)
          (Triple.seq (stage_w9_subNLogN hm9 a b cSpec (h9 a b cSpec hj))
            (WP.Top.stage_out _ a b (a * b) cSpec)))))

/-- **Stage-5 `BLoc m9` multiplier contract, per-stage version (`W9SubNLogNSpec`):**
Existence of a closed `BLoc m9` program `P9` (`m9 ≤ 64`) over a finite nonempty register type `R9`
that, for every `cSpec` with `WP.Top.Joint (operandBits a b) cSpec`, runs from the `BLoc m9` view
of `w9In (operandBits a b) a b cSpec` to the same stacks with `.OA := natSyms (a * b)` and
`.OB := []` within `T9 a b cSpec` steps, where for `N9 ≤ operandBits a b`,
`T9 a b cSpec ≤ c.total (operandBits a b) + C9 * ((tapeSyms cSpec).length + 1)` for a 6-stage
schedule `c` with `Monotone c.total` and `SubNLogNStageBounds c A N9`. The per-stage bounds (every
stage `≤ A * n * (log₂ n)^(14/15)`) are a stronger sufficient condition that the paper's algorithm
does not meet. This contract implies the headline-shaped `W9SubNLogNSpec'`
(`w9SubNLogNSpec'_of_w9SubNLogNSpec`). -/
def W9SubNLogNSpec : Prop :=
  ∃ (m9 : ℕ) (R9 : Type) (P9 : Prog (BLoc m9) (fun _ => Sym) R9)
    (hm9 : m9 ≤ 64) (_ : Finite R9) (_ : Nonempty R9)
    (T9 : ℕ → ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ)
    (C9 : ℕ) (c : SubNLogNStageCosts) (A N9 : ℕ),
    P9.Closed ∧
    Monotone c.total ∧
    SubNLogNStageBounds c A N9 ∧
    (∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      WP.Top.Joint (operandBits a b) cSpec →
      Runs P9
        (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l))
        (Function.update
          (Function.update
            (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l))
            (.inl .OA) (natSyms (a * b) ++ []))
          (.inl .OB) [])
        (fun _ => True)
        (T9 a b cSpec)) ∧
    (∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      N9 ≤ operandBits a b →
      WP.Top.Joint (operandBits a b) cSpec →
      T9 a b cSpec ≤ c.total (operandBits a b) + C9 * ((tapeSyms cSpec).length + 1))

/-- **Stage-5 `BLoc m9` multiplier contract, headline-shaped version (`W9SubNLogNSpec'`):**
Existence of a closed `BLoc m9` program `P9` (`m9 ≤ 64`) over a finite nonempty register type `R9`
that, for every `cSpec` with `WP.Top.Joint (operandBits a b) cSpec`, runs from the `BLoc m9` view
of `w9In (operandBits a b) a b cSpec` to the same stacks with `.OA := natSyms (a * b)` and
`.OB := []` within `T9 a b cSpec` steps, where for `N9 ≤ operandBits a b`,
`T9 a b cSpec ≤ g (operandBits a b) + C9 * ((tapeSyms cSpec).length + 1)` for some function `g`
with `HeadlineCost g C N9`. No algorithm, transform, or split of the cost into stages is
prescribed. It implies the more permissive `W9SubNLogNSpecX` of `S5/TopExtended.lean`
(`w9X_of_w9'`), from which the headline is proved. -/
def W9SubNLogNSpec' : Prop :=
  ∃ (m9 : ℕ) (R9 : Type) (P9 : Prog (BLoc m9) (fun _ => Sym) R9)
    (hm9 : m9 ≤ 64) (_ : Finite R9) (_ : Nonempty R9)
    (T9 : ℕ → ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ)
    (C9 : ℕ) (g : ℕ → ℕ) (C N9 : ℕ),
    P9.Closed ∧
    HeadlineCost g C N9 ∧
    (∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      WP.Top.Joint (operandBits a b) cSpec →
      Runs P9
        (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l))
        (Function.update
          (Function.update
            (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l))
            (.inl .OA) (natSyms (a * b) ++ []))
          (.inl .OB) [])
        (fun _ => True)
        (T9 a b cSpec)) ∧
    (∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      N9 ≤ operandBits a b →
      WP.Top.Joint (operandBits a b) cSpec →
      T9 a b cSpec ≤ g (operandBits a b) + C9 * ((tapeSyms cSpec).length + 1))

/-- `W9SubNLogNSpec` implies `W9SubNLogNSpec'` (take `g = c.total`, by
`headlineCost_of_stageBounds`; 0 `sorry`). -/
theorem w9SubNLogNSpec'_of_w9SubNLogNSpec (h : W9SubNLogNSpec) : W9SubNLogNSpec' := by
  obtain ⟨m9, R9, P9, hm9, hf9, hn9, T9, C9, c, A, N9, hcl9, hmono, hb, hspec9, hbound9⟩ := h
  obtain ⟨C, hC⟩ := headlineCost_of_stageBounds c A N9 hmono hb
  exact ⟨m9, R9, P9, hm9, hf9, hn9, T9, C9, c.total, C, N9, hcl9, hC, hspec9, hbound9⟩

/-- **6-stage assembly from `W9SubNLogNSpec'` (`headline_46_of_w9_subNLogN'`, 0 `sorry`):**
Plugs `W0m_inputStage_proved` (Stage 1), `W7_buildTables_proved` (Stage 2),
`WP.Top.TapeConv_proved` (Stage 3), `WP.Top.glueStage` (Stage 4), `hW9 : W9SubNLogNSpec'`
(Stage 5), and `WP.Top.outStage` (Stage 6) into `WP.Top.topProg`, proves that Stages 1, 2, 3, 4, 6
and the tape-reading term `C9 * (|tapeSyms| + 1)` are `O(n)` via `inCostN_le_linear` and
`poly_le_linear` (absorbed by `HeadlineCost.add_linear`), and compiles `WP.Top.topProg` via
`TMFw.acceptTM` and `transport_TM2_subNLogN` to `Headline_TM2_SubNLogN_46`. -/
theorem headline_46_of_w9_subNLogN' (hW9 : W9SubNLogNSpec') :
    Headline_TM2_SubNLogN_46 := by
  obtain ⟨σi, hfi, hni, C0, hW0⟩ := W0m_inputStage_proved
  obtain ⟨Pin, hclin, hin⟩ := hW0 WP.Top.GW WP.Top.ι0 WP.Top.ι0_inj
  obtain ⟨C7, hC7⟩ := W7_buildTables_proved
  obtain ⟨m7, R7, -, P7, hm7, hf7, hn7, hcl7, hspec7⟩ := hC7 ()
  obtain ⟨Cc, hCc⟩ := WP.Top.TapeConv_proved
  obtain ⟨mc, Rc, -, Pc, hmc, hfc, hnc, hclc, hspecc⟩ := hCc ()
  obtain ⟨Cp, Np, hCp⟩ := WP.W7pure.W7_tableCost_sqrt_holds
  obtain ⟨Ct, Nt, hCt⟩ := WP.W7pure.W7_tapeBound_sqrt_holds
  obtain ⟨m9, R9, P9, hm9, hf9, hn9, T9, C9, g9, Cg, N9, hcl9, hg9, hspec9, hbound9⟩ := hW9
  have _ := hfi; have _ := hf7; have _ := hfc; have _ := hf9
  haveI : Fintype σi := Fintype.ofFinite σi
  haveI : Fintype R7 := Fintype.ofFinite R7
  haveI : Fintype Rc := Fintype.ofFinite Rc
  haveI : Fintype R9 := Fintype.ofFinite R9
  let Tin (a b : ℕ) : ℕ :=
    C0 * ((IntMulTM.encNatPair.encode (a, b)).length + 1) +
      C0 * ((WP.W0m.lam a b + 1) * (WP.W0m.lam a b + 1))
  let σ0 : WP.Top.TopRegs σi R7 Rc R9 :=
    (Classical.choice hni, Classical.choice hn7, Classical.choice hnc, Classical.choice hn9, none)
  have htop := fun a b =>
    top_subNLogN_triple hm7 hmc hm9 hin hspec7 hspecc hspec9 σ0 a b
  obtain ⟨cS, hcS⟩ := Classical.skolem.mp (fun a => Classical.skolem.mp (htop a))
  let f (a b : ℕ) : ℕ :=
    Tin a b + (WP.Top.tabCost C7 (operandBits a b) (cS a b) + (WP.Top.convCost Cc (cS a b) +
      (WP.Top.glueCost (operandBits a b) + (T9 a b (cS a b) +
        WP.Top.outCost (bitLen (a * b))
          (WP.Top.totalSize (WP.Top.w9Out (operandBits a b) a b (cS a b) (a * b)))))))
  let KA : ℕ := WP.Top.auxα C7 Cp Ct Cc C9 * 2 ^ 41 + WP.Top.auxβ C7 + WP.Top.auxγ C7 Cc C9
  let KO : ℕ := 152 * (Cc * Ct) * 2 ^ 41 + 3064 + (152 * Cc + 6708)
  let Klin : ℕ := 580 * C0 + KA + KO + 1
  let g (n : ℕ) : ℕ := g9 n + Klin * n
  let Ncut : ℕ := max (max Np Nt) N9
  have hN9_2 : 2 ≤ N9 := hg9.2.2.1
  have hNcut_2 : 2 ≤ Ncut := le_trans hN9_2 (le_max_right _ _)
  have hgH : HeadlineCost g (2 * (Cg + (Klin + 1))) Ncut :=
    (hg9.add_linear Klin).of_le (le_max_right _ _)
  have hfg : ∀ a b, Ncut ≤ operandBits a b → f a b ≤ g (operandBits a b) := by
    intro a b hN
    set n := operandBits a b with hn_def
    have hNp : Np ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hNt : Nt ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN9 : N9 ≤ n := le_trans (le_max_right _ _) hN
    have hn2 : 2 ≤ n := le_trans hNcut_2 hN
    have hn1 : 1 ≤ n := by omega
    have hj := (hcS a b).1
    have hP : (W8.hSpec n).precomputeSeriesTableCost ≤ Cp * WP.Top.sqP n := by
      have h := hCp n hNp
      unfold WP.Top.sqP
      rw [← Nat.mul_assoc]
      exact h
    have hT7 : (W7.tape W7.snapshotSchedule.toTapeFormat (cS a b)).length ≤ Ct * WP.Top.sqP n := by
      have h1 := hj.size
      have h2 := hCt n hNt (cS a b) hj.canonical hj.faithful
      have h3 : (Nat.log2 n + 1) ^ 3 ≤ (Nat.log2 n + 1) ^ 8 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : Ct * (Nat.sqrt n + 1) * (Nat.log2 n + 1) ^ 3 ≤ Ct * WP.Top.sqP n := by
        unfold WP.Top.sqP
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      exact le_trans h1 (le_trans h2 h4)
    have hTS := (hspecc n (cS a b)
      (fun _ => W7.tape W7.snapshotSchedule.toTapeFormat (cS a b)) hj rfl).1
    have h_in : Tin a b ≤ 580 * C0 * n :=
      le_trans (WP.Top.tin_le C0 a b) (inCostN_le_linear C0 n hn1)
    have h_aux : WP.Top.tabCost C7 n (cS a b) +
        (WP.Top.convCost Cc (cS a b) +
          (WP.Top.glueCost n + C9 * ((tapeSyms (cS a b)).length + 1))) ≤ KA * n :=
      le_trans (WP.Top.aux_le C7 Cp Ct Cc C9 n hn1 (cS a b) hP hT7 hTS)
        (poly_le_linear _ _ _ n hn2)
    have h_out : WP.Top.outCost (bitLen (a * b))
        (WP.Top.totalSize (WP.Top.w9Out n a b (cS a b) (a * b))) ≤ KO * n :=
      le_trans (WP.Top.out_le Cc Ct a b (cS a b) hT7 hTS)
        (poly_le_linear _ _ _ n hn2)
    have h_T9 : T9 a b (cS a b) ≤ g9 n + C9 * ((tapeSyms (cS a b)).length + 1) :=
      hbound9 a b (cS a b) hN9 hj
    dsimp only [f, g, Klin]
    rw [← hn_def]
    calc Tin a b + (WP.Top.tabCost C7 n (cS a b) + (WP.Top.convCost Cc (cS a b) +
          (WP.Top.glueCost n + (T9 a b (cS a b) +
            WP.Top.outCost (bitLen (a * b))
              (WP.Top.totalSize (WP.Top.w9Out n a b (cS a b) (a * b)))))))
        ≤ Tin a b + (WP.Top.tabCost C7 n (cS a b) + (WP.Top.convCost Cc (cS a b) +
          (WP.Top.glueCost n + ((g9 n + C9 * ((tapeSyms (cS a b)).length + 1)) +
            WP.Top.outCost (bitLen (a * b))
              (WP.Top.totalSize (WP.Top.w9Out n a b (cS a b) (a * b))))))) :=
          Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
            (Nat.add_le_add_left (Nat.add_le_add_right h_T9 _) _) _) _) _
      _ = g9 n + Tin a b +
            (WP.Top.tabCost C7 n (cS a b) + (WP.Top.convCost Cc (cS a b) +
              (WP.Top.glueCost n + C9 * ((tapeSyms (cS a b)).length + 1)))) +
            WP.Top.outCost (bitLen (a * b))
              (WP.Top.totalSize (WP.Top.w9Out n a b (cS a b) (a * b))) := by ring
      _ ≤ g9 n + 580 * C0 * n + KA * n + KO * n :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl h_in) h_aux) h_out
      _ = g9 n + (580 * C0 + KA + KO) * n := by ring
      _ ≤ g9 n + (580 * C0 + KA + KO + 1) * n :=
          Nat.add_le_add_left (Nat.mul_le_mul_right n (by omega)) _
  obtain ⟨C', N', hC', hSup⟩ :=
    eventually_supCost_subNLogN f g Ncut (2 * (Cg + (Klin + 1))) hgH.1 hfg hgH.2.2.2
  let Ptop := WP.Top.topProg Pin P7 hm7 Pc hmc P9 hm9
  have hEval : ∀ p : ℕ × ℕ, ∃ v t,
      Eval [] Ptop ⟨σ0, inputStk (IntMulTM.encNatPair.encode p)⟩
        ⟨v, outputStk (encodeNat (p.1 * p.2))⟩ t ∧
      t ≤ WP.Top.supCost f (IntMulTM.encNatPair.encode p).length := by
    intro p
    have htr := (hcS p.1 p.2).2.cost_mono
      (WP.Top.le_supCost f (WP.Top.lt_two_pow_enc_left p.1 p.2)
        (WP.Top.lt_two_pow_enc_right p.1 p.2))
    obtain ⟨s', t, he, hq, ht⟩ := htr _ rfl
    refine ⟨s'.var, t, ?_, ht⟩
    rw [← hq]
    exact he
  exact transport_TM2_subNLogN
    ⟨TMFw.acceptTM IntMulTM.encNatPair (fun p => p.1 * p.2) Ptop σ0 (WP.Top.supCost f) hEval,
      TMFw.acceptTM_finite, C', N', hC', hSup⟩

/-- **6-stage assembly from `W9SubNLogNSpec` (`headline_46_of_w9_subNLogN`, 0 `sorry`):**
Corollary of `headline_46_of_w9_subNLogN'` and `w9SubNLogNSpec'_of_w9SubNLogNSpec`. -/
theorem headline_46_of_w9_subNLogN (hW9 : W9SubNLogNSpec) :
    Headline_TM2_SubNLogN_46 :=
  headline_46_of_w9_subNLogN' (w9SubNLogNSpec'_of_w9SubNLogNSpec hW9)

/-! ## Stage-5 Root Composite Reduction (`WP.W9mp.multProg`) to `W9PipeSubNLogNSpec'` -/

/-- **`O(n √(log₂ n))` satisfies the `14/15` power bound (`sqrt_pow15_le`, 0 `sorry`):**
`(K * n * (⌊√(128 log₂ n)⌋ + 1))^15 ≤ (256 * K * n)^15 * (log₂ n)^14` for `n ≥ 2`; this is
`sqrtLog_pow15_le` from `S5/HeadlineCost.lean`. -/
theorem sqrt_pow15_le (K n : ℕ) (hn : 2 ≤ n) :
    (K * n * (Nat.sqrt (128 * Nat.log2 n) + 1)) ^ 15 ≤
      ((256 * K) * n) ^ 15 * (Nat.log2 n) ^ 14 :=
  sqrtLog_pow15_le K n hn

/-- **`rootBound` at `T3 c0 c1 w0` and `wRHead n` is `O(n √(log₂ n))` (`rootBound_T3_le`, 0 `sorry`).** -/
theorem rootBound_T3_le (c0 c1 w0 : ℕ) :
    ∃ Kroot : ℕ, ∀ n ≥ 2,
      rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) ≤
        Kroot * n * (Nat.sqrt (128 * Nat.log2 n) + 1) := by
  obtain ⟨CM, hCM⟩ := WP.W5.W5_T3_bound_holds c0 c1 w0
  refine ⟨13800 + 8192 * CM, fun n hn => ?_⟩
  have hlog : 1 ≤ Nat.log2 n := WP.Top.log2_pos hn
  have hwR_le : ∀ m, WP.W11b.wRHead m ≤ 64 * (Nat.log2 m + 1) := fun m => by
    have := WP.W11b.wRHead_le m
    omega
  have hlin := WP.W10b.rootLin_le 64 WP.W11b.wRHead hwR_le hn
  have hwR4 : 4 ≤ WP.W11b.wRHead n := by
    have : WP.W11b.wRHead n = 4 * (2 * W8.hB n + 2 * W8.hK0 n + 6) := rfl
    omega
  have hlogw : 1 ≤ Nat.log2 (WP.W11b.wRHead n) := WP.Top.log2_pos (by omega)
  have hT3 : T3 c0 c1 w0 (WP.W11b.wRHead n) ≤
      CM * (WP.W11b.wRHead n * Nat.sqrt (WP.W11b.wRHead n)) :=
    le_trans (Nat.le_mul_of_pos_right _ hlogw) (hCM (WP.W11b.wRHead n) hwR4)
  have hEl := WP.W10b.E_mul_le hn
  have hEw : 2 ^ W8.hK0 n * WP.W11b.wRHead n ≤ 2048 * n := by
    calc 2 ^ W8.hK0 n * WP.W11b.wRHead n
        ≤ 2 ^ W8.hK0 n * (64 * (Nat.log2 n + 1)) := Nat.mul_le_mul_left _ (hwR_le n)
      _ = 64 * (2 ^ W8.hK0 n * (Nat.log2 n + 1)) := by ring
      _ ≤ 64 * (32 * n) := Nat.mul_le_mul_left 64 hEl
      _ = 2048 * n := by ring
  have hsqw : Nat.sqrt (WP.W11b.wRHead n) ≤ Nat.sqrt (128 * Nat.log2 n) := by
    apply Nat.sqrt_le_sqrt
    have := hwR_le n
    omega
  have hmul : 4 * 2 ^ W8.hK0 n * T3 c0 c1 w0 (WP.W11b.wRHead n) ≤
      (8192 * CM) * n * Nat.sqrt (128 * Nat.log2 n) := by
    calc 4 * 2 ^ W8.hK0 n * T3 c0 c1 w0 (WP.W11b.wRHead n)
        ≤ 4 * 2 ^ W8.hK0 n * (CM * (WP.W11b.wRHead n * Nat.sqrt (WP.W11b.wRHead n))) :=
          Nat.mul_le_mul_left _ hT3
      _ = 4 * CM * (2 ^ W8.hK0 n * WP.W11b.wRHead n) * Nat.sqrt (WP.W11b.wRHead n) := by ring
      _ ≤ 4 * CM * (2048 * n) * Nat.sqrt (128 * Nat.log2 n) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hEw) hsqw
      _ = (8192 * CM) * n * Nat.sqrt (128 * Nat.log2 n) := by ring
  rw [WP.W10b.rootBound_split]
  calc rootBound WP.W10b.mul0 (WP.W11b.wRHead n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
        4 * 2 ^ W8.hK0 n * T3 c0 c1 w0 (WP.W11b.wRHead n)
      ≤ 13800 * n + (8192 * CM) * n * Nat.sqrt (128 * Nat.log2 n) :=
        Nat.add_le_add hlin hmul
    _ ≤ (13800 + 8192 * CM) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) := by
        have : (13800 + 8192 * CM) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) =
          13800 * n + (8192 * CM) * n * Nat.sqrt (128 * Nat.log2 n) +
            (13800 * n * Nat.sqrt (128 * Nat.log2 n) + 8192 * CM * n) := by ring
        omega

/-- **Root invariant for a transform map `F` (`RootOKSubNLogN`):**
`F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ)` (precision, spec,
input ↦ output) is an arbitrary transform map (the Walsh-bridge multiplier discharges Stage 5 on
the extended-stack path in `SubNLogN/Assembly/`). (`IntMul.computablePaperFastDFT` satisfies the invariant at the headline
root parameters, `rootOKSubNLogN_computablePaperFastDFT`.) With `x0 = rootPackV b K0 k1 k2 A1 A2`,
`yF = F b cSpec x0`, `p0 = IntMul.rootPrecision b K0`, `x1 = rootSquareV p0 K0 yF` and
`yI = F p0 cSpec x1`, it states: `ChainOK (fun _ => wd) cSpec b 0 [x0]` and
`ChainOK (fun _ => wd) cSpec p0 0 [x1]`; `yF.size = 2 ^ K0` and `yI.size = 2 ^ K0`; `x0`, `yF`,
`x1`, `yI` have width `≤ wR` (`ArrW wR`); every entry of `rootDigits b K0 k1 k2 yI` has
`bitLen ≤ wR`; and `IntMul.reconstructChunksTree b (rootDigits b K0 k1 k2 yI) = A1 * A2`. -/
def RootOKSubNLogN
    (F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (b K0 k1 k2 A1 A2 wd wR : ℕ) : Prop :=
  let x0 := rootPackV b K0 k1 k2 A1 A2
  let yF := F b cSpec x0
  let p0 := IntMul.rootPrecision b K0
  let x1 := rootSquareV p0 K0 yF
  let yI := F p0 cSpec x1
  ChainOK (fun _ => wd) cSpec b 0 [x0] ∧
  ChainOK (fun _ => wd) cSpec p0 0 [x1] ∧
  ArrW wR x0 ∧
  yF.size = 2 ^ K0 ∧
  ArrW wR yF ∧
  ArrW wR x1 ∧
  yI.size = 2 ^ K0 ∧
  ArrW wR yI ∧
  (∀ c ∈ rootDigits b K0 k1 k2 yI, bitLen c ≤ wR) ∧
  IntMul.reconstructChunksTree b (rootDigits b K0 k1 k2 yI) = A1 * A2

/-- **Non-vacuity of `RootOKSubNLogN` (`rootOKSubNLogN_computablePaperFastDFT`, 0 `sorry`):**
`IntMul.computablePaperFastDFT` satisfies `RootOKSubNLogN` at the headline root parameters for all
`a, b` and `cSpec` with `WP.Top.Joint (operandBits a b) cSpec`. -/
theorem rootOKSubNLogN_computablePaperFastDFT (a b : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) (hj : WP.Top.Joint (operandBits a b) cSpec) :
    RootOKSubNLogN IntMul.computablePaperFastDFT cSpec
      (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
      (W8.hK (operandBits a b)) (W8.hK (operandBits a b))
      a b (WP.W11b.wdHead (operandBits a b)) (WP.W11b.wRHead (operandBits a b)) := by
  obtain ⟨hA, hB, -, -⟩ := input_bridge a b
  obtain ⟨hcF, hcI, hfs, hw0, hwF, hwQ, his, hwI, hwD⟩ :=
    WP.W11b.w9RootOK_headline (operandBits a b) a b cSpec (WP.W0m.operandBits_pos a b) hA hB hj
  refine ⟨hcF, hcI, hw0, hfs, hwF, hwQ, his, hwI, hwD, ?_⟩
  have hval := WP.Top.w9_value a b hj
  rw [multiply_eq_root_phases] at hval
  exact hval

/-- **Transform-pipeline program contract (`SpecPipeSubNLogN F Tp m1 R1 Pp`):**
For an arbitrary transform map `F` (quantified over any root-compatible transform; Stage 5 uses
`W9SubNLogNSpecX` in `SubNLogN/Assembly/`): whenever `WP.Top.Joint n cSpec`, the input `x` satisfies
`ChainOK (fun _ => WP.W11b.wdHead n) cSpec p_in 0 [x]`, `x.size = 2 ^ W8.hK0 n` and
`ArrW (WP.W11b.wRHead n) x`, the precision `p_in` is `W8.hB n` or
`IntMul.rootPrecision (W8.hB n) (W8.hK0 n)`, `.S` holds `streamSyms [x] ++ restS`, `.W0` is empty,
`.TR` holds `tapeSyms cSpec ++ restT` (with `restT.head? ≠ some symPost`) and `.C1` holds
`hdrSyms [p_in] ++ r1`, the program `Pp` replaces `.S` by `streamSyms [F p_in cSpec x] ++ restS`,
leaving all other stacks unchanged, within `Tp n cSpec` steps. -/
def SpecPipeSubNLogN
    (F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ) (m1 : ℕ) (R1 : Type)
    (Pp : Prog (BLoc m1) (fun _ => Sym) R1) : Prop :=
  ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ))
    (σ : BLoc m1 → List Sym) (restS restT r1 : List Sym),
    WP.Top.Joint n cSpec →
    ChainOK (fun _ => WP.W11b.wdHead n) cSpec p_in 0 [x] →
    x.size = 2 ^ W8.hK0 n →
    ArrW (WP.W11b.wRHead n) x →
    (p_in = W8.hB n ∨ p_in = IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) →
    σ (.inl .S) = streamSyms [x] ++ restS →
    σ (.inl .W0) = [] →
    σ (.inl .TR) = tapeSyms cSpec ++ restT →
    restT.head? ≠ some symPost →
    σ (.inl .C1) = hdrSyms [p_in] ++ r1 →
    Runs Pp σ
      (Function.update σ (.inl .S)
        (streamSyms [F p_in cSpec x] ++ restS))
      (fun _ => True)
      (Tp n cSpec)

/-- Step lemma for `Pp` inside `WP.W9mp.multProg` (`st_pipe_subNLogN`, 0 `sorry`). -/
theorem st_pipe_subNLogN
    {F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ)}
    {Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ} {m m1 : ℕ} {R1 τ : Type}
    {Pp : Prog (BLoc m1) (fun _ => Sym) R1}
    (s : SpecPipeSubNLogN F Tp m1 R1 Pp) (hm : m1 ≤ m) (l : Lens τ R1)
    (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (p_in : ℕ) (x : Array (ℤ × ℤ))
    (S : BLoc m → List Sym) (restS restT r1 : List Sym)
    (hj : WP.Top.Joint n cSpec)
    (hc : ChainOK (fun _ => WP.W11b.wdHead n) cSpec p_in 0 [x])
    (hsz : x.size = 2 ^ W8.hK0 n)
    (hwx : ArrW (WP.W11b.wRHead n) x)
    (hp : p_in = W8.hB n ∨ p_in = IntMul.rootPrecision (W8.hB n) (W8.hK0 n))
    (hS : S (.inl .S) = streamSyms [x] ++ restS)
    (hW0 : S (.inl .W0) = [])
    (hTR : S (.inl .TR) = tapeSyms cSpec ++ restT)
    (hrT : restT.head? ≠ some symPost)
    (hC1 : S (.inl .C1) = hdrSyms [p_in] ++ r1) :
    Runs (WP.W9comp.callB hm l Pp) S
      (Function.update S (.inl .S)
        (streamSyms [F p_in cSpec x] ++ restS))
      (fun _ => True)
      (1 * (Tp n cSpec + (tapeSyms cSpec).length + 1)) := by
  have hrun := s n cSpec p_in x (S ∘ WP.W9comp.emb hm) restS restT r1 hj hc hsz hwx hp hS hW0 hTR hrT hC1
  rw [WP.W9comp.upd_comp_emb] at hrun
  exact WP.W9comp.runs_mono (WP.W9comp.runs_callB hm l hrun fun j => by simp)
    (fun _ _ => trivial) (by omega)

attribute [local instance 10000] IntMul.instZeroIntElementary in
/-- **Root Composite Theorem (`multProg_subNLogN_runs`, 0 `sorry`):**
Composes `Ps` (`SpecSplit`), `pushB`, `Pp` (`SpecPipeSubNLogN`, forward), `dropTo`,
`Pq` (`SpecSquare`), `pushP0`, `Pp` (`SpecPipeSubNLogN`, inverse), `dropTo`,
`Pe` (`SpecExtract`), and `Pr` (`SpecRecon`) into `WP.W9mp.multProg`, using `RootOKSubNLogN F`
to establish `OA = natSyms (A1 * A2) ++ rA`. -/
theorem multProg_subNLogN_runs
    {F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ)}
    {Mul : ℕ → ℕ} {Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ}
    {m m1 m2 m3 m4 m5 : ℕ} {R1 R2 R3 R4 R5 : Type}
    {Cs Cq Ce Cr : ℕ} (h1 : m1 ≤ m) (h2 : m2 ≤ m) (h3 : m3 ≤ m) (h4 : m4 ≤ m) (h5 : m5 ≤ m)
    (hx : 3 ≤ m)
    {Pp : Prog (BLoc m1) (fun _ => Sym) R1} {Ps : Prog (BLoc m2) (fun _ => Sym) R2}
    {Pq : Prog (BLoc m3) (fun _ => Sym) R3} {Pe : Prog (BLoc m4) (fun _ => Sym) R4}
    {Pr : Prog (BLoc m5) (fun _ => Sym) R5}
    (sP : SpecPipeSubNLogN F Tp m1 R1 Pp) (sS : WP.W9mp.SpecSplit m2 R2 Cs Ps)
    (sQ : WP.W9mp.SpecSquare Mul m3 R3 Cq Pq) (sE : WP.W9mp.SpecExtract m4 R4 Ce Pe)
    (sR : WP.W9mp.SpecRecon m5 R5 Cr Pr)
    (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (b K0 k1 k2 A1 A2 : ℕ)
    (σ : BLoc m → List Sym) (rA rB r0 restT : List Sym)
    (hj : WP.Top.Joint n cSpec)
    (hb_eq : b = W8.hB n) (hK0_eq : K0 = W8.hK0 n)
    (hA : A1 < 2 ^ (b * k1)) (hB : A2 < 2 ^ (b * k2)) (hk : k1 + k2 ≤ 2 ^ K0)
    (hrA : TermOK rA) (hrB : TermOK rB)
    (hRoot : RootOKSubNLogN F cSpec b K0 k1 k2 A1 A2 (WP.W11b.wdHead n) (WP.W11b.wRHead n))
    (hOA : σ (.inl .OA) = natSyms A1 ++ rA) (hOB : σ (.inl .OB) = natSyms A2 ++ rB)
    (hC0 : σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0) (hW0 : σ (.inl .W0) = [])
    (hTR : σ (.inl .TR) = tapeSyms cSpec ++ restT) (hrT : restT.head? ≠ some symPost) :
    Runs (WP.W9mp.multProg h1 h2 h3 h4 h5 hx Pp Ps Pq Pe Pr) σ
      (Function.update (Function.update σ (.inl .OA)
          (natSyms (A1 * A2) ++ rA))
        (.inl .OB) rB)
      (fun _ => True)
      ((Cs + 2 * 1 + Cq + Ce + Cr + 200) *
        (rootBound Mul (WP.W11b.wRHead n) b K0 k1 k2 + Tp n cSpec + Tp n cSpec +
          (tapeSyms cSpec).length + 1)) := by
  obtain ⟨hcF, hcI, hw0, hfs, hwF, hwQ, his, hwI, hwD, hrec⟩ := hRoot
  have hx0_sz : (rootPackV b K0 k1 k2 A1 A2).size = 2 ^ W8.hK0 n := by
    rw [WP.W11b.size_rootPackV, hK0_eq]
  have hx1_sz :
      (rootSquareV (IntMul.rootPrecision b K0) K0
        (F b cSpec (rootPackV b K0 k1 k2 A1 A2))).size = 2 ^ W8.hK0 n := by
    rw [WP.W11b.size_rootSquareV, hK0_eq]
  have hpF : b = W8.hB n ∨ b = IntMul.rootPrecision (W8.hB n) (W8.hK0 n) :=
    Or.inl hb_eq
  have hpI :
      IntMul.rootPrecision b K0 = W8.hB n ∨
      IntMul.rootPrecision b K0 = IntMul.rootPrecision (W8.hB n) (W8.hK0 n) :=
    Or.inr (by rw [hb_eq, hK0_eq])
  rw [← hrec]
  have chain :=
    WP.W9comp.runs_seq (WP.W9mp.st_split sS h2 (WP.W9mp.mlS R1 R2 R3 R4 R5) b K0 k1 k2 A1 A2 σ rA rB r0
      hA hB hk hrA hrB hOA hOB hC0) <|
    WP.W9comp.runs_seq (WP.W9mp.runs_liftRegs (WP.W9mp.mlg R1 R2 R3 R4 R5) (WP.W9mp.runs_pushB_m hx b
      (.mark :: (hdrSyms [K0, k1, k2] ++ r0)) _ (WP.W9mp.termOK_mark _)
      (by simp [hC0, WP.W9mp.hdrSyms_cons]))) <|
    WP.W9comp.runs_seq (st_pipe_subNLogN sP h1 (WP.W9mp.mlP R1 R2 R3 R4 R5) n cSpec b _ _
      (σ (.inl .S)) restT (σ (.inl .C1)) hj hcF hx0_sz hw0 hpF (by simp) (by simp [hW0]) (by simp [hTR]) hrT
      (by simp)) <|
    WP.W9comp.runs_seq (WP.W9mp.runs_liftRegs (WP.W9mp.mlg R1 R2 R3 R4 R5)
      (WP.W9mp.runs_popHdr (K := BLoc m) (.inl .C1) b (σ (.inl .C1)) _ (by simp))) <|
    WP.W9comp.runs_seq (WP.W9mp.st_square sQ h3 (WP.W9mp.mlQ R1 R2 R3 R4 R5) b K0 k1 k2
      (WP.W11b.wRHead n) _ _ (σ (.inl .S)) r0 hfs hwF hwQ (by simp [hC0]) (by simp)) <|
    WP.W9comp.runs_seq (WP.W9mp.runs_liftRegs (WP.W9mp.mlg R1 R2 R3 R4 R5)
      (WP.W9mp.runs_pushP0_m hx b K0 (hdrSyms [k1, k2] ++ r0) _
        (by simp [hC0, WP.W9mp.hdrSyms_cons]))) <|
    WP.W9comp.runs_seq (st_pipe_subNLogN sP h1 (WP.W9mp.mlP R1 R2 R3 R4 R5) n cSpec
      (IntMul.rootPrecision b K0) _ _ (σ (.inl .S)) restT (σ (.inl .C1)) hj hcI hx1_sz hwQ hpI (by simp)
      (by simp [hW0]) (by simp [hTR]) hrT (by simp)) <|
    WP.W9comp.runs_seq (WP.W9mp.runs_liftRegs (WP.W9mp.mlg R1 R2 R3 R4 R5)
      (WP.W9mp.runs_popHdr (K := BLoc m) (.inl .C1) (IntMul.rootPrecision b K0) (σ (.inl .C1)) _
        (by simp))) <|
    WP.W9comp.runs_seq (WP.W9mp.st_extract sE h4 (WP.W9mp.mlE R1 R2 R3 R4 R5) b K0 k1 k2
      (WP.W11b.wRHead n) _ _ (σ (.inl .S)) r0 his hk hwI (by simp [hC0]) (by simp)) <|
    WP.W9mp.st_recon sR h5 (WP.W9mp.mlR R1 R2 R3 R4 R5) b K0 k1 k2 (WP.W11b.wRHead n) _ _ rA r0
      (by simp [rootDigits]) hk hwD hrA (by simp [hC0]) (by simp)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr chain ?_) (fun _ _ => trivial)
    (WP.W9mp.multCost_le Mul (WP.W11b.wRHead n) b K0 k1 k2 _ _ _ Cs 1 Cq Ce Cr hk)
  funext k
  rcases k with k | j
  · cases k <;> simp
  · simp

/-- **Transform-pipeline Stage-5 contract, per-stage version (`W9PipeSubNLogNSpec`):**
Existence of a transform map `F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ)`
(arbitrary: `F` is existentially quantified over any root-compatible transform; see
`SubNLogN/Assembly/`) and a closed `BLoc m1` program `Pp` (`m1 ≤ 64`) over a finite nonempty
register type `R1` such that `RootOKSubNLogN F` holds at the headline root parameters whenever
`WP.Top.Joint (operandBits a b) cSpec`, `SpecPipeSubNLogN F Tp m1 R1 Pp` holds, and for `N9 ≤ n`
with `WP.Top.Joint n cSpec`, `Tp n cSpec ≤ c.total n + Cp * ((tapeSyms cSpec).length + 1)` for a
6-stage schedule `c` with `Monotone c.total` and `SubNLogNStageBounds c A N9`. The per-stage
bounds (every stage `≤ A * n * (log₂ n)^(14/15)`) are a stronger sufficient condition that the
paper's algorithm does not meet. This contract implies the headline-shaped
`W9PipeSubNLogNSpec'` (`w9PipeSubNLogNSpec'_of_w9PipeSubNLogNSpec`). -/
def W9PipeSubNLogNSpec : Prop :=
  ∃ (F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (m1 : ℕ) (R1 : Type) (Pp : Prog (BLoc m1) (fun _ => Sym) R1)
    (_hm1 : m1 ≤ 64) (_ : Finite R1) (_ : Nonempty R1)
    (Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ)
    (Cp : ℕ) (c : SubNLogNStageCosts) (A N9 : ℕ),
    Pp.Closed ∧
    Monotone c.total ∧
    SubNLogNStageBounds c A N9 ∧
    (∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      WP.Top.Joint (operandBits a b) cSpec →
      RootOKSubNLogN F cSpec
        (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
        (W8.hK (operandBits a b)) (W8.hK (operandBits a b))
        a b (WP.W11b.wdHead (operandBits a b)) (WP.W11b.wRHead (operandBits a b))) ∧
    SpecPipeSubNLogN F Tp m1 R1 Pp ∧
    (∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      N9 ≤ n →
      WP.Top.Joint n cSpec →
      Tp n cSpec ≤ c.total n + Cp * ((tapeSyms cSpec).length + 1))

/-- **Transform-pipeline Stage-5 contract, headline-shaped version (`W9PipeSubNLogNSpec'`):**
Existence of a transform map `F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ)`
(arbitrary: `F` is existentially quantified over any root-compatible transform; see
`SubNLogN/Assembly/`) and a closed `BLoc m1` program `Pp` (`m1 ≤ 64`) over a finite nonempty
register type `R1` such that `RootOKSubNLogN F` holds at the headline root parameters whenever
`WP.Top.Joint (operandBits a b) cSpec`, `SpecPipeSubNLogN F Tp m1 R1 Pp` holds, and for `N9 ≤ n`
with `WP.Top.Joint n cSpec`, `Tp n cSpec ≤ g n + Cp * ((tapeSyms cSpec).length + 1)` for some
function `g` with `HeadlineCost g C N9` (no split of the cost into stages is prescribed).
It implies `W9SubNLogNSpec'` (`w9SubNLogNSpec'_of_pipe'`). -/
def W9PipeSubNLogNSpec' : Prop :=
  ∃ (F : ℕ → IntMul.ComputablePaperFastDFTSpec → Array (ℤ × ℤ) → Array (ℤ × ℤ))
    (m1 : ℕ) (R1 : Type) (Pp : Prog (BLoc m1) (fun _ => Sym) R1)
    (_hm1 : m1 ≤ 64) (_ : Finite R1) (_ : Nonempty R1)
    (Tp : ℕ → IntMul.ComputablePaperFastDFTSpec → ℕ)
    (Cp : ℕ) (g : ℕ → ℕ) (C N9 : ℕ),
    Pp.Closed ∧
    HeadlineCost g C N9 ∧
    (∀ (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      WP.Top.Joint (operandBits a b) cSpec →
      RootOKSubNLogN F cSpec
        (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
        (W8.hK (operandBits a b)) (W8.hK (operandBits a b))
        a b (WP.W11b.wdHead (operandBits a b)) (WP.W11b.wRHead (operandBits a b))) ∧
    SpecPipeSubNLogN F Tp m1 R1 Pp ∧
    (∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec),
      N9 ≤ n →
      WP.Top.Joint n cSpec →
      Tp n cSpec ≤ g n + Cp * ((tapeSyms cSpec).length + 1))

/-- `W9PipeSubNLogNSpec` implies `W9PipeSubNLogNSpec'` (take `g = c.total`, by
`headlineCost_of_stageBounds`; 0 `sorry`). -/
theorem w9PipeSubNLogNSpec'_of_w9PipeSubNLogNSpec (h : W9PipeSubNLogNSpec) :
    W9PipeSubNLogNSpec' := by
  obtain ⟨F, m1, R1, Pp, hm1, hf1, hn1, Tp, Cp, c, A, N9, hc1, hmono, hb, hRootF, sP, hTp⟩ := h
  obtain ⟨C, hC⟩ := headlineCost_of_stageBounds c A N9 hmono hb
  exact ⟨F, m1, R1, Pp, hm1, hf1, hn1, Tp, Cp, c.total, C, N9, hc1, hC, hRootF, sP, hTp⟩

/-- **Reduction from `W9SubNLogNSpec` to `W9PipeSubNLogNSpec` (`w9SubNLogNSpec_of_pipe`, 0 `sorry`):**
Instantiates `WP.W9mp.multProg` with `Pp` (`W9PipeSubNLogNSpec`) and the four proved root stages
(`WP.W9sp.W9_splitPack_holds`, `WP.W9sq.W9_square_holds`, `WP.W9ex.W9_extract_proved`,
`WP.W9h.W9_reconstruct_holds`), and absorbs the `O(n √(log₂ n))` root bound into `c.pre`. -/
theorem w9SubNLogNSpec_of_pipe (hPipe : W9PipeSubNLogNSpec) :
    W9SubNLogNSpec := by
  have h5 : W5_toom3Mul := WP.W5.W5_toom3Mul_holds
    (TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
    (TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
    TMFw.W3b.W3_smallOpInt_holds TMFw.W3s.W3_splitAt_holds TMFw.W3s.W3_shlVar_holds
  obtain ⟨c0, c1, w0, hmul⟩ := W5_toom3Mul_iff_mulAt.mp h5
  obtain ⟨Kroot, hKroot⟩ := rootBound_T3_le c0 c1 w0
  obtain ⟨F, m1, R1, Pp, hm1, hf1, hn1, Tp, Cp, c, A, N9, hc1, hmono, hb, hRootF, sP, hTp⟩ := hPipe
  obtain ⟨Cs, kS⟩ := WP.W9sp.W9_splitPack_holds WP.Top.W3_all_holds
  obtain ⟨Cq, kQ⟩ := WP.W9sq.W9_square_holds (T3 c0 c1 w0) hmul WP.Top.W3_all_holds
  obtain ⟨Ce, kE⟩ := WP.W9ex.W9_extract_proved
  obtain ⟨Cr, kR⟩ := WP.W9h.W9_reconstruct_holds WP.Top.W3_all_holds
  obtain ⟨m2, R2, Ps, hm2, hf2, hn2, hc2, sS⟩ := kS ()
  obtain ⟨m3, R3, Pq, hm3, hf3, hn3, hc3, sQ⟩ := kQ ()
  obtain ⟨m4, R4, Pe, hm4, hf4, hn4, hc4, sE⟩ := kE ()
  obtain ⟨m5, R5, Pr, hm5, hf5, hn5, hc5, sR⟩ := kR ()
  have _ := hf1; have _ := hf2; have _ := hf3; have _ := hf4; have _ := hf5
  have _ := hn1; have _ := hn2; have _ := hn3; have _ := hn4; have _ := hn5
  have h64 : w9Scratch = 64 := rfl
  let m9 : ℕ := max (max m1 (max m2 (max m3 (max m4 m5)))) 3
  have hm9 : m9 ≤ 64 := by dsimp [m9]; omega
  have e1 : m1 ≤ m9 := by dsimp [m9]; omega
  have e2 : m2 ≤ m9 := by dsimp [m9]; omega
  have e3 : m3 ≤ m9 := by dsimp [m9]; omega
  have e4 : m4 ≤ m9 := by dsimp [m9]; omega
  have e5 : m5 ≤ m9 := by dsimp [m9]; omega
  have ex : 3 ≤ m9 := by dsimp [m9]; omega
  let R9 := WP.W9mp.MRegs R1 R2 R3 R4 R5
  let P9 := WP.W9mp.multProg e1 e2 e3 e4 e5 ex Pp Ps Pq Pe Pr
  let C9_base : ℕ := Cs + 2 * 1 + Cq + Ce + Cr + 200
  let C9 : ℕ := C9_base * (2 * Cp + 1)
  let T9 (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) : ℕ :=
    C9_base * (rootBound (T3 c0 c1 w0) (WP.W11b.wRHead (operandBits a b))
      (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
      (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) +
      Tp (operandBits a b) cSpec + Tp (operandBits a b) cSpec +
      (tapeSyms cSpec).length + 1)
  let K9 : ℕ := C9_base * Kroot + 1
  let c' : SubNLogNStageCosts :=
    { pre := fun n => 2 * C9_base * c.pre n + K9 * n * (Nat.sqrt (128 * Nat.log2 n) + 1)
      spread := fun n => 2 * C9_base * c.spread n
      solve := fun n => 2 * C9_base * c.solve n
      tw := fun n => 2 * C9_base * c.tw n
      last := fun n => 2 * C9_base * c.last n
      fft := fun n => 2 * C9_base * c.fft n }
  have hc'_total : ∀ n, c'.total n =
      2 * C9_base * c.total n + K9 * n * (Nat.sqrt (128 * Nat.log2 n) + 1) := by
    intro n
    dsimp [c', SubNLogNStageCosts.total]
    ring
  have hc'_mono : Monotone c'.total := by
    intro x y hxy
    rw [hc'_total x, hc'_total y]
    have hlog_xy : Nat.log2 x ≤ Nat.log2 y := IntMul.nat_log2_mono hxy
    have hsq_xy : Nat.sqrt (128 * Nat.log2 x) + 1 ≤ Nat.sqrt (128 * Nat.log2 y) + 1 :=
      Nat.add_le_add_right (Nat.sqrt_le_sqrt (Nat.mul_le_mul_left 128 hlog_xy)) 1
    exact Nat.add_le_add
      (Nat.mul_le_mul_left (2 * C9_base) (hmono hxy))
      (Nat.mul_le_mul (Nat.mul_le_mul_left K9 hxy) hsq_xy)
  obtain ⟨hA_pos, hN9_2, hpre, hspread, hsolve, htw, hlast, hfft⟩ := hb
  let A' : ℕ := 2 * (2 * C9_base * A + 256 * K9 + 1)
  have hA'_pos : 0 < A' := by dsimp [A']; omega
  have hscale15 : ∀ (f : ℕ → ℕ),
      (∀ L ≥ N9, (f L) ^ 15 ≤ (A * L) ^ 15 * (Nat.log2 L) ^ 14) →
      (∀ L ≥ N9, (2 * C9_base * f L) ^ 15 ≤ (A' * L) ^ 15 * (Nat.log2 L) ^ 14) := by
    intro f hf L hL
    have h1 := hf L hL
    have hle : 2 * C9_base * A ≤ A' := by dsimp [A']; omega
    calc (2 * C9_base * f L) ^ 15
        = (2 * C9_base) ^ 15 * (f L) ^ 15 := mul_pow _ _ _
      _ ≤ (2 * C9_base) ^ 15 * ((A * L) ^ 15 * (Nat.log2 L) ^ 14) := Nat.mul_le_mul_left _ h1
      _ = ((2 * C9_base * A) * L) ^ 15 * (Nat.log2 L) ^ 14 := by
          rw [← mul_assoc, ← mul_pow, ← mul_assoc]
      _ ≤ (A' * L) ^ 15 * (Nat.log2 L) ^ 14 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right L hle) 15)
  have hpre' : ∀ L ≥ N9, (c'.pre L) ^ 15 ≤ (A' * L) ^ 15 * (Nat.log2 L) ^ 14 := by
    intro L hL
    have hL2 : 2 ≤ L := le_trans hN9_2 hL
    set X := 2 * C9_base * c.pre L
    set Y := K9 * L * (Nat.sqrt (128 * Nat.log2 L) + 1)
    have hX : X ^ 15 ≤ ((2 * C9_base * A) * L) ^ 15 * (Nat.log2 L) ^ 14 := by
      calc X ^ 15 = (2 * C9_base) ^ 15 * (c.pre L) ^ 15 := mul_pow _ _ _
        _ ≤ (2 * C9_base) ^ 15 * ((A * L) ^ 15 * (Nat.log2 L) ^ 14) :=
            Nat.mul_le_mul_left _ (hpre L hL)
        _ = ((2 * C9_base * A) * L) ^ 15 * (Nat.log2 L) ^ 14 := by
            rw [← mul_assoc, ← mul_pow, ← mul_assoc]
    have hY : Y ^ 15 ≤ ((256 * K9) * L) ^ 15 * (Nat.log2 L) ^ 14 :=
      sqrt_pow15_le K9 L hL2
    rcases le_total X Y with hXY | hYX
    · have hle : 2 * (256 * K9) ≤ A' := by dsimp [A']; omega
      calc (X + Y) ^ 15 ≤ (2 * Y) ^ 15 := Nat.pow_le_pow_left (by omega) 15
        _ = 2 ^ 15 * Y ^ 15 := mul_pow _ _ _
        _ ≤ 2 ^ 15 * (((256 * K9) * L) ^ 15 * (Nat.log2 L) ^ 14) := Nat.mul_le_mul_left _ hY
        _ = ((2 * (256 * K9)) * L) ^ 15 * (Nat.log2 L) ^ 14 := by
            rw [← mul_assoc, ← mul_pow, ← mul_assoc]
        _ ≤ (A' * L) ^ 15 * (Nat.log2 L) ^ 14 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right L hle) 15)
    · have hle : 2 * (2 * C9_base * A) ≤ A' := by dsimp [A']; omega
      calc (X + Y) ^ 15 ≤ (2 * X) ^ 15 := Nat.pow_le_pow_left (by omega) 15
        _ = 2 ^ 15 * X ^ 15 := mul_pow _ _ _
        _ ≤ 2 ^ 15 * (((2 * C9_base * A) * L) ^ 15 * (Nat.log2 L) ^ 14) := Nat.mul_le_mul_left _ hX
        _ = ((2 * (2 * C9_base * A)) * L) ^ 15 * (Nat.log2 L) ^ 14 := by
            rw [← mul_assoc, ← mul_pow, ← mul_assoc]
        _ ≤ (A' * L) ^ 15 * (Nat.log2 L) ^ 14 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right L hle) 15)
  have hfft' : ∀ L ≥ N9, (c'.fft L) ^ (15 * 2 ^ 50) ≤
      (A' * L) ^ (15 * 2 ^ 50) * (Nat.log2 L) ^ (14 * (2 ^ 50 - 1)) := by
    intro L hL
    have h1 := hfft L hL
    have hle : 2 * C9_base * A ≤ A' := by dsimp [A']; omega
    calc (2 * C9_base * c.fft L) ^ (15 * 2 ^ 50)
        = (2 * C9_base) ^ (15 * 2 ^ 50) * (c.fft L) ^ (15 * 2 ^ 50) := mul_pow _ _ _
      _ ≤ (2 * C9_base) ^ (15 * 2 ^ 50) *
            ((A * L) ^ (15 * 2 ^ 50) * (Nat.log2 L) ^ (14 * (2 ^ 50 - 1))) :=
          Nat.mul_le_mul_left _ h1
      _ = ((2 * C9_base * A) * L) ^ (15 * 2 ^ 50) * (Nat.log2 L) ^ (14 * (2 ^ 50 - 1)) := by
          rw [← mul_assoc, ← mul_pow, ← mul_assoc]
      _ ≤ (A' * L) ^ (15 * 2 ^ 50) * (Nat.log2 L) ^ (14 * (2 ^ 50 - 1)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right L hle) _)
  have hb' : SubNLogNStageBounds c' A' N9 :=
    ⟨hA'_pos, hN9_2, hpre', hscale15 c.spread hspread, hscale15 c.solve hsolve,
      hscale15 c.tw htw, hscale15 c.last hlast, hfft'⟩
  refine ⟨m9, R9, P9, hm9, inferInstance, inferInstance, T9, C9, c', A', N9,
    WP.W9mp.multProg_closed e1 e2 e3 e4 e5 ex hc1 hc2 hc3 hc4 hc5,
    hc'_mono, hb', ?_, ?_⟩
  · intro a b cSpec hj
    obtain ⟨hA, hB, -, -⟩ := input_bridge a b
    exact multProg_subNLogN_runs e1 e2 e3 e4 e5 ex sP sS sQ sE sR
      (operandBits a b) cSpec (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
      (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) a b
      (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l)) [] [] [] []
      hj rfl rfl (WP.Top.lt_pow_bk hA) (WP.Top.lt_pow_bk hB) (WP.Top.headline_kk _)
      TermOK.nil TermOK.nil
      (hRootF a b cSpec hj)
      (by rw [List.append_nil]; exact WP.Top.w9In_oa _ _ _ _)
      (by rw [List.append_nil]; exact WP.Top.w9In_ob _ _ _ _)
      (by rw [List.append_nil]; exact WP.Top.w9In_c0 _ _ _ _)
      (WP.Top.w9In_w0 _ _ _ _)
      (by rw [List.append_nil]; exact WP.Top.w9In_tr _ _ _ _)
      (by simp)
  · intro a b cSpec hN hj
    set n := operandBits a b with hn_def
    have hn2 : 2 ≤ n := le_trans hN9_2 hN
    have hroot : C9_base * rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n)
        (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) ≤
        (C9_base * Kroot) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) := by
      have := Nat.mul_le_mul_left C9_base (hKroot n hn2)
      linarith
    have hTp_le : Tp n cSpec ≤ c.total n + Cp * ((tapeSyms cSpec).length + 1) :=
      hTp n cSpec hN hj
    rw [hc'_total n]
    dsimp only [T9, K9, C9]
    rw [← hn_def]
    calc C9_base * (rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
          Tp n cSpec + Tp n cSpec + (tapeSyms cSpec).length + 1)
        ≤ C9_base * (rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
          (c.total n + Cp * ((tapeSyms cSpec).length + 1)) +
          (c.total n + Cp * ((tapeSyms cSpec).length + 1)) + (tapeSyms cSpec).length + 1) :=
          Nat.mul_le_mul_left C9_base (by omega)
      _ = 2 * C9_base * c.total n +
          C9_base * rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
          C9_base * (2 * Cp + 1) * ((tapeSyms cSpec).length + 1) := by ring
      _ ≤ 2 * C9_base * c.total n +
          (C9_base * Kroot) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) +
          C9_base * (2 * Cp + 1) * ((tapeSyms cSpec).length + 1) :=
          Nat.add_le_add_right (Nat.add_le_add_left hroot _) _
      _ ≤ 2 * C9_base * c.total n +
          (C9_base * Kroot + 1) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) +
          C9_base * (2 * Cp + 1) * ((tapeSyms cSpec).length + 1) := by
          have : (C9_base * Kroot) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) ≤
              (C9_base * Kroot + 1) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right n (by omega))
          omega

/-- **Assembly from `W9PipeSubNLogNSpec` (`headline_46_of_w9_pipe`, 0 `sorry`):**
Immediate corollary of `headline_46_of_w9_subNLogN` and `w9SubNLogNSpec_of_pipe`. -/
theorem headline_46_of_w9_pipe (hPipe : W9PipeSubNLogNSpec) :
    Headline_TM2_SubNLogN_46 :=
  headline_46_of_w9_subNLogN (w9SubNLogNSpec_of_pipe hPipe)

/-- **Reduction of `W9SubNLogNSpec'` to `W9PipeSubNLogNSpec'` (`w9SubNLogNSpec'_of_pipe'`, 0 `sorry`):**
Instantiates `WP.W9mp.multProg` with `Pp` (`W9PipeSubNLogNSpec'`) and the four proved root stages
(`WP.W9sp.W9_splitPack_holds`, `WP.W9sq.W9_square_holds`, `WP.W9ex.W9_extract_proved`,
`WP.W9h.W9_reconstruct_holds`). The Stage-5 cost function is
`g' n = 2 * C9_base * g n + K9 * n * (⌊√(128 log₂ n)⌋ + 1)` (two pipeline calls plus the
`O(n √(log₂ n))` root bound), which satisfies `HeadlineCost` by `HeadlineCost.const_mul` and
`HeadlineCost.add_sqrtLog`. -/
theorem w9SubNLogNSpec'_of_pipe' (h : W9PipeSubNLogNSpec') :
    W9SubNLogNSpec' := by
  have h5 : W5_toom3Mul := WP.W5.W5_toom3Mul_holds
    (TMFw.W3b.W3_addInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
    (TMFw.W3b.W3_subInt_holds WP.W3.W3_addNat_holds WP.W3.W3_subNat_holds)
    TMFw.W3b.W3_smallOpInt_holds TMFw.W3s.W3_splitAt_holds TMFw.W3s.W3_shlVar_holds
  obtain ⟨c0, c1, w0, hmul⟩ := W5_toom3Mul_iff_mulAt.mp h5
  obtain ⟨Kroot, hKroot⟩ := rootBound_T3_le c0 c1 w0
  obtain ⟨F, m1, R1, Pp, hm1, hf1, hn1, Tp, Cp, g, Cg, N9, hc1, hg, hRootF, sP, hTp⟩ := h
  obtain ⟨Cs, kS⟩ := WP.W9sp.W9_splitPack_holds WP.Top.W3_all_holds
  obtain ⟨Cq, kQ⟩ := WP.W9sq.W9_square_holds (T3 c0 c1 w0) hmul WP.Top.W3_all_holds
  obtain ⟨Ce, kE⟩ := WP.W9ex.W9_extract_proved
  obtain ⟨Cr, kR⟩ := WP.W9h.W9_reconstruct_holds WP.Top.W3_all_holds
  obtain ⟨m2, R2, Ps, hm2, hf2, hn2, hc2, sS⟩ := kS ()
  obtain ⟨m3, R3, Pq, hm3, hf3, hn3, hc3, sQ⟩ := kQ ()
  obtain ⟨m4, R4, Pe, hm4, hf4, hn4, hc4, sE⟩ := kE ()
  obtain ⟨m5, R5, Pr, hm5, hf5, hn5, hc5, sR⟩ := kR ()
  have _ := hf1; have _ := hf2; have _ := hf3; have _ := hf4; have _ := hf5
  have _ := hn1; have _ := hn2; have _ := hn3; have _ := hn4; have _ := hn5
  have h64 : w9Scratch = 64 := rfl
  let m9 : ℕ := max (max m1 (max m2 (max m3 (max m4 m5)))) 3
  have hm9 : m9 ≤ 64 := by dsimp [m9]; omega
  have e1 : m1 ≤ m9 := by dsimp [m9]; omega
  have e2 : m2 ≤ m9 := by dsimp [m9]; omega
  have e3 : m3 ≤ m9 := by dsimp [m9]; omega
  have e4 : m4 ≤ m9 := by dsimp [m9]; omega
  have e5 : m5 ≤ m9 := by dsimp [m9]; omega
  have ex : 3 ≤ m9 := by dsimp [m9]; omega
  let R9 := WP.W9mp.MRegs R1 R2 R3 R4 R5
  let P9 := WP.W9mp.multProg e1 e2 e3 e4 e5 ex Pp Ps Pq Pe Pr
  let C9_base : ℕ := Cs + 2 * 1 + Cq + Ce + Cr + 200
  let C9 : ℕ := C9_base * (2 * Cp + 1)
  let T9 (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) : ℕ :=
    C9_base * (rootBound (T3 c0 c1 w0) (WP.W11b.wRHead (operandBits a b))
      (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
      (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) +
      Tp (operandBits a b) cSpec + Tp (operandBits a b) cSpec +
      (tapeSyms cSpec).length + 1)
  let K9 : ℕ := C9_base * Kroot + 1
  let g' (n : ℕ) : ℕ := 2 * C9_base * g n + K9 * n * (Nat.sqrt (128 * Nat.log2 n) + 1)
  have hg' : HeadlineCost g' (2 * ((2 * C9_base + 1) * Cg + 2 * (256 * K9 + 1))) N9 :=
    (hg.const_mul (2 * C9_base)).add_sqrtLog K9
  have hN9_2 : 2 ≤ N9 := hg.2.2.1
  refine ⟨m9, R9, P9, hm9, inferInstance, inferInstance, T9, C9, g', _, N9,
    WP.W9mp.multProg_closed e1 e2 e3 e4 e5 ex hc1 hc2 hc3 hc4 hc5,
    hg', ?_, ?_⟩
  · intro a b cSpec hj
    obtain ⟨hA, hB, -, -⟩ := input_bridge a b
    exact multProg_subNLogN_runs e1 e2 e3 e4 e5 ex sP sS sQ sE sR
      (operandBits a b) cSpec (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
      (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) a b
      (fun l => WP.Top.w9In (operandBits a b) a b cSpec (WP.Top.ι9 hm9 l)) [] [] [] []
      hj rfl rfl (WP.Top.lt_pow_bk hA) (WP.Top.lt_pow_bk hB) (WP.Top.headline_kk _)
      TermOK.nil TermOK.nil
      (hRootF a b cSpec hj)
      (by rw [List.append_nil]; exact WP.Top.w9In_oa _ _ _ _)
      (by rw [List.append_nil]; exact WP.Top.w9In_ob _ _ _ _)
      (by rw [List.append_nil]; exact WP.Top.w9In_c0 _ _ _ _)
      (WP.Top.w9In_w0 _ _ _ _)
      (by rw [List.append_nil]; exact WP.Top.w9In_tr _ _ _ _)
      (by simp)
  · intro a b cSpec hN hj
    set n := operandBits a b with hn_def
    have hn2 : 2 ≤ n := le_trans hN9_2 hN
    have hroot : C9_base * rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n)
        (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) ≤
        (C9_base * Kroot) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) := by
      have := Nat.mul_le_mul_left C9_base (hKroot n hn2)
      linarith
    have hTp_le : Tp n cSpec ≤ g n + Cp * ((tapeSyms cSpec).length + 1) :=
      hTp n cSpec hN hj
    dsimp only [T9, K9, C9, g']
    rw [← hn_def]
    calc C9_base * (rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
          Tp n cSpec + Tp n cSpec + (tapeSyms cSpec).length + 1)
        ≤ C9_base * (rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
          (g n + Cp * ((tapeSyms cSpec).length + 1)) +
          (g n + Cp * ((tapeSyms cSpec).length + 1)) + (tapeSyms cSpec).length + 1) :=
          Nat.mul_le_mul_left C9_base (by omega)
      _ = 2 * C9_base * g n +
          C9_base * rootBound (T3 c0 c1 w0) (WP.W11b.wRHead n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
          C9_base * (2 * Cp + 1) * ((tapeSyms cSpec).length + 1) := by ring
      _ ≤ 2 * C9_base * g n +
          (C9_base * Kroot) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) +
          C9_base * (2 * Cp + 1) * ((tapeSyms cSpec).length + 1) :=
          Nat.add_le_add_right (Nat.add_le_add_left hroot _) _
      _ ≤ 2 * C9_base * g n +
          (C9_base * Kroot + 1) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) +
          C9_base * (2 * Cp + 1) * ((tapeSyms cSpec).length + 1) := by
          have : (C9_base * Kroot) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) ≤
              (C9_base * Kroot + 1) * n * (Nat.sqrt (128 * Nat.log2 n) + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right n (by omega))
          omega

/-- **Assembly from `W9PipeSubNLogNSpec'` (`headline_46_of_w9_pipe'`, 0 `sorry`):**
Corollary of `headline_46_of_w9_subNLogN'` and `w9SubNLogNSpec'_of_pipe'`. -/
theorem headline_46_of_w9_pipe' (h : W9PipeSubNLogNSpec') :
    Headline_TM2_SubNLogN_46 :=
  headline_46_of_w9_subNLogN' (w9SubNLogNSpec'_of_pipe' h)

end SubNLogN.S5
