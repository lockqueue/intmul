import SubNLogN.Math.Networks.AppCCore

/-!
# Appendix A procedures (IV): the butterfly layer (Proposition A.11 (`prop:prop14-param`)) as an explicit procedure

Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`). On a layer array (`LayerAddr A K D S`, records `Fin rr → ℂ`), with
`H₀^{⊗D} = b^D 𝒮_D C^{⊗D} 𝒮_D` (eq. (`eq:oai-h0-transfer`), [OAI26, §5.1, (18)]):
1. phase 1 on `layerLayout A K D S`: `𝒮_D` (an address phase `i^{#sel}`) and individual kernels on the
   selected bits of the first `q₀ = ⌈lg W_c⌉⌈log_m 2d⌉` chunks;
2. reshape: the first `q₀` chunks become the least significant factor of the prefix, padded to the
   least multiple `R` of `W_c^{k₀}` (`k₀ = ⌈log_m d⌉`) that is `≥ 2^{q₀K}` (rows and padding,
   Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)); phase 2 runs the Lemma A.10 (`lem:transfer-phase`) core `cCoreProc` on the base-`m` pieces of
   the remaining `D − q₀` chunks (leaves `e < d^β`, `β = 1/64`, decided exactly by
   `k < ⌈log_{m^{64}} d⌉`); reshape back;
3. phase 3: `𝒮_D`, the scalar `b^D`, and the final truncation `Q_P`.
Reshapes are stream operations realized in `SubNLogN/Machine/`. This file is the functional specification;
all machine-level step bounds are proved in `SubNLogN/Machine/`.
-/

namespace SubNLogN.Math.Networks

open Model SubNLogN.Math.Walsh SubNLogN.Math.Common

/-! ## Sequences of procedures and the row reshape -/

/-- A sequence of procedures of varying depths, run in one class. -/
abbrev PSeq (L : Layout) (β : Type) := List (Σ d : ℕ, ProcK L β d)

/-- Run a sequence. -/
noncomputable def PSeq.run {L : Layout} {β : Type} (s : PSeq L β) (c : RowClass L)
    (A : L.Addr → β) : L.Addr → β :=
  s.foldl (fun A p => ProcK.run p.1 p.2 c A) A

/-- The prefix class (whole array, row field `0`) of `layerLayout`. -/
def topClass (A K D S : ℕ) : RowClass (layerLayout A K D S) :=
  RowClass.top ⟨0, by simp [layerLayout]⟩

/-- Row reshape of addresses: prefix `a` and the first `q` chunks (value `v`) become the prefix
`a·R + v`; the other chunks and the suffix are kept. -/
def mergeAddr (A K D S q R : ℕ) (hR : 0 < R) (hq : q ≤ D) (x : (layerLayout A K D S).Addr) :
    (layerLayout (A * R) K (D - q) S).Addr := fun i =>
  have hDK : (D - q) * K + q * K = D * K := by rw [← Nat.add_mul, Nat.sub_add_cancel hq]
  if h0 : i.val = 0 then
    ⟨(x ⟨0, by simp [layerLayout]⟩).val * R +
        (layerLayout A K D S).blockVal 1 (1 + q * K) x % R, by
      have hx : (x ⟨0, by simp [layerLayout]⟩).val < A := by
        have h := (x ⟨0, by simp [layerLayout]⟩).isLt
        simpa [layerLayout] using h
      have hm := Nat.mod_lt ((layerLayout A K D S).blockVal 1 (1 + q * K) x) hR
      have hr : (layerLayout (A * R) K (D - q) S).r i = A * R := by simp [layerLayout, h0]
      rw [hr]
      calc (x ⟨0, by simp [layerLayout]⟩).val * R +
            (layerLayout A K D S).blockVal 1 (1 + q * K) x % R
          < (x ⟨0, by simp [layerLayout]⟩).val * R + R := by omega
        _ = ((x ⟨0, by simp [layerLayout]⟩).val + 1) * R := by ring
        _ ≤ A * R := Nat.mul_le_mul_right _ hx⟩
  else if h1 : i.val ≤ (D - q) * K then
    have hlt : i.val + q * K < (layerLayout A K D S).n := by
      simp only [layerLayout]; omega
    ⟨(x ⟨i.val + q * K, hlt⟩).val, by
      have hL1 : (layerLayout (A * R) K (D - q) S).r i = 2 := by
        simp only [layerLayout]; rw [if_neg h0, if_pos h1]
      have hL0 : (layerLayout A K D S).r ⟨i.val + q * K, hlt⟩ = 2 := by
        simp only [layerLayout]; rw [if_neg (by omega), if_pos (by omega)]
      have h := (x ⟨i.val + q * K, hlt⟩).isLt
      rw [hL1]; exact h.trans_eq hL0⟩
  else
    have hlt : D * K + 1 < (layerLayout A K D S).n := by simp [layerLayout]
    ⟨(x ⟨D * K + 1, hlt⟩).val, by
      have hL1 : (layerLayout (A * R) K (D - q) S).r i = S := by
        simp only [layerLayout]; rw [if_neg h0, if_neg h1]
      have hL0 : (layerLayout A K D S).r ⟨D * K + 1, hlt⟩ = S := by
        simp only [layerLayout]; rw [if_neg (by omega), if_neg (by omega)]
      have h := (x ⟨D * K + 1, hlt⟩).isLt
      rw [hL1]; exact h.trans_eq hL0⟩

/-- Embed an array along `mergeAddr`; padded addresses get zero records. -/
noncomputable def embedArr {A K D S q R rr : ℕ} (hR : 0 < R) (hq : q ≤ D)
    (A0 : (layerLayout A K D S).Addr → Fin rr → ℂ) :
    (layerLayout (A * R) K (D - q) S).Addr → Fin rr → ℂ := fun y =>
  open Classical in
  if h : ∃ x, mergeAddr A K D S q R hR hq x = y then A0 (Classical.choose h) else 0

/-- Restrict an array back along `mergeAddr`. -/
def restrictArr {A K D S q R rr : ℕ} (hR : 0 < R) (hq : q ≤ D)
    (A1 : (layerLayout (A * R) K (D - q) S).Addr → Fin rr → ℂ) :
    (layerLayout A K D S).Addr → Fin rr → ℂ := fun x => A1 (mergeAddr A K D S q R hR hq x)

/-! ## Layer parameters (exact integer computations) -/

/-- `q₀ = ⌈lg W_c⌉ ⌈log_m 2d⌉`. -/
noncomputable def q0Of (d : ℕ) : ℕ := Nat.clog 2 Wc * Nat.clog mH (2 * d)

/-- `k₀ = ⌈log_m d⌉`. -/
def k0Of (d : ℕ) : ℕ := Nat.clog mH d

/-- The padded row range: the least multiple of `W_c^{k₀}` that is `≥ 2^{q₀K}`. -/
noncomputable def padR (d K : ℕ) : ℕ :=
  Wc ^ k0Of d * ((2 ^ (q0Of d * K) + Wc ^ k0Of d - 1) / Wc ^ k0Of d)

/-- Leaf rule `e = m^k < d^{1/64}`, i.e. `k < kLeafOf d` (`m^{64k} < d`). -/
def kLeafOf (d : ℕ) : ℕ := Nat.clog (mH ^ 64) d

/-- Base-`m` pieces: from the digit list (least significant first) produce `(depth, offset)`. -/
def piecesAux : List ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _ => []
  | a :: ds, j, o => (List.range a).map (fun t => (j, o + t * mH ^ j)) ++ piecesAux ds (j + 1) (o + a * mH ^ j)

/-- The base-`m` pieces of `e` consecutive chunks (Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`)). -/
def piecesOf (e : ℕ) : List (ℕ × ℕ) := piecesAux (Nat.digits mH e) 0 0

/-! ## The procedure -/

/-- `𝒮_D`: multiply each record by `i^{#selected bits}` (address phase, `lem:transfer-long-record`). -/
noncomputable def sDiag {A K D S rr : ℕ} (ρ : ℕ) : Step (layerLayout A K D S) (Fin rr → ℂ) :=
  .addrMap fun x v => (Complex.I ^ (∑ j ∈ Finset.range D,
    (layerLayout A K D S).blockVal (selField K ρ j) (selField K ρ j + 1) x)) • v

/-- Phase 1: `𝒮_D` and individual kernels on the first `min q₀ D` chunks. -/
noncomputable def layerPhase1 (A K D S rr ρ d : ℕ) : ProcK (layerLayout A K D S) (Fin rr → ℂ) 0 :=
  [sDiag ρ] ++ (List.range (min (q0Of d) D)).flatMap fun j => dgate (selField K ρ j)

/-- Phase 2: the Lemma A.10 (`lem:transfer-phase`) core on the base-`m` pieces of the remaining chunks (on the reshaped layout). -/
noncomputable def layerPhase2 (A K D S rr ρ d : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) :
    PSeq (layerLayout (A * padR d K) K (D - q0Of d) S) (Fin rr → ℂ) :=
  (piecesOf (D - q0Of d)).map fun p =>
    ⟨p.1, cCoreProc (A * padR d K) K (D - q0Of d) S rr ρ (kLeafOf d) cdat p.1 p.2⟩

/-- Phase 3: `𝒮_D`, the scalar `b^D`, the final truncation `Q_P`. -/
noncomputable def layerPhase3 (A K D S rr ρ P : ℕ) : ProcK (layerLayout A K D S) (Fin rr → ℂ) 0 :=
  [sDiag ρ, .recMap fun v => bD D • v, .recMap fun v k => truncC P (v k)]

/-- Is the row reshape used (more than `q₀` chunks; the padded range is positive)? -/
noncomputable def useRows (D K d : ℕ) : Prop := q0Of d < D ∧ 0 < padR d K

/-- **The layer procedure** (value semantics): `decode ∘ phases ∘ encode`. -/
noncomputable def layerRun (P A K D S rr ρ d : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (z : RArr (LayerAddr A K D S) rr) : RArr (LayerAddr A K D S) rr :=
  open Classical in
  let A₁ := ProcK.run 0 (layerPhase1 A K D S rr ρ d) (topClass A K D S) (encodeArr z)
  let A₂ := if h : useRows D K d then
      restrictArr h.2 h.1.le (PSeq.run (layerPhase2 A K D S rr ρ d cdat)
        (topClass (A * padR d K) K (D - q0Of d) S) (embedArr h.2 h.1.le A₁))
    else A₁
  decodeArr (ProcK.run 0 (layerPhase3 A K D S rr ρ P) (topClass A K D S) A₂)

/-! ## Contracts: Proposition A.11 (`prop:prop14-param`) at the `κ = 2^{-46}` row -/

/-- CONTRACT (Proposition A.11 (`prop:prop14-param`), value level, Appendix A.6 (`sec:transfer-layer`)). With the
complex network certificate, valid edge data and the Lemma A.10 (`lem:transfer-phase`) / eq. (`eq:oai-h0`) statements as explicit hypotheses, the
layer procedure returns exactly `Q_P(Hz)` on every disk-grid input (`LayerSpec`), for every
tuple with `K ≥ 6`, `1 ≤ D ≤ d` (so every piece has depth `≤ k₀` and complete role splits). This holds
in particular uniformly in the bands of Proposition A.11 (`prop:prop14-param`), eq. (`eq:walsh-layer-bands`). Machine-level step bounds are in `SubNLogN/Machine/`. -/
def Prop71LayerSpecStmt : Prop :=
  ComplexNetCert → CCoreProcCorrectStmt → RunEightSpecStmt → PackedAgreeStmt → PackedProcCorrectStmt →
  TranslationConjStmt → H0TensorIdentityStmt → Prop71FunctionalStmt → DecodeEncodeAddrStmt →
  ∀ (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData),
    (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) →
  ∀ (P d rr K D A S : ℕ) (ρ : Fin K), 6 ≤ K → 1 ≤ D → D ≤ d →
    LayerSpec P rr A K D S ρ (layerRun P A K D S rr ρ.val d cdat)

/-- Guard grid: every coefficient on the `2^{-(P+Δ)}` grid with `|Re|, |Im| < 2^{Δ+2}`. -/
def OnGuardGrid {α : Type} {rr : ℕ} (P Δ : ℕ) (A : α → Fin rr → ℂ) : Prop :=
  ∀ x k, OnGrid (P + Δ) (A x k) ∧ |(A x k).re| < 2 ^ (Δ + 2) ∧ |(A x k).im| < 2 ^ (Δ + 2)

/-- Every intermediate array of a sequence satisfies `Good`. -/
def PSeq.AllStates {L : Layout} {β : Type} (Good : (L.Addr → β) → Prop) (s : PSeq L β)
    (c : RowClass L) (A : L.Addr → β) : Prop :=
  ∀ i : Fin s.length, ProcK.AllStates Good (s.get i).1 (s.get i).2 c
    ((s.take i.val).foldl (fun A p => ProcK.run p.1 p.2 c A) A)

/-- The guard property of one layer run: all intermediate arrays of phase 1, of phase 2 (on the
reshaped array) and of phase 3 before its last step (the truncation `Q_P`) are on the guard grid. -/
def LayerGuarded (P A K D S rr ρ d Δ : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (z : RArr (LayerAddr A K D S) rr) : Prop :=
  open Classical in
  let A₁ := ProcK.run 0 (layerPhase1 A K D S rr ρ d) (topClass A K D S) (encodeArr z)
  let A₂ := if h : useRows D K d then
      restrictArr h.2 h.1.le (PSeq.run (layerPhase2 A K D S rr ρ d cdat)
        (topClass (A * padR d K) K (D - q0Of d) S) (embedArr h.2 h.1.le A₁))
    else A₁
  ProcK.AllStates (OnGuardGrid P Δ) 0 (layerPhase1 A K D S rr ρ d) (topClass A K D S) (encodeArr z) ∧
  (∀ h : useRows D K d, PSeq.AllStates (OnGuardGrid P Δ) (layerPhase2 A K D S rr ρ d cdat)
      (topClass (A * padR d K) K (D - q0Of d) S) (embedArr h.2 h.1.le A₁)) ∧
  ProcK.AllStates (OnGuardGrid P Δ) 0 ((layerPhase3 A K D S rr ρ P).take 2) (topClass A K D S) A₂

/-- CONTRACT (guard, Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`), eq. (`eq:walsh-guard-growth`); `A(k) ≤ s_c A(k−1) + E_*` over
sequential children, denominator headroom). In the bands, with `Δ = ⌈C₀ d^{14}⌉`, every intermediate
array of a layer run on a disk-grid input is on the guard grid (`LayerGuarded`): the machine layer represents all
of them in `P + 2Δ + 3` bits per component, and no rounding happens before the final `Q_P`. -/
def Prop71GuardStmt : Prop :=
  ComplexNetCert → GuardGrowthStmt → GuardSmallStmt →
  ∀ (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData),
    (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) →
  ∀ (aD bD : ℝ), 0 < aD → aD ≤ bD → ∃ P₀ : ℝ, ∀ (P d rr K D A S : ℕ) (ρ : Fin K)
    (z : RArr (LayerAddr A K D S) rr),
    P₀ ≤ P → aD * (P : ℝ) ^ ((1 : ℝ) / 15) ≤ d → (d : ℝ) ≤ bD * (P : ℝ) ^ ((1 : ℝ) / 15) →
    K = ⌊(d : ℝ) ^ c46⌋₊ → 1 ≤ D → D ≤ d → ArrOnDiskGrid P z →
      LayerGuarded P A K D S rr ρ.val d ⌈(guardC0 100 : ℝ) * (d : ℝ) ^ 14⌉₊ cdat z

end SubNLogN.Math.Networks
