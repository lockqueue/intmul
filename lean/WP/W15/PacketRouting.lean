import IntMul.Theorem6And7Barriers
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import IntMulTM.Framework.AxiomGuard

/-!
# WP.W15.PacketRouting: Floyd's conserved-packet routing bound for `c` registers, with non-vacuity witnesses (analyzing the omitted earlier `[MS]` draft barrier discussion)

**W15 disclaimer (verbatim in every W15 file).** No W15 result is a lower bound for Turing machines,
Boolean circuits, the Word RAM or bit complexity. Every result in this file holds only in the
restricted model defined explicitly below.

**Model (a): conserved-packet `c`-register routing (Floyd).** A state `a : ι → δ → ℕ` counts, for
each register `i` and destination `d`, the packets in `i` bound for `d`. Packets are indivisible and
are never created, copied, encoded or combined. One step (`ValidCStep c B`) touches a set `S` of at
most `c` registers, each holding at most `B` packets before the step, and redistributes their packets
arbitrarily, preserving the number of packets for each destination inside `S`; registers outside
`S` are unchanged. The register type `ι` is arbitrary, so any number of scratch registers is allowed.
Arbitrary functions of register contents ("table lookups") are **not** steps of this model.

**What is proved.**
* `validCStep_pot_le`: one step raises Floyd's potential `Φ = ∑ a log a` by at most `c B log c`
  (Jensen for `x log x` on the old cells, superadditivity on the new cells).
* `cReg_transpose_lower_bound`: transposing `B × B` packets (with any number of scratch registers)
  needs at least `B log B / (c log c)` steps; `cReg_transpose_lower_bound_pow2` for `B = 2^k`.
* `validTwoRegStep_to_cStep`: the snapshot's 2-register model (B67:614) is the case `c = 2`.
* Non-vacuity and tightness: explicit transposition traces for `B = 2` (1 step) and `B = 4`
  (4 steps) in the snapshot's model; both meet the bound `k 2^k / 2` exactly (`floyd_tight_two`,
  `floyd_tight_four`).
-/

namespace WP.W15

open IntMul
open scoped BigOperators

/-! ## The model -/

/-- A packet distribution: `a i d` packets in register `i` are bound for destination `d`. -/
abbrev Packets (ι δ : Type*) : Type _ := ι → δ → ℕ

section Model

variable {ι δ : Type*} [Fintype ι] [Fintype δ]

/-- Floyd's potential `Φ(a) = ∑ᵢ ∑_d a log a` (natural logarithm; the base only scales `Φ`). -/
noncomputable def pot (a : Packets ι δ) : ℝ := ∑ i, ∑ d, floydPhi (a i d)

/-- One step of the conserved-packet `c`-register model. -/
def ValidCStep (c B : ℕ) (a a' : Packets ι δ) : Prop :=
  ∃ S : Finset ι, S.card ≤ c ∧ (∀ i ∈ S, ∑ d, a i d ≤ B) ∧
    (∀ d, ∑ i ∈ S, a' i d = ∑ i ∈ S, a i d) ∧ ∀ i, i ∉ S → a' i = a i

/-- A trace of `ValidCStep`s from `a` to `b` (the list holds the successive states). -/
inductive CTrace (c B : ℕ) : Packets ι δ → List (Packets ι δ) → Packets ι δ → Prop
  | nil (a : Packets ι δ) : CTrace c B a [] a
  | cons {a a₁ b : Packets ι δ} {rest : List (Packets ι δ)} :
      ValidCStep c B a a₁ → CTrace c B a₁ rest b → CTrace c B a (a₁ :: rest) b

end Model

/-! ## Potential inequalities -/

theorem floydPhi_def (x : ℕ) : floydPhi x = (x : ℝ) * Real.log (x : ℝ) := rfl

theorem floydPhi_nonneg (x : ℕ) : 0 ≤ floydPhi x := by
  rw [floydPhi_def]
  rcases Nat.eq_zero_or_pos x with h | h
  · simp [h]
  · exact mul_nonneg (Nat.cast_nonneg x) (Real.log_nonneg (Nat.one_le_cast.mpr h))

/-- Superadditivity of `x log x` over a finite family. -/
theorem sum_floydPhi_le {ι : Type*} (S : Finset ι) (x : ι → ℕ) :
    ∑ i ∈ S, floydPhi (x i) ≤ floydPhi (∑ i ∈ S, x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have := floydPhi_superadditive (x i) (∑ j ∈ S, x j)
    linarith

/-- Jensen for `x log x`: `∑ᵢ xᵢ log xᵢ ≥ A log (A / n)` with `A = ∑ᵢ xᵢ`, `n = |S|`. -/
theorem sum_floydPhi_ge {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (x : ι → ℕ) :
    ((∑ i ∈ S, x i : ℕ) : ℝ) * Real.log (((∑ i ∈ S, x i : ℕ) : ℝ) / (S.card : ℝ)) ≤
      ∑ i ∈ S, floydPhi (x i) := by
  have hn : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hn' : (S.card : ℝ) ≠ 0 := hn.ne'
  have hJ := Real.convexOn_mul_log.map_sum_le (t := S) (w := fun _ => 1 / (S.card : ℝ))
    (p := fun i => (x i : ℝ)) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun _ _ => Set.mem_Ici.mpr (Nat.cast_nonneg _))
  simp only [smul_eq_mul] at hJ
  have hsum : ∑ i ∈ S, 1 / (S.card : ℝ) * (x i : ℝ) =
      ((∑ i ∈ S, x i : ℕ) : ℝ) / (S.card : ℝ) := by
    rw [← Finset.mul_sum]
    push_cast
    ring
  have hrhs : ∑ i ∈ S, 1 / (S.card : ℝ) * ((x i : ℝ) * Real.log (x i : ℝ)) =
      (∑ i ∈ S, floydPhi (x i)) / (S.card : ℝ) := by
    rw [← Finset.mul_sum]
    simp only [floydPhi_def]
    ring
  rw [hsum, hrhs, le_div_iff₀ hn] at hJ
  calc ((∑ i ∈ S, x i : ℕ) : ℝ) * Real.log (((∑ i ∈ S, x i : ℕ) : ℝ) / (S.card : ℝ))
      = ((∑ i ∈ S, x i : ℕ) : ℝ) / (S.card : ℝ) *
          Real.log (((∑ i ∈ S, x i : ℕ) : ℝ) / (S.card : ℝ)) * (S.card : ℝ) := by
        field_simp
    _ ≤ ∑ i ∈ S, floydPhi (x i) := hJ

/-- **One-step bound.** A `ValidCStep c B` raises `Φ` by at most `c B log c`. -/
theorem validCStep_pot_le {ι δ : Type*} [Fintype ι] [Fintype δ] (c B : ℕ) (hc : 1 ≤ c)
    (a a' : Packets ι δ) (h : ValidCStep c B a a') :
    pot a' - pot a ≤ (c : ℝ) * B * Real.log c := by
  classical
  obtain ⟨S, hcard, hcap, hcons, hframe⟩ := h
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg (by exact_mod_cast hc)
  have hsplit : ∀ b : Packets ι δ,
      pot b = ∑ i ∈ S, ∑ d, floydPhi (b i d) + ∑ i ∈ Sᶜ, ∑ d, floydPhi (b i d) := by
    intro b
    unfold pot
    rw [Finset.sum_add_sum_compl]
  have hrest : ∑ i ∈ Sᶜ, ∑ d, floydPhi (a' i d) = ∑ i ∈ Sᶜ, ∑ d, floydPhi (a i d) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hframe i (Finset.mem_compl.mp hi)]
  rw [hsplit a', hsplit a, hrest]
  have htarget : 0 ≤ (c : ℝ) * B * Real.log c :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hlogc
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    simp only [Finset.sum_empty, zero_add, sub_self]
    exact htarget
  · have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have hnc : (S.card : ℝ) ≤ c := by exact_mod_cast hcard
    have hd : ∀ d, ∑ i ∈ S, floydPhi (a' i d) - ∑ i ∈ S, floydPhi (a i d) ≤
        ((∑ i ∈ S, a i d : ℕ) : ℝ) * Real.log c := by
      intro d
      have hup := sum_floydPhi_le S (fun i => a' i d)
      have hcd := hcons d
      rw [hcd] at hup
      have hlow := sum_floydPhi_ge S hS (fun i => a i d)
      rcases Nat.eq_zero_or_pos (∑ i ∈ S, a i d) with hA0 | hApos
      · rw [hA0] at hup hlow ⊢
        simp only [Nat.cast_zero, zero_mul, floydPhi_zero] at hup hlow ⊢
        linarith
      · have hAr : (0 : ℝ) < ((∑ i ∈ S, a i d : ℕ) : ℝ) := by exact_mod_cast hApos
        have hlogdiv : Real.log (((∑ i ∈ S, a i d : ℕ) : ℝ) / S.card) =
            Real.log ((∑ i ∈ S, a i d : ℕ) : ℝ) - Real.log S.card :=
          Real.log_div hAr.ne' hn.ne'
        rw [hlogdiv] at hlow
        rw [floydPhi_def (∑ i ∈ S, a i d)] at hup
        have hmono : Real.log (S.card : ℝ) ≤ Real.log c := Real.log_le_log hn hnc
        have hm2 := mul_le_mul_of_nonneg_left hmono hAr.le
        nlinarith
    have hsum_d : ∑ d, (∑ i ∈ S, floydPhi (a' i d) - ∑ i ∈ S, floydPhi (a i d)) ≤
        ∑ d, ((∑ i ∈ S, a i d : ℕ) : ℝ) * Real.log c :=
      Finset.sum_le_sum fun d _ => hd d
    have hcapsum : (∑ d, ((∑ i ∈ S, a i d : ℕ) : ℝ)) ≤ (S.card : ℝ) * B := by
      have hcomm : ∑ d, (∑ i ∈ S, a i d) = ∑ i ∈ S, ∑ d, a i d := Finset.sum_comm
      have h2 : ∑ i ∈ S, ∑ d, a i d ≤ ∑ _i ∈ S, B := Finset.sum_le_sum fun i hi => hcap i hi
      have h3 : (∑ d, (∑ i ∈ S, a i d)) ≤ S.card * B := by
        rw [hcomm]
        simpa using h2
      exact_mod_cast h3
    have hswap1 : ∑ i ∈ S, ∑ d, floydPhi (a' i d) = ∑ d, ∑ i ∈ S, floydPhi (a' i d) :=
      Finset.sum_comm
    have hswap2 : ∑ i ∈ S, ∑ d, floydPhi (a i d) = ∑ d, ∑ i ∈ S, floydPhi (a i d) :=
      Finset.sum_comm
    rw [hswap1, hswap2]
    have hdiff : ∑ d, ∑ i ∈ S, floydPhi (a' i d) - ∑ d, ∑ i ∈ S, floydPhi (a i d) =
        ∑ d, (∑ i ∈ S, floydPhi (a' i d) - ∑ i ∈ S, floydPhi (a i d)) :=
      (Finset.sum_sub_distrib _ _).symm
    have hfin : ∑ d, ((∑ i ∈ S, a i d : ℕ) : ℝ) * Real.log c ≤ (c : ℝ) * B * Real.log c := by
      rw [← Finset.sum_mul]
      have hSB : (S.card : ℝ) * B ≤ c * B := mul_le_mul_of_nonneg_right hnc (Nat.cast_nonneg B)
      exact mul_le_mul_of_nonneg_right (hcapsum.trans hSB) hlogc
    linarith

/-- **Trace bound.** A trace of length `T` raises `Φ` by at most `T c B log c`. -/
theorem ctrace_pot_le {ι δ : Type*} [Fintype ι] [Fintype δ] (c B : ℕ) (hc : 1 ≤ c)
    {a b : Packets ι δ} {tr : List (Packets ι δ)} (h : CTrace c B a tr b) :
    pot b - pot a ≤ tr.length * ((c : ℝ) * B * Real.log c) := by
  induction h with
  | nil a => simp
  | cons hstep _ ih =>
    have h1 := validCStep_pot_le c B hc _ _ hstep
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-! ## Transposition with scratch registers -/

section Scratch

variable (σ : Type*) [Fintype σ]

/-- Initial state: home register `j` holds one packet for every destination; scratch registers are
empty. -/
def initP (B : ℕ) : Packets (Fin B ⊕ σ) (Fin B) :=
  fun i _ => Sum.elim (fun _ => 1) (fun _ => 0) i

/-- Target state: home register `j` holds all `B` packets bound for `j`; scratch registers are
empty. -/
def targetP (B : ℕ) : Packets (Fin B ⊕ σ) (Fin B) :=
  fun i d => Sum.elim (fun j => if j = d then B else 0) (fun _ => 0) i

theorem pot_initP (B : ℕ) : pot (initP σ B) = 0 := by
  simp [pot, initP, Fintype.sum_sum_type]

theorem pot_targetP (B : ℕ) : pot (targetP σ B) = (B : ℝ) ^ 2 * Real.log B := by
  have h := floydMatrixPotential_target B
  unfold floydMatrixPotential targetPacketMatrix at h
  simp only [pot, targetP, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, floydPhi_zero,
    Finset.sum_const_zero, add_zero]
  exact h

/-- **Conserved-packet `c`-register transposition lower bound (Floyd; refines `theorem7_2_floyd_trace_lower_bound` from the omitted earlier `[MS]` draft barrier discussion).** Every `c`-register trace that transposes
`B × B` packets, with any finite set `σ` of scratch registers, has length `T` with
`B log B ≤ T · c log c`, i.e. `T ≥ B log B / (c log c)`. -/
theorem cReg_transpose_lower_bound (c B : ℕ) (hc : 2 ≤ c) (hB : 0 < B)
    (tr : List (Packets (Fin B ⊕ σ) (Fin B))) (h : CTrace c B (initP σ B) tr (targetP σ B)) :
    (B : ℝ) * Real.log B ≤ tr.length * ((c : ℝ) * Real.log c) := by
  have h1 := ctrace_pot_le c B (by omega) h
  rw [pot_initP, pot_targetP, sub_zero] at h1
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have h2 : (B : ℝ) * ((B : ℝ) * Real.log B) ≤ (B : ℝ) * (tr.length * ((c : ℝ) * Real.log c)) := by
    calc (B : ℝ) * ((B : ℝ) * Real.log B) = (B : ℝ) ^ 2 * Real.log B := by ring
      _ ≤ tr.length * ((c : ℝ) * B * Real.log c) := h1
      _ = (B : ℝ) * (tr.length * ((c : ℝ) * Real.log c)) := by ring
  exact le_of_mul_le_mul_left h2 hBr

/-- The bound for `B = 2^k`: `k 2^k log 2 ≤ T · c log c` (for `c = 2`: `T ≥ k 2^k / 2`). -/
theorem cReg_transpose_lower_bound_pow2 (c k : ℕ) (hc : 2 ≤ c)
    (tr : List (Packets (Fin (2 ^ k) ⊕ σ) (Fin (2 ^ k))))
    (h : CTrace c (2 ^ k) (initP σ (2 ^ k)) tr (targetP σ (2 ^ k))) :
    (k : ℝ) * 2 ^ k * Real.log 2 ≤ tr.length * ((c : ℝ) * Real.log c) := by
  have := cReg_transpose_lower_bound σ c (2 ^ k) hc (by positivity) tr h
  push_cast at this
  rw [Real.log_pow] at this
  linarith

end Scratch

/-! ## The snapshot's 2-register model is the case `c = 2` -/

/-- Every snapshot step `ValidTwoRegStep` (B67:614) is a `ValidCStep 2`. -/
theorem validTwoRegStep_to_cStep (B : ℕ) (a a' : PacketMatrix B) (h : ValidTwoRegStep B a a') :
    ValidCStep 2 B a a' := by
  classical
  obtain ⟨i1, i2, hne, x, y, z, w, hcap1, hcap2, ha1, ha2, ha'1, ha'2, hframe⟩ := h
  refine ⟨{i1, i2}, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_pair hne]
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hcap1
    · rw [Finset.mem_singleton.mp hi]
      exact hcap2
  · intro d
    rw [Finset.sum_pair hne, Finset.sum_pair hne, ha'1 d, ha'2 d, ha1 d, ha2 d]
    ring
  · intro i hi
    have h1 : i ≠ i1 := fun h => hi (by simp [h])
    have h2 : i ≠ i2 := fun h => hi (by simp [h])
    funext d
    exact hframe i h1 h2 d

theorem validTransposeTrace_to_cTrace (B : ℕ) {a b : PacketMatrix B} {tr : List (PacketMatrix B)}
    (h : ValidTransposeTrace B a tr b) : CTrace 2 B a tr b := by
  induction h with
  | nil a => exact CTrace.nil a
  | cons hstep _ ih => exact CTrace.cons (validTwoRegStep_to_cStep B _ _ hstep) ih

/-! ## Non-vacuity and tightness: explicit transposition traces -/

/-- `B = 2`: one exchange transposes. -/
theorem floyd_step_two : ValidTwoRegStep 2 (initPacketMatrix 2) (targetPacketMatrix 2) := by
  refine ⟨0, 1, by decide, ![1, 0], ![0, 1], ![1, 0], ![0, 1], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

theorem floyd_witness_two :
    ValidTransposeTrace 2 (initPacketMatrix 2) [targetPacketMatrix 2] (targetPacketMatrix 2) :=
  .cons floyd_step_two (.nil _)

/-- Intermediate states of the 4-step transposition of a `4 × 4` packet matrix. -/
def w4a1 : PacketMatrix 4 := ![![2, 0, 2, 0], ![0, 2, 0, 2], ![1, 1, 1, 1], ![1, 1, 1, 1]]
def w4a2 : PacketMatrix 4 := ![![2, 0, 2, 0], ![0, 2, 0, 2], ![2, 0, 2, 0], ![0, 2, 0, 2]]
def w4a3 : PacketMatrix 4 := ![![4, 0, 0, 0], ![0, 2, 0, 2], ![0, 0, 4, 0], ![0, 2, 0, 2]]

theorem floyd_step_four_1 : ValidTwoRegStep 4 (initPacketMatrix 4) w4a1 := by
  refine ⟨0, 1, by decide, ![1, 0, 1, 0], ![0, 1, 0, 1], ![1, 0, 1, 0], ![0, 1, 0, 1],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem floyd_step_four_2 : ValidTwoRegStep 4 w4a1 w4a2 := by
  refine ⟨2, 3, by decide, ![1, 0, 1, 0], ![0, 1, 0, 1], ![1, 0, 1, 0], ![0, 1, 0, 1],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem floyd_step_four_3 : ValidTwoRegStep 4 w4a2 w4a3 := by
  refine ⟨0, 2, by decide, ![2, 0, 0, 0], ![0, 0, 2, 0], ![2, 0, 0, 0], ![0, 0, 2, 0],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem floyd_step_four_4 : ValidTwoRegStep 4 w4a3 (targetPacketMatrix 4) := by
  refine ⟨1, 3, by decide, ![0, 2, 0, 0], ![0, 0, 0, 2], ![0, 2, 0, 0], ![0, 0, 0, 2],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem floyd_witness_four :
    ValidTransposeTrace 4 (initPacketMatrix 4) [w4a1, w4a2, w4a3, targetPacketMatrix 4]
      (targetPacketMatrix 4) :=
  .cons floyd_step_four_1 (.cons floyd_step_four_2 (.cons floyd_step_four_3
    (.cons floyd_step_four_4 (.nil _))))

/-- **Tightness for `B = 2`.** The shortest 2-register transposition trace has exactly
`k 2^k / 2 = 1` step. -/
theorem floyd_tight_two :
    (∃ tr, ValidTransposeTrace 2 (initPacketMatrix 2) tr (targetPacketMatrix 2) ∧ tr.length = 1) ∧
    ∀ tr, ValidTransposeTrace 2 (initPacketMatrix 2) tr (targetPacketMatrix 2) → 1 ≤ tr.length := by
  refine ⟨⟨_, floyd_witness_two, rfl⟩, fun tr htr => ?_⟩
  have := (theorem7_2_floyd_trace_lower_bound 1 tr htr).2
  norm_num at this
  exact_mod_cast this

/-- **Tightness for `B = 4`.** The shortest 2-register transposition trace has exactly
`k 2^k / 2 = 4` steps. -/
theorem floyd_tight_four :
    (∃ tr, ValidTransposeTrace 4 (initPacketMatrix 4) tr (targetPacketMatrix 4) ∧ tr.length = 4) ∧
    ∀ tr, ValidTransposeTrace 4 (initPacketMatrix 4) tr (targetPacketMatrix 4) → 4 ≤ tr.length := by
  refine ⟨⟨_, floyd_witness_four, rfl⟩, fun tr htr => ?_⟩
  have := (theorem7_2_floyd_trace_lower_bound 2 tr htr).2
  norm_num at this
  exact_mod_cast this

/-- **Non-vacuity of the `c`-register model.** For every `c ≥ 2` there is a valid `c`-register
transposition trace for `B = 4` (so `cReg_transpose_lower_bound` is not vacuous). -/
theorem cTrace_witness_four (c : ℕ) (hc : 2 ≤ c) :
    ∃ tr, CTrace c 4 (initPacketMatrix 4) tr (targetPacketMatrix 4) ∧ tr.length = 4 := by
  refine ⟨[w4a1, w4a2, w4a3, targetPacketMatrix 4], ?_, rfl⟩
  -- monotonicity in `c`
  have mono : ∀ {a b : PacketMatrix 4} {tr : List (PacketMatrix 4)},
      CTrace 2 4 a tr b → CTrace c 4 a tr b := by
    intro a b tr h
    induction h with
    | nil a => exact CTrace.nil a
    | cons hstep _ ih =>
      obtain ⟨S, hS, h1, h2, h3⟩ := hstep
      exact CTrace.cons ⟨S, hS.trans hc, h1, h2, h3⟩ ih
  exact mono (validTransposeTrace_to_cTrace 4 floyd_witness_four)

#assert_std_axioms sum_floydPhi_le sum_floydPhi_ge validCStep_pot_le ctrace_pot_le pot_initP
  pot_targetP cReg_transpose_lower_bound cReg_transpose_lower_bound_pow2 validTwoRegStep_to_cStep
  validTransposeTrace_to_cTrace floyd_witness_two floyd_witness_four floyd_tight_two
  floyd_tight_four cTrace_witness_four

#assert_std_axioms floydPhi_def floydPhi_nonneg floyd_step_two floyd_step_four_1 floyd_step_four_2
  floyd_step_four_3 floyd_step_four_4

end WP.W15
