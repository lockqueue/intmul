import IntMulTM.Framework.Sim
import IntMulTM.Framework.Triple
import IntMulTM.Framework.Layout

/-!
# IntMulTM.Framework.Accept — acceptance packaging

For a program `p` over the production layout `StackId W` (input alphabet = `ea.Γ`, output `Bool`,
work stacks `Sym`) that maps every encoded input to `encodeNat (f a)` on the output stack (all
other stacks empty) within `T (input length)` source steps:

* `acceptTM` : the `Turing.TM2ComputableInTime ea finEncodingNatBool f` value, `time L = T L + 1`;
* `acceptTM_finite` : `∀ k, Finite (M.tm.Γ k)` (all stack alphabets, incl. the hidden return stack);
* `nlogn_add_one`, `linear_nlogn` : asymptotic helpers;
* `acceptance_of_spec` / `acceptance_of_triple` : the acceptance-theorem shape
  `∃ M, (∀ k, Finite (M.tm.Γ k)) ∧ ∃ C N₀, ∀ L ≥ N₀, M.time L ≤ C * L * Nat.log2 L`.
-/

namespace TMFw

open Turing Computability

section Accept

variable {W σ : Type} [DecidableEq W]

/-- Production initial stacks: only `input` is nonempty. -/
def inputStk {A : Type} (l : List A) : ∀ k : StackId W, List (StackId.Γ A k) :=
  stkOnly (Γ := StackId.Γ A) .input l

/-- Production final stacks: only `output` is nonempty. -/
def outputStk {A : Type} (l : List Bool) : ∀ k : StackId W, List (StackId.Γ A k) :=
  stkOnly (Γ := StackId.Γ A) .output l

variable [Fintype W] [Fintype σ]

/-- **Production wrapper.** -/
noncomputable def acceptTM {α αΓ : Type} [Fintype αΓ] (ea : Encoding α αΓ) (f : α → ℕ)
    (p : Prog (StackId W) (StackId.Γ αΓ) σ) (σ0 : σ) (T : ℕ → ℕ)
    (hspec : ∀ a, ∃ v t, Eval [] p ⟨σ0, inputStk (ea.encode a)⟩
      ⟨v, outputStk (encodeNat (f a))⟩ t ∧ t ≤ T (ea.encode a).length) :
    TM2ComputableInTime ea.encode encodingNatBool.encode f :=
  toTM2ComputableInTime ea encodingNatBool f .input .output (Equiv.refl _) (Equiv.refl _) p σ0
    (fun L => T L + 1) (by
      intro a
      obtain ⟨v, t, he, hle⟩ := hspec a
      refine ⟨v, t, ?_, by show t + 1 ≤ T (ea.encode a).length + 1; omega⟩
      have e1 : List.map (Equiv.refl (StackId.Γ αΓ (StackId.input : StackId W))).invFun
          (ea.encode a) = ea.encode a := List.map_id _
      have e2 : List.map (Equiv.refl (StackId.Γ αΓ (StackId.output : StackId W))).invFun
          (encodingNatBool.encode (f a)) = encodeNat (f a) := List.map_id _
      rw [e1, e2]
      exact he)

theorem acceptTM_time {α αΓ : Type} [Fintype αΓ] {ea : Encoding α αΓ} {f : α → ℕ}
    {p : Prog (StackId W) (StackId.Γ αΓ) σ} {σ0 : σ} {T : ℕ → ℕ} {hspec} (L : ℕ) :
    (acceptTM ea f p σ0 T hspec).time L = T L + 1 := rfl

theorem acceptTM_finite {α αΓ : Type} [Fintype αΓ] {ea : Encoding α αΓ} {f : α → ℕ}
    {p : Prog (StackId W) (StackId.Γ αΓ) σ} {σ0 : σ} {T : ℕ → ℕ} {hspec} :
    ∀ k, Finite ((acceptTM ea f p σ0 T hspec).tm.Γ k) :=
  toTM2ComputableInTime_finite (Γ := StackId.Γ αΓ) finite_StackId_Γ

end Accept

/-! ## Asymptotics -/

theorem one_le_log2_of_two_le {L : ℕ} (h : 2 ≤ L) : 1 ≤ Nat.log2 L := by
  rw [Nat.log2_def, if_pos h]
  omega

/-- Absorb the `+ 1` of the wrapper's cleanup step. -/
theorem nlogn_add_one {T : ℕ → ℕ} (h : ∃ C N₀, ∀ L ≥ N₀, T L ≤ C * L * Nat.log2 L) :
    ∃ C N₀, ∀ L ≥ N₀, T L + 1 ≤ C * L * Nat.log2 L := by
  obtain ⟨C, N₀, hC⟩ := h
  refine ⟨C + 1, max N₀ 2, fun L hL => ?_⟩
  have h1 := hC L (le_of_max_le_left hL)
  have hL2 : 2 ≤ L := le_of_max_le_right hL
  have hlog := one_le_log2_of_two_le hL2
  have hpos : 0 < L * Nat.log2 L := Nat.mul_pos (by omega) hlog
  have e : (C + 1) * L * Nat.log2 L = C * L * Nat.log2 L + L * Nat.log2 L := by
    rw [Nat.succ_mul, Nat.add_mul]
  rw [e]
  omega

/-- Linear bounds are `O(L log L)`. -/
theorem linear_nlogn (a b : ℕ) : ∃ C N₀, ∀ L ≥ N₀, a * L + b ≤ C * L * Nat.log2 L := by
  refine ⟨a + b, 2, fun L hL => ?_⟩
  have hlog := one_le_log2_of_two_le hL
  have h1 : (a + b) * L ≤ (a + b) * L * Nat.log2 L := Nat.le_mul_of_pos_right _ hlog
  have h2 : a * L + b ≤ (a + b) * L := by
    rw [Nat.add_mul]
    have : b ≤ b * L := Nat.le_mul_of_pos_right _ (by omega)
    omega
  omega

section AcceptShape

variable {W σ : Type} [DecidableEq W] [Fintype W] [Fintype σ]

/-- **Acceptance-theorem shape** from an evaluation spec and an `O(L log L)` source-time bound. -/
theorem acceptance_of_spec {α αΓ : Type} [Fintype αΓ] (ea : Encoding α αΓ) (f : α → ℕ)
    (p : Prog (StackId W) (StackId.Γ αΓ) σ) (σ0 : σ) (T : ℕ → ℕ)
    (hspec : ∀ a, ∃ v t, Eval [] p ⟨σ0, inputStk (ea.encode a)⟩
      ⟨v, outputStk (encodeNat (f a))⟩ t ∧ t ≤ T (ea.encode a).length)
    (hT : ∃ C N₀, ∀ L ≥ N₀, T L ≤ C * L * Nat.log2 L) :
    ∃ M : TM2ComputableInTime ea.encode encodingNatBool.encode f,
      (∀ k, Finite (M.tm.Γ k)) ∧ ∃ C N₀, ∀ L ≥ N₀, M.time L ≤ C * L * Nat.log2 L :=
  ⟨acceptTM ea f p σ0 T hspec, acceptTM_finite, nlogn_add_one hT⟩

/-- Same, from a `Triple` spec. -/
theorem acceptance_of_triple {α αΓ : Type} [Fintype αΓ] (ea : Encoding α αΓ) (f : α → ℕ)
    (p : Prog (StackId W) (StackId.Γ αΓ) σ) (σ0 : σ) (T : ℕ → ℕ)
    (hspec : ∀ a, Triple [] (· = ⟨σ0, inputStk (ea.encode a)⟩) p
      (fun s => s.stk = outputStk (encodeNat (f a))) (T (ea.encode a).length))
    (hT : ∃ C N₀, ∀ L ≥ N₀, T L ≤ C * L * Nat.log2 L) :
    ∃ M : TM2ComputableInTime ea.encode encodingNatBool.encode f,
      (∀ k, Finite (M.tm.Γ k)) ∧ ∃ C N₀, ∀ L ≥ N₀, M.time L ≤ C * L * Nat.log2 L := by
  refine acceptance_of_spec ea f p σ0 T (fun a => ?_) hT
  obtain ⟨s', t, he, hq, ht⟩ := hspec a _ rfl
  refine ⟨s'.var, t, ?_, ht⟩
  rw [← hq]
  exact he

end AcceptShape

end TMFw
