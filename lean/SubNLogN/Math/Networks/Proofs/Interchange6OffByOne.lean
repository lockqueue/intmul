import SubNLogN.Math.Networks.AppCProc6b
import SubNLogN.Math.Networks.Proofs.Interchange6Common

/-!
# Lemma A.8 (`lem:transfer12`) for binary fields whose widths differ by one bit

Proof of the contract `Interchange6OffByOneStmt` (`AppCProc6b.lean`; Lemma A.8 (`lem:transfer12`),
Appendix A.3 (`sec:transfer-arbitrary`), [OAI26, §4.3, Lemma 12]).

## Proof
Every map involved is a field relabelling (`fieldTransport`), possibly composed with the equal-width
interchange `Step.swapBlocks`. The latter reads field `swapSrc j` at field `j` when both chunks are
binary (`Interchange6Aux.swapPull_val`). Two arrays obtained in this way agree once the field indices
they read agree. Those indices are explicit piecewise-linear maps (`rot3Bwd`, `swapSrc`), compared by
case analysis (`split_ifs`, `omega`). The range conjuncts reduce to the same case analysis: field by
field, either the two read fields coincide, or both lie in the binary chunks.
-/

namespace SubNLogN.Math.Networks

open Model

namespace Interchange6OffByOneAux

open Interchange6Aux

/-- Field values of a relabelled address. -/
theorem fieldTransport_val {L L'' : Layout} (σ : Fin L''.n ≃ Fin L.n)
    (hr : ∀ i, L''.r i = L.r (σ i)) (y : L''.Addr) (j : Fin L.n) :
    (fieldTransport L L'' σ hr y j).val = (y (σ.symm j)).val := by
  simp [fieldTransport]

/-- Fields with equal indices have equal values. -/
theorem val_congr_idx {L : Layout} (y : L.Addr) {p q : Fin L.n} (h : p.val = q.val) :
    (y p).val = (y q).val := by
  rw [Fin.ext h]

/-- `swapPull_val` with the read field given as an arbitrary `Fin` with the right index. -/
theorem swapPull_val' {L : Layout} {r len t₀ s₀ : ℕ} (hb : TwoBlocks L r len t₀ s₀) (x : L.Addr)
    (j k : Fin L.n) (hk : k.val = swapSrc t₀ s₀ len j.val) :
    (swapPull L t₀ s₀ len x j).val = (x k).val := by
  rw [swapPull_val hb x j]
  exact val_congr_idx x hk.symm

theorem rot3Perm_apply {n t₀ a s₀ b : ℕ} (H : t₀ + a ≤ s₀ ∧ s₀ + b ≤ n) (i : Fin n) :
    (rot3Perm n t₀ a s₀ b i).val = rot3Fwd t₀ a s₀ b i.val := by
  simp [rot3Perm, dif_pos H]

theorem rot3Perm_symm_apply {n t₀ a s₀ b : ℕ} (H : t₀ + a ≤ s₀ ∧ s₀ + b ≤ n) (j : Fin n) :
    ((rot3Perm n t₀ a s₀ b).symm j).val = rot3Bwd t₀ a s₀ b j.val := by
  simp [rot3Perm, dif_pos H]

/-- Range conjunct, earlier field longer. -/
theorem rangeX {L : Layout} {u t₀ s₀ : ℕ} (h1 : t₀ + (u + 1) ≤ s₀) (h2 : s₀ + u ≤ L.n)
    (hbin : ∀ i : Fin L.n, (t₀ ≤ i.val ∧ i.val < t₀ + (u + 1)) ∨ (s₀ ≤ i.val ∧ i.val < s₀ + u) →
      L.r i = 2) (i : Fin L.n) :
    (rot3Layout L t₀ (u + 1) s₀ u).r i = L.r (rot3Perm L.n t₀ 1 s₀ 0 i) := by
  show L.r (rot3Perm L.n t₀ (u + 1) s₀ u i) = L.r (rot3Perm L.n t₀ 1 s₀ 0 i)
  have hjv := rot3Perm_apply (n := L.n) (t₀ := t₀) (a := u + 1) (s₀ := s₀) (b := u) ⟨h1, h2⟩ i
  have hkv := rot3Perm_apply (n := L.n) (t₀ := t₀) (a := 1) (s₀ := s₀) (b := 0)
    ⟨by omega, by omega⟩ i
  generalize rot3Perm L.n t₀ (u + 1) s₀ u i = j at hjv ⊢
  generalize rot3Perm L.n t₀ 1 s₀ 0 i = k at hkv ⊢
  have key : j.val = k.val ∨
      (((t₀ ≤ j.val ∧ j.val < t₀ + (u + 1)) ∨ (s₀ ≤ j.val ∧ j.val < s₀ + u)) ∧
        ((t₀ ≤ k.val ∧ k.val < t₀ + (u + 1)) ∨ (s₀ ≤ k.val ∧ k.val < s₀ + u))) := by
    rw [hjv, hkv]
    have := i.isLt
    unfold rot3Fwd
    split_ifs <;> omega
  rcases key with heq | ⟨hjb, hkb⟩
  · rw [Fin.ext heq]
  · rw [hbin j hjb, hbin k hkb]

/-- Range conjunct, later field longer. -/
theorem rangeY {L : Layout} {u t₀ s₀ : ℕ} (h1 : t₀ + u ≤ s₀) (h2 : s₀ + (u + 1) ≤ L.n)
    (hbin : ∀ i : Fin L.n, (t₀ ≤ i.val ∧ i.val < t₀ + u) ∨ (s₀ ≤ i.val ∧ i.val < s₀ + (u + 1)) →
      L.r i = 2) (i : Fin L.n) :
    (rot3Layout L t₀ u s₀ (u + 1)).r i = (rot3Layout L t₀ 0 s₀ 1).r i := by
  show L.r (rot3Perm L.n t₀ u s₀ (u + 1) i) = L.r (rot3Perm L.n t₀ 0 s₀ 1 i)
  have hjv := rot3Perm_apply (n := L.n) (t₀ := t₀) (a := u) (s₀ := s₀) (b := u + 1) ⟨h1, h2⟩ i
  have hkv := rot3Perm_apply (n := L.n) (t₀ := t₀) (a := 0) (s₀ := s₀) (b := 1)
    ⟨by omega, by omega⟩ i
  generalize rot3Perm L.n t₀ u s₀ (u + 1) i = j at hjv ⊢
  generalize rot3Perm L.n t₀ 0 s₀ 1 i = k at hkv ⊢
  have key : j.val = k.val ∨
      (((t₀ ≤ j.val ∧ j.val < t₀ + u) ∨ (s₀ ≤ j.val ∧ j.val < s₀ + (u + 1))) ∧
        ((t₀ ≤ k.val ∧ k.val < t₀ + u) ∨ (s₀ ≤ k.val ∧ k.val < s₀ + (u + 1)))) := by
    rw [hjv, hkv]
    have := i.isLt
    unfold rot3Fwd
    split_ifs <;> omega
  rcases key with heq | ⟨hjb, hkb⟩
  · rw [Fin.ext heq]
  · rw [hbin j hjb, hbin k hkb]

/-- Earlier field longer: interchange, then the single-bit move of field `t₀` to `s₀ − 1`. -/
theorem caseX {L : Layout} {β : Type} {u t₀ s₀ : ℕ} (A : L.Addr → β) (h1 : t₀ + (u + 1) ≤ s₀)
    (h2 : s₀ + u ≤ L.n)
    (hbin : ∀ i : Fin L.n, (t₀ ≤ i.val ∧ i.val < t₀ + (u + 1)) ∨ (s₀ ≤ i.val ∧ i.val < s₀ + u) →
      L.r i = 2)
    (h : ∀ i, (rot3Layout L t₀ (u + 1) s₀ u).r i = L.r (rot3Perm L.n t₀ 1 s₀ 0 i)) :
    rot3Run L t₀ (u + 1) s₀ u A =
      (Step.swapBlocks (t₀ + 1) s₀ u : Step L β).run A ∘
        fieldTransport L (rot3Layout L t₀ (u + 1) s₀ u) (rot3Perm L.n t₀ 1 s₀ 0) h := by
  have HA : t₀ + (u + 1) ≤ s₀ ∧ s₀ + u ≤ L.n := ⟨h1, h2⟩
  have HB : t₀ + 1 ≤ s₀ ∧ s₀ + 0 ≤ L.n := ⟨by omega, by omega⟩
  have htb : TwoBlocks L 2 u (t₀ + 1) s₀ := ⟨by omega, h2, fun i hi => hbin i (by omega)⟩
  rw [swapBlocks_run]
  funext y
  simp only [rot3Run, Function.comp]
  congr 1
  funext j
  refine Fin.ext ?_
  rw [swapPull_val htb, fieldTransport_val, fieldTransport_val]
  apply val_congr_idx
  rw [rot3Perm_symm_apply HA, rot3Perm_symm_apply HB]
  show rot3Bwd t₀ (u + 1) s₀ u j.val = rot3Bwd t₀ 1 s₀ 0 (swapSrc (t₀ + 1) s₀ u j.val)
  have := j.isLt
  unfold rot3Bwd swapSrc
  split_ifs <;> omega

/-- Later field longer: the single-bit move of field `s₀` to `t₀`, then the interchange on the
moved layout. -/
theorem caseY {L : Layout} {β : Type} {u t₀ s₀ : ℕ} (A : L.Addr → β) (h1 : t₀ + u ≤ s₀)
    (h2 : s₀ + (u + 1) ≤ L.n)
    (hbin : ∀ i : Fin L.n, (t₀ ≤ i.val ∧ i.val < t₀ + u) ∨ (s₀ ≤ i.val ∧ i.val < s₀ + (u + 1)) →
      L.r i = 2)
    (h : ∀ i, (rot3Layout L t₀ u s₀ (u + 1)).r i = (rot3Layout L t₀ 0 s₀ 1).r i) :
    rot3Run L t₀ u s₀ (u + 1) A =
      (Step.swapBlocks (t₀ + 1) (s₀ + 1) u : Step (rot3Layout L t₀ 0 s₀ 1) β).run
          (rot3Run L t₀ 0 s₀ 1 A) ∘
        fieldTransport (rot3Layout L t₀ 0 s₀ 1) (rot3Layout L t₀ u s₀ (u + 1)) (Equiv.refl _) h := by
  have HA : t₀ + u ≤ s₀ ∧ s₀ + (u + 1) ≤ L.n := ⟨h1, h2⟩
  have HB : t₀ + 0 ≤ s₀ ∧ s₀ + 1 ≤ L.n := ⟨by omega, by omega⟩
  have htb : TwoBlocks (rot3Layout L t₀ 0 s₀ 1) 2 u (t₀ + 1) (s₀ + 1) := by
    refine ⟨by omega, show s₀ + 1 + u ≤ L.n by omega, fun i hi => ?_⟩
    show L.r (rot3Perm L.n t₀ 0 s₀ 1 i) = 2
    apply hbin
    rw [rot3Perm_apply HB]
    have := i.isLt
    have hi' : (t₀ + 1 ≤ i.val ∧ i.val < t₀ + 1 + u) ∨ (s₀ + 1 ≤ i.val ∧ i.val < s₀ + 1 + u) := hi
    unfold rot3Fwd
    split_ifs <;> omega
  rw [swapBlocks_run]
  funext y
  simp only [rot3Run, Function.comp]
  congr 1
  funext j
  refine Fin.ext ?_
  have hbound : swapSrc (t₀ + 1) (s₀ + 1) u ((rot3Perm L.n t₀ 0 s₀ 1).symm j).val < L.n := by
    have := ((rot3Perm L.n t₀ 0 s₀ 1).symm j).isLt
    unfold swapSrc
    split_ifs <;> omega
  rw [fieldTransport_val, fieldTransport_val,
    swapPull_val' htb _ _ ⟨swapSrc (t₀ + 1) (s₀ + 1) u ((rot3Perm L.n t₀ 0 s₀ 1).symm j).val, hbound⟩
      rfl]
  refine Eq.trans ?_ (fieldTransport_val (L := rot3Layout L t₀ 0 s₀ 1)
    (L'' := rot3Layout L t₀ u s₀ (u + 1)) (Equiv.refl _) h y _).symm
  apply val_congr_idx
  rw [rot3Perm_symm_apply HA]
  simp only [Equiv.refl_symm, Equiv.refl_apply]
  rw [rot3Perm_symm_apply HB]
  have := j.isLt
  unfold rot3Bwd swapSrc
  split_ifs <;> omega

end Interchange6OffByOneAux

open Interchange6OffByOneAux in
/-- **Lemma A.8 (`lem:transfer12`), widths differing by one bit** (Appendix A.3 (`sec:transfer-arbitrary`)): the contract
`Interchange6OffByOneStmt`. -/
theorem interchange6OffByOne_holds : Interchange6OffByOneStmt :=
  ⟨fun _ _ _ _ _ A h1 h2 hbin => ⟨rangeX h1 h2 hbin, fun h => caseX A h1 h2 hbin h⟩,
    fun _ _ _ _ _ A h1 h2 hbin => ⟨rangeY h1 h2 hbin, fun h => caseY A h1 h2 hbin h⟩⟩

end SubNLogN.Math.Networks
