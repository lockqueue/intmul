/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7RepairDefs
import SubNLogN.Machine.AppC.C7RepairMath
import SubNLogN.Machine.AppC.C7Reinsert

/-!
# Lemma A.9 repair phase from its parts (`Machine/AppC/C7Repair.lean`)

`c7Repair_of_parts : C7ExtractStmt σ → C7RepairGlueStmt τ σ → C7RepairStmt τ σ` (0 `sorry`). The
repair kernel runs, on `KLoc (Fin 8) (Fin 6 ⊕ E)` (six work stacks `H, Bk, Ac, b0, b1, t`, then the
extraction kernel's private scratch `E`):

1. the extraction kernel (`C7ExtractStmt`, via `callInj`): skeleton on `H`, bank on `Bk`, key width
   `A = c7KeyWidth M` on `Ac`;
2. the radix sort `rsSortProg Bk b0 b1 Ac t` (`rsSort_runs`), then `popR Ac` (the `mark`);
3. the reinsertion `rinProg H Bk b0 0` (`rinProg_runs`), then `popR Bk` (the bank terminator).

The final array is `fillHoles (holes …) ((rsSort A (bank …)).map snd) = permByInv (c7RepairInv …) w`
(`repair_fill`, `C7RepairMath.lean`). All work stacks end as they started (restored convention).
`C7RepairGlueStmt` collects the small pure facts used (hole count, record lengths, key width, cost
arithmetic); it is proved in `C7RepairGlue.lean`. (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Math.Networks AppC.C7Aux AppC.C7RadixAux
  AppC.C7RepairAux AppC.C7RepairAux.Math SubNLogN.Machine.Calculus

/-- **[MATH] Glue facts for the repair composition.** For valid parameters and an array
`w` of `M = c7M …` records of `R` bits, with `A = c7KeyWidth M`, `L = lgVol (vol w)`: the skeleton has
as many holes as the bank has records; kept records, bank keys and payloads have lengths `R`, `A`,
`R`; `1 ≤ A` and `M ≤ 2 ^ A`; the sort, reinsertion and two pops cost at most `64 · c7Cost`, and the
extraction budget `M (L + 1)^3 + V + badMax · (L + 1) + 1` is at most `2 · c7Cost`. -/
def C7RepairGlueStmt (τ : ℝ) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ (K ρ f N0 N1 N2 N3 R : ℕ) (w : List (List Bool)),
    6 ≤ K → ρ < K → 1 ≤ f → 1 ≤ N0 → 1 ≤ N1 → 1 ≤ N2 → 1 ≤ N3 → 1 ≤ R →
    w.length = c7M K f N0 N1 N2 N3 → (∀ p ∈ w, p.length = R) →
    holeCount (holes K ρ f N1 N2 N3 σ w) =
        (bank K ρ f N1 N2 N3 σ (c7KeyWidth w.length) w).length ∧
      (∀ p, some p ∈ holes K ρ f N1 N2 N3 σ w → p.length = R) ∧
      (∀ r ∈ bank K ρ f N1 N2 N3 σ (c7KeyWidth w.length) w,
        r.1.length = c7KeyWidth w.length ∧ r.2.length = R) ∧
      1 ≤ c7KeyWidth w.length ∧ w.length ≤ 2 ^ c7KeyWidth w.length ∧
      countdownCost (fun _ => (bank K ρ f N1 N2 N3 σ (c7KeyWidth w.length) w).length *
          (8 * c7KeyWidth w.length + 8 * R + 17) + 10) (c7KeyWidth w.length) +
        (1 + ((holes K ρ f N1 N2 N3 σ w).length * (3 * c7KeyWidth w.length + 8 * R + 16) + 7 + 1)) ≤
        64 * c7Cost τ K f w.length (vol w) R ∧
      w.length * (lgVol (vol w) + 1) ^ 3 + vol w + badMax K f w.length * (lgVol (vol w) + 1) + 1 ≤
        2 * c7Cost τ K f w.length (vol w) R

namespace AppC.C7RepairAux

/-- Embedding of the extraction layout into the repair layout. -/
def repIota (E : Type) : KLoc (Fin 8 ⊕ Fin 3) E → KLoc (Fin 8) (Fin 6 ⊕ E)
  | .inl (.inl i) => .inl i
  | .inl (.inr j) => .inr (.inl ⟨j.val, by omega⟩)
  | .inr e => .inr (.inr e)

theorem repIota_injective (E : Type) : Function.Injective (repIota E) := by
  intro a b h
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;> simp [repIota, Fin.ext_iff] at h ⊢ <;>
    exact h

/-- Work stacks of the repair kernel. -/
def repH (E : Type) : KLoc (Fin 8) (Fin 6 ⊕ E) := repIota E (.inl (.inr 0))
def repBk (E : Type) : KLoc (Fin 8) (Fin 6 ⊕ E) := repIota E (.inl (.inr 1))
def repAc (E : Type) : KLoc (Fin 8) (Fin 6 ⊕ E) := repIota E (.inl (.inr 2))
def repB0 (E : Type) : KLoc (Fin 8) (Fin 6 ⊕ E) := .inr (.inl 3)
def repB1 (E : Type) : KLoc (Fin 8) (Fin 6 ⊕ E) := .inr (.inl 4)
def repT (E : Type) : KLoc (Fin 8) (Fin 6 ⊕ E) := .inr (.inl 5)

/-- The repair program. -/
def repProg (E RE : Type) (PE : Prog (KLoc (Fin 8 ⊕ Fin 3) E) (fun _ => Sym) RE) :
    Prog (KLoc (Fin 8) (Fin 6 ⊕ E)) (fun _ => Sym) (RE × Option Sym) :=
  .seq (callInj (repIota E) (Lens.fst RE (Option Sym)) PE)
    (.seq ((rsSortProg (repBk E) (repB0 E) (repB1 E) (repAc E) (repT E)).liftRegs
        (Lens.snd RE (Option Sym)))
      (.seq ((popR (repAc E)).liftRegs (Lens.snd RE (Option Sym)))
        (.seq ((rinProg (repH E) (repBk E) (repB0 E) (.inl 0)).liftRegs (Lens.snd RE (Option Sym)))
          ((popR (repBk E)).liftRegs (Lens.snd RE (Option Sym))))))

theorem closed_repProg (E RE : Type) {PE : Prog (KLoc (Fin 8 ⊕ Fin 3) E) (fun _ => Sym) RE}
    (hc : PE.Closed) : (repProg E RE PE).Closed :=
  ⟨closed_callInj _ _ hc, WP.W9comp.closed_liftRegs _ (closed_rsSortProg _ _ _ _ _),
    WP.W9comp.closed_liftRegs _ trivial, WP.W9comp.closed_liftRegs _ (closed_rinProg _ _ _ _),
    WP.W9comp.closed_liftRegs _ trivial⟩

end AppC.C7RepairAux

/-! ## The composition -/

/-- **The repair phase from the extraction kernel** (`c7Repair_of_parts`, 0 `sorry`): with the
glue facts, `C7ExtractStmt σ` gives `C7RepairStmt τ σ`; cost constant `2 C_E + 64`. -/
theorem c7Repair_of_parts (τ : ℝ) (σ : Equiv.Perm (Fin 3)) (hE : C7ExtractStmt σ)
    (hG : C7RepairGlueStmt τ σ) : C7RepairStmt τ σ := by
  intro _hprem
  obtain ⟨CE, hcE⟩ := hE
  refine ⟨2 * CE + 64, fun _ => ?_⟩
  obtain ⟨E, _, _, RE, PE, hfE, hnE, hclE, hsE⟩ := hcE ()
  refine ⟨Fin 6 ⊕ E, inferInstance, inferInstance, RE × Option Sym, repProg E RE PE,
    inferInstance, inferInstance, closed_repProg E RE hclE, ?_⟩
  intro K ρ f N0 N1 N2 N3 R w rest r1 r2 r3 r4 r5 r6 r7 S hK hρ hf hN0 hN1 hN2 hN3 hR hlen hrec
    hrest hr1 hr2 hr3 hr4 hr5 hr6 hr7 hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS7
  obtain ⟨hcnt, hhs, hbk, hA1, hA2, hcost1, hcost2⟩ :=
    hG K ρ f N0 N1 N2 N3 R w hK hρ hf hN0 hN1 hN2 hN3 hR hlen hrec
  -- distinctness of the work stacks
  have dHB : repH E ≠ repBk E := by simp [repH, repBk, repIota]
  have dH0 : repH E ≠ repB0 E := by simp [repH, repB0, repIota]
  have dHA : repH E ≠ repAc E := by simp [repH, repAc, repIota]
  have dB0 : repBk E ≠ repB0 E := by simp [repBk, repB0, repIota]
  have dB1 : repBk E ≠ repB1 E := by simp [repBk, repB1, repIota]
  have d01 : repB0 E ≠ repB1 E := by simp [repB0, repB1]
  have dAB : repAc E ≠ repBk E := by simp [repAc, repBk, repIota]
  have dAT : repAc E ≠ repT E := by simp [repAc, repT, repIota]
  have dH : repH E ≠ (.inl 0 : KLoc (Fin 8) (Fin 6 ⊕ E)) := by simp [repH, repIota]
  have dB : repBk E ≠ (.inl 0 : KLoc (Fin 8) (Fin 6 ⊕ E)) := by simp [repBk, repIota]
  have dA : repAc E ≠ (.inl 0 : KLoc (Fin 8) (Fin 6 ⊕ E)) := by simp [repAc, repIota]
  have d0 : repB0 E ≠ (.inl 0 : KLoc (Fin 8) (Fin 6 ⊕ E)) := by simp [repB0]
  -- 1. extraction
  have e1 := hsE K ρ f N0 N1 N2 N3 R w rest r1 r2 r3 r4 r5 r6 r7 (S ∘ repIota E) hK hρ hf hN0 hN1
    hN2 hN3 hR hlen hrec hrest hr1 hr2 hr3 hr4 hr5 hr6 hr7 hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS7
  have X1 : Runs (callInj (repIota E) (Lens.fst RE (Option Sym)) PE) S
      (Function.update (Function.update (Function.update (Function.update S (.inl 0) rest)
        (repH E) (holeSyms (holes K ρ f N1 N2 N3 σ w) ++ Sym.tag 15 :: S (repH E)))
        (repBk E) (bankSyms (bank K ρ f N1 N2 N3 σ (c7KeyWidth w.length) w) ++
          bankEnd :: S (repBk E)))
        (repAc E) (natSyms (c7KeyWidth w.length) ++ Sym.mark :: S (repAc E)))
      (fun _ => True)
      (CE * (w.length * (lgVol (vol w) + 1) ^ 3 + vol w +
        badMax K f w.length * (lgVol (vol w) + 1) + 1)) := by
    refine runs_callInj (repIota_injective E) _ (Q := fun _ => True) ?_ ?_
    · convert e1 using 2
      funext x
      rcases x with (i | j) | e
      · simp [repIota, repH, repBk, repAc, Function.update_apply]
      · fin_cases j <;> simp [repIota, repH, repBk, repAc]
      · simp [repIota, repH, repBk, repAc]
    · intro k hk
      have h0 : k ≠ .inl 0 := fun h => hk (.inl (.inl 0)) (by rw [h]; rfl)
      have hH : k ≠ repH E := fun h => hk (.inl (.inr 0)) (by rw [h]; rfl)
      have hB : k ≠ repBk E := fun h => hk (.inl (.inr 1)) (by rw [h]; rfl)
      have hA : k ≠ repAc E := fun h => hk (.inl (.inr 2)) (by rw [h]; rfl)
      simp [h0, hH, hB, hA]
  -- 2. sort
  have hS1B : Function.update (Function.update (Function.update (Function.update S (.inl 0) rest)
        (repH E) (holeSyms (holes K ρ f N1 N2 N3 σ w) ++ Sym.tag 15 :: S (repH E)))
        (repBk E) (bankSyms (bank K ρ f N1 N2 N3 σ (c7KeyWidth w.length) w) ++
          bankEnd :: S (repBk E)))
        (repAc E) (natSyms (c7KeyWidth w.length) ++ Sym.mark :: S (repAc E)) (repBk E) =
      bankSyms (bank K ρ f N1 N2 N3 σ (c7KeyWidth w.length) w) ++ bankEnd :: S (repBk E) := by
    simp [dAB.symm]
  have hcount : holeCount (holes K ρ f N1 N2 N3 σ w) =
      (rsSort (c7KeyWidth w.length) (bank K ρ f N1 N2 N3 σ (c7KeyWidth w.length) w)).length := by
    rw [rsSort_length, hcnt]
  have X := RunsIn.seq (RunsIn.iff_runs.mpr X1)
    (RunsIn.seq (RunsIn.of_runs_liftRegs (Lens.snd RE (Option Sym))
      (rsSort_runs dB0 dB1 d01 dAB dAT hA1 _ hbk (S (repBk E)) (Sym.mark :: S (repAc E))
        (FrameTail.termOK (FrameTail.mark _)) _ hS1B (by simp)) (closed_rsSortProg _ _ _ _ _) [])
    (RunsIn.seq (RunsIn.of_runs_liftRegs (Lens.snd RE (Option Sym))
      (runs_popR_c (repAc E) _ Sym.mark (S (repAc E)) (by simp)) trivial [])
    (RunsIn.seq (RunsIn.of_runs_liftRegs (Lens.snd RE (Option Sym))
      (rinProg_runs (D := (.inl 0 : KLoc (Fin 8) (Fin 6 ⊕ E))) dHB dH0 dB0 d0 dH dB
        (holes K ρ f N1 N2 N3 σ w) _ hhs (rsSort_shape _ _ hbk) hcount (S (repH E))
        (bankEnd :: S (repBk E)) _
        (by simp [dHB, dHA])
        (by simp [dAB.symm])) (closed_rinProg _ _ _ _) [])
      (RunsIn.of_runs_liftRegs (Lens.snd RE (Option Sym))
        (runs_popR_c (repBk E) _ bankEnd (S (repBk E)) (by simp [Function.update_apply, dB]))
        trivial []))))
  have hfill := repair_fill σ hK hρ hf hN0 hN1 hN2 hN3 (c7KeyWidth w.length) w hlen (hlen ▸ hA2)
  show Runs _ S (Function.update S (.inl 0)
    (arrSyms (permByInv (c7RepairInv K ρ f N1 N2 N3 σ) w) ++ rest)) _ _
  rw [← hfill]
  refine RunsIn.iff_runs.mp (RunsIn.congr (RunsIn.mono X (fun _ _ => trivial) le_rfl) ?_ ?_)
  · funext k
    by_cases h0 : k = .inl 0
    · subst h0
      simp [dH.symm, dB.symm, dA.symm]
    · by_cases hH : k = repH E
      · subst hH
        simp [Function.update_apply, dHB, dH]
      · by_cases hB : k = repBk E
        · subst hB
          simp [Function.update_apply, dB]
        · by_cases hA : k = repAc E
          · subst hA
            simp [Function.update_apply, dAB, dHA.symm, dA]
          · simp [Function.update_apply, h0, hH, hB, hA]
  · calc CE * (w.length * (lgVol (vol w) + 1) ^ 3 + vol w +
          badMax K f w.length * (lgVol (vol w) + 1) + 1) +
          (countdownCost (fun _ => (bank K ρ f N1 N2 N3 σ (c7KeyWidth w.length) w).length *
            (8 * c7KeyWidth w.length + 8 * R + 17) + 10) (c7KeyWidth w.length) +
          (1 + ((holes K ρ f N1 N2 N3 σ w).length * (3 * c7KeyWidth w.length + 8 * R + 16) + 7 +
            1)))
        ≤ CE * (2 * c7Cost τ K f w.length (vol w) R) + 64 * c7Cost τ K f w.length (vol w) R :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hcost2) hcost1
      _ = (2 * CE + 64) * c7Cost τ K f w.length (vol w) R := by ring

end SubNLogN.Machine
