/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Desc

/-!
# Framed procedure calculus, pilot (`Calculus/Pilot.lean`): a binary recursive procedure, end to end

A small recursive TM2 procedure, proved with the calculus only, to validate the interface. It has
two recursive calls per node, a descriptor stack, protected tails and parking.

**The procedure** `pilot = fix pilotBody` on five stacks `desc, acc, park, t1, t2`. The descriptor
is a counter `natSyms k` on top of `desc`.
* Leaf (`k = 0`): push one `1` on `acc`.
* Node (`k + 1`): push the child descriptor `k` above a `mark` (`pushPred`); first child
  (`recur 0`), which leaves its block `B` on `acc`; park `B` and run the second child with `acc` in
  its frame-tail state (`parkCall`); unpark `B` on top of the second child's block; pop the child
  descriptor (`popDesc`).

**The theorem** `pilot_runs`: for every `k` and all stacks with a number terminator below the
descriptor and frame tails on `acc` and `park`, `pilot` pushes exactly `2^k` one-bits on `acc` and
restores every other stack, within `pilotT k + 4` steps, where `pilotT` is the cost recurrence
`pilotT (k+1) = 2·pilotT k + 6·2^k + O(log k)`; `pilotT_le : pilotT k ≤ 52·(k+1)·2^k`.

The proof uses `runs_descRec` (induction on the descriptor), `runs_pushPred`, `runs_popDesc`,
`runsIn_parkCall` and the closed-component rule `RunsIn.of_runs`.
-/

namespace SubNLogN.Machine.Calculus.Pilot

open Computability TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

/-- Stacks of the pilot. -/
inductive PK
  | desc | acc | park | t1 | t2
  deriving DecidableEq

/-- The identity lens. -/
def idLens (σ : Type) : Lens σ σ where
  get := id
  set _ w := w
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- `n` one-bits. -/
def ones (n : ℕ) : List Sym := (List.replicate n true).map Sym.bit

theorem ones_add (a b : ℕ) : ones (a + b) = ones a ++ ones b := by
  unfold ones
  rw [List.replicate_add, List.map_append]

theorem length_ones (n : ℕ) : (ones n).length = n := by
  simp [ones]

/-- Leaf (descriptor `0`): push one `1` on `acc`. -/
def pilotLeaf : SProg PK := pushC .acc (.bit true)

/-- Internal node (descriptor `k + 1`). -/
def pilotInternal : SProg PK :=
  .seq (pushPred .desc .t1 .t2) (.seq (.recur 0)
    (.seq (parkCall (idLens _) .acc .park (.recur 0)) (popDesc .desc)))

/-- The body. -/
def pilotBody : SProg PK := descBody (idLens _) .desc pilotLeaf pilotInternal

/-- **The pilot procedure.** -/
def pilot : SProg PK := .fix pilotBody

/-- Spec instances: descriptor `k` above a number terminator, frame tails on `acc` and `park`. -/
def PilotPre (k : ℕ) (S : PK → List Sym) : Prop :=
  (∃ tl, TermOK tl ∧ S .desc = natSyms k ++ tl) ∧ FrameTail (S .acc) ∧ FrameTail (S .park)

/-- The pilot's cost recurrence (step bound of the body). -/
def pilotT : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * pilotT k + 6 * 2 ^ k + 22 * bitLen (k + 1) + 2 * bitLen k + 51

/-- The leaf. -/
theorem runs_pilotLeaf (S : PK → List Sym) :
    Runs pilotLeaf S (Function.update S .acc (ones (2 ^ 0) ++ S .acc)) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, by
    have h := Eval.push ([] : List (SProg PK)) PK.acc (fun _ => Sym.bit true) v S
    have e : ones (2 ^ 0) ++ S PK.acc = Sym.bit true :: S PK.acc := by simp [ones]
    rw [e]
    exact h, trivial, le_rfl⟩

theorem ones_pow_succ (k : ℕ) : ones (2 ^ (k + 1)) = ones (2 ^ k) ++ ones (2 ^ k) := by
  rw [pow_succ, Nat.mul_two, ones_add]

/-- **The pilot, end to end.** From stacks with descriptor `k` on `desc` (above a number
terminator) and frame tails on `acc` and `park`, `pilot` pushes exactly `2^k` one-bits on `acc`
and restores every other stack, within `pilotT k + 4` steps. -/
theorem pilot_runs (k : ℕ) (S : PK → List Sym) (hpre : PilotPre k S) :
    Runs pilot S (Function.update S .acc (ones (2 ^ k) ++ S .acc)) (fun _ => True)
      (pilotT k + 4) := by
  have key := runs_descRec (idLens (Option Sym)) PK.desc (leaf := pilotLeaf)
    (internal := pilotInternal) (X := {x : ℕ × (PK → List Sym) // PilotPre x.1 x.2})
    (fun x => x.1.1) (S := fun x => x.1.2)
    (S' := fun x => Function.update x.1.2 .acc (ones (2 ^ x.1.1) ++ x.1.2 .acc))
    (T := fun x => pilotT x.1.1) (fun x => x.2.1) ?_ ?_
  · exact key ⟨(k, S), hpre⟩
  · rintro ⟨⟨k, S⟩, hpre⟩ h0
    dsimp only at h0 ⊢
    subst h0
    exact RunsIn.of_runs (runs_pilotLeaf S)
      (by simp [Prog.Closed, pilotLeaf, pushC, Prog.FreeBelow]) _
  · rintro ⟨⟨k, S⟩, hpre⟩ hk ih
    dsimp only at hk ⊢
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨⟨tl, htl, hSd⟩, hacc, hpark⟩ := hpre
    have hSd' : S .desc = natSyms (k + 1) ++ tl := hSd
    -- 1. push the child descriptor `k`
    have e1 := RunsIn.of_runs (runs_pushPred (d := PK.desc) (t1 := PK.t1) (t2 := PK.t2)
      (by decide) (by decide) (by decide) k tl S htl hSd) (closed_pushPred _ _ _)
      [descBody (idLens (Option Sym)) PK.desc pilotLeaf pilotInternal]
    set S1 := Function.update S .desc (natSyms k ++ Sym.mark :: (natSyms (k + 1) ++ tl)) with hS1
    have hS1acc : S1 .acc = S .acc := by rw [hS1, Function.update_of_ne (by decide)]
    have hS1park : S1 .park = S .park := by rw [hS1, Function.update_of_ne (by decide)]
    have pre1 : PilotPre k S1 := by
      refine ⟨⟨Sym.mark :: (natSyms (k + 1) ++ tl), TermOK.cons (by rfl) _,
        by rw [hS1, Function.update_self]⟩, ?_, ?_⟩
      · rw [hS1acc]; exact hacc
      · rw [hS1park]; exact hpark
    -- 2. first child
    have e2 := ih ⟨(k, S1), pre1⟩ (Nat.lt_succ_self k)
    dsimp only at e2
    set S2 := Function.update S1 .acc (ones (2 ^ k) ++ S1 .acc) with hS2
    have hS2acc : S2 .acc = ones (2 ^ k) ++ S .acc := by rw [hS2, Function.update_self, hS1acc]
    -- 3. second child, with the first child's block parked
    set S3 := Function.update (Function.update S2 .acc (S .acc)) .park
      (Sym.mark :: ((ones (2 ^ k)).reverse ++ Sym.mark :: S2 .park)) with hS3
    have pre3 : PilotPre k S3 := by
      refine ⟨⟨Sym.mark :: (natSyms (k + 1) ++ tl), TermOK.cons (by rfl) _, ?_⟩, ?_, ?_⟩
      · rw [hS3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS2,
          Function.update_of_ne (by decide), hS1, Function.update_self]
      · rw [hS3, Function.update_of_ne (by decide), Function.update_self]
        exact hacc
      · rw [hS3, Function.update_self]
        exact FrameTail.mark _
    have e3c := ih ⟨(k, S3), pre3⟩ (Nat.lt_succ_self k)
    dsimp only at e3c
    have e3 := runsIn_parkCall (idLens (Option Sym)) (r := PK.acc) (p := PK.park) (by decide)
      (ones (2 ^ k)) (S .acc) (MarkFree.bits _) hacc hS2acc e3c
      (by rw [Function.update_of_ne (by decide), hS3, Function.update_self])
    set S3' := Function.update S3 .acc (ones (2 ^ k) ++ S3 .acc) with hS3'
    set S4 := Function.update (Function.update S3' .park (S2 .park)) .acc
      (ones (2 ^ k) ++ S3' .acc) with hS4
    -- 4. pop the child descriptor
    have hS4d : S4 .desc = natSyms k ++ Sym.mark :: (natSyms (k + 1) ++ tl) := by
      rw [hS4, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS3',
        Function.update_of_ne (by decide), hS3, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hS2, Function.update_of_ne (by decide), hS1,
        Function.update_self]
    have e4 := RunsIn.of_runs (runs_popDesc (d := PK.desc) k (natSyms (k + 1) ++ tl) S4 hS4d)
      (closed_popDesc _) [descBody (idLens (Option Sym)) PK.desc pilotLeaf pilotInternal]
    have efin : Function.update S4 .desc (natSyms (k + 1) ++ tl) =
        Function.update S .acc (ones (2 ^ (k + 1)) ++ S .acc) := by
      funext j
      cases j <;> simp [hS4, hS3', hS3, hS2, hS1, hSd', ones_pow_succ]
    refine RunsIn.congr (RunsIn.seq e1 (RunsIn.seq e2 (RunsIn.seq e3 e4))) efin ?_
    rw [length_ones]
    simp only [pilotT]
    omega

/-- The cost recurrence is `O(k·2^k)`: `pilotT k ≤ 52·(k+1)·2^k`. -/
theorem pilotT_le : ∀ k, pilotT k ≤ 52 * (k + 1) * 2 ^ k
  | 0 => by simp [pilotT]
  | k + 1 => by
    have ih := pilotT_le k
    have hb1 : bitLen (k + 1) ≤ k + 1 := WP.W0m.bitLen_le_self _
    have hb0 : bitLen k ≤ k := WP.W0m.bitLen_le_self _
    have hk : k < 2 ^ k := Nat.lt_two_pow_self
    simp only [pilotT]
    have e : 52 * (k + 1 + 1) * 2 ^ (k + 1) = 2 * (52 * (k + 1) * 2 ^ k) + 104 * 2 ^ k := by ring
    rw [e]
    omega

/-- **The pilot from empty stacks**: descriptor `k` alone on `desc` gives exactly `2^k` one-bits on
`acc` and everything else as before, within `52·(k+1)·2^k + 4` steps. -/
theorem pilot_runs_empty (k : ℕ) :
    Runs pilot (Function.update (fun _ => []) .desc (natSyms k))
      (Function.update (Function.update (fun _ => []) .desc (natSyms k)) .acc (ones (2 ^ k)))
      (fun _ => True) (52 * (k + 1) * 2 ^ k + 4) := by
  have h := pilot_runs k (Function.update (fun _ => []) .desc (natSyms k))
    ⟨⟨[], TermOK.nil, by simp⟩, by simp [FrameTail.nil], by simp [FrameTail.nil]⟩
  have e : Function.update (Function.update (fun _ => []) PK.desc (natSyms k)) PK.acc
      (ones (2 ^ k) ++ Function.update (fun _ => []) PK.desc (natSyms k) PK.acc) =
      Function.update (Function.update (fun _ => []) PK.desc (natSyms k)) PK.acc (ones (2 ^ k)) := by
    simp
  rw [e] at h
  exact WP.W0m.runs_mono h (fun _ h => h) (by have := pilotT_le k; omega)

#assert_std_axioms ones_add length_ones runs_pilotLeaf ones_pow_succ pilot_runs pilotT_le
  pilot_runs_empty

end SubNLogN.Machine.Calculus.Pilot
