/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermLeaf

/-!
# K3-PERM (`Machine/Walsh/PosPermMath.lean`): value facts for the schedule of Theorem 5.8

**Scope (honest summary).** Proved lemmas (no machine programs) about the schedule
`posPermSched` (`Machine/Walsh/PosPermLeaf.lean`):
* `sched_erase`: erasing the commands to `WStep` programs (`Math/Walsh/PositionalPerm.lean`) gives `posPermProg`.
* `sched_ok`: every command satisfies the preconditions of its kernel (slice shape, disjoint pairs,
  targets in the slice; `c ≠ t` for single flips).
* `foldl_sched`: executing the commands' array effects (`cmdEff`) gives `posPermArr π` on disk
  arrays (`positional_perm` with the ideal layer oracle).
* `length_sched_le`, `nSlice_le_nat`: at most `6(N_slice + K)` commands, `N_slice ≤ m/d + K`.
-/

namespace SubNLogN.Machine.PosPermRed

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Walsh SubNLogN.Math.Walsh.PosPermAux
open SubNLogN.Math.Common

/-! ## Erasure to algebraic `WStep` programs -/

/-- A command as a `WStep` program (`Math/Walsh/PositionalPerm.lean`). -/
noncomputable def eraseCmd {m K : ℕ} (P d : ℕ) : PosCmd m K → List (WStep m)
  | .batch j₀ D nS ρ ps => cnotBatchProg P d K j₀ D nS ρ ps
  | .one c t => [.cnot1 c t]

theorem flatMap_singleton_eq_map {α β : Type} (l : List α) (f : α → β) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem slice_erase {m : ℕ} (P d K g : ℕ) (ρ : Fin K) (pairs : List (Fin m × Fin m)) :
    (sliceCmds m d K g ρ pairs).flatMap (eraseCmd P d) = batchProg P d K g ρ pairs := by
  unfold sliceCmds batchProg
  split_ifs <;> simp [eraseCmd]

theorem stage_erase {m : ℕ} (P d K : ℕ) (pairs : List (Fin m × Fin m)) :
    (stageCmds m d K pairs).flatMap (eraseCmd P d) = stageProg P d K pairs := by
  rw [stageProg_eq, stageCmds, List.flatMap_append]
  congr 1
  · simp only [List.flatMap_assoc, slice_erase]
  · rw [List.flatMap_map]
    exact flatMap_singleton_eq_map _ _

/-- **The schedule erases to `posPermProg`**: `(posPermSched).flatMap eraseCmd = posPermProg`. -/
theorem sched_erase {m : ℕ} (P d K : ℕ) (π : Fin m → Fin m) :
    (posPermSched m d K π).flatMap (eraseCmd P d) = posPermProg P d K π := by
  simp only [posPermSched, involCmds, List.flatMap_append, stage_erase, posPermProg, involProg]

/-! ## Preconditions and effects -/

/-- The array effect of a command. -/
def cmdEff {m K r : ℕ} : PosCmd m K → RArr (Cube m) r → RArr (Cube m) r
  | .batch _ _ _ _ ps => cnotArr ps
  | .one c t => cnotArr [(c, t)]

/-- The preconditions of a command's kernel (`CnotBatchMachineStmt`, `Cnot1MachineStmt`). -/
def CmdOK (m d K : ℕ) : PosCmd m K → Prop
  | .batch j₀ D nS ρ ps => j₀ + D * K + nS = m ∧ 1 ≤ D ∧ D ≤ d ∧ CnotPairsValid ps ∧
      targets ps ⊆ slicePos m K j₀ D ρ
  | .one c t => c ≠ t

theorem stageCmds_ok {m d K : ℕ} (hd : 1 ≤ d) {pairs : List (Fin m × Fin m)}
    (hv : CnotPairsValid pairs) : ∀ c ∈ stageCmds m d K pairs, CmdOK m d K c := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · simp only [List.mem_flatMap, List.mem_range, List.mem_finRange, true_and] at hc
    obtain ⟨g, hg, ρ, hc⟩ := hc
    unfold sliceCmds at hc
    split_ifs at hc with he
    · simp at hc
    · rw [List.mem_singleton] at hc
      subst hc
      refine ⟨?_, one_le_groupSize hd hg, groupSize_le _ _ _ _,
        valid_of_sublist hv List.filter_sublist, ?_⟩
      · have := groupEnd_le_m₀ (m₀ := m) (K := K) hd hg
        omega
      · intro t ht
        simp only [targets, List.mem_toFinset, List.mem_map] at ht
        obtain ⟨q, hq, rfl⟩ := ht
        exact (mem_batchPairs.1 hq).2
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    show p.1 ≠ p.2
    have hp' := (mem_leftPairs.1 hp).1
    intro h
    have hdisj := (List.nodup_append.1 hv).2.2
    exact hdisj _ (List.mem_map_of_mem hp') _ (List.mem_map_of_mem hp') h

/-- **Every command of the schedule satisfies its kernel's preconditions.** -/
theorem sched_ok {m d K : ℕ} (hd : 1 ≤ d) (π : Equiv.Perm (Fin m)) :
    ∀ c ∈ posPermSched m d K π, CmdOK m d K c := by
  obtain ⟨hI0, hI1, -⟩ := walsh_involutions π
  obtain ⟨hA0, hB0, -⟩ := involution_three_stages (r := 0) (invol0 ⇑π) hI0
  obtain ⟨hA1, hB1, -⟩ := involution_three_stages (r := 0) (invol1 ⇑π) hI1
  intro c hc
  simp only [posPermSched, involCmds, List.mem_append] at hc
  rcases hc with ((h | h) | h) | ((h | h) | h)
  · exact stageCmds_ok hd hA0 c h
  · exact stageCmds_ok hd hB0 c h
  · exact stageCmds_ok hd hA0 c h
  · exact stageCmds_ok hd hA1 c h
  · exact stageCmds_ok hd hB1 c h
  · exact stageCmds_ok hd hA1 c h

/-- The ideal layer oracle (every call returns `Q_P(H z)` exactly). -/
noncomputable def idealL : LayerOracle := fun P _ _ _ _ _ ρ z => truncArr P (layerH ρ z)

theorem runProg_erase {m K r : ℕ} (P d : ℕ) {c : PosCmd m K} (hc : CmdOK m d K c)
    {z : RArr (Cube m) r} (hz : ArrOnDiskGrid P z) :
    runProg idealL r (eraseCmd P d c) z = cmdEff c z := by
  cases c with
  | batch j₀ D nS ρ ps =>
    obtain ⟨hm, -, hDd, hv, ht⟩ := hc
    exact (cnot_batch idealL P d K j₀ D nS ρ ps hm hDd hv ht (fun _ _ => rfl) z hz).1
  | one c t => rfl

theorem cmdEff_diskGrid {m K r P : ℕ} (c : PosCmd m K) {z : RArr (Cube m) r}
    (hz : ArrOnDiskGrid P z) : ArrOnDiskGrid P (cmdEff c z) := by
  cases c <;> exact arrOnDiskGrid_cnotArr _ hz

theorem foldl_cmdEff {m K r : ℕ} (P d : ℕ) :
    ∀ (l : List (PosCmd m K)), (∀ c ∈ l, CmdOK m d K c) → ∀ z : RArr (Cube m) r,
      ArrOnDiskGrid P z →
      l.foldl (fun z c => cmdEff c z) z = runProg idealL r (l.flatMap (eraseCmd P d)) z
  | [], _, _, _ => rfl
  | c :: l, hl, z, hz => by
    rw [List.foldl_cons, List.flatMap_cons, runProg_append,
      runProg_erase P d (hl c List.mem_cons_self) hz]
    exact foldl_cmdEff P d l (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')) _
      (cmdEff_diskGrid c hz)

/-- **Executing the schedule performs the positional permutation** (Theorem 5.8, value part,
`positional_perm` in `Math/Walsh/PositionalPerm.lean`). -/
theorem foldl_sched {m r : ℕ} (P d K : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (π : Equiv.Perm (Fin m))
    (z : RArr (Cube m) r) (hz : ArrOnDiskGrid P z) :
    (posPermSched m d K π).foldl (fun z c => cmdEff c z) z = posPermArr π z := by
  rw [foldl_cmdEff P d _ (sched_ok hd π) z hz, sched_erase]
  exact (positional_perm idealL P d K hK hd (fun _ _ _ _ _ _ _ => fun _ _ => rfl) π).1 z hz

/-! ## Counts -/

theorem length_flatMap_le {α β : Type} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

theorem length_stageCmds_le {m d K : ℕ} (hK : 1 ≤ K) {pairs : List (Fin m × Fin m)}
    (hv : CnotPairsValid pairs) : (stageCmds m d K pairs).length ≤ nSlice m K d + K := by
  rw [stageCmds, List.length_append, List.length_map]
  have h1 : ((List.range (numGroups m K d)).flatMap fun g =>
      (List.finRange K).flatMap fun ρ => sliceCmds m d K g ρ pairs).length ≤ nSlice m K d := by
    have := length_flatMap_le (List.range (numGroups m K d))
      (fun g => (List.finRange K).flatMap fun ρ => sliceCmds m d K g ρ pairs) (K * 1)
      (fun g _ => by
        have := length_flatMap_le (List.finRange K) (fun ρ => sliceCmds m d K g ρ pairs) 1
          (fun ρ _ => by unfold sliceCmds; split_ifs <;> simp)
        simpa using this)
    simpa [nSlice, Nat.mul_comm] using this
  have h2 := leftPairs_length_le K hK pairs hv
  omega

/-- **The schedule has at most `6(N_slice + K)` commands.** -/
theorem length_sched_le {m d K : ℕ} (hK : 1 ≤ K) (π : Equiv.Perm (Fin m)) :
    (posPermSched m d K π).length ≤ 6 * (nSlice m K d + K) := by
  obtain ⟨hI0, hI1, -⟩ := walsh_involutions π
  obtain ⟨hA0, hB0, -⟩ := involution_three_stages (r := 0) (invol0 ⇑π) hI0
  obtain ⟨hA1, hB1, -⟩ := involution_three_stages (r := 0) (invol1 ⇑π) hI1
  simp only [posPermSched, involCmds, List.length_append]
  have := length_stageCmds_le (m := m) (d := d) hK hA0
  have := length_stageCmds_le (m := m) (d := d) hK hB0
  have := length_stageCmds_le (m := m) (d := d) hK hA1
  have := length_stageCmds_le (m := m) (d := d) hK hB1
  omega

/-- `N_slice ≤ m/d + K` in `ℕ` (from the real-valued bound `nSlice_le`). -/
theorem nSlice_le_nat (m K d : ℕ) (hd : 1 ≤ d) : nSlice m K d ≤ m / d + K := by
  have h := nSlice_le m K d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have h2 : (m : ℝ) / d < ((m / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hdpos]
    have := Nat.lt_div_mul_add (a := m) (b := d) (by omega)
    have h' : (m : ℝ) < ((m / d * d + d : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    linarith
  have h3 : (nSlice m K d : ℝ) < ((m / d + K + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h4 : nSlice m K d < m / d + K + 1 := by exact_mod_cast h3
  omega

end SubNLogN.Machine.PosPermRed
