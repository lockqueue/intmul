/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafSplitVal
import SubNLogN.Machine.CCore.LeafSplitCtr

/-!
# C-core leaves 6-7 (split / collect), part 4: layout and phases (`CCore/LeafSplitLay.lean`)

The private scratch of both kernels is `SE E₂ = Fin 6 ⊕ (Fin W ⊕ E₂)`: six work stacks (`TT` a
guarded temporary, `CB` the row-size counter, `CD`/`CK` the header copies of `D`/`K`, `CD2` the
copy of `D`, `HT` the header temporary), one private buffer per role, and the scratch `E₂` of the
embedded K2 kernel. All states are written `mkS io desc park role wk buf ex`.

Proved here (no hypotheses):
* `mkS` update/evaluation lemmas, `mkS_eta` (every state is an `mkS`);
* `safe_forEachFin_rb`: a fixed loop over the roles whose step `u` only changes role `u` and
  buffer `u` (used for the guards, the owned marks, and the buffer/role transfers);
* `ιK` (embedding of a K2 block-kernel layout into unframed stacks: `io`, `CB`, the buffers, the
  K2 scratch) and the embedded K2 kernels `safe_distCall`, `safe_mergeCall` (boundary safe via
  `SafeRunsIn.callInj` with an empty framed set on the kernel side and
  `SafeRunsIn.of_runsIn_unframed`; the kernels' own `Runs` specs are hypotheses of these lemmas
  and are discharged by `k2DistributeBlk_holds` / `k2MergeBlk_holds` in the main theorems).
The work-stack phases and the length facts are in `CCore/LeafSplitPhase.lean`.
-/

namespace SubNLogN.Machine.CCore.LeafSplitAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine SubNLogN.Machine.Calculus
open SubNLogN.Machine.CCore

/-- Private scratch of the split / collect kernels. -/
abbrev SE (E₂ : Type) : Type := Fin 6 ⊕ (Fin Wn ⊕ E₂)

/-- Work stack names. -/
abbrev iTT : Fin 6 := 0
abbrev iCB : Fin 6 := 1
abbrev iCD : Fin 6 := 2
abbrev iCK : Fin 6 := 3
abbrev iCD2 : Fin 6 := 4
abbrev iHT : Fin 6 := 5

section Layout

variable {E₂ : Type}

/-- Work stack `i`. -/
abbrev wkL (i : Fin 6) : CL (SE E₂) := .inr (.inl i)
/-- The private buffer of role `u`. -/
abbrev bufL (u : Fin Wn) : CL (SE E₂) := .inr (.inr (.inl u))
/-- Scratch stack `e` of the embedded K2 kernel. -/
abbrev exL (e : E₂) : CL (SE E₂) := .inr (.inr (.inr e))

/-- A state of the split / collect layout, by components. -/
def mkS (io desc park : List Sym) (role : Fin Wn → List Sym) (wk : Fin 6 → List Sym)
    (buf : Fin Wn → List Sym) (ex : E₂ → List Sym) : CL (SE E₂) → List Sym
  | .inl .io => io
  | .inl .desc => desc
  | .inl .park => park
  | .inl (.role u) => role u
  | .inr (.inl i) => wk i
  | .inr (.inr (.inl u)) => buf u
  | .inr (.inr (.inr e)) => ex e

theorem mkS_eta (S : CL (SE E₂) → List Sym) :
    S = mkS (S ioL) (S descL) (S parkL) (fun u => S (roleL u)) (fun i => S (wkL i))
      (fun u => S (bufL u)) (fun e => S (exL e)) := by
  funext k
  rcases k with ((_ | _ | _ | u) | (i | (u | e))) <;> rfl

variable [DecidableEq E₂]

theorem mkS_upd_io (io desc park : List Sym) (role : Fin Wn → List Sym) (wk : Fin 6 → List Sym)
    (buf : Fin Wn → List Sym) (ex : E₂ → List Sym) (l : List Sym) :
    Function.update (mkS io desc park role wk buf ex) ioL l = mkS l desc park role wk buf ex := by
  funext k
  rcases k with ((_ | _ | _ | u) | (i | (u | e))) <;> simp [mkS, Function.update_apply]

theorem mkS_upd_role (io desc park : List Sym) (role : Fin Wn → List Sym)
    (wk : Fin 6 → List Sym) (buf : Fin Wn → List Sym) (ex : E₂ → List Sym) (u : Fin Wn)
    (l : List Sym) :
    Function.update (mkS io desc park role wk buf ex) (roleL u) l =
      mkS io desc park (Function.update role u l) wk buf ex := by
  funext k
  rcases k with ((_ | _ | _ | v) | (i | (v | e))) <;> simp [mkS, Function.update_apply]

theorem mkS_upd_wk (io desc park : List Sym) (role : Fin Wn → List Sym) (wk : Fin 6 → List Sym)
    (buf : Fin Wn → List Sym) (ex : E₂ → List Sym) (i : Fin 6) (l : List Sym) :
    Function.update (mkS io desc park role wk buf ex) (wkL i) l =
      mkS io desc park role (Function.update wk i l) buf ex := by
  funext k
  rcases k with ((_ | _ | _ | v) | (j | (v | e))) <;> simp [mkS, Function.update_apply]

theorem mkS_upd_buf (io desc park : List Sym) (role : Fin Wn → List Sym)
    (wk : Fin 6 → List Sym) (buf : Fin Wn → List Sym) (ex : E₂ → List Sym) (u : Fin Wn)
    (l : List Sym) :
    Function.update (mkS io desc park role wk buf ex) (bufL u) l =
      mkS io desc park role wk (Function.update buf u l) ex := by
  funext k
  rcases k with ((_ | _ | _ | v) | (j | (v | e))) <;> simp [mkS, Function.update_apply]

end Layout

/-! ## Role loops -/

section Family

variable {E₂ : Type} [DecidableEq E₂]

/-- The role/buffer component after the first `i` steps of a role loop. -/
def mixF (i : ℕ) (new old : Fin Wn → List Sym) : Fin Wn → List Sym :=
  fun u => if u.val < i then new u else old u

theorem mixF_zero (new old : Fin Wn → List Sym) : mixF 0 new old = old := by
  funext u
  simp [mixF]

theorem mixF_Wn (new old : Fin Wn → List Sym) : mixF Wn new old = new := by
  funext u
  simp [mixF, u.isLt]

theorem mixF_self (u : Fin Wn) (new old : Fin Wn → List Sym) : mixF u.val new old u = old u := by
  simp [mixF]

theorem mixF_succ (u : Fin Wn) (new old : Fin Wn → List Sym) :
    Function.update (mixF u.val new old) u (new u) = mixF (u.val + 1) new old := by
  funext v
  by_cases hv : v = u
  · subst hv
    simp [mixF]
  · rw [Function.update_of_ne hv]
    have : v.val ≠ u.val := fun h => hv (Fin.ext h)
    simp only [mixF]
    by_cases h : v.val < u.val
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

theorem sum_finRange_const (T : ℕ) : ((List.finRange Wn).map fun _ => T).sum = Wn * T := by
  simp [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]

/-- **A role loop** (`forEachFin` over the roles) whose step `u` only changes role `u` and
buffer `u`, from `oldR u, oldB u` to `newR u, newB u`, within `T`. -/
theorem safe_forEachFin_rb {framed : CL (SE E₂) → Prop} {σ : Type}
    {ρ : List (Prog (CL (SE E₂)) (fun _ => Sym) σ)} (g : Fin Wn → Prog (CL (SE E₂)) (fun _ => Sym) σ)
    (T : ℕ) (io desc park : List Sym) (wk : Fin 6 → List Sym) (ex : E₂ → List Sym)
    (oldR newR oldB newB : Fin Wn → List Sym)
    (hstep : ∀ (u : Fin Wn) (R Bf : Fin Wn → List Sym), R u = oldR u → Bf u = oldB u →
      SafeRunsIn framed ρ (g u) (mkS io desc park R wk Bf ex)
        (mkS io desc park (Function.update R u (newR u)) wk (Function.update Bf u (newB u)) ex)
        (fun _ => True) T) :
    SafeRunsIn framed ρ (forEachFin Wn g) (mkS io desc park oldR wk oldB ex)
      (mkS io desc park newR wk newB ex) (fun _ => True) (Wn * T + 1) := by
  have h := SafeRunsIn.forEachFin (framed := framed) (ρ := ρ) Wn g (fun _ => T)
    (fun i => mkS io desc park (mixF i newR oldR) wk (mixF i newB oldB) ex) (fun u => by
      have := hstep u (mixF u.val newR oldR) (mixF u.val newB oldB) (mixF_self u _ _)
        (mixF_self u _ _)
      rw [mixF_succ, mixF_succ] at this
      exact this)
  simp only [mixF_zero, mixF_Wn] at h
  rw [sum_finRange_const] at h
  exact h

end Family

/-! ## Embedding of the K2 kernels -/

section Embed

variable {E₂ : Type}

/-- The embedding of a K2 block-kernel layout (`Fin 2 ⊕ Fin W` named stacks, scratch `E₂`):
named stack `0` (array source / destination) ↦ `io`, named stack `1` (row-size counter) ↦ `CB`,
role stack `w` ↦ buffer `w`, scratch `e` ↦ `ex e`. Its image is unframed. -/
def ιK : KLoc (Fin 2 ⊕ Fin Wn) E₂ → CL (SE E₂)
  | .inl (.inl i) => if i = 0 then ioL else wkL iCB
  | .inl (.inr w) => bufL w
  | .inr e => exL e

theorem ιK_injective : Function.Injective (ιK (E₂ := E₂)) := by
  intro x y h
  rcases x with ((i | w) | e) <;> rcases y with ((j | w') | e')
  all_goals first
    | (fin_cases i <;> fin_cases j <;> simp_all [ιK])
    | (fin_cases i <;> simp_all [ιK])
    | (fin_cases j <;> simp_all [ιK])
    | simp_all [ιK]

theorem ιK_unframed (x : KLoc (Fin 2 ⊕ Fin Wn) E₂) : ¬ ccoreFramed (ιK x) := by
  rcases x with ((i | w) | e)
  · simp only [ιK]
    split_ifs <;> simp [ccoreFramed]
  · simp [ιK, ccoreFramed]
  · simp [ιK, ccoreFramed]

end Embed

section Calls

variable {E₂ R₂ : Type} [DecidableEq E₂]

/-- **The K2 distribution, embedded.** A closed program `P₂` meeting the spec of
`K2DistributeBlkStmt W` moves the array `v` (rows of `s` records) from `io` to the buffers
(row `a` to buffer `a mod W`, on top of the old buffer content), safely. -/
theorem safe_distCall (P₂ : Prog (KLoc (Fin 2 ⊕ Fin Wn) E₂) (fun _ => Sym) R₂) (hcl : P₂.Closed)
    (C₂ : ℕ)
    (hspec : ∀ (R s : ℕ) (v : List (List Bool)) (rest r1 : List Sym)
      (S : KLoc (Fin 2 ⊕ Fin Wn) E₂ → List Sym),
      v.length = R * s → BlkTerm rest → TermOK r1 →
      S (.inl (.inl 0)) = arrSyms v ++ rest → S (.inl (.inl 1)) = natSyms s ++ r1 →
      Runs P₂ S (distBlkPost s v rest S) (fun _ => True) (C₂ * (vol v + 1)))
    (R s : ℕ) (v : List (List Bool)) (tio cb : List Sym) (hv : v.length = R * s)
    (htio : BlkTerm tio) (hcb : TermOK cb) (desc park : List Sym) (role : Fin Wn → List Sym)
    (wk : Fin 6 → List Sym) (buf : Fin Wn → List Sym) (ex : E₂ → List Sym)
    (hwk : wk iCB = natSyms s ++ cb)
    (ρ : List (Prog (CL (SE E₂)) (fun _ => Sym) (Option Sym × R₂))) :
    SafeRunsIn ccoreFramed ρ (callInj ιK (Lens.snd (Option Sym) R₂) P₂)
      (mkS (arrSyms v ++ tio) desc park role wk buf ex)
      (mkS tio desc park role wk (fun w => arrSyms (roleBlocks Wn w.val s v) ++ buf w) ex)
      (fun _ => True) (C₂ * (vol v + 1)) := by
  have hRuns := hspec R s v tio cb (mkS (arrSyms v ++ tio) desc park role wk buf ex ∘ ιK) hv htio
    hcb (by simp [ιK, mkS]) (by simp [ιK, mkS, hwk])
  have hpost : distBlkPost s v tio (mkS (arrSyms v ++ tio) desc park role wk buf ex ∘ ιK) =
      mkS tio desc park role wk (fun w => arrSyms (roleBlocks Wn w.val s v) ++ buf w) ex ∘ ιK := by
    funext x
    rcases x with ((i | w) | e)
    · fin_cases i <;> simp [distBlkPost, ιK, mkS]
    · simp [distBlkPost, ιK, mkS]
    · simp [distBlkPost, ιK, mkS]
  rw [hpost] at hRuns
  refine SafeRunsIn.callInj (framedL := fun _ => False) ιK_injective (fun x h => ιK_unframed x h)
    _ hcl (SafeRunsIn.of_runsIn_unframed (RunsIn.iff_runs.mpr hRuns)) ?_ ρ
  intro k hk
  rcases k with ((_ | _ | _ | u) | (i | (u | e)))
  · exact absurd (show ιK (E₂ := E₂) (.inl (.inl 0)) = ioL by simp [ιK]) (hk _)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absurd (show ιK (E₂ := E₂) (.inl (.inr u)) = bufL u by simp [ιK]) (hk _)
  · rfl

/-- **The K2 merge, embedded.** A closed program `P₃` meeting the spec of `K2MergeBlkStmt W π`
merges the buffers (`g` rows of `s` records each, round `t` takes row `t` of buffers
`π 0, …, π (W-1)`) onto `io`, emptying the buffers, safely. -/
theorem safe_mergeCall (π : Equiv.Perm (Fin Wn))
    (P₃ : Prog (KLoc (Fin 2 ⊕ Fin Wn) E₂) (fun _ => Sym) R₂) (hcl : P₃.Closed) (C₃ : ℕ)
    (hspec : ∀ (g s : ℕ) (us : Fin Wn → List (List Bool)) (rests : Fin Wn → List Sym)
      (r1 : List Sym) (S : KLoc (Fin 2 ⊕ Fin Wn) E₂ → List Sym),
      (∀ w, (us w).length = g * s) → (∀ w, BlkTerm (rests w)) → TermOK r1 →
      (∀ w, S (.inl (.inr w)) = arrSyms (us w) ++ rests w) →
      S (.inl (.inl 1)) = natSyms s ++ r1 →
      Runs P₃ S (mergeBlkPost π g s us rests S) (fun _ => True)
        (C₃ * (((List.finRange Wn).map fun w => vol (us w)).sum + 1)))
    (g s : ℕ) (us : Fin Wn → List (List Bool)) (hus : ∀ w, (us w).length = g * s)
    (tio cb : List Sym) (hcb : TermOK cb) (desc park : List Sym) (role : Fin Wn → List Sym)
    (wk : Fin 6 → List Sym) (ex : E₂ → List Sym) (hwk : wk iCB = natSyms s ++ cb)
    (ρ : List (Prog (CL (SE E₂)) (fun _ => Sym) (Option Sym × R₂))) :
    SafeRunsIn ccoreFramed ρ (callInj ιK (Lens.snd (Option Sym) R₂) P₃)
      (mkS tio desc park role wk (fun w => arrSyms (us w)) ex)
      (mkS (arrSyms (mergeBlocks Wn π g s us) ++ tio) desc park role wk (fun _ => []) ex)
      (fun _ => True) (C₃ * (((List.finRange Wn).map fun w => vol (us w)).sum + 1)) := by
  have hRuns := hspec g s us (fun _ => []) cb
    (mkS tio desc park role wk (fun w => arrSyms (us w)) ex ∘ ιK) hus
    (fun _ d hd => by simp at hd) hcb (fun w => by simp [ιK, mkS]) (by simp [ιK, mkS, hwk])
  have hpost : mergeBlkPost π g s us (fun _ => [])
      (mkS tio desc park role wk (fun w => arrSyms (us w)) ex ∘ ιK) =
      mkS (arrSyms (mergeBlocks Wn π g s us) ++ tio) desc park role wk (fun _ => []) ex ∘ ιK := by
    funext x
    rcases x with ((i | w) | e)
    · fin_cases i <;> simp [mergeBlkPost, ιK, mkS]
    · simp [mergeBlkPost, ιK, mkS]
    · simp [mergeBlkPost, ιK, mkS]
  rw [hpost] at hRuns
  refine SafeRunsIn.callInj (framedL := fun _ => False) ιK_injective (fun x h => ιK_unframed x h)
    _ hcl (SafeRunsIn.of_runsIn_unframed (RunsIn.iff_runs.mpr hRuns)) ?_ ρ
  intro k hk
  rcases k with ((_ | _ | _ | u) | (i | (u | e)))
  · exact absurd (show ιK (E₂ := E₂) (.inl (.inl 0)) = ioL by simp [ιK]) (hk _)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absurd (show ιK (E₂ := E₂) (.inl (.inr u)) = bufL u by simp [ιK]) (hk _)
  · rfl

end Calls

end SubNLogN.Machine.CCore.LeafSplitAux
