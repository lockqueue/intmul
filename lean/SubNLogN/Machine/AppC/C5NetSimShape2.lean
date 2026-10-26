/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5NetSimShape
import SubNLogN.Math.Networks.Proofs.FrameInvariant

/-!
# Proposition A.7 network simulation, part 6b: counts and validity of the raw schedule

`rawMain fac` has `tripleSb 100` calls under the pure-network child-count bound (`rawMain_calls`, hypothesis
`InterchangeCallCountStmt`), valid stream ops (`rawMain_valid`, from `FacData.Valid`) and XOR gates
with distinct ends (`rawMain_gates_ne`). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5.NetAux

open SubNLogN.Math.Networks
open SubNLogN.Math.Networks.Model (Layout Step RoleOp ProcK Elem)

/-! ## Calls -/

theorem forall₂_calls {L : Layout} {β : Type} {Child : Type} {l : List (RoleOp L β Wb Child)}
    {r : List (RawOp Wb mH)} (h : List.Forall₂ (fun o x => o.isCall = x.isCall) l r) :
    (l.filter Model.RoleOp.isCall).length = (r.filter RawOp.isCall).length := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    rw [List.filter_cons, List.filter_cons, hab]
    split <;> simp [ih]

theorem ip_succ {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ) :
    interchangeProc (L := L) (β := β) q fac (k + 1) h₀ d₀ =
      ((subHSteps (q ^ mH ^ k) h₀ d₀ (mH ^ k)).map Model.Op.prim ++
        [Model.Op.node Wb Wb_pos (bitNodeOps (q ^ mH ^ k) h₀ d₀ (mH ^ k) fac
          (fun i j => interchangeProc (L := L) (β := β) q fac k (h₀ + i.val * mH ^ k)
            (d₀ + j.val * mH ^ k)))] ++
        (hMinusDSteps (q ^ mH ^ k) h₀ d₀ (mH ^ k)).map Model.Op.prim :
          List (Model.Op L β (ProcK L β k))) := rfl

theorem sum_callCount_prim {L : Layout} {β : Type} {Child : Type} (l : List (Step L β)) :
    ((l.map (Model.Op.prim : Step L β → Model.Op L β Child)).map Model.Op.callCount).sum = 0 := by
  induction l with
  | nil => rfl
  | cons s l ih => rw [List.map_cons, List.map_cons, List.sum_cons, ih]; rfl

theorem callCount_node' {L : Layout} {β : Type} {Child : Type} (W : ℕ) (hW : 0 < W)
    (ops : List (RoleOp L β W Child)) :
    Model.Op.callCount (Model.Op.node W hW ops) = (ops.filter Model.RoleOp.isCall).length := rfl

theorem callCount_level {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β] (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (k h₀ d₀ : ℕ) :
    Model.ProcK.callCount k (interchangeProc (L := L) (β := β) q fac (k + 1) h₀ d₀) =
      (((nodeEvents .bit 100).flatMap (InterchangeCorrect.evOps (L := L) (β := β) (q ^ mH ^ k) h₀ d₀
        (mH ^ k) fac (fun i j => interchangeProc (L := L) (β := β) q fac k (h₀ + i.val * mH ^ k)
          (d₀ + j.val * mH ^ k)))).filter Model.RoleOp.isCall).length := by
  -- `ip_succ` has its list ascription on the right-hand side, so the `++` live at list type.
  unfold Model.ProcK.callCount
  rw [ip_succ]
  simp only [List.map_append, List.sum_append, sum_callCount_prim, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, callCount_node', Nat.add_zero, Nat.zero_add]
  -- No `rfl` on the whole goal: it would unfold the closed list `nodeEvents .bit 100`.
  have h0 : (([Model.RoleOp.relabel rhoPerm] : List (RoleOp L β Wb (ProcK L β k))).filter
      Model.RoleOp.isCall).length = 0 := rfl
  rw [InterchangeCorrect.bitNodeOps_eq, List.filter_append, List.length_append, h0, Nat.add_zero,
    InterchangeCorrect.nodeMainOps_eq_flatMap]

/-- **Calls of the raw schedule**: `s_b = tripleSb 100` (from the pure-network child-count bound). -/
theorem rawMain_calls (hCC : InterchangeCallCountStmt) (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (hC : C5Params q fac) :
    ((rawMain fac).filter RawOp.isCall).length = tripleSb 100 := by
  have h1 := hCC (⟨0, Fin.elim0⟩ : Layout) (ZMod 2) q fac 0 0 0 hC
  rw [← h1, callCount_level]
  refine (forall₂_calls (forall₂_main (fun o x => o.isCall = x.isCall) _ _ _ _ fac _
    (fun w F => forall₂_shear _ _ _ _ _ _ F _ (fun E => forall₂_lower _ _ _ _ _ _ E
      (fun _ => rfl) (fun _ => rfl)) (fun E => forall₂_lower _ _ _ _ _ _ E (fun _ => rfl)
      (fun _ => rfl)) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    (fun _ _ _ => rfl))).symm

/-! ## Validity and distinct XOR ends -/

theorem rawShear_cases (w : Fin Wb) (F : FacData) : ∀ x ∈ rawShear w F,
    (∃ E, (E = F.E₁ ∨ E = F.E₁' ∨ E = F.E₂ ∨ E = F.E₂') ∧ ∃ (X : Chunk) (i : Fin mH),
      x = .stream w (.unit X i (E i i)) ∨ x = .stream w (.lowShift X i (fun j => E i j))) ∨
    (∃ i j : Fin mH, x = .stream w (.hdShift i j false)) ∨ (∃ i j : Fin mH, x = .call w i j) ∨
    (∃ j : Fin mH, x = .stream w (.unit .D j (-1))) := by
  have hL : ∀ X E, ∀ x ∈ rawLower w X E, ∃ i : Fin mH,
      x = .stream w (.unit X i (E i i)) ∨ x = .stream w (.lowShift X i (fun j => E i j)) := by
    intro X E x hx
    simp only [rawLower, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨i, -, h⟩ := hx
    exact ⟨i, h⟩
  intro x hx
  simp only [rawShear, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with (((h | h) | ⟨p, -, h | h | h | h⟩) | h) | h
  · obtain ⟨i, hi⟩ := hL _ _ x h
    exact Or.inl ⟨F.E₂, Or.inr (Or.inr (Or.inl rfl)), .D, i, hi⟩
  · obtain ⟨i, hi⟩ := hL _ _ x h
    exact Or.inl ⟨F.E₁', Or.inr (Or.inl rfl), .H, i, hi⟩
  · exact Or.inr (Or.inl ⟨p.1, p.2, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p.1, p.2, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨p.2, h⟩))
  · exact Or.inr (Or.inl ⟨p.1, p.2, h⟩)
  · obtain ⟨i, hi⟩ := hL _ _ x h
    exact Or.inl ⟨F.E₁, Or.inl rfl, .H, i, hi⟩
  · obtain ⟨i, hi⟩ := hL _ _ x h
    exact Or.inl ⟨F.E₂', Or.inr (Or.inr (Or.inr rfl)), .D, i, hi⟩

theorem coprime_of_not_dvd {q a : ℕ} (hq : q.Prime) (h : ¬ q ∣ a) : Nat.Coprime a q :=
  ((Nat.Prime.coprime_iff_not_dvd hq).2 h).symm

theorem rawShear_valid {q : ℕ} (hq : q.Prime) (w : Fin Wb) (F : FacData)
    (A : Matrix (Fin mH) (Fin mH) ℚ) (hv : F.Valid q A) :
    ∀ x ∈ rawShear w F, ∀ op ∈ x.opsOf, op.Valid q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hQ, hD⟩ := hv
  intro x hx op hop
  rcases rawShear_cases w F x hx with ⟨E, hE, X, i, rfl | rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩ | ⟨j, rfl⟩
  · simp only [RawOp.opsOf, List.mem_singleton] at hop
    subst hop
    have hden : QIntegral q (E i i) := by
      rcases hE with rfl | rfl | rfl | rfl
      exacts [(hQ i i).1, (hQ i i).2.1, (hQ i i).2.2.1, (hQ i i).2.2.2]
    have hnum : ¬ (q : ℤ) ∣ (E i i).num := by
      rcases hE with rfl | rfl | rfl | rfl
      exacts [(hD i).1, (hD i).2.1, (hD i).2.2.1, (hD i).2.2.2]
    exact ⟨coprime_of_not_dvd hq (fun h => hnum (Int.ofNat_dvd_left.2 h)),
      coprime_of_not_dvd hq hden⟩
  · simp only [RawOp.opsOf, List.mem_singleton] at hop
    subst hop
    intro j
    have hden : QIntegral q (E i j) := by
      rcases hE with rfl | rfl | rfl | rfl
      exacts [(hQ i j).1, (hQ i j).2.1, (hQ i j).2.2.1, (hQ i j).2.2.2]
    exact coprime_of_not_dvd hq hden
  · simp only [RawOp.opsOf, List.mem_singleton] at hop
    subst hop
    trivial
  · simp [RawOp.opsOf] at hop
  · simp only [RawOp.opsOf, List.mem_singleton] at hop
    subst hop
    show Nat.Coprime (-1 : ℚ).num.natAbs q ∧ Nat.Coprime (-1 : ℚ).den q
    rw [show (-1 : ℚ).num.natAbs = 1 by rfl, show (-1 : ℚ).den = 1 by rfl]
    exact ⟨Nat.coprime_one_left q, Nat.coprime_one_left q⟩

theorem rawShear_gates (w : Fin Wb) (F : FacData) : ∀ x ∈ rawShear w F, x.gatesOf = [] := by
  intro x hx
  rcases rawShear_cases w F x hx with ⟨E, -, X, i, rfl | rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩ | ⟨j, rfl⟩ <;>
    rfl

theorem rawMain_forall (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (P : RawOp Wb mH → Prop)
    (hE : ∀ w v, ∀ x ∈ rawEdge fac w v, P x) (hG : ∀ j ι r, P (.gate (gateXors j ι r))) :
    ∀ x ∈ rawMain fac, P x := by
  intro x hx
  unfold rawMain at hx
  obtain ⟨ev, -, hx⟩ := List.mem_flatMap.1 hx
  cases ev with
  | edge w v => exact hE w v x hx
  | row j ι r =>
    have hx' : x = .gate (gateXors j ι r) := List.mem_singleton.1 hx
    rw [hx']
    exact hG j ι r

theorem rawEdge_forall (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (P : RawOp Wb mH → Prop)
    (hsh : ∀ w e, e ∈ edges w → ∀ x ∈ rawShear (roleIdxB w) (fac (edgeMatFin e)), P x) :
    ∀ w v, ∀ x ∈ rawEdge fac w v, P x := by
  intro w v x hx
  unfold rawEdge at hx
  split at hx
  · rename_i e he
    exact hsh w e (FI.edgeInto_mem he) x hx
  · simp at hx

theorem rawMain_valid {q : ℕ} (hq : q.Prime) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e)) :
    ∀ x ∈ rawMain fac, ∀ op ∈ x.opsOf, op.Valid q :=
  rawMain_forall fac _ (rawEdge_forall fac _ fun w e he =>
      rawShear_valid hq (roleIdxB w) _ _ (hfac w e he))
    fun _ _ _ op hop => by simp [RawOp.opsOf] at hop

/-- `gatesOf` of a gate entry, generically (proved by `rfl` over a variable list, so that uses
only instantiate it: the kernel never compares `gatesOf (.gate (gateXors …))` with
`gateXors …` by unfolding the latter). -/
theorem gatesOf_gate {W m : ℕ} (xs : List (Fin W × Fin W)) :
    (RawOp.gate xs : RawOp W m).gatesOf = xs := rfl

theorem rawMain_gates_ne (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) :
    ∀ x ∈ rawMain fac, ∀ p ∈ x.gatesOf, p.1 ≠ p.2 := by
  refine rawMain_forall fac (fun x => ∀ p ∈ x.gatesOf, p.1 ≠ p.2) ?_ ?_
  · refine rawEdge_forall fac (fun x => ∀ p ∈ x.gatesOf, p.1 ≠ p.2) ?_
    intro w e _ x hx p hp
    rw [rawShear_gates _ _ x hx] at hp
    simp at hp
  · intro j ι r p hp
    rw [gatesOf_gate] at hp
    exact gateXors_ne j ι r p hp

end SubNLogN.Machine.C5.NetAux
