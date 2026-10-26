/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5NetSimShape
import SubNLogN.Math.Networks.Proofs.FrameInvariant
import SubNLogN.Math.Networks.Proofs.InterchangeCounts

/-!
# Structural counts and validity of the raw schedule (`AppC/R2C5NetShape2.lean`)

Alternative structural proofs of the three schedule lemmas of `AppC/C5NetSimShape2.lean` (with `R2`
and `_r2`/`AppC`/`C5` retained from earlier draft naming for identifier stability; see Appendix A,
Proposition A.7 (`prop:transfer11`)):
* `rawMain_calls_r2`: `rawMain fac` has `tripleSb 100` calls, under the pure-network child-count
  bound (`InterchangeCallCountStmt`, an explicit hypothesis as in `C5NetSimShape2.lean`);
* `rawMain_valid_r2`: every stream op of `rawMain fac` is valid (`FacData.Valid` of every edge);
* `rawMain_gates_ne_r2`: the XOR gates of `rawMain fac` have distinct ends.

Method: membership in `rawMain` is decomposed through `List.mem_flatMap` over the event list
(`rawMain`, `rawEv`, `rawEdge`, `rawShear`, `rawLower`), with every lemma stated for an arbitrary
role `w`, factor data `F`, matrix `E`. The closed lists (`nodeEvents .bit 100`, `List.finRange mH`,
`Finset.univ` of roles) are never evaluated: no `rfl`/`decide`/`show` on a goal containing them.
The call count keeps `InterchangeCountsAux.calls` folded and rewrites with its unfolding
lemmas in the hypothesis (`callCount_interchangeProc`, `bitNodeOps_eq`, `nodeMainOps_eq_flatMap`,
`calls_append`).
-/

namespace SubNLogN.Machine.C5.R2ShapeAux

open SubNLogN.Math.Networks SubNLogN.Machine.C5.NetAux
open SubNLogN.Math.Networks.Model (Layout Step RoleOp ProcK Elem)

/-! ## Calls -/

/-- A relabelling is not a call. -/
theorem calls_relabel_single {L : Layout} {β : Type} {W : ℕ} {Child : Type}
    (π : Equiv.Perm (Fin W)) :
    InterchangeCountsAux.calls ([Model.RoleOp.relabel π] : List (RoleOp L β W Child)) = 0 := rfl

/-- Lists related entrywise by "same call status" have the same number of calls. -/
theorem calls_eq_of_forall₂ {L : Layout} {β : Type} {Child : Type} {l : List (RoleOp L β Wb Child)}
    {r : List (RawOp Wb mH)} (h : List.Forall₂ (fun o x => o.isCall = x.isCall) l r) :
    InterchangeCountsAux.calls l = (r.filter RawOp.isCall).length := by
  unfold InterchangeCountsAux.calls
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    rw [List.filter_cons, List.filter_cons, hab]
    split <;> simp [ih]

/-- **Calls of the raw schedule** (structural proof of `NetAux.rawMain_calls`): `s_b = tripleSb 100`. -/
theorem rawMain_calls_r2 (hCC : InterchangeCallCountStmt) (q : ℕ)
    (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) (hC : C5Params q fac) :
    ((rawMain fac).filter RawOp.isCall).length = tripleSb 100 := by
  have h1 := hCC (⟨0, Fin.elim0⟩ : Layout) (ZMod 2) q fac 0 0 0 hC
  rw [InterchangeCountsAux.callCount_interchangeProc, InterchangeCorrect.bitNodeOps_eq,
    InterchangeCorrect.nodeMainOps_eq_flatMap, InterchangeCountsAux.calls_append,
    calls_relabel_single, Nat.add_zero] at h1
  rw [← h1]
  exact (calls_eq_of_forall₂ (forall₂_main (fun o x => o.isCall = x.isCall) _ _ _ _ fac _
    (fun _ F => forall₂_shear _ _ _ _ _ _ F _
      (fun E => forall₂_lower _ _ _ _ _ _ E (fun _ => rfl) (fun _ => rfl))
      (fun E => forall₂_lower _ _ _ _ _ _ E (fun _ => rfl) (fun _ => rfl))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    (fun _ _ _ => rfl))).symm

/-! ## Validity -/

theorem coprime_den {q : ℕ} (hq : q.Prime) {r : ℚ} (h : QIntegral q r) : Nat.Coprime r.den q :=
  ((Nat.Prime.coprime_iff_not_dvd hq).2 h).symm

theorem coprime_num {q : ℕ} (hq : q.Prime) {r : ℚ} (h : ¬ (q : ℤ) ∣ r.num) :
    Nat.Coprime r.num.natAbs q :=
  ((Nat.Prime.coprime_iff_not_dvd hq).2 (fun hd => h (Int.ofNat_dvd_left.2 hd))).symm

/-- The stream ops of the raw lower-triangular steps are valid for a `q`-integral matrix with
diagonal numerators prime to `q`. -/
theorem rawLower_valid {q : ℕ} (hq : q.Prime) (w : Fin Wb) (X : Chunk)
    (E : Matrix (Fin mH) (Fin mH) ℚ) (hI : ∀ i j, QIntegral q (E i j))
    (hN : ∀ i, ¬ (q : ℤ) ∣ (E i i).num) :
    ∀ x ∈ rawLower w X E, ∀ op ∈ x.opsOf, op.Valid q := by
  intro x hx op hop
  unfold rawLower at hx
  obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
  rcases List.mem_cons.1 hx with rfl | hx
  · rcases List.mem_singleton.1 hop with rfl
    exact ⟨coprime_num hq (hN i), coprime_den hq (hI i i)⟩
  · rcases List.mem_singleton.1 hx with rfl
    rcases List.mem_singleton.1 hop with rfl
    exact fun j => coprime_den hq (hI i j)

/-- `-1` is a `q`-adic unit. -/
theorem valid_neg_one (q : ℕ) (X : Chunk) (j : Fin mH) :
    (StreamOp.unit X j (-1 : ℚ) : StreamOp mH).Valid q := by
  show Nat.Coprime (-1 : ℚ).num.natAbs q ∧ Nat.Coprime (-1 : ℚ).den q
  have h1 : (-1 : ℚ).num.natAbs = 1 := rfl
  have h2 : (-1 : ℚ).den = 1 := rfl
  rw [h1, h2]
  exact ⟨Nat.coprime_one_left q, Nat.coprime_one_left q⟩

/-- The stream ops of the raw Lemma A.6 (`lem:transfer-shear`) edge program are valid for valid factor data. -/
theorem rawShear_valid_r2 {q : ℕ} (hq : q.Prime) (w : Fin Wb) (F : FacData)
    (A : Matrix (Fin mH) (Fin mH) ℚ) (hv : F.Valid q A) :
    ∀ x ∈ rawShear w F, ∀ op ∈ x.opsOf, op.Valid q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hQ, hD⟩ := hv
  intro x hx op hop
  unfold rawShear at hx
  simp only [List.mem_append] at hx
  rcases hx with (((h | h) | h) | h) | h
  · exact rawLower_valid hq w .D F.E₂ (fun i j => (hQ i j).2.2.1) (fun i => (hD i).2.2.1) x h op hop
  · exact rawLower_valid hq w .H F.E₁' (fun i j => (hQ i j).2.1) (fun i => (hD i).2.1) x h op hop
  · obtain ⟨p, -, h⟩ := List.mem_flatMap.1 h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · rcases List.mem_singleton.1 hop with rfl
      trivial
    · simp [RawOp.opsOf] at hop
    · rcases List.mem_singleton.1 hop with rfl
      exact valid_neg_one q .D p.2
    · rcases List.mem_singleton.1 hop with rfl
      trivial
  · exact rawLower_valid hq w .H F.E₁ (fun i j => (hQ i j).1) (fun i => (hD i).1) x h op hop
  · exact rawLower_valid hq w .D F.E₂' (fun i j => (hQ i j).2.2.2) (fun i => (hD i).2.2.2) x h op
      hop

/-- **Validity of the raw schedule** (structural proof of `NetAux.rawMain_valid`). -/
theorem rawMain_valid_r2 {q : ℕ} (hq : q.Prime) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData)
    (hfac : ∀ w : Role .bit 100, ∀ e ∈ edges w, (fac (edgeMatFin e)).Valid q (edgeMatFin e)) :
    ∀ x ∈ rawMain fac, ∀ op ∈ x.opsOf, op.Valid q := by
  intro x hx op hop
  unfold rawMain at hx
  obtain ⟨ev, -, hx⟩ := List.mem_flatMap.1 hx
  cases ev with
  | edge w v =>
    change x ∈ rawEdge fac w v at hx
    unfold rawEdge at hx
    split at hx
    · rename_i e he
      exact rawShear_valid_r2 hq (roleIdxB w) _ _ (hfac w e (FI.edgeInto_mem he)) x hx op hop
    · simp at hx
  | row j ι r =>
    have hx' : x = .gate (gateXors j ι r) := List.mem_singleton.1 hx
    subst hx'
    simp [RawOp.opsOf] at hop

/-! ## Distinct XOR ends -/

/-- The XOR list of a gate entry (generic, so that no defeq check ever unfolds `gateXors`). -/
theorem gatesOf_gate {W m : ℕ} (xs : List (Fin W × Fin W)) : (RawOp.gate xs : RawOp W m).gatesOf = xs :=
  rfl

theorem rawLower_gates (w : Fin Wb) (X : Chunk) (E : Matrix (Fin mH) (Fin mH) ℚ) :
    ∀ x ∈ rawLower w X E, x.gatesOf = [] := by
  intro x hx
  unfold rawLower at hx
  obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
  rcases List.mem_cons.1 hx with rfl | hx
  · rfl
  · rcases List.mem_singleton.1 hx with rfl
    rfl

theorem rawShear_gates_r2 (w : Fin Wb) (F : FacData) : ∀ x ∈ rawShear w F, x.gatesOf = [] := by
  intro x hx
  unfold rawShear at hx
  simp only [List.mem_append] at hx
  rcases hx with (((h | h) | h) | h) | h
  · exact rawLower_gates _ _ _ x h
  · exact rawLower_gates _ _ _ x h
  · obtain ⟨p, -, h⟩ := List.mem_flatMap.1 h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  · exact rawLower_gates _ _ _ x h
  · exact rawLower_gates _ _ _ x h

/-- **Distinct XOR ends of the raw schedule** (structural proof of `NetAux.rawMain_gates_ne`). -/
theorem rawMain_gates_ne_r2 (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) :
    ∀ x ∈ rawMain fac, ∀ p ∈ x.gatesOf, p.1 ≠ p.2 := by
  intro x hx p hp
  unfold rawMain at hx
  obtain ⟨ev, -, hx⟩ := List.mem_flatMap.1 hx
  cases ev with
  | edge w v =>
    change x ∈ rawEdge fac w v at hx
    unfold rawEdge at hx
    split at hx
    · rw [rawShear_gates_r2 _ _ x hx] at hp
      simp at hp
    · simp at hx
  | row j ι r =>
    have hx' : x = .gate (gateXors j ι r) := List.mem_singleton.1 hx
    subst hx'
    rw [gatesOf_gate] at hp
    exact gateXors_ne j ι r p hp

end SubNLogN.Machine.C5.R2ShapeAux
