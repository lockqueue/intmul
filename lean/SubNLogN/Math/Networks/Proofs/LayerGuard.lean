import SubNLogN.Math.Networks.AppCLayerProc
import SubNLogN.Math.Networks.Proofs.GuardArith
import SubNLogN.Math.Networks.Proofs.LayerGuardRun
import SubNLogN.Math.Networks.Proofs.LayerGuardSteps
import SubNLogN.Math.Networks.Proofs.LayerGuardCore
import SubNLogN.Math.Networks.Proofs.LayerGuardAsm

/-!
# Proposition A.11 (`prop:prop14-param`) guard: `prop71Guard_holds : Prop71GuardStmt`

`Prop71GuardStmt` (`AppCLayerProc.lean`; Proposition A.11 (`prop:prop14-param`), Appendix A.6 (`sec:transfer-layer`), eq. (`eq:walsh-guard-growth`);
`prop71` is a historical identifier prefix retained for stability): in the band `a_d P^{1/15} ≤ d`, with
`Δ = ⌈C₀ d^{14}⌉` (`C₀ = guardC0 100`), every intermediate array of the three layer phases started from a disk-grid input lies on the guard grid (`LayerGuarded`).

Proof: sequential charge accounting (`LayerGuardRun.run_charge`, `pseq_charge`) with the guard
predicate `ptG P J` (`LayerGuardSteps`). Kernels cost `1`, gates cost `gateCharge`, unit phases and
address moves cost `0`, the scalar `b_D` costs `D/2+1`, and a child call costs its own total charge.

* Part A: the base-`m` pieces of phase 2 (`piecesOf`): at most `n` pieces, each inside `[0, n)`.
* Part C: a role meets at most twelve gate rows (`gateAt` is injective on its gates).
* Part D: one node of the Lemma A.10 (`lem:transfer-phase`) core charges at most `gateSumOf gateCharge + 13·W_c·m·B`
  when every child charges at most `B` (`chg_cxNodeOps_le`).
* Part E: `chargeK` of `cCoreProc` at level `k` is at most `Bseq s E kLeaf k`
  (`Bseq (k+1) = m^{k+1}` below the leaf level, `E + s · Bseq k` above it), and the three phases
  are assembled by `LayerGuardAsm.layerGuarded_of_charges`.
* Part F: `Bseq ≤ s (8 + E/(s-1)) d^6` (`guardRecurrence_holds`, using `s = 13 W_c m < m^5` from
  `ComplexNetCert.card_roles`), so the total charge `D + Σ_pieces Bseq + (D/2+1) ≤ C₀ d^{14}` for
  `d ≥ d*` (`GuardGrowthStmt`).

Implementation note: no closed arithmetic term containing `W_c = Fintype.card (Role .complex 100)`
(or `Fintype.card (Fix 100)`) is ever unfolded or compared up to non-syntactic definitional
equality; the kernel would otherwise try to evaluate the cardinality. Such constants enter only
syntactically, through lemmas about variables instantiated by application.
-/

namespace SubNLogN.Math.Networks.LayerGuardAux

open SubNLogN.Math.Networks SubNLogN.Math.Networks.Model SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks.LayerGuardRun SubNLogN.Math.Networks.LayerGuardSteps
open SubNLogN.Math.Networks.LayerGuardCore

/-! ## Part A: the base-`m` pieces -/

theorem piecesAux_length (ds : List ℕ) (j o : ℕ) : (piecesAux ds j o).length = ds.sum := by
  induction ds generalizing j o with
  | nil => simp [piecesAux]
  | cons a ds ih => simp [piecesAux, ih]

theorem piecesAux_bound (ds : List ℕ) (j o : ℕ) : ∀ p ∈ piecesAux ds j o,
    p.2 + mH ^ p.1 ≤ o + mH ^ j * Nat.ofDigits mH ds := by
  induction ds generalizing j o with
  | nil => simp [piecesAux]
  | cons a ds ih =>
    intro p hp
    simp only [piecesAux, List.mem_append, List.mem_map, List.mem_range] at hp
    rw [Nat.ofDigits_cons]
    rcases hp with ⟨t, ht, rfl⟩ | hp
    · have h1 : t * mH ^ j + mH ^ j ≤ a * mH ^ j := by
        have := Nat.mul_le_mul_right (mH ^ j) (Nat.succ_le_of_lt ht)
        simpa [Nat.succ_mul] using this
      have h2 : a * mH ^ j ≤ mH ^ j * (a + mH * Nat.ofDigits mH ds) := by
        rw [mul_comm (mH ^ j)]
        exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      show o + t * mH ^ j + mH ^ j ≤ o + mH ^ j * (a + mH * Nat.ofDigits mH ds)
      omega
    · have h := ih (j + 1) (o + a * mH ^ j) p hp
      have h3 : o + a * mH ^ j + mH ^ (j + 1) * Nat.ofDigits mH ds =
          o + mH ^ j * (a + mH * Nat.ofDigits mH ds) := by ring
      omega

theorem piecesOf_length_le (n : ℕ) : (piecesOf n).length ≤ n := by
  unfold piecesOf
  rw [piecesAux_length]
  exact Nat.digit_sum_le _ _

theorem piecesOf_bound (n : ℕ) : ∀ p ∈ piecesOf n, p.2 + mH ^ p.1 ≤ n := by
  intro p hp
  have h := piecesAux_bound (Nat.digits mH n) 0 0 p hp
  simpa [Nat.ofDigits_digits] using h

/-! ## Part C: every role meets at most twelve gate times -/

theorem card_filter_isSome_le {T G : Type} [Fintype T] (F : T → Option G) (l : List G)
    (hmem : ∀ t g, F t = some g → g ∈ l) (hinj : ∀ t t' g, F t = some g → F t' = some g → t = t') :
    (Finset.univ.filter fun t => (F t).isSome).card ≤ l.length := by
  classical
  calc (Finset.univ.filter fun t => (F t).isSome).card
      ≤ (l.map some).toFinset.card := by
        apply Finset.card_le_card_of_injOn F
        · intro t ht
          have ht' : (F t).isSome := (Finset.mem_filter.mp ht).2
          obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp ht'
          rw [hg]
          simpa using hmem t g hg
        · intro t ht t' ht' heq
          have ht1 : (F t).isSome := (Finset.mem_filter.mp ht).2
          obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp ht1
          exact hinj t t' g hg (heq ▸ hg)
    _ ≤ (l.map some).length := List.toFinset_card_le _
    _ = l.length := List.length_map _

theorem touch_length_le {κ : Kind} (w : Role κ 100) : (touch w).length ≤ 12 := by
  cases w <;> simp [touch]

theorem gateAt_some {κ : Kind} {j : Stage} {ι : Fix 100} {r : Fin 8} {w : Role κ 100} {g : Gate 100}
    (h : gateAt j ι r w = some g) : g ∈ touch w ∧ g.stage = j ∧ g.inv = ι ∧ g.time = r := by
  unfold gateAt at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

/-! ## Part D: the charge of one complex-network node -/

theorem sum_map_append {γ : Type} (f : γ → ℕ) (l₁ l₂ : List γ) :
    ((l₁ ++ l₂).map f).sum = (l₁.map f).sum + (l₂.map f).sum := by
  simp [List.map_append, List.sum_append]

theorem sum_map_flatMap {α γ : Type} (f : γ → ℕ) (l : List α) (F : α → List γ) :
    ((l.flatMap F).map f).sum = (l.map fun x => ((F x).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem sum_stage_list (g : Stage → ℕ) : ([Stage.one, .two, .three].map g).sum = ∑ j, g j := by
  rw [show (Finset.univ : Finset Stage) = {Stage.one, Stage.two, Stage.three} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp

theorem sum_map_le_length_mul {α : Type} (l : List α) (F : α → ℕ) (B : ℕ) (h : ∀ x ∈ l, F x ≤ B) :
    (l.map F).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a (List.mem_cons_self)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    rw [Nat.succ_mul]
    omega

/-- Indicator bound for the edges of `w` before the row `(j, ι, r)`. -/
noncomputable def ind (Bk : ℕ) (j : Stage) (ι : Fix 100) (r : Fin 8) (w : Role .complex 100) : ℕ :=
  if (gateAt j ι r w).isSome then mH * Bk else 0

theorem sum_ite_isSome_le {T G : Type} [Fintype T] (F : T → Option G) (l : List G) (c : ℕ)
    (hmem : ∀ t g, F t = some g → g ∈ l) (hinj : ∀ t t' g, F t = some g → F t' = some g → t = t') :
    (∑ t, if (F t).isSome then c else 0) ≤ l.length * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_filter_isSome_le F l hmem hinj)

theorem sum_ind_le (Bk : ℕ) :
    ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, ∑ w : Role .complex 100, ind Bk j ι r w ≤
      Wc * (12 * (mH * Bk)) := by
  have h1 : (∑ p : Stage × Fix 100 × Fin 8, ∑ w : Role .complex 100, ind Bk p.1 p.2.1 p.2.2 w) =
      ∑ j : Stage, ∑ ι : Fix 100, ∑ r : Fin 8, ∑ w : Role .complex 100, ind Bk j ι r w := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type]
  rw [← h1, Finset.sum_comm]
  calc ∑ w : Role .complex 100, ∑ p : Stage × Fix 100 × Fin 8, ind Bk p.1 p.2.1 p.2.2 w
      ≤ ∑ _w : Role .complex 100, 12 * (mH * Bk) := by
        refine Finset.sum_le_sum fun w _ => ?_
        unfold ind
        refine le_trans (sum_ite_isSome_le (fun p : Stage × Fix 100 × Fin 8 =>
          gateAt p.1 p.2.1 p.2.2 w) (touch w) (mH * Bk) ?_ ?_)
          (Nat.mul_le_mul_right _ (touch_length_le w))
        · intro t g hg
          exact (gateAt_some hg).1
        · intro t t' g hg hg'
          obtain ⟨-, h1, h2, h3⟩ := gateAt_some hg
          obtain ⟨-, h1', h2', h3'⟩ := gateAt_some hg'
          rcases t with ⟨j, ι, r⟩
          rcases t' with ⟨j', ι', r'⟩
          simp only at h1 h2 h3 h1' h2' h3'
          rw [← h1, ← h2, ← h3, ← h1', ← h2', ← h3']
    _ = Wc * (12 * (mH * Bk)) := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- `List.sum` of a pointwise sum. -/
theorem sum_map_add2 {α : Type} (l : List α) (f g : α → ℕ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

/-- Splitting a constant summand off a fourfold nested list sum (generic lists). -/
theorem sum4_split {α β γ δ : Type} (l1 : List α) (l2 : List β) (l3 : List γ) (l4 : List δ)
    (F : α → β → γ → δ → ℕ) (c : ℕ) :
    (l1.map fun a => (l2.map fun b => (l3.map fun g =>
        (l4.map fun x => F a b g x).sum + c).sum).sum).sum =
      (l1.map fun a => (l2.map fun b => (l3.map fun g =>
        (l4.map fun x => F a b g x).sum).sum).sum).sum +
      (l1.map fun _ => (l2.map fun _ => (l3.map fun _ => c).sum).sum).sum := by
  simp only [sum_map_add2]

/-- A fourfold nested list sum as a fourfold `Finset` sum (generic index types). -/
theorem sum4_eq_fintype {S I R W : Type} [Fintype S] [Fintype I] [Fintype R] [Fintype W]
    (l1 : List S) (l2 : List I) (l3 : List R) (l4 : List W)
    (h1 : ∀ f : S → ℕ, (l1.map f).sum = ∑ x, f x) (h2 : ∀ f : I → ℕ, (l2.map f).sum = ∑ x, f x)
    (h3 : ∀ f : R → ℕ, (l3.map f).sum = ∑ x, f x) (h4 : ∀ f : W → ℕ, (l4.map f).sum = ∑ x, f x)
    (F : S → I → R → W → ℕ) :
    (l1.map fun a => (l2.map fun b => (l3.map fun g =>
        (l4.map fun x => F a b g x).sum).sum).sum).sum =
      ∑ a, ∑ b, ∑ g, ∑ x, F a b g x := by
  rw [h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h3]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [h4]

/-- The gate charges of one node: one charge `c` for each of the `3 · |Fix 100| · 8` rows
(kept as a list sum; its value is never needed). -/
noncomputable def gateSumOf (c : ℕ) : ℕ :=
  ([Stage.one, .two, .three].map fun _ => ((Finset.univ : Finset (Fix 100)).toList.map fun _ =>
    ((List.finRange 8).map fun _ => c).sum).sum).sum

theorem gateSumOf_eq (c : ℕ) : gateSumOf c = ([Stage.one, .two, .three].map fun _ =>
    ((Finset.univ : Finset (Fix 100)).toList.map fun _ =>
      ((List.finRange 8).map fun _ => c).sum).sum).sum :=
  rfl

theorem add_le_swap (x y z : ℕ) (h : x ≤ z) : x + y ≤ y + z := by omega

theorem arith_node (E W M B a b c e g : ℕ) (ha : a = 0) (he : e = 0) (hg : g = 0)
    (hb : b ≤ E + W * (12 * (M * B))) (hc : c ≤ W * (M * B)) :
    a + b + c + e + g ≤ E + 13 * W * M * B := by
  have h1 : W * (12 * (M * B)) = 12 * (W * (M * B)) := by ring
  have h2 : 13 * W * M * B = 13 * (W * (M * B)) := by ring
  rw [h1] at hb
  rw [h2]
  omega

section Node

variable {A₂ K D₂ S rr k : ℕ}

/-- A gate row charges `gateCharge`. -/
theorem chg_gateOpC (cc : ProcK (layerLayout A₂ K D₂ S) (Fin rr → ℂ) k → ℕ) (j : Stage)
    (ι : Fix 100) (r : Fin 8) :
    ([gateOpC (A := A₂) (K := K) (D := D₂) (S := S) (rr := rr)
      (Child := ProcK (layerLayout A₂ K D₂ S) (Fin rr → ℂ) k) j ι r].map
      (RoleOp.chg cs2 gateCharge cc)).sum = gateCharge := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rfl

theorem chg_coreEdgeOps_le (ρ f j0 : ℕ) (Dd : CxEdgeData)
    (childOf : ℕ → ProcK (layerLayout A₂ K D₂ S) (Fin rr → ℂ) k) (kk : Fin Wc) (Bk : ℕ)
    (hch : ∀ t, chargeK cs2 gateCharge k (childOf t) ≤ Bk) :
    ((coreEdgeOps (A := A₂) (K := K) (D := D₂) (S := S) (rr := rr) ρ f j0 Dd childOf kk).map
      (RoleOp.chg cs2 gateCharge (chargeK cs2 gateCharge k))).sum ≤ Dd.basis.length * Bk := by
  have key : ∀ x y z n : ℕ, x = 0 → z = 0 → y ≤ n * Bk → x + y + z ≤ n * Bk := by
    intros; omega
  unfold coreEdgeOps
  simp only [sum_map_append, sum_map_flatMap]
  apply key
  · refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
    refine List.sum_eq_zero fun y hy => ?_
    obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hro
    exact cs2_of_isMove (isMove_packed _ _ _ _ _ s hs)
  · refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
    refine List.sum_eq_zero fun y hy => ?_
    obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hro
    exact cs2_of_isMove (isMove_packed _ _ _ _ _ s hs)
  · refine le_trans (sum_map_le_length_mul _ _ Bk fun p _ => ?_) ?_
    · split_ifs
      · simpa [RoleOp.chg] using hch p.1
      · simpa [RoleOp.chg, cs2, zSlot] using hch p.1
    · refine Nat.mul_le_mul_right _ ?_
      simp only [List.length_zip, List.length_range]
      exact min_le_left _ _

theorem chg_coreEdgeOpsAt_le (ρ f j0 : ℕ) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (childOf : ℕ → ProcK (layerLayout A₂ K D₂ S) (Fin rr → ℂ) k) (w : Role .complex 100)
    (v : Vertex .complex 100) (Bk : ℕ) (hch : ∀ t, chargeK cs2 gateCharge k (childOf t) ≤ Bk) :
    ((coreEdgeOpsAt (A := A₂) (K := K) (D := D₂) (S := S) (rr := rr) ρ f j0 cdat childOf w v).map
      (RoleOp.chg cs2 gateCharge (chargeK cs2 gateCharge k))).sum ≤ mH * Bk := by
  unfold coreEdgeOpsAt
  split
  · next e he =>
    have he' : e ∈ edges w := by
      unfold edgeInto at he
      exact List.mem_of_find?_eq_some he
    calc _ ≤ (cdat e).basis.length * Bk := chg_coreEdgeOps_le ρ f j0 (cdat e) childOf _ Bk hch
      _ ≤ mH * Bk := Nat.mul_le_mul_right _ (valid_basis_length_le (hval w e he'))
  · simp

/-- **One node.** If every child charges at most `Bk`, the role operations of a node charge at most
`gateSumOf gateCharge + 13 W_c m Bk`: masks, phases and the relabelling are free, every gate row
costs `gateCharge`, every wire meets at most `12` gate rows plus its sink, and every edge calls at
most `m` children. -/
theorem chg_cxNodeOps_le (ρ f j0 : ℕ) (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (childOf : ℕ → ProcK (layerLayout A₂ K D₂ S) (Fin rr → ℂ) k) (Bk : ℕ)
    (hch : ∀ t, chargeK cs2 gateCharge k (childOf t) ≤ Bk) :
    ((cxNodeOps (A := A₂) (K := K) (D := D₂) (S := S) (rr := rr) ρ f j0 cdat childOf).map
      (RoleOp.chg cs2 gateCharge (chargeK cs2 gateCharge k))).sum ≤
        gateSumOf gateCharge + 13 * Wc * mH * Bk := by
  unfold cxNodeOps
  simp only [sum_map_append, sum_map_flatMap]
  refine arith_node (gateSumOf gateCharge) Wc mH Bk _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · -- the masks `Z_a` on the `X` wires
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hro
    rfl
  · -- the masks and phases on the `Y`/`X` wires
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    rfl
  · -- the relabelling
    rfl
  · -- the gate rows with the edges entering them
    simp only [chg_gateOpC]
    refine le_trans (le_of_eq (sum4_split _ _ _ _ _ gateCharge)) ?_
    rw [gateSumOf_eq]
    refine add_le_swap _ _ _ ?_
    refine le_trans (le_of_eq (sum4_eq_fintype [Stage.one, .two, .three]
      (Finset.univ : Finset (Fix 100)).toList (List.finRange 8)
      (Finset.univ : Finset (Role .complex 100)).toList sum_stage_list
      (fun g => Finset.sum_map_toList _ g) (fun g => (Fin.sum_univ_def g).symm)
      (fun g => Finset.sum_map_toList _ g) _)) ?_
    refine le_trans (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun ι _ =>
      Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun w _ => ?_) (sum_ind_le Bk)
    unfold ind
    cases hga : gateAt j ι r w with
    | none => simp
    | some g =>
      refine le_trans (chg_coreEdgeOpsAt_le ρ f j0 cdat hval childOf w (.gate g) Bk hch) ?_
      simp
  · -- the sink edges
    rw [Finset.sum_map_toList]
    refine le_trans (Finset.sum_le_sum fun w _ =>
      chg_coreEdgeOpsAt_le ρ f j0 cdat hval childOf w _ Bk hch) ?_
    exact le_of_eq (by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul])

end Node

/-! ## Part E: the charge accounting of the three phases -/

/-- Phase 1/3 step charges: kernels `1`, the scalar `b^D` (`D/2+1`), everything else `0`. -/
def cs13 {L : Layout} {rr : ℕ} (D : ℕ) : Step L (Fin rr → ℂ) → ℕ
  | .digitGate _ _ => 1
  | .recMap _ => D / 2 + 1
  | _ => 0

/-- The charge bound of `cCoreProc` at level `k`: leaves below `kLeaf`, and above it a node with
overhead `E` and `s`-fold child charge. -/
def Bseq (s E kLeaf : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => if k + 1 < kLeaf then mH ^ (k + 1) else E + s * Bseq s E kLeaf k

theorem Bseq_zero (s E kLeaf : ℕ) : Bseq s E kLeaf 0 = 1 := rfl

theorem Bseq_succ_lt {s E kLeaf k : ℕ} (h : k + 1 < kLeaf) :
    Bseq s E kLeaf (k + 1) = mH ^ (k + 1) := by
  rw [Bseq]
  exact if_pos h

theorem Bseq_succ_not_lt {s E kLeaf k : ℕ} (h : ¬ k + 1 < kLeaf) :
    Bseq s E kLeaf (k + 1) = E + s * Bseq s E kLeaf k := by
  rw [Bseq]
  exact if_neg h

theorem chargeK_zero_eq {L : Layout} {β : Type} (cs : Step L β → ℕ) (cg : ℕ) (p : ProcK L β 0) :
    chargeK cs cg 0 p = ((@id (List (Step L β)) p).map cs).sum := rfl

theorem chargeK_succ_eq {L : Layout} {β : Type} (cs : Step L β → ℕ) (cg k : ℕ)
    (p : ProcK L β (k + 1)) :
    chargeK cs cg (k + 1) p = ((@id (List (Model.Op L β (ProcK L β k))) p).map
      (LayerGuardRun.Op.chg cs cg (chargeK cs cg k))).sum := rfl

theorem chg_node {L : Layout} {β : Type} {Child : Type} (cs : Step L β → ℕ) (cg : ℕ)
    (cc : Child → ℕ) (W : ℕ) (hW : 0 < W) (ops : List (RoleOp L β W Child)) :
    LayerGuardRun.Op.chg cs cg cc (Model.Op.node W hW ops) = (ops.map (RoleOp.chg cs cg cc)).sum :=
  rfl

theorem cCoreProc_succ_lt {A K D S rr ρ kLeaf : ℕ}
    {cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData} {k j0 : ℕ}
    (h : k + 1 < kLeaf) :
    cCoreProc A K D S rr ρ kLeaf cdat (k + 1) j0 =
      (List.range (mH ^ (k + 1))).flatMap fun t =>
        (dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) (selField K ρ (j0 + t))).map
          Model.Op.prim := by
  simp only [cCoreProc]
  exact if_pos h

theorem cCoreProc_succ_not_lt {A K D S rr ρ kLeaf : ℕ}
    {cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData} {k j0 : ℕ}
    (h : ¬ k + 1 < kLeaf) :
    cCoreProc A K D S rr ρ kLeaf cdat (k + 1) j0 =
      [.node Wc Wc_pos (cxNodeOps ρ (mH ^ k) j0 cdat
        (fun t => cCoreProc A K D S rr ρ kLeaf cdat k (j0 + t * mH ^ k)))] := by
  simp only [cCoreProc]
  exact if_neg h

theorem sum_range_le_of_le_one (n : ℕ) (f : ℕ → ℕ) (hf : ∀ t, f t ≤ 1) :
    ((List.range n).map f).sum ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have := hf n
    omega

theorem chg_dgate_le {A K D S rr : ℕ} (i : ℕ) :
    ((dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) i).map cs2).sum ≤ 1 := by
  unfold dgate
  split_ifs <;> simp [cs2]

/-- **Charge of the Lemma A.10 (`lem:transfer-phase`) core.** Given a node bound `E + s · B` (for children charging `≤ B`), the
procedure `cCoreProc … k j0` charges at most `Bseq s E kLeaf k`. -/
theorem chargeK_cCore_le (A₂ K D₂ S rr ρ kLeaf : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (s E : ℕ)
    (hnode : ∀ (f j0 k Bk : ℕ) (childOf : ℕ → ProcK (layerLayout A₂ K D₂ S) (Fin rr → ℂ) k),
      (∀ t, chargeK cs2 gateCharge k (childOf t) ≤ Bk) →
      ((cxNodeOps (A := A₂) (K := K) (D := D₂) (S := S) (rr := rr) ρ f j0 cdat childOf).map
        (RoleOp.chg cs2 gateCharge (chargeK cs2 gateCharge k))).sum ≤ E + s * Bk) :
    ∀ (k j0 : ℕ), chargeK cs2 gateCharge k (cCoreProc A₂ K D₂ S rr ρ kLeaf cdat k j0) ≤
      Bseq s E kLeaf k := by
  intro k
  induction k with
  | zero =>
    intro j0
    rw [chargeK_zero_eq]
    exact chg_dgate_le (A := A₂) (K := K) (D := D₂) (S := S) (rr := rr) (selField K ρ j0)
  | succ k ih =>
    intro j0
    by_cases hk : k + 1 < kLeaf
    · rw [chargeK_succ_eq, cCoreProc_succ_lt hk, Bseq_succ_lt hk, id_eq, sum_map_flatMap]
      refine sum_range_le_of_le_one _ _ fun t => ?_
      rw [List.map_map]
      exact chg_dgate_le (A := A₂) (K := K) (D := D₂) (S := S) (rr := rr) (selField K ρ (j0 + t))
    · rw [chargeK_succ_eq, cCoreProc_succ_not_lt hk, Bseq_succ_not_lt hk, id_eq, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, chg_node]
      exact hnode (mH ^ k) j0 k (Bseq s E kLeaf k) _ (fun t => ih _)

theorem layerLayout_r_sel {A K D S ρ j : ℕ} (hρ : ρ < K) (hj : j < D)
    (h : selField K ρ j < (layerLayout A K D S).n) :
    (layerLayout A K D S).r ⟨selField K ρ j, h⟩ = 2 := by
  have h1 : j * K + K ≤ D * K := by
    have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hj)
    simpa [Nat.succ_mul] using this
  show (if selField K ρ j = 0 then A else if selField K ρ j ≤ D * K then 2 else S) = 2
  unfold selField
  rw [if_neg (by omega), if_pos (by omega)]

theorem stepOK_dgate (P : ℕ) {A K D S rr ρ j : ℕ} (hρ : ρ < K) (hj : j < D)
    (s : Step (layerLayout A K D S) (Fin rr → ℂ)) (hs : s ∈ dgate (selField K ρ j)) :
    StepOK (ptG (rr := rr) P) s 1 ∧ cs2 s = 1 ∧ cs13 D s = 1 := by
  unfold dgate at hs
  split_ifs at hs with h
  · rw [List.mem_singleton] at hs
    subst hs
    exact ⟨stepOK_digitGate_cGate P _ (layerLayout_r_sel hρ hj h), rfl, rfl⟩
  · simp at hs

theorem chargeOK_phase1 (P A K D S rr ρ d : ℕ) (hρ : ρ < K) :
    ChargeOK (ptG (rr := rr) P) (cs13 D) gateCharge 0 (layerPhase1 A K D S rr ρ d) := by
  intro s hs
  have hs' : s ∈ ([sDiag ρ] ++ (List.range (min (q0Of d) D)).flatMap fun j =>
      dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) (selField K ρ j) :
        List (Step (layerLayout A K D S) (Fin rr → ℂ))) := hs
  rcases List.mem_append.mp hs' with h | h
  · rw [List.mem_singleton] at h
    subst h
    exact stepOK_addrMap_phase P _ (fun x => phase_I_pow _)
  · obtain ⟨j, hj, hs2⟩ := List.mem_flatMap.mp h
    rw [List.mem_range] at hj
    obtain ⟨hok, -, h13⟩ := stepOK_dgate P hρ (lt_of_lt_of_le hj (min_le_right _ _)) s hs2
    rw [h13]
    exact hok

theorem chargeK_phase1_le (A K D S rr ρ d : ℕ) :
    chargeK (cs13 (L := layerLayout A K D S) (rr := rr) D) gateCharge 0
      (layerPhase1 A K D S rr ρ d) ≤ D := by
  show ((([sDiag ρ] ++ (List.range (min (q0Of d) D)).flatMap fun j =>
      dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) (selField K ρ j) :
        List (Step (layerLayout A K D S) (Fin rr → ℂ)))).map (cs13 D)).sum ≤ D
  rw [sum_map_append, sum_map_flatMap]
  have h0 : (([sDiag ρ] : List (Step (layerLayout A K D S) (Fin rr → ℂ))).map (cs13 D)).sum = 0 := rfl
  rw [h0, zero_add]
  have hle : ∀ j, ((dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) (selField K ρ j)).map
      (cs13 D)).sum ≤ 1 := by
    intro j
    unfold dgate
    split_ifs <;> simp [cs13]
  exact le_trans (sum_range_le_of_le_one _ _ hle) (min_le_right _ _)

theorem phase3_take (A K D S rr ρ P : ℕ) :
    (layerPhase3 A K D S rr ρ P).take 2 = [sDiag ρ, .recMap fun v => bD D • v] := rfl

theorem chargeOK_phase3 (P A K D S rr ρ : ℕ) :
    ChargeOK (ptG (rr := rr) P) (cs13 D) gateCharge 0 ((layerPhase3 A K D S rr ρ P).take 2) := by
  rw [phase3_take]
  intro s hs
  simp only [id, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl
  · exact stepOK_addrMap_phase P _ (fun x => phase_I_pow _)
  · exact stepOK_recMap_bD P D

theorem chargeK_phase3 (P A K D S rr ρ : ℕ) :
    chargeK (cs13 (L := layerLayout A K D S) (rr := rr) D) gateCharge 0
      ((layerPhase3 A K D S rr ρ P).take 2) = D / 2 + 1 := by
  rw [phase3_take]
  show cs13 (L := layerLayout A K D S) (rr := rr) D (sDiag ρ) +
    (cs13 (L := layerLayout A K D S) (rr := rr) D (Step.recMap fun v => bD D • v) + 0) = D / 2 + 1
  have h1 : cs13 (L := layerLayout A K D S) (rr := rr) D (sDiag ρ) = 0 := rfl
  have h2 : cs13 (L := layerLayout A K D S) (rr := rr) D (Step.recMap fun v => bD D • v) =
    D / 2 + 1 := rfl
  rw [h1, h2]
  omega

theorem chargeOK_phase2 (P A K D S rr ρ d : ℕ) (hρ : ρ < K)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) :
    ∀ q ∈ layerPhase2 A K D S rr ρ d cdat, ChargeOK (ptG (rr := rr) P) cs2 gateCharge q.1 q.2 := by
  intro q hq
  simp only [layerPhase2, List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact chargeOK_cCoreProc P (A * padR d K) K (D - q0Of d) S rr ρ (kLeafOf d) hρ cdat hval p.1 p.2
    (piecesOf_bound _ p hp)

theorem chargeK_phase2_le (A K D S rr ρ d : ℕ)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData) (s E : ℕ)
    (hnode : ∀ (f j0 k Bk : ℕ)
      (childOf : ℕ → ProcK (layerLayout (A * padR d K) K (D - q0Of d) S) (Fin rr → ℂ) k),
      (∀ t, chargeK cs2 gateCharge k (childOf t) ≤ Bk) →
      ((cxNodeOps (A := A * padR d K) (K := K) (D := D - q0Of d) (S := S) (rr := rr) ρ f j0 cdat
        childOf).map (RoleOp.chg cs2 gateCharge (chargeK cs2 gateCharge k))).sum ≤ E + s * Bk) :
    ((layerPhase2 A K D S rr ρ d cdat).map fun q => chargeK cs2 gateCharge q.1 q.2).sum ≤
      ((piecesOf (D - q0Of d)).map fun p => Bseq s E (kLeafOf d) p.1).sum := by
  simp only [layerPhase2, List.map_map]
  exact List.sum_le_sum fun p _ =>
    chargeK_cCore_le (A * padR d K) K (D - q0Of d) S rr ρ (kLeafOf d) cdat s E hnode p.1 p.2

/-- **Assembly.** The three phase charge bounds give `LayerGuarded` as soon as
`D + Σ_pieces Bseq + (D/2 + 1) ≤ Δ`. -/
theorem layerGuarded_of_bound (P d rr K D A S ρ : ℕ) (hρ : ρ < K)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hval : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (z : RArr (LayerAddr A K D S) rr) (hz : ArrOnDiskGrid P z) (Δ s E : ℕ)
    (hnode : ∀ (f j0 k Bk : ℕ)
      (childOf : ℕ → ProcK (layerLayout (A * padR d K) K (D - q0Of d) S) (Fin rr → ℂ) k),
      (∀ t, chargeK cs2 gateCharge k (childOf t) ≤ Bk) →
      ((cxNodeOps (A := A * padR d K) (K := K) (D := D - q0Of d) (S := S) (rr := rr) ρ f j0 cdat
        childOf).map (RoleOp.chg cs2 gateCharge (chargeK cs2 gateCharge k))).sum ≤ E + s * Bk)
    (hΔ : D + ((piecesOf (D - q0Of d)).map fun p => Bseq s E (kLeafOf d) p.1).sum + (D / 2 + 1)
      ≤ Δ) :
    LayerGuarded P A K D S rr ρ d Δ cdat z :=
  LayerGuardAsm.layerGuarded_of_charges P d rr K D A S ρ cdat z hz Δ (cs13 D) (cs13 D) cs2
    gateCharge D ((piecesOf (D - q0Of d)).map fun p => Bseq s E (kLeafOf d) p.1).sum (D / 2 + 1)
    (chargeOK_phase1 P A K D S rr ρ d hρ) (chargeK_phase1_le A K D S rr ρ d)
    (chargeOK_phase2 P A K D S rr ρ d hρ cdat hval)
    (chargeK_phase2_le A K D S rr ρ d cdat s E hnode)
    (chargeOK_phase3 P A K D S rr ρ) (le_of_eq (chargeK_phase3 P A K D S rr ρ)) hΔ

/-! ## Part F: the numeric bound (all lemmas about variables) -/

theorem le_13 (w m : ℕ) (hw : 0 < w) : m ≤ 13 * w * m := by
  have h1 : 1 ≤ 13 * w := by omega
  calc m = 1 * m := (one_mul m).symm
    _ ≤ 13 * w * m := Nat.mul_le_mul_right m h1

theorem one_lt_13 (w m : ℕ) (hw : 0 < w) (hm : 0 < m) : 1 < 13 * w * m := by
  have h1 : 13 ≤ 13 * w := by omega
  have h2 : 13 ≤ 13 * w * m := le_trans h1 (Nat.le_mul_of_pos_right _ hm)
  omega

theorem lg_mH_pos : 0 < mH := by norm_num [mH]

/-- `13 W m < m^5` once `W = tripleWc 100` (`≈ 2.4·10^{28} < 10^{30}`). -/
theorem s13_lt (w : ℕ) (hw : w = tripleWc 100) : ((13 * w * mH : ℕ) : ℝ) < (mH : ℝ) ^ 5 := by
  subst hw
  have h : 13 * tripleWc 100 * mH < mH ^ 5 := by decide
  exact_mod_cast h

theorem cdep_nonneg (s E : ℕ) (hs : 1 < s) : 0 ≤ (s : ℝ) * (8 + (E : ℝ) / ((s : ℝ) - 1)) := by
  have hs' : (1 : ℝ) < s := by exact_mod_cast hs
  have h : 0 ≤ (E : ℝ) / ((s : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) (by linarith)
  exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (by norm_num) h)

theorem pow_le_Bseq (s E kLeaf : ℕ) (hms : mH ≤ s) : ∀ j, mH ^ j ≤ Bseq s E kLeaf j := by
  intro j
  induction j with
  | zero => simp [Bseq_zero]
  | succ j ih =>
    by_cases hk : j + 1 < kLeaf
    · rw [Bseq_succ_lt hk]
    · rw [Bseq_succ_not_lt hk, pow_succ']
      exact le_trans (Nat.mul_le_mul hms ih) (Nat.le_add_left _ _)

theorem Bseq_succ_le (s E kLeaf j : ℕ) (hms : mH ≤ s) :
    Bseq s E kLeaf (j + 1) ≤ s * Bseq s E kLeaf j + E := by
  by_cases hk : j + 1 < kLeaf
  · rw [Bseq_succ_lt hk, pow_succ']
    exact le_trans (Nat.mul_le_mul hms (pow_le_Bseq s E kLeaf hms j)) (Nat.le_add_right _ _)
  · rw [Bseq_succ_not_lt hk]
    exact le_of_eq (Nat.add_comm _ _)

theorem Bseq_le_real (s E kLeaf k : ℕ) (hs1 : 1 < s) (hms : mH ≤ s)
    (hs5 : (s : ℝ) < (mH : ℝ) ^ 5) (d : ℝ) (hd : 1 ≤ d) (hk : (mH : ℝ) ^ k ≤ d) :
    (Bseq s E kLeaf k : ℝ) ≤ (s : ℝ) * (8 + (E : ℝ) / ((s : ℝ) - 1)) * d ^ 6 := by
  have hm : (1 : ℝ) < mH := by norm_num [mH]
  refine guardRecurrence_holds (mH : ℝ) (s : ℝ) (E : ℝ) d k (fun j => (Bseq s E kLeaf j : ℝ)) hm
    (by exact_mod_cast hs1) hs5 (Nat.cast_nonneg _) hd ?_ ?_ ?_
  · exact le_trans (pow_le_pow_right₀ hm.le (Nat.sub_le k 1)) hk
  · simp only [Bseq_zero, Nat.cast_one]
    linarith
  · intro j _
    have h := Bseq_succ_le s E kLeaf j hms
    exact_mod_cast h

theorem total_bound (C0 M Cdep : ℝ) (d D : ℕ) (xs : List ℕ) (hd1 : (1 : ℝ) ≤ d) (hDd : D ≤ d)
    (hCdep0 : 0 ≤ Cdep) (hM : 1 ≤ M) (hxs : ∀ x ∈ xs, (x : ℝ) ≤ Cdep * (d : ℝ) ^ 6)
    (hlen : xs.length ≤ d) (hgrow : (M * Cdep + 18) * (d : ℝ) ^ 7 ≤ C0 * (d : ℝ) ^ 14) :
    D + xs.sum + (D / 2 + 1) ≤ ⌈C0 * (d : ℝ) ^ 14⌉₊ := by
  have hS : ((xs.sum : ℕ) : ℝ) ≤ (d : ℝ) * (Cdep * (d : ℝ) ^ 6) := by
    rw [Nat.cast_list_sum]
    have h1 := List.sum_le_card_nsmul (xs.map (Nat.cast : ℕ → ℝ)) (Cdep * (d : ℝ) ^ 6) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hxs y hy)
    rw [List.length_map, nsmul_eq_mul] at h1
    have hlen' : (xs.length : ℝ) ≤ d := by exact_mod_cast hlen
    exact le_trans h1 (mul_le_mul_of_nonneg_right hlen' (by positivity))
  have hD : (D : ℝ) ≤ d := by exact_mod_cast hDd
  have hDh : ((D / 2 : ℕ) : ℝ) ≤ d := by
    have : D / 2 ≤ d := le_trans (Nat.div_le_self _ _) hDd
    exact_mod_cast this
  have hd7 : (d : ℝ) ≤ (d : ℝ) ^ 7 := by
    calc (d : ℝ) = (d : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (d : ℝ) ^ 7 := pow_le_pow_right₀ hd1 (by norm_num)
  have h1d7 : (1 : ℝ) ≤ (d : ℝ) ^ 7 := one_le_pow₀ hd1
  have hdd : (d : ℝ) * (Cdep * (d : ℝ) ^ 6) = Cdep * (d : ℝ) ^ 7 := by ring
  rw [hdd] at hS
  have hmono : (Cdep + 3) * (d : ℝ) ^ 7 ≤ (M * Cdep + 18) * (d : ℝ) ^ 7 := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith
  have key : ((D + xs.sum + (D / 2 + 1) : ℕ) : ℝ) ≤ C0 * (d : ℝ) ^ 14 := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_one]
    have e1 : (D : ℝ) + (xs.sum : ℝ) + (((D / 2 : ℕ) : ℝ) + 1) ≤ (Cdep + 3) * (d : ℝ) ^ 7 := by
      nlinarith
    linarith
  exact_mod_cast le_trans key (Nat.le_ceil _)

end SubNLogN.Math.Networks.LayerGuardAux

namespace SubNLogN.Math.Networks

open LayerGuardAux LayerGuardRun LayerGuardSteps LayerGuardCore

/-- **Proposition A.11 (`prop:prop14-param`) guard** (Appendix A.6 (`sec:transfer-layer`), eq. (`eq:walsh-guard-growth`)):
in the `ε = 1/15` band, with `Δ = ⌈C₀ d^{14}⌉`, every intermediate array of a layer run on a disk-grid
input is on the guard grid. (`GuardSmallStmt` and `a_d ≤ b_d` are not needed for this conclusion.) -/
theorem prop71Guard_holds : Prop71GuardStmt := by
  intro hcert hgrowth _hsmall cdat hval aD bD haD _hab
  have hs1 : 1 < 13 * Wc * mH := one_lt_13 Wc mH Wc_pos lg_mH_pos
  have hms : mH ≤ 13 * Wc * mH := le_13 Wc mH Wc_pos
  have hs5 : ((13 * Wc * mH : ℕ) : ℝ) < (mH : ℝ) ^ 5 := s13_lt Wc hcert.card_roles
  obtain ⟨Cdep, hCdep⟩ : ∃ C : ℝ, C = ((13 * Wc * mH : ℕ) : ℝ) *
      (8 + ((gateSumOf gateCharge : ℕ) : ℝ) / (((13 * Wc * mH : ℕ) : ℝ) - 1)) := ⟨_, rfl⟩
  have hCdep0 : 0 ≤ Cdep := by
    rw [hCdep]
    exact cdep_nonneg (13 * Wc * mH) (gateSumOf gateCharge) hs1
  obtain ⟨dstar, hdstar⟩ := hgrowth Cdep 14 le_rfl
  refine ⟨(max (dstar : ℝ) 1 / aD) ^ (15 : ℕ), ?_⟩
  intro P d rr K D A S ρ z hP hd1 _hd2 _hK _hD1 hDd hz
  have hM : 0 ≤ max (dstar : ℝ) 1 / aD :=
    div_nonneg (le_trans zero_le_one (le_max_right _ _)) haD.le
  have hroot : ((max (dstar : ℝ) 1 / aD) ^ (15 : ℕ)) ^ ((1 : ℝ) / 15) = max (dstar : ℝ) 1 / aD := by
    rw [show ((1 : ℝ) / 15) = ((15 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast hM (by norm_num)
  have hPr : max (dstar : ℝ) 1 / aD ≤ (P : ℝ) ^ ((1 : ℝ) / 15) := by
    rw [← hroot]
    exact Real.rpow_le_rpow (pow_nonneg hM _) hP (by norm_num)
  have hdM : max (dstar : ℝ) 1 ≤ d := by
    calc max (dstar : ℝ) 1 = aD * (max (dstar : ℝ) 1 / aD) := by
          rw [← mul_div_assoc, mul_div_cancel_left₀ _ haD.ne']
      _ ≤ aD * (P : ℝ) ^ ((1 : ℝ) / 15) := mul_le_mul_of_nonneg_left hPr haD.le
      _ ≤ d := hd1
  have hd1' : (1 : ℝ) ≤ d := le_trans (le_max_right _ _) hdM
  have hdstar' : dstar ≤ d := by exact_mod_cast le_trans (le_max_left _ _) hdM
  refine layerGuarded_of_bound P d rr K D A S ρ.val ρ.isLt cdat hval z hz _ (13 * Wc * mH)
    (gateSumOf gateCharge) (fun f j0 k Bk childOf hch =>
      chg_cxNodeOps_le ρ.val f j0 cdat hval childOf Bk hch) ?_
  refine total_bound (guardC0 100 : ℝ) (tripleM 100 : ℝ) Cdep d D _ hd1' hDd hCdep0
    (by norm_num [tripleM]) ?_ ?_ (hdstar d hdstar')
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hb := piecesOf_bound _ p hp
    have hk : (mH : ℝ) ^ p.1 ≤ d := by
      have : mH ^ p.1 ≤ d := by omega
      exact_mod_cast this
    rw [hCdep]
    exact Bseq_le_real (13 * Wc * mH) (gateSumOf gateCharge) (kLeafOf d) p.1 hs1 hms hs5 d hd1' hk
  · rw [List.length_map]
    exact le_trans (piecesOf_length_le _) (le_trans (Nat.sub_le _ _) hDd)

end SubNLogN.Math.Networks
