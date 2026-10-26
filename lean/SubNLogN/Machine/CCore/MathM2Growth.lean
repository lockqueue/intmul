/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.SkelCode
import SubNLogN.Math.Networks.Proofs.LayerGuardSteps
import SubNLogN.S1.Params

/-!
# CCORE-M2 (I): growth of the value-level effects of the node operations

Per-operation growth facts used by `NodeGrowthStmt` (`CCore/SkelMathDefs.lean`). For the growth
bound `ArrGrowth P b` (every coefficient on the `2^{-(P+b)}`-grid with modulus `≤ 2^b`):
* phase kernels (`runSteps [phaseStep t κ]`) and Lemma A.9 row additions (`runSteps (rowAddSteps …)`)
  preserve the bound (unit phases `i^n`, resp. address permutations);
* a scalar row (`gateVal`) raises it by at most `gateG = 102` (`LayerGuardSteps.Aux.rowUpd_bound`,
  charge `h + 1 = 101` on Gaussian dyadics, plus one bit for the modulus conversion);
* a child (`childVal`) raises it by at most `f = m^{k-1}` (`C^{⊗f}` has `2^f` terms with coefficients
  of modulus `≤ 1` in `ℤ[i]/2^f`).
All helpers live in `SubNLogN.Machine.CCore.M2Aux`.
-/

namespace SubNLogN.Machine.CCore

namespace M2Aux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Math.Walsh SubNLogN.Math.Common
open SubNLogN.Math.Networks

/-- A coefficient within growth bound `b` at root precision `P`. -/
def GoodV (P b : ℕ) (z : ℂ) : Prop := OnGrid (P + b) z ∧ ‖z‖ ≤ 2 ^ b

theorem arrGrowth_iff {α : Type} {r P b : ℕ} (z : RArr α r) :
    ArrGrowth P b z ↔ ∀ x k, GoodV P b (z x k) := Iff.rfl

/-! ### Grids and monotonicity -/

theorem onGridR_mono {q q' : ℕ} (h : q ≤ q') {x : ℝ} (hx : OnGridR q x) : OnGridR q' x := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨a * 2 ^ (q' - q), ?_⟩
  unfold gridUnit
  have h2 : (2 : ℝ) ^ q' = 2 ^ q * 2 ^ (q' - q) := by
    rw [← pow_add]; congr 1; omega
  rw [h2]
  push_cast
  field_simp

theorem onGrid_mono {q q' : ℕ} (h : q ≤ q') {z : ℂ} (hz : OnGrid q z) : OnGrid q' z :=
  ⟨onGridR_mono h hz.1, onGridR_mono h hz.2⟩

theorem goodV_mono {P b b' : ℕ} (h : b ≤ b') {z : ℂ} (hz : GoodV P b z) : GoodV P b' z :=
  ⟨onGrid_mono (by omega) hz.1, hz.2.trans (pow_le_pow_right₀ (by norm_num) h)⟩

theorem arrGrowth_mono {α : Type} {r P b b' : ℕ} (h : b ≤ b') {z : RArr α r}
    (hz : ArrGrowth P b z) : ArrGrowth P b' z :=
  fun x k => goodV_mono h (hz x k)

/-! ### Unit phases -/

theorem goodV_mulI {P b : ℕ} {z : ℂ} (hz : GoodV P b z) : GoodV P b (Complex.I * z) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨a', ha'⟩⟩, hn⟩ := hz
  refine ⟨⟨⟨-a', ?_⟩, ⟨a, ?_⟩⟩, ?_⟩
  · rw [Complex.I_mul_re, ha']; push_cast; ring
  · rw [Complex.I_mul_im, ha]
  · rw [norm_mul, Complex.norm_I, one_mul]; exact hn

theorem goodV_Ipow (n : ℕ) {P b : ℕ} {z : ℂ} (hz : GoodV P b z) :
    GoodV P b (Complex.I ^ n * z) := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [pow_succ, mul_comm (Complex.I ^ n) Complex.I, mul_assoc]
    exact goodV_mulI ih

theorem goodV_negOnePow (n : ℕ) {P b : ℕ} {z : ℂ} (hz : GoodV P b z) :
    GoodV P b ((-1 : ℂ) ^ n * z) := by
  have h : (-1 : ℂ) ^ n = Complex.I ^ (2 * n) := by
    rw [pow_mul, Complex.I_sq]
  rw [h]; exact goodV_Ipow _ hz

theorem goodV_negIPow (n : ℕ) {P b : ℕ} {z : ℂ} (hz : GoodV P b z) :
    GoodV P b ((-Complex.I) ^ n * z) := by
  have h : (-Complex.I) ^ n = Complex.I ^ (3 * n) := by
    rw [pow_mul]
    congr 1
    rw [pow_succ, Complex.I_sq]; ring
  rw [h]; exact goodV_Ipow _ hz

theorem goodV_neg {P b : ℕ} {z : ℂ} (hz : GoodV P b z) : GoodV P b ((-1 : ℂ) * z) := by
  simpa using goodV_negOnePow 1 hz

/-! ### Steps that preserve the growth bound -/

/-- A step maps arrays within growth bound `b` to arrays within growth bound `b`. -/
def StepPres (P b : ℕ) {Ly : Model.Layout} {r : ℕ} (s : Model.Step Ly (Fin r → ℂ)) : Prop :=
  ∀ B : Ly.Addr → Fin r → ℂ, (∀ y k, GoodV P b (B y k)) → ∀ y k, GoodV P b (s.run B y k)

/-- Steps that only move records. -/
def IsPullStep {Ly : Model.Layout} {β : Type} : Model.Step Ly β → Prop
  | .elem _ => True
  | .sparsePerm _ _ => True
  | .swapBlocks _ _ _ => True
  | _ => False

theorem stepPres_of_isPull {P b : ℕ} {Ly : Model.Layout} {r : ℕ} (s : Model.Step Ly (Fin r → ℂ))
    (hs : IsPullStep s) : StepPres P b s := by
  intro B hB y k
  cases s with
  | elem e => exact hB _ k
  | sparsePerm pull supp => exact hB _ k
  | swapBlocks t₀ s₀ len => exact hB _ k
  | recMap f => exact absurd hs (by simp [IsPullStep])
  | addrMap f => exact absurd hs (by simp [IsPullStep])
  | digitGate i G => exact absurd hs (by simp [IsPullStep])

theorem stepPres_addrMap {P b : ℕ} {Ly : Model.Layout} {r : ℕ} (c : Ly.Addr → ℂ)
    (hc : ∀ x {z : ℂ}, GoodV P b z → GoodV P b (c x * z)) :
    StepPres P b (Model.Step.addrMap (β := Fin r → ℂ) fun x v => c x • v) := by
  intro B hB y k
  show GoodV P b ((c y • B y) k)
  rw [Pi.smul_apply, smul_eq_mul]
  exact hc y (hB y k)

theorem stepPres_recMap {P b : ℕ} {Ly : Model.Layout} {r : ℕ} (c : ℂ)
    (hc : ∀ {z : ℂ}, GoodV P b z → GoodV P b (c * z)) :
    StepPres P b (Model.Step.recMap (L := Ly) (β := Fin r → ℂ) fun v => c • v) := by
  intro B hB y k
  show GoodV P b ((c • B y) k)
  rw [Pi.smul_apply, smul_eq_mul]
  exact hc (hB y k)

/-- `runSteps` with growth-preserving steps preserves the growth bound. -/
theorem runSteps_growth {A K D S r P b : ℕ}
    (ss : List (Model.Step (layerLayout A K D S) (Fin r → ℂ))) (hss : ∀ s ∈ ss, StepPres P b s)
    (w : RArr (LayerAddr A K D S) r) (hw : ArrGrowth P b w) : ArrGrowth P b (runSteps ss w) := by
  have key : ∀ (l : List (Model.Step (layerLayout A K D S) (Fin r → ℂ))),
      (∀ s ∈ l, StepPres P b s) → ∀ B : (layerLayout A K D S).Addr → Fin r → ℂ,
      (∀ y k, GoodV P b (B y k)) → ∀ y k, GoodV P b (l.foldl (fun B s => s.run B) B y k) := by
    intro l
    induction l with
    | nil => intro _ B hB; exact hB
    | cons s l ih =>
      intro hl B hB
      rw [List.foldl_cons]
      exact ih (fun s' hs' => hl s' (List.mem_cons_of_mem _ hs'))
        _ (hl s (List.mem_cons_self) B hB)
  intro x k
  exact key ss hss (encodeArr w) (fun y k => hw _ k) (encodeAddr x) k

/-! ### Phase kernels and row additions -/

theorem stepPres_phaseStep (P b : ℕ) (t : CCoreRT) (κ : PhaseKind) :
    StepPres P b (phaseStep t κ) := by
  cases κ with
  | zMask a => exact stepPres_addrMap _ (fun _ _ hz => goodV_negOnePow _ hz)
  | zSlot sl => exact stepPres_addrMap _ (fun _ _ hz => goodV_negOnePow _ hz)
  | negIPow => exact stepPres_recMap _ (fun hz => goodV_negIPow _ hz)
  | iPow27 => exact stepPres_recMap _ (fun hz => goodV_Ipow _ hz)
  | neg => exact stepPres_recMap _ (fun hz => goodV_neg hz)

theorem lineSteps_pull {Ly : Model.Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3)
    (op : Bool × ℤ × ℕ) : ∀ s ∈ lineSteps (Ly := Ly) (β := β) L K ρ f C op, IsPullStep s := by
  simp only [lineSteps]
  split_ifs <;> simp [IsPullStep]

theorem topBitSteps_pull {Ly : Model.Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3) :
    ∀ s ∈ topBitSteps (Ly := Ly) (β := β) L K ρ f C, IsPullStep s := by
  simp only [topBitSteps]
  split_ifs <;> simp [IsPullStep]

theorem rowAddSteps_pull (t : CCoreRT) (p₁ p₂ : Fin mn) :
    ∀ s ∈ rowAddSteps t p₁ p₂, IsPullStep s := by
  intro s hs
  unfold rowAddSteps packedAddProc at hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨op, -, hs⟩ := List.mem_flatMap.mp hs
      exact lineSteps_pull _ _ _ _ _ op s hs
    · rw [List.mem_singleton] at hs
      subst hs
      simp [repairStep, IsPullStep]
  · exact topBitSteps_pull _ _ _ _ _ s hs

/-! ### Gaussian-dyadic denominators and the child -/

open LayerGuardSteps.Aux in
theorem gden_mul {a c : ℕ} {z w : ℂ} (hz : GDen a z) (hw : GDen c w) : GDen (a + c) (z * w) := by
  obtain ⟨m, n, rfl⟩ := hz
  obtain ⟨m', n', rfl⟩ := hw
  refine ⟨m * m' - n * n', m * n' + n * m', ?_⟩
  rw [pow_add]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

open LayerGuardSteps.Aux in
theorem gden_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i, GDen 1 (f i)) :
    GDen s.card (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, 0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_comm]
    exact gden_mul (hf a) ih

open LayerGuardSteps.Aux in
theorem gden_of_onGrid {q : ℕ} {z : ℂ} (hz : OnGrid q z) : GDen q z := by
  obtain ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ := hz
  refine ⟨a, a', Complex.ext ?_ ?_⟩
  · rw [ha]; unfold gridUnit
    rw [(re_im_of_eq (a := q) (m := a) (n := a') rfl).1]
    ring
  · rw [ha']; unfold gridUnit
    rw [(re_im_of_eq (a := q) (m := a) (n := a') rfl).2]
    ring

open LayerGuardSteps.Aux in
theorem onGrid_of_gden {q : ℕ} {z : ℂ} (hz : GDen q z) : OnGrid q z := by
  obtain ⟨m, n, h⟩ := hz
  obtain ⟨h1, h2⟩ := re_im_of_eq h
  refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
  · rw [h1]; unfold gridUnit; ring
  · rw [h2]; unfold gridUnit; ring

open LayerGuardSteps.Aux in
theorem gden_ka : GDen 1 ka := ⟨1, 1, by simp [ka]⟩

open LayerGuardSteps.Aux in
theorem gden_kb : GDen 1 kb := ⟨1, -1, by simp [kb]; ring⟩

theorem norm_ka_le : ‖ka‖ ≤ 1 := by
  unfold ka
  rw [norm_div]
  have h1 : ‖(1 : ℂ) + Complex.I‖ ≤ 2 := by
    calc ‖(1 : ℂ) + Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one, Complex.norm_I]; norm_num
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  linarith [h1]

theorem norm_kb_le : ‖kb‖ ≤ 1 := by
  unfold kb
  rw [norm_div]
  have h1 : ‖(1 : ℂ) - Complex.I‖ ≤ 2 := by
    calc ‖(1 : ℂ) - Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, Complex.norm_I]; norm_num
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  linarith [h1]

open LayerGuardSteps.Aux in
/-- `C^{⊗D}` raises the growth bound by at most `D`. -/
theorem CD_good (D P b : ℕ) (u : (Fin D → Bool) → ℂ) (hu : ∀ e, GoodV P b (u e))
    (e : Fin D → Bool) : GoodV P (b + D) (CD D u e) := by
  refine ⟨onGrid_of_gden ?_, ?_⟩
  · unfold CD
    refine gden_sum _ _ (fun e' => ?_)
    have hp : GDen D (∏ j, (if e j = e' j then ka else kb)) := by
      have := gden_prod (Finset.univ : Finset (Fin D)) (fun j => if e j = e' j then ka else kb)
        (fun j => by split_ifs; exacts [gden_ka, gden_kb])
      rwa [Finset.card_univ, Fintype.card_fin] at this
    have h2 := gden_mul hp (gden_of_onGrid (hu e').1)
    have h3 : D + (P + b) = P + (b + D) := by ring
    rwa [h3] at h2
  · unfold CD
    calc ‖∑ e' : Fin D → Bool, (∏ j, (if e j = e' j then ka else kb)) * u e'‖
        ≤ ∑ e' : Fin D → Bool, ‖(∏ j, (if e j = e' j then ka else kb)) * u e'‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _e' : Fin D → Bool, (2 : ℝ) ^ b := by
          refine Finset.sum_le_sum (fun e' _ => ?_)
          rw [norm_mul, norm_prod]
          have hp : ∏ j, ‖(if e j = e' j then ka else kb)‖ ≤ 1 := by
            refine Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => ?_)
            split_ifs
            exacts [norm_ka_le, norm_kb_le]
          calc (∏ j, ‖(if e j = e' j then ka else kb)‖) * ‖u e'‖ ≤ 1 * 2 ^ b :=
                mul_le_mul hp (hu e').2 (norm_nonneg _) zero_le_one
            _ = 2 ^ b := one_mul _
      _ = 2 ^ (b + D) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul, pow_add]
          push_cast
          ring

/-- `cCoreVal` on `e` chunks raises the growth bound by at most `e`. -/
theorem cCoreVal_growth {r A K D S P b : ℕ} (ρ : Fin K) (j0 e : ℕ) (h : j0 + e ≤ D)
    (z : RArr (LayerAddr A K D S) r) (hz : ArrGrowth P b z) :
    ArrGrowth P (b + e) (cCoreVal ρ j0 e h z) := by
  intro x k
  exact CD_good e P b _ (fun bs => hz _ k) _

/-- A child call raises the growth bound by at most `f = m^(k-1)`. -/
theorem childVal_growth (t : CCoreRT) (a : Fin mn) {b : ℕ}
    (w : RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r) (hw : ArrGrowth t.P b w) :
    ArrGrowth t.P (b + mn ^ (t.k - 1)) (childVal t a w) := by
  unfold childVal
  split_ifs with h
  · exact cCoreVal_growth _ _ _ h.2 w hw
  · exact arrGrowth_mono (Nat.le_add_right _ _) hw

/-! ### Scalar rows -/

theorem gd_of_goodV {P b : ℕ} {z : ℂ} (hz : GoodV P b z) : GaussDyadic (P + b) b z := by
  obtain ⟨m, n, h⟩ := gden_of_onGrid hz.1
  exact ⟨⟨m, n, h⟩, (Complex.abs_re_le_norm z).trans hz.2, (Complex.abs_im_le_norm z).trans hz.2⟩

theorem goodV_of_gd {a c P b : ℕ} {z : ℂ} (hz : GaussDyadic a c z) (ha : a ≤ P + b)
    (hc : c + 1 ≤ b) : GoodV P b z := by
  obtain ⟨⟨m, n, h⟩, hre, him⟩ := hz
  refine ⟨onGrid_mono ha (onGrid_of_gden ⟨m, n, h⟩), ?_⟩
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 2 ^ c + 2 ^ c := add_le_add hre him
    _ = 2 ^ (c + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hc

/-- The growth charge of one scalar row. -/
def gateG : ℕ := 102

/-- A scalar row raises the growth bound of all role streams by at most `gateG`. -/
theorem gateVal_growth (j : Stage) (ι : Fix 100) (r : Fin 8) {A K D S rr P b : ℕ}
    (w : Fin Wn → RArr (LayerAddr A K D S) rr) (hw : ∀ u, ArrGrowth P b (w u)) :
    ∀ u, ArrGrowth P (b + gateG) (gateVal j ι r w u) := by
  intro u x k
  have h := LayerGuardSteps.Aux.rowUpd_bound j ι (rowOp j r) _ (LayerGuardSteps.Aux.rowSign_cases j r)
    (fun w' => w (roleIdxN w') x) (fun w' k => gd_of_goodV (hw _ x k)) (roleIdxN.symm u) k
  exact goodV_of_gd h (by unfold gateG; omega) (by unfold gateG; omega)

/-! ### One machine operation -/

/-- Growth increment of a machine operation (`c'` for a child, `gateG` for a scalar row). -/
def incOf (c' : ℕ) : MOp → ℕ
  | .child _ _ => c'
  | .gate _ _ _ => gateG
  | _ => 0

/-- One machine operation raises the growth bound of all role streams by at most `incOf c'`. -/
theorem mopVal_growth (t : CCoreRT) (c' : ℕ) (hc' : mn ^ (t.k - 1) ≤ c') (o : MOp) (b : ℕ)
    (W : Fin Wn → RArr (LayerAddr (t.A / Wn) t.K t.D t.S) t.r)
    (hW : ∀ u, ArrGrowth t.P b (W u)) :
    ∀ u, ArrGrowth t.P (b + incOf c' o) (mopVal t o W u) := by
  intro u
  cases o with
  | phase u' κ =>
    simp only [mopVal, incOf, add_zero]
    by_cases hu : u = u'
    · subst hu
      rw [Function.update_self]
      exact runSteps_growth _ (fun s hs => by
        rw [List.mem_singleton] at hs; subst hs; exact stepPres_phaseStep _ _ t κ) _ (hW u)
    · rw [Function.update_of_ne hu]; exact hW u
  | rowAdd u' p₁ p₂ =>
    simp only [mopVal, incOf, add_zero]
    by_cases hu : u = u'
    · subst hu
      rw [Function.update_self]
      exact runSteps_growth _ (fun s hs => stepPres_of_isPull s (rowAddSteps_pull t p₁ p₂ s hs))
        _ (hW u)
    · rw [Function.update_of_ne hu]; exact hW u
  | child u' a =>
    simp only [mopVal, incOf]
    by_cases hu : u = u'
    · subst hu
      rw [Function.update_self]
      exact arrGrowth_mono (by omega) (childVal_growth t a (W u) (hW u))
    · rw [Function.update_of_ne hu]; exact arrGrowth_mono (Nat.le_add_right _ _) (hW u)
  | gate j ι r =>
    simp only [mopVal, incOf]
    exact gateVal_growth j ι r W hW u

end M2Aux

end SubNLogN.Machine.CCore
