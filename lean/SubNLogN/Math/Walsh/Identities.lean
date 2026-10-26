import SubNLogN.Math.Walsh.Cube

/-!
# Walsh: unconditional operator identities (Lemmas 5.1, 5.4, 5.7)

Paper: Lemma 5.1 (`lem:walsh-select`), Lemma 5.4 (`lem:cnot`)
in Section 5.2, Lemma 5.7 (`lem:walsh-involutions`).

All identities are stated over `ℂ`; restricted to Gaussian-dyadic inputs they are the paper's
identities over `ℤ[i, 1/2]` (every operator involved maps Gaussian dyadics to Gaussian dyadics).

Involution decomposition (Lemma 5.7): for a positional map `π`, on each cycle
`(i_0, …, i_{n-1})` (`π i_j = i_{j+1}`, base point `i_0` = the minimum of the cycle) put
`I_0(i_j) = i_{-j}`, `I_1(i_j) = i_{1-j}` (`invol0`, `invol1`). An involution `I` is the set of
disjoint swaps `swapPairs I`; a swap of `b₁ < b₂` is the three controlled flips
`x_{b₁} ← x_{b₁} ⊕ x_{b₂}`, `x_{b₂} ← x_{b₂} ⊕ x_{b₁}`, `x_{b₁} ← x_{b₁} ⊕ x_{b₂}`
(stages `stageA`, `stageB`, `stageA`).

Proof method. `H_T` and `S_U` are tensor-product kernel operators `kerOp` (kernel `H_0`, resp. `S`,
on the chosen positions and the identity elsewhere: `hT_eq_kerOp`, `sDiag_eq_kerOp`); composing
kernel operators multiplies the kernels positionwise (`kerOp_comp`), which reduces the third
identity of Lemma 5.1 to `H0_cube` and `H0S_cube`. Lemma 5.4 is a direct character-sum
computation: on the support of `H_T` the `CZ` sign factors over the target positions
(`czSign_eq_prod_aux`), and each target position contributes `2 H_0 diag(1, ±1) H_0 ∈ {I, X}`
(`H0_flip_entry`). For Lemma 5.7 the cycle data are identified through `Function.minimalPeriod`
(`cycleLen_eq`, `cycleIdx_iterate`, `cycleBase_iterate`).
-/

namespace SubNLogN.Math.Walsh

open SubNLogN.Math.Common

/-! ## Lemma 5.1: three-layer selection -/

/-- The normalized butterfly `H_0 = (1/2)[[1, 1], [1, -1]]`. -/
noncomputable def H0 : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, -1 / 2]

/-- `S = diag(1, i)`. -/
noncomputable def Smat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.I]

/-- The scalar `2^s [2(1-i)]^{q_sel}` of Lemma 5.1. -/
noncomputable def selScalar (s qsel : ℕ) : ℂ := 2 ^ s * (2 * (1 - Complex.I)) ^ qsel

/-- **Lemma 5.1, first identity** (`lem:walsh-select`, eq. (`eq:walsh-three-layer`)): `H_0^3 = (1/2) H_0`. CONTRACT. -/
theorem H0_cube :
    H0 ^ 3 = (1 / 2 : ℂ) • H0 := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H0, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- **Lemma 5.1, second identity** (`lem:walsh-select`, eq. (`eq:walsh-three-layer`)): `(H_0 S)^3 = ((1+i)/4) I`. CONTRACT. -/
theorem H0S_cube :
    (H0 * Smat) ^ 3 = ((1 + Complex.I) / 4) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H0, Smat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-! ## Kernel (tensor-product) operators on the cube -/

/-- The index in `Fin 2` of a bit (`false ↦ 0`, `true ↦ 1`). -/
def bIdx (b : Bool) : Fin 2 := if b then 1 else 0

theorem sum_bIdx {M : Type*} [AddCommMonoid M] (f : Fin 2 → M) :
    ∑ b : Bool, f (bIdx b) = ∑ c : Fin 2, f c := by
  simp [bIdx, Fin.sum_univ_two, add_comm]

/-- The tensor-product operator with the `2 × 2` kernel `K j` on position `j`, identically on
every coefficient: `(kerOp K z)(x) = ∑_y (∏_j K_j(x_j, y_j)) z(y)`. -/
noncomputable def kerOp {m r : ℕ} (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ) (z : RArr (Cube m) r) :
    RArr (Cube m) r :=
  fun x k => ∑ y : Cube m, (∏ j, K j (bIdx (x j)) (bIdx (y j))) * z y k

/-- Composition of kernel operators multiplies the kernels positionwise. -/
theorem kerOp_comp {m r : ℕ} (K L : Fin m → Matrix (Fin 2) (Fin 2) ℂ) (z : RArr (Cube m) r) :
    kerOp K (kerOp L z) = kerOp (fun j => K j * L j) z := by
  funext x k
  simp only [kerOp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  have hent : ∀ j, (K j * L j) (bIdx (x j)) (bIdx (w j)) =
      ∑ b : Bool, K j (bIdx (x j)) (bIdx b) * L j (bIdx b) (bIdx (w j)) := by
    intro j
    rw [Matrix.mul_apply]
    exact (sum_bIdx (fun c => K j (bIdx (x j)) c * L j c (bIdx (w j)))).symm
  simp only [hent, Fintype.prod_sum, ← Finset.prod_mul_distrib]

/-- Scalar kernels factor out. -/
theorem kerOp_smul {m r : ℕ} (c : Fin m → ℂ) (K : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (z : RArr (Cube m) r) :
    kerOp (fun j => c j • K j) z = scaleArr (∏ j, c j) (kerOp K z) := by
  funext x k
  simp only [kerOp, scaleArr, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.mul_sum, mul_assoc]

/-- The kernels of `H_T`: `H_0` on `T`, the identity elsewhere. -/
noncomputable def hKer {m : ℕ} (T : Finset (Fin m)) (j : Fin m) : Matrix (Fin 2) (Fin 2) ℂ :=
  if j ∈ T then H0 else 1

/-- The kernels of `S_U`: `S` on `U`, the identity elsewhere. -/
noncomputable def sKer {m : ℕ} (U : Finset (Fin m)) (j : Fin m) : Matrix (Fin 2) (Fin 2) ℂ :=
  if j ∈ U then Smat else 1

theorem H0_bIdx (a b : Bool) :
    H0 (bIdx a) (bIdx b) = (1 / 2 : ℂ) * (if a = true ∧ b = true then -1 else 1) := by
  cases a <;> cases b <;> norm_num [H0, bIdx]

theorem one_bIdx (a b : Bool) :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) (bIdx a) (bIdx b) = if b = a then 1 else 0 := by
  cases a <;> cases b <;> simp [bIdx]

theorem Smat_bIdx (a b : Bool) :
    Smat (bIdx a) (bIdx b) = if b = a then (if a = true then Complex.I else 1) else 0 := by
  cases a <;> cases b <;> simp [Smat, bIdx]

theorem prod_ite_one_pow {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] (a : ℂ) :
    ∏ j ∈ s, (if p j then a else 1) = a ^ (s.filter p).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem hKer_prod {m : ℕ} (T : Finset (Fin m)) (x y : Cube m) :
    ∏ j, hKer T j (bIdx (x j)) (bIdx (y j)) =
      if (∀ j, j ∉ T → y j = x j) then
        ((2 : ℂ) ^ T.card)⁻¹ * (-1 : ℂ) ^ (T.filter (fun j => x j = true ∧ y j = true)).card
      else 0 := by
  split_ifs with hP
  · have hj : ∀ j, hKer T j (bIdx (x j)) (bIdx (y j)) =
        if j ∈ T then (1 / 2 : ℂ) * (if x j = true ∧ y j = true then -1 else 1) else 1 := by
      intro j
      unfold hKer
      by_cases hjT : j ∈ T
      · rw [if_pos hjT, if_pos hjT, H0_bIdx]
      · rw [if_neg hjT, if_neg hjT, one_bIdx, if_pos (hP j hjT)]
    rw [Finset.prod_congr rfl (fun j _ => hj j), Fintype.prod_ite_mem, Finset.prod_mul_distrib,
      Finset.prod_const, prod_ite_one_pow, one_div_pow, one_div]
  · obtain ⟨j, hj⟩ := not_forall.1 hP
    obtain ⟨hjT, hne⟩ := Classical.not_imp.1 hj
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    unfold hKer
    rw [if_neg hjT, one_bIdx, if_neg hne]

/-- `H_T` is the kernel operator with kernels `hKer T`. -/
theorem hT_eq_kerOp {m r : ℕ} (T : Finset (Fin m)) (z : RArr (Cube m) r) :
    hT T z = kerOp (hKer T) z := by
  funext x k
  simp only [hT, kerOp, hKer_prod]
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

theorem sKer_prod {m : ℕ} (U : Finset (Fin m)) (x y : Cube m) :
    ∏ j, sKer U j (bIdx (x j)) (bIdx (y j)) = if y = x then sPhase U x else 0 := by
  split_ifs with hxy
  · subst hxy
    have hj : ∀ j, sKer U j (bIdx (y j)) (bIdx (y j)) =
        if j ∈ U ∧ y j = true then Complex.I else 1 := by
      intro j
      unfold sKer
      by_cases hjU : j ∈ U
      · rw [if_pos hjU, Smat_bIdx, if_pos rfl]
        cases y j <;> simp [hjU]
      · rw [if_neg hjU, one_bIdx, if_pos rfl]
        simp [hjU]
    rw [Finset.prod_congr rfl (fun j _ => hj j), prod_ite_one_pow]
    unfold sPhase
    congr 2
    ext j
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 hxy
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    unfold sKer
    split_ifs
    · rw [Smat_bIdx, if_neg hj]
    · rw [one_bIdx, if_neg hj]

/-- `S_U` is the kernel operator with kernels `sKer U`. -/
theorem sDiag_eq_kerOp {m r : ℕ} (U : Finset (Fin m)) (z : RArr (Cube m) r) :
    sDiag U z = kerOp (sKer U) z := by
  funext x k
  simp only [sDiag, diagArr, kerOp, sKer_prod]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- **Lemma 5.1, third identity** (`lem:walsh-select`, eq. (`eq:walsh-three-layer`)): for a set `Sel` of selected positions
and `T ⊆ Sel`, with `s = |T|`, `U = Sel \ T`, `q_sel = |U|`, `H_all = H_{Sel}`:
`H_T = 2^s [2(1-i)]^{q_sel} (H_all S_U)^3` (chronologically: `S_U, H_all, S_U, H_all, S_U, H_all`,
then the scalar). CONTRACT. -/
theorem hT_eq_selScalar_three_layer {m r : ℕ} (Sel T : Finset (Fin m)) (hTS : T ⊆ Sel) (z : RArr (Cube m) r) :
    hT T z = scaleArr (selScalar T.card (Sel \ T).card)
      (hT Sel (sDiag (Sel \ T) (hT Sel (sDiag (Sel \ T) (hT Sel (sDiag (Sel \ T) z)))))) := by
  let c : Fin m → ℂ := fun j =>
    if j ∈ T then 1 / 2 else if j ∈ Sel \ T then (1 + Complex.I) / 4 else 1
  have hthree : hT Sel (sDiag (Sel \ T) (hT Sel (sDiag (Sel \ T) (hT Sel (sDiag (Sel \ T) z))))) =
      kerOp (fun j => c j • hKer T j) z := by
    simp only [hT_eq_kerOp, sDiag_eq_kerOp, kerOp_comp]
    congr 1
    funext j
    by_cases hjT : j ∈ T
    · have hjS : j ∈ Sel := hTS hjT
      have hjU : j ∉ Sel \ T := fun h => (Finset.mem_sdiff.1 h).2 hjT
      simp only [c, hKer, sKer, if_pos hjT, if_pos hjS, if_neg hjU, mul_one, one_mul]
      rw [← H0_cube, pow_three]
    · by_cases hjS : j ∈ Sel
      · have hjU : j ∈ Sel \ T := Finset.mem_sdiff.2 ⟨hjS, hjT⟩
        simp only [c, hKer, sKer, if_neg hjT, if_pos hjS, if_pos hjU]
        rw [← H0S_cube, pow_three]
        simp only [mul_assoc]
      · have hjU : j ∉ Sel \ T := fun h => hjS (Finset.mem_sdiff.1 h).1
        simp only [c, hKer, sKer, if_neg hjT, if_neg hjS, if_neg hjU, one_mul, one_smul]
  have hprod : ∏ j, c j = (1 / 2 : ℂ) ^ T.card * ((1 + Complex.I) / 4) ^ (Sel \ T).card := by
    have hc : ∀ j, c j = (if j ∈ T then (1 / 2 : ℂ) else 1) *
        (if j ∈ Sel \ T then (1 + Complex.I) / 4 else 1) := by
      intro j
      by_cases hjT : j ∈ T
      · have hjU : j ∉ Sel \ T := fun h => (Finset.mem_sdiff.1 h).2 hjT
        simp [c, hjT, hjU]
      · simp [c, hjT]
    rw [Finset.prod_congr rfl (fun j _ => hc j), Finset.prod_mul_distrib, Fintype.prod_ite_mem,
      Fintype.prod_ite_mem, Finset.prod_const, Finset.prod_const]
  have hscal : selScalar T.card (Sel \ T).card * ∏ j, c j = 1 := by
    rw [hprod, selScalar]
    have h1 : (2 : ℂ) * (1 - Complex.I) * ((1 + Complex.I) / 4) = 1 := by
      linear_combination (-(1 : ℂ) / 2) * Complex.I_sq
    rw [mul_mul_mul_comm, ← mul_pow, ← mul_pow, h1]
    norm_num
  rw [hthree, kerOp_smul, ← hT_eq_kerOp]
  funext x k
  simp only [scaleArr, ← mul_assoc, hscal, one_mul]

/-- **Lemma 5.1, scalar form** (`lem:walsh-select`): if `q_sel = 2f + e` with `e ∈ {0, 1}`, then
`2^s [2(1-i)]^{q_sel} = 2^{s+3f+e} (-i)^f (1-i)^e`. CONTRACT. -/
theorem selScalar_eq (s f e : ℕ) (he : e ≤ 1) :
    selScalar s (2 * f + e) = 2 ^ (s + 3 * f + e) * (-Complex.I) ^ f * (1 - Complex.I) ^ e := by
  -- the identity holds for every `e`: the hypothesis `he : e ≤ 1` is not used
  unfold selScalar
  have h : (2 * (1 - Complex.I)) ^ 2 = (2 : ℂ) ^ 3 * (-Complex.I) := by
    linear_combination (4 : ℂ) * Complex.I_sq
  rw [pow_add, pow_mul, h, mul_pow, mul_pow, ← pow_mul, pow_add, pow_add]
  ring

/-! ## Lemma 5.4: controlled flips -/

/-- **Lemma 5.4, address map** (`lem:cnot`): for valid pairs the address map of
`CNOT^{⊗s}` is an involution, so the move and pull conventions agree. CONTRACT. -/
theorem cnotAddr_involutive {m : ℕ} (pairs : List (Fin m × Fin m)) (hv : CnotPairsValid pairs) :
    Function.Involutive (cnotAddr pairs) := by
  have hdis : ∀ q ∈ pairs, ∀ q' ∈ pairs, q'.2 ≠ q.1 := by
    intro q hq q' hq' h
    exact (List.nodup_append.1 hv).2.2 q.1 (List.mem_map_of_mem hq) q'.2
      (List.mem_map_of_mem hq') h.symm
  have hfix : ∀ x : Cube m, ∀ q ∈ pairs, cnotAddr pairs x q.1 = x q.1 := by
    intro x q hq
    have : pairs.any (fun q' => decide (q'.2 = q.1) && x q'.1) = false := by
      rw [List.any_eq_false]
      intro q' hq'
      simp [hdis q hq q' hq']
    simp only [cnotAddr, this, Bool.xor_false]
  intro x
  funext p
  have hany : pairs.any (fun q => decide (q.2 = p) && cnotAddr pairs x q.1) =
      pairs.any (fun q => decide (q.2 = p) && x q.1) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨q, hq, h⟩
      exact ⟨q, hq, by rwa [hfix x q hq] at h⟩
    · rintro ⟨q, hq, h⟩
      exact ⟨q, hq, by rwa [hfix x q hq]⟩
  show xor (cnotAddr pairs x p) (pairs.any (fun q => decide (q.2 = p) && cnotAddr pairs x q.1)) = x p
  rw [hany]
  simp only [cnotAddr, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The control bit that flips position `j` in `cnotAddr pairs y`. -/
def ctlBit {m : ℕ} (pairs : List (Fin m × Fin m)) (y : Cube m) (j : Fin m) : Bool :=
  pairs.any (fun q => decide (q.2 = j) && y q.1)

theorem ctlBit_cons {m : ℕ} (q : Fin m × Fin m) (ps : List (Fin m × Fin m)) (y : Cube m)
    (j : Fin m) : ctlBit (q :: ps) y j = ((decide (q.2 = j) && y q.1) || ctlBit ps y j) := rfl

/-- For distinct targets and `w` agreeing with `y` on the controls, the `CZ` sign of `w` is a
product of single-position signs. -/
theorem czSign_eq_prod_aux {m : ℕ} (ps : List (Fin m × Fin m)) (hnd : (ps.map Prod.snd).Nodup)
    (w y : Cube m) (hwy : ∀ q ∈ ps, w q.1 = y q.1) :
    (-1 : ℂ) ^ (ps.countP (fun p => w p.1 && w p.2)) =
      ∏ j, (if w j = true ∧ ctlBit ps y j = true then -1 else 1) := by
  induction ps with
  | nil => simp [ctlBit]
  | cons q ps ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih' := ih hnd.2 (fun q' hq' => hwy q' (List.mem_cons_of_mem _ hq'))
    have hq : w q.1 = y q.1 := hwy q (by simp)
    have hnot : ctlBit ps y q.2 = false := by
      unfold ctlBit
      rw [List.any_eq_false]
      intro q' hq' h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact hnd.1 (List.mem_map.2 ⟨q', hq', h.1⟩)
    rw [List.countP_cons, pow_add, ih']
    have hfac : ∀ j, (if w j = true ∧ ctlBit (q :: ps) y j = true then (-1 : ℂ) else 1) =
        (if w j = true ∧ ctlBit ps y j = true then -1 else 1) *
          (if j = q.2 then (if w q.2 = true ∧ y q.1 = true then -1 else 1) else 1) := by
      intro j
      by_cases hj : j = q.2
      · subst hj
        rw [ctlBit_cons, hnot]
        simp
      · have hj' : ¬ q.2 = j := fun h => hj h.symm
        rw [ctlBit_cons]
        simp [hj, hj']
    rw [Finset.prod_congr rfl (fun j _ => hfac j), Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    congr 1
    rw [hq]
    cases y q.1 <;> cases w q.2 <;> simp

theorem H0_flip_entry (a c t : Bool) :
    ∑ b : Bool, H0 (bIdx a) (bIdx b) * (if b = true ∧ t = true then (-1 : ℂ) else 1) *
      H0 (bIdx b) (bIdx c) = (1 / 2 : ℂ) * (if c = xor a t then 1 else 0) := by
  cases a <;> cases c <;> cases t <;> norm_num [H0_bIdx]

theorem one_flip_entry (a c t : Bool) (ht : t = false) :
    ∑ b : Bool, (1 : Matrix (Fin 2) (Fin 2) ℂ) (bIdx a) (bIdx b) *
      (if b = true ∧ t = true then (-1 : ℂ) else 1) * (1 : Matrix (Fin 2) (Fin 2) ℂ) (bIdx b) (bIdx c) =
        1 * (if c = xor a t then 1 else 0) := by
  subst ht
  cases a <;> cases c <;> simp [one_bIdx]

/-- **Lemma 5.4** (`lem:cnot`): for disjoint pairs `(c_j, t_j)`, all `2s` positions
distinct, with target set `T`, as array operators `CNOT^{⊗s} = 2^s H_T CZ H_T`. CONTRACT. -/
theorem cnotArr_eq_hT_cz_hT {m r : ℕ} (pairs : List (Fin m × Fin m)) (hv : CnotPairsValid pairs) (z : RArr (Cube m) r) :
    cnotArr pairs z =
      scaleArr (2 ^ pairs.length) (hT (targets pairs) (diagArr (czSign pairs) (hT (targets pairs) z))) := by
  have hnd2 : (pairs.map Prod.snd).Nodup := (List.nodup_append.1 hv).2.1
  have hcard : (targets pairs).card = pairs.length := by
    rw [targets, List.toFinset_card_of_nodup hnd2, List.length_map]
  have hctlT : ∀ (y : Cube m) j, ctlBit pairs y j = true → j ∈ targets pairs := by
    intro y j h
    unfold ctlBit at h
    rw [List.any_eq_true] at h
    obtain ⟨q, hq, hq'⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
    unfold targets
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨q, hq, hq'.1⟩
  have hctrl : ∀ q ∈ pairs, q.1 ∉ targets pairs := by
    intro q hq h
    unfold targets at h
    rw [List.mem_toFinset, List.mem_map] at h
    obtain ⟨q', hq', h'⟩ := h
    exact (List.nodup_append.1 hv).2.2 q.1 (List.mem_map_of_mem hq) q'.2
      (List.mem_map_of_mem hq') h'.symm
  funext y k
  simp only [cnotArr, scaleArr, diagArr, hT_eq_kerOp, kerOp]
  have hcz : ∀ w : Cube m, (∏ j, hKer (targets pairs) j (bIdx (y j)) (bIdx (w j))) * czSign pairs w =
      (∏ j, hKer (targets pairs) j (bIdx (y j)) (bIdx (w j))) *
        ∏ j, (if w j = true ∧ ctlBit pairs y j = true then (-1 : ℂ) else 1) := by
    intro w
    by_cases hP : ∀ j, j ∉ targets pairs → w j = y j
    · congr 1
      exact czSign_eq_prod_aux pairs hnd2 w y (fun q hq => hP q.1 (hctrl q hq))
    · rw [hKer_prod, if_neg hP, zero_mul, zero_mul]
  have hstep : ∑ w : Cube m, (∏ j, hKer (targets pairs) j (bIdx (y j)) (bIdx (w j))) *
        (czSign pairs w * ∑ v : Cube m,
          (∏ j, hKer (targets pairs) j (bIdx (w j)) (bIdx (v j))) * z v k) =
      ∑ v : Cube m, (∏ j, ∑ b : Bool, hKer (targets pairs) j (bIdx (y j)) (bIdx b) *
          (if b = true ∧ ctlBit pairs y j = true then (-1 : ℂ) else 1) *
            hKer (targets pairs) j (bIdx b) (bIdx (v j))) * z v k := by
    simp only [Fintype.prod_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
    calc (∏ j, hKer (targets pairs) j (bIdx (y j)) (bIdx (w j))) *
          (czSign pairs w * ((∏ j, hKer (targets pairs) j (bIdx (w j)) (bIdx (v j))) * z v k))
        = ((∏ j, hKer (targets pairs) j (bIdx (y j)) (bIdx (w j))) * czSign pairs w) *
            (∏ j, hKer (targets pairs) j (bIdx (w j)) (bIdx (v j))) * z v k := by ring
      _ = ((∏ j, hKer (targets pairs) j (bIdx (y j)) (bIdx (w j))) *
            ∏ j, (if w j = true ∧ ctlBit pairs y j = true then (-1 : ℂ) else 1)) *
            (∏ j, hKer (targets pairs) j (bIdx (w j)) (bIdx (v j))) * z v k := by rw [hcz w]
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hent : ∀ (v : Cube m) j, (∑ b : Bool, hKer (targets pairs) j (bIdx (y j)) (bIdx b) *
          (if b = true ∧ ctlBit pairs y j = true then (-1 : ℂ) else 1) *
            hKer (targets pairs) j (bIdx b) (bIdx (v j))) =
        (if j ∈ targets pairs then (1 / 2 : ℂ) else 1) *
          (if v j = cnotAddr pairs y j then 1 else 0) := by
    intro v j
    have hcA : cnotAddr pairs y j = xor (y j) (ctlBit pairs y j) := rfl
    rw [hcA]
    by_cases hj : j ∈ targets pairs
    · simp only [hKer, if_pos hj]
      exact H0_flip_entry (y j) (v j) (ctlBit pairs y j)
    · have hc : ctlBit pairs y j = false := by
        cases h : ctlBit pairs y j
        · rfl
        · exact absurd (hctlT y j h) hj
      simp only [hKer, if_neg hj]
      exact one_flip_entry (y j) (v j) (ctlBit pairs y j) hc
  have hprodv : ∀ v : Cube m, ∏ j, ((if j ∈ targets pairs then (1 / 2 : ℂ) else 1) *
        (if v j = cnotAddr pairs y j then 1 else 0)) =
      (1 / 2 : ℂ) ^ (targets pairs).card * (if v = cnotAddr pairs y then 1 else 0) := by
    intro v
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem, Finset.prod_const, Fintype.prod_boole]
    congr 1
    by_cases h : v = cnotAddr pairs y
    · rw [if_pos h, if_pos (fun j => by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (funext h'))]
  rw [hstep]
  simp only [hent, hprodv]
  rw [Finset.mul_sum, Finset.sum_eq_single (cnotAddr pairs y)]
  · rw [if_pos rfl, hcard, mul_one, ← mul_assoc, ← mul_pow]
    norm_num
  · intro v _ hv
    rw [if_neg hv]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## Lemma 5.7: two involutions -/

/-- Base point of the cycle of `x` under `π`: the minimum of `x, π x, …, π^{m-1} x`. -/
def cycleBase {m : ℕ} (π : Fin m → Fin m) (x : Fin m) : Fin m :=
  ((List.range m).map (fun k => π^[k] x)).foldl min x

/-- The index `j` of `x` on its cycle: the least `k < m` with `π^k (base) = x` (`0` if none). -/
def cycleIdx {m : ℕ} (π : Fin m → Fin m) (x : Fin m) : ℕ :=
  ((List.range m).find? (fun k => π^[k] (cycleBase π x) = x)).getD 0

/-- The length `n_c` of the cycle of `x`: the least `k ≥ 1` with `π^k (base) = base`. -/
def cycleLen {m : ℕ} (π : Fin m → Fin m) (x : Fin m) : ℕ :=
  ((List.range m).find? (fun k => π^[k + 1] (cycleBase π x) = cycleBase π x)).getD 0 + 1

/-- `I_0(i_j) = i_{-j}` (Lemma 5.7 (`lem:walsh-involutions`)). -/
def invol0 {m : ℕ} (π : Fin m → Fin m) (x : Fin m) : Fin m :=
  π^[(cycleLen π x - cycleIdx π x) % cycleLen π x] (cycleBase π x)

/-- `I_1(i_j) = i_{1-j}` (Lemma 5.7 (`lem:walsh-involutions`)). -/
def invol1 {m : ℕ} (π : Fin m → Fin m) (x : Fin m) : Fin m :=
  π^[(cycleLen π x + 1 - cycleIdx π x) % cycleLen π x] (cycleBase π x)

/-- The disjoint swaps `(b₁, b₂)`, `b₁ < b₂ = I b₁`, of an involution `I`. -/
def swapPairs {m : ℕ} (I : Fin m → Fin m) : List (Fin m × Fin m) :=
  (List.finRange m).filterMap (fun x => if x < I x then some (x, I x) else none)

/-- Stages 1 and 3 of the swaps of `I`: pairs (control `b₂`, target `b₁`), i.e.
`x_{b₁} ← x_{b₁} ⊕ x_{b₂}`. -/
def stageA {m : ℕ} (I : Fin m → Fin m) : List (Fin m × Fin m) :=
  (swapPairs I).map (fun p => (p.2, p.1))

/-- Stage 2 of the swaps of `I`: pairs (control `b₁`, target `b₂`), i.e.
`x_{b₂} ← x_{b₂} ⊕ x_{b₁}`. -/
def stageB {m : ℕ} (I : Fin m → Fin m) : List (Fin m × Fin m) :=
  swapPairs I

/-! ## Involutions: helper lemmas -/

theorem foldl_min_spec {α : Type*} [LinearOrder α] (l : List α) (x : α) :
    l.foldl min x ≤ x ∧ (∀ y ∈ l, l.foldl min x ≤ y) ∧
      (l.foldl min x = x ∨ l.foldl min x ∈ l) := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2, h3⟩ := ih (min x a)
    simp only [List.foldl_cons]
    refine ⟨h1.trans (min_le_left _ _), ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h1.trans (min_le_right _ _)
      · exact h2 y hy
    · rcases h3 with h3 | h3
      · rcases min_choice x a with h | h
        · left; rw [h3, h]
        · right; rw [h3, h]; simp
      · right; exact List.mem_cons_of_mem _ h3

section Cycles

variable {m : ℕ} (π : Equiv.Perm (Fin m))

theorem perm_mem_periodicPts (x : Fin m) : x ∈ Function.periodicPts π :=
  π.injective.mem_periodicPts x

theorem perm_minimalPeriod_pos (x : Fin m) : 0 < Function.minimalPeriod π x :=
  Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts π x)

theorem perm_minimalPeriod_le (x : Fin m) : Function.minimalPeriod π x ≤ m := by
  simpa using Function.minimalPeriod_le_card (f := π) (x := x)

theorem perm_minimalPeriod_iterate (x : Fin m) (k : ℕ) :
    Function.minimalPeriod π (π^[k] x) = Function.minimalPeriod π x :=
  Function.minimalPeriod_apply_iterate (perm_mem_periodicPts π x) k

theorem perm_iterate_mod (x : Fin m) (k : ℕ) :
    π^[k % Function.minimalPeriod π x] x = π^[k] x :=
  Function.iterate_mod_minimalPeriod_eq

theorem perm_iterate_eq_of_modEq (x : Fin m) {a b : ℕ}
    (h : a ≡ b [MOD Function.minimalPeriod π x]) : π^[a] x = π^[b] x := by
  rw [← perm_iterate_mod π x a, ← perm_iterate_mod π x b]
  exact congrArg (fun t => π^[t] x) h

/-- `(n + c - j % n) + j ≡ c [MOD n]`. -/
theorem add_sub_mod_add_modEq {n : ℕ} (hn : 0 < n) (c j : ℕ) :
    n + c - j % n + j ≡ c [MOD n] := by
  have hlt : j % n < n := Nat.mod_lt j hn
  calc n + c - j % n + j ≡ n + c - j % n + j % n [MOD n] :=
        Nat.ModEq.add_left _ (Nat.mod_modEq j n).symm
    _ = c + n := by omega
    _ ≡ c [MOD n] := by simp [Nat.ModEq]

theorem perm_exists_iterate_back (x : Fin m) (k : ℕ) : ∃ c, π^[c] (π^[k] x) = x := by
  have hn := perm_minimalPeriod_pos π x
  refine ⟨Function.minimalPeriod π x + 0 - k % Function.minimalPeriod π x, ?_⟩
  rw [← Function.iterate_add_apply]
  exact (perm_iterate_eq_of_modEq π x (add_sub_mod_add_modEq hn 0 k)).trans rfl

theorem cycleBase_spec (x : Fin m) :
    (∃ a, cycleBase π x = π^[a] x) ∧ ∀ k, cycleBase π x ≤ π^[k] x := by
  obtain ⟨-, h2, h3⟩ := foldl_min_spec ((List.range m).map (fun k => π^[k] x)) x
  refine ⟨?_, fun k => ?_⟩
  · rcases h3 with h3 | h3
    · exact ⟨0, h3⟩
    · obtain ⟨a, -, ha⟩ := List.mem_map.1 h3
      exact ⟨a, ha.symm⟩
  · rw [← perm_iterate_mod π x k]
    apply h2
    apply List.mem_map.2
    refine ⟨k % Function.minimalPeriod π x, ?_, rfl⟩
    exact List.mem_range.2
      ((Nat.mod_lt _ (perm_minimalPeriod_pos π x)).trans_le (perm_minimalPeriod_le π x))

theorem cycleBase_iterate (x : Fin m) (k : ℕ) : cycleBase π (π^[k] x) = cycleBase π x := by
  obtain ⟨a, ha⟩ := (cycleBase_spec π (π^[k] x)).1
  obtain ⟨a', ha'⟩ := (cycleBase_spec π x).1
  obtain ⟨c, hc⟩ := perm_exists_iterate_back π x k
  apply le_antisymm
  · calc cycleBase π (π^[k] x) ≤ π^[a' + c] (π^[k] x) := (cycleBase_spec π (π^[k] x)).2 _
      _ = π^[a'] (π^[c] (π^[k] x)) := Function.iterate_add_apply _ _ _ _
      _ = π^[a'] x := by rw [hc]
      _ = cycleBase π x := ha'.symm
  · calc cycleBase π x ≤ π^[a + k] x := (cycleBase_spec π x).2 _
      _ = π^[a] (π^[k] x) := Function.iterate_add_apply _ _ _ _
      _ = cycleBase π (π^[k] x) := ha.symm

theorem cycleBase_cycleBase (x : Fin m) : cycleBase π (cycleBase π x) = cycleBase π x := by
  obtain ⟨a, ha⟩ := (cycleBase_spec π x).1
  conv_lhs => rw [ha]
  exact cycleBase_iterate π x a

theorem exists_iterate_cycleBase (x : Fin m) : ∃ j, π^[j] (cycleBase π x) = x := by
  obtain ⟨a, ha⟩ := (cycleBase_spec π x).1
  obtain ⟨c, hc⟩ := perm_exists_iterate_back π x a
  exact ⟨c, by rw [ha, hc]⟩

theorem minimalPeriod_cycleBase (x : Fin m) :
    Function.minimalPeriod π (cycleBase π x) = Function.minimalPeriod π x := by
  obtain ⟨a, ha⟩ := (cycleBase_spec π x).1
  rw [ha, perm_minimalPeriod_iterate]

theorem cycleLen_eq (x : Fin m) : cycleLen π x = Function.minimalPeriod π x := by
  have hbn := minimalPeriod_cycleBase π x
  have hn := perm_minimalPeriod_pos π x
  have hle := perm_minimalPeriod_le π x
  have hfind : (List.range m).find?
      (fun k => decide (π^[k + 1] (cycleBase π x) = cycleBase π x)) =
        some (Function.minimalPeriod π x - 1) := by
    rw [List.find?_range_eq_some]
    refine ⟨?_, List.mem_range.2 (by omega), ?_⟩
    · simp only [decide_eq_true_eq]
      rw [Nat.sub_add_cancel hn, ← hbn]
      exact Function.iterate_minimalPeriod
    · intro j hj
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      intro h
      have := Function.IsPeriodicPt.minimalPeriod_le (Nat.succ_pos j) h
      omega
  unfold cycleLen
  rw [hfind]
  simp only [Option.getD_some]
  omega

theorem cycleIdx_iterate (x : Fin m) (k : ℕ) :
    cycleIdx π (π^[k] (cycleBase π x)) = k % Function.minimalPeriod π x := by
  have hbn := minimalPeriod_cycleBase π x
  have hn := perm_minimalPeriod_pos π x
  have hle := perm_minimalPeriod_le π x
  have hbase : cycleBase π (π^[k] (cycleBase π x)) = cycleBase π x := by
    rw [cycleBase_iterate, cycleBase_cycleBase]
  have hlt : k % Function.minimalPeriod π x < Function.minimalPeriod π x := Nat.mod_lt _ hn
  have hfind : (List.range m).find?
      (fun i => decide (π^[i] (cycleBase π x) = π^[k] (cycleBase π x))) =
        some (k % Function.minimalPeriod π x) := by
    rw [List.find?_range_eq_some]
    refine ⟨?_, List.mem_range.2 (by omega), ?_⟩
    · simp only [decide_eq_true_eq]
      rw [← hbn]
      exact perm_iterate_mod π _ k
    · intro j hj
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      intro h
      rw [← perm_iterate_mod π (cycleBase π x) k, hbn] at h
      have := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        (by rw [hbn]; omega) (by rw [hbn]; exact hlt)).1 h
      omega
  unfold cycleIdx
  rw [hbase, hfind]
  rfl

theorem cycleLen_iterate (x : Fin m) (k : ℕ) :
    cycleLen π (π^[k] (cycleBase π x)) = Function.minimalPeriod π x := by
  rw [cycleLen_eq, perm_minimalPeriod_iterate, minimalPeriod_cycleBase]

theorem invol0_iterate (x : Fin m) (k t : ℕ)
    (h : t + k ≡ 0 [MOD Function.minimalPeriod π x]) :
    invol0 π (π^[k] (cycleBase π x)) = π^[t] (cycleBase π x) := by
  have hn := perm_minimalPeriod_pos π x
  have hbase : cycleBase π (π^[k] (cycleBase π x)) = cycleBase π x := by
    rw [cycleBase_iterate, cycleBase_cycleBase]
  unfold invol0
  rw [hbase, cycleLen_iterate, cycleIdx_iterate]
  apply perm_iterate_eq_of_modEq
  rw [minimalPeriod_cycleBase]
  have h2 : (Function.minimalPeriod π x - k % Function.minimalPeriod π x) %
      Function.minimalPeriod π x + k ≡ 0 [MOD Function.minimalPeriod π x] := by
    have := add_sub_mod_add_modEq hn 0 k
    simp only [add_zero] at this
    exact (Nat.ModEq.add_right k (Nat.mod_modEq _ _)).trans this
  exact Nat.ModEq.add_right_cancel' k (h2.trans h.symm)

theorem invol1_iterate (x : Fin m) (k t : ℕ)
    (h : t + k ≡ 1 [MOD Function.minimalPeriod π x]) :
    invol1 π (π^[k] (cycleBase π x)) = π^[t] (cycleBase π x) := by
  have hn := perm_minimalPeriod_pos π x
  have hbase : cycleBase π (π^[k] (cycleBase π x)) = cycleBase π x := by
    rw [cycleBase_iterate, cycleBase_cycleBase]
  unfold invol1
  rw [hbase, cycleLen_iterate, cycleIdx_iterate]
  apply perm_iterate_eq_of_modEq
  rw [minimalPeriod_cycleBase]
  have h2 : (Function.minimalPeriod π x + 1 - k % Function.minimalPeriod π x) %
      Function.minimalPeriod π x + k ≡ 1 [MOD Function.minimalPeriod π x] :=
    (Nat.ModEq.add_right k (Nat.mod_modEq _ _)).trans (add_sub_mod_add_modEq hn 1 k)
  exact Nat.ModEq.add_right_cancel' k (h2.trans h.symm)

end Cycles

/-- **Lemma 5.7, decomposition** (`lem:walsh-involutions`): every positional map `π` is `I_1 ∘ I_0`
with `I_0`, `I_1` involutions. CONTRACT. -/
theorem walsh_involutions {m : ℕ} (π : Equiv.Perm (Fin m)) :
    Function.Involutive (invol0 π) ∧ Function.Involutive (invol1 π) ∧
      ∀ x, invol1 π (invol0 π x) = π x := by
  have key : ∀ x : Fin m, ∃ j, x = π^[j] (cycleBase π x) :=
    fun x => (exists_iterate_cycleBase π x).imp fun _ h => h.symm
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · obtain ⟨j, hj⟩ := key x
    have hn := perm_minimalPeriod_pos π x
    have h0 := add_sub_mod_add_modEq hn 0 j
    rw [hj, invol0_iterate π x j _ h0, invol0_iterate π x _ j (by rwa [add_comm])]
  · obtain ⟨j, hj⟩ := key x
    have hn := perm_minimalPeriod_pos π x
    have h1 := add_sub_mod_add_modEq hn 1 j
    rw [hj, invol1_iterate π x j _ h1, invol1_iterate π x _ j (by rwa [add_comm])]
  · obtain ⟨j, hj⟩ := key x
    have hn := perm_minimalPeriod_pos π x
    have h0 := add_sub_mod_add_modEq hn 0 j
    have h1 : j + 1 + (Function.minimalPeriod π x + 0 - j % Function.minimalPeriod π x) ≡ 1
        [MOD Function.minimalPeriod π x] := by
      have := Nat.ModEq.add_right 1 h0
      rw [zero_add] at this
      calc j + 1 + (Function.minimalPeriod π x + 0 - j % Function.minimalPeriod π x)
          = Function.minimalPeriod π x + 0 - j % Function.minimalPeriod π x + j + 1 := by ring
        _ ≡ 1 [MOD Function.minimalPeriod π x] := this
    rw [hj, invol0_iterate π x j _ h0, invol1_iterate π x _ (j + 1) h1,
      Function.iterate_succ_apply']

/-- **Lemma 5.7, composition on arrays**: `posPermArr π = posPermArr I_1 ∘ posPermArr I_0`
(`I_0` is executed first). CONTRACT. -/
theorem posPermArr_eq_invol {m r : ℕ} (π : Equiv.Perm (Fin m)) (z : RArr (Cube m) r) :
    posPermArr π z = posPermArr (invol1 π) (posPermArr (invol0 π) z) := by
  funext y k
  simp only [posPermArr, (walsh_involutions π).2.2]

/-! ## Involutions: three stages of controlled flips -/

theorem mem_swapPairs {m : ℕ} (I : Fin m → Fin m) (q : Fin m × Fin m) :
    q ∈ swapPairs I ↔ q.1 < I q.1 ∧ q.2 = I q.1 := by
  unfold swapPairs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, -, hx⟩
    by_cases h : x < I x
    · rw [if_pos h, Option.some.injEq] at hx
      subst hx
      exact ⟨h, rfl⟩
    · rw [if_neg h] at hx
      cases hx
  · rintro ⟨h1, h2⟩
    refine ⟨q.1, List.mem_finRange _, ?_⟩
    rw [if_pos h1, ← h2]

theorem swapPairs_nodup {m : ℕ} (I : Fin m → Fin m) : (swapPairs I).Nodup := by
  unfold swapPairs
  refine List.Nodup.filterMap ?_ (List.nodup_finRange m)
  intro a a' b ha ha'
  by_cases h : a < I a
  · by_cases h' : a' < I a'
    · rw [if_pos h, Option.mem_def, Option.some.injEq] at ha
      rw [if_pos h', Option.mem_def, Option.some.injEq] at ha'
      have := congrArg Prod.fst (ha.trans ha'.symm)
      exact this
    · rw [if_neg h'] at ha'
      cases ha'
  · rw [if_neg h] at ha
    cases ha

theorem swapPairs_valid {m : ℕ} (I : Fin m → Fin m) (hI : Function.Involutive I) :
    ((swapPairs I).map Prod.fst ++ (swapPairs I).map Prod.snd).Nodup := by
  have hmem := mem_swapPairs I
  rw [List.nodup_append]
  refine ⟨List.Nodup.map_on ?_ (swapPairs_nodup I),
    List.Nodup.map_on ?_ (swapPairs_nodup I), ?_⟩
  · intro q hq q' hq' h
    obtain ⟨-, h2⟩ := (hmem q).1 hq
    obtain ⟨-, h2'⟩ := (hmem q').1 hq'
    exact Prod.ext h (by rw [h2, h2', h])
  · intro q hq q' hq' h
    obtain ⟨-, h2⟩ := (hmem q).1 hq
    obtain ⟨-, h2'⟩ := (hmem q').1 hq'
    exact Prod.ext (hI.injective (by rw [← h2, ← h2', h])) h
  · intro a ha b hb hab
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hb
    obtain ⟨h1, -⟩ := (hmem q).1 hq
    obtain ⟨h1', h2'⟩ := (hmem q').1 hq'
    have hIq : I q.1 = q'.1 := by rw [hab, h2', hI]
    have : q.1 < q.1 :=
      calc q.1 < I q.1 := h1
        _ = q'.1 := hIq
        _ < I q'.1 := h1'
        _ = q'.2 := h2'.symm
        _ = q.1 := hab.symm
    exact lt_irrefl _ this

theorem stageB_valid {m : ℕ} (I : Fin m → Fin m) (hI : Function.Involutive I) :
    CnotPairsValid (stageB I) :=
  swapPairs_valid I hI

theorem stageA_valid {m : ℕ} (I : Fin m → Fin m) (hI : Function.Involutive I) :
    CnotPairsValid (stageA I) := by
  unfold CnotPairsValid stageA
  rw [List.map_map, List.map_map]
  exact List.nodup_append_comm.1 (swapPairs_valid I hI)

theorem cnotAddr_stageA {m : ℕ} (I : Fin m → Fin m) (y : Cube m) (p : Fin m) :
    cnotAddr (stageA I) y p = if p < I p then xor (y p) (y (I p)) else y p := by
  have hany : (stageA I).any (fun q => decide (q.2 = p) && y q.1) =
      (decide (p < I p) && y (I p)) := by
    rw [Bool.eq_iff_iff, List.any_eq_true]
    simp only [stageA, List.mem_map, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, h1, h2⟩
      obtain ⟨hq1, hq2⟩ := (mem_swapPairs I q).1 hq
      simp only at h1 h2
      subst h1
      rw [hq2] at h2
      exact ⟨hq1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(I p, p), ⟨(p, I p), (mem_swapPairs I _).2 ⟨h1, rfl⟩, rfl⟩, rfl, h2⟩
  simp only [cnotAddr, hany]
  by_cases h : p < I p <;> simp [h]

theorem cnotAddr_stageB {m : ℕ} (I : Fin m → Fin m) (hI : Function.Involutive I) (y : Cube m)
    (p : Fin m) :
    cnotAddr (stageB I) y p = if I p < p then xor (y p) (y (I p)) else y p := by
  have hany : (stageB I).any (fun q => decide (q.2 = p) && y q.1) =
      (decide (I p < p) && y (I p)) := by
    rw [Bool.eq_iff_iff, List.any_eq_true]
    simp only [stageB, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨q, hq, h1, h2⟩
      obtain ⟨hq1, hq2⟩ := (mem_swapPairs I q).1 hq
      have hq' : q.1 = I p := by rw [← h1, hq2, hI]
      rw [hq'] at hq1 h2
      rw [hI] at hq1
      exact ⟨hq1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(I p, p), (mem_swapPairs I _).2 ⟨by rwa [hI], (hI p).symm⟩, rfl, h2⟩
  simp only [cnotAddr, hany]
  by_cases h : I p < p <;> simp [h]

/-- **Lemma 5.7, three stages** (`lem:walsh-involutions`): an involution is a set of
disjoint positional swaps, implemented by three stages of disjoint controlled flips: each stage is
a valid batch and `posPermArr I = CNOT_{stageA} ∘ CNOT_{stageB} ∘ CNOT_{stageA}` (stage 1
first). CONTRACT. -/
theorem involution_three_stages {m r : ℕ} (I : Fin m → Fin m) (hI : Function.Involutive I) :
    CnotPairsValid (stageA I) ∧ CnotPairsValid (stageB I) ∧
      ∀ z : RArr (Cube m) r,
        posPermArr I z = cnotArr (stageA I) (cnotArr (stageB I) (cnotArr (stageA I) z)) := by
  refine ⟨stageA_valid I hI, stageB_valid I hI, fun z => ?_⟩
  have haddr : ∀ y : Cube m,
      cnotAddr (stageA I) (cnotAddr (stageB I) (cnotAddr (stageA I) y)) = fun j => y (I j) := by
    intro y
    funext p
    simp only [cnotAddr_stageA I, cnotAddr_stageB I hI, hI p]
    rcases lt_trichotomy p (I p) with h | h | h
    · have h' : ¬ I p < p := not_lt.2 h.le
      simp only [h, h', if_true, if_false]
      cases y p <;> cases y (I p) <;> rfl
    · have h1 : ¬ p < I p := by rw [← h]; exact lt_irrefl _
      have h2 : ¬ I p < p := by rw [← h]; exact lt_irrefl _
      simp only [h1, h2, if_false]
      rw [← h]
    · have h' : ¬ p < I p := not_lt.2 h.le
      simp only [h, h', if_true, if_false]
      cases y p <;> cases y (I p) <;> rfl
  funext y k
  simp only [posPermArr, cnotArr, haddr]

end SubNLogN.Math.Walsh
