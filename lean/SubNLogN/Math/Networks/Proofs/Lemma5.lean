import SubNLogN.Math.Networks.Scalar

/-!
# [OAI26] Lemma 5 for the scalar triple networks, uniform in `h`

Proves, for every `h`, the four contracts of `Networks/Scalar.lean`:
`lemma5InvocationBit_holds`, `lemma5InvocationComplex_holds`, `lemma5Bit_holds`,
`lemma5Complex_holds`. No hypothesis is used beyond those in the statements (`2 * half = 1` in the
complex case); the modules and the coefficient ring are arbitrary (in `Type`, as in the statements)
and the initial scratch values are arbitrary ([OAI26, §3.1, Lemma 5]; Appendix D.2, Proposition D.3 (`oai:networks`)).

## Proof plan ([OAI26, §3.1, Lemma 5])
1. Fix an invocation `(j, ι)` and write `x_T = s (srcRole j ι T)`. For `α β : R`, `δ : Tri h → M`
   the state `upd s α β δ` adds `α • x_T` to every side wire `A_{ST}` of the invocation,
   `β • (G x)_c` to every central wire `C_c` of the invocation and `δ S` to the logical target
   `y_S`; all other roles keep their `s`-value. Each row maps such states to such states
   (`rowUpd_V_upd`, `rowUpd_G_upd`, `rowUpd_J_upd`, `rowUpd_R_upd`):
   `V(ε)`: `α ↦ α + ε`; `G(ε)`: `β ↦ β + ε`; `J(ε)`: `δ ↦ δ + ε • (J a + α • J V x)`;
   `R(ε)`: `δ ↦ δ + ε • (R c + β • R G x)`. This uses: no row writes a source role; `V`, `G` read
   only sources; `J`, `R` read only the side / central wires of the invocation.
2. Running the eight rows from `upd s 0 0 0 = s` gives `upd s 0 0 (σ_j • (J V x + R G x))`, with
   `σ_j = 1` (forward) and `σ_j = -1` (inverse schedule of stage 2) (`invocation_eq_upd`).
3. Combinatorics (`jv_add_rg_bit`, `jv_add_rg_complex`): `(J V x + R G x)_S = x_S`, via
   `Σ_{i∈S} Σ_{T∋i} x_T = Σ_T |S∩T| • x_T` and the coefficient check for `k = |S∩T| ∈ {0,1,2,3}`,
   where `k = 3 ↔ T = S`.
4. `stageMap`: a data role lies in the invocation `a.fix j` of stage `j` (`addr_mk_fix_var`);
   scratch roles are restored. Composing the three stages gives the network statements.
-/

namespace SubNLogN.Math.Networks

namespace Lemma5Proof

variable {h : ℕ} {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- `(J V x)_S`: the side injection applied to the copied sources `x_T = s (srcRole j ι T)`. -/
def jvVal (κ : Kind) (half : R) (j : Stage) (ι : Fix h) (s : Role κ h → M) (S : Tri h) : M :=
  ∑ T : {T : Tri h // Nbr κ S T}, coefJ κ half S T.1 • s (srcRole j ι T.1)

/-- `(R G x)_S`: the scatter applied to the gathered sources. -/
def rgVal (κ : Kind) (half : R) (j : Stage) (ι : Fix h) (s : Role κ h → M) (S : Tri h) : M :=
  match κ, s with
  | .bit, s => ∑ i ∈ S.1, gatherVal j ι s (.inl i)
  | .complex, s => half • (∑ i ∈ S.1, gatherVal j ι s (.inl i) - gatherVal j ι s (.inr ()))

/-- Intermediate state of invocation `(j, ι)` started from `s`: side wires of the invocation are
shifted by `α • x_T`, its central wires by `β • (G x)_c`, the logical target `y_S` by `δ S`; every
other role keeps its `s`-value. -/
def upd (κ : Kind) (j : Stage) (ι : Fix h) (s : Role κ h → M) (α β : R) (δ : Tri h → M) :
    Role κ h → M
  | .X a => match tgtTriple? j ι (Role.X (κ := κ) a) with
      | some S => s (.X a) + δ S
      | none => s (.X a)
  | .Y a => match tgtTriple? j ι (Role.Y (κ := κ) a) with
      | some S => s (.Y a) + δ S
      | none => s (.Y a)
  | .side j' ι' p => if j' = j ∧ ι' = ι then s (.side j' ι' p) + α • s (srcRole j ι p.1.2)
      else s (.side j' ι' p)
  | .center j' ι' c => if j' = j ∧ ι' = ι then s (.center j' ι' c) + β • gatherVal j ι s c
      else s (.center j' ι' c)

/-! ### Step 1: one row maps `upd`-states to `upd`-states -/

section RowLemmas

variable {κ : Kind} {half : R} {j : Stage} {ι : Fix h}

/-- `upd` does not change source roles. -/
theorem upd_srcRole (s : Role κ h → M) (α β : R) (δ : Tri h → M) (T : Tri h) :
    upd κ j ι s α β δ (srcRole j ι T) = s (srcRole j ι T) := by
  unfold srcRole
  cases hj : j.isInverse <;> simp [upd, tgtTriple?, hj]

/-- The gather reads only source roles. -/
theorem gatherVal_upd (s : Role κ h → M) (α β : R) (δ : Tri h → M) (c : Center κ h) :
    gatherVal j ι (upd κ j ι s α β δ) c = gatherVal j ι s c := by
  cases c <;> simp only [gatherVal, upd_srcRole]

/-- The side injection reads only the side wires of the invocation. -/
theorem sideVal_upd (s : Role κ h → M) (α β : R) (δ : Tri h → M) (S : Tri h) :
    sideVal κ half j ι (upd κ j ι s α β δ) S =
      sideVal κ half j ι s S + α • jvVal κ half j ι s S := by
  simp only [sideVal, jvVal, upd, true_and, if_true, Finset.smul_sum, ← Finset.sum_add_distrib,
    smul_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [smul_comm α]

/-- The scatter reads only the central wires of the invocation. -/
theorem scatterVal_upd (s : Role κ h → M) (α β : R) (δ : Tri h → M) (S : Tri h) :
    scatterVal κ half j ι (upd κ j ι s α β δ) S =
      scatterVal κ half j ι s S + β • rgVal κ half j ι s S := by
  cases κ with
  | bit =>
    simp only [scatterVal, rgVal, upd, true_and, if_true, Finset.sum_add_distrib,
      Finset.smul_sum]
  | complex =>
    simp only [scatterVal, rgVal, upd, true_and, if_true, Finset.sum_add_distrib,
      ← Finset.smul_sum]
    module

theorem rowUpd_V_upd (s : Role κ h → M) (α β ε : R) (δ : Tri h → M) :
    rowUpd κ half j ι .V ε (upd κ j ι s α β δ) = upd κ j ι s (α + ε) β δ := by
  funext w
  cases w with
  | X a => rfl
  | Y a => rfl
  | side j' ι' p =>
    simp only [rowUpd, upd_srcRole]
    simp only [upd]
    split_ifs <;> simp [add_smul, add_assoc]
  | center j' ι' c => rfl

theorem rowUpd_G_upd (s : Role κ h → M) (α β ε : R) (δ : Tri h → M) :
    rowUpd κ half j ι .G ε (upd κ j ι s α β δ) = upd κ j ι s α (β + ε) δ := by
  funext w
  cases w with
  | X a => rfl
  | Y a => rfl
  | side j' ι' p => rfl
  | center j' ι' c =>
    simp only [rowUpd, upd, gatherVal_upd]
    split_ifs <;> simp [add_smul, add_assoc]

theorem rowUpd_J_upd (s : Role κ h → M) (α β ε : R) (δ : Tri h → M) :
    rowUpd κ half j ι .J ε (upd κ j ι s α β δ) =
      upd κ j ι s α β (fun S => δ S + ε • (sideVal κ half j ι s S + α • jvVal κ half j ι s S)) := by
  funext w
  cases w with
  | X a =>
    simp only [rowUpd, upd, sideVal_upd]
    rcases tgtTriple? j ι (Role.X a) with _ | S
    · rfl
    · simp only [add_assoc]
  | Y a =>
    simp only [rowUpd, upd, sideVal_upd]
    rcases tgtTriple? j ι (Role.Y a) with _ | S
    · rfl
    · simp only [add_assoc]
  | side j' ι' p => rfl
  | center j' ι' c => rfl

theorem rowUpd_R_upd (s : Role κ h → M) (α β ε : R) (δ : Tri h → M) :
    rowUpd κ half j ι .R ε (upd κ j ι s α β δ) =
      upd κ j ι s α β
        (fun S => δ S + ε • (scatterVal κ half j ι s S + β • rgVal κ half j ι s S)) := by
  funext w
  cases w with
  | X a =>
    simp only [rowUpd, upd, scatterVal_upd]
    rcases tgtTriple? j ι (Role.X a) with _ | S
    · rfl
    · simp only [add_assoc]
  | Y a =>
    simp only [rowUpd, upd, scatterVal_upd]
    rcases tgtTriple? j ι (Role.Y a) with _ | S
    · rfl
    · simp only [add_assoc]
  | side j' ι' p => rfl
  | center j' ι' c => rfl

theorem upd_zero (s : Role κ h → M) : upd κ j ι s (0 : R) 0 (fun _ => 0) = s := by
  funext w
  cases w with
  | X a =>
    simp only [upd, add_zero]
    rcases tgtTriple? j ι (Role.X a) with _ | S <;> rfl
  | Y a =>
    simp only [upd, add_zero]
    rcases tgtTriple? j ι (Role.Y a) with _ | S <;> rfl
  | side j' ι' p => simp [upd]
  | center j' ι' c => simp [upd]

theorem upd_zero_apply (s : Role κ h → M) (δ : Tri h → M) (w : Role κ h) :
    upd κ j ι s (0 : R) 0 δ w =
      match tgtTriple? j ι w with
      | some S => s w + δ S
      | none => s w := by
  cases w with
  | X a => rfl
  | Y a => rfl
  | side j' ι' p => simp [upd, tgtTriple?]
  | center j' ι' c => simp [upd, tgtTriple?]

end RowLemmas

/-! ### Step 2: the eight rows of an invocation -/

/-- The forward schedule `−J, −R, +V, +G, +R, +J, −G, −V` as an explicit composition. -/
theorem invocation_fwd (κ : Kind) (half : R) (j : Stage) (ι : Fix h) (hj : j.isInverse = false)
    (s : Role κ h → M) :
    invocation κ half j ι s =
      rowUpd κ half j ι .V ((-1 : ℤ) : R) (rowUpd κ half j ι .G ((-1 : ℤ) : R)
        (rowUpd κ half j ι .J ((1 : ℤ) : R) (rowUpd κ half j ι .R ((1 : ℤ) : R)
        (rowUpd κ half j ι .G ((1 : ℤ) : R) (rowUpd κ half j ι .V ((1 : ℤ) : R)
        (rowUpd κ half j ι .R ((-1 : ℤ) : R) (rowUpd κ half j ι .J ((-1 : ℤ) : R) s))))))) := by
  cases j
  · rfl
  · simp [Stage.isInverse] at hj
  · rfl

/-- The inverse schedule of stage 2: `+V, +G, −J, −R, −G, −V, +R, +J`. -/
theorem invocation_inv (κ : Kind) (half : R) (j : Stage) (ι : Fix h) (hj : j.isInverse = true)
    (s : Role κ h → M) :
    invocation κ half j ι s =
      rowUpd κ half j ι .J ((1 : ℤ) : R) (rowUpd κ half j ι .R ((1 : ℤ) : R)
        (rowUpd κ half j ι .V ((-1 : ℤ) : R) (rowUpd κ half j ι .G ((-1 : ℤ) : R)
        (rowUpd κ half j ι .R ((-1 : ℤ) : R) (rowUpd κ half j ι .J ((-1 : ℤ) : R)
        (rowUpd κ half j ι .G ((1 : ℤ) : R) (rowUpd κ half j ι .V ((1 : ℤ) : R) s))))))) := by
  cases j
  · simp [Stage.isInverse] at hj
  · rfl
  · simp [Stage.isInverse] at hj

/-- One invocation, for arbitrary initial scratch values: the logical target `y_S` gains
`σ_j • ((J V x)_S + (R G x)_S)` with `σ_j = 1` forward and `σ_j = -1` at the inverse stage 2, and
every other role (sources, side and central wires, other roles) is restored. -/
theorem invocation_eq_upd (κ : Kind) (half : R) (j : Stage) (ι : Fix h) (s : Role κ h → M) :
    invocation κ half j ι s = upd κ j ι s (0 : R) 0 (fun S =>
      ((if j.isInverse then -1 else 1 : ℤ) : R) •
        (jvVal κ half j ι s S + rgVal κ half j ι s S)) := by
  have h0 : upd κ j ι s (0 : R) 0 (fun _ => 0) = s := upd_zero s
  cases hj : j.isInverse
  · rw [invocation_fwd κ half j ι hj s]
    conv_lhs => rw [← h0]
    simp only [rowUpd_J_upd, rowUpd_R_upd, rowUpd_V_upd, rowUpd_G_upd]
    congr 1
    · simp
    · simp
    · funext S
      simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_one]
      module
  · rw [invocation_inv κ half j ι hj s]
    conv_lhs => rw [← h0]
    simp only [rowUpd_J_upd, rowUpd_R_upd, rowUpd_V_upd, rowUpd_G_upd]
    congr 1
    · simp
    · simp
    · funext S
      simp only [↓reduceIte, Int.cast_neg, Int.cast_one]
      module

/-! ### Step 3: `J V + R G = 1` ([OAI26, §3.1, Lemma 5]) -/

theorem inter_le_three (S T : Tri h) : inter S T ≤ 3 := by
  unfold inter
  calc (S.1 ∩ T.1).card ≤ S.1.card := Finset.card_le_card Finset.inter_subset_left
    _ = 3 := S.2

theorem inter_self_eq_three (S : Tri h) : inter S S = 3 := by
  simp [inter, S.2]

/-- `|S ∩ T| = 3` forces `T = S`. -/
theorem eq_of_inter_eq_three {S T : Tri h} (hST : inter S T = 3) : T = S := by
  unfold inter at hST
  have h1 : S.1 ∩ T.1 = S.1 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hST, S.2])
  have h2 : S.1 ⊆ T.1 := Finset.inter_eq_left.mp h1
  have h3 : S.1 = T.1 := Finset.eq_of_subset_of_card_le h2 (by rw [S.2, T.2])
  exact Subtype.ext h3.symm

/-- Scatter after gather: `Σ_{i∈S} Σ_{T∋i} x_T = Σ_T |S ∩ T| • x_T`. -/
theorem sum_sum_filter_mem {N : Type*} [AddCommMonoid N] (S : Tri h) (x : Tri h → N) :
    ∑ i ∈ S.1, ∑ T ∈ Finset.univ.filter (fun T : Tri h => i ∈ T.1), x T =
      ∑ T, inter S T • x T := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_mem_eq_inter]
  rfl

/-- A sum over the neighbours of `S` as a sum over all triples. -/
theorem sum_nbr {N : Type*} [AddCommMonoid N] (κ : Kind) (S : Tri h) (f : Tri h → N) :
    ∑ T : {T : Tri h // Nbr κ S T}, f T.1 = ∑ T, if Nbr κ S T then f T else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun T => by simp) f).symm

/-- Bit network: `(J V x + R G x)_S = x_S` over `𝔽₂` (coefficient `[k = 1] + k ≡ [T = S]`). -/
theorem jv_add_rg_bit {Md : Type*} [AddCommGroup Md] [Module (ZMod 2) Md] (half : ZMod 2)
    (j : Stage) (ι : Fix h) (s : Role .bit h → Md) (S : Tri h) :
    jvVal .bit half j ι s S + rgVal .bit half j ι s S = s (srcRole j ι S) := by
  have hjv : jvVal .bit half j ι s S =
      ∑ T, (if inter S T = 1 then (1 : ZMod 2) else 0) • s (srcRole j ι T) := by
    simp only [jvVal, coefJ, one_smul]
    rw [sum_nbr .bit S (fun T => s (srcRole j ι T))]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases hn : inter S T = 1
    · have hn' : Nbr .bit S T := hn
      rw [if_pos hn', if_pos hn, one_smul]
    · have hn' : ¬ Nbr .bit S T := hn
      rw [if_neg hn', if_neg hn, zero_smul]
  have hrg : rgVal .bit half j ι s S =
      ∑ T, ((inter S T : ℕ) : ZMod 2) • s (srcRole j ι T) := by
    simp only [rgVal, gatherVal]
    rw [sum_sum_filter_mem S (fun T => s (srcRole j ι T))]
    simp only [Nat.cast_smul_eq_nsmul]
  have hc : ∀ T : Tri h, (if inter S T = 1 then (1 : ZMod 2) else 0) + ((inter S T : ℕ) : ZMod 2)
      = if T = S then 1 else 0 := by
    intro T
    by_cases hT : T = S
    · subst hT
      rw [inter_self_eq_three, if_pos rfl]
      decide
    · have h3 : inter S T ≠ 3 := fun e => hT (eq_of_inter_eq_three e)
      have hle := inter_le_three S T
      rw [if_neg hT]
      obtain e | e | e : inter S T = 0 ∨ inter S T = 1 ∨ inter S T = 2 := by omega
      all_goals rw [e]; decide
  rw [hjv, hrg, ← Finset.sum_add_distrib]
  simp_rw [← add_smul, hc, ite_smul, one_smul, zero_smul]
  simp

/-- Complex network: `(J V x + R G x)_S = x_S` when `2 * half = 1` (coefficient
`-[T nbr S] (k-1)/2 + (k-1)/2 = [T = S]`). -/
theorem jv_add_rg_complex {Rg Md : Type*} [CommRing Rg] [AddCommGroup Md] [Module Rg Md]
    (half : Rg) (h2 : 2 * half = 1) (j : Stage) (ι : Fix h) (s : Role .complex h → Md)
    (S : Tri h) :
    jvVal .complex half j ι s S + rgVal .complex half j ι s S = s (srcRole j ι S) := by
  have hjv : jvVal .complex half j ι s S = ∑ T, (if Nbr .complex S T then
      (if inter S T = 0 then half else -half) else 0) • s (srcRole j ι T) := by
    simp only [jvVal, coefJ]
    rw [sum_nbr .complex S
      (fun T => (if inter S T = 0 then half else -half) • s (srcRole j ι T))]
    refine Finset.sum_congr rfl fun T _ => ?_
    split_ifs <;> simp
  have hrg : rgVal .complex half j ι s S =
      ∑ T, (half * ((inter S T : Rg) - 1)) • s (srcRole j ι T) := by
    simp only [rgVal, gatherVal]
    rw [sum_sum_filter_mem S (fun T => s (srcRole j ι T)), smul_sub, Finset.smul_sum,
      Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← Nat.cast_smul_eq_nsmul Rg, mul_sub, mul_one, sub_smul, mul_smul]
  have hc : ∀ T : Tri h, (if Nbr .complex S T then (if inter S T = 0 then half else -half)
      else 0) + half * ((inter S T : Rg) - 1) = if T = S then 1 else 0 := by
    intro T
    by_cases hT : T = S
    · subst hT
      have hn : ¬ Nbr .complex T T := fun hn => hn.1 rfl
      rw [if_neg hn, inter_self_eq_three, if_pos rfl]
      push_cast
      linear_combination h2
    · have h3 : inter S T ≠ 3 := fun e => hT (eq_of_inter_eq_three e)
      have hle := inter_le_three S T
      rw [if_neg hT]
      obtain e | e | e : inter S T = 0 ∨ inter S T = 1 ∨ inter S T = 2 := by omega
      · have hn : Nbr .complex S T :=
          show S ≠ T ∧ (inter S T = 0 ∨ inter S T = 2) from ⟨fun e' => hT e'.symm, Or.inl e⟩
        rw [if_pos hn, e, if_pos rfl]
        push_cast
        ring
      · have hn : ¬ Nbr .complex S T := by
          rintro ⟨-, e' | e'⟩ <;> omega
        rw [if_neg hn, e]
        push_cast
        ring
      · have hn : Nbr .complex S T :=
          show S ≠ T ∧ (inter S T = 0 ∨ inter S T = 2) from ⟨fun e' => hT e'.symm, Or.inr e⟩
        rw [if_pos hn, e, if_neg (by norm_num)]
        push_cast
        ring
  rw [hjv, hrg, ← Finset.sum_add_distrib]
  simp_rw [← add_smul, hc, ite_smul, one_smul, zero_smul]
  simp

/-! ### Step 4: stages and the whole network ([OAI26, §3.1, Lemma 5]) -/

theorem addr_mk_fix_var (j : Stage) (a : Addr h) : Addr.mk j (a.fix j) (a.var j) = a := by
  cases j <;> rfl

theorem isInverse_one : Stage.isInverse .one = false := rfl
theorem isInverse_two : Stage.isInverse .two = true := rfl
theorem isInverse_three : Stage.isInverse .three = false := rfl

/-- The two facts about one invocation used by the stage computation, with net coefficient
`σ j`: a logical target `y_S` gains `σ j • x_S`, every other role is unchanged. -/
structure InvFacts (h : ℕ) (κ : Kind) (half : R) (σ : Stage → R) (M : Type*) [AddCommGroup M]
    [Module R M] : Prop where
  tgt : ∀ (j : Stage) (ι : Fix h) (s : Role κ h → M) (w : Role κ h) (S : Tri h),
    tgtTriple? j ι w = some S → invocation κ half j ι s w = s w + σ j • s (srcRole j ι S)
  other : ∀ (j : Stage) (ι : Fix h) (s : Role κ h → M) (w : Role κ h),
    tgtTriple? j ι w = none → invocation κ half j ι s w = s w

section Stages

variable {κ : Kind} {half : R} {σ : Stage → R}

theorem stage_X (hinv : InvFacts h κ half σ M) (j : Stage) (s : Role κ h → M) (a : Addr h) :
    stageMap κ half j s (.X a) =
      if j.isInverse then s (.X a) + σ j • s (.Y a) else s (.X a) := by
  show invocation κ half j (a.fix j) s (.X a) = _
  cases hj : j.isInverse
  · rw [if_neg Bool.false_ne_true]
    exact hinv.other j (a.fix j) s (.X a) (by simp [tgtTriple?, hj])
  · rw [if_pos rfl, hinv.tgt j (a.fix j) s (.X a) (a.var j) (by simp [tgtTriple?, hj])]
    simp [srcRole, hj, addr_mk_fix_var]

theorem stage_Y (hinv : InvFacts h κ half σ M) (j : Stage) (s : Role κ h → M) (a : Addr h) :
    stageMap κ half j s (.Y a) =
      if j.isInverse then s (.Y a) else s (.Y a) + σ j • s (.X a) := by
  show invocation κ half j (a.fix j) s (.Y a) = _
  cases hj : j.isInverse
  · rw [if_neg Bool.false_ne_true, hinv.tgt j (a.fix j) s (.Y a) (a.var j)
      (by simp [tgtTriple?, hj])]
    simp [srcRole, hj, addr_mk_fix_var]
  · rw [if_pos rfl]
    exact hinv.other j (a.fix j) s (.Y a) (by simp [tgtTriple?, hj])

theorem stage_scratch (hinv : InvFacts h κ half σ M) (j : Stage) (s : Role κ h → M)
    (w : Role κ h) (hw : w.IsScratch) : stageMap κ half j s w = s w := by
  simp only [stageMap]
  split
  · cases w with
    | X a => exact False.elim hw
    | Y a => exact False.elim hw
    | side j' ι' p => exact hinv.other _ _ _ _ rfl
    | center j' ι' c => exact hinv.other _ _ _ _ rfl
  · rfl

theorem net_X (hinv : InvFacts h κ half σ M) (s : Role κ h → M) (a : Addr h) :
    net κ half s (.X a) = s (.X a) + σ .two • (s (.Y a) + σ .one • s (.X a)) := by
  unfold net
  rw [stage_X hinv .three, isInverse_three, stage_X hinv .two, isInverse_two,
    stage_X hinv .one, stage_Y hinv .one, isInverse_one]
  simp

theorem net_Y (hinv : InvFacts h κ half σ M) (s : Role κ h → M) (a : Addr h) :
    net κ half s (.Y a) = (s (.Y a) + σ .one • s (.X a)) +
      σ .three • (s (.X a) + σ .two • (s (.Y a) + σ .one • s (.X a))) := by
  unfold net
  rw [stage_Y hinv .three, isInverse_three, stage_X hinv .two, stage_Y hinv .two, isInverse_two,
    stage_X hinv .one, stage_Y hinv .one, isInverse_one]
  simp

theorem net_scratch (hinv : InvFacts h κ half σ M) (s : Role κ h → M) (w : Role κ h)
    (hw : w.IsScratch) : net κ half s w = s w := by
  unfold net
  rw [stage_scratch hinv _ _ w hw, stage_scratch hinv _ _ w hw, stage_scratch hinv _ _ w hw]

end Stages

/-- Over `𝔽₂`, `x + x = 0`. -/
theorem add_self_bit {Md : Type*} [AddCommGroup Md] [Module (ZMod 2) Md] (x : Md) :
    x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 by decide, zero_smul]

end Lemma5Proof

open Lemma5Proof

/-- [OAI26, §3.1, Lemma 5] (first sentence), bit network: for every `h`, every
`𝔽₂`-module and arbitrary scratch values, one invocation sends `y_S ↦ y_S + x_S` (at stage 2:
`X_S ↦ X_S + Y_S = X_S − Y_S`) and leaves every other role unchanged. -/
theorem lemma5InvocationBit_holds (h : ℕ) : Lemma5InvocationBitStmt h := by
  intro Md _ _ j ι s w
  rw [invocation_eq_upd, upd_zero_apply]
  rcases tgtTriple? j ι w with _ | S
  · rfl
  · dsimp only
    rw [jv_add_rg_bit]
    have hσ : ((if j.isInverse then -1 else 1 : ℤ) : ZMod 2) = 1 := by
      split_ifs <;> decide
    rw [hσ, one_smul]

/-- [OAI26, §3.1, Lemma 5], complex network: for every `h`, every
commutative ring with `2 * half = 1`, every module and arbitrary scratch values, a forward
invocation sends `y_S ↦ y_S + x_S`, the inverse schedule of stage 2 sends `X_S ↦ X_S − Y_S`, and
every other role is unchanged. -/
theorem lemma5InvocationComplex_holds (h : ℕ) : Lemma5InvocationComplexStmt h := by
  intro Rg Md _ _ _ half h2 j ι s w
  rw [invocation_eq_upd, upd_zero_apply]
  rcases tgtTriple? j ι w with _ | S
  · rfl
  · dsimp only
    rw [jv_add_rg_complex half h2]

/-- [OAI26] Lemma 5 (B1), bit network: for every `h`, every `𝔽₂`-module and arbitrary scratch
values, the three stages realize the role permutation `ρ` (exchange `X_a ↔ Y_a`, scratch
restored): `net s (ρ w) = s w`. -/
theorem lemma5Bit_holds (h : ℕ) : Lemma5BitStmt h := by
  intro Md _ _ s w
  have hinv : InvFacts h .bit (0 : ZMod 2) (fun _ => 1) Md :=
    ⟨fun j ι s w S hS => by simp only [lemma5InvocationBit_holds h j ι s w, hS, one_smul],
      fun j ι s w hS => by simp only [lemma5InvocationBit_holds h j ι s w, hS]⟩
  cases w with
  | X a =>
    show net .bit (0 : ZMod 2) s (.Y a) = s (.X a)
    rw [net_Y hinv]
    simp only [one_smul]
    calc _ = (s (.X a) + s (.X a)) + (s (.Y a) + s (.Y a)) + s (.X a) := by abel
      _ = s (.X a) := by rw [add_self_bit, add_self_bit, zero_add, zero_add]
  | Y a =>
    show net .bit (0 : ZMod 2) s (.X a) = s (.Y a)
    rw [net_X hinv]
    simp only [one_smul]
    calc _ = (s (.X a) + s (.X a)) + s (.Y a) := by abel
      _ = s (.Y a) := by rw [add_self_bit, zero_add]
  | side j ι p => exact net_scratch hinv s (.side j ι p) trivial
  | center j ι c => exact net_scratch hinv s (.center j ι c) trivial

/-- [OAI26] Lemma 5 (C1), complex network: for every `h`, every commutative ring with
`2 * half = 1`, every module and arbitrary scratch values, the three stages send
`(X_a, Y_a) ↦ (−Y_a, X_a)` and restore every scratch role. -/
theorem lemma5Complex_holds (h : ℕ) : Lemma5ComplexStmt h := by
  intro Rg Md _ _ _ half h2 s
  have hinv : InvFacts h .complex half
      (fun j => ((if j.isInverse then -1 else 1 : ℤ) : Rg)) Md :=
    ⟨fun j ι s w S hS => by simp only [lemma5InvocationComplex_holds h half h2 j ι s w, hS],
      fun j ι s w hS => by simp only [lemma5InvocationComplex_holds h half h2 j ι s w, hS]⟩
  refine ⟨fun a => ?_, fun a => ?_, fun w hw => net_scratch hinv s w hw⟩
  · rw [net_Y hinv]
    simp only [isInverse_one, isInverse_two, isInverse_three, Bool.false_eq_true, if_true,
      if_false, Int.cast_neg, Int.cast_one]
    module
  · rw [net_X hinv]
    simp only [isInverse_one, isInverse_two, Bool.false_eq_true, if_true, if_false,
      Int.cast_neg, Int.cast_one]
    module

end SubNLogN.Math.Networks
