import SubNLogN.Math.Networks.CellCalc

/-!
# Networks: counting lemmas for the triple networks ([OAI26, §3.1, (3)–(4)])

Proofs of the counting contracts
* `CardTriStmt`, `CardNbrStmt`, `CardRoleStmt` (statements in `Networks/Basic.lean`), and
* `Cell.SumClassOfBitStmt`, `Cell.SumClassOfComplexStmt` (statements in `Networks/CellCalc.lean`).

All five statements are proved outright, for every `h` (no hypotheses). For `h < 3` there are no
triples and both sides vanish; the numerals of `Spec.lean` (truncated `ℕ` subtraction and
division) agree with the binomial coefficients for every `h`.

Proof plan.
1. `|Tri h| = C(h,3)` (`Fintype.card_finset_len`) and `C(n,3) = n(n-1)(n-2)/6`
   (`Nat.choose_eq_descFactorial_div_factorial`).
2. For `S : Tri h` and `k ≤ 3`: `#{T | |S ∩ T| = k} = C(3,k)·C(h-3,3-k)`, by the bijection
   `T ↦ (S ∩ T, T \ S)` onto `powersetCard k S ×ˢ powersetCard (3-k) Sᶜ` (`Finset.card_bij`;
   preimage of `(A, B)` is `A ∪ B`). Bit neighbours: `k = 1`; complex neighbours: `k ∈ {0, 2}`
   (the condition `S ≠ T` is then automatic since `|S ∩ S| = 3`).
3. `|SideIdx κ h| = Σ_S #{T | Nbr κ S T} = v·z` (`Equiv.subtypeProdEquivSigmaSubtype`,
   `Fintype.card_sigma`).
4. Roles: `Role.equivSum` gives `|Role| = 2|Addr| + |Stage×Fix×SideIdx| + |Stage×Fix×Center|`.
5. Class sums: reindex `Σ_w f (classOf w)` along `Role.equivSum` (`Fintype.sum_equiv`) to a
   function on the sum type defined by `Sum.elim`; split sums over `⊕` and `×`; every block has a
   constant summand; the `Stage` sum is the three-term list sum.
-/

namespace SubNLogN.Math.Networks

/-! ### Triples -/

/-- `C(n,3) = n(n-1)(n-2)/6` (truncated subtraction and division; valid for every `n`). -/
theorem choose_three_eq (n : ℕ) : n.choose 3 = n * (n - 1) * (n - 2) / 6 := by
  have h1 : n.descFactorial 3 = n * (n - 1) * (n - 2) := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one]
    ring
  have h2 : (3 : ℕ).factorial = 6 := rfl
  rw [Nat.choose_eq_descFactorial_div_factorial, h1, h2]

/-- `|𝒯| = C(h,3)`. -/
theorem card_tri_choose (h : ℕ) : Fintype.card (Tri h) = h.choose 3 := by
  rw [Fintype.card_finset_len, Fintype.card_fin]

/-- `|𝒯| = v` ([OAI26, §3.1]), for every `h`. -/
theorem card_tri (h : ℕ) : Fintype.card (Tri h) = tripleV h := by
  rw [card_tri_choose, choose_three_eq]
  rfl

/-- CONTRACT `CardTriStmt` holds. -/
theorem cardTri_holds : CardTriStmt := card_tri

/-! ### Neighbour counts -/

/-- `|S ∩ S| = 3`. -/
theorem inter_self_eq {h : ℕ} (S : Tri h) : inter S S = 3 := by
  unfold inter
  rw [Finset.inter_self]
  exact S.2

/-- For `S : Tri h` and `k ≤ 3`, exactly `C(3,k)·C(h-3,3-k)` triples `T` satisfy `|S ∩ T| = k`
(bijection `T ↦ (S ∩ T, T \ S)` onto `powersetCard k S ×ˢ powersetCard (3-k) Sᶜ`). -/
theorem card_filter_inter_eq {h : ℕ} (S : Tri h) (k : ℕ) (hk : k ≤ 3) :
    (Finset.univ.filter (fun T : Tri h => inter S T = k)).card =
      (3 : ℕ).choose k * (h - 3).choose (3 - k) := by
  have hS : S.1.card = 3 := S.2
  have hSc : S.1ᶜ.card = h - 3 := by rw [Finset.card_compl, Fintype.card_fin, hS]
  calc (Finset.univ.filter (fun T : Tri h => inter S T = k)).card
      = (Finset.powersetCard k S.1 ×ˢ Finset.powersetCard (3 - k) S.1ᶜ).card := by
        refine Finset.card_bij (fun T _ => (S.1 ∩ T.1, T.1 \ S.1)) ?_ ?_ ?_
        · intro T hT
          have hT' : (S.1 ∩ T.1).card = k := (Finset.mem_filter.1 hT).2
          refine Finset.mem_product.2 ⟨Finset.mem_powersetCard.2 ⟨Finset.inter_subset_left, hT'⟩,
            Finset.mem_powersetCard.2 ⟨?_, ?_⟩⟩
          · intro x hx
            exact Finset.mem_compl.2 (Finset.mem_sdiff.1 hx).2
          · rw [Finset.card_sdiff, T.2, hT']
        · intro T₁ _ T₂ _ heq
          obtain ⟨h1, h2⟩ := Prod.mk.inj heq
          apply Subtype.ext
          ext x
          have e1 := Finset.ext_iff.1 h1 x
          have e2 := Finset.ext_iff.1 h2 x
          simp only [Finset.mem_inter, Finset.mem_sdiff] at e1 e2
          tauto
        · rintro ⟨A, B⟩ hAB
          obtain ⟨hA, hB⟩ := Finset.mem_product.1 hAB
          obtain ⟨hAS, hAk⟩ := Finset.mem_powersetCard.1 hA
          obtain ⟨hBS, hBk⟩ := Finset.mem_powersetCard.1 hB
          have hdisj : Disjoint A B :=
            Finset.disjoint_left.2 fun x hxA hxB => Finset.mem_compl.1 (hBS hxB) (hAS hxA)
          have hcard : (A ∪ B).card = 3 := by
            rw [Finset.card_union_of_disjoint hdisj, hAk, hBk]
            omega
          have e1 : S.1 ∩ (A ∪ B) = A := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨hxS, hxA | hxB⟩
              · exact hxA
              · exact absurd hxS (Finset.mem_compl.1 (hBS hxB))
            · intro hxA
              exact ⟨hAS hxA, Or.inl hxA⟩
          have e2 : (A ∪ B) \ S.1 = B := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_union]
            constructor
            · rintro ⟨hxA | hxB, hxS⟩
              · exact absurd (hAS hxA) hxS
              · exact hxB
            · intro hxB
              exact ⟨Or.inr hxB, Finset.mem_compl.1 (hBS hxB)⟩
          refine ⟨⟨A ∪ B, hcard⟩, ?_, ?_⟩
          · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
            show (S.1 ∩ (A ∪ B)).card = k
            rw [e1, hAk]
          · show (S.1 ∩ (A ∪ B), (A ∪ B) \ S.1) = (A, B)
            rw [e1, e2]
    _ = (3 : ℕ).choose k * (h - 3).choose (3 - k) := by
        rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, hS, hSc]

/-- Bit neighbours (`|S ∩ T| = 1`): `z_b = 3·C(h-3,2)` ([OAI26, §3.1, (3)–(4)]). -/
theorem card_nbr_bit {h : ℕ} (S : Tri h) :
    (Finset.univ.filter (fun T => Nbr .bit S T)).card = tripleZb h := by
  have e : Finset.univ.filter (fun T => Nbr .bit S T) =
      Finset.univ.filter (fun T : Tri h => inter S T = 1) :=
    Finset.filter_congr (fun _ _ => Iff.rfl)
  have hc := card_filter_inter_eq S 1 (by norm_num)
  rw [show (3 : ℕ) - 1 = 2 from rfl, Nat.choose_one_right, Nat.choose_two_right] at hc
  have e4 : h - 3 - 1 = h - 4 := by omega
  rw [e, hc, e4]
  rfl

/-- Complex neighbours (`S ≠ T`, `|S ∩ T| ∈ {0, 2}`): `z_c = C(h-3,3) + 3(h-3)` ([OAI26, §3.1, (3)–(4)]). -/
theorem card_nbr_complex {h : ℕ} (S : Tri h) :
    (Finset.univ.filter (fun T => Nbr .complex S T)).card = tripleZc h := by
  have e : Finset.univ.filter (fun T => Nbr .complex S T) =
      Finset.univ.filter (fun T : Tri h => inter S T = 0) ∪
        Finset.univ.filter (fun T : Tri h => inter S T = 2) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro T _
    show S ≠ T ∧ (inter S T = 0 ∨ inter S T = 2) ↔ (inter S T = 0 ∨ inter S T = 2)
    constructor
    · exact fun hT => hT.2
    · intro hT
      refine ⟨?_, hT⟩
      rintro rfl
      rw [inter_self_eq] at hT
      omega
  have hdisj : Disjoint (Finset.univ.filter (fun T : Tri h => inter S T = 0))
      (Finset.univ.filter (fun T : Tri h => inter S T = 2)) := by
    rw [Finset.disjoint_filter]
    intro T _ h0 h2
    omega
  have h0 := card_filter_inter_eq S 0 (by norm_num)
  have h2 := card_filter_inter_eq S 2 (by norm_num)
  rw [show (3 : ℕ) - 0 = 3 from rfl, Nat.choose_zero_right, one_mul, choose_three_eq] at h0
  rw [show (3 : ℕ) - 2 = 1 from rfl, Nat.choose_one_right,
    show (3 : ℕ).choose 2 = 3 from rfl] at h2
  have e4 : h - 3 - 1 = h - 4 := by omega
  have e5 : h - 3 - 2 = h - 5 := by omega
  rw [e, Finset.card_union_of_disjoint hdisj, h0, h2, e4, e5]
  rfl

/-- CONTRACT `CardNbrStmt` holds. -/
theorem cardNbr_holds : CardNbrStmt := fun _ S => ⟨card_nbr_bit S, card_nbr_complex S⟩

/-! ### Role counts -/

/-- `|Stage| = 3`. -/
theorem card_stage : Fintype.card Stage = 3 := rfl

/-- No extra central wire in the bit network. -/
theorem card_cstar_bit : Fintype.card (CStar .bit) = 0 := rfl

/-- One extra central wire `C_*` in the complex network. -/
theorem card_cstar_complex : Fintype.card (CStar .complex) = 1 := rfl

/-- `|Center κ h| = h + |CStar κ|`. -/
theorem card_center (κ : Kind) (h : ℕ) :
    Fintype.card (Center κ h) = h + Fintype.card (CStar κ) := by
  rw [Fintype.card_sum, Fintype.card_fin]

/-- If every triple has exactly `z` `κ`-neighbours, there are `v·z` side indices. -/
theorem card_sideIdx_of {κ : Kind} {h : ℕ} (z : ℕ)
    (hz : ∀ S : Tri h, (Finset.univ.filter (fun T => Nbr κ S T)).card = z) :
    Fintype.card (SideIdx κ h) = tripleV h * z := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun S T : Tri h => Nbr κ S T)),
    Fintype.card_sigma]
  simp only [Fintype.card_subtype, hz]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, card_tri]

/-- Role count through `Role.equivSum`: `2N + I·(|SideIdx| + |Center|)`. -/
theorem card_role_eq (κ : Kind) (h : ℕ) :
    Fintype.card (Role κ h) = 2 * tripleN h +
      tripleI h * (Fintype.card (SideIdx κ h) + Fintype.card (Center κ h)) := by
  rw [Fintype.card_congr (Role.equivSum κ h)]
  simp only [Fintype.card_sum, Fintype.card_prod, card_stage, card_tri]
  unfold tripleN tripleI
  ring

/-- CONTRACT `CardRoleStmt` holds. -/
theorem cardRole_holds : CardRoleStmt := by
  intro h
  refine ⟨?_, ?_⟩
  · rw [card_role_eq, card_sideIdx_of (tripleZb h) (fun S => card_nbr_bit S), card_center,
      card_cstar_bit]
    rfl
  · rw [card_role_eq, card_sideIdx_of (tripleZc h) (fun S => card_nbr_complex S), card_center,
      card_cstar_complex]
    rfl

/-! ### Class sums -/

/-- A sum over the three stages. -/
theorem sum_stage {M : Type*} [AddCommMonoid M] (F : Stage → M) :
    ∑ j, F j = F .one + F .two + F .three := by
  have hu : (Finset.univ : Finset Stage) = {.one, .two, .three} := rfl
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    add_assoc]

/-- Summing a class function over all roles of either network. -/
theorem sum_classOf_eq (κ : Kind) (h : ℕ) (f : Cell.RClass → ℕ) :
    ∑ w : Role κ h, f (Cell.classOf w) = tripleN h * (f .X + f .Y) +
      ([Stage.one, .two, .three].map fun j =>
        tripleV h ^ 2 * Fintype.card (SideIdx κ h) * f (.side j) +
          tripleV h ^ 2 * (h + Fintype.card (CStar κ)) * f (.center j)).sum := by
  rw [Fintype.sum_equiv (Role.equivSum κ h) (fun w => f (Cell.classOf w))
    (Sum.elim (Sum.elim (fun _ => f .X) (fun _ => f .Y))
      (Sum.elim (fun x => f (.side x.1)) (fun x => f (.center x.1))))
    (fun w => by cases w <;> rfl)]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_sum,
    Fintype.card_fin, card_tri, sum_stage, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  unfold tripleN
  ring

/-- CONTRACT `Cell.SumClassOfBitStmt` holds. -/
theorem Cell.sumClassOfBit_holds : Cell.SumClassOfBitStmt := by
  intro h f
  rw [sum_classOf_eq, card_sideIdx_of (tripleZb h) (fun S => card_nbr_bit S), card_cstar_bit]
  rfl

/-- CONTRACT `Cell.SumClassOfComplexStmt` holds. -/
theorem Cell.sumClassOfComplex_holds : Cell.SumClassOfComplexStmt := by
  intro h f
  rw [sum_classOf_eq, card_sideIdx_of (tripleZc h) (fun S => card_nbr_complex S),
    card_cstar_complex]

end SubNLogN.Math.Networks
