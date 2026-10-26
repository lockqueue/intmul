import SubNLogN.Math.Networks.Proofs.CCoreRole

/-!
# Lemma A.10 (`lem:transfer-phase`): the source and sink corrections of a complex-core node as folds

The source masks `Z_{a,f}` on the `X_a` roles and the sink corrections (`i^{27f} Z_{a,f}` on `Y_a`,
`−1` on `X_a`) of one internal node of `cCoreProc` run, at the level of role states, as a left fold
of `Function.update`s over the list `(Finset.univ : Finset (Addr 100)).toList`. We prove:

* `fold_pre_eq`: the fold of the source masks is `cxPre f`;
* `fold_post_eq`: the fold of the sink corrections is `cxPost f`.

Route (helpers in `SubNLogN.Math.Networks.CCoreNode.Folds`): `foldl_pointwise` — a fold over a
duplicate-free list of steps, where step `a` changes only the values at its keys `K a` (pairwise
disjoint for distinct `a`) and the new value at a key depends only on the old value there, is the
pointwise map. It is stated for an abstract key list, so membership in `Finset.univ` of the product
type `Addr 100` is only used through the generic lemma `mem_toList_univ` (never unfolded).
-/

namespace SubNLogN.Math.Networks

namespace CCoreNode

namespace Folds

/-- Every element of a finite type lies in `Finset.univ.toList`. -/
theorem mem_toList_univ {T : Type*} [Fintype T] (a : T) : a ∈ (Finset.univ : Finset T).toList :=
  Finset.mem_toList.mpr (Finset.mem_univ a)

/-- **Folds of key-local steps.** Let step `a` (`g s a`) change only the values at the keys
`K a w`, the new value at such a key `w` being `Φ a w (s w)`, and let distinct steps have disjoint
keys. Then along a duplicate-free list `l`, the fold has value `Φ a w (s w)` at every key `w` of a
step `a ∈ l`, and value `s w` at every other `w`. -/
theorem foldl_pointwise {κ α β : Type*} (g : (α → β) → κ → (α → β)) (K : κ → α → Prop)
    (Φ : κ → α → β → β)
    (hgK : ∀ s a w, K a w → g s a w = Φ a w (s w))
    (hgN : ∀ s a w, ¬ K a w → g s a w = s w)
    (hdisj : ∀ a b w, K a w → K b w → a = b) :
    ∀ (l : List κ), l.Nodup → ∀ s : α → β,
      (∀ a ∈ l, ∀ w, K a w → (l.foldl g s) w = Φ a w (s w)) ∧
      (∀ w, (∀ a ∈ l, ¬ K a w) → (l.foldl g s) w = s w) := by
  intro l
  induction l with
  | nil =>
    intro _ s
    exact ⟨fun a ha => absurd ha (List.not_mem_nil), fun w _ => rfl⟩
  | cons b l ih =>
    intro hnd s
    rw [List.nodup_cons] at hnd
    obtain ⟨hb, hl⟩ := hnd
    obtain ⟨ih1, ih2⟩ := ih hl (g s b)
    have hnotK : ∀ w, K b w → ∀ a ∈ l, ¬ K a w := fun w hbw a ha haw =>
      hb (by rw [← hdisj a b w haw hbw]; exact ha)
    refine ⟨?_, ?_⟩
    · intro a ha w haw
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | ha'
      · rw [ih2 w (hnotK w haw), hgK s a w haw]
      · have hbw : ¬ K b w := fun hbw => hnotK w hbw a ha' haw
        rw [ih1 a ha' w haw, hgN s b w hbw]
    · intro w hw
      rw [List.foldl_cons, ih2 w (fun a ha => hw a (List.mem_cons_of_mem b ha)),
        hgN s b w (hw b List.mem_cons_self)]

/-- Scalars pull out of `applyCol`. -/
theorem applyCol_smul_left {ι σ : Type*} [Fintype ι] (c : ℂ) (A : Matrix ι ι ℂ)
    (g : ι × σ → ℂ) : applyCol (c • A) g = c • applyCol A g := by
  funext p
  simp only [applyCol, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun y _ => by ring)

end Folds

open Folds

/-- The source masks `Z_{a,f}` on all `X_a` (as a fold of updates over `Addr 100`) give `cxPre f`. -/
theorem fold_pre_eq {σ : Type*} (f : ℕ) (s : Role .complex 100 → ((Fin f → Pt 100) × σ → ℂ)) :
    (Finset.univ : Finset (Addr 100)).toList.foldl
      (fun s a => Function.update s (Role.X a) (applyCol (Zk f (ua a)) (s (Role.X a)))) s =
      cxPre f s := by
  have hP := foldl_pointwise
    (fun (s : Role .complex 100 → ((Fin f → Pt 100) × σ → ℂ)) (a : Addr 100) =>
      Function.update s (Role.X a) (applyCol (Zk f (ua a)) (s (Role.X a))))
    (fun (a : Addr 100) (w : Role .complex 100) => w = Role.X a)
    (fun (a : Addr 100) (_ : Role .complex 100) (v : (Fin f → Pt 100) × σ → ℂ) =>
      applyCol (Zk f (ua a)) v)
    (fun s a w hw => by subst hw; exact Function.update_self _ _ _)
    (fun s a w hw => Function.update_of_ne hw _ _)
    (fun a b w ha hb => Role.X.inj (ha.symm.trans hb))
    (Finset.univ : Finset (Addr 100)).toList (Finset.nodup_toList _) s
  funext w
  cases w with
  | X a => exact hP.1 a (mem_toList_univ a) (Role.X a) rfl
  | Y a => exact hP.2 (Role.Y a) (fun b _ h => nomatch h)
  | side j ι p => exact hP.2 (Role.side j ι p) (fun b _ h => nomatch h)
  | center j ι c => exact hP.2 (Role.center j ι c) (fun b _ h => nomatch h)

/-- The sink corrections (`i^{27f} Z_{a,f}` on `Y_a`, `−1` on `X_a`; as a fold of updates over
`Addr 100`) give `cxPost f`. -/
theorem fold_post_eq {σ : Type*} (f : ℕ) (s : Role .complex 100 → ((Fin f → Pt 100) × σ → ℂ)) :
    (Finset.univ : Finset (Addr 100)).toList.foldl
      (fun s a => Function.update (Function.update s (Role.Y a)
        ((Complex.I ^ (27 * f)) • applyCol (Zk f (ua a)) (s (Role.Y a)))) (Role.X a)
        ((-1 : ℂ) • s (Role.X a))) s = cxPost f s := by
  have hP := foldl_pointwise
    (fun (s : Role .complex 100 → ((Fin f → Pt 100) × σ → ℂ)) (a : Addr 100) =>
      Function.update (Function.update s (Role.Y a)
        ((Complex.I ^ (27 * f)) • applyCol (Zk f (ua a)) (s (Role.Y a)))) (Role.X a)
        ((-1 : ℂ) • s (Role.X a)))
    (fun (a : Addr 100) (w : Role .complex 100) => w = Role.Y a ∨ w = Role.X a)
    (fun (a : Addr 100) (w : Role .complex 100) (v : (Fin f → Pt 100) × σ → ℂ) =>
      if w = Role.Y a then (Complex.I ^ (27 * f)) • applyCol (Zk f (ua a)) v
      else (-1 : ℂ) • v)
    (fun s a w hw => by
      rcases hw with rfl | rfl
      · rw [Function.update_of_ne
          (show (Role.Y a : Role .complex 100) ≠ Role.X a from fun h => nomatch h),
          Function.update_self, if_pos rfl]
      · rw [Function.update_self,
          if_neg (show ¬ ((Role.X a : Role .complex 100) = Role.Y a) from fun h => nomatch h)])
    (fun s a w hw => by
      rw [Function.update_of_ne (fun h => hw (Or.inr h)),
        Function.update_of_ne (fun h => hw (Or.inl h))])
    (fun a b w ha hb => by
      rcases ha with rfl | rfl <;> rcases hb with h | h
      · exact Role.Y.inj h
      · exact nomatch h
      · exact nomatch h
      · exact Role.X.inj h)
    (Finset.univ : Finset (Addr 100)).toList (Finset.nodup_toList _) s
  funext w
  cases w with
  | X a =>
    refine (hP.1 a (mem_toList_univ a) (Role.X a) (Or.inr rfl)).trans ?_
    show (if Role.X a = Role.Y a then _ else (-1 : ℂ) • s (Role.X a)) = -s (Role.X a)
    rw [if_neg (show ¬ ((Role.X a : Role .complex 100) = Role.Y a) from fun h => nomatch h)]
    exact neg_one_smul ℂ _
  | Y a =>
    refine (hP.1 a (mem_toList_univ a) (Role.Y a) (Or.inl rfl)).trans ?_
    show (if Role.Y a = Role.Y a then (Complex.I ^ (27 * f)) • applyCol (Zk f (ua a)) (s (Role.Y a))
      else _) = applyCol ((Complex.I ^ (27 * f)) • Zk f (ua a)) (s (Role.Y a))
    rw [if_pos rfl, applyCol_smul_left]
  | side j ι p =>
    exact hP.2 (Role.side j ι p)
      (fun b _ h => h.elim (fun h' => nomatch h') (fun h' => nomatch h'))
  | center j ι c =>
    exact hP.2 (Role.center j ι c)
      (fun b _ h => h.elim (fun h' => nomatch h') (fun h' => nomatch h'))

end CCoreNode

end SubNLogN.Math.Networks
