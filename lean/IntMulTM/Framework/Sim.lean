import IntMulTM.Framework.Eval

/-!
# IntMulTM.Framework.Sim — the compiler is exact; machines and the generic wrapper

* `sim` : if `Eval ρ p s s' t`, any machine with the code of `p` installed (and the enclosing
  bodies installed, `EnvOK`) goes from the entry of `p` to its exit in **exactly** `t`
  `Turing.TM2.step`s; the return stack below the current frame is unchanged.
* `machine`, `toFinTM2` : the compiled `Turing.FinTM2` (stacks `Option K`, registers
  `σ × Option Λ`, labels `Option (Lab p)`; label `none` resets the registers and halts).
* `toTM2ComputableInTime` : program + spec ⇒ `Turing.TM2ComputableInTime` (generic stacks).
* `finite_MachΓ` : all machine alphabets are finite if the user alphabets are.
-/

namespace TMFw

open Turing Prog

section Sim

variable {K : Type} {Γ : K → Type} {σ : Type} [DecidableEq K]

theorem update_liftStk_some {Λ : Type} (S : ∀ k, List (Γ k)) (R : List Λ) (k : K)
    (x : List (Γ k)) :
    Function.update (liftStk S R) (some k) x = liftStk (Function.update S k x) R := by
  funext k'
  cases k' with
  | none => erw [Function.update_of_ne (by simp)]; rfl
  | some k' =>
    by_cases h : k' = k
    · subst h
      erw [Function.update_self]
      show x = Function.update S _ x _
      rw [Function.update_self]
    · erw [Function.update_of_ne (by simpa using h)]
      show S k' = Function.update S k x k'
      rw [Function.update_of_ne h]

theorem update_liftStk_none {Λ : Type} (S : ∀ k, List (Γ k)) (R R' : List Λ) :
    Function.update (liftStk S R) none R' = liftStk (Γ := Γ) S R' := by
  funext k'
  cases k' with
  | none => erw [Function.update_self]; rfl
  | some k' => erw [Function.update_of_ne (by simp)]; rfl

theorem rstep_some {Λ : Type} (M : Λ → TM2.Stmt (MachΓ K Γ Λ) Λ (σ × Option Λ)) (l : Λ)
    (v : σ × Option Λ) (S : ∀ k, List (MachΓ K Γ Λ k)) :
    TM2.step M ⟨some l, v, S⟩ = some (TM2.stepAux (M l) v S) := rfl

/-- **Exact simulation.** -/
theorem sim {ρ : List (Prog K Γ σ)} {p : Prog K Γ σ} {s s' : St K Γ σ} {t : ℕ}
    (h : Eval ρ p s s' t) :
    ∀ {Λ : Type} (M : Λ → TM2.Stmt (MachΓ K Γ Λ) Λ (σ × Option Λ)) (emb : Lab p → Λ) (ex : Λ)
      (res : List Λ), Installed M p emb ex res → EnvOK M ρ res →
      ∀ (R : List Λ) (r : Option Λ), ∃ r',
        ReachesIn (TM2.step M) t ⟨some (emb (entry p)), (s.var, r), liftStk s.stk R⟩
          ⟨some ex, (s'.var, r'), liftStk s'.stk R⟩ := by
  induction h with
  | push _ k f v S =>
    intro Λ M emb ex res hM _ R r
    refine ⟨r, ReachesIn.single ?_⟩
    rw [rstep_some, hM]
    show some (⟨some ex, (v, r), Function.update (liftStk S R) (some k) (f v :: S k)⟩ :
        TM2.Cfg _ _ _) = some ⟨some ex, (v, r), liftStk (Function.update S k (f v :: S k)) R⟩
    erw [update_liftStk_some]
    rfl
  | peek _ k f v S =>
    intro Λ M emb ex res hM _ R r
    exact ⟨r, ReachesIn.single (by rw [rstep_some, hM]; rfl)⟩
  | pop _ k f v S =>
    intro Λ M emb ex res hM _ R r
    refine ⟨r, ReachesIn.single ?_⟩
    rw [rstep_some, hM]
    show some (⟨some ex, (f v (S k).head?, r),
        Function.update (liftStk S R) (some k) (S k).tail⟩ : TM2.Cfg _ _ _) =
      some ⟨some ex, (f v (S k).head?, r), liftStk (Function.update S k (S k).tail) R⟩
    rw [update_liftStk_some]
  | load _ f v S =>
    intro Λ M emb ex res hM _ R r
    exact ⟨r, ReachesIn.single (by rw [rstep_some, hM]; rfl)⟩
  | seq _ _ ih₁ ih₂ =>
    intro Λ M emb ex res hM hE R r
    obtain ⟨r₁, h₁⟩ := ih₁ M _ _ res (fun l => hM (Sum.inl l)) hE R r
    obtain ⟨r₂, h₂⟩ := ih₂ M _ ex res (fun l => hM (Sum.inr l)) hE R r₁
    exact ⟨r₂, h₁.trans h₂⟩
  | @ite_true ρ c p q s s' t hc _ ih =>
    intro Λ M emb ex res hM hE R r
    obtain ⟨r₁, h₁⟩ := ih M _ ex res (fun l => hM (Sum.inr (Sum.inl l))) hE R r
    refine ⟨r₁, ReachesIn.head ?_ h₁⟩
    rw [rstep_some, hM]
    show some (cond (c s.var) _ _) = _
    rw [hc]
    rfl
  | @ite_false ρ c p q s s' t hc _ ih =>
    intro Λ M emb ex res hM hE R r
    obtain ⟨r₁, h₁⟩ := ih M _ ex res (fun l => hM (Sum.inr (Sum.inr l))) hE R r
    refine ⟨r₁, ReachesIn.head ?_ h₁⟩
    rw [rstep_some, hM]
    show some (cond (c s.var) _ _) = _
    rw [hc]
    rfl
  | @loop_true ρ c p s s₁ s₂ t₁ t₂ hc _ _ ih₁ ih₂ =>
    intro Λ M emb ex res hM hE R r
    obtain ⟨r₁, h₁⟩ := ih₁ M (fun l => emb (Sum.inr l)) (emb (Sum.inl ())) res
      (fun l => hM (Sum.inr l)) hE R r
    obtain ⟨r₂, h₂⟩ := ih₂ M emb ex res hM hE R r₁
    have h₀ : TM2.step M ⟨some (emb (entry (.loop c p))), (s.var, r), liftStk s.stk R⟩ =
        some ⟨some (emb (Sum.inr (entry p))), (s.var, r), liftStk s.stk R⟩ := by
      rw [rstep_some, hM]
      show some (cond (c s.var) _ _) = _
      rw [hc]
      rfl
    exact ⟨r₂, ReachesIn.head h₀ (h₁.trans h₂)⟩
  | @loop_false ρ c p s hc =>
    intro Λ M emb ex res hM _ R r
    refine ⟨r, ReachesIn.single ?_⟩
    rw [rstep_some, hM]
    show some (cond (c s.var) _ _) = _
    rw [hc]
    rfl
  | @fix ρ b s s' t _ ih =>
    intro Λ M emb ex res hM hE R r
    have hE' : EnvOK M (b :: ρ) (emb (Sum.inr (Sum.inr (entry b))) :: res) :=
      ⟨⟨fun l => emb (Sum.inr (Sum.inr l)), emb (Sum.inr (Sum.inl ())), ex,
        fun l => hM (Sum.inr (Sum.inr l)), rfl, hM (Sum.inr (Sum.inl ()))⟩, hE⟩
    obtain ⟨r₁, h₁⟩ := ih M (fun l => emb (Sum.inr (Sum.inr l))) (emb (Sum.inr (Sum.inl ())))
      (emb (Sum.inr (Sum.inr (entry b))) :: res) (fun l => hM (Sum.inr (Sum.inr l))) hE'
      (ex :: R) r
    have hcall : TM2.step M ⟨some (emb (entry (.fix b))), (s.var, r), liftStk s.stk R⟩ =
        some ⟨some (emb (Sum.inr (Sum.inr (entry b)))), (s.var, r), liftStk s.stk (ex :: R)⟩ := by
      rw [rstep_some, hM]
      show some (⟨some (emb (Sum.inr (Sum.inr (entry b)))), (s.var, r),
          Function.update (liftStk s.stk R) none (ex :: R)⟩ : TM2.Cfg _ _ _) =
        some ⟨some (emb (Sum.inr (Sum.inr (entry b)))), (s.var, r), liftStk s.stk (ex :: R)⟩
      erw [update_liftStk_none]
      rfl
    have hret : TM2.step M ⟨some (emb (Sum.inr (Sum.inl ()))), (s'.var, r₁),
        liftStk s'.stk (ex :: R)⟩ = some ⟨some ex, (s'.var, some ex), liftStk s'.stk R⟩ := by
      erw [rstep_some, hM]
      show some (⟨some ex, (s'.var, some ex),
          Function.update (liftStk s'.stk (ex :: R)) none R⟩ : TM2.Cfg _ _ _) =
        some ⟨some ex, (s'.var, some ex), liftStk s'.stk R⟩
      rw [update_liftStk_none]
    exact ⟨some ex, ReachesIn.head hcall (h₁.trans (ReachesIn.single hret))⟩
  | @recur ρ n b s s' t hb _ ih =>
    intro Λ M emb ex res hM hE R r
    have hd := EnvOK.drop n hE
    rw [drop_eq_cons_of_getElem? hb] at hd
    obtain ⟨re, res', hres⟩ : ∃ re res', res.drop n = re :: res' := by
      cases h' : res.drop n with
      | nil => rw [h'] at hd; exact False.elim hd
      | cons re res' => exact ⟨re, res', rfl⟩
    rw [hres] at hd
    obtain ⟨⟨embB, rl, d, hB, hentry, hrl⟩, hrest⟩ := hd
    have hd' : EnvOK M (ρ.drop n) (re :: res') := by
      rw [drop_eq_cons_of_getElem? hb]
      exact ⟨⟨embB, rl, d, hB, hentry, hrl⟩, hrest⟩
    obtain ⟨r₁, h₁⟩ := ih M embB rl (re :: res') hB hd' (ex :: R) r
    rw [hentry] at h₁
    have hcall : TM2.step M ⟨some (emb (entry (.recur n : Prog K Γ σ))), (s.var, r),
        liftStk s.stk R⟩ = some ⟨some re, (s.var, r), liftStk s.stk (ex :: R)⟩ := by
      rw [rstep_some, hM]
      show some (⟨some (res.getD n ex), (s.var, r),
          Function.update (liftStk s.stk R) none (ex :: R)⟩ : TM2.Cfg _ _ _) =
        some ⟨some re, (s.var, r), liftStk s.stk (ex :: R)⟩
      erw [getD_eq_of_drop_eq_cons hres, update_liftStk_none]
      rfl
    have hret : TM2.step M ⟨some rl, (s'.var, r₁), liftStk s'.stk (ex :: R)⟩ =
        some ⟨some ex, (s'.var, some ex), liftStk s'.stk R⟩ := by
      rw [rstep_some, hrl]
      show some (⟨some ex, (s'.var, some ex),
          Function.update (liftStk s'.stk (ex :: R)) none R⟩ : TM2.Cfg _ _ _) =
        some ⟨some ex, (s'.var, some ex), liftStk s'.stk R⟩
      rw [update_liftStk_none]
    exact ⟨some ex, ReachesIn.head hcall (h₁.trans (ReachesIn.single hret))⟩

/-! ## Whole machines -/

omit [DecidableEq K] in
/-- The compiled machine: control points of `p`, plus the final label `none` (reset the
registers, halt). -/
def machine (p : Prog K Γ σ) (σ0 : σ) :
    Option (Lab p) →
      TM2.Stmt (MachΓ K Γ (Option (Lab p))) (Option (Lab p)) (σ × Option (Option (Lab p)))
  | some l => code p some none [] l
  | none => .load (fun _ => (σ0, none)) .halt

omit [DecidableEq K] in
theorem machine_installed (p : Prog K Γ σ) (σ0 : σ) :
    Installed (machine p σ0) p some none [] :=
  fun _ => rfl

/-- End-to-end run: `t` steps for the program, one for the final register reset. -/
theorem machine_run {p : Prog K Γ σ} (σ0 : σ) {s s' : St K Γ σ} {t : ℕ} (h : Eval [] p s s' t) :
    ReachesIn (TM2.step (machine p σ0)) (t + 1)
      ⟨some (some (entry p)), (s.var, none), liftStk s.stk []⟩
      ⟨none, (σ0, none), liftStk s'.stk []⟩ := by
  obtain ⟨_, h'⟩ := sim h (machine p σ0) some none [] (machine_installed p σ0) trivial [] none
  exact h'.trans (ReachesIn.single rfl)

/-- The bundled Mathlib machine. -/
def toFinTM2 [Fintype K] [Fintype σ] (k₀ k₁ : K) [Fintype (Γ k₀)] (p : Prog K Γ σ) (σ0 : σ) :
    FinTM2 where
  K := Option K
  k₀ := some k₀
  k₁ := some k₁
  Γ := MachΓ K Γ (Option (Lab p))
  Λ := Option (Lab p)
  main := some (entry p)
  σ := σ × Option (Option (Lab p))
  initialState := (σ0, none)
  Γk₀Fin := inferInstanceAs (Fintype (Γ k₀))
  m := machine p σ0

/-- Stacks that are all empty except stack `k`, which holds `l`. -/
def stkOnly (k : K) (l : List (Γ k)) : ∀ k', List (Γ k') :=
  Function.update (fun k' => ([] : List (Γ k'))) k l

theorem liftStk_stkOnly {Λ : Type} (k : K) (l : List (Γ k)) :
    liftStk (stkOnly k l) ([] : List Λ) =
      Function.update (fun k' => ([] : List (MachΓ K Γ Λ k'))) (some k) l := by
  funext k'
  cases k' with
  | none => erw [Function.update_of_ne (by simp)]; rfl
  | some k' =>
    show stkOnly k l k' =
      Function.update (fun k' => ([] : List (MachΓ K Γ Λ k'))) (some k) l (some k')
    by_cases h : k' = k
    · subst h
      erw [Function.update_self]
      exact Function.update_self _ _ _
    · erw [Function.update_of_ne (by simpa using h)]
      exact Function.update_of_ne h _ _

end Sim

/-! ## Mathlib's `initList` / `haltList` -/

theorem initList_eq (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    initList tm l = ⟨some tm.main, tm.initialState,
      Function.update (fun k => ([] : List (tm.Γ k))) tm.k₀ l⟩ := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h
    rw [dif_pos rfl, Function.update_self]
    rfl
  · rw [dif_neg h, Function.update_of_ne h]

theorem haltList_eq (tm : FinTM2) (l : List (tm.Γ tm.k₁)) :
    haltList tm l = ⟨none, tm.initialState,
      Function.update (fun k => ([] : List (tm.Γ k))) tm.k₁ l⟩ := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h
    rw [dif_pos rfl, Function.update_self]
    rfl
  · rw [dif_neg h, Function.update_of_ne h]

/-- Extract Mathlib's (data-carrying) `EvalsToInTime` from a propositional step bound. -/
noncomputable def evalsToInTime_of_exists {α : Type} {f : α → Option α} {a : α} {b : Option α}
    {m : ℕ} (h : ∃ n, n ≤ m ∧ (flip bind f)^[n] (some a) = b) :
    StateTransition.EvalsToInTime f a b m :=
  ⟨⟨h.choose, h.choose_spec.2⟩, h.choose_spec.1⟩

section Wrapper

variable {K : Type} {Γ : K → Type} {σ : Type}

/-- **Generic wrapper**: program + spec ⇒ `Turing.TM2ComputableInTime`. -/
noncomputable def toTM2ComputableInTime {α β αΓ βΓ : Type} [Fintype αΓ]
    (ea : Computability.Encoding α αΓ)
    (eb : Computability.Encoding β βΓ) (f : α → β) [DecidableEq K] [Fintype K] [Fintype σ]
    (k₀ k₁ : K) (e₀ : Γ k₀ ≃ αΓ) (e₁ : Γ k₁ ≃ βΓ) (p : Prog K Γ σ) (σ0 : σ)
    (time : ℕ → ℕ)
    (hspec : ∀ a, ∃ v t, Eval [] p ⟨σ0, stkOnly k₀ ((ea.encode a).map e₀.invFun)⟩
      ⟨v, stkOnly k₁ ((eb.encode (f a)).map e₁.invFun)⟩ t ∧ t + 1 ≤ time (ea.encode a).length) :
    TM2ComputableInTime ea.encode eb.encode f :=
  letI : Fintype (Γ k₀) := Fintype.ofEquiv _ e₀.symm
  { tm := toFinTM2 k₀ k₁ p σ0
    inputAlphabet := e₀
    outputAlphabet := e₁
    time := time
    outputsFun := fun a => evalsToInTime_of_exists (by
      obtain ⟨v, t, he, hle⟩ := hspec a
      refine ⟨t + 1, hle, ?_⟩
      rw [initList_eq, Option.map_some, haltList_eq]
      have hr := (machine_run σ0 he).iterate_eq
      rw [liftStk_stkOnly, liftStk_stkOnly] at hr
      exact hr) }

theorem toTM2ComputableInTime_time {α β αΓ βΓ : Type} [Fintype αΓ]
    {ea : Computability.Encoding α αΓ}
    {eb : Computability.Encoding β βΓ} {f : α → β} [DecidableEq K] [Fintype K] [Fintype σ]
    {k₀ k₁ : K} {e₀ : Γ k₀ ≃ αΓ} {e₁ : Γ k₁ ≃ βΓ} {p : Prog K Γ σ} {σ0 : σ}
    {time : ℕ → ℕ} {hspec} (L : ℕ) :
    (toTM2ComputableInTime ea eb f k₀ k₁ e₀ e₁ p σ0 time hspec).time L = time L := rfl

/-- All machine alphabets (including the hidden return stack) are finite. -/
theorem finite_MachΓ {Λ : Type} [Finite Λ] (hΓ : ∀ k, Finite (Γ k)) :
    ∀ k, Finite (MachΓ K Γ Λ k)
  | none => inferInstanceAs (Finite Λ)
  | some k => hΓ k

theorem toTM2ComputableInTime_finite {α β αΓ βΓ : Type} [Fintype αΓ]
    {ea : Computability.Encoding α αΓ}
    {eb : Computability.Encoding β βΓ} {f : α → β} [DecidableEq K] [Fintype K] [Fintype σ]
    {k₀ k₁ : K} {e₀ : Γ k₀ ≃ αΓ} {e₁ : Γ k₁ ≃ βΓ} {p : Prog K Γ σ} {σ0 : σ}
    {time : ℕ → ℕ} {hspec} (hΓ : ∀ k, Finite (Γ k)) :
    ∀ k, Finite ((toTM2ComputableInTime ea eb f k₀ k₁ e₀ e₁ p σ0 time hspec).tm.Γ k) :=
  finite_MachΓ (Λ := Option (Lab p)) hΓ

end Wrapper

end TMFw
