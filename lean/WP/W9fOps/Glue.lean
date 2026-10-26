import Contracts.Machine.W3

/-!
# WP.W9fOps.Glue — calling contract programs, atom lemmas, sign-magnitude facts

Standalone copy (frozen deps only) of the glue of `wp/W3b`:
* `call ι lens P := (P.mapStk ι).liftRegs lens` runs a contract program on the host stacks `ι l`
  with its registers at `lens`; `call_eval_upd` / `call_eval_same` turn the contract's `Runs` on
  `B ∘ ι` into an exact `Eval` on the host stacks; `call_closed` preserves closedness.
* `emb f hm : Loc n m → Loc n' 4`: named stacks along `f`, scratch stacks shared (`j ↦ j`).
* Atoms with rewritten end states; facts about `natSyms`, `intSyms`, `sgnSym`.
-/

namespace WP.W9fOps

open TMFw TMFw.Lib TMFw.Contracts Computability

/-! ## Closedness -/

section Closed

variable {K K' A σ τ : Type}

theorem freeBelow_mapStk (ι : K → K') (p : Prog K (fun _ => A) σ) :
    ∀ d, p.FreeBelow d → (p.mapStk ι).FreeBelow d := by
  induction p with
  | push _ _ => exact fun _ _ => trivial
  | peek _ _ => exact fun _ _ => trivial
  | pop _ _ => exact fun _ _ => trivial
  | load _ => exact fun _ _ => trivial
  | seq p q ihp ihq =>
    intro d h
    obtain ⟨h1, h2⟩ := h
    exact ⟨ihp d h1, ihq d h2⟩
  | ite c p q ihp ihq =>
    intro d h
    obtain ⟨h1, h2⟩ := h
    exact ⟨ihp d h1, ihq d h2⟩
  | loop c p ih => exact fun d h => ih d h
  | fix b ih => exact fun d h => ih (d + 1) h
  | recur _ => exact fun _ h => h

theorem freeBelow_liftRegs {Γ : K → Type} (l : Lens σ τ) (p : Prog K Γ τ) :
    ∀ d, p.FreeBelow d → (p.liftRegs l).FreeBelow d := by
  induction p with
  | push _ _ => exact fun _ _ => trivial
  | peek _ _ => exact fun _ _ => trivial
  | pop _ _ => exact fun _ _ => trivial
  | load _ => exact fun _ _ => trivial
  | seq p q ihp ihq =>
    intro d h
    obtain ⟨h1, h2⟩ := h
    exact ⟨ihp d h1, ihq d h2⟩
  | ite c p q ihp ihq =>
    intro d h
    obtain ⟨h1, h2⟩ := h
    exact ⟨ihp d h1, ihq d h2⟩
  | loop c p ih => exact fun d h => ih d h
  | fix b ih => exact fun d h => ih (d + 1) h
  | recur _ => exact fun _ h => h

end Closed

/-! ## Calling a contract program -/

section Call

variable {L K R σ : Type}

/-- Run `P` on the stacks `ι l`, with its registers at `lens`. -/
def call (ι : L → K) (lens : Lens σ R) (P : Prog L (fun _ => Sym) R) : Prog K (fun _ => Sym) σ :=
  (P.mapStk ι).liftRegs lens

theorem call_closed (ι : L → K) (lens : Lens σ R) {P : Prog L (fun _ => Sym) R} (hP : P.Closed) :
    (call ι lens P).Closed :=
  freeBelow_liftRegs lens _ 0 (freeBelow_mapStk ι P 0 hP)

variable [DecidableEq L] [DecidableEq K]

theorem call_eval {ι : L → K} (hι : Function.Injective ι) {P : Prog L (fun _ => Sym) R}
    {B : K → List Sym} {S' : L → List Sym} {Q : R → Prop} {T : ℕ}
    (h : Runs P (fun l => B (ι l)) S' Q T) (lens : Lens σ R) (v : σ) :
    ∃ r t B', Eval [] (call ι lens P) ⟨v, B⟩ ⟨lens.set v r, B'⟩ t ∧ Q r ∧ t ≤ T ∧
      (∀ l, B' (ι l) = S' l) ∧ (∀ k, (∀ l, ι l ≠ k) → B' k = B k) := by
  obtain ⟨s', t, e, ⟨hs', hq⟩, ht⟩ := h ⟨lens.get v, fun l => B (ι l)⟩ rfl
  obtain ⟨B', ha, hb, e'⟩ := Eval.mapStk hι e B (fun _ => rfl)
  exact ⟨s'.var, t, B', Eval.liftRegs lens e' v rfl, hq, ht,
    fun l => (ha l).trans (congrFun hs' l), hb⟩

/-- `call_eval` when the contract updates one stack `l₀`. -/
theorem call_eval_upd {ι : L → K} (hι : Function.Injective ι) {P : Prog L (fun _ => Sym) R}
    {B : K → List Sym} {l₀ : L} {x : List Sym} {Q : R → Prop} {T : ℕ}
    (h : Runs P (fun l => B (ι l)) (Function.update (fun l => B (ι l)) l₀ x) Q T)
    (lens : Lens σ R) (v : σ) :
    ∃ r t, Eval [] (call ι lens P) ⟨v, B⟩ ⟨lens.set v r, Function.update B (ι l₀) x⟩ t ∧
      Q r ∧ t ≤ T := by
  obtain ⟨r, t, B', e, hq, ht, h1, h2⟩ := call_eval hι h lens v
  have hB' : B' = Function.update B (ι l₀) x := by
    funext k
    by_cases hk : ∃ l, ι l = k
    · obtain ⟨l, rfl⟩ := hk
      rw [h1 l]
      by_cases hl : l = l₀
      · subst hl
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hl, Function.update_of_ne (hι.ne hl)]
    · have hk' : ∀ l, ι l ≠ k := fun l hl => hk ⟨l, hl⟩
      rw [h2 k hk', Function.update_of_ne (fun e => hk' l₀ e.symm)]
  subst hB'
  exact ⟨r, t, e, hq, ht⟩

/-- `call_eval` when the contract leaves every stack unchanged. -/
theorem call_eval_same {ι : L → K} (hι : Function.Injective ι) {P : Prog L (fun _ => Sym) R}
    {B : K → List Sym} {Q : R → Prop} {T : ℕ}
    (h : Runs P (fun l => B (ι l)) (fun l => B (ι l)) Q T) (lens : Lens σ R) (v : σ) :
    ∃ r t, Eval [] (call ι lens P) ⟨v, B⟩ ⟨lens.set v r, B⟩ t ∧ Q r ∧ t ≤ T := by
  obtain ⟨r, t, B', e, hq, ht, h1, h2⟩ := call_eval hι h lens v
  have hB' : B' = B := by
    funext k
    by_cases hk : ∃ l, ι l = k
    · obtain ⟨l, rfl⟩ := hk
      exact h1 l
    · exact h2 k fun l hl => hk ⟨l, hl⟩
  subst hB'
  exact ⟨r, t, e, hq, ht⟩

end Call

/-! ## The standard embedding into `Loc n' 4` -/

/-- Named stacks along `f`, scratch stack `j ↦ j`. -/
def emb {n n' m : ℕ} (f : Fin n → Fin n') (hm : m ≤ 4) : Loc n m → Loc n' 4
  | .inl i => .inl (f i)
  | .inr j => .inr ⟨j.val, by have := j.isLt; omega⟩

theorem emb_injective {n n' m : ℕ} {f : Fin n → Fin n'} (hf : Function.Injective f) (hm : m ≤ 4) :
    Function.Injective (emb f hm) := by
  rintro (i | j) (i' | j') h
  · simp only [emb, Sum.inl.injEq] at h
    rw [hf h]
  · simp [emb] at h
  · simp [emb] at h
  · simp only [emb, Sum.inr.injEq, Fin.mk.injEq] at h
    rw [Fin.ext h]

/-! ## Atoms with rewritten end states -/

section Atoms

variable {K σ : Type} [DecidableEq K]

theorem eval_stk {ρ : List (Prog K (fun _ => Sym) σ)} {p : Prog K (fun _ => Sym) σ}
    {s : St K (fun _ => Sym) σ} {v : σ} {S₁ S₂ : K → List Sym} {t : ℕ}
    (h : Eval ρ p s ⟨v, S₁⟩ t) (hS : S₁ = S₂) : Eval ρ p s ⟨v, S₂⟩ t := by
  subst hS
  exact h

theorem eval_pop_eq (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ)
    (v : σ) (S : K → List Sym) (x : Sym) (L : List Sym) (hS : S k = x :: L) :
    Eval ρ (.pop k f) ⟨v, S⟩ ⟨f v (some x), Function.update S k L⟩ 1 :=
  (Eval.pop ρ k f v S).of_eq (by simp only [hS, List.head?_cons, List.tail_cons]) rfl

theorem eval_pop_int (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Option Sym → σ)
    (v : σ) (S : K → List Sym) (z : ℤ) (rx : List Sym) (hS : S k = intSyms z ++ rx) :
    Eval ρ (.pop k f) ⟨v, S⟩
      ⟨f v (some (sgnSym z)), Function.update S k (natSyms z.natAbs ++ rx)⟩ 1 :=
  eval_pop_eq ρ k f v S _ _ hS

theorem eval_push_eq (ρ : List (Prog K (fun _ => Sym) σ)) (k : K) (f : σ → Sym) (v : σ)
    (S : K → List Sym) (x : Sym) (L : List Sym) (hx : f v = x) (hL : S k = L) :
    Eval ρ (.push k f) ⟨v, S⟩ ⟨v, Function.update S k (x :: L)⟩ 1 :=
  (Eval.push ρ k f v S).of_eq (by rw [hx, hL]) rfl

end Atoms

/-! ## Sign-magnitude facts -/

theorem intSyms_append (z : ℤ) (rx : List Sym) :
    intSyms z ++ rx = sgnSym z :: (natSyms z.natAbs ++ rx) := rfl

theorem sgnSym_of_neg {z : ℤ} (h : z < 0) : sgnSym z = .neg := if_pos h

theorem sgnSym_of_nonneg {z : ℤ} (h : 0 ≤ z) : sgnSym z = .pos := if_neg (by omega)

theorem sgnSym_congr {z w : ℤ} (h : z < 0 ↔ w < 0) : sgnSym z = sgnSym w := by
  unfold sgnSym
  by_cases hz : z < 0
  · rw [if_pos hz, if_pos (h.1 hz)]
  · rw [if_neg hz, if_neg (fun hw => hz (h.2 hw))]

/-- Is the register the sign `neg`? -/
def isNegR (r : Option Sym) : Bool := decide (r = some .neg)

theorem isNegR_sgnSym (z : ℤ) : isNegR (some (sgnSym z)) = decide (z < 0) := by
  unfold isNegR sgnSym
  by_cases h : z < 0 <;> simp [h]

#assert_std_axioms freeBelow_mapStk freeBelow_liftRegs call_closed call_eval call_eval_upd
  call_eval_same emb_injective eval_stk eval_pop_eq eval_pop_int eval_push_eq sgnSym_congr
  isNegR_sgnSym

end WP.W9fOps
