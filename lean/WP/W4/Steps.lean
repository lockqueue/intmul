import WP.W4.Rec
import WP.W4.PureT

/-!
# WP.W4.Steps — bounded evaluation from a known register (`EvLe`), atoms, record facts
-/

namespace TMFw.W4

open TMFw TMFw.Lib TMFw.Contracts

variable {K : Type} [DecidableEq K]

/-- From register `r` and stacks `S`, `p` reaches register `r'` and stacks `S'` within `T` steps. -/
def EvLe (ρ : List (SProg K)) (p : SProg K) (r : Option Sym) (S : K → List Sym)
    (r' : Option Sym) (S' : K → List Sym) (T : ℕ) : Prop :=
  ∃ t, Eval ρ p ⟨r, S⟩ ⟨r', S'⟩ t ∧ t ≤ T

section EvLe

variable {ρ : List (SProg K)} {p q : SProg K} {r r₁ r₂ : Option Sym} {S S₁ S₂ : K → List Sym}
  {T T₁ T₂ : ℕ}

theorem EvLe.of_eval {t : ℕ} (e : Eval ρ p ⟨r, S⟩ ⟨r₁, S₁⟩ t) (h : t ≤ T) :
    EvLe ρ p r S r₁ S₁ T := ⟨t, e, h⟩

theorem EvLe.seq (h₁ : EvLe ρ p r S r₁ S₁ T₁) (h₂ : EvLe ρ q r₁ S₁ r₂ S₂ T₂) :
    EvLe ρ (.seq p q) r S r₂ S₂ (T₁ + T₂) := by
  obtain ⟨t₁, e₁, h₁⟩ := h₁
  obtain ⟨t₂, e₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂, Eval.seq e₁ e₂, by omega⟩

theorem EvLe.mono (h : EvLe ρ p r S r₁ S₁ T₁) (hT : T₁ ≤ T₂) : EvLe ρ p r S r₁ S₁ T₂ := by
  obtain ⟨t, e, ht⟩ := h
  exact ⟨t, e, by omega⟩

theorem EvLe.of_eq (h : EvLe ρ p r S r₁ S₁ T₁) (hr : r₁ = r₂) (hS : S₁ = S₂) (hT : T₁ ≤ T₂) :
    EvLe ρ p r S r₂ S₂ T₂ := by
  subst hr hS
  exact h.mono hT

theorem EvLe.loop_true {c : Option Sym → Bool} (hc : c r = true) (h₁ : EvLe ρ p r S r₁ S₁ T₁)
    (h₂ : EvLe ρ (.loop c p) r₁ S₁ r₂ S₂ T₂) : EvLe ρ (.loop c p) r S r₂ S₂ (T₁ + T₂ + 1) := by
  obtain ⟨t₁, e₁, h₁⟩ := h₁
  obtain ⟨t₂, e₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂ + 1, Eval.loop_true hc e₁ e₂, by omega⟩

theorem EvLe.loop_false {c : Option Sym → Bool} (hc : c r = false) :
    EvLe ρ (.loop c p) r S r S 1 :=
  ⟨1, Eval.loop_false hc, le_rfl⟩

theorem RunsIn.of_evLe (f : Option Sym → Option Sym) (h : ∀ r, EvLe ρ p r S (f r) S₁ T) :
    RunsIn ρ p S S₁ T := fun v => by
  obtain ⟨t, e, ht⟩ := h v
  exact ⟨f v, t, e, ht⟩

theorem RunsIn.evLe (h : RunsIn ρ p S S₁ T) (r : Option Sym) : ∃ r₁, EvLe ρ p r S r₁ S₁ T := by
  obtain ⟨v', t, e, ht⟩ := h r
  exact ⟨v', t, e, ht⟩

end EvLe

/-! ## Atoms -/

theorem peekR_evLe (ρ : List (SProg K)) (k : K) (r : Option Sym) (S : K → List Sym) :
    EvLe ρ (peekR k) r S (S k).head? S 1 :=
  ⟨1, Eval.peek ρ k (fun _ o => o) r S, le_rfl⟩

theorem popR_evLe (ρ : List (SProg K)) (k : K) (r : Option Sym) (S : K → List Sym) :
    EvLe ρ (popR k) r S (S k).head? (Function.update S k (S k).tail) 1 :=
  ⟨1, Eval.pop ρ k (fun _ o => o) r S, le_rfl⟩

theorem pushC_evLe (ρ : List (SProg K)) (k : K) (x : Sym) (r : Option Sym) (S : K → List Sym) :
    EvLe ρ (pushC k x) r S r (Function.update S k (x :: S k)) 1 :=
  ⟨1, Eval.push ρ k (fun _ => x) r S, le_rfl⟩

/-! ## Record facts -/

theorem length_le_length_flatten : ∀ (l : List (List Sym)), (∀ r ∈ l, RecOK r) →
    l.length ≤ l.flatten.length
  | [], _ => le_rfl
  | r :: l, h => by
    have h1 := RecOK.length_pos (h r (by simp))
    have h2 := length_le_length_flatten l (fun x hx => h x (by simp [hx]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

theorem Good.length_le {N L : ℕ} {l : List (List Sym)} (h : Good N L l) : N ≤ L := by
  rw [← h.1, ← h.2.1]
  exact length_le_length_flatten l h.2.2

theorem mem_of_mem_dealE {α : Type} {l : List α} {x : α} (hx : x ∈ dealE l) : x ∈ l :=
  (perm_unsh l).mem_iff.1 (List.mem_append_left _ hx)

theorem mem_of_mem_dealO {α : Type} {l : List α} {x : α} (hx : x ∈ dealO l) : x ∈ l :=
  (perm_unsh l).mem_iff.1 (List.mem_append_right _ hx)

theorem length_flatten_deal (l : List (List Sym)) :
    (dealE l).flatten.length + (dealO l).flatten.length = l.flatten.length := by
  rw [← length_flatten_of_perm (perm_unsh l), unsh, List.flatten_append, List.length_append]

/-- `RecOK` records start with `sep` once reversed. -/
theorem reverse_recOK_head {r : List Sym} (hr : RecOK r) (rest : List Sym) :
    (r.reverse ++ rest).head? = some Sym.sep := by
  obtain ⟨d, rfl, _⟩ := hr
  simp

#assert_std_axioms EvLe.of_eval EvLe.seq EvLe.mono EvLe.of_eq EvLe.loop_true EvLe.loop_false
  RunsIn.of_evLe RunsIn.evLe peekR_evLe popR_evLe pushC_evLe length_le_length_flatten
  Good.length_le mem_of_mem_dealE mem_of_mem_dealO length_flatten_deal reverse_recOK_head

end TMFw.W4
