import WP.W7k2.Call
import WP.W9comp.Kit

/-!
# WP.W9s.Basic — layout, encodings and loop rules for the synthetic-FFT machine

The machine keeps a matrix as a *block*: its rows, each followed by `symRow`, then `symBlk`.
Temporary stacks are guarded by `symG`; unary counters are runs of `symU`. All these are tags, so
they never occur inside entries (`tag_not_mem_es`).

Programs live on a W7k2 host `Loc a b` and are specified with `HT` (exact stacks). Loops are
`whileTop lS k f body`: peek `k`, and run `body` while `f` holds of the peeked symbol. `LoopHT`
is the loop part entered with the register already holding the top of `k`; `LoopHT.stop` and
`LoopHT.step` give it by induction over the data, and `HT.whileTop` closes it.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-! ## Layout symbols -/

/-- End of a row. -/
def symRow : Sym := .tag 8
/-- End of a block. -/
def symBlk : Sym := .tag 9
/-- Wrap marker inside a rotated row. -/
def symWrap : Sym := .tag 10
/-- Guard of a temporary stack. -/
def symG : Sym := .tag 11
/-- Unary unit. -/
def symU : Sym := .tag 12

/-- Layout tags. -/
def isTag : Sym → Bool
  | .tag _ => true
  | _ => false

/-! ## Encodings -/

/-- Entries, first entry on top. -/
def es (l : List (ℤ × ℤ)) : List Sym := l.flatMap entrySyms

/-- A row and its terminator. -/
def rowE (row : List (ℤ × ℤ)) : List Sym := es row ++ [symRow]

/-- The rows of a block (without the block terminator). -/
def blkR (X : List (List (ℤ × ℤ))) : List Sym := X.flatMap rowE

/-- A unary counter. -/
def units (n : ℕ) : List Sym := List.replicate n symU

theorem notTag_intSyms (z : ℤ) : ∀ x ∈ intSyms z, isTag x = false := by
  intro x hx
  simp only [intSyms, natSyms, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨b, -, rfl⟩
  · unfold sgnSym
    split <;> rfl
  · rfl

theorem notTag_entrySyms (z : ℤ × ℤ) : ∀ x ∈ entrySyms z, isTag x = false := by
  intro x hx
  unfold entrySyms at hx
  rcases List.mem_append.mp hx with h | h
  · exact notTag_intSyms _ x h
  · rcases List.mem_cons.mp h with rfl | h
    · rfl
    · rcases List.mem_append.mp h with h | h
      · exact notTag_intSyms _ x h
      · rw [List.mem_singleton.mp h]
        rfl

theorem notTag_es (l : List (ℤ × ℤ)) : ∀ x ∈ es l, isTag x = false := by
  intro x hx
  obtain ⟨z, -, hz⟩ := List.mem_flatMap.mp hx
  exact notTag_entrySyms z x hz

theorem tag_not_mem_es {t : Sym} (ht : isTag t = true) (l : List (ℤ × ℤ)) : t ∉ es l :=
  fun h => by
    rw [notTag_es l t h] at ht
    exact Bool.false_ne_true ht

theorem es_nil : es [] = [] := rfl

theorem es_cons (z : ℤ × ℤ) (l : List (ℤ × ℤ)) : es (z :: l) = entrySyms z ++ es l := by
  simp [es]

theorem es_append (l₁ l₂ : List (ℤ × ℤ)) : es (l₁ ++ l₂) = es l₁ ++ es l₂ := by
  simp [es]

theorem blkR_nil : blkR [] = [] := rfl

theorem blkR_cons (row : List (ℤ × ℤ)) (X : List (List (ℤ × ℤ))) :
    blkR (row :: X) = rowE row ++ blkR X := by
  simp [blkR]

theorem blkR_append (X Y : List (List (ℤ × ℤ))) : blkR (X ++ Y) = blkR X ++ blkR Y := by
  simp [blkR]

theorem units_succ (n : ℕ) : units (n + 1) = symU :: units n := rfl

theorem units_add (m n : ℕ) : units (m + n) = units m ++ units n := by
  rw [units, units, units, List.replicate_add]

theorem length_units (n : ℕ) : (units n).length = n := by
  simp [units]

/-! ## Generic `HT` rules -/

section Rules

variable {a b : ℕ} {σ : Type}

/-- `rewindTo` lifted through a symbol register, in any environment. -/
theorem HT.rewind (lS : Lens σ (Option Sym)) {src dst : Loc a b} (hne : src ≠ dst) (g : Sym)
    (L rest : List Sym) (B : Loc a b → List Sym) (hg : g ∉ L) (hB : B src = L ++ g :: rest)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B ((WP.W9comp.rewindTo src dst g).liftRegs lS)
      (Function.update (Function.update B src rest) dst (L.reverse ++ B dst))
      (3 * L.length + 2) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  have e := Eval.liftRegs lS (WP.W9comp.rewindTo_eval hne g (lS.get v) L rest S hg hB) v rfl
  exact ⟨_, _, e.env_irrel (WP.W9comp.closed_rewind lS src dst g) ρ, rfl, le_rfl⟩

/-- A closed program on another register type, lifted through a lens. -/
theorem HT.lift {τ : Type} (l : Lens σ τ) {p : Prog (Loc a b) (fun _ => Sym) τ} (hc : p.Closed)
    {B B' : Loc a b → List Sym} {T : ℕ} (h : HT [] B p B' T)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) : HT ρ B (p.liftRegs l) B' T := by
  have h2 := Triple.liftRegs l h (fun _ => True) (fun _ _ _ => trivial)
  have h3 := Triple.env_irrel h2 (WP.W9comp.closed_liftRegs l hc) ρ
  exact Triple.conseq h3 (fun s hs => ⟨hs, trivial⟩) (fun s hs => hs.1) le_rfl

/-- Peek `k` into the symbol register. -/
def peekL (lS : Lens σ (Option Sym)) (k : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .peek k (fun v o => lS.set v o)

/-- **While loop on the top of a stack**: peek `k`, then run `body` while `f` holds of the peeked
symbol (the body is followed by a fresh peek). -/
def whileTop (lS : Lens σ (Option Sym)) (k : Loc a b) (f : Option Sym → Bool)
    (body : Prog (Loc a b) (fun _ => Sym) σ) : Prog (Loc a b) (fun _ => Sym) σ :=
  .seq (peekL lS k) (.loop (fun v => f (lS.get v)) (.seq body (peekL lS k)))

theorem whileTop_closed (lS : Lens σ (Option Sym)) (k : Loc a b) (f : Option Sym → Bool)
    {body : Prog (Loc a b) (fun _ => Sym) σ} (hb : body.Closed) :
    (whileTop lS k f body).Closed :=
  ⟨trivial, hb, trivial⟩

/-- The loop part of `whileTop`, entered with the register holding the top of `k`. -/
def LoopHT (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) (lS : Lens σ (Option Sym)) (k : Loc a b)
    (f : Option Sym → Bool) (body : Prog (Loc a b) (fun _ => Sym) σ)
    (B B' : Loc a b → List Sym) (T : ℕ) : Prop :=
  Triple ρ (fun s => s.stk = B ∧ lS.get s.var = (B k).head?)
    (.loop (fun v => f (lS.get v)) (.seq body (peekL lS k))) (fun s => s.stk = B') T

variable {ρ : List (Prog (Loc a b) (fun _ => Sym) σ)} {lS : Lens σ (Option Sym)} {k : Loc a b}
  {f : Option Sym → Bool} {body : Prog (Loc a b) (fun _ => Sym) σ}

theorem LoopHT.stop {B : Loc a b → List Sym} (h : f (B k).head? = false) :
    LoopHT ρ lS k f body B B 1 := by
  rintro ⟨v, S⟩ ⟨hS, hv⟩
  change S = B at hS
  subst hS
  refine ⟨_, 1, Eval.loop_false ?_, rfl, le_rfl⟩
  show f (lS.get v) = false
  rw [hv]
  exact h

theorem LoopHT.step {B B₁ B₂ : Loc a b → List Sym} {T₁ T₂ : ℕ} (h : f (B k).head? = true)
    (hb : HT ρ B body B₁ T₁) (hr : LoopHT ρ lS k f body B₁ B₂ T₂) :
    LoopHT ρ lS k f body B B₂ (T₁ + 1 + T₂ + 1) := by
  rintro ⟨v, S⟩ ⟨hS, hv⟩
  change S = B at hS
  subst hS
  obtain ⟨⟨v₁, S₁⟩, t₁, e₁, h₁, ht₁⟩ := hb ⟨v, S⟩ rfl
  change S₁ = B₁ at h₁
  subst h₁
  have e₂ : Eval ρ (peekL lS k) ⟨v₁, S₁⟩ ⟨lS.set v₁ (S₁ k).head?, S₁⟩ 1 :=
    Eval.peek ρ k (fun v o => lS.set v o) v₁ S₁
  obtain ⟨s₃, t₃, e₃, h₃, ht₃⟩ := hr ⟨lS.set v₁ (S₁ k).head?, S₁⟩ ⟨rfl, lS.get_set _ _⟩
  refine ⟨s₃, t₁ + 1 + t₃ + 1, Eval.loop_true ?_ (Eval.seq e₁ e₂) e₃, h₃, by omega⟩
  show f (lS.get v) = true
  rw [hv]
  exact h

theorem LoopHT.mono {B B' : Loc a b → List Sym} {T T' : ℕ} (h : LoopHT ρ lS k f body B B' T)
    (hT : T ≤ T') : LoopHT ρ lS k f body B B' T' :=
  Triple.cost_mono h hT

theorem HT.whileTop {B B' : Loc a b → List Sym} {T : ℕ} (h : LoopHT ρ lS k f body B B' T) :
    HT ρ B (WP.W9s.whileTop lS k f body) B' (T + 1) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  obtain ⟨s', t, e, h', ht⟩ := h ⟨lS.set v (S k).head?, S⟩ ⟨rfl, lS.get_set _ _⟩
  exact ⟨s', 1 + t, Eval.seq (Eval.peek ρ k _ v S) e, h', by omega⟩

end Rules

#assert_std_axioms notTag_intSyms notTag_entrySyms notTag_es tag_not_mem_es es_cons es_append
  blkR_cons blkR_append units_add length_units HT.rewind HT.lift whileTop_closed LoopHT.stop
  LoopHT.step LoopHT.mono HT.whileTop es_nil blkR_nil units_succ

end WP.W9s
