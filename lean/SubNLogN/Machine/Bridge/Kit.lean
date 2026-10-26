/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.Values

/-!
# K5 reduction (3): composition kit for the bridge machine

* `peekTop`, `topIsBit`, `runs_peekTop`: the loop test reads the top of the counter stack into the
  flag register (`natSyms n` has a bit on top iff `n ≠ 0`).
* `runs_counted_loop`: a machine loop over a `natSyms` counter (counting down to `0`), from a
  `Runs` contract of one iteration; cost via `loopCost`, `loopCost_le`.
* the composite layout `KLoc BrN (BrW ⊕ EP)`: embeddings of a bridge part (`ιK`), of the middle
  (`ιM`, named stacks `Fin 2`) and of a one-stack `Loc 1 m` kernel on the counter (`ιD`); the
  composite state `mkB S W sr ds` and transport lemmas; `runs_partK`, `runs_partM`, `runs_partD`.

All proved.
-/

namespace SubNLogN.Machine.BridgeRed

open TMFw TMFw.Contracts SubNLogN.Machine Computability

/-! ## The loop test and counted loops -/

section Loop

variable {K σ' : Type} [DecidableEq K]

/-- Read the top of stack `k` into the flag register (`Option Sym × σ'`). -/
def peekTop (k : K) : Prog K (fun _ => Sym) (Option Sym × σ') := .peek k (fun v o => (o, v.2))

/-- The loop test: the flag holds a bit. -/
def topIsBit : Option Sym × σ' → Bool
  | (some (.bit _), _) => true
  | _ => false

theorem runs_peekTop (k : K) (B : K → List Sym) :
    Runs (peekTop (σ' := σ') k) B B (fun v => v.1 = (B k).head?) 1 := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = B at hs
  subst hs
  exact ⟨_, 1, Eval.peek _ _ _ _ _, ⟨rfl, rfl⟩, le_refl _⟩

theorem closed_peekTop (k : K) : (peekTop (σ' := σ') k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, peekTop]

omit [DecidableEq K] in
theorem topIsBit_natSyms (n : ℕ) (w : σ') :
    topIsBit ((natSyms n).head?, w) = decide (n ≠ 0) := by
  rcases h : encodeNat n with _ | ⟨b, l⟩
  · have := (encodeNat_eq_nil_iff n).mp h
    subst this
    simp [natSyms, h, topIsBit]
  · have hn : n ≠ 0 := by
      intro h0
      subst h0
      simp [encodeNat_zero] at h
    simp [natSyms, h, topIsBit, hn]

/-- `loopCost` as a sum. -/
theorem loopCost_eq_sum (B : ℕ → ℕ) :
    ∀ N, loopCost B N = ((List.range N).map fun n => B n + 1).sum + 1
  | 0 => by simp [loopCost]
  | N + 1 => by
    rw [loopCost, loopCost_eq_sum B N, List.range_succ, List.map_append, List.sum_append]
    simp
    omega

/-- **Counted loop over a `natSyms` counter.** If the stack `k` holds exactly `natSyms n` in the
state `B n` (`n ≤ N`) and one iteration `core` runs from `B (n+1)` to `B n`, then
`peekTop k ; loop topIsBit (core ; peekTop k)` runs from `B N` to `B 0`. -/
theorem runs_counted_loop (k : K) (core : Prog K (fun _ => Sym) (Option Sym × σ'))
    (B : ℕ → K → List Sym) (N : ℕ) (T : ℕ → ℕ)
    (hk : ∀ n, n ≤ N → B n k = natSyms n)
    (hstep : ∀ n, n + 1 ≤ N → Runs core (B (n + 1)) (B n) (fun _ => True) (T n)) :
    Runs (.seq (peekTop k) (.loop topIsBit (.seq core (peekTop k)))) (B N) (B 0) (fun _ => True)
      (1 + loopCost (fun n => T n + 1) N) := by
  let I : ℕ → St K (fun _ => Sym) (Option Sym × σ') → Prop := fun n s =>
    n ≤ N ∧ s.stk = B n ∧ s.var.1 = (natSyms n).head?
  have hloop := Triple.loop (ρ := []) (c := topIsBit) (I := I) (B := fun n => T n + 1)
    (p := .seq core (peekTop k))
    (fun n => by
      intro s hs
      obtain ⟨hn, hstk, -⟩ := hs
      have h1 := hstep n hn
      have h2 := runs_peekTop (σ' := σ') k (B n)
      have h12 := WP.W9comp.runs_seq h1 h2
      obtain ⟨s', t, e, ⟨hs', hq⟩, ht⟩ := h12 s hstk
      refine ⟨s', t, e, ⟨by omega, hs', ?_⟩, ht⟩
      rw [hq, hk n (by omega)])
    (fun n s hs => by
      obtain ⟨-, -, hv⟩ := hs
      have : s.var = (s.var.1, s.var.2) := rfl
      rw [this, hv, topIsBit_natSyms]
      simp)
    (fun s hs => by
      obtain ⟨-, -, hv⟩ := hs
      have : s.var = (s.var.1, s.var.2) := rfl
      rw [this, hv, topIsBit_natSyms]
      simp)
    N
  have hp := runs_peekTop (σ' := σ') k (B N)
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ := hp s hs
  obtain ⟨s2, t2, e2, ⟨-, hs2, -⟩, ht2⟩ := hloop s1 ⟨le_refl N, hs1, by rw [hv1, hk N le_rfl]⟩
  exact ⟨s2, t1 + t2, Eval.seq e1 e2, ⟨hs2, trivial⟩, by omega⟩

end Loop

/-! ## The composite layout -/

section Layout

variable {EP : Type}

/-- Embedding of a bridge part (`KLoc BrK Ek`) into the composite (`KLoc BrN (BrW ⊕ EP)`): named
stacks to named stacks, work stacks to the composite's private work stacks, the part's scratch
through `inj`. -/
def ιK {Ek : Type} (inj : Ek → EP) : KLoc BrK Ek → KLoc BrN (BrW ⊕ EP)
  | .inl (.inl n) => .inl n
  | .inl (.inr w) => .inr (.inl w)
  | .inr e => .inr (.inr (inj e))

theorem ιK_injective {Ek : Type} {inj : Ek → EP} (h : Function.Injective inj) :
    Function.Injective (ιK inj) := by
  rintro ((a | a) | a) ((b | b) | b) hab <;> simp_all [ιK, h.eq_iff]

/-- Embedding of the middle (`KLoc (Fin 2) Em`): stack `0` to the work array, stack `1` to `mpar`. -/
def ιM {Em : Type} (inj : Em → EP) : KLoc (Fin 2) Em → KLoc BrN (BrW ⊕ EP)
  | .inl i => if (i : ℕ) = 0 then .inr (.inl .arr) else .inl .mpar
  | .inr e => .inr (.inr (inj e))

theorem ιM_injective {Em : Type} {inj : Em → EP} (h : Function.Injective inj) :
    Function.Injective (ιM inj) := by
  rintro (a | a) (b | b) hab
  · simp only [ιM] at hab
    congr 1
    apply Fin.ext
    have ha := a.isLt
    have hb := b.isLt
    split_ifs at hab with h1 h2 h2 <;> simp_all <;> omega
  · simp only [ιM] at hab
    split_ifs at hab <;> simp at hab
  · simp only [ιM] at hab
    split_ifs at hab <;> simp at hab
  · simp_all [ιM, h.eq_iff]

/-- Embedding of a one-stack kernel (`Loc 1 m`, e.g. `W3_decNat`) on the counter `ax`, its `m`
scratch stacks through `inj`. -/
def ιD {m : ℕ} (inj : Fin m → EP) : Loc 1 m → KLoc BrN (BrW ⊕ EP)
  | .inl _ => .inr (.inl .ax)
  | .inr j => .inr (.inr (inj j))

theorem ιD_injective {m : ℕ} {inj : Fin m → EP} (h : Function.Injective inj) :
    Function.Injective (ιD inj) := by
  rintro (a | a) (b | b) hab
  · congr 1
    exact Subsingleton.elim a b
  · simp [ιD] at hab
  · simp [ιD] at hab
  · simp_all [ιD, h.eq_iff]

/-- Work-stack contents from three lists. -/
def wst (a x e : List Sym) : BrW → List Sym
  | .arr => a
  | .ax => x
  | .ex => e

/-- **Composite state**: interface stacks of `S` except `src := sr`, `dst := ds`; work stacks `W`;
scratch of `S`. -/
def mkB (S : KLoc BrN (BrW ⊕ EP) → List Sym) (W : BrW → List Sym) (sr ds : List Sym) :
    KLoc BrN (BrW ⊕ EP) → List Sym
  | .inl .src => sr
  | .inl .dst => ds
  | .inl .par => S (.inl .par)
  | .inl .mpar => S (.inl .mpar)
  | .inl .tapTab => S (.inl .tapTab)
  | .inl .solTab => S (.inl .solTab)
  | .inr (.inl w) => W w
  | .inr (.inr e) => S (.inr (.inr e))

variable [DecidableEq EP]

theorem mkB_update_arr (S : KLoc BrN (BrW ⊕ EP) → List Sym) (a x e sr ds v : List Sym) :
    Function.update (mkB S (wst a x e) sr ds) (.inr (.inl .arr)) v = mkB S (wst v x e) sr ds := by
  funext k
  rcases k with n | (w | e')
  · cases n <;> simp [mkB, Function.update]
  · cases w <;> simp [mkB, wst, Function.update]
  · simp [mkB, Function.update]

theorem mkB_update_ax (S : KLoc BrN (BrW ⊕ EP) → List Sym) (a x e sr ds v : List Sym) :
    Function.update (mkB S (wst a x e) sr ds) (.inr (.inl .ax)) v = mkB S (wst a v e) sr ds := by
  funext k
  rcases k with n | (w | e')
  · cases n <;> simp [mkB, Function.update]
  · cases w <;> simp [mkB, wst, Function.update]
  · simp [mkB, Function.update]

omit [DecidableEq EP] in
/-- Transport of a part's work-stack update. -/
theorem update_kW_comp {Ek : Type} [DecidableEq Ek] (inj : Ek → EP)
    (S : KLoc BrN (BrW ⊕ EP) → List Sym) (W : BrW → List Sym) (sr ds : List Sym) (w : BrW)
    (v : List Sym) :
    Function.update (mkB S W sr ds ∘ ιK inj) (kW w) v =
      mkB S (Function.update W w v) sr ds ∘ ιK inj := by
  funext k
  rcases k with (n | w') | e
  · cases n <;> simp [mkB, ιK, Function.update]
  · by_cases h : w' = w
    · subst h
      simp [mkB, ιK, Function.update]
    · cases w <;> cases w' <;> simp_all [mkB, ιK, Function.update]
  · simp [mkB, ιK, Function.update]

omit [DecidableEq EP] in
theorem update_src_comp {Ek : Type} [DecidableEq Ek] (inj : Ek → EP)
    (S : KLoc BrN (BrW ⊕ EP) → List Sym) (W : BrW → List Sym) (sr ds v : List Sym) :
    Function.update (mkB S W sr ds ∘ ιK inj) (kN .src) v = mkB S W v ds ∘ ιK inj := by
  funext k
  rcases k with (n | w') | e
  · cases n <;> simp [mkB, ιK, Function.update]
  · simp [mkB, ιK, Function.update]
  · simp [mkB, ιK, Function.update]

omit [DecidableEq EP] in
theorem update_dst_comp {Ek : Type} [DecidableEq Ek] (inj : Ek → EP)
    (S : KLoc BrN (BrW ⊕ EP) → List Sym) (W : BrW → List Sym) (sr ds v : List Sym) :
    Function.update (mkB S W sr ds ∘ ιK inj) (kN .dst) v = mkB S W sr v ∘ ιK inj := by
  funext k
  rcases k with (n | w') | e
  · cases n <;> simp [mkB, ιK, Function.update]
  · simp [mkB, ιK, Function.update]
  · simp [mkB, ιK, Function.update]

/-- **Calling a bridge part inside the composite.** -/
theorem runs_partK {Ek Rk σ : Type} [DecidableEq Ek] {inj : Ek → EP}
    (hinj : Function.Injective inj) (l : Lens σ Rk) {P : Prog (KLoc BrK Ek) (fun _ => Sym) Rk}
    {S : KLoc BrN (BrW ⊕ EP) → List Sym} {W W' : BrW → List Sym} {sr sr' ds ds' : List Sym}
    {Q : Rk → Prop} {T : ℕ}
    (h : Runs P (mkB S W sr ds ∘ ιK inj) (mkB S W' sr' ds' ∘ ιK inj) Q T) :
    Runs (callInj (ιK inj) l P) (mkB S W sr ds) (mkB S W' sr' ds') (fun _ => True) T := by
  refine runs_callInj (ιK_injective hinj) l h ?_
  rintro (n | (w | e)) hk
  · exact absurd rfl (hk (.inl (.inl n)))
  · exact absurd rfl (hk (.inl (.inr w)))
  · rfl

/-- **Calling the middle inside the composite** (in place on the work array). -/
theorem runs_partM {Em Rm σ : Type} [DecidableEq Em] {inj : Em → EP}
    (hinj : Function.Injective inj) (l : Lens σ Rm) {P : Prog (KLoc (Fin 2) Em) (fun _ => Sym) Rm}
    {S : KLoc BrN (BrW ⊕ EP) → List Sym} {a a' x e sr ds : List Sym} {Q : Rm → Prop} {T : ℕ}
    (h : Runs P (mkB S (wst a x e) sr ds ∘ ιM inj) (mkB S (wst a' x e) sr ds ∘ ιM inj) Q T) :
    Runs (callInj (ιM inj) l P) (mkB S (wst a x e) sr ds) (mkB S (wst a' x e) sr ds)
      (fun _ => True) T := by
  refine runs_callInj (ιM_injective hinj) l h ?_
  rintro (n | (w | e')) hk
  · cases n <;> rfl
  · cases w
    · exact absurd (by simp [ιM]) (hk (.inl 0))
    · rfl
    · rfl
  · rfl

/-- **Calling a counter kernel inside the composite** (in place on `ax`). -/
theorem runs_partD {m : ℕ} {Rd σ : Type} {inj : Fin m → EP} (hinj : Function.Injective inj)
    (l : Lens σ Rd) {P : Prog (Loc 1 m) (fun _ => Sym) Rd}
    {S : KLoc BrN (BrW ⊕ EP) → List Sym} {a x x' e sr ds : List Sym} {Q : Rd → Prop} {T : ℕ}
    (h : Runs P (mkB S (wst a x e) sr ds ∘ ιD inj) (mkB S (wst a x' e) sr ds ∘ ιD inj) Q T) :
    Runs (callInj (ιD inj) l P) (mkB S (wst a x e) sr ds) (mkB S (wst a x' e) sr ds)
      (fun _ => True) T := by
  refine runs_callInj (ιD_injective hinj) l h ?_
  rintro (n | (w | e')) hk
  · cases n <;> rfl
  · cases w
    · rfl
    · exact absurd rfl (hk (.inl 0))
    · rfl
  · rfl

end Layout

end SubNLogN.Machine.BridgeRed
