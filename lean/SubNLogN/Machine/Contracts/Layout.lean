/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WP.W9comp.Kit

/-!
# `SubNLogN.Machine` contracts, K0.1 (`Contracts/Layout.lean`): extended layout, contract shapes, embeddings

**Scope (honest summary).** This file contains layout conventions, two contract *shapes*
(`XContract`, `KContract`) and generic embedding lemmas. It contains no algorithm, and it does not
assert that any contract holds. Proved (no `sorry`): `embX_injective`, `closed_callInj`,
`runs_callInj`, `closed_callX`, `runs_callX`, `upd_comp_embX`, `EClean.update_inl`.

## Conventions
* **Extended Stage-5 layout.** `XLoc m E = BLoc m ⊕ E`. `.inl` holds W9's named layout-B stacks
  `LB` plus `m` scratch stacks (`Contracts/W9/Common.lean:52,57`); `.inr e` holds extra stacks
  indexed by a finite type `E`. This matches the Stage-5 slot `BLoc m9 ⊕ E` of
  `SubNLogN/S5/TopExtended.lean` (`[Fintype E] [DecidableEq E]`; there the `E` stacks start and
  end empty at the Stage-5 boundary).
* **Two scratch conventions for `E`.** The default is *restored*: specs use `Runs` (exact final
  stacks), so every `E` stack the spec does not mention ends with its arbitrary initial content,
  like `Fin m` scratch in `MContract`. The alternative is *clean*: the spec also assumes `EClean S`
  (all `E` stacks empty at entry), and exact final stacks then force them empty at exit. Kernels
  that reuse the `WP.Top` stage lemmas, which assume empty stacks, need the clean convention.
* **Size of `E`.** `E` is fixed but may be astronomically large. Appendix A reserves
  `W_b ≈ 1.8·10^20` role tapes plus a parking and a descriptor stack
  (Proposition A.7, `prop:transfer11`). `FinTM2` allows any `Fintype` of
  stacks. Proofs must never enumerate `E` or `decide` over it.
* **Kernel layout.** `KLoc N E = N ⊕ E`: named interface stacks `N` plus a private finite scratch
  family `E` chosen by the kernel. `KContract` generalizes `MContract`
  (`Contracts/Machine/Common.lean:85`; there `N = Fin n` and scratch is `Fin m`, `m ≤ maxScratch`).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9

/-! ## Layouts and contract shapes -/

/-- **[CONTRACT] Extended Stage-5 local stacks** (paper: the fixed role, parking and descriptor
tapes of Proposition A.7, `prop:transfer11`; machine model in Section 3.2, `sec:prelim-model`). `XLoc m E = BLoc m ⊕ E`:
`.inl` is W9's layout `BLoc m` (named stacks `LB`, `m` scratch stacks), `.inr e` the extra stacks. -/
abbrev XLoc (m : ℕ) (E : Type) : Type := BLoc m ⊕ E

/-- All extra stacks of an extended state are empty (the *clean* convention). -/
def EClean {m : ℕ} {E : Type} (S : XLoc m E → List Sym) : Prop := ∀ e : E, S (.inr e) = []

/-- **[CONTRACT] Shape of an extended-layout contract** (`XContract Par spec`). There is one cost
constant `C`. For each compile-time parameter `p` there are a scratch count `m ≤ w9Scratch`, a
finite type `E` of extra stacks (with `Fintype` and `DecidableEq` instances), a finite nonempty
register type `R`, and a closed program `P` on `XLoc m E` satisfying `spec p m E R C P`.
Like `BContract` (`Contracts/W9/Common.lean:70`), specs use `Runs` with exact final stacks.
The bound `m ≤ w9Scratch` keeps the `.inl` part embeddable in the Stage-5 slot, where `ι9` needs
`m9 ≤ 64` (`WP/Top/Embed.lean:233`); any further scratch lives in `E`. -/
def XContract (Par : Type)
    (spec : Par → (m : ℕ) → (E : Type) → [Fintype E] → [DecidableEq E] → (R : Type) → ℕ →
      Prog (XLoc m E) (fun _ => Sym) R → Prop) : Prop :=
  ∃ C : ℕ, ∀ p : Par, ∃ (m : ℕ) (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R : Type)
    (P : Prog (XLoc m E) (fun _ => Sym) R),
    m ≤ w9Scratch ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧ spec p m E R C P

/-- **[CONTRACT] Kernel local stacks** `KLoc N E = N ⊕ E`: named interface stacks `N` and a
private finite scratch family `E`. -/
abbrev KLoc (N E : Type) : Type := N ⊕ E

/-- All private scratch stacks of a kernel state are empty (the *clean* convention). -/
def KClean {N E : Type} (S : KLoc N E → List Sym) : Prop := ∀ e : E, S (.inr e) = []

/-- **[CONTRACT] Shape of a kernel contract with named stacks `N`** (`KContract N Par spec`).
There is one cost constant `C`. For each compile-time parameter `p` the kernel chooses a finite
scratch type `E` (with `Fintype` and `DecidableEq` instances), a finite nonempty register type `R`,
and a closed program on `KLoc N E` satisfying `spec p E R C P`. Unlike `MContract`, there is no
a-priori cap on the scratch count, so kernels may use, for example, `q²` digit streams or `W` role
streams internally. `E` depends only on `p`, never on the data. -/
def KContract (N : Type) (Par : Type)
    (spec : Par → (E : Type) → [Fintype E] → [DecidableEq E] → (R : Type) → ℕ →
      Prog (KLoc N E) (fun _ => Sym) R → Prop) : Prop :=
  ∃ C : ℕ, ∀ p : Par, ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (R : Type)
    (P : Prog (KLoc N E) (fun _ => Sym) R), Finite R ∧ Nonempty R ∧ P.Closed ∧ spec p E R C P

theorem EClean.update_inl {m : ℕ} {E : Type} [DecidableEq E] {S : XLoc m E → List Sym}
    (h : EClean S) (k : BLoc m) (v : List Sym) : EClean (Function.update S (.inl k) v) := by
  intro e
  rw [Function.update_of_ne (by simp)]
  exact h e

/-! ## Embedding a component along an injective stack map -/

section CallInj

variable {L K σ R : Type}

/-- Run a component `P` on an injective sub-layout `ι : L → K`, with its registers reached through
the lens `l`. This generalizes `WP.W9comp.callB` (`WP/W9comp/Kit.lean:50`), which is the case
`ι = emb h`. -/
def callInj (ι : L → K) (l : Lens σ R) (P : Prog L (fun _ => Sym) R) : Prog K (fun _ => Sym) σ :=
  (P.mapStk ι).liftRegs l

theorem closed_callInj (ι : L → K) (l : Lens σ R) {P : Prog L (fun _ => Sym) R} (hP : P.Closed) :
    (callInj ι l P).Closed :=
  WP.W9comp.closed_liftRegs l ((WP.W9comp.freeBelow_mapStk ι P 0).2 hP)

/-- **A component's `Runs` along an injective embedding (`runs_callInj`).** Suppose `P` runs from
the restriction `B ∘ ι` to `B' ∘ ι`, and the big final stacks `B'` agree with `B` outside the image
of `ι`. Then the embedded program runs from `B` to `B'`, with the same cost. This generalizes
`WP.W9comp.runs_callB` (`WP/W9comp/Kit.lean:59`). -/
theorem runs_callInj [DecidableEq L] [DecidableEq K] {ι : L → K} (hι : Function.Injective ι)
    (l : Lens σ R) {P : Prog L (fun _ => Sym) R} {B B' : K → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ ι) (B' ∘ ι) Q T) (hout : ∀ k, (∀ x, ι x ≠ k) → B' k = B k) :
    Runs (callInj ι l P) B B' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = B at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := hP ⟨l.get v, stk ∘ ι⟩ rfl
  obtain ⟨T', h1, h2, e'⟩ := e.mapStk hι stk (fun _ => rfl)
  have hT' : T' = B' := by
    funext k
    by_cases hk : ∃ x, ι x = k
    · obtain ⟨x, rfl⟩ := hk
      exact (h1 x).trans (congrFun hs' x)
    · simp only [not_exists] at hk
      rw [h2 _ hk, hout k hk]
  subst hT'
  exact ⟨⟨l.set v s'.var, T'⟩, t, Eval.liftRegs l e' v rfl, ⟨rfl, trivial⟩, ht⟩

end CallInj

/-! ## `callX`: a `BLoc m` kernel inside the extended layout `XLoc m' E` -/

section CallX

/-- Stack embedding `BLoc m → XLoc m' E`, namely `WP.W9comp.emb h` followed by `Sum.inl`. Named
stacks map to named stacks, scratch `j` to scratch `j`, and no `E` stack is in the image. -/
def embX {m m' : ℕ} (E : Type) (h : m ≤ m') (k : BLoc m) : XLoc m' E :=
  Sum.inl (WP.W9comp.emb h k)

theorem embX_injective {m m' : ℕ} (E : Type) (h : m ≤ m') : Function.Injective (embX E h) :=
  Sum.inl_injective.comp (WP.W9comp.emb_injective h)

/-- **[CONTRACT] `callX`.** Run a `BLoc m` program (for example a `BContract` kernel) inside
the extended layout `XLoc m' E`, with `m ≤ m'`. Registers are reached through a lens and the `E`
stacks are never addressed. -/
def callX {m m' : ℕ} {σ R : Type} (E : Type) (h : m ≤ m') (l : Lens σ R)
    (P : Prog (BLoc m) (fun _ => Sym) R) : Prog (XLoc m' E) (fun _ => Sym) σ :=
  callInj (embX E h) l P

theorem closed_callX {m m' : ℕ} {σ R : Type} (E : Type) (h : m ≤ m') (l : Lens σ R)
    {P : Prog (BLoc m) (fun _ => Sym) R} (hP : P.Closed) : (callX E h l P).Closed :=
  closed_callInj _ l hP

/-- **`runs_callX`** generalizes `WP.W9comp.runs_callB` to the extended layout. A `BLoc m` kernel's
`Runs` from `B ∘ embX` to `B' ∘ embX` lifts to `Runs` of `callX` from `B` to `B'`, with the same
cost. The side conditions are that the big final stacks agree with the initial ones on every
scratch stack `.inl (.inr j)` and on every extra stack `.inr e`, so the `E` stacks are untouched. -/
theorem runs_callX {m m' : ℕ} {E σ R : Type} [DecidableEq E] (h : m ≤ m') (l : Lens σ R)
    {P : Prog (BLoc m) (fun _ => Sym) R} {B B' : XLoc m' E → List Sym} {Q : R → Prop} {T : ℕ}
    (hP : Runs P (B ∘ embX E h) (B' ∘ embX E h) Q T)
    (hscr : ∀ j : Fin m', B' (.inl (.inr j)) = B (.inl (.inr j)))
    (hE : ∀ e : E, B' (.inr e) = B (.inr e)) :
    Runs (callX E h l P) B B' (fun _ => True) T := by
  refine runs_callInj (embX_injective E h) l hP ?_
  rintro ((k | j) | e) hk
  · exact absurd rfl (hk (.inl k))
  · exact hscr j
  · exact hE e

/-- `Function.update` on a named stack commutes with `embX` (the analogue of
`WP.W9comp.upd_comp_emb`). -/
theorem upd_comp_embX {m m' : ℕ} {E : Type} [DecidableEq E] (h : m ≤ m')
    (B : XLoc m' E → List Sym) (k : LB) (v : List Sym) :
    Function.update (B ∘ embX E h) (.inl k) v =
      (Function.update B (.inl (.inl k)) v) ∘ embX E h :=
  (Function.update_comp_eq_of_injective B (embX_injective E h) (.inl k) v).symm

end CallX

/-! ## Smoke tests: both shapes are inhabited by the trivial (`skip`) kernel -/

/-- Smoke test: `XContract` elaborates with its instance binders and is satisfiable by `skip`
(`E = Empty`). -/
example : XContract Unit fun _ m E _ _ _ C P =>
    ∀ S : XLoc m E → List Sym, Runs P S S (fun _ => True) C := by
  refine ⟨1, fun _ => ⟨0, Empty, inferInstance, inferInstance, Unit, TMFw.Lib.skip,
    Nat.zero_le _, inferInstance, inferInstance, ?_, ?_⟩⟩
  · simp [Prog.Closed, Prog.FreeBelow, TMFw.Lib.skip]
  · intro S
    exact (Triple.load (ρ := []) id (fun s => s.stk = S ∧ True)).pre (fun _ hs => ⟨hs, trivial⟩)

/-- Smoke test: the same for `KContract`. -/
example : KContract Unit Unit fun _ E _ _ _ C P =>
    ∀ S : KLoc Unit E → List Sym, Runs P S S (fun _ => True) C := by
  refine ⟨1, fun _ => ⟨Empty, inferInstance, inferInstance, Unit, TMFw.Lib.skip,
    inferInstance, inferInstance, ?_, ?_⟩⟩
  · simp [Prog.Closed, Prog.FreeBelow, TMFw.Lib.skip]
  · intro S
    exact (Triple.load (ρ := []) id (fun s => s.stk = S ∧ True)).pre (fun _ hs => ⟨hs, trivial⟩)

end SubNLogN.Machine
