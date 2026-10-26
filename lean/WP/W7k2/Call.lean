import Contracts.W7.Tables

/-!
# WP.W7k2.Call — calling contract programs inside a host program

The composition layer of W7k2. A host program runs over the local stacks `Loc a b` of its own
contract and calls contract programs (`MContract` witnesses) on chosen host stacks:

* `Inst n cap O` packages one witness of an `MContract _ n cap O _` (one compile-time parameter):
  scratch count `m ≤ cap`, register type `R`, observation, closed program. `exists_inst` extracts
  witnesses from a contract.
* `callMap dflt named` sends the callee's named stack `.inl i` to `named[i]` and its scratch stack
  `.inr j` to the `j`-th host stack **not** in `named` (`freeLoc`). Scratch content is arbitrary and
  restored by every contract, so any host stack (inputs, outputs, live values) can serve as callee
  scratch; only the named stacks of one call must be distinct (`callMap_injective`).
* `callI I named dflt l` is the embedded program (stacks renamed, registers lifted through `l`).
* `HT ρ B p B' T` is the exact-stacks triple used throughout: from stacks `B` (any registers) the
  program reaches stacks `B'` within `T` steps.
* `HT.callI_upd` / `HT.callI_upd2`: a contract whose final stacks update one / two named stacks gives
  the same update on the host stacks. `HT.callI_test`: a contract with unchanged stacks and a
  register result, followed by a branch on it.
* Raw operations: `pushS` (push a constant symbol), `popS` (drop the top symbol), and a branch on a
  popped symbol (`HT.popBranch`).
-/

namespace WP.W7k2

open TMFw TMFw.Contracts

/-! ## Closedness is preserved by stack renaming and register lifting -/

section Closed

variable {K K' A σ τ : Type}

theorem freeBelow_mapStk (ι : K → K') :
    ∀ (p : Prog K (fun _ => A) σ) (d : ℕ), p.FreeBelow d → (p.mapStk ι).FreeBelow d
  | .push _ _, _, _ => trivial
  | .peek _ _, _, _ => trivial
  | .pop _ _, _, _ => trivial
  | .load _, _, _ => trivial
  | .seq p q, d, h => ⟨freeBelow_mapStk ι p d h.1, freeBelow_mapStk ι q d h.2⟩
  | .ite _ p q, d, h => ⟨freeBelow_mapStk ι p d h.1, freeBelow_mapStk ι q d h.2⟩
  | .loop _ p, d, h => freeBelow_mapStk ι p d h
  | .fix b, d, h => freeBelow_mapStk ι b (d + 1) h
  | .recur _, _, h => h

theorem freeBelow_liftRegs {Γ : K → Type} (l : Lens σ τ) :
    ∀ (p : Prog K Γ τ) (d : ℕ), p.FreeBelow d → (p.liftRegs l).FreeBelow d
  | .push _ _, _, _ => trivial
  | .peek _ _, _, _ => trivial
  | .pop _ _, _, _ => trivial
  | .load _, _, _ => trivial
  | .seq p q, d, h => ⟨freeBelow_liftRegs l p d h.1, freeBelow_liftRegs l q d h.2⟩
  | .ite _ p q, d, h => ⟨freeBelow_liftRegs l p d h.1, freeBelow_liftRegs l q d h.2⟩
  | .loop _ p, d, h => freeBelow_liftRegs l p d h
  | .fix b, d, h => freeBelow_liftRegs l b (d + 1) h
  | .recur _, _, h => h

end Closed

/-! ## Contract instances -/

/-- One witness of an `MContract _ n cap O _` (for one compile-time parameter). -/
structure Inst (n cap : ℕ) (O : Type) : Type 1 where
  /-- number of scratch stacks -/
  m : ℕ
  /-- register type -/
  R : Type
  /-- observation of the final registers -/
  obs : R → O
  /-- the program -/
  P : Prog (Loc n m) (fun _ => Sym) R
  hm : m ≤ cap
  fin : Finite R
  ne : Nonempty R
  cl : P.Closed

/-- Extract instances from a contract: one cost constant, one instance per parameter. -/
theorem exists_inst {Par : Type} {n cap : ℕ} {O : Type}
    {spec : Par → (m : ℕ) → (R : Type) → ℕ → (R → O) → Prog (Loc n m) (fun _ => Sym) R → Prop}
    (h : MContract Par n cap O spec) :
    ∃ C : ℕ, ∀ p : Par, ∃ I : Inst n cap O, spec p I.m I.R C I.obs I.P := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun p => ?_⟩
  obtain ⟨m, R, obs, P, hm, hfin, hne, hcl, hs⟩ := hC p
  exact ⟨⟨m, R, obs, P, hm, hfin, hne, hcl⟩, hs⟩

/-! ## Free host stacks and the call map -/

/-- All stacks of `Loc a b`, without repetition. -/
def allLoc (a b : ℕ) : List (Loc a b) := (List.finRange (a + b)).map finSumFinEquiv.symm

theorem nodup_allLoc (a b : ℕ) : (allLoc a b).Nodup :=
  (List.nodup_finRange _).map finSumFinEquiv.symm.injective

theorem mem_allLoc {a b : ℕ} (x : Loc a b) : x ∈ allLoc a b :=
  List.mem_map.mpr ⟨finSumFinEquiv x, List.mem_finRange _, finSumFinEquiv.symm_apply_apply x⟩

theorem length_allLoc (a b : ℕ) : (allLoc a b).length = a + b := by
  simp [allLoc]

/-- Is `x` among `named`? -/
def inNamed {a b : ℕ} (named : List (Loc a b)) (x : Loc a b) : Bool :=
  named.any (fun y => decide (y = x))

theorem inNamed_iff {a b : ℕ} {named : List (Loc a b)} {x : Loc a b} :
    inNamed named x = true ↔ x ∈ named := by
  unfold inNamed
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [decide_eq_true_iff] at h
    exact h ▸ hy
  · intro h
    exact ⟨x, h, decide_eq_true rfl⟩

/-- Host stacks not in `named`. -/
def freeLoc {a b : ℕ} (named : List (Loc a b)) : List (Loc a b) :=
  (allLoc a b).filter (fun x => !inNamed named x)

theorem mem_freeLoc {a b : ℕ} {named : List (Loc a b)} {x : Loc a b} :
    x ∈ freeLoc named ↔ x ∉ named := by
  unfold freeLoc
  rw [List.mem_filter]
  constructor
  · rintro ⟨-, h⟩ hx
    rw [inNamed_iff.mpr hx] at h
    exact absurd h (by decide)
  · intro hx
    refine ⟨mem_allLoc x, ?_⟩
    cases h : inNamed named x
    · rfl
    · exact absurd (inNamed_iff.mp h) hx

theorem nodup_freeLoc {a b : ℕ} (named : List (Loc a b)) : (freeLoc named).Nodup :=
  (nodup_allLoc a b).filter _

theorem length_freeLoc {a b : ℕ} (named : List (Loc a b)) :
    a + b ≤ (freeLoc named).length + named.length := by
  have h1 := List.length_eq_length_filter_add (l := allLoc a b) (fun x => !inNamed named x)
  rw [length_allLoc] at h1
  have h2 : ((allLoc a b).filter (fun x => !!inNamed named x)).length ≤ named.length := by
    refine (((nodup_allLoc a b).filter _).subperm (fun x hx => ?_)).length_le
    have h := (List.mem_filter.mp hx).2
    rw [Bool.not_not] at h
    exact inNamed_iff.mp h
  unfold freeLoc
  omega

/-- The stack map of one call: named stacks to `named`, scratch stacks to free host stacks. -/
def callMap {a b n m : ℕ} (dflt : Loc a b) (named : List (Loc a b)) : Loc n m → Loc a b
  | .inl i => named.getD i dflt
  | .inr j => (freeLoc named).getD j dflt

theorem callMap_inl {a b n m : ℕ} (dflt : Loc a b) (named : List (Loc a b)) (i : Fin n) :
    callMap (m := m) dflt named (.inl i) = named.getD i dflt := rfl

theorem getD_mem_of_lt {α : Type} {l : List α} {i : ℕ} (d : α) (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem getD_inj_of_nodup {α : Type} {l : List α} (hl : l.Nodup) {i j : ℕ} (d : α)
    (hi : i < l.length) (hj : j < l.length) (h : l.getD i d = l.getD j d) : i = j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h
  exact (hl.getElem_inj_iff).mp h

theorem callMap_injective {a b n m : ℕ} (dflt : Loc a b) (named : List (Loc a b))
    (hnd : named.Nodup) (hn : named.length = n) (hm : m + n ≤ a + b) :
    Function.Injective (callMap (n := n) (m := m) dflt named) := by
  have hfl := length_freeLoc named
  have hfree : ∀ j : Fin m, j.1 < (freeLoc named).length := fun j => by have := j.2; omega
  have hnamed : ∀ i : Fin n, i.1 < named.length := fun i => by have := i.2; omega
  rintro (i | j) (i' | j') h <;> simp only [callMap] at h
  · exact congrArg Sum.inl (Fin.ext (getD_inj_of_nodup hnd dflt (hnamed i) (hnamed i') h))
  · exfalso
    have h1 := getD_mem_of_lt dflt (hnamed i)
    have h2 := getD_mem_of_lt dflt (hfree j')
    rw [h] at h1
    exact (mem_freeLoc.mp h2) h1
  · exfalso
    have h1 := getD_mem_of_lt dflt (hfree j)
    have h2 := getD_mem_of_lt dflt (hnamed i')
    rw [h] at h1
    exact (mem_freeLoc.mp h1) h2
  · exact congrArg Sum.inr
      (Fin.ext (getD_inj_of_nodup (nodup_freeLoc named) dflt (hfree j) (hfree j') h))

/-! ## Embedded calls -/

variable {a b : ℕ} {σ : Type}

/-- A contract program called on host stacks `named` (scratch on free host stacks), registers
lifted through `l`. -/
def callI {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b)) (dflt : Loc a b)
    (l : Lens σ I.R) : Prog (Loc a b) (fun _ => Sym) σ :=
  (I.P.mapStk (callMap dflt named)).liftRegs l

theorem callI_closed {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b))
    (dflt : Loc a b) (l : Lens σ I.R) : (callI I named dflt l).Closed :=
  freeBelow_liftRegs l _ 0 (freeBelow_mapStk _ I.P 0 I.cl)

/-- **Exact-stacks triple**: from stacks `B` (any registers), reach stacks `B'` within `T`. -/
def HT (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) (B : Loc a b → List Sym)
    (p : Prog (Loc a b) (fun _ => Sym) σ) (B' : Loc a b → List Sym) (T : ℕ) : Prop :=
  Triple ρ (fun s => s.stk = B) p (fun s => s.stk = B') T

namespace HT

variable {ρ : List (Prog (Loc a b) (fun _ => Sym) σ)} {B B₁ B₂ B' : Loc a b → List Sym}
  {p q : Prog (Loc a b) (fun _ => Sym) σ} {T T₁ T₂ : ℕ}

theorem seq (h₁ : HT ρ B p B₁ T₁) (h₂ : HT ρ B₁ q B₂ T₂) : HT ρ B (p.seq q) B₂ (T₁ + T₂) :=
  Triple.seq h₁ h₂

theorem mono (h : HT ρ B p B' T₁) (hT : T₁ ≤ T₂) : HT ρ B p B' T₂ := Triple.cost_mono h hT

theorem of_eq (h : HT ρ B p B₁ T₁) (hB : B₁ = B₂) (hT : T₁ ≤ T₂) : HT ρ B p B₂ T₂ := by
  subst hB
  exact h.mono hT

/-- The kernel contracts' `Runs` is an `HT` with a trivial register condition. -/
theorem runs {R : Type} {P : Prog (Loc a b) (fun _ => Sym) R} {S S' : Loc a b → List Sym} {T : ℕ}
    (h : HT [] S P S' T) : Runs P S S' (fun _ => True) T :=
  Triple.post h (fun _ hs => ⟨hs, trivial⟩)

end HT

/-- **Call rule (general form).** -/
theorem callI_spec {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b))
    (dflt : Loc a b) (hnd : named.Nodup) (hn : named.length = n) (hcap : cap + n ≤ a + b)
    (l : Lens σ I.R) (B : Loc a b → List Sym) {S' : Loc n I.m → List Sym} {Q : I.R → Prop}
    {T : ℕ} (h : Runs I.P (fun x => B (callMap dflt named x)) S' Q T)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    Triple ρ (fun s => s.stk = B) (callI I named dflt l)
      (fun s => (∀ x : Loc n I.m, s.stk (callMap dflt named x) = S' x) ∧
        (∀ g, (∀ x : Loc n I.m, callMap dflt named x ≠ g) → s.stk g = B g) ∧ Q (l.get s.var)) T := by
  have hinj := callMap_injective (m := I.m) dflt named hnd hn (by have := I.hm; omega)
  have h1 := Runs.embed hinj h B (fun _ => rfl)
  have h2 := Triple.liftRegs l h1 (fun _ => True) (fun _ _ _ => trivial)
  have h3 := Triple.env_irrel h2 (by
    show ((I.P.mapStk (callMap dflt named)).liftRegs l).FreeBelow 0
    exact freeBelow_liftRegs l _ 0 (freeBelow_mapStk _ I.P 0 I.cl)) ρ
  refine Triple.conseq h3 (fun s hs => ⟨hs, trivial⟩) (fun s hs => ?_) le_rfl
  obtain ⟨⟨ha, hb, hq⟩, -⟩ := hs
  exact ⟨ha, hb, hq⟩

/-- **Call rule, one updated stack.** -/
theorem HT.callI_upd {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b))
    (dflt : Loc a b) (hnd : named.Nodup) (hn : named.length = n) (hcap : cap + n ≤ a + b)
    (l : Lens σ I.R) (B : Loc a b → List Sym) (k : Loc n I.m) (v : List Sym) {Q : I.R → Prop}
    {T : ℕ}
    (h : Runs I.P (fun x => B (callMap dflt named x))
      (Function.update (fun x => B (callMap dflt named x)) k v) Q T)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I named dflt l) (Function.update B (callMap dflt named k) v) T := by
  have hinj := callMap_injective (m := I.m) dflt named hnd hn (by have := I.hm; omega)
  refine Triple.post (callI_spec I named dflt hnd hn hcap l B h ρ) (fun s hs => ?_)
  obtain ⟨ha, hb, -⟩ := hs
  funext g
  by_cases hg : ∃ x : Loc n I.m, callMap dflt named x = g
  · obtain ⟨x, rfl⟩ := hg
    rw [ha x]
    by_cases hx : x = k
    · subst hx
      simp
    · rw [Function.update_of_ne hx, Function.update_of_ne (hinj.ne hx)]
  · push_neg at hg
    rw [hb g hg, Function.update_of_ne (fun e => hg k e.symm)]

/-- **Call rule, two updated stacks** (`divMod`, `splitAt`, `concatAt`). -/
theorem HT.callI_upd2 {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b))
    (dflt : Loc a b) (hnd : named.Nodup) (hn : named.length = n) (hcap : cap + n ≤ a + b)
    (l : Lens σ I.R) (B : Loc a b → List Sym) (k₁ k₂ : Loc n I.m) (v₁ v₂ : List Sym)
    {Q : I.R → Prop} {T : ℕ}
    (h : Runs I.P (fun x => B (callMap dflt named x))
      (Function.update (Function.update (fun x => B (callMap dflt named x)) k₁ v₁) k₂ v₂) Q T)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I named dflt l)
      (Function.update (Function.update B (callMap dflt named k₁) v₁) (callMap dflt named k₂) v₂)
      T := by
  have hinj := callMap_injective (m := I.m) dflt named hnd hn (by have := I.hm; omega)
  refine Triple.post (callI_spec I named dflt hnd hn hcap l B h ρ) (fun s hs => ?_)
  obtain ⟨ha, hb, -⟩ := hs
  funext g
  by_cases hg : ∃ x : Loc n I.m, callMap dflt named x = g
  · obtain ⟨x, rfl⟩ := hg
    rw [ha x]
    by_cases hx2 : x = k₂
    · subst hx2
      simp
    · rw [Function.update_of_ne hx2, Function.update_of_ne (hinj.ne hx2)]
      by_cases hx1 : x = k₁
      · subst hx1
        simp
      · rw [Function.update_of_ne hx1, Function.update_of_ne (hinj.ne hx1)]
  · push_neg at hg
    rw [hb g hg, Function.update_of_ne (fun e => hg k₂ e.symm),
      Function.update_of_ne (fun e => hg k₁ e.symm)]

/-- **Test call then branch.** A contract that leaves the stacks unchanged and reports `b0` through
`obs`, followed by `ite` on the observation. -/
theorem HT.callI_test {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b))
    (dflt : Loc a b) (hnd : named.Nodup) (hn : named.length = n) (hcap : cap + n ≤ a + b)
    (l : Lens σ I.R) (B B' : Loc a b → List Sym) (f : O → Bool) (o : O) {T T₁ T₂ : ℕ}
    (h : Runs I.P (fun x => B (callMap dflt named x)) (fun x => B (callMap dflt named x))
      (fun r => I.obs r = o) T)
    (p q : Prog (Loc a b) (fun _ => Sym) σ) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ))
    (hp : f o = true → HT ρ B p B' T₁) (hq : f o = false → HT ρ B q B' T₂) :
    HT ρ B ((callI I named dflt l).seq (.ite (fun v => f (I.obs (l.get v))) p q)) B'
      (T + (max T₁ T₂ + 1)) := by
  have hc := callI_spec I named dflt hnd hn hcap l B h ρ
  have hc' : Triple ρ (fun s => s.stk = B) (callI I named dflt l)
      (fun s => s.stk = B ∧ I.obs (l.get s.var) = o) T := by
    refine Triple.post hc (fun s hs => ?_)
    obtain ⟨ha, hb, hq'⟩ := hs
    refine ⟨?_, hq'⟩
    funext g
    by_cases hg : ∃ x : Loc n I.m, callMap dflt named x = g
    · obtain ⟨x, rfl⟩ := hg
      exact ha x
    · push_neg at hg
      exact hb g hg
  refine Triple.seq hc' (Triple.ite ?_ ?_)
  · rintro s ⟨⟨hsB, hso⟩, hc⟩
    have hfo : f o = true := by rw [← hso]; exact hc
    exact (hp hfo).mono (le_max_left _ _) s hsB
  · rintro s ⟨⟨hsB, hso⟩, hc⟩
    have hfo : f o = false := by rw [← hso]; exact hc
    exact (hq hfo).mono (le_max_right _ _) s hsB

/-! ## Raw operations -/

/-- Push a constant symbol. -/
def pushS (k : Loc a b) (x : Sym) : Prog (Loc a b) (fun _ => Sym) σ := .push k (fun _ => x)

/-- Pop and discard the top symbol. -/
def popS (k : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ := .pop k (fun v _ => v)

/-- Pop the top symbol into the symbol register `lS`. -/
def popR' (lS : Lens σ (Option Sym)) (k : Loc a b) : Prog (Loc a b) (fun _ => Sym) σ :=
  .pop k (fun v o => lS.set v o)

theorem HT.pushS (k : Loc a b) (x : Sym) (B : Loc a b → List Sym)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (WP.W7k2.pushS k x) (Function.update B k (x :: B k)) 1 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  exact ⟨_, 1, Eval.push ρ k (fun _ => x) v S, rfl, le_rfl⟩

theorem HT.popS (k : Loc a b) (B : Loc a b → List Sym) (x : Sym) (rest : List Sym)
    (hk : B k = x :: rest) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (WP.W7k2.popS k) (Function.update B k rest) 1 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  refine ⟨_, 1, Eval.pop ρ k (fun v _ => v) v S, ?_, le_rfl⟩
  show Function.update S k (S k).tail = Function.update S k rest
  rw [hk]
  rfl

/-- **Pop, then branch on the popped symbol.** -/
theorem HT.popBranch (lS : Lens σ (Option Sym)) (k : Loc a b) (B B' : Loc a b → List Sym)
    (x : Sym) (rest : List Sym) (hk : B k = x :: rest) (f : Option Sym → Bool)
    (p q : Prog (Loc a b) (fun _ => Sym) σ) {T₁ T₂ : ℕ}
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ))
    (hp : f (some x) = true → HT ρ (Function.update B k rest) p B' T₁)
    (hq : f (some x) = false → HT ρ (Function.update B k rest) q B' T₂) :
    HT ρ B ((popR' lS k).seq (.ite (fun v => f (lS.get v)) p q)) B' (1 + (max T₁ T₂ + 1)) := by
  have h1 : Triple ρ (fun s => s.stk = B) (popR' lS k)
      (fun s => s.stk = Function.update B k rest ∧ lS.get s.var = some x) 1 := by
    rintro ⟨v, S⟩ hS
    change S = B at hS
    subst hS
    refine ⟨_, 1, Eval.pop ρ k (fun v o => lS.set v o) v S, ⟨?_, ?_⟩, le_rfl⟩
    · show Function.update S k (S k).tail = Function.update S k rest
      rw [hk]
      rfl
    · show lS.get (lS.set v (S k).head?) = some x
      rw [lS.get_set, hk]
      rfl
  refine Triple.seq h1 (Triple.ite ?_ ?_)
  · rintro s ⟨⟨hsB, hsx⟩, hc⟩
    have hfo : f (some x) = true := by rw [← hsx]; exact hc
    exact (hp hfo).mono (le_max_left _ _) s hsB
  · rintro s ⟨⟨hsB, hsx⟩, hc⟩
    have hfo : f (some x) = false := by rw [← hsx]; exact hc
    exact (hq hfo).mono (le_max_right _ _) s hsB

/-! ## Facts about the numeric encodings -/

theorem termOK_cons_nonbit {x : Sym} (hx : x.isBit = false) (l : List Sym) : TermOK (x :: l) :=
  TermOK.cons hx l

theorem termOK_mark (l : List Sym) : TermOK (Sym.mark :: l) := TermOK.cons rfl l

theorem termOK_intSyms (z : ℤ) (l : List Sym) : TermOK (intSyms z ++ l) := by
  unfold intSyms sgnSym
  split_ifs <;> exact TermOK.cons rfl _

theorem intSyms_pos {z : ℤ} (hz : 0 ≤ z) : intSyms z = Sym.pos :: natSyms z.toNat := by
  unfold intSyms sgnSym
  rw [if_neg (by omega)]
  congr 2
  omega

theorem intSyms_natCast' (n : ℕ) (l : List Sym) :
    Sym.pos :: (natSyms n ++ l) = intSyms (n : ℤ) ++ l := by
  rw [intSyms_natCast]
  rfl

#assert_std_axioms freeBelow_mapStk freeBelow_liftRegs exists_inst nodup_allLoc mem_allLoc
  length_allLoc mem_freeLoc nodup_freeLoc length_freeLoc callMap_inl getD_mem_of_lt getD_inj_of_nodup
  callMap_injective callI_closed HT.seq HT.mono HT.of_eq HT.runs callI_spec HT.callI_upd
  HT.callI_upd2 HT.callI_test HT.pushS HT.popS HT.popBranch termOK_cons_nonbit termOK_mark
  termOK_intSyms intSyms_pos intSyms_natCast'

end WP.W7k2
