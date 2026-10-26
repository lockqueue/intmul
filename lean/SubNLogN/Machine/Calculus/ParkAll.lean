/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.Park
import SubNLogN.Machine.Calculus.Rules

/-!
# Framed procedure calculus (`Calculus/ParkAll.lean`): protecting and parking families of stacks

Family versions of the single-stack rules of `Calculus/Park.lean`, for calls that protect or park
many role stacks at once (CCore protects/parks its role streams before every child call). Every
program is a `forEachProg` fold over a symbolic list of stacks and every proof is by induction on
that list: no proof enumerates a family.

Programs (the symbol register is reached through a lens `l : Lens σ (Option Sym)`):
* `protectAll l ks` / `unprotectAll l ks`: `protect k` / `unprotect k` for each `k ∈ ks`;
* `protectAllCall l ks child = protectAll ; child ; unprotectAll`;
* `parkAll l rs p`: `park r p` for each `r ∈ rs` in list order; `unparkAll l p rs`: `unpark p r`
  for each `r ∈ rs` in reverse order;
* `parkAllCall l rs p child = parkAll ; protect p ; child ; unprotect p ; unparkAll`;
* `protectFin`, `parkFin`, `unparkFin`, … : the same over a role family `role : Fin W → K` written
  with `forEachFin` (`*_eq` lemmas identify them with the list versions on
  `(List.finRange W).map role`).

Rules (any environment `ρ`, so the child may be `recur 0`; lists duplicate-free):
* `runsIn_protectAll`, `runsIn_unprotectAll`: exact states (`protState ks S` puts a `mark` on top of
  every `k ∈ ks`), cost `|ks| + 1`;
* `runsIn_protectAllCall`: overhead `2|ks| + 2`;
* `runsIn_parkAll`, `runsIn_unparkAll`: exact states; the parking stack receives `parked rs es`
  (each block reversed and closed by a `mark`, the last parked block on top); costs
  `3·parkLen rs es + 5|rs| + 1` and `3·parkLen rs es + 2|rs| + 1`, where
  `parkLen rs es = Σ_{r ∈ rs} |es r|`;
* `runsIn_parkAllCall`: overhead `6·parkLen rs es + 7|rs| + 4`, independent of all tails;
* Fin-family corollaries `runsIn_protectFinCall`, `runsIn_parkFinCall`.
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

/-! ## Programs -/

section Programs

variable {K σ : Type}

/-- Protect every stack of `ks`: push one `mark` on each, in list order. -/
def protectAll (l : Lens σ (Option Sym)) (ks : List K) : Prog K (fun _ => Sym) σ :=
  forEachProg ks (fun k => (protect k).liftRegs l)

/-- Unprotect every stack of `ks`: pop one symbol (the protecting `mark`) from each. -/
def unprotectAll (l : Lens σ (Option Sym)) (ks : List K) : Prog K (fun _ => Sym) σ :=
  forEachProg ks (fun k => (unprotect k).liftRegs l)

/-- **Call with protection of a family**: `protectAll ks ; child ; unprotectAll ks`. -/
def protectAllCall (l : Lens σ (Option Sym)) (ks : List K) (child : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq (protectAll l ks) (.seq child (unprotectAll l ks))

/-- Park every stack of `rs` on the parking stack `p`, in list order. -/
def parkAll (l : Lens σ (Option Sym)) (rs : List K) (p : K) : Prog K (fun _ => Sym) σ :=
  forEachProg rs (fun r => (park r p).liftRegs l)

/-- Unpark every stack of `rs` from the parking stack `p`, in reverse list order. -/
def unparkAll (l : Lens σ (Option Sym)) (p : K) (rs : List K) : Prog K (fun _ => Sym) σ :=
  forEachProg rs.reverse (fun r => (unpark p r).liftRegs l)

/-- **Call with parking of a family**:
`parkAll rs p ; protect p ; child ; unprotect p ; unparkAll p rs`. -/
def parkAllCall (l : Lens σ (Option Sym)) (rs : List K) (p : K) (child : Prog K (fun _ => Sym) σ) :
    Prog K (fun _ => Sym) σ :=
  .seq (parkAll l rs p) (.seq ((protect p).liftRegs l) (.seq child
    (.seq ((unprotect p).liftRegs l) (unparkAll l p rs))))

/-- The content that `parkAll rs p` pushes on the parking stack: the block `es r` of every
`r ∈ rs`, reversed and closed by a `mark`; the block of the last stack of `rs` is on top. -/
def parked : List K → (K → List Sym) → List Sym
  | [], _ => []
  | r :: rs, es => parked rs es ++ ((es r).reverse ++ [Sym.mark])

/-- `parkLen rs es = Σ_{r ∈ rs} |es r|`, the total parked length. -/
def parkLen (rs : List K) (es : K → List Sym) : ℕ := (rs.map fun r => (es r).length).sum

theorem closed_protectAll (l : Lens σ (Option Sym)) (ks : List K) :
    (protectAll l ks).Closed :=
  closed_forEachProg _ ks (fun k _ => WP.W9comp.closed_liftRegs l (closed_protect k))

theorem closed_unprotectAll (l : Lens σ (Option Sym)) (ks : List K) :
    (unprotectAll l ks).Closed :=
  closed_forEachProg _ ks (fun k _ => WP.W9comp.closed_liftRegs l (closed_unprotect k))

theorem closed_protectAllCall (l : Lens σ (Option Sym)) (ks : List K)
    {child : Prog K (fun _ => Sym) σ} (hc : child.Closed) : (protectAllCall l ks child).Closed :=
  ⟨closed_protectAll l ks, hc, closed_unprotectAll l ks⟩

theorem closed_parkAll (l : Lens σ (Option Sym)) (rs : List K) (p : K) :
    (parkAll l rs p).Closed :=
  closed_forEachProg _ rs (fun r _ => WP.W9comp.closed_liftRegs l (closed_park r p))

theorem closed_unparkAll (l : Lens σ (Option Sym)) (p : K) (rs : List K) :
    (unparkAll l p rs).Closed :=
  closed_forEachProg _ rs.reverse (fun r _ => WP.W9comp.closed_liftRegs l (closed_unpark p r))

theorem closed_parkAllCall (l : Lens σ (Option Sym)) (rs : List K) (p : K)
    {child : Prog K (fun _ => Sym) σ} (hc : child.Closed) : (parkAllCall l rs p child).Closed :=
  ⟨closed_parkAll l rs p, WP.W9comp.closed_liftRegs l (closed_protect p), hc,
    WP.W9comp.closed_liftRegs l (closed_unprotect p), closed_unparkAll l p rs⟩

theorem parked_nil (es : K → List Sym) : parked [] es = [] := rfl

theorem parked_cons (r : K) (rs : List K) (es : K → List Sym) :
    parked (r :: rs) es = parked rs es ++ ((es r).reverse ++ [Sym.mark]) := rfl

theorem parked_append (es : K → List Sym) :
    ∀ l₁ l₂ : List K, parked (l₁ ++ l₂) es = parked l₂ es ++ parked l₁ es
  | [], l₂ => by simp [parked]
  | r :: l₁, l₂ => by
    rw [List.cons_append, parked_cons, parked_cons, parked_append es l₁ l₂, List.append_assoc]

theorem parkLen_cons (r : K) (rs : List K) (es : K → List Sym) :
    parkLen (r :: rs) es = (es r).length + parkLen rs es := by
  simp [parkLen]

theorem parkLen_reverse (rs : List K) (es : K → List Sym) :
    parkLen rs.reverse es = parkLen rs es := by
  simp [parkLen, List.map_reverse, List.sum_reverse]

end Programs

/-! ## Protecting a family -/

section Protect

variable {K σ : Type} [DecidableEq K] {ρ : List (Prog K (fun _ => Sym) σ)}

/-- The state after `protectAll ks` from `S`: a `mark` on top of every stack of `ks`. -/
def protState (ks : List K) (S : K → List Sym) : K → List Sym :=
  fun k => if k ∈ ks then Sym.mark :: S k else S k

theorem protState_nil (S : K → List Sym) : protState [] S = S := by
  funext k
  simp [protState]

theorem protState_cons_protect {k : K} {ks : List K} (hk : k ∉ ks) (S : K → List Sym) :
    protState ks (Function.update S k (Sym.mark :: S k)) = protState (k :: ks) S := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp [protState, hk]
  · simp [protState, hj]

theorem protState_cons_unprotect {k : K} {ks : List K} (hk : k ∉ ks) (U : K → List Sym) :
    Function.update (protState (k :: ks) U) k (U k) = protState ks U := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp [protState, hk]
  · simp [protState, hj]

/-- The empty fixed sequence costs one step. -/
theorem runsIn_forEachProg_nil {α : Type} (f : α → Prog K (fun _ => Sym) σ) (S : K → List Sym) :
    RunsIn ρ (forEachProg [] f) S S (fun _ => True) 1 := by
  have h := RunsIn.forEachProg (ρ := ρ) f (fun _ => 0) [] (fun _ => S)
    (fun i hi => absurd hi (Nat.not_lt_zero _))
  simpa using h

/-- **`protectAll`**, exact: a `mark` on top of every stack of `ks`; cost `|ks| + 1`. -/
theorem runsIn_protectAll (l : Lens σ (Option Sym)) :
    ∀ (ks : List K), ks.Nodup → ∀ S : K → List Sym,
      RunsIn ρ (protectAll l ks) S (protState ks S) (fun _ => True) (ks.length + 1)
  | [], _, S => by
    rw [protState_nil]
    exact runsIn_forEachProg_nil _ S
  | k :: ks, hnd, S => by
    have hk : k ∉ ks := (List.nodup_cons.1 hnd).1
    have h1 := RunsIn.of_runs_liftRegs l (runs_protect k S) (closed_protect k) ρ
    have h2 := runsIn_protectAll l ks (List.nodup_cons.1 hnd).2
      (Function.update S k (Sym.mark :: S k))
    rw [protState_cons_protect hk] at h2
    exact RunsIn.mono (RunsIn.seq h1 h2) (fun _ _ => trivial)
      (by simp only [List.length_cons]; omega)

/-- **`unprotectAll`**, exact: removes the `mark` that `protectAll` put on every stack of `ks`;
cost `|ks| + 1`. -/
theorem runsIn_unprotectAll (l : Lens σ (Option Sym)) :
    ∀ (ks : List K), ks.Nodup → ∀ U : K → List Sym,
      RunsIn ρ (unprotectAll l ks) (protState ks U) U (fun _ => True) (ks.length + 1)
  | [], _, U => by
    rw [protState_nil]
    exact runsIn_forEachProg_nil _ U
  | k :: ks, hnd, U => by
    have hk : k ∉ ks := (List.nodup_cons.1 hnd).1
    have h1 := RunsIn.of_runs_liftRegs l
      (runs_unprotect k (protState (k :: ks) U) (U k) (by simp [protState])) (closed_unprotect k) ρ
    rw [protState_cons_unprotect hk] at h1
    have h2 := runsIn_unprotectAll l ks (List.nodup_cons.1 hnd).2 U
    exact RunsIn.mono (RunsIn.seq h1 h2) (fun _ _ => trivial)
      (by simp only [List.length_cons]; omega)

/-- **The protection rule for a family.** The child runs with a `mark` on top of every stack of
`ks` (so the old contents are frame tails for it) and must leave each of these stacks as it found
it (`mark :: S k`). After the call every `k ∈ ks` holds `S k` again and every other stack is as the
child left it. The overhead `2|ks| + 2` does not depend on any tail. -/
theorem runsIn_protectAllCall (l : Lens σ (Option Sym)) {ks : List K} (hks : ks.Nodup)
    {child : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hchild : RunsIn ρ child (protState ks S) S' Q T)
    (hk' : ∀ k ∈ ks, S' k = Sym.mark :: S k) :
    RunsIn ρ (protectAllCall l ks child) S (fun k => if k ∈ ks then S k else S' k)
      (fun _ => True) (T + 2 * ks.length + 2) := by
  have h1 := runsIn_protectAll (ρ := ρ) l ks hks S
  have hS' : S' = protState ks (fun k => if k ∈ ks then S k else S' k) := by
    funext k
    by_cases hk : k ∈ ks
    · simp [protState, hk, hk' k hk]
    · simp [protState, hk]
  have h3 := runsIn_unprotectAll (ρ := ρ) l ks hks (fun k => if k ∈ ks then S k else S' k)
  rw [← hS'] at h3
  exact RunsIn.mono (RunsIn.seq h1 (RunsIn.seq hchild h3)) (fun _ _ => trivial) (by omega)

end Protect

/-! ## Parking a family -/

section Park

variable {K σ : Type} [DecidableEq K] {ρ : List (Prog K (fun _ => Sym) σ)}

/-- **`parkAll`**, exact. Every `r ∈ rs` holds a mark-free block `es r` above its frame tail
`rest r`; afterwards `r` holds `rest r` and the parking stack `p ∉ rs` holds `parked rs es` above
its old content. Cost `3·parkLen rs es + 5|rs| + 1`, independent of the tails. -/
theorem runsIn_parkAll (l : Lens σ (Option Sym)) (p : K) (es rest : K → List Sym) :
    ∀ (rs : List K), rs.Nodup → p ∉ rs → (∀ r ∈ rs, MarkFree (es r)) →
      (∀ r ∈ rs, FrameTail (rest r)) → ∀ S : K → List Sym, (∀ r ∈ rs, S r = es r ++ rest r) →
      RunsIn ρ (parkAll l rs p) S
        (fun k => if k = p then parked rs es ++ S p else if k ∈ rs then rest k else S k)
        (fun _ => True) (3 * parkLen rs es + 5 * rs.length + 1)
  | [], _, _, _, _, S, _ => by
    refine RunsIn.congr (runsIn_forEachProg_nil (ρ := ρ) (fun r => (park r p).liftRegs l) S) ?_
      (by simp [parkLen])
    funext k
    by_cases hk : k = p
    · simp [hk, parked]
    · simp [hk]
  | r :: rs, hnd, hp, hes, hrest, S, hS => by
    have hr : r ∉ rs := (List.nodup_cons.1 hnd).1
    have hrp : r ≠ p := fun h => hp (h ▸ List.mem_cons_self)
    have hp' : p ∉ rs := fun h => hp (List.mem_cons_of_mem r h)
    have h1 := RunsIn.of_runs_liftRegs l
      (runs_park hrp (es r) (rest r) S (hes r List.mem_cons_self) (hrest r List.mem_cons_self)
        (hS r List.mem_cons_self)) (closed_park r p) ρ
    have hS1 : ∀ r' ∈ rs, Function.update (Function.update S r (rest r)) p
        ((es r).reverse ++ Sym.mark :: S p) r' = es r' ++ rest r' := by
      intro r' hr'
      have h1 : r' ≠ p := fun h => hp' (h ▸ hr')
      have h2 : r' ≠ r := fun h => hr (h ▸ hr')
      rw [Function.update_of_ne h1, Function.update_of_ne h2]
      exact hS r' (List.mem_cons_of_mem r hr')
    have h2 := runsIn_parkAll l p es rest rs (List.nodup_cons.1 hnd).2 hp'
      (fun r' hr' => hes r' (List.mem_cons_of_mem r hr'))
      (fun r' hr' => hrest r' (List.mem_cons_of_mem r hr')) _ hS1
    refine RunsIn.congr (RunsIn.seq h1 h2) ?_ ?_
    · funext k
      by_cases hk : k = p
      · subst hk
        simp [parked, List.append_assoc]
      · by_cases hkr : k = r
        · subst hkr
          simp [hk, hr]
        · simp [hk, hkr]
    · simp only [parkLen_cons, List.length_cons]
      omega

/-- `unpark` along a list `qs` (the reverse of the parking order). -/
theorem runsIn_unparkFold (l : Lens σ (Option Sym)) (p : K) (es : K → List Sym) :
    ∀ (qs : List K), qs.Nodup → p ∉ qs → (∀ q ∈ qs, MarkFree (es q)) →
      ∀ (X : List Sym) (U : K → List Sym), U p = parked qs.reverse es ++ X →
      RunsIn ρ (forEachProg qs (fun r => (unpark p r).liftRegs l)) U
        (fun k => if k = p then X else if k ∈ qs then es k ++ U k else U k)
        (fun _ => True) (3 * parkLen qs es + 2 * qs.length + 1)
  | [], _, _, _, X, U, hU => by
    refine RunsIn.congr (runsIn_forEachProg_nil (ρ := ρ) (fun r => (unpark p r).liftRegs l) U) ?_
      (by simp [parkLen])
    funext k
    by_cases hk : k = p
    · subst hk
      simpa [parked] using hU
    · simp [hk]
  | q :: qs, hnd, hp, hes, X, U, hU => by
    have hq : q ∉ qs := (List.nodup_cons.1 hnd).1
    have hpq : p ≠ q := fun h => hp (h ▸ List.mem_cons_self)
    have hp' : p ∉ qs := fun h => hp (List.mem_cons_of_mem q h)
    have hUp : U p = (es q).reverse ++ Sym.mark :: (parked qs.reverse es ++ X) := by
      rw [hU, List.reverse_cons, parked_append]
      simp [parked, List.append_assoc]
    have h1 := RunsIn.of_runs_liftRegs l
      (runs_unpark hpq (es q) (parked qs.reverse es ++ X) U (hes q List.mem_cons_self) hUp)
      (closed_unpark p q) ρ
    have h2 := runsIn_unparkFold l p es qs (List.nodup_cons.1 hnd).2 hp'
      (fun q' hq' => hes q' (List.mem_cons_of_mem q hq')) X
      (Function.update (Function.update U p (parked qs.reverse es ++ X)) q (es q ++ U q))
      (by rw [Function.update_of_ne hpq, Function.update_self])
    refine RunsIn.congr (RunsIn.seq h1 h2) ?_ ?_
    · funext k
      by_cases hk : k = p
      · simp [hk]
      · by_cases hkq : k = q
        · subst hkq
          simp [hk, hq]
        · simp [hk, hkq]
    · simp only [parkLen_cons, List.length_cons]
      omega

/-- **`unparkAll`**, exact. If the parking stack holds `parked rs es` above `X`, then afterwards
it holds `X` and every `r ∈ rs` has `es r` back on top of its current content. Cost
`3·parkLen rs es + 2|rs| + 1`, independent of the tails. -/
theorem runsIn_unparkAll (l : Lens σ (Option Sym)) (p : K) (es : K → List Sym) {rs : List K}
    (hnd : rs.Nodup) (hp : p ∉ rs) (hes : ∀ r ∈ rs, MarkFree (es r)) (X : List Sym)
    (U : K → List Sym) (hU : U p = parked rs es ++ X) :
    RunsIn ρ (unparkAll l p rs) U
      (fun k => if k = p then X else if k ∈ rs then es k ++ U k else U k)
      (fun _ => True) (3 * parkLen rs es + 2 * rs.length + 1) := by
  have h := runsIn_unparkFold (ρ := ρ) l p es rs.reverse (List.nodup_reverse.2 hnd)
    (by simpa using hp) (fun q hq => hes q (List.mem_reverse.1 hq)) X U
    (by rw [List.reverse_reverse]; exact hU)
  refine RunsIn.congr h ?_ (by rw [parkLen_reverse, List.length_reverse])
  funext k
  simp only [List.mem_reverse]

/-- **The parking rule for a family.** Every `r ∈ rs` holds a mark-free block `es r` above its
frame tail `rest r`; `p ∉ rs` is the parking stack. The child runs with `r ↦ rest r` on `rs` and
with `p` holding `mark :: (parked rs es ++ S p)` (all frame tails); it may change every `r ∈ rs`
arbitrarily (for example push results on it) but must leave `p` as it found it. After the call
every `r ∈ rs` has `es r` back on top of what the child left, `p` holds `S p` again, and every
other stack is as the child left it. The overhead `6·parkLen rs es + 7|rs| + 4` does not depend on
any tail. -/
theorem runsIn_parkAllCall (l : Lens σ (Option Sym)) {rs : List K} {p : K} (hnd : rs.Nodup)
    (hp : p ∉ rs) (es rest : K → List Sym) (hes : ∀ r ∈ rs, MarkFree (es r))
    (hrest : ∀ r ∈ rs, FrameTail (rest r)) {child : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ} (hS : ∀ r ∈ rs, S r = es r ++ rest r)
    (hchild : RunsIn ρ child
      (fun k => if k = p then Sym.mark :: (parked rs es ++ S p) else if k ∈ rs then rest k else S k)
      S' Q T)
    (hp' : S' p = Sym.mark :: (parked rs es ++ S p)) :
    RunsIn ρ (parkAllCall l rs p child) S
      (fun k => if k = p then S p else if k ∈ rs then es k ++ S' k else S' k)
      (fun _ => True) (T + 6 * parkLen rs es + 7 * rs.length + 4) := by
  have h1 := runsIn_parkAll (ρ := ρ) l p es rest rs hnd hp hes hrest S hS
  have h2 := RunsIn.of_runs_liftRegs l
    (runs_protect p (fun k => if k = p then parked rs es ++ S p else if k ∈ rs then rest k else S k))
    (closed_protect p) ρ
  have hS2 : Function.update
      (fun k => if k = p then parked rs es ++ S p else if k ∈ rs then rest k else S k) p
      (Sym.mark :: (fun k => if k = p then parked rs es ++ S p else if k ∈ rs then rest k else S k) p)
      = (fun k => if k = p then Sym.mark :: (parked rs es ++ S p) else if k ∈ rs then rest k else S k) := by
    funext k
    by_cases hk : k = p
    · simp [hk]
    · simp [hk]
  have h4 := RunsIn.of_runs_liftRegs l (runs_unprotect p S' _ hp') (closed_unprotect p) ρ
  have h5 := runsIn_unparkAll (ρ := ρ) l p es hnd hp hes (S p)
    (Function.update S' p (parked rs es ++ S p)) (Function.update_self _ _ _)
  refine RunsIn.congr (RunsIn.seq h1 (RunsIn.seq (RunsIn.congr h2 hS2 le_rfl)
    (RunsIn.seq hchild (RunsIn.seq h4 h5)))) ?_ ?_
  · funext k
    by_cases hk : k = p
    · simp [hk]
    · simp [hk]
  · omega

end Park

/-! ## Role families `role : Fin W → K` -/

section Fin

variable {K σ : Type}

theorem forEachProg_comp_map {Γ : K → Type} {α β : Type} (g : α → β) (f : β → Prog K Γ σ) :
    ∀ l : List α, forEachProg (l.map g) f = forEachProg l (fun a => f (g a))
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, forEachProg_cons, forEachProg_cons, forEachProg_comp_map g f l]

/-- `protectAll` over a role family, written with `forEachFin`. -/
def protectFin (l : Lens σ (Option Sym)) (W : ℕ) (role : Fin W → K) : Prog K (fun _ => Sym) σ :=
  forEachFin W (fun i => (protect (role i)).liftRegs l)

/-- `unprotectAll` over a role family, written with `forEachFin`. -/
def unprotectFin (l : Lens σ (Option Sym)) (W : ℕ) (role : Fin W → K) :
    Prog K (fun _ => Sym) σ :=
  forEachFin W (fun i => (unprotect (role i)).liftRegs l)

/-- `parkAll` over a role family, written with `forEachFin`. -/
def parkFin (l : Lens σ (Option Sym)) (W : ℕ) (role : Fin W → K) (p : K) :
    Prog K (fun _ => Sym) σ :=
  forEachFin W (fun i => (park (role i) p).liftRegs l)

/-- `unparkAll` over a role family, written with `forEachFin` (roles in decreasing order). -/
def unparkFin (l : Lens σ (Option Sym)) (p : K) (W : ℕ) (role : Fin W → K) :
    Prog K (fun _ => Sym) σ :=
  forEachFin W (fun i => (unpark p (role (Fin.rev i))).liftRegs l)

/-- Protected call over a role family. -/
def protectFinCall (l : Lens σ (Option Sym)) (W : ℕ) (role : Fin W → K)
    (child : Prog K (fun _ => Sym) σ) : Prog K (fun _ => Sym) σ :=
  .seq (protectFin l W role) (.seq child (unprotectFin l W role))

/-- Parked call over a role family. -/
def parkFinCall (l : Lens σ (Option Sym)) (W : ℕ) (role : Fin W → K) (p : K)
    (child : Prog K (fun _ => Sym) σ) : Prog K (fun _ => Sym) σ :=
  .seq (parkFin l W role p) (.seq ((protect p).liftRegs l) (.seq child
    (.seq ((unprotect p).liftRegs l) (unparkFin l p W role))))

theorem protectFin_eq (l : Lens σ (Option Sym)) (W : ℕ) (role : Fin W → K) :
    protectFin l W role = protectAll l ((List.finRange W).map role) := by
  rw [protectAll, forEachProg_comp_map]
  rfl

theorem unprotectFin_eq (l : Lens σ (Option Sym)) (W : ℕ) (role : Fin W → K) :
    unprotectFin l W role = unprotectAll l ((List.finRange W).map role) := by
  rw [unprotectAll, forEachProg_comp_map]
  rfl

theorem parkFin_eq (l : Lens σ (Option Sym)) (W : ℕ) (role : Fin W → K) (p : K) :
    parkFin l W role p = parkAll l ((List.finRange W).map role) p := by
  rw [parkAll, forEachProg_comp_map]
  rfl

theorem unparkFin_eq (l : Lens σ (Option Sym)) (p : K) (W : ℕ) (role : Fin W → K) :
    unparkFin l p W role = unparkAll l p ((List.finRange W).map role) := by
  rw [unparkAll, ← List.map_reverse, List.finRange_reverse, List.map_map, forEachProg_comp_map]
  rfl

theorem protectFinCall_eq (l : Lens σ (Option Sym)) (W : ℕ) (role : Fin W → K)
    (child : Prog K (fun _ => Sym) σ) :
    protectFinCall l W role child = protectAllCall l ((List.finRange W).map role) child := by
  rw [protectFinCall, protectAllCall, protectFin_eq, unprotectFin_eq]

theorem parkFinCall_eq (l : Lens σ (Option Sym)) (W : ℕ) (role : Fin W → K) (p : K)
    (child : Prog K (fun _ => Sym) σ) :
    parkFinCall l W role p child = parkAllCall l ((List.finRange W).map role) p child := by
  rw [parkFinCall, parkAllCall, parkFin_eq, unparkFin_eq]

theorem nodup_map_finRange {W : ℕ} {role : Fin W → K} (hrole : Function.Injective role) :
    ((List.finRange W).map role).Nodup :=
  (List.nodup_finRange W).map hrole

theorem forall_mem_map_finRange {W : ℕ} {role : Fin W → K} {P : K → Prop}
    (h : ∀ i, P (role i)) : ∀ k ∈ (List.finRange W).map role, P k := by
  intro k hk
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hk
  exact h i

variable [DecidableEq K] {ρ : List (Prog K (fun _ => Sym) σ)}

/-- **The protection rule for a role family** `role : Fin W → K` (injective). -/
theorem runsIn_protectFinCall (l : Lens σ (Option Sym)) {W : ℕ} {role : Fin W → K}
    (hrole : Function.Injective role) {child : Prog K (fun _ => Sym) σ} {S S' : K → List Sym}
    {Q : σ → Prop} {T : ℕ}
    (hchild : RunsIn ρ child (protState ((List.finRange W).map role) S) S' Q T)
    (hk' : ∀ i, S' (role i) = Sym.mark :: S (role i)) :
    RunsIn ρ (protectFinCall l W role child) S
      (fun k => if k ∈ (List.finRange W).map role then S k else S' k)
      (fun _ => True) (T + 2 * W + 2) := by
  rw [protectFinCall_eq]
  have h := runsIn_protectAllCall (ρ := ρ) l (nodup_map_finRange hrole) hchild
    (forall_mem_map_finRange (P := fun k => S' k = Sym.mark :: S k) hk')
  exact RunsIn.congr h rfl (by simp)

/-- **The parking rule for a role family** `role : Fin W → K` (injective, parking stack `p` not a
role stack). -/
theorem runsIn_parkFinCall (l : Lens σ (Option Sym)) {W : ℕ} {role : Fin W → K}
    (hrole : Function.Injective role) {p : K} (hp : ∀ i, role i ≠ p) (es rest : K → List Sym)
    (hes : ∀ i, MarkFree (es (role i))) (hrest : ∀ i, FrameTail (rest (role i)))
    {child : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hS : ∀ i, S (role i) = es (role i) ++ rest (role i))
    (hchild : RunsIn ρ child
      (fun k => if k = p then Sym.mark :: (parked ((List.finRange W).map role) es ++ S p)
        else if k ∈ (List.finRange W).map role then rest k else S k) S' Q T)
    (hp' : S' p = Sym.mark :: (parked ((List.finRange W).map role) es ++ S p)) :
    RunsIn ρ (parkFinCall l W role p child) S
      (fun k => if k = p then S p else if k ∈ (List.finRange W).map role then es k ++ S' k
        else S' k)
      (fun _ => True) (T + 6 * parkLen ((List.finRange W).map role) es + 7 * W + 4) := by
  rw [parkFinCall_eq]
  have hp0 : p ∉ (List.finRange W).map role := by
    intro h
    obtain ⟨i, -, hi⟩ := List.mem_map.1 h
    exact hp i hi
  have h := runsIn_parkAllCall (ρ := ρ) l (nodup_map_finRange hrole) hp0 es rest
    (forall_mem_map_finRange (P := fun k => MarkFree (es k)) hes)
    (forall_mem_map_finRange (P := fun k => FrameTail (rest k)) hrest)
    (forall_mem_map_finRange (P := fun k => S k = es k ++ rest k) hS) hchild hp'
  exact RunsIn.congr h rfl (by simp)

end Fin

#assert_std_axioms closed_protectAll closed_unprotectAll closed_protectAllCall closed_parkAll
  closed_unparkAll closed_parkAllCall parked_append parkLen_cons parkLen_reverse
  runsIn_forEachProg_nil runsIn_protectAll runsIn_unprotectAll runsIn_protectAllCall
  runsIn_parkAll runsIn_unparkFold runsIn_unparkAll runsIn_parkAllCall forEachProg_comp_map
  protectFin_eq unprotectFin_eq parkFin_eq unparkFin_eq protectFinCall_eq parkFinCall_eq
  runsIn_protectFinCall runsIn_parkFinCall

end SubNLogN.Machine.Calculus
