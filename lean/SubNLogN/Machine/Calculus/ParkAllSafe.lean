/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Calculus.ParkAll
import SubNLogN.Machine.Calculus.SafePark

/-!
# Framed procedure calculus (`Calculus/ParkAllSafe.lean`): boundary-safe family protection and parking

Boundary-safe (`SafeRunsIn`, every framed set) versions of the family programs of
`Calculus/ParkAll.lean`, for the **same programs** and with the **same costs**, composed from the
owned-delimiter certificates of `Calculus/SafePark.lean` (`safeRunsIn_protect`,
`safeRunsIn_unprotect`, `safeRunsIn_park`, `safeRunsIn_unpark`):

* `safeRunsIn_protectAll`, `safeRunsIn_unprotectAll`, `safeRunsIn_protectAllCall`;
* `safeRunsIn_parkAll`, `safeRunsIn_unparkAll`, `safeRunsIn_parkAllCall`. Parking uses the
  owned-delimiter convention: every parked stack holds `es r ++ mark :: rt r`, so the `mark` that
  stops the scan is visible (`Calculus/SafePark.lean`); the stack `r` is left as `mark :: rt r`.

Safe-child introduction (family protection and family parking). The child is certified
on a *stripped view*: a protected role shows only its owned `[mark]`, and the parked content is a
protected tail (`SafeRunsIn.frame_tail`). Since the wrapper programs are themselves certified
safe (above), the conclusion is a `SafeRunsIn` fact for the whole wrapper
(`safeRunsIn_protectAllCall_of_safe_child`, `safeRunsIn_parkAllCall_of_safe_child`); the
corresponding `RunsIn` forms follow (`runsIn_protectAllCall_of_safe_child`,
`runsIn_parkAllCall_of_safe_child`).
-/

namespace SubNLogN.Machine.Calculus

open TMFw TMFw.Contracts TMFw.Lib

section SafeFamilies

variable {K σ : Type} [DecidableEq K] {ρ : List (Prog K (fun _ => Sym) σ)}

/-- The empty fixed sequence (`skip`) is safe; cost one step. -/
theorem safeRunsIn_forEachProg_nil (framed : K → Prop) {α : Type}
    (f : α → Prog K (fun _ => Sym) σ) (S : K → List Sym) :
    SafeRunsIn framed ρ (forEachProg [] f) S S (fun _ => True) 1 :=
  fun v => ⟨v, 1, SafeEval.load ρ id v S, trivial, le_rfl⟩

/-- **`protectAll`**, boundary-safe for every framed set; exact state `protState ks S`, cost
`|ks| + 1`. -/
theorem safeRunsIn_protectAll (framed : K → Prop) (l : Lens σ (Option Sym)) :
    ∀ (ks : List K), ks.Nodup → ∀ S : K → List Sym,
      SafeRunsIn framed ρ (protectAll l ks) S (protState ks S) (fun _ => True) (ks.length + 1)
  | [], _, S => by
    rw [protState_nil]
    exact safeRunsIn_forEachProg_nil framed _ S
  | k :: ks, hnd, S => by
    have hk : k ∉ ks := (List.nodup_cons.1 hnd).1
    have h1 := SafeRunsIn.liftRegs l (closed_protect k) (safeRunsIn_protect framed [] k S) ρ
    have h2 := safeRunsIn_protectAll framed l ks (List.nodup_cons.1 hnd).2
      (Function.update S k (Sym.mark :: S k))
    rw [protState_cons_protect hk] at h2
    exact SafeRunsIn.mono (SafeRunsIn.seq h1 h2) (fun _ _ => trivial)
      (by simp only [List.length_cons]; omega)

/-- **`unprotectAll`**, boundary-safe for every framed set (every popped `mark` is visible); cost
`|ks| + 1`. -/
theorem safeRunsIn_unprotectAll (framed : K → Prop) (l : Lens σ (Option Sym)) :
    ∀ (ks : List K), ks.Nodup → ∀ U : K → List Sym,
      SafeRunsIn framed ρ (unprotectAll l ks) (protState ks U) U (fun _ => True) (ks.length + 1)
  | [], _, U => by
    rw [protState_nil]
    exact safeRunsIn_forEachProg_nil framed _ U
  | k :: ks, hnd, U => by
    have hk : k ∉ ks := (List.nodup_cons.1 hnd).1
    have h1 := SafeRunsIn.liftRegs l (closed_unprotect k)
      (safeRunsIn_unprotect framed [] k (protState (k :: ks) U) (U k) (by simp [protState])) ρ
    rw [protState_cons_unprotect hk] at h1
    have h2 := safeRunsIn_unprotectAll framed l ks (List.nodup_cons.1 hnd).2 U
    exact SafeRunsIn.mono (SafeRunsIn.seq h1 h2) (fun _ _ => trivial)
      (by simp only [List.length_cons]; omega)

/-- **The safe protection rule for a family**: as `runsIn_protectAllCall`, boundary-safe as soon
as the child's run is. -/
theorem safeRunsIn_protectAllCall (framed : K → Prop) (l : Lens σ (Option Sym)) {ks : List K}
    (hks : ks.Nodup) {child : Prog K (fun _ => Sym) σ} {S S' : K → List Sym} {Q : σ → Prop}
    {T : ℕ} (hchild : SafeRunsIn framed ρ child (protState ks S) S' Q T)
    (hk' : ∀ k ∈ ks, S' k = Sym.mark :: S k) :
    SafeRunsIn framed ρ (protectAllCall l ks child) S (fun k => if k ∈ ks then S k else S' k)
      (fun _ => True) (T + 2 * ks.length + 2) := by
  have h1 := safeRunsIn_protectAll (ρ := ρ) framed l ks hks S
  have hS' : S' = protState ks (fun k => if k ∈ ks then S k else S' k) := by
    funext k
    by_cases hk : k ∈ ks
    · simp [protState, hk, hk' k hk]
    · simp [protState, hk]
  have h3 := safeRunsIn_unprotectAll (ρ := ρ) framed l ks hks
    (fun k => if k ∈ ks then S k else S' k)
  rw [← hS'] at h3
  exact SafeRunsIn.mono (SafeRunsIn.seq h1 (SafeRunsIn.seq hchild h3)) (fun _ _ => trivial)
    (by omega)

/-- **`parkAll`**, boundary-safe for every framed set (owned delimiters): every `r ∈ rs` holds
`es r ++ mark :: rt r` with `es r` mark-free; afterwards `r` holds `mark :: rt r` and the parking
stack `p ∉ rs` holds `parked rs es` above its old content. Cost `3·parkLen rs es + 5|rs| + 1`. -/
theorem safeRunsIn_parkAll (framed : K → Prop) (l : Lens σ (Option Sym)) (p : K)
    (es rt : K → List Sym) :
    ∀ (rs : List K), rs.Nodup → p ∉ rs → (∀ r ∈ rs, MarkFree (es r)) →
      ∀ S : K → List Sym, (∀ r ∈ rs, S r = es r ++ Sym.mark :: rt r) →
      SafeRunsIn framed ρ (parkAll l rs p) S
        (fun k => if k = p then parked rs es ++ S p else if k ∈ rs then Sym.mark :: rt k else S k)
        (fun _ => True) (3 * parkLen rs es + 5 * rs.length + 1)
  | [], _, _, _, S, _ => by
    refine SafeRunsIn.congr (safeRunsIn_forEachProg_nil (ρ := ρ) framed
      (fun r => (park r p).liftRegs l) S) ?_ (by simp [parkLen])
    funext k
    by_cases hk : k = p
    · simp [hk, parked]
    · simp [hk]
  | r :: rs, hnd, hp, hes, S, hS => by
    have hr : r ∉ rs := (List.nodup_cons.1 hnd).1
    have hrp : r ≠ p := fun h => hp (h ▸ List.mem_cons_self)
    have hp' : p ∉ rs := fun h => hp (List.mem_cons_of_mem r h)
    have h1 := SafeRunsIn.liftRegs l (closed_park r p)
      (safeRunsIn_park framed hrp [] (es r) (rt r) S (hes r List.mem_cons_self)
        (hS r List.mem_cons_self)) ρ
    have hS1 : ∀ r' ∈ rs, Function.update (Function.update S r (Sym.mark :: rt r)) p
        ((es r).reverse ++ Sym.mark :: S p) r' = es r' ++ Sym.mark :: rt r' := by
      intro r' hr'
      have h1 : r' ≠ p := fun h => hp' (h ▸ hr')
      have h2 : r' ≠ r := fun h => hr (h ▸ hr')
      rw [Function.update_of_ne h1, Function.update_of_ne h2]
      exact hS r' (List.mem_cons_of_mem r hr')
    have h2 := safeRunsIn_parkAll framed l p es rt rs (List.nodup_cons.1 hnd).2 hp'
      (fun r' hr' => hes r' (List.mem_cons_of_mem r hr')) _ hS1
    refine SafeRunsIn.congr (SafeRunsIn.seq h1 h2) ?_ ?_
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

/-- `unpark` along a list `qs` (the reverse of the parking order), boundary-safe. -/
theorem safeRunsIn_unparkFold (framed : K → Prop) (l : Lens σ (Option Sym)) (p : K)
    (es : K → List Sym) :
    ∀ (qs : List K), qs.Nodup → p ∉ qs → (∀ q ∈ qs, MarkFree (es q)) →
      ∀ (X : List Sym) (U : K → List Sym), U p = parked qs.reverse es ++ X →
      SafeRunsIn framed ρ (forEachProg qs (fun r => (unpark p r).liftRegs l)) U
        (fun k => if k = p then X else if k ∈ qs then es k ++ U k else U k)
        (fun _ => True) (3 * parkLen qs es + 2 * qs.length + 1)
  | [], _, _, _, X, U, hU => by
    refine SafeRunsIn.congr (safeRunsIn_forEachProg_nil (ρ := ρ) framed
      (fun r => (unpark p r).liftRegs l) U) ?_ (by simp [parkLen])
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
    have h1 := SafeRunsIn.liftRegs l (closed_unpark p q)
      (safeRunsIn_unpark framed hpq [] (es q) (parked qs.reverse es ++ X) U
        (hes q List.mem_cons_self) hUp) ρ
    have h2 := safeRunsIn_unparkFold framed l p es qs (List.nodup_cons.1 hnd).2 hp'
      (fun q' hq' => hes q' (List.mem_cons_of_mem q hq')) X
      (Function.update (Function.update U p (parked qs.reverse es ++ X)) q (es q ++ U q))
      (by rw [Function.update_of_ne hpq, Function.update_self])
    refine SafeRunsIn.congr (SafeRunsIn.seq h1 h2) ?_ ?_
    · funext k
      by_cases hk : k = p
      · simp [hk]
      · by_cases hkq : k = q
        · subst hkq
          simp [hk, hq]
        · simp [hk, hkq]
    · simp only [parkLen_cons, List.length_cons]
      omega

/-- **`unparkAll`**, boundary-safe for every framed set; as `runsIn_unparkAll`. -/
theorem safeRunsIn_unparkAll (framed : K → Prop) (l : Lens σ (Option Sym)) (p : K)
    (es : K → List Sym) {rs : List K} (hnd : rs.Nodup) (hp : p ∉ rs)
    (hes : ∀ r ∈ rs, MarkFree (es r)) (X : List Sym) (U : K → List Sym)
    (hU : U p = parked rs es ++ X) :
    SafeRunsIn framed ρ (unparkAll l p rs) U
      (fun k => if k = p then X else if k ∈ rs then es k ++ U k else U k)
      (fun _ => True) (3 * parkLen rs es + 2 * rs.length + 1) := by
  have h := safeRunsIn_unparkFold (ρ := ρ) framed l p es rs.reverse (List.nodup_reverse.2 hnd)
    (by simpa using hp) (fun q hq => hes q (List.mem_reverse.1 hq)) X U
    (by rw [List.reverse_reverse]; exact hU)
  refine SafeRunsIn.congr h ?_ (by rw [parkLen_reverse, List.length_reverse])
  funext k
  simp only [List.mem_reverse]

/-- **The safe parking rule for a family** (owned delimiters): as `runsIn_parkAllCall`, with every
parked stack holding `es r ++ mark :: rt r`; boundary-safe as soon as the child's run is. The
child sees `r ↦ mark :: rt r` on `rs` and `p ↦ mark :: (parked rs es ++ S p)`; it may change every
`r ∈ rs` arbitrarily but must restore `p`. Overhead `6·parkLen rs es + 7|rs| + 4`. -/
theorem safeRunsIn_parkAllCall (framed : K → Prop) (l : Lens σ (Option Sym)) {rs : List K}
    {p : K} (hnd : rs.Nodup) (hp : p ∉ rs) (es rt : K → List Sym)
    (hes : ∀ r ∈ rs, MarkFree (es r)) {child : Prog K (fun _ => Sym) σ}
    {S S' : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hS : ∀ r ∈ rs, S r = es r ++ Sym.mark :: rt r)
    (hchild : SafeRunsIn framed ρ child
      (fun k => if k = p then Sym.mark :: (parked rs es ++ S p)
        else if k ∈ rs then Sym.mark :: rt k else S k) S' Q T)
    (hp' : S' p = Sym.mark :: (parked rs es ++ S p)) :
    SafeRunsIn framed ρ (parkAllCall l rs p child) S
      (fun k => if k = p then S p else if k ∈ rs then es k ++ S' k else S' k)
      (fun _ => True) (T + 6 * parkLen rs es + 7 * rs.length + 4) := by
  have h1 := safeRunsIn_parkAll (ρ := ρ) framed l p es rt rs hnd hp hes S hS
  have h2 := SafeRunsIn.liftRegs l (closed_protect p) (safeRunsIn_protect framed [] p
    (fun k => if k = p then parked rs es ++ S p else if k ∈ rs then Sym.mark :: rt k else S k)) ρ
  have hS2 : Function.update
      (fun k => if k = p then parked rs es ++ S p else if k ∈ rs then Sym.mark :: rt k else S k) p
      (Sym.mark :: (fun k => if k = p then parked rs es ++ S p
        else if k ∈ rs then Sym.mark :: rt k else S k) p)
      = (fun k => if k = p then Sym.mark :: (parked rs es ++ S p)
        else if k ∈ rs then Sym.mark :: rt k else S k) := by
    funext k
    by_cases hk : k = p
    · simp [hk]
    · simp [hk]
  have h4 := SafeRunsIn.liftRegs l (closed_unprotect p)
    (safeRunsIn_unprotect framed [] p S' _ hp') ρ
  have h5 := safeRunsIn_unparkAll (ρ := ρ) framed l p es hnd hp hes (S p)
    (Function.update S' p (parked rs es ++ S p)) (Function.update_self _ _ _)
  refine SafeRunsIn.congr (SafeRunsIn.seq h1 (SafeRunsIn.seq (SafeRunsIn.congr h2 hS2 le_rfl)
    (SafeRunsIn.seq hchild (SafeRunsIn.seq h4 h5)))) ?_ ?_
  · funext k
    by_cases hk : k = p
    · simp [hk]
    · simp [hk]
  · omega

/-! ## Safe-child introduction -/

/-- **Family protection with a stripped child view**, boundary-safe for the whole
wrapper. The child is certified on the view where every protected role shows only its owned
`[mark]` (the former content `S k` becomes a protected tail; all roles of `ks` must be framed),
and it must leave that `[mark]`. -/
theorem safeRunsIn_protectAllCall_of_safe_child {framed : K → Prop} (l : Lens σ (Option Sym))
    {ks : List K} (hks : ks.Nodup) (hframe : ∀ k ∈ ks, framed k)
    {child : Prog K (fun _ => Sym) σ} {S V : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hchild : SafeRunsIn framed ρ child (fun k => if k ∈ ks then [Sym.mark] else S k) V Q T)
    (hV : ∀ k ∈ ks, V k = [Sym.mark]) :
    SafeRunsIn framed ρ (protectAllCall l ks child) S (fun k => if k ∈ ks then S k else V k)
      (fun _ => True) (T + 2 * ks.length + 2) := by
  have hτ : ∀ k, ¬ framed k → (fun k => if k ∈ ks then S k else []) k = [] := by
    intro k hk
    by_cases hm : k ∈ ks
    · exact (hk (hframe k hm)).elim
    · simp [hm]
  have hc := hchild.frame_tail (fun k => if k ∈ ks then S k else []) hτ
  have hI : appendTail (fun k => if k ∈ ks then [Sym.mark] else S k)
      (fun k => if k ∈ ks then S k else []) = protState ks S := by
    funext k
    by_cases hk : k ∈ ks <;> simp [appendTail, protState, hk]
  rw [hI] at hc
  have hV' : ∀ k ∈ ks, appendTail V (fun k => if k ∈ ks then S k else []) k = Sym.mark :: S k := by
    intro k hk
    simp [appendTail, hk, hV k hk]
  refine SafeRunsIn.congr (safeRunsIn_protectAllCall framed l hks hc hV') ?_ le_rfl
  funext k
  by_cases hk : k ∈ ks <;> simp [appendTail, hk]

/-- The `RunsIn` corollary of `safeRunsIn_protectAllCall_of_safe_child`. -/
theorem runsIn_protectAllCall_of_safe_child {framed : K → Prop} (l : Lens σ (Option Sym))
    {ks : List K} (hks : ks.Nodup) (hframe : ∀ k ∈ ks, framed k)
    {child : Prog K (fun _ => Sym) σ} {S V : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hchild : SafeRunsIn framed ρ child (fun k => if k ∈ ks then [Sym.mark] else S k) V Q T)
    (hV : ∀ k ∈ ks, V k = [Sym.mark]) :
    RunsIn ρ (protectAllCall l ks child) S (fun k => if k ∈ ks then S k else V k)
      (fun _ => True) (T + 2 * ks.length + 2) :=
  (safeRunsIn_protectAllCall_of_safe_child l hks hframe hchild hV).runsIn

/-- **Family parking with owned role guards**, boundary-safe for the whole wrapper.
Every parked role holds `es r ++ mark :: rt r`; the child is certified on the view where `p` and
every role of `rs` show only their owned `[mark]` (the parked content `parked rs es ++ S p` and the
role remainders `rt r` become protected tails; `p` and the roles must be framed); the child must
leave `p` as `[mark]`. Afterwards a role holds `es r ++ V r ++ rt r`, `p` holds `S p` again. The
cost is that of `runsIn_parkAllCall`. -/
theorem safeRunsIn_parkAllCall_of_safe_child {framed : K → Prop} (l : Lens σ (Option Sym))
    {rs : List K} {p : K} (hnd : rs.Nodup) (hp : p ∉ rs) (hfp : framed p)
    (hfr : ∀ r ∈ rs, framed r) (es rt : K → List Sym) (hes : ∀ r ∈ rs, MarkFree (es r))
    {child : Prog K (fun _ => Sym) σ} {S V : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hS : ∀ r ∈ rs, S r = es r ++ Sym.mark :: rt r)
    (hchild : SafeRunsIn framed ρ child
      (fun k => if k = p then [Sym.mark] else if k ∈ rs then [Sym.mark] else S k) V Q T)
    (hVp : V p = [Sym.mark]) :
    SafeRunsIn framed ρ (parkAllCall l rs p child) S
      (fun k => if k = p then S p else if k ∈ rs then es k ++ V k ++ rt k else V k)
      (fun _ => True) (T + 6 * parkLen rs es + 7 * rs.length + 4) := by
  have hτ : ∀ k, ¬ framed k →
      (fun k => if k = p then parked rs es ++ S p else if k ∈ rs then rt k else []) k = [] := by
    intro k hk
    by_cases hkp : k = p
    · exact (hk (hkp ▸ hfp)).elim
    · by_cases hm : k ∈ rs
      · exact (hk (hfr k hm)).elim
      · simp [hkp, hm]
  have hc := hchild.frame_tail
    (fun k => if k = p then parked rs es ++ S p else if k ∈ rs then rt k else []) hτ
  have hI : appendTail (fun k => if k = p then [Sym.mark] else if k ∈ rs then [Sym.mark] else S k)
      (fun k => if k = p then parked rs es ++ S p else if k ∈ rs then rt k else []) =
      (fun k => if k = p then Sym.mark :: (parked rs es ++ S p)
        else if k ∈ rs then Sym.mark :: rt k else S k) := by
    funext k
    by_cases hkp : k = p
    · simp [appendTail, hkp]
    · by_cases hm : k ∈ rs <;> simp [appendTail, hkp, hm]
  rw [hI] at hc
  have hp' : appendTail V
      (fun k => if k = p then parked rs es ++ S p else if k ∈ rs then rt k else []) p =
      Sym.mark :: (parked rs es ++ S p) := by
    simp [appendTail, hVp]
  refine SafeRunsIn.congr (safeRunsIn_parkAllCall framed l hnd hp es rt hes hS hc hp') ?_ le_rfl
  funext k
  by_cases hkp : k = p
  · simp [hkp]
  · by_cases hm : k ∈ rs <;> simp [appendTail, hkp, hm]

/-- The `RunsIn` corollary of `safeRunsIn_parkAllCall_of_safe_child`. -/
theorem runsIn_parkAllCall_of_safe_child {framed : K → Prop} (l : Lens σ (Option Sym))
    {rs : List K} {p : K} (hnd : rs.Nodup) (hp : p ∉ rs) (hfp : framed p)
    (hfr : ∀ r ∈ rs, framed r) (es rt : K → List Sym) (hes : ∀ r ∈ rs, MarkFree (es r))
    {child : Prog K (fun _ => Sym) σ} {S V : K → List Sym} {Q : σ → Prop} {T : ℕ}
    (hS : ∀ r ∈ rs, S r = es r ++ Sym.mark :: rt r)
    (hchild : SafeRunsIn framed ρ child
      (fun k => if k = p then [Sym.mark] else if k ∈ rs then [Sym.mark] else S k) V Q T)
    (hVp : V p = [Sym.mark]) :
    RunsIn ρ (parkAllCall l rs p child) S
      (fun k => if k = p then S p else if k ∈ rs then es k ++ V k ++ rt k else V k)
      (fun _ => True) (T + 6 * parkLen rs es + 7 * rs.length + 4) :=
  (safeRunsIn_parkAllCall_of_safe_child l hnd hp hfp hfr es rt hes hS hchild hVp).runsIn

end SafeFamilies

#assert_std_axioms safeRunsIn_forEachProg_nil safeRunsIn_protectAll safeRunsIn_unprotectAll
  safeRunsIn_protectAllCall safeRunsIn_parkAll safeRunsIn_unparkFold safeRunsIn_unparkAll
  safeRunsIn_parkAllCall safeRunsIn_protectAllCall_of_safe_child
  runsIn_protectAllCall_of_safe_child safeRunsIn_parkAllCall_of_safe_child
  runsIn_parkAllCall_of_safe_child

end SubNLogN.Machine.Calculus
