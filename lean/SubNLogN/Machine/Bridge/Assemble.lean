/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.Kit

/-!
# K5 reduction (4): the bridge program skeleton and its `Runs` rule

`bridgeProgOf ax pre reo init expo spr res dec mid sol post` is the bridge machine's control
structure (Section 4.4 (`sec:bridge-alg`), steps (1)–(5)):

```
pre ; reo ; init ;
peek ax ; while (ax ≠ 0) { expo ; spr ; res ; dec ; peek ax } ;     -- spreadFixedR roundHalfUpR: axes d-1, …, 1
mid ; init ;
peek ax ; while (ax ≠ 0) { sol ; dec ; peek ax } ;                  -- deconvFixedR roundHalfUpR: axes 1, …, d-1
post
```

`runs_bridgeProgOf` composes `Runs` contracts of the pieces between explicit states. Also: the
composite states at entry/exit (`mkB_init`, `mkB_final`), more transport lemmas, cost lemmas. All
proved.
-/

namespace SubNLogN.Machine.BridgeRed

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Bridge

/-! ## Skeleton -/

section Skeleton

variable {K σ' : Type}

/-- The control structure of the bridge machine. -/
def bridgeProgOf (ax : K) (pre reo init expo spr res dec mid sol post :
    Prog K (fun _ => Sym) (Option Sym × σ')) : Prog K (fun _ => Sym) (Option Sym × σ') :=
  .seq pre (.seq reo (.seq init
    (.seq (.seq (peekTop ax) (.loop topIsBit (.seq (.seq expo (.seq spr (.seq res dec)))
      (peekTop ax))))
    (.seq mid (.seq init
      (.seq (.seq (peekTop ax) (.loop topIsBit (.seq (.seq sol dec) (peekTop ax)))) post))))))

theorem closed_bridgeProgOf (ax : K) {pre reo init expo spr res dec mid sol post :
    Prog K (fun _ => Sym) (Option Sym × σ')} (h1 : pre.Closed) (h2 : reo.Closed)
    (h3 : init.Closed) (h4 : expo.Closed) (h5 : spr.Closed) (h6 : res.Closed) (h7 : dec.Closed)
    (h8 : mid.Closed) (h9 : sol.Closed) (h10 : post.Closed) :
    (bridgeProgOf ax pre reo init expo spr res dec mid sol post).Closed := by
  simp only [Prog.Closed, bridgeProgOf, Prog.FreeBelow, peekTop, true_and, and_true] at *
  tauto

variable [DecidableEq K]

/-- **`Runs` rule of the skeleton.** -/
theorem runs_bridgeProgOf (ax : K) (pre reo init expo spr res dec mid sol post :
    Prog K (fun _ => Sym) (Option Sym × σ')) (N : ℕ) (S0 S1 S2 S3 S4 : K → List Sym)
    (Bsp Bsol : ℕ → K → List Sym) (Tpre Treo Tinit Tmid Tpost : ℕ) (TcSp TcSol : ℕ → ℕ)
    (hpre : Runs pre S0 S1 (fun _ => True) Tpre) (hreo : Runs reo S1 S2 (fun _ => True) Treo)
    (hinit1 : Runs init S2 (Bsp N) (fun _ => True) Tinit)
    (hsp : ∀ n, n + 1 ≤ N →
      Runs (.seq expo (.seq spr (.seq res dec))) (Bsp (n + 1)) (Bsp n) (fun _ => True) (TcSp n))
    (hk1 : ∀ n, n ≤ N → Bsp n ax = natSyms n)
    (hmid : Runs mid (Bsp 0) S3 (fun _ => True) Tmid)
    (hinit2 : Runs init S3 (Bsol N) (fun _ => True) Tinit)
    (hsol : ∀ n, n + 1 ≤ N → Runs (.seq sol dec) (Bsol (n + 1)) (Bsol n) (fun _ => True) (TcSol n))
    (hk2 : ∀ n, n ≤ N → Bsol n ax = natSyms n)
    (hpost : Runs post (Bsol 0) S4 (fun _ => True) Tpost) :
    Runs (bridgeProgOf ax pre reo init expo spr res dec mid sol post) S0 S4 (fun _ => True)
      (Tpre + (Treo + (Tinit + ((1 + loopCost (fun n => TcSp n + 1) N) +
        (Tmid + (Tinit + ((1 + loopCost (fun n => TcSol n + 1) N) + Tpost))))))) := by
  have hL1 := runs_counted_loop ax _ Bsp N TcSp hk1 hsp
  have hL2 := runs_counted_loop ax _ Bsol N TcSol hk2 hsol
  unfold bridgeProgOf
  exact WP.W9comp.runs_seq hpre (WP.W9comp.runs_seq hreo (WP.W9comp.runs_seq hinit1
    (WP.W9comp.runs_seq hL1 (WP.W9comp.runs_seq hmid (WP.W9comp.runs_seq hinit2
      (WP.W9comp.runs_seq hL2 hpost))))))

end Skeleton

/-! ## Composite states -/

section States

variable {EP : Type}

theorem mkB_init (S : KLoc BrN (BrW ⊕ EP) → List Sym) (hS : KClean S) :
    S = mkB S (wst [] [] []) (S (.inl .src)) (S (.inl .dst)) := by
  funext k
  rcases k with n | (w | e)
  · cases n <;> rfl
  · cases w <;> exact hS _
  · rfl

variable [DecidableEq EP]

theorem mkB_final (S : KLoc BrN (BrW ⊕ EP) → List Sym) (hS : KClean S) (sr ds : List Sym) :
    mkB S (wst [] [] []) sr ds =
      Function.update (Function.update S (.inl .src) sr) (.inl .dst) ds := by
  funext k
  rcases k with n | (w | e)
  · cases n <;> simp [mkB, Function.update]
  · cases w <;> simp [mkB, wst, Function.update, hS (.inl _)]
  · simp [mkB, Function.update]

theorem wst_update_arr (a x e v : List Sym) : Function.update (wst a x e) .arr v = wst v x e := by
  funext w
  cases w <;> simp [wst, Function.update]

theorem wst_update_ax (a x e v : List Sym) : Function.update (wst a x e) .ax v = wst a v e := by
  funext w
  cases w <;> simp [wst, Function.update]

theorem wst_update_ex (a x e v : List Sym) : Function.update (wst a x e) .ex v = wst a x v := by
  funext w
  cases w <;> simp [wst, Function.update]

theorem update_arr_compM {Em : Type} [DecidableEq Em] (inj : Em → EP)
    (S : KLoc BrN (BrW ⊕ EP) → List Sym) (a x e sr ds v : List Sym) :
    Function.update (mkB S (wst a x e) sr ds ∘ ιM inj) (.inl 0) v =
      mkB S (wst v x e) sr ds ∘ ιM inj := by
  funext k
  rcases k with i | e'
  · by_cases hi : i = 0
    · subst hi
      simp [mkB, wst, ιM, Function.update]
    · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [mkB, wst, ιM, Function.update, hi, hi']
  · simp [mkB, ιM, Function.update]

theorem update_ax_compD {m : ℕ} (inj : Fin m → EP) (S : KLoc BrN (BrW ⊕ EP) → List Sym)
    (a x e sr ds v : List Sym) :
    Function.update (mkB S (wst a x e) sr ds ∘ ιD inj) (.inl 0) v =
      mkB S (wst a v e) sr ds ∘ ιD inj := by
  funext k
  rcases k with i | j
  · have : i = 0 := Subsingleton.elim i 0
    subst this
    simp [mkB, wst, ιD, Function.update]
  · simp [mkB, ιD, Function.update]

end States

/-! ## Cost lemmas -/

/-- A loop whose iterations are bounded by `C * g n`. -/
theorem loopCost_le_of (T g : ℕ → ℕ) (C N : ℕ) (h : ∀ n, n < N → T n + 1 ≤ C * g n) :
    loopCost (fun n => T n + 1) N ≤ C * ((List.range N).map g).sum + N + 1 := by
  induction N with
  | zero => simp [loopCost]
  | succ N ih =>
    have h1 := ih (fun n hn => h n (by omega))
    have h2 := h N (by omega)
    rw [loopCost, List.range_succ, List.map_append, List.sum_append, Nat.mul_add]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

/-- The sum over `spreadOrder` as a sum over `List.range (d-1)`. -/
theorem sum_spreadOrder_eq {d : ℕ} (f : Fin d → ℕ) :
    ((spreadOrder d).map f).sum =
      ((List.range (d - 1)).map fun n => if h : n + 1 < d then f ⟨n + 1, h⟩ else 0).sum := by
  cases d with
  | zero => simp [spreadOrder_zero]
  | succ m =>
    rw [spreadOrder_succ, List.map_map, List.map_reverse, List.sum_reverse]
    congr 1
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.getElem_map, List.getElem_finRange, Function.comp_apply, List.getElem_range]
      rw [dif_pos (by simp at h2; omega)]
      congr 1

end SubNLogN.Machine.BridgeRed
