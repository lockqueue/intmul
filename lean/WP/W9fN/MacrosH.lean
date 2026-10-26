import WP.W9fN.Macros

/-!
# WP.W9fN.MacrosH — the entry / variable macros on `Lay.hst` host states

* `popEntry_runs`, `pushEntry_runs`: entries between a non-variable stack and two variables.
* `loadNat_runs`, `loadInt_runs`: copy a parameter from a non-variable stack into a variable.
* `initVars`, `initVars_runs`: from any host stacks `S`, reach `L.hst S S (fun _ => 0)` (every
  variable `0`, mark-guarded).
* `dropVars`, `dropVars_runs`: from `L.hst S0 X env`, drop every variable and its guard, reaching
  `L.hst0 S0 X` (`S0` on variable stacks, `X` elsewhere); cost `dCost env V.all`.
-/

namespace WP.W9fN

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fN.IL Computability

/-- Cost of dropping the variables `vs` (with their guards). -/
def dCost (env : V → ℤ) (vs : List V) : ℕ := (vs.map fun v => 2 * bitLen (env v).natAbs + 6).sum + 1

theorem V.all_nodup : V.all.Nodup :=
  (List.nodup_range).map_on (fun a ha b hb h => by
    rw [← V.idx_ofIdx (List.mem_range.mp ha), h, V.idx_ofIdx (List.mem_range.mp hb)])

theorem termOK_guard (l : List Sym) : TermOK (Sym.mark :: l) := TermOK.cons rfl l

namespace Lay

variable {K : Type} [DecidableEq K] (L : Lay K) {O : Type} [DecidableEq O] (I : O → OpImpl)

/-! ## Entries and parameters -/

omit [DecidableEq O] in
theorem popEntry_runs {src tmp : K} (hsrc : ∀ v, L.varLoc v ≠ src) (htmp : ∀ v, L.varLoc v ≠ tmp)
    (hst : src ≠ tmp) {v1 v2 : V} (h12 : v1 ≠ v2) (S0 X : K → List Sym) (env : V → ℤ)
    (y : ℤ × ℤ) (rest : List Sym) (hX : X src = entrySyms y ++ rest) :
    RunsS (hM I (popEntry src (L.varLoc v1) (L.varLoc v2) tmp)) (L.hst S0 X env)
      (L.hst S0 (Function.update X src rest) (Function.update (Function.update env v1 y.1) v2 y.2))
      (9 * bitLen y.1.natAbs + 9 * bitLen y.2.natAbs + 2 * bitLen (env v1).natAbs +
        2 * bitLen (env v2).natAbs + 46) := by
  have h := hM_runs I (fun r => ⟨_, popEntry_eval (Ne.symm (hsrc v1)) (Ne.symm (hsrc v2)) hst
    (L.var_inj.ne h12) (htmp v1) (htmp v2) y (env v1) (env v2) _ _ rest (L.hst S0 X env)
    (termOK_guard _) (termOK_guard _) (by rw [L.hst_other S0 X env hsrc]; exact hX)
    (L.hst_var S0 X env v1) (L.hst_var S0 X env v2) r⟩) le_rfl
  refine RunsS.of_eq h ?_ le_rfl
  rw [L.hst_upd_X S0 X env hsrc, ← L.hst_upd_env, ← L.hst_upd_env]

omit [DecidableEq O] in
theorem pushEntry_runs {dst tmp : K} (hdst : ∀ v, L.varLoc v ≠ dst) (htmp : ∀ v, L.varLoc v ≠ tmp)
    (hdt : dst ≠ tmp) (v1 v2 : V) (S0 X : K → List Sym) (env : V → ℤ) :
    RunsS (hM I (pushEntry (L.varLoc v1) (L.varLoc v2) dst tmp)) (L.hst S0 X env)
      (L.hst S0 (Function.update X dst (entrySyms (env v1, env v2) ++ X dst)) env)
      (7 * bitLen (env v1).natAbs + 7 * bitLen (env v2).natAbs + 26) := by
  have h := hM_runs I (fun r => ⟨_, pushEntry_eval (hdst v1) (hdst v2) (htmp v1) (htmp v2) hdt
    (env v1) (env v2) _ _ (L.hst S0 X env) (termOK_guard _) (termOK_guard _)
    (L.hst_var S0 X env v1) (L.hst_var S0 X env v2) r⟩) le_rfl
  refine RunsS.of_eq h ?_ le_rfl
  rw [L.hst_other S0 X env hdst, L.hst_upd_X S0 X env hdst]

omit [DecidableEq O] in
theorem loadNat_runs {src tmp : K} (hsrc : ∀ v, L.varLoc v ≠ src) (htmp : ∀ v, L.varLoc v ≠ tmp)
    (hst : src ≠ tmp) (v : V) (S0 X : K → List Sym) (env : V → ℤ) (n : ℕ) (rs : List Sym)
    (hrs : TermOK rs) (hX : X src = natSyms n ++ rs) :
    RunsS (hM I (loadNat src (L.varLoc v) tmp)) (L.hst S0 X env)
      (L.hst S0 X (Function.update env v (n : ℤ)))
      (2 * bitLen (env v).natAbs + 7 * bitLen n + 13) := by
  have h := hM_runs I (fun r => ⟨_, loadNat_eval (Ne.symm (hsrc v)) hst (htmp v) n (env v) _ rs
    (L.hst S0 X env) (termOK_guard _) hrs (by rw [L.hst_other S0 X env hsrc]; exact hX)
    (L.hst_var S0 X env v) r⟩) le_rfl
  refine RunsS.of_eq h ?_ le_rfl
  rw [← L.hst_upd_env]

omit [DecidableEq O] in
theorem loadInt_runs {src tmp : K} (hsrc : ∀ v, L.varLoc v ≠ src) (htmp : ∀ v, L.varLoc v ≠ tmp)
    (hst : src ≠ tmp) (v : V) (S0 X : K → List Sym) (env : V → ℤ) (z : ℤ) (rs : List Sym)
    (hrs : TermOK rs) (hX : X src = intSyms z ++ rs) :
    RunsS (hM I (loadInt src (L.varLoc v) tmp)) (L.hst S0 X env)
      (L.hst S0 X (Function.update env v z))
      (2 * bitLen (env v).natAbs + 7 * bitLen z.natAbs + 17) := by
  have h := hM_runs I (fun r => ⟨_, loadInt_eval (Ne.symm (hsrc v)) hst (htmp v) z (env v) _ rs
    (L.hst S0 X env) (termOK_guard _) hrs (by rw [L.hst_other S0 X env hsrc]; exact hX)
    (L.hst_var S0 X env v) r⟩) le_rfl
  refine RunsS.of_eq h ?_ le_rfl
  rw [← L.hst_upd_env]

/-! ## Creating and dropping the variables -/

/-- Push `pos` over `mark` on every listed variable stack (value `0` above a guard). -/
def initVars : List V → SProg K
  | [] => skip
  | v :: vs => .seq (pushC (L.varLoc v) .mark) (.seq (pushC (L.varLoc v) .pos) (initVars vs))

/-- Stacks after `initVars vs`. -/
def iF (vs : List V) (S : K → List Sym) (k : K) : List Sym :=
  match L.varOf k with
  | some v => if v ∈ vs then Sym.pos :: Sym.mark :: S k else S k
  | none => S k

theorem initVars_eval (r : Option Sym) : ∀ (vs : List V) (S : K → List Sym), vs.Nodup →
    Eval [] (L.initVars vs) ⟨r, S⟩ ⟨r, L.iF vs S⟩ (2 * vs.length + 1)
  | [], S, _ => by
    refine (skip_eval [] _).of_eq ?_ rfl
    congr 1
    funext k
    unfold iF
    cases L.varOf k <;> simp
  | v :: vs, S, hnd => by
    have hv : v ∉ vs := (List.nodup_cons.mp hnd).1
    have hnd' := (List.nodup_cons.mp hnd).2
    have e1 := pushC_eval' [] (L.varLoc v) .mark r S
    have e2 := pushC_eval' [] (L.varLoc v) .pos r
      (Function.update S (L.varLoc v) (.mark :: S (L.varLoc v)))
    rw [Function.update_idem, Function.update_self] at e2
    have e3 := initVars_eval r vs
      (Function.update S (L.varLoc v) (.pos :: .mark :: S (L.varLoc v))) hnd'
    refine (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    unfold iF
    cases hk : L.varOf k with
    | none =>
      simp only
      rw [Function.update_of_ne (Ne.symm (L.varOf_none hk v))]
    | some w =>
      have hw := L.loc_of_varOf hk
      subst hw
      simp only
      by_cases hwv : w = v
      · subst hwv
        simp [hv]
      · rw [Function.update_of_ne (L.var_inj.ne hwv)]
        simp [hwv]

theorem iF_all (S : K → List Sym) : L.iF V.all S = L.hst S S (fun _ => 0) := by
  funext k
  unfold iF hst
  cases L.varOf k with
  | none => rfl
  | some v =>
    simp only
    rw [if_pos (V.mem_all v)]
    simp [intSyms, sgnSym, natSyms, encodeNat_zero]

omit [DecidableEq O] in
theorem initVars_runs (S : K → List Sym) :
    RunsS (hM I (L.initVars V.all)) S (L.hst S S (fun _ => 0)) (2 * V.all.length + 1) :=
  hM_runs I (fun r => ⟨r, (L.initVars_eval r V.all S V.all_nodup).of_eq (by rw [L.iF_all]) rfl⟩)
    le_rfl

/-- Drop every listed variable value and its guard. -/
def dropVars : List V → SProg K
  | [] => skip
  | v :: vs => .seq (dropInt (L.varLoc v)) (.seq (popR (L.varLoc v)) (dropVars vs))

/-- Stacks after `dropVars vs`. -/
def dF (S0 : K → List Sym) (vs : List V) (S : K → List Sym) (k : K) : List Sym :=
  match L.varOf k with
  | some v => if v ∈ vs then S0 k else S k
  | none => S k

theorem dropVars_eval (S0 : K → List Sym) (env : V → ℤ) :
    ∀ (vs : List V) (S : K → List Sym) (r : Option Sym), vs.Nodup →
      (∀ v ∈ vs, S (L.varLoc v) = intSyms (env v) ++ Sym.mark :: S0 (L.varLoc v)) →
      ∃ r', Eval [] (L.dropVars vs) ⟨r, S⟩ ⟨r', L.dF S0 vs S⟩ (dCost env vs)
  | [], S, r, _, _ => by
    refine ⟨r, (skip_eval [] _).of_eq ?_ (by simp [dCost])⟩
    congr 1
    funext k
    unfold dF
    cases L.varOf k <;> simp
  | v :: vs, S, r, hnd, hS => by
    have hv : v ∉ vs := (List.nodup_cons.mp hnd).1
    have hnd' := (List.nodup_cons.mp hnd).2
    have e1 := dropInt_eval [] (L.varLoc v) r (env v) (Sym.mark :: S0 (L.varLoc v)) S
      (termOK_guard _) (hS v (List.mem_cons_self ..))
    have e2 := popR_eval' [] (L.varLoc v) (Sym.mark :: S0 (L.varLoc v)).head?
      (Function.update S (L.varLoc v) (Sym.mark :: S0 (L.varLoc v))) Sym.mark (S0 (L.varLoc v))
      (Function.update_self _ _ _)
    rw [Function.update_idem] at e2
    obtain ⟨r', e3⟩ := dropVars_eval S0 env vs
      (Function.update S (L.varLoc v) (S0 (L.varLoc v))) (some .mark) hnd' (fun w hw => by
        have hwv : w ≠ v := fun e => hv (e ▸ hw)
        rw [Function.update_of_ne (L.var_inj.ne hwv)]
        exact hS w (List.mem_cons_of_mem _ hw))
    refine ⟨r', (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ ?_⟩
    · congr 1
      funext k
      unfold dF
      cases hk : L.varOf k with
      | none =>
        simp only
        rw [Function.update_of_ne (Ne.symm (L.varOf_none hk v))]
      | some w =>
        have hw := L.loc_of_varOf hk
        subst hw
        simp only
        by_cases hwv : w = v
        · subst hwv
          simp [hv]
        · rw [Function.update_of_ne (L.var_inj.ne hwv)]
          simp [hwv]
    · simp only [dCost, List.map_cons, List.sum_cons]
      omega

/-- Host stacks after dropping all variables: `S0` on variable stacks, `X` elsewhere. -/
def hst0 (S0 X : K → List Sym) (k : K) : List Sym :=
  match L.varOf k with
  | some _ => S0 k
  | none => X k

theorem dF_all (S0 X : K → List Sym) (env : V → ℤ) :
    L.dF S0 V.all (L.hst S0 X env) = L.hst0 S0 X := by
  funext k
  unfold dF hst0 hst
  cases L.varOf k with
  | none => rfl
  | some v =>
    simp only
    rw [if_pos (V.mem_all v)]

theorem hst0_eq (S0 X : K → List Sym) (h : ∀ v, X (L.varLoc v) = S0 (L.varLoc v)) :
    L.hst0 S0 X = X := by
  funext k
  unfold hst0
  cases hk : L.varOf k with
  | none => rfl
  | some v =>
    simp only
    rw [← L.loc_of_varOf hk, h v]

omit [DecidableEq O] in
theorem dropVars_runs (S0 X : K → List Sym) (env : V → ℤ) :
    RunsS (hM I (L.dropVars V.all)) (L.hst S0 X env) (L.hst0 S0 X) (dCost env V.all) := by
  refine hM_runs I (fun r => ?_) le_rfl
  obtain ⟨r', e⟩ := L.dropVars_eval S0 env V.all (L.hst S0 X env) r V.all_nodup
    (fun v _ => L.hst_var S0 X env v)
  exact ⟨r', e.of_eq (by rw [L.dF_all]) rfl⟩

end Lay

#assert_std_axioms V.all_nodup termOK_guard Lay.popEntry_runs Lay.pushEntry_runs Lay.loadNat_runs
  Lay.loadInt_runs Lay.initVars_eval Lay.iF_all Lay.initVars_runs Lay.dropVars_eval Lay.dF_all
  Lay.hst0_eq Lay.dropVars_runs

end WP.W9fN
