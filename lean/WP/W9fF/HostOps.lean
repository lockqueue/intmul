import WP.W9fF.Layout
import WP.W9fF.Loop
import WP.W9fF.Closed

/-!
# WP.W9fF.HostOps — the host operations of the forward core on `hs` states

`hs S env inS outS pz ph` (Layout) is the host state: variables per `env` above guards, IN, OUT,
PZ, PH as given, every other stack as in `S`. This file restates the generic host lemmas
(`HostL`, `MacrosH`) for the concrete stacks:
* `slc I p` (a compiled SL block on the host) and `slc_runs`;
* entry pops from IN / PZ / PH into two variables, entry pushes onto PZ / PH / OUT;
* guard pushes / pops on PZ and PH.
-/

namespace WP.W9fF

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W9fF.IL

/-! ## Distinctness of the fixed stacks -/

theorem inL_ne_outL : inL ≠ outL := by decide
theorem inL_ne_pzL : inL ≠ pzL := by decide
theorem inL_ne_phL : inL ≠ phL := by decide
theorem outL_ne_pzL : outL ≠ pzL := by decide
theorem outL_ne_phL : outL ≠ phL := by decide
theorem pzL_ne_phL : pzL ≠ phL := by decide
theorem inL_ne_tmpL : inL ≠ tmpL := by decide
theorem outL_ne_tmpL : outL ≠ tmpL := by decide
theorem pzL_ne_tmpL : pzL ≠ tmpL := by decide
theorem phL_ne_tmpL : phL ≠ tmpL := by decide
theorem qL_ne_tmpL : qL ≠ tmpL := by decide
theorem hL_ne_tmpL : hL ≠ tmpL := by decide
theorem muL_ne_tmpL : muL ≠ tmpL := by decide
theorem aL_ne_tmpL : aL ≠ tmpL := by decide
theorem cL_ne_tmpL : cL ≠ tmpL := by decide

theorem nv_inL : ∀ v, lay.varLoc v ≠ inL := vLoc_ne_inL
theorem nv_outL : ∀ v, lay.varLoc v ≠ outL := vLoc_ne_outL
theorem nv_pzL : ∀ v, lay.varLoc v ≠ pzL := vLoc_ne_pzL
theorem nv_phL : ∀ v, lay.varLoc v ≠ phL := vLoc_ne_phL
theorem nv_tmpL : ∀ v, lay.varLoc v ≠ tmpL := vLoc_ne_tmpL
theorem nv_inl (i : Fin 7) : ∀ v, lay.varLoc v ≠ .inl i := fun v => vLoc_ne_inl v i

/-! ## The non-variable contents `XS` -/

section XS

variable (S : HK → List Sym) (i o p h : List Sym)

@[simp] theorem XS_in : XS S i o p h inL = i := by
  simp [XS, inL_ne_outL, inL_ne_pzL, inL_ne_phL]

@[simp] theorem XS_out : XS S i o p h outL = o := by
  simp [XS, outL_ne_pzL, outL_ne_phL]

@[simp] theorem XS_pz : XS S i o p h pzL = p := by
  simp [XS, pzL_ne_phL]

@[simp] theorem XS_ph : XS S i o p h phL = h := by simp [XS]

theorem XS_upd_in (i' : List Sym) : Function.update (XS S i o p h) inL i' = XS S i' o p h := by
  funext k
  by_cases hk : k = inL
  · subst hk
    simp
  · simp only [Function.update_of_ne hk, XS, Function.update_apply, hk, if_false]

theorem XS_upd_out (o' : List Sym) : Function.update (XS S i o p h) outL o' = XS S i o' p h := by
  funext k
  by_cases hk : k = outL
  · subst hk
    simp
  · simp only [Function.update_of_ne hk, XS, Function.update_apply, hk, if_false]

theorem XS_upd_pz (p' : List Sym) : Function.update (XS S i o p h) pzL p' = XS S i o p' h := by
  funext k
  by_cases hk : k = pzL
  · subst hk
    simp
  · simp only [Function.update_of_ne hk, XS, Function.update_apply, hk, if_false]

theorem XS_upd_ph (h' : List Sym) : Function.update (XS S i o p h) phL h' = XS S i o p h' := by
  funext k
  by_cases hk : k = phL
  · subst hk
    simp
  · simp only [Function.update_of_ne hk, XS, Function.update_apply, hk, if_false]

theorem XS_inl (j : Fin 7) (h2 : 2 ≤ j.1) : XS S i o p h (.inl j) = S (.inl j) := by
  have e1 : (Sum.inl j : HK) ≠ inL := by
    intro e; simp only [inL, Sum.inl.injEq] at e; subst e; simp at h2
  have e2 : (Sum.inl j : HK) ≠ outL := by
    intro e; simp only [outL, Sum.inl.injEq] at e; subst e; simp at h2
  have e3 : (Sum.inl j : HK) ≠ pzL := Sum.inl_ne_inr
  have e4 : (Sum.inl j : HK) ≠ phL := Sum.inl_ne_inr
  simp [XS, e1, e2, e3, e4]

theorem XS_self : XS S (S inL) (S outL) (S pzL) (S phL) = S := by
  simp [XS, Function.update_eq_self]

end XS

/-! ## Compiled blocks and macros on `hs` states -/

variable (I : Op → OpImpl)

/-- A compiled straight-line block on the host. -/
def slc (p : SL) : Prog HK (fun _ => Sym) (GReg I) := (p.compile I).mapStk lay.emb

theorem slc_runs (κ : Op → ℤ → ℤ → ℕ) (hok : ∀ o, BinOK (I o) (Op.sem o) (κ o)) (p : SL)
    (S : HK → List Sym) (env : V → ℤ) (i o pz ph : List Sym) :
    RunsS (slc I p) (hs S env i o pz ph) (hs S (ev p env) i o pz ph) (p.cost Op.sem κ env) :=
  lay.hst_compile I κ hok p S _ env

theorem popIn_runs {v1 v2 : V} (h12 : v1 ≠ v2) (S : HK → List Sym) (env : V → ℤ) (y : ℤ × ℤ)
    (rest o pz ph : List Sym) :
    RunsS (hM I (popEntry inL (vLoc v1) (vLoc v2) tmpL)) (hs S env (entrySyms y ++ rest) o pz ph)
      (hs S (Function.update (Function.update env v1 y.1) v2 y.2) rest o pz ph)
      (9 * bitLen y.1.natAbs + 9 * bitLen y.2.natAbs + 2 * bitLen (env v1).natAbs +
        2 * bitLen (env v2).natAbs + 46) := by
  have h := lay.popEntry_runs I nv_inL nv_tmpL inL_ne_tmpL h12 S
    (XS S (entrySyms y ++ rest) o pz ph) env y rest (XS_in _ _ _ _ _)
  rwa [XS_upd_in] at h

theorem popPz_runs {v1 v2 : V} (h12 : v1 ≠ v2) (S : HK → List Sym) (env : V → ℤ) (y : ℤ × ℤ)
    (i o rest ph : List Sym) :
    RunsS (hM I (popEntry pzL (vLoc v1) (vLoc v2) tmpL)) (hs S env i o (entrySyms y ++ rest) ph)
      (hs S (Function.update (Function.update env v1 y.1) v2 y.2) i o rest ph)
      (9 * bitLen y.1.natAbs + 9 * bitLen y.2.natAbs + 2 * bitLen (env v1).natAbs +
        2 * bitLen (env v2).natAbs + 46) := by
  have h := lay.popEntry_runs I nv_pzL nv_tmpL pzL_ne_tmpL h12 S
    (XS S i o (entrySyms y ++ rest) ph) env y rest (XS_pz _ _ _ _ _)
  rwa [XS_upd_pz] at h

theorem popPh_runs {v1 v2 : V} (h12 : v1 ≠ v2) (S : HK → List Sym) (env : V → ℤ) (y : ℤ × ℤ)
    (i o pz rest : List Sym) :
    RunsS (hM I (popEntry phL (vLoc v1) (vLoc v2) tmpL)) (hs S env i o pz (entrySyms y ++ rest))
      (hs S (Function.update (Function.update env v1 y.1) v2 y.2) i o pz rest)
      (9 * bitLen y.1.natAbs + 9 * bitLen y.2.natAbs + 2 * bitLen (env v1).natAbs +
        2 * bitLen (env v2).natAbs + 46) := by
  have h := lay.popEntry_runs I nv_phL nv_tmpL phL_ne_tmpL h12 S
    (XS S i o pz (entrySyms y ++ rest)) env y rest (XS_ph _ _ _ _ _)
  rwa [XS_upd_ph] at h

theorem pushPz_runs (v1 v2 : V) (S : HK → List Sym) (env : V → ℤ) (i o pz ph : List Sym) :
    RunsS (hM I (pushEntry (vLoc v1) (vLoc v2) pzL tmpL)) (hs S env i o pz ph)
      (hs S env i o (entrySyms (env v1, env v2) ++ pz) ph)
      (7 * bitLen (env v1).natAbs + 7 * bitLen (env v2).natAbs + 26) := by
  have h := lay.pushEntry_runs I nv_pzL nv_tmpL pzL_ne_tmpL v1 v2 S (XS S i o pz ph) env
  rwa [XS_pz, XS_upd_pz] at h

theorem pushPh_runs (v1 v2 : V) (S : HK → List Sym) (env : V → ℤ) (i o pz ph : List Sym) :
    RunsS (hM I (pushEntry (vLoc v1) (vLoc v2) phL tmpL)) (hs S env i o pz ph)
      (hs S env i o pz (entrySyms (env v1, env v2) ++ ph))
      (7 * bitLen (env v1).natAbs + 7 * bitLen (env v2).natAbs + 26) := by
  have h := lay.pushEntry_runs I nv_phL nv_tmpL phL_ne_tmpL v1 v2 S (XS S i o pz ph) env
  rwa [XS_ph, XS_upd_ph] at h

theorem pushOut_runs (v1 v2 : V) (S : HK → List Sym) (env : V → ℤ) (i o pz ph : List Sym) :
    RunsS (hM I (pushEntry (vLoc v1) (vLoc v2) outL tmpL)) (hs S env i o pz ph)
      (hs S env i (entrySyms (env v1, env v2) ++ o) pz ph)
      (7 * bitLen (env v1).natAbs + 7 * bitLen (env v2).natAbs + 26) := by
  have h := lay.pushEntry_runs I nv_outL nv_tmpL outL_ne_tmpL v1 v2 S (XS S i o pz ph) env
  rwa [XS_out, XS_upd_out] at h

/-- Push a symbol on a non-variable host stack. -/
theorem pushC_hst_runs {k : HK} (hk : ∀ v, lay.varLoc v ≠ k) (x : Sym) (S0 X : HK → List Sym)
    (env : V → ℤ) :
    RunsS (hM I (pushC k x)) (lay.hst S0 X env) (lay.hst S0 (Function.update X k (x :: X k)) env)
      1 := by
  refine hM_runs I (fun r => ⟨r, (pushC_eval' [] k x r (lay.hst S0 X env)).of_eq ?_ rfl⟩) le_rfl
  rw [lay.hst_other S0 X env hk, lay.hst_upd_X S0 X env hk]

/-- Pop a symbol from a non-variable host stack. -/
theorem popR_hst_runs {k : HK} (hk : ∀ v, lay.varLoc v ≠ k) (x : Sym) (l : List Sym)
    (S0 X : HK → List Sym) (env : V → ℤ) (hX : X k = x :: l) :
    RunsS (hM I (popR k)) (lay.hst S0 X env) (lay.hst S0 (Function.update X k l) env) 1 := by
  refine hM_runs I (fun r => ⟨some x, (popR_eval' [] k r (lay.hst S0 X env) x l
    (by rw [lay.hst_other S0 X env hk, hX])).of_eq ?_ rfl⟩) le_rfl
  rw [lay.hst_upd_X S0 X env hk]

theorem slc_closed (hI : ∀ o, (I o).P.Closed) (p : SL) : (slc I p).Closed :=
  WP.W7k2.freeBelow_mapStk _ _ 0 (compile_closed I hI p)

#assert_std_axioms inL_ne_outL XS_in XS_out XS_pz XS_ph XS_upd_in XS_upd_out XS_upd_pz XS_upd_ph
  XS_inl XS_self slc_runs popIn_runs popPz_runs popPh_runs pushPz_runs pushPh_runs pushOut_runs
  pushC_hst_runs popR_hst_runs slc_closed

end WP.W9fF
