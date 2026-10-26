import WP.W9fF.HostL

/-!
# WP.W9fF.Layout — host stacks of the forward core

`HK = Loc 7 44`: the contract's 7 named stacks (`0` IN, `1` OUT, `2` q, `3` H, `4` μ, `5` a,
`6` c) and 44 scratch stacks:
* `.inr 0 … .inr 30`: the 31 variables (`vLoc v = .inr v.idx`), each mark-guarded;
* `.inr 31` PZ (zPart entries), `.inr 32` PH (zHom entries), `.inr 33` TMP (copy temporary);
* IntLang's 20 scratch stacks (`ilS`): the 7 named stacks and `.inr 31 … .inr 43` (their content
  is restored by every compiled block, so they may hold live data).
-/

namespace WP.W9fF

open TMFw TMFw.Lib TMFw.Contracts WP.W9fF.IL

/-- Host stacks of the forward core. -/
abbrev HK : Type := Loc 7 44

/-- Stack of variable `v`. -/
def vLoc (v : V) : HK := .inr ⟨v.idx, by have := V.idx_lt v; unfold V.card at this; omega⟩

/-- IntLang scratch stack `j`. -/
def ilS (j : Fin 20) : HK := if h : j.1 < 7 then .inl ⟨j.1, h⟩ else .inr ⟨j.1 + 24, by omega⟩

/-- Named and private stacks. -/
def inL : HK := .inl 0
def outL : HK := .inl 1
def qL : HK := .inl 2
def hL : HK := .inl 3
def muL : HK := .inl 4
def aL : HK := .inl 5
def cL : HK := .inl 6
def pzL : HK := .inr 31
def phL : HK := .inr 32
def tmpL : HK := .inr 33

theorem vLoc_injective : Function.Injective vLoc := by
  intro a b h
  simp only [vLoc, Sum.inr.injEq, Fin.mk.injEq] at h
  exact V.idx_injective h

theorem ilS_injective : Function.Injective ilS := by
  intro i j h
  unfold ilS at h
  split_ifs at h
  all_goals first
    | exact absurd h Sum.inl_ne_inr
    | exact absurd h Sum.inr_ne_inl
    | (simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq] at h; exact Fin.ext (by omega))

theorem vLoc_ne_ilS (v : V) (j : Fin 20) : vLoc v ≠ ilS j := by
  unfold vLoc ilS
  split_ifs with hj
  · exact Sum.inr_ne_inl
  · intro h
    simp only [Sum.inr.injEq, Fin.mk.injEq] at h
    have := V.idx_lt v
    unfold V.card at this
    omega

/-- The host layout of the forward core. -/
def lay : Lay HK where
  varLoc := vLoc
  ilScr := ilS
  var_inj := vLoc_injective
  scr_inj := ilS_injective
  disj := vLoc_ne_ilS

@[simp] theorem lay_varLoc : lay.varLoc = vLoc := rfl

theorem vLoc_ne_inl (v : V) (i : Fin 7) : vLoc v ≠ .inl i := Sum.inr_ne_inl

theorem vLoc_ne_inr {v : V} {j : Fin 44} (h : 31 ≤ j.1) : vLoc v ≠ .inr j := by
  intro e
  simp only [vLoc, Sum.inr.injEq] at e
  have h1 := V.idx_lt v
  unfold V.card at h1
  have h2 := congrArg Fin.val e
  simp only at h2
  omega

theorem vLoc_ne_inL (v : V) : vLoc v ≠ inL := vLoc_ne_inl v 0
theorem vLoc_ne_outL (v : V) : vLoc v ≠ outL := vLoc_ne_inl v 1
theorem vLoc_ne_pzL (v : V) : vLoc v ≠ pzL := vLoc_ne_inr (by decide)
theorem vLoc_ne_phL (v : V) : vLoc v ≠ phL := vLoc_ne_inr (by decide)
theorem vLoc_ne_tmpL (v : V) : vLoc v ≠ tmpL := vLoc_ne_inr (by decide)

/-- The non-variable host stacks during the run: IN, OUT, PZ, PH change, everything else is the
initial content `S`. -/
def XS (S : HK → List Sym) (inS outS pz ph : List Sym) : HK → List Sym :=
  Function.update (Function.update (Function.update (Function.update S inL inS) outL outS) pzL pz)
    phL ph

/-- Host state: variables per `env` (mark-guarded above `S`), IN/OUT/PZ/PH as given. -/
def hs (S : HK → List Sym) (env : V → ℤ) (inS outS pz ph : List Sym) : HK → List Sym :=
  lay.hst S (XS S inS outS pz ph) env

#assert_std_axioms vLoc_injective ilS_injective vLoc_ne_ilS lay_varLoc vLoc_ne_inl vLoc_ne_inr
  vLoc_ne_inL vLoc_ne_outL vLoc_ne_pzL vLoc_ne_phL vLoc_ne_tmpL

end WP.W9fF
