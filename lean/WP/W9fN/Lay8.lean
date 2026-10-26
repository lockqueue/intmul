import WP.W9fN.Loop

/-!
# WP.W9fN.Lay8 — the Nyquist core's host layout on `Loc 8 48`

Named stacks (the contract's): `IN = .inl 0`, `OUT = .inl 1`, `PQ = .inl 2` (`q`), `PH = .inl 3`
(`H`), `PMU = .inl 4` (`μ`), `PK = .inl 5` (`k`), `PA = .inl 6` (`a`), `PALT = .inl 7` (`alt`).
Scratch: variable `v` on `.inr v.idx` (`0..30`), the zPart store `ZS = .inr 31`, the macro
temporary `TMP = .inr 47`. IntLang's 20 scratch stacks: the 8 named stacks and `.inr 31..42`
(all restored by compiled code).
-/

namespace WP.W9fN

open TMFw TMFw.Contracts

/-- Host stacks of the Nyquist core. -/
abbrev HK : Type := Loc 8 48

theorem V.idx_lt31 (v : V) : v.idx < 31 := V.idx_lt v

/-- Variable stacks. -/
def vL (v : V) : HK := .inr ⟨v.idx, by have := V.idx_lt31 v; omega⟩

/-- IntLang scratch stacks. -/
def iS (j : Fin 20) : HK :=
  if h : j.1 < 8 then .inl ⟨j.1, h⟩ else .inr ⟨31 + (j.1 - 8), by omega⟩

theorem vL_injective : Function.Injective vL := by
  intro a b h
  simp only [vL, Sum.inr.injEq, Fin.mk.injEq] at h
  exact V.idx_injective h

theorem iS_injective : Function.Injective iS := by
  intro a b h
  unfold iS at h
  split_ifs at h with ha hb hb <;> simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq] at h <;> exact Fin.ext (by omega)

theorem vL_ne_iS (v : V) (j : Fin 20) : vL v ≠ iS j := by
  unfold vL iS
  have := V.idx_lt31 v
  split_ifs with h
  · simp
  · simp only [ne_eq, Sum.inr.injEq, Fin.mk.injEq]
    omega

/-- The layout. -/
def LN : Lay HK := ⟨vL, iS, vL_injective, iS_injective, vL_ne_iS⟩

/-- Named and private stacks. -/
def kIN : HK := .inl 0
def kOUT : HK := .inl 1
def kPQ : HK := .inl 2
def kPH : HK := .inl 3
def kPMU : HK := .inl 4
def kPK : HK := .inl 5
def kPA : HK := .inl 6
def kPALT : HK := .inl 7
def kZS : HK := .inr 31
def kTMP : HK := .inr 47

theorem vL_ne_inl (v : V) (i : Fin 8) : LN.varLoc v ≠ .inl i := by
  simp [LN, vL]

theorem vL_ne_ZS (v : V) : LN.varLoc v ≠ kZS := by
  have h1 := V.idx_lt31 v
  intro h
  have h2 : v.idx = (31 : Fin 48).val := congrArg Fin.val (Sum.inr.inj h)
  have h3 : (31 : Fin 48).val = 31 := rfl
  omega

theorem vL_ne_TMP (v : V) : LN.varLoc v ≠ kTMP := by
  have h1 := V.idx_lt31 v
  intro h
  have h2 : v.idx = (47 : Fin 48).val := congrArg Fin.val (Sum.inr.inj h)
  have h3 : (47 : Fin 48).val = 47 := rfl
  omega

#assert_std_axioms V.idx_lt31 vL_injective iS_injective vL_ne_iS vL_ne_inl vL_ne_ZS vL_ne_TMP

end WP.W9fN
