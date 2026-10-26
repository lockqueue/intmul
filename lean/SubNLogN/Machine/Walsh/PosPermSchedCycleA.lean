/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedCyc
import SubNLogN.Machine.Walsh.PosPermSchedDefs

/-!
# Schedule compiler cycle base, part 1 (`Machine/Walsh/PosPermSchedCycleA.lean`): the cycle base

On the compiler's stacks `Stk` (`PosPermSchedState.lean`), with the table `PT = utab (finVals π)`:
`baseProg` computes `b := baseAcc π x m` (`= cycleBase π x`, `cycleBase_val`): `b := x`, `y := x`,
then `m` times `b := min b y; y := π y` (`minStep`, `stepPi` of `PosPermSchedCyc.lean`), then
`y := 0`. It uses the registers `b y kc f t1 t2 tmp v lc` and the raw stack `U`.

**Scope (honest summary).** Proved: `runs_baseProg` (exact `Runs` rule, cost
`200 (m + 1)^4`), `closed_baseProg`, and the frozen target `cycBase_holds : CycBaseStmt`
(`PosPermSchedDefs.lean`), with no hypotheses.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.CycA

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.Walsh.PosPermSchedAux

/-! ## The base walk -/

/-- One step of the base walk: `b := min b y`, then `y := π y`. -/
def baseBody : SProg Stk := .seq minStep stepPi

/-- `b := baseAcc π x m`: `b := x`, `y := x`, `kc := m`; `kc` times `baseBody`; `y := 0`. -/
def baseProg : SProg Stk :=
  .seq (copyU (rg .x) (rg .b) (rg .tmp)) (.seq (copyU (rg .x) (rg .y) (rg .tmp))
    (.seq (copyU (rg .m) (rg .kc) (rg .tmp)) (.seq (forDown (rg .kc) baseBody)
      (clearU (rg .y)))))

theorem closed_baseProg : baseProg.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, baseProg, baseBody, minStep, stepPi, lookup, ltF, ifNE,
    copyU, forDown, whileNE, whileTop, skipEntry, moveToks, copyToks, drainTo, clearU, moveU,
    incR, mv, popR, peekR, pushR, pushC, skip]

/-- The loop state of the base walk after `i` steps. -/
def baseSt {m : ℕ} (π : Fin m → Fin m) (S : Stk → List Sym) (x i : ℕ) : Stk → List Sym :=
  Function.update (Function.update S (rg .b) (una (baseAcc π x i))) (rg .y)
    (una ((piN π)^[i] x))

theorem runs_baseBody {m : ℕ} (π : Fin m → Fin m) (S : Stk → List Sym) (x c i : ℕ) (hx : x < m)
    (hPT : S (rs .PT) = utab (finVals π)) (hf : S (rg .f) = []) (h1 : S (rg .t1) = [])
    (h2 : S (rg .t2) = []) (htmp : S (rg .tmp) = []) (hv : S (rg .v) = [])
    (hlc : S (rg .lc) = []) (hU : S (rs .U) = []) :
    Runs baseBody (Function.update (baseSt π S x i) (rg .kc) (una c))
      (Function.update (baseSt π S x (i + 1)) (rg .kc) (una c))
      (fun _ => True) (120 * (m + 1) ^ 3) := by
  have hyl : (piN π)^[i] x < m := piN_iterate_lt π i x hx
  have hbl : baseAcc π x i < m := baseAcc_lt π x i hx
  have c1 := runs_minStep (Function.update (baseSt π S x i) (rg .kc) (una c)) ((piN π)^[i] x)
    (baseAcc π x i) (by simp [baseSt])
    (by simp [baseSt]) (by simp [baseSt, hf])
    (by simp [baseSt, h1]) (by simp [baseSt, h2])
    (by simp [baseSt, htmp])
  have c2 := runs_stepPi π (Function.update (Function.update (baseSt π S x i) (rg .kc) (una c))
    (rg .b) (una (min (baseAcc π x i) ((piN π)^[i] x)))) ((piN π)^[i] x) hyl
    (by simp [baseSt, hPT]) (by simp [baseSt])
    (by simp [baseSt, hv]) (by simp [baseSt, hU])
    (by simp [baseSt, hlc]) (by simp [baseSt, htmp])
  refine runs_seq' c1 (runs_weak c2 ?_ le_rfl) ?_
  · clear c1 c2
    rw [baseSt, baseSt, baseAcc_succ, Function.iterate_succ_apply']
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · have hX : m + 1 ≤ (m + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    generalize (m + 1) ^ 3 = X at hX ⊢
    omega

theorem runs_baseProg {m : ℕ} (π : Fin m → Fin m) (x : ℕ) (S : Stk → List Sym) (hx : x < m)
    (hPT : S (rs .PT) = utab (finVals π)) (hm : S (rg .m) = una m) (hxr : S (rg .x) = una x)
    (hc : ScrClean S [.m, .xc, .x, .d, .K]) :
    Runs baseProg S (Function.update S (rg .b) (una (baseAcc π x m))) (fun _ => True)
      (200 * (m + 1) ^ 4) := by
  obtain ⟨hr, hU, -, -, -, -, -⟩ := hc
  have hb : S (rg .b) = [] := hr .b (by decide)
  have hy : S (rg .y) = [] := hr .y (by decide)
  have hkc : S (rg .kc) = [] := hr .kc (by decide)
  have hf : S (rg .f) = [] := hr .f (by decide)
  have h1 : S (rg .t1) = [] := hr .t1 (by decide)
  have h2 : S (rg .t2) = [] := hr .t2 (by decide)
  have htmp : S (rg .tmp) = [] := hr .tmp (by decide)
  have hv : S (rg .v) = [] := hr .v (by decide)
  have hlc : S (rg .lc) = [] := hr .lc (by decide)
  clear hr
  have c1 := runs_copyU (src := rg .x) (dst := rg .b) (tmp := rg .tmp) (by decide) (by decide)
    (by decide) S x 0 hxr (by rw [hb]; rfl) htmp
  have c2 := runs_copyU (src := rg .x) (dst := rg .y) (tmp := rg .tmp) (by decide) (by decide)
    (by decide) (Function.update S (rg .b) (una (0 + x))) x 0
    (by simp [hxr]) (by simp [hy])
    (by simp [htmp])
  have c3 := runs_copyU (src := rg .m) (dst := rg .kc) (tmp := rg .tmp) (by decide) (by decide)
    (by decide) (Function.update (Function.update S (rg .b) (una (0 + x))) (rg .y) (una (0 + x)))
    m 0 (by simp [hm]) (by simp [hkc])
    (by simp [htmp])
  have c4 := runs_forDown (c := rg .kc) (p := baseBody) (fun i => baseSt π S x i)
    (120 * (m + 1) ^ 3) m
    (fun i _ => runs_baseBody π S x (m - 1 - i) i hx hPT hf h1 h2 htmp hv hlc hU)
  have e0 : Function.update (baseSt π S x 0) (rg .kc) (una m) =
      Function.update (Function.update (Function.update S (rg .b) (una (0 + x))) (rg .y)
        (una (0 + x))) (rg .kc) (una (0 + m)) := by
    simp only [baseSt, baseAcc_zero, Function.iterate_zero, id_eq, Nat.zero_add]
  rw [e0] at c4
  have c5 := runs_clearU (rg .y) (Function.update (baseSt π S x m) (rg .kc) [])
    ((piN π)^[m] x) (by simp [baseSt])
  refine runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_seq' c4 (runs_weak c5 ?_ le_rfl)
    le_rfl) le_rfl) le_rfl) ?_
  · clear c1 c2 c3 c4 c5
    funext k
    simp only [baseSt, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · have hyl : (piN π)^[m] x < m := piN_iterate_lt π m x hx
    have hX : m + 1 ≤ (m + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have e4 : (m + 1) ^ 4 = m * (m + 1) ^ 3 + (m + 1) ^ 3 := by ring
    rw [e4]
    generalize (m + 1) ^ 3 = X at hX ⊢
    have e5 : m * (120 * X + 3) = 120 * (m * X) + 3 * m := by ring
    rw [e5]
    omega

end SubNLogN.Machine.Walsh.PosPermSchedAux.CycA

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

/-- **(a) The cycle base (frozen target `CycBaseStmt`), proved.** -/
theorem cycBase_holds : CycBaseStmt :=
  ⟨CycA.baseProg, CycA.closed_baseProg, 200, 4,
    fun _ π x S hx hPT hm hxr hc => CycA.runs_baseProg π x S hx hPT hm hxr hc⟩

end SubNLogN.Machine.Walsh.PosPermSchedAux
