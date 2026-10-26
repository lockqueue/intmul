/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedCyc
import SubNLogN.Machine.Walsh.PosPermSchedDefs

/-!
# Schedule compiler cycle scan, part 2 (`Machine/Walsh/PosPermSchedCycleAScan.lean`): cycle index and length

On the compiler's stacks `Stk` (`PosPermSchedState.lean`), with the table `PT = utab (finVals π)`:
* `scanProg w`: a first-hit scan. From `y = s` it walks `m` steps `y := π y` (`stepPi`); at step
  `k` it compares `y` with the target register `tgtR w` (`x` for `w = true`, `b` for `w = false`)
  and records the first hit index `k` in `outR w` (`idx`, resp. `len`): the result is
  `findAcc (hitP π s t) m` (default `0` when there is no hit, as in `cycleIdx`, `cycleLen`).
  Registers `y kc kk fnd f t1 t2 t3 tmp v lc` and the raw stack `U` are scratch (empty before and
  after).
* `idxLenProg`: `y := b`; index scan; `y := b`; `y := π y`; length scan; `len := len + 1`.

**Scope (honest summary).** Proved: `runs_scanProg`, `runs_idxLenProg` (exact `Runs` rules),
`closed_idxLenProg`, and the frozen target `cycIdxLen_holds : CycIdxLenStmt`
(`PosPermSchedDefs.lean`), with no hypotheses.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.CycA

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.Walsh.PosPermSchedAux

/-! ## Registers of the two scans -/

/-- The target register of scan `w`: `x` (index scan) or `b` (length scan). -/
def tgtR (w : Bool) : RegN := cond w .x .b

/-- The output register of scan `w`: `idx` (index scan) or `len` (length scan). -/
def outR (w : Bool) : RegN := cond w .idx .len

@[simp] theorem tgtR_eq_iff (w : Bool) (q : RegN) :
    tgtR w = q ↔ (w = true ∧ q = .x) ∨ (w = false ∧ q = .b) := by
  cases w <;> cases q <;> decide

@[simp] theorem eq_tgtR_iff (w : Bool) (q : RegN) :
    q = tgtR w ↔ (w = true ∧ q = .x) ∨ (w = false ∧ q = .b) := by
  cases w <;> cases q <;> decide

@[simp] theorem outR_eq_iff (w : Bool) (q : RegN) :
    outR w = q ↔ (w = true ∧ q = .idx) ∨ (w = false ∧ q = .len) := by
  cases w <;> cases q <;> decide

@[simp] theorem eq_outR_iff (w : Bool) (q : RegN) :
    q = outR w ↔ (w = true ∧ q = .idx) ∨ (w = false ∧ q = .len) := by
  cases w <;> cases q <;> decide

@[simp] theorem tgtR_ne_outR (w : Bool) : tgtR w ≠ outR w := by cases w <;> decide

@[simp] theorem outR_ne_tgtR (w : Bool) : outR w ≠ tgtR w := by cases w <;> decide

/-- `f^[n + 1] x = f (f^[n] x)` (stated with `n + 1` for `simp`). -/
theorem iter_succ (f : ℕ → ℕ) (n x : ℕ) : f^[n + 1] x = f (f^[n] x) :=
  Function.iterate_succ_apply' f n x

/-! ## Programs -/

/-- The first-hit predicate of a scan from `s` towards `t`: `k ↦ [π^k s = t]`. -/
def hitP {m : ℕ} (π : Fin m → Fin m) (s t : ℕ) : ℕ → Bool := fun k => decide ((piN π)^[k] s = t)

/-- The test of one scan step: `f := [y = tgt]`; on a hit `out := kk`, `fnd := 1`; `f := 0`. -/
def testBlk (w : Bool) : SProg Stk :=
  .seq (eqF (rg .y) (rg (tgtR w)) (rg .f) (rg .t1) (rg .t2) (rg .t3) (rg .tmp))
    (.seq (ifNE (rg .f) (.seq (copyU (rg .kk) (rg (outR w)) (rg .tmp)) (incR (rg .fnd))) skip)
      (clearU (rg .f)))

/-- One scan step: the test unless `fnd` is set; then `y := π y`, `kk := kk + 1`. -/
def scanBody (w : Bool) : SProg Stk :=
  .seq (ifNE (rg .fnd) skip (testBlk w)) (.seq stepPi (incR (rg .kk)))

/-- The scan: `kc := m`; `kc` times `scanBody w`; then `y, kk, fnd := 0`. -/
def scanProg (w : Bool) : SProg Stk :=
  .seq (copyU (rg .m) (rg .kc) (rg .tmp))
    (.seq (forDown (rg .kc) (scanBody w))
      (.seq (clearU (rg .y)) (.seq (clearU (rg .kk)) (clearU (rg .fnd)))))

/-- (b): `y := b`; index scan; `y := b`; `y := π y`; length scan; `len := len + 1`. -/
def idxLenProg : SProg Stk :=
  .seq (copyU (rg .b) (rg .y) (rg .tmp)) (.seq (scanProg true)
    (.seq (copyU (rg .b) (rg .y) (rg .tmp)) (.seq stepPi (.seq (scanProg false)
      (incR (rg .len))))))

theorem closed_idxLenProg : idxLenProg.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, idxLenProg, scanProg, scanBody, testBlk, eqF, ltF, stepPi,
    lookup, ifNE, copyU, forDown, whileNE, whileTop, skipEntry, moveToks, copyToks, drainTo,
    clearU, moveU, incR, mv, popR, peekR, pushR, pushC, skip]

/-! ## The test block -/

theorem una_eq_nil_iff_cyc (n : ℕ) : una n = [] ↔ n = 0 := by
  cases n <;> simp [una_succ]

theorem runs_testHit (w : Bool) (G : Stk → List Sym) (a i : ℕ)
    (hy : G (rg .y) = una a) (htg : G (rg (tgtR w)) = una a) (hkk : G (rg .kk) = una i)
    (ho : G (rg (outR w)) = []) (hfnd : G (rg .fnd) = []) (hf : G (rg .f) = [])
    (h1 : G (rg .t1) = []) (h2 : G (rg .t2) = []) (h3 : G (rg .t3) = [])
    (htmp : G (rg .tmp) = []) :
    Runs (testBlk w) G
      (Function.update (Function.update G (rg (outR w)) (una i)) (rg .fnd) (una 1))
      (fun _ => True) (a * 100 + i * 10 + 120) := by
  have cE := runs_eqF (x := rg .y) (y := rg (tgtR w)) (f := rg .f) (t1 := rg .t1) (t2 := rg .t2)
    (t3 := rg .t3) (tmp := rg .tmp) (by cases w <;> decide) G a a 0 hy htg (by rw [hf]; rfl)
    h1 h2 h3 htmp
  rw [if_pos (rfl : a = a)] at cE
  have cC := runs_copyU (src := rg .kk) (dst := rg (outR w)) (tmp := rg .tmp)
    (by cases w <;> decide) (by decide) (by cases w <;> decide)
    (Function.update G (rg .f) (una (0 + 1))) i 0 (by simp [hkk])
    (by simp [ho]) (by simp [htmp])
  have cI := runs_incR (rg .fnd) (Function.update (Function.update G (rg .f) (una (0 + 1)))
    (rg (outR w)) (una (0 + i))) 0 (by simp [hfnd])
  have cIf := runs_ifNE_pos (k := rg .f) (q := skip) (by simp [una_eq_nil_iff_cyc])
    (runs_seq' cC cI le_rfl)
  have cCl := runs_clearU (rg .f) (Function.update (Function.update (Function.update G (rg .f)
    (una (0 + 1))) (rg (outR w)) (una (0 + i))) (rg .fnd) (una (0 + 1))) (0 + 1)
    (by simp)
  refine runs_seq' cE (runs_seq' cIf (runs_weak cCl ?_ le_rfl) le_rfl) ?_
  · clear cE cC cI cIf cCl
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · omega

theorem runs_testMiss (w : Bool) (G : Stk → List Sym) (a b : ℕ) (hab : a ≠ b)
    (hy : G (rg .y) = una a) (htg : G (rg (tgtR w)) = una b) (hf : G (rg .f) = [])
    (h1 : G (rg .t1) = []) (h2 : G (rg .t2) = []) (h3 : G (rg .t3) = [])
    (htmp : G (rg .tmp) = []) :
    Runs (testBlk w) G G (fun _ => True) ((a + b) * 50 + 110) := by
  have cE := runs_eqF (x := rg .y) (y := rg (tgtR w)) (f := rg .f) (t1 := rg .t1) (t2 := rg .t2)
    (t3 := rg .t3) (tmp := rg .tmp) (by cases w <;> decide) G a b 0 hy htg (by rw [hf]; rfl)
    h1 h2 h3 htmp
  rw [if_neg hab] at cE
  have cIf := runs_ifNE_neg (k := rg .f)
    (p := .seq (copyU (rg .kk) (rg (outR w)) (rg .tmp)) (incR (rg .fnd)))
    (S := Function.update G (rg .f) (una (0 + 0))) (by simp)
    (runs_skip _)
  have cCl := runs_clearU (rg .f) (Function.update G (rg .f) (una (0 + 0))) (0 + 0)
    (by simp)
  refine runs_seq' cE (runs_seq' cIf (runs_weak cCl ?_ le_rfl) le_rfl) ?_
  · clear cE cIf cCl
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · omega

/-- The common tail of a scan step: `y := π y`, `kk := kk + 1`. -/
theorem runs_tail {m : ℕ} (π : Fin m → Fin m) (H : Stk → List Sym) (yv i : ℕ) (hyv : yv < m)
    (hPT : H (rs .PT) = utab (finVals π)) (hy : H (rg .y) = una yv) (hk : H (rg .kk) = una i)
    (hv : H (rg .v) = []) (hU : H (rs .U) = []) (hlc : H (rg .lc) = [])
    (htmp : H (rg .tmp) = []) :
    Runs (.seq stepPi (incR (rg .kk))) H
      (Function.update (Function.update H (rg .y) (una (piN π yv))) (rg .kk) (una (i + 1)))
      (fun _ => True) (40 * (m + 1) ^ 3 + 1) := by
  have c1 := runs_stepPi π H yv hyv hPT hy hv hU hlc htmp
  have c2 := runs_incR (rg .kk) (Function.update H (rg .y) (una (piN π yv))) i
    (by simp [hk])
  exact runs_seq' c1 c2 le_rfl

/-! ## One scan step -/

/-- The loop state of scan `w` from `s` towards `t` after `i` steps. -/
def scanSt {m : ℕ} (π : Fin m → Fin m) (S : Stk → List Sym) (w : Bool) (s t i : ℕ) :
    Stk → List Sym :=
  Function.update (Function.update (Function.update (Function.update S (rg .y)
    (una ((piN π)^[i] s))) (rg .kk) (una i)) (rg (outR w)) (una (findAcc (hitP π s t) i)))
    (rg .fnd) (una (foundAcc (hitP π s t) i))

theorem runs_scanBody {m : ℕ} (π : Fin m → Fin m) (w : Bool) (S : Stk → List Sym)
    (s t c i : ℕ) (hi : i < m) (hs : s < m) (ht : t < m)
    (hPT : S (rs .PT) = utab (finVals π)) (htg : S (rg (tgtR w)) = una t)
    (hf : S (rg .f) = []) (h1 : S (rg .t1) = []) (h2 : S (rg .t2) = []) (h3 : S (rg .t3) = [])
    (htmp : S (rg .tmp) = []) (hv : S (rg .v) = []) (hlc : S (rg .lc) = [])
    (hU : S (rs .U) = []) :
    Runs (scanBody w) (Function.update (scanSt π S w s t i) (rg .kc) (una c))
      (Function.update (scanSt π S w s t (i + 1)) (rg .kc) (una c))
      (fun _ => True) (160 * (m + 1) ^ 3) := by
  have hyl : (piN π)^[i] s < m := piN_iterate_lt π i s hs
  have hX : m + 1 ≤ (m + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hfl := foundAcc_le (hitP π s t) i
  have cB := runs_tail π (Function.update (scanSt π S w s t i) (rg .kc) (una c))
    ((piN π)^[i] s) i hyl (by simp [scanSt, hPT])
    (by simp [scanSt]) (by simp [scanSt])
    (by simp [scanSt, hv]) (by simp [scanSt, hU])
    (by simp [scanSt, hlc]) (by simp [scanSt, htmp])
  by_cases hfd : foundAcc (hitP π s t) i = 1
  · -- already found: skip the test
    have cA := runs_ifNE_pos (k := rg .fnd) (p := skip) (q := testBlk w)
      (S := Function.update (scanSt π S w s t i) (rg .kc) (una c))
      (by simp [scanSt, hfd, una_eq_nil_iff_cyc]) (runs_skip _)
    refine runs_seq' cA (runs_weak cB ?_ le_rfl) ?_
    · clear cA cB
      have e1 : findAcc (hitP π s t) (i + 1) = findAcc (hitP π s t) i := by
        rw [findAcc_succ, if_pos hfd]
      have e2 : foundAcc (hitP π s t) (i + 1) = foundAcc (hitP π s t) i := by
        rw [foundAcc_succ, if_pos hfd, hfd]
      simp only [scanSt, e1, e2, iter_succ]
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all)
    · generalize (m + 1) ^ 3 = X at hX ⊢
      omega
  · have hfa0 : foundAcc (hitP π s t) i = 0 := by omega
    have hfi0 : findAcc (hitP π s t) i = 0 := findAcc_of_not_found _ i hfd
    by_cases hyt : (piN π)^[i] s = t
    · -- first hit at step `i`
      have hP : hitP π s t i = true := by simp [hitP, hyt]
      have cT := runs_testHit w (Function.update (scanSt π S w s t i) (rg .kc) (una c)) t i
        (by simp [scanSt, hyt])
        (by simp [scanSt, htg]) (by simp [scanSt])
        (by simp [scanSt, hfi0])
        (by simp [scanSt, hfa0])
        (by simp [scanSt, hf]) (by simp [scanSt, h1])
        (by simp [scanSt, h2]) (by simp [scanSt, h3])
        (by simp [scanSt, htmp])
      have cA := runs_ifNE_neg (k := rg .fnd) (p := skip)
        (by simp [scanSt, hfa0]) cT
      have cB' := runs_tail π (Function.update (Function.update (Function.update
        (scanSt π S w s t i) (rg .kc) (una c)) (rg (outR w)) (una i)) (rg .fnd) (una 1))
        ((piN π)^[i] s) i hyl (by simp [scanSt, hPT])
        (by simp [scanSt]) (by simp [scanSt])
        (by simp [scanSt, hv]) (by simp [scanSt, hU])
        (by simp [scanSt, hlc])
        (by simp [scanSt, htmp])
      refine runs_seq' cA (runs_weak cB' ?_ le_rfl) ?_
      · clear cA cB cB' cT
        have e1 : findAcc (hitP π s t) (i + 1) = i := by
          rw [findAcc_succ, hfa0, if_neg (by omega), if_pos hP]
        have e2 : foundAcc (hitP π s t) (i + 1) = 1 := by
          rw [foundAcc_succ, hfa0, if_neg (by omega), if_pos hP]
        simp only [scanSt, e1, e2, hfa0, hfi0, iter_succ]
        funext k
        simp only [Function.update_apply]
        split_ifs <;> (try subst_vars) <;> (try simp_all)
      · generalize (m + 1) ^ 3 = X at hX ⊢
        omega
    · -- no hit at step `i`
      have hP : hitP π s t i = false := by simp [hitP, hyt]
      have cT := runs_testMiss w (Function.update (scanSt π S w s t i) (rg .kc) (una c))
        ((piN π)^[i] s) t hyt (by simp [scanSt])
        (by simp [scanSt, htg])
        (by simp [scanSt, hf]) (by simp [scanSt, h1])
        (by simp [scanSt, h2]) (by simp [scanSt, h3])
        (by simp [scanSt, htmp])
      have cA := runs_ifNE_neg (k := rg .fnd) (p := skip)
        (by simp [scanSt, hfa0]) cT
      refine runs_seq' cA (runs_weak cB ?_ le_rfl) ?_
      · clear cA cB cT
        have e1 : findAcc (hitP π s t) (i + 1) = 0 := by
          rw [findAcc_succ, hfa0, if_neg (by omega), if_neg (by simp [hP])]
        have e2 : foundAcc (hitP π s t) (i + 1) = 0 := by
          rw [foundAcc_succ, hfa0, if_neg (by omega), if_neg (by simp [hP])]
        simp only [scanSt, e1, e2, hfa0, hfi0, iter_succ]
        funext k
        simp only [Function.update_apply]
        split_ifs <;> (try subst_vars) <;> (try simp_all)
      · generalize (m + 1) ^ 3 = X at hX ⊢
        omega

/-! ## The scan -/

theorem runs_scanProg {m : ℕ} (π : Fin m → Fin m) (w : Bool) (S : Stk → List Sym) (s t : ℕ)
    (hs : s < m) (ht : t < m)
    (hPT : S (rs .PT) = utab (finVals π)) (hm : S (rg .m) = una m)
    (hy : S (rg .y) = una s) (htg : S (rg (tgtR w)) = una t) (ho : S (rg (outR w)) = [])
    (hkc : S (rg .kc) = []) (hkk : S (rg .kk) = []) (hfnd : S (rg .fnd) = [])
    (hf : S (rg .f) = []) (h1 : S (rg .t1) = []) (h2 : S (rg .t2) = []) (h3 : S (rg .t3) = [])
    (htmp : S (rg .tmp) = []) (hv : S (rg .v) = []) (hlc : S (rg .lc) = [])
    (hU : S (rs .U) = []) :
    Runs (scanProg w) S
      (Function.update (Function.update S (rg .y) []) (rg (outR w))
        (una (findAcc (hitP π s t) m)))
      (fun _ => True) (200 * (m + 1) ^ 4) := by
  have c1 := runs_copyU (src := rg .m) (dst := rg .kc) (tmp := rg .tmp) (by decide) (by decide)
    (by decide) S m 0 hm (by rw [hkc]; rfl) htmp
  rw [Nat.zero_add] at c1
  have c2 := runs_forDown (c := rg .kc) (p := scanBody w) (fun i => scanSt π S w s t i)
    (160 * (m + 1) ^ 3) m
    (fun i hi => runs_scanBody π w S s t (m - 1 - i) i hi hs ht hPT htg hf h1 h2 h3 htmp hv hlc
      hU)
  have e0 : scanSt π S w s t 0 = S := by
    funext k
    simp only [scanSt, Function.iterate_zero, id_eq, findAcc_zero, foundAcc_zero,
      Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  simp only [e0] at c2
  have c3 := runs_clearU (rg .y) (Function.update (scanSt π S w s t m) (rg .kc) [])
    ((piN π)^[m] s) (by simp [scanSt])
  have c4 := runs_clearU (rg .kk) (Function.update (Function.update (scanSt π S w s t m)
    (rg .kc) []) (rg .y) []) m (by simp [scanSt])
  have c5 := runs_clearU (rg .fnd) (Function.update (Function.update (Function.update
    (scanSt π S w s t m) (rg .kc) []) (rg .y) []) (rg .kk) []) (foundAcc (hitP π s t) m)
    (by simp [scanSt])
  refine runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_seq' c4 (runs_weak c5 ?_ le_rfl)
    le_rfl) le_rfl) le_rfl) ?_
  · clear c1 c2 c3 c4 c5 e0
    funext k
    simp only [scanSt, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · have hyl : (piN π)^[m] s < m := piN_iterate_lt π m s hs
    have hfl := foundAcc_le (hitP π s t) m
    have hX : m + 1 ≤ (m + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have e4 : (m + 1) ^ 4 = m * (m + 1) ^ 3 + (m + 1) ^ 3 := by ring
    rw [e4]
    generalize (m + 1) ^ 3 = X at hX ⊢
    have e5 : m * (160 * X + 3) = 160 * (m * X) + 3 * m := by ring
    rw [e5]
    omega

/-! ## (b) Index and length -/

theorem runs_idxLenProg {m : ℕ} (π : Fin m → Fin m) (x bb : ℕ) (S : Stk → List Sym)
    (hx : x < m) (hb : bb < m)
    (hPT : S (rs .PT) = utab (finVals π)) (hm : S (rg .m) = una m) (hxr : S (rg .x) = una x)
    (hbr : S (rg .b) = una bb) (hc : ScrClean S [.m, .xc, .x, .b, .d, .K]) :
    Runs idxLenProg S
      (Function.update (Function.update S (rg .idx) (una (findAcc (hitP π bb x) m))) (rg .len)
        (una (findAcc (hitP π (piN π bb) bb) m + 1)))
      (fun _ => True) (500 * (m + 1) ^ 4) := by
  obtain ⟨hr, hU, -, -, -, -, -⟩ := hc
  have hy : S (rg .y) = [] := hr .y (by decide)
  have hidx : S (rg .idx) = [] := hr .idx (by decide)
  have hlen : S (rg .len) = [] := hr .len (by decide)
  have hkc : S (rg .kc) = [] := hr .kc (by decide)
  have hkk : S (rg .kk) = [] := hr .kk (by decide)
  have hfnd : S (rg .fnd) = [] := hr .fnd (by decide)
  have hf : S (rg .f) = [] := hr .f (by decide)
  have h1 : S (rg .t1) = [] := hr .t1 (by decide)
  have h2 : S (rg .t2) = [] := hr .t2 (by decide)
  have h3 : S (rg .t3) = [] := hr .t3 (by decide)
  have htmp : S (rg .tmp) = [] := hr .tmp (by decide)
  have hv : S (rg .v) = [] := hr .v (by decide)
  have hlc : S (rg .lc) = [] := hr .lc (by decide)
  clear hr
  have hpb : piN π bb < m := piN_lt π bb hb
  -- `y := b`
  have c1 := runs_copyU (src := rg .b) (dst := rg .y) (tmp := rg .tmp) (by decide) (by decide)
    (by decide) S bb 0 hbr (by rw [hy]; rfl) htmp
  rw [Nat.zero_add] at c1
  -- the index scan
  have c2 := runs_scanProg π true (Function.update S (rg .y) (una bb)) bb x hb hx
    (by simp [hPT]) (by simp [hm])
    (by simp) (by simp [tgtR, hxr])
    (by simp [outR, hidx]) (by simp [hkc])
    (by simp [hkk]) (by simp [hfnd])
    (by simp [hf]) (by simp [h1])
    (by simp [h2]) (by simp [h3])
    (by simp [htmp]) (by simp [hv])
    (by simp [hlc]) (by simp [hU])
  have e2 : Function.update (Function.update (Function.update S (rg .y) (una bb)) (rg .y) [])
      (rg (outR true)) (una (findAcc (hitP π bb x) m)) =
      Function.update S (rg .idx) (una (findAcc (hitP π bb x) m)) := by
    funext k
    simp only [outR, cond_true, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  rw [e2] at c2
  -- `y := b`, `y := π y`
  have c3 := runs_copyU (src := rg .b) (dst := rg .y) (tmp := rg .tmp) (by decide) (by decide)
    (by decide) (Function.update S (rg .idx) (una (findAcc (hitP π bb x) m))) bb 0
    (by simp [hbr]) (by simp [hy])
    (by simp [htmp])
  rw [Nat.zero_add] at c3
  have c4 := runs_stepPi π (Function.update (Function.update S (rg .idx)
    (una (findAcc (hitP π bb x) m))) (rg .y) (una bb)) bb hb
    (by simp [hPT]) (by simp)
    (by simp [hv]) (by simp [hU])
    (by simp [hlc]) (by simp [htmp])
  rw [Function.update_idem] at c4
  -- the length scan
  have c5 := runs_scanProg π false (Function.update (Function.update S (rg .idx)
    (una (findAcc (hitP π bb x) m))) (rg .y) (una (piN π bb))) (piN π bb) bb hpb hb
    (by simp [hPT]) (by simp [hm])
    (by simp) (by simp [tgtR, hbr])
    (by simp [outR, hlen]) (by simp [hkc])
    (by simp [hkk]) (by simp [hfnd])
    (by simp [hf]) (by simp [h1])
    (by simp [h2]) (by simp [h3])
    (by simp [htmp]) (by simp [hv])
    (by simp [hlc]) (by simp [hU])
  -- `len := len + 1`
  have c6 := runs_incR (rg .len) (Function.update (Function.update (Function.update
    (Function.update S (rg .idx) (una (findAcc (hitP π bb x) m))) (rg .y) (una (piN π bb)))
    (rg .y) []) (rg (outR false)) (una (findAcc (hitP π (piN π bb) bb) m)))
    (findAcc (hitP π (piN π bb) bb) m) (by simp [outR])
  refine runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_seq' c4 (runs_seq' c5
    (runs_weak c6 ?_ le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) ?_
  · clear c1 c2 c3 c4 c5 c6 e2
    funext k
    simp only [outR, cond_false, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · have hX : m + 1 ≤ (m + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have e4 : (m + 1) ^ 4 = m * (m + 1) ^ 3 + (m + 1) ^ 3 := by ring
    rw [e4]
    generalize (m + 1) ^ 3 = X at hX ⊢
    omega

end SubNLogN.Machine.Walsh.PosPermSchedAux.CycA

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

/-- **(b) The cycle index and length (frozen target `CycIdxLenStmt`), proved.** -/
theorem cycIdxLen_holds : CycIdxLenStmt :=
  ⟨CycA.idxLenProg, CycA.closed_idxLenProg, 500, 4,
    fun _ π x bb S hx hb hPT hm hxr hbr hc =>
      CycA.runs_idxLenProg π x bb S hx hb hPT hm hxr hbr hc⟩

end SubNLogN.Machine.Walsh.PosPermSchedAux
