/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.PosPermSchedDefs
import SubNLogN.Machine.Walsh.PosPermSchedCyc

/-!
# Schedule compiler cycle push (`Machine/Walsh/PosPermSchedCycleB.lean`): the involution values of a point

Work package (c) of the cycle phase of the runtime schedule compiler of Theorem 5.8
(`PosPermSchedStmt`, `PosPermLeaf.lean`; frozen sub-statements in `PosPermSchedDefs.lean`).
For the current point, with its cycle base `b = bb`, index `idx = i` and length `len = n` held in
unary registers, push `(piN π)^[(n - i) % n] bb` onto `I0T` and `(piN π)^[(n + 1 - i) % n] bb`
onto `I1T` (for `bb = cycleBase π x`, `i = cycleIdx π x`, `n = cycleLen π x` these are
`invol0 π x` and `invol1 π x`, by `invol0_val`, `invol1_val` in `PosPermSchedCycMath.lean`).

* `offProg one`: `e0 := (n + [one] - i) % n` (unary `copyU`, `incR`, `subU`, `divmodU`);
* `runs_iterPi`: `forDown e0 stepPi` iterates `y := piN π y` exactly `e0` times;
* `pushPiProg T`: `y := b`, then `e0` steps of `π`, then push `y` onto the raw stack `T`;
* `cycPushProg := offProg false; pushPiProg I0T; offProg true; pushPiProg I1T`.

**Scope (honest summary).** Everything here is proved: `cycPush_holds : CycPushStmt` (the frozen
statement of `PosPermSchedDefs.lean`, with its bounds `n ≤ m`, `i ≤ m`), with cost
`3400 (m + 1)^4`. The registers `b`, `idx`, `len` and every other stack are restored; the
temporaries used (`e0 q1 q2 q3 q4 f t1 t2 t3 tmp y v lc`, raw `U`) are empty before and after.
-/

namespace SubNLogN.Machine.Walsh.PosPermSchedAux.CycB

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine SubNLogN.Math.Walsh

/-! ## Programs -/

/-- `e0 := (n + [one] - i) % n` for `n = len`, `i = idx` (both kept); the temporaries
`q1 q2 q3 q4 f t1 t2 t3 tmp` are empty before and after. -/
def offProg (one : Bool) : SProg Stk :=
  .seq (copyU (rg .len) (rg .q1) (rg .tmp)) (.seq (if one then incR (rg .q1) else skip)
    (.seq (subU (rg .q1) (rg .idx) (rg .q2) (rg .t1) (rg .t2) (rg .tmp))
      (.seq (divmodU (rg .q2) (rg .len) (rg .q3) (rg .e0) (rg .q4) (rg .f) (rg .t1) (rg .t2)
          (rg .t3) (rg .tmp))
        (.seq (clearU (rg .q3)) (.seq (clearU (rg .q2)) (clearU (rg .q1)))))))

/-- Push `(piN π)^[e0] b` onto the raw stack `T`: `y := b`, `e0` steps `y := π y` (`e0` is
consumed), push `y` (`y` emptied). -/
def pushPiProg (T : RawN) : SProg Stk :=
  .seq (copyU (rg .b) (rg .y) (rg .tmp))
    (.seq (forDown (rg .e0) stepPi) (pushEntry (rs T) (rg .y)))

/-- **The program of work package (c).** -/
def cycPushProg : SProg Stk :=
  .seq (offProg false) (.seq (pushPiProg .I0T) (.seq (offProg true) (pushPiProg .I1T)))

theorem closed_cycPushProg : cycPushProg.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, cycPushProg, offProg, pushPiProg, stepPi, lookup, copyU,
    subU, divmodU, eqF, ltF, ifNE, forDown, whileNE, whileTop, skipEntry, moveToks, copyToks,
    drainTo, clearU, moveU, incR, pushEntry, mv, popR, peekR, pushR, pushC, skip]

/-! ## The offsets -/

/-- **Offset.** `e0 := (n + [one] - i) % n`; `len = n ≥ 1`, `idx = i` and every other stack
restored. -/
theorem runs_offProg (one : Bool) (S : Stk → List Sym) (i n : ℕ) (hn : 1 ≤ n)
    (hidx : S (rg .idx) = una i) (hlen : S (rg .len) = una n) (he0 : S (rg .e0) = [])
    (hq1 : S (rg .q1) = []) (hq2 : S (rg .q2) = []) (hq3 : S (rg .q3) = [])
    (hq4 : S (rg .q4) = []) (hf : S (rg .f) = []) (h1 : S (rg .t1) = []) (h2 : S (rg .t2) = [])
    (h3 : S (rg .t3) = []) (htmp : S (rg .tmp) = []) :
    Runs (offProg one) S (Function.update S (rg .e0) (una ((n + one.toNat - i) % n)))
      (fun _ => True) ((n + i + 2) ^ 2 * 400) := by
  have hc : one.toNat ≤ 1 := by cases one <;> simp
  have c1 := runs_copyU (src := rg .len) (dst := rg .q1) (tmp := rg .tmp) (by decide) (by decide)
    (by decide) S n 0 hlen (by rw [hq1]; rfl) htmp
  rw [Nat.zero_add] at c1
  have c2 : Runs (if one then incR (rg .q1) else skip) (Function.update S (rg .q1) (una n))
      (Function.update S (rg .q1) (una (n + one.toNat))) (fun _ => True) 1 := by
    cases one
    · simpa using runs_skip (Function.update S (rg .q1) (una n))
    · have h := runs_incR (rg .q1) (Function.update S (rg .q1) (una n)) n (by simp)
      simpa [Function.update_idem] using h
  set S2 := Function.update S (rg .q1) (una (n + one.toNat)) with hS2
  have c3 := runs_subU (x := rg .q1) (y := rg .idx) (dst := rg .q2) (t1 := rg .t1)
    (t2 := rg .t2) (tmp := rg .tmp) (by decide) S2 (n + one.toNat) i 0 (by simp [hS2])
    (by simp [hS2, Function.update_apply, hidx]) (by simp [hS2, Function.update_apply, hq2])
    (by simp [hS2, Function.update_apply, h1]) (by simp [hS2, Function.update_apply, h2])
    (by simp [hS2, Function.update_apply, htmp])
  rw [Nat.zero_add] at c3
  set a := n + one.toNat - i with ha
  set S3 := Function.update S2 (rg .q2) (una a) with hS3
  have c4 := runs_divmodU (x := rg .q2) (y := rg .len) (q := rg .q3) (r := rg .e0)
    (cnt := rg .q4) (f := rg .f) (t1 := rg .t1) (t2 := rg .t2) (t3 := rg .t3) (tmp := rg .tmp)
    (by decide) S3 a n 0 (by omega) (by simp [hS3])
    (by simp [hS3, hS2, Function.update_apply, hlen])
    (by simp [hS3, hS2, Function.update_apply, hq3])
    (by simp [hS3, hS2, Function.update_apply, he0])
    (by simp [hS3, hS2, Function.update_apply, hq4])
    (by simp [hS3, hS2, Function.update_apply, hf])
    (by simp [hS3, hS2, Function.update_apply, h1])
    (by simp [hS3, hS2, Function.update_apply, h2])
    (by simp [hS3, hS2, Function.update_apply, h3])
    (by simp [hS3, hS2, Function.update_apply, htmp])
  rw [Nat.zero_add] at c4
  set S4 := Function.update (Function.update S3 (rg .q3) (una (a / n))) (rg .e0) (una (a % n))
    with hS4
  have c5 := runs_clearU (rg .q3) S4 (a / n) (by simp [hS4, Function.update_apply])
  have c6 := runs_clearU (rg .q2) (Function.update S4 (rg .q3) []) a
    (by simp [hS4, hS3, Function.update_apply])
  have c7 := runs_clearU (rg .q1) (Function.update (Function.update S4 (rg .q3) []) (rg .q2) [])
    (n + one.toNat) (by simp [hS4, hS3, hS2, Function.update_apply])
  refine runs_seq' c1 (runs_seq' c2 (runs_seq' c3 (runs_seq' c4 (runs_seq' c5
    (runs_seq' c6 (runs_weak c7 ?_ le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) ?_
  · clear c1 c2 c3 c4 c5 c6 c7
    funext k
    simp only [hS4, hS3, hS2, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · have ha1 : a ≤ n + 1 := by omega
    have hd : a / n ≤ a := Nat.div_le_self a n
    have e1 : (a + 1) * (n + 1) ≤ (n + i + 2) * (n + i + 2) := Nat.mul_le_mul (by omega) (by omega)
    have e3 : 2 * (n + i + 2) ≤ (n + i + 2) * (n + i + 2) := Nat.mul_le_mul_right _ (by omega)
    rw [sq]
    omega

/-! ## Iterating `π` and pushing -/

/-- **`E` steps of `π`.** `forDown e0 stepPi` runs `y := piN π y` exactly `E` times (`e0 = una E`
is consumed). -/
theorem runs_iterPi {m : ℕ} (π : Fin m → Fin m) (S : Stk → List Sym) (j E : ℕ) (hj : j < m)
    (hPT : S (rs .PT) = utab (finVals π)) (hy : S (rg .y) = una j) (he : S (rg .e0) = una E)
    (hv : S (rg .v) = []) (hU : S (rs .U) = []) (hlc : S (rg .lc) = [])
    (htmp : S (rg .tmp) = []) :
    Runs (forDown (rg .e0) stepPi) S
      (Function.update (Function.update S (rg .y) (una ((piN π)^[E] j))) (rg .e0) [])
      (fun _ => True) (E * (40 * (m + 1) ^ 3 + 3) + 2) := by
  have hit : ∀ k, (piN π)^[k] j < m := fun k => piN_iterate_lt π k j hj
  have L := runs_forDown (c := rg .e0) (p := stepPi)
    (fun k => Function.update S (rg .y) (una ((piN π)^[k] j))) (40 * (m + 1) ^ 3) E
    (fun k _ => by
      have hs := runs_stepPi π (Function.update (Function.update S (rg .y)
        (una ((piN π)^[k] j))) (rg .e0) (una (E - 1 - k))) ((piN π)^[k] j) (hit k)
        (by simp [Function.update_apply, hPT]) (by simp [Function.update_apply])
        (by simp [Function.update_apply, hv]) (by simp [Function.update_apply, hU])
        (by simp [Function.update_apply, hlc]) (by simp [Function.update_apply, htmp])
      refine runs_weak hs ?_ le_rfl
      rw [Function.iterate_succ_apply' (piN π) k j]
      funext x
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all))
  have e0 : Function.update (Function.update S (rg .y) (una ((piN π)^[0] j))) (rg .e0) (una E)
      = S := by
    rw [Function.iterate_zero_apply, ← hy, ← he, Function.update_eq_self, Function.update_eq_self]
  rw [e0] at L
  exact L

/-- **Push one involution value.** `T := ent ((piN π)^[E] bb) ++ T` (for `T ∉ {PT, U}`); `e0` is
consumed, `b` and every other stack restored. -/
theorem runs_pushPiProg {m : ℕ} (π : Fin m → Fin m) (T : RawN) (S : Stk → List Sym) (bb E : ℕ)
    (hbb : bb < m) (hPT : S (rs .PT) = utab (finVals π)) (hb : S (rg .b) = una bb)
    (he : S (rg .e0) = una E) (hy : S (rg .y) = []) (hv : S (rg .v) = []) (hU : S (rs .U) = [])
    (hlc : S (rg .lc) = []) (htmp : S (rg .tmp) = []) :
    Runs (pushPiProg T) S
      (Function.update (Function.update S (rs T) (ent ((piN π)^[E] bb) ++ S (rs T))) (rg .e0) [])
      (fun _ => True) (E * (40 * (m + 1) ^ 3 + 3) + 14 * m + 11) := by
  have c1 := runs_copyU (src := rg .b) (dst := rg .y) (tmp := rg .tmp) (by decide) (by decide)
    (by decide) S bb 0 hb (by rw [hy]; rfl) htmp
  rw [Nat.zero_add] at c1
  have c2 := runs_iterPi π (Function.update S (rg .y) (una bb)) bb E hbb
    (by simp [Function.update_apply, hPT]) (by simp) (by simp [Function.update_apply, he])
    (by simp [Function.update_apply, hv]) (by simp [Function.update_apply, hU])
    (by simp [Function.update_apply, hlc]) (by simp [Function.update_apply, htmp])
  have c3 := runs_pushEntry (T := rs T) (v := rg .y) (by simp)
    (Function.update (Function.update (Function.update S (rg .y) (una bb)) (rg .y)
      (una ((piN π)^[E] bb))) (rg .e0) []) ((piN π)^[E] bb) (by simp [Function.update_apply])
  refine runs_seq' c1 (runs_seq' c2 (runs_weak c3 ?_ le_rfl) le_rfl) ?_
  · clear c1 c2 c3
    funext k
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all [ent])
  · have := piN_iterate_lt π E bb hbb
    omega

/-! ## The work package -/

/-- **Work package (c).** From the current point's `b = bb`, `idx = i`, `len = n`, push
`(piN π)^[(n - i) % n] bb` onto `I0T` and `(piN π)^[(n + 1 - i) % n] bb` onto `I1T`; every other
stack is restored. -/
theorem runs_cycPushProg {m : ℕ} (π : Fin m → Fin m) (bb i n : ℕ) (S : Stk → List Sym)
    (hbb : bb < m) (hn : 1 ≤ n) (hnm : n ≤ m) (him : i ≤ m)
    (hPT : S (rs .PT) = utab (finVals π)) (hb : S (rg .b) = una bb)
    (hidx : S (rg .idx) = una i) (hlen : S (rg .len) = una n)
    (hcl : ScrClean S [.m, .xc, .x, .b, .idx, .len, .d, .K]) :
    Runs cycPushProg S
      (Function.update (Function.update S (rs .I0T)
          (ent ((piN π)^[(n - i) % n] bb) ++ S (rs .I0T))) (rs .I1T)
        (ent ((piN π)^[(n + 1 - i) % n] bb) ++ S (rs .I1T)))
      (fun _ => True) (3400 * (m + 1) ^ 4) := by
  obtain ⟨hreg, hU, -, -, -, -, -⟩ := hcl
  have he0 : S (rg .e0) = [] := hreg .e0 (by decide)
  have hq1 : S (rg .q1) = [] := hreg .q1 (by decide)
  have hq2 : S (rg .q2) = [] := hreg .q2 (by decide)
  have hq3 : S (rg .q3) = [] := hreg .q3 (by decide)
  have hq4 : S (rg .q4) = [] := hreg .q4 (by decide)
  have hf : S (rg .f) = [] := hreg .f (by decide)
  have h1 : S (rg .t1) = [] := hreg .t1 (by decide)
  have h2 : S (rg .t2) = [] := hreg .t2 (by decide)
  have h3 : S (rg .t3) = [] := hreg .t3 (by decide)
  have htmp : S (rg .tmp) = [] := hreg .tmp (by decide)
  have hy : S (rg .y) = [] := hreg .y (by decide)
  have hv : S (rg .v) = [] := hreg .v (by decide)
  have hlc : S (rg .lc) = [] := hreg .lc (by decide)
  clear hreg
  have o0 := runs_offProg false S i n hn hidx hlen he0 hq1 hq2 hq3 hq4 hf h1 h2 h3 htmp
  rw [Bool.toNat_false, Nat.add_zero] at o0
  set E0 := (n - i) % n with hE0
  set A1 := Function.update S (rg .e0) (una E0) with hA1
  have p0 := runs_pushPiProg π .I0T A1 bb E0 hbb (by simp [hA1, Function.update_apply, hPT])
    (by simp [hA1, Function.update_apply, hb]) (by simp [hA1])
    (by simp [hA1, Function.update_apply, hy]) (by simp [hA1, Function.update_apply, hv])
    (by simp [hA1, Function.update_apply, hU]) (by simp [hA1, Function.update_apply, hlc])
    (by simp [hA1, Function.update_apply, htmp])
  set A2 := Function.update (Function.update A1 (rs .I0T)
    (ent ((piN π)^[E0] bb) ++ A1 (rs .I0T))) (rg .e0) [] with hA2
  have o1 := runs_offProg true A2 i n hn (by simp [hA2, hA1, Function.update_apply, hidx])
    (by simp [hA2, hA1, Function.update_apply, hlen]) (by simp [hA2])
    (by simp [hA2, hA1, Function.update_apply, hq1])
    (by simp [hA2, hA1, Function.update_apply, hq2])
    (by simp [hA2, hA1, Function.update_apply, hq3])
    (by simp [hA2, hA1, Function.update_apply, hq4])
    (by simp [hA2, hA1, Function.update_apply, hf])
    (by simp [hA2, hA1, Function.update_apply, h1])
    (by simp [hA2, hA1, Function.update_apply, h2])
    (by simp [hA2, hA1, Function.update_apply, h3])
    (by simp [hA2, hA1, Function.update_apply, htmp])
  rw [Bool.toNat_true] at o1
  set E1 := (n + 1 - i) % n with hE1
  set A3 := Function.update A2 (rg .e0) (una E1) with hA3
  have p1 := runs_pushPiProg π .I1T A3 bb E1 hbb
    (by simp [hA3, hA2, hA1, hPT])
    (by simp [hA3, hA2, hA1, hb]) (by simp [hA3])
    (by simp [hA3, hA2, hA1, hy])
    (by simp [hA3, hA2, hA1, hv])
    (by simp [hA3, hA2, hA1, hU])
    (by simp [hA3, hA2, hA1, hlc])
    (by simp [hA3, hA2, hA1, htmp])
  refine runs_seq' o0 (runs_seq' p0 (runs_seq' o1 (runs_weak p1 ?_ le_rfl) le_rfl) le_rfl) ?_
  · clear o0 p0 o1 p1
    funext k
    simp only [hA3, hA2, hA1, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · have hE0n : E0 < n := Nat.mod_lt _ (by omega)
    have hE1n : E1 < n := Nat.mod_lt _ (by omega)
    have hM : 1 ≤ m + 1 := by omega
    have p24 : (m + 1) ^ 2 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_right hM (by norm_num)
    have p14 : m + 1 ≤ (m + 1) ^ 4 := by
      have := Nat.pow_le_pow_right hM (show 1 ≤ 4 by norm_num)
      simpa using this
    have hoff : (n + i + 2) ^ 2 ≤ 4 * (m + 1) ^ 2 := by
      have hle : n + i + 2 ≤ 2 * (m + 1) := by omega
      calc (n + i + 2) ^ 2 ≤ (2 * (m + 1)) ^ 2 := Nat.pow_le_pow_left hle 2
        _ = 4 * (m + 1) ^ 2 := by ring
    have hp0 : E0 * (40 * (m + 1) ^ 3 + 3) ≤ (m + 1) * (40 * (m + 1) ^ 3 + 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have hp1 : E1 * (40 * (m + 1) ^ 3 + 3) ≤ (m + 1) * (40 * (m + 1) ^ 3 + 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have e5 : (m + 1) * (40 * (m + 1) ^ 3 + 3) = 40 * (m + 1) ^ 4 + 3 * (m + 1) := by ring
    omega

end SubNLogN.Machine.Walsh.PosPermSchedAux.CycB

namespace SubNLogN.Machine.Walsh.PosPermSchedAux

/-- **[PROVED] Work package (c) of the cycle phase** (`CycPushStmt`, `PosPermSchedDefs.lean`):
the closed program `CycB.cycPushProg` pushes the two involution values of the current point, at
cost `3400 (m + 1)^4`. -/
theorem cycPush_holds : CycPushStmt :=
  ⟨CycB.cycPushProg, CycB.closed_cycPushProg, 3400, 4,
    fun _ π bb i n S hbb hn hnm him hPT _ hb hidx hlen hcl =>
      CycB.runs_cycPushProg π bb i n S hbb hn hnm him hPT hb hidx hlen hcl⟩

end SubNLogN.Machine.Walsh.PosPermSchedAux
