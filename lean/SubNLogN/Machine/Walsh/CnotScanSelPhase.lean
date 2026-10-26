/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanSelPhaseK
import SubNLogN.Machine.Walsh.CnotScanCz

/-!
# `SubNLogN.Machine.Walsh.CnotScanSelPhase`: the scan `S_U` (mode `selPhase`)

Paper: Section 5.1 eq. (`eq:walsh-SU`) (the diagonal `S_U`: the record at `x` is
multiplied by `i^{∑_{j ∈ U} x_j}`), Lemma 5.1 (`lem:walsh-select`: `U = Sel ∖ T`, applied in one scan as a
fourth-root phase), and Lemma 5.3 (`lem:walsh-lift`: `P_* = P + 8d`, `w_* = w + 8d`). Engine: K3-LIFT's
`recLoopS`; the `U`-vector: K3-LIFT's `uvBuild` (`Walsh/CnotScanUV.lean`).

## Plan
`scanSP`: the field template (`tplSetup`); the `U`-vector `uv` (`uvBuild`); `k := 0`,
`μ := false`; the index `x := idxSyms m 0` (`xInit`); the record loop with the unit routine
`kRsp` (`k = #{p ∈ U : x_p = 1} mod 4`) and the increment `incX`; the output drained back onto
the array; templates, index and `U`-vector cleared. Every coefficient of record `i` is
multiplied by `i^k` (`sPhase_eq`), exactly as `W`-bit two's-complement words.

**Scope (honest summary).** `scanSP_runs` and the public
`cnotScanSelPhase_holds : CnotScanStmt .selPhase` (`J = 1`), no `sorry` in these files. Helpers
live in `SubNLogN.Machine.WalshScanSP`.
-/

namespace SubNLogN.Machine.WalshScanSP

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine WalshLift
  SubNLogN.Machine.WalshScanAux SubNLogN.Machine.WalshScanX SubNLogN.Machine.WalshScanCz
open SubNLogN.Math.Walsh SubNLogN.Math.Common
open WP.W9comp (runs_seq runs_mono runs_congr)

/-! ## Value level -/

theorem spCount_map {α : Type} (f g : α → Bool) : ∀ l : List α,
    spCount (l.map f) (l.map g) = l.countP (fun p => f p && g p)
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.map_cons, spCount, spCount_map f g l, List.countP_cons, Nat.add_comm]

theorem bitsLE_eq_cube (m i : ℕ) :
    bitsLE m i = (List.finRange m).reverse.map (cubeOfNat m i) := by
  apply List.ext_getElem
  · simp [K1.length_bitsLE]
  · intro j h1 h2
    simp only [K1.length_bitsLE] at h1
    simp only [bitsLE, List.getElem_map, List.getElem_range, List.getElem_reverse,
      List.getElem_finRange, cubeOfNat, List.length_finRange]
    congr 1
    simp
    omega

theorem countP_finRange_eq_card {m : ℕ} (q : Fin m → Bool) :
    (List.finRange m).countP q = (Finset.univ.filter (fun p => q p = true)).card := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _), List.toFinset_filter,
    List.toFinset_finRange]

theorem spKfun_eq (m : ℕ) (U : Finset (Fin m)) (i : ℕ) :
    spKfun m U i = fin4 (U.filter (fun j => cubeOfNat m i j = true)).card := by
  have hc : spCount (bitsLE m i) (uvBits m U) =
      (U.filter (fun j => cubeOfNat m i j = true)).card := by
    rw [bitsLE_eq_cube, uvBits, spCount_map, List.countP_reverse, countP_finRange_eq_card]
    congr 1
    ext p
    simp [and_comm]
  rw [spKfun, hc]

theorem toC_unitZ (k : Fin 4) : toC (unitZ k) = Complex.I ^ k.val := by
  fin_cases k <;> apply Complex.ext <;> simp [unitZ, toC, pow_succ]

theorem toC_unitZ_fin4 (c : ℕ) : toC (unitZ (fin4 c)) = Complex.I ^ c := by
  rw [toC_unitZ, val_fin4]
  conv_rhs => rw [← Nat.div_add_mod c 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

/-- **The value of the scan `S_U`**: record `i` is multiplied by `i^{spKfun i}`. -/
theorem sPhase_eq (m : ℕ) (U : Finset (Fin m)) (i : ℕ) :
    sPhase U (cubeOfNat m i) = toC (cZ 0 false (spKfun m U i)) := by
  rw [cZ_zero_false, spKfun_eq, toC_unitZ_fin4]
  rfl

theorem runsR_of_runsE {P : EProg SK} {S S' : SK → List Sym} {T : ℕ}
    (h : Runs P S S' (fun _ => True) T) : RunsR P S S' (fun _ => True) (fun _ => True) T := by
  intro r _
  obtain ⟨s', t, e, ⟨hs, -⟩, ht⟩ := h ⟨r, S⟩ rfl
  obtain ⟨var', stk'⟩ := s'
  change stk' = S' at hs
  subst hs
  exact ⟨var', t, e, trivial, ht⟩

/-! ## The program -/

/-- The scan `S_U`, `U = Sel ∖ T`. -/
def scanSP : EProg SK :=
  .seq (tplSetup.liftRegs lT)
  (.seq uvBuild
  (.seq (.load fun r => { r with k := 0, mu := false })
  (.seq xInit
  (.seq (recLoopS kRsp incX)
  (.seq ((drain (.inr .o) (.inl 0)).liftRegs lT)
  (.seq ((clear (.inr .tcc)).liftRegs lT)
  (.seq ((clear (.inr .x)).liftRegs lT)
    ((clear (.inr .uv)).liftRegs lT))))))))

theorem closed_scanSP : scanSP.Closed := by
  unfold scanSP
  exact WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT closed_tplSetup)
    (WP.W9comp.closed_seq closed_uvBuild
    (WP.W9comp.closed_seq (by simp [Prog.Closed, Prog.FreeBelow])
    (WP.W9comp.closed_seq closed_xInit
    (WP.W9comp.closed_seq (closed_recLoopS closed_kRsp closed_incX)
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_drain _ _))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_clear _))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_clear _))
      (WP.W9comp.closed_liftRegs lT (closed_clear _)))))))))

/-- The cost bound of `scanSP` (`hl` the header length). -/
def spCost (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m)) (hl : ℕ) : ℕ :=
  tplCost P d r w + uvCost P d r w K m j₀ D nS ρ pairs + 1 + (6 * hl + 23 * m + 12) +
    (2 ^ m * ((12 * m + 7) + r * (coefCost (w + 8 * d) 0 + 2) + (7 * m + 5) + 7) + 2) +
    (3 * cvolCube m r (w + 8 * d) + 2) + (2 * (w + 8 * d) + 2) + (2 * m + 2) + (2 * m + 2)

theorem length_uvSyms (m : ℕ) (U : Finset (Fin m)) : (uvSyms m U).length = m := by
  simp [uvSyms]

theorem scanSP_runs (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m))
    (y : RArr (Cube m) r) (rest hrest prest : List Sym) (S : SK → List Sym)
    (hcl : ∀ e : SS, S (.inr e) = []) (hm : j₀ + D * K + nS = m) (hρ : ρ < K) (hw : P + 2 ≤ w)
    (hy : ArrOnGrid (P + 8 * d) y) (hrest' : BlkTerm rest)
    (hA : S (.inl 0) = carrSyms (w + 8 * d) (encCube (P + 8 * d) y) ++ rest)
    (hH : S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest)
    (hQ : S (.inl 2) = pairsSyms pairs ++ prest) :
    Runs scanSP S
      (Function.update S (.inl 0)
        (carrSyms (w + 8 * d) (encCube (P + 8 * d)
          (sDiag (slicePos m K j₀ D ρ \ targets pairs) y)) ++ rest))
      (fun _ => True)
      (spCost P d r w K m j₀ D nS ρ pairs (sliceHdr P d r w K m j₀ D nS ρ).length) := by
  have hA2 : S (.inl 0) = arrSyms ((recsOf (w + 8 * d) (encCube (P + 8 * d) y)).map
      fun cs => cs.flatMap fun c => c.1 ++ c.2) ++ rest := by
    rw [hA, carrSyms_recsOf]
  have hrecs : ∀ cs ∈ recsOf (w + 8 * d) (encCube (P + 8 * d) y), ∀ c ∈ cs,
      c.1.length = (w + 8 * d) + 0 ∧ c.2.length = (w + 8 * d) + 0 := by
    intro cs hcs c hc
    simp only [recsOf, List.mem_map] at hcs
    obtain ⟨cs0, -, rfl⟩ := hcs
    obtain ⟨c0, -, rfl⟩ := List.mem_map.1 hc
    simp only [K1.length_twosBits]
    constructor <;> omega
  have hval : arrSyms (outRecs false (spKfun m (slicePos m K j₀ D ρ \ targets pairs)) (w + 8 * d)
      0 0 (recsOf (w + 8 * d) (encCube (P + 8 * d) y))) =
      carrSyms (w + 8 * d) (encCube (P + 8 * d)
        (sDiag (slicePos m K j₀ D ρ \ targets pairs) y)) := by
    have h := arrSyms_outRecs false (spKfun m (slicePos m K j₀ D ρ \ targets pairs)) (w + 8 * d)
      0 0 (encCube (P + 8 * d) y)
    simp only [Nat.zero_min, Nat.sub_zero] at h
    rw [h, show sDiag (slicePos m K j₀ D ρ \ targets pairs) y =
      diagArr (sPhase (slicePos m K j₀ D ρ \ targets pairs)) y from rfl,
      encCube_scale (P + 8 * d) (sPhase (slicePos m K j₀ D ρ \ targets pairs)) y hy
        (fun i => cZ 0 false (spKfun m (slicePos m K j₀ D ρ \ targets pairs) i))
        (sPhase_eq m (slicePos m K j₀ D ρ \ targets pairs))]
  have R := RunsR.seq (runsR_of_runs (runs_tplSetup P d r w K m j₀ D nS ρ hrest S hcl hH)
      (fun _ => True) (fun _ _ _ => trivial))
    (RunsR.seq (runsR_of_runsE (runs_uvBuild P d r w K m j₀ D nS ρ pairs hrest prest _ hm hρ
      (by simp [hH]) (by simp [hQ]) (by simp [hcl]) (by simp [hcl]) (by simp [hcl])
      (by simp [hcl]) (by simp [hcl]) (by simp [hcl]) (by simp [hcl]) (by simp [hcl])
      (by simp [hcl]) (by simp [hcl])))
    (RunsR.seq (runsR_load (fun r => { r with k := 0, mu := false }) _ (fun _ => True)
      (fun r => r.mu = false) (fun _ _ => rfl))
    (RunsR.seq (runsR_xInit P d r w K m j₀ D nS ρ hrest _ (by simp [hH]) (by simp [hcl])
      (by simp [hcl]) (by simp [hcl]) (by simp [hcl]) (by simp [hcl]) (fun r => r.mu = false)
      (fun _ _ h => h))
    (RunsR.seq (recLoopS_runs kRsp incX (spKfun m (slicePos m K j₀ D ρ \ targets pairs))
      (idxSyms m) (spStat m (slicePos m K j₀ D ρ \ targets pairs)) (12 * m + 7) (7 * m + 5)
      (kRSpec_kRsp m _) (incSpec_incX m _ (fun _ h => h.2.1)) (statFrame_spStat m _)
      (w + 8 * d) 0 (by omega) false rest hrest'
      (recsOf (w + 8 * d) (encCube (P + 8 * d) y)) 0 _ hrecs
      ⟨by simp [hcl], by simp, by simp [hcl], by simp [hcl], by simp [hcl], by simp [hcl],
        by simp [hcl], by simp [hcl]⟩
      ⟨by simp, by simp [hcl], by simp [hcl]⟩ (by simp) (by simp [hA2]))
    (RunsR.seq (runsR_drainE (src := (.inr .o : SK)) (dst := .inl 0) (by simp)
      (arrSyms (outRecs false (spKfun m (slicePos m K j₀ D ρ \ targets pairs)) (w + 8 * d) 0 0
        (recsOf (w + 8 * d) (encCube (P + 8 * d) y)))).reverse _ (by simp [hcl])
      (fun r : ER => r.mu = false) (fun _ h => h))
    (RunsR.seq (runsR_clearE (.inr .tcc : SK) (List.replicate (w + 8 * d) uSym) _ (by simp)
      (fun r : ER => r.mu = false) (fun _ h => h))
    (RunsR.seq (runsR_clearE (.inr .x : SK)
      (idxSyms m (0 + (recsOf (w + 8 * d) (encCube (P + 8 * d) y)).length)) _ (by simp)
      (fun r : ER => r.mu = false) (fun _ h => h))
      (runsR_clearE (.inr .uv : SK) (uvSyms m (slicePos m K j₀ D ρ \ targets pairs)) _
        (by simp) (fun r : ER => r.mu = false) (fun _ h => h)))))))))
  rw [← hval]
  refine runs_mono (runs_congr (runs_of_runsR R) ?_) (fun _ _ => trivial) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp
    · cases e <;> simp [hcl]
  · simp only [spCost, sum_recsOf_encCube', List.length_reverse, hval,
      WalshCnot1.length_carrSyms_encCube, List.length_replicate, length_idxSyms, length_uvSyms]
    omega

theorem spCost_le (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m))
    (hm : j₀ + D * K + nS = m) (hρ : ρ < K) (hw : P + 2 ≤ w) (hd : d ≤ w + m) (hK : K ≤ w + m) :
    spCost P d r w K m j₀ D nS ρ pairs (sliceHdr P d r w K m j₀ D nS ρ).length ≤
      1000 * (cvolCube m r (w + 8 * d) + 2 ^ m * ((w + m + 1) ^ 1 + (pairsSyms pairs).length) +
        (sliceHdr P d r w K m j₀ D nS ρ).length) := by
  have hu := uvCost_le P d r w K m j₀ D nS ρ pairs hm hρ
  have hH' := length_sliceHdr P d r w K m j₀ D nS ρ
  have hM : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hmM : m < 2 ^ m := Nat.lt_two_pow_self
  have hnQ := length_le_pairsSyms pairs
  have hmn : m * pairs.length ≤ 2 ^ m * (pairsSyms pairs).length := Nat.mul_le_mul hmM.le hnQ
  have h1 : r * (coefCost (w + 8 * d) 0 + 2) ≤ 42 * (2 * r * (w + 8 * d)) := by
    have hc : coefCost (w + 8 * d) 0 + 2 ≤ 84 * (w + 8 * d) := by
      simp only [coefCost]
      omega
    calc r * (coefCost (w + 8 * d) 0 + 2) ≤ r * (84 * (w + 8 * d)) := Nat.mul_le_mul_left _ hc
      _ = 42 * (2 * r * (w + 8 * d)) := by ring
  have h3 : 2 ^ m * (42 * (2 * r * (w + 8 * d))) ≤ 42 * cvolCube m r (w + 8 * d) := by
    have e : 2 ^ m * (42 * (2 * r * (w + 8 * d))) = 42 * (2 ^ m * (2 * r * (w + 8 * d))) := by
      ring
    rw [e, cvolCube]
    exact Nat.mul_le_mul_left 42 (Nat.mul_le_mul_left _ (by omega))
  have hrec : 2 ^ m * ((12 * m + 7) + r * (coefCost (w + 8 * d) 0 + 2) + (7 * m + 5) + 7) ≤
      42 * cvolCube m r (w + 8 * d) + 19 * (2 ^ m * (w + m + 1)) := by
    have e : 2 ^ m * ((12 * m + 7) + r * (coefCost (w + 8 * d) 0 + 2) + (7 * m + 5) + 7) =
        2 ^ m * (r * (coefCost (w + 8 * d) 0 + 2)) + 2 ^ m * (19 * m + 19) := by
      ring
    have f1 : 2 ^ m * (r * (coefCost (w + 8 * d) 0 + 2)) ≤
        2 ^ m * (42 * (2 * r * (w + 8 * d))) := Nat.mul_le_mul_left _ h1
    have f2 : 2 ^ m * (19 * m + 19) ≤ 2 ^ m * (19 * (w + m + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    have f3 : 2 ^ m * (19 * (w + m + 1)) = 19 * (2 ^ m * (w + m + 1)) := by ring
    omega
  have hXM : w + m + 1 ≤ 2 ^ m * (w + m + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hQM : (pairsSyms pairs).length ≤ 2 ^ m * (pairsSyms pairs).length :=
    Nat.le_mul_of_pos_left _ (by omega)
  simp only [spCost, tplCost]
  rw [pow_one, mul_add (2 ^ m) (w + m + 1) (pairsSyms pairs).length]
  omega

end SubNLogN.Machine.WalshScanSP

namespace SubNLogN.Machine

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WalshLift SubNLogN.Machine.WalshScanAux
  SubNLogN.Machine.WalshScanX SubNLogN.Machine.WalshScanSP SubNLogN.Math.Walsh SubNLogN.Math.Common

/-- **K3.4b, mode `selPhase`, proved** (`CnotScanStmt .selPhase`, `Walsh/CnotLeaf.lean:83`;
Section 5.1 eq. (`eq:walsh-SU`) and Lemma 5.1 (`lem:walsh-select`), the diagonal `S_U`, `U = Sel ∖ T`, applied in one scan as a
fourth-root phase), with `J = 1` and `C = 1000`: the program `WalshScanSP.scanSP`
(`scanSP_runs`), scratch `SS` (clean on entry, restored), registers `ER`. The output fields are
the exact `W`-bit two's-complement words of `i^k (a, b)` (`W = w + 8d`). Of the hypotheses,
`CnotPairsValid pairs` and the output disk-grid hypothesis are not needed for this mode;
`j₀ + DK + nS = m` and `ρ < K` enter the `U`-vector builder (`runs_uvBuild`), `P + 2 ≤ w`,
`d ≤ w + m`, `K ≤ w + m` the cost bound, the input grid hypothesis the exact value. -/
theorem cnotScanSelPhase_holds : CnotScanStmt .selPhase := by
  refine ⟨1, 1000, fun _ => ⟨SS, inferInstance, inferInstance, ER, scanSP, inferInstance,
    inferInstance, closed_scanSP, ?_⟩⟩
  intro P d r w K m j₀ D nS ρ pairs y rest hrest prest S hcl hm hρ hw hd hK _ hy _ hrest' hA hH hQ
  have hgrid : ArrOnGrid (P + 8 * d) y := fun x k => (hy x k).1
  exact _root_.WP.W9comp.runs_mono (scanSP_runs P d r w K m j₀ D nS ρ pairs y rest hrest prest S
    hcl hm hρ hw hgrid hrest' hA hH hQ) (fun _ _ => trivial)
    (spCost_le P d r w K m j₀ D nS ρ pairs hm hρ hw hd hK)

end SubNLogN.Machine
