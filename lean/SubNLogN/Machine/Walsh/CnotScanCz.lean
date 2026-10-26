/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanCzK
import SubNLogN.Machine.Walsh.CnotScanModeShift

/-!
# `SubNLogN.Machine.Walsh.CnotScanCz`: the scan `CZ` (mode `cz`)

Paper: Section 5.2, eq. (`eq:walsh-CZ`), and Proposition 5.5 (`prop:cnot-batch`) (the sign diagonal `CZ` of the pairs:
the record at `x` is multiplied by `(-1)^{∑_j x_{c_j} x_{t_j}}`, computed once per record from
its address and the pair list), Lemma 5.3 (`lem:walsh-lift`: `P_* = P + 8d`, `w_* = w + 8d`). Engine:
K3-LIFT's `recLoopS` (`Walsh/CnotScanRec.lean`); template `scanShift`
(`Walsh/CnotScanModeShift.lean`).

## Plan
`scanCz`: the field template `tcc = uSym^{w+8d}` (`tplSetup`); `k := 0`, `μ := false`; the index
`x := idxSyms m 0` (`xInit`); the unary pair list `pl` (`plBuild`); the record loop with the unit
routine `kRcz` (`k = 2·#{j : x_{c_j} = x_{t_j} = 1} mod 4`) and the increment `incX`; the output
drained back onto the array; templates, index and pair list cleared. Every coefficient of record
`i` is multiplied by `i^k = (-1)^{#…}` (`czSign_eq`), exactly as `W`-bit two's-complement words.

**Scope (honest summary).** `scanCz_runs` and the public `cnotScanCz_holds : CnotScanStmt .cz`
(`J = 2`), no `sorry`. Helpers live in `SubNLogN.Machine.WalshScanCz`.
-/

namespace SubNLogN.Machine.WalshScanCz

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine WalshLift
  SubNLogN.Machine.WalshScanAux SubNLogN.Machine.WalshScanX
open SubNLogN.Math.Walsh SubNLogN.Math.Common
open WP.W9comp (runs_seq runs_mono runs_congr)

/-! ## Value level -/

theorem czK_eq (L : List Bool) {m : ℕ} :
    ∀ (qs : List (Fin m × Fin m)) (k0 : Fin 4),
      czK L qs k0 = k0 + fin4 (2 * qs.countP (fun q => L.getD q.2 false && L.getD q.1 false))
  | [], k0 => by simp [czK, add_fin4_zero]
  | q :: qs, k0 => by
    rw [czK, czK_eq L qs, List.countP_cons]
    have h2 : (2 : Fin 4).val = 2 := rfl
    apply Fin.ext
    by_cases h : (L.getD q.2 false && L.getD q.1 false) = true
    · rw [if_pos h, if_pos h]
      simp only [Fin.val_add, val_fin4, h2]
      omega
    · rw [if_neg h, if_neg h]
      simp only [Fin.val_add, val_fin4]
      omega

theorem getD_rev_bitsLE (m i p : ℕ) (hp : p < m) :
    (bitsLE m i).reverse.getD p false = i.testBit (m - 1 - p) := by
  have hl : (bitsLE m i).length = m := K1.length_bitsLE m i
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega), hl]
  simp [bitsLE, List.getElem?_range (show m - 1 - p < m by omega)]

theorem czKfun_eq (m : ℕ) (pairs : List (Fin m × Fin m)) (i : ℕ) :
    czKfun m pairs i =
      fin4 (2 * pairs.countP (fun q => cubeOfNat m i q.1 && cubeOfNat m i q.2)) := by
  have hc : pairs.countP (fun q => (bitsLE m i).reverse.getD q.2 false &&
      (bitsLE m i).reverse.getD q.1 false) =
      pairs.countP (fun q => cubeOfNat m i q.1 && cubeOfNat m i q.2) := by
    apply List.countP_congr
    intro q _
    rw [getD_rev_bitsLE m i q.2 q.2.isLt, getD_rev_bitsLE m i q.1 q.1.isLt, Bool.and_comm]
    rfl
  rw [czKfun, czK_eq, List.countP_reverse, hc]
  apply Fin.ext
  simp only [Fin.val_add, val_fin4, Fin.val_zero]
  omega

theorem cZ_zero_false (k : Fin 4) : cZ 0 false k = unitZ k := by
  simp [cZ, gfacZ, cmulC]

theorem two_mul_cast_fin4 (c : ℕ) : fin4 (2 * c) = if c % 2 = 0 then 0 else 2 := by
  apply Fin.ext
  rw [val_fin4]
  split_ifs with h
  · show 2 * c % 4 = 0
    omega
  · show 2 * c % 4 = 2
    omega

theorem toC_unitZ_two_mul (c : ℕ) : toC (unitZ (fin4 (2 * c))) = (-1 : ℂ) ^ c := by
  rw [two_mul_cast_fin4]
  split_ifs with h
  · rw [Even.neg_one_pow (Nat.even_iff.mpr h)]
    have h0 : unitZ 0 = (1, 0) := rfl
    rw [h0]
    apply Complex.ext <;> simp [toC]
  · rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))]
    have h2 : unitZ 2 = (-1, 0) := rfl
    rw [h2]
    apply Complex.ext <;> simp [toC]

/-- **The value of the scan `CZ`**: record `i` is multiplied by `i^{czKfun i}`. -/
theorem czSign_eq (m : ℕ) (pairs : List (Fin m × Fin m)) (i : ℕ) :
    czSign pairs (cubeOfNat m i) = toC (cZ 0 false (czKfun m pairs i)) := by
  rw [cZ_zero_false, czKfun_eq, toC_unitZ_two_mul]
  rfl

/-! ## The program -/

/-- The scan `CZ`. -/
def scanCz : EProg SK :=
  .seq (tplSetup.liftRegs lT)
  (.seq (.load fun r => { r with k := 0, mu := false })
  (.seq xInit
  (.seq (plBuild.liftRegs lT)
  (.seq (recLoopS kRcz incX)
  (.seq ((drain (.inr .o) (.inl 0)).liftRegs lT)
  (.seq ((clear (.inr .tcc)).liftRegs lT)
  (.seq ((clear (.inr .x)).liftRegs lT)
    ((clear (.inr .pl)).liftRegs lT))))))))

theorem closed_scanCz : scanCz.Closed := by
  unfold scanCz
  exact WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT closed_tplSetup)
    (WP.W9comp.closed_seq (by simp [Prog.Closed, Prog.FreeBelow])
    (WP.W9comp.closed_seq closed_xInit
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT closed_plBuild)
    (WP.W9comp.closed_seq (closed_recLoopS closed_kRcz closed_incX)
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_drain _ _))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_clear _))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_clear _))
      (WP.W9comp.closed_liftRegs lT (closed_clear _)))))))))

theorem sum_recsOf_encCube' (W F A B C : ℕ) {m r : ℕ} (y : RArr (Cube m) r) :
    ((recsOf W (encCube F y)).map fun cs => A + cs.length * B + C + 7).sum =
      2 ^ m * (A + r * B + C + 7) := by
  simp only [recsOf, encCube, encArr, cubeAddrs, List.map_map, Function.comp_def, List.length_map,
    List.length_finRange]
  rw [WalshCnot1.sum_range_const]

/-- The cost bound of `scanCz` (`W = w + 8d`, `hl` the header length). -/
def czCost (P d r w m : ℕ) (pairs : List (Fin m × Fin m)) (hl : ℕ) : ℕ :=
  tplCost P d r w + 1 + (6 * hl + 23 * m + 12) + plCost pairs +
    (2 ^ m * (czCk pairs + r * (coefCost (w + 8 * d) 0 + 2) + (7 * m + 5) + 7) + 2) +
    (3 * cvolCube m r (w + 8 * d) + 2) + (2 * (w + 8 * d) + 2) + (2 * m + 2) +
    (2 * (plSyms pairs).length + 2)

theorem scanCz_runs (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m))
    (y : RArr (Cube m) r) (rest hrest prest : List Sym) (S : SK → List Sym)
    (hcl : ∀ e : SS, S (.inr e) = []) (hw : P + 2 ≤ w) (hy : ArrOnGrid (P + 8 * d) y)
    (hrest' : BlkTerm rest)
    (hA : S (.inl 0) = carrSyms (w + 8 * d) (encCube (P + 8 * d) y) ++ rest)
    (hH : S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest)
    (hQ : S (.inl 2) = pairsSyms pairs ++ prest) :
    Runs scanCz S
      (Function.update S (.inl 0)
        (carrSyms (w + 8 * d) (encCube (P + 8 * d) (diagArr (czSign pairs) y)) ++ rest))
      (fun _ => True) (czCost P d r w m pairs (sliceHdr P d r w K m j₀ D nS ρ).length) := by
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
  have hval : arrSyms (outRecs false (czKfun m pairs) (w + 8 * d) 0 0
      (recsOf (w + 8 * d) (encCube (P + 8 * d) y))) =
      carrSyms (w + 8 * d) (encCube (P + 8 * d) (diagArr (czSign pairs) y)) := by
    have h := arrSyms_outRecs false (czKfun m pairs) (w + 8 * d) 0 0 (encCube (P + 8 * d) y)
    simp only [Nat.zero_min, Nat.sub_zero] at h
    rw [h, encCube_scale (P + 8 * d) (czSign pairs) y hy
      (fun i => cZ 0 false (czKfun m pairs i)) (czSign_eq m pairs)]
  have R := RunsR.seq (runsR_of_runs (runs_tplSetup P d r w K m j₀ D nS ρ hrest S hcl hH)
      (fun _ => True) (fun _ _ _ => trivial))
    (RunsR.seq (runsR_load (fun r => { r with k := 0, mu := false }) _ (fun _ => True)
      (fun r => r.mu = false) (fun _ _ => rfl))
    (RunsR.seq (runsR_xInit P d r w K m j₀ D nS ρ hrest _ (by simp [hH]) (by simp [hcl])
      (by simp [hcl]) (by simp [hcl]) (by simp [hcl]) (by simp [hcl]) (fun r => r.mu = false)
      (fun _ _ h => h))
    (RunsR.seq (runsR_of_runs (runs_plBuild pairs prest _ (by simp [hQ]) (by simp [hcl])
      (by simp [hcl]) (by simp [hcl]) (by simp [hcl]) (by simp [hcl]) (by simp [hcl]))
      (fun r => r.mu = false) (fun _ _ h => h))
    (RunsR.seq (recLoopS_runs kRcz incX (czKfun m pairs) (idxSyms m) (czStat pairs) (czCk pairs)
      (7 * m + 5) (kRSpec_kRcz pairs) (incSpec_incX m (czStat pairs) (fun _ h => h.2.1))
      (statFrame_czStat pairs) (w + 8 * d) 0 (by omega) false rest hrest'
      (recsOf (w + 8 * d) (encCube (P + 8 * d) y)) 0 _ hrecs
      ⟨by simp [hcl], by simp, by simp [hcl], by simp [hcl], by simp [hcl], by simp [hcl],
        by simp [hcl], by simp [hcl]⟩
      ⟨by simp, by simp [hcl], by simp [hcl], by simp [hcl]⟩ (by simp) (by simp [hA2]))
    (RunsR.seq (runsR_drainE (src := (.inr .o : SK)) (dst := .inl 0) (by simp)
      (arrSyms (outRecs false (czKfun m pairs) (w + 8 * d) 0 0
        (recsOf (w + 8 * d) (encCube (P + 8 * d) y)))).reverse _ (by simp [hcl])
      (fun r : ER => r.mu = false) (fun _ h => h))
    (RunsR.seq (runsR_clearE (.inr .tcc : SK) (List.replicate (w + 8 * d) uSym) _ (by simp)
      (fun r : ER => r.mu = false) (fun _ h => h))
    (RunsR.seq (runsR_clearE (.inr .x : SK)
      (idxSyms m (0 + (recsOf (w + 8 * d) (encCube (P + 8 * d) y)).length)) _ (by simp)
      (fun r : ER => r.mu = false) (fun _ h => h))
      (runsR_clearE (.inr .pl : SK) (plSyms pairs) _ (by simp)
        (fun r : ER => r.mu = false) (fun _ h => h)))))))))
  rw [← hval]
  refine runs_mono (runs_congr (runs_of_runsR R) ?_) (fun _ _ => trivial) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp
    · cases e <;> simp [hcl]
  · simp only [czCost, sum_recsOf_encCube', List.length_reverse, hval,
      WalshCnot1.length_carrSyms_encCube, List.length_replicate, length_idxSyms]
    omega

/-! ## Cost estimates -/

theorem pairs_length_le {m : ℕ} {pairs : List (Fin m × Fin m)} (h : CnotPairsValid pairs) :
    2 * pairs.length ≤ m := by
  have h1 := h.length_le_card
  simp only [List.length_append, List.length_map, Fintype.card_fin] at h1
  omega

theorem pairsCost_le {m : ℕ} : ∀ (ps : List (Fin m × Fin m)),
    pairsCost ps ≤ ps.length * (46 * m + 20) + 3 * (hdrSyms (pairFields ps)).length
  | [] => by simp [pairsCost]
  | p :: ps => by
    have ih := pairsCost_le ps
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    have hf : (hdrSyms (pairFields (p :: ps))).length = (hdrSyms [(p.1 : ℕ)]).length +
        (hdrSyms [(p.2 : ℕ)]).length + (hdrSyms (pairFields ps)).length := by
      simp [pairFields, hdrSyms]
      omega
    simp only [pairsCost, List.map_cons, List.sum_cons, fieldCost, List.length_cons] at ih ⊢
    rw [hf, show (ps.length + 1) * (46 * m + 20) = ps.length * (46 * m + 20) + (46 * m + 20) by
      ring]
    generalize ps.length * (46 * m + 20) = A at *
    omega

theorem length_flatMap_plEntry_le {m : ℕ} : ∀ (qs : List (Fin m × Fin m)),
    (qs.flatMap plEntry).length ≤ qs.length * (2 * m)
  | [] => by simp
  | q :: qs => by
    have ih := length_flatMap_plEntry_le qs
    have h1 := q.1.isLt
    have h2 := q.2.isLt
    simp only [List.flatMap_cons, List.length_append, plEntry, List.length_cons,
      List.length_replicate, List.length_nil] at ih ⊢
    rw [show (qs.length + 1) * (2 * m) = qs.length * (2 * m) + 2 * m by ring]
    generalize qs.length * (2 * m) = A at *
    omega

theorem length_plSyms_le {m : ℕ} (pairs : List (Fin m × Fin m)) :
    (plSyms pairs).length ≤ pairs.length * (2 * m) := by
  have h := length_flatMap_plEntry_le pairs.reverse
  rwa [List.length_reverse] at h

theorem czCost_le (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m))
    (hw : P + 2 ≤ w) (hd : d ≤ w + m) (hpv : CnotPairsValid pairs) :
    czCost P d r w m pairs (sliceHdr P d r w K m j₀ D nS ρ).length ≤
      400 * (cvolCube m r (w + 8 * d) + 2 ^ m * ((w + m + 1) ^ 2 + (pairsSyms pairs).length) +
        (sliceHdr P d r w K m j₀ D nS ρ).length) := by
  have hn := pairs_length_le hpv
  have hPC := pairsCost_le pairs
  have hPL := length_plSyms_le pairs
  have hQl := length_pairsSyms' pairs
  have hH' := length_sliceHdr P d r w K m j₀ D nS ρ
  have hM : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have k1 : pairs.length * (46 * m + 20) ≤ 23 * (m * m) + 10 * m := by nlinarith
  have k2 : pairs.length * (16 * m + 16) ≤ 8 * (m * m) + 8 * m := by nlinarith
  have k3 : pairs.length * (2 * m) ≤ m * m := by nlinarith
  have hX : m * m + m + 1 ≤ (w + m + 1) ^ 2 := by nlinarith
  have hX1 : w + m + 1 ≤ (w + m + 1) ^ 2 := by nlinarith
  have hck0 : czCk pairs + (7 * m + 5) + 7 ≤ 11 * (m * m) + 21 * m + 21 := by
    simp only [czCk]
    omega
  have hck : czCk pairs + (7 * m + 5) + 7 ≤ 21 * (w + m + 1) ^ 2 := by nlinarith
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
  have hrec : 2 ^ m * (czCk pairs + r * (coefCost (w + 8 * d) 0 + 2) + (7 * m + 5) + 7) ≤
      42 * cvolCube m r (w + 8 * d) + 21 * (2 ^ m * (w + m + 1) ^ 2) := by
    have e : 2 ^ m * (czCk pairs + r * (coefCost (w + 8 * d) 0 + 2) + (7 * m + 5) + 7) =
        2 ^ m * (r * (coefCost (w + 8 * d) 0 + 2)) + 2 ^ m * (czCk pairs + (7 * m + 5) + 7) := by
      ring
    have f1 : 2 ^ m * (r * (coefCost (w + 8 * d) 0 + 2)) ≤
        2 ^ m * (42 * (2 * r * (w + 8 * d))) := Nat.mul_le_mul_left _ h1
    have f2 : 2 ^ m * (czCk pairs + (7 * m + 5) + 7) ≤ 2 ^ m * (21 * (w + m + 1) ^ 2) :=
      Nat.mul_le_mul_left _ hck
    have f3 : 2 ^ m * (21 * (w + m + 1) ^ 2) = 21 * (2 ^ m * (w + m + 1) ^ 2) := by ring
    omega
  have hXM : (w + m + 1) ^ 2 ≤ 2 ^ m * (w + m + 1) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  have hQM : (pairsSyms pairs).length ≤ 2 ^ m * (pairsSyms pairs).length :=
    Nat.le_mul_of_pos_left _ (by omega)
  simp only [czCost, tplCost, plCost]
  rw [mul_add (2 ^ m) ((w + m + 1) ^ 2) (pairsSyms pairs).length]
  omega

end SubNLogN.Machine.WalshScanCz

namespace SubNLogN.Machine

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WalshLift SubNLogN.Machine.WalshScanAux
  SubNLogN.Machine.WalshScanX SubNLogN.Machine.WalshScanCz SubNLogN.Math.Walsh SubNLogN.Math.Common

/-- **K3.4b, mode `cz`, proved** (`CnotScanStmt .cz`, `Walsh/CnotLeaf.lean:83`; Section 5.2 eq. (`eq:walsh-CZ`),
the sign diagonal `CZ` of the pairs, computed once per record from its address and the pair
list), with `J = 2` and `C = 400`: the program `WalshScanCz.scanCz` (`scanCz_runs`), scratch `SS`
(clean on entry, restored), registers `ER`. The output fields are the exact `W`-bit
two's-complement words of `±(a, b)` (`W = w + 8d`). Of the hypotheses, `j₀ + DK + nS = m`,
`ρ < K`, `K ≤ w + m`, `BlkTerm`-free header tails and the output disk-grid hypothesis are not
needed for this mode; `P + 2 ≤ w`, `d ≤ w + m` and `CnotPairsValid pairs` (`2|pairs| ≤ m`) enter
the cost bound, the input grid hypothesis the exact value. -/
theorem cnotScanCz_holds : CnotScanStmt .cz := by
  refine ⟨2, 400, fun _ => ⟨SS, inferInstance, inferInstance, ER, scanCz, inferInstance,
    inferInstance, closed_scanCz, ?_⟩⟩
  intro P d r w K m j₀ D nS ρ pairs y rest hrest prest S hcl _ _ hw hd _ hpv hy _ hrest' hA hH hQ
  have hgrid : ArrOnGrid (P + 8 * d) y := fun x k => (hy x k).1
  exact _root_.WP.W9comp.runs_mono (scanCz_runs P d r w K m j₀ D nS ρ pairs y rest hrest prest S
    hcl hw hgrid hrest' hA hH hQ) (fun _ _ => trivial)
    (czCost_le P d r w K m j₀ D nS ρ pairs hw hd hpv)

end SubNLogN.Machine
