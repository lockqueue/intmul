/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanSelScalar

/-!
# `SubNLogN.Machine.Walsh.CnotScanModeSelScalar`: the selective-scalar scan (mode `selScalar`)

Paper: Lemma 5.1 (`lem:walsh-select`: the gadget's scalar
`2^s (2(1-i))^{q_sel}`, `s = |T|`, `q_sel = |Sel ∖ T|`) and Lemma 5.3 (`lem:walsh-lift`: `w_* = w + 8d`).
Plan: top of `Walsh/CnotScanEngine.lean`.

**Scope (honest summary).** `scanSelScalar_runs`: the program `scanSelScalar` maps the lifted array
to `carrSyms W (encCube F (cnotScanMap K j₀ D ρ pairs .selScalar y))` (`W = w + 8d`,
`F = P + 8d`), restoring every other stack, within `selScalarCost`; hypotheses: `y` on the
`F`-grid, valid pairs, `j₀ + DK + nS = m`, `ρ < K`, `P + 2 ≤ w`. Each coefficient is multiplied by
the Gaussian integer `2^e i^k (1-i)^μ` (`e = s + q + ⌊q/2⌋`, `k = 3⌊q/2⌋ mod 4`, `μ = [q odd]`)
as `W`-bit two's-complement words. `cnotScanSelScalar_holds : CnotScanStmt .selScalar` (`J = 1`).
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine WalshLift Computability
open SubNLogN.Math.Walsh SubNLogN.Math.Common
open WP.W9comp (runs_mono runs_congr)

theorem runsR_of_runsE {P : EProg SK} {S S' : SK → List Sym} {T : ℕ}
    (h : Runs P S S' (fun _ => True) T) : RunsR P S S' (fun _ => True) (fun _ => True) T := by
  intro r _
  obtain ⟨s', t, e, ⟨hs, -⟩, ht⟩ := h ⟨r, S⟩ rfl
  obtain ⟨var', stk'⟩ := s'
  change stk' = S' at hs
  subst hs
  exact ⟨var', t, e, trivial, ht⟩

theorem count_uvBits {m : ℕ} (U : Finset (Fin m)) :
    ((List.finRange m).reverse.map fun p => decide (p ∈ U)).count true = U.card := by
  rw [((List.reverse_perm (List.finRange m)).map _).count_eq, count_true_map_mem]

theorem sum_recsOf_encCube' (W F n1 n2 ck ci : ℕ) {m r : ℕ} (y : RArr (Cube m) r) :
    ((recsOf W (encCube F y)).map fun cs => ck + cs.length * (coefCost n1 n2 + 2) + ci + 7).sum =
      2 ^ m * (ck + r * (coefCost n1 n2 + 2) + ci + 7) := by
  simp only [recsOf, encCube, encArr, cubeAddrs, List.map_map, Function.comp_def, List.length_map,
    List.length_finRange]
  rw [WalshCnot1.sum_range_const]

/-- The selective-scalar scan. -/
def scanSelScalar : EProg SK :=
  .seq (tplSetup.liftRegs lT)
  (.seq uvBuild
  (.seq ((unaryOfTop (.inl 2) (.inr .n3) (.inr .n1) (.inr .u)).liftRegs lT)
  (.seq (.load fun r => { r with k := 0, mu := false })
  (.seq pcLoop
  (.seq ((clear (.inr .tmp)).liftRegs lT)
  (.seq writeK
  (.seq splitP
  (.seq (recLoopS kRu inc0)
  (.seq ((drain (.inr .o) (.inl 0)).liftRegs lT)
  (.seq ((clear (.inr .tz)).liftRegs lT)
  (.seq ((clear (.inr .tcc)).liftRegs lT)
  (.seq ((clear (.inr .td)).liftRegs lT)
    ((clear (.inr .pl)).liftRegs lT)))))))))))))

theorem closed_scanSelScalar : scanSelScalar.Closed := by
  have hk : kRu.Closed := by
    have h1 := WP.W9comp.closed_liftRegs lT (closed_drain (.inr .x2 : SK) (.inr .pl))
    simp only [Prog.Closed] at h1 ⊢
    simp [Prog.FreeBelow, kRu, kIncStep, popT, pushK, h1]
  have h0 : (recLoopS kRu inc0).Closed :=
    closed_recLoopS hk (by simp [Prog.Closed, Prog.FreeBelow, inc0])
  have hp : pcLoop.Closed := by
    simp [Prog.Closed, Prog.FreeBelow, pcLoop, pcStep, peekT, popS, pushS, pushK]
  have hw : writeK.Closed := by simp [Prog.Closed, Prog.FreeBelow, writeK, pushK]
  unfold scanSelScalar
  exact WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT closed_tplSetup)
    (WP.W9comp.closed_seq closed_uvBuild
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_unaryOfTop _ _ _ _))
    (WP.W9comp.closed_seq (by simp [Prog.Closed, Prog.FreeBelow])
    (WP.W9comp.closed_seq hp
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_clear _))
    (WP.W9comp.closed_seq hw
    (WP.W9comp.closed_seq closed_splitP
    (WP.W9comp.closed_seq h0
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_drain _ _))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_clear _))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_clear _))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_clear _))
      (WP.W9comp.closed_liftRegs lT (closed_clear _))))))))))))))

/-- The cost bound of `scanSelScalar` (`e` the shift exponent). -/
def selScalarCost (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m)) (e : ℕ) : ℕ :=
  tplCost P d r w + uvCost P d r w K m j₀ D nS ρ pairs + 20 * pairs.length + 11 * m + 6 * e +
    2 ^ m * (30 + r * (coefCost (w + 8 * d - min e (w + 8 * d)) (min e (w + 8 * d)) + 2) + 1 + 7) +
    3 * cvolCube m r (w + 8 * d) + 4 * (w + 8 * d) + 40

theorem scanSelScalar_runs (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m))
    (y : RArr (Cube m) r) (rest hrest prest : List Sym) (S : SK → List Sym)
    (hcl : ∀ e : SS, S (.inr e) = []) (hm : j₀ + D * K + nS = m) (hρ : ρ < K) (hw : P + 2 ≤ w)
    (hpv : CnotPairsValid pairs) (hy : ArrOnGrid (P + 8 * d) y) (hrest' : BlkTerm rest)
    (hA : S (.inl 0) = carrSyms (w + 8 * d) (encCube (P + 8 * d) y) ++ rest)
    (hH : S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest)
    (hQ : S (.inl 2) = pairsSyms pairs ++ prest) (bits : List Bool)
    (hbits : bits = (List.finRange m).reverse.map
      fun p => decide (p ∈ slicePos m K j₀ D ρ \ targets pairs))
    (e : ℕ) (he : e = addU bits 0 + pairs.length) :
    Runs scanSelScalar S
      (Function.update S (.inl 0) (carrSyms (w + 8 * d)
        (encCube (P + 8 * d) (cnotScanMap K j₀ D ρ pairs .selScalar y)) ++ rest))
      (fun _ => True) (selScalarCost P d r w K m j₀ D nS ρ pairs e) := by
  have huv : uvSyms m (slicePos m K j₀ D ρ \ targets pairs) = bits.map Sym.bit := by
    rw [hbits]; rfl
  have hlen : bits.length = m := by rw [hbits]; simp
  have hQ' := hQ.trans (pairsSyms_eq pairs prest)
  have hA2 : S (.inl 0) = arrSyms ((recsOf (w + 8 * d) (encCube (P + 8 * d) y)).map
      fun cs => cs.flatMap fun c => c.1 ++ c.2) ++ rest := by
    rw [hA, carrSyms_recsOf]
  have hrecs : ∀ cs ∈ recsOf (w + 8 * d) (encCube (P + 8 * d) y), ∀ c ∈ cs,
      c.1.length = (w + 8 * d - min e (w + 8 * d)) + min e (w + 8 * d) ∧
      c.2.length = (w + 8 * d - min e (w + 8 * d)) + min e (w + 8 * d) := by
    intro cs hcs c hc
    simp only [recsOf, List.mem_map] at hcs
    obtain ⟨cs0, -, rfl⟩ := hcs
    obtain ⟨c0, -, rfl⟩ := List.mem_map.1 hc
    simp only [K1.length_twosBits]
    constructor <;> omega
  have hsc : selScalar (targets pairs).card (slicePos m K j₀ D ρ \ targets pairs).card =
      toC (cZ e (decide (bits.count true % 2 = 1)) (kOf (bits.count true))) := by
    have hq : bits.count true = (slicePos m K j₀ D ρ \ targets pairs).card := by
      rw [hbits, count_uvBits]
    rw [card_targets hpv, ← hq, selScalar_eq_toC]
    have h0 := addU_spec bits 0
    simp only [Nat.zero_div, Nat.add_zero, Nat.zero_add] at h0
    congr 2
    omega
  have hval : arrSyms (outRecs (decide (bits.count true % 2 = 1)) (fun _ => kOf (bits.count true))
      (w + 8 * d - min e (w + 8 * d)) (min e (w + 8 * d)) 0
      (recsOf (w + 8 * d) (encCube (P + 8 * d) y))) =
      carrSyms (w + 8 * d) (encCube (P + 8 * d) (cnotScanMap K j₀ D ρ pairs .selScalar y)) := by
    rw [arrSyms_outRecs, show cnotScanMap K j₀ D ρ pairs .selScalar y = diagArr (fun _ =>
      selScalar (targets pairs).card (slicePos m K j₀ D ρ \ targets pairs).card) y from rfl,
      encCube_scale (P + 8 * d) _ y hy (fun _ => cZ e (decide (bits.count true % 2 = 1))
        (kOf (bits.count true))) (fun _ => hsc)]
  have R := RunsR.seq (runsR_of_runs (runs_tplSetup P d r w K m j₀ D nS ρ hrest S hcl hH)
      (fun _ => True) (fun _ _ _ => trivial))
    (RunsR.seq (runsR_of_runsE (runs_uvBuild P d r w K m j₀ D nS ρ pairs hrest prest _ hm hρ
      (by simp [hH]) (by simp [hQ]) (by simp [hcl]) (by simp [hcl]) (by simp [hcl])
      (by simp [hcl]) (by simp [hcl]) (by simp [hcl]) (by simp [hcl]) (by simp [hcl])
      (by simp [hcl]) (by simp [hcl])))
    (RunsR.seq (runsR_of_runs (runs_unaryOfTop (src := (.inl 2 : SK)) (dst := .inr .n3)
      (bits := .inr .n1) (u := .inr .u) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) pairs.length
      (hdrSyms (pairs.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]) ++ prest) _ (by simp [hQ'])
      (by simp [hcl]) (by simp [hcl]) (by simp [hcl])) (fun _ => True) (fun _ _ _ => trivial))
    (RunsR.seq (runsR_load (fun r => { r with k := 0, mu := false }) _ (fun _ => True)
      (fun r => r.k = 0 ∧ r.mu = false) (fun _ _ => ⟨rfl, rfl⟩))
    (RunsR.seq (runsR_pcLoop bits _ (by simp [huv]))
    (RunsR.seq (runsR_clearE (.inr .tmp : SK) (bits.reverse.map Sym.bit) _ (by simp [hcl])
      (fun r : ER => r.mu = decide (bits.count true % 2 = 1) ∧ r.k = kOf (bits.count true))
      (fun _ h => h))
    (RunsR.seq (RunsR.mono (runsR_writeK _ (by simp [hcl]) (kOf (bits.count true))
      (decide (bits.count true % 2 = 1))) (fun _ h => ⟨h.2, h.1⟩) (fun _ h => h) le_rfl)
    (RunsR.seq (runsR_splitP (fun r : ER => r.mu = decide (bits.count true % 2 = 1))
      (fun _ _ _ h => h) e (w + 8 * d) _ (by simp [he]) (by simp) (by simp [hcl])
      (by simp [hcl]))
    (RunsR.seq (recLoopS_runs kRu inc0 (fun _ => kOf (bits.count true)) (fun _ => [])
      (kStat (kOf (bits.count true))) 30 1 (kRSpec_kRu _)
      (fun x S' r' hx _ => incSpec_inc0 x S' r' hx trivial) (statFrame_kStat _)
      (w + 8 * d - min e (w + 8 * d)) (min e (w + 8 * d)) (by omega)
      (decide (bits.count true % 2 = 1)) rest hrest'
      (recsOf (w + 8 * d) (encCube (P + 8 * d) y)) 0 _ hrecs
      ⟨by simp, by simp, by simp, by simp [hcl], by simp [hcl], by simp [hcl], by simp [hcl],
        by simp [hcl]⟩ ⟨by simp, by simp [hcl]⟩ (by simp [hcl]) (by rw [← hA2]; simp))
    (RunsR.seq (runsR_drainE (src := (.inr .o : SK)) (dst := .inl 0) (by decide)
      (arrSyms (outRecs (decide (bits.count true % 2 = 1)) (fun _ => kOf (bits.count true))
        (w + 8 * d - min e (w + 8 * d)) (min e (w + 8 * d)) 0
        (recsOf (w + 8 * d) (encCube (P + 8 * d) y)))).reverse
      _ (by simp [hcl]) (fun r : ER => r.mu = decide (bits.count true % 2 = 1)) (fun _ h => h))
    (RunsR.seq (runsR_clearE (.inr .tz : SK) (List.replicate (min e (w + 8 * d)) uSym)
      _ (by simp) (fun r : ER => r.mu = decide (bits.count true % 2 = 1)) (fun _ h => h))
    (RunsR.seq (runsR_clearE (.inr .tcc : SK)
      (List.replicate (w + 8 * d - min e (w + 8 * d)) uSym) _ (by simp)
      (fun r : ER => r.mu = decide (bits.count true % 2 = 1)) (fun _ h => h))
    (RunsR.seq (runsR_clearE (.inr .td : SK) (List.replicate (min e (w + 8 * d)) uSym) _
        (by simp) (fun r : ER => r.mu = decide (bits.count true % 2 = 1)) (fun _ h => h))
      (runsR_clearE (.inr .pl : SK) (List.replicate (kOf (bits.count true)).val uSym) _
        (by simp) (fun r : ER => r.mu = decide (bits.count true % 2 = 1))
        (fun _ h => h))))))))))))))
  rw [← hval]
  refine runs_mono (runs_congr (runs_of_runsR R) ?_) (fun _ _ => trivial) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp
    · cases e <;> simp [hcl]
  · have hk4 := (kOf (bits.count true)).isLt
    simp only [selScalarCost, sum_recsOf_encCube', List.length_reverse, List.length_map, hlen,
      hval, WalshCnot1.length_carrSyms_encCube, List.length_replicate]
    omega

/-- **K3.4b, mode `selScalar`, proved** (`CnotScanStmt .selScalar`, `Walsh/CnotLeaf.lean`;
Lemma 5.1 (`lem:walsh-select`): the scalar `2^s (2(1-i))^{q_sel}`, `s = |T|`,
`q_sel = |Sel ∖ T|`), with `J = 1` and `C = 1000`: the program `scanSelScalar`
(`scanSelScalar_runs`), scratch `SS` (clean on entry, restored), registers `ER`. Used
hypotheses: `j₀ + DK + nS = m`, `ρ < K` (the slice mask), `CnotPairsValid` (`s = |pairs|`),
the input disk-grid hypothesis (exact value), `P + 2 ≤ w`, `d ≤ w + m`, `K ≤ w + m` (cost). The
output disk-grid hypothesis is not needed. -/
theorem cnotScanSelScalar_holds : CnotScanStmt .selScalar := by
  refine ⟨1, 1000, fun _ => ⟨SS, inferInstance, inferInstance, ER, scanSelScalar, inferInstance,
    inferInstance, closed_scanSelScalar, ?_⟩⟩
  intro P d r w K m j₀ D nS ρ pairs y rest hrest prest S hcl hm hρ hw hd hK hpv hy _ hrest' hA
    hH hQ
  have hgrid : ArrOnGrid (P + 8 * d) y := fun x k => (hy x k).1
  refine runs_mono (scanSelScalar_runs P d r w K m j₀ D nS ρ pairs y rest hrest prest S hcl hm hρ
    hw hpv hgrid hrest' hA hH hQ _ rfl _ rfl) (fun _ _ => trivial) ?_
  have hlen : ((List.finRange m).reverse.map
      fun p => decide (p ∈ slicePos m K j₀ D ρ \ targets pairs)).length = m := by simp
  have hq := List.count_le_length (a := true) (l := (List.finRange m).reverse.map
      fun p => decide (p ∈ slicePos m K j₀ D ρ \ targets pairs))
  have h0 := addU_spec ((List.finRange m).reverse.map
      fun p => decide (p ∈ slicePos m K j₀ D ρ \ targets pairs)) 0
  simp only [Nat.zero_div, Nat.add_zero, Nat.zero_add] at h0
  have hX : w + m + 1 ≤ 2 ^ m * (w + m + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  have hP := length_le_pairsSyms pairs
  have hY : (pairsSyms pairs).length ≤ 2 ^ m * (pairsSyms pairs).length :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have hmp : m * pairs.length ≤ 2 ^ m * (pairsSyms pairs).length :=
    Nat.mul_le_mul Nat.lt_two_pow_self.le hP
  have hH' := length_sliceHdr P d r w K m j₀ D nS ρ
  have huv := uvCost_le P d r w K m j₀ D nS ρ pairs hm hρ
  set e := addU ((List.finRange m).reverse.map
      fun p => decide (p ∈ slicePos m K j₀ D ρ \ targets pairs)) 0 + pairs.length with he
  have hcc : coefCost (w + 8 * d - min e (w + 8 * d)) (min e (w + 8 * d)) + 2 ≤
      94 * (w + 8 * d) := by
    simp only [coefCost]
    omega
  have h3 : 2 ^ m * (30 + r * (coefCost (w + 8 * d - min e (w + 8 * d)) (min e (w + 8 * d)) +
      2) + 1 + 7) ≤ 47 * cvolCube m r (w + 8 * d) := by
    have h4 : 30 + r * (coefCost (w + 8 * d - min e (w + 8 * d)) (min e (w + 8 * d)) + 2) +
        1 + 7 ≤ 47 * (2 * r * (w + 8 * d) + 1) := by
      have := Nat.mul_le_mul_left r hcc
      nlinarith
    calc _ ≤ 2 ^ m * (47 * (2 * r * (w + 8 * d) + 1)) := Nat.mul_le_mul_left _ h4
      _ = 47 * cvolCube m r (w + 8 * d) := by simp only [cvolCube]; ring
  simp only [selScalarCost, tplCost]
  rw [pow_one, mul_add (2 ^ m) (w + m + 1) (pairsSyms pairs).length]
  omega

end SubNLogN.Machine.WalshScanAux
