/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanShift
import SubNLogN.Machine.K1.Twos

/-!
# `SubNLogN.Machine.Walsh.CnotScanModeShift`: the scan `×2^s` (mode `shift`)

Paper: Proposition 5.5 (`prop:cnot-batch`, the final multiplication by `2^s` of a CNOT
batch) and Lemma 5.3 (`lem:walsh-lift`: `P_* = P + 8d`, `w_* = w + 8d`). Plan: top of
`Walsh/CnotScanEngine.lean`.

**Scope (honest summary).**
* `closed_coefProg`, `closed_recLoopS`: closedness of the coefficient and record loops.
* `scanShift_runs`: the program `scanShift` maps the lifted array
  `carrSyms W (encCube F y)` (`W = w + 8d`, `F = P + 8d`, `y` on the `F`-grid) to
  `carrSyms W (encCube F (scaleArr (2^s) y))`, `s = |pairs|` (read from the count field of the pair
  list), restoring every other stack, within `shiftCost`. The fields are multiplied by `2^s` as
  `W`-bit two's-complement words (exact modulo `2^W`), so no fit hypothesis is used here.
* `cnotScanShift_holds : CnotScanStmt .shift` (with `J = 1`).
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine WalshLift Computability
open SubNLogN.Math.Walsh SubNLogN.Math.Common
open WP.W9comp (runs_mono runs_congr)

/-! ## Closedness -/

theorem closed_coefProg : coefProg.Closed := by
  have hd : ∀ a b : SK, ((drain a b).liftRegs lT).FreeBelow 0 :=
    fun a b => WP.W9comp.closed_liftRegs lT (closed_drain a b)
  have hc : ∀ a : SK, ((clear a).liftRegs lT).FreeBelow 0 :=
    fun a => WP.W9comp.closed_liftRegs lT (closed_clear a)
  simp [Prog.Closed, Prog.FreeBelow, coefProg, readField, outField, resetC, readWalk, readStep,
    zWalk, zStep, dWalk, dStep, cWalk, cStep, popT, popS, pushT, pushS, pushK, hd, hc]

theorem closed_recLoopS {kR incR : EProg SK} (h1 : kR.Closed) (h2 : incR.Closed) :
    (recLoopS kR incR).Closed := by
  have hc := closed_coefProg
  simp only [Prog.Closed] at h1 h2 hc ⊢
  simp [Prog.FreeBelow, recLoopS, recBodyS, coefLoop, peekT, popT, pushK, h1, h2, hc]

/-! ## Unit routine and index increment of the scalar scans -/

/-- Unit routine of the scalar scans: `k := 0` (no address work). -/
def kR0 : EProg SK := .load fun r => { r with k := 0 }

/-- Index increment of the scalar scans: nothing (no index is kept). -/
def inc0 : EProg SK := .load id

theorem kRSpec_kR0 : KRSpec kR0 (fun _ => 0) (fun _ => []) (fun _ => True) 1 :=
  fun _ S r _ _ => ⟨{ r with k := 0 }, 1, Eval.load [] _ r S, rfl, rfl, le_rfl⟩

theorem incSpec_inc0 : IncSpec inc0 (fun _ => []) (fun _ => True) 1 := by
  intro x S r hx _
  have hx' : S (.inr .x) = [] := hx
  have hu : Function.update S (.inr .x) ([] : List Sym) = S := by
    funext j
    by_cases h : j = .inr .x
    · subst h
      simp [hx']
    · simp [h]
  exact ⟨r, 1, (Eval.load [] id r S).of_eq (by simp only [id, hu]) rfl, rfl, le_rfl⟩

theorem statFrame_true : StatFrame (fun _ => True) := fun _ _ _ h => h

/-! ## Value and cost facts -/

theorem two_pow_eq_toC (e : ℕ) : (2 : ℂ) ^ e = toC (cZ e false 0) := by
  have h : (2 : ℂ) ^ e = (((2 : ℝ) ^ e : ℝ) : ℂ) := by push_cast; rfl
  rw [h]
  apply Complex.ext
  · rw [Complex.ofReal_re]
    simp [toC, cZ, gfacZ, unitZ, cmulC]
  · rw [Complex.ofReal_im]
    simp [toC, cZ, gfacZ, unitZ, cmulC]

theorem sum_recsOf_encCube (W F n1 n2 : ℕ) {m r : ℕ} (y : RArr (Cube m) r) :
    ((recsOf W (encCube F y)).map fun cs => 1 + cs.length * (coefCost n1 n2 + 2) + 1 + 7).sum =
      2 ^ m * (r * (coefCost n1 n2 + 2) + 9) := by
  simp only [recsOf, encCube, encArr, cubeAddrs, List.map_map, Function.comp_def, List.length_map,
    List.length_finRange]
  rw [WalshCnot1.sum_range_const]
  ring

theorem length_le_hdrSyms : ∀ l : List ℕ, l.length ≤ (hdrSyms l).length
  | [] => by simp [hdrSyms]
  | a :: l => by
    have := length_le_hdrSyms l
    rw [WalshCnot1.length_hdrSyms_cons, List.length_cons]
    omega

theorem length_le_pairsSyms {m : ℕ} (pairs : List (Fin m × Fin m)) :
    pairs.length ≤ (pairsSyms pairs).length := by
  have h1 := length_le_hdrSyms (pairs.length :: pairs.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)])
  have h2 : ∀ ps : List (Fin m × Fin m),
      (ps.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]).length = 2 * ps.length := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
      omega
  rw [pairsSyms]
  simp only [List.length_cons, h2] at h1
  omega

theorem pairsSyms_eq {m : ℕ} (pairs : List (Fin m × Fin m)) (prest : List Sym) :
    pairsSyms pairs ++ prest = natSyms pairs.length ++ Sym.mark ::
      (hdrSyms (pairs.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]) ++ prest) := by
  simp [pairsSyms, hdrSyms]

/-! ## The program -/

/-- The scan `×2^s`, `s = |pairs|`: the template `tcc = uSym^W` from the header, `n3 = uSym^s`
from the pair count, the split `tz = td = uSym^{min s W}`, `tcc = uSym^{W - min s W}`, the record
loop with `k = 0`, `μ = false`, the output moved back onto the array, the templates cleared. -/
def scanShift : EProg SK :=
  .seq (tplSetup.liftRegs lT)
  (.seq ((unaryOfTop (.inl 2) (.inr .n3) (.inr .n1) (.inr .u)).liftRegs lT)
  (.seq splitP
  (.seq (.load fun r => { r with k := 0, mu := false })
  (.seq (recLoopS kR0 inc0)
  (.seq ((drain (.inr .o) (.inl 0)).liftRegs lT)
  (.seq ((clear (.inr .tz)).liftRegs lT)
  (.seq ((clear (.inr .tcc)).liftRegs lT)
    ((clear (.inr .td)).liftRegs lT))))))))

theorem closed_scanShift : scanShift.Closed := by
  have h0 : (recLoopS kR0 inc0).Closed :=
    closed_recLoopS (by simp [Prog.Closed, Prog.FreeBelow, kR0])
      (by simp [Prog.Closed, Prog.FreeBelow, inc0])
  unfold scanShift
  exact WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT closed_tplSetup)
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_unaryOfTop _ _ _ _))
    (WP.W9comp.closed_seq closed_splitP
    (WP.W9comp.closed_seq (by simp [Prog.Closed, Prog.FreeBelow])
    (WP.W9comp.closed_seq h0
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_drain _ _))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_clear _))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_clear _))
      (WP.W9comp.closed_liftRegs lT (closed_clear _)))))))))

/-- The cost bound of `scanShift` (`W = w + 8d`, `e = |pairs|`). -/
def shiftCost (P d r w m e : ℕ) : ℕ :=
  tplCost P d r w + 26 * e + 18 +
    2 ^ m * (r * (coefCost (w + 8 * d - min e (w + 8 * d)) (min e (w + 8 * d)) + 2) + 9) +
    3 * cvolCube m r (w + 8 * d) + 4 * (w + 8 * d)

theorem scanShift_runs (P d r w K m j₀ D nS ρ : ℕ) (pairs : List (Fin m × Fin m))
    (y : RArr (Cube m) r) (rest hrest prest : List Sym) (S : SK → List Sym)
    (hcl : ∀ e : SS, S (.inr e) = []) (hw : P + 2 ≤ w) (hy : ArrOnGrid (P + 8 * d) y)
    (hrest' : BlkTerm rest)
    (hA : S (.inl 0) = carrSyms (w + 8 * d) (encCube (P + 8 * d) y) ++ rest)
    (hH : S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest)
    (hQ : S (.inl 2) = pairsSyms pairs ++ prest) :
    Runs scanShift S
      (Function.update S (.inl 0)
        (carrSyms (w + 8 * d) (encCube (P + 8 * d) (scaleArr (2 ^ pairs.length) y)) ++ rest))
      (fun _ => True) (shiftCost P d r w m pairs.length) := by
  have hQ' := hQ.trans (pairsSyms_eq pairs prest)
  have hA2 : S (.inl 0) = arrSyms ((recsOf (w + 8 * d) (encCube (P + 8 * d) y)).map
      fun cs => cs.flatMap fun c => c.1 ++ c.2) ++ rest := by
    rw [hA, carrSyms_recsOf]
  have hrecs : ∀ cs ∈ recsOf (w + 8 * d) (encCube (P + 8 * d) y), ∀ c ∈ cs,
      c.1.length = (w + 8 * d - min pairs.length (w + 8 * d)) + min pairs.length (w + 8 * d) ∧
      c.2.length = (w + 8 * d - min pairs.length (w + 8 * d)) + min pairs.length (w + 8 * d) := by
    intro cs hcs c hc
    simp only [recsOf, List.mem_map] at hcs
    obtain ⟨cs0, -, rfl⟩ := hcs
    obtain ⟨c0, -, rfl⟩ := List.mem_map.1 hc
    simp only [K1.length_twosBits]
    constructor <;> omega
  have hval : arrSyms (outRecs false (fun _ => 0) (w + 8 * d - min pairs.length (w + 8 * d))
      (min pairs.length (w + 8 * d)) 0 (recsOf (w + 8 * d) (encCube (P + 8 * d) y))) =
      carrSyms (w + 8 * d) (encCube (P + 8 * d) (scaleArr (2 ^ pairs.length) y)) := by
    rw [arrSyms_outRecs,
      show scaleArr (2 ^ pairs.length) y = diagArr (fun _ => (2 : ℂ) ^ pairs.length) y from rfl,
      encCube_scale (P + 8 * d) _ y hy (fun _ => cZ pairs.length false 0)
        (fun _ => two_pow_eq_toC pairs.length)]
  have R := RunsR.seq (runsR_of_runs (runs_tplSetup P d r w K m j₀ D nS ρ hrest S hcl hH)
      (fun _ => True) (fun _ _ _ => trivial))
    (RunsR.seq (runsR_of_runs (runs_unaryOfTop (src := (.inl 2 : SK)) (dst := .inr .n3)
      (bits := .inr .n1) (u := .inr .u) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) pairs.length
      (hdrSyms (pairs.flatMap fun p => [(p.1 : ℕ), (p.2 : ℕ)]) ++ prest) _ (by simp [hQ'])
      (by simp [hcl]) (by simp [hcl]) (by simp [hcl])) (fun _ => True) (fun _ _ _ => trivial))
    (RunsR.seq (runsR_splitP (fun _ => True) (fun _ _ _ _ => trivial) pairs.length (w + 8 * d) _
      (by simp) (by simp) (by simp [hcl]) (by simp [hcl]))
    (RunsR.seq (runsR_load (fun r => { r with k := 0, mu := false }) _ (fun _ => True)
      (fun r => r.mu = false) (fun _ _ => rfl))
    (RunsR.seq (recLoopS_runs kR0 inc0 (fun _ => 0) (fun _ => []) (fun _ => True) 1 1 kRSpec_kR0
      incSpec_inc0 statFrame_true (w + 8 * d - min pairs.length (w + 8 * d))
      (min pairs.length (w + 8 * d)) (by omega) false rest hrest'
      (recsOf (w + 8 * d) (encCube (P + 8 * d) y)) 0 _ hrecs
      ⟨by simp, by simp, by simp, by simp [hcl], by simp [hcl], by simp [hcl], by simp [hcl],
        by simp [hcl]⟩ trivial (by simp [hcl]) (by rw [← hA2]; simp))
    (RunsR.seq (runsR_drainE (src := (.inr .o : SK)) (dst := .inl 0) (by simp)
      (arrSyms (outRecs false (fun _ => 0) (w + 8 * d - min pairs.length (w + 8 * d))
        (min pairs.length (w + 8 * d)) 0 (recsOf (w + 8 * d) (encCube (P + 8 * d) y)))).reverse
      _ (by simp [hcl]) (fun r : ER => r.mu = false) (fun _ h => h))
    (RunsR.seq (runsR_clearE (.inr .tz : SK) (List.replicate (min pairs.length (w + 8 * d)) uSym)
      _ (by simp) (fun r : ER => r.mu = false) (fun _ h => h))
    (RunsR.seq (runsR_clearE (.inr .tcc : SK)
      (List.replicate (w + 8 * d - min pairs.length (w + 8 * d)) uSym) _ (by simp)
      (fun r : ER => r.mu = false) (fun _ h => h))
      (runsR_clearE (.inr .td : SK) (List.replicate (min pairs.length (w + 8 * d)) uSym) _
        (by simp) (fun r : ER => r.mu = false) (fun _ h => h)))))))))
  rw [← hval]
  refine runs_mono (runs_congr (runs_of_runsR R) ?_) (fun _ _ => trivial) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp
    · cases e <;> simp [hcl]
  · simp only [shiftCost, sum_recsOf_encCube, List.length_reverse, hval,
      WalshCnot1.length_carrSyms_encCube, List.length_replicate]
    omega

/-- **K3.4b, mode `shift`, proved** (`CnotScanStmt .shift`, `Walsh/CnotLeaf.lean`;
Proposition 5.5 (`prop:cnot-batch`), the final `×2^s` of a CNOT batch, `s = |pairs|`), with `J = 1` and `C = 200`:
the program `scanShift` (`scanShift_runs`), scratch `SS` (clean on entry, restored), registers
`ER`. The hypotheses `j₀ + DK + nS = m`, `ρ < K`, `K ≤ w + m`, `CnotPairsValid pairs` and the
output disk-grid hypothesis are not needed for this mode; `P + 2 ≤ w` (so `W ≥ 2`) and
`d ≤ w + m` enter the cost bound, the input grid hypothesis the exact value. -/
theorem cnotScanShift_holds : CnotScanStmt .shift := by
  refine ⟨1, 200, fun _ => ⟨SS, inferInstance, inferInstance, ER, scanShift, inferInstance,
    inferInstance, closed_scanShift, ?_⟩⟩
  intro P d r w K m j₀ D nS ρ pairs y rest hrest prest S hcl _ _ hw hd _ _ hy _ hrest' hA hH hQ
  have hgrid : ArrOnGrid (P + 8 * d) y := fun x k => (hy x k).1
  refine runs_mono (scanShift_runs P d r w K m j₀ D nS ρ pairs y rest hrest prest S hcl hw hgrid
    hrest' hA hH hQ) (fun _ _ => trivial) ?_
  have hX : w + m + 1 ≤ 2 ^ m * (w + m + 1) := Nat.le_mul_of_pos_left _ (by positivity)
  have hY : pairs.length ≤ 2 ^ m * (pairsSyms pairs).length :=
    (length_le_pairsSyms pairs).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hH' := length_sliceHdr P d r w K m j₀ D nS ρ
  have hcc : coefCost (w + 8 * d - min pairs.length (w + 8 * d)) (min pairs.length (w + 8 * d)) +
      2 ≤ 94 * (w + 8 * d) := by
    simp only [coefCost]
    omega
  have h3 : 2 ^ m * (r * (coefCost (w + 8 * d - min pairs.length (w + 8 * d))
      (min pairs.length (w + 8 * d)) + 2) + 9) ≤ 47 * cvolCube m r (w + 8 * d) := by
    have h4 : r * (coefCost (w + 8 * d - min pairs.length (w + 8 * d))
        (min pairs.length (w + 8 * d)) + 2) + 9 ≤ 47 * (2 * r * (w + 8 * d) + 1) := by
      have := Nat.mul_le_mul_left r hcc
      nlinarith
    calc _ ≤ 2 ^ m * (47 * (2 * r * (w + 8 * d) + 1)) := Nat.mul_le_mul_left _ h4
      _ = 47 * cvolCube m r (w + 8 * d) := by simp only [cvolCube]; ring
  simp only [shiftCost, tplCost]
  rw [pow_one, mul_add (2 ^ m) (w + m + 1) (pairsSyms pairs).length]
  omega

end SubNLogN.Machine.WalshScanAux
