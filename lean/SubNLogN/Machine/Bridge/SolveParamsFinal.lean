/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveParamsAsm
import SubNLogN.Machine.Bridge.SolveParamsDefs

/-!
# SOL-PARAM-ROWS (9): the kernel from a header parse

`solParamRows_of_hdr`: let `hp` be any closed header-parse program meeting `HdrParseSpec`, i.e. it
produces the rulers of `wT` and `wT + 1` bits and the counters `i - 1`, `t_i / 2` and
`∏_{l>i} t_l`. Then the program `hp ; bodyB` proves `SolParamRowsStmt`, with registers `BReg × R`
and scratch `Fin 25`. The cost bound is `bodyCost_le`.

All proved; helpers in `SubNLogN.Machine.Bridge.SolveParamsAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveParamsAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability
  SubNLogN.Math.Common SubNLogN.Math.Bridge
open WP.W9comp (runs_seq runs_mono runs_congr)

/-- The header-parse interface (proved in `SolveParamsHdr.lean`). -/
def HdrParseSpec {R : Type} (hp : Prog SK (fun _ => Sym) R) : Prop :=
  ∃ c : ℕ, ∀ (b : BrPar) (m : ℕ) (i : Fin b.d) (rpar rax : List Sym) (S : SK → List Sym),
    ShapeOK b.t → (i : ℕ) ≠ 0 → (i : ℕ) + m = b.d → 1 ≤ b.wT → TermOK rax →
    S sPar = hdrSyms b.hdr ++ rpar → S sAx = natSyms m ++ rax →
    (∀ e : Fin 25, S (.inr e) = []) →
    Runs hp S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        kRU (ruler b.wT)) kRX (ruler (b.wT + 1))) kCX (natSyms ((i : ℕ) - 1)))
        kCT (natSyms (b.t i / 2))) kCU (natSyms (suffixProd b.t i)))
      (fun _ => True) (c * (b.wT + b.setup))

/-! ## Data -/

/-- The record lists of the table blocks. -/
noncomputable def blOf (b : BrPar) (T : BridgeTables b.t) : List (List (List Bool)) :=
  (deconvOrder b.d).map fun a => (solBlock b.t b.P T a).map (crecBits b.wT)

theorem solTabSyms_eq (b : BrPar) (T : BridgeTables b.t) :
    solTabSyms b.wT b.P b.t T = tabSyms (blOf b T) := by
  simp only [solTabSyms, tabSyms, blOf, blkSyms, List.flatMap_def, List.map_map,
    Function.comp_def, SolveAux.carrSyms_eq_recsOf]

theorem length_crecBits_solRec (b : BrPar) (T : BridgeTables b.t) (a : Fin b.d) (u : ℕ) :
    (crecBits b.wT (solRec b.P T a u)).length = 6 * b.wT := by
  rw [crecBits_solRec]
  simp only [List.length_append, K1.length_twosBits]
  ring

theorem blOf_len (b : BrPar) (T : BridgeTables b.t) :
    ∀ rs ∈ blOf b T, ∀ bs ∈ rs, bs.length = 6 * b.wT := by
  intro rs hrs bs hbs
  simp only [blOf, List.mem_map] at hrs
  obtain ⟨a, _, rfl⟩ := hrs
  simp only [solBlock, List.map_map, List.mem_map, Function.comp_apply] at hbs
  obtain ⟨u, _, rfl⟩ := hbs
  exact length_crecBits_solRec b T a u

theorem length_blOf (b : BrPar) (T : BridgeTables b.t) : (blOf b T).length = b.d - 1 := by
  simp [blOf, BridgeRed.length_deconvOrder]

theorem blOf_getElem (b : BrPar) (T : BridgeTables b.t) (i : Fin b.d) (hi : (i : ℕ) ≠ 0)
    (h : (i : ℕ) - 1 < (blOf b T).length) :
    (blOf b T)[(i : ℕ) - 1] = recList b.wT (b.t i) (solGMu b.P T i)
      (fun u => -solGNa b.P T i u) (solGGm b.P T i) := by
  have hlt : (i : ℕ) - 1 < b.d - 1 := by have := i.2; omega
  have hlen : (i : ℕ) - 1 < (deconvOrder b.d).length := by
    rw [BridgeRed.length_deconvOrder]; exact hlt
  have hd : (deconvOrder b.d)[(i : ℕ) - 1]? = some i := by
    rw [BridgeRed.getElem?_deconvOrder b.d _ hlt]
    exact congrArg some (Fin.ext (show (i : ℕ) - 1 + 1 = (i : ℕ) by omega))
  have hd' : (deconvOrder b.d)[(i : ℕ) - 1] = i := by
    rw [List.getElem?_eq_getElem hlen] at hd
    exact Option.some.inj hd
  simp only [blOf, List.getElem_map, hd', solBlock, List.map_map, recList]
  apply List.map_congr_left
  intro u _
  simp only [Function.comp_apply, crecBits_solRec, recBits]

theorem fit_of_tablesFit (b : BrPar) (T : BridgeTables b.t) (i : Fin b.d) (hi : (i : ℕ) ≠ 0)
    (hfit : TablesFit b.wT b.P b.t T) :
    ∀ u, u < b.t i → FitsTwos b.wT (solGMu b.P T i u) ∧ FitsTwos b.wT (-solGNa b.P T i u) ∧
      FitsTwos b.wT (solGGm b.P T i u) := by
  intro u hu
  have hmem : i ∈ deconvOrder b.d := by simp [deconvOrder, hi]
  have hc := hfit.2 i hmem
  have hrec : solRec b.P T i u ∈ solBlock b.t b.P T i :=
    List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩
  have h1 := (hc _ hrec (realInt (b.P + 2) (T.mu i u), 0) (by simp [solRec])).1
  have h2 := (hc _ hrec (realInt (b.P + 2) (T.ahat i u), 0) (by simp [solRec])).1
  have h3 := (hc _ hrec (realInt (b.P + 2) (T.gam i u), 0) (by simp [solRec])).1
  refine ⟨h1, ?_, h3⟩
  simpa [solGNa] using h2

theorem carrSyms_solParamRow (b : BrPar) (i : Fin b.d) (h : ℕ) (g : ℕ → ℤ) (hS : ShapeOK b.t) :
    carrSyms (b.wT + 1) (solParamRow b i h g) =
      SolveAux.recsOf (rowRecs b.wT (suffixProd b.t i) (h * (b.t i / 2)) (b.t i / 2) g) := by
  rw [SolveAux.carrSyms_eq_recsOf, solParamRow_eq b i h g hS]
  simp only [rowRecs, List.map_flatMap, List.map_replicate, solU0]

/-! ## Closedness -/

theorem fb_L {p : SProg SK} (hp : p.Closed) : Prog.FreeBelow 0 (L p) :=
  WP.W9comp.closed_liftRegs _ hp

theorem fb_L_copyBlock (a b c : SK) : Prog.FreeBelow 0 (L (copyBlock a b c)) := fb_L (by
  simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
    dupBody, restoreR, popR, pushR, pushC, skip])

theorem fb_L_moveBlock (a b : SK) : Prog.FreeBelow 0 (L (moveBlock a b)) := fb_L (by
  simp [Prog.Closed, Prog.FreeBelow, moveBlock, moveBits, moveBitsBody, restoreR, skip, popR,
    pushC, pushR])

theorem fb_L_dec (a b : SK) : Prog.FreeBelow 0 (L (dec a b)) := fb_L (by
  simp [Prog.Closed, Prog.FreeBelow, dec, decFix, scanLoop, scanBody, peekR, popR, pushC, skip,
    moveBits, moveBitsBody, pushR])

theorem fb_L_moveRec (a b c : SK) : Prog.FreeBelow 0 (L (SolveAux.moveRec a b c)) := fb_L (by
  simp [Prog.Closed, Prog.FreeBelow, SolveAux.moveRec, moveBlock, moveBits, moveBitsBody,
    restoreR, skip, popR, pushC, pushR])

theorem fb_L_copyRec (a b c : SK) : Prog.FreeBelow 0 (L (SolveAux.copyRec a b c)) := fb_L (by
  simp [Prog.Closed, Prog.FreeBelow, SolveAux.copyRec, copyBlock, moveBlock, moveBits,
    moveBitsBody, restoreR, skip, moveBitsDup, dupBody, popR, pushC, pushR])

theorem fb_L_eraseRec (a : SK) : Prog.FreeBelow 0 (L (SolveAux.eraseRec a)) := fb_L (by
  simp [Prog.Closed, Prog.FreeBelow, SolveAux.eraseRec, popR])

theorem fb_L_drainRecs (a b c : SK) : Prog.FreeBelow 0 (L (SolveAux.drainRecs a b c)) := fb_L (by
  simp [Prog.Closed, Prog.FreeBelow, SolveAux.drainRecs, SolveAux.drainBody, SolveAux.moveRec,
    moveBlock, moveBits, moveBitsBody, restoreR, skip, popR, pushC, pushR, peekR])

theorem fb_L_moveSym (a b : SK) : Prog.FreeBelow 0 (L (BridgePP.moveSym a b)) :=
  fb_L (BridgePP.closed_moveSym a b)

theorem fb_lift_moveBlock (a b : SK) :
    Prog.FreeBelow 0 ((moveBlock a b).liftRegs (Lens.fst (Option Sym) Bool)) :=
  fb_L_moveBlock a b

theorem closed_bodyB : bodyB.Closed := by
  simp [Prog.Closed, Prog.FreeBelow, bodyB, navLoop, navCore, halfLoop, halfCore, skipLoop,
    skipCore, mainLoop, digitBody, digitSplit, stageId, stageNeg, rField, rLoop, rBody, dupB,
    emitOne, emitLoop, emitCore, drains, restLoop, restCore, clearBits, BridgeRed.peekTop, popB,
    peekB, pushCB, pushRB, pushFB, carryFB, setCarry, fb_L_copyBlock, fb_L_moveBlock, fb_L_dec,
    fb_L_moveRec, fb_L_copyRec, fb_L_eraseRec, fb_L_drainRecs, fb_L_moveSym, fb_lift_moveBlock]

/-! ## Cost -/

theorem bitLen_le_self (n : ℕ) : bitLen n ≤ n := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem bitLen_le_log2 {n R : ℕ} (h : n ≤ R) : bitLen n ≤ Nat.log2 R + 1 := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]
  exact le_trans (Nat.size_le_size h) (Nat.size_le.mpr Nat.lt_log2_self)

theorem loopCost_le_sum (B g : ℕ → ℕ) (c : ℕ) : ∀ N, (∀ n, n < N → B n ≤ g n + c) →
    loopCost B N ≤ (∑ n ∈ Finset.range N, g n) + N * (c + 1) + 1
  | 0, _ => by simp [loopCost]
  | N + 1, h => by
    have ih := loopCost_le_sum B g c N (fun n hn => h n (by omega))
    have hN := h N (by omega)
    simp only [loopCost, Finset.sum_range_succ]
    nlinarith

theorem sum_range_getD (f : List (List Bool) → ℕ) : ∀ bl : List (List (List Bool)),
    (∑ j ∈ Finset.range bl.length, f (bl.getD j [])) = (bl.map f).sum
  | [] => by simp
  | rs :: bl => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [sum_range_getD f bl, add_comm]

theorem navCost_le (bl : List (List (List Bool))) (N L0 : ℕ) (hN : N ≤ bl.length)
    (hNL : bitLen N ≤ L0) :
    1 + loopCost (fun n => navStepCost (bl.getD (N - (n + 1)) []) n + 1) N ≤
      (bl.map SolveAux.drainCost).sum + N * (6 * L0 + 13) + 2 := by
  have h1 := loopCost_le_sum (fun n => navStepCost (bl.getD (N - (n + 1)) []) n + 1)
    (fun n => SolveAux.drainCost (bl.getD (N - 1 - n) [])) (6 * L0 + 12) N (by
      intro n hn
      have hz : zerosLead (encodeNat (n + 1)) ≤ L0 :=
        le_trans (zerosLead_le_length _) (le_trans (bitLen_mono'' (by omega)) hNL)
      have he : N - (n + 1) = N - 1 - n := by omega
      simp only [navStepCost, he]
      omega)
  have h2 : (∑ n ∈ Finset.range N, SolveAux.drainCost (bl.getD (N - 1 - n) [])) =
      ∑ n ∈ Finset.range N, SolveAux.drainCost (bl.getD n []) :=
    Finset.sum_range_reflect (fun j => SolveAux.drainCost (bl.getD j [])) N
  have h3 : (∑ n ∈ Finset.range N, SolveAux.drainCost (bl.getD n [])) ≤
      ∑ n ∈ Finset.range bl.length, SolveAux.drainCost (bl.getD n []) :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hN)
  rw [sum_range_getD] at h3
  nlinarith

theorem drainCost_reverse (l : List (List Bool)) :
    SolveAux.drainCost l.reverse = SolveAux.drainCost l := by
  simp [SolveAux.drainCost, List.sum_reverse]

theorem restCost_le (bl : List (List (List Bool))) (N L0 : ℕ) (hN : N ≤ bl.length)
    (hNL : bitLen N ≤ L0) :
    1 + loopCost (fun n => navStepCost (bl.getD n []).reverse n + 1) N ≤
      (bl.map SolveAux.drainCost).sum + N * (6 * L0 + 13) + 2 := by
  have h1 := loopCost_le_sum (fun n => navStepCost (bl.getD n []).reverse n + 1)
    (fun n => SolveAux.drainCost (bl.getD n [])) (6 * L0 + 12) N (by
      intro n hn
      have hz : zerosLead (encodeNat (n + 1)) ≤ L0 :=
        le_trans (zerosLead_le_length _) (le_trans (bitLen_mono'' (by omega)) hNL)
      simp only [navStepCost, drainCost_reverse]
      omega)
  have h3 : (∑ n ∈ Finset.range N, SolveAux.drainCost (bl.getD n [])) ≤
      ∑ n ∈ Finset.range bl.length, SolveAux.drainCost (bl.getD n []) :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hN)
  rw [sum_range_getD] at h3
  nlinarith

theorem mainCost_le (w U H : ℕ) :
    1 + loopCost (fun n => digitCost w U n + 1) H ≤ H * (digitCost w U H + 2) + 2 := by
  have h := loopCost_le_mul' (fun n => digitCost w U n + 1) (digitCost w U H + 1) H (by
    intro n hn
    have : bitLen (n + 1) ≤ bitLen (H + 1) := bitLen_mono'' (by omega)
    simp only [digitCost]
    omega)
  nlinarith

theorem drainCost_take_rev (rl : List (List Bool)) (ℓ k : ℕ) (hℓ : ∀ bs ∈ rl, bs.length = ℓ)
    (hk : k ≤ rl.length) : SolveAux.drainCost (rl.take k).reverse = k * (6 * ℓ + 12) + 1 := by
  rw [drainCost_reverse, SolveAux.drainCost,
    sum_drain_const ℓ _ (fun bs hbs => hℓ bs (List.mem_of_mem_take hbs)), List.length_take,
    min_eq_left hk]

theorem drainCost_blk (b : BrPar) (T : BridgeTables b.t) (a : Fin b.d) :
    SolveAux.drainCost ((solBlock b.t b.P T a).map (crecBits b.wT)) =
      b.t a * (6 * (6 * b.wT) + 12) + 1 := by
  rw [SolveAux.drainCost, sum_drain_const (6 * b.wT) _ (fun bs hbs => by
    simp only [solBlock, List.map_map, List.mem_map, Function.comp_apply] at hbs
    obtain ⟨u, _, rfl⟩ := hbs
    exact length_crecBits_solRec b T a u)]
  simp [solBlock]

theorem sum_drainCost_blOf (b : BrPar) (T : BridgeTables b.t) :
    ((blOf b T).map SolveAux.drainCost).sum ≤ 12 * solTabLen b := by
  unfold blOf solTabLen
  generalize deconvOrder b.d = l
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, drainCost_blk] at ih ⊢
    nlinarith [Nat.zero_le (b.t a * b.wT)]

theorem length_le_hdrSyms : ∀ fs : List ℕ, fs.length ≤ (hdrSyms fs).length
  | [] => by simp [hdrSyms]
  | n :: fs => by
    have ih := length_le_hdrSyms fs
    simp only [hdrSyms, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem bodyCost_le (w N H U u0 Lh ST Λ : ℕ) (bl : List (List (List Bool)))
    (rl : List (List Bool)) (hw : 1 ≤ w) (hH : 1 ≤ H) (hU : 1 ≤ U) (hN : N ≤ bl.length)
    (hNL : N ≤ Lh) (hbH : bitLen H ≤ Λ) (hbH1 : bitLen (H + 1) ≤ Λ) (hbU : bitLen U ≤ Λ)
    (hST : (bl.map SolveAux.drainCost).sum ≤ 12 * ST) (hrl : ∀ bs ∈ rl, bs.length = 6 * w)
    (hu0 : u0 ≤ H) (hu0H : u0 + H ≤ rl.length) :
    bodyCost w N H U u0 bl rl ≤ 2000 * (H * U * (w + Λ)) + 24 * ST + 200 * (Lh + 1) ^ 2 := by
  have hbN : bitLen N ≤ Lh := le_trans (bitLen_le_self N) hNL
  have hHU : 1 ≤ H * U := Nat.mul_le_mul hH hU
  have hH1 : H * 1 ≤ H * U := Nat.mul_le_mul_left H hU
  have q1 : H * w ≤ H * U * w := by
    have := Nat.mul_le_mul_right w hH1; rwa [Nat.mul_one] at this
  have q2 : H ≤ H * U * w := by
    have := Nat.mul_le_mul hH1 hw; rwa [Nat.mul_one, Nat.mul_one] at this
  have q3 : H * U ≤ H * U * w := by
    have := Nat.mul_le_mul_left (H * U) hw; rwa [Nat.mul_one] at this
  have q4 : H * U * bitLen U ≤ H * U * Λ := Nat.mul_le_mul_left (H * U) hbU
  have q5 : H * bitLen U ≤ H * U * Λ := by
    have := Nat.mul_le_mul hH1 hbU; rwa [Nat.mul_one] at this
  have q6 : H * bitLen (H + 1) ≤ H * U * Λ := by
    have := Nat.mul_le_mul hH1 hbH1; rwa [Nat.mul_one] at this
  have q7 : H * bitLen H ≤ H * U * Λ := by
    have := Nat.mul_le_mul hH1 hbH; rwa [Nat.mul_one] at this
  have q8 : Λ ≤ H * U * Λ := by
    have := Nat.mul_le_mul_right Λ hHU; rwa [Nat.one_mul] at this
  have q10 : w ≤ H * U * w := by
    have := Nat.mul_le_mul_right w hHU; rwa [Nat.one_mul] at this
  have q11 : 1 ≤ H * U * w := by
    have := Nat.mul_le_mul hHU hw; rwa [Nat.one_mul] at this
  have q12 : u0 * w ≤ H * w := Nat.mul_le_mul_right w hu0
  have q14 : N * Lh ≤ Lh * Lh := Nat.mul_le_mul_right Lh hNL
  have t2 := navCost_le bl N Lh hN hbN
  have t5 := mainCost_le w U H
  have t7 := drainCost_take_rev rl (6 * w) (u0 + H) hrl hu0H
  have t9 := restCost_le bl N Lh hN hbN
  simp only [bodyCost, digitCost, emitCost] at t5 ⊢
  rw [t7]
  have z1 := Nat.zero_le (Lh * Lh)
  have z2 := Nat.zero_le (N * Lh)
  have z3 := Nat.zero_le (H * U * Λ)
  have z4 := Nat.zero_le (H * U * w)
  linarith [t2, t5, t9, hST, q1, q2, q3, q4, q5, q6, q7, q8, q10, q11, q12, q14, hbN, hNL, hbH,
    hbU, z1, z2, z3, z4]

/-! ## Assembly -/

/-- The full program: the header parse, then `bodyB` (registers `BReg × R`). -/
def fullProg {R : Type} (hp : Prog SK (fun _ => Sym) R) : Prog SK (fun _ => Sym) (BReg × R) :=
  .seq (hp.liftRegs (Lens.snd BReg R)) (bodyB.liftRegs (Lens.fst BReg R))

theorem closed_fullProg {R : Type} {hp : Prog SK (fun _ => Sym) R} (hcl : hp.Closed) :
    (fullProg hp).Closed :=
  WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs _ hcl)
    (WP.W9comp.closed_liftRegs _ closed_bodyB)

/-- **SOL-PARAM-ROWS from a header parse.** -/
theorem solParamRows_of_hdr {R : Type} [Finite R] [Nonempty R] (hp : Prog SK (fun _ => Sym) R)
    (hcl : hp.Closed) (hspec : HdrParseSpec hp) : SolParamRowsStmt := by
  obtain ⟨ch, hch⟩ := hspec
  refine ⟨ch + 2300, fun _ => ⟨Fin 25, inferInstance, inferInstance, BReg × R, fullProg hp,
    inferInstance, inferInstance, closed_fullProg hcl, ?_⟩⟩
  intro b m h i T rsol rpar rax rh S hS hShape hi him hh hw hgrid hfit hrax hrh hTab hPar hAx
    hHalf
  have hS' : ∀ e : Fin 25, S (.inr e) = [] := hS
  have hti := (hShape i).1
  have hU := suffixProd_pos hShape i
  have hR := prefixProd_mul_mul_suffixProd b.t i
  have hA := prefixProd_pos'' hShape i
  have hNlt : (i : ℕ) - 1 < (blOf b T).length := by
    rw [length_blOf]; have := i.2; omega
  have hrl := blOf_getElem b T i hi hNlt
  have hfit' := fit_of_tablesFit b T i hi hfit
  rw [solTabSyms_eq] at hTab
  have hbody := runs_bodyB b.wT hw (blOf b T) ((i : ℕ) - 1) hNlt (blOf_len b T) (b.t i)
    (suffixProd b.t i) (b.t i / 2) h hh (Nat.mul_div_le (b.t i) 2) (solGMu b.P T i)
    (fun u => -solGNa b.P T i u) (solGGm b.P T i) hfit' hrl rsol rh hrh S hS' hTab hHalf
  have hhdr := hch b m i rpar rax S hShape hi him hw hrax hPar hAx hS'
  refine runs_mono (runs_congr (runs_seq (BridgePP.runs_liftRegs _ hhdr)
    (BridgePP.runs_liftRegs _ hbody)) ?_) (fun _ _ => trivial) ?_
  · funext k
    by_cases k4 : k = sMU
    · subst k4; simp [Function.update_apply, carrSyms_solParamRow _ _ _ _ hShape]
    by_cases k5 : k = sNA
    · subst k5; simp [Function.update_apply, carrSyms_solParamRow _ _ _ _ hShape]
    by_cases k6 : k = sGM
    · subst k6; simp [Function.update_apply, carrSyms_solParamRow _ _ _ _ hShape]
    have k4' : k ≠ .inl 4 := k4
    have k5' : k ≠ .inl 5 := k5
    have k6' : k ≠ .inl 6 := k6
    simp [Function.update_apply, k4, k5, k6, k4', k5', k6']
  · have hM := solHalfM_eq b i hShape
    have hH1 : 1 ≤ b.t i / 2 := by omega
    have htR : b.t i ≤ totalLen b.t := by
      rw [← hR]
      calc b.t i = 1 * b.t i * 1 := by ring
        _ ≤ prefixProd b.t i * b.t i * suffixProd b.t i :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hA) hU
    have hHR : b.t i / 2 + 1 ≤ totalLen b.t := le_trans (by omega) htR
    have hUR : suffixProd b.t i ≤ totalLen b.t := by
      rw [← hR]
      calc suffixProd b.t i = 1 * 1 * suffixProd b.t i := by ring
        _ ≤ prefixProd b.t i * b.t i * suffixProd b.t i :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul hA (by omega))
    have hdl : b.hdr.length = 9 + b.d := by
      simp only [BrPar.hdr, List.length_append, List.length_ofFn, List.length_cons,
        List.length_nil] <;> omega
    have hNL : (i : ℕ) - 1 ≤ (hdrSyms b.hdr).length := by
      have := length_le_hdrSyms b.hdr; have := i.2; omega
    have hrlen : ∀ bs ∈ recList b.wT (b.t i) (solGMu b.P T i) (fun u => -solGNa b.P T i u)
        (solGGm b.P T i), bs.length = 6 * b.wT := by
      intro bs hbs
      simp only [recList, List.mem_map] at hbs
      obtain ⟨u, _, rfl⟩ := hbs
      exact length_recBits _ _ _ _
    have hlen : (recList b.wT (b.t i) (solGMu b.P T i) (fun u => -solGNa b.P T i u)
        (solGGm b.P T i)).length = b.t i := by simp [recList]
    have hu0 : h * (b.t i / 2) ≤ b.t i / 2 := by
      rcases (show h = 0 ∨ h = 1 by omega) with rfl | rfl <;> omega
    have hbc := bodyCost_le b.wT ((i : ℕ) - 1) (b.t i / 2) (suffixProd b.t i)
      (h * (b.t i / 2)) (hdrSyms b.hdr).length (solTabLen b) (Nat.log2 (totalLen b.t) + 1)
      (blOf b T) _ hw hH1 hU hNlt.le hNL (bitLen_le_log2 (by omega))
      (bitLen_le_log2 hHR) (bitLen_le_log2 hUR) (sum_drainCost_blOf b T) hrlen hu0
      (by rw [hlen]; have := Nat.mul_div_le (b.t i) 2; omega)
    have hset : ((hdrSyms b.hdr).length + 1) ^ 2 ≤ b.setup := by
      unfold BrPar.setup
      exact Nat.pow_le_pow_right (by omega) (by norm_num)
    have hHU : 1 ≤ b.t i / 2 * suffixProd b.t i := Nat.mul_le_mul hH1 hU
    rw [hM]
    have e1 : b.t i / 2 * suffixProd b.t i * (b.wT + (Nat.log2 (totalLen b.t) + 1)) =
        b.t i / 2 * suffixProd b.t i * (b.wT + Nat.log2 (totalLen b.t) + 1) := by ring
    rw [e1] at hbc
    have hch' : ch * (b.wT + b.setup) ≤ ch * (b.t i / 2 * suffixProd b.t i *
        (b.wT + Nat.log2 (totalLen b.t) + 1) + solTabLen b + b.setup) :=
      Nat.mul_le_mul_left ch (by
        nlinarith [Nat.mul_le_mul_right (b.wT + Nat.log2 (totalLen b.t) + 1) hHU])
    have e2 : (ch + 2300) * (b.t i / 2 * suffixProd b.t i *
        (b.wT + Nat.log2 (totalLen b.t) + 1) + solTabLen b + b.setup) =
        ch * (b.t i / 2 * suffixProd b.t i * (b.wT + Nat.log2 (totalLen b.t) + 1) +
          solTabLen b + b.setup) + 2300 * (b.t i / 2 * suffixProd b.t i *
          (b.wT + Nat.log2 (totalLen b.t) + 1) + solTabLen b + b.setup) := by ring
    rw [e2]
    omega

end SubNLogN.Machine.Bridge.SolveParamsAux
