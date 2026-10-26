/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadStageMainBase
import SubNLogN.Machine.Bridge.SpreadStageLoop
import SubNLogN.Machine.Bridge.SpreadStageAR2
import SubNLogN.Machine.Bridge.SpreadLine

/-!
# K5 spreading, stage main (2): `SpreadLinesStmt` (`Bridge/SpreadStageMain.lean`)

The composition of one spreading stage (`SpreadLinesStmt`, `Contracts/Bridge.lean`):
`stageProg Ps PF PL = setup ; stagePre ; groupLoop ; stagePost`, with
* the setup kernel `Ps` of `SpreadSetupStmt` (rulers on `sp (.ru r)`, `Stage.runs_setupCall`);
* `stagePre` (product rulers, skip of the tap-table blocks before the axis block onto `TT`);
* the stage double loop `Stage.groupLoop` (`Stage.runs_groupLoop`): the filter packer `PF` of
  `PackFilterStmt` and the line step `PL` of `SpreadLineStmt`;
* `stagePost` (restore the tap table, move the outputs onto `arr`, clear the rulers).
The outputs are the stage values by `SpreadStageValStmt` (`stageVals_eq`), and the cost is
within `Ctot · spreadCost` (`stage_cost_le`, `SpreadStageMainBase.lean`).

Main results: `SpreadAux.spreadLines_of (hS : SpreadSetupStmt) (hL : SpreadLineStmt) :
SpreadLinesStmt`, `SpreadAux.spreadLines_of_line (hL : SpreadLineStmt) : SpreadLinesStmt` and the
unconditional `SpreadAux.spreadLines_holds : SpreadLinesStmt` (from `spreadSetup_holds` and
`Line.spreadLine_holds`). Everything is proved. Helpers live in
`SubNLogN.Machine.Bridge.SpreadAux.StageMain`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux.StageMain

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Arith Computability
  SubNLogN.Machine.Bridge.SpreadAux SubNLogN.Machine.Bridge.SpreadAux.Stage SubNLogN.Math.Common
  SubNLogN.Math.Bridge

/-! ## The stage program -/

section Prog

variable {Es Rs Rm : Type} [DecidableEq Es]

/-- Registers of the stage: the setup kernel's, the AR registers, `mulBig`'s. -/
abbrev Sg (Rs Rm : Type) : Type := Rs × (AReg × Rm)

/-- Lens to the setup registers. -/
def lensS : Lens (Sg Rs Rm) Rs := Lens.fst _ _

/-- Lens to the AR registers. -/
def lensA : Lens (Sg Rs Rm) AReg := (Lens.snd _ _).comp (Lens.fst _ _)

/-- Lens to the `mulBig` registers. -/
def lensM : Lens (Sg Rs Rm) Rm := (Lens.snd _ _).comp (Lens.snd _ _)

/-- **The stage program**: setup ; `stagePre` ; the double loop ; `stagePost`. -/
def stageProg (Ps : Prog (KLoc SetupN Es) (fun _ => Sym) Rs) (PF : AProg (SK Es))
    (PL : Prog (SK Es) (fun _ => Sym) (Sg Rs Rm)) : Prog (SK Es) (fun _ => Sym) (Sg Rs Rm) :=
  .seq (callInj ιSU lensS Ps) (.seq (ar lensA stagePre)
    (.seq (groupLoop lensA PF PL) (ar lensA stagePost)))

theorem closed_stageProg {Ps : Prog (KLoc SetupN Es) (fun _ => Sym) Rs} {PF : AProg (SK Es)}
    {PL : Prog (SK Es) (fun _ => Sym) (Sg Rs Rm)} (hPs : Ps.Closed) (hPF : PF.Closed)
    (hPL : PL.Closed) : (stageProg Ps PF PL).Closed :=
  closed_seq' (closed_callInj ιSU lensS hPs) (closed_seq' (closed_ar lensA closed_stagePre)
    (closed_seq' (closed_groupLoop lensA hPF hPL) (closed_ar lensA closed_stagePost)))

/-- The body of `SpreadSetupStmt` for one program `Ps` with constant `Cs`. -/
def SetupSpec (Ps : Prog (KLoc SetupN Es) (fun _ => Sym) Rs) (Cs : ℕ) : Prop :=
  ∀ (b : BrPar) (i : Fin b.d) (rax rpar : List Sym) (S : KLoc SetupN Es → List Sym),
    KClean S → ShapeOK b.t → (i : ℕ) ≠ 0 → 1 ≤ b.wI → 1 ≤ b.wT →
    b.P + 2 ≤ b.wI → Nat.log2 (totalLen b.t) ≤ b.wI → TermOK rax →
    S (.inl .par) = hdrSyms b.hdr ++ rpar → S (.inl .ax) = natSyms i ++ rax →
    (∀ r, S (.inl (.ru r)) = []) →
    Runs Ps S (withRulers b i S) (fun _ => True) (Cs * (b.setup + b.R + spreadSlot b i))

end Prog


/-! ## The stage cost in terms of the bridge parameters -/

theorem stage_cost_b (Cs CF CL : ℕ) (b : BrPar) (i : Fin b.d) (ht : ShapeOK b.t)
    (hi0 : (i : ℕ) ≠ 0) (L1 L2 sumR : ℕ) (hL : L1 + L2 ≤ tapTabLen b)
    (hsum : sumR ≤ 22 * (totalLen b.t * (2 * b.wI + 1) + totalLen b.t * spreadSlot b i +
      b.setup)) :
    Cs * (b.setup + b.R + spreadSlot b i) +
      (stagePreCost (spreadWin b.t b.P i - 1) (2 * b.wI + 1) (b.t i) (spreadA0 b i)
          (b.t i - spreadA0 b i) (spreadSlot b i) (b.d - 1 - i) L1 +
        ((prefixProd b.t i * (grpCost CF CL (spreadSlot b i) (b.t i) (spreadWin b.t b.P i)
            (suffixProd b.t i) + 8) + 4) +
          (4 * (L2 + L1 + totalLen b.t * (2 * b.wI + 1)) + 3 * sumR + 60))) ≤
    Ctot Cs CF CL * spreadCost b i := by
  have hRdef : totalLen b.t = prefixProd b.t i * b.t i * suffixProd b.t i :=
    (prefixProd_mul_mul_suffixProd b.t i).symm
  have hid := i.isLt
  have hSC : spreadCost b i = kB (prefixProd b.t i) (suffixProd b.t i) (b.t i)
      (spreadWin b.t b.P i) (spreadSlot b i) b.wI b.wT (mulW (2 * spreadBlkBits b i + 1)) b.d
      (tapTabLen b) b.setup := by
    unfold spreadCost kB vol1
    simp only [BrPar.R]
    rw [totalLen_div_eq b i ht, hRdef]
  rw [hSC]
  have h := stage_cost_le Cs CF CL (prefixProd b.t i) (suffixProd b.t i) (b.t i)
    (spreadWin b.t b.P i) (spreadA0 b i) (spreadSlot b i) b.wI b.wT
    (mulW (2 * spreadBlkBits b i + 1)) b.d (b.d - 1 - i) L1 L2 (tapTabLen b) b.setup sumR
    (prefixProd_pos_ ht i) (suffixProd_pos_ ht i) (one_le_spreadWin b i ht) (spreadWin_le b i)
    (spreadA0_le b i) (by omega) (by omega) (d_le_setup b) hL (by rw [← hRdef]; exact hsum) rfl
  unfold grpCost
  simp only [BrPar.R]
  rw [hRdef]
  exact h


/-! ## Ruler stacks and `stagePost` inside the stage registers -/

theorem length_rulerStacks {Es : Type} [DecidableEq Es] :
    (rulerStacks (Esu := Es)).length = 22 := by
  simp [rulerStacks]

section Post

variable {Es σ : Type} [DecidableEq Es]

/-- `stagePost_eval` as a `Runs` fact of the lifted program `ar lA stagePost`. -/
theorem runs_stagePost (lA : Lens σ AReg) (S : SK Es → List Sym)
    (hru : ∀ k ∈ rulerStacks, S k = List.replicate (S k).length .mark) :
    Runs (ar lA stagePost) S (stagePostSt S) (fun _ => True)
      (4 * ((S (sp .TR)).length + (S (sp .TT)).length + (S (sp .Out)).length) +
        3 * (rulerStacks.map fun k => (S k).length).sum + 60) :=
  runs_ar lA (Runs.of_eval (Q := fun _ => True) fun v => by
    obtain ⟨v', c, e, hc⟩ := stagePost_eval S v hru
    exact ⟨v', c, e, trivial, hc⟩)

end Post

/-! ## The stage run -/

/-- The outputs of the double loop are the stage values (`stageVals_eq`). -/
theorem stageOuts_eq' (b : BrPar) (i : Fin b.d) (T : BridgeTables b.t) (W : Idx b.t → ℂ)
    (ht : ShapeOK b.t) (hi0 : (i : ℕ) ≠ 0) (hOG : TablesOnGrid b.P b.t T)
    (hTW : TapsWindowed b.P b.t T) (hWg : ∀ k, OnGrid (b.P + 2) (W k)) :
    stageOuts (b.P + 2) (b.t i) (spreadWin b.t b.P i) (spreadA0 b i) (suffixProd b.t i)
        ((expAddrs b.t i).map fun k => gridInt (b.P + 2) (W k)) (tapBlock b.t b.P T i)
        (prefixProd b.t i * suffixProd b.t i) =
      (expAddrs b.t i).map (fun k =>
        gridInt (b.P + 2) (spreadAxisFixedR roundHalfUpR (b.P + 2) b.t i (T.tap i) W k)) :=
  stageVals_eq b i T W ht hi0 hOG hTW hWg

section Run

variable {Es Rs Rm : Type} [DecidableEq Es]

set_option maxHeartbeats 1600000 in
/-- **The stage run**: `stageProg` meets the specification of `SpreadLinesStmt`, with cost
`Ctot Cs CF CL · spreadCost b i`. -/
theorem runs_stageProg {Ps : Prog (KLoc SetupN Es) (fun _ => Sym) Rs} {Cs : ℕ}
    (hPs : SetupSpec Ps Cs) {PF : AProg (SK Es)} {CF : ℕ} (hPF : PFSpec PF CF)
    {PL : Prog (SK Es) (fun _ => Sym) (Sg Rs Rm)} {CL : ℕ} (hPL : SpreadLineSpec PL CL)
    (b : BrPar) (i : Fin b.d) (T : BridgeTables b.t) (W : Idx b.t → ℂ)
    (rarr rax rpar rtap : List Sym) (S : SK Es → List Sym)
    (hS : KClean S) (ht : ShapeOK b.t) (hi0 : (i : ℕ) ≠ 0) (hwI : 1 ≤ b.wI) (hwT : 1 ≤ b.wT)
    (hPw : b.P + 2 ≤ b.wI) (hlog : Nat.log2 (totalLen b.t) ≤ b.wI)
    (hOG : TablesOnGrid b.P b.t T) (hTW : TapsWindowed b.P b.t T)
    (hTF : TablesFit b.wT b.P b.t T) (hWg : ∀ k, OnGrid (b.P + 2) (W k))
    (hWf : ArrFits b.wI (b.P + 2) W)
    (hYf : ArrFits b.wI (b.P + 2) (spreadAxisFixedR roundHalfUpR (b.P + 2) b.t i (T.tap i) W))
    (hrax : TermOK rax)
    (harr : S (kW .arr) = carrSyms b.wI (encT (b.P + 2) (expAddrs b.t i) W) ++ rarr)
    (hax : S (kW .ax) = natSyms i ++ rax) (hpar : S (kN .par) = hdrSyms b.hdr ++ rpar)
    (htap : S (kN .tapTab) = tapTabSyms b.wT b.P b.t T ++ rtap) :
    Runs (stageProg Ps PF PL) S
      (Function.update S (kW .arr) (carrSyms b.wI (encT (b.P + 2) (expAddrs b.t i)
        (spreadAxisFixedR roundHalfUpR (b.P + 2) b.t i (T.tap i) W)) ++ rarr))
      (fun _ => True) (Ctot Cs CF CL * spreadCost b i) := by
  have hcl : ∀ x : SpS, S (sp x) = [] := fun x => hS (.inl x)
  have hlenE : (expAddrs b.t i).length = totalLen b.t := (expAddrsStruct_holds b.t i ht).1
  have hslot := slot_ge b i
  -- the tap blocks before and after the axis block
  obtain ⟨blks, hblks⟩ : ∃ blks : List (List Sym), blks =
      ((spreadOrder b.d).take (b.d - 1 - i)).map fun i' => carrSyms b.wT (tapBlock b.t b.P T i') :=
    ⟨_, rfl⟩
  obtain ⟨post, hpost⟩ : ∃ post : List Sym, post =
      ((spreadOrder b.d).drop (b.d - i)).flatMap fun i' =>
        carrSyms b.wT (tapBlock b.t b.P T i') ++ [Sym.mark] := ⟨_, rfl⟩
  have hsplit : tapTabSyms b.wT b.P b.t T = blks.flatMap (· ++ [Sym.mark]) ++
      (carrSyms b.wT (tapBlock b.t b.P T i) ++ Sym.mark :: post) := by
    rw [hblks, hpost]
    exact tapTabSyms_split b.wT b.P b.t T i hi0
  -- phase 1: the setup kernel installs the rulers
  obtain ⟨S1, hS1, r1⟩ : ∃ S1, S1 = setRu b i S ∧ Runs (callInj ιSU (lensS (Rm := Rm)) Ps) S S1
      (fun _ => True) (Cs * (b.setup + b.R + spreadSlot b i)) :=
    ⟨_, rfl, runs_setupCall _ hPs b i rax rpar S (fun e => hS (.inr e)) (fun r => hcl _)
      ht hi0 hwI hwT hPw hlog hrax hpar hax⟩
  have hS1ru : ∀ r, S1 (sp (.ru r)) = List.replicate (spreadRulers b i r) .mark := by
    intro r; rw [hS1]; exact setRu_ru b i S r
  have hS1o : ∀ k, (∀ r, k ≠ sp (.ru r)) → S1 k = S k := by
    intro k hk; rw [hS1]; exact setRu_of_ne b i S k hk
  have hS1sp : ∀ x : SpS, (∀ r, x ≠ .ru r) → S1 (sp x) = [] := by
    intro x hx
    rw [hS1o (sp x) (fun r h => hx r (sp_injective h))]
    exact hcl x

  -- phase 2: product rulers; the tap blocks before the axis block go onto `TT`
  have htap1 : S1 (kN .tapTab) = blks.flatMap (· ++ [Sym.mark]) ++
      (carrSyms b.wT (tapBlock b.t b.P T i) ++ Sym.mark :: (post ++ rtap)) := by
    rw [hS1o (kN .tapTab) (fun r => by simp), htap, hsplit]
    simp only [List.append_assoc, List.cons_append]
  have hblen : blks.length = b.d - 1 - i := by
    rw [hblks, List.length_map, List.length_take, length_spreadOrder_]; omega
  have hbmk : ∀ bl ∈ blks, ∀ x ∈ bl, x ≠ Sym.mark := by
    intro bl hbl x hx hxm
    rw [hblks] at hbl
    obtain ⟨i', -, rfl⟩ := List.mem_map.1 hbl
    exact mark_not_mem_carrSyms_ _ _ (hxm ▸ hx)
  obtain ⟨S2, hS2, r2⟩ : ∃ S2, S2 = _ ∧
      Runs (ar (lensA (Rs := Rs) (Rm := Rm)) stagePre) S1 S2 (fun _ => True) _ :=
    ⟨_, rfl, runs_stagePre _ (spreadWin b.t b.P i - 1) (2 * b.wI + 1) (b.t i) (spreadA0 b i)
      (b.t i - spreadA0 b i) (spreadSlot b i) (b.d - 1 - i) blks
      (carrSyms b.wT (tapBlock b.t b.P T i) ++ Sym.mark :: (post ++ rtap)) S1
      (hS1ru .Wm1) (hS1ru .recw) (hS1ru .t) (hS1ru .a0) (hS1ru .ta) (hS1ru .s) (hS1ru .skip)
      (fun k => hS1sp (.pr k) (fun r => by simp)) (hS1sp (.X 0) (fun r => by simp))
      (hS1sp (.X 7) (fun r => by simp)) (hS1sp (.X 3) (fun r => by simp))
      (hS1sp .TT (fun r => by simp)) htap1 hblen hbmk⟩
  have hS2o : ∀ k, k ≠ sp .TT → k ≠ kN .tapTab → (∀ j, k ≠ sp (.pr j)) → S2 k = S1 k := by
    intro k h1 h2 h3
    rw [hS2, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne (h3 4),
      Function.update_of_ne (h3 3), Function.update_of_ne (h3 2), Function.update_of_ne (h3 1),
      Function.update_of_ne (h3 0)]
  have hS2ru : ∀ r, S2 (sp (.ru r)) = List.replicate (spreadRulers b i r) .mark := by
    intro r
    rw [hS2o (sp (.ru r)) (by simp) (by simp) (fun j => by simp)]
    exact hS1ru r
  have hS2sp : ∀ x : SpS, (∀ r, x ≠ .ru r) → (∀ j, x ≠ .pr j) → x ≠ .TT → S2 (sp x) = [] := by
    intro x h1 h2 h3
    rw [hS2o (sp x) (fun h => h3 (sp_injective h)) (by simp) (fun j h => h2 j (sp_injective h))]
    exact hS1sp x h1
  have hS2arr : S2 (kW .arr) = carrSyms b.wI
      (((expAddrs b.t i).map fun k => gridInt (b.P + 2) (W k)).map fun x => [x]) ++ rarr := by
    rw [hS2o (kW .arr) (by simp) (by simp) (fun j => by simp), hS1o (kW .arr) (fun r => by simp),
      harr, encT_eq]
  have hS2tap : S2 (kN .tapTab) =
      carrSyms b.wT (tapBlock b.t b.P T i) ++ Sym.mark :: (post ++ rtap) := by
    rw [hS2, Function.update_of_ne (show (kN .tapTab : SK Es) ≠ sp .TT by simp),
      Function.update_self]
  have hp0 : S2 (sp (.pr 0)) =
      List.replicate ((spreadWin b.t b.P i - 1) * (2 * b.wI + 1)) .mark := by
    rw [hS2]; simp
  have hp1 : S2 (sp (.pr 1)) = List.replicate (b.t i * (2 * b.wI + 1)) .mark := by
    rw [hS2]; simp
  have hp2 : S2 (sp (.pr 2)) = List.replicate (spreadA0 b i * (2 * b.wI + 1)) .mark := by
    rw [hS2]; simp
  have hp3 : S2 (sp (.pr 3)) =
      List.replicate ((b.t i - spreadA0 b i) * (2 * b.wI + 1)) .mark := by
    rw [hS2]; simp
  have hp4 : S2 (sp (.pr 4)) =
      List.replicate ((spreadWin b.t b.P i - 1) * spreadSlot b i) .mark := by
    rw [hS2]; simp
  have hLS : ∀ x, LineScratch x → S2 (sp x) = [] := by
    intro x hx
    apply hS2sp x
    all_goals
      rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp

  -- phase 3: the stage double loop
  have hFi : ∀ F ∈ tapBlock b.t b.P T i, ∀ y ∈ F, FitsTwos b.wT y.1 ∧ FitsTwos b.wT y.2 :=
    hTF.1 i (by rw [spreadOrder_split i hi0]; simp)
  have hWlt : spreadWin b.t b.P i < 2 ^ Nat.size (b.t i) :=
    lt_of_le_of_lt (spreadWin_le b i) (Nat.lt_size_self _)
  obtain ⟨S3, hS3, r3⟩ : ∃ S3, S3 = _ ∧
      Runs (groupLoop (lensA (Rs := Rs) (Rm := Rm)) PF PL) S2 S3 (fun _ => True) _ :=
    ⟨_, rfl, runs_groupLoop _ hPF hPL (spreadSlot b i) b.wI b.wT (b.P + 2) (b.t i)
      (spreadWin b.t b.P i) (spreadA0 b i) (prefixProd b.t i) (suffixProd b.t i)
      ((expAddrs b.t i).map fun k => gridInt (b.P + 2) (W k)) (tapBlock b.t b.P T i) rarr
      (post ++ rtap) S2
      (by rw [List.length_map, hlenE, ← prefixProd_mul_mul_suffixProd b.t i]; ring)
      (length_tapBlock_eq b.t b.P T i ht) (fun F hF => length_of_mem_tapBlock hF)
      (one_le_spreadWin b i ht) (spreadWin_le b i) (spreadA0_le b i) hwI (by omega) (by omega)
      hwT (by omega)
      (fun x hx => by obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx; exact hWf k)
      hFi (slot_bound hWlt (by unfold spreadSlot; omega))
      (slot_bound_nat hWlt (by unfold spreadSlot; omega))
      (fun y hy => by
        rw [stageOuts_eq' b i T W ht hi0 hOG hTW hWg] at hy
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hy
        exact hYf k)
      hS2arr (hS2sp .Out (fun r => by simp) (fun j => by simp) (by simp)) hS2tap
      (hS2sp .TR (fun r => by simp) (fun j => by simp) (by simp))
      (fun k => hS2sp (.F k) (fun r => by simp) (fun j => by simp) (by simp))
      (hS2sp (.X 3) (fun r => by simp) (fun j => by simp) (by simp))
      (hS2sp (.X 4) (fun r => by simp) (fun j => by simp) (by simp))
      (hS2ru .A) (hS2ru .rep) (hS2ru .s) (hS2ru .sq) (hS2ru .h) (hS2ru .wI) (hS2ru .Wm1)
      (hS2ru .W) (hS2ru .wI1) (hS2ru .sWI) (hS2ru .wT1) (hS2ru .sWT) hp0 hp1 hp2 hp3 hp4 hLS⟩
  -- phase 4: restore the tap table, move the outputs onto `arr`, clear the rulers
  have hS3o : ∀ k, k ≠ sp .TR → k ≠ kN .tapTab → k ≠ sp .Out → k ≠ kW .arr → S3 k = S2 k := by
    intro k h1 h2 h3 h4
    rw [hS3, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4]
  have hS2pr : ∀ j : Fin 5, ∃ n, S2 (sp (.pr j)) = List.replicate n .mark := by
    intro j
    fin_cases j
    exacts [⟨_, hp0⟩, ⟨_, hp1⟩, ⟨_, hp2⟩, ⟨_, hp3⟩, ⟨_, hp4⟩]
  have hru3 : ∀ k ∈ rulerStacks, S3 k = List.replicate (S3 k).length .mark := by
    intro k hk
    rcases List.mem_append.1 hk with h | h <;> obtain ⟨r, -, rfl⟩ := List.mem_map.1 h
    · rw [hS3o (sp (.ru r)) (by simp) (by simp) (by simp) (by simp), hS2ru r,
        List.length_replicate]
    · obtain ⟨n, hn⟩ := hS2pr r
      rw [hS3o (sp (.pr r)) (by simp) (by simp) (by simp) (by simp), hn, List.length_replicate]
  obtain ⟨S4, hS4, r4⟩ : ∃ S4, S4 = stagePostSt S3 ∧
      Runs (ar (lensA (Rs := Rs) (Rm := Rm)) stagePost) S3 S4 (fun _ => True) _ :=
    ⟨_, rfl, runs_stagePost _ S3 hru3⟩
  have hall := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3 r4))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_

  · -- the final state
    funext k
    rw [hS4]
    simp only [stagePostSt]
    by_cases hk : k ∈ rulerStacks (Esu := Es)
    · rw [if_pos hk]
      have hka : k ≠ kW .arr := by
        rintro rfl
        rcases List.mem_append.1 hk with h | h <;> obtain ⟨r, -, hr⟩ := List.mem_map.1 h <;>
          simp at hr
      rw [Function.update_of_ne hka]
      rcases List.mem_append.1 hk with h | h <;> obtain ⟨r, -, rfl⟩ := List.mem_map.1 h <;>
        exact (hcl _).symm
    rw [if_neg hk]
    by_cases k1 : k = kN .tapTab
    · subst k1
      rw [if_pos rfl, Function.update_of_ne (show (kN .tapTab : SK Es) ≠ kW .arr by simp), htap,
        hsplit]
      have e1 : S3 (sp .TT) = (blks.flatMap (· ++ [Sym.mark])).reverse := by
        rw [hS3o (sp .TT) (by simp) (by simp) (by simp) (by simp), hS2, Function.update_self]
      have e2 : S3 (sp .TR) = (carrSyms b.wT (tapBlock b.t b.P T i)).reverse := by
        rw [hS3, Function.update_self]
      have e3 : S3 (kN .tapTab) = Sym.mark :: (post ++ rtap) := by
        rw [hS3, Function.update_of_ne (show (kN .tapTab : SK Es) ≠ sp .TR by simp),
          Function.update_self]
      rw [e1, e2, e3]
      simp only [List.reverse_reverse, List.append_assoc, List.cons_append]
    by_cases k2 : k = kW .arr
    · subst k2
      rw [if_neg (show (kW .arr : SK Es) ≠ kN .tapTab by simp), if_pos rfl, Function.update_self,
        hS3, stageOuts_eq' b i T W ht hi0 hOG hTW hWg, encT_eq]
      simp
    by_cases k3 : k = sp .TR ∨ k = sp .TT ∨ k = sp .Out
    · rw [if_neg k1, if_neg k2, if_pos k3, Function.update_of_ne k2]
      rcases k3 with rfl | rfl | rfl <;> exact (hcl _).symm
    rw [if_neg k1, if_neg k2, if_neg k3, Function.update_of_ne k2]
    have k3a : k ≠ sp .TR := fun h => k3 (Or.inl h)
    have k3b : k ≠ sp .TT := fun h => k3 (Or.inr (Or.inl h))
    have k3c : k ≠ sp .Out := fun h => k3 (Or.inr (Or.inr h))
    have hkru : ∀ r, k ≠ sp (.ru r) := fun r h => hk (by rw [h]; exact mem_rulerStacks_ru r)
    have hkpr : ∀ j, k ≠ sp (.pr j) := fun j h => hk (by rw [h]; exact mem_rulerStacks_pr j)
    rw [hS3o k k3a k1 k3c k2, hS2o k k3b k1 hkpr, hS1o k hkru]
  · -- the cost
    have eTR : (S3 (sp .TR)).length = (carrSyms b.wT (tapBlock b.t b.P T i)).length := by
      rw [hS3, Function.update_self, List.length_reverse]
    have eTT : (S3 (sp .TT)).length = (blks.flatMap (· ++ [Sym.mark])).length := by
      rw [hS3o (sp .TT) (by simp) (by simp) (by simp) (by simp), hS2, Function.update_self,
        List.length_reverse]
    have eOut : (S3 (sp .Out)).length = totalLen b.t * (2 * b.wI + 1) := by
      rw [hS3, Function.update_of_ne (show (sp .Out : SK Es) ≠ sp .TR by simp),
        Function.update_of_ne (show (sp .Out : SK Es) ≠ kN .tapTab by simp), Function.update_self,
        List.length_reverse, length_carrSyms_singles, stageOuts_eq' b i T W ht hi0 hOG hTW hWg,
        List.length_map, hlenE]
    have hLL : (blks.flatMap (· ++ [Sym.mark])).length +
        (carrSyms b.wT (tapBlock b.t b.P T i)).length ≤ tapTabLen b := by
      have h := congrArg List.length hsplit
      rw [length_tapTabSyms b T ht] at h
      simp only [List.length_append, List.length_cons] at h
      omega
    have hW1 := spreadWin_le b i
    have hsum : (rulerStacks.map fun k => (S3 k).length).sum ≤
        22 * (totalLen b.t * (2 * b.wI + 1) + totalLen b.t * spreadSlot b i + b.setup) := by
      have h := List.sum_le_card_nsmul (rulerStacks.map fun k => (S3 k).length)
        (totalLen b.t * (2 * b.wI + 1) + totalLen b.t * spreadSlot b i + b.setup) (by
          intro n hn
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hn
          rcases List.mem_append.1 hk with h | h <;> obtain ⟨r, -, rfl⟩ := List.mem_map.1 h
          · rw [hS3o (sp (.ru r)) (by simp) (by simp) (by simp) (by simp), hS2ru r,
              List.length_replicate]
            exact spreadRulers_le b i ht hPw r
          · rw [hS3o (sp (.pr r)) (by simp) (by simp) (by simp) (by simp)]
            fin_cases r
            · exact (congrArg List.length hp0).trans_le
                (by rw [List.length_replicate]; exact prod_le b i ht _ (by omega))
            · exact (congrArg List.length hp1).trans_le
                (by rw [List.length_replicate]; exact prod_le b i ht _ le_rfl)
            · exact (congrArg List.length hp2).trans_le
                (by rw [List.length_replicate]; exact prod_le b i ht _ (spreadA0_le b i))
            · exact (congrArg List.length hp3).trans_le
                (by rw [List.length_replicate]; exact prod_le b i ht _ (Nat.sub_le _ _))
            · exact (congrArg List.length hp4).trans_le
                (by rw [List.length_replicate]; exact prod_s_le b i ht _ (by omega)))
      rw [List.length_map, length_rulerStacks, smul_eq_mul] at h
      exact h
    rw [eTR, eTT, eOut]
    exact stage_cost_b Cs CF CL b i ht hi0 _ _ _ hLL hsum

end Run

end SubNLogN.Machine.Bridge.SpreadAux.StageMain


namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine Computability SubNLogN.Machine.Bridge.SpreadAux.Stage
  SubNLogN.Machine.Bridge.SpreadAux.StageMain

/-- **Spreading along an exposed axis** (`SpreadLinesStmt`) from the setup kernel
(`SpreadSetupStmt`) and the line step (`SpreadLineStmt`). The filter packer, the data packer and
the slot pass enter through their proved statements (`packFilter_holds`, `packData_holds`,
`slotPass_holds`). -/
theorem spreadLines_of (hS : SpreadSetupStmt) (hL : SpreadLineStmt) : SpreadLinesStmt := by
  intro hMul
  obtain ⟨Cm, Rm, Pm, hRmf, hRmn, hPmc, hPms⟩ := hMul
  obtain ⟨Cs, hS1⟩ := hS
  obtain ⟨Es, hEsF, hEsD, Rs, Ps, hRsf, hRsn, hPsc, hPss⟩ := hS1 ()
  obtain ⟨progF, CF, hcF, hsF⟩ := packFilter_holds
  obtain ⟨PL, hPLc, CL, hPL⟩ := hL packData_holds slotPass_holds (Esu := Es)
    (lensA (Rs := Rs) (Rm := Rm)) (lensM (Rs := Rs) (Rm := Rm)) Pm Cm hPmc hPms
  refine ⟨Ctot Cs CF CL, fun _ => ⟨SpS ⊕ Es, inferInstance, inferInstance, Sg Rs Rm,
    stageProg Ps (progF (SK Es) ιPF) PL, inferInstance, inferInstance,
    closed_stageProg hPsc (hcF _ _) hPLc, ?_⟩⟩
  intro b i T W rarr rax rpar rtap S hKS ht hi0 hwI hwT hPw hlog hOG hTW hTF hWg hWf hYf _hrarr
    hrax harr hax hpar htap
  exact runs_stageProg hPss (hsF (SK Es) ιPF ιPF_injective) hPL b i T W rarr rax rpar rtap S
    hKS ht hi0 hwI hwT hPw hlog hOG hTW hTF hWg hWf hYf hrax harr hax hpar htap

/-- `SpreadLinesStmt` from the line step alone (the setup kernel is `spreadSetup_holds`). -/
theorem spreadLines_of_line (hL : SpreadLineStmt) : SpreadLinesStmt :=
  spreadLines_of spreadSetup_holds hL

/-- **`SpreadLinesStmt`, unconditionally** (the line step is `Line.spreadLine_holds`). -/
theorem spreadLines_holds : SpreadLinesStmt :=
  spreadLines_of_line Line.spreadLine_holds

end SubNLogN.Machine.Bridge.SpreadAux
