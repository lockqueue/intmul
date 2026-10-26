/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadLineAR
import SubNLogN.Machine.Bridge.SpreadLineStmt
import SubNLogN.Machine.Calculus.Loops

/-!
# K5 spreading: the line step (`Bridge/SpreadLine.lean`)

`lineProg`: build the extended line `E = X ++ X.take (W - 1)` and the zero tails (`linePre`), run
the block step (`blockProg`) on the `⌈|E| / W⌉` chunks of `E` (overlap-add; the loop flag is the
next record of `Es`), then rotate the finalized outputs onto `Out` (`linePost`).

* `loop_step`: one block as a `Runs` fact between the loop states `loopF … j` and `loopF … (j+1)`
  (from `block_runs`);
* `spreadLine_holds : SpreadLineStmt`.

**Scope (honest summary).** Proves `SpreadLineStmt` (`SpreadLineStmt.lean`); the packer, the slot
pass and `mulBig` enter through their specifications (premises of the statement).
-/

namespace SubNLogN.Machine.Bridge.SpreadAux.Line

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith SubNLogN.Machine.Calculus
  Computability SubNLogN.Machine.Bridge.SpreadAux

/-! ## Pure lemmas -/

/-- The rounded outputs of the first `n` convolution indices. -/
def outs (q : ℕ) (E G : List CInt) (n : ℕ) : List CInt :=
  (List.range n).map fun k => roundHalfUpShiftC q (ccF E G k)

theorem outs_add (q : ℕ) (E G : List CInt) (a b : ℕ) :
    outs q E G (a + b) =
      outs q E G a ++ (List.range b).map fun i => roundHalfUpShiftC q (ccF E G (a + i)) := by
  simp only [outs, List.range_add, List.map_append, List.map_map, Function.comp_def]

theorem outs_lineConv (q t W : ℕ) (X F : List CInt) :
    outs q (X ++ X.take (W - 1)) F.reverse (t + W - 1) =
      (lineConv t W X F).map (roundHalfUpShiftC q) := by
  simp only [outs, lineConv, List.map_map, Function.comp_def]

theorem lt_nblk_iff {L W k : ℕ} (hW : 1 ≤ W) : k < (L + W - 1) / W ↔ k * W < L := by
  rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le (by omega), Nat.succ_mul]
  omega

theorem nblk_le {t W : ℕ} (hW : 1 ≤ W) : (t + W - 1 + W - 1) / W ≤ t / W + 2 :=
  calc (t + W - 1 + W - 1) / W ≤ (t + 2 * W) / W := Nat.div_le_div_right (by omega)
    _ = t / W + 2 := Nat.add_mul_div_right t 2 (by omega)

theorem termOK_nil : TermOK [] := fun _ h => by simp at h

theorem cpartT_lt {s wI wT W : ℕ} (hW1 : 1 ≤ W)
    (hdig : W * (2 ^ (wI - 1) * 2 ^ (wT - 1)) < 2 ^ s) (k : Fin 4) (y : CInt) :
    cpart wT k y < 2 ^ s := by
  have h2 : 1 ≤ 2 ^ (wI - 1) := Nat.one_le_two_pow
  have h1 : 2 ^ (wT - 1) ≤ W * (2 ^ (wI - 1) * 2 ^ (wT - 1)) :=
    calc 2 ^ (wT - 1) = 1 * (1 * 2 ^ (wT - 1)) := by ring
      _ ≤ W * (2 ^ (wI - 1) * 2 ^ (wT - 1)) := Nat.mul_le_mul hW1 (Nat.mul_le_mul_right _ h2)
  exact lt_of_le_of_lt (cpart_le wT k y) (lt_of_le_of_lt h1 hdig)

theorem mulBigBound_le {x y n : ℕ} (h : mulBigSize x y ≤ n) : mulBigBound x y ≤ mulW n := by
  unfold mulBigBound mulW
  have hl : Nat.log2 (mulBigSize x y) + 1 ≤ Nat.log2 n + 1 := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.add_le_add_right (Nat.log_mono_right h) 1
  have := Nat.mul_le_mul h hl
  omega

theorem one_le_mulW (n : ℕ) : 1 ≤ mulW n := by
  unfold mulW
  omega

/-- The block-loop fields after `j` blocks of the extended line `E` (empty prefix of outputs
`Q0 = []`). -/
def loopF (s wI q W : ℕ) (E G : List CInt) (j : ℕ) : BF :=
  fRest (csym wI (E.drop (j * W)))
    ((tailBits s Prod.fst (pend (E.take (j * W)) G)).map Sym.bit)
    ((tailBits s Prod.snd (pend (E.take (j * W)) G)).map Sym.bit)
    (csym wI (outs q E G (min (j * W) E.length))).reverse

theorem loopQ_step (wI q W : ℕ) (E G : List CInt) (j : ℕ) (hj : j * W < E.length) :
    (carrSyms wI ((List.range (chunk E W j).length).map fun i =>
        [roundHalfUpShiftC q (vB (E.take (j * W)) (chunk E W j) G i)])).reverse ++
      (csym wI (outs q E G (min (j * W) E.length))).reverse =
    (csym wI (outs q E G (min ((j + 1) * W) E.length))).reverse := by
  have hm : (chunk E W j).length = min W (E.length - j * W) := length_chunk E W j
  have e1 : min ((j + 1) * W) E.length = j * W + (chunk E W j).length := by
    rw [hm, Nat.succ_mul]
    omega
  have e2 : min (j * W) E.length = j * W := by omega
  have hin : (List.range (chunk E W j).length).map (fun i =>
      [roundHalfUpShiftC q (vB (E.take (j * W)) (chunk E W j) G i)]) =
      ((List.range (chunk E W j).length).map fun i =>
        roundHalfUpShiftC q (ccF E G (j * W + i))).map fun x => [x] := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [vB_chunk E G W j i hj.le hi]
  rw [e1, e2, outs_add, csym_append, List.reverse_append, hin]
  rfl

/-- The total cost of one block, in the form of the line cost unit. -/
theorem blkCost_le {s q wI W Cpd Csp Cm M : ℕ} (hq : q ≤ s) (hwI : wI ≤ s) (_hW : 1 ≤ W)
    (hM : 1 ≤ M) :
    blkCost s q wI W W Cpd Csp Cm M + 1 ≤
      (Cpd + 4 * Csp + 16 * Cm + 200) * (W * (s + 1) + M) := by
  have hfin : finCost s q wI + 3 ≤ 93 * (s + 1) := by
    unfold finCost fieldCost
    omega
  have hW1 : W - 1 ≤ W := Nat.sub_le W 1
  unfold blkCost blkCostA
  have hY1 : W ≤ W * (s + 1) := Nat.le_mul_of_pos_right W (by omega)
  have hsW : s * W ≤ W * (s + 1) :=
    calc s * W ≤ (s + 1) * W := Nat.mul_le_mul_right _ (Nat.le_succ s)
      _ = W * (s + 1) := Nat.mul_comm _ _
  have e1 : W * (2 * (Csp * (s + 1)) + finCost s q wI + 2 + 1) =
      2 * (Csp * (W * (s + 1))) + W * (finCost s q wI + 3) := by ring
  have e2 : W * (finCost s q wI + 3) ≤ 93 * (W * (s + 1)) :=
    calc W * (finCost s q wI + 3) ≤ W * (93 * (s + 1)) := Nat.mul_le_mul_left _ hfin
      _ = 93 * (W * (s + 1)) := by ring
  have e3 : (W - 1) * (2 * (Csp * (s + 1)) + 2 + 1) ≤ 2 * (Csp * (W * (s + 1))) + 3 * W :=
    calc (W - 1) * (2 * (Csp * (s + 1)) + 2 + 1) ≤ W * (2 * (Csp * (s + 1)) + 2 + 1) :=
          Nat.mul_le_mul_right _ hW1
      _ = 2 * (Csp * (W * (s + 1))) + 3 * W := by ring
  have e4 : s * (W - 1) ≤ W * (s + 1) := le_trans (Nat.mul_le_mul_left _ hW1) hsW
  have e5 : Cpd * (W * (s + 1) + 1) ≤ Cpd * (W * (s + 1)) + Cpd * M := by
    rw [Nat.mul_add]
    exact Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left Cpd hM) _
  have e6 : (Cpd + 4 * Csp + 16 * Cm + 200) * (W * (s + 1) + M) =
      Cpd * (W * (s + 1)) + Cpd * M + 4 * (Csp * (W * (s + 1))) + 4 * (Csp * M) +
        16 * (Cm * (W * (s + 1))) + 16 * (Cm * M) + 200 * (W * (s + 1)) + 200 * M := by ring
  rw [e1, e6]
  omega

theorem blkCost_mono {s q wI m W Cpd Csp Cm M : ℕ} (h : m ≤ W) :
    blkCost s q wI m W Cpd Csp Cm M ≤ blkCost s q wI W W Cpd Csp Cm M := by
  unfold blkCost blkCostA
  gcongr

theorem linePreCost_le {t W wI s : ℕ} (hwI : wI ≤ s) (hW : 1 ≤ W) :
    linePreCost t W wI s ≤ 150 * ((t + W) * (s + 1)) := by
  have hA : 1 ≤ (t + W) * (s + 1) :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h1 : (W - 1) * (2 * wI + 1) ≤ 2 * ((t + W) * (s + 1)) :=
    calc (W - 1) * (2 * wI + 1) ≤ (t + W) * (2 * (s + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * ((t + W) * (s + 1)) := by ring
  have h2 : t * (2 * wI + 1) ≤ 2 * ((t + W) * (s + 1)) :=
    calc t * (2 * wI + 1) ≤ (t + W) * (2 * (s + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * ((t + W) * (s + 1)) := by ring
  have h3 : (W - 1) * s ≤ (t + W) * (s + 1) := Nat.mul_le_mul (by omega) (by omega)
  unfold linePreCost
  omega

theorem linePostCost_le {t W wI s a0 : ℕ} (hwI : wI ≤ s) (hW : 1 ≤ W) (ha0 : a0 ≤ t) :
    linePostCost t W wI a0 (s * (W - 1)) (s * (W - 1)) ≤ 149 * ((t + W) * (s + 1)) := by
  have hA : 1 ≤ (t + W) * (s + 1) :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h1 : (W - 1) * (2 * wI + 1) ≤ 2 * ((t + W) * (s + 1)) :=
    calc (W - 1) * (2 * wI + 1) ≤ (t + W) * (2 * (s + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * ((t + W) * (s + 1)) := by ring
  have h2 : a0 * (2 * wI + 1) ≤ 2 * ((t + W) * (s + 1)) :=
    calc a0 * (2 * wI + 1) ≤ (t + W) * (2 * (s + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * ((t + W) * (s + 1)) := by ring
  have h3 : (t - a0) * (2 * wI + 1) ≤ 2 * ((t + W) * (s + 1)) :=
    calc (t - a0) * (2 * wI + 1) ≤ (t + W) * (2 * (s + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * ((t + W) * (s + 1)) := by ring
  have h4 : s * (W - 1) ≤ (t + W) * (s + 1) :=
    calc s * (W - 1) ≤ (s + 1) * (t + W) := Nat.mul_le_mul (by omega) (by omega)
      _ = (t + W) * (s + 1) := Nat.mul_comm _ _
  unfold linePostCost
  omega

theorem cost_combine {pre post N b A Bk Y K : ℕ} (hpre : pre ≤ 150 * A) (hpost : post ≤ 149 * A)
    (hA : 1 ≤ A) (hN : N ≤ Bk) (hb : b + 1 ≤ K * Y) :
    pre + (N * (b + 1) + 1) + post ≤ (K + 300) * (A + Bk * Y) := by
  have h1 : N * (b + 1) ≤ Bk * (K * Y) := Nat.mul_le_mul hN hb
  have e1 : Bk * (K * Y) = K * (Bk * Y) := by ring
  have e2 : (K + 300) * (A + Bk * Y) = K * A + 300 * A + K * (Bk * Y) + 300 * (Bk * Y) := by ring
  rw [e2]
  rw [e1] at h1
  omega

section Line

variable {Esu σ Rm : Type} [DecidableEq Esu]

omit [DecidableEq Esu] in
theorem bst_fRest_nil {S : SK Esu → List Sym} (h : ∀ x, LineScratch x → S (sp x) = []) :
    bst S (fRest [] [] [] []) = S := by
  funext k
  rcases k with k | (x | e)
  · rfl
  · cases x <;> first
      | rfl
      | exact (h _ (by simp [LineScratch])).symm
  · rfl

/-- **One block of the loop** (from `block_runs`). -/
theorem loop_step {pdp : ∀ (K : Type) [DecidableEq K], (PackRole → K) → AProg K} {Cpd : ℕ}
    (hpd : PackSpecOf pdp Cpd)
    (hpdc : ∀ (K : Type) [DecidableEq K] (ι : PackRole → K), (pdp K ι).Closed)
    {prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K} {Csp : ℕ}
    (hsp : SlotSpecOf prog Csp)
    (hspc : ∀ (K : Type) [DecidableEq K] (ι : SlotRole → K), (prog K ι).Closed)
    {Pm : Prog MBLoc (fun _ => Sym) Rm} {Cm : ℕ} (hcl : Pm.Closed) (hspec : SpecMulBig Pm Cm)
    (lA : Lens σ AReg) (lM : Lens σ Rm)
    {s wI wT q W : ℕ} {E G : List CInt} {S0 : SK Esu → List Sym} (j : ℕ)
    (hj : j * W < E.length) (hGW : G.length = W) (hW1 : 1 ≤ W) (hq : q ≤ s) (hwI1 : 1 ≤ wI)
    (hwIs : wI ≤ s) (hE : ∀ x ∈ E, FitsTwos wI x.1 ∧ FitsTwos wI x.2)
    (hG : ∀ y ∈ G, FitsTwos wT y.1 ∧ FitsTwos wT y.2)
    (hslot : (W : ℤ) * (2 * (2 ^ (wI - 1) * 2 ^ (wT - 1))) < 2 ^ (s - 1))
    (hdig : W * (2 ^ (wI - 1) * 2 ^ (wT - 1)) < 2 ^ s)
    (hb : BaseHyp S0 s q wI W)
    (hRW : S0 (sp (.ru .W)) = List.replicate W .mark)
    (hRlo : S0 (sp (.ru .wI1)) = List.replicate (wI - 1) .mark)
    (hRpad : S0 (sp (.ru .sWI)) = List.replicate (s - wI) .mark)
    (htmp : ∀ j, S0 (sp (.tmp j)) = [])
    (hF : ∀ b, S0 (sp (.F b)) = natSyms (pack s (G.map (cpart wT b))))
    (hmb : ∀ g, S0 (sp (.mb g)) = []) :
    Runs (blockProg pdp prog lA lM Pm) (bst S0 (loopF s wI q W E G j))
      (bst S0 (loopF s wI q W E G (j + 1)))
      (fun x => isBitO (lA.get x).q = decide ((j + 1) * W < E.length))
      (blkCost s q wI W W Cpd Csp Cm (mulW (2 * (W * s + 1) + 1))) := by
  have hm := length_chunk E W j
  have hm1 : 1 ≤ (chunk E W j).length := by rw [hm]; omega
  have hmW : (chunk E W j).length ≤ W := by rw [hm]; omega
  have hBlk : BlkHyp s wI wT q (chunk E W j).length W (E.take (j * W)) (chunk E W j) G :=
    { hGW := hGW, hBm := rfl, hm1 := hm1, hW1 := hW1, hq := hq, hs1 := by omega,
      hE := fun x hx => by
        rw [take_append_chunk] at hx
        exact hE x (List.mem_of_mem_take hx)
      hG := hG
      hslot := by rw [hGW]; exact hslot
      hdig := by rw [hGW]; exact hdig }
  have hes : csym wI (E.drop (j * W)) =
      carrSyms wI ((chunk E W j).map fun x => [x]) ++ csym wI (E.drop ((j + 1) * W)) := by
    show csym wI (E.drop (j * W)) = csym wI (chunk E W j) ++ csym wI (E.drop ((j + 1) * W))
    rw [← csym_append, drop_succ_chunk, chunk, List.take_append_drop]
  have hrest : (chunk E W j).length < W → TermOK (csym wI (E.drop ((j + 1) * W))) := by
    intro hlt
    have hle : E.length ≤ (j + 1) * W := by
      rw [hm] at hlt
      rw [Nat.succ_mul]
      omega
    rw [List.drop_eq_nil_of_le hle]
    exact termOK_nil
  have hMB : ∀ a b, mulBigBound (pack s ((chunk E W j).map (cpart wI a)))
      (pack s (G.map (cpart wT b))) ≤ mulW (2 * (W * s + 1) + 1) := by
    intro a b
    have h1 : bitLen (pack s ((chunk E W j).map (cpart wI a))) ≤ s * W :=
      le_trans (length_encodeNat_pack hBlk a) (Nat.mul_le_mul_left _ hmW)
    have h2 : bitLen (pack s (G.map (cpart wT b))) ≤ s * W := by
      apply length_encodeNat_le
      have := pack_lt s (G.map (cpart wT b)) (fun d hd => by
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hd
        exact cpartT_lt hW1 hdig b y)
      rwa [List.length_map, hGW] at this
    apply mulBigBound_le
    unfold mulBigSize
    have : s * W = W * s := Nat.mul_comm s W
    omega
  have hrun := block_runs hpd hpdc hsp hspc hcl hspec lA lM (csym wI (E.drop ((j + 1) * W)))
    ((csym wI (outs q E G (min (j * W) E.length))).reverse) hBlk hb hwI1 hwIs hmW hrest hRW hRlo
    hRpad htmp hF hmb (mulW (2 * (W * s + 1) + 1)) hMB
  have hpre : loopF s wI q W E G j = fRest (carrSyms wI ((chunk E W j).map fun x => [x]) ++
      csym wI (E.drop ((j + 1) * W)))
      ((tailBits s Prod.fst (pend (E.take (j * W)) G)).map Sym.bit)
      ((tailBits s Prod.snd (pend (E.take (j * W)) G)).map Sym.bit)
      ((csym wI (outs q E G (min (j * W) E.length))).reverse) := by
    rw [loopF, hes]
  have hpost : fOut s wI q (chunk E W j).length (E.take (j * W)) (chunk E W j) G
      ((csym wI (outs q E G (min (j * W) E.length))).reverse) (csym wI (E.drop ((j + 1) * W))) =
      loopF s wI q W E G (j + 1) := by
    rw [loopF, ← take_append_chunk, ← loopQ_step wI q W E G j hj]
    rfl
  rw [hpost] at hrun
  rw [hpre]
  refine WP.W9comp.runs_mono hrun (fun x hx => ?_) (blkCost_mono hmW)
  rw [hx]
  by_cases hlt : (j + 1) * W < E.length
  · rw [decide_eq_true hlt]
    obtain ⟨y, rest, hyr⟩ : ∃ y rest, E.drop ((j + 1) * W) = y :: rest := by
      cases h : E.drop ((j + 1) * W) with
      | nil =>
        rw [List.drop_eq_nil_iff] at h
        omega
      | cons y rest => exact ⟨y, rest, rfl⟩
    obtain ⟨b, hb'⟩ := head_carrSyms_cons wI hwI1 y rest
    rw [hyr]
    show isBitO (carrSyms wI ((y :: rest).map fun y => [y])).head? = true
    rw [hb']
    rfl
  · have hle : E.length ≤ (j + 1) * W := by omega
    rw [decide_eq_false hlt, List.drop_eq_nil_of_le hle]
    rfl

/-- **The line program.** -/
def lineProg (pdp : ∀ (K : Type) [DecidableEq K], (PackRole → K) → AProg K)
    (prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K) (lA : Lens σ AReg)
    (lM : Lens σ Rm) (Pm : Prog MBLoc (fun _ => Sym) Rm) : Prog (SK Esu) (fun _ => Sym) σ :=
  .seq (.seq ((linePre (Esu := Esu)).liftRegs lA)
    (.loop (fun x => isBitO (lA.get x).q) (blockProg pdp prog lA lM Pm)))
    ((linePost (Esu := Esu)).liftRegs lA)

theorem closed_lineProg {pdp : ∀ (K : Type) [DecidableEq K], (PackRole → K) → AProg K}
    (hpdc : ∀ (K : Type) [DecidableEq K] (ι : PackRole → K), (pdp K ι).Closed)
    {prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K}
    (hspc : ∀ (K : Type) [DecidableEq K] (ι : SlotRole → K), (prog K ι).Closed)
    (lA : Lens σ AReg) (lM : Lens σ Rm) {Pm : Prog MBLoc (fun _ => Sym) Rm} (hcl : Pm.Closed) :
    (lineProg (Esu := Esu) pdp prog lA lM Pm).Closed :=
  ⟨⟨WP.W9comp.closed_liftRegs lA closed_linePre, closed_blockProg hpdc hspc lA lM hcl⟩,
    WP.W9comp.closed_liftRegs lA closed_linePost⟩

end Line

/-- **The line step holds** (`SpreadLineStmt`, constant `Cpd + 4 Csp + 16 Cm + 500`). -/
theorem spreadLine_holds : SpreadLineStmt := by
  intro hPD hSP Esu σ Rm _ lA lM Pm Cm hcl hspec
  obtain ⟨pdp, Cpd, hpdc, hpd⟩ := hPD
  obtain ⟨prog, Csp, hspc, hsp⟩ := hSP
  refine ⟨lineProg pdp prog lA lM Pm, closed_lineProg hpdc hspc lA lM hcl,
    Cpd + 4 * Csp + 16 * Cm + 200 + 300, ?_⟩
  intro s wI wT q t W a0 X F rarr S hX hF hW1 hWt ha0 hwI1 hwIs hqs hXf hFf hslot hdig _hout
    harr hFk hRs hRsq hRh hRwI hRWm1 hRW hRwI1 hRsWI hp0 hp1 hp2 hp3 hp4 hscr
  have sc : ∀ x, LineScratch x → S (sp x) = [] := hscr
  have hT2 : S (sp .T2) = [] := sc _ (by simp [LineScratch])
  have hT4 : S (sp .T4) = [] := sc _ (by simp [LineScratch])
  have hT5 : S (sp .T5) = [] := sc _ (by simp [LineScratch])
  have hX2 : S (sp (.X 2)) = [] := sc _ (by simp [LineScratch])
  have hP1 : S (sp .P1) = [] := sc _ (by simp [LineScratch])
  have hP2 : S (sp .P2) = [] := sc _ (by simp [LineScratch])
  have hS'sp : ∀ x, Function.update S (kW .arr) rarr (sp x) = S (sp x) := fun x =>
    Function.update_of_ne (by simp) _ _
  have hb' : BaseHyp (Function.update S (kW .arr) rarr) s q wI W :=
    ⟨by rw [hS'sp]; exact hRs, by rw [hS'sp]; exact sc _ (by simp [LineScratch]),
      by rw [hS'sp]; exact sc _ (by simp [LineScratch]),
      by rw [hS'sp]; exact sc _ (by simp [LineScratch]),
      by rw [hS'sp]; exact sc _ (by simp [LineScratch]),
      by rw [hS'sp]; exact sc _ (by simp [LineScratch]),
      by rw [hS'sp]; exact hRsq, by rw [hS'sp]; exact hRh, by rw [hS'sp]; exact hRwI,
      by rw [hS'sp]; exact hRWm1, by rw [hS'sp]; exact sc _ (by simp [LineScratch])⟩
  have hEl : (X ++ X.take (W - 1)).length = t + W - 1 := by
    rw [List.length_append, List.length_take, hX]
    omega
  have hGl : F.reverse.length = W := by rw [List.length_reverse, hF]
  have hEf : ∀ x ∈ X ++ X.take (W - 1), FitsTwos wI x.1 ∧ FitsTwos wI x.2 := fun x hx => by
    rcases List.mem_append.mp hx with h | h
    · exact hXf x h
    · exact hXf x (List.mem_of_mem_take h)
  have hGf : ∀ y ∈ F.reverse, FitsTwos wT y.1 ∧ FitsTwos wT y.2 := fun y hy =>
    hFf y (List.mem_reverse.mp hy)
  obtain ⟨N, hN⟩ : ∃ N, N = ((X ++ X.take (W - 1)).length + W - 1) / W := ⟨_, rfl⟩
  have hN1 : 0 < N := by
    rw [hN, lt_nblk_iff hW1, Nat.zero_mul, hEl]
    omega
  have hNW : (X ++ X.take (W - 1)).length ≤ N * W := by
    by_contra h
    have := (lt_nblk_iff hW1).2 (show N * W < (X ++ X.take (W - 1)).length by omega)
    rw [← hN] at this
    omega
  have hNle : N ≤ t / W + 2 := by
    rw [hN, hEl]
    exact nblk_le hW1
  -- building the extended line
  have hpre := runs_liftA (Q := fun w => w.q = (csym wI (X ++ X.take (W - 1))).head?) lA
    closed_linePre (fun v => by
      obtain ⟨w, c, e, hc, hq⟩ := linePre_eval t W wI s X rarr [] S v hX (by omega) harr hT2 hT4
        hT5 hX2 hp0 hp1 hp4
      exact ⟨w, c, e, hc, hq⟩)
  have hF0 : loopF s wI q W (X ++ X.take (W - 1)) F.reverse 0 =
      fRest (csym wI (X ++ X.take (W - 1))) (List.replicate ((W - 1) * s) (.bit false))
        (List.replicate ((W - 1) * s) (.bit false)) [] := by
    simp only [loopF, Nat.zero_mul, List.drop_zero, List.take_zero, Nat.zero_min]
    rw [tailBits_pend_nil s Prod.fst rfl F.reverse, tailBits_pend_nil s Prod.snd rfl F.reverse,
      hGl, List.map_replicate]
    rfl
  have h0 : RunsIn [] ((linePre (Esu := Esu)).liftRegs lA) (bst S (fRest [] [] [] []))
      (bst (Function.update S (kW .arr) rarr)
        (loopF s wI q W (X ++ X.take (W - 1)) F.reverse (N - N)))
      (fun x => isBitO (lA.get x).q = decide (0 < N)) (linePreCost t W wI s) := by
    rw [Nat.sub_self, hF0]
    refine RunsIn.mono (RunsIn.iff_runs.mpr hpre) (fun x hx => ?_) le_rfl
    rw [hx, decide_eq_true hN1]
    obtain ⟨y, rest, hyr⟩ : ∃ y rest, X ++ X.take (W - 1) = y :: rest := by
      cases h : X ++ X.take (W - 1) with
      | nil =>
        have := congrArg List.length h
        rw [hEl, List.length_nil] at this
        omega
      | cons y rest => exact ⟨y, rest, rfl⟩
    obtain ⟨b, hb⟩ := head_carrSyms_cons wI hwI1 y rest
    rw [hyr]
    show isBitO (carrSyms wI ((y :: rest).map fun y => [y])).head? = true
    rw [hb]
    rfl
  -- the block loop
  have hstep : ∀ n, n < N → RunsIn [] (blockProg pdp prog lA lM Pm)
      (bst (Function.update S (kW .arr) rarr)
        (loopF s wI q W (X ++ X.take (W - 1)) F.reverse (N - (n + 1))))
      (bst (Function.update S (kW .arr) rarr)
        (loopF s wI q W (X ++ X.take (W - 1)) F.reverse (N - n)))
      (fun x => isBitO (lA.get x).q = decide (0 < n))
      (blkCost s q wI W W Cpd Csp Cm (mulW (2 * (W * s + 1) + 1))) := by
    intro n hn
    have hj : (N - (n + 1)) * W < (X ++ X.take (W - 1)).length := by
      rw [← lt_nblk_iff hW1, ← hN]
      omega
    have e : N - n = N - (n + 1) + 1 := by omega
    rw [e]
    have hst := loop_step hpd hpdc hsp hspc hcl hspec lA lM
      (S0 := Function.update S (kW .arr) rarr) (N - (n + 1)) hj hGl hW1 hqs hwI1 hwIs hEf hGf
      hslot hdig hb' (by rw [hS'sp]; exact hRW) (by rw [hS'sp]; exact hRwI1)
      (by rw [hS'sp]; exact hRsWI) (fun j => by rw [hS'sp]; exact sc _ (by simp [LineScratch]))
      (fun b => by rw [hS'sp]; exact hFk b)
      (fun g => by rw [hS'sp]; exact sc _ (by simp [LineScratch]))
    refine RunsIn.mono (RunsIn.iff_runs.mpr hst) (fun x hx => ?_) le_rfl
    rw [hx]
    have hiff : (N - (n + 1) + 1) * W < (X ++ X.take (W - 1)).length ↔ 0 < n := by
      rw [← lt_nblk_iff hW1, ← hN]
      omega
    by_cases h0 : 0 < n
    · rw [decide_eq_true h0, decide_eq_true (hiff.2 h0)]
    · rw [decide_eq_false h0, decide_eq_false (fun h => h0 (hiff.1 h))]
  have hloop := RunsIn.seq_loop_const
    (st := fun n => bst (Function.update S (kW .arr) rarr)
      (loopF s wI q W (X ++ X.take (W - 1)) F.reverse (N - n)))
    (B := fun _ => blkCost s q wI W W Cpd Csp Cm (mulW (2 * (W * s + 1) + 1)))
    (b := blkCost s q wI W W Cpd Csp Cm (mulW (2 * (W * s + 1) + 1))) h0 hstep
    (fun _ _ => le_rfl)
  have hFN : loopF s wI q W (X ++ X.take (W - 1)) F.reverse N =
      fRest [] ((tailBits s Prod.fst (pend (X ++ X.take (W - 1)) F.reverse)).map Sym.bit)
        ((tailBits s Prod.snd (pend (X ++ X.take (W - 1)) F.reverse)).map Sym.bit)
        (csym wI ((lineConv t W X F).map (roundHalfUpShiftC q))).reverse := by
    rw [loopF, List.drop_eq_nil_of_le hNW, List.take_of_length_le hNW, Nat.min_eq_right hNW, hEl,
      outs_lineConv]
    rfl
  simp only [Nat.sub_zero] at hloop
  rw [hFN] at hloop
  -- rotating the outputs onto `Out`
  have hpost := runs_liftA (Q := fun _ => True) lA closed_linePost (fun v => by
    obtain ⟨w, c, e, hc⟩ := linePost_eval t W wI a0 q X F
      (tailBits s Prod.fst (pend (X ++ X.take (W - 1)) F.reverse))
      (tailBits s Prod.snd (pend (X ++ X.take (W - 1)) F.reverse)) (S (sp .Out))
      (Function.update S (kW .arr) rarr) v hX hF hW1 hWt ha0
      (by rw [hS'sp]; exact hP1) (by rw [hS'sp]; exact hP2) (hS'sp _)
      (by rw [hS'sp]; exact hX2) (by rw [hS'sp]; exact hp0) (by rw [hS'sp]; exact hp2)
      (by rw [hS'sp]; exact hp3)
    exact ⟨w, c, e, hc, trivial⟩)
  rw [length_tailBits, length_tailBits, length_pend, hGl] at hpost
  have hall := RunsIn.seq hloop (RunsIn.iff_runs.mpr hpost)
  have hfin : bst (Function.update (Function.update S (kW .arr) rarr) (sp .Out)
      ((csym wI (lineOut q t W a0 X F)).reverse ++ S (sp .Out))) (fRest [] [] [] []) =
      Function.update (Function.update S (kW .arr) rarr) (sp .Out)
        ((carrSyms wI ((lineOut q t W a0 X F).map fun y => [y])).reverse ++ S (sp .Out)) := by
    apply bst_fRest_nil
    intro x hx
    have hne : sp x ≠ (sp .Out : SK Esu) := fun h => by
      have := sp_injective h
      subst this
      simp [LineScratch] at hx
    rw [Function.update_of_ne hne, hS'sp, sc x hx]
  rw [hfin, bst_fRest_nil sc] at hall
  refine WP.W9comp.runs_mono (RunsIn.iff_runs.mp hall) (fun _ _ => trivial) ?_
  have hA : 1 ≤ (t + W) * (s + 1) :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  unfold lineCost
  exact cost_combine (linePreCost_le hwIs hW1) (linePostCost_le hwIs hW1 ha0) hA hNle
    (blkCost_le hqs hwIs hW1 (one_le_mulW _))

end SubNLogN.Machine.Bridge.SpreadAux.Line
