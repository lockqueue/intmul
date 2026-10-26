import WP.Top.Cost
import Contracts.Top.W12

/-!
# WP.Top.Main — `intMul_TM2_nlogn_of_stages`

**The final theorem, modulo the stage contracts** (`TopStatement`, WP.Top.Skeleton).

Proof outline:
1. **Open the stage contracts.**
   * W0m (at `GW`, `ι0`) gives `Pin`.
   * W7 gives `P7` (`m7 ≤ 32`), TapeConv gives `Pc` (`mc ≤ 75`).
   * W5 fixes `Mul := T3 c0 c1 w0` (`W5_toom3Mul_iff_mulAt`); W9 at that `Mul` gives `P9` (`m9 ≤ 64`).
   * The registers `σi × R7 × Rc × R9 × Option Sym` are finite (`Fintype.ofFinite`).
2. **Correctness** (`top_triple`): every input `(a, b)` reaches `outputStk (encodeNat (a * b))`. W7
   chooses a hierarchy `cS a b` (skolemized); the cost is `topCost … a b`.
3. **Cost glue.**
   * For `n = operandBits a b` above `N`, `topCost … a b ≤ (topCosts …).total M n` (`hfg`). This
     uses `tin_le`, `aux_le`, `out_le`, W9CostShape, and W7's √n bounds.
   * `topCosts_bounds` gives `StageBounds`; `mulBound_of_T3` gives `MulBound`. So W10 yields
     `NLogN (total M)`.
4. **From bit length to input length.**
   * `T L := supCost (topCost …) L`, the maximum over `a, b < 2^L`, bounds the cost of every input of
     length `L` (`le_supCost`).
   * `eventually_supCost` gives `T L + 1 ≤ C·L·log₂ L` eventually. Inputs with `operandBits < N` are
     finitely many, and their cost is absorbed into the constant.
5. **`W12_assembly_holds`.**
-/

namespace WP.Top

open Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  IntMulTM.Contracts.Top

/-! ## From the operand bit length to the input length -/

/-- The maximum of `f` over operand pairs below `2^L`. -/
def supCost (f : ℕ → ℕ → ℕ) (L : ℕ) : ℕ :=
  ((Finset.range (2 ^ L)) ×ˢ (Finset.range (2 ^ L))).sup fun p => f p.1 p.2

theorem le_supCost (f : ℕ → ℕ → ℕ) {a b L : ℕ} (ha : a < 2 ^ L) (hb : b < 2 ^ L) :
    f a b ≤ supCost f L :=
  Finset.le_sup (f := fun p : ℕ × ℕ => f p.1 p.2) (b := (a, b))
    (Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr hb⟩)

theorem supCost_le (f : ℕ → ℕ → ℕ) {L B : ℕ} (h : ∀ a b, a < 2 ^ L → b < 2 ^ L → f a b ≤ B) :
    supCost f L ≤ B :=
  Finset.sup_le fun p hp => by
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    exact h p.1 p.2 (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)

theorem operandBits_le {a b L : ℕ} (hL : 1 ≤ L) (ha : a < 2 ^ L) (hb : b < 2 ^ L) :
    operandBits a b ≤ L := by
  unfold operandBits
  have h1 : (encodeNat a).length ≤ L := by rw [length_encodeNat]; exact Nat.size_le.mpr ha
  have h2 : (encodeNat b).length ≤ L := by rw [length_encodeNat]; exact Nat.size_le.mpr hb
  omega

theorem lt_two_pow_enc_left (a b : ℕ) : a < 2 ^ (encNatPair.encode (a, b)).length := by
  rw [encNatPair_encode_length]
  exact (lt_two_pow_length_encodeNat a).trans_le (Nat.pow_le_pow_right (by omega) (by omega))

theorem lt_two_pow_enc_right (a b : ℕ) : b < 2 ^ (encNatPair.encode (a, b)).length := by
  rw [encNatPair_encode_length]
  exact (lt_two_pow_length_encodeNat b).trans_le (Nat.pow_le_pow_right (by omega) (by omega))

/-- **Eventually `O(L log L)` in the input length.** If `f a b` is bounded by `g` at the operand
bit length above `N`, and `g` is eventually `≤ C·n·log₂ n`, then the maximum over inputs of length
`L` (`supCost`) satisfies `T L + 1 ≤ C'·L·log₂ L` eventually. The finitely many inputs with
`operandBits < N` contribute the constant `supCost f N`. -/
theorem eventually_supCost (f : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (N C : ℕ)
    (hfg : ∀ a b, N ≤ operandBits a b → f a b ≤ g (operandBits a b))
    (hg : ∀ n ≥ N, g n ≤ C * n * Nat.log2 n) :
    ∃ C' N', ∀ L ≥ N', supCost f L + 1 ≤ C' * L * Nat.log2 L := by
  refine ⟨C + supCost f N + 1, max N 2, fun L hL => ?_⟩
  have hL2 : 2 ≤ L := le_of_max_le_right hL
  have hlog : 1 ≤ Nat.log2 L := log2_pos hL2
  have hX : 1 ≤ L * Nat.log2 L := le_trans (by omega) (Nat.le_mul_of_pos_right L hlog)
  have hsup : supCost f L ≤ supCost f N + C * (L * Nat.log2 L) := by
    refine supCost_le f (fun a b ha hb => ?_)
    obtain ⟨hA, hB, -, -⟩ := input_bridge a b
    by_cases hn : N ≤ operandBits a b
    · have h1 := hfg a b hn
      have h2 := hg _ hn
      have h3 := nlogn_mono (operandBits_le (by omega) ha hb)
      have h4 : C * operandBits a b * Nat.log2 (operandBits a b) ≤ C * (L * Nat.log2 L) := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left C h3
      omega
    · push_neg at hn
      have hpow : 2 ^ operandBits a b ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) hn.le
      have : f a b ≤ supCost f N := le_supCost f (hA.trans_le hpow) (hB.trans_le hpow)
      omega
  have e : (C + supCost f N + 1) * L * Nat.log2 L =
      C * (L * Nat.log2 L) + (supCost f N + 1) * (L * Nat.log2 L) := by ring
  have hK : supCost f N + 1 ≤ (supCost f N + 1) * (L * Nat.log2 L) :=
    Nat.le_mul_of_pos_right _ hX
  rw [e]
  omega

/-! ## The per-input cost -/

/-- The per-input cost of the composed program, for the hierarchy choice `cS`. -/
def topCost (C0 C7 Cc C9 : ℕ) (Mul : ℕ → ℕ) (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ)
    (cS : ℕ → ℕ → IntMul.ComputablePaperFastDFTSpec) (a b : ℕ) : ℕ :=
  (C0 * ((encNatPair.encode (a, b)).length + 1) +
      C0 * ((WP.W0m.lam a b + 1) * (WP.W0m.lam a b + 1))) +
    (tabCost C7 (operandBits a b) (cS a b) + (convCost Cc (cS a b) +
      (glueCost (operandBits a b) + (w9Cost C9 Mul wdF wdI wR (operandBits a b) (cS a b) +
        outCost (bitLen (a * b)) (totalSize (w9Out (operandBits a b) a b (cS a b) (a * b)))))))

/-! ## The theorem -/

/-- **`intMul_TM2_nlogn_of_stages`: integer multiplication in `O(L log L)` on Mathlib's
`TM2ComputableInTime`, from the stage contracts and the open obligations.** -/
theorem intMul_TM2_nlogn_of_stages : TopStatement := by
  intro wdF wdI wR h0 h7 h7c h7t h5 h5b h9 hconv hroot hshape
  -- 1. the stage contracts
  obtain ⟨σi, hfi, hni, C0, hW0⟩ := h0
  obtain ⟨Pin, hclin, hin⟩ := hW0 GW ι0 ι0_inj
  obtain ⟨C7, hC7⟩ := h7
  obtain ⟨m7, R7, -, P7, hm7, hf7, hn7, hcl7, hspec7⟩ := hC7 ()
  obtain ⟨Cc, hCc⟩ := hconv
  obtain ⟨mc, Rc, -, Pc, hmc, hfc, hnc, hclc, hspecc⟩ := hCc ()
  obtain ⟨c0, c1, w0, hmul⟩ := W5_toom3Mul_iff_mulAt.mp h5
  obtain ⟨C9, hC9⟩ := h9 (T3 c0 c1 w0) hmul
  obtain ⟨m9, R9, P9, hm9, hf9, hn9, hcl9, hspec9⟩ := hC9 ()
  obtain ⟨pc, A9, K9, N9, hpb, hcs⟩ := hshape c0 c1 w0 C9
  obtain ⟨CM, hMB⟩ := mulBound_of_T3 h5b c0 c1 w0 K9
  obtain ⟨Cp, Np, hCp⟩ := h7c
  obtain ⟨Ct, Nt, hCt⟩ := h7t
  haveI := hfi
  haveI := hf7
  haveI := hfc
  haveI := hf9
  haveI : Fintype σi := Fintype.ofFinite σi
  haveI : Fintype R7 := Fintype.ofFinite R7
  haveI : Fintype Rc := Fintype.ofFinite Rc
  haveI : Fintype R9 := Fintype.ofFinite R9
  -- 2. correctness, with W7's hierarchy choice skolemized
  have htop := fun a b => top_triple
    (Tin := fun a b => C0 * ((encNatPair.encode (a, b)).length + 1) +
      C0 * ((WP.W0m.lam a b + 1) * (WP.W0m.lam a b + 1)))
    hm7 hmc hm9 hin hspec7 hspecc hspec9 hroot
    (Classical.choice hni, Classical.choice hn7, Classical.choice hnc, Classical.choice hn9, none) a b
  obtain ⟨cS, hcS⟩ := Classical.skolem.mp (fun a => Classical.skolem.mp (htop a))
  -- 3. the cost glue
  have hW10 := WP.W10.W10_cost_holds (topCosts C0 C7 Cp Ct Cc C9 (max (max Np Nt) N9) pc) _
    (topCosts_bounds hpb) (mulCost K9 (T3 c0 c1 w0)) CM hMB
  obtain ⟨C10, N10, hC10⟩ := hW10
  have hfg : ∀ a b, max (max (max Np Nt) N9) N10 ≤ operandBits a b →
      topCost C0 C7 Cc C9 (T3 c0 c1 w0) wdF wdI wR cS a b ≤
        (topCosts C0 C7 Cp Ct Cc C9 (max (max Np Nt) N9) pc).total (mulCost K9 (T3 c0 c1 w0))
          (operandBits a b) := by
    intro a b hN
    have hNn : max (max Np Nt) N9 ≤ operandBits a b := le_trans (le_max_left _ _) hN
    have hNp : Np ≤ operandBits a b :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNn
    have hNt : Nt ≤ operandBits a b :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNn
    have hN9 : N9 ≤ operandBits a b := le_trans (le_max_right _ _) hNn
    have hn1 : 1 ≤ operandBits a b := WP.W0m.operandBits_pos a b
    have hj := (hcS a b).1
    have hP : (W8.hSpec (operandBits a b)).precomputeSeriesTableCost ≤
        Cp * sqP (operandBits a b) := by
      have h := hCp _ hNp
      unfold sqP
      rw [← Nat.mul_assoc]
      exact h
    have hT7 : (W7.tape W7.snapshotSchedule.toTapeFormat (cS a b)).length ≤
        Ct * sqP (operandBits a b) := by
      have h1 := hj.size
      have h2 := hCt _ hNt (cS a b) hj.canonical hj.faithful
      have h3 : (Nat.log2 (operandBits a b) + 1) ^ 3 ≤ (Nat.log2 (operandBits a b) + 1) ^ 8 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : Ct * (Nat.sqrt (operandBits a b) + 1) * (Nat.log2 (operandBits a b) + 1) ^ 3 ≤
          Ct * sqP (operandBits a b) := by
        unfold sqP
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      exact le_trans h1 (le_trans h2 h4)
    have hTS := (hspecc (operandBits a b) (cS a b)
      (fun _ => W7.tape W7.snapshotSchedule.toTapeFormat (cS a b)) hj rfl).1
    have h1 := tin_le C0 a b
    have h2 := aux_le C7 Cp Ct Cc C9 (operandBits a b) hn1 (cS a b) hP hT7 hTS
    have h3 := hcs (operandBits a b) hN9 (cS a b) hj
    have h4 := out_le Cc Ct a b (cS a b) hT7 hTS
    have hw9 : w9Cost C9 (T3 c0 c1 w0) wdF wdI wR (operandBits a b) (cS a b) =
        C9 * (rootBound (T3 c0 c1 w0) (wR (operandBits a b)) (W8.hB (operandBits a b))
            (W8.hK0 (operandBits a b)) (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) +
          pipeBound (T3 c0 c1 w0) (wdF (operandBits a b)) (cS a b) (W8.hB (operandBits a b)) 0 1 +
          pipeBound (T3 c0 c1 w0) (wdI (operandBits a b)) (cS a b)
            (IntMul.rootPrecision (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))) 0 1) +
        C9 * ((tapeSyms (cS a b)).length + 1) := by
      unfold w9Cost
      ring
    rw [topCosts_total]
    unfold tabsN outN topCost
    rw [if_pos hNn, if_pos hNn, hw9]
    omega
  -- 4.–5. assembly
  refine W12_assembly_holds GW (TopRegs σi R7 Rc R9) (topProg Pin P7 hm7 Pc hmc P9 hm9)
    (Classical.choice hni, Classical.choice hn7, Classical.choice hnc, Classical.choice hn9, none)
    (supCost (topCost C0 C7 Cc C9 (T3 c0 c1 w0) wdF wdI wR cS))
    (topProg_closed hm7 hmc hm9 hclin hcl7 hclc hcl9) (fun a b => ?_) ?_
  · exact (hcS a b).2.cost_mono
      (le_supCost (topCost C0 C7 Cc C9 (T3 c0 c1 w0) wdF wdI wR cS) (lt_two_pow_enc_left a b)
        (lt_two_pow_enc_right a b))
  · exact eventually_supCost _ _ _ C10 hfg (fun n hn => hC10 n (le_trans (le_max_right _ _) hn))

#assert_std_axioms le_supCost supCost_le operandBits_le lt_two_pow_enc_left lt_two_pow_enc_right
  eventually_supCost intMul_TM2_nlogn_of_stages

end WP.Top
