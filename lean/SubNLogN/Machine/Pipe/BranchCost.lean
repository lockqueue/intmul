/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Pipe.BranchDefs
import SubNLogN.Machine.Pipe.Contract
import SubNLogN.Machine.Tables.Lists
import SubNLogN.Math.Cost.WalshAggregate
import SubNLogN.Math.Bridge.Proofs.WalshOK

/-!
# K7 (`Machine/Pipe/BranchCost.lean`): the Walsh cost clause of the branch

Main result: `walshCostClause_branchCost_of`. The step bound `branchCost rpCost X fnewSched md` of
the Walsh branch (`BranchDefs.lean`: two calls of `callCost`, Sections 7.3–7.4 (`sec:main-tables`–`sec:main-gaps`))
satisfies `WalshCostClause` (`Contract.lean`, with `m = mLog`, `A_m = 1`, `j_m = 1`), provided the
four parts that are not fixed in `BranchDefs.lean` obey the bounds below. Each enters as an explicit
hypothesis that holds eventually in `n`, at both call precisions
`p_in ∈ {W8.hB n, rootPrecision (W8.hB n) (W8.hK0 n)}` (`BranchPin`):
* `hRP` (parameter kernel): `rpCost b K0 p_in ≤ c·P^j`;
* `hX` (interchange factor): `X ℓ ≤ c·(1 + ⌈ℓ^τ⌉₊)` for all large `ℓ`;
* `hMid` (middle transform): `Tmid ≤ c·V·(d·K + ℓ·⌈d^{λ'}⌉₊ + ℓ + 1) + c·ℓ·2^k·mulW((c+1)P)
  + c·((2^k/r)·P^j + r·P^j + P^j)` (the shape of `midCost`);
* `hMH` (middle header): `|hdrSyms mhdr| ≤ c·P^j`.
Here `P = PBK b k`, `V = VBK b k = 2^k P`, `d = dK row46 k`, `ℓ = lK row46 k`, `K = KK row46 k`
at `b = w8B n`, `k = w8K n`, and `τ, λ'` are `Row46.tau`, `Row46.lam'`.

Everything else in `callCost` is bounded in this file: guard and record conversions (`O(V)`),
the tables (`tabCost = O((2^k/r)·P^8 + r·P^6 + P^4)`), the bridge (`bridgeCost`: exposures via
`eventually_expose_le_W`, spreading line passes via `spread_term_le`, solver products via
`eventually_dmulW_le_W`, the rest `O(d·V + V)` or polynomial in `P`), header and table-stack
lengths.

## Layout
* `BranchCostAux` §1: list and size helpers (`hdrSyms`, table stacks); §2: the shape
  `fnewShape row46 k` (`totalLen = 2^k`, axes `≤ r`, prefix products `≤ 2^k/r`, `axisBits = ℓ`);
  §3: generic bounds on `tabCost` and `bridgeCost` for any `BrPar` satisfying `ParOK`;
  §4: `ParOK` at the pipe's parameters (`parOK_of_facts`) and the pointwise bound `callCost_le`;
  §5: the eventual per-call bound `eventually_callCost_le`.
* `walshCostClause_branchCost_of`: the clause.
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN SubNLogN.S5 Computability TMFw TMFw.Contracts TMFw.Contracts.W9 IntMulTM
  IntMulTM.Contracts SubNLogN.Machine SubNLogN.Math.Common SubNLogN.Math.Bridge
  SubNLogN.Math.Cost
open Filter

/-- The two call precisions of the Walsh branch at size `n` (`branchCost`): `p_in = W8.hB n` and
`p_in = rootPrecision (W8.hB n) (W8.hK0 n)`. -/
def BranchPin (n pin : ℕ) : Prop :=
  pin = W8.hB n ∨ pin = IntMul.rootPrecision (W8.hB n) (W8.hK0 n)

namespace BranchCostAux

/-! ## 1. List and size helpers -/

theorem sum_map_le_mul {α : Type} (l : List α) (f : α → ℕ) (B : ℕ) (h : ∀ x ∈ l, f x ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem size_le_self (x : ℕ) : Nat.size x ≤ x := Nat.size_le.2 Nat.lt_two_pow_self

theorem length_hdrSyms_eq (fs : List ℕ) :
    (hdrSyms fs).length = (fs.map fun n => Nat.size n + 1).sum := by
  unfold hdrSyms
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro n _
  rw [List.length_append, length_natSyms, bitLen, IntMulTM.length_encodeNat, List.length_singleton]

theorem length_hdrSyms_le (fs : List ℕ) (M : ℕ) (h : ∀ x ∈ fs, Nat.size x ≤ M) :
    (hdrSyms fs).length ≤ fs.length * (M + 1) := by
  rw [length_hdrSyms_eq]
  apply sum_map_le_mul
  intro x hx
  have := h x hx
  omega

theorem length_hdrSyms_single (x : ℕ) : (hdrSyms [x]).length ≤ x + 1 := by
  rw [length_hdrSyms_eq]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have := size_le_self x
  omega

theorem length_hdr (bp : BrPar) : bp.hdr.length = 9 + bp.d := by
  rw [BrPar.hdr, List.length_append, List.length_ofFn]
  rfl

theorem hdr_size_le (bp : BrPar) (M : ℕ)
    (h9 : bp.p ≤ M ∧ bp.P ≤ M ∧ bp.ω ≤ M ∧ bp.wI ≤ M ∧ bp.wT ≤ M ∧ bp.wOut ≤ M ∧ bp.pIn ≤ M ∧
      bp.wIn ≤ M ∧ bp.d ≤ M)
    (ht : ∀ i, Nat.size (bp.t i) ≤ M) : ∀ x ∈ bp.hdr, Nat.size x ≤ M := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h9
  intro x hx
  rw [BrPar.hdr, List.mem_append] at hx
  rcases hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact le_trans (size_le_self _) (by assumption)
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact ht i

theorem length_flatten_append_mark (L : List (List Sym)) :
    ((L.map (· ++ [Sym.mark])).flatten).length = (L.map fun s => s.length + 1).sum := by
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_singleton,
      List.sum_cons, ih]

theorem length_tapTabSyms_le (bp : BrPar) (T : BridgeTables bp.t) :
    (tapTabSyms bp.wT bp.P bp.t T).length ≤ tapTabLen bp := by
  rw [Tables.tapTabSyms_eq_segs, length_flatten_append_mark]
  exact Tables.sum_tapSegs_le bp T

theorem length_solTabSyms_eq (bp : BrPar) (T : BridgeTables bp.t) :
    (solTabSyms bp.wT bp.P bp.t T).length = solTabLen bp := by
  rw [Tables.solTabSyms_eq_segs, length_flatten_append_mark]
  exact Tables.sum_solSegs_eq bp T

theorem length_tapOffsets_le {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (i : Fin d) :
    (tapOffsets t P i).length ≤ 2 * P + 1 := by
  unfold tapOffsets
  split_ifs with h
  · simp
  · simp
    omega

/-! ## 2. The shape `fnewShape row46 k` -/

theorem one_le_fnewShape (k : ℕ) (i : Fin (fnewD row46 k + 1)) : 1 ≤ fnewShape row46 k i :=
  Nat.one_le_two_pow

theorem fnewShape_le_rK (k : ℕ) (i : Fin (fnewD row46 k + 1)) :
    fnewShape row46 k i ≤ rK row46 k := by
  unfold fnewShape rK
  apply Nat.pow_le_pow_right (by norm_num)
  split_ifs with h
  · unfold fnewA
    split_ifs <;> omega
  · exact le_refl _

theorem log2_fnewShape_le (k : ℕ) (i : Fin (fnewD row46 k + 1)) :
    Nat.log2 (fnewShape row46 k i) ≤ lK row46 k := by
  unfold fnewShape
  rw [Nat.log2_two_pow]
  split_ifs with h
  · unfold fnewA
    split_ifs <;> omega
  · exact le_refl _

theorem fnewShape_last (k : ℕ) : fnewShape row46 k (Fin.last _) = rK row46 k := by
  unfold fnewShape rK
  rw [dif_neg (by simp)]
  rfl

/-- `axisBits (fnewShape row46 k) = ℓ`: every axis has `log₂ t_i ≤ ℓ`, the last one `= ℓ`. -/
theorem axisBits_fnewShape (k : ℕ) : axisBits (fnewShape row46 k) = lK row46 k := by
  unfold axisBits
  apply le_antisymm
  · exact Finset.sup_le fun i _ => log2_fnewShape_le k i
  · have h : Nat.log2 (fnewShape row46 k (Fin.last _)) = lK row46 k := by
      rw [fnewShape_last]
      exact Nat.log2_two_pow
    rw [← h]
    exact Finset.le_sup (f := fun i => Nat.log2 (fnewShape row46 k i)) (Finset.mem_univ _)

/-- `totalLen (fnewShape row46 k) = 2^k` (as in `walshOK_balanced`, using only `d ≥ 1`, `ℓ ≥ 1`;
`dℓ - k < d` holds since `ℓ = ⌈k/d⌉`). -/
theorem totalLen_fnewShape {k : ℕ} (hd : 1 ≤ dK row46 k) (hl : 1 ≤ lK row46 k) :
    totalLen (fnewShape row46 k) = 2 ^ k := by
  have hK : k ≤ dK row46 k * lK row46 k := WalshOKProof.le_dK_mul_lK row46 k hd
  have h1 : dK row46 k * lK row46 k ≤ k + dK row46 k - 1 := by
    have := Nat.div_mul_le_self (k + dK row46 k - 1) (dK row46 k)
    unfold lK
    rw [Nat.mul_comm]
    exact this
  have hs : dK row46 k * lK row46 k - k < dK row46 k := by omega
  show ∏ i, fnewShape row46 k i = 2 ^ k
  simp only [fnewShape]
  rw [Finset.prod_pow_eq_pow_sum, WalshOKProof.fnewShape_exp_sum,
    WalshOKProof.sum_range_ite_exp _ _ _ (by unfold fnewD; omega)]
  congr 1
  have := WalshOKProof.exp_sum_arith (dK row46 k) (lK row46 k) k hd hl hK hs
  unfold fnewD
  exact this

theorem prefixProd_mul_dvd {d : ℕ} (t : Fin d → ℕ) (i j : Fin d) (hij : (i : ℕ) ≤ j) :
    prefixProd t i * t j ∣ totalLen t := by
  unfold prefixProd totalLen
  have hj : j ∉ Finset.univ.filter (fun l : Fin d => (l : ℕ) < i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact hij
  rw [mul_comm, ← Finset.prod_insert hj]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

/-- Every prefix product of `fnewShape row46 k` is at most `2^k/r` (the last axis is `r = 2^ℓ`). -/
theorem prefixProd_le_div {k : ℕ} (hd : 1 ≤ dK row46 k) (hl : 1 ≤ lK row46 k)
    (i : Fin (fnewD row46 k + 1)) :
    prefixProd (fnewShape row46 k) i ≤ 2 ^ k / rK row46 k := by
  have hr : 0 < rK row46 k := by unfold rK; positivity
  rw [Nat.le_div_iff_mul_le hr, ← fnewShape_last k]
  apply Nat.le_of_dvd (by positivity)
  rw [← totalLen_fnewShape hd hl]
  exact prefixProd_mul_dvd _ i (Fin.last _) (Fin.le_last i)

theorem mul_prefixProd_le {k : ℕ} (hd : 1 ≤ dK row46 k) (hl : 1 ≤ lK row46 k)
    (i : Fin (fnewD row46 k + 1)) :
    fnewShape row46 k i * prefixProd (fnewShape row46 k) i ≤ 2 ^ k := by
  rw [mul_comm, ← totalLen_fnewShape hd hl]
  apply Nat.le_of_dvd (by rw [totalLen_fnewShape hd hl]; positivity)
  exact prefixProd_mul_dvd _ i i le_rfl

/-! ## 3. Generic cost bounds for a bridge parameter record -/

/-- Side conditions on bridge parameters `bp` used by the generic bounds: widths `O(P)`, `d ≤ P`,
axes `1 ≤ t_i ≤ r` of bit length `≤ P - 4`, prefix products `≤ Rr`, and setup `≤ 125 P^6`. -/
structure ParOK (bp : BrPar) (Rr r : ℕ) : Prop where
  hP : 100 ≤ bp.P
  hdP : bp.d ≤ bp.P
  hwI : bp.wI ≤ 2 * bp.P
  hwT : bp.wT ≤ 2 * bp.P
  hwOut : bp.wOut ≤ 3 * bp.P
  hwIn : bp.wIn ≤ 3 * bp.P
  hω : bp.ω ≤ 3 * bp.P
  ht1 : ∀ i, 1 ≤ bp.t i
  htr : ∀ i, bp.t i ≤ r
  hts : ∀ i, Nat.size (bp.t i) + 4 ≤ bp.P
  hA : ∀ i : Fin bp.d, prefixProd bp.t i ≤ Rr
  hAt : ∀ i : Fin bp.d, Nat.size (2 * bp.t i * prefixProd bp.t i) + 4 ≤ bp.P
  hS : bp.setup ≤ 125 * bp.P ^ 6

section Generic

variable {bp : BrPar} {Rr r : ℕ}

theorem tapTabLen_le (h : ParOK bp Rr r) :
    tapTabLen bp ≤ bp.d * (13 * (Rr * bp.P ^ 2) + 1) := by
  unfold tapTabLen
  refine le_trans (sum_map_le_mul _ _ (13 * (Rr * bp.P ^ 2) + 1) ?_) ?_
  · intro i _
    have h1 := h.hA i
    have h2 := length_tapOffsets_le bp.t bp.P i
    have h3 := h.hwT
    have hP := h.hP
    have h4 : (tapOffsets bp.t bp.P i).length * (2 * bp.wT) + 1 ≤ 13 * bp.P ^ 2 := by
      have h5 : (tapOffsets bp.t bp.P i).length * (2 * bp.wT) ≤ (3 * bp.P) * (4 * bp.P) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h6 : (3 * bp.P) * (4 * bp.P) = 12 * bp.P ^ 2 := by ring
      have h7 : 1 ≤ bp.P ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    calc prefixProd bp.t ↑i * ((tapOffsets bp.t bp.P i).length * (2 * bp.wT) + 1) + 1
        ≤ Rr * (13 * bp.P ^ 2) + 1 := Nat.add_le_add_right (Nat.mul_le_mul h1 h4) 1
      _ = 13 * (Rr * bp.P ^ 2) + 1 := by ring
  · rw [Tables.length_spreadOrder]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

theorem solTabLen_le (h : ParOK bp Rr r) : solTabLen bp ≤ bp.d * (13 * (r * bp.P) + 1) := by
  unfold solTabLen
  refine le_trans (sum_map_le_mul _ _ (13 * (r * bp.P) + 1) ?_) ?_
  · intro i _
    have h1 := h.htr i
    have h3 := h.hwT
    have hP := h.hP
    calc bp.t i * (3 * (2 * bp.wT) + 1) + 1 ≤ r * (13 * bp.P) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul h1 (by omega)) 1
      _ = 13 * (r * bp.P) + 1 := by ring
  · rw [Tables.length_deconvOrder]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

theorem tabUnit_le (h : ParOK bp Rr r) (i : Fin bp.d) : tabUnit bp i ≤ 100000 * bp.P ^ 5 := by
  unfold tabUnit
  have h1 := h.hAt i
  have h2 := h.hω
  have hP := h.hP
  calc (bp.ω + 4 * bp.P + 2 * Nat.size (2 * bp.t i * prefixProd bp.t ↑i) + 100) ^ 5
      ≤ (10 * bp.P) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    _ = 100000 * bp.P ^ 5 := by ring

theorem tabCost_le (h : ParOK bp Rr r) :
    tabCost bp ≤ 900000 * (Rr * bp.P ^ 8) + 100000 * (r * bp.P ^ 6) + 6250000 * bp.P ^ 4 +
      tapTabLen bp + solTabLen bp + 125 * bp.P ^ 6 := by
  have hP := h.hP
  have hdP := h.hdP
  have hsp : ((spreadOrder bp.d).map fun i : Fin bp.d =>
      prefixProd bp.t i * ((2 * bp.P + 1) * (2 * bp.P + 1) * tabUnit bp i)).sum ≤
      900000 * (Rr * bp.P ^ 8) := by
    refine le_trans (sum_map_le_mul _ _
      (Rr * ((3 * bp.P) * (3 * bp.P) * (100000 * bp.P ^ 5))) ?_) ?_
    · intro i _
      exact Nat.mul_le_mul (h.hA i) (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega))
        (tabUnit_le h i))
    · rw [Tables.length_spreadOrder]
      calc (bp.d - 1) * (Rr * ((3 * bp.P) * (3 * bp.P) * (100000 * bp.P ^ 5)))
          ≤ bp.P * (Rr * ((3 * bp.P) * (3 * bp.P) * (100000 * bp.P ^ 5))) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 900000 * (Rr * bp.P ^ 8) := by ring
  have hdc : ((deconvOrder bp.d).map fun i : Fin bp.d => bp.t i * tabUnit bp i).sum ≤
      100000 * (r * bp.P ^ 6) := by
    refine le_trans (sum_map_le_mul _ _ (r * (100000 * bp.P ^ 5)) ?_) ?_
    · intro i _
      exact Nat.mul_le_mul (h.htr i) (tabUnit_le h i)
    · rw [Tables.length_deconvOrder]
      calc (bp.d - 1) * (r * (100000 * bp.P ^ 5)) ≤ bp.P * (r * (100000 * bp.P ^ 5)) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 100000 * (r * bp.P ^ 6) := by ring
  have hon : tabOnce bp ≤ 6250000 * bp.P ^ 4 := by
    unfold tabOnce
    calc (40 * bp.P + 1000) ^ 4 ≤ (50 * bp.P) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      _ = 6250000 * bp.P ^ 4 := by ring
  have hS := h.hS
  unfold tabCost
  omega

/-- Constant of the pointwise spreading bound (`spread_term_le` at `c = 5`). -/
def spreadK : ℕ := 16 * (mLog (6 * 5 + 3) + 1) * (2 * 5 + 3) + 2 * 5 + 1

theorem spreadCost_le (h : ParOK bp Rr r) (i : Fin bp.d) :
    spreadCost bp i ≤ 10 * (bp.R * bp.P) + spreadK * (bp.R * bp.P * mLog (bp.P ^ 2)) +
      bp.d * tapTabLen bp + 125 * bp.P ^ 6 := by
  have hP := h.hP
  have hwI := h.hwI
  have hwT := h.hwT
  have hts := h.hts i
  have hslot : spreadSlot bp i ≤ 5 * bp.P := by unfold spreadSlot; omega
  have hLP : bp.R / bp.t i * ((bp.t i / spreadWin bp.t bp.P i + 1) *
      (4 * mulW (2 * spreadBlkBits bp i + 1)) + spreadWin bp.t bp.P i * (2 * bp.wT + 1)) ≤
      spreadK * (bp.R * bp.P * mLog (bp.P ^ 2)) :=
    spread_term_le (P := bp.P) (R := bp.R) (t := bp.t i) (slot := spreadSlot bp i)
      (wT := bp.wT) (c := 5) (by omega) (h.ht1 i) hslot (by omega)
  have hv : vol1 bp.R bp.wI ≤ 5 * (bp.R * bp.P) := by
    unfold vol1
    calc bp.R * (2 * bp.wI + 1) ≤ bp.R * (5 * bp.P) := Nat.mul_le_mul_left _ (by omega)
      _ = 5 * (bp.R * bp.P) := by ring
  have hs : bp.R * spreadSlot bp i ≤ 5 * (bp.R * bp.P) := by
    calc bp.R * spreadSlot bp i ≤ bp.R * (5 * bp.P) := Nat.mul_le_mul_left _ hslot
      _ = 5 * (bp.R * bp.P) := by ring
  have hS := h.hS
  unfold spreadCost
  omega

theorem solveCost_le (h : ParOK bp Rr r) :
    solveCost bp ≤ 9 * (bp.R * bp.P) + bp.R * mulW (bp.wI + bp.wT + 1) +
      bp.d * solTabLen bp + 125 * bp.P ^ 6 := by
  have hP := h.hP
  have hwI := h.hwI
  have hwT := h.hwT
  have hv : vol1 bp.R (bp.wI + bp.wT) ≤ 9 * (bp.R * bp.P) := by
    unfold vol1
    calc bp.R * (2 * (bp.wI + bp.wT) + 1) ≤ bp.R * (9 * bp.P) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 9 * (bp.R * bp.P) := by ring
  have hS := h.hS
  unfold solveCost
  omega

theorem preCost_le (h : ParOK bp Rr r) :
    preCost bp ≤ 7 * (bp.R * bp.P) + 4 * bp.P + 125 * bp.P ^ 6 := by
  have hP := h.hP
  have hwI := h.hwI
  have hwIn := h.hwIn
  have h1 : bp.R * (bp.wIn + bp.wI + 1) ≤ 6 * (bp.R * bp.P) := by
    calc bp.R * (bp.wIn + bp.wI + 1) ≤ bp.R * (6 * bp.P) := Nat.mul_le_mul_left _ (by omega)
      _ = 6 * (bp.R * bp.P) := by ring
  have h2 : bp.R ≤ bp.R * bp.P := Nat.le_mul_of_pos_right _ (by omega)
  have hS := h.hS
  unfold preCost eBound
  omega

theorem postCost_le (h : ParOK bp Rr r) :
    postCost bp ≤ 7 * (bp.R * bp.P) + 4 * bp.P + 125 * bp.P ^ 6 := by
  have hP := h.hP
  have hwI := h.hwI
  have hwIn := h.hwIn
  have hwOut := h.hwOut
  have h1 : bp.R * (bp.wI + bp.wOut + 1) ≤ 6 * (bp.R * bp.P) := by
    calc bp.R * (bp.wI + bp.wOut + 1) ≤ bp.R * (6 * bp.P) := Nat.mul_le_mul_left _ (by omega)
      _ = 6 * (bp.R * bp.P) := by ring
  have h2 : bp.R ≤ bp.R * bp.P := Nat.le_mul_of_pos_right _ (by omega)
  have hS := h.hS
  unfold postCost eBound
  omega

/-- **Generic bound on `bridgeCost`**: exposures `3(d+1)·E` (`E = (X ℓ + 1)·R(2wI+1)`), volume
terms `O(d·R·P + R·P)`, the spreading line passes `spreadK·d·R·P·mLog(P²)`, the solver products
`d·R·mulW(wI+wT+1)`, and table scans/setup (polynomial). -/
theorem bridgeCost_le {X : ℕ → ℕ} (h : ParOK bp Rr r) :
    bridgeCost X bp ≤ 3 * ((bp.d + 1) * ((X (axisBits bp.t) + 1) * vol1 bp.R bp.wI)) +
      19 * (bp.d * (bp.R * bp.P)) + spreadK * (bp.d * (bp.R * bp.P * mLog (bp.P ^ 2))) +
      bp.d * (bp.R * mulW (bp.wI + bp.wT + 1)) + 14 * (bp.R * bp.P) + 8 * bp.P +
      bp.d * (bp.d * tapTabLen bp) + bp.d * (bp.d * solTabLen bp) +
      7 * (bp.d * (125 * bp.P ^ 6)) + 4 * (125 * bp.P ^ 6) := by
  have hS := h.hS
  have hpre := preCost_le h
  have hpost := postCost_le h
  have hsolve := solveCost_le h
  have hE : exposeCost X bp = (X (axisBits bp.t) + 1) * vol1 bp.R bp.wI + bp.setup := rfl
  have hreo : reorderCost X bp ≤ (bp.d + 1) * ((X (axisBits bp.t) + 1) * vol1 bp.R bp.wI) +
      bp.d * (125 * bp.P ^ 6) + 125 * bp.P ^ 6 := by
    unfold reorderCost
    rw [hE]
    calc (bp.d + 1) * ((X (axisBits bp.t) + 1) * vol1 bp.R bp.wI + bp.setup)
        ≤ (bp.d + 1) * ((X (axisBits bp.t) + 1) * vol1 bp.R bp.wI + 125 * bp.P ^ 6) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have hsum : ((spreadOrder bp.d).map fun i =>
      2 * exposeCost X bp + spreadCost bp i + bp.setup).sum ≤
      2 * (bp.d * ((X (axisBits bp.t) + 1) * vol1 bp.R bp.wI)) + 10 * (bp.d * (bp.R * bp.P)) +
        spreadK * (bp.d * (bp.R * bp.P * mLog (bp.P ^ 2))) + bp.d * (bp.d * tapTabLen bp) +
        4 * (bp.d * (125 * bp.P ^ 6)) := by
    refine le_trans (sum_map_le_mul _ _ (2 * ((X (axisBits bp.t) + 1) * vol1 bp.R bp.wI) +
      10 * (bp.R * bp.P) + spreadK * (bp.R * bp.P * mLog (bp.P ^ 2)) + bp.d * tapTabLen bp +
      4 * (125 * bp.P ^ 6)) ?_) ?_
    · intro i _
      have := spreadCost_le h i
      rw [hE]
      omega
    · rw [Tables.length_spreadOrder]
      calc (bp.d - 1) * (2 * ((X (axisBits bp.t) + 1) * vol1 bp.R bp.wI) +
            10 * (bp.R * bp.P) + spreadK * (bp.R * bp.P * mLog (bp.P ^ 2)) +
            bp.d * tapTabLen bp + 4 * (125 * bp.P ^ 6))
          ≤ bp.d * (2 * ((X (axisBits bp.t) + 1) * vol1 bp.R bp.wI) +
            10 * (bp.R * bp.P) + spreadK * (bp.R * bp.P * mLog (bp.P ^ 2)) +
            bp.d * tapTabLen bp + 4 * (125 * bp.P ^ 6)) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _ = _ := by ring
  have hsol' : bp.d * (solveCost bp + bp.setup) ≤ 9 * (bp.d * (bp.R * bp.P)) +
      bp.d * (bp.R * mulW (bp.wI + bp.wT + 1)) + bp.d * (bp.d * solTabLen bp) +
      2 * (bp.d * (125 * bp.P ^ 6)) := by
    calc bp.d * (solveCost bp + bp.setup) ≤ bp.d * (9 * (bp.R * bp.P) +
          bp.R * mulW (bp.wI + bp.wT + 1) + bp.d * solTabLen bp + 125 * bp.P ^ 6 +
          125 * bp.P ^ 6) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have hdE : bp.d * ((X (axisBits bp.t) + 1) * vol1 bp.R bp.wI) ≤
      (bp.d + 1) * ((X (axisBits bp.t) + 1) * vol1 bp.R bp.wI) :=
    Nat.mul_le_mul_right _ (Nat.le_succ _)
  unfold bridgeCost
  omega

end Generic

/-! ## 4. The pipe's parameters and the pointwise bound on `callCost` -/

/-- Numeric facts at the W8 root parameters (as in `eventually_w8_facts`) for a call precision
`pin ≤ P`. -/
structure Facts (b k pin : ℕ) : Prop where
  hk : 2 ^ 15 ≤ k
  hP16 : 16 * k ≤ PBK b k
  hP32 : PBK b k ≤ 32 * k
  hkb : k ≤ b
  hb2 : b ≤ 2 * k
  hd2 : 2 ≤ dK row46 k
  hdl : dK row46 k < lK row46 k
  hlk : lK row46 k ≤ k
  hpin : pin ≤ PBK b k

theorem par_P (b k pin : ℕ) :
    (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).P = PBK b k := rfl

theorem par_wI (b k pin : ℕ) :
    (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).wI = PBK b k + 2 * k + 16 := rfl

theorem par_wT (b k pin : ℕ) :
    (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).wT = PBK b k + 2 * k + 16 := rfl

theorem par_wIn (b k pin : ℕ) :
    (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).wIn =
      IntMul.rootPrecision b k + pin + 2 := rfl

theorem par_wOut (b k pin : ℕ) :
    (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).wOut =
      2 * IntMul.rootPrecision b k + k + 8 := rfl

theorem par_d {b k pin : ℕ} (hd : 1 ≤ dK row46 k) :
    (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).d = dK row46 k := by
  show fnewD row46 k + 1 = dK row46 k
  unfold fnewD
  omega

theorem par_R {b k pin : ℕ} (hd : 1 ≤ dK row46 k) (hl : 1 ≤ lK row46 k) :
    (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).R = 2 ^ k :=
  totalLen_fnewShape hd hl

theorem par_axisBits (b k pin : ℕ) :
    axisBits (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).t = lK row46 k :=
  axisBits_fnewShape k

theorem size_fnewShape_le {k : ℕ} (hlk : lK row46 k ≤ k) (i : Fin (fnewD row46 k + 1)) :
    Nat.size (fnewShape row46 k i) ≤ k + 1 := by
  apply Nat.size_le.2
  have h1 := fnewShape_le_rK k i
  have h2 : rK row46 k ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlk
  have h3 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- The bridge header of the call has `≤ P` entries of bit length `≤ 3P`, so
`|hdrSyms hdr| ≤ 4P²`. -/
theorem hdrLen_le {b k pin : ℕ} (h : Facts b k pin) :
    (hdrSyms (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).hdr).length ≤
      4 * PBK b k ^ 2 := by
  obtain ⟨hk, hP16, hP32, hkb, hb2, hd2, hdl, hlk, hpin⟩ := h
  have hPd : PBK b k = 2 * pBK b k + 12 * k + 32 * Nat.clog 2 (pBK b k + k + 2) + 256 := rfl
  have hpd : pBK b k = 2 * b + 2 * k + 6 := rfl
  have hrp : IntMul.rootPrecision b k = 2 * b + 2 * k + 6 := rfl
  have hfD : fnewD row46 k + 1 = dK row46 k := by unfold fnewD; omega
  have hlg : lg (fnewD row46 k + 1) ≤ k := by
    unfold lg
    have : Nat.clog 2 (fnewD row46 k + 1) ≤ fnewD row46 k + 1 :=
      Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    omega
  have hω : schedOmega (IntMul.rootPrecision b k) k (fnewD row46 k + 1) ≤ 3 * PBK b k := by
    unfold schedOmega; omega
  have hM : ∀ x ∈ (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).hdr,
      Nat.size x ≤ 3 * PBK b k := by
    apply hdr_size_le
    · exact ⟨by show IntMul.rootPrecision b k ≤ 3 * PBK b k; omega,
        by show PBK b k ≤ 3 * PBK b k; omega, hω,
        by show PBK b k + 2 * k + 16 ≤ 3 * PBK b k; omega,
        by show PBK b k + 2 * k + 16 ≤ 3 * PBK b k; omega,
        by show 2 * IntMul.rootPrecision b k + k + 8 ≤ 3 * PBK b k; omega,
        by show pin + 2 ≤ 3 * PBK b k; omega,
        by show IntMul.rootPrecision b k + pin + 2 ≤ 3 * PBK b k; omega,
        by show fnewD row46 k + 1 ≤ 3 * PBK b k; omega⟩
    · intro i
      have := size_fnewShape_le hlk i
      show Nat.size (fnewShape row46 k i) ≤ 3 * PBK b k
      omega
  have h1 := length_hdrSyms_le _ _ hM
  rw [length_hdr] at h1
  have h2 : 9 + (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).d ≤ PBK b k := by
    show 9 + (fnewD row46 k + 1) ≤ PBK b k
    omega
  have h3 : PBK b k * 1 ≤ PBK b k * PBK b k := Nat.mul_le_mul_left _ (by omega)
  have h4 : PBK b k * (3 * PBK b k + 1) = 3 * (PBK b k * PBK b k) + PBK b k * 1 := by ring
  have h5 : PBK b k ^ 2 = PBK b k * PBK b k := by ring
  have h6 := Nat.mul_le_mul_right (3 * PBK b k + 1) h2
  omega

theorem parOK_of_facts {b k pin : ℕ} (h : Facts b k pin) :
    ParOK (fnewPar fnewSched (IntMul.rootPrecision b k) k pin) (2 ^ k / rK row46 k)
      (rK row46 k) := by
  have hhdr := hdrLen_le h
  obtain ⟨hk, hP16, hP32, hkb, hb2, hd2, hdl, hlk, hpin⟩ := h
  have hd1 : 1 ≤ dK row46 k := by omega
  have hl1 : 1 ≤ lK row46 k := by omega
  have hPd : PBK b k = 2 * pBK b k + 12 * k + 32 * Nat.clog 2 (pBK b k + k + 2) + 256 := rfl
  have hpd : pBK b k = 2 * b + 2 * k + 6 := rfl
  have hrp : IntMul.rootPrecision b k = 2 * b + 2 * k + 6 := rfl
  have hfD : fnewD row46 k + 1 = dK row46 k := by unfold fnewD; omega
  have hlg : lg (fnewD row46 k + 1) ≤ k := by
    unfold lg
    have : Nat.clog 2 (fnewD row46 k + 1) ≤ fnewD row46 k + 1 :=
      Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    omega
  have hω : schedOmega (IntMul.rootPrecision b k) k (fnewD row46 k + 1) ≤ 3 * PBK b k := by
    unfold schedOmega; omega
  have hts : ∀ i : Fin (fnewD row46 k + 1), Nat.size (fnewShape row46 k i) + 4 ≤ PBK b k := by
    intro i
    have := size_fnewShape_le hlk i
    omega
  have hAt : ∀ i : Fin (fnewD row46 k + 1),
      Nat.size (2 * fnewShape row46 k i * prefixProd (fnewShape row46 k) i) + 4 ≤ PBK b k := by
    intro i
    have h1 := mul_prefixProd_le hd1 hl1 i
    have h2 : 2 * fnewShape row46 k i * prefixProd (fnewShape row46 k) i < 2 ^ (k + 2) := by
      have h3 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
      have h4 := Nat.two_pow_pos k
      have h5 : 2 * fnewShape row46 k i * prefixProd (fnewShape row46 k) i =
          2 * (fnewShape row46 k i * prefixProd (fnewShape row46 k) i) := by ring
      omega
    have h6 := Nat.size_le.2 h2
    omega
  have hP2 : 1 ≤ PBK b k ^ 2 := Nat.one_le_pow _ _ (by omega)
  exact {
    hP := by show 100 ≤ PBK b k; omega
    hdP := by show fnewD row46 k + 1 ≤ PBK b k; omega
    hwI := by show PBK b k + 2 * k + 16 ≤ 2 * PBK b k; omega
    hwT := by show PBK b k + 2 * k + 16 ≤ 2 * PBK b k; omega
    hwOut := by show 2 * IntMul.rootPrecision b k + k + 8 ≤ 3 * PBK b k; omega
    hwIn := by show IntMul.rootPrecision b k + pin + 2 ≤ 3 * PBK b k; omega
    hω := hω
    ht1 := fun i => one_le_fnewShape k i
    htr := fun i => fnewShape_le_rK k i
    hts := hts
    hA := fun i => prefixProd_le_div hd1 hl1 i
    hAt := hAt
    hS := by
      show ((hdrSyms (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).hdr).length + 1) ^ 3 ≤
        125 * PBK b k ^ 6
      calc ((hdrSyms (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).hdr).length + 1) ^ 3
          ≤ (5 * PBK b k ^ 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 125 * PBK b k ^ 6 := by ring }

/-- **Pointwise bound on one branch call** under `Facts`: `callCost` is at most the four sub-kernel
parts (`rpCost`, `Tmid`, twice the middle header) plus the exposure term, `d·V`, the spreading
term `d·V·mLog(P²)`, the solver products, `50·V` and `10^7·((2^k/r)·P^12 + r·P^12 + P^12)`. -/
theorem callCost_le {rpCost : ℕ → ℕ → ℕ → ℕ} {X : ℕ → ℕ} {md : MidData} {b k pin : ℕ}
    (h : Facts b k pin) :
    callCost rpCost X fnewSched md b k pin ≤
      rpCost b k pin + md.Tmid (IntMul.rootPrecision b k) k pin +
      2 * (hdrSyms (md.mhdr (IntMul.rootPrecision b k) k pin)).length +
      3 * ((dK row46 k + 1) * ((X (lK row46 k) + 1) * (2 ^ k * (2 * (PBK b k + 2 * k + 16) + 1)))) +
      19 * (dK row46 k * VBK b k) + spreadK * (dK row46 k * (VBK b k * mLog (PBK b k ^ 2))) +
      dK row46 k * (2 ^ k * mulW (PBK b k + 2 * k + 16 + (PBK b k + 2 * k + 16) + 1)) +
      50 * VBK b k +
      10000000 * (2 ^ k / rK row46 k * PBK b k ^ 12 + rK row46 k * PBK b k ^ 12 + PBK b k ^ 12) := by
  have hOK := parOK_of_facts h
  have hhdr := hdrLen_le h
  obtain ⟨hk, hP16, hP32, hkb, hb2, hd2, hdl, hlk, hpin⟩ := h
  have hd1 : 1 ≤ dK row46 k := by omega
  have hl1 : 1 ≤ lK row46 k := by omega
  have hP1 : 1 ≤ PBK b k := by omega
  have hdP : dK row46 k ≤ PBK b k := by omega
  have hrp : IntMul.rootPrecision b k = 2 * b + 2 * k + 6 := rfl
  have hPd : PBK b k = 2 * pBK b k + 12 * k + 32 * Nat.clog 2 (pBK b k + k + 2) + 256 := rfl
  have hpd : pBK b k = 2 * b + 2 * k + 6 := rfl
  have hVBK : 2 ^ k * PBK b k = VBK b k := rfl
  -- the bridge and the tables, at the concrete parameters
  have hB := bridgeCost_le (X := X) hOK
  rw [par_axisBits, par_R hd1 hl1, par_P, par_d hd1, par_wI, par_wT] at hB
  simp only [vol1] at hB
  rw [hVBK] at hB
  have hT := tabCost_le hOK
  rw [par_P] at hT
  have htap := tapTabLen_le hOK
  rw [par_P, par_d hd1] at htap
  have hsol := solTabLen_le hOK
  rw [par_P, par_d hd1] at hsol
  have hts := length_tapTabSyms_le (fnewPar fnewSched (IntMul.rootPrecision b k) k pin)
    (tabOf (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).ω
      (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).P
      (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).t)
  have hss := length_solTabSyms_eq (fnewPar fnewSched (IntMul.rootPrecision b k) k pin)
    (tabOf (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).ω
      (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).P
      (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).t)
  -- guard, conversions, small headers
  have hV : 2 ^ k * eb (4 * IntMul.rootPrecision b k) ≤ 9 * VBK b k := by
    have h1 : eb (4 * IntMul.rootPrecision b k) ≤ 9 * PBK b k := by unfold eb; omega
    calc 2 ^ k * eb (4 * IntMul.rootPrecision b k) ≤ 2 ^ k * (9 * PBK b k) :=
          Nat.mul_le_mul_left _ h1
      _ = 9 * VBK b k := by rw [← hVBK]; ring
  have hg : (2 ^ k + 1) * (IntMul.rootPrecision b k + pin + 2) ≤ 3 * VBK b k + 3 * PBK b k := by
    calc (2 ^ k + 1) * (IntMul.rootPrecision b k + pin + 2) ≤ (2 ^ k + 1) * (3 * PBK b k) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 3 * VBK b k + 3 * PBK b k := by rw [← hVBK]; ring
  have hwIn : (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).wIn ≤ 3 * PBK b k := by
    rw [par_wIn]; omega
  have hwOut : (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).wOut ≤ 3 * PBK b k := by
    rw [par_wOut]; omega
  have hgIn : 2 ^ k * ((fnewPar fnewSched (IntMul.rootPrecision b k) k pin).wIn + 1) ≤
      4 * VBK b k := by
    calc 2 ^ k * ((fnewPar fnewSched (IntMul.rootPrecision b k) k pin).wIn + 1)
        ≤ 2 ^ k * (4 * PBK b k) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * VBK b k := by rw [← hVBK]; ring
  have hgOut : 2 ^ k * ((fnewPar fnewSched (IntMul.rootPrecision b k) k pin).wOut + 1) ≤
      4 * VBK b k := by
    calc 2 ^ k * ((fnewPar fnewSched (IntMul.rootPrecision b k) k pin).wOut + 1)
        ≤ 2 ^ k * (4 * PBK b k) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * VBK b k := by rw [← hVBK]; ring
  have hhIn := length_hdrSyms_single (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).wIn
  have hhOut := length_hdrSyms_single (fnewPar fnewSched (IntMul.rootPrecision b k) k pin).wOut
  -- polynomial terms, all `≤ c·((2^k/r)·P^12 + r·P^12 + P^12)`
  have p12 : ∀ a, a ≤ 12 → PBK b k ^ a ≤ PBK b k ^ 12 := fun a ha => Nat.pow_le_pow_right hP1 ha
  have q1 : 2 ^ k / rK row46 k * PBK b k ^ 8 ≤ 2 ^ k / rK row46 k * PBK b k ^ 12 :=
    Nat.mul_le_mul_left _ (p12 8 (by norm_num))
  have q2 : rK row46 k * PBK b k ^ 6 ≤ rK row46 k * PBK b k ^ 12 :=
    Nat.mul_le_mul_left _ (p12 6 (by norm_num))
  have q3 := p12 4 (by norm_num)
  have q4 := p12 6 (by norm_num)
  have q5 := p12 2 (by norm_num)
  have q6 : PBK b k ≤ PBK b k ^ 12 := by simpa using p12 1 (by norm_num)
  have q7 : 1 ≤ PBK b k ^ 12 := Nat.one_le_pow _ _ hP1
  have q8 : tapTabLen (fnewPar fnewSched (IntMul.rootPrecision b k) k pin) ≤
      13 * (2 ^ k / rK row46 k * PBK b k ^ 12) + PBK b k ^ 12 := by
    have e1 := Nat.mul_le_mul_left (2 ^ k / rK row46 k) (p12 3 (by norm_num))
    calc tapTabLen (fnewPar fnewSched (IntMul.rootPrecision b k) k pin)
        ≤ dK row46 k * (13 * (2 ^ k / rK row46 k * PBK b k ^ 2) + 1) := htap
      _ ≤ PBK b k * (13 * (2 ^ k / rK row46 k * PBK b k ^ 2) + 1) := Nat.mul_le_mul_right _ hdP
      _ = 13 * (2 ^ k / rK row46 k * PBK b k ^ 3) + PBK b k := by ring
      _ ≤ 13 * (2 ^ k / rK row46 k * PBK b k ^ 12) + PBK b k ^ 12 := by omega
  have q9 : dK row46 k * (dK row46 k * tapTabLen (fnewPar fnewSched (IntMul.rootPrecision b k) k pin)) ≤
      13 * (2 ^ k / rK row46 k * PBK b k ^ 12) + PBK b k ^ 12 := by
    have e1 := Nat.mul_le_mul_left (2 ^ k / rK row46 k) (p12 5 (by norm_num))
    have e2 := p12 3 (by norm_num)
    calc dK row46 k * (dK row46 k * tapTabLen (fnewPar fnewSched (IntMul.rootPrecision b k) k pin))
        ≤ PBK b k * (PBK b k * (PBK b k * (13 * (2 ^ k / rK row46 k * PBK b k ^ 2) + 1))) :=
          Nat.mul_le_mul hdP (Nat.mul_le_mul hdP (le_trans htap (Nat.mul_le_mul_right _ hdP)))
      _ = 13 * (2 ^ k / rK row46 k * PBK b k ^ 5) + PBK b k ^ 3 := by ring
      _ ≤ 13 * (2 ^ k / rK row46 k * PBK b k ^ 12) + PBK b k ^ 12 := by omega
  have q10 : solTabLen (fnewPar fnewSched (IntMul.rootPrecision b k) k pin) ≤
      13 * (rK row46 k * PBK b k ^ 12) + PBK b k ^ 12 := by
    have e1 := Nat.mul_le_mul_left (rK row46 k) (p12 2 (by norm_num))
    calc solTabLen (fnewPar fnewSched (IntMul.rootPrecision b k) k pin)
        ≤ dK row46 k * (13 * (rK row46 k * PBK b k) + 1) := hsol
      _ ≤ PBK b k * (13 * (rK row46 k * PBK b k) + 1) := Nat.mul_le_mul_right _ hdP
      _ = 13 * (rK row46 k * PBK b k ^ 2) + PBK b k := by ring
      _ ≤ 13 * (rK row46 k * PBK b k ^ 12) + PBK b k ^ 12 := by omega
  have q11 : dK row46 k * (dK row46 k * solTabLen (fnewPar fnewSched (IntMul.rootPrecision b k) k pin)) ≤
      13 * (rK row46 k * PBK b k ^ 12) + PBK b k ^ 12 := by
    have e1 := Nat.mul_le_mul_left (rK row46 k) (p12 4 (by norm_num))
    have e2 := p12 3 (by norm_num)
    calc dK row46 k * (dK row46 k * solTabLen (fnewPar fnewSched (IntMul.rootPrecision b k) k pin))
        ≤ PBK b k * (PBK b k * (PBK b k * (13 * (rK row46 k * PBK b k) + 1))) :=
          Nat.mul_le_mul hdP (Nat.mul_le_mul hdP (le_trans hsol (Nat.mul_le_mul_right _ hdP)))
      _ = 13 * (rK row46 k * PBK b k ^ 4) + PBK b k ^ 3 := by ring
      _ ≤ 13 * (rK row46 k * PBK b k ^ 12) + PBK b k ^ 12 := by omega
  have q12 : dK row46 k * (125 * PBK b k ^ 6) ≤ 125 * PBK b k ^ 12 := by
    have e1 := p12 7 (by norm_num)
    calc dK row46 k * (125 * PBK b k ^ 6) ≤ PBK b k * (125 * PBK b k ^ 6) :=
          Nat.mul_le_mul_right _ hdP
      _ = 125 * PBK b k ^ 7 := by ring
      _ ≤ 125 * PBK b k ^ 12 := by omega
  dsimp only [callCost]
  omega

/-! ## 5. Eventual bounds -/

/-- `ℓ = lK row46 (w8K n) → ∞` (from `P ≤ r = 2^ℓ`, `eventually_w8_r_large`). -/
theorem eventually_lK_ge (L : ℕ) : ∀ᶠ n in atTop, L ≤ lK row46 (w8K n) := by
  filter_upwards [eventually_w8_r_large 1 1, tendsto_w8K.eventually_ge_atTop (2 ^ L),
    eventually_w8_facts] with n hr hk hf
  obtain ⟨-, hP16, -⟩ := hf
  have h1 : PBK (w8B n) (w8K n) ≤ 2 ^ lK row46 (w8K n) := by
    have := hr.1
    rw [one_mul, pow_one] at this
    exact this
  by_contra hc
  have h2 : 2 ^ lK row46 (w8K n) < 2 ^ L := Nat.pow_lt_pow_right (by norm_num) (not_le.1 hc)
  omega

/-- The constant of the per-call bound `eventually_callCost_le`. -/
def callConst (cR cX cM cH : ℕ) : ℕ :=
  cR + (4 * cM + cM * (2 * (cM + 1 + 0) * (mLog (cM + 1 + 0) + 1)) + 3 * cM) + 2 * cH +
    3 * (2 * (cX + 2 + 1) * (2 * (cX + 2) + 1)) + 19 + spreadK +
    2 * (4 + 1) * (mLog (4 + 1) + 1) + 50 + 30000000

/-- **Eventual bound on one branch call** at a call precision `pinF n` (`BranchPin`), from the
eventual bounds on the four sub-kernel parts. -/
theorem eventually_callCost_le (rpCost : ℕ → ℕ → ℕ → ℕ) (X : ℕ → ℕ) (md : MidData)
    (lam' tau : ℝ) (Dset cR jR cX cM jM cH jH : ℕ) (hjR : jR ≤ Dset) (hjM : jM ≤ Dset)
    (hjH : jH ≤ Dset) (h12 : 12 ≤ Dset) (pinF : ℕ → ℕ) (hpin : ∀ n, BranchPin n (pinF n))
    (hRP : ∀ᶠ n in atTop, ∀ pin, BranchPin n pin →
      rpCost (W8.hB n) (W8.hK0 n) pin ≤ cR * PBK (w8B n) (w8K n) ^ jR)
    (hX : ∀ᶠ n in atTop, X (lK row46 (w8K n)) ≤ cX * (1 + ⌈(lK row46 (w8K n) : ℝ) ^ tau⌉₊))
    (hMid : ∀ᶠ n in atTop, ∀ pin, BranchPin n pin →
      md.Tmid (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin ≤
        cM * VBK (w8B n) (w8K n) * (dK row46 (w8K n) * KK row46 (w8K n) +
          lK row46 (w8K n) * ⌈(dK row46 (w8K n) : ℝ) ^ lam'⌉₊ + lK row46 (w8K n) + 1) +
        cM * (lK row46 (w8K n) * (2 ^ w8K n * mulW ((cM + 1) * PBK (w8B n) (w8K n)))) +
        cM * (2 ^ w8K n / rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ jM +
          rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ jM + PBK (w8B n) (w8K n) ^ jM))
    (hMH : ∀ᶠ n in atTop, ∀ pin, BranchPin n pin →
      (hdrSyms (md.mhdr (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin)).length ≤
        cH * PBK (w8B n) (w8K n) ^ jH) :
    ∀ᶠ n in atTop, callCost rpCost X fnewSched md (W8.hB n) (W8.hK0 n) (pinF n) ≤
      callConst cR cX cM cH * walshCostNatW8 row46 lam' tau mLog Dset n := by
  filter_upwards [eventually_w8_facts, hRP, hX, hMid, hMH,
    eventually_expose_le_W lam' tau mLog Dset (cX + 2),
    eventually_dmulW_le_W lam' tau Dset 4 1,
    eventually_mid_le_W lam' tau Dset cM,
    eventually_lmulW_le_W lam' tau Dset (cM + 1) 0] with n hf hrp hxn hmd hmh hexp hdm hmid hlm
  obtain ⟨hk, hP16, hP32, hkb, hb2, hd2, hdl, hlk, -, -, hpP, -⟩ := hf
  have hpinP : pinF n ≤ PBK (w8B n) (w8K n) := by
    rcases hpin n with e | e
    · rw [e]
      show w8B n ≤ PBK (w8B n) (w8K n)
      omega
    · rw [e]
      exact hpP
  have hF : Facts (w8B n) (w8K n) (pinF n) := ⟨hk, hP16, hP32, hkb, hb2, hd2, hdl, hlk, hpinP⟩
  have h0 := callCost_le (rpCost := rpCost) (X := X) (md := md) hF
  have hP1 : 1 ≤ PBK (w8B n) (w8K n) := by omega
  have hW1 : PBK (w8B n) (w8K n) ^ Dset ≤ walshCostNatW8 row46 lam' tau mLog Dset n :=
    setup1_le_walshCostNatBK row46 lam' tau mLog Dset (w8B n) (w8K n) n
  have hWR : 2 ^ w8K n / rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ Dset ≤
      walshCostNatW8 row46 lam' tau mLog Dset n :=
    setupR_le_walshCostNatBK row46 lam' tau mLog Dset (w8B n) (w8K n) n
  have hWr : rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ Dset ≤
      walshCostNatW8 row46 lam' tau mLog Dset n :=
    setupr_le_walshCostNatBK row46 lam' tau mLog Dset (w8B n) (w8K n) n
  have hpow : ∀ j, j ≤ Dset → PBK (w8B n) (w8K n) ^ j ≤ PBK (w8B n) (w8K n) ^ Dset :=
    fun j hj => Nat.pow_le_pow_right hP1 hj
  have e1 : rpCost (w8B n) (w8K n) (pinF n) ≤ cR * walshCostNatW8 row46 lam' tau mLog Dset n :=
    le_trans (hrp _ (hpin n)) (Nat.mul_le_mul_left _ (le_trans (hpow jR hjR) hW1))
  have e2 : md.Tmid (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n) (pinF n) ≤
      4 * cM * walshCostNatW8 row46 lam' tau mLog Dset n +
        cM * (2 * (cM + 1 + 0) * (mLog (cM + 1 + 0) + 1) *
          walshCostNatW8 row46 lam' tau mLog Dset n) +
        cM * (walshCostNatW8 row46 lam' tau mLog Dset n +
          walshCostNatW8 row46 lam' tau mLog Dset n +
          walshCostNatW8 row46 lam' tau mLog Dset n) := by
    have a1 := hmd _ (hpin n)
    have a2 := hmid (cM * VBK (w8B n) (w8K n)) le_rfl
    have a3 : lK row46 (w8K n) * (2 ^ w8K n * mulW ((cM + 1) * PBK (w8B n) (w8K n))) ≤
        2 * (cM + 1 + 0) * (mLog (cM + 1 + 0) + 1) * walshCostNatW8 row46 lam' tau mLog Dset n :=
      hlm _ (le_trans (by norm_num) (Nat.mul_le_mul (show 1 ≤ cM + 1 by omega) hP1))
        (Nat.le_add_right _ _)
    have a4 : 2 ^ w8K n / rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ jM +
        rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ jM + PBK (w8B n) (w8K n) ^ jM ≤
        walshCostNatW8 row46 lam' tau mLog Dset n + walshCostNatW8 row46 lam' tau mLog Dset n +
          walshCostNatW8 row46 lam' tau mLog Dset n :=
      add_le_add (add_le_add (le_trans (Nat.mul_le_mul_left _ (hpow jM hjM)) hWR)
        (le_trans (Nat.mul_le_mul_left _ (hpow jM hjM)) hWr)) (le_trans (hpow jM hjM) hW1)
    have a3' := Nat.mul_le_mul_left cM a3
    have a4' := Nat.mul_le_mul_left cM a4
    change md.Tmid (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n) (pinF n) ≤ _ at a1
    omega
  have e3 : (hdrSyms (md.mhdr (IntMul.rootPrecision (w8B n) (w8K n)) (w8K n) (pinF n))).length ≤
      cH * walshCostNatW8 row46 lam' tau mLog Dset n :=
    le_trans (hmh _ (hpin n)) (Nat.mul_le_mul_left _ (le_trans (hpow jH hjH) hW1))
  have e4 := hexp (X (lK row46 (w8K n))) (PBK (w8B n) (w8K n) + 2 * w8K n + 16)
    (le_trans hxn (Nat.mul_le_mul_right _ (by omega)))
    (le_trans (show PBK (w8B n) (w8K n) + 2 * w8K n + 16 ≤ 2 * PBK (w8B n) (w8K n) by omega)
      (Nat.mul_le_mul_right _ (by omega)))
  have e5 : dK row46 (w8K n) * VBK (w8B n) (w8K n) ≤
      walshCostNatW8 row46 lam' tau mLog Dset n := by
    have a1 : dK row46 (w8K n) * (VBK (w8B n) (w8K n) * mLog (PBK (w8B n) (w8K n))) ≤
        walshCostNatW8 row46 lam' tau mLog Dset n :=
      dvol_mLog_le_walshCostNatBK row46 lam' tau Dset (w8B n) (w8K n) n
    have a2 : VBK (w8B n) (w8K n) ≤ VBK (w8B n) (w8K n) * mLog (PBK (w8B n) (w8K n)) :=
      Nat.le_mul_of_pos_right _ (one_le_mLog _)
    exact le_trans (Nat.mul_le_mul_left _ a2) a1
  have e6 : spreadK * (dK row46 (w8K n) * (VBK (w8B n) (w8K n) *
      mLog (PBK (w8B n) (w8K n) ^ 2))) ≤ spreadK * walshCostNatW8 row46 lam' tau mLog Dset n :=
    Nat.mul_le_mul_left _ (dvol_mLogsq_le_walshCostNatBK row46 lam' tau Dset (w8B n) (w8K n) n)
  have e7 : dK row46 (w8K n) * (2 ^ w8K n * mulW (PBK (w8B n) (w8K n) + 2 * w8K n + 16 +
      (PBK (w8B n) (w8K n) + 2 * w8K n + 16) + 1)) ≤
      2 * (4 + 1) * (mLog (4 + 1) + 1) * walshCostNatW8 row46 lam' tau mLog Dset n :=
    hdm _ (by omega) (by omega)
  have e8 : VBK (w8B n) (w8K n) ≤ walshCostNatW8 row46 lam' tau mLog Dset n :=
    vol_le_walshCostNatBK row46 lam' tau mLog Dset (w8B n) (w8K n) n (by omega)
  have e9 : 2 ^ w8K n / rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ 12 ≤
      walshCostNatW8 row46 lam' tau mLog Dset n :=
    le_trans (Nat.mul_le_mul_left _ (hpow 12 h12)) hWR
  have e10 : rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ 12 ≤
      walshCostNatW8 row46 lam' tau mLog Dset n :=
    le_trans (Nat.mul_le_mul_left _ (hpow 12 h12)) hWr
  have e11 : PBK (w8B n) (w8K n) ^ 12 ≤ walshCostNatW8 row46 lam' tau mLog Dset n :=
    le_trans (hpow 12 h12) hW1
  clear hW1 hWR hWr hpow hrp hmd hmh hexp hdm hmid hlm hxn
  generalize walshCostNatW8 row46 lam' tau mLog Dset n = W at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ⊢
  calc callCost rpCost X fnewSched md (W8.hB n) (W8.hK0 n) (pinF n)
      = callCost rpCost X fnewSched md (w8B n) (w8K n) (pinF n) := rfl
    _ ≤ cR * W + (4 * cM * W + cM * (2 * (cM + 1 + 0) * (mLog (cM + 1 + 0) + 1) * W) +
        cM * (W + W + W)) + 2 * (cH * W) +
        3 * (2 * (cX + 2 + 1) * (2 * (cX + 2) + 1) * W) + 19 * W + spreadK * W +
        2 * (4 + 1) * (mLog (4 + 1) + 1) * W + 50 * W + 10000000 * (W + W + W) := by omega
    _ = callConst cR cX cM cH * W := by unfold callConst; ring

end BranchCostAux

open BranchCostAux in
/-- **The Walsh cost clause of the branch**: `WalshCostClause (branchCost rpCost X fnewSched md)`
(with `m = mLog`, `A_m = 1`, `j_m = 1`), provided, eventually in `n` and at both call precisions
(`BranchPin`), the parameter kernel and the middle header cost `O(P^j)`, the interchange factor is
`X ℓ = O(1 + ℓ^τ)` for large `ℓ`, and the middle costs
`O(V·(dK + ℓ⌈d^{λ'}⌉₊ + ℓ + 1) + ℓ·2^k·mulW((c+1)P) + (2^k/r)·P^j + r·P^j + P^j)` (the shape of
`midCost`; `P = PBK`, `V = VBK`, `d = dK row46`, `ℓ = lK row46`, `K = KK row46`, `r = rK row46` at
`b = w8B n`, `k = w8K n`). -/
theorem walshCostClause_branchCost_of (rpCost : ℕ → ℕ → ℕ → ℕ) (X : ℕ → ℕ) (md : MidData)
    (hRP : ∃ c j : ℕ, ∀ᶠ n in atTop, ∀ pin, BranchPin n pin →
      rpCost (W8.hB n) (W8.hK0 n) pin ≤ c * PBK (w8B n) (w8K n) ^ j)
    (hX : ∃ c : ℕ, ∀ᶠ l in atTop,
      X l ≤ c * (1 + ⌈(l : ℝ) ^ ((Math.Cost.Row46.tau : ℚ) : ℝ)⌉₊))
    (hMid : ∃ c j : ℕ, ∀ᶠ n in atTop, ∀ pin, BranchPin n pin →
      md.Tmid (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin ≤
        c * VBK (w8B n) (w8K n) * (dK row46 (w8K n) * KK row46 (w8K n) +
          lK row46 (w8K n) * ⌈(dK row46 (w8K n) : ℝ) ^ ((Math.Cost.Row46.lam' : ℚ) : ℝ)⌉₊ +
          lK row46 (w8K n) + 1) +
        c * (lK row46 (w8K n) * (2 ^ w8K n * mulW ((c + 1) * PBK (w8B n) (w8K n)))) +
        c * (2 ^ w8K n / rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ j +
          rK row46 (w8K n) * PBK (w8B n) (w8K n) ^ j + PBK (w8B n) (w8K n) ^ j))
    (hMH : ∃ c j : ℕ, ∀ᶠ n in atTop, ∀ pin, BranchPin n pin →
      (hdrSyms (md.mhdr (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) (W8.hK0 n) pin)).length ≤
        c * PBK (w8B n) (w8K n) ^ j) :
    WalshCostClause (branchCost rpCost X fnewSched md) := by
  obtain ⟨cR, jR, hRP⟩ := hRP
  obtain ⟨cX, hX⟩ := hX
  obtain ⟨cM, jM, hMid⟩ := hMid
  obtain ⟨cH, jH, hMH⟩ := hMH
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.1 hX
  have hXn : ∀ᶠ n in atTop, X (lK row46 (w8K n)) ≤
      cX * (1 + ⌈(lK row46 (w8K n) : ℝ) ^ ((Math.Cost.Row46.tau : ℚ) : ℝ)⌉₊) := by
    filter_upwards [eventually_lK_ge L] with n hn
    exact hL _ hn
  have h1 := eventually_callCost_le rpCost X md ((Math.Cost.Row46.lam' : ℚ) : ℝ)
    ((Math.Cost.Row46.tau : ℚ) : ℝ) (jR + jM + jH + 12) cR jR cX cM jM cH jH (by omega)
    (by omega) (by omega) (by omega) W8.hB (fun n => Or.inl rfl) hRP hXn hMid hMH
  have h2 := eventually_callCost_le rpCost X md ((Math.Cost.Row46.lam' : ℚ) : ℝ)
    ((Math.Cost.Row46.tau : ℚ) : ℝ) (jR + jM + jH + 12) cR jR cX cM jM cH jH (by omega)
    (by omega) (by omega) (by omega) (fun n => IntMul.rootPrecision (W8.hB n) (W8.hK0 n))
    (fun n => Or.inr rfl) hRP hXn hMid hMH
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (h1.and h2)
  refine ⟨2 * callConst cR cX cM cH, mLog, 1, 1, jR + jM + jH + 12, N₀,
    fun N hN => mLog_le_logb hN, ?_⟩
  intro n cSpec hn _
  obtain ⟨e1, e2⟩ := hN₀ n hn
  have e2' : callCost rpCost X fnewSched md (W8.hB n) (W8.hK0 n)
      (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) ≤ callConst cR cX cM cH *
      walshCostNatW8 row46 ((Math.Cost.Row46.lam' : ℚ) : ℝ) ((Math.Cost.Row46.tau : ℚ) : ℝ) mLog
        (jR + jM + jH + 12) n := e2
  have hb : branchCost rpCost X fnewSched md n cSpec ≤
      2 * callConst cR cX cM cH * walshCostNatW8 row46 ((Math.Cost.Row46.lam' : ℚ) : ℝ)
        ((Math.Cost.Row46.tau : ℚ) : ℝ) mLog (jR + jM + jH + 12) n := by
    show callCost rpCost X fnewSched md (W8.hB n) (W8.hK0 n) (W8.hB n) +
      callCost rpCost X fnewSched md (W8.hB n) (W8.hK0 n)
        (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) ≤ _
    linarith [add_le_add e1 e2']
  exact le_trans hb (Nat.le_add_right _ _)

end SubNLogN.Machine.Pipe
