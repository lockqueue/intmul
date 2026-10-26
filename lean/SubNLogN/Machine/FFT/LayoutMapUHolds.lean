/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.LayoutMapUBody

/-!
# K4.3c-U (`Machine/FFT/LayoutMapUHolds.lean`): `LayoutMapGenStmt .U` proved

The builder `progU` of the runtime map of the layout `U = (L ∘ B)^{-1}` (`LayoutMapGenStmt .U`,
`Machine/FFT/LayoutCompile.lean`): read the five leading header fields; pass 1 over the axis
exponents (`m₀ = Σ a_i`, by `bd1` of `Machine/FFT/LayoutMapL.lean`); restore the header; the
constants `ℓ - 1`, `J_blk = (ℓ - 1) / K`, `b₀ = (ℓ - 1) % K` (one `divModNat`); the long-slot pass,
the prefix-round loop and the chunk loop of `Machine/FFT/LayoutMapUBody.lean`, which emit `genU`
onto the scratch stack `so`; restore the five leading fields; move the emitted fields onto the
destination (`hdrSyms`, first value on top); drop the scratch numbers. `genU_eq`
(`Machine/FFT/LayoutMapMath.lean`) and `ofFn_layoutU` identify the emitted list with
`permSyms (layoutMap .U ℓ K a)`. `layoutMapGen_U_holds : LayoutMapGenStmt .U` is proved from the
proved contracts `W3_copyNat`, `W3_dropNat`, `W3_isZeroNat`, `W3_decNat`, `W3_incNat`, `W3_addNat`,
`W3_cmpNat`, `W3_subNat` and `W6a_divModNat` only (exponent `J = 4`). Fully proved, no placeholders.
-/

namespace SubNLogN.Machine.FFT.LayoutMapUAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.FFT.LayoutHdrAux (savedF savedF_nil savedF_concat natSyms_zero'
  hdrSyms_cons' hdrSyms_nil' midHdr_eq' opY cost1_le cost2_le one_le_opY bitLen_le
  loopCost_le_of_le sum_take_le' take_succ_sum' drop_hdr' savedF_take_succ' C_le_opY hdr_assoc)
open SubNLogN.Machine.FFT.LayoutMapMath SubNLogN.Math.Walsh.IntForms
open SubNLogN.Machine.FFT.LayoutMapAux

/-! ## Records of the builder of `U` -/

/-- The initial record: header `H`, destination `P`, all scratch stacks empty. -/
def U0 (H P : List Sym) : MS :=
  ⟨H, P, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    []⟩

/-- After reading the five leading header fields. -/
def UA (H P : List Sym) (q D ℓ K w : ℕ) : MS :=
  {U0 H P with q := natSyms q, D := natSyms D, l := natSyms ℓ, K := natSyms K, w := natSyms w}

/-- The records of pass 1 (`j` exponents processed). -/
def UR1 (H P : List Sym) (q D ℓ K w : ℕ) (as : List ℕ) (j : ℕ) : MS :=
  {UA H P q D ℓ K w with m := natSyms ((as.take j).sum), lc := natSyms ((as.take j).count ℓ)}

/-- After pass 1, the restore, and the constants `ℓ - 1`, `J_blk`, `b₀`. -/
def UC (H P : List Sym) (q D ℓ K w : ℕ) (as : List ℕ) : MS :=
  {UR1 H P q D ℓ K w as D with
    L1 := natSyms (ℓ - 1), J := natSyms ((ℓ - 1) / K), b := natSyms ((ℓ - 1) % K)}

/-- The header with its five leading fields. -/
def fullH (q D ℓ K w : ℕ) (H : List Sym) : List Sym :=
  natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
    (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: H))))

theorem tcount_succ (as : List ℕ) (j ℓ : ℕ) (hj : j < as.length) :
    (as.take (j + 1)).count ℓ = (as.take j).count ℓ + if as[j] = ℓ then 1 else 0 := by
  rw [List.take_succ_eq_append_getElem hj, List.count_append]
  by_cases h : as[j] = ℓ <;> simp [h]

theorem tcount_le (as : List ℕ) (j ℓ : ℕ) : (as.take j).count ℓ ≤ j := by
  refine le_trans List.count_le_length ?_
  rw [List.length_take]; exact Nat.min_le_left _ _

/-- The shape facts used by the bounds. -/
theorem shapeFactsU {q ℓ K w D : ℕ} {a : Fin D → ℕ} (hsh : MidShapeOK q ℓ K w a) :
    0 < K ∧ 2 ≤ ℓ ∧ K ≤ ℓ - 1 ∧ ℓ < q ∧ q + 2 ≤ w ∧ D ≤ addrBits a ∧ (ℓ - 1) / K ≤ ℓ ∧
    (ℓ - 1) % K < K ∧ (ℓ - 1) / K * K ≤ ℓ - 1 ∧
    (∀ x ∈ List.ofFn a, x = ℓ - 1 ∨ x = ℓ) ∧ (List.ofFn a).length = D := by
  obtain ⟨hq8, hD1, hl2, hlq, hK1, hKl, ha, hqw⟩ := hsh
  have hmem : ∀ x ∈ List.ofFn a, x = ℓ - 1 ∨ x = ℓ := by
    intro x hx; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact ha i
  have hK0 : 0 < K := by omega
  exact ⟨hK0, hl2, hKl, hlq, hqw, FFT.LayoutAux.le_addrBits hl2 ha,
    le_trans (Nat.div_le_self _ _) (by omega), Nat.mod_lt _ hK0, Nat.div_mul_le_self _ _, hmem,
    List.length_ofFn⟩

theorem zc_polyU (Cs Bm : ℕ) (hBm : 1 ≤ Bm) :
    Zc Cs (8 * Bm) 3 ≤ 6561 * (2 * Cs + 2) * Bm ^ 4 := by
  unfold Zc SubNLogN.Machine.FFT.LayoutHdrAux.opY
  have h1 : 8 * Bm + 1 ≤ 9 * Bm := by omega
  have h2 : (8 * Bm + 1) ^ 3 ≤ (9 * Bm) ^ 3 := Nat.pow_le_pow_left h1 3
  have h0 : Cs ≤ Cs * Bm := Nat.le_mul_of_pos_right _ hBm
  have h3 : Cs * (2 * (8 * Bm) + 1) + 2 * (8 * Bm) + 2 ≤ (2 * Cs + 2) * (9 * Bm) := by
    nlinarith
  calc (8 * Bm + 1) ^ 3 * (Cs * (2 * (8 * Bm) + 1) + 2 * (8 * Bm) + 2)
      ≤ (9 * Bm) ^ 3 * ((2 * Cs + 2) * (9 * Bm)) := Nat.mul_le_mul h2 h3
    _ = 6561 * (2 * Cs + 2) * Bm ^ 4 := by ring

section Consts

variable {I : HI} {C : ℕ}

/-- The constants `ℓ - 1`, `J_blk`, `b₀` (one `divModNat`). -/
def constsU (I : HI) : HP I := (hcp I vl sL1).seq ((hdc I sL1).seq (hdm I sL1 vK vJ vb))

theorem ht_constsU (hI : I.Spec C) (M : MS) (ℓ K B : ℕ) (hl : M.l = natSyms ℓ)
    (hK : M.K = natSyms K) (hL1 : M.L1 = []) (hJ : M.J = []) (hb : M.b = []) (hl1 : 1 ≤ ℓ)
    (hK0 : 0 < K) (hlB : ℓ ≤ B) (hKB : K ≤ B) :
    HT [] (toF M) (constsU I)
      (toF {M with
        L1 := natSyms (ℓ - 1), J := natSyms ((ℓ - 1) / K), b := natSyms ((ℓ - 1) % K)})
      (3 * Zc C B 1) := by
  unfold constsU
  refine HT.of_eq ((ht_cp0 hI vl sL1 (by decide) (toF M) ℓ [] TermOK.nil
      (by simp [toF, hl]) (by simp [toF, hL1])).seq
     ((ht_dc hI sL1 _ (ℓ - 1) [] TermOK.nil (by simp [Nat.sub_add_cancel hl1])).seq
     (ht_dm0 hI sL1 vK vJ vb (by decide) _ (ℓ - 1) K [] [] hK0 TermOK.nil TermOK.nil
       (by simp) (by simp [toF, hK]) (by simp [toF, hJ]) (by simp [toF, hb])))) ?_ ?_
  · simp only [upd_L1, upd_J, upd_b, List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le hlB)
    have c2 := cost_dc_le (C := C) (B := B) (k := ℓ - 1) (by omega)
    have c3 := cost_dm_le (C := C) (bitLen_le (show ℓ - 1 ≤ B by omega)) (bitLen_le hKB)
    have h3 := opY_le_Zc C B 1
    omega

/-- Drop the five leading header numbers. -/
def cleanU1 (I : HI) : HP I :=
  (hdr I vq).seq ((hdr I vD).seq ((hdr I vl).seq ((hdr I vK).seq (hdr I vw))))

/-- Drop the remaining scratch numbers. -/
def cleanU2 (I : HI) : HP I :=
  (hdr I vm).seq ((hdr I slc).seq ((hdr I sL1).seq ((hdr I vJ).seq (hdr I vb))))

theorem ht_cleanU1 (hI : I.Spec C) (M : MS) (q D ℓ K w B : ℕ)
    (h1 : M.q = natSyms q) (h2 : M.D = natSyms D) (h3 : M.l = natSyms ℓ) (h4 : M.K = natSyms K)
    (h5 : M.w = natSyms w) (b1 : q ≤ B) (b2 : D ≤ B) (b3 : ℓ ≤ B) (b4 : K ≤ B) (b5 : w ≤ B) :
    HT [] (toF M) (cleanU1 I) (toF {M with q := [], D := [], l := [], K := [], w := []})
      (5 * opY C B) := by
  unfold cleanU1
  refine HT.of_eq
    ((ht_dr hI vq _ q [] TermOK.nil (by simp [toF, h1])).seq
    ((ht_dr hI vD _ D [] TermOK.nil (by simp [toF, h2])).seq
    ((ht_dr hI vl _ ℓ [] TermOK.nil (by simp [toF, h3])).seq
    ((ht_dr hI vK _ K [] TermOK.nil (by simp [toF, h4])).seq
    (ht_dr hI vw _ w [] TermOK.nil (by simp [toF, h5])))))) ?_ ?_
  · simp only [upd_q, upd_D, upd_l, upd_K, upd_w]
  · have c1 := cost1_le (C := C) (bitLen_le b1)
    have c2 := cost1_le (C := C) (bitLen_le b2)
    have c3 := cost1_le (C := C) (bitLen_le b3)
    have c4 := cost1_le (C := C) (bitLen_le b4)
    have c5 := cost1_le (C := C) (bitLen_le b5)
    omega

theorem ht_cleanU2 (hI : I.Spec C) (M : MS) (m lc L1 J b B : ℕ)
    (h1 : M.m = natSyms m) (h2 : M.lc = natSyms lc) (h3 : M.L1 = natSyms L1)
    (h4 : M.J = natSyms J) (h5 : M.b = natSyms b) (b1 : m ≤ B) (b2 : lc ≤ B) (b3 : L1 ≤ B)
    (b4 : J ≤ B) (b5 : b ≤ B) :
    HT [] (toF M) (cleanU2 I) (toF {M with m := [], lc := [], L1 := [], J := [], b := []})
      (5 * opY C B) := by
  unfold cleanU2
  refine HT.of_eq
    ((ht_dr hI vm _ m [] TermOK.nil (by simp [toF, h1])).seq
    ((ht_dr hI slc _ lc [] TermOK.nil (by simp [toF, h2])).seq
    ((ht_dr hI sL1 _ L1 [] TermOK.nil (by simp [toF, h3])).seq
    ((ht_dr hI vJ _ J [] TermOK.nil (by simp [toF, h4])).seq
    (ht_dr hI vb _ b [] TermOK.nil (by simp [toF, h5])))))) ?_ ?_
  · simp only [upd_m, upd_lc, upd_L1, upd_J, upd_b]
  · have c1 := cost1_le (C := C) (bitLen_le b1)
    have c2 := cost1_le (C := C) (bitLen_le b2)
    have c3 := cost1_le (C := C) (bitLen_le b3)
    have c4 := cost1_le (C := C) (bitLen_le b4)
    have c5 := cost1_le (C := C) (bitLen_le b5)
    omega

end Consts

/-! ## The builder of `U` -/

/-- Stage 1: the five leading fields, pass 1 (`m₀`), restore, the constants. -/
def progU1 (I : HI) : HP I := (blockA I).seq ((passB I (bd1 I)).seq ((passC I).seq (constsU I)))

/-- Stage 2: the long slots, then the prefix rounds. -/
def progU2 (I : HI) : HP I := (passU I (bdU1 I)).seq (loopV I)

/-- Stage 4: the leading fields back, the final move, the drops. -/
def progU4 (I : HI) : HP I := (blockD I).seq ((moveO I).seq ((cleanU1 I).seq (cleanU2 I)))

/-- **The builder of the runtime map of `U`.** -/
def progU (I : HI) : HP I := (progU1 I).seq ((progU2 I).seq ((loopJ I).seq (progU4 I)))

theorem closed_progU {I : HI} : (progU I).Closed := by
  unfold progU progU1 progU2 progU4 loopJ blockA blockD constsU cleanU1 cleanU2 loopV bodyJ
    pDecK passU bdU1 bdU2 bdU3 pInnerD bd1
  repeat' (first
    | exact closed_passC
    | exact closed_moveO
    | refine closed_passB _ ?_
    | exact closed_rdF _ _
    | exact closed_wrF _ _ _
    | exact closed_addTo _ _ _
    | refine closed_hifEq _ _ _ _ _ ?_ ?_
    | refine closed_hcd _ _ _ ?_
    | exact callI_closed _ _ _ _
    | exact trivial
    | refine WP.W9comp.closed_seq ?_ ?_)

section MainU

variable {I : HI} {C : ℕ}

theorem ht_progU1 (hI : I.Spec C) (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest prest : List Sym)
    (hsh : MidShapeOK q ℓ K w a) :
    HT [] (toF (U0 (fullH q D ℓ K w (hdrSyms (List.ofFn a) ++ hrest)) prest)) (progU1 I)
      (toF (UC (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a)))
      (50 * Zc C (8 * (w + addrBits a + 1)) 1) := by
  obtain ⟨hK0, hl2, hKl, hlq, hqw, hDm, hJl, hbK, hJK, hmem, hlen⟩ := shapeFactsU hsh
  have hxB : ∀ x ∈ List.ofFn a, x ≤ 8 * (w + addrBits a + 1) := by
    intro x hx; rcases hmem x hx with h | h <;> omega
  have hbd1 : ∀ j (hj : j < (List.ofFn a).length) (i : ℕ), HT []
      (toF {UR1 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) j with
        h := natSyms (List.ofFn a)[j] ++ Sym.mark ::
          (hdrSyms ((List.ofFn a).drop (j + 1)) ++ hrest),
        A := natSyms (List.ofFn a)[j], s := savedF ((List.ofFn a).take j),
        c := natSyms i ++ []}) (bd1 I)
      (toF {UR1 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) (j + 1) with
        h := natSyms (List.ofFn a)[j] ++ Sym.mark ::
          (hdrSyms ((List.ofFn a).drop (j + 1)) ++ hrest),
        A := natSyms (List.ofFn a)[j], s := savedF ((List.ofFn a).take j),
        c := natSyms i ++ []}) (10 * opY C (8 * (w + addrBits a + 1))) := by
    intro j hj i
    have hxj := hmem _ (List.getElem_mem hj)
    have hs1 : ((List.ofFn a).take (j + 1)).sum ≤ addrBits a := sum_take_le' _ _
    rw [tsum_succ _ j hj] at hs1
    have hc1 := tcount_le (List.ofFn a) j ℓ
    refine HT.of_eq (ht_bd1 hI _ (List.ofFn a)[j] ℓ (((List.ofFn a).take j).sum)
      (((List.ofFn a).take j).count ℓ) (8 * (w + addrBits a + 1)) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rcases hxj with h | h <;> omega) (by omega) (by omega) (by omega))
      ?_ le_rfl
    unfold UR1
    rw [tsum_succ _ j hj, tcount_succ _ j ℓ hj]
    rfl
  unfold progU1
  refine HT.of_eq
    ((HT.of_eq (ht_blockA hI _ q D ℓ K w (8 * (w + addrBits a + 1))
        (hdrSyms (List.ofFn a) ++ hrest) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by omega) (by omega) (by omega) (by omega) (by omega)) rfl le_rfl).seq
    ((ht_passB hI (bd1 I) (List.ofFn a) D (8 * (w + addrBits a + 1))
        (10 * opY C (8 * (w + addrBits a + 1))) hrest
        (UR1 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a)) hlen (by omega) hxB
        rfl hbd1).seq
    ((ht_passC hI {UR1 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) D with
        A := [], c := []} (List.ofFn a) D (8 * (w + addrBits a + 1)) hrest hlen (by omega) hxB
        rfl rfl).seq
    (ht_constsU hI _ ℓ K (8 * (w + addrBits a + 1)) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by omega) hK0 (by omega) (by omega))))) rfl ?_
  have k1 : ((8 * (w + addrBits a + 1)) + 1) * (10 * opY C (8 * (w + addrBits a + 1)) +
      10 * opY C (8 * (w + addrBits a + 1))) = 20 * Zc C (8 * (w + addrBits a + 1)) 1 := by
    simp only [Zc]; ring
  have k2 : ((8 * (w + addrBits a + 1)) + 1) * (8 * opY C (8 * (w + addrBits a + 1))) =
      8 * Zc C (8 * (w + addrBits a + 1)) 1 := by
    simp only [Zc]; ring
  have m1 := opY_le_Zc C (8 * (w + addrBits a + 1)) 1
  omega

theorem ht_progU2 (hI : I.Spec C) (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest prest : List Sym)
    (hsh : MidShapeOK q ℓ K w a) :
    HT [] (toF (UC (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a))) (progU2 I)
      (toF {UC (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) with
        o := savedF (genU1 ℓ (List.ofFn a) ++
          (List.range ((ℓ - 1) % K)).reverse.flatMap (genU2 (List.ofFn a)))})
      (70 * Zc C (8 * (w + addrBits a + 1)) 2) := by
  obtain ⟨hK0, hl2, hKl, hlq, hqw, hDm, hJl, hbK, hJK, hmem, hlen⟩ := shapeFactsU hsh
  have hsum : (List.ofFn a).sum = addrBits a := rfl
  have hxB : ∀ x ∈ List.ofFn a, x ≤ 8 * (w + addrBits a + 1) := by
    intro x hx; rcases hmem x hx with h | h <;> omega
  unfold progU2
  refine HT.of_eq
    ((ht_pass1U hI _ (List.ofFn a) D ℓ (8 * (w + addrBits a + 1)) [] hrest hlen (by omega) hxB
        (by omega) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by rfl) (by rfl) (by rfl)).seq
    (ht_loopV hI _ (List.ofFn a) D ((ℓ - 1) % K) (8 * (w + addrBits a + 1))
        (genU1 ℓ (List.ofFn a)) hrest hlen (by omega) hxB (by omega) (by omega) (by rfl)
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl))) rfl ?_
  have k : ((8 * (w + addrBits a + 1)) + 1) * (12 * opY C (8 * (w + addrBits a + 1)) +
      19 * opY C (8 * (w + addrBits a + 1))) = 31 * Zc C (8 * (w + addrBits a + 1)) 1 := by
    simp only [Zc]; ring
  have m2 : Zc C (8 * (w + addrBits a + 1)) 1 ≤ Zc C (8 * (w + addrBits a + 1)) 2 :=
    Zc_mono _ _ 1
  omega

theorem ht_progU3 (hI : I.Spec C) (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest prest : List Sym)
    (hsh : MidShapeOK q ℓ K w a) :
    HT [] (toF {UC (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) with
        o := savedF (genU1 ℓ (List.ofFn a) ++
          (List.range ((ℓ - 1) % K)).reverse.flatMap (genU2 (List.ofFn a)))}) (loopJ I)
      (toF {UC (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) with
        o := savedF (genU ℓ K ((ℓ - 1) % K) ((ℓ - 1) / K) (List.ofFn a))})
      (45 * Zc C (8 * (w + addrBits a + 1)) 3) := by
  obtain ⟨hK0, hl2, hKl, hlq, hqw, hDm, hJl, hbK, hJK, hmem, hlen⟩ := shapeFactsU hsh
  have hsum : (List.ofFn a).sum = addrBits a := rfl
  have hxB : ∀ x ∈ List.ofFn a, x ≤ 8 * (w + addrBits a + 1) := by
    intro x hx; rcases hmem x hx with h | h <;> omega
  exact HT.of_eq (ht_loopJ hI _ (List.ofFn a) D ℓ K ((ℓ - 1) / K) (8 * (w + addrBits a + 1))
    (genU1 ℓ (List.ofFn a) ++ (List.range ((ℓ - 1) % K)).reverse.flatMap (genU2 (List.ofFn a)))
    hrest hlen (by omega) hxB (by omega) (by omega) (by omega) (by omega) hJK (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl)) rfl le_rfl

theorem ht_progU4 (hI : I.Spec C) (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest prest : List Sym)
    (hsh : MidShapeOK q ℓ K w a) :
    HT [] (toF {UC (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) with
        o := savedF (genU ℓ K ((ℓ - 1) % K) ((ℓ - 1) / K) (List.ofFn a))}) (progU4 I)
      (toF (U0 (fullH q D ℓ K w (hdrSyms (List.ofFn a) ++ hrest))
        (hdrSyms (genU ℓ K ((ℓ - 1) % K) ((ℓ - 1) / K) (List.ofFn a)) ++ prest)))
      (30 * Zc C (8 * (w + addrBits a + 1)) 1) := by
  obtain ⟨hK0, hl2, hKl, hlq, hqw, hDm, hJl, hbK, hJK, hmem, hlen⟩ := shapeFactsU hsh
  have hsD : ((List.ofFn a).take D).sum ≤ addrBits a := sum_take_le' _ _
  have hcD : ((List.ofFn a).take D).count ℓ ≤ D := tcount_le _ _ _
  have ha : ∀ i, a i = ℓ - 1 ∨ a i = ℓ := fun i => hmem _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  have hgen : genU ℓ K ((ℓ - 1) % K) ((ℓ - 1) / K) (List.ofFn a) = layoutUList ℓ K a :=
    genU_eq ℓ K a hK0
  have hLlen : (genU ℓ K ((ℓ - 1) % K) ((ℓ - 1) / K) (List.ofFn a)).length =
      ((List.ofFn a).take D).sum := by
    rw [hgen, List.take_of_length_le (le_of_eq hlen), layoutUList, List.length_map,
      LayoutPermAux.length_newSlots ℓ K a hK0 (by omega) ha]
    rfl
  have hLB : ∀ x ∈ genU ℓ K ((ℓ - 1) % K) ((ℓ - 1) / K) (List.ofFn a),
      x ≤ 8 * (w + addrBits a + 1) := by
    intro x hx
    rw [hgen, ← ofFn_layoutU ℓ K a hK0 hl2 ha] at hx
    obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hx
    have := (layoutU ℓ K a p).isLt
    omega
  unfold progU4
  refine HT.of_eq
    ((ht_blockD hI _ q D ℓ K w (8 * (w + addrBits a + 1)) (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by omega) (by omega) (by omega) (by omega) (by omega)).seq
    ((ht_moveO hI {UC (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) with
        o := savedF (genU ℓ K ((ℓ - 1) % K) ((ℓ - 1) / K) (List.ofFn a)),
        h := fullH q D ℓ K w (hdrSyms (List.ofFn a) ++ hrest)}
        _ (((List.ofFn a).take D).sum) (8 * (w + addrBits a + 1)) prest hLlen (by omega) hLB
        rfl rfl).seq
    ((ht_cleanU1 hI _ q D ℓ K w (8 * (w + addrBits a + 1)) (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by omega) (by omega) (by omega) (by omega) (by omega)).seq
    (ht_cleanU2 hI _ (((List.ofFn a).take D).sum) (((List.ofFn a).take D).count ℓ) (ℓ - 1)
        ((ℓ - 1) / K) ((ℓ - 1) % K) (8 * (w + addrBits a + 1)) (by rfl) (by rfl) (by rfl)
        (by rfl) (by rfl) (by omega) (by omega) (by omega) (by omega) (by omega))))) rfl ?_
  have k2 : ((8 * (w + addrBits a + 1)) + 1) * (8 * opY C (8 * (w + addrBits a + 1))) =
      8 * Zc C (8 * (w + addrBits a + 1)) 1 := by
    simp only [Zc]; ring
  have m1 := opY_le_Zc C (8 * (w + addrBits a + 1)) 1
  omega

theorem ht_progU (hI : I.Spec C) (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest prest : List Sym)
    (hsh : MidShapeOK q ℓ K w a) :
    HT [] (toF (U0 (midHdr q ℓ K w a ++ hrest) prest)) (progU I)
      (toF (U0 (midHdr q ℓ K w a ++ hrest) (hdrSyms (layoutUList ℓ K a) ++ prest)))
      (200 * Zc C (8 * (w + addrBits a + 1)) 3) := by
  obtain ⟨hK0, -, -, -, -, -, -, -, -, -, -⟩ := shapeFactsU hsh
  have hgen : genU ℓ K ((ℓ - 1) % K) ((ℓ - 1) / K) (List.ofFn a) = layoutUList ℓ K a :=
    genU_eq ℓ K a hK0
  have hhdr : midHdr q ℓ K w a ++ hrest = fullH q D ℓ K w (hdrSyms (List.ofFn a) ++ hrest) := by
    rw [midHdr_eq', hdr_assoc]
    rfl
  rw [hhdr, ← hgen]
  unfold progU
  refine HT.mono ((ht_progU1 hI q ℓ K w D a hrest prest hsh).seq
    ((ht_progU2 hI q ℓ K w D a hrest prest hsh).seq
    ((ht_progU3 hI q ℓ K w D a hrest prest hsh).seq
    (ht_progU4 hI q ℓ K w D a hrest prest hsh)))) ?_
  have m2 : Zc C (8 * (w + addrBits a + 1)) 1 ≤ Zc C (8 * (w + addrBits a + 1)) 2 :=
    Zc_mono _ _ 1
  have m3 : Zc C (8 * (w + addrBits a + 1)) 2 ≤ Zc C (8 * (w + addrBits a + 1)) 3 :=
    Zc_mono _ _ 2
  omega

end MainU

end SubNLogN.Machine.FFT.LayoutMapUAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Math.Walsh
open SubNLogN.Math.Walsh.IntForms SubNLogN.Machine.FFT.LayoutMapAux
  SubNLogN.Machine.FFT.LayoutMapUAux

/-- **K4.3c for `U` proved: the runtime map of the layout `U` from the middle header**
(exponent `J = 4`), from the proved W3 contracts and `W6a_divModNat` only. Fully proved, no placeholders. -/
theorem layoutMapGen_U_holds : LayoutMapGenStmt .U := by
  obtain ⟨C1, h1⟩ := exists_inst WP.W3.W3_copyNat_holds
  obtain ⟨Icp, hIcp⟩ := h1 ()
  obtain ⟨C2, h2⟩ := exists_inst WP.W3.W3_dropNat_holds
  obtain ⟨Idr, hIdr⟩ := h2 ()
  obtain ⟨C3, h3⟩ := exists_inst WP.W3.W3_isZeroNat_holds
  obtain ⟨Iiz, hIiz⟩ := h3 ()
  obtain ⟨C4, h4⟩ := exists_inst WP.W3.W3_decNat_holds
  obtain ⟨Idc, hIdc⟩ := h4 ()
  obtain ⟨C5, h5⟩ := exists_inst WP.W3.W3_incNat_holds
  obtain ⟨Iic, hIic⟩ := h5 ()
  obtain ⟨C6, h6⟩ := exists_inst WP.W3.W3_addNat_holds
  obtain ⟨Iad, hIad⟩ := h6 ()
  obtain ⟨C7, h7⟩ := exists_inst WP.W3.W3_cmpNat_holds
  obtain ⟨Icm, hIcm⟩ := h7 ()
  obtain ⟨C8, h8⟩ := exists_inst (WP.W6a.W6a_divModNat_holds WP.W3.W3_subNat_holds)
  obtain ⟨Idm, hIdm⟩ := h8 ()
  have s1 : SpecCopy Icp C1 := hIcp
  have s2 : SpecDrop Idr C2 := hIdr
  have s3 : SpecIsZero Iiz C3 := hIiz
  have s4 : SpecDec Idc C4 := hIdc
  have s5 : SpecInc Iic C5 := hIic
  have s6 : SpecAddNat Iad C6 := hIad
  have s7 : SpecCmpNat Icm C7 := hIcm
  have s8 : SpecDivMod Idm C8 := hIdm
  let I : HI := ⟨Icp, Idr, Iiz, Idc, Iic, Iad, Icm, Idm⟩
  have hI : I.Spec (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) :=
    ⟨s1.mono (by omega), s2.mono (by omega), s3.mono (by omega), s4.mono (by omega),
      s5.mono (by omega), s6.mono (by omega), s7.mono (by omega), s8.mono (by omega)⟩
  refine ⟨4, 200 * (6561 * (2 * (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) + 2)),
    fun _ => ⟨Fin 24, inferInstance, inferInstance, I.R, progU I, I.R_finite, I.R_nonempty,
      closed_progU, ?_⟩⟩
  intro q ℓ K w D a hrest prest S hcl hsh hS0 hS1
  have hSeq : S = toF (U0 (midHdr q ℓ K w a ++ hrest) prest) := by
    funext x
    rcases x with i | j
    · fin_cases i
      · simpa [toF, U0] using hS0
      · simpa [toF, U0] using hS1
    · rw [hcl j]
      fin_cases j <;> rfl
  subst hSeq
  obtain ⟨-, -, hl2, -, hK1, -, ha, -⟩ := id hsh
  refine HT.runs (HT.of_eq (ht_progU hI q ℓ K w D a hrest prest hsh) ?_ ?_)
  · rw [upd_p]
    simp only [permSyms, layoutMap]
    rw [ofFn_layoutU ℓ K a (by omega) hl2 ha]
    rfl
  · have hz := zc_polyU (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) (w + addrBits a + 1) (by omega)
    calc 200 * Zc (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) (8 * (w + addrBits a + 1)) 3
        ≤ 200 * (6561 * (2 * (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) + 2) *
            (w + addrBits a + 1) ^ 4) := Nat.mul_le_mul_left _ hz
      _ ≤ 200 * (6561 * (2 * (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) + 2)) *
            ((w + addrBits a + 1) ^ 4 + (midHdr q ℓ K w a).length) := by
        have e : 200 * (6561 * (2 * (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) + 2) *
            (w + addrBits a + 1) ^ 4) =
            200 * (6561 * (2 * (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) + 2)) *
            (w + addrBits a + 1) ^ 4 := by ring
        rw [e]
        exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

end SubNLogN.Machine
