/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.LayoutMapL

/-!
# K4.3c-L (`Machine/FFT/LayoutMapLHolds.lean`): `LayoutMapGenStmt .L` proved

The builder `progL` of the runtime map of the layout `L` (`LayoutMapGenStmt .L`,
`Machine/FFT/LayoutCompile.lean`): read the five leading header fields; pass 1 over the axis
exponents (`m₀ = Σ a_i`, `n_long`); restore the header; the constants (`ℓ - 1`, `J_blk`, `b₀` by
one `divModNat`, `D·K` and `n_P` by addition loops); the main pass emitting `genL` onto the scratch
stack `so` (Machine/FFT/LayoutMapL.lean); restore the header and its five leading fields; move the
emitted fields onto the destination (`hdrSyms`, first value on top); drop the scratch numbers.
`genL_eq`, `ofFn_layoutL` identify the emitted list with `permSyms (layoutMap .L ℓ K a)`.
`layoutMapGen_L_holds : LayoutMapGenStmt .L` is proved from the proved contracts `W3_copyNat`,
`W3_dropNat`, `W3_isZeroNat`, `W3_decNat`, `W3_incNat`, `W3_addNat`, `W3_cmpNat`, `W3_subNat`
and `W6a_divModNat` only (exponent `J = 4`). No `sorry`.
-/

namespace SubNLogN.Machine.FFT.LayoutMapAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.FFT.LayoutHdrAux (savedF savedF_nil savedF_concat natSyms_zero'
  hdrSyms_cons' hdrSyms_nil' midHdr_eq' opY cost1_le cost2_le one_le_opY bitLen_le
  loopCost_le_of_le sum_take_le' take_succ_sum' drop_hdr' savedF_take_succ' C_le_opY hdr_assoc)
open SubNLogN.Machine.FFT.LayoutMapMath SubNLogN.Math.Walsh.IntForms

/-! ## 1. Records, final drop, list facts -/

/-- The initial record: header `H`, destination `P`, all scratch stacks empty. -/
def M0 (H P : List Sym) : MS :=
  ⟨H, P, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    []⟩

/-- After reading the five leading header fields. -/
def SA (H P : List Sym) (q D ℓ K w : ℕ) : MS :=
  {M0 H P with q := natSyms q, D := natSyms D, l := natSyms ℓ, K := natSyms K, w := natSyms w}

/-- The records of pass 1 (`j` exponents processed). -/
def RL1 (H P : List Sym) (q D ℓ K w : ℕ) (as : List ℕ) (j : ℕ) : MS :=
  {SA H P q D ℓ K w with m := natSyms ((as.take j).sum), lc := natSyms ((as.take j).count ℓ)}

/-- The records of the main pass of `L` (`j` exponents processed). -/
def RL3 (H P : List Sym) (q D ℓ K w : ℕ) (as : List ℕ) (j : ℕ) : MS :=
  {SA H P q D ℓ K w with
    m := natSyms ((as.take D).sum), lc := natSyms ((as.take D).count ℓ),
    L1 := natSyms (ℓ - 1), J := natSyms ((ℓ - 1) / K), b := natSyms ((ℓ - 1) % K),
    DK := natSyms (D * K),
    ck := natSyms ((as.take D).count ℓ + (ℓ - 1) % K * D + K * j),
    pf := natSyms ((as.take D).count ℓ + j), rr := natSyms ((as.take j).count ℓ),
    o := savedF (genL ℓ ((ℓ - 1) / K) K (D * K) ((ℓ - 1) % K) D
      ((as.take D).count ℓ + (ℓ - 1) % K * D) ((as.take D).count ℓ) (as.take j))}

theorem ht_pre {I : HI} {B0 B B' : LM → List Sym} {p : HP I} {T : ℕ} (h : HT [] B p B' T)
    (e : B0 = B) : HT [] B0 p B' T := e ▸ h

theorem take_succ_sum'' (as : List ℕ) (j : ℕ) (hj : j < as.length) :
    (as.take (j + 1)).sum = (as.take j).sum + as[j] := by
  rw [take_succ_sum' as j hj, Nat.add_comm]

theorem take_succ_count (as : List ℕ) (j ℓ : ℕ) (hj : j < as.length) :
    (as.take (j + 1)).count ℓ = (as.take j).count ℓ + if as[j] = ℓ then 1 else 0 := by
  rw [List.take_succ_eq_append_getElem hj, List.count_append]
  by_cases h : as[j] = ℓ <;> simp [h]

theorem count_take_le (as : List ℕ) (j ℓ : ℕ) : (as.take j).count ℓ ≤ j := by
  refine le_trans List.count_le_length ?_
  rw [List.length_take]; exact Nat.min_le_left _ _

theorem genL_take_succ (ℓ J K dk b D nP lc : ℕ) (as : List ℕ) (j : ℕ) (hj : j < as.length) :
    genL ℓ J K dk b D nP lc (as.take (j + 1)) = genL ℓ J K dk b D nP lc (as.take j) ++
      axL ℓ J K dk b D as[j] ((as.take j).count ℓ) (nP + j * K) (lc + j) := by
  rw [List.take_succ_eq_append_getElem hj, genL_concat, List.length_take,
    Nat.min_eq_left (le_of_lt hj)]

section CleanL

variable {I : HI} {C : ℕ}

/-- Drop the scratch numbers of the builder of `L` (first half). -/
def cleanL1 (I : HI) : HP I :=
  (hdr I vq).seq ((hdr I vD).seq ((hdr I vl).seq ((hdr I vK).seq ((hdr I vw).seq ((hdr I vm).seq
  (hdr I slc))))))

/-- Drop the scratch numbers of the builder of `L` (second half). -/
def cleanL2 (I : HI) : HP I :=
  (hdr I sL1).seq ((hdr I vJ).seq ((hdr I vb).seq ((hdr I vDK).seq ((hdr I sck).seq
  ((hdr I spf).seq (hdr I srr))))))

theorem ht_cleanL1 (hI : I.Spec C) (M : MS) (q D ℓ K w m lc B : ℕ)
    (h1 : M.q = natSyms q) (h2 : M.D = natSyms D) (h3 : M.l = natSyms ℓ) (h4 : M.K = natSyms K)
    (h5 : M.w = natSyms w) (h6 : M.m = natSyms m) (h7 : M.lc = natSyms lc)
    (b1 : q ≤ B) (b2 : D ≤ B) (b3 : ℓ ≤ B) (b4 : K ≤ B) (b5 : w ≤ B) (b6 : m ≤ B)
    (b7 : lc ≤ B) :
    HT [] (toF M) (cleanL1 I)
      (toF {M with q := [], D := [], l := [], K := [], w := [], m := [], lc := []})
      (7 * opY C B) := by
  unfold cleanL1
  refine HT.of_eq
    ((ht_dr hI vq _ q [] TermOK.nil (by simp [toF, h1])).seq
    ((ht_dr hI vD _ D [] TermOK.nil (by simp [toF, h2])).seq
    ((ht_dr hI vl _ ℓ [] TermOK.nil (by simp [toF, h3])).seq
    ((ht_dr hI vK _ K [] TermOK.nil (by simp [toF, h4])).seq
    ((ht_dr hI vw _ w [] TermOK.nil (by simp [toF, h5])).seq
    ((ht_dr hI vm _ m [] TermOK.nil (by simp [toF, h6])).seq
    (ht_dr hI slc _ lc [] TermOK.nil (by simp [toF, h7])))))))) ?_ ?_
  · simp only [upd_q, upd_D, upd_l, upd_K, upd_w, upd_m, upd_lc]
  · have c1 := cost1_le (C := C) (bitLen_le b1)
    have c2 := cost1_le (C := C) (bitLen_le b2)
    have c3 := cost1_le (C := C) (bitLen_le b3)
    have c4 := cost1_le (C := C) (bitLen_le b4)
    have c5 := cost1_le (C := C) (bitLen_le b5)
    have c6 := cost1_le (C := C) (bitLen_le b6)
    have c7 := cost1_le (C := C) (bitLen_le b7)
    omega

theorem ht_cleanL2 (hI : I.Spec C) (M : MS) (L1 J b dk ck pf rr B : ℕ)
    (h8 : M.L1 = natSyms L1) (h9 : M.J = natSyms J) (h10 : M.b = natSyms b)
    (h11 : M.DK = natSyms dk) (h12 : M.ck = natSyms ck) (h13 : M.pf = natSyms pf)
    (h14 : M.rr = natSyms rr)
    (b8 : L1 ≤ B) (b9 : J ≤ B) (b10 : b ≤ B) (b11 : dk ≤ B) (b12 : ck ≤ B) (b13 : pf ≤ B)
    (b14 : rr ≤ B) :
    HT [] (toF M) (cleanL2 I)
      (toF {M with L1 := [], J := [], b := [], DK := [], ck := [], pf := [], rr := []})
      (7 * opY C B) := by
  unfold cleanL2
  refine HT.of_eq
    ((ht_dr hI sL1 _ L1 [] TermOK.nil (by simp [toF, h8])).seq
    ((ht_dr hI vJ _ J [] TermOK.nil (by simp [toF, h9])).seq
    ((ht_dr hI vb _ b [] TermOK.nil (by simp [toF, h10])).seq
    ((ht_dr hI vDK _ dk [] TermOK.nil (by simp [toF, h11])).seq
    ((ht_dr hI sck _ ck [] TermOK.nil (by simp [toF, h12])).seq
    ((ht_dr hI spf _ pf [] TermOK.nil (by simp [toF, h13])).seq
    (ht_dr hI srr _ rr [] TermOK.nil (by simp [toF, h14])))))))) ?_ ?_
  · simp only [upd_L1, upd_J, upd_b, upd_DK, upd_ck, upd_pf, upd_rr]
  · have c8 := cost1_le (C := C) (bitLen_le b8)
    have c9 := cost1_le (C := C) (bitLen_le b9)
    have c10 := cost1_le (C := C) (bitLen_le b10)
    have c11 := cost1_le (C := C) (bitLen_le b11)
    have c12 := cost1_le (C := C) (bitLen_le b12)
    have c13 := cost1_le (C := C) (bitLen_le b13)
    have c14 := cost1_le (C := C) (bitLen_le b14)
    omega

end CleanL

/-! ## 2. The builder of `L` -/

/-- Stage 1: the five leading fields, pass 1, restore, the constants. -/
def progL1 (I : HI) : HP I := (blockA I).seq ((passB I (bd1 I)).seq ((passC I).seq (constsL I)))

/-- Stage 2: the main pass, restore. -/
def progL2 (I : HI) : HP I := (passB I (pBdL I)).seq (passC I)

/-- Stage 3: the leading fields back, the final move, the drops. -/
def progL3 (I : HI) : HP I := (blockD I).seq ((moveO I).seq ((cleanL1 I).seq (cleanL2 I)))

/-- **The builder of the runtime map of `L`.** -/
def progL (I : HI) : HP I := (progL1 I).seq ((progL2 I).seq (progL3 I))

theorem closed_progL {I : HI} : (progL I).Closed := by
  unfold progL progL1 progL2 progL3 blockA blockD constsL mulDK mulCK cleanL1 cleanL2 pBdL pLongL
    pChunkL pChunkJ pInnerK pPrefL bd1
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

/-! ## 3. The run of the builder of `L` -/

/-- The shape facts used by the bounds. -/
theorem shapeFactsL {q ℓ K w D : ℕ} {a : Fin D → ℕ} (hsh : MidShapeOK q ℓ K w a) :
    0 < K ∧ 2 ≤ ℓ ∧ K ≤ ℓ - 1 ∧ ℓ < q ∧ q + 2 ≤ w ∧ D ≤ addrBits a ∧
    D * (ℓ - 1) ≤ addrBits a ∧ D * K ≤ D * (ℓ - 1) ∧ (ℓ - 1) / K * (D * K) ≤ D * (ℓ - 1) ∧
    (ℓ - 1) % K * D ≤ D * (ℓ - 1) ∧ (ℓ - 1) / K ≤ ℓ ∧ (ℓ - 1) % K < K ∧
    (∀ x ∈ List.ofFn a, x = ℓ - 1 ∨ x = ℓ) ∧ (List.ofFn a).length = D := by
  obtain ⟨hq8, hD1, hl2, hlq, hK1, hKl, ha, hqw⟩ := hsh
  have hmem : ∀ x ∈ List.ofFn a, x = ℓ - 1 ∨ x = ℓ := by
    intro x hx; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact ha i
  have hK0 : 0 < K := by omega
  have hJK : (ℓ - 1) / K * K ≤ ℓ - 1 := Nat.div_mul_le_self _ _
  have hbK : (ℓ - 1) % K < K := Nat.mod_lt _ hK0
  refine ⟨hK0, hl2, hKl, hlq, hqw, FFT.LayoutAux.le_addrBits hl2 ha, ?_,
    Nat.mul_le_mul_left _ hKl, ?_, ?_, le_trans (Nat.div_le_self _ _) (by omega), hbK, hmem,
    List.length_ofFn⟩
  · rw [LayoutPermAux.addrBits_eq ℓ a (by omega) ha]; omega
  · calc (ℓ - 1) / K * (D * K) = D * ((ℓ - 1) / K * K) := by ring
      _ ≤ D * (ℓ - 1) := Nat.mul_le_mul_left _ hJK
  · calc (ℓ - 1) % K * D ≤ (ℓ - 1) * D := Nat.mul_le_mul_right _ (by omega)
      _ = D * (ℓ - 1) := by ring

section MainL

variable {I : HI} {C : ℕ}

theorem ht_progL1 (hI : I.Spec C) (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest prest : List Sym)
    (hsh : MidShapeOK q ℓ K w a) :
    HT [] (toF (M0 (natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
        (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms (List.ofFn a) ++ hrest)))))) prest)) (progL1 I)
      (toF (RL3 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) 0))
      (70 * Zc C (8 * (w + addrBits a + 1)) 1) := by
  obtain ⟨hK0, hl2, hKl, hlq, hqw, hDm, hDl, hDK, hJDK, hbD, hJl, hbK, hmem, hlen⟩ :=
    shapeFactsL hsh
  have hKD : K * D = D * K := Nat.mul_comm _ _
  have hxB : ∀ x ∈ List.ofFn a, x ≤ 8 * (w + addrBits a + 1) := by
    intro x hx; rcases hmem x hx with h | h <;> omega
  have hsD : ((List.ofFn a).take D).sum ≤ addrBits a := sum_take_le' _ _
  have hcD : ((List.ofFn a).take D).count ℓ ≤ D := count_take_le _ _ _
  have hsum : (List.ofFn a).sum = addrBits a := rfl
  have hbd1 : ∀ j (hj : j < (List.ofFn a).length) (i : ℕ), HT []
      (toF {RL1 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) j with
        h := natSyms (List.ofFn a)[j] ++ Sym.mark ::
          (hdrSyms ((List.ofFn a).drop (j + 1)) ++ hrest),
        A := natSyms (List.ofFn a)[j], s := savedF ((List.ofFn a).take j),
        c := natSyms i ++ []}) (bd1 I)
      (toF {RL1 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) (j + 1) with
        h := natSyms (List.ofFn a)[j] ++ Sym.mark ::
          (hdrSyms ((List.ofFn a).drop (j + 1)) ++ hrest),
        A := natSyms (List.ofFn a)[j], s := savedF ((List.ofFn a).take j),
        c := natSyms i ++ []}) (10 * opY C (8 * (w + addrBits a + 1))) := by
    intro j hj i
    have hxj := hmem _ (List.getElem_mem hj)
    have hs1 := sum_take_le' (List.ofFn a) (j + 1)
    rw [take_succ_sum'' _ j hj] at hs1
    have hc1 := count_take_le (List.ofFn a) j ℓ
    refine HT.of_eq (ht_bd1 hI _ (List.ofFn a)[j] ℓ (((List.ofFn a).take j).sum)
      (((List.ofFn a).take j).count ℓ) (8 * (w + addrBits a + 1)) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rcases hxj with h | h <;> omega) (by omega) (by omega) (by omega))
      ?_ le_rfl
    unfold RL1
    rw [take_succ_sum'' _ j hj, take_succ_count _ j ℓ hj]
    rfl
  unfold progL1
  refine HT.of_eq
    ((HT.of_eq (ht_blockA hI _ q D ℓ K w (8 * (w + addrBits a + 1))
        (hdrSyms (List.ofFn a) ++ hrest) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by omega) (by omega) (by omega) (by omega) (by omega)) rfl le_rfl).seq
    ((ht_passB hI (bd1 I) (List.ofFn a) D (8 * (w + addrBits a + 1))
        (10 * opY C (8 * (w + addrBits a + 1))) hrest
        (RL1 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a)) hlen (by omega) hxB
        rfl hbd1).seq
    ((ht_passC hI {RL1 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) D with
        A := [], c := []} (List.ofFn a) D (8 * (w + addrBits a + 1)) hrest hlen (by omega) hxB
        rfl rfl).seq
    (ht_constsL hI _ ℓ K D (((List.ofFn a).take D).count ℓ) (8 * (w + addrBits a + 1))
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by rfl) (by rfl) (by omega) hK0 (by omega) (by omega) (by omega) (by omega)
        (by omega))))) rfl ?_
  have k1 : ((8 * (w + addrBits a + 1)) + 1) * (10 * opY C (8 * (w + addrBits a + 1)) +
      10 * opY C (8 * (w + addrBits a + 1))) = 20 * Zc C (8 * (w + addrBits a + 1)) 1 := by
    simp only [Zc]; ring
  have k2 : ((8 * (w + addrBits a + 1)) + 1) * (8 * opY C (8 * (w + addrBits a + 1))) =
      8 * Zc C (8 * (w + addrBits a + 1)) 1 := by
    simp only [Zc]; ring
  have m1 := opY_le_Zc C (8 * (w + addrBits a + 1)) 1
  omega

theorem ht_progL2 (hI : I.Spec C) (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest prest : List Sym)
    (hsh : MidShapeOK q ℓ K w a) :
    HT [] (toF (RL3 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) 0)) (progL2 I)
      (toF {RL3 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) D with
        A := [], c := [], s := []})
      (70 * Zc C (8 * (w + addrBits a + 1)) 3) := by
  obtain ⟨hK0, hl2, hKl, hlq, hqw, hDm, hDl, hDK, hJDK, hbD, hJl, hbK, hmem, hlen⟩ :=
    shapeFactsL hsh
  have hKD : K * D = D * K := Nat.mul_comm _ _
  have hxB : ∀ x ∈ List.ofFn a, x ≤ 8 * (w + addrBits a + 1) := by
    intro x hx; rcases hmem x hx with h | h <;> omega
  have hsD : ((List.ofFn a).take D).sum ≤ addrBits a := sum_take_le' _ _
  have hcD : ((List.ofFn a).take D).count ℓ ≤ D := count_take_le _ _ _
  have hsum : (List.ofFn a).sum = addrBits a := rfl
  have hbdL : ∀ j (hj : j < (List.ofFn a).length) (i : ℕ), HT []
      (toF {RL3 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) j with
        h := natSyms (List.ofFn a)[j] ++ Sym.mark ::
          (hdrSyms ((List.ofFn a).drop (j + 1)) ++ hrest),
        A := natSyms (List.ofFn a)[j], s := savedF ((List.ofFn a).take j),
        c := natSyms i ++ []}) (pBdL I)
      (toF {RL3 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) (j + 1) with
        h := natSyms (List.ofFn a)[j] ++ Sym.mark ::
          (hdrSyms ((List.ofFn a).drop (j + 1)) ++ hrest),
        A := natSyms (List.ofFn a)[j], s := savedF ((List.ofFn a).take j),
        c := natSyms i ++ []}) (50 * Zc C (8 * (w + addrBits a + 1)) 2) := by
    intro j hj i
    have hxj := hmem _ (List.getElem_mem hj)
    have hc1 := count_take_le (List.ofFn a) j ℓ
    have hjD : j < D := by omega
    have hKj : K * j ≤ D * K := by
      rw [Nat.mul_comm D K]; exact Nat.mul_le_mul_left _ (le_of_lt hjD)
    refine HT.of_eq (ht_bdL hI _ (genL ℓ ((ℓ - 1) / K) K (D * K) ((ℓ - 1) % K) D
      (((List.ofFn a).take D).count ℓ + (ℓ - 1) % K * D) (((List.ofFn a).take D).count ℓ)
      ((List.ofFn a).take j)) (List.ofFn a)[j] ℓ (((List.ofFn a).take j).count ℓ)
      (((List.ofFn a).take D).count ℓ + (ℓ - 1) % K * D + K * j)
      (((List.ofFn a).take D).count ℓ + j) ((ℓ - 1) / K) K (D * K) ((ℓ - 1) % K) D
      (8 * (w + addrBits a + 1)) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rcases hxj with h | h <;> omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) ?_ le_rfl
    have eck : ((List.ofFn a).take D).count ℓ + (ℓ - 1) % K * D + K * (j + 1) =
        ((List.ofFn a).take D).count ℓ + (ℓ - 1) % K * D + K * j + K := by ring
    have epf : ((List.ofFn a).take D).count ℓ + (j + 1) =
        ((List.ofFn a).take D).count ℓ + j + 1 := by ring
    unfold RL3
    rw [genL_take_succ _ _ _ _ _ _ _ _ _ j hj, take_succ_count _ j ℓ hj, Nat.mul_comm j K, eck,
      epf]
    rfl
  unfold progL2
  refine HT.of_eq
    ((ht_pre (ht_passB hI (pBdL I) (List.ofFn a) D (8 * (w + addrBits a + 1))
        (50 * Zc C (8 * (w + addrBits a + 1)) 2) hrest
        (RL3 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a)) hlen (by omega) hxB
        rfl hbdL) rfl).seq
    (ht_passC hI {RL3 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) D with
        A := [], c := []} (List.ofFn a) D (8 * (w + addrBits a + 1)) hrest hlen (by omega) hxB
        rfl rfl)) rfl ?_
  have k2 : ((8 * (w + addrBits a + 1)) + 1) * (8 * opY C (8 * (w + addrBits a + 1))) =
      8 * Zc C (8 * (w + addrBits a + 1)) 1 := by
    simp only [Zc]; ring
  have k3 : ((8 * (w + addrBits a + 1)) + 1) * (50 * Zc C (8 * (w + addrBits a + 1)) 2 +
      10 * opY C (8 * (w + addrBits a + 1))) = 50 * Zc C (8 * (w + addrBits a + 1)) 3 +
      10 * Zc C (8 * (w + addrBits a + 1)) 1 := by
    simp only [Zc]; ring
  have m2 : Zc C (8 * (w + addrBits a + 1)) 1 ≤ Zc C (8 * (w + addrBits a + 1)) 2 := Zc_mono _ _ 1
  have m3 : Zc C (8 * (w + addrBits a + 1)) 2 ≤ Zc C (8 * (w + addrBits a + 1)) 3 := Zc_mono _ _ 2
  omega

theorem ht_progL3 (hI : I.Spec C) (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest prest : List Sym)
    (hsh : MidShapeOK q ℓ K w a) :
    HT [] (toF {RL3 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) D with
        A := [], c := [], s := []}) (progL3 I)
      (toF (M0 (natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
        (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms (List.ofFn a) ++ hrest))))))
        (hdrSyms (genL ℓ ((ℓ - 1) / K) K (D * K) ((ℓ - 1) % K) D
          (((List.ofFn a).take D).count ℓ + (ℓ - 1) % K * D) (((List.ofFn a).take D).count ℓ)
          ((List.ofFn a).take D)) ++ prest)))
      (35 * Zc C (8 * (w + addrBits a + 1)) 1) := by
  obtain ⟨hK0, hl2, hKl, hlq, hqw, hDm, hDl, hDK, hJDK, hbD, hJl, hbK, hmem, hlen⟩ :=
    shapeFactsL hsh
  have hKD : K * D = D * K := Nat.mul_comm _ _
  have hxB : ∀ x ∈ List.ofFn a, x ≤ 8 * (w + addrBits a + 1) := by
    intro x hx; rcases hmem x hx with h | h <;> omega
  have hsD : ((List.ofFn a).take D).sum ≤ addrBits a := sum_take_le' _ _
  have hcD : ((List.ofFn a).take D).count ℓ ≤ D := count_take_le _ _ _
  have hsum : (List.ofFn a).sum = addrBits a := rfl
  have hgen : genL ℓ ((ℓ - 1) / K) K (D * K) ((ℓ - 1) % K) D
      (((List.ofFn a).take D).count ℓ + (ℓ - 1) % K * D) (((List.ofFn a).take D).count ℓ)
      ((List.ofFn a).take D) = layoutLList ℓ K a := by
    rw [List.take_of_length_le (le_of_eq hlen)]
    exact genL_eq ℓ K a hK0 hKl hl2 (fun i => hmem _ (List.mem_ofFn.2 ⟨i, rfl⟩))
  have hLlen : (layoutLList ℓ K a).length = ((List.ofFn a).take D).sum := by
    rw [List.take_of_length_le (le_of_eq hlen), layoutLList, List.length_map,
      LayoutPermAux.length_origSlots]
    rfl
  have hLB : ∀ x ∈ layoutLList ℓ K a, x ≤ 8 * (w + addrBits a + 1) := by
    intro x hx
    rw [← ofFn_layoutL ℓ K a hK0 hl2 (fun i => hmem _ (List.mem_ofFn.2 ⟨i, rfl⟩))] at hx
    obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hx
    have := (layoutL ℓ K a p).isLt
    omega
  rw [← hgen] at hLlen hLB
  unfold progL3
  refine HT.of_eq
    ((ht_blockD hI _ q D ℓ K w (8 * (w + addrBits a + 1)) (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by omega) (by omega) (by omega) (by omega) (by omega)).seq
    ((ht_moveO hI {RL3 (hdrSyms (List.ofFn a) ++ hrest) prest q D ℓ K w (List.ofFn a) D with
        A := [], c := [], s := [], h := natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
        (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms (List.ofFn a) ++ hrest)))))}
        _ (((List.ofFn a).take D).sum) (8 * (w + addrBits a + 1)) prest hLlen (by omega) hLB
        rfl rfl).seq
    ((ht_cleanL1 hI _ q D ℓ K w (((List.ofFn a).take D).sum) (((List.ofFn a).take D).count ℓ)
        (8 * (w + addrBits a + 1)) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).seq
    (ht_cleanL2 hI _ (ℓ - 1) ((ℓ - 1) / K) ((ℓ - 1) % K) (D * K)
        (((List.ofFn a).take D).count ℓ + (ℓ - 1) % K * D + K * D)
        (((List.ofFn a).take D).count ℓ + D) (((List.ofFn a).take D).count ℓ)
        (8 * (w + addrBits a + 1)) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))
    rfl ?_
  have k2 : ((8 * (w + addrBits a + 1)) + 1) * (8 * opY C (8 * (w + addrBits a + 1))) =
      8 * Zc C (8 * (w + addrBits a + 1)) 1 := by
    simp only [Zc]; ring
  have m1 := opY_le_Zc C (8 * (w + addrBits a + 1)) 1
  omega

theorem ht_progL (hI : I.Spec C) (q ℓ K w D : ℕ) (a : Fin D → ℕ) (hrest prest : List Sym)
    (hsh : MidShapeOK q ℓ K w a) :
    HT [] (toF (M0 (midHdr q ℓ K w a ++ hrest) prest)) (progL I)
      (toF (M0 (midHdr q ℓ K w a ++ hrest) (hdrSyms (layoutLList ℓ K a) ++ prest)))
      (200 * Zc C (8 * (w + addrBits a + 1)) 3) := by
  obtain ⟨hK0, hl2, hKl, hlq, hqw, hDm, hDl, hDK, hJDK, hbD, hJl, hbK, hmem, hlen⟩ :=
    shapeFactsL hsh
  have hgen : genL ℓ ((ℓ - 1) / K) K (D * K) ((ℓ - 1) % K) D
      (((List.ofFn a).take D).count ℓ + (ℓ - 1) % K * D) (((List.ofFn a).take D).count ℓ)
      ((List.ofFn a).take D) = layoutLList ℓ K a := by
    rw [List.take_of_length_le (le_of_eq hlen)]
    exact genL_eq ℓ K a hK0 hKl hl2 (fun i => hmem _ (List.mem_ofFn.2 ⟨i, rfl⟩))
  have hhdr : midHdr q ℓ K w a ++ hrest = natSyms q ++ Sym.mark :: (natSyms D ++ Sym.mark :: (natSyms ℓ ++ Sym.mark ::
        (natSyms K ++ Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms (List.ofFn a) ++ hrest))))) := by
    rw [midHdr_eq', hdr_assoc]
  rw [hhdr, ← hgen]
  unfold progL
  refine HT.mono ((ht_progL1 hI q ℓ K w D a hrest prest hsh).seq
    ((ht_progL2 hI q ℓ K w D a hrest prest hsh).seq (ht_progL3 hI q ℓ K w D a hrest prest hsh))) ?_
  have m2 : Zc C (8 * (w + addrBits a + 1)) 1 ≤ Zc C (8 * (w + addrBits a + 1)) 2 := Zc_mono _ _ 1
  have m3 : Zc C (8 * (w + addrBits a + 1)) 2 ≤ Zc C (8 * (w + addrBits a + 1)) 3 := Zc_mono _ _ 2
  omega

end MainL

end SubNLogN.Machine.FFT.LayoutMapAux

namespace SubNLogN.Machine

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Math.Walsh
open SubNLogN.Math.Walsh.IntForms SubNLogN.Machine.FFT.LayoutMapAux

theorem zc_poly (Cs Bm : ℕ) (hBm : 1 ≤ Bm) : Zc Cs (8 * Bm) 3 ≤ 6561 * (2 * Cs + 2) * Bm ^ 4 := by
  unfold Zc SubNLogN.Machine.FFT.LayoutHdrAux.opY
  have h1 : 8 * Bm + 1 ≤ 9 * Bm := by omega
  have h2 : (8 * Bm + 1) ^ 3 ≤ (9 * Bm) ^ 3 := Nat.pow_le_pow_left h1 3
  have h0 : Cs ≤ Cs * Bm := Nat.le_mul_of_pos_right _ hBm
  have h3 : Cs * (2 * (8 * Bm) + 1) + 2 * (8 * Bm) + 2 ≤ (2 * Cs + 2) * (9 * Bm) := by
    nlinarith
  calc (8 * Bm + 1) ^ 3 * (Cs * (2 * (8 * Bm) + 1) + 2 * (8 * Bm) + 2)
      ≤ (9 * Bm) ^ 3 * ((2 * Cs + 2) * (9 * Bm)) := Nat.mul_le_mul h2 h3
    _ = 6561 * (2 * Cs + 2) * Bm ^ 4 := by ring

/-- **K4.3c for `L` proved: the runtime map of the layout `L` from the middle header**
(exponent `J = 4`), from the proved W3 contracts and `W6a_divModNat` only. No `sorry`. -/
theorem layoutMapGen_L_holds : LayoutMapGenStmt .L := by
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
    fun _ => ⟨Fin 24, inferInstance, inferInstance, I.R, progL I, I.R_finite, I.R_nonempty,
      closed_progL, ?_⟩⟩
  intro q ℓ K w D a hrest prest S hcl hsh hS0 hS1
  have hSeq : S = toF (M0 (midHdr q ℓ K w a ++ hrest) prest) := by
    funext x
    rcases x with i | j
    · fin_cases i
      · simpa [toF, M0] using hS0
      · simpa [toF, M0] using hS1
    · rw [hcl j]
      fin_cases j <;> rfl
  subst hSeq
  obtain ⟨-, -, hl2, -, hK1, -, ha, -⟩ := id hsh
  refine HT.runs (HT.of_eq (ht_progL hI q ℓ K w D a hrest prest hsh) ?_ ?_)
  · rw [upd_p]
    simp only [permSyms, layoutMap]
    rw [ofFn_layoutL ℓ K a (by omega) hl2 ha]
    rfl
  · have hz := zc_poly (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) (w + addrBits a + 1) (by omega)
    have hm : 0 ≤ (midHdr q ℓ K w a).length := Nat.zero_le _
    calc 200 * Zc (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) (8 * (w + addrBits a + 1)) 3
        ≤ 200 * (6561 * (2 * (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) + 2) *
            (w + addrBits a + 1) ^ 4) := Nat.mul_le_mul_left _ hz
      _ = 200 * (6561 * (2 * (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) + 2)) *
            (w + addrBits a + 1) ^ 4 := by ring
      _ ≤ 200 * (6561 * (2 * (C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8) + 2)) *
            ((w + addrBits a + 1) ^ 4 + (midHdr q ℓ K w a).length) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

end SubNLogN.Machine
