/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.LayoutMapBase
import SubNLogN.Machine.FFT.LayoutMapMath

/-!
# K4.3c-L (`Machine/FFT/LayoutMapL.lean`): the runtime map of the layout `L` from `midHdr`

The bodies of the map builder of `L` (`LayoutMapGenStmt .L`, `Machine/FFT/LayoutCompile.lean`):
per axis exponent `a_i` (in order) the builder emits onto the scratch stack `so` the list
`axL` of `Machine/FFT/LayoutMapMath.lean` (the long slot if `a_i = ℓ`, then `J_blk` blocks of `K`
consecutive positions, then `b₀` positions of stride `D`), by nested counted loops with additions
only. Costs are bounded in the units `Zc C B n = (B+1)^n · opY C B`. No `sorry`.
-/

namespace SubNLogN.Machine.FFT.LayoutMapAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.FFT.LayoutHdrAux (savedF savedF_nil savedF_concat natSyms_zero'
  hdrSyms_cons' hdrSyms_nil' midHdr_eq' opY cost1_le cost2_le one_le_opY bitLen_le
  loopCost_le_of_le sum_take_le' take_succ_sum' drop_hdr' savedF_take_succ' C_le_opY)
open SubNLogN.Machine.FFT.LayoutMapMath

/-! ## 1. Cost units -/

/-- Cost unit of loop depth `n`. -/
def Zc (C B n : ℕ) : ℕ := (B + 1) ^ n * opY C B

theorem Zc_zero (C B : ℕ) : Zc C B 0 = opY C B := by simp [Zc]

theorem Zc_succ (C B n : ℕ) : Zc C B (n + 1) = (B + 1) * Zc C B n := by unfold Zc; ring

theorem Zc_mono (C B n : ℕ) : Zc C B n ≤ Zc C B (n + 1) := by
  rw [Zc_succ]; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

theorem opY_le_Zc (C B n : ℕ) : opY C B ≤ Zc C B n := by
  induction n with
  | zero => rw [Zc_zero]
  | succ n ih => exact le_trans ih (Zc_mono C B n)

theorem loop_Z (C B N n m k : ℕ) (hm : m = n + 1) (hN : N ≤ B) (f : ℕ → ℕ)
    (hf : ∀ i, i < N → f i ≤ k * Zc C B n) :
    C + loopCost (fun i => C * (bitLen (i + 1) + 1) + f i + C) N ≤ (k + 3) * Zc C B m := by
  subst hm
  refine le_trans (loop_cost C B N (k * Zc C B n) hN f hf) ?_
  have h1 := opY_le_Zc C B n
  rw [Zc_succ]
  calc (B + 1) * (k * Zc C B n + 3 * opY C B) ≤ (B + 1) * ((k + 3) * Zc C B n) :=
        Nat.mul_le_mul_left _ (by nlinarith)
    _ = (k + 3) * ((B + 1) * Zc C B n) := by ring

theorem cost_ic_le {C B v : ℕ} (hv : v ≤ B) :
    C * (ones (Computability.encodeNat v) + 1) ≤ opY C B := by
  have h1 : ones (Computability.encodeNat v) ≤ bitLen v := by unfold bitLen; exact ones_le_length _
  exact le_trans (Nat.mul_le_mul_left _ (by omega)) (cost1_le (bitLen_le hv))

theorem cost_dc_le {C B k : ℕ} (hk : k + 1 ≤ B) :
    C * (zerosLead (Computability.encodeNat (k + 1)) + 1) ≤ opY C B := by
  have h1 : zerosLead (Computability.encodeNat (k + 1)) ≤ bitLen (k + 1) := zerosLead_le_length _
  exact le_trans (Nat.mul_le_mul_left _ (by omega)) (cost1_le (bitLen_le hk))

theorem cost_addTo_le {C B u v : ℕ} (hu : u ≤ B) (hv : v ≤ B) (huv : u + v ≤ B) :
    C * (bitLen u + bitLen v + 1) + (C * (bitLen u + 1) +
      (C * (bitLen (u + v) + 1) + C * (bitLen (u + v) + 1))) ≤ 4 * opY C B := by
  have c1 := cost2_le (C := C) (bitLen_le hu) (bitLen_le hv)
  have c2 := cost1_le (C := C) (bitLen_le hu)
  have c3 := cost1_le (C := C) (bitLen_le huv)
  omega

/-! ## 2. Pass 1: sum of the exponents and number of long axes -/

section Pass1

variable {I : HI} {C : ℕ}

/-- Pass 1 body: `m += a`, and `lc += 1` if `a = ℓ`. -/
def bd1 (I : HI) : HP I := (addTo I vm vA).seq (hifEq I vA vl (hic I slc) (hskip I))

theorem closed_bd1 : (bd1 I).Closed :=
  WP.W9comp.closed_seq (closed_addTo _ _ _)
    (closed_hifEq _ _ _ _ _ (callI_closed _ _ _ _) trivial)

theorem ht_bd1 (hI : I.Spec C) (M : MS) (x ℓ s0 c0 B : ℕ)
    (hA : M.A = natSyms x) (hl : M.l = natSyms ℓ) (hm : M.m = natSyms s0)
    (hlc : M.lc = natSyms c0) (ht : M.t = [])
    (hB1 : x ≤ B) (hB2 : ℓ ≤ B) (hB3 : s0 + x ≤ B) (hB4 : c0 + 1 ≤ B) :
    HT [] (toF M) (bd1 I)
      (toF {M with m := natSyms (s0 + x), lc := natSyms (c0 + if x = ℓ then 1 else 0), t := []})
      (10 * opY C B) := by
  unfold bd1
  have hadd := HT.of_eq (ht_addTo hI vm vA (by decide) (toF M) s0 x [] TermOK.nil
      (by simp [toF, hm]) (by simp [toF, hA]) (by simp [toF, ht]))
    (show _ = toF {M with m := natSyms (s0 + x), t := []} by simp only [upd_t, upd_m]) le_rfl
  refine HT.of_eq (hadd.seq (ht_ifEq hI vA vl (by decide) _
    (toF {M with m := natSyms (s0 + x), lc := natSyms (c0 + if x = ℓ then 1 else 0), t := []})
    x ℓ [] [] TermOK.nil TermOK.nil (by simp [toF, hA]) (by simp [toF, hl]) _ _
    (fun h => HT.of_eq (ht_ic hI slc _ c0 [] TermOK.nil (by simp [toF, hlc]))
      (by rw [if_pos h, upd_lc, List.append_nil]) le_rfl)
    (fun h => HT.of_eq (ht_skip _) (by rw [if_neg h, Nat.add_zero, ← hlc]) le_rfl))) rfl ?_
  have c1 := cost_addTo_le (C := C) (show s0 ≤ B by omega) hB1 hB3
  have c2 := cost2_le (C := C) (bitLen_le hB1) (bitLen_le hB2)
  have c3 := cost_ic_le (C := C) (show c0 ≤ B by omega)
  have c4 := one_le_opY C B
  omega

end Pass1

/-! ## 3. Constants: `ℓ - 1`, `J_blk`, `b₀`, `D·K`, `n_P` -/

section Consts

variable {I : HI} {C : ℕ}

theorem cost_dm_le {C B x y : ℕ} (hx : bitLen x ≤ B) (hy : bitLen y ≤ B) :
    C * (bitLen x * bitLen y + bitLen x + bitLen y + 1) ≤ Zc C B 1 := by
  have h1 : bitLen x * bitLen y ≤ B * B := Nat.mul_le_mul hx hy
  have h2 : C * (bitLen x * bitLen y + bitLen x + bitLen y + 1) ≤ C * ((B + 1) * (B + 1)) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  rw [Zc_succ, Zc_zero]
  unfold opY
  nlinarith

/-- `DK := D·K` by `D` additions of `K`. -/
def mulDK (I : HI) : HP I := (hcp I vD sc2).seq (hcd I sc2 (addTo I vDK vK))

def stDK (M : MS) (D K i : ℕ) : LM → List Sym :=
  toF {M with DK := natSyms ((D - i) * K), c2 := natSyms i ++ [], t := []}

theorem ht_mulDK (hI : I.Spec C) (M : MS) (D K B : ℕ) (hD : M.D = natSyms D)
    (hK : M.K = natSyms K) (hDK : M.DK = []) (hc2 : M.c2 = []) (ht : M.t = [])
    (hDB : D ≤ B) (hKB : K ≤ B) (hDKB : D * K ≤ B) :
    HT [] (toF M) (mulDK I) (toF {M with DK := natSyms (D * K), c2 := [], t := []})
      (8 * Zc C B 1) := by
  unfold mulDK hcd
  have hc0 := HT.of_eq (ht_cp0 hI vD sc2 (by decide) (toF M) D [] TermOK.nil
      (by simp [toF, hD]) (by simp [toF, hc2]))
    (show _ = stDK M D K D by
      rw [upd_c2]; unfold stDK; congr 1; ext <;> simp [hDK, ht, natSyms_zero']) le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc sc2 d0 [] TermOK.nil (stDK M D K)
    (fun i => by simp [stDK, toF]) (addTo I vDK vK) (fun _ => 4 * opY C B) D (by
      intro i hi
      have hj : D - i = D - (i + 1) + 1 := by omega
      have hle : (D - (i + 1)) * K + K ≤ D * K := by
        have := Nat.mul_le_mul_right K (show D - (i + 1) + 1 ≤ D by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      have e1 : (D - (i + 1)) * K + K = (D - i) * K := by rw [hj, Nat.add_mul, Nat.one_mul]
      simp only [stDK, upd_c2]
      refine HT.of_eq (ht_addTo hI vDK vK (by decide) _ ((D - (i + 1)) * K) K [] TermOK.nil
        (by simp [toF]) (by simp [toF, hK]) (by simp [toF])) ?_ ?_
      · simp only [upd_t, upd_DK, e1]
      · exact cost_addTo_le (by omega) hKB (by omega))
  refine HT.of_eq (hc0.seq hloop) ?_ ?_
  · simp only [stDK, Nat.sub_zero, natSyms_zero', List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le hDB)
    have h2 := loop_Z C B D 0 1 4 rfl hDB (fun _ => 4 * opY C B) (fun i _ => by rw [Zc_zero])
    have h3 := opY_le_Zc C B 1
    omega

/-- `ck := lc + b·D` by `b` additions of `D`. -/
def mulCK (I : HI) : HP I :=
  ((hcp I slc sck).seq (hcp I vb sc2)).seq (hcd I sc2 (addTo I sck vD))

def stCK (M : MS) (lc b D i : ℕ) : LM → List Sym :=
  toF {M with ck := natSyms (lc + (b - i) * D), c2 := natSyms i ++ [], t := []}

theorem ht_mulCK (hI : I.Spec C) (M : MS) (lc b D B : ℕ) (hlc : M.lc = natSyms lc)
    (hb : M.b = natSyms b) (hD : M.D = natSyms D) (hck : M.ck = []) (hc2 : M.c2 = [])
    (ht : M.t = []) (hbB : b ≤ B) (hDB : D ≤ B) (hcB : lc + b * D ≤ B) :
    HT [] (toF M) (mulCK I) (toF {M with ck := natSyms (lc + b * D), c2 := [], t := []})
      (9 * Zc C B 1) := by
  unfold mulCK hcd
  have hc0 := HT.of_eq ((ht_cp0 hI slc sck (by decide) (toF M) lc [] TermOK.nil
      (by simp [toF, hlc]) (by simp [toF, hck])).seq
      (ht_cp0 hI vb sc2 (by decide) _ b [] TermOK.nil (by simp [toF, hb]) (by simp [toF, hc2])))
    (show _ = stCK M lc b D b by
      rw [upd_ck, upd_c2]; unfold stCK; congr 1; ext <;> simp [ht]) le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc sc2 d0 [] TermOK.nil (stCK M lc b D)
    (fun i => by simp [stCK, toF]) (addTo I sck vD) (fun _ => 4 * opY C B) b (by
      intro i hi
      have hj : b - i = b - (i + 1) + 1 := by omega
      have hle : (b - (i + 1)) * D + D ≤ b * D := by
        have := Nat.mul_le_mul_right D (show b - (i + 1) + 1 ≤ b by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      have e1 : lc + (b - (i + 1)) * D + D = lc + (b - i) * D := by
        rw [hj, Nat.add_mul, Nat.one_mul]; omega
      simp only [stCK, upd_c2]
      refine HT.of_eq (ht_addTo hI sck vD (by decide) _ (lc + (b - (i + 1)) * D) D [] TermOK.nil
        (by simp [toF]) (by simp [toF, hD]) (by simp [toF])) ?_ ?_
      · simp only [upd_t, upd_ck, e1]
      · exact cost_addTo_le (by omega) hDB (by omega))
  refine HT.of_eq (hc0.seq hloop) ?_ ?_
  · simp only [stCK, Nat.sub_zero, natSyms_zero', List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le (show lc ≤ B by nlinarith))
    have c2 := cost1_le (C := C) (bitLen_le hbB)
    have h2 := loop_Z C B b 0 1 4 rfl hbB (fun _ => 4 * opY C B) (fun i _ => by rw [Zc_zero])
    have h3 := opY_le_Zc C B 1
    omega

/-- The constants of the map of `L`. -/
def constsL (I : HI) : HP I :=
  ((hcp I vl sL1).seq ((hdc I sL1).seq (hdm I sL1 vK vJ vb))).seq
    ((mulDK I).seq ((mulCK I).seq (hcp I slc spf)))

theorem ht_constsL (hI : I.Spec C) (M : MS) (ℓ K D lc B : ℕ) (hl : M.l = natSyms ℓ)
    (hK : M.K = natSyms K) (hD : M.D = natSyms D) (hlc : M.lc = natSyms lc)
    (hL1 : M.L1 = []) (hJ : M.J = []) (hb : M.b = []) (hDK : M.DK = []) (hck : M.ck = [])
    (hpf : M.pf = []) (hc2 : M.c2 = []) (ht : M.t = []) (hl1 : 1 ≤ ℓ) (hK0 : 0 < K)
    (hlB : ℓ ≤ B) (hKB : K ≤ B) (hDB : D ≤ B) (hDKB : D * K ≤ B)
    (hcB : lc + (ℓ - 1) % K * D ≤ B) :
    HT [] (toF M) (constsL I)
      (toF {M with
        L1 := natSyms (ℓ - 1), J := natSyms ((ℓ - 1) / K), b := natSyms ((ℓ - 1) % K),
        DK := natSyms (D * K), ck := natSyms (lc + (ℓ - 1) % K * D), pf := natSyms lc,
        c2 := [], t := []})
      (21 * Zc C B 1) := by
  unfold constsL
  have hbK : (ℓ - 1) % K ≤ B := le_trans (le_of_lt (Nat.mod_lt _ hK0)) hKB
  have h1 := HT.of_eq ((ht_cp0 hI vl sL1 (by decide) (toF M) ℓ [] TermOK.nil
      (by simp [toF, hl]) (by simp [toF, hL1])).seq
     ((ht_dc hI sL1 _ (ℓ - 1) [] TermOK.nil (by simp [toF, Nat.sub_add_cancel hl1])).seq
     (ht_dm0 hI sL1 vK vJ vb (by decide) _ (ℓ - 1) K [] [] hK0 TermOK.nil TermOK.nil
       (by simp) (by simp [toF, hK]) (by simp [toF, hJ]) (by simp [toF, hb]))))
    (show _ = toF {M with
        L1 := natSyms (ℓ - 1), J := natSyms ((ℓ - 1) / K), b := natSyms ((ℓ - 1) % K)} by
      simp only [upd_L1, upd_J, upd_b, List.append_nil]) le_rfl
  refine HT.of_eq (h1.seq
    ((ht_mulDK hI _ D K B (by exact hD) (by exact hK) (by exact hDK) (by exact hc2) (by exact ht)
      hDB hKB hDKB).seq
    ((ht_mulCK hI _ lc ((ℓ - 1) % K) D B (by exact hlc) (by rfl) (by exact hD) (by exact hck)
      (by rfl) (by rfl) hbK hDB hcB).seq
    (ht_cp0 hI slc spf (by decide) _ lc [] TermOK.nil (by simp [toF, hlc])
      (by simp [toF, hpf]))))) ?_ ?_
  · simp only [upd_pf]
  · have c1 := cost1_le (C := C) (bitLen_le hlB)
    have c2 := cost_dc_le (C := C) (B := B) (k := ℓ - 1) (by omega)
    have c3 := cost_dm_le (C := C) (bitLen_le (show ℓ - 1 ≤ B by omega)) (bitLen_le hKB)
    have c4 := cost1_le (C := C) (bitLen_le (show lc ≤ B by omega))
    have h3 := opY_le_Zc C B 1
    omega

end Consts

/-! ## 4. The body of the main pass -/

theorem chunkL_succ (n K dk ck : ℕ) :
    chunkL (n + 1) K dk ck = chunkL n K dk ck ++ (List.range K).map (fun t => ck + n * dk + t) := by
  unfold chunkL
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

section MainBody

variable {I : HI} {C : ℕ}

/-- The long slot: emit `rr` and increment it if `a = ℓ`. -/
def pLongL (I : HI) : HP I := hifEq I vA vl ((wrF I srr so).seq (hic I srr)) (hskip I)

theorem ht_longL (hI : I.Spec C) (M : MS) (x ℓ r B : ℕ) (E : List ℕ) (hA : M.A = natSyms x)
    (hl : M.l = natSyms ℓ) (hr : M.rr = natSyms r) (ho : M.o = savedF E) (hxB : x ≤ B)
    (hlB : ℓ ≤ B) (hrB : r + 1 ≤ B) :
    HT [] (toF M) (pLongL I)
      (toF {M with
        o := savedF (E ++ if x = ℓ then [r] else []),
        rr := natSyms (r + if x = ℓ then 1 else 0)}) (5 * opY C B) := by
  unfold pLongL
  refine HT.of_eq (ht_ifEq hI vA vl (by decide) _ _ x ℓ [] [] TermOK.nil TermOK.nil
    (by simp [toF, hA]) (by simp [toF, hl]) _ _
    (fun h => HT.of_eq ((ht_wrF hI srr so (by decide) _ r [] (savedF E) TermOK.nil
        (by simp [toF, hr]) (by simp [toF, ho])).seq
      (ht_ic hI srr _ r [] TermOK.nil (by simp [toF, hr])))
      (by rw [if_pos h, if_pos h, savedF_concat]; simp only [upd_o, upd_rr, List.append_nil])
      le_rfl)
    (fun h => HT.of_eq (ht_skip _)
      (by rw [if_neg h, if_neg h, List.append_nil, Nat.add_zero, ← ho, ← hr]) le_rfl)) rfl ?_
  have c1 := cost2_le (C := C) (bitLen_le hxB) (bitLen_le hlB)
  have c2 := cost1_le (C := C) (bitLen_le (show r ≤ B by omega))
  have c3 := cost_ic_le (C := C) (show r ≤ B by omega)
  have c4 := one_le_opY C B
  omega

/-- `K` consecutive values from `v`: emit `v`, increment, `K` times. -/
def pInnerK (I : HI) : HP I := (hcp I vK sc3).seq (hcd I sc3 ((wrF I sval so).seq (hic I sval)))

def stIK (M : MS) (E : List ℕ) (v0 K i : ℕ) : LM → List Sym :=
  toF {M with
    v := natSyms (v0 + (K - i)), o := savedF (E ++ (List.range (K - i)).map (fun t => v0 + t)),
    c3 := natSyms i ++ []}

theorem ht_innerK (hI : I.Spec C) (M : MS) (E : List ℕ) (v0 K B : ℕ) (hv : M.v = natSyms v0)
    (hK : M.K = natSyms K) (ho : M.o = savedF E) (hc3 : M.c3 = []) (hKB : K ≤ B)
    (hvB : v0 + K ≤ B) :
    HT [] (toF M) (pInnerK I)
      (toF {M with
        v := natSyms (v0 + K), o := savedF (E ++ (List.range K).map (fun t => v0 + t)),
        c3 := []}) (8 * Zc C B 1) := by
  unfold pInnerK hcd
  have hc0 := HT.of_eq (ht_cp0 hI vK sc3 (by decide) (toF M) K [] TermOK.nil (by simp [toF, hK])
      (by simp [toF, hc3]))
    (show _ = stIK M E v0 K K by
      rw [upd_c3]; unfold stIK; congr 1; ext <;> simp [hv, ho]) le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc sc3 d0 [] TermOK.nil (stIK M E v0 K)
    (fun i => by simp [stIK, toF]) ((wrF I sval so).seq (hic I sval)) (fun _ => 3 * opY C B) K (by
      intro i hi
      have hj : K - i = K - (i + 1) + 1 := by omega
      have e1 : v0 + (K - (i + 1)) + 1 = v0 + (K - i) := by omega
      simp only [stIK, upd_c3]
      refine HT.of_eq ((ht_wrF hI sval so (by decide) _ (v0 + (K - (i + 1))) []
          (savedF (E ++ (List.range (K - (i + 1))).map (fun t => v0 + t))) TermOK.nil
          (by simp [toF]) (by simp [toF])).seq
        (ht_ic hI sval _ (v0 + (K - (i + 1))) [] TermOK.nil (by simp [toF]))) ?_ ?_
      · simp only [upd_o, upd_v, List.append_nil]
        rw [e1, hj, List.range_succ, List.map_append, List.map_singleton, ← List.append_assoc,
          savedF_concat]
      · have c1 := cost1_le (C := C) (bitLen_le (show v0 + (K - (i + 1)) ≤ B by omega))
        have c2 := cost_ic_le (C := C) (show v0 + (K - (i + 1)) ≤ B by omega)
        have c3 := one_le_opY C B
        omega)
  refine HT.of_eq (hc0.seq hloop) ?_ ?_
  · simp only [stIK, Nat.sub_zero, natSyms_zero', List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le hKB)
    have h2 := loop_Z C B K 0 1 3 rfl hKB (fun _ => 3 * opY C B) (fun i _ => by rw [Zc_zero])
    have h3 := opY_le_Zc C B 1
    omega

/-- One chunk block: `K` consecutive values from `cj`, then `cj += DK`. -/
def pChunkJ (I : HI) : HP I :=
  (hcp I scj sval).seq ((pInnerK I).seq ((hdr I sval).seq (addTo I scj vDK)))

theorem ht_chunkJ (hI : I.Spec C) (M : MS) (E : List ℕ) (c0 K dk B : ℕ)
    (hcj : M.cj = natSyms c0) (hv : M.v = []) (hK : M.K = natSyms K) (hDK : M.DK = natSyms dk)
    (ho : M.o = savedF E) (hc3 : M.c3 = []) (ht : M.t = []) (hKB : K ≤ B) (hvB : c0 + K ≤ B)
    (hdB : dk ≤ B) (hcdB : c0 + dk ≤ B) :
    HT [] (toF M) (pChunkJ I)
      (toF {M with
        cj := natSyms (c0 + dk), v := [], o := savedF (E ++ (List.range K).map (fun t => c0 + t)),
        c3 := [], t := []}) (15 * Zc C B 1) := by
  unfold pChunkJ
  refine HT.of_eq
    ((HT.of_eq (ht_cp0 hI scj sval (by decide) (toF M) c0 [] TermOK.nil (by simp [toF, hcj])
        (by simp [toF, hv])) (upd_v M _) le_rfl).seq
    ((ht_innerK hI _ E c0 K B (by rfl) (by exact hK) (by exact ho) (by exact hc3) hKB hvB).seq
    ((HT.of_eq (ht_dr hI sval _ (c0 + K) [] TermOK.nil (by simp [toF])) (upd_v _ _) le_rfl).seq
    (ht_addTo hI scj vDK (by decide) _ c0 dk [] TermOK.nil (by simp [toF, hcj])
      (by simp [toF, hDK]) (by simp [toF, ht]))))) ?_ ?_
  · simp only [upd_t, upd_cj]
  · have c1 := cost1_le (C := C) (bitLen_le (show c0 ≤ B by omega))
    have c2 := cost1_le (C := C) (bitLen_le hvB)
    have c3 := cost_addTo_le (C := C) (show c0 ≤ B by omega) hdB hcdB
    have h3 := opY_le_Zc C B 1
    omega

/-- The chunk part of one axis: `J` blocks from `ck`. -/
def pChunkL (I : HI) : HP I :=
  ((hcp I sck scj).seq (hcp I vJ sc2)).seq ((hcd I sc2 (pChunkJ I)).seq (hdr I scj))

def stCL (M : MS) (E : List ℕ) (ck0 J K dk i : ℕ) : LM → List Sym :=
  toF {M with
    cj := natSyms (ck0 + (J - i) * dk), v := [], o := savedF (E ++ chunkL (J - i) K dk ck0),
    c2 := natSyms i ++ [], c3 := [], t := []}

theorem ht_chunkL (hI : I.Spec C) (M : MS) (E : List ℕ) (ck0 J K dk B : ℕ)
    (hck : M.ck = natSyms ck0) (hJ : M.J = natSyms J) (hcj : M.cj = []) (hc2 : M.c2 = [])
    (hv : M.v = []) (hK : M.K = natSyms K) (hDK : M.DK = natSyms dk) (ho : M.o = savedF E)
    (hc3 : M.c3 = []) (ht : M.t = []) (hJB : J ≤ B) (hKB : K ≤ B) (hdB : dk ≤ B)
    (hcB : ck0 + J * dk + K ≤ B) :
    HT [] (toF M) (pChunkL I)
      (toF {M with
        cj := [], v := [], o := savedF (E ++ chunkL J K dk ck0), c2 := [], c3 := [], t := []})
      (22 * Zc C B 2) := by
  unfold pChunkL hcd
  have hc0 := HT.of_eq ((ht_cp0 hI sck scj (by decide) (toF M) ck0 [] TermOK.nil
      (by simp [toF, hck]) (by simp [toF, hcj])).seq
      (ht_cp0 hI vJ sc2 (by decide) _ J [] TermOK.nil (by simp [toF, hJ]) (by simp [toF, hc2])))
    (show _ = stCL M E ck0 J K dk J by
      rw [upd_cj, upd_c2]; unfold stCL; congr 1; ext <;> simp [hv, ho, hc3, ht, chunkL]) le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc sc2 d0 [] TermOK.nil (stCL M E ck0 J K dk)
    (fun i => by simp [stCL, toF]) (pChunkJ I) (fun _ => 15 * Zc C B 1) J (by
      intro i hi
      have hj : J - i = J - (i + 1) + 1 := by omega
      have hle : (J - (i + 1)) * dk + dk ≤ J * dk := by
        have := Nat.mul_le_mul_right dk (show J - (i + 1) + 1 ≤ J by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      have e1 : ck0 + (J - (i + 1)) * dk + dk = ck0 + (J - i) * dk := by
        rw [hj, Nat.add_mul, Nat.one_mul]; omega
      simp only [stCL, upd_c2]
      refine HT.of_eq (ht_chunkJ hI _ (E ++ chunkL (J - (i + 1)) K dk ck0)
        (ck0 + (J - (i + 1)) * dk) K dk B (by rfl) (by rfl) (by exact hK) (by exact hDK) (by rfl)
        (by rfl) (by rfl) hKB (by omega) hdB (by omega)) ?_ le_rfl
      rw [e1, hj, chunkL_succ, List.append_assoc])
  refine HT.of_eq (hc0.seq (hloop.seq (ht_dr hI scj _ (ck0 + (J - 0) * dk) [] TermOK.nil
    (by simp [stCL, toF])))) ?_ ?_
  · simp only [stCL, upd_cj, Nat.sub_zero, natSyms_zero', List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le (show ck0 ≤ B by omega))
    have c2 := cost1_le (C := C) (bitLen_le hJB)
    have c3 := cost1_le (C := C) (bitLen_le (show ck0 + (J - 0) * dk ≤ B by
      rw [Nat.sub_zero]; omega))
    have h2 := loop_Z C B J 1 2 15 rfl hJB (fun _ => 15 * Zc C B 1) (fun i _ => le_rfl)
    have h3 := opY_le_Zc C B 2
    omega

/-- The prefix part of one axis: `b` values of stride `D` from `pf`. -/
def pPrefL (I : HI) : HP I :=
  ((hcp I spf sval).seq (hcp I vb sc2)).seq
    ((hcd I sc2 ((wrF I sval so).seq (addTo I sval vD))).seq (hdr I sval))

def stPL (M : MS) (E : List ℕ) (pf0 b D i : ℕ) : LM → List Sym :=
  toF {M with
    v := natSyms (pf0 + (b - i) * D),
    o := savedF (E ++ (List.range (b - i)).map (fun s => pf0 + s * D)),
    c2 := natSyms i ++ [], t := []}

theorem ht_prefL (hI : I.Spec C) (M : MS) (E : List ℕ) (pf0 b D B : ℕ)
    (hpf : M.pf = natSyms pf0) (hb : M.b = natSyms b) (hD : M.D = natSyms D) (hv : M.v = [])
    (hc2 : M.c2 = []) (ho : M.o = savedF E) (ht : M.t = []) (hbB : b ≤ B) (hDB : D ≤ B)
    (hpB : pf0 + b * D ≤ B) :
    HT [] (toF M) (pPrefL I)
      (toF {M with v := [], o := savedF (E ++ prefL b D pf0), c2 := [], t := []})
      (12 * Zc C B 1) := by
  unfold pPrefL hcd
  have hc0 := HT.of_eq ((ht_cp0 hI spf sval (by decide) (toF M) pf0 [] TermOK.nil
      (by simp [toF, hpf]) (by simp [toF, hv])).seq
      (ht_cp0 hI vb sc2 (by decide) _ b [] TermOK.nil (by simp [toF, hb]) (by simp [toF, hc2])))
    (show _ = stPL M E pf0 b D b by
      rw [upd_v, upd_c2]; unfold stPL; congr 1; ext <;> simp [ho, ht]) le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc sc2 d0 [] TermOK.nil (stPL M E pf0 b D)
    (fun i => by simp [stPL, toF]) ((wrF I sval so).seq (addTo I sval vD)) (fun _ => 6 * opY C B)
    b (by
      intro i hi
      have hj : b - i = b - (i + 1) + 1 := by omega
      have hle : (b - (i + 1)) * D + D ≤ b * D := by
        have := Nat.mul_le_mul_right D (show b - (i + 1) + 1 ≤ b by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      have e1 : pf0 + (b - (i + 1)) * D + D = pf0 + (b - i) * D := by
        rw [hj, Nat.add_mul, Nat.one_mul]; omega
      simp only [stPL, upd_c2]
      refine HT.of_eq ((ht_wrF hI sval so (by decide) _ (pf0 + (b - (i + 1)) * D) []
          (savedF (E ++ (List.range (b - (i + 1))).map (fun s => pf0 + s * D))) TermOK.nil
          (by simp [toF]) (by simp [toF])).seq
        (ht_addTo hI sval vD (by decide) _ (pf0 + (b - (i + 1)) * D) D [] TermOK.nil (by simp [toF])
          (by simp [toF, hD]) (by simp [toF]))) ?_ ?_
      · simp only [upd_o, upd_v, upd_t]
        rw [e1, hj, List.range_succ, List.map_append, List.map_singleton, ← List.append_assoc,
          savedF_concat]
      · have c1 := cost1_le (C := C) (bitLen_le (show pf0 + (b - (i + 1)) * D ≤ B by omega))
        have c2 := cost_addTo_le (C := C) (show pf0 + (b - (i + 1)) * D ≤ B by omega) hDB
          (by omega)
        have c3 := one_le_opY C B
        omega)
  refine HT.of_eq (hc0.seq (hloop.seq (ht_dr hI sval _ (pf0 + (b - 0) * D) [] TermOK.nil
    (by simp [stPL, toF])))) ?_ ?_
  · simp only [stPL, upd_v, Nat.sub_zero, natSyms_zero', List.append_nil]
    rfl
  · have c1 := cost1_le (C := C) (bitLen_le (show pf0 ≤ B by nlinarith))
    have c2 := cost1_le (C := C) (bitLen_le hbB)
    have c3 := cost1_le (C := C) (bitLen_le (show pf0 + (b - 0) * D ≤ B by
      rw [Nat.sub_zero]; omega))
    have h2 := loop_Z C B b 0 1 6 rfl hbB (fun _ => 6 * opY C B) (fun i _ => by rw [Zc_zero])
    have h3 := opY_le_Zc C B 1
    omega

/-- **The body of the main pass of `L`** (one axis). -/
def pBdL (I : HI) : HP I :=
  (pLongL I).seq ((pChunkL I).seq ((pPrefL I).seq ((addTo I sck vK).seq (hic I spf))))

theorem ht_bdL (hI : I.Spec C) (M : MS) (E : List ℕ) (x ℓ r ck0 pf0 J K dk b D B : ℕ)
    (hA : M.A = natSyms x) (hl : M.l = natSyms ℓ) (hr : M.rr = natSyms r)
    (ho : M.o = savedF E) (hck : M.ck = natSyms ck0) (hpf : M.pf = natSyms pf0)
    (hJ : M.J = natSyms J) (hK : M.K = natSyms K) (hDK : M.DK = natSyms dk)
    (hb : M.b = natSyms b) (hD : M.D = natSyms D) (hcj : M.cj = []) (hv : M.v = [])
    (hc2 : M.c2 = []) (hc3 : M.c3 = []) (ht : M.t = [])
    (hxB : x ≤ B) (hlB : ℓ ≤ B) (hrB : r + 1 ≤ B) (hJB : J ≤ B) (hKB : K ≤ B) (hdB : dk ≤ B)
    (hbB : b ≤ B) (hDB : D ≤ B) (hcB : ck0 + J * dk + K ≤ B) (hpB : pf0 + b * D ≤ B)
    (hp1 : pf0 + 1 ≤ B) :
    HT [] (toF M) (pBdL I)
      (toF {M with
        o := savedF (E ++ axL ℓ J K dk b D x r ck0 pf0),
        rr := natSyms (r + if x = ℓ then 1 else 0), ck := natSyms (ck0 + K),
        pf := natSyms (pf0 + 1), cj := [], v := [], c2 := [], c3 := [], t := []})
      (50 * Zc C B 2) := by
  unfold pBdL
  refine HT.of_eq ((ht_longL hI M x ℓ r B E hA hl hr ho hxB hlB hrB).seq
    ((ht_chunkL hI _ (E ++ if x = ℓ then [r] else []) ck0 J K dk B (by exact hck) (by exact hJ)
      (by exact hcj) (by exact hc2) (by exact hv) (by exact hK) (by exact hDK) (by rfl)
      (by exact hc3) (by exact ht) hJB hKB hdB hcB).seq
    ((ht_prefL hI _ ((E ++ if x = ℓ then [r] else []) ++ chunkL J K dk ck0) pf0 b D B
      (by exact hpf) (by exact hb) (by exact hD) (by rfl) (by rfl) (by rfl) (by rfl) hbB hDB
      hpB).seq
    ((ht_addTo hI sck vK (by decide) _ ck0 K [] TermOK.nil (by simp [toF, hck])
      (by simp [toF, hK]) (by simp [toF])).seq
    (ht_ic hI spf _ pf0 [] TermOK.nil (by simp [toF, hpf])))))) ?_ ?_
  · simp only [upd_t, upd_ck, upd_pf, List.append_nil, axL, List.append_assoc]
  · have c1 := cost_addTo_le (C := C) (show ck0 ≤ B by omega) hKB (by omega)
    have c2 := cost_ic_le (C := C) (show pf0 ≤ B by omega)
    have h1 := opY_le_Zc C B 2
    have h2 : Zc C B 1 ≤ Zc C B 2 := Zc_mono C B 1
    omega

end MainBody

end SubNLogN.Machine.FFT.LayoutMapAux
