/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.LayoutMapL

/-!
# K4.3c-U bodies (`Machine/FFT/LayoutMapUBody.lean`): passes and loops of the map builder of `U`

The bodies of the builder of the runtime map of the layout `U = (L ∘ B)^{-1}`
(`LayoutMapGenStmt .U`, `Machine/FFT/LayoutCompile.lean`), on the host of
`Machine/FFT/LayoutMapBase.lean`. A pass over the axis exponents (`passU`: `passB`, restore, drop
the offset) keeps the running offset `off_i = Σ_{i' < i} a_{i'}` on `srr` and emits onto the scratch
stack `so`:
* `bdU1`: `off_i + ℓ - 1` if `a_i = ℓ` (the long slots, `genU1` of `Machine/FFT/LayoutMapMath.lean`);
* `bdU2`: `off_i + v` with `v` the counter of the prefix-round loop `loopV`, which runs
  `b₀ - 1, …, 0` (`genU2`);
* `bdU3`: `off_i + c - 1, …, off_i + c - K` by an inner count-down loop that decrements, then emits
  (`genU3`). The chunk loop `loopJ` runs these passes for `c = ℓ - 1 - jK`, `j < J_blk`, and lowers
  `c` by `K` after each pass (`pDecK`).
Every rule is an exact-stacks triple on the records `MS`, with costs in the units `Zc C B n` of
`Machine/FFT/LayoutMapL.lean`. Fully proved, no placeholders.
-/

namespace SubNLogN.Machine.FFT.LayoutMapUAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Math.Walsh
open SubNLogN.Machine.FFT.LayoutHdrAux (savedF savedF_nil savedF_concat natSyms_zero'
  hdrSyms_cons' hdrSyms_nil' midHdr_eq' opY cost1_le cost2_le one_le_opY bitLen_le
  loopCost_le_of_le sum_take_le' take_succ_sum' drop_hdr' savedF_take_succ' C_le_opY hdr_assoc)
open SubNLogN.Machine.FFT.LayoutMapMath SubNLogN.Math.Walsh.IntForms
open SubNLogN.Machine.FFT.LayoutMapAux

theorem ht_preU {I : HI} {B0 B B' : LM → List Sym} {p : HP I} {T : ℕ} (h : HT [] B p B' T)
    (e : B0 = B) : HT [] B0 p B' T := e ▸ h

theorem tsum_succ (as : List ℕ) (j : ℕ) (hj : j < as.length) :
    (as.take (j + 1)).sum = (as.take j).sum + as[j] := by
  rw [take_succ_sum' as j hj, Nat.add_comm]

theorem genU1_take_succ (ℓ : ℕ) (as : List ℕ) (j : ℕ) (hj : j < as.length) :
    genU1 ℓ (as.take (j + 1)) =
      genU1 ℓ (as.take j) ++ (if as[j] = ℓ then [(as.take j).sum + (ℓ - 1)] else []) := by
  rw [List.take_succ_eq_append_getElem hj, genU1_concat]

theorem genU2_take_succ (as : List ℕ) (v j : ℕ) (hj : j < as.length) :
    genU2 (as.take (j + 1)) v = genU2 (as.take j) v ++ [(as.take j).sum + v] := by
  rw [List.take_succ_eq_append_getElem hj, genU2_concat]

theorem genU3_take_succ (K : ℕ) (as : List ℕ) (c j : ℕ) (hj : j < as.length) :
    genU3 K (as.take (j + 1)) c =
      genU3 K (as.take j) c ++ (List.range K).map (fun t => (as.take j).sum + c - (t + 1)) := by
  rw [List.take_succ_eq_append_getElem hj, genU3_concat]

/-- `[b-1, b-2, …, i]`. -/
def vtail (b i : ℕ) : List ℕ := (List.range (b - i)).map (fun u => b - 1 - u)

theorem vtail_self (b : ℕ) : vtail b b = [] := by simp [vtail]

theorem vtail_zero (b : ℕ) : vtail b 0 = (List.range b).reverse := by
  rw [vtail, Nat.sub_zero, range_reverse_eq]

theorem vtail_succ (b i : ℕ) (hi : i < b) : vtail b i = vtail b (i + 1) ++ [i] := by
  have h1 : b - i = b - (i + 1) + 1 := by omega
  have h2 : b - 1 - (b - (i + 1)) = i := by omega
  unfold vtail
  rw [h1, List.range_succ, List.map_append, List.map_singleton, h2]

section Bodies

variable {I : HI} {C : ℕ}

/-- Long-slot body: emit `off + (ℓ - 1)` if `a = ℓ`, then `off += a` (`off` on `srr`). -/
def bdU1 (I : HI) : HP I :=
  (hifEq I vA vl ((had I srr sL1 sval).seq ((wrF I sval so).seq (hdr I sval))) (hskip I)).seq
    (addTo I srr vA)

theorem ht_bdU1 (hI : I.Spec C) (M : MS) (E : List ℕ) (x ℓ r B : ℕ)
    (hA : M.A = natSyms x) (hl : M.l = natSyms ℓ) (hL1 : M.L1 = natSyms (ℓ - 1))
    (hr : M.rr = natSyms r) (ho : M.o = savedF E) (hv : M.v = []) (ht : M.t = [])
    (hxB : x ≤ B) (hlB : ℓ ≤ B) (hrB : r + ℓ ≤ B) (hrx : r + x ≤ B) :
    HT [] (toF M) (bdU1 I)
      (toF {M with
        v := [], o := savedF (E ++ if x = ℓ then [r + (ℓ - 1)] else []),
        rr := natSyms (r + x), t := []}) (12 * opY C B) := by
  unfold bdU1
  refine HT.of_eq ((ht_ifEq hI vA vl (by decide) _
      (toF {M with v := [], o := savedF (E ++ if x = ℓ then [r + (ℓ - 1)] else [])})
      x ℓ [] [] TermOK.nil TermOK.nil (by simp [toF, hA]) (by simp [toF, hl]) _ _
      (fun h => HT.of_eq
        ((ht_ad0 hI srr sL1 sval (by decide) (toF M) r (ℓ - 1) [] [] TermOK.nil TermOK.nil
          (by simp [toF, hr]) (by simp [toF, hL1]) (by simp [toF, hv])).seq
        ((ht_wrF hI sval so (by decide) _ (r + (ℓ - 1)) [] (savedF E) TermOK.nil
          (by simp) (by simp [toF, ho])).seq
        (ht_dr hI sval _ (r + (ℓ - 1)) [] TermOK.nil (by simp))))
        (by rw [if_pos h]; simp only [upd_v, upd_o, savedF_concat]) le_rfl)
      (fun h => HT.of_eq (ht_skip _)
        (by rw [if_neg h, List.append_nil]; congr 1; ext <;> simp [hv, ho]) le_rfl)).seq
    (ht_addTo hI srr vA (by decide) _ r x [] TermOK.nil (by simp [toF, hr])
      (by simp [toF, hA]) (by simp [toF, ht]))) ?_ ?_
  · simp only [upd_t, upd_rr]
  · have c1 := cost2_le (C := C) (bitLen_le hxB) (bitLen_le hlB)
    have c2 := cost2_le (C := C) (bitLen_le (show r ≤ B by omega))
      (bitLen_le (show ℓ - 1 ≤ B by omega))
    have c3 := cost1_le (C := C) (bitLen_le (show r + (ℓ - 1) ≤ B by omega))
    have c4 := cost_addTo_le (C := C) (show r ≤ B by omega) hxB hrx
    have c5 := one_le_opY C B
    omega

/-- Prefix-round body: emit `off + v` (`v` on `sc2`), then `off += a`. -/
def bdU2 (I : HI) : HP I :=
  (had I srr sc2 sval).seq ((wrF I sval so).seq ((hdr I sval).seq (addTo I srr vA)))

theorem ht_bdU2 (hI : I.Spec C) (M : MS) (E : List ℕ) (x v r B : ℕ)
    (hA : M.A = natSyms x) (hc2 : M.c2 = natSyms v ++ []) (hr : M.rr = natSyms r)
    (ho : M.o = savedF E) (hv : M.v = []) (ht : M.t = [])
    (hxB : x ≤ B) (hvB : r + v ≤ B) (hrx : r + x ≤ B) :
    HT [] (toF M) (bdU2 I)
      (toF {M with v := [], o := savedF (E ++ [r + v]), rr := natSyms (r + x), t := []})
      (10 * opY C B) := by
  unfold bdU2
  refine HT.of_eq
    ((ht_ad0 hI srr sc2 sval (by decide) (toF M) r v [] [] TermOK.nil TermOK.nil
        (by simp [toF, hr]) (by simp [toF, hc2]) (by simp [toF, hv])).seq
    ((ht_wrF hI sval so (by decide) _ (r + v) [] (savedF E) TermOK.nil (by simp)
        (by simp [toF, ho])).seq
    ((ht_dr hI sval _ (r + v) [] TermOK.nil (by simp)).seq
    (ht_addTo hI srr vA (by decide) _ r x [] TermOK.nil (by simp [toF, hr])
        (by simp [toF, hA]) (by simp [toF, ht]))))) ?_ ?_
  · simp only [upd_v, upd_o, upd_rr, upd_t, savedF_concat]
  · have c1 := cost2_le (C := C) (bitLen_le (show r ≤ B by omega))
      (bitLen_le (show v ≤ B by omega))
    have c2 := cost1_le (C := C) (bitLen_le hvB)
    have c3 := cost_addTo_le (C := C) (show r ≤ B by omega) hxB hrx
    have c4 := one_le_opY C B
    omega

/-- `K` values below `v0`: decrement `sval`, emit it; `K` times (counter `sc3`). -/
def pInnerD (I : HI) : HP I := (hcp I vK sc3).seq (hcd I sc3 ((hdc I sval).seq (wrF I sval so)))

def stID (M : MS) (E : List ℕ) (v0 K i : ℕ) : LM → List Sym :=
  toF {M with
    v := natSyms (v0 - (K - i)),
    o := savedF (E ++ (List.range (K - i)).map (fun t => v0 - (t + 1))),
    c3 := natSyms i ++ []}

theorem ht_innerD (hI : I.Spec C) (M : MS) (E : List ℕ) (v0 K B : ℕ) (hv : M.v = natSyms v0)
    (hK : M.K = natSyms K) (ho : M.o = savedF E) (hc3 : M.c3 = []) (hKB : K ≤ B)
    (hvB : v0 ≤ B) (hKv : K ≤ v0) :
    HT [] (toF M) (pInnerD I)
      (toF {M with
        v := natSyms (v0 - K), o := savedF (E ++ (List.range K).map (fun t => v0 - (t + 1))),
        c3 := []}) (8 * Zc C B 1) := by
  unfold pInnerD hcd
  have hc0 := HT.of_eq (ht_cp0 hI vK sc3 (by decide) (toF M) K [] TermOK.nil (by simp [toF, hK])
      (by simp [toF, hc3]))
    (show _ = stID M E v0 K K by
      rw [upd_c3]; unfold stID; congr 1; ext <;> simp [hv, ho]) le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc sc3 d0 [] TermOK.nil (stID M E v0 K)
    (fun i => by simp [stID, toF]) ((hdc I sval).seq (wrF I sval so)) (fun _ => 3 * opY C B) K (by
      intro i hi
      have hj : K - i = K - (i + 1) + 1 := by omega
      have e1 : v0 - (K - (i + 1)) = v0 - (K - i) + 1 := by omega
      simp only [stID, upd_c3]
      refine HT.of_eq ((ht_dc hI sval _ (v0 - (K - i)) [] TermOK.nil
          (by rw [← e1]; simp [toF])).seq
        (ht_wrF hI sval so (by decide) _ (v0 - (K - i)) []
          (savedF (E ++ (List.range (K - (i + 1))).map (fun t => v0 - (t + 1)))) TermOK.nil
          (by simp) (by simp [toF]))) ?_ ?_
      · simp only [upd_o, upd_v, List.append_nil]
        rw [hj, List.range_succ, List.map_append, List.map_singleton, ← List.append_assoc,
          savedF_concat]
      · have c1 := cost_dc_le (C := C) (B := B) (k := v0 - (K - i)) (by omega)
        have c2 := cost1_le (C := C) (bitLen_le (show v0 - (K - i) ≤ B by omega))
        have c3 := one_le_opY C B
        omega)
  refine HT.of_eq (hc0.seq hloop) ?_ ?_
  · simp only [stID, Nat.sub_zero, natSyms_zero', List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le hKB)
    have h2 := loop_Z C B K 0 1 3 rfl hKB (fun _ => 3 * opY C B) (fun i _ => by rw [Zc_zero])
    have h3 := opY_le_Zc C B 1
    omega

/-- Chunk body: `sval := off + c`; emit `off + c - 1, …, off + c - K`; then `off += a`. -/
def bdU3 (I : HI) : HP I :=
  (had I srr scs sval).seq ((pInnerD I).seq ((hdr I sval).seq (addTo I srr vA)))

theorem ht_bdU3 (hI : I.Spec C) (M : MS) (E : List ℕ) (x c r K B : ℕ)
    (hA : M.A = natSyms x) (hcs : M.cs = natSyms c) (hr : M.rr = natSyms r)
    (hK : M.K = natSyms K) (ho : M.o = savedF E) (hv : M.v = []) (hc3 : M.c3 = [])
    (ht : M.t = []) (hxB : x ≤ B) (hKB : K ≤ B) (hcB : r + c ≤ B) (hrx : r + x ≤ B)
    (hKc : K ≤ c) :
    HT [] (toF M) (bdU3 I)
      (toF {M with
        v := [], o := savedF (E ++ (List.range K).map (fun t => r + c - (t + 1))),
        rr := natSyms (r + x), c3 := [], t := []}) (14 * Zc C B 1) := by
  unfold bdU3
  refine HT.of_eq
    ((HT.of_eq (ht_ad0 hI srr scs sval (by decide) (toF M) r c [] [] TermOK.nil TermOK.nil
        (by simp [toF, hr]) (by simp [toF, hcs]) (by simp [toF, hv])) (upd_v M _) le_rfl).seq
    ((ht_innerD hI _ E (r + c) K B (by rfl) (by exact hK) (by exact ho) (by exact hc3) hKB hcB
        (by omega)).seq
    ((HT.of_eq (ht_dr hI sval _ (r + c - K) [] TermOK.nil (by simp [toF])) (upd_v _ _)
        le_rfl).seq
    (ht_addTo hI srr vA (by decide) _ r x [] TermOK.nil (by simp [toF, hr])
        (by simp [toF, hA]) (by simp [toF, ht]))))) ?_ ?_
  · simp only [upd_t, upd_rr]
  · have c1 := cost2_le (C := C) (bitLen_le (show r ≤ B by omega))
      (bitLen_le (show c ≤ B by omega))
    have c2 := cost1_le (C := C) (bitLen_le (show r + c - K ≤ B by omega))
    have c3 := cost_addTo_le (C := C) (show r ≤ B by omega) hxB hrx
    have h3 := opY_le_Zc C B 1
    omega

/-- `cs := cs - K` by `K` decrements (counter `sc3`). -/
def pDecK (I : HI) : HP I := (hcp I vK sc3).seq (hcd I sc3 (hdc I scs))

def stDec (M : MS) (c K i : ℕ) : LM → List Sym :=
  toF {M with cs := natSyms (c - (K - i)), c3 := natSyms i ++ []}

theorem ht_decK (hI : I.Spec C) (M : MS) (c K B : ℕ) (hcs : M.cs = natSyms c)
    (hK : M.K = natSyms K) (hc3 : M.c3 = []) (hKB : K ≤ B) (hcB : c ≤ B) (hKc : K ≤ c) :
    HT [] (toF M) (pDecK I) (toF {M with cs := natSyms (c - K), c3 := []}) (6 * Zc C B 1) := by
  unfold pDecK hcd
  have hc0 := HT.of_eq (ht_cp0 hI vK sc3 (by decide) (toF M) K [] TermOK.nil (by simp [toF, hK])
      (by simp [toF, hc3]))
    (show _ = stDec M c K K by
      rw [upd_c3]; unfold stDec; congr 1; ext <;> simp [hcs]) le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc sc3 d0 [] TermOK.nil (stDec M c K)
    (fun i => by simp [stDec, toF]) (hdc I scs) (fun _ => 2 * opY C B) K (by
      intro i hi
      have e1 : c - (K - (i + 1)) = c - (K - i) + 1 := by omega
      simp only [stDec, upd_c3]
      refine HT.of_eq (ht_dc hI scs _ (c - (K - i)) [] TermOK.nil (by rw [← e1]; simp [toF]))
        ?_ ?_
      · simp only [upd_cs, List.append_nil]
      · have c1 := cost_dc_le (C := C) (B := B) (k := c - (K - i)) (by omega)
        omega)
  refine HT.of_eq (hc0.seq hloop) ?_ ?_
  · simp only [stDec, Nat.sub_zero, natSyms_zero', List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le hKB)
    have h2 := loop_Z C B K 0 1 2 rfl hKB (fun _ => 2 * opY C B) (fun i _ => by rw [Zc_zero])
    have h3 := opY_le_Zc C B 1
    omega

end Bodies

section Passes

variable {I : HI} {C : ℕ}

/-- A pass with the running offset on `srr`: `passB bd`, the restore, drop the offset. -/
def passU (I : HI) (bd : HP I) : HP I := (passB I bd).seq ((passC I).seq (hdr I srr))

theorem ht_passU (hI : I.Spec C) (bd : HP I) (g : List ℕ → List ℕ) (hg0 : g [] = [])
    (M : MS) (as : List ℕ) (D B cb : ℕ) (E : List ℕ) (H0 : List Sym)
    (hlen : as.length = D) (hDB : D ≤ B) (hxB : ∀ x ∈ as, x ≤ B) (hsB : as.sum ≤ B)
    (hh : M.h = hdrSyms as ++ H0) (hA : M.A = []) (hs : M.s = []) (hc : M.c = [])
    (hD : M.D = natSyms D) (hr : M.rr = []) (ho : M.o = savedF E) (hv : M.v = [])
    (hc3 : M.c3 = []) (ht : M.t = [])
    (hbd : ∀ j (hj : j < as.length) (i : ℕ), HT []
      (toF {M with
        h := natSyms as[j] ++ Sym.mark :: (hdrSyms (as.drop (j + 1)) ++ H0),
        A := natSyms as[j], s := savedF (as.take j), c := natSyms i ++ [],
        rr := natSyms ((as.take j).sum), o := savedF (E ++ g (as.take j)),
        v := [], c3 := [], t := []}) bd
      (toF {M with
        h := natSyms as[j] ++ Sym.mark :: (hdrSyms (as.drop (j + 1)) ++ H0),
        A := natSyms as[j], s := savedF (as.take j), c := natSyms i ++ [],
        rr := natSyms ((as.take (j + 1)).sum), o := savedF (E ++ g (as.take (j + 1))),
        v := [], c3 := [], t := []}) cb) :
    HT [] (toF M) (passU I bd) (toF {M with o := savedF (E ++ g as)})
      ((B + 1) * (cb + 19 * opY C B)) := by
  unfold passU
  have e0 : toF M = toF {M with
      rr := natSyms ((as.take 0).sum), o := savedF (E ++ g (as.take 0)), v := [], c3 := [],
      t := [], h := hdrSyms as ++ H0, A := [], s := [], c := []} := by
    congr 1
    ext <;> simp [hh, hA, hs, hc, hr, ho, hv, hc3, ht, hg0, natSyms_zero']
  refine HT.of_eq ((ht_preU (ht_passB hI bd as D B cb H0
      (fun j => {M with
        rr := natSyms ((as.take j).sum), o := savedF (E ++ g (as.take j)), v := [], c3 := [],
        t := []}) hlen hDB hxB hD hbd) e0).seq
    ((ht_passC hI {M with
        rr := natSyms ((as.take D).sum), o := savedF (E ++ g (as.take D)), v := [], c3 := [],
        t := [], A := [], c := []} as D B H0 hlen hDB hxB hD rfl).seq
    (ht_dr hI srr _ ((as.take D).sum) [] TermOK.nil (by simp [toF])))) ?_ ?_
  · rw [upd_rr]
    congr 1
    ext <;> simp [hh, hA, hs, hc, hr, hv, hc3, ht, List.take_of_length_le (le_of_eq hlen)]
  · have c1 := cost1_le (C := C) (bitLen_le (le_trans (sum_take_le' as D) hsB))
    have h1 : (B + 1) * (cb + 19 * opY C B) = (B + 1) * (cb + 10 * opY C B) +
        (B + 1) * (8 * opY C B) + (B + 1) * opY C B := by ring
    have h2 : opY C B ≤ (B + 1) * opY C B := Nat.le_mul_of_pos_left _ (by omega)
    omega

theorem ht_pass1U (hI : I.Spec C) (M : MS) (as : List ℕ) (D ℓ B : ℕ) (E : List ℕ)
    (H0 : List Sym) (hlen : as.length = D) (hDB : D ≤ B) (hxB : ∀ x ∈ as, x ≤ B)
    (hsB : as.sum + ℓ ≤ B)
    (hh : M.h = hdrSyms as ++ H0) (hA : M.A = []) (hs : M.s = []) (hc : M.c = [])
    (hD : M.D = natSyms D) (hr : M.rr = []) (ho : M.o = savedF E) (hv : M.v = [])
    (hc3 : M.c3 = []) (ht : M.t = []) (hl : M.l = natSyms ℓ) (hL1 : M.L1 = natSyms (ℓ - 1)) :
    HT [] (toF M) (passU I (bdU1 I)) (toF {M with o := savedF (E ++ genU1 ℓ as)})
      ((B + 1) * (12 * opY C B + 19 * opY C B)) := by
  refine ht_passU hI (bdU1 I) (genU1 ℓ) (by simp [genU1]) M as D B (12 * opY C B) E H0 hlen hDB
    hxB (by omega) hh hA hs hc hD hr ho hv hc3 ht (fun j hj i => ?_)
  have hxj := hxB _ (List.getElem_mem hj)
  have hs0 := sum_take_le' as j
  have hs1 := sum_take_le' as (j + 1)
  rw [tsum_succ as j hj] at hs1
  refine HT.of_eq (ht_bdU1 hI _ (E ++ genU1 ℓ (as.take j)) as[j] ℓ ((as.take j).sum) B
    (by rfl) (by exact hl) (by exact hL1) (by rfl) (by rfl) (by rfl) (by rfl) hxj (by omega)
    (by omega) (by omega)) ?_ le_rfl
  rw [tsum_succ as j hj, genU1_take_succ ℓ as j hj, List.append_assoc]

theorem ht_pass2U (hI : I.Spec C) (M : MS) (as : List ℕ) (D v B : ℕ) (E : List ℕ)
    (H0 : List Sym) (hlen : as.length = D) (hDB : D ≤ B) (hxB : ∀ x ∈ as, x ≤ B)
    (hsB : as.sum + v ≤ B)
    (hh : M.h = hdrSyms as ++ H0) (hA : M.A = []) (hs : M.s = []) (hc : M.c = [])
    (hD : M.D = natSyms D) (hr : M.rr = []) (ho : M.o = savedF E) (hv : M.v = [])
    (hc3 : M.c3 = []) (ht : M.t = []) (hc2 : M.c2 = natSyms v ++ []) :
    HT [] (toF M) (passU I (bdU2 I)) (toF {M with o := savedF (E ++ genU2 as v)})
      ((B + 1) * (10 * opY C B + 19 * opY C B)) := by
  refine ht_passU hI (bdU2 I) (fun l => genU2 l v) (by simp [genU2]) M as D B (10 * opY C B) E
    H0 hlen hDB hxB (by omega) hh hA hs hc hD hr ho hv hc3 ht (fun j hj i => ?_)
  have hxj := hxB _ (List.getElem_mem hj)
  have hs0 := sum_take_le' as j
  have hs1 := sum_take_le' as (j + 1)
  rw [tsum_succ as j hj] at hs1
  refine HT.of_eq (ht_bdU2 hI _ (E ++ genU2 (as.take j) v) as[j] v ((as.take j).sum) B
    (by rfl) (by exact hc2) (by rfl) (by rfl) (by rfl) (by rfl) hxj (by omega) (by omega)) ?_
    le_rfl
  rw [tsum_succ as j hj, genU2_take_succ as v j hj, List.append_assoc]

theorem ht_pass3U (hI : I.Spec C) (M : MS) (as : List ℕ) (D K c B : ℕ) (E : List ℕ)
    (H0 : List Sym) (hlen : as.length = D) (hDB : D ≤ B) (hxB : ∀ x ∈ as, x ≤ B) (hKB : K ≤ B)
    (hsB : as.sum + c ≤ B) (hKc : K ≤ c)
    (hh : M.h = hdrSyms as ++ H0) (hA : M.A = []) (hs : M.s = []) (hc : M.c = [])
    (hD : M.D = natSyms D) (hr : M.rr = []) (ho : M.o = savedF E) (hv : M.v = [])
    (hc3 : M.c3 = []) (ht : M.t = []) (hK : M.K = natSyms K) (hcs : M.cs = natSyms c) :
    HT [] (toF M) (passU I (bdU3 I)) (toF {M with o := savedF (E ++ genU3 K as c)})
      ((B + 1) * (14 * Zc C B 1 + 19 * opY C B)) := by
  refine ht_passU hI (bdU3 I) (fun l => genU3 K l c) (by simp [genU3]) M as D B (14 * Zc C B 1)
    E H0 hlen hDB hxB (by omega) hh hA hs hc hD hr ho hv hc3 ht (fun j hj i => ?_)
  have hxj := hxB _ (List.getElem_mem hj)
  have hs0 := sum_take_le' as j
  have hs1 := sum_take_le' as (j + 1)
  rw [tsum_succ as j hj] at hs1
  refine HT.of_eq (ht_bdU3 hI _ (E ++ genU3 K (as.take j) c) as[j] c ((as.take j).sum) K B
    (by rfl) (by exact hcs) (by rfl) (by exact hK) (by rfl) (by rfl) (by rfl) (by rfl) hxj hKB
    (by omega) (by omega) hKc) ?_ le_rfl
  rw [tsum_succ as j hj, genU3_take_succ K as c j hj, List.append_assoc]

end Passes

section Loops

variable {I : HI} {C : ℕ}

/-- The prefix-round loop: `b₀` passes, the counter `sc2` running `b₀ - 1, …, 0`. -/
def loopV (I : HI) : HP I := (hcp I vb sc2).seq (hcd I sc2 (passU I (bdU2 I)))

def stV (M : MS) (E as : List ℕ) (b i : ℕ) : LM → List Sym :=
  toF {M with o := savedF (E ++ (vtail b i).flatMap (genU2 as)), c2 := natSyms i ++ []}

theorem ht_loopV (hI : I.Spec C) (M : MS) (as : List ℕ) (D b B : ℕ) (E : List ℕ)
    (H0 : List Sym) (hlen : as.length = D) (hDB : D ≤ B) (hxB : ∀ x ∈ as, x ≤ B)
    (hbB : b ≤ B) (hsB : as.sum + b ≤ B)
    (hh : M.h = hdrSyms as ++ H0) (hA : M.A = []) (hs : M.s = []) (hc : M.c = [])
    (hD : M.D = natSyms D) (hr : M.rr = []) (ho : M.o = savedF E) (hv : M.v = [])
    (hc3 : M.c3 = []) (ht : M.t = []) (hb : M.b = natSyms b) (hc2 : M.c2 = []) :
    HT [] (toF M) (loopV I)
      (toF {M with o := savedF (E ++ (List.range b).reverse.flatMap (genU2 as)), c2 := []})
      (33 * Zc C B 2) := by
  unfold loopV hcd
  have hc0 := HT.of_eq (ht_cp0 hI vb sc2 (by decide) (toF M) b [] TermOK.nil
      (by simp [toF, hb]) (by simp [toF, hc2]))
    (show _ = stV M E as b b by
      rw [upd_c2]; unfold stV; congr 1; ext <;> simp [ho, vtail_self]) le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc sc2 d0 [] TermOK.nil (stV M E as b)
    (fun i => by simp [stV, toF]) (passU I (bdU2 I)) (fun _ => 29 * Zc C B 1) b (by
      intro i hi
      simp only [stV, upd_c2]
      refine HT.of_eq (ht_pass2U hI _ as D i B (E ++ (vtail b (i + 1)).flatMap (genU2 as)) H0
        hlen hDB hxB (by omega) (by exact hh) (by exact hA) (by exact hs) (by exact hc)
        (by exact hD) (by exact hr) (by rfl) (by exact hv) (by exact hc3) (by exact ht)
        (by rfl)) ?_ ?_
      · rw [vtail_succ b i hi, List.flatMap_append, List.flatMap_singleton,
          List.append_assoc]
      · exact le_of_eq (by simp only [Zc]; ring))
  refine HT.of_eq (hc0.seq hloop) ?_ ?_
  · simp only [stV, vtail_zero, natSyms_zero', List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le hbB)
    have h2 := loop_Z C B b 1 2 29 rfl hbB (fun _ => 29 * Zc C B 1) (fun i _ => le_rfl)
    have h3 := opY_le_Zc C B 2
    omega

/-- One chunk pass, then `cs := cs - K`. -/
def bodyJ (I : HI) : HP I := (passU I (bdU3 I)).seq (pDecK I)

theorem ht_bodyJ (hI : I.Spec C) (M : MS) (as : List ℕ) (D K c B : ℕ) (E : List ℕ)
    (H0 : List Sym) (hlen : as.length = D) (hDB : D ≤ B) (hxB : ∀ x ∈ as, x ≤ B) (hKB : K ≤ B)
    (hsB : as.sum + c ≤ B) (hKc : K ≤ c)
    (hh : M.h = hdrSyms as ++ H0) (hA : M.A = []) (hs : M.s = []) (hc : M.c = [])
    (hD : M.D = natSyms D) (hr : M.rr = []) (ho : M.o = savedF E) (hv : M.v = [])
    (hc3 : M.c3 = []) (ht : M.t = []) (hK : M.K = natSyms K) (hcs : M.cs = natSyms c) :
    HT [] (toF M) (bodyJ I)
      (toF {M with o := savedF (E ++ genU3 K as c), cs := natSyms (c - K), c3 := []})
      (39 * Zc C B 2) := by
  unfold bodyJ
  refine HT.of_eq ((ht_pass3U hI M as D K c B E H0 hlen hDB hxB hKB hsB hKc hh hA hs hc hD hr
      ho hv hc3 ht hK hcs).seq
    (ht_decK hI _ c K B (by exact hcs) (by exact hK) (by exact hc3) hKB (by omega) hKc)) rfl ?_
  have k : (B + 1) * (14 * Zc C B 1 + 19 * opY C B) = 14 * Zc C B 2 + 19 * Zc C B 1 := by
    simp only [Zc]; ring
  have m2 : Zc C B 1 ≤ Zc C B 2 := Zc_mono _ _ 1
  omega

/-- The chunk loop: `J_blk` passes with `c = ℓ - 1 - jK` on `scs` (counter `sc2`). -/
def loopJ (I : HI) : HP I :=
  ((hcp I sL1 scs).seq (hcp I vJ sc2)).seq ((hcd I sc2 (bodyJ I)).seq (hdr I scs))

def stJ (M : MS) (E as : List ℕ) (ℓ K J i : ℕ) : LM → List Sym :=
  toF {M with
    o := savedF (E ++ (List.range (J - i)).flatMap (fun j => genU3 K as (ℓ - 1 - j * K))),
    cs := natSyms (ℓ - 1 - (J - i) * K), c2 := natSyms i ++ [], c3 := []}

theorem ht_loopJ (hI : I.Spec C) (M : MS) (as : List ℕ) (D ℓ K J B : ℕ) (E : List ℕ)
    (H0 : List Sym) (hlen : as.length = D) (hDB : D ≤ B) (hxB : ∀ x ∈ as, x ≤ B)
    (hKB : K ≤ B) (hJB : J ≤ B) (hlB : ℓ ≤ B) (hsB : as.sum + (ℓ - 1) ≤ B)
    (hJK : J * K ≤ ℓ - 1)
    (hh : M.h = hdrSyms as ++ H0) (hA : M.A = []) (hs : M.s = []) (hc : M.c = [])
    (hD : M.D = natSyms D) (hr : M.rr = []) (ho : M.o = savedF E) (hv : M.v = [])
    (hc3 : M.c3 = []) (ht : M.t = []) (hK : M.K = natSyms K) (hL1 : M.L1 = natSyms (ℓ - 1))
    (hJ : M.J = natSyms J) (hcs : M.cs = []) (hc2 : M.c2 = []) :
    HT [] (toF M) (loopJ I)
      (toF {M with
        o := savedF (E ++ (List.range J).flatMap (fun j => genU3 K as (ℓ - 1 - j * K))),
        cs := [], c2 := [], c3 := []}) (45 * Zc C B 3) := by
  unfold loopJ hcd
  have hc0 := HT.of_eq ((ht_cp0 hI sL1 scs (by decide) (toF M) (ℓ - 1) [] TermOK.nil
      (by simp [toF, hL1]) (by simp [toF, hcs])).seq
      (ht_cp0 hI vJ sc2 (by decide) _ J [] TermOK.nil (by simp [toF, hJ]) (by simp [toF, hc2])))
    (show _ = stJ M E as ℓ K J J by
      rw [upd_cs, upd_c2]; unfold stJ; congr 1; ext <;> simp [ho, hc3]) le_rfl
  have hloop := ht_cdLoop hI.iz hI.dc I.liz I.ldc sc2 d0 [] TermOK.nil (stJ M E as ℓ K J)
    (fun i => by simp [stJ, toF]) (bodyJ I) (fun _ => 39 * Zc C B 2) J (by
      intro i hi
      have hj : J - i = J - (i + 1) + 1 := by omega
      have hle : (J - (i + 1)) * K + K ≤ J * K := by
        have := Nat.mul_le_mul_right K (show J - (i + 1) + 1 ≤ J by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      have e2 : ℓ - 1 - (J - (i + 1)) * K - K = ℓ - 1 - (J - i) * K := by
        rw [hj, Nat.add_mul, Nat.one_mul]; omega
      simp only [stJ, upd_c2]
      refine HT.of_eq (ht_bodyJ hI _ as D K (ℓ - 1 - (J - (i + 1)) * K) B
        (E ++ (List.range (J - (i + 1))).flatMap (fun j => genU3 K as (ℓ - 1 - j * K))) H0
        hlen hDB hxB hKB (by omega) (by omega) (by exact hh) (by exact hA) (by exact hs)
        (by exact hc) (by exact hD) (by exact hr) (by rfl) (by exact hv) (by rfl) (by exact ht)
        (by exact hK) (by rfl)) ?_ le_rfl
      rw [e2, hj, List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.append_assoc])
  refine HT.of_eq (hc0.seq (hloop.seq (ht_dr hI scs _ (ℓ - 1 - (J - 0) * K) [] TermOK.nil
    (by simp [stJ, toF])))) ?_ ?_
  · simp only [stJ, upd_cs, Nat.sub_zero, natSyms_zero', List.append_nil]
  · have c1 := cost1_le (C := C) (bitLen_le (show ℓ - 1 ≤ B by omega))
    have c2 := cost1_le (C := C) (bitLen_le hJB)
    have c3 := cost1_le (C := C) (bitLen_le (show ℓ - 1 - (J - 0) * K ≤ B by omega))
    have h2 := loop_Z C B J 2 3 39 rfl hJB (fun _ => 39 * Zc C B 2) (fun i _ => le_rfl)
    have h3 := opY_le_Zc C B 3
    omega

end Loops

end SubNLogN.Machine.FFT.LayoutMapUAux
