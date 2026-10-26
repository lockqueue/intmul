/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadStageBase
import SubNLogN.Machine.Bridge.SpreadStageAR
import SubNLogN.Machine.Bridge.SpreadVal
import SubNLogN.Machine.Bridge.SpreadAddr
import SubNLogN.Machine.Bridge.SpreadPackFiltTop
import SubNLogN.Machine.Bridge.SpreadPackDataTop
import SubNLogN.Machine.Bridge.SpreadSlot
import SubNLogN.Machine.Bridge.SpreadSetupRun

/-!
# K5 spreading, stage main (1): lists, lengths, values, costs (`Bridge/SpreadStageMainBase.lean`)

Pure facts for the composition `spreadLines_of` (`Bridge/SpreadStageMain.lean`): the tap table
around the axis block (`tapTabSyms_split`), the lengths of tap blocks, records and the tap table
(`length_tapBlock_eq`, `length_carrSyms_const`, `length_tapTabSyms`), the stage values
(`stageVals_eq`, from `SpreadStageValStmt`), the slot bounds, the ruler sizes, and the cost
bound of the stage against `Ctot · spreadCost` (`stage_cost_le`). Everything is proved.
Helpers live in `SubNLogN.Machine.Bridge.SpreadAux.StageMain`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux.StageMain

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Arith Computability
  SubNLogN.Machine.Bridge.SpreadAux SubNLogN.Machine.Bridge.SpreadAux.Stage SubNLogN.Math.Common
  SubNLogN.Math.Bridge

/-! ## Lists and shapes -/

theorem deconvOrder_succ_ (n : ℕ) :
    deconvOrder (n + 1) = (List.finRange n).map Fin.succ := by
  unfold deconvOrder
  rw [List.finRange_succ, List.filter_cons]
  simp only [Fin.val_zero, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte]
  rw [List.filter_eq_self]
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  simp

theorem spreadOrder_eq_rev_ (d : ℕ) : spreadOrder d = (deconvOrder d).reverse := by
  unfold spreadOrder deconvOrder
  rw [List.filter_reverse]

theorem length_spreadOrder_ (d : ℕ) : (spreadOrder d).length = d - 1 := by
  cases d with
  | zero => simp [spreadOrder]
  | succ n => simp [spreadOrder_eq_rev_, deconvOrder_succ_]

theorem spreadOrder_getElem_ (d c : ℕ) (hc : c < (spreadOrder d).length) :
    ((spreadOrder d)[c] : ℕ) = d - 1 - c := by
  cases d with
  | zero => simp [spreadOrder] at hc
  | succ n =>
    have hc' : c < n := by rw [length_spreadOrder_] at hc; omega
    simp only [spreadOrder_eq_rev_, deconvOrder_succ_, List.getElem_reverse,
      List.getElem_map, List.getElem_finRange, Fin.val_succ, List.length_map,
      List.length_finRange, Fin.val_cast]
    omega

/-- `spreadOrder d = [d-1, …, 1]` around a spread axis `i`. -/
theorem spreadOrder_split {d : ℕ} (i : Fin d) (hi : (i : ℕ) ≠ 0) :
    spreadOrder d = (spreadOrder d).take (d - 1 - i) ++ i :: (spreadOrder d).drop (d - i) := by
  have hlen := length_spreadOrder_ d
  have hid := i.isLt
  have hc : d - 1 - (i : ℕ) < (spreadOrder d).length := by rw [hlen]; omega
  have hget : (spreadOrder d)[d - 1 - (i : ℕ)] = i := by
    apply Fin.ext
    rw [spreadOrder_getElem_ d _ hc]
    omega
  conv_lhs => rw [← List.take_append_drop (d - 1 - (i : ℕ)) (spreadOrder d)]
  rw [List.drop_eq_getElem_cons hc, hget, show d - 1 - (i : ℕ) + 1 = d - i by omega]

theorem flatMap_map_mark {α : Type} (g : α → List Sym) : ∀ A : List α,
    (A.map g).flatMap (· ++ [Sym.mark]) = A.flatMap fun x => g x ++ [Sym.mark]
  | [] => rfl
  | a :: A => by rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, flatMap_map_mark g A]

/-- The tap table around the block of a spread axis `i`. -/
theorem tapTabSyms_split {d : ℕ} (wT P : ℕ) (t : Fin d → ℕ) (T : BridgeTables t) (i : Fin d)
    (hi : (i : ℕ) ≠ 0) :
    tapTabSyms wT P t T =
      (((spreadOrder d).take (d - 1 - i)).map fun i' => carrSyms wT (tapBlock t P T i')).flatMap
          (· ++ [Sym.mark]) ++
        (carrSyms wT (tapBlock t P T i) ++ Sym.mark ::
          ((spreadOrder d).drop (d - i)).flatMap fun i' =>
            carrSyms wT (tapBlock t P T i') ++ [Sym.mark]) := by
  unfold tapTabSyms
  conv_lhs => rw [spreadOrder_split i hi]
  rw [List.flatMap_append, List.flatMap_cons, flatMap_map_mark]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem length_filterMap_some {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, (f a).isSome) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self ..))
    rw [List.filterMap_cons_some hb, List.length_cons, List.length_cons,
      length_filterMap_some f l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem suffixProd_pos_ {d : ℕ} {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) :
    0 < suffixProd t i := by
  unfold suffixProd
  exact Finset.prod_pos fun l _ => by have := (ht l).1; omega

theorem prefixProd_pos_ {d : ℕ} {t : Fin d → ℕ} (ht : ShapeOK t) (k : ℕ) :
    0 < prefixProd t k := by
  unfold prefixProd
  exact Finset.prod_pos fun l _ => by have := (ht l).1; omega

/-- The tap block of axis `i` has `A_i` records. -/
theorem length_tapBlock_eq {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (T : BridgeTables t) (i : Fin d)
    (ht : ShapeOK t) : (tapBlock t P T i).length = prefixProd t i := by
  obtain ⟨hlen, -, -, -, h5⟩ := expAddrsStruct_holds t i ht
  rw [h5 P T, length_filterMap_some _ _ ?_, List.length_range]
  intro g hg
  rw [List.mem_range] at hg
  have hpos : 0 < t i * suffixProd t i :=
    Nat.mul_pos (by have := (ht i).1; omega) (suffixProd_pos_ ht i)
  have hlt : g * (t i * suffixProd t i) < (expAddrs t i).length := by
    rw [hlen, ← prefixProd_mul_mul_suffixProd t i, mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right hg hpos
  rw [List.getElem?_eq_getElem hlt]
  rfl

theorem length_tapOffsets_ {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (i : Fin d) :
    (tapOffsets t P i).length = spreadWin t P i := by
  unfold tapOffsets spreadWin
  split_ifs with h
  · simp [← List.map_eq_flatMap] <;> omega
  · simp [← List.map_eq_flatMap] <;> omega

theorem length_tapRec_ {d : ℕ} (t : Fin d → ℕ) (P : ℕ) (tap : ℕ → ℤ → ℂ) (i : Fin d) (a : ℕ) :
    (tapRec t P tap i a).length = spreadWin t P i := by
  unfold tapRec
  rw [List.length_map, length_tapOffsets_]

theorem length_of_mem_tapBlock {d : ℕ} {t : Fin d → ℕ} {P : ℕ} {T : BridgeTables t} {i : Fin d}
    {F : List CInt} (hF : F ∈ tapBlock t P T i) : F.length = spreadWin t P i := by
  unfold tapBlock at hF
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hF
  exact length_tapRec_ _ _ _ _ _

theorem mark_not_mem_carrSyms_ (w : ℕ) (v : List (List CInt)) : Sym.mark ∉ carrSyms w v := by
  simp [carrSyms, arrSyms, blk, recSyms]

/-! ## The value identity -/

/-- `R / t_i = A_i · nrep`. -/
theorem totalLen_div_eq (b : BrPar) (i : Fin b.d) (ht : ShapeOK b.t) :
    totalLen b.t / b.t i = prefixProd b.t i * suffixProd b.t i := by
  rw [← prefixProd_mul_mul_suffixProd b.t i,
    show prefixProd b.t i * b.t i * suffixProd b.t i =
      b.t i * (prefixProd b.t i * suffixProd b.t i) by ring]
  exact Nat.mul_div_cancel_left _ (by have := (ht i).1; omega)

/-- **The stage values** (`SpreadStageValStmt` at `R / t_i = A_i · nrep`). -/
theorem stageVals_eq (b : BrPar) (i : Fin b.d) (T : BridgeTables b.t) (W : Idx b.t → ℂ)
    (ht : ShapeOK b.t) (hi0 : (i : ℕ) ≠ 0) (hOG : TablesOnGrid b.P b.t T)
    (hTW : TapsWindowed b.P b.t T) (hWg : ∀ k, OnGrid (b.P + 2) (W k)) :
    (List.range (prefixProd b.t i * suffixProd b.t i)).flatMap (fun l =>
      lineOut (b.P + 2) (b.t i) (spreadWin b.t b.P i) (spreadA0 b i)
        ((((expAddrs b.t i).map fun k => gridInt (b.P + 2) (W k)).drop (l * b.t i)).take (b.t i))
        ((tapBlock b.t b.P T i).getD (l / suffixProd b.t i) [])) =
    (expAddrs b.t i).map (fun k =>
      gridInt (b.P + 2) (spreadAxisFixedR roundHalfUpR (b.P + 2) b.t i (T.tap i) W k)) := by
  rw [spreadStageVal_of expAddrsStruct_holds b i T W ht hi0 hOG hTW hWg,
    totalLen_div_eq b i ht]

/-! ## Records and lengths -/

theorem length_twosBits_ (w : ℕ) (z : ℤ) : (twosBits w z).length = w := by
  simp [twosBits, bitsLE]

theorem length_crecBits_ (w : ℕ) (cs : List CInt) : (crecBits w cs).length = 2 * w * cs.length := by
  induction cs with
  | nil => simp [crecBits]
  | cons c cs ih =>
    simp only [crecBits, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    simp only [coefBits, List.length_append, length_twosBits_, List.length_cons]
    ring

theorem length_carrSyms_ (w : ℕ) (v : List (List CInt)) :
    (carrSyms w v).length = (v.map fun r => 2 * w * r.length + 1).sum := by
  induction v with
  | nil => simp [carrSyms, arrSyms, blk]
  | cons r v ih =>
    simp only [carrSyms, arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append,
      List.sum_cons] at ih ⊢
    rw [ih]
    simp [recSyms, length_crecBits_]

theorem length_carrSyms_const (w k : ℕ) (v : List (List CInt)) (hk : ∀ r ∈ v, r.length = k) :
    (carrSyms w v).length = v.length * (2 * w * k + 1) := by
  rw [length_carrSyms_]
  have h : (v.map fun r => 2 * w * r.length + 1) = v.map fun _ => 2 * w * k + 1 :=
    List.map_congr_left fun r hr => by rw [hk r hr]
  rw [h, List.map_const', List.sum_replicate, smul_eq_mul]

theorem length_carrSyms_singles (w : ℕ) (L : List CInt) :
    (carrSyms w (L.map fun y => [y])).length = L.length * (2 * w + 1) := by
  rw [length_carrSyms_const w 1 _ (fun r hr => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hr; rfl), List.length_map]
  ring

/-- The tap table has `tapTabLen b` symbols. -/
theorem length_tapTabSyms (b : BrPar) (T : BridgeTables b.t) (ht : ShapeOK b.t) :
    (tapTabSyms b.wT b.P b.t T).length = tapTabLen b := by
  unfold tapTabSyms tapTabLen
  rw [List.length_flatMap]
  congr 1
  refine List.map_congr_left fun i' _ => ?_
  rw [List.length_append, length_carrSyms_const b.wT (spreadWin b.t b.P i') _
    (fun r hr => length_of_mem_tapBlock hr), length_tapBlock_eq _ _ _ _ ht, List.length_singleton]
  have hw : (tapOffsets b.t b.P i').length = spreadWin b.t b.P i' := length_tapOffsets_ _ _ _
  rw [hw]
  ring

theorem encT_eq {d : ℕ} {t : Fin d → ℕ} (F : ℕ) (addrs : List (Idx t)) (Z : Idx t → ℂ) :
    encT F addrs Z = (addrs.map fun k => gridInt F (Z k)).map fun x => [x] := by
  simp [encT, recsAt, List.map_map, Function.comp_def]

/-! ## Slot bounds -/

theorem slot_bound {W n a c e : ℕ} (hW : W < 2 ^ n) (he : n + a + c + 1 ≤ e) :
    (W : ℤ) * (2 * (2 ^ a * 2 ^ c)) < 2 ^ e := by
  have h1 : (W : ℤ) < 2 ^ n := by exact_mod_cast hW
  have h2 : (2 : ℤ) * (2 ^ a * 2 ^ c) = 2 ^ (a + c + 1) := by ring
  have h3 : (2 : ℤ) ^ n * 2 ^ (a + c + 1) ≤ 2 ^ e := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  rw [h2]
  have h4 : (0 : ℤ) < 2 ^ (a + c + 1) := by positivity
  nlinarith

theorem slot_bound_nat {W n a c e : ℕ} (hW : W < 2 ^ n) (he : n + a + c ≤ e) :
    W * (2 ^ a * 2 ^ c) < 2 ^ e := by
  have h3 : 2 ^ n * (2 ^ a * 2 ^ c) ≤ 2 ^ e := by
    rw [← pow_add, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 0 < 2 ^ a * 2 ^ c := by positivity
  calc W * (2 ^ a * 2 ^ c) < 2 ^ n * (2 ^ a * 2 ^ c) := Nat.mul_lt_mul_of_pos_right hW h4
    _ ≤ 2 ^ e := h3

/-! ## Rulers after the setup -/

section Rulers

variable {Es : Type} [DecidableEq Es]

theorem setRu_ru (b : BrPar) (i : Fin b.d) (B : SK Es → List Sym) (r : RulerId) :
    setRu b i B (sp (.ru r)) = List.replicate (spreadRulers b i r) .mark := rfl

theorem setRu_of_ne (b : BrPar) (i : Fin b.d) (B : SK Es → List Sym) (k : SK Es)
    (hk : ∀ r, k ≠ sp (.ru r)) : setRu b i B k = B k := by
  unfold setRu
  split
  · next r => exact absurd rfl (hk r)
  · rfl

end Rulers


/-! ## Size facts -/

theorem d_le_setup (b : BrPar) : b.d ≤ b.setup := by
  have h1 := SpreadSetupAux.d_le b
  have h2 : (hdrSyms b.hdr).length + 1 ≤ b.setup := by
    unfold BrPar.setup
    exact Nat.le_self_pow (by norm_num) _
  omega

theorem t_le_totalLen {d : ℕ} {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) :
    t i ≤ totalLen t := by
  rw [← prefixProd_mul_mul_suffixProd t i]
  calc t i = 1 * t i * 1 := by ring
    _ ≤ prefixProd t i * t i * suffixProd t i :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (prefixProd_pos_ ht i)) (suffixProd_pos_ ht i)

theorem prefixProd_le_totalLen {d : ℕ} {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) :
    prefixProd t i ≤ totalLen t := by
  rw [← prefixProd_mul_mul_suffixProd t i]
  calc prefixProd t i = prefixProd t i * 1 * 1 := by ring
    _ ≤ prefixProd t i * t i * suffixProd t i :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by have := (ht i).1; omega)) (suffixProd_pos_ ht i)

theorem suffixProd_le_totalLen {d : ℕ} {t : Fin d → ℕ} (ht : ShapeOK t) (i : Fin d) :
    suffixProd t i ≤ totalLen t := by
  rw [← prefixProd_mul_mul_suffixProd t i]
  calc suffixProd t i = 1 * 1 * suffixProd t i := by ring
    _ ≤ prefixProd t i * t i * suffixProd t i :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (prefixProd_pos_ ht i) (by have := (ht i).1; omega))

theorem spreadWin_le (b : BrPar) (i : Fin b.d) : spreadWin b.t b.P i ≤ b.t i := by
  unfold spreadWin; omega

theorem one_le_spreadWin (b : BrPar) (i : Fin b.d) (ht : ShapeOK b.t) :
    1 ≤ spreadWin b.t b.P i := by
  unfold spreadWin; have := (ht i).1; omega

theorem spreadA0_le (b : BrPar) (i : Fin b.d) : spreadA0 b i ≤ b.t i := by
  unfold spreadA0; split_ifs <;> omega

theorem slot_ge (b : BrPar) (i : Fin b.d) : b.wI + b.wT + 4 ≤ spreadSlot b i := by
  unfold spreadSlot; omega

/-- Every parameter ruler is within the stage budget. -/
theorem spreadRulers_le (b : BrPar) (i : Fin b.d) (ht : ShapeOK b.t) (hPw : b.P + 2 ≤ b.wI)
    (r : RulerId) : spreadRulers b i r ≤
      totalLen b.t * (2 * b.wI + 1) + totalLen b.t * spreadSlot b i + b.setup := by
  have htR := t_le_totalLen ht i
  have hR1 : 1 ≤ totalLen b.t := by have := (ht i).1; omega
  have hAR := prefixProd_le_totalLen ht i
  have hrepR := suffixProd_le_totalLen ht i
  have hd := d_le_setup b
  have hV1 : totalLen b.t ≤ totalLen b.t * (2 * b.wI + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hs1 : spreadSlot b i ≤ totalLen b.t * spreadSlot b i := Nat.le_mul_of_pos_left _ hR1
  have hwV : 2 * b.wI + 1 ≤ totalLen b.t * (2 * b.wI + 1) := Nat.le_mul_of_pos_left _ hR1
  have hslot := slot_ge b i
  have hW := spreadWin_le b i
  have ha0 := spreadA0_le b i
  generalize totalLen b.t * (2 * b.wI + 1) = V at *
  generalize totalLen b.t * spreadSlot b i = RS at *
  cases r <;> simp only [spreadRulers] <;> omega

/-- The product rulers are within the stage budget. -/
theorem prod_le (b : BrPar) (i : Fin b.d) (ht : ShapeOK b.t) (n : ℕ) (hn : n ≤ b.t i) :
    n * (2 * b.wI + 1) ≤ totalLen b.t * (2 * b.wI + 1) + totalLen b.t * spreadSlot b i +
      b.setup := by
  have h1 : n * (2 * b.wI + 1) ≤ totalLen b.t * (2 * b.wI + 1) :=
    Nat.mul_le_mul_right _ (hn.trans (t_le_totalLen ht i))
  omega

theorem prod_s_le (b : BrPar) (i : Fin b.d) (ht : ShapeOK b.t) (n : ℕ) (hn : n ≤ b.t i) :
    n * spreadSlot b i ≤ totalLen b.t * (2 * b.wI + 1) + totalLen b.t * spreadSlot b i +
      b.setup := by
  have h1 : n * spreadSlot b i ≤ totalLen b.t * spreadSlot b i :=
    Nat.mul_le_mul_right _ (hn.trans (t_le_totalLen ht i))
  omega


/-! ## The cost bound -/

/-- The cost constant of the stage program. -/
def Ctot (Cs CF CL : ℕ) : ℕ := Cs + 3 * CF + 10 * CL + 500

/-- The stage budget (`spreadCost`) in terms of `A = A_i`, `rep = nrep`, `t = t_i`. -/
def kB (A rep t W s wI wT m d Tl setup : ℕ) : ℕ :=
  A * t * rep * (2 * wI + 1) + A * t * rep * s +
    A * rep * ((t / W + 1) * (4 * m) + W * (2 * wT + 1)) + d * Tl + setup

theorem setup_cost_le (Cs A rep t W s wI wT m d Tl setup : ℕ) (hA : 1 ≤ A) (hrep : 1 ≤ rep)
    (ht : 1 ≤ t) :
    Cs * (setup + A * t * rep + s) ≤ Cs * kB A rep t W s wI wT m d Tl setup := by
  apply Nat.mul_le_mul_left
  unfold kB
  have hR : 1 ≤ A * t * rep := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))
  have h1 : s ≤ A * t * rep * s := Nat.le_mul_of_pos_left s (by omega)
  have h2 : A * t * rep ≤ A * t * rep * (2 * wI + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem stagePre_cost_le (A rep t W a0 s wI wT m d nk L1 Tl setup : ℕ)
    (hA : 1 ≤ A) (hrep : 1 ≤ rep) (hWt : W ≤ t) (ha0 : a0 ≤ t) (hnk : nk ≤ d)
    (hset : d ≤ setup) (hd1 : 1 ≤ d) (hL : L1 ≤ Tl) :
    stagePreCost (W - 1) (2 * wI + 1) t a0 (t - a0) s nk L1 ≤
      100 * kB A rep t W s wI wT m d Tl setup := by
  unfold stagePreCost kB
  have hN : 1 ≤ A * rep := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hR : t ≤ A * t * rep := by
    calc t = 1 * t := (one_mul t).symm
      _ ≤ (A * rep) * t := Nat.mul_le_mul_right _ hN
      _ = A * t * rep := by ring
  have hW1 : W - 1 ≤ t := by omega
  have hta : t - a0 ≤ t := Nat.sub_le _ _
  have h1 : (W - 1) * (9 * (2 * wI + 1) + 8) ≤ t * (9 * (2 * wI + 1) + 8) :=
    Nat.mul_le_mul_right _ hW1
  have h2 : a0 * (9 * (2 * wI + 1) + 8) ≤ t * (9 * (2 * wI + 1) + 8) :=
    Nat.mul_le_mul_right _ ha0
  have h3 : (t - a0) * (9 * (2 * wI + 1) + 8) ≤ t * (9 * (2 * wI + 1) + 8) :=
    Nat.mul_le_mul_right _ hta
  have h4 : (W - 1) * (9 * s + 8) ≤ t * (9 * s + 8) := Nat.mul_le_mul_right _ hW1
  have h5 : t * (9 * (2 * wI + 1) + 8) ≤ A * t * rep * (9 * (2 * wI + 1) + 8) :=
    Nat.mul_le_mul_right _ hR
  have h6 : t * (9 * s + 8) ≤ A * t * rep * (9 * s + 8) := Nat.mul_le_mul_right _ hR
  have h7 : nk * (3 * L1 + 5 + 4) ≤ d * (3 * Tl + 9) := Nat.mul_le_mul hnk (by omega)
  have h8 : A * t * rep ≤ A * t * rep * (2 * wI + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h9 := Nat.zero_le (A * rep * ((t / W + 1) * (4 * m) + W * (2 * wT + 1)))
  have h10 := Nat.zero_le (A * t * rep * s)
  have h11 := Nat.zero_le (d * Tl)
  linarith

theorem group_cost_le (CF CL A rep t W s wI wT m d Tl setup : ℕ) (hA : 1 ≤ A)
    (hrep : 1 ≤ rep) (hW1 : 1 ≤ W) (hWt : W ≤ t) (hs1 : 1 ≤ setup)
    (hm : mulW (2 * (W * s + 1) + 1) = m) :
    A * (CF * (W * (s + 1) + 1) + rep * (CL * lineCost s t W + 4) + 4 * rep + 12 * (s * W) + 40 + 8) + 4 ≤
      (2 * CF + 5 * CL + 60) * kB A rep t W s wI wT m d Tl setup := by
  unfold lineCost
  rw [hm]
  have hK : kB A rep t W s wI wT m d Tl setup = A * t * rep * (2 * wI + 1) + A * t * rep * s +
      A * rep * ((t / W + 1) * (4 * m) + W * (2 * wT + 1)) + d * Tl + setup := rfl
  generalize kB A rep t W s wI wT m d Tl setup = K at hK ⊢
  have hN : A * rep ≤ A * t * rep := by
    calc A * rep = A * 1 * rep := by ring
      _ ≤ A * t * rep := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have hR1 : A ≤ A * t * rep := by
    calc A = A * 1 * 1 := by ring
      _ ≤ A * t * rep := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hrep
  have hAW : A * W ≤ A * t * rep := by
    calc A * W ≤ A * t * 1 := by rw [mul_one]; exact Nat.mul_le_mul_left _ hWt
      _ ≤ A * t * rep := Nat.mul_le_mul_left _ hrep
  have hAWs : A * W * s ≤ A * t * rep * s := Nat.mul_le_mul_right _ hAW
  have hdiv : t / W * W ≤ t := Nat.div_mul_le_self t W
  have hV : A * t * rep ≤ A * t * rep * (2 * wI + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hPs := Nat.zero_le (A * t * rep * s)
  have hDK := Nat.zero_le (d * Tl)
  have hWT := Nat.zero_le (A * rep * (W * (2 * wT + 1)))
  -- the line costs
  have e4 : (t + W) * (s + 1) + (t / W + 2) * (W * (s + 1)) ≤ 5 * t * (s + 1) := by
    have h0 : (t / W + 2) * W ≤ 3 * t := by nlinarith [hdiv]
    have p1 : (t / W + 2) * W * (s + 1) ≤ 3 * t * (s + 1) := Nat.mul_le_mul_right _ h0
    have p2 : W * (s + 1) ≤ t * (s + 1) := Nat.mul_le_mul_right _ hWt
    nlinarith [p1, p2]
  have e6 : A * rep * ((t + W) * (s + 1) + (t / W + 2) * (W * (s + 1))) ≤
      A * rep * (5 * t * (s + 1)) := Nat.mul_le_mul_left _ e4
  have e7 : A * rep * ((t / W + 2) * m) ≤ 2 * (A * rep * ((t / W + 1) * m)) := by
    have : (t / W + 2) * m ≤ 2 * ((t / W + 1) * m) := by nlinarith [Nat.zero_le (t / W * m)]
    calc A * rep * ((t / W + 2) * m) ≤ A * rep * (2 * ((t / W + 1) * m)) :=
          Nat.mul_le_mul_left _ this
      _ = 2 * (A * rep * ((t / W + 1) * m)) := by ring
  have g2 : A * rep * ((t + W) * (s + 1) + (t / W + 2) * (W * (s + 1) + m)) ≤ 5 * K := by
    have e5 : A * rep * ((t + W) * (s + 1) + (t / W + 2) * (W * (s + 1) + m)) =
        A * rep * ((t + W) * (s + 1) + (t / W + 2) * (W * (s + 1))) +
          A * rep * ((t / W + 2) * m) := by ring
    rw [e5]
    have e8 : A * rep * (5 * t * (s + 1)) = 5 * (A * t * rep * s) + 5 * (A * t * rep) := by ring
    have e9 : A * rep * ((t / W + 1) * (4 * m) + W * (2 * wT + 1)) =
        4 * (A * rep * ((t / W + 1) * m)) + A * rep * (W * (2 * wT + 1)) := by ring
    rw [hK]
    linarith [Nat.zero_le (A * rep * ((t / W + 1) * m))]
  have g2' : CL * (A * rep * ((t + W) * (s + 1) + (t / W + 2) * (W * (s + 1) + m))) ≤
      CL * (5 * K) := Nat.mul_le_mul_left _ g2
  have g1 : A * (W * (s + 1) + 1) ≤ 2 * K := by
    have : A * (W * (s + 1) + 1) = A * W * s + A * W + A := by ring
    rw [this, hK]
    linarith [Nat.zero_le (A * rep * ((t / W + 1) * (4 * m) + W * (2 * wT + 1)))]
  have g1' : CF * (A * (W * (s + 1) + 1)) ≤ CF * (2 * K) := Nat.mul_le_mul_left _ g1
  have g3 : A * (4 * rep + 12 * (s * W) + 40 + 8) + 4 * (A * rep) + 4 ≤ 60 * K := by
    have : A * (4 * rep + 12 * (s * W) + 40 + 8) + 4 * (A * rep) + 4 =
        8 * (A * rep) + 12 * (A * W * s) + 48 * A + 4 := by ring
    rw [this, hK]
    linarith [Nat.zero_le (A * rep * ((t / W + 1) * (4 * m) + W * (2 * wT + 1)))]
  linarith [g1', g2', g3]

theorem post_cost_le (A rep t W s wI wT m d Tl setup L1 L2 sumR : ℕ) (hd1 : 1 ≤ d)
    (hs1 : 1 ≤ setup) (hL : L1 + L2 ≤ Tl)
    (hsum : sumR ≤ 22 * (A * t * rep * (2 * wI + 1) + A * t * rep * s + setup)) :
    4 * (L2 + L1 + A * t * rep * (2 * wI + 1)) + 3 * sumR + 60 ≤
      130 * kB A rep t W s wI wT m d Tl setup := by
  unfold kB
  have h1 : Tl ≤ d * Tl := Nat.le_mul_of_pos_left Tl (by omega)
  have h2 := Nat.zero_le (A * rep * ((t / W + 1) * (4 * m) + W * (2 * wT + 1)))
  omega

/-- **The stage cost** against `Ctot · spreadCost`. -/
theorem stage_cost_le (Cs CF CL A rep t W a0 s wI wT m d nk L1 L2 Tl setup sumR : ℕ)
    (hA : 1 ≤ A) (hrep : 1 ≤ rep) (hW1 : 1 ≤ W) (hWt : W ≤ t) (ha0 : a0 ≤ t) (hnk : nk ≤ d)
    (hd1 : 1 ≤ d) (hset : d ≤ setup) (hL : L1 + L2 ≤ Tl)
    (hsum : sumR ≤ 22 * (A * t * rep * (2 * wI + 1) + A * t * rep * s + setup))
    (hm : mulW (2 * (W * s + 1) + 1) = m) :
    Cs * (setup + A * t * rep + s) + (stagePreCost (W - 1) (2 * wI + 1) t a0 (t - a0) s nk L1 +
      ((A * (CF * (W * (s + 1) + 1) + rep * (CL * lineCost s t W + 4) + 4 * rep + 12 * (s * W) + 40 + 8) + 4) +
        (4 * (L2 + L1 + A * t * rep * (2 * wI + 1)) + 3 * sumR + 60))) ≤
    Ctot Cs CF CL * kB A rep t W s wI wT m d Tl setup := by
  have c1 := setup_cost_le Cs A rep t W s wI wT m d Tl setup hA hrep (by omega)
  have c2 := stagePre_cost_le A rep t W a0 s wI wT m d nk L1 Tl setup hA hrep hWt ha0 hnk hset hd1
    (by omega)
  have c3 := group_cost_le CF CL A rep t W s wI wT m d Tl setup hA hrep hW1 hWt (by omega) hm
  have c4 := post_cost_le A rep t W s wI wT m d Tl setup L1 L2 sumR hd1 (by omega) hL hsum
  generalize kB A rep t W s wI wT m d Tl setup = K at c1 c2 c3 c4 ⊢
  unfold Ctot
  linarith [Nat.zero_le (CF * K), Nat.zero_le (CL * K), Nat.zero_le K]



/-! ## `stagePre` inside the stage registers -/

section Pre

variable {Es σ : Type} [DecidableEq Es]

/-- `stagePre_eval` as a `Runs` fact of the lifted program `ar lA stagePre`. -/
theorem runs_stagePre (lA : Lens σ AReg) (nW nr nt na nta ns nk : ℕ) (blks : List (List Sym))
    (rest : List Sym) (S : SK Es → List Sym)
    (hWm1 : S (sp (.ru .Wm1)) = List.replicate nW .mark)
    (hrecw : S (sp (.ru .recw)) = List.replicate nr .mark)
    (ht : S (sp (.ru .t)) = List.replicate nt .mark)
    (ha0 : S (sp (.ru .a0)) = List.replicate na .mark)
    (hta : S (sp (.ru .ta)) = List.replicate nta .mark)
    (hs : S (sp (.ru .s)) = List.replicate ns .mark)
    (hskip : S (sp (.ru .skip)) = List.replicate nk .mark)
    (hpr : ∀ k, S (sp (.pr k)) = []) (hX0 : S (sp (.X 0)) = []) (hX7 : S (sp (.X 7)) = [])
    (hX3 : S (sp (.X 3)) = []) (hTT : S (sp .TT) = [])
    (htap : S (kN .tapTab) = blks.flatMap (· ++ [.mark]) ++ rest) (hlen : blks.length = nk)
    (hmk : ∀ b ∈ blks, ∀ x ∈ b, x ≠ .mark) :
    Runs (ar lA stagePre) S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S (sp (.pr 0)) (List.replicate (nW * nr) .mark))
          (sp (.pr 1)) (List.replicate (nt * nr) .mark))
          (sp (.pr 2)) (List.replicate (na * nr) .mark))
          (sp (.pr 3)) (List.replicate (nta * nr) .mark))
          (sp (.pr 4)) (List.replicate (nW * ns) .mark))
          (kN .tapTab) rest) (sp .TT) (blks.flatMap (· ++ [.mark])).reverse)
      (fun _ => True)
      (stagePreCost nW nr nt na nta ns nk (blks.flatMap (· ++ [.mark])).length) :=
  runs_ar lA (Runs.of_eval (Q := fun _ => True) fun v => by
    obtain ⟨v', c, e, hc⟩ := stagePre_eval nW nr nt na nta ns nk blks rest S v hWm1 hrecw ht ha0
      hta hs hskip hpr hX0 hX7 hX3 hTT htap hlen hmk
    exact ⟨v', c, e, trivial, hc⟩)

end Pre

end SubNLogN.Machine.Bridge.SpreadAux.StageMain
