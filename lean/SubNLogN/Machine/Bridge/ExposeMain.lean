/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.ExposeKit

/-!
# K5 axis exposures (3): the exposure / restoration machine

The machine `exposeProg rst P6` (`rst = false`: exposure, `rst = true`: restoration) of one axis
`i` of a balanced shape, with a Lemma A.8 (`lem:transfer12`) interchange program `P6` (`C6InterchangeStmt`; `C6` kept for stability):
1. `headA`: skip `p, P, ω`, copy `wI` (as `2·wI`) to `W`, skip `wI … wIn`, copy `d` to `D`, skip
   `d`, copy the axis `i` (from `ax`) to `I`; skipped fields go to `T` (guard `sep2` at the bottom);
2. `scanA`: skip the shape fields `t_0 … t_{i-1}` (`D` counts down), read `log₂ t_i` onto `U1`,
   decrement `D` (now `d - 1 - i`);
3. if `D ≠ 0` (`i < d-1`), `callA`: `D := d-2-i`; build `G = t_{i+1}⋯t_{d-2}` on `GB` in binary
   (the fields are powers of two, read in unary); read `ℓ = log₂ t_{d-1}` onto `U2`; `BB := 1`; call
   `P6` on `(arr, U1/U2, GB, BB, W)` (`U1`/`U2` swapped for the restoration); drop the counters;
4. `tailA`: rewind the header from `T`, drop `U1` and `W`.
For `i = d-1` the exposed order is the natural order and step 3 is skipped.

Main result: `runs_exposeProg` (generic in the direction, with the Lemma A.8 (`lem:transfer12`) specification as hypothesis).
-/

namespace SubNLogN.Machine.BridgeExp

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability
open SubNLogN.Math.Common SubNLogN.Math.Bridge

/-! ## A peeked branch -/

theorem runs_peek_ite {K σ' : Type} [DecidableEq K] (k : K)
    (p q : Prog K (fun _ => Sym) (Option Sym × σ')) {S S' : K → List Sym} {T : ℕ} (b : Bool)
    (hb : ∀ w : σ', BridgeRed.topIsBit ((S k).head?, w) = b)
    (hp : Runs (cond b p q) S S' (fun _ => True) T) :
    Runs (.seq (BridgeRed.peekTop k) (.ite BridgeRed.topIsBit p q)) S S' (fun _ => True)
      (T + 2) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ := BridgeRed.runs_peekTop (σ' := σ') k S s hs
  obtain ⟨s2, t2, e2, ⟨hs2, -⟩, ht2⟩ := hp s1 hs1
  have hc : BridgeRed.topIsBit s1.var = b := by
    have h : s1.var = ((S k).head?, s1.var.2) := Prod.ext hv1 rfl
    rw [h]
    exact hb _
  cases b
  · exact ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_false hc e2), ⟨hs2, trivial⟩, by omega⟩
  · exact ⟨s2, t1 + (t2 + 1), Eval.seq e1 (Eval.ite_true hc e2), ⟨hs2, trivial⟩, by omega⟩

/-! ## Small facts on encodings -/

theorem natSyms_zero_x : natSyms 0 = [] := rfl

theorem natSyms_eq_map_x (n : ℕ) : natSyms n = (encodeNat n).map Sym.bit := rfl

theorem length_natSyms_x (n : ℕ) : (natSyms n).length = bitLen n := by
  simp [natSyms, bitLen]

theorem bitLen_le_self_x (n : ℕ) : bitLen n ≤ n := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le.2 Nat.lt_two_pow_self

theorem bitLen_pow_two_x (a : ℕ) : bitLen (2 ^ a) = a + 1 := by
  simp [bitLen, encodeNat_pow_two]

theorem bitLen_one_x : bitLen 1 = 1 := by
  have h := congrArg List.length natSyms_one
  rw [length_natSyms_x] at h
  simpa using h

theorem length_hdrSyms_cons_x (a : ℕ) (L : List ℕ) :
    (hdrSyms (a :: L)).length = bitLen a + 1 + (hdrSyms L).length := by
  rw [hdrSyms_cons']
  simp [length_natSyms_x]
  omega

theorem bitLen_le_hdrSyms {f : ℕ} : ∀ {L : List ℕ}, f ∈ L → bitLen f + 1 ≤ (hdrSyms L).length
  | [], h => by simp at h
  | a :: L, h => by
    rw [length_hdrSyms_cons_x]
    rcases List.mem_cons.1 h with rfl | h'
    · omega
    · have := bitLen_le_hdrSyms h'
      omega

theorem length_le_hdrSyms : ∀ L : List ℕ, L.length ≤ (hdrSyms L).length
  | [] => by simp [hdrSyms_nil]
  | a :: L => by
    rw [length_hdrSyms_cons_x, List.length_cons]
    have := length_le_hdrSyms L
    omega

theorem sum_le_hdrSyms_pow : ∀ es : List ℕ, es.sum ≤ (hdrSyms (es.map (2 ^ ·))).length
  | [] => by simp
  | e :: es => by
    rw [List.map_cons, length_hdrSyms_cons_x, bitLen_pow_two_x, List.sum_cons]
    have := sum_le_hdrSyms_pow es
    omega

theorem sep2_not_mem_rev_hdr (L : List ℕ) : Sym.sep2 ∉ (hdrSyms L).reverse := by
  rw [List.mem_reverse]
  exact BridgePP.sep2_not_mem_hdrSyms L

/-! ## Stacks of the exposure machine -/

/-- Private scratch of the exposure machine: `T` the skipped header fields (guard `sep2` at the
bottom); `I` the axis counter; `D` the field countdown; `U1`, `U2` the interchange bit counters
(`log₂ t_i` and `ℓ`); `GB`, `BB` the interchange counters `G` and `B`; `W` the record width `2·wI`;
`tmp` scratch of the copies and decrements. -/
inductive XS
  | T | I | D | U1 | U2 | GB | BB | W | tmp
  deriving DecidableEq

instance : Fintype XS where
  elems := {XS.T, XS.I, XS.D, XS.U1, XS.U2, XS.GB, XS.BB, XS.W, XS.tmp}
  complete := by intro x; cases x <;> simp

/-- Stacks of the exposure machine: the bridge stacks, the private scratch `XS`, and the scratch
of the embedded interchange program `P6`. -/
abbrev XL (E6 : Type) : Type := KLoc BrK (XS ⊕ E6)

/-- A private stack of the exposure machine. -/
abbrev xs {E6 : Type} (s : XS) : XL E6 := .inr (.inl s)

/-- Embedding of the interchange stacks: `0 ↦ arr`, `1, 2 ↦ U1, U2` (swapped when `rst`), `3 ↦ GB`,
`4 ↦ BB`, `5 ↦ W`; the interchange scratch goes to its own part of the scratch. -/
def ι6 {E6 : Type} (rst : Bool) : KLoc (Fin 6) E6 → XL E6
  | .inl j =>
    if j.val = 0 then kW .arr else if j.val = 1 then xs (cond rst .U2 .U1)
    else if j.val = 2 then xs (cond rst .U1 .U2) else if j.val = 3 then xs .GB
    else if j.val = 4 then xs .BB else xs .W
  | .inr e => .inr (.inr e)

theorem ι6_injective {E6 : Type} (rst : Bool) : Function.Injective (ι6 (E6 := E6) rst) := by
  rintro (a | a) (b | b) h
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    interval_cases a <;> interval_cases b <;> cases rst <;> simp_all [ι6]
  · obtain ⟨a, ha⟩ := a
    interval_cases a <;> cases rst <;> simp_all [ι6]
  · obtain ⟨b, hb⟩ := b
    interval_cases b <;> cases rst <;> simp_all [ι6]
  · simp_all [ι6]

/-! ## Programs -/

section Progs

variable {E6 R6 : Type} [DecidableEq E6]

/-- Header part (`SProg`): guard, skip `p, P, ω`, `W := 2·wI`, skip `wI … wIn`, `D := d`, skip `d`,
`I := i`. -/
def headA : SProg (XL E6) :=
  .seq (pushC (xs .T) .sep2)
  (.seq (BridgePP.skipFields (kN .par) (xs .T) 3)
  (.seq (pushC (xs .W) .mark)
  (.seq (copyBlock (kN .par) (xs .W) (xs .tmp))
  (.seq (pushC (xs .W) (.bit false))
  (.seq (BridgePP.skipFields (kN .par) (xs .T) 5)
  (.seq (copyBlock (kN .par) (xs .D) (xs .tmp))
  (.seq (BridgePP.skipFields (kN .par) (xs .T) 1)
    (copyBlock (kW .ax) (xs .I) (xs .tmp)))))))))

/-- Scan to axis `i`: skip `i` shape fields, read `log₂ t_i` onto `U1`, decrement `D`. -/
def scanA : Prog (XL E6) (fun _ => Sym) (Option Sym × R6) :=
  .seq (skipLoop (kN .par) (xs .T) (xs .I) (xs .D) (xs .tmp))
  (.seq (lift (pushC (xs .U1) .mark))
  (.seq (countField (kN .par) (xs .T) (xs .U1) (xs .tmp))
    (lift (BridgePP.decIfPos (xs .D) (xs .tmp)))))

/-- Cleanup (`SProg`): rewind the header from `T`, drop `U1` and `W`. -/
def tailA : SProg (XL E6) :=
  .seq (WP.W9comp.rewindTo (xs .T) (kN .par) .sep2)
  (.seq (WP.W9mp.dropTo (xs .U1) .mark) (WP.W9mp.dropTo (xs .W) .mark))

/-- The interchange branch (`i < d-1`). -/
def callA (rst : Bool) (P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6) :
    Prog (XL E6) (fun _ => Sym) (Option Sym × R6) :=
  .seq (lift (.seq (BridgePP.decIfPos (xs .D) (xs .tmp))
    (.seq (pushC (xs .GB) .mark) (pushC (xs .GB) (.bit true)))))
  (.seq (unaryLoop (kN .par) (xs .T) (xs .D) (xs .GB) (xs .tmp))
  (.seq (lift (pushC (xs .U2) .mark))
  (.seq (countField (kN .par) (xs .T) (xs .U2) (xs .tmp))
  (.seq (lift (.seq (pushC (xs .BB) .mark) (pushC (xs .BB) (.bit true))))
  (.seq (callInj (ι6 rst) (Lens.snd (Option Sym) R6) P6)
    (lift (.seq (WP.W9mp.dropTo (xs .U2) .mark) (.seq (WP.W9mp.dropTo (xs .GB) .mark)
      (WP.W9mp.dropTo (xs .BB) .mark)))))))))

/-- **The exposure (`rst = false`) / restoration (`rst = true`) machine** of one axis. -/
def exposeProg (rst : Bool) (P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6) :
    Prog (XL E6) (fun _ => Sym) (Option Sym × R6) :=
  .seq (lift headA) (.seq scanA (.seq (BridgeRed.peekTop (xs .D))
    (.ite BridgeRed.topIsBit (.seq (callA rst P6) (lift tailA)) (lift tailA))))

theorem closed_copyBlock_x (a b c : XL E6) : (copyBlock a b c).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup,
    dupBody, restoreR, popR, pushR, pushC, skip]

theorem closed_headA : (headA (E6 := E6)).Closed := by
  have h3 := BridgePP.closed_skipFields (K := XL E6) (kN .par) (xs .T) 3
  have h5 := BridgePP.closed_skipFields (K := XL E6) (kN .par) (xs .T) 5
  have h1 := BridgePP.closed_skipFields (K := XL E6) (kN .par) (xs .T) 1
  have hc1 := closed_copyBlock_x (kN .par : XL E6) (xs .W) (xs .tmp)
  have hc2 := closed_copyBlock_x (kN .par : XL E6) (xs .D) (xs .tmp)
  have hc3 := closed_copyBlock_x (kW .ax : XL E6) (xs .I) (xs .tmp)
  simp only [headA, Prog.Closed] at h3 h5 h1 hc1 hc2 hc3 ⊢
  exact ⟨trivial, h3, trivial, hc1, trivial, h5, hc2, h1, hc3⟩

theorem closed_scanA : (scanA (E6 := E6) (R6 := R6)).Closed := by
  have h1 := closed_skipLoop (σ' := R6) (kN .par : XL E6) (xs .T) (xs .I) (xs .D) (xs .tmp)
  have h2 := closed_countField (σ' := R6) (kN .par : XL E6) (xs .T) (xs .U1) (xs .tmp)
  have h3 : (lift (σ' := R6) (BridgePP.decIfPos (xs .D : XL E6) (xs .tmp))).Closed :=
    closed_lift (BridgePP.closed_decIfPos _ _)
  have h4 : (lift (σ' := R6) (pushC (xs .U1 : XL E6) .mark)).Closed := closed_lift trivial
  simp only [scanA, Prog.Closed] at h1 h2 h3 h4 ⊢
  exact ⟨h1, h4, h2, h3⟩

theorem closed_tailA : (tailA (E6 := E6)).Closed := by
  have h1 : (WP.W9comp.rewindTo (xs .T : XL E6) (kN .par) .sep2).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, WP.W9comp.rewindTo, WP.W9comp.rewindBody, popR, pushR]
  have h2 := WP.W9mp.closed_dropTo (xs .U1 : XL E6) .mark
  have h3 := WP.W9mp.closed_dropTo (xs .W : XL E6) .mark
  simp only [tailA, Prog.Closed] at h1 h2 h3 ⊢
  exact ⟨h1, h2, h3⟩

theorem closed_callA (rst : Bool) {P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6}
    (h6 : P6.Closed) : (callA rst P6).Closed := by
  have hd := BridgePP.closed_decIfPos (xs .D : XL E6) (xs .tmp)
  have h1 : (lift (σ' := R6) (.seq (BridgePP.decIfPos (xs .D : XL E6) (xs .tmp))
      (.seq (pushC (xs .GB) .mark) (pushC (xs .GB) (.bit true))))).Closed :=
    closed_lift (by simp only [Prog.Closed] at hd ⊢; exact ⟨hd, trivial, trivial⟩)
  have h2 := closed_unaryLoop (σ' := R6) (kN .par : XL E6) (xs .T) (xs .D) (xs .GB) (xs .tmp)
  have h3 : (lift (σ' := R6) (pushC (xs .U2 : XL E6) .mark)).Closed := closed_lift trivial
  have h4 := closed_countField (σ' := R6) (kN .par : XL E6) (xs .T) (xs .U2) (xs .tmp)
  have h5 : (lift (σ' := R6) (.seq (pushC (xs .BB : XL E6) .mark)
      (pushC (xs .BB) (.bit true)))).Closed :=
    closed_lift (by simp only [Prog.Closed]; exact ⟨trivial, trivial⟩)
  have h6' := closed_callInj (ι6 rst) (Lens.snd (Option Sym) R6) h6
  have hu := WP.W9mp.closed_dropTo (xs .U2 : XL E6) .mark
  have hg := WP.W9mp.closed_dropTo (xs .GB : XL E6) .mark
  have hb := WP.W9mp.closed_dropTo (xs .BB : XL E6) .mark
  have h7 : (lift (σ' := R6) (.seq (WP.W9mp.dropTo (xs .U2 : XL E6) .mark)
      (.seq (WP.W9mp.dropTo (xs .GB) .mark) (WP.W9mp.dropTo (xs .BB) .mark)))).Closed :=
    closed_lift (by simp only [Prog.Closed] at hu hg hb ⊢; exact ⟨hu, hg, hb⟩)
  simp only [callA, Prog.Closed] at h1 h2 h3 h4 h5 h6' h7 ⊢
  exact ⟨h1, h2, h3, h4, h5, h6', h7⟩

theorem closed_exposeProg (rst : Bool) {P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6}
    (h6 : P6.Closed) : (exposeProg rst P6).Closed := by
  have hH : (lift (σ' := R6) (headA (E6 := E6))).Closed := closed_lift closed_headA
  have hS := closed_scanA (E6 := E6) (R6 := R6)
  have hP := BridgeRed.closed_peekTop (σ' := R6) (xs .D : XL E6)
  have hT : (lift (σ' := R6) (tailA (E6 := E6))).Closed := closed_lift closed_tailA
  have hC := closed_callA rst h6
  simp only [exposeProg, Prog.Closed] at hH hS hP hT hC ⊢
  exact ⟨hH, hS, hP, ⟨hC, hT⟩, hT⟩

end Progs

/-! ## Shape arithmetic -/

section Shape

variable {d : ℕ}

/-- Bit width `log₂ t_m` of axis `m` (`0` beyond `d`). -/
def aN (t : Fin d → ℕ) (m : ℕ) : ℕ := Nat.log2 (tAt t 1 m)

theorem tAt_one_of_lt (t : Fin d → ℕ) {m : ℕ} (hm : m < d) : tAt t 1 m = t ⟨m, hm⟩ := by
  simp [tAt, hm]

theorem tAt_one_val (t : Fin d → ℕ) (m : Fin d) : tAt t 1 m = t m := by
  simp [tAt]

theorem tAt_eq_pow {t : Fin d → ℕ} (ht : ShapeOK t) {m : ℕ} (hm : m < d) :
    tAt t 1 m = 2 ^ aN t m := by
  obtain ⟨_, a, ha⟩ := ht ⟨m, hm⟩
  rw [aN, tAt_one_of_lt t hm, ha, Nat.log2_two_pow]

theorem ofFn_eq_map_range (t : Fin d → ℕ) : List.ofFn t = (List.range d).map (tAt t 1) := by
  apply List.ext_getElem
  · simp
  · intro m h1 h2
    have hm : m < d := by simpa using h1
    simp [tAt_one_of_lt t hm]

theorem range_split1 {i n : ℕ} (hi : i < n) :
    List.range n = List.range' 0 i ++ i :: List.range' (i + 1) (n - 1 - i) := by
  rw [List.range_eq_range']
  have e1 : List.range' 0 n = List.range' 0 i ++ List.range' i (n - i) := by
    have h := (List.range'_append_1 (s := 0) (m := i) (n := n - i)).symm
    rw [show i + (n - i) = n by omega, Nat.zero_add] at h
    exact h
  have e2 : List.range' i (n - i) = i :: List.range' (i + 1) (n - 1 - i) := by
    rw [show n - i = (n - 1 - i) + 1 by omega, List.range'_succ]
  rw [e1, e2]

theorem range'_split_last {s n : ℕ} (hn : 1 ≤ n) :
    List.range' s n = List.range' s (n - 1) ++ [s + n - 1] := by
  have h := (List.range'_append_1 (s := s) (m := n - 1) (n := 1)).symm
  rw [show n - 1 + 1 = n by omega] at h
  rw [h, show s + n - 1 = s + (n - 1) by omega] <;> rfl

theorem ofFn_split (t : Fin d → ℕ) {i : ℕ} (hi : i < d) :
    List.ofFn t = (List.range' 0 i).map (tAt t 1) ++
      tAt t 1 i :: (List.range' (i + 1) (d - 1 - i)).map (tAt t 1) := by
  rw [ofFn_eq_map_range, range_split1 hi, List.map_append, List.map_cons]

theorem prod_map_pow (f : ℕ → ℕ) : ∀ L : List ℕ,
    (L.map fun m => 2 ^ f m).prod = 2 ^ (L.map f).sum
  | [] => by simp
  | m :: L => by simp [prod_map_pow f L, pow_add]

theorem map_tAt_eq {t : Fin d → ℕ} (ht : ShapeOK t) {s n : ℕ} (h : s + n ≤ d) :
    (List.range' s n).map (tAt t 1) = (List.range' s n).map fun m => 2 ^ aN t m := by
  refine List.map_congr_left fun m hm => ?_
  rw [List.mem_range'_1] at hm
  exact tAt_eq_pow ht (by omega)

theorem blockProd_eq_pow {t : Fin d → ℕ} (ht : ShapeOK t) {s n : ℕ} (h : s + n ≤ d) :
    blockProd t 1 s n = 2 ^ ((List.range' s n).map (aN t)).sum := by
  rw [blockProd, map_tAt_eq ht h, prod_map_pow]

theorem totalLen_eq_prod (t : Fin d → ℕ) :
    totalLen t = ((List.range d).map (tAt t 1)).prod := by
  rw [← ofFn_eq_map_range, List.prod_ofFn]

theorem totalLen_split (t : Fin d → ℕ) {i : ℕ} (hi : i < d - 1) :
    totalLen t = blockProd t 1 0 i * tAt t 1 i * blockProd t 1 (i + 1) (d - 2 - i) *
      tAt t 1 (d - 1) := by
  rw [totalLen_eq_prod, range_split (p := i) (q := d - 1) (n := d) hi (by omega),
    show d - 1 - i - 1 = d - 2 - i by omega, show d - (d - 1) - 1 = 0 by omega]
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons, blockProd,
    List.range'_zero, List.map_nil, List.prod_nil, mul_one]
  ring

theorem tAt_last {t : Fin d → ℕ} {k ℓ : ℕ} (hb : BalancedShape t k ℓ) :
    tAt t 1 (d - 1) = 2 ^ ℓ := by
  have hd : 2 ≤ d := hb.1
  rw [tAt_one_of_lt t (by omega : d - 1 < d), hb.2.2.2.1 (by omega)]

theorem aN_bal {t : Fin d → ℕ} {k ℓ : ℕ} (hb : BalancedShape t k ℓ) {m : ℕ} (hm : m < d) :
    aN t m = ℓ ∨ aN t m + 1 = ℓ := by
  have hℓ : 2 ≤ ℓ := hb.2.2.1
  rcases hb.2.2.2.2 ⟨m, hm⟩ with h | h
  · left
    rw [aN, tAt_one_of_lt t hm, h, Nat.log2_two_pow]
  · right
    have e : 2 ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ ℓ)]
    have h2 : t ⟨m, hm⟩ = 2 ^ (ℓ - 1) := Nat.eq_of_mul_eq_mul_left (by norm_num) (h.trans e)
    rw [aN, tAt_one_of_lt t hm, h2, Nat.log2_two_pow]
    omega

theorem axisBits_bal {t : Fin d → ℕ} {k ℓ : ℕ} (hb : BalancedShape t k ℓ) :
    axisBits t = ℓ := by
  have hd : 2 ≤ d := hb.1
  apply le_antisymm
  · unfold axisBits
    apply Finset.sup_le
    intro m _
    have h1 := aN_bal hb m.isLt
    rw [aN, tAt_one_val] at h1
    show Nat.log2 (t m) ≤ ℓ
    omega
  · have h1 : Nat.log2 (t ⟨d - 1, by omega⟩) = ℓ := by
      rw [hb.2.2.2.1 (by omega), Nat.log2_two_pow]
    rw [← h1]
    unfold axisBits
    exact Finset.le_sup (f := fun i => Nat.log2 (t i)) (Finset.mem_univ _)

end Shape

theorem vol_const {w : ℕ} : ∀ v : List (List Bool), (∀ p ∈ v, p.length = w) →
    vol v = v.length * (w + 1)
  | [], _ => by simp [vol, arrSyms, blk]
  | p :: v, h => by
    have ih := vol_const v fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp : p.length = w := h p (List.mem_cons_self ..)
    simp only [vol, arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append] at ih ⊢
    rw [ih, recSyms, List.length_append, List.length_map, List.length_singleton, hp,
      List.length_cons]
    ring

theorem length_crec1 (w : ℕ) (c : CInt) : (crecBits w [c]).length = 2 * w := by
  simp only [crecBits, coefBits, twosBits, bitsLE, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.length_append, List.length_map, List.length_range]
  omega

/-! ## The Lemma A.8 (`lem:transfer12`) interchange specification -/

/-- The runtime specification of an interchange program `P6` with constant `C6` (Lemma A.8 (`lem:transfer12`)): the body of
`C6InterchangeStmt τ` (`Contracts/AppC.lean`). -/
def C6Spec (τ : ℝ) (E6 R6 : Type) [DecidableEq E6] (C6 : ℕ)
    (P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6) : Prop :=
  ∀ (A u1 u2 G B w : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 r5 : List Sym)
    (S : KLoc (Fin 6) E6 → List Sym),
    1 ≤ u1 → 1 ≤ u2 → u1 ≤ u2 + 1 → u2 ≤ u1 + 1 → 1 ≤ A → 1 ≤ G → 1 ≤ B →
    v.length = A * 2 ^ u1 * G * 2 ^ u2 * B → (∀ p ∈ v, p.length = w) →
    BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 →
    S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms u1 ++ r1 →
    S (.inl 2) = natSyms u2 ++ r2 → S (.inl 3) = natSyms G ++ r3 →
    S (.inl 4) = natSyms B ++ r4 → S (.inl 5) = natSyms w ++ r5 →
    Runs P6 S
      (Function.update S (.inl 0)
        (arrSyms (permByInv (swapFieldsInv (2 ^ u1) G (2 ^ u2) B) v) ++ rest))
      (fun _ => True) (C6 * (⌈(vol v : ℝ) * ((max u1 u2 : ℕ) : ℝ) ^ τ⌉₊ + 1))

theorem hdrSyms_hdr_split (b : BrPar) :
    hdrSyms b.hdr = hdrSyms [b.p, b.P, b.ω] ++ (hdrSyms [b.wI, b.wT, b.wOut, b.pIn, b.wIn] ++
      (hdrSyms [b.d] ++ hdrSyms (List.ofFn b.t))) := by
  simp only [BrPar.hdr, List.cons_append, List.nil_append, hdrSyms_cons', hdrSyms_nil,
    List.append_assoc]

theorem le_sum_of_mem_x {e : ℕ} : ∀ {L : List ℕ}, e ∈ L → e ≤ L.sum
  | [], h => by simp at h
  | a :: L, h => by
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · omega
    · have := le_sum_of_mem_x h'
      omega

theorem carrSyms_recsAt {α : Type} (w : ℕ) (addrs : List α) (v : α → CInt) :
    carrSyms w (recsAt addrs v) = arrSyms (addrs.map fun j => crecBits w [v j]) := by
  rw [carrSyms, recsAt, List.map_map]
  rfl

/-! ## Phase lemmas -/

section Phases

variable {E6 R6 : Type} [DecidableEq E6]

/-- **Header phase.** -/
theorem runs_headA (b : BrPar) {i : ℕ} (hi : i < b.d) (rax rpar : List Sym)
    (S : XL E6 → List Sym) (hcl : KClean S) (hwI : 1 ≤ b.wI) (hrax : TermOK rax)
    (hax : S (kW .ax) = natSyms i ++ rax) (hpar : S (kN .par) = hdrSyms b.hdr ++ rpar) :
    ∃ Z, Runs (lift (σ' := R6) (headA (E6 := E6))) S Z (fun _ => True)
        (40 * ((hdrSyms b.hdr).length + 1)) ∧
      Z (kN .par) = hdrSyms (List.ofFn b.t) ++ rpar ∧
      Z (xs .T) = (hdrSyms [b.d]).reverse ++ ((hdrSyms [b.wI, b.wT, b.wOut, b.pIn, b.wIn]).reverse
        ++ ((hdrSyms [b.p, b.P, b.ω]).reverse ++ [Sym.sep2])) ∧
      Z (xs .W) = natSyms (2 * b.wI) ++ [Sym.mark] ∧ Z (xs .D) = natSyms b.d ∧
      Z (xs .I) = natSyms i ∧
      ∀ k, k ≠ kN .par → k ≠ xs .T → k ≠ xs .W → k ≠ xs .D → k ≠ xs .I → Z k = S k := by
  have hcl' : ∀ e, S (.inr e) = [] := hcl
  have hpar0 : S (kN .par) = hdrSyms [b.p, b.P, b.ω] ++ (hdrSyms [b.wI, b.wT, b.wOut, b.pIn, b.wIn]
      ++ (hdrSyms [b.d] ++ (hdrSyms (List.ofFn b.t) ++ rpar))) := by
    rw [hpar, hdrSyms_hdr_split]
    simp only [List.append_assoc]
  have r0 := BridgePP.runs_pushC (xs .T : XL E6) Sym.sep2 S
  set S0 := Function.update S (xs .T) (Sym.sep2 :: S (xs .T)) with hS0
  have r1 := BridgePP.runs_skipFields (src := (kN .par : XL E6)) (dst := xs .T) (by simp)
    [b.p, b.P, b.ω] (hdrSyms [b.wI, b.wT, b.wOut, b.pIn, b.wIn] ++ (hdrSyms [b.d] ++
      (hdrSyms (List.ofFn b.t) ++ rpar))) S0 (by simp [hS0, hpar0])
  set S1 := Function.update (Function.update S0 (kN .par)
    (hdrSyms [b.wI, b.wT, b.wOut, b.pIn, b.wIn] ++ (hdrSyms [b.d] ++
      (hdrSyms (List.ofFn b.t) ++ rpar)))) (xs .T)
    ((hdrSyms [b.p, b.P, b.ω]).reverse ++ S0 (xs .T)) with hS1
  have r2 := BridgePP.runs_pushC (xs .W : XL E6) Sym.mark S1
  set S2 := Function.update S1 (xs .W) (Sym.mark :: S1 (xs .W)) with hS2
  have r3 := BridgePP.runs_copyBlock (src := (kN .par : XL E6)) (dst := xs .W) (tmp := xs .tmp) (by simp)
    (by simp) (by simp) (encodeNat b.wI) (Sym.mark :: (hdrSyms [b.wT, b.wOut, b.pIn, b.wIn] ++
      (hdrSyms [b.d] ++ (hdrSyms (List.ofFn b.t) ++ rpar)))) S2 (BridgePP.termOK_mark_cons _)
    (by simp [hS2, hS1, hdrSyms_cons', ← natSyms_eq_map_x])
  set S3 := Function.update S2 (xs .W) ((encodeNat b.wI).map Sym.bit ++ S2 (xs .W)) with hS3
  have r4 := BridgePP.runs_pushC (xs .W : XL E6) (Sym.bit false) S3
  set S4 := Function.update S3 (xs .W) (Sym.bit false :: S3 (xs .W)) with hS4
  have r5 := BridgePP.runs_skipFields (src := (kN .par : XL E6)) (dst := xs .T) (by simp)
    [b.wI, b.wT, b.wOut, b.pIn, b.wIn] (hdrSyms [b.d] ++ (hdrSyms (List.ofFn b.t) ++ rpar)) S4
    (by simp [hS4, hS3, hS2, hS1])
  set S5 := Function.update (Function.update S4 (kN .par) (hdrSyms [b.d] ++
      (hdrSyms (List.ofFn b.t) ++ rpar))) (xs .T)
    ((hdrSyms [b.wI, b.wT, b.wOut, b.pIn, b.wIn]).reverse ++ S4 (xs .T)) with hS5
  have r6 := BridgePP.runs_copyBlock (src := (kN .par : XL E6)) (dst := xs .D) (tmp := xs .tmp) (by simp)
    (by simp) (by simp) (encodeNat b.d) (Sym.mark :: (hdrSyms (List.ofFn b.t) ++ rpar)) S5
    (BridgePP.termOK_mark_cons _) (by simp [hS5, hdrSyms_cons', hdrSyms_nil, ← natSyms_eq_map_x])
  set S6 := Function.update S5 (xs .D) ((encodeNat b.d).map Sym.bit ++ S5 (xs .D)) with hS6
  have r7 := BridgePP.runs_skipFields (src := (kN .par : XL E6)) (dst := xs .T) (by simp)
    [b.d] (hdrSyms (List.ofFn b.t) ++ rpar) S6 (by simp [hS6, hS5])
  set S7 := Function.update (Function.update S6 (kN .par) (hdrSyms (List.ofFn b.t) ++ rpar))
    (xs .T) ((hdrSyms [b.d]).reverse ++ S6 (xs .T)) with hS7
  have r8 := BridgePP.runs_copyBlock (src := (kW .ax : XL E6)) (dst := xs .I) (tmp := xs .tmp) (by simp)
    (by simp) (by simp) (encodeNat i) rax S7 hrax
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hS0, hax, ← natSyms_eq_map_x])
  set S8 := Function.update S7 (xs .I) ((encodeNat i).map Sym.bit ++ S7 (xs .I)) with hS8
  have hall := WP.W9comp.runs_seq r0 (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5
      (WP.W9comp.runs_seq r6 (WP.W9comp.runs_seq r7 r8)))))))
  refine ⟨S8, WP.W9comp.runs_mono (runs_lift hall) (fun _ _ => trivial) ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · have hs := congrArg List.length (hdrSyms_hdr_split b)
    simp only [List.length_append] at hs
    have h5 := length_hdrSyms_cons_x b.wI [b.wT, b.wOut, b.pIn, b.wIn]
    have hd1 := length_hdrSyms_cons_x b.d []
    have hi1 : (encodeNat i).length ≤ (encodeNat b.d).length := bitLen_le_of_le hi.le
    simp only [hdrSyms_nil, List.length_nil] at hd1
    unfold bitLen at h5 hd1
    omega
  · simp [hS8, hS7]
  · simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hS0, hcl']
  · rw [natSyms_two_mul hwI]
    simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hS0, hcl', ← natSyms_eq_map_x]
  · simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hS0, hcl', ← natSyms_eq_map_x]
  · simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hS0, hcl', ← natSyms_eq_map_x]
  · intro k h1 h2 h3 h4 h5
    simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hS0, h1, h2, h3, h4, h5]

/-- **Scan phase**: skip `t_0 … t_{i-1}`, read `log₂ t_i`, `D := d - i - 1`. -/
theorem runs_scanA (b : BrPar) (ht : ShapeOK b.t) {i : ℕ} (hi : i < b.d) (rpar : List Sym)
    (Z : XL E6 → List Sym) (H : ℕ) (hH : (hdrSyms b.hdr).length ≤ H)
    (hpar : Z (kN .par) = hdrSyms (List.ofFn b.t) ++ rpar) (hI : Z (xs .I) = natSyms i)
    (hD : Z (xs .D) = natSyms b.d) (hU1 : Z (xs .U1) = []) :
    ∃ Z', Runs (scanA (E6 := E6) (R6 := R6)) Z Z' (fun _ => True) (40 * (H + 1) ^ 2) ∧
      Z' (kN .par) = hdrSyms ((List.range' (i + 1) (b.d - 1 - i)).map (tAt b.t 1)) ++ rpar ∧
      Z' (xs .T) = (natSyms (tAt b.t 1 i) ++ [Sym.mark]).reverse ++
        ((hdrSyms ((List.range' 0 i).map (tAt b.t 1))).reverse ++ Z (xs .T)) ∧
      Z' (xs .I) = [] ∧ Z' (xs .D) = natSyms (b.d - i - 1) ∧
      Z' (xs .U1) = natSyms (aN b.t i) ++ [Sym.mark] ∧
      ∀ k, k ≠ kN .par → k ≠ xs .T → k ≠ xs .I → k ≠ xs .D → k ≠ xs .U1 → Z' k = Z k := by
  have hsplit := ofFn_split b.t hi
  have hAlen : ((List.range' 0 i).map (tAt b.t 1)).length = i := by simp
  have hdH : b.d + 9 ≤ H := by
    have h1 := length_le_hdrSyms b.hdr
    have h2 : b.hdr.length = 9 + b.d := by
      simp [BrPar.hdr] <;> omega
    omega
  have hmem : ∀ f ∈ List.ofFn b.t, bitLen f + 1 ≤ H := fun f hf =>
    le_trans (bitLen_le_hdrSyms (by simp only [BrPar.hdr]; exact List.mem_append_right _ hf)) hH
  have hti : tAt b.t 1 i = 2 ^ aN b.t i := tAt_eq_pow ht hi
  have haH : aN b.t i + 2 ≤ H := by
    have h1 := hmem (tAt b.t 1 i) (by rw [hsplit]; simp)
    rw [hti, bitLen_pow_two_x] at h1
    omega
  have hdbl : bitLen b.d ≤ H := le_trans (bitLen_le_self_x _) (by omega)
  have r1 := runs_skipLoop (σ' := R6) (par := (kN .par : XL E6)) (T := xs .T) (I := xs .I)
    (D := xs .D) (tmp := xs .tmp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp)
    ((List.range' 0 i).map (tAt b.t 1))
    (tAt b.t 1 i :: (List.range' (i + 1) (b.d - 1 - i)).map (tAt b.t 1))
    b.d H rpar Z (by rw [hpar, hsplit]) (by rw [hI, hAlen]) hD
    (fun f hf => by
      have := hmem f (by rw [hsplit]; exact List.mem_append_left _ hf)
      omega)
    hdbl (by rw [hAlen]; exact le_trans (bitLen_le_of_le hi.le) hdbl)
  set Z1 := Function.update (Function.update (Function.update (Function.update Z (kN .par)
    (hdrSyms (tAt b.t 1 i :: (List.range' (i + 1) (b.d - 1 - i)).map (tAt b.t 1)) ++ rpar))
    (xs .T) ((hdrSyms ((List.range' 0 i).map (tAt b.t 1))).reverse ++ Z (xs .T))) (xs .I) [])
    (xs .D) (natSyms (b.d - ((List.range' 0 i).map (tAt b.t 1)).length)) with hZ1
  have r2 := runs_lift (σ' := R6) (BridgePP.runs_pushC (xs .U1 : XL E6) Sym.mark Z1)
  set Z2 := Function.update Z1 (xs .U1) (Sym.mark :: Z1 (xs .U1)) with hZ2
  have r3 := runs_countField (σ' := R6) (src := (kN .par : XL E6)) (dst := xs .T)
    (cnt := xs .U1) (tmp := xs .tmp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (aN b.t i) 0 (hdrSyms ((List.range' (i + 1) (b.d - 1 - i)).map (tAt b.t 1)) ++ rpar)
    [Sym.mark] (BridgePP.termOK_mark_cons []) Z2 (by simp [hZ2, hZ1, hdrSyms_cons', hti])
    (by simp [hZ2, hZ1, hU1, natSyms_zero_x])
  set Z3 := Function.update (Function.update (Function.update Z2 (kN .par)
    (hdrSyms ((List.range' (i + 1) (b.d - 1 - i)).map (tAt b.t 1)) ++ rpar)) (xs .T)
    ((natSyms (2 ^ aN b.t i) ++ [Sym.mark]).reverse ++ Z2 (xs .T)))
    (xs .U1) (natSyms (0 + aN b.t i) ++ [Sym.mark]) with hZ3
  have r4 := runs_lift (σ' := R6) (BridgePP.runs_decIfPos (k := (xs .D : XL E6)) (t := xs .tmp)
    (by simp) (b.d - i) [] Z3 TermOK.nil (by simp [hZ3, hZ2, hZ1, hAlen]))
  refine ⟨_, WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 r4))) (fun _ _ => trivial) ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hAlen]
    have h1 : i * (19 * H + 30) ≤ H * (19 * H + 30) := Nat.mul_le_mul_right _ (by omega)
    have h2 : (aN b.t i + 1) * (6 * (0 + aN b.t i) + 20) ≤ (H + 1) * (6 * H + 20) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : bitLen (b.d - i) ≤ H := le_trans (bitLen_le_of_le (Nat.sub_le _ _)) hdbl
    nlinarith
  · simp [hZ3]
  · simp [hZ3, hZ2, hZ1, hti]
  · simp [hZ3, hZ2, hZ1]
  · simp [hZ3]
  · simp [hZ3]
  · intro k h1 h2 h3 h4 h5
    simp [hZ3, hZ2, hZ1, h1, h2, h3, h4, h5]

/-- **Cleanup phase.** -/
theorem runs_tailA (Z : XL E6 → List Sym) (Lt : List Sym) (hLt : Sym.sep2 ∉ Lt) (u w : ℕ)
    (hT : Z (xs .T) = Lt ++ [Sym.sep2]) (hU1 : Z (xs .U1) = natSyms u ++ [Sym.mark])
    (hW : Z (xs .W) = natSyms w ++ [Sym.mark]) :
    Runs (lift (σ' := R6) (tailA (E6 := E6))) Z
      (Function.update (Function.update (Function.update (Function.update Z (xs .T) [])
        (kN .par) (Lt.reverse ++ Z (kN .par))) (xs .U1) []) (xs .W) [])
      (fun _ => True) (3 * Lt.length + 2 + (2 * bitLen u + 2 + (2 * bitLen w + 2))) := by
  have r1 := BridgePP.runs_rewindTo (src := (xs .T : XL E6)) (dst := kN .par) (by simp) Sym.sep2 Lt []
    Z hLt hT
  have r2 := WP.W9mp.runs_popHdr (xs .U1 : XL E6) u []
    (Function.update (Function.update Z (xs .T) []) (kN .par) (Lt.reverse ++ Z (kN .par)))
    (by simp [hU1, hdrSyms_cons', hdrSyms_nil])
  have r3 := WP.W9mp.runs_popHdr (xs .W : XL E6) w []
    (Function.update (Function.update (Function.update Z (xs .T) []) (kN .par)
      (Lt.reverse ++ Z (kN .par))) (xs .U1) [])
    (by simp [hW, hdrSyms_cons', hdrSyms_nil])
  exact runs_lift (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 r3))

/-- **Interchange phase** (`i < d-1`): build the interchange counters, call `P6`, drop the counters. -/
theorem runs_callA (τ : ℝ) {C6 : ℕ} {P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6}
    (h6 : C6Spec τ E6 R6 C6 P6) (rst : Bool) (es : List ℕ) (a ℓ wI A H : ℕ)
    (v6 : List (List Bool)) (rpar rarr : List Sym) (Z : XL E6 → List Sym)
    (ha : 1 ≤ a) (hal : a ≤ ℓ) (hla : ℓ ≤ a + 1) (hA : 1 ≤ A)
    (hlen : v6.length = A * 2 ^ a * 2 ^ es.sum * 2 ^ ℓ)
    (hw : ∀ p ∈ v6, p.length = 2 * wI) (hrarr : BlkTerm rarr)
    (hsum : es.sum ≤ H) (hlH : ℓ ≤ H) (hesl : es.length + 1 ≤ H)
    (hpar : Z (kN .par) = hdrSyms (es.map (2 ^ ·) ++ [2 ^ ℓ]) ++ rpar)
    (hD : Z (xs .D) = natSyms (es.length + 1)) (hGB : Z (xs .GB) = [])
    (hU2 : Z (xs .U2) = []) (hBB : Z (xs .BB) = []) (hU1 : Z (xs .U1) = natSyms a ++ [Sym.mark])
    (hW : Z (xs .W) = natSyms (2 * wI) ++ [Sym.mark]) (harr : Z (kW .arr) = arrSyms v6 ++ rarr) :
    ∃ Z', Runs (callA rst P6) Z Z' (fun _ => True)
        (40 * (H + 1) ^ 2 + C6 * (⌈(vol v6 : ℝ) * (ℓ : ℝ) ^ τ⌉₊ + 1)) ∧
      Z' (kN .par) = rpar ∧
      Z' (xs .T) = (natSyms (2 ^ ℓ) ++ [Sym.mark]).reverse ++
        ((hdrSyms (es.map (2 ^ ·))).reverse ++ Z (xs .T)) ∧
      Z' (xs .D) = [] ∧
      Z' (kW .arr) = arrSyms (permByInv (swapFieldsInv (2 ^ cond rst ℓ a) (2 ^ es.sum)
        (2 ^ cond rst a ℓ) 1) v6) ++ rarr ∧
      ∀ k, k ≠ kN .par → k ≠ xs .T → k ≠ xs .D → k ≠ kW .arr → Z' k = Z k := by
  -- 1: `D := |es|`, `GB := [1, mark]`
  have r1a := BridgePP.runs_decIfPos (k := (xs .D : XL E6)) (t := xs .tmp) (by simp)
    (es.length + 1) [] Z TermOK.nil (by simp [hD])
  set Z1a := Function.update Z (xs .D) (natSyms (es.length + 1 - 1) ++ []) with hZ1a
  have r1b := BridgePP.runs_pushC (xs .GB : XL E6) Sym.mark Z1a
  set Z1b := Function.update Z1a (xs .GB) (Sym.mark :: Z1a (xs .GB)) with hZ1b
  have r1c := BridgePP.runs_pushC (xs .GB : XL E6) (Sym.bit true) Z1b
  set Z1 := Function.update Z1b (xs .GB) (Sym.bit true :: Z1b (xs .GB)) with hZ1
  have r1 := runs_lift (σ' := R6) (WP.W9comp.runs_seq r1a (WP.W9comp.runs_seq r1b r1c))
  -- 2: the middle fields in unary onto `GB`
  have r2 := runs_unaryLoop (σ' := R6) (par := (kN .par : XL E6)) (T := xs .T) (D := xs .D)
    (g := xs .GB) (tmp := xs .tmp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) es [2 ^ ℓ] H rpar Z1
    (by simp [hZ1, hZ1b, hZ1a, hpar]) (by simp [hZ1, hZ1b, hZ1a])
    (fun e he => le_trans (le_sum_of_mem_x he) hsum)
    (le_trans (bitLen_le_self_x _) (by omega))
  set Z2 := Function.update (Function.update (Function.update (Function.update Z1 (kN .par)
    (hdrSyms [2 ^ ℓ] ++ rpar)) (xs .T) ((hdrSyms (es.map (2 ^ ·))).reverse ++ Z1 (xs .T)))
    (xs .D) []) (xs .GB) (List.replicate es.sum (Sym.bit false) ++ Z1 (xs .GB)) with hZ2
  -- 3, 4: `U2 := ℓ`
  have r3 := runs_lift (σ' := R6) (BridgePP.runs_pushC (xs .U2 : XL E6) Sym.mark Z2)
  set Z3 := Function.update Z2 (xs .U2) (Sym.mark :: Z2 (xs .U2)) with hZ3
  have r4 := runs_countField (σ' := R6) (src := (kN .par : XL E6)) (dst := xs .T)
    (cnt := xs .U2) (tmp := xs .tmp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    ℓ 0 rpar [Sym.mark] (BridgePP.termOK_mark_cons []) Z3
    (by simp [hZ3, hZ2, hdrSyms_cons', hdrSyms_nil])
    (by simp [hZ3, hZ2, hZ1, hZ1b, hZ1a, hU2, natSyms_zero_x])
  set Z4 := Function.update (Function.update (Function.update Z3 (kN .par) rpar) (xs .T)
    ((natSyms (2 ^ ℓ) ++ [Sym.mark]).reverse ++ Z3 (xs .T))) (xs .U2)
    (natSyms (0 + ℓ) ++ [Sym.mark]) with hZ4
  -- 5: `BB := 1`
  have r5a := BridgePP.runs_pushC (xs .BB : XL E6) Sym.mark Z4
  set Z5a := Function.update Z4 (xs .BB) (Sym.mark :: Z4 (xs .BB)) with hZ5a
  have r5b := BridgePP.runs_pushC (xs .BB : XL E6) (Sym.bit true) Z5a
  set Z5 := Function.update Z5a (xs .BB) (Sym.bit true :: Z5a (xs .BB)) with hZ5
  have r5 := runs_lift (σ' := R6) (WP.W9comp.runs_seq r5a r5b)
  -- 6: interchange call (P6)
  have hmax : max (cond rst ℓ a) (cond rst a ℓ) = ℓ := by
    cases rst
    · exact max_eq_right hal
    · exact max_eq_left hal
  have hP := h6 A (cond rst ℓ a) (cond rst a ℓ) (2 ^ es.sum) 1 (2 * wI) v6 rarr [Sym.mark]
    [Sym.mark] [Sym.mark] [Sym.mark] [Sym.mark] (Z5 ∘ ι6 rst)
    (by cases rst <;> simp <;> omega) (by cases rst <;> simp <;> omega)
    (by cases rst <;> simp <;> omega) (by cases rst <;> simp <;> omega) hA
    Nat.one_le_two_pow le_rfl
    (by cases rst <;> rw [hlen] <;> simp only [cond_true, cond_false, mul_one] <;> ring) hw hrarr
    (BridgePP.termOK_mark_cons []) (BridgePP.termOK_mark_cons []) (BridgePP.termOK_mark_cons []) (BridgePP.termOK_mark_cons [])
    (BridgePP.termOK_mark_cons [])
    (by simp [ι6, hZ5, hZ5a, hZ4, hZ3, hZ2, hZ1, hZ1b, hZ1a, harr])
    (by cases rst <;> simp [ι6, hZ5, hZ5a, hZ4, hZ3, hZ2, hZ1, hZ1b, hZ1a, hU1])
    (by cases rst <;> simp [ι6, hZ5, hZ5a, hZ4, hZ3, hZ2, hZ1, hZ1b, hZ1a, hU1])
    (by simp [ι6, hZ5, hZ5a, hZ4, hZ3, hZ2, hZ1, hZ1b, hZ1a, hGB, natSyms_pow_two])
    (by simp [ι6, hZ5, hZ5a, hZ4, hZ3, hZ2, hZ1, hZ1b, hZ1a, hBB, natSyms_one])
    (by simp [ι6, hZ5, hZ5a, hZ4, hZ3, hZ2, hZ1, hZ1b, hZ1a, hW])
  rw [hmax] at hP
  have hc : Function.update Z5 (kW .arr) (arrSyms (permByInv (swapFieldsInv (2 ^ cond rst ℓ a)
      (2 ^ es.sum) (2 ^ cond rst a ℓ) 1) v6) ++ rarr) ∘ ι6 rst =
      Function.update (Z5 ∘ ι6 rst) (.inl 0) (arrSyms (permByInv (swapFieldsInv
        (2 ^ cond rst ℓ a) (2 ^ es.sum) (2 ^ cond rst a ℓ) 1) v6) ++ rarr) :=
    Function.update_comp_eq_of_injective Z5 (ι6_injective rst) (.inl 0) _
  have r6 : Runs (callInj (ι6 rst) (Lens.snd (Option Sym) R6) P6) Z5
      (Function.update Z5 (kW .arr) (arrSyms (permByInv (swapFieldsInv (2 ^ cond rst ℓ a)
        (2 ^ es.sum) (2 ^ cond rst a ℓ) 1) v6) ++ rarr)) (fun _ => True)
      (C6 * (⌈(vol v6 : ℝ) * (ℓ : ℝ) ^ τ⌉₊ + 1)) := by
    refine runs_callInj (Q := fun _ => True) (ι6_injective rst) (Lens.snd (Option Sym) R6) ?_ ?_
    · rw [hc]
      exact hP
    · intro k hk
      have hk0 : k ≠ kW .arr := by
        intro h
        apply hk (.inl 0)
        rw [h]
        simp [ι6]
      exact Function.update_of_ne hk0 _ _
  set Z6 := Function.update Z5 (kW .arr) (arrSyms (permByInv (swapFieldsInv (2 ^ cond rst ℓ a)
    (2 ^ es.sum) (2 ^ cond rst a ℓ) 1) v6) ++ rarr) with hZ6
  -- 7: drop `U2`, `GB`, `BB`
  have r7a := WP.W9mp.runs_popHdr (xs .U2 : XL E6) ℓ [] Z6
    (by simp [hZ6, hZ5, hZ5a, hZ4, hdrSyms_cons', hdrSyms_nil])
  set Z7a := Function.update Z6 (xs .U2) [] with hZ7a
  have r7b := WP.W9mp.runs_popHdr (xs .GB : XL E6) (2 ^ es.sum) [] Z7a
    (by simp [hZ7a, hZ6, hZ5, hZ5a, hZ4, hZ3, hZ2, hZ1, hZ1b, hZ1a, hGB, hdrSyms_cons',
      hdrSyms_nil, natSyms_pow_two])
  set Z7b := Function.update Z7a (xs .GB) [] with hZ7b
  have r7c := WP.W9mp.runs_popHdr (xs .BB : XL E6) 1 [] Z7b
    (by simp [hZ7b, hZ7a, hZ6, hZ5, hZ5a, hZ4, hZ3, hZ2, hZ1, hZ1b, hZ1a, hBB, hdrSyms_cons',
      hdrSyms_nil, natSyms_one])
  have r7 := runs_lift (σ' := R6) (WP.W9comp.runs_seq r7a (WP.W9comp.runs_seq r7b r7c))
  refine ⟨_, WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5
      (WP.W9comp.runs_seq r6 r7)))))) (fun _ _ => trivial) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : bitLen (es.length + 1) ≤ H := le_trans (bitLen_le_self_x _) hesl
    have e2 : es.length * (16 * H + 30) ≤ H * (16 * H + 30) := Nat.mul_le_mul_right _ (by omega)
    have e3 : (ℓ + 1) * (6 * (0 + ℓ) + 20) ≤ (H + 1) * (6 * H + 20) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e4 : bitLen ℓ ≤ H := le_trans (bitLen_le_self_x _) hlH
    rw [bitLen_pow_two_x, bitLen_one_x]
    nlinarith
  · simp [hZ7b, hZ7a, hZ6, hZ5, hZ5a, hZ4]
  · simp [hZ7b, hZ7a, hZ6, hZ5, hZ5a, hZ4, hZ3, hZ2, hZ1, hZ1b, hZ1a]
  · simp [hZ7b, hZ7a, hZ6, hZ5, hZ5a, hZ4, hZ3, hZ2]
  · simp [hZ7b, hZ7a, hZ6]
  · intro k h1 h2 h3 h4
    by_cases hg : k = xs .GB
    · subst hg
      simp [hZ7b, hGB]
    by_cases hu : k = xs .U2
    · subst hu
      simp [hZ7b, hZ7a, hU2]
    by_cases hb : k = xs .BB
    · subst hb
      simp [hBB]
    simp [hZ7b, hZ7a, hZ6, hZ5, hZ5a, hZ4, hZ3, hZ2, hZ1, hZ1b, hZ1a, h1, h2, h3, h4, hg, hu, hb]

end Phases

/-! ## The exposure machine -/

section Main

variable {E6 R6 : Type} [DecidableEq E6]

/-- **The exposure / restoration machine runs** (generic in the direction `rst` and in the address
lists): records in the order `addrsIn` become the records in the order `addrsOut`, provided the
Lemma A.8 (`lem:transfer12`) interchange `(t_i | G | t_{d-1})` (for `rst`: `(t_{d-1} | G | t_i)`) maps one to the other
when `i < d-1`, and the orders agree when `i = d-1`. Cost `200·setup + C6·(⌈V·ℓ^τ⌉₊ + 1)`. -/
theorem runs_exposeProg (τ : ℝ) {C6 : ℕ} {P6 : Prog (KLoc (Fin 6) E6) (fun _ => Sym) R6}
    (h6 : C6Spec τ E6 R6 C6 P6) (rst : Bool) (b : BrPar) (i : Fin b.d) {k ℓ : ℕ}
    (hbal : BalancedShape b.t k ℓ) (ht : ShapeOK b.t) (hwI : 1 ≤ b.wI)
    (addrsIn addrsOut : List (Idx b.t)) (v : Idx b.t → CInt)
    (hin : addrsIn.length = totalLen b.t)
    (hperm : (i : ℕ) < b.d - 1 → permByInv (swapFieldsInv (2 ^ cond rst ℓ (aN b.t i))
        (blockProd b.t 1 (i + 1) (b.d - 2 - i)) (2 ^ cond rst (aN b.t i) ℓ) 1)
        (addrsIn.map fun j => crecBits b.wI [v j]) = addrsOut.map fun j => crecBits b.wI [v j])
    (hlast : (i : ℕ) = b.d - 1 → addrsOut = addrsIn)
    (rarr rax rpar : List Sym) (S : XL E6 → List Sym) (hcl : KClean S) (hrarr : BlkTerm rarr)
    (hrax : TermOK rax) (harr : S (kW .arr) = carrSyms b.wI (recsAt addrsIn v) ++ rarr)
    (hax : S (kW .ax) = natSyms i ++ rax) (hpar : S (kN .par) = hdrSyms b.hdr ++ rpar) :
    Runs (exposeProg rst P6) S
      (Function.update S (kW .arr) (carrSyms b.wI (recsAt addrsOut v) ++ rarr))
      (fun _ => True)
      (200 * b.setup + C6 * (⌈(vol1 b.R b.wI : ℝ) * (ℓ : ℝ) ^ τ⌉₊ + 1)) := by
  have hcl' : ∀ e, S (.inr e) = [] := hcl
  have hd2 : 2 ≤ b.d := hbal.1
  have hℓ : 2 ≤ ℓ := hbal.2.2.1
  have hi : (i : ℕ) < b.d := i.isLt
  have hdH : b.d + 9 ≤ (hdrSyms b.hdr).length := by
    have h1 := length_le_hdrSyms b.hdr
    have h2 : b.hdr.length = 9 + b.d := by
      simp [BrPar.hdr] <;> omega
    omega
  have hsetup : ((hdrSyms b.hdr).length + 1) ^ 2 ≤ b.setup := by
    unfold BrPar.setup
    exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hX : (hdrSyms b.hdr).length + 1 ≤ ((hdrSyms b.hdr).length + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  have hmemt : ∀ f ∈ List.ofFn b.t, bitLen f + 1 ≤ (hdrSyms b.hdr).length := fun f hf =>
    bitLen_le_hdrSyms (by simp only [BrPar.hdr]; exact List.mem_append_right _ hf)
  have hwIH : bitLen (2 * b.wI) ≤ (hdrSyms b.hdr).length := by
    have h1 : bitLen b.wI + 1 ≤ (hdrSyms b.hdr).length :=
      bitLen_le_hdrSyms (by simp [BrPar.hdr])
    have h2 : bitLen (2 * b.wI) = bitLen b.wI + 1 := by
      rw [← length_natSyms_x, ← length_natSyms_x, natSyms_two_mul hwI, List.length_cons]
    omega
  have haN := aN_bal hbal hi
  have haH : bitLen (aN b.t i) ≤ (hdrSyms b.hdr).length := by
    have h1 := hmemt (tAt b.t 1 i) (by rw [ofFn_split b.t hi]; simp)
    rw [tAt_eq_pow ht hi, bitLen_pow_two_x] at h1
    have := bitLen_le_self_x (aN b.t i)
    omega
  have hv6 : carrSyms b.wI (recsAt addrsIn v) =
      arrSyms (addrsIn.map fun j => crecBits b.wI [v j]) := carrSyms_recsAt _ _ _
  have hw6 : ∀ p ∈ addrsIn.map (fun j => crecBits b.wI [v j]), p.length = 2 * b.wI := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
    exact length_crec1 _ _
  have hvol : vol (addrsIn.map fun j => crecBits b.wI [v j]) = vol1 b.R b.wI := by
    rw [vol_const _ hw6, List.length_map, hin, vol1]
  -- head and scan
  obtain ⟨ZA, rA, hA1, hA2, hA3, hA4, hA5, hA6⟩ :=
    runs_headA (E6 := E6) (R6 := R6) b hi rax rpar S hcl hwI hrax hax hpar
  have hAU1 : ZA (xs .U1) = [] := by
    rw [hA6 _ (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact hcl' _
  obtain ⟨ZB, rB, hB1, hB2, hB3, hB4, hB5, hB6⟩ :=
    runs_scanA (E6 := E6) (R6 := R6) b ht hi rpar ZA (hdrSyms b.hdr).length le_rfl hA1 hA5 hA4
      hAU1
  have hBW : ZB (xs .W) = natSyms (2 * b.wI) ++ [Sym.mark] := by
    rw [hB6 _ (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact hA3
  have hBarr : ZB (kW .arr) = S (kW .arr) := by
    rw [hB6 _ (by simp) (by simp) (by simp) (by simp) (by simp),
      hA6 _ (by simp) (by simp) (by simp) (by simp) (by simp)]
  have hBGB : ZB (xs .GB) = [] := by
    rw [hB6 _ (by simp) (by simp) (by simp) (by simp) (by simp),
      hA6 _ (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact hcl' _
  have hBU2 : ZB (xs .U2) = [] := by
    rw [hB6 _ (by simp) (by simp) (by simp) (by simp) (by simp),
      hA6 _ (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact hcl' _
  have hBBB : ZB (xs .BB) = [] := by
    rw [hB6 _ (by simp) (by simp) (by simp) (by simp) (by simp),
      hA6 _ (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact hcl' _
  by_cases hlt : (i : ℕ) < b.d - 1
  · -- the interchange branch
    set es := (List.range' (i + 1) (b.d - 2 - i)).map (aN b.t) with hes
    have hesl : es.length = b.d - 2 - i := by simp [hes]
    have hmid : (List.range' (i + 1) (b.d - 1 - i)).map (tAt b.t 1) =
        es.map (2 ^ ·) ++ [2 ^ ℓ] := by
      rw [range'_split_last (s := i + 1) (n := b.d - 1 - i) (by omega), List.map_append,
        map_tAt_eq (s := i + 1) (n := b.d - 1 - i - 1) ht (by omega), hes, List.map_map,
        List.map_singleton, show (i : ℕ) + 1 + (b.d - 1 - i) - 1 = b.d - 1 by omega,
        tAt_last hbal, show b.d - 1 - (i : ℕ) - 1 = b.d - 2 - i by omega]
      rfl
    have hofn : List.ofFn b.t = (List.range' 0 i).map (tAt b.t 1) ++ tAt b.t 1 i ::
        (es.map (2 ^ ·) ++ [2 ^ ℓ]) := by
      rw [ofFn_split b.t hi, hmid]
    have hsum : es.sum ≤ (hdrSyms b.hdr).length := by
      have h1 := sum_le_hdrSyms_pow es
      have h2 := congrArg List.length (hdrSyms_hdr_split b)
      rw [hofn] at h2
      simp only [hdrSyms_append', hdrSyms_cons', List.length_append, List.length_cons] at h2
      omega
    have hlH : ℓ ≤ (hdrSyms b.hdr).length := by
      have h1 := hmemt (2 ^ ℓ) (by rw [hofn]; simp)
      rw [bitLen_pow_two_x] at h1
      omega
    have hA : 1 ≤ blockProd b.t 1 0 i := by
      rw [blockProd_eq_pow ht (by omega)]
      exact Nat.one_le_two_pow
    have hlen : (addrsIn.map fun j => crecBits b.wI [v j]).length =
        blockProd b.t 1 0 i * 2 ^ aN b.t i * 2 ^ es.sum * 2 ^ ℓ := by
      rw [List.length_map, hin, totalLen_split b.t hlt, tAt_eq_pow ht hi, tAt_last hbal,
        blockProd_eq_pow (s := i + 1) (n := b.d - 2 - i) ht (by omega), ← hes]
    obtain ⟨ZC, rC, hC1, hC2, hC3, hC4, hC5⟩ := runs_callA (E6 := E6) (R6 := R6) τ h6 rst es
      (aN b.t i) ℓ b.wI (blockProd b.t 1 0 i) (hdrSyms b.hdr).length
      (addrsIn.map fun j => crecBits b.wI [v j]) rpar rarr ZB
      (by omega) (by omega) (by omega) hA hlen hw6 hrarr hsum hlH (by omega)
      (by rw [hB1, hmid]) (by rw [hB4]; congr 1; omega) hBGB hBU2 hBBB hB5 hBW
      (by rw [hBarr, harr, hv6])
    have hCT : ZC (xs .T) = (hdrSyms b.hdr).reverse ++ [Sym.sep2] := by
      rw [hC2, hB2, hA2, hdrSyms_hdr_split, hofn]
      simp [hdrSyms_append', hdrSyms_cons', hdrSyms_nil, List.reverse_append, List.append_assoc]
    have hCU1 : ZC (xs .U1) = natSyms (aN b.t i) ++ [Sym.mark] := by
      rw [hC5 _ (by simp) (by simp) (by simp) (by simp), hB5]
    have hCW : ZC (xs .W) = natSyms (2 * b.wI) ++ [Sym.mark] := by
      rw [hC5 _ (by simp) (by simp) (by simp) (by simp), hBW]
    have rD := runs_tailA (E6 := E6) (R6 := R6) ZC ((hdrSyms b.hdr).reverse)
      (sep2_not_mem_rev_hdr _) (aN b.t i) (2 * b.wI) hCT hCU1 hCW
    have hb : ∀ w : R6, BridgeRed.topIsBit ((ZB (xs .D)).head?, w) = true := by
      intro w
      rw [hB4, BridgeRed.topIsBit_natSyms]
      simp only [decide_eq_true_eq, ne_eq]
      omega
    have rI := runs_peek_ite (σ' := R6) (xs .D : XL E6) (.seq (callA rst P6) (lift tailA))
      (lift tailA) true hb (WP.W9comp.runs_seq rC rD)
    have hall := WP.W9comp.runs_seq rA (WP.W9comp.runs_seq rB rI)
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
    · funext k
      by_cases k1 : k = xs .W
      · subst k1
        simp [hcl']
      by_cases k2 : k = xs .U1
      · subst k2
        simp [hcl']
      by_cases k3 : k = kN .par
      · subst k3
        simp [hC1, hpar]
      by_cases k4 : k = xs .T
      · subst k4
        simp [hcl']
      by_cases k5 : k = kW .arr
      · subst k5
        have hp := hperm hlt
        rw [blockProd_eq_pow (s := i + 1) (n := b.d - 2 - i) ht (by omega), ← hes] at hp
        have n1 : (kW .arr : XL E6) ≠ xs .W := by simp
        have n2 : (kW .arr : XL E6) ≠ xs .U1 := by simp
        have n3 : (kW .arr : XL E6) ≠ kN .par := by simp
        have n4 : (kW .arr : XL E6) ≠ xs .T := by simp
        rw [Function.update_of_ne n1, Function.update_of_ne n2, Function.update_of_ne n3,
          Function.update_of_ne n4, Function.update_self, hC4, hp, carrSyms_recsAt]
      by_cases k6 : k = xs .D
      · subst k6
        simp [hC3, hcl']
      by_cases k7 : k = xs .I
      · subst k7
        simp [hC5 (xs .I) (by simp) (by simp) (by simp) (by simp), hB3, hcl']
      rw [Function.update_of_ne k1, Function.update_of_ne k2, Function.update_of_ne k3,
        Function.update_of_ne k4, Function.update_of_ne k5, hC5 k k3 k4 k6 k5,
        hB6 k k3 k4 k7 k6 k2, hA6 k k3 k4 k1 k6 k7]
    · rw [hvol, List.length_reverse]
      nlinarith [hsetup, hwIH, haH, hX]
  · -- the last axis: no interchange
    have hieq : (i : ℕ) = b.d - 1 := by omega
    have hofn : List.ofFn b.t = (List.range' 0 i).map (tAt b.t 1) ++ [tAt b.t 1 i] := by
      rw [ofFn_split b.t hi, show b.d - 1 - (i : ℕ) = 0 by omega, List.range'_zero,
        List.map_nil]
    have hBT : ZB (xs .T) = (hdrSyms b.hdr).reverse ++ [Sym.sep2] := by
      rw [hB2, hA2, hdrSyms_hdr_split, hofn]
      simp [hdrSyms_append', hdrSyms_cons', hdrSyms_nil, List.reverse_append, List.append_assoc]
    have hBpar : ZB (kN .par) = rpar := by
      rw [hB1, show b.d - 1 - (i : ℕ) = 0 by omega, List.range'_zero, List.map_nil, hdrSyms_nil,
        List.nil_append]
    have rD := runs_tailA (E6 := E6) (R6 := R6) ZB ((hdrSyms b.hdr).reverse)
      (sep2_not_mem_rev_hdr _) (aN b.t i) (2 * b.wI) hBT hB5 hBW
    have hb : ∀ w : R6, BridgeRed.topIsBit ((ZB (xs .D)).head?, w) = false := by
      intro w
      rw [hB4, BridgeRed.topIsBit_natSyms, show b.d - (i : ℕ) - 1 = 0 by omega] <;> simp
    have rI := runs_peek_ite (σ' := R6) (xs .D : XL E6) (.seq (callA rst P6) (lift tailA))
      (lift tailA) false hb rD
    have hall := WP.W9comp.runs_seq rA (WP.W9comp.runs_seq rB rI)
    have hio := hlast hieq
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
    · funext k
      by_cases k1 : k = xs .W
      · subst k1
        simp [hcl']
      by_cases k2 : k = xs .U1
      · subst k2
        simp [hcl']
      by_cases k3 : k = kN .par
      · subst k3
        simp [hBpar, hpar]
      by_cases k4 : k = xs .T
      · subst k4
        simp [hcl']
      by_cases k5 : k = kW .arr
      · subst k5
        simp [hBarr, harr, hio]
      by_cases k6 : k = xs .D
      · subst k6
        simp [hB4, show b.d - (i : ℕ) - 1 = 0 by omega, natSyms_zero_x, hcl']
      by_cases k7 : k = xs .I
      · subst k7
        simp [hB3, hcl']
      rw [Function.update_of_ne k1, Function.update_of_ne k2, Function.update_of_ne k3,
        Function.update_of_ne k4, Function.update_of_ne k5, hB6 k k3 k4 k7 k6 k2,
        hA6 k k3 k4 k1 k6 k7]
    · rw [List.length_reverse]
      nlinarith [hsetup, hwIH, haH, hX]

end Main

end SubNLogN.Machine.BridgeExp
