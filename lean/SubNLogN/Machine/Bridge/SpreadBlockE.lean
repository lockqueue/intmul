/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadBlockD

/-!
# K5 spreading: AR-level block step, part E (`Bridge/SpreadBlockE.lean`)

`postBlk_eval`: the AR part of one block step (final slots onto `Q`, tail slots, new tail, drain
the packed data, peek the next record), with an explicit final state and the cost bound
`blkCostA`. Everything is proved; the slot pass enters through `SlotSpecOf`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

/-- Cost bound of `postBlk`. -/
def blkCostA (s q wI m W Csp : ℕ) : ℕ :=
  1 + (m * (2 * (Csp * (s + 1)) + finCost s q wI + 2 + 1) + 1) + (9 * (W - 1) + 4) +
    (1 + ((W - 1) * (2 * (Csp * (s + 1)) + 2 + 1) + 1)) + 2 * (4 * (s * (W - 1)) + 2) +
    4 * (3 * (s * m) + 2) + 1

section Post

variable {Esu : Type} [DecidableEq Esu]
variable {prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K} {Csp : ℕ}
variable {s wI wT q m W : ℕ} {Epre B G : List CInt} {Q0 es : List Sym} {dd : Fin 4 → List Sym}
variable {S0 : SK Esu → List Sym}

theorem cpart_lt_slot (h : BlkHyp s wI wT q m W Epre B G) (k : Fin 4) (x : CInt) :
    cpart wI k x < 2 ^ s := by
  have h1 : 2 ^ (wI - 1) ≤ G.length * (2 ^ (wI - 1) * 2 ^ (wT - 1)) := by
    have hG1 : 1 ≤ G.length := by rw [h.hGW]; exact h.hW1
    have h2 : 1 ≤ 2 ^ (wT - 1) := Nat.one_le_two_pow
    calc 2 ^ (wI - 1) = 1 * (2 ^ (wI - 1) * 1) := by ring
      _ ≤ G.length * (2 ^ (wI - 1) * 2 ^ (wT - 1)) :=
        Nat.mul_le_mul hG1 (Nat.mul_le_mul_left _ h2)
  exact lt_of_le_of_lt (cpart_le wI k x) (lt_of_le_of_lt h1 h.hdig)

theorem length_encodeNat_pack (h : BlkHyp s wI wT q m W Epre B G) (k : Fin 4) :
    (encodeNat (pack s (B.map (cpart wI k)))).length ≤ s * m := by
  apply length_encodeNat_le
  have := pack_lt s (B.map (cpart wI k)) (fun d hd => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hd
    exact cpart_lt_slot h k x)
  rwa [List.length_map, h.hBm] at this

theorem postBlk_eval (hsp : SlotSpecOf prog Csp) (h : BlkHyp s wI wT q m W Epre B G)
    (hb : BaseHyp S0 s q wI W) (hdd : ∀ k, dd k = natSyms (pack s (B.map (cpart wI k))))
    (v : AReg) :
    ∃ w t, Eval [] (postBlk prog) ⟨v, bst S0 (fFin s wI wT q m Epre B G Q0 es dd 0)⟩
      ⟨w, bst S0 (fOut s wI q m Epre B G Q0 es)⟩ t ∧ t ≤ blkCostA s q wI m W Csp ∧
      w.q = es.head? := by
  have hG1 : 1 ≤ G.length := by rw [h.hGW]; exact h.hW1
  have hB1 : 1 ≤ B.length := by rw [h.hBm]; exact h.hm1
  -- final slots
  obtain ⟨w1, t1, e1, ht1⟩ := finLoop_eval (Q0 := Q0) (es := es) (dd := dd) hsp h hb v
  -- count the tail slots
  obtain ⟨w2, e2⟩ := pushN_eval (R := sp (.ru .Wm1)) (X := sp (.X 1)) (dst := sp .M) (by simp)
    (by simp) (by simp) (W - 1) .mark [] (bst S0 (fFin s wI wT q m Epre B G Q0 es dd m)) (by simp)
    (by show (S0 (sp (.X 1))).head? ≠ _; rw [hb.hX1]; simp)
    (by show S0 (sp (.ru .Wm1)) = _; rw [hb.hWm1, List.append_nil]) w1
  have hM0 : bst S0 (fFin s wI wT q m Epre B G Q0 es dd m) (sp .M) = [] := by
    show List.replicate (m - m) Sym.mark = []
    rw [Nat.sub_self, List.replicate_zero]
  rw [hM0, List.append_nil, bst_upd_M] at e2
  have e2' : Eval [] (pushN (sp (.ru .Wm1)) (sp (.X 1)) (sp .M) .mark)
      ⟨w1, bst S0 (fFin s wI wT q m Epre B G Q0 es dd m)⟩
      ⟨w2, bst S0 (fTail s wI wT q m W Epre B G Q0 es dd 0)⟩ (9 * (W - 1) + 4) := by
    refine e2.of_eq ?_ rfl
    congr 2
  -- tail slots
  obtain ⟨w3, t3, e3, ht3⟩ := tailLoop_eval (Q0 := Q0) (es := es) (dd := dd) hsp h hb w2
  -- the streams are exhausted
  have hend : ∀ (pairs : Fin 8 → Fin 4 × Fin 4) (f : CInt → ℤ) (j : Fin 9),
      slotL s wI wT (m + (W - 1)) B G (pend Epre G) pairs f j = [] := by
    intro pairs f j
    refine slotL_end s wI wT B G _ pairs f _ hB1 hG1 h.hdig ?_ ?_ j
    · rw [h.hBm, h.hGW]; have := h.hW1; omega
    · rw [length_pend, h.hGW]; omega
  set X := (List.range (W - 1)).map fun i => vB Epre B G (m + i) with hX
  have hXp : X = pend (Epre ++ B) G := by
    rw [hX, ← pend_extend, h.hGW, h.hBm]
  -- new tail, real
  have e4 := mvBits_eval (A := sp .NTre) (B := sp .Tre) (by simp) (tailBits s Prod.fst X).reverse
    [] w3 (bst S0 (fTail s wI wT q m W Epre B G Q0 es dd (W - 1))) TermOK.nil
    (by rw [List.append_nil]; rfl)
  have htre0 : bst S0 (fTail s wI wT q m W Epre B G Q0 es dd (W - 1)) (sp .Tre) = [] := by
    show (rL s wI wT (m + (W - 1)) Epre B G (Fin.last 8)).map Sym.bit = []
    rw [rL, hend]; rfl
  rw [htre0, List.append_nil, List.reverse_reverse, bst_upd_ntre, bst_upd_tre] at e4
  -- new tail, imaginary
  set f4 : BF := { { fTail s wI wT q m W Epre B G Q0 es dd (W - 1) with ntre := [] } with
    tre := (tailBits s Prod.fst X).map Sym.bit } with hf4
  have e5 := mvBits_eval (A := sp .NTim) (B := sp .Tim) (by simp) (tailBits s Prod.snd X).reverse
    [] { w3 with q := none } (bst S0 f4) TermOK.nil (by rw [List.append_nil]; rfl)
  have htim0 : bst S0 f4 (sp .Tim) = [] := by
    show (iL s wI wT (m + (W - 1)) Epre B G (Fin.last 8)).map Sym.bit = []
    rw [iL, hend]; rfl
  rw [htim0, List.append_nil, List.reverse_reverse, bst_upd_ntim, bst_upd_tim] at e5
  set f5 : BF := { { f4 with ntim := [] } with tim := (tailBits s Prod.snd X).map Sym.bit }
    with hf5
  -- drain the packed data
  have hdk : ∀ (f : BF) (k : Fin 4), f.d k = dd k →
      bst S0 f (sp (.D k)) = (encodeNat (pack s (B.map (cpart wI k)))).map Sym.bit ++ [] := by
    intro f k hk
    rw [List.append_nil]; show f.d k = _; rw [hk, hdd]; rfl
  have e6 := drainBits_eval (B := sp (.D 0)) _ [] { w3 with q := none } (bst S0 f5) TermOK.nil
    (hdk f5 0 rfl)
  rw [bst_upd_d] at e6
  set f6 : BF := { f5 with d := Function.update f5.d 0 [] } with hf6
  have e7 := drainBits_eval (B := sp (.D 1)) _ [] { w3 with q := none } (bst S0 f6) TermOK.nil
    (hdk f6 1 rfl)
  rw [bst_upd_d] at e7
  set f7 : BF := { f6 with d := Function.update f6.d 1 [] } with hf7
  have e8 := drainBits_eval (B := sp (.D 2)) _ [] { w3 with q := none } (bst S0 f7) TermOK.nil
    (hdk f7 2 rfl)
  rw [bst_upd_d] at e8
  set f8 : BF := { f7 with d := Function.update f7.d 2 [] } with hf8
  have e9 := drainBits_eval (B := sp (.D 3)) _ [] { w3 with q := none } (bst S0 f8) TermOK.nil
    (hdk f8 3 rfl)
  rw [bst_upd_d] at e9
  set f9 : BF := { f8 with d := Function.update f8.d 3 [] } with hf9
  have e10 := eval_peekQ (sp .Es) { w3 with q := none } (bst S0 f9)
  have hf9o : f9 = fOut s wI q m Epre B G Q0 es := by
    refine BF.ext' (funext fun i => ?_) (funext fun i => ?_) ?_ ?_ ?_ rfl rfl rfl rfl rfl
      (funext fun k => ?_) rfl
    · show (rL s wI wT (m + (W - 1)) Epre B G i.castSucc).map Sym.bit = []
      rw [rL, hend]; rfl
    · show (iL s wI wT (m + (W - 1)) Epre B G i.castSucc).map Sym.bit = []
      rw [iL, hend]; rfl
    · show (tailBits s Prod.fst X).map Sym.bit = _; rw [hXp]; rfl
    · show (tailBits s Prod.snd X).map Sym.bit = _; rw [hXp]; rfl
    · show W - 1 - (W - 1) = 0; omega
    · fin_cases k <;> simp [hf9, hf8, hf7, hf6, fOut, Function.update_apply]
  refine ⟨_, t1 + ((9 * (W - 1) + 4) + (t3 + ((4 * (tailBits s Prod.fst X).reverse.length + 2) +
    ((4 * (tailBits s Prod.snd X).reverse.length + 2) +
    ((3 * (encodeNat (pack s (B.map (cpart wI 0)))).length + 2) +
    ((3 * (encodeNat (pack s (B.map (cpart wI 1)))).length + 2) +
    ((3 * (encodeNat (pack s (B.map (cpart wI 2)))).length + 2) +
    ((3 * (encodeNat (pack s (B.map (cpart wI 3)))).length + 2) + 1)))))))),
    (Eval.seq e1 (Eval.seq e2' (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6 (Eval.seq e7
      (Eval.seq e8 (Eval.seq e9 e10))))))))).of_eq (by rw [hf9o]) rfl, ?_, ?_⟩
  · have l1 : (tailBits s Prod.fst X).reverse.length = s * (W - 1) := by
      rw [List.length_reverse, length_tailBits, hX, List.length_map, List.length_range]
    have l2 : (tailBits s Prod.snd X).reverse.length = s * (W - 1) := by
      rw [List.length_reverse, length_tailBits, hX, List.length_map, List.length_range]
    have d0 := length_encodeNat_pack h 0
    have d1 := length_encodeNat_pack h 1
    have d2 := length_encodeNat_pack h 2
    have d3 := length_encodeNat_pack h 3
    unfold blkCostA
    rw [l1, l2]
    omega
  · rfl

end Post

end SubNLogN.Machine.Bridge.SpreadAux
