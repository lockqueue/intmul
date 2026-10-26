/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadBlockC

/-!
# K5 spreading: AR-level block step, part D (`Bridge/SpreadBlockD.lean`)

One final slot (`finStep`), one tail slot (`tailStep`), the two slot loops, and the AR part of the
block step `postBlk_eval`. Everything is proved; the slot pass enters through `SlotSpecOf`.
-/

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.Arith Computability

theorem length_tailBits (s : ℕ) (f : CInt → ℤ) : ∀ T : List CInt,
    (tailBits s f T).length = s * T.length
  | [] => rfl
  | x :: T => by
    have ih := length_tailBits s f T
    unfold tailBits at ih ⊢
    rw [List.map_cons, List.flatten_cons, List.length_append, K1.length_twosBits, ih,
      List.length_cons]
    ring

theorem length_encodeNat_le : ∀ (k x : ℕ), x < 2 ^ k → (encodeNat x).length ≤ k
  | 0, x, h => by
    have : x = 0 := by simpa using h
    subst this; simp [encodeNat_zero]
  | k + 1, x, h => by
    have ht := (encodeNat_head_tail x).2
    have h2 : x / 2 < 2 ^ k := by rw [pow_succ] at h; omega
    have ih := length_encodeNat_le k (x / 2) h2
    have hl : (encodeNat x).length ≤ (encodeNat x).tail.length + 1 := by
      rw [List.length_tail]; omega
    rw [ht] at hl
    omega

section Iter

variable {Esu : Type} [DecidableEq Esu]
variable {prog : ∀ (K : Type) [DecidableEq K], (SlotRole → K) → AProg K} {Csp : ℕ}
variable {s wI wT q m W : ℕ} {Epre B G : List CInt} {Q0 es : List Sym} {dd : Fin 4 → List Sym}
variable {S0 : SK Esu → List Sym}

theorem finStep (hsp : SlotSpecOf prog Csp) (h : BlkHyp s wI wT q m W Epre B G)
    (hb : BaseHyp S0 s q wI W) (n : ℕ) (hn : n < m) (u : AReg) :
    ∃ w t, Eval [] (finBody prog) ⟨u, bst S0 (fFin s wI wT q m Epre B G Q0 es dd n)⟩
      ⟨w, bst S0 (fFin s wI wT q m Epre B G Q0 es dd (n + 1))⟩ t ∧
      t ≤ 2 * (Csp * (s + 1)) + finCost s q wI + 2 ∧ isMarkO w.r = decide (n + 1 < m) := by
  set qq := (carrSyms wI ((List.range n).map fun i =>
    [roundHalfUpShiftC q (vB Epre B G i)])).reverse ++ Q0 with hqq
  set outR := (twosBits s (vB Epre B G n).1).reverse.map Sym.bit with houtR
  set outI := (twosBits s (vB Epre B G n).2).reverse.map Sym.bit with houtI
  have hM : bst S0 (fFin s wI wT q m Epre B G Q0 es dd n) (sp .M) =
      .mark :: List.replicate (m - n - 1) .mark := by
    show List.replicate (m - n) Sym.mark = _
    obtain ⟨k, hk⟩ : ∃ k, m - n = k + 1 := ⟨m - n - 1, by omega⟩
    rw [hk, List.replicate_succ, Nat.add_sub_cancel]
  have e1 := eval_drop1 (sp .M) u _ _ _ hM
  rw [bst_upd_M] at e1
  have e1' : Eval [] (drop1 (sp .M)) ⟨u, bst S0 (fFin s wI wT q m Epre B G Q0 es dd n)⟩
      ⟨u, bst S0 (fMid s wI wT q m Epre B G Q0 es dd n 0 0 [] [] (m - n - 1) [] [] qq)⟩ 1 :=
    e1.of_eq rfl rfl
  obtain ⟨v2, c2, e2, hc2⟩ := slot_re_step hsp s S0
    (fMid s wI wT q m Epre B G Q0 es dd n 0 0 [] [] (m - n - 1) [] [] qq)
    (rL s wI wT (n + 0) Epre B G) u .Vre (Or.inl rfl) hb.hRs hb.hX5 (fun i => rfl) rfl
  rw [bst_upd_vre] at e2
  have e2' : Eval [] (prog (SK Esu) (ιSP .Zr .Tre .Vre))
      ⟨u, bst S0 (fMid s wI wT q m Epre B G Q0 es dd n 0 0 [] [] (m - n - 1) [] [] qq)⟩
      ⟨v2, bst S0 (fMid s wI wT q m Epre B G Q0 es dd n 1 0 outR [] (m - n - 1) [] [] qq)⟩ c2 := by
    refine e2.of_eq ?_ rfl
    congr 2
    refine BF.ext' (funext fun i => ?_) rfl ?_ rfl rfl rfl ?_ rfl rfl rfl rfl rfl
    · show ((rL s wI wT (n + 0) Epre B G i.castSucc).drop s).map Sym.bit =
        (rL s wI wT (n + 1) Epre B G i.castSucc).map Sym.bit
      rw [rL, rL, slotL_drop]
    · show ((rL s wI wT (n + 0) Epre B G (Fin.last 8)).drop s).map Sym.bit =
        (rL s wI wT (n + 1) Epre B G (Fin.last 8)).map Sym.bit
      rw [rL, rL, slotL_drop]
    · show (serialRun s 0 (slotSrcs (rL s wI wT (n + 0) Epre B G))).reverse.map Sym.bit ++ [] =
        outR
      rw [List.append_nil, Nat.add_zero, slot_val_re h n (by have := h.hW1; omega)]
  obtain ⟨v3, c3, e3, hc3⟩ := slot_im_step hsp s S0
    (fMid s wI wT q m Epre B G Q0 es dd n 1 0 outR [] (m - n - 1) [] [] qq)
    (iL s wI wT (n + 0) Epre B G) v2 .Vim (Or.inl rfl) hb.hRs hb.hX5 (fun i => rfl) rfl
  rw [bst_upd_vim] at e3
  have e3' : Eval [] (prog (SK Esu) (ιSP .Zi .Tim .Vim))
      ⟨v2, bst S0 (fMid s wI wT q m Epre B G Q0 es dd n 1 0 outR [] (m - n - 1) [] [] qq)⟩
      ⟨v3, bst S0 (fMid s wI wT q m Epre B G Q0 es dd n 1 1 outR outI (m - n - 1) [] [] qq)⟩
      c3 := by
    refine e3.of_eq ?_ rfl
    congr 2
    refine BF.ext' rfl (funext fun i => ?_) rfl ?_ rfl rfl rfl ?_ rfl rfl rfl rfl
    · show ((iL s wI wT (n + 0) Epre B G i.castSucc).drop s).map Sym.bit =
        (iL s wI wT (n + 1) Epre B G i.castSucc).map Sym.bit
      rw [iL, iL, slotL_drop]
    · show ((iL s wI wT (n + 0) Epre B G (Fin.last 8)).drop s).map Sym.bit =
        (iL s wI wT (n + 1) Epre B G (Fin.last 8)).map Sym.bit
      rw [iL, iL, slotL_drop]
    · show (serialRun s 0 (slotSrcs (iL s wI wT (n + 0) Epre B G))).reverse.map Sym.bit ++ [] =
        outI
      rw [List.append_nil, Nat.add_zero, slot_val_im h n (by have := h.hW1; omega)]
  obtain ⟨v4, e4⟩ := finRec_eval s q wI h.hq h.hs1 (vB Epre B G n) (fits_vB h n) S0
    (fMid s wI wT q m Epre B G Q0 es dd n 1 1 outR outI (m - n - 1) [] [] qq) v3 rfl rfl
    hb.hBf hb.hFA hb.hFB hb.hX6 hb.hsq hb.hh hb.hwI
  have e5 := eval_peekR (sp .M) v4 (bst S0 (fFin s wI wT q m Epre B G Q0 es dd (n + 1)))
  have hfin : (fMid s wI wT q m Epre B G Q0 es dd n 1 1 outR outI (m - n - 1) [] [] qq).finOut
      ((recSyms (crecBits wI [roundHalfUpShiftC q (vB Epre B G n)])).reverse
        ++ (fMid s wI wT q m Epre B G Q0 es dd n 1 1 outR outI (m - n - 1) [] [] qq).q) =
      fFin s wI wT q m Epre B G Q0 es dd (n + 1) := by
    refine BF.ext' rfl rfl rfl rfl (by show m - n - 1 = m - (n + 1); omega) ?_ rfl rfl rfl rfl
      rfl rfl
    show _ = (carrSyms wI ((List.range (n + 1)).map fun i =>
      [roundHalfUpShiftC q (vB Epre B G i)])).reverse ++ Q0
    rw [carrSyms_range_succ, List.append_assoc]
    rfl
  rw [hfin] at e4
  refine ⟨_, 1 + (c2 + (c3 + (finCost s q wI + 1))), Eval.seq e1' (Eval.seq e2' (Eval.seq e3'
    (Eval.seq e4 e5))), by omega, ?_⟩
  show isMarkO (List.replicate (m - (n + 1)) Sym.mark).head? = _
  rcases Nat.lt_or_ge (n + 1) m with h1 | h1
  · rw [show m - (n + 1) = (m - (n + 1) - 1) + 1 by omega, List.replicate_succ]
    simp [isMarkO, h1]
  · rw [show m - (n + 1) = 0 by omega]
    simp [isMarkO, show ¬ (n + 1 < m) by omega]

theorem tailStep (hsp : SlotSpecOf prog Csp) (h : BlkHyp s wI wT q m W Epre B G)
    (hb : BaseHyp S0 s q wI W) (r : ℕ) (hr : r < W - 1) (u : AReg) :
    ∃ w t, Eval [] (tailBody prog) ⟨u, bst S0 (fTail s wI wT q m W Epre B G Q0 es dd r)⟩
      ⟨w, bst S0 (fTail s wI wT q m W Epre B G Q0 es dd (r + 1))⟩ t ∧
      t ≤ 2 * (Csp * (s + 1)) + 2 ∧ isMarkO w.r = decide (r + 1 < W - 1) := by
  set qq := (carrSyms wI ((List.range m).map fun i =>
    [roundHalfUpShiftC q (vB Epre B G i)])).reverse ++ Q0 with hqq
  set g : ℕ → CInt := fun i => vB Epre B G (m + i) with hg
  set nr := (tailBits s Prod.fst ((List.range r).map g)).reverse.map Sym.bit with hnr
  set ni := (tailBits s Prod.snd ((List.range r).map g)).reverse.map Sym.bit with hni
  set nr' := (tailBits s Prod.fst ((List.range (r + 1)).map g)).reverse.map Sym.bit with hnr'
  set ni' := (tailBits s Prod.snd ((List.range (r + 1)).map g)).reverse.map Sym.bit with hni'
  have hM : bst S0 (fTail s wI wT q m W Epre B G Q0 es dd r) (sp .M) =
      .mark :: List.replicate (W - 1 - r - 1) .mark := by
    show List.replicate (W - 1 - r) Sym.mark = _
    obtain ⟨k, hk⟩ : ∃ k, W - 1 - r = k + 1 := ⟨W - 1 - r - 1, by omega⟩
    rw [hk, List.replicate_succ, Nat.add_sub_cancel]
  have e1 := eval_drop1 (sp .M) u _ _ _ hM
  rw [bst_upd_M] at e1
  have e1' : Eval [] (drop1 (sp .M)) ⟨u, bst S0 (fTail s wI wT q m W Epre B G Q0 es dd r)⟩
      ⟨u, bst S0 (fMid s wI wT q m Epre B G Q0 es dd (m + r) 0 0 [] [] (W - 1 - r - 1) nr ni
        qq)⟩ 1 :=
    e1.of_eq rfl rfl
  obtain ⟨v2, c2, e2, hc2⟩ := slot_re_step hsp s S0
    (fMid s wI wT q m Epre B G Q0 es dd (m + r) 0 0 [] [] (W - 1 - r - 1) nr ni qq)
    (rL s wI wT (m + r + 0) Epre B G) u .NTre (Or.inr rfl) hb.hRs hb.hX5 (fun i => rfl) rfl
  rw [bst_upd_ntre] at e2
  have e2' : Eval [] (prog (SK Esu) (ιSP .Zr .Tre .NTre))
      ⟨u, bst S0 (fMid s wI wT q m Epre B G Q0 es dd (m + r) 0 0 [] [] (W - 1 - r - 1) nr ni qq)⟩
      ⟨v2, bst S0 (fMid s wI wT q m Epre B G Q0 es dd (m + r) 1 0 [] [] (W - 1 - r - 1) nr' ni
        qq)⟩ c2 := by
    refine e2.of_eq ?_ rfl
    congr 2
    refine BF.ext' (funext fun i => ?_) rfl ?_ rfl rfl rfl rfl rfl ?_ rfl rfl rfl
    · show ((rL s wI wT (m + r + 0) Epre B G i.castSucc).drop s).map Sym.bit =
        (rL s wI wT (m + r + 1) Epre B G i.castSucc).map Sym.bit
      rw [rL, rL, slotL_drop]
    · show ((rL s wI wT (m + r + 0) Epre B G (Fin.last 8)).drop s).map Sym.bit =
        (rL s wI wT (m + r + 1) Epre B G (Fin.last 8)).map Sym.bit
      rw [rL, rL, slotL_drop]
    · show (serialRun s 0 (slotSrcs (rL s wI wT (m + r + 0) Epre B G))).reverse.map Sym.bit ++
        nr = nr'
      rw [Nat.add_zero, slot_val_re h (m + r) (by omega), hnr, hnr', tailBits_range_succ,
        List.reverse_append, List.map_append]
  obtain ⟨v3, c3, e3, hc3⟩ := slot_im_step hsp s S0
    (fMid s wI wT q m Epre B G Q0 es dd (m + r) 1 0 [] [] (W - 1 - r - 1) nr' ni qq)
    (iL s wI wT (m + r + 0) Epre B G) v2 .NTim (Or.inr rfl) hb.hRs hb.hX5 (fun i => rfl) rfl
  rw [bst_upd_ntim] at e3
  have e3' : Eval [] (prog (SK Esu) (ιSP .Zi .Tim .NTim))
      ⟨v2, bst S0 (fMid s wI wT q m Epre B G Q0 es dd (m + r) 1 0 [] [] (W - 1 - r - 1) nr' ni qq)⟩
      ⟨v3, bst S0 (fTail s wI wT q m W Epre B G Q0 es dd (r + 1))⟩ c3 := by
    refine e3.of_eq ?_ rfl
    congr 2
    refine BF.ext' rfl (funext fun i => ?_) rfl ?_ (by show W - 1 - r - 1 = W - 1 - (r + 1); omega)
      rfl rfl rfl rfl ?_ rfl rfl
    · show ((iL s wI wT (m + r + 0) Epre B G i.castSucc).drop s).map Sym.bit =
        (iL s wI wT (m + (r + 1)) Epre B G i.castSucc).map Sym.bit
      rw [iL, iL, slotL_drop]
      rfl
    · show ((iL s wI wT (m + r + 0) Epre B G (Fin.last 8)).drop s).map Sym.bit =
        (iL s wI wT (m + (r + 1)) Epre B G (Fin.last 8)).map Sym.bit
      rw [iL, iL, slotL_drop]
      rfl
    · show (serialRun s 0 (slotSrcs (iL s wI wT (m + r + 0) Epre B G))).reverse.map Sym.bit ++
        ni = ni'
      rw [Nat.add_zero, slot_val_im h (m + r) (by omega), hni, hni', tailBits_range_succ,
        List.reverse_append, List.map_append]
  have e4 := eval_peekR (sp .M) v3 (bst S0 (fTail s wI wT q m W Epre B G Q0 es dd (r + 1)))
  refine ⟨_, 1 + (c2 + (c3 + 1)), Eval.seq e1' (Eval.seq e2' (Eval.seq e3' e4)), by omega, ?_⟩
  show isMarkO (List.replicate (W - 1 - (r + 1)) Sym.mark).head? = _
  rcases Nat.lt_or_ge (r + 1) (W - 1) with h1 | h1
  · rw [show W - 1 - (r + 1) = (W - 1 - (r + 1) - 1) + 1 by omega, List.replicate_succ]
    simp [isMarkO, h1]
  · rw [show W - 1 - (r + 1) = 0 by omega]
    simp [isMarkO, show ¬ (r + 1 < W - 1) by omega]

theorem finLoop_eval (hsp : SlotSpecOf prog Csp) (h : BlkHyp s wI wT q m W Epre B G)
    (hb : BaseHyp S0 s q wI W) (v : AReg) :
    ∃ w t, Eval [] (mLoop (finBody prog)) ⟨v, bst S0 (fFin s wI wT q m Epre B G Q0 es dd 0)⟩
      ⟨w, bst S0 (fFin s wI wT q m Epre B G Q0 es dd m)⟩ t ∧
      t ≤ 1 + (m * (2 * (Csp * (s + 1)) + finCost s q wI + 2 + 1) + 1) := by
  have e0 := eval_peekR (sp .M) v (bst S0 (fFin s wI wT q m Epre B G Q0 es dd 0))
  obtain ⟨w, t, e, ht⟩ := eval_loop_bounded (c := fun v => isMarkO v.r) (body := finBody prog)
    (2 * (Csp * (s + 1)) + finCost s q wI + 2) m
    (fun n => bst S0 (fFin s wI wT q m Epre B G Q0 es dd n))
    { v with r := (bst S0 (fFin s wI wT q m Epre B G Q0 es dd 0) (sp .M)).head? }
    (by
      show isMarkO (List.replicate (m - 0) Sym.mark).head? = decide (0 < m)
      rw [Nat.sub_zero, show m = (m - 1) + 1 by have := h.hm1; omega, List.replicate_succ]
      simp [isMarkO])
    (fun n hn u => finStep hsp h hb n hn u)
  exact ⟨w, 1 + t, Eval.seq e0 e, by omega⟩

theorem tailLoop_eval (hsp : SlotSpecOf prog Csp) (h : BlkHyp s wI wT q m W Epre B G)
    (hb : BaseHyp S0 s q wI W) (v : AReg) :
    ∃ w t, Eval [] (mLoop (tailBody prog))
      ⟨v, bst S0 (fTail s wI wT q m W Epre B G Q0 es dd 0)⟩
      ⟨w, bst S0 (fTail s wI wT q m W Epre B G Q0 es dd (W - 1))⟩ t ∧
      t ≤ 1 + ((W - 1) * (2 * (Csp * (s + 1)) + 2 + 1) + 1) := by
  have e0 := eval_peekR (sp .M) v (bst S0 (fTail s wI wT q m W Epre B G Q0 es dd 0))
  obtain ⟨w, t, e, ht⟩ := eval_loop_bounded (c := fun v => isMarkO v.r) (body := tailBody prog)
    (2 * (Csp * (s + 1)) + 2) (W - 1)
    (fun r => bst S0 (fTail s wI wT q m W Epre B G Q0 es dd r))
    { v with r := (bst S0 (fTail s wI wT q m W Epre B G Q0 es dd 0) (sp .M)).head? }
    (by
      show isMarkO (List.replicate (W - 1 - 0) Sym.mark).head? = decide (0 < W - 1)
      rw [Nat.sub_zero]
      rcases Nat.eq_zero_or_pos (W - 1) with h0 | h0
      · rw [h0]; rfl
      · rw [show W - 1 = (W - 1 - 1) + 1 by omega, List.replicate_succ]
        simp [isMarkO])
    (fun r hr u => tailStep hsp h hb r hr u)
  exact ⟨w, 1 + t, Eval.seq e0 e, by omega⟩

end Iter

end SubNLogN.Machine.Bridge.SpreadAux
