/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveParamsBits

/-!
# SOL-PARAM-ROWS (3): stack layout, `Runs` wrappers and record staging

* The kernel layout `SK = KLoc (Fin 7) (Fin 25)`: the named stacks of `SolParamRowsStmt`
  (`sTab, sPar, sAx, sHalf, sMU, sNA, sGM`) and 25 private scratch stacks.
* `Runs` wrappers (register `BReg`) for the lifted `TMFw.Lib` moves, the ruler pass, pushes and the
  duplication of a top symbol.
* Staging of one output record from the current solver record on `kW`:
  `stageId` (`μ̂`, `γ̂`: sign extension to `wT + 1` bits) and `stageNeg` (`â`: sign extension, then
  negation by the ripple `fNeg` over a ruler of `wT + 1` bits); the imaginary part is the
  `wT + 1` zeros of the second ruler, the consumed imaginary input field goes to the junk stack.

All proved; helpers in `SubNLogN.Machine.Bridge.SolveParamsAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveParamsAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine
open WP.W9comp (runs_seq runs_mono runs_congr)

/-! ## Layout -/

/-- The kernel's stacks: the 7 named stacks of the contract and 25 scratch stacks. -/
abbrev SK : Type := KLoc (Fin 7) (Fin 25)

abbrev sTab : SK := .inl 0
abbrev sPar : SK := .inl 1
abbrev sAx : SK := .inl 2
abbrev sHalf : SK := .inl 3
abbrev sMU : SK := .inl 4
abbrev sNA : SK := .inl 5
abbrev sGM : SK := .inl 6

abbrev kH : SK := .inr 0
abbrev kCW : SK := .inr 1
abbrev kRU : SK := .inr 2
abbrev kRX : SK := .inr 3
abbrev kRV : SK := .inr 4
abbrev kTP : SK := .inr 5
abbrev kTQ : SK := .inr 6
abbrev kCX : SK := .inr 7
abbrev kCT : SK := .inr 8
abbrev kCU : SK := .inr 9
abbrev kCC : SK := .inr 10
abbrev kCD : SK := .inr 11
abbrev kZB : SK := .inr 12
abbrev kZR : SK := .inr 13
abbrev kW : SK := .inr 14
abbrev kYT : SK := .inr 15
abbrev kYT2 : SK := .inr 16
abbrev kJ : SK := .inr 17
abbrev kY0 : SK := .inr 18
abbrev kY1 : SK := .inr 19
abbrev kY2 : SK := .inr 20
abbrev kA0 : SK := .inr 21
abbrev kA1 : SK := .inr 22
abbrev kA2 : SK := .inr 23
abbrev kCY : SK := .inr 24

/-- A ruler of `n` bits. -/
def ruler (n : ℕ) : List Sym := List.replicate n (Sym.bit false)

/-! ## Wrappers -/

section Wrappers

variable {K : Type} [DecidableEq K]

/-- Lift a `TMFw.Lib` program to the register `BReg`. -/
def L (p : SProg K) : BProg K := p.liftRegs (Lens.fst (Option Sym) Bool)

theorem runs_L {p : SProg K} {S S' : K → List Sym} {t : ℕ}
    (h : ∀ v, ∃ v', Eval [] p ⟨v, S⟩ ⟨v', S'⟩ t) : Runs (L p) S S' (fun _ => True) t :=
  SolveAux.runs_liftRegs_of_eval _ h

theorem runs_L_moveBlock {src dst : K} (hne : src ≠ dst) (es : List Bool) (rest : List Sym)
    (S : K → List Sym) (hrest : TermOK rest) (hS : S src = es.map Sym.bit ++ rest) :
    Runs (L (moveBlock src dst)) S
      (Function.update (Function.update S src rest) dst (es.reverse.map Sym.bit ++ S dst))
      (fun _ => True) (3 * es.length + 4) :=
  runs_L fun v => ⟨_, moveBlock_eval hne [] v es rest S hrest hS⟩

theorem runs_L_copyBlock {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (blk : List Bool) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = blk.map Sym.bit ++ rest) :
    Runs (L (copyBlock src dst tmp)) S (Function.update S dst (blk.map Sym.bit ++ S dst))
      (fun _ => True) (7 * blk.length + 7) :=
  runs_L fun v => ⟨_, copyBlock_eval hsd hst hdt [] v blk rest S hrest hS⟩

theorem runs_pushCB (k : K) (x : Sym) (S : K → List Sym) :
    Runs (pushCB k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, Eval.push [] k _ v S, trivial, le_refl _⟩

/-- Duplicate the top symbol of `k`. -/
def dupB (k : K) : BProg K := .seq (peekB k) (pushRB k)

theorem runs_dupB (k : K) (x : Sym) (L' : List Sym) (S : K → List Sym) (hS : S k = x :: L') :
    Runs (dupB k) S (Function.update S k (x :: S k)) (fun _ => True) 2 := by
  refine Runs.of_eval fun v => ⟨(some x, v.2), 2, ?_, trivial, le_refl _⟩
  have e1 : Eval [] (peekB k) ⟨v, S⟩ ⟨(some x, v.2), S⟩ 1 := by
    have := Eval.peek [] k (fun (v : BReg) o => (o, v.2)) v S
    rw [hS] at this
    exact this
  have e2 : Eval [] (pushRB k) ⟨(some x, v.2), S⟩ ⟨(some x, v.2), Function.update S k (x :: S k)⟩ 1 :=
    Eval.push [] k _ _ _
  exact Eval.seq e1 e2

theorem runs_rField {RU RV src dst : K} (h1 : RU ≠ RV) (h2 : RU ≠ src) (h3 : RU ≠ dst)
    (h4 : RV ≠ src) (h5 : RV ≠ dst) (h6 : src ≠ dst) (f : Bool → Bool → Bool × Bool) (c0 : Bool)
    (ruRest : List Sym) (hru : TermOK ruRest) (bs : List Bool) (srcRest : List Sym)
    (S : K → List Sym) (hRU : S RU = List.replicate bs.length (Sym.bit false) ++ ruRest)
    (hsrc : S src = bs.map Sym.bit ++ srcRest) (hRV : TermOK (S RV)) :
    Runs (rField RU RV src dst f c0) S
      (Function.update (Function.update S src srcRest) dst
        ((rip f c0 bs).reverse.map Sym.bit ++ S dst)) (fun _ => True) (10 * bs.length + 7) :=
  Runs.of_eval fun v => by
    obtain ⟨v', e⟩ := rField_eval h1 h2 h3 h4 h5 h6 f c0 ruRest hru bs srcRest S hRU hsrc hRV v
    exact ⟨v', _, e, trivial, le_refl _⟩

end Wrappers

theorem termOK_nil : TermOK ([] : List Sym) := fun _ h => by simp at h

/-! ## Staging one output record -/

theorem ruler_eq (n : ℕ) : ruler n = (List.replicate n false).map Sym.bit := by
  simp [ruler, List.map_replicate]

theorem map_bit_twosBits_zero (w : ℕ) : (twosBits w 0).map Sym.bit = ruler w := by
  rw [twosBits_zero, ruler_eq]

/-- Stage `[(g, 0)]` at width `wT + 1` on `Yk` from the two fields `twosBits wT g`,
`twosBits wT 0` on top of `kW` (sign extension). -/
def stageId (Yk : SK) : BProg SK :=
  .seq (pushCB Yk .sep) (.seq (L (copyBlock kRX Yk kTP)) (.seq (rField kRU kRV kW kYT fId false)
    (.seq (dupB kYT) (.seq (rField kRU kRV kW kJ fId false) (L (moveBlock kYT Yk))))))

theorem runs_stageId (Yk : SK) (hYk : Yk = kY0 ∨ Yk = kY1 ∨ Yk = kY2) (w : ℕ) (hw : 1 ≤ w)
    (g : ℤ) (hg : FitsTwos w g) (rest : List Sym) (S : SK → List Sym)
    (hRU : S kRU = ruler w) (hRX : S kRX = ruler (w + 1)) (hRV : S kRV = []) (hYT : S kYT = [])
    (hW : S kW = (twosBits w g).map Sym.bit ++ (twosBits w 0).map Sym.bit ++ rest) :
    Runs (stageId Yk) S
      (Function.update (Function.update (Function.update S kW rest) kJ (ruler w ++ S kJ)) Yk
        (recSyms (crecBits (w + 1) [(g, 0)]) ++ S Yk))
      (fun _ => True) (30 * w + 38) := by
  have hsplit := twosBits_eq_init_sign hw hg
  set s : Bool := decide (g < 0) with hs
  set bs := twosBits (w - 1) g with hbs
  have hext : twosBits (w + 1) g = twosBits w g ++ [s] := twosBits_succ_eq_append hg
  have hlen : (twosBits w g).length = w := K1.length_twosBits w g
  have hlen0 : (twosBits w 0).length = w := K1.length_twosBits w 0
  have n1 : Yk ≠ kRX := by rcases hYk with rfl | rfl | rfl <;> decide
  have n2 : Yk ≠ kTP := by rcases hYk with rfl | rfl | rfl <;> decide
  have n3 : Yk ≠ kRU := by rcases hYk with rfl | rfl | rfl <;> decide
  have n4 : Yk ≠ kRV := by rcases hYk with rfl | rfl | rfl <;> decide
  have n5 : Yk ≠ kW := by rcases hYk with rfl | rfl | rfl <;> decide
  have n6 : Yk ≠ kYT := by rcases hYk with rfl | rfl | rfl <;> decide
  have n7 : Yk ≠ kJ := by rcases hYk with rfl | rfl | rfl <;> decide
  refine runs_mono (runs_congr (runs_seq (runs_pushCB (K := SK) Yk Sym.sep S)
    (runs_seq (runs_L_copyBlock (src := kRX) (dst := Yk) (tmp := kTP) n1.symm (by decide) n2
        (List.replicate (w + 1) false) [] _ termOK_nil
        (by simp [Function.update_apply, n1.symm, hRX, ruler_eq]))
    (runs_seq (runs_rField (RU := kRU) (RV := kRV) (src := kW) (dst := kYT) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) fId false [] termOK_nil
        (twosBits w g) ((twosBits w 0).map Sym.bit ++ rest) _
        (by simp [Function.update_apply, n3.symm, hRU, ruler, hlen])
        (by simp [Function.update_apply, n5.symm, hW])
        (by simp [Function.update_apply, n4.symm, hRV]; exact termOK_nil))
    (runs_seq (runs_dupB (K := SK) kYT (Sym.bit s) (bs.reverse.map Sym.bit) _
        (by simp [Function.update_apply, n6.symm, rip_fId, hYT, hsplit]))
    (runs_seq (runs_rField (RU := kRU) (RV := kRV) (src := kW) (dst := kJ) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) fId false [] termOK_nil
        (twosBits w 0) rest _
        (by simp [Function.update_apply, n3.symm, hRU, ruler, hlen0])
        (by simp [Function.update_apply, n5.symm])
        (by simp [Function.update_apply, n4.symm, hRV]; exact termOK_nil))
      (runs_L_moveBlock (src := kYT) (dst := Yk) n6.symm (s :: (twosBits w g).reverse)
        [] _ termOK_nil
        (by simp [Function.update_apply, n6.symm, n7.symm, rip_fId, hYT, hsplit]))))))) ?_)
    (fun _ _ => trivial) (by simp [hlen, hlen0]; omega)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;>
    simp_all [rip_fId, hext, crecBits_one, recSyms, map_bit_twosBits_zero, ruler_eq,
      List.map_append, List.reverse_cons]

/-- Stage `[(-x, 0)]` at width `wT + 1` on `Yk` from the two fields `twosBits wT x`, `twosBits wT 0`
on top of `kW` (sign extension, then negation over the ruler `kRX` of `wT + 1` bits). -/
def stageNeg (Yk : SK) : BProg SK :=
  .seq (pushCB Yk .sep) (.seq (L (copyBlock kRX Yk kTP)) (.seq (rField kRU kRV kW kYT fId false)
    (.seq (dupB kYT) (.seq (L (moveBlock kYT kYT2)) (.seq (rField kRX kRV kYT2 kYT fNeg false)
    (.seq (rField kRU kRV kW kJ fId false) (L (moveBlock kYT Yk))))))))

theorem runs_stageNeg (Yk : SK) (hYk : Yk = kY0 ∨ Yk = kY1 ∨ Yk = kY2) (w : ℕ) (hw : 1 ≤ w)
    (x : ℤ) (hx : FitsTwos w x) (rest : List Sym) (S : SK → List Sym)
    (hRU : S kRU = ruler w) (hRX : S kRX = ruler (w + 1)) (hRV : S kRV = []) (hYT : S kYT = [])
    (hYT2 : S kYT2 = [])
    (hW : S kW = (twosBits w x).map Sym.bit ++ (twosBits w 0).map Sym.bit ++ rest) :
    Runs (stageNeg Yk) S
      (Function.update (Function.update (Function.update S kW rest) kJ (ruler w ++ S kJ)) Yk
        (recSyms (crecBits (w + 1) [(-x, 0)]) ++ S Yk))
      (fun _ => True) (45 * w + 70) := by
  have hsplit := twosBits_eq_init_sign hw hx
  set s : Bool := decide (x < 0) with hs
  set bs := twosBits (w - 1) x with hbs
  have hext : twosBits (w + 1) x = twosBits w x ++ [s] := twosBits_succ_eq_append hx
  have hlen : (twosBits w x).length = w := K1.length_twosBits w x
  have hlen0 : (twosBits w 0).length = w := K1.length_twosBits w 0
  have hlen1 : (twosBits (w + 1) x).length = w + 1 := K1.length_twosBits (w + 1) x
  have hneg : rip fNeg false (twosBits (w + 1) x) = twosBits (w + 1) (-x) := by
    rw [rip_fNeg_eq, twosBits_neg]
  have n1 : Yk ≠ kRX := by rcases hYk with rfl | rfl | rfl <;> decide
  have n2 : Yk ≠ kTP := by rcases hYk with rfl | rfl | rfl <;> decide
  have n3 : Yk ≠ kRU := by rcases hYk with rfl | rfl | rfl <;> decide
  have n4 : Yk ≠ kRV := by rcases hYk with rfl | rfl | rfl <;> decide
  have n5 : Yk ≠ kW := by rcases hYk with rfl | rfl | rfl <;> decide
  have n6 : Yk ≠ kYT := by rcases hYk with rfl | rfl | rfl <;> decide
  have n7 : Yk ≠ kJ := by rcases hYk with rfl | rfl | rfl <;> decide
  have n8 : Yk ≠ kYT2 := by rcases hYk with rfl | rfl | rfl <;> decide
  refine runs_mono (runs_congr (runs_seq (runs_pushCB (K := SK) Yk Sym.sep S)
    (runs_seq (runs_L_copyBlock (src := kRX) (dst := Yk) (tmp := kTP) n1.symm (by decide) n2
        (List.replicate (w + 1) false) [] _ termOK_nil
        (by simp [Function.update_apply, n1.symm, hRX, ruler_eq]))
    (runs_seq (runs_rField (RU := kRU) (RV := kRV) (src := kW) (dst := kYT) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) fId false [] termOK_nil
        (twosBits w x) ((twosBits w 0).map Sym.bit ++ rest) _
        (by simp [Function.update_apply, n3.symm, hRU, ruler, hlen])
        (by simp [Function.update_apply, n5.symm, hW])
        (by simp [Function.update_apply, n4.symm, hRV]; exact termOK_nil))
    (runs_seq (runs_dupB (K := SK) kYT (Sym.bit s) (bs.reverse.map Sym.bit) _
        (by simp [Function.update_apply, n6.symm, rip_fId, hYT, hsplit]))
    (runs_seq (runs_L_moveBlock (src := kYT) (dst := kYT2) (by decide)
        (s :: (twosBits w x).reverse) [] _ termOK_nil
        (by simp [Function.update_apply, n6.symm, rip_fId, hYT, hsplit]))
    (runs_seq (runs_rField (RU := kRX) (RV := kRV) (src := kYT2) (dst := kYT) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) fNeg false [] termOK_nil
        (twosBits (w + 1) x) [] _
        (by simp [Function.update_apply, n1.symm, hRX, ruler, hlen1])
        (by simp [Function.update_apply, n8.symm, hYT2, hext, List.reverse_cons])
        (by simp [Function.update_apply, n4.symm, hRV]; exact termOK_nil))
    (runs_seq (runs_rField (RU := kRU) (RV := kRV) (src := kW) (dst := kJ) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) fId false [] termOK_nil
        (twosBits w 0) rest _
        (by simp [Function.update_apply, n3.symm, hRU, ruler, hlen0])
        (by simp [Function.update_apply, n5.symm])
        (by simp [Function.update_apply, n4.symm, hRV]; exact termOK_nil))
      (runs_L_moveBlock (src := kYT) (dst := Yk) n6.symm (twosBits (w + 1) (-x)).reverse
        [] _ termOK_nil
        (by simp [Function.update_apply, n6.symm, n7.symm, hneg, hYT]))))))))) ?_)
    (fun _ _ => trivial) (by simp [K1.length_twosBits]; omega)
  funext k
  by_cases k1 : k = Yk
  · subst k1
    simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, crecBits_one, recSyms,
      map_bit_twosBits_zero, ruler_eq, List.map_append]
  by_cases k2 : k = kW
  · subst k2
    simp [Function.update_apply, n5.symm]
  by_cases k3 : k = kJ
  · subst k3
    simp [Function.update_apply, n7.symm, rip_fId, map_bit_twosBits_zero, ruler_eq]
  by_cases k4 : k = kYT
  · subst k4
    simp [Function.update_apply, n6.symm, hYT]
  by_cases k5 : k = kYT2
  · subst k5
    simp [Function.update_apply, n8.symm, hYT2]
  simp [Function.update_apply, k1, k2, k3, k4, k5]

end SubNLogN.Machine.Bridge.SolveParamsAux
