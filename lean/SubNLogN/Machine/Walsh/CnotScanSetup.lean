/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanValue
import SubNLogN.Machine.Walsh.CnotHdr

/-!
# `SubNLogN.Machine.Walsh.CnotScanSetup`: templates of the CNOT-batch scans

Paper: Lemma 5.3 (`lem:walsh-lift`, `w_* = w + 8d`). Plan: top of
`Walsh/CnotScanEngine.lean`.

**Scope (honest summary).** Setup programs with `Runs` lemmas: unary copies of header fields
(`unaryOfTop`), the field-width template `tcc = uSym^{w + 8d}` (`tplSetup`, header restored);
the lift of `Runs` to `RunsR` (`runsR_of_runs`) and back (`runs_of_runsR`). (The shift split
`splitP` is in `Walsh/CnotScanShift.lean`.) No contract is proved here.
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine WalshLift Computability
open WP.W9comp (runs_seq runs_mono runs_congr)

/-! ## From `Runs` to `RunsR` -/

theorem runsR_of_runs {P : SProg SK} {S S' : SK → List Sym} {T : ℕ}
    (h : Runs P S S' (fun _ => True) T) (A : ER → Prop) (hA : ∀ r v, A r → A { r with t := v }) :
    RunsR (P.liftRegs lT) S S' A A T := by
  intro r hr
  obtain ⟨s', t, e, ⟨hs, -⟩, ht⟩ := h ⟨r.t, S⟩ rfl
  obtain ⟨var', stk'⟩ := s'
  change stk' = S' at hs
  subst hs
  exact ⟨{ r with t := var' }, t, Eval.liftRegs lT e r rfl, hA r var' hr, ht⟩

theorem runs_of_runsR {P : EProg SK} {S S' : SK → List Sym} {B : ER → Prop} {T : ℕ}
    (h : RunsR P S S' (fun _ => True) B T) : Runs P S S' (fun _ => True) T :=
  Runs.of_eval fun v => by
    obtain ⟨r', t, e, -, ht⟩ := h v trivial
    exact ⟨r', t, e, trivial, ht⟩

/-! ## Unary copies of header fields -/

section Unary

variable {K : Type}

/-- Put `uSym^n` on `dst`, `n` the top field of `src` (restored); `bits`, `u` scratch. -/
def unaryOfTop (src dst bits u : K) : SProg K :=
  .seq (moveBits src bits) (.seq (pushC src .mark) (toUnary bits dst src u))

theorem closed_unaryOfTop (src dst bits u : K) : (unaryOfTop src dst bits u).Closed := by
  refine WP.W9comp.closed_seq ?_ (WP.W9comp.closed_seq trivial (closed_toUnary _ _ _ _))
  simp [Prog.Closed, Prog.FreeBelow, moveBits, moveBitsBody, pushR, popR]

variable [DecidableEq K]

theorem runs_unaryOfTop {src dst bits u : K} (h1 : src ≠ dst) (h2 : src ≠ bits) (h3 : src ≠ u)
    (h4 : dst ≠ bits) (h5 : dst ≠ u) (h6 : bits ≠ u) (n : ℕ) (rest : List Sym)
    (S : K → List Sym) (hS : S src = natSyms n ++ Sym.mark :: rest) (hb : S bits = [])
    (hd : S dst = []) (hu : S u = []) :
    Runs (unaryOfTop src dst bits u) S (Function.update S dst (List.replicate n uSym))
      (fun _ => True) (20 * n + 5) := by
  apply Runs.of_eval
  intro v
  have e1 := moveBits_eval h2 [] v (encodeNat n) (Sym.mark :: rest) S (TermOK.cons rfl _) hS
  simp only [List.tail_cons, List.head?_cons] at e1
  set S1 := Function.update (Function.update S src rest) bits
    ((encodeNat n).reverse.map Sym.bit ++ S bits) with hS1
  have e2 := eval_pushC src Sym.mark (some .mark) S1
  set S2 := Function.update S1 src (Sym.mark :: S1 src) with hS2
  obtain ⟨t3, e3, ht3⟩ := toUnary_eval (src := bits) (dst := dst) (h := src) (u := u) h4.symm
    h2.symm h6 h1.symm h5 h3 (some .mark) (encodeNat n).reverse 0 S2
    (by rw [hS2, Function.update_of_ne h2.symm, hS1, Function.update_self, hb, List.append_nil])
    (by rw [hS2, Function.update_of_ne h1.symm, hS1, Function.update_of_ne h4,
      Function.update_of_ne h1.symm, hd]; rfl)
    (by rw [hS2, Function.update_of_ne h3.symm, hS1, Function.update_of_ne h6.symm,
      Function.update_of_ne h3.symm, hu])
  rw [accBits_encodeNat, List.reverse_reverse] at e3
  rw [accBits_encodeNat] at ht3
  refine ⟨none, _, (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ rfl, trivial, ?_⟩
  · congr 1
    funext k
    by_cases a1 : k = src
    · subst a1
      simp [hS2, hS1, h1, h2, hS, natSyms]
    by_cases a2 : k = bits
    · subst a2
      simp [hS2, hS1, h2, hb, Ne.symm h2, Ne.symm h4]
    by_cases a3 : k = dst
    · subst a3
      simp [hS2, hS1, Ne.symm h1]
    · simp [hS2, hS1, a1, a2, a3]
  · have hb' : (encodeNat n).length ≤ n := bitLen_le_self n
    simp only [List.length_reverse] at ht3
    omega

theorem runs_drain2 {src dst : K} (hne : src ≠ dst) (L : List Sym) (S : K → List Sym)
    (hS : S src = L) :
    Runs (drain2 src dst) S (Function.update (Function.update S src []) dst
      (List.replicate (2 * L.length) uSym ++ S dst)) (fun _ => True) (4 * L.length + 2) :=
  Runs.of_eval fun v => ⟨_, _, drain2_eval hne v L S hS, trivial, le_rfl⟩

end Unary

/-! ## The field-width template -/

/-- Build `tcc = uSym^{w + 8d}` from the slice header (restored). -/
def tplSetup : SProg SK :=
  .seq (WalshCnot1.skipFields (.inl 1) (.inr .pk) 1)
  (.seq (unaryOfTop (.inl 1) (.inr .n2) (.inr .n1) (.inr .u))
  (.seq (WalshCnot1.skipFields (.inl 1) (.inr .pk) 1)
  (.seq (WalshCnot1.skipFields (.inl 1) (.inr .pk) 1)
  (.seq (unaryOfTop (.inl 1) (.inr .tcc) (.inr .n1) (.inr .u))
  (.seq (drain (.inr .pk) (.inl 1))
  (.seq (drain2 (.inr .n2) (.inr .n4)) (.seq (drain2 (.inr .n4) (.inr .n5))
    (drain2 (.inr .n5) (.inr .tcc)))))))))

theorem closed_tplSetup : tplSetup.Closed := by
  have hsk := WalshCnot1.closed_skipFields (.inl 1 : SK) (.inr .pk) 1
  have hd2 : ∀ src dst : SK, (drain2 src dst).Closed := fun _ _ => by
    simp [Prog.Closed, Prog.FreeBelow, drain2, drain2Body, pushC, popR]
  exact WP.W9comp.closed_seq hsk (WP.W9comp.closed_seq (closed_unaryOfTop _ _ _ _)
    (WP.W9comp.closed_seq hsk (WP.W9comp.closed_seq hsk (WP.W9comp.closed_seq
    (closed_unaryOfTop _ _ _ _) (WP.W9comp.closed_seq (closed_drain _ _) (WP.W9comp.closed_seq
    (hd2 _ _) (WP.W9comp.closed_seq (hd2 _ _) (hd2 _ _))))))))

/-- The cost bound of `tplSetup`. -/
def tplCost (P d r w : ℕ) : ℕ :=
  6 * (bitLen P + bitLen d + bitLen r) + 48 * d + 20 * w + 39

theorem runs_tplSetup (P d r w K m j₀ D nS ρ : ℕ) (hrest : List Sym) (S : SK → List Sym)
    (hcl : ∀ e : SS, S (.inr e) = []) (hH : S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest) :
    Runs tplSetup S (Function.update S (.inr .tcc) (List.replicate (w + 8 * d) uSym))
      (fun _ => True) (tplCost P d r w) := by
  have hH' : S (.inl 1) = hdrSyms [P] ++ (natSyms d ++ Sym.mark :: (natSyms r ++
      Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms [K, m, j₀, D, nS, ρ] ++ hrest)))) := by
    rw [hH]
    simp [sliceHdr, hdrSyms]
  have R := runs_seq (runs_skipFields (src := (.inl 1 : SK)) (pk := .inr .pk) (by simp)
      (natSyms d ++ Sym.mark :: (natSyms r ++ Sym.mark :: (natSyms w ++ Sym.mark ::
        (hdrSyms [K, m, j₀, D, nS, ρ] ++ hrest)))) [P] S hH')
    (runs_seq (runs_unaryOfTop (src := (.inl 1 : SK)) (dst := .inr .n2) (bits := .inr .n1)
      (u := .inr .u) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) d
      (natSyms r ++ Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms [K, m, j₀, D, nS, ρ] ++ hrest)))
      _ (by simp) (by simp [hcl]) (by simp [hcl]) (by simp [hcl]))
    (runs_seq (runs_skipFields (src := (.inl 1 : SK)) (pk := .inr .pk) (by simp)
      (natSyms r ++ Sym.mark :: (natSyms w ++ Sym.mark :: (hdrSyms [K, m, j₀, D, nS, ρ] ++ hrest)))
      [d] _ (by simp [hdrSyms]))
    (runs_seq (runs_skipFields (src := (.inl 1 : SK)) (pk := .inr .pk) (by simp)
      (natSyms w ++ Sym.mark :: (hdrSyms [K, m, j₀, D, nS, ρ] ++ hrest)) [r] _
      (by simp [hdrSyms]))
    (runs_seq (runs_unaryOfTop (src := (.inl 1 : SK)) (dst := .inr .tcc) (bits := .inr .n1)
      (u := .inr .u) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) w
      (hdrSyms [K, m, j₀, D, nS, ρ] ++ hrest) _ (by simp) (by simp [hcl]) (by simp [hcl])
      (by simp [hcl]))
    (runs_seq (runs_drain (src := (.inr .pk : SK)) (dst := .inl 1) (by simp)
      ((hdrSyms [r]).reverse ++ ((hdrSyms [d]).reverse ++ (hdrSyms [P]).reverse)) _
      (by simp [hcl]))
    (runs_seq (runs_drain2 (src := (.inr .n2 : SK)) (dst := .inr .n4) (by simp)
      (List.replicate d uSym) _ (by simp))
    (runs_seq (runs_drain2 (src := (.inr .n4 : SK)) (dst := .inr .n5) (by simp)
      (List.replicate (2 * d) uSym) _ (by simp [hcl]))
      (runs_drain2 (src := (.inr .n5 : SK)) (dst := .inr .tcc) (by simp)
        (List.replicate (2 * (2 * d)) uSym) _ (by simp [hcl])))))))))
  rw [show w + 8 * d = 2 * (2 * (2 * d)) + w by omega]
  refine runs_mono (runs_congr R ?_) (fun _ _ => trivial) ?_
  · funext j
    rcases j with i | e
    · fin_cases i
      · simp
      · simp [hH, sliceHdr, hdrSyms]
      · simp
    · cases e <;> simp [hcl]
  · simp only [tplCost, WalshCnot1.length_hdrSyms_single, List.length_reverse, List.length_append,
      List.length_replicate]
    omega

end SubNLogN.Machine.WalshScanAux
