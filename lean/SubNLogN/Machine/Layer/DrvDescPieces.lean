/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvDescPiecesProg

/-!
# DrvDesc PIECES, part 4 (`Machine/Layer/DrvDescPieces.lean`): the kernel and its contract

**Scope (honest summary).** Proves `drvDescPieces_holds : DrvDescPiecesStmt`
(`Machine/Layer/DrvDescDefs.lean`) with `J = 3`, `C = 10^12`. The closed program `piecesProg`
on `KLoc (Fin 2) PE` (registers `PReg`):
1. copies the value record `hdrSyms [P, d, r, a, R, K, e, S, ρ]` (restored) and splits it into
   floored field stacks (`parseProg`);
2. pushes the end tag `.tag 15` and the constant `mH`, and initializes the digit loop
   (`initProg`);
3. builds the base-`mH` digit table of `e`, entries `(digit, offset, mH^j, j)` (`runs_digitLoop`);
4. emits the piece descriptors entry by entry, the most significant digit first and, within an
   entry, `t = c - 1, …, 0` (`runs_emitLoop`), so that the first piece of `piecesOf e` ends on
   top;
5. pops the tables and the floored stacks (`cleanupProg`).
Every private stack is restored exactly (arbitrary content at entry). The cost is
`10^12 · (|record| + 1)^3`: the number of pieces is at most `mH` per digit, and every value has at
most `|record| + 21` bits.
-/

namespace SubNLogN.Machine.Layer.DrvDescPiecesAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability SubNLogN.Machine
open SubNLogN.Math.Networks (mH)

theorem len_hdr9 (P d r a R K e Sv ρ : ℕ) : (hdrSyms [P, d, r, a, R, K, e, Sv, ρ]).length =
    bitLen P + bitLen d + bitLen r + bitLen a + bitLen R + bitLen K + bitLen e + bitLen Sv +
      bitLen ρ + 9 := by
  simp only [hdrSyms, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    List.length_singleton, natSyms, List.length_map, bitLen] <;> omega

/-! ## Parsing the value record -/

/-- Parse one field: floor `f`, copy the top number of `hc` onto it, drop it and its mark. -/
def parseF (f : PE) : PP PL :=
  .seq (pushW (sx f) .mark) (.seq (copyW (sx .hc) (sx f) (sx .u))
    (.seq (dropW (sx .hc)) (popW (sx .hc))))

theorem runs_parseF (f : PE) (hfh : f ≠ .hc) (hfu : f ≠ .u) (S : PL → List Sym) (v : ℕ)
    (rest : List Sym) (hS : S (sx .hc) = natSyms v ++ Sym.mark :: rest) :
    Runs (parseF f) S
      (Function.update (Function.update S (sx f) (natSyms v ++ Sym.mark :: S (sx f))) (sx .hc)
        rest) (fun _ => True) (9 * bitLen v + 13) := by
  have hne : (sx .hc : PL) ≠ sx f := by simpa using hfh.symm
  have X := WP.W9comp.runs_seq (runs_pushW (sx f) .mark S)
    (WP.W9comp.runs_seq (runs_copyW (src := sx .hc) (dst := sx f) (tmp := sx .u) hne (by decide)
        (by simpa using hfu) v (Sym.mark :: rest) _ (tok_mark _)
        (by simp [Function.update_apply, hS, hfh.symm]))
    (WP.W9comp.runs_seq (runs_dropW (sx .hc) v (Sym.mark :: rest) _ (tok_mark _)
        (by simp [Function.update_apply, hS, hfh.symm]))
      (runs_popW (sx .hc) _ Sym.mark rest (by simp [Function.update_apply]))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) (by omega)
  funext k
  simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all)

/-- Parse the value record into the field stacks `f0 … f8`. -/
def parseProg : PP PL :=
  .seq (pushW (sx .u) .mark) (.seq (copyHdrW 9 kR (sx .hc) (sx .u)) (.seq (popW (sx .u))
    (.seq (parseF .f0) (.seq (parseF .f1) (.seq (parseF .f2) (.seq (parseF .f3)
      (.seq (parseF .f4) (.seq (parseF .f5) (.seq (parseF .f6) (.seq (parseF .f7)
        (parseF .f8)))))))))))

/-- The state after parsing: every field above a `mark`. -/
def fldSt (Sk : PL → List Sym) (P d r a R K e Sv ρ : ℕ) : PL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update Sk
      (sx .f0) (natSyms P ++ Sym.mark :: Sk (sx .f0)))
      (sx .f1) (natSyms d ++ Sym.mark :: Sk (sx .f1)))
      (sx .f2) (natSyms r ++ Sym.mark :: Sk (sx .f2)))
      (sx .f3) (natSyms a ++ Sym.mark :: Sk (sx .f3)))
      (sx .f4) (natSyms R ++ Sym.mark :: Sk (sx .f4)))
      (sx .f5) (natSyms K ++ Sym.mark :: Sk (sx .f5)))
      (sx .f6) (natSyms e ++ Sym.mark :: Sk (sx .f6)))
      (sx .f7) (natSyms Sv ++ Sym.mark :: Sk (sx .f7)))
      (sx .f8) (natSyms ρ ++ Sym.mark :: Sk (sx .f8))

theorem runs_parseProg (Sk : PL → List Sym) (P d r a R K e Sv ρ : ℕ) (vrest : List Sym)
    (hR : Sk kR = hdrSyms [P, d, r, a, R, K, e, Sv, ρ] ++ vrest) :
    Runs parseProg Sk (fldSt Sk P d r a R K e Sv ρ) (fun _ => True)
      (25 * (hdrSyms [P, d, r, a, R, K, e, Sv, ρ]).length + 300) := by
  have X := WP.W9comp.runs_seq (runs_pushW (sx .u) .mark Sk)
    (WP.W9comp.runs_seq (runs_copyHdrW (src := kR) (dst := sx .hc) (t := sx .u) (by decide)
        (by decide) (by decide) [P, d, r, a, R, K, e, Sv, ρ] vrest _
        (by simp [Function.update_apply, hR])
        (by simp only [Function.update_self]; exact tok_mark _))
    (WP.W9comp.runs_seq (runs_popW (sx .u) _ Sym.mark (Sk (sx .u))
        (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_parseF .f0 (by decide) (by decide) _ P
        (hdrSyms [d, r, a, R, K, e, Sv, ρ] ++ Sk (sx .hc)) (by simp [Function.update_apply, hdrSyms]))
    (WP.W9comp.runs_seq (runs_parseF .f1 (by decide) (by decide) _ d
        (hdrSyms [r, a, R, K, e, Sv, ρ] ++ Sk (sx .hc)) (by simp [Function.update_apply, hdrSyms]))
    (WP.W9comp.runs_seq (runs_parseF .f2 (by decide) (by decide) _ r
        (hdrSyms [a, R, K, e, Sv, ρ] ++ Sk (sx .hc)) (by simp [Function.update_apply, hdrSyms]))
    (WP.W9comp.runs_seq (runs_parseF .f3 (by decide) (by decide) _ a
        (hdrSyms [R, K, e, Sv, ρ] ++ Sk (sx .hc)) (by simp [Function.update_apply, hdrSyms]))
    (WP.W9comp.runs_seq (runs_parseF .f4 (by decide) (by decide) _ R
        (hdrSyms [K, e, Sv, ρ] ++ Sk (sx .hc)) (by simp [Function.update_apply, hdrSyms]))
    (WP.W9comp.runs_seq (runs_parseF .f5 (by decide) (by decide) _ K
        (hdrSyms [e, Sv, ρ] ++ Sk (sx .hc)) (by simp [Function.update_apply, hdrSyms]))
    (WP.W9comp.runs_seq (runs_parseF .f6 (by decide) (by decide) _ e
        (hdrSyms [Sv, ρ] ++ Sk (sx .hc)) (by simp [Function.update_apply, hdrSyms]))
    (WP.W9comp.runs_seq (runs_parseF .f7 (by decide) (by decide) _ Sv
        (hdrSyms [ρ] ++ Sk (sx .hc)) (by simp [Function.update_apply, hdrSyms]))
      (runs_parseF .f8 (by decide) (by decide) _ ρ (Sk (sx .hc))
        (by simp [Function.update_apply, hdrSyms]))))))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext k
    rcases k with i | x
    · simp [fldSt, Function.update_apply]
    · cases x <;> simp [fldSt, Function.update_apply]
  · have hl := len_hdr9 P d r a R K e Sv ρ
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-! ## Initialization -/

/-- Push the end tag and `mH`; initialize `q = e`, `j = 0`, `pw = 1`, `o = 0` and the tables. -/
def initProg : PP PL :=
  .seq (pushW kD drvEndTag) (.seq (pushW (sx .cM) .mark) (.seq (pushNatP (sx .cM) mH)
    (.seq (pushW (sx .q) .mark) (.seq (copyW (sx .f6) (sx .q) (sx .u))
      (.seq (pushW (sx .tA) .sep) (.seq (pushW (sx .tO) .sep) (.seq (pushW (sx .tP) .sep)
        (.seq (pushW (sx .tJ) .sep) (.seq (pushW (sx .o) .mark) (.seq (pushW (sx .pw) .mark)
          (.seq (pushNatP (sx .pw) 1) (pushW (sx .jj) .mark))))))))))))

/-- The base state of the digit loop: the fields, the end tag on `desc`, the constant `mH`. -/
def baseSt (Sk : PL → List Sym) (P d r a R K e Sv ρ : ℕ) : PL → List Sym :=
  Function.update (Function.update (fldSt Sk P d r a R K e Sv ρ) kD (drvEndTag :: Sk kD))
    (sx .cM) (natSyms mH ++ Sym.mark :: Sk (sx .cM))

theorem runs_initProg (Sk : PL → List Sym) (P d r a R K e Sv ρ : ℕ) :
    Runs initProg (fldSt Sk P d r a R K e Sv ρ)
      (digSt (baseSt Sk P d r a R K e Sv ρ) e (Sk (sx .q)) (Sk (sx .jj)) (Sk (sx .pw))
        (Sk (sx .o)) (Sk (sx .tA)) (Sk (sx .tO)) (Sk (sx .tP)) (Sk (sx .tJ)) 0)
      (fun _ => True) (7 * bitLen e + 60) := by
  have X := WP.W9comp.runs_seq (runs_pushW kD drvEndTag (fldSt Sk P d r a R K e Sv ρ))
    (WP.W9comp.runs_seq (runs_pushW (sx .cM) .mark _)
    (WP.W9comp.runs_seq (runs_pushNatP (sx .cM) mH _)
    (WP.W9comp.runs_seq (runs_pushW (sx .q) .mark _)
    (WP.W9comp.runs_seq (runs_copyW (src := sx .f6) (dst := sx .q) (tmp := sx .u) (by decide)
        (by decide) (by decide) e (Sym.mark :: Sk (sx .f6)) _ (tok_mark _)
        (by simp [fldSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_pushW (sx .tA) .sep _)
    (WP.W9comp.runs_seq (runs_pushW (sx .tO) .sep _)
    (WP.W9comp.runs_seq (runs_pushW (sx .tP) .sep _)
    (WP.W9comp.runs_seq (runs_pushW (sx .tJ) .sep _)
    (WP.W9comp.runs_seq (runs_pushW (sx .o) .mark _)
    (WP.W9comp.runs_seq (runs_pushW (sx .pw) .mark _)
    (WP.W9comp.runs_seq (runs_pushNatP (sx .pw) 1 _)
      (runs_pushW (sx .jj) .mark _))))))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext k
    rcases k with i | x
    · simp [digSt, baseSt, fldSt, Function.update_apply]
    · cases x <;> simp [digSt, baseSt, fldSt, Function.update_apply, dst_zero, digEs,
        tabOf_nil, NatArith.natSyms_zero]
  · have h1 : bitLen 1 ≤ 1 := NatArith.bitLen_le_of_lt' (by norm_num)
    have hm := bitLen_mH
    generalize bitLen mH = bm at hm ⊢
    generalize bitLen 1 = b1 at h1 ⊢
    omega

/-! ## Clean-up -/

/-- Pop the table floors and the floored stacks. -/
def cleanupProg : PP PL :=
  .seq (popW (sx .tA)) (.seq (popW (sx .tO)) (.seq (popW (sx .tP)) (.seq (popW (sx .tJ))
    (.seq (dropFW (sx .q)) (.seq (dropFW (sx .jj)) (.seq (dropFW (sx .pw)) (.seq (dropFW (sx .o))
      (.seq (dropFW (sx .cM)) (.seq (dropFW (sx .f0)) (.seq (dropFW (sx .f1))
        (.seq (dropFW (sx .f2)) (.seq (dropFW (sx .f3)) (.seq (dropFW (sx .f4))
          (.seq (dropFW (sx .f5)) (.seq (dropFW (sx .f6)) (.seq (dropFW (sx .f7))
            (dropFW (sx .f8))))))))))))))))))

/-- **The kernel.** -/
def piecesProg : PP PL :=
  .seq parseProg (.seq initProg (.seq (whileW (sx .q) optIsBit digitStep)
    (.seq (whileW (sx .tA) notSep entryStep) cleanupProg)))

theorem digEs_bounds (e n : ℕ) (hn : bitLen e + 20 ≤ n) :
    ∀ x ∈ digEs e (Nat.digits mH e).length, x.1 ≤ mH ∧ bitLen x.2.1 ≤ n ∧
      bitLen x.2.2.1 ≤ n ∧ bitLen x.2.2.2 ≤ n ∧ ∀ t < x.1, bitLen (t * x.2.2.1 + x.2.1) ≤ n := by
  intro x hx
  simp only [digEs, List.mem_reverse, List.mem_map, List.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  have hpow : mH ^ k ≤ e := pow_le_of_lt_len hk
  have ho : (dst e k).2.2 < mH ^ k := dst_o_lt e k
  have hlt : (dst e k).1 % mH < mH := Nat.mod_lt _ mH_pos
  have hNb := len_le_bitLen e
  have hmul : bitLen (mH * e) ≤ bitLen e + 20 :=
    le_trans (NatArith.bitLen_mul_le' _ _) (by have := bitLen_mH; omega)
  simp only [dent, dst_j]
  refine ⟨hlt.le, ?_, ?_, ?_, ?_⟩
  · exact le_trans (NatArith.bitLen_mono'' (le_of_lt (lt_of_lt_of_le ho hpow))) (by omega)
  · exact le_trans (NatArith.bitLen_mono'' hpow) (by omega)
  · exact le_trans (bitLen_le_self _) (by omega)
  · intro t ht
    have h1 : t * mH ^ k ≤ (mH - 1) * mH ^ k := Nat.mul_le_mul_right _ (by omega)
    have h2 : (mH - 1) * mH ^ k + mH ^ k = mH ^ k * mH := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (show 1 ≤ mH by norm_num [mH]),
        Nat.mul_comm]
    have h3 : mH ^ k * mH ≤ mH * e := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hpow
    exact le_trans (NatArith.bitLen_mono'' (show t * mH ^ k + (dst e k).2.2 ≤ mH * e by omega))
      (by omega)

theorem desc_eq (P d r a R K e Sv ρ : ℕ) (L : List Sym) :
    (digEs e (Nat.digits mH e).length).reverse.flatMap (entBlk P d r a R K e Sv ρ) ++
      drvEndTag :: L = descOfVals P d r a R K e Sv ρ ++ L := by
  rw [descOfVals_eq, digEs, List.reverse_reverse, ents_eq]
  simp

theorem pow_len_le (e : ℕ) : mH ^ (Nat.digits mH e).length ≤ mH * e + 1 := by
  rcases h : (Nat.digits mH e).length with _ | k
  · simp
  · have := pow_le_of_lt_len (e := e) (i := k) (by omega)
    rw [pow_succ, Nat.mul_comm]
    have := Nat.mul_le_mul_left mH this
    omega

/-! ## The kernel runs -/

/-- **The kernel**: from the value record, the descriptor stack gains `descOfVals …`; every other
stack is restored. -/
theorem runs_piecesProg (P d r a R K e Sv ρ : ℕ) (vrest : List Sym) (Sk : PL → List Sym)
    (hR : Sk kR = hdrSyms [P, d, r, a, R, K, e, Sv, ρ] ++ vrest) :
    Runs piecesProg Sk (Function.update Sk kD (descOfVals P d r a R K e Sv ρ ++ Sk kD))
      (fun _ => True) (10 ^ 12 * ((hdrSyms [P, d, r, a, R, K, e, Sv, ρ]).length + 1) ^ 3) := by
  have hl := len_hdr9 P d r a R K e Sv ρ
  obtain ⟨n0, hn0⟩ : ∃ n0, (hdrSyms [P, d, r, a, R, K, e, Sv, ρ]).length = n0 := ⟨_, rfl⟩
  rw [hn0] at hl ⊢
  have hB : FldB P d r a R K e Sv ρ (n0 + 21) := by unfold FldB; omega
  have hNb : (Nat.digits mH e).length ≤ bitLen e := len_le_bitLen e
  have X1 := runs_parseProg Sk P d r a R K e Sv ρ vrest hR
  rw [hn0] at X1
  have X2 := runs_initProg Sk P d r a R K e Sv ρ
  obtain ⟨B, hBd⟩ : ∃ B, B = baseSt Sk P d r a R K e Sv ρ := ⟨_, rfl⟩
  rw [← hBd] at X2
  have X3 := runs_digitLoop B e (Sk (sx .q)) (Sk (sx .jj)) (Sk (sx .pw)) (Sk (sx .o))
    (Sk (sx .tA)) (Sk (sx .tO)) (Sk (sx .tP)) (Sk (sx .tJ)) (Sk (sx .cM)) (by simp [hBd, baseSt])
  obtain ⟨D, hD⟩ : ∃ D, D = digSt B e (Sk (sx .q)) (Sk (sx .jj)) (Sk (sx .pw)) (Sk (sx .o))
      (Sk (sx .tA)) (Sk (sx .tO)) (Sk (sx .tP)) (Sk (sx .tJ)) (Nat.digits mH e).length :=
    ⟨_, rfl⟩
  rw [← hD] at X3
  have hFD : FldOK D P d r a R K e Sv ρ := by
    simp only [FldOK, hD, hBd, digSt, baseSt, fldSt, Function.update_apply]
    simp
  have X4 := runs_emitLoop D P d r a R K e Sv ρ (n0 + 21) (digEs e (Nat.digits mH e).length)
    (Sk (sx .tA)) (Sk (sx .tO)) (Sk (sx .tP)) (Sk (sx .tJ)) hFD hB
    (by simp [hD, digSt, Function.update_apply]) (by simp [hD, digSt, Function.update_apply])
    (by simp [hD, digSt, Function.update_apply]) (by simp [hD, digSt, Function.update_apply])
    (by omega) (digEs_bounds e (n0 + 21) (by omega))
  obtain ⟨E, hE⟩ : ∃ E, E = emitSt D P d r a R K e Sv ρ (digEs e (Nat.digits mH e).length)
      (Sk (sx .tA)) (Sk (sx .tO)) (Sk (sx .tP)) (Sk (sx .tJ))
      (digEs e (Nat.digits mH e).length).length := ⟨_, rfl⟩
  rw [← hE] at X4
  have hlen : (digEs e (Nat.digits mH e).length).length = (Nat.digits mH e).length := by
    simp [digEs]
  have hq0 : (dst e (Nat.digits mH e).length).1 = 0 := (dst_eq_zero_iff e _).2 le_rfl
  have ev : ∀ k : PL, E k = emitSt D P d r a R K e Sv ρ (digEs e (Nat.digits mH e).length)
      (Sk (sx .tA)) (Sk (sx .tO)) (Sk (sx .tP)) (Sk (sx .tJ))
      (digEs e (Nat.digits mH e).length).length k := fun k => by rw [hE]
  refine pseq X1 (pseq X2 (pseq X3 (pseq X4 (pweak
    (WP.W9comp.runs_seq (runs_popW (sx .tA) E Sym.sep (Sk (sx .tA))
      (by simp [ev, emitSt, Function.update_apply, tabOf_nil]))
    (WP.W9comp.runs_seq (runs_popW (sx .tO) _ Sym.sep (Sk (sx .tO))
      (by simp [ev, emitSt, Function.update_apply, tabOf_nil]))
    (WP.W9comp.runs_seq (runs_popW (sx .tP) _ Sym.sep (Sk (sx .tP))
      (by simp [ev, emitSt, Function.update_apply, tabOf_nil]))
    (WP.W9comp.runs_seq (runs_popW (sx .tJ) _ Sym.sep (Sk (sx .tJ))
      (by simp [ev, emitSt, Function.update_apply, tabOf_nil]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .q) (dst e (Nat.digits mH e).length).1 .mark (Sk (sx .q)) _ rfl
      (by simp [ev, emitSt, hD, digSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .jj) (Nat.digits mH e).length .mark (Sk (sx .jj)) _ rfl
      (by simp [ev, emitSt, hD, digSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .pw) (mH ^ (Nat.digits mH e).length) .mark (Sk (sx .pw)) _ rfl
      (by simp [ev, emitSt, hD, digSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .o) (dst e (Nat.digits mH e).length).2.2 .mark (Sk (sx .o)) _ rfl
      (by simp [ev, emitSt, hD, digSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .cM) mH .mark (Sk (sx .cM)) _ rfl
      (by simp [ev, emitSt, hD, digSt, hBd, baseSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .f0) P .mark (Sk (sx .f0)) _ rfl
      (by simp [ev, emitSt, hD, digSt, hBd, baseSt, fldSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .f1) d .mark (Sk (sx .f1)) _ rfl
      (by simp [ev, emitSt, hD, digSt, hBd, baseSt, fldSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .f2) r .mark (Sk (sx .f2)) _ rfl
      (by simp [ev, emitSt, hD, digSt, hBd, baseSt, fldSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .f3) a .mark (Sk (sx .f3)) _ rfl
      (by simp [ev, emitSt, hD, digSt, hBd, baseSt, fldSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .f4) R .mark (Sk (sx .f4)) _ rfl
      (by simp [ev, emitSt, hD, digSt, hBd, baseSt, fldSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .f5) K .mark (Sk (sx .f5)) _ rfl
      (by simp [ev, emitSt, hD, digSt, hBd, baseSt, fldSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .f6) e .mark (Sk (sx .f6)) _ rfl
      (by simp [ev, emitSt, hD, digSt, hBd, baseSt, fldSt, Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .f7) Sv .mark (Sk (sx .f7)) _ rfl
      (by simp [ev, emitSt, hD, digSt, hBd, baseSt, fldSt, Function.update_apply]))
      (runs_dropFW (sx .f8) ρ .mark (Sk (sx .f8)) _ rfl
        (by simp [ev, emitSt, hD, digSt, hBd, baseSt, fldSt, Function.update_apply])))))))))))))))))))
    ?_ le_rfl) le_rfl) le_rfl) le_rfl) ?_
  · rw [← desc_eq P d r a R K e Sv ρ (Sk kD)]
    funext k
    rcases k with i | x
    · fin_cases i <;> simp [ev, emitSt, hD, digSt, hBd, baseSt, fldSt, Function.update_apply]
    · cases x <;> simp [ev, emitSt, hD, digSt, hBd, baseSt, fldSt, Function.update_apply]
  · have hbe : bitLen e ≤ n0 := by omega
    have hNn : (Nat.digits mH e).length ≤ n0 := le_trans hNb hbe
    have hM : 1 ≤ n0 + 1 := by omega
    have p1 : n0 + 1 ≤ (n0 + 1) ^ 3 := by
      have := Nat.pow_le_pow_right hM (show 1 ≤ 3 by norm_num)
      simpa using this
    have q1 : (bitLen e + 22) ^ 2 ≤ 484 * (n0 + 1) ^ 2 := by
      have h : bitLen e + 22 ≤ 22 * (n0 + 1) := by omega
      calc (bitLen e + 22) ^ 2 ≤ (22 * (n0 + 1)) ^ 2 := Nat.pow_le_pow_left h 2
        _ = 484 * (n0 + 1) ^ 2 := by ring
    have q2 : (n0 + 21 + 1) ^ 2 ≤ 484 * (n0 + 1) ^ 2 := by
      have h : n0 + 21 + 1 ≤ 22 * (n0 + 1) := by omega
      calc (n0 + 21 + 1) ^ 2 ≤ (22 * (n0 + 1)) ^ 2 := Nat.pow_le_pow_left h 2
        _ = 484 * (n0 + 1) ^ 2 := by ring
    have hsq : 1 ≤ (n0 + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have c3 : (Nat.digits mH e).length * (900 * (bitLen e + 22) ^ 2 + 2) ≤
        (n0 + 1) * (435602 * (n0 + 1) ^ 2) := Nat.mul_le_mul (by omega) (by omega)
    have c4 : (digEs e (Nat.digits mH e).length).length *
        ((mH + 1) * (1000 * (n0 + 21 + 1) ^ 2 + 40) + 2) ≤
        (n0 + 1) * (484040484042 * (n0 + 1) ^ 2) := by
      apply Nat.mul_le_mul (by omega)
      have h5 : (mH + 1) * (1000 * (n0 + 21 + 1) ^ 2 + 40) + 2 =
          1000001000 * (n0 + 21 + 1) ^ 2 + 40000042 := by norm_num [mH]; ring
      rw [h5]
      omega
    have e3 : (n0 + 1) * (435602 * (n0 + 1) ^ 2) = 435602 * (n0 + 1) ^ 3 := by ring
    have e4 : (n0 + 1) * (484040484042 * (n0 + 1) ^ 2) = 484040484042 * (n0 + 1) ^ 3 := by ring
    have hpw := pow_len_le e
    have hpwb : bitLen (mH ^ (Nat.digits mH e).length) ≤ n0 + 22 := by
      have h1 := NatArith.bitLen_mono'' hpw
      have h2 := NatArith.bitLen_add_le' (mH * e) 1
      have h3 := NatArith.bitLen_mul_le' mH e
      have h4 : bitLen 1 ≤ 1 := NatArith.bitLen_le_of_lt' (by norm_num)
      have h5 := bitLen_mH
      generalize bitLen (mH ^ (Nat.digits mH e).length) = x0 at h1 ⊢
      generalize bitLen (mH * e + 1) = x1 at h1 h2
      generalize bitLen (mH * e) = x2 at h2 h3
      generalize bitLen mH = x3 at h3 h5
      generalize bitLen 1 = x4 at h2 h4
      omega
    have hob : bitLen (dst e (Nat.digits mH e).length).2.2 ≤ n0 + 22 :=
      le_trans (NatArith.bitLen_mono'' (dst_o_lt e _).le) hpwb
    have hNb' : bitLen (Nat.digits mH e).length ≤ n0 := le_trans (bitLen_le_self _) hNn
    have hm := bitLen_mH
    have h0 : bitLen 0 = 0 := rfl
    rw [hq0, h0, show (10 : ℕ) ^ 12 = 1000000000000 by norm_num]
    generalize bitLen (mH ^ (Nat.digits mH e).length) = bpw at hpwb ⊢
    generalize bitLen (dst e (Nat.digits mH e).length).2.2 = bo at hob ⊢
    generalize bitLen (Nat.digits mH e).length = bN at hNb' ⊢
    generalize bitLen mH = bm at hm ⊢
    generalize (Nat.digits mH e).length * (900 * (bitLen e + 22) ^ 2 + 2) = Y3 at c3 ⊢
    generalize (digEs e (Nat.digits mH e).length).length *
      ((mH + 1) * (1000 * (n0 + 21 + 1) ^ 2 + 40) + 2) = Y4 at c4 ⊢
    generalize (n0 + 1) * (435602 * (n0 + 1) ^ 2) = Z3 at c3 e3
    generalize (n0 + 1) * (484040484042 * (n0 + 1) ^ 2) = Z4 at c4 e4
    generalize (n0 + 1) ^ 3 = M3 at e3 e4 p1 ⊢
    clear * - hl c3 e3 c4 e4 p1 hpwb hob hNb' hm
    linarith

end SubNLogN.Machine.Layer.DrvDescPiecesAux
