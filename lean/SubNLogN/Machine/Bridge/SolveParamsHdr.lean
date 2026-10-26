/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SolveParamsStage
import SubNLogN.Machine.Arith.Ruler
import SubNLogN.Machine.Bridge.PrePostBase
import SubNLogN.Machine.Calculus.Basic
import IntMulTM.SpecFacts

/-!
# SOL-PARAM-ROWS (P1): the header parse (`Bridge/SolveParamsHdr.lean`)

`hdrParse` reads the header `hdrSyms b.hdr` on `sPar` and the stage counter `natSyms m` on `sAx`
(both restored) and leaves on the scratch stacks of the parameter-row kernel (`SK`):
`kRU = ruler wT`, `kRX = ruler (wT + 1)`, `kCX = natSyms (i - 1)` (`i = d - m`),
`kCT = natSyms (t_i / 2)`, `kCU = natSyms (∏_{l > i} t_l)`; every other scratch stack ends empty.
Register `AReg`; `TMFw.Lib` programs run through `lensO` (`Lo`).
* `fetchF k dst`: copy header field `k` onto `dst` (guard `sep2` on `kH`, skip, copy, rewind);
* `cLoop c body`: `while (c ≠ 0) { body ; c := c - 1 }` (`runs_cLoop`);
* phases: `i` by `d - m` (`subLoop`), the walk to `t_i` (`skipLoop`), the suffix product of the
  powers of two `t_l`, `l > i` (`sufLoop`), and the rulers (`buildRuler`, a walk, `clearMarks`).
All proved; helpers in `SubNLogN.Machine.Bridge.SolveParamsHdrAux`.
-/

namespace SubNLogN.Machine.Bridge.SolveParamsHdrAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Arith
  SubNLogN.Machine.Bridge.SolveParamsAux SubNLogN.Math.Common SubNLogN.Math.Bridge Computability
open WP.W9comp (runs_seq runs_mono runs_congr)

/-! ## Lifting and evaluation helpers -/

/-- A `TMFw.Lib` program on the register `AReg` (through `lensO`). -/
def Lo (p : TMFw.Lib.SProg SK) : AProg SK := p.liftRegs lensO

theorem runs_Lo {p : TMFw.Lib.SProg SK} {S S' : SK → List Sym} {Q : Option Sym → Prop} {T : ℕ}
    (h : Runs p S S' Q T) : Runs (Lo p) S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨⟨v', stk'⟩, t, e, ⟨hs', -⟩, ht⟩ := h ⟨lensO.get v, stk⟩ rfl
  change stk' = S' at hs'
  subst hs'
  exact ⟨_, t, Eval.liftRegs lensO e v rfl, ⟨rfl, trivial⟩, ht⟩

theorem runsA_of_eval {p : AProg SK} {S S' : SK → List Sym} {T : ℕ}
    (h : ∀ v, ∃ v' t, Eval [] p ⟨v, S⟩ ⟨v', S'⟩ t ∧ t ≤ T) :
    Runs p S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨v', t, e, ht⟩ := h v
  exact ⟨⟨v', S'⟩, t, e, ⟨rfl, trivial⟩, ht⟩

theorem runs_LoEval {p : TMFw.Lib.SProg SK} {S S' : SK → List Sym} {t : ℕ}
    (h : ∀ v, ∃ v', Eval [] p ⟨v, S⟩ ⟨v', S'⟩ t) : Runs (Lo p) S S' (fun _ => True) t :=
  SolveAux.runs_liftRegs_of_eval lensO h

/-! ## Binary encodings -/

theorem encodeNat_two_mul' {n : ℕ} (hn : 1 ≤ n) : encodeNat (2 * n) = false :: encodeNat n := by
  rw [two_mul, encodeNat_add, if_neg]
  intro h
  rw [encodeNat_eq_nil_iff] at h
  omega

theorem encodeNat_pow_two' : ∀ a : ℕ, encodeNat (2 ^ a) = List.replicate a false ++ [true]
  | 0 => by simpa [encodeNat_zero] using encodeNat_add_add_one 0
  | a + 1 => by
    rw [pow_succ, mul_comm, encodeNat_two_mul' Nat.one_le_two_pow, encodeNat_pow_two' a]
    simp [List.replicate_succ]

theorem natSyms_pow_two' (a : ℕ) :
    natSyms (2 ^ a) = List.replicate a (Sym.bit false) ++ [Sym.bit true] := by
  rw [natSyms, encodeNat_pow_two']
  simp [List.map_replicate]

theorem isBitO_natSyms_head (n : ℕ) (rc : List Sym) (hrc : TermOK rc) :
    isBitO (natSyms n ++ rc).head? = decide (0 < n) := by
  by_cases hn : n = 0
  · subst hn
    simp only [natSyms, encodeNat_zero, List.map_nil, List.nil_append]
    rw [isBitO_false_of_termOK hrc]
    simp
  · obtain ⟨b, l, hbl⟩ : ∃ b l, encodeNat n = b :: l := by
      cases h : encodeNat n with
      | nil => exact absurd ((encodeNat_eq_nil_iff n).1 h) hn
      | cons b l => exact ⟨b, l, rfl⟩
    simp [natSyms, hbl, Nat.pos_of_ne_zero hn]

/-! ## Header lemmas -/

theorem hdrSyms_drop' (fs : List ℕ) (k : ℕ) (hk : k < fs.length) :
    hdrSyms (fs.drop k) = natSyms fs[k] ++ Sym.mark :: hdrSyms (fs.drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons hk, BridgePP.hdrSyms_cons]

theorem hdrSyms_take_succ' (fs : List ℕ) (k : ℕ) (hk : k < fs.length) :
    (hdrSyms (fs.take (k + 1))).reverse =
      (natSyms fs[k] ++ [Sym.mark]).reverse ++ (hdrSyms (fs.take k)).reverse := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, BridgePP.hdrSyms_append,
    List.reverse_append]
  simp [hdrSyms]

theorem hdrSyms_split (fs : List ℕ) (k : ℕ) :
    hdrSyms fs = hdrSyms (fs.take k) ++ hdrSyms (fs.drop k) := by
  rw [← BridgePP.hdrSyms_append, List.take_append_drop]

theorem length_hdrSyms_le (fs : List ℕ) (k : ℕ) (hk : k < fs.length) :
    (hdrSyms (fs.take k)).length + bitLen fs[k] + 1 ≤ (hdrSyms fs).length := by
  have h1 := hdrSyms_split fs k
  rw [hdrSyms_drop' fs k hk] at h1
  have h2 := congrArg List.length h1
  simp only [List.length_append, List.length_cons, length_natSyms] at h2
  omega

/-! ## Counter loops -/

/-- `while (c ≠ 0) { body ; c := c - 1 }` on the binary counter `c` (temporary `kTQ`). -/
def cLoop (c : SK) (body : AProg SK) : AProg SK :=
  .seq (peekO c) (.loop (fun v => isBitO v.o)
    (.seq body (.seq (Lo (TMFw.Lib.dec c kTQ)) (peekO c))))

theorem runs_peekO (c : SK) (S : SK → List Sym) :
    Runs (peekO c) S S (fun v => v.o = (S c).head?) 1 := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  exact ⟨_, 1, eval_peekO c v stk, ⟨rfl, rfl⟩, le_refl _⟩

theorem runs_decC (c : SK) (hc : c ≠ kTQ) (n : ℕ) (rc : List Sym) (hrc : TermOK rc)
    (S : SK → List Sym) (hS : S c = natSyms n ++ rc) :
    Runs (Lo (TMFw.Lib.dec c kTQ)) (Function.update S c (natSyms (n + 1) ++ rc)) S
      (fun _ => True) (6 * bitLen (n + 1) + 8) := by
  have hz : TMFw.zerosLead (encodeNat (n + 1)) ≤ bitLen (n + 1) := by
    unfold bitLen; exact TMFw.zerosLead_le_length _
  refine runs_mono (runs_LoEval (t := 6 * TMFw.zerosLead (encodeNat (n + 1)) + 8)
    fun v => ⟨some .mark, ?_⟩) (fun _ _ => trivial) (by omega)
  have e := TMFw.Lib.dec_eval hc [] v n rc (Function.update S c (natSyms (n + 1) ++ rc)) hrc
    (by rw [Function.update_self]; rfl)
  refine e.of_eq ?_ rfl
  rw [Function.update_idem]
  congr 1
  rw [show List.map Sym.bit (encodeNat n) ++ rc = S c from hS.symm, Function.update_eq_self]

theorem runs_decC' (c : SK) (hc : c ≠ kTQ) (n : ℕ) (rc : List Sym) (hrc : TermOK rc)
    (S : SK → List Sym) (hS : S c = natSyms (n + 1) ++ rc) :
    Runs (Lo (TMFw.Lib.dec c kTQ)) S (Function.update S c (natSyms n ++ rc)) (fun _ => True)
      (6 * bitLen (n + 1) + 8) := by
  have h := runs_decC c hc n rc hrc (Function.update S c (natSyms n ++ rc))
    (Function.update_self ..)
  rwa [Function.update_idem, ← hS, Function.update_eq_self] at h

theorem natSyms_zero'' : natSyms 0 = [] := by simp [natSyms, TMFw.encodeNat_zero]

theorem natSyms_one' : natSyms 1 = [Sym.bit true] := by
  have h := natSyms_pow_two' 0
  simpa using h

theorem map_bit_encodeNat (n : ℕ) : (encodeNat n).map Sym.bit = natSyms n := rfl

theorem loopCost_le_of_lt (B : ℕ → ℕ) (c : ℕ) : ∀ N, (∀ n, n < N → B n ≤ c) →
    loopCost B N ≤ N * (c + 1) + 1
  | 0, _ => by simp [loopCost]
  | N + 1, h => by
    have ih := loopCost_le_of_lt B c N (fun n hn => h n (by omega))
    have := h N (by omega)
    simp only [loopCost]
    rw [Nat.add_one_mul]
    omega

theorem runs_cLoop (c : SK) (hc : c ≠ kTQ) (body : AProg SK) (B : ℕ → SK → List Sym)
    (rc : List Sym) (hrc : TermOK rc) (N : ℕ) (T : ℕ → ℕ)
    (hB : ∀ n, n ≤ N → B n c = natSyms n ++ rc)
    (hstep : ∀ n, n < N → Runs body (B (n + 1))
      (Function.update (B n) c (natSyms (n + 1) ++ rc)) (fun _ => True) (T n)) :
    Runs (cLoop c body) (B N) (B 0) (fun _ => True)
      (1 + loopCost (fun n => T n + (6 * bitLen (n + 1) + 8 + 1)) N) := by
  have h0 : Runs (peekO c) (B N) (B N) (fun v => isBitO v.o = decide (0 < N)) 1 :=
    runs_mono (runs_peekO c (B N))
      (fun v hv => by rw [hv, hB N le_rfl, isBitO_natSyms_head N rc hrc]) le_rfl
  have hs : ∀ n, n < N → Runs (.seq body (.seq (Lo (TMFw.Lib.dec c kTQ)) (peekO c)))
      (B (n + 1)) (B n) (fun v => isBitO v.o = decide (0 < n))
      (T n + (6 * bitLen (n + 1) + 8 + 1)) := fun n hn =>
    runs_seq (hstep n hn) (runs_seq (runs_decC c hc n rc hrc (B n) (hB n (by omega)))
      (runs_mono (runs_peekO c (B n))
        (fun v hv => by rw [hv, hB n (by omega), isBitO_natSyms_head n rc hrc]) le_rfl))
  have h0' : Calculus.RunsIn [] (peekO c) (B N) (B N)
      (fun v => isBitO v.o = decide (0 < N)) 1 := h0
  have hs' : ∀ n, n < N → Calculus.RunsIn [] (.seq body (.seq (Lo (TMFw.Lib.dec c kTQ))
      (peekO c))) (B (n + 1)) (B n) (fun v => isBitO v.o = decide (0 < n))
      (T n + (6 * bitLen (n + 1) + 8 + 1)) := hs
  have h : Calculus.RunsIn [] (.seq (peekO c) (.loop (fun v => isBitO v.o)
      (.seq body (.seq (Lo (TMFw.Lib.dec c kTQ)) (peekO c))))) (B N) (B 0)
      (fun v => isBitO v.o = false)
      (1 + loopCost (fun n => T n + (6 * bitLen (n + 1) + 8 + 1)) N) :=
    Calculus.RunsIn.seq_loop h0' hs'
  have h' : Runs (cLoop c body) (B N) (B 0) (fun v => isBitO v.o = false)
      (1 + loopCost (fun n => T n + (6 * bitLen (n + 1) + 8 + 1)) N) := h
  exact runs_mono h' (fun _ _ => trivial) le_rfl

/-! ## Fetching a header field -/

theorem runs_skipFieldsN {src dst : SK} (hne : src ≠ dst) (fs : List ℕ) (n : ℕ)
    (hn : fs.length = n) (L : List Sym) (S : SK → List Sym) (hS : S src = hdrSyms fs ++ L) :
    Runs (Lo (BridgePP.skipFields src dst n)) S
      (Function.update (Function.update S src L) dst ((hdrSyms fs).reverse ++ S dst))
      (fun _ => True) (6 * (hdrSyms fs).length + 1) := by
  subst hn; exact runs_Lo (BridgePP.runs_skipFields hne fs L S hS)

/-- Copy header field `k` onto `dst` (guard `sep2` on `kH`; `sPar` restored). -/
def fetchF (k : ℕ) (dst : SK) : AProg SK :=
  .seq (Lo (TMFw.Lib.pushC kH .sep2)) (.seq (Lo (BridgePP.skipFields sPar kH k))
    (.seq (Lo (TMFw.Lib.copyBlock sPar dst kTP)) (Lo (WP.W9comp.rewindTo kH sPar .sep2))))

theorem runs_fetchF (fs : List ℕ) (k : ℕ) (hk : k < fs.length) (dst : SK) (hd1 : dst ≠ sPar)
    (hd2 : dst ≠ kH) (hd3 : dst ≠ kTP) (rpar : List Sym) (S : SK → List Sym)
    (hP : S sPar = hdrSyms fs ++ rpar) (hH : S kH = []) :
    Runs (fetchF k dst) S (Function.update S dst (natSyms fs[k] ++ S dst)) (fun _ => True)
      (10 * (hdrSyms fs).length + 11) := by
  have hlen : (fs.take k).length = k := by simp; omega
  have hsp : sPar ≠ kH := by decide
  refine runs_mono (runs_congr (runs_seq (runs_Lo (BridgePP.runs_pushC kH Sym.sep2 S))
    (runs_seq (runs_skipFieldsN hsp (fs.take k) k hlen (hdrSyms (fs.drop k) ++ rpar) _ ?h1)
    (runs_seq (runs_Lo (BridgePP.runs_copyBlock (src := sPar) (dst := dst) (tmp := kTP)
      hd1.symm (by decide) hd3 (encodeNat fs[k]) (Sym.mark :: (hdrSyms (fs.drop (k + 1)) ++ rpar))
      _ (BridgePP.termOK_mark_cons _) ?h2))
    (runs_Lo (BridgePP.runs_rewindTo (src := kH) (dst := sPar) hsp.symm Sym.sep2
      ((hdrSyms (fs.take k)).reverse) [] _ ?h3 ?h4))))) ?he) (fun _ _ => trivial) ?hc
  case h1 => rw [Function.update_of_ne hsp, hP, hdrSyms_split fs k, List.append_assoc]
  case h2 =>
    rw [Function.update_of_ne hsp, Function.update_self, hdrSyms_drop' fs k hk]
    simp [natSyms]
  case h3 => simpa using BridgePP.sep2_not_mem_hdrSyms (fs.take k)
  case h4 =>
    rw [Function.update_of_ne hd2.symm, Function.update_self, Function.update_self, hH]
  case he =>
    funext x
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [natSyms, hdrSyms_split fs k]
  case hc =>
    have := length_hdrSyms_le fs k hk
    simp only [List.length_reverse]
    unfold bitLen at this
    omega

/-! ## Header fields -/

theorem hdr_length (b : BrPar) : b.hdr.length = 9 + b.d := by
  simp [BrPar.hdr]; omega

theorem hdr_get8 (b : BrPar) (h : 8 < b.hdr.length) : b.hdr[8] = b.d := by
  simp [BrPar.hdr]

theorem hdr_get4 (b : BrPar) (h : 4 < b.hdr.length) : b.hdr[4] = b.wT := by
  simp [BrPar.hdr]

theorem hdr_getT (b : BrPar) (l : Fin b.d) (h : 9 + (l : ℕ) < b.hdr.length) :
    b.hdr[9 + (l : ℕ)] = b.t l := by
  simp only [BrPar.hdr, List.getElem_append, List.length_cons, List.length_nil]
  simp

theorem blMono {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat, IntMulTM.length_encodeNat]
  exact Nat.size_le_size h

theorem length_le_hdrSyms (fs : List ℕ) : fs.length ≤ (hdrSyms fs).length := by
  induction fs with
  | nil => simp
  | cons a fs ih => rw [BridgePP.length_hdrSyms_cons]; simp; omega

theorem bitLen_field_le (fs : List ℕ) (k : ℕ) (hk : k < fs.length) :
    bitLen fs[k] ≤ (hdrSyms fs).length := by
  have := length_hdrSyms_le fs k hk; omega

/-! ## Phase A: `i = d - m` -/

/-- Counters: `kCX := natSyms (i - 1)`, `kCD := natSyms m`, `kZB := natSyms i`. -/
def phaseA : AProg SK :=
  .seq (fetchF 8 kCX) (.seq (Lo (TMFw.Lib.copyBlock sAx kCC kTP))
    (.seq (Lo (TMFw.Lib.copyBlock sAx kCD kTP)) (.seq (cLoop kCC (Lo (TMFw.Lib.dec kCX kTQ)))
    (.seq (Lo (TMFw.Lib.copyBlock kCX kZB kTP)) (Lo (TMFw.Lib.dec kCX kTQ))))))

/-- The state family of the subtraction loop. -/
def subB (S : SK → List Sym) (i : ℕ) (n : ℕ) : SK → List Sym :=
  Function.update (Function.update S kCC (natSyms n)) kCX (natSyms (i + n))

theorem runs_phaseA (b : BrPar) (m : ℕ) (i : Fin b.d) (hi : (i : ℕ) ≠ 0)
    (him : (i : ℕ) + m = b.d) (rpar rax : List Sym) (hrax : TermOK rax) (S : SK → List Sym)
    (hP : S sPar = hdrSyms b.hdr ++ rpar) (hA : S sAx = natSyms m ++ rax)
    (hE : ∀ e : Fin 25, S (.inr e) = []) :
    Runs phaseA S (Function.update (Function.update (Function.update S kCX
      (natSyms ((i : ℕ) - 1))) kCD (natSyms m)) kZB (natSyms i)) (fun _ => True)
      (60 * ((hdrSyms b.hdr).length + 1) ^ 2) := by
  have hlen := hdr_length b
  have h8 : 8 < b.hdr.length := by omega
  have hH := length_le_hdrSyms b.hdr
  have hbd : bitLen b.d ≤ (hdrSyms b.hdr).length := by
    have := bitLen_field_le b.hdr 8 h8; rwa [hdr_get8] at this
  have hbm : bitLen m ≤ (hdrSyms b.hdr).length :=
    (blMono (show m ≤ b.d by omega)).trans hbd
  have hbi : bitLen (i : ℕ) ≤ (hdrSyms b.hdr).length :=
    (blMono (show (i : ℕ) ≤ b.d by omega)).trans hbd
  -- the loop
  have hloop := runs_cLoop kCC (by decide) (Lo (TMFw.Lib.dec kCX kTQ))
    (subB (Function.update (Function.update (Function.update S kCX (natSyms b.d ++ []))
      kCC (natSyms m ++ [])) kCD (natSyms m ++ [])) i) [] TermOK.nil m
    (fun n => 6 * bitLen ((i : ℕ) + n + 1) + 8)
    (fun n _ => by simp [subB])
    (fun n hn => by
      have e : subB (Function.update (Function.update (Function.update S kCX (natSyms b.d ++ []))
          kCC (natSyms m ++ [])) kCD (natSyms m ++ [])) i (n + 1) =
          Function.update (Function.update (subB (Function.update (Function.update
            (Function.update S kCX (natSyms b.d ++ [])) kCC (natSyms m ++ [])) kCD
            (natSyms m ++ [])) i n) kCC (natSyms (n + 1) ++ [])) kCX
            (natSyms ((i : ℕ) + n + 1) ++ []) := by
        funext x
        simp only [subB, Function.update_apply]
        split_ifs <;> simp_all [Nat.add_assoc]
      rw [e]
      exact runs_decC kCX (by decide) ((i : ℕ) + n) [] TermOK.nil _ (by
        simp [subB, Function.update_apply]))
  have hi1 : (i : ℕ) - 1 + 1 = (i : ℕ) := by omega
  refine runs_mono (runs_congr (runs_seq (runs_congr
      (S'' := Function.update S kCX (natSyms b.d ++ [])) (runs_fetchF b.hdr 8 h8 kCX (by decide)
      (by decide) (by decide) rpar S hP (hE 0)) ?e1)
    (runs_seq (runs_Lo (BridgePP.runs_copyBlock (src := sAx) (dst := kCC) (tmp := kTP)
      (by decide) (by decide) (by decide) (encodeNat m) rax _ hrax ?h2))
    (runs_seq (runs_congr (S'' := subB (Function.update (Function.update (Function.update S kCX
      (natSyms b.d ++ [])) kCC (natSyms m ++ [])) kCD (natSyms m ++ [])) i m)
      (runs_Lo (BridgePP.runs_copyBlock (src := sAx) (dst := kCD)
      (tmp := kTP) (by decide) (by decide) (by decide) (encodeNat m) rax _ hrax ?h3)) ?e3)
    (runs_seq hloop
    (runs_seq (runs_Lo (BridgePP.runs_copyBlock (src := kCX) (dst := kZB) (tmp := kTP)
      (by decide) (by decide) (by decide) (encodeNat i) [] _ TermOK.nil ?h5))
    (runs_decC' kCX (by decide) ((i : ℕ) - 1) [] TermOK.nil _ ?h6)))))) ?he)
    (fun _ _ => trivial) ?hc
  case e1 => rw [hdr_get8, hE 7]
  case h2 => simp [Function.update_apply, hA, natSyms]
  case h3 => simp [Function.update_apply, hA, natSyms]
  case e3 =>
    funext x
    simp only [subB, Function.update_apply]
    split_ifs <;> simp_all [natSyms]
  case h5 => simp [subB, natSyms]
  case h6 => simp [subB, hi1]
  case he =>
    funext x
    simp only [subB, Function.update_apply]
    split_ifs <;> simp_all [natSyms_zero'', map_bit_encodeNat]
  case hc =>
    have hl := loopCost_le_of_lt (fun n => 6 * bitLen ((i : ℕ) + n + 1) + 8 +
      (6 * bitLen (n + 1) + 8 + 1)) (12 * (hdrSyms b.hdr).length + 17) m (fun n hn => by
        have h1 := blMono (show (i : ℕ) + n + 1 ≤ b.d by omega)
        have h2 := blMono (show n + 1 ≤ m by omega)
        omega)
    have hmH : m ≤ (hdrSyms b.hdr).length := by omega
    have hm2 := Nat.mul_le_mul_right (12 * (hdrSyms b.hdr).length + 17 + 1) hmH
    have e1 : ((hdrSyms b.hdr).length + 1) ^ 2 = (hdrSyms b.hdr).length * (hdrSyms b.hdr).length +
        2 * (hdrSyms b.hdr).length + 1 := by ring
    have e2 : (hdrSyms b.hdr).length * (12 * (hdrSyms b.hdr).length + 17 + 1) =
        12 * ((hdrSyms b.hdr).length * (hdrSyms b.hdr).length) + 18 * (hdrSyms b.hdr).length := by
      ring
    have hb := bitLen_field_le b.hdr 8 h8
    rw [hdr_get8] at hb
    rw [hi1]
    unfold bitLen at hbm hbi hb hl ⊢
    omega

/-! ## Header walks -/

/-- Walk state: the fields `0..p-1` of the header skipped onto the guard stack `kH`. -/
def walkV (X : SK → List Sym) (fs : List ℕ) (rpar : List Sym) (p : ℕ) : SK → List Sym :=
  Function.update (Function.update X sPar (hdrSyms (fs.drop p) ++ rpar)) kH
    ((hdrSyms (fs.take p)).reverse ++ [Sym.sep2])

theorem runs_skipWalk (X : SK → List Sym) (fs : List ℕ) (rpar : List Sym) (p : ℕ)
    (hp : p < fs.length) :
    Runs (Lo (BridgePP.skipField sPar kH)) (walkV X fs rpar p) (walkV X fs rpar (p + 1))
      (fun _ => True) (3 * bitLen fs[p] + 6) := by
  have h := runs_Lo (BridgePP.runs_skipField (src := sPar) (dst := kH) (by decide) fs[p]
    (hdrSyms (fs.drop (p + 1)) ++ rpar) (walkV X fs rpar p)
    (by simp [walkV, Function.update_apply, hdrSyms_drop' fs p hp]))
  refine runs_congr h ?_
  funext x
  simp only [walkV, Function.update_apply]
  split_ifs <;> simp_all [hdrSyms_take_succ' fs p hp]

theorem runs_walkStart (X : SK → List Sym) (fs : List ℕ) (rpar : List Sym) (k : ℕ)
    (hk : k ≤ fs.length) (hP : X sPar = hdrSyms fs ++ rpar) (hH : X kH = []) :
    Runs (.seq (Lo (TMFw.Lib.pushC kH .sep2)) (Lo (BridgePP.skipFields sPar kH k))) X
      (walkV X fs rpar k) (fun _ => True) (1 + (6 * (hdrSyms (fs.take k)).length + 1)) := by
  have hlen : (fs.take k).length = k := by simp; omega
  refine runs_congr (runs_seq (runs_Lo (BridgePP.runs_pushC kH Sym.sep2 X))
    (runs_skipFieldsN (by decide) (fs.take k) k hlen (hdrSyms (fs.drop k) ++ rpar) _ ?h1)) ?he
  case h1 => rw [Function.update_of_ne (by decide), hP, hdrSyms_split fs k, List.append_assoc]
  case he =>
    funext x
    simp only [walkV, Function.update_apply]
    split_ifs <;> simp_all

theorem runs_walkEnd (X : SK → List Sym) (fs : List ℕ) (rpar : List Sym) (p : ℕ)
    (hP : X sPar = hdrSyms fs ++ rpar) (hH : X kH = []) :
    Runs (Lo (WP.W9comp.rewindTo kH sPar .sep2)) (walkV X fs rpar p) X (fun _ => True)
      (3 * (hdrSyms (fs.take p)).length + 2) := by
  have h := runs_Lo (BridgePP.runs_rewindTo (src := kH) (dst := sPar) (by decide) Sym.sep2
    ((hdrSyms (fs.take p)).reverse) [] (walkV X fs rpar p)
    (by simpa using BridgePP.sep2_not_mem_hdrSyms (fs.take p)) (by simp [walkV]))
  rw [List.length_reverse] at h
  refine runs_congr h ?_
  funext x
  simp only [walkV, Function.update_apply]
  split_ifs <;> simp_all [hdrSyms_split fs p]

/-- The walk from field `9` to field `9 + i` (`kZB` counts down). -/
theorem runs_skipLoop (X : SK → List Sym) (fs : List ℕ) (rpar : List Sym) (i : ℕ)
    (hi : 9 + i ≤ fs.length) :
    Runs (cLoop kZB (Lo (BridgePP.skipField sPar kH)))
      (walkV (Function.update X kZB (natSyms i)) fs rpar 9)
      (walkV (Function.update X kZB []) fs rpar (9 + i)) (fun _ => True)
      (1 + loopCost (fun n => 3 * (hdrSyms fs).length + 6 + (6 * bitLen (n + 1) + 8 + 1)) i) := by
  have h := runs_cLoop kZB (by decide) (Lo (BridgePP.skipField sPar kH))
    (fun n => walkV (Function.update X kZB (natSyms n)) fs rpar (9 + (i - n))) [] TermOK.nil i
    (fun _ => 3 * (hdrSyms fs).length + 6)
    (fun n _ => by simp [walkV, Function.update_apply])
    (fun n hn => by
      have hp : 9 + (i - (n + 1)) < fs.length := by omega
      have h1 := runs_skipWalk (Function.update X kZB (natSyms (n + 1))) fs rpar
        (9 + (i - (n + 1))) hp
      have hb := bitLen_field_le fs (9 + (i - (n + 1))) hp
      refine runs_mono (runs_congr h1 ?_) (fun _ _ => trivial) (by omega)
      rw [show 9 + (i - (n + 1)) + 1 = 9 + (i - n) by omega]
      funext x
      simp only [walkV, Function.update_apply]
      split_ifs <;> simp_all)
  simp only [Nat.sub_self, Nat.add_zero, Nat.sub_zero, natSyms_zero''] at h
  exact h

/-! ## The suffix product -/

/-- `t_l` as a function of `l : ℕ` (`1` out of range). -/
def fT (b : BrPar) (l : ℕ) : ℕ := if h : l < b.d then b.t ⟨l, h⟩ else 1

/-- Exponent sum `∑_{k<j} log₂ t_{i+1+k}`. -/
def sufE (b : BrPar) (i j : ℕ) : ℕ := ∑ k ∈ Finset.range j, Nat.log2 (fT b (i + 1 + k))

theorem fT_pow (b : BrPar) (hshape : ShapeOK b.t) (l : ℕ) (hl : l < b.d) :
    fT b l = 2 ^ Nat.log2 (fT b l) := by
  obtain ⟨-, a, ha⟩ := hshape ⟨l, hl⟩
  simp only [fT, dif_pos hl, ha, Nat.log2_two_pow]

theorem hdr_getT' (b : BrPar) (l : ℕ) (hl : l < b.d) (h : 9 + l < b.hdr.length) :
    b.hdr[9 + l] = fT b l := by
  simp only [fT, dif_pos hl]
  exact hdr_getT b ⟨l, hl⟩ h

theorem suffixProd_eq_sufE (b : BrPar) (hshape : ShapeOK b.t) (i : Fin b.d) :
    suffixProd b.t i = 2 ^ sufE b i (b.d - ((i : ℕ) + 1)) := by
  have h1 : suffixProd b.t i = ∏ j ∈ Finset.Ico ((i : ℕ) + 1) b.d, fT b j := by
    unfold suffixProd
    refine Finset.prod_bij' (fun l _ => (l : ℕ)) (fun j hj => ⟨j, (Finset.mem_Ico.1 hj).2⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp only [Finset.mem_Ico]
      exact ⟨hl, l.isLt⟩
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show (i : ℕ) < j
      omega
    · intro l _; rfl
    · intro j _; rfl
    · intro l _
      simp [fT, l.isLt]
  rw [h1, Finset.prod_Ico_eq_prod_range]
  unfold sufE
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  exact fT_pow b hshape _ (by omega)

/-- Body of the suffix loop: copy `t_l`, fold its zeros into `kCU`, skip the field. -/
def sufBody : AProg SK :=
  .seq (Lo (TMFw.Lib.copyBlock sPar kY0 kTP)) (.seq (Lo (TMFw.Lib.moveBlock kY0 kCU))
    (.seq (drop1 kCU) (Lo (BridgePP.skipField sPar kH))))

theorem runs_drop1 (k : SK) (y : Sym) (L : List Sym) (S : SK → List Sym) (h : S k = y :: L) :
    Runs (drop1 k) S (Function.update S k L) (fun _ => True) 1 :=
  runsA_of_eval fun v => ⟨v, 1, eval_drop1 k v S y L h, le_refl _⟩

theorem runs_pushS (k : SK) (y : Sym) (S : SK → List Sym) :
    Runs (pushS k y) S (Function.update S k (y :: S k)) (fun _ => True) 1 :=
  runsA_of_eval fun v => ⟨v, 1, eval_pushS k y v S, le_refl _⟩

theorem runs_sufBody (b : BrPar) (hshape : ShapeOK b.t) (X : SK → List Sym) (rpar : List Sym)
    (i j : ℕ) (hj : i + 1 + j < b.d) (hW : X kY0 = []) :
    Runs sufBody
      (walkV (Function.update X kCU (natSyms (2 ^ sufE b i j))) b.hdr rpar (9 + (i + 1 + j)))
      (walkV (Function.update X kCU (natSyms (2 ^ sufE b i (j + 1)))) b.hdr rpar
        (9 + (i + 1 + (j + 1))))
      (fun _ => True) (13 * (hdrSyms b.hdr).length + 18) := by
  have hlen := hdr_length b
  have hp : 9 + (i + 1 + j) < b.hdr.length := by omega
  have hf : b.hdr[9 + (i + 1 + j)] = fT b (i + 1 + j) := hdr_getT' b (i + 1 + j) hj hp
  obtain ⟨-, a, ha⟩ := hshape ⟨i + 1 + j, hj⟩
  have hfa : fT b (i + 1 + j) = 2 ^ a := by simp only [fT, dif_pos hj, ha]
  have hla : Nat.log2 (fT b (i + 1 + j)) = a := by rw [hfa, Nat.log2_two_pow]
  have hsuc : sufE b i (j + 1) = sufE b i j + a := by
    simp only [sufE, Finset.sum_range_succ, hla]
  have henc : encodeNat b.hdr[9 + (i + 1 + j)] = List.replicate a false ++ [true] := by
    rw [hf, hfa, encodeNat_pow_two']
  have hcu : List.replicate a (Sym.bit false) ++ natSyms (2 ^ sufE b i j) =
      natSyms (2 ^ sufE b i (j + 1)) := by
    rw [hsuc, natSyms_pow_two', natSyms_pow_two', ← List.append_assoc, ← List.replicate_add,
      Nat.add_comm]
  have hb := bitLen_field_le b.hdr (9 + (i + 1 + j)) hp
  refine runs_mono (runs_congr (runs_seq
    (runs_Lo (BridgePP.runs_copyBlock (src := sPar) (dst := kY0) (tmp := kTP) (by decide)
      (by decide) (by decide) (encodeNat b.hdr[9 + (i + 1 + j)])
      (Sym.mark :: (hdrSyms (b.hdr.drop (9 + (i + 1 + j) + 1)) ++ rpar)) _
      (BridgePP.termOK_mark_cons _) ?h1))
    (runs_seq (runs_Lo (BridgePP.runs_moveBlock (src := kY0) (dst := kCU) (by decide)
      (encodeNat b.hdr[9 + (i + 1 + j)]) [] _ TermOK.nil ?h2))
    (runs_seq (runs_congr (S'' := walkV (Function.update X kCU (natSyms (2 ^ sufE b i (j + 1))))
      b.hdr rpar (9 + (i + 1 + j)))
      (runs_drop1 kCU (Sym.bit true) (List.replicate a (Sym.bit false) ++ natSyms (2 ^ sufE b i j))
        _ ?h3) ?e3)
      (runs_skipWalk (Function.update X kCU (natSyms (2 ^ sufE b i (j + 1)))) b.hdr rpar
        (9 + (i + 1 + j)) hp)))) ?he) (fun _ _ => trivial) ?hc
  case h1 =>
    simp [walkV, Function.update_apply, hdrSyms_drop' b.hdr (9 + (i + 1 + j)) hp, natSyms]
  case h2 => simp [walkV, Function.update_apply, hW]
  case h3 =>
    simp [walkV, Function.update_apply, henc, List.reverse_replicate, List.map_replicate]
  case e3 =>
    funext x
    simp only [walkV, Function.update_apply]
    split_ifs <;> simp_all
  case he => rw [show 9 + (i + 1 + j) + 1 = 9 + (i + 1 + (j + 1)) by omega]
  case hc =>
    unfold bitLen at hb ⊢
    omega

theorem runs_sufLoop (b : BrPar) (hshape : ShapeOK b.t) (X : SK → List Sym) (rpar : List Sym)
    (i M1 : ℕ) (hM : i + 1 + M1 = b.d) (hW : X kY0 = []) :
    Runs (cLoop kCD sufBody)
      (walkV (Function.update (Function.update X kCD (natSyms M1)) kCU
        (natSyms (2 ^ sufE b i 0))) b.hdr rpar (9 + (i + 1)))
      (walkV (Function.update (Function.update X kCD []) kCU (natSyms (2 ^ sufE b i M1)))
        b.hdr rpar (9 + (i + 1 + M1)))
      (fun _ => True)
      (1 + loopCost (fun n => 13 * (hdrSyms b.hdr).length + 18 + (6 * bitLen (n + 1) + 8 + 1))
        M1) := by
  have h := runs_cLoop kCD (by decide) sufBody
    (fun n => walkV (Function.update (Function.update X kCD (natSyms n)) kCU
      (natSyms (2 ^ sufE b i (M1 - n)))) b.hdr rpar (9 + (i + 1 + (M1 - n)))) [] TermOK.nil M1
    (fun _ => 13 * (hdrSyms b.hdr).length + 18)
    (fun n _ => by simp [walkV, Function.update_apply])
    (fun n hn => by
      have h1 := runs_sufBody b hshape (Function.update X kCD (natSyms (n + 1))) rpar i
        (M1 - (n + 1)) (by omega) (by simp [Function.update_apply, hW])
      refine runs_congr h1 ?_
      rw [show M1 - (n + 1) + 1 = M1 - n by omega]
      funext x
      simp only [walkV, Function.update_apply]
      split_ifs <;> simp_all)
  simp only [Nat.sub_self, Nat.sub_zero, Nat.add_zero, natSyms_zero''] at h
  exact h

/-! ## Phase B: the walk to `t_i` and the suffix product -/

/-- Walk to `t_i`, `kCT := t_i / 2`, the suffix product into `kCU`; `sPar` restored. -/
def phaseB : AProg SK :=
  .seq (.seq (Lo (TMFw.Lib.pushC kH .sep2)) (Lo (BridgePP.skipFields sPar kH 9)))
  (.seq (cLoop kZB (Lo (BridgePP.skipField sPar kH)))
  (.seq (Lo (TMFw.Lib.copyBlock sPar kCT kTP)) (.seq (drop1 kCT)
  (.seq (Lo (BridgePP.skipField sPar kH)) (.seq (pushS kCU (.bit true))
  (.seq (Lo (TMFw.Lib.dec kCD kTQ)) (.seq (cLoop kCD sufBody)
  (Lo (WP.W9comp.rewindTo kH sPar .sep2)))))))))

theorem runs_phaseB (b : BrPar) (m : ℕ) (i : Fin b.d) (hshape : ShapeOK b.t)
    (him : (i : ℕ) + m = b.d) (rpar : List Sym) (X : SK → List Sym)
    (hP : X sPar = hdrSyms b.hdr ++ rpar) (hH : X kH = []) (hW : X kY0 = []) (hCT : X kCT = [])
    (hCU : X kCU = []) :
    Runs phaseB (Function.update (Function.update X kCD (natSyms m)) kZB (natSyms i))
      (Function.update (Function.update (Function.update (Function.update X kCD []) kZB [])
        kCT (natSyms (b.t i / 2))) kCU (natSyms (suffixProd b.t i)))
      (fun _ => True) (100 * ((hdrSyms b.hdr).length + 1) ^ 2) := by
  have hlen := hdr_length b
  have hH0 := length_le_hdrSyms b.hdr
  have hm1 : 1 ≤ m := by have := i.isLt; omega
  have hp : 9 + (i : ℕ) < b.hdr.length := by have := i.isLt; omega
  have hf : b.hdr[9 + (i : ℕ)] = fT b i := hdr_getT' b i i.isLt hp
  obtain ⟨ht2, a, ha⟩ := hshape i
  have ha1 : 1 ≤ a := by
    rcases a with _ | a
    · simp at ha; omega
    · omega
  have hfa : fT b i = 2 ^ a := by simp only [fT, dif_pos i.isLt, Fin.eta, ha]
  have hhalf : b.t i / 2 = 2 ^ (a - 1) := by
    rw [ha, show a = a - 1 + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    simp
  have henc : encodeNat b.hdr[9 + (i : ℕ)] = false :: (List.replicate (a - 1) false ++ [true]) := by
    rw [hf, hfa, encodeNat_pow_two', show a = a - 1 + 1 by omega, List.replicate_succ]
    simp
  have hsuf : suffixProd b.t i = 2 ^ sufE b i (m - 1) := by
    rw [suffixProd_eq_sufE b hshape i, show b.d - ((i : ℕ) + 1) = m - 1 by omega]
  have hs0 : sufE b i 0 = 0 := by simp [sufE]
  have hb := bitLen_field_le b.hdr (9 + (i : ℕ)) hp
  have htk : ∀ k, (hdrSyms (b.hdr.take k)).length ≤ (hdrSyms b.hdr).length := fun k => by
    have := congrArg List.length (hdrSyms_split b.hdr k)
    simp only [List.length_append] at this
    omega
  refine runs_mono (runs_congr (runs_seq
    (runs_walkStart _ b.hdr rpar 9 (by omega) (by simp [Function.update_apply, hP])
      (by simp [Function.update_apply, hH]))
    (runs_seq (runs_skipLoop (Function.update X kCD (natSyms m)) b.hdr rpar i (by omega))
    (runs_seq (runs_Lo (BridgePP.runs_copyBlock (src := sPar) (dst := kCT) (tmp := kTP)
      (by decide) (by decide) (by decide) (encodeNat b.hdr[9 + (i : ℕ)])
      (Sym.mark :: (hdrSyms (b.hdr.drop (9 + (i : ℕ) + 1)) ++ rpar)) _
      (BridgePP.termOK_mark_cons _) ?h3))
    (runs_seq (runs_congr (S'' := walkV (Function.update (Function.update (Function.update X kCD
        (natSyms m)) kZB []) kCT (natSyms (b.t i / 2))) b.hdr rpar (9 + (i : ℕ)))
      (runs_drop1 kCT (Sym.bit false) (natSyms (b.t i / 2)) _ ?h4) ?e5)
    (runs_seq (runs_congr (S'' := walkV (Function.update (Function.update (Function.update X kCD
        (natSyms m)) kZB []) kCT (natSyms (b.t i / 2))) b.hdr rpar (9 + ((i : ℕ) + 1)))
      (runs_skipWalk _ b.hdr rpar (9 + (i : ℕ)) hp) (by rw [Nat.add_assoc]))
    (runs_seq (runs_congr (S'' := walkV (Function.update (Function.update (Function.update
        (Function.update X kCD (natSyms m)) kZB []) kCT (natSyms (b.t i / 2))) kCU [Sym.bit true])
        b.hdr rpar (9 + ((i : ℕ) + 1)))
      (runs_pushS kCU (Sym.bit true) _) ?e7)
    (runs_seq (runs_congr (S'' := walkV (Function.update (Function.update (Function.update
        (Function.update (Function.update X kCD (natSyms m)) kZB []) kCT (natSyms (b.t i / 2)))
        kCD (natSyms (m - 1))) kCU (natSyms (2 ^ sufE b i 0))) b.hdr rpar (9 + ((i : ℕ) + 1)))
      (runs_decC' kCD (by decide) (m - 1) [] TermOK.nil _ ?h8) ?e8)
    (runs_seq (runs_sufLoop b hshape _ rpar i (m - 1) (by omega)
      (by simp [Function.update_apply, hW]))
    (runs_walkEnd _ b.hdr rpar _ (by simp [Function.update_apply, hP])
      (by simp [Function.update_apply, hH])))))))))) ?he) (fun _ _ => trivial) ?hc
  case h3 => simp [walkV, Function.update_apply, hdrSyms_drop' b.hdr (9 + (i : ℕ)) hp, natSyms]
  case h4 =>
    simp only [walkV, Function.update_apply]
    simp [henc, hCT, hhalf, natSyms_pow_two', List.map_replicate]
  case e5 =>
    funext x
    simp only [walkV, Function.update_apply]
    split_ifs <;> simp_all
  case e7 =>
    funext x
    simp only [walkV, Function.update_apply]
    split_ifs <;> simp_all
  case h8 =>
    simp only [walkV, Function.update_apply]
    simp [show m - 1 + 1 = m by omega]
  case e8 =>
    funext x
    simp only [walkV, Function.update_apply]
    split_ifs <;> simp_all [hs0, natSyms_one']
  case he =>
    funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  case hc =>
    have l1 := loopCost_le_of_lt (fun n => 3 * (hdrSyms b.hdr).length + 6 +
      (6 * bitLen (n + 1) + 8 + 1)) (9 * (hdrSyms b.hdr).length + 15) (i : ℕ) (fun n hn => by
        have := blMono (show n + 1 ≤ b.d by omega)
        have := bitLen_field_le b.hdr 8 (by omega)
        rw [hdr_get8] at this
        omega)
    have l2 := loopCost_le_of_lt (fun n => 13 * (hdrSyms b.hdr).length + 18 +
      (6 * bitLen (n + 1) + 8 + 1)) (19 * (hdrSyms b.hdr).length + 27) (m - 1) (fun n hn => by
        have := blMono (show n + 1 ≤ b.d by omega)
        have := bitLen_field_le b.hdr 8 (by omega)
        rw [hdr_get8] at this
        omega)
    have hbm := blMono (show m - 1 + 1 ≤ b.d by omega)
    have hbd := bitLen_field_le b.hdr 8 (by omega)
    rw [hdr_get8] at hbd
    have t1 := htk 9
    have t2 := htk (9 + ((i : ℕ) + 1 + (m - 1)))
    have hdH : b.d ≤ (hdrSyms b.hdr).length := by omega
    have q1 : (i : ℕ) * (9 * (hdrSyms b.hdr).length + 15 + 1) ≤
        (i : ℕ) * (19 * (hdrSyms b.hdr).length + 27 + 1) := Nat.mul_le_mul_left _ (by omega)
    have q2 : ((i : ℕ) + (m - 1)) * (19 * (hdrSyms b.hdr).length + 27 + 1) ≤
        (hdrSyms b.hdr).length * (19 * (hdrSyms b.hdr).length + 27 + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have q3 : ((i : ℕ) + (m - 1)) * (19 * (hdrSyms b.hdr).length + 27 + 1) =
        (i : ℕ) * (19 * (hdrSyms b.hdr).length + 27 + 1) +
        (m - 1) * (19 * (hdrSyms b.hdr).length + 27 + 1) := by ring
    have q4 : (hdrSyms b.hdr).length * (19 * (hdrSyms b.hdr).length + 27 + 1) =
        19 * ((hdrSyms b.hdr).length * (hdrSyms b.hdr).length) + 28 * (hdrSyms b.hdr).length := by
      ring
    have e1 : ((hdrSyms b.hdr).length + 1) ^ 2 = (hdrSyms b.hdr).length * (hdrSyms b.hdr).length +
        2 * (hdrSyms b.hdr).length + 1 := by ring
    unfold bitLen at hb hbm hbd l1 l2 ⊢
    omega

/-! ## Phase C: the rulers -/

/-- One ruler step: a `false` bit on each of `kRU` and `kRX`. -/
def rulBody : AProg SK := .seq (pushS kRU (.bit false)) (pushS kRX (.bit false))

theorem rulLoop_eval {R X : SK} (hRX : R ≠ X) (hR1 : R ≠ kRU) (hR2 : R ≠ kRX) (hX1 : X ≠ kRU)
    (hX2 : X ≠ kRX) :
    ∀ (n : ℕ) (DR : List Sym) (v : AReg) (S : SK → List Sym), DR.head? ≠ some .mark →
      S R = List.replicate n .mark ++ DR → v.r = (List.replicate n Sym.mark ++ DR).head? →
      Eval [] (walkLoop R X rulBody) ⟨v, S⟩
        ⟨{ v with r := DR.head? }, Function.update (Function.update (Function.update
          (Function.update S R DR) X (List.replicate n .mark ++ S X)) kRU
          (List.replicate n (.bit false) ++ S kRU)) kRX (List.replicate n (.bit false) ++ S kRX)⟩
        (6 * n + 1)
  | 0, DR, v, S, hD, hR, hv => by
    simp only [List.replicate_zero, List.nil_append] at hR hv ⊢
    refine (Eval.loop_false (by rw [hv]; exact isMarkO_false_of_ne hD)).of_eq ?_ rfl
    rw [← hv, ← hR, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self,
      Function.update_eq_self]
  | n + 1, DR, v, S, hD, hR, hv => by
    set S1 := Function.update (Function.update S R (List.replicate n .mark ++ DR)) X
      (.mark :: S X) with hS1
    have eb1 := eval_pushS kRU (.bit false) v S1
    have eb2 := eval_pushS kRX (.bit false) v (Function.update S1 kRU (.bit false :: S1 kRU))
    have eb : Eval [] rulBody ⟨v, S1⟩ ⟨v, Function.update (Function.update S1 kRU
        (.bit false :: S1 kRU)) kRX (.bit false :: (Function.update S1 kRU
        (.bit false :: S1 kRU)) kRX)⟩ 2 := Eval.seq eb1 eb2
    have h2R : (Function.update (Function.update S1 kRU (Sym.bit false :: S1 kRU)) kRX
        (Sym.bit false :: (Function.update S1 kRU (Sym.bit false :: S1 kRU)) kRX)) R =
        List.replicate n .mark ++ DR := by
      rw [Function.update_of_ne hR2, Function.update_of_ne hR1, hS1, Function.update_of_ne hRX,
        Function.update_self]
    have es := walkStep_eval hRX rulBody n DR v S hR eb h2R
    have ih := rulLoop_eval hRX hR1 hR2 hX1 hX2 n DR (setR v (List.replicate n Sym.mark ++ DR).head?)
      _ hD h2R rfl
    refine (Eval.loop_true (by rw [hv, replicate_mark_head]; rfl) es ih).of_eq ?_ (by ring)
    have n1 : kRX ≠ kRU := by decide
    clear eb1 eb2 eb es ih
    congr 1
    funext k
    rw [hS1]
    by_cases h1 : k = kRX
    · subst h1
      simp only [Function.update_self, Function.update_of_ne n1, Function.update_of_ne hX2.symm,
        Function.update_of_ne hR2.symm, List.replicate_succ, List.cons_append, rep_cons]
    · by_cases h2 : k = kRU
      · subst h2
        simp only [Function.update_self, Function.update_of_ne h1, Function.update_of_ne hX1.symm,
          Function.update_of_ne hR1.symm, List.replicate_succ, List.cons_append, rep_cons]
      · by_cases h3 : k = X
        · subst h3
          simp only [Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
            List.replicate_succ, List.cons_append, rep_cons]
        · by_cases h4 : k = R
          · subst h4
            simp only [Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
              Function.update_of_ne h3]
          · simp only [Function.update_of_ne h1, Function.update_of_ne h2,
              Function.update_of_ne h3, Function.update_of_ne h4]

/-- The rulers `kRU = ruler wT`, `kRX = ruler (wT + 1)`. -/
def phaseC : AProg SK :=
  .seq (fetchF 4 kCW) (.seq (buildRuler kCW kRV kCC kYT)
  (.seq (walk kRV kYT2 rulBody) (.seq (pushS kRX (.bit false))
  (.seq (clearMarks kYT2) (drainBits kCW)))))

theorem runs_phaseC (b : BrPar) (rpar : List Sym) (X : SK → List Sym)
    (hP : X sPar = hdrSyms b.hdr ++ rpar) (hH : X kH = []) (hCW : X kCW = []) (hRV : X kRV = [])
    (hYT2 : X kYT2 = []) (hRU : X kRU = []) (hRX : X kRX = []) :
    Runs phaseC X (Function.update (Function.update X kRU (ruler b.wT)) kRX (ruler (b.wT + 1)))
      (fun _ => True) (30 * b.wT + 40 * ((hdrSyms b.hdr).length + 1)) := by
  have hlen := hdr_length b
  have h4 : 4 < b.hdr.length := by omega
  have hbw := bitLen_field_le b.hdr 4 h4
  rw [hdr_get4] at hbw
  -- the ruler builder, as `Runs`
  have hBR : ∀ S : SK → List Sym, S kCW = natSyms b.wT ++ [] → S kRV = [] →
      Runs (buildRuler kCW kRV kCC kYT) S
        (Function.update S kRV (List.replicate b.wT .mark ++ [])) (fun _ => True)
        (9 * b.wT + 16 * bitLen b.wT + 8) := fun S h1 h2 =>
    runsA_of_eval fun v => buildRuler_eval (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) b.wT [] [] v S TermOK.nil (by simp) h1 h2
  have hWK : ∀ S : SK → List Sym, S kRV = List.replicate b.wT .mark ++ [] →
      Runs (walk kRV kYT2 rulBody) S
        (Function.update (Function.update (Function.update (Function.update S kRV []) kYT2
          (List.replicate b.wT .mark ++ S kYT2)) kRU (List.replicate b.wT (.bit false) ++ S kRU))
          kRX (List.replicate b.wT (.bit false) ++ S kRX)) (fun _ => True) (6 * b.wT + 2) :=
    fun S h1 => runsA_of_eval fun v => ⟨_, _, (Eval.seq (eval_peekR kRV v S)
      (rulLoop_eval (by decide) (by decide) (by decide) (by decide) (by decide) b.wT [] _ S
        (by simp) h1
        (by rw [h1]))).of_eq rfl rfl, by omega⟩
  have hCM : ∀ S : SK → List Sym, S kYT2 = List.replicate b.wT .mark ++ [] →
      Runs (clearMarks kYT2) S (Function.update S kYT2 []) (fun _ => True) (3 * b.wT + 2) :=
    fun S h1 => runsA_of_eval fun v => ⟨_, _, clearMarks_eval b.wT [] v S (by simp) h1, le_refl _⟩
  have hDB : ∀ S : SK → List Sym, S kCW = (encodeNat b.wT).map Sym.bit ++ [] →
      Runs (drainBits kCW) S (Function.update S kCW []) (fun _ => True)
        (3 * (encodeNat b.wT).length + 2) :=
    fun S h1 => runsA_of_eval fun v => ⟨_, _, drainBits_eval (encodeNat b.wT) [] v S TermOK.nil h1,
      le_refl _⟩
  refine runs_mono (runs_congr (runs_seq (runs_congr
      (S'' := Function.update X kCW (natSyms b.wT ++ []))
      (runs_fetchF b.hdr 4 h4 kCW (by decide) (by decide) (by decide) rpar X hP hH) ?e1)
    (runs_seq (hBR _ ?h2 ?h3)
    (runs_seq (hWK _ ?h4)
    (runs_seq (runs_pushS kRX (Sym.bit false) _)
    (runs_seq (hCM _ ?h5) (hDB _ ?h6)))))) ?he) (fun _ _ => trivial) ?hc
  case e1 => rw [hdr_get4, hCW]
  case h2 => simp [Function.update_apply]
  case h3 => simp [Function.update_apply, hRV]
  case h4 => simp [Function.update_apply]
  case h5 => simp [Function.update_apply, hYT2]
  case h6 => simp [Function.update_apply, natSyms]
  case he =>
    funext x
    simp only [Function.update_apply, ruler]
    split_ifs <;> simp_all [List.replicate_succ]
  case hc =>
    unfold bitLen at hbw ⊢
    omega

/-! ## The header parse -/

/-- **The header parse** of the parameter-row kernel. -/
def hdrParse : AProg SK := .seq phaseA (.seq phaseB phaseC)

theorem closed_Lo {p : TMFw.Lib.SProg SK} (hp : p.Closed) : (Lo p).Closed :=
  WP.W9comp.closed_liftRegs lensO hp

theorem hdrParse_closed : hdrParse.Closed := by
  have c1 : ∀ a b c : SK, (Lo (TMFw.Lib.copyBlock a b c)).Closed := fun a b c => closed_Lo (by
    simp [Prog.Closed, Prog.FreeBelow, TMFw.Lib.copyBlock, TMFw.Lib.moveBlock, TMFw.Lib.moveBits,
      TMFw.Lib.moveBitsBody, TMFw.Lib.restoreR, TMFw.Lib.skip, TMFw.Lib.moveBitsDup,
      TMFw.Lib.dupBody, TMFw.Lib.popR, TMFw.Lib.pushC, TMFw.Lib.pushR])
  have c2 : ∀ a b : SK, (Lo (TMFw.Lib.moveBlock a b)).Closed := fun a b => closed_Lo (by
    simp [Prog.Closed, Prog.FreeBelow, TMFw.Lib.moveBlock, TMFw.Lib.moveBits,
      TMFw.Lib.moveBitsBody, TMFw.Lib.restoreR, TMFw.Lib.skip, TMFw.Lib.popR, TMFw.Lib.pushR])
  have c3 : ∀ (a : SK) (x : Sym), (Lo (TMFw.Lib.pushC a x)).Closed := fun a x => closed_Lo (by
    simp [Prog.Closed, Prog.FreeBelow, TMFw.Lib.pushC])
  have c4 : ∀ a b : SK, (Lo (TMFw.Lib.dec a b)).Closed := fun a b => closed_Lo (by
    simp [Prog.Closed, Prog.FreeBelow, TMFw.Lib.dec, TMFw.Lib.decFix, TMFw.Lib.scanLoop,
      TMFw.Lib.scanBody, TMFw.Lib.peekR, TMFw.Lib.popR, TMFw.Lib.pushC, TMFw.Lib.skip,
      TMFw.Lib.moveBits, TMFw.Lib.moveBitsBody, TMFw.Lib.pushR])
  have c5 : ∀ a b : SK, (Lo (BridgePP.skipField a b)).Closed := fun a b => closed_Lo (by
    simp [Prog.Closed, Prog.FreeBelow, BridgePP.skipField, BridgePP.moveSym, TMFw.Lib.moveBlock,
      TMFw.Lib.moveBits, TMFw.Lib.moveBitsBody, TMFw.Lib.restoreR, TMFw.Lib.skip, TMFw.Lib.popR,
      TMFw.Lib.pushR])
  have c6 : ∀ n, (Lo (BridgePP.skipFields sPar kH n)).Closed := fun n =>
    closed_Lo (BridgePP.closed_skipFields _ _ n)
  have c7 : (Lo (WP.W9comp.rewindTo kH sPar .sep2)).Closed := closed_Lo (by
    simp [Prog.Closed, Prog.FreeBelow, WP.W9comp.rewindTo, WP.W9comp.rewindBody, TMFw.Lib.popR,
      TMFw.Lib.pushR])
  simp only [Prog.Closed] at c1 c2 c3 c4 c5 c6 c7 ⊢
  simp [hdrParse, phaseA, phaseB, phaseC, fetchF, cLoop, sufBody, rulBody, Prog.FreeBelow,
    buildRuler, walk, walkLoop, walkStep, clearMarks, cmLoop, drainBits, dbLoop, mvBits, mvLoop,
    brLoop, brBody, double, dblLoop, moveMarks, mmLoop, peekQ, peekO, drop1, pushS, skipA, peekR,
    c1, c2, c3, c4, c5, c6, c7]

/-- **The header parse**: the five outputs from the header and the stage counter. -/
theorem runs_hdrParse : ∃ c : ℕ, ∀ (b : BrPar) (m : ℕ) (i : Fin b.d) (rpar rax : List Sym)
    (S : SK → List Sym),
    ShapeOK b.t → (i : ℕ) ≠ 0 → (i : ℕ) + m = b.d → 1 ≤ b.wT → TermOK rax →
    S sPar = hdrSyms b.hdr ++ rpar → S sAx = natSyms m ++ rax →
    (∀ e : Fin 25, S (.inr e) = []) →
    Runs hdrParse S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        kRU (ruler b.wT)) kRX (ruler (b.wT + 1))) kCX (natSyms ((i : ℕ) - 1)))
        kCT (natSyms (b.t i / 2))) kCU (natSyms (suffixProd b.t i)))
      (fun _ => True) (c * (b.wT + b.setup)) := by
  refine ⟨200, fun b m i rpar rax S hshape hi him _ hrax hP hA hE => ?_⟩
  have hA' := runs_phaseA b m i hi him rpar rax hrax S hP hA hE
  have hB' := runs_phaseB b m i hshape him rpar (Function.update S kCX (natSyms ((i : ℕ) - 1)))
    (by simp [Function.update_apply, hP]) (by simp [Function.update_apply, hE])
    (by simp [Function.update_apply, hE]) (by simp [Function.update_apply, hE])
    (by simp [Function.update_apply, hE])
  have hC' := runs_phaseC b rpar (Function.update (Function.update (Function.update
    (Function.update (Function.update S kCX (natSyms ((i : ℕ) - 1))) kCD []) kZB [])
    kCT (natSyms (b.t i / 2))) kCU (natSyms (suffixProd b.t i))) (by simp [Function.update_apply, hP])
    (by simp [Function.update_apply, hE]) (by simp [Function.update_apply, hE])
    (by simp [Function.update_apply, hE]) (by simp [Function.update_apply, hE])
    (by simp [Function.update_apply, hE]) (by simp [Function.update_apply, hE])
  refine runs_mono (runs_congr (runs_seq hA' (runs_seq hB' hC')) ?he) (fun _ _ => trivial) ?hc
  case he =>
    funext x
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  case hc =>
    have h1 : ((hdrSyms b.hdr).length + 1) ^ 2 ≤ b.setup := by
      unfold BrPar.setup
      exact Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : (hdrSyms b.hdr).length + 1 ≤ ((hdrSyms b.hdr).length + 1) ^ 2 := by
      nlinarith
    nlinarith

end SubNLogN.Machine.Bridge.SolveParamsHdrAux
