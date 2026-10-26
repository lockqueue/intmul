/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7BadTri
import SubNLogN.Machine.AppC.C7ExtractKit
import SubNLogN.Machine.AppC.C7ExtractMath
import SubNLogN.Machine.Calculus.FramePassR

/-!
# Lemma A.9 extraction: line sums on the arithmetic kit (`Machine/AppC/C7BadTriLine.lean`)

Programs over an abstract arithmetic kit `xk : XKit K` (`C7ExtractKit.lean`) computing the line sum
`lsum K ρ x o par m` (`C7ExtractMath.lean`): with `XS = x / 2^J`, `OS = o / 2^J`, `P = 2^J` for
`J = ρ + iK`, each step tests the low bits of `XS` and `OS` (one `peek` each), adds `P` to the
accumulator when `x_J = 1` and `o_J = par`, and advances `J` by `K` (two divisions, one product). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)
-/

namespace SubNLogN.Machine.AppC.C7BadTriAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine.AppC.C7ExtractAux SubNLogN.Machine.Calculus

/-! ## Parity of a number from the top of its stack -/

theorem natSyms_head_bit_true (n : ℕ) (r : List Sym) (hr : TermOK r) :
    (natSyms n ++ r).head? = some (Sym.bit true) ↔ n % 2 = 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h2 : (2 * m) % 2 = 0 := by omega
    rw [h2]
    simp only [zero_ne_one, iff_false]
    rw [show 2 * m = m + m by omega]
    unfold natSyms
    rw [encodeNat_add]
    split_ifs with h
    · simp only [List.map_nil, List.nil_append]
      intro hh
      have := hr _ hh
      simp [Sym.isBit] at this
    · simp
  · have h2 : (2 * m + 1) % 2 = 1 := by omega
    rw [h2]
    simp only [iff_true]
    rw [show 2 * m + 1 = m + m + 1 by omega]
    unfold natSyms
    rw [encodeNat_add_add_one]
    simp

/-! ## Arithmetic helpers -/

theorem btBitLen_le {m B : ℕ} (h : m < 2 ^ B) : bitLen m ≤ B := by
  rw [bitLen_eq_size]
  exact Nat.size_le.mpr h

theorem btOpCost_ge {K : Type} [DecidableEq K] (xk : XKit K) (n : ℕ) :
    40 * (n + 1) ≤ opCost xk n := by
  unfold opCost
  calc 40 * (n + 1) ≤ 40 * (n + 1) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
    _ ≤ (2 * xk.c + 40) * (n + 1) ^ 2 := Nat.mul_le_mul_right _ (by omega)

theorem btSumConst (c : ℕ) : ∀ N, ((List.range N).map (fun _ => c)).sum = N * c
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, btSumConst c N]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring

theorem btNatSyms0 : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]

/-! ## Layout

The kernel runs on `BTLoc = KLoc (Fin 11) (Fin 12)`: the named stacks of `C7BadTriStmt` (only
`0`-`2` and `7`-`10` are used; `3`-`6` are never touched) and twelve private scratch stacks. -/

/-- The stacks of the kernel. -/
abbrev BTLoc : Type := KLoc (Fin 11) (Fin 12)

/-- Named stack `0`: the chunk `x`. -/
abbrev bX : BTLoc := .inl 0
/-- Named stack `1`: the chunk `y`. -/
abbrev bY : BTLoc := .inl 1
/-- Named stack `2`: the chunk `z`. -/
abbrev bZ : BTLoc := .inl 2
/-- Named stack `7`: `2^L`. -/
abbrev bPL : BTLoc := .inl 7
/-- Named stack `8`: `2^K`. -/
abbrev bPK : BTLoc := .inl 8
/-- Named stack `9`: `2^ρ`. -/
abbrev bPr : BTLoc := .inl 9
/-- Named stack `10`: `f - 1`. -/
abbrev bF1 : BTLoc := .inl 10
/-- Scratch: `x / 2^J`. -/
abbrev bXS : BTLoc := .inr 0
/-- Scratch: `o / 2^J`. -/
abbrev bOS : BTLoc := .inr 1
/-- Scratch: `2^J`. -/
abbrev bP : BTLoc := .inr 2
/-- Scratch: the line-sum accumulator. -/
abbrev bOFF : BTLoc := .inr 3
/-- Scratch: a copy of `y` (for `T₀`). -/
abbrev bYC : BTLoc := .inr 4
/-- Scratch: the loop counter. -/
abbrev bCNT : BTLoc := .inr 5
/-- Scratch: the temporary of the counter and of the copies. -/
abbrev bCT : BTLoc := .inr 6
/-- Scratch: kit temporary. -/
abbrev bT0 : BTLoc := .inr 7
/-- Scratch: kit temporary. -/
abbrev bT1 : BTLoc := .inr 8
/-- Scratch: kit temporary. -/
abbrev bT2 : BTLoc := .inr 9
/-- Scratch: kit temporary. -/
abbrev bT3 : BTLoc := .inr 10
/-- Scratch: kit temporary. -/
abbrev bT4 : BTLoc := .inr 11

/-! ## Building a number on a fresh floor -/

section Init

variable {K : Type} [DecidableEq K] (xk : XKit K)

/-- Push a floor on `k` and copy the number on top of `src` onto it (`tmp` restored). -/
def btInitCopy (src k tmp : K) : Prog K (fun _ => Sym) xk.R :=
  .seq (pushW xk k .mark) (copyW xk src k tmp)

/-- `btInitCopy`, then divide the new number by the number on top of `d` (kit temporaries
`t j d0 d1 d2`). -/
def btInitDiv (src k tmp d t j d0 d1 d2 : K) : Prog K (fun _ => Sym) xk.R :=
  .seq (btInitCopy xk src k tmp) (divBy xk k d t j d0 d1 d2)

theorem closed_btInitCopy (src k tmp : K) : (btInitCopy xk src k tmp).Closed :=
  ⟨closed_pushW xk _ _, closed_copyW xk _ _ _⟩

theorem closed_btInitDiv (src k tmp d t j d0 d1 d2 : K) :
    (btInitDiv xk src k tmp d t j d0 d1 d2).Closed :=
  ⟨closed_btInitCopy xk _ _ _, closed_divBy xk _ _ _ _ _ _ _⟩

theorem runs_btPush (k : K) (s : Sym) (l : List Sym) (S : K → List Sym) (hl : S k = l) :
    Runs (pushW xk k s) S (Function.update S k (s :: l)) (fun _ => True) 1 := by
  subst hl
  exact runs_pushW xk k s S

theorem runs_btInitCopy {src k tmp : K} (h1 : src ≠ k) (h2 : src ≠ tmp) (h3 : k ≠ tmp)
    (a B : ℕ) (rs l : List Sym) (S : K → List Sym) (hrs : TermOK rs)
    (hS : S src = natSyms a ++ rs) (hl : S k = l) (ha : bitLen a ≤ B) :
    Runs (btInitCopy xk src k tmp) S (Function.update S k (natSyms a ++ Sym.mark :: l))
      (fun _ => True) (opCost xk B) := by
  subst hl
  have hW := btOpCost_ge xk B
  have e2 := runs_copyW xk h1 h2 h3 a rs (Function.update S k (Sym.mark :: S k)) hrs
    (by rw [Function.update_of_ne h1]; exact hS)
  rw [Function.update_self, Function.update_idem] at e2
  exact WP.W9comp.runs_mono (WP.W9comp.runs_seq (runs_pushW xk k .mark S) e2)
    (fun _ _ => trivial) (by omega)

theorem runs_btInitDiv {src k tmp d t j d0 d1 d2 : K} (h1 : src ≠ k) (h2 : src ≠ tmp)
    (h3 : k ≠ tmp) (hN : [k, d, t, j, d0, d1, d2].Nodup) (hdk : d ≠ k) (a q B : ℕ)
    (rs rd l : List Sym) (S : K → List Sym) (hrs : TermOK rs) (hrd : TermOK rd)
    (hS : S src = natSyms a ++ rs) (hd : S d = natSyms q ++ rd) (hl : S k = l) (hq : 0 < q)
    (ha : bitLen a ≤ B) (hqB : bitLen q ≤ B) :
    Runs (btInitDiv xk src k tmp d t j d0 d1 d2) S
      (Function.update S k (natSyms (a / q) ++ Sym.mark :: l)) (fun _ => True)
      (2 * opCost xk B) := by
  have e1 := runs_btInitCopy xk h1 h2 h3 a B rs l S hrs hS hl ha
  have e2 := runs_divBy xk hN a q B (Sym.mark :: l) rd
    (Function.update S k (natSyms a ++ Sym.mark :: l)) (termOK_mark _) hrd hq
    (Function.update_self _ _ _) (by rw [Function.update_of_ne hdk]; exact hd) ha hqB
  rw [Function.update_idem] at e2
  exact WP.W9comp.runs_mono (WP.W9comp.runs_seq e1 e2) (fun _ _ => trivial) (by omega)

end Init

/-! ## One step of the line sum -/

section Body

variable (xk : XKit BTLoc)

/-- The peeked symbol is `bit true`. -/
def btIsOne (v : xk.R) : Bool := decide (xk.lw.get v = some (Sym.bit true))

/-- One step of the line sum: if the low bits of `XS` and `OS` are `1` and `par`, then
`OFF += P`; then `XS /= 2^K`, `OS /= 2^K`, `P *= 2^K`. -/
def btBody (par : Bool) : Prog BTLoc (fun _ => Sym) xk.R :=
  .seq (.seq (peekW xk bXS) (.ite (btIsOne xk)
      (.seq (peekW xk bOS) (.ite (fun v => btIsOne xk v == par)
        (addTo xk bOFF bP bT0 bT1 bT2 bT3) (skipW xk)))
      (skipW xk)))
    (.seq (divBy xk bXS bPK bT0 bT1 bT2 bT3 bT4)
      (.seq (divBy xk bOS bPK bT0 bT1 bT2 bT3 bT4)
        (mulBy xk bP bPK bT0 bT1 bT2 bT3 bT4)))

theorem closed_btBody (par : Bool) : (btBody xk par).Closed :=
  ⟨⟨closed_peekW xk _, ⟨closed_peekW xk _, ⟨closed_addTo xk _ _ _ _ _ _, closed_skipW xk⟩⟩,
    closed_skipW xk⟩, closed_divBy xk _ _ _ _ _ _ _, closed_divBy xk _ _ _ _ _ _ _,
    closed_mulBy xk _ _ _ _ _ _ _⟩

/-- The test part of a step: `OFF += 2^J` iff `x_J = 1` and `(o_J = 1) = par`. -/
theorem btTest_runs (par : Bool) (x o J acc B : ℕ) (lXS lOS lP lOFF : List Sym)
    (S : BTLoc → List Sym)
    (hXS : S bXS = natSyms (x / 2 ^ J) ++ Sym.mark :: lXS)
    (hOS : S bOS = natSyms (o / 2 ^ J) ++ Sym.mark :: lOS)
    (hP : S bP = natSyms (2 ^ J) ++ Sym.mark :: lP)
    (hOFF : S bOFF = natSyms acc ++ Sym.mark :: lOFF)
    (hB1 : acc + 2 ^ J < 2 ^ B) :
    Runs (.seq (peekW xk bXS) (.ite (btIsOne xk)
        (.seq (peekW xk bOS) (.ite (fun v => btIsOne xk v == par)
          (addTo xk bOFF bP bT0 bT1 bT2 bT3) (skipW xk)))
        (skipW xk))) S
      (Function.update S bOFF (natSyms (acc + if x / 2 ^ J % 2 = 1 ∧
        decide (o / 2 ^ J % 2 = 1) = par then 2 ^ J else 0) ++ Sym.mark :: lOFF))
      (fun _ => True) (opCost xk B + 4) := by
  have hpx : ((S bXS).head? = some (Sym.bit true)) ↔ x / 2 ^ J % 2 = 1 := by
    rw [hXS]; exact natSyms_head_bit_true _ _ (termOK_mark _)
  have hpo : ((S bOS).head? = some (Sym.bit true)) ↔ o / 2 ^ J % 2 = 1 := by
    rw [hOS]; exact natSyms_head_bit_true _ _ (termOK_mark _)
  have hW := btOpCost_ge xk B
  by_cases hx1 : x / 2 ^ J % 2 = 1
  · have hc1 : RunsIn [] (peekW xk bXS) S S (fun v => btIsOne xk v = true) 1 :=
      RunsIn.mono (runsIn_peekW xk bXS S) (fun v hv => by
        simp only [btIsOne, decide_eq_true_eq]; rw [hv]; exact hpx.mpr hx1) le_rfl
    have hio : ∀ v, xk.lw.get v = (S bOS).head? →
        btIsOne xk v = decide (o / 2 ^ J % 2 = 1) := fun v hv => by
      simp only [btIsOne]; rw [hv]; exact decide_eq_decide.mpr hpo
    by_cases ho : decide (o / 2 ^ J % 2 = 1) = par
    · have hc2 : RunsIn [] (peekW xk bOS) S S (fun v => (btIsOne xk v == par) = true) 1 :=
        RunsIn.mono (runsIn_peekW xk bOS S) (fun v hv => by
          rw [hio v hv, ho]; exact beq_self_eq_true par) le_rfl
      have hacc : acc < 2 ^ B := lt_of_le_of_lt (Nat.le_add_right acc (2 ^ J)) hB1
      have hpj : 2 ^ J < 2 ^ B := lt_of_le_of_lt (Nat.le_add_left (2 ^ J) acc) hB1
      have hadd := runs_addTo xk (k := bOFF) (b := bP) (t := bT0) (t1 := bT1) (t2 := bT2)
        (t3 := bT3) (by decide) acc (2 ^ J) B (Sym.mark :: lOFF) (Sym.mark :: lP) S
        (termOK_mark _) (termOK_mark _) hOFF hP
        (btBitLen_le hacc) (btBitLen_le hpj) (btBitLen_le hB1)
      have X := RunsIn.ite_true (Pf := skipW xk) hc1
        (RunsIn.ite_true (Pf := skipW xk) hc2 (RunsIn.iff_runs.mpr hadd))
      refine RunsIn.iff_runs.mp (RunsIn.congr X ?_ (by omega))
      rw [if_pos ⟨hx1, ho⟩]
    · have hc2 : RunsIn [] (peekW xk bOS) S S (fun v => (btIsOne xk v == par) = false) 1 :=
        RunsIn.mono (runsIn_peekW xk bOS S) (fun v hv => by
          rw [hio v hv, beq_eq_false_iff_ne]; exact ho) le_rfl
      have X := RunsIn.ite_true (Pf := skipW xk) hc1
        (RunsIn.ite_false (Pt := addTo xk bOFF bP bT0 bT1 bT2 bT3) hc2
          (RunsIn.iff_runs.mpr (runs_skipW xk S)))
      refine RunsIn.iff_runs.mp (RunsIn.congr X ?_ (by omega))
      rw [if_neg (fun h => ho h.2), Nat.add_zero, ← hOFF, Function.update_eq_self]
  · have hc1 : RunsIn [] (peekW xk bXS) S S (fun v => btIsOne xk v = false) 1 :=
      RunsIn.mono (runsIn_peekW xk bXS S) (fun v hv => by
        simp only [btIsOne, decide_eq_false_iff_not]; rw [hv]
        exact fun h => hx1 (hpx.mp h)) le_rfl
    have X := RunsIn.ite_false (Pt := .seq (peekW xk bOS) (.ite (fun v => btIsOne xk v == par)
        (addTo xk bOFF bP bT0 bT1 bT2 bT3) (skipW xk))) hc1
      (RunsIn.iff_runs.mpr (runs_skipW xk S))
    refine RunsIn.iff_runs.mp (RunsIn.congr X ?_ (by omega))
    rw [if_neg (fun h => hx1 h.1), Nat.add_zero, ← hOFF, Function.update_eq_self]

/-- **One step of the line sum** (`J ↦ J + K`). -/
theorem btBody_runs (par : Bool) (x o J K acc B : ℕ) (lXS lOS lP lOFF r3 : List Sym)
    (S : BTLoc → List Sym)
    (hXS : S bXS = natSyms (x / 2 ^ J) ++ Sym.mark :: lXS)
    (hOS : S bOS = natSyms (o / 2 ^ J) ++ Sym.mark :: lOS)
    (hP : S bP = natSyms (2 ^ J) ++ Sym.mark :: lP)
    (hOFF : S bOFF = natSyms acc ++ Sym.mark :: lOFF)
    (hPK : S bPK = natSyms (2 ^ K) ++ r3) (hr3 : TermOK r3)
    (hB1 : acc + 2 ^ J < 2 ^ B) (hx : x / 2 ^ J < 2 ^ B) (ho : o / 2 ^ J < 2 ^ B)
    (hJK : 2 ^ (J + K) < 2 ^ B) :
    Runs (btBody xk par) S
      (Function.update (Function.update (Function.update (Function.update S
        bOFF (natSyms (acc + if x / 2 ^ J % 2 = 1 ∧ decide (o / 2 ^ J % 2 = 1) = par
          then 2 ^ J else 0) ++ Sym.mark :: lOFF))
        bXS (natSyms (x / 2 ^ J / 2 ^ K) ++ Sym.mark :: lXS))
        bOS (natSyms (o / 2 ^ J / 2 ^ K) ++ Sym.mark :: lOS))
        bP (natSyms (2 ^ J * 2 ^ K) ++ Sym.mark :: lP))
      (fun _ => True) (4 * opCost xk B + 4) := by
  have hK2 : 2 ^ K < 2 ^ B :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left K J)) hJK
  have hJ2 : 2 ^ J < 2 ^ B :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right J K)) hJK
  have hJK' : 2 ^ J * 2 ^ K < 2 ^ B := by rw [← pow_add]; exact hJK
  have e1 := btTest_runs xk par x o J acc B lXS lOS lP lOFF S hXS hOS hP hOFF hB1
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq
    (runs_divBy xk (k := bXS) (b := bPK) (t := bT0) (j := bT1) (d0 := bT2) (d1 := bT3)
      (d2 := bT4) (by decide) (x / 2 ^ J) (2 ^ K) B (Sym.mark :: lXS) r3 _ (termOK_mark _) hr3
      (Nat.two_pow_pos K) (by simp +decide [hXS])
      (by simp +decide [hPK]) (btBitLen_le hx) (btBitLen_le hK2))
    (WP.W9comp.runs_seq
      (runs_divBy xk (k := bOS) (b := bPK) (t := bT0) (j := bT1) (d0 := bT2) (d1 := bT3)
        (d2 := bT4) (by decide) (o / 2 ^ J) (2 ^ K) B (Sym.mark :: lOS) r3 _ (termOK_mark _)
        hr3 (Nat.two_pow_pos K) (by simp +decide [hOS])
        (by simp +decide [hPK]) (btBitLen_le ho) (btBitLen_le hK2))
      (runs_mulBy xk (k := bP) (b := bPK) (t := bT0) (A := bT1) (Bs := bT2) (Acc := bT3)
        (T := bT4) (by decide) (2 ^ J) (2 ^ K) B (Sym.mark :: lP) r3 _ (termOK_mark _) hr3
        (by simp +decide [hP])
        (by simp +decide [hPK]) (btBitLen_le hJ2)
        (btBitLen_le hK2) (btBitLen_le hJK'))))) (fun _ _ => trivial) (by omega)

end Body

/-! ## The line sum -/

section Lsum

variable (xk : XKit BTLoc)

/-- Setup of the line sum: `XS := x / 2^ρ`, `OS := o / 2^ρ` (`o` on top of `b`), `P := 2^ρ`,
`OFF := 0`, `CNT := f - 1`, each above a fresh floor. -/
def btSetup (b : BTLoc) : Prog BTLoc (fun _ => Sym) xk.R :=
  .seq (btInitDiv xk bX bXS bCT bPr bT0 bT1 bT2 bT3 bT4)
  (.seq (btInitDiv xk b bOS bCT bPr bT0 bT1 bT2 bT3 bT4)
  (.seq (btInitCopy xk bPr bP bCT)
  (.seq (pushW xk bOFF .mark) (btInitCopy xk bF1 bCNT bCT))))

/-- Cleanup of the line sum: pop the counter's floor, drop the work stacks other than `OFF`. -/
def btClean : Prog BTLoc (fun _ => Sym) xk.R :=
  .seq (popW xk bCNT) (.seq (dropFW xk bXS) (.seq (dropFW xk bOS) (dropFW xk bP)))

/-- **The line-sum program**: `OFF := lsum K ρ x o par (f - 1)` above a fresh floor. -/
def btLsum (b : BTLoc) (par : Bool) : Prog BTLoc (fun _ => Sym) xk.R :=
  .seq (btSetup xk b) (.seq (countdown xk.lw bCNT bCT (btBody xk par)) (btClean xk))

theorem closed_btSetup (b : BTLoc) : (btSetup xk b).Closed :=
  ⟨closed_btInitDiv xk _ _ _ _ _ _ _ _ _, closed_btInitDiv xk _ _ _ _ _ _ _ _ _,
    closed_btInitCopy xk _ _ _, closed_pushW xk _ _, closed_btInitCopy xk _ _ _⟩

theorem closed_btClean : (btClean xk).Closed :=
  ⟨closed_popW xk _, closed_dropFW xk _, closed_dropFW xk _, closed_dropFW xk _⟩

theorem closed_btLsum (b : BTLoc) (par : Bool) : (btLsum xk b par).Closed :=
  ⟨closed_btSetup xk b, closed_countdown xk.lw _ _ (closed_btBody xk par), closed_btClean xk⟩

end Lsum

/-- Loop state of the line sum after `i` steps (`J = ρ + iK`) over the base stacks `S`. -/
def btSt (K ρ x o : ℕ) (par : Bool) (S : BTLoc → List Sym) (i : ℕ) : BTLoc → List Sym :=
  Function.update (Function.update (Function.update (Function.update S
    bXS (natSyms (x / 2 ^ (ρ + i * K)) ++ Sym.mark :: S bXS))
    bOS (natSyms (o / 2 ^ (ρ + i * K)) ++ Sym.mark :: S bOS))
    bP (natSyms (2 ^ (ρ + i * K)) ++ Sym.mark :: S bP))
    bOFF (natSyms (lsum K ρ x o par i) ++ Sym.mark :: S bOFF)

theorem btSt_zero (K ρ x o : ℕ) (par : Bool) (S : BTLoc → List Sym) :
    btSt K ρ x o par S 0 =
      Function.update (Function.update (Function.update (Function.update S
        bXS (natSyms (x / 2 ^ ρ) ++ Sym.mark :: S bXS))
        bOS (natSyms (o / 2 ^ ρ) ++ Sym.mark :: S bOS))
        bP (natSyms (2 ^ ρ) ++ Sym.mark :: S bP))
        bOFF (Sym.mark :: S bOFF) := by
  simp only [btSt, Nat.zero_mul, Nat.add_zero, lsum, btNatSyms0, List.nil_append]

theorem btChain_body (S : BTLoc → List Sym) (a b c d e a' b' c' d' : List Sym) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update S
        bXS a) bOS b) bP c) bOFF d) bCNT e) bOFF d') bXS a') bOS b') bP c' =
    Function.update (Function.update (Function.update (Function.update (Function.update S
      bXS a') bOS b') bP c') bOFF d') bCNT e := by
  funext k
  rcases k with j | j <;> fin_cases j <;> simp +decide

theorem btChain_clean (S : BTLoc → List Sym) (a b c d e : List Sym) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update S
        bXS a) bOS b) bP c) bOFF d) bCNT e) bCNT (S bCNT)) bXS (S bXS)) bOS (S bOS))
        bP (S bP) =
    Function.update S bOFF d := by
  funext k
  rcases k with j | j <;> fin_cases j <;> simp +decide

/-- **The line sum on the machine.** With `x` on `X`, `o` on `b` and the parameters `2^K, 2^ρ, N`
on their named stacks, `btLsum` pushes `lsum K ρ x o par N` (above a floor) on `OFF` and changes
nothing else. All numbers stay below `2^B`. -/
theorem btLsum_runs (xk : XKit BTLoc) (b : BTLoc) (hbXS : b ≠ bXS) (hbOS : b ≠ bOS)
    (hbCT : b ≠ bCT) (par : Bool) (K ρ N B x o : ℕ) (rx rb r3 r4 r6 : List Sym)
    (S : BTLoc → List Sym)
    (hrx : TermOK rx) (hrb : TermOK rb) (hr3 : TermOK r3) (hr4 : TermOK r4) (hr6 : TermOK r6)
    (hSx : S bX = natSyms x ++ rx) (hSb : S b = natSyms o ++ rb)
    (hS3 : S bPK = natSyms (2 ^ K) ++ r3) (hS4 : S bPr = natSyms (2 ^ ρ) ++ r4)
    (hS6 : S bF1 = natSyms N ++ r6)
    (hK : 1 ≤ K) (hB : ρ + N * K < B) (hx : x < 2 ^ B) (ho : o < 2 ^ B) (hN : N < 2 ^ B) :
    Runs (btLsum xk b par) S
      (Function.update S bOFF (natSyms (lsum K ρ x o par N) ++ Sym.mark :: S bOFF))
      (fun _ => True) (12 * opCost xk B * (N + 1)) := by
  have hW := btOpCost_ge xk B
  have hρB : 2 ^ ρ < 2 ^ B := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hNKB : 2 ^ (ρ + N * K) < 2 ^ B := Nat.pow_lt_pow_right (by norm_num) hB
  have hset : Runs (btSetup xk b) S
      (Function.update (btSt K ρ x o par S 0) bCNT (natSyms N ++ Sym.mark :: S bCNT))
      (fun _ => True) (6 * opCost xk B + 1) := by
    rw [btSt_zero]
    refine WP.W9comp.runs_mono (WP.W9comp.runs_seq
      (runs_btInitDiv xk (src := bX) (k := bXS) (tmp := bCT) (d := bPr) (t := bT0) (j := bT1)
        (d0 := bT2) (d1 := bT3) (d2 := bT4) (by decide) (by decide) (by decide) (by decide)
        (by decide) x (2 ^ ρ) B rx r4 (S bXS) S hrx hr4 hSx hS4 rfl (Nat.two_pow_pos ρ)
        (btBitLen_le hx) (btBitLen_le hρB))
      (WP.W9comp.runs_seq
      (runs_btInitDiv xk (src := b) (k := bOS) (tmp := bCT) (d := bPr) (t := bT0) (j := bT1)
        (d0 := bT2) (d1 := bT3) (d2 := bT4) hbOS hbCT (by decide) (by decide) (by decide)
        o (2 ^ ρ) B rb r4 (S bOS) _ hrb hr4
        (by simp +decide [hbXS, hSb])
        (by simp +decide [hS4])
        (by simp +decide) (Nat.two_pow_pos ρ)
        (btBitLen_le ho) (btBitLen_le hρB))
      (WP.W9comp.runs_seq
      (runs_btInitCopy xk (src := bPr) (k := bP) (tmp := bCT) (by decide) (by decide)
        (by decide) (2 ^ ρ) B r4 (S bP) _ hr4 (by simp +decide [hS4])
        (by simp +decide) (btBitLen_le hρB))
      (WP.W9comp.runs_seq
      (runs_btPush xk bOFF .mark (S bOFF) _ (by simp +decide))
      (runs_btInitCopy xk (src := bF1) (k := bCNT) (tmp := bCT) (by decide) (by decide)
        (by decide) N B r6 (S bCNT) _ hr6 (by simp +decide [hS6])
        (by simp +decide) (btBitLen_le hN))))))
      (fun _ _ => trivial) (by omega)
  have hbody : ∀ n, n < N →
      RunsIn [] (btBody xk par)
        (Function.update (btSt K ρ x o par S (N - (n + 1))) bCNT
          (natSyms (n + 1) ++ Sym.mark :: S bCNT))
        (Function.update (btSt K ρ x o par S (N - n)) bCNT
          (natSyms (n + 1) ++ Sym.mark :: S bCNT))
        (fun _ => True) (4 * opCost xk B + 4) := by
    intro n hn
    obtain ⟨i, hi1, hi2⟩ : ∃ i, N - (n + 1) = i ∧ N - n = i + 1 := ⟨N - (n + 1), rfl, by omega⟩
    rw [hi1, hi2]
    have hiN : i + 1 ≤ N := by omega
    have hlt := lsum_lt K ρ x o par hK i
    have hstep := pow_step K ρ i hK
    have hmul : (i + 1) * K ≤ N * K := Nat.mul_le_mul_right K hiN
    have e1 : (i + 1) * K = i * K + K := by ring
    have hJB : ρ + i * K + K < B := by omega
    have hpow : 2 ^ (ρ + (i + 1) * K) ≤ 2 ^ (ρ + N * K) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hB1 : lsum K ρ x o par i + 2 ^ (ρ + i * K) < 2 ^ B := by omega
    have hxB : x / 2 ^ (ρ + i * K) < 2 ^ B := lt_of_le_of_lt (Nat.div_le_self _ _) hx
    have hoB : o / 2 ^ (ρ + i * K) < 2 ^ B := lt_of_le_of_lt (Nat.div_le_self _ _) ho
    have hJK : 2 ^ (ρ + i * K + K) < 2 ^ B := Nat.pow_lt_pow_right (by norm_num) hJB
    have hrun := btBody_runs xk par x o (ρ + i * K) K (lsum K ρ x o par i) B (S bXS) (S bOS)
      (S bP) (S bOFF) r3
      (Function.update (btSt K ρ x o par S i) bCNT (natSyms (n + 1) ++ Sym.mark :: S bCNT))
      (by simp +decide [btSt])
      (by simp +decide [btSt])
      (by simp +decide [btSt])
      (by simp +decide [btSt])
      (by simp +decide [btSt, hS3]) hr3 hB1 hxB hoB hJK
    have ex : ∀ v, v / 2 ^ (ρ + i * K) / 2 ^ K = v / 2 ^ (ρ + (i + 1) * K) := fun v => by
      rw [Nat.div_div_eq_div_mul, ← pow_add, e1, Nat.add_assoc]
    have ep : 2 ^ (ρ + i * K) * 2 ^ K = 2 ^ (ρ + (i + 1) * K) := by
      rw [← pow_add, e1, Nat.add_assoc]
    rw [ex, ex, ep] at hrun
    exact RunsIn.iff_runs.mpr (WP.W9comp.runs_congr hrun (btChain_body S _ _ _ _ _ _ _ _ _))
  have hcd := RunsIn.mono (runsIn_countdown xk.lw (c := bCNT) (t := bCT) (by decide) N
      (Sym.mark :: S bCNT) (termOK_mark _) (fun n => btSt K ρ x o par S (N - n))
      (fun _ => 4 * opCost xk B + 4) hbody) (Q' := fun _ => True) (fun _ _ => trivial) le_rfl
  simp only [Nat.sub_self, Nat.sub_zero] at hcd
  have hcl : Runs (btClean xk)
      (Function.update (btSt K ρ x o par S N) bCNT (Sym.mark :: S bCNT))
      (Function.update S bOFF (natSyms (lsum K ρ x o par N) ++ Sym.mark :: S bOFF))
      (fun _ => True) (3 * opCost xk B + 1) := by
    have h1 := btBitLen_le (lt_of_le_of_lt (Nat.div_le_self x (2 ^ (ρ + N * K))) hx)
    have h2 := btBitLen_le (lt_of_le_of_lt (Nat.div_le_self o (2 ^ (ρ + N * K))) ho)
    have h3 := btBitLen_le hNKB
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq
      (runs_popW_cons xk bCNT _ Sym.mark (S bCNT) (by simp))
      (WP.W9comp.runs_seq
        (runs_dropFW xk bXS (x / 2 ^ (ρ + N * K)) Sym.mark (S bXS) _ rfl
          (by simp +decide [btSt]))
        (WP.W9comp.runs_seq
          (runs_dropFW xk bOS (o / 2 ^ (ρ + N * K)) Sym.mark (S bOS) _ rfl
            (by simp +decide [btSt]))
          (runs_dropFW xk bP (2 ^ (ρ + N * K)) Sym.mark (S bP) _ rfl
            (by simp +decide [btSt]))))) (btChain_clean S _ _ _ _ _))
      (fun _ _ => trivial) (by omega)
  have hall := WP.W9comp.runs_seq hset (WP.W9comp.runs_seq (RunsIn.iff_runs.mp hcd) hcl)
  refine WP.W9comp.runs_mono hall (fun _ _ => trivial) ?_
  have hcdc := countdownCost_le (fun _ => 4 * opCost xk B + 4) N
  rw [btSumConst] at hcdc
  have hWN : 20 * N ≤ opCost xk B * N := Nat.mul_le_mul_right N (by omega)
  have e3 : N * (4 * opCost xk B + 4) = 4 * (opCost xk B * N) + 4 * N := by ring
  have e4 : 12 * opCost xk B * (N + 1) = 12 * (opCost xk B * N) + 12 * opCost xk B := by ring
  omega

end SubNLogN.Machine.AppC.C7BadTriAux
