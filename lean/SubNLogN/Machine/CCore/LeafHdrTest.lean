/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.CCore.LeafHdrBase
import SubNLogN.Machine.CCore.LeafHdrCost

/-!
# C-core leaf (1): the header (leaf) test (`CCore/LeafHdrTest.lean`)

Proves `HdrTestStmt p βn βd` (`CCore/SkelDefs.lean:181`) for all `p`, `βn`, `βd` (no extra
hypotheses): from the call descriptor `t.hdr` on top of `desc`, the kernel leaves the flag
`decide (t.k = 0 ∨ (m^k)^βd < d^βn)` in its register and restores every stack.

## Program (sub-layout `HL = Option (Fin 12)`: `none` = `desc`, `some i` = scratch `i`)
1. `phase1` (Hdr programs): copy field 1 (`d`) and field 10 (`k`) of the header onto the scratch
   stacks `Sd`, `Sk`, each above a `mark` floor (`extractField`: park the fields above the wanted
   one on `tT`, copy, move them back). `desc` is restored.
2. `peek Sk`: the flag is `true` iff the top of `Sk` is not a bit, i.e. `k = 0` (`natSyms 0 = []`).
3. `phase2` (`NatArith`): `SY := (m^βd)^k` (`powMulN`, counter on `Sk`), `SX := d^βn`
   (`βn` times `mulInPlace`, i.e. `mulN` + copy back).
4. `cmpN SY SX`: the compare register holds `ordOf ((m^βd)^k) (d^βn)`.
5. `load`: `flag := flag || (ord = lt)`.
6. `phase3`: drop the four numbers with their floors; the scratch is empty again.
The flag lives in the `Bool` component of `FReg = Bool × NatArith.Reg`; every other program is
lifted through a lens that does not touch it (`RunsF`).

## Safety and embedding
The program reads only `desc` and private scratch, which are unframed in `ccoreFramed`
(`Contracts/CCore.lean:209`). It is embedded into `KLoc (CCoreN Wn) (Fin 12)` by `Prog.mapStk`;
`readsIn_of_forall` gives the read footprint and `SafeRunsIn.of_runs_readsIn` the safe run.

## Cost
`C · t.volG` with `P₀ = 1`: the header terms are bounded by `t.volG` field by field (and the
`d`-band for `bitLen d`), `powMulN` costs `O((k+1)^3) ≤ O(m^k) ≤ O(D) ≤ O(t.volG)`, the `βn`
multiplications and the comparison cost `O((bitLen d + 1)^2) = O(P)` (`LeafHdrCost.lean`).
Paper: the leaf stopping test `e^{βd} < d^{βn}` of Proposition A.11 (`prop:prop14-param`)
and Remark A.12 (`rem:transfer-guard`), Section A.6 (`sec:transfer-layer`).
-/

namespace SubNLogN.Machine.CCore.LeafHdrAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability

/-! ## Layout -/

/-- Sub-layout of the header-test kernel: `none` is `desc`, `some i` is scratch stack `i`. -/
abbrev HL : Type := Option (Fin 12)

/-- `desc`. -/
abbrev hDsc : HL := none
/-- Copy of `d`. -/
abbrev hSd : HL := some 0
/-- Copy of `k` (also the counter of `powMulN`). -/
abbrev hSk : HL := some 1
/-- `(m^βd)^k`. -/
abbrev hSY : HL := some 2
/-- `d^βn`. -/
abbrev hSX : HL := some 3
/-- Product destination of `mulN` / `powMulN`. -/
abbrev hZ : HL := some 4
/-- Temporaries of `mulN`. -/
abbrev hA : HL := some 5
abbrev hBs : HL := some 6
abbrev hAcc : HL := some 7
abbrev hT : HL := some 8
/-- Loop counter of `powMulN`. -/
abbrev hKc : HL := some 9
/-- Field parking stack (and counter temporary). -/
abbrev hTt : HL := some 10
/-- Copy temporary. -/
abbrev hQ : HL := some 11

/-- Embedding of the sub-layout into the kernel layout `KLoc (CCoreN Wn) (Fin 12)`. -/
def hEmb : HL → CL (Fin 12)
  | none => descL
  | some i => .inr i

theorem hEmb_injective : Function.Injective hEmb := by
  intro a b h
  cases a <;> cases b <;> simp_all [hEmb]

/-! ## Program -/

/-- Phase 1: copy `d` (field 1) and `k` (field 10) onto `Sd`, `Sk` above `mark` floors. -/
def htPhase1 : SProg HL :=
  .seq (pushC hSd .mark) (.seq (extractField 1 hDsc hSd hTt hQ)
    (.seq (pushC hSk .mark) (extractField 10 hDsc hSk hTt hQ)))

/-- Phase 2: `SY := (m^βd)^k`, `SX := d^βn`. -/
def htPhase2 (βn βd : ℕ) : Prog HL (fun _ => Sym) NatArith.Reg :=
  .seq (NatArith.pushMark hSY) (.seq (NatArith.pushNat hSY 1)
    (.seq (NatArith.powMulN hSY (mn ^ βd) hSk hKc hTt hQ hZ hA hBs hAcc)
    (.seq (NatArith.pushMark hSX) (.seq (NatArith.pushNat hSX 1)
      (mulPow βn hSX hSd hZ hA hBs hAcc hT hQ)))))

/-- Phase 3: drop the four numbers with their floors. -/
def htPhase3 : Prog HL (fun _ => Sym) NatArith.Reg :=
  .seq (NatArith.dropF hSX) (.seq (NatArith.dropF hSY) (.seq (NatArith.dropF hSk)
    (NatArith.dropF hSd)))

/-- The flag update after the comparison. -/
def htFlag (v : FReg) : FReg := (v.1 || decide (v.2.2.2.2.2 = Ordering.lt), v.2)

/-- **The header-test program** on the sub-layout. -/
def hdrTestL (βn βd : ℕ) : Prog HL (fun _ => Sym) FReg :=
  .seq (htPhase1.liftRegs lS) (.seq (.peek hSk (fun v o => (!optIsBit o, v.2)))
    (.seq ((htPhase2 βn βd).liftRegs lN) (.seq ((NatArith.cmpN hSY hSX hA hBs).liftRegs lN)
      (.seq (.load htFlag) (htPhase3.liftRegs lN)))))

theorem closed_htPhase1 : htPhase1.Closed :=
  ⟨by simp [Prog.FreeBelow, pushC], closed_extractField _ _ _ _ _,
    by simp [Prog.FreeBelow, pushC], closed_extractField _ _ _ _ _⟩

theorem closed_htPhase2 (βn βd : ℕ) : (htPhase2 βn βd).Closed :=
  ⟨NatArith.closed_pushMark _, NatArith.closed_pushNat _ _, NatArith.closed_powMulN _ _ _ _ _ _ _ _ _ _,
    NatArith.closed_pushMark _, NatArith.closed_pushNat _ _, closed_mulPow _ _ _ _ _ _ _ _ _⟩

theorem closed_htPhase3 : htPhase3.Closed :=
  ⟨NatArith.closed_dropF _, NatArith.closed_dropF _, NatArith.closed_dropF _,
    NatArith.closed_dropF _⟩

theorem closed_hdrTestL (βn βd : ℕ) : (hdrTestL βn βd).Closed :=
  ⟨WP.W9comp.closed_liftRegs _ closed_htPhase1, by simp [Prog.FreeBelow],
    WP.W9comp.closed_liftRegs _ (closed_htPhase2 βn βd),
    WP.W9comp.closed_liftRegs _ (WP.W3.closed_of_noRec rfl),
    by simp [Prog.FreeBelow], WP.W9comp.closed_liftRegs _ closed_htPhase3⟩

end SubNLogN.Machine.CCore.LeafHdrAux

namespace SubNLogN.Machine.CCore.LeafHdrAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability

/-! ## Runs facts of the phases -/

section MulPowRuns

variable {K : Type} [DecidableEq K]

/-- **`mulPow n`**, exact: `x = natSyms a ++ rx` becomes `natSyms (a * b ^ n) ++ rx`. -/
theorem runs_mulPow {x y z A Bs Acc T tmp : K} (h : [x, y, z, A, Bs, Acc, T].Nodup)
    (hxt : x ≠ tmp) (hzt : z ≠ tmp) (n a b : ℕ) (rx ry : List Sym) (S : K → List Sym)
    (hrx : TermOK rx) (hry : TermOK ry) (hz : TermOK (S z)) (hx : S x = natSyms a ++ rx)
    (hy : S y = natSyms b ++ ry) :
    Runs (mulPow n x y z A Bs Acc T tmp) S (Function.update S x (natSyms (a * b ^ n) ++ rx))
      (fun _ => True) (((List.range n).map fun j => mulStepCost (a * b ^ j) b).sum + 1) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hxy, hxz, -, -, -, -⟩, -, -, -, -, -⟩ := h'
  have hS0 : Function.update S x (natSyms (a * b ^ 0) ++ rx) = S := by
    rw [pow_zero, Nat.mul_one, ← hx, Function.update_eq_self]
  have r := runs_forEachRange n (fun _ => mulInPlace x y z A Bs Acc T tmp)
    (fun j => mulStepCost (a * b ^ j) b)
    (fun j => Function.update S x (natSyms (a * b ^ j) ++ rx)) (fun j _ => by
      have r0 := runs_mulInPlace h hxt hzt (a * b ^ j) b rx ry
        (Function.update S x (natSyms (a * b ^ j) ++ rx)) hrx hry
        (by rw [Function.update_of_ne (Ne.symm hxz)]; exact hz) (Function.update_self _ _ _)
        (by rw [Function.update_of_ne (Ne.symm hxy)]; exact hy)
      rw [Function.update_idem, show a * b ^ j * b = a * b ^ (j + 1) by ring] at r0
      exact r0)
  simp only [hS0] at r
  exact r

end MulPowRuns

/-- The top of `natSyms k ++ [mark]` is a bit iff `k ≠ 0`. -/
theorem not_optIsBit_head (k : ℕ) :
    (!optIsBit (natSyms k ++ [Sym.mark]).head?) = decide (k = 0) := by
  by_cases hk : k = 0
  · subst hk
    rw [NatArith.natSyms_zero]
    rfl
  · obtain ⟨d, L, hdL⟩ := NatArith.natSyms_cons_of_ne hk
    rw [hdL]
    simp [optIsBit, hk]

theorem termOK_markNil : TermOK [Sym.mark] := TermOK.cons rfl _

/-- The descriptor fields of a call. -/
def fsOf (t : CCoreRT) : List ℕ := [t.P, t.d, t.r, t.Δ, t.A, t.R, t.K, t.D, t.S, t.j0, t.k, t.ρ]

theorem hdr_eq (t : CCoreRT) : t.hdr = W9.hdrSyms (fsOf t) := rfl

/-- Header cost sum `Σ_f (3·bitLen f + 6)` over the twelve fields. -/
def hdrSum (t : CCoreRT) : ℕ := ((fsOf t).map fun f => 3 * bitLen f + 6).sum

theorem sum_map_take_le (f : ℕ → ℕ) (l : List ℕ) (i : ℕ) :
    ((l.take i).map f).sum ≤ (l.map f).sum := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.map_append, List.sum_append]
  omega

/-- **Phase 1**, exact. -/
theorem runs_htPhase1 (t : CCoreRT) (tdesc : List Sym) (S : HL → List Sym)
    (hd : S hDsc = t.hdr ++ tdesc) (h1 : S hSd = []) (h2 : S hSk = []) (h3 : S hTt = []) :
    Runs htPhase1 S (Function.update (Function.update S hSd (natSyms t.d ++ [Sym.mark])) hSk
      (natSyms t.k ++ [Sym.mark])) (fun _ => True)
      (4 * hdrSum t + 7 * bitLen t.d + 7 * bitLen t.k + 20) := by
  have r1 := runs_pushC hSd Sym.mark S
  rw [h1] at r1
  have r2 : Runs (extractField 1 hDsc hSd hTt hQ) (Function.update S hSd [Sym.mark])
      (Function.update S hSd (natSyms t.d ++ [Sym.mark])) (fun _ => True)
      (2 * (((fsOf t).take 1).map fun f => 3 * bitLen f + 6).sum + 7 * bitLen t.d + 9) := by
    refine WP.W9comp.runs_congr (runs_extractField (d := hDsc) (dst := hSd) (t := hTt) (tmp := hQ)
      (by decide) (by decide) (by decide) (by decide) (by decide) (i := 1) (fs := fsOf t)
      (by simp [fsOf]) tdesc (Function.update S hSd [Sym.mark]) ?_ ?_) ?_
    · rw [Function.update_of_ne (by decide), hd]; rfl
    · rw [Function.update_of_ne (by decide), h3]; exact TermOK.nil
    · rw [Function.update_idem, Function.update_self]; rfl
  have hS2k : Function.update S hSd (natSyms t.d ++ [Sym.mark]) hSk = [] := by
    rw [Function.update_of_ne (by decide), h2]
  have r3 := runs_pushC hSk Sym.mark (Function.update S hSd (natSyms t.d ++ [Sym.mark]))
  rw [hS2k] at r3
  have r4 : Runs (extractField 10 hDsc hSk hTt hQ)
      (Function.update (Function.update S hSd (natSyms t.d ++ [Sym.mark])) hSk [Sym.mark])
      (Function.update (Function.update S hSd (natSyms t.d ++ [Sym.mark])) hSk
        (natSyms t.k ++ [Sym.mark])) (fun _ => True)
      (2 * (((fsOf t).take 10).map fun f => 3 * bitLen f + 6).sum + 7 * bitLen t.k + 9) := by
    refine WP.W9comp.runs_congr (runs_extractField (d := hDsc) (dst := hSk) (t := hTt) (tmp := hQ)
      (by decide) (by decide) (by decide) (by decide) (by decide) (i := 10) (fs := fsOf t)
      (by simp [fsOf]) tdesc _ ?_ ?_) ?_
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hd]; rfl
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), h3]
      exact TermOK.nil
    · rw [Function.update_idem, Function.update_self]; rfl
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 r4))) (fun _ _ => trivial) ?_
  have e1 := sum_map_take_le (fun f => 3 * bitLen f + 6) (fsOf t) 1
  have e2 := sum_map_take_le (fun f => 3 * bitLen f + 6) (fsOf t) 10
  simp only [hdrSum] at e1 e2 ⊢
  omega

theorem one_le_mn_pow (n : ℕ) : 1 ≤ mn ^ n := Nat.one_le_pow _ _ (by norm_num [mn, tripleM])

/-- **Phase 2**, exact: `SY := (m^βd)^k`, `SX := d^βn`, above `mark` floors. -/
theorem runs_htPhase2 (βn βd d k : ℕ) (S : HL → List Sym)
    (hd' : S hSd = natSyms d ++ [Sym.mark]) (hk' : S hSk = natSyms k ++ [Sym.mark])
    (hY : S hSY = []) (hX : S hSX = []) (hz' : S hZ = []) :
    Runs (htPhase2 βn βd) S
      (Function.update (Function.update S hSY (natSyms ((mn ^ βd) ^ k) ++ [Sym.mark])) hSX
        (natSyms (d ^ βn) ++ [Sym.mark])) (fun _ => True)
      (NatArith.powCost (mn ^ βd) 1 k +
        ((List.range βn).map fun j => mulStepCost (1 * d ^ j) d).sum + 9) := by
  have r1 := NatArith.runs_pushMark hSY S
  rw [hY] at r1
  have r2 := NatArith.runs_pushNat hSY 1 (Function.update S hSY [Sym.mark])
  rw [Function.update_self, Function.update_idem] at r2
  have r3 := NatArith.runs_powMulN (k := hSY) (ns := hSk) (Kc := hKc) (t := hTt) (Q := hQ)
    (Tdst := hZ) (A := hA) (Bs := hBs) (Acc := hAcc) (by decide) (mn ^ βd) (one_le_mn_pow βd) 1 k
    [Sym.mark] [Sym.mark] (Function.update S hSY (natSyms 1 ++ [Sym.mark])) termOK_markNil
    termOK_markNil (Function.update_self _ _ _)
    (by rw [Function.update_of_ne (by decide), hk'])
  rw [Function.update_idem, Nat.one_mul] at r3
  have r4 := NatArith.runs_pushMark hSX
    (Function.update S hSY (natSyms ((mn ^ βd) ^ k) ++ [Sym.mark]))
  rw [Function.update_of_ne (by decide), hX] at r4
  have r5 := NatArith.runs_pushNat hSX 1 (Function.update (Function.update S hSY
    (natSyms ((mn ^ βd) ^ k) ++ [Sym.mark])) hSX [Sym.mark])
  rw [Function.update_self, Function.update_idem] at r5
  have r6 := runs_mulPow (x := hSX) (y := hSd) (z := hZ) (A := hA) (Bs := hBs) (Acc := hAcc)
    (T := hT) (tmp := hQ) (by decide) (by decide) (by decide) βn 1 d [Sym.mark] [Sym.mark]
    (Function.update (Function.update S hSY (natSyms ((mn ^ βd) ^ k) ++ [Sym.mark])) hSX
      (natSyms 1 ++ [Sym.mark])) termOK_markNil termOK_markNil
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hz']
        exact TermOK.nil)
    (Function.update_self _ _ _)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hd'])
  rw [Function.update_idem, Nat.one_mul] at r6
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 (WP.W9comp.runs_seq r4 (WP.W9comp.runs_seq r5 r6)))))
    (fun _ _ => trivial) ?_
  have := bitLen_one_le
  omega

/-- **Phase 3**, exact: the four numbers and their floors are dropped. -/
theorem runs_htPhase3 (x y k d : ℕ) (S : HL → List Sym)
    (hX : S hSX = natSyms x ++ [Sym.mark]) (hY : S hSY = natSyms y ++ [Sym.mark])
    (hk : S hSk = natSyms k ++ [Sym.mark]) (hd : S hSd = natSyms d ++ [Sym.mark]) :
    Runs htPhase3 S (Function.update (Function.update (Function.update (Function.update S hSX [])
      hSY []) hSk []) hSd []) (fun _ => True)
      (2 * bitLen x + 2 * bitLen y + 2 * bitLen k + 2 * bitLen d + 8) := by
  have r1 := NatArith.runs_dropF hSX x Sym.mark [] S rfl hX
  have r2 := NatArith.runs_dropF hSY y Sym.mark [] (Function.update S hSX []) rfl
    (by rw [Function.update_of_ne (by decide), hY])
  have r3 := NatArith.runs_dropF hSk k Sym.mark []
    (Function.update (Function.update S hSX []) hSY []) rfl
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hk])
  have r4 := NatArith.runs_dropF hSd d Sym.mark []
    (Function.update (Function.update (Function.update S hSX []) hSY []) hSk []) rfl
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hd])
  exact WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2
    (WP.W9comp.runs_seq r3 r4))) (fun _ _ => trivial) (by omega)

end SubNLogN.Machine.CCore.LeafHdrAux

namespace SubNLogN.Machine.CCore.LeafHdrAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability

/-! ## The whole program on the sub-layout -/

/-- The cost bound of the header-test program (exact sum of the phase costs). -/
def htCost (βn βd : ℕ) (t : CCoreRT) : ℕ :=
  (4 * hdrSum t + 7 * bitLen t.d + 7 * bitLen t.k + 20) + (1 +
    ((NatArith.powCost (mn ^ βd) 1 t.k +
      ((List.range βn).map fun j => mulStepCost (1 * t.d ^ j) t.d).sum + 9) +
    ((12 * min (bitLen ((mn ^ βd) ^ t.k)) (bitLen (t.d ^ βn)) + 15) + (1 +
    (2 * bitLen (t.d ^ βn) + 2 * bitLen ((mn ^ βd) ^ t.k) + 2 * bitLen t.k +
      2 * bitLen t.d + 8)))))

/-- The flag identity: `k = 0 || ordOf ((m^βd)^k) (d^βn) = lt` is the leaf test. -/
theorem flag_eq (k d βn βd : ℕ) :
    (decide (k = 0) || decide (Lib.ordOf ((mn ^ βd) ^ k) (d ^ βn) = Ordering.lt)) =
      decide (k = 0 ∨ (mn ^ k) ^ βd < d ^ βn) := by
  have e : (mn ^ βd) ^ k = (mn ^ k) ^ βd := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [e]
  unfold Lib.ordOf
  by_cases h1 : (mn ^ k) ^ βd < d ^ βn
  · simp [h1]
  · by_cases h2 : (mn ^ k) ^ βd = d ^ βn <;> simp [h1, h2]

/-- **The header test on the sub-layout**, exact: all stacks restored, flag = the leaf test. -/
theorem runs_hdrTestL (βn βd : ℕ) (t : CCoreRT) (tdesc : List Sym) (S : HL → List Sym)
    (hd : S hDsc = t.hdr ++ tdesc) (hcl : ∀ i : Fin 12, S (some i) = []) :
    Runs (hdrTestL βn βd) S S (fun v => v.1 = decide (t.k = 0 ∨ (mn ^ t.k) ^ βd < t.d ^ βn))
      (htCost βn βd t) := by
  set S1 := Function.update (Function.update S hSd (natSyms t.d ++ [Sym.mark])) hSk
    (natSyms t.k ++ [Sym.mark]) with hS1
  set S2 := Function.update (Function.update S1 hSY (natSyms ((mn ^ βd) ^ t.k) ++ [Sym.mark]))
    hSX (natSyms (t.d ^ βn) ++ [Sym.mark]) with hS2
  set f0 := decide (t.k = 0) with hf0
  set ord := Lib.ordOf ((mn ^ βd) ^ t.k) (t.d ^ βn) with hord
  have p1 := runs_htPhase1 t tdesc S hd (hcl 0) (hcl 1) (hcl 10)
  have q1 := WP.W0m.runs_liftRegs lS p1
  have q2 : Triple [] (fun s => s.stk = S1 ∧ True)
      (.peek hSk (fun (v : FReg) o => (!optIsBit o, v.2)))
      (fun s => s.stk = S1 ∧ s.var.1 = f0) 1 := by
    refine Triple.pre (Triple.peek hSk _ _) ?_
    rintro ⟨v, stk⟩ ⟨h, -⟩
    change stk = S1 at h
    subst h
    refine ⟨rfl, ?_⟩
    show (!optIsBit (S1 hSk).head?) = decide (t.k = 0)
    rw [hS1, Function.update_self]
    exact not_optIsBit_head t.k
  have p2 := runs_htPhase2 βn βd t.d t.k S1
    (by rw [hS1, Function.update_of_ne (by decide), Function.update_self])
    (by rw [hS1, Function.update_self])
    (by rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        exact hcl 2)
    (by rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        exact hcl 3)
    (by rw [hS1, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        exact hcl 4)
  have q3 := runsF_liftN p2 f0
  have q4 := triple_cmpF (x := hSY) (y := hSX) (t1 := hA) (t2 := hBs) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ((mn ^ βd) ^ t.k) (t.d ^ βn) [Sym.mark]
    [Sym.mark] S2 termOK_markNil termOK_markNil
    (by rw [hS2, Function.update_of_ne (by decide), Function.update_self])
    (by rw [hS2, Function.update_self]) f0
  have q5 : Triple [] (fun s => s.stk = S2 ∧ s.var.1 = f0 ∧ s.var.2.2.2.2.2 = ord)
      (.load htFlag) (fun s => s.stk = S2 ∧ s.var.1 = (f0 || decide (ord = Ordering.lt))) 1 := by
    refine Triple.pre (Triple.load htFlag _) ?_
    rintro ⟨v, stk⟩ ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    show (v.1 || decide (v.2.2.2.2.2 = Ordering.lt)) = _
    rw [h2, h3]
  have p3 := runs_htPhase3 (t.d ^ βn) ((mn ^ βd) ^ t.k) t.k t.d S2
    (by rw [hS2, Function.update_self])
    (by rw [hS2, Function.update_of_ne (by decide), Function.update_self])
    (by rw [hS2, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS1,
      Function.update_self])
    (by rw [hS2, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hS1,
      Function.update_of_ne (by decide), Function.update_self])
  have hS3 : Function.update (Function.update (Function.update (Function.update S2 hSX [])
      hSY []) hSk []) hSd [] = S := by
    funext x
    by_cases x0 : x = hSd
    · rw [x0, Function.update_self]; exact (hcl 0).symm
    rw [Function.update_of_ne x0]
    by_cases x1 : x = hSk
    · rw [x1, Function.update_self]; exact (hcl 1).symm
    rw [Function.update_of_ne x1]
    by_cases x2 : x = hSY
    · rw [x2, Function.update_self]; exact (hcl 2).symm
    rw [Function.update_of_ne x2]
    by_cases x3 : x = hSX
    · rw [x3, Function.update_self]; exact (hcl 3).symm
    rw [Function.update_of_ne x3, hS2, Function.update_of_ne x3, Function.update_of_ne x2, hS1,
      Function.update_of_ne x1, Function.update_of_ne x0]
  rw [hS3] at p3
  have q6 := runsF_liftN p3 (f0 || decide (ord = Ordering.lt))
  have hall := Triple.seq q1 (Triple.seq q2 (Triple.seq q3 (Triple.seq q4 (Triple.seq q5 q6))))
  refine Triple.conseq hall (fun s hs => hs) (fun s hs => ⟨hs.1, ?_⟩) (le_of_eq rfl)
  show s.var.1 = _
  rw [hs.2, hf0, hord]
  exact flag_eq t.k t.d βn βd

end SubNLogN.Machine.CCore.LeafHdrAux

namespace SubNLogN.Machine.CCore.LeafHdrAux

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus Computability

/-! ## Cost bound -/

/-- Per-step coefficient of `mulInPlace` (in units of `(bitLen d + 1)^2`). -/
def cmul (βn : ℕ) : ℕ := 100 * (βn + 2) * (βn + 3) + 11 * βn + 26

theorem mulStepCost_le {βn j d : ℕ} (hj : j < βn) :
    mulStepCost (1 * d ^ j) d ≤ cmul βn * (bitLen d + 1) ^ 2 := by
  unfold mulStepCost cmul
  have ha : bitLen (1 * d ^ j) ≤ βn * (bitLen d) + 1 := by
    rw [Nat.one_mul]
    have h1 := bitLen_pow_le d j
    have h2 : j * (bitLen d) ≤ βn * (bitLen d) := Nat.mul_le_mul_right _ hj.le
    omega
  have hab : bitLen (1 * d ^ j * d) ≤ βn * (bitLen d) + 1 := by
    rw [Nat.one_mul, ← pow_succ]
    have h1 := bitLen_pow_le d (j + 1)
    have h2 : (j + 1) * (bitLen d) ≤ βn * (bitLen d) := Nat.mul_le_mul_right _ hj
    omega
  have e1 : bitLen (1 * d ^ j) + 1 ≤ (βn + 2) * ((bitLen d) + 1) := by
    have : (βn + 2) * ((bitLen d) + 1) = βn * (bitLen d) + βn + 2 * (bitLen d) + 2 := by ring
    omega
  have e2 : bitLen (1 * d ^ j) + (bitLen d) + 2 ≤ (βn + 3) * ((bitLen d) + 1) := by
    have : (βn + 3) * ((bitLen d) + 1) = βn * (bitLen d) + βn + 3 * (bitLen d) + 3 := by ring
    omega
  have e3 : NatArith.mulCost (1 * d ^ j) d ≤
      100 * ((βn + 2) * ((bitLen d) + 1)) * ((βn + 3) * ((bitLen d) + 1)) := by
    unfold NatArith.mulCost
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 100 e1) e2
  have h5 : (bitLen d) + 1 ≤ ((bitLen d) + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h6 : (11 * βn + 26) * ((bitLen d) + 1) ≤ (11 * βn + 26) * ((bitLen d) + 1) ^ 2 := Nat.mul_le_mul_left _ h5
  have h7 : (11 * βn + 26) * ((bitLen d) + 1) = 11 * (βn * (bitLen d)) + 11 * βn + 26 * (bitLen d) + 26 := by ring
  have e5 : 100 * ((βn + 2) * ((bitLen d) + 1)) * ((βn + 3) * ((bitLen d) + 1)) =
      100 * (βn + 2) * (βn + 3) * ((bitLen d) + 1) ^ 2 := by ring
  have e6 : (100 * (βn + 2) * (βn + 3) + 11 * βn + 26) * ((bitLen d) + 1) ^ 2 =
      100 * (βn + 2) * (βn + 3) * ((bitLen d) + 1) ^ 2 + (11 * βn + 26) * ((bitLen d) + 1) ^ 2 := by ring
  omega

theorem powCost_le (βd k : ℕ) :
    NatArith.powCost (mn ^ βd) 1 k ≤ 200 * (bitLen (mn ^ βd) + 3) ^ 2 * (k + 1) ^ 3 := by
  unfold NatArith.powCost
  set b := bitLen (mn ^ βd) with hb
  have h1 : bitLen (1 * (mn ^ βd) ^ k) ≤ k * b + 1 := by
    rw [Nat.one_mul]; exact bitLen_pow_le _ k
  have h2 : bitLen (1 * (mn ^ βd) ^ k) + b + 2 ≤ (k + 1) * (b + 3) := by
    have : (k + 1) * (b + 3) = k * b + 3 * k + b + 3 := by ring
    omega
  calc (k + 1) * (200 * (bitLen (1 * (mn ^ βd) ^ k) + b + 2) ^ 2)
      ≤ (k + 1) * (200 * ((k + 1) * (b + 3)) ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 2))
    _ = 200 * (b + 3) ^ 2 * (k + 1) ^ 3 := by ring

/-- The cost constant of the header test (depends on `p`, `βn`, `βd` only). -/
noncomputable def htC (p : LayerParams) (βn βd : ℕ) : ℕ :=
  600 + 200 * (bitLen (mn ^ βd) + 3) ^ 2 + 2 * bitLen (mn ^ βd) +
    (βn * cmul βn + 14 * βn + 21) * dConst p

/-- **Cost bound**: under the bands (cutoff `P₀ = 1`), `htCost βn βd t ≤ htC p βn βd · t.volG`. -/
theorem htCost_le {p : LayerParams} {βn βd : ℕ} {t : CCoreRT} (h : CCoreBands p 1 t) :
    htCost βn βd t ≤ htC p βn βd * t.volG := by
  obtain ⟨hPV, hrV, hΔV, hAV, hRV, hKV, hDV, hSV, hjV, hkV, hρV, hk3, hV1⟩ := fields_le_volG h
  have hX := bitLen_d_sq_le h.1 h.2.2.1
  have hh : hdrSum t ≤ 33 * t.volG + 3 * bitLen t.d + 72 := by
    have b0 := WP.W0m.bitLen_le_self t.P
    have b2 := WP.W0m.bitLen_le_self t.r
    have b3 := WP.W0m.bitLen_le_self t.Δ
    have b4 := WP.W0m.bitLen_le_self t.A
    have b5 := WP.W0m.bitLen_le_self t.R
    have b6 := WP.W0m.bitLen_le_self t.K
    have b7 := WP.W0m.bitLen_le_self t.D
    have b8 := WP.W0m.bitLen_le_self t.S
    have b9 := WP.W0m.bitLen_le_self t.j0
    have b10 := WP.W0m.bitLen_le_self t.k
    have b11 := WP.W0m.bitLen_le_self t.ρ
    simp only [hdrSum, fsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have hkk : bitLen t.k ≤ t.volG := le_trans (WP.W0m.bitLen_le_self _) hkV
  have hpw : NatArith.powCost (mn ^ βd) 1 t.k ≤ 200 * (bitLen (mn ^ βd) + 3) ^ 2 * t.volG :=
    le_trans (powCost_le βd t.k) (Nat.mul_le_mul_left _ hk3)
  have hml : ((List.range βn).map fun j => mulStepCost (1 * t.d ^ j) t.d).sum ≤
      βn * (cmul βn * (bitLen t.d + 1) ^ 2) :=
    NatArith.sum_range_le βn (fun j hj => mulStepCost_le hj)
  have hdp : bitLen (t.d ^ βn) ≤ βn * bitLen t.d + 1 := bitLen_pow_le _ _
  have hbp : bitLen ((mn ^ βd) ^ t.k) ≤ t.k * bitLen (mn ^ βd) + 1 := bitLen_pow_le _ _
  have hmin : min (bitLen ((mn ^ βd) ^ t.k)) (bitLen (t.d ^ βn)) ≤ bitLen (t.d ^ βn) :=
    min_le_right _ _
  unfold htCost htC
  set V := t.volG with hV
  set L := bitLen t.d with hL
  set b := bitLen (mn ^ βd) with hb
  set Dc := dConst p with hDc
  set X := (L + 1) ^ 2 with hXd
  have hXV : X ≤ Dc * V := le_trans hX (Nat.mul_le_mul_left _ hPV)
  have hLX : L + 1 ≤ X := Nat.le_self_pow (by norm_num) _
  have hkb : t.k * b ≤ V * b := Nat.mul_le_mul_right _ hkV
  have hbL : βn * L ≤ βn * X := Nat.mul_le_mul_left _ (by omega)
  have hcX : (βn * cmul βn + 14 * βn + 21) * X ≤ (βn * cmul βn + 14 * βn + 21) * (Dc * V) :=
    Nat.mul_le_mul_left _ hXV
  have hK2 : (βn * cmul βn + 14 * βn + 21) * X = βn * (cmul βn * X) + 14 * (βn * X) + 21 * X := by
    ring
  have hR : (600 + 200 * (b + 3) ^ 2 + 2 * b + (βn * cmul βn + 14 * βn + 21) * Dc) * V =
      600 * V + 200 * (b + 3) ^ 2 * V + 2 * (V * b) + (βn * cmul βn + 14 * βn + 21) * (Dc * V) := by
    ring
  rw [hR]
  omega

end SubNLogN.Machine.CCore.LeafHdrAux

namespace SubNLogN.Machine.CCore

open TMFw TMFw.Contracts TMFw.Lib SubNLogN.Machine.Calculus

/-- **[LEAF (1)] `HdrTestStmt p βn βd` holds**, for every `p`, `βn`, `βd`
(`CCore/SkelDefs.lean:181`). Cutoff `P₀ = 1`; kernel: scratch `E = Fin 12`, register
`FReg = Bool × NatArith.Reg`, observation `obs v = v.1`, program
`(hdrTestL βn βd).mapStk hEmb`, cost constant `htC p βn βd`. For every call `t` in the bands, every
descriptor tail `tdesc` and every state with clean scratch and `desc = t.hdr ++ tdesc`, the run is
boundary-safe for `ccoreFramed`, restores **every** stack, and ends with
`obs = decide (t.k = 0 ∨ (m^k)^βd < d^βn)`, within `htC p βn βd · t.volG` steps. -/
theorem hdrTest_holds (p : LayerParams) (βn βd : ℕ) : HdrTestStmt p βn βd := by
  refine ⟨1, LeafHdrAux.htC p βn βd, fun _ => ⟨Fin 12, inferInstance, inferInstance,
    LeafHdrAux.FReg, (LeafHdrAux.hdrTestL βn βd).mapStk LeafHdrAux.hEmb, inferInstance,
    inferInstance, LeafHdrAux.closed_mapStk _ (LeafHdrAux.closed_hdrTestL βn βd),
    fun v => v.1, ?_⟩⟩
  intro t tdesc S hB hcl hd
  have hrun := LeafHdrAux.runs_hdrTestL βn βd t tdesc (S ∘ LeafHdrAux.hEmb) hd (fun i => hcl i)
  have hrun' := LeafHdrAux.runs_mapStk_post LeafHdrAux.hEmb_injective hrun (fun _ _ => rfl)
  have hsafe := SafeRunsIn.of_runs_readsIn (framed := ccoreFramed) hrun'
    (LeafHdrAux.closed_mapStk _ (LeafHdrAux.closed_hdrTestL βn βd))
    (readsIn_mapStk LeafHdrAux.hEmb _ _ (LeafHdrAux.readsIn_of_forall (fun x => by
      cases x <;> simp [LeafHdrAux.hEmb, ccoreFramed]) _)) []
  exact SafeRunsIn.mono hsafe (fun _ h => h) (LeafHdrAux.htCost_le hB)

end SubNLogN.Machine.CCore
