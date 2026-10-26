/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.UnitMulMath

/-!
# K5-unit, programs and state kit (`K1/UnitMulProg.lean`)

**Scope (honest summary).** Programs of the unit-multiplication kernel (`K5UnitMulMixStmt q a d`,
`SubNLogN/Machine/Contracts/Streams.lean` §5) and generic proved lemmas (no contract here).

**Plan ([OAI26, §2.1, proof of Lemma 4], the residue-class construction; paper:
Fact 3.3(4) (`fact:oai-streams`), Lemma A.4 (`lem:transfer-streams`)).** Layout `L5 n n`,
`n = max a d`: token counters `Z_j` and streams `X_j`, `j < n`. Register
`(Q mod a, Q mod d, u mod a, t mod d)` with `Q = q^b`; it determines the classes
`jA = jIdx a Q u` and `jD = jIdx d Q t` (`jA_regU`, `jD_regU`). Per fiber of `Q` blocks of `s`
records (the depth stack holds `b` tokens; `recProg` runs a step `Q` times):
* pass A (multiplication by `a`): count (block `u` to the store `NEG5`, a token on `Z_{jA u}`),
  cut (piece `j` = the next `count_j` blocks, from the top of the store, onto `X_j`), merge
  (block `u` of the output = the next block of `X_{jA u}`) onto `TMP25`, rewound onto `MID5`;
* pass D (division by `d`): distribute (block `t` of `MID5` onto `X_{jD t}`), concatenate
  `X_0, …, X_{n-1}` onto `CAT5`, rewound onto the accumulator.
Correctness: `mulA_cut`, `mulA_cat`, `divD_correct`, `unitFib_eq` (`K1/UnitMulMath.lean`).
Cost per fiber `O(vol + n·Q)`, `Q ≤ vol`; setup `O(b)`, `b < q^b ≤ V`.

Families are indexed by the compile-time `n` only; runtime counts live on stacks.
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts Computability

/-- Register of the unit kernel: `(Q mod a, Q mod d, u mod a, t mod d)`. -/
abbrev MU (a d : ℕ) : Type := ZMod a × ZMod d × ZMod a × ZMod d

/-- Unit kernel programs: `n` token counters, `n` streams. -/
abbrev PU (n a d : ℕ) : Type := KP (L5 n n) (MU a d)

section Sel

variable {a d : ℕ}

/-- Pass A class of the current block, `jIdx a Q u` from `(Q mod a, u mod a)`. -/
def jA (r : Option Sym × MU a d) : ℕ := ((-r.2.2.2.1) * r.2.1⁻¹).val

/-- Pass D class of the current block, `jIdx d Q t` from `(Q mod d, t mod d)`. -/
def jD (r : Option Sym × MU a d) : ℕ := ((-r.2.2.2.2) * r.2.2.1⁻¹).val

/-- Register value `(Q, Q, u, t)`. -/
def regU (a d Q u t : ℕ) : MU a d := ((Q : ZMod a), (Q : ZMod d), (u : ZMod a), (t : ZMod d))

theorem jA_regU (Q u t : ℕ) (o : Option Sym) : jA (o, regU a d Q u t) = jIdx a Q u := rfl

theorem jD_regU (Q u t : ℕ) (o : Option Sym) : jD (o, regU a d Q u t) = jIdx d Q t := rfl

/-- `u := u + 1`. -/
def incAf (m : MU a d) : MU a d := (m.1, m.2.1, m.2.2.1 + 1, m.2.2.2)

/-- `t := t + 1`. -/
def incDf (m : MU a d) : MU a d := (m.1, m.2.1, m.2.2.1, m.2.2.2 + 1)

/-- `u, t := 0`. -/
def rstf (m : MU a d) : MU a d := (m.1, m.2.1, 0, 0)

/-- `(Q mod a, Q mod d) := (1, 1)`, `u, t := 0`. -/
def initf (_ : MU a d) : MU a d := (1, 1, 0, 0)

/-- `Q := Q·q`. -/
def mulQf (q : ℕ) (m : MU a d) : MU a d := (m.1 * q, m.2.1 * q, m.2.2.1, m.2.2.2)

theorem incAf_regU (Q u t : ℕ) : incAf (regU a d Q u t) = regU a d Q (u + 1) t := by
  simp [incAf, regU]

theorem incDf_regU (Q u t : ℕ) : incDf (regU a d Q u t) = regU a d Q u (t + 1) := by
  simp [incDf, regU]

theorem rstf_regU (Q u t : ℕ) : rstf (regU a d Q u t) = regU a d Q 0 0 := by
  simp [rstf, regU]

theorem initf_eq (q : ℕ) (m : MU a d) : initf m = regU a d (q ^ 0) 0 0 := by
  simp [initf, regU]

theorem mulQf_regU (q i : ℕ) : mulQf q (regU a d (q ^ i) 0 0) = regU a d (q ^ (i + 1)) 0 0 := by
  simp [mulQf, regU, pow_succ]

end Sel

/-! ## Stack selectors and states with `ℕ`-indexed families -/

section States

variable {n : ℕ}

/-- Token counter `j` (`j < n`). -/
def zst (j : ℕ) : L5 n n := if h : j < n then ZS5 ⟨j, h⟩ else SG5 8

/-- Stream `j` (`j < n`). -/
def xst (j : ℕ) : L5 n n := if h : j < n then XS5 ⟨j, h⟩ else SG5 8

/-- A state whose families are given by `ℕ`-indexed functions. -/
abbrev mkF (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zF xF : ℕ → List Sym) :
    L5 n n → List Sym :=
  mk5 nm sg (fun i => zF i.val) (fun i => xF i.val)

theorem zst_of_lt {j : ℕ} (hj : j < n) : zst (n := n) j = ZS5 ⟨j, hj⟩ := dif_pos hj

theorem xst_of_lt {j : ℕ} (hj : j < n) : xst (n := n) j = XS5 ⟨j, hj⟩ := dif_pos hj

theorem update_finval (F : ℕ → List Sym) (j : ℕ) (hj : j < n) (v : List Sym) :
    Function.update (fun i : Fin n => F i.val) ⟨j, hj⟩ v = fun i => Function.update F j v i.val := by
  funext i
  by_cases h : i.val = j
  · have : i = ⟨j, hj⟩ := Fin.ext h
    subst this
    simp
  · rw [Function.update_of_ne (fun h' => h (by rw [h'])), Function.update_of_ne h]

variable (nm : Fin 4 → List Sym) (sg : Fin 9 → List Sym) (zF xF : ℕ → List Sym)

theorem mkF_nm (i : Fin 4) : mkF (n := n) nm sg zF xF (.inl i) = nm i := rfl

theorem mkF_sg (j : Fin 9) : mkF (n := n) nm sg zF xF (.inr (.inl j)) = sg j := rfl

theorem mkF_zst {j : ℕ} (hj : j < n) : mkF (n := n) nm sg zF xF (zst j) = zF j := by
  rw [zst_of_lt hj]
  rfl

theorem mkF_xst {j : ℕ} (hj : j < n) : mkF (n := n) nm sg zF xF (xst j) = xF j := by
  rw [xst_of_lt hj]
  rfl

theorem updF_nm (i : Fin 4) (v : List Sym) :
    Function.update (mkF (n := n) nm sg zF xF) (.inl i) v = mkF (Function.update nm i v) sg zF xF :=
  upd5_nm _ _ _ _ i v

theorem updF_sg (j : Fin 9) (v : List Sym) :
    Function.update (mkF (n := n) nm sg zF xF) (.inr (.inl j)) v =
      mkF nm (Function.update sg j v) zF xF :=
  upd5_sg _ _ _ _ j v

theorem updF_zst {j : ℕ} (hj : j < n) (v : List Sym) :
    Function.update (mkF (n := n) nm sg zF xF) (zst j) v = mkF nm sg (Function.update zF j v) xF := by
  rw [zst_of_lt hj, upd5_zs, update_finval zF j hj v]

theorem updF_xst {j : ℕ} (hj : j < n) (v : List Sym) :
    Function.update (mkF (n := n) nm sg zF xF) (xst j) v = mkF nm sg zF (Function.update xF j v) := by
  rw [xst_of_lt hj, upd5_xs, update_finval xF j hj v]

omit nm sg zF xF in
theorem mkF_ext {nm nm' : Fin 4 → List Sym} {sg sg' : Fin 9 → List Sym} {zF zF' xF xF' : ℕ → List Sym}
    (h1 : nm = nm') (h2 : sg = sg') (h3 : ∀ j < n, zF j = zF' j) (h4 : ∀ j < n, xF j = xF' j) :
    mkF (n := n) nm sg zF xF = mkF nm' sg' zF' xF' := by
  subst h1 h2
  refine mk5_ext rfl rfl ?_ ?_
  · funext i
    exact h3 i.val i.isLt
  · funext i
    exact h4 i.val i.isLt

end States

section Distinct

variable {n : ℕ} {j : ℕ}

theorem zst_ne_sg (hj : j < n) (k : Fin 9) : zst (n := n) j ≠ SG5 k := by
  rw [zst_of_lt hj]; intro h; cases h

theorem xst_ne_sg (hj : j < n) (k : Fin 9) : xst (n := n) j ≠ SG5 k := by
  rw [xst_of_lt hj]; intro h; cases h

theorem zst_ne_nm (hj : j < n) (i : Fin 4) : zst (n := n) j ≠ .inl i := by
  rw [zst_of_lt hj]; intro h; cases h

theorem xst_ne_nm (hj : j < n) (i : Fin 4) : xst (n := n) j ≠ .inl i := by
  rw [xst_of_lt hj]; intro h; cases h

end Distinct

/-! ## Generic: counted sequences and dispatch -/

section Generic

variable {K M : Type}

/-- `forN f k` runs `f (k-1), …, f 1, f 0`. -/
def forN (f : ℕ → KP K M) : ℕ → KP K M
  | 0 => Lib.skip
  | k + 1 => .seq (f k) (forN f k)

theorem closed_forN {f : ℕ → KP K M} (h : ∀ j, (f j).Closed) : ∀ k, (forN f k).Closed
  | 0 => trivial
  | k + 1 => ⟨h k, closed_forN h k⟩

variable [DecidableEq K]

theorem runsM_dispatch {sel : Option Sym × M → ℕ} {ps : ℕ → KP K M} {m m' : M}
    {S S' : K → List Sym} {T j n : ℕ} (hj : ∀ o, sel (o, m) = j) (hjn : j < n)
    (h : RunsM (ps j) m S m' S' T) : RunsM (dispatch sel ps n) m S m' S' (T + n) := by
  intro o
  obtain ⟨o', t, ht, e⟩ := h o
  exact ⟨o', t + (n - j), by omega, eval_dispatch sel ps (hj o) e n hjn⟩

end Generic

/-! ## Programs -/

section Progs

variable {n a d : ℕ}

/-- Move one block (`s` records, `s` = the counter `SC5`) from `src` to `dst`, reversed. -/
def blkMv (src dst : L5 n n) : PU n a d := cdMove SC5 CNT5 TMP5 (mvRec src dst)

/-- Move one reversed block from `src` to `dst`, restoring its order. -/
def blkMvR (src dst : L5 n n) : PU n a d := cdMove SC5 CNT5 TMP5 (mvRev src dst)

/-- Push a `mark`. -/
def pushM (k : L5 n n) : PU n a d := lift (Lib.pushC k .mark)

/-- Pop the top symbol. -/
def popM (k : L5 n n) : PU n a d := lift (Lib.popR k)

/-- Register update. -/
def ldU (f : MU a d → MU a d) : PU n a d := .load fun r => (r.1, f r.2)

/-- Pass A, count step: block `u` to the store, a token on `Z_{jA u}`, `u := u + 1`. -/
def actA1 (n a d : ℕ) : PU n a d :=
  .seq (blkMv SRC5 NEG5) (.seq (dispatch jA (fun j => lift (Lib.pushC (zst j) tok)) n) (ldU incAf))

/-- Pass A, cut piece `j`: for each token on `Z_j`, a block from the store onto `X_j`. -/
def cutPiece (j : ℕ) : PU n a d :=
  whileTop (zst j) isTokS (.seq (popM (zst j)) (blkMvR NEG5 (xst j)))

/-- Pass A, merge step: the next block of `X_{jA u}` onto `TMP25`, `u := u + 1`. -/
def actA2 (n a d : ℕ) : PU n a d :=
  .seq (dispatch jA (fun j => blkMv (xst j) TMP25) n) (ldU incAf)

/-- Pass D, distribute step: block `t` of `MID5` onto `X_{jD t}`, `t := t + 1`. -/
def actD (n a d : ℕ) : PU n a d :=
  .seq (dispatch jD (fun j => blkMv MID5 (xst j)) n) (ldU incDf)

/-- Pass A, phase 1: marks, count. -/
def phA1 (q n a d : ℕ) : PU n a d :=
  .seq (ldU rstf) (.seq (pushM NEG5) (.seq (forN (fun j => pushM (zst j)) n)
    (.seq (forN (fun j => pushM (xst j)) n) (recProg q DEP5 (actA1 n a d)))))

/-- Pass A, phase 2: cut, drop the marks of the counters and the store. -/
def phA2 (n a d : ℕ) : PU n a d :=
  .seq (forN cutPiece n) (.seq (forN (fun j => popM (zst j)) n) (popM NEG5))

/-- Pass A, phase 3: merge, drop the stream marks, rewind onto `MID5`. -/
def phA3 (q n a d : ℕ) : PU n a d :=
  .seq (ldU rstf) (.seq (pushM TMP25) (.seq (recProg q DEP5 (actA2 n a d))
    (.seq (forN (fun j => popM (xst j)) n) (rwd TMP25 MID5))))

/-- Pass D: distribute, concatenate, rewind onto the accumulator. -/
def phD (q n a d : ℕ) : PU n a d :=
  .seq (ldU rstf) (.seq (forN (fun j => pushM (xst j)) n) (.seq (pushM CAT5)
    (.seq (recProg q DEP5 (actD n a d)) (.seq (forN (fun j => rwd (xst j) CAT5) n)
      (rwd CAT5 ACC5)))))

/-- One fiber. -/
def fibU (q n a d : ℕ) : PU n a d :=
  .seq (phA1 q n a d) (.seq (phA2 n a d) (.seq (phA3 q n a d) (phD q n a d)))

/-- Setup: `b` depth tokens; the register gets `(q^b mod a, q^b mod d, 0, 0)`. -/
def setupU (q n a d : ℕ) : PU n a d :=
  .seq (ldU initf) (.seq (pushM DEP5)
    (cdMove BC5 CNT5 TMP5 (.seq (lift (Lib.pushC DEP5 tok)) (ldU (mulQf q)))))

/-- Nonempty input: setup, all fibers, clear the depth stack. -/
def mainU (q n a d : ℕ) : PU n a d :=
  .seq (setupU q n a d) (.seq (whileTop SRC5 isRecStart (fibU q n a d)) (clearDep DEP5))

/-- **The unit kernel** for `q ≥ 2` (counters are read only if the input is nonempty). -/
def mulProg (q n a d : ℕ) : PU n a d :=
  .seq (pushM ACC5) (.seq (.seq (peekO SRC5)
    (.ite (fun r => testO isRecStart r.1) (mainU q n a d) Lib.skip)) (rwd ACC5 DST5))

theorem closed_pushM (k : L5 n n) : (pushM (a := a) (d := d) k).Closed :=
  closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC])

theorem closed_popM (k : L5 n n) : (popM (a := a) (d := d) k).Closed :=
  closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.popR])

theorem closed_blkMv (src dst : L5 n n) : (blkMv (a := a) (d := d) src dst).Closed :=
  closed_cdMove _ _ _ (closed_mvRec _ _)

theorem closed_blkMvR (src dst : L5 n n) : (blkMvR (a := a) (d := d) src dst).Closed :=
  closed_cdMove _ _ _ (closed_mvRev _ _)

theorem closed_actA1 : (actA1 n a d).Closed :=
  ⟨closed_blkMv _ _, closed_dispatch _ (fun _ => closed_lift
    (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC])) n, trivial⟩

theorem closed_actA2 : (actA2 n a d).Closed :=
  ⟨closed_dispatch _ (fun _ => closed_blkMv _ _) n, trivial⟩

theorem closed_actD : (actD n a d).Closed :=
  ⟨closed_dispatch _ (fun _ => closed_blkMv _ _) n, trivial⟩

theorem closed_cutPiece (j : ℕ) : (cutPiece (n := n) (a := a) (d := d) j).Closed :=
  closed_whileTop _ _ ⟨closed_popM _, closed_blkMvR _ _⟩

theorem closed_fibU (q : ℕ) : (fibU q n a d).Closed :=
  ⟨⟨trivial, closed_pushM _, closed_forN (fun _ => closed_pushM _) n,
      closed_forN (fun _ => closed_pushM _) n, closed_recProg q _ closed_actA1⟩,
    ⟨closed_forN closed_cutPiece n, closed_forN (fun _ => closed_popM _) n, closed_popM _⟩,
    ⟨trivial, closed_pushM _, closed_recProg q _ closed_actA2,
      closed_forN (fun _ => closed_popM _) n, closed_rwd _ _⟩,
    ⟨trivial, closed_forN (fun _ => closed_pushM _) n, closed_pushM _,
      closed_recProg q _ closed_actD, closed_forN (fun _ => closed_rwd _ _) n, closed_rwd _ _⟩⟩

theorem closed_mulProg (q : ℕ) : (mulProg q n a d).Closed :=
  ⟨closed_pushM _, ⟨trivial, ⟨⟨trivial, closed_pushM _, closed_cdMove _ _ _
      ⟨closed_lift (by simp [Prog.Closed, Prog.FreeBelow, Lib.pushC]), trivial⟩⟩,
    closed_whileTop _ _ (closed_fibU q), closed_clearDep _⟩, trivial⟩, closed_rwd _ _⟩

end Progs

end SubNLogN.Machine.K1.SMM
