/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Layer.DrvDescPiecesKit
import SubNLogN.Machine.Layer.DrvDescPiecesMath

/-!
# DrvDesc PIECES, part 3 (`Machine/Layer/DrvDescPiecesProg.lean`): the emission programs

The stacks `PL = KLoc (Fin 2) PE` of the piece-descriptor kernel (`DrvDescPiecesStmt`) and its
emission programs, with exact `Runs` rules on arbitrary states:
* `emitDesc`: push the descriptor `pdesc … j0 k` (fields copied from the field stacks, `z` and the
  table `tJ`) onto the descriptor stack;
* `innerStep`, `runs_innerLoop`: the pieces `t = c - 1, …, 0` of one table entry;
* `entryStep`, `runs_emitLoop`: all table entries, top first.

**Scope (honest summary).** Definitions and proved rules only; no contract is proved here.
-/

namespace SubNLogN.Machine.Layer.DrvDescPiecesAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability SubNLogN.Machine
open SubNLogN.Math.Networks (mH)

/-! ## Stacks -/

/-- Private stacks: the header copy `hc`, the fields `f0 … f8`, the constant `cM = mH`, the digit
loop variables `q jj pw o`, the tables `tA tO tP tJ`, the piece counter `cnt`, the offset `z`, and
temporaries `u w0 … w5`. -/
inductive PE
  | hc | f0 | f1 | f2 | f3 | f4 | f5 | f6 | f7 | f8
  | cM | q | jj | pw | o | tA | tO | tP | tJ | cnt | z
  | u | w0 | w1 | w2 | w3 | w4 | w5
  deriving DecidableEq

instance : Fintype PE :=
  Fintype.ofList [.hc, .f0, .f1, .f2, .f3, .f4, .f5, .f6, .f7, .f8, .cM, .q, .jj, .pw, .o, .tA,
    .tO, .tP, .tJ, .cnt, .z, .u, .w0, .w1, .w2, .w3, .w4, .w5] (by intro x; cases x <;> decide)

/-- The kernel's stacks. -/
abbrev PL : Type := KLoc (Fin 2) PE

/-- A private stack. -/
abbrev sx (x : PE) : PL := .inr x
/-- The value record (named stack `0`). -/
abbrev kR : PL := .inl 0
/-- The descriptor stack (named stack `1`). -/
abbrev kD : PL := .inl 1

/-! ## Helpers -/

theorem upd22 {S : PL → List Sym} {x y : PL} (hxy : x ≠ y) (A B A' B' : List Sym) :
    Function.update (Function.update (Function.update (Function.update S x A) y B) x A') y B' =
      Function.update (Function.update S x A') y B' := by
  funext k
  by_cases h1 : k = y
  · subst h1
    simp only [Function.update_self]
  · by_cases h2 : k = x
    · subst h2
      simp only [Function.update_of_ne h1, Function.update_self]
    · simp only [Function.update_of_ne h1, Function.update_of_ne h2]

theorem optIsBit_natSyms (n : ℕ) (hn : n ≠ 0) (L : List Sym) :
    optIsBit (natSyms n ++ L).head? = true := by
  have h : encodeNat n ≠ [] := fun h => hn ((TMFw.encodeNat_eq_nil_iff n).1 h)
  unfold natSyms
  generalize encodeNat n = l at h
  cases l with
  | nil => exact absurd rfl h
  | cons b bs => rfl

theorem optIsBit_zero (L : List Sym) : optIsBit (natSyms 0 ++ Sym.mark :: L).head? = false := by
  rw [NatArith.natSyms_zero]
  rfl

/-- Test: the top is not the table floor `sep`. -/
def notSep : Option Sym → Bool
  | some .sep => false
  | _ => true

theorem notSep_natSyms (n : ℕ) (L : List Sym) :
    notSep (natSyms n ++ Sym.mark :: L).head? = true := by
  unfold natSyms
  generalize encodeNat n = l
  cases l <;> rfl

/-- A table: one entry `natSyms (f x) ++ [mark]` per element (the first on top), over `sep`. -/
def tabOf (f : ℕ × ℕ × ℕ × ℕ → ℕ) (es : List (ℕ × ℕ × ℕ × ℕ)) (r : List Sym) : List Sym :=
  (es.map fun x => natSyms (f x) ++ [Sym.mark]).flatten ++ Sym.sep :: r

theorem tabOf_nil (f : ℕ × ℕ × ℕ × ℕ → ℕ) (r : List Sym) : tabOf f [] r = Sym.sep :: r := rfl

theorem tabOf_cons (f : ℕ × ℕ × ℕ × ℕ → ℕ) (x : ℕ × ℕ × ℕ × ℕ) (es : List (ℕ × ℕ × ℕ × ℕ))
    (r : List Sym) : tabOf f (x :: es) r = natSyms (f x) ++ Sym.mark :: tabOf f es r := by
  simp [tabOf]

/-- The field stacks hold the value record, each value above a `mark`. -/
def FldOK (S : PL → List Sym) (P d r a R K e Sv ρ : ℕ) : Prop :=
  (∃ x, S (sx .f0) = natSyms P ++ Sym.mark :: x) ∧ (∃ x, S (sx .f1) = natSyms d ++ Sym.mark :: x) ∧
  (∃ x, S (sx .f2) = natSyms r ++ Sym.mark :: x) ∧ (∃ x, S (sx .f3) = natSyms a ++ Sym.mark :: x) ∧
  (∃ x, S (sx .f4) = natSyms R ++ Sym.mark :: x) ∧ (∃ x, S (sx .f5) = natSyms K ++ Sym.mark :: x) ∧
  (∃ x, S (sx .f6) = natSyms e ++ Sym.mark :: x) ∧ (∃ x, S (sx .f7) = natSyms Sv ++ Sym.mark :: x) ∧
  (∃ x, S (sx .f8) = natSyms ρ ++ Sym.mark :: x)

/-- A stack that is not a field stack. -/
def NotFld (k : PL) : Prop :=
  k ≠ sx .f0 ∧ k ≠ sx .f1 ∧ k ≠ sx .f2 ∧ k ≠ sx .f3 ∧ k ≠ sx .f4 ∧ k ≠ sx .f5 ∧ k ≠ sx .f6 ∧
    k ≠ sx .f7 ∧ k ≠ sx .f8

instance (k : PL) : Decidable (NotFld k) := by unfold NotFld; infer_instance

theorem FldOK.upd {S : PL → List Sym} {P d r a R K e Sv ρ : ℕ} (h : FldOK S P d r a R K e Sv ρ)
    {k : PL} (hk : NotFld k) (L : List Sym) :
    FldOK (Function.update S k L) P d r a R K e Sv ρ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8⟩ := hk
  exact ⟨by rw [Function.update_of_ne (Ne.symm k0)]; exact h0,
    by rw [Function.update_of_ne (Ne.symm k1)]; exact h1,
    by rw [Function.update_of_ne (Ne.symm k2)]; exact h2,
    by rw [Function.update_of_ne (Ne.symm k3)]; exact h3,
    by rw [Function.update_of_ne (Ne.symm k4)]; exact h4,
    by rw [Function.update_of_ne (Ne.symm k5)]; exact h5,
    by rw [Function.update_of_ne (Ne.symm k6)]; exact h6,
    by rw [Function.update_of_ne (Ne.symm k7)]; exact h7,
    by rw [Function.update_of_ne (Ne.symm k8)]; exact h8⟩

/-- Bit-length bounds of the value record. -/
def FldB (P d r a R K e Sv ρ n : ℕ) : Prop :=
  bitLen P ≤ n ∧ bitLen d ≤ n ∧ bitLen r ≤ n ∧ bitLen a ≤ n ∧ bitLen R ≤ n ∧ bitLen K ≤ n ∧
    bitLen e ≤ n ∧ bitLen Sv ≤ n ∧ bitLen ρ ≤ n

/-! ## One descriptor -/

/-- Push `mark`, then copy the top number of `src` onto the descriptor stack. -/
def emitF (src : PE) : PP PL := .seq (pushW kD .mark) (copyW (sx src) kD (sx .u))

theorem runs_emitF (src : PE) (hsu : src ≠ .u) (S : PL → List Sym) (X : List Sym) (v : ℕ)
    (r : List Sym) (hS : S (sx src) = natSyms v ++ Sym.mark :: r) :
    Runs (emitF src) (Function.update S kD X)
      (Function.update S kD (natSyms v ++ Sym.mark :: X)) (fun _ => True) (7 * bitLen v + 8) := by
  have h1 := runs_pushW kD .mark (Function.update S kD X)
  have h2 := runs_copyW (src := sx src) (dst := kD) (tmp := sx .u) (by simp) (by simpa using hsu)
    (by simp) v (Sym.mark :: r)
    (Function.update (Function.update S kD X) kD (Sym.mark :: (Function.update S kD X) kD))
    (tok_mark _) (by simp [Function.update_apply, hS])
  refine pseq h1 (pweak h2 ?_ le_rfl) (by omega)
  simp only [Function.update_idem, Function.update_self]

/-- Push the descriptor `pdesc … j0 k`, fields from `f0 … f8`, `j0` from `z`, `k` from `tJ`. -/
def emitDesc : PP PL :=
  .seq (emitF .f8) (.seq (emitF .tJ) (.seq (emitF .z) (.seq (emitF .f7) (.seq (emitF .f6)
    (.seq (emitF .f5) (.seq (emitF .f4) (.seq (emitF .f3) (.seq (emitF .f0) (.seq (emitF .f2)
      (.seq (emitF .f1) (emitF .f0)))))))))))

theorem runs_emitDesc (S : PL → List Sym) (P d r a R K e Sv ρ j0 k : ℕ) (rz rJ : List Sym)
    (hF : FldOK S P d r a R K e Sv ρ) (hz : S (sx .z) = natSyms j0 ++ Sym.mark :: rz)
    (hJ : S (sx .tJ) = natSyms k ++ Sym.mark :: rJ) :
    Runs emitDesc S (Function.update S kD (pdesc P d r a R K e Sv ρ j0 k ++ S kD))
      (fun _ => True)
      (7 * (2 * bitLen P + bitLen d + bitLen r + bitLen a + bitLen R + bitLen K + bitLen e +
        bitLen Sv + bitLen j0 + bitLen k + bitLen ρ) + 96) := by
  obtain ⟨⟨x0, h0⟩, ⟨x1, h1⟩, ⟨x2, h2⟩, ⟨x3, h3⟩, ⟨x4, h4⟩, ⟨x5, h5⟩, ⟨x6, h6⟩, ⟨x7, h7⟩,
    ⟨x8, h8⟩⟩ := hF
  have H := pseq (runs_emitF .f8 (by decide) S (S kD) ρ x8 h8)
    (pseq (runs_emitF .tJ (by decide) S _ k rJ hJ)
    (pseq (runs_emitF .z (by decide) S _ j0 rz hz)
    (pseq (runs_emitF .f7 (by decide) S _ Sv x7 h7)
    (pseq (runs_emitF .f6 (by decide) S _ e x6 h6)
    (pseq (runs_emitF .f5 (by decide) S _ K x5 h5)
    (pseq (runs_emitF .f4 (by decide) S _ R x4 h4)
    (pseq (runs_emitF .f3 (by decide) S _ a x3 h3)
    (pseq (runs_emitF .f0 (by decide) S _ P x0 h0)
    (pseq (runs_emitF .f2 (by decide) S _ r x2 h2)
    (pseq (runs_emitF .f1 (by decide) S _ d x1 h1)
      (runs_emitF .f0 (by decide) S _ P x0 h0)
      le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl) le_rfl
  rw [Function.update_eq_self] at H
  refine pweak H ?_ (by omega)
  simp [pdesc, hdrSyms]

/-! ## The pieces of one entry -/

/-- One piece: `cnt := cnt - 1` (`= t`), `z := t·pw + o`, push the descriptor, drop `z`. -/
def innerStep : PP PL :=
  .seq (decW (sx .cnt) (sx .u)) (.seq (pushW (sx .z) .mark)
    (.seq (mulP (sx .cnt) (sx .tP) (sx .z) (sx .w1) (sx .w2) (sx .w3) (sx .w4))
      (.seq (addTo (sx .z) (sx .tO) (sx .w5) (sx .w1) (sx .w2) (sx .w3))
        (.seq emitDesc (dropFW (sx .z))))))

theorem runs_innerStep (S : PL → List Sym) (P d r a R K e Sv ρ t o pw j n : ℕ)
    (rc rO rP rJ : List Sym) (hF : FldOK S P d r a R K e Sv ρ) (hB : FldB P d r a R K e Sv ρ n)
    (hc : S (sx .cnt) = natSyms (t + 1) ++ Sym.mark :: rc)
    (hO : S (sx .tO) = natSyms o ++ Sym.mark :: rO)
    (hP : S (sx .tP) = natSyms pw ++ Sym.mark :: rP)
    (hJ : S (sx .tJ) = natSyms j ++ Sym.mark :: rJ)
    (bt : bitLen (t + 1) ≤ n) (bo : bitLen o ≤ n) (bpw : bitLen pw ≤ n) (bj : bitLen j ≤ n)
    (bz : bitLen (t * pw + o) ≤ n) :
    Runs innerStep S
      (Function.update (Function.update S (sx .cnt) (natSyms t ++ Sym.mark :: rc)) kD
        (pdesc P d r a R K e Sv ρ (o + t * pw) j ++ S kD))
      (fun _ => True) (1000 * (n + 1) ^ 2) := by
  have c1 := runs_decW (k := sx .cnt) (t := sx .u) (by decide) t (Sym.mark :: rc) S (tok_mark _) hc
  set S1 := Function.update S (sx .cnt) (natSyms t ++ Sym.mark :: rc) with hS1
  have c2 := runs_pushW (sx .z) .mark S1
  set S2 := Function.update S1 (sx .z) (Sym.mark :: S1 (sx .z)) with hS2
  have c3 := runs_mulP (x := sx .cnt) (y := sx .tP) (z := sx .z) (A := sx .w1) (Bs := sx .w2)
    (Acc := sx .w3) (T := sx .w4) (by decide) t pw (Sym.mark :: rc) (Sym.mark :: rP) S2
    (tok_mark _) (tok_mark _) (by simp [hS2, hS1, Function.update_apply])
    (by simp [hS2, hS1, Function.update_apply, hP])
  set S3 := Function.update S2 (sx .z) (natSyms (t * pw) ++ S2 (sx .z)) with hS3
  have c4 := runs_addTo (k := sx .z) (b := sx .tO) (t := sx .w5) (t1 := sx .w1) (t2 := sx .w2)
    (t3 := sx .w3) (by decide) (t * pw) o (Sym.mark :: S (sx .z)) (Sym.mark :: rO) S3
    (tok_mark _) (tok_mark _) (by simp [hS3, hS2, hS1, Function.update_apply])
    (by simp [hS3, hS2, hS1, Function.update_apply, hO])
  set S4 := Function.update S3 (sx .z) (natSyms (t * pw + o) ++ Sym.mark :: S (sx .z)) with hS4
  have hF4 : FldOK S4 P d r a R K e Sv ρ :=
    (((hF.upd (k := sx .cnt) (by decide) _).upd (k := sx .z) (by decide) _).upd (k := sx .z)
      (by decide) _).upd (k := sx .z) (by decide) _
  have c5 := runs_emitDesc S4 P d r a R K e Sv ρ (t * pw + o) j (S (sx .z)) rJ hF4
    (by simp [hS4]) (by simp [hS4, hS3, hS2, hS1, Function.update_apply, hJ])
  have c6 := runs_dropFW (sx .z) (t * pw + o) .mark (S (sx .z))
    (Function.update S4 kD (pdesc P d r a R K e Sv ρ (t * pw + o) j ++ S4 kD)) rfl
    (by simp [hS4, Function.update_apply])
  refine pseq c1 (pseq c2 (pseq c3 (pseq c4 (pseq c5 (pweak c6 ?_ le_rfl) le_rfl) le_rfl)
    le_rfl) le_rfl) ?_
  · clear c1 c2 c3 c4 c5 c6 hF4
    rw [Nat.add_comm (t * pw) o]
    funext k
    simp only [hS4, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := hB
    have hbt : bitLen t ≤ n := le_trans (NatArith.bitLen_mono'' (Nat.le_succ t)) bt
    have hbm : bitLen (t * pw) ≤ n :=
      le_trans (NatArith.bitLen_mono'' (Nat.le_add_right _ _)) bz
    have m1 := Nat.mul_le_mul (show bitLen t + 1 ≤ n + 1 by omega)
      (show bitLen t + bitLen pw + 2 ≤ 2 * n + 2 by omega)
    have m2 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
    unfold NatArith.mulCost
    nlinarith [m1, m2]

/-- The inner-loop state after `s` pieces of an entry with count `c`. -/
def innerSt (S : PL → List Sym) (g : ℕ → List Sym) (c : ℕ) (rc : List Sym) (s : ℕ) :
    PL → List Sym :=
  Function.update (Function.update S (sx .cnt) (natSyms (c - s) ++ Sym.mark :: rc)) kD
    (((List.range' (c - s) s).map g).flatten ++ S kD)

theorem innerSt_cnt (S : PL → List Sym) (g : ℕ → List Sym) (c : ℕ) (rc : List Sym) (s : ℕ) :
    innerSt S g c rc s (sx .cnt) = natSyms (c - s) ++ Sym.mark :: rc := by
  simp [innerSt, Function.update_apply]

theorem innerSt_kD (S : PL → List Sym) (g : ℕ → List Sym) (c : ℕ) (rc : List Sym) (s : ℕ) :
    innerSt S g c rc s kD = ((List.range' (c - s) s).map g).flatten ++ S kD := by
  simp [innerSt]

theorem innerSt_other (S : PL → List Sym) (g : ℕ → List Sym) (c : ℕ) (rc : List Sym) (s : ℕ)
    (k : PL) (h1 : k ≠ sx .cnt) (h2 : k ≠ kD) : innerSt S g c rc s k = S k := by
  simp [innerSt, Function.update_of_ne h1, Function.update_of_ne h2]

theorem range'_step (c s : ℕ) (hs : s < c) :
    List.range' (c - (s + 1)) (s + 1) = (c - (s + 1)) :: List.range' (c - s) s := by
  rw [List.range'_succ]
  congr 2
  omega

/-- **The pieces of one entry** `(c, o, pw, j)`: `t = c - 1, …, 0`, so that `t = 0` ends on top. -/
theorem runs_innerLoop (S : PL → List Sym) (P d r a R K e Sv ρ c o pw j n : ℕ)
    (rc rO rP rJ : List Sym) (hF : FldOK S P d r a R K e Sv ρ) (hB : FldB P d r a R K e Sv ρ n)
    (hc : S (sx .cnt) = natSyms c ++ Sym.mark :: rc)
    (hO : S (sx .tO) = natSyms o ++ Sym.mark :: rO)
    (hP : S (sx .tP) = natSyms pw ++ Sym.mark :: rP)
    (hJ : S (sx .tJ) = natSyms j ++ Sym.mark :: rJ)
    (bc : bitLen c ≤ n) (bo : bitLen o ≤ n) (bpw : bitLen pw ≤ n) (bj : bitLen j ≤ n)
    (bz : ∀ t < c, bitLen (t * pw + o) ≤ n) :
    Runs (whileW (sx .cnt) optIsBit innerStep) S
      (Function.update (Function.update S (sx .cnt) (natSyms 0 ++ Sym.mark :: rc)) kD
        (((List.range c).map fun t => pdesc P d r a R K e Sv ρ (o + t * pw) j).flatten ++ S kD))
      (fun _ => True) (c * (1000 * (n + 1) ^ 2 + 2) + 2) := by
  set g : ℕ → List Sym := fun t => pdesc P d r a R K e Sv ρ (o + t * pw) j with hg
  have L := runs_whileW (k := sx .cnt) (c := optIsBit) (p := innerStep) (innerSt S g c rc)
    (1000 * (n + 1) ^ 2) c
    (fun s hs => by rw [innerSt_cnt]; exact optIsBit_natSyms _ (by omega) _)
    (by rw [innerSt_cnt, Nat.sub_self]; exact optIsBit_zero _)
    (fun s hs => by
      have h := runs_innerStep (innerSt S g c rc s) P d r a R K e Sv ρ (c - s - 1) o pw j n rc
        rO rP rJ ((hF.upd (k := sx .cnt) (by decide) _).upd (k := kD) (by decide) _) hB
        (by rw [innerSt_cnt, show c - s - 1 + 1 = c - s by omega])
        (by rw [innerSt_other _ _ _ _ _ _ (by decide) (by decide)]; exact hO)
        (by rw [innerSt_other _ _ _ _ _ _ (by decide) (by decide)]; exact hP)
        (by rw [innerSt_other _ _ _ _ _ _ (by decide) (by decide)]; exact hJ)
        (le_trans (NatArith.bitLen_mono'' (by omega)) bc) bo bpw bj (bz _ (by omega))
      refine pweak h ?_ le_rfl
      rw [innerSt_kD]
      unfold innerSt
      rw [upd22 (by decide : (sx .cnt : PL) ≠ kD), show c - s - 1 = c - (s + 1) by omega,
        range'_step c s hs]
      simp [hg])
  have e0 : innerSt S g c rc 0 = S := by
    unfold innerSt
    simp only [Nat.sub_zero, List.range'_zero, List.map_nil, List.flatten_nil, List.nil_append]
    rw [← hc, Function.update_eq_self, Function.update_eq_self]
  have e1 : innerSt S g c rc c = Function.update (Function.update S (sx .cnt)
      (natSyms 0 ++ Sym.mark :: rc)) kD (((List.range c).map g).flatten ++ S kD) := by
    unfold innerSt
    rw [Nat.sub_self, ← List.range_eq_range']
  rw [e0, e1] at L
  exact L

/-! ## The table entries -/

/-- One table entry: `cnt := count`, its pieces, then drop `cnt` and the entry. -/
def entryStep : PP PL :=
  .seq (pushW (sx .cnt) .mark) (.seq (copyW (sx .tA) (sx .cnt) (sx .u))
    (.seq (whileW (sx .cnt) optIsBit innerStep) (.seq (dropFW (sx .cnt))
      (.seq (dropFW (sx .tA)) (.seq (dropFW (sx .tO)) (.seq (dropFW (sx .tP))
        (dropFW (sx .tJ))))))))

theorem runs_entryStep (S : PL → List Sym) (P d r a R K e Sv ρ n c o pw j : ℕ)
    (RA RO RP RJ : List Sym) (hF : FldOK S P d r a R K e Sv ρ) (hB : FldB P d r a R K e Sv ρ n)
    (hA : S (sx .tA) = natSyms c ++ Sym.mark :: RA)
    (hO : S (sx .tO) = natSyms o ++ Sym.mark :: RO)
    (hP : S (sx .tP) = natSyms pw ++ Sym.mark :: RP)
    (hJ : S (sx .tJ) = natSyms j ++ Sym.mark :: RJ)
    (bc : c ≤ mH) (bn : 20 ≤ n) (bo : bitLen o ≤ n) (bpw : bitLen pw ≤ n) (bj : bitLen j ≤ n)
    (bz : ∀ t < c, bitLen (t * pw + o) ≤ n) :
    Runs entryStep S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        (sx .tA) RA) (sx .tO) RO) (sx .tP) RP) (sx .tJ) RJ) kD
        (entBlk P d r a R K e Sv ρ (c, o, pw, j) ++ S kD))
      (fun _ => True) ((mH + 1) * (1000 * (n + 1) ^ 2 + 40)) := by
  have hbc : bitLen c ≤ n := le_trans (NatArith.bitLen_mono'' bc) (le_trans bitLen_mH bn)
  have c1 := runs_pushW (sx .cnt) .mark S
  set S1 := Function.update S (sx .cnt) (Sym.mark :: S (sx .cnt)) with hS1
  have c2 := runs_copyW (src := sx .tA) (dst := sx .cnt) (tmp := sx .u) (by decide) (by decide)
    (by decide) c (Sym.mark :: RA) S1 (tok_mark _) (by simp [hS1, Function.update_apply, hA])
  set S2 := Function.update S1 (sx .cnt) (natSyms c ++ S1 (sx .cnt)) with hS2
  have c3 := runs_innerLoop S2 P d r a R K e Sv ρ c o pw j n (S (sx .cnt)) RO RP RJ
    ((hF.upd (k := sx .cnt) (by decide) _).upd (k := sx .cnt) (by decide) _) hB
    (by simp [hS2, hS1]) (by simp [hS2, hS1, Function.update_apply, hO])
    (by simp [hS2, hS1, Function.update_apply, hP]) (by simp [hS2, hS1, Function.update_apply, hJ])
    hbc bo bpw bj bz
  refine pseq c1 (pseq c2 (pseq c3 (pweak (WP.W9comp.runs_seq
    (runs_dropFW (sx .cnt) 0 .mark (S (sx .cnt)) _ rfl (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .tA) c .mark RA _ rfl
      (by simp [hS2, hS1, Function.update_apply, hA]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .tO) o .mark RO _ rfl
      (by simp [hS2, hS1, Function.update_apply, hO]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .tP) pw .mark RP _ rfl
      (by simp [hS2, hS1, Function.update_apply, hP]))
      (runs_dropFW (sx .tJ) j .mark RJ _ rfl
        (by simp [hS2, hS1, Function.update_apply, hJ])))))) ?_ le_rfl) le_rfl) le_rfl) ?_
  · clear c1 c2 c3
    funext k
    simp only [hS2, hS1, Function.update_apply, entBlk]
    split_ifs <;> (try subst_vars) <;> (try simp_all)
  · have hmul : c * (1000 * (n + 1) ^ 2 + 2) ≤ mH * (1000 * (n + 1) ^ 2 + 2) :=
      Nat.mul_le_mul_right _ bc
    have h0 : bitLen 0 = 0 := rfl
    have m2 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
    rw [h0]
    nlinarith [hmul, m2]

/-! ## The digit table -/

/-- Digit step, first half: `tA := q % mH` (a new entry), `q := q / mH`, and the entries `o`,
`pw`, `jj` pushed onto `tO`, `tP`, `tJ`. -/
def dsA : PP PL :=
  .seq (pushW (sx .tA) .mark) (.seq (pushW (sx .w0) .mark)
    (.seq (dmP (sx .q) (sx .cM) (sx .w0) (sx .tA) (sx .w1) (sx .w2) (sx .w3))
      (.seq (dropW (sx .q)) (.seq (copyW (sx .w0) (sx .q) (sx .u)) (.seq (dropFW (sx .w0))
        (.seq (pushW (sx .tO) .mark) (.seq (copyW (sx .o) (sx .tO) (sx .u))
          (.seq (pushW (sx .tP) .mark) (.seq (copyW (sx .pw) (sx .tP) (sx .u))
            (.seq (pushW (sx .tJ) .mark) (copyW (sx .jj) (sx .tJ) (sx .u))))))))))))

theorem runs_dsA (S : PL → List Sym) (Q J W O n : ℕ) (rq rj rw ro rM : List Sym)
    (hq : S (sx .q) = natSyms Q ++ Sym.mark :: rq) (hj : S (sx .jj) = natSyms J ++ Sym.mark :: rj)
    (hw : S (sx .pw) = natSyms W ++ Sym.mark :: rw) (ho : S (sx .o) = natSyms O ++ Sym.mark :: ro)
    (hM : S (sx .cM) = natSyms mH ++ Sym.mark :: rM)
    (bQ : bitLen Q ≤ n) (bJ : bitLen J ≤ n) (bW : bitLen W ≤ n) (bO : bitLen O ≤ n)
    (bn : 20 ≤ n) :
    Runs dsA S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        (sx .q) (natSyms (Q / mH) ++ Sym.mark :: rq))
        (sx .tA) (natSyms (Q % mH) ++ Sym.mark :: S (sx .tA)))
        (sx .tO) (natSyms O ++ Sym.mark :: S (sx .tO)))
        (sx .tP) (natSyms W ++ Sym.mark :: S (sx .tP)))
        (sx .tJ) (natSyms J ++ Sym.mark :: S (sx .tJ)))
      (fun _ => True) (300 * (n + 1) ^ 2) := by
  have X := WP.W9comp.runs_seq (runs_pushW (sx .tA) .mark S)
    (WP.W9comp.runs_seq (runs_pushW (sx .w0) .mark _)
    (WP.W9comp.runs_seq (runs_dmP (x := sx .q) (y := sx .cM) (q := sx .w0) (r := sx .tA)
        (d0 := sx .w1) (d1 := sx .w2) (d2 := sx .w3) (by decide) Q mH (Sym.mark :: rq)
        (Sym.mark :: rM) _ mH_pos (tok_mark _) (tok_mark _) (by simp [Function.update_apply, hq])
        (by simp [Function.update_apply, hM]))
    (WP.W9comp.runs_seq (runs_dropW (sx .q) Q (Sym.mark :: rq) _ (tok_mark _)
        (by simp [Function.update_apply, hq]))
    (WP.W9comp.runs_seq (runs_copyW (src := sx .w0) (dst := sx .q) (tmp := sx .u) (by decide)
        (by decide) (by decide) (Q / mH) (Sym.mark :: S (sx .w0)) _ (tok_mark _)
        (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .w0) (Q / mH) .mark (S (sx .w0)) _ rfl
        (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_pushW (sx .tO) .mark _)
    (WP.W9comp.runs_seq (runs_copyW (src := sx .o) (dst := sx .tO) (tmp := sx .u) (by decide)
        (by decide) (by decide) O (Sym.mark :: ro) _ (tok_mark _)
        (by simp [Function.update_apply, ho]))
    (WP.W9comp.runs_seq (runs_pushW (sx .tP) .mark _)
    (WP.W9comp.runs_seq (runs_copyW (src := sx .pw) (dst := sx .tP) (tmp := sx .u) (by decide)
        (by decide) (by decide) W (Sym.mark :: rw) _ (tok_mark _)
        (by simp [Function.update_apply, hw]))
    (WP.W9comp.runs_seq (runs_pushW (sx .tJ) .mark _)
      (runs_copyW (src := sx .jj) (dst := sx .tJ) (tmp := sx .u) (by decide) (by decide)
        (by decide) J (Sym.mark :: rj) _ (tok_mark _) (by simp [Function.update_apply, hj]))))))))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext k
    rcases k with i | x
    · simp [Function.update_apply]
    · cases x <;> simp [Function.update_apply]
  · have hbq : bitLen (Q / mH) ≤ n :=
      le_trans (NatArith.bitLen_mono'' (Nat.div_le_self _ _)) bQ
    have hm := bitLen_mH
    generalize bitLen (Q / mH) = bq at hbq ⊢
    generalize bitLen mH = bm at hm ⊢
    have m1 : bitLen Q * bm ≤ n * n := Nat.mul_le_mul bQ (by omega)
    nlinarith [m1]

/-- Digit step, second half: `o := o + a·pw` (`a` the top entry of `tA`), `pw := pw·mH`,
`jj := jj + 1`. -/
def dsB : PP PL :=
  .seq (pushW (sx .w0) .mark)
    (.seq (mulP (sx .tA) (sx .pw) (sx .w0) (sx .w1) (sx .w2) (sx .w3) (sx .w4))
      (.seq (addTo (sx .o) (sx .w0) (sx .w5) (sx .w1) (sx .w2) (sx .w3)) (.seq (dropFW (sx .w0))
        (.seq (mulBy (sx .pw) (sx .cM) (sx .w0) (sx .w1) (sx .w2) (sx .w3) (sx .w4))
          (incW (sx .jj) (sx .u))))))

theorem runs_dsB (S : PL → List Sym) (A J W O n : ℕ) (rA rj rw ro rM : List Sym)
    (hA : S (sx .tA) = natSyms A ++ Sym.mark :: rA) (hj : S (sx .jj) = natSyms J ++ Sym.mark :: rj)
    (hw : S (sx .pw) = natSyms W ++ Sym.mark :: rw) (ho : S (sx .o) = natSyms O ++ Sym.mark :: ro)
    (hM : S (sx .cM) = natSyms mH ++ Sym.mark :: rM)
    (bA : bitLen A ≤ n) (bJ : bitLen (J + 1) ≤ n) (bW : bitLen W ≤ n)
    (bAW : bitLen (O + A * W) ≤ n) (bWM : bitLen (W * mH) ≤ n) (bn : 20 ≤ n) :
    Runs dsB S
      (Function.update (Function.update (Function.update S
        (sx .o) (natSyms (O + A * W) ++ Sym.mark :: ro))
        (sx .pw) (natSyms (W * mH) ++ Sym.mark :: rw))
        (sx .jj) (natSyms (J + 1) ++ Sym.mark :: rj))
      (fun _ => True) (600 * (n + 1) ^ 2) := by
  have X := WP.W9comp.runs_seq (runs_pushW (sx .w0) .mark S)
    (WP.W9comp.runs_seq (runs_mulP (x := sx .tA) (y := sx .pw) (z := sx .w0) (A := sx .w1)
        (Bs := sx .w2) (Acc := sx .w3) (T := sx .w4) (by decide) A W (Sym.mark :: rA)
        (Sym.mark :: rw) _ (tok_mark _) (tok_mark _) (by simp [Function.update_apply, hA])
        (by simp [Function.update_apply, hw]))
    (WP.W9comp.runs_seq (runs_addTo (k := sx .o) (b := sx .w0) (t := sx .w5) (t1 := sx .w1)
        (t2 := sx .w2) (t3 := sx .w3) (by decide) O (A * W) (Sym.mark :: ro)
        (Sym.mark :: S (sx .w0)) _ (tok_mark _) (tok_mark _) (by simp [Function.update_apply, ho])
        (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_dropFW (sx .w0) (A * W) .mark (S (sx .w0)) _ rfl
        (by simp [Function.update_apply]))
    (WP.W9comp.runs_seq (runs_mulBy (k := sx .pw) (b := sx .cM) (t := sx .w0) (A := sx .w1)
        (Bs := sx .w2) (Acc := sx .w3) (T := sx .w4) (by decide) W mH (Sym.mark :: rw)
        (Sym.mark :: rM) _ (tok_mark _) (tok_mark _) (by simp [Function.update_apply, hw])
        (by simp [Function.update_apply, hM]))
      (runs_incW (k := sx .jj) (t := sx .u) (by decide) J (Sym.mark :: rj) _ (tok_mark _)
        (by simp [Function.update_apply, hj]))))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext k
    rcases k with i | x
    · simp [Function.update_apply]
    · cases x <;> simp [Function.update_apply]
  · have hbO : bitLen O ≤ n := le_trans (NatArith.bitLen_mono'' (Nat.le_add_right _ _)) bAW
    have hbAW : bitLen (A * W) ≤ n :=
      le_trans (NatArith.bitLen_mono'' (Nat.le_add_left _ _)) bAW
    have hbJ : bitLen J ≤ n := le_trans (NatArith.bitLen_mono'' (Nat.le_succ J)) bJ
    have hm := bitLen_mH
    have m1 := Nat.mul_le_mul (show bitLen A + 1 ≤ n + 1 by omega)
      (show bitLen A + bitLen W + 2 ≤ 2 * n + 2 by omega)
    have m2 := Nat.mul_le_mul (show bitLen W + 1 ≤ n + 1 by omega)
      (show bitLen W + bitLen mH + 2 ≤ 2 * n + 2 by omega)
    unfold NatArith.mulCost
    nlinarith [m1, m2]

/-! ## All table entries -/

/-- The emission state after `i` entries. -/
def emitSt (S : PL → List Sym) (P d r a R K e Sv ρ : ℕ) (es : List (ℕ × ℕ × ℕ × ℕ))
    (rA rO rP rJ : List Sym) (i : ℕ) : PL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update S
    (sx .tA) (tabOf (fun x => x.1) (es.drop i) rA))
    (sx .tO) (tabOf (fun x => x.2.1) (es.drop i) rO))
    (sx .tP) (tabOf (fun x => x.2.2.1) (es.drop i) rP))
    (sx .tJ) (tabOf (fun x => x.2.2.2) (es.drop i) rJ)) kD
    ((es.take i).reverse.flatMap (entBlk P d r a R K e Sv ρ) ++ S kD)

/-- **All table entries**, top first. -/
theorem runs_emitLoop (S : PL → List Sym) (P d r a R K e Sv ρ n : ℕ)
    (es : List (ℕ × ℕ × ℕ × ℕ)) (rA rO rP rJ : List Sym) (hF : FldOK S P d r a R K e Sv ρ)
    (hB : FldB P d r a R K e Sv ρ n) (hA : S (sx .tA) = tabOf (fun x => x.1) es rA)
    (hO : S (sx .tO) = tabOf (fun x => x.2.1) es rO)
    (hP : S (sx .tP) = tabOf (fun x => x.2.2.1) es rP)
    (hJ : S (sx .tJ) = tabOf (fun x => x.2.2.2) es rJ) (bn : 20 ≤ n)
    (hes : ∀ x ∈ es, x.1 ≤ mH ∧ bitLen x.2.1 ≤ n ∧ bitLen x.2.2.1 ≤ n ∧ bitLen x.2.2.2 ≤ n ∧
      ∀ t < x.1, bitLen (t * x.2.2.1 + x.2.1) ≤ n) :
    Runs (whileW (sx .tA) notSep entryStep) S
      (emitSt S P d r a R K e Sv ρ es rA rO rP rJ es.length)
      (fun _ => True) (es.length * ((mH + 1) * (1000 * (n + 1) ^ 2 + 40) + 2) + 2) := by
  have h0 : emitSt S P d r a R K e Sv ρ es rA rO rP rJ 0 = S := by
    simp only [emitSt, List.drop_zero, List.take_zero, List.reverse_nil, List.flatMap_nil,
      List.nil_append]
    rw [← hA, ← hO, ← hP, ← hJ]
    simp only [Function.update_eq_self]
  have eA : ∀ i, emitSt S P d r a R K e Sv ρ es rA rO rP rJ i (sx .tA) =
      tabOf (fun x => x.1) (es.drop i) rA := fun i => by simp [emitSt, Function.update_apply]
  have eO : ∀ i, emitSt S P d r a R K e Sv ρ es rA rO rP rJ i (sx .tO) =
      tabOf (fun x => x.2.1) (es.drop i) rO := fun i => by simp [emitSt, Function.update_apply]
  have eP : ∀ i, emitSt S P d r a R K e Sv ρ es rA rO rP rJ i (sx .tP) =
      tabOf (fun x => x.2.2.1) (es.drop i) rP := fun i => by simp [emitSt, Function.update_apply]
  have eJ : ∀ i, emitSt S P d r a R K e Sv ρ es rA rO rP rJ i (sx .tJ) =
      tabOf (fun x => x.2.2.2) (es.drop i) rJ := fun i => by simp [emitSt, Function.update_apply]
  have L := runs_whileW (k := sx .tA) (c := notSep) (p := entryStep)
    (emitSt S P d r a R K e Sv ρ es rA rO rP rJ) ((mH + 1) * (1000 * (n + 1) ^ 2 + 40))
    es.length
    (fun i hi => by
      rw [eA, List.drop_eq_getElem_cons hi, tabOf_cons]
      exact notSep_natSyms _ _)
    (by rw [eA, List.drop_length, tabOf_nil]; rfl)
    (fun i hi => by
      have hx := List.drop_eq_getElem_cons hi
      obtain ⟨b1, b2, b3, b4, b5⟩ := hes es[i] (List.getElem_mem hi)
      have h := runs_entryStep (emitSt S P d r a R K e Sv ρ es rA rO rP rJ i) P d r a R K e Sv ρ n
        es[i].1 es[i].2.1 es[i].2.2.1 es[i].2.2.2
        (tabOf (fun x => x.1) (es.drop (i + 1)) rA) (tabOf (fun x => x.2.1) (es.drop (i + 1)) rO)
        (tabOf (fun x => x.2.2.1) (es.drop (i + 1)) rP)
        (tabOf (fun x => x.2.2.2) (es.drop (i + 1)) rJ)
        (((((hF.upd (k := sx .tA) (by decide) _).upd (k := sx .tO) (by decide) _).upd
          (k := sx .tP) (by decide) _).upd (k := sx .tJ) (by decide) _).upd (k := kD)
          (by decide) _) hB
        (by rw [eA, hx, tabOf_cons]) (by rw [eO, hx, tabOf_cons]) (by rw [eP, hx, tabOf_cons])
        (by rw [eJ, hx, tabOf_cons]) b1 bn b2 b3 b4 b5
      refine pweak h ?_ le_rfl
      have hk : emitSt S P d r a R K e Sv ρ es rA rO rP rJ i kD =
          (es.take i).reverse.flatMap (entBlk P d r a R K e Sv ρ) ++ S kD := by
        simp [emitSt]
      have hblk : (es.take (i + 1)).reverse.flatMap (entBlk P d r a R K e Sv ρ) =
          entBlk P d r a R K e Sv ρ es[i] ++
            (es.take i).reverse.flatMap (entBlk P d r a R K e Sv ρ) := by
        rw [List.take_succ_eq_append_getElem hi]
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          List.flatMap_cons]
      rw [hk]
      unfold emitSt
      funext k
      simp only [Function.update_apply]
      split_ifs <;> (try subst_vars) <;> (try simp_all [hblk]))
  rw [h0] at L
  exact L

/-! ## The digit loop -/

/-- One digit step. -/
def digitStep : PP PL := .seq dsA dsB

/-- The digit-table entries after `i` steps (the latest first). -/
def digEs (e i : ℕ) : List (ℕ × ℕ × ℕ × ℕ) := ((List.range i).map fun k => dent (dst e k)).reverse

theorem digEs_succ (e i : ℕ) : digEs e (i + 1) = dent (dst e i) :: digEs e i := by
  simp [digEs, List.range_succ]

/-- The digit-loop state after `i` steps. -/
def digSt (S : PL → List Sym) (e : ℕ) (rq rj rw ro rA rO rP rJ : List Sym) (i : ℕ) :
    PL → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update S
      (sx .q) (natSyms (dst e i).1 ++ Sym.mark :: rq))
      (sx .tA) (tabOf (fun x => x.1) (digEs e i) rA))
      (sx .tO) (tabOf (fun x => x.2.1) (digEs e i) rO))
      (sx .tP) (tabOf (fun x => x.2.2.1) (digEs e i) rP))
      (sx .tJ) (tabOf (fun x => x.2.2.2) (digEs e i) rJ))
      (sx .o) (natSyms (dst e i).2.2 ++ Sym.mark :: ro))
      (sx .pw) (natSyms (mH ^ i) ++ Sym.mark :: rw))
      (sx .jj) (natSyms i ++ Sym.mark :: rj)

theorem lt_two_pow' : ∀ m : ℕ, m < 2 ^ m
  | 0 => by norm_num
  | m + 1 => by
    have := lt_two_pow' m
    rw [pow_succ]
    omega

theorem bitLen_le_self (m : ℕ) : bitLen m ≤ m := NatArith.bitLen_le_of_lt' (lt_two_pow' m)

/-- **The digit loop**: from `digSt … 0` (`q = e`, `j = 0`, `pw = 1`, `o = 0`, empty tables) to
`digSt … N`, `N = (Nat.digits mH e).length` (`q = 0`; the tables hold all the entries). -/
theorem runs_digitLoop (S : PL → List Sym) (e : ℕ) (rq rj rw ro rA rO rP rJ rM : List Sym)
    (hM : S (sx .cM) = natSyms mH ++ Sym.mark :: rM) :
    Runs (whileW (sx .q) optIsBit digitStep) (digSt S e rq rj rw ro rA rO rP rJ 0)
      (digSt S e rq rj rw ro rA rO rP rJ (Nat.digits mH e).length) (fun _ => True)
      ((Nat.digits mH e).length * (900 * (bitLen e + 22) ^ 2 + 2) + 2) := by
  have hNb : (Nat.digits mH e).length ≤ bitLen e := len_le_bitLen e
  have hmul : bitLen (mH * e) ≤ bitLen e + 20 :=
    le_trans (NatArith.bitLen_mul_le' _ _) (by have := bitLen_mH; omega)
  have eq_ : ∀ i, digSt S e rq rj rw ro rA rO rP rJ i (sx .q) =
      natSyms (dst e i).1 ++ Sym.mark :: rq := fun i => by simp [digSt, Function.update_apply]
  refine runs_whileW (digSt S e rq rj rw ro rA rO rP rJ) (900 * (bitLen e + 22) ^ 2) _ ?_ ?_ ?_
  · intro i hi
    rw [eq_]
    exact optIsBit_natSyms _ (by rw [Ne, dst_eq_zero_iff]; omega) _
  · rw [eq_, (dst_eq_zero_iff e _).2 le_rfl]
    exact optIsBit_zero _
  · intro i hi
    have hpow : mH ^ i ≤ e := pow_le_of_lt_len hi
    have hq : (dst e i).1 ≤ e := by rw [dst_q]; exact Nat.div_le_self _ _
    have ho : (dst e i).2.2 < mH ^ i := dst_o_lt e i
    have ho1 := dst_o_lt e (i + 1)
    have e1 : dst e (i + 1) =
        ((dst e i).1 / mH, i + 1, (dst e i).2.2 + (dst e i).1 % mH * mH ^ i) := by
      rw [dst_succ]
      simp [dstep, dst_j]
    rw [e1] at ho1
    simp only at ho1
    have h2 : mH ^ (i + 1) ≤ mH * e := by
      rw [pow_succ, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hpow
    have hlt : (dst e i).1 % mH < mH := Nat.mod_lt _ mH_pos
    have bQ : bitLen (dst e i).1 ≤ bitLen e + 21 :=
      le_trans (NatArith.bitLen_mono'' hq) (by omega)
    have bJ : bitLen i ≤ bitLen e + 21 := le_trans (bitLen_le_self _) (by omega)
    have bJ1 : bitLen (i + 1) ≤ bitLen e + 21 := le_trans (bitLen_le_self _) (by omega)
    have bW : bitLen (mH ^ i) ≤ bitLen e + 21 := le_trans (NatArith.bitLen_mono'' hpow) (by omega)
    have bO : bitLen (dst e i).2.2 ≤ bitLen e + 21 :=
      le_trans (NatArith.bitLen_mono'' (le_of_lt (lt_of_lt_of_le ho hpow))) (by omega)
    have bA : bitLen ((dst e i).1 % mH) ≤ bitLen e + 21 :=
      le_trans (NatArith.bitLen_mono'' hlt.le) (by have := bitLen_mH; omega)
    have bAW : bitLen ((dst e i).2.2 + (dst e i).1 % mH * mH ^ i) ≤ bitLen e + 21 :=
      le_trans (NatArith.bitLen_mono'' (show _ ≤ mH * e by omega)) (by omega)
    have bWM : bitLen (mH ^ i * mH) ≤ bitLen e + 21 := by
      have h3 : mH ^ i * mH ≤ mH * e := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left _ hpow
      exact le_trans (NatArith.bitLen_mono'' h3) (by omega)
    have h1 := runs_dsA (digSt S e rq rj rw ro rA rO rP rJ i) (dst e i).1 i (mH ^ i) (dst e i).2.2
      (bitLen e + 21) rq rj rw ro rM (eq_ i) (by simp [digSt, Function.update_apply])
      (by simp [digSt, Function.update_apply]) (by simp [digSt, Function.update_apply])
      (by simp [digSt, Function.update_apply, hM]) bQ bJ bW bO (by omega)
    refine pseq h1 (pweak (runs_dsB _ ((dst e i).1 % mH) i (mH ^ i) (dst e i).2.2 (bitLen e + 21)
      (digSt S e rq rj rw ro rA rO rP rJ i (sx .tA)) rj rw ro rM
      (by simp [Function.update_apply]) (by simp [digSt, Function.update_apply])
      (by simp [digSt, Function.update_apply]) (by simp [digSt, Function.update_apply])
      (by simp [digSt, Function.update_apply, hM]) bA bJ1 bW bAW bWM (by omega)) ?_ le_rfl)
      (by rw [show bitLen e + 21 + 1 = bitLen e + 22 by omega]; omega)
    have eA : digSt S e rq rj rw ro rA rO rP rJ i (sx .tA) =
        tabOf (fun x => x.1) (digEs e i) rA := by simp [digSt, Function.update_apply]
    have eO : digSt S e rq rj rw ro rA rO rP rJ i (sx .tO) =
        tabOf (fun x => x.2.1) (digEs e i) rO := by simp [digSt, Function.update_apply]
    have eP : digSt S e rq rj rw ro rA rO rP rJ i (sx .tP) =
        tabOf (fun x => x.2.2.1) (digEs e i) rP := by simp [digSt, Function.update_apply]
    have eJ : digSt S e rq rj rw ro rA rO rP rJ i (sx .tJ) =
        tabOf (fun x => x.2.2.2) (digEs e i) rJ := by simp [digSt, Function.update_apply]
    clear h1 bQ bJ bJ1 bW bO bA bAW bWM ho ho1 h2 hlt hpow hq hmul hNb
    rw [eA, eO, eP, eJ]
    unfold digSt
    rw [e1, digEs_succ]
    funext k
    rcases k with i | x
    · simp [Function.update_apply]
    · cases x <;> simp [Function.update_apply, tabOf_cons, dent, dst_j, pow_succ]

end SubNLogN.Machine.Layer.DrvDescPiecesAux
