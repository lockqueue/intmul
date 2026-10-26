/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.SolMuAh

/-!
# K6 (`Machine/Tables/SolGam.lean`): solver entries, parts 1 and 3 — coefficients and `γ̂`

**Scope (honest summary).** The fragment `solCoeffs2` (`x43 := ĉ_max`, `x44 := ĉ_min` from the digit
`u`, `HT.solCoeffs2_spec`) and the closure fragment `solGam` (`x54 := γ̂`): the truncated
binary powering `X = powTruncInt Q q â A` over the bits of `A` (most significant first; each
square computed once), then `γ̂ = rhuDiv (2^(Q+q)) (2^Q - X)` (`HT.solGam_spec`).
-/

namespace SubNLogN.Machine.Tables

open TMFw TMFw.Contracts WP.W7k2 SubNLogN.Machine SubNLogN.Math.Bridge
  SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common.GridInt

/-! ## Part 1 -/

/-- `x43 := intSyms ĉ_max`, `x44 := intSyms ĉ_min` from `ru = u` (temporaries `x40 … x42`). -/
def solCoeffs2 (I : TB) : TP I :=
  (tcp I ru x41).seq ((tad I ru x41 x40).seq ((tdr I x41).seq ((tcp I x40 x41).seq
    ((tic I x40).seq ((tcc I rW rPC r2t x40 x42).seq ((solOrient I).seq
      ((tdr I x40).seq (tdr I x41))))))))

theorem solCoeffs2_closed (I : TB) : (solCoeffs2 I).Closed :=
  ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _,
    ⟨callI_closed _ _ _ _, ⟨callI_closed _ _ _ _, ⟨solOrient_closed I,
      ⟨callI_closed _ _ _ _, callI_closed _ _ _ _⟩⟩⟩⟩⟩⟩⟩⟩

section Coef

variable {I : TB} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.solCoeffs2_spec (hI : I.Spec Mul C) (B : TL → List Sym) (ω P t u : ℕ)
    (hω : 1 ≤ ω) (hut : u < t)
    (hu : B ru = natSyms u) (hW : B rW = natSyms ω) (hPC : B rPC = natSyms (coeffPrec P))
    (h2t : B r2t = natSyms (2 * t)) (hT : B rT = natSyms t)
    (h40 : B x40 = []) (h41 : B x41 = []) (h42 : B x42 = []) (h43 : B x43 = [])
    (h44 : B x44 = []) (ρ : List (TP I)) :
    HT ρ B (solCoeffs2 I)
      (Function.update (Function.update B x43 (intSyms (cmaxN ω P t u))) x44
        (intSyms (cminN ω P t u)))
      (C * (bitLen u + 1) + (C * (bitLen u + bitLen u + 1) + (C * (bitLen u + 1) +
        (C * (bitLen (u + u) + 1) + (C * (bitLen (u + u) + 1) +
        (C * (ω + coeffPrec P + bitLen (2 * t) + 1) ^ 4 +
        ((C * (bitLen (u + u) + bitLen t + 1) +
          (2 * (C * (bitLen (c0Int ω P t u).natAbs + bitLen (c1Int ω P t u).natAbs + 2)) + 6 +
            1)) + (C * (bitLen (u + u + 1) + 1) + C * (bitLen (u + u) + 1))))))))) := by
  have hu2 : 2 * u + 1 = u + u + 1 := by ring
  refine (HT.seq (HT.tcp_spec hI ru x41 (by decide) B u [] TermOK.nil
      (by rw [hu, List.append_nil]) ρ)
    (HT.seq (HT.tad_spec hI ru x41 x40 (by decide) _ u u [] [] TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hu, List.append_nil])
      (by simp (disch := decide) only [Function.update_self, h41, List.append_nil]) ρ)
    (HT.seq (HT.tdr_spec hI x41 _ u [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h41,
        List.append_nil]) ρ)
    (HT.seq (HT.tcp_spec hI x40 x41 (by decide) _ (u + u) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h40,
        List.append_nil]) ρ)
    (HT.seq (HT.tic_spec hI x40 _ (u + u) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, h40,
        List.append_nil]) ρ)
    (HT.seq (HT.tcc_spec hI rW rPC r2t x40 x42 (by decide) _ ω (coeffPrec P) (2 * t) (2 * u + 1)
      [] [] [] [] (by omega) (by omega) (by omega) TermOK.nil TermOK.nil TermOK.nil TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hW, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hPC, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, h2t, List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self, hu2]) ρ)
    (HT.seq (HT.solOrient_spec hI _ u t (c0Int ω P t u) (c1Int ω P t u)
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil])
      (by simp (disch := decide) only [Function.update_of_ne, hT])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne, h42,
        List.append_nil]; rfl)
      (by simp (disch := decide) only [Function.update_of_ne, h43])
      (by simp (disch := decide) only [Function.update_of_ne, h44]) ρ)
    (HT.seq (HT.tdr_spec hI x40 _ (u + u + 1) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        List.append_nil]) ρ)
      (HT.tdr_spec hI x41 _ (u + u) [] TermOK.nil
        (by simp (disch := decide) only [Function.update_of_ne, Function.update_self,
          List.append_nil]) ρ))))))))).of_eq ?_ le_rfl
  have e0 : (if 2 * u < t then c0Int ω P t u else c1Int ω P t u) = cmaxN ω P t u := rfl
  have e1 : (if 2 * u < t then c1Int ω P t u else c0Int ω P t u) = cminN ω P t u := rfl
  rw [e0, e1]
  simp (disch := first | decide | simp (config := { failIfUnchanged := false }) (disch := decide)
    only [ValEq.eq_1, Function.update_self, Function.update_of_ne, h40, h41, h42, h43, h44])
    only [tupd_swap, Function.update_idem, tupd_eq_self_of, Function.update_self,
    Function.update_of_ne, h40, h41, h42, h43, h44, List.append_nil]

end Coef

/-! ## Nonnegative signed helpers -/

section PosOps

variable (I : TB)

/-- `Y := intSyms z` for `X = intSyms z`, `z ≥ 0` (copy of a nonnegative signed number). -/
def copyPos (X Y : TL) : TP I :=
  (tpop I X).seq ((tcp I X Y).seq ((tpush I Y .pos).seq (tpush I X .pos)))

/-- `X = intSyms z ↦ intSyms (z / 2^k)` for `z ≥ 0`, `K = natSyms k`. -/
def shrPos (X K : TL) : TP I := (tpop I X).seq ((tsr I X K).seq (tpush I X .pos))

theorem copyPos_closed (X Y : TL) : (copyPos I X Y).Closed :=
  ⟨trivial, ⟨callI_closed _ _ _ _, ⟨trivial, trivial⟩⟩⟩

theorem shrPos_closed (X K : TL) : (shrPos I X K).Closed :=
  ⟨trivial, ⟨callI_closed _ _ _ _, trivial⟩⟩

variable {I} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.copyPos_spec (hI : I.Spec Mul C) (X Y : TL) (hXY : X ≠ Y) (B : TL → List Sym)
    (z : ℕ) (rx : List Sym) (hrx : TermOK rx) (hB : B X = intSyms (z : ℤ) ++ rx)
    (ρ : List (TP I)) :
    HT ρ B (copyPos I X Y) (Function.update B Y (intSyms (z : ℤ) ++ B Y))
      (1 + (C * (bitLen z + 1) + (1 + 1))) := by
  have hB' : B X = Sym.pos :: (natSyms z ++ rx) := by rw [hB, intSyms_natCast]; rfl
  refine (HT.seq (HT.tpop_spec X B _ _ hB' ρ)
    (HT.seq (HT.tcp_spec hI X Y (by simp [hXY]) _ z rx hrx (by rw [Function.update_self]) ρ)
    (HT.seq (HT.tpush_spec Y .pos _ ρ) (HT.tpush_spec X .pos _ ρ)))).of_eq ?_ le_rfl
  funext g
  by_cases hgX : g = X
  · subst hgX
    simp [Function.update_apply, hXY, hB, intSyms_natCast]
  by_cases hgY : g = Y
  · subst hgY
    simp [Function.update_apply, Ne.symm hXY, intSyms_natCast]
  simp [Function.update_apply, hgX, hgY]

theorem HT.shrPos_spec (hI : I.Spec Mul C) (X K : TL) (hXK : X ≠ K) (B : TL → List Sym)
    (z k : ℕ) (rx rk : List Sym) (hrx : TermOK rx) (hrk : TermOK rk)
    (hB : B X = intSyms (z : ℤ) ++ rx) (hK : B K = natSyms k ++ rk) (ρ : List (TP I)) :
    HT ρ B (shrPos I X K) (Function.update B X (intSyms ((z / 2 ^ k : ℕ) : ℤ) ++ rx))
      (1 + (C * (min k (bitLen z) + bitLen k + 1) + 1)) := by
  have hB' : B X = Sym.pos :: (natSyms z ++ rx) := by rw [hB, intSyms_natCast]; rfl
  refine (HT.seq (HT.tpop_spec X B _ _ hB' ρ)
    (HT.seq (HT.tsr_spec hI X K (by simp [hXK]) _ z k rx rk hrx hrk (by rw [Function.update_self])
      (by rw [Function.update_of_ne (Ne.symm hXK), hK]) ρ)
      (HT.tpush_spec X .pos _ ρ))).of_eq ?_ le_rfl
  rw [Function.update_idem, Function.update_self, Function.update_idem, intSyms_natCast]
  rfl

end PosOps

/-! ## Truncated powering bounds -/

theorem powStepN_le {Q p a X : ℕ} {b : Bool} (ha : a ≤ 2 ^ p) (hX : X ≤ 2 ^ Q) :
    powStepN Q p a b X ≤ 2 ^ Q := by
  have h1 : X * X / 2 ^ Q ≤ 2 ^ Q := by
    rw [Nat.div_le_iff_le_mul_add_pred (by positivity)]
    nlinarith
  unfold powStepN
  split_ifs
  · rw [Nat.div_le_iff_le_mul_add_pred (by positivity)]
    nlinarith
  · exact h1

theorem powFoldN_le {Q p a : ℕ} (ha : a ≤ 2 ^ p) :
    ∀ (bs : List Bool) (X : ℕ), X ≤ 2 ^ Q → powFoldN Q p a bs X ≤ 2 ^ Q
  | [], X, hX => hX
  | b :: bs, X, hX => by
    show powFoldN Q p a bs (powStepN Q p a b X) ≤ 2 ^ Q
    exact powFoldN_le ha bs _ (powStepN_le ha hX)

end SubNLogN.Machine.Tables
