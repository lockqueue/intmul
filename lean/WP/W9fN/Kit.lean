import WP.W9fN.Bound
import Contracts.W9.Pipeline
import WP.W9fDiv.Holds

/-!
# WP.W9fN.Kit — the column ops as IntLang operation implementations, one cost constant

Shared operation-kit adapter used by the Nyquist (`WP.W9fN`) and forward (`WP.W9fF`) column cores.

* `BinOpH f`, `ShiftOpH f`: verbatim bodies of `WP.W9fOps.W9fBinOp` / `W9fShiftOp` (hypotheses
  until W9fOps is merged); `OpsHyp` collects the three shift/compare ops.
* `Kit Mul`: an `OpImpl` for every `Op`, all `Good`, with ONE constant `C` such that every op
  satisfies `BinOK` against `kap C Mul W` for EVERY declared product width `W`.
* `kit_exists`: from `W5_mulAt Mul` (mul, declared width `max W (max |a| |b|)`), `W3_all`
  (`W3_addInt`, `W3_subInt`), `W6a_all` (divRound via `WP.W9fDiv.W9fDiv_holds`) and `OpsHyp`.
  `C` is the sum of the seven constants.
-/

namespace WP.W9fN

open TMFw TMFw.Contracts WP.W9fN.IL

/-- Verbatim body of `WP.W9fOps.W9fBinOp` (cost `C·(|a| + |b| + 1)`). -/
def BinOpH (f : ℤ → ℤ → ℤ) : Prop :=
  ∃ C : ℕ, ∃ (m : ℕ) (R : Type) (P : Prog (Loc 3 m) (fun _ => Sym) R),
    m ≤ 16 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧
    ∀ (a b : ℤ) (ra rb : List Sym) (S : Loc 3 m → List Sym),
      TermOK ra → TermOK rb → TermOK (S (.inl 2)) →
      S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
      Runs P S (Function.update S (.inl 2) (intSyms (f a b) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Verbatim body of `WP.W9fOps.W9fShiftOp` (cost `C·(|a| + |b| + b.natAbs + 1)`). -/
def ShiftOpH (f : ℤ → ℤ → ℤ) : Prop :=
  ∃ C : ℕ, ∃ (m : ℕ) (R : Type) (P : Prog (Loc 3 m) (fun _ => Sym) R),
    m ≤ 16 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧
    ∀ (a b : ℤ) (ra rb : List Sym) (S : Loc 3 m → List Sym),
      TermOK ra → TermOK rb → TermOK (S (.inl 2)) →
      S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
      Runs P S (Function.update S (.inl 2) (intSyms (f a b) ++ S (.inl 2))) (fun _ => True)
        (C * (bitLen a.natAbs + bitLen b.natAbs + b.natAbs + 1))

/-- The shift and compare ops (W9fOps). -/
def OpsHyp : Prop :=
  BinOpH (fun a b => a >>> b.natAbs) ∧ ShiftOpH (fun a b => a * 2 ^ b.natAbs) ∧
    BinOpH (fun a b => if a ≤ b then 1 else 0)

/-- Implementations of all column ops with ONE cost constant, valid at every declared width. -/
structure Kit (Mul : ℕ → ℕ) : Type 1 where
  I : Op → OpImpl
  good : ∀ o, (I o).Good
  C : ℕ
  ok : ∀ (W : ℕ) (o : Op), BinOK (I o) (Op.sem o) (kap C Mul W o)

theorem runs_mono {K R : Type} [DecidableEq K] {P : Prog K (fun _ => Sym) R}
    {S S' : K → List Sym} {Q : R → Prop} {T T' : ℕ} (h : Runs P S S' Q T) (hT : T ≤ T') :
    Runs P S S' Q T' :=
  Triple.cost_mono h hT

/-- **The ops kit exists.** -/
theorem kit_exists (Mul : ℕ → ℕ) (h5 : W5_mulAt Mul) (h3 : W3_all) (h6 : W6a_all)
    (hops : OpsHyp) : Nonempty (Kit Mul) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hadd, hsub, -, -⟩ := h3
  obtain ⟨Ca, hadd'⟩ := hadd
  obtain ⟨ma, Ra, -, Pa, hma, hfa, hna, hca, hsa⟩ := hadd' ()
  obtain ⟨Cs, hsub'⟩ := hsub
  obtain ⟨ms, Rs, -, Ps, hms, hfs, hns, hcs, hss⟩ := hsub' ()
  obtain ⟨Cm, hmul'⟩ := h5
  obtain ⟨mm, Rm, -, Pm, hmm, hfm, hnm, hcm, hsm⟩ := hmul' ()
  obtain ⟨Cd, hdiv'⟩ := WP.W9fDiv.W9fDiv_holds h6.2
  obtain ⟨md, Rd, -, Pd, hmd, hfd, hnd, hcd, hsd⟩ := hdiv' ()
  obtain ⟨⟨Cr, mr, Rr, Pr, hmr, hfr, hnr, hcr, hsr⟩, ⟨Cl, ml, Rl, Pl, hml, hfl, hnl, hcl, hsl⟩,
    ⟨Ce, me, Re, Pe, hme, hfe, hne, hce, hse⟩⟩ := hops
  let I : Op → OpImpl := fun o => match o with
    | .add => ⟨ma, by omega, Ra, Pa⟩
    | .sub => ⟨ms, by omega, Rs, Ps⟩
    | .mul => ⟨mm, by omega, Rm, Pm⟩
    | .shl => ⟨ml, hml, Rl, Pl⟩
    | .sar => ⟨mr, hmr, Rr, Pr⟩
    | .le => ⟨me, hme, Re, Pe⟩
    | .divR => ⟨md, hmd, Rd, Pd⟩
  refine ⟨⟨I, ?_, Ca + Cs + Cm + Cd + Cr + Cl + Ce, ?_⟩⟩
  · intro o
    cases o
    · show Pa.Closed ∧ Finite Ra ∧ Nonempty Ra
      exact ⟨hca, hfa, hna⟩
    · show Ps.Closed ∧ Finite Rs ∧ Nonempty Rs
      exact ⟨hcs, hfs, hns⟩
    · show Pm.Closed ∧ Finite Rm ∧ Nonempty Rm
      exact ⟨hcm, hfm, hnm⟩
    · show Pl.Closed ∧ Finite Rl ∧ Nonempty Rl
      exact ⟨hcl, hfl, hnl⟩
    · show Pr.Closed ∧ Finite Rr ∧ Nonempty Rr
      exact ⟨hcr, hfr, hnr⟩
    · show Pe.Closed ∧ Finite Re ∧ Nonempty Re
      exact ⟨hce, hfe, hne⟩
    · show Pd.Closed ∧ Finite Rd ∧ Nonempty Rd
      exact ⟨hcd, hfd, hnd⟩
  · intro W o
    cases o
    · intro a b ra rb S hra hrb _ h0 h1
      exact runs_mono (hsa a b ra rb S hra hrb h0 h1) (Nat.mul_le_mul_right _ (by omega))
    · intro a b ra rb S hra hrb _ h0 h1
      exact runs_mono (hss a b ra rb S hra hrb h0 h1) (Nat.mul_le_mul_right _ (by omega))
    · intro a b ra rb S hra hrb _ h0 h1
      exact runs_mono (hsm (max W (max (bitLen a.natAbs) (bitLen b.natAbs))) a b ra rb S
        (by omega) (by omega) hra hrb h0 h1)
        (Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (by omega))
    · intro a b ra rb S hra hrb h2 h0 h1
      exact runs_mono (hsl a b ra rb S hra hrb h2 h0 h1) (Nat.mul_le_mul_right _ (by omega))
    · intro a b ra rb S hra hrb h2 h0 h1
      exact runs_mono (hsr a b ra rb S hra hrb h2 h0 h1) (Nat.mul_le_mul_right _ (by omega))
    · intro a b ra rb S hra hrb h2 h0 h1
      exact runs_mono (hse a b ra rb S hra hrb h2 h0 h1) (Nat.mul_le_mul_right _ (by omega))
    · intro a b ra rb S hra hrb h2 h0 h1
      exact runs_mono (hsd a b ra rb S hra hrb h2 h0 h1) (Nat.mul_le_mul_right _ (by omega))

#assert_std_axioms runs_mono kit_exists

end WP.W9fN
