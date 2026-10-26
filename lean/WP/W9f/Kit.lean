import WP.W9f.GlueRec
import WP.W7k2.Ops

/-!
# WP.W9f.Kit — sub-kernel instances and the entry mover in host form

* `SpecFwd`, `SpecNyq`, `SpecMove`: the bodies of `W9f_fwdCore`, `W9f_nyqCore`, `W9f_moveEntries`
  for one extracted instance (`exists_inst`), verbatim.
* `Kit Mul`: one instance of each sub-kernel and of `W3_cmpNat`, with their constants and specs.
* `KReg K`: host registers (macro register and the four instances' registers), with lenses.
* `HT.moverF`: the entry mover called on two modified host stacks.
-/

namespace WP.W9f

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-- Body of `W9f_fwdCore` for one instance. -/
def SpecFwd (Mul : ℕ → ℕ) (I : Inst 7 48 Unit) (C : ℕ) : Prop :=
  ∀ (q H μ : ℕ) (a c : ℤ) (Ys : Array (ℤ × ℤ)) (rIn r2 r3 r4 r5 r6 : List Sym)
    (S : Loc 7 I.m → List Sym),
    2 ≤ Ys.size → q + 2 ≤ H → 0 < a → (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a →
    bitLen a.natAbs ≤ H → bitLen c.natAbs ≤ H → ArrW H Ys →
    IntMulTM.Contracts.W8.zPartFwdBound q H a c Ys (Ys.size - 1) →
    IntMulTM.Contracts.W8.zHomFwdBound q H a c (Ys.size - 1) →
    ArrW H (IntMulTM.Contracts.W8.solveFwdBarrett q H Ys.size μ a c Ys) →
    NotEntry rIn → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
    S (.inl 0) = blkE Ys.toList ++ rIn → S (.inl 2) = natSyms q ++ r2 →
    S (.inl 3) = natSyms H ++ r3 → S (.inl 4) = natSyms μ ++ r4 →
    S (.inl 5) = intSyms a ++ r5 → S (.inl 6) = intSyms c ++ r6 →
    Runs I.P S (Function.update (Function.update S (.inl 0) rIn) (.inl 1)
        (blkE (IntMulTM.Contracts.W8.solveFwdBarrett q H Ys.size μ a c Ys).toList ++
          S (.inl 1)))
      (fun _ => True) (C * (Ys.size * (Mul (solW H) + H + 1) + (H + 1) ^ 2))

/-- Body of `W9f_nyqCore` for one instance. -/
def SpecNyq (Mul : ℕ → ℕ) (I : Inst 8 48 Unit) (C : ℕ) : Prop :=
  ∀ (q H μ k : ℕ) (a : ℤ) (alt : ℤ × ℤ) (Ys : Array (ℤ × ℤ))
    (rIn r2 r3 r4 r5 r6 r7 : List Sym) (S : Loc 8 I.m → List Sym),
    Ys.size = 2 ^ k → 1 ≤ k → q + 2 ≤ H → 0 < a → (μ : ℤ) = ((2 ^ H : ℕ) : ℤ) / a →
    bitLen a.natAbs ≤ H → ArrW H Ys → EntryW H alt →
    IntMulTM.Contracts.W8.zPartNyqBound q H a Ys (Ys.size - 1) →
    ArrW H (IntMulTM.Contracts.W8.solveNyqBarrett q H Ys.size k μ a Ys alt) →
    NotEntry rIn → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 → TermOK r6 →
    S (.inl 0) = blkE Ys.toList ++ rIn → S (.inl 2) = natSyms q ++ r2 →
    S (.inl 3) = natSyms H ++ r3 → S (.inl 4) = natSyms μ ++ r4 →
    S (.inl 5) = natSyms k ++ r5 → S (.inl 6) = intSyms a ++ r6 →
    S (.inl 7) = entrySyms alt ++ r7 →
    Runs I.P S (Function.update (Function.update S (.inl 0) rIn) (.inl 1)
        (blkE (IntMulTM.Contracts.W8.solveNyqBarrett q H Ys.size k μ a Ys alt).toList ++
          S (.inl 1)))
      (fun _ => True) (C * (Ys.size * (Mul (solW H) + H + k + 1) + (H + 1) ^ 2))

/-- Body of `W9f_moveEntries` for one instance. -/
def SpecMove (I : Inst 2 8 Unit) (C : ℕ) : Prop :=
  ∀ (xs : List (ℤ × ℤ)) (r0 : List Sym) (S : Loc 2 I.m → List Sym), NotEntry r0 →
    S (.inl 0) = blkE xs ++ r0 →
    Runs I.P S (Function.update (Function.update S (.inl 0) r0) (.inl 1)
        (blkE xs.reverse ++ S (.inl 1))) (fun _ => True)
      (C * ((blkE xs).length + 1))

/-- One instance of each sub-kernel (and of `W3_cmpNat`), with constants and specs. -/
structure Kit (Mul : ℕ → ℕ) where
  IF : Inst 7 48 Unit
  IN : Inst 8 48 Unit
  IM : Inst 2 8 Unit
  IC : Inst 2 4 Ordering
  CF : ℕ
  CN : ℕ
  CM : ℕ
  CC : ℕ
  hF : SpecFwd Mul IF CF
  hN : SpecNyq Mul IN CN
  hM : SpecMove IM CM
  hC : SpecCmpNat IC CC

theorem exists_kit (Mul : ℕ → ℕ) (hF : W9f_fwdCore Mul) (hN : W9f_nyqCore Mul)
    (hM : W9f_moveEntries) : Nonempty (Kit Mul) := by
  obtain ⟨CF, hF'⟩ := exists_inst hF
  obtain ⟨IF, hIF⟩ := hF' ()
  obtain ⟨CN, hN'⟩ := exists_inst hN
  obtain ⟨IN, hIN⟩ := hN' ()
  obtain ⟨CM, hM'⟩ := exists_inst hM
  obtain ⟨IM, hIM⟩ := hM' ()
  obtain ⟨CC, hC'⟩ := exists_inst w3_cmpNat
  obtain ⟨IC, hIC⟩ := hC' ()
  exact ⟨⟨IF, IN, IM, IC, CF, CN, CM, CC, hIF, hIN, hIM, hIC⟩⟩

variable {Mul : ℕ → ℕ} (K : Kit Mul)

/-- Host registers: macro register, then the registers of the four instances. -/
abbrev KReg : Type := Option Sym × (K.IF.R × (K.IN.R × (K.IM.R × K.IC.R)))

/-- Host programs. -/
abbrev KP : Type := Prog HL (fun _ => Sym) (KReg K)

def lS : Lens (KReg K) (Option Sym) := Lens.fst _ _
def lF : Lens (KReg K) K.IF.R := (Lens.snd _ _).comp (Lens.fst _ _)
def lN : Lens (KReg K) K.IN.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lM : Lens (KReg K) K.IM.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lC : Lens (KReg K) K.IC.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _)))

theorem kreg_finite : Finite (KReg K) := by
  haveI := K.IF.fin
  haveI := K.IN.fin
  haveI := K.IM.fin
  haveI := K.IC.fin
  infer_instance

theorem kreg_nonempty : Nonempty (KReg K) := by
  obtain ⟨a⟩ := K.IF.ne
  obtain ⟨b⟩ := K.IN.ne
  obtain ⟨c⟩ := K.IM.ne
  obtain ⟨d⟩ := K.IC.ne
  exact ⟨(none, a, b, c, d)⟩

/-- Default location of the call maps (never used: named lists are long enough). -/
def dflt : HL := .inr 63

/-- The entry mover from `src` to `dst`. -/
def mover (src dst : F) : KP K := callI K.IM [src.loc, dst.loc] dflt (lM K)

theorem nodup_pair {src dst : F} (hne : src ≠ dst) : [src.loc, dst.loc].Nodup := by
  refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
  simpa using F.loc_injective.ne hne

/-- **Entry mover** between modified host stacks. -/
theorem HT.moverF (σ0 : HL → List Sym) (s : F → List Sym) (src dst : F) (hne : src ≠ dst)
    (xs : List (ℤ × ℤ)) (r0 : List Sym) (hNE : NotEntry r0) (hs : s src = blkE xs ++ r0) :
    HT [] (henc σ0 s) (mover K src dst)
      (henc σ0 (Function.update (Function.update s src r0) dst (blkE xs.reverse ++ s dst)))
      (K.CM * ((blkE xs).length + 1)) := by
  have h := HT.callI_upd2 K.IM [src.loc, dst.loc] dflt (nodup_pair hne) rfl (by norm_num) (lM K)
    (henc σ0 s) (.inl 0) (.inl 1) _ _
    (K.hM xs r0 _ hNE (by show henc σ0 s src.loc = _; rw [henc_loc]; exact hs)) []
  refine h.of_eq ?_ le_rfl
  show Function.update (Function.update (henc σ0 s) src.loc r0) dst.loc
    (blkE xs.reverse ++ henc σ0 s dst.loc) = _
  rw [henc_loc, henc_update, henc_update]

#assert_std_axioms exists_kit kreg_finite kreg_nonempty nodup_pair HT.moverF

end WP.W9f
