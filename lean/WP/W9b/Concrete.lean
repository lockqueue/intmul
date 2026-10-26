import WP.Inst.W4
import WP.F9.InstB
import WP.W9b.AltSum
import WP.W9b.Emit
import WP.W9b.Transpose

/-!
# WP.W9b.Concrete — concrete programs for the W9b kernels P1, P2, P8

For each kernel, `progC` is **exactly** the witness program of its `_holds` theorem, with every
subroutine taken from the shared instance modules (`WP.Inst.W4`, `WP.Inst.W3`, `WP.F9.InstB`):

| namespace | contract | `progC` | `mC` | `RC` |
|---|---|---|---|---|
| `P1` | `W9_preTranspose` | `(tProg (WP.Inst.transpose.prog .down .up) _).mapStk tι` | 8 | `TReg CReg` |
| `P2` | `W9_altSum` | `(altKernel kitC).mapStk aι` | 24 | `KReg kitC` |
| `P8` | `W9_emitRows` | `emitProg.mapStk eι` | 6 | `Option Sym` |

`kitC`, the W3 kit of P2, is `WP.Inst.{addInt, subInt, addNat, subNat, shlVar, shrVar}`. `r0C` is
the nonemptiness witness of the `_holds` proof built from the instances' `r0`, and `closedC` is its
closedness term built from the instances' `closed`. The runs are in `WP.W9b.ConcreteRun`.

Contract bodies (`specC`), each re-proved with the proof of the `_holds` theorem:
* P1: `specC` at constant `64 + 40`. W4's constant is `64`, and `trSpecC` is `WP.Inst.transpose.ok`'s
  proof specialized to `.down .up`. `holdsC : W9_preTranspose` uses exactly `progC`.
* P8: `specC` at constant `35`, and `holdsC : W9_emitRows`.
* P2: `specC_of (hok : W3Ok kitC C)` at constant `1100·(C+1)`, and `holdsC_of`. An unconditional
  version needs non-existential spec lemmas for the instance programs. `WP.Inst.W3Ok` only states
  the existential contracts `W3_<c>`.
-/

namespace WP.W9b.Concrete

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

/-! ## P1 (`W9_preTranspose`) -/

namespace P1

/-- Scratch count of P1. -/
abbrev mC : ℕ := 8

/-- Registers of P1: the kernel's symbol register and the W4 transpose's registers. -/
abbrev RC : Type := TReg WP.Inst.transpose.R

/-- Initial registers of P1. -/
def r0C : RC := (none, WP.Inst.transpose.r0)

/-- **P1**: the witness of `W9_preTranspose_holds`, with the verified W4 transpose (`.down .up`). -/
def progC : Prog (BLoc mC) (fun _ => Sym) RC :=
  (tProg (WP.Inst.transpose.prog .down .up) (le_refl 4)).mapStk tι

theorem hmC : mC ≤ w9Scratch := by decide

theorem closedC : progC.Closed :=
  closed_mapStk _ (closed_tProg (le_refl 4) (WP.Inst.transpose.closed .down .up))

end P1

/-! ## P2 (`W9_altSum`) -/

namespace P2

/-- The W3 kit of P2, from the instances. -/
def kitC : W3Kit :=
  ⟨WP.Inst.addInt.m, WP.Inst.addInt.R, WP.Inst.addInt.prog, by decide,
    WP.Inst.subInt.m, WP.Inst.subInt.R, WP.Inst.subInt.prog, by decide,
    WP.Inst.addNat.m, WP.Inst.addNat.R, WP.Inst.addNat.prog, by decide,
    WP.Inst.subNat.m, WP.Inst.subNat.R, WP.Inst.subNat.prog, by decide,
    WP.Inst.shlVar.m, WP.Inst.shlVar.R, WP.Inst.shlVar.prog, by decide,
    WP.Inst.shrVar.m, WP.Inst.shrVar.R, WP.Inst.shrVar.prog, by decide⟩

/-- Scratch count of P2. -/
abbrev mC : ℕ := 24

/-- Registers of P2. -/
abbrev RC : Type := KReg kitC

/-- Initial registers of P2. -/
def r0C : RC :=
  (none, (none, none, .eq), WP.Inst.addInt.r0, WP.Inst.subInt.r0, WP.Inst.addNat.r0,
    WP.Inst.subNat.r0, WP.Inst.shlVar.r0, WP.Inst.shrVar.r0)

/-- **P2**: the witness of `W9_altSum_holds`, with the W3 kit `kitC`. -/
def progC : Prog (BLoc mC) (fun _ => Sym) RC := (altKernel kitC).mapStk aι

theorem hmC : mC ≤ w9Scratch := by decide

theorem closedC : progC.Closed :=
  closed_mapStk _ (closed_altKernel kitC WP.Inst.addInt.closed WP.Inst.subInt.closed
    WP.Inst.addNat.closed WP.Inst.subNat.closed WP.Inst.shlVar.closed WP.Inst.shrVar.closed)

end P2

/-! ## P8 (`W9_emitRows`) -/

namespace P8

/-- Scratch count of P8. -/
abbrev mC : ℕ := 6

/-- Registers of P8. -/
abbrev RC : Type := Option Sym

/-- Initial registers of P8. -/
def r0C : RC := none

/-- **P8**: the witness of `W9_emitRows_holds` (no subroutines). -/
def progC : Prog (BLoc mC) (fun _ => Sym) RC := emitProg.mapStk eι

theorem hmC : mC ≤ w9Scratch := by decide

theorem closedC : progC.Closed := closed_mapStk _ closed_emitProg

end P8

#assert_std_axioms P1.hmC P1.closedC P2.hmC P2.closedC P8.hmC P8.closedC

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability IntMul IntMul.LevelSync

attribute [local instance 10000] instZeroIntElementary

/-! ## Contract bodies for `progC` (`specC`) -/

namespace P1

/-- The W4 transpose instance satisfies what P1 needs of it (`TrSpec`) at W4's constant `64`. The
proof is that of `WP.Inst.transpose.ok`, specialized to `.down .up`. -/
theorem trSpecC : TrSpec (WP.Inst.transpose.prog .down .up) 64 := by
  intro a b v rest r2 r3 S hlen hrec hrest hr2 hr3 hS0 hS2 hS3
  have hblk : (blk .down v).length = v.flatten.length := by simp [blk]
  have hNL : 2 ^ a * 2 ^ b ≤ v.flatten.length := by
    rw [← hlen]
    exact TMFw.W4.length_le_length_flatten v hrec
  rw [hblk]
  exact Triple.cost_mono (TMFw.W4.transposeProgP_spec TMFw.W4.riffOK .down .up a b v rest r2 r3 S
    hlen hrec hrest hr2 hr3 hS0 hS2 hS3) (TMFw.W4.cost_le a b _ hNL)

/-- The body of `W9_preTranspose` for `(tProg P4 hm4).mapStk tι` at constant `C4 + 40`, for any
`P4` with `TrSpec P4 C4`. The proof is that of `W9_preTranspose_holds`. -/
theorem spec_of {m4 : ℕ} {R4 : Type} {P4 : Prog (Loc 4 m4) (fun _ => Sym) R4} (hm4 : m4 ≤ 4)
    {C4 : ℕ} (hP : TrSpec P4 C4) :
    ∀ (h : PreHdr) (w : ℕ) (x : Array (ℤ × ℤ)) (σ : BLoc 8 → List Sym),
      PreDims h → PreCtx h σ → x.size = h.N → ArrW w x → MatW w (w9XRows h.t1 h.r x) →
      σ (.inl .W0) = blkE x.toList →
      Runs ((tProg P4 hm4).mapStk tι) σ
        (Function.update σ (.inl .W0) (matSyms (w9XRows h.t1 h.r x))) (fun _ => True)
        ((C4 + 40) * preTransposeBound w h) := by
  intro h w x σ hdims hctx hx hxw hxr hW0
  obtain ⟨⟨r0, hC0⟩, -⟩ := hctx
  have hloc := tLocal_runs hm4 hP (fun k => σ (tι k)) h x r0 hdims hC0 hx hW0
  refine runs_mono (runs_embed_upd tι_inj σ TStk.W0 _ hloc) (fun _ _ => trivial) ?_
  have hb : (blkE x.toList).length ≤ h.N * eb w := by
    have := length_blkE_le w x.toList hxw
    rwa [show x.toList.length = h.N by simp [hx]] at this
  have hm : (matSyms (w9XRows h.t1 h.r x)).length ≤ h.N * eb w :=
    length_matSyms_le w h.t1 h.r _ (w9XRows_size _ _ _) (w9XRows_rows _ _ _) hxr
  have hH : (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length ≤ h.hdrLen := by
    unfold PreHdr.hdrLen
    omega
  have hb1 := bitLen_le_self h.mr
  have hb2 := bitLen_le_self h.mt1
  have hmin : min h.mr h.mt1 = min h.mt1 h.mr := Nat.min_comm _ _
  rw [hmin]
  have hX1 : C4 * ((blkE x.toList).length + 1) * (min h.mt1 h.mr + 1) ≤
      C4 * ((h.N * eb w + 1) * (min h.mt1 h.mr + 1)) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  have hX2 : C4 * (bitLen h.mr + bitLen h.mt1 + 1) ≤ C4 * (h.mt1 + h.mr + h.hdrLen + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hX3 : h.N * eb w + 1 ≤ (h.N * eb w + 1) * (min h.mt1 h.mr + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hexp : (C4 + 40) * preTransposeBound w h =
      C4 * ((h.N * eb w + 1) * (min h.mt1 h.mr + 1)) + C4 * (h.mt1 + h.mr + h.hdrLen + 1) +
        40 * ((h.N * eb w + 1) * (min h.mt1 h.mr + 1)) + 40 * (h.mt1 + h.mr + h.hdrLen + 1) := by
    unfold preTransposeBound
    ring
  rw [hexp]
  omega

/-- **The body of `W9_preTranspose` for `progC`**, at constant `64 + 40`. -/
theorem specC : ∀ (h : PreHdr) (w : ℕ) (x : Array (ℤ × ℤ)) (σ : BLoc mC → List Sym),
    PreDims h → PreCtx h σ → x.size = h.N → ArrW w x → MatW w (w9XRows h.t1 h.r x) →
    σ (.inl .W0) = blkE x.toList →
    Runs progC σ (Function.update σ (.inl .W0) (matSyms (w9XRows h.t1 h.r x))) (fun _ => True)
      ((64 + 40) * preTransposeBound w h) :=
  spec_of (le_refl 4) trSpecC

/-- `W9_preTranspose`, with exactly `progC`, `r0C`, `closedC` as the witness. -/
theorem holdsC : W9_preTranspose :=
  ⟨64 + 40, fun _ => ⟨mC, RC, progC, hmC, inferInstance, ⟨r0C⟩, closedC, specC⟩⟩

end P1

namespace P2

/-- `RC` is finite. -/
theorem finiteRC : Finite RC := by
  show Finite (Option Sym × CReg × WP.Inst.addInt.R × WP.Inst.subInt.R × WP.Inst.addNat.R ×
    WP.Inst.subNat.R × WP.Inst.shlVar.R × WP.Inst.shrVar.R)
  infer_instance

/-- **The body of `W9_altSum` for `progC`**, given the kit's specs at a common constant `C`
(`W3Ok kitC C`). The constant is `1100·(C+1)`, and the proof is that of `W9_altSum_holds`. -/
theorem specC_of {C : ℕ} (hok : W3Ok kitC C) :
    ∀ (h : PreHdr) (w : ℕ) (xRows : Array (Array (ℤ × ℤ))) (σ : BLoc mC → List Sym),
      PreDims h → PreCtx h σ → xRows.size = h.t1 → (∀ row ∈ xRows.toList, row.size = h.r) →
      MatW w xRows →
      EntryW w (computableNyquistAltSumContiguous h.p_in h.pSub h.r (xRows.getD (h.t1 / 2) #[])) →
      σ (.inl .W0) = matSyms xRows →
      Runs progC σ (Function.update σ (.inl .RET)
          ((entrySyms (computableNyquistAltSumContiguous h.p_in h.pSub h.r
            (xRows.getD (h.t1 / 2) #[]))).reverse ++ σ (.inl .RET))) (fun _ => True)
        (1100 * (C + 1) * altSumBound w h) := by
  intro h w xRows σ hdims hctx hsize hrows hW hout hW0
  obtain ⟨⟨r0, hC0⟩, ⟨r1, hC1⟩⟩ := hctx
  have hloc := rs_altKernel kitC hok h w xRows (fun x => σ (aι x)) r0 r1 hdims hC0 hC1 hsize
    hrows hW hout hW0
  exact runs_mono (runs_embed_upd aι_inj σ AStk.RET _ hloc) (fun _ _ => trivial) le_rfl

/-- `W9_altSum` with exactly `progC`, `r0C`, `closedC` as the witness, given `W3Ok kitC C`. -/
theorem holdsC_of {C : ℕ} (hok : W3Ok kitC C) : W9_altSum :=
  ⟨1100 * (C + 1), fun _ => ⟨mC, RC, progC, hmC, finiteRC, ⟨r0C⟩, closedC, specC_of hok⟩⟩

end P2

namespace P8

/-- **The body of `W9_emitRows` for `progC`**, at constant `35`. The proof is that of
`W9_emitRows_holds`. -/
theorem specC : ∀ (h : PreHdr) (w : ℕ) (M : Array (Array (ℤ × ℤ))) (σ : BLoc mC → List Sym),
    PreCtx h σ → M.size = h.t1 → (∀ row ∈ M.toList, row.size = h.r) → MatW w M →
    σ (.inl .W0) = matSyms M →
    Runs progC σ (Function.update σ (.inl .W0) (M.toList.flatMap nodeSyms)) (fun _ => True)
      (35 * emitBound w h) := by
  intro h w M σ hctx hsize hrows hW hW0
  obtain ⟨⟨r0, hC0⟩, -⟩ := hctx
  have hloc := emit_runs (fun k => σ (eι k)) h.pSub h.m1 h.t1 h.r r0 M hC0 hW0 hsize hrows
  refine runs_mono (runs_embed_upd eι_inj σ EStk.W0 _ hloc) (fun _ _ => trivial) ?_
  have hm := length_matSyms_le w h.t1 h.r M hsize hrows hW
  have heb : 1 ≤ eb w := by unfold eb; omega
  have hN : h.t1 * h.r ≤ h.t1 * h.r * eb w := Nat.le_mul_of_pos_right _ heb
  have hH : (hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r)).length ≤ h.hdrLen := by
    unfold PreHdr.hdrLen
    omega
  unfold emitBound PreHdr.N
  omega

/-- `W9_emitRows`, with exactly `progC`, `r0C`, `closedC` as the witness. -/
theorem holdsC : W9_emitRows :=
  ⟨35, fun _ => ⟨mC, RC, progC, hmC, inferInstance, ⟨r0C⟩, closedC, specC⟩⟩

end P8

#assert_std_axioms P1.trSpecC P1.spec_of P1.specC P1.holdsC P2.finiteRC P2.specC_of P2.holdsC_of
  P8.specC P8.holdsC

end WP.W9b.Concrete
