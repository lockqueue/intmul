import WP.W9c.RowLib

/-!
# WP.W9c.RowHdr — `W9c_rowHdr`: the header fields of the spread, and `p_in`

`hdrProg` (local stacks `Loc 9 1`: named `C0 C1 d2 … d8`, scratch `H`): six `copyField`s from the
PRE header on `C0` (fields 0, 1, 3, 5, 6, 8: `pSub, m1, r, log₂ r, W, s`) and one `copyBlock` of
`p_in` from `C1`. `C0` and `C1` are restored. Cost `≤ 85·(|header| + |p_in| + 1)`. No hypotheses.
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability WP.W9c.RowLib IntMul

namespace RowHdr

/-- Local stacks: named `C0 C1 d2 … d8`, one scratch `H`. -/
abbrev HL : Type := Loc 9 1

/-- **The header kernel.** -/
def hdrProg : SProg HL :=
  .seq (copyField 0 (.inl 0) (.inl 2) (.inr 0)) (.seq (copyField 1 (.inl 0) (.inl 3) (.inr 0))
  (.seq (copyField 3 (.inl 0) (.inl 4) (.inr 0)) (.seq (copyField 5 (.inl 0) (.inl 5) (.inr 0))
  (.seq (copyField 6 (.inl 0) (.inl 6) (.inr 0)) (.seq (copyField 8 (.inl 0) (.inl 7) (.inr 0))
  (copyBlock (.inl 1) (.inl 8) (.inr 0)))))))

theorem closed_hdrProg : hdrProg.Closed :=
  ⟨closed_copyField _ _ _ _, closed_copyField _ _ _ _, closed_copyField _ _ _ _,
    closed_copyField _ _ _ _, closed_copyField _ _ _ _, closed_copyField _ _ _ _,
    by simp [Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody,
      restoreR, pushC, pushR, popR, Lib.skip]⟩

/-- **Local specification of the header kernel.** -/
theorem rs_hdr (pSub m1 t1 r p_in : ℕ) (r0 r1 : List Sym) (S : HL → List Sym)
    (h0 : S (.inl 0) = hdrSyms (preTapeFields pSub m1 t1 r) ++ r0)
    (h1 : S (.inl 1) = hdrSyms [p_in] ++ r1) :
    Runs hdrProg S (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update S
        (.inl 2) (natSyms pSub ++ S (.inl 2)))
        (.inl 3) (natSyms m1 ++ S (.inl 3)))
        (.inl 4) (natSyms r ++ S (.inl 4)))
        (.inl 5) (natSyms (natLog2Fuel r r) ++ S (.inl 5)))
        (.inl 6) (natSyms (effectiveFilterWidth m1 r) ++ S (.inl 6)))
        (.inl 7) (natSyms (strideOf pSub) ++ S (.inl 7)))
        (.inl 8) (natSyms p_in ++ S (.inl 8)))
      (fun _ => True) (85 * ((hdrSyms (preTapeFields pSub m1 t1 r)).length + bitLen p_in + 1)) := by
  set fs := preTapeFields pSub m1 t1 r with hfs
  have hlen : fs.length = 9 := by simp [hfs, preTapeFields]
  have e1 : Runs (copyField 0 (.inl 0) (.inl 2) (.inr 0)) S
      (Function.update S (.inl 2) (natSyms pSub ++ S (.inl 2))) (fun _ => True)
      (13 * (hdrSyms fs).length + 11) :=
    rs_copyField (by decide) (by decide) (by decide) fs 0 (by omega) r0 S h0
  set S1 := Function.update S (.inl 2) (natSyms pSub ++ S (.inl 2)) with hS1
  have e2 : Runs (copyField 1 (.inl 0) (.inl 3) (.inr 0)) S1
      (Function.update S1 (.inl 3) (natSyms m1 ++ S1 (.inl 3))) (fun _ => True)
      (13 * (hdrSyms fs).length + 11) :=
    rs_copyField (by decide) (by decide) (by decide) fs 1 (by omega) r0 S1 (by simp [hS1, h0])
  set S2 := Function.update S1 (.inl 3) (natSyms m1 ++ S1 (.inl 3)) with hS2
  have e3 : Runs (copyField 3 (.inl 0) (.inl 4) (.inr 0)) S2
      (Function.update S2 (.inl 4) (natSyms r ++ S2 (.inl 4))) (fun _ => True)
      (13 * (hdrSyms fs).length + 11) :=
    rs_copyField (by decide) (by decide) (by decide) fs 3 (by omega) r0 S2
      (by simp [hS2, hS1, h0])
  set S3 := Function.update S2 (.inl 4) (natSyms r ++ S2 (.inl 4)) with hS3
  have e4 : Runs (copyField 5 (.inl 0) (.inl 5) (.inr 0)) S3
      (Function.update S3 (.inl 5) (natSyms (natLog2Fuel r r) ++ S3 (.inl 5))) (fun _ => True)
      (13 * (hdrSyms fs).length + 11) :=
    rs_copyField (by decide) (by decide) (by decide) fs 5 (by omega) r0 S3
      (by simp [hS3, hS2, hS1, h0])
  set S4 := Function.update S3 (.inl 5) (natSyms (natLog2Fuel r r) ++ S3 (.inl 5)) with hS4
  have e5 : Runs (copyField 6 (.inl 0) (.inl 6) (.inr 0)) S4
      (Function.update S4 (.inl 6) (natSyms (effectiveFilterWidth m1 r) ++ S4 (.inl 6)))
      (fun _ => True) (13 * (hdrSyms fs).length + 11) :=
    rs_copyField (by decide) (by decide) (by decide) fs 6 (by omega) r0 S4
      (by simp [hS4, hS3, hS2, hS1, h0])
  set S5 := Function.update S4 (.inl 6) (natSyms (effectiveFilterWidth m1 r) ++ S4 (.inl 6))
    with hS5
  have e6 : Runs (copyField 8 (.inl 0) (.inl 7) (.inr 0)) S5
      (Function.update S5 (.inl 7) (natSyms (strideOf pSub) ++ S5 (.inl 7))) (fun _ => True)
      (13 * (hdrSyms fs).length + 11) :=
    rs_copyField (by decide) (by decide) (by decide) fs 8 (by omega) r0 S5
      (by simp [hS5, hS4, hS3, hS2, hS1, h0])
  set S6 := Function.update S5 (.inl 7) (natSyms (strideOf pSub) ++ S5 (.inl 7)) with hS6
  have e7 := rs_copy (src := (.inl 1 : HL)) (dst := .inl 8) (tmp := .inr 0) (by decide)
    (by decide) (by decide) p_in (Sym.mark :: r1) S6 (TermOK.cons rfl _)
    (by simp [hS6, hS5, hS4, hS3, hS2, hS1, h1, hdrSyms_cons, hdrSyms_nil])
  refine runs_post (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4 (runs_seq e5
    (runs_seq e6 e7)))))) ?_ ?_
  · funext x
    rcases x with i | j
    · fin_cases i <;> simp [hS6, hS5, hS4, hS3, hS2, hS1]
    · fin_cases j
      simp [hS6, hS5, hS4, hS3, hS2, hS1]
  · omega

end RowHdr

/-- **`W9c_rowHdr` holds** (no hypotheses). -/
theorem w9c_rowHdr_holds : W9c_rowHdr := by
  refine ⟨85, fun _ => ⟨1, Option Sym, fun _ => (), RowHdr.hdrProg, by decide, inferInstance,
    ⟨none⟩, RowHdr.closed_hdrProg, ?_⟩⟩
  intro pSub m1 t1 r p_in r0 r1 S h0 h1
  exact RowHdr.rs_hdr pSub m1 t1 r p_in r0 r1 S h0 h1

#assert_std_axioms RowHdr.closed_hdrProg RowHdr.rs_hdr w9c_rowHdr_holds

end WP.W9c
