import WP.W9cS.Ends

/-!
# WP.W9cS.Driver — the spread driver (generic in the stacks and the row kernel)

`driver e kerP = lf (prologue; peek IN); rowLoop e kerP; lf epilogue`. From
`W0 = blkE (rows)`, `TR = (filter rows) ++ x :: restT` and the header on `C0` it produces
`W0 = blkE (outputs)`, `TR = restT`, `TL = x :: (filter rows).reverse ++ TL`; every other stack
is restored.
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 TMFw.W4 Computability

variable {K R : Type}

/-- The driver. -/
def driver (e : DS → K) (kerP : BProg K R) : BProg K R :=
  .seq (lf (.seq (prologue e) (peekR (e .IN)))) (.seq (rowLoop e kerP) (lf (epilogue e)))

theorem driver_closed (e : DS → K) {kerP : BProg K R} (hk : kerP.Closed) :
    (driver e kerP).Closed :=
  ⟨lf_closed ⟨prologue_closed e, by simp [Prog.FreeBelow, peekR]⟩, rowLoop_closed e hk,
    lf_closed (epilogue_closed e)⟩

variable [DecidableEq K]

omit [DecidableEq K] in
/-- Extensionality over the driver's stacks. -/
theorem ext_DS {e : DS → K} {S T : K → List Sym}
    (hout : ∀ k, (∀ d, k ≠ e d) → S k = T k) (hin : ∀ d, S (e d) = T (e d)) : S = T := by
  funext k
  by_cases h : ∃ d, e d = k
  · obtain ⟨d, rfl⟩ := h
    exact hin d
  · exact hout k fun d hd => h ⟨d, hd.symm⟩

theorem prologue_spec {e : DS → K} (he : Function.Injective e) (a b c r : ℕ) (rest0 : List Sym)
    (all : List (ℤ × ℤ)) (S : K → List Sym)
    (hC : S (e .C0) = natSyms a ++ Sym.mark :: (natSyms b ++ Sym.mark :: (natSyms c ++ Sym.mark ::
      (natSyms r ++ Sym.mark :: rest0))))
    (hW : S (e .W0) = blkE all) :
    RunsIn [] (prologue e) S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S (e .IN) (blkE all ++ Sym.mark :: S (e .IN))) (e .T)
        (Sym.mark :: S (e .T))) (e .OUT) (Sym.mark :: S (e .OUT))) (e .RS)
        (natSyms r ++ Sym.mark :: S (e .RS))) (e .Q) (Sym.mark :: S (e .Q))) (e .TMP)
        (Sym.mark :: S (e .TMP))) (e .W0) [])
      (6 * (bitLen a + bitLen b + bitLen c) + 7 * bitLen r + 6 * (blkE all).length + 55) := by
  have r1 := pushC_runs' (e .IN) Sym.mark S
  set S1 := Function.update S (e .IN) (Sym.mark :: S (e .IN)) with hS1
  have r2 := pushC_runs' (e .T) Sym.mark S1
  set S2 := Function.update S1 (e .T) (Sym.mark :: S1 (e .T)) with hS2
  have r3 := pushC_runs' (e .OUT) Sym.mark S2
  set S3 := Function.update S2 (e .OUT) (Sym.mark :: S2 (e .OUT)) with hS3
  have r4 := pushC_runs' (e .RS) Sym.mark S3
  set S4 := Function.update S3 (e .RS) (Sym.mark :: S3 (e .RS)) with hS4
  have r5 := pushC_runs' (e .Q) Sym.mark S4
  set S5 := Function.update S4 (e .Q) (Sym.mark :: S4 (e .Q)) with hS5
  have r6 := pushC_runs' (e .TMP) Sym.mark S5
  set S6 := Function.update S5 (e .TMP) (Sym.mark :: S5 (e .TMP)) with hS6
  have r7 := getF4_spec (C0 := e .C0) (RS := e .RS) (TMP := e .TMP) (Q := e .Q)
    (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
    (he.ne (by decide)) (he.ne (by decide)) [] a b c r rest0 (S5 (e .TMP)) S6
    (by simp [hS6, hS5, hS4, hS3, hS2, hS1, he.eq_iff, hC]) (by simp [hS6])
  set S7 := Function.update S6 (e .RS) (natSyms r ++ S6 (e .RS)) with hS7
  have hS7W : S7 (e .W0) = blkE all ++ [] := by
    simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, he.eq_iff, hW]
  have r8 : RunsIn [] (moveAll (e .W0) (e .T)) S7
      (Function.update (Function.update S7 (e .W0) ([] : List Sym).tail) (e .T)
        ((blkE all).reverse ++ S7 (e .T))) (3 * (blkE all).length + 2) :=
    RunsIn.of_eval (f := fun _ => ([] : List Sym).head?) (fun v => moveAll_eval
      (he.ne (by decide)) [] v (blkE all) [] S7 (isRecSym_of_mem_flatten recOK_of_mem_map)
      (fun d hd => by simp at hd) hS7W) le_rfl
  set S8 := Function.update (Function.update S7 (e .W0) ([] : List Sym).tail) (e .T)
    ((blkE all).reverse ++ S7 (e .T)) with hS8
  have hS8T : S8 (e .T) = (blkE all).reverse ++ Sym.mark :: S (e .T) := by
    simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, he.eq_iff]
  have r9 : RunsIn [] (moveBlk (e .T) (e .IN)) S8
      (Function.update (Function.update S8 (e .T) (Sym.mark :: S (e .T))) (e .IN)
        ((blkE all).reverse.reverse ++ S8 (e .IN))) (3 * (blkE all).reverse.length + 4) :=
    RunsIn.of_eval (f := fun _ => (Sym.mark :: S (e .T)).head?) (fun v => moveBlk_eval
      (he.ne (by decide)) [] v (blkE all).reverse (Sym.mark :: S (e .T)) S8
      (isRecSym_of_mem_reverse_flatten recOK_of_mem_map) (RecTerm.mark _) hS8T) le_rfl
  refine RunsIn.of_eq ((r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).seq (r7.seq
    (r8.seq r9))) ?_ (by simp only [List.length_reverse]; omega)
  refine ext_DS (e := e) (fun k hk => ?_) (fun d => ?_)
  · simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply, hk]
  · cases d <;> simp [hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, he.eq_iff]

theorem epilogue_spec {e : DS → K} (he : Function.Injective e) (r : ℕ) (U : List (ℤ × ℤ))
    (x : Sym) (restT IN0 T0 OUT0 Q0 TMP0 RS0 : List Sym) (S : K → List Sym)
    (hW : S (e .W0) = []) (hOUT : S (e .OUT) = (blkE U).reverse ++ Sym.mark :: OUT0)
    (hTR : S (e .TR) = x :: restT) (hIN : S (e .IN) = Sym.mark :: IN0)
    (hT : S (e .T) = Sym.mark :: T0) (hQ : S (e .Q) = Sym.mark :: Q0)
    (hTMP : S (e .TMP) = Sym.mark :: TMP0) (hRS : S (e .RS) = natSyms r ++ Sym.mark :: RS0) :
    RunsIn [] (epilogue e) S
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update S (e .W0) (blkE U))
        (e .OUT) OUT0) (e .TR) restT) (e .TL) (x :: S (e .TL))) (e .IN) IN0) (e .T) T0) (e .Q) Q0)
        (e .TMP) TMP0) (e .RS) RS0)
      (3 * (blkE U).length + 2 * bitLen r + 15) := by
  have r1 : RunsIn [] (moveBlk (e .OUT) (e .W0)) S
      (Function.update (Function.update S (e .OUT) (Sym.mark :: OUT0)) (e .W0)
        ((blkE U).reverse.reverse ++ S (e .W0))) (3 * (blkE U).reverse.length + 4) :=
    RunsIn.of_eval (f := fun _ => (Sym.mark :: OUT0).head?) (fun v => moveBlk_eval
      (he.ne (by decide)) [] v (blkE U).reverse (Sym.mark :: OUT0) S
      (isRecSym_of_mem_reverse_flatten recOK_of_mem_map) (RecTerm.mark _) hOUT) le_rfl
  set S1 := Function.update (Function.update S (e .OUT) (Sym.mark :: OUT0)) (e .W0)
    ((blkE U).reverse.reverse ++ S (e .W0)) with hS1
  have r2 := xferTop_spec (src := e .TR) (dst := e .TL) (he.ne (by decide)) [] x restT S1
    (by simp [hS1, he.eq_iff, hTR])
  set S2 := Function.update (Function.update S1 (e .TR) restT) (e .TL) (x :: S1 (e .TL)) with hS2
  have r3 := popR_runs' (e .IN) S2
  set S3 := Function.update S2 (e .IN) (S2 (e .IN)).tail with hS3
  have r4 := popR_runs' (e .T) S3
  set S4 := Function.update S3 (e .T) (S3 (e .T)).tail with hS4
  have r5 := popR_runs' (e .OUT) S4
  set S5 := Function.update S4 (e .OUT) (S4 (e .OUT)).tail with hS5
  have r6 := popR_runs' (e .Q) S5
  set S6 := Function.update S5 (e .Q) (S5 (e .Q)).tail with hS6
  have r7 := popR_runs' (e .TMP) S6
  set S7 := Function.update S6 (e .TMP) (S6 (e .TMP)).tail with hS7
  have r8 := drain_spec (e .RS) [] r RS0 S7
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, he.eq_iff, hRS])
  refine RunsIn.of_eq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))))) ?_
    (by simp only [List.length_reverse]; omega)
  refine ext_DS (e := e) (fun k hk => ?_) (fun d => ?_)
  · simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply, hk]
  · cases d <;> simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, he.eq_iff, hW, hIN, hT, hQ, hTMP]

#assert_std_axioms driver_closed ext_DS prologue_spec epilogue_spec

end WP.W9c
