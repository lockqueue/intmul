import WP.W9cS.Driver

/-!
# WP.W9cS.DriverSpec — the driver's triple

Prologue (+ peek), row loop, epilogue. The header on `C0` gives the row length `r` as its 4th
field; the kernel is used through `KerOK` for every row.
-/

namespace WP.W9c

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 TMFw.W4 Computability

variable {K R : Type} [DecidableEq K]

/-- **The driver.** -/
theorem driver_spec {e : DS → K} (he : Function.Injective e) (kerP : BProg K R) (a b c r : ℕ)
    (hr : 0 < r) (rest0 c1 : List Sym) (Ck Lr : ℕ)
    (Ls : List (List (ℤ × ℤ) × List (ℤ × ℤ) × List Sym)) (x : Sym) (restT : List Sym)
    (S : K → List Sym)
    (hC : S (e .C0) = natSyms a ++ Sym.mark :: (natSyms b ++ Sym.mark :: (natSyms c ++ Sym.mark ::
      (natSyms r ++ Sym.mark :: rest0))))
    (hC1 : S (e .C1) = c1)
    (hLs : ∀ y ∈ Ls, y.1.length = r ∧ (blkE y.1).length ≤ Lr ∧ (blkE y.2.1).length ≤ Lr ∧
      KerOK e kerP (S (e .C0)) c1 Ck y)
    (hW : S (e .W0) = blkE (Ls.flatMap (·.1))) (hTR : S (e .TR) = Ls.flatMap (·.2.2) ++ x :: restT) :
    RunsIn [] (driver e kerP) S
      (Function.update (Function.update (Function.update S (e .W0) (blkE (Ls.flatMap (·.2.1))))
        (e .TR) restT) (e .TL) (x :: ((Ls.flatMap (·.2.2)).reverse ++ S (e .TL))))
      (6 * (bitLen a + bitLen b + bitLen c) + 9 * bitLen r + 6 * (blkE (Ls.flatMap (·.1))).length +
        3 * (blkE (Ls.flatMap (·.2.1))).length +
        Ls.length * (Ck + 7 * bitLen r + 16 * r + 9 * Lr + 17) + 72) := by
  intro v
  obtain ⟨v1, t1, e1, ht1⟩ := prologue_spec he a b c r rest0 _ S hC hW v.1
  set Sp := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update S (e .IN) (blkE (Ls.flatMap (·.1)) ++ Sym.mark :: S (e .IN)))
    (e .T) (Sym.mark :: S (e .T))) (e .OUT) (Sym.mark :: S (e .OUT))) (e .RS)
    (natSyms r ++ Sym.mark :: S (e .RS))) (e .Q) (Sym.mark :: S (e .Q))) (e .TMP)
    (Sym.mark :: S (e .TMP))) (e .W0) [] with hSp
  have e2 := Eval.peek [] (e .IN) (fun _ o => o) v1 Sp
  have e12 := Eval.liftRegs (Lens.fst (Option Sym) R) (Eval.seq e1 e2) v rfl
  obtain ⟨v2, t2, e3, ht2⟩ := rowLoop_spec he kerP (S (e .C0)) c1 Ck r Lr hr Ls Sp (S (e .IN))
    (x :: restT) (S (e .Q)) (S (e .T)) (S (e .RS)) hLs (by simp [hSp, he.eq_iff])
    (by simp [hSp]) (by simp [hSp, he.eq_iff]) (by simp [hSp, he.eq_iff])
    (by simp [hSp, he.eq_iff]) (by simp [hSp, he.eq_iff, hTR]) (by simp [hSp, he.eq_iff])
    (by simp [hSp, he.eq_iff, hC1]) ((Lens.fst (Option Sym) R).set v (Sp (e .IN)).head?) rfl
  set Sl := Function.update (Function.update (Function.update (Function.update Sp (e .IN)
    (Sym.mark :: S (e .IN))) (e .OUT) ((blkE (Ls.flatMap (·.2.1))).reverse ++ Sp (e .OUT)))
    (e .TR) (x :: restT)) (e .TL) ((Ls.flatMap (·.2.2)).reverse ++ Sp (e .TL)) with hSl
  obtain ⟨v3, t3, e4, ht3⟩ := lf_runs (R := R) (epilogue_spec he r (Ls.flatMap (·.2.1)) x restT
    (S (e .IN)) (S (e .T)) (S (e .OUT)) (S (e .Q)) (S (e .TMP)) (S (e .RS)) Sl
    (by simp [hSl, hSp, he.eq_iff]) (by simp [hSl, hSp, he.eq_iff]) (by simp [hSl, hSp, he.eq_iff])
    (by simp [hSl, hSp, he.eq_iff]) (by simp [hSl, hSp, he.eq_iff]) (by simp [hSl, hSp, he.eq_iff])
    (by simp [hSl, hSp, he.eq_iff]) (by simp [hSl, hSp, he.eq_iff])) v2
  refine ⟨v3, _, (Eval.seq e12 (Eval.seq e3 e4)).of_eq ?_ rfl, by omega⟩
  congr 1
  refine ext_DS (e := e) (fun k hk => ?_) (fun d => ?_)
  · simp [hSl, hSp, Function.update_apply, hk]
  · cases d <;> simp [hSl, hSp, he.eq_iff]

#assert_std_axioms driver_spec

end WP.W9c
