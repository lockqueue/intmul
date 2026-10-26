import WP.W9fN.Lay8
import WP.W9fN.FinishSpec
import WP.W7k2.Call

/-!
# WP.W9fN.FinCall — calling the Nyquist finish (`W9f_nyqFinish`) on the core's host stacks

Host-stack call adapter for `WP.W9fN`. The finish's named stacks are mapped to
`[kZS, kOUT, kPK, kPALT]`; its scratch goes to free host stacks (W7k2 `callI`).
-/

namespace WP.W9fN

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2

/-- Named stacks of the finish call: Z store, OUT, `k`, `alt`. -/
def finNamed : List HK := [kZS, kOUT, kPK, kPALT]

theorem finNamed_nodup : finNamed.Nodup := by decide

/-- **Finish call rule.** -/
theorem finCall_runs {σ : Type} (IF : Inst 4 48 Unit) (CF : ℕ)
    (hF : ∀ (H k : ℕ) (alt : ℤ × ℤ) (Z : Array (ℤ × ℤ)) (rZ r2 r3 : List Sym)
      (S : Loc 4 IF.m → List Sym),
      Z.size = 2 ^ k → 1 ≤ k → ArrW (H + 1) Z → EntryW H alt →
      (∀ s, rZ.head? = some s → s ≠ Sym.pos ∧ s ≠ Sym.neg) → TermOK r2 →
      S (.inl 0) = blkE Z.toList.reverse ++ rZ → S (.inl 2) = natSyms k ++ r2 →
      S (.inl 3) = entrySyms alt ++ r3 →
      Runs IF.P S (Function.update (Function.update S (.inl 0) rZ) (.inl 1)
        (blkE (WP.W9f.nyqOut k alt Z).toList ++ S (.inl 1))) (fun _ => True)
        (CF * (Z.size * (H + k + 1) + (H + 1) ^ 2)))
    (l : Lens σ IF.R) (B : HK → List Sym) (H k : ℕ) (alt : ℤ × ℤ) (Z : Array (ℤ × ℤ))
    (rZ r2 r3 : List Sym) (hsz : Z.size = 2 ^ k) (hk : 1 ≤ k) (hZ : ArrW (H + 1) Z)
    (halt : EntryW H alt) (hrZ : WP.W9f.NotEntry rZ) (hr2 : TermOK r2)
    (h0 : B kZS = blkE Z.toList.reverse ++ rZ) (h2 : B kPK = natSyms k ++ r2)
    (h3 : B kPALT = entrySyms alt ++ r3) :
    HT [] B (callI IF finNamed kTMP l)
      (Function.update (Function.update B kZS rZ) kOUT
        (blkE (WP.W9f.nyqOut k alt Z).toList ++ B kOUT))
      (CF * (Z.size * (H + k + 1) + (H + 1) ^ 2)) := by
  have h := HT.callI_upd2 IF finNamed kTMP finNamed_nodup rfl (by norm_num) l B (.inl 0) (.inl 1)
    _ _ (hF H k alt Z rZ r2 r3 _ hsz hk hZ halt hrZ hr2 h0 h2 h3) []
  exact h

#assert_std_axioms finNamed_nodup finCall_runs

end WP.W9fN
