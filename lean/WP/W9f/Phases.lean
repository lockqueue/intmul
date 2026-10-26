import WP.W9f.RegBwd

/-!
# WP.W9f.Phases — guards, header phase, cleanup

* `pushAll gs`: push a guard `mark` on each private stack (`HT.pushAll`).
* `hdrPhase`: copy `pSub → PQ`, `r/2 → RH` (copy `r`, pop its low zero bit), `log t1 → PK`,
  `H → PH` from the header on `C0` (`HT.hdrPhase`).
* `cleanup`: drop the parameter copies and pop all guards (`HT.cleanup`).
-/

namespace WP.W9f

open IntMul TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 Computability

theorem natSyms_double {m : ℕ} (hm : 0 < m) : natSyms (2 * m) = Sym.bit false :: natSyms m := by
  unfold natSyms
  rw [two_mul, encodeNat_add, if_neg (by rw [encodeNat_eq_nil_iff]; omega)]
  rfl

variable {Mul : ℕ → ℕ} (K : Kit Mul)

/-- The private stacks of the composition, each guarded by a `mark`. -/
def privs : List F := [.X, .X', .TT, .PQ, .PH, .PK, .PMU, .PA, .PC, .RH]

/-- Push a `mark` on every stack of `gs`. -/
def pushAll : List F → KP K
  | [] => skip
  | f :: gs => (pushS f.loc Sym.mark).seq (pushAll gs)

/-- `s` with a `mark` pushed on every stack of `gs`. -/
def withMarks (gs : List F) (s : F → List Sym) (f : F) : List Sym :=
  if f ∈ gs then Sym.mark :: s f else s f

theorem HT.pushAll (σ0 : HL → List Sym) : ∀ (gs : List F) (s : F → List Sym), gs.Nodup →
    HT [] (henc σ0 s) (pushAll K gs) (henc σ0 (withMarks gs s)) (gs.length + 1)
  | [], s, _ =>
    (HT.skipH (σ := KReg K) _).of_eq (congrArg _ (funext fun f => by simp [withMarks])) (by simp)
  | f :: gs, s, hnd => by
    have h1 := HT.pushF (σ := KReg K) σ0 s f Sym.mark
    have h2 := HT.pushAll σ0 gs (Function.update s f (Sym.mark :: s f)) (List.nodup_cons.mp hnd).2
    refine (HT.seq h1 h2).of_eq ?_ (by simp only [List.length_cons]; omega)
    congr 1
    funext g
    have hf : f ∉ gs := (List.nodup_cons.mp hnd).1
    by_cases hg : g = f
    · subst hg
      simp [withMarks, hf]
    · simp [withMarks, hg]

/-- Drop a natural and its guard. -/
def dnm (f : F) : KP K := ((dropBits f.loc).liftRegs (lS K)).seq (popS f.loc)

/-- Drop a signed number and its guard. -/
def dim (f : F) : KP K := (popS f.loc).seq (dnm K f)

theorem HT.dnm (σ0 : HL → List Sym) (s : F → List Sym) (f : F) (n : ℕ) (b : List Sym)
    (hs : s f = natSyms n ++ Sym.mark :: b) :
    HT [] (henc σ0 s) (dnm K f) (henc σ0 (Function.update s f b)) (2 * bitLen n + 5) := by
  have h1 := HT.dropBitsF (lS K) σ0 s f (encodeNat n) (Sym.mark :: b) (TermOK.cons rfl _) hs
  have h2 := HT.popF (σ := KReg K) σ0 (Function.update s f (Sym.mark :: b)) f Sym.mark b
    (by simp)
  exact (HT.seq h1 h2).of_eq (by rw [Function.update_idem]) (by simp only [bitLen]; omega)

theorem HT.dim (σ0 : HL → List Sym) (s : F → List Sym) (f : F) (z : ℤ) (b : List Sym)
    (hs : s f = intSyms z ++ Sym.mark :: b) :
    HT [] (henc σ0 s) (dim K f) (henc σ0 (Function.update s f b)) (2 * bitLen z.natAbs + 6) := by
  have h0 := HT.popF (σ := KReg K) σ0 s f (sgnSym z) (natSyms z.natAbs ++ Sym.mark :: b)
    (by rw [hs]; rfl)
  have h1 := HT.dnm K σ0 (Function.update s f (natSyms z.natAbs ++ Sym.mark :: b)) f z.natAbs b
    (by simp)
  exact (HT.seq h0 h1).of_eq (by rw [Function.update_idem]) (by omega)

/-- The header phase. -/
def hdrPhase : KP K :=
  (copyField (lS K) 1 .PQ).seq ((copyField (lS K) 3 .RH).seq ((popS F.RH.loc).seq
    ((copyField (lS K) 4 .PK).seq (copyField (lS K) 7 .PH))))

theorem HT.hdrPhase (σ0 : HL → List Sym) (s : F → List Sym) (fs : List ℕ) (r0 : List Sym)
    (m : ℕ) (hfs : fs.length = 8) (hs : s .C0 = hdrSyms fs ++ r0) (htt : TermOK (s .TT))
    (hr : fs.getD 3 0 = 2 * m) (hm : 0 < m) :
    HT [] (henc σ0 s) (hdrPhase K)
      (henc σ0 (Function.update (Function.update (Function.update (Function.update s
        .PQ (natSyms (fs.getD 1 0) ++ s .PQ)) .RH (natSyms m ++ s .RH))
        .PK (natSyms (fs.getD 4 0) ++ s .PK)) .PH (natSyms (fs.getD 7 0) ++ s .PH)))
      (8 * mvCost fs + 7 * (bitLen (fs.getD 1 0) + bitLen (fs.getD 3 0) + bitLen (fs.getD 4 0) +
        bitLen (fs.getD 7 0)) + 37) := by
  have h1 := HT.copyField (lS K) σ0 1 .PQ (by decide) (by decide) (by decide) fs r0 s
    (by omega) hs htt
  set s1 := Function.update s .PQ (natSyms (fs.getD 1 0) ++ s .PQ) with hs1
  have h2 := HT.copyField (lS K) σ0 3 .RH (by decide) (by decide) (by decide) fs r0 s1
    (by omega) (by rw [hs1, Function.update_of_ne (by decide)]; exact hs)
    (by rw [hs1, Function.update_of_ne (by decide)]; exact htt)
  set s2 := Function.update s1 .RH (natSyms (fs.getD 3 0) ++ s1 .RH) with hs2
  have h3 := HT.popF (σ := KReg K) σ0 s2 .RH (Sym.bit false) (natSyms m ++ s .RH) (by
    rw [hs2, Function.update_self, hr, natSyms_double hm, hs1, Function.update_of_ne (by decide)]
    rfl)
  set s3 := Function.update s2 .RH (natSyms m ++ s .RH) with hs3
  have h4 := HT.copyField (lS K) σ0 4 .PK (by decide) (by decide) (by decide) fs r0 s3
    (by omega) (by simp [hs3, hs2, hs1, hs])
    (by simpa [hs3, hs2, hs1, Function.update_apply] using htt)
  set s4 := Function.update s3 .PK (natSyms (fs.getD 4 0) ++ s3 .PK) with hs4
  have h5 := HT.copyField (lS K) σ0 7 .PH (by decide) (by decide) (by decide) fs r0 s4
    (by omega) (by simp [hs4, hs3, hs2, hs1, hs])
    (by simpa [hs4, hs3, hs2, hs1, Function.update_apply] using htt)
  refine (HT.seq h1 (HT.seq h2 (HT.seq h3 (HT.seq h4 h5)))).of_eq ?_ (by omega)
  congr 1
  funext g
  cases g <;> simp [hs4, hs3, hs2, hs1]

end WP.W9f
