/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.TwiddleSel
import SubNLogN.Machine.Calculus.Hdr
import SubNLogN.Machine.Contracts.FFT

/-!
# K4-TWIDDLE part (E1): the multiplication parameters from the header
(`Machine/FFT/TwiddleHdr.lean`)

**Scope (honest summary).** A generic machine routine `hdrPhase` (any stack type, registers through
a lens) for the twiddle pass `TwiddlePassStmt`: from the header `midHdr q ℓ K w a`
(`Machine/Contracts/FFT.lean`) it pushes `natSyms q` on `QS` and `natSyms w` on `W1`, `W2`, `W3`;
the header is restored. The four fields `q, D, ℓ, K` in front of `w` are parked on `PK` and moved
back, so every skipped header field is paid: the cost is at most `27·|midHdr|`. Proved, no `sorry`.
-/

namespace SubNLogN.Machine.FFT.TwiddleAux

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Machine SubNLogN.Machine.FFT.DIF

section Hdr

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- `copyBits` on a number field. -/
theorem runs_copyNat {src dst tmp : K} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (S : K → List Sym) (n : ℕ) (R : List Sym) (hS : S src = natSyms n ++ R)
    (hR : TermOK R) (ht : TermOK (S tmp)) :
    Runs (copyBits lO src dst tmp) S (Function.update S dst (natSyms n ++ S dst))
      (fun _ => True) (9 * bitLen n + 4) :=
  runs_copyBits lO h1 h2 h3 S (Computability.encodeNat n) R hS hR ht

theorem midHdr_split {D : ℕ} (q ℓ Kp w : ℕ) (a : Fin D → ℕ) (hrest : List Sym) :
    midHdr q ℓ Kp w a ++ hrest =
      W9.hdrSyms [q, D, ℓ, Kp] ++
        (natSyms w ++ Sym.mark :: (W9.hdrSyms (List.ofFn a) ++ hrest)) := by
  simp [midHdr, W9.hdrSyms]

theorem length_midHdr_ge {D : ℕ} (q ℓ Kp w : ℕ) (a : Fin D → ℕ) :
    bitLen q + bitLen D + bitLen ℓ + bitLen Kp + bitLen w + 5 ≤ (midHdr q ℓ Kp w a).length := by
  rw [midHdr, Calculus.HdrAux.length_hdrSyms]
  simp only [List.cons_append, List.map_cons, List.sum_cons]
  omega

/-- The final stacks of `hdrPhase`. -/
theorem hdrPhase_final {HDR PK QS W1 W2 W3 : K} (dHP : HDR ≠ PK) (dHQ : HDR ≠ QS)
    (dH1 : HDR ≠ W1) (dH2 : HDR ≠ W2) (dH3 : HDR ≠ W3) (dPQ : PK ≠ QS) (dP1 : PK ≠ W1)
    (dP2 : PK ≠ W2) (dP3 : PK ≠ W3) (dQ1 : QS ≠ W1) (dQ2 : QS ≠ W2) (dQ3 : QS ≠ W3)
    (d12 : W1 ≠ W2) (d13 : W1 ≠ W3) (d23 : W2 ≠ W3)
    (S : K → List Sym) (q w : ℕ) (Y X MF : List Sym) (hH : S HDR = Y ++ X) (hPK : S PK = []) :
    let S1 := Function.update S QS (natSyms q ++ S QS)
    let S2 := Function.update (Function.update S1 HDR X) PK (MF ++ S1 PK)
    let S3 := Function.update S2 W1 (natSyms w ++ S2 W1)
    let S4 := Function.update S3 W2 (natSyms w ++ S3 W2)
    let S5 := Function.update S4 W3 (natSyms w ++ S4 W3)
    Function.update (Function.update S5 PK []) HDR (Y ++ S5 HDR) =
      Function.update (Function.update (Function.update (Function.update S QS
        (natSyms q ++ S QS)) W1 (natSyms w ++ S W1)) W2 (natSyms w ++ S W2)) W3
        (natSyms w ++ S W3) := by
  intro S1 S2 S3 S4 S5
  funext j
  simp only [S5, S4, S3, S2, S1, Function.update_apply, dHP, dHQ, dH1, dH2, dH3, dPQ, dH1.symm,
    dH2.symm, dH3.symm, dP1.symm, dP2.symm, dP3.symm, dQ1.symm, dQ2.symm, dQ3.symm, d12.symm,
    d13.symm, d23.symm, if_false, if_true]
  split_ifs <;> simp_all

/-- Read `q` and three copies of `w` from the header (which is restored). -/
def hdrPhase (HDR PK TC QS W1 W2 W3 : K) : Prog K (fun _ => Sym) σ :=
  .seq (copyBits lO HDR QS TC)
  (.seq ((forEachRange 4 (fun _ => Calculus.moveFieldTo HDR PK)).liftRegs lO)
  (.seq (copyBits lO HDR W1 TC)
  (.seq (copyBits lO HDR W2 TC)
  (.seq (copyBits lO HDR W3 TC)
    ((forEachRange 4 (fun _ => Calculus.moveFieldBack PK HDR)).liftRegs lO)))))

omit [DecidableEq K] in
theorem closed_hdrPhase (HDR PK TC QS W1 W2 W3 : K) :
    (hdrPhase lO HDR PK TC QS W1 W2 W3).Closed :=
  ⟨closed_copyBits lO HDR QS TC,
    closed_liftRegs lO (closed_forEachRange 4 _ (fun _ _ => Calculus.closed_moveFieldTo HDR PK)),
    closed_copyBits lO HDR W1 TC, closed_copyBits lO HDR W2 TC, closed_copyBits lO HDR W3 TC,
    closed_liftRegs lO
      (closed_forEachRange 4 _ (fun _ _ => Calculus.closed_moveFieldBack PK HDR))⟩

theorem runs_hdrPhase {HDR PK TC QS W1 W2 W3 : K} (hd : [HDR, PK, TC, QS, W1, W2, W3].Nodup)
    (S : K → List Sym) {D : ℕ} (q ℓ Kp w : ℕ) (a : Fin D → ℕ) (hrest : List Sym)
    (hH : S HDR = midHdr q ℓ Kp w a ++ hrest) (hPK : S PK = []) (hTC : S TC = []) :
    Runs (hdrPhase lO HDR PK TC QS W1 W2 W3) S
      (Function.update (Function.update (Function.update (Function.update S QS
        (natSyms q ++ S QS)) W1 (natSyms w ++ S W1)) W2 (natSyms w ++ S W2)) W3
        (natSyms w ++ S W3))
      (fun _ => True) (27 * (midHdr q ℓ Kp w a).length) := by
  have p0 := List.pairwise_cons.1 hd
  have dHP : HDR ≠ PK := p0.1 PK (by simp)
  have dHC : HDR ≠ TC := p0.1 TC (by simp)
  have dHQ : HDR ≠ QS := p0.1 QS (by simp)
  have dH1 : HDR ≠ W1 := p0.1 W1 (by simp)
  have dH2 : HDR ≠ W2 := p0.1 W2 (by simp)
  have dH3 : HDR ≠ W3 := p0.1 W3 (by simp)
  have p1 := List.pairwise_cons.1 p0.2
  have dPC : PK ≠ TC := p1.1 TC (by simp)
  have dPQ : PK ≠ QS := p1.1 QS (by simp)
  have dP1 : PK ≠ W1 := p1.1 W1 (by simp)
  have dP2 : PK ≠ W2 := p1.1 W2 (by simp)
  have dP3 : PK ≠ W3 := p1.1 W3 (by simp)
  have p2 := List.pairwise_cons.1 p1.2
  have dCQ : TC ≠ QS := p2.1 QS (by simp)
  have dC1 : TC ≠ W1 := p2.1 W1 (by simp)
  have dC2 : TC ≠ W2 := p2.1 W2 (by simp)
  have dC3 : TC ≠ W3 := p2.1 W3 (by simp)
  have p3 := List.pairwise_cons.1 p2.2
  have dQ1 : QS ≠ W1 := p3.1 W1 (by simp)
  have dQ2 : QS ≠ W2 := p3.1 W2 (by simp)
  have dQ3 : QS ≠ W3 := p3.1 W3 (by simp)
  have p4 := List.pairwise_cons.1 p3.2
  have d12 : W1 ≠ W2 := p4.1 W2 (by simp)
  have d13 : W1 ≠ W3 := p4.1 W3 (by simp)
  have d23 : W2 ≠ W3 := (List.pairwise_cons.1 p4.2).1 W3 (by simp)
  have hlen := length_midHdr_ge q ℓ Kp w a
  set X := natSyms w ++ Sym.mark :: (W9.hdrSyms (List.ofFn a) ++ hrest) with hX
  have hH' : S HDR = W9.hdrSyms [q, D, ℓ, Kp] ++ X := by rw [hH, midHdr_split]
  -- 1. `q`
  have e1 := runs_copyNat lO dHQ dHC dCQ.symm S q _
    (by rw [hH', Calculus.HdrAux.hdrSyms_cons, List.append_assoc, List.cons_append])
    (TermOK.cons rfl _) (by rw [hTC]; exact termOK_nil')
  set S1 := Function.update S QS (natSyms q ++ S QS) with hS1
  -- 2. park `q, D, ℓ, K`
  have e2 := runs_liftS lO (Calculus.runs_moveFieldsTo dHP [q, D, ℓ, Kp] X S1
    (by rw [hS1, Function.update_of_ne dHQ, hH']))
  set S2 := Function.update (Function.update S1 HDR X) PK
    (Calculus.movedFields [q, D, ℓ, Kp] ++ S1 PK) with hS2
  have hS2H : S2 HDR = X := by rw [hS2, Function.update_of_ne dHP, Function.update_self]
  have hS2C : S2 TC = [] := by
    rw [hS2, Function.update_of_ne dPC.symm, Function.update_of_ne dHC.symm, hS1,
      Function.update_of_ne dCQ, hTC]
  -- 3. three copies of `w`
  have e3 := runs_copyNat lO dH1 dHC dC1.symm S2 w _ (by rw [hS2H]) (TermOK.cons rfl _)
    (by rw [hS2C]; exact termOK_nil')
  set S3 := Function.update S2 W1 (natSyms w ++ S2 W1) with hS3
  have e4 := runs_copyNat lO dH2 dHC dC2.symm S3 w _
    (by rw [hS3, Function.update_of_ne dH1, hS2H]) (TermOK.cons rfl _)
    (by rw [hS3, Function.update_of_ne dC1, hS2C]; exact termOK_nil')
  set S4 := Function.update S3 W2 (natSyms w ++ S3 W2) with hS4
  have e5 := runs_copyNat lO dH3 dHC dC3.symm S4 w _
    (by rw [hS4, Function.update_of_ne dH2, hS3, Function.update_of_ne dH1, hS2H])
    (TermOK.cons rfl _)
    (by rw [hS4, Function.update_of_ne dC2, hS3, Function.update_of_ne dC1, hS2C]
        exact termOK_nil')
  set S5 := Function.update S4 W3 (natSyms w ++ S4 W3) with hS5
  -- 4. move the parked fields back
  have e6 := runs_liftS lO (Calculus.runs_moveFieldsBack dHP.symm [Kp, ℓ, D, q] [] S5
    termOK_nil' (by
      rw [hS5, Function.update_of_ne dP3, hS4, Function.update_of_ne dP2, hS3,
        Function.update_of_ne dP1, hS2, Function.update_self, hS1, Function.update_of_ne dPQ, hPK]
      rfl))
  refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 (runs_seq' e3 (runs_seq' e4
    (runs_seq' e5 e6))))) (fun _ _ => trivial) ?_) ?_
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · exact hdrPhase_final dHP dHQ dH1 dH2 dH3 dPQ dP1 dP2 dP3 dQ1 dQ2 dQ3 d12 d13 d23 S q w
      (W9.hdrSyms [Kp, ℓ, D, q].reverse) X (Calculus.movedFields [q, D, ℓ, Kp])
      (by rw [hH']; rfl) hPK

end Hdr

end SubNLogN.Machine.FFT.TwiddleAux
