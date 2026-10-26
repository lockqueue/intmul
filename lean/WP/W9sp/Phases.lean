import WP.W9sp.Body

/-!
# WP.W9sp.Phases — the five phases of `W9_splitPack`

1. `floorsP`: a `mark` floor on each scratch stack `sB`, `sN`, `sT`, `sO`.
2. `hdrP`: `sB := b` (copy from `C0`); `C0`'s field `b` is parked on `sT` (`skipF`), so that
   `shlVar` turns `1` on `sN` into `2^K0` with counter `K0` read in place on `C0`; then `unskipF`.
3. `loopP`: `2^K0` iterations of `bodyP` (`cdLoop`, counter `sN`); loop state `Wl … i` after
   `2^K0 - i` entries.
4. `emitP`: push `symLevel`, `symNode` on `S`, then the blind transfer `sO → S` (`rewindTo`) down to
   the floor of `sO`, which restores entry order.
5. `cleanP`: drop `b`, pop the floors of `sB`, `sN`, `sT`.
-/

namespace WP.W9sp

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 Computability

variable (K : Kit)

/-! ## Programs -/

def floorsP : Prog H (fun _ => Sym) K.Reg :=
  (pushS sB Sym.mark).seq ((pushS sN Sym.mark).seq ((pushS sT Sym.mark).seq (pushS sO Sym.mark)))

def hdrP : Prog H (fun _ => Sym) K.Reg :=
  (K.pCopy hC0 sB).seq ((skipF K.lS hC0 sT).seq ((pushS sN (Sym.bit true)).seq
    ((K.pShlV sN hC0).seq (unskipF K.lS sT hC0))))

def loopP : Prog H (fun _ => Sym) K.Reg :=
  cdLoop K.isZ K.dec K.lIsZ K.lDec sN Kit.dflt (bodyP K)

def emitP : Prog H (fun _ => Sym) K.Reg :=
  (pushS hS symLevel).seq ((pushS hS symNode).seq ((rewindTo sO hS Sym.mark).liftRegs K.lS))

def cleanP : Prog H (fun _ => Sym) K.Reg :=
  (K.pDrop sB).seq ((popS sB).seq ((popS sN).seq (popS sT)))

theorem floorsP_closed : (floorsP K).Closed := ⟨trivial, trivial, trivial, trivial⟩

theorem hdrP_closed : (hdrP K).Closed :=
  ⟨K.pCopy_closed _ _, skipF_closed _ _ _, trivial, K.pShlV_closed _ _, unskipF_closed _ _ _⟩

theorem loopP_closed : (loopP K).Closed :=
  cdLoop_closed _ _ _ _ _ _ _ (bodyP_closed K)

theorem emitP_closed : (emitP K).Closed := ⟨trivial, trivial, rewindTo_closed _ _ _ _⟩

theorem cleanP_closed : (cleanP K).Closed := ⟨K.pDrop_closed _, trivial, trivial, trivial⟩

/-! ## Phase rules on the state normal form -/

theorem HT.floors (σ : H → List Sym) (w : W) :
    HT [] (w.toB σ) (floorsP K)
      ({ w with
          xb := Sym.mark :: w.xb, xn := Sym.mark :: w.xn,
          xt := Sym.mark :: w.xt, xo := Sym.mark :: w.xo }.toB σ) (1 + (1 + (1 + 1))) :=
  (HT.seq ((HT.pushS sB Sym.mark (w.toB σ) []).of_eq (by rw [toB_sB, upd_sB]) le_rfl)
    (HT.seq ((HT.pushS sN Sym.mark _ []).of_eq (by rw [toB_sN, upd_sN]) le_rfl)
    (HT.seq ((HT.pushS sT Sym.mark _ []).of_eq (by rw [toB_sT, upd_sT]) le_rfl)
      ((HT.pushS sO Sym.mark _ []).of_eq (by rw [toB_sO, upd_sO]) le_rfl)))).of_eq rfl le_rfl

/-- Cost of the header phase. -/
def chdr (C b K0 : ℕ) : ℕ :=
  C * (bitLen b + 1) + ((3 * bitLen b + 6) + (1 + (C * (K0 + bitLen K0 + 1) + (3 * bitLen b + 6))))

theorem HT.hdr {C : ℕ} (hK : K.Spec C) (σ : H → List Sym) (w : W) (b K0 : ℕ) (r : List Sym)
    (hc0 : w.c0 = natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark :: r))
    (hxn : TermOK w.xn) (hxt : TermOK w.xt) :
    HT [] (w.toB σ) (hdrP K)
      ({ w with
          c0 := natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark :: r),
          xb := natSyms b ++ w.xb,
          xn := natSyms (1 * 2 ^ K0) ++ w.xn }.toB σ) (chdr C b K0) := by
  have s1 := (HT.copyNat hK.copy Kit.dflt K.lCopy hC0 sB (by decide) (by decide) (w.toB σ) b
    (Sym.mark :: (natSyms K0 ++ Sym.mark :: r)) (TermOK.cons rfl _) (by simp [hc0]) []).of_eq
    (by rw [toB_sB, upd_sB]) le_rfl
  have s2 := (HT.skipF K.lS (show hC0 ≠ sT by decide) ({ w with xb := natSyms b ++ w.xb }.toB σ)
    b (natSyms K0 ++ Sym.mark :: r) (by simp [hc0])).of_eq
    (by rw [toB_sT, upd_C0, upd_sT]) le_rfl
  have s3 := (HT.pushS (σ := K.Reg) sN (Sym.bit true) ({ w with
      xb := natSyms b ++ w.xb,
      c0 := natSyms K0 ++ Sym.mark :: r,
      xt := Sym.mark :: ((encodeNat b).reverse.map Sym.bit ++ w.xt) }.toB σ) []).of_eq
    (by rw [toB_sN, upd_sN]) le_rfl
  have s4 := (HT.shlVar hK.shlV Kit.dflt K.lShlV sN hC0 (by decide) (by decide) ({ w with
      xb := natSyms b ++ w.xb,
      c0 := natSyms K0 ++ Sym.mark :: r,
      xt := Sym.mark :: ((encodeNat b).reverse.map Sym.bit ++ w.xt),
      xn := Sym.bit true :: w.xn }.toB σ) 1 K0 w.xn (Sym.mark :: r) hxn (TermOK.cons rfl _)
    (by simp [natSyms_one_sp]) (by simp) []).of_eq (by rw [upd_sN]) le_rfl
  have s5 := (HT.unskipF K.lS (show hC0 ≠ sT by decide) ({ w with
      xb := natSyms b ++ w.xb,
      c0 := natSyms K0 ++ Sym.mark :: r,
      xt := Sym.mark :: ((encodeNat b).reverse.map Sym.bit ++ w.xt),
      xn := natSyms (1 * 2 ^ K0) ++ w.xn }.toB σ) b w.xt hxt (by simp)).of_eq
    (by rw [toB_C0, upd_sT, upd_C0]) le_rfl
  exact (HT.seq s1 (HT.seq s2 (HT.seq s3 (HT.seq s4 s5)))).of_eq rfl le_rfl

/-- Loop state with counter `i`: entries `0, …, N - i - 1` are on `sO` (reversed). -/
def Wl (σ : H → List Sym) (b N A B : ℕ) (rA rB : List Sym) (i : ℕ) : W :=
  ⟨σ hS, σ hC0, natSyms (A / 2 ^ (b * (N - i))) ++ rA, natSyms (B / 2 ^ (b * (N - i))) ++ rB,
    natSyms b ++ Sym.mark :: σ sB, natSyms i ++ Sym.mark :: σ sN, Sym.mark :: σ sT,
    (packSyms b A B (N - i)).reverse ++ Sym.mark :: σ sO⟩

theorem HT.mainLoop {C : ℕ} (hK : K.Spec C) (σ : H → List Sym) (b N A B : ℕ) (rA rB : List Sym)
    (hrA : TermOK rA) (hrB : TermOK rB) :
    HT [] ((Wl σ b N A B rA rB N).toB σ) (loopP K) ((Wl σ b N A B rA rB 0).toB σ)
      (C + loopCost (fun i => C * (zerosLead (encodeNat (i + 1)) + 1) + cbody C b + C) N) := by
  refine HT.cdLoop hK.isZ hK.dec K.lIsZ K.lDec sN Kit.dflt (by decide) (Sym.mark :: σ sN)
    (TermOK.cons rfl _) N (fun i => (Wl σ b N A B rA rB i).toB σ) (fun i _ => by simp [Wl])
    (bodyP K) (fun _ => cbody C b) ?_
  intro i hi
  show HT [] (Function.update ((Wl σ b N A B rA rB (i + 1)).toB σ) sN
    (natSyms i ++ Sym.mark :: σ sN)) (bodyP K) ((Wl σ b N A B rA rB i).toB σ) (cbody C b)
  rw [upd_sN]
  have hj : N - i = N - (i + 1) + 1 := by omega
  have e1 := div_step A b (N - (i + 1))
  have e2 := div_step B b (N - (i + 1))
  have e3 := rev_entry b A B (N - (i + 1))
    ((packSyms b A B (N - (i + 1))).reverse ++ Sym.mark :: σ sO)
  have e4 := rev_packSyms_succ b A B (N - (i + 1)) (Sym.mark :: σ sO)
  unfold chunk at e3
  rw [← hj] at e1 e2 e4
  refine (HT.body K hK σ _ b (A / 2 ^ (b * (N - (i + 1)))) (B / 2 ^ (b * (N - (i + 1)))) rA rB
    (Sym.mark :: σ sB) hrA hrB (TermOK.cons rfl _) (TermOK.cons rfl _) rfl rfl rfl).of_eq
    (congrArg (W.toB σ) ?_) le_rfl
  simp only [Wl, e1, e2, e3, e4]

theorem HT.emit (σ : H → List Sym) (w : W) (L rest : List Sym) (hL : Sym.mark ∉ L)
    (hxo : w.xo = L ++ Sym.mark :: rest) :
    HT [] (w.toB σ) (emitP K)
      ({ w with
          s := L.reverse ++ symNode :: symLevel :: w.s,
          xo := rest }.toB σ) (1 + (1 + (3 * L.length + 2))) :=
  (HT.seq ((HT.pushS hS symLevel (w.toB σ) []).of_eq (by rw [toB_S, upd_S]) le_rfl)
    (HT.seq ((HT.pushS hS symNode _ []).of_eq (by rw [toB_S, upd_S]) le_rfl)
      ((HT.rewind K.lS (show sO ≠ hS by decide) Sym.mark _ L rest hL (by simp [hxo])).of_eq
        (by rw [toB_S, upd_sO, upd_S]) le_rfl))).of_eq rfl le_rfl

theorem HT.cleanup {C : ℕ} (hK : K.Spec C) (σ : H → List Sym) (w : W) (b : ℕ)
    (xb' xn' xt' : List Sym) (hxb : w.xb = natSyms b ++ Sym.mark :: xb')
    (hxn : w.xn = Sym.mark :: xn') (hxt : w.xt = Sym.mark :: xt') :
    HT [] (w.toB σ) (cleanP K) ({ w with xb := xb', xn := xn', xt := xt' }.toB σ)
      (C * (bitLen b + 1) + (1 + (1 + 1))) :=
  (HT.seq ((HT.dropNat hK.drop Kit.dflt K.lDrop sB (by decide) (w.toB σ) b (Sym.mark :: xb')
      (TermOK.cons rfl _) (by simp [hxb]) []).of_eq (by rw [upd_sB]) le_rfl)
    (HT.seq ((HT.popS sB _ Sym.mark xb' (by simp) []).of_eq (by rw [upd_sB]) le_rfl)
    (HT.seq ((HT.popS sN _ Sym.mark xn' (by simp [hxn]) []).of_eq (by rw [upd_sN]) le_rfl)
      ((HT.popS sT _ Sym.mark xt' (by simp [hxt]) []).of_eq (by rw [upd_sT]) le_rfl)))).of_eq
    rfl le_rfl

#assert_std_axioms floorsP_closed hdrP_closed loopP_closed emitP_closed cleanP_closed
  HT.floors HT.hdr HT.mainLoop HT.emit HT.cleanup

end WP.W9sp
