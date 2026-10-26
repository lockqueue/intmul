import WP.W7k3c.Steps

/-!
# WP.W7k3c.Steps2 — series call, signed drop, output, and the two comparisons
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

section Rules

variable {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C)
  {S : HL → List Sym} {V : Fin 16 → Option Val} {dv : List Sym}

include hI

theorem sSer {a b c d z : Fin 16} {a0 cc : ℤ} {dd n W' : ℕ}
    (hnd : [(.inr a : HL), .inr b, .inr c, .inr d, .inr z].Nodup)
    (ha : V a = some (.int a0)) (hb : V b = some (.int cc)) (hc : V c = some (.nat dd))
    (hd : V d = some (.nat n)) (hz : V z = none) (hdd : 0 < dd) (hn : 0 < n)
    (hws : IntMul.RecurrenceCallSitesWidthSound W' a0 cc dd WP.W7k3.SK.erf.f WP.W7k3.SK.erf.g n)
    (hnW : n ≤ W) (hW' : W' ≤ W) :
    HT [] (St S V dv) (pSer I a b c d z)
      (St S (Function.update V z (some (.int
        (serState a0 cc dd WP.W7k3.SK.erf.f WP.W7k3.SK.erf.g n).2))) dv) (U C W) :=
  (HT.callI_upd I.se [.inr a, .inr b, .inr c, .inr d, .inr z] (.inl 0) hnd rfl (by norm_num) I.lse
    (St S V dv) (.inl 4) _ (hI.se W' a0 cc dd n _ _ _ _ _ hdd hn hws (termOK_mark _) (termOK_mark _)
      (termOK_mark _) (termOK_mark _) (St_int S V dv ha) (St_int S V dv hb) (St_nat S V dv hc)
      (St_nat S V dv hd)) []).of_eq
    (St_push S V dv hz (.int (serState a0 cc dd WP.W7k3.SK.erf.f WP.W7k3.SK.erf.g n).2))
    (U_ser hI.one hnW hW')

theorem sDrI {x : Fin 16} {z : ℤ} (hx : V x = some (.int z)) (hz : bitLen z.natAbs ≤ W) :
    HT [] (St S V dv) (pDrI I x) (St S (Function.update V x none) dv) (U C W) := by
  have h1 := (HT.popS (σ := I.R) (.inr x) (St S V dv) (sgnSym z)
    (natSyms z.natAbs ++ Sym.mark :: S (.inr x)) (by rw [St_int S V dv hx]; rfl) []).of_eq
    (St_put S V dv x (.nat z.natAbs)) le_rfl
  have h2 := (HT.dropNat hI.dr (.inl 0) I.ldr (.inr x) (by norm_num)
    (St S (Function.update V x (some (.nat z.natAbs))) dv) z.natAbs _ (termOK_mark _)
    (St_nat S _ dv (by simp)) []).of_eq
    ((St_clear S _ dv x).trans (by rw [Function.update_idem])) le_rfl
  refine (HT.seq h1 h2).mono ?_
  have := U_lin (W := W) hI.one (x := bitLen z.natAbs + 2) (by omega)
  have h3 : C * (bitLen z.natAbs + 1) + C ≤ C * (bitLen z.natAbs + 2) := by ring_nf; omega
  have h4 := hI.one
  omega

theorem sOut {x z0 : Fin 16} {a : ℤ} (h : x ≠ z0) (hx : V x = some (.int a))
    (h0 : V z0 = some (.int 0)) (ha : bitLen a.natAbs ≤ W) :
    HT [] (St S V dv) (pOut I x z0) (St S V (intSyms a ++ dv)) (U C W) := by
  refine (HT.addInt hI.ai (.inl 0) I.lai (.inr x) (.inr z0) (.inl 4) (by simp [h]) (by norm_num)
    (St S V dv) a 0 _ _ (termOK_mark _) (termOK_mark _) (St_int S V dv hx) (St_int S V dv h0)
    []).of_eq ?_ (U_lin hI.one (by simp [WP.W7k2.bitLen_zero]; omega))
  rw [add_zero, St_dst, St_setd]

theorem sCmpN {x y : HL} {u v : ℕ} {ru rv : List Sym} (hnd : [x, y].Nodup)
    (hx : St S V dv x = natSyms u ++ ru) (hru : TermOK ru) (hy : St S V dv y = natSyms v ++ rv)
    (hrv : TermOK rv) (hu : bitLen u ≤ W) (hv : bitLen v ≤ W) (f : Ordering → Bool)
    (p q : CP I) {B' : HL → List Sym} {T₁ T₂ : ℕ}
    (hp : f (Lib.ordOf u v) = true → HT [] (St S V dv) p B' T₁)
    (hq : f (Lib.ordOf u v) = false → HT [] (St S V dv) q B' T₂) :
    HT [] (St S V dv) (pCmpN I x y f p q) B' (U C W + (max T₁ T₂ + 1)) :=
  (HT.cmpNat_ite hI.cm (.inl 0) I.lcm x y hnd (by norm_num) (St S V dv) B' u v ru rv hru hrv hx hy
    f p q [] hp hq).mono (Nat.add_le_add_right (U_lin hI.one (by omega)) _)

theorem sCmpI {x y : Fin 16} {a b : ℤ} (h : x ≠ y) (hx : V x = some (.int a))
    (hy : V y = some (.int b)) (ha : bitLen a.natAbs ≤ W) (hb : bitLen b.natAbs ≤ W)
    (f : Ordering → Bool) (p q : CP I) {B' : HL → List Sym} {T₁ T₂ : ℕ}
    (hp : f (cmpZ a b) = true → HT [] (St S V dv) p B' T₁)
    (hq : f (cmpZ a b) = false → HT [] (St S V dv) q B' T₂) :
    HT [] (St S V dv) (pCmpI I x y f p q) B' (U C W + (max T₁ T₂ + 1)) :=
  (HT.callI_test I.ci [.inr x, .inr y] (.inl 0) (nd2 h) rfl (by norm_num) I.lci (St S V dv) B' f
    (cmpZ a b) (hI.ci a b _ _ _ (termOK_mark _) (termOK_mark _) (St_int S V dv hx)
      (St_int S V dv hy)) p q [] hp hq).mono (Nat.add_le_add_right (U_lin hI.one (by omega)) _)

#assert_std_axioms sSer sDrI sOut sCmpN sCmpI

end Rules

end WP.W7k3c
