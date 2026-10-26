import WP.W7k3c.Macro

/-!
# WP.W7k3c.Steps — the kernel's machine steps on the abstract state

Programs (`p*`) and their rules (`s*`): each takes `St S V dv` to `St S V' dv` with cost `U C W`.
-/

namespace WP.W7k3c

open TMFw TMFw.Contracts WP.W7k2

section Progs

variable (I : CI)

def pPush (j : Fin 16) (c : ℕ) : CP I := pushNat (.inr j) c
def pToInt (j : Fin 16) : CP I := pushS (.inr j) .pos
def pToNat (j : Fin 16) : CP I := popS (.inr j)
def pCp (x : HL) (j : Fin 16) : CP I := callI I.cp [x, .inr j] (.inl 0) I.lcp
def pAdN (x y z : Fin 16) : CP I := callI I.ad [.inr x, .inr y, .inr z] (.inl 0) I.lad
def pSbN (x y z : Fin 16) : CP I := callI I.sb [.inr x, .inr y, .inr z] (.inl 0) I.lsb
def pShl (x c : Fin 16) : CP I := callI I.sv [.inr x, .inr c] (.inl 0) I.lsv
def pMul (x y z : Fin 16) : CP I := callI I.mu [.inr x, .inr y, .inr z] (.inl 0) I.lmu
def pNeg (x : Fin 16) : CP I := callI I.ng [.inr x] (.inl 0) I.lng
def pAdI (x y z : Fin 16) : CP I := callI I.ai [.inr x, .inr y, .inr z] (.inl 0) I.lai
def pSbI (x y z : Fin 16) : CP I := callI I.si [.inr x, .inr y, .inr z] (.inl 0) I.lsi
def pDiv (x y z : Fin 16) : CP I := callI I.dv [.inr x, .inr y, .inr z] (.inl 0) I.ldv
def pIsq (x z : Fin 16) : CP I := callI I.sq [.inr x, .inr z] (.inl 0) I.lsq
def pPi (x z : Fin 16) : CP I := callI I.pi [.inr x, .inr z] (.inl 0) I.lpi
def pLn (x z : Fin 16) : CP I := callI I.ln [.inr x, .inr z] (.inl 0) I.lln
def pSer (a b c d z : Fin 16) : CP I :=
  callI I.se [.inr a, .inr b, .inr c, .inr d, .inr z] (.inl 0) I.lse
def pDrN (x : Fin 16) : CP I := callI I.dr [.inr x] (.inl 0) I.ldr
def pDrI (x : Fin 16) : CP I := (popS (.inr x)).seq (pDrN I x)
def pOut (x z0 : Fin 16) : CP I := callI I.ai [.inr x, .inr z0, .inl 4] (.inl 0) I.lai
def pCmpN (x y : HL) (f : Ordering → Bool) (p q : CP I) : CP I :=
  (callI I.cm [x, y] (.inl 0) I.lcm).seq (.ite (fun s => f (I.cm.obs (I.lcm.get s))) p q)
def pCmpI (x y : Fin 16) (f : Ordering → Bool) (p q : CP I) : CP I :=
  (callI I.ci [.inr x, .inr y] (.inl 0) I.lci).seq (.ite (fun s => f (I.ci.obs (I.lci.get s))) p q)

end Progs

/-! ## State bookkeeping -/

section Book

variable (S : HL → List Sym) (V : Fin 16 → Option Val) (dv : List Sym)

theorem St_push {j : Fin 16} (hj : V j = none) (v : Val) :
    Function.update (St S V dv) (.inr j) (v.enc ++ St S V dv (.inr j)) =
      St S (Function.update V j (some v)) dv := by
  rw [St_scr, hj]
  exact St_set S V dv j (some v)

theorem St_put (j : Fin 16) (v : Val) :
    Function.update (St S V dv) (.inr j) (v.enc ++ Sym.mark :: S (.inr j)) =
      St S (Function.update V j (some v)) dv :=
  St_set S V dv j (some v)

theorem St_clear (j : Fin 16) :
    Function.update (St S V dv) (.inr j) (Sym.mark :: S (.inr j)) =
      St S (Function.update V j none) dv :=
  St_set S V dv j none

theorem St_nat {j : Fin 16} {a : ℕ} (h : V j = some (.nat a)) :
    St S V dv (.inr j) = natSyms a ++ Sym.mark :: S (.inr j) := by
  rw [St_scr, h]
  rfl

theorem St_int {j : Fin 16} {z : ℤ} (h : V j = some (.int z)) :
    St S V dv (.inr j) = intSyms z ++ Sym.mark :: S (.inr j) := by
  rw [St_scr, h]
  rfl

end Book

theorem nd2 {x y : Fin 16} (h : x ≠ y) : [(.inr x : HL), .inr y].Nodup := by simp [h]
theorem nd3 {x y z : Fin 16} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) :
    [(.inr x : HL), .inr y, .inr z].Nodup := by simp [h1, h2, h3]

/-! ## Rules -/

section Rules

variable {I : CI} {Mul : ℕ → ℕ} {C W : ℕ} (hI : I.Spec Mul C)
  {S : HL → List Sym} {V : Fin 16 → Option Val} {dv : List Sym}

include hI

theorem sPush (j : Fin 16) (c : ℕ) (hj : V j = none) (hc : bitLen c ≤ W) :
    HT [] (St S V dv) (pPush I j c) (St S (Function.update V j (some (.nat c))) dv) (U C W) :=
  (HT.pushNat (.inr j) c (St S V dv) []).of_eq (St_push S V dv hj (.nat c))
    (le_trans (Nat.le_mul_of_pos_left _ hI.one) (U_lin (W := W) hI.one (x := bitLen c + 1) (by omega)))

theorem sToInt {j : Fin 16} {a : ℕ} (hj : V j = some (.nat a)) :
    HT [] (St S V dv) (pToInt I j) (St S (Function.update V j (some (.int a))) dv) (U C W) := by
  refine (HT.pushS (.inr j) .pos (St S V dv) []).of_eq ?_ (one_le_U hI.one)
  rw [St_nat S V dv hj, ← St_put S V dv j (.int a)]
  simp [Val.enc, intSyms_natCast]

theorem sToNat {j : Fin 16} {z : ℤ} (hj : V j = some (.int z)) (hz : 0 ≤ z) :
    HT [] (St S V dv) (pToNat I j) (St S (Function.update V j (some (.nat z.toNat))) dv) (U C W) := by
  refine (HT.popS (.inr j) (St S V dv) .pos (natSyms z.toNat ++ Sym.mark :: S (.inr j)) ?_ []).of_eq
    (St_put S V dv j (.nat z.toNat)) (one_le_U hI.one)
  rw [St_int S V dv hj, intSyms_pos hz]
  rfl

theorem sCp (x : HL) (j : Fin 16) {a : ℕ} {rx : List Sym} (hnd : [x, .inr j].Nodup)
    (hx : St S V dv x = natSyms a ++ rx) (hrx : TermOK rx) (hj : V j = none) (ha : bitLen a ≤ W) :
    HT [] (St S V dv) (pCp I x j) (St S (Function.update V j (some (.nat a))) dv) (U C W) :=
  (HT.copyNat hI.cp (.inl 0) I.lcp x (.inr j) hnd (by norm_num) (St S V dv) a rx hrx hx []).of_eq
    (St_push S V dv hj (.nat a)) (U_lin hI.one (by omega))

theorem sAdN {x y z : Fin 16} {a b : ℕ} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z)
    (hx : V x = some (.nat a)) (hy : V y = some (.nat b)) (hz : V z = none)
    (ha : bitLen a ≤ W) (hb : bitLen b ≤ W) :
    HT [] (St S V dv) (pAdN I x y z) (St S (Function.update V z (some (.nat (a + b)))) dv) (U C W) :=
  (HT.addNat hI.ad (.inl 0) I.lad (.inr x) (.inr y) (.inr z) (nd3 h1 h2 h3) (by norm_num) (St S V dv)
    a b _ _ (termOK_mark _) (termOK_mark _) (St_nat S V dv hx) (St_nat S V dv hy) []).of_eq
    (St_push S V dv hz (.nat (a + b))) (U_lin hI.one (by omega))

theorem sSbN {x y z : Fin 16} {a b : ℕ} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z)
    (hx : V x = some (.nat a)) (hy : V y = some (.nat b)) (hz : V z = none) (hba : b ≤ a)
    (ha : bitLen a ≤ W) (hb : bitLen b ≤ W) :
    HT [] (St S V dv) (pSbN I x y z) (St S (Function.update V z (some (.nat (a - b)))) dv) (U C W) :=
  (HT.callI_upd I.sb [.inr x, .inr y, .inr z] (.inl 0) (nd3 h1 h2 h3) rfl (by norm_num) I.lsb
    (St S V dv) (.inl 2) _ (hI.sb a b _ _ _ (termOK_mark _) (termOK_mark _) hba (St_nat S V dv hx)
      (St_nat S V dv hy)) []).of_eq (St_push S V dv hz (.nat (a - b))) (U_lin hI.one (by omega))

theorem sShl {x c : Fin 16} {a k : ℕ} (h1 : x ≠ c) (hx : V x = some (.nat a))
    (hc : V c = some (.nat k)) (hk : k ≤ W) :
    HT [] (St S V dv) (pShl I x c) (St S (Function.update V x (some (.nat (a * 2 ^ k)))) dv)
      (U C W) :=
  (HT.shlVar hI.sv (.inl 0) I.lsv (.inr x) (.inr c) (nd2 h1) (by norm_num) (St S V dv) a k _ _
    (termOK_mark _) (termOK_mark _) (St_nat S V dv hx) (St_nat S V dv hc) []).of_eq
    (St_put S V dv x (.nat (a * 2 ^ k)))
    (U_lin hI.one (by have := bitLen_le_self k; omega))

theorem sMul {x y z : Fin 16} {a b : ℤ} (w : ℕ) (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z)
    (hx : V x = some (.int a)) (hy : V y = some (.int b)) (hz : V z = none)
    (ha : bitLen a.natAbs ≤ w) (hb : bitLen b.natAbs ≤ w) (hw : w ≤ W) :
    HT [] (St S V dv) (pMul I x y z) (St S (Function.update V z (some (.int (a * b)))) dv) (U C W) :=
  (HT.mul hI.mu (.inl 0) I.lmu (.inr x) (.inr y) (.inr z) (nd3 h1 h2 h3) (by norm_num) (St S V dv)
    w a b _ _ ha hb (termOK_mark _) (termOK_mark _) (St_int S V dv hx) (St_int S V dv hy) []).of_eq
    (St_push S V dv hz (.int (a * b))) (U_mul hI.one hI.mulB hw)

theorem sNeg {x : Fin 16} {z : ℤ} (hx : V x = some (.int z)) :
    HT [] (St S V dv) (pNeg I x) (St S (Function.update V x (some (.int (-z)))) dv) (U C W) :=
  (HT.callI_upd I.ng [.inr x] (.inl 0) (List.nodup_singleton _) rfl (by norm_num) I.lng
    (St S V dv) (.inl 0) _ (hI.ng z _ _ (termOK_mark _) (St_int S V dv hx)) []).of_eq
    (St_put S V dv x (.int (-z))) (le_trans (Nat.le_mul_of_pos_right _ (by norm_num))
      (U_lin (x := 1) hI.one (by omega)))

theorem sAdI {x y z : Fin 16} {a b : ℤ} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z)
    (hx : V x = some (.int a)) (hy : V y = some (.int b)) (hz : V z = none)
    (ha : bitLen a.natAbs ≤ W) (hb : bitLen b.natAbs ≤ W) :
    HT [] (St S V dv) (pAdI I x y z) (St S (Function.update V z (some (.int (a + b)))) dv) (U C W) :=
  (HT.addInt hI.ai (.inl 0) I.lai (.inr x) (.inr y) (.inr z) (nd3 h1 h2 h3) (by norm_num) (St S V dv)
    a b _ _ (termOK_mark _) (termOK_mark _) (St_int S V dv hx) (St_int S V dv hy) []).of_eq
    (St_push S V dv hz (.int (a + b))) (U_lin hI.one (by omega))

theorem sSbI {x y z : Fin 16} {a b : ℤ} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z)
    (hx : V x = some (.int a)) (hy : V y = some (.int b)) (hz : V z = none)
    (ha : bitLen a.natAbs ≤ W) (hb : bitLen b.natAbs ≤ W) :
    HT [] (St S V dv) (pSbI I x y z) (St S (Function.update V z (some (.int (a - b)))) dv) (U C W) :=
  (HT.callI_upd I.si [.inr x, .inr y, .inr z] (.inl 0) (nd3 h1 h2 h3) rfl (by norm_num) I.lsi
    (St S V dv) (.inl 2) _ (hI.si a b _ _ _ (termOK_mark _) (termOK_mark _) (St_int S V dv hx)
      (St_int S V dv hy)) []).of_eq (St_push S V dv hz (.int (a - b))) (U_lin hI.one (by omega))

theorem sDiv {x y z : Fin 16} {n : ℤ} {d : ℕ} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z)
    (hx : V x = some (.int n)) (hy : V y = some (.nat d)) (hz : V z = none) (hd : 0 < d)
    (hn : bitLen n.natAbs ≤ W) (hdw : bitLen d ≤ W) :
    HT [] (St S V dv) (pDiv I x y z)
      (St S (Function.update V z (some (.int (IntMul.divRoundRatInt n d)))) dv) (U C W) :=
  (HT.callI_upd I.dv [.inr x, .inr y, .inr z] (.inl 0) (nd3 h1 h2 h3) rfl (by norm_num) I.ldv
    (St S V dv) (.inl 2) _ (hI.dv n d _ _ _ hd (termOK_mark _) (termOK_mark _) (St_int S V dv hx)
      (St_nat S V dv hy)) []).of_eq (St_push S V dv hz (.int (divRoundRatInt n d)))
    (U_quad hI.one (by omega) (by omega))

theorem sIsq {x z : Fin 16} {a : ℕ} (h1 : x ≠ z) (hx : V x = some (.nat a)) (hz : V z = none)
    (ha : bitLen a ≤ W) :
    HT [] (St S V dv) (pIsq I x z) (St S (Function.update V z (some (.nat (Nat.sqrt a)))) dv)
      (U C W) :=
  (HT.callI_upd I.sq [.inr x, .inr z] (.inl 0) (nd2 h1) rfl (by norm_num) I.lsq (St S V dv) (.inl 1)
    _ (hI.sq a _ _ (termOK_mark _) (St_nat S V dv hx)) []).of_eq
    (St_push S V dv hz (.nat (Nat.sqrt a))) (U_sq hI.one (by omega))

theorem sPi {x z : Fin 16} {B : ℕ} (h1 : x ≠ z) (hx : V x = some (.nat B)) (hz : V z = none)
    (hB : B ≤ W) :
    HT [] (St S V dv) (pPi I x z)
      (St S (Function.update V z (some (.int (IntMul.computablePiScaledWithCost B).1))) dv) (U C W) :=
  (HT.piScaled hI.pi (.inl 0) I.lpi (.inr x) (.inr z) (nd2 h1) (by norm_num) (St S V dv) B _
    (termOK_mark _) (St_nat S V dv hx) []).of_eq
    (St_push S V dv hz (.int (IntMul.computablePiScaledWithCost B).1)) (U_four hI.one hB)

theorem sLn {x z : Fin 16} {B : ℕ} (h1 : x ≠ z) (hx : V x = some (.nat B)) (hz : V z = none)
    (hB : B ≤ W) :
    HT [] (St S V dv) (pLn I x z)
      (St S (Function.update V z (some (.int (IntMul.computableLog2ScaledWithCost B).1))) dv)
      (U C W) :=
  (HT.log2Scaled hI.ln (.inl 0) I.lln (.inr x) (.inr z) (nd2 h1) (by norm_num) (St S V dv) B _
    (termOK_mark _) (St_nat S V dv hx) []).of_eq
    (St_push S V dv hz (.int (IntMul.computableLog2ScaledWithCost B).1)) (U_four hI.one hB)

theorem sDrN {x : Fin 16} {a : ℕ} (hx : V x = some (.nat a)) (ha : bitLen a ≤ W) :
    HT [] (St S V dv) (pDrN I x) (St S (Function.update V x none) dv) (U C W) :=
  (HT.dropNat hI.dr (.inl 0) I.ldr (.inr x) (by norm_num) (St S V dv) a _ (termOK_mark _)
    (St_nat S V dv hx) []).of_eq (St_clear S V dv x) (U_lin hI.one (by omega))

#assert_std_axioms St_push St_put St_clear St_nat St_int nd2 nd3 sPush sToInt sToNat sCp sAdN
  sSbN sShl sMul sNeg sAdI sSbI sDiv sIsq sPi sLn sDrN

end Rules

end WP.W7k3c
