import WP.W9h.Loop

/-!
# WP.W9h.KOps — kernel-level operations of a `Kit` on the host `H`

Shorthands for calling the kit's instances on host stacks (default stack `hS`, the kit's register
lenses) and their exact host rules at the kit's single cost constant.
-/

namespace WP.W9h

open TMFw TMFw.Contracts WP.W7k2

namespace Kit

variable (K : Kit)

/-- Kernel programs. -/
abbrev KP : Type := Prog H (fun _ => Sym) K.Reg

def cp (x y : H) : K.KP := callI K.copy [x, y] hS K.lCopy
def dr (x : H) : K.KP := callI K.drop [x] hS K.lDrop
def ad (x y z : H) : K.KP := callI K.add [x, y, z] hS K.lAdd
def spl (x c y : H) : K.KP := callI K.split [x, c, y] hS K.lSplit
def cat (x c y : H) : K.KP := callI K.concat [x, c, y] hS K.lConcat
def sh2 (x : H) : K.KP := callI K.shl2 [x] hS K.lShl2
def shv (x c : H) : K.KP := callI K.shlV [x, c] hS K.lShlV
def sk (src tmp : H) : K.KP := skipF K.lS src tmp
def usk (tmp src : H) : K.KP := unskipF K.lS tmp src
def push (k : H) (x : Sym) : K.KP := pushS k x
def pop (k : H) : K.KP := popS k
def loopc (ctr : H) (body : K.KP) : K.KP := cdLoop K.isZ K.dec K.lIsZ K.lDec ctr hS body

variable {K} {C : ℕ} (hK : K.Spec C)
include hK

theorem HT_cp {x y : H} (hnd : [x, y].Nodup) (B : H → List Sym) (u : ℕ) (r : List Sym)
    (hr : TermOK r) (hx : B x = natSyms u ++ r) :
    HT [] B (K.cp x y) (Function.update B y (natSyms u ++ B y)) (C * (bitLen u + 1)) :=
  HT.copyNat hK.copy hS K.lCopy x y hnd (by norm_num) B u r hr hx []

theorem HT_dr (x : H) (B : H → List Sym) (u : ℕ) (r : List Sym) (hr : TermOK r)
    (hx : B x = natSyms u ++ r) :
    HT [] B (K.dr x) (Function.update B x r) (C * (bitLen u + 1)) :=
  HT.dropNat hK.drop hS K.lDrop x (by norm_num) B u r hr hx []

theorem HT_ad {x y z : H} (hnd : [x, y, z].Nodup) (B : H → List Sym) (u v : ℕ)
    (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv) (hx : B x = natSyms u ++ ru)
    (hy : B y = natSyms v ++ rv) :
    HT [] B (K.ad x y z) (Function.update B z (natSyms (u + v) ++ B z))
      (C * (bitLen u + bitLen v + 1)) :=
  HT.addNat hK.add hS K.lAdd x y z hnd (by norm_num) B u v ru rv hru hrv hx hy []

theorem HT_spl {x c y : H} (hnd : [x, c, y].Nodup) (B : H → List Sym) (u w : ℕ)
    (rx rc : List Sym) (hrx : TermOK rx) (hrc : TermOK rc) (hx : B x = natSyms u ++ rx)
    (hc : B c = natSyms w ++ rc) :
    HT [] B (K.spl x c y)
      (Function.update (Function.update B x (natSyms (u / 2 ^ w) ++ rx)) y
        (natSyms (u % 2 ^ w) ++ B y))
      (C * (min w (bitLen u) + bitLen w + 1)) :=
  HT.splitAt hK.split hS K.lSplit x c y hnd (by norm_num) B u w rx rc hrx hrc hx hc []

theorem HT_cat {x c y : H} (hnd : [x, c, y].Nodup) (B : H → List Sym) (hi lo w : ℕ)
    (rx rc ry : List Sym) (hrx : TermOK rx) (hrc : TermOK rc) (hry : TermOK ry)
    (hlo : lo < 2 ^ w) (hx : B x = natSyms hi ++ rx) (hc : B c = natSyms w ++ rc)
    (hy : B y = natSyms lo ++ ry) :
    HT [] B (K.cat x c y)
      (Function.update (Function.update B x (natSyms (lo + hi * 2 ^ w) ++ rx)) y ry)
      (C * (w + bitLen w + 1)) :=
  HT.concatAt hK.concat hS K.lConcat x c y hnd (by norm_num) B hi lo w rx rc ry hrx hrc hry hlo
    hx hc hy []

theorem HT_sh2 (x : H) (B : H → List Sym) (u : ℕ) (r : List Sym) (hr : TermOK r)
    (hx : B x = natSyms u ++ r) :
    HT [] B (K.sh2 x) (Function.update B x (natSyms (u * 2 ^ 2) ++ r)) (C * (2 + 1)) :=
  HT.shlConst hK.shl2 hS K.lShl2 x (by norm_num) B u r hr hx []

theorem HT_shv {x c : H} (hnd : [x, c].Nodup) (B : H → List Sym) (u w : ℕ) (rx rc : List Sym)
    (hrx : TermOK rx) (hrc : TermOK rc) (hx : B x = natSyms u ++ rx) (hc : B c = natSyms w ++ rc) :
    HT [] B (K.shv x c) (Function.update B x (natSyms (u * 2 ^ w) ++ rx))
      (C * (w + bitLen w + 1)) :=
  HT.shlVar hK.shlV hS K.lShlV x c hnd (by norm_num) B u w rx rc hrx hrc hx hc []

omit hK in
theorem HT_push (k : H) (x : Sym) (B : H → List Sym) :
    HT [] B (K.push k x) (Function.update B k (x :: B k)) 1 :=
  HT.pushS k x B []

omit hK in
theorem HT_pop (k : H) (B : H → List Sym) (x : Sym) (r : List Sym) (hk : B k = x :: r) :
    HT [] B (K.pop k) (Function.update B k r) 1 :=
  HT.popS k B x r hk []

theorem HT_loopc (ctr : H) (rc : List Sym) (hrc : TermOK rc) (n : ℕ)
    (St : ℕ → H → List Sym) (hSt : ∀ i ≤ n, St i ctr = natSyms i ++ rc) (body : K.KP) (c : ℕ)
    (hbody : ∀ i < n, HT [] (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i) c) :
    HT [] (St n) (K.loopc ctr body) (St 0) (C * (2 * n + bitLen n) + n * (c + C + 1) + 1 + C) :=
  (HT.cdLoop hK.isZ hK.dec K.lIsZ K.lDec ctr hS (by norm_num) rc hrc n St hSt body (fun _ => c)
    hbody).mono
    (by
      have := loopCost_amort hK.amort C C c (fun _ => c) n (fun _ _ => le_rfl)
      beta_reduce at this ⊢
      omega)

omit hK

/-! ## Closedness -/

theorem cp_closed (x y : H) : (K.cp x y).Closed := callI_closed _ _ _ _
theorem dr_closed (x : H) : (K.dr x).Closed := callI_closed _ _ _ _
theorem ad_closed (x y z : H) : (K.ad x y z).Closed := callI_closed _ _ _ _
theorem spl_closed (x c y : H) : (K.spl x c y).Closed := callI_closed _ _ _ _
theorem cat_closed (x c y : H) : (K.cat x c y).Closed := callI_closed _ _ _ _
theorem sh2_closed (x : H) : (K.sh2 x).Closed := callI_closed _ _ _ _
theorem shv_closed (x c : H) : (K.shv x c).Closed := callI_closed _ _ _ _
theorem sk_closed (x y : H) : (K.sk x y).Closed := skipF_closed _ _ _
theorem usk_closed (x y : H) : (K.usk x y).Closed := unskipF_closed _ _ _
theorem push_closed (k : H) (x : Sym) : (K.push k x).Closed := trivial
theorem pop_closed (k : H) : (K.pop k).Closed := trivial
theorem loopc_closed (ctr : H) {body : K.KP} (h : body.Closed) : (K.loopc ctr body).Closed :=
  cdLoop_closed _ _ _ _ _ _ _ h

end Kit

#assert_std_axioms Kit.HT_cp Kit.HT_dr Kit.HT_ad Kit.HT_spl Kit.HT_cat Kit.HT_sh2 Kit.HT_shv
  Kit.HT_push Kit.HT_pop Kit.HT_loopc Kit.loopc_closed

end WP.W9h
