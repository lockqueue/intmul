import WP.W9c.BlockPackKit

/-!
# WP.W9c.BlockPackOps — the calls of the block-pack program and their record-level rules

Each W3 operation is called through `callI` on host stacks of `Loc 6 8` (named stacks in contract
order, callee scratch on free host stacks). `ht_*` restate the `WP.W7k2` call rules with the host
state as an `HS` record: from `r.f` the call reaches `(r.set j v).f`.
-/

namespace WP.W9c.BlockPack

open TMFw TMFw.Contracts WP.W7k2 Computability

section Progs

variable (K : Kit)

/-- `dst += src` -/
def cCopy (src dst : Loc 6 8) : BProg 6 8 K.Reg := callI K.iCopy [src, dst] kX K.lCopy
/-- drop the number on `s` -/
def cDrop (s : Loc 6 8) : BProg 6 8 K.Reg := callI K.iDrop [s] kX K.lDrop
/-- `s := s + 1` -/
def cInc (s : Loc 6 8) : BProg 6 8 K.Reg := callI K.iInc [s] kX K.lInc
/-- `s := s - 1` -/
def cDec (s : Loc 6 8) : BProg 6 8 K.Reg := callI K.iDec [s] kX K.lDec
/-- `z += x + y` -/
def cAdd (x y z : Loc 6 8) : BProg 6 8 K.Reg := callI K.iAdd [x, y, z] kX K.lAdd
/-- `z += x - y` -/
def cSub (x y z : Loc 6 8) : BProg 6 8 K.Reg := callI K.iSub [x, y, z] kX K.lSub
/-- `s := s * 2^c` -/
def cShl (s c : Loc 6 8) : BProg 6 8 K.Reg := callI K.iShl [s, c] kX K.lShl
/-- `s := s / 2^c` -/
def cShr (s c : Loc 6 8) : BProg 6 8 K.Reg := callI K.iShr [s, c] kX K.lShr
/-- `s := s / 2` -/
def cShr1 (s : Loc 6 8) : BProg 6 8 K.Reg := callI K.iShr1 [s] kX K.lShr1
/-- `x := x / 2^c`, `y += x % 2^c` -/
def cSplit (x c y : Loc 6 8) : BProg 6 8 K.Reg := callI K.iSplit [x, c, y] kX K.lSplit
/-- `x := y + x * 2^c`, `y` consumed -/
def cCat (x c y : Loc 6 8) : BProg 6 8 K.Reg := callI K.iCat [x, c, y] kX K.lCat
/-- `z += x - y` (signed) -/
def cSubI (x y z : Loc 6 8) : BProg 6 8 K.Reg := callI K.iSubI [x, y, z] kX K.lSubI
/-- compare `x` with `y`, then branch on `f (ordOf x y)` -/
def cCmpIte (x y : Loc 6 8) (f : Ordering → Bool) (p q : BProg 6 8 K.Reg) : BProg 6 8 K.Reg :=
  (callI K.iCmp [x, y] kX K.lCmp).seq (.ite (fun s => f (K.iCmp.obs (K.lCmp.get s))) p q)
/-- pop `k`, then branch on the popped symbol -/
def cPopIte (k : Loc 6 8) (f : Option Sym → Bool) (p q : BProg 6 8 K.Reg) : BProg 6 8 K.Reg :=
  (popR' K.lS1 k).seq (.ite (fun v => f (K.lS1.get v)) p q)

end Progs

/-! ## Rules -/

variable {K : Kit} {C : ℕ} {ρ : List (BProg 6 8 K.Reg)}

theorem ht_copy (hK : K.OK C) (r : HS) (src dst : Loc 6 8) (hnd : [src, dst].Nodup) (x : ℕ)
    (rx : List Sym) (hrx : TermOK rx) (hs : r.f src = natSyms x ++ rx) :
    HT ρ r.f (cCopy K src dst) (r.set dst (natSyms x ++ r.f dst)).f (C * (bitLen x + 1)) :=
  (HT.copyNat hK.copy kX K.lCopy src dst hnd (by norm_num) r.f x rx hrx hs ρ).of_eq
    (HS.update_eq_set _ _ _) le_rfl

theorem ht_drop (hK : K.OK C) (r : HS) (s : Loc 6 8) (x : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hs : r.f s = natSyms x ++ rx) :
    HT ρ r.f (cDrop K s) (r.set s rx).f (C * (bitLen x + 1)) :=
  (HT.dropNat hK.drop kX K.lDrop s (by norm_num) r.f x rx hrx hs ρ).of_eq
    (HS.update_eq_set _ _ _) le_rfl

theorem ht_inc (hK : K.OK C) (r : HS) (s : Loc 6 8) (x : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hs : r.f s = natSyms x ++ rx) :
    HT ρ r.f (cInc K s) (r.set s (natSyms (x + 1) ++ rx)).f (C * (ones (encodeNat x) + 1)) :=
  (HT.callI_upd K.iInc [s] kX (List.nodup_singleton s) rfl (by norm_num) K.lInc r.f (.inl 0) _
    (hK.inc x rx _ hrx hs) ρ).of_eq (HS.update_eq_set _ _ _) le_rfl

theorem ht_dec (hK : K.OK C) (r : HS) (s : Loc 6 8) (x : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hs : r.f s = natSyms (x + 1) ++ rx) :
    HT ρ r.f (cDec K s) (r.set s (natSyms x ++ rx)).f
      (C * (zerosLead (encodeNat (x + 1)) + 1)) :=
  (HT.callI_upd K.iDec [s] kX (List.nodup_singleton s) rfl (by norm_num) K.lDec r.f (.inl 0) _
    (hK.dec x rx _ hrx hs) ρ).of_eq (HS.update_eq_set _ _ _) le_rfl

theorem ht_add (hK : K.OK C) (r : HS) (x y z : Loc 6 8) (hnd : [x, y, z].Nodup) (a b' : ℕ)
    (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hx : r.f x = natSyms a ++ rx)
    (hy : r.f y = natSyms b' ++ ry) :
    HT ρ r.f (cAdd K x y z) (r.set z (natSyms (a + b') ++ r.f z)).f
      (C * (bitLen a + bitLen b' + 1)) :=
  (HT.callI_upd K.iAdd [x, y, z] kX hnd rfl (by norm_num) K.lAdd r.f (.inl 2) _
    (hK.add a b' rx ry _ hrx hry hx hy) ρ).of_eq (HS.update_eq_set _ _ _) le_rfl

theorem ht_sub (hK : K.OK C) (r : HS) (x y z : Loc 6 8) (hnd : [x, y, z].Nodup) (a b' : ℕ)
    (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hba : b' ≤ a)
    (hx : r.f x = natSyms a ++ rx) (hy : r.f y = natSyms b' ++ ry) :
    HT ρ r.f (cSub K x y z) (r.set z (natSyms (a - b') ++ r.f z)).f
      (C * (bitLen a + bitLen b' + 1)) :=
  (HT.callI_upd K.iSub [x, y, z] kX hnd rfl (by norm_num) K.lSub r.f (.inl 2) _
    (hK.sub a b' rx ry _ hrx hry hba hx hy) ρ).of_eq (HS.update_eq_set _ _ _) le_rfl

theorem ht_shl (hK : K.OK C) (r : HS) (s c : Loc 6 8) (hnd : [s, c].Nodup) (x y : ℕ)
    (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hs : r.f s = natSyms x ++ rx)
    (hc : r.f c = natSyms y ++ ry) :
    HT ρ r.f (cShl K s c) (r.set s (natSyms (x * 2 ^ y) ++ rx)).f (C * (y + bitLen y + 1)) :=
  (HT.shlVar hK.shl kX K.lShl s c hnd (by norm_num) r.f x y rx ry hrx hry hs hc ρ).of_eq
    (HS.update_eq_set _ _ _) le_rfl

theorem ht_shr (hK : K.OK C) (r : HS) (s c : Loc 6 8) (hnd : [s, c].Nodup) (x y : ℕ)
    (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hs : r.f s = natSyms x ++ rx)
    (hc : r.f c = natSyms y ++ ry) :
    HT ρ r.f (cShr K s c) (r.set s (natSyms (x / 2 ^ y) ++ rx)).f
      (C * (min y (bitLen x) + bitLen y + 1)) :=
  (HT.callI_upd K.iShr [s, c] kX hnd rfl (by norm_num) K.lShr r.f (.inl 0) _
    (hK.shr x y rx ry _ hrx hry hs hc) ρ).of_eq (HS.update_eq_set _ _ _) le_rfl

theorem ht_shr1 (hK : K.OK C) (r : HS) (s : Loc 6 8) (x : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hs : r.f s = natSyms x ++ rx) :
    HT ρ r.f (cShr1 K s) (r.set s (natSyms (x / 2) ++ rx)).f (C * 2) := by
  have h := HT.callI_upd K.iShr1 [s] kX (List.nodup_singleton s) rfl (by norm_num) K.lShr1 r.f
    (.inl 0) _ (hK.shr1 x rx _ hrx hs) ρ
  rw [pow_one] at h
  exact h.of_eq (HS.update_eq_set _ _ _) (by omega)

theorem ht_split (hK : K.OK C) (r : HS) (x c y : Loc 6 8) (hnd : [x, c, y].Nodup) (a cc : ℕ)
    (rx rc : List Sym) (hrx : TermOK rx) (hrc : TermOK rc) (hx : r.f x = natSyms a ++ rx)
    (hc : r.f c = natSyms cc ++ rc) :
    HT ρ r.f (cSplit K x c y)
      ((r.set x (natSyms (a / 2 ^ cc) ++ rx)).set y (natSyms (a % 2 ^ cc) ++ r.f y)).f
      (C * (min cc (bitLen a) + bitLen cc + 1)) := by
  have h := HT.callI_upd2 K.iSplit [x, c, y] kX hnd rfl (by norm_num) K.lSplit r.f (.inl 0)
    (.inl 2) _ _ (hK.split a cc rx rc _ hrx hrc hx hc) ρ
  refine h.of_eq ?_ le_rfl
  rw [HS.update_eq_set, HS.update_eq_set]
  rfl

theorem ht_cat (hK : K.OK C) (r : HS) (x c y : Loc 6 8) (hnd : [x, c, y].Nodup) (hi lo cc : ℕ)
    (rx rc ry : List Sym) (hrx : TermOK rx) (hrc : TermOK rc) (hry : TermOK ry)
    (hlo : lo < 2 ^ cc) (hx : r.f x = natSyms hi ++ rx) (hc : r.f c = natSyms cc ++ rc)
    (hy : r.f y = natSyms lo ++ ry) :
    HT ρ r.f (cCat K x c y) ((r.set x (natSyms (lo + hi * 2 ^ cc) ++ rx)).set y ry).f
      (C * (cc + bitLen cc + 1)) := by
  have h := HT.callI_upd2 K.iCat [x, c, y] kX hnd rfl (by norm_num) K.lCat r.f (.inl 0)
    (.inl 2) _ _ (hK.cat hi lo cc rx rc ry _ hrx hrc hry hlo hx hc hy) ρ
  refine h.of_eq ?_ le_rfl
  rw [HS.update_eq_set, HS.update_eq_set]
  rfl

theorem ht_subI (hK : K.OK C) (r : HS) (x y z : Loc 6 8) (hnd : [x, y, z].Nodup) (a b' : ℤ)
    (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hx : r.f x = intSyms a ++ rx)
    (hy : r.f y = intSyms b' ++ ry) :
    HT ρ r.f (cSubI K x y z) (r.set z (intSyms (a - b') ++ r.f z)).f
      (C * (bitLen a.natAbs + bitLen b'.natAbs + 1)) :=
  (HT.callI_upd K.iSubI [x, y, z] kX hnd rfl (by norm_num) K.lSubI r.f (.inl 2) _
    (hK.subI a b' rx ry _ hrx hry hx hy) ρ).of_eq (HS.update_eq_set _ _ _) le_rfl

theorem ht_cmpIte (hK : K.OK C) (r B' : HS) (x y : Loc 6 8) (hnd : [x, y].Nodup) (u v : ℕ)
    (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv) (hx : r.f x = natSyms u ++ ru)
    (hy : r.f y = natSyms v ++ rv) (f : Ordering → Bool) (p q : BProg 6 8 K.Reg) {T₁ T₂ : ℕ}
    (hp : f (Lib.ordOf u v) = true → HT ρ r.f p B'.f T₁)
    (hq : f (Lib.ordOf u v) = false → HT ρ r.f q B'.f T₂) :
    HT ρ r.f (cCmpIte K x y f p q) B'.f (C * (bitLen u + bitLen v + 1) + (max T₁ T₂ + 1)) :=
  HT.cmpNat_ite hK.cmp kX K.lCmp x y hnd (by norm_num) r.f B'.f u v ru rv hru hrv hx hy f p q ρ
    hp hq

theorem ht_push (r : HS) (k : Loc 6 8) (x : Sym) :
    HT ρ r.f (pushS k x) (r.set k (x :: r.f k)).f 1 :=
  (HT.pushS k x r.f ρ).of_eq (HS.update_eq_set _ _ _) le_rfl

theorem ht_pop (r : HS) (k : Loc 6 8) (x : Sym) (rest : List Sym) (hk : r.f k = x :: rest) :
    HT ρ r.f (popS k) (r.set k rest).f 1 :=
  (HT.popS k r.f x rest hk ρ).of_eq (HS.update_eq_set _ _ _) le_rfl

theorem ht_mvSym (r : HS) (src dst : Loc 6 8) (hne : src ≠ dst) (x : Sym) (rest : List Sym)
    (hB : r.f src = x :: rest) :
    HT ρ r.f (mvSym K.lS1 src dst) ((r.set src rest).set dst (x :: r.f dst)).f 2 := by
  refine (HT.mvSym K.lS1 hne r.f x rest hB).of_eq ?_ le_rfl
  rw [HS.update_eq_set, HS.update_eq_set]

theorem ht_ifTop (r B' : HS) (k : Loc 6 8) (c : Sym → Bool) (p q : BProg 6 8 K.Reg)
    {T₁ T₂ : ℕ} (hp : optP c (r.f k).head? = true → HT ρ r.f p B'.f T₁)
    (hq : optP c (r.f k).head? = false → HT ρ r.f q B'.f T₂) :
    HT ρ r.f (ifTopP K.lS1 k c p q) B'.f (1 + (max T₁ T₂ + 1)) :=
  HT.ifTopP K.lS1 k c r.f B'.f p q hp hq

theorem ht_popIte (r B' : HS) (k : Loc 6 8) (x : Sym) (rest : List Sym)
    (hk : r.f k = x :: rest) (f : Option Sym → Bool) (p q : BProg 6 8 K.Reg) {T₁ T₂ : ℕ}
    (hp : f (some x) = true → HT ρ (r.set k rest).f p B'.f T₁)
    (hq : f (some x) = false → HT ρ (r.set k rest).f q B'.f T₂) :
    HT ρ r.f (cPopIte K k f p q) B'.f (1 + (max T₁ T₂ + 1)) :=
  HT.popBranch K.lS1 k r.f B'.f x rest hk f p q ρ
    (fun h => by rw [HS.update_eq_set]; exact hp h)
    (fun h => by rw [HS.update_eq_set]; exact hq h)

theorem ht_skip (r : HS) : HT ρ r.f skipP r.f 1 := HT.skipP r.f

/-! ## Closedness -/

theorem cCmpIte_closed (x y : Loc 6 8) (f : Ordering → Bool) {p q : BProg 6 8 K.Reg}
    (hp : p.Closed) (hq : q.Closed) : (cCmpIte K x y f p q).Closed :=
  ⟨callI_closed _ _ _ _, hp, hq⟩

theorem cPopIte_closed (k : Loc 6 8) (f : Option Sym → Bool) {p q : BProg 6 8 K.Reg}
    (hp : p.Closed) (hq : q.Closed) : (cPopIte K k f p q).Closed :=
  ⟨trivial, hp, hq⟩

#assert_std_axioms ht_copy ht_drop ht_inc ht_dec ht_add ht_sub ht_shl ht_shr ht_shr1 ht_split
  ht_cat ht_subI ht_cmpIte ht_push ht_pop ht_mvSym ht_ifTop ht_popIte ht_skip cCmpIte_closed
  cPopIte_closed

end WP.W9c.BlockPack
