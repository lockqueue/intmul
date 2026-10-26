import WP.W7k3t.Base
import WP.W7k2.ColRecip

/-!
# WP.W7k3t.Rules — host programs and rules of the base operations, at uniform cost `uc U W`

Every rule is generic in the host `Loc a b` (`[Big a b]`: at least 24 stacks). A call whose operands
have bit length `≤ W` costs `≤ uc U W` (`TI.Ok I U`); raw pushes and pops too. Sub-kernels are
packaged with `mkInst` and called with `tsub` (`tsub_ht`).
-/

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

/-- Host programs over `Loc a b` with the bundle's registers. -/
abbrev HP (a b : ℕ) (I : TI) : Type := Prog (Loc a b) (fun _ => Sym) I.R

section Programs

variable {a b : ℕ} [NeZero a] (I : TI)

def tcp (x y : Loc a b) : HP a b I := callI I.cp [x, y] (.inl 0) I.lcp
def tdr (x : Loc a b) : HP a b I := callI I.dr [x] (.inl 0) I.ldr
def tic (x : Loc a b) : HP a b I := callI I.ic [x] (.inl 0) I.lic
def tad (x y z : Loc a b) : HP a b I := callI I.ad [x, y, z] (.inl 0) I.lad
def tsv (x c : Loc a b) : HP a b I := callI I.sv [x, c] (.inl 0) I.lsv
def tcm (x y : Loc a b) : HP a b I := callI I.cm [x, y] (.inl 0) I.lcm
def tai (x y z : Loc a b) : HP a b I := callI I.ai [x, y, z] (.inl 0) I.lai
def tsi (x y z : Loc a b) : HP a b I := callI I.si [x, y, z] (.inl 0) I.lsi
def tci (x y : Loc a b) : HP a b I := callI I.ci [x, y] (.inl 0) I.lci
def tmu (x y z : Loc a b) : HP a b I := callI I.mu [x, y, z] (.inl 0) I.lmu
def tdv (x y z : Loc a b) : HP a b I := callI I.dv [x, y, z] (.inl 0) I.ldv

/-- `while ctr ≠ 0 do (dec ctr; body)`. -/
def tcd (ctr : Loc a b) (body : HP a b I) : HP a b I :=
  cdLoop I.iz I.dc I.liz I.ldc ctr (.inl 0) body

/-- Drop the signed number on `x`. -/
def tdrI (x : Loc a b) : HP a b I := (popS x).seq (tdr I x)

/-- `x += 2^c` (`c` read from its stack). -/
def tp2 (c x : Loc a b) : HP a b I := (pushS x (.bit true)).seq (tsv I x c)

/-- Package a closed program on `Loc n m` (registers `I.R`) as an instance. -/
def mkInst {n m : ℕ} (P : Prog (Loc n m) (fun _ => Sym) I.R) (hP : P.Closed) : Inst n m Unit :=
  ⟨m, I.R, fun _ => (), P, le_rfl, I.R_finite, I.R_nonempty, hP⟩

/-- Call a packaged sub-kernel on the host stacks `named`. -/
def tsub {n m : ℕ} (P : Prog (Loc n m) (fun _ => Sym) I.R) (hP : P.Closed)
    (named : List (Loc a b)) : HP a b I :=
  callI (mkInst I P hP) named (.inl 0) (lid I.R)

theorem tdrI_closed (x : Loc a b) : (tdrI I x).Closed := ⟨trivial, callI_closed _ _ _ _⟩

theorem tp2_closed (c x : Loc a b) : (tp2 I c x).Closed := ⟨trivial, callI_closed _ _ _ _⟩

theorem tcd_closed (ctr : Loc a b) (body : HP a b I) (hb : body.Closed) :
    (tcd I ctr body).Closed :=
  cdLoop_closed _ _ _ _ _ _ _ hb

theorem tsub_closed {n m : ℕ} (P : Prog (Loc n m) (fun _ => Sym) I.R) (hP : P.Closed)
    (named : List (Loc a b)) : (tsub I P hP named).Closed :=
  callI_closed _ _ _ _

end Programs

/-! ## Rules -/

section Cap

variable {a b : ℕ} [Big a b]

theorem cap_le {k : ℕ} (hk : k ≤ 24) : k ≤ a + b := le_trans hk Big.le

end Cap

section Rules

variable {a b : ℕ} [NeZero a] [Big a b] {I : TI} {U : ℕ}

theorem tcp_ht (hI : I.Ok U) (x y : Loc a b) (hxy : x ≠ y) (B : Loc a b → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) {W : ℕ} (hw : bitLen v ≤ W)
    (ρ : List (HP a b I)) :
    HT ρ B (tcp I x y) (Function.update B y (natSyms v ++ B y)) (uc U W) :=
  (HT.copyNat hI.cp (.inl 0) I.lcp x y (by simp [hxy]) (cap_le (by norm_num)) B v r hr hB
    ρ).mono (uc_lin hw)

theorem tdr_ht (hI : I.Ok U) (x : Loc a b) (B : Loc a b → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) {W : ℕ} (hw : bitLen v ≤ W)
    (ρ : List (HP a b I)) :
    HT ρ B (tdr I x) (Function.update B x r) (uc U W) :=
  (HT.dropNat hI.dr (.inl 0) I.ldr x (cap_le (by norm_num)) B v r hr hB ρ).mono (uc_lin hw)

theorem tic_ht (hI : I.Ok U) (x : Loc a b) (B : Loc a b → List Sym) (v : ℕ) (r : List Sym)
    (hr : TermOK r) (hB : B x = natSyms v ++ r) {W : ℕ} (hw : bitLen v ≤ W)
    (ρ : List (HP a b I)) :
    HT ρ B (tic I x) (Function.update B x (natSyms (v + 1) ++ r)) (uc U W) :=
  (HT.incNat hI.ic (.inl 0) I.lic x (cap_le (by norm_num)) B v r hr hB ρ).mono
    (le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (ones_le_length _) 1)) (uc_lin hw))

theorem tad_ht (hI : I.Ok U) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (B : Loc a b → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) {W : ℕ} (hu : bitLen u ≤ W)
    (hv : bitLen v ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (tad I x y z) (Function.update B z (natSyms (u + v) ++ B z)) (uc U W) :=
  (HT.addNat hI.ad (.inl 0) I.lad x y z hnd (cap_le (by norm_num)) B u v ru rv hru hrv hx hy
    ρ).mono (uc_lin2 hu hv)

theorem tsv_ht (hI : I.Ok U) (x c : Loc a b) (hxc : x ≠ c) (B : Loc a b → List Sym) (u v : ℕ)
    (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv) (hx : B x = natSyms u ++ ru)
    (hc : B c = natSyms v ++ rv) {W : ℕ} (hv : v ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (tsv I x c) (Function.update B x (natSyms (u * 2 ^ v) ++ ru)) (uc U W) :=
  (HT.shlVar hI.sv (.inl 0) I.lsv x c (by simp [hxc]) (cap_le (by norm_num)) B u v ru rv hru hrv
    hx hc ρ).mono (uc_lin2 hv (le_trans (bitLen_le_self v) hv))

theorem tcm_ite_ht (hI : I.Ok U) (x y : Loc a b) (hxy : x ≠ y) (B B' : Loc a b → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) {W : ℕ} (hu : bitLen u ≤ W)
    (hv : bitLen v ≤ W) (f : Ordering → Bool) (p q : HP a b I) (ρ : List (HP a b I))
    {T₁ T₂ : ℕ} (hp : f (Lib.ordOf u v) = true → HT ρ B p B' T₁)
    (hq : f (Lib.ordOf u v) = false → HT ρ B q B' T₂) :
    HT ρ B ((tcm I x y).seq (.ite (fun s => f (I.cm.obs (I.lcm.get s))) p q)) B'
      (uc U W + (max T₁ T₂ + 1)) :=
  (HT.cmpNat_ite hI.cm (.inl 0) I.lcm x y (by simp [hxy]) (cap_le (by norm_num)) B B' u v ru rv
    hru hrv hx hy f p q ρ hp hq).mono (Nat.add_le_add_right (uc_lin2 hu hv) _)

theorem tai_ht (hI : I.Ok U) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (B : Loc a b → List Sym)
    (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv) {W : ℕ}
    (hu : bitLen u.natAbs ≤ W) (hv : bitLen v.natAbs ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (tai I x y z) (Function.update B z (intSyms (u + v) ++ B z)) (uc U W) :=
  (HT.addInt hI.ai (.inl 0) I.lai x y z hnd (cap_le (by norm_num)) B u v ru rv hru hrv hx hy
    ρ).mono (uc_lin2 hu hv)

theorem tsi_ht (hI : I.Ok U) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (B : Loc a b → List Sym)
    (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv) {W : ℕ}
    (hu : bitLen u.natAbs ≤ W) (hv : bitLen v.natAbs ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (tsi I x y z) (Function.update B z (intSyms (u - v) ++ B z)) (uc U W) :=
  (HT.callI_upd I.si [x, y, z] (.inl 0) hnd rfl (cap_le (by norm_num)) I.lsi B (.inl 2) _
    (hI.si u v ru rv _ hru hrv hx hy) ρ).mono (uc_lin2 hu hv)

theorem tci_ite_ht (hI : I.Ok U) (x y : Loc a b) (hxy : x ≠ y) (B B' : Loc a b → List Sym)
    (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv) {W : ℕ}
    (hu : bitLen u.natAbs ≤ W) (hv : bitLen v.natAbs ≤ W) (f : Ordering → Bool)
    (p q : HP a b I) (ρ : List (HP a b I)) {T₁ T₂ : ℕ}
    (hp : f (cmpZ u v) = true → HT ρ B p B' T₁) (hq : f (cmpZ u v) = false → HT ρ B q B' T₂) :
    HT ρ B ((tci I x y).seq (.ite (fun s => f (I.ci.obs (I.lci.get s))) p q)) B'
      (uc U W + (max T₁ T₂ + 1)) :=
  (HT.callI_test I.ci [x, y] (.inl 0) (by simp [hxy]) rfl (cap_le (by norm_num)) I.lci B B' f
    (cmpZ u v) (hI.ci u v ru rv _ hru hrv hx hy) p q ρ hp hq).mono
    (Nat.add_le_add_right (uc_lin2 hu hv) _)

theorem tmu_ht (hI : I.Ok U) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (B : Loc a b → List Sym)
    (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv) {W : ℕ}
    (hu : bitLen u.natAbs ≤ W) (hv : bitLen v.natAbs ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (tmu I x y z) (Function.update B z (intSyms (u * v) ++ B z)) (uc U W) :=
  HT.callI_upd I.mu [x, y, z] (.inl 0) hnd rfl (cap_le (by norm_num)) I.lmu B (.inl 2) _
    (hI.mu W u v ru rv _ hu hv hru hrv hx hy) ρ

/-- Multiplication of two non-negative numbers (`pos` sign on top). -/
theorem tmuN_ht (hI : I.Ok U) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (B : Loc a b → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = Sym.pos :: (natSyms u ++ ru)) (hy : B y = Sym.pos :: (natSyms v ++ rv)) {W : ℕ}
    (hu : bitLen u ≤ W) (hv : bitLen v ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (tmu I x y z) (Function.update B z (Sym.pos :: (natSyms (u * v) ++ B z))) (uc U W) := by
  have h := tmu_ht hI x y z hnd B (u : ℤ) (v : ℤ) ru rv hru hrv
    (by rw [hx, intSyms_natCast]; rfl) (by rw [hy, intSyms_natCast]; rfl)
    (by simpa using hu) (by simpa using hv) ρ
  rwa [← Nat.cast_mul, intSyms_natCast, List.cons_append] at h

theorem tdv_ht (hI : I.Ok U) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (B : Loc a b → List Sym)
    (u : ℤ) (v : ℕ) (ru rv : List Sym) (hv0 : 0 < v) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = natSyms v ++ rv) {W : ℕ}
    (hu : bitLen u.natAbs ≤ W) (hv : bitLen v ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (tdv I x y z) (Function.update B z (intSyms (divRoundRatInt u v) ++ B z)) (uc U W) :=
  (HT.callI_upd I.dv [x, y, z] (.inl 0) hnd rfl (cap_le (by norm_num)) I.ldv B (.inl 2) _
    (hI.dv u v ru rv _ hv0 hru hrv hx hy) ρ).mono (uc_quad hu hv)

omit [NeZero a] [Big a b] in
theorem push_ht (hI : I.Ok U) (k : Loc a b) (s : Sym) (B : Loc a b → List Sym) {W : ℕ}
    (ρ : List (HP a b I)) :
    HT ρ B (pushS k s) (Function.update B k (s :: B k)) (uc U W) :=
  (HT.pushS k s B ρ).mono (uc_one hI.one)

omit [NeZero a] [Big a b] in
theorem pop_ht (hI : I.Ok U) (k : Loc a b) (B : Loc a b → List Sym) (s : Sym) (rest : List Sym)
    (hk : B k = s :: rest) {W : ℕ} (ρ : List (HP a b I)) :
    HT ρ B (popS k) (Function.update B k rest) (uc U W) :=
  (HT.popS k B s rest hk ρ).mono (uc_one hI.one)

theorem tdrI_ht (hI : I.Ok U) (x : Loc a b) (B : Loc a b → List Sym) (z : ℤ) (r : List Sym)
    (hr : TermOK r) (hB : B x = intSyms z ++ r) {W : ℕ} (hw : bitLen z.natAbs ≤ W)
    (ρ : List (HP a b I)) :
    HT ρ B (tdrI I x) (Function.update B x r) (2 * uc U W) := by
  have hBx : B x = sgnSym z :: (natSyms z.natAbs ++ r) := by rw [hB]; rfl
  refine (HT.seq (pop_ht hI x B _ _ hBx (W := W) ρ) (tdr_ht hI x _ z.natAbs r hr (by simp) hw ρ)).of_eq ?_
    (by omega)
  rw [Function.update_idem]

theorem tp2_ht (hI : I.Ok U) (c x : Loc a b) (hxc : x ≠ c) (B : Loc a b → List Sym) (k : ℕ)
    (rc : List Sym) (hrc : TermOK rc) (hc : B c = natSyms k ++ rc) (hx : TermOK (B x)) {W : ℕ}
    (hk : k ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (tp2 I c x) (Function.update B x (natSyms (2 ^ k) ++ B x)) (2 * uc U W) := by
  refine (HT.seq (push_ht hI x (.bit true) B (W := W) ρ) (tsv_ht hI x c hxc _ 1 k (B x) rc hx hrc
    (by simp [natSyms_one]) (by simp [Function.update_of_ne (Ne.symm hxc), hc]) hk ρ)).of_eq ?_
    (by omega)
  rw [Function.update_idem, one_mul]

omit [Big a b] in
/-- **Calling a packaged sub-kernel**: a program whose exact-stacks triple updates its named
stack `o` with `v` gives the same update on the host stack `named[o]`. -/
theorem tsub_ht {n m : ℕ} (P : Prog (Loc n m) (fun _ => Sym) I.R) (hP : P.Closed)
    (named : List (Loc a b)) (hnd : named.Nodup) (hn : named.length = n) (hcap : m + n ≤ a + b)
    (B : Loc a b → List Sym) (o : Fin n) (v : List Sym) {T : ℕ}
    (h : HT [] (fun x => B (callMap (.inl 0) named x)) P
      (Function.update (fun x => B (callMap (.inl 0) named x)) (.inl o) v) T)
    (ρ : List (HP a b I)) :
    HT ρ B (tsub I P hP named) (Function.update B (named.getD o (.inl 0)) v) T :=
  HT.callI_upd (mkInst I P hP) named (.inl 0) hnd hn hcap (lid I.R) B (.inl o) v (HT.runs h) ρ

end Rules

#assert_std_axioms tdrI_closed tp2_closed tcd_closed tsub_closed cap_le tcp_ht tdr_ht tic_ht tad_ht tsv_ht
  tcm_ite_ht tai_ht tsi_ht tci_ite_ht tmu_ht tmuN_ht tdv_ht push_ht pop_ht tdrI_ht tp2_ht tsub_ht

end WP.W7k3t
