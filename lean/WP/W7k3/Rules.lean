import WP.W7k3.Base

/-!
# WP.W7k3.Rules — uniform-cost host rules

A cost context `X : KX` fixes the multiplication cost `X.Mul`, the bundle constant `X.C`, the growth
constant `X.K` (`Mul w ≤ K·(w+1)²`) and an operand width bound `X.V`. The **cost unit** is
`X.U = C·(K+8)·(V+1)²`. Every W3 / W5 / W6a call whose operands have at most `V` bits costs at most
`X.U` (`HT.u*`), so a straight-line kernel phase of `m` calls costs at most `m·X.U`.

`HT.uloop`: the countdown loop `kloop` (`while ctr ≠ 0 do (dec ctr; body)`) with a uniform body
cost, the body premise only below the trip count.
-/

namespace WP.W7k3

open TMFw TMFw.Contracts WP.W7k2

/-! ## The cost context -/

/-- A cost context. -/
structure KX where
  Mul : ℕ → ℕ
  C : ℕ
  K : ℕ
  V : ℕ

/-- The uniform per-operation cost unit. -/
def KX.U (X : KX) : ℕ := X.C * (X.K + 8) * (X.V + 1) ^ 2

/-- The bundle meets its contracts in context `X`, and `Mul` grows at most quadratically. -/
structure KX.OK (X : KX) (I : KI) : Prop where
  spec : I.Spec X.Mul X.C
  grow : ∀ w, X.Mul w ≤ X.K * (w + 1) ^ 2

namespace KX

variable {X : KX} {I : KI}

theorem le_U (_hX : X.OK I) {t : ℕ} (ht : t ≤ (X.K + 8) * (X.V + 1) ^ 2) : X.C * t ≤ X.U := by
  unfold U
  calc X.C * t ≤ X.C * ((X.K + 8) * (X.V + 1) ^ 2) := Nat.mul_le_mul_left _ ht
    _ = X.C * (X.K + 8) * (X.V + 1) ^ 2 := by ring

theorem sq_le (X : KX) {x : ℕ} (hx : x ≤ (X.V + 1) ^ 2) : x ≤ (X.K + 8) * (X.V + 1) ^ 2 :=
  le_trans hx (Nat.le_mul_of_pos_left _ (by omega))

theorem eight_le (hX : X.OK I) : 8 ≤ X.U := by
  have h1 := hX.spec.one
  have h2 : 1 ≤ (X.V + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold U
  calc 8 = 1 * 8 * 1 := by norm_num
    _ ≤ X.C * (X.K + 8) * (X.V + 1) ^ 2 := Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) h2

theorem cst (hX : X.OK I) : X.C ≤ X.U := by
  have h := le_U hX (t := 1) (le_trans (Nat.one_le_pow _ _ (by omega)) (sq_le X le_rfl))
  simpa using h

theorem lin (hX : X.OK I) {x : ℕ} (hx : x ≤ X.V) : X.C * (x + 1) ≤ X.U :=
  le_U hX (sq_le X (by nlinarith))

theorem two (hX : X.OK I) {x y : ℕ} (hx : x ≤ X.V) (hy : y ≤ X.V) : X.C * (x + y + 1) ≤ X.U :=
  le_U hX (sq_le X (by nlinarith))

theorem dm (hX : X.OK I) {x y : ℕ} (hx : x ≤ X.V) (hy : y ≤ X.V) :
    X.C * (x * y + x + y + 1) ≤ X.U := by
  refine le_U hX (sq_le X ?_)
  have h := Nat.mul_le_mul (show x + 1 ≤ X.V + 1 by omega) (show y + 1 ≤ X.V + 1 by omega)
  nlinarith

theorem k2 (hX : X.OK I) : X.C * (1 + 1) ≤ X.U :=
  le_U hX (le_trans (by norm_num : 1 + 1 ≤ 8 * 1)
    (Nat.mul_le_mul (by omega) (Nat.one_le_pow _ _ (by omega))))

theorem mul (hX : X.OK I) : X.C * X.Mul X.V + X.C ≤ X.U := by
  have hg := hX.grow X.V
  have h1 : X.C * X.Mul X.V ≤ X.C * (X.K * (X.V + 1) ^ 2) := Nat.mul_le_mul_left _ hg
  have h2 : X.C ≤ X.C * (X.V + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have e : X.U = X.C * (X.K * (X.V + 1) ^ 2) + 8 * (X.C * (X.V + 1) ^ 2) := by unfold U; ring
  omega

end KX

/-! ## Uniform-cost host rules -/

section URules

variable {a b : ℕ} {X : KX} {I : KI}

theorem HT.ucp (hX : X.OK I) (x y : Loc a b) (hxy : [x, y].Nodup) (hcap : 4 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (v : ℕ) (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r)
    (hv : bitLen v ≤ X.V) : HT [] B (kcp I x y) (Function.update B y (natSyms v ++ B y)) X.U :=
  (HT.copyNat hX.spec.cp x I.lcp x y hxy hcap B v r hr hB []).mono (KX.lin hX hv)

theorem HT.udr (hX : X.OK I) (x : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (hv : bitLen v ≤ X.V) :
    HT [] B (kdr I x) (Function.update B x r) X.U :=
  (HT.dropNat hX.spec.dr x I.ldr x hcap B v r hr hB []).mono (KX.lin hX hv)

theorem HT.uic (hX : X.OK I) (x : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) (hv : bitLen v ≤ X.V) :
    HT [] B (kic I x) (Function.update B x (natSyms (v + 1) ++ r)) X.U :=
  (HT.incNat hX.spec.ic x I.lic x hcap B v r hr hB []).mono
    (le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (ones_le_length _) 1)) (KX.lin hX hv))

theorem HT.uad (hX : X.OK I) (hE : I.SpecX X.C) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (hu : bitLen u ≤ X.V)
    (hv : bitLen v ≤ X.V) :
    HT [] B (kad I x y z) (Function.update B z (natSyms (u + v) ++ B z)) X.U :=
  (HT.addNat hE.ad x I.lad x y z hnd hcap B u v ru rv hru hrv hx hy []).mono (KX.two hX hu hv)

theorem HT.us1 (hX : X.OK I) (hE : I.SpecX X.C) (x : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (v : ℕ)
    (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) :
    HT [] B (ks1 I x) (Function.update B x (natSyms (v * 2 ^ 1) ++ r)) X.U :=
  (HT.shlConst hE.s1 x I.ls1 x hcap B v r hr hB []).mono (KX.k2 hX)

theorem HT.usv (hX : X.OK I) (hE : I.SpecX X.C) (x c : Loc a b) (hnd : [x, c].Nodup) (hcap : 4 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hc : B c = natSyms v ++ rv) (hv : v ≤ X.V) :
    HT [] B (ksv I x c) (Function.update B x (natSyms (u * 2 ^ v) ++ ru)) X.U :=
  (HT.shlVar hE.sv x I.lsv x c hnd hcap B u v ru rv hru hrv hx hc []).mono
    (KX.two hX hv (le_trans (bitLen_le_self v) hv))

theorem HT.uai (hX : X.OK I) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv) (hu : bitLen u.natAbs ≤ X.V)
    (hv : bitLen v.natAbs ≤ X.V) :
    HT [] B (kai I x y z) (Function.update B z (intSyms (u + v) ++ B z)) X.U :=
  (HT.addInt hX.spec.ai x I.lai x y z hnd hcap B u v ru rv hru hrv hx hy []).mono (KX.two hX hu hv)

theorem HT.ung (hX : X.OK I) (hE : I.SpecX X.C) (x : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (z : ℤ)
    (r : List Sym) (hr : TermOK r) (hB : B x = intSyms z ++ r) :
    HT [] B (kng I x) (Function.update B x (intSyms (-z) ++ r)) X.U :=
  (HT.callI_upd I.ng [x] x (List.nodup_singleton x) rfl hcap I.lng B (.inl 0) _
    (hE.ng z r _ hr hB) []).mono (KX.cst hX)

theorem HT.umu (hX : X.OK I) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (hcap : 8 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv) (hu : bitLen u.natAbs ≤ X.V)
    (hv : bitLen v.natAbs ≤ X.V) :
    HT [] B (kmu I x y z) (Function.update B z (intSyms (u * v) ++ B z)) X.U :=
  (HT.mul hX.spec.mu x I.lmu x y z hnd hcap B X.V u v ru rv hu hv hru hrv hx hy []).mono
    (KX.mul hX)

theorem HT.udv (hX : X.OK I) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (hcap : 6 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (u : ℤ) (v : ℕ) (ru rv : List Sym) (hv0 : 0 < v) (hru : TermOK ru)
    (hrv : TermOK rv) (hx : B x = intSyms u ++ ru) (hy : B y = natSyms v ++ rv)
    (hu : bitLen u.natAbs ≤ X.V) (hv : bitLen v ≤ X.V) :
    HT [] B (kdv I x y z) (Function.update B z (intSyms (divRoundRatInt u v) ++ B z)) X.U :=
  (HT.callI_upd I.dv [x, y, z] x hnd rfl hcap I.ldv B (.inl 2) _
    (hX.spec.dv u v ru rv _ hv0 hru hrv hx hy) []).mono (KX.dm hX hu hv)

theorem HT.upi (hE : I.SpecX X.C) (x z : Loc a b) (hnd : [x, z].Nodup) (hcap : 16 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (v : ℕ) (r : List Sym) (hr : TermOK r) (hB : B x = natSyms v ++ r) :
    HT [] B (kpi I x z)
      (Function.update B z (intSyms (IntMul.computablePiScaledWithCost v).1 ++ B z))
      (X.C * (v + 1) ^ 4) :=
  HT.piScaled hE.pi x I.lpi x z hnd hcap B v r hr hB []

theorem HT.upushNat (hX : X.OK I) (k : Loc a b) (c : ℕ) (B : Loc a b → List Sym)
    (hc : bitLen c ≤ X.V) :
    HT [] B (pushNat (σ := I.R) k c) (Function.update B k (natSyms c ++ B k)) X.U :=
  (HT.pushNat k c B []).mono
    (le_trans (Nat.le_mul_of_pos_left _ hX.spec.one) (KX.lin hX hc))

end URules

#assert_std_axioms KX.le_U KX.sq_le KX.eight_le KX.cst KX.lin KX.two KX.dm KX.k2 KX.mul HT.ucp
  HT.udr HT.uic HT.uad HT.us1 HT.usv HT.uai HT.ung HT.umu HT.udv HT.upi HT.upushNat

end WP.W7k3
