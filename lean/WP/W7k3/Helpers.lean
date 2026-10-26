import WP.W7k3.Rules

/-!
# WP.W7k3.Helpers — small helper programs and the uniform countdown loop

| program | effect (top of stack first) | cost |
|---|---|---|
| `kdrI x` | drop the signed number on `x` | `2U` |
| `kmvI x y` | move the signed number on `x` onto `y` | `3U` |
| `kcpI x y` | copy the signed number on `x` onto `y` | `2U` |
| `kshlI x c` | `z ↦ z·2^k` (signed, `k` on `c`) | `2U` |
| `kincN x m` | `v ↦ v + m` | `m·U + 1` |
| `kloop ctr body` | `while ctr ≠ 0 do (dec ctr; body)` | `HT.uloop` |
-/

namespace WP.W7k3

open TMFw TMFw.Contracts WP.W7k2

/-! ## Programs -/

section Programs

variable {a b : ℕ} (I : KI)

/-- Drop the signed number on top of `x`. -/
def kdrI (x : Loc a b) : KP a b I := (popS x).seq (kdr I x)

/-- Move the signed number on top of `x` onto `y`. -/
def kmvI (x y : Loc a b) : KP a b I := moveInt I.cp I.dr I.lS I.lcp I.ldr x y x

/-- Copy the signed number on top of `x` onto `y`. -/
def kcpI (x y : Loc a b) : KP a b I :=
  (popR' I.lS x).seq (.ite (fun v => decide (I.lS.get v = some Sym.neg))
    ((kcp I x y).seq ((pushS y .neg).seq (pushS x .neg)))
    ((kcp I x y).seq ((pushS y .pos).seq (pushS x .pos))))

/-- Shift the signed number on top of `x` left by the counter on `c`. -/
def kshlI (x c : Loc a b) : KP a b I :=
  (popR' I.lS x).seq (.ite (fun v => decide (I.lS.get v = some Sym.neg))
    ((ksv I x c).seq (pushS x .neg)) ((ksv I x c).seq (pushS x .pos)))

/-- `m` increments of the number on `x`. -/
def kincN (x : Loc a b) : ℕ → KP a b I
  | 0 => .load id
  | m + 1 => (kincN x m).seq (kic I x)

/-- `while ctr ≠ 0 do (dec ctr; body)`. -/
def kloop (ctr : Loc a b) (body : KP a b I) : KP a b I :=
  cdLoop I.iz I.dc I.liz I.ldc ctr ctr body

theorem kdrI_closed (x : Loc a b) : (kdrI I x).Closed := ⟨trivial, callI_closed _ _ _ _⟩

theorem kmvI_closed (x y : Loc a b) : (kmvI I x y).Closed := moveInt_closed _ _ _ _ _ _ _ _

theorem kcpI_closed (x y : Loc a b) : (kcpI I x y).Closed :=
  ⟨trivial, ⟨callI_closed _ _ _ _, trivial, trivial⟩, ⟨callI_closed _ _ _ _, trivial, trivial⟩⟩

theorem kshlI_closed (x c : Loc a b) : (kshlI I x c).Closed :=
  ⟨trivial, ⟨callI_closed _ _ _ _, trivial⟩, ⟨callI_closed _ _ _ _, trivial⟩⟩

theorem kincN_closed (x : Loc a b) : ∀ m, (kincN I x m).Closed
  | 0 => trivial
  | m + 1 => ⟨kincN_closed x m, callI_closed _ _ _ _⟩

theorem kloop_closed (ctr : Loc a b) (body : KP a b I) (hb : body.Closed) :
    (kloop I ctr body).Closed := cdLoop_closed _ _ _ _ _ _ _ hb

end Programs

/-! ## Encoding facts -/

theorem intSyms_mul_two_pow (z : ℤ) (k : ℕ) :
    intSyms (z * ((2 ^ k : ℕ) : ℤ)) = sgnSym z :: natSyms (z.natAbs * 2 ^ k) := by
  have hp : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by positivity
  unfold intSyms sgnSym
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  congr 1
  by_cases hz : z < 0
  · rw [if_pos hz, if_pos (Int.mul_neg_of_neg_of_pos hz hp)]
  · rw [if_neg hz, if_neg (not_lt.mpr (Int.mul_nonneg (by omega) hp.le))]

theorem intSyms_zero_append (l : List Sym) : intSyms 0 ++ l = Sym.pos :: l := by
  simp [intSyms, sgnSym, natSyms, encodeNat_zero]

/-! ## Rules -/

section HRules

variable {a b : ℕ} {X : KX} {I : KI}

theorem HT.udrI (hX : X.OK I) (x : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym)
    (z : ℤ) (r : List Sym) (hr : TermOK r) (hB : B x = intSyms z ++ r)
    (hz : bitLen z.natAbs ≤ X.V) : HT [] B (kdrI I x) (Function.update B x r) (2 * X.U) := by
  have hBx : B x = sgnSym z :: (natSyms z.natAbs ++ r) := by rw [hB]; rfl
  refine (HT.seq (HT.popS x B _ _ hBx []) (HT.udr hX x hcap _ z.natAbs r hr (by simp) hz)).of_eq
    (by rw [Function.update_idem]) ?_
  have := KX.eight_le hX
  omega

theorem HT.umvI (hX : X.OK I) (x y : Loc a b) (hxy : x ≠ y) (hcap : 4 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (z : ℤ) (r : List Sym) (hr : TermOK r) (hB : B x = intSyms z ++ r)
    (hz : bitLen z.natAbs ≤ X.V) :
    HT [] B (kmvI I x y) (Function.update (Function.update B y (intSyms z ++ B y)) x r)
      (3 * X.U) :=
  (HT.moveInt hX.spec.cp hX.spec.dr I.lS I.lcp I.ldr x y x hxy hcap B z r hr hB []).mono (by
    have h1 := KX.lin hX hz
    have h2 := KX.eight_le hX
    omega)

theorem HT.ucpI (hX : X.OK I) (x y : Loc a b) (hxy : x ≠ y) (hcap : 4 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (z : ℤ) (r : List Sym) (hr : TermOK r) (hB : B x = intSyms z ++ r)
    (hz : bitLen z.natAbs ≤ X.V) :
    HT [] B (kcpI I x y) (Function.update B y (intSyms z ++ B y)) (2 * X.U) := by
  have hBx : B x = sgnSym z :: (natSyms z.natAbs ++ r) := by rw [hB]; rfl
  have hnd : [x, y].Nodup := by simp [hxy]
  have hbr : ∀ s : Sym, sgnSym z = s →
      HT [] (Function.update B x (natSyms z.natAbs ++ r))
        ((kcp I x y).seq ((pushS y s).seq (pushS x s)))
        (Function.update B y (intSyms z ++ B y)) (X.U + (1 + 1)) := by
    intro s hs
    refine (HT.seq (HT.ucp hX x y hnd hcap _ z.natAbs r hr (by simp) hz)
      (HT.seq (HT.pushS y s _ []) (HT.pushS x s _ []))).of_eq ?_ le_rfl
    funext g
    by_cases hgy : g = y
    · subst hgy
      simp [Function.update_apply, Ne.symm hxy, intSyms, hs]
    · by_cases hgx : g = x
      · subst hgx
        simp [Function.update_apply, hxy, hBx, hs]
      · simp [Function.update_apply, hgx, hgy]
  refine (HT.popBranch I.lS x B _ (sgnSym z) _ hBx (fun o => decide (o = some Sym.neg)) _ _ []
    (fun h => hbr .neg (by simpa using h))
    (fun h => hbr .pos (sgnSym_eq_pos_of_ne (by simpa using h)))).mono ?_
  have := KX.eight_le hX
  simp only [max_self]
  omega

theorem HT.ushlI (hX : X.OK I) (hE : I.SpecX X.C) (x c : Loc a b) (hxc : x ≠ c)
    (hcap : 4 + 2 ≤ a + b) (B : Loc a b → List Sym) (z : ℤ) (k : ℕ) (rx rc : List Sym)
    (hrx : TermOK rx) (hrc : TermOK rc) (hB : B x = intSyms z ++ rx) (hC : B c = natSyms k ++ rc)
    (hk : k ≤ X.V) :
    HT [] B (kshlI I x c) (Function.update B x (intSyms (z * ((2 ^ k : ℕ) : ℤ)) ++ rx))
      (2 * X.U) := by
  have hBx : B x = sgnSym z :: (natSyms z.natAbs ++ rx) := by rw [hB]; rfl
  have hnd : [x, c].Nodup := by simp [hxc]
  have hbr : ∀ s : Sym, sgnSym z = s →
      HT [] (Function.update B x (natSyms z.natAbs ++ rx)) ((ksv I x c).seq (pushS x s))
        (Function.update B x (intSyms (z * ((2 ^ k : ℕ) : ℤ)) ++ rx)) (X.U + 1) := by
    intro s hs
    refine (HT.seq (HT.usv hX hE x c hnd hcap _ z.natAbs k rx rc hrx hrc (by simp)
      (by simp [Ne.symm hxc, hC]) hk)
      (HT.pushS x s _ [])).of_eq ?_ le_rfl
    rw [Function.update_self, Function.update_idem, Function.update_idem, intSyms_mul_two_pow, hs]
    rfl
  refine (HT.popBranch I.lS x B _ (sgnSym z) _ hBx (fun o => decide (o = some Sym.neg)) _ _ []
    (fun h => hbr .neg (by simpa using h))
    (fun h => hbr .pos (sgnSym_eq_pos_of_ne (by simpa using h)))).mono ?_
  have := KX.eight_le hX
  simp only [max_self]
  omega

theorem HT.uincN (hX : X.OK I) (x : Loc a b) (hcap : 4 + 1 ≤ a + b) (r : List Sym)
    (hr : TermOK r) : ∀ (m v : ℕ) (B : Loc a b → List Sym), B x = natSyms v ++ r →
      bitLen (v + m) ≤ X.V →
      HT [] B (kincN I x m) (Function.update B x (natSyms (v + m) ++ r)) (m * X.U + 1)
  | 0, v, B, hB, _ => by
    rintro ⟨w, S⟩ hS
    change S = B at hS
    subst hS
    refine ⟨⟨w, S⟩, 1, Eval.load [] id w S, ?_, by simp⟩
    show S = Function.update S x (natSyms (v + 0) ++ r)
    rw [Nat.add_zero, ← hB, Function.update_eq_self]
  | m + 1, v, B, hB, hw => by
    have hm : bitLen (v + m) ≤ X.V := le_trans (bitLen_mono (by omega)) hw
    refine (HT.seq (HT.uincN hX x hcap r hr m v B hB hm)
      (HT.uic hX x hcap _ (v + m) r hr (by simp) hm)).of_eq ?_ ?_
    · rw [Function.update_idem]
      rfl
    · rw [Nat.succ_mul]
      omega

/-- **Countdown loop, uniform cost.** `St i` is the state with counter `i`; the body turns
`St (i+1)` with the counter already decremented to `i` into `St i`, for `i < n`. -/
theorem HT.uloop (hX : X.OK I) (ctr : Loc a b) (hcap : 4 + 1 ≤ a + b) (rc : List Sym)
    (hrc : TermOK rc) (St : ℕ → Loc a b → List Sym) (hSt : ∀ i, St i ctr = natSyms i ++ rc)
    (body : KP a b I) (n cb : ℕ) (hn : bitLen n ≤ X.V)
    (hbody : ∀ i < n, HT [] (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i) cb) :
    HT [] (St n) (kloop I ctr body) (St 0) (n * (cb + 2 * X.U + 1) + X.U + 1) := by
  have htest : ∀ i, Triple [] (fun s => s.stk = St i) (callI I.iz [ctr] ctr I.liz)
      (fun s => s.stk = St i ∧ I.iz.obs (I.liz.get s.var) = decide (i = 0)) X.C := fun i =>
    callI_same I.iz [ctr] ctr (List.nodup_singleton _) rfl hcap I.liz (St i)
      (hX.spec.iz i rc _ hrc (hSt i)) []
  have hloop := Triple.loop (ρ := []) (c := fun v => !(I.iz.obs (I.liz.get v)))
    (p := ((callI I.dc [ctr] ctr I.ldc).seq body).seq (callI I.iz [ctr] ctr I.liz))
    (I := fun k s => k ≤ n ∧ s.stk = St k ∧ I.iz.obs (I.liz.get s.var) = decide (k = 0))
    (B := fun _ => X.U + cb + X.C) ?_ ?_ ?_ n
  · refine (Triple.seq (htest n) (Triple.conseq hloop (fun s hs => ⟨le_rfl, hs⟩)
      (fun s hs => hs.2.1) le_rfl)).cost_mono ?_
    rw [loopCost_const]
    have h1 := KX.cst hX
    have h2 : n * (X.U + cb + X.C + 1) ≤ n * (cb + 2 * X.U + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · intro k
    by_cases hk : k + 1 ≤ n
    · have hdec : HT [] (St (k + 1)) (callI I.dc [ctr] ctr I.ldc)
          (Function.update (St (k + 1)) ctr (natSyms k ++ rc))
          (X.C * (zerosLead (Computability.encodeNat (k + 1)) + 1)) :=
        HT.callI_upd I.dc [ctr] ctr (List.nodup_singleton _) rfl hcap I.ldc (St (k + 1))
          (.inl 0) _ (hX.spec.dc k rc _ hrc (hSt (k + 1))) []
      have hzl : zerosLead (Computability.encodeNat (k + 1)) ≤ bitLen (k + 1) :=
        zerosLead_le_length _
      have hb1 : bitLen (k + 1) ≤ X.V := le_trans (bitLen_mono hk) hn
      have hdU : X.C * (zerosLead (Computability.encodeNat (k + 1)) + 1) ≤ X.U :=
        le_trans (Nat.mul_le_mul_left _ (by omega)) (KX.lin hX hb1)
      have h1 := Triple.seq (Triple.seq hdec (hbody k (by omega))) (htest k)
      refine Triple.conseq h1 (fun s hs => hs.2.1) (fun s hs => ⟨by omega, hs⟩) ?_
      show _ ≤ X.U + cb + X.C
      omega
    · intro s hs
      exact absurd hs.1 hk
  · intro k s hs
    simp [hs.2.2]
  · intro s hs
    simp [hs.2.2]

end HRules

#assert_std_axioms kdrI_closed kmvI_closed kcpI_closed kshlI_closed kincN_closed kloop_closed
  intSyms_mul_two_pow intSyms_zero_append HT.udrI HT.umvI HT.ucpI HT.ushlI HT.uincN HT.uloop

end WP.W7k3
