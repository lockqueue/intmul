import WP.W7k2.Ops

/-!
# WP.W9dR.Ops — host-level rules for the W3 operations used by the round shift

`Spec*` restates one W3 contract body for an extracted instance (`exists_inst` produces it by
definitional unfolding); `HT.*` is the host-level rule (call the instance on chosen host stacks,
get the exact host update). Generic in the host `Loc a b`, as in `WP.W7k2.Ops`.
`HT.callI_upd_test`: an in-place update with a register observation, then a branch on it
(`splitSign`).
-/

namespace WP.W9dR

open TMFw TMFw.Contracts Computability WP.W7k2

/-! ## Instance specifications (contract bodies) -/

/-- Body of `W3_shrConst` at shift `k`. -/
def SpecShrConst (k : ℕ) (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a / 2 ^ k) ++ rx)) (fun _ => True)
      (C * (k + 1))

/-- Body of `W3_shrVar`. -/
def SpecShrVar (I : Inst 2 4 Unit) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx)) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- Body of `W3_natToInt`. -/
def SpecNatToInt (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (intSyms (a : ℤ) ++ rx)) (fun _ => True) C

/-- Body of `W3_addInt`. -/
def SpecAddInt (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- Body of `W3_splitSign`. -/
def SpecSplitSign (I : Inst 1 4 Bool) (C : ℕ) : Prop :=
  ∀ (z : ℤ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = intSyms z ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms z.natAbs ++ rx))
      (fun r => I.obs r = decide (z < 0)) C

/-- Body of `W3_incNat`. -/
def SpecInc (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a + 1) ++ rx)) (fun _ => True)
      (C * (ones (encodeNat a) + 1))

/-- Body of `W3_decNat`. -/
def SpecDec (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms (a + 1) ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
      (C * (zerosLead (encodeNat (a + 1)) + 1))

/-! ## Host-level rules -/

variable {a b : ℕ} {σ : Type}

theorem HT.shrConst {k : ℕ} {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecShrConst k I C)
    (dflt : Loc a b) (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b)
    (B : Loc a b → List Sym) (x : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hB : B s = natSyms x ++ rx) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s] dflt l) (Function.update B s (natSyms (x / 2 ^ k) ++ rx)) (C * (k + 1)) :=
  HT.callI_upd I [s] dflt (List.nodup_singleton s) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

theorem HT.shrVar {I : Inst 2 4 Unit} {C : ℕ} (hI : SpecShrVar I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s c : Loc a b) (hnd : [s, c].Nodup) (hcap : 4 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (x y : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hB : B s = natSyms x ++ rx) (hC : B c = natSyms y ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s, c] dflt l) (Function.update B s (natSyms (x / 2 ^ y) ++ rx))
      (C * (min y (bitLen x) + bitLen y + 1)) :=
  HT.callI_upd I [s, c] dflt hnd rfl hcap l B (.inl 0) _ (hI x y rx ry _ hrx hry hB hC) ρ

theorem HT.natToInt {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecNatToInt I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (x : ℕ)
    (rx : List Sym) (hrx : TermOK rx) (hB : B s = natSyms x ++ rx)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s] dflt l) (Function.update B s (intSyms (x : ℤ) ++ rx)) C :=
  HT.callI_upd I [s] dflt (List.nodup_singleton s) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

theorem HT.addInt {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecAddInt I C) (dflt : Loc a b)
    (l : Lens σ I.R) (x y d : Loc a b) (hnd : [x, y, d].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (u v : ℤ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = intSyms u ++ ru) (hy : B y = intSyms v ++ rv)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [x, y, d] dflt l) (Function.update B d (intSyms (u + v) ++ B d))
      (C * (bitLen u.natAbs + bitLen v.natAbs + 1)) :=
  HT.callI_upd I [x, y, d] dflt hnd rfl hcap l B (.inl 2) _ (hI u v ru rv _ hru hrv hx hy) ρ

theorem HT.incNat {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecInc I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (x : ℕ)
    (rx : List Sym) (hrx : TermOK rx) (hB : B s = natSyms x ++ rx)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s] dflt l) (Function.update B s (natSyms (x + 1) ++ rx))
      (C * (ones (encodeNat x) + 1)) :=
  HT.callI_upd I [s] dflt (List.nodup_singleton s) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

theorem HT.decNat {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecDec I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (x : ℕ)
    (rx : List Sym) (hrx : TermOK rx) (hB : B s = natSyms (x + 1) ++ rx)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s] dflt l) (Function.update B s (natSyms x ++ rx))
      (C * (zerosLead (encodeNat (x + 1)) + 1)) :=
  HT.callI_upd I [s] dflt (List.nodup_singleton s) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

/-- **In-place update with an observation, then a branch on it.** -/
theorem HT.callI_upd_test {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b))
    (dflt : Loc a b) (hnd : named.Nodup) (hn : named.length = n) (hcap : cap + n ≤ a + b)
    (l : Lens σ I.R) (B B' : Loc a b → List Sym) (k : Loc n I.m) (v : List Sym) (f : O → Bool)
    (o : O) {T T₁ T₂ : ℕ}
    (h : Runs I.P (fun x => B (callMap dflt named x))
      (Function.update (fun x => B (callMap dflt named x)) k v) (fun r => I.obs r = o) T)
    (p q : Prog (Loc a b) (fun _ => Sym) σ) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ))
    (hp : f o = true → HT ρ (Function.update B (callMap dflt named k) v) p B' T₁)
    (hq : f o = false → HT ρ (Function.update B (callMap dflt named k) v) q B' T₂) :
    HT ρ B ((callI I named dflt l).seq (.ite (fun s => f (I.obs (l.get s))) p q)) B'
      (T + (max T₁ T₂ + 1)) := by
  have hinj := callMap_injective (m := I.m) dflt named hnd hn (by have := I.hm; omega)
  have hc := callI_spec I named dflt hnd hn hcap l B h ρ
  have hc' : Triple ρ (fun s => s.stk = B) (callI I named dflt l)
      (fun s => s.stk = Function.update B (callMap dflt named k) v ∧ I.obs (l.get s.var) = o) T := by
    refine Triple.post hc (fun s hs => ?_)
    obtain ⟨ha, hb, hq'⟩ := hs
    refine ⟨?_, hq'⟩
    funext g
    by_cases hg : ∃ x : Loc n I.m, callMap dflt named x = g
    · obtain ⟨x, rfl⟩ := hg
      rw [ha x]
      by_cases hx : x = k
      · subst hx
        simp
      · rw [Function.update_of_ne hx, Function.update_of_ne (hinj.ne hx)]
    · push_neg at hg
      rw [hb g hg, Function.update_of_ne (fun e => hg k e.symm)]
  refine Triple.seq hc' (Triple.ite ?_ ?_)
  · rintro s ⟨⟨hsB, hso⟩, hc⟩
    have hfo : f o = true := by rw [← hso]; exact hc
    exact (hp hfo).mono (le_max_left _ _) s hsB
  · rintro s ⟨⟨hsB, hso⟩, hc⟩
    have hfo : f o = false := by rw [← hso]; exact hc
    exact (hq hfo).mono (le_max_right _ _) s hsB

/-- Split the sign, then branch on it. -/
theorem HT.splitSign_ite {I : Inst 1 4 Bool} {C : ℕ} (hI : SpecSplitSign I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b) (B B' : Loc a b → List Sym) (z : ℤ)
    (rz : List Sym) (hrz : TermOK rz) (hB : B s = intSyms z ++ rz)
    (p q : Prog (Loc a b) (fun _ => Sym) σ) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ))
    {T₁ T₂ : ℕ}
    (hp : z < 0 → HT ρ (Function.update B s (natSyms z.natAbs ++ rz)) p B' T₁)
    (hq : ¬ z < 0 → HT ρ (Function.update B s (natSyms z.natAbs ++ rz)) q B' T₂) :
    HT ρ B ((callI I [s] dflt l).seq (.ite (fun r => I.obs (l.get r)) p q)) B'
      (C + (max T₁ T₂ + 1)) :=
  HT.callI_upd_test I [s] dflt (List.nodup_singleton s) rfl hcap l B B' (.inl 0) _ id
    (decide (z < 0)) (hI z rz _ hrz hB) p q ρ (fun h => hp (of_decide_eq_true h))
    (fun h => hq (of_decide_eq_false h))

#assert_std_axioms HT.shrConst HT.shrVar HT.natToInt HT.addInt HT.incNat HT.decNat
  HT.callI_upd_test HT.splitSign_ite

end WP.W9dR
