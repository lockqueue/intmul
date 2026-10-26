import WP.W7k2.Ops
import WP.W7k1.Isqrt

/-!
# WP.W7k1.PiOps — host-level rules for the remaining W3 operations, the isqrt kernel, and a
counted loop that needs its body only below the trip count

Same pattern as `WP.W7k2.Ops`: `Spec*` restates a contract body for one extracted instance
(`exists_inst`), `HT.*` calls the instance on chosen host stacks and gives the exact host update.

| rule | contract | host effect |
|---|---|---|
| `HT.addNat` | `W3_addNat` | `z += x + y` |
| `HT.subNat` | `W3_subNat` | `z += x − y` (`y ≤ x`) |
| `HT.shrVar` | `W3_shrVar` | `x := x / 2^c` |
| `HT.shrConst` | `W3_shrConst k` | `x := x / 2^k` |
| `HT.incNat` | `W3_incNat` | `x := x + 1` |
| `HT.isqrt` | `W7_isqrt` (proved, `WP.W7k1.Isqrt`) | `z += ⌊√x⌋` |

The counted loop `pcdLoop` (`while ctr ≠ 0 do (dec ctr; body)`, a `W3_isZeroNat` test before every
iteration, `W3_decNat` on the counter) and its rule `HT.cdLoopLt` are defined here (same program
as W7k2's `cdLoop`, whose module is not used); the body premise is needed only for `i < n` (the
state family of a loop that counts iterations need not make sense beyond the trip count).
-/

namespace WP.W7k1

open TMFw TMFw.Contracts WP.W7k2 Computability

/-! ## Instance specifications (contract bodies) -/

/-- Body of `W3_addNat`. -/
def SpecAddNat (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_subNat`. -/
def SpecSubNat (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry → b ≤ a →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- Body of `W3_shrVar`. -/
def SpecShrVar (I : Inst 2 4 Unit) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx)) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- Body of `W3_shrConst` at shift `k`. -/
def SpecShrConst (k : ℕ) (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a / 2 ^ k) ++ rx)) (fun _ => True)
      (C * (k + 1))

/-- Body of `W3_incNat`. -/
def SpecInc (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a + 1) ++ rx)) (fun _ => True)
      (C * (ones (encodeNat a) + 1))

/-- Body of `W7_isqrt`. -/
def SpecIsq (I : Inst 2 16 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (ra : List Sym) (S : Loc 2 I.m → List Sym), TermOK ra →
    S (.inl 0) = natSyms a ++ ra →
    Runs I.P S (Function.update S (.inl 1) (natSyms (Nat.sqrt a) ++ S (.inl 1))) (fun _ => True)
      (C * (bitLen a * bitLen a + 1))

/-- Body of `W3_isZeroNat`. -/
def SpecIsZ (I : Inst 1 4 Bool) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx → Runs I.P S S (fun r => I.obs r = decide (a = 0)) C

/-- Body of `W3_decNat`. -/
def SpecDecr (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms (a + 1) ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
      (C * (zerosLead (encodeNat (a + 1)) + 1))

/-! ## Host-level rules -/

variable {a b : ℕ} {σ : Type}

/-- `z += x + y`. -/
theorem HT.addNat {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecAddNat I C) (dflt : Loc a b)
    (l : Lens σ I.R) (sx sy sz : Loc a b) (hnd : [sx, sy, sz].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (x y : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : B sx = natSyms x ++ rx) (hy : B sy = natSyms y ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [sx, sy, sz] dflt l) (Function.update B sz (natSyms (x + y) ++ B sz))
      (C * (bitLen x + bitLen y + 1)) :=
  HT.callI_upd I [sx, sy, sz] dflt hnd rfl hcap l B (.inl 2) _ (hI x y rx ry _ hrx hry hx hy) ρ

/-- `z += x − y` for `y ≤ x`. -/
theorem HT.subNat {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecSubNat I C) (dflt : Loc a b)
    (l : Lens σ I.R) (sx sy sz : Loc a b) (hnd : [sx, sy, sz].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (x y : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hle : y ≤ x) (hx : B sx = natSyms x ++ rx) (hy : B sy = natSyms y ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [sx, sy, sz] dflt l) (Function.update B sz (natSyms (x - y) ++ B sz))
      (C * (bitLen x + bitLen y + 1)) :=
  HT.callI_upd I [sx, sy, sz] dflt hnd rfl hcap l B (.inl 2) _
    (hI x y rx ry _ hrx hry hle hx hy) ρ

/-- `x := x / 2^c`, in place. -/
theorem HT.shrVar {I : Inst 2 4 Unit} {C : ℕ} (hI : SpecShrVar I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s c : Loc a b) (hnd : [s, c].Nodup) (hcap : 4 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (x y : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hB : B s = natSyms x ++ rx) (hC : B c = natSyms y ++ ry)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s, c] dflt l) (Function.update B s (natSyms (x / 2 ^ y) ++ rx))
      (C * (min y (bitLen x) + bitLen y + 1)) :=
  HT.callI_upd I [s, c] dflt hnd rfl hcap l B (.inl 0) _ (hI x y rx ry _ hrx hry hB hC) ρ

/-- `x := x / 2^k`, in place. -/
theorem HT.shrConst {k : ℕ} {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecShrConst k I C)
    (dflt : Loc a b) (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b)
    (B : Loc a b → List Sym) (x : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hB : B s = natSyms x ++ rx) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s] dflt l) (Function.update B s (natSyms (x / 2 ^ k) ++ rx)) (C * (k + 1)) :=
  HT.callI_upd I [s] dflt (List.nodup_singleton s) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

/-- `x := x + 1`, in place. -/
theorem HT.incNat {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecInc I C) (dflt : Loc a b)
    (l : Lens σ I.R) (s : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (x : ℕ)
    (rx : List Sym) (hrx : TermOK rx) (hB : B s = natSyms x ++ rx)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [s] dflt l) (Function.update B s (natSyms (x + 1) ++ rx))
      (C * (ones (encodeNat x) + 1)) :=
  HT.callI_upd I [s] dflt (List.nodup_singleton s) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

/-- `z += ⌊√x⌋` (the `W7_isqrt` kernel). -/
theorem HT.isqrt {I : Inst 2 16 Unit} {C : ℕ} (hI : SpecIsq I C) (dflt : Loc a b)
    (l : Lens σ I.R) (sx sz : Loc a b) (hnd : [sx, sz].Nodup) (hcap : 16 + 2 ≤ a + b)
    (B : Loc a b → List Sym) (x : ℕ) (rx : List Sym) (hrx : TermOK rx)
    (hx : B sx = natSyms x ++ rx) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I [sx, sz] dflt l) (Function.update B sz (natSyms (Nat.sqrt x) ++ B sz))
      (C * (bitLen x * bitLen x + 1)) :=
  HT.callI_upd I [sx, sz] dflt hnd rfl hcap l B (.inl 1) _ (hI x rx _ hrx hx) ρ

/-! ## Counted loop with the body premise below the trip count -/

/-- **Test call**: stacks unchanged, the register property `Q` holds afterwards. -/
theorem callI_keep {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b))
    (dflt : Loc a b) (hnd : named.Nodup) (hn : named.length = n) (hcap : cap + n ≤ a + b)
    (l : Lens σ I.R) (B : Loc a b → List Sym) {Q : I.R → Prop} {T : ℕ}
    (h : Runs I.P (fun x => B (callMap dflt named x)) (fun x => B (callMap dflt named x)) Q T)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    Triple ρ (fun s => s.stk = B) (callI I named dflt l)
      (fun s => s.stk = B ∧ Q (l.get s.var)) T := by
  refine Triple.post (callI_spec I named dflt hnd hn hcap l B h ρ) (fun s hs => ?_)
  obtain ⟨ha, hb, hq⟩ := hs
  refine ⟨?_, hq⟩
  funext g
  by_cases hg : ∃ x : Loc n I.m, callMap dflt named x = g
  · obtain ⟨x, rfl⟩ := hg
    exact ha x
  · exact hb g (fun x hx => hg ⟨x, hx⟩)

/-- `while ctr ≠ 0 do (dec ctr; body)`, with a zero test before every iteration. -/
def pcdLoop (Iz : Inst 1 4 Bool) (Id : Inst 1 4 Unit) (lz : Lens σ Iz.R) (ld : Lens σ Id.R)
    (ctr dflt : Loc a b) (body : Prog (Loc a b) (fun _ => Sym) σ) :
    Prog (Loc a b) (fun _ => Sym) σ :=
  (callI Iz [ctr] dflt lz).seq
    (.loop (fun v => !(Iz.obs (lz.get v)))
      (((callI Id [ctr] dflt ld).seq body).seq (callI Iz [ctr] dflt lz)))

theorem pcdLoop_closed (Iz : Inst 1 4 Bool) (Id : Inst 1 4 Unit) (lz : Lens σ Iz.R)
    (ld : Lens σ Id.R) (ctr dflt : Loc a b) (body : Prog (Loc a b) (fun _ => Sym) σ)
    (hb : body.Closed) : (pcdLoop Iz Id lz ld ctr dflt body).Closed :=
  ⟨callI_closed _ _ _ _, ⟨⟨callI_closed _ _ _ _, hb⟩, callI_closed _ _ _ _⟩⟩

/-- **Counted loop rule**, body premise only for `i < n`. `St i` is the state with counter `i`
(`natSyms i ++ rc`); the body turns `St (i+1)` with the counter already decremented to `i` into
`St i`. -/
theorem HT.cdLoopLt {Iz : Inst 1 4 Bool} {Id : Inst 1 4 Unit} {Cz Cd : ℕ} (hz : SpecIsZ Iz Cz)
    (hd : SpecDecr Id Cd) (lz : Lens σ Iz.R) (ld : Lens σ Id.R) (ctr dflt : Loc a b)
    (hcap : 4 + 1 ≤ a + b) (rc : List Sym) (hrc : TermOK rc) (St : ℕ → Loc a b → List Sym)
    (hSt : ∀ i, St i ctr = natSyms i ++ rc) (body : Prog (Loc a b) (fun _ => Sym) σ)
    (cb : ℕ → ℕ) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) (n : ℕ)
    (hbody : ∀ i, i < n →
      HT ρ (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i) (cb i)) :
    HT ρ (St n) (pcdLoop Iz Id lz ld ctr dflt body) (St 0)
      (Cz + loopCost (fun i => Cd * (bitLen (i + 1) + 1) + cb i + Cz) n) := by
  have htest : ∀ i, Triple ρ (fun s => s.stk = St i) (callI Iz [ctr] dflt lz)
      (fun s => s.stk = St i ∧ Iz.obs (lz.get s.var) = decide (i = 0)) Cz := fun i =>
    callI_keep Iz [ctr] dflt (List.nodup_singleton _) rfl hcap lz (St i)
      (hz i rc _ hrc (hSt i)) ρ
  refine Triple.seq (R := fun s => n ≤ n ∧ s.stk = St n ∧ Iz.obs (lz.get s.var) = decide (n = 0))
    (Triple.conseq (htest n) (fun s hs => hs) (fun s hs => ⟨le_refl n, hs⟩) le_rfl) ?_
  have hloop := Triple.loop (ρ := ρ) (c := fun v => !(Iz.obs (lz.get v)))
    (p := ((callI Id [ctr] dflt ld).seq body).seq (callI Iz [ctr] dflt lz))
    (I := fun k s => k ≤ n ∧ s.stk = St k ∧ Iz.obs (lz.get s.var) = decide (k = 0))
    (B := fun i => Cd * (bitLen (i + 1) + 1) + cb i + Cz) ?_ ?_ ?_ n
  · exact Triple.post hloop (fun s hs => hs.2.1)
  · intro k
    by_cases hk : k < n
    · have hdec : HT ρ (St (k + 1)) (callI Id [ctr] dflt ld)
          (Function.update (St (k + 1)) ctr (natSyms k ++ rc))
          (Cd * (zerosLead (encodeNat (k + 1)) + 1)) :=
        HT.callI_upd Id [ctr] dflt (List.nodup_singleton _) rfl hcap ld (St (k + 1)) (.inl 0) _
          (hd k rc _ hrc (hSt (k + 1))) ρ
      have hzl : zerosLead (encodeNat (k + 1)) ≤ bitLen (k + 1) := zerosLead_le_length _
      have h1 := Triple.seq (Triple.seq hdec (hbody k hk)) (htest k)
      refine Triple.conseq h1 (fun s hs => hs.2.1) (fun s hs => ⟨by omega, hs⟩) ?_
      have : Cd * (zerosLead (encodeNat (k + 1)) + 1) ≤ Cd * (bitLen (k + 1) + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      show Cd * (zerosLead (encodeNat (k + 1)) + 1) + cb k + Cz ≤
        Cd * (bitLen (k + 1) + 1) + cb k + Cz
      omega
    · intro s hs
      exact absurd hs.1 (by omega)
  · intro k s hs
    have h : Iz.obs (lz.get s.var) = decide (k + 1 = 0) := hs.2.2
    show (!(Iz.obs (lz.get s.var))) = true
    simp [h]
  · intro s hs
    have h : Iz.obs (lz.get s.var) = decide (0 = 0) := hs.2.2
    show (!(Iz.obs (lz.get s.var))) = false
    simp [h]

#assert_std_axioms HT.addNat HT.subNat HT.shrVar HT.shrConst HT.incNat HT.isqrt callI_keep
  pcdLoop_closed HT.cdLoopLt

end WP.W7k1
