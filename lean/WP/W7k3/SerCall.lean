import WP.W7k3.Rules
import WP.W7k3.SeriesSpec

/-!
# WP.W7k3.SerCall — calling the series sub-kernel

* `SpecSer κ J C`: the body of `W7S_series` for one instance `J` (kind `κ`);
  `exists_ser` extracts one constant and one instance per kind from the contract.
* `HT.user`: the host rule (any host with `≥ 17` stacks, any register lens);
  `HT.usc`, `HT.uss`: the same for the bundle fields `sc`, `ss` (`ksc`, `kss`).
-/

namespace WP.W7k3

open TMFw TMFw.Contracts WP.W7k2

/-- The body of `W7S_series` for one instance `J` of kind `κ`. -/
def SpecSer (κ : SK) (J : Inst 5 12 Unit) (C : ℕ) : Prop :=
  κ.OK → ∀ (W : ℕ) (a0 c : ℤ) (d n : ℕ) (r0 r1 r2 r3 : List Sym) (S : Loc 5 J.m → List Sym),
    0 < d → 0 < n → IntMul.RecurrenceCallSitesWidthSound W a0 c d κ.f κ.g n →
    TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 →
    S (.inl 0) = intSyms a0 ++ r0 → S (.inl 1) = intSyms c ++ r1 →
    S (.inl 2) = natSyms d ++ r2 → S (.inl 3) = natSyms n ++ r3 →
    Runs J.P S (Function.update S (.inl 4)
        (intSyms (serState a0 c d κ.f κ.g n).2 ++ S (.inl 4))) (fun _ => True)
      (C * (n + 1) * (W + 2) ^ 2)

theorem SpecSer.mono {κ : SK} {J : Inst 5 12 Unit} {C C' : ℕ} (h : SpecSer κ J C)
    (hC : C ≤ C') : SpecSer κ J C' :=
  fun hκ W a0 c d n r0 r1 r2 r3 S h1 h2 h3 h4 h5 h6 h7 e0 e1 e2 e3 =>
    runs_mono (h hκ W a0 c d n r0 r1 r2 r3 S h1 h2 h3 h4 h5 h6 h7 e0 e1 e2 e3)
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hC))

/-- One constant, one instance per kind, from the contract. -/
theorem exists_ser {Mul : ℕ → ℕ} (h : W7S_series Mul) :
    ∃ C : ℕ, ∀ κ : SK, ∃ J : Inst 5 12 Unit, SpecSer κ J C :=
  exists_inst h

/-- **Call rule of the series sub-kernel.** -/
theorem HT.user {a b : ℕ} {σ : Type} {κ : SK} {J : Inst 5 12 Unit} {C : ℕ} (hJ : SpecSer κ J C)
    (hκ : κ.OK) (l : Lens σ J.R) (x0 x1 x2 x3 z : Loc a b) (hnd : [x0, x1, x2, x3, z].Nodup)
    (hcap : 12 + 5 ≤ a + b) (B : Loc a b → List Sym) (W : ℕ) (a0 c : ℤ) (d n : ℕ)
    (r0 r1 r2 r3 : List Sym) (hd : 0 < d) (hn : 0 < n)
    (hw : IntMul.RecurrenceCallSitesWidthSound W a0 c d κ.f κ.g n)
    (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3)
    (e0 : B x0 = intSyms a0 ++ r0) (e1 : B x1 = intSyms c ++ r1) (e2 : B x2 = natSyms d ++ r2)
    (e3 : B x3 = natSyms n ++ r3) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI J [x0, x1, x2, x3, z] x0 l)
      (Function.update B z (intSyms (serState a0 c d κ.f κ.g n).2 ++ B z))
      (C * (n + 1) * (W + 2) ^ 2) :=
  HT.callI_upd J [x0, x1, x2, x3, z] x0 hnd rfl hcap l B (.inl 4) _
    (hJ hκ W a0 c d n r0 r1 r2 r3 _ hd hn hw h0 h1 h2 h3 e0 e1 e2 e3) ρ

section Bundle

variable {a b : ℕ} {I : KI} {C : ℕ}

/-- The cos-kind series call of the bundle. -/
theorem HT.usc (hS : SpecSer SK.cos I.sc C) (x0 x1 x2 x3 z : Loc a b)
    (hnd : [x0, x1, x2, x3, z].Nodup) (hcap : 12 + 5 ≤ a + b) (B : Loc a b → List Sym) (W : ℕ)
    (a0 c : ℤ) (d n : ℕ) (r0 r1 r2 r3 : List Sym) (hd : 0 < d) (hn : 0 < n)
    (hw : IntMul.RecurrenceCallSitesWidthSound W a0 c d SK.cos.f SK.cos.g n)
    (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3)
    (e0 : B x0 = intSyms a0 ++ r0) (e1 : B x1 = intSyms c ++ r1) (e2 : B x2 = natSyms d ++ r2)
    (e3 : B x3 = natSyms n ++ r3) :
    HT [] B (ksc I x0 x1 x2 x3 z)
      (Function.update B z (intSyms (serState a0 c d SK.cos.f SK.cos.g n).2 ++ B z))
      (C * (n + 1) * (W + 2) ^ 2) :=
  HT.user hS SK.cos_OK I.lsc x0 x1 x2 x3 z hnd hcap B W a0 c d n r0 r1 r2 r3 hd hn hw h0 h1 h2 h3
    e0 e1 e2 e3 []

/-- The sin-kind series call of the bundle. -/
theorem HT.uss (hS : SpecSer SK.sin I.ss C) (x0 x1 x2 x3 z : Loc a b)
    (hnd : [x0, x1, x2, x3, z].Nodup) (hcap : 12 + 5 ≤ a + b) (B : Loc a b → List Sym) (W : ℕ)
    (a0 c : ℤ) (d n : ℕ) (r0 r1 r2 r3 : List Sym) (hd : 0 < d) (hn : 0 < n)
    (hw : IntMul.RecurrenceCallSitesWidthSound W a0 c d SK.sin.f SK.sin.g n)
    (h0 : TermOK r0) (h1 : TermOK r1) (h2 : TermOK r2) (h3 : TermOK r3)
    (e0 : B x0 = intSyms a0 ++ r0) (e1 : B x1 = intSyms c ++ r1) (e2 : B x2 = natSyms d ++ r2)
    (e3 : B x3 = natSyms n ++ r3) :
    HT [] B (kss I x0 x1 x2 x3 z)
      (Function.update B z (intSyms (serState a0 c d SK.sin.f SK.sin.g n).2 ++ B z))
      (C * (n + 1) * (W + 2) ^ 2) :=
  HT.user hS SK.sin_OK I.lss x0 x1 x2 x3 z hnd hcap B W a0 c d n r0 r1 r2 r3 hd hn hw h0 h1 h2 h3
    e0 e1 e2 e3 []

end Bundle

#assert_std_axioms SpecSer.mono exists_ser HT.user HT.usc HT.uss

end WP.W7k3
