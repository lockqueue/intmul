import WP.W0m.Kit
import WP.W0m.Macros
import IntMulTM.Framework.Lib.CompareEval
import Contracts.Machine.W3
import Contracts.Machine.W6a

/-!
# WP.W0m.Steps — `Runs` lemmas for each component used by the input stage

Every step has the form `Runs (component through a register lens) S S' Q T`, where `S'` is an
explicit `Function.update` of `S`.
* Library macros: `moveBits`, `copyBlock`, `inc`, `dec`, `zeroTest`, `pushC`, `skip`, `cmpNum`.
* New macros (`WP.W0m.Macros`): `dropNat`, `countBits`.
* Hypothesized W3/W6a contract instances (`AddSpec`, `DivSpec`), embedded along an injective stack
  map with `runs_embed_upd`/`runs_embed_upd2`.
-/

namespace WP.W0m

open Computability TMFw TMFw.Lib TMFw.Contracts

variable {K σ : Type} [DecidableEq K]

theorem natSyms_zero : natSyms 0 = [] := by
  rw [natSyms, encodeNat_zero]
  rfl

theorem length_encodeNat_eq_bitLen (a : ℕ) : (encodeNat a).length = bitLen a := rfl

section SymSteps

variable (l : Lens σ (Option Sym))

theorem rs_moveBits {src dst : K} (hne : src ≠ dst) (es : List Bool) (rest : List Sym)
    (S : K → List Sym) (hrest : TermOK rest) (hS : S src = es.map Sym.bit ++ rest) :
    Runs ((moveBits src dst).liftRegs l) S
      (Function.update (Function.update S src rest.tail) dst (es.reverse.map Sym.bit ++ S dst))
      (fun _ => True) (3 * es.length + 2) :=
  runs_liftMacro l (Qr := fun _ => True) fun r =>
    ⟨_, _, moveBits_eval hne [] r es rest S hrest hS, trivial, le_refl _⟩

theorem rs_copy {src dst tmp : K} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp) (a : ℕ)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest) (hS : S src = natSyms a ++ rest) :
    Runs ((copyBlock src dst tmp).liftRegs l) S (Function.update S dst (natSyms a ++ S dst))
      (fun _ => True) (7 * bitLen a + 7) :=
  runs_liftMacro l (Qr := fun _ => True) fun r =>
    ⟨_, _, copyBlock_eval h1 h2 h3 [] r (encodeNat a) rest S hrest hS, trivial, le_refl _⟩

theorem rs_drop {k : K} (a : ℕ) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = natSyms a ++ rest) :
    Runs ((dropNat k).liftRegs l) S (Function.update S k rest) (fun _ => True) (2 * bitLen a + 4) :=
  runs_liftMacro l (Qr := fun _ => True) fun r =>
    ⟨_, _, dropNat_eval [] r (encodeNat a) rest S hrest hS, trivial, le_refl _⟩

theorem rs_count0 {src t tm c ct : K} (hst : src ≠ t) (hstm : src ≠ tm) (httm : t ≠ tm)
    (htc : t ≠ c) (htct : t ≠ ct) (hcct : c ≠ ct) (a : ℕ) (rest rc : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hrc : TermOK rc) (hS : S src = natSyms a ++ rest) (hc : S c = rc) :
    Runs ((countBits src t tm c ct).liftRegs l) S
      (Function.update S c (natSyms (bitLen a) ++ rc)) (fun _ => True) (24 * bitLen a + 10) := by
  refine runs_liftMacro l (Qr := fun _ => True) fun r => ?_
  obtain ⟨cost, hcost, e⟩ := countBits_eval hst hstm httm htc htct hcct [] r (encodeNat a) rest 0
    rc S hrest hrc hS (by rw [hc, natSyms_zero, List.nil_append])
  rw [Nat.zero_add] at e
  have h17 := cntCost_zero_le (encodeNat a).length
  exact ⟨_, cost, e, trivial, by rw [← length_encodeNat_eq_bitLen]; omega⟩

theorem rs_inc {k t : K} (hkt : k ≠ t) (a : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms a ++ rest) :
    Runs ((inc k t).liftRegs l) S (Function.update S k (natSyms (a + 1) ++ rest))
      (fun _ => True) (6 * bitLen a + 9) := by
  refine runs_liftMacro l (Qr := fun _ => True) fun r => ?_
  obtain ⟨c, hc, e⟩ := inc_eval hkt [] r (encodeNat a) rest S hrest hS
  rw [← encodeNat_succ] at e
  have := ones_le_length (encodeNat a)
  exact ⟨_, c, e, trivial, by rw [← length_encodeNat_eq_bitLen]; omega⟩

theorem rs_dec {k t : K} (hkt : k ≠ t) (a : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms (a + 1) ++ rest) :
    Runs ((dec k t).liftRegs l) S (Function.update S k (natSyms a ++ rest))
      (fun _ => True) (6 * bitLen (a + 1) + 8) := by
  refine runs_liftMacro l (Qr := fun _ => True) fun r => ?_
  have := zerosLead_le_length (encodeNat (a + 1))
  exact ⟨_, _, dec_eval hkt [] r a rest S hrest hS, trivial, by
    rw [← length_encodeNat_eq_bitLen]; omega⟩

theorem rs_zeroTest {k : K} (a : ℕ) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = natSyms a ++ rest) :
    Runs ((zeroTest k).liftRegs l) S S (fun v => optIsBit (l.get v) = !decide (a = 0)) 1 := by
  refine runs_liftMacro l (Qr := fun r => optIsBit r = !decide (a = 0)) fun r => ?_
  obtain ⟨r', hr', e⟩ := zeroTest_eval [] r a rest S hrest hS
  exact ⟨r', 1, e, hr', le_refl _⟩

theorem rs_push (k : K) (x : Sym) (S : K → List Sym) :
    Runs ((pushC k x).liftRegs l) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  runs_liftMacro l (Qr := fun _ => True) fun r => ⟨r, 1, Eval.push _ _ _ _ _, trivial, le_refl _⟩

theorem rs_skip (S : K → List Sym) :
    Runs ((Lib.skip : SProg K).liftRegs l) S S (fun _ => True) 1 :=
  runs_liftMacro l (Qr := fun _ => True) fun r => ⟨r, 1, skip_eval [] ⟨r, S⟩, trivial, le_refl _⟩

end SymSteps

theorem rs_cmp (lc : Lens σ CReg) {k₁ k₂ t₁ t₂ : K} (h12 : k₁ ≠ k₂) (h1a : k₁ ≠ t₁)
    (h1b : k₁ ≠ t₂) (h2a : k₂ ≠ t₁) (h2b : k₂ ≠ t₂) (hab : t₁ ≠ t₂) (x y : ℕ) (rx ry : List Sym)
    (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hx : S k₁ = natSyms x ++ rx)
    (hy : S k₂ = natSyms y ++ ry) :
    Runs ((cmpNum k₁ k₂ t₁ t₂).liftRegs lc) S S (fun v => (lc.get v).2.2 = Lib.ordOf x y)
      (12 * min (bitLen x) (bitLen y) + 15) := by
  refine runs_liftMacro lc (Qr := fun v => v.2.2 = Lib.ordOf x y) fun r => ?_
  refine ⟨_, _, cmpNum_eval h12 h1a h1b h2a h2b hab r (encodeNat x) (encodeNat y) rx ry S hrx hry
    hx hy, ?_, le_refl _⟩
  show cmpAll .eq (encodeNat x) (encodeNat y) = ordOf x y
  rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat x) (normBits_encodeNat y), bitsVal_encodeNat,
    bitsVal_encodeNat]

/-! ## Hypothesized contract instances -/

/-- The behaviour `W3_addNat` promises for its program (named stacks `0, 1` → `2`). -/
def AddSpec {m : ℕ} {R : Type} (P : Prog (Loc 3 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs P S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- The behaviour `W6a_divModNat` promises for its program (named stacks `0, 1` → `2, 3`). -/
def DivSpec {m : ℕ} {R : Type} (P : Prog (Loc 4 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (ra rb : List Sym) (S : Loc 4 m → List Sym), 0 < b → TermOK ra → TermOK rb →
    S (.inl 0) = natSyms a ++ ra → S (.inl 1) = natSyms b ++ rb →
    Runs P S (Function.update (Function.update S (.inl 2) (natSyms (a / b) ++ S (.inl 2)))
        (.inl 3) (natSyms (a % b) ++ S (.inl 3))) (fun _ => True)
      (C * (bitLen a * bitLen b + bitLen a + bitLen b + 1))

theorem addSpec_of_W3 (h : W3_addNat) :
    ∃ (C m : ℕ) (R : Type) (P : Prog (Loc 3 m) (fun _ => Sym) R),
      m ≤ 4 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧ AddSpec P C := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨m, R, _, P, hm, hfin, hne, hcl, hs⟩ := hC ()
  exact ⟨C, m, R, P, hm, hfin, hne, hcl, hs⟩

theorem divSpec_of_W6a (h : W6a_divModNat) :
    ∃ (C m : ℕ) (R : Type) (P : Prog (Loc 4 m) (fun _ => Sym) R),
      m ≤ 6 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧ DivSpec P C := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨m, R, _, P, hm, hfin, hne, hcl, hs⟩ := hC ()
  exact ⟨C, m, R, P, hm, hfin, hne, hcl, hs⟩

/-- Call-site stack map: named stacks via `named`, scratch stacks via `scr`. -/
def embL {n m : ℕ} (named : Fin n → K) (scr : Fin m → K) : Loc n m → K := Sum.elim named scr

omit [DecidableEq K] in
theorem embL_inj {n m : ℕ} {named : Fin n → K} {scr : Fin m → K}
    (h1 : Function.Injective named) (h2 : Function.Injective scr) (h3 : ∀ i j, named i ≠ scr j) :
    Function.Injective (embL named scr) := by
  rintro (i | i) (j | j) h
  · exact congrArg Sum.inl (h1 h)
  · exact absurd h (h3 i j)
  · exact absurd h.symm (h3 j i)
  · exact congrArg Sum.inr (h2 h)

theorem rs_add {m : ℕ} {R : Type} {P : Prog (Loc 3 m) (fun _ => Sym) R} {C : ℕ}
    (hP : AddSpec P C) (l : Lens σ R) {named : Fin 3 → K} {scr : Fin m → K}
    (hinj : Function.Injective (embL named scr)) (a b : ℕ) (rx ry : List Sym) (S : K → List Sym)
    (hrx : TermOK rx) (hry : TermOK ry) (hx : S (named 0) = natSyms a ++ rx)
    (hy : S (named 1) = natSyms b ++ ry) :
    Runs ((P.mapStk (embL named scr)).liftRegs l) S
      (Function.update S (named 2) (natSyms (a + b) ++ S (named 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1)) :=
  runs_liftRegs l (runs_embed_upd hinj S (.inl 2) _ (hP a b rx ry _ hrx hry hx hy))

theorem rs_div {m : ℕ} {R : Type} {P : Prog (Loc 4 m) (fun _ => Sym) R} {C : ℕ}
    (hP : DivSpec P C) (l : Lens σ R) {named : Fin 4 → K} {scr : Fin m → K}
    (hinj : Function.Injective (embL named scr)) (a b : ℕ) (ra rb : List Sym) (S : K → List Sym)
    (hb : 0 < b) (hra : TermOK ra) (hrb : TermOK rb) (hx : S (named 0) = natSyms a ++ ra)
    (hy : S (named 1) = natSyms b ++ rb) :
    Runs ((P.mapStk (embL named scr)).liftRegs l) S
      (Function.update (Function.update S (named 2) (natSyms (a / b) ++ S (named 2))) (named 3)
        (natSyms (a % b) ++ S (named 3))) (fun _ => True)
      (C * (bitLen a * bitLen b + bitLen a + bitLen b + 1)) :=
  runs_liftRegs l (runs_embed_upd2 hinj S (.inl 2) (.inl 3) _ _ (hP a b ra rb _ hb hra hrb hx hy))

#assert_std_axioms natSyms_zero rs_moveBits rs_copy rs_drop rs_count0 rs_inc rs_dec rs_zeroTest
  rs_push rs_skip rs_cmp addSpec_of_W3 divSpec_of_W6a embL_inj rs_add rs_div

end WP.W0m
