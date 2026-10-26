import WP.W9c.Tool2
import WP.W9c.Iface
import WP.W9c.PureUnpack

/-!
# WP.W9c.UnpackDefs — definitions for `W9c_unpack` (streamed balanced digits)

Host `UL = Loc 4 8`. Named: `.inl 0` X (signed product, then the remaining magnitude), `.inl 1` K,
`.inl 2` N (counters, restored), `.inl 3` D (output). Scratch, each on a `mark` floor:
`.inr 0` CN (loop counter), `.inr 1` T (digits so far, reversed), `.inr 2` H (`2^(k-1)`),
`.inr 3` LO (slot, then digit magnitude), `.inr 4` DG (temporary), `.inr 5` CY (carry `0`/`1`).

One digit (`digitP`): `splitAt X K LO`; if CY holds `1`, pop it and increment LO (`t`); compare `t`
with H; on a carry LO := `H - (t - H) = 2^k - t` and CY := `1`; push the sign onto T, move LO's
bits onto T, push `sep`. At the end T is reversed onto D. All helpers live in `WP.W9c.Unp`.
-/

namespace WP.W9c.Unp

open TMFw TMFw.Contracts WP.W7k2 WP.W9c Computability

/-! ## Pure helpers -/

/-- Magnitude and carry after `j` streamed digits. -/
def udSt (neg : Bool) (k : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, M, c => (M, c)
  | j + 1, M, c => udSt neg k j (M / 2 ^ k) (udStep neg k M c).2

theorem udSt_succ (neg : Bool) (k : ℕ) : ∀ (j M c : ℕ),
    udSt neg k (j + 1) M c =
      ((udSt neg k j M c).1 / 2 ^ k, (udStep neg k (udSt neg k j M c).1 (udSt neg k j M c).2).2)
  | 0, _, _ => rfl
  | j + 1, M, c => udSt_succ neg k j (M / 2 ^ k) (udStep neg k M c).2

theorem udig_snoc (neg : Bool) (k : ℕ) : ∀ (j M c : ℕ),
    udig neg k (j + 1) M c =
      udig neg k j M c ++ [(udStep neg k (udSt neg k j M c).1 (udSt neg k j M c).2).1]
  | 0, _, _ => rfl
  | j + 1, M, c =>
    congrArg ((udStep neg k M c).1 :: ·) (udig_snoc neg k j (M / 2 ^ k) (udStep neg k M c).2)

theorem udig_length (neg : Bool) (k : ℕ) : ∀ (n M c : ℕ), (udig neg k n M c).length = n
  | 0, _, _ => rfl
  | n + 1, M, c => congrArg (· + 1) (udig_length neg k n (M / 2 ^ k) (udStep neg k M c).2)

theorem udSt_carry_le (neg : Bool) (k : ℕ) (hk : 1 ≤ k) :
    ∀ (j M c : ℕ), c ≤ 1 → (udSt neg k j M c).2 ≤ 1
  | 0, _, _, hc => hc
  | j + 1, M, c, hc =>
    udSt_carry_le neg k hk j (M / 2 ^ k) (udStep neg k M c).2 (udStep_carry_le neg k M c hk hc)

theorem udSt_fst_le (neg : Bool) (k : ℕ) : ∀ (j M c : ℕ), (udSt neg k j M c).1 ≤ M
  | 0, _, _ => le_rfl
  | j + 1, M, c =>
    le_trans (udSt_fst_le neg k j (M / 2 ^ k) (udStep neg k M c).2) (Nat.div_le_self M _)

theorem two_pow_eq' {k : ℕ} (hk : 1 ≤ k) : 2 ^ k = 2 * 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, Nat.mul_comm]

/-- Every digit has at most `k` bits. -/
theorem bitLen_udig_le (neg : Bool) (k : ℕ) (hk : 1 ≤ k) (n M c : ℕ) (hc : c ≤ 1) :
    ∀ d ∈ udig neg k n M c, bitLen d.natAbs ≤ k := fun d hd => by
  apply bitLen_le_of_lt
  have h1 := udig_natAbs_le neg k hk n M c hc d hd
  have h2 := two_pow_eq' hk
  have h3 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  omega

theorem bitLen_udStep_le (neg : Bool) (k M c : ℕ) (hk : 1 ≤ k) (hc : c ≤ 1) :
    bitLen (udStep neg k M c).1.natAbs ≤ k :=
  bitLen_udig_le neg k hk 1 M c hc _ (by simp [udig])

/-- `udStep` as a function of `t = M % 2^k + c`. -/
def udT (neg : Bool) (k t : ℕ) : ℤ × ℕ :=
  if neg then (if 2 ^ (k - 1) < t then (((2 ^ k - t : ℕ) : ℤ), 1) else (-(t : ℤ), 0))
  else (if 2 ^ (k - 1) ≤ t then ((t : ℤ) - ((2 ^ k : ℕ) : ℤ), 1) else ((t : ℤ), 0))

theorem udStep_eq_udT (neg : Bool) (k M c : ℕ) : udStep neg k M c = udT neg k (M % 2 ^ k + c) :=
  rfl

theorem udT_false (k t : ℕ) : udT false k t =
    if 2 ^ (k - 1) ≤ t then ((t : ℤ) - ((2 ^ k : ℕ) : ℤ), 1) else ((t : ℤ), 0) := rfl

theorem udT_true (k t : ℕ) : udT true k t =
    if 2 ^ (k - 1) < t then (((2 ^ k - t : ℕ) : ℤ), 1) else (-(t : ℤ), 0) := rfl

theorem lsy_cons (v : ℤ) (vs : List ℤ) :
    listSyms (v :: vs) = intSyms v ++ Sym.sep :: listSyms vs := by
  simp [listSyms]

theorem lsy_snoc (vs : List ℤ) (v : ℤ) :
    listSyms (vs ++ [v]) = listSyms vs ++ (intSyms v ++ [Sym.sep]) := by
  simp [listSyms]

theorem rev_digit (z : ℤ) (l : List Sym) :
    (intSyms z ++ [Sym.sep]).reverse ++ l =
      Sym.sep :: ((natSyms z.natAbs).reverse ++ sgnSym z :: l) := by
  simp [intSyms]

theorem T_step (vs : List ℤ) (v : ℤ) (l : List Sym) :
    (listSyms (vs ++ [v])).reverse ++ l =
      Sym.sep :: ((natSyms v.natAbs).reverse ++ sgnSym v :: ((listSyms vs).reverse ++ l)) := by
  rw [lsy_snoc, List.reverse_append, List.append_assoc, rev_digit]

theorem lsy_ne_mark (vs : List ℤ) : ∀ y ∈ listSyms vs, y ≠ Sym.mark := by
  intro y hy
  simp only [listSyms, List.mem_flatMap, List.mem_append, List.mem_singleton] at hy
  obtain ⟨v, -, hv | rfl⟩ := hy
  · simp only [intSyms, natSyms, List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | ⟨b, -, rfl⟩
    · unfold sgnSym; split <;> decide
    · intro h; cases h
  · decide

theorem length_lsy_le (k : ℕ) : ∀ ds : List ℤ, (∀ d ∈ ds, bitLen d.natAbs ≤ k) →
    (listSyms ds).length ≤ ds.length * (k + 2)
  | [], _ => by simp [listSyms]
  | d :: ds, h => by
    have h1 := h d (List.mem_cons_self ..)
    have h2 := length_lsy_le k ds (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [lsy_cons]
    simp only [List.length_append, List.length_cons, intSyms, length_natSyms]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem isBit_natSyms (n : ℕ) : ∀ y ∈ natSyms n, Sym.isBit y = true := by
  intro y hy
  simp only [natSyms, List.mem_map] at hy
  obtain ⟨b, -, rfl⟩ := hy
  rfl

theorem natSyms_zero_U : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]

theorem natSyms_one_U : natSyms 1 = [Sym.bit true] := by
  have h : encodeNat 1 = [true] := by simpa [encodeNat_zero] using encodeNat_add_add_one 0
  simp [natSyms, h]

/-! ## Contract bodies (verbatim from `Contracts/Machine/W3.lean`) and host rules -/

/-- Body of `W3_splitAt`. -/
def SpecSplitU (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs I.P S (Function.update (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx))
        (.inl 2) (natSyms (a % 2 ^ c) ++ S (.inl 2))) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- Body of `W3_incNat`. -/
def SpecIncU (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms (a + 1) ++ rx)) (fun _ => True)
      (C * (ones (encodeNat a) + 1))

/-- Body of `W3_subNat`. -/
def SpecSubU (I : Inst 3 4 Unit) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 I.m → List Sym), TermOK rx → TermOK ry → b ≤ a →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs I.P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

section rules

variable {a b : ℕ} {σ : Type}

theorem ht_skip (B : Loc a b → List Sym) (ρ : List (HP a b σ)) :
    HT ρ B (Lib.skip : HP a b σ) B 1 := by
  rintro ⟨v, S⟩ hS
  exact ⟨⟨v, S⟩, 1, Lib.skip_eval ρ _, hS, le_rfl⟩

theorem ht_split {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecSplitU I C) (dflt : Loc a b)
    (l : Lens σ I.R) (x c y : Loc a b) (hnd : [x, c, y].Nodup) (hcap : 4 + 3 ≤ a + b)
    (B : Loc a b → List Sym) (u w : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hc : B c = natSyms w ++ rv) (ρ : List (HP a b σ)) :
    HT ρ B (callI I [x, c, y] dflt l)
      (Function.update (Function.update B x (natSyms (u / 2 ^ w) ++ ru)) y
        (natSyms (u % 2 ^ w) ++ B y))
      (C * (min w (bitLen u) + bitLen w + 1)) :=
  HT.callI_upd2 I [x, c, y] dflt hnd rfl hcap l B (.inl 0) (.inl 2) _ _
    (hI u w ru rv _ hru hrv hx hc) ρ

theorem ht_inc {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecIncU I C) (dflt : Loc a b) (l : Lens σ I.R)
    (k : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (x : ℕ) (rx : List Sym)
    (hrx : TermOK rx) (hB : B k = natSyms x ++ rx) (ρ : List (HP a b σ)) :
    HT ρ B (callI I [k] dflt l) (Function.update B k (natSyms (x + 1) ++ rx))
      (C * (ones (encodeNat x) + 1)) :=
  HT.callI_upd I [k] dflt (List.nodup_singleton k) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

theorem ht_sub {I : Inst 3 4 Unit} {C : ℕ} (hI : SpecSubU I C) (dflt : Loc a b) (l : Lens σ I.R)
    (x y z : Loc a b) (hnd : [x, y, z].Nodup) (hcap : 4 + 3 ≤ a + b) (B : Loc a b → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv) (hle : v ≤ u)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (ρ : List (HP a b σ)) :
    HT ρ B (callI I [x, y, z] dflt l) (Function.update B z (natSyms (u - v) ++ B z))
      (C * (bitLen u + bitLen v + 1)) :=
  HT.callI_upd I [x, y, z] dflt hnd rfl hcap l B (.inl 2) _ (hI u v ru rv _ hru hrv hle hx hy) ρ

theorem ht_dec {I : Inst 1 4 Unit} {C : ℕ} (hI : SpecDec I C) (dflt : Loc a b) (l : Lens σ I.R)
    (k : Loc a b) (hcap : 4 + 1 ≤ a + b) (B : Loc a b → List Sym) (x : ℕ) (rx : List Sym)
    (hrx : TermOK rx) (hB : B k = natSyms (x + 1) ++ rx) (ρ : List (HP a b σ)) :
    HT ρ B (callI I [k] dflt l) (Function.update B k (natSyms x ++ rx))
      (C * (zerosLead (encodeNat (x + 1)) + 1)) :=
  HT.callI_upd I [k] dflt (List.nodup_singleton k) rfl hcap l B (.inl 0) _ (hI x rx _ hrx hB) ρ

end rules

/-! ## Instances, registers, specifications -/

/-- The instances `W9c_unpack` calls. -/
structure UInst where
  split : Inst 3 4 Unit
  inc : Inst 1 4 Unit
  cmp : Inst 2 4 Ordering
  sub : Inst 3 4 Unit
  drop : Inst 1 4 Unit
  zero : Inst 1 4 Bool
  dec : Inst 1 4 Unit
  copy : Inst 2 4 Unit
  shlV : Inst 2 4 Unit

namespace UInst

variable (J : UInst)

/-- Registers: the symbol register, then one component per instance. -/
abbrev Reg : Type := Option Sym × J.split.R × J.inc.R × J.cmp.R × J.sub.R × J.drop.R ×
  J.zero.R × J.dec.R × J.copy.R × J.shlV.R

def lS : Lens J.Reg (Option Sym) := Lens.fst _ _
def lSplit : Lens J.Reg J.split.R := (Lens.snd _ _).comp (Lens.fst _ _)
def lInc : Lens J.Reg J.inc.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
def lCmp : Lens J.Reg J.cmp.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
def lSub : Lens J.Reg J.sub.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
  ((Lens.snd _ _).comp (Lens.fst _ _))))
def lDrop : Lens J.Reg J.drop.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))))
def lZero : Lens J.Reg J.zero.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))
def lDec : Lens J.Reg J.dec.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _)))))))
def lCopy : Lens J.Reg J.copy.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _))))))))
def lShlV : Lens J.Reg J.shlV.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
  ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.snd _ _))))))))

/-- Specifications of the instances, with one constant. -/
structure Spec (J : UInst) (C : ℕ) : Prop where
  split : SpecSplitU J.split C
  inc : SpecIncU J.inc C
  cmp : SpecCmpNat J.cmp C
  sub : SpecSubU J.sub C
  drop : SpecDrop J.drop C
  zero : SpecIsZero J.zero C
  dec : SpecDec J.dec C
  copy : SpecCopy J.copy C
  shlV : SpecShlVar J.shlV C

end UInst

#assert_std_axioms udSt_succ udig_snoc udig_length udSt_carry_le udSt_fst_le two_pow_eq'
  bitLen_udig_le bitLen_udStep_le udStep_eq_udT udT_false udT_true lsy_cons lsy_snoc rev_digit
  T_step lsy_ne_mark length_lsy_le isBit_natSyms natSyms_zero_U natSyms_one_U ht_skip ht_split
  ht_inc ht_sub ht_dec

end WP.W9c.Unp
