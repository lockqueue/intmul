import WP.W9e.Macros
import Contracts.W9.Common

/-!
# WP.W9e.Stk — local stacks of the POST routing phases, and the contract call sites

* `Stk`: the stacks the three phases use. `w0`/`c0` are layout-B's `W0`/`C0`; every other stack
  is private scratch (arbitrary content, restored). `s i` (`i < 4`) hosts the scratch stacks of the
  embedded W3/W4 programs (each contract allows at most 4).
* `toB : Stk → BLoc 32` places them in the W9 stack type (`toB_inj`).
* `TrSpec`, `OrSpec`, `OfSpec`, `ShlSpec`, `SplitSpec`, `SubSpec`, `CmpSpec`: the behaviour a
  contract promises for its program (`W4_transpose .down .down`, `W4_oddRoute .down .down`,
  `W4_oddStrideFactor`, `W3_shlVar`, `W3_splitAt`, `W3_subNat`, `W3_cmpNat`), extracted by
  `*_of`, and the `Runs` rule of an embedded call (`rs_*Call`).
-/

namespace WP.W9e

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9

/-- Local stacks of the POST routing phases. -/
inductive Stk
  | w0 | c0 | tmp | ka | kb | dd | ee | x | x2 | y | acc | ks | t1s | cnt | u | ws | bs
  | pin | pout | dist | dist1 | ms | sg | lo
  | s (i : Fin 4)
  deriving DecidableEq

/-- Placement in the W9 stack type: `W0`, `C0`, and scratch `0 … 25` (of 32). -/
def toB : Stk → BLoc 32
  | .w0 => .inl .W0
  | .c0 => .inl .C0
  | .tmp => .inr 4
  | .ka => .inr 5
  | .kb => .inr 6
  | .dd => .inr 7
  | .ee => .inr 8
  | .x => .inr 9
  | .x2 => .inr 10
  | .y => .inr 11
  | .acc => .inr 12
  | .ks => .inr 13
  | .t1s => .inr 14
  | .cnt => .inr 15
  | .u => .inr 16
  | .ws => .inr 17
  | .bs => .inr 18
  | .pin => .inr 19
  | .pout => .inr 20
  | .dist => .inr 21
  | .dist1 => .inr 22
  | .ms => .inr 23
  | .sg => .inr 24
  | .lo => .inr 25
  | .s i => .inr (Fin.castLE (by decide) i)

/-- A left inverse of `toB`. -/
def ofB : BLoc 32 → Stk
  | .inl .C0 => .c0
  | .inl _ => .w0
  | .inr j =>
    match j.val with
    | 0 => .s 0 | 1 => .s 1 | 2 => .s 2 | 3 => .s 3
    | 4 => .tmp | 5 => .ka | 6 => .kb | 7 => .dd | 8 => .ee | 9 => .x | 10 => .x2 | 11 => .y
    | 12 => .acc | 13 => .ks | 14 => .t1s | 15 => .cnt | 16 => .u | 17 => .ws | 18 => .bs
    | 19 => .pin | 20 => .pout | 21 => .dist | 22 => .dist1 | 23 => .ms | 24 => .sg
    | 25 => .lo | _ => .w0

theorem ofB_toB : ∀ k, ofB (toB k) = k
  | .w0 | .c0 | .tmp | .ka | .kb | .dd | .ee | .x | .x2 | .y | .acc | .ks | .t1s | .cnt | .u
  | .ws | .bs | .pin | .pout | .dist | .dist1 | .ms | .sg | .lo => rfl
  | .s ⟨0, _⟩ | .s ⟨1, _⟩ | .s ⟨2, _⟩ | .s ⟨3, _⟩ => rfl
  | .s ⟨n + 4, h⟩ => absurd h (by omega)

theorem toB_inj : Function.Injective toB := fun a b h => by
  rw [← ofB_toB a, ← ofB_toB b, h]

/-! ## Call sites -/

/-- Scratch stacks of an embedded contract instance. -/
def scr {m : ℕ} (hm : m ≤ 4) : Fin m → Stk := fun j => .s (Fin.castLE hm j)

theorem scr_inj {m : ℕ} (hm : m ≤ 4) : Function.Injective (scr hm) := by
  intro i j h
  simp only [scr, Stk.s.injEq] at h
  exact Fin.castLE_inj.mp h

/-- Is this a callee scratch stack? -/
def isS : Stk → Bool
  | .s _ => true
  | _ => false

def nm2 (a b : Stk) : Fin 2 → Stk := fun i => if i.val = 0 then a else b
def nm3 (a b c : Stk) : Fin 3 → Stk := fun i => if i.val = 0 then a else if i.val = 1 then b else c
def nm4 (a b c d : Stk) : Fin 4 → Stk := fun i =>
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d
def nm5 (a b c d e : Stk) : Fin 5 → Stk := fun i =>
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else if i.val = 3 then d
  else e

/-- A call site is injective when the named stacks are pairwise distinct and none of them is a
callee scratch stack. -/
theorem embL_scr_inj {n m : ℕ} (hm : m ≤ 4) {named : Fin n → Stk}
    (h1 : ∀ i j, named i = named j → i = j) (h2 : ∀ i, isS (named i) = false) :
    Function.Injective (embL named (scr hm)) := by
  refine embL_inj (fun i j h => h1 i j h) (scr_inj hm) (fun i j h => ?_)
  have := h2 i
  rw [h] at this
  simp [scr, isS] at this

theorem nm2_ok {a b : Stk} (hab : a ≠ b) (ha : isS a = false) (hb : isS b = false) :
    (∀ i j, nm2 a b i = nm2 a b j → i = j) ∧ ∀ i, isS (nm2 a b i) = false := by
  refine ⟨fun ⟨i, hi⟩ ⟨j, hj⟩ h => ?_, fun ⟨i, hi⟩ => ?_⟩
  · simp only [nm2] at h
    apply Fin.ext
    split_ifs at h <;> first | (simp only; omega) | (exfalso; simp_all)
  · simp only [nm2]
    split_ifs <;> assumption

theorem nm3_ok {a b c : Stk} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : isS a = false)
    (hb : isS b = false) (hc : isS c = false) :
    (∀ i j, nm3 a b c i = nm3 a b c j → i = j) ∧ ∀ i, isS (nm3 a b c i) = false := by
  refine ⟨fun ⟨i, hi⟩ ⟨j, hj⟩ h => ?_, fun ⟨i, hi⟩ => ?_⟩
  · simp only [nm3] at h
    apply Fin.ext
    split_ifs at h <;> first | (simp only; omega) | (exfalso; simp_all)
  · simp only [nm3]
    split_ifs <;> assumption

theorem nm4_ok {a b c d : Stk} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (ha : isS a = false) (hb : isS b = false) (hc : isS c = false)
    (hd : isS d = false) :
    (∀ i j, nm4 a b c d i = nm4 a b c d j → i = j) ∧ ∀ i, isS (nm4 a b c d i) = false := by
  refine ⟨fun ⟨i, hi⟩ ⟨j, hj⟩ h => ?_, fun ⟨i, hi⟩ => ?_⟩
  · simp only [nm4] at h
    apply Fin.ext
    split_ifs at h <;> first | (simp only; omega) | (exfalso; simp_all)
  · simp only [nm4]
    split_ifs <;> assumption

theorem nm5_ok {a b c d e : Stk} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (ha : isS a = false) (hb : isS b = false) (hc : isS c = false) (hd : isS d = false)
    (he : isS e = false) :
    (∀ i j, nm5 a b c d e i = nm5 a b c d e j → i = j) ∧ ∀ i, isS (nm5 a b c d e i) = false := by
  refine ⟨fun ⟨i, hi⟩ ⟨j, hj⟩ h => ?_, fun ⟨i, hi⟩ => ?_⟩
  · simp only [nm5] at h
    apply Fin.ext
    split_ifs at h <;> first | (simp only; omega) | (exfalso; simp_all)
  · simp only [nm5]
    split_ifs <;> assumption

/-! ## Contract behaviours -/

section Specs

variable {m : ℕ} {R : Type}

/-- What `W4_transpose .down .down` promises for its program. -/
def TrSpec (P : Prog (Loc 4 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (v : List (List Sym)) (rest r2 r3 : List Sym) (S : Loc 4 m → List Sym),
    v.length = 2 ^ a * 2 ^ b → (∀ r ∈ v, RecOK r) → BlkTerm rest → TermOK r2 → TermOK r3 →
    S (.inl 0) = blk .down v ++ rest → S (.inl 2) = natSyms a ++ r2 →
    S (.inl 3) = natSyms b ++ r3 →
    Runs P S (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (blk .down (transposeL (2 ^ a) (2 ^ b) v) ++ S (.inl 1))) (fun _ => True)
      (C * ((blk .down v).length + 1) * (min a b + 1) + C * (bitLen a + bitLen b + 1))

/-- What `W4_oddRoute .down .down` promises for its program. -/
def OrSpec (P : Prog (Loc 5 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (k w b : ℕ) (v : List (List Sym)) (rest r2 r3 r4 : List Sym) (S : Loc 5 m → List Sym),
    OddRouteParam k w → b < 2 ^ k → v.length = 2 ^ k → (∀ r ∈ v, RecOK r) →
    BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 →
    S (.inl 0) = blk .down v ++ rest → S (.inl 2) = natSyms k ++ r2 →
    S (.inl 3) = natSyms w ++ r3 → S (.inl 4) = natSyms b ++ r4 →
    Runs P S (Function.update (Function.update S (.inl 0) rest) (.inl 1)
        (blk .down (oddRouteL k w b v) ++ S (.inl 1))) (fun _ => True)
      (C * ((blk .down v).length + 1) * (k + 1))

/-- What `W4_oddStrideFactor` promises for its program. -/
def OfSpec (P : Prog (Loc 3 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (k u2 : ℕ) (r0 r1 : List Sym) (S : Loc 3 m → List Sym), TermOK r0 → TermOK r1 →
    S (.inl 0) = natSyms k ++ r0 → S (.inl 1) = natSyms u2 ++ r1 →
    Runs P S (Function.update S (.inl 2) (natSyms (computableOddStrideFactor k u2) ++ S (.inl 2)))
      (fun _ => True) (C * ((k + 1) ^ 2 + bitLen u2))

/-- What `W3_shlVar` promises for its program. -/
def ShlSpec (P : Prog (Loc 2 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs P S (Function.update S (.inl 0) (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
      (C * (c + bitLen c + 1))

/-- What `W3_splitAt` promises for its program. -/
def SplitSpec (P : Prog (Loc 3 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs P S (Function.update (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx))
        (.inl 2) (natSyms (a % 2 ^ c) ++ S (.inl 2))) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- What `W3_subNat` promises for its program. -/
def SubSpec (P : Prog (Loc 3 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry → b ≤ a →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- What `W3_cmpNat` promises for its program (observation `obs`). -/
def CmpSpec (P : Prog (Loc 2 m) (fun _ => Sym) R) (obs : R → Ordering) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs P S S (fun r => obs r = Lib.ordOf a b) (C * (bitLen a + bitLen b + 1))

end Specs

theorem trSpec_of (h : W4_transpose .down .down) :
    ∃ (C m : ℕ) (R : Type) (P : Prog (Loc 4 m) (fun _ => Sym) R),
      m ≤ 4 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧ TrSpec P C := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨m, R, _, P, hm, hfin, hne, hcl, hs⟩ := hC ()
  exact ⟨C, m, R, P, hm, hfin, hne, hcl, hs⟩

theorem orSpec_of (h : W4_oddRoute .down .down) :
    ∃ (C m : ℕ) (R : Type) (P : Prog (Loc 5 m) (fun _ => Sym) R),
      m ≤ 4 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧ OrSpec P C := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨m, R, _, P, hm, hfin, hne, hcl, hs⟩ := hC ()
  exact ⟨C, m, R, P, hm, hfin, hne, hcl, hs⟩

theorem ofSpec_of (h : W4_oddStrideFactor) :
    ∃ (C m : ℕ) (R : Type) (P : Prog (Loc 3 m) (fun _ => Sym) R),
      m ≤ 4 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧ OfSpec P C := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨m, R, _, P, hm, hfin, hne, hcl, hs⟩ := hC ()
  exact ⟨C, m, R, P, hm, hfin, hne, hcl, hs⟩

theorem shlSpec_of (h : W3_shlVar) :
    ∃ (C m : ℕ) (R : Type) (P : Prog (Loc 2 m) (fun _ => Sym) R),
      m ≤ 4 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧ ShlSpec P C := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨m, R, _, P, hm, hfin, hne, hcl, hs⟩ := hC ()
  exact ⟨C, m, R, P, hm, hfin, hne, hcl, hs⟩

theorem splitSpec_of (h : W3_splitAt) :
    ∃ (C m : ℕ) (R : Type) (P : Prog (Loc 3 m) (fun _ => Sym) R),
      m ≤ 4 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧ SplitSpec P C := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨m, R, _, P, hm, hfin, hne, hcl, hs⟩ := hC ()
  exact ⟨C, m, R, P, hm, hfin, hne, hcl, hs⟩

theorem subSpec_of (h : W3_subNat) :
    ∃ (C m : ℕ) (R : Type) (P : Prog (Loc 3 m) (fun _ => Sym) R),
      m ≤ 4 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧ SubSpec P C := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨m, R, _, P, hm, hfin, hne, hcl, hs⟩ := hC ()
  exact ⟨C, m, R, P, hm, hfin, hne, hcl, hs⟩

theorem cmpSpec_of (h : W3_cmpNat) :
    ∃ (C m : ℕ) (R : Type) (obs : R → Ordering) (P : Prog (Loc 2 m) (fun _ => Sym) R),
      m ≤ 4 ∧ Finite R ∧ Nonempty R ∧ P.Closed ∧ CmpSpec P obs C := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨m, R, obs, P, hm, hfin, hne, hcl, hs⟩ := hC ()
  exact ⟨C, m, R, obs, P, hm, hfin, hne, hcl, hs⟩

/-! ## Embedded calls -/

section Calls

variable {σ : Type} {m : ℕ} {R : Type}

theorem rs_trCall {P : Prog (Loc 4 m) (fun _ => Sym) R} {C : ℕ} (hP : TrSpec P C)
    (lT : Lens σ R) (hm : m ≤ 4) {src dst sa sb : Stk}
    (hinj : Function.Injective (embL (nm4 src dst sa sb) (scr hm))) (a b : ℕ)
    (v : List (List Sym)) (rest r2 r3 : List Sym) (S : Stk → List Sym)
    (hv : v.length = 2 ^ a * 2 ^ b) (hrec : ∀ r ∈ v, RecOK r) (hrest : BlkTerm rest)
    (hr2 : TermOK r2) (hr3 : TermOK r3) (hsrc : S src = blk .down v ++ rest)
    (hka : S sa = natSyms a ++ r2) (hkb : S sb = natSyms b ++ r3) :
    Runs ((P.mapStk (embL (nm4 src dst sa sb) (scr hm))).liftRegs lT) S
      (Function.update (Function.update S src rest) dst
        (blk .down (transposeL (2 ^ a) (2 ^ b) v) ++ S dst)) (fun _ => True)
      (C * ((blk .down v).length + 1) * (min a b + 1) + C * (bitLen a + bitLen b + 1)) :=
  runs_weak (runs_liftRegs lT (runs_embed_upd2 hinj S (.inl 0) (.inl 1) _ _
    (hP a b v rest r2 r3 _ hv hrec hrest hr2 hr3 hsrc hka hkb)))

theorem rs_orCall {P : Prog (Loc 5 m) (fun _ => Sym) R} {C : ℕ} (hP : OrSpec P C)
    (lR : Lens σ R) (hm : m ≤ 4) {src dst kk kw kof : Stk}
    (hinj : Function.Injective (embL (nm5 src dst kk kw kof) (scr hm))) (k w b : ℕ)
    (v : List (List Sym)) (rest r2 r3 r4 : List Sym) (S : Stk → List Sym)
    (hw : OddRouteParam k w) (hb : b < 2 ^ k) (hv : v.length = 2 ^ k) (hrec : ∀ r ∈ v, RecOK r)
    (hrest : BlkTerm rest) (hr2 : TermOK r2) (hr3 : TermOK r3) (hr4 : TermOK r4)
    (hsrc : S src = blk .down v ++ rest) (hk : S kk = natSyms k ++ r2)
    (hkw : S kw = natSyms w ++ r3) (hkb : S kof = natSyms b ++ r4) :
    Runs ((P.mapStk (embL (nm5 src dst kk kw kof) (scr hm))).liftRegs lR) S
      (Function.update (Function.update S src rest) dst (blk .down (oddRouteL k w b v) ++ S dst))
      (fun _ => True) (C * ((blk .down v).length + 1) * (k + 1)) :=
  runs_weak (runs_liftRegs lR (runs_embed_upd2 hinj S (.inl 0) (.inl 1) _ _
    (hP k w b v rest r2 r3 r4 _ hw hb hv hrec hrest hr2 hr3 hr4 hsrc hk hkw hkb)))

theorem rs_ofCall {P : Prog (Loc 3 m) (fun _ => Sym) R} {C : ℕ} (hP : OfSpec P C)
    (lF : Lens σ R) (hm : m ≤ 4) {kk ku kd : Stk}
    (hinj : Function.Injective (embL (nm3 kk ku kd) (scr hm))) (k u2 : ℕ) (r0 r1 : List Sym)
    (S : Stk → List Sym) (hr0 : TermOK r0) (hr1 : TermOK r1) (hk : S kk = natSyms k ++ r0)
    (hu : S ku = natSyms u2 ++ r1) :
    Runs ((P.mapStk (embL (nm3 kk ku kd) (scr hm))).liftRegs lF) S
      (Function.update S kd (natSyms (computableOddStrideFactor k u2) ++ S kd)) (fun _ => True)
      (C * ((k + 1) ^ 2 + bitLen u2)) :=
  runs_weak (runs_liftRegs lF (runs_embed_upd hinj S (.inl 2) _
    (hP k u2 r0 r1 _ hr0 hr1 hk hu)))

theorem rs_shlCall {P : Prog (Loc 2 m) (fun _ => Sym) R} {C : ℕ} (hP : ShlSpec P C)
    (lH : Lens σ R) (hm : m ≤ 4) {kx kc : Stk}
    (hinj : Function.Injective (embL (nm2 kx kc) (scr hm))) (a c : ℕ) (rx rc : List Sym)
    (S : Stk → List Sym) (hrx : TermOK rx) (hrc : TermOK rc) (hx : S kx = natSyms a ++ rx)
    (hc : S kc = natSyms c ++ rc) :
    Runs ((P.mapStk (embL (nm2 kx kc) (scr hm))).liftRegs lH) S
      (Function.update S kx (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
      (C * (c + bitLen c + 1)) :=
  runs_weak (runs_liftRegs lH (runs_embed_upd hinj S (.inl 0) _ (hP a c rx rc _ hrx hrc hx hc)))

theorem rs_splitCall {P : Prog (Loc 3 m) (fun _ => Sym) R} {C : ℕ} (hP : SplitSpec P C)
    (lP : Lens σ R) (hm : m ≤ 4) {kx kc ky : Stk}
    (hinj : Function.Injective (embL (nm3 kx kc ky) (scr hm))) (a c : ℕ) (rx rc : List Sym)
    (S : Stk → List Sym) (hrx : TermOK rx) (hrc : TermOK rc) (hx : S kx = natSyms a ++ rx)
    (hc : S kc = natSyms c ++ rc) :
    Runs ((P.mapStk (embL (nm3 kx kc ky) (scr hm))).liftRegs lP) S
      (Function.update (Function.update S kx (natSyms (a / 2 ^ c) ++ rx)) ky
        (natSyms (a % 2 ^ c) ++ S ky)) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1)) :=
  runs_weak (runs_liftRegs lP (runs_embed_upd2 hinj S (.inl 0) (.inl 2) _ _
    (hP a c rx rc _ hrx hrc hx hc)))

theorem rs_subCall {P : Prog (Loc 3 m) (fun _ => Sym) R} {C : ℕ} (hP : SubSpec P C)
    (lB : Lens σ R) (hm : m ≤ 4) {kx ky kz : Stk}
    (hinj : Function.Injective (embL (nm3 kx ky kz) (scr hm))) (a b : ℕ) (rx ry : List Sym)
    (S : Stk → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hba : b ≤ a)
    (hx : S kx = natSyms a ++ rx) (hy : S ky = natSyms b ++ ry) :
    Runs ((P.mapStk (embL (nm3 kx ky kz) (scr hm))).liftRegs lB) S
      (Function.update S kz (natSyms (a - b) ++ S kz)) (fun _ => True)
      (C * (bitLen a + bitLen b + 1)) :=
  runs_weak (runs_liftRegs lB (runs_embed_upd hinj S (.inl 2) _
    (hP a b rx ry _ hrx hry hba hx hy)))

theorem rs_cmpCall {P : Prog (Loc 2 m) (fun _ => Sym) R} {obs : R → Ordering} {C : ℕ}
    (hP : CmpSpec P obs C) (lC : Lens σ R) (hm : m ≤ 4) {kx ky : Stk}
    (hinj : Function.Injective (embL (nm2 kx ky) (scr hm))) (a b : ℕ) (rx ry : List Sym)
    (S : Stk → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hx : S kx = natSyms a ++ rx)
    (hy : S ky = natSyms b ++ ry) :
    Runs ((P.mapStk (embL (nm2 kx ky) (scr hm))).liftRegs lC) S S
      (fun v => obs (lC.get v) = Lib.ordOf a b) (C * (bitLen a + bitLen b + 1)) :=
  runs_liftRegs lC (runs_embed_same hinj S (hP a b rx ry _ hrx hry hx hy))

end Calls

#assert_std_axioms ofB_toB toB_inj scr_inj embL_scr_inj nm2_ok nm3_ok nm4_ok nm5_ok trSpec_of
  orSpec_of ofSpec_of shlSpec_of splitSpec_of subSpec_of cmpSpec_of rs_trCall rs_orCall rs_ofCall
  rs_shlCall rs_splitCall rs_subCall rs_cmpCall

end WP.W9e
