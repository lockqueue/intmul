import WP.W9b.AltMath
import WP.W9b.Emit
import Contracts.Machine.W3

/-!
# WP.W9b.AltOps — components of the P2 kernel (`W9_altSum`)

* `cdLoop_runsL`: the count-down loop over a fixed list `L`; the body lemma may use the split
  `done ++ a :: todo = L` (needed for the accumulator width bounds).
* `AStk`: the kernel's local stacks; `W3Kit`: the six W3 programs it is parametrized by (rule 6:
  `W3_addInt`, `W3_subInt`, `W3_addNat`, `W3_subNat`, `W3_shlVar`, `W3_shrVar`); `W3Ok k C`: their
  specifications at one constant `C`; `KReg k`: the register file, with lenses `kS`, `kC`, `kA`, ….
* Call wrappers `addI`, `subI`, `addN`, `subN`, `shlV`, `shrV` with `Runs` lemmas.
* `mvIntOnly`, the signed left shift `shlS`, and the pair step `pairBody` of the alternating sum.
-/

namespace WP.W9b

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Count-down loops over a fixed list -/

section LoopL

variable {K σ : Type} [DecidableEq K]

theorem cdLoop_loopL (lS : Lens σ (Option Sym)) {k t : K} (hkt : k ≠ t)
    (body : Prog K (fun _ => Sym) σ) {α : Type} (Fs : List α → List α → K → List Sym)
    (L : List α) (kb : List Sym) (hkb : TermOK kb) (B : α → ℕ)
    (hbody : ∀ done a todo, done ++ a :: todo = L → Runs body
      (Function.update (Fs done (a :: todo)) k (natSyms (todo.length + 1) ++ kb))
      (Function.update (Fs (done ++ [a]) todo) k (natSyms (todo.length + 1) ++ kb))
      (fun _ => True) (B a)) :
    ∀ (todo done : List α) (s : TMFw.St K (fun _ => Sym) σ), done ++ todo = L →
      s.stk = Function.update (Fs done todo) k (natSyms todo.length ++ kb) →
      optIsBit (lS.get s.var) = !decide (todo.length = 0) →
      ∃ s' t', Eval [] (.loop (fun v => optIsBit (lS.get v))
          (.seq body (.seq (decL lS k t) (ztL lS k)))) s s' t' ∧
        s'.stk = Function.update (Fs L []) k (natSyms 0 ++ kb) ∧
        t' ≤ (todo.map B).sum + decSum todo.length + 2 * todo.length + 1
  | [], done, s, hL, hs, hc => by
    refine ⟨s, 1, Eval.loop_false ?_, ?_, by simp⟩
    · simpa using hc
    · rw [← hL, List.append_nil]
      simpa using hs
  | a :: todo, done, s, hL, hs, hc => by
    have hd : Runs (decL lS k t)
        (Function.update (Fs (done ++ [a]) todo) k (natSyms (todo.length + 1) ++ kb))
        (Function.update (Fs (done ++ [a]) todo) k (natSyms todo.length ++ kb)) (fun _ => True)
        (6 * zerosLead (encodeNat (todo.length + 1)) + 8) :=
      runs_post (runs_lift lS (rs_dec hkt todo.length kb _ hkb (Function.update_self _ _ _)))
        (Function.update_idem _ _ _) le_rfl
    have hz : Runs (ztL lS k)
        (Function.update (Fs (done ++ [a]) todo) k (natSyms todo.length ++ kb))
        (Function.update (Fs (done ++ [a]) todo) k (natSyms todo.length ++ kb))
        (fun v => optIsBit (lS.get v) = !decide (todo.length = 0)) 1 :=
      runs_liftRegs lS (rs_zeroTest todo.length kb _ hkb (Function.update_self _ _ _))
    obtain ⟨s1, t1, e1, ⟨hs1, hc1⟩, ht1⟩ := runs_seq (hbody done a todo hL) (runs_seq hd hz) s hs
    obtain ⟨s2, t2, e2, hs2, ht2⟩ :=
      cdLoop_loopL lS hkt body Fs L kb hkb B hbody todo (done ++ [a]) s1
        (by rw [List.append_assoc, List.singleton_append]; exact hL) hs1 hc1
    refine ⟨s2, t1 + t2 + 1, Eval.loop_true ?_ e1 e2, hs2, ?_⟩
    · simpa using hc
    · simp only [List.map_cons, List.sum_cons, List.length_cons, decSum]
      omega

/-- **Count-down loop over a fixed list `L`, `Runs` form.** -/
theorem cdLoop_runsL (lS : Lens σ (Option Sym)) {k t : K} (hkt : k ≠ t)
    (body : Prog K (fun _ => Sym) σ) {α : Type} (Fs : List α → List α → K → List Sym)
    (L : List α) (kb : List Sym) (hkb : TermOK kb) (B : α → ℕ)
    (hbody : ∀ done a todo, done ++ a :: todo = L → Runs body
      (Function.update (Fs done (a :: todo)) k (natSyms (todo.length + 1) ++ kb))
      (Function.update (Fs (done ++ [a]) todo) k (natSyms (todo.length + 1) ++ kb))
      (fun _ => True) (B a)) :
    Runs (cdLoop lS k t body) (Function.update (Fs [] L) k (natSyms L.length ++ kb))
      (Function.update (Fs L []) k (natSyms 0 ++ kb)) (fun _ => True)
      ((L.map B).sum + decSum L.length + 2 * L.length + 2) := by
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hc1⟩, ht1⟩ :=
    runs_liftRegs lS (rs_zeroTest L.length kb _ hkb (Function.update_self _ _ _)) s hs
  obtain ⟨s2, t2, e2, hs2, ht2⟩ := cdLoop_loopL lS hkt body Fs L kb hkb B hbody L [] s1 rfl hs1 hc1
  exact ⟨s2, t1 + t2, Eval.seq e1 e2, ⟨hs2, trivial⟩, by omega⟩

/-- Move a signed number (sign and bits) onto `dst`, reversing it; its terminator stays. -/
def mvIntOnly (src dst : K) : SProg K := .seq (mvSym src dst) (moveBlock src dst)

theorem rs_mvIntOnly {src dst : K} (hne : src ≠ dst) (z : ℤ) (rest : List Sym)
    (hrest : TermOK rest) (S : K → List Sym) (hS : S src = intSyms z ++ rest) :
    Runs (mvIntOnly src dst) S
      (Function.update (Function.update S src rest) dst ((intSyms z).reverse ++ S dst))
      (fun _ => True) (3 * bitLen z.natAbs + 6) := by
  have h1 := rs_mvSym hne (sgnSym z) (natSyms z.natAbs ++ rest) S (by rw [hS]; rfl)
  have h2 := rs_moveBlock hne (encodeNat z.natAbs) rest
    (Function.update (Function.update S src (natSyms z.natAbs ++ rest)) dst (sgnSym z :: S dst))
    hrest (by rw [Function.update_of_ne hne, Function.update_self]; rfl)
  refine runs_post (runs_seq h1 h2) ?_ (by simp only [bitLen]; omega)
  funext x
  simp only [Function.update_apply, intSyms, natSyms]
  split_ifs <;> simp_all

end LoopL

theorem closed_mvIntOnly {K : Type} (src dst : K) : (mvIntOnly src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, mvIntOnly, mvSym, moveBlock, moveBits, moveBitsBody, restoreR,
    popR, pushR, Lib.skip]

/-! ## Local stacks, the W3 kit, registers -/

/-- Local stacks of the P2 kernel; `s i` are the (shared) scratch stacks of the W3 programs. -/
inductive AStk
  | W0 | C0 | C1 | RET | T | J | K | R | H | t
  | AR | AR' | AI | AI' | P | Q | PI | SS | D | E | F | Y | G | SG
  | s (i : Fin 4)
  deriving DecidableEq

/-- The W3 programs the P2 kernel is parametrized by. -/
structure W3Kit where
  mA : ℕ
  RA : Type
  PA : Prog (Loc 3 mA) (fun _ => Sym) RA
  hA : mA ≤ 4
  mS : ℕ
  RS : Type
  PS : Prog (Loc 3 mS) (fun _ => Sym) RS
  hS : mS ≤ 4
  mN : ℕ
  RN : Type
  PN : Prog (Loc 3 mN) (fun _ => Sym) RN
  hN : mN ≤ 4
  mM : ℕ
  RM : Type
  PM : Prog (Loc 3 mM) (fun _ => Sym) RM
  hM : mM ≤ 4
  mL : ℕ
  RL : Type
  PL : Prog (Loc 2 mL) (fun _ => Sym) RL
  hL : mL ≤ 4
  mR : ℕ
  RR : Type
  PR : Prog (Loc 2 mR) (fun _ => Sym) RR
  hR : mR ≤ 4

/-- Registers: symbol register, comparator, and the six W3 programs' registers. -/
abbrev KReg (k : W3Kit) : Type :=
  Option Sym × CReg × k.RA × k.RS × k.RN × k.RM × k.RL × k.RR

/-- Lens: symbol register. -/
def kS (k : W3Kit) : Lens (KReg k) (Option Sym) := Lens.fst _ _
/-- Lens: comparator registers. -/
def kC (k : W3Kit) : Lens (KReg k) CReg := (Lens.snd _ _).comp (Lens.fst _ _)
/-- Lens: signed adder. -/
def kA (k : W3Kit) : Lens (KReg k) k.RA :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
/-- Lens: signed subtractor. -/
def kSb (k : W3Kit) : Lens (KReg k) k.RS :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
/-- Lens: unsigned adder. -/
def kN (k : W3Kit) : Lens (KReg k) k.RN :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
/-- Lens: unsigned subtractor. -/
def kM (k : W3Kit) : Lens (KReg k) k.RM :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))
/-- Lens: left shift. -/
def kL (k : W3Kit) : Lens (KReg k) k.RL :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))
/-- Lens: right shift. -/
def kR (k : W3Kit) : Lens (KReg k) k.RR :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))))))

/-! ## The W3 specifications used -/

/-- `W3_addInt`'s promise. -/
def AddISpec {m : ℕ} {R : Type} (P : Prog (Loc 3 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs P S (Function.update S (.inl 2) (intSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- `W3_subInt`'s promise. -/
def SubISpec {m : ℕ} {R : Type} (P : Prog (Loc 3 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs P S (Function.update S (.inl 2) (intSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1))

/-- `W3_addNat`'s promise. -/
def AddNSpec {m : ℕ} {R : Type} (P : Prog (Loc 3 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs P S (Function.update S (.inl 2) (natSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- `W3_subNat`'s promise. -/
def SubNSpec {m : ℕ} {R : Type} (P : Prog (Loc 3 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (a b : ℕ) (rx ry : List Sym) (S : Loc 3 m → List Sym), TermOK rx → TermOK ry → b ≤ a →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms b ++ ry →
    Runs P S (Function.update S (.inl 2) (natSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (C * (bitLen a + bitLen b + 1))

/-- `W3_shlVar`'s promise. -/
def ShlSpec {m : ℕ} {R : Type} (P : Prog (Loc 2 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs P S (Function.update S (.inl 0) (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
      (C * (c + bitLen c + 1))

/-- `W3_shrVar`'s promise. -/
def ShrSpec {m : ℕ} {R : Type} (P : Prog (Loc 2 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs P S (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx)) (fun _ => True)
      (C * (min c (bitLen a) + bitLen c + 1))

/-- The six specifications at one constant. -/
structure W3Ok (k : W3Kit) (C : ℕ) : Prop where
  add : AddISpec k.PA C
  sub : SubISpec k.PS C
  addN : AddNSpec k.PN C
  subN : SubNSpec k.PM C
  shl : ShlSpec k.PL C
  shr : ShrSpec k.PR C

/-! ## Call sites -/

/-- Named stacks of a 3-stack call. -/
def nm3 (x y z : AStk) : Fin 3 → AStk := fun i =>
  if i.val = 0 then x else if i.val = 1 then y else z

/-- Named stacks of a 2-stack call. -/
def nm2 (x y : AStk) : Fin 2 → AStk := fun i => if i.val = 0 then x else y

/-- The W3 scratch stacks. -/
def aScr {m : ℕ} (hm : m ≤ 4) : Fin m → AStk := fun j => .s (Fin.castLE hm j)

/-- Not a W3 scratch stack. -/
def NotS : AStk → Prop
  | .s _ => False
  | _ => True

theorem aScr_inj {m : ℕ} (hm : m ≤ 4) : Function.Injective (aScr hm) := by
  intro i j h
  simp only [aScr, AStk.s.injEq] at h
  exact Fin.castLE_inj.mp h

theorem embL3_inj {m : ℕ} (hm : m ≤ 4) {x y z : AStk} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : NotS x) (hy : NotS y) (hz : NotS z) :
    Function.Injective (embL (nm3 x y z) (aScr hm)) := by
  refine embL_inj ?_ (aScr_inj hm) ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [nm3]
  · intro i j h
    fin_cases i <;> simp only [nm3, aScr] at h <;> simp at h <;> subst h <;>
      first | exact hx | exact hy | exact hz

theorem embL2_inj {m : ℕ} (hm : m ≤ 4) {x y : AStk} (hxy : x ≠ y) (hx : NotS x) (hy : NotS y) :
    Function.Injective (embL (nm2 x y) (aScr hm)) := by
  refine embL_inj ?_ (aScr_inj hm) ?_
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [nm2]
  · intro i j h
    fin_cases i <;> simp only [nm2, aScr] at h <;> simp at h <;> subst h <;>
      first | exact hx | exact hy

section Calls

variable (k : W3Kit)

/-- A symbol-register macro inside the P2 kernel. -/
def kSym (p : SProg AStk) : Prog AStk (fun _ => Sym) (KReg k) := p.liftRegs (kS k)

/-- `z += x + y` (signed). -/
def addI (x y z : AStk) : Prog AStk (fun _ => Sym) (KReg k) :=
  (k.PA.mapStk (embL (nm3 x y z) (aScr k.hA))).liftRegs (kA k)

/-- `z += x − y` (signed). -/
def subI (x y z : AStk) : Prog AStk (fun _ => Sym) (KReg k) :=
  (k.PS.mapStk (embL (nm3 x y z) (aScr k.hS))).liftRegs (kSb k)

/-- `z += x + y` (unsigned). -/
def addN (x y z : AStk) : Prog AStk (fun _ => Sym) (KReg k) :=
  (k.PN.mapStk (embL (nm3 x y z) (aScr k.hN))).liftRegs (kN k)

/-- `z += x − y` (unsigned, `y ≤ x`). -/
def subN (x y z : AStk) : Prog AStk (fun _ => Sym) (KReg k) :=
  (k.PM.mapStk (embL (nm3 x y z) (aScr k.hM))).liftRegs (kM k)

/-- `x := x · 2^c` (in place). -/
def shlV (x c : AStk) : Prog AStk (fun _ => Sym) (KReg k) :=
  (k.PL.mapStk (embL (nm2 x c) (aScr k.hL))).liftRegs (kL k)

/-- `x := x / 2^c` (in place). -/
def shrV (x c : AStk) : Prog AStk (fun _ => Sym) (KReg k) :=
  (k.PR.mapStk (embL (nm2 x c) (aScr k.hR))).liftRegs (kR k)

theorem rs_addI {C : ℕ} (hP : AddISpec k.PA C) {x y z : AStk}
    (hinj : Function.Injective (embL (nm3 x y z) (aScr k.hA))) (a b : ℤ) (rx ry : List Sym)
    (S : AStk → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hx : S x = intSyms a ++ rx)
    (hy : S y = intSyms b ++ ry) :
    Runs (addI k x y z) S (Function.update S z (intSyms (a + b) ++ S z)) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1)) :=
  runs_lift (kA k) (runs_embed_upd hinj S (.inl 2) _ (hP a b rx ry _ hrx hry hx hy))

theorem rs_subI {C : ℕ} (hP : SubISpec k.PS C) {x y z : AStk}
    (hinj : Function.Injective (embL (nm3 x y z) (aScr k.hS))) (a b : ℤ) (rx ry : List Sym)
    (S : AStk → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hx : S x = intSyms a ++ rx)
    (hy : S y = intSyms b ++ ry) :
    Runs (subI k x y z) S (Function.update S z (intSyms (a - b) ++ S z)) (fun _ => True)
      (C * (bitLen a.natAbs + bitLen b.natAbs + 1)) :=
  runs_lift (kSb k) (runs_embed_upd hinj S (.inl 2) _ (hP a b rx ry _ hrx hry hx hy))

theorem rs_addN {C : ℕ} (hP : AddNSpec k.PN C) {x y z : AStk}
    (hinj : Function.Injective (embL (nm3 x y z) (aScr k.hN))) (a b : ℕ) (rx ry : List Sym)
    (S : AStk → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hx : S x = natSyms a ++ rx)
    (hy : S y = natSyms b ++ ry) :
    Runs (addN k x y z) S (Function.update S z (natSyms (a + b) ++ S z)) (fun _ => True)
      (C * (bitLen a + bitLen b + 1)) :=
  runs_lift (kN k) (runs_embed_upd hinj S (.inl 2) _ (hP a b rx ry _ hrx hry hx hy))

theorem rs_subN {C : ℕ} (hP : SubNSpec k.PM C) {x y z : AStk}
    (hinj : Function.Injective (embL (nm3 x y z) (aScr k.hM))) (a b : ℕ) (rx ry : List Sym)
    (S : AStk → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hba : b ≤ a)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) :
    Runs (subN k x y z) S (Function.update S z (natSyms (a - b) ++ S z)) (fun _ => True)
      (C * (bitLen a + bitLen b + 1)) :=
  runs_lift (kM k) (runs_embed_upd hinj S (.inl 2) _ (hP a b rx ry _ hrx hry hba hx hy))

theorem rs_shlV {C : ℕ} (hP : ShlSpec k.PL C) {x c : AStk}
    (hinj : Function.Injective (embL (nm2 x c) (aScr k.hL))) (a n : ℕ) (rx rc : List Sym)
    (S : AStk → List Sym) (hrx : TermOK rx) (hrc : TermOK rc) (hx : S x = natSyms a ++ rx)
    (hc : S c = natSyms n ++ rc) :
    Runs (shlV k x c) S (Function.update S x (natSyms (a * 2 ^ n) ++ rx)) (fun _ => True)
      (C * (n + bitLen n + 1)) :=
  runs_lift (kL k) (runs_embed_upd hinj S (.inl 0) _ (hP a n rx rc _ hrx hrc hx hc))

theorem rs_shrV {C : ℕ} (hP : ShrSpec k.PR C) {x c : AStk}
    (hinj : Function.Injective (embL (nm2 x c) (aScr k.hR))) (a n : ℕ) (rx rc : List Sym)
    (S : AStk → List Sym) (hrx : TermOK rx) (hrc : TermOK rc) (hx : S x = natSyms a ++ rx)
    (hc : S c = natSyms n ++ rc) :
    Runs (shrV k x c) S (Function.update S x (natSyms (a / 2 ^ n) ++ rx)) (fun _ => True)
      (C * (min n (bitLen a) + bitLen n + 1)) :=
  runs_lift (kR k) (runs_embed_upd hinj S (.inl 0) _ (hP a n rx rc _ hrx hrc hx hc))

/-! ## The signed left shift -/

/-- Signed `z := z · 2^d` (the sign is parked on `SG`). -/
def shlS (z : AStk) : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (kSym k (mvSym z .SG)) (.seq (shlV k z .D) (kSym k (mvSym .SG z)))

theorem rs_shlS {C : ℕ} (hok : W3Ok k C) {z : AStk} (hz : z = .AI ∨ z = .AR) (zv : ℤ) (dv : ℕ)
    (zr dr : List Sym) (hzr : TermOK zr) (hdr : TermOK dr) (S : AStk → List Sym)
    (hzS : S z = intSyms zv ++ zr) (hdS : S .D = natSyms dv ++ dr) :
    Runs (shlS k z) S (Function.update S z (intSyms (zv * ((2 ^ dv : ℕ) : ℤ)) ++ zr))
      (fun _ => True) (C * (dv + bitLen dv + 1) + 4) := by
  have hzSG : z ≠ .SG := by rcases hz with rfl | rfl <;> decide
  have hzD : z ≠ .D := by rcases hz with rfl | rfl <;> decide
  have hzN : NotS z := by rcases hz with rfl | rfl <;> trivial
  have e1 := runs_lift (kS k) (rs_mvSym hzSG (sgnSym zv) (natSyms zv.natAbs ++ zr) S
    (by rw [hzS]; rfl))
  set S1 := Function.update (Function.update S z (natSyms zv.natAbs ++ zr)) .SG
    (sgnSym zv :: S .SG) with hS1
  have e2 := rs_shlV k hok.shl (embL2_inj k.hL hzD hzN trivial) zv.natAbs dv zr dr S1 hzr hdr
    (by simp [hS1, hzSG])
    (by simp [hS1, Ne.symm hzD, hdS])
  set S2 := Function.update S1 z (natSyms (zv.natAbs * 2 ^ dv) ++ zr) with hS2
  have e3 := runs_lift (kS k) (rs_mvSym (Ne.symm hzSG) (sgnSym zv) (S .SG) S2
    (by simp [hS2, hS1, Ne.symm hzSG]))
  refine runs_post (runs_seq e1 (runs_seq e2 e3)) ?_ (by omega)
  rw [intSyms_mul_two_pow]
  funext x
  simp only [hS2, hS1, Function.update_apply]
  split_ifs <;> simp_all

/-! ## One step of the alternating sum: a pair of entries -/

/-- The pair step: `AR += a.1 − b.1`, `AI += b.2 − a.2`, both entries moved `W0 → T`. -/
def pairBody : Prog AStk (fun _ => Sym) (KReg k) :=
  .seq (addI k .AR .W0 .AR') (.seq (kSym k (dropInt .AR)) (.seq (kSym k (mvInt .W0 .T))
  (.seq (subI k .AI .W0 .AI') (.seq (kSym k (dropInt .AI)) (.seq (kSym k (mvInt .W0 .T))
  (.seq (subI k .AR' .W0 .AR) (.seq (kSym k (dropInt .AR')) (.seq (kSym k (mvInt .W0 .T))
  (.seq (addI k .AI' .W0 .AI) (.seq (kSym k (dropInt .AI')) (kSym k (mvInt .W0 .T))))))))))))

theorem entrySyms_split (a : ℤ × ℤ) (l : List Sym) :
    entrySyms a ++ l = intSyms a.1 ++ Sym.sep2 :: (intSyms a.2 ++ Sym.sep :: l) := by
  simp [entrySyms]

theorem rs_pairBody {C : ℕ} (hok : W3Ok k C) (X : AStk → List Sym) (a b : ℤ × ℤ) (A B : ℤ)
    (rest Tb ARb AIb : List Sym) (hARb : TermOK ARb) (hAIb : TermOK AIb)
    (hAR'b : TermOK (X .AR')) (hAI'b : TermOK (X .AI'))
    (hW : X .W0 = entrySyms a ++ (entrySyms b ++ rest)) (hT : X .T = Tb)
    (hAR : X .AR = intSyms A ++ ARb) (hAI : X .AI = intSyms B ++ AIb) :
    Runs (pairBody k) X
      (Function.update (Function.update (Function.update (Function.update X .W0 rest) .T
        ((entrySyms b).reverse ++ ((entrySyms a).reverse ++ Tb))) .AR
          (intSyms (A + a.1 - b.1) ++ ARb)) .AI (intSyms (B - a.2 + b.2) ++ AIb))
      (fun _ => True)
      (C * (bitLen A.natAbs + bitLen a.1.natAbs + 1) +
        C * (bitLen B.natAbs + bitLen a.2.natAbs + 1) +
        C * (bitLen (A + a.1).natAbs + bitLen b.1.natAbs + 1) +
        C * (bitLen (B - a.2).natAbs + bitLen b.2.natAbs + 1) +
        3 * (bitLen A.natAbs + bitLen B.natAbs + bitLen (A + a.1).natAbs +
          bitLen (B - a.2).natAbs) +
        3 * (bitLen a.1.natAbs + bitLen a.2.natAbs + bitLen b.1.natAbs + bitLen b.2.natAbs) +
        44) := by
  -- step 1: AR' := A + a.1
  have e1 := rs_addI k hok.add (x := .AR) (y := .W0) (z := .AR')
    (embL3_inj k.hA (by decide) (by decide) (by decide) trivial trivial trivial) A a.1 ARb
    (Sym.sep2 :: (intSyms a.2 ++ Sym.sep :: (entrySyms b ++ rest))) X hARb (TermOK.cons rfl _)
    hAR (by rw [hW, entrySyms_split])
  set S1 := Function.update X .AR' (intSyms (A + a.1) ++ X .AR') with hS1
  have e2 := runs_lift (kS k) (rs_dropInt .AR A ARb S1 hARb (by simp [hS1, hAR]))
  set S2 := Function.update S1 .AR ARb with hS2
  have e3 := runs_lift (kS k) (rs_mvInt (src := AStk.W0) (dst := AStk.T) (by decide) a.1
    Sym.sep2 rfl (intSyms a.2 ++ Sym.sep :: (entrySyms b ++ rest)) S2
    (by simp [hS2, hS1, hW, entrySyms_split]))
  set S3 := Function.update (Function.update S2 .W0
    (intSyms a.2 ++ Sym.sep :: (entrySyms b ++ rest))) .T
    ((intSyms a.1 ++ [Sym.sep2]).reverse ++ S2 .T) with hS3
  -- step 2: AI' := B − a.2
  have e4 := rs_subI k hok.sub (x := .AI) (y := .W0) (z := .AI')
    (embL3_inj k.hS (by decide) (by decide) (by decide) trivial trivial trivial) B a.2 AIb
    (Sym.sep :: (entrySyms b ++ rest)) S3 hAIb (TermOK.cons rfl _)
    (by simp [hS3, hS2, hS1, hAI]) (by simp [hS3])
  set S4 := Function.update S3 .AI' (intSyms (B - a.2) ++ S3 .AI') with hS4
  have e5 := runs_lift (kS k) (rs_dropInt .AI B AIb S4 hAIb (by simp [hS4, hS3, hS2, hS1, hAI]))
  set S5 := Function.update S4 .AI AIb with hS5
  have e6 := runs_lift (kS k) (rs_mvInt (src := AStk.W0) (dst := AStk.T) (by decide) a.2
    Sym.sep rfl (entrySyms b ++ rest) S5 (by simp [hS5, hS4, hS3]))
  set S6 := Function.update (Function.update S5 .W0 (entrySyms b ++ rest)) .T
    ((intSyms a.2 ++ [Sym.sep]).reverse ++ S5 .T) with hS6
  -- step 3: AR := (A + a.1) − b.1
  have e7 := rs_subI k hok.sub (x := .AR') (y := .W0) (z := .AR)
    (embL3_inj k.hS (by decide) (by decide) (by decide) trivial trivial trivial) (A + a.1) b.1
    (X .AR') (Sym.sep2 :: (intSyms b.2 ++ Sym.sep :: rest)) S6 hAR'b (TermOK.cons rfl _)
    (by simp [hS6, hS5, hS4, hS3, hS2, hS1]) (by simp [hS6, entrySyms_split])
  set S7 := Function.update S6 .AR (intSyms (A + a.1 - b.1) ++ S6 .AR) with hS7
  have e8 := runs_lift (kS k) (rs_dropInt .AR' (A + a.1) (X .AR') S7 hAR'b
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1]))
  set S8 := Function.update S7 .AR' (X .AR') with hS8
  have e9 := runs_lift (kS k) (rs_mvInt (src := AStk.W0) (dst := AStk.T) (by decide) b.1
    Sym.sep2 rfl (intSyms b.2 ++ Sym.sep :: rest) S8 (by simp [hS8, hS7, hS6, entrySyms_split]))
  set S9 := Function.update (Function.update S8 .W0 (intSyms b.2 ++ Sym.sep :: rest)) .T
    ((intSyms b.1 ++ [Sym.sep2]).reverse ++ S8 .T) with hS9
  -- step 4: AI := (B − a.2) + b.2
  have e10 := rs_addI k hok.add (x := .AI') (y := .W0) (z := .AI)
    (embL3_inj k.hA (by decide) (by decide) (by decide) trivial trivial trivial) (B - a.2) b.2
    (X .AI') (Sym.sep :: rest) S9 hAI'b (TermOK.cons rfl _)
    (by simp [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]) (by simp [hS9])
  set S10 := Function.update S9 .AI (intSyms (B - a.2 + b.2) ++ S9 .AI) with hS10
  have e11 := runs_lift (kS k) (rs_dropInt .AI' (B - a.2) (X .AI') S10 hAI'b
    (by simp [hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1]))
  set S11 := Function.update S10 .AI' (X .AI') with hS11
  have e12 := runs_lift (kS k) (rs_mvInt (src := AStk.W0) (dst := AStk.T) (by decide) b.2
    Sym.sep rfl rest S11 (by simp [hS11, hS10, hS9]))
  refine runs_post (runs_seq e1 (runs_seq e2 (runs_seq e3 (runs_seq e4 (runs_seq e5
    (runs_seq e6 (runs_seq e7 (runs_seq e8 (runs_seq e9 (runs_seq e10 (runs_seq e11
      e12))))))))))) ?_ (by omega)
  funext x
  cases x <;> simp [hS11, hS10, hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, hT, entrySyms]

end Calls

#assert_std_axioms cdLoop_loopL cdLoop_runsL rs_mvIntOnly closed_mvIntOnly aScr_inj embL3_inj
  embL2_inj rs_addI rs_subI rs_addN rs_subN rs_shlV rs_shrV rs_shlS entrySyms_split rs_pairBody

end WP.W9b
