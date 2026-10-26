import WP.W9comp.Kit
import WP.W7pure.Basic
import IntMulTM.Framework.Lib.Counter

/-!
# WP.W9mp.Glue — header glue of the root composite

`W9_pipeline` reads its input precision from the top of `C1` (`hdrSyms [p_in]`), while
`W9_multiply` only promises the root header `hdrSyms [b, K0, k1, k2]` on `C0` (and must restore `C1`).
The composite therefore pushes `b` (forward transform) and `p0 = rootPrecision b K0 = 2(b + K0 + 3)`
(inverse transform) onto `C1` and pops them afterwards. All glue is built from the framework's
exact-evaluation programs (`copyBlock`, `inc`, `dec`, `zeroTest`) and W9comp's `rewindTo`:

* `pushB C0 C1 X`: `C1 := hdrSyms [b] ++ C1` (copy of the first header field);
* `dropTo k g`: pop `k` down to and including the first `g` (header pop);
* `addLoop X Y T`: `Y += X`, consuming the counter `X` (`while X ≠ 0 { dec X; inc Y }`);
* `pushP0 C0 C1 X Y T`: `C1 := hdrSyms [rootPrecision b K0] ++ C1`, cost `≤ 100·(b+K0+1)·(K0+1)`.

Every lemma is an exact `Runs` (all other stacks restored, scratch included).
-/

namespace WP.W9mp

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Symbol facts -/

theorem mark_not_mem_natSyms (n : ℕ) : Sym.mark ∉ natSyms n := by
  simp [natSyms]

theorem guard_not_mem_natSyms (n : ℕ) : symGuard ∉ natSyms n := by
  simp [natSyms, symGuard]

theorem termOK_mark (l : List Sym) : TermOK (Sym.mark :: l) := TermOK.cons (by rfl) _

theorem natSyms_double (x : ℕ) (hx : x ≠ 0) : natSyms (x + x) = .bit false :: natSyms x := by
  have hne : encodeNat x ≠ [] := by rwa [Ne, encodeNat_eq_nil_iff]
  simp only [natSyms]
  rw [encodeNat_add, if_neg hne]
  rfl

theorem hdrSyms_cons (n : ℕ) (fs : List ℕ) :
    hdrSyms (n :: fs) = natSyms n ++ Sym.mark :: hdrSyms fs := by
  simp [hdrSyms]

section Glue

variable {K : Type} [DecidableEq K]

/-! ## Registers through a lens -/

theorem runs_liftRegs {σ τ : Type} (l : Lens σ τ) {P : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ} (h : Runs P S S' Q T) :
    Runs (P.liftRegs l) S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := h ⟨l.get v, stk⟩ rfl
  exact ⟨⟨l.set v s'.var, s'.stk⟩, t, Eval.liftRegs l e v rfl, ⟨hs', trivial⟩, ht⟩

/-! ## Primitive steps as `Runs` -/

theorem runs_pushC (k : K) (x : Sym) (S : K → List Sym) :
    Runs (pushC k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 := by
  refine Runs.of_eval fun v => ⟨v, 1, ?_, trivial, le_refl _⟩
  exact Eval.push (Γ := fun _ => Sym) [] k (fun _ => x) v S

theorem runs_popR (k : K) (x : Sym) (rest : List Sym) (S : K → List Sym) (hS : S k = x :: rest) :
    Runs (popR k) S (Function.update S k rest) (fun _ => True) 1 := by
  refine Runs.of_eval fun v => ⟨some x, 1, ?_, trivial, le_refl _⟩
  have h := Eval.pop (Γ := fun _ => Sym) [] k (fun (_ : Option Sym) o => o) v S
  rw [hS] at h
  exact h

theorem runs_copyBlock {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (a : ℕ) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = natSyms a ++ rest) :
    Runs (copyBlock src dst tmp) S (Function.update S dst (natSyms a ++ S dst)) (fun _ => True)
      (7 * bitLen a + 7) :=
  Runs.of_eval fun v =>
    ⟨_, _, copyBlock_eval hsd hst hdt [] v (encodeNat a) rest S hrest hS, trivial, le_refl _⟩

theorem runs_rewindTo {src dst : K} (hne : src ≠ dst) (g : Sym) (L rest : List Sym)
    (S : K → List Sym) (hg : g ∉ L) (hS : S src = L ++ g :: rest) :
    Runs (WP.W9comp.rewindTo src dst g) S
      (Function.update (Function.update S src rest) dst (L.reverse ++ S dst)) (fun _ => True)
      (3 * L.length + 2) :=
  Runs.of_eval fun v =>
    ⟨_, _, WP.W9comp.rewindTo_eval hne g v L rest S hg hS, trivial, le_refl _⟩

theorem runs_inc {k t : K} (hkt : k ≠ t) (a : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms a ++ rest) :
    Runs (inc k t) S (Function.update S k (natSyms (a + 1) ++ rest)) (fun _ => True)
      (6 * a + 9) := by
  refine Runs.of_eval fun v => ?_
  obtain ⟨c, hc, e⟩ := inc_eval hkt [] v (encodeNat a) rest S hrest hS
  have h1 := ones_le_length (encodeNat a)
  have h2 : (encodeNat a).length ≤ a := WP.W7pure.bitLen_le_self a
  refine ⟨some .mark, c, ?_, trivial, by omega⟩
  rw [natSyms, encodeNat_succ]
  exact e

/-! ## dropTo -/

/-- Pop `k` down to and including the first `g`. -/
def dropTo (k : K) (g : Sym) : SProg K := .seq (popR k) (.loop (WP.W9comp.notG g) (popR k))

theorem dropTo_loop_eval {k : K} (g : Sym) :
    ∀ (L rest : List Sym) (S : K → List Sym), g ∉ L → S k = (L ++ g :: rest).tail →
      Eval [] (.loop (WP.W9comp.notG g) (popR k)) ⟨(L ++ g :: rest).head?, S⟩
        ⟨some g, Function.update S k rest⟩ (2 * L.length + 1)
  | [], rest, S, _, hS => by
    refine (Eval.loop_false (by simp [WP.W9comp.notG])).of_eq ?_ rfl
    have hS' : S k = rest := hS
    show (⟨some g, S⟩ : SSt K) = ⟨some g, Function.update S k rest⟩
    rw [← hS', Function.update_eq_self]
  | x :: L, rest, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self ..)
    have hg' : g ∉ L := fun h => hg (List.mem_cons_of_mem _ h)
    have hS' : S k = L ++ g :: rest := hS
    have hpop : Eval [] (popR k) ⟨some x, S⟩
        ⟨(L ++ g :: rest).head?, Function.update S k (L ++ g :: rest).tail⟩ 1 := by
      refine (Eval.pop [] k (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hS']
    have ih := dropTo_loop_eval g L rest (Function.update S k (L ++ g :: rest).tail) hg'
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by simp [WP.W9comp.notG, hx]) hpop ih).of_eq ?_ ?_
    · rw [Function.update_idem]
    · simp only [List.length_cons]
      omega

theorem dropTo_eval {k : K} (g : Sym) (v : Option Sym) (L rest : List Sym) (S : K → List Sym)
    (hg : g ∉ L) (hS : S k = L ++ g :: rest) :
    Eval [] (dropTo k g) ⟨v, S⟩ ⟨some g, Function.update S k rest⟩ (2 * L.length + 2) := by
  have h1 : Eval [] (popR k) ⟨v, S⟩
      ⟨(L ++ g :: rest).head?, Function.update S k (L ++ g :: rest).tail⟩ 1 := by
    refine (Eval.pop [] k (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := dropTo_loop_eval g L rest (Function.update S k (L ++ g :: rest).tail) hg
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  rw [Function.update_idem]

/-- **Header pop**: `k = hdrSyms [n] ++ rest ↦ rest`. -/
theorem runs_popHdr (k : K) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hS : S k = hdrSyms [n] ++ rest) :
    Runs (dropTo k .mark) S (Function.update S k rest) (fun _ => True) (2 * bitLen n + 2) := by
  refine Runs.of_eval fun v => ⟨_, _, dropTo_eval .mark v (natSyms n) rest S
    (mark_not_mem_natSyms n) (by rw [hS]; simp [hdrSyms]), trivial, ?_⟩
  rw [length_natSyms]

omit [DecidableEq K] in
theorem closed_dropTo (k : K) (g : Sym) : (dropTo k g).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, dropTo, popR]

/-! ## addLoop -/

/-- Loop body: decrement `X`, increment `Y`, test `X`. -/
def addBody (X Y T : K) : SProg K := .seq (dec X T) (.seq (inc Y T) (zeroTest X))

/-- `Y += X`, consuming `X` down to zero. -/
def addLoop (X Y T : K) : SProg K := .seq (zeroTest X) (.loop optIsBit (addBody X Y T))

theorem addLoop_loop_eval {X Y T : K} (hXY : X ≠ Y) (hXT : X ≠ T) (hYT : Y ≠ T)
    (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry) :
    ∀ (j v : ℕ) (r : Option Sym) (S : K → List Sym), optIsBit r = !decide (j = 0) →
      S X = natSyms j ++ rx → S Y = natSyms v ++ ry →
      ∃ r' t, Eval [] (.loop optIsBit (addBody X Y T)) ⟨r, S⟩
        ⟨r', Function.update (Function.update S X rx) Y (natSyms (v + j) ++ ry)⟩ t ∧
        t ≤ j * (12 * j + 6 * v + 32) + 1
  | 0, v, r, S, hr, hX, hY => by
    refine ⟨r, 1, (Eval.loop_false (by simpa using hr)).of_eq ?_ rfl, by omega⟩
    have hX' : S X = rx := by simpa [natSyms, encodeNat_zero] using hX
    congr 1
    rw [Nat.add_zero, ← hY, ← hX', Function.update_eq_self, Function.update_eq_self]
  | j + 1, v, r, S, hr, hX, hY => by
    have e1 := dec_eval (k := X) (t := T) hXT [] r j rx S hrx hX
    have hY1 : Function.update S X ((encodeNat j).map Sym.bit ++ rx) Y =
        (encodeNat v).map Sym.bit ++ ry := by
      rw [Function.update_of_ne (Ne.symm hXY)]
      exact hY
    obtain ⟨c2, hc2, e2⟩ := inc_eval (k := Y) (t := T) hYT [] (some .mark) (encodeNat v) ry
      (Function.update S X ((encodeNat j).map Sym.bit ++ rx)) hry hY1
    have hX2 : Function.update (Function.update S X ((encodeNat j).map Sym.bit ++ rx)) Y
        ((incBits (encodeNat v)).map Sym.bit ++ ry) X = natSyms j ++ rx := by
      rw [Function.update_of_ne hXY, Function.update_self]
      rfl
    obtain ⟨r3, hr3, e3⟩ := zeroTest_eval (k := X) [] (some .mark) j rx _ hrx hX2
    have hY2 : Function.update (Function.update S X ((encodeNat j).map Sym.bit ++ rx)) Y
        ((incBits (encodeNat v)).map Sym.bit ++ ry) Y = natSyms (v + 1) ++ ry := by
      rw [Function.update_self, natSyms, encodeNat_succ]
    obtain ⟨r', t, e4, ht⟩ := addLoop_loop_eval hXY hXT hYT rx ry hrx hry j (v + 1) r3 _ hr3
      hX2 hY2
    refine ⟨r', _, (Eval.loop_true (by simpa using hr) (Eval.seq e1 (Eval.seq e2 e3)) e4).of_eq
      ?_ rfl, ?_⟩
    · congr 1
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all [Nat.add_right_comm v 1 j, Nat.add_assoc]
    · have h1 := zerosLead_le_length (encodeNat (j + 1))
      have h2 : (encodeNat (j + 1)).length ≤ j + 1 := WP.W7pure.bitLen_le_self (j + 1)
      have h3 := ones_le_length (encodeNat v)
      have h4 : (encodeNat v).length ≤ v := WP.W7pure.bitLen_le_self v
      nlinarith

theorem runs_addLoop {X Y T : K} (hXY : X ≠ Y) (hXT : X ≠ T) (hYT : Y ≠ T)
    (j v : ℕ) (rx ry : List Sym) (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hX : S X = natSyms j ++ rx) (hY : S Y = natSyms v ++ ry) :
    Runs (addLoop X Y T) S (Function.update (Function.update S X rx) Y (natSyms (v + j) ++ ry))
      (fun _ => True) (j * (12 * j + 6 * v + 32) + 2) := by
  refine Runs.of_eval fun r0 => ?_
  obtain ⟨r, hr, e0⟩ := zeroTest_eval (k := X) [] r0 j rx S hrx hX
  obtain ⟨r', t, e, ht⟩ := addLoop_loop_eval hXY hXT hYT rx ry hrx hry j v r S hr hX hY
  exact ⟨r', 1 + t, Eval.seq e0 e, trivial, by omega⟩

end Glue

#assert_std_axioms mark_not_mem_natSyms guard_not_mem_natSyms termOK_mark natSyms_double
  hdrSyms_cons runs_liftRegs runs_pushC runs_popR runs_copyBlock runs_rewindTo runs_inc
  dropTo_loop_eval dropTo_eval runs_popHdr closed_dropTo addLoop_loop_eval runs_addLoop

end WP.W9mp
