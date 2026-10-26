import WP.W5.State

/-!
# WP.W5.Prims — framework-level macros of the Toom-3 program (exact `Eval` lemmas)

All macros are `SProg L` (register `Option Sym`) built from framework atoms and seed macros; they
are lifted into the full register type through the lens `lR` (`liftR_eval`, `liftR_triple`).

| macro | effect | cost |
|---|---|---|
| `copyIP s d t1 t2` | `d += intSyms v` (copy of the signed top of `s`) | `7·|v| + 12` |
| `dropBitsP k` | pop the bit block of `k`, keep its terminator | `2·|blk| + 4` |
| `dropIP k` | pop the signed number on top of `k` | `2·|v| + 5` |
| `clrP k` | pop everything above the first `sep` of `k` (no `sep` above it) | `3·|syms| + 2` |
| `shr1P x` | `natSyms n ↦ natSyms (n / 2)` | `3` |
| `negP x` | `intSyms v ↦ intSyms (-v)` (zero stays `pos`) | `≤ 5` |
| `sfixP r x y` | `intSyms v ↦ intSyms (sgnFix a b v)` on `r`, signs read from `x`, `y` | `≤ 10` |
-/

namespace WP.W5

open TMFw TMFw.Contracts TMFw.Lib Computability

/-! ## Programs -/

/-- Copy the signed number on top of `s` onto `d` (temporaries `t1`, `t2` restored). -/
def copyIP (s d t1 t2 : L) : SProg L :=
  .seq (popR s) (.seq (pushR t1) (.seq (copyBlock s d t2) (.seq (popR t1) (.seq (pushR s)
    (pushR d)))))

/-- Pop the bit block on top of `k`, keeping its terminator. -/
def dropBitsP (k : L) : SProg L := .seq (popR k) (.seq (.loop optIsBit (popR k)) (restoreR k))

/-- Pop the signed number on top of `k`. -/
def dropIP (k : L) : SProg L := .seq (popR k) (dropBitsP k)

/-- Not a separator. -/
def notSep (r : Option Sym) : Bool := !decide (r = some Sym.sep)

/-- Pop everything above the first `sep` of `k`. -/
def clrP (k : L) : SProg L := .seq (peekR k) (.loop notSep (.seq (popR k) (peekR k)))

/-- Halve the unsigned number on top of `x` (drop its LSB). -/
def shr1P (x : L) : SProg L := .seq (peekR x) (.ite optIsBit (popR x) skip)

/-- Is the register `neg`? -/
def isNegR (r : Option Sym) : Bool := decide (r = some Sym.neg)

/-- Negate the signed number on top of `x`. -/
def negP (x : L) : SProg L :=
  .seq (popR x) (.ite isNegR (pushC x .pos)
    (.seq (peekR x) (.ite optIsBit (pushC x .neg) (pushC x .pos))))

/-- Negate the top of `r` iff exactly one of the tops of `x`, `y` is negative. -/
def sfixP (r x y : L) : SProg L :=
  .seq (peekR x) (.ite isNegR (.seq (peekR y) (.ite isNegR skip (negP r)))
    (.seq (peekR y) (.ite isNegR (negP r) skip)))

/-! ## Closedness -/

theorem copyIP_closed (s d t1 t2 : L) : (copyIP s d t1 t2).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyIP, copyBlock, moveBlock, moveBits, moveBitsBody,
    moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip]

theorem dropIP_closed (k : L) : (dropIP k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, dropIP, dropBitsP, popR, restoreR, pushR, skip]

theorem clrP_closed (k : L) : (clrP k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, clrP, popR, peekR]

theorem shr1P_closed (x : L) : (shr1P x).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, shr1P, popR, peekR, skip]

theorem sfixP_closed (r x y : L) : (sfixP r x y).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, sfixP, negP, popR, peekR, pushC, skip]

/-! ## Exact evaluations -/

theorem natSyms_zero : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]

theorem natSyms_pos (n : ℕ) (hn : 0 < n) :
    natSyms n = Sym.bit (decide (n % 2 = 1)) :: natSyms (n / 2) := by
  simp [natSyms, encodeNat_pos n hn]

theorem copyIP_eval {s d t1 t2 : L} (hsd : s ≠ d) (hs1 : s ≠ t1) (hs2 : s ≠ t2) (hd1 : d ≠ t1)
    (hd2 : d ≠ t2) (h12 : t1 ≠ t2) (ρ : List (SProg L)) (r : Option Sym) (v : ℤ)
    (rest : List Sym) (S : L → List Sym) (hrest : TermOK rest) (hS : S s = intSyms v ++ rest) :
    Eval ρ (copyIP s d t1 t2) ⟨r, S⟩
      ⟨some (sgnSym v), Function.update S d (intSyms v ++ S d)⟩ (7 * bitLen v.natAbs + 12) := by
  have hS' : S s = sgnSym v :: ((encodeNat v.natAbs).map Sym.bit ++ rest) := by rw [hS]; rfl
  have e1 : Eval ρ (popR s) ⟨r, S⟩
      ⟨some (sgnSym v), Function.update S s ((encodeNat v.natAbs).map Sym.bit ++ rest)⟩ 1 := by
    refine (Eval.pop ρ s (fun _ o => o) r S).of_eq ?_ rfl
    rw [hS']; rfl
  set S1 := Function.update S s ((encodeNat v.natAbs).map Sym.bit ++ rest) with hS1
  have e2 : Eval ρ (pushR t1) ⟨some (sgnSym v), S1⟩
      ⟨some (sgnSym v), Function.update S1 t1 (sgnSym v :: S1 t1)⟩ 1 :=
    (Eval.push ρ t1 (fun r => r.getD .sep) (some (sgnSym v)) S1).of_eq rfl rfl
  set S2 := Function.update S1 t1 (sgnSym v :: S1 t1) with hS2
  have hS2s : S2 s = (encodeNat v.natAbs).map Sym.bit ++ rest := by
    rw [hS2, Function.update_of_ne hs1, hS1, Function.update_self]
  have e3 := copyBlock_eval hsd hs2 hd2 ρ (some (sgnSym v)) (encodeNat v.natAbs) rest S2 hrest hS2s
  set S3 := Function.update S2 d ((encodeNat v.natAbs).map Sym.bit ++ S2 d) with hS3
  have hS3t1 : S3 t1 = sgnSym v :: S t1 := by
    rw [hS3, Function.update_of_ne (Ne.symm hd1), hS2, Function.update_self, hS1,
      Function.update_of_ne (Ne.symm hs1)]
  have e4 : Eval ρ (popR t1) ⟨some .mark, S3⟩
      ⟨some (sgnSym v), Function.update S3 t1 (S t1)⟩ 1 := by
    refine (Eval.pop ρ t1 (fun _ o => o) _ S3).of_eq ?_ rfl
    rw [hS3t1]; rfl
  set S4 := Function.update S3 t1 (S t1) with hS4
  have e5 : Eval ρ (pushR s) ⟨some (sgnSym v), S4⟩
      ⟨some (sgnSym v), Function.update S4 s (sgnSym v :: S4 s)⟩ 1 :=
    (Eval.push ρ s (fun r => r.getD .sep) _ S4).of_eq rfl rfl
  set S5 := Function.update S4 s (sgnSym v :: S4 s) with hS5
  have e6 : Eval ρ (pushR d) ⟨some (sgnSym v), S5⟩
      ⟨some (sgnSym v), Function.update S5 d (sgnSym v :: S5 d)⟩ 1 :=
    (Eval.push ρ d (fun r => r.getD .sep) _ S5).of_eq rfl rfl
  have hS5d : S5 d = (encodeNat v.natAbs).map Sym.bit ++ S d := by
    rw [hS5, Function.update_of_ne (Ne.symm hsd), hS4, Function.update_of_ne hd1, hS3,
      Function.update_self, hS2, Function.update_of_ne hd1, hS1, Function.update_of_ne (Ne.symm hsd)]
  have hS4s : S4 s = (encodeNat v.natAbs).map Sym.bit ++ rest := by
    rw [hS4, Function.update_of_ne hs1, hS3, Function.update_of_ne hsd, hS2s]
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))).of_eq ?_ ?_
  · congr 1
    funext k
    by_cases hkd : k = d
    · subst hkd
      rw [Function.update_self, Function.update_self, hS5d]
      rfl
    · rw [Function.update_of_ne hkd, Function.update_of_ne hkd]
      by_cases hks : k = s
      · subst hks
        rw [hS5, Function.update_self, hS4s, hS]
        rfl
      · rw [hS5, Function.update_of_ne hks]
        by_cases hk1 : k = t1
        · subst hk1
          rw [hS4, Function.update_self]
        · rw [hS4, Function.update_of_ne hk1, hS3, Function.update_of_ne hkd, hS2,
            Function.update_of_ne hk1, hS1, Function.update_of_ne hks]
  · simp only [bitLen]
    omega

theorem dropLoop_eval {k : L} (ρ : List (SProg L)) :
    ∀ (es : List Bool) (rest : List Sym) (S : L → List Sym), TermOK rest →
      S k = (es.map Sym.bit ++ rest).tail →
      Eval ρ (.loop optIsBit (popR k)) ⟨(es.map Sym.bit ++ rest).head?, S⟩
        ⟨rest.head?, Function.update S k rest.tail⟩ (2 * es.length + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    have hS' : S k = rest.tail := hS
    show (⟨rest.head?, S⟩ : SSt L) = ⟨rest.head?, Function.update S k rest.tail⟩
    rw [← hS', Function.update_eq_self]
  | e :: es, rest, S, hrest, hS => by
    have hS' : S k = es.map Sym.bit ++ rest := hS
    have hpop : Eval ρ (popR k) ⟨some (.bit e), S⟩
        ⟨(es.map Sym.bit ++ rest).head?, Function.update S k (es.map Sym.bit ++ rest).tail⟩ 1 := by
      refine (Eval.pop ρ k (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS']
    have ih := dropLoop_eval ρ es rest (Function.update S k (es.map Sym.bit ++ rest).tail) hrest
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) hpop ih).of_eq ?_ (by simp only [List.length_cons]; omega)
    rw [Function.update_idem]

theorem dropBits_eval {k : L} (ρ : List (SProg L)) (r : Option Sym) (es : List Bool)
    (rest : List Sym) (S : L → List Sym) (hrest : TermOK rest) (hS : S k = es.map Sym.bit ++ rest) :
    Eval ρ (dropBitsP k) ⟨r, S⟩ ⟨rest.head?, Function.update S k rest⟩ (2 * es.length + 4) := by
  have e1 : Eval ρ (popR k) ⟨r, S⟩
      ⟨(es.map Sym.bit ++ rest).head?, Function.update S k (es.map Sym.bit ++ rest).tail⟩ 1 := by
    refine (Eval.pop ρ k (fun _ o => o) r S).of_eq ?_ rfl
    rw [hS]
  have e2 := dropLoop_eval ρ es rest (Function.update S k (es.map Sym.bit ++ rest).tail) hrest
    (Function.update_self _ _ _)
  have e3 := restoreR_eval ρ k rest
    (Function.update (Function.update S k (es.map Sym.bit ++ rest).tail) k rest.tail)
    (Function.update_self _ _ _)
  refine (Eval.seq e1 (Eval.seq e2 e3)).of_eq ?_ (by omega)
  rw [Function.update_idem, Function.update_idem]

theorem dropIP_eval {k : L} (ρ : List (SProg L)) (r : Option Sym) (v : ℤ) (rest : List Sym)
    (S : L → List Sym) (hrest : TermOK rest) (hS : S k = intSyms v ++ rest) :
    Eval ρ (dropIP k) ⟨r, S⟩ ⟨rest.head?, Function.update S k rest⟩ (2 * bitLen v.natAbs + 5) := by
  have e1 : Eval ρ (popR k) ⟨r, S⟩
      ⟨some (sgnSym v), Function.update S k ((encodeNat v.natAbs).map Sym.bit ++ rest)⟩ 1 := by
    refine (Eval.pop ρ k (fun _ o => o) r S).of_eq ?_ rfl
    rw [hS]; rfl
  have e2 := dropBits_eval ρ (some (sgnSym v)) (encodeNat v.natAbs) rest
    (Function.update S k ((encodeNat v.natAbs).map Sym.bit ++ rest)) hrest
    (Function.update_self _ _ _)
  refine (Eval.seq e1 e2).of_eq ?_ (by simp only [bitLen]; omega)
  rw [Function.update_idem]

theorem clrLoop_eval {k : L} (ρ : List (SProg L)) :
    ∀ (syms rest : List Sym) (S : L → List Sym), Sym.sep ∉ syms →
      S k = syms ++ Sym.sep :: rest →
      Eval ρ (.loop notSep (.seq (popR k) (peekR k))) ⟨(syms ++ Sym.sep :: rest).head?, S⟩
        ⟨some Sym.sep, Function.update S k (Sym.sep :: rest)⟩ (3 * syms.length + 1)
  | [], rest, S, _, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    show (⟨some Sym.sep, S⟩ : SSt L) = ⟨some Sym.sep, Function.update S k (Sym.sep :: rest)⟩
    rw [← (show S k = Sym.sep :: rest from hS), Function.update_eq_self]
  | x :: syms, rest, S, hx, hS => by
    have hxs : x ≠ Sym.sep := fun h => hx (h ▸ List.mem_cons_self ..)
    have hsyms : Sym.sep ∉ syms := fun h => hx (List.mem_cons_of_mem _ h)
    have e1 : Eval ρ (popR k) ⟨some x, S⟩
        ⟨some x, Function.update S k (syms ++ Sym.sep :: rest)⟩ 1 := by
      refine (Eval.pop ρ k (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS]; rfl
    have e2 : Eval ρ (peekR k) ⟨some x, Function.update S k (syms ++ Sym.sep :: rest)⟩
        ⟨(syms ++ Sym.sep :: rest).head?, Function.update S k (syms ++ Sym.sep :: rest)⟩ 1 := by
      refine (Eval.peek ρ k (fun _ o => o) _ _).of_eq ?_ rfl
      rw [Function.update_self]
    have ih := clrLoop_eval ρ syms rest (Function.update S k (syms ++ Sym.sep :: rest)) hsyms
      (Function.update_self _ _ _)
    refine (Eval.loop_true ?_ (Eval.seq e1 e2) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    · show notSep (some x) = true
      simp [notSep, hxs]
    · rw [Function.update_idem]

theorem clr_eval {k : L} (ρ : List (SProg L)) (r : Option Sym) (syms rest : List Sym)
    (S : L → List Sym) (hsep : Sym.sep ∉ syms) (hS : S k = syms ++ Sym.sep :: rest) :
    Eval ρ (clrP k) ⟨r, S⟩ ⟨some Sym.sep, Function.update S k (Sym.sep :: rest)⟩
      (3 * syms.length + 2) := by
  have e1 : Eval ρ (peekR k) ⟨r, S⟩ ⟨(syms ++ Sym.sep :: rest).head?, S⟩ 1 := by
    refine (Eval.peek ρ k (fun _ o => o) r S).of_eq ?_ rfl
    rw [hS]
  exact (Eval.seq e1 (clrLoop_eval ρ syms rest S hsep hS)).of_eq rfl (by omega)

theorem shr1_eval {x : L} (ρ : List (SProg L)) (r : Option Sym) (n : ℕ) (rest : List Sym)
    (S : L → List Sym) (hrest : TermOK rest) (hS : S x = natSyms n ++ rest) :
    ∃ r', Eval ρ (shr1P x) ⟨r, S⟩ ⟨r', Function.update S x (natSyms (n / 2) ++ rest)⟩ 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [natSyms_zero, List.nil_append] at hS
    refine ⟨rest.head?, ?_⟩
    have e1 : Eval ρ (peekR x) ⟨r, S⟩ ⟨rest.head?, S⟩ 1 := by
      refine (Eval.peek ρ x (fun _ o => o) r S).of_eq ?_ rfl
      rw [hS]
    have e2 := Eval.ite_false (p := popR x) (q := (skip : SProg L)) (ρ := ρ) (c := optIsBit)
      (s := ⟨rest.head?, S⟩) (optIsBit_head?_of_termOK hrest) (skip_eval ρ _)
    refine (Eval.seq e1 e2).of_eq ?_ rfl
    rw [Nat.zero_div, natSyms_zero, List.nil_append, ← hS, Function.update_eq_self]
  · have hS' : S x = Sym.bit (decide (n % 2 = 1)) :: (natSyms (n / 2) ++ rest) := by
      rw [hS, natSyms_pos n hn]; rfl
    refine ⟨some (Sym.bit (decide (n % 2 = 1))), ?_⟩
    have e1 : Eval ρ (peekR x) ⟨r, S⟩ ⟨some (Sym.bit (decide (n % 2 = 1))), S⟩ 1 := by
      refine (Eval.peek ρ x (fun _ o => o) r S).of_eq ?_ rfl
      rw [hS']; rfl
    have e2 : Eval ρ (popR x) ⟨some (Sym.bit (decide (n % 2 = 1))), S⟩
        ⟨some (Sym.bit (decide (n % 2 = 1))), Function.update S x (natSyms (n / 2) ++ rest)⟩ 1 := by
      refine (Eval.pop ρ x (fun _ o => o) _ S).of_eq ?_ rfl
      rw [hS']; rfl
    exact (Eval.seq e1 (Eval.ite_true (by rfl) e2)).of_eq rfl rfl

theorem isNegR_sgn (a : ℤ) : isNegR (some (sgnSym a)) = decide (a < 0) := by
  unfold isNegR sgnSym
  by_cases h : a < 0 <;> simp [h]

theorem negP_eval {x : L} (ρ : List (SProg L)) (r : Option Sym) (v : ℤ) (rest : List Sym)
    (S : L → List Sym) (hrest : TermOK rest) (hS : S x = intSyms v ++ rest) :
    ∃ r' t, t ≤ 5 ∧ Eval ρ (negP x) ⟨r, S⟩ ⟨r', Function.update S x (intSyms (-v) ++ rest)⟩ t := by
  have e1 : Eval ρ (popR x) ⟨r, S⟩
      ⟨some (sgnSym v), Function.update S x (natSyms v.natAbs ++ rest)⟩ 1 := by
    refine (Eval.pop ρ x (fun _ o => o) r S).of_eq ?_ rfl
    rw [hS]; rfl
  set S1 := Function.update S x (natSyms v.natAbs ++ rest) with hS1
  rcases lt_trichotomy v 0 with hv | hv | hv
  · -- negative: push `pos`
    have hc : isNegR (some (sgnSym v)) = true := by rw [isNegR_sgn]; simp [hv]
    have e2 : Eval ρ (pushC x .pos) ⟨some (sgnSym v), S1⟩
        ⟨some (sgnSym v), Function.update S1 x (Sym.pos :: S1 x)⟩ 1 :=
      Eval.push ρ x (fun _ => .pos) _ S1
    have hneg : ¬ (-v < 0) := by omega
    have hI : intSyms (-v) = Sym.pos :: natSyms v.natAbs := by
      rw [intSyms_eq, Int.natAbs_neg]; unfold sgnSym; rw [if_neg hneg]
    have e : Eval ρ (negP x) ⟨r, S⟩
        ⟨some (sgnSym v), Function.update S x (intSyms (-v) ++ rest)⟩ 3 := by
      refine (Eval.seq e1 (Eval.ite_true hc e2)).of_eq ?_ rfl
      congr 1
      rw [hS1, Function.update_idem, Function.update_self, hI]
      rfl
    exact ⟨_, _, by omega, e⟩
  · -- zero: the magnitude is empty; push `pos`
    subst hv
    have hc : isNegR (some (sgnSym 0)) = false := by rw [isNegR_sgn]; simp
    have hS1x : S1 x = rest := by rw [hS1, Function.update_self]; simp [natSyms_zero]
    have e2 : Eval ρ (peekR x) ⟨some (sgnSym 0), S1⟩ ⟨rest.head?, S1⟩ 1 := by
      refine (Eval.peek ρ x (fun _ o => o) _ S1).of_eq ?_ rfl
      rw [hS1x]
    have e3 : Eval ρ (pushC x .pos) ⟨rest.head?, S1⟩
        ⟨rest.head?, Function.update S1 x (Sym.pos :: S1 x)⟩ 1 :=
      Eval.push ρ x (fun _ => .pos) _ S1
    have e : Eval ρ (negP x) ⟨r, S⟩
        ⟨rest.head?, Function.update S x (intSyms (-0) ++ rest)⟩ 5 := by
      refine (Eval.seq e1 (Eval.ite_false hc (Eval.seq e2
        (Eval.ite_false (optIsBit_head?_of_termOK hrest) e3)))).of_eq ?_ rfl
      congr 1
      rw [hS1, Function.update_idem, Function.update_self]
      simp [intSyms, sgnSym, natSyms_zero]
    exact ⟨_, _, le_refl 5, e⟩
  · -- positive: magnitude nonempty; push `neg`
    have hc : isNegR (some (sgnSym v)) = false := by rw [isNegR_sgn]; simp; omega
    have hpos : 0 < v.natAbs := by omega
    have hS1x : S1 x = Sym.bit (decide (v.natAbs % 2 = 1)) :: (natSyms (v.natAbs / 2) ++ rest) := by
      rw [hS1, Function.update_self, natSyms_pos _ hpos]; rfl
    have e2 : Eval ρ (peekR x) ⟨some (sgnSym v), S1⟩
        ⟨some (Sym.bit (decide (v.natAbs % 2 = 1))), S1⟩ 1 := by
      refine (Eval.peek ρ x (fun _ o => o) _ S1).of_eq ?_ rfl
      rw [hS1x]; rfl
    have e3 : Eval ρ (pushC x .neg) ⟨some (Sym.bit (decide (v.natAbs % 2 = 1))), S1⟩
        ⟨some (Sym.bit (decide (v.natAbs % 2 = 1))), Function.update S1 x (Sym.neg :: S1 x)⟩ 1 :=
      Eval.push ρ x (fun _ => .neg) _ S1
    have hI : intSyms (-v) = Sym.neg :: natSyms v.natAbs := by
      rw [intSyms_eq, Int.natAbs_neg]; unfold sgnSym; rw [if_pos (by omega)]
    have e : Eval ρ (negP x) ⟨r, S⟩
        ⟨some (Sym.bit (decide (v.natAbs % 2 = 1))), Function.update S x (intSyms (-v) ++ rest)⟩
        5 := by
      refine (Eval.seq e1 (Eval.ite_false hc (Eval.seq e2
        (Eval.ite_true (by rfl) e3)))).of_eq ?_ rfl
      congr 1
      rw [hS1, Function.update_idem, Function.update_self, hI]
      rfl
    exact ⟨_, _, le_refl 5, e⟩

theorem sfix_eval {r x y : L} (ρ : List (SProg L)) (reg : Option Sym) (a b v : ℤ)
    (ra rb rest : List Sym) (S : L → List Sym) (hx : S x = intSyms a ++ ra)
    (hy : S y = intSyms b ++ rb) (hrest : TermOK rest) (hr : S r = intSyms v ++ rest) :
    ∃ r' t, t ≤ 10 ∧ Eval ρ (sfixP r x y) ⟨reg, S⟩
      ⟨r', Function.update S r (intSyms (sgnFix a b v) ++ rest)⟩ t := by
  have e1 : Eval ρ (peekR x) ⟨reg, S⟩ ⟨some (sgnSym a), S⟩ 1 := by
    refine (Eval.peek ρ x (fun _ o => o) reg S).of_eq ?_ rfl
    rw [hx]; rfl
  have e2 : Eval ρ (peekR y) ⟨some (sgnSym a), S⟩ ⟨some (sgnSym b), S⟩ 1 := by
    refine (Eval.peek ρ y (fun _ o => o) _ S).of_eq ?_ rfl
    rw [hy]; rfl
  obtain ⟨rn, tn, htn, en⟩ := negP_eval ρ (some (sgnSym b)) v rest S hrest hr
  have hskip : Eval ρ (skip : SProg L) ⟨some (sgnSym b), S⟩
      ⟨some (sgnSym b), Function.update S r (intSyms v ++ rest)⟩ 1 := by
    refine (skip_eval ρ _).of_eq ?_ rfl
    rw [← hr, Function.update_eq_self]
  have ha := isNegR_sgn a
  have hb := isNegR_sgn b
  unfold sgnFix
  by_cases hA : a < 0 <;> by_cases hB : b < 0
  · rw [if_pos (by simp [hA, hB])]
    exact ⟨_, _, by omega, Eval.seq e1 (Eval.ite_true (by rw [ha]; simp [hA])
      (Eval.seq e2 (Eval.ite_true (by rw [hb]; simp [hB]) hskip)))⟩
  · rw [if_neg (by simp [hA, hB])]
    exact ⟨_, _, by omega, Eval.seq e1 (Eval.ite_true (by rw [ha]; simp [hA])
      (Eval.seq e2 (Eval.ite_false (by rw [hb]; simp [hB]) en)))⟩
  · rw [if_neg (by simp [hA, hB])]
    exact ⟨_, _, by omega, Eval.seq e1 (Eval.ite_false (by rw [ha]; simp [hA])
      (Eval.seq e2 (Eval.ite_true (by rw [hb]; simp [hB]) en)))⟩
  · rw [if_pos (by simp [hA, hB])]
    exact ⟨_, _, by omega, Eval.seq e1 (Eval.ite_false (by rw [ha]; simp [hA])
      (Eval.seq e2 (Eval.ite_false (by rw [hb]; simp [hB]) hskip)))⟩

/-! ## Lifting into the full register type -/

theorem liftR_eval {U : Subs} {p : SProg L} (hc : p.Closed) {r r' : Option Sym}
    {S S' : L → List Sym} {t : ℕ} (h : Eval [] p ⟨r, S⟩ ⟨r', S'⟩ t) (v : U.σ)
    (hv : (lR U).get v = r) (ρ : List (Prog L (fun _ => Sym) U.σ)) :
    Eval ρ (p.liftRegs (lR U)) ⟨v, S⟩ ⟨(lR U).set v r', S'⟩ t :=
  (Eval.liftRegs (lR U) h v hv).env_irrel (closed_liftRegs _ hc) ρ

/-- A framework macro that maps stacks `S` to `S'` from every register value is a triple. -/
theorem liftR_triple {U : Subs} {p : SProg L} (hc : p.Closed) {S S' : L → List Sym} {t : ℕ}
    (h : ∀ r, ∃ r' t', t' ≤ t ∧ Eval [] p ⟨r, S⟩ ⟨r', S'⟩ t')
    (ρ : List (Prog L (fun _ => Sym) U.σ)) :
    Triple ρ (fun s => s.stk = S) (p.liftRegs (lR U)) (fun s => s.stk = S') t := by
  rintro ⟨v, stk⟩ hs
  change stk = S at hs
  subst hs
  obtain ⟨r', t', ht, e⟩ := h ((lR U).get v)
  exact ⟨_, t', liftR_eval hc e v rfl ρ, rfl, ht⟩

#assert_std_axioms copyIP_eval dropIP_eval clr_eval shr1_eval negP_eval sfix_eval liftR_eval
  liftR_triple copyIP_closed dropIP_closed clrP_closed shr1P_closed sfixP_closed

end WP.W5
