import WP.W9g.Base
import Contracts.W9.Common

/-!
# WP.W9g.Macros — entry and number macros (generic in the stack type)

Entries are pair records `entrySyms (a, b) = intSyms a ++ sep2 :: intSyms b ++ [sep]`
(`Contracts.W9.Common`). Every macro here is an `SProg K` (one `Option Sym` register) with an exact
`Eval` lemma, valid from every register value, in every procedure environment.

| macro | effect | cost |
|---|---|---|
| `emove src dst t` | move the top entry of `src` onto `dst`, same orientation | `6·|e| + 3` |
| `copyEntry src dst t` | copy the top entry of `src` onto `dst` | `7·|e| + 3` |
| `dropEntry k` | pop the top entry (any record) of `k` | `2·|e|` |
| `copyInt src dst t` | copy the signed number on top of `src` onto `dst` | `7·|z| + 12` |
| `dropInt k` | pop the signed number on top of `k` | `3·|z| + 3` |
| `copyIm src dst t1 t2` | copy the second coordinate of the top entry of `src` onto `dst` | `6|a| + 7|b| + 29` |
| `packEntry nre nim dst t` | push the entry `(re, im)` read from two number stacks onto `dst` | `7|re| + 7|im| + 26` |

Temporaries (`t`, `t1`, `t2`) get a `mark` pushed first and consumed, so they may hold anything.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Symbols -/

/-- Register is not `mark` (and not empty). -/
def notMarkR : Option Sym → Bool
  | some .mark => false
  | some _ => true
  | none => false

/-- Data symbols are not `mark`. -/
theorem notMarkR_of_data {y : Sym} (h : isDataSym y = true) : notMarkR (some y) = true := by
  cases y <;> simp_all [isDataSym, notMarkR]

/-- Payload of an entry (everything before the final `sep`). -/
def entryData (z : ℤ × ℤ) : List Sym := intSyms z.1 ++ Sym.sep2 :: intSyms z.2

theorem entrySyms_eq (z : ℤ × ℤ) : entrySyms z = entryData z ++ [Sym.sep] := by
  simp [entrySyms, entryData]

theorem isData_entryData (z : ℤ × ℤ) : ∀ y ∈ entryData z, isDataSym y = true := by
  intro y hy
  simp only [entryData, List.mem_append, List.mem_cons] at hy
  rcases hy with h | rfl | h
  · exact isData_intSyms _ y h
  · rfl
  · exact isData_intSyms _ y h

theorem length_entryData (z : ℤ × ℤ) :
    (entryData z).length = bitLen z.1.natAbs + bitLen z.2.natAbs + 3 := by
  simp only [entryData, intSyms, List.length_append, List.length_cons, length_natSyms]
  omega

theorem notMark_rev_entry (z : ℤ × ℤ) :
    ∀ y ∈ Sym.sep :: (entryData z).reverse, notMarkR (some y) = true := by
  intro y hy
  simp only [List.mem_cons, List.mem_reverse] at hy
  rcases hy with rfl | h
  · rfl
  · exact notMarkR_of_data (isData_entryData z y h)

theorem moveRec_closed {K : Type} (src dst : K) : (moveRec src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, Lib.pushR, Lib.popR]

/-! ## Generic drop loop -/

section Drop

variable {K : Type} [DecidableEq K]

theorem drop_loop_eval (k : K) (c : Option Sym → Bool) (ρ : List (SProg K)) :
    ∀ (l : List Sym) (s0 : Sym) (rest : List Sym) (S : K → List Sym),
      (∀ y ∈ l, c (some y) = true) → c (some s0) = false →
      S k = (l ++ s0 :: rest).tail →
      Eval ρ (.loop c (popR k)) ⟨(l ++ s0 :: rest).head?, S⟩
        ⟨some s0, Function.update S k rest⟩ (2 * l.length + 1)
  | [], s0, rest, S, _, hs0, hS => by
    refine (Eval.loop_false hs0).of_eq ?_ rfl
    have hS' : S k = rest := hS
    show (⟨some s0, S⟩ : SSt K) = ⟨some s0, Function.update S k rest⟩
    rw [← hS', Function.update_eq_self]
  | x :: l, s0, rest, S, hl, hs0, hS => by
    have hx : c (some x) = true := hl x (by simp)
    have hl' : ∀ y ∈ l, c (some y) = true := fun y hy => hl y (by simp [hy])
    have hS' : S k = l ++ s0 :: rest := hS
    have hpop : Eval ρ (popR k) ⟨some x, S⟩
        ⟨(l ++ s0 :: rest).head?, Function.update S k (l ++ s0 :: rest).tail⟩ 1 := by
      refine (Eval.pop ρ k (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hS']
    have ih := drop_loop_eval k c ρ l s0 rest (Function.update S k (l ++ s0 :: rest).tail) hl' hs0
      (Function.update_self _ _ _)
    refine (Eval.loop_true hx hpop ih).of_eq ?_ ?_
    · rw [Function.update_idem]
    · simp only [List.length_cons]
      omega

end Drop

/-! ## Entry macros -/

section Entry

variable {K : Type}

/-- Move the top entry of `src` onto `dst`, keeping its orientation (via `t`). -/
def emove (src dst t : K) : SProg K :=
  .seq (pushC t .mark) (.seq (moveRec src t) (xferUntil t dst notMarkR))

/-- Copy the top entry of `src` onto `dst` (via `t`); `src` unchanged. -/
def copyEntry (src dst t : K) : SProg K :=
  .seq (pushC t .mark) (.seq (moveRec src t) (dupUntil t src dst notMarkR))

/-- Pop the top record of `k` (payload and final `sep`). -/
def dropEntry (k : K) : SProg K := .seq (popR k) (.loop isDataR (popR k))

/-- Copy the signed number on `src` onto `dst` (same order), using `tmp` (restored). -/
def copyInt (src dst tmp : K) : SProg K :=
  .seq (popR src) (.seq (pushR tmp) (.seq (copyBlock src dst tmp)
    (.seq (popR tmp) (.seq (pushR src) (pushR dst)))))

/-- Pop the signed number on top of `k`, keeping its terminator. -/
def dropInt (k : K) : SProg K := .seq (popR k) (WP.W6a.dropBits k)

/-- Copy the second coordinate of the top entry of `src` onto `dst` (temporaries `t1`, `t2`). -/
def copyIm (src dst t1 t2 : K) : SProg K :=
  .seq (pushC t1 .mark) (.seq (popR src) (.seq (pushR t1) (.seq (moveBlock src t1)
    (.seq (popR src) (.seq (pushR t1) (.seq (copyInt src dst t2) (xferUntil t1 src notMarkR)))))))

/-- Push the entry `(re, im)` read from the number stacks `nre`, `nim` onto `dst`. -/
def packEntry (nre nim dst tmp : K) : SProg K :=
  .seq (pushC dst .sep) (.seq (copyInt nim dst tmp) (.seq (pushC dst .sep2) (copyInt nre dst tmp)))

theorem emove_closed (src dst t : K) : (emove src dst t).Closed :=
  ⟨trivial, moveRec_closed src t, xferUntil_closed t dst notMarkR⟩

theorem copyEntry_closed (src dst t : K) : (copyEntry src dst t).Closed :=
  ⟨trivial, moveRec_closed src t, dupUntil_closed t src dst notMarkR⟩

theorem dropEntry_closed (k : K) : (dropEntry k).Closed := ⟨trivial, trivial⟩

theorem copyInt_closed (src dst tmp : K) : (copyInt src dst tmp).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, copyInt, copyBlock, moveBlock, moveBits, moveBitsBody,
    moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip]

theorem dropInt_closed (k : K) : (dropInt k).Closed := ⟨trivial, WP.W6a.closed_dropBits k⟩

theorem moveBlock_closed (src dst : K) : (moveBlock src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveBlock, moveBits, moveBitsBody, pushR, popR, restoreR,
    skip]

theorem copyIm_closed (src dst t1 t2 : K) : (copyIm src dst t1 t2).Closed :=
  ⟨trivial, trivial, trivial, moveBlock_closed src t1, trivial, trivial, copyInt_closed _ _ _,
    xferUntil_closed _ _ _⟩

theorem packEntry_closed (nre nim dst tmp : K) : (packEntry nre nim dst tmp).Closed :=
  ⟨trivial, copyInt_closed _ _ _, trivial, copyInt_closed _ _ _⟩

variable [DecidableEq K]

/-- **emove**, exact. -/
theorem emove_eval {src dst t : K} (hsd : src ≠ dst) (hst : src ≠ t) (hdt : dst ≠ t)
    (ρ : List (SProg K)) (v : Option Sym) (z : ℤ × ℤ) (rest : List Sym) (S : K → List Sym)
    (hS : S src = entrySyms z ++ rest) :
    Eval ρ (emove src dst t) ⟨v, S⟩
      ⟨some .mark, Function.update (Function.update S src rest) dst (entrySyms z ++ S dst)⟩
      (6 * (entrySyms z).length + 3) := by
  set d := entryData z with hd
  have e1 : Eval ρ (pushC t .mark) ⟨v, S⟩ ⟨v, Function.update S t (.mark :: S t)⟩ 1 :=
    Eval.push ρ t (fun _ => .mark) v S
  set S1 := Function.update S t (.mark :: S t) with hS1
  have e2 := moveRec_eval (src := src) (dst := t) hst v d rest S1 (isData_entryData z)
    (by rw [hS1, Function.update_of_ne hst, hS, entrySyms_eq, List.append_assoc]; rfl)
  set S2 := Function.update (Function.update S1 src rest) t (Sym.sep :: (d.reverse ++ S1 t))
    with hS2
  have e3 := xferUntil_eval (Ne.symm hdt) notMarkR ρ (some .sep) (Sym.sep :: d.reverse) .mark
    (S t) S2 (notMark_rev_entry z) rfl
    (by rw [hS2, Function.update_self, hS1, Function.update_self]; rfl)
  refine (Eval.seq e1 (Eval.seq (e2.env_irrel (moveRec_closed src t) ρ) e3)).of_eq ?_ ?_
  · congr 1
    have hrev : (Sym.sep :: d.reverse).reverse = entrySyms z := by
      rw [List.reverse_cons, List.reverse_reverse, entrySyms_eq]
    rw [hrev]
    funext k
    simp only [hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [hd, List.length_cons, List.length_nil, List.length_reverse, entrySyms_eq,
      List.length_append]
    omega

theorem emove_rs {τ : Type} {src dst t : K} (hsd : src ≠ dst) (hst : src ≠ t) (hdt : dst ≠ t)
    (z : ℤ × ℤ) (rest : List Sym) (S : K → List Sym) (hS : S src = entrySyms z ++ rest) :
    RS [] (lm (emove src dst t) : MProg K τ) S
      (Function.update (Function.update S src rest) dst (entrySyms z ++ S dst))
      (6 * (entrySyms z).length + 3) :=
  rs_lm (RS.of_eval_exact (fun v => ⟨_, emove_eval hsd hst hdt [] v z rest S hS⟩) le_rfl)

/-- **copyEntry**, exact: only `dst` changes. -/
theorem copyEntry_eval {src dst t : K} (hsd : src ≠ dst) (hst : src ≠ t) (hdt : dst ≠ t)
    (ρ : List (SProg K)) (v : Option Sym) (z : ℤ × ℤ) (rest : List Sym) (S : K → List Sym)
    (hS : S src = entrySyms z ++ rest) :
    Eval ρ (copyEntry src dst t) ⟨v, S⟩
      ⟨some .mark, Function.update S dst (entrySyms z ++ S dst)⟩
      (7 * (entrySyms z).length + 3) := by
  set d := entryData z with hd
  have e1 : Eval ρ (pushC t .mark) ⟨v, S⟩ ⟨v, Function.update S t (.mark :: S t)⟩ 1 :=
    Eval.push ρ t (fun _ => .mark) v S
  set S1 := Function.update S t (.mark :: S t) with hS1
  have e2 := moveRec_eval (src := src) (dst := t) hst v d rest S1 (isData_entryData z)
    (by rw [hS1, Function.update_of_ne hst, hS, entrySyms_eq, List.append_assoc]; rfl)
  set S2 := Function.update (Function.update S1 src rest) t (Sym.sep :: (d.reverse ++ S1 t))
    with hS2
  have e3 := dupUntil_eval (Ne.symm hst) (Ne.symm hdt) hsd notMarkR ρ (some .sep)
    (Sym.sep :: d.reverse) .mark (S t) S2 (notMark_rev_entry z) rfl
    (by rw [hS2, Function.update_self, hS1, Function.update_self]; rfl)
  refine (Eval.seq e1 (Eval.seq (e2.env_irrel (moveRec_closed src t) ρ) e3)).of_eq ?_ ?_
  · congr 1
    have hrev : (Sym.sep :: d.reverse).reverse = entrySyms z := by
      rw [List.reverse_cons, List.reverse_reverse, entrySyms_eq]
    rw [hrev]
    funext k
    simp only [hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [hd, List.length_cons, List.length_nil, List.length_reverse, entrySyms_eq,
      List.length_append]
    omega

theorem copyEntry_rs {τ : Type} {src dst t : K} (hsd : src ≠ dst) (hst : src ≠ t)
    (hdt : dst ≠ t) (z : ℤ × ℤ) (rest : List Sym) (S : K → List Sym)
    (hS : S src = entrySyms z ++ rest) :
    RS [] (lm (copyEntry src dst t) : MProg K τ) S
      (Function.update S dst (entrySyms z ++ S dst)) (7 * (entrySyms z).length + 3) :=
  rs_lm (RS.of_eval_exact (fun v => ⟨_, copyEntry_eval hsd hst hdt [] v z rest S hS⟩) le_rfl)

/-- **dropEntry**, exact, for any record `d ++ [sep]`. -/
theorem dropEntry_eval_rec (k : K) (ρ : List (SProg K)) (v : Option Sym) (d rest : List Sym)
    (S : K → List Sym) (hd : ∀ y ∈ d, isDataSym y = true) (hS : S k = d ++ Sym.sep :: rest) :
    Eval ρ (dropEntry k) ⟨v, S⟩ ⟨some .sep, Function.update S k rest⟩ (2 * d.length + 2) := by
  have h1 : Eval ρ (popR k) ⟨v, S⟩
      ⟨(d ++ Sym.sep :: rest).head?, Function.update S k (d ++ Sym.sep :: rest).tail⟩ 1 := by
    refine (Eval.pop ρ k (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := drop_loop_eval k isDataR ρ d .sep rest (Function.update S k (d ++ Sym.sep :: rest).tail)
    (fun y hy => by simp [isDataR, hd y hy]) rfl (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  rw [Function.update_idem]

theorem dropEntry_rs {τ : Type} (k : K) (z : ℤ × ℤ) (rest : List Sym) (S : K → List Sym)
    (hS : S k = entrySyms z ++ rest) :
    RS [] (lm (dropEntry k) : MProg K τ) S (Function.update S k rest)
      (2 * (entrySyms z).length) := by
  refine rs_lm (RS.of_eval_exact (fun v => ⟨_, dropEntry_eval_rec k [] v (entryData z) rest S
    (isData_entryData z) (by rw [hS, entrySyms_eq, List.append_assoc]; rfl)⟩) ?_)
  rw [entrySyms_eq, List.length_append, List.length_singleton]
  omega

theorem intSyms_append (z : ℤ) (r : List Sym) :
    intSyms z ++ r = sgnSym z :: ((encodeNat z.natAbs).map Sym.bit ++ r) := rfl

/-- **copyInt**, exact: only `dst` changes. -/
theorem copyInt_eval {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (ρ : List (SProg K)) (v : Option Sym) (z : ℤ) (r : List Sym) (S : K → List Sym)
    (hr : TermOK r) (hS : S src = intSyms z ++ r) :
    Eval ρ (copyInt src dst tmp) ⟨v, S⟩
      ⟨some (sgnSym z), Function.update S dst (intSyms z ++ S dst)⟩
      (7 * bitLen z.natAbs + 12) := by
  have e1 : Eval ρ (popR src) ⟨v, S⟩
      ⟨some (sgnSym z), Function.update S src ((encodeNat z.natAbs).map Sym.bit ++ r)⟩ 1 := by
    have h := Eval.pop ρ src (fun _ o => o) v S
    rw [hS] at h
    exact h
  set S1 := Function.update S src ((encodeNat z.natAbs).map Sym.bit ++ r) with hS1
  have e2 : Eval ρ (pushR tmp) ⟨some (sgnSym z), S1⟩
      ⟨some (sgnSym z), Function.update S1 tmp (sgnSym z :: S1 tmp)⟩ 1 :=
    (Eval.push ρ tmp (fun r => r.getD .sep) (some (sgnSym z)) S1).of_eq rfl rfl
  set S2 := Function.update S1 tmp (sgnSym z :: S1 tmp) with hS2
  have hS2src : S2 src = (encodeNat z.natAbs).map Sym.bit ++ r := by
    rw [hS2, Function.update_of_ne hst, hS1, Function.update_self]
  have e3 := copyBlock_eval hsd hst hdt ρ (some (sgnSym z)) (encodeNat z.natAbs) r S2 hr hS2src
  set S3 := Function.update S2 dst ((encodeNat z.natAbs).map Sym.bit ++ S2 dst) with hS3
  have hS3tmp : S3 tmp = sgnSym z :: S tmp := by
    rw [hS3, Function.update_of_ne (Ne.symm hdt), hS2, Function.update_self, hS1,
      Function.update_of_ne (Ne.symm hst)]
  have e4 : Eval ρ (popR tmp) ⟨some .mark, S3⟩
      ⟨some (sgnSym z), Function.update S3 tmp (S tmp)⟩ 1 := by
    have h := Eval.pop ρ tmp (fun _ o => o) (some .mark) S3
    rw [hS3tmp] at h
    exact h
  set S4 := Function.update S3 tmp (S tmp) with hS4
  have e5 : Eval ρ (pushR src) ⟨some (sgnSym z), S4⟩
      ⟨some (sgnSym z), Function.update S4 src (sgnSym z :: S4 src)⟩ 1 :=
    (Eval.push ρ src (fun r => r.getD .sep) (some (sgnSym z)) S4).of_eq rfl rfl
  set S5 := Function.update S4 src (sgnSym z :: S4 src) with hS5
  have e6 : Eval ρ (pushR dst) ⟨some (sgnSym z), S5⟩
      ⟨some (sgnSym z), Function.update S5 dst (sgnSym z :: S5 dst)⟩ 1 :=
    (Eval.push ρ dst (fun r => r.getD .sep) (some (sgnSym z)) S5).of_eq rfl rfl
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))).of_eq ?_ ?_
  · congr 1
    funext k
    simp only [hS5, hS4, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all [intSyms_append]
  · simp only [bitLen]
    omega

theorem copyInt_rs {τ : Type} {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp)
    (hdt : dst ≠ tmp) (z : ℤ) (r : List Sym) (S : K → List Sym) (hr : TermOK r)
    (hS : S src = intSyms z ++ r) :
    RS [] (lm (copyInt src dst tmp) : MProg K τ) S (Function.update S dst (intSyms z ++ S dst))
      (7 * bitLen z.natAbs + 12) :=
  rs_lm (RS.of_eval_exact (fun v => ⟨_, copyInt_eval hsd hst hdt [] v z r S hr hS⟩) le_rfl)

/-- **dropInt**, exact. -/
theorem dropInt_eval (k : K) (ρ : List (SProg K)) (v : Option Sym) (z : ℤ) (r : List Sym)
    (S : K → List Sym) (hr : TermOK r) (hS : S k = intSyms z ++ r) :
    Eval ρ (dropInt k) ⟨v, S⟩ ⟨r.head?, Function.update S k r⟩ (3 * bitLen z.natAbs + 3) := by
  have h1 : Eval ρ (popR k) ⟨v, S⟩
      ⟨some (sgnSym z), Function.update S k ((encodeNat z.natAbs).map Sym.bit ++ r)⟩ 1 := by
    have h := Eval.pop ρ k (fun _ o => o) v S
    rw [hS] at h
    exact h
  have h2 := WP.W6a.dropBits_eval k ρ (some (sgnSym z)) (encodeNat z.natAbs) r
    (Function.update S k ((encodeNat z.natAbs).map Sym.bit ++ r)) hr (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ ?_
  · rw [Function.update_idem]
  · simp only [bitLen]
    omega

theorem dropInt_rs {τ : Type} (k : K) (z : ℤ) (r : List Sym) (S : K → List Sym) (hr : TermOK r)
    (hS : S k = intSyms z ++ r) :
    RS [] (lm (dropInt k) : MProg K τ) S (Function.update S k r) (3 * bitLen z.natAbs + 3) :=
  rs_lm (RS.of_eval_exact (fun v => ⟨_, dropInt_eval k [] v z r S hr hS⟩) le_rfl)

/-- **copyIm**, exact: only `dst` changes. -/
theorem copyIm_eval {src dst t1 t2 : K} (hsd : src ≠ dst) (hs1 : src ≠ t1) (hs2 : src ≠ t2)
    (hd1 : dst ≠ t1) (hd2 : dst ≠ t2) (h12 : t1 ≠ t2)
    (ρ : List (SProg K)) (v : Option Sym) (a b : ℤ) (rest : List Sym) (S : K → List Sym)
    (hS : S src = entrySyms (a, b) ++ rest) :
    ∃ v', Eval ρ (copyIm src dst t1 t2) ⟨v, S⟩
      ⟨v', Function.update S dst (intSyms b ++ S dst)⟩
      (6 * bitLen a.natAbs + 7 * bitLen b.natAbs + 29) := by
  have hS' : S src = sgnSym a :: ((encodeNat a.natAbs).map Sym.bit ++
      (Sym.sep2 :: (intSyms b ++ Sym.sep :: rest))) := by
    rw [hS]
    simp [entrySyms, intSyms, natSyms]
  have e1 : Eval ρ (pushC t1 .mark) ⟨v, S⟩ ⟨v, Function.update S t1 (.mark :: S t1)⟩ 1 :=
    Eval.push ρ t1 (fun _ => .mark) v S
  set S1 := Function.update S t1 (.mark :: S t1) with hS1
  have hS1src : S1 src = sgnSym a :: ((encodeNat a.natAbs).map Sym.bit ++
      (Sym.sep2 :: (intSyms b ++ Sym.sep :: rest))) := by
    rw [hS1, Function.update_of_ne hs1, hS']
  have e2 : Eval ρ (popR src) ⟨v, S1⟩ ⟨some (sgnSym a), Function.update S1 src
      ((encodeNat a.natAbs).map Sym.bit ++ (Sym.sep2 :: (intSyms b ++ Sym.sep :: rest)))⟩ 1 := by
    have h := Eval.pop ρ src (fun _ o => o) v S1
    rw [hS1src] at h
    exact h
  set S2 := Function.update S1 src
    ((encodeNat a.natAbs).map Sym.bit ++ (Sym.sep2 :: (intSyms b ++ Sym.sep :: rest))) with hS2
  have e3 : Eval ρ (pushR t1) ⟨some (sgnSym a), S2⟩
      ⟨some (sgnSym a), Function.update S2 t1 (sgnSym a :: S2 t1)⟩ 1 :=
    (Eval.push ρ t1 (fun r => r.getD .sep) _ S2).of_eq rfl rfl
  set S3 := Function.update S2 t1 (sgnSym a :: S2 t1) with hS3
  have e4 := moveBlock_eval hs1 ρ (some (sgnSym a)) (encodeNat a.natAbs)
    (Sym.sep2 :: (intSyms b ++ Sym.sep :: rest)) S3 (TermOK.cons (by rfl) _)
    (by rw [hS3, Function.update_of_ne hs1, hS2, Function.update_self])
  set S4 := Function.update (Function.update S3 src (Sym.sep2 :: (intSyms b ++ Sym.sep :: rest)))
    t1 ((encodeNat a.natAbs).reverse.map Sym.bit ++ S3 t1) with hS4
  have hS4src : S4 src = Sym.sep2 :: (intSyms b ++ Sym.sep :: rest) := by
    rw [hS4, Function.update_of_ne hs1, Function.update_self]
  have e5 : Eval ρ (popR src) ⟨some .sep2, S4⟩
      ⟨some .sep2, Function.update S4 src (intSyms b ++ Sym.sep :: rest)⟩ 1 := by
    have h := Eval.pop ρ src (fun _ o => o) (some .sep2) S4
    rw [hS4src] at h
    exact h
  set S5 := Function.update S4 src (intSyms b ++ Sym.sep :: rest) with hS5
  have e6 : Eval ρ (pushR t1) ⟨some .sep2, S5⟩
      ⟨some .sep2, Function.update S5 t1 (.sep2 :: S5 t1)⟩ 1 :=
    (Eval.push ρ t1 (fun r => r.getD .sep) _ S5).of_eq rfl rfl
  set S6 := Function.update S5 t1 (.sep2 :: S5 t1) with hS6
  have e7 := copyInt_eval hsd hs2 hd2 ρ (some .sep2) b (Sym.sep :: rest) S6 (TermOK.cons rfl _)
    (by rw [hS6, Function.update_of_ne hs1, hS5, Function.update_self])
  set S7 := Function.update S6 dst (intSyms b ++ S6 dst) with hS7
  have hS7t1 : S7 t1 = (Sym.sep2 :: ((encodeNat a.natAbs).reverse.map Sym.bit ++ [sgnSym a])) ++
      Sym.mark :: S t1 := by
    rw [hS7, Function.update_of_ne (Ne.symm hd1), hS6, Function.update_self, hS5,
      Function.update_of_ne (Ne.symm hs1), hS4, Function.update_self, hS3, Function.update_self,
      hS2, Function.update_of_ne (Ne.symm hs1), hS1, Function.update_self]
    simp
  have hl : ∀ y ∈ Sym.sep2 :: ((encodeNat a.natAbs).reverse.map Sym.bit ++ [sgnSym a]),
      notMarkR (some y) = true := by
    intro y hy
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | ⟨b', -, rfl⟩ | rfl
    · rfl
    · rfl
    · unfold sgnSym; split <;> rfl
  have e8 := xferUntil_eval (Ne.symm hs1) notMarkR ρ (some (sgnSym b)) _ .mark (S t1) S7 hl rfl
    hS7t1
  have hS7src : S7 src = intSyms b ++ Sym.sep :: rest := by
    rw [hS7, Function.update_of_ne hsd, hS6, Function.update_of_ne hs1, hS5, Function.update_self]
  have hrev : (Sym.sep2 :: ((encodeNat a.natAbs).reverse.map Sym.bit ++ [sgnSym a])).reverse ++
      S7 src = S src := by
    rw [hS7src, hS]
    simp [entrySyms, intSyms, natSyms, List.map_reverse]
  refine ⟨some .mark, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 (Eval.seq e7 e8))))))).of_eq ?_ ?_⟩
  · congr 1
    rw [hrev]
    funext k
    simp only [hS7, hS6, hS5, hS4, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [List.length_cons, List.length_append, List.length_map, List.length_reverse,
      List.length_nil, bitLen]
    omega

theorem copyIm_rs {τ : Type} {src dst t1 t2 : K} (hsd : src ≠ dst) (hs1 : src ≠ t1)
    (hs2 : src ≠ t2) (hd1 : dst ≠ t1) (hd2 : dst ≠ t2) (h12 : t1 ≠ t2) (a b : ℤ)
    (rest : List Sym) (S : K → List Sym) (hS : S src = entrySyms (a, b) ++ rest) :
    RS [] (lm (copyIm src dst t1 t2) : MProg K τ) S (Function.update S dst (intSyms b ++ S dst))
      (6 * bitLen a.natAbs + 7 * bitLen b.natAbs + 29) :=
  rs_lm (RS.of_eval_exact (fun v => copyIm_eval hsd hs1 hs2 hd1 hd2 h12 [] v a b rest S hS) le_rfl)

/-- **packEntry**, exact: only `dst` changes. -/
theorem packEntry_eval {nre nim dst tmp : K} (hrd : nre ≠ dst) (hrt : nre ≠ tmp)
    (hid : nim ≠ dst) (hit : nim ≠ tmp) (hdt : dst ≠ tmp)
    (ρ : List (SProg K)) (v : Option Sym) (a b : ℤ) (ra rb : List Sym) (S : K → List Sym)
    (hra : TermOK ra) (hrb : TermOK rb) (hA : S nre = intSyms a ++ ra)
    (hB : S nim = intSyms b ++ rb) :
    ∃ v', Eval ρ (packEntry nre nim dst tmp) ⟨v, S⟩
      ⟨v', Function.update S dst (entrySyms (a, b) ++ S dst)⟩
      (7 * bitLen a.natAbs + 7 * bitLen b.natAbs + 26) := by
  have e1 : Eval ρ (pushC dst .sep) ⟨v, S⟩ ⟨v, Function.update S dst (.sep :: S dst)⟩ 1 :=
    Eval.push ρ dst (fun _ => .sep) v S
  set S1 := Function.update S dst (.sep :: S dst) with hS1
  have e2 := copyInt_eval hid hit hdt ρ v b rb S1 hrb (by rw [hS1, Function.update_of_ne hid, hB])
  set S2 := Function.update S1 dst (intSyms b ++ S1 dst) with hS2
  have e3 : Eval ρ (pushC dst .sep2) ⟨some (sgnSym b), S2⟩
      ⟨some (sgnSym b), Function.update S2 dst (.sep2 :: S2 dst)⟩ 1 :=
    Eval.push ρ dst (fun _ => .sep2) _ S2
  set S3 := Function.update S2 dst (.sep2 :: S2 dst) with hS3
  have e4 := copyInt_eval hrd hrt hdt ρ (some (sgnSym b)) a ra S3 hra
    (by rw [hS3, Function.update_of_ne hrd, hS2, Function.update_of_ne hrd, hS1,
      Function.update_of_ne hrd, hA])
  refine ⟨some (sgnSym a), (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ (by omega)⟩
  congr 1
  rw [hS3, hS2, hS1]
  simp only [Function.update_idem, Function.update_self, entrySyms, List.append_assoc,
    List.cons_append, List.nil_append]

theorem packEntry_rs {τ : Type} {nre nim dst tmp : K} (hrd : nre ≠ dst) (hrt : nre ≠ tmp)
    (hid : nim ≠ dst) (hit : nim ≠ tmp) (hdt : dst ≠ tmp) (a b : ℤ) (ra rb : List Sym)
    (S : K → List Sym) (hra : TermOK ra) (hrb : TermOK rb) (hA : S nre = intSyms a ++ ra)
    (hB : S nim = intSyms b ++ rb) :
    RS [] (lm (packEntry nre nim dst tmp) : MProg K τ) S
      (Function.update S dst (entrySyms (a, b) ++ S dst))
      (7 * bitLen a.natAbs + 7 * bitLen b.natAbs + 26) :=
  rs_lm (RS.of_eval_exact
    (fun v => packEntry_eval hrd hrt hid hit hdt [] v a b ra rb S hra hrb hA hB) le_rfl)

end Entry

#assert_std_axioms notMarkR_of_data entrySyms_eq isData_entryData length_entryData
  notMark_rev_entry moveRec_closed drop_loop_eval emove_closed copyEntry_closed dropEntry_closed
  copyInt_closed dropInt_closed moveBlock_closed copyIm_closed packEntry_closed emove_eval emove_rs
  copyEntry_eval copyEntry_rs dropEntry_eval_rec dropEntry_rs copyInt_eval copyInt_rs dropInt_eval
  dropInt_rs copyIm_eval copyIm_rs packEntry_eval packEntry_rs

end WP.W9g
