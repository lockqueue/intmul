import WP.W5.Prims

/-!
# WP.W5.Interp — a verified symbolic interpreter for straight-line code

Straight-line segments of the program are lists of `Op`s. `Op.step` computes, on the **abstract**
entry table `E`, the effect of one op and its side obligation (exact divisions, the shift bound).
`run` folds `step` over a list.

All cost and size data are **closed functions of the op list** (`unitsOf`, `constsOf`, `dmOf`,
`dkOf`), never projections of the symbolic result: Lean's `whnf` neither caches nor evaluates
`Nat` arithmetic on terms with free variables, so counting along the symbolic run is exponential.

* `run_sound`: if `run bok kb ops E = some (E', P)`, `P` holds and every entry of `E` has bit
  length `≤ m`, then `seqOf U ops` runs from `stOf E B` to `stOf E' B` within
  `unitsOf ops · unit Cu m' + constsOf ops + 1` steps, where `m' = m + dmOf ops + dkOf ops · kb`
  bounds every entry of `E'` (`kb` bounds the shift amounts of `shl`).
* In proofs, `run … = some ?r` is closed by `rfl`: the interpreter is evaluated on concrete stack
  names with symbolic values.

The cost unit `unit Cu m = Cu·(2m + 2) + 8m + 16` bounds every op whose operands have bit length
`≤ m` (W3 ops cost `≤ Cu·(2m + 1)`, framework macros `≤ 7m + 12`); `clr` clears at most
`clrMax` entries and costs `clrMax + 1` units.
-/

namespace WP.W5

open TMFw TMFw.Contracts TMFw.Lib Computability

/-! ## The interpreter -/

/-- Straight-line operations. -/
inductive Op where
  /-- `d += x + y` (W3 addInt) -/
  | add (x y d : L)
  /-- `d += x - y` (W3 subInt) -/
  | sub (x y d : L)
  /-- in place `x := o x` (W3 smallOpInt; `mul2`, `div2`, `div3`) -/
  | sop (o : SmallOp) (x : L)
  /-- `x := x / 2^c`, `y += x % 2^c` (W3 splitAt) -/
  | split (x c y : L)
  /-- `x := x · 2^c` (W3 shlVar) -/
  | shl (x c : L)
  /-- `d += copy of the signed top of s` -/
  | copyI (s d : L)
  /-- `d += copy of the unsigned top of s` -/
  | copyN (s d : L)
  /-- pop a signed number -/
  | dropI (s : L)
  /-- `intSyms z ↦ natSyms |z|` -/
  | toNat (x : L)
  /-- `natSyms n ↦ intSyms n` -/
  | toInt (x : L)
  /-- push `intSyms 0` -/
  | pushZ (x : L)
  /-- push `sep` -/
  | pushS (k : L)
  /-- pop `sep` -/
  | popS (k : L)
  /-- pop everything above the first `sep` (at most `clrMax` entries) -/
  | clr (k : L)
  /-- `natSyms n ↦ natSyms (n / 2)` -/
  | shr1 (x : L)
  /-- `r := sgnFix (top x) (top y) r` -/
  | sfix (r x y : L)

/-- `Nodup` check. -/
def nd (l : List L) : Bool := decide l.Nodup

/-- The supported constant operations. -/
def smallOK : SmallOp → Bool
  | .mul3 => false
  | _ => true

/-- A signed top with a `TermOK` rest. -/
def needI (bk : Bool) : List Ent → Option (ℤ × List Ent)
  | .I z :: es => if tok bk es then some (z, es) else none
  | _ => none

/-- An unsigned top with a `TermOK` rest. -/
def needN (bk : Bool) : List Ent → Option (ℕ × List Ent)
  | .N n :: es => if tok bk es then some (n, es) else none
  | _ => none

/-- A signed top. -/
def headI : List Ent → Option (ℤ × List Ent)
  | .I z :: es => some (z, es)
  | _ => none

/-- An unsigned top. -/
def headN : List Ent → Option (ℕ × List Ent)
  | .N n :: es => some (n, es)
  | _ => none

/-- A separator top. -/
def headS : List Ent → Option (List Ent)
  | .S :: es => some es
  | _ => none

/-- Split at the first separator. -/
def splitS : List Ent → Option (List Ent × List Ent)
  | [] => none
  | .S :: rest => some ([], rest)
  | .I z :: rest => (splitS rest).map fun p => (.I z :: p.1, p.2)
  | .N n :: rest => (splitS rest).map fun p => (.N n :: p.1, p.2)

/-- Maximal number of entries one `clr` removes. -/
def clrMax : ℕ := 3

/-- `l` has at most `n` elements (structural: no arithmetic on symbolic terms). -/
def lenLe : ℕ → List Ent → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | n + 1, _ :: l => lenLe n l

/-- One abstract step: new entry table and side obligation (`kb` bounds shift amounts). -/
def Op.step (bok : L → Bool) (kb : ℕ) : Op → (L → List Ent) → Option ((L → List Ent) × Prop)
  | .add x y d, E =>
    if nd (List.ofFn ![x, y, d] ++ List.ofFn (scr [x, y, d])) then
      (needI (bok x) (E x)).bind fun p => (needI (bok y) (E y)).bind fun q =>
        some (Function.update E d (.I (p.1 + q.1) :: E d), True)
    else none
  | .sub x y d, E =>
    if nd (List.ofFn ![x, y, d] ++ List.ofFn (scr [x, y, d])) then
      (needI (bok x) (E x)).bind fun p => (needI (bok y) (E y)).bind fun q =>
        some (Function.update E d (.I (p.1 - q.1) :: E d), True)
    else none
  | .sop o x, E =>
    if smallOK o && nd (List.ofFn ![x] ++ List.ofFn (scr [x])) then
      (needI (bok x) (E x)).bind fun p =>
        some (Function.update E x (.I (o.apply p.1) :: p.2), o.ok p.1)
    else none
  | .split x k y, E =>
    if nd (List.ofFn ![x, k, y] ++ List.ofFn (scr [x, k, y])) then
      (needN (bok x) (E x)).bind fun p => (needN (bok k) (E k)).bind fun q =>
        some (Function.update (Function.update E x (.N (p.1 / 2 ^ q.1) :: p.2)) y
          (.N (p.1 % 2 ^ q.1) :: E y), True)
    else none
  | .shl x k, E =>
    if nd (List.ofFn ![x, k] ++ List.ofFn (scr [x, k])) then
      (needN (bok x) (E x)).bind fun p => (needN (bok k) (E k)).bind fun q =>
        some (Function.update E x (.N (p.1 * 2 ^ q.1) :: p.2), q.1 ≤ kb)
    else none
  | .copyI s d, E =>
    if nd ([s, d] ++ List.ofFn (scr [s, d])) then
      (needI (bok s) (E s)).bind fun p => some (Function.update E d (.I p.1 :: E d), True)
    else none
  | .copyN s d, E =>
    if nd ([s, d] ++ List.ofFn (scr [s, d])) then
      (needN (bok s) (E s)).bind fun p => some (Function.update E d (.N p.1 :: E d), True)
    else none
  | .dropI s, E => (needI (bok s) (E s)).bind fun p => some (Function.update E s p.2, True)
  | .toNat x, E =>
    (headI (E x)).bind fun p => some (Function.update E x (.N p.1.natAbs :: p.2), True)
  | .toInt x, E =>
    (headN (E x)).bind fun p => some (Function.update E x (.I (p.1 : ℤ) :: p.2), True)
  | .pushZ x, E => some (Function.update E x (.I 0 :: E x), True)
  | .pushS k, E => some (Function.update E k (.S :: E k), True)
  | .popS k, E => (headS (E k)).bind fun es => some (Function.update E k es, True)
  | .clr k, E =>
    (splitS (E k)).bind fun p =>
      if lenLe clrMax p.1 then some (Function.update E k (.S :: p.2), True) else none
  | .shr1 x, E =>
    (needN (bok x) (E x)).bind fun p => some (Function.update E x (.N (p.1 / 2) :: p.2), True)
  | .sfix r x y, E =>
    (needI (bok r) (E r)).bind fun p => (headI (E x)).bind fun a =>
      (headI (E y)).bind fun b =>
        some (Function.update E r (.I (sgnFix a.1 b.1 p.1) :: p.2), True)

/-- Cost units of an op (charged at the size bound after the op). -/
def Op.units : Op → ℕ
  | .add _ _ _ => 1
  | .sub _ _ _ => 1
  | .sop _ _ => 1
  | .split _ _ _ => 1
  | .shl _ _ => 1
  | .copyI _ _ => 1
  | .copyN _ _ => 1
  | .dropI _ => 1
  | .clr _ => clrMax + 1
  | _ => 0

/-- Constant steps of an op. -/
def Op.consts : Op → ℕ
  | .toNat _ => 1
  | .toInt _ => 1
  | .pushZ _ => 1
  | .pushS _ => 1
  | .popS _ => 1
  | .shr1 _ => 3
  | .sfix _ _ _ => 10
  | _ => 0

/-- Literal growth of the size bound. -/
def Op.dm : Op → ℕ
  | .add _ _ _ => 1
  | .sub _ _ _ => 1
  | .sop _ _ => 2
  | _ => 0

/-- Growth of the size bound in multiples of the shift bound `kb`. -/
def Op.dk : Op → ℕ
  | .shl _ _ => 1
  | _ => 0

/-- The machine code of one op. -/
def Op.prog (U : Subs) : Op → Prog L (fun _ => Sym) U.σ
  | .add x y d => (U.add.P.mapStk (emb ![x, y, d] [x, y, d] U.add.hm)).liftRegs (lAdd U)
  | .sub x y d => (U.sub.P.mapStk (emb ![x, y, d] [x, y, d] U.sub.hm)).liftRegs (lSub U)
  | .sop .mul2 x => (U.mul2.P.mapStk (emb ![x] [x] U.mul2.hm)).liftRegs (lMul2 U)
  | .sop .div2 x => (U.div2.P.mapStk (emb ![x] [x] U.div2.hm)).liftRegs (lDiv2 U)
  | .sop .div3 x => (U.div3.P.mapStk (emb ![x] [x] U.div3.hm)).liftRegs (lDiv3 U)
  | .sop .mul3 _ => skip
  | .split x k y => (U.split.P.mapStk (emb ![x, k, y] [x, k, y] U.split.hm)).liftRegs (lSplit U)
  | .shl x k => (U.shl.P.mapStk (emb ![x, k] [x, k] U.shl.hm)).liftRegs (lShl U)
  | .copyI s d => (copyIP s d (scr [s, d] 0) (scr [s, d] 1)).liftRegs (lR U)
  | .copyN s d => (copyBlock s d (scr [s, d] 0)).liftRegs (lR U)
  | .dropI s => (dropIP s).liftRegs (lR U)
  | .toNat x => (popR x).liftRegs (lR U)
  | .toInt x => (pushC x .pos).liftRegs (lR U)
  | .pushZ x => (pushC x .pos).liftRegs (lR U)
  | .pushS k => (pushC k .sep).liftRegs (lR U)
  | .popS k => (popR k).liftRegs (lR U)
  | .clr k => (clrP k).liftRegs (lR U)
  | .shr1 x => (shr1P x).liftRegs (lR U)
  | .sfix r x y => (sfixP r x y).liftRegs (lR U)

/-- Sequential composition of a segment (terminated by `skip`). -/
def seqOf (U : Subs) : List Op → Prog L (fun _ => Sym) U.σ
  | [] => skip
  | o :: os => .seq (o.prog U) (seqOf U os)

/-- Run a segment abstractly: final entry table and conjoined obligations. -/
def run (bok : L → Bool) (kb : ℕ) : List Op → (L → List Ent) → Option ((L → List Ent) × Prop)
  | [], E => some (E, True)
  | o :: os, E =>
    (o.step bok kb E).bind fun r1 => (run bok kb os r1.1).bind fun r2 =>
      some (r2.1, r1.2 ∧ r2.2)

/-- Total cost units of a segment. -/
def unitsOf : List Op → ℕ
  | [] => 0
  | o :: os => o.units + unitsOf os

/-- Total constant steps of a segment. -/
def constsOf : List Op → ℕ
  | [] => 0
  | o :: os => o.consts + constsOf os

/-- Total literal growth of the size bound. -/
def dmOf : List Op → ℕ
  | [] => 0
  | o :: os => o.dm + dmOf os

/-- Total growth of the size bound in multiples of `kb`. -/
def dkOf : List Op → ℕ
  | [] => 0
  | o :: os => o.dk + dkOf os

/-- The cost unit at size bound `m`. -/
def unit (Cu m : ℕ) : ℕ := Cu * (2 * m + 2) + 8 * m + 16

theorem unit_mono (Cu : ℕ) {m m' : ℕ} (h : m ≤ m') : unit Cu m ≤ unit Cu m' := by
  unfold unit
  have := Nat.mul_le_mul_left Cu (show 2 * m + 2 ≤ 2 * m' + 2 by omega)
  omega

/-! ## Helper facts -/

theorem needI_some {bk : Bool} {l : List Ent} {p : ℤ × List Ent} (h : needI bk l = some p) :
    l = .I p.1 :: p.2 ∧ tok bk p.2 = true := by
  match l, h with
  | .I z :: es, h =>
    simp only [needI] at h
    split_ifs at h with ht
    cases h
    exact ⟨rfl, ht⟩

theorem needN_some {bk : Bool} {l : List Ent} {p : ℕ × List Ent} (h : needN bk l = some p) :
    l = .N p.1 :: p.2 ∧ tok bk p.2 = true := by
  match l, h with
  | .N n :: es, h =>
    simp only [needN] at h
    split_ifs at h with ht
    cases h
    exact ⟨rfl, ht⟩

theorem headI_some {l : List Ent} {p : ℤ × List Ent} (h : headI l = some p) :
    l = .I p.1 :: p.2 := by
  match l, h with
  | .I z :: es, h => cases h; rfl

theorem headN_some {l : List Ent} {p : ℕ × List Ent} (h : headN l = some p) :
    l = .N p.1 :: p.2 := by
  match l, h with
  | .N n :: es, h => cases h; rfl

theorem headS_some {l es : List Ent} (h : headS l = some es) : l = .S :: es := by
  match l, h with
  | .S :: es, h => cases h; rfl

theorem splitS_some : ∀ {l : List Ent} {p : List Ent × List Ent}, splitS l = some p →
    l = p.1 ++ .S :: p.2 ∧ noS p.1 = true
  | .S :: rest, p, h => by
    simp only [splitS, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | .I z :: rest, p, h => by
    simp only [splitS, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    obtain ⟨h1, h2⟩ := splitS_some hq
    exact ⟨by rw [h1]; rfl, by simpa [noS] using h2⟩
  | .N n :: rest, p, h => by
    simp only [splitS, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    obtain ⟨h1, h2⟩ := splitS_some hq
    exact ⟨by rw [h1]; rfl, by simpa [noS] using h2⟩

theorem lenLe_sound : ∀ (n : ℕ) (l : List Ent), lenLe n l = true → l.length ≤ n
  | _, [], _ => Nat.zero_le _
  | 0, _ :: _, h => by simp [lenLe] at h
  | n + 1, _ :: l, h => by
    have := lenLe_sound n l (by simpa [lenLe] using h)
    simp only [List.length_cons]
    omega

theorem nd_two {s d : L} (h : nd ([s, d] ++ List.ofFn (scr [s, d])) = true) :
    s ≠ d ∧ s ≠ scr [s, d] 0 ∧ s ≠ scr [s, d] 1 ∧ d ≠ scr [s, d] 0 ∧ d ≠ scr [s, d] 1 ∧
      scr [s, d] 0 ≠ scr [s, d] 1 := by
  have h' : ([s, d, scr [s, d] 0, scr [s, d] 1, scr [s, d] 2, scr [s, d] 3]).Nodup :=
    of_decide_eq_true h
  have p1 := List.pairwise_cons.1 h'
  have p2 := List.pairwise_cons.1 p1.2
  have p3 := List.pairwise_cons.1 p2.2
  exact ⟨p1.1 _ (by simp), p1.1 _ (by simp), p1.1 _ (by simp), p2.1 _ (by simp),
    p2.1 _ (by simp), p3.1 _ (by simp)⟩

theorem encL_append : ∀ (es es' : List Ent), encL (es ++ es') = encL es ++ encL es'
  | [], _ => rfl
  | e :: es, es' => by simp [encL_append es es', List.append_assoc]

theorem stOf_push (E : L → List Ent) (B : L → List Sym) (k : L) (e : Ent) :
    stOf (Function.update E k (e :: E k)) B =
      Function.update (stOf E B) k (e.enc ++ stOf E B k) := by
  rw [stOf_update]; simp [stOf, List.append_assoc]

theorem stOf_head (E : L → List Ent) (B : L → List Sym) {k : L} {e : Ent} {es : List Ent}
    (h : E k = e :: es) : stOf E B k = e.enc ++ (encL es ++ B k) := by
  rw [stOf_apply, h, encL_cons, List.append_assoc]

theorem stOf_replace (E : L → List Ent) (B : L → List Sym) (k : L) (es : List Ent) :
    stOf (Function.update E k es) B = Function.update (stOf E B) k (encL es ++ B k) :=
  stOf_update E B k es

theorem st_eq {σ : Type} {v : σ} {S S' : L → List Sym} (h : S = S') :
    (⟨v, S⟩ : St L (fun _ => Sym) σ) = ⟨v, S'⟩ := by rw [h]

/-- One-location W3 update, transported to full stacks. -/
theorem w3_update1 {σ : Type} {n m : ℕ} {R : Type} {P : Prog (Loc n m) (fun _ => Sym) R}
    (hc : P.Closed) {ι : Loc n m → L} (hι : Function.Injective ι) (l : Lens σ R)
    (S : L → List Sym) (j0 : Loc n m) (v : List Sym) {T : ℕ}
    (h : Runs P (fun j => S (ι j)) (Function.update (fun j => S (ι j)) j0 v) (fun _ => True) T)
    (ρ : List (Prog L (fun _ => Sym) σ)) :
    Triple ρ (fun s => s.stk = S) ((P.mapStk ι).liftRegs l)
      (fun s => s.stk = Function.update S (ι j0) v) T := by
  refine embed_triple (Q := fun _ => True) hc hι l ?_ ?_ ρ
  · have e : (fun j => Function.update S (ι j0) v (ι j)) =
        Function.update (fun j => S (ι j)) j0 v := by
      funext j
      exact update_comp_inj hι S (fun j => S (ι j)) (fun _ => rfl) j0 v j
    rw [e]
    exact h
  · intro k hk
    exact Function.update_of_ne (fun e => hk j0 e.symm) _ _

/-- Two-location W3 update, transported to full stacks. -/
theorem w3_update2 {σ : Type} {n m : ℕ} {R : Type} {P : Prog (Loc n m) (fun _ => Sym) R}
    (hc : P.Closed) {ι : Loc n m → L} (hι : Function.Injective ι) (l : Lens σ R)
    (S : L → List Sym) (j0 j1 : Loc n m) (v0 v1 : List Sym) {T : ℕ}
    (h : Runs P (fun j => S (ι j))
      (Function.update (Function.update (fun j => S (ι j)) j0 v0) j1 v1) (fun _ => True) T)
    (ρ : List (Prog L (fun _ => Sym) σ)) :
    Triple ρ (fun s => s.stk = S) ((P.mapStk ι).liftRegs l)
      (fun s => s.stk = Function.update (Function.update S (ι j0) v0) (ι j1) v1) T := by
  refine embed_triple (Q := fun _ => True) hc hι l ?_ ?_ ρ
  · have hT : ∀ k, Function.update S (ι j0) v0 (ι k) =
        Function.update (fun j => S (ι j)) j0 v0 k :=
      update_comp_inj hι S (fun j => S (ι j)) (fun _ => rfl) j0 v0
    have e : (fun j => Function.update (Function.update S (ι j0) v0) (ι j1) v1 (ι j)) =
        Function.update (Function.update (fun j => S (ι j)) j0 v0) j1 v1 := by
      funext j
      exact update_comp_inj hι _ _ hT j1 v1 j
    rw [e]
    exact h
  · intro k hk
    rw [Function.update_of_ne (fun e => hk j1 e.symm), Function.update_of_ne (fun e => hk j0 e.symm)]

/-- The conclusion of an op's soundness: the triple (cost at the post bound `m'`) and the size
invariant. -/
def OpOK (U : Subs) (Cu : ℕ) (B : L → List Sym) (ρ : List (Prog L (fun _ => Sym) U.σ))
    (p : Prog L (fun _ => Sym) U.σ) (E E' : L → List Ent) (m' n kc : ℕ) : Prop :=
  Triple ρ (fun s => s.stk = stOf E B) p (fun s => s.stk = stOf E' B) (n * unit Cu m' + kc) ∧
    AllLe E' m'

theorem OpOK.mono {U : Subs} {Cu : ℕ} {B : L → List Sym} {ρ : List (Prog L (fun _ => Sym) U.σ)}
    {p : Prog L (fun _ => Sym) U.σ} {E E' : L → List Ent} {m1 m2 n kc : ℕ}
    (h : OpOK U Cu B ρ p E E' m1 n kc) (hm : m1 ≤ m2) : OpOK U Cu B ρ p E E' m2 n kc :=
  ⟨h.1.cost_mono (by have := Nat.mul_le_mul_left n (unit_mono Cu hm); omega), h.2.mono hm⟩

theorem unit_ge (Cu m : ℕ) : 8 * m + 16 ≤ unit Cu m := by unfold unit; omega

theorem le_post (m a b : ℕ) : m ≤ m + a + b := by omega

/-! ## Soundness of each op -/

section Sound

variable {U : Subs} {Cu : ℕ} (hU : SubsOK U Cu) {bok : L → Bool} {B : L → List Sym}
  (hB : ∀ k, bok k = true → TermOK (B k)) (ρ : List (Prog L (fun _ => Sym) U.σ))

theorem allLe_push {E : L → List Ent} {m m' : ℕ} (hA : AllLe E m) (hm : m ≤ m') (k : L) (e : Ent)
    (he : e.len ≤ m') : AllLe (Function.update E k (e :: E k)) m' := by
  refine (hA.mono hm).update k _ ?_
  intro e' he'
  rcases List.mem_cons.1 he' with rfl | he'
  · exact he
  · exact le_trans (hA k e' he') hm

theorem allLe_replace {E : L → List Ent} {m m' : ℕ} (hA : AllLe E m) (hm : m ≤ m') {k : L}
    {e0 : Ent} {es : List Ent} (hk : E k = e0 :: es) (e : Ent) (he : e.len ≤ m') :
    AllLe (Function.update E k (e :: es)) m' := by
  refine (hA.mono hm).update k _ ?_
  intro e' he'
  rcases List.mem_cons.1 he' with rfl | he'
  · exact he
  · exact le_trans (hA.tail hk e' he') hm

include hU hB in
theorem sound_add (x y d : L) (E : L → List Ent) (m : ℕ) (p q : ℤ × List Ent)
    (hnd : nd (List.ofFn ![x, y, d] ++ List.ofFn (scr [x, y, d])) = true)
    (hp : needI (bok x) (E x) = some p) (hq : needI (bok y) (E y) = some q) (hA : AllLe E m) :
    OpOK U Cu B ρ ((Op.add x y d).prog U) E
      (Function.update E d (.I (p.1 + q.1) :: E d)) (m + 1) 1 0 := by
  obtain ⟨hx, htx⟩ := needI_some hp
  obtain ⟨hy, hty⟩ := needI_some hq
  have ha : bitLen p.1.natAbs ≤ m := hA.of_mem hx
  have hb : bitLen q.1.natAbs ≤ m := hA.of_mem hy
  have hcost : Cu * (bitLen p.1.natAbs + bitLen q.1.natAbs + 1) ≤ 1 * unit Cu (m + 1) := by
    have := Nat.mul_le_mul_left Cu
      (show bitLen p.1.natAbs + bitLen q.1.natAbs + 1 ≤ 2 * (m + 1) + 2 by omega)
    unfold unit; omega
  have hι := emb_inj ![x, y, d] [x, y, d] U.add.hm (of_decide_eq_true hnd)
  have T0 := w3_update1 hU.add_c hι (lAdd U) (stOf E B) (.inl 2)
    (intSyms (p.1 + q.1) ++ stOf E B d)
    (hU.add p.1 q.1 _ _ _ (tok_sound (hB x) htx) (tok_sound (hB y) hty) (stOf_head E B hx)
      (stOf_head E B hy)) ρ
  refine ⟨T0.conseq (fun s hs => hs) (fun s hs => ?_) hcost, allLe_push hA (Nat.le_succ _) d _ ?_⟩
  · rw [hs, stOf_push]; rfl
  · have := bitLen_natAbs_add_le p.1 q.1
    show bitLen (p.1 + q.1).natAbs ≤ m + 1
    omega

include hU hB in
theorem sound_sub (x y d : L) (E : L → List Ent) (m : ℕ) (p q : ℤ × List Ent)
    (hnd : nd (List.ofFn ![x, y, d] ++ List.ofFn (scr [x, y, d])) = true)
    (hp : needI (bok x) (E x) = some p) (hq : needI (bok y) (E y) = some q) (hA : AllLe E m) :
    OpOK U Cu B ρ ((Op.sub x y d).prog U) E
      (Function.update E d (.I (p.1 - q.1) :: E d)) (m + 1) 1 0 := by
  obtain ⟨hx, htx⟩ := needI_some hp
  obtain ⟨hy, hty⟩ := needI_some hq
  have ha : bitLen p.1.natAbs ≤ m := hA.of_mem hx
  have hb : bitLen q.1.natAbs ≤ m := hA.of_mem hy
  have hcost : Cu * (bitLen p.1.natAbs + bitLen q.1.natAbs + 1) ≤ 1 * unit Cu (m + 1) := by
    have := Nat.mul_le_mul_left Cu
      (show bitLen p.1.natAbs + bitLen q.1.natAbs + 1 ≤ 2 * (m + 1) + 2 by omega)
    unfold unit; omega
  have hι := emb_inj ![x, y, d] [x, y, d] U.sub.hm (of_decide_eq_true hnd)
  have T0 := w3_update1 hU.sub_c hι (lSub U) (stOf E B) (.inl 2)
    (intSyms (p.1 - q.1) ++ stOf E B d)
    (hU.sub p.1 q.1 _ _ _ (tok_sound (hB x) htx) (tok_sound (hB y) hty) (stOf_head E B hx)
      (stOf_head E B hy)) ρ
  refine ⟨T0.conseq (fun s hs => hs) (fun s hs => ?_) hcost, allLe_push hA (Nat.le_succ _) d _ ?_⟩
  · rw [hs, stOf_push]; rfl
  · have := bitLen_natAbs_sub_le p.1 q.1
    show bitLen (p.1 - q.1).natAbs ≤ m + 1
    omega

include hU hB in
theorem sound_sop (o : SmallOp) (x : L) (E : L → List Ent) (m : ℕ) (p : ℤ × List Ent)
    (hsup : smallOK o = true)
    (hnd : nd (List.ofFn ![x] ++ List.ofFn (scr [x])) = true)
    (hp : needI (bok x) (E x) = some p) (hok : o.ok p.1) (hA : AllLe E m) :
    OpOK U Cu B ρ ((Op.sop o x).prog U) E
      (Function.update E x (.I (o.apply p.1) :: p.2)) (m + 2) 1 0 := by
  obtain ⟨hx, htx⟩ := needI_some hp
  have hrx : TermOK (encL p.2 ++ B x) := tok_sound (hB x) htx
  have hSx := stOf_head E B hx
  have ha : bitLen p.1.natAbs ≤ m := hA.of_mem hx
  have hcost : Cu * (bitLen p.1.natAbs + 1) ≤ 1 * unit Cu (m + 2) := by
    have := Nat.mul_le_mul_left Cu (show bitLen p.1.natAbs + 1 ≤ 2 * (m + 2) + 2 by omega)
    unfold unit; omega
  have hpost : Function.update (stOf E B) x (intSyms (o.apply p.1) ++ (encL p.2 ++ B x)) =
      stOf (Function.update E x (.I (o.apply p.1) :: p.2)) B := by
    rw [stOf_replace]; simp [List.append_assoc, Ent.enc]
  have hAll : AllLe (Function.update E x (.I (o.apply p.1) :: p.2)) (m + 2) := by
    refine allLe_replace hA (by omega) hx _ ?_
    have := bitLen_smallOp_le o p.1 hok
    show bitLen (o.apply p.1).natAbs ≤ m + 2
    omega
  refine ⟨?_, hAll⟩
  cases o with
  | mul2 =>
    have hι := emb_inj ![x] [x] U.mul2.hm (of_decide_eq_true hnd)
    have T0 := w3_update1 hU.mul2_c hι (lMul2 U) (stOf E B) (.inl 0)
      (intSyms (SmallOp.apply .mul2 p.1) ++ (encL p.2 ++ B x)) (hU.mul2 p.1 _ _ hrx hok hSx) ρ
    exact T0.conseq (fun s hs => hs) (fun s hs => by rw [hs]; exact hpost) hcost
  | div2 =>
    have hι := emb_inj ![x] [x] U.div2.hm (of_decide_eq_true hnd)
    have T0 := w3_update1 hU.div2_c hι (lDiv2 U) (stOf E B) (.inl 0)
      (intSyms (SmallOp.apply .div2 p.1) ++ (encL p.2 ++ B x)) (hU.div2 p.1 _ _ hrx hok hSx) ρ
    exact T0.conseq (fun s hs => hs) (fun s hs => by rw [hs]; exact hpost) hcost
  | div3 =>
    have hι := emb_inj ![x] [x] U.div3.hm (of_decide_eq_true hnd)
    have T0 := w3_update1 hU.div3_c hι (lDiv3 U) (stOf E B) (.inl 0)
      (intSyms (SmallOp.apply .div3 p.1) ++ (encL p.2 ++ B x)) (hU.div3 p.1 _ _ hrx hok hSx) ρ
    exact T0.conseq (fun s hs => hs) (fun s hs => by rw [hs]; exact hpost) hcost
  | mul3 => simp [smallOK] at hsup

include hU hB in
theorem sound_split (x k y : L) (E : L → List Ent) (m : ℕ) (p q : ℕ × List Ent)
    (hnd : nd (List.ofFn ![x, k, y] ++ List.ofFn (scr [x, k, y])) = true)
    (hp : needN (bok x) (E x) = some p) (hq : needN (bok k) (E k) = some q) (hA : AllLe E m) :
    OpOK U Cu B ρ ((Op.split x k y).prog U) E
      (Function.update (Function.update E x (.N (p.1 / 2 ^ q.1) :: p.2)) y
        (.N (p.1 % 2 ^ q.1) :: E y)) m 1 0 := by
  obtain ⟨hx, htx⟩ := needN_some hp
  obtain ⟨hk, htk⟩ := needN_some hq
  have ha : bitLen p.1 ≤ m := hA.of_mem hx
  have hb : bitLen q.1 ≤ m := hA.of_mem hk
  have hcost : Cu * (min q.1 (bitLen p.1) + bitLen q.1 + 1) ≤ 1 * unit Cu m := by
    have := Nat.mul_le_mul_left Cu (show min q.1 (bitLen p.1) + bitLen q.1 + 1 ≤ 2 * m + 2 by
      have := min_le_right q.1 (bitLen p.1); omega)
    unfold unit; omega
  have hι := emb_inj ![x, k, y] [x, k, y] U.split.hm (of_decide_eq_true hnd)
  have T0 := w3_update2 hU.split_c hι (lSplit U) (stOf E B) (.inl 0) (.inl 2)
    (natSyms (p.1 / 2 ^ q.1) ++ (encL p.2 ++ B x)) (natSyms (p.1 % 2 ^ q.1) ++ stOf E B y)
    (hU.split p.1 q.1 _ _ _ (tok_sound (hB x) htx) (tok_sound (hB k) htk) (stOf_head E B hx)
      (stOf_head E B hk)) ρ
  refine ⟨T0.conseq (fun s hs => hs) (fun s hs => ?_) hcost, ?_⟩
  · rw [hs, stOf_replace, stOf_replace]
    simp only [encL_cons, Ent.enc, List.append_assoc]
    rfl
  · refine (hA.update x _ ?_).update y _ ?_
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact le_trans (bitLen_div_le _ _) ha
      · exact hA.tail hx e he
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact le_trans (bitLen_mod_le _ _) ha
      · exact hA y e he

include hU hB in
theorem sound_shl (x k : L) (E : L → List Ent) (m kb : ℕ) (p q : ℕ × List Ent)
    (hnd : nd (List.ofFn ![x, k] ++ List.ofFn (scr [x, k])) = true)
    (hp : needN (bok x) (E x) = some p) (hq : needN (bok k) (E k) = some q) (hob : q.1 ≤ kb)
    (hA : AllLe E m) :
    OpOK U Cu B ρ ((Op.shl x k).prog U) E
      (Function.update E x (.N (p.1 * 2 ^ q.1) :: p.2)) (m + kb) 1 0 := by
  obtain ⟨hx, htx⟩ := needN_some hp
  obtain ⟨hk, htk⟩ := needN_some hq
  have ha : bitLen p.1 ≤ m := hA.of_mem hx
  have hb : bitLen q.1 ≤ m := hA.of_mem hk
  have hcost : Cu * (q.1 + bitLen q.1 + 1) ≤ 1 * unit Cu (m + kb) := by
    have := Nat.mul_le_mul_left Cu (show q.1 + bitLen q.1 + 1 ≤ 2 * (m + kb) + 2 by omega)
    unfold unit; omega
  have hι := emb_inj ![x, k] [x, k] U.shl.hm (of_decide_eq_true hnd)
  have T0 := w3_update1 hU.shl_c hι (lShl U) (stOf E B) (.inl 0)
    (natSyms (p.1 * 2 ^ q.1) ++ (encL p.2 ++ B x))
    (hU.shl p.1 q.1 _ _ _ (tok_sound (hB x) htx) (tok_sound (hB k) htk) (stOf_head E B hx)
      (stOf_head E B hk)) ρ
  refine ⟨T0.conseq (fun s hs => hs) (fun s hs => ?_) hcost, ?_⟩
  · rw [hs, stOf_replace]
    simp only [encL_cons, Ent.enc, List.append_assoc]
    rfl
  · refine allLe_replace hA (by omega) hx _ ?_
    have := bitLen_mul_pow_le p.1 q.1
    show bitLen (p.1 * 2 ^ q.1) ≤ m + kb
    omega

/-- Generic lifting of a framework macro with a stack-only effect. -/
theorem sound_fw {p : SProg L} (hc : p.Closed) (E E' : L → List Ent) (m' n kc t : ℕ)
    (h : ∀ r, ∃ r' t', t' ≤ t ∧ Eval [] p ⟨r, stOf E B⟩ ⟨r', stOf E' B⟩ t')
    (ht : t ≤ n * unit Cu m' + kc) (hA' : AllLe E' m') :
    OpOK U Cu B ρ (p.liftRegs (lR U)) E E' m' n kc :=
  ⟨(liftR_triple hc h ρ).cost_mono ht, hA'⟩

end Sound

/-! ## Soundness of `step` and `run` -/

theorem Op.sound {U : Subs} {Cu : ℕ} (hU : SubsOK U Cu) {bok : L → Bool} {B : L → List Sym}
    (hB : ∀ k, bok k = true → TermOK (B k)) (ρ : List (Prog L (fun _ => Sym) U.σ)) (kb : ℕ) :
    ∀ (o : Op) (E E' : L → List Ent) (P : Prop) (m : ℕ), o.step bok kb E = some (E', P) → P →
      AllLe E m → OpOK U Cu B ρ (o.prog U) E E' (m + o.dm + o.dk * kb) o.units o.consts := by
  intro o E E' P m h hP hA
  have hu := unit_ge Cu m
  cases o with
  | add x y d =>
    simp only [Op.step] at h
    split_ifs at h with hnd
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (sound_add hU hB ρ x y d E m p q hnd hp hq hA).mono (Nat.le_add_right _ _)
  | sub x y d =>
    simp only [Op.step] at h
    split_ifs at h with hnd
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (sound_sub hU hB ρ x y d E m p q hnd hp hq hA).mono (Nat.le_add_right _ _)
  | sop o x =>
    simp only [Op.step] at h
    split_ifs at h with hnd
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true] at hnd
    exact (sound_sop hU hB ρ o x E m p hnd.1 hnd.2 hp hP hA).mono
      (Nat.le_add_right _ _)
  | split x k y =>
    simp only [Op.step] at h
    split_ifs at h with hnd
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (sound_split hU hB ρ x k y E m p q hnd hp hq hA).mono
      (le_post _ _ _)
  | shl x k =>
    simp only [Op.step] at h
    split_ifs at h with hnd
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (sound_shl hU hB ρ x k E m kb p q hnd hp hq hP hA).mono
      (by show m + kb ≤ m + 0 + 1 * kb; omega)
  | copyI s d =>
    simp only [Op.step] at h
    split_ifs at h with hnd
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hs, hts⟩ := needI_some hp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := nd_two hnd
    have hv : bitLen p.1.natAbs ≤ m := hA.of_mem hs
    refine (sound_fw ρ (copyIP_closed _ _ _ _) E _ m 1 0 (7 * m + 12) (fun r => ?_) (by omega)
      (allLe_push hA le_rfl d (.I p.1) hv)).mono (le_post _ _ _)
    exact ⟨_, _, by omega, (copyIP_eval h1 h2 h3 h4 h5 h6 [] r p.1 (encL p.2 ++ B s) (stOf E B)
      (tok_sound (hB s) hts) (stOf_head E B hs)).of_eq (st_eq (by rw [stOf_push]; rfl)) rfl⟩
  | copyN s d =>
    simp only [Op.step] at h
    split_ifs at h with hnd
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hs, hts⟩ := needN_some hp
    obtain ⟨h1, h2, -, h4, -, -⟩ := nd_two hnd
    have hv : bitLen p.1 ≤ m := hA.of_mem hs
    have hv' : (encodeNat p.1).length ≤ m := hv
    refine (sound_fw ρ (by simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits,
      moveBitsBody, moveBitsDup, dupBody, pushC, pushR, popR, restoreR, skip]) E _ m 1 0
      (7 * m + 7) (fun r => ?_) (by omega) (allLe_push hA le_rfl d (.N p.1) hv)).mono
      (le_post _ _ _)
    exact ⟨_, _, by omega, (copyBlock_eval h1 h2 h4 [] r (encodeNat p.1) (encL p.2 ++ B s)
      (stOf E B) (tok_sound (hB s) hts) (stOf_head E B hs)).of_eq
      (st_eq (by rw [stOf_push]; rfl)) rfl⟩
  | dropI s =>
    simp only [Op.step] at h
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hs, hts⟩ := needI_some hp
    have hv : bitLen p.1.natAbs ≤ m := hA.of_mem hs
    refine (sound_fw ρ (dropIP_closed _) E _ m 1 0 (2 * m + 5) (fun r => ?_) (by omega)
      (hA.update s _ (hA.tail hs))).mono (le_post _ _ _)
    exact ⟨_, _, by omega, (dropIP_eval [] r p.1 (encL p.2 ++ B s) (stOf E B)
      (tok_sound (hB s) hts) (stOf_head E B hs)).of_eq (st_eq (by rw [stOf_replace])) rfl⟩
  | toNat x =>
    simp only [Op.step] at h
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hx := headI_some hp
    have hv : bitLen p.1.natAbs ≤ m := hA.of_mem hx
    refine (sound_fw ρ (by simp [Prog.Closed, Prog.FreeBelow, popR]) E _ m 0 1 1 (fun r => ?_)
      (by omega) (allLe_replace hA le_rfl hx (.N p.1.natAbs) hv)).mono
      (le_post _ _ _)
    have e : Eval [] (popR x) ⟨r, stOf E B⟩ ⟨(stOf E B x).head?,
        Function.update (stOf E B) x (stOf E B x).tail⟩ 1 := Eval.pop _ _ _ _ _
    refine ⟨_, 1, le_rfl, e.of_eq (st_eq ?_) rfl⟩
    rw [stOf_head E B hx, stOf_replace]
    simp [Ent.enc, intSyms_eq]
  | toInt x =>
    simp only [Op.step] at h
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hx := headN_some hp
    have hv : bitLen p.1 ≤ m := hA.of_mem hx
    refine (sound_fw ρ (by simp [Prog.Closed, Prog.FreeBelow, pushC]) E _ m 0 1 1 (fun r => ?_)
      (by omega) (allLe_replace hA le_rfl hx (.I (p.1 : ℤ)) (by simpa [Ent.len] using hv))).mono
      (le_post _ _ _)
    have e : Eval [] (pushC x .pos) ⟨r, stOf E B⟩
        ⟨r, Function.update (stOf E B) x (Sym.pos :: stOf E B x)⟩ 1 := Eval.push _ _ _ _ _
    refine ⟨_, 1, le_rfl, e.of_eq (st_eq ?_) rfl⟩
    rw [stOf_head E B hx, stOf_replace]
    simp [Ent.enc, intSyms_natCast]
  | pushZ x =>
    simp only [Op.step, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine (sound_fw ρ (by simp [Prog.Closed, Prog.FreeBelow, pushC]) E _ m 0 1 1 (fun r => ?_)
      (by omega) (allLe_push hA le_rfl x (.I 0) (by simp [Ent.len, bitLen_zero]))).mono
      (le_post _ _ _)
    have e : Eval [] (pushC x .pos) ⟨r, stOf E B⟩
        ⟨r, Function.update (stOf E B) x (Sym.pos :: stOf E B x)⟩ 1 := Eval.push _ _ _ _ _
    refine ⟨_, 1, le_rfl, e.of_eq (st_eq ?_) rfl⟩
    rw [stOf_push]
    simp [Ent.enc, intSyms_eq, sgnSym, natSyms_zero]
  | pushS k =>
    simp only [Op.step, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine (sound_fw ρ (by simp [Prog.Closed, Prog.FreeBelow, pushC]) E _ m 0 1 1 (fun r => ?_)
      (by omega) (allLe_push hA le_rfl k .S (Nat.zero_le _))).mono
      (le_post _ _ _)
    have e : Eval [] (pushC k .sep) ⟨r, stOf E B⟩
        ⟨r, Function.update (stOf E B) k (Sym.sep :: stOf E B k)⟩ 1 := Eval.push _ _ _ _ _
    refine ⟨_, 1, le_rfl, e.of_eq (st_eq ?_) rfl⟩
    rw [stOf_push]
    rfl
  | popS k =>
    simp only [Op.step] at h
    obtain ⟨es, hes, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hk := headS_some hes
    refine (sound_fw ρ (by simp [Prog.Closed, Prog.FreeBelow, popR]) E _ m 0 1 1 (fun r => ?_)
      (by omega) (hA.update k _ (hA.tail hk))).mono (le_post _ _ _)
    have e : Eval [] (popR k) ⟨r, stOf E B⟩ ⟨(stOf E B k).head?,
        Function.update (stOf E B) k (stOf E B k).tail⟩ 1 := Eval.pop _ _ _ _ _
    refine ⟨_, 1, le_rfl, e.of_eq (st_eq ?_) rfl⟩
    rw [stOf_head E B hk, stOf_replace]
    rfl
  | clr k =>
    simp only [Op.step] at h
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    split_ifs at h with hlen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hk, hnoS⟩ := splitS_some hp
    have hl := lenLe_sound clrMax p.1 hlen
    have hl3 : p.1.length ≤ 3 := hl
    have hes : ∀ e ∈ p.1, e.len ≤ m := fun e he => hA k e (by rw [hk]; simp [he])
    have hlen' := encL_length_le p.1 hes
    have hS : stOf E B k = encL p.1 ++ Sym.sep :: (encL p.2 ++ B k) := by
      rw [stOf_apply, hk, encL_append]
      simp [Ent.enc, List.append_assoc]
    have h2 : p.1.length * (m + 1) ≤ 3 * (m + 1) := Nat.mul_le_mul_right _ hl3
    have h3 : 4 * (8 * m + 16) ≤ (clrMax + 1) * unit Cu m := by
      have := Nat.mul_le_mul_left 4 hu
      show 4 * (8 * m + 16) ≤ (3 + 1) * unit Cu m
      omega
    refine (sound_fw ρ (clrP_closed _) E _ m (clrMax + 1) 0 (3 * (encL p.1).length + 2)
      (fun r => ⟨_, _, le_rfl, (clr_eval [] r (encL p.1) (encL p.2 ++ B k) (stOf E B)
        (sep_not_mem_encL _ hnoS) hS).of_eq (st_eq ?_) rfl⟩) (by omega) ?_).mono
      (le_post _ _ _)
    · rw [stOf_replace]; rfl
    · refine hA.update k _ ?_
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact Nat.zero_le _
      · exact hA k e (by rw [hk]; simp [he])
  | shr1 x =>
    simp only [Op.step] at h
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hx, htx⟩ := needN_some hp
    have hv : bitLen p.1 ≤ m := hA.of_mem hx
    refine (sound_fw ρ (shr1P_closed _) E _ m 0 3 3 (fun r => ?_) (by omega)
      (allLe_replace hA le_rfl hx (.N (p.1 / 2)) (le_trans (bitLen_div_le _ _) hv))).mono
      (le_post _ _ _)
    obtain ⟨r', e⟩ := shr1_eval [] r p.1 (encL p.2 ++ B x) (stOf E B) (tok_sound (hB x) htx)
      (stOf_head E B hx)
    refine ⟨r', 3, le_rfl, e.of_eq (st_eq ?_) rfl⟩
    rw [stOf_replace]
    simp [Ent.enc, List.append_assoc]
  | sfix r x y =>
    simp only [Op.step] at h
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hr, htr⟩ := needI_some hp
    have hx := headI_some ha
    have hy := headI_some hb
    have hv : bitLen p.1.natAbs ≤ m := hA.of_mem hr
    have hv' : bitLen (sgnFix a.1 b.1 p.1).natAbs ≤ m := by
      unfold sgnFix
      split
      · exact hv
      · rw [bitLen_natAbs_neg]; exact hv
    refine (sound_fw ρ (sfixP_closed _ _ _) E _ m 0 10 10 (fun reg => ?_) (by omega)
      (allLe_replace hA le_rfl hr (.I (sgnFix a.1 b.1 p.1)) hv')).mono
      (le_post _ _ _)
    obtain ⟨r', t, ht, e⟩ := sfix_eval [] reg a.1 b.1 p.1 (encL a.2 ++ B x) (encL b.2 ++ B y)
      (encL p.2 ++ B r) (stOf E B) (stOf_head E B hx) (stOf_head E B hy)
      (tok_sound (hB r) htr) (stOf_head E B hr)
    refine ⟨r', t, ht, e.of_eq (st_eq ?_) rfl⟩
    rw [stOf_replace]
    simp [Ent.enc, List.append_assoc]

theorem skip_triple {σ : Type} (S : L → List Sym) (ρ : List (Prog L (fun _ => Sym) σ)) :
    Triple ρ (fun s => s.stk = S) (skip : Prog L (fun _ => Sym) σ) (fun s => s.stk = S) 1 := by
  rintro ⟨v, stk⟩ hs
  exact ⟨⟨v, stk⟩, 1, skip_eval ρ _, hs, le_rfl⟩

/-- **Soundness of the interpreter.** -/
theorem run_sound {U : Subs} {Cu : ℕ} (hU : SubsOK U Cu) {bok : L → Bool} {B : L → List Sym}
    (hB : ∀ k, bok k = true → TermOK (B k)) (ρ : List (Prog L (fun _ => Sym) U.σ)) (kb : ℕ) :
    ∀ (os : List Op) (E E' : L → List Ent) (P : Prop) (m : ℕ), run bok kb os E = some (E', P) →
      P → AllLe E m →
      Triple ρ (fun s => s.stk = stOf E B) (seqOf U os) (fun s => s.stk = stOf E' B)
        (unitsOf os * unit Cu (m + dmOf os + dkOf os * kb) + constsOf os + 1) ∧
      AllLe E' (m + dmOf os + dkOf os * kb)
  | [], E, E', P, m, h, _, hA => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [unitsOf, constsOf, dmOf, dkOf, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
    exact ⟨skip_triple _ ρ, hA⟩
  | o :: os, E, E', P, m, h, hP, hA => by
    simp only [run] at h
    obtain ⟨r1, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r2, h2, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hP1, hP2⟩ := hP
    obtain ⟨T1, hA1⟩ := Op.sound hU hB ρ kb o E r1.1 r1.2 m h1 hP1 hA
    obtain ⟨T2, hA2⟩ := run_sound hU hB ρ kb os r1.1 r2.1 r2.2 (m + o.dm + o.dk * kb) h2 hP2 hA1
    have e : m + o.dm + o.dk * kb + dmOf os + dkOf os * kb =
        m + dmOf (o :: os) + dkOf (o :: os) * kb := by
      simp only [dmOf, dkOf, Nat.add_mul]
      omega
    rw [e] at T2 hA2
    refine ⟨(Triple.seq T1 T2).cost_mono ?_, hA2⟩
    have hu := unit_mono Cu (show m + o.dm + o.dk * kb ≤ m + dmOf (o :: os) + dkOf (o :: os) * kb by
      rw [← e]; omega)
    have := Nat.mul_le_mul_left o.units hu
    simp only [unitsOf, constsOf]
    rw [Nat.add_mul]
    omega

#assert_std_axioms Op.sound run_sound unit_mono w3_update1 w3_update2 splitS_some nd_two
  lenLe_sound

end WP.W5
