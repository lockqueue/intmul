import WP.W5.Arith
import Mathlib.Data.Fin.VecNotation

/-!
# WP.W5.State — abstract stack states, subroutine bundle, embeddings

* **Stacks.** The program runs over `L = Loc 3 8`: `X, Y` (operands), `Z` (destination), `s0 … s7`
  (scratch).
* **Abstract entries.** A stack is `encL es ++ base`, where `es : List Ent` lists what *this level*
  pushed (top first): signed numbers `I z` (`intSyms z`), unsigned numbers `N n` (`natSyms n`) and
  separators `S` (`Sym.sep`). `stOf E B` is the concrete stack function.
* **`tok`**: a conservative, *computable* check that `encL es ++ base` is `TermOK` (the head is a
  sign symbol or `sep`, or the base is known `TermOK`).
* **`AllLe E m`**: every entry has bit length `≤ m` (drives all cost bounds).
* **Subroutines.** `Subs` bundles the W3 programs (each over its own `Loc n m`, `m ≤ 4`, with its
  own registers); `SubsOK U Cu` states their W3 contracts with the common constant `Cu`. The
  program's registers are `Option Sym` (framework macros) times all subroutine registers.
* **Embedding.** `emb names ks` maps a subroutine's named stacks to `names` and its scratch stacks to
  `scr ks`, four stacks outside `ks`; `emb_inj` derives injectivity from a `Nodup` check that the
  interpreter evaluates on concrete stack names.
-/

namespace WP.W5

open TMFw TMFw.Contracts TMFw.Lib Computability

/-- Stack names (an enumeration: decidable equality reduces in one step during the
interpreter's symbolic evaluation). Mapped to `Loc 3 8` by `skLoc` at the contract boundary. -/
inductive SK where
  | X | Y | Z | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7
  deriving DecidableEq, Repr

/-- The program's stacks. -/
abbrev L := SK

/-- Operand `x`. -/ abbrev X : L := .X
/-- Operand `y`. -/ abbrev Y : L := .Y
/-- Destination `z`. -/ abbrev Z : L := .Z
/-- Scratch stacks. -/ abbrev s0 : L := .s0
/-- Scratch. -/ abbrev s1 : L := .s1
/-- Scratch. -/ abbrev s2 : L := .s2
/-- Scratch. -/ abbrev s3 : L := .s3
/-- Scratch. -/ abbrev s4 : L := .s4
/-- Scratch. -/ abbrev s5 : L := .s5
/-- Scratch. -/ abbrev s6 : L := .s6
/-- Scratch. -/ abbrev s7 : L := .s7

/-! ## Abstract entries -/

/-- An entry pushed by the current level. -/
inductive Ent where
  /-- signed number `intSyms z` -/
  | I (z : ℤ)
  /-- unsigned number `natSyms n` -/
  | N (n : ℕ)
  /-- separator `sep` -/
  | S

namespace Ent

/-- Symbols of an entry. -/
def enc : Ent → List Sym
  | I z => intSyms z
  | N n => natSyms n
  | S => [Sym.sep]

/-- Bit length of an entry. -/
def len : Ent → ℕ
  | I z => bitLen z.natAbs
  | N n => bitLen n
  | S => 0

end Ent

/-- Symbols of an entry list (top first). -/
def encL : List Ent → List Sym
  | [] => []
  | e :: es => e.enc ++ encL es

@[simp] theorem encL_nil : encL [] = [] := rfl
@[simp] theorem encL_cons (e : Ent) (es : List Ent) : encL (e :: es) = e.enc ++ encL es := rfl

/-- Concrete stacks from abstract entries `E` over bases `B`. -/
def stOf (E : L → List Ent) (B : L → List Sym) : L → List Sym := fun k => encL (E k) ++ B k

theorem stOf_apply (E : L → List Ent) (B : L → List Sym) (k : L) :
    stOf E B k = encL (E k) ++ B k := rfl

theorem stOf_update (E : L → List Ent) (B : L → List Sym) (k : L) (v : List Ent) :
    stOf (Function.update E k v) B = Function.update (stOf E B) k (encL v ++ B k) := by
  funext j
  by_cases h : j = k
  · subst h; simp [stOf]
  · simp [stOf, Function.update_of_ne h]

theorem sgnSym_isBit (z : ℤ) : (sgnSym z).isBit = false := by
  unfold sgnSym; split <;> rfl

theorem intSyms_eq (z : ℤ) : intSyms z = sgnSym z :: natSyms z.natAbs := rfl

/-- Conservative `TermOK` check of `encL es ++ base`; `bk` says whether the base is `TermOK`. -/
def tok (bk : Bool) : List Ent → Bool
  | [] => bk
  | .I _ :: _ => true
  | .S :: _ => true
  | .N _ :: _ => false

theorem tok_sound {bk : Bool} {b : List Sym} (hb : bk = true → TermOK b) :
    ∀ {es : List Ent}, tok bk es = true → TermOK (encL es ++ b)
  | [], h => by simpa using hb h
  | .I z :: es, _ => by
      simp only [encL_cons, Ent.enc, intSyms_eq, List.cons_append]
      exact TermOK.cons (sgnSym_isBit z) _
  | .S :: es, _ => by
      simp only [encL_cons, Ent.enc, List.cons_append]
      exact TermOK.cons rfl _
  | .N _ :: _, h => by simp [tok] at h

/-- Every entry has bit length at most `m`. -/
def AllLe (E : L → List Ent) (m : ℕ) : Prop := ∀ k, ∀ e ∈ E k, e.len ≤ m

theorem AllLe.mono {E : L → List Ent} {m m' : ℕ} (h : AllLe E m) (hm : m ≤ m') : AllLe E m' :=
  fun k e he => le_trans (h k e he) hm

theorem AllLe.of_mem {E : L → List Ent} {m : ℕ} (h : AllLe E m) {k : L} {e : Ent} {es : List Ent}
    (hk : E k = e :: es) : e.len ≤ m := h k e (by rw [hk]; exact List.mem_cons_self ..)

theorem AllLe.tail {E : L → List Ent} {m : ℕ} (h : AllLe E m) {k : L} {e : Ent} {es : List Ent}
    (hk : E k = e :: es) : ∀ e' ∈ es, e'.len ≤ m :=
  fun e' he' => h k e' (by rw [hk]; exact List.mem_cons_of_mem _ he')

theorem AllLe.update {E : L → List Ent} {m : ℕ} (h : AllLe E m) (k : L) (v : List Ent)
    (hv : ∀ e ∈ v, e.len ≤ m) : AllLe (Function.update E k v) m := by
  intro j e he
  by_cases hj : j = k
  · subst hj; rw [Function.update_self] at he; exact hv e he
  · rw [Function.update_of_ne hj] at he; exact h j e he

theorem AllLe.all {E : L → List Ent} {m : ℕ} (h : AllLe E m) (k : L) : ∀ e ∈ E k, e.len ≤ m :=
  h k

/-- Length of the symbols of a bounded entry list. -/
theorem encL_length_le {m : ℕ} : ∀ (es : List Ent), (∀ e ∈ es, e.len ≤ m) →
    (encL es).length ≤ es.length * (m + 1)
  | [], _ => by simp
  | e :: es, h => by
    have ih := encL_length_le es (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he := h e (List.mem_cons_self ..)
    have h1 : e.enc.length ≤ m + 1 := by
      cases e with
      | I z => simp only [Ent.enc, intSyms_eq, List.length_cons, length_natSyms]; exact
          Nat.succ_le_succ he
      | N n => simp only [Ent.enc, length_natSyms]; exact le_trans he (Nat.le_succ m)
      | S => simp [Ent.enc]
    simp only [encL_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- No entry of the list is a separator. -/
def noS : List Ent → Bool
  | [] => true
  | .S :: _ => false
  | _ :: es => noS es

theorem sep_not_mem_enc : ∀ (e : Ent), (e = .S → False) → Sym.sep ∉ e.enc
  | .I z, _ => by
      simp only [Ent.enc, intSyms_eq, natSyms, List.mem_cons, List.mem_map, not_or]
      refine ⟨?_, ?_⟩
      · unfold sgnSym; split <;> simp
      · rintro ⟨b, -, h⟩; cases h
  | .N n, _ => by
      simp only [Ent.enc, natSyms, List.mem_map, not_exists, not_and]
      intro b _ h; cases h
  | .S, h => absurd rfl h

theorem sep_not_mem_encL : ∀ (es : List Ent), noS es = true → Sym.sep ∉ encL es
  | [], _ => by simp
  | .S :: _, h => by simp [noS] at h
  | .I z :: es, h => by
      simp only [encL_cons, List.mem_append, not_or]
      exact ⟨sep_not_mem_enc (.I z) (fun h => Ent.noConfusion h),
        sep_not_mem_encL es (by simpa [noS] using h)⟩
  | .N n :: es, h => by
      simp only [encL_cons, List.mem_append, not_or]
      exact ⟨sep_not_mem_enc (.N n) (fun h => Ent.noConfusion h),
        sep_not_mem_encL es (by simpa [noS] using h)⟩

/-! ## Subroutines -/

/-- One subroutine program: `n` named stacks, `m ≤ 4` scratch stacks, own registers `R`. -/
structure Sub (n : ℕ) where
  /-- scratch count -/
  m : ℕ
  /-- scratch bound (W3 contracts allow 4) -/
  hm : m ≤ 4
  /-- registers -/
  R : Type
  /-- the program -/
  P : Prog (Loc n m) (fun _ => Sym) R

/-- The W3 subroutines used by Toom-3. -/
structure Subs where
  /-- `W3_addInt` -/
  add : Sub 3
  /-- `W3_subInt` -/
  sub : Sub 3
  /-- `W3_smallOpInt .mul2` -/
  mul2 : Sub 1
  /-- `W3_smallOpInt .div2` -/
  div2 : Sub 1
  /-- `W3_smallOpInt .div3` -/
  div3 : Sub 1
  /-- `W3_splitAt` -/
  split : Sub 3
  /-- `W3_shlVar` -/
  shl : Sub 2

/-- Registers: the framework macros' `Option Sym`, then every subroutine's registers. -/
abbrev Subs.σ (U : Subs) : Type :=
  Option Sym × (U.add.R × (U.sub.R × (U.mul2.R × (U.div2.R × (U.div3.R × (U.split.R × U.shl.R))))))

/-- Lens: the framework macro register. -/
def lR (U : Subs) : Lens U.σ (Option Sym) := Lens.fst _ _
/-- Lens: `add` registers. -/
def lAdd (U : Subs) : Lens U.σ U.add.R := (Lens.snd _ _).comp (Lens.fst _ _)
/-- Lens: `sub` registers. -/
def lSub (U : Subs) : Lens U.σ U.sub.R := (Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))
/-- Lens: `mul2` registers. -/
def lMul2 (U : Subs) : Lens U.σ U.mul2.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _)))
/-- Lens: `div2` registers. -/
def lDiv2 (U : Subs) : Lens U.σ U.div2.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    (Lens.fst _ _))))
/-- Lens: `div3` registers. -/
def lDiv3 (U : Subs) : Lens U.σ U.div3.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp (Lens.fst _ _)))))
/-- Lens: `split` registers. -/
def lSplit (U : Subs) : Lens U.σ U.split.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.fst _ _))))))
/-- Lens: `shl` registers. -/
def lShl (U : Subs) : Lens U.σ U.shl.R :=
  (Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp ((Lens.snd _ _).comp
    ((Lens.snd _ _).comp ((Lens.snd _ _).comp (Lens.snd _ _))))))

/-- The W3 contracts of the subroutines, with one constant `Cu` (the W3 contract bodies). -/
structure SubsOK (U : Subs) (Cu : ℕ) : Prop where
  add_c : U.add.P.Closed
  add : ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 U.add.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs U.add.P S (Function.update S (.inl 2) (intSyms (a + b) ++ S (.inl 2))) (fun _ => True)
      (Cu * (bitLen a.natAbs + bitLen b.natAbs + 1))
  sub_c : U.sub.P.Closed
  sub : ∀ (a b : ℤ) (rx ry : List Sym) (S : Loc 3 U.sub.m → List Sym), TermOK rx → TermOK ry →
    S (.inl 0) = intSyms a ++ rx → S (.inl 1) = intSyms b ++ ry →
    Runs U.sub.P S (Function.update S (.inl 2) (intSyms (a - b) ++ S (.inl 2))) (fun _ => True)
      (Cu * (bitLen a.natAbs + bitLen b.natAbs + 1))
  mul2_c : U.mul2.P.Closed
  mul2 : ∀ (z : ℤ) (rx : List Sym) (S : Loc 1 U.mul2.m → List Sym), TermOK rx →
    SmallOp.ok .mul2 z → S (.inl 0) = intSyms z ++ rx →
    Runs U.mul2.P S (Function.update S (.inl 0) (intSyms (SmallOp.apply .mul2 z) ++ rx))
      (fun _ => True) (Cu * (bitLen z.natAbs + 1))
  div2_c : U.div2.P.Closed
  div2 : ∀ (z : ℤ) (rx : List Sym) (S : Loc 1 U.div2.m → List Sym), TermOK rx →
    SmallOp.ok .div2 z → S (.inl 0) = intSyms z ++ rx →
    Runs U.div2.P S (Function.update S (.inl 0) (intSyms (SmallOp.apply .div2 z) ++ rx))
      (fun _ => True) (Cu * (bitLen z.natAbs + 1))
  div3_c : U.div3.P.Closed
  div3 : ∀ (z : ℤ) (rx : List Sym) (S : Loc 1 U.div3.m → List Sym), TermOK rx →
    SmallOp.ok .div3 z → S (.inl 0) = intSyms z ++ rx →
    Runs U.div3.P S (Function.update S (.inl 0) (intSyms (SmallOp.apply .div3 z) ++ rx))
      (fun _ => True) (Cu * (bitLen z.natAbs + 1))
  split_c : U.split.P.Closed
  split : ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 3 U.split.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs U.split.P S (Function.update (Function.update S (.inl 0) (natSyms (a / 2 ^ c) ++ rx))
        (.inl 2) (natSyms (a % 2 ^ c) ++ S (.inl 2))) (fun _ => True)
      (Cu * (min c (bitLen a) + bitLen c + 1))
  shl_c : U.shl.P.Closed
  shl : ∀ (a c : ℕ) (rx rc : List Sym) (S : Loc 2 U.shl.m → List Sym), TermOK rx → TermOK rc →
    S (.inl 0) = natSyms a ++ rx → S (.inl 1) = natSyms c ++ rc →
    Runs U.shl.P S (Function.update S (.inl 0) (natSyms (a * 2 ^ c) ++ rx)) (fun _ => True)
      (Cu * (c + bitLen c + 1))
  /-- register types are finite (W3 `MContract`) -/
  fin : Finite U.add.R ∧ Finite U.sub.R ∧ Finite U.mul2.R ∧ Finite U.div2.R ∧ Finite U.div3.R ∧
    Finite U.split.R ∧ Finite U.shl.R
  /-- register types are nonempty (W3 `MContract`) -/
  ne : Nonempty U.add.R ∧ Nonempty U.sub.R ∧ Nonempty U.mul2.R ∧ Nonempty U.div2.R ∧
    Nonempty U.div3.R ∧ Nonempty U.split.R ∧ Nonempty U.shl.R

/-! ## Embedding subroutines -/

/-- All stacks, in the order used to pick scratch stacks. -/
def allL : List L := [s4, s5, s6, s7, s0, s1, s2, s3, X, Y, Z]

/-- Four stacks outside `ks` (validated by a `Nodup` check at each use). -/
def scr (ks : List L) (j : Fin 4) : L := (allL.filter (fun k => !(ks.contains k))).getD j.val X

/-- Named stacks to `names`, scratch stacks to `scr ks`. -/
def emb {n m : ℕ} (names : Fin n → L) (ks : List L) (hm : m ≤ 4) : Loc n m → L :=
  Sum.elim names (fun j => scr ks (Fin.castLE hm j))

theorem emb_inj {n m : ℕ} (names : Fin n → L) (ks : List L) (hm : m ≤ 4)
    (hnd : (List.ofFn names ++ List.ofFn (scr ks)).Nodup) :
    Function.Injective (emb names ks hm) := by
  rw [List.nodup_append] at hnd
  obtain ⟨h1, h2, h3⟩ := hnd
  rw [List.nodup_ofFn] at h1 h2
  intro p q hpq
  rcases p with i | j <;> rcases q with i' | j'
  · exact congrArg Sum.inl (h1 hpq)
  · exfalso
    exact h3 (names i) (List.mem_ofFn.2 ⟨i, rfl⟩) _ (List.mem_ofFn.2 ⟨Fin.castLE hm j', rfl⟩) hpq
  · exfalso
    exact h3 (names i') (List.mem_ofFn.2 ⟨i', rfl⟩) _ (List.mem_ofFn.2 ⟨Fin.castLE hm j, rfl⟩)
      hpq.symm
  · have := h2 hpq
    exact congrArg Sum.inr (Fin.castLE_injective hm this)

/-! ## Closedness is preserved by the combinators -/

theorem freeBelow_liftRegs {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ) :
    ∀ (p : Prog K Γ τ) (d : ℕ), p.FreeBelow d → (p.liftRegs l).FreeBelow d
  | .push _ _, _, _ => trivial
  | .peek _ _, _, _ => trivial
  | .pop _ _, _, _ => trivial
  | .load _, _, _ => trivial
  | .seq p q, d, h => ⟨freeBelow_liftRegs l p d h.1, freeBelow_liftRegs l q d h.2⟩
  | .ite _ p q, d, h => ⟨freeBelow_liftRegs l p d h.1, freeBelow_liftRegs l q d h.2⟩
  | .loop _ p, d, h => freeBelow_liftRegs l p d h
  | .fix b, d, h => freeBelow_liftRegs l b (d + 1) h
  | .recur _, _, h => h

theorem freeBelow_mapStk {K K' A σ : Type} (ι : K → K') :
    ∀ (p : Prog K (fun _ => A) σ) (d : ℕ), p.FreeBelow d → (p.mapStk ι).FreeBelow d
  | .push _ _, _, _ => trivial
  | .peek _ _, _, _ => trivial
  | .pop _ _, _, _ => trivial
  | .load _, _, _ => trivial
  | .seq p q, d, h => ⟨freeBelow_mapStk ι p d h.1, freeBelow_mapStk ι q d h.2⟩
  | .ite _ p q, d, h => ⟨freeBelow_mapStk ι p d h.1, freeBelow_mapStk ι q d h.2⟩
  | .loop _ p, d, h => freeBelow_mapStk ι p d h
  | .fix b, d, h => freeBelow_mapStk ι b (d + 1) h
  | .recur _, _, h => h

theorem closed_liftRegs {K : Type} {Γ : K → Type} {σ τ : Type} (l : Lens σ τ) {p : Prog K Γ τ}
    (h : p.Closed) : (p.liftRegs l).Closed := freeBelow_liftRegs l p 0 h

theorem closed_mapStk {K K' A σ : Type} (ι : K → K') {p : Prog K (fun _ => A) σ} (h : p.Closed) :
    (p.mapStk ι).Closed := freeBelow_mapStk ι p 0 h

/-- **Embedded subroutine triple.** A local `Runs` spec of a closed program, transported along an
injective stack embedding and a register lens, as a triple on full stack functions (any
environment). -/
theorem embed_triple {n m : ℕ} {R σ : Type} {P : Prog (Loc n m) (fun _ => Sym) R} (hc : P.Closed)
    {ι : Loc n m → L} (hι : Function.Injective ι) (l : Lens σ R) {S S' : L → List Sym}
    {Q : R → Prop} {T : ℕ} (h : Runs P (fun j => S (ι j)) (fun j => S' (ι j)) Q T)
    (hout : ∀ k, (∀ j, ι j ≠ k) → S' k = S k) (ρ : List (Prog L (fun _ => Sym) σ)) :
    Triple ρ (fun s => s.stk = S) ((P.mapStk ι).liftRegs l) (fun s => s.stk = S') T := by
  have h1 := Runs.embed hι h S (fun _ => rfl)
  have h2 := Triple.liftRegs l h1 (fun _ => True) (fun _ _ _ => trivial)
  have h3 := h2.env_irrel (closed_liftRegs l (closed_mapStk ι hc)) ρ
  refine h3.conseq (fun s hs => ⟨hs, trivial⟩) ?_ le_rfl
  rintro s ⟨⟨hin, hout', -⟩, -⟩
  funext k
  by_cases hk : ∃ j, ι j = k
  · obtain ⟨j, rfl⟩ := hk
    exact hin j
  · push_neg at hk
    rw [hout' k hk, hout k hk]

#assert_std_axioms stOf_update tok_sound encL_length_le sep_not_mem_encL emb_inj embed_triple
  closed_liftRegs closed_mapStk

end WP.W5
