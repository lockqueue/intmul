/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Streams
import SubNLogN.Machine.Contracts.Family
import IntMulTM.Framework.Lib.CompareEval
import IntMulTM.Framework.Lib.Counter
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# K1 digit engine, part 1 (`K1/DigitWalk.lean`): a descriptor-driven walk over radix-`q` addresses

Paper: Fact 3.3(1) (`fact:oai-streams`) and Lemma A.4(1)–(2) (`lem:transfer-streams`,
proof: split into `q²` resp. `q` streams by
digit values, then merge, the selected digits taking another place in the nested merge).

**Scope (honest summary).** This file contains a generic program skeleton and its exact
evaluation lemma. No contract of `Contracts/Streams.lean` is proved here; see
`K1/DigitPairPerm.lean` and `K1/DigitMoveDigitMix.lean`.

## Program design (shared by K1a `pairPerm` and K1b `moveDigit`)
* A **descriptor** stack holds one label per address digit position, digit `0` (most significant)
  on top, then the end symbol `endSym`: label `A` marks the first key digit, `B` the second key
  digit, `P` a spectator digit (`labSym`). It is built once from the runtime counters `k, i, j`
  (`K1/DigitBuild.lean`); building costs `O(k log k) = O(2^k)`, absorbed by `V ≥ q^k`.
* The **walk** `walk desc ord leaf = fix walkBody` pops one label. For a label it makes `q`
  recursive calls, one per digit value `c` in the list `ord` (ascending or descending), first
  storing `c` in the key register component of the label (`updKey`), and finally pushes the label
  back. On `endSym` it pushes it back and runs `leaf` once. Hence the leaves run in address order
  (`ord` ascending) or reverse address order (`ord` descending), and at the leaf for address `x`
  the key register holds the key digits of `x` (`keyAt`). Since `q` is fixed, the `q` calls are
  unrolled (`forEachProg`), so no loop counter has to survive a recursive call.
* **Cost.** Every node costs at most `3q + 6` steps besides its children, and the tree has
  `nodes q k ≤ 2 q^k` nodes (`q ≥ 2`), so the overhead is `O(q^k) = O(V)`.
* **Invariants** (`walk_body_spec`): a sub-walk with remaining descriptor `D` starts and ends with
  the descriptor stack `D ++ endSym :: rest`; leaf costs telescope against a potential `Pot`; the
  final key `Agree`s with the initial key on every component that `D` does not set.

## Main results
* `walk_body_spec`, `walk_spec`: exact evaluation of the walk, given exact evaluations of the leaf
  at every leaf time (`LeafHyps`), with cost `Pot t0 - Pot (t0 + q^|D|) + cN · nodes q |D|`.
-/

namespace SubNLogN.Machine.K1Digit

open TMFw TMFw.Contracts TMFw.Lib

/-! ## Labels, keys, descriptors -/

/-- Digit-position labels: spectator `P`, first key digit `A`, second key digit `B`. -/
inductive Lab : Type
  | P
  | A
  | B
  deriving DecidableEq

/-- Stack symbol of a label. -/
def labSym : Lab → Sym
  | .P => .tag 0
  | .A => .tag 1
  | .B => .tag 2

/-- The descriptor end symbol (below the labels). -/
def endSym : Sym := .tag 3

theorem labSym_ne_end (l : Lab) : labSym l ≠ endSym := by cases l <;> decide

theorem labSym_inj {l l' : Lab} (h : labSym l = labSym l') : l = l' := by
  cases l <;> cases l' <;> first | rfl | exact absurd h (by decide)

/-- The key register: the two key digits. -/
abbrev Key (q : ℕ) : Type := Fin q × Fin q

/-- Registers of the K1 digit programs: the comparator registers `CReg` (whose first component is
the symbol register of the `Lib` routines) and the key. -/
abbrev Reg (q : ℕ) : Type := CReg × Key q

/-- Store digit `c` in the key component selected by a label. -/
def updKey {q : ℕ} : Lab → Fin q → Key q → Key q
  | .P, _, κ => κ
  | .A, c, κ => (c, κ.2)
  | .B, c, κ => (κ.1, c)

/-- Two keys agree on every component that the descriptor `D` does not set. -/
def Agree {q : ℕ} (D : List Lab) (κ κ' : Key q) : Prop :=
  (Lab.A ∉ D → κ.1 = κ'.1) ∧ (Lab.B ∉ D → κ.2 = κ'.2)

section AgreeLemmas

variable {q : ℕ}

theorem Agree.refl (D : List Lab) (κ : Key q) : Agree D κ κ := ⟨fun _ => rfl, fun _ => rfl⟩

theorem Agree.trans {D : List Lab} {a b c : Key q} (h1 : Agree D a b) (h2 : Agree D b c) :
    Agree D a c :=
  ⟨fun h => (h1.1 h).trans (h2.1 h), fun h => (h1.2 h).trans (h2.2 h)⟩

theorem Agree.cons {D : List Lab} {a b : Key q} (lab : Lab) (h : Agree D a b) :
    Agree (lab :: D) a b :=
  ⟨fun hA => h.1 (fun hm => hA (List.mem_cons_of_mem _ hm)),
    fun hB => h.2 (fun hm => hB (List.mem_cons_of_mem _ hm))⟩

theorem Agree.upd_self (D : List Lab) (lab : Lab) (c : Fin q) (κ : Key q) :
    Agree (lab :: D) (updKey lab c κ) κ := by
  cases lab with
  | P => exact Agree.refl _ _
  | A => exact ⟨fun h => absurd List.mem_cons_self h, fun _ => rfl⟩
  | B => exact ⟨fun _ => rfl, fun h => absurd List.mem_cons_self h⟩

theorem Agree.upd {D : List Lab} {lab : Lab} {a b : Key q} (c : Fin q)
    (h : Agree (lab :: D) a b) : Agree D (updKey lab c a) (updKey lab c b) := by
  cases lab with
  | P => exact ⟨fun hA => h.1 (by simp [hA]), fun hB => h.2 (by simp [hB])⟩
  | A => exact ⟨fun _ => rfl, fun hB => h.2 (by simp [hB])⟩
  | B => exact ⟨fun hA => h.1 (by simp [hA]), fun _ => rfl⟩

end AgreeLemmas

/-- The key at the leaf for address `x`: walk down the descriptor, storing the digit
`x / q^|rest|` (as an element of `Fin q`) at each label. -/
def keyAt (q : ℕ) [NeZero q] : List Lab → Key q → ℕ → Key q
  | [], κ, _ => κ
  | lab :: D, κ, x => keyAt q D (updKey lab (Fin.ofNat q (x / q ^ D.length)) κ) (x % q ^ D.length)

theorem keyAt_congr {q : ℕ} [NeZero q] :
    ∀ (D : List Lab) {κ κ' : Key q} (x : ℕ), Agree D κ κ' → keyAt q D κ x = keyAt q D κ' x
  | [], κ, κ', x, h => by
    simp only [keyAt]
    exact Prod.ext (h.1 (by simp)) (h.2 (by simp))
  | _ :: D, _, _, _, h => by
    simp only [keyAt]
    exact keyAt_congr D _ (Agree.upd _ h)

/-- Digit order of the `q` recursive calls: ascending (`true`) or descending (`false`). -/
def ordL (q : ℕ) (dir : Bool) : List (Fin q) :=
  if dir then List.finRange q else (List.finRange q).reverse

/-- The address handled by the `u`-th leaf of a block of `M` leaves. -/
def posL (dir : Bool) (M u : ℕ) : ℕ := if dir then u else M - 1 - u

/-- Number of nodes of the walk tree of depth `n`. -/
def nodes (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => 1 + q * nodes q n

theorem nodes_le {q : ℕ} (hq : 2 ≤ q) : ∀ n, nodes q n + 1 ≤ 2 * q ^ n
  | 0 => by simp [nodes]
  | n + 1 => by
    have ih := nodes_le hq n
    have h := Nat.mul_le_mul_left q ih
    have e1 : q * (nodes q n + 1) = q * nodes q n + q := by ring
    have e2 : q * (2 * q ^ n) = 2 * q ^ (n + 1) := by ring
    simp only [nodes]
    omega

theorem ordL_length (q : ℕ) (dir : Bool) : (ordL q dir).length = q := by
  cases dir <;> simp [ordL]

theorem ordL_getElem? {q : ℕ} [NeZero q] (dir : Bool) {m : ℕ} (hm : m < q) :
    (ordL q dir)[m]? = some (Fin.ofNat q (posL dir q m)) := by
  cases dir
  · simp only [ordL, posL, Bool.false_eq_true, if_false]
    rw [List.getElem?_reverse (by simpa using hm)]
    simp only [List.length_finRange]
    rw [List.getElem?_eq_getElem (by simp; omega)]
    simp only [List.getElem_finRange, Option.some.injEq]
    ext
    simp only [Fin.val_cast, Fin.val_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  · simp only [ordL, posL, if_true]
    rw [List.getElem?_eq_getElem (by simpa using hm)]
    simp only [List.getElem_finRange, Option.some.injEq]
    ext
    simp only [Fin.val_cast, Fin.val_ofNat]
    rw [Nat.mod_eq_of_lt hm]

theorem posL_lt {dir : Bool} {M u : ℕ} (h : u < M) : posL dir M u < M := by
  cases dir <;> simp [posL] <;> omega

theorem posL_split (dir : Bool) {q M m u : ℕ} (hm : m < q) (hu : u < M) :
    posL dir (M * q) (m * M + u) = posL dir q m * M + posL dir M u := by
  cases dir
  · simp only [posL, Bool.false_eq_true, if_false]
    obtain ⟨a, rfl⟩ : ∃ a, q = m + 1 + a := ⟨q - m - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, M = u + 1 + b := ⟨M - u - 1, by omega⟩
    rw [show m + 1 + a - 1 - m = a by omega, show u + 1 + b - 1 - u = b by omega]
    have h : (u + 1 + b) * (m + 1 + a) = (a * (u + 1 + b) + b) + 1 + (m * (u + 1 + b) + u) := by
      ring
    rw [h]
    omega
  · simp [posL]


/-! ## Programs -/

section Programs

variable {K : Type} {q : ℕ}

/-- K1 digit programs: stacks `K`, alphabet `Sym`, registers `Reg q`. -/
abbrev DProg (K : Type) (q : ℕ) : Type := Prog K (fun _ => Sym) (Reg q)

/-- Pop stack `k` into the symbol register. -/
def popSym (k : K) : DProg K q := .pop k fun v o => ((o, v.1.2), v.2)

/-- Push a constant. -/
def pushSym (k : K) (x : Sym) : DProg K q := .push k fun _ => x

/-- The symbol register holds `x`. -/
def isSymR (x : Sym) (v : Reg q) : Bool := decide (v.1.1 = some x)

/-- One recursive call for digit value `c`. -/
def child (lab : Lab) (c : Fin q) : DProg K q :=
  .seq (.load fun v => (v.1, updKey lab c v.2)) (.recur 0)

/-- The branch of a label: the `q` calls in the order `ord`, then push the label back. -/
def labBranch (desc : K) (ord : List (Fin q)) (lab : Lab) : DProg K q :=
  .seq (forEachProg ord (child lab)) (pushSym desc (labSym lab))

/-- The body of the walk (see the module doc). -/
def walkBody (desc : K) (ord : List (Fin q)) (leaf : DProg K q) : DProg K q :=
  .seq (popSym desc) (.ite (isSymR (labSym .P)) (labBranch desc ord .P)
    (.ite (isSymR (labSym .A)) (labBranch desc ord .A)
      (.ite (isSymR (labSym .B)) (labBranch desc ord .B) (.seq (pushSym desc endSym) leaf))))

/-- **The walk** over the addresses described by the descriptor stack `desc`. -/
def walk (desc : K) (ord : List (Fin q)) (leaf : DProg K q) : DProg K q :=
  .fix (walkBody desc ord leaf)

theorem freeBelow_mono' {K σ : Type} {Γ : K → Type} :
    ∀ (p : Prog K Γ σ) {d d' : ℕ}, p.FreeBelow d → d ≤ d' → p.FreeBelow d'
  | .push _ _, _, _, _, _ => trivial
  | .peek _ _, _, _, _, _ => trivial
  | .pop _ _, _, _, _, _ => trivial
  | .load _, _, _, _, _ => trivial
  | .seq p q, _, _, h, hd => ⟨freeBelow_mono' p h.1 hd, freeBelow_mono' q h.2 hd⟩
  | .ite _ p q, _, _, h, hd => ⟨freeBelow_mono' p h.1 hd, freeBelow_mono' q h.2 hd⟩
  | .loop _ p, _, _, h, hd => freeBelow_mono' p h hd
  | .fix b, _, _, h, hd => freeBelow_mono' b h (by omega)
  | .recur _, _, _, h, hd => Nat.lt_of_lt_of_le h hd

theorem freeBelow_forEachProg {α : Type} (f : α → DProg K q) (d : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (f a).FreeBelow d) → (forEachProg l f).FreeBelow d
  | [], _ => trivial
  | a :: l, h => ⟨h a List.mem_cons_self,
      freeBelow_forEachProg f d l (fun b hb => h b (List.mem_cons_of_mem a hb))⟩

theorem walk_closed (desc : K) (ord : List (Fin q)) (leaf : DProg K q) (h : leaf.Closed) :
    (walk desc ord leaf).Closed := by
  have hc : ∀ lab, (labBranch desc ord lab).FreeBelow 1 := fun lab =>
    ⟨freeBelow_forEachProg _ 1 ord (fun _ _ => ⟨trivial, Nat.zero_lt_one⟩), trivial⟩
  exact ⟨trivial, hc .P, hc .A, hc .B, trivial, freeBelow_mono' leaf h (Nat.zero_le 1)⟩

end Programs

/-! ## Exact evaluation of the walk -/

section WalkSpec

variable {K : Type} [DecidableEq K] {q : ℕ}

/-- Stacks of a sub-walk with remaining labels `D`: the base `G`, with the descriptor stack
showing `D`, then `endSym`, then `drest`. -/
def dSt (G : K → List Sym) (desc : K) (D : List Lab) (drest : List Sym) : K → List Sym :=
  Function.update G desc (D.map labSym ++ endSym :: drest)

/-- Exact leaf evaluations at the `n` consecutive leaf times `T, …, T + n - 1`; the `u`-th leaf
runs with key `keyOf u` (any other register content), keeps the key, and costs at most the drop
of the potential `Pot`. -/
def LeafHyps (leaf : DProg K q) (desc : K) (G : ℕ → K → List Sym) (drest : List Sym)
    (Pot : ℕ → ℕ) (keyOf : ℕ → Key q) (T n : ℕ) : Prop :=
  ∀ u < n, ∀ w0 : CReg, ∃ w1 c,
    Eval [] leaf ⟨(w0, keyOf u), dSt (G (T + u)) desc [] drest⟩
      ⟨(w1, keyOf u), dSt (G (T + u + 1)) desc [] drest⟩ c ∧ c + Pot (T + u + 1) ≤ Pot (T + u)

theorem pop_dSt (desc : K) (G : K → List Sym) (lab : Lab) (D : List Lab) (drest : List Sym)
    (ρ' : List (DProg K q)) (v : Reg q) :
    Eval ρ' (popSym desc) ⟨v, dSt G desc (lab :: D) drest⟩
      ⟨((some (labSym lab), v.1.2), v.2), dSt G desc D drest⟩ 1 := by
  refine (Eval.pop ρ' desc _ v _).of_eq ?_ rfl
  simp [dSt, Function.update_idem]

theorem pop_dSt_nil (desc : K) (G : K → List Sym) (drest : List Sym) (ρ' : List (DProg K q))
    (v : Reg q) :
    Eval ρ' (popSym desc) ⟨v, dSt G desc [] drest⟩
      ⟨((some endSym, v.1.2), v.2), Function.update G desc drest⟩ 1 := by
  refine (Eval.pop ρ' desc _ v _).of_eq ?_ rfl
  simp [dSt, Function.update_idem]

theorem push_end_dSt (desc : K) (G : K → List Sym) (drest : List Sym) (ρ' : List (DProg K q))
    (v : Reg q) :
    Eval ρ' (pushSym desc endSym) ⟨v, Function.update G desc drest⟩ ⟨v, dSt G desc [] drest⟩ 1 := by
  refine (Eval.push ρ' desc _ v _).of_eq ?_ rfl
  simp [dSt, Function.update_idem]

theorem push_lab_dSt (desc : K) (G : K → List Sym) (lab : Lab) (D : List Lab) (drest : List Sym)
    (ρ' : List (DProg K q)) (v : Reg q) :
    Eval ρ' (pushSym desc (labSym lab)) ⟨v, dSt G desc D drest⟩ ⟨v, dSt G desc (lab :: D) drest⟩ 1 := by
  refine (Eval.push ρ' desc _ v _).of_eq ?_ rfl
  simp [dSt, Function.update_idem]

variable [NeZero q] (desc : K) (dir : Bool) (leaf : DProg K q) (G : ℕ → K → List Sym)
  (drest : List Sym) (Pot : ℕ → ℕ) (cN : ℕ) (ρ : List (DProg K q))

/-- The statement of `walk_body_spec` for the remaining labels `D`. -/
def WalkOK (D : List Lab) : Prop :=
  ∀ (t0 : ℕ) (κ : Key q) (w : CReg),
    LeafHyps leaf desc G drest Pot (fun u => keyAt q D κ (posL dir (q ^ D.length) u)) t0
      (q ^ D.length) →
    ∃ w' κ' c, Eval (walkBody desc (ordL q dir) leaf :: ρ) (walkBody desc (ordL q dir) leaf)
        ⟨(w, κ), dSt (G t0) desc D drest⟩ ⟨(w', κ'), dSt (G (t0 + q ^ D.length)) desc D drest⟩ c ∧
      Agree D κ' κ ∧ c + Pot (t0 + q ^ D.length) ≤ Pot t0 + cN * nodes q D.length

theorem callSeq_spec (lab : Lab) (D : List Lab) (IH : WalkOK desc dir leaf G drest Pot cN ρ D)
    (t0 : ℕ) (κ : Key q) :
    ∀ (cs : List (Fin q)) (m0 : ℕ) (κc : Key q) (w : CReg),
      (∀ (m : ℕ) (c : Fin q), cs[m]? = some c →
        LeafHyps leaf desc G drest Pot
          (fun u => keyAt q D (updKey lab c κ) (posL dir (q ^ D.length) u))
          (t0 + (m0 + m) * q ^ D.length) (q ^ D.length)) →
      Agree (lab :: D) κc κ →
      ∃ w' κ' c, Eval (walkBody desc (ordL q dir) leaf :: ρ) (forEachProg cs (child lab))
          ⟨(w, κc), dSt (G (t0 + m0 * q ^ D.length)) desc D drest⟩
          ⟨(w', κ'), dSt (G (t0 + (m0 + cs.length) * q ^ D.length)) desc D drest⟩ c ∧
        Agree (lab :: D) κ' κ ∧
        c + Pot (t0 + (m0 + cs.length) * q ^ D.length) ≤
          Pot (t0 + m0 * q ^ D.length) + cs.length * (cN * nodes q D.length + 3) + 1
  | [], m0, κc, w, _, hag => by
    refine ⟨w, κc, 1, ?_, hag, ?_⟩
    · simp only [forEachProg_nil, List.length_nil, Nat.add_zero]
      exact skip_eval _ _
    · simp only [List.length_nil, Nat.add_zero, Nat.zero_mul]
      omega
  | c :: cs, m0, κc, w, hyps, hag => by
    have hy0 := hyps 0 c rfl
    have hconv : LeafHyps leaf desc G drest Pot
        (fun u => keyAt q D (updKey lab c κc) (posL dir (q ^ D.length) u))
        (t0 + m0 * q ^ D.length) (q ^ D.length) := by
      intro u hu w0
      have := hy0 u hu w0
      simp only [Nat.add_zero] at this ⊢
      rw [keyAt_congr D _ (Agree.upd c hag)]
      exact this
    obtain ⟨w1, κ1, c1, e1, hag1, hc1⟩ := IH (t0 + m0 * q ^ D.length) (updKey lab c κc) w hconv
    have hag1' : Agree (lab :: D) κ1 κ :=
      ((hag1.cons lab).trans (Agree.upd_self D lab c κc)).trans hag
    obtain ⟨w2, κ2, c2, e2, hag2, hc2⟩ := callSeq_spec lab D IH t0 κ cs (m0 + 1) κ1 w1
      (fun m c' h => by
        have := hyps (m + 1) c' (by simpa using h)
        rwa [show m0 + (m + 1) = m0 + 1 + m by omega] at this) hag1'
    have el : Eval (walkBody desc (ordL q dir) leaf :: ρ)
        (.load fun v : Reg q => (v.1, updKey lab c v.2))
        ⟨(w, κc), dSt (G (t0 + m0 * q ^ D.length)) desc D drest⟩
        ⟨(w, updKey lab c κc), dSt (G (t0 + m0 * q ^ D.length)) desc D drest⟩ 1 :=
      Eval.load _ _ _ _
    have er := Eval.recur (n := 0) (ρ := walkBody desc (ordL q dir) leaf :: ρ) rfl e1
    have hidx : t0 + (m0 + 1) * q ^ D.length = t0 + m0 * q ^ D.length + q ^ D.length := by ring
    rw [hidx] at e2 hc2
    refine ⟨w2, κ2, 1 + (c1 + 2) + c2, ?_, hag2, ?_⟩
    · have e := Eval.seq (Eval.seq el er) e2
      rw [show m0 + (c :: cs).length = m0 + 1 + cs.length by simp; omega]
      exact e
    · rw [show m0 + (c :: cs).length = m0 + 1 + cs.length by simp; omega]
      have hl : (c :: cs).length * (cN * nodes q D.length + 3) =
          cs.length * (cN * nodes q D.length + 3) + (cN * nodes q D.length + 3) := by
        simp only [List.length_cons]; ring
      rw [hl]
      generalize cN * nodes q D.length = X at *
      generalize cs.length * (X + 3) = Y at *
      omega

theorem labBranch_spec (lab : Lab) (D : List Lab) (IH : WalkOK desc dir leaf G drest Pot cN ρ D)
    (t0 : ℕ) (κ : Key q) (w : CReg)
    (hyps : LeafHyps leaf desc G drest Pot
      (fun u => keyAt q (lab :: D) κ (posL dir (q ^ (lab :: D).length) u)) t0
      (q ^ (lab :: D).length)) :
    ∃ w' κ' c, Eval (walkBody desc (ordL q dir) leaf :: ρ) (labBranch desc (ordL q dir) lab)
        ⟨(w, κ), dSt (G t0) desc D drest⟩
        ⟨(w', κ'), dSt (G (t0 + q ^ (lab :: D).length)) desc (lab :: D) drest⟩ c ∧
      Agree (lab :: D) κ' κ ∧
      c + Pot (t0 + q ^ (lab :: D).length) ≤ Pot t0 + q * (cN * nodes q D.length + 3) + 2 := by
  have hlen : q ^ (lab :: D).length = q ^ D.length * q := by
    simp only [List.length_cons, pow_succ]
  have hMpos : 0 < q ^ D.length := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne q))
  have hyps' : ∀ (m : ℕ) (c : Fin q), (ordL q dir)[m]? = some c →
      LeafHyps leaf desc G drest Pot (fun u => keyAt q D (updKey lab c κ) (posL dir (q ^ D.length) u))
        (t0 + (0 + m) * q ^ D.length) (q ^ D.length) := by
    intro m c hmc u hu w0
    have hm : m < q := by
      have h1 := (List.getElem?_eq_some_iff.1 hmc).1
      simpa [ordL_length] using h1
    rw [ordL_getElem? dir hm, Option.some.injEq] at hmc
    subst hmc
    have hlt : m * q ^ D.length + u < q ^ (lab :: D).length := by
      rw [hlen]
      calc m * q ^ D.length + u < m * q ^ D.length + q ^ D.length := by omega
        _ = (m + 1) * q ^ D.length := by ring
        _ ≤ q * q ^ D.length := Nat.mul_le_mul_right _ hm
        _ = q ^ D.length * q := by ring
    obtain ⟨w1, c', e, hc⟩ := hyps (m * q ^ D.length + u) hlt w0
    have hpos := posL_lt (dir := dir) hu
    have hkey : keyAt q (lab :: D) κ (posL dir (q ^ (lab :: D).length) (m * q ^ D.length + u)) =
        keyAt q D (updKey lab (Fin.ofNat q (posL dir q m)) κ) (posL dir (q ^ D.length) u) := by
      rw [hlen, posL_split dir hm hu]
      simp only [keyAt]
      congr 2
      · congr 1
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hMpos, Nat.div_eq_of_lt hpos, Nat.zero_add]
      · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpos]
    dsimp only at e hc ⊢
    rw [hkey] at e
    rw [show t0 + (0 + m) * q ^ D.length + u = t0 + (m * q ^ D.length + u) by ring]
    exact ⟨w1, c', e, hc⟩
  obtain ⟨w', κ', c, e, hag, hc⟩ := callSeq_spec desc dir leaf G drest Pot cN ρ lab D IH t0 κ
    (ordL q dir) 0 κ w hyps' (Agree.refl _ _)
  have ep := push_lab_dSt desc (G (t0 + (0 + (ordL q dir).length) * q ^ D.length)) lab D drest
    (walkBody desc (ordL q dir) leaf :: ρ) (w', κ')
  have hT : t0 + (0 + (ordL q dir).length) * q ^ D.length = t0 + q ^ (lab :: D).length := by
    rw [ordL_length, hlen]; ring
  rw [hT] at ep hc
  have hT0 : t0 + 0 * q ^ D.length = t0 := by ring
  rw [hT0] at e hc
  rw [hT] at e
  refine ⟨w', κ', c + 1, Eval.seq e ep, hag, ?_⟩
  rw [ordL_length] at hc
  omega

theorem walk_body_spec (hleaf : leaf.Closed) (hcN : 3 * q + 6 ≤ cN) :
    ∀ D : List Lab, WalkOK desc dir leaf G drest Pot cN ρ D
  | [] => by
    intro t0 κ w hyps
    obtain ⟨w1, c, e, hc⟩ := hyps 0 (by simp) (some endSym, w.2)
    simp only [keyAt, Nat.add_zero] at e hc
    have e' := e.env_irrel hleaf (walkBody desc (ordL q dir) leaf :: ρ)
    have ep := pop_dSt_nil desc (G t0) drest (walkBody desc (ordL q dir) leaf :: ρ) (w, κ)
    have eu := push_end_dSt desc (G t0) drest (walkBody desc (ordL q dir) leaf :: ρ)
      ((some endSym, w.2), κ)
    have eall := Eval.seq ep (Eval.ite_false (c := isSymR (labSym .P)) (p := labBranch desc (ordL q dir) .P) rfl
      (Eval.ite_false (c := isSymR (labSym .A)) (p := labBranch desc (ordL q dir) .A) rfl
        (Eval.ite_false (c := isSymR (labSym .B)) (p := labBranch desc (ordL q dir) .B) rfl
          (Eval.seq eu e'))))
    refine ⟨w1, κ, _, eall, Agree.refl _ _, ?_⟩
    simp only [List.length_nil, pow_zero, nodes]
    omega
  | lab :: D => by
    intro t0 κ w hyps
    obtain ⟨w', κ', c, e, hag, hc⟩ := labBranch_spec desc dir leaf G drest Pot cN ρ lab D
      (walk_body_spec hleaf hcN D) t0 κ (some (labSym lab), w.2) hyps
    have ep := pop_dSt desc (G t0) lab D drest (walkBody desc (ordL q dir) leaf :: ρ) (w, κ)
    have hnodes : cN * nodes q (lab :: D).length = cN + q * (cN * nodes q D.length) := by
      simp only [List.length_cons, nodes]; ring
    have hq3 : q * (cN * nodes q D.length + 3) = q * (cN * nodes q D.length) + 3 * q := by ring
    rw [hnodes]
    rw [hq3] at hc
    generalize q * (cN * nodes q D.length) = X at *
    cases lab with
    | P =>
      exact ⟨w', κ', 1 + (c + 1), Eval.seq ep (Eval.ite_true rfl e), hag, by omega⟩
    | A =>
      exact ⟨w', κ', 1 + (c + 1 + 1), Eval.seq ep (Eval.ite_false rfl (Eval.ite_true rfl e)), hag,
        by omega⟩
    | B =>
      exact ⟨w', κ', 1 + (c + 1 + 1 + 1),
        Eval.seq ep (Eval.ite_false rfl (Eval.ite_false rfl (Eval.ite_true rfl e))), hag, by omega⟩

/-- **The walk, exact.** From the sub-walk state of the full descriptor `D` at leaf time `t0`, with
any registers and key `κ`, `walk` runs the leaves `t0, …, t0 + q^|D| - 1` (the `u`-th for address
`posL dir (q^|D|) u`, with key `keyAt q D κ ·`), within the potential drop plus
`cN · nodes q |D| + 2`. -/
theorem walk_spec (hleaf : leaf.Closed) (hcN : 3 * q + 6 ≤ cN) (D : List Lab) (t0 : ℕ)
    (κ : Key q) (w : CReg)
    (hyps : LeafHyps leaf desc G drest Pot (fun u => keyAt q D κ (posL dir (q ^ D.length) u)) t0
      (q ^ D.length)) :
    ∃ w' κ' c, Eval ρ (walk desc (ordL q dir) leaf) ⟨(w, κ), dSt (G t0) desc D drest⟩
        ⟨(w', κ'), dSt (G (t0 + q ^ D.length)) desc D drest⟩ c ∧
      c + Pot (t0 + q ^ D.length) ≤ Pot t0 + cN * nodes q D.length + 2 := by
  obtain ⟨w', κ', c, e, -, hc⟩ :=
    walk_body_spec desc dir leaf G drest Pot cN ρ hleaf hcN D t0 κ w hyps
  exact ⟨w', κ', c + 2, Eval.fix e, by omega⟩

end WalkSpec

end SubNLogN.Machine.K1Digit
