/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.SplitMapMove

/-!
# K1c, the pointwise map on aligned digit tuples (`K1/SplitMapDigit.lean`)

**Scope (honest summary).** The K1c stack layout `L1 q` and register type `M1 q A`, and the
digit-level programs of the map phase with proved exact-stack specifications:
* `readT`: pop one `digitWidth A`-bit digit from each of the `q` stream stacks into a register
  buffer (`runsM_readT`);
* `writeT`: push the `q` output digits `g (input digits)` on the `q` output stacks
  (`runsM_writeT`);
* `digitStep = readT; writeT` (`runs_digitStep`).
Paper: Lemma A.4(3) (`lem:transfer-streams`, "use `q` streams"). Streams hold their blocks reversed,
so a digit's bits are popped most significant first; outputs are pushed in the same order, so
the output stacks hold the output records in `.down` orientation.
-/

namespace SubNLogN.Machine.K1.SMM

open TMFw TMFw.Contracts

/-! ## Layout -/

/-- Private scratch of the K1c kernel: `q` stream stacks, `q` output stacks, and four more
(`0` accumulator, `1` depth, `2` counter, `3` temporary). -/
abbrev E1 (q : ℕ) : Type := Fin q ⊕ (Fin q ⊕ Fin 4)

/-- Stacks of the K1c-mix kernel: named stacks `Fin 3` (`0` source, `1` destination, `2` the
counter `N1`) and the scratch `E1 q`. -/
abbrev L1 (q : ℕ) : Type := KLoc (Fin 3) (E1 q)

/-- A K1c stack state from its four component families. -/
abbrev mk1 {q : ℕ} (nm : Fin 3 → List Sym) (st ou : Fin q → List Sym) (ex : Fin 4 → List Sym) :
    L1 q → List Sym :=
  Sum.elim nm (Sum.elim st (Sum.elim ou ex))

abbrev SRC {q : ℕ} : L1 q := .inl 0
abbrev DST {q : ℕ} : L1 q := .inl 1
abbrev NC {q : ℕ} : L1 q := .inl 2
abbrev STRM {q : ℕ} (c : Fin q) : L1 q := .inr (.inl c)
abbrev OUT {q : ℕ} (c : Fin q) : L1 q := .inr (.inr (.inl c))
abbrev ACC {q : ℕ} : L1 q := .inr (.inr (.inr 0))
abbrev DEP {q : ℕ} : L1 q := .inr (.inr (.inr 1))
abbrev CNT {q : ℕ} : L1 q := .inr (.inr (.inr 2))
abbrev TMP {q : ℕ} : L1 q := .inr (.inr (.inr 3))

theorem mk1_eta {q : ℕ} (S : L1 q → List Sym) :
    S = mk1 (fun i => S (.inl i)) (fun c => S (.inr (.inl c))) (fun c => S (.inr (.inr (.inl c))))
      (fun j => S (.inr (.inr (.inr j)))) := by
  funext k
  rcases k with i | c | c | j <;> rfl

/-- Register buffer: one `digitWidth A`-bit group per stream. -/
abbrev M1 (q A : ℕ) : Type := Fin q → Fin (digitWidth A) → Bool

/-- K1c programs. -/
abbrev P1 (q A : ℕ) : Type := KP (L1 q) (M1 q A)

/-- Value of a buffered bit group (least significant bit first). -/
def decodeBuf {w : ℕ} (b : Fin w → Bool) : ℕ := TMFw.bitsVal ((List.finRange w).map b)

/-! ## Programs -/

section Progs

variable {q : ℕ} {A : ℕ}

/-- Pop bit `j` of the current digit of stream `c` into the buffer. -/
def popBit (c : Fin q) (j : Fin (digitWidth A)) : P1 q A :=
  .pop (STRM c) (fun r o => (o, Function.update r.2 c (Function.update (r.2 c) j (optBit o))))

/-- Push bit `j` of output digit `c`, computed from the buffer by `g`. -/
def pushBit (g : (Fin q → ℕ) → Fin q → ℕ) (c : Fin q) (j : Fin (digitWidth A)) : P1 q A :=
  .push (OUT c) (fun r => Sym.bit ((g (fun c' => decodeBuf (r.2 c')) c).testBit j))

/-- Read one digit tuple (bits most significant first). -/
def readT : P1 q A :=
  forEachFin q (fun c => forEachProg (List.finRange (digitWidth A)).reverse (popBit c))

/-- Write the `q` output digits (bits most significant first). -/
def writeT (g : (Fin q → ℕ) → Fin q → ℕ) : P1 q A :=
  forEachFin q (fun c => forEachProg (List.finRange (digitWidth A)).reverse (pushBit g c))

/-- One digit tuple: read, apply `g`, write. -/
def digitStep (g : (Fin q → ℕ) → Fin q → ℕ) : P1 q A := .seq readT (writeT g)

theorem closed_readT : (readT (q := q) (A := A)).Closed :=
  closed_forEachFin _ _ fun _ => closed_forEachProg _ _ fun _ _ => trivial

theorem closed_writeT (g : (Fin q → ℕ) → Fin q → ℕ) : (writeT (A := A) g).Closed :=
  closed_forEachFin _ _ fun _ => closed_forEachProg _ _ fun _ _ => trivial

theorem closed_digitStep (g : (Fin q → ℕ) → Fin q → ℕ) : (digitStep (A := A) g).Closed :=
  ⟨closed_readT, closed_writeT g⟩

end Progs

/-! ## State helpers -/

section Helpers

variable {q : ℕ}

@[simp] theorem upd_strm (nm : Fin 3 → List Sym) (st ou : Fin q → List Sym) (ex : Fin 4 → List Sym)
    (c : Fin q) (x : List Sym) :
    Function.update (mk1 nm st ou ex) (STRM c) x = mk1 nm (Function.update st c x) ou ex := by
  show Function.update (Sum.elim nm (Sum.elim st (Sum.elim ou ex))) (Sum.inr (Sum.inl c)) x = _
  rw [Sum.update_elim_inr, Sum.update_elim_inl]

@[simp] theorem upd_out (nm : Fin 3 → List Sym) (st ou : Fin q → List Sym) (ex : Fin 4 → List Sym)
    (c : Fin q) (x : List Sym) :
    Function.update (mk1 nm st ou ex) (OUT c) x = mk1 nm st (Function.update ou c x) ex := by
  show Function.update (Sum.elim nm (Sum.elim st (Sum.elim ou ex))) (Sum.inr (Sum.inr (Sum.inl c)))
    x = _
  rw [Sum.update_elim_inr, Sum.update_elim_inr, Sum.update_elim_inl]

@[simp] theorem upd_nm (nm : Fin 3 → List Sym) (st ou : Fin q → List Sym) (ex : Fin 4 → List Sym)
    (i : Fin 3) (x : List Sym) :
    Function.update (mk1 nm st ou ex) (.inl i) x = mk1 (Function.update nm i x) st ou ex := by
  show Function.update (Sum.elim nm (Sum.elim st (Sum.elim ou ex))) (Sum.inl i) x = _
  rw [Sum.update_elim_inl]

@[simp] theorem upd_ex (nm : Fin 3 → List Sym) (st ou : Fin q → List Sym) (ex : Fin 4 → List Sym)
    (j : Fin 4) (x : List Sym) :
    Function.update (mk1 nm st ou ex) (.inr (.inr (.inr j))) x =
      mk1 nm st ou (Function.update ex j x) := by
  show Function.update (Sum.elim nm (Sum.elim st (Sum.elim ou ex))) (Sum.inr (Sum.inr (Sum.inr j)))
    x = _
  rw [Sum.update_elim_inr, Sum.update_elim_inr, Sum.update_elim_inr]

/-- Updating the `i`-th member of a "first `i` done" family. -/
theorem fam_upd {α : Type} (i : ℕ) (hi : i < q) (F G : Fin q → α) :
    Function.update (fun c : Fin q => if c.val < i then F c else G c) ⟨i, hi⟩ (F ⟨i, hi⟩) =
      fun c => if c.val < i + 1 then F c else G c := by
  funext c
  by_cases h : c = ⟨i, hi⟩
  · subst h
    simp
  · have hc : c.val ≠ i := fun e => h (Fin.ext e)
    rw [Function.update_of_ne h]
    by_cases h1 : c.val < i
    · simp [h1, show c.val < i + 1 by omega]
    · simp [h1, show ¬ c.val < i + 1 by omega]

theorem fam_zero {α : Type} (F G : Fin q → α) : (fun c : Fin q => if c.val < 0 then F c else G c) = G := by
  funext c
  simp

theorem fam_all {α : Type} (F G : Fin q → α) : (fun c : Fin q => if c.val < q then F c else G c) = F := by
  funext c
  simp [c.isLt]

theorem decodeBuf_testBit {w : ℕ} (d : ℕ) (h : d < 2 ^ w) :
    decodeBuf (fun j : Fin w => d.testBit j) = d := by
  have e : (List.finRange w).map (fun j : Fin w => d.testBit j) = bitsLE w d := by
    rw [bitsLE, ← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  rw [decodeBuf, e, bitsVal_bitsLE_of_lt h]

theorem finRange_rev_map_testBit (w d : ℕ) :
    (List.finRange w).reverse.map (fun j : Fin w => Sym.bit (d.testBit j)) =
      ((bitsLE w d).map Sym.bit).reverse := by
  rw [List.map_reverse, bitsLE, ← List.map_coe_finRange_eq_range, List.map_map, List.map_map]
  rfl

theorem finRange_map_testBit (w d : ℕ) :
    (List.finRange w).map (fun j : Fin w => Sym.bit (d.testBit j)) = (bitsLE w d).map Sym.bit := by
  rw [bitsLE, ← List.map_coe_finRange_eq_range, List.map_map, List.map_map]
  rfl

end Helpers

/-! ## Reading a digit tuple -/

section Read

variable {q : ℕ} {A : ℕ}

theorem runsM_popBit (c : Fin q) (j : Fin (digitWidth A)) (x : Bool) (L : List Sym)
    (b : M1 q A) (S : L1 q → List Sym) (hS : S (STRM c) = Sym.bit x :: L) :
    RunsM (popBit c j) b S (Function.update b c (Function.update (b c) j x))
      (Function.update S (STRM c) L) 1 := by
  intro o
  refine ⟨some (Sym.bit x), 1, le_rfl, ?_⟩
  have e := Eval.pop [] (STRM c)
    (fun (r : Option Sym × M1 q A) o => (o, Function.update r.2 c (Function.update (r.2 c) j
      (optBit o)))) (o, b) S
  rw [hS] at e
  exact e

theorem runsM_popBits (c : Fin q) (bv : Fin (digitWidth A) → Bool) :
    ∀ (js : List (Fin (digitWidth A))) (b : M1 q A) (S : L1 q → List Sym) (W : List Sym),
      S (STRM c) = js.map (fun j => Sym.bit (bv j)) ++ W →
      RunsM (forEachProg js (popBit c)) b S
        (Function.update b c (fun j => if j ∈ js then bv j else b c j))
        (Function.update S (STRM c) W) (js.length + 1)
  | [], b, S, W, hS => by
    have h1 : Function.update b c (fun j => if j ∈ ([] : List (Fin (digitWidth A))) then bv j
        else b c j) = b := by
      simp
    have h2 : Function.update S (STRM c) W = S := by
      simp only [List.map_nil, List.nil_append] at hS
      rw [← hS, Function.update_eq_self]
    rw [h1, h2]
    exact RunsM.skip b S
  | j0 :: js, b, S, W, hS => by
    rw [List.map_cons, List.cons_append] at hS
    have h1 := runsM_popBit c j0 (bv j0) _ b S hS
    have h2 := runsM_popBits c bv js (Function.update b c (Function.update (b c) j0 (bv j0)))
      (Function.update S (STRM c) (js.map (fun j => Sym.bit (bv j)) ++ W)) W
      (Function.update_self _ _ _)
    refine RunsM.of_eq (h1.seq h2) rfl rfl ?_ (by rw [Function.update_idem]) (by simp; omega)
    rw [Function.update_idem, Function.update_self]
    congr 1
    funext j
    by_cases hj : j ∈ js
    · simp [hj]
    · by_cases hj0 : j = j0
      · subst hj0
        simp [hj]
      · simp [hj, hj0]

theorem runsM_readT (dg : Fin q → ℕ) (W : Fin q → List Sym) (b : M1 q A)
    (nm : Fin 3 → List Sym) (ex : Fin 4 → List Sym) (st ou : Fin q → List Sym)
    (hst : ∀ c, st c = ((bitsLE (digitWidth A) (dg c)).map Sym.bit).reverse ++ W c) :
    RunsM (readT (q := q) (A := A)) b (mk1 nm st ou ex) (fun c j => (dg c).testBit j)
      (mk1 nm W ou ex) (q * (digitWidth A + 1) + 1) := by
  have key := runsM_forEachProg
    (fun c => forEachProg (List.finRange (digitWidth A)).reverse (popBit (A := A) c))
    (List.finRange q)
    (fun i => fun c => if c.val < i then (fun (j : Fin (digitWidth A)) => (dg c).testBit j) else b c)
    (fun i => mk1 nm (fun c => if c.val < i then W c else st c) ou ex)
    (fun _ => digitWidth A + 1) ?_
  · refine RunsM.of_eq key (fam_zero _ _) (by rw [fam_zero]) ?_ ?_ ?_
    · rw [List.length_finRange, fam_all]
    · rw [List.length_finRange, fam_all]
    · simp
  · intro i hi
    rw [List.length_finRange] at hi
    have hget : (List.finRange q)[i] = ⟨i, hi⟩ := by simp
    rw [hget]
    have h := runsM_popBits (A := A) ⟨i, hi⟩ (fun (j : Fin (digitWidth A)) => (dg ⟨i, hi⟩).testBit j)
      (List.finRange (digitWidth A)).reverse
      (fun c => if c.val < i then (fun (j : Fin (digitWidth A)) => (dg c).testBit j) else b c)
      (mk1 nm (fun c => if c.val < i then W c else st c) ou ex) (W ⟨i, hi⟩) ?_
    · refine RunsM.of_eq h rfl rfl ?_ ?_ (by simp)
      · have e : (fun j : Fin (digitWidth A) => if j ∈ (List.finRange (digitWidth A)).reverse then
            (dg ⟨i, hi⟩).testBit j else
            (fun c : Fin q => if c.val < i then (fun (j : Fin (digitWidth A)) => (dg c).testBit j)
              else b c) ⟨i, hi⟩ j) =
            (fun (j : Fin (digitWidth A)) => (dg ⟨i, hi⟩).testBit j) := by
          funext j
          simp
        rw [e]
        exact fam_upd i hi (fun c (j : Fin (digitWidth A)) => (dg c).testBit j) b
      · rw [upd_strm]
        congr 1
        exact fam_upd i hi W st
    · simp only [mk1, Sum.elim_inr, Sum.elim_inl, lt_irrefl, if_false]
      rw [hst, finRange_rev_map_testBit]

end Read

/-! ## Writing a digit tuple -/

section Write

variable {q : ℕ} {A : ℕ} (g : (Fin q → ℕ) → Fin q → ℕ)

theorem runsM_pushBits (c : Fin q) (b : M1 q A) :
    ∀ (js : List (Fin (digitWidth A))) (S : L1 q → List Sym),
      RunsM (forEachProg js (pushBit g c)) b S b
        (Function.update S (OUT c) ((js.reverse.map fun (j : Fin (digitWidth A)) =>
          Sym.bit ((g (fun c' => decodeBuf (b c')) c).testBit j)) ++ S (OUT c))) (js.length + 1)
  | [], S => by
    have e : Function.update S (OUT c) ((([] : List (Fin (digitWidth A))).reverse.map
        fun (j : Fin (digitWidth A)) => Sym.bit ((g (fun c' => decodeBuf (b c')) c).testBit j)) ++
          S (OUT c)) = S := by
      simp
    rw [e]
    exact RunsM.skip b S
  | j0 :: js, S => by
    have h1 : RunsM (pushBit g c j0) b S b (Function.update S (OUT c)
        (Sym.bit ((g (fun c' => decodeBuf (b c')) c).testBit j0) :: S (OUT c))) 1 :=
      fun o => ⟨o, 1, le_rfl, Eval.push _ _ _ _ _⟩
    have h2 := runsM_pushBits c b js (Function.update S (OUT c)
        (Sym.bit ((g (fun c' => decodeBuf (b c')) c).testBit j0) :: S (OUT c)))
    refine RunsM.of_eq (h1.seq h2) rfl rfl rfl ?_ (by simp; omega)
    rw [Function.update_idem, Function.update_self]
    simp

theorem runsM_writeT (dg : Fin q → ℕ) (hdg : ∀ c, dg c < 2 ^ digitWidth A)
    (nm : Fin 3 → List Sym) (ex : Fin 4 → List Sym) (st ou : Fin q → List Sym) :
    RunsM (writeT (A := A) g) (fun c j => (dg c).testBit j) (mk1 nm st ou ex)
      (fun c j => (dg c).testBit j)
      (mk1 nm st (fun c => (bitsLE (digitWidth A) (g dg c)).map Sym.bit ++ ou c) ex)
      (q * (digitWidth A + 1) + 1) := by
  have hdec : (fun c' => decodeBuf ((fun (c : Fin q) (j : Fin (digitWidth A)) =>
      (dg c).testBit j) c')) = dg := by
    funext c'
    exact decodeBuf_testBit (dg c') (hdg c')
  have key := runsM_forEachProg
    (fun c => forEachProg (List.finRange (digitWidth A)).reverse (pushBit (A := A) g c))
    (List.finRange q)
    (fun _ => fun c (j : Fin (digitWidth A)) => (dg c).testBit j)
    (fun i => mk1 nm st (fun c => if c.val < i then
      (bitsLE (digitWidth A) (g dg c)).map Sym.bit ++ ou c else ou c) ex)
    (fun _ => digitWidth A + 1) ?_
  · refine RunsM.of_eq key rfl (by rw [fam_zero]) rfl ?_ (by simp)
    rw [List.length_finRange, fam_all]
  · intro i hi
    rw [List.length_finRange] at hi
    have hget : (List.finRange q)[i] = ⟨i, hi⟩ := by simp
    rw [hget]
    have h := runsM_pushBits (A := A) g ⟨i, hi⟩ (fun c (j : Fin (digitWidth A)) => (dg c).testBit j)
      (List.finRange (digitWidth A)).reverse
      (mk1 nm st (fun c => if c.val < i then
        (bitsLE (digitWidth A) (g dg c)).map Sym.bit ++ ou c else ou c) ex)
    refine RunsM.of_eq h rfl rfl rfl ?_ (by simp)
    rw [upd_out]
    congr 1
    rw [hdec, List.reverse_reverse, finRange_map_testBit]
    simp only [mk1, Sum.elim_inr, Sum.elim_inl, lt_irrefl, if_false]
    exact fam_upd i hi (fun c => (bitsLE (digitWidth A) (g dg c)).map Sym.bit ++ ou c) ou

/-- **One digit tuple.** Streams `c` start with the reversed bits of digit `dg c`; the output
stacks receive the bits of `g dg c` (least significant on top). -/
theorem runs_digitStep (dg : Fin q → ℕ) (hdg : ∀ c, dg c < 2 ^ digitWidth A) (W : Fin q → List Sym)
    (nm : Fin 3 → List Sym) (ex : Fin 4 → List Sym) (st ou : Fin q → List Sym)
    (hst : ∀ c, st c = ((bitsLE (digitWidth A) (dg c)).map Sym.bit).reverse ++ W c) :
    Runs (digitStep (A := A) g) (mk1 nm st ou ex)
      (mk1 nm W (fun c => (bitsLE (digitWidth A) (g dg c)).map Sym.bit ++ ou c) ex) (fun _ => True)
      (2 * (q * (digitWidth A + 1) + 1)) := by
  refine runs_of_forall_runsM fun b => ⟨fun c (j : Fin (digitWidth A)) => (dg c).testBit j, ?_⟩
  have h1 := runsM_readT dg W b nm ex st ou hst
  have h2 := runsM_writeT (A := A) g dg hdg nm ex W ou
  exact (h1.seq h2).mono (by omega)

end Write

end SubNLogN.Machine.K1.SMM
