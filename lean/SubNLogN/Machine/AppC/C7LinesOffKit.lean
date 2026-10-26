/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C7LinesOffMath
import SubNLogN.Machine.Calculus.FramePassR
import SubNLogN.Machine.K1.RotateParSpec

/-!
# Lemma A.9 offset routine: stack layout and primitive rules (`Machine/AppC/C7LinesOffKit.lean`)

The offset kernel runs on `Stk = KLoc (Fin 6) (Fin 12)` with the registers `NatArith.Reg`.
Ten stacks are *fields* (`Fld`): nine scratch stacks and the destination `.inl 3`; a kernel state
is `stk S c`, the ambient stacks `S` overwritten by the field contents `c : Sc`. The scratch
stacks `.inr 9`, `.inr 10`, `.inr 11` are temporaries of the library programs (always restored). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

This file states the primitive `Runs` rules on `stk S c` (exact final states, explicit costs),
the two branching rules (`r_ite_peek`, `r_ite_cmp`), and the small programs `readBit`, `emit`,
`strip` with their rules. Everything here is fully proved.
-/

namespace SubNLogN.Machine.AppC.C7LinesOffAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine.NatArith
  SubNLogN.Machine.Calculus

/-- Stacks of the offset kernel: six named stacks and twelve scratch stacks. -/
abbrev Stk : Type := KLoc (Fin 6) (Fin 12)

/-- Programs of the offset kernel. -/
abbrev OProg : Type := Prog Stk (fun _ => Sym) Reg

/-- The field stacks. -/
inductive Fld
  | X | O | D | KM | E2 | W | Cn | Out | F | Dst
  deriving DecidableEq

/-- Location of a field. -/
def loc : Fld → Stk
  | .X => .inr 0
  | .O => .inr 1
  | .D => .inr 2
  | .KM => .inr 3
  | .E2 => .inr 4
  | .W => .inr 5
  | .Cn => .inr 6
  | .Out => .inr 7
  | .F => .inr 8
  | .Dst => .inl 3

/-- Temporaries. -/
abbrev sT1 : Stk := .inr 9
abbrev sT2 : Stk := .inr 10
abbrev sT3 : Stk := .inr 11

/-- The field at a stack, if any. -/
def fldOf (k : Stk) : Option Fld :=
  if k = .inr 0 then some .X else if k = .inr 1 then some .O else if k = .inr 2 then some .D
  else if k = .inr 3 then some .KM else if k = .inr 4 then some .E2
  else if k = .inr 5 then some .W else if k = .inr 6 then some .Cn
  else if k = .inr 7 then some .Out else if k = .inr 8 then some .F
  else if k = .inl 3 then some .Dst else none

theorem fldOf_loc (f : Fld) : fldOf (loc f) = some f := by
  cases f <;> rfl

theorem loc_of_fldOf {k : Stk} {f : Fld} (h : fldOf k = some f) : loc f = k := by
  unfold fldOf at h
  split_ifs at h <;> (try cases h) <;> subst_vars <;> rfl

theorem loc_injective : Function.Injective loc := by
  intro f g h
  have h1 := fldOf_loc f
  rw [h, fldOf_loc] at h1
  exact (Option.some.inj h1).symm

theorem loc_ne_T1 (f : Fld) : loc f ≠ sT1 := by cases f <;> decide
theorem loc_ne_T2 (f : Fld) : loc f ≠ sT2 := by cases f <;> decide

/-- Contents of the field stacks. -/
structure Sc where
  X : List Sym
  O : List Sym
  D : List Sym
  KM : List Sym
  E2 : List Sym
  W : List Sym
  Cn : List Sym
  Out : List Sym
  F : List Sym
  Dst : List Sym

/-- Read a field. -/
def Sc.get (c : Sc) : Fld → List Sym
  | .X => c.X
  | .O => c.O
  | .D => c.D
  | .KM => c.KM
  | .E2 => c.E2
  | .W => c.W
  | .Cn => c.Cn
  | .Out => c.Out
  | .F => c.F
  | .Dst => c.Dst

/-- Write a field. -/
def Sc.set (c : Sc) : Fld → List Sym → Sc
  | .X, v => { c with X := v }
  | .O, v => { c with O := v }
  | .D, v => { c with D := v }
  | .KM, v => { c with KM := v }
  | .E2, v => { c with E2 := v }
  | .W, v => { c with W := v }
  | .Cn, v => { c with Cn := v }
  | .Out, v => { c with Out := v }
  | .F, v => { c with F := v }
  | .Dst, v => { c with Dst := v }

theorem Sc.get_set_self (c : Sc) (f : Fld) (v : List Sym) : (c.set f v).get f = v := by
  cases f <;> rfl

theorem Sc.set_get (c : Sc) (f : Fld) : c.set f (c.get f) = c := by
  cases f <;> rfl

theorem Sc.set_set (c : Sc) (f : Fld) (v w : List Sym) : (c.set f v).set f w = c.set f w := by
  cases f <;> rfl

theorem Sc.get_set_ne (c : Sc) {f g : Fld} (h : g ≠ f) (v : List Sym) :
    (c.set f v).get g = c.get g := by
  cases f <;> cases g <;> first | rfl | exact absurd rfl h

/-- The kernel state: field contents `c`, ambient stacks `S` elsewhere. -/
def stk (S : Stk → List Sym) (c : Sc) (k : Stk) : List Sym :=
  match fldOf k with
  | some f => c.get f
  | none => S k

theorem stk_loc (S : Stk → List Sym) (c : Sc) (f : Fld) : stk S c (loc f) = c.get f := by
  simp only [stk, fldOf_loc]

theorem stk_none (S : Stk → List Sym) (c : Sc) {k : Stk} (h : fldOf k = none) :
    stk S c k = S k := by
  simp only [stk, h]

theorem upd_stk (S : Stk → List Sym) (c : Sc) (f : Fld) (v : List Sym) :
    Function.update (stk S c) (loc f) v = stk S (c.set f v) := by
  funext k
  rcases h : fldOf k with _ | g
  · have hk : k ≠ loc f := by
      rintro rfl
      rw [fldOf_loc] at h
      cases h
    rw [Function.update_of_ne hk, stk_none S c h, stk_none S _ h]
  · have hk := loc_of_fldOf h
    subst hk
    by_cases hg : g = f
    · subst hg
      rw [Function.update_self, stk_loc, Sc.get_set_self]
    · rw [Function.update_of_ne (loc_injective.ne hg), stk_loc, stk_loc, Sc.get_set_ne c hg]

/-- The field contents of a state. -/
def ofS (S : Stk → List Sym) : Sc :=
  ⟨S (loc .X), S (loc .O), S (loc .D), S (loc .KM), S (loc .E2), S (loc .W), S (loc .Cn),
    S (loc .Out), S (loc .F), S (loc .Dst)⟩

theorem ofS_get (S : Stk → List Sym) (f : Fld) : (ofS S).get f = S (loc f) := by
  cases f <;> rfl

theorem stk_ofS (S : Stk → List Sym) : stk S (ofS S) = S := by
  funext k
  rcases h : fldOf k with _ | g
  · exact stk_none S _ h
  · rw [← loc_of_fldOf h, stk_loc, ofS_get]

theorem stk_ofS_dst (S : Stk → List Sym) (v : List Sym) :
    stk S ((ofS S).set .Dst v) = Function.update S (.inl 3) v := by
  rw [← upd_stk, stk_ofS]
  rfl

/-! ## Primitive rules on `stk S c` -/

section Rules

variable (S : Stk → List Sym)

theorem r_load (c : Sc) : RunsIn [] (.load id : OProg) (stk S c) (stk S c) (fun _ => True) 1 :=
  runs_loadId _

theorem r_pushMark (c : Sc) (f : Fld) :
    RunsIn [] (pushMark (loc f)) (stk S c) (stk S (c.set f (Sym.mark :: c.get f))) (fun _ => True)
      1 := by
  have h := runs_pushMark (loc f) (stk S c)
  rwa [stk_loc, upd_stk] at h

theorem r_pushW (c : Sc) (f : Fld) (x : Sym) :
    RunsIn [] (pushW (loc f) x) (stk S c) (stk S (c.set f (x :: c.get f))) (fun _ => True) 1 := by
  have h := runs_pushW (loc f) x (stk S c)
  rwa [stk_loc, upd_stk] at h

theorem r_popW (c : Sc) (f : Fld) :
    RunsIn [] (popW (loc f)) (stk S c) (stk S (c.set f (c.get f).tail)) (fun _ => True) 1 := by
  have h := runs_popW (loc f) (stk S c)
  rwa [stk_loc, upd_stk] at h

theorem r_peekW (c : Sc) (k : Stk) :
    RunsIn [] (peekW k) (stk S c) (stk S c) (fun v => v.1 = (stk S c k).head?) 1 :=
  triple_peekW k (stk S c)

theorem r_copyN {src : Stk} {f : Fld} (h1 : src ≠ loc f) (h2 : src ≠ sT1) (c : Sc) (a : ℕ)
    (rx : List Sym) (hrx : TermOK rx) (hS : stk S c src = natSyms a ++ rx) :
    RunsIn [] (copyN src (loc f) sT1) (stk S c) (stk S (c.set f (natSyms a ++ c.get f)))
      (fun _ => True) (7 * bitLen a + 7) := by
  have h := runs_copyN h1 h2 (loc_ne_T1 f) a rx (stk S c) hrx hS
  rwa [stk_loc, upd_stk] at h

theorem r_dec (c : Sc) (f : Fld) (n : ℕ) (ct : List Sym) (hct : TermOK ct)
    (hS : c.get f = natSyms (n + 1) ++ ct) :
    RunsIn [] ((dec (loc f) sT1).liftRegs lW) (stk S c) (stk S (c.set f (natSyms n ++ ct)))
      (fun _ => True) (6 * zerosLead (encodeNat (n + 1)) + 8) := by
  have h := WP.W0m.runs_liftRegs lW (FramePassRAux.runs_dec (loc_ne_T1 f) n ct (stk S c) hct
    (by rw [stk_loc]; exact hS))
  rw [upd_stk] at h
  exact h

theorem r_dblN (c : Sc) (f : Fld) (n : ℕ) (rest : List Sym) (hrest : TermOK rest)
    (hS : c.get f = natSyms n ++ rest) :
    RunsIn [] (dblN (loc f)) (stk S c) (stk S (c.set f (natSyms (n + n) ++ rest))) (fun _ => True)
      3 := by
  have h := runs_dblN (loc f) n rest (stk S c) hrest (by rw [stk_loc]; exact hS)
  rwa [upd_stk] at h

theorem r_addN {x y : Stk} {f : Fld} (hnd : [x, y, loc f, sT1, sT2, sT3].Nodup) (c : Sc)
    (a b : ℕ) (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : stk S c x = natSyms a ++ rx) (hy : stk S c y = natSyms b ++ ry) :
    RunsIn [] (addN x y (loc f) sT1 sT2 sT3) (stk S c)
      (stk S (c.set f (natSyms (a + b) ++ c.get f))) (fun _ => True)
      (20 * (bitLen a + bitLen b + 1)) := by
  have h := runs_addN hnd a b rx ry (stk S c) hrx hry hx hy
  rwa [stk_loc, upd_stk] at h

theorem r_dropF (c : Sc) (f : Fld) (a : ℕ) (t : Sym) (rest : List Sym) (ht : t.isBit = false)
    (hS : c.get f = natSyms a ++ t :: rest) :
    RunsIn [] (dropF (loc f)) (stk S c) (stk S (c.set f rest)) (fun _ => True)
      (2 * bitLen a + 2) := by
  have h := runs_dropF (loc f) a t rest (stk S c) ht (by rw [stk_loc]; exact hS)
  rwa [upd_stk] at h

theorem r_moveBits {f g : Fld} (hfg : f ≠ g) (c : Sc) (es : List Bool) (rest : List Sym)
    (hrest : TermOK rest) (hS : c.get f = es.map Sym.bit ++ rest) :
    RunsIn [] ((moveBits (loc f) (loc g)).liftRegs lW) (stk S c)
      (stk S ((c.set f rest.tail).set g (es.reverse.map Sym.bit ++ c.get g))) (fun _ => True)
      (3 * es.length + 2) := by
  have h : Runs ((moveBits (loc f) (loc g)).liftRegs lW) (stk S c)
      (Function.update (Function.update (stk S c) (loc f) rest.tail) (loc g)
        (es.reverse.map Sym.bit ++ stk S c (loc g))) (fun _ => True) (3 * es.length + 2) :=
    SubNLogN.Machine.K1.runs_liftRegs_of_eval lW fun v =>
      ⟨_, _, moveBits_eval (loc_injective.ne hfg) [] v es rest (stk S c) hrest
        (by rw [stk_loc]; exact hS), le_rfl⟩
  rwa [stk_loc, upd_stk, upd_stk] at h

/-- `cmpN` (generic stacks): the compare register holds `ordOf a b`. -/
theorem runs_cmpN_gen {K : Type} [DecidableEq K] {x y t1 t2 : K} (h : [x, y, t1, t2].Nodup)
    (a b : ℕ) (rx ry : List Sym) (S0 : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : S0 x = natSyms a ++ rx) (hy : S0 y = natSyms b ++ ry) :
    Runs (cmpN x y t1 t2) S0 S0 (fun r => r.2.2.2.2 = ordOf a b) (12 * bitLen a + 15) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h'
  obtain ⟨⟨hxy, hx1, hx2⟩, ⟨hy1, hy2⟩, h12⟩ := h'
  have hord : cmpAll .eq (encodeNat a) (encodeNat b) = ordOf a b := by
    rw [cmpAll_eq_ordOf _ _ (normBits_encodeNat a) (normBits_encodeNat b), bitsVal_encodeNat,
      bitsVal_encodeNat]
  refine Runs.of_eval fun v => ?_
  have e := cmpNum_eval hxy hx1 hx2 hy1 hy2 h12 (NatArith.lC.get v) (encodeNat a) (encodeNat b)
    rx ry S0 hrx hry hx hy
  refine ⟨_, _, Eval.liftRegs NatArith.lC e v rfl, hord, ?_⟩
  simp only [bitLen]
  omega

theorem closed_cmpN_gen {K : Type} (x y t1 t2 : K) : (cmpN x y t1 t2).Closed :=
  WP.W9comp.closed_liftRegs _ (by
    simp [Prog.Closed, Prog.FreeBelow, cmpNum, cmpBody, pushC, pushR, popR, restoreR, moveBits,
      moveBitsBody, Prog.liftRegs, Lib.skip])

theorem r_cmpN {f g : Fld} (hnd : [loc f, loc g, sT1, sT2].Nodup) (c : Sc) (a b : ℕ)
    (rx ry : List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hx : c.get f = natSyms a ++ rx)
    (hy : c.get g = natSyms b ++ ry) :
    RunsIn [] (cmpN (loc f) (loc g) sT1 sT2) (stk S c) (stk S c) (fun r => r.2.2.2.2 = ordOf a b)
      (12 * bitLen a + 15) :=
  runs_cmpN_gen hnd a b rx ry (stk S c) hrx hry (by rw [stk_loc]; exact hx)
    (by rw [stk_loc]; exact hy)

end Rules

/-! ## Branching -/

section Branch

variable (S : Stk → List Sym)

/-- Branch on the top symbol of `k` (peeked into the work register). -/
theorem r_ite_peek {k : Stk} {c : Sc} (φ : Option Sym → Bool) {Pt Pf : OProg}
    {S' : Stk → List Sym} {T : ℕ}
    (ht : φ (stk S c k).head? = true → RunsIn [] Pt (stk S c) S' (fun _ => True) T)
    (hf : φ (stk S c k).head? = false → RunsIn [] Pf (stk S c) S' (fun _ => True) T) :
    RunsIn [] (.seq (peekW k) (.ite (fun r => φ r.1) Pt Pf)) (stk S c) S' (fun _ => True)
      (T + 2) := by
  have hp := r_peekW S c k
  cases hφ : φ (stk S c k).head?
  · have h1 : RunsIn [] (peekW k) (stk S c) (stk S c) (fun v => φ v.1 = false) 1 :=
      RunsIn.mono hp (fun v (hv : v.1 = (stk S c k).head?) =>
        show φ v.1 = false by rw [hv]; exact hφ) le_rfl
    exact RunsIn.mono (RunsIn.ite_false (c := fun r => φ r.1) h1 (hf hφ)) (fun _ h => h)
      (by omega)
  · have h1 : RunsIn [] (peekW k) (stk S c) (stk S c) (fun v => φ v.1 = true) 1 :=
      RunsIn.mono hp (fun v (hv : v.1 = (stk S c k).head?) =>
        show φ v.1 = true by rw [hv]; exact hφ) le_rfl
    exact RunsIn.mono (RunsIn.ite_true (c := fun r => φ r.1) h1 (ht hφ)) (fun _ h => h)
      (by omega)

/-- Branch on a comparison of the numbers on two fields. -/
theorem r_ite_cmp {f g : Fld} (hnd : [loc f, loc g, sT1, sT2].Nodup) {c : Sc} {a b : ℕ}
    {rx ry : List Sym} (hrx : TermOK rx) (hry : TermOK ry) (hx : c.get f = natSyms a ++ rx)
    (hy : c.get g = natSyms b ++ ry) (ψ : Ordering → Bool) {Pt Pf : OProg}
    {S' : Stk → List Sym} {T : ℕ}
    (ht : ψ (ordOf a b) = true → RunsIn [] Pt (stk S c) S' (fun _ => True) T)
    (hf : ψ (ordOf a b) = false → RunsIn [] Pf (stk S c) S' (fun _ => True) T) :
    RunsIn [] (.seq (cmpN (loc f) (loc g) sT1 sT2) (.ite (fun r => ψ r.2.2.2.2) Pt Pf))
      (stk S c) S' (fun _ => True) (12 * bitLen a + T + 16) := by
  have hp := r_cmpN S hnd c a b rx ry hrx hry hx hy
  cases hψ : ψ (ordOf a b)
  · have h1 : RunsIn [] (cmpN (loc f) (loc g) sT1 sT2) (stk S c) (stk S c)
        (fun v => ψ v.2.2.2.2 = false) (12 * bitLen a + 15) :=
      RunsIn.mono hp (fun v (hv : v.2.2.2.2 = ordOf a b) =>
        show ψ v.2.2.2.2 = false by rw [hv]; exact hψ) le_rfl
    exact RunsIn.mono (RunsIn.ite_false (c := fun r => ψ r.2.2.2.2) h1 (hf hψ))
      (fun _ h => h) (by omega)
  · have h1 : RunsIn [] (cmpN (loc f) (loc g) sT1 sT2) (stk S c) (stk S c)
        (fun v => ψ v.2.2.2.2 = true) (12 * bitLen a + 15) :=
      RunsIn.mono hp (fun v (hv : v.2.2.2.2 = ordOf a b) =>
        show ψ v.2.2.2.2 = true by rw [hv]; exact hψ) le_rfl
    exact RunsIn.mono (RunsIn.ite_true (c := fun r => ψ r.2.2.2.2) h1 (ht hψ))
      (fun _ h => h) (by omega)

end Branch

/-! ## Small programs: bit read, output emission, stripping high zeros -/

section Small

variable (S : Stk → List Sym)

theorem natSyms_one : natSyms 1 = [Sym.bit true] := by
  have h := encodeNat_add_add_one 0
  simp only [Nat.add_zero, Nat.zero_add, encodeNat_zero] at h
  simp [natSyms, h]

/-- The top of `natSyms m ++ rest` is `bit true` iff `m` is odd. -/
theorem head_eq_bit_true (m : ℕ) (rest : List Sym) (hrest : TermOK rest) :
    (natSyms m ++ rest).head? = some (Sym.bit true) ↔ m % 2 = 1 := by
  by_cases hm : m = 0
  · subst hm
    rw [natSyms_zero, List.nil_append]
    constructor
    · intro h
      have h' := hrest _ h
      simp [Sym.isBit] at h'
    · intro h
      simp at h
  · rw [natSyms_div2 hm, List.cons_append, List.head?_cons]
    constructor
    · intro h
      simp only [Option.some.injEq, Sym.bit.injEq, decide_eq_true_eq] at h
      exact h
    · intro h
      simp [h]

/-- Read the low bit of the number on `k`: pop it if there is one. -/
def readBit (k : Stk) : OProg :=
  .seq (peekW k) (.ite (fun r => optIsBit r.1) (popW k) (.load id))

theorem closed_readBit (k : Stk) : (readBit k).Closed :=
  ⟨closed_peekW k, closed_popW k, trivial⟩

theorem r_readBit (c : Sc) (f : Fld) (m : ℕ) (rest : List Sym) (hrest : TermOK rest)
    (hS : c.get f = natSyms m ++ rest) :
    RunsIn [] (readBit (loc f)) (stk S c) (stk S (c.set f (natSyms (m / 2) ++ rest)))
      (fun _ => True) 3 := by
  have hb : optIsBit (stk S c (loc f)).head? = decide (m ≠ 0) := by
    rw [stk_loc, hS, optIsBit_head_natSyms m rest hrest]
  refine r_ite_peek S optIsBit (T := 1) (fun h => ?_) (fun h => ?_)
  · have hm : m ≠ 0 := by rw [hb] at h; simpa using h
    have h2 := r_popW S c f
    rwa [hS, natSyms_div2 hm, List.cons_append, List.tail_cons] at h2
  · have hm : m = 0 := by rw [hb] at h; simpa using h
    subst hm
    have e : c.set f (natSyms (0 / 2) ++ rest) = c := by
      rw [Nat.zero_div, ← hS]
      exact Sc.set_get c f
    rw [e]
    exact r_load S c

/-- Emit the output bit of a position whose indicator bit is `s`; with `neg` the two's
complement on the fly: after the first set indicator bit (flag on `F`) every bit is inverted. -/
def emit (neg s : Bool) : OProg :=
  if neg then
    .seq (peekW (loc .F)) (.ite (fun r => optIsBit r.1) (pushW (loc .Out) (.bit (!s)))
      (if s then .seq (pushW (loc .Out) (.bit true)) (pushW (loc .F) (.bit true))
        else pushW (loc .Out) (.bit false)))
  else pushW (loc .Out) (.bit s)

theorem closed_emit (neg s : Bool) : (emit neg s).Closed := by
  cases neg <;> cases s
  · exact closed_pushW _ _
  · exact closed_pushW _ _
  · exact ⟨closed_peekW _, closed_pushW _ _, closed_pushW _ _⟩
  · exact ⟨closed_peekW _, closed_pushW _ _, closed_pushW _ _, closed_pushW _ _⟩

theorem r_emit (neg s seen : Bool) (c : Sc) (jF : List Sym)
    (hF : c.F = natSyms (neg && seen).toNat ++ Sym.mark :: jF) :
    RunsIn [] (emit neg s) (stk S c)
      (stk S ((c.set .Out (Sym.bit (if neg && seen then !s else s) :: c.Out)).set .F
        (natSyms (neg && (seen || s)).toNat ++ Sym.mark :: jF))) (fun _ => True) 4 := by
  cases neg
  · have h := r_pushW S c .Out (Sym.bit s)
    have e : natSyms (false && (seen || s)).toNat ++ Sym.mark :: jF = c.F := by simp [hF]
    rw [e]
    exact RunsIn.congr h (congrArg (stk S) (Sc.set_get _ .F).symm) (by norm_num)
  · have hhead : optIsBit (stk S c (loc .F)).head? = seen := by
      rw [stk_loc]
      show optIsBit c.F.head? = seen
      rw [hF, optIsBit_head_natSyms _ _ (termOK_mark jF)]
      cases seen <;> rfl
    refine r_ite_peek S optIsBit (T := 2) (fun h => ?_) (fun h => ?_)
    · rw [hhead] at h
      subst h
      have h1 := r_pushW S c .Out (Sym.bit (!s))
      have e : natSyms (true && (true || s)).toNat ++ Sym.mark :: jF = c.F := by simp [hF]
      rw [e]
      exact RunsIn.congr (RunsIn.mono h1 (fun _ h => h) (by norm_num : 1 ≤ 2))
        (congrArg (stk S) (Sc.set_get _ .F).symm) le_rfl
    · rw [hhead] at h
      subst h
      cases s
      · have h1 := r_pushW S c .Out (Sym.bit false)
        have e : natSyms (true && (false || false)).toNat ++ Sym.mark :: jF = c.F := by
          simp [hF]
        rw [e]
        exact RunsIn.congr (RunsIn.mono h1 (fun _ h => h) (by norm_num : 1 ≤ 2))
          (congrArg (stk S) (Sc.set_get _ .F).symm) le_rfl
      · have h1 := RunsIn.seq (r_pushW S c .Out (Sym.bit true)) (r_pushW S _ .F (Sym.bit true))
        refine RunsIn.congr h1 (congrArg (stk S) ?_) le_rfl
        have e : Sym.bit true :: c.F = natSyms (true && (false || true)).toNat ++ Sym.mark :: jF := by
          simp [hF, natSyms_one, natSyms_zero]
        rw [← e] <;> rfl

/-- Strip the high zero bits on top of `Out`. -/
def strip : OProg :=
  .seq (peekW (loc .Out)) (.loop (fun r => decide (r.1 = some (Sym.bit false)))
    (.seq (popW (loc .Out)) (peekW (loc .Out))))

theorem closed_strip : strip.Closed :=
  ⟨closed_peekW _, closed_popW _, closed_peekW _⟩

theorem strip_loop (j : List Sym) : ∀ (ds : List Bool) (c : Sc),
    c.Out = ds.map Sym.bit ++ Sym.mark :: j →
    Triple [] (fun s => s.stk = stk S c ∧ s.var.1 = c.Out.head?)
      (.loop (fun r : Reg => decide (r.1 = some (Sym.bit false)))
        (.seq (popW (loc .Out)) (peekW (loc .Out))))
      (fun s => s.stk = stk S (c.set .Out ((ds.dropWhile (fun b => !b)).map Sym.bit ++
        Sym.mark :: j)) ∧ True)
      (3 * ds.length + 1)
  | [], c, hO => by
    rw [List.map_nil, List.nil_append] at hO
    rintro s ⟨hs, hv⟩
    refine ⟨s, 1, Eval.loop_false ?_, ⟨?_, trivial⟩, by simp⟩
    · show decide (s.var.1 = some (Sym.bit false)) = false
      rw [hv, hO]
      simp
    · rw [hs, List.dropWhile_nil, List.map_nil, List.nil_append, ← hO]
      exact congrArg (stk S) (Sc.set_get c .Out).symm
  | b :: ds, c, hO => by
    rintro s ⟨hs, hv⟩
    cases b
    · have hb := RunsIn.seq (r_popW S c .Out) (r_peekW S _ (loc .Out))
      obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ := hb s hs
      have hO' : (c.set .Out (c.get .Out).tail).Out = ds.map Sym.bit ++ Sym.mark :: j := by
        show c.Out.tail = _
        simp only [hO, List.map_cons, List.cons_append, List.tail_cons]
      obtain ⟨s2, t2, e2, ⟨hq2, -⟩, ht2⟩ := strip_loop j ds (c.set .Out (c.get .Out).tail) hO' s1
        ⟨hs1, by rw [hv1, stk_loc] <;> rfl⟩
      refine ⟨s2, t1 + t2 + 1, Eval.loop_true ?_ e1 e2, ⟨?_, trivial⟩, ?_⟩
      · show decide (s.var.1 = some (Sym.bit false)) = true
        rw [hv, hO]
        simp
      · rw [hq2, Sc.set_set] <;> rfl
      · simp only [List.length_cons]
        omega
    · refine ⟨s, 1, Eval.loop_false ?_, ⟨?_, trivial⟩, by omega⟩
      · show decide (s.var.1 = some (Sym.bit false)) = false
        rw [hv, hO]
        simp
      · rw [hs, show (true :: ds).dropWhile (fun b => !b) = true :: ds from rfl, ← hO]
        exact congrArg (stk S) (Sc.set_get c .Out).symm

theorem r_strip (c : Sc) (ds : List Bool) (j : List Sym)
    (hO : c.Out = ds.map Sym.bit ++ Sym.mark :: j) :
    RunsIn [] strip (stk S c)
      (stk S (c.set .Out ((ds.dropWhile (fun b => !b)).map Sym.bit ++ Sym.mark :: j)))
      (fun _ => True) (3 * ds.length + 2) := by
  have h1 := r_peekW S c (loc .Out)
  have h2 := strip_loop S j ds c hO
  refine Triple.cost_mono (Triple.seq (Triple.post h1 fun s hs => ⟨hs.1, ?_⟩) h2) (by omega)
  rw [hs.2, stk_loc] <;> rfl

end Small

end SubNLogN.Machine.AppC.C7LinesOffAux
