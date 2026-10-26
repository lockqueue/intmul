/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5StreamStep
import SubNLogN.Machine.AppC.C5StreamDefs

/-!
# Proposition A.7 stream kernel, part 2: atomic steps (descriptor counters, transfer back)

An *atomic step* runs one stream sub-kernel on the array.
1. The binary counters it needs are computed from the descriptor `(k, N1, G, B)` with the
   `NatArith` library: `b = m^(k-1)` on `cb`, `s = base·(q^xs)^b` on `cs`, `n1 = base1·(q^x1)^b`
   on `cn1`, a copy of `b` on `cb1`, the constants `0` on `cb2` and `1` on `cn2`. Each counter sits
   above a `mark` on its scratch stack.
2. The sub-kernel moves the array from stack `0` to the scratch stack `T`.
3. `C5.xfer` moves it back. Then every counter is dropped.
`runs_atom` is the generic statement: given a `Runs` fact for the sub-kernel call (from the state
after the setup), the whole step rewrites the array in place and restores every other stack. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

Namespace `SubNLogN.Machine.C5.StreamAux`.
-/

namespace SubNLogN.Machine.C5.StreamAux

open TMFw TMFw.Contracts SubNLogN.Machine NatArith

/-- Private scratch stacks of an atomic step. -/
inductive Scr
  | T | X | cb | cs | cb1 | cn1 | cb2 | cn2 | ck | co | kc | kt | tq | td | ta | tb | tc
  deriving DecidableEq

instance : Fintype Scr where
  elems := ⟨↑[Scr.T, .X, .cb, .cs, .cb1, .cn1, .cb2, .cn2, .ck, .co, .kc, .kt, .tq, .td, .ta, .tb,
    .tc], Multiset.coe_nodup.2 (by decide)⟩
  complete := fun x => by cases x <;> decide

/-- Stacks of an atomic step whose sub-kernel has private scratch `E`. -/
abbrev AK (E : Type) : Type := KLoc (Fin 5) (Scr ⊕ E)

/-- The scratch stack `x`. -/
abbrev sc {E : Type} (x : Scr) : AK E := .inr (.inl x)

/-- Counter data of an atomic step: `s = base·(q^xs)^b` and `n1 = base1·(q^x1)^b`. -/
structure Ctr where
  bs : Base
  xs : ℕ
  b1 : Base
  x1 : ℕ

section Progs

variable {E : Type}

/-- Push the base factor on `z`. -/
def pushBase : Base → Scr → Prog (AK E) (fun _ => Sym) Reg
  | .one, z => pushNat (sc z) 1
  | .G, z => copyN (.inl 3) (sc z) (sc .ta)
  | .B, z => copyN (.inl 4) (sc z) (sc .ta)
  | .GB, z => mulN (.inl 3) (.inl 4) (sc z) (sc .ta) (sc .tb) (sc .tc) (sc .kt)

/-- `z := base·(q^x)^b` above a mark (`b` read from `cb`). -/
def progVal (q : ℕ) (bs : Base) (x : ℕ) (z : Scr) : Prog (AK E) (fun _ => Sym) Reg :=
  .seq (pushMark (sc z)) (.seq (pushBase bs z)
    (powMulN (sc z) (q ^ x) (sc .cb) (sc .kc) (sc .kt) (sc .tq) (sc .td) (sc .ta) (sc .tb) (sc .tc)))

/-- `cb := m^(k-1)` above a mark (`k` read from stack `1`); for `m = 1` the constant `1`. -/
def progB (m : ℕ) : Prog (AK E) (fun _ => Sym) Reg :=
  if m = 1 then .seq (pushMark (sc .cb)) (pushNat (sc .cb) 1)
  else .seq (pushMark (sc .co)) (.seq (pushNat (sc .co) 1) (.seq (pushMark (sc .ck))
    (.seq (subN (.inl 1) (sc .co) (sc .ck) (sc .ta) (sc .tb) (sc .tc))
    (.seq (pushMark (sc .cb)) (.seq (pushNat (sc .cb) 1)
    (.seq (powMulN (sc .cb) m (sc .ck) (sc .kc) (sc .kt) (sc .tq) (sc .td) (sc .ta) (sc .tb)
      (sc .tc)) (.seq (dropF (sc .ck)) (dropF (sc .co)))))))))

/-- Compute all counters, then put a mark on `T`. -/
def setup (q m : ℕ) (c : Ctr) : Prog (AK E) (fun _ => Sym) Reg :=
  .seq (progB m) (.seq (progVal q c.bs c.xs .cs) (.seq (progVal q c.b1 c.x1 .cn1)
  (.seq (pushMark (sc .cb1)) (.seq (copyN (sc .cb) (sc .cb1) (sc .ta))
  (.seq (pushMark (sc .cb2)) (.seq (pushMark (sc .cn2)) (.seq (pushNat (sc .cn2) 1)
  (pushMark (sc .T)))))))))

/-- Move the result back from `T` to the array stack, then drop the mark and the counters. -/
def post : Prog (AK E) (fun _ => Sym) Reg :=
  .seq ((C5.xfer (sc .T) (.inl 0) (sc .X)).liftRegs lW) (.seq (popW (sc .T))
  (.seq (dropF (sc .cn2)) (.seq (dropF (sc .cb2)) (.seq (dropF (sc .cb1))
  (.seq (dropF (sc .cn1)) (.seq (dropF (sc .cs)) (dropF (sc .cb))))))))

/-- An atomic step around the sub-kernel call `call`. -/
def atomProg (q m : ℕ) (c : Ctr) {R : Type} (call : Prog (AK E) (fun _ => Sym) (Reg × R)) :
    Prog (AK E) (fun _ => Sym) (Reg × R) :=
  .seq ((setup q m c).liftRegs (Lens.fst Reg R)) (.seq call ((post).liftRegs (Lens.fst Reg R)))

theorem closed_pushBase (bs : Base) (z : Scr) : (pushBase (E := E) bs z).Closed := by
  cases bs
  · exact closed_pushNat _ _
  · exact closed_copyN _ _ _
  · exact closed_copyN _ _ _
  · exact closed_mulN _ _ _ _ _ _ _

theorem closed_progVal (q : ℕ) (bs : Base) (x : ℕ) (z : Scr) :
    (progVal (E := E) q bs x z).Closed :=
  ⟨closed_pushMark _, closed_pushBase bs z, closed_powMulN _ _ _ _ _ _ _ _ _ _⟩

theorem closed_progB (m : ℕ) : (progB (E := E) m).Closed := by
  unfold progB
  split_ifs
  · exact ⟨closed_pushMark _, closed_pushNat _ _⟩
  · exact ⟨closed_pushMark _, closed_pushNat _ _, closed_pushMark _, closed_subN _ _ _ _ _ _,
      closed_pushMark _, closed_pushNat _ _, closed_powMulN _ _ _ _ _ _ _ _ _ _, closed_dropF _,
      closed_dropF _⟩

theorem closed_setup (q m : ℕ) (c : Ctr) : (setup (E := E) q m c).Closed :=
  ⟨closed_progB m, closed_progVal _ _ _ _, closed_progVal _ _ _ _, closed_pushMark _,
    closed_copyN _ _ _, closed_pushMark _, closed_pushMark _, closed_pushNat _ _, closed_pushMark _⟩

theorem closed_post : (post (E := E)).Closed :=
  ⟨WP.W9comp.closed_liftRegs lW (C5.closed_xfer _ _ _), closed_popW _, closed_dropF _,
    closed_dropF _, closed_dropF _, closed_dropF _, closed_dropF _, closed_dropF _⟩

theorem closed_atomProg (q m : ℕ) (c : Ctr) {R : Type} {call : Prog (AK E) (fun _ => Sym) (Reg × R)}
    (h : call.Closed) : (atomProg q m c call).Closed :=
  ⟨WP.W9comp.closed_liftRegs _ (closed_setup q m c), h,
    WP.W9comp.closed_liftRegs _ closed_post⟩

end Progs

/-! ## Primed specifications (the old content of the target stack is a parameter) -/

section Primed

variable {K : Type} [DecidableEq K]

theorem runs_liftRegs' {σ τ : Type} (l : Lens σ τ) {P : Prog K (fun _ => Sym) τ}
    {S S' : K → List Sym} {Q : τ → Prop} {T : ℕ} (h : Runs P S S' Q T) :
    Runs (P.liftRegs l) S S' (fun _ => True) T := by
  intro s hs
  obtain ⟨v, stk⟩ := s
  change stk = S at hs
  subst hs
  obtain ⟨s', t, e, ⟨hs', -⟩, ht⟩ := h ⟨l.get v, stk⟩ rfl
  exact ⟨_, t, Eval.liftRegs l e v rfl, ⟨hs', trivial⟩, ht⟩

theorem runs_pushMark' (k : K) (old : List Sym) (S : K → List Sym) (h : S k = old) :
    Runs (pushMark k) S (Function.update S k (Sym.mark :: old)) (fun _ => True) 1 := by
  subst h; exact runs_pushMark k S

theorem runs_pushNat' (k : K) (c : ℕ) (old : List Sym) (S : K → List Sym) (h : S k = old) :
    Runs (pushNat k c) S (Function.update S k (natSyms c ++ old)) (fun _ => True)
      (bitLen c + 1) := by
  subst h; exact runs_pushNat k c S

theorem runs_popW' (k : K) (x : Sym) (old : List Sym) (S : K → List Sym) (h : S k = x :: old) :
    Runs (popW k) S (Function.update S k old) (fun _ => True) 1 := by
  have r := runs_popW k S
  rw [h] at r
  exact r

theorem runs_copyN' {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (a : ℕ) (rx old : List Sym) (S : K → List Sym) (hrx : TermOK rx)
    (hS : S src = natSyms a ++ rx) (hd : S dst = old) :
    Runs (copyN src dst tmp) S (Function.update S dst (natSyms a ++ old)) (fun _ => True)
      (7 * bitLen a + 7) := by
  subst hd; exact runs_copyN hsd hst hdt a rx S hrx hS

theorem runs_mulN' {x y z A Bs Acc T : K} (h : [x, y, z, A, Bs, Acc, T].Nodup) (a b : ℕ)
    (rx ry old : List Sym) (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) (hz : S z = old) :
    Runs (mulN x y z A Bs Acc T) S (Function.update S z (natSyms (a * b) ++ old))
      (fun _ => True) (mulCost a b) := by
  subst hz; exact runs_mulN h a b rx ry S hrx hry hx hy

theorem runs_subN' {x y z t1 t2 t3 : K} (h : [x, y, z, t1, t2, t3].Nodup) (a b : ℕ)
    (rx ry old : List Sym) (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry) (hab : b ≤ a)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) (hz : S z = old) :
    Runs (subN x y z t1 t2 t3) S (Function.update S z (natSyms (a - b) ++ old))
      (fun _ => True) (20 * (bitLen a + bitLen b + 1)) := by
  subst hz; exact runs_subN h a b rx ry S hrx hry hab hx hy

theorem runs_xferW {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (u : List (List Bool)) (R old : List Sym) (S : K → List Sym)
    (hR : SubNLogN.Machine.K2.isRecR R.head? = false) (hS : S src = arrSyms u ++ R) (hd : S dst = old) :
    Runs ((C5.xfer src dst tmp).liftRegs lW) S
      (Function.update (Function.update S src R) dst (arrSyms u ++ old)) (fun _ => True)
      (6 * vol u + 2 * u.length + 5) := by
  subst hd
  refine SubNLogN.Machine.K1.runs_liftRegs_of_eval lW fun v => ⟨some .mark, _, ?_, le_rfl⟩
  exact C5.xfer_eval hsd hst hdt v u R S hR hS

end Primed

theorem sc_ne {E : Type} {x y : Scr} (h : x ≠ y) : (sc x : AK E) ≠ sc y :=
  fun e => h (Sum.inl_injective (Sum.inr_injective e))

theorem inl_ne_sc {E : Type} (i : Fin 5) (x : Scr) : (Sum.inl i : AK E) ≠ sc x := Sum.inl_ne_inr

theorem sc_ne_inl {E : Type} (x : Scr) (i : Fin 5) : (sc x : AK E) ≠ Sum.inl i := Sum.inr_ne_inl

/-- The closed part `Fin 5 ⊕ Scr` of the layout. -/
def emb {E : Type} : Fin 5 ⊕ Scr → AK E := Sum.map id Sum.inl

theorem emb_injective {E : Type} : Function.Injective (emb (E := E)) :=
  Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩

/-- Distinctness of named stacks, decided on the closed part of the layout. -/
theorem nodup_emb {E : Type} {l : List (Fin 5 ⊕ Scr)} (h : l.Nodup) :
    (l.map (emb (E := E))).Nodup :=
  h.map emb_injective

/-! ## Specifications of the counter programs -/

section Specs

variable {E : Type} [DecidableEq E]

/-- Cost of pushing a base factor. -/
def baseCost : Base → ℕ → ℕ → ℕ
  | .one, _, _ => bitLen 1 + 1
  | .G, G, _ => 7 * bitLen G + 7
  | .B, _, B => 7 * bitLen B + 7
  | .GB, G, B => mulCost G B

theorem runs_pushBase (bs : Base) (z : Scr) (hz : z = .cs ∨ z = .cn1) (G B : ℕ)
    (r3 r4 old : List Sym) (S : AK E → List Sym) (hr3 : TermOK r3) (hr4 : TermOK r4)
    (hG : S (.inl 3) = natSyms G ++ r3) (hB : S (.inl 4) = natSyms B ++ r4)
    (hold : S (sc z) = old) :
    Runs (pushBase bs z) S (Function.update S (sc z) (natSyms (bs.val G B) ++ old))
      (fun _ => True) (baseCost bs G B) := by
  cases bs
  · exact runs_pushNat' (sc z) 1 old S hold
  · exact runs_copyN' (inl_ne_sc 3 z) (inl_ne_sc 3 .ta)
      (sc_ne (by rcases hz with rfl | rfl <;> decide)) G r3 old S hr3 hG hold
  · exact runs_copyN' (inl_ne_sc 4 z) (inl_ne_sc 4 .ta)
      (sc_ne (by rcases hz with rfl | rfl <;> decide)) B r4 old S hr4 hB hold
  · have hnd : [(.inl 3 : AK E), .inl 4, sc z, sc .ta, sc .tb, sc .tc, sc .kt].Nodup :=
      nodup_emb (l := [.inl 3, .inl 4, .inr z, .inr .ta, .inr .tb, .inr .tc, .inr .kt])
        (by rcases hz with rfl | rfl <;> decide)
    exact runs_mulN' hnd G B r3 r4 old S hr3 hr4 hG hB hold

theorem runs_progVal (q : ℕ) (hq : 1 ≤ q) (bs : Base) (x : ℕ) (z : Scr) (hz : z = .cs ∨ z = .cn1)
    (b G B : ℕ) (rb r3 r4 old : List Sym) (S : AK E → List Sym) (hrb : TermOK rb)
    (hr3 : TermOK r3) (hr4 : TermOK r4) (hb : S (sc .cb) = natSyms b ++ rb)
    (hG : S (.inl 3) = natSyms G ++ r3) (hB : S (.inl 4) = natSyms B ++ r4)
    (hold : S (sc z) = old) :
    Runs (progVal q bs x z) S
      (Function.update S (sc z) (natSyms (bs.val G B * (q ^ x) ^ b) ++ Sym.mark :: old))
      (fun _ => True) (1 + baseCost bs G B + powCost (q ^ x) (bs.val G B) b) := by
  have hnd : [(sc z : AK E), sc .cb, sc .kc, sc .kt, sc .tq, sc .td, sc .ta, sc .tb,
      sc .tc].Nodup :=
    nodup_emb (l := [.inr z, .inr .cb, .inr .kc, .inr .kt, .inr .tq, .inr .td, .inr .ta, .inr .tb,
      .inr .tc]) (by rcases hz with rfl | rfl <;> decide)
  have hzb : (sc .cb : AK E) ≠ sc z := sc_ne (by rcases hz with rfl | rfl <;> decide)
  have r1 := runs_pushMark' (sc z) old S hold
  have r2 := runs_pushBase bs z hz G B r3 r4 (Sym.mark :: old)
    (Function.update S (sc z) (Sym.mark :: old)) hr3 hr4
    (by rw [Function.update_of_ne (inl_ne_sc 3 z)]; exact hG)
    (by rw [Function.update_of_ne (inl_ne_sc 4 z)]; exact hB)
    (Function.update_self _ _ _)
  rw [Function.update_idem] at r2
  have r3' := runs_powMulN hnd (q ^ x) (Nat.one_le_pow _ _ hq) (bs.val G B) b (Sym.mark :: old) rb
    (Function.update S (sc z) (natSyms (bs.val G B) ++ Sym.mark :: old)) (termOK_mark _) hrb
    (Function.update_self _ _ _) (by rw [Function.update_of_ne hzb]; exact hb)
  rw [Function.update_idem] at r3'
  exact WP.W9comp.runs_mono (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 r3')) (fun _ h => h)
    (by omega)

/-- Cost bound of `progB`. -/
def costB (m k : ℕ) : ℕ := if m = 1 then 3 else 22 * bitLen k + powCost m 1 (k - 1) + 60

theorem bitLen_one_le : bitLen 1 ≤ 1 := bitLen_le_of_lt' (by norm_num)

theorem runs_progB (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : 1 ≤ k) (r1 : List Sym)
    (S : AK E → List Sym) (hr1 : TermOK r1) (hS1 : S (.inl 1) = natSyms k ++ r1) :
    Runs (progB m) S (Function.update S (sc .cb) (natSyms (bOf m k) ++ Sym.mark :: S (sc .cb)))
      (fun _ => True) (costB m k) := by
  unfold progB costB
  split_ifs with hm1
  · subst hm1
    have e1 := runs_pushMark' (sc .cb) (S (sc .cb)) S rfl
    have e2 := runs_pushNat' (sc .cb) 1 (Sym.mark :: S (sc .cb))
      (Function.update S (sc .cb) (Sym.mark :: S (sc .cb))) (Function.update_self _ _ _)
    rw [Function.update_idem] at e2
    have hb : bOf 1 k = 1 := by simp [bOf]
    rw [hb]
    have := bitLen_one_le
    exact WP.W9comp.runs_mono (WP.W9comp.runs_seq e1 e2) (fun _ h => h) (by omega)
  · have d1 : (sc .co : AK E) ≠ sc .ck := sc_ne (by decide)
    have d2 : (sc .co : AK E) ≠ sc .cb := sc_ne (by decide)
    have d3 : (sc .co : AK E) ≠ sc .tq := sc_ne (by decide)
    have d4 : (sc .ck : AK E) ≠ sc .cb := sc_ne (by decide)
    have d5 : (sc .ck : AK E) ≠ sc .tq := sc_ne (by decide)
    have d6 : (sc .cb : AK E) ≠ sc .tq := sc_ne (by decide)
    have uA : ∀ u1 u2 u3 u4 v, Function.update (st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq)
        u1 u2 u3 u4) (sc .co) v = st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) v u2 u3 u4 :=
      fun u1 u2 u3 u4 v => st4_upd_A S u1 u2 u3 u4 d1 d2 d3 d4 d5 d6 v
    have uB : ∀ u1 u2 u3 u4 v, Function.update (st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq)
        u1 u2 u3 u4) (sc .ck) v = st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) u1 v u3 u4 :=
      fun u1 u2 u3 u4 v => st4_upd_Bs S u1 u2 u3 u4 d1 d2 d3 d4 d5 d6 v
    have uC : ∀ u1 u2 u3 u4 v, Function.update (st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq)
        u1 u2 u3 u4) (sc .cb) v = st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) u1 u2 v u4 :=
      fun u1 u2 u3 u4 v => st4_upd_Acc S u1 u2 u3 u4 d1 d2 d3 d4 d5 d6 v
    have gA : ∀ u1 u2 u3 u4, st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) u1 u2 u3 u4 (sc .co) = u1 :=
      fun u1 u2 u3 u4 => st4_A S u1 u2 u3 u4 d3 d2 d1
    have gB : ∀ u1 u2 u3 u4, st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) u1 u2 u3 u4 (sc .ck) = u2 :=
      fun u1 u2 u3 u4 => st4_Bs S u1 u2 u3 u4 d5 d4
    have gC : ∀ u1 u2 u3 u4, st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) u1 u2 u3 u4 (sc .cb) = u3 :=
      fun u1 u2 u3 u4 => st4_Acc S u1 u2 u3 u4 d6
    have g1 : ∀ u1 u2 u3 u4, st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) u1 u2 u3 u4 (.inl 1) =
        natSyms k ++ r1 := fun u1 u2 u3 u4 =>
      (st4_other S u1 u2 u3 u4 (inl_ne_sc 1 .tq) (inl_ne_sc 1 .cb) (inl_ne_sc 1 .ck)
        (inl_ne_sc 1 .co)).trans hS1
    have e0 : S = st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) (S (sc .co)) (S (sc .ck))
        (S (sc .cb)) (S (sc .tq)) := (st4_self S d1 d2 d3 d4 d5 d6).symm
    have e1 := runs_pushMark (sc .co)
      (st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) (S (sc .co)) (S (sc .ck)) (S (sc .cb)) (S (sc .tq)))
    rw [gA, uA] at e1
    have e2 := runs_pushNat (sc .co) 1 (st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq)
      (Sym.mark :: S (sc .co)) (S (sc .ck)) (S (sc .cb)) (S (sc .tq)))
    rw [gA, uA] at e2
    have e3 := runs_pushMark (sc .ck) (st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq)
      (natSyms 1 ++ Sym.mark :: S (sc .co)) (S (sc .ck)) (S (sc .cb)) (S (sc .tq)))
    rw [gB, uB] at e3
    have hnd4 : [(.inl 1 : AK E), sc .co, sc .ck, sc .ta, sc .tb, sc .tc].Nodup :=
      nodup_emb (l := [.inl 1, .inr .co, .inr .ck, .inr .ta, .inr .tb, .inr .tc]) (by decide)
    have e4 := runs_subN hnd4 k 1 r1 (Sym.mark :: S (sc .co))
      (st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) (natSyms 1 ++ Sym.mark :: S (sc .co))
        (Sym.mark :: S (sc .ck)) (S (sc .cb)) (S (sc .tq))) hr1 (termOK_mark _) hk
      (g1 _ _ _ _) (gA _ _ _ _)
    rw [gB, uB] at e4
    have e5 := runs_pushMark (sc .cb) (st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq)
      (natSyms 1 ++ Sym.mark :: S (sc .co)) (natSyms (k - 1) ++ Sym.mark :: S (sc .ck))
      (S (sc .cb)) (S (sc .tq)))
    rw [gC, uC] at e5
    have e6 := runs_pushNat (sc .cb) 1 (st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq)
      (natSyms 1 ++ Sym.mark :: S (sc .co)) (natSyms (k - 1) ++ Sym.mark :: S (sc .ck))
      (Sym.mark :: S (sc .cb)) (S (sc .tq)))
    rw [gC, uC] at e6
    have hnd7 : [(sc .cb : AK E), sc .ck, sc .kc, sc .kt, sc .tq, sc .td, sc .ta, sc .tb,
        sc .tc].Nodup :=
      nodup_emb (l := [.inr .cb, .inr .ck, .inr .kc, .inr .kt, .inr .tq, .inr .td, .inr .ta,
        .inr .tb, .inr .tc]) (by decide)
    have e7 := runs_powMulN hnd7 m hm 1 (k - 1) (Sym.mark :: S (sc .cb)) (Sym.mark :: S (sc .ck))
      (st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) (natSyms 1 ++ Sym.mark :: S (sc .co))
        (natSyms (k - 1) ++ Sym.mark :: S (sc .ck)) (natSyms 1 ++ Sym.mark :: S (sc .cb))
        (S (sc .tq))) (termOK_mark _) (termOK_mark _) (gC _ _ _ _) (gB _ _ _ _)
    rw [uC] at e7
    have e8 := runs_dropF (sc .ck) (k - 1) Sym.mark (S (sc .ck))
      (st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) (natSyms 1 ++ Sym.mark :: S (sc .co))
        (natSyms (k - 1) ++ Sym.mark :: S (sc .ck)) (natSyms (1 * m ^ (k - 1)) ++ Sym.mark :: S (sc .cb))
        (S (sc .tq))) rfl (gB _ _ _ _)
    rw [uB] at e8
    have e9 := runs_dropF (sc .co) 1 Sym.mark (S (sc .co))
      (st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) (natSyms 1 ++ Sym.mark :: S (sc .co))
        (S (sc .ck)) (natSyms (1 * m ^ (k - 1)) ++ Sym.mark :: S (sc .cb)) (S (sc .tq))) rfl
      (gA _ _ _ _)
    rw [uA] at e9
    have hfin : st4 S (sc .co) (sc .ck) (sc .cb) (sc .tq) (S (sc .co)) (S (sc .ck))
        (natSyms (1 * m ^ (k - 1)) ++ Sym.mark :: S (sc .cb)) (S (sc .tq)) =
        Function.update S (sc .cb) (natSyms (bOf m k) ++ Sym.mark :: S (sc .cb)) := by
      rw [← uC (S (sc .co)) (S (sc .ck)) (S (sc .cb)) (S (sc .tq)), st4_self S d1 d2 d3 d4 d5 d6,
        Nat.one_mul, bOf]
    have hall := WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq e2 (WP.W9comp.runs_seq e3
      (WP.W9comp.runs_seq e4 (WP.W9comp.runs_seq e5 (WP.W9comp.runs_seq e6
      (WP.W9comp.runs_seq e7 (WP.W9comp.runs_seq e8 e9)))))))
    rw [hfin] at hall
    refine Triple.cost_mono (Triple.pre hall fun s hs => hs.trans e0) ?_
    have h1 := bitLen_one_le
    have h2 : bitLen (k - 1) ≤ bitLen k := bitLen_mono'' (Nat.sub_le k 1)
    omega

end Specs

/-! ## The setup, the transfer back, and the atomic step -/

section Atom

variable {E : Type} [DecidableEq E]

/-- The stacks after `setup`: counters above marks, a mark on `T`. -/
def setSt (S : AK E → List Sym) (b s n1 : ℕ) : AK E → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update S (sc .cb) (natSyms b ++ Sym.mark :: S (sc .cb)))
    (sc .cs) (natSyms s ++ Sym.mark :: S (sc .cs)))
    (sc .cn1) (natSyms n1 ++ Sym.mark :: S (sc .cn1)))
    (sc .cb1) (natSyms b ++ Sym.mark :: S (sc .cb1)))
    (sc .cb2) (Sym.mark :: S (sc .cb2)))
    (sc .cn2) (natSyms 1 ++ Sym.mark :: S (sc .cn2)))
    (sc .T) (Sym.mark :: S (sc .T))

/-- Cost of `setup`. -/
def costSetup (q m : ℕ) (c : Ctr) (k G B : ℕ) : ℕ :=
  costB m k + (1 + baseCost c.bs G B + powCost (q ^ c.xs) (c.bs.val G B) (bOf m k)) +
    (1 + baseCost c.b1 G B + powCost (q ^ c.x1) (c.b1.val G B) (bOf m k)) +
    (1 + (7 * bitLen (bOf m k) + 7)) + 1 + (1 + (bitLen 1 + 1)) + 1

theorem runs_setup (q m : ℕ) (hq : 1 ≤ q) (hm : 1 ≤ m) (c : Ctr) (k G B : ℕ) (hk : 1 ≤ k)
    (r1 r3 r4 : List Sym) (S : AK E → List Sym) (hr1 : TermOK r1) (hr3 : TermOK r3)
    (hr4 : TermOK r4) (hS1 : S (.inl 1) = natSyms k ++ r1) (hS3 : S (.inl 3) = natSyms G ++ r3)
    (hS4 : S (.inl 4) = natSyms B ++ r4) :
    Runs (setup q m c) S
      (setSt S (bOf m k) (valOf q m c.bs c.xs k G B) (valOf q m c.b1 c.x1 k G B))
      (fun _ => True) (costSetup q m c k G B) := by
  have e1 := runs_progB m hm k hk r1 S hr1 hS1
  have e2 := runs_progVal q hq c.bs c.xs .cs (Or.inl rfl) (bOf m k) G B (Sym.mark :: S (sc .cb))
    r3 r4 (S (sc .cs)) (Function.update S (sc .cb) (natSyms (bOf m k) ++ Sym.mark :: S (sc .cb)))
    (termOK_mark _) hr3 hr4 (by simp) (by simp [hS3]) (by simp [hS4]) (by simp)
  have e3 := runs_progVal q hq c.b1 c.x1 .cn1 (Or.inr rfl) (bOf m k) G B (Sym.mark :: S (sc .cb))
    r3 r4 (S (sc .cn1)) (Function.update (Function.update S (sc .cb)
      (natSyms (bOf m k) ++ Sym.mark :: S (sc .cb))) (sc .cs)
      (natSyms (c.bs.val G B * (q ^ c.xs) ^ bOf m k) ++ Sym.mark :: S (sc .cs)))
    (termOK_mark _) hr3 hr4 (by simp) (by simp [hS3]) (by simp [hS4]) (by simp)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_seq e1 (WP.W9comp.runs_seq e2
    (WP.W9comp.runs_seq e3 (WP.W9comp.runs_seq
      (runs_pushMark' (sc .cb1) (S (sc .cb1)) _ (by simp))
    (WP.W9comp.runs_seq (WP.W9comp.runs_congr (runs_copyN' (src := sc .cb) (dst := sc .cb1)
      (tmp := sc .ta) (sc_ne (by decide)) (sc_ne (by decide)) (sc_ne (by decide)) (bOf m k)
      (Sym.mark :: S (sc .cb)) (Sym.mark :: S (sc .cb1)) _ (termOK_mark _) (by simp)
      (Function.update_self _ _ _)) (Function.update_idem _ _ _))
    (WP.W9comp.runs_seq (runs_pushMark' (sc .cb2) (S (sc .cb2)) _ (by simp))
    (WP.W9comp.runs_seq (runs_pushMark' (sc .cn2) (S (sc .cn2)) _ (by simp))
    (WP.W9comp.runs_seq (WP.W9comp.runs_congr (runs_pushNat' (sc .cn2) 1
      (Sym.mark :: S (sc .cn2)) _ (Function.update_self _ _ _)) (Function.update_idem _ _ _))
      (runs_pushMark' (sc .T) (S (sc .T)) _ (by simp)))))))))) (fun _ h => h) ?_
  simp only [costSetup]
  omega

/-- Cost of `post`. -/
def costPost (b s n1 : ℕ) (v' : List (List Bool)) : ℕ :=
  (6 * vol v' + 2 * v'.length + 5) + 1 + (2 * bitLen 1 + 2) + (2 * bitLen 0 + 2) +
    (2 * bitLen b + 2) + (2 * bitLen n1 + 2) + (2 * bitLen s + 2) + (2 * bitLen b + 2)

theorem runs_post (b s n1 : ℕ) (v' : List (List Bool)) (rest : List Sym)
    (S : AK E → List Sym) :
    Runs post (Function.update (Function.update (setSt S b s n1) (.inl 0) rest) (sc .T)
        (arrSyms v' ++ Sym.mark :: S (sc .T)))
      (Function.update S (.inl 0) (arrSyms v' ++ rest)) (fun _ => True) (costPost b s n1 v') := by
  have p1 := runs_xferW (src := sc .T) (dst := .inl 0) (tmp := sc .X) (sc_ne_inl .T 0)
    (sc_ne (by decide)) (inl_ne_sc 0 .X) v' (Sym.mark :: S (sc .T)) rest
    (Function.update (Function.update (setSt S b s n1) (.inl 0) rest) (sc .T)
        (arrSyms v' ++ Sym.mark :: S (sc .T))) rfl (Function.update_self _ _ _)
    (by rw [Function.update_of_ne (inl_ne_sc 0 .T), Function.update_self])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq p1
    (WP.W9comp.runs_seq (runs_popW' (sc .T) Sym.mark (S (sc .T)) _ (by simp))
    (WP.W9comp.runs_seq (runs_dropF (sc .cn2) 1 Sym.mark (S (sc .cn2)) _ rfl (by simp [setSt]))
    (WP.W9comp.runs_seq (runs_dropF (sc .cb2) 0 Sym.mark (S (sc .cb2)) _ rfl
      (by simp [setSt, natSyms_zero]))
    (WP.W9comp.runs_seq (runs_dropF (sc .cb1) b Sym.mark (S (sc .cb1)) _ rfl (by simp [setSt]))
    (WP.W9comp.runs_seq (runs_dropF (sc .cn1) n1 Sym.mark (S (sc .cn1)) _ rfl (by simp [setSt]))
    (WP.W9comp.runs_seq (runs_dropF (sc .cs) s Sym.mark (S (sc .cs)) _ rfl (by simp [setSt]))
      (runs_dropF (sc .cb) b Sym.mark (S (sc .cb)) _ rfl (by simp [setSt]))))))))) ?_)
    (fun _ h => h) (le_of_eq ?_)
  · funext y
    simp only [setSt, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [costPost]
    ring

/-- **The atomic step** around a sub-kernel call that moves the array from stack `0` onto `T`. -/
theorem runs_atom (q m : ℕ) (hq : 1 ≤ q) (hm : 1 ≤ m) (c : Ctr) {R : Type}
    (call : Prog (AK E) (fun _ => Sym) (Reg × R)) (k G B : ℕ) (hk : 1 ≤ k)
    (r1 r3 r4 : List Sym) (S : AK E → List Sym) (hr1 : TermOK r1) (hr3 : TermOK r3)
    (hr4 : TermOK r4) (hS1 : S (.inl 1) = natSyms k ++ r1) (hS3 : S (.inl 3) = natSyms G ++ r3)
    (hS4 : S (.inl 4) = natSyms B ++ r4) (v' : List (List Bool)) (rest : List Sym) (Tc : ℕ)
    (hcall : Runs call
      (setSt S (bOf m k) (valOf q m c.bs c.xs k G B) (valOf q m c.b1 c.x1 k G B))
      (Function.update (Function.update
        (setSt S (bOf m k) (valOf q m c.bs c.xs k G B) (valOf q m c.b1 c.x1 k G B)) (.inl 0) rest)
        (sc .T) (arrSyms v' ++ Sym.mark :: S (sc .T))) (fun _ => True) Tc) :
    Runs (atomProg q m c call) S (Function.update S (.inl 0) (arrSyms v' ++ rest))
      (fun _ => True)
      (costSetup q m c k G B + (Tc + costPost (bOf m k) (valOf q m c.bs c.xs k G B)
        (valOf q m c.b1 c.x1 k G B) v')) :=
  WP.W9comp.runs_seq
    (runs_liftRegs' _ (runs_setup q m hq hm c k G B hk r1 r3 r4 S hr1 hr3 hr4 hS1 hS3 hS4))
    (WP.W9comp.runs_seq hcall (runs_liftRegs' _ (runs_post _ _ _ v' rest S)))

end Atom

end SubNLogN.Machine.C5.StreamAux
