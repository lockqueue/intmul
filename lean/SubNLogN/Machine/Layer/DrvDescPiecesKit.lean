/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5StreamArith
import SubNLogN.Machine.Calculus.Hdr
import WP.W6a.DivMod

/-!
# DrvDesc PIECES, part 1 (`Machine/Layer/DrvDescPiecesKit.lean`): primitives and loop rules

Support file for `DrvDescPiecesStmt` (`Machine/Layer/DrvDescDefs.lean`). Programs over any stack
type `K` with the register file `PReg = NatArith.Reg × WP.W6a.DReg WP.W3.AReg`, each with an exact
`Runs` rule (every stack not mentioned is unchanged; temporaries may hold arbitrary content and
are restored):
* one-symbol pieces `pushW`, `popW`, `peekW` and the stream calls `copyW` (`Lib.copyBlock`),
  `dropW` (`WP.W3.dropNum`), `dropFW` (`K1.dropBits`), `incW`/`decW` (`Lib.inc`/`Lib.dec`),
  `copyHdrW` (`Calculus.copyHdr`);
* arithmetic: `addP` (`NatArith.addN`), `mulP` (`NatArith.mulN`), `pushNatP`
  (`NatArith.pushNat`), `dmP` (the W6a divider `WP.W6a.divModProg` over the W3 subtractor, as in
  `AppC/C7ExtractInst.lean`);
* in-place `addTo` (`k := k + b`) and `mulBy` (`k := k * b`);
* `whileW k c p` (peek-tested while loop) with the rule `runs_whileW`.

**Scope (honest summary).** Definitions and proved rules only; no contract is proved here.
-/

namespace SubNLogN.Machine.Layer.DrvDescPiecesAux

open TMFw TMFw.Lib TMFw.Contracts Computability SubNLogN.Machine

/-- Register file: the `NatArith` registers and the W6a divider's. -/
abbrev PReg : Type := NatArith.Reg × WP.W6a.DReg WP.W3.AReg

/-- Lens to the `NatArith` registers. -/
def lN : Lens PReg NatArith.Reg := Lens.fst _ _
/-- Lens to the divider registers. -/
def lD : Lens PReg (WP.W6a.DReg WP.W3.AReg) := Lens.snd _ _
/-- Lens to the one-symbol work register. -/
def lW : Lens PReg (Option Sym) := lN.comp NatArith.lW

instance : Nonempty PReg :=
  ⟨((none, (none, none, false), (none, none, .eq)), (none, false, (none, none, .eq),
    (none, none, false)))⟩

theorem tok_mark (L : List Sym) : TermOK (Sym.mark :: L) := TermOK.cons rfl _
theorem tok_sep (L : List Sym) : TermOK (Sym.sep :: L) := TermOK.cons rfl _

section Prims

variable {K : Type}

/-- Programs of the kernel. -/
abbrev PP (K : Type) : Type := Prog K (fun _ => Sym) PReg

/-- Push the constant `s` on `k`. -/
def pushW (k : K) (s : Sym) : PP K := (pushC k s).liftRegs lW
/-- Pop the top of `k`. -/
def popW (k : K) : PP K := (popR k).liftRegs lW
/-- Peek the top of `k` into the work register. -/
def peekW (k : K) : PP K := (peekR k).liftRegs lW
/-- Copy the bit block on top of `src` onto `dst`. -/
def copyW (src dst tmp : K) : PP K := (copyBlock src dst tmp).liftRegs lW
/-- Pop the number on top of `k`, keeping its terminator. -/
def dropW (k : K) : PP K := (WP.W3.dropNum k).liftRegs lW
/-- Pop the number on top of `k` together with the non-bit symbol below it. -/
def dropFW (k : K) : PP K := (K1.dropBits k).liftRegs lW
/-- Increment the counter on `k`. -/
def incW (k t : K) : PP K := (inc k t).liftRegs lW
/-- Decrement the (positive) counter on `k`. -/
def decW (k t : K) : PP K := (dec k t).liftRegs lW
/-- Copy a header of `n` fields from `src` onto `dst`. -/
def copyHdrW (n : ℕ) (src dst t : K) : PP K := (Calculus.copyHdr n src dst t).liftRegs lW
/-- `z += a + b`. -/
def addP (x y z t1 t2 t3 : K) : PP K := (NatArith.addN x y z t1 t2 t3).liftRegs lN
/-- `z += a * b`. -/
def mulP (x y z A Bs Acc T : K) : PP K := (NatArith.mulN x y z A Bs Acc T).liftRegs lN
/-- Push the constant `c`. -/
def pushNatP (k : K) (c : ℕ) : PP K := (NatArith.pushNat k c).liftRegs lN

/-- Embedding of the seven stacks of the divider (`a, b, q, r` and three temporaries). -/
def dmEmb (x y q r d0 d1 d2 : K) : Loc 4 3 → K
  | .inl i => if i.val = 0 then x else if i.val = 1 then y else if i.val = 2 then q else r
  | .inr i => if i.val = 0 then d0 else if i.val = 1 then d1 else d2

/-- The concrete divider. -/
abbrev divProg : Prog WP.W6a.DStk (fun _ => Sym) (WP.W6a.DReg WP.W3.AReg) :=
  WP.W6a.divModProg (WP.W3.addSubProg WP.W3.subBit)

/-- `q += a / b`, `r += a % b`. -/
def dmP (x y q r d0 d1 d2 : K) : PP K := callInj (dmEmb x y q r d0 d1 d2) lD divProg

theorem closed_pushW (k : K) (s : Sym) : (pushW k s).Closed :=
  WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, pushC])
theorem closed_popW (k : K) : (popW k).Closed :=
  WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, popR])
theorem closed_peekW (k : K) : (peekW k).Closed :=
  WP.W9comp.closed_liftRegs _ (by simp [Prog.Closed, Prog.FreeBelow, peekR])
theorem closed_copyW (src dst tmp : K) : (copyW src dst tmp).Closed :=
  WP.W9comp.closed_liftRegs _ (WP.W3.closed_of_noRec rfl)
theorem closed_dropW (k : K) : (dropW k).Closed :=
  WP.W9comp.closed_liftRegs _ (WP.W3.closed_of_noRec rfl)
theorem closed_dropFW (k : K) : (dropFW k).Closed :=
  WP.W9comp.closed_liftRegs _ (WP.W3.closed_of_noRec rfl)
theorem closed_incW (k t : K) : (incW k t).Closed :=
  WP.W9comp.closed_liftRegs _ (WP.W3.closed_of_noRec rfl)
theorem closed_decW (k t : K) : (decW k t).Closed :=
  WP.W9comp.closed_liftRegs _ (WP.W3.closed_of_noRec rfl)
theorem closed_copyHdrW (n : ℕ) (src dst t : K) : (copyHdrW n src dst t).Closed :=
  WP.W9comp.closed_liftRegs _ (Calculus.closed_copyHdr n src dst t)
theorem closed_addP (x y z t1 t2 t3 : K) : (addP x y z t1 t2 t3).Closed :=
  WP.W9comp.closed_liftRegs _ (NatArith.closed_addN _ _ _ _ _ _)
theorem closed_mulP (x y z A Bs Acc T : K) : (mulP x y z A Bs Acc T).Closed :=
  WP.W9comp.closed_liftRegs _ (NatArith.closed_mulN _ _ _ _ _ _ _)
theorem closed_pushNatP (k : K) (c : ℕ) : (pushNatP k c).Closed :=
  WP.W9comp.closed_liftRegs _ (NatArith.closed_pushNat _ _)
theorem closed_dmP (x y q r d0 d1 d2 : K) : (dmP x y q r d0 d1 d2).Closed :=
  closed_callInj _ _ (WP.W6a.divModProg_closed _ (WP.W3.addSubProg_closed _))

theorem dmEmb_injective {x y q r d0 d1 d2 : K} (h : [x, y, q, r, d0, d1, d2].Nodup) :
    Function.Injective (dmEmb x y q r d0 d1 d2) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  obtain ⟨⟨hxy, hxq, hxr, hx0, hx1, hx2⟩, ⟨hyq, hyr, hy0, hy1, hy2⟩, ⟨hqr, hq0, hq1, hq2⟩,
    ⟨hr0, hr1, hr2⟩, ⟨h01, h02⟩, h12⟩ := h
  intro u v huv
  rcases u with ⟨a, ha⟩ | ⟨a, ha⟩ <;> rcases v with ⟨b, hb⟩ | ⟨b, hb⟩
  · simp only [dmEmb] at huv
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp_all
  · simp only [dmEmb] at huv
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl <;>
    simp_all
  · simp only [dmEmb] at huv
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp_all
  · simp only [dmEmb] at huv
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl <;>
    simp_all

/-- The W3 subtraction spec of the concrete subtractor (constant `20`). -/
theorem subSpec_sub : WP.W6a.SubSpec 20 (WP.W3.addSubProg WP.W3.subBit) := by
  intro a b rx ry S hrx hry hab hx hy
  refine Runs.of_eval fun v => ?_
  obtain ⟨v', t, e, ht⟩ := WP.W3.addSubProg_eval WP.W3.subBit (encodeNat a) (encodeNat b) rx ry
    hrx hry S hx hy v
  have hle : bitsVal (encodeNat b) ≤ bitsVal (encodeNat a) := by
    rw [bitsVal_encodeNat, bitsVal_encodeNat]
    exact hab
  have hval : bitsVal (WP.W3.rip WP.W3.subBit (max (encodeNat a).length (encodeNat b).length)
      false (encodeNat a) (encodeNat b)) = a - b := by
    rw [WP.W3.bitsVal_rip_sub (max (encodeNat a).length (encodeNat b).length) (encodeNat a)
      (encodeNat b) (le_max_left _ _) (le_max_right _ _) hle, bitsVal_encodeNat,
      bitsVal_encodeNat]
  rw [hval] at e
  refine ⟨v', t, e, trivial, ?_⟩
  simp only [bitLen]
  omega

variable [DecidableEq K]

theorem runs_pushW (k : K) (s : Sym) (S : K → List Sym) :
    Runs (pushW k s) S (Function.update S k (s :: S k)) (fun _ => True) 1 :=
  K1.runs_wk_pushC lW k s S

theorem runs_popW (k : K) (S : K → List Sym) (a : Sym) (l : List Sym) (hS : S k = a :: l) :
    Runs (popW k) S (Function.update S k l) (fun _ => True) 1 := by
  have h := K1.runs_wk_popR lW k S
  rw [hS, List.tail_cons] at h
  exact h

theorem runs_copyW {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (a : ℕ) (rx : List Sym) (S : K → List Sym) (hrx : TermOK rx)
    (hS : S src = natSyms a ++ rx) :
    Runs (copyW src dst tmp) S (Function.update S dst (natSyms a ++ S dst)) (fun _ => True)
      (7 * bitLen a + 7) :=
  K1.runs_liftRegs_of_eval lW fun v =>
    ⟨some .mark, _, copyBlock_eval hsd hst hdt [] v (encodeNat a) rx S hrx hS, le_rfl⟩

theorem runs_dropW (k : K) (a : ℕ) (rx : List Sym) (S : K → List Sym) (hrx : TermOK rx)
    (hS : S k = natSyms a ++ rx) :
    Runs (dropW k) S (Function.update S k rx) (fun _ => True) (2 * bitLen a + 4) :=
  K1.runs_liftRegs_of_eval lW fun v =>
    ⟨_, _, WP.W3.dropNum_eval [] v (encodeNat a) rx S hrx hS, le_rfl⟩

theorem runs_dropFW (k : K) (a : ℕ) (t : Sym) (rest : List Sym) (S : K → List Sym)
    (ht : t.isBit = false) (hS : S k = natSyms a ++ t :: rest) :
    Runs (dropFW k) S (Function.update S k rest) (fun _ => True) (2 * bitLen a + 2) :=
  K1.runs_wk_dropBits lW k (encodeNat a) t rest S ht hS

theorem runs_incW {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms n ++ rest) :
    Runs (incW k t) S (Function.update S k (natSyms (n + 1) ++ rest)) (fun _ => True)
      (6 * bitLen n + 9) :=
  WP.W9comp.runs_mono (K1.runs_wk_inc lW hkt n rest S hrest hS) (fun _ _ => trivial)
    (by have := ones_le_length (encodeNat n); simp only [bitLen]; omega)

theorem runs_decW {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms (n + 1) ++ rest) :
    Runs (decW k t) S (Function.update S k (natSyms n ++ rest)) (fun _ => True)
      (6 * bitLen (n + 1) + 8) :=
  WP.W9comp.runs_mono (K1.runs_wk_dec lW hkt n rest S hrest hS) (fun _ _ => trivial)
    (by have := zerosLead_le_length (encodeNat (n + 1)); simp only [bitLen]; omega)

theorem runs_copyHdrW {src dst t : K} (hsd : src ≠ dst) (hst : src ≠ t) (hdt : dst ≠ t)
    (fs : List ℕ) (tl : List Sym) (S : K → List Sym) (hS : S src = W9.hdrSyms fs ++ tl)
    (ht : TermOK (S t)) :
    Runs (copyHdrW fs.length src dst t) S (Function.update S dst (W9.hdrSyms fs ++ S dst))
      (fun _ => True) ((fs.map fun f => 13 * bitLen f + 20).sum + 2) :=
  WP.W9comp.runs_mono (WP.W0m.runs_liftRegs lW (Calculus.runs_copyHdr hsd hst hdt fs tl S hS ht))
    (fun _ _ => trivial) le_rfl

theorem runs_addP {x y z t1 t2 t3 : K} (h : [x, y, z, t1, t2, t3].Nodup) (a b : ℕ)
    (rx ry : List Sym) (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) :
    Runs (addP x y z t1 t2 t3) S (Function.update S z (natSyms (a + b) ++ S z))
      (fun _ => True) (20 * (bitLen a + bitLen b + 1)) :=
  WP.W9comp.runs_mono (WP.W0m.runs_liftRegs lN (NatArith.runs_addN h a b rx ry S hrx hry hx hy))
    (fun _ _ => trivial) le_rfl

theorem runs_mulP {x y z A Bs Acc T : K} (h : [x, y, z, A, Bs, Acc, T].Nodup) (a b : ℕ)
    (rx ry : List Sym) (S : K → List Sym) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) :
    Runs (mulP x y z A Bs Acc T) S (Function.update S z (natSyms (a * b) ++ S z))
      (fun _ => True) (NatArith.mulCost a b) :=
  WP.W9comp.runs_mono (WP.W0m.runs_liftRegs lN (NatArith.runs_mulN h a b rx ry S hrx hry hx hy))
    (fun _ _ => trivial) le_rfl

theorem runs_pushNatP (k : K) (c : ℕ) (S : K → List Sym) :
    Runs (pushNatP k c) S (Function.update S k (natSyms c ++ S k)) (fun _ => True)
      (bitLen c + 1) :=
  WP.W9comp.runs_mono (WP.W0m.runs_liftRegs lN (NatArith.runs_pushNat k c S))
    (fun _ _ => trivial) le_rfl

theorem runs_dmP {x y q r d0 d1 d2 : K} (h : [x, y, q, r, d0, d1, d2].Nodup) (a b : ℕ)
    (rx ry : List Sym) (S : K → List Sym) (hb : 0 < b) (hrx : TermOK rx) (hry : TermOK ry)
    (hx : S x = natSyms a ++ rx) (hy : S y = natSyms b ++ ry) :
    Runs (dmP x y q r d0 d1 d2) S
      (Function.update (Function.update S q (natSyms (a / b) ++ S q)) r
        (natSyms (a % b) ++ S r))
      (fun _ => True) (110 * (bitLen a * bitLen b + bitLen a + bitLen b + 1)) := by
  have hι := dmEmb_injective h
  refine runs_callInj hι lD (Q := fun _ => True) ?_ ?_
  · have e1 : (Function.update (Function.update S q (natSyms (a / b) ++ S q)) r
        (natSyms (a % b) ++ S r)) ∘ dmEmb x y q r d0 d1 d2 =
        Function.update ((Function.update S q (natSyms (a / b) ++ S q)) ∘
          dmEmb x y q r d0 d1 d2) WP.W6a.sR (natSyms (a % b) ++ S r) :=
      Function.update_comp_eq_of_injective _ hι WP.W6a.sR _
    have e2 : (Function.update S q (natSyms (a / b) ++ S q)) ∘ dmEmb x y q r d0 d1 d2 =
        Function.update (S ∘ dmEmb x y q r d0 d1 d2) WP.W6a.sQ (natSyms (a / b) ++ S q) :=
      Function.update_comp_eq_of_injective _ hι WP.W6a.sQ _
    rw [e1, e2]
    exact WP.W6a.divModProg_spec (by norm_num) subSpec_sub a b rx ry _ hb hrx hry hx hy
  · intro k hk
    rw [Function.update_of_ne, Function.update_of_ne]
    · intro hkq
      exact hk (.inl 2) hkq.symm
    · intro hkr
      exact hk (.inl 3) hkr.symm

/-! ## Sequencing and the while rule -/

theorem pseq {P Q : PP K} {S1 S2 S3 : K → List Sym} {T1 T2 T : ℕ}
    (h1 : Runs P S1 S2 (fun _ => True) T1) (h2 : Runs Q S2 S3 (fun _ => True) T2)
    (hT : T1 + T2 ≤ T) : Runs (.seq P Q) S1 S3 (fun _ => True) T :=
  WP.W9comp.runs_mono (WP.W9comp.runs_seq h1 h2) (fun _ _ => trivial) hT

theorem pweak {P : PP K} {S S' S'' : K → List Sym} {T T' : ℕ}
    (h : Runs P S S' (fun _ => True) T) (he : S' = S'') (hT : T ≤ T') :
    Runs P S S'' (fun _ => True) T' :=
  WP.W9comp.runs_mono (he ▸ h) (fun _ _ => trivial) hT

/-- `whileW k c p`: while the peeked top of `k` satisfies `c`, run `p`. -/
def whileW (k : K) (c : Option Sym → Bool) (p : PP K) : PP K :=
  .seq (peekW k) (.loop (fun v => c (lW.get v)) (.seq p (peekW k)))

theorem closed_whileW (k : K) (c : Option Sym → Bool) {p : PP K} (hp : p.Closed) :
    (whileW k c p).Closed :=
  ⟨closed_peekW k, hp, closed_peekW k⟩

/-- **While rule.** An explicit sequence of exact states `S 0, …, S N`; the test holds at `S i`
(`i < N`) and fails at `S N`; each iteration runs within `Tb`. -/
theorem runs_whileW {k : K} {c : Option Sym → Bool} {p : PP K} (S : ℕ → K → List Sym)
    (Tb N : ℕ) (hc : ∀ i < N, c (S i k).head? = true) (hN : c (S N k).head? = false)
    (hstep : ∀ i < N, Runs p (S i) (S (i + 1)) (fun _ => True) Tb) :
    Runs (whileW k c p) (S 0) (S N) (fun _ => True) (N * (Tb + 2) + 2) := by
  have hloop : Triple [] (fun s => s.stk = S 0 ∧ lW.get s.var = (S 0 k).head?)
      (.loop (fun v => c (lW.get v)) (.seq p (peekW k))) (fun s => s.stk = S N)
      (N * (Tb + 2) + 1) := by
    have h := Triple.loop (ρ := []) (c := fun v => c (lW.get v)) (p := .seq p (peekW k))
      (I := fun n s => n ≤ N ∧ s.stk = S (N - n) ∧ lW.get s.var = (S (N - n) k).head?)
      (B := fun _ => Tb + 1) ?_ ?_ ?_ N
    · rw [loopCost_const] at h
      refine (h.pre ?_).post ?_
      · rintro s ⟨h1, h2⟩
        exact ⟨le_refl _, by simpa using h1, by simpa using h2⟩
      · rintro s ⟨-, h2, -⟩
        simpa using h2
    · rintro n s ⟨hn, hs1, -⟩
      have hi : N - (n + 1) < N := by omega
      have he : N - (n + 1) + 1 = N - n := by omega
      obtain ⟨s1, t1, e1, ⟨hs1', -⟩, ht1⟩ := hstep (N - (n + 1)) hi s hs1
      obtain ⟨s2, t2, e2, ⟨hs2', hv⟩, ht2⟩ :=
        K1.triple_peek_lens lW k (S (N - (n + 1) + 1)) s1 hs1'
      refine ⟨s2, t1 + t2, Eval.seq e1 e2, ⟨by omega, ?_, ?_⟩, by omega⟩
      · rw [hs2', he]
      · rw [hv, he]
    · rintro n s ⟨hn, -, hs2⟩
      show c (lW.get s.var) = true
      rw [hs2]
      exact hc _ (by omega)
    · rintro s ⟨-, -, hs2⟩
      show c (lW.get s.var) = false
      rw [hs2]
      simpa using hN
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ := K1.triple_peek_lens lW k (S 0) s hs
  obtain ⟨s2, t2, e2, hs2, ht2⟩ := hloop s1 ⟨hs1, hv1⟩
  exact ⟨s2, t1 + t2, Eval.seq e1 e2, ⟨hs2, trivial⟩, by omega⟩

/-! ## In-place routines -/

/-- `k := k + b` (result on the floored temporary `t`; temporaries `t1 t2 t3`). -/
def addTo (k b t t1 t2 t3 : K) : PP K :=
  .seq (pushW t .mark) (.seq (addP k b t t1 t2 t3) (.seq (dropW k)
    (.seq (copyW t k t1) (dropFW t))))

/-- `k := k * b` (result on the floored temporary `t`; temporaries `A Bs Acc T`). -/
def mulBy (k b t A Bs Acc T : K) : PP K :=
  .seq (pushW t .mark) (.seq (mulP k b t A Bs Acc T) (.seq (dropW k)
    (.seq (copyW t k A) (dropFW t))))

omit [DecidableEq K] in
theorem closed_addTo (k b t t1 t2 t3 : K) : (addTo k b t t1 t2 t3).Closed :=
  ⟨closed_pushW _ _, closed_addP _ _ _ _ _ _, closed_dropW _, closed_copyW _ _ _,
    closed_dropFW _⟩

omit [DecidableEq K] in
theorem closed_mulBy (k b t A Bs Acc T : K) : (mulBy k b t A Bs Acc T).Closed :=
  ⟨closed_pushW _ _, closed_mulP _ _ _ _ _ _ _, closed_dropW _, closed_copyW _ _ _,
    closed_dropFW _⟩

theorem runs_addTo {k b t t1 t2 t3 : K} (h : [k, b, t, t1, t2, t3].Nodup) (x y : ℕ)
    (rk rb : List Sym) (S : K → List Sym) (hrk : TermOK rk) (hrb : TermOK rb)
    (hk : S k = natSyms x ++ rk) (hb : S b = natSyms y ++ rb) :
    Runs (addTo k b t t1 t2 t3) S (Function.update S k (natSyms (x + y) ++ rk))
      (fun _ => True) (40 * (bitLen x + bitLen y + bitLen (x + y) + 1)) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hkb, hkt, hk1, -, -⟩, ⟨hbt, -, -, -⟩, ⟨ht1, -, -⟩, -, -⟩ := h'
  have X := WP.W9comp.runs_seq (runs_pushW t .mark S)
    (WP.W9comp.runs_seq (runs_addP h x y rk rb _ hrk hrb
      (by simp [Function.update_apply, hkt, hk]) (by simp [Function.update_apply, hbt, hb]))
    (WP.W9comp.runs_seq (runs_dropW k x rk _ hrk (by simp [Function.update_apply, hkt, hk]))
    (WP.W9comp.runs_seq (runs_copyW (Ne.symm hkt) ht1 hk1 (x + y) (Sym.mark :: S t) _
      (tok_mark _) (by simp [Function.update_apply, Ne.symm hkt]))
      (runs_dropFW t (x + y) .mark (S t) _ rfl
        (by simp [Function.update_apply, Ne.symm hkt])))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext j
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · omega

theorem runs_mulBy {k b t A Bs Acc T : K} (h : [k, b, t, A, Bs, Acc, T].Nodup) (x y : ℕ)
    (rk rb : List Sym) (S : K → List Sym) (hrk : TermOK rk) (hrb : TermOK rb)
    (hk : S k = natSyms x ++ rk) (hb : S b = natSyms y ++ rb) :
    Runs (mulBy k b t A Bs Acc T) S (Function.update S k (natSyms (x * y) ++ rk))
      (fun _ => True) (NatArith.mulCost x y + 2 * bitLen x + 9 * bitLen (x * y) + 14) := by
  have h' := h
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h'
  obtain ⟨⟨hkb, hkt, hkA, -, -, -⟩, ⟨hbt, -, -, -, -⟩, ⟨htA, -, -, -⟩, -, -, -⟩ := h'
  have X := WP.W9comp.runs_seq (runs_pushW t .mark S)
    (WP.W9comp.runs_seq (runs_mulP h x y rk rb _ hrk hrb
      (by simp [Function.update_apply, hkt, hk]) (by simp [Function.update_apply, hbt, hb]))
    (WP.W9comp.runs_seq (runs_dropW k x rk _ hrk (by simp [Function.update_apply, hkt, hk]))
    (WP.W9comp.runs_seq (runs_copyW (Ne.symm hkt) htA hkA (x * y) (Sym.mark :: S t) _
      (tok_mark _) (by simp [Function.update_apply, Ne.symm hkt]))
      (runs_dropFW t (x * y) .mark (S t) _ rfl
        (by simp [Function.update_apply, Ne.symm hkt])))))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr X ?_) (fun _ _ => trivial) ?_
  · funext j
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · omega

end Prims

end SubNLogN.Machine.Layer.DrvDescPiecesAux
