/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.ExposeAddr
import SubNLogN.Machine.Bridge.PrePostBase
import SubNLogN.Machine.Bridge.Kit
import WP.W9mp.Glue

/-!
# K5 axis exposures (2): machine kit

Machine building blocks of the exposure kernels (register `Option Sym × σ'`, the flag first):
* `encodeNat_pow_two`, `natSyms_two_mul`: binary encodings used by the counters (`natSyms (2^a)`
  is `a` zero bits and a one bit, so a header field `t_l = 2^a` is read in unary);
* `runs_cond_loop`: a loop `peek k; while c (core; peek k)` from a state family indexed by the
  number of remaining iterations (generalizes `BridgeRed.runs_counted_loop`);
* `lift`, `runs_lift`: a flag-register program (`SProg`) run on the first register component;
* `countField` (`runs_countField`): move a header field `natSyms (2^a) ++ [mark]` to a stack,
  adding `a` to a binary counter; `unaryField` (`runs_unaryField`): the same, pushing `a` zero bits
  on a second stack (this builds `natSyms (2^{Σ a})`).

All proved.
-/

namespace SubNLogN.Machine.BridgeExp

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability

/-! ## Binary encodings -/

theorem encodeNat_two_mul {n : ℕ} (hn : 1 ≤ n) : encodeNat (2 * n) = false :: encodeNat n := by
  rw [two_mul, encodeNat_add, if_neg]
  intro h
  rw [encodeNat_eq_nil_iff] at h
  omega

theorem encodeNat_pow_two : ∀ a : ℕ, encodeNat (2 ^ a) = List.replicate a false ++ [true]
  | 0 => by simpa [encodeNat_zero] using encodeNat_add_add_one 0
  | a + 1 => by
    rw [pow_succ, mul_comm, encodeNat_two_mul Nat.one_le_two_pow, encodeNat_pow_two a]
    simp [List.replicate_succ]

theorem natSyms_pow_two (a : ℕ) :
    natSyms (2 ^ a) = List.replicate a (Sym.bit false) ++ [Sym.bit true] := by
  rw [natSyms, encodeNat_pow_two]
  simp [List.map_replicate]

theorem natSyms_two_mul {n : ℕ} (hn : 1 ≤ n) : natSyms (2 * n) = Sym.bit false :: natSyms n := by
  rw [natSyms, encodeNat_two_mul hn]
  rfl

theorem natSyms_one : natSyms 1 = [Sym.bit true] := by
  simpa using natSyms_pow_two 0

/-! ## Loops over a state family -/

section Loop

variable {K σ' : Type} [DecidableEq K]

/-- **Loop over a state family.** If the test `c` of the top of `k` holds in the state `B n` iff
`n ≠ 0`, and one iteration `core` runs from `B (n+1)` to `B n`, then
`peekTop k ; loop c (core ; peekTop k)` runs from `B N` to `B 0`. -/
theorem runs_cond_loop (k : K) (c : Option Sym × σ' → Bool)
    (core : Prog K (fun _ => Sym) (Option Sym × σ')) (B : ℕ → K → List Sym) (N : ℕ) (T : ℕ → ℕ)
    (hc : ∀ (n : ℕ) (w : σ'), n ≤ N → c ((B n k).head?, w) = decide (n ≠ 0))
    (hstep : ∀ n, n + 1 ≤ N → Runs core (B (n + 1)) (B n) (fun _ => True) (T n)) :
    Runs (.seq (BridgeRed.peekTop k) (.loop c (.seq core (BridgeRed.peekTop k)))) (B N) (B 0)
      (fun _ => True) (1 + loopCost (fun n => T n + 1) N) := by
  let I : ℕ → St K (fun _ => Sym) (Option Sym × σ') → Prop := fun n s =>
    n ≤ N ∧ s.stk = B n ∧ s.var.1 = (B n k).head?
  have hloop := Triple.loop (ρ := []) (c := c) (I := I) (B := fun n => T n + 1)
    (p := .seq core (BridgeRed.peekTop k))
    (fun n => by
      intro s hs
      obtain ⟨hn, hstk, -⟩ := hs
      have h1 := hstep n hn
      have h2 := BridgeRed.runs_peekTop (σ' := σ') k (B n)
      have h12 := WP.W9comp.runs_seq h1 h2
      obtain ⟨s', t, e, ⟨hs', hq⟩, ht⟩ := h12 s hstk
      exact ⟨s', t, e, ⟨by omega, hs', hq⟩, ht⟩)
    (fun n s hs => by
      obtain ⟨hn, -, hv⟩ := hs
      have : s.var = (s.var.1, s.var.2) := rfl
      rw [this, hv, hc (n + 1) s.var.2 hn]
      simp)
    (fun s hs => by
      obtain ⟨-, -, hv⟩ := hs
      have : s.var = (s.var.1, s.var.2) := rfl
      rw [this, hv, hc 0 s.var.2 (Nat.zero_le _)]
      simp)
    N
  have hp := BridgeRed.runs_peekTop (σ' := σ') k (B N)
  intro s hs
  obtain ⟨s1, t1, e1, ⟨hs1, hv1⟩, ht1⟩ := hp s hs
  obtain ⟨s2, t2, e2, ⟨-, hs2, -⟩, ht2⟩ := hloop s1 ⟨le_refl N, hs1, hv1⟩
  exact ⟨s2, t1 + t2, Eval.seq e1 e2, ⟨hs2, trivial⟩, by omega⟩

/-- `loopCost` of a constant-bounded body. -/
theorem loopCost_le_mul (T : ℕ → ℕ) (M N : ℕ) (h : ∀ n, n < N → T n ≤ M) :
    loopCost T N ≤ N * (M + 1) + 1 := by
  rw [BridgeRed.loopCost_eq_sum]
  have : ((List.range N).map fun n => T n + 1).sum ≤ ((List.range N).map fun _ => M + 1).sum :=
    List.sum_le_sum (by
      intro n hn
      rw [List.mem_range] at hn
      exact Nat.add_le_add_right (h n hn) 1)
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul] at this
  omega

end Loop

/-! ## Flag-register programs inside a larger register -/

section Lift

variable {K σ' : Type} [DecidableEq K]

/-- A flag-register program (`SProg`) run on the first component of the register. -/
def lift (P : SProg K) : Prog K (fun _ => Sym) (Option Sym × σ') := callInj id (Lens.fst _ _) P

omit [DecidableEq K] in
theorem closed_lift {P : SProg K} (h : P.Closed) : (lift (σ' := σ') P).Closed :=
  closed_callInj id _ h

theorem runs_lift {P : SProg K} {S S' : K → List Sym} {Q : Option Sym → Prop} {T : ℕ}
    (h : Runs P S S' Q T) : Runs (lift (σ' := σ') P) S S' (fun _ => True) T :=
  runs_callInj Function.injective_id (Lens.fst _ _) h (fun k hk => absurd rfl (hk k))

end Lift

/-! ## Reading header fields in unary -/

section Fields

variable {K σ' : Type} [DecidableEq K]

/-- The loop test: the flag is the bit `0`. -/
def isZeroTop : Option Sym × σ' → Bool := fun v => decide (v.1 = some (Sym.bit false))

/-- Body of `countField`: move a zero bit and increment the counter. -/
def countStep (src dst cnt tmp : K) : Prog K (fun _ => Sym) (Option Sym × σ') :=
  lift (.seq (BridgePP.moveSym src dst) (inc cnt tmp))

/-- Move the header field `natSyms (2^a) ++ [mark]` from `src` to `dst` (reversed), adding `a` to
the counter on `cnt` (`tmp` restored). -/
def countField (src dst cnt tmp : K) : Prog K (fun _ => Sym) (Option Sym × σ') :=
  .seq (.seq (BridgeRed.peekTop src) (.loop isZeroTop (.seq (countStep src dst cnt tmp)
    (BridgeRed.peekTop src))))
    (lift (.seq (BridgePP.moveSym src dst) (BridgePP.moveSym src dst)))

/-- Body of `unaryField`: move a zero bit and push a zero bit on `g`. -/
def unaryStep (src dst g : K) : Prog K (fun _ => Sym) (Option Sym × σ') :=
  lift (.seq (BridgePP.moveSym src dst) (pushC g (Sym.bit false)))

/-- Move the header field `natSyms (2^a) ++ [mark]` from `src` to `dst` (reversed), pushing `a` zero
bits on `g`. -/
def unaryField (src dst g : K) : Prog K (fun _ => Sym) (Option Sym × σ') :=
  .seq (.seq (BridgeRed.peekTop src) (.loop isZeroTop (.seq (unaryStep src dst g)
    (BridgeRed.peekTop src))))
    (lift (.seq (BridgePP.moveSym src dst) (BridgePP.moveSym src dst)))

theorem closed_countField (src dst cnt tmp : K) :
    (countField (σ' := σ') src dst cnt tmp).Closed := by
  have h1 : (BridgePP.moveSym src dst).Closed := BridgePP.closed_moveSym src dst
  have h2 : (inc cnt tmp).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, inc, scanLoop, scanBody, incFix, moveBits, moveBitsBody,
      popR, pushR, pushC, restoreR, skip]
  have hc : (countStep (σ' := σ') src dst cnt tmp).Closed :=
    closed_lift (by simp only [Prog.Closed] at h1 h2 ⊢; exact ⟨h1, h2⟩)
  have hm : (lift (σ' := σ') (.seq (BridgePP.moveSym src dst) (BridgePP.moveSym src dst))).Closed :=
    closed_lift (by simp only [Prog.Closed] at h1 ⊢; exact ⟨h1, h1⟩)
  have hp := BridgeRed.closed_peekTop (σ' := σ') src
  simp only [countField, Prog.Closed] at hc hm hp ⊢
  exact ⟨⟨hp, hc, hp⟩, hm⟩

theorem closed_unaryField (src dst g : K) : (unaryField (σ' := σ') src dst g).Closed := by
  have h1 : (BridgePP.moveSym src dst).Closed := BridgePP.closed_moveSym src dst
  have h2 : (pushC g (Sym.bit false) : SProg K).Closed := by
    simp [Prog.Closed, Prog.FreeBelow, pushC]
  have hc : (unaryStep (σ' := σ') src dst g).Closed :=
    closed_lift (by simp only [Prog.Closed] at h1 h2 ⊢; exact ⟨h1, h2⟩)
  have hm : (lift (σ' := σ') (.seq (BridgePP.moveSym src dst) (BridgePP.moveSym src dst))).Closed :=
    closed_lift (by simp only [Prog.Closed] at h1 ⊢; exact ⟨h1, h1⟩)
  have hp := BridgeRed.closed_peekTop (σ' := σ') src
  simp only [unaryField, Prog.Closed] at hc hm hp ⊢
  exact ⟨⟨hp, hc, hp⟩, hm⟩

theorem replicate_bit_append (n : ℕ) (L : List Sym) :
    List.replicate (n + 1) (Sym.bit false) ++ L = Sym.bit false :: (List.replicate n (Sym.bit false) ++ L) := by
  rw [List.replicate_succ, List.cons_append]

theorem field_rev (a : ℕ) (D : List Sym) :
    (natSyms (2 ^ a) ++ [Sym.mark]).reverse ++ D =
      Sym.mark :: Sym.bit true :: (List.replicate a (Sym.bit false) ++ D) := by
  rw [natSyms_pow_two]
  simp

/-- **`countField`**: the field `natSyms (2^a) ++ [mark]` moves (reversed) from `src` to `dst` and
the counter `natSyms c` on `cnt` becomes `natSyms (c + a)`. -/
theorem runs_countField {src dst cnt tmp : K} (h1 : src ≠ dst) (h2 : src ≠ cnt) (h3 : src ≠ tmp)
    (h4 : dst ≠ cnt) (h5 : dst ≠ tmp) (h6 : cnt ≠ tmp)
    (a c : ℕ) (L tl : List Sym) (htl : TermOK tl) (S : K → List Sym)
    (hS : S src = natSyms (2 ^ a) ++ Sym.mark :: L) (hC : S cnt = natSyms c ++ tl) :
    Runs (countField (σ' := σ') src dst cnt tmp) S
      (Function.update (Function.update (Function.update S src L) dst
        ((natSyms (2 ^ a) ++ [Sym.mark]).reverse ++ S dst)) cnt (natSyms (c + a) ++ tl))
      (fun _ => True) ((a + 1) * (6 * (c + a) + 20)) := by
  set B : ℕ → K → List Sym := fun n => Function.update (Function.update (Function.update S src
    (List.replicate n (Sym.bit false) ++ Sym.bit true :: Sym.mark :: L)) dst
    (List.replicate (a - n) (Sym.bit false) ++ S dst)) cnt (natSyms (c + (a - n)) ++ tl) with hB
  have hBa : B a = S := by
    funext k
    simp only [hB, Function.update_apply]
    split_ifs with e1 e2 e3
    · subst e1; rw [hC, Nat.sub_self, Nat.add_zero]
    · subst e2; simp
    · subst e3; rw [hS, natSyms_pow_two]; simp
    · rfl
  have hcond : ∀ (n : ℕ) (w : σ'), n ≤ a → isZeroTop ((B n src).head?, w) = decide (n ≠ 0) := by
    intro n w _
    simp only [hB, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self]
    rcases n with _ | n
    · simp [isZeroTop]
    · simp [isZeroTop, List.replicate_succ]
  have hstep : ∀ n, n + 1 ≤ a → Runs (countStep (σ' := σ') src dst cnt tmp) (B (n + 1)) (B n)
      (fun _ => True) (6 * (c + a) + 11) := by
    intro n hn
    have hs1 : B (n + 1) src = Sym.bit false ::
        (List.replicate n (Sym.bit false) ++ Sym.bit true :: Sym.mark :: L) := by
      simp only [hB, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self,
        replicate_bit_append]
    have r1 := BridgePP.runs_moveSym h1 _ _ (B (n + 1)) hs1
    have hs2 : Function.update (Function.update (B (n + 1)) src
        (List.replicate n (Sym.bit false) ++ Sym.bit true :: Sym.mark :: L)) dst
        (Sym.bit false :: B (n + 1) dst) cnt = natSyms (c + (a - (n + 1))) ++ tl := by
      simp only [hB, Function.update_of_ne h4.symm, Function.update_of_ne h2.symm,
        Function.update_self]
    have r2 := WP.W9mp.runs_inc h6 (c + (a - (n + 1))) tl _ htl hs2
    have r12 := WP.W9comp.runs_seq r1 r2
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (runs_lift r12) ?_) (fun _ _ => trivial) ?_
    · funext k
      simp only [hB, Function.update_apply]
      split_ifs <;> simp_all <;> first
        | (congr 1; omega)
        | (rw [show a - n = (a - (n + 1)) + 1 by omega, List.replicate_succ, List.cons_append])
    · omega
  have hloop := runs_cond_loop src isZeroTop (countStep (σ' := σ') src dst cnt tmp) B a
    (fun _ => 6 * (c + a) + 11) hcond hstep
  rw [hBa] at hloop
  have hB0src : B 0 src = Sym.bit true :: Sym.mark :: L := by
    simp only [hB, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self]
    simp
  have r3 := BridgePP.runs_moveSym h1 _ _ (B 0) hB0src
  have r4 := BridgePP.runs_moveSym h1 Sym.mark L
    (Function.update (Function.update (B 0) src (Sym.mark :: L)) dst (Sym.bit true :: B 0 dst))
    (by rw [Function.update_of_ne h1, Function.update_self])
  have r34 := runs_lift (σ' := σ') (WP.W9comp.runs_seq r3 r4)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq hloop r34) ?_)
    (fun _ _ => trivial) ?_
  · funext k
    simp only [hB, Function.update_apply]
    split_ifs <;> simp_all [natSyms_pow_two]
  · have hlc := loopCost_le_mul (fun n => 6 * (c + a) + 11 + 1) (6 * (c + a) + 12) a
      (fun _ _ => le_refl _)
    nlinarith

/-- **`unaryField`**: the field `natSyms (2^a) ++ [mark]` moves (reversed) from `src` to `dst` and
`a` zero bits are pushed on `g`. -/
theorem runs_unaryField {src dst g : K} (h1 : src ≠ dst) (h2 : src ≠ g) (h4 : dst ≠ g)
    (a : ℕ) (L : List Sym) (S : K → List Sym) (hS : S src = natSyms (2 ^ a) ++ Sym.mark :: L) :
    Runs (unaryField (σ' := σ') src dst g) S
      (Function.update (Function.update (Function.update S src L) dst
        ((natSyms (2 ^ a) ++ [Sym.mark]).reverse ++ S dst)) g
        (List.replicate a (Sym.bit false) ++ S g))
      (fun _ => True) (8 * a + 8) := by
  set B : ℕ → K → List Sym := fun n => Function.update (Function.update (Function.update S src
    (List.replicate n (Sym.bit false) ++ Sym.bit true :: Sym.mark :: L)) dst
    (List.replicate (a - n) (Sym.bit false) ++ S dst)) g
    (List.replicate (a - n) (Sym.bit false) ++ S g) with hB
  have hBa : B a = S := by
    funext k
    simp only [hB, Function.update_apply]
    split_ifs with e1 e2 e3
    · subst e1; simp
    · subst e2; simp
    · subst e3; rw [hS, natSyms_pow_two]; simp
    · rfl
  have hcond : ∀ (n : ℕ) (w : σ'), n ≤ a → isZeroTop ((B n src).head?, w) = decide (n ≠ 0) := by
    intro n w _
    simp only [hB, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self]
    rcases n with _ | n
    · simp [isZeroTop]
    · simp [isZeroTop, List.replicate_succ]
  have hstep : ∀ n, n + 1 ≤ a → Runs (unaryStep (σ' := σ') src dst g) (B (n + 1)) (B n)
      (fun _ => True) 3 := by
    intro n hn
    have hs1 : B (n + 1) src = Sym.bit false ::
        (List.replicate n (Sym.bit false) ++ Sym.bit true :: Sym.mark :: L) := by
      simp only [hB, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self,
        replicate_bit_append]
    have r1 := BridgePP.runs_moveSym h1 _ _ (B (n + 1)) hs1
    have r2 := BridgePP.runs_pushC g (Sym.bit false) (Function.update (Function.update (B (n + 1))
      src (List.replicate n (Sym.bit false) ++ Sym.bit true :: Sym.mark :: L)) dst
      (Sym.bit false :: B (n + 1) dst))
    have r12 := WP.W9comp.runs_seq r1 r2
    refine WP.W9comp.runs_congr (runs_lift r12) ?_
    funext k
    simp only [hB, Function.update_apply]
    split_ifs <;> simp_all <;>
      rw [show a - n = (a - (n + 1)) + 1 by omega, List.replicate_succ, List.cons_append]
  have hloop := runs_cond_loop src isZeroTop (unaryStep (σ' := σ') src dst g) B a
    (fun _ => 3) hcond hstep
  rw [hBa] at hloop
  have hB0src : B 0 src = Sym.bit true :: Sym.mark :: L := by
    simp only [hB, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self]
    simp
  have r3 := BridgePP.runs_moveSym h1 _ _ (B 0) hB0src
  have r4 := BridgePP.runs_moveSym h1 Sym.mark L
    (Function.update (Function.update (B 0) src (Sym.mark :: L)) dst (Sym.bit true :: B 0 dst))
    (by rw [Function.update_of_ne h1, Function.update_self])
  have r34 := runs_lift (σ' := σ') (WP.W9comp.runs_seq r3 r4)
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq hloop r34) ?_)
    (fun _ _ => trivial) ?_
  · funext k
    simp only [hB, Function.update_apply]
    split_ifs <;> simp_all [natSyms_pow_two]
  · have hlc := loopCost_le_mul (fun _ => 3 + 1) 4 a (fun _ _ => le_refl _)
    omega

end Fields

/-! ## Counted loops over header fields -/

section CLoops

variable {K σ' : Type} [DecidableEq K]

theorem bitLen_le_of_le {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat, IntMulTM.length_encodeNat]
  exact Nat.size_le_size h

theorem hdrSyms_nil : hdrSyms ([] : List ℕ) = [] := rfl

theorem hdrSyms_cons' (a : ℕ) (fs : List ℕ) :
    hdrSyms (a :: fs) = natSyms a ++ Sym.mark :: hdrSyms fs := BridgePP.hdrSyms_cons a fs

theorem hdrSyms_append' (fs gs : List ℕ) : hdrSyms (fs ++ gs) = hdrSyms fs ++ hdrSyms gs :=
  BridgePP.hdrSyms_append fs gs

/-- Skip the header fields counted by the bare counter `I`, decrementing the bare counter `D` once
per field. -/
def skipLoop (par T I D tmp : K) : Prog K (fun _ => Sym) (Option Sym × σ') :=
  .seq (BridgeRed.peekTop I) (.loop BridgeRed.topIsBit (.seq
    (lift (.seq (BridgePP.skipField par T) (.seq (BridgePP.decIfPos D tmp)
      (BridgePP.decIfPos I tmp)))) (BridgeRed.peekTop I)))

theorem closed_skipLoop (par T I D tmp : K) : (skipLoop (σ' := σ') par T I D tmp).Closed := by
  have h1 : (BridgePP.skipField par T).Closed := BridgePP.closed_skipFields par T 1 |>.1
  have h2 := BridgePP.closed_decIfPos D tmp
  have h3 := BridgePP.closed_decIfPos I tmp
  have hb : (lift (σ' := σ') (.seq (BridgePP.skipField par T) (.seq (BridgePP.decIfPos D tmp)
      (BridgePP.decIfPos I tmp)))).Closed :=
    closed_lift (by simp only [Prog.Closed] at h1 h2 h3 ⊢; exact ⟨h1, h2, h3⟩)
  have hp := BridgeRed.closed_peekTop (σ' := σ') I
  simp only [skipLoop, Prog.Closed] at hb hp ⊢
  exact ⟨hp, hb, hp⟩

theorem runs_skipLoop {par T I D tmp : K} (hpT : par ≠ T) (hpI : par ≠ I) (hpD : par ≠ D)
    (hptmp : par ≠ tmp) (hTI : T ≠ I) (hTD : T ≠ D) (hTtmp : T ≠ tmp) (hID : I ≠ D)
    (hItmp : I ≠ tmp) (hDtmp : D ≠ tmp)
    (fs gs : List ℕ) (D0 H : ℕ) (rpar : List Sym) (S : K → List Sym)
    (hpar : S par = hdrSyms (fs ++ gs) ++ rpar) (hI : S I = natSyms fs.length)
    (hD : S D = natSyms D0) (hH : ∀ f ∈ fs, bitLen f ≤ H) (hHD : bitLen D0 ≤ H)
    (hHI : bitLen fs.length ≤ H) :
    Runs (skipLoop (σ' := σ') par T I D tmp) S
      (Function.update (Function.update (Function.update (Function.update S par
        (hdrSyms gs ++ rpar)) T ((hdrSyms fs).reverse ++ S T)) I []) D (natSyms (D0 - fs.length)))
      (fun _ => True) (fs.length * (19 * H + 30) + 2) := by
  set B : ℕ → K → List Sym := fun n => Function.update (Function.update (Function.update
    (Function.update S par (hdrSyms (fs.drop (fs.length - n) ++ gs) ++ rpar))
    T ((hdrSyms (fs.take (fs.length - n))).reverse ++ S T)) I (natSyms n))
    D (natSyms (D0 - (fs.length - n))) with hB
  have hBN : B fs.length = S := by
    funext k
    simp only [hB, Function.update_apply, Nat.sub_self, List.drop_zero, List.take_zero,
      Nat.sub_zero, hdrSyms_nil, List.reverse_nil, List.nil_append]
    split_ifs with e1 e2 e3 e4
    · subst e1; exact hD.symm
    · subst e2; exact hI.symm
    · subst e3; rfl
    · subst e4; exact hpar.symm
    · rfl
  have hcond : ∀ (n : ℕ) (w : σ'), n ≤ fs.length →
      BridgeRed.topIsBit ((B n I).head?, w) = decide (n ≠ 0) := by
    intro n w _
    simp only [hB, Function.update_of_ne hID, Function.update_self]
    exact BridgeRed.topIsBit_natSyms n w
  have hstep : ∀ n, n + 1 ≤ fs.length → Runs (lift (σ' := σ') (.seq (BridgePP.skipField par T)
      (.seq (BridgePP.decIfPos D tmp) (BridgePP.decIfPos I tmp)))) (B (n + 1)) (B n)
      (fun _ => True) (19 * H + 26) := by
    intro n hn
    have hk'lt : fs.length - (n + 1) < fs.length := by omega
    have hkk : fs.length - n = fs.length - (n + 1) + 1 := by omega
    have hpar1 : B (n + 1) par = natSyms fs[fs.length - (n + 1)] ++ Sym.mark ::
        (hdrSyms (fs.drop (fs.length - (n + 1) + 1) ++ gs) ++ rpar) := by
      simp only [hB, Function.update_of_ne hpD, Function.update_of_ne hpI,
        Function.update_of_ne hpT, Function.update_self]
      rw [List.drop_eq_getElem_cons hk'lt, List.cons_append, hdrSyms_cons', List.append_assoc,
        List.cons_append]
    have r1 := BridgePP.runs_skipField hpT fs[fs.length - (n + 1)] _ (B (n + 1)) hpar1
    set S1 := Function.update (Function.update (B (n + 1)) par
      (hdrSyms (fs.drop (fs.length - (n + 1) + 1) ++ gs) ++ rpar)) T
      ((natSyms fs[fs.length - (n + 1)] ++ [Sym.mark]).reverse ++ B (n + 1) T) with hS1
    have hS1D : S1 D = natSyms (D0 - (fs.length - (n + 1))) ++ [] := by
      simp only [hS1, hB, Function.update_of_ne hTD.symm, Function.update_of_ne hpD.symm,
        Function.update_self, List.append_nil]
    have r2 := BridgePP.runs_decIfPos hDtmp (D0 - (fs.length - (n + 1))) [] S1 TermOK.nil hS1D
    set S2 := Function.update S1 D (natSyms (D0 - (fs.length - (n + 1)) - 1) ++ []) with hS2
    have hS2I : S2 I = natSyms (n + 1) ++ [] := by
      simp only [hS2, hS1, hB, Function.update_of_ne hID, Function.update_of_ne hTI.symm,
        Function.update_of_ne hpI.symm, Function.update_self, List.append_nil]
    have r3 := BridgePP.runs_decIfPos hItmp (n + 1) [] S2 TermOK.nil hS2I
    have r123 := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 r3)
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (runs_lift r123) ?_)
      (fun _ _ => trivial) ?_
    · funext k
      by_cases hkI : k = I
      · rw [hkI]
        simp only [hB, Function.update_self, Function.update_of_ne hID, Nat.add_sub_cancel,
          List.append_nil]
      by_cases hkD : k = D
      · rw [hkD]
        simp only [hS2, hB, Function.update_self, Function.update_of_ne hID.symm,
          List.append_nil]
        congr 1
        omega
      by_cases hkT : k = T
      · rw [hkT]
        simp only [hS2, hS1, hB, Function.update_self, Function.update_of_ne hTI,
          Function.update_of_ne hTD]
        rw [hkk, List.take_succ_eq_append_getElem hk'lt]
        simp only [List.map_append, List.map_cons, List.map_nil, hdrSyms_append', hdrSyms_cons',
          hdrSyms_nil, List.reverse_append, List.append_assoc]
      by_cases hkp : k = par
      · rw [hkp]
        simp only [hS2, hS1, hB, Function.update_self, Function.update_of_ne hpI,
          Function.update_of_ne hpD, Function.update_of_ne hpT, hkk]
      · simp only [hS2, hS1, hB, Function.update_of_ne hkI, Function.update_of_ne hkD,
          Function.update_of_ne hkT, Function.update_of_ne hkp]
    · have hf : bitLen fs[fs.length - (n + 1)] ≤ H := hH _ (List.getElem_mem hk'lt)
      have hd : bitLen (D0 - (fs.length - (n + 1))) ≤ H :=
        le_trans (bitLen_le_of_le (Nat.sub_le _ _)) hHD
      have hi : bitLen (n + 1) ≤ H := le_trans (bitLen_le_of_le hn) hHI
      omega
  have hloop := runs_cond_loop I BridgeRed.topIsBit _ B fs.length (fun _ => 19 * H + 26) hcond
    hstep
  rw [hBN] at hloop
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hloop ?_) (fun _ _ => trivial) ?_
  · funext k
    simp only [hB, Function.update_apply, Nat.sub_zero, List.drop_length, List.take_length,
      List.nil_append]
    split_ifs <;> simp_all [natSyms, encodeNat_zero]
  · have := loopCost_le_mul (fun _ => 19 * H + 26 + 1) (19 * H + 27) fs.length
      (fun _ _ => le_refl _)
    nlinarith

/-- Read the fields counted by the bare counter `D` in unary onto `g` (one zero bit per zero bit
of every field). -/
def unaryLoop (par T D g tmp : K) : Prog K (fun _ => Sym) (Option Sym × σ') :=
  .seq (BridgeRed.peekTop D) (.loop BridgeRed.topIsBit (.seq
    (.seq (unaryField par T g) (lift (BridgePP.decIfPos D tmp))) (BridgeRed.peekTop D)))

theorem closed_unaryLoop (par T D g tmp : K) : (unaryLoop (σ' := σ') par T D g tmp).Closed := by
  have h1 := closed_unaryField (σ' := σ') par T g
  have h2 : (lift (σ' := σ') (BridgePP.decIfPos D tmp)).Closed :=
    closed_lift (BridgePP.closed_decIfPos D tmp)
  have hp := BridgeRed.closed_peekTop (σ' := σ') D
  simp only [unaryLoop, Prog.Closed] at h1 h2 hp ⊢
  exact ⟨hp, ⟨h1, h2⟩, hp⟩

theorem runs_unaryLoop {par T D g tmp : K} (hpT : par ≠ T) (hpD : par ≠ D) (hpg : par ≠ g)
    (hptmp : par ≠ tmp) (hTD : T ≠ D) (hTg : T ≠ g) (hTtmp : T ≠ tmp) (hDg : D ≠ g)
    (hDtmp : D ≠ tmp) (hgtmp : g ≠ tmp)
    (es : List ℕ) (gs : List ℕ) (H : ℕ) (rpar : List Sym) (S : K → List Sym)
    (hpar : S par = hdrSyms (es.map (2 ^ ·) ++ gs) ++ rpar) (hD : S D = natSyms es.length)
    (hH : ∀ e ∈ es, e ≤ H) (hHD : bitLen es.length ≤ H) :
    Runs (unaryLoop (σ' := σ') par T D g tmp) S
      (Function.update (Function.update (Function.update (Function.update S par
        (hdrSyms gs ++ rpar)) T ((hdrSyms (es.map (2 ^ ·))).reverse ++ S T)) D [])
        g (List.replicate es.sum (Sym.bit false) ++ S g))
      (fun _ => True) (es.length * (16 * H + 30) + 2) := by
  set B : ℕ → K → List Sym := fun n => Function.update (Function.update (Function.update
    (Function.update S par (hdrSyms ((es.drop (es.length - n)).map (2 ^ ·) ++ gs) ++ rpar))
    T ((hdrSyms ((es.take (es.length - n)).map (2 ^ ·))).reverse ++ S T)) D (natSyms n))
    g (List.replicate (es.take (es.length - n)).sum (Sym.bit false) ++ S g) with hB
  have hBN : B es.length = S := by
    funext k
    simp only [hB, Function.update_apply, Nat.sub_self, List.drop_zero, List.take_zero,
      List.map_nil, hdrSyms_nil, List.reverse_nil, List.nil_append, List.sum_nil,
      List.replicate_zero]
    split_ifs with e1 e2 e3 e4
    · subst e1; rfl
    · subst e2; exact hD.symm
    · subst e3; rfl
    · subst e4; exact hpar.symm
    · rfl
  have hcond : ∀ (n : ℕ) (w : σ'), n ≤ es.length →
      BridgeRed.topIsBit ((B n D).head?, w) = decide (n ≠ 0) := by
    intro n w _
    simp only [hB, Function.update_of_ne hDg, Function.update_self]
    exact BridgeRed.topIsBit_natSyms n w
  have hstep : ∀ n, n + 1 ≤ es.length → Runs (.seq (unaryField (σ' := σ') par T g)
      (lift (BridgePP.decIfPos D tmp))) (B (n + 1)) (B n) (fun _ => True) (16 * H + 26) := by
    intro n hn
    have hk'lt : es.length - (n + 1) < es.length := by omega
    have hkk : es.length - n = es.length - (n + 1) + 1 := by omega
    have hpar1 : B (n + 1) par = natSyms (2 ^ es[es.length - (n + 1)]) ++ Sym.mark ::
        (hdrSyms ((es.drop (es.length - (n + 1) + 1)).map (2 ^ ·) ++ gs) ++ rpar) := by
      simp only [hB, Function.update_of_ne hpg, Function.update_of_ne hpD,
        Function.update_of_ne hpT, Function.update_self]
      rw [List.drop_eq_getElem_cons hk'lt, List.map_cons, List.cons_append, hdrSyms_cons',
        List.append_assoc, List.cons_append]
    have r1 := runs_unaryField (σ' := σ') hpT hpg hTg es[es.length - (n + 1)] _ (B (n + 1)) hpar1
    set S1 := Function.update (Function.update (Function.update (B (n + 1)) par
      (hdrSyms ((es.drop (es.length - (n + 1) + 1)).map (2 ^ ·) ++ gs) ++ rpar)) T
      ((natSyms (2 ^ es[es.length - (n + 1)]) ++ [Sym.mark]).reverse ++ B (n + 1) T)) g
      (List.replicate es[es.length - (n + 1)] (Sym.bit false) ++ B (n + 1) g) with hS1
    have hS1D : S1 D = natSyms (n + 1) ++ [] := by
      simp only [hS1, hB, Function.update_of_ne hDg, Function.update_of_ne hTD.symm,
        Function.update_of_ne hpD.symm, Function.update_self, List.append_nil]
    have r2 := runs_lift (σ' := σ') (BridgePP.runs_decIfPos hDtmp (n + 1) [] S1 TermOK.nil hS1D)
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r1 r2) ?_)
      (fun _ _ => trivial) ?_
    · have hcomm : ∀ (a b : ℕ) (x : Sym) (L : List Sym),
          List.replicate a x ++ (List.replicate b x ++ L) = List.replicate (b + a) x ++ L := by
        intro a b x L
        rw [← List.append_assoc, ← List.replicate_add, Nat.add_comm]
      funext k
      by_cases hkD : k = D
      · rw [hkD]
        simp only [hB, Function.update_self, Function.update_of_ne hDg, Nat.add_sub_cancel,
          List.append_nil]
      by_cases hkg : k = g
      · rw [hkg]
        simp only [hS1, hB, Function.update_self, Function.update_of_ne hDg.symm]
        rw [hcomm, hkk, List.take_succ_eq_append_getElem hk'lt, List.sum_append,
          List.sum_singleton]
      by_cases hkT : k = T
      · rw [hkT]
        simp only [hS1, hB, Function.update_self, Function.update_of_ne hTD,
          Function.update_of_ne hTg]
        rw [hkk, List.take_succ_eq_append_getElem hk'lt]
        simp only [List.map_append, List.map_cons, List.map_nil, hdrSyms_append', hdrSyms_cons',
          hdrSyms_nil, List.reverse_append, List.append_assoc]
      by_cases hkp : k = par
      · rw [hkp]
        simp only [hS1, hB, Function.update_self, Function.update_of_ne hpD,
          Function.update_of_ne hpg, Function.update_of_ne hpT, hkk]
      · simp only [hS1, hB, Function.update_of_ne hkD, Function.update_of_ne hkg,
          Function.update_of_ne hkT, Function.update_of_ne hkp]
    · have hf : es[es.length - (n + 1)] ≤ H := hH _ (List.getElem_mem hk'lt)
      have hi : bitLen (n + 1) ≤ H := le_trans (bitLen_le_of_le hn) hHD
      omega
  have hloop := runs_cond_loop D BridgeRed.topIsBit _ B es.length (fun _ => 16 * H + 26) hcond
    hstep
  rw [hBN] at hloop
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hloop ?_) (fun _ _ => trivial) ?_
  · funext k
    simp only [hB, Function.update_apply, Nat.sub_zero, List.drop_length, List.take_length,
      List.map_nil, List.nil_append]
    split_ifs <;> simp_all [natSyms, encodeNat_zero]
  · have := loopCost_le_mul (fun _ => 16 * H + 26 + 1) (16 * H + 27) es.length
      (fun _ _ => le_refl _)
    nlinarith

end CLoops

end SubNLogN.Machine.BridgeExp
