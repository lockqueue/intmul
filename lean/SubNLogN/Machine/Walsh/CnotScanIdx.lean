/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanShift

/-!
# `SubNLogN.Machine.Walsh.CnotScanIdx`: the record index of the address-dependent scans

Paper: Section 5.1 eq. (`eq:walsh-SU`) and Section 5.2 eq. (`eq:walsh-CZ`) (the diagonals `S_U` and `CZ` are
computed once per record from its address). Engine and hook shapes: `Walsh/CnotScanRec.lean`
(K3-LIFT's `recLoopS`, `KRSpec`, `IncSpec`).

## Plan
* The index of record `i` (address `cubeOfNat m i`) is kept on the stack `x` as
  `idxSyms m i = (bitsLE m i).map Sym.bit`: its `m` low bits, least significant on top, so the
  bit at depth `j` is `i.testBit j`, the address bit of position `m - 1 - j`.
* `incX`: ripple increment from the top (carry `c1`), the new bits pushed on `x2`, then `x2`
  drained back onto `x`; the counter wraps modulo `2^m` (`incBits_bitsLE`), so one cost bound
  `7m + 5` serves every record, including the call after the last one.
* `xInit`: `x := idxSyms m 0` (`m` zeros) from the header field `m` (`skipFields`,
  `unaryOfTop`, `drain`, then one `bit false` per unit).

**Scope (honest summary).** Programs and exact evaluation / `RunsR` lemmas (no `sorry`):
`incSpec_incX` (the engine's `IncSpec`), `runsR_xInit`. Helpers live in
`SubNLogN.Machine.WalshScanX`.
-/

namespace SubNLogN.Machine.WalshScanX

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine WalshLift
  SubNLogN.Machine.WalshScanAux

/-! ## The index and its increment (pure) -/

/-- The record index `i` on the stack `x`: its `m` low bits, least significant on top. -/
def idxSyms (m i : ℕ) : List Sym := (bitsLE m i).map Sym.bit

/-- Ripple increment of a little-endian bit list from carry `c` (the final carry is dropped). -/
def incBits : Bool → List Bool → List Bool
  | _, [] => []
  | c, b :: bs => xor b c :: incBits (b && c) bs

theorem length_incBits : ∀ (c : Bool) (bs : List Bool), (incBits c bs).length = bs.length
  | _, [] => rfl
  | c, b :: bs => by simp [incBits, length_incBits (b && c) bs]

theorem testBit_add_toNat (d : ℕ) (c : Bool) :
    (d + c.toNat).testBit 0 = xor (d.testBit 0) c ∧
      (d + c.toNat) / 2 = d / 2 + (d.testBit 0 && c).toNat := by
  rw [Nat.testBit_zero, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one d with h | h <;> cases c <;> simp [h] <;> omega

theorem incBits_bitsLE : ∀ (m d : ℕ) (c : Bool), incBits c (bitsLE m d) = bitsLE m (d + c.toNat)
  | 0, _, _ => rfl
  | m + 1, d, c => by
    rw [K1.bitsLE_succ, K1.bitsLE_succ, incBits, incBits_bitsLE m (d / 2) (d.testBit 0 && c),
      (testBit_add_toNat d c).1, (testBit_add_toNat d c).2]

theorem idxSyms_succ (m i : ℕ) : (incBits true (bitsLE m i)).map Sym.bit = idxSyms m (i + 1) := by
  rw [incBits_bitsLE]
  rfl

theorem bitsLE_zero (m : ℕ) : bitsLE m 0 = List.replicate m false := by
  simp [bitsLE, List.map_const']

theorem length_idxSyms (m i : ℕ) : (idxSyms m i).length = m := by
  simp [idxSyms, K1.length_bitsLE]

/-- `n mod 4` as an element of `Fin 4` (the unit exponents of the scans). -/
def fin4 (n : ℕ) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by decide)⟩

theorem val_fin4 (n : ℕ) : (fin4 n).val = n % 4 := rfl

theorem add_fin4_zero (k : Fin 4) : k + fin4 0 = k := by
  apply Fin.ext
  simp only [Fin.val_add, val_fin4]
  omega

/-! ## Programs -/

/-- Push `bit (t xor c1)` (the increment output bit). -/
def pushInc (k : SK) : EProg SK := .push k fun r => .bit (xor (optBit r.t) r.c1)

/-- `c1 := t ∧ c1` (the increment carry). -/
def setIncC : EProg SK := .load fun r => { r with c1 := optBit r.t && r.c1 }

/-- One increment step: push the output bit on `x2`, update the carry, pop the next bit. -/
def incStep : EProg SK := .seq (pushInc (.inr .x2)) (.seq setIncC (popT (.inr .x)))

/-- The index increment `x := idxSyms m (i + 1)` (modulo `2^m`), through `x2`. -/
def incX : EProg SK :=
  .seq (.load fun r => { r with c1 := true }) (.seq (popT (.inr .x))
    (.seq (.loop tSome incStep) ((drain (.inr .x2) (.inr .x)).liftRegs lT)))

/-- Push `bit false` on `dst` for every unit of `src` (emptied). -/
def zerosOf (src dst : SK) : EProg SK :=
  .seq (popT src) (.loop tSome (.seq (pushK dst (.bit false)) (popT src)))

/-- `x := idxSyms m 0` from the header field `m` (the header is restored). -/
def xInit : EProg SK :=
  .seq ((WalshCnot1.skipFields (.inl 1) (.inr .pk) 5).liftRegs lT)
  (.seq ((unaryOfTop (.inl 1) (.inr .n2) (.inr .n1) (.inr .u)).liftRegs lT)
  (.seq ((drain (.inr .pk) (.inl 1)).liftRegs lT)
    (zerosOf (.inr .n2) (.inr .x))))

theorem closed_incX : incX.Closed := by
  have hd := WP.W9comp.closed_liftRegs lT (closed_drain (.inr .x2 : SK) (.inr .x))
  simp only [Prog.Closed] at hd
  simp [Prog.Closed, Prog.FreeBelow, incX, incStep, pushInc, setIncC, popT, hd]

theorem closed_xInit : xInit.Closed := by
  unfold xInit
  exact WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (WalshCnot1.closed_skipFields _ _ 5))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_unaryOfTop _ _ _ _))
    (WP.W9comp.closed_seq (WP.W9comp.closed_liftRegs lT (closed_drain _ _))
      (by simp [Prog.Closed, Prog.FreeBelow, zerosOf, popT, pushK])))

/-! ## The increment: evaluation -/

theorem eval_pushInc (k : SK) (r : ER) (b : Bool) (ht : r.t = some (Sym.bit b))
    (S : SK → List Sym) :
    Eval [] (pushInc k) ⟨r, S⟩ ⟨r, Function.update S k (Sym.bit (xor b r.c1) :: S k)⟩ 1 := by
  have h := Eval.push [] k (fun r : ER => Sym.bit (xor (optBit r.t) r.c1)) r S
  simp only [ht, optBit_some_bit] at h
  exact h

theorem eval_setIncC (r : ER) (b : Bool) (ht : r.t = some (Sym.bit b)) (S : SK → List Sym) :
    Eval [] setIncC ⟨r, S⟩ ⟨{ r with c1 := b && r.c1 }, S⟩ 1 := by
  refine (Eval.load [] (fun r : ER => { r with c1 := optBit r.t && r.c1 }) r S).of_eq ?_ rfl
  simp [ht]

theorem incLoopX_eval : ∀ (bs : List Bool) (r : ER) (S : SK → List Sym),
    r.t = (bs.map Sym.bit).head? → S (.inr .x) = (bs.map Sym.bit).tail →
    ∃ r' : ER, Eval [] (.loop tSome incStep) ⟨r, S⟩
      ⟨r', Function.update (Function.update S (.inr .x) []) (.inr .x2)
        ((incBits r.c1 bs).reverse.map Sym.bit ++ S (.inr .x2))⟩ (4 * bs.length + 1) ∧
      r'.mu = r.mu ∧ r'.k = r.k
  | [], r, S, ht, hx => by
    have ht' : r.t = none := ht
    have hx' : S (.inr .x) = [] := hx
    refine ⟨r, (Eval.loop_false (by simp [tSome, ht'])).of_eq ?_ rfl, rfl, rfl⟩
    congr 1
    simp only [incBits, List.reverse_nil, List.map_nil, List.nil_append]
    rw [← hx', Function.update_eq_self, Function.update_eq_self]
  | b :: bs, r, S, ht, hx => by
    have ht' : r.t = some (Sym.bit b) := ht
    have hx' : S (.inr .x) = bs.map Sym.bit := hx
    have e1 := eval_pushInc (.inr .x2) r b ht' S
    set S1 := Function.update S (.inr .x2) (Sym.bit (xor b r.c1) :: S (.inr .x2)) with hS1
    have e2 := eval_setIncC r b ht' S1
    have e3 := eval_popT (.inr .x) { r with c1 := b && r.c1 } (bs.map Sym.bit) S1
      (by rw [hS1, Function.update_of_ne (by simp), hx'])
    obtain ⟨r', e4, hmu, hk⟩ := incLoopX_eval bs
      { { r with c1 := b && r.c1 } with t := (bs.map Sym.bit).head? }
      (Function.update S1 (.inr .x) (bs.map Sym.bit).tail) rfl (Function.update_self _ _ _)
    refine ⟨r', (Eval.loop_true (by simp [tSome, ht']) (Eval.seq e1 (Eval.seq e2 e3)) e4).of_eq
      ?_ (by simp only [List.length_cons]; omega), hmu, hk⟩
    clear e1 e2 e3 e4
    congr 1
    funext j
    simp only [hS1, Function.update_apply, incBits, List.reverse_cons, List.map_append,
      List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all

theorem incSpec_incX (m : ℕ) (stat : (SK → List Sym) → Prop)
    (hst : ∀ S, stat S → S (.inr .x2) = []) : IncSpec incX (idxSyms m) stat (7 * m + 5) := by
  intro i S r hx hS
  have hx2 := hst S hS
  have e1 := Eval.load [] (fun r : ER => { r with c1 := true }) r S
  have e2 := eval_popT (.inr .x) { r with c1 := true } (idxSyms m i) S hx
  obtain ⟨r3, e3, hmu3, -⟩ := incLoopX_eval (bitsLE m i)
    { { r with c1 := true } with t := (idxSyms m i).head? }
    (Function.update S (.inr .x) (idxSyms m i).tail) rfl (Function.update_self _ _ _)
  set S3 := Function.update (Function.update (Function.update S (.inr .x) (idxSyms m i).tail)
    (.inr .x) []) (.inr .x2) ((incBits true (bitsLE m i)).reverse.map Sym.bit ++
      Function.update S (.inr .x) (idxSyms m i).tail (.inr .x2)) with hS3
  have e4 := eval_drainE (src := (.inr .x2 : SK)) (dst := .inr .x) (by simp) r3
    ((incBits true (bitsLE m i)).reverse.map Sym.bit) S3 (by simp [hS3, hx2])
  refine ⟨{ r3 with t := none }, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ rfl,
    by simpa using hmu3, ?_⟩
  · clear e1 e2 e3 e4
    congr 1
    funext j
    by_cases h1 : j = .inr .x
    · subst h1
      simp [hS3, ← idxSyms_succ, List.map_reverse]
    · by_cases h2 : j = .inr .x2
      · subst h2
        simp [hS3, hx2]
      · simp [hS3, Function.update_of_ne h1, Function.update_of_ne h2]
  · simp only [List.length_reverse, List.length_map, length_incBits, K1.length_bitsLE]
    omega

/-! ## The initial index -/

theorem zerosOf_loop (src dst : SK) (hne : src ≠ dst) (A : ER → Prop)
    (hA : ∀ r v, A r → A { r with t := v }) :
    ∀ (n : ℕ) (r : ER) (S : SK → List Sym), A r → r.t = (List.replicate n uSym).head? →
      S src = (List.replicate n uSym).tail →
      ∃ r' : ER, Eval [] (.loop tSome (.seq (pushK dst (.bit false)) (popT src))) ⟨r, S⟩
        ⟨r', Function.update (Function.update S src []) dst
          (List.replicate n (Sym.bit false) ++ S dst)⟩ (3 * n + 1) ∧ A r'
  | 0, r, S, hr, ht, hs => by
    have ht' : r.t = none := ht
    have hs' : S src = [] := hs
    refine ⟨r, (Eval.loop_false (by simp [tSome, ht'])).of_eq ?_ rfl, hr⟩
    congr 1
    simp only [List.replicate_zero, List.nil_append]
    rw [← hs', Function.update_eq_self, Function.update_eq_self]
  | n + 1, r, S, hr, ht, hs => by
    have ht' : r.t = some uSym := by simpa [List.replicate_succ] using ht
    have hs' : S src = List.replicate n uSym := by simpa [List.replicate_succ] using hs
    have e1 := eval_pushK dst (Sym.bit false) r S
    set S1 := Function.update S dst (Sym.bit false :: S dst) with hS1
    have e2 := eval_popT src r (List.replicate n uSym) S1
      (by rw [hS1, Function.update_of_ne hne, hs'])
    obtain ⟨r', e3, hr'⟩ := zerosOf_loop src dst hne A hA n
      { r with t := (List.replicate n uSym).head? }
      (Function.update S1 src (List.replicate n uSym).tail) (hA r _ hr) rfl
      (Function.update_self _ _ _)
    refine ⟨r', (Eval.loop_true (by simp [tSome, ht']) (Eval.seq e1 e2) e3).of_eq ?_ (by omega),
      hr'⟩
    clear e1 e2 e3
    congr 1
    funext j
    simp only [hS1, Function.update_apply, List.replicate_succ', List.append_assoc,
      List.singleton_append]
    split_ifs <;> simp_all

theorem runsR_zerosOf (src dst : SK) (hne : src ≠ dst) (n : ℕ) (S : SK → List Sym)
    (hS : S src = List.replicate n uSym) (A : ER → Prop) (hA : ∀ r v, A r → A { r with t := v }) :
    RunsR (zerosOf src dst) S (Function.update (Function.update S src []) dst
      (List.replicate n (Sym.bit false) ++ S dst)) A A (3 * n + 2) := by
  intro r hr
  have e1 := eval_popT src r (List.replicate n uSym) S hS
  obtain ⟨r', e2, hr'⟩ := zerosOf_loop src dst hne A hA n
    { r with t := (List.replicate n uSym).head? }
    (Function.update S src (List.replicate n uSym).tail) (hA r _ hr) rfl
    (Function.update_self _ _ _)
  refine ⟨r', _, (Eval.seq e1 e2).of_eq ?_ rfl, hr', by omega⟩
  congr 1
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem sliceHdr_split (P d r w K m j₀ D nS ρ : ℕ) :
    sliceHdr P d r w K m j₀ D nS ρ = hdrSyms [P, d, r, w, K] ++ hdrSyms [m, j₀, D, nS, ρ] := by
  simp [sliceHdr, hdrSyms]

theorem runsR_xInit (P d r w K m j₀ D nS ρ : ℕ) (hrest : List Sym) (S : SK → List Sym)
    (hH : S (.inl 1) = sliceHdr P d r w K m j₀ D nS ρ ++ hrest)
    (hpk : S (.inr .pk) = []) (hn1 : S (.inr .n1) = []) (hn2 : S (.inr .n2) = [])
    (hu : S (.inr .u) = []) (hx : S (.inr .x) = [])
    (A : ER → Prop) (hA : ∀ r v, A r → A { r with t := v }) :
    RunsR xInit S (Function.update S (.inr .x) (idxSyms m 0)) A A
      (6 * (sliceHdr P d r w K m j₀ D nS ρ).length + 23 * m + 12) := by
  have hH' : S (.inl 1) = hdrSyms [P, d, r, w, K] ++ (natSyms m ++ Sym.mark ::
      (hdrSyms [j₀, D, nS, ρ] ++ hrest)) := by
    rw [hH]
    simp [sliceHdr, hdrSyms]
  have R := RunsR.seq (runsR_of_runs (runs_skipFields (src := (.inl 1 : SK)) (pk := .inr .pk)
      (by simp) (natSyms m ++ Sym.mark :: (hdrSyms [j₀, D, nS, ρ] ++ hrest)) [P, d, r, w, K] S
      hH') A hA)
    (RunsR.seq (runsR_of_runs (runs_unaryOfTop (src := (.inl 1 : SK)) (dst := .inr .n2)
      (bits := .inr .n1) (u := .inr .u) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) m (hdrSyms [j₀, D, nS, ρ] ++ hrest) _ (by simp) (by simp [hn1]) (by simp [hn2])
      (by simp [hu])) A hA)
    (RunsR.seq (runsR_of_runs (runs_drain (src := (.inr .pk : SK)) (dst := .inl 1) (by simp)
      ((hdrSyms [P, d, r, w, K]).reverse) _ (by simp [hpk])) A hA)
      (runsR_zerosOf (.inr .n2) (.inr .x) (by simp) m _ (by simp) A hA)))
  refine (R.congr ?_).mono (fun _ h => h) (fun _ h => h) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp [hH, sliceHdr, hdrSyms]
    · cases e <;> simp [hpk, hn1, hn2, hu, hx, idxSyms, bitsLE_zero]
  · have h1 : (hdrSyms [P, d, r, w, K]).length ≤ (sliceHdr P d r w K m j₀ D nS ρ).length := by
      rw [sliceHdr_split, List.length_append]
      omega
    simp only [List.length_reverse]
    omega

end SubNLogN.Machine.WalshScanX
