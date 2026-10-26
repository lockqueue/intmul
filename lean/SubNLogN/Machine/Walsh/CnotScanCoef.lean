/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanEngine

/-!
# `SubNLogN.Machine.Walsh.CnotScanCoef`: one coefficient of a CNOT-batch scan

Paper: Lemma 5.1 (`lem:walsh-select`), eq. (`eq:walsh-CZ`), and Proposition 5.5 (`prop:cnot-batch`). Plan: top of
`Walsh/CnotScanEngine.lean`.

**Scope (honest summary).** The scan kernels' stack layout `SK` and the per-coefficient program
`coefProg` with its exact evaluation lemma `coefProg_eval`: a coefficient `(a, b)` (two `W`-bit
fields, `W = n1 + n2`) is replaced by the fields `replicate n2 false ++ (rip2 …).take n1` of the
table `fieldSpec mu k`. No contract is proved here.
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine WalshLift

/-! ## Full walks (with the first template pop) -/

section FullWalks

variable {K : Type} [DecidableEq K]

theorem readWalk_eval {tk u src dst : K} (h1 : tk ≠ u) (h2 : tk ≠ src) (h3 : tk ≠ dst)
    (h4 : u ≠ src) (h5 : u ≠ dst) (h6 : src ≠ dst) (R : List Sym) (bs : List Bool) (r : ER)
    (S : K → List Sym) (hS : S tk = List.replicate bs.length uSym)
    (hX : S src = bs.map Sym.bit ++ R) :
    ∃ r' : ER, r'.k = r.k ∧ r'.mu = r.mu ∧ r'.c1 = r.c1 ∧ r'.c2 = r.c2 ∧
      Eval [] (readWalk tk u src dst) ⟨r, S⟩
        ⟨r', Function.update (Function.update (Function.update (Function.update S tk []) u
          (List.replicate bs.length uSym ++ S u)) src R) dst (bs.reverse.map Sym.bit ++ S dst)⟩
        (5 * bs.length + 2) := by
  have e1 := eval_popT tk r _ S hS
  obtain ⟨r', hk, hmu, hc1, hc2, e2⟩ := readWalk_loop_eval h1 h2 h3 h4 h5 h6 R bs
    { r with t := (List.replicate bs.length uSym).head? }
    (Function.update S tk (List.replicate bs.length uSym).tail) rfl (Function.update_self _ _ _)
    (by rw [Function.update_of_ne h2.symm, hX])
  refine ⟨r', hk, hmu, hc1, hc2, (Eval.seq e1 e2).of_eq ?_ (by omega)⟩
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem zWalk_eval {tk u o : K} (h1 : tk ≠ u) (h2 : tk ≠ o) (h3 : u ≠ o) (n : ℕ) (r : ER)
    (S : K → List Sym) (hS : S tk = List.replicate n uSym) :
    ∃ r' : ER, r'.k = r.k ∧ r'.mu = r.mu ∧ r'.c1 = r.c1 ∧ r'.c2 = r.c2 ∧
      Eval [] (zWalk tk u o) ⟨r, S⟩
        ⟨r', Function.update (Function.update (Function.update S tk []) u
          (List.replicate n uSym ++ S u)) o (List.replicate n (Sym.bit false) ++ S o)⟩
        (4 * n + 2) := by
  have e1 := eval_popT tk r _ S hS
  obtain ⟨r', hk, hmu, hc1, hc2, e2⟩ := zWalk_loop_eval h1 h2 h3 n
    { r with t := (List.replicate n uSym).head? }
    (Function.update S tk (List.replicate n uSym).tail) rfl (Function.update_self _ _ _)
  refine ⟨r', hk, hmu, hc1, hc2, (Eval.seq e1 e2).of_eq ?_ (by omega)⟩
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem dWalk_eval {tk u fa2 fb2 fa fb : K} (h1 : tk ≠ u) (h2 : tk ≠ fa2) (h3 : tk ≠ fb2)
    (h4 : tk ≠ fa) (h5 : tk ≠ fb) (h6 : u ≠ fa2) (h7 : u ≠ fb2) (h8 : u ≠ fa) (h9 : u ≠ fb)
    (h10 : fa2 ≠ fb2) (h11 : fa2 ≠ fa) (h12 : fa2 ≠ fb) (h13 : fb2 ≠ fa) (h14 : fb2 ≠ fb)
    (h15 : fa ≠ fb) (RA RB : List Sym) (xs ys : List Bool) (r : ER) (S : K → List Sym)
    (hlen : xs.length = ys.length) (hS : S tk = List.replicate xs.length uSym)
    (hA : S fa2 = xs.map Sym.bit ++ RA) (hB : S fb2 = ys.map Sym.bit ++ RB) :
    ∃ r' : ER, r'.k = r.k ∧ r'.mu = r.mu ∧ r'.c1 = r.c1 ∧ r'.c2 = r.c2 ∧
      Eval [] (dWalk tk u fa2 fb2 fa fb) ⟨r, S⟩
        ⟨r', Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update S tk []) u (List.replicate xs.length uSym ++ S u))
          fa2 RA) fb2 RB) fa (xs.reverse.map Sym.bit ++ S fa))
          fb (ys.reverse.map Sym.bit ++ S fb)⟩ (7 * xs.length + 2) := by
  have e1 := eval_popT tk r _ S hS
  obtain ⟨r', hk, hmu, hc1, hc2, e2⟩ := dWalk_loop_eval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    h13 h14 h15 RA RB xs ys { r with t := (List.replicate xs.length uSym).head? }
    (Function.update S tk (List.replicate xs.length uSym).tail) hlen rfl
    (Function.update_self _ _ _) (by rw [Function.update_of_ne h2.symm, hA])
    (by rw [Function.update_of_ne h3.symm, hB])
  refine ⟨r', hk, hmu, hc1, hc2, (Eval.seq e1 e2).of_eq ?_ (by omega)⟩
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem cWalk_eval (im : Bool) {tk u fa2 fb2 fa fb o : K} (h1 : tk ≠ u) (h2 : tk ≠ fa2)
    (h3 : tk ≠ fb2) (h4 : tk ≠ fa) (h5 : tk ≠ fb) (h6 : u ≠ fa2) (h7 : u ≠ fb2) (h8 : u ≠ fa)
    (h9 : u ≠ fb) (h10 : fa2 ≠ fb2) (h11 : fa2 ≠ fa) (h12 : fa2 ≠ fb) (h13 : fb2 ≠ fa)
    (h14 : fb2 ≠ fb) (h15 : fa ≠ fb) (ho1 : tk ≠ o) (ho2 : u ≠ o) (ho3 : fa2 ≠ o) (ho4 : fb2 ≠ o)
    (ho5 : fa ≠ o) (ho6 : fb ≠ o) (RA RB : List Sym) (xs ys : List Bool) (r : ER)
    (S : K → List Sym) (hlen : xs.length = ys.length) (hS : S tk = List.replicate xs.length uSym)
    (hA : S fa2 = xs.map Sym.bit ++ RA) (hB : S fb2 = ys.map Sym.bit ++ RB) :
    ∃ r' : ER, r'.k = r.k ∧ r'.mu = r.mu ∧
      Eval [] (cWalk im tk u fa2 fb2 fa fb o) ⟨r, S⟩
        ⟨r', Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update S tk []) u
          (List.replicate xs.length uSym ++ S u)) fa2 RA) fb2 RB)
          fa (xs.reverse.map Sym.bit ++ S fa)) fb (ys.reverse.map Sym.bit ++ S fb))
          o ((rip2 (fieldSpec r.mu r.k im).1.bitFn (sgnFn (fieldSpec r.mu r.k im).2) r.c1 r.c2
            xs ys).reverse.map Sym.bit ++ S o)⟩ (9 * xs.length + 2) := by
  have e1 := eval_popT tk r _ S hS
  obtain ⟨r', hk, hmu, e2⟩ := cWalk_loop_eval im h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 ho1 ho2 ho3 ho4 ho5 ho6 RA RB xs ys { r with t := (List.replicate xs.length uSym).head? }
    (Function.update S tk (List.replicate xs.length uSym).tail) hlen rfl
    (Function.update_self _ _ _) (by rw [Function.update_of_ne h2.symm, hA])
    (by rw [Function.update_of_ne h3.symm, hB])
  refine ⟨r', hk, hmu, (Eval.seq e1 e2).of_eq ?_ (by omega)⟩
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end FullWalks

/-! ## The scan kernels' stacks -/

/-- Private scratch stacks of the scan kernels: the templates `tz` (`e'` units), `tcc`
(`W - e'`), `td` (`e'`) and the walk buffer `u`; the coefficient buffers `fa`, `fb`, `fa2`, `fb2`;
the output buffer `o`; the record index `x` (most significant bit on top) and its temporary `x2`;
the U-vector `uv`, the unary pair list `pl`; the park `pk`, the copy temporary `tmp`; five
setup stacks `n1`-`n5`. -/
inductive SS : Type
  | tz | tcc | td | u | fa | fb | fa2 | fb2 | o | x | x2 | uv | pl | pk | tmp
  | n1 | n2 | n3 | n4 | n5
  deriving DecidableEq

instance : Fintype SS where
  elems := {.tz, .tcc, .td, .u, .fa, .fb, .fa2, .fb2, .o, .x, .x2, .uv, .pl, .pk, .tmp,
    .n1, .n2, .n3, .n4, .n5}
  complete := by intro e; cases e <;> simp

/-- Stacks of the scan kernels: `.inl 0` the array, `.inl 1` the slice header, `.inl 2` the
pairs. -/
abbrev SK : Type := KLoc (Fin 3) SS

/-- Reset the carries. -/
def resetC : EProg SK := .load fun r => { r with c1 := false, c2 := false }

/-- One output field (`im` false: real part). -/
def outField (im : Bool) : EProg SK :=
  .seq resetC (.seq (zWalk (.inr .tz) (.inr .u) (.inr .o))
  (.seq ((drain (.inr .u) (.inr .tz)).liftRegs lT)
  (.seq (cWalk im (.inr .tcc) (.inr .u) (.inr .fa2) (.inr .fb2) (.inr .fa) (.inr .fb) (.inr .o))
  (.seq ((drain (.inr .u) (.inr .tcc)).liftRegs lT)
  (.seq (dWalk (.inr .td) (.inr .u) (.inr .fa2) (.inr .fb2) (.inr .fa) (.inr .fb))
    ((drain (.inr .u) (.inr .td)).liftRegs lT))))))

/-- Read one field of `W = n1 + n2` bits from the array into `dst`. -/
def readField (dst : SS) : EProg SK :=
  .seq (readWalk (.inr .tcc) (.inr .u) (.inl 0) (.inr dst))
  (.seq ((drain (.inr .u) (.inr .tcc)).liftRegs lT)
  (.seq (readWalk (.inr .td) (.inr .u) (.inl 0) (.inr dst))
    ((drain (.inr .u) (.inr .td)).liftRegs lT)))

/-- One coefficient: read both fields, emit both output fields, clear the buffers. -/
def coefProg : EProg SK :=
  .seq (readField .fa) (.seq (readField .fb)
  (.seq ((drain (.inr .fa) (.inr .fa2)).liftRegs lT) (.seq ((drain (.inr .fb) (.inr .fb2)).liftRegs lT)
  (.seq (outField false)
  (.seq ((drain (.inr .fa) (.inr .fa2)).liftRegs lT) (.seq ((drain (.inr .fb) (.inr .fb2)).liftRegs lT)
  (.seq (outField true)
  (.seq ((clear (.inr .fa)).liftRegs lT) ((clear (.inr .fb)).liftRegs lT)))))))))


/-! ## `Runs` with register pre/postconditions -/

section RunsR

variable {K : Type} [DecidableEq K]

/-- From every register satisfying `pre` and stacks `S`, reach stacks exactly `S'` with a
register satisfying `post`, within `T` steps. -/
def RunsR (P : EProg K) (S S' : K → List Sym) (pre post : ER → Prop) (T : ℕ) : Prop :=
  ∀ r : ER, pre r → ∃ r' t, Eval [] P ⟨r, S⟩ ⟨r', S'⟩ t ∧ post r' ∧ t ≤ T

theorem RunsR.seq {P Q : EProg K} {S1 S2 S3 : K → List Sym} {A B C : ER → Prop} {T1 T2 : ℕ}
    (h1 : RunsR P S1 S2 A B T1) (h2 : RunsR Q S2 S3 B C T2) :
    RunsR (.seq P Q) S1 S3 A C (T1 + T2) := by
  intro r hr
  obtain ⟨r1, t1, e1, hr1, ht1⟩ := h1 r hr
  obtain ⟨r2, t2, e2, hr2, ht2⟩ := h2 r1 hr1
  exact ⟨r2, t1 + t2, Eval.seq e1 e2, hr2, by omega⟩

theorem RunsR.congr {P : EProg K} {S S' S'' : K → List Sym} {A B : ER → Prop} {T : ℕ}
    (h : RunsR P S S' A B T) (he : S' = S'') : RunsR P S S'' A B T := he ▸ h

theorem RunsR.mono {P : EProg K} {S S' : K → List Sym} {A A' B B' : ER → Prop} {T T' : ℕ}
    (h : RunsR P S S' A B T) (hA : ∀ r, A' r → A r) (hB : ∀ r, B r → B' r) (hT : T ≤ T') :
    RunsR P S S' A' B' T' := by
  intro r hr
  obtain ⟨r', t, e, hr', ht⟩ := h r (hA r hr)
  exact ⟨r', t, e, hB r' hr', by omega⟩

/-- The register predicate "unit exponent `k`, flag `mu`". -/
def KM (k : Fin 4) (mu : Bool) (r : ER) : Prop := r.k = k ∧ r.mu = mu

/-- `KM` with both carries cleared. -/
def KMC (k : Fin 4) (mu : Bool) (r : ER) : Prop := r.k = k ∧ r.mu = mu ∧ r.c1 = false ∧ r.c2 = false

theorem runsR_drainE {src dst : K} (hne : src ≠ dst) (L : List Sym) (S : K → List Sym)
    (hS : S src = L) (P : ER → Prop) (hP : ∀ r, P r → P { r with t := none }) :
    RunsR ((drain src dst).liftRegs lT) S
      (Function.update (Function.update S src []) dst (L.reverse ++ S dst)) P P
      (3 * L.length + 2) :=
  fun r hr => ⟨_, _, eval_drainE hne r L S hS, hP r hr, le_rfl⟩

theorem runsR_clearE (k : K) (L : List Sym) (S : K → List Sym) (hS : S k = L)
    (P : ER → Prop) (hP : ∀ r, P r → P { r with t := none }) :
    RunsR ((clear k).liftRegs lT) S (Function.update S k []) P P (2 * L.length + 2) :=
  fun r hr => ⟨_, _, eval_clearE k r L S hS, hP r hr, le_rfl⟩

theorem KM_t (k : Fin 4) (mu : Bool) : ∀ r, KM k mu r → KM k mu { r with t := none } :=
  fun _ h => h

theorem KMC_t (k : Fin 4) (mu : Bool) : ∀ r, KMC k mu r → KMC k mu { r with t := none } :=
  fun _ h => h

theorem runsR_readWalk {tk u src dst : K} (h1 : tk ≠ u) (h2 : tk ≠ src) (h3 : tk ≠ dst)
    (h4 : u ≠ src) (h5 : u ≠ dst) (h6 : src ≠ dst) (R : List Sym) (bs : List Bool)
    (S : K → List Sym) (hS : S tk = List.replicate bs.length uSym)
    (hX : S src = bs.map Sym.bit ++ R) (k : Fin 4) (mu : Bool) :
    RunsR (readWalk tk u src dst) S
      (Function.update (Function.update (Function.update (Function.update S tk []) u
        (List.replicate bs.length uSym ++ S u)) src R) dst (bs.reverse.map Sym.bit ++ S dst))
      (KM k mu) (KM k mu) (5 * bs.length + 2) := by
  rintro r ⟨hk, hmu⟩
  obtain ⟨r', hk', hmu', -, -, e⟩ := readWalk_eval h1 h2 h3 h4 h5 h6 R bs r S hS hX
  exact ⟨r', _, e, ⟨hk'.trans hk, hmu'.trans hmu⟩, le_rfl⟩

theorem runsR_zWalk {tk u o : K} (h1 : tk ≠ u) (h2 : tk ≠ o) (h3 : u ≠ o) (n : ℕ)
    (S : K → List Sym) (hS : S tk = List.replicate n uSym) (k : Fin 4) (mu : Bool) :
    RunsR (zWalk tk u o) S
      (Function.update (Function.update (Function.update S tk []) u
        (List.replicate n uSym ++ S u)) o (List.replicate n (Sym.bit false) ++ S o))
      (KMC k mu) (KMC k mu) (4 * n + 2) := by
  rintro r ⟨hk, hmu, hc1, hc2⟩
  obtain ⟨r', hk', hmu', hc1', hc2', e⟩ := zWalk_eval h1 h2 h3 n r S hS
  exact ⟨r', _, e, ⟨hk'.trans hk, hmu'.trans hmu, hc1'.trans hc1, hc2'.trans hc2⟩, le_rfl⟩

theorem runsR_dWalk {tk u fa2 fb2 fa fb : K} (h1 : tk ≠ u) (h2 : tk ≠ fa2) (h3 : tk ≠ fb2)
    (h4 : tk ≠ fa) (h5 : tk ≠ fb) (h6 : u ≠ fa2) (h7 : u ≠ fb2) (h8 : u ≠ fa) (h9 : u ≠ fb)
    (h10 : fa2 ≠ fb2) (h11 : fa2 ≠ fa) (h12 : fa2 ≠ fb) (h13 : fb2 ≠ fa) (h14 : fb2 ≠ fb)
    (h15 : fa ≠ fb) (RA RB : List Sym) (xs ys : List Bool) (S : K → List Sym)
    (hlen : xs.length = ys.length) (hS : S tk = List.replicate xs.length uSym)
    (hA : S fa2 = xs.map Sym.bit ++ RA) (hB : S fb2 = ys.map Sym.bit ++ RB) (k : Fin 4)
    (mu : Bool) :
    RunsR (dWalk tk u fa2 fb2 fa fb) S
      (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S tk []) u (List.replicate xs.length uSym ++ S u))
        fa2 RA) fb2 RB) fa (xs.reverse.map Sym.bit ++ S fa))
        fb (ys.reverse.map Sym.bit ++ S fb)) (KM k mu) (KM k mu) (7 * xs.length + 2) := by
  rintro r ⟨hk, hmu⟩
  obtain ⟨r', hk', hmu', -, -, e⟩ := dWalk_eval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 RA RB xs ys r S hlen hS hA hB
  exact ⟨r', _, e, ⟨hk'.trans hk, hmu'.trans hmu⟩, le_rfl⟩

theorem runsR_cWalk (im : Bool) {tk u fa2 fb2 fa fb o : K} (h1 : tk ≠ u) (h2 : tk ≠ fa2)
    (h3 : tk ≠ fb2) (h4 : tk ≠ fa) (h5 : tk ≠ fb) (h6 : u ≠ fa2) (h7 : u ≠ fb2) (h8 : u ≠ fa)
    (h9 : u ≠ fb) (h10 : fa2 ≠ fb2) (h11 : fa2 ≠ fa) (h12 : fa2 ≠ fb) (h13 : fb2 ≠ fa)
    (h14 : fb2 ≠ fb) (h15 : fa ≠ fb) (ho1 : tk ≠ o) (ho2 : u ≠ o) (ho3 : fa2 ≠ o) (ho4 : fb2 ≠ o)
    (ho5 : fa ≠ o) (ho6 : fb ≠ o) (RA RB : List Sym) (xs ys : List Bool) (S : K → List Sym)
    (hlen : xs.length = ys.length) (hS : S tk = List.replicate xs.length uSym)
    (hA : S fa2 = xs.map Sym.bit ++ RA) (hB : S fb2 = ys.map Sym.bit ++ RB) (k : Fin 4)
    (mu : Bool) :
    RunsR (cWalk im tk u fa2 fb2 fa fb o) S
      (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update S tk []) u
        (List.replicate xs.length uSym ++ S u)) fa2 RA) fb2 RB)
        fa (xs.reverse.map Sym.bit ++ S fa)) fb (ys.reverse.map Sym.bit ++ S fb))
        o ((rip2 (fieldSpec mu k im).1.bitFn (sgnFn (fieldSpec mu k im).2) false false
          xs ys).reverse.map Sym.bit ++ S o)) (KMC k mu) (KM k mu) (9 * xs.length + 2) := by
  rintro r ⟨hk, hmu, hc1, hc2⟩
  obtain ⟨r', hk', hmu', e⟩ := cWalk_eval im h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    ho1 ho2 ho3 ho4 ho5 ho6 RA RB xs ys r S hlen hS hA hB
  rw [hk, hmu, hc1, hc2] at e
  exact ⟨r', _, e, ⟨hk'.trans hk, hmu'.trans hmu⟩, le_rfl⟩

theorem runsR_resetC (S : SK → List Sym) (k : Fin 4) (mu : Bool) :
    RunsR resetC S S (KM k mu) (KMC k mu) 1 := by
  rintro r ⟨hk, hmu⟩
  exact ⟨_, _, Eval.load [] _ r S, ⟨hk, hmu, rfl, rfl⟩, le_rfl⟩

end RunsR


/-! ## One output field, one coefficient -/

/-- The bits of an output field: `n2` zeros, then the first `n1` bits of the two-stage ripple. -/
def outBits (mu : Bool) (k : Fin 4) (im : Bool) (n1 n2 : ℕ) (xs ys : List Bool) : List Bool :=
  List.replicate n2 false ++
    (rip2 (fieldSpec mu k im).1.bitFn (sgnFn (fieldSpec mu k im).2) false false xs ys).take n1

theorem outField_runs (im : Bool) (n1 n2 : ℕ) (xs ys : List Bool) (S : SK → List Sym)
    (k : Fin 4) (mu : Bool) (hlx : xs.length = n1 + n2) (hly : ys.length = n1 + n2)
    (hz : S (.inr .tz) = List.replicate n2 uSym) (hc : S (.inr .tcc) = List.replicate n1 uSym)
    (hd : S (.inr .td) = List.replicate n2 uSym) (hu : S (.inr .u) = [])
    (ha2 : S (.inr .fa2) = xs.map Sym.bit) (hb2 : S (.inr .fb2) = ys.map Sym.bit)
    (ha : S (.inr .fa) = []) (hb : S (.inr .fb) = []) :
    RunsR (outField im) S
      (Function.update (Function.update (Function.update (Function.update (Function.update S
        (.inr .fa2) []) (.inr .fb2) []) (.inr .fa) (xs.reverse.map Sym.bit)) (.inr .fb)
        (ys.reverse.map Sym.bit)) (.inr .o)
        ((outBits mu k im n1 n2 xs ys).reverse.map Sym.bit ++ S (.inr .o)))
      (KM k mu) (KM k mu) (12 * n1 + 17 * n2 + 13) := by
  have l1 : (xs.take n1).length = n1 := by simp [hlx]
  have l2 : (xs.drop n1).length = n2 := by simp [hlx]
  have l3 : (ys.take n1).length = n1 := by simp [hly]
  have l4 : (ys.drop n1).length = n2 := by simp [hly]
  have hxa : xs.map Sym.bit = (xs.take n1).map Sym.bit ++ (xs.drop n1).map Sym.bit := by
    rw [← List.map_append, List.take_append_drop]
  have hya : ys.map Sym.bit = (ys.take n1).map Sym.bit ++ (ys.drop n1).map Sym.bit := by
    rw [← List.map_append, List.take_append_drop]
  have R := RunsR.seq (runsR_resetC S k mu)
    (RunsR.seq (runsR_zWalk (tk := (.inr .tz : SK)) (u := .inr .u) (o := .inr .o) (by simp)
      (by simp) (by simp) n2 _ (by simp [hz]) k mu)
    (RunsR.seq (runsR_drainE (src := (.inr .u : SK)) (dst := .inr .tz) (by simp)
      (List.replicate n2 uSym) _ (by simp [hu]) _ (KMC_t k mu))
    (RunsR.seq (runsR_cWalk im (tk := (.inr .tcc : SK)) (u := .inr .u) (fa2 := .inr .fa2)
      (fb2 := .inr .fb2) (fa := .inr .fa) (fb := .inr .fb) (o := .inr .o) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) ((xs.drop n1).map Sym.bit) ((ys.drop n1).map Sym.bit) (xs.take n1) (ys.take n1) _
      (by rw [l1, l3]) (by simp [hc, l1])
      (by simp only [Function.update_self, Function.update_of_ne, ne_eq, reduceCtorEq, Sum.inr.injEq, not_false_eq_true]; rw [ha2, hxa])
      (by simp only [Function.update_self, Function.update_of_ne, ne_eq, reduceCtorEq, Sum.inr.injEq, not_false_eq_true]; rw [hb2, hya]) k mu)
    (RunsR.seq (runsR_drainE (src := (.inr .u : SK)) (dst := .inr .tcc) (by simp)
      (List.replicate (xs.take n1).length uSym) _ (by simp [hu]) _ (KM_t k mu))
    (RunsR.seq (runsR_dWalk (tk := (.inr .td : SK)) (u := .inr .u) (fa2 := .inr .fa2)
      (fb2 := .inr .fb2) (fa := .inr .fa) (fb := .inr .fb) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) [] [] (xs.drop n1) (ys.drop n1) _ (by rw [l2, l4])
      (by simp [hd, l2]) (by simp) (by simp) k mu)
      (runsR_drainE (src := (.inr .u : SK)) (dst := .inr .td) (by simp)
        (List.replicate (xs.drop n1).length uSym) _ (by simp [hu]) _ (KM_t k mu)))))))
  refine (R.congr ?_).mono (fun _ h => h) (fun _ h => h) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp only [Function.update_self, Function.update_of_ne, ne_eq, reduceCtorEq, Sum.inr.injEq, not_false_eq_true]
    · cases e <;> simp only [Function.update_self, Function.update_of_ne, ne_eq, reduceCtorEq, Sum.inr.injEq, not_false_eq_true]
      all_goals first
        | rfl
        | (rw [ha, List.append_nil, ← List.map_append, ← List.reverse_append,
            List.take_append_drop])
        | (rw [hb, List.append_nil, ← List.map_append, ← List.reverse_append,
            List.take_append_drop])
        | (rw [rip2_take, outBits, List.reverse_append, List.map_append, List.reverse_replicate,
            List.map_replicate, List.append_assoc])
        | simp [hz, hc, hd, hu, l1, l2]
  · simp only [List.length_replicate, l1, l2]
    omega


theorem readField_runs (dst : SS) (h1 : dst ≠ .tcc) (h2 : dst ≠ .td) (h3 : dst ≠ .u)
    (n1 n2 : ℕ) (bs : List Bool) (R : List Sym) (S : SK → List Sym) (k : Fin 4) (mu : Bool)
    (hl : bs.length = n1 + n2) (hc : S (.inr .tcc) = List.replicate n1 uSym)
    (hd : S (.inr .td) = List.replicate n2 uSym) (hu : S (.inr .u) = [])
    (hA : S (.inl 0) = bs.map Sym.bit ++ R) :
    RunsR (readField dst) S
      (Function.update (Function.update S (.inl 0) R) (.inr dst)
        (bs.reverse.map Sym.bit ++ S (.inr dst))) (KM k mu) (KM k mu)
      (8 * n1 + 8 * n2 + 8) := by
  have l1 : (bs.take n1).length = n1 := by simp [hl]
  have l2 : (bs.drop n1).length = n2 := by simp [hl]
  have hba : bs.map Sym.bit ++ R = (bs.take n1).map Sym.bit ++ ((bs.drop n1).map Sym.bit ++ R) := by
    rw [← List.append_assoc, ← List.map_append, List.take_append_drop]
  have R1 := RunsR.seq (runsR_readWalk (tk := (.inr .tcc : SK)) (u := .inr .u) (src := .inl 0)
      (dst := .inr dst) (by simp) (by simp) (by simp [Ne.symm h1]) (by simp) (by simp [Ne.symm h3])
      (by simp) ((bs.drop n1).map Sym.bit ++ R) (bs.take n1) S (by simp [hc, l1])
      (by rw [hA, hba]) k mu)
    (RunsR.seq (runsR_drainE (src := (.inr .u : SK)) (dst := .inr .tcc) (by simp)
      (List.replicate (bs.take n1).length uSym) _ (by simp [hu, Ne.symm h3]) _ (KM_t k mu))
    (RunsR.seq (runsR_readWalk (tk := (.inr .td : SK)) (u := .inr .u) (src := .inl 0)
      (dst := .inr dst) (by simp) (by simp) (by simp [Ne.symm h2]) (by simp) (by simp [Ne.symm h3])
      (by simp) R (bs.drop n1) _ (by simp [hd, l2, Ne.symm h1, Ne.symm h2]) (by simp [Ne.symm h1]) k mu)
      (runsR_drainE (src := (.inr .u : SK)) (dst := .inr .td) (by simp)
        (List.replicate (bs.drop n1).length uSym) _ (by simp [hu, h1, h3, Ne.symm h1, Ne.symm h3]) _ (KM_t k mu))))
  refine (R1.congr ?_).mono (fun _ h => h) (fun _ h => h) ?_
  · funext j
    rcases j with i | e
    · fin_cases i <;> simp [h1, h3, Ne.symm h1, Ne.symm h2]
    · by_cases he : e = dst
      · subst he
        simp only [Function.update_self, Function.update_of_ne, ne_eq, reduceCtorEq,
          Sum.inr.injEq, h1, h2, h3, not_false_eq_true]
        rw [← List.append_assoc, ← List.map_append, ← List.reverse_append, List.take_append_drop]
      · clear R1
        cases e <;> simp [hc, hd, hu, he, Ne.symm he, hl]
  · simp only [List.length_replicate, l1, l2]
    omega

end SubNLogN.Machine.WalshScanAux
