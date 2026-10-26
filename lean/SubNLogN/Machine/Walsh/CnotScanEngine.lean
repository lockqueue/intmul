/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanBits
import SubNLogN.Machine.Walsh.LiftLoop

/-!
# `SubNLogN.Machine.Walsh.CnotScanEngine`: the field walks of the CNOT-batch scans

Paper: Lemma 5.1 (`lem:walsh-select`), eq. (`eq:walsh-CZ`), and Proposition 5.5 (`prop:cnot-batch`) (the scans multiply every
coefficient of a record by a Gaussian integer `2^e i^k (1-i)^μ`).

## Plan (all scan kernels)
* Registers `ER`: two symbol registers `t`, `s`, the record's unit exponent `k : Fin 4`, the flag
  `mu` (one factor `1 - i`), and the two ripple carries `c1`, `c2`.
* Templates: unary counters `tz = uSym^{e'}`, `tcc = uSym^{W - e'}`, `td = uSym^{e'}` on clean
  scratch stacks (`W` the field width, `e' = min e W`); a walk moves the units to the scratch `u`
  and back.
* Per coefficient `(a, b)`: read both fields (`W` bits each, walks over `tcc` then `td`) into two
  buffers, reverse them, and emit each output field by a walk over `tz` (zeros), `tcc` (the
  two-stage ripple `rip2` of `fieldSpec mu k`), `td` (drop); see `Walsh/CnotScanBits.lean`.
This file: the register type, the atoms and the four walks with exact evaluation lemmas.

**Scope (honest summary).** Programs and exact evaluation lemmas only; no contract is proved
here.
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Lib TMFw.Contracts SubNLogN.Machine WalshLift

/-- Registers of the scan kernels. -/
structure ER : Type where
  /-- template / first symbol register -/
  t : Option Sym
  /-- second symbol register -/
  s : Option Sym
  /-- unit exponent of the current record -/
  k : Fin 4
  /-- one factor `1 - i` -/
  mu : Bool
  /-- stage-1 carry -/
  c1 : Bool
  /-- stage-2 carry -/
  c2 : Bool

instance : Nonempty ER := ⟨⟨none, none, 0, false, false, false⟩⟩

instance : Finite ER :=
  Finite.of_injective (fun r : ER => (r.t, r.s, r.k, r.mu, r.c1, r.c2))
    (by rintro ⟨_, _, _, _, _, _⟩ ⟨_, _, _, _, _, _⟩ h; simp_all)

/-- The lens onto `t`, to run the `Option Sym` library loops. -/
def lT : Lens ER (Option Sym) where
  get := ER.t
  set r x := { r with t := x }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Programs of the scan kernels. -/
abbrev EProg (K : Type) : Type := Prog K (fun _ => Sym) ER

/-- The field table: `(L, σ)` with `Re`, resp. `Im` (`im = true`), of `i^k (1 - i)^μ (a + bi)`
equal to `σ·L(a, b)` (`σ = true` means `-`). -/
def fieldSpec (mu : Bool) (k : Fin 4) (im : Bool) : LForm × Bool :=
  match mu, k.val, im with
  | false, 0, false => (.a, false)
  | false, 0, true => (.b, false)
  | false, 1, false => (.b, true)
  | false, 1, true => (.a, false)
  | false, 2, false => (.a, true)
  | false, 2, true => (.b, true)
  | false, _, false => (.b, false)
  | false, _, true => (.a, true)
  | true, 0, false => (.apb, false)
  | true, 0, true => (.bma, false)
  | true, 1, false => (.amb, false)
  | true, 1, true => (.apb, false)
  | true, 2, false => (.apb, true)
  | true, 2, true => (.amb, false)
  | true, _, false => (.bma, false)
  | true, _, true => (.apb, true)

/-- `i^k` as a Gaussian integer. -/
def unitZ (k : Fin 4) : CInt :=
  match k.val with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | _ => (0, -1)

/-- `i^k (1 - i)^μ` as a Gaussian integer. -/
def gfacZ (mu : Bool) (k : Fin 4) : CInt := if mu then cmulC (unitZ k) (1, -1) else unitZ k

/-- The value of a field spec. -/
def specVal (p : LForm × Bool) (x y : ℤ) : ℤ := if p.2 then -p.1.val x y else p.1.val x y

/-- **The field table is right**: the parts of `i^k (1-i)^μ (x + yi)` are the field specs. -/
theorem cmulC_gfacZ (mu : Bool) (k : Fin 4) (x y : ℤ) :
    cmulC (gfacZ mu k) (x, y) = (specVal (fieldSpec mu k false) x y,
      specVal (fieldSpec mu k true) x y) := by
  obtain ⟨kv, hk⟩ := k
  have : kv = 0 ∨ kv = 1 ∨ kv = 2 ∨ kv = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> cases mu <;> refine Prod.ext ?_ ?_ <;>
    simp [gfacZ, unitZ, fieldSpec, specVal, cmulC, LForm.val] <;> ring

/-! ## Atoms -/

section Atoms

variable {K : Type}

/-- Pop `k` into `t`. -/
def popT (k : K) : EProg K := .pop k fun r o => { r with t := o }

/-- Pop `k` into `s`. -/
def popS (k : K) : EProg K := .pop k fun r o => { r with s := o }

/-- Push `t` (default `sep`). -/
def pushT (k : K) : EProg K := .push k fun r => r.t.getD .sep

/-- Push `s` (default `sep`). -/
def pushS (k : K) : EProg K := .push k fun r => r.s.getD .sep

/-- Push a constant. -/
def pushK (k : K) (x : Sym) : EProg K := .push k fun _ => x

/-- Loop test of the walks: the template pop found a unit. -/
def tSome (r : ER) : Bool := r.t.isSome

variable [DecidableEq K]

theorem eval_popT (k : K) (r : ER) (L : List Sym) (S : K → List Sym) (hS : S k = L) :
    Eval [] (popT k) ⟨r, S⟩ ⟨{ r with t := L.head? }, Function.update S k L.tail⟩ 1 := by
  refine (Eval.pop [] k (fun r o => { r with t := o }) r S).of_eq ?_ rfl
  rw [hS]

theorem eval_popS (k : K) (r : ER) (L : List Sym) (S : K → List Sym) (hS : S k = L) :
    Eval [] (popS k) ⟨r, S⟩ ⟨{ r with s := L.head? }, Function.update S k L.tail⟩ 1 := by
  refine (Eval.pop [] k (fun r o => { r with s := o }) r S).of_eq ?_ rfl
  rw [hS]

theorem eval_pushT (k : K) (r : ER) (x : Sym) (hx : r.t = some x) (S : K → List Sym) :
    Eval [] (pushT k) ⟨r, S⟩ ⟨r, Function.update S k (x :: S k)⟩ 1 := by
  refine (Eval.push [] k (fun r : ER => r.t.getD .sep) r S).of_eq ?_ rfl
  simp [hx]

theorem eval_pushS (k : K) (r : ER) (x : Sym) (hx : r.s = some x) (S : K → List Sym) :
    Eval [] (pushS k) ⟨r, S⟩ ⟨r, Function.update S k (x :: S k)⟩ 1 := by
  refine (Eval.push [] k (fun r : ER => r.s.getD .sep) r S).of_eq ?_ rfl
  simp [hx]

theorem eval_pushK (k : K) (x : Sym) (r : ER) (S : K → List Sym) :
    Eval [] (pushK k x) ⟨r, S⟩ ⟨r, Function.update S k (x :: S k)⟩ 1 := by
  unfold pushK
  exact Eval.push [] k (fun _ : ER => x) r S

/-- `drain` through the lens `lT`. -/
theorem eval_drainE {src dst : K} (hne : src ≠ dst) (r : ER) (L : List Sym) (S : K → List Sym)
    (hS : S src = L) :
    Eval [] ((drain src dst).liftRegs lT) ⟨r, S⟩
      ⟨{ r with t := none }, Function.update (Function.update S src []) dst (L.reverse ++ S dst)⟩
      (3 * L.length + 2) :=
  Eval.liftRegs lT (drain_eval hne r.t L S hS) r rfl

/-- `clear` through the lens `lT`. -/
theorem eval_clearE (k : K) (r : ER) (L : List Sym) (S : K → List Sym) (hS : S k = L) :
    Eval [] ((clear k).liftRegs lT) ⟨r, S⟩ ⟨{ r with t := none }, Function.update S k []⟩
      (2 * L.length + 2) :=
  Eval.liftRegs lT (clear_eval k r.t L S hS) r rfl

end Atoms

/-! ## The four walks -/

section Walks

variable {K : Type}

/-- One reading step: pop an input bit of `src` into `s`, push it on `dst`. -/
def readStep (tk u src dst : K) : EProg K :=
  .seq (pushK u uSym) (.seq (popS src) (.seq (pushS dst) (popT tk)))

/-- Read one input bit per unit of `tk`. -/
def readWalk (tk u src dst : K) : EProg K := .seq (popT tk) (.loop tSome (readStep tk u src dst))

/-- One zero step: push a `0` on the output `o`. -/
def zStep (tk u o : K) : EProg K := .seq (pushK u uSym) (.seq (pushK o (.bit false)) (popT tk))

/-- One output zero per unit of `tk`. -/
def zWalk (tk u o : K) : EProg K := .seq (popT tk) (.loop tSome (zStep tk u o))

/-- One drop step: move a bit pair from `fa2`, `fb2` to `fa`, `fb` (no output). -/
def dStep (tk u fa2 fb2 fa fb : K) : EProg K :=
  .seq (pushK u uSym) (.seq (popT fa2) (.seq (pushT fa) (.seq (popS fb2) (.seq (pushS fb)
    (popT tk)))))

/-- Drop one bit pair per unit of `tk`. -/
def dWalk (tk u fa2 fb2 fa fb : K) : EProg K := .seq (popT tk) (.loop tSome (dStep tk u fa2 fb2 fa fb))

/-- The output bit of a ripple step on `(t, s)` for the field `im`. -/
def outBit (im : Bool) (r : ER) : Bool :=
  (sgnFn (fieldSpec r.mu r.k im).2
    ((fieldSpec r.mu r.k im).1.bitFn (optBit r.t) (optBit r.s) r.c1).1
    ((fieldSpec r.mu r.k im).1.bitFn (optBit r.t) (optBit r.s) r.c1).1 r.c2).1

/-- The carries after a ripple step. -/
def nextC (im : Bool) (r : ER) : ER :=
  { r with
    c1 := ((fieldSpec r.mu r.k im).1.bitFn (optBit r.t) (optBit r.s) r.c1).2
    c2 := (sgnFn (fieldSpec r.mu r.k im).2
      ((fieldSpec r.mu r.k im).1.bitFn (optBit r.t) (optBit r.s) r.c1).1
      ((fieldSpec r.mu r.k im).1.bitFn (optBit r.t) (optBit r.s) r.c1).1 r.c2).2 }

/-- One computing step: move a bit pair from `fa2`, `fb2` to `fa`, `fb`, emit the output bit. -/
def cStep (im : Bool) (tk u fa2 fb2 fa fb o : K) : EProg K :=
  .seq (pushK u uSym) (.seq (popT fa2) (.seq (pushT fa) (.seq (popS fb2) (.seq (pushS fb)
    (.seq (.push o fun r => .bit (outBit im r)) (.seq (.load (nextC im)) (popT tk)))))))

/-- One output bit per unit of `tk`, computed by the ripple of the field `im`. -/
def cWalk (im : Bool) (tk u fa2 fb2 fa fb o : K) : EProg K :=
  .seq (popT tk) (.loop tSome (cStep im tk u fa2 fb2 fa fb o))

variable [DecidableEq K]

theorem readWalk_loop_eval {tk u src dst : K} (h1 : tk ≠ u) (h2 : tk ≠ src) (h3 : tk ≠ dst)
    (h4 : u ≠ src) (h5 : u ≠ dst) (h6 : src ≠ dst) (R : List Sym) :
    ∀ (bs : List Bool) (r : ER) (S : K → List Sym),
      r.t = (List.replicate bs.length uSym).head? →
      S tk = (List.replicate bs.length uSym).tail → S src = bs.map Sym.bit ++ R →
      ∃ r' : ER, r'.k = r.k ∧ r'.mu = r.mu ∧ r'.c1 = r.c1 ∧ r'.c2 = r.c2 ∧
        Eval [] (.loop tSome (readStep tk u src dst)) ⟨r, S⟩
          ⟨r', Function.update (Function.update (Function.update (Function.update S tk []) u
            (List.replicate bs.length uSym ++ S u)) src R) dst (bs.reverse.map Sym.bit ++ S dst)⟩
          (5 * bs.length + 1)
  | [], r, S, hr, hS, hX => by
    have hr' : r.t = none := by simpa using hr
    have hS' : S tk = [] := by simpa using hS
    have hX' : S src = R := by simpa using hX
    refine ⟨r, rfl, rfl, rfl, rfl, (Eval.loop_false (by simp [tSome, hr'])).of_eq ?_ rfl⟩
    congr 1
    funext k
    simp only [Function.update_apply, List.length_nil, List.replicate_zero, List.nil_append,
      List.reverse_nil, List.map_nil]
    split_ifs <;> simp_all
  | b :: bs, r, S, hr, hS, hX => by
    have hr' : r.t = some uSym := by simpa [List.replicate_succ] using hr
    have hS' : S tk = List.replicate bs.length uSym := by simpa [List.replicate_succ] using hS
    set S1 := Function.update S u (uSym :: S u) with hS1
    have e1 := eval_pushK u uSym r S
    have e2 := eval_popS src r (Sym.bit b :: (bs.map Sym.bit ++ R)) S1
      (by rw [hS1, Function.update_of_ne h4.symm, hX]; rfl)
    set S2 := Function.update S1 src (bs.map Sym.bit ++ R) with hS2
    have e3 := eval_pushS dst { r with s := some (Sym.bit b) } (Sym.bit b) rfl S2
    set S3 := Function.update S2 dst (Sym.bit b :: S2 dst) with hS3
    have e4 := eval_popT tk { r with s := some (Sym.bit b) } (List.replicate bs.length uSym) S3
      (by rw [hS3, Function.update_of_ne h3, hS2, Function.update_of_ne h2, hS1,
        Function.update_of_ne h1, hS'])
    obtain ⟨r', hk, hmu, hc1, hc2, e5⟩ := readWalk_loop_eval h1 h2 h3 h4 h5 h6 R bs
      { r with s := some (Sym.bit b), t := (List.replicate bs.length uSym).head? }
      (Function.update S3 tk (List.replicate bs.length uSym).tail) rfl
      (Function.update_self _ _ _)
      (by rw [Function.update_of_ne h2.symm, hS3, Function.update_of_ne h6, hS2,
        Function.update_self])
    refine ⟨r', hk, hmu, hc1, hc2, (Eval.loop_true (by simp [tSome, hr'])
      (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) e5).of_eq ?_ ?_⟩
    · clear e1 e2 e3 e4 e5
      congr 1
      funext k
      simp only [hS3, hS2, hS1, Function.update_apply, List.length_cons, List.replicate_succ',
        List.append_assoc, List.singleton_append, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

theorem zWalk_loop_eval {tk u o : K} (h1 : tk ≠ u) (h2 : tk ≠ o) (h3 : u ≠ o) :
    ∀ (n : ℕ) (r : ER) (S : K → List Sym), r.t = (List.replicate n uSym).head? →
      S tk = (List.replicate n uSym).tail →
      ∃ r' : ER, r'.k = r.k ∧ r'.mu = r.mu ∧ r'.c1 = r.c1 ∧ r'.c2 = r.c2 ∧
        Eval [] (.loop tSome (zStep tk u o)) ⟨r, S⟩
          ⟨r', Function.update (Function.update (Function.update S tk []) u
            (List.replicate n uSym ++ S u)) o (List.replicate n (Sym.bit false) ++ S o)⟩
          (4 * n + 1)
  | 0, r, S, hr, hS => by
    have hr' : r.t = none := by simpa using hr
    have hS' : S tk = [] := by simpa using hS
    refine ⟨r, rfl, rfl, rfl, rfl, (Eval.loop_false (by simp [tSome, hr'])).of_eq ?_ rfl⟩
    congr 1
    funext k
    simp only [Function.update_apply, List.replicate_zero, List.nil_append]
    split_ifs <;> simp_all
  | n + 1, r, S, hr, hS => by
    have hr' : r.t = some uSym := by simpa [List.replicate_succ] using hr
    have hS' : S tk = List.replicate n uSym := by simpa [List.replicate_succ] using hS
    set S1 := Function.update S u (uSym :: S u) with hS1
    have e1 := eval_pushK u uSym r S
    have e2 := eval_pushK o (Sym.bit false) r S1
    set S2 := Function.update S1 o (Sym.bit false :: S1 o) with hS2
    have e3 := eval_popT tk r (List.replicate n uSym) S2
      (by rw [hS2, Function.update_of_ne h2, hS1, Function.update_of_ne h1, hS'])
    obtain ⟨r', hk, hmu, hc1, hc2, e4⟩ := zWalk_loop_eval h1 h2 h3 n
      { r with t := (List.replicate n uSym).head? }
      (Function.update S2 tk (List.replicate n uSym).tail) rfl (Function.update_self _ _ _)
    refine ⟨r', hk, hmu, hc1, hc2, (Eval.loop_true (by simp [tSome, hr'])
      (Eval.seq e1 (Eval.seq e2 e3)) e4).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [hS2, hS1, Function.update_apply, List.replicate_succ', List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · omega

theorem dWalk_loop_eval {tk u fa2 fb2 fa fb : K} (h1 : tk ≠ u) (h2 : tk ≠ fa2) (h3 : tk ≠ fb2)
    (h4 : tk ≠ fa) (h5 : tk ≠ fb) (h6 : u ≠ fa2) (h7 : u ≠ fb2) (h8 : u ≠ fa) (h9 : u ≠ fb)
    (h10 : fa2 ≠ fb2) (h11 : fa2 ≠ fa) (h12 : fa2 ≠ fb) (h13 : fb2 ≠ fa) (h14 : fb2 ≠ fb)
    (h15 : fa ≠ fb) (RA RB : List Sym) :
    ∀ (xs ys : List Bool) (r : ER) (S : K → List Sym), xs.length = ys.length →
      r.t = (List.replicate xs.length uSym).head? →
      S tk = (List.replicate xs.length uSym).tail → S fa2 = xs.map Sym.bit ++ RA →
      S fb2 = ys.map Sym.bit ++ RB →
      ∃ r' : ER, r'.k = r.k ∧ r'.mu = r.mu ∧ r'.c1 = r.c1 ∧ r'.c2 = r.c2 ∧
        Eval [] (.loop tSome (dStep tk u fa2 fb2 fa fb)) ⟨r, S⟩
          ⟨r', Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update S tk []) u (List.replicate xs.length uSym ++ S u))
            fa2 RA) fb2 RB) fa (xs.reverse.map Sym.bit ++ S fa))
            fb (ys.reverse.map Sym.bit ++ S fb)⟩ (7 * xs.length + 1)
  | [], [], r, S, _, hr, hS, hA, hB => by
    have hr' : r.t = none := by simpa using hr
    have hS' : S tk = [] := by simpa using hS
    have hA' : S fa2 = RA := by simpa using hA
    have hB' : S fb2 = RB := by simpa using hB
    refine ⟨r, rfl, rfl, rfl, rfl, (Eval.loop_false (by simp [tSome, hr'])).of_eq ?_ rfl⟩
    congr 1
    funext k
    simp only [Function.update_apply, List.length_nil, List.replicate_zero, List.nil_append,
      List.reverse_nil, List.map_nil]
    split_ifs <;> simp_all
  | [], _ :: _, _, _, h, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _, _ => by simp at h
  | x :: xs, y :: ys, r, S, hlen, hr, hS, hA, hB => by
    have hr' : r.t = some uSym := by simpa [List.replicate_succ] using hr
    have hS' : S tk = List.replicate xs.length uSym := by simpa [List.replicate_succ] using hS
    set S1 := Function.update S u (uSym :: S u) with hS1
    have e1 := eval_pushK u uSym r S
    have e2 := eval_popT fa2 r (Sym.bit x :: (xs.map Sym.bit ++ RA)) S1
      (by rw [hS1, Function.update_of_ne h6.symm, hA]; rfl)
    set S2 := Function.update S1 fa2 (xs.map Sym.bit ++ RA) with hS2
    have e3 := eval_pushT fa { r with t := some (Sym.bit x) } (Sym.bit x) rfl S2
    set S3 := Function.update S2 fa (Sym.bit x :: S2 fa) with hS3
    have e4 := eval_popS fb2 { r with t := some (Sym.bit x) } (Sym.bit y :: (ys.map Sym.bit ++ RB))
      S3 (by rw [hS3, Function.update_of_ne h13, hS2, Function.update_of_ne h10.symm, hS1,
        Function.update_of_ne h7.symm, hB]; rfl)
    set S4 := Function.update S3 fb2 (ys.map Sym.bit ++ RB) with hS4
    have e5 := eval_pushS fb { r with t := some (Sym.bit x), s := some (Sym.bit y) } (Sym.bit y)
      rfl S4
    set S5 := Function.update S4 fb (Sym.bit y :: S4 fb) with hS5
    have e6 := eval_popT tk { r with t := some (Sym.bit x), s := some (Sym.bit y) }
      (List.replicate xs.length uSym) S5
      (by rw [hS5, Function.update_of_ne h5, hS4, Function.update_of_ne h3, hS3,
        Function.update_of_ne h4, hS2, Function.update_of_ne h2, hS1, Function.update_of_ne h1,
        hS'])
    obtain ⟨r', hk, hmu, hc1, hc2, e7⟩ := dWalk_loop_eval h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      h13 h14 h15 RA RB xs ys
      { r with t := (List.replicate xs.length uSym).head?, s := some (Sym.bit y) }
      (Function.update S5 tk (List.replicate xs.length uSym).tail) (by simpa using hlen) rfl
      (Function.update_self _ _ _)
      (by rw [Function.update_of_ne h2.symm, hS5, Function.update_of_ne h12, hS4,
        Function.update_of_ne h10, hS3, Function.update_of_ne h11, hS2, Function.update_self])
      (by rw [Function.update_of_ne h3.symm, hS5, Function.update_of_ne h14, hS4,
        Function.update_self])
    refine ⟨r', hk, hmu, hc1, hc2, (Eval.loop_true (by simp [tSome, hr'])
      (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))) e7).of_eq ?_ ?_⟩
    · clear e1 e2 e3 e4 e5 e6 e7
      congr 1
      funext k
      by_cases a1 : k = tk
      · subst a1
        simp [Function.update_apply, hS5, hS4, hS3, hS2, hS1, h1, h2, h3, h4, h5]
      by_cases a2 : k = u
      · subst a2
        simp [Function.update_apply, hS5, hS4, hS3, hS2, hS1, h1.symm, h6, h7, h8, h9,
          List.replicate_succ']
      by_cases a3 : k = fa2
      · subst a3
        simp [Function.update_apply, hS5, hS4, hS3, hS2, hS1, h10, h11, h12]
      by_cases a4 : k = fb2
      · subst a4
        simp [Function.update_apply, hS5, hS4, hS3, hS2, hS1, h13, h14]
      by_cases a5 : k = fa
      · subst a5
        simp [Function.update_apply, hS5, hS4, hS3, hS2, hS1, h4.symm, h8.symm, h11.symm,
          h13.symm, h15]
      by_cases a6 : k = fb
      · subst a6
        simp [Function.update_apply, hS5, hS4, hS3, hS2, hS1, h5.symm, h9.symm, h12.symm,
          h14.symm, h15.symm]
      · simp [Function.update_apply, hS5, hS4, hS3, hS2, hS1, a1, a2, a3, a4, a5, a6]
    · simp only [List.length_cons]
      omega

theorem outBit_eq (im : Bool) (r : ER) (x y : Bool) :
    outBit im { r with t := some (Sym.bit x), s := some (Sym.bit y) } =
      (sgnFn (fieldSpec r.mu r.k im).2 ((fieldSpec r.mu r.k im).1.bitFn x y r.c1).1
        ((fieldSpec r.mu r.k im).1.bitFn x y r.c1).1 r.c2).1 := rfl

theorem cWalk_loop_eval (im : Bool) {tk u fa2 fb2 fa fb o : K} (h1 : tk ≠ u) (h2 : tk ≠ fa2)
    (h3 : tk ≠ fb2) (h4 : tk ≠ fa) (h5 : tk ≠ fb) (h6 : u ≠ fa2) (h7 : u ≠ fb2) (h8 : u ≠ fa)
    (h9 : u ≠ fb) (h10 : fa2 ≠ fb2) (h11 : fa2 ≠ fa) (h12 : fa2 ≠ fb) (h13 : fb2 ≠ fa)
    (h14 : fb2 ≠ fb) (h15 : fa ≠ fb) (ho1 : tk ≠ o) (ho2 : u ≠ o) (ho3 : fa2 ≠ o) (ho4 : fb2 ≠ o)
    (ho5 : fa ≠ o) (ho6 : fb ≠ o) (RA RB : List Sym) :
    ∀ (xs ys : List Bool) (r : ER) (S : K → List Sym), xs.length = ys.length →
      r.t = (List.replicate xs.length uSym).head? →
      S tk = (List.replicate xs.length uSym).tail → S fa2 = xs.map Sym.bit ++ RA →
      S fb2 = ys.map Sym.bit ++ RB →
      ∃ r' : ER, r'.k = r.k ∧ r'.mu = r.mu ∧
        Eval [] (.loop tSome (cStep im tk u fa2 fb2 fa fb o)) ⟨r, S⟩
          ⟨r', Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update S tk []) u
            (List.replicate xs.length uSym ++ S u)) fa2 RA) fb2 RB)
            fa (xs.reverse.map Sym.bit ++ S fa)) fb (ys.reverse.map Sym.bit ++ S fb))
            o ((rip2 (fieldSpec r.mu r.k im).1.bitFn (sgnFn (fieldSpec r.mu r.k im).2) r.c1 r.c2
              xs ys).reverse.map Sym.bit ++ S o)⟩ (9 * xs.length + 1)
  | [], [], r, S, _, hr, hS, hA, hB => by
    have hr' : r.t = none := by simpa using hr
    have hS' : S tk = [] := by simpa using hS
    have hA' : S fa2 = RA := by simpa using hA
    have hB' : S fb2 = RB := by simpa using hB
    refine ⟨r, rfl, rfl, (Eval.loop_false (by simp [tSome, hr'])).of_eq ?_ rfl⟩
    congr 1
    funext k
    simp only [Function.update_apply, List.length_nil, List.replicate_zero, List.nil_append,
      List.reverse_nil, List.map_nil, rip2]
    split_ifs <;> simp_all
  | [], _ :: _, _, _, h, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _, _ => by simp at h
  | x :: xs, y :: ys, r, S, hlen, hr, hS, hA, hB => by
    have hr' : r.t = some uSym := by simpa [List.replicate_succ] using hr
    have hS' : S tk = List.replicate xs.length uSym := by simpa [List.replicate_succ] using hS
    set S1 := Function.update S u (uSym :: S u) with hS1
    have e1 := eval_pushK u uSym r S
    have e2 := eval_popT fa2 r (Sym.bit x :: (xs.map Sym.bit ++ RA)) S1
      (by rw [hS1, Function.update_of_ne h6.symm, hA]; rfl)
    set S2 := Function.update S1 fa2 (xs.map Sym.bit ++ RA) with hS2
    have e3 := eval_pushT fa { r with t := some (Sym.bit x) } (Sym.bit x) rfl S2
    set S3 := Function.update S2 fa (Sym.bit x :: S2 fa) with hS3
    have e4 := eval_popS fb2 { r with t := some (Sym.bit x) } (Sym.bit y :: (ys.map Sym.bit ++ RB))
      S3 (by rw [hS3, Function.update_of_ne h13, hS2, Function.update_of_ne h10.symm, hS1,
        Function.update_of_ne h7.symm, hB]; rfl)
    set S4 := Function.update S3 fb2 (ys.map Sym.bit ++ RB) with hS4
    set r2 : ER := { r with t := some (Sym.bit x), s := some (Sym.bit y) } with hr2
    have e5 := eval_pushS fb r2 (Sym.bit y) rfl S4
    set S5 := Function.update S4 fb (Sym.bit y :: S4 fb) with hS5
    have e6 := Eval.push [] o (fun r : ER => Sym.bit (outBit im r)) r2 S5
    set S6 := Function.update S5 o (Sym.bit (outBit im r2) :: S5 o) with hS6
    have e7 := Eval.load [] (nextC im) r2 S6
    have e8 := eval_popT tk (nextC im r2) (List.replicate xs.length uSym) S6
      (by rw [hS6, Function.update_of_ne ho1, hS5, Function.update_of_ne h5, hS4,
        Function.update_of_ne h3, hS3, Function.update_of_ne h4, hS2, Function.update_of_ne h2,
        hS1, Function.update_of_ne h1, hS'])
    obtain ⟨r', hk, hmu, e9⟩ := cWalk_loop_eval im h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
      h14 h15 ho1 ho2 ho3 ho4 ho5 ho6 RA RB xs ys
      { nextC im r2 with t := (List.replicate xs.length uSym).head? }
      (Function.update S6 tk (List.replicate xs.length uSym).tail) (by simpa using hlen) rfl
      (Function.update_self _ _ _)
      (by rw [Function.update_of_ne h2.symm, hS6, Function.update_of_ne ho3, hS5,
        Function.update_of_ne h12, hS4, Function.update_of_ne h10, hS3, Function.update_of_ne h11,
        hS2, Function.update_self])
      (by rw [Function.update_of_ne h3.symm, hS6, Function.update_of_ne ho4, hS5,
        Function.update_of_ne h14, hS4, Function.update_self])
    refine ⟨r', hk.trans rfl, hmu.trans rfl, (Eval.loop_true (by simp [tSome, hr'])
      (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
        (Eval.seq e7 e8))))))) e9).of_eq ?_ ?_⟩
    · clear e1 e2 e3 e4 e5 e6 e7 e8 e9
      congr 1
      funext k
      by_cases a1 : k = tk
      · subst a1
        simp [Function.update_apply, hS6, hS5, hS4, hS3, hS2, hS1, h1, h2, h3, h4, h5, ho1]
      by_cases a2 : k = u
      · subst a2
        simp [Function.update_apply, hS6, hS5, hS4, hS3, hS2, hS1, h1.symm, h6, h7, h8, h9, ho2,
          List.replicate_succ']
      by_cases a3 : k = fa2
      · subst a3
        simp [Function.update_apply, hS6, hS5, hS4, hS3, hS2, hS1, h10, h11, h12, ho3]
      by_cases a4 : k = fb2
      · subst a4
        simp [Function.update_apply, hS6, hS5, hS4, hS3, hS2, hS1, h13, h14, ho4]
      by_cases a5 : k = fa
      · subst a5
        simp [Function.update_apply, hS6, hS5, hS4, hS3, hS2, hS1, h4.symm, h8.symm, h11.symm,
          h13.symm, h15, ho5]
      by_cases a6 : k = fb
      · subst a6
        simp [Function.update_apply, hS6, hS5, hS4, hS3, hS2, hS1, h5.symm, h9.symm, h12.symm,
          h14.symm, h15.symm, ho6]
      by_cases a7 : k = o
      · subst a7
        simp [Function.update_apply, hS6, hS5, hS4, hS3, hS2, hS1, ho1.symm, ho2.symm, ho3.symm,
          ho4.symm, ho5.symm, ho6.symm, hr2, rip2, outBit_eq, nextC]
      · simp [Function.update_apply, hS6, hS5, hS4, hS3, hS2, hS1, a1, a2, a3, a4, a5, a6, a7]
    · simp only [List.length_cons]
      omega

end Walks

end SubNLogN.Machine.WalshScanAux
