/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WP.W3s.ConcatCore
import WP.W9comp.Kit
import Contracts.W9.Common

/-!
# K3.0a kit (`Machine/Walsh/CubeHdrKit.lean`): field moves for the slice-header builder

**Scope (honest summary).** Algorithm-free stack routines on generic stacks `K`, each with an exact
`Runs` lemma (exact final stacks, explicit cost), all proved (no `sorry`), in the namespace
`SubNLogN.Machine.WalshCubeAux`. A field is `natSyms n ++ [mark]` (`hdrSyms`,
`Contracts/W9/Common.lean:121`).
* `unpackField src F pk`: move the top field of `src` to `F` (bits reversed) and to `pk` (bits
  reversed, then its `mark`);
* `parkField src pk`: move the top field of `src` to `pk` only;
* `xfer src dst`: move every symbol of `src` onto `dst` (reversed) until `src` is empty;
* `clearBits k`: empty a stack holding only bits;
* `pushFieldRev F H`: push `mark`, then the number held reversed on `F`, onto `H` (natural order),
  emptying `F`;
* `pow2Field F H C Y kc u t`: push `mark`, then `2^n` (from `n` held reversed on `F`), onto `H`,
  via the proved W3 concatenation `concatCore` (`WP/W3s/ConcatCore.lean`), emptying `F`;
* `runs_inc`: the W3 counter increment `inc` (`IntMulTM/Framework/Lib/Counter.lean`).
-/

namespace SubNLogN.Machine.WalshCubeAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

theorem natSyms_one_eq : natSyms 1 = [Sym.bit true] := by
  simp [natSyms, encodeNat_succ, encodeNat_zero, incBits]

theorem natSyms_zero_eq : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]

/-- Is the register a symbol? -/
def cubeIsSome (r : Option Sym) : Bool := r.isSome

section Routines

variable {K : Type}

/-- Loop body of `xfer`. -/
def xferBody (src dst : K) : SProg K := .seq (pushR dst) (popR src)

/-- Move every symbol of `src` onto `dst` (reversed), until `src` is empty. -/
def xfer (src dst : K) : SProg K := .seq (popR src) (.loop cubeIsSome (xferBody src dst))

/-- Empty a stack holding only bits. -/
def clearBits (k : K) : SProg K := .seq (popR k) (.loop optIsBit (popR k))

/-- Move the top field of `src` onto `F` (bits reversed) and onto `pk` (bits reversed, `mark`). -/
def unpackField (src F pk : K) : SProg K := .seq (moveBitsDup src F pk) (pushR pk)

/-- Move the top field of `src` onto `pk` (bits reversed, then its `mark`). -/
def parkField (src pk : K) : SProg K := .seq (moveBits src pk) (pushR pk)

/-- Push `mark`, then the number held reversed on `F` (natural order), onto `H`. -/
def pushFieldRev (F H : K) : SProg K := .seq (pushC H .mark) (moveBits F H)

/-- Push `mark`, then `2^n` (`n` held reversed on `F`), onto `H`. -/
def pow2Field (F H C Y kc u t : K) : SProg K :=
  .seq (pushC H .mark) (.seq (pushC H (.bit true)) (.seq (moveBits F C)
    (.seq (TMFw.W3s.concatCore H C Y kc u t) (clearBits C))))

theorem closed_xfer (src dst : K) : (xfer src dst).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, xfer, xferBody, pushR, popR]

theorem closed_clearBits (k : K) : (clearBits k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, clearBits, popR]

theorem closed_unpackField (src F pk : K) : (unpackField src F pk).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, unpackField, moveBitsDup, dupBody, pushR, popR]

theorem closed_parkField (src pk : K) : (parkField src pk).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, parkField, moveBits, moveBitsBody, pushR, popR]

theorem closed_pushFieldRev (F H : K) : (pushFieldRev F H).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, pushFieldRev, moveBits, moveBitsBody, pushR, popR, pushC]

theorem closed_pow2Field (F H C Y kc u t : K) : (pow2Field F H C Y kc u t).Closed := by
  have h := TMFw.W3s.concatCore_closed H C Y kc u t
  unfold Prog.Closed at h
  simp [Prog.Closed, Prog.FreeBelow, pow2Field, moveBits, moveBitsBody, pushR, popR, pushC,
    clearBits, h]

end Routines

section Evals

variable {K : Type} [DecidableEq K]

theorem xfer_loop_eval {src dst : K} (hne : src ≠ dst) :
    ∀ (L : List Sym) (S : K → List Sym), S src = L.tail →
      Eval [] (.loop cubeIsSome (xferBody src dst)) ⟨L.head?, S⟩
        ⟨none, Function.update (Function.update S src []) dst (L.reverse ++ S dst)⟩
        (3 * L.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false rfl).of_eq ?_ rfl
    have hS' : S src = [] := hS
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | x :: L, S, hS => by
    have hS' : S src = L := hS
    have e1 : Eval [] (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      (Eval.push ([] : List (SProg K)) dst (fun r : Option Sym => r.getD Sym.sep) (some x) S).of_eq rfl rfl
    have e2 : Eval [] (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨L.head?, Function.update (Function.update S dst (x :: S dst)) src L.tail⟩ 1 := by
      refine (Eval.pop ([] : List (SProg K)) src (fun (_ : Option Sym) (o : Option Sym) => o) _ _).of_eq ?_ rfl
      rw [Function.update_of_ne hne, hS']
    have ih := xfer_loop_eval hne L
      (Function.update (Function.update S dst (x :: S dst)) src L.tail)
      (Function.update_self _ _ _)
    refine (Eval.loop_true rfl (Eval.seq e1 e2) ih).of_eq ?_
      (by simp only [List.length_cons]; ring)
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    split_ifs <;> simp_all

/-- **`xfer`**: `src` is emptied onto `dst` (reversed); cost `3·|S src| + 2`. -/
theorem runs_xfer {src dst : K} (hne : src ≠ dst) (S : K → List Sym) :
    Runs (xfer src dst) S
      (Function.update (Function.update S src []) dst ((S src).reverse ++ S dst))
      (fun _ => True) (3 * (S src).length + 2) := by
  apply Runs.of_eval
  intro v
  have e1 : Eval [] (popR src) ⟨v, S⟩ ⟨(S src).head?, Function.update S src (S src).tail⟩ 1 :=
    (Eval.pop ([] : List (SProg K)) src (fun (_ : Option Sym) (o : Option Sym) => o) v S).of_eq rfl rfl
  have e2 := xfer_loop_eval hne (S src) (Function.update S src (S src).tail)
    (Function.update_self _ _ _)
  refine ⟨none, _, (Eval.seq e1 e2).of_eq ?_ rfl, trivial, by omega⟩
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem clearBits_loop_eval (k : K) :
    ∀ (es : List Bool) (S : K → List Sym), S k = (es.map Sym.bit).tail →
      Eval [] (.loop optIsBit (popR k)) ⟨(es.map Sym.bit).head?, S⟩
        ⟨none, Function.update S k []⟩ (2 * es.length + 1)
  | [], S, hS => by
    refine (Eval.loop_false rfl).of_eq ?_ rfl
    have hS' : S k = [] := hS
    show (⟨none, S⟩ : SSt K) = ⟨none, Function.update S k []⟩
    rw [← hS', Function.update_eq_self]
  | e :: es, S, hS => by
    have hS' : S k = es.map Sym.bit := hS
    have e1 : Eval [] (popR k) ⟨some (.bit e), S⟩
        ⟨(es.map Sym.bit).head?, Function.update S k (es.map Sym.bit).tail⟩ 1 := by
      refine (Eval.pop ([] : List (SProg K)) k (fun (_ : Option Sym) (o : Option Sym) => o) _ _).of_eq ?_ rfl
      rw [hS']
    have ih := clearBits_loop_eval k es (Function.update S k (es.map Sym.bit).tail)
      (Function.update_self _ _ _)
    refine (Eval.loop_true rfl e1 ih).of_eq ?_ (by simp only [List.length_cons]; ring)
    rw [Function.update_idem]

/-- **`clearBits`**: a stack holding only the bits `es` is emptied; cost `2·|es| + 2`. -/
theorem runs_clearBits (k : K) (es : List Bool) (S : K → List Sym) (hS : S k = es.map Sym.bit) :
    Runs (clearBits k) S (Function.update S k []) (fun _ => True) (2 * es.length + 2) := by
  apply Runs.of_eval
  intro v
  have e1 : Eval [] (popR k) ⟨v, S⟩
      ⟨(es.map Sym.bit).head?, Function.update S k (es.map Sym.bit).tail⟩ 1 := by
    refine (Eval.pop ([] : List (SProg K)) k (fun (_ : Option Sym) (o : Option Sym) => o) v S).of_eq ?_ rfl
    rw [hS]
  have e2 := clearBits_loop_eval k es (Function.update S k (es.map Sym.bit).tail)
    (Function.update_self _ _ _)
  refine ⟨none, _, (Eval.seq e1 e2).of_eq ?_ rfl, trivial, by omega⟩
  rw [Function.update_idem]

theorem natSyms_reverse (n : ℕ) : (natSyms n).reverse = (encodeNat n).reverse.map Sym.bit := by
  simp [natSyms]

/-- **`unpackField`**: the top field `natSyms n ++ [mark]` of `src` goes to `F` (bits reversed)
and to `pk` (bits reversed, then `mark`); cost `4·|n| + 3`. -/
theorem runs_unpackField {src F pk : K} (h1 : src ≠ F) (h2 : src ≠ pk) (h3 : F ≠ pk)
    (n : ℕ) (rest : List Sym) (S : K → List Sym) (hS : S src = natSyms n ++ Sym.mark :: rest) :
    Runs (unpackField src F pk) S
      (Function.update (Function.update (Function.update S src rest) F
        ((natSyms n).reverse ++ S F)) pk (Sym.mark :: ((natSyms n).reverse ++ S pk)))
      (fun _ => True) (4 * bitLen n + 3) := by
  apply Runs.of_eval
  intro v
  have e1 : Eval [] (popR src) ⟨v, S⟩
      ⟨((encodeNat n).map Sym.bit ++ Sym.mark :: rest).head?,
        Function.update S src ((encodeNat n).map Sym.bit ++ Sym.mark :: rest).tail⟩ 1 := by
    refine (Eval.pop ([] : List (SProg K)) src (fun (_ : Option Sym) (o : Option Sym) => o) v S).of_eq ?_ rfl
    rw [hS]
    rfl
  have e2 := moveBitsDup_loop_eval h1 h2 h3 [] (encodeNat n) (Sym.mark :: rest)
    (Function.update S src ((encodeNat n).map Sym.bit ++ Sym.mark :: rest).tail)
    (TermOK.cons rfl _) (Function.update_self _ _ _)
  have e3 := Eval.push ([] : List (SProg K)) pk (fun r : Option Sym => r.getD Sym.sep) (Sym.mark :: rest).head?
    (Function.update (Function.update (Function.update
      (Function.update S src ((encodeNat n).map Sym.bit ++ Sym.mark :: rest).tail) src
      (Sym.mark :: rest).tail) F ((encodeNat n).reverse.map Sym.bit ++
      Function.update S src ((encodeNat n).map Sym.bit ++ Sym.mark :: rest).tail F)) pk
      ((encodeNat n).reverse.map Sym.bit ++
        Function.update S src ((encodeNat n).map Sym.bit ++ Sym.mark :: rest).tail pk))
  refine ⟨some .mark, _, (Eval.seq (Eval.seq e1 e2) e3).of_eq ?_ rfl, trivial, ?_⟩
  · rw [natSyms_reverse]
    congr 1
    funext k
    simp only [Function.update_apply, List.tail_cons, List.head?_cons, Option.getD_some]
    split_ifs <;> simp_all
  · simp only [bitLen]
    omega

end Evals

section Evals2

variable {K : Type} [DecidableEq K]

/-- **`parkField`**: the top field of `src` goes to `pk` (bits reversed, then `mark`). -/
theorem runs_parkField {src pk : K} (hne : src ≠ pk) (n : ℕ) (rest : List Sym)
    (S : K → List Sym) (hS : S src = natSyms n ++ Sym.mark :: rest) :
    Runs (parkField src pk) S
      (Function.update (Function.update S src rest) pk
        (Sym.mark :: ((natSyms n).reverse ++ S pk)))
      (fun _ => True) (3 * bitLen n + 3) := by
  apply Runs.of_eval
  intro v
  have e1 := moveBits_eval hne [] v (encodeNat n) (Sym.mark :: rest) S (TermOK.cons rfl _) hS
  have e2 := Eval.push ([] : List (SProg K)) pk (fun r : Option Sym => r.getD Sym.sep) (Sym.mark :: rest).head?
    (Function.update (Function.update S src (Sym.mark :: rest).tail) pk
      ((encodeNat n).reverse.map Sym.bit ++ S pk))
  refine ⟨some .mark, _, (Eval.seq e1 e2).of_eq ?_ rfl, trivial, ?_⟩
  · rw [natSyms_reverse]
    congr 1
    funext k
    simp only [Function.update_apply, List.tail_cons, List.head?_cons, Option.getD_some]
    split_ifs <;> simp_all
  · simp only [bitLen]
    omega

/-- Push a constant. -/
theorem runs_pushC (k : K) (x : Sym) (S : K → List Sym) :
    Runs (pushC k x) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  Runs.of_eval fun v => ⟨v, 1, Eval.push ([] : List (SProg K)) k (fun (_ : Option Sym) => x) v S, trivial, le_rfl⟩

/-- `moveBits`, `Runs` form. -/
theorem runs_moveBits {src dst : K} (hne : src ≠ dst) (es : List Bool) (rest : List Sym)
    (S : K → List Sym) (hrest : TermOK rest) (hS : S src = es.map Sym.bit ++ rest) :
    Runs (moveBits src dst) S
      (Function.update (Function.update S src rest.tail) dst (es.reverse.map Sym.bit ++ S dst))
      (fun _ => True) (3 * es.length + 2) :=
  Runs.of_eval fun v => ⟨_, _, moveBits_eval hne [] v es rest S hrest hS, trivial, le_rfl⟩

/-- **`pushFieldRev`**: `mark`, then the number `n` held reversed on `F`, are pushed onto `H`
(natural order); `F` is emptied. -/
theorem runs_pushFieldRev {F H : K} (hne : F ≠ H) (n : ℕ) (S : K → List Sym)
    (hS : S F = (natSyms n).reverse) :
    Runs (pushFieldRev F H) S
      (Function.update (Function.update S F []) H (natSyms n ++ Sym.mark :: S H))
      (fun _ => True) (3 * bitLen n + 3) := by
  have r1 := runs_pushC H Sym.mark S
  have hF : Function.update S H (Sym.mark :: S H) F = (encodeNat n).reverse.map Sym.bit ++ [] := by
    rw [Function.update_of_ne hne, hS, natSyms_reverse, List.append_nil]
  have r2 := runs_moveBits hne (encodeNat n).reverse [] _ TermOK.nil hF
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r1 r2) ?_)
    (fun _ _ => trivial) ?_
  · funext k
    simp only [Function.update_apply, List.reverse_reverse, List.tail_nil]
    split_ifs <;> simp_all [natSyms]
  · simp only [List.length_reverse, bitLen]
    omega

/-- The W3 concatenation, `Runs` form (`WP/W3s/ConcatCore.lean`). -/
theorem runs_concatCore {x c y kc u t : K}
    (hxy : x ≠ y) (hxk : x ≠ kc) (hxt : x ≠ t) (hck : c ≠ kc) (hcu : c ≠ u) (hct : c ≠ t)
    (hyk : y ≠ kc) (hyt : y ≠ t) (hku : kc ≠ u) (hkt : kc ≠ t)
    (hi lo n : ℕ) (rx rc ry : List Sym) (hrx : TermOK rx) (hrc : TermOK rc) (hry : TermOK ry)
    (hlo : lo < 2 ^ n) (S : K → List Sym)
    (hx : S x = natSyms hi ++ rx) (hc : S c = natSyms n ++ rc) (hy : S y = natSyms lo ++ ry) :
    Runs (TMFw.W3s.concatCore x c y kc u t) S
      (Function.update (Function.update S x (natSyms (lo + hi * 2 ^ n) ++ rx)) y ry)
      (fun _ => True) (30 * (n + bitLen n + 1)) := by
  apply Runs.of_eval
  intro v
  obtain ⟨v', c', e, hc'⟩ := TMFw.W3s.concatCore_eval hxy hxk hxt hck hcu hct hyk hyt hku hkt
    [] v hi lo n rx rc ry hrx hrc hry hlo S hx hc hy
  exact ⟨v', c', e, trivial, hc'⟩

/-- The W3 increment, `Runs` form (`IntMulTM/Framework/Lib/Counter.lean`). -/
theorem runs_inc {k t : K} (hkt : k ≠ t) (n : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms n ++ rest) :
    Runs (inc k t) S (Function.update S k (natSyms (n + 1) ++ rest)) (fun _ => True)
      (6 * bitLen n + 9) := by
  apply Runs.of_eval
  intro v
  obtain ⟨c, hc, e⟩ := inc_eval hkt [] v (encodeNat n) rest S hrest hS
  refine ⟨some .mark, c, ?_, trivial, ?_⟩
  · rw [natSyms, encodeNat_succ]
    exact e
  · have := ones_le_length (encodeNat n)
    simp only [bitLen]
    omega

end Evals2

section Evals3

variable {K : Type} [DecidableEq K]

theorem hdrSyms_cons_append (n : ℕ) (fs : List ℕ) (L : List Sym) :
    hdrSyms (n :: fs) ++ L = natSyms n ++ Sym.mark :: (hdrSyms fs ++ L) := by
  simp [hdrSyms]

theorem hdrSyms_snoc_reverse (fs : List ℕ) (n : ℕ) :
    (hdrSyms (fs ++ [n])).reverse = Sym.mark :: ((natSyms n).reverse ++ (hdrSyms fs).reverse) := by
  simp [hdrSyms, List.flatMap_append, List.reverse_append]

/-- `unpackField` with explicit values of the receiving stacks. -/
theorem runs_unpackField' {src F pk : K} (h1 : src ≠ F) (h2 : src ≠ pk) (h3 : F ≠ pk)
    (n : ℕ) (fs : List ℕ) (rest : List Sym) (S : K → List Sym)
    (hS : S src = natSyms n ++ Sym.mark :: rest) (hF : S F = [])
    (hpk : S pk = (hdrSyms fs).reverse) :
    Runs (unpackField src F pk) S
      (Function.update (Function.update (Function.update S src rest) F (natSyms n).reverse) pk
        (hdrSyms (fs ++ [n])).reverse) (fun _ => True) (4 * bitLen n + 3) := by
  have h := runs_unpackField h1 h2 h3 n rest S hS
  rw [hF, hpk, List.append_nil, ← hdrSyms_snoc_reverse] at h
  exact h

/-- `parkField` with an explicit value of the parking stack. -/
theorem runs_parkField' {src pk : K} (hne : src ≠ pk) (n : ℕ) (fs : List ℕ) (rest : List Sym)
    (S : K → List Sym) (hS : S src = natSyms n ++ Sym.mark :: rest)
    (hpk : S pk = (hdrSyms fs).reverse) :
    Runs (parkField src pk) S
      (Function.update (Function.update S src rest) pk (hdrSyms (fs ++ [n])).reverse)
      (fun _ => True) (3 * bitLen n + 3) := by
  have h := runs_parkField hne n rest S hS
  rw [hpk, ← hdrSyms_snoc_reverse] at h
  exact h

/-- `xfer` with explicit values. -/
theorem runs_xfer' {src dst : K} (hne : src ≠ dst) (S : K → List Sym) (L M : List Sym)
    (hsrc : S src = L) (hdst : S dst = M) :
    Runs (xfer src dst) S (Function.update (Function.update S src []) dst (L.reverse ++ M))
      (fun _ => True) (3 * L.length + 2) := by
  have h := runs_xfer hne S
  rw [hsrc, hdst] at h
  exact h

/-- `pushFieldRev` with an explicit value of the target stack. -/
theorem runs_pushFieldRev' {F H : K} (hne : F ≠ H) (n : ℕ) (S : K → List Sym)
    (hS : S F = (natSyms n).reverse) (L : List Sym) (hH : S H = L) :
    Runs (pushFieldRev F H) S
      (Function.update (Function.update S F []) H (natSyms n ++ Sym.mark :: L))
      (fun _ => True) (3 * bitLen n + 3) := by
  have h := runs_pushFieldRev hne n S hS
  rw [hH] at h
  exact h

/-- **`pow2Field`**: `mark`, then `2^n` (`n` held reversed on `F`), are pushed onto `H`; `F` is
emptied; the counter stack `C` and the low-part stack `Y` are empty before and after. -/
theorem runs_pow2Field {F H C Y kc u t : K}
    (hFH : F ≠ H) (hFC : F ≠ C) (hFY : F ≠ Y) (hHC : H ≠ C) (hHY : H ≠ Y) (hHk : H ≠ kc)
    (hHt : H ≠ t) (hCY : C ≠ Y) (hCk : C ≠ kc) (hCu : C ≠ u) (hCt : C ≠ t) (hYk : Y ≠ kc)
    (hYt : Y ≠ t) (hku : kc ≠ u) (hkt : kc ≠ t)
    (n : ℕ) (S : K → List Sym) (hF : S F = (natSyms n).reverse) (hC : S C = []) (hY : S Y = [])
    (L : List Sym) (hH : S H = L) :
    Runs (pow2Field F H C Y kc u t) S
      (Function.update (Function.update S F []) H (natSyms (2 ^ n) ++ Sym.mark :: L))
      (fun _ => True) (36 * (n + bitLen n + 1)) := by
  obtain ⟨S1, hS1⟩ : ∃ S', S' = Function.update S H (Sym.mark :: L) := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S', S' = Function.update S1 H (Sym.bit true :: Sym.mark :: L) := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ S', S' = Function.update (Function.update S2 F []) C (natSyms n) :=
    ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ S', S' = Function.update (Function.update S3 H
      (natSyms (2 ^ n) ++ Sym.mark :: L)) Y [] := ⟨_, rfl⟩
  have r1 : Runs (pushC H .mark) S S1 (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_pushC H Sym.mark S) (by rw [hS1, hH])
  have r2 : Runs (pushC H (.bit true)) S1 S2 (fun _ => True) 1 :=
    WP.W9comp.runs_congr (runs_pushC H (Sym.bit true) S1) (by rw [hS2, hS1, Function.update_self])
  have hS2F : S2 F = (encodeNat n).reverse.map Sym.bit ++ [] := by
    rw [hS2, Function.update_of_ne hFH, hS1, Function.update_of_ne hFH, hF, natSyms_reverse,
      List.append_nil]
  have hS2C : S2 C = [] := by
    rw [hS2, Function.update_of_ne hHC.symm, hS1, Function.update_of_ne hHC.symm, hC]
  have r3 : Runs (moveBits F C) S2 S3 (fun _ => True) (3 * (encodeNat n).reverse.length + 2) :=
    WP.W9comp.runs_congr (runs_moveBits hFC (encodeNat n).reverse [] S2 TermOK.nil hS2F) (by
      rw [hS3, List.tail_nil, List.reverse_reverse, hS2C, List.append_nil]
      rfl)
  have hS3H : S3 H = natSyms 1 ++ Sym.mark :: L := by
    rw [hS3, Function.update_of_ne hHC, Function.update_of_ne hFH.symm, hS2, Function.update_self,
      natSyms_one_eq]
    rfl
  have hS3C : S3 C = natSyms n ++ [] := by rw [hS3, Function.update_self, List.append_nil]
  have hS3Y : S3 Y = natSyms 0 ++ [] := by
    rw [hS3, Function.update_of_ne hCY.symm, Function.update_of_ne hFY.symm, hS2,
      Function.update_of_ne hHY.symm, hS1, Function.update_of_ne hHY.symm, hY, natSyms_zero_eq]
    rfl
  have r4 : Runs (TMFw.W3s.concatCore H C Y kc u t) S3 S4 (fun _ => True)
      (30 * (n + bitLen n + 1)) :=
    WP.W9comp.runs_congr (runs_concatCore hHY hHk hHt hCk hCu hCt hYk hYt hku hkt 1 0 n
      (Sym.mark :: L) [] [] (TermOK.cons rfl _) TermOK.nil TermOK.nil (Nat.two_pow_pos n) S3
      hS3H hS3C hS3Y) (by rw [hS4, Nat.zero_add, one_mul])
  have hS4C : S4 C = (encodeNat n).map Sym.bit := by
    rw [hS4, Function.update_of_ne hCY, Function.update_of_ne hHC.symm, hS3C, List.append_nil]
    rfl
  have r5 := runs_clearBits C (encodeNat n) S4 hS4C
  have hall := WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 (WP.W9comp.runs_seq r3
    (WP.W9comp.runs_seq r4 r5)))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_
  · funext k
    rw [hS4, hS3, hS2, hS1]
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simp only [List.length_reverse, bitLen] at *
    omega

end Evals3

end SubNLogN.Machine.WalshCubeAux
