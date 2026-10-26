/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadSetupBase

/-!
# K5 spreading setup (`Bridge/SpreadSetup.lean`): states and step lemmas

The program `setupProg` (register `AReg`, private scratch `SX`) builds the 17 parameter rulers of
one spreading stage from the header `hdrSyms b.hdr` on `par` and the axis `natSyms i` on `ax`:

1. **Parse** (`progA`): with a guard `sep2` on the holding stack `G`, skip header fields onto `G`
   and build the base rulers `P, wI, wT, d` from the header and `i` from `ax` (`buildRuler`); the
   prefix product `∏_{j<i} t_j` (one `double` per zero bit of each `t_j = 2^a`, `prodFields`
   counted by the `i`-ruler), `t_i` (`buildRuler`) and `size t_i` (`cntField`); the ruler
   `d - 1 - i`; the suffix product (counted by that ruler); rewind `G` onto `par`.
2. **Derive** (`progB`): the output rulers by copies, subtractions and pushes; `W = min(2P+1, t_i)`
   by a simultaneous walk (`minRulers`) and `a₀` by a test of the leftover of `2P+1`.
3. **Clear** (`progC`): pop the base rulers.

Cost `O(|hdr| + R + s)`: unary work on `P ≤ wI ≤ s`, `wI, wT, size t_i ≤ s`, `t_i`, the products
`≤ R` (amortized doublings), `d, i ≤ |hdr|`.

**Scope (honest summary).** This file proves (no `sorry`) the state representation `st`, the
header bookkeeping (`tl`, `gk`, shape products) and the state-level step lemmas `rs_*`. The
programs `progA`, `progB`, `progC`, `setupProg`, their run lemmas and the theorem
`SpreadAux.spreadSetup_holds : SpreadSetupStmt` (no hypotheses) are in
`Bridge/SpreadSetupRun.lean`. Helpers live in `SubNLogN.Machine.Bridge.SpreadSetupAux`.
-/

namespace SubNLogN.Machine.Bridge.SpreadSetupAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Arith Computability
  SubNLogN.Machine.Bridge.SpreadAux SubNLogN.Math.Common SubNLogN.Math.Bridge

/-! ## Stacks and states -/

/-- Private scratch stacks of the setup kernel. -/
inductive SX
  | G | XP | XI | XT | Xd | Xi | Xti | Xsz | Xpre | Xsuf | Xk | X2 | C | Y | TX | TA | TB
  deriving DecidableEq

instance : Fintype SX where
  elems := {.G, .XP, .XI, .XT, .Xd, .Xi, .Xti, .Xsz, .Xpre, .Xsuf, .Xk, .X2, .C, .Y, .TX, .TA,
    .TB}
  complete := by intro x; cases x <;> simp

/-- Stacks of the setup kernel. -/
abbrev SK : Type := KLoc SetupN SX

/-- The header stack. -/
abbrev kp : SK := .inl .par
/-- The axis stack. -/
abbrev ka : SK := .inl .ax
/-- A ruler stack. -/
abbrev kr (r : RulerId) : SK := .inl (.ru r)
/-- A scratch stack. -/
abbrev ks (x : SX) : SK := .inr x

/-- A kernel state given by its components; the axis stack is that of `S`. -/
def st (S : SK → List Sym) (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) :
    SK → List Sym
  | .inl .par => p
  | .inl .ax => S (.inl .ax)
  | .inl (.ru r) => u r
  | .inr x => g x

@[simp] theorem st_par (S : SK → List Sym) (p g u) : st S p g u kp = p := rfl
@[simp] theorem st_ax (S : SK → List Sym) (p g u) : st S p g u ka = S ka := rfl
@[simp] theorem st_ru (S : SK → List Sym) (p g u) (r : RulerId) : st S p g u (kr r) = u r := rfl
@[simp] theorem st_x (S : SK → List Sym) (p g u) (x : SX) : st S p g u (ks x) = g x := rfl

theorem upd_par (S : SK → List Sym) (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym)
    (p' : List Sym) : Function.update (st S p g u) kp p' = st S p' g u := by
  funext k
  rcases k with (_ | _ | r) | x <;> simp [st, Function.update_apply]

theorem upd_x (S : SK → List Sym) (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym)
    (x : SX) (v : List Sym) :
    Function.update (st S p g u) (ks x) v = st S p (Function.update g x v) u := by
  funext k
  rcases k with (_ | _ | r) | y <;> simp [st, Function.update_apply]

theorem upd_ru (S : SK → List Sym) (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym)
    (r : RulerId) (v : List Sym) :
    Function.update (st S p g u) (kr r) v = st S p g (Function.update u r v) := by
  funext k
  rcases k with (_ | _ | r') | y <;> simp [st, Function.update_apply]

/-! ## Header bookkeeping -/

/-- The header from field `k` on, then the rest `rpar` of `par`. -/
def tl (b : BrPar) (rpar : List Sym) (k : ℕ) : List Sym := hdrSyms (b.hdr.drop k) ++ rpar

/-- The holding stack after the first `k` fields were moved onto it (above the guard). -/
def gk (b : BrPar) (k : ℕ) : List Sym := (hdrSyms (b.hdr.take k)).reverse ++ [Sym.sep2]

theorem tl_field (b : BrPar) (rpar : List Sym) (k x : ℕ) (hx : b.hdr[k]? = some x) :
    tl b rpar k = natSyms x ++ Sym.mark :: tl b rpar (k + 1) := by
  obtain ⟨hk, hkx⟩ := List.getElem?_eq_some_iff.mp hx
  unfold tl
  rw [List.drop_eq_getElem_cons hk, hkx, hdrSyms_cons']
  simp

theorem tl_take (b : BrPar) (rpar : List Sym) (k m : ℕ) :
    tl b rpar k = hdrSyms ((b.hdr.drop k).take m) ++ tl b rpar (k + m) := by
  unfold tl
  rw [← List.append_assoc, ← hdrSyms_append']
  congr 2
  conv_lhs => rw [← List.take_append_drop m (b.hdr.drop k)]
  rw [List.drop_drop]

theorem gk_take (b : BrPar) (k m : ℕ) :
    (hdrSyms ((b.hdr.drop k).take m)).reverse ++ gk b k = gk b (k + m) := by
  unfold gk
  rw [← List.append_assoc, ← List.reverse_append, ← hdrSyms_append', ← List.take_add]

theorem take_one_drop (b : BrPar) (k x : ℕ) (hx : b.hdr[k]? = some x) :
    (b.hdr.drop k).take 1 = [x] := by
  obtain ⟨hk, hkx⟩ := List.getElem?_eq_some_iff.mp hx
  rw [List.drop_eq_getElem_cons hk, hkx]
  rfl

theorem gk_field (b : BrPar) (k x : ℕ) (hx : b.hdr[k]? = some x) :
    (natSyms x ++ [Sym.mark]).reverse ++ gk b k = gk b (k + 1) := by
  have h := gk_take b k 1
  rw [take_one_drop b k x hx, hdrSyms_cons', hdrSyms_nil'] at h
  exact h

theorem hdr_len (b : BrPar) : b.hdr.length = 9 + b.d := by
  simp [BrPar.hdr] <;> omega

theorem hdr_get_t (b : BrPar) (j : Fin b.d) : b.hdr[9 + (j : ℕ)]? = some (b.t j) := by
  unfold BrPar.hdr
  rw [List.getElem?_append_right (by simp)]
  simp [List.getElem?_ofFn, j.isLt]

theorem hdr_drop_nine (b : BrPar) : b.hdr.drop 9 = List.ofFn b.t := by
  unfold BrPar.hdr
  exact List.drop_left' rfl

theorem tl_end (b : BrPar) (rpar : List Sym) : tl b rpar (9 + b.d) = rpar := by
  unfold tl
  rw [← hdr_len, List.drop_length, hdrSyms_nil', List.nil_append]

theorem gk_end (b : BrPar) : gk b (9 + b.d) = (hdrSyms b.hdr).reverse ++ [Sym.sep2] := by
  unfold gk
  rw [← hdr_len, List.take_length]

theorem tl_zero (b : BrPar) (rpar : List Sym) : tl b rpar 0 = hdrSyms b.hdr ++ rpar := by
  simp [tl]

theorem gk_zero (b : BrPar) : gk b 0 = [Sym.sep2] := by
  simp [gk, hdrSyms_nil']

theorem sep2_not_mem_hdrSyms' (fs : List ℕ) : Sym.sep2 ∉ hdrSyms fs := by
  simp [hdrSyms, natSyms]

/-! ## Products of the shape -/

/-- The prefix fields `t_0, …, t_{i-1}`. -/
theorem pre_fields (b : BrPar) (i : Fin b.d) :
    (b.hdr.drop 9).take i = List.ofFn (Fin.take i i.isLt.le b.t) := by
  rw [hdr_drop_nine, Fin.ofFn_take_eq_take_ofFn]

theorem pre_prod (b : BrPar) (i : Fin b.d) :
    (List.ofFn (Fin.take i i.isLt.le b.t)).prod = prefixProd b.t i := by
  rw [List.prod_ofFn, prefixProd_eq_prod_castLE]
  rfl

theorem pre_length (b : BrPar) (i : Fin b.d) :
    (List.ofFn (Fin.take i i.isLt.le b.t)).length = i := by
  simp

/-- The suffix fields `t_{i+1}, …, t_{d-1}`. -/
theorem suf_fields (b : BrPar) (i : Fin b.d) :
    b.hdr.drop (9 + (i : ℕ) + 1) = (List.ofFn b.t).drop ((i : ℕ) + 1) := by
  rw [show 9 + (i : ℕ) + 1 = 9 + ((i : ℕ) + 1) by omega, ← List.drop_drop, hdr_drop_nine]

theorem suf_length (b : BrPar) (i : Fin b.d) :
    ((List.ofFn b.t).drop ((i : ℕ) + 1)).length = b.d - 1 - i := by
  simp
  omega

theorem ofFn_split (b : BrPar) (i : Fin b.d) :
    List.ofFn b.t = List.ofFn (Fin.take i i.isLt.le b.t) ++
      b.t i :: (List.ofFn b.t).drop ((i : ℕ) + 1) := by
  rw [Fin.ofFn_take_eq_take_ofFn]
  have hi : (i : ℕ) < (List.ofFn b.t).length := by simp
  conv_lhs => rw [← List.take_append_drop i (List.ofFn b.t)]
  congr 1
  rw [List.drop_eq_getElem_cons hi]
  simp

theorem prod_ofFn_t (b : BrPar) : (List.ofFn b.t).prod = b.R := by
  rw [List.prod_ofFn]

theorem suf_prod (b : BrPar) (i : Fin b.d) (ht : ShapeOK b.t) :
    ((List.ofFn b.t).drop ((i : ℕ) + 1)).prod = suffixProd b.t i := by
  have h1 := prefixProd_mul_mul_suffixProd b.t i
  have h2 := prod_ofFn_t b
  rw [ofFn_split b i, List.prod_append, List.prod_cons, pre_prod] at h2
  have hpos : 0 < prefixProd b.t i * b.t i := by
    apply Nat.mul_pos
    · exact Finset.prod_pos fun j _ => by have := (ht j).1; omega
    · have := (ht i).1; omega
  have h3 : prefixProd b.t i * b.t i * ((List.ofFn b.t).drop ((i : ℕ) + 1)).prod =
      prefixProd b.t i * b.t i * suffixProd b.t i := by
    rw [h1, mul_assoc]
    exact h2
  exact Nat.eq_of_mul_eq_mul_left hpos h3

theorem pow_fields (b : BrPar) (ht : ShapeOK b.t) :
    ∀ f ∈ List.ofFn b.t, ∃ a, 1 ≤ a ∧ f = 2 ^ a := by
  intro f hf
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
  obtain ⟨h2, a, ha⟩ := ht j
  refine ⟨a, ?_, ha⟩
  rcases a with _ | a
  · simp at ha; omega
  · omega

theorem hdr_seg0 (b : BrPar) : (b.hdr.drop 0).take 1 = [b.p] := rfl
theorem hdr_seg1 (b : BrPar) : (b.hdr.drop 1).take 2 = [b.P, b.ω] := rfl
theorem hdr_seg2 (b : BrPar) : (b.hdr.drop 3).take 1 = [b.wI] := rfl
theorem hdr_seg3 (b : BrPar) : (b.hdr.drop 4).take 4 = [b.wT, b.wOut, b.pIn, b.wIn] := rfl
theorem hdr_seg4 (b : BrPar) : (b.hdr.drop 8).take 1 = [b.d] := rfl
theorem hdr_get1 (b : BrPar) : b.hdr[1]? = some b.P := rfl
theorem hdr_get3 (b : BrPar) : b.hdr[3]? = some b.wI := rfl
theorem hdr_get4 (b : BrPar) : b.hdr[4]? = some b.wT := rfl
theorem hdr_get8 (b : BrPar) : b.hdr[8]? = some b.d := rfl

/-! ## State-level step lemmas -/

section Steps

variable (S : SK → List Sym)

theorem rs_pushx (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x : SX) (y : Sym) :
    Runs (pushS (ks x) y) (st S p g u) (st S p (Function.update g x (y :: g x)) u)
      (fun _ => True) 1 := by
  have h := runs_pushS' (ks x) y (st S p g u)
  rwa [st_x, upd_x] at h

theorem rs_pushr (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (r : RulerId) :
    Runs (pushS (kr r) .mark) (st S p g u) (st S p g (Function.update u r (.mark :: u r)))
      (fun _ => True) 1 := by
  have h := runs_pushS' (kr r) .mark (st S p g u)
  rwa [st_ru, upd_ru] at h

theorem rs_dropx (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x : SX)
    (L : List Sym) (hx : g x = .mark :: L) :
    Runs (drop1 (ks x)) (st S p g u) (st S p (Function.update g x L) u) (fun _ => True) 1 := by
  have h := runs_drop1' (ks x) (st S p g u) .mark L (by simpa using hx)
  rwa [upd_x] at h

theorem rs_dropr (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (r : RulerId)
    (L : List Sym) (hr : u r = .mark :: L) :
    Runs (drop1 (kr r)) (st S p g u) (st S p g (Function.update u r L)) (fun _ => True) 1 := by
  have h := runs_drop1' (kr r) (st S p g u) .mark L (by simpa using hr)
  rwa [upd_ru] at h

theorem rs_copyxr (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x : SX)
    (r : RulerId) (n : ℕ) (hxT : x ≠ .TX) (hx : g x = List.replicate n .mark)
    (hT : g .TX = []) :
    Runs (copyR (ks x) (ks .TX) (kr r)) (st S p g u)
      (st S p g (Function.update u r (List.replicate n .mark ++ u r))) (fun _ => True)
      (9 * n + 4) := by
  have h := runs_copyR' (R := ks x) (X := ks .TX) (D := kr r) (by simpa using hxT) (by simp)
    (by simp) n [] (st S p g u) (by simp) (by simpa using hx) (by simp [hT])
  rwa [st_ru, upd_ru] at h

theorem rs_copyxx (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x y : SX)
    (n : ℕ) (hxT : x ≠ .TX) (hxy : x ≠ y) (hyT : y ≠ .TX) (hx : g x = List.replicate n .mark)
    (hT : g .TX = []) :
    Runs (copyR (ks x) (ks .TX) (ks y)) (st S p g u)
      (st S p (Function.update g y (List.replicate n .mark ++ g y)) u) (fun _ => True)
      (9 * n + 4) := by
  have h := runs_copyR' (R := ks x) (X := ks .TX) (D := ks y) (by simpa using hxT)
    (by simpa using hxy) (by simpa using hyT.symm) n [] (st S p g u) (by simp) (by simpa using hx)
    (by simp [hT])
  rwa [st_x, upd_x] at h

theorem rs_copyrr (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (r r' : RulerId)
    (n : ℕ) (hrr : r ≠ r') (hr : u r = List.replicate n .mark) (hT : g .TX = []) :
    Runs (copyR (kr r) (ks .TX) (kr r')) (st S p g u)
      (st S p g (Function.update u r' (List.replicate n .mark ++ u r'))) (fun _ => True)
      (9 * n + 4) := by
  have h := runs_copyR' (R := kr r) (X := ks .TX) (D := kr r') (by simp) (by simpa using hrr)
    (by simp) n [] (st S p g u) (by simp) (by simpa using hr) (by simp [hT])
  rwa [st_ru, upd_ru] at h

theorem rs_subrr (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (r r' : RulerId)
    (n k : ℕ) (hrr : r ≠ r') (hr : u r = List.replicate n .mark)
    (hr' : u r' = List.replicate (n + k) .mark) (hT : g .TX = []) :
    Runs (subR (kr r) (ks .TX) (kr r')) (st S p g u)
      (st S p g (Function.update u r' (List.replicate k .mark))) (fun _ => True) (9 * n + 4) := by
  have h := runs_subR' (R := kr r) (X := ks .TX) (D := kr r') (by simp) (by simpa using hrr)
    (by simp) n k [] [] (st S p g u) (by simp) (by simpa using hr) (by simp [hT])
    (by simpa using hr')
  rw [List.append_nil, upd_ru] at h
  exact h

theorem rs_subxx (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x y : SX)
    (n k : ℕ) (hxT : x ≠ .TX) (hxy : x ≠ y) (hyT : y ≠ .TX) (hx : g x = List.replicate n .mark)
    (hy : g y = List.replicate (n + k) .mark) (hT : g .TX = []) :
    Runs (subR (ks x) (ks .TX) (ks y)) (st S p g u)
      (st S p (Function.update g y (List.replicate k .mark)) u) (fun _ => True) (9 * n + 4) := by
  have h := runs_subR' (R := ks x) (X := ks .TX) (D := ks y) (by simpa using hxT)
    (by simpa using hxy) (by simpa using hyT.symm) n k [] [] (st S p g u) (by simp)
    (by simpa using hx) (by simp [hT]) (by simpa using hy)
  rw [List.append_nil, upd_x] at h
  exact h

theorem rs_movexr (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x : SX)
    (r : RulerId) (n : ℕ) (hx : g x = List.replicate n .mark) :
    Runs (moveMarks (ks x) (kr r)) (st S p g u)
      (st S p (Function.update g x []) (Function.update u r (List.replicate n .mark ++ u r)))
      (fun _ => True) (4 * n + 2) := by
  have h := runs_moveMarks' (X := ks x) (R := kr r) (by simp) n [] (st S p g u) (by simp)
    (by simpa using hx)
  rwa [upd_x, st_ru, upd_ru] at h

theorem rs_movexx (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x y : SX)
    (n : ℕ) (hxy : x ≠ y) (hx : g x = List.replicate n .mark) :
    Runs (moveMarks (ks x) (ks y)) (st S p g u)
      (st S p (Function.update (Function.update g x []) y (List.replicate n .mark ++ g y)) u)
      (fun _ => True) (4 * n + 2) := by
  have h := runs_moveMarks' (X := ks x) (R := ks y) (by simpa using hxy) n [] (st S p g u)
    (by simp) (by simpa using hx)
  rwa [upd_x, st_x, upd_x] at h

theorem rs_clearx (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x : SX) (n : ℕ)
    (hx : g x = List.replicate n .mark) :
    Runs (clearMarks (ks x)) (st S p g u) (st S p (Function.update g x []) u) (fun _ => True)
      (3 * n + 2) := by
  have h := runs_clearMarks' (R := ks x) n [] (st S p g u) (by simp) (by simpa using hx)
  rwa [upd_x] at h

theorem rs_buildp (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x : SX) (n : ℕ)
    (rest : List Sym) (hxC : x ≠ .C) (hxY : x ≠ .Y) (hp : p = natSyms n ++ Sym.mark :: rest)
    (hx : g x = []) :
    Runs (buildRuler kp (ks x) (ks .C) (ks .Y)) (st S p g u)
      (st S p (Function.update g x (List.replicate n .mark)) u) (fun _ => True)
      (9 * n + 16 * bitLen n + 8) := by
  have h := runs_buildRuler' (N := kp) (R := ks x) (C := ks .C) (Y := ks .Y) (by simp) (by simp)
    (by simp) (by simpa using hxC) (by simpa using hxY) (by simp) n (Sym.mark :: rest) []
    (st S p g u) (termOK_mark rest) (by simp) (by simpa using hp) (by simpa using hx)
  rwa [List.append_nil, upd_x] at h

theorem rs_builda (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x : SX) (n : ℕ)
    (rax : List Sym) (hxC : x ≠ .C) (hxY : x ≠ .Y) (ha : S ka = natSyms n ++ rax)
    (hrax : TermOK rax) (hx : g x = []) :
    Runs (buildRuler ka (ks x) (ks .C) (ks .Y)) (st S p g u)
      (st S p (Function.update g x (List.replicate n .mark)) u) (fun _ => True)
      (9 * n + 16 * bitLen n + 8) := by
  have h := runs_buildRuler' (N := ka) (R := ks x) (C := ks .C) (Y := ks .Y) (by simp) (by simp)
    (by simp) (by simpa using hxC) (by simpa using hxY) (by simp) n rax [] (st S p g u) hrax
    (by simp) (by simpa using ha) (by simpa using hx)
  rwa [List.append_nil, upd_x] at h

theorem rs_minW (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (a c : ℕ)
    (h2 : g .X2 = List.replicate a .mark) (hc : g .Xti = List.replicate c .mark) :
    Runs (minRulers (ks .X2) (ks .Xti) (ks .TA) (ks .TB) (kr .W)) (st S p g u)
      (st S p (Function.update (Function.update (Function.update (Function.update g .X2
        (List.replicate (a - min a c) .mark)) .Xti (List.replicate (c - min a c) .mark)) .TA
        (List.replicate (min a c) .mark ++ g .TA)) .TB (List.replicate (min a c) .mark ++ g .TB))
        (Function.update u .W (List.replicate (min a c) .mark ++ u .W)))
      (fun _ => True) (8 * min a c + 3) := by
  have h := runs_minRulers' (A := ks .X2) (B := ks .Xti) (TA := ks .TA) (TB := ks .TB)
    (W := kr .W) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) a c [] [] (by simp) (by simp) (st S p g u) (by simpa using h2)
    (by simpa using hc)
  simp only [List.append_nil, st_x, st_ru, upd_x, upd_ru] at h
  exact h

theorem rs_cieMark (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (L : List Sym)
    (h2 : g .X2 = .mark :: L) :
    Runs (copyIfEmpty (ks .X2) (ks .XP) (ks .TX) (kr .a0)) (st S p g u) (st S p g u)
      (fun _ => True) 3 :=
  runs_copyIfEmpty_mark (st S p g u) L (by simpa using h2)

theorem rs_cieEmpty (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (n : ℕ)
    (h2 : g .X2 = []) (hP : g .XP = List.replicate n .mark) (hT : g .TX = []) :
    Runs (copyIfEmpty (ks .X2) (ks .XP) (ks .TX) (kr .a0)) (st S p g u)
      (st S p g (Function.update u .a0 (List.replicate n .mark ++ u .a0))) (fun _ => True)
      (9 * n + 6) := by
  have h := runs_copyIfEmpty_empty (A := ks .X2) (R := ks .XP) (X := ks .TX) (D := kr .a0)
    (by simp) (by simp) (by simp) n [] (st S p g u) (by simp) (by simpa using hP)
    (by simp [hT]) (by simp [h2])
  rwa [st_ru, upd_ru] at h

end Steps

/-! ## Header-level step lemmas -/

section HSteps

variable (S : SK → List Sym) (b : BrPar) (rpar : List Sym)

theorem rs_skipk (g : SX → List Sym) (u : RulerId → List Sym) (k m : ℕ) (hG : g .G = gk b k) :
    Runs (skipFlds kp (ks .G) ((b.hdr.drop k).take m).length) (st S (tl b rpar k) g u)
      (st S (tl b rpar (k + m)) (Function.update g .G (gk b (k + m))) u) (fun _ => True)
      (4 * (hdrSyms ((b.hdr.drop k).take m)).length + 1) := by
  have h := runs_skipFlds' (A := kp) (B := ks .G) (by simp) ((b.hdr.drop k).take m)
    (tl b rpar (k + m)) (st S (tl b rpar k) g u) (by simpa using tl_take b rpar k m)
  rwa [upd_par, st_x, upd_x, hG, gk_take] at h

theorem rs_buildk (g : SX → List Sym) (u : RulerId → List Sym) (x : SX) (k n : ℕ)
    (hxC : x ≠ .C) (hxY : x ≠ .Y) (hn : b.hdr[k]? = some n) (hx : g x = []) :
    Runs (buildRuler kp (ks x) (ks .C) (ks .Y)) (st S (tl b rpar k) g u)
      (st S (tl b rpar k) (Function.update g x (List.replicate n .mark)) u) (fun _ => True)
      (9 * n + 16 * bitLen n + 8) :=
  rs_buildp S _ g u x n (tl b rpar (k + 1)) hxC hxY (tl_field b rpar k n hn) hx

theorem rs_cntk (g : SX → List Sym) (u : RulerId → List Sym) (k n : ℕ) (hn : b.hdr[k]? = some n)
    (hG : g .G = gk b k) (hz : g .Xsz = []) :
    Runs (cntField kp (ks .G) (ks .Xsz)) (st S (tl b rpar k) g u)
      (st S (tl b rpar (k + 1)) (Function.update (Function.update g .G (gk b (k + 1))) .Xsz
        (List.replicate (bitLen n) .mark)) u) (fun _ => True) (5 * bitLen n + 4) := by
  have h := runs_cntField' (A := kp) (B := ks .G) (X := ks .Xsz) (by simp) (by simp) (by simp) n
    (tl b rpar (k + 1)) (st S (tl b rpar k) g u) (by simpa using tl_field b rpar k n hn)
  rwa [upd_par, st_x, upd_x, st_x, upd_x, hG, hz, List.append_nil, gk_field b k n hn] at h

theorem rs_prodk (g : SX → List Sym) (u : RulerId → List Sym) (ct x : SX) (k m m0 : ℕ)
    (hpow : ∀ f ∈ (b.hdr.drop k).take m, ∃ a, 1 ≤ a ∧ f = 2 ^ a)
    (hct1 : ct ≠ .TX) (hct2 : ct ≠ .G) (hct3 : ct ≠ x) (hct4 : ct ≠ .Y) (hx1 : x ≠ .TX)
    (hx2 : x ≠ .G) (hx3 : x ≠ .Y)
    (hct : g ct = List.replicate ((b.hdr.drop k).take m).length .mark) (hT : g .TX = [])
    (hG : g .G = gk b k) (hx : g x = List.replicate m0 .mark) (hY : g .Y = []) :
    Runs (prodFields (ks ct) (ks .TX) kp (ks .G) (ks x) (ks .Y)) (st S (tl b rpar k) g u)
      (st S (tl b rpar (k + m)) (Function.update (Function.update g .G (gk b (k + m))) x
        (List.replicate (m0 * ((b.hdr.drop k).take m).prod) .mark)) u) (fun _ => True)
      (18 * (m0 * ((b.hdr.drop k).take m).prod) + 10 * (hdrSyms ((b.hdr.drop k).take m)).length +
        4 * ((b.hdr.drop k).take m).length + 4) := by
  have h := runs_prodFields' (Ct := ks ct) (W := ks .TX) (A := kp) (B := ks .G) (X := ks x)
    (Y := ks .Y) (by simpa using hct1) (by simp) (by simpa using hct2) (by simpa using hct3)
    (by simpa using hct4) (by simp) (by simp) (by simpa using hx1.symm) (by simp) (by simp)
    (by simp) (by simp) (by simpa using hx2.symm) (by simp) (by simpa using hx3)
    ((b.hdr.drop k).take m) hpow m0 [] (tl b rpar (k + m)) [] [] (by simp) (by simp) (by simp)
    (st S (tl b rpar k) g u) (by simpa using hct) (by simp [hT])
    (by simpa using tl_take b rpar k m) (by simpa using hx) (by simpa using hY)
  rwa [upd_par, st_x, upd_x, upd_x, hG, gk_take, List.append_nil] at h

theorem rs_rewindk (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym)
    (hG : g .G = gk b (9 + b.d)) :
    Runs (rewindG (ks .G) kp) (st S p g u) (st S (hdrSyms b.hdr ++ p) (Function.update g .G [])
      u) (fun _ => True) (3 * (hdrSyms b.hdr).length + 2) := by
  have h := runs_rewindG' (G := ks .G) (A := kp) (by simp) (hdrSyms b.hdr).reverse []
    (st S p g u) (by rw [List.mem_reverse]; exact sep2_not_mem_hdrSyms' _)
    (by simp [hG, gk_end])
  rwa [upd_x, st_par, upd_par, List.reverse_reverse, List.length_reverse] at h

end HSteps

end SubNLogN.Machine.Bridge.SpreadSetupAux
