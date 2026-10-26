/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.SpreadSetup
import IntMulTM.SpecFacts

/-!
# K5 spreading setup, runs (`Bridge/SpreadSetupRun.lean`): proof of `SpreadSetupStmt`

The program `setupProg = progA; progB; progC` (register `AReg`, private scratch `SX`) and its
phase lemmas `runs_progA` (parse, cost `≤ 200·Λ`), `runs_progB` (derive the 17 rulers,
`≤ 300·Λ`), `runs_progC` (clear the scratch, `≤ 30·Λ`), with `Λ = |hdr| + R + s + 1`; then
`SpreadAux.spreadSetup_holds : SpreadSetupStmt` with the constant `1000` (using
`|hdr| + 1 ≤ setup`).

Phase B and C states are kept in *counter form* `st S p (rep c) (rep d)` (every scratch / ruler
stack is a run of `mark`s given by its length), and every step lemma takes the new lengths as
explicit arguments, so that the composed states stay linear in size.

**Scope (honest summary).** Everything here is proved (no `sorry`, no hypotheses beyond the
premises of the statement). Helpers live in `SubNLogN.Machine.Bridge.SpreadSetupAux`.
-/

namespace SubNLogN.Machine.Bridge.SpreadSetupAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Arith Computability
  SubNLogN.Machine.Bridge.SpreadAux SubNLogN.Math.Common SubNLogN.Math.Bridge

/-! ## Composition (specialized) -/

theorem rseq {P Q : AProg SK} {S1 S2 S3 : SK → List Sym} {T1 T2 : ℕ}
    (h1 : Runs P S1 S2 (fun _ => True) T1) (h2 : Runs Q S2 S3 (fun _ => True) T2) :
    Runs (.seq P Q) S1 S3 (fun _ => True) (T1 + T2) :=
  WP.W9comp.runs_seq h1 h2

theorem runs_pre {P : AProg SK} {S0 S S' : SK → List Sym} {T : ℕ}
    (h : Runs P S0 S' (fun _ => True) T) (he : S0 = S) : Runs P S S' (fun _ => True) T :=
  he ▸ h

theorem closed_seq {p q : AProg SK} (hp : p.Closed) (hq : q.Closed) : (Prog.seq p q).Closed := by
  simp only [Prog.Closed] at hp hq ⊢
  exact ⟨hp, hq⟩

theorem closed_pushS' (k : SK) (y : Sym) : (pushS k y).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, pushS]

theorem closed_drop1' (k : SK) : (drop1 k).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, drop1]

theorem closed_buildRuler' (N R C Y : SK) : (buildRuler N R C Y).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, buildRuler, brLoop, brBody, double, dblLoop, moveMarks,
    mmLoop, mvBits, mvLoop, peekQ, peekR, drop1, pushS, skipA]

theorem closed_moveMarks' (X R : SK) : (moveMarks X R).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, moveMarks, mmLoop, peekR, drop1, pushS]

theorem closed_clearMarks' (R : SK) : (clearMarks R).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, clearMarks, cmLoop, peekR, drop1]

/-! ## Counter form -/

/-- A family of `mark` runs given by their lengths. -/
def rep {α : Type} (c : α → ℕ) : α → List Sym := fun x => List.replicate (c x) .mark

@[simp] theorem rep_apply {α : Type} (c : α → ℕ) (x : α) :
    rep c x = List.replicate (c x) .mark := rfl

theorem upd_rep {α : Type} [DecidableEq α] (c : α → ℕ) (x : α) (n : ℕ) :
    Function.update (rep c) x (List.replicate n .mark) = rep (Function.update c x n) := by
  funext y
  by_cases h : y = x
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem upd_rep0 {α : Type} [DecidableEq α] (c : α → ℕ) (x : α) :
    Function.update (rep c) x [] = rep (Function.update c x 0) :=
  upd_rep c x 0

theorem rep_cons (n : ℕ) (h : 1 ≤ n) :
    List.replicate n Sym.mark = .mark :: List.replicate (n - 1) .mark := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rfl

section CSteps

variable (S : SK → List Sym) (p : List Sym)

theorem cs_pushx (c : SX → ℕ) (d : RulerId → ℕ) (x : SX) (n : ℕ) (hx : c x = n) :
    Runs (pushS (ks x) .mark) (st S p (rep c) (rep d))
      (st S p (rep (Function.update c x (n + 1))) (rep d)) (fun _ => True) 1 := by
  have h := rs_pushx S p (rep c) (rep d) x .mark
  rwa [rep_apply, hx, ← List.replicate_succ, upd_rep] at h

theorem cs_pushr (c : SX → ℕ) (d : RulerId → ℕ) (r : RulerId) (n : ℕ) (hr : d r = n) :
    Runs (pushS (kr r) .mark) (st S p (rep c) (rep d))
      (st S p (rep c) (rep (Function.update d r (n + 1)))) (fun _ => True) 1 := by
  have h := rs_pushr S p (rep c) (rep d) r
  rwa [rep_apply, hr, ← List.replicate_succ, upd_rep] at h

theorem cs_dropr (c : SX → ℕ) (d : RulerId → ℕ) (r : RulerId) (n : ℕ) (hr : d r = n + 1) :
    Runs (drop1 (kr r)) (st S p (rep c) (rep d))
      (st S p (rep c) (rep (Function.update d r n))) (fun _ => True) 1 := by
  have h := rs_dropr S p (rep c) (rep d) r (List.replicate n .mark)
    (by rw [rep_apply, hr, List.replicate_succ])
  rwa [upd_rep] at h

theorem cs_copyxr (c : SX → ℕ) (d : RulerId → ℕ) (x : SX) (r : RulerId) (n m : ℕ)
    (hxT : x ≠ .TX) (hT : c .TX = 0) (hx : c x = n) (hr : d r = m) :
    Runs (copyR (ks x) (ks .TX) (kr r)) (st S p (rep c) (rep d))
      (st S p (rep c) (rep (Function.update d r (n + m)))) (fun _ => True) (9 * n + 4) := by
  have h := rs_copyxr S p (rep c) (rep d) x r n hxT (by rw [rep_apply, hx]) (by simp [hT])
  rwa [rep_apply, hr, List.replicate_append_replicate, upd_rep] at h

theorem cs_copyrr (c : SX → ℕ) (d : RulerId → ℕ) (r r' : RulerId) (n m : ℕ) (hrr : r ≠ r')
    (hT : c .TX = 0) (hr : d r = n) (hr' : d r' = m) :
    Runs (copyR (kr r) (ks .TX) (kr r')) (st S p (rep c) (rep d))
      (st S p (rep c) (rep (Function.update d r' (n + m)))) (fun _ => True) (9 * n + 4) := by
  have h := rs_copyrr S p (rep c) (rep d) r r' n hrr (by rw [rep_apply, hr]) (by simp [hT])
  rwa [rep_apply, hr', List.replicate_append_replicate, upd_rep] at h

theorem cs_copyxx (c : SX → ℕ) (d : RulerId → ℕ) (x y : SX) (n m : ℕ) (hxT : x ≠ .TX)
    (hxy : x ≠ y) (hyT : y ≠ .TX) (hT : c .TX = 0) (hx : c x = n) (hy : c y = m) :
    Runs (copyR (ks x) (ks .TX) (ks y)) (st S p (rep c) (rep d))
      (st S p (rep (Function.update c y (n + m))) (rep d)) (fun _ => True) (9 * n + 4) := by
  have h := rs_copyxx S p (rep c) (rep d) x y n hxT hxy hyT (by rw [rep_apply, hx])
    (by simp [hT])
  rwa [rep_apply, hy, List.replicate_append_replicate, upd_rep] at h

theorem cs_subrr (c : SX → ℕ) (d : RulerId → ℕ) (r r' : RulerId) (n k : ℕ) (hrr : r ≠ r')
    (hT : c .TX = 0) (hr : d r = n) (hr' : d r' = n + k) :
    Runs (subR (kr r) (ks .TX) (kr r')) (st S p (rep c) (rep d))
      (st S p (rep c) (rep (Function.update d r' k))) (fun _ => True) (9 * n + 4) := by
  have h := rs_subrr S p (rep c) (rep d) r r' n k hrr (by rw [rep_apply, hr])
    (by rw [rep_apply, hr']) (by simp [hT])
  rwa [upd_rep] at h

theorem cs_movexr (c : SX → ℕ) (d : RulerId → ℕ) (x : SX) (r : RulerId) (n m : ℕ)
    (hx : c x = n) (hr : d r = m) :
    Runs (moveMarks (ks x) (kr r)) (st S p (rep c) (rep d))
      (st S p (rep (Function.update c x 0)) (rep (Function.update d r (n + m))))
      (fun _ => True) (4 * n + 2) := by
  have h := rs_movexr S p (rep c) (rep d) x r n (by rw [rep_apply, hx])
  rwa [rep_apply, hr, List.replicate_append_replicate, upd_rep, upd_rep0] at h

theorem cs_movexx (c : SX → ℕ) (d : RulerId → ℕ) (x y : SX) (n m : ℕ) (hxy : x ≠ y)
    (hx : c x = n) (hy : c y = m) :
    Runs (moveMarks (ks x) (ks y)) (st S p (rep c) (rep d))
      (st S p (rep (Function.update (Function.update c x 0) y (n + m))) (rep d))
      (fun _ => True) (4 * n + 2) := by
  have h := rs_movexx S p (rep c) (rep d) x y n hxy (by rw [rep_apply, hx])
  rwa [rep_apply, hy, List.replicate_append_replicate, upd_rep0, upd_rep] at h

theorem cs_clearx (c : SX → ℕ) (d : RulerId → ℕ) (x : SX) (n : ℕ) (hx : c x = n) :
    Runs (clearMarks (ks x)) (st S p (rep c) (rep d))
      (st S p (rep (Function.update c x 0)) (rep d)) (fun _ => True) (3 * n + 2) := by
  have h := rs_clearx S p (rep c) (rep d) x n (by rw [rep_apply, hx])
  rwa [upd_rep0] at h

theorem cs_minW (c : SX → ℕ) (d : RulerId → ℕ) (a e ta tb w : ℕ) (h2 : c .X2 = a)
    (he : c .Xti = e) (hTA : c .TA = ta) (hTB : c .TB = tb) (hW : d .W = w) :
    Runs (minRulers (ks .X2) (ks .Xti) (ks .TA) (ks .TB) (kr .W)) (st S p (rep c) (rep d))
      (st S p (rep (Function.update (Function.update (Function.update (Function.update c .X2
        (a - min a e)) .Xti (e - min a e)) .TA (min a e + ta)) .TB (min a e + tb)))
        (rep (Function.update d .W (min a e + w)))) (fun _ => True) (8 * min a e + 3) := by
  have h := rs_minW S p (rep c) (rep d) a e (by rw [rep_apply, h2]) (by rw [rep_apply, he])
  simp only [rep_apply, hTA, hTB, hW, List.replicate_append_replicate, upd_rep] at h
  exact h

theorem cs_cie (c : SX → ℕ) (d : RulerId → ℕ) (n2 nP m v : ℕ)
    (hv : v = if n2 = 0 then nP else 0) (hT : c .TX = 0) (h2 : c .X2 = n2) (hP : c .XP = nP)
    (ha : d .a0 = m) :
    Runs (copyIfEmpty (ks .X2) (ks .XP) (ks .TX) (kr .a0)) (st S p (rep c) (rep d))
      (st S p (rep c) (rep (Function.update d .a0 (v + m)))) (fun _ => True) (9 * nP + 6) := by
  subst hv
  by_cases hn : n2 = 0
  · have h := rs_cieEmpty S p (rep c) (rep d) nP (by simp [h2, hn]) (by rw [rep_apply, hP])
      (by simp [hT])
    rw [rep_apply, ha, List.replicate_append_replicate, upd_rep] at h
    rw [if_pos hn]
    exact h
  · obtain ⟨k, hk⟩ : ∃ k, n2 = k + 1 := ⟨n2 - 1, by omega⟩
    have h := rs_cieMark S p (rep c) (rep d) (List.replicate k .mark)
      (by rw [rep_apply, h2, hk, List.replicate_succ])
    refine WP.W9comp.runs_mono (WP.W9comp.runs_congr h ?_) (fun _ _ => trivial) (by omega)
    rw [if_neg hn, Nat.zero_add, ← ha, Function.update_eq_self]

end CSteps

/-! ## Phase-A step variants (explicit values) -/

section AVar

variable (S : SK → List Sym)

theorem rs_pushx' (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x : SX) (y : Sym)
    (L : List Sym) (hx : g x = L) :
    Runs (pushS (ks x) y) (st S p g u) (st S p (Function.update g x (y :: L)) u)
      (fun _ => True) 1 := by
  have h := rs_pushx S p g u x y
  rwa [hx] at h

theorem rs_push1 (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x : SX)
    (hx : g x = []) :
    Runs (pushS (ks x) .mark) (st S p g u)
      (st S p (Function.update g x (List.replicate 1 .mark)) u) (fun _ => True) 1 :=
  rs_pushx' S p g u x .mark [] hx

theorem rs_copyxx' (p : List Sym) (g : SX → List Sym) (u : RulerId → List Sym) (x y : SX)
    (n m : ℕ) (hxT : x ≠ .TX) (hxy : x ≠ y) (hyT : y ≠ .TX) (hx : g x = List.replicate n .mark)
    (hy : g y = List.replicate m .mark) (hT : g .TX = []) :
    Runs (copyR (ks x) (ks .TX) (ks y)) (st S p g u)
      (st S p (Function.update g y (List.replicate (n + m) .mark)) u) (fun _ => True)
      (9 * n + 4) := by
  have h := rs_copyxx S p g u x y n hxT hxy hyT hx hT
  rwa [hy, List.replicate_append_replicate] at h

variable (b : BrPar) (rpar : List Sym)

theorem rs_skipk' (g : SX → List Sym) (u : RulerId → List Sym) (k m n k' : ℕ)
    (hn : ((b.hdr.drop k).take m).length = n) (hk' : k + m = k') (hG : g .G = gk b k) :
    Runs (skipFlds kp (ks .G) n) (st S (tl b rpar k) g u)
      (st S (tl b rpar k') (Function.update g .G (gk b k')) u) (fun _ => True)
      (4 * (hdrSyms ((b.hdr.drop k).take m)).length + 1) := by
  subst hn hk'
  exact rs_skipk S b rpar g u k m hG

theorem rs_prodk' (g : SX → List Sym) (u : RulerId → List Sym) (ct x : SX) (k m m0 k' v : ℕ)
    (hpow : ∀ f ∈ (b.hdr.drop k).take m, ∃ a, 1 ≤ a ∧ f = 2 ^ a)
    (hct1 : ct ≠ .TX) (hct2 : ct ≠ .G) (hct3 : ct ≠ x) (hct4 : ct ≠ .Y) (hx1 : x ≠ .TX)
    (hx2 : x ≠ .G) (hx3 : x ≠ .Y) (hk' : k + m = k')
    (hv : m0 * ((b.hdr.drop k).take m).prod = v)
    (hct : g ct = List.replicate ((b.hdr.drop k).take m).length .mark) (hT : g .TX = [])
    (hG : g .G = gk b k) (hx : g x = List.replicate m0 .mark) (hY : g .Y = []) :
    Runs (prodFields (ks ct) (ks .TX) kp (ks .G) (ks x) (ks .Y)) (st S (tl b rpar k) g u)
      (st S (tl b rpar k') (Function.update (Function.update g .G (gk b k')) x
        (List.replicate v .mark)) u) (fun _ => True)
      (18 * v + 10 * (hdrSyms ((b.hdr.drop k).take m)).length +
        4 * ((b.hdr.drop k).take m).length + 4) := by
  subst hk' hv
  exact rs_prodk S b rpar g u ct x k m m0 hpow hct1 hct2 hct3 hct4 hx1 hx2 hx3 hct hT hG hx hY

theorem rs_rewindk' (g : SX → List Sym) (u : RulerId → List Sym) (k : ℕ) (hk : k = 9 + b.d)
    (hG : g .G = gk b k) :
    Runs (rewindG (ks .G) kp) (st S (tl b rpar k) g u)
      (st S (hdrSyms b.hdr ++ rpar) (Function.update g .G []) u) (fun _ => True)
      (3 * (hdrSyms b.hdr).length + 2) := by
  subst hk
  exact WP.W9comp.runs_congr (rs_rewindk S b (tl b rpar (9 + b.d)) g u hG) (by rw [tl_end])

end AVar

/-! ## Header segments, products and size bounds -/

theorem bitLen_size (n : ℕ) : bitLen n = Nat.size n := IntMulTM.length_encodeNat n

theorem bitLen_le (n : ℕ) : bitLen n ≤ n := by
  rw [bitLen_size]
  exact Nat.size_le.2 Nat.lt_two_pow_self

theorem len_le_hdrSyms : ∀ fs : List ℕ, fs.length ≤ (hdrSyms fs).length
  | [] => by simp [hdrSyms_nil']
  | f :: fs => by
    rw [length_hdrSyms_cons, List.length_cons]
    have := len_le_hdrSyms fs
    omega

theorem d_le (b : BrPar) : b.d ≤ (hdrSyms b.hdr).length := by
  have h1 := len_le_hdrSyms b.hdr
  rw [hdr_len] at h1
  omega

theorem seg_le (b : BrPar) (k m : ℕ) :
    (hdrSyms ((b.hdr.drop k).take m)).length ≤ (hdrSyms b.hdr).length := by
  conv_rhs => rw [← List.take_append_drop k b.hdr, ← List.take_append_drop m (b.hdr.drop k)]
  simp only [hdrSyms_append', List.length_append]
  omega

theorem pre_take_len (b : BrPar) (i : Fin b.d) : ((b.hdr.drop 9).take (i : ℕ)).length = i := by
  rw [pre_fields, pre_length]

theorem pre_take_prod (b : BrPar) (i : Fin b.d) :
    ((b.hdr.drop 9).take (i : ℕ)).prod = prefixProd b.t i := by
  rw [pre_fields, pre_prod]

theorem suf_take (b : BrPar) (i : Fin b.d) :
    (b.hdr.drop (9 + (i : ℕ) + 1)).take (b.d - 1 - i) = (List.ofFn b.t).drop ((i : ℕ) + 1) := by
  rw [suf_fields]
  exact List.take_of_length_le (le_of_eq (suf_length b i))

theorem suf_take_len (b : BrPar) (i : Fin b.d) :
    ((b.hdr.drop (9 + (i : ℕ) + 1)).take (b.d - 1 - i)).length = b.d - 1 - i := by
  rw [suf_take, suf_length]

theorem suf_take_prod (b : BrPar) (i : Fin b.d) (ht : ShapeOK b.t) :
    ((b.hdr.drop (9 + (i : ℕ) + 1)).take (b.d - 1 - i)).prod = suffixProd b.t i := by
  rw [suf_take, suf_prod b i ht]

theorem pow_pre (b : BrPar) (i : Fin b.d) (ht : ShapeOK b.t) :
    ∀ f ∈ (b.hdr.drop 9).take (i : ℕ), ∃ a, 1 ≤ a ∧ f = 2 ^ a := fun f hf =>
  pow_fields b ht f (by rw [← hdr_drop_nine]; exact List.mem_of_mem_take hf)

theorem pow_suf (b : BrPar) (i : Fin b.d) (ht : ShapeOK b.t) :
    ∀ f ∈ (b.hdr.drop (9 + (i : ℕ) + 1)).take (b.d - 1 - i), ∃ a, 1 ≤ a ∧ f = 2 ^ a :=
  fun f hf => pow_fields b ht f (by rw [suf_take] at hf; exact List.mem_of_mem_drop hf)

theorem le_mul_pos (a : ℕ) {c : ℕ} (hc : 0 < c) : a ≤ a * c := by
  simpa using Nat.mul_le_mul (le_refl a) hc

theorem le_pos_mul (a : ℕ) {c : ℕ} (hc : 0 < c) : a ≤ c * a := by
  rw [Nat.mul_comm]
  exact le_mul_pos a hc

/-- The size facts used by the cost bounds. -/
theorem atoms (b : BrPar) (i : Fin b.d) (ht : ShapeOK b.t) (hPw : b.P + 2 ≤ b.wI) :
    b.P + 2 ≤ spreadSlot b i ∧ b.wI ≤ spreadSlot b i ∧ b.wT ≤ spreadSlot b i ∧
    bitLen (b.t i) ≤ spreadSlot b i ∧ bitLen b.P ≤ b.P ∧ bitLen b.wI ≤ b.wI ∧
    bitLen b.wT ≤ b.wT ∧ bitLen b.d ≤ b.d ∧ bitLen (i : ℕ) ≤ i ∧
    b.d ≤ (hdrSyms b.hdr).length ∧ prefixProd b.t i ≤ totalLen b.t ∧ b.t i ≤ totalLen b.t ∧
    suffixProd b.t i ≤ totalLen b.t ∧ 2 ≤ b.t i := by
  have hs : spreadSlot b i = b.wI + b.wT + bitLen (b.t i) + 4 := by
    rw [bitLen_size]; rfl
  have hpre : 0 < prefixProd b.t i := Finset.prod_pos fun j _ => by have := (ht j).1; omega
  have hsuf : 0 < suffixProd b.t i := Finset.prod_pos fun j _ => by have := (ht j).1; omega
  have hti := (ht i).1
  have hR := prefixProd_mul_mul_suffixProd b.t i
  refine ⟨by omega, by omega, by omega, by omega, bitLen_le _, bitLen_le _, bitLen_le _,
    bitLen_le _, bitLen_le _, d_le b, ?_, ?_, ?_, hti⟩
  · rw [← hR]
    exact (le_mul_pos _ (by omega)).trans (le_mul_pos _ hsuf)
  · rw [← hR]
    exact (le_pos_mul _ hpre).trans (le_mul_pos _ hsuf)
  · rw [← hR]
    exact le_pos_mul _ (Nat.mul_pos hpre (by omega))

/-- The value `a₀` produced by testing the leftover of `2P+1` after the walk. -/
def a0v (b : BrPar) (i : Fin b.d) : ℕ :=
  if 2 * b.P + 1 - min (2 * b.P + 1) (b.t i) = 0 then b.P else 0

theorem a0v_eq (b : BrPar) (i : Fin b.d) : a0v b i = spreadA0 b i := by
  unfold a0v spreadA0
  split_ifs <;> omega

theorem a0v_le (b : BrPar) (i : Fin b.d) : a0v b i ≤ b.P ∧ a0v b i ≤ b.t i := by
  unfold a0v
  split_ifs <;> omega

/-- Scratch lengths after phase A. -/
@[simp] def cA (b : BrPar) (i : Fin b.d) : SX → ℕ
  | .G => 0
  | .XP => b.P
  | .XI => b.wI
  | .XT => b.wT
  | .Xd => b.d
  | .Xi => i
  | .Xti => b.t i
  | .Xsz => bitLen (b.t i)
  | .Xpre => prefixProd b.t i
  | .Xsuf => suffixProd b.t i
  | .Xk => b.d - 1 - i
  | .X2 => 0
  | .C => 0
  | .Y => 0
  | .TX => 0
  | .TA => 0
  | .TB => 0

/-- Scratch lengths after phase B. -/
@[simp] def cB (b : BrPar) (i : Fin b.d) : SX → ℕ
  | .G => 0
  | .XP => b.P
  | .XI => b.wI
  | .XT => b.wT
  | .Xd => b.d
  | .Xi => i
  | .Xti => b.t i
  | .Xsz => bitLen (b.t i)
  | .Xpre => 0
  | .Xsuf => 0
  | .Xk => 0
  | .X2 => 2 * b.P + 1
  | .C => 0
  | .Y => 0
  | .TX => 0
  | .TA => 0
  | .TB => 0

/-! ## Phase A: parse -/

/-- Phase A: parse the header and the axis into the scratch rulers `cA`. -/
def progA : AProg SK :=
  (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq
  (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq
  (Prog.seq (Prog.seq (Prog.seq (Prog.seq
    (pushS (ks .G) .sep2)
    (skipFlds kp (ks .G) 1))
    (buildRuler kp (ks .XP) (ks .C) (ks .Y)))
    (skipFlds kp (ks .G) 2))
    (buildRuler kp (ks .XI) (ks .C) (ks .Y)))
    (skipFlds kp (ks .G) 1))
    (buildRuler kp (ks .XT) (ks .C) (ks .Y)))
    (skipFlds kp (ks .G) 4))
    (buildRuler kp (ks .Xd) (ks .C) (ks .Y)))
    (skipFlds kp (ks .G) 1))
    (buildRuler ka (ks .Xi) (ks .C) (ks .Y)))
    (pushS (ks .Xpre) .mark))
    (prodFields (ks .Xi) (ks .TX) kp (ks .G) (ks .Xpre) (ks .Y)))
    (buildRuler kp (ks .Xti) (ks .C) (ks .Y)))
    (cntField kp (ks .G) (ks .Xsz)))
    (copyR (ks .Xd) (ks .TX) (ks .Xk)))
    (drop1 (ks .Xk)))
    (subR (ks .Xi) (ks .TX) (ks .Xk)))
    (pushS (ks .Xsuf) .mark))
    (prodFields (ks .Xk) (ks .TX) kp (ks .G) (ks .Xsuf) (ks .Y)))
    (rewindG (ks .G) kp))

theorem closed_progA : progA.Closed := by
  unfold progA
  exact
    (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq
    (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq
    (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq
    (closed_pushS' _ _)
    (closed_skipFlds _ _ _))
    (closed_buildRuler' _ _ _ _))
    (closed_skipFlds _ _ _))
    (closed_buildRuler' _ _ _ _))
    (closed_skipFlds _ _ _))
    (closed_buildRuler' _ _ _ _))
    (closed_skipFlds _ _ _))
    (closed_buildRuler' _ _ _ _))
    (closed_skipFlds _ _ _))
    (closed_buildRuler' _ _ _ _))
    (closed_pushS' _ _))
    (closed_prodFields _ _ _ _ _ _))
    (closed_buildRuler' _ _ _ _))
    (closed_cntField _ _ _))
    (closed_copyR _ _ _))
    (closed_drop1' _))
    (closed_subR _ _ _))
    (closed_pushS' _ _))
    (closed_prodFields _ _ _ _ _ _))
    (closed_rewindG _ _))

theorem runs_progA (S : SK → List Sym) (b : BrPar) (i : Fin b.d) (rax rpar : List Sym)
    (u : RulerId → List Sym) (ht : ShapeOK b.t) (hPw : b.P + 2 ≤ b.wI)
    (hax : S ka = natSyms i ++ rax) (hrax : TermOK rax) :
    Runs progA (st S (tl b rpar 0) (fun _ => []) u)
      (st S (hdrSyms b.hdr ++ rpar) (rep (cA b i)) u) (fun _ => True)
      (200 * ((hdrSyms b.hdr).length + totalLen b.t + spreadSlot b i + 1)) := by
  have hi := i.isLt
  have r1 := rs_pushx' S (tl b rpar 0) (fun _ => []) u .G .sep2 [] rfl
  have r2 := rseq r1 (rs_skipk' S b rpar _ u 0 1 1 1 rfl rfl (by simp [gk_zero]))
  have r3 := rseq r2 (rs_buildk S b rpar _ u .XP 1 b.P (by decide) (by decide) (hdr_get1 b)
    (by simp))
  have r4 := rseq r3 (rs_skipk' S b rpar _ u 1 2 2 3 rfl rfl (by simp))
  have r5 := rseq r4 (rs_buildk S b rpar _ u .XI 3 b.wI (by decide) (by decide) (hdr_get3 b)
    (by simp))
  have r6 := rseq r5 (rs_skipk' S b rpar _ u 3 1 1 4 rfl rfl (by simp))
  have r7 := rseq r6 (rs_buildk S b rpar _ u .XT 4 b.wT (by decide) (by decide) (hdr_get4 b)
    (by simp))
  have r8 := rseq r7 (rs_skipk' S b rpar _ u 4 4 4 8 rfl rfl (by simp))
  have r9 := rseq r8 (rs_buildk S b rpar _ u .Xd 8 b.d (by decide) (by decide) (hdr_get8 b)
    (by simp))
  have r10 := rseq r9 (rs_skipk' S b rpar _ u 8 1 1 9 rfl rfl (by simp))
  have r11 := rseq r10 (rs_builda S _ _ u .Xi (i : ℕ) rax (by decide) (by decide) hax hrax (by simp))
  have r12 := rseq r11 (rs_push1 S _ _ u .Xpre (by simp))
  have r13 := rseq r12 (rs_prodk' S b rpar _ u .Xi .Xpre 9 (i : ℕ) 1 (9 + (i : ℕ))
    (prefixProd b.t i) (pow_pre b i ht) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl (by rw [one_mul, pre_take_prod]) (by rw [pre_take_len]; simp)
    (by simp) (by simp) (by simp) (by simp))
  have r14 := rseq r13 (rs_buildk S b rpar _ u .Xti (9 + (i : ℕ)) (b.t i) (by decide) (by decide)
    (hdr_get_t b i) (by simp))
  have r15 := rseq r14 (rs_cntk S b rpar _ u (9 + (i : ℕ)) (b.t i) (hdr_get_t b i) (by simp)
    (by simp))
  have r16 := rseq r15 (rs_copyxx' S _ _ u .Xd .Xk b.d 0 (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp))
  have r17 := rseq r16 (rs_dropx S _ _ u .Xk (List.replicate (b.d - 1) .mark)
    (by rw [Function.update_self, Nat.add_zero]; exact rep_cons _ (by omega)))
  have r18 := rseq r17 (rs_subxx S _ _ u .Xi .Xk (i : ℕ) (b.d - 1 - (i : ℕ)) (by decide) (by decide)
    (by decide) (by simp) (by rw [Function.update_self]; congr 1; omega) (by simp))
  have r19 := rseq r18 (rs_push1 S _ _ u .Xsuf (by simp))
  have r20 := rseq r19 (rs_prodk' S b rpar _ u .Xk .Xsuf (9 + (i : ℕ) + 1) (b.d - 1 - (i : ℕ)) 1
    (9 + (i : ℕ) + 1 + (b.d - 1 - (i : ℕ))) (suffixProd b.t i) (pow_suf b i ht) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [one_mul, suf_take_prod b i ht]) (by rw [suf_take_len]; simp) (by simp) (by simp)
    (by simp) (by simp))
  have r21 := rseq r20 (rs_rewindk' S b rpar _ u (9 + (i : ℕ) + 1 + (b.d - 1 - (i : ℕ))) (by omega)
    (by simp))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr r21 ?_) (fun _ _ => trivial) ?_
  · congr 1
    funext x
    cases x <;> simp
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := atoms b i ht hPw
    have e1 := seg_le b 0 1
    have e2 := seg_le b 1 2
    have e3 := seg_le b 3 1
    have e4 := seg_le b 4 4
    have e5 := seg_le b 8 1
    have e6 := seg_le b 9 i
    have e7 := seg_le b (9 + (i : ℕ) + 1) (b.d - 1 - i)
    have e8 := pre_take_len b i
    have e9 := suf_take_len b i
    omega

/-! ## Phase B: derive the rulers -/

/-- Phase B: derive the 17 parameter rulers from the scratch rulers `cA`. -/
def progB : AProg SK :=
  (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq
  (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq
  (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq
  (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq
  (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq
  (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq
    (copyR (ks .Xti) (ks .TX) (kr .t))
    (copyR (ks .XP) (ks .TX) (ks .X2)))
    (copyR (ks .XP) (ks .TX) (ks .X2)))
    (pushS (ks .X2) .mark))
    (minRulers (ks .X2) (ks .Xti) (ks .TA) (ks .TB) (kr .W)))
    (copyIfEmpty (ks .X2) (ks .XP) (ks .TX) (kr .a0)))
    (moveMarks (ks .TA) (ks .X2)))
    (moveMarks (ks .TB) (ks .Xti)))
    (copyR (kr .W) (ks .TX) (kr .Wm1)))
    (drop1 (kr .Wm1)))
    (copyR (ks .Xti) (ks .TX) (kr .ta)))
    (subR (kr .a0) (ks .TX) (kr .ta)))
    (copyR (ks .XI) (ks .TX) (kr .wI1)))
    (drop1 (kr .wI1)))
    (copyR (ks .XI) (ks .TX) (kr .s)))
    (copyR (ks .XT) (ks .TX) (kr .s)))
    (copyR (ks .Xsz) (ks .TX) (kr .s)))
    (pushS (kr .s) .mark))
    (pushS (kr .s) .mark))
    (pushS (kr .s) .mark))
    (pushS (kr .s) .mark))
    (copyR (ks .XT) (ks .TX) (kr .sWI)))
    (copyR (ks .Xsz) (ks .TX) (kr .sWI)))
    (pushS (kr .sWI) .mark))
    (pushS (kr .sWI) .mark))
    (pushS (kr .sWI) .mark))
    (pushS (kr .sWI) .mark))
    (copyR (ks .XT) (ks .TX) (kr .wT1)))
    (drop1 (kr .wT1)))
    (copyR (ks .XI) (ks .TX) (kr .sWT)))
    (copyR (ks .Xsz) (ks .TX) (kr .sWT)))
    (pushS (kr .sWT) .mark))
    (pushS (kr .sWT) .mark))
    (pushS (kr .sWT) .mark))
    (pushS (kr .sWT) .mark))
    (copyR (ks .XP) (ks .TX) (kr .sq)))
    (pushS (kr .sq) .mark))
    (pushS (kr .sq) .mark))
    (copyR (kr .s) (ks .TX) (kr .h)))
    (subR (kr .sq) (ks .TX) (kr .h)))
    (copyR (ks .XI) (ks .TX) (kr .wI)))
    (copyR (ks .XI) (ks .TX) (kr .recw)))
    (copyR (ks .XI) (ks .TX) (kr .recw)))
    (pushS (kr .recw) .mark))
    (moveMarks (ks .Xpre) (kr .A)))
    (moveMarks (ks .Xsuf) (kr .rep)))
    (moveMarks (ks .Xk) (kr .skip)))

theorem closed_progB : progB.Closed := by
  unfold progB
  exact
    (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq
    (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq
    (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq
    (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq
    (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq
    (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq
    (closed_seq (closed_seq (closed_seq (closed_seq
    (closed_copyR _ _ _)
    (closed_copyR _ _ _))
    (closed_copyR _ _ _))
    (closed_pushS' _ _))
    (closed_minRulers _ _ _ _ _))
    (closed_copyIfEmpty _ _ _ _))
    (closed_moveMarks' _ _))
    (closed_moveMarks' _ _))
    (closed_copyR _ _ _))
    (closed_drop1' _))
    (closed_copyR _ _ _))
    (closed_subR _ _ _))
    (closed_copyR _ _ _))
    (closed_drop1' _))
    (closed_copyR _ _ _))
    (closed_copyR _ _ _))
    (closed_copyR _ _ _))
    (closed_pushS' _ _))
    (closed_pushS' _ _))
    (closed_pushS' _ _))
    (closed_pushS' _ _))
    (closed_copyR _ _ _))
    (closed_copyR _ _ _))
    (closed_pushS' _ _))
    (closed_pushS' _ _))
    (closed_pushS' _ _))
    (closed_pushS' _ _))
    (closed_copyR _ _ _))
    (closed_drop1' _))
    (closed_copyR _ _ _))
    (closed_copyR _ _ _))
    (closed_pushS' _ _))
    (closed_pushS' _ _))
    (closed_pushS' _ _))
    (closed_pushS' _ _))
    (closed_copyR _ _ _))
    (closed_pushS' _ _))
    (closed_pushS' _ _))
    (closed_copyR _ _ _))
    (closed_subR _ _ _))
    (closed_copyR _ _ _))
    (closed_copyR _ _ _))
    (closed_copyR _ _ _))
    (closed_pushS' _ _))
    (closed_moveMarks' _ _))
    (closed_moveMarks' _ _))
    (closed_moveMarks' _ _))

set_option maxHeartbeats 1000000 in
theorem runs_progB (S : SK → List Sym) (b : BrPar) (i : Fin b.d) (p : List Sym)
    (ht : ShapeOK b.t) (hwI : 1 ≤ b.wI) (hwT : 1 ≤ b.wT) (hPw : b.P + 2 ≤ b.wI) :
    Runs progB (st S p (rep (cA b i)) (rep fun _ => 0))
      (st S p (rep (cB b i)) (rep (spreadRulers b i))) (fun _ => True)
      (300 * ((hdrSyms b.hdr).length + totalLen b.t + spreadSlot b i + 1)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := atoms b i ht hPw
  obtain ⟨h0P, h0t⟩ := a0v_le b i
  have hi := i.isLt
  have r1 := cs_copyxr S p (cA b i) (fun _ => 0) .Xti .t (b.t i) 0 (by decide) (by simp) (by simp)
    (by simp)
  have r2 := rseq r1 (cs_copyxx S p _ _ .XP .X2 b.P 0 (by decide) (by decide) (by decide) (by simp)
    (by simp) (by simp))
  have r3 := rseq r2 (cs_copyxx S p _ _ .XP .X2 b.P (b.P + 0) (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp))
  have r4 := rseq r3 (cs_pushx S p _ _ .X2 (b.P + (b.P + 0)) (by simp))
  have r5 := rseq r4 (cs_minW S p _ _ (2 * b.P + 1) (b.t i) 0 0 0 (by simp; omega) (by simp)
    (by simp) (by simp) (by simp))
  have r6 := rseq r5 (cs_cie S p _ _ (2 * b.P + 1 - min (2 * b.P + 1) (b.t i)) b.P 0 (a0v b i) rfl
    (by simp) (by simp) (by simp) (by simp))
  have r7 := rseq r6 (cs_movexx S p _ _ .TA .X2 (min (2 * b.P + 1) (b.t i) + 0)
    (2 * b.P + 1 - min (2 * b.P + 1) (b.t i)) (by decide) (by simp) (by simp))
  have r8 := rseq r7 (cs_movexx S p _ _ .TB .Xti (min (2 * b.P + 1) (b.t i) + 0)
    (b.t i - min (2 * b.P + 1) (b.t i)) (by decide) (by simp) (by simp))
  have r9 := rseq r8 (cs_copyrr S p _ _ .W .Wm1 (min (2 * b.P + 1) (b.t i) + 0) 0 (by decide)
    (by simp) (by simp) (by simp))
  have r10 := rseq r9 (cs_dropr S p _ _ .Wm1 (min (2 * b.P + 1) (b.t i) - 1) (by simp; omega))
  have r11 := rseq r10 (cs_copyxr S p _ _ .Xti .ta (b.t i) 0 (by decide) (by simp) (by simp)
    (by simp))
  have r12 := rseq r11 (cs_subrr S p _ _ .a0 .ta (a0v b i + 0) (b.t i - (a0v b i + 0)) (by decide)
    (by simp) (by simp) (by simp; omega))
  have r13 := rseq r12 (cs_copyxr S p _ _ .XI .wI1 b.wI 0 (by decide) (by simp) (by simp) (by simp))
  have r14 := rseq r13 (cs_dropr S p _ _ .wI1 (b.wI - 1) (by simp; omega))
  have r15 := rseq r14 (cs_copyxr S p _ _ .XI .s b.wI 0 (by decide) (by simp) (by simp) (by simp))
  have r16 := rseq r15 (cs_copyxr S p _ _ .XT .s b.wT (b.wI + 0) (by decide) (by simp) (by simp)
    (by simp))
  have r17 := rseq r16 (cs_copyxr S p _ _ .Xsz .s (bitLen (b.t i)) (b.wT + (b.wI + 0)) (by decide)
    (by simp) (by simp) (by simp))
  have r18 := rseq r17 (cs_pushr S p _ _ .s (bitLen (b.t i) + (b.wT + (b.wI + 0))) (by simp))
  have r19 := rseq r18 (cs_pushr S p _ _ .s (bitLen (b.t i) + (b.wT + (b.wI + 0)) + 1) (by simp))
  have r20 := rseq r19 (cs_pushr S p _ _ .s (bitLen (b.t i) + (b.wT + (b.wI + 0)) + 1 + 1) (by simp))
  have r21 := rseq r20 (cs_pushr S p _ _ .s (bitLen (b.t i) + (b.wT + (b.wI + 0)) + 1 + 1 + 1)
    (by simp))
  have r22 := rseq r21 (cs_copyxr S p _ _ .XT .sWI b.wT 0 (by decide) (by simp) (by simp) (by simp))
  have r23 := rseq r22 (cs_copyxr S p _ _ .Xsz .sWI (bitLen (b.t i)) (b.wT + 0) (by decide)
    (by simp) (by simp) (by simp))
  have r24 := rseq r23 (cs_pushr S p _ _ .sWI (bitLen (b.t i) + (b.wT + 0)) (by simp))
  have r25 := rseq r24 (cs_pushr S p _ _ .sWI (bitLen (b.t i) + (b.wT + 0) + 1) (by simp))
  have r26 := rseq r25 (cs_pushr S p _ _ .sWI (bitLen (b.t i) + (b.wT + 0) + 1 + 1) (by simp))
  have r27 := rseq r26 (cs_pushr S p _ _ .sWI (bitLen (b.t i) + (b.wT + 0) + 1 + 1 + 1) (by simp))
  have r28 := rseq r27 (cs_copyxr S p _ _ .XT .wT1 b.wT 0 (by decide) (by simp) (by simp) (by simp))
  have r29 := rseq r28 (cs_dropr S p _ _ .wT1 (b.wT - 1) (by simp; omega))
  have r30 := rseq r29 (cs_copyxr S p _ _ .XI .sWT b.wI 0 (by decide) (by simp) (by simp) (by simp))
  have r31 := rseq r30 (cs_copyxr S p _ _ .Xsz .sWT (bitLen (b.t i)) (b.wI + 0) (by decide)
    (by simp) (by simp) (by simp))
  have r32 := rseq r31 (cs_pushr S p _ _ .sWT (bitLen (b.t i) + (b.wI + 0)) (by simp))
  have r33 := rseq r32 (cs_pushr S p _ _ .sWT (bitLen (b.t i) + (b.wI + 0) + 1) (by simp))
  have r34 := rseq r33 (cs_pushr S p _ _ .sWT (bitLen (b.t i) + (b.wI + 0) + 1 + 1) (by simp))
  have r35 := rseq r34 (cs_pushr S p _ _ .sWT (bitLen (b.t i) + (b.wI + 0) + 1 + 1 + 1) (by simp))
  have r36 := rseq r35 (cs_copyxr S p _ _ .XP .sq b.P 0 (by decide) (by simp) (by simp) (by simp))
  have r37 := rseq r36 (cs_pushr S p _ _ .sq (b.P + 0) (by simp))
  have r38 := rseq r37 (cs_pushr S p _ _ .sq (b.P + 0 + 1) (by simp))
  have r39 := rseq r38 (cs_copyrr S p _ _ .s .h
    (bitLen (b.t i) + (b.wT + (b.wI + 0)) + 1 + 1 + 1 + 1) 0 (by decide) (by simp) (by simp)
    (by simp))
  have r40 := rseq r39 (cs_subrr S p _ _ .sq .h (b.P + 0 + 1 + 1)
    (bitLen (b.t i) + (b.wT + (b.wI + 0)) + 1 + 1 + 1 + 1 + 0 - (b.P + 0 + 1 + 1)) (by decide)
    (by simp) (by simp) (by simp; omega))
  have r41 := rseq r40 (cs_copyxr S p _ _ .XI .wI b.wI 0 (by decide) (by simp) (by simp) (by simp))
  have r42 := rseq r41 (cs_copyxr S p _ _ .XI .recw b.wI 0 (by decide) (by simp) (by simp) (by simp))
  have r43 := rseq r42 (cs_copyxr S p _ _ .XI .recw b.wI (b.wI + 0) (by decide) (by simp) (by simp)
    (by simp))
  have r44 := rseq r43 (cs_pushr S p _ _ .recw (b.wI + (b.wI + 0)) (by simp))
  have r45 := rseq r44 (cs_movexr S p _ _ .Xpre .A (prefixProd b.t i) 0 (by simp) (by simp))
  have r46 := rseq r45 (cs_movexr S p _ _ .Xsuf .rep (suffixProd b.t i) 0 (by simp) (by simp))
  have r47 := rseq r46 (cs_movexr S p _ _ .Xk .skip (b.d - 1 - (i : ℕ)) 0 (by simp) (by simp))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr r47 ?_) (fun _ _ => trivial) ?_
  · congr 1
    · congr 1
      funext x
      cases x <;> simp
    · congr 1
      funext r
      cases r <;> simp [spreadRulers, spreadWin, spreadSlot, bitLen_size, a0v_eq] <;> omega
  · omega

/-! ## Phase C: clear the scratch -/

/-- Phase C: pop the remaining scratch rulers. -/
def progC : AProg SK :=
  (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq (Prog.seq
    (clearMarks (ks .XP))
    (clearMarks (ks .XI)))
    (clearMarks (ks .XT)))
    (clearMarks (ks .Xd)))
    (clearMarks (ks .Xi)))
    (clearMarks (ks .Xti)))
    (clearMarks (ks .Xsz)))
    (clearMarks (ks .X2)))

theorem closed_progC : progC.Closed := by
  unfold progC
  exact
    (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq (closed_seq
    (closed_clearMarks' _)
    (closed_clearMarks' _))
    (closed_clearMarks' _))
    (closed_clearMarks' _))
    (closed_clearMarks' _))
    (closed_clearMarks' _))
    (closed_clearMarks' _))
    (closed_clearMarks' _))

theorem runs_progC (S : SK → List Sym) (b : BrPar) (i : Fin b.d) (p : List Sym)
    (d : RulerId → ℕ) (ht : ShapeOK b.t) (hPw : b.P + 2 ≤ b.wI) :
    Runs progC (st S p (rep (cB b i)) (rep d)) (st S p (rep fun _ => 0) (rep d)) (fun _ => True)
      (30 * ((hdrSyms b.hdr).length + totalLen b.t + spreadSlot b i + 1)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := atoms b i ht hPw
  have hi := i.isLt
  have r1 := cs_clearx S p (cB b i) d .XP b.P (by simp)
  have r2 := rseq r1 (cs_clearx S p _ d .XI b.wI (by simp))
  have r3 := rseq r2 (cs_clearx S p _ d .XT b.wT (by simp))
  have r4 := rseq r3 (cs_clearx S p _ d .Xd b.d (by simp))
  have r5 := rseq r4 (cs_clearx S p _ d .Xi (i : ℕ) (by simp))
  have r6 := rseq r5 (cs_clearx S p _ d .Xti (b.t i) (by simp))
  have r7 := rseq r6 (cs_clearx S p _ d .Xsz (bitLen (b.t i)) (by simp))
  have r8 := rseq r7 (cs_clearx S p _ d .X2 (2 * b.P + 1) (by simp))
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr r8 ?_) (fun _ _ => trivial) ?_
  · congr 1
    congr 1
    funext x
    cases x <;> simp
  · omega

/-! ## The setup program and the contract -/

/-- The setup program: parse, derive, clear. -/
def setupProg : AProg SK := .seq progA (.seq progB progC)

theorem closed_setupProg : setupProg.Closed :=
  closed_seq closed_progA (closed_seq closed_progB closed_progC)

end SubNLogN.Machine.Bridge.SpreadSetupAux

namespace SubNLogN.Machine.Bridge.SpreadAux

open TMFw TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Machine.Arith Computability
  SubNLogN.Math.Common SubNLogN.Math.Bridge SubNLogN.Machine.Bridge.SpreadSetupAux

/-- **`SpreadSetupStmt` holds** (no hypotheses): the program `setupProg` (`Bridge/SpreadSetup*`)
with the constant `1000`. -/
theorem spreadSetup_holds : SpreadSetupStmt := by
  refine ⟨1000, fun _ => ⟨SX, inferInstance, inferInstance, AReg, setupProg, inferInstance,
    inferInstance, closed_setupProg, ?_⟩⟩
  intro b i rax rpar S hS ht _hi0 hwI hwT hPw _hlog hrax hpar hax hru
  have hA := runs_progA S b i rax rpar (rep fun _ => 0) ht hPw hax hrax
  have hB := runs_progB S b i (hdrSyms b.hdr ++ rpar) ht hwI hwT hPw
  have hC := runs_progC S b i (hdrSyms b.hdr ++ rpar) (spreadRulers b i) ht hPw
  have hall := rseq hA (rseq hB hC)
  have hset : (hdrSyms b.hdr).length + 1 ≤ b.setup := by
    unfold BrPar.setup
    exact Nat.le_self_pow (by norm_num) _
  refine runs_pre (WP.W9comp.runs_mono (WP.W9comp.runs_congr hall ?_) (fun _ _ => trivial) ?_) ?_
  · funext k
    rcases k with (_ | _ | r) | x
    · exact hpar.symm
    · rfl
    · rfl
    · exact (hS x).symm
  · show _ ≤ 1000 * (b.setup + totalLen b.t + spreadSlot b i)
    omega
  · funext k
    rcases k with (_ | _ | r) | x
    · rw [hpar]
      exact tl_zero b rpar
    · rfl
    · exact (hru r).symm
    · exact (hS x).symm

end SubNLogN.Machine.Bridge.SpreadAux

