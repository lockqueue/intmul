/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Bridge.PrePostLoop
import IntMulTM.SpecFacts

/-!
# K5-PP header programs (`Bridge/PrePostHdr.lean`)

* `fetchField src G tmp dst j`: copy header field `j` (`natSyms`) onto `dst`; `src`, `G`, `tmp`
  restored (`runs_fetchField`, cost `≤ 9·|hdrSyms| + 11`).
* `zcField src G N U`: move one header field from `src` onto `G` (reversed, with its `mark`),
  adding its number of `0` bits to the counter `N` (`runs_zcField`).
* `zcFields`: the same for the `k` fields that follow, `k` counted down on a counter stack
  (`runs_zcFields`). For `t_i = 2^{a_i}` the number of `0` bits of `natSyms t_i` is `a_i`; the
  pre-scaling uses `Σ_{i ≥ 1} a_i = log₂ D` (Section 4.4 (`sec:bridge-alg`), step (1)).

**Scope (honest summary).** Programs over `Option Sym` registers and proved `Runs` lemmas
(no `sorry`). Costs are polynomial in the header length, paid by `BrPar.setup`.
-/

namespace SubNLogN.Machine.BridgePP

open TMFw TMFw.Contracts TMFw.Contracts.W9 TMFw.Lib SubNLogN.Machine Computability

variable {K : Type}

/-- Fetch header field `j` onto `dst`. -/
def fetchField (src G tmp dst : K) (j : ℕ) : SProg K :=
  .seq (pushC G .sep2) (.seq (skipFields src G j) (.seq (copyBlock src dst tmp)
    (WP.W9comp.rewindTo G src .sep2)))

theorem closed_fetchField (src G tmp dst : K) (j : ℕ) : (fetchField src G tmp dst j).Closed := by
  have h := closed_skipFields src G j
  simp only [Prog.Closed] at h ⊢
  refine ⟨by simp [Prog.FreeBelow, pushC], h, ?_, ?_⟩
  · simp [Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody,
      restoreR, popR, pushR, pushC, skip]
  · simp [Prog.FreeBelow, WP.W9comp.rewindTo, WP.W9comp.rewindBody, popR, pushR]

variable [DecidableEq K]

/-- **Fetch a header field.** -/
theorem runs_fetchField {src G tmp dst : K} (h1 : src ≠ G) (h2 : src ≠ tmp) (h3 : src ≠ dst)
    (h5 : G ≠ dst) (h6 : tmp ≠ dst) (fs1 : List ℕ) (a : ℕ) (fs2 : List ℕ)
    (L : List Sym) (S : K → List Sym) (hS : S src = hdrSyms (fs1 ++ a :: fs2) ++ L) :
    Runs (fetchField src G tmp dst fs1.length) S (Function.update S dst (natSyms a ++ S dst))
      (fun _ => True) (9 * (hdrSyms (fs1 ++ a :: fs2)).length + 11) := by
  set L1 := natSyms a ++ Sym.mark :: (hdrSyms fs2 ++ L) with hL1
  have r0 := runs_pushC G Sym.sep2 S
  set S0 := Function.update S G (Sym.sep2 :: S G) with hS0
  have hS0src : S0 src = hdrSyms fs1 ++ L1 := by
    rw [hS0, Function.update_of_ne h1, hS, hdrSyms_append, hdrSyms_cons]
    simp [hL1]
  have r1 := runs_skipFields h1 fs1 L1 S0 hS0src
  set S1 := Function.update (Function.update S0 src L1) G ((hdrSyms fs1).reverse ++ S0 G) with hS1
  have hS1src : S1 src = (encodeNat a).map Sym.bit ++ (Sym.mark :: (hdrSyms fs2 ++ L)) := by
    rw [hS1, Function.update_of_ne h1, Function.update_self, hL1]
    rfl
  have r2 := runs_copyBlock h3 h2 h6.symm (encodeNat a) _ S1 (termOK_mark_cons _) hS1src
  set S2 := Function.update S1 dst ((encodeNat a).map Sym.bit ++ S1 dst) with hS2
  have hS2G : S2 G = (hdrSyms fs1).reverse ++ Sym.sep2 :: S G := by
    rw [hS2, Function.update_of_ne h5, hS1, Function.update_self, hS0, Function.update_self]
  have r3 := runs_rewindTo h1.symm Sym.sep2 (hdrSyms fs1).reverse (S G) S2
    (by rw [List.mem_reverse]; exact sep2_not_mem_hdrSyms _) hS2G
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq r0
    (WP.W9comp.runs_seq r1 (WP.W9comp.runs_seq r2 r3))) ?_) (fun _ _ => trivial) ?_
  · have hsrc : S src = hdrSyms fs1 ++ L1 := by
      rw [hS, hdrSyms_append, hdrSyms_cons]; simp [hL1]
    funext k
    simp only [hS2, hS1, hS0, Function.update_apply, List.reverse_reverse]
    split_ifs <;> simp_all [natSyms]
  · have hl : (hdrSyms (fs1 ++ a :: fs2)).length =
        (hdrSyms fs1).length + (bitLen a + 1 + (hdrSyms fs2).length) := by
      rw [hdrSyms_append, List.length_append, length_hdrSyms_cons]
    simp only [List.length_reverse]
    unfold bitLen at hl
    omega

/-! ## Counting the `0` bits of header fields -/

section ZeroCount

/-- `whileCost` bounded along the actual trajectory. -/
theorem whileCost_le_traj {α : Type} (Tp B : ℕ) (Tb : List α → α → List α → ℕ) (all : List α)
    (hB : ∀ done x rest, done ++ x :: rest = all → Tb done x rest ≤ B) :
    ∀ rest done, done ++ rest = all → whileCost Tp Tb done rest ≤ rest.length * (B + Tp + 1) + 1
  | [], _, _ => by simp [whileCost]
  | x :: rest, done, h => by
    have ih := whileCost_le_traj Tp B Tb all hB rest (done ++ [x]) (by simpa using h)
    have hb := hB done x rest h
    simp only [whileCost, List.length_cons]
    nlinarith

variable {K : Type}

/-- Zero-count, one bit: pop it, push it on `G`, increment `N` if it is `0`. -/
def zcBody (src G N U : K) : SProg K :=
  .seq (popR src) (.seq (pushR G) (.ite (fun r => decide (r = some (.bit false))) (inc N U) skip))

/-- Zero-count, one field: its bits, then its `mark`. -/
def zcField (src G N U : K) : SProg K :=
  .seq (.seq (peekR src) (.loop optIsBit (.seq (zcBody src G N U) (peekR src)))) (moveSym src G)

/-- Zero-count over the `k` fields that follow, `k` counted down on `D`. -/
def zcFields (src G N U D : K) : SProg K :=
  .seq (peekR D) (.loop optIsBit (.seq (.seq (zcField src G N U) (dec D U)) (peekR D)))

theorem closed_zcFields (src G N U D : K) : (zcFields src G N U D).Closed := by
  simp [Prog.Closed, Prog.FreeBelow, zcFields, zcField, zcBody, moveSym, inc, incFix, dec, decFix,
    scanLoop, scanBody, pushC, popR, peekR, pushR, skip, moveBits, moveBitsBody, restoreR]

variable [DecidableEq K]

theorem runs_peekR (k : K) (S : K → List Sym) :
    Runs (peekR k) S S (fun r => r = (S k).head?) 1 :=
  Runs.of_eval fun v => ⟨(S k).head?, 1,
    Eval.peek (Γ := fun _ => Sym) [] k (fun (_ : Option Sym) o => o) v S, rfl, le_refl _⟩

/-- Number of `0` bits of `natSyms t`. -/
def zcount (t : ℕ) : ℕ := (encodeNat t).count false

theorem length_encodeNat_le (n : ℕ) : (encodeNat n).length ≤ n := by
  rw [IntMulTM.length_encodeNat]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem ones_le_self (n : ℕ) : ones (encodeNat n) ≤ n := by
  have h1 : ∀ L : List Bool, ones L ≤ L.length := by
    intro L
    induction L with
    | nil => simp [ones]
    | cons b l ih => cases b <;> simp [ones] <;> omega
  exact (h1 _).trans (length_encodeNat_le n)

theorem optIsBit_natSyms (n : ℕ) {L : List Sym} (hL : TermOK L) :
    optIsBit (natSyms n ++ L).head? = decide (n ≠ 0) := by
  rcases h : encodeNat n with _ | ⟨b, l⟩
  · have := (encodeNat_eq_nil_iff n).mp h
    subst this
    simp [natSyms, h, optIsBit_head?_of_termOK hL]
  · have hn : n ≠ 0 := by
      intro h0
      subst h0
      simp [encodeNat_zero] at h
    simp [natSyms, h, hn]

/-- **Zero-count, one field.** -/
theorem runs_zcField {src G N U : K} (h1 : src ≠ G) (h2 : src ≠ N) (h3 : src ≠ U) (h4 : G ≠ N)
    (h5 : G ≠ U) (h6 : N ≠ U) (x c : ℕ) (L RN : List Sym) (S : K → List Sym) (hRN : TermOK RN)
    (hsrc : S src = natSyms x ++ Sym.mark :: L) (hN : S N = natSyms c ++ RN) :
    Runs (zcField src G N U) S
      (Function.update (Function.update (Function.update S src L) G
        ((natSyms x ++ [Sym.mark]).reverse ++ S G)) N (natSyms (c + zcount x) ++ RN))
      (fun _ => True) (bitLen x * (6 * (c + zcount x) + 14) + 4) := by
  set bs := encodeNat x with hbs
  let st : List Bool → List Bool → K → List Sym := fun done rest =>
    Function.update (Function.update (Function.update S src (rest.map Sym.bit ++ Sym.mark :: L)) G
      (done.reverse.map Sym.bit ++ S G)) N (natSyms (c + done.count false) ++ RN)
  have h0 : st [] bs = S := by
    simp only [st, List.reverse_nil, List.map_nil, List.nil_append, List.count_nil, Nat.add_zero]
    rw [← hN, ← show S src = bs.map Sym.bit ++ Sym.mark :: L from hsrc, Function.update_eq_self,
      Function.update_eq_self, Function.update_eq_self]
  have hw := runs_while (pk := peekR src) (body := zcBody src G N U) (c := optIsBit) st 1
    (fun done y _ => if y = false then 6 * ones (encodeNat (c + done.count false)) + 12 else 4)
    (fun done rest => by
      refine WP.W9comp.runs_mono (runs_peekR src (st done rest)) (fun v hv => ?_) le_rfl
      simp only [st, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self] at hv
      rw [hv]
      cases rest <;> rfl)
    (fun done y rest => by
      refine Runs.of_eval fun v => ?_
      have e1 : Eval [] (popR src) ⟨v, st done (y :: rest)⟩ ⟨some (.bit y),
          Function.update (st done (y :: rest)) src (rest.map Sym.bit ++ Sym.mark :: L)⟩ 1 := by
        refine (Eval.pop (Γ := fun _ => Sym) [] src (fun (_ : Option Sym) o => o) v _).of_eq ?_ rfl
        simp [st, Function.update_of_ne h2, Function.update_of_ne h1]
      set S1 := Function.update (st done (y :: rest)) src (rest.map Sym.bit ++ Sym.mark :: L)
        with hS1
      have e2 : Eval [] (pushR G) ⟨some (.bit y), S1⟩
          ⟨some (.bit y), Function.update S1 G (Sym.bit y :: S1 G)⟩ 1 :=
        Eval.push [] G (fun r => r.getD .sep) (some (.bit y)) S1
      set S2 := Function.update S1 G (Sym.bit y :: S1 G) with hS2
      cases y
      · obtain ⟨cc, hcc, e3⟩ := inc_eval (ρ := []) h6 (some (.bit false))
          (encodeNat (c + done.count false)) RN S2 hRN
          (by simp [hS2, hS1, st, Function.update_of_ne h4.symm, Function.update_of_ne h2.symm,
            natSyms])
        refine ⟨some .mark, _, (Eval.seq e1 (Eval.seq e2 (Eval.ite_true (by simp) e3))).of_eq ?_ rfl,
          trivial, ?_⟩
        swap
        · show 1 + (1 + (cc + 1)) ≤ 6 * ones (encodeNat (c + done.count false)) + 12
          omega
        congr 1
        funext k
        simp only [hS2, hS1, st, Function.update_apply, ← encodeNat_succ]
        split_ifs <;> simp_all [natSyms, List.count_append, Nat.add_assoc]
      · refine ⟨some (.bit true), _,
          (Eval.seq e1 (Eval.seq e2 (Eval.ite_false (by simp) (skip_eval [] _)))).of_eq ?_ rfl,
          trivial, by simp⟩
        congr 1
        funext k
        simp only [hS2, hS1, st, Function.update_apply]
        split_ifs <;> simp_all [natSyms, List.count_append])
    bs []
  rw [h0] at hw
  have hm := runs_moveSym h1 Sym.mark L (st ([] ++ bs) [])
    (by simp [st, Function.update_of_ne h2, Function.update_of_ne h1])
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq hw hm) ?_)
    (fun _ _ => trivial) ?_
  · clear hw h0 hm
    funext k
    simp only [st, List.nil_append, List.map_nil]
    by_cases hk1 : k = G
    · subst hk1
      simp [Function.update_apply, Ne.symm h1, h4, natSyms, zcount, ← hbs, List.map_reverse]
    · by_cases hk2 : k = src
      · subst hk2
        simp [Function.update_apply, h1, h2]
      · by_cases hk3 : k = N
        · subst hk3
          simp [Function.update_apply, Ne.symm h2, Ne.symm h4, zcount, ← hbs]
        · simp [Function.update_apply, hk1, hk2, hk3]
  · have hb := whileCost_le_traj 1 (6 * (c + zcount x) + 12)
      (fun done y _ => if y = false then 6 * ones (encodeNat (c + done.count false)) + 12 else 4)
      bs (fun done y rest h => by
        have hc : done.count false + (if y = false then 1 else 0) ≤ zcount x := by
          rw [zcount, ← hbs, ← h, List.count_append, List.count_cons]
          cases y <;> simp
        have ho := ones_le_self (c + done.count false)
        split_ifs at hc ⊢ <;> omega) bs [] rfl
    unfold bitLen
    rw [← hbs]
    nlinarith

end ZeroCount

end SubNLogN.Machine.BridgePP
