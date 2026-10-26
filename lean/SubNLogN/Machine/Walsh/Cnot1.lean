/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.Cnot1Pure

/-!
# `SubNLogN.Machine.Walsh.Cnot1`: one controlled flip (K3.3) from Lemma A.4(1)

Paper: Lemma 5.4 (`lem:cnot`) and the leftover targets of Theorem 5.8 (`thm:positional-perm`),
together with Lemma A.4(1) (`lem:transfer-streams`: a fixed permutation of a digit pair, split
into `q²` streams and merge).

## Plan
* The controlled flip `CNOT_{c,t}` on a cube array is the fixed digit-pair permutation
  `cnotPP : (a, b) ↦ (a, b + a)` of the radix-2 digits `c`, `t` of the record index
  (`cubeOfNat_pairPermAddr`, `permByInv_cnot` in `Walsh/Cnot1Pure.lean`), i.e. one call of the
  Lemma A.4(1) kernel `K1PairPermStmt 2 cnotPP` (`Contracts/Streams.lean:173`), taken here as an
  explicit hypothesis (proved as `K1Digit.k1PairPerm_holds` in `K1/DigitPairPerm.lean`).
* `prep`: copy the counters `m` (6th field of the header `permHdr P d r w K m`), `c` and `t`
  (2nd and 3rd fields of `pairsSyms [(c, t)] = hdrSyms [1, c, t]`) onto clean scratch stacks
  `k2`, `k3`, `k4` (skip fields onto `pk`, `copyBlock`, move the skipped fields back). Cost
  `O(|permHdr| + bitLen c + bitLen t)`.
* The pair-permutation kernel runs embedded (`callInj`) on: the array (source), the scratch `y`
  (destination), `k2`, `k3`, `k4` (counters) and its own private stacks `E'`. Cost
  `C_PP·(V + 1)`, `V = cvolCube m r w`.
* `post`: move the result from `y` back onto the array stack (two reversals through `pk`) and clear
  `k2`, `k3`, `k4`. Cost `O(V + m)`.
* Registers `Option Sym × R'` (`R'` the kernel's registers); constant `C_PP + 100`, `J = 1`.

**Scope (honest summary).** Proved (no `sorry`):
`cnot1Machine_of_pairPerm : K1PairPermStmt 2 cnotPP → Cnot1MachineStmt`. The header fields
`P, d, r, w, K` are skipped (their reading cost is the `|permHdr|` term of the contract); `w` and
`r` are not needed since records are moved unchanged.
-/

namespace SubNLogN.Machine.WalshCnot1

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine SubNLogN.Math.Walsh
  Computability

/-! ## Skipping header fields -/

section Skip

variable {K : Type}

/-- Move one header field (`natSyms n ++ [mark]`) from `src` onto `pk` (reversed). -/
def skipField (src pk : K) : SProg K := .seq (moveBits src pk) (pushC pk .mark)

/-- Move `n` header fields from `src` onto `pk`. -/
def skipFields (src pk : K) : ℕ → SProg K
  | 0 => skip
  | n + 1 => .seq (skipField src pk) (skipFields src pk n)

theorem closed_skipFields (src pk : K) : ∀ n, (skipFields src pk n).Closed
  | 0 => by simp [Prog.Closed, Prog.FreeBelow, skipFields, skip]
  | n + 1 => WP.W9comp.closed_seq
      (by simp [Prog.Closed, Prog.FreeBelow, skipField, moveBits, moveBitsBody, pushR, popR, pushC])
      (closed_skipFields src pk n)

variable [DecidableEq K]

theorem skipField_eval {src pk : K} (hne : src ≠ pk) (v : Option Sym) (n : ℕ) (rest : List Sym)
    (S : K → List Sym) (hS : S src = natSyms n ++ Sym.mark :: rest) :
    Eval [] (skipField src pk) ⟨v, S⟩
      ⟨some .mark, Function.update (Function.update S src rest) pk
        ((natSyms n ++ [Sym.mark]).reverse ++ S pk)⟩ (3 * bitLen n + 3) := by
  have e1 := moveBits_eval hne [] v (encodeNat n) (Sym.mark :: rest) S (TermOK.cons rfl _) hS
  simp only [List.tail_cons, List.head?_cons] at e1
  have e2 := WalshLift.eval_pushC pk Sym.mark (some Sym.mark)
    (Function.update (Function.update S src rest) pk ((encodeNat n).reverse.map Sym.bit ++ S pk))
  refine (Eval.seq e1 e2).of_eq ?_ (by simp only [bitLen])
  congr 1
  funext k
  simp only [Function.update_apply, natSyms, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append]
  split_ifs <;> simp_all

theorem length_hdrSyms_cons (f : ℕ) (fs : List ℕ) :
    (hdrSyms (f :: fs)).length = bitLen f + 1 + (hdrSyms fs).length := by
  simp [hdrSyms, length_natSyms]
  omega

theorem length_hdrSyms_append (fs gs : List ℕ) :
    (hdrSyms (fs ++ gs)).length = (hdrSyms fs).length + (hdrSyms gs).length := by
  simp [hdrSyms]

theorem length_hdrSyms_single (f : ℕ) : (hdrSyms [f]).length = bitLen f + 1 := by
  rw [length_hdrSyms_cons]
  rfl

theorem skipFields_eval {src pk : K} (hne : src ≠ pk) (rest : List Sym) :
    ∀ (fs : List ℕ) (v : Option Sym) (S : K → List Sym), S src = hdrSyms fs ++ rest →
      ∃ v', Eval [] (skipFields src pk fs.length) ⟨v, S⟩
        ⟨v', Function.update (Function.update S src rest) pk ((hdrSyms fs).reverse ++ S pk)⟩
        (3 * (hdrSyms fs).length + 1)
  | [], v, S, hS => by
    have hS' : S src = rest := by simpa [hdrSyms] using hS
    refine ⟨v, (skip_eval [] _).of_eq ?_ (by simp [hdrSyms])⟩
    congr 1
    funext k
    simp only [Function.update_apply, hdrSyms, List.flatMap_nil, List.reverse_nil,
      List.nil_append]
    split_ifs <;> simp_all
  | f :: fs, v, S, hS => by
    have hS' : S src = natSyms f ++ Sym.mark :: (hdrSyms fs ++ rest) := by
      rw [hS]
      simp [hdrSyms]
    have e1 := skipField_eval hne v f _ S hS'
    obtain ⟨v', e2⟩ := skipFields_eval hne rest fs (some .mark)
      (Function.update (Function.update S src (hdrSyms fs ++ rest)) pk
        ((natSyms f ++ [Sym.mark]).reverse ++ S pk))
      (by rw [Function.update_of_ne hne, Function.update_self])
    refine ⟨v', (Eval.seq e1 e2).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [Function.update_apply, hdrSyms, List.flatMap_cons, List.reverse_append,
        List.append_assoc]
      split_ifs <;> simp_all
    · rw [length_hdrSyms_cons]
      omega

end Skip

/-! ## The kernel's stacks and the counter preparation -/

/-- Private scratch stacks of the controlled-flip kernel, besides the private stacks `E'` of the
embedded pair-permutation kernel: its destination `y`, the park stack `pk`, the counters `k2`
(`m`), `k3` (`c`), `k4` (`t`), and the temporary `tmp` of `copyBlock`. -/
inductive CS : Type
  | y | pk | k2 | k3 | k4 | tmp
  deriving DecidableEq

instance : Fintype CS where
  elems := {.y, .pk, .k2, .k3, .k4, .tmp}
  complete := by intro x; cases x <;> simp

/-- Stacks of the controlled-flip kernel: `.inl 0` the cube array, `.inl 1` the header, `.inl 2`
the pair. -/
abbrev CK (E' : Type) : Type := KLoc (Fin 3) (CS ⊕ E')

section Main

variable {E' : Type} [DecidableEq E']

/-- Copy the counters `m`, `c`, `t` onto `k2`, `k3`, `k4`; header and pair are restored. -/
def prep (E' : Type) : SProg (CK E') :=
  .seq (skipFields (.inl 1) (.inr (.inl .pk)) 5)
  (.seq (copyBlock (.inl 1) (.inr (.inl .k2)) (.inr (.inl .tmp)))
  (.seq (WalshLift.drain (.inr (.inl .pk)) (.inl 1))
  (.seq (skipFields (.inl 2) (.inr (.inl .pk)) 1)
  (.seq (copyBlock (.inl 2) (.inr (.inl .k3)) (.inr (.inl .tmp)))
  (.seq (skipFields (.inl 2) (.inr (.inl .pk)) 1)
  (.seq (copyBlock (.inl 2) (.inr (.inl .k4)) (.inr (.inl .tmp)))
    (WalshLift.drain (.inr (.inl .pk)) (.inl 2))))))))

/-- Move the permuted array from `y` back onto the array stack and clear the counters. -/
def post (E' : Type) : SProg (CK E') :=
  .seq (WalshLift.drain (.inr (.inl .y)) (.inr (.inl .pk)))
  (.seq (WalshLift.drain (.inr (.inl .pk)) (.inl 0))
  (.seq (WalshLift.clear (.inr (.inl .k2))) (.seq (WalshLift.clear (.inr (.inl .k3)))
    (WalshLift.clear (.inr (.inl .k4))))))

omit [DecidableEq E'] in
theorem closed_prep : (prep E').Closed := by
  refine WP.W9comp.closed_seq (closed_skipFields _ _ _) (WP.W9comp.closed_seq ?_
    (WP.W9comp.closed_seq (WalshLift.closed_drain _ _) (WP.W9comp.closed_seq
      (closed_skipFields _ _ _) (WP.W9comp.closed_seq ?_ (WP.W9comp.closed_seq
        (closed_skipFields _ _ _) (WP.W9comp.closed_seq ?_ (WalshLift.closed_drain _ _)))))))
  all_goals simp [Prog.Closed, Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody,
    moveBitsDup, dupBody, restoreR, pushR, popR, pushC, skip]

omit [DecidableEq E'] in
theorem closed_post : (post E').Closed :=
  WP.W9comp.closed_seq (WalshLift.closed_drain _ _) (WP.W9comp.closed_seq
    (WalshLift.closed_drain _ _) (WP.W9comp.closed_seq (WalshLift.closed_clear _)
      (WP.W9comp.closed_seq (WalshLift.closed_clear _) (WalshLift.closed_clear _))))

theorem bitLen_one : bitLen 1 = 1 := by decide

/-- **Counter preparation**: `k2 = natSyms m`, `k3 = natSyms c`, `k4 = natSyms t` (alone on
their clean stacks); every other stack ends with its initial content. -/
theorem prep_eval (P d r w K m c t : ℕ) (hrest prest : List Sym) (S : CK E' → List Sym)
    (v : Option Sym) (hcl : ∀ e : CS, S (.inr (.inl e)) = [])
    (hH : S (.inl 1) = permHdr P d r w K m ++ hrest)
    (hQ : S (.inl 2) = hdrSyms [1, c, t] ++ prest) :
    ∃ v' T, Eval [] (prep E') ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S (.inr (.inl .k2)) (natSyms m))
        (.inr (.inl .k3)) (natSyms c)) (.inr (.inl .k4)) (natSyms t)⟩ T ∧
      T ≤ 7 * (permHdr P d r w K m).length + 13 * (bitLen c + bitLen t) + 50 := by
  have hH' : S (.inl 1) = hdrSyms [P, d, r, w, K] ++ (natSyms m ++ Sym.mark :: hrest) := by
    rw [hH]
    simp [permHdr, hdrSyms]
  obtain ⟨v1, e1⟩ := skipFields_eval (src := (.inl 1 : CK E')) (pk := .inr (.inl .pk))
    (by simp) _ [P, d, r, w, K] v S hH'
  set S1 := Function.update (Function.update S (.inl 1) (natSyms m ++ Sym.mark :: hrest))
    (.inr (.inl .pk)) ((hdrSyms [P, d, r, w, K]).reverse ++ S (.inr (.inl .pk))) with hS1
  have e2 := copyBlock_eval (src := (.inl 1 : CK E')) (dst := .inr (.inl .k2))
    (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) [] v1 (encodeNat m)
    (Sym.mark :: hrest) S1 (TermOK.cons rfl _) (by simp [hS1, natSyms])
  set S2 := Function.update S1 (.inr (.inl .k2)) ((encodeNat m).map Sym.bit ++ S1 (.inr (.inl .k2)))
    with hS2
  have e3 := WalshLift.drain_eval (src := (.inr (.inl .pk) : CK E')) (dst := .inl 1) (by simp)
    (some .mark) ((hdrSyms [P, d, r, w, K]).reverse) S2 (by simp [hS2, hS1, hcl])
  set S3 := Function.update (Function.update S2 (.inr (.inl .pk)) []) (.inl 1)
    ((hdrSyms [P, d, r, w, K]).reverse.reverse ++ S2 (.inl 1)) with hS3
  have hQ1 : S3 (.inl 2) = hdrSyms [1] ++ (hdrSyms [c] ++ (hdrSyms [t] ++ prest)) := by
    simp [hS3, hS2, hS1, hQ, hdrSyms]
  obtain ⟨v4, e4⟩ := skipFields_eval (src := (.inl 2 : CK E')) (pk := .inr (.inl .pk))
    (by simp) _ [1] none S3 hQ1
  set S4 := Function.update (Function.update S3 (.inl 2) (hdrSyms [c] ++ (hdrSyms [t] ++ prest)))
    (.inr (.inl .pk)) ((hdrSyms [1]).reverse ++ S3 (.inr (.inl .pk))) with hS4
  have e5 := copyBlock_eval (src := (.inl 2 : CK E')) (dst := .inr (.inl .k3))
    (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) [] v4 (encodeNat c)
    (Sym.mark :: (hdrSyms [t] ++ prest)) S4 (TermOK.cons rfl _)
    (by simp [hS4, hdrSyms, natSyms])
  set S5 := Function.update S4 (.inr (.inl .k3)) ((encodeNat c).map Sym.bit ++ S4 (.inr (.inl .k3)))
    with hS5
  obtain ⟨v6, e6⟩ := skipFields_eval (src := (.inl 2 : CK E')) (pk := .inr (.inl .pk))
    (by simp) (hdrSyms [t] ++ prest) [c] (some .mark) S5 (by simp [hS5, hS4])
  set S6 := Function.update (Function.update S5 (.inl 2) (hdrSyms [t] ++ prest))
    (.inr (.inl .pk)) ((hdrSyms [c]).reverse ++ S5 (.inr (.inl .pk))) with hS6
  have e7 := copyBlock_eval (src := (.inl 2 : CK E')) (dst := .inr (.inl .k4))
    (tmp := .inr (.inl .tmp)) (by simp) (by simp) (by simp) [] v6 (encodeNat t)
    (Sym.mark :: prest) S6 (TermOK.cons rfl _) (by simp [hS6, hdrSyms, natSyms])
  set S7 := Function.update S6 (.inr (.inl .k4)) ((encodeNat t).map Sym.bit ++ S6 (.inr (.inl .k4)))
    with hS7
  have e8 := WalshLift.drain_eval (src := (.inr (.inl .pk) : CK E')) (dst := .inl 2) (by simp)
    (some .mark) ((hdrSyms [c]).reverse ++ (hdrSyms [1]).reverse) S7
    (by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hcl])
  refine ⟨none, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
    (Eval.seq e6 (Eval.seq e7 e8))))))).of_eq ?_ rfl, ?_⟩
  · congr 1
    funext k
    rcases k with i | (e | e)
    · fin_cases i
      · simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1]
      · simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hH']
      · simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hQ, hdrSyms]
    · cases e <;> simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, hcl, natSyms]
    · simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1]
  · have hph : (permHdr P d r w K m).length = (hdrSyms [P, d, r, w, K]).length + bitLen m + 1 := by
      rw [permHdr, show [P, d, r, w, K, m] = [P, d, r, w, K] ++ [m] from rfl,
        length_hdrSyms_append, length_hdrSyms_single]
      omega
    have l1 : (hdrSyms [1]).length = 2 := by rw [length_hdrSyms_single, bitLen_one]
    have lc : (hdrSyms [c]).length = bitLen c + 1 := length_hdrSyms_single c
    have hm : (encodeNat m).length = bitLen m := rfl
    have hc : (encodeNat c).length = bitLen c := rfl
    have ht : (encodeNat t).length = bitLen t := rfl
    simp only [List.length_reverse, List.length_append]
    omega

/-- **Result move and cleanup**: the list `L` on `y` is moved onto the array stack (same order);
`y`, `k2`, `k3`, `k4` end empty. -/
theorem post_eval (L : List Sym) (m c t : ℕ) (S : CK E' → List Sym) (v : Option Sym)
    (hY : S (.inr (.inl .y)) = L) (hP : S (.inr (.inl .pk)) = [])
    (h2 : S (.inr (.inl .k2)) = natSyms m) (h3 : S (.inr (.inl .k3)) = natSyms c)
    (h4 : S (.inr (.inl .k4)) = natSyms t) :
    Eval [] (post E') ⟨v, S⟩
      ⟨none, Function.update (Function.update (Function.update (Function.update
        (Function.update S (.inr (.inl .y)) []) (.inl 0) (L ++ S (.inl 0))) (.inr (.inl .k2)) [])
        (.inr (.inl .k3)) []) (.inr (.inl .k4)) []⟩
      (6 * L.length + 2 * (bitLen m + bitLen c + bitLen t) + 10) := by
  have e1 := WalshLift.drain_eval (src := (.inr (.inl .y) : CK E')) (dst := .inr (.inl .pk))
    (by simp) v L S hY
  set S1 := Function.update (Function.update S (.inr (.inl .y)) []) (.inr (.inl .pk))
    (L.reverse ++ S (.inr (.inl .pk))) with hS1
  have e2 := WalshLift.drain_eval (src := (.inr (.inl .pk) : CK E')) (dst := .inl 0) (by simp)
    none L.reverse S1 (by simp [hS1, hP])
  set S2 := Function.update (Function.update S1 (.inr (.inl .pk)) []) (.inl 0)
    (L.reverse.reverse ++ S1 (.inl 0)) with hS2
  have e3 := WalshLift.clear_eval (.inr (.inl .k2) : CK E') none (natSyms m) S2
    (by simp [hS2, hS1, h2])
  have e4 := WalshLift.clear_eval (.inr (.inl .k3) : CK E') none (natSyms c)
    (Function.update S2 (.inr (.inl .k2)) []) (by simp [hS2, hS1, h3])
  have e5 := WalshLift.clear_eval (.inr (.inl .k4) : CK E') none (natSyms t)
    (Function.update (Function.update S2 (.inr (.inl .k2)) []) (.inr (.inl .k3)) [])
    (by simp [hS2, hS1, h4])
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))).of_eq ?_ ?_
  · congr 1
    funext k
    rcases k with i | (e | e)
    · fin_cases i <;> simp [hS2, hS1]
    · cases e <;> simp [hS2, hS1, hP]
    · simp [hS2, hS1]
  · simp only [List.length_reverse, length_natSyms]
    omega

/-- The stack embedding of the pair-permutation kernel: source = the array, destination = `y`,
counters `k, i, j` = `k2, k3, k4`, private stacks = `E'`. -/
def ιPP (E' : Type) : KLoc (Fin 5) E' → CK E'
  | .inl ⟨0, _⟩ => .inl 0
  | .inl ⟨1, _⟩ => .inr (.inl .y)
  | .inl ⟨2, _⟩ => .inr (.inl .k2)
  | .inl ⟨3, _⟩ => .inr (.inl .k3)
  | .inl ⟨_ + 4, _⟩ => .inr (.inl .k4)
  | .inr e => .inr (.inr e)

omit [DecidableEq E'] in
theorem ιPP_injective : Function.Injective (ιPP E') := by
  rintro (⟨i, hi⟩ | e) (⟨j, hj⟩ | f) h
  · interval_cases i <;> interval_cases j <;> simp_all [ιPP]
  · interval_cases i <;> simp [ιPP] at h
  · interval_cases j <;> simp [ιPP] at h
  · simp only [ιPP, Sum.inr.injEq] at h
    rw [h]

/-- The controlled-flip kernel around a pair-permutation kernel `PP`. -/
def cnotProg {R' : Type} (PP : Prog (KLoc (Fin 5) E') (fun _ => Sym) R') :
    Prog (CK E') (fun _ => Sym) (Option Sym × R') :=
  .seq (callInj id (Lens.fst _ _) (prep E'))
    (.seq (callInj (ιPP E') (Lens.snd _ _) PP) (callInj id (Lens.fst _ _) (post E')))

omit [DecidableEq E'] in
theorem closed_cnotProg {R' : Type} {PP : Prog (KLoc (Fin 5) E') (fun _ => Sym) R'}
    (hPP : PP.Closed) : (cnotProg PP).Closed :=
  WP.W9comp.closed_seq (closed_callInj _ _ closed_prep)
    (WP.W9comp.closed_seq (closed_callInj _ _ hPP) (closed_callInj _ _ closed_post))

end Main

/-! ## The contract -/

theorem pairsSyms_single {m : ℕ} (c t : Fin m) :
    pairsSyms [(c, t)] = hdrSyms [1, (c : ℕ), (t : ℕ)] := by
  simp [pairsSyms]

theorem cost_le (CP V ph m w bm bc bt : ℕ) (hbm : bm ≤ ph) (hbc : bc ≤ m) (hbt : bt ≤ m) :
    7 * ph + 13 * (bc + bt) + 50 + (CP * (V + 1) + (6 * V + 2 * (bm + bc + bt) + 10)) ≤
      (CP + 100) * (V + (w + m + 1) ^ 1 + ph) := by
  rw [pow_one]
  have e1 : CP * (V + 1) = CP * V + CP := by ring
  have e2 : (CP + 100) * (V + (w + m + 1) + ph) =
      CP * V + CP * w + CP * m + CP + CP * ph + 100 * V + 100 * w + 100 * m + 100 + 100 * ph := by
    ring
  rw [e1, e2]
  omega

/-- **K3.3, one controlled flip, proved from Lemma A.4(1)** (`Cnot1MachineStmt`,
`Contracts/Walsh.lean`; Lemma 5.4 (`lem:cnot`) and Lemma A.4(1) (`lem:transfer-streams`)).
Hypothesis: the Lemma A.4(1) pair-permutation kernel `K1PairPermStmt 2 cnotPP`
(`Contracts/Streams.lean:173`) for the fixed digit-pair permutation `cnotPP : (a, b) ↦ (a, b + a)`.
The kernel copies the counters `m, c, t`, runs the pair permutation on the digits `c, t` of the
record index, and moves the result back; `J = 1`, constant `C_PP + 100`. -/
theorem cnot1Machine_of_pairPerm (hPP : K1PairPermStmt 2 cnotPP) : Cnot1MachineStmt := by
  obtain ⟨CP, hPPc⟩ := hPP
  obtain ⟨E', iF, iD, R', PP, hRfin, hRne, hPPcl, hPPspec⟩ := hPPc ()
  refine ⟨1, CP + 100, fun _ => ⟨CS ⊕ E', inferInstance, inferInstance, Option Sym × R',
    cnotProg PP, inferInstance, inferInstance, closed_cnotProg hPPcl, ?_⟩⟩
  intro P d r w K m c t z rest hrest prest S hclean hct hblk hS0 hS1 hS2
  have hcl : ∀ e : CS, S (.inr (.inl e)) = [] := fun e => hclean (.inl e)
  have hQ : S (.inl 2) = hdrSyms [1, (c : ℕ), (t : ℕ)] ++ prest := by
    rw [hS2, pairsSyms_single]
  -- phase 1: the counters
  set S1 := Function.update (Function.update (Function.update S (.inr (.inl .k2)) (natSyms m))
    (.inr (.inl .k3)) (natSyms c)) (.inr (.inl .k4)) (natSyms t) with hS1'
  have r1 : Runs (prep E') S S1 (fun _ => True)
      (7 * (permHdr P d r w K m).length + 13 * (bitLen c + bitLen t) + 50) := by
    apply Runs.of_eval
    intro v
    obtain ⟨v', T, e, hT⟩ := prep_eval P d r w K m c t hrest prest S v hcl hS1 hQ
    exact ⟨v', T, e, trivial, hT⟩
  have R1 := runs_callInj (ι := id) Function.injective_id (Lens.fst (Option Sym) R') (B := S)
    (B' := S1) r1 (fun k hk => (hk k rfl).elim)
  -- phase 2: the pair permutation
  set v0 := (encCube P z).map (crecBits w) with hv0
  set out := permByInv (pairPermAddr 2 m c t cnotPP.symm) v0 with hout
  set S2 := Function.update (Function.update S1 (.inl 0) rest) (.inr (.inl .y))
    (arrSyms out ++ S1 (.inr (.inl .y))) with hS2'
  have hlen : v0.length = 2 ^ m := by simp [hv0, encCube, encArr, cubeAddrs]
  have r2' := hPPspec m c t v0 rest [] [] [] (S1 ∘ ιPP E') c.isLt t.isLt
    (fun h => hct (Fin.ext h)) hlen hblk TermOK.nil TermOK.nil TermOK.nil
    (by simp [hS1', ιPP, hS0, hv0, carrSyms])
    (by simp [hS1', ιPP]) (by simp [hS1', ιPP]) (by simp [hS1', ιPP])
  have hcomp : Function.update (Function.update (S1 ∘ ιPP E') (.inl 0) rest) (.inl 1)
      (arrSyms out ++ (S1 ∘ ιPP E') (.inl 1)) = S2 ∘ ιPP E' := by
    funext x
    rcases x with ⟨i, hi⟩ | e
    · interval_cases i <;> simp [hS2', ιPP]
    · simp [hS2', ιPP]
  rw [hcomp] at r2'
  have R2 := runs_callInj ιPP_injective (Lens.snd (Option Sym) R') (B := S1) (B' := S2) r2'
    (by
      intro k hk
      rw [hS2', Function.update_of_ne (fun h => hk (.inl 1) (by rw [h]; rfl)),
        Function.update_of_ne (fun h => hk (.inl 0) (by rw [h]; rfl))])
  -- phase 3: move back and clean up
  set S3 := Function.update (Function.update (Function.update (Function.update
    (Function.update S2 (.inr (.inl .y)) []) (.inl 0) (arrSyms out ++ S2 (.inl 0)))
    (.inr (.inl .k2)) []) (.inr (.inl .k3)) []) (.inr (.inl .k4)) [] with hS3'
  have r3 : Runs (post E') S2 S3 (fun _ => True)
      (6 * (arrSyms out).length + 2 * (bitLen m + bitLen c + bitLen t) + 10) := by
    apply Runs.of_eval
    intro v
    refine ⟨none, _, (post_eval (arrSyms out) m c t S2 v (by simp [hS2', hS1', hcl])
      (by simp [hS2', hS1', hcl]) (by simp [hS2', hS1']) (by simp [hS2', hS1'])
      (by simp [hS2', hS1'])).of_eq rfl rfl, trivial, le_rfl⟩
  have R3 := runs_callInj (ι := id) Function.injective_id (Lens.fst (Option Sym) R') (B := S2)
    (B' := S3) r3 (fun k hk => (hk k rfl).elim)
  have hfinal : S3 = Function.update S (.inl 0)
      (carrSyms w (encCube P (cnotArr [(c, t)] z)) ++ rest) := by
    have hval : arrSyms out = carrSyms w (encCube P (cnotArr [(c, t)] z)) := by
      rw [hout, hv0, permByInv_cnot]
      rfl
    funext k
    rcases k with i | (e | e)
    · fin_cases i <;> simp [hS3', hS2', hS1', hval]
    · cases e <;> simp [hS3', hS2', hS1', hcl]
    · simp [hS3', hS2', hS1']
  refine WP.W9comp.runs_mono (WP.W9comp.runs_congr (WP.W9comp.runs_seq R1
    (WP.W9comp.runs_seq R2 R3)) hfinal) (fun _ _ => trivial) ?_
  have hV0 : vol v0 = cvolCube m r w := by
    rw [vol, hv0]
    exact length_carrSyms_encCube P w m r z
  have hVo : (arrSyms out).length = cvolCube m r w := by
    rw [hout, hv0, permByInv_cnot]
    exact length_carrSyms_encCube P w m r _
  rw [hV0, hVo]
  have hph : bitLen m ≤ (permHdr P d r w K m).length := by
    simp [permHdr, hdrSyms, length_natSyms]
    omega
  have hbc : bitLen c ≤ m := (WalshLift.bitLen_le_self c).trans c.isLt.le
  have hbt : bitLen t ≤ m := (WalshLift.bitLen_le_self t).trans t.isLt.le
  exact cost_le CP _ _ m w _ _ _ hph hbc hbt

end SubNLogN.Machine.WalshCnot1
