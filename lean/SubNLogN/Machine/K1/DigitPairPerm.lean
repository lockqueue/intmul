/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.DigitArith

/-!
# K1a (`K1/DigitPairPerm.lean`): fixed permutation of a digit pair, uniform radix

Paper: Fact 3.3(1) (`fact:oai-streams`) and Lemma A.4(1) (`lem:transfer-streams`),
Appendix A.1 (`sec:transfer-premises`).

**Scope (honest summary).** Proves `k1PairPerm_holds : K1PairPermStmt q π` for every `q` with
`NeZero q` and every fixed `π` (`Contracts/Streams.lean`, `K1PairPermStmt`), with no extra
hypotheses.
* `q = 1`: the array has one record; the program moves it (two record moves).
* `q ≥ 2`: build the descriptor of `k` positions with labels `A` at `i`, `B` at `j`
  (`K1/DigitBuild.lean`, cost `O(k log k) ≤ O(2^k) ≤ O(V)`), distribute by the descriptor walk in
  address order into the `q²` streams `(digit i, digit j)`, merge by the walk in reverse address
  order popping stream `π⁻¹ (e_i, e_j)`, remove the descriptor. Cost `C·(V + 1)`.

## Layout (`KU q = KLoc (Fin 5) (EU q)`)
Named `0` source, `1` destination, `2`/`3`/`4` the counters `k`, `i`, `j`; private scratch
`EU q = Key q ⊕ Fin 6`: the streams, the descriptor stack, the builder counter and three
temporaries. All scratch is restored.
-/

namespace SubNLogN.Machine.K1Digit

open TMFw TMFw.Contracts TMFw.Lib

/-- Private scratch of the uniform kernels. -/
abbrev EU (q : ℕ) : Type := Key q ⊕ Fin 6

/-- Stacks of the uniform kernels. -/
abbrev KU (q : ℕ) : Type := KLoc (Fin 5) (EU q)

section Layout

variable {q : ℕ}

def uSRC : KU q := .inl 0
def uDST : KU q := .inl 1
def uCK : KU q := .inl 2
def uCI : KU q := .inl 3
def uCJ : KU q := .inl 4
def uSTR (s : Key q) : KU q := .inr (.inl s)
def uDESC : KU q := .inr (.inr 0)
def uKC : KU q := .inr (.inr 1)
def uT1 : KU q := .inr (.inr 2)
def uT2 : KU q := .inr (.inr 3)
def uT3 : KU q := .inr (.inr 4)

def uStrIdx : KU q → Option (Key q)
  | .inr (.inl s) => some s
  | _ => none

theorem uPhaseOK : PhaseOK (uSRC : KU q) uDST uSTR uStrIdx where
  idx_str _ := rfl
  str_of_idx loc s h := by
    rcases loc with l | (s' | e)
    · simp [uStrIdx] at h
    · simp only [uStrIdx, Option.some.injEq] at h
      subst h
      rfl
    · simp [uStrIdx] at h
  idx_src := rfl
  idx_dst := rfl
  src_dst := by simp [uSRC, uDST]

theorem uBuildOK (CA CB : KU q) (hA : CA = uCI ∨ CA = uCJ) (hB : CB = uCI ∨ CB = uCJ) :
    BuildOK (uCK : KU q) CA CB uDESC uKC uT1 uT2 uT3 := by
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;>
  exact ⟨by simp [uKC, uCK], by simp [uKC, uCI, uCJ], by simp [uKC, uCI, uCJ],
    by simp [uKC, uDESC], by simp [uKC, uT1], by simp [uKC, uT2], by simp [uKC, uT3],
    by simp [uDESC, uCK], by simp [uDESC, uCI, uCJ], by simp [uDESC, uCI, uCJ],
    by simp [uT1, uCI, uCJ], by simp [uT2, uCI, uCJ], by simp [uT1, uCI, uCJ],
    by simp [uT2, uCI, uCJ], by simp [uT1, uT2], by simp [uCK, uT3]⟩

theorem uDESC_ne_SRC : (uDESC : KU q) ≠ uSRC := by simp [uDESC, uSRC]
theorem uDESC_ne_DST : (uDESC : KU q) ≠ uDST := by simp [uDESC, uDST]
theorem uDESC_ne_STR (s : Key q) : (uDESC : KU q) ≠ uSTR s := by simp [uDESC, uSTR]

end Layout

/-! ## Descriptor frames -/

theorem dSt_update {K : Type} [DecidableEq K] (G : K → List Sym) {desc a : K} (h : a ≠ desc)
    (D : List Lab) (drest : List Sym) (w : List Sym) :
    Function.update (dSt G desc D drest) a w = dSt (Function.update G a w) desc D drest := by
  unfold dSt
  exact (Function.update_comm h w _ G).symm

theorem dSt_apply {K : Type} [DecidableEq K] (G : K → List Sym) {desc a : K} (h : a ≠ desc)
    (D : List Lab) (drest : List Sym) : dSt G desc D drest a = G a := by
  unfold dSt
  exact Function.update_of_ne h _ _

/-! ## The two phases with the descriptor walk -/

section UPhases

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
theorem uLeaf1 (s1 : ℕ → Key q) (B0 : KU q → List Sym) (v : List (List Bool))
    (rest drest : List Sym) (t : ℕ) (ht : t < v.length) (w0 : CReg) :
    ∃ w1 c, Eval [] (leafP (fun _ => uSRC) (fun κ => uSTR κ))
        ⟨(w0, s1 t), dSt (st1 B0 uSRC uStrIdx v rest s1 t) uDESC [] drest⟩
        ⟨(w1, s1 t), dSt (st1 B0 uSRC uStrIdx v rest s1 (t + 1)) uDESC [] drest⟩ c ∧
      c + (3 * vol (v.drop (t + 1)) + (allKeys q).length * (v.length - (t + 1))) ≤
        3 * vol (v.drop t) + (allKeys q).length * (v.length - t) := by
  have hS : dSt (st1 B0 uSRC uStrIdx v rest s1 t) uDESC [] drest uSRC =
      (v.getD t []).map Sym.bit ++ Sym.sep :: (arrSyms (v.drop (t + 1)) ++ rest) := by
    rw [dSt_apply _ uDESC_ne_SRC.symm, st1_src, arrSyms_drop_succ v t ht]
    simp
  obtain ⟨c, hc, e⟩ := leafP_eval (fun _ => (uSRC : KU q)) (fun κ => uSTR κ) (s1 t)
    (uPhaseOK.str_ne_src _).symm w0 (v.getD t []) _ _ hS
  rw [dSt_apply _ (uDESC_ne_STR _).symm, dSt_update _ uDESC_ne_SRC.symm,
    dSt_update _ (uDESC_ne_STR _).symm, st1_step uPhaseOK] at e
  refine ⟨_, c, e, ?_⟩
  rw [vol_drop_succ v t ht]
  have h1 : v.length - t = (v.length - (t + 1)) + 1 := by omega
  rw [h1, Nat.mul_succ]
  omega

omit [NeZero q] in
theorem uLeaf2 (sel2 : Key q → Key q) (s2 : ℕ → Key q) (B1 : KU q → List Sym) (N : ℕ)
    (pay : ℕ → List Bool) (drest : List Sym) (u : ℕ) (hu : u < N) (κ : Key q)
    (hκ : sel2 κ = s2 (N - 1 - u)) (w0 : CReg) :
    ∃ w1 c, Eval [] (leafP (fun κ => uSTR (sel2 κ)) (fun _ => uDST))
        ⟨(w0, κ), dSt (st2 B1 uDST uStrIdx N pay s2 u) uDESC [] drest⟩
        ⟨(w1, κ), dSt (st2 B1 uDST uStrIdx N pay s2 (u + 1)) uDESC [] drest⟩ c ∧
      c + (3 * vol ((List.range (N - (u + 1))).map pay) + (allKeys q).length * (N - (u + 1))) ≤
        3 * vol ((List.range (N - u)).map pay) + (allKeys q).length * (N - u) := by
  have hS : dSt (st2 B1 uDST uStrIdx N pay s2 u) uDESC [] drest (uSTR (sel2 κ)) =
      ((pay (N - 1 - u)).reverse).map Sym.bit ++ Sym.sep ::
        (streamC ((List.range (N - 1 - u)).filter (fun y => s2 y = s2 (N - 1 - u))) pay ++
          B1 (uSTR (s2 (N - 1 - u)))) := by
    rw [dSt_apply _ (uDESC_ne_STR _).symm, hκ, st2_stream uPhaseOK B1 N pay s2 u hu]
  obtain ⟨c, hc, e⟩ := leafP_eval (fun κ => (uSTR (sel2 κ) : KU q)) (fun _ => uDST) κ
    (uPhaseOK.str_ne_dst _) w0 _ _ _ hS
  rw [dSt_apply _ uDESC_ne_DST.symm, dSt_update _ (uDESC_ne_STR _).symm,
    dSt_update _ uDESC_ne_DST.symm, hκ, st2_step uPhaseOK B1 N pay s2 u hu] at e
  refine ⟨_, c, e, ?_⟩
  have h1 : N - u = (N - (u + 1)) + 1 := by omega
  have h2 : N - (u + 1) = N - 1 - u := by omega
  rw [h1, List.range_succ, List.map_append, vol_append, h2]
  simp only [List.map_cons, List.map_nil, vol_cons, List.length_reverse] at hc ⊢
  rw [Nat.mul_succ]
  have : vol ([] : List (List Bool)) = 0 := rfl
  omega

theorem uPhase1 (D : List Lab) (v : List (List Bool)) (hN : v.length = q ^ D.length)
    (s1 : ℕ → Key q) (κ0 : Key q) (hsel : ∀ x < v.length, keyAt q D κ0 x = s1 x)
    (B0 : KU q → List Sym) (rest drest : List Sym) (w : CReg) :
    ∃ w' κ' c, Eval [] (walk uDESC (ordL q true) (leafP (fun _ => uSRC) (fun κ => uSTR κ)))
        ⟨(w, κ0), dSt (st1 B0 uSRC uStrIdx v rest s1 0) uDESC D drest⟩
        ⟨(w', κ'), dSt (st1 B0 uSRC uStrIdx v rest s1 v.length) uDESC D drest⟩ c ∧
      c ≤ 3 * vol v + (allKeys q).length * v.length + (3 * q + 6) * nodes q D.length + 2 := by
  have hyps : LeafHyps (leafP (fun _ => uSRC) (fun κ => uSTR κ)) uDESC
      (st1 B0 uSRC uStrIdx v rest s1) drest
      (fun t => 3 * vol (v.drop t) + (allKeys q).length * (v.length - t))
      (fun u => keyAt q D κ0 (posL true (q ^ D.length) u)) 0 (q ^ D.length) := by
    intro u hu w0
    rw [← hN] at hu
    simp only [posL, if_true, Nat.zero_add]
    rw [hsel u hu]
    exact uLeaf1 s1 B0 v rest drest u hu w0
  obtain ⟨w', κ', c, e, hc⟩ := walk_spec uDESC true _ (st1 B0 uSRC uStrIdx v rest s1) drest _
    (3 * q + 6) [] (leafP_closed _ _) le_rfl D 0 κ0 w hyps
  rw [Nat.zero_add, ← hN] at e hc
  refine ⟨w', κ', c, e, ?_⟩
  simp only [List.drop_length, Nat.sub_self, Nat.mul_zero, List.drop_zero, Nat.sub_zero] at hc
  have : vol ([] : List (List Bool)) = 0 := rfl
  omega

theorem uPhase2 (sel2 : Key q → Key q) (D : List Lab) (N : ℕ) (hN : N = q ^ D.length)
    (pay : ℕ → List Bool) (s2 : ℕ → Key q) (κ0 : Key q)
    (hsel : ∀ y < N, sel2 (keyAt q D κ0 y) = s2 y)
    (B1 : KU q → List Sym) (drest : List Sym) (w : CReg) :
    ∃ w' κ' c, Eval [] (walk uDESC (ordL q false) (leafP (fun κ => uSTR (sel2 κ)) (fun _ => uDST)))
        ⟨(w, κ0), dSt (st2 B1 uDST uStrIdx N pay s2 0) uDESC D drest⟩
        ⟨(w', κ'), dSt (st2 B1 uDST uStrIdx N pay s2 N) uDESC D drest⟩ c ∧
      c ≤ 3 * vol ((List.range N).map pay) + (allKeys q).length * N +
        (3 * q + 6) * nodes q D.length + 2 := by
  have hyps : LeafHyps (leafP (fun κ => uSTR (sel2 κ)) (fun _ => uDST)) uDESC
      (st2 B1 uDST uStrIdx N pay s2) drest
      (fun t => 3 * vol ((List.range (N - t)).map pay) + (allKeys q).length * (N - t))
      (fun u => keyAt q D κ0 (posL false (q ^ D.length) u)) 0 (q ^ D.length) := by
    intro u hu w0
    rw [← hN] at hu
    simp only [posL, Bool.false_eq_true, if_false, Nat.zero_add]
    rw [← hN]
    exact uLeaf2 sel2 s2 B1 N pay drest u hu _ (hsel _ (by omega)) w0
  obtain ⟨w', κ', c, e, hc⟩ := walk_spec uDESC false _ (st2 B1 uDST uStrIdx N pay s2) drest _
    (3 * q + 6) [] (leafP_closed _ _) le_rfl D 0 κ0 w hyps
  rw [Nat.zero_add, ← hN] at e hc
  refine ⟨w', κ', c, e, ?_⟩
  simp only [Nat.sub_self, Nat.mul_zero, Nat.sub_zero, List.range_zero, List.map_nil] at hc
  have : vol ([] : List (List Bool)) = 0 := rfl
  omega

end UPhases
/-! ## The programs -/

section Progs

variable {q : ℕ}

/-- **The uniform pair-permutation kernel** (used for `q ≥ 2`). -/
def ppuProg [NeZero q] (π : Equiv.Perm (Key q)) : DProg (KU q) q :=
  .seq (buildDesc uCK uCI uCJ uDESC uKC uT1 uT2 uT3)
    (.seq (walk uDESC (ordL q true) (leafP (fun _ => uSRC) (fun κ => uSTR κ)))
      (.seq (walk uDESC (ordL q false) (leafP (fun κ => uSTR (π.symm κ)) (fun _ => uDST)))
        (teardown uDESC)))

theorem ppuProg_closed [NeZero q] (π : Equiv.Perm (Key q)) : (ppuProg π).Closed :=
  ⟨buildDesc_closed _ _ _ _ _ _ _ _, walk_closed _ _ _ (leafP_closed _ _),
    walk_closed _ _ _ (leafP_closed _ _), teardown_closed _⟩

/-- The single-record kernel (used for `q = 1`): two record moves through `uT1`. -/
def oneProg : DProg (KU q) q := .seq (liftS (moveRecP uSRC uT1)) (liftS (moveRecP uT1 uDST))

theorem oneProg_closed : (oneProg : DProg (KU q) q).Closed :=
  ⟨liftS_closed (moveRecP_closed _ _), liftS_closed (moveRecP_closed _ _)⟩

end Progs

theorem sq_le_two_pow : ∀ k : ℕ, k * k ≤ 2 * 2 ^ k
  | 0 => by norm_num
  | k + 1 => by
    have ih := sq_le_two_pow k
    have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    rw [pow_succ]
    nlinarith

/-! ## The contract -/

/-- **[PROVED] K1a**: `K1PairPermStmt q π` holds for every `q ≥ 1` and every fixed permutation `π`
of `Fin q × Fin q`. -/
theorem k1PairPerm_holds (q : ℕ) [NeZero q] (π : Equiv.Perm (Fin q × Fin q)) :
    K1PairPermStmt q π := by
  rcases Nat.lt_or_ge q 2 with hq | hq
  · -- one record
    have hq1 : q = 1 := by have := Nat.pos_of_neZero q; omega
    subst hq1
    refine ⟨8, fun _ => ⟨EU 1, inferInstance, inferInstance, Reg 1, oneProg, inferInstance,
      ⟨((none, none, .eq), (0, 0))⟩, oneProg_closed, ?_⟩⟩
    intro k i j v rest r2 r3 r4 S hi hj hij hlen hrest hr2 hr3 hr4 hS hS2 hS3 hS4
    rw [one_pow] at hlen
    obtain ⟨p, rfl⟩ : ∃ p, v = [p] := List.length_eq_one_iff.1 hlen
    have hout : permByInv (pairPermAddr 1 k i j π.symm) [p] = [p] := by
      simp [permByInv, pairPermAddr, setDigit, digitAt]
    rw [hout]
    refine Runs.of_eval fun v0 => ?_
    have hS' : S uSRC = p.map Sym.bit ++ Sym.sep :: rest := by
      simpa [uSRC, arrSyms, blk, recSyms] using hS
    have e1 := liftS_eval (q := 1) v0 (moveRecP_eval (src := (uSRC : KU 1)) (dst := uT1)
      (by simp [uSRC, uT1]) v0.1.1 p rest S hS')
    have hT : Function.update (Function.update S uSRC rest) uT1
        (p.reverse.map Sym.bit ++ Sym.sep :: S uT1) uT1 =
        p.reverse.map Sym.bit ++ Sym.sep :: S uT1 := Function.update_self _ _ _
    have e2 := liftS_eval (q := 1) ((some Sym.sep, v0.1.2), v0.2)
      (moveRecP_eval (src := (uT1 : KU 1)) (dst := uDST) (by simp [uT1, uDST]) (some Sym.sep)
        p.reverse (S uT1) _ hT)
    have hfin : Function.update (Function.update (Function.update (Function.update S uSRC rest) uT1
        (p.reverse.map Sym.bit ++ Sym.sep :: S uT1)) uT1 (S uT1)) uDST
        (p.reverse.reverse.map Sym.bit ++ Sym.sep :: Function.update (Function.update S uSRC rest)
          uT1 (p.reverse.map Sym.bit ++ Sym.sep :: S uT1) uDST) =
        Function.update (Function.update S uSRC rest) uDST (arrSyms [p] ++ S uDST) := by
      funext x
      by_cases h1 : x = uDST
      · subst h1
        simp [uDST, uSRC, uT1, arrSyms, blk, recSyms]
      · by_cases h2 : x = uT1
        · subst h2
          simp [uDST, uSRC, uT1]
        · simp only [Function.update_apply, h1, h2, if_false]
    rw [hfin] at e2
    refine ⟨_, _, Eval.seq e1 e2, trivial, ?_⟩
    simp only [vol, arrSyms, blk, recSyms, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.length_append, List.length_map, List.length_singleton,
      List.length_reverse]
    omega
  · -- the general case
    refine ⟨2 * (allKeys q).length + 12 * q + 300, fun _ => ⟨EU q, inferInstance, inferInstance,
      Reg q, ppuProg π, inferInstance, ⟨((none, none, .eq), (0, 0))⟩, ppuProg_closed π, ?_⟩⟩
    intro k i j v rest r2 r3 r4 S hi hj hij hlen hrest hr2 hr3 hr4 hS hS2 hS3 hS4
    refine Runs.of_eval fun v0 => ?_
    obtain ⟨w, κ⟩ := v0
    obtain ⟨vb, cb, hcb, eb⟩ := buildDesc_eval (uBuildOK uCI uCJ (Or.inl rfl) (Or.inr rfl)) S k i j
      r2 r3 r4 hr2 hr3 hr4 hS2 hS3 hS4 (w, κ)
    have hD : (descL k i j).length = k := descL_length k i j
    have hN : v.length = q ^ (descL k i j).length := by rw [hD, hlen]
    have hkey : ∀ (κ0 : Key q) (x : ℕ), x < v.length →
        keyAt q (descL k i j) κ0 x = ukey q k i j x := by
      intro κ0 x hx
      exact keyAt_descL hi hj hij κ0 (by rw [← hlen]; exact hx)
    have hf : ∀ y < v.length, pairPermAddr q k i j π.symm y < v.length := by
      intro y hy
      rw [hlen] at hy ⊢
      exact ppu_lt q k i j π.symm hi hj y hy
    have hs : ∀ y < v.length, ukey q k i j (pairPermAddr q k i j π.symm y) =
        π.symm (ukey q k i j y) := fun y _ => ppu_key q k i j π.symm hi hj hij y
    have hmono : ∀ y y', y < v.length → y' < v.length →
        π.symm (ukey q k i j y) = π.symm (ukey q k i j y') → y < y' →
        pairPermAddr q k i j π.symm y < pairPermAddr q k i j π.symm y' := by
      intro y y' _ _ he hlt
      have hk : ukey q k i j y = ukey q k i j y' := π.symm.injective he
      have h1 := ppu_shift q k i j π.symm hi hj hij y
      have h2 := ppu_shift q k i j π.symm hi hj hij y'
      rw [hk] at h1
      omega
    obtain ⟨w1, κ1, c1, e1, hc1⟩ := uPhase1 (descL k i j) v hN (ukey q k i j) vb.2
      (fun x hx => hkey vb.2 x hx) S rest (S uDESC) vb.1
    have hS' : S uSRC = arrSyms v ++ rest := hS
    rw [st1_zero (strIdx := uStrIdx) S v rest _ hS'] at e1
    have hL := filter_eq_map_filter v.length (ukey q k i j) (fun y => π.symm (ukey q k i j y))
      (pairPermAddr q k i j π.symm) hf hs hmono
    rw [st1_last uPhaseOK S v rest _ _ _ hL] at e1
    obtain ⟨w2, κ2, c2, e2, hc2⟩ := uPhase2 π.symm (descL k i j) v.length hN
      (fun y => v.getD (pairPermAddr q k i j π.symm y) []) (fun y => π.symm (ukey q k i j y)) κ1
      (fun y hy => by rw [hkey κ1 y hy]) (Function.update S uSRC rest) (S uDESC) w1
    rw [st2_last] at e2
    obtain ⟨vt, ct, hct, et⟩ := teardown_eval uDESC
      (Function.update (Function.update S uSRC rest) uDST
        (arrSyms ((List.range v.length).map fun y => v.getD (pairPermAddr q k i j π.symm y) []) ++
          Function.update S uSRC rest uDST)) (descL k i j) (S uDESC) (w2, κ2)
    have hfin : Function.update (Function.update (Function.update S uSRC rest) uDST
        (arrSyms ((List.range v.length).map fun y => v.getD (pairPermAddr q k i j π.symm y) []) ++
          Function.update S uSRC rest uDST)) uDESC (S uDESC) =
        Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (pairPermAddr q k i j π.symm) v) ++ S (.inl 1)) := by
      funext x
      by_cases h1 : x = uDESC
      · subst h1
        simp [uDESC, uSRC, uDST]
      · rw [Function.update_of_ne h1]
        rfl
    rw [hfin] at et
    refine ⟨vt, _, Eval.seq eb (Eval.seq e1 (Eval.seq e2 et)), trivial, ?_⟩
    -- cost
    have hvol := vol_map_perm v (pairPermAddr q k i j π.symm) hf
      (inj_of_mono v.length (ukey q k i j) (fun y => π.symm (ukey q k i j y)) _ hs hmono)
    rw [hvol] at hc2
    rw [hD] at hc1 hc2 hct
    have hnodes := nodes_le hq k
    have hvl := length_le_vol v
    have hqk : 2 ^ k ≤ q ^ k := Nat.pow_le_pow_left hq k
    have hk2 : k < 2 ^ k := Nat.lt_two_pow_self
    have hsq := sq_le_two_pow k
    have hbl := bitLen_le_self k
    have hkb : k * bitLen k ≤ k * k := Nat.mul_le_mul_left k hbl
    rw [hlen] at hvl
    have h3 : (3 * q + 6) * nodes q k ≤ (3 * q + 6) * (2 * q ^ k) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : (allKeys q).length * v.length ≤ (allKeys q).length * vol v :=
      Nat.mul_le_mul_left _ (length_le_vol v)
    have h5 : (3 * q + 6) * (2 * q ^ k) ≤ (3 * q + 6) * (2 * vol v) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith

end SubNLogN.Machine.K1Digit
