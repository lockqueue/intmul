/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.DigitNest

/-!
# K1 digit engine, part 5 (`K1/DigitMix.lean`): the two-phase program for mixed shapes

Paper: Lemma A.4(1)–(2) (`lem:transfer-streams`).

**Scope (honest summary).** A generic two-phase kernel over the layout of the `…MixStmt`
contracts (`Contracts/Streams.lean` §5) and its exact `Runs` theorem `mixProg_runs`. The concrete
contracts are proved in `K1/DigitPairPermMix.lean` and `K1/DigitMoveDigitMix.lean`.

## Layout (`KM q = KLoc (Fin 4) (EM q)`)
Named: `0` source, `1` destination, `2`/`3` the counters `N1`, `N2` (`mNP 0`, `mNP 1`).
Private scratch `EM q = Key q ⊕ Fin 4`: the `q²` streams `mSTR s`, the counter stacks `mC 0`,
`mC 1`, the temporary `mCT` and the block-tick stack `mU`. All scratch is restored.

## Program (`mixProg sel1 sel2 D1 D2`)
`push delim on U; dataLoop1 (nest asc … D1 with leaf SRC → STR (sel1 κ));
dataLoop2 (nest desc … D2 with leaf STR (sel2 κ) → DST)`.
-/

namespace SubNLogN.Machine.K1Digit

open TMFw TMFw.Contracts TMFw.Lib

/-! ## Layout -/

/-- Private scratch of the mixed-shape kernels. -/
abbrev EM (q : ℕ) : Type := Key q ⊕ Fin 4

/-- Stacks of the mixed-shape kernels. -/
abbrev KM (q : ℕ) : Type := KLoc (Fin 4) (EM q)

section Layout

variable {q : ℕ}

def mSRC : KM q := .inl 0
def mDST : KM q := .inl 1
def mNP (r : Fin 2) : KM q := .inl ⟨r.val + 2, by omega⟩
def mSTR (s : Key q) : KM q := .inr (.inl s)
def mC (r : Fin 2) : KM q := .inr (.inr ⟨r.val, by omega⟩)
def mCT : KM q := .inr (.inr 2)
def mU : KM q := .inr (.inr 3)

/-- Private stacks: the counters and the tick stack. -/
def mPriv : KM q → Bool
  | .inr (.inr i) => decide (i.val ≠ 2)
  | _ => false

/-- Stream decoder. -/
def mStrIdx : KM q → Option (Key q)
  | .inr (.inl s) => some s
  | _ => none

theorem mPhaseOK : PhaseOK (mSRC : KM q) mDST mSTR mStrIdx where
  idx_str _ := rfl
  str_of_idx loc s h := by
    rcases loc with l | (s' | e)
    · simp [mStrIdx] at h
    · simp only [mStrIdx, Option.some.injEq] at h
      subst h
      rfl
    · simp [mStrIdx] at h
  idx_src := rfl
  idx_dst := rfl
  src_dst := by simp [mSRC, mDST]

theorem mNestOK : NestOK (mPriv : KM q → Bool) mNP mC mCT where
  c_priv r := by fin_cases r <;> rfl
  np_pub r := rfl
  ct_pub := rfl
  ct_np r := by fin_cases r <;> simp [mCT, mNP]

theorem mPriv_U : mPriv (mU : KM q) = true := rfl
theorem mPriv_SRC : mPriv (mSRC : KM q) = false := rfl
theorem mPriv_DST : mPriv (mDST : KM q) = false := rfl
theorem mPriv_STR (s : Key q) : mPriv (mSTR s : KM q) = false := rfl
theorem mStrIdx_NP (r : Fin 2) : mStrIdx (mNP r : KM q) = none := rfl
theorem mNP_ne_SRC (r : Fin 2) : (mNP r : KM q) ≠ mSRC := by
  fin_cases r <;> simp [mNP, mSRC]
theorem mNP_ne_DST (r : Fin 2) : (mNP r : KM q) ≠ mDST := by
  fin_cases r <;> simp [mNP, mDST]

end Layout

/-! ## Leaves of the two phases -/

section Leaves

variable {q : ℕ}

theorem isRecR_rec_head (p : List Bool) (L : List Sym) :
    TMFw.W4.isRecR (p.map Sym.bit ++ Sym.sep :: L).head? = true := by
  cases p <;> rfl

/-- Distribute leaf at time `t`. -/
theorem mixLeaf1 (sel1 : Key q → Key q) (s1 : ℕ → Key q) (B0 : KM q → List Sym)
    (v : List (List Bool)) (rest : List Sym) (t : ℕ) (ht : t < v.length) (κ : Key q)
    (hκ : sel1 κ = s1 t) (X : KM q → List Sym) (w0 : CReg) :
    ∃ w1 c, Eval [] (leafP (fun _ => mSRC) (fun κ => mSTR (sel1 κ)))
        ⟨(w0, κ), ovl mPriv (st1 B0 mSRC mStrIdx v rest s1 t) X⟩
        ⟨(w1, κ), ovl mPriv (st1 B0 mSRC mStrIdx v rest s1 (t + 1)) X⟩ c ∧
      c + (3 * vol (v.drop (t + 1)) + (allKeys q).length * (v.length - (t + 1))) ≤
        3 * vol (v.drop t) + (allKeys q).length * (v.length - t) := by
  have hS : ovl mPriv (st1 B0 mSRC mStrIdx v rest s1 t) X mSRC =
      (v.getD t []).map Sym.bit ++ Sym.sep :: (arrSyms (v.drop (t + 1)) ++ rest) := by
    rw [ovl_pub mPriv_SRC, st1_src, arrSyms_drop_succ v t ht]
    simp
  obtain ⟨c, hc, e⟩ := leafP_eval (fun _ => (mSRC : KM q)) (fun κ => mSTR (sel1 κ)) κ
    (mPhaseOK.str_ne_src _).symm w0 (v.getD t []) _ _ hS
  rw [ovl_pub (mPriv_STR _), ovl_update_pub mPriv_SRC, ovl_update_pub (mPriv_STR _), hκ,
    st1_step mPhaseOK] at e
  refine ⟨_, c, e, ?_⟩
  rw [vol_drop_succ v t ht]
  have h1 : v.length - t = (v.length - (t + 1)) + 1 := by omega
  rw [h1, Nat.mul_succ]
  omega

/-- Merge leaf at output time `u` (output address `N - 1 - u`). -/
theorem mixLeaf2 (sel2 : Key q → Key q) (s2 : ℕ → Key q) (B1 : KM q → List Sym) (N : ℕ)
    (pay : ℕ → List Bool) (u : ℕ) (hu : u < N) (κ : Key q) (hκ : sel2 κ = s2 (N - 1 - u))
    (X : KM q → List Sym) (w0 : CReg) :
    ∃ w1 c, Eval [] (leafP (fun κ => mSTR (sel2 κ)) (fun _ => mDST))
        ⟨(w0, κ), ovl mPriv (st2 B1 mDST mStrIdx N pay s2 u) X⟩
        ⟨(w1, κ), ovl mPriv (st2 B1 mDST mStrIdx N pay s2 (u + 1)) X⟩ c ∧
      c + (3 * vol ((List.range (N - (u + 1))).map pay) + (allKeys q).length * (N - (u + 1))) ≤
        3 * vol ((List.range (N - u)).map pay) + (allKeys q).length * (N - u) := by
  have hS : ovl mPriv (st2 B1 mDST mStrIdx N pay s2 u) X (mSTR (sel2 κ)) =
      ((pay (N - 1 - u)).reverse).map Sym.bit ++ Sym.sep ::
        (streamC ((List.range (N - 1 - u)).filter (fun y => s2 y = s2 (N - 1 - u))) pay ++
          B1 (mSTR (s2 (N - 1 - u)))) := by
    rw [ovl_pub (mPriv_STR _), hκ, st2_stream mPhaseOK B1 N pay s2 u hu]
  obtain ⟨c, hc, e⟩ := leafP_eval (fun κ => (mSTR (sel2 κ) : KM q)) (fun _ => mDST) κ
    (mPhaseOK.str_ne_dst _) w0 _ _ _ hS
  rw [ovl_pub mPriv_DST, ovl_update_pub (mPriv_STR _), ovl_update_pub mPriv_DST, hκ,
    st2_step mPhaseOK B1 N pay s2 u hu] at e
  refine ⟨_, c, e, ?_⟩
  have h1 : N - u = (N - (u + 1)) + 1 := by omega
  have h2 : N - (u + 1) = N - 1 - u := by omega
  rw [h1, List.range_succ, List.map_append, vol_append, h2]
  simp only [List.map_cons, List.map_nil, vol_cons, List.length_reverse] at hc ⊢
  rw [Nat.mul_succ]
  have : vol ([] : List (List Bool)) = 0 := rfl
  omega

end Leaves

/-! ## The two phases -/

section Phases

variable {q : ℕ} [NeZero q]

theorem mod_rev (M0 Bs m u : ℕ) (hm : m < M0) (hu : u < Bs) :
    (M0 * Bs - 1 - (m * Bs + u)) % Bs = Bs - 1 - u := by
  obtain ⟨a, rfl⟩ : ∃ a, M0 = m + 1 + a := ⟨M0 - m - 1, by omega⟩
  have h : (m + 1 + a) * Bs - 1 - (m * Bs + u) = a * Bs + (Bs - 1 - u) := by
    have e : (m + 1 + a) * Bs = m * Bs + Bs + a * Bs := by ring
    rw [e]
    omega
  rw [h, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

theorem mixPhase1 (sel1 : Key q → Key q) (D : List NLab) (Ns : Fin 2 → ℕ)
    (v : List (List Bool)) (M0 : ℕ) (hlen : v.length = M0 * sizeN q Ns D)
    (hM0 : 0 < sizeN q Ns D ∨ M0 = 0) (s1 : ℕ → Key q)
    (hsel : ∀ (κ : Key q) (x : ℕ), x < v.length →
      sel1 (keyN q Ns D κ (x % sizeN q Ns D)) = s1 x)
    (B0 : KM q → List Sym) (rest : List Sym) (hrest : BlkTerm rest) (rr : Fin 2 → List Sym)
    (hrr : ∀ r, TermOK (rr r)) (hNP : ∀ r, B0 (mNP r) = natSyms (Ns r) ++ rr r)
    (X : KM q → List Sym) (κ : Key q) (w : CReg) :
    ∃ w' κ' c, Eval [] (dataLoop1 mSRC mU (nest (ordL q true) mNP mC mCT
          (leafP (fun _ => mSRC) (fun κ => mSTR (sel1 κ))) D))
        ⟨(w, κ), ovl mPriv (st1 B0 mSRC mStrIdx v rest s1 0) X⟩
        ⟨(w', κ'), ovl mPriv (st1 B0 mSRC mStrIdx v rest s1 v.length)
          (Function.update X mU (List.replicate M0 tickSym ++ X mU))⟩ c ∧
      c ≤ 3 * vol v + (allKeys q).length * v.length + M0 * (ohN q Ns D + 3) + 2 := by
  have hG : ∀ r t, st1 B0 mSRC mStrIdx v rest s1 t (mNP r) = natSyms (Ns r) ++ rr r := by
    intro r t
    simp [st1, mNP_ne_SRC, streamPart, mStrIdx_NP, hNP]
  have hbody : ∀ m < M0, ∀ (κ : Key q) (w : CReg) (X : KM q → List Sym), ∃ w' κ' c,
      Eval [] (nest (ordL q true) mNP mC mCT (leafP (fun _ => mSRC) (fun κ => mSTR (sel1 κ))) D)
        ⟨(w, κ), ovl mPriv (st1 B0 mSRC mStrIdx v rest s1 (m * sizeN q Ns D)) X⟩
        ⟨(w', κ'), ovl mPriv (st1 B0 mSRC mStrIdx v rest s1 ((m + 1) * sizeN q Ns D)) X⟩ c ∧
        c + (3 * vol (v.drop ((m + 1) * sizeN q Ns D)) +
          (allKeys q).length * (v.length - (m + 1) * sizeN q Ns D)) ≤
        (3 * vol (v.drop (m * sizeN q Ns D)) +
          (allKeys q).length * (v.length - m * sizeN q Ns D)) + ohN q Ns D := by
    intro m hm κ w X
    have hyps : LeafHypsN mPriv (leafP (fun _ => mSRC) (fun κ => mSTR (sel1 κ)))
        (st1 B0 mSRC mStrIdx v rest s1)
        (fun t => 3 * vol (v.drop t) + (allKeys q).length * (v.length - t))
        (fun u => keyN q Ns D κ (posL true (sizeN q Ns D) u)) (m * sizeN q Ns D)
        (sizeN q Ns D) := by
      intro u hu X' w0
      have hlt : m * sizeN q Ns D + u < v.length := by
        rw [hlen]
        calc m * sizeN q Ns D + u < m * sizeN q Ns D + sizeN q Ns D := by omega
          _ = (m + 1) * sizeN q Ns D := by ring
          _ ≤ M0 * sizeN q Ns D := Nat.mul_le_mul_right _ hm
      have hk := hsel κ (m * sizeN q Ns D + u) hlt
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu, Nat.add_comm] at hk
      simp only [posL, if_true]
      exact mixLeaf1 sel1 s1 B0 v rest _ hlt _ hk X' w0
    obtain ⟨w', κ', c, e, -, hc⟩ := nest_spec (dir := true) mNestOK rr hrr hG D
      (m * sizeN q Ns D) κ w X hyps
    rw [show m * sizeN q Ns D + sizeN q Ns D = (m + 1) * sizeN q Ns D by ring] at e hc
    exact ⟨w', κ', c, e, hc⟩
  have htest : ∀ m ≤ M0, TMFw.W4.isRecR
      (st1 B0 mSRC mStrIdx v rest s1 (m * sizeN q Ns D) mSRC).head? = decide (m < M0) := by
    intro m hm
    rw [st1_src]
    by_cases hlt : m < M0
    · have hpos : 0 < sizeN q Ns D := by
        rcases hM0 with h | h
        · exact h
        · omega
      have ht : m * sizeN q Ns D < v.length := by
        rw [hlen]
        exact Nat.mul_lt_mul_of_pos_right hlt hpos
      rw [arrSyms_drop_succ v _ ht, List.append_assoc, List.cons_append, isRecR_rec_head]
      simp [hlt]
    · have hm' : m = M0 := by omega
      subst hm'
      rw [← hlen, List.drop_length]
      simp only [arrSyms, blk, List.map_nil, List.flatten_nil, List.nil_append, hlt,
        decide_false]
      exact TMFw.W4.isRecR_head?_of_recTerm (TMFw.W4.RecTerm.of_blkTerm hrest)
  obtain ⟨w', κ', c, e, hc⟩ := dataLoop1_spec (G := st1 B0 mSRC mStrIdx v rest s1)
    (Pot := fun t => 3 * vol (v.drop t) + (allKeys q).length * (v.length - t)) mSRC mU mPriv_U
    mPriv_SRC _ (sizeN q Ns D) M0 (ohN q Ns D) hbody htest X κ w
  rw [← hlen] at e hc
  refine ⟨w', κ', c, e, ?_⟩
  simp only [List.drop_length, Nat.sub_self, Nat.mul_zero, List.drop_zero, Nat.sub_zero,
    Nat.zero_mul] at hc
  have : vol ([] : List (List Bool)) = 0 := rfl
  omega

theorem mixPhase2 (sel2 : Key q → Key q) (D : List NLab) (Ns : Fin 2 → ℕ) (N M0 : ℕ)
    (hN : N = M0 * sizeN q Ns D) (pay : ℕ → List Bool) (s2 : ℕ → Key q)
    (hsel : ∀ (κ : Key q) (y : ℕ), y < N → sel2 (keyN q Ns D κ (y % sizeN q Ns D)) = s2 y)
    (B1 : KM q → List Sym) (rr : Fin 2 → List Sym) (hrr : ∀ r, TermOK (rr r))
    (hNP : ∀ r, B1 (mNP r) = natSyms (Ns r) ++ rr r) (X : KM q → List Sym) (κ : Key q)
    (w : CReg) :
    ∃ w' κ' c, Eval [] (dataLoop2 mU (nest (ordL q false) mNP mC mCT
          (leafP (fun κ => mSTR (sel2 κ)) (fun _ => mDST)) D))
        ⟨(w, κ), ovl mPriv (st2 B1 mDST mStrIdx N pay s2 0)
          (Function.update X mU (List.replicate M0 tickSym ++ delimSym :: X mU))⟩
        ⟨(w', κ'), ovl mPriv (st2 B1 mDST mStrIdx N pay s2 N) X⟩ c ∧
      c ≤ 3 * vol ((List.range N).map pay) + (allKeys q).length * N + M0 * (ohN q Ns D + 2) + 2 := by
  have hG : ∀ r t, st2 B1 mDST mStrIdx N pay s2 t (mNP r) = natSyms (Ns r) ++ rr r := by
    intro r t
    simp [st2, mNP_ne_DST, streamPart, mStrIdx_NP, hNP]
  have hbody : ∀ m < M0, ∀ (κ : Key q) (w : CReg) (X : KM q → List Sym), ∃ w' κ' c,
      Eval [] (nest (ordL q false) mNP mC mCT (leafP (fun κ => mSTR (sel2 κ)) (fun _ => mDST)) D)
        ⟨(w, κ), ovl mPriv (st2 B1 mDST mStrIdx N pay s2 (m * sizeN q Ns D)) X⟩
        ⟨(w', κ'), ovl mPriv (st2 B1 mDST mStrIdx N pay s2 ((m + 1) * sizeN q Ns D)) X⟩ c ∧
        c + (3 * vol ((List.range (N - (m + 1) * sizeN q Ns D)).map pay) +
          (allKeys q).length * (N - (m + 1) * sizeN q Ns D)) ≤
        (3 * vol ((List.range (N - m * sizeN q Ns D)).map pay) +
          (allKeys q).length * (N - m * sizeN q Ns D)) + ohN q Ns D := by
    intro m hm κ w X
    have hyps : LeafHypsN mPriv (leafP (fun κ => mSTR (sel2 κ)) (fun _ => mDST))
        (st2 B1 mDST mStrIdx N pay s2)
        (fun t => 3 * vol ((List.range (N - t)).map pay) + (allKeys q).length * (N - t))
        (fun u => keyN q Ns D κ (posL false (sizeN q Ns D) u)) (m * sizeN q Ns D)
        (sizeN q Ns D) := by
      intro u hu X' w0
      have hlt : m * sizeN q Ns D + u < N := by
        rw [hN]
        calc m * sizeN q Ns D + u < m * sizeN q Ns D + sizeN q Ns D := by omega
          _ = (m + 1) * sizeN q Ns D := by ring
          _ ≤ M0 * sizeN q Ns D := Nat.mul_le_mul_right _ hm
      have hk := hsel κ (N - 1 - (m * sizeN q Ns D + u)) (by omega)
      rw [hN, mod_rev M0 _ m u hm hu, ← hN] at hk
      simp only [posL, Bool.false_eq_true, if_false]
      exact mixLeaf2 sel2 s2 B1 N pay _ hlt _ hk X' w0
    obtain ⟨w', κ', c, e, -, hc⟩ := nest_spec (dir := false) mNestOK rr hrr hG D
      (m * sizeN q Ns D) κ w X hyps
    rw [show m * sizeN q Ns D + sizeN q Ns D = (m + 1) * sizeN q Ns D by ring] at e hc
    exact ⟨w', κ', c, e, hc⟩
  obtain ⟨w', κ', c, e, hc⟩ := dataLoop2_spec (G := st2 B1 mDST mStrIdx N pay s2)
    (Pot := fun t => 3 * vol ((List.range (N - t)).map pay) + (allKeys q).length * (N - t)) mU
    mPriv_U _ (sizeN q Ns D) M0 (ohN q Ns D) hbody X κ w
  rw [← hN] at e hc
  refine ⟨w', κ', c, e, ?_⟩
  simp only [Nat.sub_self, Nat.mul_zero, Nat.sub_zero, Nat.zero_mul, List.range_zero,
    List.map_nil] at hc
  have : vol ([] : List (List Bool)) = 0 := rfl
  omega

end Phases

/-! ## The two-phase program -/

section Prog

variable {q : ℕ} [NeZero q]

/-- **The two-phase mixed-shape kernel.** -/
def mixProg (sel1 sel2 : Key q → Key q) (D1 D2 : List NLab) : DProg (KM q) q :=
  .seq (pushSym mU delimSym)
    (.seq (dataLoop1 mSRC mU (nest (ordL q true) mNP mC mCT
        (leafP (fun _ => mSRC) (fun κ => mSTR (sel1 κ))) D1))
      (dataLoop2 mU (nest (ordL q false) mNP mC mCT
        (leafP (fun κ => mSTR (sel2 κ)) (fun _ => mDST)) D2)))

theorem mixProg_closed (sel1 sel2 : Key q → Key q) (D1 D2 : List NLab) :
    (mixProg sel1 sel2 D1 D2).Closed :=
  ⟨trivial, dataLoop1_closed _ _ (nest_closed _ _ _ _ (leafP_closed _ _) _),
    dataLoop2_closed _ (nest_closed _ _ _ _ (leafP_closed _ _) _)⟩

theorem ovl_self {K : Type} [DecidableEq K] (priv : K → Bool) (S : K → List Sym) :
    ovl priv S S = S := by
  funext loc
  simp [ovl]

theorem ovl_eq_left {K : Type} [DecidableEq K] (priv : K → Bool) (G X : K → List Sym)
    (h : ∀ loc, priv loc = true → G loc = X loc) : ovl priv G X = G := by
  funext loc
  by_cases hl : priv loc = true
  · simp [ovl, hl, h loc hl]
  · simp [ovl, hl]

theorem inj_of_mono {α : Type} (N : ℕ) (s1 s2 : ℕ → α) (f : ℕ → ℕ)
    (hs : ∀ y < N, s1 (f y) = s2 y)
    (hmono : ∀ y y', y < N → y' < N → s2 y = s2 y' → y < y' → f y < f y') :
    ∀ y y', y < N → y' < N → f y = f y' → y = y' := by
  intro y y' hy hy' h
  rcases Nat.lt_trichotomy y y' with hlt | heq | hgt
  · have e : s2 y = s2 y' := by rw [← hs y hy, ← hs y' hy', h]
    exact absurd h (Nat.ne_of_lt (hmono y y' hy hy' e hlt))
  · exact heq
  · have e : s2 y' = s2 y := by rw [← hs y hy, ← hs y' hy', h]
    exact absurd h.symm (Nat.ne_of_lt (hmono y' y hy' hy e hgt))

/-- **The two-phase kernel, exact.** Under the consistency conditions on the stream selectors
and the address map `f` (as in `filter_eq_map_filter`), `mixProg` consumes the source and pushes
`permByInv f v` onto the destination; all other stacks are restored. -/
theorem mixProg_runs (sel1 sel2 : Key q → Key q) (D1 D2 : List NLab) (Ns : Fin 2 → ℕ)
    (hsz : sizeN q Ns D2 = sizeN q Ns D1) (v : List (List Bool)) (M0 : ℕ)
    (hlen : v.length = M0 * sizeN q Ns D1) (hM0 : 0 < sizeN q Ns D1 ∨ M0 = 0)
    (s1 s2 : ℕ → Key q) (f : ℕ → ℕ)
    (hsel1 : ∀ (κ : Key q) (x : ℕ), x < v.length →
      sel1 (keyN q Ns D1 κ (x % sizeN q Ns D1)) = s1 x)
    (hsel2 : ∀ (κ : Key q) (y : ℕ), y < v.length →
      sel2 (keyN q Ns D2 κ (y % sizeN q Ns D2)) = s2 y)
    (hf : ∀ y < v.length, f y < v.length) (hs : ∀ y < v.length, s1 (f y) = s2 y)
    (hmono : ∀ y y', y < v.length → y' < v.length → s2 y = s2 y' → y < y' → f y < f y')
    (rest : List Sym) (hrest : BlkTerm rest) (rr : Fin 2 → List Sym) (hrr : ∀ r, TermOK (rr r))
    (S : KM q → List Sym) (hSRC : S mSRC = arrSyms v ++ rest)
    (hNP : ∀ r, S (mNP r) = natSyms (Ns r) ++ rr r) :
    Runs (mixProg sel1 sel2 D1 D2) S
      (Function.update (Function.update S mSRC rest) mDST (arrSyms (permByInv f v) ++ S mDST))
      (fun _ => True)
      (6 * vol v + 2 * (allKeys q).length * v.length + M0 * (ohN q Ns D1 + ohN q Ns D2 + 5) + 5) := by
  refine Runs.of_eval fun v0 => ?_
  obtain ⟨w, κ⟩ := v0
  -- push the delimiter
  have e0 := push_priv (q := q) (G := S) (X := S) mPriv_U delimSym [] (w, κ)
  rw [ovl_self] at e0
  -- distribute
  obtain ⟨w1, κ1, c1, e1, hc1⟩ := mixPhase1 sel1 D1 Ns v M0 hlen hM0 s1 hsel1 S rest hrest rr hrr
    hNP (Function.update S mU (delimSym :: S mU)) κ w
  rw [st1_zero (strIdx := mStrIdx) S v rest s1 hSRC, Function.update_self,
    Function.update_idem] at e1
  have hL := filter_eq_map_filter v.length s1 s2 f hf hs hmono
  rw [st1_last mPhaseOK S v rest s1 s2 f hL] at e1
  -- merge
  obtain ⟨w2, κ2, c2, e2, hc2⟩ := mixPhase2 sel2 D2 Ns v.length M0 (by rw [hsz]; exact hlen)
    (fun y => v.getD (f y) []) s2 hsel2 (Function.update S mSRC rest) rr hrr
    (fun r => by rw [Function.update_of_ne (mNP_ne_SRC r)]; exact hNP r) S κ1 w1
  have hpriv : ∀ loc, mPriv loc = true →
      Function.update (Function.update S mSRC rest) mDST
        (arrSyms ((List.range v.length).map fun y => v.getD (f y) []) ++
          Function.update S mSRC rest mDST) loc = S loc := by
    intro loc hloc
    have h1 : loc ≠ mDST := fun e => by rw [e, mPriv_DST] at hloc; cases hloc
    have h2 : loc ≠ mSRC := fun e => by rw [e, mPriv_SRC] at hloc; cases hloc
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
  rw [st2_last, ovl_eq_left mPriv _ S hpriv,
    Function.update_of_ne (mPhaseOK (q := q)).src_dst.symm] at e2
  refine ⟨_, _, Eval.seq e0 (Eval.seq e1 e2), trivial, ?_⟩
  have hvol := vol_map_perm v f hf (inj_of_mono v.length s1 s2 f hs hmono)
  rw [hvol] at hc2
  have hm : M0 * (ohN q Ns D1 + ohN q Ns D2 + 5) =
      M0 * (ohN q Ns D1 + 3) + M0 * (ohN q Ns D2 + 2) := by ring
  have hk : 2 * (allKeys q).length * v.length =
      (allKeys q).length * v.length + (allKeys q).length * v.length := by ring
  rw [hm, hk]
  omega

end Prog

end SubNLogN.Machine.K1Digit
