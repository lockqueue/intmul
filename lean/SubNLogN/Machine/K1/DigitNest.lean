/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.DigitPhase
import WP.W4.Rec

/-!
# K1 digit engine, part 4 (`K1/DigitNest.lean`): static nested walks over mixed shapes

Paper: Lemma A.4 (`lem:transfer-streams`, proof: digit streams; binary counters
with constant amortized increments; "wraparound and reset costs are charged to the preceding
traversal").

**Scope (honest summary).** Programs and exact evaluation lemmas only; no contract is proved here.

## Design
For a mixed shape such as `[N0] × [q] × [N1] × [q] × [N2]`, the address fields after the leading
block are described by a *static* list of labels `D : List NLab` (`A`, `B`: a radix-`q` key digit;
`R r`: a spectator block of runtime size `Ns r`, read from the counter stack `NP r`).
* `nest ord … D` is built by structural recursion on `D`: `A`/`B` become `q` unrolled iterations
  (`digitLoop`), storing the digit in the key register; `R r` becomes a counter loop (`cntLoop`):
  copy `Ns r` from `NP r` onto the private stack `C r` (above a `mark`), run the body while the
  counter is nonzero, decrementing it after each iteration.
* The leading block, whose size is implicit, is a data-driven loop: `dataLoop1` runs while the
  source starts with a record and pushes one tick per iteration on the private stack `U`;
  `dataLoop2` pops the ticks.
* **Frames.** The counter stacks and `U` are private (`priv`); states are `ovl priv (G t) X`: data
  stacks from `G t`, private stacks from `X`. Every spec holds for all `X`, and leaves never touch
  private stacks.
* **Keys** as in `K1/DigitWalk.lean` (`keyN`, mixed radix; `AgreeN`).
* **Cost.** Counter loops pay `7·bitLen N + 11` once and `≤ 16 + body` per iteration; the
  decrements are amortized through the potential `6·popcount` (`zerosLead_succ_add_popcount`).
-/

namespace SubNLogN.Machine.K1Digit

open TMFw TMFw.Contracts TMFw.Lib Computability

/-! ## Static labels and keys -/

/-- Static labels of a nested walk: key digits `A`, `B`, spectator blocks `R 0`, `R 1`. -/
inductive NLab : Type
  | A
  | B
  | R (r : Fin 2)
  deriving DecidableEq

section Keys

variable {q : ℕ}

/-- Range of a label. -/
def NLab.size (q : ℕ) (Ns : Fin 2 → ℕ) : NLab → ℕ
  | .A => q
  | .B => q
  | .R r => Ns r

/-- Number of addresses described by a label list. -/
def sizeN (q : ℕ) (Ns : Fin 2 → ℕ) : List NLab → ℕ
  | [] => 1
  | l :: D => l.size q Ns * sizeN q Ns D

/-- Key update of a label. -/
def updN (q : ℕ) [NeZero q] : NLab → ℕ → Key q → Key q
  | .A, n, κ => (Fin.ofNat q n, κ.2)
  | .B, n, κ => (κ.1, Fin.ofNat q n)
  | .R _, _, κ => κ

/-- The key at the leaf for the address `x` (mixed radix). -/
def keyN (q : ℕ) [NeZero q] (Ns : Fin 2 → ℕ) : List NLab → Key q → ℕ → Key q
  | [], κ, _ => κ
  | l :: D, κ, x => keyN q Ns D (updN q l (x / sizeN q Ns D) κ) (x % sizeN q Ns D)

/-- Two keys agree on every component that `D` does not set. -/
def AgreeN (D : List NLab) (κ κ' : Key q) : Prop :=
  (NLab.A ∉ D → κ.1 = κ'.1) ∧ (NLab.B ∉ D → κ.2 = κ'.2)

theorem AgreeN.refl (D : List NLab) (κ : Key q) : AgreeN D κ κ := ⟨fun _ => rfl, fun _ => rfl⟩

theorem AgreeN.trans {D : List NLab} {a b c : Key q} (h1 : AgreeN D a b) (h2 : AgreeN D b c) :
    AgreeN D a c :=
  ⟨fun h => (h1.1 h).trans (h2.1 h), fun h => (h1.2 h).trans (h2.2 h)⟩

theorem AgreeN.cons {D : List NLab} {a b : Key q} (l : NLab) (h : AgreeN D a b) :
    AgreeN (l :: D) a b :=
  ⟨fun hA => h.1 (fun hm => hA (List.mem_cons_of_mem _ hm)),
    fun hB => h.2 (fun hm => hB (List.mem_cons_of_mem _ hm))⟩

theorem AgreeN.ofR {D : List NLab} {a b : Key q} {r : Fin 2} (h : AgreeN (.R r :: D) a b) :
    AgreeN D a b :=
  ⟨fun hA => h.1 (by simp [hA]), fun hB => h.2 (by simp [hB])⟩

theorem AgreeN.toR {D : List NLab} {a b : Key q} (r : Fin 2) (h : AgreeN D a b) :
    AgreeN (.R r :: D) a b :=
  h.cons _

theorem keyN_congr [NeZero q] (Ns : Fin 2 → ℕ) :
    ∀ (D : List NLab) {κ κ' : Key q} (x : ℕ), AgreeN D κ κ' → keyN q Ns D κ x = keyN q Ns D κ' x
  | [], κ, κ', x, h => by
    simp only [keyN]
    exact Prod.ext (h.1 (by simp)) (h.2 (by simp))
  | .A :: D, _, _, _, h => by
    simp only [keyN, updN]
    exact keyN_congr Ns D _ ⟨fun _ => rfl, fun hB => h.2 (by simp [hB])⟩
  | .B :: D, _, _, _, h => by
    simp only [keyN, updN]
    exact keyN_congr Ns D _ ⟨fun hA => h.1 (by simp [hA]), fun _ => rfl⟩
  | .R _ :: D, _, _, _, h => by
    simp only [keyN, updN]
    exact keyN_congr Ns D _ h.ofR

end Keys

/-! ## Programs -/

/-- Tick symbol on the block-count stack `U`. -/
def tickSym : Sym := .tag 4

/-- Delimiter below the ticks. -/
def delimSym : Sym := .tag 5

section Programs

variable {K : Type} {q : ℕ}

/-- **Counter loop**: run `body` `N` times, `N` read from `NP` (restored), counted down on the
private stack `C` above a `mark`; `CT` is a temporary of the `Lib` routines. -/
def cntLoop (NP C CT : K) (body : DProg K q) : DProg K q :=
  .seq (pushSym C .mark) (.seq (liftS (copyBlock NP C CT)) (.seq (liftS (peekR C))
    (.seq (.loop bitR (.seq body (.seq (liftS (dec C CT)) (liftS (peekR C))))) (liftS (popR C)))))

/-- **Digit loop**: for each digit `c` of `ord`, store it in the key component of `lab`, run `body`. -/
def digitLoop (ord : List (Fin q)) (lab : Lab) (body : DProg K q) : DProg K q :=
  forEachProg ord (fun c => .seq (.load fun v => (v.1, updKey lab c v.2)) body)

/-- **The nested walk** of a static label list. -/
def nest (ord : List (Fin q)) (NP C : Fin 2 → K) (CT : K) (leaf : DProg K q) :
    List NLab → DProg K q
  | [] => leaf
  | .A :: D => digitLoop ord .A (nest ord NP C CT leaf D)
  | .B :: D => digitLoop ord .B (nest ord NP C CT leaf D)
  | .R r :: D => cntLoop (NP r) (C r) CT (nest ord NP C CT leaf D)

/-- The source starts with a record symbol. -/
def recR (v : Reg q) : Bool := TMFw.W4.isRecR v.1.1

/-- **Leading block, distribute side**: while `SRC` starts with a record, push a tick on `U`, run
`body`. -/
def dataLoop1 (SRC U : K) (body : DProg K q) : DProg K q :=
  .seq (liftS (peekR SRC)) (.loop recR (.seq (pushSym U tickSym) (.seq body (liftS (peekR SRC)))))

/-- **Leading block, merge side**: pop `U`; while it was a tick, run `body` and pop again. -/
def dataLoop2 (U : K) (body : DProg K q) : DProg K q :=
  .seq (popSym U) (.loop (isSymR tickSym) (.seq body (popSym U)))

theorem cntLoop_closed (NP C CT : K) {body : DProg K q} (h : body.Closed) :
    (cntLoop NP C CT body).Closed := by
  refine ⟨trivial, liftS_closed ?_, liftS_closed trivial, ⟨h, liftS_closed ?_,
    liftS_closed trivial⟩, liftS_closed trivial⟩
  · simp [copyBlock, moveBlock, moveBits, moveBitsDup, moveBitsBody, dupBody, restoreR, popR,
      pushR, pushC, skip, Prog.Closed, Prog.FreeBelow]
  · simp [dec, decFix, scanLoop, scanBody, moveBits, moveBitsBody, popR, pushR, pushC, peekR,
      skip, Prog.Closed, Prog.FreeBelow]

theorem nest_closed (ord : List (Fin q)) (NP C : Fin 2 → K) (CT : K) {leaf : DProg K q}
    (h : leaf.Closed) : ∀ D, (nest ord NP C CT leaf D).Closed
  | [] => h
  | .A :: D => closed_forEachProg _ _ (fun _ _ => ⟨trivial, nest_closed ord NP C CT h D⟩)
  | .B :: D => closed_forEachProg _ _ (fun _ _ => ⟨trivial, nest_closed ord NP C CT h D⟩)
  | .R _ :: D => cntLoop_closed _ _ _ (nest_closed ord NP C CT h D)

theorem dataLoop1_closed (SRC U : K) {body : DProg K q} (h : body.Closed) :
    (dataLoop1 SRC U body).Closed :=
  ⟨liftS_closed trivial, trivial, h, liftS_closed trivial⟩

theorem dataLoop2_closed (U : K) {body : DProg K q} (h : body.Closed) :
    (dataLoop2 U body).Closed :=
  ⟨trivial, h, trivial⟩

end Programs

/-! ## Overlays and costs -/

section Ovl

variable {K : Type} [DecidableEq K]

/-- Data stacks from `G`, private stacks from `X`. -/
def ovl (priv : K → Bool) (G X : K → List Sym) : K → List Sym :=
  fun loc => if priv loc then X loc else G loc

theorem ovl_pub {priv : K → Bool} {G X : K → List Sym} {a : K} (ha : priv a = false) :
    ovl priv G X a = G a := by simp [ovl, ha]

theorem ovl_priv {priv : K → Bool} {G X : K → List Sym} {a : K} (ha : priv a = true) :
    ovl priv G X a = X a := by simp [ovl, ha]

theorem ovl_update_pub {priv : K → Bool} {G X : K → List Sym} {a : K} (ha : priv a = false)
    (w : List Sym) : Function.update (ovl priv G X) a w = ovl priv (Function.update G a w) X := by
  funext loc
  by_cases h : loc = a
  · subst h; simp [ovl, ha]
  · simp [ovl, h]

theorem ovl_update_priv {priv : K → Bool} {G X : K → List Sym} {a : K} (ha : priv a = true)
    (w : List Sym) : Function.update (ovl priv G X) a w = ovl priv G (Function.update X a w) := by
  funext loc
  by_cases h : loc = a
  · subst h; simp [ovl, ha]
  · simp [ovl, h]

end Ovl

/-- Overhead of a nested walk (besides the leaves). -/
def ohN (q : ℕ) (Ns : Fin 2 → ℕ) : List NLab → ℕ
  | [] => 0
  | .A :: D => q * (ohN q Ns D + 1) + 1
  | .B :: D => q * (ohN q Ns D + 1) + 1
  | .R r :: D => Ns r * (ohN q Ns D + 16) + 7 * bitLen (Ns r) + 11

theorem zerosLead_incBits : ∀ L : List Bool, zerosLead (incBits L) = ones L
  | [] => rfl
  | true :: L => by simp [incBits, zerosLead, ones, zerosLead_incBits L]
  | false :: L => by simp [incBits, zerosLead, ones]

/-- **Amortized decrement**: a decrement `n + 1 ↦ n` is paid by the drop of `popcount`. -/
theorem zerosLead_succ_add_popcount (n : ℕ) :
    zerosLead (encodeNat (n + 1)) + popcount (encodeNat (n + 1)) = popcount (encodeNat n) + 1 := by
  rw [encodeNat_succ, zerosLead_incBits]
  exact ones_add_popcount_incBits _

/-! ## Exact evaluation of nested walks -/

section NestSpec

variable {K : Type} [DecidableEq K] {q : ℕ} [NeZero q]

/-- Stack facts of nested walks. -/
structure NestOK (priv : K → Bool) (NP C : Fin 2 → K) (CT : K) : Prop where
  c_priv : ∀ r, priv (C r) = true
  np_pub : ∀ r, priv (NP r) = false
  ct_pub : priv CT = false
  ct_np : ∀ r, CT ≠ NP r

theorem NestOK.c_ne_ct {priv : K → Bool} {NP C : Fin 2 → K} {CT : K} (h : NestOK priv NP C CT)
    (r : Fin 2) : C r ≠ CT := fun e => by
  have := h.c_priv r
  rw [e, h.ct_pub] at this
  cases this

theorem NestOK.np_ne_c {priv : K → Bool} {NP C : Fin 2 → K} {CT : K} (h : NestOK priv NP C CT)
    (r r' : Fin 2) : NP r ≠ C r' := fun e => by
  have := h.c_priv r'
  rw [← e, h.np_pub] at this
  cases this

variable (priv : K → Bool) (dir : Bool) (NP C : Fin 2 → K) (CT : K) (leaf : DProg K q)
  (Ns : Fin 2 → ℕ) (G : ℕ → K → List Sym) (Pot : ℕ → ℕ)

/-- Exact leaf evaluations, for every content `X` of the private stacks. -/
def LeafHypsN (keyOf : ℕ → Key q) (T n : ℕ) : Prop :=
  ∀ u < n, ∀ (X : K → List Sym) (w0 : CReg), ∃ w1 c,
    Eval [] leaf ⟨(w0, keyOf u), ovl priv (G (T + u)) X⟩
      ⟨(w1, keyOf u), ovl priv (G (T + u + 1)) X⟩ c ∧ c + Pot (T + u + 1) ≤ Pot (T + u)

/-- The statement of `nest_spec` for the label list `D`. -/
def NestSpec (D : List NLab) : Prop :=
  ∀ (t0 : ℕ) (κ : Key q) (w : CReg) (X : K → List Sym),
    LeafHypsN priv leaf G Pot (fun u => keyN q Ns D κ (posL dir (sizeN q Ns D) u)) t0
      (sizeN q Ns D) →
    ∃ w' κ' c, Eval [] (nest (ordL q dir) NP C CT leaf D) ⟨(w, κ), ovl priv (G t0) X⟩
        ⟨(w', κ'), ovl priv (G (t0 + sizeN q Ns D)) X⟩ c ∧
      AgreeN D κ' κ ∧ c + Pot (t0 + sizeN q Ns D) ≤ Pot t0 + ohN q Ns D

theorem digitSeq_spec (lab : Lab) (nl : NLab) (D : List NLab)
    (IH : NestSpec priv dir NP C CT leaf Ns G Pot D)
    (h_self : ∀ (c : Fin q) (κ : Key q), AgreeN (nl :: D) (updKey lab c κ) κ)
    (h_upd : ∀ (c : Fin q) (a b : Key q), AgreeN (nl :: D) a b →
      AgreeN D (updKey lab c a) (updKey lab c b))
    (t0 : ℕ) (κ : Key q) :
    ∀ (cs : List (Fin q)) (m0 : ℕ) (κc : Key q) (w : CReg) (X : K → List Sym),
      (∀ (m : ℕ) (c : Fin q), cs[m]? = some c →
        LeafHypsN priv leaf G Pot
          (fun u => keyN q Ns D (updKey lab c κ) (posL dir (sizeN q Ns D) u))
          (t0 + (m0 + m) * sizeN q Ns D) (sizeN q Ns D)) →
      AgreeN (nl :: D) κc κ →
      ∃ w' κ' c, Eval [] (forEachProg cs (fun c => .seq (.load fun v => (v.1, updKey lab c v.2))
            (nest (ordL q dir) NP C CT leaf D)))
          ⟨(w, κc), ovl priv (G (t0 + m0 * sizeN q Ns D)) X⟩
          ⟨(w', κ'), ovl priv (G (t0 + (m0 + cs.length) * sizeN q Ns D)) X⟩ c ∧
        AgreeN (nl :: D) κ' κ ∧
        c + Pot (t0 + (m0 + cs.length) * sizeN q Ns D) ≤
          Pot (t0 + m0 * sizeN q Ns D) + cs.length * (ohN q Ns D + 1) + 1
  | [], m0, κc, w, X, _, hag => by
    refine ⟨w, κc, 1, ?_, hag, ?_⟩
    · simp only [forEachProg_nil, List.length_nil, Nat.add_zero]
      exact skip_eval _ _
    · simp only [List.length_nil, Nat.add_zero, Nat.zero_mul]
      omega
  | c :: cs, m0, κc, w, X, hyps, hag => by
    have hy0 := hyps 0 c rfl
    have hconv : LeafHypsN priv leaf G Pot
        (fun u => keyN q Ns D (updKey lab c κc) (posL dir (sizeN q Ns D) u))
        (t0 + m0 * sizeN q Ns D) (sizeN q Ns D) := by
      intro u hu X' w0
      have := hy0 u hu X' w0
      simp only [Nat.add_zero] at this ⊢
      rw [keyN_congr Ns D _ (h_upd c _ _ hag)]
      exact this
    obtain ⟨w1, κ1, c1, e1, hag1, hc1⟩ :=
      IH (t0 + m0 * sizeN q Ns D) (updKey lab c κc) w X hconv
    have hag1' : AgreeN (nl :: D) κ1 κ := ((hag1.cons nl).trans (h_self c κc)).trans hag
    obtain ⟨w2, κ2, c2, e2, hag2, hc2⟩ := digitSeq_spec lab nl D IH h_self h_upd t0 κ cs (m0 + 1)
      κ1 w1 X (fun m c' h => by
        have := hyps (m + 1) c' (by simpa using h)
        rwa [show m0 + (m + 1) = m0 + 1 + m by omega] at this) hag1'
    have el : Eval [] (.load fun v : Reg q => (v.1, updKey lab c v.2))
        ⟨(w, κc), ovl priv (G (t0 + m0 * sizeN q Ns D)) X⟩
        ⟨(w, updKey lab c κc), ovl priv (G (t0 + m0 * sizeN q Ns D)) X⟩ 1 :=
      Eval.load _ _ _ _
    have hidx : t0 + (m0 + 1) * sizeN q Ns D = t0 + m0 * sizeN q Ns D + sizeN q Ns D := by ring
    rw [hidx] at e2 hc2
    refine ⟨w2, κ2, 1 + c1 + c2, ?_, hag2, ?_⟩
    · have e := Eval.seq (Eval.seq el e1) e2
      rw [show m0 + (c :: cs).length = m0 + 1 + cs.length by simp; omega]
      exact e
    · rw [show m0 + (c :: cs).length = m0 + 1 + cs.length by simp; omega]
      have hl : (c :: cs).length * (ohN q Ns D + 1) =
          cs.length * (ohN q Ns D + 1) + (ohN q Ns D + 1) := by
        simp only [List.length_cons]; ring
      rw [hl]
      omega

theorem digitLoop_spec (lab : Lab) (nl : NLab) (D : List NLab)
    (IH : NestSpec priv dir NP C CT leaf Ns G Pot D) (hsize : nl.size q Ns = q)
    (h_updN : ∀ (n : ℕ) (κ : Key q), updN q nl n κ = updKey lab (Fin.ofNat q n) κ)
    (h_self : ∀ (c : Fin q) (κ : Key q), AgreeN (nl :: D) (updKey lab c κ) κ)
    (h_upd : ∀ (c : Fin q) (a b : Key q), AgreeN (nl :: D) a b →
      AgreeN D (updKey lab c a) (updKey lab c b))
    (t0 : ℕ) (κ : Key q) (w : CReg) (X : K → List Sym)
    (hyps : LeafHypsN priv leaf G Pot
      (fun u => keyN q Ns (nl :: D) κ (posL dir (sizeN q Ns (nl :: D)) u)) t0
      (sizeN q Ns (nl :: D))) :
    ∃ w' κ' c, Eval [] (digitLoop (ordL q dir) lab (nest (ordL q dir) NP C CT leaf D))
        ⟨(w, κ), ovl priv (G t0) X⟩ ⟨(w', κ'), ovl priv (G (t0 + sizeN q Ns (nl :: D))) X⟩ c ∧
      AgreeN (nl :: D) κ' κ ∧
      c + Pot (t0 + sizeN q Ns (nl :: D)) ≤ Pot t0 + (q * (ohN q Ns D + 1) + 1) := by
  have hlen : sizeN q Ns (nl :: D) = sizeN q Ns D * q := by
    simp only [sizeN, hsize, Nat.mul_comm]
  have hyps' : ∀ (m : ℕ) (c : Fin q), (ordL q dir)[m]? = some c →
      LeafHypsN priv leaf G Pot
        (fun u => keyN q Ns D (updKey lab c κ) (posL dir (sizeN q Ns D) u))
        (t0 + (0 + m) * sizeN q Ns D) (sizeN q Ns D) := by
    intro m c hmc u hu X' w0
    have hm : m < q := by
      have h1 := (List.getElem?_eq_some_iff.1 hmc).1
      simpa [ordL_length] using h1
    rw [ordL_getElem? dir hm, Option.some.injEq] at hmc
    subst hmc
    have hlt : m * sizeN q Ns D + u < sizeN q Ns (nl :: D) := by
      rw [hlen]
      calc m * sizeN q Ns D + u < m * sizeN q Ns D + sizeN q Ns D := by omega
        _ = (m + 1) * sizeN q Ns D := by ring
        _ ≤ q * sizeN q Ns D := Nat.mul_le_mul_right _ hm
        _ = sizeN q Ns D * q := by ring
    obtain ⟨w1, c', e, hc⟩ := hyps (m * sizeN q Ns D + u) hlt X' w0
    have hpos := posL_lt (dir := dir) hu
    have hMpos : 0 < sizeN q Ns D := Nat.lt_of_le_of_lt (Nat.zero_le _) hu
    have hkey : keyN q Ns (nl :: D) κ (posL dir (sizeN q Ns (nl :: D)) (m * sizeN q Ns D + u)) =
        keyN q Ns D (updKey lab (Fin.ofNat q (posL dir q m)) κ) (posL dir (sizeN q Ns D) u) := by
      rw [hlen, posL_split dir hm hu]
      simp only [keyN]
      rw [h_updN]
      congr 2
      · congr 1
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hMpos, Nat.div_eq_of_lt hpos, Nat.zero_add]
      · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpos]
    dsimp only at e hc ⊢
    rw [hkey] at e
    rw [show t0 + (0 + m) * sizeN q Ns D + u = t0 + (m * sizeN q Ns D + u) by ring]
    exact ⟨w1, c', e, hc⟩
  obtain ⟨w', κ', c, e, hag, hc⟩ := digitSeq_spec priv dir NP C CT leaf Ns G Pot lab nl D IH
    h_self h_upd t0 κ (ordL q dir) 0 κ w X hyps' (AgreeN.refl _ _)
  have hT : t0 + (0 + (ordL q dir).length) * sizeN q Ns D = t0 + sizeN q Ns (nl :: D) := by
    rw [ordL_length, hlen]; ring
  have hT0 : t0 + 0 * sizeN q Ns D = t0 := by ring
  rw [hT0, hT] at e
  rw [hT0, hT, ordL_length] at hc
  exact ⟨w', κ', c, e, hag, by omega⟩

theorem cntIter_spec {priv : K → Bool} {dir : Bool} {NP C : Fin 2 → K} {CT : K} {leaf : DProg K q}
    {Ns : Fin 2 → ℕ} {G : ℕ → K → List Sym} {Pot : ℕ → ℕ} (hN : NestOK priv NP C CT)
    (r : Fin 2) (D : List NLab) (IH : NestSpec priv dir NP C CT leaf Ns G Pot D)
    (t0 : ℕ) (κ : Key q) (X : K → List Sym)
    (hyps : ∀ m < Ns r, LeafHypsN priv leaf G Pot
      (fun u => keyN q Ns D κ (posL dir (sizeN q Ns D) u)) (t0 + m * sizeN q Ns D)
      (sizeN q Ns D)) :
    ∀ n, n ≤ Ns r → ∀ (κc : Key q) (w : CReg), AgreeN D κc κ →
      w.1 = (natSyms n ++ Sym.mark :: X (C r)).head? →
      ∃ w' κ' c, Eval [] (.loop bitR (.seq (nest (ordL q dir) NP C CT leaf D)
            (.seq (liftS (dec (C r) CT)) (liftS (peekR (C r))))))
          ⟨(w, κc), ovl priv (G (t0 + (Ns r - n) * sizeN q Ns D))
            (Function.update X (C r) (natSyms n ++ Sym.mark :: X (C r)))⟩
          ⟨(w', κ'), ovl priv (G (t0 + Ns r * sizeN q Ns D))
            (Function.update X (C r) (Sym.mark :: X (C r)))⟩ c ∧
        AgreeN D κ' κ ∧
        c + Pot (t0 + Ns r * sizeN q Ns D) + 6 * popcount (encodeNat n) ≤
          Pot (t0 + (Ns r - n) * sizeN q Ns D) + n * (ohN q Ns D + 16) + 1
  | 0, _, κc, w, hag, hw => by
    have hs : natSyms 0 ++ Sym.mark :: X (C r) = Sym.mark :: X (C r) := by
      simp [natSyms, encodeNat_zero]
    refine ⟨w, κc, 1, ?_, hag, ?_⟩
    · rw [hs, Nat.sub_zero]
      refine Eval.loop_false ?_
      show optIsBit w.1 = false
      rw [hw, hs]
      rfl
    · simp only [Nat.sub_zero, encodeNat_zero, popcount, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      omega
  | n + 1, hn, κc, w, hag, hw => by
    have hmlt : Ns r - (n + 1) < Ns r := by omega
    have hconv : LeafHypsN priv leaf G Pot (fun u => keyN q Ns D κc (posL dir (sizeN q Ns D) u))
        (t0 + (Ns r - (n + 1)) * sizeN q Ns D) (sizeN q Ns D) := by
      intro u hu X' w0
      have := hyps _ hmlt u hu X' w0
      simp only at this ⊢
      rw [keyN_congr Ns D _ hag]
      exact this
    obtain ⟨w1, κ1, c1, e1, hag1, hc1⟩ := IH (t0 + (Ns r - (n + 1)) * sizeN q Ns D) κc w
      (Function.update X (C r) (natSyms (n + 1) ++ Sym.mark :: X (C r))) hconv
    have hidx : t0 + (Ns r - (n + 1)) * sizeN q Ns D + sizeN q Ns D =
        t0 + (Ns r - n) * sizeN q Ns D := by
      have : Ns r - n = Ns r - (n + 1) + 1 := by omega
      rw [this]; ring
    rw [hidx] at e1 hc1
    have hC : ovl priv (G (t0 + (Ns r - n) * sizeN q Ns D))
        (Function.update X (C r) (natSyms (n + 1) ++ Sym.mark :: X (C r))) (C r) =
        (encodeNat (n + 1)).map Sym.bit ++ (Sym.mark :: X (C r)) := by
      rw [ovl_priv (hN.c_priv r)]
      simp [natSyms]
    have e2 := liftS_eval (q := q) (w1, κ1)
      (dec_eval (hN.c_ne_ct r) [] w1.1 n (Sym.mark :: X (C r)) _ (TermOK.cons rfl _) hC)
    rw [ovl_update_priv (hN.c_priv r), Function.update_idem] at e2
    have e3 := liftS_eval (q := q) ((some Sym.mark, w1.2), κ1)
      (Eval.peek [] (C r) (fun _ o => o) (some Sym.mark)
        (ovl priv (G (t0 + (Ns r - n) * sizeN q Ns D))
          (Function.update X (C r) ((encodeNat n).map Sym.bit ++ Sym.mark :: X (C r)))))
    have hpk : (ovl priv (G (t0 + (Ns r - n) * sizeN q Ns D))
        (Function.update X (C r) ((encodeNat n).map Sym.bit ++ Sym.mark :: X (C r))) (C r)).head? =
        (natSyms n ++ Sym.mark :: X (C r)).head? := by
      rw [ovl_priv (hN.c_priv r)]
      simp [natSyms]
    obtain ⟨w4, κ4, c4, e4, hag4, hc4⟩ := cntIter_spec hN r D IH t0 κ X hyps n (by omega) κ1
      (((ovl priv (G (t0 + (Ns r - n) * sizeN q Ns D))
        (Function.update X (C r) ((encodeNat n).map Sym.bit ++ Sym.mark :: X (C r))) (C r)).head?,
        w1.2)) (hag1.trans hag) hpk
    have hbit : bitR (w, κc) = true := by
      show optIsBit w.1 = true
      rw [hw]
      obtain ⟨b0, l, hbl⟩ : ∃ b0 l, encodeNat (n + 1) = b0 :: l := by
        cases h : encodeNat (n + 1) with
        | nil => exact absurd ((encodeNat_eq_nil_iff _).1 h) (by omega)
        | cons b0 l => exact ⟨b0, l, rfl⟩
      simp [natSyms, hbl]
    have e4' : Eval [] (.loop bitR (.seq (nest (ordL q dir) NP C CT leaf D)
            (.seq (liftS (dec (C r) CT)) (liftS (peekR (C r))))))
          ⟨_, ovl priv (G (t0 + (Ns r - n) * sizeN q Ns D))
            (Function.update X (C r) ((encodeNat n).map Sym.bit ++ Sym.mark :: X (C r)))⟩ _ c4 := e4
    refine ⟨w4, κ4, _, Eval.loop_true hbit (Eval.seq e1 (Eval.seq e2 e3)) e4', hag4, ?_⟩
    have hz := zerosLead_succ_add_popcount n
    have hsub : Ns r - (n + 1) + 1 = Ns r - n := by omega
    have hmul : (n + 1) * (ohN q Ns D + 16) = n * (ohN q Ns D + 16) + (ohN q Ns D + 16) := by ring
    rw [hmul]
    omega

end NestSpec

section NestSpec2

variable {K : Type} [DecidableEq K] {q : ℕ} [NeZero q]

theorem push_priv {priv : K → Bool} {G X : K → List Sym} {a : K} (ha : priv a = true) (x : Sym)
    (ρ' : List (DProg K q)) (v : Reg q) :
    Eval ρ' (pushSym a x) ⟨v, ovl priv G X⟩ ⟨v, ovl priv G (Function.update X a (x :: X a))⟩ 1 := by
  refine (Eval.push ρ' a _ v _).of_eq ?_ rfl
  rw [ovl_priv ha, ovl_update_priv ha]

theorem pop_priv {priv : K → Bool} {G X : K → List Sym} {a : K} (ha : priv a = true)
    (ρ' : List (DProg K q)) (v : Reg q) :
    Eval ρ' (popSym a) ⟨v, ovl priv G X⟩
      ⟨(((X a).head?, v.1.2), v.2), ovl priv G (Function.update X a (X a).tail)⟩ 1 := by
  refine (Eval.pop ρ' a _ v _).of_eq ?_ rfl
  rw [ovl_priv ha, ovl_update_priv ha]

theorem cntLoop_spec {priv : K → Bool} {dir : Bool} {NP C : Fin 2 → K} {CT : K}
    {leaf : DProg K q} {Ns : Fin 2 → ℕ} {G : ℕ → K → List Sym} {Pot : ℕ → ℕ}
    (hN : NestOK priv NP C CT) (r : Fin 2) (D : List NLab)
    (IH : NestSpec priv dir NP C CT leaf Ns G Pot D)
    (rr : List Sym) (hrr : TermOK rr) (hNP : ∀ t, G t (NP r) = natSyms (Ns r) ++ rr)
    (t0 : ℕ) (κ : Key q) (w : CReg) (X : K → List Sym)
    (hyps : LeafHypsN priv leaf G Pot
      (fun u => keyN q Ns (.R r :: D) κ (posL dir (sizeN q Ns (.R r :: D)) u)) t0
      (sizeN q Ns (.R r :: D))) :
    ∃ w' κ' c, Eval [] (cntLoop (NP r) (C r) CT (nest (ordL q dir) NP C CT leaf D))
        ⟨(w, κ), ovl priv (G t0) X⟩ ⟨(w', κ'), ovl priv (G (t0 + sizeN q Ns (.R r :: D))) X⟩ c ∧
      AgreeN (.R r :: D) κ' κ ∧
      c + Pot (t0 + sizeN q Ns (.R r :: D)) ≤ Pot t0 + ohN q Ns (.R r :: D) := by
  have hsz : sizeN q Ns (.R r :: D) = Ns r * sizeN q Ns D := rfl
  have hyps' : ∀ m < Ns r, LeafHypsN priv leaf G Pot
      (fun u => keyN q Ns D κ (posL dir (sizeN q Ns D) u)) (t0 + m * sizeN q Ns D)
      (sizeN q Ns D) := by
    intro m hm u hu X' w0
    have hlt : m * sizeN q Ns D + u < sizeN q Ns (.R r :: D) := by
      rw [hsz]
      calc m * sizeN q Ns D + u < m * sizeN q Ns D + sizeN q Ns D := by omega
        _ = (m + 1) * sizeN q Ns D := by ring
        _ ≤ Ns r * sizeN q Ns D := Nat.mul_le_mul_right _ hm
    obtain ⟨w1, c', e, hc⟩ := hyps (m * sizeN q Ns D + u) hlt X' w0
    have hpos := posL_lt (dir := dir) hu
    have hkey : keyN q Ns (.R r :: D) κ (posL dir (sizeN q Ns (.R r :: D)) (m * sizeN q Ns D + u)) =
        keyN q Ns D κ (posL dir (sizeN q Ns D) u) := by
      rw [hsz, Nat.mul_comm (Ns r), posL_split dir hm hu]
      simp only [keyN, updN]
      congr 1
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpos]
    dsimp only at e hc ⊢
    rw [hkey] at e
    rw [show t0 + m * sizeN q Ns D + u = t0 + (m * sizeN q Ns D + u) by ring]
    exact ⟨w1, c', e, hc⟩
  have e1 := push_priv (q := q) (G := G t0) (X := X) (hN.c_priv r) Sym.mark [] (w, κ)
  have hNPv : ovl priv (G t0) (Function.update X (C r) (Sym.mark :: X (C r))) (NP r) =
      (encodeNat (Ns r)).map Sym.bit ++ rr := by
    rw [ovl_pub (hN.np_pub r), hNP]
    rfl
  have e2 := liftS_eval (q := q) (w, κ) (copyBlock_eval (hN.np_ne_c r r) (hN.ct_np r).symm
    (hN.c_ne_ct r) [] w.1 (encodeNat (Ns r)) rr _ hrr hNPv)
  rw [ovl_update_priv (hN.c_priv r), ovl_priv (hN.c_priv r), Function.update_idem,
    Function.update_self] at e2
  have e3 := liftS_eval (q := q) ((some Sym.mark, w.2), κ)
    (Eval.peek [] (C r) (fun _ o => o) (some Sym.mark)
      (ovl priv (G t0) (Function.update X (C r)
        ((encodeNat (Ns r)).map Sym.bit ++ Sym.mark :: X (C r)))))
  have hpk : (ovl priv (G t0) (Function.update X (C r)
      ((encodeNat (Ns r)).map Sym.bit ++ Sym.mark :: X (C r))) (C r)).head? =
      (natSyms (Ns r) ++ Sym.mark :: X (C r)).head? := by
    rw [ovl_priv (hN.c_priv r)]
    simp [natSyms]
  obtain ⟨w4, κ4, c4, e4, hag4, hc4⟩ := cntIter_spec hN r D IH t0 κ X hyps' (Ns r) le_rfl κ
    ((ovl priv (G t0) (Function.update X (C r)
      ((encodeNat (Ns r)).map Sym.bit ++ Sym.mark :: X (C r))) (C r)).head?, w.2)
    (AgreeN.refl _ _) hpk
  simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at e4 hc4
  have hX : Function.update X (C r) (natSyms (Ns r) ++ Sym.mark :: X (C r)) =
      Function.update X (C r) ((encodeNat (Ns r)).map Sym.bit ++ Sym.mark :: X (C r)) := rfl
  rw [hX] at e4
  have e5 := pop_priv (q := q) (G := G (t0 + Ns r * sizeN q Ns D))
    (X := Function.update X (C r) (Sym.mark :: X (C r))) (hN.c_priv r) [] (w4, κ4)
  rw [Function.update_self, Function.update_idem, List.tail_cons, Function.update_eq_self] at e5
  refine ⟨_, κ4, _, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5))), hag4.toR r, ?_⟩
  rw [hsz]
  simp only [ohN]
  have hbl : (encodeNat (Ns r)).length = bitLen (Ns r) := rfl
  rw [hbl]
  omega

/-- **Nested walks, exact.** -/
theorem nest_spec {priv : K → Bool} {dir : Bool} {NP C : Fin 2 → K} {CT : K}
    {leaf : DProg K q} {Ns : Fin 2 → ℕ} {G : ℕ → K → List Sym} {Pot : ℕ → ℕ}
    (hN : NestOK priv NP C CT) (rr : Fin 2 → List Sym) (hrr : ∀ r, TermOK (rr r))
    (hNP : ∀ r t, G t (NP r) = natSyms (Ns r) ++ rr r) :
    ∀ D, NestSpec priv dir NP C CT leaf Ns G Pot D
  | [] => by
    intro t0 κ w X hyps
    obtain ⟨w1, c, e, hc⟩ := hyps 0 (by simp [sizeN]) X w
    simp only [keyN, Nat.add_zero] at e hc
    refine ⟨w1, κ, c, ?_, AgreeN.refl _ _, ?_⟩
    · simpa [sizeN, nest] using e
    · simp only [sizeN, ohN]
      omega
  | .A :: D => by
    intro t0 κ w X hyps
    exact digitLoop_spec priv dir NP C CT leaf Ns G Pot .A .A D (nest_spec hN rr hrr hNP D) rfl
      (fun _ _ => rfl) (fun _ _ => ⟨fun h => absurd List.mem_cons_self h, fun _ => rfl⟩)
      (fun _ _ _ h => ⟨fun _ => rfl, fun hB => h.2 (by simp [hB])⟩) t0 κ w X hyps
  | .B :: D => by
    intro t0 κ w X hyps
    exact digitLoop_spec priv dir NP C CT leaf Ns G Pot .B .B D (nest_spec hN rr hrr hNP D) rfl
      (fun _ _ => rfl) (fun _ _ => ⟨fun _ => rfl, fun h => absurd List.mem_cons_self h⟩)
      (fun _ _ _ h => ⟨fun hA => h.1 (by simp [hA]), fun _ => rfl⟩) t0 κ w X hyps
  | .R r :: D => by
    intro t0 κ w X hyps
    exact cntLoop_spec hN r D (nest_spec hN rr hrr hNP D) (rr r) (hrr r) (hNP r) t0 κ w X hyps

/-! ## Leading-block loops -/

theorem dataLoop1_iter {priv : K → Bool} {G : ℕ → K → List Sym} {Pot : ℕ → ℕ} (SRC U : K)
    (hU : priv U = true) (hS : priv SRC = false) (body : DProg K q) (Bs M0 oh : ℕ)
    (hbody : ∀ m < M0, ∀ (κ : Key q) (w : CReg) (X : K → List Sym), ∃ w' κ' c,
      Eval [] body ⟨(w, κ), ovl priv (G (m * Bs)) X⟩ ⟨(w', κ'), ovl priv (G ((m + 1) * Bs)) X⟩ c ∧
        c + Pot ((m + 1) * Bs) ≤ Pot (m * Bs) + oh)
    (htest : ∀ m ≤ M0, TMFw.W4.isRecR (G (m * Bs) SRC).head? = decide (m < M0))
    (X : K → List Sym) :
    ∀ n, n ≤ M0 → ∀ (κ : Key q) (w : CReg), w.1 = (G ((M0 - n) * Bs) SRC).head? →
      ∃ w' κ' c, Eval [] (.loop recR (.seq (pushSym U tickSym) (.seq body (liftS (peekR SRC)))))
          ⟨(w, κ), ovl priv (G ((M0 - n) * Bs))
            (Function.update X U (List.replicate (M0 - n) tickSym ++ X U))⟩
          ⟨(w', κ'), ovl priv (G (M0 * Bs))
            (Function.update X U (List.replicate M0 tickSym ++ X U))⟩ c ∧
        c + Pot (M0 * Bs) ≤ Pot ((M0 - n) * Bs) + n * (oh + 3) + 1
  | 0, _, κ, w, hw => by
    rw [Nat.sub_zero] at hw ⊢
    refine ⟨w, κ, 1, ?_, by simp only [Nat.zero_mul, Nat.add_zero]; omega⟩
    refine Eval.loop_false ?_
    show TMFw.W4.isRecR w.1 = false
    rw [hw, htest M0 le_rfl]
    simp
  | n + 1, hn, κ, w, hw => by
    have hm : M0 - (n + 1) < M0 := by omega
    have e1 := push_priv (q := q) (G := G ((M0 - (n + 1)) * Bs))
      (X := Function.update X U (List.replicate (M0 - (n + 1)) tickSym ++ X U)) hU tickSym [] (w, κ)
    rw [Function.update_self, Function.update_idem, ← List.cons_append, ← List.replicate_succ,
      show M0 - (n + 1) + 1 = M0 - n by omega] at e1
    obtain ⟨w2, κ2, c2, e2, hc2⟩ := hbody _ hm κ w
      (Function.update X U (List.replicate (M0 - n) tickSym ++ X U))
    rw [show M0 - (n + 1) + 1 = M0 - n by omega] at e2 hc2
    have e3 := liftS_eval (q := q) (w2, κ2) (Eval.peek [] SRC (fun _ o => o) w2.1
      (ovl priv (G ((M0 - n) * Bs)) (Function.update X U (List.replicate (M0 - n) tickSym ++ X U))))
    obtain ⟨w4, κ4, c4, e4, hc4⟩ := dataLoop1_iter SRC U hU hS body Bs M0 oh hbody htest X n
      (by omega) κ2 ((ovl priv (G ((M0 - n) * Bs))
        (Function.update X U (List.replicate (M0 - n) tickSym ++ X U)) SRC).head?, w2.2)
      (by simp [ovl_pub hS])
    have htrue : recR (w, κ) = true := by
      show TMFw.W4.isRecR w.1 = true
      rw [hw, htest _ (by omega)]
      simp [hm]
    refine ⟨w4, κ4, _, Eval.loop_true htrue (Eval.seq e1 (Eval.seq e2 e3)) e4, ?_⟩
    have hmul : (n + 1) * (oh + 3) = n * (oh + 3) + (oh + 3) := by ring
    rw [hmul]
    omega

theorem dataLoop1_spec {priv : K → Bool} {G : ℕ → K → List Sym} {Pot : ℕ → ℕ} (SRC U : K)
    (hU : priv U = true) (hS : priv SRC = false) (body : DProg K q) (Bs M0 oh : ℕ)
    (hbody : ∀ m < M0, ∀ (κ : Key q) (w : CReg) (X : K → List Sym), ∃ w' κ' c,
      Eval [] body ⟨(w, κ), ovl priv (G (m * Bs)) X⟩ ⟨(w', κ'), ovl priv (G ((m + 1) * Bs)) X⟩ c ∧
        c + Pot ((m + 1) * Bs) ≤ Pot (m * Bs) + oh)
    (htest : ∀ m ≤ M0, TMFw.W4.isRecR (G (m * Bs) SRC).head? = decide (m < M0))
    (X : K → List Sym) (κ : Key q) (w : CReg) :
    ∃ w' κ' c, Eval [] (dataLoop1 SRC U body) ⟨(w, κ), ovl priv (G 0) X⟩
        ⟨(w', κ'), ovl priv (G (M0 * Bs))
          (Function.update X U (List.replicate M0 tickSym ++ X U))⟩ c ∧
      c + Pot (M0 * Bs) ≤ Pot 0 + M0 * (oh + 3) + 2 := by
  have e1 := liftS_eval (q := q) (w, κ) (Eval.peek [] SRC (fun _ o => o) w.1 (ovl priv (G 0) X))
  obtain ⟨w2, κ2, c2, e2, hc2⟩ := dataLoop1_iter SRC U hU hS body Bs M0 oh hbody htest X M0
    le_rfl κ ((ovl priv (G 0) X SRC).head?, w.2) (by simp [ovl_pub hS])
  rw [Nat.sub_self, Nat.zero_mul, List.replicate_zero, List.nil_append,
    Function.update_eq_self] at e2
  rw [Nat.sub_self, Nat.zero_mul] at hc2
  exact ⟨w2, κ2, _, Eval.seq e1 e2, by omega⟩

theorem dataLoop2_iter {priv : K → Bool} {G : ℕ → K → List Sym} {Pot : ℕ → ℕ} (U : K)
    (hU : priv U = true) (body : DProg K q) (Bs M0 oh : ℕ)
    (hbody : ∀ m < M0, ∀ (κ : Key q) (w : CReg) (X : K → List Sym), ∃ w' κ' c,
      Eval [] body ⟨(w, κ), ovl priv (G (m * Bs)) X⟩ ⟨(w', κ'), ovl priv (G ((m + 1) * Bs)) X⟩ c ∧
        c + Pot ((m + 1) * Bs) ≤ Pot (m * Bs) + oh)
    (X : K → List Sym) :
    ∀ n, n ≤ M0 → ∀ (κ : Key q) (w : CReg),
      w.1 = (List.replicate n tickSym ++ delimSym :: X U).head? →
      ∃ w' κ' c, Eval [] (.loop (isSymR tickSym) (.seq body (popSym U)))
          ⟨(w, κ), ovl priv (G ((M0 - n) * Bs))
            (Function.update X U (List.replicate n tickSym ++ delimSym :: X U).tail)⟩
          ⟨(w', κ'), ovl priv (G (M0 * Bs)) X⟩ c ∧
        c + Pot (M0 * Bs) ≤ Pot ((M0 - n) * Bs) + n * (oh + 2) + 1
  | 0, _, κ, w, hw => by
    refine ⟨w, κ, 1, ?_, by simp only [Nat.sub_zero, Nat.zero_mul, Nat.add_zero]; omega⟩
    simp only [Nat.sub_zero, List.replicate_zero, List.nil_append, List.tail_cons,
      Function.update_eq_self]
    refine Eval.loop_false ?_
    show decide (w.1 = some tickSym) = false
    rw [hw]
    simp [tickSym, delimSym]
  | n + 1, hn, κ, w, hw => by
    have hm : M0 - (n + 1) < M0 := by omega
    obtain ⟨w2, κ2, c2, e2, hc2⟩ := hbody _ hm κ w
      (Function.update X U (List.replicate (n + 1) tickSym ++ delimSym :: X U).tail)
    rw [show M0 - (n + 1) + 1 = M0 - n by omega] at e2 hc2
    have e3 := pop_priv (q := q) (G := G ((M0 - n) * Bs))
      (X := Function.update X U (List.replicate (n + 1) tickSym ++ delimSym :: X U).tail) hU [] (w2, κ2)
    rw [Function.update_self, Function.update_idem] at e3
    have htail : (List.replicate (n + 1) tickSym ++ delimSym :: X U).tail =
        List.replicate n tickSym ++ delimSym :: X U := by
      simp [List.replicate_succ]
    rw [htail] at e3
    obtain ⟨w4, κ4, c4, e4, hc4⟩ := dataLoop2_iter U hU body Bs M0 oh hbody X n (by omega) κ2
      ((List.replicate n tickSym ++ delimSym :: X U).head?, w2.2) rfl
    have htrue : isSymR tickSym (w, κ) = true := by
      show decide (w.1 = some tickSym) = true
      rw [hw]
      simp [List.replicate_succ]
    refine ⟨w4, κ4, _, Eval.loop_true htrue (Eval.seq e2 e3) e4, ?_⟩
    have hmul : (n + 1) * (oh + 2) = n * (oh + 2) + (oh + 2) := by ring
    rw [hmul]
    omega

theorem dataLoop2_spec {priv : K → Bool} {G : ℕ → K → List Sym} {Pot : ℕ → ℕ} (U : K)
    (hU : priv U = true) (body : DProg K q) (Bs M0 oh : ℕ)
    (hbody : ∀ m < M0, ∀ (κ : Key q) (w : CReg) (X : K → List Sym), ∃ w' κ' c,
      Eval [] body ⟨(w, κ), ovl priv (G (m * Bs)) X⟩ ⟨(w', κ'), ovl priv (G ((m + 1) * Bs)) X⟩ c ∧
        c + Pot ((m + 1) * Bs) ≤ Pot (m * Bs) + oh)
    (X : K → List Sym) (κ : Key q) (w : CReg) :
    ∃ w' κ' c, Eval [] (dataLoop2 U body)
        ⟨(w, κ), ovl priv (G 0) (Function.update X U (List.replicate M0 tickSym ++ delimSym :: X U))⟩
        ⟨(w', κ'), ovl priv (G (M0 * Bs)) X⟩ c ∧
      c + Pot (M0 * Bs) ≤ Pot 0 + M0 * (oh + 2) + 2 := by
  have e1 := pop_priv (q := q) (G := G 0)
    (X := Function.update X U (List.replicate M0 tickSym ++ delimSym :: X U)) hU [] (w, κ)
  rw [Function.update_self, Function.update_idem] at e1
  obtain ⟨w2, κ2, c2, e2, hc2⟩ := dataLoop2_iter U hU body Bs M0 oh hbody X M0 le_rfl κ
    ((List.replicate M0 tickSym ++ delimSym :: X U).head?, w.2) rfl
  rw [Nat.sub_self, Nat.zero_mul] at e2 hc2
  exact ⟨w2, κ2, _, Eval.seq e1 e2, by omega⟩

end NestSpec2

end SubNLogN.Machine.K1Digit
