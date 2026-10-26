import WP.Top.Skeleton
import Contracts.Top.W11

/-!
# WP.Top.Correct — the six stages compose to the acceptance triple

Each stage's own triple is lifted to the global registers (`liftRegs`) and, for the work-stack
stages, to the production layout (`liftWork`, after `Runs.embed` for the contract programs). Its
postcondition is rewritten to the exact global state that the next stage expects:

| after | global state | lemma |
|---|---|---|
| input (W0m) | `prodOf (prmState n a b)` | `stage_in` |
| tables (W7) | `prodOf (tabOut n a b cSpec)` | `stage_tab` |
| conversion | `prodOf (convOut n a b cSpec)` | `stage_conv` |
| glue | `prodOf (w9In n a b cSpec)` | `stage_glue` |
| pipeline (W9) | `prodOf (w9Out n a b cSpec (a * b))` | `stage_w9` (value via W11 and W8) |
| output | `outputStk (encodeNat (a * b))` | `stage_out` |

`top_triple`: for each input there is a W7 joint output `cSpec` such that `topProg` maps
`⟨σ0, inputStk (encNatPair.encode (a, b))⟩` to `outputStk (encodeNat (a * b))`. The cost is the sum
of the stage costs.
-/

namespace WP.Top

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 IntMulTM IntMulTM.Contracts
  IntMulTM.Contracts.Top

/-! ## Stage specifications and costs -/

/-- W7's cost at bit length `n` for the hierarchy `cSpec` (the `W7_buildTables` bound). -/
def tabCost (C7 n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) : ℕ :=
  C7 * ((W8.hSpec n).precomputeSeriesTableCost +
    (W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length +
    bitLen (W8.hL n) + bitLen (W8.hP0 n) + bitLen (W8.hK0 n) + 1)

/-- The converter's cost. -/
def convCost (Cc : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) : ℕ :=
  Cc * ((W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length + 1)

/-- W9's cost at the headline parameters. -/
def w9Cost (C9 : ℕ) (Mul : ℕ → ℕ) (wdF wdI : ℕ → ℕ → ℕ) (wR : ℕ → ℕ) (n : ℕ)
    (cSpec : IntMul.ComputablePaperFastDFTSpec) : ℕ :=
  C9 * (rootBound Mul (wR n) (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) +
    pipeBound Mul (wdF n) cSpec (W8.hB n) 0 1 +
    pipeBound Mul (wdI n) cSpec (IntMul.rootPrecision (W8.hB n) (W8.hK0 n)) 0 1 +
    (tapeSyms cSpec).length + 1)

/-- The body of `W7_buildTables W7.snapshotSchedule` for one builder instance. -/
def W7Spec {m : ℕ} {R : Type} (P : Prog (Loc 4 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (L p K : ℕ) (rL rp rK : List Sym) (S : Loc 4 m → List Sym),
    8 ≤ p → K ≤ 2 ^ (L + 1) → TermOK rL → TermOK rp → TermOK rK →
    S (.inl 1) = natSyms L ++ rL → S (.inl 2) = natSyms p ++ rp → S (.inl 3) = natSyms K ++ rK →
    ∃ cSpec : IntMul.ComputablePaperFastDFTSpec,
      W7.JointOutput W7.snapshotSchedule.toTapeFormat W7.snapshotSchedule.Faithful
        (IntMul.buildQuantizedSpecPaperStop L p K) cSpec ∧
      Runs P S (Function.update S (.inl 0)
          (W7.tape W7.snapshotSchedule.toTapeFormat cSpec ++ S (.inl 0)))
        (fun _ => True)
        (C * ((IntMul.buildQuantizedSpecPaperStop L p K).precomputeSeriesTableCost +
          (W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length + bitLen L + bitLen p +
            bitLen K + 1))

/-- The body of `TapeConv` for one converter instance. -/
def ConvSpec {m : ℕ} {R : Type} (P : Prog (Loc 1 m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (n : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) (S : Loc 1 m → List Sym), Joint n cSpec →
    S (.inl 0) = W7.tape W7.snapshotSchedule.toTapeFormat cSpec →
    (tapeSyms cSpec).length ≤ C * ((W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length + 1) ∧
    Runs P S (Function.update S (.inl 0) (tapeSyms cSpec)) (fun _ => True)
      (C * ((W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length + 1))

/-- The body of `W9_multiply Mul` for one multiplier instance. -/
def W9Spec {m : ℕ} {R : Type} (Mul : ℕ → ℕ) (P : Prog (BLoc m) (fun _ => Sym) R) (C : ℕ) : Prop :=
  ∀ (cSpec : IntMul.ComputablePaperFastDFTSpec) (b K0 k1 k2 A B : ℕ) (wdF wdI : ℕ → ℕ) (wR : ℕ)
    (σ : BLoc m → List Sym) (rA rB r0 restT : List Sym),
    A < 2 ^ (b * k1) → B < 2 ^ (b * k2) → k1 + k2 ≤ 2 ^ K0 → TermOK rA → TermOK rB →
    RootOK cSpec b K0 k1 k2 A B wdF wdI wR →
    σ (.inl .OA) = natSyms A ++ rA → σ (.inl .OB) = natSyms B ++ rB →
    σ (.inl .C0) = hdrSyms [b, K0, k1, k2] ++ r0 → σ (.inl .W0) = [] →
    σ (.inl .TR) = tapeSyms cSpec ++ restT → restT.head? ≠ some symPost →
    Runs P σ (Function.update (Function.update σ (.inl .OA)
        (natSyms (IntMul.computablePaperFastDFTMultiply cSpec b K0 k1 k2 A B) ++ rA)) (.inl .OB) rB)
      (fun _ => True)
      (C * (rootBound Mul wR b K0 k1 k2 + pipeBound Mul wdF cSpec b 0 1 +
        pipeBound Mul wdI cSpec (IntMul.rootPrecision b K0) 0 1 + (tapeSyms cSpec).length + 1))

/-- W0m's postcondition at the global layout. -/
def InPost {σ : Type} (a b : ℕ) (s : St (StackId GW) (StackId.Γ encNatPair.Γ) σ) : Prop :=
  s.stk .input = [] ∧ s.stk .output = [] ∧ (∀ x, s.stk (.work (ι0 x)) = WP.W0m.outW a b x) ∧
    ∀ w, (∀ x, ι0 x ≠ w) → s.stk (.work w) = []

/-! ## Headline facts -/

theorem headline_bk (n : ℕ) : n ≤ W8.hB n * W8.hK n := by
  have hb : 1 ≤ W8.hB n := le_max_left 1 (Nat.log2 n)
  unfold W8.hK
  have hdiv := Nat.div_add_mod n (W8.hB n)
  have hmod : n % W8.hB n < W8.hB n := Nat.mod_lt n (by omega)
  have hmul : W8.hB n * (n / W8.hB n + 1) = W8.hB n * (n / W8.hB n) + W8.hB n := by ring
  omega

theorem headline_kk (n : ℕ) : W8.hK n + W8.hK n ≤ 2 ^ W8.hK0 n := by
  have hlt := IntMul.lt_two_pow_log2_succ (2 * W8.hK n)
  have hle : Nat.log2 (2 * W8.hK n) + 2 ≤ W8.hK0 n := le_max_right 4 _
  have hpow : 2 ^ (Nat.log2 (2 * W8.hK n) + 1) ≤ 2 ^ W8.hK0 n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem lt_pow_bk {n A : ℕ} (hA : A < 2 ^ n) : A < 2 ^ (W8.hB n * W8.hK n) :=
  hA.trans_le (Nat.pow_le_pow_right (by omega) (headline_bk n))

/-- W11's obligation for `W9_multiply`'s output relation holds outright. -/
def MOutW9 (n A B out : ℕ) : Prop :=
  ∃ cSpec, Joint n cSpec ∧
    out = IntMul.computablePaperFastDFTMultiply cSpec (W8.hB n) (W8.hK0 n) (W8.hK n) (W8.hK n) A B

theorem w11_W9 : W11_refinement True MOutW9 := by
  rintro - n A B out - - ⟨cSpec, hj, rfl⟩
  exact ⟨cSpec, hj.faithful, rfl⟩

/-- **The pipeline's value is the product**, through the W11 interface. -/
theorem w9_value (a b : ℕ) {cSpec : IntMul.ComputablePaperFastDFTSpec}
    (hj : Joint (operandBits a b) cSpec) :
    IntMul.computablePaperFastDFTMultiply cSpec (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
      (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) a b = a * b :=
  W11_output_eq_mul_input w11_W9 trivial ⟨cSpec, hj, rfl⟩

/-! ## The stages, lifted -/

variable {σi R7 Rc R9 : Type}

/-- Precondition shape of the work-stack stages. -/
theorem pre_of_prodOf {σ : Type} {s : St (StackId GW) (StackId.Γ encNatPair.Γ) σ}
    {S : GW → List Sym} (hs : s.stk = prodOf S) :
    (fun w => s.stk (.work w)) = S ∧ s.stk .input = [] ∧ s.stk .output = [] := by
  refine ⟨funext fun w => ?_, ?_, ?_⟩ <;> simp only [hs, prodOf]

/-- **Stage 1** (input, W0m). -/
theorem stage_in {Pin : Prog (StackId GW) (StackId.Γ encNatPair.Γ) σi} {Tin : ℕ} (a b : ℕ)
    (σ0 : TopRegs σi R7 Rc R9)
    (h : Triple [] (fun s => s.stk = inputStk (encNatPair.encode (a, b))) Pin (InPost a b) Tin) :
    Triple [] (· = ⟨σ0, inputStk (encNatPair.encode (a, b))⟩) (Pin.liftRegs (lIn σi R7 Rc R9))
      (fun s => s.stk = prodOf (prmState (operandBits a b) a b)) Tin := by
  refine (Triple.liftRegs (lIn σi R7 Rc R9) h (fun _ => True) (fun _ _ _ => trivial)).conseq ?_ ?_
    le_rfl
  · rintro s rfl
    exact ⟨rfl, trivial⟩
  · rintro s ⟨⟨hi, ho, hw, hz⟩, -⟩
    exact afterIn_eq a b hi ho hw hz

/-- **Stage 2** (tables, W7). W7 picks the hierarchy `cSpec`. -/
theorem stage_tab {m : ℕ} (hm : m ≤ 32) {P7 : Prog (Loc 4 m) (fun _ => Sym) R7} {C7 : ℕ}
    (h7 : W7Spec P7 C7) (n A B : ℕ) :
    ∃ cSpec, Joint n cSpec ∧
      Triple []
        (fun s : St (StackId GW) (StackId.Γ encNatPair.Γ) (TopRegs σi R7 Rc R9) =>
          s.stk = prodOf (prmState n A B))
        ((tabStage P7 hm).liftRegs (l7 σi R7 Rc R9))
        (fun s => s.stk = prodOf (tabOut n A B cSpec)) (tabCost C7 n cSpec) := by
  have hpre := W7.headline_pre n
  obtain ⟨cSpec, hj, hr⟩ := h7 (W8.hL n) (W8.hP0 n) (W8.hK0 n) [] [] []
    (fun l => prmState n A B (ι7 hm l)) hpre.1 hpre.2 TermOK.nil TermOK.nil TermOK.nil
    (List.append_nil _).symm (List.append_nil _).symm (List.append_nil _).symm
  refine ⟨cSpec, hj, ?_⟩
  have he := Runs.embed (ι7_inj hm) hr (prmState n A B) (fun _ => rfl)
  have hw := Triple.liftWork (A := encNatPair.Γ) he
    (fun s => s.stk .input = [] ∧ s.stk .output = [])
    (fun _ _ hs hi ho => ⟨hi.trans hs.1, ho.trans hs.2⟩)
  refine (Triple.liftRegs (l7 σi R7 Rc R9) hw (fun _ => True) (fun _ _ _ => trivial)).conseq ?_
    ?_ le_rfl
  · intro s hs
    exact ⟨pre_of_prodOf hs, trivial⟩
  · rintro s ⟨⟨⟨h1, h2, -⟩, hi, ho⟩, -⟩
    refine eq_prodOf hi ho (fun w => ?_)
    exact congrFun (afterTab_eq hm n A B cSpec (T := fun w => s.stk (.work w)) h1 h2) w

/-- **Stage 3** (tape conversion). -/
theorem stage_conv {m : ℕ} (hm : m ≤ 75) {Pc : Prog (Loc 1 m) (fun _ => Sym) Rc} {Cc : ℕ}
    (hc : ConvSpec Pc Cc) (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (hj : Joint n cSpec) :
    Triple []
      (fun s : St (StackId GW) (StackId.Γ encNatPair.Γ) (TopRegs σi R7 Rc R9) =>
        s.stk = prodOf (tabOut n A B cSpec))
      ((convStage Pc hm).liftRegs (lc σi R7 Rc R9))
      (fun s => s.stk = prodOf (convOut n A B cSpec)) (convCost Cc cSpec) := by
  obtain ⟨-, hr⟩ := hc n cSpec (fun l => tabOut n A B cSpec (ιc hm l)) hj
    (by show tabOut n A B cSpec .tr = _; unfold tabOut; rw [Function.update_self])
  have he := Runs.embed (ιc_inj hm) hr (tabOut n A B cSpec) (fun _ => rfl)
  have hw := Triple.liftWork (A := encNatPair.Γ) he
    (fun s => s.stk .input = [] ∧ s.stk .output = [])
    (fun _ _ hs hi ho => ⟨hi.trans hs.1, ho.trans hs.2⟩)
  refine (Triple.liftRegs (lc σi R7 Rc R9) hw (fun _ => True) (fun _ _ _ => trivial)).conseq ?_
    ?_ le_rfl
  · intro s hs
    exact ⟨pre_of_prodOf hs, trivial⟩
  · rintro s ⟨⟨⟨h1, h2, -⟩, hi, ho⟩, -⟩
    refine eq_prodOf hi ho (fun w => ?_)
    exact congrFun (afterConv_eq hm n A B cSpec (T := fun w => s.stk (.work w)) h1 h2) w

/-- **Stage 4** (parameter glue). -/
theorem stage_glue (n A B : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) :
    Triple []
      (fun s : St (StackId GW) (StackId.Γ encNatPair.Γ) (TopRegs σi R7 Rc R9) =>
        s.stk = prodOf (convOut n A B cSpec))
      (glueStage.liftRegs (lOut σi R7 Rc R9))
      (fun s => s.stk = prodOf (w9In n A B cSpec)) (glueCost n) := by
  have hg : Triple [] (fun s : SSt GW => s.stk = convOut n A B cSpec) glueProg
      (fun s => s.stk = w9In n A B cSpec) (glueCost n) := by
    rintro ⟨v, S⟩ hS
    change S = convOut n A B cSpec at hS
    subst hS
    exact ⟨_, _, glue_eval (convOut n A B cSpec) n (by simp [convOut, prmState])
      (by simp [convOut, prmState]) (by simp [convOut, prmState]) (by simp [convOut, prmState]) v,
      rfl, le_rfl⟩
  have hw := Triple.liftWork (A := encNatPair.Γ) hg
    (fun s => s.stk .input = [] ∧ s.stk .output = [])
    (fun _ _ hs hi ho => ⟨hi.trans hs.1, ho.trans hs.2⟩)
  refine (Triple.liftRegs (lOut σi R7 Rc R9) hw (fun _ => True) (fun _ _ _ => trivial)).conseq ?_
    ?_ le_rfl
  · intro s hs
    exact ⟨pre_of_prodOf hs, trivial⟩
  · rintro s ⟨⟨h1, hi, ho⟩, -⟩
    exact eq_prodOf hi ho (fun w => congrFun h1 w)

/-- **Stage 5** (pipeline, W9). -/
theorem stage_w9 {m : ℕ} (hm : m ≤ 64) {Mul : ℕ → ℕ} {P9 : Prog (BLoc m) (fun _ => Sym) R9}
    {C9 : ℕ} (h9 : W9Spec Mul P9 C9) {wdF wdI : ℕ → ℕ → ℕ} {wR : ℕ → ℕ}
    (hroot : W9RootOK wdF wdI wR) (a b : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec)
    (hj : Joint (operandBits a b) cSpec) :
    Triple []
      (fun s : St (StackId GW) (StackId.Γ encNatPair.Γ) (TopRegs σi R7 Rc R9) =>
        s.stk = prodOf (w9In (operandBits a b) a b cSpec))
      ((w9Stage P9 hm).liftRegs (l9 σi R7 Rc R9))
      (fun s => s.stk = prodOf (w9Out (operandBits a b) a b cSpec (a * b)))
      (w9Cost C9 Mul wdF wdI wR (operandBits a b) cSpec) := by
  obtain ⟨hA, hB, -, -⟩ := input_bridge a b
  have hr := h9 cSpec (W8.hB (operandBits a b)) (W8.hK0 (operandBits a b))
    (W8.hK (operandBits a b)) (W8.hK (operandBits a b)) a b (wdF (operandBits a b))
    (wdI (operandBits a b)) (wR (operandBits a b))
    (fun l => w9In (operandBits a b) a b cSpec (ι9 hm l)) [] [] [] []
    (lt_pow_bk hA) (lt_pow_bk hB) (headline_kk _) TermOK.nil TermOK.nil
    (hroot _ a b cSpec (WP.W0m.operandBits_pos a b) hA hB hj)
    (by rw [List.append_nil]; exact w9In_oa _ _ _ _)
    (by rw [List.append_nil]; exact w9In_ob _ _ _ _)
    (by rw [List.append_nil]; exact w9In_c0 _ _ _ _)
    (w9In_w0 _ _ _ _)
    (by rw [List.append_nil]; exact w9In_tr _ _ _ _)
    (by simp)
  rw [w9_value a b hj] at hr
  have he := Runs.embed (ι9_inj hm) hr (w9In (operandBits a b) a b cSpec) (fun _ => rfl)
  have hw := Triple.liftWork (A := encNatPair.Γ) he
    (fun s => s.stk .input = [] ∧ s.stk .output = [])
    (fun _ _ hs hi ho => ⟨hi.trans hs.1, ho.trans hs.2⟩)
  refine (Triple.liftRegs (l9 σi R7 Rc R9) hw (fun _ => True) (fun _ _ _ => trivial)).conseq ?_
    ?_ le_rfl
  · intro s hs
    exact ⟨pre_of_prodOf hs, trivial⟩
  · rintro s ⟨⟨⟨h1, h2, -⟩, hi, ho⟩, -⟩
    refine eq_prodOf hi ho (fun w => ?_)
    exact congrFun (afterW9_eq hm _ a b cSpec (a * b) (T := fun w => s.stk (.work w)) h1 h2) w

/-- **Stage 6** (output). -/
theorem stage_out (n A B v : ℕ) (cSpec : IntMul.ComputablePaperFastDFTSpec) :
    Triple []
      (fun s : St (StackId GW) (StackId.Γ encNatPair.Γ) (TopRegs σi R7 Rc R9) =>
        s.stk = prodOf (w9Out n A B cSpec v))
      (outStage.liftRegs (lOut σi R7 Rc R9)) (fun s => s.stk = outputStk (encodeNat v))
      (outCost (bitLen v) (totalSize (w9Out n A B cSpec v))) := by
  refine (Triple.liftRegs (lOut σi R7 Rc R9)
    (outStage_triple v (totalSize (w9Out n A B cSpec v))) (fun _ => True)
    (fun _ _ _ => trivial)).conseq ?_ ?_ le_rfl
  · intro s hs
    have h := pre_of_prodOf hs
    refine ⟨⟨h.2.1, h.2.2, ⟨[], TermOK.nil, ?_⟩, ?_⟩, trivial⟩
    · show s.stk (.work .oa) = _
      rw [hs, List.append_nil]
      simp [prodOf, w9Out]
    · show totalSize (fun w => s.stk (.work w)) ≤ _
      rw [h.1]
  · rintro s ⟨h, -⟩
    exact h

/-- **The composed triple.** -/
theorem top_triple {m7 mc m9 : ℕ} (hm7 : m7 ≤ 32) (hmc : mc ≤ 75) (hm9 : m9 ≤ 64)
    {Pin : Prog (StackId GW) (StackId.Γ encNatPair.Γ) σi} {Tin : ℕ → ℕ → ℕ}
    (hin : ∀ a b, Triple [] (fun s => s.stk = inputStk (encNatPair.encode (a, b))) Pin (InPost a b)
      (Tin a b))
    {P7 : Prog (Loc 4 m7) (fun _ => Sym) R7} {C7 : ℕ} (h7 : W7Spec P7 C7)
    {Pc : Prog (Loc 1 mc) (fun _ => Sym) Rc} {Cc : ℕ} (hc : ConvSpec Pc Cc)
    {Mul : ℕ → ℕ} {P9 : Prog (BLoc m9) (fun _ => Sym) R9} {C9 : ℕ} (h9 : W9Spec Mul P9 C9)
    {wdF wdI : ℕ → ℕ → ℕ} {wR : ℕ → ℕ} (hroot : W9RootOK wdF wdI wR)
    (σ0 : TopRegs σi R7 Rc R9) (a b : ℕ) :
    ∃ cSpec, Joint (operandBits a b) cSpec ∧
      Triple [] (· = ⟨σ0, inputStk (encNatPair.encode (a, b))⟩)
        (topProg Pin P7 hm7 Pc hmc P9 hm9)
        (fun s => s.stk = outputStk (encodeNat (a * b)))
        (Tin a b + (tabCost C7 (operandBits a b) cSpec + (convCost Cc cSpec +
          (glueCost (operandBits a b) + (w9Cost C9 Mul wdF wdI wR (operandBits a b) cSpec +
            outCost (bitLen (a * b)) (totalSize (w9Out (operandBits a b) a b cSpec (a * b)))))))) := by
  obtain ⟨cSpec, hj, h2⟩ := stage_tab (σi := σi) (Rc := Rc) (R9 := R9) hm7 h7 (operandBits a b) a b
  refine ⟨cSpec, hj, ?_⟩
  exact Triple.seq (stage_in a b σ0 (hin a b))
    (Triple.seq h2
      (Triple.seq (stage_conv hmc hc _ a b cSpec hj)
        (Triple.seq (stage_glue _ a b cSpec)
          (Triple.seq (stage_w9 hm9 h9 hroot a b cSpec hj)
            (stage_out _ a b (a * b) cSpec)))))

#assert_std_axioms headline_bk headline_kk lt_pow_bk w11_W9 w9_value pre_of_prodOf stage_in
  stage_tab stage_conv stage_glue stage_w9 stage_out top_triple

end WP.Top
