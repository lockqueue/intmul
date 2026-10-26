import WP.W9s.Conv
import WP.W9s.SpecMath
import WP.W9s.RecMain
import WP.W9s.MainCost
import WP.W9s.Halve
import Contracts.Machine.W3

/-!
# WP.W9s.Main — **`W9_synFFT`** (the top level of W9s)

Top-level assembly of `W9_synFFT` over the host program and pure `synL` equivalence.

* **Kit** (`Top.mkKit`, `Top.exists_kitOK`): the adder and subtracter instances of `W3_addInt` and
  `W3_subInt`, and the rounding halving `halveRound Ii · sA` (piece [b]) from the seed instance
  `w3_incNat`.
* **Program** (`Top.synTop`), on the W9s host `Loc 2 20`:
  `readHdr ; toBlk ; fft ; fromBlk ; dsPop ; dropTo sUR symG`. Steps:
  1. push the unary counters `r` and `Δ0 = 2r/t1`;
  2. flat entries become a block;
  3. run the recursion (`fft_spec`);
  4. flatten back;
  5. pop both counters.

  `Top.HT.synTop` is the exact host triple; its cost is exactly `synCostB`.
* **Embedding** (`Top.eB : Host → BLoc 20`, `sA ↦ W0`, `sC0 ↦ C0`). `Top.runs_of_HT_eB`: by
  `Runs.embed`, every other layout-B stack is untouched.
* **`W9_synFFT_holds`**:
  - value step: `out_eq` with `Δ0 = 2r/t1 = 2·(r/t1)` (`Top.delta0_eq`);
  - cost step: `synCostB_le`, with constant `CM CA CS CH` and `20` scratch stacks.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul IntMul.LevelSync

attribute [local instance 10000] instZeroIntElementary

namespace Top

/-! ## The kit from the W3 contracts -/

/-- The kit: adder, subtracter, rounding halving. -/
def mkKit (Ia Is : Inst 3 4 Unit) (Ii : Inst 1 4 Unit) : Kit :=
  ⟨Ia, Is, HReg Ii, fun k => halveRound Ii k sA⟩

theorem halveSpec_mk {Ii : Inst 1 4 Unit} {C : ℕ} (hI : SpecInc Ii C) :
    HalveSpec (fun k => halveRound Ii k sA) (C + 20) :=
  ⟨fun k => halveRound_closed Ii k sA, fun k B x rest hrest hB =>
    HT.halveRound hI k sA (by decide) B x rest hrest hB []⟩

theorem finite_R_mk (Ia Is : Inst 3 4 Unit) (Ii : Inst 1 4 Unit) : Finite (mkKit Ia Is Ii).R := by
  haveI := Ia.fin; haveI := Is.fin; haveI := Ii.fin
  show Finite (Option Sym × Ia.R × Is.R × (Option Sym × Option Sym × Ii.R))
  infer_instance

theorem nonempty_R_mk (Ia Is : Inst 3 4 Unit) (Ii : Inst 1 4 Unit) :
    Nonempty (mkKit Ia Is Ii).R := by
  haveI := Ia.ne; haveI := Is.ne; haveI := Ii.ne
  show Nonempty (Option Sym × Ia.R × Is.R × (Option Sym × Option Sym × Ii.R))
  infer_instance

/-- **A kit from the W3 contracts** (`incNat` is the seed instance `w3_incNat`). -/
theorem exists_kitOK (ha : W3_addInt) (hs : W3_subInt) :
    ∃ (K : Kit) (CA CS CH : ℕ), KitOK K CA CS CH ∧ Finite K.R ∧ Nonempty K.R := by
  obtain ⟨CA, hA⟩ := exists_inst ha
  obtain ⟨Ia, sa⟩ := hA ()
  obtain ⟨CS, hS⟩ := exists_inst hs
  obtain ⟨Is, ss⟩ := hS ()
  obtain ⟨CI, hI⟩ := exists_inst w3_incNat
  obtain ⟨Ii, si⟩ := hI ()
  exact ⟨mkKit Ia Is Ii, CA, CS, CI + 20, ⟨sa, ss, halveSpec_mk si⟩, finite_R_mk Ia Is Ii,
    nonempty_R_mk Ia Is Ii⟩

/-! ## The program and its exact host triple -/

/-- **The top-level program.** -/
def synTop (K : Kit) : MProg K :=
  .seq (readHdr K) <| .seq (toBlk K) <| .seq (fft K) <| .seq (fromBlk K) <|
  .seq (dsPop K) (dropTo (lS K) sUR symG)

theorem synTop_closed {K : Kit} {CH : ℕ} (hH : HalveSpec K.Hp CH) : (synTop K).Closed :=
  ⟨readHdr_closed K, toBlk_closed K, fft_closed hH, fromBlk_closed K, dropTo_closed _ _ _,
    dropTo_closed _ _ _⟩

/-- `fft_spec` as an exact-stacks triple. -/
theorem HT.fftTop {K : Kit} {CA CS CH : ℕ} (hK : KitOK K CA CS CH) (hS : SynFacts) (r w n Δ : ℕ)
    (X : List (List (ℤ × ℤ))) (B : Host → List Sym) (rA rDS rUR : List Sym)
    (hlen : X.length = 2 ^ n) (hrows : ∀ row ∈ X, row.length = r)
    (hwid : ∀ row ∈ X, ∀ z ∈ row, EntryW w z) (hA : B sA = blkR X ++ symBlk :: rA)
    (hDS : B sDS = units Δ ++ symG :: rDS) (hUR : B sUR = units r ++ symG :: rUR)
    (hΔ : Δ * 2 ^ n = 2 * r) (ρ : List (MProg K)) :
    HT ρ B (fft K) (Function.update B sA (blkR (synL Δ n X) ++ symBlk :: rA))
      (costF CA CS CH w r n + 2) :=
  Triple.pre (fft_spec hK hS r w ρ ⟨n, X, Δ, B, rA⟩)
    (fun _ hs => ⟨⟨hlen, hrows, hwid, hA, ⟨rDS, hDS⟩, ⟨rUR, hUR⟩, hΔ⟩, hs⟩)

/-- `Δ0·2^mt1 = 2r`. -/
theorem delta0_mul (h : PreHdr) (hD : PreDims h) : 2 * h.r / h.t1 * 2 ^ h.mt1 = 2 * h.r := by
  obtain ⟨ht1, hr1, -, hle⟩ := hD
  have hdvd : h.t1 ∣ 2 * h.r := by
    rw [ht1, hr1]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 hle) 2
  rw [← ht1]
  exact Nat.div_mul_cancel hdvd

/-- `Δ0 = 2r/t1 = 2·(r/t1)` (the form of `out_eq`). -/
theorem delta0_eq (h : PreHdr) (hD : PreDims h) : 2 * h.r / h.t1 = 2 * (h.r / h.t1) := by
  obtain ⟨ht1, hr1, -, hle⟩ := hD
  have hdvd : h.t1 ∣ h.r := by
    rw [ht1, hr1]
    exact pow_dvd_pow 2 hle
  exact Nat.mul_div_assoc 2 hdvd

/-- `SynFacts` from piece [a]. -/
theorem synFacts : SynFacts := ⟨synL_length, synL_rows, synL_width⟩

/-- **The top level on the host**: `es X.flatten` on `sA` becomes `es (synL Δ0 mt1 X).flatten`;
every other host stack is restored; the cost is `synCostB`. -/
theorem HT.synTop {K : Kit} {CA CS CH : ℕ} (hK : KitOK K CA CS CH) (h : PreHdr) (hD : PreDims h)
    (w : ℕ) (X : List (List (ℤ × ℤ))) (B : Host → List Sym) (r0 : List Sym)
    (hlen : X.length = h.t1) (hrows : ∀ row ∈ X, row.length = h.r)
    (hwid : ∀ row ∈ X, ∀ z ∈ row, EntryW w z) (hA : B sA = es X.flatten)
    (hC0 : B sC0 = hdrSyms (preTapeFields h.pSub h.m1 h.t1 h.r) ++ r0) :
    HT [] B (synTop K) (Function.update B sA (es (synL (2 * h.r / h.t1) h.mt1 X).flatten))
      (synCostB CA CS CH w h) := by
  have hD' := hD
  obtain ⟨ht1, hr1, -, -⟩ := hD'
  have hr : 0 < h.r := by rw [hr1]; exact Nat.two_pow_pos _
  have hlen' : X.length = 2 ^ h.mt1 := by rw [hlen]; exact ht1
  have hYl := synL_length (2 * h.r / h.t1) h.mt1 X hlen'
  have hYr := synL_rows (2 * h.r / h.t1) h.r h.mt1 X hlen' hrows
  have hYw := synL_width w (2 * h.r / h.t1) h.mt1 X hwid
  have chain :=
    (HT.readHdr K h hD B r0 hC0 []).seq <|
    (HT.toBlk K h.r w hr X _ (B sUR) hrows hwid (by simp [hA]) (by simp) []).seq <|
    (HT.fftTop hK synFacts h.r w h.mt1 (2 * h.r / h.t1) X _ [] (B sDS) (B sUR) hlen' hrows hwid
      (by simp) (by simp) (by simp) (delta0_mul h hD) []).seq <|
    (HT.fromBlk K h.r w (synL (2 * h.r / h.t1) h.mt1 X) _ hYr hYw (by simp) []).seq <|
    (HT.dsPop K _ (2 * h.r / h.t1) (B sDS) (by simp) []).seq <|
    WP.W9s.HT.dropTo (lS K) sUR symG (units h.r) (B sUR) _ (by simp [units, symG, symU])
      (by simp) []
  refine chain.of_eq ?_ ?_
  · funext k
    by_cases e1 : k = sA
    · subst e1
      simp
    by_cases e2 : k = sDS
    · subst e2
      simp
    by_cases e3 : k = sUR
    · subst e3
      simp
    simp [e1, e2, e3]
  · rw [hlen, hYl, length_units, ← ht1]
    unfold synCostB
    exact le_refl _

/-! ## The layout-B embedding -/

/-- The two named host stacks as layout-B stacks. -/
def lb2 : Fin 2 → LB
  | ⟨0, _⟩ => .W0
  | ⟨_ + 1, _⟩ => .C0

theorem lb2_injective : Function.Injective lb2 := by decide

/-- The host inside a layout-B stage with `20` scratch stacks. -/
def eB : Host → BLoc 20
  | .inl i => .inl (lb2 i)
  | .inr j => .inr j

theorem eB_injective : Function.Injective eB := by
  rintro (i | j) (i' | j') hij
  · exact congrArg Sum.inl (lb2_injective (Sum.inl.inj hij))
  · cases hij
  · cases hij
  · exact congrArg Sum.inr (Sum.inr.inj hij)

theorem eB_sA : eB sA = .inl .W0 := rfl

/-- **Transport**: a host triple from `σ ∘ eB` rewriting only `sA` is the stage's `Runs`. -/
theorem runs_of_HT_eB {R : Type} {P : Prog Host (fun _ => Sym) R} {σ : BLoc 20 → List Sym}
    {v : List Sym} {T : ℕ} (h : HT [] (σ ∘ eB) P (Function.update (σ ∘ eB) sA v) T) :
    Runs (P.mapStk eB) σ (Function.update σ (.inl .W0) v) (fun _ => True) T := by
  have h1 := Runs.embed eB_injective (WP.W7k2.HT.runs h) σ (fun _ => rfl)
  intro s hs
  obtain ⟨s', t, e, ⟨hin, hout, -⟩, ht⟩ := h1 s hs
  refine ⟨s', t, e, ⟨?_, trivial⟩, ht⟩
  funext k
  by_cases hk : ∃ l, eB l = k
  · obtain ⟨l, rfl⟩ := hk
    rw [hin l]
    by_cases hl : l = sA
    · subst hl
      rw [eB_sA, Function.update_self, Function.update_self]
    · have hne : eB l ≠ .inl .W0 := fun he => hl (eB_injective (he.trans eB_sA.symm))
      rw [Function.update_of_ne hl, Function.update_of_ne hne]
      rfl
  · push_neg at hk
    rw [hout k hk, Function.update_of_ne]
    intro he
    exact hk sA (by rw [eB_sA, he])

/-- The contract's `W0 = matSyms Pm` is the flat entry list of W9s. -/
theorem matSyms_eq_es (Pm : Array (Array (ℤ × ℤ))) :
    matSyms Pm = es (Pm.toList.map Array.toList).flatten := by
  rw [matSyms, es_eq_blkE]
  rfl

#assert_std_axioms halveSpec_mk finite_R_mk nonempty_R_mk exists_kitOK synTop_closed HT.fftTop
  delta0_mul delta0_eq synFacts HT.synTop lb2_injective eB_injective eB_sA runs_of_HT_eB
  matSyms_eq_es

end Top

open Top in
/-- **`W9_synFFT`** from the W3 contracts `W3_addInt` and `W3_subInt`. -/
theorem W9_synFFT_holds (ha : W3_addInt) (hs : W3_subInt) : W9_synFFT := by
  obtain ⟨K, CA, CS, CH, hK, hfin, hne⟩ := exists_kitOK ha hs
  refine ⟨CM CA CS CH, fun _ => ⟨20, K.R, (synTop K).mapStk eB, by norm_num [w9Scratch], hfin,
    hne, freeBelow_mapStk eB _ 0 (synTop_closed hK.halve), ?_⟩⟩
  intro h w Pm σ hD hC hsz hrows hW _ hW0
  obtain ⟨⟨r0, hC0⟩, -⟩ := hC
  apply runs_of_HT_eB
  have hlen : (Pm.toList.map Array.toList).length = h.t1 := by simp [hsz]
  have hrowsX : ∀ row ∈ Pm.toList.map Array.toList, row.length = h.r := by
    intro row hrow
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hrow
    simpa using hrows a ha'
  have hwidX : ∀ row ∈ Pm.toList.map Array.toList, ∀ z ∈ row, EntryW w z := by
    intro row hrow z hz
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hrow
    exact hW a ha' z hz
  have hA : (σ ∘ eB) sA = es (Pm.toList.map Array.toList).flatten := by
    show σ (.inl .W0) = _
    rw [hW0, matSyms_eq_es]
  refine (HT.synTop hK h hD w _ (σ ∘ eB) r0 hlen hrowsX hwidX hA hC0).of_eq ?_
    (synCostB_le CA CS CH w h hD)
  rw [delta0_eq h hD, es_eq_blkE, out_eq h Pm hD hsz hrows]

#assert_std_axioms W9_synFFT_holds

end WP.W9s
