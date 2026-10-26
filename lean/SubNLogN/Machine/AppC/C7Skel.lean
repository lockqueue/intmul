/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.Corr
import SubNLogN.Machine.Calculus.Basic

/-!
# Lemma A.9 skeleton (`Machine/AppC/C7Skel.lean`): `C7PackedXorStmt` from three phase kernels

Lemma A.9 (`lem:transfer13`,
Appendix A.4 (`sec:transfer-packed`)). The Lemma A.9 kernel is the sequence of three phases, each a
kernel on the same named stacks (`Fin 8`: the array and the counters `K, ρ, f, N1, N2, N3, R`) with
the same restored-scratch convention as `C7PackedXorStmt`:

1. **Lines** (`C7LinesStmt`): the eight packed cyclic chunk shifts (`packedS0`), each one a Lemma A.8
   exchange, a block rotation and the inverse exchange. Pull map: `c7Lift … (packedS0inv …)`.
2. **Repair** (`C7RepairStmt`): extraction of the exceptional records with their destination keys,
   a stable radix sort and reinsertion. Pull map: `c7Lift … (packedS0 ∘ packedT0)`, which moves
   only exceptional records (by `PackedAgreeStmt`; used inside the leaf's proof only).
3. **Top bit** (`C7TopStmt`): `y_{ρ+(f-1)K} ⊕= x_{ρ+(f-1)K}`. Pull map: `c7Lift … (packedTop …)`.

`C7AddrStmt` is the pure address identity: the three pull maps keep record indices in range, and
`lines ∘ repair ∘ top = packedXorAddr` on the rectangle (it uses only `packedS0inv ∘ packedS0 = id`
and `packedT0 ∘ packedTop = ` the `f`-bit XOR; no agreement or counting fact). (Note: `Machine/AppC` and `C7`/`c7` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.9 (`lem:transfer13`).)

**Proved here (0 `sorry`):** `c7PackedXor_of_parts : C7AddrStmt σ → C7LinesStmt τ σ →
C7RepairStmt τ σ → C7TopStmt τ σ → C7PackedXorStmt τ σ` (composition by `callInj`, cost
`(C₁ + C₂ + C₃) · c7Cost`). The four hypotheses are stated here and proved in `C7Addr`/`C7Lines*`/`C7Repair*`/`C7Top`.
Each phase is charged the full `c7Cost` budget of its input array (all three arrays have the same
length and volume).
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts SubNLogN.Math.Networks

namespace AppC.C7Aux

/-! ## Chunk-triple maps of the three phases -/

/-- Inverse of `packedS0`: the eight lines in reverse order with negated signs. -/
def packedS0inv (L K ρ f : ℕ) (xyz : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  eightOps.reverse.foldl (fun p op => packedLine L K ρ f (op.1, -op.2.1, op.2.2) p) xyz

/-- The omitted top selected bit (Lemma A.9 (`lem:transfer13`)): `y_{J} ⊕= x_{J}`,
`J = ρ + (f-1)K`. -/
def packedTop (K ρ f : ℕ) (xyz : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (xyz.1, Nat.xor xyz.2.1 (2 ^ (ρ + (f - 1) * K) * bitAt xyz.1 (ρ + (f - 1) * K)), xyz.2.2)

/-- Component of a named triple `(x, y, z)` by name (`0 = x`, `1 = y`, `2 = z`). -/
def nameGet (t : ℕ × ℕ × ℕ) (n : Fin 3) : ℕ :=
  if n.val = 0 then t.1 else if n.val = 1 then t.2.1 else t.2.2

/-- **Rank-level lift of a chunk-triple map** on the Lemma A.9 rectangle: the named chunk triple of
record index `p` (slot `σ⁻¹ i` holds name `i`) is replaced by its image under `F`; the spectator
coordinates are kept. -/
def c7Lift (L N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) (F : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (p : ℕ) : ℕ :=
  p - (c7Slot L N1 N2 N3 0 p * c7Stride L N1 N2 N3 0 + c7Slot L N1 N2 N3 1 p * c7Stride L N1 N2 N3 1 +
      c7Slot L N1 N2 N3 2 p * c7Stride L N1 N2 N3 2) +
    (nameGet (F (c7Slot L N1 N2 N3 (σ.symm 0) p, c7Slot L N1 N2 N3 (σ.symm 1) p,
        c7Slot L N1 N2 N3 (σ.symm 2) p)) (σ 0) * c7Stride L N1 N2 N3 0 +
      nameGet (F (c7Slot L N1 N2 N3 (σ.symm 0) p, c7Slot L N1 N2 N3 (σ.symm 1) p,
        c7Slot L N1 N2 N3 (σ.symm 2) p)) (σ 1) * c7Stride L N1 N2 N3 1 +
      nameGet (F (c7Slot L N1 N2 N3 (σ.symm 0) p, c7Slot L N1 N2 N3 (σ.symm 1) p,
        c7Slot L N1 N2 N3 (σ.symm 2) p)) (σ 2) * c7Stride L N1 N2 N3 2)

/-- Pull map of phase 1 (lines). -/
def c7LinesInv (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) : ℕ → ℕ :=
  c7Lift (f * K) N1 N2 N3 σ (packedS0inv (f * K) K ρ f)

/-- Pull map of phase 2 (repair). -/
def c7RepairInv (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) : ℕ → ℕ :=
  c7Lift (f * K) N1 N2 N3 σ (fun t => packedS0 (f * K) K ρ f (packedT0 K ρ f t))

/-- Pull map of phase 3 (top bit). -/
def c7TopInv (K ρ f N1 N2 N3 : ℕ) (σ : Equiv.Perm (Fin 3)) : ℕ → ℕ :=
  c7Lift (f * K) N1 N2 N3 σ (packedTop K ρ f)

/-! ## Arrays under index maps -/

section PermLemmas

variable {α : Type} [Inhabited α]

theorem permByInv_length (g : ℕ → ℕ) (v : List α) : (permByInv g v).length = v.length := by
  simp [permByInv]

theorem permByInv_getD {g : ℕ → ℕ} {v : List α} {y : ℕ} (hy : y < v.length) :
    (permByInv g v).getD y default = v.getD (g y) default := by
  simp [permByInv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hy]

theorem permByInv_mem {g : ℕ → ℕ} {v : List α} (hg : ∀ y < v.length, g y < v.length) {a : α}
    (ha : a ∈ permByInv g v) : a ∈ v := by
  simp only [permByInv, List.mem_map, List.mem_range] at ha
  obtain ⟨y, hy, rfl⟩ := ha
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hg y hy)]
  exact List.getElem_mem _

/-- Composition of index maps (the inner map must keep indices in range). -/
theorem permByInv_permByInv {a b : ℕ → ℕ} {v : List α} (ha : ∀ y < v.length, a y < v.length) :
    permByInv a (permByInv b v) = permByInv (fun y => b (a y)) v := by
  apply List.ext_getElem
  · simp [permByInv_length]
  · intro n h1 h2
    have hn : n < v.length := by simpa [permByInv_length] using h1
    simp only [permByInv, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
      List.getElem?_range (ha n hn)]
    rfl

/-- Index maps that agree below the length give the same array. -/
theorem permByInv_congr {a b : ℕ → ℕ} {v : List α} (h : ∀ y < v.length, a y = b y) :
    permByInv a v = permByInv b v := by
  apply List.ext_getElem
  · simp [permByInv_length]
  · intro n h1 _
    have hn : n < v.length := by simpa [permByInv_length] using h1
    simp only [permByInv, List.getElem_map, List.getElem_range]
    rw [h n hn]

end PermLemmas

/-- The volume of an array of `R`-bit records is `M (R + 1)`. -/
theorem vol_of_len {v : List (List Bool)} {R : ℕ} (h : ∀ p ∈ v, p.length = R) :
    vol v = v.length * (R + 1) := by
  induction v with
  | nil => simp [vol, arrSyms, blk]
  | cons p v ih =>
    have hp := h p List.mem_cons_self
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    simp only [vol, arrSyms, blk, List.map_cons, List.flatten_cons, List.length_append, recSyms,
      List.length_map, List.length_singleton] at ih' ⊢
    rw [ih', hp, List.length_cons]
    ring

/-- Number of records of the Lemma A.9 rectangle, `M = N0·2^L·N1·2^L·N2·2^L·N3` with `L = fK`. -/
def c7M (K f N0 N1 N2 N3 : ℕ) : ℕ := N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3

end AppC.C7Aux

open AppC.C7Aux

/-! ## The phase contracts -/

/-- **Lemma A.9 phase contract with index map `g`** (shared shape of the three phases): the named
stacks, hypotheses and restored-scratch convention of `C7PackedXorStmt`, with effect
`arrSyms (permByInv (g K ρ f N1 N2 N3) v)` on stack `0` and cost `C · c7Cost τ K f M V R`.
`C7PackedXorStmt τ σ` is the premise `s_b/W_b < m^τ` followed by this statement for
`g = packedXorAddr` (`AppC.C7Aux.c7PackedXor_iff`). -/
def C7PhaseStmt (τ : ℝ) (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  KContract (Fin 8) Unit fun _ E _ _ _ C P =>
    ∀ (K ρ f N0 N1 N2 N3 R : ℕ) (v : List (List Bool)) (rest r1 r2 r3 r4 r5 r6 r7 : List Sym)
      (S : KLoc (Fin 8) E → List Sym),
      6 ≤ K → ρ < K → 1 ≤ f → 1 ≤ N0 → 1 ≤ N1 → 1 ≤ N2 → 1 ≤ N3 → 1 ≤ R →
      v.length = N0 * 2 ^ (f * K) * N1 * 2 ^ (f * K) * N2 * 2 ^ (f * K) * N3 →
      (∀ p ∈ v, p.length = R) →
      BlkTerm rest → TermOK r1 → TermOK r2 → TermOK r3 → TermOK r4 → TermOK r5 →
      TermOK r6 → TermOK r7 →
      S (.inl 0) = arrSyms v ++ rest → S (.inl 1) = natSyms K ++ r1 →
      S (.inl 2) = natSyms ρ ++ r2 → S (.inl 3) = natSyms f ++ r3 →
      S (.inl 4) = natSyms N1 ++ r4 → S (.inl 5) = natSyms N2 ++ r5 →
      S (.inl 6) = natSyms N3 ++ r6 → S (.inl 7) = natSyms R ++ r7 →
      Runs P S
        (Function.update S (.inl 0) (arrSyms (permByInv (g K ρ f N1 N2 N3) v) ++ rest))
        (fun _ => True) (C * c7Cost τ K f v.length (vol v) R)

/-- `C7PackedXorStmt` is the phase contract for `packedXorAddr` (definitional). -/
theorem AppC.C7Aux.c7PackedXor_iff (τ : ℝ) (σ : Equiv.Perm (Fin 3)) :
    C7PackedXorStmt τ σ ↔ ((tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ →
      C7PhaseStmt τ (fun K ρ f N1 N2 N3 => packedXorAddr (f * K) K ρ f N1 N2 N3 σ)) :=
  Iff.rfl

/-- **[CONTRACT] Lemma A.9 phase 1: the eight packed lines** (Lemma A.9
(`lem:transfer13`)). Index map `c7LinesInv` (the inverse of the composite push map `packedS0`). Under the
premise of `C7PackedXorStmt` (needed by the Lemma A.8 exchanges). -/
def C7LinesStmt (τ : ℝ) (σ : Equiv.Perm (Fin 3)) : Prop :=
  (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ →
    C7PhaseStmt τ (fun K ρ f N1 N2 N3 => c7LinesInv K ρ f N1 N2 N3 σ)

/-- **[CONTRACT] Lemma A.9 phase 2: repair** (Lemma A.9 (`lem:transfer13`): extraction with
destination keys, stable radix sort, reinsertion). Index map `c7RepairInv`. -/
def C7RepairStmt (τ : ℝ) (σ : Equiv.Perm (Fin 3)) : Prop :=
  (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ →
    C7PhaseStmt τ (fun K ρ f N1 N2 N3 => c7RepairInv K ρ f N1 N2 N3 σ)

/-- **[CONTRACT] Lemma A.9 phase 3: the omitted top selected bit** (Lemma A.9
(`lem:transfer13`)). Index map `c7TopInv`. -/
def C7TopStmt (τ : ℝ) (σ : Equiv.Perm (Fin 3)) : Prop :=
  (tripleSb 100 : ℝ) / tripleWb 100 < (tripleM 100 : ℝ) ^ τ →
    C7PhaseStmt τ (fun K ρ f N1 N2 N3 => c7TopInv K ρ f N1 N2 N3 σ)

/-- **[MATH] Lemma A.9 address identity.** For valid parameters and every record index
`p < M`: the three phase maps keep indices below `M`, and
`c7LinesInv (c7RepairInv (c7TopInv p)) = packedXorAddr (fK) K ρ f N1 N2 N3 σ p`. -/
def C7AddrStmt (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ K ρ f N0 N1 N2 N3 : ℕ, 6 ≤ K → ρ < K → 1 ≤ f → 1 ≤ N0 → 1 ≤ N1 → 1 ≤ N2 → 1 ≤ N3 →
    ∀ p, p < c7M K f N0 N1 N2 N3 →
      c7LinesInv K ρ f N1 N2 N3 σ p < c7M K f N0 N1 N2 N3 ∧
      c7RepairInv K ρ f N1 N2 N3 σ p < c7M K f N0 N1 N2 N3 ∧
      c7TopInv K ρ f N1 N2 N3 σ p < c7M K f N0 N1 N2 N3 ∧
      c7LinesInv K ρ f N1 N2 N3 σ (c7RepairInv K ρ f N1 N2 N3 σ (c7TopInv K ρ f N1 N2 N3 σ p)) =
        packedXorAddr (f * K) K ρ f N1 N2 N3 σ p


/-! ## Composition of the three phases -/

/-- **Three phases compose** (`c7Phase_comp`, 0 `sorry`). If, for valid parameters, the index maps
keep indices below `M` and `g₁ (g₂ (g₃ p)) = g p` for `p < M`, then running the three phase kernels
in sequence (`callInj` on disjoint private scratch `E₁ ⊕ E₂ ⊕ E₃`, registers `R₁ × R₂ × R₃`) is a
phase kernel for `g`, with cost constant `C₁ + C₂ + C₃` (every phase costs at most its constant
times `c7Cost` of its input, and all three inputs have the same length and volume). -/
theorem AppC.C7Aux.c7Phase_comp {τ : ℝ} {g₁ g₂ g₃ g : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hg : ∀ K ρ f N0 N1 N2 N3 : ℕ, 6 ≤ K → ρ < K → 1 ≤ f → 1 ≤ N0 → 1 ≤ N1 → 1 ≤ N2 → 1 ≤ N3 →
      ∀ p, p < c7M K f N0 N1 N2 N3 →
        g₁ K ρ f N1 N2 N3 p < c7M K f N0 N1 N2 N3 ∧ g₂ K ρ f N1 N2 N3 p < c7M K f N0 N1 N2 N3 ∧
        g₃ K ρ f N1 N2 N3 p < c7M K f N0 N1 N2 N3 ∧
        g₁ K ρ f N1 N2 N3 (g₂ K ρ f N1 N2 N3 (g₃ K ρ f N1 N2 N3 p)) = g K ρ f N1 N2 N3 p)
    (h₁ : C7PhaseStmt τ g₁) (h₂ : C7PhaseStmt τ g₂) (h₃ : C7PhaseStmt τ g₃) :
    C7PhaseStmt τ g := by
  obtain ⟨C₁, hc₁⟩ := h₁
  obtain ⟨C₂, hc₂⟩ := h₂
  obtain ⟨C₃, hc₃⟩ := h₃
  refine ⟨C₁ + C₂ + C₃, fun _ => ?_⟩
  obtain ⟨E₁, _, _, R₁, P₁, hf₁, hn₁, hcl₁, hs₁⟩ := hc₁ ()
  obtain ⟨E₂, _, _, R₂, P₂, hf₂, hn₂, hcl₂, hs₂⟩ := hc₂ ()
  obtain ⟨E₃, _, _, R₃, P₃, hf₃, hn₃, hcl₃, hs₃⟩ := hc₃ ()
  have hι₁ : Function.Injective
      (Sum.map id Sum.inl : KLoc (Fin 8) E₁ → KLoc (Fin 8) (E₁ ⊕ E₂ ⊕ E₃)) :=
    Function.injective_id.sumMap Sum.inl_injective
  have hι₂ : Function.Injective
      (Sum.map id (Sum.inr ∘ Sum.inl) : KLoc (Fin 8) E₂ → KLoc (Fin 8) (E₁ ⊕ E₂ ⊕ E₃)) :=
    Function.injective_id.sumMap (Sum.inr_injective.comp Sum.inl_injective)
  have hι₃ : Function.Injective
      (Sum.map id (Sum.inr ∘ Sum.inr) : KLoc (Fin 8) E₃ → KLoc (Fin 8) (E₁ ⊕ E₂ ⊕ E₃)) :=
    Function.injective_id.sumMap (Sum.inr_injective.comp Sum.inr_injective)
  refine ⟨E₁ ⊕ E₂ ⊕ E₃, inferInstance, inferInstance, R₁ × R₂ × R₃,
    .seq (callInj (Sum.map id Sum.inl) (Lens.fst R₁ (R₂ × R₃)) P₁)
      (.seq (callInj (Sum.map id (Sum.inr ∘ Sum.inl))
          ((Lens.snd R₁ (R₂ × R₃)).comp (Lens.fst R₂ R₃)) P₂)
        (callInj (Sum.map id (Sum.inr ∘ Sum.inr))
          ((Lens.snd R₁ (R₂ × R₃)).comp (Lens.snd R₂ R₃)) P₃)),
    inferInstance, inferInstance,
    ⟨closed_callInj _ _ hcl₁, closed_callInj _ _ hcl₂, closed_callInj _ _ hcl₃⟩, ?_⟩
  intro K ρ f N0 N1 N2 N3 R v rest r1 r2 r3 r4 r5 r6 r7 S hK hρ hf hN0 hN1 hN2 hN3 hR hlen hrec
    hrest hr1 hr2 hr3 hr4 hr5 hr6 hr7 hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS7
  have hgv := hg K ρ f N0 N1 N2 N3 hK hρ hf hN0 hN1 hN2 hN3
  have hlen' : v.length = c7M K f N0 N1 N2 N3 := hlen
  -- the intermediate arrays
  obtain ⟨w₁, hw₁⟩ : ∃ w, permByInv (g₁ K ρ f N1 N2 N3) v = w := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w, permByInv (g₂ K ρ f N1 N2 N3) w₁ = w := ⟨_, rfl⟩
  obtain ⟨w₃, hw₃⟩ : ∃ w, permByInv (g₃ K ρ f N1 N2 N3) w₂ = w := ⟨_, rfl⟩
  have hl₁ : w₁.length = v.length := by rw [← hw₁, permByInv_length]
  have hl₂ : w₂.length = v.length := by rw [← hw₂, permByInv_length, hl₁]
  have hin₁ : ∀ y < v.length, g₁ K ρ f N1 N2 N3 y < v.length := fun y hy => by
    rw [hlen'] at hy ⊢; exact (hgv y hy).1
  have hin₂ : ∀ y < w₁.length, g₂ K ρ f N1 N2 N3 y < w₁.length := fun y hy => by
    rw [hl₁, hlen'] at hy ⊢; exact (hgv y hy).2.1
  have hin₃ : ∀ y < w₂.length, g₃ K ρ f N1 N2 N3 y < w₂.length := fun y hy => by
    rw [hl₂, hlen'] at hy ⊢; exact (hgv y hy).2.2.1
  have hrec₁ : ∀ p ∈ w₁, p.length = R := fun p hp => hrec p (permByInv_mem hin₁ (hw₁ ▸ hp))
  have hrec₂ : ∀ p ∈ w₂, p.length = R := fun p hp => hrec₁ p (permByInv_mem hin₂ (hw₂ ▸ hp))
  have hvol₁ : vol w₁ = vol v := by rw [vol_of_len hrec₁, vol_of_len hrec, hl₁]
  have hvol₂ : vol w₂ = vol v := by rw [vol_of_len hrec₂, vol_of_len hrec, hl₂]
  have hw : w₃ = permByInv (g K ρ f N1 N2 N3) v := by
    have hin₃' : ∀ y < w₁.length, g₃ K ρ f N1 N2 N3 y < w₁.length := fun y hy => by
      rw [hl₁, hlen'] at hy ⊢; exact (hgv y hy).2.2.1
    rw [← hw₃, ← hw₂, permByInv_permByInv hin₃', ← hw₁, permByInv_permByInv]
    · apply permByInv_congr
      intro y hy
      rw [hlen'] at hy
      exact (hgv y hy).2.2.2
    · intro y hy
      have hy' := hy
      rw [hlen'] at hy'
      rw [hlen']
      exact (hgv _ (hgv y hy').2.2.1).2.1
  -- phase 1
  have e₁ := hs₁ K ρ f N0 N1 N2 N3 R v rest r1 r2 r3 r4 r5 r6 r7 (S ∘ Sum.map id Sum.inl) hK hρ hf
    hN0 hN1 hN2 hN3 hR hlen hrec hrest hr1 hr2 hr3 hr4 hr5 hr6 hr7 hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS7
  rw [hw₁] at e₁
  have X₁ : Runs (callInj (Sum.map id Sum.inl) (Lens.fst R₁ (R₂ × R₃)) P₁) S
      (Function.update S (.inl 0) (arrSyms w₁ ++ rest)) (fun _ => True)
      (C₁ * c7Cost τ K f v.length (vol v) R) := by
    refine runs_callInj hι₁ _ (Q := fun _ => True) ?_ ?_
    · have hc : Function.update S (.inl 0) (arrSyms w₁ ++ rest) ∘
          (Sum.map id Sum.inl : KLoc (Fin 8) E₁ → KLoc (Fin 8) (E₁ ⊕ E₂ ⊕ E₃)) =
          Function.update (S ∘ Sum.map id Sum.inl) (.inl 0) (arrSyms w₁ ++ rest) :=
        Function.update_comp_eq_of_injective S hι₁ (.inl 0) _
      rw [hc]
      exact e₁
    · intro k hk
      exact Function.update_of_ne (fun h => hk (.inl 0) h.symm) _ _
  -- phase 2
  have hS₁ : ∀ i : Fin 8, i ≠ 0 →
      Function.update S (.inl 0) (arrSyms w₁ ++ rest) (.inl i) = S (.inl i) :=
    fun i hi => Function.update_of_ne (by simpa using hi) _ _
  have e₂ := hs₂ K ρ f N0 N1 N2 N3 R w₁ rest r1 r2 r3 r4 r5 r6 r7
    (Function.update S (.inl 0) (arrSyms w₁ ++ rest) ∘ Sum.map id (Sum.inr ∘ Sum.inl)) hK hρ hf
    hN0 hN1 hN2 hN3 hR (hl₁.trans hlen) hrec₁ hrest hr1 hr2 hr3 hr4 hr5 hr6 hr7 (by simp)
    ((hS₁ 1 (by decide)).trans hS1) ((hS₁ 2 (by decide)).trans hS2)
    ((hS₁ 3 (by decide)).trans hS3) ((hS₁ 4 (by decide)).trans hS4)
    ((hS₁ 5 (by decide)).trans hS5) ((hS₁ 6 (by decide)).trans hS6)
    ((hS₁ 7 (by decide)).trans hS7)
  rw [hw₂, hl₁, hvol₁] at e₂
  have X₂ : Runs (callInj (Sum.map id (Sum.inr ∘ Sum.inl))
        ((Lens.snd R₁ (R₂ × R₃)).comp (Lens.fst R₂ R₃)) P₂)
      (Function.update S (.inl 0) (arrSyms w₁ ++ rest))
      (Function.update (Function.update S (.inl 0) (arrSyms w₁ ++ rest)) (.inl 0)
        (arrSyms w₂ ++ rest)) (fun _ => True) (C₂ * c7Cost τ K f v.length (vol v) R) := by
    refine runs_callInj hι₂ _ (Q := fun _ => True) ?_ ?_
    · have hc : Function.update (Function.update S (.inl 0) (arrSyms w₁ ++ rest)) (.inl 0)
            (arrSyms w₂ ++ rest) ∘
          (Sum.map id (Sum.inr ∘ Sum.inl) : KLoc (Fin 8) E₂ → KLoc (Fin 8) (E₁ ⊕ E₂ ⊕ E₃)) =
          Function.update (Function.update S (.inl 0) (arrSyms w₁ ++ rest) ∘
            Sum.map id (Sum.inr ∘ Sum.inl)) (.inl 0) (arrSyms w₂ ++ rest) :=
        Function.update_comp_eq_of_injective _ hι₂ (.inl 0) _
      rw [hc]
      exact e₂
    · intro k hk
      exact Function.update_of_ne (fun h => hk (.inl 0) h.symm) _ _
  -- phase 3
  have hS₂ : ∀ i : Fin 8, i ≠ 0 →
      Function.update (Function.update S (.inl 0) (arrSyms w₁ ++ rest)) (.inl 0)
        (arrSyms w₂ ++ rest) (.inl i) = S (.inl i) :=
    fun i hi => (Function.update_of_ne (by simpa using hi) _ _).trans (hS₁ i hi)
  have e₃ := hs₃ K ρ f N0 N1 N2 N3 R w₂ rest r1 r2 r3 r4 r5 r6 r7
    (Function.update (Function.update S (.inl 0) (arrSyms w₁ ++ rest)) (.inl 0)
      (arrSyms w₂ ++ rest) ∘ Sum.map id (Sum.inr ∘ Sum.inr)) hK hρ hf
    hN0 hN1 hN2 hN3 hR (hl₂.trans hlen) hrec₂ hrest hr1 hr2 hr3 hr4 hr5 hr6 hr7 (by simp)
    ((hS₂ 1 (by decide)).trans hS1) ((hS₂ 2 (by decide)).trans hS2)
    ((hS₂ 3 (by decide)).trans hS3) ((hS₂ 4 (by decide)).trans hS4)
    ((hS₂ 5 (by decide)).trans hS5) ((hS₂ 6 (by decide)).trans hS6)
    ((hS₂ 7 (by decide)).trans hS7)
  rw [hw₃, hl₂, hvol₂] at e₃
  have X₃ : Runs (callInj (Sum.map id (Sum.inr ∘ Sum.inr))
        ((Lens.snd R₁ (R₂ × R₃)).comp (Lens.snd R₂ R₃)) P₃)
      (Function.update (Function.update S (.inl 0) (arrSyms w₁ ++ rest)) (.inl 0)
        (arrSyms w₂ ++ rest))
      (Function.update (Function.update (Function.update S (.inl 0) (arrSyms w₁ ++ rest)) (.inl 0)
        (arrSyms w₂ ++ rest)) (.inl 0) (arrSyms w₃ ++ rest))
      (fun _ => True) (C₃ * c7Cost τ K f v.length (vol v) R) := by
    refine runs_callInj hι₃ _ (Q := fun _ => True) ?_ ?_
    · have hc : Function.update (Function.update (Function.update S (.inl 0) (arrSyms w₁ ++ rest))
            (.inl 0) (arrSyms w₂ ++ rest)) (.inl 0) (arrSyms w₃ ++ rest) ∘
          (Sum.map id (Sum.inr ∘ Sum.inr) : KLoc (Fin 8) E₃ → KLoc (Fin 8) (E₁ ⊕ E₂ ⊕ E₃)) =
          Function.update (Function.update (Function.update S (.inl 0) (arrSyms w₁ ++ rest))
            (.inl 0) (arrSyms w₂ ++ rest) ∘ Sum.map id (Sum.inr ∘ Sum.inr)) (.inl 0)
            (arrSyms w₃ ++ rest) :=
        Function.update_comp_eq_of_injective _ hι₃ (.inl 0) _
      rw [hc]
      exact e₃
    · intro k hk
      exact Function.update_of_ne (fun h => hk (.inl 0) h.symm) _ _
  -- sequence
  have X := Calculus.RunsIn.seq (Calculus.RunsIn.iff_runs.mpr X₁)
    (Calculus.RunsIn.seq (Calculus.RunsIn.iff_runs.mpr X₂) (Calculus.RunsIn.iff_runs.mpr X₃))
  refine Calculus.RunsIn.iff_runs.mp (Calculus.RunsIn.congr X ?_ (le_of_eq (by ring)))
  rw [Function.update_idem, Function.update_idem, hw]

/-! ## The reduction -/

/-- **Lemma A.9 from its three phases** (`c7PackedXor_of_parts`, 0 `sorry`): the address identity and
the three phase contracts give `C7PackedXorStmt τ σ`. The program runs lines, repair and top bit in
sequence; the cost constant is the sum of the three phase constants. -/
theorem c7PackedXor_of_parts (τ : ℝ) (σ : Equiv.Perm (Fin 3)) (hA : C7AddrStmt σ)
    (hL : C7LinesStmt τ σ) (hR : C7RepairStmt τ σ) (hT : C7TopStmt τ σ) :
    C7PackedXorStmt τ σ := by
  intro hprem
  exact c7Phase_comp (g := fun K ρ f N1 N2 N3 => packedXorAddr (f * K) K ρ f N1 N2 N3 σ) hA
    (hL hprem) (hR hprem) (hT hprem)

end SubNLogN.Machine
