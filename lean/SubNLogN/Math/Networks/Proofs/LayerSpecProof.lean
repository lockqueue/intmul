import SubNLogN.Math.Networks.AppCLayerProc
import SubNLogN.Math.Networks.Proofs.CDon
import SubNLogN.Math.Networks.Proofs.LayerSpecPad

/-!
# Proposition A.11 (`prop:prop14-param`), functional part: the explicit layer procedure satisfies `LayerSpec`

`Prop71LayerSpecStmt` (`AppCLayerProc.lean`): for valid complex edge data, `K ≥ 6` and
`1 ≤ D ≤ d`, the decoded run `layerRun P A K D S rr ρ d cdat` returns exactly `Q_P(H z)` on every
disk-grid input (`LayerSpec`). Paper: Proposition A.11 (`prop:prop14-param`),
Appendix A.6 (`sec:transfer-layer`). Main theorem: `prop71LayerSpec_holds : Prop71LayerSpecStmt`.

Proof. `selOp ρ T w` is `C` applied on the selected bits in `T` (through `CDon`, `Proofs/CDon.lean`):
`selOp` of disjoint sets compose to the union (`selOp_selOp`), `selOp ∅ = id`, `selOp univ = C^{⊗D}`
(`selOp_univ`), and `cCoreVal` on a group of consecutive chunks is `selOp` of that group
(`cd_group_eq_cdon`, `cCoreVal_eq_selOp`).
* Phase 1 (`LayerSpecPadAux.phase1_eq`): `𝒮_D`, then the individual kernels on the first
  `min q₀ D` chunks, each of which is `selOp` of one bit (`kernel_step`, `kernels_run`).
* Phase 2 (only if `q₀ < D`): each C-core piece is `selOp` of its group by `CCoreProcCorrectStmt`
  (`piece_run`); the base-`m` pieces tile `[0, D − q₀)` (`pieces_run`), so phase 2 is
  `C^{⊗(D−q₀)}` on the reshaped layout (`phase2_run`). Every piece has depth `≤ k₀ = ⌈log_m d⌉`,
  so its role splits are complete (`wc_pow_dvd`, `padR_ge`). Through the row reshape (padded rows
  are never read, `LayerSpecPadAux.embedArr_mergeL`) this is `selOp` of the chunks `q₀, …, D−1` of
  the original array (`transfer`).
* Phase 3 (`LayerSpecPadAux.phase3_decode`): `𝒮_D`, `b^D`, `Q_P`.
Hence `layerRun z = Q_P(b^D 𝒮_D C^{⊗D} 𝒮_D z)` for every array `z`, and `Prop71FunctionalStmt`
gives `LayerSpec`. The hypotheses `H0TensorIdentityStmt` and `1 ≤ D` are not needed: the proof is
`LayerSpecAux.layerSpec_strong`, which omits them (re-exported in `LayerSpecCover.lean`). The
encoding/padding lemmas are in `Proofs/LayerSpecPad.lean` (namespace
`LayerSpecPadAux`); the helpers of this file live in `SubNLogN.Math.Networks.LayerSpecAux`.
-/

namespace SubNLogN.Math.Networks
namespace LayerSpecAux
open Model SubNLogN.Math.Walsh SubNLogN.Math.Common

/-! ## Selected bits and `C` on a set of selected bits -/

/-- The selected bits (bit `ρ` of every chunk) of a layer address. -/
def selBits {A K D S : ℕ} (ρ : Fin K) (x : LayerAddr A K D S) : Fin D → Bool := fun j => x.2.1 j ρ

theorem setSelBits_setSelBits {A K D S : ℕ} (ρ : Fin K) (x : LayerAddr A K D S)
    (e e' : Fin D → Bool) : setSelBits ρ (setSelBits ρ x e) e' = setSelBits ρ x e' := by
  simp [setSelBits]

theorem selBits_setSelBits {A K D S : ℕ} (ρ : Fin K) (x : LayerAddr A K D S) (e : Fin D → Bool) :
    selBits ρ (setSelBits ρ x e) = e := by
  funext j; simp [selBits, setSelBits]

theorem setSelBits_selBits {A K D S : ℕ} (ρ : Fin K) (x : LayerAddr A K D S) :
    setSelBits ρ x (selBits ρ x) = x := by
  rcases x with ⟨a, c, s⟩
  simp [setSelBits, selBits]

/-- `C` on the selected bits in `T` (identity on the other selected bits). -/
noncomputable def selOp {A K D S r : ℕ} (ρ : Fin K) (T : Finset (Fin D))
    (w : RArr (LayerAddr A K D S) r) : RArr (LayerAddr A K D S) r :=
  fun x k => CDon T (fun e => w (setSelBits ρ x e) k) (selBits ρ x)

theorem selOp_selOp {A K D S r : ℕ} (ρ : Fin K) {T T' : Finset (Fin D)} (h : Disjoint T T')
    (w : RArr (LayerAddr A K D S) r) : selOp ρ T (selOp ρ T' w) = selOp ρ (T ∪ T') w := by
  funext x k
  simp only [selOp, setSelBits_setSelBits, selBits_setSelBits]
  exact congrFun (cdon_holds.2.2.1 D T T' (fun e => w (setSelBits ρ x e) k) h) (selBits ρ x)

theorem selOp_empty {A K D S r : ℕ} (ρ : Fin K) (w : RArr (LayerAddr A K D S) r) :
    selOp ρ (∅ : Finset (Fin D)) w = w := by
  funext x k
  simp only [selOp]
  rw [cdon_holds.2.1 D]
  simp only [setSelBits_selBits]

theorem selOp_univ {A K D S r : ℕ} (ρ : Fin K) (w : RArr (LayerAddr A K D S) r) :
    selOp ρ (Finset.univ : Finset (Fin D)) w =
      fun x k => CD D (fun e => w (setSelBits ρ x e) k) (selBits ρ x) := by
  funext x k
  simp only [selOp]
  rw [cdon_holds.1 D]

/-! ## A group of consecutive selected bits -/

/-- The positions `j0 ≤ j < j1`. -/
def iv {D : ℕ} (j0 j1 : ℕ) : Finset (Fin D) := Finset.univ.filter fun j => j0 ≤ j.val ∧ j.val < j1

/-- Insert the bits `bs` at the positions `j0, …, j0+e−1` of `e₀`. -/
def insGroup {D : ℕ} (j0 e : ℕ) (e₀ : Fin D → Bool) (bs : Fin e → Bool) : Fin D → Bool :=
  fun j => if h : j0 ≤ j.val ∧ j.val < j0 + e then bs ⟨j.val - j0, by omega⟩ else e₀ j

theorem insGroup_injective {D : ℕ} (j0 e : ℕ) (h : j0 + e ≤ D) (e₀ : Fin D → Bool) :
    Function.Injective (insGroup j0 e e₀) := by
  intro bs bs' hb
  funext i
  have := congrFun hb ⟨j0 + i.val, by omega⟩
  simp only [insGroup] at this
  rw [dif_pos (by omega), dif_pos (by omega)] at this
  have hi : (⟨j0 + i.val - j0, by omega⟩ : Fin e) = i := Fin.ext (by simp)
  rwa [hi] at this

/-- **Group lemma**: `C^{⊗e}` on a group of `e` consecutive selected bits is `CDon` of the group. -/
theorem cd_group_eq_cdon {D : ℕ} (j0 e : ℕ) (h : j0 + e ≤ D) (g : (Fin D → Bool) → ℂ)
    (e₀ : Fin D → Bool) :
    CD e (fun bs => g (insGroup j0 e e₀ bs)) (fun i => e₀ ⟨j0 + i.val, by omega⟩) =
      CDon (iv j0 (j0 + e)) g e₀ := by
  classical
  simp only [CDon, CD]
  -- restrict the `CDon` sum to the image of `insGroup`
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (insGroup j0 e e₀)))]
  · rw [Finset.sum_image (fun bs _ bs' _ hb => insGroup_injective j0 e h e₀ hb)]
    refine Finset.sum_congr rfl fun bs _ => ?_
    rw [if_pos]
    · congr 1
      refine (Finset.prod_bij' (fun i _ => (⟨j0 + i.val, by omega⟩ : Fin D))
        (fun j hj => (⟨j.val - j0, by simp [iv] at hj; omega⟩ : Fin e)) ?_ ?_ ?_ ?_ ?_)
      · intro i _; simp [iv]
      · intro j _; simp
      · intro i _; apply Fin.ext; simp
      · intro j hj; apply Fin.ext; simp [iv] at hj; simp; omega
      · intro i _
        simp only [insGroup]
        rw [dif_pos (by simp)]
        have hi : (⟨j0 + i.val - j0, by omega⟩ : Fin e) = i := Fin.ext (by simp)
        simp only [hi]
    · intro j hj
      simp only [iv, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [insGroup]
      rw [dif_neg hj]
  · intro e' _ he'
    rw [if_neg, zero_mul]
    intro hagree
    apply he'
    refine Finset.mem_image.2 ⟨fun i => e' ⟨j0 + i.val, by omega⟩, Finset.mem_univ _, ?_⟩
    funext j
    simp only [insGroup]
    split_ifs with hj
    · congr 1; apply Fin.ext; simp; omega
    · exact hagree j (by simp [iv]; omega)

/-- `setSelBits` with a group inserted into the current selected bits is `groupSel`. -/
theorem setSelBits_insGroup {A K D S : ℕ} (ρ : Fin K) (j0 e : ℕ) (x : LayerAddr A K D S)
    (bs : Fin e → Bool) :
    setSelBits ρ x (insGroup j0 e (selBits ρ x) bs) = groupSel ρ j0 e x bs := by
  rcases x with ⟨a, c, s⟩
  simp only [setSelBits, groupSel, insGroup, selBits]
  congr 1; congr 1
  funext j
  split_ifs with hj
  · rfl
  · exact Function.update_eq_self ρ (c j)

/-- `cCoreVal` is `C` on the selected bits of its group. -/
theorem cCoreVal_eq_selOp {A K D S r : ℕ} (ρ : Fin K) (j0 e : ℕ) (h : j0 + e ≤ D)
    (z : RArr (LayerAddr A K D S) r) : cCoreVal ρ j0 e h z = selOp ρ (iv j0 (j0 + e)) z := by
  funext x k
  simp only [cCoreVal, selOp]
  rw [← cd_group_eq_cdon j0 e h]
  simp only [setSelBits_insGroup]
  rfl


end LayerSpecAux


namespace LayerSpecAux
open Model SubNLogN.Math.Walsh SubNLogN.Math.Common
open LayerSpecPadAux (encodeArr_decodeArr runIn_topClass phase3_decode phase1_eq mergeL mergeL_chunk
  mergeL_suffix mergeL_prefix embedArr_mergeL)

/-! ## Individual kernels (phase 1) -/

theorem divModAux {K j t : ℕ} (ht : t < K) :
    (1 + j * K + (K - 1 - t) - 1) / K = j ∧ K - 1 - (1 + j * K + (K - 1 - t) - 1) % K = t := by
  have h1 : 1 + j * K + (K - 1 - t) - 1 = (K - 1 - t) + j * K := by omega
  have hK : 0 < K := by omega
  rw [h1, Nat.add_mul_div_right _ _ hK, Nat.add_mul_mod_self_right,
    Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem field_le {K D j t : ℕ} (hj : j < D) (ht : t < K) : 1 + j * K + (K - 1 - t) ≤ D * K := by
  have : j * K + K ≤ D * K := by nlinarith
  omega

theorem decodeArr_encodeArr (hDE : DecodeEncodeAddrStmt) {A K D S rr : ℕ}
    (w : RArr (LayerAddr A K D S) rr) : decodeArr (encodeArr w) = w := by
  funext x
  show w (decodeAddr (encodeAddr x)) = w x
  rw [hDE]

/-- Value of the field of bit `t` of chunk `j`. -/
theorem encodeAddr_chunk {A K D S : ℕ} (x : LayerAddr A K D S) (j : Fin D) (t : Fin K)
    (hi : 1 + j.val * K + (K - 1 - t.val) < (layerLayout A K D S).n) :
    (encodeAddr x ⟨1 + j.val * K + (K - 1 - t.val), hi⟩).val = if x.2.1 j t then 1 else 0 := by
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) t.isLt
  obtain ⟨e1, e2⟩ := divModAux (K := K) (j := j.val) t.isLt
  have h1 := field_le j.isLt t.isLt
  simp [encodeAddr, h1, hK, e1, e2]

theorem selField_lt {A K D S : ℕ} (ρ : Fin K) (j : Fin D) :
    selField K ρ.val j.val < (layerLayout A K D S).n := by
  have := field_le j.isLt ρ.isLt
  simp only [selField, layerLayout]; omega

/-- Overwriting the selected-bit field of chunk `j` by `v`, then decoding. -/
theorem decodeAddr_update_sel {A K D S : ℕ} (ρ : Fin K) (j : Fin D) (x : LayerAddr A K D S)
    (v : Fin ((layerLayout A K D S).r ⟨selField K ρ.val j.val, selField_lt ρ j⟩)) :
    decodeAddr (Function.update (encodeAddr x) ⟨selField K ρ.val j.val, selField_lt ρ j⟩ v) =
      setSelBits ρ x (Function.update (selBits ρ x) j (decide (v.val = 1))) := by
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) ρ.isLt
  have hsel := field_le j.isLt ρ.isLt
  rcases x with ⟨a, c, s⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Fin.ext
    simp only [decodeAddr, setSelBits]
    rw [Function.update_of_ne (by
      intro h; have := congrArg Fin.val h; simp only [selField] at this; omega)]
    simp [encodeAddr]
  · funext j' t'
    simp only [decodeAddr, setSelBits]
    by_cases hjt : j' = j ∧ t' = ρ
    · obtain ⟨rfl, rfl⟩ := hjt
      erw [Function.update_self]
      simp
    · have hne : (⟨1 + j'.val * K + (K - 1 - t'.val), by
          have := field_le j'.isLt t'.isLt; simp only [layerLayout]; omega⟩ :
            Fin (layerLayout A K D S).n) ≠ ⟨selField K ρ.val j.val, selField_lt ρ j⟩ := by
        intro h
        apply hjt
        have h' := congrArg Fin.val h
        simp only [selField] at h'
        obtain ⟨a1, a2⟩ := divModAux (K := K) (j := j'.val) t'.isLt
        obtain ⟨b1, b2⟩ := divModAux (K := K) (j := j.val) ρ.isLt
        rw [h'] at a1 a2
        exact ⟨Fin.ext (a1.symm.trans b1), Fin.ext (a2.symm.trans b2)⟩
      rw [Function.update_of_ne hne, encodeAddr_chunk]
      by_cases ht : t' = ρ
      · subst ht
        have hj : j' ≠ j := fun h => hjt ⟨h, rfl⟩
        simp [Function.update_of_ne hj, selBits]
      · simp [Function.update_of_ne ht]
  · apply Fin.ext
    simp only [decodeAddr, setSelBits]
    rw [Function.update_of_ne (by
      intro h; have := congrArg Fin.val h; simp only [selField] at this; omega)]
    have h1 : ¬ (D * K + 1 ≤ D * K) := by omega
    simp [encodeAddr, h1]

/-- `cGate` on a binary field. -/
theorem cGate_two {n rr : ℕ} (hn : n = 2) (v : Fin n → (Fin rr → ℂ)) (t : Fin n) :
    cGate v t = ka • v t + kb • v ⟨1 - t.val, by have := t.isLt; omega⟩ := by
  subst hn
  simp only [cGate]
  congr 2
  have hs : Finset.univ.erase t = {(⟨1 - t.val, by have := t.isLt; omega⟩ : Fin 2)} := by
    ext s
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_singleton, ne_eq]
    constructor
    · intro hs
      apply Fin.ext
      have h1 := s.isLt
      have h2 := t.isLt
      have h3 : s.val ≠ t.val := fun h => hs (Fin.ext h)
      simp only
      omega
    · intro hs h
      subst hs
      have := congrArg Fin.val h
      simp only at this
      have := t.isLt
      omega
  rw [hs, Finset.sum_singleton]


/-! ## Intervals of chunks -/

theorem iv_self {D : ℕ} (a : ℕ) : (iv a a : Finset (Fin D)) = ∅ := by
  ext j; simp only [iv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, not_and, not_lt]; omega

theorem iv_union {D : ℕ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (iv b c ∪ iv a b : Finset (Fin D)) = iv a c := by
  ext j; simp only [iv, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega

theorem iv_disjoint {D : ℕ} (a b c : ℕ) : Disjoint (iv b c : Finset (Fin D)) (iv a b) := by
  rw [Finset.disjoint_left]
  intro j h1 h2
  simp only [iv, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  omega

theorem iv_univ {D : ℕ} : (iv 0 D : Finset (Fin D)) = Finset.univ := by
  ext j; simp [iv]

theorem iv_single {D : ℕ} (n : ℕ) (hn : n < D) : (iv n (n + 1) : Finset (Fin D)) = {⟨n, hn⟩} := by
  ext j; simp only [iv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Fin.ext_iff]; omega

/-! ## Phase 1: individual kernels -/

theorem run0_append {L : Layout} {β : Type} (c : RowClass L) (l₁ l₂ : List (Step L β))
    (B : L.Addr → β) : ProcK.run 0 (l₁ ++ l₂) c B = ProcK.run 0 l₂ c (ProcK.run 0 l₁ c B) := by
  simp only [ProcK.run, List.foldl_append]

theorem encodeAddr_sel {A K D S : ℕ} (x : LayerAddr A K D S) (j : ℕ) (hj : j < D) (ρ : Fin K)
    (hi : selField K ρ.val j < (layerLayout A K D S).n) :
    (encodeAddr x ⟨selField K ρ.val j, hi⟩).val = if x.2.1 ⟨j, hj⟩ ρ then 1 else 0 :=
  encodeAddr_chunk x ⟨j, hj⟩ ρ hi

/-- One individual kernel on the selected bit of chunk `j` is `C` on that bit. -/
theorem kernel_step {A K D S rr : ℕ} (ρ : Fin K) (j : ℕ) (hj : j < D)
    (y : RArr (LayerAddr A K D S) rr) :
    ProcK.run 0 (dgate (A := A) (K := K) (D := D) (S := S) (rr := rr) (selField K ρ.val j))
      (topClass A K D S) (encodeArr y) = encodeArr (selOp ρ (iv j (j + 1)) y) := by
  rw [← encodeArr_decodeArr (ProcK.run 0 (dgate (A := A) (K := K) (D := D) (S := S) (rr := rr)
    (selField K ρ.val j)) (topClass A K D S) (encodeArr y)), iv_single j hj]
  congr 1
  funext x k
  have hi := selField_lt (A := A) (S := S) ρ ⟨j, hj⟩
  simp only [ProcK.run, dgate, dif_pos hi, List.foldl_cons, List.foldl_nil, runIn_topClass,
    Step.run, decodeArr]
  have hn : (layerLayout A K D S).r ⟨selField K ρ.val j, hi⟩ = 2 := by
    have := field_le hj ρ.isLt
    simp only [layerLayout, selField]
    rw [if_neg (by omega), if_pos this]
  rw [cGate_two hn]
  simp only [encodeArr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [decodeAddr_update_sel ρ ⟨j, hj⟩ x, decodeAddr_update_sel ρ ⟨j, hj⟩ x]
  simp only [Fin.val_mk]
  simp only [encodeAddr_sel x j hj ρ hi]
  simp only [selOp]
  rw [cdon_holds.2.2.2 D ⟨j, hj⟩]
  simp only [selBits]
  rcases Bool.eq_false_or_eq_true (x.2.1 ⟨j, hj⟩ ρ) with hb | hb <;> simp [hb, ka, kb] <;> ring

/-- The individual kernels on the selected bits of the first `n` chunks. -/
theorem kernels_run (hDE : DecodeEncodeAddrStmt) {A K D S rr : ℕ} (ρ : Fin K) :
    ∀ (n : ℕ), n ≤ D → ∀ (y : RArr (LayerAddr A K D S) rr),
      ProcK.run 0 ((List.range n).flatMap fun j => dgate (selField K ρ.val j)) (topClass A K D S)
        (encodeArr y) = encodeArr (selOp ρ (iv 0 n) y)
  | 0, _, y => by
    simp only [List.range_zero, List.flatMap_nil, iv_self, selOp_empty]
    rfl
  | n + 1, hn, y => by
    rw [List.range_succ, List.flatMap_append, run0_append, kernels_run hDE ρ n (by omega) y,
      List.flatMap_singleton, kernel_step ρ n (by omega),
      selOp_selOp ρ (iv_disjoint 0 n (n + 1)), iv_union (Nat.zero_le n) (Nat.le_succ n)]

/-! ## Row padding parameters -/

theorem padR_ge (d K : ℕ) : 2 ^ (q0Of d * K) ≤ padR d K := by
  unfold padR
  have hW : 0 < Wc ^ k0Of d := pow_pos Wc_pos _
  have h1 := Nat.div_add_mod (2 ^ (q0Of d * K) + Wc ^ k0Of d - 1) (Wc ^ k0Of d)
  have h2 := Nat.mod_lt (2 ^ (q0Of d * K) + Wc ^ k0Of d - 1) hW
  omega

theorem padR_pos (d K : ℕ) : 0 < padR d K := lt_of_lt_of_le (Nat.two_pow_pos _) (padR_ge d K)

theorem wc_pow_dvd {A K D d : ℕ} (hDd : D ≤ d) (k : ℕ) (hk : mH ^ k ≤ D - q0Of d) :
    Wc ^ k ∣ A * padR d K := by
  have h1 : mH ^ k ≤ d := le_trans hk (le_trans (Nat.sub_le _ _) hDd)
  have h2 : k ≤ Nat.log mH d := Nat.le_log_of_pow_le (by norm_num) h1
  have h3 : Nat.log mH d ≤ k0Of d := Nat.log_le_clog _ _
  exact Dvd.dvd.mul_left ((pow_dvd_pow Wc (h2.trans h3)).trans (Dvd.intro _ rfl)) A


/-! ## Phase 2: the C-core pieces -/

theorem mem_topClass {A K D S : ℕ} (y : (layerLayout A K D S).Addr) : (topClass A K D S).mem y :=
  Nat.mod_one _

/-- One C-core piece (CCoreProcCorrectStmt) is `C` on its group of selected bits. -/
theorem piece_run (hcert : ComplexNetCert) (hCC : CCoreProcCorrectStmt) (hR8 : RunEightSpecStmt)
    (hPA : PackedAgreeStmt) (hPP : PackedProcCorrectStmt) (hTC : TranslationConjStmt)
    {A' K D' S rr kLeaf : ℕ} (ρ : Fin K) (hK : 6 ≤ K)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hcdat : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (k j0 : ℕ) (hj : j0 + mH ^ k ≤ D') (hdvd : Wc ^ k ∣ A')
    (Y : (layerLayout A' K D' S).Addr → Fin rr → ℂ) :
    ProcK.run k (cCoreProc A' K D' S rr ρ.val kLeaf cdat k j0) (topClass A' K D' S) Y =
      encodeArr (selOp ρ (iv j0 (j0 + mH ^ k)) (decodeArr Y)) := by
  have hhyp : CCoreHyps A' K D' S ρ.val cdat k j0 (topClass A' K D' S) :=
    ⟨hK, ρ.isLt, hj, rfl, by simpa [topClass, RowClass.top] using hdvd, hcdat⟩
  have h1 := hCC hcert hR8 hPA hPP hTC A' K D' S rr kLeaf ρ cdat k j0 (topClass A' K D' S) hj hhyp
    (decodeArr Y)
  rw [encodeArr_decodeArr] at h1
  rw [← encodeArr_decodeArr (ProcK.run k _ _ Y), h1]
  congr 1
  funext x
  rw [if_pos (mem_topClass _), cCoreVal_eq_selOp]

/-- `a` consecutive pieces of width `m^j`. -/
theorem range_pieces_run (hcert : ComplexNetCert) (hCC : CCoreProcCorrectStmt)
    (hR8 : RunEightSpecStmt) (hPA : PackedAgreeStmt) (hPP : PackedProcCorrectStmt)
    (hTC : TranslationConjStmt) (hDE : DecodeEncodeAddrStmt)
    {A' K D' S rr kLeaf : ℕ} (ρ : Fin K) (hK : 6 ≤ K)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hcdat : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (hdiv : ∀ k, mH ^ k ≤ D' → Wc ^ k ∣ A') (j o : ℕ) :
    ∀ (a : ℕ) (Y : (layerLayout A' K D' S).Addr → Fin rr → ℂ), o + a * mH ^ j ≤ D' →
      ((List.range a).map (fun t => (j, o + t * mH ^ j))).foldl
          (fun B p => ProcK.run p.1 (cCoreProc A' K D' S rr ρ.val kLeaf cdat p.1 p.2)
            (topClass A' K D' S) B) Y =
        encodeArr (selOp ρ (iv o (o + a * mH ^ j)) (decodeArr Y))
  | 0, Y, _ => by
    simp only [List.range_zero, List.map_nil, List.foldl_nil, zero_mul, add_zero, iv_self,
      selOp_empty, encodeArr_decodeArr]
  | a + 1, Y, h => by
    have h' : o + a * mH ^ j + mH ^ j ≤ D' := by
      rw [show o + (a + 1) * mH ^ j = o + a * mH ^ j + mH ^ j by ring] at h; exact h
    rw [List.range_succ, List.map_append, List.foldl_append,
      range_pieces_run hcert hCC hR8 hPA hPP hTC hDE ρ hK cdat hcdat hdiv j o a Y (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [piece_run hcert hCC hR8 hPA hPP hTC ρ hK cdat hcdat j (o + a * mH ^ j) h'
      (hdiv j (by omega)), decodeArr_encodeArr hDE, selOp_selOp ρ (iv_disjoint _ _ _),
      iv_union (by omega) (by omega), show o + (a + 1) * mH ^ j = o + a * mH ^ j + mH ^ j by ring]

/-- The base-`m` pieces `piecesAux ds j o`. -/
theorem pieces_run (hcert : ComplexNetCert) (hCC : CCoreProcCorrectStmt)
    (hR8 : RunEightSpecStmt) (hPA : PackedAgreeStmt) (hPP : PackedProcCorrectStmt)
    (hTC : TranslationConjStmt) (hDE : DecodeEncodeAddrStmt)
    {A' K D' S rr kLeaf : ℕ} (ρ : Fin K) (hK : 6 ≤ K)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hcdat : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e)
    (hdiv : ∀ k, mH ^ k ≤ D' → Wc ^ k ∣ A') :
    ∀ (ds : List ℕ) (j o : ℕ) (Y : (layerLayout A' K D' S).Addr → Fin rr → ℂ),
      o + mH ^ j * Nat.ofDigits mH ds ≤ D' →
      (piecesAux ds j o).foldl
          (fun B p => ProcK.run p.1 (cCoreProc A' K D' S rr ρ.val kLeaf cdat p.1 p.2)
            (topClass A' K D' S) B) Y =
        encodeArr (selOp ρ (iv o (o + mH ^ j * Nat.ofDigits mH ds)) (decodeArr Y))
  | [], j, o, Y, _ => by
    simp only [piecesAux, List.foldl_nil, Nat.ofDigits_nil, mul_zero, add_zero, iv_self,
      selOp_empty, encodeArr_decodeArr]
  | a :: ds, j, o, Y, h => by
    have hsplit : mH ^ j * Nat.ofDigits mH (a :: ds) =
        a * mH ^ j + mH ^ (j + 1) * Nat.ofDigits mH ds := by
      rw [Nat.ofDigits_cons, pow_succ]; ring
    rw [hsplit] at h ⊢
    simp only [piecesAux, List.foldl_append]
    rw [range_pieces_run hcert hCC hR8 hPA hPP hTC hDE ρ hK cdat hcdat hdiv j o a Y (by omega),
      pieces_run hcert hCC hR8 hPA hPP hTC hDE ρ hK cdat hcdat hdiv ds (j + 1) (o + a * mH ^ j) _
        (by omega),
      decodeArr_encodeArr hDE, selOp_selOp ρ (iv_disjoint _ _ _), iv_union (by omega) (by omega),
      Nat.add_assoc]

/-- Phase 2 runs `C` on all selected bits of the reshaped layout. -/
theorem phase2_run (hcert : ComplexNetCert) (hCC : CCoreProcCorrectStmt)
    (hR8 : RunEightSpecStmt) (hPA : PackedAgreeStmt) (hPP : PackedProcCorrectStmt)
    (hTC : TranslationConjStmt) (hDE : DecodeEncodeAddrStmt)
    {A K D S rr d : ℕ} (ρ : Fin K) (hK : 6 ≤ K)
    (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData)
    (hcdat : ∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) (hDd : D ≤ d)
    (Y : (layerLayout (A * padR d K) K (D - q0Of d) S).Addr → Fin rr → ℂ) :
    PSeq.run (layerPhase2 A K D S rr ρ.val d cdat) (topClass (A * padR d K) K (D - q0Of d) S) Y =
      encodeArr (selOp ρ Finset.univ (decodeArr Y)) := by
  have h := pieces_run hcert hCC hR8 hPA hPP hTC hDE (A' := A * padR d K) (D' := D - q0Of d)
    (S := S) (rr := rr) (kLeaf := kLeafOf d) ρ hK cdat hcdat (wc_pow_dvd hDd)
    (Nat.digits mH (D - q0Of d)) 0 0 Y (by simp [Nat.ofDigits_digits])
  simp only [pow_zero, one_mul, zero_add, Nat.ofDigits_digits, iv_univ] at h
  simp only [PSeq.run, layerPhase2, List.foldl_map, piecesOf]
  exact h

/-! ## Transfer through the row reshape -/

theorem setSelBits_mergeL {A K D S q R : ℕ} (hR : 0 < R) (hq : q ≤ D) (ρ : Fin K)
    (x : LayerAddr A K D S) (e : Fin (D - q) → Bool) :
    setSelBits ρ (mergeL hR hq x) e =
      mergeL hR hq (setSelBits ρ x (insGroup q (D - q) (selBits ρ x) e)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (mergeL hR hq x).1 = (mergeL hR hq _).1
    refine mergeL_prefix hR hq rfl fun j hj => ?_
    have h1 : insGroup q (D - q) (selBits ρ x) e j = x.2.1 j ρ := by
      simp only [insGroup]; rw [dif_neg (by omega)]; rfl
    simp only [setSelBits, h1, Function.update_eq_self]
  · funext j
    have h2 : insGroup q (D - q) (selBits ρ x) e ⟨q + j.val, by omega⟩ = e j := by
      simp only [insGroup]
      rw [dif_pos (by simp)]
      congr 1; apply Fin.ext; simp
    simp only [setSelBits]
    rw [mergeL_chunk, mergeL_chunk]
    simp only [h2]
  · show (mergeL hR hq x).2.2 = (mergeL hR hq _).2.2
    rw [mergeL_suffix, mergeL_suffix]
    rfl

/-- `C` on all selected bits of the reshaped array is `C` on the selected bits of the chunks
`q, …, D−1` of the original array (padded rows are never read). -/
theorem transfer {A K D S rr q R : ℕ} (hR : 0 < R) (hq : q ≤ D) (hRq : 2 ^ (q * K) ≤ R)
    (ρ : Fin K) (A₁ : (layerLayout A K D S).Addr → Fin rr → ℂ) :
    decodeArr (restrictArr hR hq (encodeArr (selOp ρ Finset.univ
        (decodeArr (embedArr hR hq A₁))))) = selOp ρ (iv q D) (decodeArr A₁) := by
  have hy : ∀ u, decodeArr (embedArr hR hq A₁) (mergeL hR hq u) = decodeArr A₁ u := by
    intro u
    show embedArr hR hq A₁ (encodeAddr (mergeL hR hq u)) = A₁ (encodeAddr u)
    conv_lhs => rw [← encodeArr_decodeArr A₁]
    exact embedArr_mergeL hR hq hRq (decodeArr A₁) u
  funext x k
  show selOp ρ Finset.univ (decodeArr (embedArr hR hq A₁)) (mergeL hR hq x) k = _
  rw [selOp_univ]
  simp only [setSelBits_mergeL hR hq ρ x, hy]
  have hsel : selBits ρ (mergeL hR hq x) = fun i => selBits ρ x ⟨q + i.val, by omega⟩ := by
    funext i; simp only [selBits]; rw [mergeL_chunk]
  rw [hsel, cd_group_eq_cdon q (D - q) (by omega) (fun e' => decodeArr A₁ (setSelBits ρ x e') k)
    (selBits ρ x)]
  have hqD : q + (D - q) = D := by omega
  simp only [selOp, hqD]

end LayerSpecAux

open Model SubNLogN.Math.Walsh SubNLogN.Math.Common LayerSpecAux
open LayerSpecPadAux (phase3_decode phase1_eq)

namespace LayerSpecAux

/-- **Proposition A.11, functional, strong form**: as `Prop71LayerSpecStmt`, without the hypotheses
`H0TensorIdentityStmt` and `1 ≤ D` (re-exported as `prop71LayerSpec_all` in `LayerSpecCover.lean`). -/
theorem layerSpec_strong : ComplexNetCert → CCoreProcCorrectStmt → RunEightSpecStmt →
    PackedAgreeStmt → PackedProcCorrectStmt → TranslationConjStmt → Prop71FunctionalStmt →
    DecodeEncodeAddrStmt →
    ∀ (cdat : Vertex .complex 100 × Vertex .complex 100 → CxEdgeData),
      (∀ w : Role .complex 100, ∀ e ∈ edges w, (cdat e).Valid e) →
    ∀ (P d rr K D A S : ℕ) (ρ : Fin K), 6 ≤ K → D ≤ d →
      LayerSpec P rr A K D S ρ (layerRun P A K D S rr ρ.val d cdat) := by
  intro hcert hCC hR8 hPA hPP hTC hFun hDE cdat hcdat P d rr K D A S ρ hK hDd
  have hC : ∀ (z : RArr (LayerAddr A K D S) rr) (x₀ : LayerAddr A K D S) (e₀ : Fin D → Bool)
      (k : Fin rr), selOp ρ Finset.univ z (setSelBits ρ x₀ e₀) k =
        CD D (fun e => z (setSelBits ρ x₀ e) k) e₀ := by
    intro z x₀ e₀ k
    rw [selOp_univ]
    simp only [setSelBits_setSelBits, selBits_setSelBits]
  intro z hz
  have hA1 : ProcK.run 0 (layerPhase1 A K D S rr ρ.val d) (topClass A K D S) (encodeArr z) =
      encodeArr (selOp ρ (iv 0 (min (q0Of d) D)) (fun y k' =>
        Complex.I ^ (Finset.univ.filter fun j => y.2.1 j ρ = true).card * z y k')) := by
    rw [phase1_eq, kernels_run hDE ρ _ (min_le_right _ _)]
  have key : layerRun P A K D S rr ρ.val d cdat z = truncArr P (fun x k => bD D *
      (Complex.I ^ (Finset.univ.filter fun j => x.2.1 j ρ = true).card *
        selOp ρ Finset.univ (fun y k' =>
          Complex.I ^ (Finset.univ.filter fun j => y.2.1 j ρ = true).card * z y k') x k)) := by
    by_cases h : useRows D K d
    · have e : layerRun P A K D S rr ρ.val d cdat z =
          decodeArr (ProcK.run 0 (layerPhase3 A K D S rr ρ.val P) (topClass A K D S)
            (restrictArr h.2 h.1.le (PSeq.run (layerPhase2 A K D S rr ρ.val d cdat)
              (topClass (A * padR d K) K (D - q0Of d) S) (embedArr h.2 h.1.le
                (ProcK.run 0 (layerPhase1 A K D S rr ρ.val d) (topClass A K D S)
                  (encodeArr z)))))) := by
        simp only [layerRun, dif_pos h]
      rw [e, phase3_decode, phase2_run hcert hCC hR8 hPA hPP hTC hDE ρ hK cdat hcdat hDd, hA1,
        transfer h.2 h.1.le (padR_ge d K) ρ, decodeArr_encodeArr hDE, min_eq_left h.1.le,
        selOp_selOp ρ (iv_disjoint 0 _ D), iv_union (Nat.zero_le _) h.1.le, iv_univ]
    · have hq : D ≤ q0Of d := by
        by_contra hlt
        exact h ⟨by omega, padR_pos d K⟩
      have e : layerRun P A K D S rr ρ.val d cdat z =
          decodeArr (ProcK.run 0 (layerPhase3 A K D S rr ρ.val P) (topClass A K D S)
            (ProcK.run 0 (layerPhase1 A K D S rr ρ.val d) (topClass A K D S) (encodeArr z))) := by
        simp only [layerRun, dif_neg h]
      rw [e, phase3_decode, hA1, decodeArr_encodeArr hDE, min_eq_right hq, iv_univ]
  rw [key]
  exact hFun P rr A K D S ρ (selOp ρ Finset.univ) hC z hz

end LayerSpecAux

/-- **Proposition A.11, functional** (`Prop71LayerSpecStmt`), from `LayerSpecAux.layerSpec_strong`. -/
theorem prop71LayerSpec_holds : Prop71LayerSpecStmt :=
  fun hcert hCC hR8 hPA hPP hTC _ hFun hDE cdat hcdat P d rr K D A S ρ hK _ hDd =>
    LayerSpecAux.layerSpec_strong hcert hCC hR8 hPA hPP hTC hFun hDE cdat hcdat P d rr K D A S ρ hK
      hDd

end SubNLogN.Math.Networks
