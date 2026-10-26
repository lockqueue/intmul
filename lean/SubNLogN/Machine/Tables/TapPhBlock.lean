/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Tables.TapPhBlockStmt
import SubNLogN.Machine.Tables.TapRankProof
import SubNLogN.Machine.Tables.SolBlock
import IntMulTM.SpecFacts

/-!
# K6: one tap block (`Machine/Tables/TapPhBlock.lean`), `TapBlockStmt` from `TapRecStmt`

**Program** (`tapBlockProg`, the `solBlockProg` template): push `mark` on `tapTab`; copy `A_i`
from `rA` to the counter `ru`; countdown `r = A_i - 1, …, 0`: the rank fragment
(`TapPhAux.rankProg`, `TapPhRank.lean`) puts `a = rankA (lowerShape t i) r` on `ra`, the tap-record
program of `TapRecStmt` pushes the record of shift index `a`, and `ra` is dropped. The records
are pushed last first, so `tapTab` gains `carrSyms wT (tapBlock …) ++ mark` (record order:
`tapBlockRank_holds`, `TapRankProof.lean`; record contents: `tapRec_tabOf`).

**Hypotheses.** `TapRecStmt` (`TapEntryStmt.lean`) and the rank fragment's contract
`RankProgSpec rankP rc` (`TapPhAux.rankProg` with its specification `HT.rankProg_spec`,
consumed here with all temporaries empty) with a cost `rc C KM β ≤ Kr·(C+1)(KM+1)(β+1)^3`.

**Scope (honest summary).** `tapBlock_of`: `RankProgSpec rankP rc → (cost bound) → TapRecStmt →
TapBlockStmt`, fully proved; no other hypotheses.
-/

namespace SubNLogN.Machine.Tables.TapPhBlock

open TMFw TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 SubNLogN.Machine SubNLogN.Machine.Tables
  SubNLogN.Math.Bridge SubNLogN.Math.Bridge.IntForms SubNLogN.Math.Common

/-! ## The rank fragment's contract (as consumed) -/

/-- The contract of a rank fragment `rankP` (`TapPhAux.rankProg`, `TapPhRank.lean`)
with cost function `rc`: a closed program that, from the rank `r` on `ru`, `∏ L` on `rA`, `|L|` on
`rI` and `hdrSyms L` on `rSH`, puts `rankA L r` on the empty `ra`, every other stack restored
(temporaries `.inr 40 … .inr 60` empty before and after). -/
def RankProgSpec (rankP : (I : TB) → TP I) (rc : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (I : TB) (Mul : ℕ → ℕ) (C KM : ℕ), I.Spec Mul C → (∀ w, Mul w ≤ KM * (w + 1) ^ 2) →
    (rankP I).Closed ∧
    ∀ (B : TL → List Sym) (L : List ℕ) (r β : ℕ), (∀ t ∈ L, 1 ≤ t) → r < L.prod →
      bitLen L.prod ≤ β → L.length ≤ β →
      B ru = natSyms r → B rA = natSyms L.prod → B rI = natSyms L.length → B rSH = hdrSyms L →
      B ra = [] → (∀ j : Fin 61, 40 ≤ (j : ℕ) → B (.inr j) = []) → ∀ ρ : List (TP I),
      HT ρ B (rankP I) (Function.update B ra (natSyms (rankA L r))) (rc C KM β)

/-! ## Pure facts on the lower shape and the rank fold -/

theorem lowerShape_len' {d : ℕ} (t : Fin d → ℕ) (i : ℕ) (hi : i ≤ d) :
    (lowerShape t i).length = i := by
  simp [lowerShape, hi]

theorem lowerShape_ge' {d : ℕ} (t : Fin d → ℕ) (h2 : ∀ j, 2 ≤ t j) (i : ℕ) :
    ∀ x ∈ lowerShape t i, 2 ≤ x := by
  intro x hx
  unfold lowerShape at hx
  rw [List.mem_reverse] at hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 (List.mem_of_mem_take hx)
  exact h2 j

theorem lowerShape_prod' {d : ℕ} (t : Fin d → ℕ) (i : ℕ) (hi : i ≤ d) :
    (lowerShape t i).prod = prefixProd t i := by
  rw [TapRankProof.lowerShape_eq t i hi, List.map_reverse, List.prod_reverse,
    TapRankProof.prod_map_range]
  unfold prefixProd
  have hs : (Finset.univ.filter (fun l : Fin d => (l : ℕ) < i)).map Fin.valEmbedding =
      Finset.range i := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨c, h, rfl⟩
      exact h
    · intro h
      exact ⟨⟨x, by omega⟩, h, rfl⟩
  rw [← hs, Finset.prod_map]
  exact Finset.prod_congr rfl fun c _ => TapRankProof.extT_fin t c

theorem two_pow_le_prod' (L : List ℕ) (h : ∀ x ∈ L, 2 ≤ x) : 2 ^ L.length ≤ L.prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    rw [List.length_cons, pow_succ, List.prod_cons]
    calc 2 ^ L.length * 2 = 2 * 2 ^ L.length := by ring
      _ ≤ x * L.prod := Nat.mul_le_mul hx ih'

theorem length_lt_bitLen_prod' (L : List ℕ) (h : ∀ x ∈ L, 2 ≤ x) :
    L.length < bitLen L.prod := by
  have h1 := WP.W7k2.bitLen_mono (two_pow_le_prod' L h)
  rw [WP.W7k2.bitLen_two_pow] at h1
  omega

theorem rankG_lt : ∀ (L : List ℕ), (∀ t ∈ L, 1 ≤ t) → ∀ x, TapRankProof.rankG L x < L.prod
  | [], _, _ => by simp [TapRankProof.rankG]
  | u :: L, hL, x => by
    have hu : 1 ≤ u := hL u (by simp)
    have ih := rankG_lt L (fun v hv => hL v (by simp [hv])) (x / u)
    have hmod : x % u + 1 ≤ u := Nat.mod_lt _ (by omega)
    have h1 : L.prod * (x % u) + L.prod ≤ L.prod * u := by
      have := Nat.mul_le_mul_left L.prod hmod
      rw [Nat.mul_add, Nat.mul_one] at this
      exact this
    simp only [TapRankProof.rankG, List.prod_cons]
    rw [Nat.mul_comm u]
    omega

theorem rankA_lt' (L : List ℕ) (r : ℕ) (hL : ∀ t ∈ L, 1 ≤ t) : rankA L r < L.prod := by
  rw [TapRankProof.rankA_eq_rankG L (fun u hu => hL u hu) r]
  exact rankG_lt L hL r

/-! ## Records -/

/-- The stored tap record of shift index `a`, in integer form (`tapInt`). -/
theorem tapRec_tabOf {d : ℕ} (ω P : ℕ) (t : Fin d → ℕ) (i : Fin d) (a : ℕ) :
    tapRec t P ((tabOf ω P t).tap i) i a =
      (tapWin (t i) P).map (tapInt ω P (t i) (prefixProd t i) a) := by
  unfold tapRec
  rw [tapOffsets_eq_tapWin]
  exact List.map_congr_left fun e _ => gridIntC_tapConcreteR ω P (t i) (prefixProd t i) a e

/-- The records of one tap block, in block order. -/
noncomputable def tapRecsN (ω P t A : ℕ) (L : List ℕ) : List (List CInt) :=
  (List.range A).map fun r => (tapWin t P).map (tapInt ω P t A (rankA L r))

theorem length_tapRecsN (ω P t A : ℕ) (L : List ℕ) : (tapRecsN ω P t A L).length = A := by
  simp [tapRecsN]

theorem tapBlock_tabOf {d : ℕ} (ω P : ℕ) (t : Fin d → ℕ) (i : Fin d) (ht : ShapeOK t) :
    tapBlock t P (tabOf ω P t) i =
      tapRecsN ω P (t i) (prefixProd t i) (lowerShape t i) := by
  rw [TapRankProof.tapBlockRank_holds d t P (tabOf ω P t) i ht]
  unfold tapRecsN
  exact List.map_congr_left fun r _ => tapRec_tabOf ω P t i _

theorem tapRecsN_drop (ω P t A : ℕ) (L : List ℕ) (k : ℕ) (hk : k < A) :
    (tapRecsN ω P t A L).drop k =
      (tapWin t P).map (tapInt ω P t A (rankA L k)) :: (tapRecsN ω P t A L).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [length_tapRecsN]; exact hk)]
  simp [tapRecsN]

theorem length_tapWin_le (t P : ℕ) : (tapWin t P).length ≤ 2 * P + 1 := by
  unfold tapWin
  split_ifs with h
  · simp
  · simp; omega

/-! ## The program -/

section Prog

variable (I : TB)

/-- One iteration: shift index, record, drop the shift index. -/
def tapIter (rankP recP : TP I) : TP I := rankP.seq (recP.seq (tdr I ra))

/-- **One tap block.** -/
def tapBlockProg (rankP recP : TP I) : TP I :=
  (tpush I sTap .mark).seq ((tcp I rA ru).seq (tcd I ru (tapIter I rankP recP)))

theorem tapBlockProg_closed (rankP recP : TP I) (hrank : rankP.Closed) (hrec : recP.Closed) :
    (tapBlockProg I rankP recP).Closed :=
  ⟨trivial, ⟨callI_closed _ _ _ _, tcd_closed I _ _ ⟨hrank, ⟨hrec, callI_closed _ _ _ _⟩⟩⟩⟩

end Prog

/-- The countdown states: records `k … A-1` pushed (above the mark), counter `k`. -/
noncomputable def tapSt (B : TL → List Sym) (wT ω P t A : ℕ) (L : List ℕ) (k : ℕ) :
    TL → List Sym :=
  Function.update (Function.update B sTap
    (carrSyms wT ((tapRecsN ω P t A L).drop k) ++ Sym.mark :: B sTap)) ru (natSyms k ++ [])

/-! ## Cost arithmetic -/

theorem bitLen_le_size (n : ℕ) : bitLen n ≤ Nat.size n := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat]

theorem block_cost_arith (A Q G U K0 setup lc : ℕ) (hA : 1 ≤ A) (hQ : 1 ≤ Q) (hUG : U ≤ G)
    (hU : 1 ≤ U) (hlc : lc ≤ A * (K0 * Q * G + 1) + 1) (hsetup : setup ≤ 3 * Q * U) :
    setup + lc ≤ (K0 + 5) * Q * (A * G + 1) := by
  have hG : 1 ≤ G := le_trans hU hUG
  have h1 : Q * U ≤ Q * (A * G) :=
    Nat.mul_le_mul_left Q (le_trans hUG (Nat.le_mul_of_pos_left G hA))
  have h2 : A ≤ Q * (A * G) := by
    calc A ≤ A * G := Nat.le_mul_of_pos_right A hG
      _ ≤ Q * (A * G) := Nat.le_mul_of_pos_left _ hQ
  have e1 : A * (K0 * Q * G + 1) = K0 * (Q * (A * G)) + A := by ring
  have e2 : (K0 + 5) * Q * (A * G + 1) =
      K0 * (Q * (A * G)) + 5 * (Q * (A * G)) + (K0 + 5) * Q := by ring
  have e3 : 3 * Q * U = 3 * (Q * U) := by ring
  rw [e1] at hlc
  rw [e3] at hsetup
  rw [e2]
  have h4 : 1 ≤ (K0 + 5) * Q := le_trans hQ (Nat.le_mul_of_pos_left Q (by omega))
  omega

theorem Y_bounds (Y : ℕ) (hY : 100 ≤ Y) : Y + 1 ≤ Y ^ 5 ∧ (Y + 1) ^ 3 ≤ Y ^ 5 := by
  have h1 : (Y + 1) ^ 3 ≤ (2 * Y) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h2 : (2 * Y) ^ 3 = 8 * Y ^ 3 := by ring
  have h3 : 8 * Y ^ 3 ≤ Y ^ 2 * Y ^ 3 := Nat.mul_le_mul_right _ (by nlinarith)
  have h4 : Y ^ 2 * Y ^ 3 = Y ^ 5 := by ring
  have h5 : Y + 1 ≤ (Y + 1) ^ 3 := by nlinarith
  omega

/-- Per-record cost bound. -/
theorem iter_cost_le (C KM Kr Krec β P wT nW Y rcv recv bk ba : ℕ) (hY : 100 ≤ Y)
    (hβ : β ≤ Y) (hbk : bk ≤ Y) (hba : ba ≤ Y) (hW : nW ≤ 2 * P + 1) (hwT : 1 ≤ wT)
    (hrcv : rcv ≤ Kr * (C + 1) * (KM + 1) * (β + 1) ^ 3)
    (hrecv : recv = nW * ((2 * P + 1) * Y ^ 5 + wT + 1)) :
    C * (bk + 1) + (rcv + (Krec * (C + 1) * (KM + 1) * recv + C * (ba + 1))) + C ≤
      (Kr + Krec + 3) * ((C + 1) * (KM + 1)) *
        ((2 * P + 1) * (2 * P + 1) * Y ^ 5 + nW * (2 * wT) + 1) := by
  obtain ⟨hY1, hY3⟩ := Y_bounds Y hY
  generalize hU : Y ^ 5 = U at hY1 hY3 hrecv ⊢
  generalize hQ : (C + 1) * (KM + 1) = Q
  have hCQ : C + 1 ≤ Q := by rw [← hQ]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hQ1 : 1 ≤ Q := le_trans (by omega) hCQ
  have hβ3 : (β + 1) ^ 3 ≤ U := le_trans (Nat.pow_le_pow_left (by omega) 3) hY3
  have hrc' : rcv ≤ Kr * (Q * U) := by
    calc rcv ≤ Kr * (C + 1) * (KM + 1) * (β + 1) ^ 3 := hrcv
      _ = Kr * ((C + 1) * (KM + 1) * (β + 1) ^ 3) := by ring
      _ ≤ Kr * (Q * U) := by rw [hQ]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hβ3)
  have hrec' : recv ≤ (2 * P + 1) * (2 * P + 1) * U + nW * (2 * wT) := by
    rw [hrecv]
    have h1 : nW * ((2 * P + 1) * U) ≤ (2 * P + 1) * ((2 * P + 1) * U) :=
      Nat.mul_le_mul_right _ hW
    have h2 : nW * (wT + 1) ≤ nW * (2 * wT) := Nat.mul_le_mul_left _ (by omega)
    have e : nW * ((2 * P + 1) * U + wT + 1) = nW * ((2 * P + 1) * U) + nW * (wT + 1) := by ring
    rw [e]
    nlinarith
  have hrec'' : Krec * (C + 1) * (KM + 1) * recv ≤
      Krec * (Q * ((2 * P + 1) * (2 * P + 1) * U + nW * (2 * wT))) := by
    calc Krec * (C + 1) * (KM + 1) * recv = Krec * ((C + 1) * (KM + 1) * recv) := by ring
      _ ≤ _ := by rw [hQ]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hrec')
  have hC1 : C * (bk + 1) ≤ Q * U := Nat.mul_le_mul (by omega) (by omega)
  have hC2 : C * (ba + 1) ≤ Q * U := Nat.mul_le_mul (by omega) (by omega)
  have hC3 : C ≤ Q * U := le_trans (by omega) (Nat.le_mul_of_pos_right Q (by omega))
  have hUG : U ≤ (2 * P + 1) * (2 * P + 1) * U :=
    Nat.le_mul_of_pos_left U (by positivity)
  have hfin : (Kr + Krec + 3) * Q * ((2 * P + 1) * (2 * P + 1) * U + nW * (2 * wT) + 1) =
      Kr * (Q * ((2 * P + 1) * (2 * P + 1) * U + nW * (2 * wT) + 1)) +
        Krec * (Q * ((2 * P + 1) * (2 * P + 1) * U + nW * (2 * wT))) + Krec * Q +
        3 * (Q * ((2 * P + 1) * (2 * P + 1) * U + nW * (2 * wT) + 1)) := by ring
  rw [hfin]
  have hKr : Kr * (Q * U) ≤ Kr * (Q * ((2 * P + 1) * (2 * P + 1) * U + nW * (2 * wT) + 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have h3 : Q * U ≤ Q * ((2 * P + 1) * (2 * P + 1) * U + nW * (2 * wT) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## `TapBlockStmt` -/

/-- **`TapBlockStmt`** from a rank fragment (`RankProgSpec rankP rc`, cost
`rc C KM β ≤ Kr·(C+1)(KM+1)(β+1)^3`) and the tap-record machine (`TapRecStmt`). -/
theorem tapBlock_of (rankP : (I : TB) → TP I) (rc : ℕ → ℕ → ℕ → ℕ) (Kr : ℕ)
    (hrc : ∀ C KM β, rc C KM β ≤ Kr * (C + 1) * (KM + 1) * (β + 1) ^ 3)
    (hRank : RankProgSpec rankP rc) (hTap : TapRecStmt) : TapBlockStmt := by
  obtain ⟨Krec, hTap⟩ := hTap
  refine ⟨Kr + Krec + 3 + 5, fun I Mul C KM hI hMul => ?_⟩
  obtain ⟨recP, hrecC, hrec⟩ := hTap I Mul C KM hI hMul
  obtain ⟨hrankC, hrank⟩ := hRank I Mul C KM hI hMul
  refine ⟨tapBlockProg I (rankP I) recP, tapBlockProg_closed I (rankP I) recP hrankC hrecC, ?_⟩
  intro b i B ht hω hwT hfit hP hW hB' hPi hLn hPW hPW1 hT hA hDen hI' hSH hru hra htmp
  have hL2 : ∀ x ∈ lowerShape b.t i, 2 ≤ x := lowerShape_ge' b.t (fun j => (ht j).1) i
  have hL1 : ∀ x ∈ lowerShape b.t i, 1 ≤ x := fun x hx => le_trans (by norm_num) (hL2 x hx)
  have hLA : (lowerShape b.t i).prod = prefixProd b.t i :=
    lowerShape_prod' b.t i (le_of_lt i.isLt)
  have hLlen : (lowerShape b.t i).length = i := lowerShape_len' b.t i (le_of_lt i.isLt)
  have hβL : (lowerShape b.t i).length ≤ bitLen (prefixProd b.t i) := by
    have := length_lt_bitLen_prod' (lowerShape b.t i) hL2
    rw [hLA] at this
    omega
  have ht1 : 1 ≤ b.t i := le_trans (by norm_num) (ht i).1
  have hA1 : 1 ≤ prefixProd b.t i := by
    rw [← hLA]
    exact List.prod_pos (fun x hx => hL1 x hx)
  have hblock := tapBlock_tabOf b.ω b.P b.t i ht
  have hfitk : ∀ k < prefixProd b.t i, ∀ e ∈ tapWin (b.t i) b.P,
      FitsTwos b.wT (tapInt b.ω b.P (b.t i) (prefixProd b.t i)
        (rankA (lowerShape b.t i) k) e).1 ∧
      FitsTwos b.wT (tapInt b.ω b.P (b.t i) (prefixProd b.t i)
        (rankA (lowerShape b.t i) k) e).2 := by
    intro k hk e he
    rw [hblock] at hfit
    exact hfit _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩) _ (List.mem_map_of_mem he)
  have hrk : ∀ k, rankA (lowerShape b.t i) k < prefixProd b.t i := fun k => by
    rw [← hLA]
    exact rankA_lt' _ k hL1
  have hloop := HT.tcd_spec hI ru [] TermOK.nil
    (tapSt B b.wT b.ω b.P (b.t i) (prefixProd b.t i) (lowerShape b.t i))
    (fun k => by simp only [tapSt, Function.update_self]) (tapIter I (rankP I) recP)
    (prefixProd b.t i)
    (fun k => rc C KM (bitLen (prefixProd b.t i)) +
      (Krec * (C + 1) * (KM + 1) * tapRecCost b.ω b.P (b.t i) (prefixProd b.t i) b.wT +
        C * (bitLen (rankA (lowerShape b.t i) k) + 1))) []
    (fun k hk => by
      have r1 := hrank
        (Function.update (tapSt B b.wT b.ω b.P (b.t i) (prefixProd b.t i) (lowerShape b.t i)
          (k + 1)) ru (natSyms k ++ []))
        (lowerShape b.t i) k (bitLen (prefixProd b.t i)) hL1 (by rw [hLA]; exact hk)
        (by rw [hLA]) hβL
        (by simp only [Function.update_self, List.append_nil])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hA, hLA])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hI', hLlen])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hSH])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hra])
        (fun j hj => by
          have h1 : (Sum.inr j : TL) ≠ ru := inr_ne_inr (by simp; omega)
          have h2 : (Sum.inr j : TL) ≠ sTap := Sum.inr_ne_inl
          rw [Function.update_of_ne h1, tapSt, Function.update_of_ne h1,
            Function.update_of_ne h2]
          exact htmp j hj) []
      have r2 := hrec
        (Function.update (Function.update (tapSt B b.wT b.ω b.P (b.t i) (prefixProd b.t i)
          (lowerShape b.t i) (k + 1)) ru (natSyms k ++ [])) ra
          (natSyms (rankA (lowerShape b.t i) k)))
        b.ω b.P b.wT (b.t i) (prefixProd b.t i) (rankA (lowerShape b.t i) k) hω hwT ht1 (hrk k)
        (hfitk k hk)
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hP])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hW])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hB'])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hPi])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hLn])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hPW])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hPW1])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hT])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hA])
        (by simp (disch := decide) only [tapSt, Function.update_of_ne, hDen])
        (by simp only [Function.update_self])
        (fun j hj => by
          have h1 : (Sum.inr j : TL) ≠ ru := inr_ne_inr (by simp; omega)
          have h2 : (Sum.inr j : TL) ≠ sTap := Sum.inr_ne_inl
          have h3 : (Sum.inr j : TL) ≠ ra := inr_ne_inr (by simp; omega)
          rw [Function.update_of_ne h3, Function.update_of_ne h1, tapSt,
            Function.update_of_ne h1, Function.update_of_ne h2]
          exact htmp j hj)
      refine (HT.seq r1 (HT.seq r2 (HT.tdr_spec hI ra _ (rankA (lowerShape b.t i) k) []
        TermOK.nil ?_ []))).of_eq ?_ le_rfl
      · simp (disch := decide) only [Function.update_of_ne, Function.update_self,
          List.append_nil]
      · funext g
        by_cases g1 : g = sTap
        · subst g1
          simp (disch := decide) only [tapSt, Function.update_of_ne, Function.update_self]
          rw [tapRecsN_drop _ _ _ _ _ k hk, carrSyms_cons, List.append_assoc]
        by_cases g2 : g = ru
        · subst g2
          simp (disch := decide) only [tapSt, Function.update_of_ne, Function.update_self]
        by_cases g3 : g = ra
        · subst g3
          simp (disch := decide) only [tapSt, Function.update_of_ne, Function.update_self, hra]
        simp only [tapSt, Function.update_of_ne g1, Function.update_of_ne g2,
          Function.update_of_ne g3])
  have hstart : tapSt B b.wT b.ω b.P (b.t i) (prefixProd b.t i) (lowerShape b.t i)
      (prefixProd b.t i) = Function.update (Function.update B sTap (Sym.mark :: B sTap)) ru
        (natSyms (prefixProd b.t i) ++ Function.update B sTap (Sym.mark :: B sTap) ru) := by
    rw [tapSt, Function.update_of_ne (by decide : ru ≠ sTap), hru,
      List.drop_eq_nil_of_le (by rw [length_tapRecsN]), carrSyms_nil, List.nil_append]
  rw [hstart] at hloop
  refine (HT.seq (HT.tpush_spec sTap .mark B [])
    (HT.seq (HT.tcp_spec hI rA ru (by decide) _ (prefixProd b.t i) [] TermOK.nil
      (by simp (disch := decide) only [Function.update_of_ne, hA, List.append_nil]) [])
      hloop)).of_eq ?_ ?_
  · rw [hblock]
    funext g
    by_cases g2 : g = ru
    · subst g2
      simp (disch := decide) only [tapSt, Function.update_of_ne, Function.update_self, hru,
        natSyms_zero', List.append_nil]
    simp only [tapSt, Function.update_of_ne g2, List.drop_zero]
  · have hYbig : 100 ≤ b.ω + 4 * b.P + 2 * Nat.size (2 * b.t i * prefixProd b.t i) + 100 := by
      omega
    have hβY : bitLen (prefixProd b.t i) ≤
        b.ω + 4 * b.P + 2 * Nat.size (2 * b.t i * prefixProd b.t i) + 100 := by
      have h1 := bitLen_le_size (prefixProd b.t i)
      have h2 : Nat.size (prefixProd b.t i) ≤ Nat.size (2 * b.t i * prefixProd b.t i) :=
        Nat.size_le_size (by nlinarith)
      omega
    obtain ⟨hY1, -⟩ := Y_bounds _ hYbig
    have hU : tabUnit b i =
        (b.ω + 4 * b.P + 2 * Nat.size (2 * b.t i * prefixProd b.t i) + 100) ^ 5 := rfl
    have hlc := loopCost_le_unif
      (fun k => C * (bitLen (k + 1) + 1) + (rc C KM (bitLen (prefixProd b.t i)) +
        (Krec * (C + 1) * (KM + 1) * tapRecCost b.ω b.P (b.t i) (prefixProd b.t i) b.wT +
          C * (bitLen (rankA (lowerShape b.t i) k) + 1))) + C)
      ((Kr + Krec + 3) * ((C + 1) * (KM + 1)) *
        ((2 * b.P + 1) * (2 * b.P + 1) * tabUnit b i +
          (tapWin (b.t i) b.P).length * (2 * b.wT) + 1))
      (prefixProd b.t i)
      (fun k hk => iter_cost_le C KM Kr Krec (bitLen (prefixProd b.t i)) b.P b.wT
        (tapWin (b.t i) b.P).length _ _
        (tapRecCost b.ω b.P (b.t i) (prefixProd b.t i) b.wT) _ _ hYbig hβY
        (le_trans (WP.W7k2.bitLen_mono hk) hβY)
        (le_trans (WP.W7k2.bitLen_mono (le_of_lt (hrk k))) hβY)
        (length_tapWin_le _ _) hwT (hrc C KM _) rfl)
    have hAx : tapAxisCost b i = prefixProd b.t i * ((2 * b.P + 1) * (2 * b.P + 1) * tabUnit b i +
        (tapWin (b.t i) b.P).length * (2 * b.wT) + 1) + 1 := by
      unfold tapAxisCost
      rw [tapOffsets_eq_tapWin]
      ring
    have hQ1 : 1 ≤ (C + 1) * (KM + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    have hU1 : 1 ≤ tabUnit b i := by rw [hU]; omega
    have hUG : tabUnit b i ≤ (2 * b.P + 1) * (2 * b.P + 1) * tabUnit b i +
        (tapWin (b.t i) b.P).length * (2 * b.wT) + 1 := by
      have := Nat.le_mul_of_pos_left (tabUnit b i)
        (show 0 < (2 * b.P + 1) * (2 * b.P + 1) by positivity)
      omega
    have hsetup : 1 + C * (bitLen (prefixProd b.t i) + 1) + C ≤
        3 * ((C + 1) * (KM + 1)) * tabUnit b i := by
      have hCQ : C + 1 ≤ (C + 1) * (KM + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have h1 : C * (bitLen (prefixProd b.t i) + 1) ≤ ((C + 1) * (KM + 1)) * tabUnit b i :=
        Nat.mul_le_mul (by omega) (by rw [hU]; omega)
      have h2 : C + 1 ≤ ((C + 1) * (KM + 1)) * tabUnit b i :=
        le_trans hCQ (Nat.le_mul_of_pos_right _ (by omega))
      have e : 3 * ((C + 1) * (KM + 1)) * tabUnit b i =
          3 * (((C + 1) * (KM + 1)) * tabUnit b i) := by ring
      rw [e]
      omega
    have harith := block_cost_arith (prefixProd b.t i) ((C + 1) * (KM + 1))
      ((2 * b.P + 1) * (2 * b.P + 1) * tabUnit b i + (tapWin (b.t i) b.P).length * (2 * b.wT) + 1)
      (tabUnit b i) (Kr + Krec + 3) _ _ hA1 hQ1 hUG hU1 hlc hsetup
    rw [hAx]
    have e2 : (Kr + Krec + 3 + 5) * (C + 1) * (KM + 1) *
        (prefixProd b.t i * ((2 * b.P + 1) * (2 * b.P + 1) * tabUnit b i +
          (tapWin (b.t i) b.P).length * (2 * b.wT) + 1) + 1) =
        (Kr + Krec + 3 + 5) * ((C + 1) * (KM + 1)) *
        (prefixProd b.t i * ((2 * b.P + 1) * (2 * b.P + 1) * tabUnit b i +
          (tapWin (b.t i) b.P).length * (2 * b.wT) + 1) + 1) := by ring
    rw [e2]
    omega

end SubNLogN.Machine.Tables.TapPhBlock
