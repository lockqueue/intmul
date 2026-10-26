/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.DIFLevel

/-!
# K4-DIF, the whole kernel (`Machine/FFT/DIFMain.lean`): setup, the two loops, the program

**Scope (honest summary).** Proved (no `sorry`), conditional on the two arithmetic sub-kernels
given as `HSDSpec`/`CMSpec` hypotheses (`DIFLevel.lean`):
* setup helpers: `skipField` (skip one header field), `rcBuild` (unit ruler of `2w` marks from
  the first table record), `hfCount` (count the `r` coefficients of the first data record);
* `cinterBits_crecBits`: the bit-level unit interleave of two encoded records is the encoding of
  the coefficientwise interleave;
* `brBody`, `runs_brBody`: one bit-reversal pass (deal, then coefficientwise merge);
* `mainProg`: the kernel program.
-/

namespace SubNLogN.Machine.FFT.DIF

open TMFw TMFw.Contracts WP.W9comp SubNLogN.Math.Common SubNLogN.Math.Walsh

/-! ## Unit interleave of encoded records -/

theorem coefBits_length' (w : ℕ) (c : CInt) : (coefBits w c).length = 2 * w := by
  simp [coefBits, twosBits_length]; ring

theorem cinterBits_cons (n k : ℕ) (c d a b : List Bool) (hc : c.length = n) (hd : d.length = n) :
    cinterBits n (k + 1) (c ++ a) (d ++ b) = c ++ d ++ cinterBits n k a b := by
  unfold cinterBits
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp only [Nat.zero_mul, List.drop_zero]
  rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  congr 1
  apply List.flatMap_congr
  intro j _
  rw [Nat.succ_mul, Nat.add_comm (j * n) n, ← List.drop_drop, ← List.drop_drop,
    List.drop_left' hc, List.drop_left' hd]

theorem cinterBits_crecBits (w : ℕ) :
    ∀ (a b : List CInt), a.length = b.length →
      cinterBits (2 * w) a.length (crecBits w a) (crecBits w b) = crecBits w (inter a b)
  | [], [], _ => by simp [cinterBits, inter, crecBits]
  | x :: a, y :: b, h => by
    have h' : a.length = b.length := by simpa using h
    have e : crecBits w (x :: a) = coefBits w x ++ crecBits w a := by simp [crecBits]
    have e' : crecBits w (y :: b) = coefBits w y ++ crecBits w b := by simp [crecBits]
    rw [List.length_cons, e, e', cinterBits_cons _ _ _ _ _ _ (coefBits_length' w x)
      (coefBits_length' w y), cinterBits_crecBits w a b h']
    simp [inter, crecBits]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ## Setup helpers -/

section Setup

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-- Skip one header field (a binary number and its `mark`), parking it on `dst`. -/
def skipField (src dst : K) : Prog K (fun _ => Sym) σ :=
  .seq (movePrefix lO src dst optIsBit) (mv lO src dst)

omit [DecidableEq K] in
theorem closed_skipField (src dst : K) : (skipField lO src dst).Closed :=
  ⟨closed_movePrefix lO src dst _, closed_mv lO src dst⟩

theorem runs_skipField {src dst : K} (hne : src ≠ dst) (S : K → List Sym) (n : ℕ)
    (rest : List Sym) (hS : S src = natSyms n ++ Sym.mark :: rest) :
    Runs (skipField lO src dst) S
      (Function.update (Function.update S src rest) dst
        (Sym.mark :: ((natSyms n).reverse ++ S dst)))
      (fun _ => True) (4 * bitLen n + 4) := by
  have hb : ∀ x ∈ natSyms n, optIsBit (some x) = true := by
    intro x hx
    simp only [natSyms, List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    rfl
  have e1 := runs_movePrefix lO hne optIsBit S _ _ hS hb rfl
  have e2 := runs_mv lO hne (Function.update (Function.update S src (Sym.mark :: rest)) dst
    ((natSyms n).reverse ++ S dst)) (x := Sym.mark) (l := rest)
    (by rw [Function.update_of_ne hne, Function.update_self])
  refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial)
    (by rw [length_natSyms] <;> omega)) ?_
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- The unit ruler: `2w` marks on `RC`, one per payload bit of the first table record. -/
def rcBuild (TB TMP RC : K) : Prog K (fun _ => Sym) σ :=
  .seq (movePrefix lO TB TMP optIsBit)
    (ploop lO TMP Option.isSome (.seq (mv lO TMP TB) (pushK RC .mark)))

omit [DecidableEq K] in
theorem closed_rcBuild (TB TMP RC : K) : (rcBuild lO TB TMP RC).Closed :=
  ⟨closed_movePrefix lO TB TMP _, closed_ploop lO TMP _ ⟨closed_mv lO TMP TB, closed_pushK RC _⟩⟩

theorem runs_rcBuild {TB TMP RC : K} (h1 : TB ≠ TMP) (h2 : TB ≠ RC) (h3 : TMP ≠ RC)
    (S : K → List Sym) (p : List Bool) (rest : List Sym)
    (hS : S TB = p.map Sym.bit ++ Sym.sep :: rest) (hT : S TMP = []) (hR : S RC = []) :
    Runs (rcBuild lO TB TMP RC) S (Function.update S RC (List.replicate p.length .mark))
      (fun _ => True) (9 * p.length + 4) := by
  have e1 := runs_movePrefix lO h1 optIsBit S _ _ hS (bits_optIsBit p) rfl
  rw [hT, List.append_nil] at e1
  set L := (p.map Sym.bit).reverse with hL
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (Function.update S TB
      ((L.take i).reverse ++ Sym.sep :: rest)) TMP (L.drop i)) RC (List.replicate i .mark)
  have h0 : St 0 = Function.update (Function.update S TB (Sym.sep :: rest)) TMP L := by
    funext j
    simp only [St, Function.update_apply, List.take_zero, List.drop_zero, List.reverse_nil,
      List.nil_append, List.replicate_zero]
    split_ifs <;> simp_all
  have hloop := runs_ploop_const lO TMP Option.isSome (.seq (mv lO TMP TB) (pushK RC .mark))
    L.length St 3 ?_ ?_
  · rw [h0] at hloop
    refine runs_congr (runs_mono (runs_seq' e1 hloop) (fun _ _ => trivial)
      (by simp only [hL, List.length_reverse, List.length_map]; omega)) ?_
    have e2 : (L.take L.length).reverse = p.map Sym.bit := by
      rw [List.take_length, hL, List.reverse_reverse]
    funext j
    simp only [St, Function.update_apply, e2, List.drop_length, hL, List.length_reverse,
      List.length_map]
    split_ifs <;> simp_all
  · intro i hi
    simp only [St, Function.update_of_ne h3, Function.update_self]
    rcases Nat.lt_or_ge i L.length with hlt | hge
    · rw [List.drop_eq_getElem_cons hlt]
      simp [hlt]
    · rw [List.drop_of_length_le hge]
      simp
      omega
  · intro i hi
    have hx : St i TMP = L[i] :: L.drop (i + 1) := by
      simp only [St, Function.update_of_ne h3, Function.update_self]
      exact List.drop_eq_getElem_cons hi
    have e2 := runs_mv lO h1.symm (St i) hx
    have e3 := runs_pushK (σ := σ) RC .mark (Function.update (Function.update (St i) TMP
      (L.drop (i + 1))) TB (L[i] :: St i TB))
    refine runs_congr (runs_mono (runs_seq' e2 e3) (fun _ _ => trivial) le_rfl) ?_
    have ht : (L.take (i + 1)).reverse = L[i] :: (L.take i).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      simp
    funext j
    simp only [St, Function.update_apply, ht, List.replicate_succ]
    split_ifs <;> simp_all

/-- Count the units (of `|RC|` bits) of the first data record onto `HF` (the record is
restored). -/
def hfCount (D TMP RC RA HF : K) : Prog K (fun _ => Sym) σ :=
  .seq (ploop lO D optIsBit (.seq (rmove lO D TMP RC RA) (pushK HF .mark)))
    (movePrefix lO TMP D Option.isSome)

omit [DecidableEq K] in
theorem closed_hfCount (D TMP RC RA HF : K) : (hfCount lO D TMP RC RA HF).Closed :=
  ⟨closed_ploop lO D _ ⟨closed_rmove lO D TMP RC RA, closed_pushK HF _⟩,
    closed_movePrefix lO TMP D _⟩

theorem runs_hfCount {D TMP RC RA HF : K} (hd : [D, TMP, RC, RA, HF].Nodup) (S : K → List Sym)
    (p : List Bool) (rest : List Sym) (k n : ℕ) (hn : 1 ≤ n) (hp : p.length = k * n)
    (hS : S D = p.map Sym.bit ++ Sym.sep :: rest) (hT : S TMP = [])
    (hR : S RC = List.replicate n .mark) (hA : S RA = []) (hF : S HF = []) :
    Runs (hfCount lO D TMP RC RA HF) S (Function.update S HF (List.replicate k .mark))
      (fun _ => True) (k * (10 * n + 5 + 2) + 2 + (4 * (k * n) + 2)) := by
  have p0 := List.pairwise_cons.1 hd
  have h_D_TMP : D ≠ TMP := p0.1 TMP (by simp)
  have h_D_RC : D ≠ RC := p0.1 RC (by simp)
  have h_D_RA : D ≠ RA := p0.1 RA (by simp)
  have h_D_HF : D ≠ HF := p0.1 HF (by simp)
  have p1 := List.pairwise_cons.1 p0.2
  have h_TMP_RC : TMP ≠ RC := p1.1 RC (by simp)
  have h_TMP_RA : TMP ≠ RA := p1.1 RA (by simp)
  have h_TMP_HF : TMP ≠ HF := p1.1 HF (by simp)
  have p2 := List.pairwise_cons.1 p1.2
  have h_RC_RA : RC ≠ RA := p2.1 RA (by simp)
  have h_RC_HF : RC ≠ HF := p2.1 HF (by simp)
  have p3 := List.pairwise_cons.1 p2.2
  have h_RA_HF : RA ≠ HF := p3.1 HF (by simp)
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (Function.update S D
      ((p.drop (i * n)).map Sym.bit ++ Sym.sep :: rest)) TMP
      ((p.take (i * n)).map Sym.bit).reverse) HF (List.replicate i .mark)
  have h0 : St 0 = S := by
    funext j
    simp only [St, Function.update_apply, Nat.zero_mul, List.drop_zero, List.take_zero,
      List.map_nil, List.reverse_nil, List.replicate_zero]
    split_ifs <;> simp_all
  have hloop := runs_ploop_const lO D optIsBit (.seq (rmove lO D TMP RC RA) (pushK HF .mark)) k
    St (10 * n + 5) ?_ ?_
  · rw [h0] at hloop
    have hkn : p.drop (k * n) = [] := List.drop_of_length_le (by omega)
    have hkn' : p.take (k * n) = p := List.take_of_length_le (by omega)
    have hT' : St k TMP = (p.map Sym.bit).reverse ++ [] := by
      simp only [St, Function.update_of_ne h_TMP_HF, Function.update_self, hkn', List.append_nil]
    have e2 := runs_movePrefix lO h_D_TMP.symm Option.isSome (St k) _ [] hT' (by simp) rfl
    refine runs_congr (runs_mono (runs_seq hloop e2) (fun _ _ => trivial)
      (by simp only [List.length_reverse, List.length_map, hp]; omega)) ?_
    funext j
    simp only [St, Function.update_apply, hkn, hkn', List.map_nil, List.nil_append,
      List.reverse_reverse]
    split_ifs <;> simp_all
  · intro i hi
    simp only [St, Function.update_of_ne h_D_HF, Function.update_of_ne h_D_TMP,
      Function.update_self]
    rcases Nat.lt_or_ge i k with hlt | hge
    · have hl : i * n < p.length := by rw [hp]; exact Nat.mul_lt_mul_of_pos_right hlt hn
      rw [List.drop_eq_getElem_cons hl, List.map_cons, List.cons_append, List.head?_cons]
      exact (decide_eq_true hlt).symm
    · have hl : p.length ≤ i * n := by rw [hp]; exact Nat.mul_le_mul_right n hge
      rw [List.drop_of_length_le hl]
      simp [optIsBit]
      omega
  · intro i hi
    have hjn : (i + 1) * n ≤ k * n := Nat.mul_le_mul_right n hi
    rw [Nat.add_mul, one_mul] at hjn
    have hla : ((p.drop (i * n)).take n).length = n := by
      rw [List.length_take, List.length_drop]; omega
    have hD1 : St i D = ((p.drop (i * n)).take n).map Sym.bit ++
        (((p.drop (i * n)).drop n).map Sym.bit ++ Sym.sep :: rest) := by
      simp only [St, Function.update_of_ne h_D_HF, Function.update_of_ne h_D_TMP,
        Function.update_self]
      rw [← List.append_assoc, ← List.map_append, List.take_append_drop]
    have e1 := runs_rmove lO h_D_TMP h_D_RC h_D_RA h_TMP_RC h_TMP_RA h_RC_RA (St i) _ _
      (by rw [List.length_map, hla]
          simp only [St, Function.update_of_ne h_RC_HF, Function.update_of_ne h_TMP_RC.symm,
            Function.update_of_ne h_D_RC.symm, hR])
      (by simp only [St, Function.update_of_ne h_RA_HF, Function.update_of_ne h_TMP_RA.symm,
            Function.update_of_ne h_D_RA.symm, hA]) hD1
    have e2 := runs_pushK (σ := σ) HF .mark (Function.update (Function.update (St i) D
      (((p.drop (i * n)).drop n).map Sym.bit ++ Sym.sep :: rest)) TMP
      ((((p.drop (i * n)).take n).map Sym.bit).reverse ++ St i TMP))
    refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial)
      (by rw [List.length_map, hla])) ?_
    have hdr : (p.drop (i * n)).drop n = p.drop ((i + 1) * n) := by
      rw [List.drop_drop, Nat.add_mul, one_mul]
    have htk : (((p.drop (i * n)).take n).map Sym.bit).reverse ++
        ((p.take (i * n)).map Sym.bit).reverse = ((p.take ((i + 1) * n)).map Sym.bit).reverse := by
      rw [← List.reverse_append, ← List.map_append, Nat.add_mul, one_mul, List.take_add]
    funext j
    simp only [St, Function.update_apply, hdr, List.replicate_succ]
    split_ifs <;> simp_all [← htk]

end Setup


/-! ## Width guards and shapes of every level (value level) -/

section Fits

theorem zipWith_cinterBits (w k : ℕ) :
    ∀ (A Bb : List (List CInt)), A.length = Bb.length → (∀ r ∈ A, r.length = k) →
      (∀ r ∈ Bb, r.length = k) →
      List.zipWith (cinterBits (2 * w) k) (A.map (crecBits w)) (Bb.map (crecBits w)) =
        (List.zipWith inter A Bb).map (crecBits w)
  | [], [], _, _, _ => rfl
  | a :: A, b :: Bb, hl, hA, hB => by
    have ha := hA a List.mem_cons_self
    have hb := hB b List.mem_cons_self
    simp only [List.map_cons, List.zipWith_cons_cons]
    rw [zipWith_cinterBits w k A Bb (by simpa using hl) (fun r h => hA r (List.mem_cons_of_mem _ h))
      (fun r h => hB r (List.mem_cons_of_mem _ h)), ← ha, cinterBits_crecBits w a b (by rw [ha, hb])]
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

variable (q ℓ m w : ℕ) (θt : ℕ → ℂ) (z : RArr (Cube m) (2 ^ ℓ))

theorem blkF_disk (hθ : ∀ j, j < 2 * 2 ^ ℓ → OnDiskGrid q (θt j)) (hz : ArrOnDiskGrid q z)
    (s : ℕ) (hs : s ≤ ℓ) (g j : ℕ) :
    ∃ v, OnDiskGrid q v ∧ blkF q ℓ m θt z s g j = gridInt q v :=
  ⟨_, getCoeff_diskGrid (Wst_diskGrid hθ (fun k => hz _ k) s hs) _, rfl⟩

theorem fits_of_tab2 {n k : ℕ} {f : ℕ → ℕ → CInt} (hw : q + 2 ≤ w)
    (hf : ∀ i j, ∃ v, OnDiskGrid q v ∧ f i j = gridInt q v) : CArrFits w (tab2 n k f) := by
  intro cs hcs c hc
  obtain ⟨-, hmem⟩ := mem_tab2 hcs
  obtain ⟨i, -, j, -, rfl⟩ := hmem c hc
  obtain ⟨v, hv, hfv⟩ := hf i j
  rw [hfv]
  exact fits_gridInt hw hv

theorem tabInt_getD_disk (hθ : ∀ j, j < 2 * 2 ^ ℓ → OnDiskGrid q (θt j)) (i : ℕ) :
    ∃ v, OnDiskGrid q v ∧ (tabInt q ℓ θt).getD i 0 = gridInt q v := by
  by_cases hi : i < 2 * 2 ^ ℓ
  · refine ⟨θt i, hθ i hi, ?_⟩
    rw [tabInt, List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  · refine ⟨0, ⟨onGrid_zero q, by simp⟩, ?_⟩
    rw [List.getD_eq_default _ _ (by simp [tabInt]; omega)]
    simp [gridInt, Prod.ext_iff]

end Fits

/-! ## The bit-reversal pass on the level state -/

section BR

variable {Eh Ec : Type} [DecidableEq Eh] [DecidableEq Ec] {σ : Type}

/-- One bit-reversal pass: pop the pass counter, deal, merge. -/
def brBody (lO : Lens σ (Option Sym)) : Prog (KD Eh Ec) (fun _ => Sym) σ :=
  .seq (popO lO (ds .LC)) (.seq (deal lO (ds .T) (ds .Q) (ds .P))
    (cmerge lO (ds .P) (ds .Q) (ds .T) (ds .RC) (ds .RA)))

theorem closed_brBody (lO : Lens σ (Option Sym)) : (brBody (Eh := Eh) (Ec := Ec) lO).Closed :=
  ⟨closed_popO lO _, closed_deal lO _ _ _, closed_cmerge lO _ _ _ _ _⟩

theorem runs_brBody (lO : Lens σ (Option Sym)) (S0 : KD Eh Ec → List Sym) (w : ℕ) (hw : 1 ≤ w)
    (hP : S0 (ds .P) = []) (hQ : S0 (ds .Q) = [])
    (hRC : S0 (ds .RC) = List.replicate (2 * w) .mark) (hRA : S0 (ds .RA) = [])
    (A Bb : List (List CInt)) (k qc j : ℕ) (hlen : A.length = Bb.length)
    (hA : ∀ r ∈ A, r.length = k) (hB : ∀ r ∈ Bb, r.length = k) :
    Runs (brBody lO)
      (upd4 S0 (ds .T) (ds .HC) (ds .QC) (ds .LC) (carrSyms w (inter A Bb)).reverse []
        (List.replicate qc .mark) (List.replicate (j + 1) .mark))
      (upd4 S0 (ds .T) (ds .HC) (ds .QC) (ds .LC) (carrSyms w (List.zipWith inter A Bb)).reverse []
        (List.replicate qc .mark) (List.replicate j .mark))
      (fun _ => True)
      (1 + (A.length * (8 * (2 * w * k) + 10) + 2 +
        (A.length * (k * (20 * (2 * w) + 10) + 9) + 2))) := by
  have e1 := runs_popO lO (ds .LC) (upd4 S0 (ds .T) (ds .HC) (ds .QC) (ds .LC)
    (carrSyms w (inter A Bb)).reverse [] (List.replicate qc .mark) (List.replicate (j + 1) .mark))
  rw [upd4_4, upd4_set4, List.replicate_succ, List.tail_cons] at e1
  set U1 := upd4 S0 (ds .T) (ds .HC) (ds .QC) (ds .LC) (carrSyms w (inter A Bb)).reverse []
    (List.replicate qc .mark) (List.replicate j .mark) with hU1
  have hA' : ∀ p ∈ A.map (crecBits w), p.length = 2 * w * k := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
    rw [crecBits_length', hA r hr]
  have hB' : ∀ p ∈ Bb.map (crecBits w), p.length = 2 * w * k := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
    rw [crecBits_length', hB r hr]
  have e2 := runs_deal lO (T := ds .T) (Q := ds .Q) (P := ds .P) (by simp) (by simp) (by simp) U1
    (A.map (crecBits w)) (Bb.map (crecBits w)) (2 * w * k) (by simp [hlen]) hA' hB'
    (by rw [hU1, upd4_1 (by simp) (by simp) (by simp), carrSyms_eq, inter_map])
  have hU1Q : U1 (ds .Q) = [] := by simp [hU1, upd4, Function.update_apply, hQ]
  have hU1P : U1 (ds .P) = [] := by simp [hU1, upd4, Function.update_apply, hP]
  rw [hU1Q, hU1P, List.append_nil, List.append_nil] at e2
  set U2 := Function.update (Function.update (Function.update U1 (ds .T) []) (ds .Q)
    (arrSyms (Bb.map (crecBits w)))) (ds .P) (arrSyms (A.map (crecBits w))) with hU2
  have e3 := runs_cmerge lO (P := ds .P) (Q := ds .Q) (T := ds .T) (R := ds .RC) (A := ds .RA)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) U2 (A.map (crecBits w)) (Bb.map (crecBits w)) (2 * w) k (by omega)
    (by simp [hlen]) (fun p hp => by rw [hA' p hp]; ring) (fun p hp => by rw [hB' p hp]; ring)
    (by simp [hU2]) (by simp [hU2])
    (by simp [hU2, hU1, upd4, Function.update_apply, hRC])
    (by simp [hU2, hU1, upd4, Function.update_apply, hRA])
  have hU2T : U2 (ds .T) = [] := by simp [hU2]
  rw [hU2T, List.append_nil, zipWith_cinterBits w k A Bb hlen hA hB] at e3
  refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 e3)) (fun _ _ => trivial)
    (by simp only [List.length_map, le_refl])) ?_
  simp only [ds] at hP hQ
  funext x
  rcases x with (i | (d | (e | e)))
  · fin_cases i <;> simp [hU2, hU1, upd4, Function.update_apply, nD, nH, nTB, ds]
  · cases d <;> simp [hU2, hU1, upd4, Function.update_apply, ds, hP, hQ, carrSyms_eq]
  · simp [hU2, hU1, upd4, Function.update_apply, ds]
  · simp [hU2, hU1, upd4, Function.update_apply, ds]

end BR

/-! ## The program -/

section Prog

variable {Eh Ec : Type} [DecidableEq Eh] [DecidableEq Ec] {σ Rh Rc : Type}

/-- Setup: copy `q` and `w` from the header, build the unit ruler and the counters, move the
array to the working stack (reversed). -/
def setupProg (lO : Lens σ (Option Sym)) : Prog (KD Eh Ec) (fun _ => Sym) σ :=
  .seq (copyBits lO nH (ds .QS) (ds .TMP))
  (.seq (skipField lO nH (ds .TMP2))
  (.seq (skipField lO nH (ds .TMP2))
  (.seq (skipField lO nH (ds .TMP2))
  (.seq (skipField lO nH (ds .TMP2))
  (.seq (copyBits lO nH (ds .W1) (ds .TMP))
  (.seq (movePrefix lO (ds .TMP2) nH Option.isSome)
  (.seq (copyBits lO (ds .W1) (ds .W2) (ds .TMP))
  (.seq (copyBits lO (ds .W1) (ds .W3) (ds .TMP))
  (.seq (rcBuild lO nTB (ds .TMP) (ds .RC))
  (.seq (hfCount lO nD (ds .TMP) (ds .RC) (ds .RA) (ds .HF))
  (.seq (halveTo lO (ds .HF) (ds .HC))
  (.seq (pushK (ds .QC) .mark)
  (movePrefix lO nD (ds .T) isRecO)))))))))))))

/-- Cleanup: empty the counters and the width/precision copies. -/
def cleanupProg (lO : Lens σ (Option Sym)) : Prog (KD Eh Ec) (fun _ => Sym) σ :=
  .seq (drain lO (ds .RC)) (.seq (drain lO (ds .W1)) (.seq (drain lO (ds .W2))
    (.seq (drain lO (ds .W3)) (.seq (drain lO (ds .QS)) (drain lO (ds .QC))))))

/-- **The record DIF kernel.** -/
def mainProg (lO : Lens σ (Option Sym)) (lh : Lens σ Rh) (lc : Lens σ Rc)
    (Ph : Prog (KLoc (Fin 5) Eh) (fun _ => Sym) Rh) (Pc : Prog (KLoc (Fin 7) Ec) (fun _ => Sym) Rc) :
    Prog (KD Eh Ec) (fun _ => Sym) σ :=
  .seq (setupProg lO)
  (.seq (ploop lO (ds .HC) Option.isSome (levelBody lO lh lc Ph Pc))
  (.seq (ploop lO (ds .LC) Option.isSome (brBody lO))
  (.seq (movePrefix lO (ds .T) nD isRecO)
  (cleanupProg lO))))

theorem closed_mainProg (lO : Lens σ (Option Sym)) (lh : Lens σ Rh) (lc : Lens σ Rc)
    {Ph : Prog (KLoc (Fin 5) Eh) (fun _ => Sym) Rh} {Pc : Prog (KLoc (Fin 7) Ec) (fun _ => Sym) Rc}
    (hPh : Ph.Closed) (hPc : Pc.Closed) : (mainProg lO lh lc Ph Pc).Closed := by
  refine ⟨⟨closed_copyBits lO _ _ _, closed_skipField lO _ _, closed_skipField lO _ _,
    closed_skipField lO _ _, closed_skipField lO _ _, closed_copyBits lO _ _ _,
    closed_movePrefix lO _ _ _, closed_copyBits lO _ _ _, closed_copyBits lO _ _ _,
    closed_rcBuild lO _ _ _, closed_hfCount lO _ _ _ _ _, closed_halveTo lO _ _,
    closed_pushK _ _, closed_movePrefix lO _ _ _⟩,
    closed_ploop lO _ _ (closed_levelBody lO lh lc hPh hPc),
    closed_ploop lO _ _ (closed_brBody lO), closed_movePrefix lO _ _ _,
    closed_drain lO _, closed_drain lO _, closed_drain lO _, closed_drain lO _,
    closed_drain lO _, closed_drain lO _⟩

/-- The base state reached by the setup (before the array is moved). -/
def baseState (S : KD Eh Ec → List Sym) (w q : ℕ) (rest : List Sym) : KD Eh Ec → List Sym :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update S (ds .QS) (natSyms q)) (ds .W1) (natSyms w)) (ds .W2) (natSyms w))
    (ds .W3) (natSyms w)) (ds .RC) (List.replicate (2 * w) .mark)) nD rest

end Prog

/-! ## The setup -/

section SetupRuns

variable {Eh Ec : Type} [DecidableEq Eh] [DecidableEq Ec] {σ : Type}

/-- Cost of the setup. -/
def setupCost (q f1 f2 f3 w ℓ V : ℕ) : ℕ :=
  (9 * bitLen q + 4) + ((4 * bitLen q + 4) + ((4 * bitLen f1 + 4) + ((4 * bitLen f2 + 4) +
  ((4 * bitLen f3 + 4) + ((9 * bitLen w + 4) +
  ((4 * (bitLen q + bitLen f1 + bitLen f2 + bitLen f3 + 4) + 2) + ((9 * bitLen w + 4) +
  ((9 * bitLen w + 4) + ((9 * (2 * w) + 4) +
  ((2 ^ ℓ * (10 * (2 * w) + 5 + 2) + 2 + (4 * (2 ^ ℓ * (2 * w)) + 2)) +
  ((3 * 2 ^ ℓ + 5) + (1 + (4 * V + 2)))))))))))))

theorem natSyms_bits (n : ℕ) : natSyms n = (Computability.encodeNat n).map Sym.bit := rfl

theorem termOK_mark (l : List Sym) : TermOK (Sym.mark :: l) := TermOK.cons rfl _

set_option maxHeartbeats 4000000 in
theorem runs_setup (lO : Lens σ (Option Sym)) (S : KD Eh Ec → List Sym)
    (hclean : ∀ d : DS, S (ds d) = []) (q f1 f2 f3 w ℓ : ℕ) (hr : List Sym) (hw : 1 ≤ w)
    (B0 : List (List CInt)) (row0 : List CInt) (Brest : List (List CInt))
    (hB0 : B0 = row0 :: Brest) (hrow0 : row0.length = 2 ^ ℓ) (c0 : CInt)
    (rest trest : List Sym) (hrest : BlkTerm rest)
    (hD : S nD = carrSyms w B0 ++ rest)
    (hH : S nH = natSyms q ++ Sym.mark :: (natSyms f1 ++ Sym.mark :: (natSyms f2 ++ Sym.mark ::
      (natSyms f3 ++ Sym.mark :: (natSyms w ++ Sym.mark :: hr)))))
    (hTB : S nTB = (crecBits w [c0]).map Sym.bit ++ Sym.sep :: trest) :
    Runs (setupProg lO) S (lvState (baseState S w q rest) w B0 (2 ^ ℓ / 2) 1 0) (fun _ => True)
      (setupCost q f1 f2 f3 w ℓ (carrSyms w B0).length) := by
  have cl : ∀ d : DS, S (Sum.inr (Sum.inl d)) = [] := fun d => hclean d
  -- 1. copy `q`
  have e1 := runs_copyBits lO (src := nH) (dst := ds .QS) (tmp := ds .TMP) (by simp) (by simp)
    (by simp) S (Computability.encodeNat q) _ (by rw [hH]; rfl) (termOK_mark _)
    (by rw [hclean]; exact TermOK.nil)
  rw [hclean, List.append_nil, ← natSyms_bits] at e1
  set A1 := Function.update S (ds .QS) (natSyms q) with hA1
  -- 2-5. skip four fields
  have e2 := runs_skipField lO (src := nH) (dst := ds .TMP2) (by simp) A1 q
    (natSyms f1 ++ Sym.mark :: (natSyms f2 ++ Sym.mark :: (natSyms f3 ++ Sym.mark ::
      (natSyms w ++ Sym.mark :: hr)))) (by simp [hA1, hH])
  set A2 := Function.update (Function.update A1 nH (natSyms f1 ++ Sym.mark :: (natSyms f2 ++
    Sym.mark :: (natSyms f3 ++ Sym.mark :: (natSyms w ++ Sym.mark :: hr))))) (ds .TMP2)
    (Sym.mark :: ((natSyms q).reverse ++ A1 (ds .TMP2))) with hA2
  have e3 := runs_skipField lO (src := nH) (dst := ds .TMP2) (by simp) A2 f1
    (natSyms f2 ++ Sym.mark :: (natSyms f3 ++ Sym.mark :: (natSyms w ++ Sym.mark :: hr)))
    (by simp [hA2])
  set A3 := Function.update (Function.update A2 nH (natSyms f2 ++ Sym.mark :: (natSyms f3 ++
    Sym.mark :: (natSyms w ++ Sym.mark :: hr)))) (ds .TMP2)
    (Sym.mark :: ((natSyms f1).reverse ++ A2 (ds .TMP2))) with hA3
  have e4 := runs_skipField lO (src := nH) (dst := ds .TMP2) (by simp) A3 f2
    (natSyms f3 ++ Sym.mark :: (natSyms w ++ Sym.mark :: hr)) (by simp [hA3])
  set A4 := Function.update (Function.update A3 nH (natSyms f3 ++
    Sym.mark :: (natSyms w ++ Sym.mark :: hr))) (ds .TMP2)
    (Sym.mark :: ((natSyms f2).reverse ++ A3 (ds .TMP2))) with hA4
  have e5 := runs_skipField lO (src := nH) (dst := ds .TMP2) (by simp) A4 f3
    (natSyms w ++ Sym.mark :: hr) (by simp [hA4])
  set A5 := Function.update (Function.update A4 nH (natSyms w ++ Sym.mark :: hr)) (ds .TMP2)
    (Sym.mark :: ((natSyms f3).reverse ++ A4 (ds .TMP2))) with hA5
  -- 6. copy `w`
  have e6 := runs_copyBits lO (src := nH) (dst := ds .W1) (tmp := ds .TMP) (by simp) (by simp)
    (by simp) A5 (Computability.encodeNat w) _ (by simp [hA5]; rfl) (termOK_mark _)
    (by simp [hA5, hA4, hA3, hA2, hA1, cl, hclean]; exact TermOK.nil)
  have hA5W1 : A5 (ds .W1) = [] := by simp [hA5, hA4, hA3, hA2, hA1, cl, hclean]
  rw [hA5W1, List.append_nil, ← natSyms_bits] at e6
  set A6 := Function.update A5 (ds .W1) (natSyms w) with hA6
  -- 7. restore the header
  set L := Sym.mark :: ((natSyms f3).reverse ++ Sym.mark :: ((natSyms f2).reverse ++ Sym.mark ::
    ((natSyms f1).reverse ++ Sym.mark :: (natSyms q).reverse))) with hL
  have hA6T2 : A6 (ds .TMP2) = L ++ [] := by
    simp [hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean, hL]
  have e7 := runs_movePrefix lO (src := ds .TMP2) (dst := nH) (by simp) Option.isSome A6 L []
    hA6T2 (by simp [hL]) rfl
  have hA6H : A6 nH = natSyms w ++ Sym.mark :: hr := by simp [hA6, hA5]
  have hLrev : L.reverse ++ (natSyms w ++ Sym.mark :: hr) = S nH := by
    rw [hH, hL]
    simp
  rw [hA6H, hLrev] at e7
  set A7 := Function.update (Function.update A6 (ds .TMP2) []) nH (S nH) with hA7
  -- 8-9. copy `w` twice more
  have e8 := runs_copyBits lO (src := ds .W1) (dst := ds .W2) (tmp := ds .TMP) (by simp) (by simp)
    (by simp) A7 (Computability.encodeNat w) [] (by simp [hA7, hA6]; rfl) TermOK.nil
    (by simp [hA7, hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean]; exact TermOK.nil)
  have hA7W2 : A7 (ds .W2) = [] := by simp [hA7, hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean]
  rw [hA7W2, List.append_nil, ← natSyms_bits] at e8
  set A8 := Function.update A7 (ds .W2) (natSyms w) with hA8
  have e9 := runs_copyBits lO (src := ds .W1) (dst := ds .W3) (tmp := ds .TMP) (by simp) (by simp)
    (by simp) A8 (Computability.encodeNat w) [] (by simp [hA8, hA7, hA6]; rfl) TermOK.nil
    (by simp [hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean]; exact TermOK.nil)
  have hA8W3 : A8 (ds .W3) = [] := by simp [hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean]
  rw [hA8W3, List.append_nil, ← natSyms_bits] at e9
  set A9 := Function.update A8 (ds .W3) (natSyms w) with hA9
  -- 10. the unit ruler
  have e10 := runs_rcBuild lO (TB := nTB) (TMP := ds .TMP) (RC := ds .RC) (by simp) (by simp)
    (by simp) A9 (crecBits w [c0]) trest
    (by simp [hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, hTB])
    (by simp [hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean])
    (by simp [hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean])
  rw [crecBits_length', List.length_singleton, mul_one] at e10
  set A10 := Function.update A9 (ds .RC) (List.replicate (2 * w) .mark) with hA10
  -- 11. count the coefficients of the first record
  have hD' : S nD = (crecBits w row0).map Sym.bit ++ Sym.sep :: (carrSyms w Brest ++ rest) := by
    rw [hD, hB0, carrSyms_eq, List.map_cons, arrSyms_cons', recSyms_eq]
    simp [carrSyms_eq]
  have e11 := runs_hfCount lO (D := nD) (TMP := ds .TMP) (RC := ds .RC) (RA := ds .RA) (HF := ds .HF)
    (by simp [nD, ds]) A10 (crecBits w row0) (carrSyms w Brest ++ rest) (2 ^ ℓ) (2 * w)
    (by omega) (by rw [crecBits_length', hrow0]; ring)
    (by simp [hA10, hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, hD'])
    (by simp [hA10, hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean])
    (by simp [hA10])
    (by simp [hA10, hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean])
    (by simp [hA10, hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean])
  set A11 := Function.update A10 (ds .HF) (List.replicate (2 ^ ℓ) .mark) with hA11
  -- 12. half of it
  have e12 := runs_halveTo lO (src := ds .HF) (dst := ds .HC) (by simp) A11 (2 ^ ℓ) (by simp [hA11])
  have hA11HC : A11 (ds .HC) = [] := by
    simp [hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean]
  rw [hA11HC, List.append_nil] at e12
  set A12 := Function.update (Function.update A11 (ds .HF) []) (ds .HC)
    (List.replicate (2 ^ ℓ / 2) .mark) with hA12
  -- 13. the stride counter
  have e13 := runs_pushK (σ := σ) (ds .QC) .mark A12
  have hA12QC : A12 (ds .QC) = [] := by
    simp [hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean]
  rw [hA12QC] at e13
  set A13 := Function.update A12 (ds .QC) [Sym.mark] with hA13
  -- 14. the array to the working stack
  have e14 := runs_revArr_out lO (src := nD) (dst := ds .T) (by simp) A13
    (B0.map (crecBits w)) rest
    (by simp [hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, hD,
      carrSyms_eq]) hrest
  have hA13T : A13 (ds .T) = [] := by
    simp [hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, cl, hclean]
  rw [hA13T, List.append_nil, ← carrSyms_eq] at e14
  refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 (runs_seq' e3 (runs_seq' e4
    (runs_seq' e5 (runs_seq' e6 (runs_seq' e7 (runs_seq' e8 (runs_seq' e9 (runs_seq' e10
    (runs_seq' e11 (runs_seq' e12 (runs_seq' e13 e14)))))))))))))
    (fun _ _ => trivial) ?_) ?_
  · have hLl : L.length = bitLen q + bitLen f1 + bitLen f2 + bitLen f3 + 4 := by
      simp [hL, length_natSyms]
      ring
    simp only [setupCost, hLl, length_natSyms]
    rfl
  · funext x
    rcases x with (i | (d | (e | e)))
    · fin_cases i <;>
        simp [hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, lvState,
          baseState, upd4, Function.update_apply, nD, nH, nTB, ds]
    · cases d <;>
        simp [hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, lvState,
          baseState, upd4, Function.update_apply, ds, cl, hclean, nD, nH, nTB]
    · simp [hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, lvState,
        baseState, upd4, Function.update_apply, ds, nD, nH, nTB]
    · simp [hA13, hA12, hA11, hA10, hA9, hA8, hA7, hA6, hA5, hA4, hA3, hA2, hA1, lvState,
        baseState, upd4, Function.update_apply, ds, nD, nH, nTB]

end SetupRuns

end SubNLogN.Machine.FFT.DIF
