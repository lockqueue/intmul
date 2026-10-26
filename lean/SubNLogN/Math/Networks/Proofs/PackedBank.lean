import SubNLogN.Math.Networks.Proofs.PackedProc
import SubNLogN.Math.Networks.Proofs.PackedProcWF
import SubNLogN.Math.Networks.Proofs.PackedBad

/-!
# Lemma A.9 (`lem:transfer13`): the value-level bank interface of the packed repair

This file is the **value-level** interface of the repair step of `packedAddProc`
(Lemma A.9 (`lem:transfer13`)). The *bank* is the set of addresses whose chunk triple is not
`packedGood` (the support of `repairStep`). Extracting the bank, attaching destination ranks,
stable sorting, reinsertion and all costs are **machine-level obligations (`SubNLogN/Machine/`)**; here we only state and
prove the facts about values and address maps that such a machine relies on.

* `packedBank`, `repairPull` (the pull `addrS0 ∘ addrT0` of `repairStep`, `repairStep_eq`);
* (i) `repairPull_of_not_mem`: the pull is the identity off the bank;
  `repairPull_bijOn`: it maps the bank bijectively onto itself;
* (ii) an explicit forward destination map `repairFwd = addrT0 ∘ addrS0inv`, where `addrS0inv`
  applies the eight packed lines in reverse order with negated offsets (`packedS0inv`), and
  `repairFwd_pull`, `repairPull_fwd`: the two maps are mutually inverse;
* (iii) `packedBank_card_class`: in every row class whose row field lies outside the three chunks,
  `2^K · #(bank ∩ c) ≤ 80(f−1) · #c` (from `packedBadCard_holds`, fiberwise over the non-chunk
  fields).
-/

namespace SubNLogN.Math.Networks

open Model

/-- The bank of the packed repair: addresses whose chunk triple is not `packedGood`
(the support of `repairStep`). -/
noncomputable def packedBank (Ly : Layout) (L K ρ f : ℕ) (C : Chunks3) : Finset Ly.Addr :=
  open Classical in Finset.univ.filter fun a => ¬ packedGood K ρ f (chunkVals L C a)

/-- The pull of the repair step: `addrS0 ∘ addrT0`. -/
def repairPull {Ly : Layout} (L K ρ f : ℕ) (C : Chunks3) (a : Ly.Addr) : Ly.Addr :=
  addrS0 L K ρ f C (addrT0 L K ρ f C a)

/-- Negated offset of a packed line. -/
def negOp (op : Bool × ℤ × ℕ) : Bool × ℤ × ℕ := (op.1, -op.2.1, op.2.2)

/-- The inverse of the eight packed lines on chunk values: the lines in reverse order with negated
offsets. -/
def packedS0inv (L K ρ f : ℕ) (xyz : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  eightOps.reverse.foldl (fun p op => packedLine L K ρ f (negOp op) p) xyz

/-- The inverse of `addrS0` on addresses. -/
def addrS0inv {Ly : Layout} (L K ρ f : ℕ) (C : Chunks3) (a : Ly.Addr) : Ly.Addr :=
  Ly.blockSet C.pz (C.pz + L)
    (Ly.blockSet C.py (C.py + L) a (packedS0inv L K ρ f (chunkVals L C a)).2.1)
    (packedS0inv L K ρ f (chunkVals L C a)).2.2

/-- The forward destination map of the repair: `addrT0 ∘ addrS0inv`. -/
def repairFwd {Ly : Layout} (L K ρ f : ℕ) (C : Chunks3) (a : Ly.Addr) : Ly.Addr :=
  addrT0 L K ρ f C (addrS0inv L K ρ f C a)

theorem repairStep_eq {Ly : Layout} {β : Type} (L K ρ f : ℕ) (C : Chunks3) :
    repairStep (Ly := Ly) (β := β) L K ρ f C =
      Step.sparsePerm (repairPull L K ρ f C) (packedBank Ly L K ρ f C) := rfl

namespace PackedBankAux

open PackedProcAux

variable {Ly : Layout} {L K ρ f : ℕ} {C : Chunks3}

/-- A bijection that is the identity off `S` maps `S` bijectively onto itself. -/
theorem bijOn_of_bijective_of_fix {α : Type*} (g : α → α) (S : Set α) (hb : Function.Bijective g)
    (hfix : ∀ x, x ∉ S → g x = x) : Set.BijOn g S S := by
  refine ⟨fun x hx => ?_, hb.1.injOn, fun y hy => ?_⟩
  · by_contra hgx
    have h1 : g (g x) = g x := hfix _ hgx
    have h2 : g x = x := hb.1 h1
    exact hgx (by rw [h2]; exact hx)
  · obtain ⟨x, rfl⟩ := hb.2 y
    refine ⟨x, ?_, rfl⟩
    by_contra hx
    have h3 := hfix x hx
    rw [h3] at hy
    exact hx hy

end PackedBankAux

/-- (i) The repair pull is the identity off the bank. -/
theorem repairPull_of_not_mem {Ly : Layout} {L K ρ f : ℕ} {C : Chunks3}
    (hP : PackedHyps Ly L K ρ f C) (a : Ly.Addr) (ha : a ∉ packedBank Ly L K ρ f C) :
    repairPull L K ρ f C a = a :=
  (PackedProcWFAux.repairStep_WF (β := Unit) packedAgree_holds hP
    (PackedProcWFAux.chunkFacts_of_hyps hP)).2 a ha

/-- (i) The repair pull maps the bank bijectively onto itself. -/
theorem repairPull_bijOn {Ly : Layout} {L K ρ f : ℕ} {C : Chunks3}
    (hP : PackedHyps Ly L K ρ f C) :
    Set.BijOn (repairPull L K ρ f C) (packedBank Ly L K ρ f C : Set Ly.Addr)
      (packedBank Ly L K ρ f C : Set Ly.Addr) :=
  PackedBankAux.bijOn_of_bijective_of_fix _ _
    (PackedProcWFAux.repairStep_WF (β := Unit) packedAgree_holds hP
      (PackedProcWFAux.chunkFacts_of_hyps hP)).1
    (fun a ha => repairPull_of_not_mem hP a (by simpa using ha))

namespace PackedBankAux

open PackedProcAux

variable {Ly : Layout} {L K ρ f : ℕ} {C : Chunks3}

/-! ### (ii) The inverse of the eight packed lines -/

theorem negOp_negOp (op : Bool × ℤ × ℕ) : negOp (negOp op) = op := by
  obtain ⟨a, b, c⟩ := op
  simp [negOp]

theorem toNat_cancel {y : ℕ} (hy : y < 2 ^ L) (s : ℤ) :
    (((((((y : ℤ) + s) % (2 : ℤ) ^ L).toNat : ℕ) : ℤ) + -s) % (2 : ℤ) ^ L).toNat = y := by
  have hR : (0 : ℤ) < (2 : ℤ) ^ L := by positivity
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hR.ne'), Int.emod_add_emod,
    show (y : ℤ) + s + -s = y by ring, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hy)]
  simp

/-- A packed line followed by the same line with negated offset is the identity (on chunks below
`2^L`): the offset only reads the control and the other chunk, which the line does not change. -/
theorem packedLine_negOp_cancel (op : Bool × ℤ × ℕ) (xyz : ℕ × ℕ × ℕ) (h2 : xyz.2.1 < 2 ^ L)
    (h3 : xyz.2.2 < 2 ^ L) :
    packedLine L K ρ f (negOp op) (packedLine L K ρ f op xyz) = xyz := by
  obtain ⟨x, y, z⟩ := xyz
  obtain ⟨isY, ε, par⟩ := op
  cases isY with
  | true =>
    simp only [packedLine, negOp, ite_true]
    rw [neg_mul, toNat_cancel h2]
  | false =>
    simp only [packedLine, negOp, ite_false, Bool.false_eq_true]
    rw [neg_mul, toNat_cancel h3]

theorem packedLine_rect (op : Bool × ℤ × ℕ) {xyz : ℕ × ℕ × ℕ} (h : xyz ∈ packedRect L) :
    packedLine L K ρ f op xyz ∈ packedRect L :=
  packedLine_lt op h.1 h.2.1 h.2.2

theorem foldl_rect (ops : List (Bool × ℤ × ℕ)) (g : Bool × ℤ × ℕ → Bool × ℤ × ℕ)
    {xyz : ℕ × ℕ × ℕ} (h : xyz ∈ packedRect L) :
    ops.foldl (fun p op => packedLine L K ρ f (g op) p) xyz ∈ packedRect L := by
  induction ops generalizing xyz with
  | nil => exact h
  | cons op ops ih => exact ih (packedLine_rect (g op) h)

theorem foldl_inv_fwd (ops : List (Bool × ℤ × ℕ)) {xyz : ℕ × ℕ × ℕ} (h : xyz ∈ packedRect L) :
    ops.reverse.foldl (fun p op => packedLine L K ρ f (negOp op) p)
      (ops.foldl (fun p op => packedLine L K ρ f op p) xyz) = xyz := by
  induction ops generalizing xyz with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (packedLine_rect op h)]
    exact packedLine_negOp_cancel op xyz h.2.1 h.2.2

theorem foldl_fwd_inv (ops : List (Bool × ℤ × ℕ)) {xyz : ℕ × ℕ × ℕ} (h : xyz ∈ packedRect L) :
    ops.foldl (fun p op => packedLine L K ρ f op p)
      (ops.reverse.foldl (fun p op => packedLine L K ρ f (negOp op) p) xyz) = xyz := by
  induction ops generalizing xyz with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hw := foldl_rect (L := L) (K := K) (ρ := ρ) (f := f) ops.reverse negOp h
    have hc := packedLine_negOp_cancel (L := L) (K := K) (ρ := ρ) (f := f) (negOp op)
      (List.foldl (fun p op => packedLine L K ρ f (negOp op) p) xyz ops.reverse) hw.2.1 hw.2.2
    rw [negOp_negOp] at hc
    rw [hc, ih h]

theorem packedS0inv_packedS0 {xyz : ℕ × ℕ × ℕ} (h : xyz ∈ packedRect L) :
    packedS0inv L K ρ f (packedS0 L K ρ f xyz) = xyz :=
  foldl_inv_fwd eightOps h

theorem packedS0_packedS0inv {xyz : ℕ × ℕ × ℕ} (h : xyz ∈ packedRect L) :
    packedS0 L K ρ f (packedS0inv L K ρ f xyz) = xyz :=
  foldl_fwd_inv eightOps h

theorem packedS0inv_fst (xyz : ℕ × ℕ × ℕ) : (packedS0inv L K ρ f xyz).1 = xyz.1 := by
  unfold packedS0inv
  generalize eightOps.reverse = ops
  induction ops generalizing xyz with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.foldl_cons]
    rw [ih, packedLine_fst]

theorem chunkVals_rect (G : Geo Ly L C) (a : Ly.Addr) : chunkVals L C a ∈ packedRect L :=
  ⟨chunkVal_lt G.hx a, chunkVal_lt G.hy a, chunkVal_lt G.hz a⟩

theorem addrS0inv_eq (a : Ly.Addr) :
    addrS0inv L K ρ f C a = setChunks L C a (packedS0inv L K ρ f (chunkVals L C a)) := by
  have h1 : (packedS0inv L K ρ f (chunkVals L C a)).1 = chunkVal L C.px a := packedS0inv_fst _
  have h2 : Ly.blockSet C.px (C.px + L) a (chunkVal L C.px a) = a := blockSet_blockVal _ _ a
  unfold addrS0inv setChunks
  rw [h1, h2]

theorem addrS0inv_addrS0 (G : Geo Ly L C) (a : Ly.Addr) :
    addrS0inv L K ρ f C (addrS0 L K ρ f C a) = a := by
  have hr : packedS0 L K ρ f (chunkVals L C a) ∈ packedRect L :=
    foldl_rect (L := L) (K := K) (ρ := ρ) (f := f) eightOps id (chunkVals_rect G a)
  rw [addrS0inv_eq, addrS0_eq, chunkVals_setChunks G _ hr.1 hr.2.1 hr.2.2,
    packedS0inv_packedS0 (chunkVals_rect G a), setChunks_setChunks G, setChunks_self G]

theorem addrS0_addrS0inv (G : Geo Ly L C) (a : Ly.Addr) :
    addrS0 L K ρ f C (addrS0inv L K ρ f C a) = a := by
  have hr : packedS0inv L K ρ f (chunkVals L C a) ∈ packedRect L :=
    foldl_rect (L := L) (K := K) (ρ := ρ) (f := f) eightOps.reverse negOp (chunkVals_rect G a)
  rw [addrS0_eq, addrS0inv_eq, chunkVals_setChunks G _ hr.1 hr.2.1 hr.2.2,
    packedS0_packedS0inv (chunkVals_rect G a), setChunks_setChunks G, setChunks_self G]

end PackedBankAux

/-- (ii) The forward destination map inverts the repair pull: `repairFwd ∘ repairPull = id`. -/
theorem repairFwd_pull {Ly : Layout} {L K ρ f : ℕ} {C : Chunks3}
    (hP : PackedHyps Ly L K ρ f C) (a : Ly.Addr) :
    repairFwd L K ρ f C (repairPull L K ρ f C a) = a := by
  have G := PackedProcAux.geo_of_hyps hP
  have hF := PackedProcWFAux.chunkFacts_of_hyps hP
  obtain ⟨hK, hL, hρ, -⟩ := hP
  unfold repairFwd repairPull
  rw [PackedBankAux.addrS0inv_addrS0 G, PackedProcWFAux.addrT0_invol hF (by omega) hL hρ]

/-- (ii) The repair pull inverts the forward destination map: `repairPull ∘ repairFwd = id`. -/
theorem repairPull_fwd {Ly : Layout} {L K ρ f : ℕ} {C : Chunks3}
    (hP : PackedHyps Ly L K ρ f C) (a : Ly.Addr) :
    repairPull L K ρ f C (repairFwd L K ρ f C a) = a := by
  have G := PackedProcAux.geo_of_hyps hP
  have hF := PackedProcWFAux.chunkFacts_of_hyps hP
  obtain ⟨hK, hL, hρ, -⟩ := hP
  unfold repairFwd repairPull
  rw [PackedProcWFAux.addrT0_invol hF (by omega) hL hρ, PackedBankAux.addrS0_addrS0inv G]
namespace PackedBankAux

open PackedProcAux

variable {Ly : Layout} {L K ρ f : ℕ} {C : Chunks3}

/-! ### (iii) Fiberwise counting over the non-chunk fields -/

/-- The non-chunk part of an address (the three chunks set to `0`). -/
def outPart (L : ℕ) (C : Chunks3) (a : Ly.Addr) : Ly.Addr := setChunks L C a (0, 0, 0)

theorem setChunks_outPart (G : Geo Ly L C) (a : Ly.Addr) (v : ℕ × ℕ × ℕ) :
    setChunks L C (outPart L C a) v = setChunks L C a v :=
  setChunks_setChunks G a _ v

theorem outPart_setChunks (G : Geo Ly L C) (a : Ly.Addr) (v : ℕ × ℕ × ℕ) :
    outPart L C (setChunks L C a v) = outPart L C a :=
  setChunks_setChunks G a v _

theorem mem_setChunks (c : RowClass Ly) (hrow : Out3 L C c.row.val) (a : Ly.Addr)
    (v : ℕ × ℕ × ℕ) : c.mem (setChunks L C a v) ↔ c.mem a := by
  unfold RowClass.mem
  rw [setChunks_apply_out a v c.row hrow]

/-- The full rectangle of chunk triples, as a `Finset`. -/
def rectF (L : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.range (2 ^ L) ×ˢ Finset.range (2 ^ L) ×ˢ Finset.range (2 ^ L)

theorem mem_rectF {v : ℕ × ℕ × ℕ} :
    v ∈ rectF L ↔ v.1 < 2 ^ L ∧ v.2.1 < 2 ^ L ∧ v.2.2 < 2 ^ L := by
  simp only [rectF, Finset.mem_product, Finset.mem_range]

theorem card_rectF : (rectF L).card = 2 ^ (3 * L) := by
  simp only [rectF, Finset.card_product, Finset.card_range]
  ring

open Classical in
/-- The bad chunk triples (as in `PackedBadCardStmt`). -/
noncomputable def badF (L K ρ f : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (2 ^ L) ×ˢ Finset.range (2 ^ L) ×ˢ Finset.range (2 ^ L)).filter
    (fun xyz => ¬ packedGood K ρ f xyz)

open Classical in
theorem mem_badF {v : ℕ × ℕ × ℕ} : v ∈ badF L K ρ f ↔ v ∈ rectF L ∧ ¬ packedGood K ρ f v := by
  unfold badF rectF
  exact Finset.mem_filter

open Classical in
theorem mem_packedBank (a : Ly.Addr) :
    a ∈ packedBank Ly L K ρ f C ↔ ¬ packedGood K ρ f (chunkVals L C a) := by
  unfold packedBank
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ a, h⟩⟩

theorem fiber_bank_card (G : Geo Ly L C) (c : RowClass Ly) (hrow : Out3 L C c.row.val)
    (b : Ly.Addr) (hb : c.mem b) :
    (((packedBank Ly L K ρ f C).filter c.mem).filter (fun a => outPart L C a = outPart L C b)).card =
      (badF L K ρ f).card := by
  refine Finset.card_nbij' (chunkVals L C) (setChunks L C b) ?_ ?_ ?_ ?_
  · intro a ha
    have ha1 := Finset.mem_filter.mp ha
    have ha2 := Finset.mem_filter.mp ha1.1
    exact mem_badF.mpr ⟨mem_rectF.mpr (chunkVals_rect G a), (mem_packedBank a).mp ha2.1⟩
  · intro v hv
    have hv1 := mem_badF.mp hv
    have hv' := mem_rectF.mp hv1.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(mem_packedBank _).mpr ?_,
      (mem_setChunks c hrow b v).mpr hb⟩, outPart_setChunks G b v⟩
    rw [chunkVals_setChunks G b hv'.1 hv'.2.1 hv'.2.2]
    exact hv1.2
  · intro a ha
    have ha1 := Finset.mem_filter.mp ha
    rw [← setChunks_outPart G b, ← ha1.2, setChunks_outPart G a, setChunks_self G]
  · intro v hv
    have hv' := mem_rectF.mp (mem_badF.mp hv).1
    exact chunkVals_setChunks G b hv'.1 hv'.2.1 hv'.2.2

theorem fiber_class_card (G : Geo Ly L C) (c : RowClass Ly) (hrow : Out3 L C c.row.val)
    (b : Ly.Addr) (hb : c.mem b) :
    ((Finset.univ.filter c.mem).filter (fun a => outPart L C a = outPart L C b)).card =
      (rectF L).card := by
  refine Finset.card_nbij' (chunkVals L C) (setChunks L C b) ?_ ?_ ?_ ?_
  · intro a _
    exact mem_rectF.mpr (chunkVals_rect G a)
  · intro v _
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (mem_setChunks c hrow b v).mpr hb⟩, outPart_setChunks G b v⟩
  · intro a ha
    have ha1 := Finset.mem_filter.mp ha
    rw [← setChunks_outPart G b, ← ha1.2, setChunks_outPart G a, setChunks_self G]
  · intro v hv
    have hv' := mem_rectF.mp hv
    exact chunkVals_setChunks G b hv'.1 hv'.2.1 hv'.2.2

end PackedBankAux

/-- (iii) **Class-filtered bank size**: in every row class whose row field lies outside the three
chunks, `2^K · #(bank ∩ c) ≤ 80(f−1) · #c` (every fiber of the non-chunk fields is a full rectangle
of chunk triples, where `packedBadCard_holds` applies). -/
theorem packedBank_card_class {Ly : Layout} {L K ρ f : ℕ} {C : Chunks3}
    (hP : PackedHyps Ly L K ρ f C) (c : RowClass Ly)
    (hcx : c.row.val < C.px ∨ C.px + L ≤ c.row.val) (hcy : c.row.val < C.py ∨ C.py + L ≤ c.row.val)
    (hcz : c.row.val < C.pz ∨ C.pz + L ≤ c.row.val) :
    2 ^ K * ((packedBank Ly L K ρ f C).filter c.mem).card ≤
      80 * (f - 1) * (Finset.univ.filter c.mem).card := by
  have G := PackedProcAux.geo_of_hyps hP
  have hrow : PackedProcAux.Out3 L C c.row.val := ⟨by omega, by omega, by omega⟩
  obtain ⟨hK, hL, hρ, -⟩ := hP
  set t := (Finset.univ.filter c.mem).image (PackedBankAux.outPart L C) with ht
  have hmapB : ∀ a ∈ (packedBank Ly L K ρ f C).filter c.mem, PackedBankAux.outPart L C a ∈ t :=
    fun a ha => Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, (Finset.mem_filter.mp ha).2⟩, rfl⟩
  have hmapC : ∀ a ∈ Finset.univ.filter c.mem, PackedBankAux.outPart L C a ∈ t :=
    fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hfibB : ∀ o ∈ t, (((packedBank Ly L K ρ f C).filter c.mem).filter
      (fun a => PackedBankAux.outPart L C a = o)).card = (PackedBankAux.badF L K ρ f).card := by
    intro o ho
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ho
    exact PackedBankAux.fiber_bank_card G c hrow b (Finset.mem_filter.mp hb).2
  have hfibC : ∀ o ∈ t, ((Finset.univ.filter c.mem).filter
      (fun a => PackedBankAux.outPart L C a = o)).card = (PackedBankAux.rectF L).card := by
    intro o ho
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ho
    exact PackedBankAux.fiber_class_card G c hrow b (Finset.mem_filter.mp hb).2
  have h1 : ((packedBank Ly L K ρ f C).filter c.mem).card =
      t.card * (PackedBankAux.badF L K ρ f).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmapB, Finset.sum_const_nat hfibB]
  have h2 : (Finset.univ.filter c.mem).card = t.card * (PackedBankAux.rectF L).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmapC, Finset.sum_const_nat hfibC]
  have hbad : 2 ^ K * (PackedBankAux.badF L K ρ f).card ≤ 80 * (f - 1) * 2 ^ (3 * L) :=
    packedBadCard_holds L K ρ f hK hL hρ
  rw [h1, h2, PackedBankAux.card_rectF]
  calc 2 ^ K * (t.card * (PackedBankAux.badF L K ρ f).card)
      = t.card * (2 ^ K * (PackedBankAux.badF L K ρ f).card) := by ring
    _ ≤ t.card * (80 * (f - 1) * 2 ^ (3 * L)) := Nat.mul_le_mul_left _ hbad
    _ = 80 * (f - 1) * (t.card * 2 ^ (3 * L)) := by ring

end SubNLogN.Math.Networks
