import WP.Top.Obligations
import WP.Top.Embed
import WP.TapeConv.Main

/-!
# WP.Top.TapeConvBridge — `TapeConv` from the proved converter (wp/TapeConv)

The table-tape converter `WP.TapeConv` is proved and hypothesis-free. It provides two things:
* `TapeConv_snapshotSchedule : TapeConv_contract W7.snapshotSchedule.toTapeFormat`. This is a W9
  `BContract` (named stacks `LB`, at most `w9Scratch` scratch stacks): `TR = W7.tape F cSpec ++ rest`
  becomes `TR = tapeSyms cSpec ++ rest`, every other stack is restored, and the cost is
  `C·(|W7.tape F cSpec| + 1)`, with `C = 32` and 3 scratch stacks.
* `tapeSyms_length_le'`: `|tapeSyms cSpec| ≤ 2·(|W7.tape F cSpec| + 1)`.

**`TapeConv_of_contract`** turns these into `WP.Top.Obligations.TapeConv` (1 named stack plus
scratch). It renames the converter's stacks along the bijection `ιB m : BLoc m → Loc 1 (11 + m)`:
* `TR` becomes the named stack `0`;
* the other 11 named stacks become scratch slots `0..10`;
* scratch `j` becomes scratch `11 + j`.

Hence `convScratch = 75`: 11 + `w9Scratch` fits, and 1 + 75 stacks fill `GW` exactly. The constant is
`C + 2`, which covers both the cost and the size clause.

**`TapeConv_proved : TapeConv`** is the instance.

**`TR` starts empty.** W9_multiply's side condition `restT.head? ≠ some symPost` needs nothing extra:
* `GW.tr` is empty after the input stage (`prmState n A B .tr = []`, `prmState_tr`);
* W7 and the converter both leave `rest = []`;
* `stage_w9` (WP.Top.Correct) supplies the condition for `restT = []`.
-/

namespace WP.Top

open TMFw TMFw.Contracts TMFw.Contracts.W9

/-- The converter's named stacks in the 1-named-stack shape. -/
def ιBn (m : ℕ) : LB → Loc 1 (11 + m)
  | .TR => .inl 0
  | .S => .inr ⟨0, by omega⟩
  | .W0 => .inr ⟨1, by omega⟩
  | .TL => .inr ⟨2, by omega⟩
  | .RET => .inr ⟨3, by omega⟩
  | .RQ => .inr ⟨4, by omega⟩
  | .C0 => .inr ⟨5, by omega⟩
  | .C1 => .inr ⟨6, by omega⟩
  | .C2 => .inr ⟨7, by omega⟩
  | .C3 => .inr ⟨8, by omega⟩
  | .OA => .inr ⟨9, by omega⟩
  | .OB => .inr ⟨10, by omega⟩

/-- A left inverse of `ιBn m`. -/
def backB (m : ℕ) : Loc 1 (11 + m) → LB
  | .inl _ => .TR
  | .inr k =>
    if k.val = 0 then .S else if k.val = 1 then .W0 else if k.val = 2 then .TL else
    if k.val = 3 then .RET else if k.val = 4 then .RQ else if k.val = 5 then .C0 else
    if k.val = 6 then .C1 else if k.val = 7 then .C2 else if k.val = 8 then .C3 else
    if k.val = 9 then .OA else .OB

theorem backB_ιBn (m : ℕ) : Function.LeftInverse (backB m) (ιBn m) := by
  intro l
  cases l <;> rfl

/-- The renaming `BLoc m → Loc 1 (11 + m)`. -/
def ιB (m : ℕ) : BLoc m → Loc 1 (11 + m) :=
  Sum.elim (ιBn m) (fun j => .inr (Fin.natAdd 11 j))

theorem ιB_inj (m : ℕ) : Function.Injective (ιB m) := by
  refine sumElim_inj (backB_ιBn m).injective ?_ ?_
  · intro a b h
    have h' := congrArg Fin.val (Sum.inr.inj h)
    simp only [Fin.val_natAdd] at h'
    exact Fin.ext (by omega)
  · intro l j h
    cases l <;> simp [ιBn, Fin.ext_iff] at h <;> omega

theorem ιB_TR (m : ℕ) : ιB m (.inl .TR) = .inl 0 := rfl

/-- **`TapeConv` from the converter's contract and its size lemma.** -/
theorem TapeConv_of_contract (h : WP.TapeConv.TapeConv_contract W7.snapshotSchedule.toTapeFormat)
    (hsize : ∀ cSpec : IntMul.ComputablePaperFastDFTSpec, (tapeSyms cSpec).length ≤
      2 * ((W7.tape W7.snapshotSchedule.toTapeFormat cSpec).length + 1)) :
    TapeConv := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C + 2, fun _ => ?_⟩
  obtain ⟨m, R, P, hm, hfin, hne, hcl, hspec⟩ := hC ()
  have hm' : 11 + m ≤ convScratch := by
    have : m ≤ 64 := hm
    show 11 + m ≤ 75
    omega
  refine ⟨11 + m, R, fun _ => (), P.mapStk (ιB m), hm', hfin, hne, ?_, ?_⟩
  · unfold Prog.Closed at hcl ⊢
    exact (WP.W0m.freeBelow_mapStk (ιB m) P 0).2 hcl
  · intro n cSpec S _ hS
    refine ⟨(hsize cSpec).trans (Nat.mul_le_mul_right _ (by omega)), ?_⟩
    have hr := hspec cSpec (fun l => S (ιB m l)) []
      (by show S (.inl 0) = _; rw [hS, List.append_nil])
    have he := Runs.embed (ιB_inj m) hr S (fun _ => rfl)
    refine he.conseq (fun _ hs => hs) ?_ (Nat.mul_le_mul_right _ (by omega))
    rintro s ⟨h1, h2, -⟩
    refine ⟨funext fun k => ?_, trivial⟩
    by_cases hk : k = .inl 0
    · subst hk
      have h := h1 (.inl .TR)
      rw [Function.update_self, List.append_nil] at h
      rw [Function.update_self]
      exact h
    · rw [Function.update_of_ne hk]
      by_cases hr' : ∃ l, ιB m l = k
      · obtain ⟨l, rfl⟩ := hr'
        have hl : l ≠ .inl .TR := by
          rintro rfl
          exact hk rfl
        rw [h1 l, Function.update_of_ne hl]
      · push_neg at hr'
        exact h2 k hr'


/-- **`TR` is empty after the input stage**, so the converter and W9 start with `rest = []`. -/
theorem prmState_tr (n A B : ℕ) : prmState n A B .tr = [] := rfl

/-- **`TapeConv`, proved** (from the hypothesis-free converter `WP.TapeConv`). -/
theorem TapeConv_proved : TapeConv :=
  TapeConv_of_contract WP.TapeConv.TapeConv_snapshotSchedule
    (WP.TapeConv.tapeSyms_length_le' _ (fun _ _ => rfl) (fun _ _ => rfl))

#assert_std_axioms backB_ιBn ιB_inj ιB_TR TapeConv_of_contract prmState_tr TapeConv_proved

end WP.Top
