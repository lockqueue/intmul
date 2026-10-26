import WP.W7k2.B.Rules
import WP.W7k2.ColRecip
import WP.W7k2.Canon.Tape

/-!
# WP.W7k2.B.Help — generic helper sub-programs of the table builder

| program | effect (top of stack first) |
|---|---|
| `bdrI x` | drop the signed number on `x` |
| `bacon x c t y` | `y += x + c` (temporary `t`) |
| `bnm x y t1 t2 z` | `z += x·y` for naturals, through `W5_mulAt` (temporaries `t1`, `t2`) |
| `bp2 c y` | `y += 2^c` |
| `bmin x y z` | `z += min x y` |
| `bset x y` | replace the number on `y` by the number on `x` |
| `pushMarks ks` / `popMarks ks` | push / pop one `mark` on each stack of `ks` |

Also: `NatAt B k v` (stack `k` holds `v` on a terminated rest) and its update lemmas; `mark ∉`
lemmas for the encodings and the pre segment (the `moveBlock` side condition).
-/

namespace WP.W7k2

open TMFw TMFw.Contracts

/-! ## Values on stacks -/

/-- Stack `k` of `B` holds the number `v` on top of a terminated rest. -/
def NatAt (B : BL → List Sym) (k : BL) (v : ℕ) : Prop := ∃ r, TermOK r ∧ B k = natSyms v ++ r

theorem NatAt.upd {B : BL → List Sym} {k j : BL} {v : ℕ} (h : NatAt B k v) (hne : k ≠ j)
    (w : List Sym) : NatAt (Function.update B j w) k v := by
  obtain ⟨r, hr, e⟩ := h
  exact ⟨r, hr, by rw [Function.update_of_ne hne, e]⟩

theorem NatAt.self (B : BL → List Sym) (k : BL) (v : ℕ) {r : List Sym} (hr : TermOK r) :
    NatAt (Function.update B k (natSyms v ++ r)) k v :=
  ⟨r, hr, by rw [Function.update_self]⟩

theorem termOK_upd {B : BL → List Sym} {k j : BL} (h : TermOK (B k)) (hne : k ≠ j)
    (w : List Sym) : TermOK (Function.update B j w k) := by
  rw [Function.update_of_ne hne]
  exact h

theorem bitLen_one : bitLen 1 = 1 := by simpa using bitLen_two_pow 0

/-! ## Helper programs -/

section Programs

variable (I : BI)

/-- Drop the signed number on top of `x`. -/
def bdrI (x : BL) : BP I := (popS x).seq (bdr I x)

/-- `y += x + c`, using the temporary `t`. -/
def bacon (x : BL) (c : ℕ) (t y : BL) : BP I := (pushNat t c).seq ((bad I x t y).seq (bdr I t))

/-- `z += x * y` for naturals (through the signed multiplier), temporaries `t1`, `t2`. -/
def bnm (x y t1 t2 z : BL) : BP I :=
  (bcp I x t1).seq <| (pushS t1 .pos).seq <| (bcp I y t2).seq <| (pushS t2 .pos).seq <|
  (bmu I t1 t2 z).seq <| (popS z).seq <| (popS t1).seq <| (bdr I t1).seq <| (popS t2).seq <|
  bdr I t2

/-- `y += 2 ^ c`. -/
def bp2 (c y : BL) : BP I := (pushNat y 1).seq (bsv I y c)

/-- `z += min x y`. -/
def bmin (x y z : BL) : BP I :=
  (bcm I x y).seq (.ite (fun s => decide (I.cm.obs (I.lcm.get s) ≠ .gt)) (bcp I x z) (bcp I y z))

/-- Replace the number on `y` by a copy of the number on `x`. -/
def bset (x y : BL) : BP I := (bdr I y).seq (bcp I x y)

/-- Push a `mark` on each stack of `ks`. -/
def pushMarks : List BL → BP I
  | [] => .load id
  | k :: ks => (pushS k .mark).seq (pushMarks ks)

/-- Pop one symbol from each stack of `ks`. -/
def popMarks : List BL → BP I
  | [] => .load id
  | k :: ks => (popS k).seq (popMarks ks)

theorem bdrI_closed (x : BL) : (bdrI I x).Closed := ⟨trivial, callI_closed _ _ _ _⟩

theorem bacon_closed (x : BL) (c : ℕ) (t y : BL) : (bacon I x c t y).Closed :=
  ⟨pushBits_closed _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem bnm_closed (x y t1 t2 z : BL) : (bnm I x y t1 t2 z).Closed :=
  ⟨callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial,
    trivial, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _⟩

theorem bp2_closed (c y : BL) : (bp2 I c y).Closed := ⟨pushBits_closed _ _, callI_closed _ _ _ _⟩

theorem bmin_closed (x y z : BL) : (bmin I x y z).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem bset_closed (x y : BL) : (bset I x y).Closed :=
  ⟨callI_closed _ _ _ _, callI_closed _ _ _ _⟩

theorem pushMarks_closed : ∀ ks : List BL, (pushMarks I ks).Closed
  | [] => trivial
  | _ :: ks => ⟨trivial, pushMarks_closed ks⟩

theorem popMarks_closed : ∀ ks : List BL, (popMarks I ks).Closed
  | [] => trivial
  | _ :: ks => ⟨trivial, popMarks_closed ks⟩

end Programs

/-! ## Host rules of the helpers -/

section Rules

variable {I : BI} {Mul : ℕ → ℕ} {C : ℕ}

theorem HT.bdrI (hI : I.Spec Mul C) (x : BL) (B : BL → List Sym) (z : ℤ) (r : List Sym)
    (hr : TermOK r) (hB : B x = intSyms z ++ r) (ρ : List (BP I)) :
    HT ρ B (bdrI I x) (Function.update B x r) (1 + C * (bitLen z.natAbs + 1)) := by
  have hBx : B x = sgnSym z :: (natSyms z.natAbs ++ r) := by rw [hB]; rfl
  refine (HT.seq (HT.popS x B _ _ hBx ρ) (HT.bdr hI x _ z.natAbs r hr (by simp) ρ)).of_eq ?_
    le_rfl
  rw [Function.update_idem]

theorem HT.bacon (hI : I.Spec Mul C) (x : BL) (c : ℕ) (t y : BL) (hnd : [x, t, y].Nodup)
    (B : BL → List Sym) (v : ℕ) (rx : List Sym) (hrx : TermOK rx) (hx : B x = natSyms v ++ rx)
    (ht : TermOK (B t)) (ρ : List (BP I)) :
    HT ρ B (bacon I x c t y) (Function.update B y (natSyms (v + c) ++ B y))
      (bitLen c + 1 + (C * (bitLen v + bitLen c + 1) + C * (bitLen c + 1))) := by
  have hxt : x ≠ t := fun h => by simp [h] at hnd
  have hty : t ≠ y := fun h => by simp [h] at hnd
  refine (HT.seq (HT.pushNat t c B ρ) (HT.seq
    (HT.bad hI x t y hnd _ v c rx (B t) hrx ht (by simp [Function.update_apply, hxt, hx])
      (by simp) ρ)
    (HT.bdr hI t _ c (B t) ht (by simp [Function.update_apply, hty]) ρ))).of_eq ?_ le_rfl
  funext g
  by_cases hg : g = t
  · rw [hg]
    simp [Function.update_apply, hty]
  · simp [Function.update_apply, hg, hty.symm]

theorem HT.bnm (hI : I.Spec Mul C) (x y t1 t2 z : BL) (hx1 : [x, t1, t2, z].Nodup)
    (hy1 : [y, t1, t2, z].Nodup) (B : BL → List Sym) (u v : ℕ) (ru rv : List Sym)
    (hru : TermOK ru) (hrv : TermOK rv) (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv)
    (h1 : TermOK (B t1)) (h2 : TermOK (B t2)) (ρ : List (BP I)) :
    HT ρ B (bnm I x y t1 t2 z) (Function.update B z (natSyms (u * v) ++ B z))
      (2 * (C * (bitLen u + 1)) + 2 * (C * (bitLen v + 1)) +
        (C * Mul (max (bitLen u) (bitLen v)) + C) + 5) := by
  have hxt1 : x ≠ t1 := fun h => by simp [h] at hx1
  have hyt1 : y ≠ t1 := fun h => by simp [h] at hy1
  have hyt2 : y ≠ t2 := fun h => by simp [h] at hy1
  have ht12 : t1 ≠ t2 := fun h => by simp [h] at hx1
  have ht1z : t1 ≠ z := fun h => by simp [h] at hx1
  have ht2z : t2 ≠ z := fun h => by simp [h] at hx1
  have eu : intSyms (u : ℤ) = Sym.pos :: natSyms u := intSyms_natCast u
  have ev : intSyms (v : ℤ) = Sym.pos :: natSyms v := intSyms_natCast v
  have euv : intSyms ((u : ℤ) * (v : ℤ)) = Sym.pos :: natSyms (u * v) := by
    rw [← Nat.cast_mul]
    exact intSyms_natCast _
  have hw1 : bitLen (u : ℤ).natAbs ≤ max (bitLen u) (bitLen v) := by simp
  have hw2 : bitLen (v : ℤ).natAbs ≤ max (bitLen u) (bitLen v) := by simp
  refine (HT.seq (HT.bcp hI x t1 (by simp [hxt1]) B u ru hru hx ρ) <|
    HT.seq (HT.pushS t1 .pos _ ρ) <|
    HT.seq (HT.bcp hI y t2 (by simp [hyt2]) _ v rv hrv
      (by simp [Function.update_apply, hyt1, hy]) ρ) <|
    HT.seq (HT.pushS t2 .pos _ ρ) <|
    HT.seq (HT.bmu hI t1 t2 z (by simp [ht12, ht1z, ht2z]) _ (max (bitLen u) (bitLen v))
      (u : ℤ) (v : ℤ) (B t1) (B t2) hw1 hw2 h1 h2
      (by simp [Function.update_apply, ht12, eu])
      (by simp [Function.update_apply, ht12.symm, ev]) ρ) <|
    HT.seq (HT.popS z _ .pos (natSyms (u * v) ++ B z)
      (by simp [Function.update_apply, euv, ht1z.symm, ht2z.symm]) ρ) <|
    HT.seq (HT.popS t1 _ .pos (natSyms u ++ B t1)
      (by simp [Function.update_apply, ht1z, ht12]) ρ) <|
    HT.seq (HT.bdr hI t1 _ u (B t1) h1 (by simp) ρ) <|
    HT.seq (HT.popS t2 _ .pos (natSyms v ++ B t2)
      (by simp [Function.update_apply, ht12.symm, ht2z]) ρ) <|
    HT.bdr hI t2 _ v (B t2) h2 (by simp) ρ).of_eq ?_ (by omega)
  funext g
  by_cases hg1 : g = t1
  · rw [hg1]
    simp [Function.update_apply, ht12, ht1z]
  · by_cases hg2 : g = t2
    · rw [hg2]
      simp [Function.update_apply, ht12.symm, ht2z]
    · by_cases hgz : g = z
      · rw [hgz]
        simp [Function.update_apply, ht1z.symm, ht2z.symm]
      · simp [Function.update_apply, hg1, hg2, hgz]

theorem HT.bp2 (hI : I.Spec Mul C) (c y : BL) (hnd : [y, c].Nodup) (B : BL → List Sym) (k : ℕ)
    (rc : List Sym) (hrc : TermOK rc) (hc : B c = natSyms k ++ rc) (hy : TermOK (B y))
    (ρ : List (BP I)) :
    HT ρ B (bp2 I c y) (Function.update B y (natSyms (2 ^ k) ++ B y))
      (2 + C * (k + bitLen k + 1)) := by
  have hyc : y ≠ c := fun h => by simp [h] at hnd
  refine (HT.seq (HT.pushNat y 1 B ρ) (HT.bsv hI y c hnd _ 1 k (B y) rc hy hrc (by simp)
    (by simp [Function.update_apply, hyc.symm, hc]) ρ)).of_eq ?_ (by rw [bitLen_one])
  rw [Function.update_idem, one_mul]

theorem HT.bmin (hI : I.Spec Mul C) (x y z : BL) (hnd : [x, y, z].Nodup) (B : BL → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) (ρ : List (BP I)) :
    HT ρ B (bmin I x y z) (Function.update B z (natSyms (min u v) ++ B z))
      (C * (bitLen u + bitLen v + 1) + (max (C * (bitLen u + 1)) (C * (bitLen v + 1)) + 1)) := by
  have hxy : x ≠ y := fun h => by simp [h] at hnd
  have hxz : x ≠ z := fun h => by simp [h] at hnd
  have hyz : y ≠ z := fun h => by simp [h] at hnd
  refine HT.bcmIte hI x y (by simp [hxy]) B _ u v ru rv hru hrv hx hy
    (fun o => decide (o ≠ .gt)) _ _ ρ (fun h => ?_) (fun h => ?_)
  · have hle : u ≤ v := (ordOf_ne_gt_iff u v).mp (of_decide_eq_true h)
    exact (HT.bcp hI x z (by simp [hxz]) B u ru hru hx ρ).of_eq (by rw [min_eq_left hle]) le_rfl
  · have hgt : ¬ u ≤ v := fun hle =>
      absurd ((ordOf_ne_gt_iff u v).mpr hle) (of_decide_eq_false h)
    exact (HT.bcp hI y z (by simp [hyz]) B v rv hrv hy ρ).of_eq
      (by rw [min_eq_right (by omega)]) le_rfl

theorem HT.bset (hI : I.Spec Mul C) (x y : BL) (hxy : x ≠ y) (B : BL → List Sym) (u w : ℕ)
    (ru rw : List Sym) (hru : TermOK ru) (hrw : TermOK rw) (hx : B x = natSyms u ++ ru)
    (hy : B y = natSyms w ++ rw) (ρ : List (BP I)) :
    HT ρ B (bset I x y) (Function.update B y (natSyms u ++ rw))
      (C * (bitLen w + 1) + C * (bitLen u + 1)) := by
  refine (HT.seq (HT.bdr hI y B w rw hrw hy ρ) (HT.bcp hI x y (by simp [hxy]) _ u ru hru
    (by simp [Function.update_apply, hxy, hx]) ρ)).of_eq ?_ le_rfl
  simp [Function.update_idem]

/-! ### Marks -/

/-- `B` with a `mark` pushed on each of `ks`, in order. -/
def marked (B : BL → List Sym) : List BL → BL → List Sym
  | [] => B
  | k :: ks => marked (Function.update B k (Sym.mark :: B k)) ks

theorem marked_update_comm (B : BL → List Sym) (k : BL) (w : List Sym) :
    ∀ ks : List BL, k ∉ ks → Function.update (marked B ks) k w = marked (Function.update B k w) ks
  | [], _ => rfl
  | j :: js, hk => by
    have hkj : k ≠ j := fun e => hk (by simp [e])
    have hks : k ∉ js := fun h => hk (List.mem_cons_of_mem _ h)
    simp only [marked]
    rw [marked_update_comm _ k w js hks, Function.update_of_ne (Ne.symm hkj),
      Function.update_comm (Ne.symm hkj)]

theorem HT.pushMarks (ρ : List (BP I)) :
    ∀ (ks : List BL) (B : BL → List Sym),
      HT ρ B (WP.W7k2.pushMarks I ks) (marked B ks) (ks.length + 1)
  | [], B => by
    rintro ⟨v, S⟩ hS
    change S = B at hS
    subst hS
    exact ⟨⟨v, S⟩, 1, Eval.load ρ id v S, rfl, by simp⟩
  | k :: ks, B =>
    (HT.seq (HT.pushS k .mark B ρ) (HT.pushMarks ρ ks _)).of_eq rfl
      (by simp only [List.length_cons]; omega)

theorem HT.popMarks (ρ : List (BP I)) (S : BL → List Sym) :
    ∀ ks : List BL, ks.Nodup → HT ρ (marked S ks) (WP.W7k2.popMarks I ks) S (ks.length + 1)
  | [], _ => by
    rintro ⟨v, S'⟩ hS
    change S' = S at hS
    subst hS
    exact ⟨⟨v, S'⟩, 1, Eval.load ρ id v S', rfl, by simp⟩
  | k :: ks, hnd => by
    have hk : k ∉ ks := (List.nodup_cons.mp hnd).1
    have hks : ks.Nodup := (List.nodup_cons.mp hnd).2
    have e1 : marked S (k :: ks) k = Sym.mark :: S k := by
      show marked (Function.update S k (Sym.mark :: S k)) ks k = _
      rw [← marked_update_comm S k _ ks hk, Function.update_self]
    have e2 : Function.update (marked S (k :: ks)) k (S k) = marked S ks := by
      show Function.update (marked (Function.update S k (Sym.mark :: S k)) ks) k (S k) = _
      rw [marked_update_comm _ k _ ks hk, Function.update_idem, Function.update_eq_self]
    have h2 : HT ρ (Function.update (marked S (k :: ks)) k (S k)) (WP.W7k2.popMarks I ks) S
        (ks.length + 1) := by
      rw [e2]
      exact HT.popMarks ρ S ks hks
    exact (HT.seq (HT.popS k _ .mark (S k) e1 ρ) h2).mono (by simp only [List.length_cons]; omega)

end Rules

/-! ## `mark` does not occur in table records -/

theorem mark_not_mem_natSyms (n : ℕ) : Sym.mark ∉ natSyms n := by simp [natSyms]

theorem mark_not_mem_intSyms (z : ℤ) : Sym.mark ∉ intSyms z := by
  unfold intSyms sgnSym
  split_ifs <;> simp [mark_not_mem_natSyms]

theorem mark_not_mem_preSegC (pIn p K : ℕ) : Sym.mark ∉ preSegC pIn p K := by
  simp [preSegC, preSegE, W7.header, W7.field, W7.realRec, W7.cplxRec, W7.tagPre, W7.tagSub,
    W7.tagRow, mark_not_mem_natSyms, mark_not_mem_intSyms]

#assert_std_axioms NatAt.upd NatAt.self termOK_upd bitLen_one bdrI_closed bacon_closed bnm_closed
  bp2_closed bmin_closed bset_closed pushMarks_closed popMarks_closed HT.bdrI HT.bacon HT.bnm
  HT.bp2 HT.bmin HT.bset marked_update_comm HT.pushMarks HT.popMarks mark_not_mem_natSyms
  mark_not_mem_intSyms mark_not_mem_preSegC

end WP.W7k2
