import WP.W9f.Macros

/-!
# WP.W9f.GlueHdr — reading level-header fields from `C0` (restored)

`copyField k dst`: move the first `k` header fields from `C0` onto `TT` (`mvSeq k`), copy field `k`
onto `dst` (`copyBlock`), move the `k` fields back (`bkSeq k`). `HT.copyField`: only `dst` changes.
Cost `O(|header|)`.
-/

namespace WP.W9f

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 Computability

variable {σ : Type} (lS : Lens σ (Option Sym))

/-- A header field moved onto `TT`: `mark`, then its bits reversed. -/
def revF (n : ℕ) : List Sym := Sym.mark :: (encodeNat n).reverse.map Sym.bit

/-- Header symbols of a list of fields. -/
theorem hdrSyms_nil : hdrSyms [] = [] := rfl

theorem hdrSyms_cons (n : ℕ) (fs : List ℕ) :
    hdrSyms (n :: fs) = natSyms n ++ Sym.mark :: hdrSyms fs := by
  simp [hdrSyms]

theorem hdrSyms_append (fs gs : List ℕ) : hdrSyms (fs ++ gs) = hdrSyms fs ++ hdrSyms gs := by
  simp [hdrSyms]

/-- Cost of moving the fields `fs` one way. -/
def mvCost (fs : List ℕ) : ℕ := (fs.map (fun n => 3 * bitLen n + 6)).sum

theorem mvCost_append (l1 l2 : List ℕ) : mvCost (l1 ++ l2) = mvCost l1 + mvCost l2 := by
  simp [mvCost]

theorem mvCost_reverse (l : List ℕ) : mvCost l.reverse = mvCost l := by
  simp [mvCost, List.map_reverse, List.sum_reverse]

theorem mvCost_take_le (l : List ℕ) (k : ℕ) : mvCost (l.take k) ≤ mvCost l := by
  have h := mvCost_append (l.take k) (l.drop k)
  rw [List.take_append_drop] at h
  omega

/-- Move one field from `C0` onto `TT`. -/
def mvF : Prog HL (fun _ => Sym) σ :=
  ((moveBlock F.C0.loc F.TT.loc).liftRegs lS).seq ((popS F.C0.loc).seq (pushS F.TT.loc Sym.mark))

/-- Move one field back from `TT` onto `C0`. -/
def bkF : Prog HL (fun _ => Sym) σ :=
  (popS F.TT.loc).seq ((pushS F.C0.loc Sym.mark).seq ((moveBlock F.TT.loc F.C0.loc).liftRegs lS))

/-- Move `k` fields from `C0` onto `TT`. -/
def mvSeq : ℕ → Prog HL (fun _ => Sym) σ
  | 0 => skip
  | k + 1 => (mvF lS).seq (mvSeq k)

/-- Move `k` fields back from `TT` onto `C0`. -/
def bkSeq : ℕ → Prog HL (fun _ => Sym) σ
  | 0 => skip
  | k + 1 => (bkF lS).seq (bkSeq k)

/-- Copy header field `k` onto `dst`. -/
def copyField (k : ℕ) (dst : F) : Prog HL (fun _ => Sym) σ :=
  (mvSeq lS k).seq (((copyBlock F.C0.loc dst.loc F.X'.loc).liftRegs lS).seq (bkSeq lS k))

theorem HT.skipH (B : HL → List Sym) : HT (σ := σ) [] B skip B 1 := by
  rintro ⟨v, S⟩ hs
  exact ⟨⟨v, S⟩, 1, skip_eval [] _, hs, le_rfl⟩

theorem HT.mvF (σ0 : HL → List Sym) (s : F → List Sym) (n : ℕ) (rest : List Sym)
    (hs : s .C0 = natSyms n ++ Sym.mark :: rest) :
    HT [] (henc σ0 s) (mvF lS)
      (henc σ0 (Function.update (Function.update s .C0 rest) .TT (revF n ++ s .TT)))
      (3 * bitLen n + 6) := by
  have h1 := HT.moveBlockF lS σ0 s .C0 .TT (by decide) (encodeNat n) (Sym.mark :: rest)
    (TermOK.cons rfl _) hs
  have h2 := HT.popF (σ := σ) σ0 (Function.update (Function.update s .C0 (Sym.mark :: rest)) .TT
    ((encodeNat n).reverse.map Sym.bit ++ s .TT)) .C0 Sym.mark rest (by simp)
  have h3 := HT.pushF (σ := σ) σ0 (Function.update (Function.update (Function.update s .C0
    (Sym.mark :: rest)) .TT ((encodeNat n).reverse.map Sym.bit ++ s .TT)) .C0 rest) .TT Sym.mark
  refine (HT.seq h1 (HT.seq h2 h3)).of_eq ?_ (by simp only [bitLen]; omega)
  congr 1
  funext f
  cases f <;> simp [revF]

theorem HT.bkF (σ0 : HL → List Sym) (s : F → List Sym) (n : ℕ) (rest : List Sym)
    (hrest : TermOK rest) (hs : s .TT = revF n ++ rest) :
    HT [] (henc σ0 s) (bkF lS)
      (henc σ0 (Function.update (Function.update s .TT rest) .C0 (natSyms n ++ Sym.mark :: s .C0)))
      (3 * bitLen n + 6) := by
  have h1 := HT.popF (σ := σ) σ0 s .TT Sym.mark ((encodeNat n).reverse.map Sym.bit ++ rest)
    (by rw [hs]; rfl)
  have h2 := HT.pushF (σ := σ) σ0 (Function.update s .TT ((encodeNat n).reverse.map Sym.bit ++ rest))
    .C0 Sym.mark
  have h3 := HT.moveBlockF lS σ0 (Function.update (Function.update s .TT
    ((encodeNat n).reverse.map Sym.bit ++ rest)) .C0 (Sym.mark :: s .C0)) .TT .C0 (by decide)
    (encodeNat n).reverse rest hrest (by simp)
  refine (HT.seq h1 (HT.seq h2 h3)).of_eq ?_ (by simp only [bitLen, List.length_reverse]; omega)
  congr 1
  funext f
  cases f <;> simp [natSyms]

theorem HT.mvSeq (σ0 : HL → List Sym) :
    ∀ (k : ℕ) (fs : List ℕ) (r0 : List Sym) (s : F → List Sym), k ≤ fs.length →
      s .C0 = hdrSyms fs ++ r0 →
      HT [] (henc σ0 s) (mvSeq lS k)
        (henc σ0 (Function.update (Function.update s .C0 (hdrSyms (fs.drop k) ++ r0)) .TT
          ((((fs.take k).reverse).map revF).flatten ++ s .TT)))
        (mvCost (fs.take k) + 1)
  | 0, fs, r0, s, _, hs => by
    refine (HT.skipH (σ := σ) _).of_eq ?_ (by simp [mvCost])
    congr 1
    funext f
    cases f <;> simp [hs]
  | k + 1, [], r0, s, hk, _ => absurd hk (by simp)
  | k + 1, n :: fs, r0, s, hk, hs => by
    have h1 := HT.mvF lS σ0 s n (hdrSyms fs ++ r0) (by rw [hs, hdrSyms_cons]; simp)
    have h2 := HT.mvSeq σ0 k fs r0 (Function.update (Function.update s .C0 (hdrSyms fs ++ r0)) .TT
      (revF n ++ s .TT)) (by simp at hk; omega) (by simp)
    refine (HT.seq h1 h2).of_eq ?_ (by simp [mvCost]; omega)
    congr 1
    funext f
    cases f <;> simp

theorem termOK_revFs (ms : List ℕ) (tt : List Sym) (htt : TermOK tt) :
    TermOK ((ms.map revF).flatten ++ tt) := by
  cases ms with
  | nil => simpa using htt
  | cons m ms => exact TermOK.cons rfl _

theorem HT.bkSeq (σ0 : HL → List Sym) :
    ∀ (k : ℕ) (ms : List ℕ) (s : F → List Sym) (tt : List Sym), k = ms.length → TermOK tt →
      s .TT = (ms.map revF).flatten ++ tt →
      HT [] (henc σ0 s) (bkSeq lS k)
        (henc σ0 (Function.update (Function.update s .TT tt) .C0 (hdrSyms ms.reverse ++ s .C0)))
        (mvCost ms + 1)
  | 0, [], s, tt, _, _, hs => by
    refine (HT.skipH (σ := σ) _).of_eq ?_ (by simp [mvCost])
    congr 1
    funext f
    cases f <;> simp [hs, hdrSyms]
  | 0, _ :: _, _, _, hk, _, _ => absurd hk (by simp)
  | k + 1, [], _, _, hk, _, _ => absurd hk (by simp)
  | k + 1, m :: ms, s, tt, hk, htt, hs => by
    have h1 := HT.bkF lS σ0 s m ((ms.map revF).flatten ++ tt) (termOK_revFs ms tt htt)
      (by rw [hs]; simp)
    have h2 := HT.bkSeq σ0 k ms (Function.update (Function.update s .TT
      ((ms.map revF).flatten ++ tt)) .C0 (natSyms m ++ Sym.mark :: s .C0)) tt
      (by simp at hk; omega) htt (by simp)
    refine (HT.seq h1 h2).of_eq ?_ (by simp [mvCost]; omega)
    congr 1
    funext f
    cases f <;> simp [hdrSyms_append, hdrSyms_cons, hdrSyms_nil]

/-- **Copy header field `k` onto `dst`** (`C0`, `TT` restored; `X'` is the copy temporary). -/
theorem HT.copyField (σ0 : HL → List Sym) (k : ℕ) (dst : F) (hd0 : dst ≠ .C0) (hdT : dst ≠ .TT)
    (hdX : dst ≠ .X') (fs : List ℕ) (r0 : List Sym) (s : F → List Sym) (hk : k < fs.length)
    (hs : s .C0 = hdrSyms fs ++ r0) (htt : TermOK (s .TT)) :
    HT [] (henc σ0 s) (copyField lS k dst)
      (henc σ0 (Function.update s dst (natSyms (fs.getD k 0) ++ s dst)))
      (2 * mvCost fs + 7 * bitLen (fs.getD k 0) + 9) := by
  have hgk : fs.drop k = fs.getD k 0 :: fs.drop (k + 1) := by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.drop_eq_getElem_cons hk
  have h1 := HT.mvSeq lS σ0 k fs r0 s hk.le hs
  set s1 := Function.update (Function.update s .C0 (hdrSyms (fs.drop k) ++ r0)) .TT
    ((((fs.take k).reverse).map revF).flatten ++ s .TT) with hs1
  have hs1C : s1 .C0 = (encodeNat (fs.getD k 0)).map Sym.bit ++
      Sym.mark :: (hdrSyms (fs.drop (k + 1)) ++ r0) := by
    rw [hs1, Function.update_of_ne (by decide), Function.update_self, hgk, hdrSyms_cons]
    simp [natSyms]
  have h2 := HT.copyBlockF lS σ0 s1 .C0 dst .X' (Ne.symm hd0) (by decide) hdX
    (encodeNat (fs.getD k 0)) (Sym.mark :: (hdrSyms (fs.drop (k + 1)) ++ r0)) (TermOK.cons rfl _)
    hs1C
  set s2 := Function.update s1 dst ((encodeNat (fs.getD k 0)).map Sym.bit ++ s1 dst) with hs2
  have hs2T : s2 .TT = ((((fs.take k).reverse).map revF).flatten ++ s .TT) := by
    rw [hs2, Function.update_of_ne (Ne.symm hdT), hs1, Function.update_self]
  have h3 := HT.bkSeq lS σ0 k (fs.take k).reverse s2 (s .TT)
    (by simp only [List.length_reverse, List.length_take]; omega) htt hs2T
  have hC0 : hdrSyms (fs.take k).reverse.reverse ++ s2 .C0 = s .C0 := by
    rw [hs2, Function.update_of_ne (Ne.symm hd0), hs1, Function.update_of_ne (by decide),
      Function.update_self, List.reverse_reverse, ← List.append_assoc, ← hdrSyms_append,
      List.take_append_drop, hs]
  refine (HT.seq h1 (HT.seq h2 h3)).of_eq ?_ ?_
  · congr 1
    funext g
    by_cases g0 : g = .C0
    · subst g0
      rw [Function.update_self, Function.update_of_ne (Ne.symm hd0), hC0]
    by_cases gT : g = .TT
    · subst gT
      rw [Function.update_of_ne (by decide), Function.update_self, Function.update_of_ne (Ne.symm hdT)]
    by_cases gd : g = dst
    · subst gd
      rw [Function.update_of_ne g0, Function.update_of_ne gT, hs2, Function.update_self,
        Function.update_self, hs1, Function.update_of_ne gT, Function.update_of_ne g0]
      rfl
    · rw [Function.update_of_ne g0, Function.update_of_ne gT, hs2, Function.update_of_ne gd,
        hs1, Function.update_of_ne gT, Function.update_of_ne g0, Function.update_of_ne gd]
  · have h4 := mvCost_take_le fs k
    rw [mvCost_reverse]
    simp only [bitLen] at *
    omega

#assert_std_axioms hdrSyms_cons hdrSyms_append mvCost_append mvCost_reverse mvCost_take_le
  HT.skipH HT.mvF HT.bkF HT.mvSeq termOK_revFs HT.bkSeq HT.copyField

end WP.W9f
