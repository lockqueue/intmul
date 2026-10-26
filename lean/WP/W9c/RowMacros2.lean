import WP.W9c.RowMacros

/-!
# WP.W9c.RowMacros2 — header fields: `skipF`, `skipFs`, `copyField` (self-contained copy)

Verbatim copies (namespace `WP.W9c.RowLib`) of the header-field macros of `WP.W9b.Macros`.
-/

namespace WP.W9c.RowLib

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

section Fields

variable {K : Type} [DecidableEq K]

/-! ### Header fields -/

/-- Move one header field (its bits and its `mark`) from `src` onto `tmp`. -/
def skipF (src tmp : K) : SProg K := .seq (moveBlock src tmp) (mvSym src tmp)

/-- Move one header field back from `tmp` onto `src`. -/
def unskipF (tmp src : K) : SProg K := .seq (mvSym tmp src) (moveBlock tmp src)

theorem rs_skipF {src tmp : K} (hne : src ≠ tmp) (f : ℕ) (rest : List Sym) (S : K → List Sym)
    (hS : S src = natSyms f ++ Sym.mark :: rest) :
    Runs (skipF src tmp) S
      (Function.update (Function.update S src rest) tmp
        (Sym.mark :: ((natSyms f).reverse ++ S tmp)))
      (fun _ => True) (3 * bitLen f + 6) := by
  have h1 := rs_moveBlock hne (encodeNat f) (Sym.mark :: rest) S (TermOK.cons rfl _) hS
  have h2 := rs_mvSym hne Sym.mark rest
    (Function.update (Function.update S src (Sym.mark :: rest)) tmp
      ((encodeNat f).reverse.map Sym.bit ++ S tmp))
    (by rw [Function.update_of_ne hne, Function.update_self])
  refine runs_post (runs_seq h1 h2) ?_ (by simp only [bitLen]; omega)
  funext k
  simp only [Function.update_apply, natSyms]
  split_ifs <;> simp_all

theorem rs_unskipF {src tmp : K} (hne : src ≠ tmp) (f : ℕ) (trest : List Sym)
    (htr : TermOK trest) (S : K → List Sym)
    (hS : S tmp = Sym.mark :: ((natSyms f).reverse ++ trest)) :
    Runs (unskipF tmp src) S
      (Function.update (Function.update S tmp trest) src (natSyms f ++ Sym.mark :: S src))
      (fun _ => True) (3 * bitLen f + 6) := by
  have h1 := rs_mvSym (Ne.symm hne) Sym.mark ((natSyms f).reverse ++ trest) S hS
  have h2 := rs_moveBlock (Ne.symm hne) (encodeNat f).reverse trest
    (Function.update (Function.update S tmp ((natSyms f).reverse ++ trest)) src
      (Sym.mark :: S src))
    htr (by rw [Function.update_of_ne (Ne.symm hne), Function.update_self]; simp [natSyms])
  refine runs_post (runs_seq h1 h2) ?_ (by simp only [List.length_reverse, bitLen]; omega)
  funext k
  simp only [Function.update_apply, natSyms, List.reverse_reverse]
  split_ifs <;> simp_all

/-- Move `n` header fields from `src` onto `tmp`. -/
def skipFs (src tmp : K) : ℕ → SProg K
  | 0 => Lib.skip
  | n + 1 => .seq (skipF src tmp) (skipFs src tmp n)

/-- Move `n` header fields back from `tmp` onto `src`. -/
def unskipFs (tmp src : K) : ℕ → SProg K
  | 0 => Lib.skip
  | n + 1 => .seq (unskipF tmp src) (unskipFs tmp src n)

theorem rs_skipFs {src tmp : K} (hne : src ≠ tmp) :
    ∀ (fs : List ℕ) (rest : List Sym) (S : K → List Sym), S src = hdrSyms fs ++ rest →
      Runs (skipFs src tmp fs.length) S
        (Function.update (Function.update S src rest) tmp ((hdrSyms fs).reverse ++ S tmp))
        (fun _ => True) (6 * (hdrSyms fs).length + 1)
  | [], rest, S, hS => by
    have hS' : S src = rest := by simpa [hdrSyms_nil] using hS
    refine runs_post (rs_skip S) ?_ (by simp)
    rw [hdrSyms_nil, List.reverse_nil, List.nil_append, ← hS', Function.update_eq_self,
      Function.update_eq_self]
  | f :: fs, rest, S, hS => by
    have h1 := rs_skipF hne f (hdrSyms fs ++ rest) S (by rw [hS, hdrSyms_cons]; simp)
    have h2 := rs_skipFs hne fs rest
      (Function.update (Function.update S src (hdrSyms fs ++ rest)) tmp
        (Sym.mark :: ((natSyms f).reverse ++ S tmp)))
      (by rw [Function.update_of_ne hne, Function.update_self])
    refine runs_post (runs_seq h1 h2) ?_ (by rw [length_hdrSyms_cons]; omega)
    funext k
    simp only [Function.update_apply, hdrSyms_cons, List.reverse_append, List.reverse_cons]
    split_ifs <;> simp_all

theorem rs_unskipFs {src tmp : K} (hne : src ≠ tmp) (trest : List Sym) (htr : TermOK trest) :
    ∀ (fs : List ℕ) (S : K → List Sym), S tmp = (hdrSyms fs).reverse ++ trest →
      Runs (unskipFs tmp src fs.length) S
        (Function.update (Function.update S tmp trest) src (hdrSyms fs ++ S src))
        (fun _ => True) (6 * (hdrSyms fs).length + 1) := by
  intro fs
  induction fs using List.reverseRecOn with
  | nil =>
    intro S hS
    have hS' : S tmp = trest := by simpa [hdrSyms_nil] using hS
    refine runs_post (rs_skip S) ?_ (by simp)
    rw [hdrSyms_nil, List.nil_append, ← hS', Function.update_eq_self, Function.update_eq_self]
  | append_singleton fs f ih =>
    intro S hS
    have hrev : (hdrSyms (fs ++ [f])).reverse =
        Sym.mark :: ((natSyms f).reverse ++ (hdrSyms fs).reverse) := by
      simp [hdrSyms_append, hdrSyms_cons, hdrSyms_nil]
    have hlen : (fs ++ [f]).length = fs.length + 1 := by simp
    rw [hlen]
    have h1 := rs_unskipF hne f ((hdrSyms fs).reverse ++ trest) (termOK_hdr_rev fs trest htr) S
      (by rw [hS, hrev]; simp)
    have h2 := ih (Function.update (Function.update S tmp ((hdrSyms fs).reverse ++ trest)) src
        (natSyms f ++ Sym.mark :: S src))
      (by rw [Function.update_of_ne (Ne.symm hne), Function.update_self])
    refine runs_post (runs_seq h1 h2) ?_ (by rw [length_hdrSyms_concat]; omega)
    funext k
    simp only [Function.update_apply, hdrSyms_append, hdrSyms_cons, hdrSyms_nil]
    split_ifs <;> simp_all

/-- Push a copy of header field `j` of `src` onto `dst` (temporary `tmp`, guarded). -/
def copyField (j : ℕ) (src dst tmp : K) : SProg K :=
  .seq (pushC tmp .mark) (.seq (skipFs src tmp j) (.seq (copyBlock src dst tmp)
    (.seq (unskipFs tmp src j) (popR tmp))))

theorem rs_copyField {src dst tmp : K} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (fs : List ℕ) (j : ℕ) (hj : j < fs.length) (rest : List Sym) (S : K → List Sym)
    (hS : S src = hdrSyms fs ++ rest) :
    Runs (copyField j src dst tmp) S (Function.update S dst (natSyms fs[j] ++ S dst))
      (fun _ => True) (13 * (hdrSyms fs).length + 11) := by
  have hA : (fs.take j).length = j := by simp; omega
  have hsplit : hdrSyms fs = hdrSyms (fs.take j) ++
      (natSyms fs[j] ++ Sym.mark :: hdrSyms (fs.drop (j + 1))) := by
    conv_lhs => rw [← List.take_append_drop j fs]
    rw [hdrSyms_append, List.drop_eq_getElem_cons hj, hdrSyms_cons]
  have hlen : (hdrSyms fs).length = (hdrSyms (fs.take j)).length + bitLen fs[j] + 1 +
      (hdrSyms (fs.drop (j + 1))).length := by
    rw [hsplit]
    simp [length_natSyms]
    omega
  set B := natSyms fs[j] ++ Sym.mark :: hdrSyms (fs.drop (j + 1)) with hB
  -- push the guard
  have e0 := rs_push tmp Sym.mark S
  set S1 := Function.update S tmp (Sym.mark :: S tmp) with hS1
  -- skip the first `j` fields
  have e1 := rs_skipFs h2 (fs.take j) (B ++ rest) S1
    (by rw [hS1, Function.update_of_ne h2, hS, hsplit, List.append_assoc])
  rw [hA] at e1
  set S2 := Function.update (Function.update S1 src (B ++ rest)) tmp
    ((hdrSyms (fs.take j)).reverse ++ S1 tmp) with hS2
  -- copy field `j`
  have e2 := rs_copy h1 h2 h3 fs[j] (Sym.mark :: (hdrSyms (fs.drop (j + 1)) ++ rest)) S2
    (TermOK.cons rfl _) (by rw [hS2, Function.update_of_ne h2, Function.update_self, hB]; simp)
  set S3 := Function.update S2 dst (natSyms fs[j] ++ S2 dst) with hS3
  -- move the `j` fields back
  have e3 := rs_unskipFs h2 (Sym.mark :: S tmp) (TermOK.cons rfl _) (fs.take j) S3
    (by rw [hS3, Function.update_of_ne (Ne.symm h3), hS2, Function.update_self, hS1,
      Function.update_self])
  rw [hA] at e3
  set S4 := Function.update (Function.update S3 tmp (Sym.mark :: S tmp)) src
    (hdrSyms (fs.take j) ++ S3 src) with hS4
  -- pop the guard
  have e4 := rs_pop tmp Sym.mark (S tmp) S4
    (by rw [hS4, Function.update_of_ne (Ne.symm h2), Function.update_self])
  refine runs_post (runs_seq e0 (runs_seq e1 (runs_seq e2 (runs_seq e3 e4)))) ?_ (by omega)
  funext k
  simp only [hS4, hS3, hS2, hS1, Function.update_apply]
  split_ifs <;> simp_all

end Fields

section Closed

variable {K : Type}

theorem closed_skipFs (src tmp : K) : ∀ n, (skipFs src tmp n).Closed
  | 0 => by simp [Prog.Closed, Prog.FreeBelow, skipFs, Lib.skip]
  | n + 1 => ⟨by simp [Prog.FreeBelow, skipF, moveBlock, moveBits, moveBitsBody, restoreR, mvSym,
      popR, pushR, Lib.skip], closed_skipFs src tmp n⟩

theorem closed_unskipFs (tmp src : K) : ∀ n, (unskipFs tmp src n).Closed
  | 0 => by simp [Prog.Closed, Prog.FreeBelow, unskipFs, Lib.skip]
  | n + 1 => ⟨by simp [Prog.FreeBelow, unskipF, moveBlock, moveBits, moveBitsBody, restoreR, mvSym,
      popR, pushR, Lib.skip], closed_unskipFs tmp src n⟩

theorem closed_copyField (j : ℕ) (src dst tmp : K) : (copyField j src dst tmp).Closed :=
  ⟨by simp [Prog.FreeBelow, pushC], closed_skipFs src tmp j,
    by simp [Prog.FreeBelow, copyBlock, moveBlock, moveBits, moveBitsBody, moveBitsDup, dupBody,
      restoreR, pushC, pushR, popR, Lib.skip],
    closed_unskipFs tmp src j, by simp [Prog.FreeBelow, popR]⟩

end Closed

#assert_std_axioms rs_skipF rs_unskipF rs_skipFs rs_unskipFs rs_copyField closed_skipFs
  closed_unskipFs closed_copyField

end WP.W9c.RowLib
