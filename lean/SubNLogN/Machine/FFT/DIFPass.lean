/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.FFT.DIFBase

/-!
# K4-DIF passes (`Machine/FFT/DIFPass.lean`): whole-array passes of the record DIF kernel

**Scope (honest summary).** Generic machine passes over record arrays `arrSyms v` (W4 records:
payload bits, then `sep`), all proved (no `sorry`). A *reversed* array is
`(arrSyms v).reverse` (last record on top, every record reversed: `sep` first). All record
lists below are *uniform* (every record of the same payload length), which gives uniform loop
bounds.
* `moveRec` / `moveRevRec`: move one record (normal / reversed orientation); the moved record
  arrives reversed / normal.
* `runs_revArr_out` / `runs_revArr_in`: a whole array to / from the reversed orientation.
* `rmerge X Z T`: records of `X` and `Z` alternately onto `T`: `T` receives the reversed
  `inter xs zs` (the DIF level's final record interleave).
* `deal T Q P`: a reversed `inter as bs` on `T` is dealt into `P := as` and `Q := bs`.
* `cmerge P Q T`: pairs of records merged by interleaving units of `n` bits (`cinterBits`), using
  the unit ruler `R`; `T` receives the reversed merged array (one bit-reversal pass).
* `split T U L TH`: a reversed array of records `a ++ b` (`|b| = k·n`, ruler `H` of `k` units) is
  split into `U := [a]` and `L := [b]`, and `TH` receives one copy of the stage record per record.
* `gather`: the stage table (every `(m+1)`-th of the first `k·(m+1)` table records, payloads
  concatenated) onto `ST`; the table is restored.
-/

namespace SubNLogN.Machine.FFT.DIF

open TMFw TMFw.Contracts WP.W9comp

/-! ## Record-array algebra -/

theorem arrSyms_nil' : arrSyms ([] : List (List Bool)) = [] := rfl

theorem arrSyms_cons' (p : List Bool) (v : List (List Bool)) :
    arrSyms (p :: v) = recSyms p ++ arrSyms v := by
  simp [arrSyms, blk]

theorem arrSyms_append' (u v : List (List Bool)) : arrSyms (u ++ v) = arrSyms u ++ arrSyms v := by
  simp [arrSyms, blk]

theorem recSyms_eq (p : List Bool) : recSyms p = p.map Sym.bit ++ [Sym.sep] := rfl

theorem reverse_recSyms' (p : List Bool) :
    (recSyms p).reverse = Sym.sep :: (p.map Sym.bit).reverse := by
  simp [recSyms]

theorem length_arrSyms_uniform (v : List (List Bool)) (n0 : ℕ) (h : ∀ p ∈ v, p.length = n0) :
    (arrSyms v).length = v.length * (n0 + 1) := by
  induction v with
  | nil => simp [arrSyms_nil']
  | cons p v ih =>
    rw [arrSyms_cons', List.length_append, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp [recSyms, h p List.mem_cons_self]
    ring

/-- Register tests. -/
def isRecO : Option Sym → Bool
  | some (.bit _) => true
  | some .sep => true
  | _ => false

def isSepO : Option Sym → Bool
  | some .sep => true
  | _ => false

theorem isRecO_arrSyms {v : List (List Bool)} {x : Sym} (hx : x ∈ arrSyms v) :
    isRecO (some x) = true := by
  induction v with
  | nil => simp [arrSyms_nil'] at hx
  | cons p v ih =>
    rw [arrSyms_cons', List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [recSyms, List.mem_append, List.mem_map, List.mem_singleton] at hx
      rcases hx with ⟨b, _, rfl⟩ | rfl <;> rfl
    · exact ih hx

theorem isRecO_of_blkTerm {rest : List Sym} (h : BlkTerm rest) : isRecO rest.head? = false := by
  cases rest with
  | nil => rfl
  | cons d l =>
    obtain ⟨h1, h2⟩ := h d rfl
    cases d <;> simp_all [isRecO, isDataSym]

theorem bits_optIsBit (p : List Bool) : ∀ x ∈ p.map Sym.bit, optIsBit (some x) = true := by
  intro x hx
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  rfl

theorem bits_optIsBit_rev (p : List Bool) :
    ∀ x ∈ (p.map Sym.bit).reverse, optIsBit (some x) = true :=
  fun x hx => bits_optIsBit p x (List.mem_reverse.1 hx)

/-- The reversed array starts with `sep` (or is empty): a valid bit-block terminator. -/
theorem termOK_rev_arrSyms (v : List (List Bool)) (R : List Sym) (hR : TermOK R) :
    TermOK ((arrSyms v).reverse ++ R) := by
  rcases List.eq_nil_or_concat v with rfl | ⟨u, p, rfl⟩
  · simpa [arrSyms_nil'] using hR
  · rw [List.concat_eq_append, arrSyms_append', List.reverse_append, arrSyms_cons', arrSyms_nil', List.append_nil,
      reverse_recSyms', List.cons_append, List.cons_append]
    exact TermOK.cons rfl _

theorem head?_rev_arrSyms_cons (u : List (List Bool)) (p : List Bool) (R : List Sym) :
    ((arrSyms (u ++ [p])).reverse ++ R).head? = some Sym.sep := by
  rw [arrSyms_append', List.reverse_append, arrSyms_cons', arrSyms_nil', List.append_nil,
    reverse_recSyms']
  rfl

section Passes

variable {K σ : Type} [DecidableEq K] (lO : Lens σ (Option Sym))

/-! ## One record -/

/-- Move one normal record from `src` to `dst` (it arrives reversed). -/
def moveRec (src dst : K) : Prog K (fun _ => Sym) σ :=
  .seq (movePrefix lO src dst optIsBit) (mv lO src dst)

/-- Move one reversed record from `src` to `dst` (it arrives in normal order). -/
def moveRevRec (src dst : K) : Prog K (fun _ => Sym) σ :=
  .seq (mv lO src dst) (movePrefix lO src dst optIsBit)

omit [DecidableEq K] in
theorem closed_moveRec (src dst : K) : (moveRec lO src dst).Closed :=
  ⟨closed_movePrefix lO src dst _, closed_mv lO src dst⟩

omit [DecidableEq K] in
theorem closed_moveRevRec (src dst : K) : (moveRevRec lO src dst).Closed :=
  ⟨closed_mv lO src dst, closed_movePrefix lO src dst _⟩

theorem runs_moveRec {src dst : K} (hne : src ≠ dst) (S : K → List Sym) (p : List Bool)
    (rest : List Sym) (hS : S src = recSyms p ++ rest) :
    Runs (moveRec lO src dst) S
      (Function.update (Function.update S src rest) dst ((recSyms p).reverse ++ S dst))
      (fun _ => True) (4 * p.length + 4) := by
  have hS' : S src = p.map Sym.bit ++ (Sym.sep :: rest) := by rw [hS]; simp [recSyms]
  have e1 := runs_movePrefix lO hne optIsBit S _ _ hS' (bits_optIsBit p) rfl
  set S1 := Function.update (Function.update S src (Sym.sep :: rest)) dst
    ((p.map Sym.bit).reverse ++ S dst) with hS1
  have h1 : S1 src = Sym.sep :: rest := by
    rw [hS1, Function.update_of_ne hne, Function.update_self]
  have e2 := runs_mv lO hne S1 h1
  refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial)
    (by simp only [List.length_map]; omega)) ?_
  funext j
  simp only [hS1, Function.update_apply, reverse_recSyms']
  split_ifs <;> simp_all

theorem runs_moveRevRec {src dst : K} (hne : src ≠ dst) (S : K → List Sym) (p : List Bool)
    (rest : List Sym) (hrest : TermOK rest) (hS : S src = (recSyms p).reverse ++ rest) :
    Runs (moveRevRec lO src dst) S
      (Function.update (Function.update S src rest) dst (recSyms p ++ S dst))
      (fun _ => True) (4 * p.length + 4) := by
  have hS' : S src = Sym.sep :: ((p.map Sym.bit).reverse ++ rest) := by
    rw [hS, reverse_recSyms']; rfl
  have e1 := runs_mv lO hne S hS'
  set S1 := Function.update (Function.update S src ((p.map Sym.bit).reverse ++ rest)) dst
    (Sym.sep :: S dst) with hS1
  have h1 : S1 src = (p.map Sym.bit).reverse ++ rest := by
    rw [hS1, Function.update_of_ne hne, Function.update_self]
  have e2 := runs_movePrefix lO hne optIsBit S1 _ _ h1 (bits_optIsBit_rev p)
    (optIsBit_head?_of_termOK hrest)
  refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial)
    (by simp only [List.length_reverse, List.length_map]; omega)) ?_
  funext j
  simp only [hS1, Function.update_apply, recSyms_eq, List.reverse_reverse]
  split_ifs <;> simp_all

/-! ## Whole arrays -/

theorem runs_revArr_out {src dst : K} (hne : src ≠ dst) (S : K → List Sym)
    (v : List (List Bool)) (rest : List Sym) (hS : S src = arrSyms v ++ rest)
    (hrest : BlkTerm rest) :
    Runs (movePrefix lO src dst isRecO) S
      (Function.update (Function.update S src rest) dst ((arrSyms v).reverse ++ S dst))
      (fun _ => True) (4 * (arrSyms v).length + 2) :=
  runs_movePrefix lO hne isRecO S _ _ hS (fun _ hx => isRecO_arrSyms hx)
    (isRecO_of_blkTerm hrest)

theorem runs_revArr_in {src dst : K} (hne : src ≠ dst) (S : K → List Sym)
    (v : List (List Bool)) (hS : S src = (arrSyms v).reverse) :
    Runs (movePrefix lO src dst isRecO) S
      (Function.update (Function.update S src []) dst (arrSyms v ++ S dst))
      (fun _ => True) (4 * (arrSyms v).length + 2) := by
  have h := runs_movePrefix lO hne isRecO S _ [] (by rw [hS, List.append_nil])
    (fun _ hx => isRecO_arrSyms (List.mem_reverse.1 hx)) rfl
  simpa [List.reverse_reverse] using h

/-! ## Record interleave (`rmerge`) -/

/-- Records of `X` and `Z` alternately onto `T`. -/
def rmerge (X Z T : K) : Prog K (fun _ => Sym) σ :=
  ploop lO X Option.isSome (.seq (moveRec lO X T) (moveRec lO Z T))

omit [DecidableEq K] in
theorem closed_rmerge (X Z T : K) : (rmerge lO X Z T).Closed :=
  closed_ploop lO X _ ⟨closed_moveRec lO X T, closed_moveRec lO Z T⟩

theorem arrSyms_inter_take_succ (xs zs : List (List Bool)) (i : ℕ) (hx : i < xs.length)
    (hz : i < zs.length) :
    (arrSyms (inter (xs.take (i + 1)) (zs.take (i + 1)))).reverse =
      (recSyms zs[i]).reverse ++ ((recSyms xs[i]).reverse ++
        (arrSyms (inter (xs.take i) (zs.take i))).reverse) := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hx,
    List.getElem?_eq_getElem hz, Option.toList_some, Option.toList_some,
    inter_append_pair _ _ _ _ (by simp; omega), arrSyms_append']
  simp [arrSyms_cons', arrSyms_nil']

theorem runs_rmerge {X Z T : K} (h1 : X ≠ Z) (h2 : X ≠ T) (h3 : Z ≠ T) (S : K → List Sym)
    (xs zs : List (List Bool)) (n0 : ℕ) (hlen : xs.length = zs.length)
    (hx : ∀ p ∈ xs, p.length = n0) (hz : ∀ p ∈ zs, p.length = n0)
    (hX : S X = arrSyms xs) (hZ : S Z = arrSyms zs) :
    Runs (rmerge lO X Z T) S
      (Function.update (Function.update (Function.update S X []) Z []) T
        ((arrSyms (inter xs zs)).reverse ++ S T))
      (fun _ => True) (xs.length * (8 * n0 + 10) + 2) := by
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (Function.update S X (arrSyms (xs.drop i))) Z
      (arrSyms (zs.drop i))) T ((arrSyms (inter (xs.take i) (zs.take i))).reverse ++ S T)
  have hStX : ∀ i, St i X = arrSyms (xs.drop i) := fun i => by
    simp only [St, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self]
  have hStZ : ∀ i, St i Z = arrSyms (zs.drop i) := fun i => by
    simp only [St, Function.update_of_ne h3, Function.update_self]
  have h0 : St 0 = S := by
    funext j
    simp only [St, Function.update_apply, List.drop_zero, List.take_zero]
    split_ifs <;> simp_all [inter, arrSyms_nil']
  have hloop := runs_ploop_const lO X Option.isSome
    (.seq (moveRec lO X T) (moveRec lO Z T)) xs.length St (8 * n0 + 8) ?_ ?_
  · rw [h0] at hloop
    refine runs_congr (runs_mono hloop (fun _ _ => trivial) le_rfl) ?_
    have e1 : xs.drop xs.length = [] := List.drop_length
    have e2 : zs.drop xs.length = [] := by rw [hlen]; exact List.drop_length
    have e3 : xs.take xs.length = xs := List.take_length
    have e4 : zs.take xs.length = zs := by rw [hlen]; exact List.take_length
    funext j
    simp only [St, Function.update_apply, e1, e2, e3, e4, arrSyms_nil']
  · intro i hi
    rw [hStX]
    rcases Nat.lt_or_ge i xs.length with hlt | hge
    · rw [List.drop_eq_getElem_cons hlt, arrSyms_cons']
      cases h : xs[i] <;> simp [recSyms, hlt]
    · rw [List.drop_of_length_le hge, arrSyms_nil']
      simp only [List.head?_nil, Option.isSome_none]
      exact (decide_eq_false (by omega)).symm
  · intro i hi
    have hi' : i < zs.length := hlen ▸ hi
    have hxi : St i X = recSyms xs[i] ++ arrSyms (xs.drop (i + 1)) := by
      rw [hStX, List.drop_eq_getElem_cons hi, arrSyms_cons']
    have e1 := runs_moveRec lO h2 (St i) xs[i] _ hxi
    set S1 := Function.update (Function.update (St i) X (arrSyms (xs.drop (i + 1)))) T
      ((recSyms xs[i]).reverse ++ St i T) with hS1
    have hzi : S1 Z = recSyms zs[i] ++ arrSyms (zs.drop (i + 1)) := by
      rw [hS1, Function.update_of_ne h3, Function.update_of_ne h1.symm, hStZ,
        List.drop_eq_getElem_cons hi', arrSyms_cons']
    have e2 := runs_moveRec lO h3 S1 zs[i] _ hzi
    have hc : 4 * xs[i].length + 4 + (4 * zs[i].length + 4) ≤ 8 * n0 + 8 := by
      rw [hx _ (List.getElem_mem hi), hz _ (List.getElem_mem hi')]
      omega
    refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial) hc) ?_
    have hT := arrSyms_inter_take_succ xs zs i hi hi'
    funext j
    simp only [hS1, St, Function.update_apply, hT]
    split_ifs <;> simp_all

/-! ## Dealing a reversed interleaved array (`deal`) -/

/-- Deal a reversed array `inter as bs` from `T`: `Q` receives `bs`, `P` receives `as`. -/
def deal (T Q P : K) : Prog K (fun _ => Sym) σ :=
  ploop lO T isSepO (.seq (moveRevRec lO T Q) (moveRevRec lO T P))

omit [DecidableEq K] in
theorem closed_deal (T Q P : K) : (deal lO T Q P).Closed :=
  closed_ploop lO T _ ⟨closed_moveRevRec lO T Q, closed_moveRevRec lO T P⟩

theorem runs_deal {T Q P : K} (h1 : T ≠ Q) (h2 : T ≠ P) (h3 : Q ≠ P) (S : K → List Sym)
    (as bs : List (List Bool)) (n0 : ℕ) (hlen : as.length = bs.length)
    (ha : ∀ p ∈ as, p.length = n0) (hb : ∀ p ∈ bs, p.length = n0)
    (hT : S T = (arrSyms (inter as bs)).reverse) :
    Runs (deal lO T Q P) S
      (Function.update (Function.update (Function.update S T []) Q (arrSyms bs ++ S Q)) P
        (arrSyms as ++ S P))
      (fun _ => True) (as.length * (8 * n0 + 10) + 2) := by
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (Function.update S T
      ((arrSyms (inter (as.take (as.length - i)) (bs.take (as.length - i)))).reverse)) Q
      (arrSyms (bs.drop (as.length - i)) ++ S Q)) P (arrSyms (as.drop (as.length - i)) ++ S P)
  have hStT : ∀ i, St i T = (arrSyms (inter (as.take (as.length - i))
      (bs.take (as.length - i)))).reverse :=
    fun i => by simp only [St, Function.update_of_ne h2, Function.update_of_ne h1,
      Function.update_self]
  have h0 : St 0 = S := by
    have e1 : as.take as.length = as := List.take_length
    have e2 : bs.take as.length = bs := by rw [hlen]; exact List.take_length
    have e3 : as.drop as.length = [] := List.drop_length
    have e4 : bs.drop as.length = [] := by rw [hlen]; exact List.drop_length
    funext j
    simp only [St, Function.update_apply, Nat.sub_zero, e1, e2, e3, e4, arrSyms_nil',
      List.nil_append]
    split_ifs <;> simp_all
  have hloop := runs_ploop_const lO T isSepO
    (.seq (moveRevRec lO T Q) (moveRevRec lO T P)) as.length St (8 * n0 + 8) ?_ ?_
  · rw [h0] at hloop
    refine runs_congr (runs_mono hloop (fun _ _ => trivial) le_rfl) ?_
    funext j
    simp only [St, Function.update_apply, Nat.sub_self, List.take_zero, List.drop_zero, inter,
      arrSyms_nil', List.reverse_nil]
  · intro i hi
    rw [hStT]
    rcases Nat.lt_or_ge i as.length with hlt | hge
    · obtain ⟨j, hj⟩ : ∃ j, as.length - i = j + 1 := ⟨as.length - i - 1, by omega⟩
      have hja : j < as.length := by omega
      have hjb : j < bs.length := by omega
      rw [hj, List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hja,
        List.getElem?_eq_getElem hjb, Option.toList_some, Option.toList_some,
        inter_append_pair _ _ _ _ (by simp; omega), show ∀ (u : List (List Bool)) x y,
          u ++ [x, y] = (u ++ [x]) ++ [y] from fun _ _ _ => by simp]
      have := head?_rev_arrSyms_cons (inter (as.take j) (bs.take j) ++ [as[j]]) bs[j] []
      rw [List.append_nil] at this
      rw [this]
      simp [isSepO, hlt]
    · have : as.length - i = 0 := by omega
      rw [this]
      simp [isSepO, inter, arrSyms_nil']
      omega
  · intro i hi
    obtain ⟨j, hj⟩ : ∃ j, as.length - i = j + 1 := ⟨as.length - i - 1, by omega⟩
    have hj' : as.length - (i + 1) = j := by omega
    have hja : j < as.length := by omega
    have hjb : j < bs.length := by omega
    have hTi : St i T = (recSyms bs[j]).reverse ++ ((recSyms as[j]).reverse ++
        (arrSyms (inter (as.take j) (bs.take j))).reverse) := by
      rw [hStT, hj]
      exact arrSyms_inter_take_succ as bs j hja hjb
    have e1 := runs_moveRevRec lO h1 (St i) bs[j] _
      (by rw [reverse_recSyms', List.cons_append]; exact TermOK.cons rfl _) hTi
    set S1 := Function.update (Function.update (St i) T ((recSyms as[j]).reverse ++
        (arrSyms (inter (as.take j) (bs.take j))).reverse)) Q (recSyms bs[j] ++ St i Q) with hS1
    have hT1 : S1 T = (recSyms as[j]).reverse ++
        (arrSyms (inter (as.take j) (bs.take j))).reverse := by
      rw [hS1, Function.update_of_ne h1, Function.update_self]
    have e2 := runs_moveRevRec lO h2 S1 as[j] _
      (by simpa using termOK_rev_arrSyms (inter (as.take j) (bs.take j)) [] TermOK.nil) hT1
    have hc : 4 * bs[j].length + 4 + (4 * as[j].length + 4) ≤ 8 * n0 + 8 := by
      rw [ha _ (List.getElem_mem hja), hb _ (List.getElem_mem hjb)]
      omega
    refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial) hc) ?_
    have hQ : arrSyms (bs.drop j) = recSyms bs[j] ++ arrSyms (bs.drop (j + 1)) := by
      rw [List.drop_eq_getElem_cons hjb, arrSyms_cons']
    have hP : arrSyms (as.drop j) = recSyms as[j] ++ arrSyms (as.drop (j + 1)) := by
      rw [List.drop_eq_getElem_cons hja, arrSyms_cons']
    funext x
    simp only [hS1, St, Function.update_apply, hj, hj', hQ, hP]
    split_ifs <;> simp_all

/-! ## Coefficientwise merge of record pairs (`cmerge`, one bit-reversal pass) -/

/-- Interleave units of `n` bits of `a` and `b` (`k` units each). -/
def cinterBits (n k : ℕ) (a b : List Bool) : List Bool :=
  (List.range k).flatMap fun j => (a.drop (j * n)).take n ++ (b.drop (j * n)).take n

theorem cinterBits_succ (n k : ℕ) (a b : List Bool) :
    cinterBits n (k + 1) a b =
      cinterBits n k a b ++ ((a.drop (k * n)).take n ++ (b.drop (k * n)).take n) := by
  simp [cinterBits, List.range_succ, List.flatMap_append]

/-- Inner loop: move units of `|R|` bits from `P` and `Q` alternately onto `T`, while `P` shows a
bit. -/
def cmInner (P Q T R A : K) : Prog K (fun _ => Sym) σ :=
  ploop lO P optIsBit (.seq (rmove lO P T R A) (rmove lO Q T R A))

/-- Merge the record pairs of `P` and `Q` unit by unit onto `T`. -/
def cmerge (P Q T R A : K) : Prog K (fun _ => Sym) σ :=
  ploop lO P Option.isSome
    (.seq (cmInner lO P Q T R A) (.seq (popO lO P) (.seq (popO lO Q) (pushK T .sep))))

omit [DecidableEq K] in
theorem closed_cmerge (P Q T R A : K) : (cmerge lO P Q T R A).Closed :=
  closed_ploop lO P _ ⟨closed_ploop lO P _ ⟨closed_rmove lO P T R A, closed_rmove lO Q T R A⟩,
    closed_popO lO P, closed_popO lO Q, closed_pushK T .sep⟩

theorem runs_cmInner {P Q T R A : K} (h1 : P ≠ Q) (h2 : P ≠ T) (h3 : P ≠ R) (h4 : P ≠ A)
    (h5 : Q ≠ T) (h6 : Q ≠ R) (h7 : Q ≠ A) (h8 : T ≠ R) (h9 : T ≠ A) (h10 : R ≠ A)
    (S : K → List Sym) (a b : List Bool) (n k : ℕ) (hn : 1 ≤ n) (ha : a.length = k * n)
    (hb : b.length = k * n) (Prest Qrest : List Sym)
    (hP : S P = a.map Sym.bit ++ Sym.sep :: Prest) (hQ : S Q = b.map Sym.bit ++ Sym.sep :: Qrest)
    (hR : S R = List.replicate n .mark) (hA : S A = []) :
    Runs (cmInner lO P Q T R A) S
      (Function.update (Function.update (Function.update S P (Sym.sep :: Prest)) Q
        (Sym.sep :: Qrest)) T (((cinterBits n k a b).map Sym.bit).reverse ++ S T))
      (fun _ => True) (k * (20 * n + 10) + 2) := by
  let St : ℕ → K → List Sym := fun j =>
    Function.update (Function.update (Function.update S P
      ((a.drop (j * n)).map Sym.bit ++ Sym.sep :: Prest)) Q
      ((b.drop (j * n)).map Sym.bit ++ Sym.sep :: Qrest)) T
      (((cinterBits n j a b).map Sym.bit).reverse ++ S T)
  have hStP : ∀ j, St j P = (a.drop (j * n)).map Sym.bit ++ Sym.sep :: Prest := fun j => by
    simp only [St, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self]
  have hStQ : ∀ j, St j Q = (b.drop (j * n)).map Sym.bit ++ Sym.sep :: Qrest := fun j => by
    simp only [St, Function.update_of_ne h5, Function.update_self]
  have h0 : St 0 = S := by
    funext x
    simp only [St, Function.update_apply, Nat.zero_mul, List.drop_zero]
    split_ifs <;> simp_all [cinterBits]
  have hloop := runs_ploop_const lO P optIsBit
    (.seq (rmove lO P T R A) (rmove lO Q T R A)) k St (20 * n + 8) ?_ ?_
  · rw [h0] at hloop
    refine runs_congr (runs_mono hloop (fun _ _ => trivial) le_rfl) ?_
    have e1 : a.drop (k * n) = [] := List.drop_of_length_le (by omega)
    have e2 : b.drop (k * n) = [] := List.drop_of_length_le (by omega)
    funext x
    simp only [St, Function.update_apply, e1, e2, List.map_nil, List.nil_append]
  · intro j hj
    rw [hStP]
    rcases Nat.lt_or_ge j k with hlt | hge
    · have hl : j * n < a.length := by rw [ha]; exact Nat.mul_lt_mul_of_pos_right hlt hn
      rw [List.drop_eq_getElem_cons hl, List.map_cons, List.cons_append, List.head?_cons]
      exact (decide_eq_true hlt).symm
    · have hl : a.length ≤ j * n := by rw [ha]; exact Nat.mul_le_mul_right n hge
      rw [List.drop_of_length_le hl]
      simp [optIsBit]
      omega
  · intro j hj
    have hjn : (j + 1) * n ≤ k * n := Nat.mul_le_mul_right n hj
    rw [Nat.add_mul, one_mul] at hjn
    have hla : ((a.drop (j * n)).take n).length = n := by
      rw [List.length_take, List.length_drop]; omega
    have hlb : ((b.drop (j * n)).take n).length = n := by
      rw [List.length_take, List.length_drop]; omega
    have hP1 : St j P = ((a.drop (j * n)).take n).map Sym.bit ++
        (((a.drop (j * n)).drop n).map Sym.bit ++ Sym.sep :: Prest) := by
      rw [hStP, ← List.append_assoc, ← List.map_append, List.take_append_drop]
    have hR1 : St j R = List.replicate (((a.drop (j * n)).take n).map Sym.bit).length .mark := by
      rw [List.length_map, hla]
      simp only [St, Function.update_of_ne h8.symm, Function.update_of_ne h6.symm,
        Function.update_of_ne h3.symm, hR]
    have hA1 : St j A = [] := by
      simp only [St, Function.update_of_ne h9.symm, Function.update_of_ne h7.symm,
        Function.update_of_ne h4.symm, hA]
    have e1 := runs_rmove lO h2 h3 h4 h8 h9 h10 (St j) _ _ hR1 hA1 hP1
    set S1 := Function.update (Function.update (St j) P
      (((a.drop (j * n)).drop n).map Sym.bit ++ Sym.sep :: Prest)) T
      ((((a.drop (j * n)).take n).map Sym.bit).reverse ++ St j T) with hS1
    have hQ1 : S1 Q = ((b.drop (j * n)).take n).map Sym.bit ++
        (((b.drop (j * n)).drop n).map Sym.bit ++ Sym.sep :: Qrest) := by
      rw [hS1, Function.update_of_ne h5, Function.update_of_ne h1.symm, hStQ,
        ← List.append_assoc, ← List.map_append, List.take_append_drop]
    have hR2 : S1 R = List.replicate (((b.drop (j * n)).take n).map Sym.bit).length .mark := by
      rw [List.length_map, hlb, hS1, Function.update_of_ne h8.symm, Function.update_of_ne h3.symm,
        hR1, List.length_map, hla]
    have hA2 : S1 A = [] := by
      rw [hS1, Function.update_of_ne h9.symm, Function.update_of_ne h4.symm, hA1]
    have e2 := runs_rmove lO h5 h6 h7 h8 h9 h10 S1 _ _ hR2 hA2 hQ1
    have hc : 10 * (((a.drop (j * n)).take n).map Sym.bit).length + 4 +
        (10 * (((b.drop (j * n)).take n).map Sym.bit).length + 4) ≤ 20 * n + 8 := by
      rw [List.length_map, List.length_map, hla, hlb]; omega
    refine runs_congr (runs_mono (runs_seq' e1 e2) (fun _ _ => trivial) hc) ?_
    have hda : (a.drop (j * n)).drop n = a.drop ((j + 1) * n) := by
      rw [List.drop_drop, Nat.add_mul, one_mul]
    have hdb : (b.drop (j * n)).drop n = b.drop ((j + 1) * n) := by
      rw [List.drop_drop, Nat.add_mul, one_mul]
    have hT : ((cinterBits n (j + 1) a b).map Sym.bit).reverse =
        (((b.drop (j * n)).take n).map Sym.bit).reverse ++
          ((((a.drop (j * n)).take n).map Sym.bit).reverse ++
            ((cinterBits n j a b).map Sym.bit).reverse) := by
      rw [cinterBits_succ]
      simp [List.reverse_append]
    funext x
    simp only [hS1, St, Function.update_apply, hda, hdb, hT]
    split_ifs <;> simp_all

theorem runs_cmerge {P Q T R A : K} (h1 : P ≠ Q) (h2 : P ≠ T) (h3 : P ≠ R) (h4 : P ≠ A)
    (h5 : Q ≠ T) (h6 : Q ≠ R) (h7 : Q ≠ A) (h8 : T ≠ R) (h9 : T ≠ A) (h10 : R ≠ A)
    (S : K → List Sym) (as bs : List (List Bool)) (n k : ℕ) (hn : 1 ≤ n)
    (hlen : as.length = bs.length) (ha : ∀ p ∈ as, p.length = k * n)
    (hb : ∀ p ∈ bs, p.length = k * n)
    (hP : S P = arrSyms as) (hQ : S Q = arrSyms bs) (hR : S R = List.replicate n .mark)
    (hA : S A = []) :
    Runs (cmerge lO P Q T R A) S
      (Function.update (Function.update (Function.update S P []) Q []) T
        ((arrSyms (List.zipWith (cinterBits n k) as bs)).reverse ++ S T))
      (fun _ => True) (as.length * (k * (20 * n + 10) + 9) + 2) := by
  let St : ℕ → K → List Sym := fun i =>
    Function.update (Function.update (Function.update S P (arrSyms (as.drop i))) Q
      (arrSyms (bs.drop i))) T
      ((arrSyms (List.zipWith (cinterBits n k) (as.take i) (bs.take i))).reverse ++ S T)
  have hStP : ∀ i, St i P = arrSyms (as.drop i) := fun i => by
    simp only [St, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_self]
  have hStQ : ∀ i, St i Q = arrSyms (bs.drop i) := fun i => by
    simp only [St, Function.update_of_ne h5, Function.update_self]
  have h0 : St 0 = S := by
    funext x
    simp only [St, Function.update_apply, List.drop_zero, List.take_zero]
    split_ifs <;> simp_all [arrSyms_nil']
  have hloop := runs_ploop_const lO P Option.isSome
    (.seq (cmInner lO P Q T R A) (.seq (popO lO P) (.seq (popO lO Q) (pushK T .sep))))
    as.length St (k * (20 * n + 10) + 2 + 3) ?_ ?_
  · rw [h0] at hloop
    refine runs_congr (runs_mono hloop (fun _ _ => trivial) (by nlinarith)) ?_
    have e1 : as.drop as.length = [] := List.drop_length
    have e2 : bs.drop as.length = [] := by rw [hlen]; exact List.drop_length
    have e3 : as.take as.length = as := List.take_length
    have e4 : bs.take as.length = bs := by rw [hlen]; exact List.take_length
    funext x
    simp only [St, Function.update_apply, e1, e2, e3, e4, arrSyms_nil']
  · intro i hi
    rw [hStP]
    rcases Nat.lt_or_ge i as.length with hlt | hge
    · rw [List.drop_eq_getElem_cons hlt, arrSyms_cons']
      cases h : as[i] <;> simp [recSyms, hlt]
    · rw [List.drop_of_length_le hge, arrSyms_nil']
      simp only [List.head?_nil, Option.isSome_none]
      exact (decide_eq_false (by omega)).symm
  · intro i hi
    have hi' : i < bs.length := hlen ▸ hi
    have hP1 : St i P = as[i].map Sym.bit ++ Sym.sep :: arrSyms (as.drop (i + 1)) := by
      rw [hStP, List.drop_eq_getElem_cons hi, arrSyms_cons']
      simp [recSyms]
    have hQ1 : St i Q = bs[i].map Sym.bit ++ Sym.sep :: arrSyms (bs.drop (i + 1)) := by
      rw [hStQ, List.drop_eq_getElem_cons hi', arrSyms_cons']
      simp [recSyms]
    have hR1 : St i R = List.replicate n .mark := by
      simp only [St, Function.update_of_ne h8.symm, Function.update_of_ne h6.symm,
        Function.update_of_ne h3.symm, hR]
    have hA1 : St i A = [] := by
      simp only [St, Function.update_of_ne h9.symm, Function.update_of_ne h7.symm,
        Function.update_of_ne h4.symm, hA]
    have e1 := runs_cmInner lO h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (St i) as[i] bs[i] n k hn
      (ha _ (List.getElem_mem hi)) (hb _ (List.getElem_mem hi')) _ _ hP1 hQ1 hR1 hA1
    set S1 := Function.update (Function.update (Function.update (St i) P
      (Sym.sep :: arrSyms (as.drop (i + 1)))) Q (Sym.sep :: arrSyms (bs.drop (i + 1)))) T
      (((cinterBits n k as[i] bs[i]).map Sym.bit).reverse ++ St i T) with hS1
    have e2 := runs_popO lO P S1
    have e3 := runs_popO lO Q (Function.update S1 P (S1 P).tail)
    have e4 := runs_pushK (σ := σ) T .sep (Function.update (Function.update S1 P (S1 P).tail) Q
      ((Function.update S1 P (S1 P).tail) Q).tail)
    refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 (runs_seq' e3 e4)))
      (fun _ _ => trivial) le_rfl) ?_
    have hZ : List.zipWith (cinterBits n k) (as.take (i + 1)) (bs.take (i + 1)) =
        List.zipWith (cinterBits n k) (as.take i) (bs.take i) ++ [cinterBits n k as[i] bs[i]] := by
      rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem hi', Option.toList_some, Option.toList_some,
        List.zipWith_append (by simp; omega)]
      rfl
    have hT : (arrSyms (List.zipWith (cinterBits n k) (as.take (i + 1)) (bs.take (i + 1)))).reverse
        = Sym.sep :: (((cinterBits n k as[i] bs[i]).map Sym.bit).reverse ++
          (arrSyms (List.zipWith (cinterBits n k) (as.take i) (bs.take i))).reverse) := by
      rw [hZ, arrSyms_append', List.reverse_append, arrSyms_cons', arrSyms_nil', List.append_nil,
        reverse_recSyms']
      rfl
    funext x
    simp only [hS1, St, Function.update_apply, hT]
    split_ifs <;> simp_all


/-! ## Splitting every record into halves (`split`) -/

/-- One record of the split: a reversed record `a ++ b` (`|b| = k·|R|`) on `T` becomes `b` on `L`,
`a` on `U`, and one copy of the stage record `ST` is pushed on `TH`. -/
def splitBody (T U L TH ST TMP H HA R A : K) : Prog K (fun _ => Sym) σ :=
  .seq (popO lO T) (.seq (pushK L .sep) (.seq (rmoveN lO T L H HA R A) (.seq (pushK U .sep)
    (.seq (movePrefix lO T U optIsBit) (.seq (pushK TH .sep) (copyBits lO ST TH TMP))))))

/-- Split all records of the reversed array on `T`. -/
def split (T U L TH ST TMP H HA R A : K) : Prog K (fun _ => Sym) σ :=
  ploop lO T isSepO (splitBody lO T U L TH ST TMP H HA R A)

omit [DecidableEq K] in
theorem closed_split (T U L TH ST TMP H HA R A : K) :
    (split lO T U L TH ST TMP H HA R A).Closed :=
  closed_ploop lO T _ ⟨closed_popO lO T, closed_pushK L .sep, closed_rmoveN lO T L H HA R A,
    closed_pushK U .sep, closed_movePrefix lO T U _, closed_pushK TH .sep,
    closed_copyBits lO ST TH TMP⟩

set_option maxHeartbeats 1000000 in
theorem runs_split {T U L TH ST TMP H HA R A : K}
    (hd : [T, U, L, TH, ST, TMP, H, HA, R, A].Nodup)
    (S : K → List Sym) (ps : List (List Bool × List Bool)) (st : List Bool) (n k : ℕ)
    (hps1 : ∀ p ∈ ps, p.1.length = k * n) (hps2 : ∀ p ∈ ps, p.2.length = k * n)
    (hT : S T = (arrSyms (ps.map fun p => p.1 ++ p.2)).reverse)
    (hH : S H = List.replicate k .mark) (hHA : S HA = []) (hR : S R = List.replicate n .mark)
    (hA : S A = []) (hST : S ST = recSyms st) (hTMP : S TMP = []) :
    Runs (split lO T U L TH ST TMP H HA R A) S
      (upd4 S T U L TH [] (arrSyms (ps.map Prod.fst) ++ S U) (arrSyms (ps.map Prod.snd) ++ S L)
        (arrSyms (List.replicate ps.length st) ++ S TH))
      (fun _ => True)
      (ps.length * (k * (10 * n + 8) + 4 * k + 4 * (k * n) + 9 * st.length + 16) + 2) := by
  have p0 := List.pairwise_cons.1 hd
  have h_T_U : T ≠ U := p0.1 U (by simp)
  have h_T_L : T ≠ L := p0.1 L (by simp)
  have h_T_TH : T ≠ TH := p0.1 TH (by simp)
  have h_T_ST : T ≠ ST := p0.1 ST (by simp)
  have h_T_TMP : T ≠ TMP := p0.1 TMP (by simp)
  have h_T_H : T ≠ H := p0.1 H (by simp)
  have h_T_HA : T ≠ HA := p0.1 HA (by simp)
  have h_T_R : T ≠ R := p0.1 R (by simp)
  have h_T_A : T ≠ A := p0.1 A (by simp)
  have p1 := List.pairwise_cons.1 p0.2
  have h_U_L : U ≠ L := p1.1 L (by simp)
  have h_U_TH : U ≠ TH := p1.1 TH (by simp)
  have h_U_ST : U ≠ ST := p1.1 ST (by simp)
  have h_U_TMP : U ≠ TMP := p1.1 TMP (by simp)
  have h_U_H : U ≠ H := p1.1 H (by simp)
  have h_U_HA : U ≠ HA := p1.1 HA (by simp)
  have h_U_R : U ≠ R := p1.1 R (by simp)
  have h_U_A : U ≠ A := p1.1 A (by simp)
  have p2 := List.pairwise_cons.1 p1.2
  have h_L_TH : L ≠ TH := p2.1 TH (by simp)
  have h_L_ST : L ≠ ST := p2.1 ST (by simp)
  have h_L_TMP : L ≠ TMP := p2.1 TMP (by simp)
  have h_L_H : L ≠ H := p2.1 H (by simp)
  have h_L_HA : L ≠ HA := p2.1 HA (by simp)
  have h_L_R : L ≠ R := p2.1 R (by simp)
  have h_L_A : L ≠ A := p2.1 A (by simp)
  have p3 := List.pairwise_cons.1 p2.2
  have h_TH_ST : TH ≠ ST := p3.1 ST (by simp)
  have h_TH_TMP : TH ≠ TMP := p3.1 TMP (by simp)
  have h_TH_H : TH ≠ H := p3.1 H (by simp)
  have h_TH_HA : TH ≠ HA := p3.1 HA (by simp)
  have h_TH_R : TH ≠ R := p3.1 R (by simp)
  have h_TH_A : TH ≠ A := p3.1 A (by simp)
  have p4 := List.pairwise_cons.1 p3.2
  have h_ST_TMP : ST ≠ TMP := p4.1 TMP (by simp)
  have h_ST_H : ST ≠ H := p4.1 H (by simp)
  have h_ST_HA : ST ≠ HA := p4.1 HA (by simp)
  have h_ST_R : ST ≠ R := p4.1 R (by simp)
  have h_ST_A : ST ≠ A := p4.1 A (by simp)
  have p5 := List.pairwise_cons.1 p4.2
  have h_TMP_H : TMP ≠ H := p5.1 H (by simp)
  have h_TMP_HA : TMP ≠ HA := p5.1 HA (by simp)
  have h_TMP_R : TMP ≠ R := p5.1 R (by simp)
  have h_TMP_A : TMP ≠ A := p5.1 A (by simp)
  have p6 := List.pairwise_cons.1 p5.2
  have h_H_HA : H ≠ HA := p6.1 HA (by simp)
  have h_H_R : H ≠ R := p6.1 R (by simp)
  have h_H_A : H ≠ A := p6.1 A (by simp)
  have p7 := List.pairwise_cons.1 p6.2
  have h_HA_R : HA ≠ R := p7.1 R (by simp)
  have h_HA_A : HA ≠ A := p7.1 A (by simp)
  have p8 := List.pairwise_cons.1 p7.2
  have h_R_A : R ≠ A := p8.1 A (by simp)
  have hloop := runs_ploop_const lO T isSepO (splitBody lO T U L TH ST TMP H HA R A) ps.length
    (fun i => upd4 S T U L TH
      ((arrSyms ((ps.take (ps.length - i)).map fun p => p.1 ++ p.2)).reverse)
      (arrSyms ((ps.drop (ps.length - i)).map Prod.fst) ++ S U)
      (arrSyms ((ps.drop (ps.length - i)).map Prod.snd) ++ S L)
      (arrSyms (List.replicate i st) ++ S TH))
    (k * (10 * n + 8) + 4 * k + 4 * (k * n) + 9 * st.length + 14) ?_ ?_
  · have e1 : ps.take ps.length = ps := List.take_length
    have e2 : ps.drop ps.length = [] := List.drop_length
    simp only [Nat.sub_zero, e1, e2, List.map_nil, arrSyms_nil', List.nil_append,
      List.replicate_zero, ← hT, upd4_self, Nat.sub_self, List.take_zero, List.drop_zero,
      List.reverse_nil] at hloop
    exact runs_mono hloop (fun _ _ => trivial) le_rfl
  · intro i hi
    rw [upd4_1 h_T_U h_T_L h_T_TH]
    rcases Nat.lt_or_ge i ps.length with hlt | hge
    · obtain ⟨j, hj⟩ : ∃ j, ps.length - i = j + 1 := ⟨ps.length - i - 1, by omega⟩
      have hj' : j < ps.length := by omega
      rw [hj, List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some, List.map_append,
        List.map_singleton]
      have := head?_rev_arrSyms_cons ((ps.take j).map fun p => p.1 ++ p.2)
        (ps[j].1 ++ ps[j].2) []
      rw [List.append_nil] at this
      rw [this]
      simp [isSepO, hlt]
    · have : ps.length - i = 0 := by omega
      rw [this]
      simp [isSepO, arrSyms_nil']
      omega
  · intro i hi
    obtain ⟨j, hj⟩ : ∃ j, ps.length - i = j + 1 := ⟨ps.length - i - 1, by omega⟩
    have hj' : ps.length - (i + 1) = j := by omega
    have hjl : j < ps.length := by omega
    have hla : ps[j].1.length = k * n := hps1 _ (List.getElem_mem hjl)
    have hlb : ps[j].2.length = k * n := hps2 _ (List.getElem_mem hjl)
    have hTR : TermOK (arrSyms ((ps.take j).map fun p => p.1 ++ p.2)).reverse := by
      have := termOK_rev_arrSyms ((ps.take j).map fun p => p.1 ++ p.2) [] TermOK.nil
      rwa [List.append_nil] at this
    have hTi : (arrSyms ((ps.take (ps.length - i)).map fun p => p.1 ++ p.2)).reverse =
        Sym.sep :: ((ps[j].2.map Sym.bit).reverse ++ ((ps[j].1.map Sym.bit).reverse ++
          (arrSyms ((ps.take j).map fun p => p.1 ++ p.2)).reverse)) := by
      rw [hj, List.take_add_one, List.getElem?_eq_getElem hjl, Option.toList_some,
        List.map_append, List.map_singleton, arrSyms_append', List.reverse_append, arrSyms_cons',
        arrSyms_nil', List.append_nil, reverse_recSyms', List.map_append, List.reverse_append,
        List.cons_append, List.append_assoc]
    have hUi : ps.drop (ps.length - i) = ps.drop (j + 1) := by rw [hj]
    have hU1 : arrSyms ((ps.drop (ps.length - (i + 1))).map Prod.fst) ++ S U =
        ps[j].1.map Sym.bit ++ Sym.sep :: (arrSyms ((ps.drop (j + 1)).map Prod.fst) ++ S U) := by
      rw [hj', List.drop_eq_getElem_cons hjl, List.map_cons, arrSyms_cons', recSyms_eq]
      simp
    have hL1 : arrSyms ((ps.drop (ps.length - (i + 1))).map Prod.snd) ++ S L =
        ps[j].2.map Sym.bit ++ Sym.sep :: (arrSyms ((ps.drop (j + 1)).map Prod.snd) ++ S L) := by
      rw [hj', List.drop_eq_getElem_cons hjl, List.map_cons, arrSyms_cons', recSyms_eq]
      simp
    have hTH1 : arrSyms (List.replicate (i + 1) st) ++ S TH =
        st.map Sym.bit ++ Sym.sep :: (arrSyms (List.replicate i st) ++ S TH) := by
      rw [List.replicate_succ, arrSyms_cons', recSyms_eq]
      simp
    have hT1 : (arrSyms ((ps.take (ps.length - (i + 1))).map fun p => p.1 ++ p.2)).reverse =
        (arrSyms ((ps.take j).map fun p => p.1 ++ p.2)).reverse := by rw [hj']
    rw [hTi, hUi, hU1, hL1, hTH1, hT1]
    -- 1. pop the record end
    have e1 := runs_popO lO T (upd4 S T U L TH (Sym.sep :: ((ps[j].2.map Sym.bit).reverse ++
      ((ps[j].1.map Sym.bit).reverse ++ (arrSyms ((ps.take j).map fun p => p.1 ++ p.2)).reverse)))
      (arrSyms ((ps.drop (j + 1)).map Prod.fst) ++ S U)
      (arrSyms ((ps.drop (j + 1)).map Prod.snd) ++ S L) (arrSyms (List.replicate i st) ++ S TH))
    rw [upd4_1 h_T_U h_T_L h_T_TH, upd4_set1 h_T_U h_T_L h_T_TH, List.tail_cons] at e1
    -- 2. push `sep` on `L`
    have e2 := runs_pushK (σ := σ) L .sep (upd4 S T U L TH ((ps[j].2.map Sym.bit).reverse ++
      ((ps[j].1.map Sym.bit).reverse ++ (arrSyms ((ps.take j).map fun p => p.1 ++ p.2)).reverse))
      (arrSyms ((ps.drop (j + 1)).map Prod.fst) ++ S U)
      (arrSyms ((ps.drop (j + 1)).map Prod.snd) ++ S L) (arrSyms (List.replicate i st) ++ S TH))
    rw [upd4_3 h_L_TH, upd4_set3 h_L_TH] at e2
    -- 3. ruled move of the lower half
    have e3 := runs_rmoveN lO h_T_L h_T_H h_T_HA h_T_R h_T_A h_L_H h_L_HA h_L_R h_L_A h_H_HA
      h_H_R h_H_A h_HA_R h_HA_A h_R_A (upd4 S T U L TH ((ps[j].2.map Sym.bit).reverse ++
      ((ps[j].1.map Sym.bit).reverse ++ (arrSyms ((ps.take j).map fun p => p.1 ++ p.2)).reverse))
      (arrSyms ((ps.drop (j + 1)).map Prod.fst) ++ S U)
      (Sym.sep :: (arrSyms ((ps.drop (j + 1)).map Prod.snd) ++ S L))
      (arrSyms (List.replicate i st) ++ S TH)) k n _ _
      (by rw [upd4_o h_T_H.symm h_U_H.symm h_L_H.symm h_TH_H.symm, hH])
      (by rw [upd4_o h_T_HA.symm h_U_HA.symm h_L_HA.symm h_TH_HA.symm, hHA])
      (by rw [upd4_o h_T_R.symm h_U_R.symm h_L_R.symm h_TH_R.symm, hR])
      (by rw [upd4_o h_T_A.symm h_U_A.symm h_L_A.symm h_TH_A.symm, hA])
      (upd4_1 h_T_U h_T_L h_T_TH) (by rw [List.length_reverse, List.length_map, hlb])
    rw [upd4_3 h_L_TH, upd4_set1 h_T_U h_T_L h_T_TH, upd4_set3 h_L_TH,
      List.reverse_reverse] at e3
    -- 4. push `sep` on `U`
    have e4 := runs_pushK (σ := σ) U .sep (upd4 S T U L TH ((ps[j].1.map Sym.bit).reverse ++
      (arrSyms ((ps.take j).map fun p => p.1 ++ p.2)).reverse)
      (arrSyms ((ps.drop (j + 1)).map Prod.fst) ++ S U)
      (ps[j].2.map Sym.bit ++ Sym.sep :: (arrSyms ((ps.drop (j + 1)).map Prod.snd) ++ S L))
      (arrSyms (List.replicate i st) ++ S TH))
    rw [upd4_2 h_U_L h_U_TH, upd4_set2 h_U_L h_U_TH] at e4
    -- 5. move the upper half
    have e5 := runs_movePrefix lO h_T_U optIsBit (upd4 S T U L TH ((ps[j].1.map Sym.bit).reverse ++
      (arrSyms ((ps.take j).map fun p => p.1 ++ p.2)).reverse)
      (Sym.sep :: (arrSyms ((ps.drop (j + 1)).map Prod.fst) ++ S U))
      (ps[j].2.map Sym.bit ++ Sym.sep :: (arrSyms ((ps.drop (j + 1)).map Prod.snd) ++ S L))
      (arrSyms (List.replicate i st) ++ S TH)) _ _ (upd4_1 h_T_U h_T_L h_T_TH)
      (bits_optIsBit_rev _) (optIsBit_head?_of_termOK hTR)
    rw [upd4_2 h_U_L h_U_TH, upd4_set1 h_T_U h_T_L h_T_TH, upd4_set2 h_U_L h_U_TH,
      List.reverse_reverse] at e5
    -- 6. push `sep` on `TH`
    have e6 := runs_pushK (σ := σ) TH .sep (upd4 S T U L TH
      (arrSyms ((ps.take j).map fun p => p.1 ++ p.2)).reverse
      (ps[j].1.map Sym.bit ++ Sym.sep :: (arrSyms ((ps.drop (j + 1)).map Prod.fst) ++ S U))
      (ps[j].2.map Sym.bit ++ Sym.sep :: (arrSyms ((ps.drop (j + 1)).map Prod.snd) ++ S L))
      (arrSyms (List.replicate i st) ++ S TH))
    rw [upd4_4, upd4_set4] at e6
    -- 7. copy the stage record
    have e7 := runs_copyBits lO (Ne.symm h_TH_ST) h_ST_TMP h_TH_TMP (upd4 S T U L TH
      (arrSyms ((ps.take j).map fun p => p.1 ++ p.2)).reverse
      (ps[j].1.map Sym.bit ++ Sym.sep :: (arrSyms ((ps.drop (j + 1)).map Prod.fst) ++ S U))
      (ps[j].2.map Sym.bit ++ Sym.sep :: (arrSyms ((ps.drop (j + 1)).map Prod.snd) ++ S L))
      (Sym.sep :: (arrSyms (List.replicate i st) ++ S TH))) st [Sym.sep]
      (by rw [upd4_o h_T_ST.symm h_U_ST.symm h_L_ST.symm h_TH_ST.symm, hST]; rfl)
      (TermOK.cons rfl _)
      (by rw [upd4_o h_T_TMP.symm h_U_TMP.symm h_L_TMP.symm h_TH_TMP.symm, hTMP];
          exact TermOK.nil)
    rw [upd4_4, upd4_set4] at e7
    have hc : 1 + (1 + (k * (10 * n + 8) + 4 * k + 4 + (1 + (4 * (ps[j].1.map Sym.bit).reverse.length +
        2 + (1 + (9 * st.length + 4)))))) ≤
        k * (10 * n + 8) + 4 * k + 4 * (k * n) + 9 * st.length + 14 := by
      rw [List.length_reverse, List.length_map, hla]
      omega
    exact runs_mono (runs_seq' e1 (runs_seq' e2 (runs_seq' e3 (runs_seq' e4
      (runs_seq' e5 (runs_seq' e6 e7)))))) (fun _ _ => trivial) hc


/-! ## Gathering the stage table (`gather`) -/

/-- Skip `|QC|` records: move them from `TB` to `TT` (reversed); the counter is restored. -/
def skipRecs (TB TT QC QA : K) : Prog K (fun _ => Sym) σ :=
  .seq (ploop lO QC Option.isSome (.seq (popO lO QC) (.seq (pushK QA .mark) (moveRec lO TB TT))))
    (movePrefix lO QA QC Option.isSome)

omit [DecidableEq K] in
theorem closed_skipRecs (TB TT QC QA : K) : (skipRecs lO TB TT QC QA).Closed :=
  ⟨closed_ploop lO QC _ ⟨closed_popO lO QC, closed_pushK QA .mark, closed_moveRec lO TB TT⟩,
    closed_movePrefix lO QA QC _⟩

theorem runs_skipRecs {TB TT QC QA : K} (h1 : TB ≠ TT) (h2 : TB ≠ QC) (h3 : TB ≠ QA)
    (h4 : TT ≠ QC) (h5 : TT ≠ QA) (h6 : QC ≠ QA) (S : K → List Sym) (tab : List (List Bool))
    (trest : List Sym) (n0 b m : ℕ) (htab : ∀ p ∈ tab, p.length = n0) (hbm : b + m ≤ tab.length)
    (hTB : S TB = arrSyms (tab.drop b) ++ trest) (hTT : S TT = (arrSyms (tab.take b)).reverse)
    (hQC : S QC = List.replicate m .mark) (hQA : S QA = []) :
    Runs (skipRecs lO TB TT QC QA) S
      (Function.update (Function.update S TB (arrSyms (tab.drop (b + m)) ++ trest)) TT
        (arrSyms (tab.take (b + m))).reverse) (fun _ => True) (m * (4 * n0 + 8) + 4 * m + 4) := by
  let St : ℕ → K → List Sym := fun j =>
    Function.update (Function.update (Function.update (Function.update S TB
      (arrSyms (tab.drop (b + j)) ++ trest)) TT (arrSyms (tab.take (b + j))).reverse) QC
      (List.replicate (m - j) .mark)) QA (List.replicate j .mark)
  have hStQC : ∀ j, St j QC = List.replicate (m - j) .mark := fun j => by
    simp only [St, Function.update_of_ne h6, Function.update_self]
  have hStQA : ∀ j, St j QA = List.replicate j .mark := fun j => by
    simp only [St, Function.update_self]
  have hStTB : ∀ j, St j TB = arrSyms (tab.drop (b + j)) ++ trest := fun j => by
    simp only [St, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1,
      Function.update_self]
  have h0 : St 0 = S := by
    funext x
    simp only [St, Function.update_apply, Nat.add_zero, Nat.sub_zero]
    split_ifs <;> simp_all
  have hloop := runs_ploop_const lO QC Option.isSome
    (.seq (popO lO QC) (.seq (pushK QA .mark) (moveRec lO TB TT))) m St (4 * n0 + 6) ?_ ?_
  · rw [h0] at hloop
    have hQA' : St m QA = List.replicate m .mark ++ [] := by rw [hStQA, List.append_nil]
    have hrest := runs_movePrefix lO h6.symm Option.isSome (St m) _ [] hQA' (by simp) rfl
    refine runs_congr (runs_mono (runs_seq hloop hrest) (fun _ _ => trivial)
      (by simp only [List.length_replicate]; nlinarith)) ?_
    funext x
    simp only [St, Function.update_apply, Nat.sub_self, List.replicate_zero]
    split_ifs <;> simp_all
  · intro j hj
    rw [hStQC, isSome_head?_replicate]
    exact decide_eq_decide.mpr (by omega)
  · intro j hj
    have hbj : b + j < tab.length := by omega
    have e1 := runs_popO lO QC (St j)
    have e2 := runs_pushK (σ := σ) QA .mark (Function.update (St j) QC (St j QC).tail)
    set S2 := Function.update (Function.update (St j) QC (St j QC).tail) QA
      (Sym.mark :: Function.update (St j) QC (St j QC).tail QA) with hS2
    have hS2TB : S2 TB = recSyms tab[b + j] ++ (arrSyms (tab.drop (b + j + 1)) ++ trest) := by
      rw [hS2, Function.update_of_ne h3, Function.update_of_ne h2, hStTB,
        List.drop_eq_getElem_cons hbj, arrSyms_cons', List.append_assoc]
    have e3 := runs_moveRec lO h1 S2 tab[b + j] _ hS2TB
    have hc : 1 + (1 + (4 * tab[b + j].length + 4)) ≤ 4 * n0 + 6 := by
      rw [htab _ (List.getElem_mem hbj)]; omega
    refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 e3)) (fun _ _ => trivial) hc) ?_
    have hTT' : (arrSyms (tab.take (b + j + 1))).reverse =
        (recSyms tab[b + j]).reverse ++ (arrSyms (tab.take (b + j))).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hbj,
        Option.toList_some, arrSyms_append', List.reverse_append, arrSyms_cons', arrSyms_nil',
        List.append_nil]
    have hrep : List.replicate (m - j) Sym.mark = Sym.mark :: List.replicate (m - (j + 1)) .mark := by
      rw [show m - j = (m - (j + 1)) + 1 by omega, List.replicate_succ]
    funext x
    simp only [hS2, St, Function.update_apply, hTT', show b + (j + 1) = b + j + 1 by omega]
    split_ifs <;> simp_all [List.replicate_succ]

/-- The stage table: the payloads of table records `0, m+1, 2(m+1), …` (`k` of them),
concatenated. -/
def stageBits (tab : List (List Bool)) (k m : ℕ) : List Bool :=
  (List.range k).flatMap fun j => tab.getD (j * (m + 1)) []

/-- One gather step: copy one table record's payload (reversed) onto `ACC`, skip `m` more. -/
def gatherBody (TB TT ACC QC QA H HA : K) : Prog K (fun _ => Sym) σ :=
  .seq (popO lO H) (.seq (pushK HA .mark) (.seq (dupPrefix lO TB TT ACC optIsBit)
    (.seq (mv lO TB TT) (skipRecs lO TB TT QC QA))))

/-- Gather the stage table onto `ST` (one forward scan of `k·(m+1)` table records and one rewind). -/
def gather (TB TT ACC ST QC QA H HA : K) : Prog K (fun _ => Sym) σ :=
  .seq (ploop lO H Option.isSome (gatherBody lO TB TT ACC QC QA H HA))
    (.seq (movePrefix lO HA H Option.isSome) (.seq (movePrefix lO TT TB isRecO)
      (.seq (pushK ST .sep) (movePrefix lO ACC ST optIsBit))))

omit [DecidableEq K] in
theorem closed_gather (TB TT ACC ST QC QA H HA : K) :
    (gather lO TB TT ACC ST QC QA H HA).Closed :=
  ⟨closed_ploop lO H _ ⟨closed_popO lO H, closed_pushK HA .mark, closed_dupPrefix lO TB TT ACC _,
    closed_mv lO TB TT, closed_skipRecs lO TB TT QC QA⟩, closed_movePrefix lO HA H _,
    closed_movePrefix lO TT TB _, closed_pushK ST .sep, closed_movePrefix lO ACC ST _⟩

set_option maxHeartbeats 1000000 in
theorem runs_gather {TB TT ACC ST QC QA H HA : K} (hd : [TB, TT, ACC, ST, QC, QA, H, HA].Nodup)
    (S : K → List Sym) (tab : List (List Bool)) (trest : List Sym) (n0 k m : ℕ)
    (htab : ∀ p ∈ tab, p.length = n0) (hk : k * (m + 1) ≤ tab.length)
    (hTB : S TB = arrSyms tab ++ trest) (hTT : S TT = []) (hACC : S ACC = [])
    (hH : S H = List.replicate k .mark) (hHA : S HA = []) (hQC : S QC = List.replicate m .mark)
    (hQA : S QA = []) :
    Runs (gather lO TB TT ACC ST QC QA H HA) S
      (Function.update S ST (recSyms (stageBits tab k m) ++ S ST)) (fun _ => True)
      (k * (5 * n0 + m * (4 * n0 + 8) + 4 * m + 12 + 2) + 2 + (4 * k + 2) +
        (4 * (k * (m + 1) * (n0 + 1)) + 2) + 1 + (4 * (k * n0) + 2)) := by
  have p0 := List.pairwise_cons.1 hd
  have h_TB_TT : TB ≠ TT := p0.1 TT (by simp)
  have h_TB_ACC : TB ≠ ACC := p0.1 ACC (by simp)
  have h_TB_ST : TB ≠ ST := p0.1 ST (by simp)
  have h_TB_QC : TB ≠ QC := p0.1 QC (by simp)
  have h_TB_QA : TB ≠ QA := p0.1 QA (by simp)
  have h_TB_H : TB ≠ H := p0.1 H (by simp)
  have h_TB_HA : TB ≠ HA := p0.1 HA (by simp)
  have p1 := List.pairwise_cons.1 p0.2
  have h_TT_ACC : TT ≠ ACC := p1.1 ACC (by simp)
  have h_TT_ST : TT ≠ ST := p1.1 ST (by simp)
  have h_TT_QC : TT ≠ QC := p1.1 QC (by simp)
  have h_TT_QA : TT ≠ QA := p1.1 QA (by simp)
  have h_TT_H : TT ≠ H := p1.1 H (by simp)
  have h_TT_HA : TT ≠ HA := p1.1 HA (by simp)
  have p2 := List.pairwise_cons.1 p1.2
  have h_ACC_ST : ACC ≠ ST := p2.1 ST (by simp)
  have h_ACC_QC : ACC ≠ QC := p2.1 QC (by simp)
  have h_ACC_QA : ACC ≠ QA := p2.1 QA (by simp)
  have h_ACC_H : ACC ≠ H := p2.1 H (by simp)
  have h_ACC_HA : ACC ≠ HA := p2.1 HA (by simp)
  have p3 := List.pairwise_cons.1 p2.2
  have h_ST_QC : ST ≠ QC := p3.1 QC (by simp)
  have h_ST_QA : ST ≠ QA := p3.1 QA (by simp)
  have h_ST_H : ST ≠ H := p3.1 H (by simp)
  have h_ST_HA : ST ≠ HA := p3.1 HA (by simp)
  have p4 := List.pairwise_cons.1 p3.2
  have h_QC_QA : QC ≠ QA := p4.1 QA (by simp)
  have h_QC_H : QC ≠ H := p4.1 H (by simp)
  have h_QC_HA : QC ≠ HA := p4.1 HA (by simp)
  have p5 := List.pairwise_cons.1 p4.2
  have h_QA_H : QA ≠ H := p5.1 H (by simp)
  have h_QA_HA : QA ≠ HA := p5.1 HA (by simp)
  have p6 := List.pairwise_cons.1 p5.2
  have h_H_HA : H ≠ HA := p6.1 HA (by simp)
  have hS0 : upd5 S TB TT ACC H HA (arrSyms tab ++ trest) [] [] (List.replicate k .mark) [] = S := by
    have := @upd5_self K _ S TB TT ACC H HA
    rw [hTB, hTT, hACC, hH, hHA] at this
    exact this
  have hloop := runs_ploop_const lO H Option.isSome (gatherBody lO TB TT ACC QC QA H HA) k
    (fun i => upd5 S TB TT ACC H HA (arrSyms (tab.drop (i * (m + 1))) ++ trest)
      (arrSyms (tab.take (i * (m + 1)))).reverse ((stageBits tab i m).map Sym.bit).reverse
      (List.replicate (k - i) .mark) (List.replicate i .mark))
    (5 * n0 + m * (4 * n0 + 8) + 4 * m + 12) ?_ ?_
  · have hst0 : stageBits tab 0 m = [] := by simp [stageBits]
    simp only [Nat.zero_mul, List.drop_zero, List.take_zero, arrSyms_nil', List.reverse_nil,
      Nat.sub_zero, List.replicate_zero, hst0, List.map_nil, Nat.sub_self] at hloop
    rw [hS0] at hloop
    -- restore `H`
    have e1 := runs_movePrefix lO h_H_HA.symm Option.isSome (upd5 S TB TT ACC H HA
      (arrSyms (tab.drop (k * (m + 1))) ++ trest) (arrSyms (tab.take (k * (m + 1)))).reverse
      ((stageBits tab k m).map Sym.bit).reverse [] (List.replicate k .mark))
      (List.replicate k .mark) [] (by rw [upd5_5, List.append_nil]) (by simp) rfl
    rw [upd5_4 h_H_HA, upd5_set5, upd5_set4 h_H_HA, List.reverse_replicate, List.append_nil] at e1
    -- rewind the table
    have e2 := runs_movePrefix lO h_TB_TT.symm isRecO (upd5 S TB TT ACC H HA
      (arrSyms (tab.drop (k * (m + 1))) ++ trest) (arrSyms (tab.take (k * (m + 1)))).reverse
      ((stageBits tab k m).map Sym.bit).reverse (List.replicate k .mark) [])
      (arrSyms (tab.take (k * (m + 1)))).reverse []
      (by rw [upd5_2 h_TT_ACC h_TT_H h_TT_HA, List.append_nil])
      (fun _ hx => isRecO_arrSyms (List.mem_reverse.1 hx)) rfl
    rw [upd5_1 h_TB_TT h_TB_ACC h_TB_H h_TB_HA, upd5_set2 h_TT_ACC h_TT_H h_TT_HA,
      upd5_set1 h_TB_TT h_TB_ACC h_TB_H h_TB_HA, List.reverse_reverse, ← List.append_assoc,
      ← arrSyms_append', List.take_append_drop] at e2
    -- push `sep` on `ST`, then move the reversed stage payload
    set X2 := upd5 S TB TT ACC H HA (arrSyms tab ++ trest) []
      ((stageBits tab k m).map Sym.bit).reverse (List.replicate k .mark) [] with hX2
    have hX2ST : X2 ST = S ST := upd5_o h_TB_ST.symm h_TT_ST.symm h_ACC_ST.symm h_ST_H h_ST_HA
    have e3 := runs_pushK (σ := σ) ST .sep X2
    rw [hX2ST] at e3
    have e4 := runs_movePrefix lO h_ACC_ST optIsBit (Function.update X2 ST (Sym.sep :: S ST))
      ((stageBits tab k m).map Sym.bit).reverse []
      (by rw [Function.update_of_ne h_ACC_ST, hX2, upd5_3 h_ACC_H h_ACC_HA, List.append_nil])
      (bits_optIsBit_rev _) rfl
    rw [Function.update_self, List.reverse_reverse, Function.update_comm h_ACC_ST,
      Function.update_idem, Function.update_comm h_ACC_ST.symm, upd5_set3 h_ACC_H h_ACC_HA,
      hS0, show List.map Sym.bit (stageBits tab k m) ++ Sym.sep :: S ST =
        recSyms (stageBits tab k m) ++ S ST by simp [recSyms_eq]] at e4
    have hlen1 : (arrSyms (tab.take (k * (m + 1)))).length = k * (m + 1) * (n0 + 1) := by
      rw [length_arrSyms_uniform _ n0 (fun p hp => htab p (List.mem_of_mem_take hp)),
        List.length_take, Nat.min_eq_left hk]
    have hlen2 : (stageBits tab k m).length = k * n0 := by
      unfold stageBits
      rw [List.length_flatMap]
      have : ∀ j ∈ List.range k, (tab.getD (j * (m + 1)) []).length = n0 := by
        intro j hj
        have hj' : j * (m + 1) < tab.length := by
          have := List.mem_range.1 hj
          have : (j + 1) * (m + 1) ≤ k * (m + 1) := Nat.mul_le_mul_right _ this
          rw [Nat.add_mul, one_mul] at this
          omega
        rw [List.getD_eq_getElem _ _ hj']
        exact htab _ (List.getElem_mem hj')
      rw [List.map_congr_left this]
      simp
    refine runs_mono (runs_seq hloop (runs_seq' e1 (runs_seq' e2 (runs_seq' e3 e4))))
      (fun _ _ => trivial) ?_
    simp only [List.length_replicate, List.length_reverse, List.length_map, hlen1, hlen2]
    simp only [recSyms_eq, List.append_assoc, List.singleton_append] at *
    omega
  · intro i hi
    rw [upd5_4 h_H_HA, isSome_head?_replicate]
    exact decide_eq_decide.mpr (by omega)
  · intro i hi
    have hb : i * (m + 1) + 1 + m ≤ tab.length := by
      have : (i + 1) * (m + 1) ≤ k * (m + 1) := Nat.mul_le_mul_right _ hi
      rw [Nat.add_mul, one_mul] at this
      omega
    have hbl : i * (m + 1) < tab.length := by omega
    have hlt : tab[i * (m + 1)].length = n0 := htab _ (List.getElem_mem hbl)
    have hTBi : arrSyms (tab.drop (i * (m + 1))) ++ trest = tab[i * (m + 1)].map Sym.bit ++
        (Sym.sep :: (arrSyms (tab.drop (i * (m + 1) + 1)) ++ trest)) := by
      rw [List.drop_eq_getElem_cons hbl, arrSyms_cons', recSyms_eq]
      simp
    have hrep : List.replicate (k - i) Sym.mark = Sym.mark :: List.replicate (k - (i + 1)) .mark := by
      rw [show k - i = (k - (i + 1)) + 1 by omega, List.replicate_succ]
    have hTT1 : Sym.sep :: ((tab[i * (m + 1)].map Sym.bit).reverse ++
        (arrSyms (tab.take (i * (m + 1)))).reverse) = (arrSyms (tab.take (i * (m + 1) + 1))).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hbl, Option.toList_some, arrSyms_append',
        List.reverse_append, arrSyms_cons', arrSyms_nil', List.append_nil, reverse_recSyms']
      rfl
    have hidx : i * (m + 1) + 1 + m = (i + 1) * (m + 1) := by ring
    have hACC : ((stageBits tab (i + 1) m).map Sym.bit).reverse =
        (tab[i * (m + 1)].map Sym.bit).reverse ++ ((stageBits tab i m).map Sym.bit).reverse := by
      rw [stageBits, List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.getD_eq_getElem _ _ hbl, List.map_append, List.reverse_append]
      rfl
    rw [hTBi, hrep]
    -- 1. pop `H`
    have e1 := runs_popO lO H (upd5 S TB TT ACC H HA (tab[i * (m + 1)].map Sym.bit ++
      (Sym.sep :: (arrSyms (tab.drop (i * (m + 1) + 1)) ++ trest)))
      (arrSyms (tab.take (i * (m + 1)))).reverse ((stageBits tab i m).map Sym.bit).reverse
      (Sym.mark :: List.replicate (k - (i + 1)) .mark) (List.replicate i .mark))
    rw [upd5_4 h_H_HA, upd5_set4 h_H_HA, List.tail_cons] at e1
    -- 2. park the mark on `HA`
    have e2 := runs_pushK (σ := σ) HA .mark (upd5 S TB TT ACC H HA (tab[i * (m + 1)].map Sym.bit ++
      (Sym.sep :: (arrSyms (tab.drop (i * (m + 1) + 1)) ++ trest)))
      (arrSyms (tab.take (i * (m + 1)))).reverse ((stageBits tab i m).map Sym.bit).reverse
      (List.replicate (k - (i + 1)) .mark) (List.replicate i .mark))
    rw [upd5_5, upd5_set5] at e2
    -- 3. copy the payload to `TT` and `ACC`
    have e3 := runs_dupPrefix lO h_TB_TT h_TB_ACC h_TT_ACC optIsBit (upd5 S TB TT ACC H HA
      (tab[i * (m + 1)].map Sym.bit ++ (Sym.sep :: (arrSyms (tab.drop (i * (m + 1) + 1)) ++ trest)))
      (arrSyms (tab.take (i * (m + 1)))).reverse ((stageBits tab i m).map Sym.bit).reverse
      (List.replicate (k - (i + 1)) .mark) (Sym.mark :: List.replicate i .mark)) _ _
      (upd5_1 h_TB_TT h_TB_ACC h_TB_H h_TB_HA) (bits_optIsBit _) rfl
    rw [upd5_2 h_TT_ACC h_TT_H h_TT_HA, upd5_3 h_ACC_H h_ACC_HA,
      upd5_set1 h_TB_TT h_TB_ACC h_TB_H h_TB_HA, upd5_set2 h_TT_ACC h_TT_H h_TT_HA,
      upd5_set3 h_ACC_H h_ACC_HA] at e3
    -- 4. move the record end
    have e4 := runs_mv lO h_TB_TT (upd5 S TB TT ACC H HA
      (Sym.sep :: (arrSyms (tab.drop (i * (m + 1) + 1)) ++ trest))
      ((tab[i * (m + 1)].map Sym.bit).reverse ++ (arrSyms (tab.take (i * (m + 1)))).reverse)
      ((tab[i * (m + 1)].map Sym.bit).reverse ++ ((stageBits tab i m).map Sym.bit).reverse)
      (List.replicate (k - (i + 1)) .mark) (Sym.mark :: List.replicate i .mark))
      (upd5_1 h_TB_TT h_TB_ACC h_TB_H h_TB_HA)
    rw [upd5_2 h_TT_ACC h_TT_H h_TT_HA, upd5_set1 h_TB_TT h_TB_ACC h_TB_H h_TB_HA,
      upd5_set2 h_TT_ACC h_TT_H h_TT_HA, hTT1] at e4
    -- 5. skip `m` records
    have e5 := runs_skipRecs lO h_TB_TT h_TB_QC h_TB_QA h_TT_QC h_TT_QA h_QC_QA (upd5 S TB TT ACC H HA
      (arrSyms (tab.drop (i * (m + 1) + 1)) ++ trest) (arrSyms (tab.take (i * (m + 1) + 1))).reverse
      ((tab[i * (m + 1)].map Sym.bit).reverse ++ ((stageBits tab i m).map Sym.bit).reverse)
      (List.replicate (k - (i + 1)) .mark) (Sym.mark :: List.replicate i .mark)) tab trest n0
      (i * (m + 1) + 1) m htab hb (upd5_1 h_TB_TT h_TB_ACC h_TB_H h_TB_HA)
      (upd5_2 h_TT_ACC h_TT_H h_TT_HA)
      (by rw [upd5_o h_TB_QC.symm h_TT_QC.symm h_ACC_QC.symm h_QC_H h_QC_HA, hQC])
      (by rw [upd5_o h_TB_QA.symm h_TT_QA.symm h_ACC_QA.symm h_QA_H h_QA_HA, hQA])
    rw [upd5_set1 h_TB_TT h_TB_ACC h_TB_H h_TB_HA, upd5_set2 h_TT_ACC h_TT_H h_TT_HA, hidx] at e5
    have hc : 1 + (1 + (5 * (tab[i * (m + 1)].map Sym.bit).length + 2 + (2 +
        (m * (4 * n0 + 8) + 4 * m + 4)))) ≤ 5 * n0 + m * (4 * n0 + 8) + 4 * m + 12 := by
      rw [List.length_map, hlt]; omega
    refine runs_congr (runs_mono (runs_seq' e1 (runs_seq' e2 (runs_seq' e3 (runs_seq' e4 e5))))
      (fun _ _ => trivial) hc) ?_
    simp only [hACC, List.replicate_succ]

end Passes

end SubNLogN.Machine.FFT.DIF
