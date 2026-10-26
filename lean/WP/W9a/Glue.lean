import WP.W9a.Basic

/-!
# WP.W9a.Glue — embedding contracts and the glue macros of the level programs

* `embL h : BLoc mc → BLoc mL` embeds a contract program with `mc ≤ mL` scratch stacks
  (`runs_embed`: a contract's `Runs` becomes an exact evaluation in the bigger state, every scratch
  stack beyond `mc` unchanged). `stk_of_parts` rebuilds a whole state from `S`, `W0`, the scratch
  stacks and `outer`.
* Header macros: `copyFields n src a b` copies `n` header fields (`natSyms f ++ [mark]`) onto `a` and
  `b`; `moveFields`; `copyFieldAt k src dst tmp delim` copies field `k` of a header on `src` onto
  `dst`; `readHdr n` moves a segment tag and its header from `TR` to `TL` and copies the header onto
  `C0` (above `symGuard`).
* `chunkLoop_eval`: a counted loop that moves `x`-terminated chunks (filter rows, leaf stages).
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Embedding contract programs -/

/-- Stack embedding of a contract with `mc` scratch stacks into `mL ≥ mc`. -/
def embL {mc mL : ℕ} (h : mc ≤ mL) : BLoc mc → BLoc mL
  | .inl k => .inl k
  | .inr j => .inr (Fin.castLE h j)

theorem embL_injective {mc mL : ℕ} (h : mc ≤ mL) : Function.Injective (embL h)
  | .inl a, .inl b, hab => by
    simp only [embL, Sum.inl.injEq] at hab
    rw [hab]
  | .inr a, .inr b, hab => by
    simp only [embL, Sum.inr.injEq] at hab
    exact congrArg Sum.inr (Fin.ext (by simpa using congrArg Fin.val hab))
  | .inl a, .inr b, hab => by simp [embL] at hab
  | .inr a, .inl b, hab => by simp [embL] at hab

/-- A contract's `Runs` on the embedded view of a big state gives an exact evaluation of the
embedded program, provided the target agrees with the source beyond the contract's scratch. -/
theorem runs_embed {mc mL : ℕ} (h : mc ≤ mL) {R : Type} {P : Prog (BLoc mc) (fun _ => Sym) R}
    {T : ℕ} (B B' : BLoc mL → List Sym)
    (hP : Runs P (B ∘ embL h) (B' ∘ embL h) (fun _ => True) T)
    (hout : ∀ j : Fin mL, mc ≤ j.val → B' (.inr j) = B (.inr j)) (v : R) :
    ∃ v' t, Eval [] (P.mapStk (embL h)) ⟨v, B⟩ ⟨v', B'⟩ t ∧ t ≤ T := by
  obtain ⟨s', t, e, ⟨h1, h2, -⟩, ht⟩ :=
    Runs.embed (embL_injective h) hP B (fun _ => rfl) ⟨v, B⟩ rfl
  have hs : s'.stk = B' := by
    funext k
    rcases k with k | j
    · exact h1 (.inl k)
    · by_cases hj : j.val < mc
      · have := h1 (.inr ⟨j.val, hj⟩)
        simpa [embL] using this
      · rw [h2 (.inr j) (fun l => ?_), hout j (by omega)]
        rcases l with l | l
        · simp [embL]
        · simp only [embL, ne_eq, Sum.inr.injEq]
          intro e
          apply hj
          rw [← e]
          simp
  refine ⟨s'.var, t, e.of_eq ?_ rfl, ht⟩
  cases s'
  simp only at hs
  rw [hs]

/-- A state is determined by `S`, `W0`, the scratch stacks and `outer`. -/
theorem stk_of_parts {m : ℕ} {s τ : BLoc m → List Sym} (hS : s (.inl .S) = τ (.inl .S))
    (hW : s (.inl .W0) = τ (.inl .W0)) (hr : ∀ j, s (.inr j) = τ (.inr j))
    (ho : outer s = outer τ) : s = τ := by
  funext k
  rcases k with k | j
  · by_cases h1 : k = .S
    · subst h1
      exact hS
    · by_cases h2 : k = .W0
      · subst h2
        exact hW
      · have := congrFun ho k
        simp only [outer, h1, h2, or_self, if_false] at this
        exact this
  · exact hr j

theorem closed_embL {mc mL : ℕ} (h : mc ≤ mL) {R : Type} {P : Prog (BLoc mc) (fun _ => Sym) R}
    (hP : P.Closed) : (P.mapStk (embL h)).Closed :=
  closed_mapStk _ hP

/-! ## Header fields -/

theorem hdrSyms_nil : hdrSyms [] = [] := rfl

theorem hdrSyms_cons (f : ℕ) (fs : List ℕ) :
    hdrSyms (f :: fs) = natSyms f ++ Sym.mark :: hdrSyms fs := by
  simp [hdrSyms]

theorem hdrSyms_append (a b : List ℕ) : hdrSyms (a ++ b) = hdrSyms a ++ hdrSyms b := by
  simp [hdrSyms, List.flatMap_append]

theorem length_hdrSyms_cons (f : ℕ) (fs : List ℕ) :
    (hdrSyms (f :: fs)).length = bitLen f + 1 + (hdrSyms fs).length := by
  rw [hdrSyms_cons, List.length_append, List.length_cons, length_natSyms]
  omega

theorem hdrSyms_sym (fs : List ℕ) : ∀ x ∈ hdrSyms fs, x = Sym.mark ∨ ∃ b, x = Sym.bit b := by
  intro x hx
  simp only [hdrSyms, List.mem_flatMap, List.mem_append, natSyms, List.mem_map,
    List.mem_singleton] at hx
  obtain ⟨f, -, (⟨b, -, rfl⟩ | rfl)⟩ := hx
  · exact Or.inr ⟨b, rfl⟩
  · exact Or.inl rfl

theorem tag_not_mem_hdrSyms (t : Fin 16) (fs : List ℕ) : Sym.tag t ∉ hdrSyms fs := by
  intro h
  rcases hdrSyms_sym fs _ h with h | ⟨b, h⟩ <;> cases h

theorem bitLen_le_length_hdrSyms (f : ℕ) (fs : List ℕ) (hf : f ∈ fs) :
    bitLen f ≤ (hdrSyms fs).length := by
  induction fs with
  | nil => simp at hf
  | cons g fs ih =>
    rw [length_hdrSyms_cons]
    rcases List.mem_cons.1 hf with rfl | hf
    · omega
    · have := ih hf
      omega

theorem natSyms_zero : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]

theorem encodeNat_one : encodeNat 1 = [true] := by
  have h := encodeNat_add_add_one 0
  rw [encodeNat_zero] at h
  exact h

theorem natSyms_one : natSyms 1 = [Sym.bit true] := by
  simp [natSyms, encodeNat_one]

theorem bitLen_one : bitLen 1 = 1 := by
  rw [← length_natSyms, natSyms_one]
  rfl

theorem bitLen_two_pow : ∀ k : ℕ, bitLen (2 ^ k) = k + 1
  | 0 => bitLen_one
  | k + 1 => by
    have hne : encodeNat (2 ^ k) ≠ [] := by
      rw [Ne, encodeNat_eq_nil_iff]
      exact Nat.ne_of_gt (Nat.two_pow_pos k)
    unfold bitLen
    rw [pow_succ, Nat.mul_two, encodeNat_add, if_neg hne, List.length_cons]
    have := bitLen_two_pow k
    unfold bitLen at this
    rw [this]

/-! ## Macros -/

section Macros

variable {K : Type}

/-- Copy one header field (`natSyms f ++ [mark]`) from `src` onto both `a` and `b` (reversed). -/
def copyField (src a b : K) : SProg K := .seq (moveBitsDup src a b) (.seq (pushR a) (pushR b))

/-- Copy `n` header fields. -/
def copyFields (src a b : K) : ℕ → SProg K
  | 0 => skip
  | n + 1 => .seq (copyField src a b) (copyFields src a b n)

/-- Move one header field from `src` onto `dst` (reversed). -/
def moveField (src dst : K) : SProg K := .seq (moveBits src dst) (pushR dst)

/-- Move `n` header fields. -/
def moveFields (src dst : K) : ℕ → SProg K
  | 0 => skip
  | n + 1 => .seq (moveField src dst) (moveFields src dst n)

/-- Copy field `k` of the header on `src` onto `dst` (`tmp` parks the first `k` fields above
`delim`). -/
def copyFieldAt (k : ℕ) (src dst tmp : K) (delim : Sym) : SProg K :=
  .seq (pushC tmp delim) (.seq (moveFields src tmp k) (.seq (copyBlock src dst tmp)
    (moveUntil tmp src (isSym delim))))

/-- Move a segment tag and its `n`-field header from `TR` to `TL`, and copy the header onto `C0`
above a `symGuard` (`tA` is a temporary, `$`-delimited). -/
def readHdr (n : ℕ) (TR TL C0 tA : K) : SProg K :=
  .seq (pushC C0 symGuard) (.seq (moveSym TR TL) (.seq (pushC tA symLevel)
    (.seq (copyFields TR tA TL n) (moveUntil tA C0 (isSym symLevel)))))

theorem closed_copyFields (src a b : K) : ∀ n, (copyFields src a b n).Closed
  | 0 => trivial
  | n + 1 => ⟨⟨closed_moveBitsDup _ _ _, ⟨trivial, trivial⟩⟩, closed_copyFields src a b n⟩

theorem closed_moveFields (src dst : K) : ∀ n, (moveFields src dst n).Closed
  | 0 => trivial
  | n + 1 => ⟨⟨closed_moveBits _ _, trivial⟩, closed_moveFields src dst n⟩

theorem closed_copyFieldAt (k : ℕ) (src dst tmp : K) (delim : Sym) :
    (copyFieldAt k src dst tmp delim).Closed :=
  ⟨trivial, ⟨closed_moveFields _ _ _, ⟨closed_copyBlock _ _ _, closed_moveUntil _ _ _⟩⟩⟩

theorem closed_readHdr (n : ℕ) (TR TL C0 tA : K) : (readHdr n TR TL C0 tA).Closed :=
  ⟨trivial, ⟨closed_moveSym _ _, ⟨trivial, ⟨closed_copyFields _ _ _ _,
    closed_moveUntil _ _ _⟩⟩⟩⟩

variable [DecidableEq K]

theorem moveBitsDup_eval {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (v : Option Sym) (es : List Bool) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S src = es.map Sym.bit ++ rest) :
    Eval [] (moveBitsDup src a b) ⟨v, S⟩
      ⟨rest.head?, Function.update (Function.update (Function.update S src rest.tail) a
        (es.reverse.map Sym.bit ++ S a)) b (es.reverse.map Sym.bit ++ S b)⟩
      (4 * es.length + 2) := by
  have := Ne.symm hsa
  have := Ne.symm hsb
  have := Ne.symm hab
  have h1 : Eval [] (popR src) ⟨v, S⟩
      ⟨(es.map Sym.bit ++ rest).head?, Function.update S src (es.map Sym.bit ++ rest).tail⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := moveBitsDup_loop_eval hsa hsb hab [] es rest
    (Function.update S src (es.map Sym.bit ++ rest).tail) hrest (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem copyFields_eval {src a b : K} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b) :
    ∀ (fs : List ℕ) (rest : List Sym) (S : K → List Sym) (v : Option Sym),
      S src = hdrSyms fs ++ rest →
      ∃ v', Eval [] (copyFields src a b fs.length) ⟨v, S⟩
        ⟨v', Function.update (Function.update (Function.update S src rest) a
          ((hdrSyms fs).reverse ++ S a)) b ((hdrSyms fs).reverse ++ S b)⟩
        (4 * (hdrSyms fs).length + 1)
  | [], rest, S, v, hS => by
    refine ⟨v, (skip_eval [] _).of_eq ?_ rfl⟩
    simp only [hdrSyms_nil, List.nil_append] at hS
    congr 1
    funext k
    simp only [Function.update_apply, hdrSyms_nil, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | f :: fs, rest, S, v, hS => by
    have := Ne.symm hsa
    have := Ne.symm hsb
    have := Ne.symm hab
    rw [hdrSyms_cons, List.append_assoc, List.cons_append] at hS
    have e1 := moveBitsDup_eval hsa hsb hab v (encodeNat f) (Sym.mark :: (hdrSyms fs ++ rest)) S
      (TermOK.cons rfl _) hS
    have e2 : Eval [] (pushR a) ⟨some Sym.mark, Function.update (Function.update
          (Function.update S src (hdrSyms fs ++ rest)) a ((encodeNat f).reverse.map Sym.bit ++ S a))
          b ((encodeNat f).reverse.map Sym.bit ++ S b)⟩
        ⟨some Sym.mark, Function.update (Function.update (Function.update
          (Function.update S src (hdrSyms fs ++ rest)) a ((encodeNat f).reverse.map Sym.bit ++ S a))
          b ((encodeNat f).reverse.map Sym.bit ++ S b)) a
          (Sym.mark :: ((encodeNat f).reverse.map Sym.bit ++ S a))⟩ 1 := by
      refine (Eval.push _ _ _ _ _).of_eq ?_ rfl
      rw [Function.update_of_ne hab, Function.update_self]
      rfl
    have e3 : Eval [] (pushR b) ⟨some Sym.mark, Function.update (Function.update (Function.update
          (Function.update S src (hdrSyms fs ++ rest)) a ((encodeNat f).reverse.map Sym.bit ++ S a))
          b ((encodeNat f).reverse.map Sym.bit ++ S b)) a
          (Sym.mark :: ((encodeNat f).reverse.map Sym.bit ++ S a))⟩
        ⟨some Sym.mark, Function.update (Function.update (Function.update (Function.update
          (Function.update S src (hdrSyms fs ++ rest)) a ((encodeNat f).reverse.map Sym.bit ++ S a))
          b ((encodeNat f).reverse.map Sym.bit ++ S b)) a
          (Sym.mark :: ((encodeNat f).reverse.map Sym.bit ++ S a))) b
          (Sym.mark :: ((encodeNat f).reverse.map Sym.bit ++ S b))⟩ 1 := by
      refine (Eval.push _ _ _ _ _).of_eq ?_ rfl
      rw [Function.update_of_ne (Ne.symm hab), Function.update_self]
      rfl
    obtain ⟨v', e4⟩ := copyFields_eval hsa hsb hab fs rest _ (some Sym.mark)
      (show Function.update (Function.update (Function.update (Function.update
          (Function.update S src (hdrSyms fs ++ rest)) a ((encodeNat f).reverse.map Sym.bit ++ S a))
          b ((encodeNat f).reverse.map Sym.bit ++ S b)) a
          (Sym.mark :: ((encodeNat f).reverse.map Sym.bit ++ S a))) b
          (Sym.mark :: ((encodeNat f).reverse.map Sym.bit ++ S b)) src = hdrSyms fs ++ rest by
        rw [Function.update_of_ne hsb, Function.update_of_ne hsa, Function.update_of_ne hsb,
          Function.update_of_ne hsa, Function.update_self])
    refine ⟨v', (Eval.seq (Eval.seq e1 (Eval.seq e2 e3)) e4).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [Function.update_apply, hdrSyms_cons, natSyms, List.reverse_append,
        List.reverse_cons, List.map_reverse, List.append_assoc, List.cons_append,
        List.nil_append]
      split_ifs <;> simp_all
    · rw [length_hdrSyms_cons, bitLen]
      omega

theorem moveFields_eval {src dst : K} (hsd : src ≠ dst) :
    ∀ (fs : List ℕ) (rest : List Sym) (S : K → List Sym) (v : Option Sym),
      S src = hdrSyms fs ++ rest →
      ∃ v', Eval [] (moveFields src dst fs.length) ⟨v, S⟩
        ⟨v', Function.update (Function.update S src rest) dst ((hdrSyms fs).reverse ++ S dst)⟩
        (3 * (hdrSyms fs).length + 1)
  | [], rest, S, v, hS => by
    refine ⟨v, (skip_eval [] _).of_eq ?_ rfl⟩
    simp only [hdrSyms_nil, List.nil_append] at hS
    congr 1
    funext k
    simp only [Function.update_apply, hdrSyms_nil, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | f :: fs, rest, S, v, hS => by
    have := Ne.symm hsd
    rw [hdrSyms_cons, List.append_assoc, List.cons_append] at hS
    have e1 := moveBits_eval hsd [] v (encodeNat f) (Sym.mark :: (hdrSyms fs ++ rest)) S
      (TermOK.cons rfl _) hS
    have e2 : Eval [] (pushR dst) ⟨some Sym.mark, Function.update (Function.update S src
          (hdrSyms fs ++ rest)) dst ((encodeNat f).reverse.map Sym.bit ++ S dst)⟩
        ⟨some Sym.mark, Function.update (Function.update (Function.update S src
          (hdrSyms fs ++ rest)) dst ((encodeNat f).reverse.map Sym.bit ++ S dst)) dst
          (Sym.mark :: ((encodeNat f).reverse.map Sym.bit ++ S dst))⟩ 1 := by
      refine (Eval.push _ _ _ _ _).of_eq ?_ rfl
      rw [Function.update_self]
      rfl
    obtain ⟨v', e3⟩ := moveFields_eval hsd fs rest _ (some Sym.mark)
      (show Function.update (Function.update (Function.update S src
          (hdrSyms fs ++ rest)) dst ((encodeNat f).reverse.map Sym.bit ++ S dst)) dst
          (Sym.mark :: ((encodeNat f).reverse.map Sym.bit ++ S dst)) src = hdrSyms fs ++ rest by
        rw [Function.update_of_ne hsd, Function.update_of_ne hsd, Function.update_self])
    refine ⟨v', (Eval.seq (Eval.seq e1 e2) e3).of_eq ?_ ?_⟩
    · congr 1
      funext k
      simp only [Function.update_apply, hdrSyms_cons, natSyms, List.reverse_append,
        List.reverse_cons, List.map_reverse, List.append_assoc, List.cons_append,
        List.nil_append]
      split_ifs <;> simp_all
    · rw [length_hdrSyms_cons, bitLen]
      omega

/-- **copyFieldAt**, exact: field `pre.length` of the header on `src` is copied onto `dst`. -/
theorem copyFieldAt_eval {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (t : Fin 16) (pre : List ℕ) (f : ℕ) (rest : List Sym) (S : K → List Sym) (v : Option Sym)
    (hS : S src = hdrSyms pre ++ natSyms f ++ Sym.mark :: rest) :
    Eval [] (copyFieldAt pre.length src dst tmp (.tag t)) ⟨v, S⟩
      ⟨some (.tag t), Function.update S dst (natSyms f ++ S dst)⟩
      (6 * (hdrSyms pre).length + 7 * bitLen f + 11) := by
  have := Ne.symm hsd
  have := Ne.symm hst
  have := Ne.symm hdt
  have e1 : Eval [] (pushC tmp (.tag t)) ⟨v, S⟩
      ⟨v, Function.update S tmp (.tag t :: S tmp)⟩ 1 := Eval.push _ _ _ _ _
  obtain ⟨v2, e2⟩ := moveFields_eval hst pre (natSyms f ++ Sym.mark :: rest)
    (Function.update S tmp (.tag t :: S tmp)) v
    (by rw [Function.update_of_ne hst, hS, List.append_assoc])
  have e3 := copyBlock_eval hsd hst hdt [] v2 (encodeNat f) (Sym.mark :: rest)
    (Function.update (Function.update (Function.update S tmp (.tag t :: S tmp)) src
      (natSyms f ++ Sym.mark :: rest)) tmp ((hdrSyms pre).reverse ++
        Function.update S tmp (.tag t :: S tmp) tmp)) (TermOK.cons rfl _)
    (by rw [Function.update_of_ne hst, Function.update_self]; rfl)
  have hd : ∀ x ∈ (hdrSyms pre).reverse, isSym (.tag t) (some x) = false := by
    intro x hx
    refine isSym_some_of_ne (fun e => tag_not_mem_hdrSyms t pre ?_)
    rw [← e]
    exact List.mem_reverse.1 hx
  have e4 := moveUntil_eval (Ne.symm hst) (isSym (.tag t)) (some Sym.mark) (hdrSyms pre).reverse
    (.tag t :: S tmp) _ hd (isSym_some_self _)
    (show Function.update (Function.update (Function.update (Function.update S tmp
        (.tag t :: S tmp)) src (natSyms f ++ Sym.mark :: rest)) tmp ((hdrSyms pre).reverse ++
          Function.update S tmp (.tag t :: S tmp) tmp)) dst ((encodeNat f).map Sym.bit ++
        Function.update (Function.update (Function.update S tmp (.tag t :: S tmp)) src
          (natSyms f ++ Sym.mark :: rest)) tmp ((hdrSyms pre).reverse ++
            Function.update S tmp (.tag t :: S tmp) tmp) dst) tmp =
          (hdrSyms pre).reverse ++ .tag t :: S tmp by
      rw [Function.update_of_ne (Ne.symm hdt), Function.update_self, Function.update_self])
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ ?_
  · congr 1
    funext k
    simp only [Function.update_apply, List.reverse_reverse, List.tail_cons, natSyms]
    split_ifs <;> simp_all [natSyms, List.append_assoc]
  · rw [List.length_reverse, bitLen]
    omega

/-- **readHdr**, exact. -/
theorem readHdr_eval {TR TL C0 tA : K} (h1 : TR ≠ TL) (h2 : TR ≠ C0) (h3 : TR ≠ tA)
    (h4 : TL ≠ C0) (h5 : TL ≠ tA) (h6 : C0 ≠ tA) (tag : Sym) (fs : List ℕ) (rest : List Sym)
    (S : K → List Sym) (v : Option Sym) (hS : S TR = tag :: (hdrSyms fs ++ rest)) :
    Eval [] (readHdr fs.length TR TL C0 tA) ⟨v, S⟩
      ⟨some symLevel, Function.update (Function.update (Function.update S TR rest) TL
        ((hdrSyms fs).reverse ++ tag :: S TL)) C0 (hdrSyms fs ++ symGuard :: S C0)⟩
      (7 * (hdrSyms fs).length + 7) := by
  have := Ne.symm h1
  have := Ne.symm h2
  have := Ne.symm h3
  have := Ne.symm h4
  have := Ne.symm h5
  have := Ne.symm h6
  have e1 : Eval [] (pushC C0 symGuard) ⟨v, S⟩
      ⟨v, Function.update S C0 (symGuard :: S C0)⟩ 1 := Eval.push _ _ _ _ _
  have e2 := moveSym_eval h1 v tag (hdrSyms fs ++ rest) (Function.update S C0 (symGuard :: S C0))
    (by rw [Function.update_of_ne h2, hS])
  have e3 : Eval [] (pushC tA symLevel) ⟨some tag, Function.update (Function.update
        (Function.update S C0 (symGuard :: S C0)) TR (hdrSyms fs ++ rest)) TL
        (tag :: Function.update S C0 (symGuard :: S C0) TL)⟩
      ⟨some tag, Function.update (Function.update (Function.update
        (Function.update S C0 (symGuard :: S C0)) TR (hdrSyms fs ++ rest)) TL
        (tag :: Function.update S C0 (symGuard :: S C0) TL)) tA (symLevel :: S tA)⟩ 1 := by
    refine (Eval.push _ _ _ _ _).of_eq ?_ rfl
    rw [Function.update_of_ne (Ne.symm h5), Function.update_of_ne (Ne.symm h3),
      Function.update_of_ne (Ne.symm h6)]
  generalize hS3 : Function.update (Function.update (Function.update
        (Function.update S C0 (symGuard :: S C0)) TR (hdrSyms fs ++ rest)) TL
        (tag :: Function.update S C0 (symGuard :: S C0) TL)) tA (symLevel :: S tA) = S3 at e3
  have hS3TR : S3 TR = hdrSyms fs ++ rest := by
    rw [← hS3, Function.update_of_ne h3, Function.update_of_ne h1, Function.update_self]
  have hS3tA : S3 tA = symLevel :: S tA := by rw [← hS3, Function.update_self]
  obtain ⟨v4, e4⟩ := copyFields_eval h3 h1 (Ne.symm h5) fs rest S3 (some tag) hS3TR
  have hd : ∀ x ∈ (hdrSyms fs).reverse, isSym symLevel (some x) = false := by
    intro x hx
    refine isSym_some_of_ne (fun e => tag_not_mem_hdrSyms 1 fs ?_)
    have hx' := List.mem_reverse.1 hx
    rw [e] at hx'
    exact hx'
  have e5 := moveUntil_eval h6.symm (isSym symLevel) v4 (hdrSyms fs).reverse (symLevel :: S tA)
    (Function.update (Function.update (Function.update S3 TR rest) tA
      ((hdrSyms fs).reverse ++ S3 tA)) TL ((hdrSyms fs).reverse ++ S3 TL)) hd (isSym_some_self _)
    (by rw [Function.update_of_ne (Ne.symm h5), Function.update_self, hS3tA])
  refine (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))).of_eq ?_ ?_
  · congr 1
    funext k
    subst hS3
    simp only [Function.update_apply, List.reverse_reverse, List.tail_cons]
    split_ifs <;> simp_all
  · rw [List.length_reverse]
    omega

/-- **Chunk loop**: a counter `|cs|` on `Kc` drives `|cs|` moves of `x`-terminated chunks from `src`
to `dst`. -/
theorem chunkLoop_eval {Kc t src dst : K} (hKt : Kc ≠ t) (hsd : src ≠ dst) (hKs : Kc ≠ src)
    (hKd : Kc ≠ dst) (x : Sym) (cs : List (List Sym)) (hcs : ∀ c ∈ cs, x ∉ c) (rest rK : List Sym)
    (hrK : TermOK rK) (S : K → List Sym) (v : Option Sym)
    (hS : S src = cs.flatMap (· ++ [x]) ++ rest) (hK : S Kc = natSyms cs.length ++ rK) :
    ∃ v', Eval [] (countLoop Kc t (moveChunk src dst x)) ⟨v, S⟩
      ⟨v', Function.update (Function.update (Function.update S src rest) dst
        ((cs.flatMap (· ++ [x])).reverse ++ S dst)) Kc rK⟩
      (incSeqCost 6 10 cs.length + 3 * (cs.flatMap (· ++ [x])).length + 2) := by
  have := Ne.symm hKt
  have := Ne.symm hsd
  have := Ne.symm hKs
  have := Ne.symm hKd
  let F : List (List Sym) → List (List Sym) → K → List Sym := fun done ys =>
    Function.update (Function.update (Function.update S src (ys.flatMap (· ++ [x]) ++ rest)) dst
      ((done.flatMap (· ++ [x])).reverse ++ S dst)) Kc (natSyms ys.length ++ rK)
  let P : List (List Sym) → (K → List Sym) → Prop := fun ys S' =>
    (∃ done, done ++ ys = cs ∧ S' = F done ys) ∧ ∀ c ∈ ys, x ∉ c
  have hP0 : P cs S := by
    refine ⟨⟨[], rfl, ?_⟩, hcs⟩
    funext k
    simp only [F, Function.update_apply, List.flatMap_nil, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  have hKP : ∀ ys S', P ys S' → S' Kc = natSyms ys.length ++ rK := by
    rintro ys S' ⟨⟨done, -, rfl⟩, -⟩
    simp [F]
  have hbody : ∀ y ys S' v, P (y :: ys) S' → ∃ v' S'', Eval [] (moveChunk src dst x)
      ⟨v, Function.update S' Kc (natSyms ys.length ++ rK)⟩ ⟨v', S''⟩ (3 * y.length + 3) ∧
      P ys S'' := by
    rintro y ys S' v ⟨⟨done, hdone, rfl⟩, hys⟩
    have hy : x ∉ y := hys y (List.mem_cons_self ..)
    refine ⟨_, _, moveChunk_eval hsd x v y (ys.flatMap (· ++ [x]) ++ rest) _ hy ?_,
      ⟨⟨done ++ [y], by rw [List.append_assoc]; exact hdone, ?_⟩,
        fun c hc => hys c (List.mem_cons_of_mem _ hc)⟩⟩
    · simp only [F, Function.update_apply]
      simp [Ne.symm hKs, hsd, List.flatMap_cons, List.append_assoc]
    · funext k
      simp only [F, Function.update_apply, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.reverse_append]
      split_ifs <;> simp_all
  obtain ⟨v', S', e, ⟨⟨done, hdone, rfl⟩, -⟩⟩ := countLoop_eval hKt _ P rK hrK
    (fun y => 3 * y.length + 3) hKP hbody cs S v hP0
  rw [List.append_nil] at hdone
  subst hdone
  refine ⟨v', e.of_eq ?_ ?_⟩
  · simp only [F, List.flatMap_nil, List.nil_append, List.length_nil, natSyms_zero]
  · have : ∀ l : List (List Sym), (l.map (fun y => 3 * y.length + 3)).sum =
        3 * (l.flatMap (· ++ [x])).length := by
      intro l
      induction l with
      | nil => rfl
      | cons y l ih =>
        rw [List.map_cons, List.sum_cons, ih, List.flatMap_cons, List.length_append,
          List.length_append, List.length_singleton]
        omega
    rw [this]

end Macros

#assert_std_axioms embL_injective runs_embed stk_of_parts hdrSyms_cons hdrSyms_append
  length_hdrSyms_cons hdrSyms_sym tag_not_mem_hdrSyms bitLen_le_length_hdrSyms natSyms_one
  bitLen_two_pow moveBitsDup_eval copyFields_eval moveFields_eval copyFieldAt_eval readHdr_eval
  chunkLoop_eval

end WP.W9a
