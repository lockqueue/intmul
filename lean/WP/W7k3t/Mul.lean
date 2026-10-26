import WP.W7k3t.Rules

/-!
# WP.W7k3t.Mul — natural products: `NMUL` (`z += x·y`), `NSQ` (`z += x·x`), `AFF a b` (`z += a·x + b`)

Sub-kernels on their own hosts (24 stacks), called through `tsub` with host rules `tnmul_ht`,
`tnsq_ht`, `taff_ht`. Every scratch stack gets a `mark` floor first and is restored.

**Proof pattern** (all sub-kernels): a chain of `HT.seq` of host rules; the intermediate states are
the raw `Function.update` chains; operand side conditions by
`simp (disch := decide) only [Function.update_self, Function.update_of_ne, …]`; the final state by
the normalisation `simp (disch := first | decide | with_unfolding_all rfl) only [uswap,
Function.update_idem, uself, Function.update_self, Function.update_of_ne, …]`; the cost by `omega`
with `uc U W` as an atom.
-/

-- The uniform operand-read / normalisation simp sets are used verbatim at every step; single steps
-- may need only part of them.
set_option linter.unusedSimpArgs false

namespace WP.W7k3t

open TMFw TMFw.Contracts WP.W7k2

instance : Big 3 21 := ⟨by decide⟩
instance : Big 2 22 := ⟨by decide⟩

section Push

variable {a b : ℕ} {I : TI} {U : ℕ}

theorem pushNat_ht (hI : I.Ok U) (k : Loc a b) (c : ℕ) (B : Loc a b → List Sym) {W : ℕ}
    (hc : bitLen c ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (pushNat k c) (Function.update B k (natSyms c ++ B k)) (uc U W) :=
  (HT.pushNat k c B ρ).mono (le_trans (by nlinarith [hI.one]) (uc_lin (U := U) hc))

end Push

/-! ## `NMUL`: host `Loc 3 21`, named `0 x, 1 y, 2 z` -/

/-- `z += x·y` for naturals (through the signed multiplier). -/
def nmulProg (I : TI) : Prog (Loc 3 21) (fun _ => Sym) I.R :=
  (pushS (.inr 0) .mark).seq <| (tcp I (.inl 0) (.inr 0)).seq <| (pushS (.inr 0) .pos).seq <|
  (pushS (.inr 1) .mark).seq <| (tcp I (.inl 1) (.inr 1)).seq <| (pushS (.inr 1) .pos).seq <|
  (tmu I (.inr 0) (.inr 1) (.inl 2)).seq <| (popS (.inl 2)).seq <|
  (popS (.inr 1)).seq <| (tdr I (.inr 1)).seq <| (popS (.inr 1)).seq <|
  (popS (.inr 0)).seq <| (tdr I (.inr 0)).seq <| popS (.inr 0)

theorem nmulProg_closed (I : TI) : (nmulProg I).Closed :=
  ⟨trivial, callI_closed _ _ _ _, trivial, trivial, callI_closed _ _ _ _, trivial,
    callI_closed _ _ _ _, trivial, trivial, callI_closed _ _ _ _, trivial, trivial,
    callI_closed _ _ _ _, trivial⟩

theorem nmulProg_spec {I : TI} {U : ℕ} (hI : I.Ok U) (x y : ℕ) (r0 r1 : List Sym)
    (S : Loc 3 21 → List Sym) (h0 : TermOK r0) (h1 : TermOK r1)
    (e0 : S (.inl 0) = natSyms x ++ r0) (e1 : S (.inl 1) = natSyms y ++ r1) {W : ℕ}
    (hx : bitLen x ≤ W) (hy : bitLen y ≤ W) :
    HT [] S (nmulProg I) (Function.update S (.inl 2) (natSyms (x * y) ++ S (.inl 2)))
      (14 * uc U W) := by
  refine (HT.seq (push_ht hI (.inr 0) .mark S (W := W) []) <|
    HT.seq (tcp_ht hI (.inl 0) (.inr 0) (by decide) _ x r0 h0
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne, e0]) hx []) <|
    HT.seq (push_ht hI (.inr 0) .pos _ (W := W) []) <|
    HT.seq (push_ht hI (.inr 1) .mark _ (W := W) []) <|
    HT.seq (tcp_ht hI (.inl 1) (.inr 1) (by decide) _ y r1 h1
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne, e1]) hy []) <|
    HT.seq (push_ht hI (.inr 1) .pos _ (W := W) []) <|
    HT.seq (tmuN_ht hI (.inr 0) (.inr 1) (.inl 2) (by decide) _ x y (Sym.mark :: S (.inr 0))
      (Sym.mark :: S (.inr 1)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hx hy []) <|
    HT.seq (pop_ht hI (.inl 2) _ .pos (natSyms (x * y) ++ S (.inl 2))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W) []) <|
    HT.seq (pop_ht hI (.inr 1) _ .pos (natSyms y ++ Sym.mark :: S (.inr 1))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 1) _ y (Sym.mark :: S (.inr 1)) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hy []) <|
    HT.seq (pop_ht hI (.inr 1) _ .mark (S (.inr 1))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W) []) <|
    HT.seq (pop_ht hI (.inr 0) _ .pos (natSyms x ++ Sym.mark :: S (.inr 0))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 0) _ x (Sym.mark :: S (.inr 0)) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hx []) <|
    pop_ht hI (.inr 0) _ .mark (S (.inr 0))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W)
      []).of_eq ?_ (by omega)
  simp (disch := first | decide | (refine id ?_; with_unfolding_all rfl)) only [uswap,
    Function.update_idem, uself, Function.update_self, Function.update_of_ne]

section Host

variable {a b : ℕ} [NeZero a] [Big a b] {I : TI} {U : ℕ}

/-- `z += x·y` (naturals), on host stacks. -/
def tnmul (I : TI) (x y z : Loc a b) : HP a b I := tsub I (nmulProg I) (nmulProg_closed I) [x, y, z]

omit [Big a b] in
theorem tnmul_closed (I : TI) (x y z : Loc a b) : (tnmul I x y z).Closed := tsub_closed _ _ _ _

theorem tnmul_ht (hI : I.Ok U) (x y z : Loc a b) (hnd : [x, y, z].Nodup) (B : Loc a b → List Sym)
    (u v : ℕ) (ru rv : List Sym) (hru : TermOK ru) (hrv : TermOK rv)
    (hx : B x = natSyms u ++ ru) (hy : B y = natSyms v ++ rv) {W : ℕ} (hu : bitLen u ≤ W)
    (hv : bitLen v ≤ W) (ρ : List (HP a b I)) :
    HT ρ B (tnmul I x y z) (Function.update B z (natSyms (u * v) ++ B z)) (14 * uc U W) :=
  tsub_ht (nmulProg I) (nmulProg_closed I) [x, y, z] hnd rfl (cap_le (by norm_num)) B 2 _
    (nmulProg_spec hI u v ru rv _ hru hrv hx hy hu hv) ρ

end Host

/-! ## `NSQ`: host `Loc 2 22`, named `0 x, 1 z` -/

/-- `z += x·x`. -/
def nsqProg (I : TI) : Prog (Loc 2 22) (fun _ => Sym) I.R :=
  (pushS (.inr 0) .mark).seq <| (tcp I (.inl 0) (.inr 0)).seq <|
  (tnmul I (.inl 0) (.inr 0) (.inl 1)).seq <| (tdr I (.inr 0)).seq <| popS (.inr 0)

theorem nsqProg_closed (I : TI) : (nsqProg I).Closed :=
  ⟨trivial, callI_closed _ _ _ _, tnmul_closed _ _ _ _, callI_closed _ _ _ _, trivial⟩

theorem nsqProg_spec {I : TI} {U : ℕ} (hI : I.Ok U) (x : ℕ) (r0 : List Sym)
    (S : Loc 2 22 → List Sym) (h0 : TermOK r0) (e0 : S (.inl 0) = natSyms x ++ r0) {W : ℕ}
    (hx : bitLen x ≤ W) :
    HT [] S (nsqProg I) (Function.update S (.inl 1) (natSyms (x * x) ++ S (.inl 1)))
      (18 * uc U W) := by
  refine (HT.seq (push_ht hI (.inr 0) .mark S (W := W) []) <|
    HT.seq (tcp_ht hI (.inl 0) (.inr 0) (by decide) _ x r0 h0
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne, e0]) hx []) <|
    HT.seq (tnmul_ht hI (.inl 0) (.inr 0) (.inl 1) (by decide) _ x x r0 (Sym.mark :: S (.inr 0))
      h0 (termOK_mark _) (by simp (disch := decide) only [Function.update_self, Function.update_of_ne, e0])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hx hx []) <|
    HT.seq (tdr_ht hI (.inr 0) _ x (Sym.mark :: S (.inr 0)) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hx []) <|
    pop_ht hI (.inr 0) _ .mark (S (.inr 0))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W)
      []).of_eq ?_ (by omega)
  simp (disch := first | decide | (refine id ?_; with_unfolding_all rfl)) only [uswap,
    Function.update_idem, uself, Function.update_self, Function.update_of_ne]

/-! ## `AFF ca cb`: host `Loc 2 22`, named `0 x, 1 z` -/

/-- `z += ca·x + cb` (compile-time constants `ca`, `cb`). -/
def affProg (I : TI) (ca cb : ℕ) : Prog (Loc 2 22) (fun _ => Sym) I.R :=
  (pushS (.inr 0) .mark).seq <| (pushNat (.inr 0) ca).seq <|
  (pushS (.inr 1) .mark).seq <| (tnmul I (.inr 0) (.inl 0) (.inr 1)).seq <|
  (pushS (.inr 2) .mark).seq <| (pushNat (.inr 2) cb).seq <|
  (tad I (.inr 1) (.inr 2) (.inl 1)).seq <|
  (tdr I (.inr 2)).seq <| (popS (.inr 2)).seq <| (tdr I (.inr 1)).seq <| (popS (.inr 1)).seq <|
  (tdr I (.inr 0)).seq <| popS (.inr 0)

theorem affProg_closed (I : TI) (ca cb : ℕ) : (affProg I ca cb).Closed :=
  ⟨trivial, pushBits_closed _ _, trivial, tnmul_closed _ _ _ _, trivial, pushBits_closed _ _,
    callI_closed _ _ _ _, callI_closed _ _ _ _, trivial, callI_closed _ _ _ _, trivial,
    callI_closed _ _ _ _, trivial⟩

theorem affProg_spec {I : TI} {U : ℕ} (hI : I.Ok U) (ca cb x : ℕ) (r0 : List Sym)
    (S : Loc 2 22 → List Sym) (h0 : TermOK r0) (e0 : S (.inl 0) = natSyms x ++ r0) {W : ℕ}
    (hx : bitLen x ≤ W) (ha : bitLen ca ≤ W) (hw : bitLen (ca * x + cb) ≤ W) :
    HT [] S (affProg I ca cb)
      (Function.update S (.inl 1) (natSyms (ca * x + cb) ++ S (.inl 1))) (30 * uc U W) := by
  have hm : bitLen (ca * x) ≤ W := le_trans (bitLen_mono (Nat.le_add_right _ _)) hw
  have hb : bitLen cb ≤ W := le_trans (bitLen_mono (Nat.le_add_left _ _)) hw
  refine (HT.seq (push_ht hI (.inr 0) .mark S (W := W) []) <|
    HT.seq (pushNat_ht hI (.inr 0) ca _ ha []) <|
    HT.seq (push_ht hI (.inr 1) .mark _ (W := W) []) <|
    HT.seq (tnmul_ht hI (.inr 0) (.inl 0) (.inr 1) (by decide) _ ca x (Sym.mark :: S (.inr 0)) r0
      (termOK_mark _) h0 (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne, e0]) ha hx []) <|
    HT.seq (push_ht hI (.inr 2) .mark _ (W := W) []) <|
    HT.seq (pushNat_ht hI (.inr 2) cb _ hb []) <|
    HT.seq (tad_ht hI (.inr 1) (.inr 2) (.inl 1) (by decide) _ (ca * x) cb (Sym.mark :: S (.inr 1))
      (Sym.mark :: S (.inr 2)) (termOK_mark _) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne])
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hm hb []) <|
    HT.seq (tdr_ht hI (.inr 2) _ cb (Sym.mark :: S (.inr 2)) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hb []) <|
    HT.seq (pop_ht hI (.inr 2) _ .mark (S (.inr 2))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 1) _ (ca * x) (Sym.mark :: S (.inr 1)) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) hm []) <|
    HT.seq (pop_ht hI (.inr 1) _ .mark (S (.inr 1))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W) []) <|
    HT.seq (tdr_ht hI (.inr 0) _ ca (Sym.mark :: S (.inr 0)) (termOK_mark _)
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) ha []) <|
    pop_ht hI (.inr 0) _ .mark (S (.inr 0))
      (by simp (disch := decide) only [Function.update_self, Function.update_of_ne]) (W := W)
      []).of_eq ?_ (by omega)
  simp (disch := first | decide | (refine id ?_; with_unfolding_all rfl)) only [uswap,
    Function.update_idem, uself, Function.update_self, Function.update_of_ne]

section Host2

variable {a b : ℕ} [NeZero a] [Big a b] {I : TI} {U : ℕ}

/-- `z += x·x`, on host stacks. -/
def tnsq (I : TI) (x z : Loc a b) : HP a b I := tsub I (nsqProg I) (nsqProg_closed I) [x, z]

theorem tnsq_ht (hI : I.Ok U) (x z : Loc a b) (hxz : x ≠ z) (B : Loc a b → List Sym) (u : ℕ)
    (ru : List Sym) (hru : TermOK ru) (hx : B x = natSyms u ++ ru) {W : ℕ} (hu : bitLen u ≤ W)
    (ρ : List (HP a b I)) :
    HT ρ B (tnsq I x z) (Function.update B z (natSyms (u * u) ++ B z)) (18 * uc U W) :=
  tsub_ht (nsqProg I) (nsqProg_closed I) [x, z] (by simp [hxz]) rfl (cap_le (by norm_num)) B 1 _
    (nsqProg_spec hI u ru _ hru hx hu) ρ

/-- `z += ca·x + cb`, on host stacks. -/
def taff (I : TI) (ca cb : ℕ) (x z : Loc a b) : HP a b I :=
  tsub I (affProg I ca cb) (affProg_closed I ca cb) [x, z]

theorem taff_ht (hI : I.Ok U) (ca cb : ℕ) (x z : Loc a b) (hxz : x ≠ z) (B : Loc a b → List Sym)
    (u : ℕ) (ru : List Sym) (hru : TermOK ru) (hx : B x = natSyms u ++ ru) {W : ℕ}
    (hu : bitLen u ≤ W) (ha : bitLen ca ≤ W) (hw : bitLen (ca * u + cb) ≤ W)
    (ρ : List (HP a b I)) :
    HT ρ B (taff I ca cb x z) (Function.update B z (natSyms (ca * u + cb) ++ B z))
      (30 * uc U W) :=
  tsub_ht (affProg I ca cb) (affProg_closed I ca cb) [x, z] (by simp [hxz]) rfl
    (cap_le (by norm_num)) B 1 _ (affProg_spec hI ca cb u ru _ hru hx hu ha hw) ρ

end Host2

#assert_std_axioms pushNat_ht nmulProg_closed nmulProg_spec tnmul_closed tnmul_ht nsqProg_closed nsqProg_spec
  affProg_closed affProg_spec tnsq_ht taff_ht

end WP.W7k3t
