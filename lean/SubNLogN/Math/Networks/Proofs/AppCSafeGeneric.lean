import SubNLogN.Math.Networks.AppCSafe

/-!
# Class-local safety, generic part

Proofs of `AlignedSpecStmt`, `AlignedSelfStmt` and `SafeRunLocalStmt` (statements in
`AppCSafe.lean`, namespace `Model`), with no hypotheses.

* Aligned partners: for `x` in `c`, `x_row = res + μ m` with `m = x_row / μ`. If `μ W ∣ r_row`, say
  `r_row = μ W t`, then `m < W t`, so `m / W < t` and the partner row value
  `res + μ (k + W (m / W))` is `< r_row` (`withRow` takes effect). It is `≡ res (mod μ)`, has role `k`
  and position `m / W`; with `k = m % W` it is `x_row` itself.
* Local runs, by induction on the depth: writes are local by the `else` branches of `runIn`, `gateRun`
  and `relabelRun`; reads stay in the class (class-safe pulls and digit-gate fibres; aligned partners of
  a complete split, by `alignedSpec_holds`); children and role primitives are local to `c.sub W hW k`,
  which is contained in `c`; sequential composition (`List.foldl`) preserves locality.
-/

namespace SubNLogN.Math.Networks

open Model

namespace AppCSafeAux

variable {L : Layout}

/-! ### Arithmetic of aligned row values -/

theorem row_decomp (c : RowClass L) (x : L.Addr) (hx : c.mem x) :
    (x c.row).val = c.res + c.μ * ((x c.row).val / c.μ) := by
  have h := Nat.mod_add_div (x c.row).val c.μ
  unfold RowClass.mem at hx
  omega

theorem arith_lt {μ W t res m k : ℕ} (hW : 0 < W) (hres : res < μ) (hk : k < W)
    (hm : res + μ * m < μ * W * t) : res + μ * (k + W * (m / W)) < μ * W * t := by
  have h1 : μ * m < μ * (W * t) := by rw [← mul_assoc]; omega
  have h1' : m < W * t := Nat.lt_of_mul_lt_mul_left h1
  have h2 : m / W < t := (Nat.div_lt_iff_lt_mul hW).2 (by rw [mul_comm]; exact h1')
  have h3 : k + W * (m / W) + 1 ≤ W * t := by
    have h4 : W * (m / W + 1) ≤ W * t := Nat.mul_le_mul_left W h2
    rw [mul_add, mul_one] at h4
    omega
  have h5 : μ * (k + W * (m / W) + 1) ≤ μ * (W * t) := Nat.mul_le_mul_left μ h3
  rw [mul_add, mul_one, ← mul_assoc] at h5
  omega

/-- The aligned row value is in range for a complete split. -/
theorem aligned_val_lt (c : RowClass L) (W : ℕ) (hc : CompleteRoles c W) (x : L.Addr)
    (hx : c.mem x) (k : ℕ) (hk : k < W) :
    c.res + c.μ * (k + W * rolePos c W x) < L.r c.row := by
  obtain ⟨hW, t, ht⟩ := hc
  have hv : (x c.row).val < c.μ * W * t := (x c.row).isLt.trans_eq ht
  have hdec := row_decomp c x hx
  rw [ht]
  show c.res + c.μ * (k + W * ((x c.row).val / c.μ / W)) < c.μ * W * t
  exact arith_lt hW c.hres hk (by rw [← hdec]; exact hv)

theorem aligned_eq (c : RowClass L) (W : ℕ) (x : L.Addr) (k : ℕ)
    (h : c.res + c.μ * (k + W * rolePos c W x) < L.r c.row) :
    aligned c W x k = Function.update x c.row ⟨c.res + c.μ * (k + W * rolePos c W x), h⟩ := by
  simp only [aligned, withRow, dif_pos h]

/-! ### Sub-classes -/

theorem sub_mem (c : RowClass L) (W : ℕ) (hW : 0 < W) (k : Fin W) (x : L.Addr)
    (hx : (c.sub W hW k).mem x) : c.mem x := by
  unfold RowClass.mem at hx ⊢
  simp only [RowClass.sub] at hx
  have h1 : (x c.row).val % (c.μ * W) % c.μ = (x c.row).val % c.μ :=
    Nat.mod_mod_of_dvd _ (Dvd.intro W rfl)
  rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.hres] at h1
  exact h1.symm

end AppCSafeAux

open AppCSafeAux

/-- **Aligned partners** (`AlignedSpecStmt`): for `x` in `c` and a complete split into `W` roles, the
partner of `x` in role `k` is in `c`, has role `k` and the same role position, and differs from `x`
only in the row field. No hypotheses beyond those of the statement. -/
theorem alignedSpec_holds : AlignedSpecStmt := by
  intro L c W x hx hc k
  have hW := hc.1
  have hlt := aligned_val_lt c W hc x hx k k.isLt
  have hres := c.hres
  have hμ := c.hμ
  have hmod : (c.res + c.μ * ((k : ℕ) + W * rolePos c W x)) % c.μ = c.res := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hres]
  have hdiv : (c.res + c.μ * ((k : ℕ) + W * rolePos c W x)) / c.μ = (k : ℕ) + W * rolePos c W x := by
    rw [Nat.add_mul_div_left _ _ hμ, Nat.div_eq_of_lt hres, zero_add]
  have hKmod : ((k : ℕ) + W * rolePos c W x) % W = k := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.isLt]
  have hKdiv : ((k : ℕ) + W * rolePos c W x) / W = rolePos c W x := by
    rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt k.isLt, zero_add]
  rw [aligned_eq c W x k hlt]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((Function.update x c.row ⟨_, hlt⟩) c.row).val % c.μ = c.res
    rw [Function.update_self]
    exact hmod
  · apply Fin.ext
    show ((Function.update x c.row ⟨_, hlt⟩) c.row).val / c.μ % W = k
    rw [Function.update_self]
    show (c.res + c.μ * ((k : ℕ) + W * rolePos c W x)) / c.μ % W = k
    rw [hdiv, hKmod]
  · show ((Function.update x c.row ⟨_, hlt⟩) c.row).val / c.μ / W = rolePos c W x
    rw [Function.update_self]
    show (c.res + c.μ * ((k : ℕ) + W * rolePos c W x)) / c.μ / W = rolePos c W x
    rw [hdiv, hKdiv]
  · intro i hi
    exact Function.update_of_ne hi _ _

/-- **Aligned self** (`AlignedSelfStmt`): the partner of `x` in its own role is `x`. -/
theorem alignedSelf_holds : AlignedSelfStmt := by
  intro L c W x hx hc
  have hlt := aligned_val_lt c W hc x hx (roleIdx c W hc.1 x) (roleIdx c W hc.1 x).isLt
  rw [aligned_eq c W x _ hlt]
  have hval : c.res + c.μ * ((roleIdx c W hc.1 x : ℕ) + W * rolePos c W x) = (x c.row).val := by
    have hdec := row_decomp c x hx
    have hm := Nat.mod_add_div ((x c.row).val / c.μ) W
    show c.res + c.μ * ((x c.row).val / c.μ % W + W * ((x c.row).val / c.μ / W)) = (x c.row).val
    rw [hm]
    exact hdec.symm
  have hfin : (⟨c.res + c.μ * ((roleIdx c W hc.1 x : ℕ) + W * rolePos c W x), hlt⟩ :
      Fin (L.r c.row)) = x c.row := Fin.ext hval
  rw [hfin, Function.update_eq_self]

namespace AppCSafeAux

variable {L : Layout} {β : Type}

/-! ### Locality and composition -/

theorem local_comp {c : RowClass L} {F G : (L.Addr → β) → (L.Addr → β)}
    (hF : ReadsWithin c F ∧ WritesWithin c F) (hG : ReadsWithin c G ∧ WritesWithin c G) :
    ReadsWithin c (fun A => G (F A)) ∧ WritesWithin c (fun A => G (F A)) := by
  refine ⟨fun A B hAB x hx => hG.1 (F A) (F B) (hF.1 A B hAB) x hx, fun A x hx => ?_⟩
  show G (F A) x = A x
  rw [hG.2 (F A) x hx, hF.2 A x hx]

theorem local_id {c : RowClass L} :
    ReadsWithin c (fun A : L.Addr → β => A) ∧ WritesWithin c (fun A : L.Addr → β => A) :=
  ⟨fun _ _ hAB x hx => hAB x hx, fun _ _ _ => rfl⟩

theorem local_foldl {c : RowClass L} {α : Type} (run : α → (L.Addr → β) → (L.Addr → β)) :
    ∀ l : List α, (∀ a ∈ l, ReadsWithin c (run a) ∧ WritesWithin c (run a)) →
      ReadsWithin c (fun A => l.foldl (fun A a => run a A) A) ∧
        WritesWithin c (fun A => l.foldl (fun A a => run a A) A)
  | [], _ => local_id
  | a :: l, h => by
    have h1 := h a List.mem_cons_self
    have h2 := local_foldl run l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    exact local_comp h1 h2

theorem local_of_sub {c c' : RowClass L} (hsub : ∀ x, c'.mem x → c.mem x)
    {F : (L.Addr → β) → (L.Addr → β)} (h : ReadsWithin c' F ∧ WritesWithin c' F) :
    ReadsWithin c F ∧ WritesWithin c F := by
  refine ⟨fun A B hAB x hx => ?_, fun A x hx => h.2 A x (fun hx' => hx (hsub x hx'))⟩
  by_cases hx' : c'.mem x
  · exact h.1 A B (fun y hy => hAB y (hsub y hy)) x hx'
  · rw [h.2 A x hx', h.2 B x hx']
    exact hAB x hx

/-- A class-safe primitive run in `c` reads and writes only `c`. -/
theorem step_local (c : RowClass L) (s : Step L β) (hs : Step.ClassSafe c s) :
    ReadsWithin c (s.runIn c) ∧ WritesWithin c (s.runIn c) := by
  refine ⟨fun A B hAB x hx => ?_, fun A x hx => ?_⟩
  · simp only [Step.runIn, if_pos hx]
    cases s with
    | elem e => exact hAB _ ((hs x).2 hx)
    | recMap f => simp only [Step.run, Function.comp_apply, hAB x hx]
    | addrMap f => simp only [Step.run, hAB x hx]
    | sparsePerm pull supp => exact hAB _ ((hs x).2 hx)
    | swapBlocks t₀ s₀ len => exact hAB _ ((hs x).2 hx)
    | digitGate i G =>
      simp only [Step.run]
      congr 1
      funext v
      exact hAB _ (hs x v hx)
  · simp only [Step.runIn, if_neg hx]

/-- Depth-indexed induction: a class-safe procedure run in `c` reads and writes only `c`. -/
theorem safeRunLocal_aux (β : Type) : ∀ (d : ℕ) (p : ProcK L β d) (c : RowClass L),
    ProcK.ClassSafe d p c → ReadsWithin c (ProcK.run d p c) ∧ WritesWithin c (ProcK.run d p c)
  | 0, p, c, hp =>
    local_foldl (fun s A => Step.runIn c s A) p
      (fun s hs => step_local c s (List.forall_iff_forall_mem.1 hp s hs))
  | d + 1, p, c, hp => by
    refine local_foldl (fun o A => Model.Op.run (ProcK.run d) c o A) p (fun o ho => ?_)
    have hso : Model.Op.ClassSafe (ProcK.ClassSafe d) c o := List.forall_iff_forall_mem.1 hp o ho
    cases o with
    | prim s => exact step_local c s hso
    | node W hW ops =>
      obtain ⟨hcomp, hops⟩ := hso
      refine local_foldl (fun r A => RoleOp.run (ProcK.run d) c hW r A) ops (fun r hr => ?_)
      have hsr := hops r hr
      cases r with
      | prim k s =>
        exact local_of_sub (fun x hx => sub_mem c W hW k x hx) (step_local _ s hsr)
      | gate G t =>
        refine ⟨fun A B hAB x hx => ?_, fun A x hx => ?_⟩
        · simp only [RoleOp.run, gateRun, if_pos hx]
          congr 1
          funext k'
          exact hAB _ (alignedSpec_holds L c W x hx hcomp k').1
        · simp only [RoleOp.run, gateRun, if_neg hx]
      | call k ch =>
        exact local_of_sub (fun x hx => sub_mem c W hW k x hx) (safeRunLocal_aux β d ch _ hsr)
      | relabel π =>
        refine ⟨fun A B hAB x hx => ?_, fun A x hx => ?_⟩
        · simp only [RoleOp.run, relabelRun, if_pos hx]
          exact hAB _ (alignedSpec_holds L c W x hx hcomp _).1
        · simp only [RoleOp.run, relabelRun, if_neg hx]

end AppCSafeAux

/-- **Local runs** (`SafeRunLocalStmt`): a class-safe procedure (any depth) run in class `c` reads
only `c` and writes only `c`. No hypotheses beyond those of the statement. -/
theorem safeRunLocal_holds : SafeRunLocalStmt := by
  intro L β d p c hp
  exact AppCSafeAux.safeRunLocal_aux β d p c hp

end SubNLogN.Math.Networks
