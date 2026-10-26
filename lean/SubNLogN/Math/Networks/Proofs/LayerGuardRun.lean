import SubNLogN.Math.Networks.LayerCore
import SubNLogN.Math.Networks.AppCLayerProc

/-!
# Generic guard accounting over `ProcK.run` (helper for `Prop71GuardStmt`)

A *pointwise guard* is a family `pt : ℕ → β → Prop` of record predicates indexed by a charge `J`
and monotone in `J`; an array is guarded at charge `J` (`InvA pt J A`) if every record is. Each
step, gate and child of a procedure is given a charge (`cs`, `cg`, and recursively `chargeK` for
children); the charges of a procedure add up sequentially (`chargeK`). `run_charge`: if every step
and gate of a procedure `p` raises the guard charge by at most its own charge (`ChargeOK`), then
from an input guarded at charge `J` the output is guarded at charge `J + chargeK p`, and every
intermediate array of the run (inside nodes and children, `ProcK.AllStates`) is guarded at every
charge `J' ≥ J + chargeK p`.

Proof: one generic accumulation lemma over lists of operations (`list_accum`, by induction on the
list), instantiated at the three levels (steps of a depth-`0` procedure, operations of a depth-`d+1`
procedure, role operations of a node), by induction on the depth. Steps run in a row class
(`Step.runIn`), gates (`gateRun`) and relabellings (`relabelRun`) mix the new values with the old
ones; pointwise guards and monotonicity in `J` make this harmless.
-/

namespace SubNLogN.Math.Networks.LayerGuardRun

open SubNLogN.Math.Networks.Model

variable {L : Layout} {β : Type}

/-- `A` is pointwise guarded at charge `J`. -/
def InvA (pt : ℕ → β → Prop) (J : ℕ) (A : L.Addr → β) : Prop := ∀ x, pt J (A x)

/-- A step raises the guard charge by at most `g`. -/
def StepOK (pt : ℕ → β → Prop) (s : Step L β) (g : ℕ) : Prop :=
  ∀ (J : ℕ) (A : L.Addr → β), InvA pt J A → InvA pt (J + g) (s.run A)

/-- A gate on `W` aligned records raises the guard charge by at most `g`. -/
def GateOK (pt : ℕ → β → Prop) {W : ℕ} (G : (Fin W → β) → (Fin W → β)) (g : ℕ) : Prop :=
  ∀ (J : ℕ) (v : Fin W → β), (∀ k, pt J (v k)) → ∀ k, pt (J + g) (G v k)

/-- Charge of a role operation (step charges `cs`, gate charge `cg`, child charges `cc`). -/
def RoleOp.chg {W : ℕ} {Child : Type} (cs : Step L β → ℕ) (cg : ℕ) (cc : Child → ℕ) :
    RoleOp L β W Child → ℕ
  | .prim _ s => cs s
  | .gate _ _ => cg
  | .call _ ch => cc ch
  | .relabel _ => 0

/-- Charge of an operation: a node charges the sum of its role operations. -/
def Op.chg {Child : Type} (cs : Step L β → ℕ) (cg : ℕ) (cc : Child → ℕ) : Model.Op L β Child → ℕ
  | .prim s => cs s
  | .node _ _ ops => (ops.map (RoleOp.chg cs cg cc)).sum

/-- Total (sequential) charge of a depth-`d` procedure. -/
def chargeK (cs : Step L β → ℕ) (cg : ℕ) : (d : ℕ) → ProcK L β d → ℕ
  | 0, p => ((@id (List (Step L β)) p).map cs).sum
  | d + 1, p => ((@id (List (Model.Op L β (ProcK L β d))) p).map (Op.chg cs cg (chargeK cs cg d))).sum

/-- Every step and gate of a role operation respects its charge (children: `cok`). -/
def RoleOp.chgOK {W : ℕ} {Child : Type} (pt : ℕ → β → Prop) (cs : Step L β → ℕ) (cg : ℕ)
    (cok : Child → Prop) : RoleOp L β W Child → Prop
  | .prim _ s => StepOK pt s (cs s)
  | .gate G _ => GateOK pt G cg
  | .call _ ch => cok ch
  | .relabel _ => True

/-- Every step and gate of an operation respects its charge. -/
def Op.chgOK {Child : Type} (pt : ℕ → β → Prop) (cs : Step L β → ℕ) (cg : ℕ)
    (cok : Child → Prop) : Model.Op L β Child → Prop
  | .prim s => StepOK pt s (cs s)
  | .node _ _ ops => ∀ ro ∈ ops, RoleOp.chgOK pt cs cg cok ro

/-- Every step and gate of a depth-`d` procedure (children included) respects its charge. -/
def ChargeOK (pt : ℕ → β → Prop) (cs : Step L β → ℕ) (cg : ℕ) : (d : ℕ) → ProcK L β d → Prop
  | 0, p => ∀ s ∈ (@id (List (Step L β)) p), StepOK pt s (cs s)
  | d + 1, p => ∀ o ∈ (@id (List (Model.Op L β (ProcK L β d))) p), Op.chgOK pt cs cg (ChargeOK pt cs cg d) o

/-! ## Generic accumulation over a list of operations -/

theorem forall_fin_cons {α B : Type*} (run : α → B → B) (P : α → B → Prop) (a : α) (l : List α)
    (A : B) :
    (∀ i : Fin (a :: l).length,
        P ((a :: l).get i) (((a :: l).take i.val).foldl (fun B o => run o B) A)) ↔
      P a A ∧ ∀ i : Fin l.length, P (l.get i) ((l.take i.val).foldl (fun B o => run o B) (run a A)) := by
  constructor
  · intro h
    exact ⟨h ⟨0, Nat.succ_pos _⟩, fun i => h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩⟩
  · rintro ⟨h0, hs⟩ ⟨i, hi⟩
    cases i with
    | zero => exact h0
    | succ i => exact hs ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem foldl_take_succ {α B : Type*} (f : B → α → B) (l : List α) (A : B) (i : Fin l.length) :
    (l.take (i.val + 1)).foldl f A = f ((l.take i.val).foldl f A) (l.get i) := by
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem i.isLt]
  rfl

/-- Charges add up along a list of operations: the final state is guarded at the initial charge
plus the total, and the per-operation state predicates `P J` hold for every `J` at least that. -/
theorem list_accum {α B : Type*} (run : α → B → B) (P : ℕ → α → B → Prop) (G : ℕ → B → Prop)
    (charge : α → ℕ) (l : List α)
    (hrun : ∀ o ∈ l, ∀ j b, G j b → G (j + charge o) (run o b))
    (hP : ∀ o ∈ l, ∀ j J b, j + charge o ≤ J → G j b → P J o b) :
    ∀ j A, G j A → G (j + (l.map charge).sum) (l.foldl (fun B o => run o B) A) ∧
      ∀ J, j + (l.map charge).sum ≤ J →
        ∀ i : Fin l.length, P J (l.get i) ((l.take i.val).foldl (fun B o => run o B) A) := by
  induction l with
  | nil =>
    intro j A hA
    exact ⟨by simpa using hA, fun J _ i => absurd i.isLt (Nat.not_lt_zero _)⟩
  | cons a l ih =>
    intro j A hA
    have ha : a ∈ a :: l := List.mem_cons.mpr (Or.inl rfl)
    have hGa := hrun a ha j A hA
    obtain ⟨hfin, hst⟩ := ih (fun o ho => hrun o (List.mem_cons_of_mem _ ho))
      (fun o ho => hP o (List.mem_cons_of_mem _ ho)) (j + charge a) (run a A) hGa
    refine ⟨?_, fun J hJ => ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      rw [← Nat.add_assoc]
      exact hfin
    · simp only [List.map_cons, List.sum_cons] at hJ
      exact (forall_fin_cons run (P J) a l A).mpr
        ⟨hP a ha j J A (by omega) hA, hst J (by omega)⟩

/-! ## Steps, gates, relabellings -/

section Mono

variable {pt : ℕ → β → Prop} (hmono : ∀ J J' b, J ≤ J' → pt J b → pt J' b)
include hmono

theorem invA_mono {J J' : ℕ} (h : J ≤ J') {A : L.Addr → β} (hA : InvA pt J A) : InvA pt J' A :=
  fun x => hmono _ _ _ h (hA x)

theorem stepOK_mono {s : Step L β} {g g' : ℕ} (hs : StepOK pt s g) (hg : g ≤ g') :
    StepOK pt s g' :=
  fun J A hA => invA_mono hmono (Nat.add_le_add_left hg J) (hs J A hA)

theorem stepOK_runIn {s : Step L β} {g : ℕ} (hs : StepOK pt s g) (c : RowClass L) {J : ℕ}
    {A : L.Addr → β} (hA : InvA pt J A) : InvA pt (J + g) (Step.runIn c s A) := by
  intro x
  unfold Step.runIn
  split_ifs
  · exact hs J A hA x
  · exact hmono _ _ _ (Nat.le_add_right J g) (hA x)

theorem gateOK_gateRun {W : ℕ} {G : (Fin W → β) → (Fin W → β)} {g : ℕ} (hG : GateOK pt G g)
    (c : RowClass L) (hW : 0 < W) {J : ℕ} {A : L.Addr → β} (hA : InvA pt J A) :
    InvA pt (J + g) (gateRun c W hW G A) := by
  intro x
  unfold gateRun
  split_ifs
  · exact hG J _ (fun _ => hA _) _
  · exact hmono _ _ _ (Nat.le_add_right J g) (hA x)

end Mono

theorem invA_relabelRun {pt : ℕ → β → Prop} {W : ℕ} (c : RowClass L) (hW : 0 < W)
    (π : Equiv.Perm (Fin W)) {J : ℕ} {A : L.Addr → β} (hA : InvA pt J A) :
    InvA pt J (relabelRun c W hW π A) := by
  intro x
  unfold relabelRun
  split_ifs
  · exact hA _
  · exact hA x

theorem stepOK_elem (pt : ℕ → β → Prop) (e : Elem L) : StepOK pt (.elem e) 0 :=
  fun _ _ hA x => hA (e.pull x)

theorem stepOK_sparsePerm (pt : ℕ → β → Prop) (pull : L.Addr → L.Addr) (supp : Finset L.Addr) :
    StepOK pt (.sparsePerm pull supp) 0 :=
  fun _ _ hA x => hA (pull x)

theorem stepOK_swapBlocks (pt : ℕ → β → Prop) (t₀ s₀ len : ℕ) :
    StepOK pt (Step.swapBlocks t₀ s₀ len : Step L β) 0 :=
  fun _ _ hA _ => hA _

theorem stepOK_recMap {pt : ℕ → β → Prop} {f : β → β} {g : ℕ}
    (hf : ∀ J b, pt J b → pt (J + g) (f b)) : StepOK pt (Step.recMap f : Step L β) g :=
  fun J A hA x => hf J (A x) (hA x)

theorem stepOK_addrMap {pt : ℕ → β → Prop} {f : L.Addr → β → β} {g : ℕ}
    (hf : ∀ J x b, pt J b → pt (J + g) (f x b)) : StepOK pt (.addrMap f) g :=
  fun J A hA x => hf J x (A x) (hA x)

theorem stepOK_digitGate {pt : ℕ → β → Prop} {i : Fin L.n}
    {G : (Fin (L.r i) → β) → (Fin (L.r i) → β)} {g : ℕ} (hG : GateOK pt G g) :
    StepOK pt (.digitGate i G) g :=
  fun J _ hA x => hG J _ (fun _ => hA _) (x i)

/-! ## The run theorem -/

/-- **Guard accounting over a run.** If every step and gate of `p` respects its charge, then from
an input guarded at charge `J` the output of `ProcK.run d p c A` is guarded at charge
`J + chargeK cs cg d p`, and all intermediate arrays (`ProcK.AllStates`) are guarded at every
charge `J' ≥ J + chargeK cs cg d p`. -/
theorem run_charge (pt : ℕ → β → Prop) (hmono : ∀ J J' b, J ≤ J' → pt J b → pt J' b)
    (cs : Step L β → ℕ) (cg : ℕ) :
    ∀ (d : ℕ) (p : ProcK L β d), ChargeOK pt cs cg d p → ∀ (c : RowClass L) (J : ℕ)
      (A : L.Addr → β), InvA pt J A →
      InvA pt (J + chargeK cs cg d p) (ProcK.run d p c A) ∧
      ∀ J', J + chargeK cs cg d p ≤ J' → ProcK.AllStates (InvA pt J') d p c A := by
  intro d
  induction d with
  | zero =>
    intro p hp c J A hA
    have hrun : ∀ s ∈ (@id (List (Step L β)) p), ∀ j B, InvA pt j B →
        InvA pt (j + cs s) (Step.runIn c s B) :=
      fun s hs j B hB => stepOK_runIn hmono (hp s hs) c hB
    have hP : ∀ s ∈ (@id (List (Step L β)) p), ∀ j J' B, j + cs s ≤ J' → InvA pt j B →
        InvA pt J' (Step.runIn c s B) :=
      fun s hs j J' B hJ hB => invA_mono hmono hJ (stepOK_runIn hmono (hp s hs) c hB)
    obtain ⟨hfin, hst⟩ := list_accum (fun s B => Step.runIn c s B)
      (fun J' s B => InvA pt J' (Step.runIn c s B)) (InvA pt) cs (@id (List (Step L β)) p)
      hrun hP J A hA
    refine ⟨hfin, fun J' hJ' => ?_⟩
    simp only [ProcK.AllStates]
    refine ⟨invA_mono hmono (le_trans (Nat.le_add_right _ _) hJ') hA, fun i => ?_⟩
    rw [foldl_take_succ]
    exact hst J' hJ' i
  | succ d ih =>
    intro p hp c J A hA
    have hro : ∀ {W : ℕ} (hW : 0 < W) (ro : RoleOp L β W (ProcK L β d)),
        RoleOp.chgOK pt cs cg (ChargeOK pt cs cg d) ro →
        (∀ j B, InvA pt j B → InvA pt (j + RoleOp.chg cs cg (chargeK cs cg d) ro)
          (RoleOp.run (ProcK.run d) c hW ro B)) ∧
        (∀ j J' B, j + RoleOp.chg cs cg (chargeK cs cg d) ro ≤ J' → InvA pt j B →
          RoleOp.allStates (ProcK.run d) (ProcK.AllStates (InvA pt J') d) (InvA pt J') c hW ro B) := by
      intro W hW ro hok
      cases ro with
      | prim k s =>
        exact ⟨fun j B hB => stepOK_runIn hmono hok (c.sub W hW k) hB,
          fun j J' B hJ hB => invA_mono hmono hJ (stepOK_runIn hmono hok (c.sub W hW k) hB)⟩
      | gate G t =>
        exact ⟨fun j B hB => gateOK_gateRun hmono hok c hW hB,
          fun j J' B hJ hB => invA_mono hmono hJ (gateOK_gateRun hmono hok c hW hB)⟩
      | call k ch =>
        exact ⟨fun j B hB => (ih ch hok (c.sub W hW k) j B hB).1,
          fun j J' B hJ hB => (ih ch hok (c.sub W hW k) j B hB).2 J' hJ⟩
      | relabel π =>
        exact ⟨fun j B hB => invA_relabelRun c hW π hB,
          fun j J' B hJ hB => invA_mono hmono (le_trans (Nat.le_add_right _ _) hJ)
            (invA_relabelRun c hW π hB)⟩
    have hop : ∀ o : Model.Op L β (ProcK L β d), Op.chgOK pt cs cg (ChargeOK pt cs cg d) o →
        (∀ j B, InvA pt j B → InvA pt (j + Op.chg cs cg (chargeK cs cg d) o)
          (Op.run (ProcK.run d) c o B)) ∧
        (∀ j J' B, j + Op.chg cs cg (chargeK cs cg d) o ≤ J' → InvA pt j B →
          Op.allStates (ProcK.run d) (ProcK.AllStates (InvA pt J') d) (InvA pt J') c o B) := by
      intro o hok
      cases o with
      | prim s =>
        exact ⟨fun j B hB => stepOK_runIn hmono hok c hB,
          fun j J' B hJ hB => invA_mono hmono hJ (stepOK_runIn hmono hok c hB)⟩
      | node W hW ops =>
        have hrun : ∀ ro ∈ ops, ∀ j B, InvA pt j B →
            InvA pt (j + RoleOp.chg cs cg (chargeK cs cg d) ro) (RoleOp.run (ProcK.run d) c hW ro B) :=
          fun ro hmem => (hro hW ro (hok ro hmem)).1
        have hP : ∀ ro ∈ ops, ∀ j J' B, j + RoleOp.chg cs cg (chargeK cs cg d) ro ≤ J' →
            InvA pt j B → RoleOp.allStates (ProcK.run d) (ProcK.AllStates (InvA pt J') d)
              (InvA pt J') c hW ro B :=
          fun ro hmem => (hro hW ro (hok ro hmem)).2
        have key := list_accum (fun ro B => RoleOp.run (ProcK.run d) c hW ro B)
          (fun J' ro B => RoleOp.allStates (ProcK.run d) (ProcK.AllStates (InvA pt J') d)
            (InvA pt J') c hW ro B) (InvA pt) (RoleOp.chg cs cg (chargeK cs cg d)) ops hrun hP
        exact ⟨fun j B hB => (key j B hB).1, fun j J' B hJ hB => (key j B hB).2 J' hJ⟩
    have hrun : ∀ o ∈ (@id (List (Model.Op L β (ProcK L β d))) p), ∀ j B, InvA pt j B →
        InvA pt (j + Op.chg cs cg (chargeK cs cg d) o) (Op.run (ProcK.run d) c o B) :=
      fun o hmem => (hop o (hp o hmem)).1
    have hP : ∀ o ∈ (@id (List (Model.Op L β (ProcK L β d))) p), ∀ j J' B,
        j + Op.chg cs cg (chargeK cs cg d) o ≤ J' → InvA pt j B →
        Op.allStates (ProcK.run d) (ProcK.AllStates (InvA pt J') d) (InvA pt J') c o B :=
      fun o hmem => (hop o (hp o hmem)).2
    obtain ⟨hfin, hst⟩ := list_accum (fun o B => Op.run (ProcK.run d) c o B)
      (fun J' o B => Op.allStates (ProcK.run d) (ProcK.AllStates (InvA pt J') d) (InvA pt J') c o B)
      (InvA pt) (Op.chg cs cg (chargeK cs cg d)) (@id (List (Model.Op L β (ProcK L β d))) p) hrun hP
      J A hA
    refine ⟨hfin, fun J' hJ' => ?_⟩
    simp only [ProcK.AllStates]
    exact ⟨invA_mono hmono (le_trans (Nat.le_add_right _ _) hJ') hA, hst J' hJ'⟩

/-! ## Monotonicity of `AllStates` in the guard predicate -/

theorem roleOp_allStates_mono {W : ℕ} {Child : Type}
    {crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)}
    {call call' : Child → RowClass L → (L.Addr → β) → Prop} {G G' : (L.Addr → β) → Prop}
    (hcall : ∀ ch c A, call ch c A → call' ch c A) (hG : ∀ B, G B → G' B) (c : RowClass L)
    (hW : 0 < W) (o : RoleOp L β W Child) (A : L.Addr → β) :
    RoleOp.allStates crun call G c hW o A → RoleOp.allStates crun call' G' c hW o A := by
  cases o with
  | call k ch => exact hcall _ _ _
  | prim k s => exact hG _
  | gate Gf t => exact hG _
  | relabel π => exact hG _

theorem op_allStates_mono {Child : Type}
    {crun : Child → RowClass L → (L.Addr → β) → (L.Addr → β)}
    {call call' : Child → RowClass L → (L.Addr → β) → Prop} {G G' : (L.Addr → β) → Prop}
    (hcall : ∀ ch c A, call ch c A → call' ch c A) (hG : ∀ B, G B → G' B) (c : RowClass L)
    (o : Model.Op L β Child) (A : L.Addr → β) :
    Op.allStates crun call G c o A → Op.allStates crun call' G' c o A := by
  cases o with
  | prim s => exact hG _
  | node W hW ops => exact fun h i => roleOp_allStates_mono hcall hG c hW _ _ (h i)

/-- `ProcK.AllStates` is monotone in the guard predicate. -/
theorem allStates_mono {G G' : (L.Addr → β) → Prop} :
    ∀ {d : ℕ} {p : ProcK L β d} {c : RowClass L} {A : L.Addr → β},
      ProcK.AllStates G d p c A → (∀ B, G B → G' B) → ProcK.AllStates G' d p c A := by
  intro d
  induction d with
  | zero =>
    intro p c A h hG
    simp only [ProcK.AllStates] at h ⊢
    exact ⟨hG _ h.1, fun i => hG _ (h.2 i)⟩
  | succ d ih =>
    intro p c A h hG
    simp only [ProcK.AllStates] at h ⊢
    exact ⟨hG _ h.1, fun i => op_allStates_mono (fun ch c' B h' => ih h' hG) hG c _ _ (h.2 i)⟩

/-! ## Charges of concatenations -/

theorem chargeK_append_zero (cs : Step L β → ℕ) (cg : ℕ) (p q : List (Step L β)) :
    chargeK cs cg 0 (p ++ q) = chargeK cs cg 0 p + chargeK cs cg 0 q := by
  simp [chargeK, List.map_append, List.sum_append]

theorem chargeK_append_succ (cs : Step L β → ℕ) (cg : ℕ) (d : ℕ)
    (p q : List (Model.Op L β (ProcK L β d))) :
    chargeK cs cg (d + 1) (p ++ q) = chargeK cs cg (d + 1) p + chargeK cs cg (d + 1) q := by
  simp [chargeK, List.map_append, List.sum_append]

theorem chargeOK_append_zero (pt : ℕ → β → Prop) (cs : Step L β → ℕ) (cg : ℕ)
    (p q : List (Step L β)) :
    ChargeOK pt cs cg 0 (p ++ q) ↔ ChargeOK pt cs cg 0 p ∧ ChargeOK pt cs cg 0 q := by
  simp only [ChargeOK]
  exact ⟨fun h => ⟨fun s hs => h s (List.mem_append_left _ hs),
      fun s hs => h s (List.mem_append_right _ hs)⟩,
    fun h s hs => (List.mem_append.mp hs).elim (h.1 s) (h.2 s)⟩

theorem chargeOK_append_succ (pt : ℕ → β → Prop) (cs : Step L β → ℕ) (cg : ℕ) (d : ℕ)
    (p q : List (Model.Op L β (ProcK L β d))) :
    ChargeOK pt cs cg (d + 1) (p ++ q) ↔ ChargeOK pt cs cg (d + 1) p ∧ ChargeOK pt cs cg (d + 1) q := by
  simp only [ChargeOK]
  exact ⟨fun h => ⟨fun o ho => h o (List.mem_append_left _ ho),
      fun o ho => h o (List.mem_append_right _ ho)⟩,
    fun h o ho => (List.mem_append.mp ho).elim (h.1 o) (h.2 o)⟩

/-! ## Sequences of procedures (`PSeq`, phase 2 of the layer) -/

/-- **Guard accounting over a sequence of procedures**: the charges of the members add up. -/
theorem pseq_charge (pt : ℕ → β → Prop) (hmono : ∀ J J' b, J ≤ J' → pt J b → pt J' b)
    (cs : Step L β → ℕ) (cg : ℕ) :
    ∀ (s : PSeq L β), (∀ q ∈ s, ChargeOK pt cs cg q.1 q.2) → ∀ (c : RowClass L) (J : ℕ)
      (A : L.Addr → β), InvA pt J A →
      InvA pt (J + (s.map fun q => chargeK cs cg q.1 q.2).sum) (s.run c A) ∧
      ∀ J', J + (s.map fun q => chargeK cs cg q.1 q.2).sum ≤ J' →
        PSeq.AllStates (InvA pt J') s c A := by
  intro s hs c J A hA
  have key := list_accum (fun q B => ProcK.run q.1 q.2 c B)
    (fun J' q B => ProcK.AllStates (InvA pt J') q.1 q.2 c B) (InvA pt)
    (fun q => chargeK cs cg q.1 q.2) s
    (fun q hq j B hB => (run_charge pt hmono cs cg q.1 q.2 (hs q hq) c j B hB).1)
    (fun q hq j J' B hJ hB => (run_charge pt hmono cs cg q.1 q.2 (hs q hq) c j B hB).2 J' hJ)
    J A hA
  exact ⟨key.1, fun J' hJ' => key.2 J' hJ'⟩

/-- `PSeq.AllStates` is monotone in the guard predicate. -/
theorem pseq_allStates_mono {G G' : (L.Addr → β) → Prop} {s : PSeq L β} {c : RowClass L}
    {A : L.Addr → β} (h : PSeq.AllStates G s c A) (hG : ∀ B, G B → G' B) :
    PSeq.AllStates G' s c A :=
  fun i => allStates_mono (h i) hG

end SubNLogN.Math.Networks.LayerGuardRun
