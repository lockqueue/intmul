import SubNLogN.Math.Networks.Framed

/-!
# Frame invariant (5) of [OAI26] §3.2 and the bit-network array corollary (B3)

Proved here:
* `frameInvariant_holds (h : ℕ) : FrameInvariantStmt h` — unconditional, every `h`, both networks;
  the general form `FI.framedNet_eq` only needs the edge operators to agree with `D_v ∘ D_u⁻¹` on
  the actual edges of each wire;
* `bitArrayCorollary_of` : `FrameInvariantStmt 100 → Lemma5BitStmt 100 → Prop7EndpointStmt →
  BitArrayCorollaryStmt` (B1 = `Lemma5BitStmt`, B2 = `Prop7EndpointStmt` enter as hypotheses).

Reusable incidence lemmas (used for the serialization `SerialEqFramedStmt` and Proposition A.7 (`prop:transfer11`)):
`FI.touch_pairwise`, `FI.touch_inv`, `FI.touch_unique`, `FI.gateAt_eq_some_iff`, `FI.edgeInto_gate`,
`FI.edgeInto_sink`, `FI.rowUpd_untouched` (a row writes only wires touched at its time),
`FI.rowUpd_local` (on a wire of gate `g` it reads only wires of `g`), `FI.rowUpd_comm` (it commutes
with linear maps constant on each gate).

Sources: [OAI26, §3.2, (5)]; Appendix D.2, Proposition D.3 (`oai:networks`); Proposition A.7 (`prop:transfer11`).

## Proof plan
1. *Clocks.* A gate `g` has clock `clk g = 8·stage + time ∈ [0, 24)`. Every touch list is strictly
   increasing in clock (`touch_pairwise`), and a gate of `w` at stage `j` belongs to the invocation
   `invOf j w` (`touch_inv`).
2. *Vertex before a clock.* `vtxAt w c` is the last vertex of `w` (its source or a gate) with clock
   `< c`. Then `edgeInto w (gate g) = (vtxAt w (clk g), gate g)` for `g ∈ touch w`,
   `edgeInto w (sink w) = (vtxAt w 24, sink w)`, `vtxAt w (clk g + 1) = gate g`, and `vtxAt w` is
   constant across clocks at which `w` has no gate.
3. *Row commutation.* A schedule row at `(j, ι, r)` changes a wire only by adding a linear
   combination of wires touched by the same gate at `(j, ι, r)` (side rows: `y_S` and the `A_{S·}`,
   or `x_T` and the `A_{·T}`; centre rows: one logical bank and the centres). Hence the row commutes
   with any family of linear maps that is constant on each gate at `(j, ι, r)` (`rowUpd_comm`).
4. *Step.* If `s w = D (pos w) (l w)` for all `w`, then after the incoming edges and the row at
   `(j, ι, r)` the same holds with `pos' w` = the gate of `w` at `(j, ι, r)` (if any), else `pos w`.
5. *Invocation, stage, network.* Iterate 4 over `r = 0, …, 7` with `pos w = vtxAt w (8j + r)` on
   the wires of `ι` (other wires frozen); after stage `j` the invariant holds at clock `8(j+1)`.
   Finally the sink edge `D_sink D_{vtxAt w 24}⁻¹` gives `D_sink (net …)`.
6. *Corollary.* `D_v` = precomposition with `(H, D, σ) ↦ (H − M_v' D, D, σ)` (`M' = M mod q^b`).
   `ratMod` is additive on `q`-integral rationals, so `Φ_{M_v − M_u} = D_v D_u⁻¹`; then B1 routes
   input role `w` to `ρ w`, and B2 (through `LinearMap.toMatrix'`) gives `M_{sink ρw} − M_{source w} = 1`.
-/

namespace SubNLogN.Math.Networks

namespace FI

variable {h : ℕ} {κ : Kind}

/-! ### 1. Clocks -/

/-- Numeric index of a stage (`0, 1, 2`). -/
def stIdx : Stage → ℕ
  | .one => 0
  | .two => 1
  | .three => 2

theorem stIdx_lt (j : Stage) : stIdx j < 3 := by cases j <;> decide

theorem stIdx_inj {j j' : Stage} (hj : stIdx j = stIdx j') : j = j' := by
  cases j <;> cases j' <;> simp_all [stIdx]

/-- Global clock of a gate: `8 · stage + time ∈ [0, 24)`. -/
def clk (g : Gate h) : ℕ := 8 * stIdx g.stage + g.time.val

theorem clk_lt (g : Gate h) : clk g < 24 := by
  have := stIdx_lt g.stage
  have := g.time.isLt
  unfold clk
  omega

theorem clk_eq_iff (g : Gate h) (j : Stage) (r : Fin 8) :
    clk g = 8 * stIdx j + r.val ↔ g.stage = j ∧ g.time = r := by
  constructor
  · intro hc
    have h1 := g.time.isLt
    have h2 := r.isLt
    unfold clk at hc
    have hs : stIdx g.stage = stIdx j := by omega
    have ht : g.time.val = r.val := by omega
    exact ⟨stIdx_inj hs, Fin.ext ht⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ### 2. The vertex of a wire before a clock -/

/-- The last vertex (the start vertex `v`, or a gate of `gs`) whose clock is `< c`; meaningful for
clock-sorted `gs`. -/
def lastBefore (c : ℕ) : Vertex κ h → List (Gate h) → Vertex κ h
  | v, [] => v
  | v, g :: gs => if clk g < c then lastBefore c (.gate g) gs else v

theorem lastBefore_of_le (c : ℕ) (v : Vertex κ h) (gs : List (Gate h))
    (hc : ∀ g ∈ gs, c ≤ clk g) : lastBefore c v gs = v := by
  cases gs with
  | nil => rfl
  | cons g gs =>
    have : ¬ clk g < c := Nat.not_lt.2 (hc g List.mem_cons_self)
    simp only [lastBefore, if_neg this]

theorem lastBefore_succ_of_ne (c : ℕ) : ∀ (v : Vertex κ h) (gs : List (Gate h)),
    (∀ g ∈ gs, clk g ≠ c) → lastBefore (c + 1) v gs = lastBefore c v gs
  | _, [], _ => rfl
  | v, g :: gs, hne => by
    have h1 : clk g ≠ c := hne g List.mem_cons_self
    have ih := lastBefore_succ_of_ne c (.gate g) gs
      (fun g' hg' => hne g' (List.mem_cons_of_mem _ hg'))
    by_cases hlt : clk g < c
    · have hlt' : clk g < c + 1 := by omega
      simp only [lastBefore, if_pos hlt, if_pos hlt', ih]
    · have hlt' : ¬ clk g < c + 1 := by omega
      simp only [lastBefore, if_neg hlt, if_neg hlt']

theorem lastBefore_succ_of_mem : ∀ (v : Vertex κ h) (gs : List (Gate h)) (g : Gate h),
    gs.Pairwise (fun a b => clk a < clk b) → g ∈ gs → lastBefore (clk g + 1) v gs = .gate g
  | _, [], _, _, hg => absurd hg List.not_mem_nil
  | v, g' :: gs, g, hpw, hg => by
    rw [List.pairwise_cons] at hpw
    by_cases hgg : g' = g
    · subst hgg
      simp only [lastBefore, if_pos (Nat.lt_succ_self _)]
      exact lastBefore_of_le _ _ _ (fun g'' hg'' => hpw.1 g'' hg'')
    · have hg' : g ∈ gs := by
        rcases List.mem_cons.1 hg with h' | h'
        · exact absurd h'.symm hgg
        · exact h'
      have hlt : clk g' < clk g + 1 := by have := hpw.1 g hg'; omega
      simp only [lastBefore, if_pos hlt]
      exact lastBefore_succ_of_mem _ gs g hpw.2 hg'

/-- `find?` on the edge list of `v0, gs, t` looking for the edge into a gate `g ∈ gs`. -/
theorem find_zip_gate (t : Vertex κ h) (g : Gate h)
    (p : Vertex κ h × Vertex κ h → Bool) (hp : ∀ e, p e = true ↔ e.2 = .gate g) :
    ∀ (gs : List (Gate h)) (v0 : Vertex κ h), gs.Pairwise (fun a b => clk a < clk b) → g ∈ gs →
    (List.zip (v0 :: (gs.map Vertex.gate ++ [t])) (gs.map Vertex.gate ++ [t])).find? p =
      some (lastBefore (clk g) v0 gs, .gate g)
  | [], _, _, hg => absurd hg List.not_mem_nil
  | g' :: gs, v0, hpw, hg => by
    rw [List.pairwise_cons] at hpw
    simp only [List.map_cons, List.cons_append, List.zip_cons_cons]
    by_cases hgg : g' = g
    · subst hgg
      rw [List.find?_cons_of_pos ((hp _).2 rfl)]
      simp only [lastBefore, lt_irrefl, if_false]
    · have hg' : g ∈ gs := by
        rcases List.mem_cons.1 hg with h' | h'
        · exact absurd h'.symm hgg
        · exact h'
      have hpf : ¬ p (v0, .gate g') = true := by
        rw [hp]
        intro he
        exact hgg (Vertex.gate.inj he)
      rw [List.find?_cons_of_neg hpf, find_zip_gate t g p hp gs (.gate g') hpw.2 hg']
      simp only [lastBefore, if_pos (hpw.1 g hg')]

/-- `find?` on the edge list of `v0, gs, t` looking for the edge into the final vertex `t`. -/
theorem find_zip_last (t : Vertex κ h) (ht : ∀ g, t ≠ .gate g)
    (p : Vertex κ h × Vertex κ h → Bool) (hp : ∀ e, p e = true ↔ e.2 = t) :
    ∀ (gs : List (Gate h)) (v0 : Vertex κ h),
    (List.zip (v0 :: (gs.map Vertex.gate ++ [t])) (gs.map Vertex.gate ++ [t])).find? p =
      some (lastBefore 24 v0 gs, t)
  | [], v0 => by
    simp only [List.map_nil, List.nil_append, List.zip_cons_cons, List.zip_nil_right]
    rw [List.find?_cons_of_pos ((hp _).2 rfl)]
    rfl
  | g' :: gs, v0 => by
    simp only [List.map_cons, List.cons_append, List.zip_cons_cons]
    have hpf : ¬ p (v0, .gate g') = true := by
      rw [hp]
      exact fun he => ht g' he.symm
    rw [List.find?_cons_of_neg hpf, find_zip_last t ht p hp gs (.gate g')]
    simp only [lastBefore, if_pos (clk_lt g')]

/-! ### Touch lists: clock order and invocations -/

theorem touch_pairwise (w : Role κ h) : (touch w).Pairwise (fun a b => clk a < clk b) := by
  cases w with
  | X a => simp [touch, clk, Gate.stage, Gate.time, stIdx]
  | Y a => simp [touch, clk, Gate.stage, Gate.time, stIdx]
  | side j ι p => cases j <;> simp [touch, clk, Gate.stage, Gate.time, stIdx]
  | center j ι c => cases j <;> simp [touch, clk, Gate.stage, Gate.time, stIdx]

theorem touch_inv (w : Role κ h) : ∀ g ∈ touch w, invOf g.stage w = some g.inv := by
  cases w with
  | X a => simp [touch, invOf, Gate.stage, Gate.inv]
  | Y a => simp [touch, invOf, Gate.stage, Gate.inv]
  | side j ι p => simp [touch, invOf, Gate.stage, Gate.inv]
  | center j ι c => simp [touch, invOf, Gate.stage, Gate.inv]


/-! ### `vtxAt`, `edgeInto` and `gateAt` -/

/-- The vertex of `w` just before clock `c`: its source, or its last gate with clock `< c`. -/
def vtxAt (w : Role κ h) (c : ℕ) : Vertex κ h := lastBefore c (.source w) (touch w)

theorem vtxAt_zero (w : Role κ h) : vtxAt w 0 = .source w :=
  lastBefore_of_le 0 _ _ (fun _ _ => Nat.zero_le _)

theorem vtxAt_succ_of_mem (w : Role κ h) (g : Gate h) (hg : g ∈ touch w) :
    vtxAt w (clk g + 1) = .gate g :=
  lastBefore_succ_of_mem _ _ g (touch_pairwise w) hg

theorem vtxAt_succ_of_ne (w : Role κ h) (c : ℕ) (hne : ∀ g ∈ touch w, clk g ≠ c) :
    vtxAt w (c + 1) = vtxAt w c :=
  lastBefore_succ_of_ne c _ _ hne

theorem vtxAt_add_of_no (w : Role κ h) (c : ℕ) : ∀ k : ℕ,
    (∀ g ∈ touch w, ¬ (c ≤ clk g ∧ clk g < c + k)) → vtxAt w (c + k) = vtxAt w c
  | 0, _ => rfl
  | k + 1, hno => by
    rw [← Nat.add_assoc, vtxAt_succ_of_ne]
    · exact vtxAt_add_of_no w c k (fun g hg hc => hno g hg ⟨hc.1, by omega⟩)
    · intro g hg hc
      exact hno g hg ⟨by omega, by omega⟩

theorem vertices_eq (w : Role κ h) :
    vertices w = Vertex.source w :: ((touch w).map Vertex.gate ++ [Vertex.sink w]) := by
  simp [vertices]

theorem edgeInto_gate (w : Role κ h) (g : Gate h) (hg : g ∈ touch w) :
    edgeInto w (.gate g) = some (vtxAt w (clk g), .gate g) := by
  unfold edgeInto edges
  rw [vertices_eq, List.tail_cons]
  exact find_zip_gate _ g _ (fun e => by simp) _ _ (touch_pairwise w) hg

theorem edgeInto_sink (w : Role κ h) :
    edgeInto w (.sink w) = some (vtxAt w 24, .sink w) := by
  unfold edgeInto edges
  rw [vertices_eq, List.tail_cons]
  exact find_zip_last _ (fun g => by simp) _ (fun e => by simp) _ _

/-- The edge returned by `edgeInto` is an edge of the wire. -/
theorem edgeInto_mem {w : Role κ h} {v : Vertex κ h} {e : Vertex κ h × Vertex κ h}
    (he : edgeInto w v = some e) : e ∈ edges w := by
  unfold edgeInto at he
  exact List.mem_of_find?_eq_some he

theorem gateAt_spec {j : Stage} {ι : Fix h} {r : Fin 8} {w : Role κ h} {g : Gate h}
    (hg : gateAt j ι r w = some g) : g ∈ touch w ∧ g.stage = j ∧ g.inv = ι ∧ g.time = r := by
  unfold gateAt at hg
  have h1 := List.mem_of_find?_eq_some hg
  have h2 := List.find?_some hg
  simp only [decide_eq_true_eq] at h2
  exact ⟨h1, h2⟩

theorem gateAt_none {j : Stage} {ι : Fix h} {r : Fin 8} {w : Role κ h}
    (hg : gateAt j ι r w = none) : ∀ g ∈ touch w, ¬ (g.stage = j ∧ g.inv = ι ∧ g.time = r) := by
  unfold gateAt at hg
  rw [List.find?_eq_none] at hg
  intro g hgm hc
  exact hg g hgm (by simpa using hc)

theorem find?_eq_some_of_unique {α : Type*} (f : α → ℕ) (p : α → Bool) :
    ∀ (l : List α) (a : α), l.Pairwise (fun x y => f x < f y) → a ∈ l → p a = true →
    (∀ b ∈ l, p b = true → f b = f a) → l.find? p = some a
  | [], _, _, ha, _, _ => absurd ha List.not_mem_nil
  | b :: l, a, hpw, ha, hpa, huniq => by
    rw [List.pairwise_cons] at hpw
    by_cases hpb : p b = true
    · rw [List.find?_cons_of_pos hpb]
      have hfb := huniq b List.mem_cons_self hpb
      rcases List.mem_cons.1 ha with h' | h'
      · rw [h']
      · exact absurd hfb (Nat.ne_of_lt (hpw.1 a h'))
    · rw [List.find?_cons_of_neg hpb]
      rcases List.mem_cons.1 ha with h' | h'
      · exact absurd (h' ▸ hpa) hpb
      · exact find?_eq_some_of_unique f p l a hpw.2 h' hpa
          (fun b' hb' hpb' => huniq b' (List.mem_cons_of_mem _ hb') hpb')

theorem gateAt_of_mem {j : Stage} {ι : Fix h} {r : Fin 8} {w : Role κ h} {g : Gate h}
    (hm : g ∈ touch w) (hs : g.stage = j) (hi : g.inv = ι) (ht : g.time = r) :
    gateAt j ι r w = some g := by
  unfold gateAt
  apply find?_eq_some_of_unique clk _ _ g (touch_pairwise w) hm (by simp [hs, hi, ht])
  intro b _ hb
  simp only [decide_eq_true_eq] at hb
  unfold clk
  rw [hb.1, hb.2.2, hs, ht]


/-! ### 3. Row commutation -/

theorem fix_mk (j : Stage) (ι : Fix h) (S : Tri h) : (Addr.mk j ι S).fix j = ι := by
  cases j <;> rfl

theorem var_mk (j : Stage) (ι : Fix h) (S : Tri h) : (Addr.mk j ι S).var j = S := by
  cases j <;> rfl

theorem mem_touch_X {a : Addr h} {j : Stage} {ι : Fix h} (hι : a.fix j = ι) {S : Tri h}
    (hS : a.var j = S) (r : Fin 8) (hr : r = 2 ∨ r = 7) :
    Gate.side j ι r S ∈ touch (κ := κ) (.X a) := by
  subst hι hS
  cases j <;> rcases hr with rfl | rfl <;> simp [touch]

theorem mem_touch_X_center {a : Addr h} {j : Stage} {ι : Fix h} (hι : a.fix j = ι) (r : Fin 8)
    (hr : r = 3 ∨ r = 6) : Gate.center j ι r ∈ touch (κ := κ) (.X a) := by
  subst hι
  cases j <;> rcases hr with rfl | rfl <;> simp [touch]

theorem mem_touch_Y {a : Addr h} {j : Stage} {ι : Fix h} (hι : a.fix j = ι) {S : Tri h}
    (hS : a.var j = S) (r : Fin 8) (hr : r = 0 ∨ r = 5) :
    Gate.side j ι r S ∈ touch (κ := κ) (.Y a) := by
  subst hι hS
  cases j <;> rcases hr with rfl | rfl <;> simp [touch]

theorem mem_touch_Y_center {a : Addr h} {j : Stage} {ι : Fix h} (hι : a.fix j = ι) (r : Fin 8)
    (hr : r = 1 ∨ r = 4) : Gate.center j ι r ∈ touch (κ := κ) (.Y a) := by
  subst hι
  cases j <;> rcases hr with rfl | rfl <;> simp [touch]

theorem mem_touch_side_y {j : Stage} {ι : Fix h} (p : SideIdx κ h) (r : Fin 8)
    (hr : r = 0 ∨ r = 5) :
    Gate.side j ι r (if j.isInverse then p.1.2 else p.1.1) ∈ touch (.side j ι p) := by
  rcases hr with rfl | rfl <;> simp [touch]

theorem mem_touch_side_x {j : Stage} {ι : Fix h} (p : SideIdx κ h) (r : Fin 8)
    (hr : r = 2 ∨ r = 7) :
    Gate.side j ι r (if j.isInverse then p.1.1 else p.1.2) ∈ touch (.side j ι p) := by
  rcases hr with rfl | rfl <;> simp [touch]

theorem mem_touch_center {j : Stage} {ι : Fix h} (c : Center κ h) (r : Fin 8)
    (hr : r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 6) : Gate.center j ι r ∈ touch (.center j ι c) := by
  rcases hr with rfl | rfl | rfl | rfl <;> simp [touch]

theorem tgtTriple?_some {j : Stage} {ι : Fix h} {w : Role κ h} {S : Tri h}
    (hS : tgtTriple? j ι w = some S) :
    (∃ a, w = .X a ∧ j.isInverse = true ∧ a.fix j = ι ∧ a.var j = S) ∨
    (∃ a, w = .Y a ∧ j.isInverse = false ∧ a.fix j = ι ∧ a.var j = S) := by
  cases w with
  | X a =>
    left
    simp only [tgtTriple?, Option.ite_none_right_eq_some, Option.some.injEq] at hS
    exact ⟨a, rfl, hS.1.1, hS.1.2, hS.2⟩
  | Y a =>
    right
    simp only [tgtTriple?, Option.ite_none_right_eq_some, Option.some.injEq] at hS
    exact ⟨a, rfl, hS.1.1, hS.1.2, hS.2⟩
  | side _ _ _ => simp [tgtTriple?] at hS
  | center _ _ _ => simp [tgtTriple?] at hS

section Row

variable {Rg Ar : Type*} [CommRing Rg] [AddCommGroup Ar] [Module Rg Ar]

theorem gatherVal_comm (j : Stage) (ι : Fix h) (F : Role κ h → Ar →ₗ[Rg] Ar)
    (hG : ∀ (c : Center κ h) (T : Tri h), F (srcRole j ι T) = F (.center j ι c))
    (l : Role κ h → Ar) (c : Center κ h) :
    gatherVal j ι (fun w => F w (l w)) c = F (.center j ι c) (gatherVal j ι l c) := by
  cases c with
  | inl i =>
    simp only [gatherVal, map_sum]
    exact Finset.sum_congr rfl (fun T _ => by rw [hG (.inl i) T])
  | inr u =>
    simp only [gatherVal, map_sum]
    exact Finset.sum_congr rfl (fun T _ => by rw [hG (.inr u) T])

theorem sideVal_comm (half : Rg) (j : Stage) (ι : Fix h) (G : Ar →ₗ[Rg] Ar)
    (F : Role κ h → Ar →ₗ[Rg] Ar) (S : Tri h)
    (hJ : ∀ (T : Tri h) (hT : Nbr κ S T), F (.side j ι ⟨(S, T), hT⟩) = G)
    (l : Role κ h → Ar) :
    sideVal κ half j ι (fun w => F w (l w)) S = G (sideVal κ half j ι l S) := by
  simp only [sideVal, map_sum, map_smul]
  exact Finset.sum_congr rfl (fun T _ => by rw [hJ T.1 T.2])

theorem scatterVal_comm (half : Rg) (j : Stage) (ι : Fix h) (G : Ar →ₗ[Rg] Ar)
    (F : Role κ h → Ar →ₗ[Rg] Ar) (hR : ∀ c : Center κ h, F (.center j ι c) = G)
    (l : Role κ h → Ar) (S : Tri h) :
    scatterVal κ half j ι (fun w => F w (l w)) S = G (scatterVal κ half j ι l S) := by
  cases κ with
  | bit => simp only [scatterVal, map_sum, hR]
  | complex => simp only [scatterVal, map_smul, map_sub, map_sum, hR]

theorem rowUpd_V_comm (half : Rg) (j : Stage) (ι : Fix h) (ε : Rg)
    (F : Role κ h → Ar →ₗ[Rg] Ar)
    (hV : ∀ p : SideIdx κ h, F (.side j ι p) = F (srcRole j ι p.1.2)) (l : Role κ h → Ar)
    (w : Role κ h) :
    rowUpd κ half j ι .V ε (fun w => F w (l w)) w = F w (rowUpd κ half j ι .V ε l w) := by
  cases w with
  | side j' ι' p =>
    simp only [rowUpd]
    split_ifs with hc
    · obtain ⟨h1, h2⟩ := hc
      subst h1 h2
      rw [map_add, map_smul, hV p]
    · rfl
  | X a => rfl
  | Y a => rfl
  | center j' ι' c => rfl

theorem rowUpd_G_comm (half : Rg) (j : Stage) (ι : Fix h) (ε : Rg)
    (F : Role κ h → Ar →ₗ[Rg] Ar)
    (hG : ∀ (c : Center κ h) (T : Tri h), F (srcRole j ι T) = F (.center j ι c))
    (l : Role κ h → Ar) (w : Role κ h) :
    rowUpd κ half j ι .G ε (fun w => F w (l w)) w = F w (rowUpd κ half j ι .G ε l w) := by
  cases w with
  | center j' ι' c =>
    simp only [rowUpd]
    split_ifs with hc
    · obtain ⟨h1, h2⟩ := hc
      subst h1 h2
      rw [map_add, map_smul, gatherVal_comm _ _ F hG l c]
    · rfl
  | X a => rfl
  | Y a => rfl
  | side j' ι' p => rfl

theorem rowUpd_J_comm (half : Rg) (j : Stage) (ι : Fix h) (ε : Rg)
    (F : Role κ h → Ar →ₗ[Rg] Ar)
    (hJ : ∀ (w : Role κ h) (S : Tri h), tgtTriple? j ι w = some S →
      ∀ (T : Tri h) (hT : Nbr κ S T), F (.side j ι ⟨(S, T), hT⟩) = F w)
    (l : Role κ h → Ar) (w : Role κ h) :
    rowUpd κ half j ι .J ε (fun w => F w (l w)) w = F w (rowUpd κ half j ι .J ε l w) := by
  simp only [rowUpd]
  cases hS : tgtTriple? j ι w with
  | none => rfl
  | some S =>
    show F w (l w) + ε • sideVal κ half j ι (fun w => F w (l w)) S =
      F w (l w + ε • sideVal κ half j ι l S)
    rw [map_add, map_smul, sideVal_comm half j ι (F w) F S (hJ w S hS) l]

theorem rowUpd_R_comm (half : Rg) (j : Stage) (ι : Fix h) (ε : Rg)
    (F : Role κ h → Ar →ₗ[Rg] Ar)
    (hR : ∀ (w : Role κ h) (S : Tri h), tgtTriple? j ι w = some S →
      ∀ c : Center κ h, F (.center j ι c) = F w)
    (l : Role κ h → Ar) (w : Role κ h) :
    rowUpd κ half j ι .R ε (fun w => F w (l w)) w = F w (rowUpd κ half j ι .R ε l w) := by
  simp only [rowUpd]
  cases hS : tgtTriple? j ι w with
  | none => rfl
  | some S =>
    show F w (l w) + ε • scatterVal κ half j ι (fun w => F w (l w)) S =
      F w (l w + ε • scatterVal κ half j ι l S)
    rw [map_add, map_smul, scatterVal_comm half j ι (F w) F (hR w S hS) l S]

end Row


/-! ### Incidence facts of the rows: which gate at `(j, ι, r)` meets which wire -/

/-- Times of the `V` rows: `2, 7` (forward stages), `0, 5` (stage 2). -/
def TimesV (j : Stage) (r : Fin 8) : Prop :=
  (j.isInverse = false ∧ (r = 2 ∨ r = 7)) ∨ (j.isInverse = true ∧ (r = 0 ∨ r = 5))

/-- Times of the `G` rows: `3, 6` (forward stages), `1, 4` (stage 2). -/
def TimesG (j : Stage) (r : Fin 8) : Prop :=
  (j.isInverse = false ∧ (r = 3 ∨ r = 6)) ∨ (j.isInverse = true ∧ (r = 1 ∨ r = 4))

/-- Times of the `J` rows: `0, 5` (forward stages), `2, 7` (stage 2). -/
def TimesJ (j : Stage) (r : Fin 8) : Prop :=
  (j.isInverse = false ∧ (r = 0 ∨ r = 5)) ∨ (j.isInverse = true ∧ (r = 2 ∨ r = 7))

/-- Times of the `R` rows: `1, 4` (forward stages), `3, 6` (stage 2). -/
def TimesR (j : Stage) (r : Fin 8) : Prop :=
  (j.isInverse = false ∧ (r = 1 ∨ r = 4)) ∨ (j.isInverse = true ∧ (r = 3 ∨ r = 6))

theorem rowOp_cases (j : Stage) (r : Fin 8) :
    (rowOp j r = .V ∧ TimesV j r) ∨ (rowOp j r = .G ∧ TimesG j r) ∨
    (rowOp j r = .J ∧ TimesJ j r) ∨ (rowOp j r = .R ∧ TimesR j r) := by
  unfold TimesV TimesG TimesJ TimesR
  revert r
  cases j <;> decide

theorem center_times {j : Stage} {r : Fin 8} (hr : TimesG j r ∨ TimesR j r) :
    r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 6 := by
  unfold TimesG TimesR at hr
  rcases hr with (⟨_, h' | h'⟩ | ⟨_, h' | h'⟩) | (⟨_, h' | h'⟩ | ⟨_, h' | h'⟩) <;> simp [h']

/-- A `V` row at `(j, ι, r)` updating `A_p` reads `x_{p.2}`; the gate `side j ι r p.2` meets both. -/
theorem memV {j : Stage} {ι : Fix h} {r : Fin 8} (hr : TimesV j r) (p : SideIdx κ h) :
    Gate.side j ι r p.1.2 ∈ touch (.side j ι p : Role κ h) ∧
      Gate.side j ι r p.1.2 ∈ touch (srcRole j ι p.1.2 : Role κ h) := by
  rcases hr with ⟨hj, hr'⟩ | ⟨hj, hr'⟩
  · refine ⟨by simpa [hj] using mem_touch_side_x (j := j) (ι := ι) p r hr', ?_⟩
    rw [show (srcRole j ι p.1.2 : Role κ h) = .X (Addr.mk j ι p.1.2) by simp [srcRole, hj]]
    exact mem_touch_X (fix_mk j ι _) (var_mk j ι _) r hr'
  · refine ⟨by simpa [hj] using mem_touch_side_y (j := j) (ι := ι) p r hr', ?_⟩
    rw [show (srcRole j ι p.1.2 : Role κ h) = .Y (Addr.mk j ι p.1.2) by simp [srcRole, hj]]
    exact mem_touch_Y (fix_mk j ι _) (var_mk j ι _) r hr'

/-- A `G` row at `(j, ι, r)` reads the logical source bank; the gate `center j ι r` meets it. -/
theorem memG_src {j : Stage} {ι : Fix h} {r : Fin 8} (hr : TimesG j r) (T : Tri h) :
    Gate.center j ι r ∈ touch (srcRole j ι T : Role κ h) := by
  rcases hr with ⟨hj, hr'⟩ | ⟨hj, hr'⟩
  · rw [show (srcRole j ι T : Role κ h) = .X (Addr.mk j ι T) by simp [srcRole, hj]]
    exact mem_touch_X_center (fix_mk j ι T) r hr'
  · rw [show (srcRole j ι T : Role κ h) = .Y (Addr.mk j ι T) by simp [srcRole, hj]]
    exact mem_touch_Y_center (fix_mk j ι T) r hr'

/-- A `J` row at `(j, ι, r)` updating `y_S` reads `A_{S·}`; the gate `side j ι r S` meets them. -/
theorem memJ_side {j : Stage} {ι : Fix h} {r : Fin 8} (hr : TimesJ j r) (S T : Tri h)
    (hT : Nbr κ S T) : Gate.side j ι r S ∈ touch (.side j ι ⟨(S, T), hT⟩ : Role κ h) := by
  rcases hr with ⟨hj, hr'⟩ | ⟨hj, hr'⟩
  · simpa [hj] using mem_touch_side_y (j := j) (ι := ι) (⟨(S, T), hT⟩ : SideIdx κ h) r hr'
  · simpa [hj] using mem_touch_side_x (j := j) (ι := ι) (⟨(S, T), hT⟩ : SideIdx κ h) r hr'

/-- The logical target `y_S` of a `J` row at `(j, ι, r)` meets the gate `side j ι r S`. -/
theorem memJ_tgt {j : Stage} {ι : Fix h} {r : Fin 8} (hr : TimesJ j r) {w : Role κ h}
    {S : Tri h} (hS : tgtTriple? j ι w = some S) : Gate.side j ι r S ∈ touch w := by
  rcases tgtTriple?_some hS with ⟨a, rfl, hj, hι, hS'⟩ | ⟨a, rfl, hj, hι, hS'⟩
  · rcases hr with ⟨hj', _⟩ | ⟨_, hr'⟩
    · simp [hj] at hj'
    · exact mem_touch_X hι hS' r hr'
  · rcases hr with ⟨_, hr'⟩ | ⟨hj', _⟩
    · exact mem_touch_Y hι hS' r hr'
    · simp [hj] at hj'

/-- The logical target `y_S` of an `R` row at `(j, ι, r)` meets the gate `center j ι r`. -/
theorem memR_tgt {j : Stage} {ι : Fix h} {r : Fin 8} (hr : TimesR j r) {w : Role κ h}
    {S : Tri h} (hS : tgtTriple? j ι w = some S) : Gate.center j ι r ∈ touch w := by
  rcases tgtTriple?_some hS with ⟨a, rfl, hj, hι, -⟩ | ⟨a, rfl, hj, hι, -⟩
  · rcases hr with ⟨hj', _⟩ | ⟨_, hr'⟩
    · simp [hj] at hj'
    · exact mem_touch_X_center hι r hr'
  · rcases hr with ⟨_, hr'⟩ | ⟨hj', _⟩
    · exact mem_touch_Y_center hι r hr'
    · simp [hj] at hj'

section RowGate

variable {Rg Ar : Type*} [CommRing Rg] [AddCommGroup Ar] [Module Rg Ar]

/-- `F` agrees with `Fg g` on every wire touched by a gate `g` at `(j, ι, r)`. -/
def GateConst (j : Stage) (ι : Fix h) (r : Fin 8) (F : Role κ h → Ar →ₗ[Rg] Ar)
    (Fg : Gate h → Ar →ₗ[Rg] Ar) : Prop :=
  ∀ w g, g ∈ touch w → g.stage = j → g.inv = ι → g.time = r → F w = Fg g

/-- **Row commutation**: the scalar row at `(j, ι, r)` commutes with any family of linear maps that
is constant on each gate at `(j, ι, r)`. -/
theorem rowUpd_comm (half : Rg) (j : Stage) (ι : Fix h) (r : Fin 8) (ε : Rg)
    (F : Role κ h → Ar →ₗ[Rg] Ar) (Fg : Gate h → Ar →ₗ[Rg] Ar) (hF : GateConst j ι r F Fg)
    (l : Role κ h → Ar) (w : Role κ h) :
    rowUpd κ half j ι (rowOp j r) ε (fun w => F w (l w)) w =
      F w (rowUpd κ half j ι (rowOp j r) ε l w) := by
  rcases rowOp_cases j r with ⟨hop, hr⟩ | ⟨hop, hr⟩ | ⟨hop, hr⟩ | ⟨hop, hr⟩ <;> rw [hop]
  · refine rowUpd_V_comm half j ι ε F (fun p => ?_) l w
    rw [hF _ _ (memV hr p).1 rfl rfl rfl, hF _ _ (memV hr p).2 rfl rfl rfl]
  · refine rowUpd_G_comm half j ι ε F (fun c T => ?_) l w
    rw [hF _ _ (memG_src hr T) rfl rfl rfl,
      hF _ _ (mem_touch_center c r (center_times (Or.inl hr))) rfl rfl rfl]
  · refine rowUpd_J_comm half j ι ε F (fun w S hS T hT => ?_) l w
    rw [hF _ _ (memJ_side hr S T hT) rfl rfl rfl, hF _ _ (memJ_tgt hr hS) rfl rfl rfl]
  · refine rowUpd_R_comm half j ι ε F (fun w S hS c => ?_) l w
    rw [hF _ _ (mem_touch_center c r (center_times (Or.inr hr))) rfl rfl rfl,
      hF _ _ (memR_tgt hr hS) rfl rfl rfl]

end RowGate


/-! ### 4-5. Step, invocation, stage, network -/

section Invariant

variable {Rg Ar : Type*} [CommRing Rg] [AddCommGroup Ar] [Module Rg Ar]

/-- One framed time step `(j, ι, r)` preserves the invariant `s = D_pos (l)`, the positions of the
touched wires moving to their gates. -/
theorem framed_step (half : Rg) (E : EdgeOps κ h Ar) (D : Vertex κ h → (Ar ≃ₗ[Rg] Ar))
    (hE : ∀ w e, e ∈ edges w → ∀ x, E w e x = D e.2 ((D e.1).symm x))
    (j : Stage) (ι : Fix h) (r : Fin 8) (pos pos' : Role κ h → Vertex κ h)
    (hedge : ∀ w g, gateAt j ι r w = some g →
      edgeInto w (.gate g) = some (pos w, .gate g) ∧ pos' w = .gate g)
    (hnone : ∀ w, gateAt j ι r w = none → pos' w = pos w)
    (s l : Role κ h → Ar) (hinv : ∀ w, s w = D (pos w) (l w)) (w : Role κ h) :
    rowUpd κ half j ι (rowOp j r) ((rowSign j r : ℤ) : Rg) (preEdges E j ι r s) w =
      D (pos' w) (rowUpd κ half j ι (rowOp j r) ((rowSign j r : ℤ) : Rg) l w) := by
  have hpre : preEdges E j ι r s =
      fun w => ((D (pos' w) : Ar ≃ₗ[Rg] Ar) : Ar →ₗ[Rg] Ar) (l w) := by
    funext w
    unfold preEdges
    rcases hg : gateAt j ι r w with _ | g
    · simp only [hinv, hnone w hg, LinearEquiv.coe_coe]
    · obtain ⟨he, hp⟩ := hedge w g hg
      simp only [he, hE w _ (edgeInto_mem he), hinv, hp, LinearEquiv.symm_apply_apply,
        LinearEquiv.coe_coe]
  rw [hpre]
  have hF : GateConst j ι r (fun w => ((D (pos' w) : Ar ≃ₗ[Rg] Ar) : Ar →ₗ[Rg] Ar))
      (fun g => ((D (.gate g) : Ar ≃ₗ[Rg] Ar) : Ar →ₗ[Rg] Ar)) := by
    intro w' g hm hs hi ht
    simp only [(hedge w' g (gateAt_of_mem hm hs hi ht)).2]
  have := rowUpd_comm half j ι r ((rowSign j r : ℤ) : Rg) _ _ hF l w
  simpa only [LinearEquiv.coe_coe] using this

/-- Positions inside invocation `(j, ι)` after its first `n` time steps: wires of `ι` sit before
clock `8j + n`, all other wires before clock `8j`. -/
def posIn (j : Stage) (ι : Fix h) (n : ℕ) (w : Role κ h) : Vertex κ h :=
  if invOf j w = some ι then vtxAt w (8 * stIdx j + n) else vtxAt w (8 * stIdx j)

theorem posIn_edge (j : Stage) (ι : Fix h) (r : Fin 8) (n : ℕ) (hn : r.val = n) (w : Role κ h)
    (g : Gate h) (hg : gateAt j ι r w = some g) :
    edgeInto w (.gate g) = some (posIn j ι n w, .gate g) ∧ posIn j ι (n + 1) w = .gate g := by
  obtain ⟨hm, hs, hi, ht⟩ := gateAt_spec hg
  have hinv : invOf j w = some ι := by rw [← hs, ← hi]; exact touch_inv w g hm
  have hclk : clk g = 8 * stIdx j + n := by rw [← hn]; exact (clk_eq_iff g j r).2 ⟨hs, ht⟩
  refine ⟨?_, ?_⟩
  · rw [edgeInto_gate w g hm, posIn, if_pos hinv, hclk]
  · rw [posIn, if_pos hinv, ← Nat.add_assoc, ← hclk]
    exact vtxAt_succ_of_mem w g hm

theorem posIn_none (j : Stage) (ι : Fix h) (r : Fin 8) (n : ℕ) (hn : r.val = n) (w : Role κ h)
    (hg : gateAt j ι r w = none) : posIn j ι (n + 1) w = posIn j ι n w := by
  unfold posIn
  split_ifs with hinv
  · rw [← Nat.add_assoc]
    apply vtxAt_succ_of_ne
    intro g hm hc
    rw [← hn] at hc
    obtain ⟨hs, ht⟩ := (clk_eq_iff g j r).1 hc
    have h2 := touch_inv w g hm
    rw [hs, hinv] at h2
    exact gateAt_none hg g hm ⟨hs, (Option.some.inj h2).symm, ht⟩
  · rfl

/-- `rs` lists consecutive times starting at `n`. -/
def Consec : ℕ → List (Fin 8) → Prop
  | _, [] => True
  | n, r :: rs => r.val = n ∧ Consec (n + 1) rs

theorem fold_inv (half : Rg) (E : EdgeOps κ h Ar) (D : Vertex κ h → (Ar ≃ₗ[Rg] Ar))
    (hE : ∀ w e, e ∈ edges w → ∀ x, E w e x = D e.2 ((D e.1).symm x)) (j : Stage) (ι : Fix h) :
    ∀ (rs : List (Fin 8)) (n : ℕ), Consec n rs → ∀ (s l : Role κ h → Ar),
    (∀ w, s w = D (posIn j ι n w) (l w)) → ∀ w,
    rs.foldl (fun s r => rowUpd κ half j ι (rowOp j r) ((rowSign j r : ℤ) : Rg)
        (preEdges E j ι r s)) s w =
      D (posIn j ι (n + rs.length) w)
        (rs.foldl (fun s r => rowUpd κ half j ι (rowOp j r) ((rowSign j r : ℤ) : Rg) s) l w)
  | [], n, _, s, l, hinv, w => by simpa using hinv w
  | r :: rs, n, hc, s, l, hinv, w => by
    obtain ⟨hn, hc⟩ := hc
    simp only [List.foldl_cons, List.length_cons]
    rw [show n + (rs.length + 1) = (n + 1) + rs.length by omega]
    apply fold_inv half E D hE j ι rs (n + 1) hc
    intro w'
    exact framed_step half E D hE j ι r (posIn j ι n) (posIn j ι (n + 1))
      (fun w g hg => posIn_edge j ι r n hn w g hg) (fun w hg => posIn_none j ι r n hn w hg)
      s l hinv w'

theorem finRange_eight : List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide

theorem framed_invocation (half : Rg) (E : EdgeOps κ h Ar) (D : Vertex κ h → (Ar ≃ₗ[Rg] Ar))
    (hE : ∀ w e, e ∈ edges w → ∀ x, E w e x = D e.2 ((D e.1).symm x)) (j : Stage) (ι : Fix h)
    (s l : Role κ h → Ar) (hinv : ∀ w, s w = D (vtxAt w (8 * stIdx j)) (l w))
    (w : Role κ h) (hw : invOf j w = some ι) :
    framedInvocation κ half E j ι s w =
      D (vtxAt w (8 * stIdx j + 8)) (invocation κ half j ι l w) := by
  have h0 : ∀ w, s w = D (posIn j ι 0 w) (l w) := by
    intro w
    unfold posIn
    split_ifs <;> simpa using hinv w
  have hc : Consec 0 (List.finRange 8) := by
    rw [finRange_eight]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  have := fold_inv half E D hE j ι (List.finRange 8) 0 hc s l h0 w
  unfold framedInvocation invocation
  rw [this]
  simp [posIn, hw]

theorem framed_stage (half : Rg) (E : EdgeOps κ h Ar) (D : Vertex κ h → (Ar ≃ₗ[Rg] Ar))
    (hE : ∀ w e, e ∈ edges w → ∀ x, E w e x = D e.2 ((D e.1).symm x)) (j : Stage)
    (s l : Role κ h → Ar) (hinv : ∀ w, s w = D (vtxAt w (8 * stIdx j)) (l w)) (w : Role κ h) :
    framedStage κ half E j s w = D (vtxAt w (8 * stIdx j + 8)) (stageMap κ half j l w) := by
  unfold framedStage stageMap
  rcases hw : invOf j w with _ | ι
  · rw [hinv w, vtxAt_add_of_no]
    intro g hg hc
    have hs : g.stage = j := by
      have := g.time.isLt
      unfold clk at hc
      apply stIdx_inj
      omega
    have := touch_inv w g hg
    rw [hs, hw] at this
    cases this
  · exact framed_invocation half E D hE j ι s l hinv w hw

/-- The framed network computes `D_sink ∘ net ∘ D_source⁻¹`, for any edge operators `E` that agree
with `D_head ∘ D_tail⁻¹` on the actual edges of every wire (a slight strengthening of the contract,
which fixes `E` to be exactly this map on all pairs). -/
theorem framedNet_eq (half : Rg) (E : EdgeOps κ h Ar) (D : Vertex κ h → (Ar ≃ₗ[Rg] Ar))
    (hE : ∀ w e, e ∈ edges w → ∀ x, E w e x = D e.2 ((D e.1).symm x)) (s : Role κ h → Ar) (w : Role κ h) :
    framedNet κ half E s w =
      D (.sink w) (net κ half (fun w' => (D (.source w')).symm (s w')) w) := by
  set l0 : Role κ h → Ar := fun w' => (D (.source w')).symm (s w') with hl0
  have h0 : ∀ w, s w = D (vtxAt w (8 * stIdx .one)) (l0 w) := by
    intro w
    simp [stIdx, vtxAt_zero, hl0]
  have h1 : ∀ w, framedStage κ half E .one s w =
      D (vtxAt w (8 * stIdx .two)) (stageMap κ half .one l0 w) :=
    framed_stage half E D hE .one s l0 h0
  have h2 : ∀ w, framedStage κ half E .two (framedStage κ half E .one s) w =
      D (vtxAt w (8 * stIdx .three)) (stageMap κ half .two (stageMap κ half .one l0) w) :=
    framed_stage half E D hE .two _ _ h1
  have h3 : ∀ w, framedStage κ half E .three
      (framedStage κ half E .two (framedStage κ half E .one s)) w =
      D (vtxAt w 24) (net κ half l0 w) :=
    framed_stage half E D hE .three _ _ h2
  unfold framedNet
  simp only [edgeInto_sink, hE w _ (edgeInto_mem (edgeInto_sink w)), h3,
    LinearEquiv.symm_apply_apply]

end Invariant

end FI

/-- **Frame invariant (5)** ([OAI26, §3.2, (5)]): with edge operators `D_v ∘ D_u⁻¹` the framed
network equals `D_out ∘ S_Ω ∘ D_in⁻¹`. Unconditional; every `h`, both networks. -/
theorem frameInvariant_holds (h : ℕ) : FrameInvariantStmt h := by
  intro κ Rg Ar _ _ _ half D s w
  exact FI.framedNet_eq half _ D (fun _ _ _ _ => rfl) s w

namespace FI

variable {h : ℕ} {κ : Kind}

/-! ### Reusable incidence lemmas (ordered gate lists vs. simultaneous schedule rows)

* `touch_unique`: a wire meets at most one gate at a given stage and time;
* `gateAt_eq_some_iff`: `gateAt` returns exactly that gate;
* `rowUpd_untouched`: the row at `(j, ι, r)` leaves every wire without a gate at `(j, ι, r)` unchanged;
* `rowUpd_local`: on a wire touched by the gate `g` at `(j, ι, r)`, the row only reads the wires
  touched by `g`;
* `rowUpd_comm` (above): the row commutes with linear maps that are constant on each gate. -/

theorem eq_of_pairwise_lt {α : Type*} (f : α → ℕ) : ∀ {l : List α},
    l.Pairwise (fun x y => f x < f y) → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, hpw, a, b, ha, hb, hab => by
    rw [List.pairwise_cons] at hpw
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · rw [ha'] at hab
      exact absurd hab (Nat.ne_of_lt (hpw.1 b hb'))
    · rw [hb'] at hab
      exact absurd hab.symm (Nat.ne_of_lt (hpw.1 a ha'))
    · exact eq_of_pairwise_lt f hpw.2 ha' hb' hab

/-- A wire meets at most one gate at a given stage and time. -/
theorem touch_unique {w : Role κ h} {g g' : Gate h} (hg : g ∈ touch w) (hg' : g' ∈ touch w)
    (hs : g.stage = g'.stage) (ht : g.time = g'.time) : g = g' := by
  refine eq_of_pairwise_lt clk (touch_pairwise w) hg hg' ?_
  unfold clk
  rw [hs, ht]

/-- `gateAt j ι r w` is the unique gate of `w` at stage `j`, invocation `ι`, time `r`. -/
theorem gateAt_eq_some_iff {j : Stage} {ι : Fix h} {r : Fin 8} {w : Role κ h} {g : Gate h} :
    gateAt j ι r w = some g ↔ g ∈ touch w ∧ g.stage = j ∧ g.inv = ι ∧ g.time = r :=
  ⟨gateAt_spec, fun ⟨hm, hs, hi, ht⟩ => gateAt_of_mem hm hs hi ht⟩

/-- The row at `(j, ι, r)` leaves every wire without a gate at `(j, ι, r)` unchanged. -/
theorem rowUpd_untouched {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (half : R)
    (j : Stage) (ι : Fix h) (r : Fin 8) (ε : R) (s : Role κ h → M) (w : Role κ h)
    (hw : gateAt j ι r w = none) : rowUpd κ half j ι (rowOp j r) ε s w = s w := by
  have hno := gateAt_none hw
  rcases rowOp_cases j r with ⟨hop, hr⟩ | ⟨hop, hr⟩ | ⟨hop, hr⟩ | ⟨hop, hr⟩ <;> rw [hop]
  · cases w with
    | side j' ι' p =>
      simp only [rowUpd]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      subst h1 h2
      exact hno _ (memV hr p).1 ⟨rfl, rfl, rfl⟩
    | X a => rfl
    | Y a => rfl
    | center j' ι' c => rfl
  · cases w with
    | center j' ι' c =>
      simp only [rowUpd]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      subst h1 h2
      exact hno _ (mem_touch_center c r (center_times (Or.inl hr))) ⟨rfl, rfl, rfl⟩
    | X a => rfl
    | Y a => rfl
    | side j' ι' p => rfl
  · simp only [rowUpd]
    cases hS : tgtTriple? j ι w with
    | none => rfl
    | some S => exact (hno _ (memJ_tgt hr hS) ⟨rfl, rfl, rfl⟩).elim
  · simp only [rowUpd]
    cases hS : tgtTriple? j ι w with
    | none => rfl
    | some S => exact (hno _ (memR_tgt hr hS) ⟨rfl, rfl, rfl⟩).elim

/-- On a wire touched by the gate `g` at `(j, ι, r)`, the row at `(j, ι, r)` reads only the wires
touched by `g`. -/
theorem rowUpd_local {Rg Ar : Type*} [CommRing Rg] [AddCommGroup Ar] [Module Rg Ar] (half : Rg)
    (j : Stage) (ι : Fix h) (r : Fin 8) (ε : Rg) (g : Gate h) (s s' : Role κ h → Ar)
    (hss : ∀ w', g ∈ touch w' → s w' = s' w') (w : Role κ h) (hw : gateAt j ι r w = some g) :
    rowUpd κ half j ι (rowOp j r) ε s w = rowUpd κ half j ι (rowOp j r) ε s' w := by
  classical
  obtain ⟨hgm, hgs, hgi, hgt⟩ := gateAt_spec hw
  let F : Role κ h → Ar →ₗ[Rg] Ar := fun w' => if g ∈ touch w' then LinearMap.id else 0
  let Fg : Gate h → Ar →ₗ[Rg] Ar := fun g' => if g' = g then LinearMap.id else 0
  have hF : GateConst j ι r F Fg := by
    intro w' g' hm hs hi ht
    by_cases hgg : g' = g
    · have hm' : g ∈ touch w' := hgg ▸ hm
      simp only [F, Fg, if_pos hm', if_pos hgg]
    · have hn : g ∉ touch w' := fun hg =>
        hgg (touch_unique hm hg (hs.trans hgs.symm) (ht.trans hgt.symm))
      simp only [F, Fg, if_neg hn, if_neg hgg]
  have hFs : (fun w' => F w' (s w')) = (fun w' => F w' (s' w')) := by
    funext w'
    by_cases hg : g ∈ touch w'
    · simp only [F, if_pos hg, hss w' hg]
    · simp only [F, if_neg hg, LinearMap.zero_apply]
  have h1 := rowUpd_comm half j ι r ε F Fg hF s w
  have h2 := rowUpd_comm half j ι r ε F Fg hF s' w
  have hFw : F w = LinearMap.id := by simp only [F, if_pos hgm]
  rw [hFs, h2, hFw] at h1
  simpa using h1.symm

/-! ### 6. The bit-network array corollary -/

/-- `ratMod` agrees with every fraction representation whose denominator is prime to `n`. -/
theorem ratMod_eq_of_mul (n : ℕ) (a : ℚ) (z : ℤ) (d : ℕ) (hd : Nat.Coprime d n)
    (ha : Nat.Coprime a.den n) (had : a * d = z) :
    ratMod n a = (z : ZMod n) * ((d : ZMod n))⁻¹ := by
  have key : a.num * (d : ℤ) = z * (a.den : ℤ) := by
    have h1 : a * a.den = a.num := Rat.mul_den_eq_num a
    have h2 : ((a.num * d : ℤ) : ℚ) = ((z * a.den : ℤ) : ℚ) := by
      push_cast
      rw [← h1, ← had]
      ring
    exact_mod_cast h2
  have key' : (a.num : ZMod n) * (d : ZMod n) = (z : ZMod n) * (a.den : ZMod n) := by
    have := congrArg (Int.cast : ℤ → ZMod n) key
    push_cast at this
    exact this
  have hu := ZMod.coe_mul_inv_eq_one d hd
  have hv := ZMod.coe_mul_inv_eq_one a.den ha
  unfold ratMod
  linear_combination ((a.den : ZMod n))⁻¹ * ((d : ZMod n))⁻¹ * key'
    - (a.num : ZMod n) * ((a.den : ZMod n))⁻¹ * hu + (z : ZMod n) * ((d : ZMod n))⁻¹ * hv

/-- `ratMod n` is additive (here: subtractive) on rationals with denominators prime to `n`. -/
theorem ratMod_sub (n : ℕ) (a b : ℚ) (ha : Nat.Coprime a.den n) (hb : Nat.Coprime b.den n) :
    ratMod n (a - b) = ratMod n a - ratMod n b := by
  have hab : Nat.Coprime (a.den * b.den) n := Nat.Coprime.mul_left ha hb
  have hden : Nat.Coprime (a - b).den n :=
    Nat.Coprime.coprime_dvd_left (Rat.sub_den_dvd a b) hab
  have hrep : (a - b) * ((a.den * b.den : ℕ) : ℚ) =
      ((a.num * b.den - b.num * a.den : ℤ) : ℚ) := by
    have h1 : a * a.den = a.num := Rat.mul_den_eq_num a
    have h2 : b * b.den = b.num := Rat.mul_den_eq_num b
    push_cast
    rw [← h1, ← h2]
    ring
  rw [ratMod_eq_of_mul n (a - b) _ _ hab hden hrep]
  have hu := ZMod.coe_mul_inv_eq_one a.den ha
  have hv := ZMod.coe_mul_inv_eq_one b.den hb
  have hw := ZMod.coe_mul_inv_eq_one (a.den * b.den) hab
  set W := (((a.den * b.den : ℕ) : ZMod n))⁻¹ with hW
  rw [Nat.cast_mul] at hw
  unfold ratMod
  push_cast
  linear_combination ((a.num : ZMod n) * ((a.den : ZMod n))⁻¹
      - (b.num : ZMod n) * ((b.den : ZMod n))⁻¹) * hw
    - ((a.num : ZMod n) * (b.den : ZMod n) * W) * hu
    + ((b.num : ZMod n) * (a.den : ZMod n) * W) * hv

theorem ratMod_zero (n : ℕ) : ratMod n 0 = 0 := by simp [ratMod]

theorem ratMod_one (n : ℕ) : ratMod n 1 = 1 := by simp [ratMod]

theorem coprime_of_qIntegral {q : ℕ} (hq : q.Prime) (b : ℕ) {r : ℚ} (hr : QIntegral q r) :
    Nat.Coprime r.den (q ^ b) :=
  Nat.Coprime.pow_right b ((Nat.Prime.coprime_iff_not_dvd hq).2 hr).symm


section Shear

variable {σ : Type*}

/-- The address map `(H, D, σ) ↦ (H − M' D, D, σ)` (`M' = M mod Q`) as a bijection. -/
def addrShear (Q : ℕ) (Mx : Matrix (Cube h) (Cube h) ℚ) : ChunkAddr h Q σ ≃ ChunkAddr h Q σ where
  toFun x := (x.1 - (Mx.map (ratMod Q)).mulVec x.2.1, x.2.1, x.2.2)
  invFun x := (x.1 + (Mx.map (ratMod Q)).mulVec x.2.1, x.2.1, x.2.2)
  left_inv x := by simp
  right_inv x := by simp

theorem addrShear_apply (Q : ℕ) (Mx : Matrix (Cube h) (Cube h) ℚ) (x : ChunkAddr h Q σ) :
    addrShear Q Mx x = (x.1 - (Mx.map (ratMod Q)).mulVec x.2.1, x.2.1, x.2.2) := rfl

theorem addrShear_symm_apply (Q : ℕ) (Mx : Matrix (Cube h) (Cube h) ℚ) (x : ChunkAddr h Q σ) :
    (addrShear Q Mx).symm x = (x.1 + (Mx.map (ratMod Q)).mulVec x.2.1, x.2.1, x.2.2) := rfl

/-- The array frame `Φ_M` (precomposition with `addrShear`) as a linear equivalence; as a function
it is `shearArr Q M`. -/
def shearLE {R Md : Type*} [Semiring R] [AddCommMonoid Md] [Module R Md] (Q : ℕ)
    (Mx : Matrix (Cube h) (Cube h) ℚ) :
    (ChunkAddr h Q σ → Md) ≃ₗ[R] (ChunkAddr h Q σ → Md) where
  toFun f := fun x => f (addrShear Q Mx x)
  invFun f := fun x => f ((addrShear Q Mx).symm x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by funext x; simp
  right_inv f := by funext x; simp

theorem shearLE_apply {R Md : Type*} [Semiring R] [AddCommMonoid Md] [Module R Md] (Q : ℕ)
    (Mx : Matrix (Cube h) (Cube h) ℚ) (f : ChunkAddr h Q σ → Md) (x : ChunkAddr h Q σ) :
    shearLE (R := R) Q Mx f x = f (addrShear Q Mx x) := rfl

theorem shearLE_symm_apply {R Md : Type*} [Semiring R] [AddCommMonoid Md] [Module R Md]
    (Q : ℕ) (Mx : Matrix (Cube h) (Cube h) ℚ) (f : ChunkAddr h Q σ → Md) (x : ChunkAddr h Q σ) :
    (shearLE (R := R) Q Mx).symm f x = f ((addrShear Q Mx).symm x) := rfl

theorem shearLE_eq_shearArr {R Md : Type*} [Semiring R] [AddCommMonoid Md] [Module R Md]
    (Q : ℕ) (Mx : Matrix (Cube h) (Cube h) ℚ) (f : ChunkAddr h Q σ → Md) :
    shearLE (R := R) Q Mx f = shearArr Q Mx f := rfl

/-- For `q`-integral matrices and `Q = q^b`: `Φ_{M_v − M_u} = Φ_{M_v} ∘ Φ_{M_u}⁻¹` on arrays. -/
theorem shearArr_sub_eq {R Md : Type*} [Semiring R] [AddCommMonoid Md] [Module R Md] {q : ℕ}
    (hq : q.Prime) (b : ℕ) (Mv Mu : Matrix (Cube h) (Cube h) ℚ)
    (hv : ∀ i j, QIntegral q (Mv i j)) (hu : ∀ i j, QIntegral q (Mu i j))
    (f : ChunkAddr h (q ^ b) σ → Md) :
    shearArr (q ^ b) (Mv - Mu) f =
      shearLE (R := R) (q ^ b) Mv ((shearLE (R := R) (q ^ b) Mu).symm f) := by
  have hmap : (Mv - Mu).map (ratMod (q ^ b)) =
      Mv.map (ratMod (q ^ b)) - Mu.map (ratMod (q ^ b)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply]
    exact ratMod_sub _ _ _ (coprime_of_qIntegral hq b (hv i j))
      (coprime_of_qIntegral hq b (hu i j))
  funext x
  rw [shearLE_apply, shearLE_symm_apply, addrShear_apply, addrShear_symm_apply]
  simp only [shearArr, hmap, Matrix.sub_mulVec]
  congr 2
  abel

end Shear

end FI

/-- **Bit-network array corollary (B3)** ([OAI26, §3.4, Prop. 7];
Proposition A.7 (`prop:transfer11`)), from the frame invariant at `h = 100`, B1 (`Lemma5BitStmt 100`)
and B2 (`Prop7EndpointStmt`): with the physical edge operators `Φ_{A_e}` every output role `ρ w` holds
input role `w` sheared by `H ← H + D`, for arbitrary arrays on all roles. -/
theorem bitArrayCorollary_of (hFI : FrameInvariantStmt 100) (hB1 : Lemma5BitStmt 100)
    (hB2 : Prop7EndpointStmt) : BitArrayCorollaryStmt := by
  intro σ Md _ _ q b hq hint s w x
  have hE : (bitEdgeOps (q ^ b) : EdgeOps .bit 100 (ChunkAddr 100 (q ^ b) σ → Md)) =
      fun (_ : Role .bit 100) (e : Vertex .bit 100 × Vertex .bit 100)
        (f : ChunkAddr 100 (q ^ b) σ → Md) => FI.shearLE (R := ZMod 2) (q ^ b) (matB e.2)
        ((FI.shearLE (R := ZMod 2) (q ^ b) (matB e.1)).symm f) := by
    funext w' e f
    exact FI.shearArr_sub_eq hq b _ _ (hint e.2) (hint e.1) f
  have hFI' := hFI .bit (0 : ZMod 2)
    (fun v => FI.shearLE (R := ZMod 2) (σ := σ) (Md := Md) (q ^ b) (matB v)) s w.rho
  rw [hE, hFI', hB1]
  have hM : matB (.sink w.rho : Vertex .bit 100) - matB (.source w) = 1 := by
    unfold matB
    rw [← map_sub, hB2 w]
    exact LinearMap.toMatrix'_one
  rw [← FI.shearArr_sub_eq hq b (matB (.sink w.rho)) (matB (.source w)) (hint _) (hint _) (s w),
    hM]
  simp only [shearArr]
  rw [Matrix.map_one _ (FI.ratMod_zero _) (FI.ratMod_one _), Matrix.one_mulVec]

/-- B3 from B1 and B2 alone: the frame invariant is proved unconditionally (`frameInvariant_holds`). -/
theorem bitArrayCorollary_of_B1B2 (hB1 : Lemma5BitStmt 100) (hB2 : Prop7EndpointStmt) :
    BitArrayCorollaryStmt :=
  bitArrayCorollary_of (frameInvariant_holds 100) hB1 hB2

end SubNLogN.Math.Networks
