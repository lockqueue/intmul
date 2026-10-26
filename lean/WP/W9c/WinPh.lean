import WP.W9c.WinState

/-!
# WP.W9c.WinPh — the four loops of the window kernel

Registers `WR R = Option Sym × R`: the symbol register, then the adder's registers.

| loop | driven by | body | one iteration |
|---|---|---|---|
| 1 | `sWn` (window entries) | `wB1` | move `w` to `sTW` and `d` to `sTD` (order kept), one unit on `sU` |
| 2 | `sTW` | `wB2` | `sE += w + d` (one list entry), drop `d` and `w` |
| 3 | `sD` (remaining digits) | `wB3` | move `d` to `sTD` with its symbols reversed, remove one unit |
| 4 | `sU` (units left) | `wB4` | remove one unit, push a zero entry on `sWn` |
-/

namespace WP.W9c.CK

open TMFw TMFw.Contracts WP.W7k2

/-- Registers of the window kernel: the symbol register and the adder's registers. -/
abbrev WR (R : Type) : Type := Option Sym × R

/-- `k` units of the unary counter. -/
def units (k : ℕ) : List Sym := List.replicate k (Sym.bit true)

/-- Loop 1 body. -/
def wB1 (R : Type) : HP 4 4 (WR R) :=
  (mvNum (Lens.fst _ _) sWn sTW sX).seq ((mvNum (Lens.fst _ _) sD sTD sX).seq
    (pushS sU (.bit true)))

/-- Loop 2 body. -/
def wB2 (I : Inst 3 4 Unit) : HP 4 4 (WR I.R) :=
  (pushS sE .sep).seq ((callI I [sTW, sTD, sE] sD (Lens.snd _ _)).seq
    ((dropNum (Lens.fst _ _) sTD).seq (dropNum (Lens.fst _ _) sTW)))

/-- Loop 3 body. -/
def wB3 (R : Type) : HP 4 4 (WR R) := (mvRev (Lens.fst _ _) sD sTD).seq (popS sU)

/-- Loop 4 body. -/
def wB4 (R : Type) : HP 4 4 (WR R) := (popS sU).seq ((pushS sWn .sep).seq (pushS sWn .pos))

theorem wB1_closed (R : Type) : (wB1 R).Closed :=
  ⟨mvNum_closed _ _ _ _, mvNum_closed _ _ _ _, trivial⟩

theorem wB2_closed (I : Inst 3 4 Unit) : (wB2 I).Closed :=
  ⟨trivial, callI_closed _ _ _ _, dropNum_closed _ _, dropNum_closed _ _⟩

theorem wB3_closed (R : Type) : (wB3 R).Closed := ⟨mvRev_closed _ _ _, trivial⟩

theorem wB4_closed (R : Type) : (wB4 R).Closed := ⟨trivial, trivial, trivial⟩

theorem rev_entry (acc : List ℤ) (d : ℤ) (r : List Sym) :
    (intSyms d ++ [Sym.sep]).reverse ++ ((listSyms acc).reverse ++ r) =
      (listSyms (acc ++ [d])).reverse ++ r := by
  simp [listSyms_append, listSyms_cons, listSyms_nil]

variable {R : Type}

/-! ## Loop 1 -/

theorem win_b1 (ρ : List (HP 4 4 (WR R))) (B : ℕ) (w d : ℤ) (ws ds : List ℤ)
    (rd rw e c td tw u x : List Sym) (hw : bitLen w.natAbs ≤ B) (hd : bitLen d.natAbs ≤ B) :
    HT ρ (WS.f ⟨listSyms (d :: ds) ++ rd, listSyms (w :: ws) ++ rw, e, c, td, tw, u, x⟩) (wB1 R)
      (WS.f ⟨listSyms ds ++ rd, listSyms ws ++ rw, e, c, intSyms d ++ Sym.sep :: td,
        intSyms w ++ Sym.sep :: tw, Sym.bit true :: u, x⟩) (16 * B + 21) := by
  have h1 := ck_mvNum (ρ := ρ) (Lens.fst (Option Sym) R) (src := sWn) (dst := sTW) (X := sX)
    (by decide) (by decide) (by decide)
    (WS.f ⟨listSyms (d :: ds) ++ rd, listSyms (w :: ws) ++ rw, e, c, td, tw, u, x⟩) w
    (listSyms ws ++ rw) (cons_entry w ws rw).symm
  rw [upd_w, f_tw, upd_tw] at h1
  have h2 := ck_mvNum (ρ := ρ) (Lens.fst (Option Sym) R) (src := sD) (dst := sTD) (X := sX)
    (by decide) (by decide) (by decide)
    (WS.f ⟨listSyms (d :: ds) ++ rd, listSyms ws ++ rw, e, c, td, intSyms w ++ Sym.sep :: tw, u,
      x⟩) d (listSyms ds ++ rd) (cons_entry d ds rd).symm
  rw [upd_d, f_td, upd_td] at h2
  have h3 := HT.pushS (σ := WR R) sU (Sym.bit true) (WS.f ⟨listSyms ds ++ rd, listSyms ws ++ rw,
    e, c, intSyms d ++ Sym.sep :: td, intSyms w ++ Sym.sep :: tw, u, x⟩) ρ
  rw [f_u, upd_u] at h3
  refine HT.mono (HT.seq h1 (HT.seq h2 h3)) ?_
  omega

theorem win_ph1 (ρ : List (HP 4 4 (WR R))) (B : ℕ) (rd rw e c td0 tw0 u0 x : List Sym)
    (hrw : EndOK rw) (ws : List ℤ) :
    ∀ (ds twacc tdacc : List ℤ) (k : ℕ), ws.length ≤ ds.length →
      (∀ v ∈ ws, bitLen v.natAbs ≤ B) → (∀ v ∈ ds, bitLen v.natAbs ≤ B) →
      LT ρ (Lens.fst _ _) sWn isSign (wB1 R)
        (WS.f ⟨listSyms ds ++ rd, listSyms ws ++ rw, e, c, listSyms tdacc ++ Sym.mark :: td0,
          listSyms twacc ++ Sym.mark :: tw0, units k ++ Sym.mark :: u0, x⟩)
        (WS.f ⟨listSyms (ds.drop ws.length) ++ rd, rw, e, c,
          listSyms ((ds.take ws.length).reverse ++ tdacc) ++ Sym.mark :: td0,
          listSyms (ws.reverse ++ twacc) ++ Sym.mark :: tw0,
          units (k + ws.length) ++ Sym.mark :: u0, x⟩)
        (ws.length * (16 * B + 23) + 1) := by
  induction ws with
  | nil =>
    intro ds twacc tdacc k _ _ _
    exact LT.of_eq (ck_lt_stop _ _ _ _ _ (optT_isSign_of_endOK hrw)) rfl (by simp)
  | cons w ws ih =>
    intro ds twacc tdacc k hlen hbw hbd
    cases ds with
    | nil => simp at hlen
    | cons d ds =>
      have h1 := win_b1 (R := R) ρ B w d ws ds rd rw e c (listSyms tdacc ++ Sym.mark :: td0)
        (listSyms twacc ++ Sym.mark :: tw0) (units k ++ Sym.mark :: u0) x (hbw w (by simp))
        (hbd d (by simp))
      rw [cons_entry, cons_entry] at h1
      have h2 := ih ds (w :: twacc) (d :: tdacc) (k + 1) (by simp at hlen; omega)
        (fun v hv => hbw v (by simp [hv])) (fun v hv => hbd v (by simp [hv]))
      rw [show k + 1 + ws.length = k + (ws.length + 1) by omega] at h2
      refine LT.of_eq (ck_lt_step _ _ _ _ (optT_isSign_listSyms_cons w ws rw) h1 h2) ?_ ?_
      · simp only [List.length_cons, List.drop_succ_cons, List.take_succ_cons, List.reverse_cons,
          List.append_assoc, List.singleton_append]
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega

/-! ## Loop 2 -/

theorem win_b2 {I : Inst 3 4 Unit} {Ca : ℕ} (hI : SpecAddInt I Ca) (ρ : List (HP 4 4 (WR I.R)))
    (B : ℕ) (w d : ℤ) (pw pd : List ℤ) (dd ww e c td0 tw0 u x : List Sym)
    (hw : bitLen w.natAbs ≤ B) (hd : bitLen d.natAbs ≤ B) :
    HT ρ (WS.f ⟨dd, ww, e, c, listSyms (d :: pd) ++ Sym.mark :: td0,
        listSyms (w :: pw) ++ Sym.mark :: tw0, u, x⟩) (wB2 I)
      (WS.f ⟨dd, ww, intSyms (w + d) ++ Sym.sep :: e, c, listSyms pd ++ Sym.mark :: td0,
        listSyms pw ++ Sym.mark :: tw0, u, x⟩) (Ca * (2 * B + 1) + 6 * B + 9) := by
  have h1 := HT.pushS (σ := WR I.R) sE Sym.sep (WS.f ⟨dd, ww, e, c,
    listSyms (d :: pd) ++ Sym.mark :: td0, listSyms (w :: pw) ++ Sym.mark :: tw0, u, x⟩) ρ
  rw [f_e, upd_e] at h1
  have h2 := ck_addInt (ρ := ρ) hI sD (Lens.snd (Option Sym) I.R) sTW sTD sE (by decide)
    (by decide) (WS.f ⟨dd, ww, Sym.sep :: e, c, listSyms (d :: pd) ++ Sym.mark :: td0,
      listSyms (w :: pw) ++ Sym.mark :: tw0, u, x⟩) w d _ _ (termOK_sep _) (termOK_sep _)
    (cons_entry w pw _).symm (cons_entry d pd _).symm
  rw [f_e, upd_e] at h2
  have h3 := ck_dropNum (ρ := ρ) (Lens.fst (Option Sym) I.R) sTD
    (WS.f ⟨dd, ww, intSyms (w + d) ++ Sym.sep :: e, c, listSyms (d :: pd) ++ Sym.mark :: td0,
      listSyms (w :: pw) ++ Sym.mark :: tw0, u, x⟩) d _ (cons_entry d pd _).symm
  rw [upd_td] at h3
  have h4 := ck_dropNum (ρ := ρ) (Lens.fst (Option Sym) I.R) sTW
    (WS.f ⟨dd, ww, intSyms (w + d) ++ Sym.sep :: e, c, listSyms pd ++ Sym.mark :: td0,
      listSyms (w :: pw) ++ Sym.mark :: tw0, u, x⟩) w _ (cons_entry w pw _).symm
  rw [upd_tw] at h4
  refine HT.mono (HT.seq h1 (HT.seq h2 (HT.seq h3 h4))) ?_
  have : Ca * (bitLen w.natAbs + bitLen d.natAbs + 1) ≤ Ca * (2 * B + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem win_ph2 {I : Inst 3 4 Unit} {Ca : ℕ} (hI : SpecAddInt I Ca) (ρ : List (HP 4 4 (WR I.R)))
    (B : ℕ) (dd ww c td0 tw0 u x : List Sym) (pw : List ℤ) :
    ∀ (pd : List ℤ) (e : List Sym), pw.length = pd.length →
      (∀ v ∈ pw, bitLen v.natAbs ≤ B) → (∀ v ∈ pd, bitLen v.natAbs ≤ B) →
      LT ρ (Lens.fst _ _) sTW isSign (wB2 I)
        (WS.f ⟨dd, ww, e, c, listSyms pd ++ Sym.mark :: td0, listSyms pw ++ Sym.mark :: tw0, u, x⟩)
        (WS.f ⟨dd, ww, listSyms (List.zipWith (· + ·) pw pd).reverse ++ e, c, Sym.mark :: td0,
          Sym.mark :: tw0, u, x⟩)
        (pw.length * (Ca * (2 * B + 1) + 6 * B + 11) + 1) := by
  induction pw with
  | nil =>
    intro pd e hlen _ _
    cases pd with
    | nil => exact LT.of_eq (ck_lt_stop _ _ _ _ _ rfl) rfl (by simp)
    | cons _ _ => simp at hlen
  | cons w pw ih =>
    intro pd e hlen hbw hbd
    cases pd with
    | nil => simp at hlen
    | cons d pd =>
      have h1 := win_b2 hI ρ B w d pw pd dd ww e c td0 tw0 u x (hbw w (by simp)) (hbd d (by simp))
      have h2 := ih pd (intSyms (w + d) ++ Sym.sep :: e) (by simpa using hlen)
        (fun v hv => hbw v (by simp [hv])) (fun v hv => hbd v (by simp [hv]))
      refine LT.of_eq (ck_lt_step _ _ _ _ (optT_isSign_listSyms_cons w pw _) h1 h2) ?_ ?_
      · simp [listSyms_append, listSyms_cons, listSyms_nil]
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega

/-! ## Loop 3 -/

theorem win_b3 (ρ : List (HP 4 4 (WR R))) (B : ℕ) (d : ℤ) (ds : List ℤ)
    (rd w e c td tw u x : List Sym) (hd : bitLen d.natAbs ≤ B) :
    HT ρ (WS.f ⟨listSyms (d :: ds) ++ rd, w, e, c, td, tw, Sym.bit true :: u, x⟩) (wB3 R)
      (WS.f ⟨listSyms ds ++ rd, w, e, c, (intSyms d ++ [Sym.sep]).reverse ++ td, tw, u, x⟩)
      (4 * B + 7) := by
  have h1 := ck_mvRev (ρ := ρ) (Lens.fst (Option Sym) R) (src := sD) (dst := sTD) (by decide)
    (WS.f ⟨listSyms (d :: ds) ++ rd, w, e, c, td, tw, Sym.bit true :: u, x⟩) d (listSyms ds ++ rd)
    (cons_entry d ds rd).symm
  rw [upd_d, f_td, upd_td] at h1
  have h2 := HT.popS (σ := WR R) sU (WS.f ⟨listSyms ds ++ rd, w, e, c,
    (intSyms d ++ [Sym.sep]).reverse ++ td, tw, Sym.bit true :: u, x⟩) (Sym.bit true) u rfl ρ
  rw [upd_u] at h2
  refine HT.mono (HT.seq h1 h2) ?_
  omega

theorem win_ph3 (ρ : List (HP 4 4 (WR R))) (B : ℕ) (rd w e c td0 tw u0 x : List Sym)
    (hrd : EndOK rd) (ds : List ℤ) :
    ∀ (acc : List ℤ) (k : ℕ), ds.length ≤ k → (∀ v ∈ ds, bitLen v.natAbs ≤ B) →
      LT ρ (Lens.fst _ _) sD isSign (wB3 R)
        (WS.f ⟨listSyms ds ++ rd, w, e, c, (listSyms acc).reverse ++ Sym.mark :: td0, tw,
          units k ++ Sym.mark :: u0, x⟩)
        (WS.f ⟨rd, w, e, c, (listSyms (acc ++ ds)).reverse ++ Sym.mark :: td0, tw,
          units (k - ds.length) ++ Sym.mark :: u0, x⟩)
        (ds.length * (4 * B + 9) + 1) := by
  induction ds with
  | nil =>
    intro acc k _ _
    exact LT.of_eq (ck_lt_stop _ _ _ _ _ (optT_isSign_of_endOK hrd)) (by simp [listSyms_nil])
      (by simp)
  | cons d ds ih =>
    intro acc k hk hbd
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have h1 := win_b3 (R := R) ρ B d ds rd w e c ((listSyms acc).reverse ++ Sym.mark :: td0) tw
      (units k ++ Sym.mark :: u0) x (hbd d (by simp))
    rw [rev_entry] at h1
    have h2 := ih (acc ++ [d]) k (by simp at hk; omega) (fun v hv => hbd v (by simp [hv]))
    refine LT.of_eq (ck_lt_step _ _ _ _ (optT_isSign_listSyms_cons d ds rd) h1 h2) ?_ ?_
    · simp
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-! ## Loop 4 -/

theorem win_b4 (ρ : List (HP 4 4 (WR R))) (d w e c td tw u x : List Sym) :
    HT ρ (WS.f ⟨d, w, e, c, td, tw, Sym.bit true :: u, x⟩) (wB4 R)
      (WS.f ⟨d, Sym.pos :: Sym.sep :: w, e, c, td, tw, u, x⟩) 3 := by
  have h1 := HT.popS (σ := WR R) sU (WS.f ⟨d, w, e, c, td, tw, Sym.bit true :: u, x⟩)
    (Sym.bit true) u rfl ρ
  rw [upd_u] at h1
  have h2 := HT.pushS (σ := WR R) sWn Sym.sep (WS.f ⟨d, w, e, c, td, tw, u, x⟩) ρ
  rw [f_w, upd_w] at h2
  have h3 := HT.pushS (σ := WR R) sWn Sym.pos (WS.f ⟨d, Sym.sep :: w, e, c, td, tw, u, x⟩) ρ
  rw [f_w, upd_w] at h3
  exact HT.seq h1 (HT.seq h2 h3)

theorem win_ph4 (ρ : List (HP 4 4 (WR R))) (d e c td tw u0 x rw : List Sym) (j : ℕ) :
    ∀ zs : ℕ, LT ρ (Lens.fst _ _) sU Sym.isBit (wB4 R)
      (WS.f ⟨d, listSyms (List.replicate zs 0) ++ rw, e, c, td, tw, units j ++ Sym.mark :: u0, x⟩)
      (WS.f ⟨d, listSyms (List.replicate (zs + j) 0) ++ rw, e, c, td, tw, Sym.mark :: u0, x⟩)
      (j * 5 + 1) := by
  induction j with
  | zero =>
    intro zs
    exact LT.of_eq (ck_lt_stop _ _ _ _ _ rfl) rfl (by simp)
  | succ j ih =>
    intro zs
    have h1 := win_b4 (R := R) ρ d (listSyms (List.replicate zs 0) ++ rw) e c td tw
      (units j ++ Sym.mark :: u0) x
    have h2 := ih (zs + 1)
    rw [show zs + 1 + j = zs + (j + 1) by omega] at h2
    refine LT.of_eq (ck_lt_step _ _ _ _ rfl (h1.of_eq ?_ le_rfl) h2) rfl ?_
    · rw [List.replicate_succ, listSyms_cons, intSyms_zero]
      rfl
    · omega

#assert_std_axioms wB1_closed wB2_closed wB3_closed wB4_closed rev_entry win_b1 win_ph1 win_b2 win_ph2 win_b3 win_ph3 win_b4 win_ph4

end WP.W9c.CK
