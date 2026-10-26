/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Walsh.CnotScanUV
import SubNLogN.Machine.Walsh.CnotScanModeShift

/-!
# `SubNLogN.Machine.Walsh.CnotScanSelScalar`: popcount and unit routine of the selective scalar

Paper: Lemma 5.1 (`lem:walsh-select`, the scalar `2^s (2(1-i))^{q_sel}` of the
gadget, Lemma 5.1). Plan: top of `Walsh/CnotScanEngine.lean`.

**Scope (honest summary).** `pcLoop` walks the `U`-vector and, for its `q` ones, adds
`q + ⌊q/2⌋` units to `n3` and leaves `k = 3⌊q/2⌋ mod 4`, `μ = [q odd]` in the registers
(`runsR_pcLoop`); `writeK` stores `k` in unary on `pl`; `kRu` is the per-record unit routine
reading it back (`kRSpec_kRu`). No contract is proved here.
-/

namespace SubNLogN.Machine.WalshScanAux

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine WalshLift Computability
open SubNLogN.Math.Walsh SubNLogN.Math.Common

/-! ## Arithmetic of the popcount -/

/-- Units added by the popcount for the ones of `bs`, after `c` ones. -/
def addU : List Bool → ℕ → ℕ
  | [], _ => 0
  | true :: bs, c => 1 + (if c % 2 = 1 then 1 else 0) + addU bs (c + 1)
  | false :: bs, c => addU bs c

theorem addU_spec : ∀ (bs : List Bool) (c : ℕ),
    addU bs c + (c + c / 2) = (c + bs.count true) + (c + bs.count true) / 2
  | [], c => by simp [addU]
  | true :: bs, c => by
    have ih := addU_spec bs (c + 1)
    have hc : (true :: bs).count true = bs.count true + 1 := by simp
    rw [hc]
    simp only [addU]
    split_ifs with h <;> omega
  | false :: bs, c => by
    have ih := addU_spec bs c
    have hc : (false :: bs).count true = bs.count true := by simp
    rw [hc]
    simp only [addU]
    exact ih

theorem parity_succ (c : ℕ) : decide ((c + 1) % 2 = 1) = !decide (c % 2 = 1) := by
  by_cases h : c % 2 = 1
  · have h' : ¬ (c + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (c + 1) % 2 = 1 := by omega
    simp [h, h']

theorem kOf_succ (c : ℕ) : kOf (c + 1) = if c % 2 = 1 then kOf c + 3 else kOf c := by
  unfold kOf
  split_ifs with h
  · ext
    simp only [Fin.val_add]
    omega
  · ext
    simp only
    omega

/-! ## The popcount loop -/

/-- The mask bit in `s` is a one. -/
def sTrue (r : ER) : Bool := decide (r.s = some (Sym.bit true))

/-- The register update of a popcount step. -/
def pcUpd (r : ER) : ER :=
  { r with k := if sTrue r && r.mu then r.k + 3 else r.k, mu := if sTrue r then !r.mu else r.mu }

/-- One popcount step: move a mask bit `uv → tmp`; on a one add `1 + [μ]` units to `n3`,
`3[μ]` to `k`, flip `μ`. -/
def pcStep : EProg SK :=
  .seq (popS (.inr .uv))
  (.seq (pushS (.inr .tmp))
  (.seq (.ite sTrue (pushK (.inr .n3) uSym) (.load id))
  (.seq (.ite (fun r => sTrue r && r.mu) (pushK (.inr .n3) uSym) (.load id))
  (.seq (.load pcUpd)
    (peekT (.inr .uv))))))

/-- The popcount loop over the `U`-vector. -/
def pcLoop : EProg SK := .seq (peekT (.inr .uv)) (.loop tIsBit pcStep)

theorem eval_iteK (c : ER → Bool) (k : SK) (r : ER) (S : SK → List Sym) :
    Eval [] (.ite c (pushK k uSym) (.load id)) ⟨r, S⟩
      ⟨r, if c r then Function.update S k (uSym :: S k) else S⟩ 2 := by
  cases h : c r
  · exact (Eval.ite_false h (Eval.load [] id r S)).of_eq (by simp) rfl
  · exact (Eval.ite_true h (eval_pushK k uSym r S)).of_eq (by simp) rfl

/-- The register after a popcount step on the bit `b` (rest `bs`). -/
def pcReg (b : Bool) (bs : List Bool) (r : ER) : ER :=
  ⟨(bs.map Sym.bit).head?, some (Sym.bit b), (if b && r.mu then r.k + 3 else r.k),
    (if b then (!r.mu) else r.mu), r.c1, r.c2⟩

theorem pcStep_eval (b : Bool) (bs : List Bool) (r : ER) (S : SK → List Sym)
    (hS : S (.inr .uv) = (b :: bs).map Sym.bit) :
    Eval [] pcStep ⟨r, S⟩
      ⟨pcReg b bs r,
       Function.update (Function.update (Function.update S (.inr .uv) (bs.map Sym.bit))
         (.inr .tmp) (Sym.bit b :: S (.inr .tmp))) (.inr .n3)
         (List.replicate ((if b then 1 else 0) + (if b && r.mu then 1 else 0)) uSym ++
           S (.inr .n3))⟩ 8 := by
  have e1 := eval_popS (.inr .uv : SK) r _ S hS
  refine (Eval.seq e1 (Eval.seq (eval_pushS (.inr .tmp : SK) _ (Sym.bit b) rfl _)
    (Eval.seq (eval_iteK sTrue (.inr .n3) _ _)
    (Eval.seq (eval_iteK (fun r => sTrue r && r.mu) (.inr .n3) _ _)
    (Eval.seq (Eval.load [] pcUpd _ _) (eval_peekT (.inr .uv) _ _)))))).of_eq ?_ rfl
  cases b <;> cases hmu : r.mu
  all_goals
    congr 1
    all_goals simp [sTrue, pcUpd, pcReg, hmu]

theorem pcLoop_loop : ∀ (bs : List Bool) (c : ℕ) (r : ER) (S : SK → List Sym),
    r.t = (bs.map Sym.bit).head? → S (.inr .uv) = bs.map Sym.bit →
    r.mu = decide (c % 2 = 1) → r.k = kOf c →
    ∃ r' t, Eval [] (.loop tIsBit pcStep) ⟨r, S⟩
      ⟨r', Function.update (Function.update (Function.update S (.inr .uv) [])
        (.inr .tmp) (bs.reverse.map Sym.bit ++ S (.inr .tmp))) (.inr .n3)
        (List.replicate (addU bs c) uSym ++ S (.inr .n3))⟩ t ∧
      r'.mu = decide ((c + bs.count true) % 2 = 1) ∧ r'.k = kOf (c + bs.count true) ∧
      t ≤ 9 * bs.length + 1
  | [], c, r, S, ht, hS, hmu, hk => by
    have ht' : r.t = none := by simpa using ht
    refine ⟨r, 1, (Eval.loop_false (by simp [tIsBit, ht', optIsBit])).of_eq ?_ rfl,
      by simpa using hmu, by simpa using hk, by simp⟩
    congr 1
    funext j
    rcases j with i | e
    · simp
    · cases e <;> simp [hS, addU]
  | b :: bs, c, r, S, ht, hS, hmu, hk => by
    have ht' : r.t = some (Sym.bit b) := by simpa using ht
    have e1 := pcStep_eval b bs r S hS
    obtain ⟨r', t, e2, hmu', hk', ht2⟩ := pcLoop_loop bs (c + if b then 1 else 0)
      (pcReg b bs r)
      (Function.update (Function.update (Function.update S (.inr .uv) (bs.map Sym.bit))
         (.inr .tmp) (Sym.bit b :: S (.inr .tmp))) (.inr .n3)
         (List.replicate ((if b then 1 else 0) + (if b && r.mu then 1 else 0)) uSym ++
           S (.inr .n3)))
      rfl (by simp)
      (by cases b <;> simp [pcReg, hmu, parity_succ])
      (by cases b <;> simp [pcReg, hk, hmu, kOf_succ])
    have hn3 : List.replicate (addU bs (c + if b then 1 else 0)) uSym ++
        (List.replicate ((if b then 1 else 0) + (if b && r.mu then 1 else 0)) uSym ++
          S (.inr .n3)) = List.replicate (addU (b :: bs) c) uSym ++ S (.inr .n3) := by
      rw [← List.append_assoc, List.replicate_append_replicate]
      congr 2
      by_cases hc : c % 2 = 1
      · have hm : r.mu = true := by rw [hmu]; simp [hc]
        cases b <;> simp [addU, hm, hc] <;> omega
      · have hm : r.mu = false := by rw [hmu]; simp [hc]
        cases b <;> simp [addU, hm, hc] <;> omega
    have hcnt : c + (b :: bs).count true = (c + if b then 1 else 0) + bs.count true := by
      cases b <;> simp <;> omega
    refine ⟨r', _, (Eval.loop_true (by simp [tIsBit, ht', optIsBit]) e1 e2).of_eq ?_ rfl,
      by rw [hcnt]; exact hmu', by rw [hcnt]; exact hk', by simp only [List.length_cons]; omega⟩
    congr 1
    funext j
    rcases j with i | e
    · simp
    · cases e
      case n3 =>
        simp only [Function.update_self]
        exact hn3
      all_goals simp

theorem runsR_pcLoop (bs : List Bool) (S : SK → List Sym) (hS : S (.inr .uv) = bs.map Sym.bit) :
    RunsR pcLoop S
      (Function.update (Function.update (Function.update S (.inr .uv) [])
        (.inr .tmp) (bs.reverse.map Sym.bit ++ S (.inr .tmp))) (.inr .n3)
        (List.replicate (addU bs 0) uSym ++ S (.inr .n3)))
      (fun r => r.k = 0 ∧ r.mu = false)
      (fun r => r.mu = decide (bs.count true % 2 = 1) ∧ r.k = kOf (bs.count true))
      (9 * bs.length + 2) := by
  rintro r ⟨hk, hmu⟩
  have e1 := eval_peekT (.inr .uv : SK) r S
  obtain ⟨r', t, e2, hmu', hk', ht⟩ := pcLoop_loop bs 0 { r with t := (S (.inr .uv)).head? } S
    (by simp [hS]) hS (by simp [hmu]) (by simp [hk, kOf])
  refine ⟨r', 1 + t, Eval.seq e1 e2, ⟨by simpa using hmu', by simpa using hk'⟩, by omega⟩

/-! ## Storing and reading back the unit exponent -/

/-- Store `k` in unary on `pl`. -/
def writeK : EProg SK :=
  .seq (.ite (fun r => decide (1 ≤ r.k.val)) (pushK (.inr .pl) uSym) (.load id))
  (.seq (.ite (fun r => decide (2 ≤ r.k.val)) (pushK (.inr .pl) uSym) (.load id))
    (.ite (fun r => decide (3 ≤ r.k.val)) (pushK (.inr .pl) uSym) (.load id)))

theorem runsR_writeK (S : SK → List Sym) (hpl : S (.inr .pl) = []) (k0 : Fin 4) (mu0 : Bool) :
    RunsR writeK S (Function.update S (.inr .pl) (List.replicate k0.val uSym))
      (fun r => r.k = k0 ∧ r.mu = mu0) (fun r => r.mu = mu0) 6 := by
  rintro r ⟨hk, hmu⟩
  refine ⟨r, 6, (Eval.seq (eval_iteK _ (.inr .pl) r S) (Eval.seq (eval_iteK _ (.inr .pl) r _)
    (eval_iteK _ (.inr .pl) r _))).of_eq ?_ rfl, hmu, le_rfl⟩
  congr 1
  rw [hk]
  funext j
  rcases j with i | e
  · fin_cases k0 <;> simp
  · cases e <;> fin_cases k0 <;> simp [hpl]

/-- One read step: move a unit `pl → x2`, `k := k + 1`. -/
def kIncStep : EProg SK :=
  .seq (pushK (.inr .x2) uSym) (.seq (.load fun r => { r with k := r.k + 1 }) (popT (.inr .pl)))

/-- The unit routine of the selective scalar: `k :=` the unary value on `pl` (restored). -/
def kRu : EProg SK :=
  .seq (.load fun r => { r with k := 0 })
  (.seq (popT (.inr .pl))
  (.seq (.loop tSome kIncStep)
    ((drain (.inr .x2) (.inr .pl)).liftRegs lT)))

theorem kInc_loop : ∀ (n : ℕ) (r : ER) (S : SK → List Sym), r.t = (List.replicate n uSym).head? →
    S (.inr .pl) = (List.replicate n uSym).tail →
    ∃ r' t, Eval [] (.loop tSome kIncStep) ⟨r, S⟩
      ⟨r', Function.update (Function.update S (.inr .pl) []) (.inr .x2)
        (List.replicate n uSym ++ S (.inr .x2))⟩ t ∧
      r'.k.val = (r.k.val + n) % 4 ∧ r'.mu = r.mu ∧ t ≤ 4 * n + 1
  | 0, r, S, ht, hS => by
    have ht' : r.t = none := by simpa using ht
    have hS' : S (.inr .pl) = [] := by simpa using hS
    refine ⟨r, 1, (Eval.loop_false (by simp [tSome, ht'])).of_eq ?_ rfl,
      by simp [Nat.mod_eq_of_lt r.k.isLt], rfl, by omega⟩
    congr 1
    funext j
    rcases j with i | e
    · simp
    · cases e <;> simp [hS']
  | n + 1, r, S, ht, hS => by
    have ht' : r.t = some uSym := by simpa [List.replicate_succ] using ht
    have hS' : S (.inr .pl) = List.replicate n uSym := by simpa [List.replicate_succ] using hS
    have e1 := eval_pushK (.inr .x2 : SK) uSym r S
    have e2 := Eval.load [] (fun r : ER => { r with k := r.k + 1 }) r
      (Function.update S (.inr .x2) (uSym :: S (.inr .x2)))
    have e3 := eval_popT (.inr .pl : SK) { r with k := r.k + 1 } (List.replicate n uSym)
      (Function.update S (.inr .x2) (uSym :: S (.inr .x2))) (by simp [hS'])
    obtain ⟨r', t, e4, hk', hmu', ht4⟩ := kInc_loop n
      { r with k := r.k + 1, t := (List.replicate n uSym).head? }
      (Function.update (Function.update S (.inr .x2) (uSym :: S (.inr .x2))) (.inr .pl)
        (List.replicate n uSym).tail) rfl (by simp)
    refine ⟨r', _, (Eval.loop_true (by simp [tSome, ht']) (Eval.seq e1 (Eval.seq e2 e3))
      e4).of_eq ?_ rfl, ?_, hmu', by omega⟩
    · congr 1
      funext j
      rcases j with i | e
      · simp
      · cases e <;> simp [List.replicate_succ']
    · rw [hk']
      simp only [Fin.val_add, Fin.val_one]
      omega

/-- The static data of `kRu`: `pl = uSym^{k₀}`, `x2` empty. -/
def kStat (k0 : Fin 4) (S : SK → List Sym) : Prop :=
  S (.inr .pl) = List.replicate k0.val uSym ∧ S (.inr .x2) = []

theorem statFrame_kStat (k0 : Fin 4) : StatFrame (kStat k0) := by
  intro S S' h ⟨h1, h2⟩
  exact ⟨by rw [h _ (by simp) (by simp) (by simp)]; exact h1,
    by rw [h _ (by simp) (by simp) (by simp)]; exact h2⟩

theorem kRSpec_kRu (k0 : Fin 4) : KRSpec kRu (fun _ => k0) (fun _ => []) (kStat k0) 30 := by
  intro x S r _ ⟨hpl, hx2⟩
  have e1 := Eval.load [] (fun r : ER => { r with k := 0 }) r S
  have e2 := eval_popT (.inr .pl : SK) { r with k := 0 } _ S hpl
  obtain ⟨r', t, e3, hk', hmu', ht⟩ := kInc_loop k0.val
    { r with k := 0, t := (List.replicate k0.val uSym).head? }
    (Function.update S (.inr .pl) (List.replicate k0.val uSym).tail) rfl (by simp)
  obtain ⟨r'', t', e4, ⟨hk'', hmu''⟩, ht'⟩ := runsR_drainE (src := (.inr .x2 : SK))
    (dst := .inr .pl) (by decide) (List.replicate k0.val uSym)
    (Function.update (Function.update (Function.update S (.inr .pl)
      (List.replicate k0.val uSym).tail) (.inr .pl) []) (.inr .x2)
      (List.replicate k0.val uSym ++ (Function.update S (.inr .pl)
        (List.replicate k0.val uSym).tail) (.inr .x2))) (by simp [hx2])
    (fun q : ER => q.k = r'.k ∧ q.mu = r'.mu) (fun _ h => h) r' ⟨rfl, rfl⟩
  refine ⟨r'', _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))).of_eq ?_ rfl, ?_, ?_, ?_⟩
  · congr 1
    funext j
    rcases j with i | e
    · simp
    · cases e <;> simp [hpl, hx2]
  · rw [hk'']
    ext
    rw [hk']
    simp [Nat.mod_eq_of_lt k0.isLt]
  · rw [hmu'', hmu']
  · simp only [List.length_replicate] at ht'
    have := k0.isLt
    omega

