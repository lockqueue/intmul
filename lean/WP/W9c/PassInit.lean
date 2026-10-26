import WP.W9c.PassLoop2

/-!
# WP.W9c.PassInit — initialisation of a pass: zero tape, zero window, markers
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

variable {σ : Type} (K : PKit σ) {Mul : ℕ → ℕ} {C : ℕ}

/-- Cost of `pushZeros` for `n` cells. -/
def pzT (C n : ℕ) : ℕ :=
  1 + C * (bitLen n + 1) +
    (C + loopCost (fun i => C * (zerosLead (Computability.encodeNat (i + 1)) + 1) + 2 + C) n) + 1

theorem natSyms_zero' : natSyms 0 = [] := by simp [natSyms, encodeNat_zero]

theorem intSyms_zero : intSyms 0 = [Sym.pos] := by simp [intSyms, sgnSym, natSyms_zero']

theorem ht_pushZeros (hK : PKitOK Mul K C) (src dst : PL) (hsc : src ≠ pCT) (hdc : dst ≠ pCT)
    (B : PL → List Sym) (n : ℕ) (rs : List Sym) (hrs : TermOK rs) (hB : B src = natSyms n ++ rs)
    (ρ : List (HP 10 24 σ)) :
    HT ρ B (pushZeros K src dst) (Function.update B dst (listSyms (List.replicate n 0) ++ B dst))
      (pzT C n) := by
  have s1 := HT.pushS (ρ := ρ) pCT Sym.mark B
  set B1 := Function.update B pCT (Sym.mark :: B pCT) with hB1
  have s2 : HT ρ B1 (callI K.cp [src, pCT] pX K.lcp)
      (Function.update B1 pCT (natSyms n ++ Sym.mark :: B pCT)) (C * (bitLen n + 1)) := by
    have h := HT.copyNat hK.cp pX K.lcp src pCT (by simp [hsc]) (by norm_num) B1 n rs hrs
      (by rw [hB1, Function.update_of_ne hsc]; exact hB) ρ
    rwa [show B1 pCT = Sym.mark :: B pCT by rw [hB1, Function.update_self]] at h
  let St : ℕ → PL → List Sym := fun i =>
    Function.update (Function.update B pCT (natSyms i ++ Sym.mark :: B pCT)) dst
      (listSyms (List.replicate (n - i) 0) ++ B dst)
  have hSt : ∀ i, St i pCT = natSyms i ++ Sym.mark :: B pCT := fun i => by
    simp only [St]
    rw [Function.update_of_ne hdc.symm, Function.update_self]
  have s3 := ht_cdLoop (ρ := ρ) hK.iz hK.dc K.liz K.ldc pCT pX (by norm_num) (Sym.mark :: B pCT)
    (termOK_mark _) St hSt (zeroCell dst) (fun _ => 2) n (fun i hi => by
      have h := HT.seq (HT.pushS (ρ := ρ) dst Sym.sep
        (Function.update (St (i + 1)) pCT (natSyms i ++ Sym.mark :: B pCT)))
        (HT.pushS (ρ := ρ) dst Sym.pos _)
      refine h.of_eq ?_ le_rfl
      have e : n - i = (n - (i + 1)) + 1 := by omega
      funext j
      simp only [St, Function.update_apply]
      split_ifs <;> simp_all [List.replicate_succ, listSyms_cons, intSyms_zero])
  have hn : St n = Function.update B1 pCT (natSyms n ++ Sym.mark :: B pCT) := by
    funext j
    simp only [St, hB1, Function.update_apply, Nat.sub_self, List.replicate_zero, listSyms_nil,
      List.nil_append]
    split_ifs <;> simp_all
  rw [hn] at s3
  have s3' : HT ρ (Function.update B1 pCT (natSyms n ++ Sym.mark :: B pCT))
      (cdLoop K.iz K.dc K.liz K.ldc pCT pX (zeroCell dst)) (St 0)
      (C + loopCost (fun i => C * (zerosLead (Computability.encodeNat (i + 1)) + 1) + 2 + C) n) :=
    s3
  have s4 := HT.popS (ρ := ρ) pCT (St 0) Sym.mark (B pCT) (by rw [hSt, natSyms_zero', List.nil_append])
  refine (HT.seq s1 (HT.seq s2 (HT.seq s3' s4))).of_eq ?_ (by unfold pzT; omega)
  funext j
  simp only [St, Function.update_apply, Nat.sub_zero]
  split_ifs <;> simp_all

#assert_std_axioms natSyms_zero' intSyms_zero ht_pushZeros

end WP.W9c
