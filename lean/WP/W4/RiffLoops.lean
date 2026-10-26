import WP.W4.Steps

/-!
# WP.W4.RiffLoops — the three loops of the riffle pass

* `buildL X Y U`: move every record `X → Y` (reversing), push one ruler unit `sep` on `U` each;
* `splitL X Y U`: while `U` has units: pop two, move one record `X → Y`;
* `interL X Y Z`: while `Y`'s top is `sep` (a reversed record): `moveRecUp Z X; moveRecUp Y X`.
-/

namespace TMFw.W4

open TMFw TMFw.Lib TMFw.Contracts

variable {K : Type}

def buildBody (X Y U : K) : SProg K := .seq (moveRec X Y) (.seq (pushC U .sep) (peekR X))
def buildL (X Y U : K) : SProg K := .seq (peekR X) (.loop isRecR (buildBody X Y U))
def splitBody (X Y U : K) : SProg K :=
  .seq (popR U) (.seq (popR U) (.seq (moveRec X Y) (peekR U)))
def splitL (X Y U : K) : SProg K := .seq (peekR U) (.loop isSepR (splitBody X Y U))
def interBody (X Y Z : K) : SProg K := .seq (moveRecUp Z X) (moveRecUp Y X)
def interL (X Y Z : K) : SProg K := .seq (peekR Y) (.loop isSepR (interBody X Y Z))

theorem inter_append_single {α : Type} (a b : α) : ∀ (A B : List α), A.length = B.length →
    inter (A ++ [a]) (B ++ [b]) = inter A B ++ [a, b]
  | [], [], _ => rfl
  | x :: A, y :: B, h => by
    simp only [List.cons_append, inter_cons_cons, inter_append_single a b A B (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

variable [DecidableEq K]

theorem build_loop {X Y U : K} (hXY : X ≠ Y) (hXU : X ≠ U) (hYU : Y ≠ U) (ρ : List (SProg K)) :
    ∀ (l : List (List Sym)) (rest : List Sym) (S : K → List Sym), (∀ r ∈ l, RecOK r) →
      RecTerm rest → S X = l.flatten ++ rest →
      EvLe ρ (.loop isRecR (buildBody X Y U)) (l.flatten ++ rest).head? S rest.head?
        (Function.update (Function.update (Function.update S X rest) Y
          (l.flatten.reverse ++ S Y)) U (List.replicate l.length Sym.sep ++ S U))
        (3 * l.flatten.length + 3 * l.length + 1)
  | [], rest, S, _, hrest, hS => by
    refine (EvLe.loop_false (isRecR_head?_of_recTerm (by simpa using hrest))).of_eq (by simp) ?_
      (by simp)
    have hS' : S X = rest := by simpa using hS
    funext k
    simp only [Function.update_apply, List.flatten_nil, List.reverse_nil, List.nil_append,
      List.length_nil, List.replicate_zero]
    split_ifs <;> simp_all
  | r :: l, rest, S, hl, hrest, hS => by
    have hr : RecOK r := hl r (by simp)
    have hl' : ∀ x ∈ l, RecOK x := fun x hx => hl x (by simp [hx])
    have e1 := moveRec_rec_eval hXY ρ ((r :: l).flatten ++ rest).head? r (l.flatten ++ rest) S hr
      (by rw [hS]; simp)
    set S1 := Function.update (Function.update S X (l.flatten ++ rest)) Y (r.reverse ++ S Y)
      with hS1
    have e2 := pushC_evLe ρ U Sym.sep (some Sym.sep) S1
    set S2 := Function.update S1 U (Sym.sep :: S1 U) with hS2
    have hS2X : S2 X = l.flatten ++ rest := by
      rw [hS2, Function.update_of_ne hXU, hS1, Function.update_of_ne hXY, Function.update_self]
    have e3 := peekR_evLe ρ X (some Sym.sep) S2
    rw [hS2X] at e3
    have ih := build_loop hXY hXU hYU ρ l rest S2 hl' hrest hS2X
    have hc : isRecR ((r :: l).flatten ++ rest).head? = true := by
      rw [List.flatten_cons, List.append_assoc]
      exact isRecR_head_of_recOK hr _
    refine (EvLe.loop_true hc ((EvLe.of_eval e1 le_rfl).seq (e2.seq e3)) ih).of_eq rfl ?_ ?_
    · funext k
      simp only [hS2, hS1, Function.update_apply, List.flatten_cons, List.reverse_append,
        List.append_assoc, List.length_cons, List.replicate_succ', List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.flatten_cons, List.length_append, List.length_cons]
      omega

theorem split_loop {X Y U : K} (hXY : X ≠ Y) (hXU : X ≠ U) (hYU : Y ≠ U) (ρ : List (SProg K)) :
    ∀ (A : List (List Sym)) (restX restU : List Sym) (S : K → List Sym), (∀ r ∈ A, RecOK r) →
      isSepR restU.head? = false → S X = A.flatten ++ restX →
      S U = List.replicate (2 * A.length) Sym.sep ++ restU →
      EvLe ρ (.loop isSepR (splitBody X Y U))
        (List.replicate (2 * A.length) Sym.sep ++ restU).head? S restU.head?
        (Function.update (Function.update (Function.update S X restX) Y
          (A.flatten.reverse ++ S Y)) U restU)
        (3 * A.flatten.length + 5 * A.length + 1)
  | [], restX, restU, S, _, hU0, hX, hU => by
    simp only [List.length_nil, Nat.mul_zero, List.replicate_zero, List.nil_append] at hU ⊢
    refine (EvLe.loop_false hU0).of_eq rfl ?_ (by simp)
    have hX' : S X = restX := by simpa using hX
    funext k
    simp only [Function.update_apply, List.flatten_nil, List.reverse_nil, List.nil_append]
    split_ifs <;> simp_all
  | r :: A, restX, restU, S, hA, hU0, hX, hU => by
    have hr : RecOK r := hA r (by simp)
    have hA' : ∀ x ∈ A, RecOK x := fun x hx => hA x (by simp [hx])
    set R := List.replicate (2 * A.length) Sym.sep ++ restU with hR
    have hU' : S U = Sym.sep :: Sym.sep :: R := by
      rw [hU, hR, List.length_cons, show 2 * (A.length + 1) = 2 * A.length + 1 + 1 by omega,
        List.replicate_succ, List.replicate_succ]
      rfl
    have e1 := popR_evLe ρ U (List.replicate (2 * (r :: A).length) Sym.sep ++ restU).head? S
    rw [hU'] at e1
    simp only [List.head?_cons, List.tail_cons] at e1
    set S1 := Function.update S U (Sym.sep :: R) with hS1
    have e2 := popR_evLe ρ U (some Sym.sep) S1
    rw [show S1 U = Sym.sep :: R by rw [hS1, Function.update_self]] at e2
    simp only [List.head?_cons, List.tail_cons] at e2
    set S2 := Function.update S1 U R with hS2
    have e3 := moveRec_rec_eval hXY ρ (some Sym.sep) r (A.flatten ++ restX) S2 hr
      (by rw [hS2, Function.update_of_ne hXU, hS1, Function.update_of_ne hXU, hX]; simp)
    set S3 := Function.update (Function.update S2 X (A.flatten ++ restX)) Y (r.reverse ++ S2 Y)
      with hS3
    have hS3U : S3 U = R := by
      rw [hS3, Function.update_of_ne (Ne.symm hYU), Function.update_of_ne (Ne.symm hXU), hS2,
        Function.update_self]
    have e4 := peekR_evLe ρ U (some Sym.sep) S3
    rw [hS3U] at e4
    have ih := split_loop hXY hXU hYU ρ A restX restU S3 hA' hU0
      (by rw [hS3, Function.update_of_ne hXY, Function.update_self]) hS3U
    have hc : isSepR (List.replicate (2 * (r :: A).length) Sym.sep ++ restU).head? = true := by
      rw [List.length_cons, show 2 * (A.length + 1) = 2 * A.length + 1 + 1 by omega,
        List.replicate_succ]
      rfl
    refine (EvLe.loop_true hc (e1.seq (e2.seq ((EvLe.of_eval e3 le_rfl).seq e4))) ih).of_eq rfl
      ?_ ?_
    · funext k
      simp only [hS3, hS2, hS1, Function.update_apply, List.flatten_cons, List.reverse_append,
        List.append_assoc]
      split_ifs <;> simp_all
    · simp only [List.flatten_cons, List.length_append, List.length_cons]
      omega

theorem inter_loop {X Y Z : K} (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z) (ρ : List (SProg K)) :
    ∀ (A B : List (List Sym)) (restY restZ : List Sym) (S : K → List Sym), A.length = B.length →
      (∀ r ∈ A, RecOK r) → (∀ r ∈ B, RecOK r) → DataTerm restY → isSepR restY.head? = false →
      DataTerm restZ → S Y = (A.map List.reverse).flatten ++ restY →
      S Z = (B.map List.reverse).flatten ++ restZ →
      EvLe ρ (.loop isSepR (interBody X Y Z)) ((A.map List.reverse).flatten ++ restY).head? S
        restY.head? (Function.update (Function.update (Function.update S X
          ((inter A.reverse B.reverse).flatten ++ S X)) Y restY) Z restZ)
        (4 * A.flatten.length + 4 * B.flatten.length + A.length + 1)
  | [], [], restY, restZ, S, _, _, _, _, hY0, _, hY, hZ => by
    simp only [List.map_nil, List.flatten_nil, List.nil_append] at hY hZ ⊢
    refine (EvLe.loop_false hY0).of_eq rfl ?_ (by simp)
    funext k
    simp only [Function.update_apply, List.reverse_nil, inter_nil_left, List.flatten_nil,
      List.nil_append]
    split_ifs <;> simp_all
  | a :: A, b :: B, restY, restZ, S, hlen, hA, hB, hdY, hY0, hdZ, hY, hZ => by
    have ha : RecOK a := hA a (by simp)
    have hb : RecOK b := hB b (by simp)
    have hA' : ∀ x ∈ A, RecOK x := fun x hx => hA x (by simp [hx])
    have hB' : ∀ x ∈ B, RecOK x := fun x hx => hB x (by simp [hx])
    have e1 := moveRecUp_eval (Ne.symm hXZ) ρ (((a :: A).map List.reverse).flatten ++ restY).head?
      b ((B.map List.reverse).flatten ++ restZ) S hb (dataTerm_up hB' restZ hdZ)
      (by rw [hZ]; simp)
    set S1 := Function.update (Function.update S Z ((B.map List.reverse).flatten ++ restZ)) X
      (b ++ S X) with hS1
    have e2 := moveRecUp_eval (Ne.symm hXY) ρ ((B.map List.reverse).flatten ++ restZ).head? a
      ((A.map List.reverse).flatten ++ restY) S1 ha (dataTerm_up hA' restY hdY)
      (by rw [hS1, Function.update_of_ne (Ne.symm hXY), Function.update_of_ne hYZ, hY]; simp)
    set S2 := Function.update (Function.update S1 Y ((A.map List.reverse).flatten ++ restY)) X
      (a ++ S1 X) with hS2
    have ih := inter_loop hXY hXZ hYZ ρ A B restY restZ S2 (by simpa using hlen) hA' hB' hdY hY0
      hdZ (by rw [hS2, Function.update_of_ne (Ne.symm hXY), Function.update_self])
      (by rw [hS2, Function.update_of_ne (Ne.symm hXZ), Function.update_of_ne (Ne.symm hYZ), hS1,
        Function.update_of_ne (Ne.symm hXZ), Function.update_self])
    have hc : isSepR (((a :: A).map List.reverse).flatten ++ restY).head? = true := by
      rw [List.map_cons, List.flatten_cons, List.append_assoc, reverse_recOK_head ha]
      rfl
    have key : inter (a :: A).reverse (b :: B).reverse = inter A.reverse B.reverse ++ [a, b] := by
      rw [List.reverse_cons, List.reverse_cons]
      exact inter_append_single a b _ _ (by simpa using hlen)
    refine (EvLe.loop_true hc ((EvLe.of_eval e1 le_rfl).seq (EvLe.of_eval e2 le_rfl)) ih).of_eq rfl
      ?_ ?_
    · funext k
      simp only [hS2, hS1, Function.update_apply, key, List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.append_assoc]
      split_ifs <;> simp_all
    · simp only [List.flatten_cons, List.length_append, List.length_cons]
      omega
  | [], _ :: _, _, _, _, h, _, _, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _, _, _, _, _, _ => by simp at h

#assert_std_axioms inter_append_single build_loop split_loop inter_loop

end TMFw.W4
