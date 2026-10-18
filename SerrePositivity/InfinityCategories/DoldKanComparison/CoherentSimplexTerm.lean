module

public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentHomCoordinates

/-!
# 比較単体の rhs の一項と内部点の微分項

概要：既存 dg 単体の符号付き削除−合成の一項を、内部点表示の合成−削除へ同定する。
方針：削除と左右切断の内部集合を比較し、次数と符号の点数を合わせる。
規約：dg nerve の符号は終点を数え、内部点表示の符号は終点を数えない。
使われ方：HA 1.3.1.16、Kerodon 2.5.9 の Simplex.equation の rhs の各項。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：元の有限頂点番号で指定した内部点の微分項を定義する。
方針：native な内部点へ移し、合成項−削除成分の降順符号付きの差を取る。
規約：始次数は負の内部点数、値の次数はその一つ上。
使われ方：Kerodon 2.5.9 の内部点の和を元の頂点集合の和へ移す。 -/
def coherentSimplexInteriorTerm {n : ℕ}
    (s : (doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hdeg : k = -((coherentVertexInterior.{u} I a b).card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    GradedHom R (s.obj (.mk (ULift.up a))) (s.obj (.mk (ULift.up b))) (k + 1) :=
  let S := coherentVertexInterior.{u} I a b
  let t := coherentInteriorVertexPoint.{u} I j hj haj hjb
  have hdegS : k = -(S.card : ℤ) := hdeg
  (-1 : ℤ) ^ (S.filter (t.val < ·)).card •
    (coherentCubeCompositionAt s (show ULift.up a < ULift.up b from haj.trans hjb)
      S t (k + 1) (by omega) -
      coherentCubeComponentAt s (show ULift.up a < ULift.up b from haj.trans hjb)
        (S.erase t.val) (k + 1) (by
          have h : (S.erase t.val).card + 1 = S.card := Finset.card_erase_add_one t.property
          omega))

/-- 概要：比較単体の既存 rhs の一項は内部点表示の微分項に等しい。
方針：削除成分と左右の成分を対応する内部集合へ同定し、符号を差の反転へ移す。
規約：全ての次数を k+1 にそろえた通常の等号。
使われ方：HA 1.3.1.16 の比較成分族が dg 方程式を満たすことの項ごとの確認。 -/
lemma coherentSimplexData_term_eq_interior {n : ℕ}
    (s : (doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (DGNerve.Index.nonempty hI))
    (hb : b = I.max' (DGNerve.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hdeg : k = -((coherentVertexInterior.{u} I a b).card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    (coherentSimplexData s).term I a b k hI ha hb hk j hj haj hjb =
      coherentSimplexInteriorTerm s I a b k hdeg j hj haj hjb := by
  have hmin : IsLeast (I : Set (Fin (n + 1))) a := by rw [ha]; exact I.isLeast_min' _
  have hmax : IsGreatest (I : Set (Fin (n + 1))) b := by rw [hb]; exact I.isGreatest_max' _
  have hE := DGNerve.Index.erase_two hmin.1 hmax.1 haj hjb
  have hL := DGNerve.Index.left_two hmin.1 hj haj
  have hR := DGNerve.Index.right_two hj hmax.1 hjb
  have haE := DGNerve.Index.erase_min hmin haj (DGNerve.Index.nonempty hE)
  have hbE := DGNerve.Index.erase_max hmax hjb (DGNerve.Index.nonempty hE)
  have haL := DGNerve.Index.left_min hmin haj.le (DGNerve.Index.nonempty hL)
  have hjL := DGNerve.Index.left_max hj (DGNerve.Index.nonempty hL)
  have hjR := DGNerve.Index.right_min hj (DGNerve.Index.nonempty hR)
  have hbR := DGNerve.Index.right_max hmax hjb.le (DGNerve.Index.nonempty hR)
  have hkE : k + 1 = 2 - ((I.erase j).card : ℤ) := by
    have h := Finset.card_erase_add_one hj
    omega
  let S := coherentVertexInterior.{u} I a b
  let t := coherentInteriorVertexPoint.{u} I j hj haj hjb
  have hdegS : k = -(S.card : ℤ) := hdeg
  let fe := (coherentSimplexData s).hom (I.erase j) a b (k + 1) hE haE hbE hkE
  let fl := (coherentSimplexData s).hom (I.filter (· ≤ j)) a j
    (2 - ((I.filter (· ≤ j)).card : ℤ)) hL haL hjL rfl
  let fr := (coherentSimplexData s).hom (I.filter (j ≤ ·)) j b
    (2 - ((I.filter (j ≤ ·)).card : ℤ)) hR hjR hbR rfl
  have he : fe = coherentCubeComponentAt s
      (show ULift.up a < ULift.up b from haj.trans hjb) (S.erase t.val) (k + 1)
      (by
        have h : (S.erase t.val).card + 1 = S.card := Finset.card_erase_add_one t.property
        omega) := by
    apply eq_of_heq
    refine (coherentSimplexData_hom_heq_set s (I.erase j) a b (k + 1) hE haE hbE hkE
      (haj.trans hjb) _ (coherentVertexInterior_erase I haj hjb)).trans ?_
    exact (coherentCubeComponentAt_heq _ _ _ _ _).symm
  have hfl := coherentSimplexData_hom_heq_set s (I.filter (· ≤ j)) a j _ hL haL hjL rfl
    haj _ (coherentVertexInterior_left I haj hjb)
  have hfr := coherentSimplexData_hom_heq_set s (I.filter (j ≤ ·)) j b _ hR hjR hbR rfl
    hjb _ (coherentVertexInterior_right I haj hjb)
  have hLc := coherentVertexInterior_card
    (show IsLeast ((I.filter (· ≤ j)) : Set _) a from
      haL.symm ▸ Finset.isLeast_min' _ (DGNerve.Index.nonempty hL))
    (show IsGreatest ((I.filter (· ≤ j)) : Set _) j from
      Eq.mpr (congrArg (fun x : Fin (n + 1) ↦
        IsGreatest ((I.filter (· ≤ j)) : Set _) x) hjL)
        (Finset.isGreatest_max' _ (DGNerve.Index.nonempty hL)))
    haj
  have hRc := coherentVertexInterior_card
    (show IsLeast ((I.filter (j ≤ ·)) : Set _) j from
      Eq.mpr (congrArg (fun x : Fin (n + 1) ↦
        IsLeast ((I.filter (j ≤ ·)) : Set _) x) hjR)
        (Finset.isLeast_min' _ (DGNerve.Index.nonempty hR)))
    (show IsGreatest ((I.filter (j ≤ ·)) : Set _) b from
      hbR.symm ▸ Finset.isGreatest_max' _ (DGNerve.Index.nonempty hR))
    hjb
  rw [coherentVertexInterior_left I haj hjb] at hLc
  rw [coherentVertexInterior_right I haj hjb] at hRc
  have hLc' : (pathIntervalSet S (ULift.up a) t.val.val).card + 2 =
      (I.filter (· ≤ j)).card := hLc
  have hRc' : (pathIntervalSet S t.val.val (ULift.up b)).card + 2 =
      (I.filter (j ≤ ·)).card := hRc
  have hc : compose R fr fl (show (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 by
        have h := DGNerve.Index.split_card hj; omega) =
      coherentCubeCompositionAt s (show ULift.up a < ULift.up b from haj.trans hjb)
        S t (k + 1) (by omega) := by
    unfold coherentCubeCompositionAt
    apply compose_eq_of_heq
    · exact hfr
    · exact hfl
    · omega
    · omega
  change ((I.filter (j < ·)).card : ℤ).negOnePow • (fe - compose R fr fl _) = _
  rw [he, hc, ← coherentVertexSet_sign_card.{u} I j hj]
  exact coherentInterior_term_sign (coherentVertexSet_isGreatest hmax) t.val _ _

end SerrePositivity.InfinityCategories.DoldKanComparison
