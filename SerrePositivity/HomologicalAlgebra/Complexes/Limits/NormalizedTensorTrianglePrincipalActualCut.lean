module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTrianglePrincipalEvaluation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeTriangleMiddleCardinality

/-!
概要：元の主切断の評価・単位合成と符号から、同じ中央相の全切断和を比較する。
方針：元の二つの切断・実評価成分・全添字と次数を保持する。
規約：全二次境界と混合 HA は別工程。使われ方：大域評価三角形の実三相単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTriangleData_cutCompose_principal {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hc : 3 ≤ I.card)
    (hs1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) = 1)
    (hp1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) = 1)
    (haz : τ (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 0)
    (hbt : τ (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 2)
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hJ : (I.filter (fun i => τ i = 1)).Nonempty)
    (hkJ : k + 1 = 1 - ((I.filter (fun i => τ i = 1)).card : ℤ)) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).cutCompose I
      (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) k
        (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI))
      ((k + 1).negOnePow • (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c)).val.component
          (I.filter (fun i => τ i = 1)) (k + 1) hJ hkJ) := by
  let s := _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ
  let a := I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
  let b := I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
  let j := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI
  let L := I.filter (· ≤ j)
  let R := I.filter (j ≤ ·)
  have hj : j ∈ I := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate_mem I hI
  have haj : a < j := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.min_lt_penultimate I hI hc
  have hjb : j < b := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate_lt_max I hI
  have ham : IsLeast (I : Set (Fin (n + 1))) a := I.isLeast_min' _
  have hbm : IsGreatest (I : Set (Fin (n + 1))) b := I.isGreatest_max' _
  have hL : 2 ≤ L.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two ham.1 hj haj
  have hR : 2 ≤ R.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbm.1 hjb
  have hr : R.card = 2 :=
    (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.right_card_two_iff_penultimate I hI j hj hjb).mpr rfl
  have hl : 2 - (L.card : ℤ) = k + 1 := by
    have hsplit : L.card + R.card = I.card + 1 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  have hkR : (0 : ℤ) = 2 - (R.card : ℤ) := by omega
  have hsum : (2 - (L.card : ℤ)) + (2 - (R.card : ℤ)) = k + 1 := by omega
  change HEq (s.cutCompose I a b k j) _
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose
  rw [dite_eq_left hsum]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s R j b _ hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbm hjb.le _) rfl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s L a j _ hL (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ham haj.le _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl]
  have ht : HEq
      (s.hom R j b (2 - (R.card : ℤ)) hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbm hjb.le _) rfl)
      (s.hom R j b 0 hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbm hjb.le _) hkR) :=
    s.hom_heq_of_indices_degree rfl rfl rfl hkR.symm
  have hf : HEq
      (s.hom L a j (2 - (L.card : ℤ)) hL (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ham haj.le _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl)
      (s.hom L a j (k + 1) hL (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ham haj.le _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) hl.symm) :=
    s.hom_heq_of_indices_degree rfl rfl rfl hl
  have hcomp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) rfl rfl rfl hl hkR.symm rfl
    _ _ _ _ ht hf hsum (add_zero (k + 1))
  exact hcomp.trans (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_principal_composite A X Y c τ I hI
    hs1 hp1 haz hbt L rfl R (k + 1) hL (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ham haj.le _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) hl.symm hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbm hjb.le _)
    hkR hJ hkJ)

end SerrePositivity.ComplexLimits
