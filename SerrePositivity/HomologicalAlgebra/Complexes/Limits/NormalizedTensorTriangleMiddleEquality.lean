module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTrianglePrincipalWeighted
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleMiddleDegenerate

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

lemma normalizedTensorTriangle_middle_sum_heq {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hc : 3 ≤ I.card) (a b : Fin (n + 1)) (k : ℤ)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (haz : τ a = 0) (hbt : τ b = 2) :
    HEq (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (fun j => τ j = 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).cutCompose I a b k j)
      (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (fun j => τ j = 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).toSimplexData.cutCompose I a b k j) := by
  subst ha
  subst hb
  by_cases hp : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) = 1 ∧ τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) = 1
  · have hJ : (I.filter (fun i => τ i = 1)).Nonempty :=
      ⟨_, Finset.mem_filter.mpr ⟨_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second_mem I hI, hp.1⟩⟩
    have hcard := _root_.SerrePositivity.ComplexLimits.middle_card_add_two τ I hI hp.1 hp.2 haz hbt
    have hkJ : k + 1 = 1 - ((I.filter (fun i => τ i = 1)).card : ℤ) := by omega
    rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_middle_sum A X Y c τ I hI hc _ _ k rfl rfl hbt,
      _root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_middle_sum A X Y c τ I hI hc _ _ k rfl rfl,
      ite_eq_left hp.2, ite_eq_left hp.1]
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangle_principal_weighted_cut A X Y c τ I hI hc
      hp.1 hp.2 haz hbt k hk hJ hkJ
  · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangle_middle_sum_heq_of_not_both A X Y c τ I hI hc
      _ _ k rfl rfl haz hbt hp

end SerrePositivity.ComplexLimits
