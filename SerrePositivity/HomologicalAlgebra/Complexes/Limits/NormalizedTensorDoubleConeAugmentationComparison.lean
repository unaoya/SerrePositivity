module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeOverColumn
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementAugmentationJoin
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeSliceEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCurryHomExt

/-!
概要：構成した実 slice 図式の全余錐は、元の通常 augmentation の同じ混合宇宙の余錐に等しい。
方針：固定終端と全標準単体の実列表示から大域 join を比較し、元の全円柱を回収する。
規約：全パラメータと元の自然変換を保持する。使われ方：同じ augmentation の逆との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeOverDiagram_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverDiagram A X Y) =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationJoin A X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_left_hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed, _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationJoin_inr]
  · intro n a
    obtain ⟨c, rfl⟩ := (SSet.yonedaEquiv (X := nerve
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y))).symm.surjective a
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, SSet.yonedaEquiv_symm_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda, _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverDiagram_app]
    exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationJoin_restrict_simplex A X Y c).symm

lemma normalizedTensorDoubleConeSliceEvaluationHomotopy_h_standard :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y).h =
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y)).h ≫
        nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A) := by
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSliceEvaluationHomotopy_h,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverDiagram_uncurry, _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentationJoin_prism]

end SerrePositivity.ComplexLimits
