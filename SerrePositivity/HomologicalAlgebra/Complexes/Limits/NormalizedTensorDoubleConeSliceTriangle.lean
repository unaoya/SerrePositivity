module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeSliceEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SlicePrismFamilyComposition

/-!
概要：元の大域 cone 族と同じ実 slice 評価族の合成は、全関手圏で恒等となる。
方針：同じ slice prism の両端・全射影を既存の全族の合成定理へ代入する。
規約：通常 augmentation の円柱との同定は未主張。使われ方：元の augmentation 逆との比較。
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

lemma normalizedTensorDoubleConeSliceEvaluation_triangle :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorConeFamilyHom A X Y ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSliceEvaluationHom A X Y =
      𝟙 (SSet.HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y))
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X)))) := by
  let K := nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)
  let z := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X
  have hb : (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism K ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSlicePrism A X Y) =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (SSet.const (X := K) z)).h := by
    rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSlicePrism_zero,
      ← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy_precomp_h, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy_const_identity_h]
    exact (SSet.comp_const _ z).symm
  have ht : (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism K ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSlicePrism A X Y) =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y).h := by
    rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSlicePrism_one]
    exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSliceEvaluationHomotopy_h A X Y).symm
  have hl : (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSlicePrism A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X) =
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeHomotopy A X Y).h := by
    rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSlicePrism_projection]
    rfl
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.slicePrismFamily_comp z (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeHomotopy A X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (SSet.const (X := K) z))
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSlicePrism A X Y) hb ht hl
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom] at h
  exact h

end SerrePositivity.ComplexLimits
