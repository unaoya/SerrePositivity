module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeSliceEvaluation
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeSliceEvaluation_triangle :
    normalizedTensorConeFamilyHom A X Y ≫ normalizedTensorDoubleConeSliceEvaluationHom A X Y =
      𝟙 (SSet.HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := nerve (normalizedTensorElementIndex A X Y))
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X)))) := by
  let K := nerve (normalizedTensorElementIndex A X Y)
  let z := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X
  have hb : (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism K ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ normalizedTensorDoubleConeSlicePrism A X Y) =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (SSet.const (X := K) z)).h := by
    rw [normalizedTensorDoubleConeSlicePrism_zero,
      ← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy_precomp_h, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy_const_identity_h]
    exact (SSet.comp_const _ z).symm
  have ht : (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism K ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ normalizedTensorDoubleConeSlicePrism A X Y) =
      (normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y).h := by
    rw [normalizedTensorDoubleConeSlicePrism_one]
    exact (normalizedTensorDoubleConeSliceEvaluationHomotopy_h A X Y).symm
  have hl : (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ normalizedTensorDoubleConeSlicePrism A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (normalizedTensorConePoint A X) =
        (normalizedTensorConeHomotopy A X Y).h := by
    rw [normalizedTensorDoubleConeSlicePrism_projection]
    rfl
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.slicePrismFamily_comp z (normalizedTensorConeHomotopy A X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (SSet.const (X := K) z))
    (normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y)
    (normalizedTensorDoubleConeSlicePrism A X Y) hb ht hl
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom] at h
  exact h

end SerrePositivity.EInfinity.ComplexLimits
