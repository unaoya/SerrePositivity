module
public import
  SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeAugmentationComparison
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementDerivedRoof
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses

/-!
概要：構成した slice 評価族の同じ既存 D(R) 像は、元の全 augmentation 同型の射に等しい。
方針：同じ半自由分解への後合成と全円柱の等式を、全関手圏の Arrow の一致へ移す。
規約：両端の表示も保持した全射の比較。使われ方：元の大域 cone を同じ augmentation の逆へ照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeSliceEvaluation_derived_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y)
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)))) =
      Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedAugmentationIso A X Y).hom := by
  change Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y)
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)))) =
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHomotopy A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y))))
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
  change (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y).h ≫
      _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A =
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y)).h ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSliceEvaluationHomotopy_h_standard]
  simp only [_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource, Category.assoc]

end SerrePositivity.ComplexLimits
