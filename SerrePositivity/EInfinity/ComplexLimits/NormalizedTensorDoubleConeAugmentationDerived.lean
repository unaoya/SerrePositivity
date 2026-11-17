module
public import
  SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeAugmentationComparison
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementDerivedRoof
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeSliceEvaluation_derived_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
        (normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y)
        (complexSemifreeResolutionInfinity A)))) =
      Arrow.mk (normalizedTensorElementDerivedAugmentationIso A X Y).hom := by
  change Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
        (normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y)
        (complexSemifreeResolutionInfinity A)))) =
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (complexOrdinaryDerivedNatTransHomotopy A (normalizedTensorElementAugmentation A X Y))))
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
  change (normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y).h ≫
      complexSemifreeResolutionInfinity A =
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy (normalizedTensorElementAugmentation A X Y)).h ≫
      complexOrdinaryDerivedSource A
  rw [normalizedTensorDoubleConeSliceEvaluationHomotopy_h_standard]
  simp only [complexOrdinaryDerivedSource, Category.assoc]

end SerrePositivity.EInfinity.ComplexLimits
