module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeSlicePrismProjection
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeFamily
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.SliceEvaluationPinched

/-!
概要：構成した実 slice 図式の普遍評価を、元の frame 図式から同じ X への全族にする。
方針：同じ普遍評価ホモトピーを全図式で制限し、元の射影の等式で始域を合わせる。
規約：通常 augmentation の円柱との同定は別に検証する。使われ方：大域合成三角形。
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

def normalizedTensorDoubleConeSliceEvaluationHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y)
      (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X)) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X))
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverDiagram A X Y)).h
  h₀ := by
    rw [SSet.Homotopy.h₀]
    change _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverDiagram A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X) =
        _root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverDiagram_projection A X Y
  h₁ := by
    rw [SSet.Homotopy.h₁, SSet.comp_const]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

lemma normalizedTensorDoubleConeSliceEvaluationHomotopy_h :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y).h =
      (β_ (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) (Δ[1] : SSet.{u + 1})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverDiagram A X Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy_precomp_h _ _

def normalizedTensorDoubleConeSliceEvaluationHom :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y)
      (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X)) :=
  SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y))

end SerrePositivity.ComplexLimits
