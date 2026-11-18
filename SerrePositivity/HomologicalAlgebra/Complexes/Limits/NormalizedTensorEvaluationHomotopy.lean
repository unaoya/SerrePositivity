module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleMap
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeFamily
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveConstant
/-! 概要：元の大域評価三角形は全関手圏内で同じ全族の合成を与える。
方針：元の全三辺を持つ二単体族を curry する。
規約：全 K と元の円柱を保持。使われ方：同じ導来 roof との大域比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.SimplicialModel
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
def normalizedTensorEvaluationHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) := by
  let T := nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)
  refine _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (HomotopyClasses.postHomotopy T
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A X Y))) ?_ ?_
  · rfl
  · rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.nerveMap_const, SSet.const_comp]
    have hv : T.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := A) Y := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).injective
      rfl
    exact congrArg SSet.const hv

lemma normalizedTensorEvaluationHomotopy_h :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorEvaluationHomotopy A X Y).h =
      (β_ (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) (Δ[1] : SSet.{u + 1})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationJoin A X Y := by
  exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluationJoin_prism A X Y).symm

end SerrePositivity.ComplexLimits
